(function () {
'use strict';

const KEY = 'timelock.v2';
const DAYN = ['Sun', 'Mon', 'Tue', 'Wed', 'Thu', 'Fri', 'Sat'];
const $ = id => document.getElementById(id);
const ARMOR = '-----BEGIN AGE ENCRYPTED FILE-----';

/* ---------- time-lock engine (drand quicknet) ---------- */
function realEngine() {
  const TL = window.TL;
  const INFO = TL.defaultChainInfo;
  const RELAYS = ['https://api.drand.sh', 'https://api2.drand.sh', 'https://api3.drand.sh', 'https://drand.cloudflare.com'];
  const opts = { disableBeaconVerification: false, noCache: false,
    chainVerificationParams: { chainHash: INFO.hash, publicKey: INFO.public_key } };
  const clients = RELAYS.map(base => {
    const chain = new TL.HttpCachingChain(base + '/' + INFO.hash, opts);
    chain.info = async () => INFO; // chain info is built in, so sealing works offline
    return new TL.HttpChainClient(chain, opts);
  });
  const timeOf = r => (INFO.genesis_time + (r - 1) * INFO.period) * 1000;
  return {
    timeOf,
    roundFor(t) { let r = TL.roundAt(t, INFO); while (timeOf(r) < t) r++; return r; },
    async encrypt(round, text) { return TL.timelockEncrypt(round, TL.Buffer.from(text, 'utf8'), clients[0]); },
    async decrypt(ct) {
      let last;
      for (const c of clients) {
        try { return (await TL.timelockDecrypt(ct, c)).toString('utf8'); }
        catch (e) { if (/too early/i.test(e.message)) throw new Error('TOO_EARLY'); last = e; }
      }
      throw last || new Error('Could not reach drand');
    },
    async latestTime() {
      for (const base of RELAYS) {
        try {
          const r = await fetch(base + '/' + INFO.hash + '/public/latest', { cache: 'no-store' });
          if (r.ok) { const j = await r.json(); return { round: j.round, time: timeOf(j.round) }; }
        } catch (e) { /* try next relay */ }
      }
      return null;
    }
  };
}
const engine = window.__TL_ENGINE__ || realEngine();

/* ---------- state ---------- */
let locks = [], mode = 'until', days = [1, 2, 3, 4, 5];
const mem = {};    // id -> {num, until}  plaintext for an open repeating window, memory only
const peeks = {};  // id -> ms when the brief reveal ends
const busy = {};   // id -> true while unlocking or re-sealing
const errs = {};   // id -> {msg, retryAt}
let confirmDel = null, skew = 0, netOk = null;

function load() { try { const r = localStorage.getItem(KEY); return r ? JSON.parse(r) : []; } catch (e) { return []; } }
function saveLocal() { try { localStorage.setItem(KEY, JSON.stringify(locks)); } catch (e) {} }
function save() { saveLocal(); schedulePush(); }
function touch(L) { L.rev = (L.rev || 0) + 1; L.updated = Date.now(); }
const live = () => locks.filter(l => !l.deleted).sort((a, b) => (!!b.pinned - !!a.pinned) || ((b.created || 0) - (a.created || 0)));
const now = () => Date.now();
const repeating = L => L.mode === 'schedule' || L.mode === 'cycle';

/* ---------- windows ---------- */
function schedIntervals(L, t) {
  const [fh, fm] = L.from.split(':').map(Number), [th, tm] = L.to.split(':').map(Number);
  const base = new Date(t); base.setHours(0, 0, 0, 0);
  const out = [];
  for (let d = -1; d <= 8; d++) {
    const st = new Date(base); st.setDate(base.getDate() + d);
    if (!L.days.includes(st.getDay())) continue;
    st.setHours(fh, fm, 0, 0);
    const en = new Date(st); en.setHours(th, tm, 0, 0);
    if (en <= st) en.setDate(en.getDate() + 1);
    out.push([+st, +en]);
  }
  return out;
}
function currentWindow(L, t) {
  if (L.mode === 'schedule') { const w = schedIntervals(L, t).find(([s, e]) => t >= s && t < e); return w ? { start: w[0], end: w[1] } : null; }
  if (L.mode === 'cycle') {
    const P = L.lockMs + L.openMs, ph = (t - L.start) % P;
    if (t < L.start || ph < L.lockMs) return null;
    return { start: t - ph + L.lockMs, end: t - ph + P };
  }
  return null;
}
function nextWindowStart(L, t) { // first window start strictly after t
  if (L.mode === 'schedule') {
    let tt = t;
    for (let i = 0; i < 6; i++) { const s = schedIntervals(L, tt).map(w => w[0]).filter(s => s > t).sort((a, b) => a - b)[0]; if (s) return s; tt += 7 * 86400000; }
    return null;
  }
  const P = L.lockMs + L.openMs;
  const k = Math.max(0, Math.floor((t - L.start - L.lockMs) / P) + 1);
  return L.start + k * P + L.lockMs;
}

/* ---------- unlocking ---------- */
async function openCapsule(ct) {
  let out = await engine.decrypt(ct);
  while (out.startsWith(ARMOR)) out = await engine.decrypt(out); // added time wraps the older seal
  return JSON.parse(out).n;
}
async function seal(t, num) {
  const round = engine.roundFor(t);
  return { round, at: engine.timeOf(round), ct: await engine.encrypt(round, JSON.stringify({ n: num })) };
}

async function process(L) {
  if (busy[L.id] || L.opened) return;
  if (errs[L.id] && now() < errs[L.id].retryAt) return;
  const t = now();
  const safeDue = L.safety && t >= L.safety.at;
  const mainDue = L.capsule && t >= L.capsule.at;
  if (!safeDue && !mainDue) return;
  busy[L.id] = true; render();
  try {
    if (safeDue) {
      const n = await openCapsule(L.safety.ct);
      L.opened = { num: n, how: 'safety', at: now() }; L.capsule = null; L.safety = null; delete mem[L.id];
    } else if (!repeating(L)) {
      const n = await openCapsule(L.capsule.ct);
      L.opened = { num: n, how: 'time', at: now() }; L.capsule = null; L.safety = null;
    } else {
      const n = await openCapsule(L.capsule.ct);
      const t2 = now(), w = currentWindow(L, t2);
      const next = nextWindowStart(L, w ? w.end - 1 : t2);
      L.capsule = await seal(next, n); // re-seal for the next window before showing anything
      if (w) mem[L.id] = { num: n, until: w.end, win: w.start };
    }
    delete errs[L.id]; touch(L); save();
  } catch (e) {
    let msg = 'Could not reach drand to unlock. Retrying shortly.';
    if (e.message === 'TOO_EARLY') msg = Math.abs(skew) > 60000 ? 'Your device clock is behind. Set it to the correct time to unlock.' : 'Not quite time yet. Retrying shortly.';
    errs[L.id] = { msg, retryAt: now() + 15000 };
  } finally { delete busy[L.id]; render(); }
}

async function extend(L, ms) {
  if (busy[L.id] || !L.capsule || repeating(L)) return;
  busy[L.id] = true; render();
  try {
    const r = engine.roundFor(L.capsule.at + ms);
    L.capsule = { round: r, at: engine.timeOf(r), ct: await engine.encrypt(r, L.capsule.ct) };
    L.unlockAt += ms;
    if (L.safety) { const s = engine.roundFor(L.safety.at + ms); L.safety = { round: s, at: engine.timeOf(s), ct: await engine.encrypt(s, L.safety.ct) }; }
    touch(L); save();
  } finally { delete busy[L.id]; render(); }
}

/* ---------- formatting ---------- */
function dur(ms) {
  ms = Math.max(0, ms); const s = Math.floor(ms / 1000), d = Math.floor(s / 86400), h = Math.floor(s % 86400 / 3600), m = Math.floor(s % 3600 / 60), x = s % 60;
  const p = n => String(n).padStart(2, '0'); return (d ? d + 'd ' : '') + (d || h ? p(h) + 'h ' : '') + p(m) + 'm ' + p(x) + 's';
}
const when = ms => new Date(ms).toLocaleString(undefined, { weekday: 'short', month: 'short', day: 'numeric', hour: 'numeric', minute: '2-digit' });
function unitTxt(ms) { for (const [u, n] of [[604800000, 'week'], [86400000, 'day'], [3600000, 'hour'], [60000, 'minute']]) if (ms % u === 0) { const v = ms / u; return v + ' ' + n + (v === 1 ? '' : 's'); } return dur(ms); }
function ruleTxt(L) {
  if (!repeating(L)) return 'Unlocks ' + when(L.unlockAt);
  if (L.mode === 'cycle') return 'Locked ' + unitTxt(L.lockMs) + ', then visible ' + unitTxt(L.openMs) + ', repeating';
  const ds = L.days.length === 7 ? 'Every day' : L.days.slice().sort().map(d => DAYN[d]).join(', ');
  return ds + ', ' + L.from + ' to ' + L.to;
}
const esc = s => String(s).replace(/[&<>"]/g, c => ({ '&': '&amp;', '<': '&lt;', '>': '&gt;', '"': '&quot;' }[c]));

/* ---------- render ---------- */
function render() {
  renderSync();
  const all = live(), pinned = all.filter(l => l.pinned), rest = all.filter(l => !l.pinned);
  $('pinnedSec').hidden = !pinned.length;
  $('pinned').innerHTML = pinned.map(cardHTML).join('');
  $('restTitle').hidden = !rest.length && !!pinned.length;
  $('list').innerHTML = rest.length ? rest.map(cardHTML).join('')
    : pinned.length ? '' : '<div class="empty">No locks yet. Seal a number above and it will appear here.</div>';
}
function cardHTML(L) {
  const t = now();
  {
    const m = mem[L.id] && mem[L.id].until > t ? mem[L.id] : null;
    if (mem[L.id] && !m) delete mem[L.id];
    const num = L.opened ? L.opened.num : m ? m.num : null;
    const open = num !== null;
    const usedUp = m && L.once && L.usedWin === m.win && !(peeks[L.id] > t);
    const needsPeek = open && (L.peekSec || (m && L.once));
    const visible = open && !usedUp && (!needsPeek || peeks[L.id] > t);
    let pill = open ? ['open', 'Unlocked'] : busy[L.id] ? ['busy', 'Working'] : ['locked', 'Locked'];
    let count;
    const nextAt = Math.min(L.capsule ? L.capsule.at : Infinity, L.safety ? L.safety.at : Infinity);
    if (busy[L.id]) count = 'Fetching the drand key and unlocking…';
    else if (errs[L.id]) count = errs[L.id].msg;
    else if (usedUp) count = 'Already revealed this window · hides in ' + dur(m.until - t);
    else if (visible && needsPeek) count = 'Covering again in ' + dur(peeks[L.id] - t);
    else if (L.opened) count = L.opened.how === 'safety' ? 'Opened by the safety unlock' : 'Unlocked ' + when(L.opened.at);
    else if (m) count = 'Hides in ' + dur(m.until - t);
    else if (nextAt < Infinity) count = (nextAt > t ? 'Opens in ' + dur(nextAt - t) + ' · ' : 'Opening · ') + when(nextAt) + (L.safety && nextAt === L.safety.at ? ' (safety unlock)' : '');
    else count = 'No upcoming window';
    let acts = '';
    if (open && needsPeek && !visible && !usedUp) acts += `<button class="btn" data-act="peek" data-id="${L.id}">Reveal</button>`;
    if (visible && needsPeek) acts += `<button class="btn" data-act="unpeek" data-id="${L.id}">Cover now</button>`;
    if (!open && !repeating(L) && L.capsule && !busy[L.id]) acts += `<button class="btn" data-act="ext" data-ms="3600000" data-id="${L.id}">+1 hour</button><button class="btn" data-act="ext" data-ms="86400000" data-id="${L.id}">+1 day</button><button class="btn" data-act="ext" data-ms="604800000" data-id="${L.id}">+1 week</button>`;
    if (confirmDel === L.id) acts += `<span class="rule">Delete this lock? ${open ? '' : 'The number will be gone for good.'}</span><button class="btn danger" data-act="delgo" data-id="${L.id}">Delete</button><button class="btn" data-act="delno">Keep</button>`;
    else acts += `<button class="btn" data-act="pin" data-id="${L.id}">${L.pinned ? 'Unpin' : 'Pin to top'}</button><button class="btn danger" data-act="del" data-id="${L.id}">Delete</button>`;
    const extra = [];
    if (L.safety) extra.push('safety unlock ' + when(L.safety.at));
    if (L.once && repeating(L)) extra.push('one reveal per window');
    if (L.peekSec) extra.push('brief reveal ' + L.peekSec + 's');
    return `<article class="card${visible ? ' open' : ''}${L.pinned ? ' pinned' : ''}">
      <div class="top"><h3>${esc(L.label)}</h3><span class="pill ${pill[0]}">${pill[1]}</span></div>
      <div class="digits${visible ? '' : ' hidden'}">${visible ? esc(num) : '••••••'}</div>
      <div class="count">${esc(count)}</div>
      <div class="rule">${esc(ruleTxt(L))}${extra.length ? ' · ' + esc(extra.join(' · ')) : ''}</div>
      <div class="actions">${acts}</div>
    </article>`;
  }
}

/* ---------- list actions ---------- */
function onCardClick(e) {
  const b = e.target.closest('button[data-act]'); if (!b) return;
  const L = locks.find(l => l.id === b.dataset.id), a = b.dataset.act, t = now();
  if (a === 'peek') { const m = mem[L.id]; peeks[L.id] = t + (L.peekSec ? L.peekSec * 1000 : 30000); if (m && L.once) { L.usedWin = m.win; touch(L); save(); } }
  if (a === 'unpeek') delete peeks[L.id];
  if (a === 'pin') { L.pinned = !L.pinned; touch(L); save(); }
  if (a === 'ext') { extend(L, +b.dataset.ms); return; }
  if (a === 'del') confirmDel = L.id;
  if (a === 'delno') confirmDel = null;
  if (a === 'delgo') { // keep a deletion marker so other devices delete it too
    const rev = (L.rev || 0) + 1, id = L.id;
    Object.keys(L).forEach(k => delete L[k]); Object.assign(L, { id, deleted: true, rev, updated: Date.now() });
    delete mem[id]; confirmDel = null; save();
  }
  render();
}
$('list').addEventListener('click', onCardClick);
$('pinned').addEventListener('click', onCardClick);

/* ---------- form ---------- */
$('modes').addEventListener('click', e => {
  const b = e.target.closest('.mode'); if (!b) return; mode = b.dataset.mode;
  document.querySelectorAll('.mode').forEach(m => m.setAttribute('aria-pressed', String(m === b)));
  ['until', 'duration', 'schedule', 'cycle'].forEach(m => { $('m-' + m).hidden = m !== mode; });
  $('m-schedule').style.display = mode === 'schedule' ? 'flex' : '';
  $('repeatNote').hidden = !(mode === 'schedule' || mode === 'cycle');
});
$('days').innerHTML = DAYN.map((d, i) => `<button type="button" class="day" data-d="${i}" aria-pressed="${days.includes(i)}">${d}</button>`).join('');
$('days').addEventListener('click', e => {
  const b = e.target.closest('.day'); if (!b) return; const d = +b.dataset.d;
  days = days.includes(d) ? days.filter(x => x !== d) : [...days, d]; b.setAttribute('aria-pressed', String(days.includes(d)));
});
$('o-safe').addEventListener('change', () => { $('o-safen').disabled = $('o-safeunit').disabled = !$('o-safe').checked; });
function setDefaultDate() { // today's date and the current time
  const d = new Date(), p = n => String(n).padStart(2, '0');
  $('f-date').value = d.getFullYear() + '-' + p(d.getMonth() + 1) + '-' + p(d.getDate());
  $('f-time').value = p(d.getHours()) + ':' + p(d.getMinutes());
}
setDefaultDate();

$('form').addEventListener('submit', async e => {
  e.preventDefault();
  const err = $('err'); err.hidden = true;
  const fail = m => { err.textContent = m; err.hidden = false; };
  const t = now(), n = id => +$(id).value;
  const num = $('f-num').value.trim(); if (!num) return fail('Enter the number you want to lock.');
  const L = { id: Math.random().toString(36).slice(2) + t.toString(36), label: $('f-label').value.trim() || 'Untitled lock', mode, created: t, rev: 1, updated: t };
  if (mode === 'until') {
    const v = new Date($('f-date').value + 'T' + ($('f-time').value || '00:00')).getTime();
    if (!v) return fail('Pick an unlock date and time.');
    if (v <= t) return fail('That time has already passed. Pick a later date or time.');
    L.unlockAt = v;
  }
  if (mode === 'duration') { if (!(n('f-dur') > 0)) return fail('Enter how long to lock it.'); L.unlockAt = t + n('f-dur') * n('f-durunit'); }
  if (mode === 'schedule') { if (!days.length) return fail('Pick at least one day.'); if ($('f-from').value === $('f-to').value) return fail('Start and end times must differ.'); L.days = days.slice(); L.from = $('f-from').value; L.to = $('f-to').value; }
  if (mode === 'cycle') { if (!(n('f-cl') > 0 && n('f-co') > 0)) return fail('Enter both cycle lengths.'); L.lockMs = n('f-cl') * n('f-clunit'); L.openMs = n('f-co') * n('f-counit'); L.start = t; }
  L.peekSec = $('o-peek').checked ? Math.max(1, n('o-peeksec') || 10) : 0;
  L.once = $('o-once').checked && repeating(L);
  L.pinned = $('f-pin').checked;
  const first = repeating(L) ? nextWindowStart(L, t) : L.unlockAt;
  if (!first) return fail('That schedule has no upcoming window.');
  const btn = $('submit'); btn.disabled = true; btn.textContent = 'Sealing…';
  try {
    L.capsule = await seal(first, num);
    if ($('o-safe').checked) {
      const safeAt = t + (Math.max(1, n('o-safen')) || 7) * n('o-safeunit');
      if (repeating(L) || safeAt < L.unlockAt) L.safety = await seal(safeAt, num);
    }
    locks.unshift(L); save();
    $('f-num').value = ''; $('f-label').value = ''; $('f-pin').checked = false; setDefaultDate();
  } catch (ex) { fail('Sealing failed: ' + ex.message); }
  finally { btn.disabled = false; btn.textContent = 'Seal it'; render(); }
});

/* ---------- backup ---------- */
let exportText = '';
$('exp').addEventListener('click', () => {
  exportText = JSON.stringify({ app: 'number-time-lock', v: 2, exported: new Date().toISOString(), locks: locks.filter(l => !l.deleted) });
  const ta = $('expText'); ta.value = exportText; ta.hidden = false; $('copy').hidden = false; $('dl').hidden = false;
});
$('copy').addEventListener('click', async () => {
  try { await navigator.clipboard.writeText(exportText); $('copy').textContent = 'Copied'; }
  catch (e) { $('expText').select(); $('copy').textContent = 'Press Ctrl+C to copy'; }
  setTimeout(() => { $('copy').textContent = 'Copy'; }, 2500);
});
$('dl').addEventListener('click', () => {
  const a = document.createElement('a');
  a.href = URL.createObjectURL(new Blob([exportText], { type: 'application/json' }));
  a.download = 'number-time-lock-backup-' + new Date().toISOString().slice(0, 10) + '.json';
  document.body.appendChild(a); a.click(); a.remove();
});
function restore(text) {
  const msg = $('impMsg'); msg.hidden = false;
  try {
    const data = JSON.parse(text.trim());
    if (!data || !Array.isArray(data.locks)) throw new Error();
    const res = merge(data.locks.filter(l => l && l.id));
    save(); render();
    msg.className = 'ok'; msg.textContent = res.added ? 'Restored ' + res.added + ' lock' + (res.added === 1 ? '' : 's') + '.' : 'Nothing new to restore. Those locks are already here.';
  } catch (e) { msg.className = 'err'; msg.textContent = "That doesn't look like a backup from this app. Paste the whole text, starting with {."; }
}
$('imp').addEventListener('click', () => restore($('impText').value));
$('impFile').addEventListener('change', e => { const f = e.target.files[0]; if (f) f.text().then(restore); e.target.value = ''; });

/* ---------- merge (used by sync and restore) ---------- */
const newer = (a, b) => ((a.rev || 0) - (b.rev || 0)) || ((a.updated || 0) - (b.updated || 0));
function merge(remote) {
  let added = 0, changed = false, needPush = false;
  const byId = new Map(locks.map(l => [l.id, l])), seen = new Set();
  for (const r of remote) {
    seen.add(r.id);
    const l = byId.get(r.id);
    if (!l) { locks.push(r); if (!r.deleted) added++; changed = true; continue; }
    const c = newer(r, l);
    if (c > 0) { Object.keys(l).forEach(k => delete l[k]); Object.assign(l, r); changed = true; if (r.deleted) delete mem[r.id]; }
    else if (c < 0) needPush = true;
  }
  if (locks.some(l => !seen.has(l.id))) needPush = true;
  return { added, changed, needPush };
}

/* ---------- sync through a private GitHub repository ---------- */
const SYNC_KEY = 'timelock.sync', FILE = '/contents/timelock-locks.json';
let sync = null, sha = null, syncing = false, again = false, pushTimer = null, syncState = { ok: null, msg: '', at: 0 };
try { sync = JSON.parse(localStorage.getItem(SYNC_KEY) || 'null'); } catch (e) {}
const b64enc = s => btoa(unescape(encodeURIComponent(s)));
const b64dec = s => decodeURIComponent(escape(atob(s.replace(/\s/g, ''))));
function gh(method, path, body, cfg = sync) {
  return fetch('https://api.github.com/repos/' + cfg.repo + path, {
    method, cache: 'no-store',
    headers: Object.assign({ Authorization: 'Bearer ' + cfg.token, Accept: 'application/vnd.github+json' }, body ? { 'Content-Type': 'application/json' } : {}),
    body: body ? JSON.stringify(body) : undefined
  });
}
function ghError(status) {
  if (status === 401) return 'GitHub rejected the access key. It may have expired. Create a new one and reconnect.';
  if (status === 403) return "The access key doesn't have permission to change files. It needs Contents: Read and write.";
  if (status === 404) return "Can't find that repository, or the access key isn't allowed to use it.";
  return 'GitHub returned an error (' + status + '). Retrying later.';
}
async function pull() {
  const r = await gh('GET', FILE + '?t=' + Date.now());
  if (r.status === 404) { sha = null; return []; }
  if (!r.ok) throw new Error(ghError(r.status));
  const j = await r.json(); sha = j.sha;
  const data = JSON.parse(b64dec(j.content));
  return Array.isArray(data.locks) ? data.locks : [];
}
async function push() {
  const body = { message: 'Update locks', content: b64enc(JSON.stringify({ app: 'number-time-lock', v: 2, updated: new Date().toISOString(), locks }, null, 1)) };
  if (sha) body.sha = sha;
  const r = await gh('PUT', FILE, body);
  if (r.status === 409 || r.status === 422) return false; // someone else wrote first
  if (!r.ok) throw new Error(ghError(r.status));
  sha = (await r.json()).content.sha; return true;
}
async function syncNow() {
  if (!sync) return;
  if (syncing) { again = true; return; }
  syncing = true; renderSync();
  try {
    for (let i = 0; i < 4; i++) {
      const res = merge(await pull());
      if (res.changed) { saveLocal(); render(); }
      if (!res.needPush || await push()) break;
    }
    syncState = { ok: true, msg: '', at: Date.now() };
  } catch (e) {
    syncState = { ok: false, msg: e instanceof TypeError ? "Can't reach GitHub. Changes will sync when you're back online." : e.message, at: syncState.at };
  } finally {
    syncing = false; renderSync();
    if (again) { again = false; syncNow(); }
  }
}
function schedulePush() { if (!sync) return; clearTimeout(pushTimer); pushTimer = setTimeout(syncNow, 1500); }
function renderSync() {
  $('syncOff').hidden = !!sync; $('syncOn').hidden = !sync;
  if (!sync) return;
  $('syncRepo').textContent = sync.repo;
  const s = $('syncStatus');
  if (syncing) { s.className = 'net'; s.textContent = 'Syncing…'; }
  else if (syncState.ok === false) { s.className = 'err'; s.textContent = syncState.msg; }
  else if (syncState.at) { s.className = 'ok'; s.textContent = 'Synced ' + new Date(syncState.at).toLocaleTimeString([], { hour: 'numeric', minute: '2-digit' }); }
  else { s.className = 'net'; s.textContent = 'Not synced yet'; }
}
async function connect(repo, token) {
  const msg = $('syncMsg'); msg.hidden = false; msg.className = 'net'; msg.textContent = 'Checking…';
  repo = repo.trim().replace(/^https?:\/\/github\.com\//, '').replace(/\.git$|\/$/g, '');
  token = token.trim();
  if (!/^[\w.-]+\/[\w.-]+$/.test(repo)) { msg.className = 'err'; msg.textContent = 'Enter the repository as owner/name, for example withstandingspring/timelock-data.'; return false; }
  if (!token) { msg.className = 'err'; msg.textContent = 'Paste your access key.'; return false; }
  try {
    const r = await gh('GET', '', null, { repo, token });
    if (!r.ok) { msg.className = 'err'; msg.textContent = ghError(r.status); return false; }
    const info = await r.json();
    if (!info.private) { msg.className = 'err'; msg.textContent = 'That repository is public. Unlocked numbers would be visible to anyone, so use a private repository.'; return false; }
  } catch (e) { msg.className = 'err'; msg.textContent = "Can't reach GitHub. Check your connection."; return false; }
  sync = { repo, token }; sha = null;
  try { localStorage.setItem(SYNC_KEY, JSON.stringify(sync)); } catch (e) {}
  msg.hidden = true; $('s-token').value = '';
  await syncNow(); render(); return true;
}
$('syncForm').addEventListener('submit', e => { e.preventDefault(); connect($('s-repo').value, $('s-token').value); });
$('syncNow').addEventListener('click', syncNow);
$('syncOff2').addEventListener('click', () => { $('syncConfirm').hidden = false; });
$('syncKeep').addEventListener('click', () => { $('syncConfirm').hidden = true; });
$('syncDisc').addEventListener('click', () => {
  sync = null; sha = null; syncState = { ok: null, msg: '', at: 0 };
  try { localStorage.removeItem(SYNC_KEY); } catch (e) {}
  $('syncConfirm').hidden = true; $('linkBox').hidden = true; renderSync();
});
$('syncLink').addEventListener('click', async () => {
  const link = location.origin + location.pathname + '#sync=' + b64enc(JSON.stringify(sync));
  const box = $('linkBox'); box.hidden = false; $('linkText').value = link;
  try { await navigator.clipboard.writeText(link); $('linkHint').textContent = 'Copied. Open it on your other device. It contains your access key, so only send it to yourself.'; }
  catch (e) { $('linkText').select(); $('linkHint').textContent = 'Copy this link and open it on your other device. It contains your access key, so only send it to yourself.'; }
});
function setupFromLink() {
  const m = location.hash.match(/^#sync=(.+)$/); if (!m) return;
  history.replaceState(null, '', location.pathname + location.search);
  try { const cfg = JSON.parse(b64dec(decodeURIComponent(m[1]))); if (cfg.repo && cfg.token) connect(cfg.repo, cfg.token); } catch (e) {}
}
setupFromLink();
window.addEventListener('hashchange', setupFromLink);

/* ---------- network clock check ---------- */
async function checkNet() {
  const r = await engine.latestTime();
  if (!r) { netOk = false; $('net').textContent = "Can't reach drand right now. You can still seal numbers. Unlocking needs a connection."; return; }
  netOk = true; skew = r.time - Date.now();
  $('net').textContent = 'Connected to drand · round ' + r.round.toLocaleString();
  const ca = $('clockAlert');
  if (Math.abs(skew) > 60000) { ca.hidden = false; ca.textContent = 'Your device clock is ' + dur(Math.abs(skew)) + (skew > 0 ? ' behind' : ' ahead') + ' the real time. Countdowns may be off, and locks can only unlock once your clock is correct.'; }
  else ca.hidden = true;
}

/* ---------- start ---------- */
locks = load();
render();
checkNet();
setInterval(() => { locks.forEach(L => { process(L); }); render(); }, 1000);
setInterval(checkNet, 5 * 60000);
syncNow();
setInterval(() => { if (!document.hidden) syncNow(); }, 60000);
document.addEventListener('visibilitychange', () => { if (!document.hidden) { syncNow(); locks.forEach(L => { process(L); }); render(); } });
})();
