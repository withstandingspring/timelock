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
/* Exclusions for repeating cycles: periods (days + all day or a time range) when no window shows.
   A time range that ends earlier than it starts runs from that day into the next morning.
   A window that overlaps an exclusion at all is skipped. Times use the time zone saved with the lock. */
const LOCAL_TZ = Intl.DateTimeFormat().resolvedOptions().timeZone || 'UTC';
const partFmt = {}, WD = { Sun: 0, Mon: 1, Tue: 2, Wed: 3, Thu: 4, Fri: 5, Sat: 6 };
function localParts(ms, tz) {
  const f = partFmt[tz] || (partFmt[tz] = new Intl.DateTimeFormat('en-US', { timeZone: tz, weekday: 'short', hour: '2-digit', minute: '2-digit', hourCycle: 'h23' }));
  const p = {}; for (const x of f.formatToParts(new Date(ms))) p[x.type] = x.value;
  return { wd: WD[p.weekday], m: (+p.hour % 24) * 60 + +p.minute };
}
const toMin = s => { const [h, m] = s.split(':').map(Number); return h * 60 + m; };
function inExclusion(ms, ex) {
  const { wd, m } = localParts(ms, ex.tz || LOCAL_TZ), prev = (wd + 6) % 7;
  return ex.rules.some(r => {
    if (r.allDay) return r.days.includes(wd);
    const f = toMin(r.from), e = toMin(r.to);
    if (f < e) return r.days.includes(wd) && m >= f && m < e;
    return (r.days.includes(wd) && m >= f) || (r.days.includes(prev) && m < e); // runs past midnight
  });
}
function windowExcluded(L, s, e) {
  if (!L.excl || !L.excl.rules || !L.excl.rules.length) return false;
  const step = e - s <= 6 * 3600000 ? 60000 : 900000;
  for (let t = s; t < e; t += step) if (inExclusion(t, L.excl)) return true;
  return inExclusion(e - 60000, L.excl);
}

function currentWindow(L, t) {
  if (L.mode === 'schedule') { const w = schedIntervals(L, t).find(([s, e]) => t >= s && t < e); return w ? { start: w[0], end: w[1] } : null; }
  if (L.mode === 'cycle') {
    const P = L.lockMs + L.openMs, ph = (t - L.start) % P;
    if (t < L.start || ph < L.lockMs) return null;
    const w = { start: t - ph + L.lockMs, end: t - ph + P };
    return windowExcluded(L, w.start, w.end) ? null : w;
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
  for (let w = L.start + k * P + L.lockMs, i = 0; i < 5000; w += P, i++) if (!windowExcluded(L, w, w + L.openMs)) return w;
  return null; // everything excluded
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

/* Unlocked numbers live only on this device. The synced lock keeps a sealed copy for an
   already-published round, so other devices open it from drand themselves. */
const PLAIN_KEY = 'timelock.plain';
let plain = {};
try { plain = JSON.parse(localStorage.getItem(PLAIN_KEY) || '{}') || {}; } catch (e) {}
function savePlain() { try { localStorage.setItem(PLAIN_KEY, JSON.stringify(plain)); } catch (e) {} }
let migrating = false;
async function migrate() { // move numbers saved by older versions out of the synced data
  if (migrating) return; migrating = true;
  try {
    for (const L of locks) {
      if (!L.opened || L.opened.num == null) continue;
      const n = L.opened.num;
      plain[L.id] = n; savePlain();
      if (!L.opened.ct) L.opened.ct = (await seal(Math.min(L.opened.at || now(), now()), n)).ct;
      delete L.opened.num; touch(L); save();
    }
  } catch (e) { /* retried on the next sync */ } finally { migrating = false; }
}

async function process(L) {
  if (busy[L.id] || L.deleted) return;
  if (errs[L.id] && now() < errs[L.id].retryAt) return;
  if (L.opened) { // unlocked elsewhere or restored: fetch the key to show it here
    if (plain[L.id] != null || !L.opened.ct) return;
    busy[L.id] = true; render();
    try { plain[L.id] = await openCapsule(L.opened.ct); savePlain(); delete errs[L.id]; }
    catch (e) { errs[L.id] = { msg: "Unlocked, but couldn't reach drand to show it on this device. Retrying shortly.", retryAt: now() + 15000 }; }
    finally { delete busy[L.id]; render(); }
    return;
  }
  const t = now();
  const safeDue = L.safety && t >= L.safety.at;
  const mainDue = L.capsule && t >= L.capsule.at;
  if (!safeDue && !mainDue) return;
  busy[L.id] = true; render();
  try {
    if (safeDue) {
      const n = await openCapsule(L.safety.ct);
      plain[L.id] = n; savePlain();
      L.opened = { how: 'safety', at: now(), ct: L.safety.ct }; L.capsule = null; L.safety = null; delete mem[L.id];
    } else if (!repeating(L)) {
      const n = await openCapsule(L.capsule.ct);
      plain[L.id] = n; savePlain();
      L.opened = { how: 'time', at: now(), ct: L.capsule.ct }; L.capsule = null; L.safety = null;
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
    touch(L); save(); bookAll();
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
  if (L.mode === 'cycle') return 'Locked ' + unitTxt(L.lockMs) + ', then visible ' + unitTxt(L.openMs) + ', repeating from ' + when(L.start) + (L.excl && L.excl.rules.length ? ' · not during: ' + L.excl.rules.map(exclTxt).join('; ') : '');
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
    const num = L.opened ? (plain[L.id] != null ? plain[L.id] : L.opened.num != null ? L.opened.num : null) : m ? m.num : null;
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
    else acts += (ntfyTopic && !L.opened ? `<button class="btn" data-act="notify" data-id="${L.id}">Notify: ${!L.notify ? 'off' : L.notify === 'quiet' ? 'not during quiet hours' : 'always'}</button>` : '') + (L.mode === 'cycle' && !L.opened ? `<button class="btn" data-act="excl" data-id="${L.id}">Exclusions</button>` : '') + `<button class="btn" data-act="pin" data-id="${L.id}">${L.pinned ? 'Unpin' : 'Pin to top'}</button><button class="btn danger" data-act="del" data-id="${L.id}">Delete</button>`;
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
  if (a === 'excl') { openExEdit(L); return; }
  if (a === 'notify') { // cycles always -> not during quiet hours -> off
    setNotify(L, !L.notify ? 'always' : L.notify === 'quiet' ? 'off' : 'quiet');
    if (!L.notify) cancelBookings(L); touch(L); save(); if (L.notify) bookAll();
  }
  if (a === 'ext') { extend(L, +b.dataset.ms); return; }
  if (a === 'del') confirmDel = L.id;
  if (a === 'delno') confirmDel = null;
  if (a === 'delgo') { // keep a deletion marker so other devices delete it too
    cancelBookings(L);
    const rev = (L.rev || 0) + 1, id = L.id;
    Object.keys(L).forEach(k => delete L[k]); Object.assign(L, { id, deleted: true, rev, updated: Date.now() });
    delete mem[id]; delete plain[id]; savePlain(); confirmDel = null; save();
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
function setCycleStart(d) {
  const p = n => String(n).padStart(2, '0');
  $('f-cdate').value = d.getFullYear() + '-' + p(d.getMonth() + 1) + '-' + p(d.getDate());
  $('f-ctime').value = p(d.getHours()) + ':' + p(d.getMinutes());
  cyclePreview();
}
function cycleStart() { const v = new Date($('f-cdate').value + 'T' + ($('f-ctime').value || '00:00')).getTime(); return v || null; }
function cyclePreview() { // show the next few windows so the timing is easy to check
  const s = cycleStart(), lock = +$('f-cl').value * +$('f-clunit').value, open = +$('f-co').value * +$('f-counit').value;
  if (!s || !(lock > 0) || !(open > 0)) { $('cPreview').textContent = ''; return; }
  const L = { mode: 'cycle', start: s, lockMs: lock, openMs: open, excl: exRules.length ? { tz: LOCAL_TZ, rules: exRules } : null }, out = [];
  const tf = ms => new Date(ms).toLocaleString(undefined, { weekday: 'short', hour: 'numeric', minute: '2-digit' });
  let w = nextWindowStart(L, now());
  for (let i = 0; i < 3 && w; i++) { out.push(tf(w) + ' to ' + new Date(w + open).toLocaleTimeString(undefined, { hour: 'numeric', minute: '2-digit' })); w = nextWindowStart(L, w); }
  $('cPreview').textContent = out.length ? 'Next visible: ' + out.join(' · ') : 'With these exclusions it would never be visible.';
}
/* exclusion editor */
let exRules = [];
const dayList = days => days.length === 7 ? 'Every day' : days.slice().sort((a, b) => ((a + 6) % 7) - ((b + 6) % 7)).map(d => DAYN[d]).join(', ');
const exclTxt = r => dayList(r.days) + ' ' + (r.allDay ? 'all day' : r.from + '–' + r.to + (toMin(r.to) <= toMin(r.from) ? ' (next morning)' : ''));
// One editor component, used by the New lock form and by "Exclusions" on an existing lock.
function exEditor(listEl, addBtn, getRules, onChange) {
  const draw = () => {
    listEl.innerHTML = getRules().map((r, i) => `<div class="exRule">
    <div class="days">${[1, 2, 3, 4, 5, 6, 0].map(d => `<button type="button" class="day" data-ex="${i}" data-d="${d}" aria-pressed="${r.days.includes(d)}">${DAYN[d]}</button>`).join('')}</div>
    <div class="row">
      <label class="check" style="align-self:end"><input type="checkbox" data-exall="${i}" ${r.allDay ? 'checked' : ''}><span>All day</span></label>
      <label ${r.allDay ? 'hidden' : ''}>From<input type="time" data-exfrom="${i}" value="${r.from}"></label>
      <label ${r.allDay ? 'hidden' : ''}>Until<input type="time" data-exto="${i}" value="${r.to}"></label>
    </div>
    <div><button type="button" class="btn danger" data-exdel="${i}">Remove</button></div>
  </div>`).join('');
    onChange();
  };
  addBtn.addEventListener('click', () => { getRules().push({ days: [], allDay: false, from: '18:00', to: '10:00' }); draw(); });
  listEl.addEventListener('click', e => {
    const d = e.target.closest('[data-ex]'), del = e.target.closest('[data-exdel]'), rules = getRules();
    if (d) { const r = rules[+d.dataset.ex], v = +d.dataset.d; r.days = r.days.includes(v) ? r.days.filter(x => x !== v) : [...r.days, v]; draw(); }
    if (del) { rules.splice(+del.dataset.exdel, 1); draw(); }
  });
  listEl.addEventListener('change', e => { const t = e.target; if (t.dataset.exall != null) { getRules()[+t.dataset.exall].allDay = t.checked; draw(); } });
  listEl.addEventListener('input', e => {
    const t = e.target, rules = getRules();
    if (t.dataset.exfrom != null) rules[+t.dataset.exfrom].from = t.value || '00:00';
    if (t.dataset.exto != null) rules[+t.dataset.exto].to = t.value || '00:00';
    onChange();
  });
  return draw;
}
function exProblem(rules) {
  if (rules.some(r => !r.days.length)) return 'Pick at least one day for each exclusion, or remove it.';
  if (rules.some(r => !r.allDay && r.from === r.to)) return "An exclusion's start and end times must differ. Tick All day for a whole day.";
  return null;
}
const renderEx = exEditor($('exList'), $('exAdd'), () => exRules, () => cyclePreview());

/* editing exclusions on an existing repeating cycle */
let editId = null, editRules = [];
const editLock = () => locks.find(l => l.id === editId && !l.deleted);
const fmtWin = ms => new Date(ms).toLocaleString(undefined, { weekday: 'short', month: 'short', day: 'numeric', hour: 'numeric', minute: '2-digit' });
function cycleWindowStartAt(L, at) { // start of the cycle window a sealed time belongs to
  const P = L.lockMs + L.openMs; return L.start + Math.floor((at - L.start - L.lockMs + 5000) / P) * P + L.lockMs;
}
function editPreview() {
  const L = editLock(); if (!L) return;
  const Ln = Object.assign({}, L, { excl: editRules.length ? { tz: LOCAL_TZ, rules: editRules } : null });
  const p = exProblem(editRules); if (p) { $('exEditPreview').textContent = ''; return; }
  const out = []; let w = nextWindowStart(Ln, now());
  for (let i = 0; i < 3 && w; i++) { out.push(new Date(w).toLocaleString(undefined, { weekday: 'short', hour: 'numeric', minute: '2-digit' })); w = nextWindowStart(Ln, w); }
  $('exEditPreview').textContent = out.length ? 'With these rules, next visible: ' + out.join(' · ') : 'With these exclusions it would never be visible.';
}
const drawEdit = exEditor($('exEditList'), $('exEditAdd'), () => editRules, editPreview);
function openExEdit(L) {
  editId = L.id; editRules = JSON.parse(JSON.stringify((L.excl && L.excl.rules) || []));
  $('exEditTitle').textContent = 'Exclusions for "' + L.label + '"'; $('exEditErr').hidden = true;
  $('exEdit').hidden = false; drawEdit(); $('exEdit').scrollIntoView({ behavior: 'smooth', block: 'start' });
}
function closeExEdit() { editId = null; $('exEdit').hidden = true; }
$('exEditCancel').addEventListener('click', closeExEdit);
$('exEditSave').addEventListener('click', async () => {
  const L = editLock(), err = $('exEditErr'), btn = $('exEditSave');
  const fail = m => { err.textContent = m; err.hidden = false; };
  if (!L) return closeExEdit();
  if (exProblem(editRules)) return fail(exProblem(editRules));
  const excl = editRules.length ? { tz: LOCAL_TZ, rules: JSON.parse(JSON.stringify(editRules)) } : null;
  const Ln = Object.assign({}, L, { excl }), t = now();
  if (!nextWindowStart(Ln, t)) return fail('With these exclusions the number would never be visible.');
  if (busy[L.id]) return fail('This lock is busy unlocking. Try again in a moment.');
  busy[L.id] = true; btn.disabled = true; btn.textContent = 'Saving…';
  let note = '';
  try {
    if (mem[L.id]) { // window open here, so the number is known: re-seal properly under the new rules
      L.excl = excl;
      const w = currentWindow(L, t), next = nextWindowStart(L, w ? w.end - 1 : t);
      L.capsule = await seal(next, mem[L.id].num);
      if (!w) delete mem[L.id];
      note = 'Next visible ' + fmtWin(L.capsule.at) + '.';
    } else if (L.capsule) {
      const ws = cycleWindowStartAt(L, L.capsule.at);
      if (windowExcluded(Ln, ws, ws + L.openMs)) { // sealed window is now excluded: wrap the seal to the next allowed one
        const target = nextWindowStart(Ln, ws), r = engine.roundFor(target);
        L.capsule = { round: r, at: engine.timeOf(r), ct: await engine.encrypt(r, L.capsule.ct) };
        note = 'The next window was excluded, so the seal moved to ' + fmtWin(L.capsule.at) + '.';
      } else {
        note = 'Next visible ' + fmtWin(L.capsule.at) + '.';
        const earliest = nextWindowStart(Ln, t);
        if (earliest && earliest < ws) note += ' Removed exclusions take effect after that unlock.';
      }
      L.excl = excl;
    } else L.excl = excl;
    touch(L); save(); bookAll(); closeExEdit();
    toast('Exclusions saved. ' + note);
  } catch (e) { fail('Saving failed: ' + e.message); }
  finally { delete busy[L.id]; btn.disabled = false; btn.textContent = 'Save exclusions'; render(); }
});
function toast(msg) {
  const el = $('toast');
  el.textContent = msg; el.hidden = false; clearTimeout(toast.t); toast.t = setTimeout(() => { el.hidden = true; }, 12000);
}
$('cNow').addEventListener('click', () => setCycleStart(new Date()));
$('cHour').addEventListener('click', () => { const d = new Date(); d.setMinutes(0, 0, 0); setCycleStart(d); });
$('cNext').addEventListener('click', () => { const d = new Date(); d.setMinutes(0, 0, 0); d.setHours(d.getHours() + 1); setCycleStart(d); });
['f-cdate', 'f-ctime', 'f-cl', 'f-clunit', 'f-co', 'f-counit'].forEach(id => $(id).addEventListener('input', cyclePreview));
setDefaultDate();
setCycleStart(new Date());

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
  if (mode === 'cycle') { if (!(n('f-cl') > 0 && n('f-co') > 0)) return fail('Enter both cycle lengths.'); L.lockMs = n('f-cl') * n('f-clunit'); L.openMs = n('f-co') * n('f-counit'); L.start = cycleStart(); if (!L.start) return fail('Pick when the cycle starts.');
    if (exProblem(exRules)) return fail(exProblem(exRules));
    if (exRules.length) L.excl = { tz: LOCAL_TZ, rules: JSON.parse(JSON.stringify(exRules)) };
    if (!nextWindowStart(L, t)) return fail('With these exclusions the number would never be visible.');
  }
  L.peekSec = $('o-peek').checked ? Math.max(1, n('o-peeksec') || 10) : 0;
  L.once = $('o-once').checked && repeating(L);
  L.pinned = $('f-pin').checked;
  setNotify(L, ntfyTopic ? $('f-notify').value : 'off');
  const first = repeating(L) ? nextWindowStart(L, t) : L.unlockAt;
  if (!first) return fail('That schedule has no upcoming window.');
  const btn = $('submit'); btn.disabled = true; btn.textContent = 'Sealing…';
  try {
    L.capsule = await seal(first, num);
    if ($('o-safe').checked) {
      const safeAt = t + (Math.max(1, n('o-safen')) || 7) * n('o-safeunit');
      if (repeating(L) || safeAt < L.unlockAt) L.safety = await seal(safeAt, num);
    }
    locks.unshift(L); save(); bookAll();
    $('f-num').value = ''; $('f-label').value = ''; $('f-pin').checked = false; setDefaultDate(); setCycleStart(new Date());
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
    if (c > 0) { Object.keys(l).forEach(k => delete l[k]); Object.assign(l, r); changed = true; if (r.deleted) { delete mem[r.id]; if (plain[r.id] != null) { delete plain[r.id]; savePlain(); } } }
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
      if (res.changed) { saveLocal(); render(); migrate(); }
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
    if (!info.private) { msg.className = 'err'; msg.textContent = 'That repository is public. Use a private one so your lock names and times stay private.'; return false; }
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
  const link = location.origin + location.pathname + '#sync=' + b64enc(JSON.stringify(Object.assign({}, sync, ntfyTopic ? { ntfy: ntfyTopic } : {})));
  const box = $('linkBox'); box.hidden = false; $('linkText').value = link;
  try { await navigator.clipboard.writeText(link); $('linkHint').textContent = 'Copied. Open it on your other device. It contains your access key, so only send it to yourself.'; }
  catch (e) { $('linkText').select(); $('linkHint').textContent = 'Copy this link and open it on your other device. It contains your access key, so only send it to yourself.'; }
});
function setupFromLink() {
  const m = location.hash.match(/^#sync=(.+)$/); if (!m) return;
  history.replaceState(null, '', location.pathname + location.search);
  try { const cfg = JSON.parse(b64dec(decodeURIComponent(m[1]))); if (cfg.ntfy) setTopic(cfg.ntfy); if (cfg.repo && cfg.token) connect(cfg.repo, cfg.token); } catch (e) {}
}
setupFromLink();
window.addEventListener('hashchange', setupFromLink);

/* ---------- unlock notifications through ntfy ---------- */
const NTFY = 'https://ntfy.sh', NTFY_KEY = 'timelock.ntfy', MAX_AHEAD = 3 * 86400000 - 10 * 60000;
let ntfyTopic = null;
try { ntfyTopic = localStorage.getItem(NTFY_KEY) || null; } catch (e) {}
const validTopic = s => /^[A-Za-z0-9_-]{1,64}$/.test(s);
const hm = ms => new Date(ms).toLocaleTimeString(undefined, { hour: 'numeric', minute: '2-digit' });
function setTopic(t) {
  ntfyTopic = t || null;
  try { if (ntfyTopic) localStorage.setItem(NTFY_KEY, ntfyTopic); else localStorage.removeItem(NTFY_KEY); } catch (e) {}
  renderNotify();
}
function renderNotify() {
  $('n-topic').value = ntfyTopic || $('n-topic').value;
  $('n-clear').hidden = !ntfyTopic; $('n-test').disabled = !ntfyTopic;
  $('f-notify').disabled = !ntfyTopic;
  if (!ntfyTopic) $('f-notify').value = 'off';
  else if (!$('f-notify').dataset.touched) $('f-notify').value = 'quiet';
  $('notifyHint').textContent = ntfyTopic ? 'Sends a push notification through ntfy at the unlock time.' : 'Set up notifications further down the page first.';
}
function nMsg(text, cls) { const m = $('n-msg'); m.hidden = false; m.className = cls || 'net'; m.textContent = text; }
/* Quiet hours: saved on this device, and copied into each lock set to "not during quiet hours"
   (with the time zone) so other devices and the GitHub job follow the same rule. */
const QUIET_KEY = 'timelock.quiet', TZ = (Intl.DateTimeFormat().resolvedOptions().timeZone) || 'UTC';
let quiet = { from: '22:00', to: '07:00', act: 'skip' };
try { quiet = Object.assign(quiet, JSON.parse(localStorage.getItem(QUIET_KEY) || '{}')); } catch (e) {}
const quietRule = () => ({ from: quiet.from, to: quiet.to, act: quiet.act, tz: TZ });
function setNotify(L, mode) {
  if (mode === 'always') { L.notify = true; delete L.quiet; }
  else if (mode === 'quiet') { L.notify = 'quiet'; L.quiet = quietRule(); }
  else { L.notify = false; delete L.quiet; }
}
const fmtCache = {};
function localMinutes(ms, tz) {
  const f = fmtCache[tz] || (fmtCache[tz] = new Intl.DateTimeFormat('en-GB', { timeZone: tz, hour: '2-digit', minute: '2-digit', hourCycle: 'h23' }));
  const [h, m] = f.format(new Date(ms)).split(':').map(Number); return h * 60 + m;
}
function inQuiet(ms, q) {
  const toM = s => { const [h, m] = s.split(':').map(Number); return h * 60 + m; };
  const f = toM(q.from), e = toM(q.to), m = localMinutes(ms, q.tz || TZ);
  return f === e ? false : f < e ? m >= f && m < e : m >= f || m < e;
}
function quietEnd(ms, q) { let t = Math.ceil(ms / 60000) * 60000; for (let i = 0; i < 1500 && inQuiet(t, q); i++) t += 60000; return t; }
// Adjust one booking for quiet hours: returns it (maybe silent or moved), or null to skip it.
function applyQuiet(L, x, isWindow) {
  x.p = 4;
  if (L.notify !== 'quiet' || !L.quiet || !inQuiet(x.at, L.quiet)) return x;
  if (L.quiet.act === 'silent') { x.p = 2; return x; }
  if (L.quiet.act === 'defer' && !isWindow) return Object.assign(x, { at: quietEnd(x.at, L.quiet), body: '"' + L.label + '" unlocked at ' + hm(x.at) + '.' });
  return null;
}
function saveQuiet() {
  quiet = { from: $('q-from').value || '22:00', to: $('q-to').value || '07:00', act: $('q-act').value };
  try { localStorage.setItem(QUIET_KEY, JSON.stringify(quiet)); } catch (e) {}
  for (const L of locks) if (L.notify === 'quiet' && !L.deleted) { L.quiet = quietRule(); touch(L); }
  save(); render(); bookAll();
}
['q-from', 'q-to', 'q-act'].forEach(id => $(id).addEventListener('change', saveQuiet));
$('q-from').value = quiet.from; $('q-to').value = quiet.to; $('q-act').value = quiet.act;

async function ntfySend(seq, at, title, body, prio) {
  const headers = { Title: title, Tags: 'unlock', Priority: String(prio || 4), Click: location.origin + location.pathname };
  if (at) headers.At = String(Math.floor(at / 1000));
  const r = await fetch(NTFY + '/' + ntfyTopic + (seq ? '/' + seq : ''), { method: 'POST', headers, body });
  if (!r.ok) throw new Error(r.status === 429 ? 'ntfy says too many messages today. Try again later.' : 'ntfy returned an error (' + r.status + ').');
}
// The times a lock should notify at, within ntfy's 3-day booking limit. Each gets a fixed ID so re-booking replaces it.
function targets(L, t) {
  if (L.deleted || L.opened || !L.notify) return [];
  const out = [], label = L.label;
  if (!repeating(L)) {
    const at = Math.min(L.capsule ? L.capsule.at : Infinity, L.safety ? L.safety.at : Infinity);
    if (at < Infinity) out.push(applyQuiet(L, { seq: 'tl' + L.id, at, body: '"' + label + '" is unlocking now.' }, false));
  } else {
    let w = nextWindowStart(L, t);
    const horizon = t + (L.mode === 'cycle' ? 26 * 3600000 : MAX_AHEAD);
    for (let i = 0; i < 40 && w && w <= horizon; i++) {
      const end = L.mode === 'cycle' ? w + L.openMs : (schedIntervals(L, w).find(x => x[0] === w) || [w, w])[1];
      out.push(applyQuiet(L, { seq: 'tl' + L.id + '-' + Math.floor(w / 1000), at: w, body: '"' + label + '" is visible now until ' + hm(end) + '.' }, true));
      w = nextWindowStart(L, w);
    }
    if (L.safety) out.push(applyQuiet(L, { seq: 'tl' + L.id + '-safe', at: L.safety.at, body: '"' + label + '" is unlocking for good (safety unlock).' }, false));
  }
  return out.filter(x => x && x.at - t > 15000 && x.at - t <= MAX_AHEAD);
}
let booking = false;
async function bookAll() {
  if (!ntfyTopic || booking) return;
  booking = true;
  try {
    const t = now();
    for (const L of locks) {
      if (L.opened && L.booked) cancelBookings(L, t); // opened early (safety): drop the rest
      L.booked = L.booked || {};
      let changed = false;
      const bk = v => typeof v === 'number' ? { at: v, p: 4 } : v; // older versions stored just the time
      for (const k of Object.keys(L.booked)) if (bk(L.booked[k]).at < t - 3600000) { delete L.booked[k]; changed = true; }
      const want = targets(L, t), seqs = new Set(want.map(x => x.seq));
      for (const k of Object.keys(L.booked)) { // booked earlier but no longer wanted (e.g. now in quiet hours): cancel
        if (!seqs.has(k) && bk(L.booked[k]).at - t > 60000) { fetch(NTFY + '/' + ntfyTopic + '/' + k, { method: 'DELETE' }).catch(() => {}); delete L.booked[k]; changed = true; }
      }
      for (const x of want) {
        const b = L.booked[x.seq] && bk(L.booked[x.seq]);
        if (b && b.at === x.at && b.p === x.p) continue;
        try { await ntfySend(x.seq, x.at, 'Time Lock', x.body, x.p); L.booked[x.seq] = { at: x.at, p: x.p }; touch(L); saveLocal(); changed = true; }
        catch (e) { nMsg(e instanceof TypeError ? "Can't reach ntfy right now. Notifications will be booked when you're back online." : e.message, 'err'); break; }
      }
      if (!Object.keys(L.booked).length) delete L.booked;
      if (changed) { touch(L); save(); }
    }
  } finally { booking = false; }
}
function cancelBookings(L, after) {
  if (!ntfyTopic || !L.booked) return;
  for (const [seq, v] of Object.entries(L.booked)) {
    const at = typeof v === 'number' ? v : v.at;
    if (after && at <= after) continue;
    fetch(NTFY + '/' + ntfyTopic + '/' + seq, { method: 'DELETE' }).catch(() => {});
  }
  L.booked = {};
}
$('n-save').addEventListener('click', () => {
  const v = $('n-topic').value.trim();
  if (!validTopic(v)) return nMsg('Use only letters, numbers, - and _, up to 64 characters.', 'err');
  if (v.length < 10) return nMsg('Use at least 10 characters so nobody can guess it.', 'err');
  setTopic(v); nMsg('Saved. Tap Send test to check your phone gets it.', 'ok'); render(); bookAll();
});
$('n-test').addEventListener('click', async () => {
  try { await ntfySend(null, 0, 'Time Lock', 'Test notification. Unlock notifications are working.'); nMsg('Sent. It should arrive on your phone within a few seconds.', 'ok'); }
  catch (e) { nMsg(e instanceof TypeError ? "Couldn't reach ntfy. Check your connection." : e.message, 'err'); }
});
$('n-clear').addEventListener('click', () => { setTopic(null); $('n-topic').value = ''; nMsg('Notifications are off on this device.', 'net'); render(); });
$('f-notify').addEventListener('change', () => { $('f-notify').dataset.touched = '1'; });
renderNotify();

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
migrate();
checkNet();
setInterval(() => { locks.forEach(L => { process(L); }); render(); }, 1000);
setInterval(checkNet, 5 * 60000);
syncNow().then(bookAll);
setInterval(() => { if (!document.hidden) syncNow().then(bookAll); }, 60000);
document.addEventListener('visibilitychange', () => { if (!document.hidden) { syncNow(); locks.forEach(L => { process(L); }); render(); } });
})();
