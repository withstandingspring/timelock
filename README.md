# Number Time Lock

Hide a number until a set time. The number is sealed with time-lock encryption using the public
[drand](https://drand.love) network (quicknet), via [tlock-js](https://github.com/drand/tlock-js).
Until the unlock time arrives, nobody can decrypt it, including you. Changing the device clock
doesn't help, because the key for that moment hasn't been published yet.

## Modes

- **Until a date**: unlocks at a set date and time.
- **For a duration**: locked for a set time from now.
- **On a schedule**: visible only on chosen weekdays between two times.
- **Repeating cycle**: locked for X, visible for Y, repeating.

Options: safety unlock (on by default, 7 days), adding time to a sealed lock, a brief reveal, and
one reveal per window (repeating modes).

## How it works

- Sealing happens in the browser and works offline. The drand chain info is built in.
- Only the sealed text is stored (in `localStorage`). The plain number is stored only once a one-time
  lock has unlocked.
- Adding time wraps the existing seal in another seal for the later time.
- Repeating locks: when a window opens, the page unseals the number, re-seals it for the next window,
  then shows it. The plain number stays in memory only.
- The safety unlock is a second sealed copy for an earlier time.

## Sync between devices

Optional. Locks are saved to `timelock-locks.json` in a **private** GitHub repository you choose, using a
fine-grained access token limited to that repository (Contents: read and write). Each device keeps a
local copy and merges changes by revision, so deletions and added time carry over. Other devices can
be set up with a one-time setup link, which contains the access token.

## Unlock notifications

Optional, through [ntfy](https://ntfy.sh). Enter a private ntfy channel name in the app and subscribe to it in the
ntfy phone app. Locks book a notification for their unlock time (repeating locks book about a day of
windows ahead) whenever the app is open. Each booking uses a fixed sequence ID, so adding time replaces it,
deleting a lock cancels it, and two devices can't double-book. Messages contain the lock name, never the number.

ntfy only accepts bookings up to 3 days ahead. A scheduled GitHub Actions job in the private data
repository books upcoming notifications every 12 hours, so long locks are covered even if the app isn't opened.

## Limits

- Once you've seen a number, you know it.
- Repeating locks re-seal only while the page is open during a window. If a window passes without the
  page open, the old seal stays decryptable by technical means until the page is opened again.
- Unlocking needs an internet connection to fetch the published drand key.
- If drand stopped operating before the unlock time, the number couldn't be recovered.
- Without sync, locks live in one browser. Use sync or the Backup section to move them. Sealed locks stay sealed in
  a backup, but a backup of a repeating lock becomes decryptable once the window it was sealed for
  has passed.

## Development

`vendor/tlock.js` is a browser bundle of tlock-js. To rebuild it:

```bash
npm install
```

```bash
npm run build:vendor
```
