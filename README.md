# Number Time Lock

Hide a number until a set time. The number is sealed with time-lock encryption using the public
[drand](https://drand.love) network (quicknet), via [tlock-js](https://github.com/drand/tlock-js).
Until the unlock time arrives, nobody can decrypt it, including you. Changing the device clock
doesn't help, because the key for that moment hasn't been published yet.

## Modes

- **Until a date**: unlocks at a set date and time.
- **For a duration**: locked for a set time from now.
- **On a schedule**: visible only on chosen weekdays between two times.
- **Repeating cycle**: locked for X, visible for Y, repeating, set by when the first visible window starts. Exclusions (days plus all day
  or a time range, which can run past midnight) skip any window that overlaps them.

Any lock can be edited later. Changes that make it open the same or later apply at once (the seal is wrapped
to the new time); changes that would open it sooner are saved and applied at the next unlock. While a lock is
open, any change applies immediately.

Options: safety unlock (on by default, 7 days), adding time to a sealed lock, a brief reveal, and
one reveal per window (repeating modes).

## How it works

- Sealing happens in the browser and works offline. The drand chain info is built in.
- Only sealed text is stored and synced. Once a lock unlocks, its number is kept on that device only
  (in `localStorage`); the synced copy stays sealed to a round that has already been published, so other
  devices open it from drand themselves. The sync repository and backups never hold a readable number.
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

Each lock can notify always, not during quiet hours, or not at all. Quiet hours (default 22:00 to 07:00,
in the phone's time zone) can skip the notification, send it silently, or hold a one-time unlock's
notification until they end. The rule is saved with each lock so other devices and the GitHub job follow it.

ntfy only accepts bookings up to 3 days ahead. A scheduled GitHub Actions job in the private data
repository books upcoming notifications every 12 hours, so long locks are covered even if the app isn't opened.

## Limits

- Once you've seen a number, you know it.
- Repeating locks re-seal only while the page is open during a window. If a window passes without the
  page open, the old seal stays decryptable by technical means until the page is opened again.
- Unlocking needs an internet connection to fetch the published drand key.
- If drand stopped operating before the unlock time, the number couldn't be recovered.
- Without sync, locks live in one browser. Use sync or the Backup section to move them. Every lock stays sealed in
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
