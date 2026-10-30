# Yank's interactive commands, and heist-edit's

This report lists every interactive command Yank defines, with its key
bindings, and says whether heist-edit (`editor/`) has it. It is a
snapshot, so it will go stale as either editor changes.

- **Yank:** `~/Dev/Emacs/yank`, branch `main` at `98132c0`, read from
  that commit (`git archive`). heist-edit was ported from Yank's
  `cahoots` branch, so `main` may have commands `cahoots` never had.
- **heist-edit:** Heist at `ec3505bf` (first written against `7e703634`; see "Since the first survey").

## How the lists were made

Both editors' sources were read as s-expressions:

- **Yank's commands** are its `define-command` forms (192), plus the
  command each `define-major-mode` defines (5): 197 in all.
- **Yank's keys** are its `define-key` forms, including those applied
  over a quoted list of `(key command)` pairs. `M-0`..`M-9` come from
  the loop that binds `digit-argument`.
- **heist-edit's commands** come from:
  - its built-in table (`commands` in `frame.fx`);
  - every `define-command!`.
- **heist-edit's keys** come from:
  - its global `keymap`;
  - `paredit-keys`, active while `paredit-mode` is on;
  - every `define-key!`;
  - every `define-buffer-key!`, which binds keys in one buffer, or in
    one kind of buffer: a listing, a Scheme buffer.

Matching commands across the two editors, and judging whether one is
less complete, was done by reading both sides' code and docs.

Each Yank command gets one of four statuses:

| Status | Meaning |
| --- | --- |
| **same** | heist-edit has a command of the same name that does the same thing. |
| **renamed** | heist-edit does the same under another name. |
| **partial** | heist-edit has the command, or its counterpart, but with less. The note says what is lacking. |
| **missing** | heist-edit has nothing that does it. |

"(keys differ)" after a status means the keys bound in the two editors
are not the same set; the note says how.

## Summary

Of Yank's 197 commands:

| Status | Count |
| --- | --- |
| same | 76 |
| renamed | 30 |
| partial | 13 |
| missing | 78 |

The keys differ for 21 of the 119 that heist-edit has in some form.

### Since the first survey

The first survey (at `7e703634`) found 51 the same, 11 renamed, 24 partial
and 111 missing. Since then heist-edit has gained:

- **isearch as Yank's:** `DEL` takes back the last key, `C-g` takes back
  only the failing part, a failed search wraps around, `C-s C-s` repeats
  the last search, and case is ignored unless the text has an upper-case
  letter. Also `C-w`, and regexps (`C-M-s`, `C-M-r`, `M-r`), from a port
  of Yank's regexp engine (`editor/regexp.fx`).
- **The kill ring:** kills in a row make one entry, and `M-y` cycles
  through the ring.
- **Indentation:** a line that starts with `(` is indented, and
  distinguished arguments by four. The first survey said Scheme buffers
  were not indented; they were, and that was wrong.
- **The buffer menu**, Yank's whole: flags, `x`, `o`, `g`, `q`.
- **dired**, Yank's whole: modes, sizes and times; marks and flags;
  delete, rename, copy, make a directory. This needed Fixpt's new file
  primitives (`FIXPT-CHANGES.md` F5).
- **Lists:** `n`, `p`, `q` in *xref* and listings, and `quit-window`.
  The first survey said `RET` in *xref* left the list open; it replaces
  it in its window, so that was wrong too.
- **`M-?`** lists a name's uses in *xref*, in another window.
- **`C-c C-c`** in a Scheme buffer runs it in a fresh s7st.

### Missing: whole areas

- **Prefix arguments.** There is no `C-u`, `M-0`..`M-9` or `M--`. Every
  Yank command that takes a count (`forward-char`, `kill-word`,
  `call-last-kbd-macro`, …) does one step in heist-edit.
- **Editor variables:** `set-variable` and `describe-variable`.
- **Mode commands.** There is no `M-x scheme-mode` or `M-x
  fundamental-mode`; a buffer's behaviour comes from its file or buffer
  name.
- **Keyboard macros:** `C-x (`, `C-x )`, `C-x e`.
- **Replacing:** `query-replace`, `query-replace-regexp`,
  `replace-string`, `replace-regexp`. heist-edit now has a regexp
  engine for them.
- **`occur`.**
- **Version control:** `vc-*`, `git-status` and its keys, `log-edit-*`,
  and diff mode.
- **Recent files:** `recentf-open-files`.
- **Evaluation in the editor itself.** Yank evaluates Scheme in its own
  running image (`eval-expression`, `M-:`, `editor-repl`). heist-edit
  is compiled FX-26 and has no evaluator of its own; Scheme runs in s7st,
  a separate process.
- **Debugging and profiling an inferior:** breakpoints, watches,
  instrumentation, profiling, coverage, `yank-attach`.
- **Yank's flow-analysis commands:** `next-flow-warning`,
  `flow-why-unknown`, `flow-analysis-status`, the R5RS `load` worlds.
  heist-edit's CFA commands are a different set; see "Only in
  heist-edit" below.
- **Smaller single commands:** `recenter` (`C-l`), `split-window-right`
  (`C-x 3`), `mark-sexp`, `indent-region`, `async-shell-command`,
  `comint-bol`, `comint-send-eof`, and *shell*'s input history.

### Present, but less

- **No counts**, as above.
- **Scheme evaluation** (`C-x C-e`, `C-M-x`, `C-c C-r`, `C-c C-l`) runs
  in s7st rather than in a Larceny inferior; `C-c C-l` runs the buffer's
  forms, not the file, and imports no library.
- **Completion** of names is s7st's, in Scheme buffers only; none in
  FX-26 buffers.
- ***shell*** has only `RET` and `C-c C-c`.
- **`C-j`** finishes nothing in the minibuffer, and inserts nothing in a
  buffer.

### Keys that differ

- **`C-<right>` and `C-<left>`** move by words in Yank. In heist-edit
  they are paredit's slurp and barf.
- **`C-c C-b` in a Scheme buffer** sets a breakpoint in Yank. In
  heist-edit it runs the buffer in s7st.
- **Unbound in heist-edit:**
  - `C-j` (newline);
  - `M-<right>`, `M-<left>` (word motion);
  - `C-M-h` (`backward-kill-word`);
  - `C-c C-e` (send definition);
  - `C-M-i` (complete).
- **Keys heist-edit adds where Yank has none:**
  - `C-c c` for `compile`;
  - `q` in *Help* and *Apropos*;
  - s7st's evaluation keys in Scheme buffers.
- **Global in heist-edit, Scheme mode only in Yank:**
  - `M-.`, `M-,` and `M-?` work in FX-26 and Scheme buffers alike. A
    Scheme buffer's names are resolved by s7st's analysis.
  - `TAB` and `RET` are bound everywhere, and indent in FX-26 and
    Scheme buffers.

## Command by command

The tables below go by area, in each Yank file's order.

### Editing and moving

| Yank command | Yank keys | In heist-edit | heist-edit command | heist-edit keys | Notes |
| --- | --- | --- | --- | --- | --- |
| `self-insert-command` | — | partial | `self-insert-command` | — | Typing a character inserts it, but it is not an M-x command, and takes no count. |
| `insert-newline` | `RET`, `C-j` | renamed (keys differ) | `newline` | `RET` | `newline` also indents the new line in FX-26 and Scheme buffers. `C-j` is unbound. |
| `open-line` | `C-o` | same | `open-line` | `C-o` |  |
| `forward-char` | `C-f`, `<right>` | same | `forward-char` | `C-f`, `<right>` |  |
| `backward-char` | `C-b`, `<left>` | same | `backward-char` | `C-b`, `<left>` |  |
| `forward-word` | `M-f`, `C-right`, `M-right` | same (keys differ) | `forward-word` | `M-f` | `C-<right>` is `paredit-forward-slurp-sexp` in heist-edit; `M-<right>` is unbound. |
| `backward-word` | `M-b`, `C-left`, `M-left` | same (keys differ) | `backward-word` | `M-b` | `C-<left>` is `paredit-forward-barf-sexp` in heist-edit; `M-<left>` is unbound. |
| `next-line` | `C-n`, `<down>`, `n` (recent files), `n` (vc log), `n` (vc annotate) | same (keys differ) | `next-line` | `n` (*xref*), `n` (<listing>), `SPC` (<listing>), `n` (*Buffer List*), `SPC` (*Buffer List*), `C-n`, `<down>` | Also `n` in *Buffer List*, listings and *xref*. |
| `previous-line` | `C-p`, `<up>`, `p` (recent files), `p` (vc log), `p` (vc annotate) | same | `previous-line` | `p` (*xref*), `p` (<listing>), `p` (*Buffer List*), `C-p`, `<up>` | Also `p` in *Buffer List*, listings and *xref*. |
| `move-beginning-of-line` | `C-a`, `<home>` | same | `move-beginning-of-line` | `C-a`, `<home>` |  |
| `move-end-of-line` | `C-e`, `<end>` | same | `move-end-of-line` | `C-e`, `<end>` |  |
| `beginning-of-buffer` | `M-<` | same | `beginning-of-buffer` | `M-<` |  |
| `end-of-buffer` | `M->` | same | `end-of-buffer` | `M->` |  |
| `scroll-up-command` | `C-v`, `<next>` | same | `scroll-up-command` | `C-v`, `<next>` |  |
| `scroll-down-command` | `M-v`, `<prior>` | same | `scroll-down-command` | `M-v`, `<prior>` |  |
| `recenter` | `C-l` | missing | — | — | `C-l` is unbound. |
| `goto-line` | `M-g g`, `M-g M-g` | partial | `goto-line` | `M-g g`, `M-g M-g` | Reads the line number; Yank also takes it as a prefix argument. |
| `delete-forward-char` | `C-d`, `<delete>` | renamed | `delete-char` | `C-d`, `<delete>` |  |
| `delete-backward-char` | `DEL` | same | `delete-backward-char` | `DEL` |  |
| `set-mark-command` | `C-SPC` | same | `set-mark-command` | `C-SPC` |  |
| `exchange-point-and-mark` | `C-x C-x` | same | `exchange-point-and-mark` | `C-x C-x` |  |
| `undo` | `C-_`, `C-/`, `C-x u` | same | `undo` | `C-_`, `C-/`, `C-x u` |  |
| `universal-argument` | `C-u` | missing | — | — | heist-edit has no prefix arguments at all. |
| `digit-argument` | `M-0`..`M-9` | missing | — | — |  |
| `negative-argument` | `M--` | missing | — | — |  |
| `set-variable` | — | missing | — | — | heist-edit has no editor variables. |
| `keyboard-quit` | `C-g` | same | `keyboard-quit` | `C-g` |  |
| `indent-for-tab-command` | `TAB` (Scheme mode) | same | `indent-for-tab-command` | `TAB` | Global in heist-edit: FX-26 and Scheme buffers, and *s7st*. |
| `newline-and-indent` | `RET` (Scheme mode) | renamed | `newline` | `RET` | `RET` in every buffer; it indents in FX-26 and Scheme ones. |
| `indent-region` | `C-M-\` (Scheme mode) | missing | — | — | `C-M-\` is unbound. |
| `kill-region` | `C-w` | same | `kill-region` | `C-w` |  |
| `kill-ring-save` | `M-w` | same | `kill-ring-save` | `M-w` |  |
| `kill-line` | `C-k` | same | `kill-line` | `C-k` |  |
| `kill-word` | `M-d` | same | `kill-word` | `M-d` |  |
| `backward-kill-word` | `M-DEL`, `C-M-h` | same (keys differ) | `backward-kill-word` | `M-DEL` | `C-M-h` is unbound. |
| `yank` | `C-y` | same | `yank` | `C-y` |  |
| `yank-pop` | `M-y` | same | `yank-pop` | `M-y` |  |
| `forward-sexp` | `C-M-f` | same | `forward-sexp` | `C-M-f` |  |
| `backward-sexp` | `C-M-b` | same | `backward-sexp` | `C-M-b` |  |
| `backward-up-list` | `C-M-u` | same | `backward-up-list` | `C-M-u` |  |
| `down-list` | `C-M-d` | same | `down-list` | `C-M-d` |  |
| `kill-sexp` | `C-M-k` | same | `kill-sexp` | `C-M-k` |  |
| `mark-sexp` | `C-M-SPC`, `C-M-@` | missing | — | — |  |
| `start-kbd-macro` | `C-x (` | missing | — | — |  |
| `end-kbd-macro` | `C-x )` | missing | — | — |  |
| `call-last-kbd-macro` | `C-x e` | missing | — | — |  |

### Search and replace

| Yank command | Yank keys | In heist-edit | heist-edit command | heist-edit keys | Notes |
| --- | --- | --- | --- | --- | --- |
| `isearch-forward` | `C-s` | same | `isearch-forward` | `C-s` |  |
| `isearch-backward` | `C-r` | same | `isearch-backward` | `C-r` |  |
| `isearch-forward-regexp` | `C-M-s` | same | `isearch-forward-regexp` | `C-M-s` |  |
| `isearch-backward-regexp` | `C-M-r` | same | `isearch-backward-regexp` | `C-M-r` |  |
| `query-replace` | `M-%` | missing | — | — |  |
| `replace-string` | — | missing | — | — |  |
| `query-replace-regexp` | `C-M-%` | missing | — | — |  |
| `replace-regexp` | — | missing | — | — |  |

### Files, buffers and windows

| Yank command | Yank keys | In heist-edit | heist-edit command | heist-edit keys | Notes |
| --- | --- | --- | --- | --- | --- |
| `find-file` | `C-x C-f` | same | `find-file` | `C-x C-f` |  |
| `save-buffer` | `C-x C-s` | same | `save-buffer` | `C-x C-s` |  |
| `write-file` | `C-x C-w` | same | `write-file` | `C-x C-w` |  |
| `switch-to-buffer` | `C-x b` | same | `switch-to-buffer` | `C-x b` |  |
| `kill-buffer` | `C-x k` | same | `kill-buffer` | `C-x k` |  |
| `save-buffers-kill-editor` | `C-x C-c` | renamed | `save-buffers-kill-terminal` | `C-x C-c` |  |
| `list-buffers` | `C-x C-b` | same | `list-buffers` | `C-x C-b` |  |
| `buffer-menu-visit` | `RET` (buffer menu), `f` (buffer menu) | renamed | `Buffer-menu-this-window` | `RET` (*Buffer List*), `f` (*Buffer List*) |  |
| `buffer-menu-visit-other-window` | `o` (buffer menu) | renamed | `Buffer-menu-other-window` | `o` (*Buffer List*) |  |
| `buffer-menu-delete` | `d` (buffer menu), `k` (buffer menu) | renamed | `Buffer-menu-delete` | `d` (*Buffer List*), `k` (*Buffer List*) |  |
| `buffer-menu-delete-backward` | `C-d` (buffer menu) | renamed | `Buffer-menu-delete-backwards` | `C-d` (*Buffer List*) |  |
| `buffer-menu-save` | `s` (buffer menu) | renamed | `Buffer-menu-save` | `s` (*Buffer List*) |  |
| `buffer-menu-unmark` | `u` (buffer menu) | renamed | `Buffer-menu-unmark` | `u` (*Buffer List*) |  |
| `buffer-menu-unmark-backward` | `DEL` (buffer menu) | renamed | `Buffer-menu-backup-unmark` | `DEL` (*Buffer List*) |  |
| `buffer-menu-execute` | `x` (buffer menu) | renamed | `Buffer-menu-execute` | `x` (*Buffer List*) |  |
| `buffer-menu-next` | `n` (buffer menu), `SPC` (buffer menu), `<down>` (buffer menu) | renamed (keys differ) | `next-line` | `n` (*xref*), `n` (<listing>), `SPC` (<listing>), `n` (*Buffer List*), `SPC` (*Buffer List*), `C-n`, `<down>` | `<down>` is `next-line` everywhere. |
| `buffer-menu-previous` | `p` (buffer menu), `<up>` (buffer menu) | renamed (keys differ) | `previous-line` | `p` (*xref*), `p` (<listing>), `p` (*Buffer List*), `C-p`, `<up>` | `<up>` is `previous-line` everywhere. |
| `buffer-menu-refresh` | `g` (buffer menu) | renamed | `Buffer-menu-refresh` | `g` (*Buffer List*) |  |
| `buffer-menu-quit` | `q` (buffer menu) | renamed | `quit-window` | `q` (*xref*), `q` (<listing>), `q` (*Buffer List*) |  |
| `split-window-below` | `C-x 2` | same | `split-window-below` | `C-x 2` |  |
| `split-window-right` | `C-x 3` | missing | — | — |  |
| `other-window` | `C-x o` | same | `other-window` | `C-x o` |  |
| `quit-window` | `q` (listings), `q` (dired), `q` (git status), `q` (recent files), `q` (vc log), `q` (vc annotate), `q` (diff view) | same | `quit-window` | `q` (*xref*), `q` (<listing>), `q` (*Buffer List*) | Bound in *Buffer List*, listings and *xref*; *Help* and *Apropos* bind `q` to `delete-window`. |
| `delete-window` | `C-x 0` | same (keys differ) | `delete-window` | `C-x 0`, `q` (*Help*), `q` (*Apropos*) | heist-edit also binds `q` in *Help* and *Apropos* to it. |
| `delete-other-windows` | `C-x 1` | same | `delete-other-windows` | `C-x 1` |  |
| `recentf-open-files` | `C-x C-r` | missing | — | — |  |
| `recent-files-visit` | `RET` (recent files), `f` (recent files) | missing | — | — |  |
| `recent-files-visit-other-window` | `o` (recent files) | missing | — | — |  |
| `dired` | `C-x d` | same | `dired` | `C-x d` | Its listing shows times in UTC: FX-26 has no time zone. |
| `dired-find-file` | `RET` (dired), `f` (dired), `e` (dired) | same | `dired-find-file` | `RET` (<listing>), `f` (<listing>), `e` (<listing>) |  |
| `dired-find-file-other-window` | `o` (dired) | same | `dired-find-file-other-window` | `o` (<listing>) |  |
| `dired-up-directory` | `^` (dired) | same | `dired-up-directory` | `^` (<listing>) |  |
| `dired-mark` | `m` (dired) | same | `dired-mark` | `m` (<listing>) |  |
| `dired-unmark` | `u` (dired) | same | `dired-unmark` | `u` (<listing>) |  |
| `dired-unmark-backward` | `DEL` (dired) | same | `dired-unmark-backward` | `DEL` (<listing>) |  |
| `dired-flag-file-deletion` | `d` (dired) | same | `dired-flag-file-deletion` | `d` (<listing>) |  |
| `dired-unmark-all-marks` | `U` (dired) | same | `dired-unmark-all-marks` | `U` (<listing>) |  |
| `dired-do-delete` | `D` (dired) | same | `dired-do-delete` | `D` (<listing>) |  |
| `dired-do-flagged-delete` | `x` (dired) | same | `dired-do-flagged-delete` | `x` (<listing>) |  |
| `dired-do-rename` | `R` (dired) | same | `dired-do-rename` | `R` (<listing>) |  |
| `dired-do-copy` | `C` (dired) | same | `dired-do-copy` | `C` (<listing>) |  |
| `dired-create-directory` | `+` (dired) | same | `dired-create-directory` | `+` (<listing>) |  |
| `dired-next-line` | `n` (dired), `SPC` (dired), `<down>` (dired) | renamed (keys differ) | `next-line` | `n` (*xref*), `n` (<listing>), `SPC` (<listing>), `n` (*Buffer List*), `SPC` (*Buffer List*), `C-n`, `<down>` | `<down>` is `next-line` everywhere. |
| `dired-previous-line` | `p` (dired), `<up>` (dired) | renamed (keys differ) | `previous-line` | `p` (*xref*), `p` (<listing>), `p` (*Buffer List*), `C-p`, `<up>` | `<up>` is `previous-line` everywhere. |
| `dired-revert` | `g` (dired) | same | `dired-revert` | `g` (<listing>) |  |

### Minibuffer and help

| Yank command | Yank keys | In heist-edit | heist-edit command | heist-edit keys | Notes |
| --- | --- | --- | --- | --- | --- |
| `exit-minibuffer` | `RET` (minibuffer), `C-j` (minibuffer) | partial | (built in) | see note | Built into the minibuffer, not a command: `RET` works, `C-j` does not. |
| `abort-minibuffer` | `C-g` (minibuffer) | same | (built in) | see note | Built into the minibuffer (`C-g`), not a command. |
| `minibuffer-complete` | `TAB` (minibuffer) | same | (built in) | see note | Built into the minibuffer (`TAB`), not a command. |
| `execute-extended-command` | `M-x` | same | `execute-extended-command` | `M-x` |  |
| `describe-key` | `C-h k` | same | `describe-key` | `C-h k` |  |
| `describe-command` | `C-h f` | same (keys differ) | `describe-command` | — | `C-h f` runs heist-edit's `describe-function`, which does the same thing; `describe-command` itself has no key. |
| `describe-variable` | `C-h v` | missing | — | — | heist-edit has no editor variables. |
| `describe-bindings` | `C-h b` | same | `describe-bindings` | `C-h b` |  |

### Processes and lists of places

| Yank command | Yank keys | In heist-edit | heist-edit command | heist-edit keys | Notes |
| --- | --- | --- | --- | --- | --- |
| `shell-command` | `M-!` | same | `shell-command` | `M-!` |  |
| `async-shell-command` | `M-&` | missing | — | — |  |
| `comint-mode` | — | missing | — | — | heist-edit has no mode commands; a buffer's behaviour comes from its name. |
| `comint-send-input` | `RET` (comint) | same | `comint-send-input` | `RET` (*shell*) | Bound in *shell* only. |
| `comint-previous-input` | `M-p` (comint) | missing | — | — | Missing in *shell*. *s7st* has its own (`s7st-previous-input`, `M-p`). |
| `comint-next-input` | `M-n` (comint) | missing | — | — | Missing in *shell*. *s7st* has its own (`s7st-next-input`, `M-n`). |
| `comint-bol` | `C-a` (comint) | missing | — | — |  |
| `comint-interrupt-subjob` | `C-c C-c` (comint) | same | `comint-interrupt-subjob` | `C-c C-c` (*shell*) | Bound in *shell* only. |
| `comint-send-eof` | `C-c C-d` (comint) | missing | — | — |  |
| `shell` | — | partial | `shell` | — | Has `RET` and `C-c C-c` only: no history, `comint-bol` or `C-c C-d`. |
| `compile` | — | same (keys differ) | `compile` | `C-c c` | heist-edit adds `C-c c`; Yank has no key. |
| `grep` | — | same | `grep` | — |  |
| `recompile` | — | same (keys differ) | `recompile` | `g` (*compilation*), `g` (*grep*) | `g` in *compilation* and *grep*; Yank's `g` there is `listing-again`. |
| `kill-compilation` | `C-c C-k` (listings) | same | `kill-compilation` | `C-c C-k` (*compilation*), `C-c C-k` (*grep*) |  |
| `next-error` | `M-g n`, `M-g M-n`, `C-x `` | partial | `next-error` | `C-x ``, `M-g n`, `M-g M-n` | Only *compilation* and *grep*; Yank also steps through *Occur*. |
| `previous-error` | `M-g p`, `M-g M-p` | same | `previous-error` | `M-g p`, `M-g M-p` |  |
| `compile-goto-error` | `RET` (listings) | same | `compile-goto-error` | `RET` (*compilation*), `RET` (*grep*) |  |
| `compilation-next-error` | `n` (listings) | missing | — | — |  |
| `compilation-previous-error` | `p` (listings) | missing | — | — |  |
| `occur` | — | missing | — | — |  |
| `listing-again` | `g` (listings) | partial | `recompile` | `g` (*compilation*), `g` (*grep*) | `g` reruns the command in *compilation* and *grep*. There is no *Occur* to search again. |
| `places-visit` | `RET` (places) | renamed | `xref-visit` | `RET` (*xref*) | heist-edit's *Definitions* and *Uses* are one list, *xref*. |
| `places-next` | `n` (places), `<down>` (places) | renamed (keys differ) | `next-line` | `n` (*xref*), `n` (<listing>), `SPC` (<listing>), `n` (*Buffer List*), `SPC` (*Buffer List*), `C-n`, `<down>` | `n` in *xref*. |
| `places-previous` | `p` (places), `<up>` (places) | renamed (keys differ) | `previous-line` | `p` (*xref*), `p` (<listing>), `p` (*Buffer List*), `C-p`, `<up>` | `p` in *xref*. |
| `places-quit` | `q` (places) | renamed | `quit-window` | `q` (*xref*), `q` (<listing>), `q` (*Buffer List*) | `q` in *xref*. |

### Version control

| Yank command | Yank keys | In heist-edit | heist-edit command | heist-edit keys | Notes |
| --- | --- | --- | --- | --- | --- |
| `vc-diff` | `C-x v =` | missing | — | — |  |
| `vc-print-log` | `C-x v l` | missing | — | — |  |
| `vc-log-show-commit` | `RET` (vc log), `d` (vc log) | missing | — | — |  |
| `vc-annotate` | `C-x v g` | missing | — | — |  |
| `vc-next-action` | `C-x v v` | missing | — | — |  |
| `log-edit-done` | `C-c C-c` (log edit) | missing | — | — |  |
| `log-edit-cancel` | `C-c C-k` (log edit) | missing | — | — |  |
| `git-status` | `C-x g`, `C-x v d` | missing | — | — |  |
| `git-status-stage` | `s` (git status) | missing | — | — |  |
| `git-status-unstage` | `u` (git status) | missing | — | — |  |
| `git-status-toggle-diff` | `TAB` (git status) | missing | — | — |  |
| `git-status-visit` | `RET` (git status) | missing | — | — |  |
| `git-status-commit` | `c` (git status) | missing | — | — |  |
| `git-status-log` | `l` (git status) | missing | — | — |  |
| `git-status-next` | `n` (git status) | missing | — | — |  |
| `git-status-previous` | `p` (git status) | missing | — | — |  |
| `git-status-refresh` | `g` (git status) | missing | — | — |  |
| `diff-mode` | — | missing | — | — | heist-edit has no mode commands; a buffer's mode comes from its file or buffer name. |
| `diff-hunk-next` | `M-n` (diff), `n` (diff view) | missing | — | — |  |
| `diff-hunk-prev` | `M-p` (diff), `p` (diff view) | missing | — | — |  |
| `diff-goto-source` | `C-c C-c` (diff), `RET` (diff view), `o` (diff view) | missing | — | — |  |
| `diff-revert` | `g` (vc log), `g` (vc annotate), `g` (diff view) | missing | — | — |  |

### Scheme: modes, navigation, evaluation

| Yank command | Yank keys | In heist-edit | heist-edit command | heist-edit keys | Notes |
| --- | --- | --- | --- | --- | --- |
| `fundamental-mode` | — | missing | — | — | heist-edit has no mode commands; a buffer's mode comes from its file or buffer name. |
| `scheme-mode` | — | missing | — | — | heist-edit has no mode commands; a buffer's mode comes from its file or buffer name. |
| `scheme-interaction-mode` | — | missing | — | — | heist-edit has no mode commands; a buffer's mode comes from its file or buffer name. |
| `eval-print-last-sexp` | `C-j` (Scheme Interaction) | missing | — | — |  |
| `find-definition` | `M-.` (Scheme mode) | renamed | `xref-find-definitions` | `M-.` | Global in heist-edit, in FX-26 and Scheme buffers. A name with several definitions is not listed: heist-edit goes to one. |
| `find-uses` | `M-?` (Scheme mode) | renamed | `xref-find-references` | `M-?` | Lists a name's uses in *xref*, and marks them for `M-n`/`M-p`. Yank lists where a procedure may be called, by its flow analysis; heist-edit's `C-c r` (`cfa-callers`) does that. |
| `pop-definition-stack` | `M-,` (Scheme mode) | renamed | `xref-go-back` | `M-,` |  |
| `complete-symbol` | `C-M-i` (Scheme mode), `M-TAB` (Scheme mode) | partial (keys differ) | `s7st-complete` | `TAB` (*s7st*), `M-TAB` (*s7st*), `M-TAB` (<scheme>) | In Scheme buffers on `M-TAB`, from s7st's top level. No completion in FX-26 buffers, and `C-M-i` is unbound. |
| `eval-input-mode` | — | missing | — | — | heist-edit has no mode commands; a buffer's mode comes from its file or buffer name. |
| `eval-input-end` | `C-c C-d` (eval input) | missing | — | — |  |
| `eval-expression` | `M-:` | missing | — | — |  |
| `eval-last-sexp` | `C-x C-e` | partial | `s7st-eval-last-sexp` | `C-x C-e` (*s7st*), `C-x C-e` (<scheme>) | Yank's evaluates in the editor, anywhere. heist-edit's runs the sexp in s7st, in Scheme buffers and *s7st* only. |
| `eval-defun` | `C-M-x` (Scheme Interaction) | partial | `s7st-eval-defun` | `C-M-x` (<scheme>) | Runs in s7st, not in the editor. |
| `eval-region` | — | partial (keys differ) | `s7st-eval-region` | `C-c C-r` (<scheme>) | Runs in s7st, not in the editor. On `C-c C-r` in Scheme buffers; Yank has no key. |
| `eval-buffer` | — | partial (keys differ) | `s7st-eval-buffer` | `C-c C-b` (<scheme>), `C-c C-l` (<scheme>) | Runs in s7st, not in the editor. On `C-c C-b` and `C-c C-l` in Scheme buffers; Yank has no key. |
| `eval-cancel` | — | missing | — | — |  |
| `load-file` | — | missing | — | — |  |
| `editor-repl` | — | missing | — | — | heist-edit cannot evaluate code in itself. |

### Scheme: the inferior REPL and debugging

| Yank command | Yank keys | In heist-edit | heist-edit command | heist-edit keys | Notes |
| --- | --- | --- | --- | --- | --- |
| `run-scheme` | — | partial | `run-scheme` | — | Shows *s7st*, heist-edit's s7st REPL, rather than starting a Larceny. |
| `scheme-run` | `C-c C-c` (Scheme mode) | renamed | `s7st-run` | `C-c C-c` (<scheme>) | In s7st, started afresh. |
| `scheme-send-definition` | `C-M-x` (Scheme mode), `C-c C-e` (Scheme mode) | renamed (keys differ) | `s7st-eval-defun` | `C-M-x` (<scheme>) | Only `C-M-x`, not `C-c C-e`. Shows the value in the echo area. |
| `scheme-send-region` | `C-c C-r` (Scheme mode) | renamed | `s7st-eval-region` | `C-c C-r` (<scheme>) |  |
| `scheme-load-file` | `C-c C-l` (Scheme mode) | partial (keys differ) | `s7st-eval-buffer` | `C-c C-b` (<scheme>), `C-c C-l` (<scheme>) | Runs the buffer's forms, not the file, and imports no library. Also on `C-c C-b`, which is Yank's `scheme-toggle-breakpoint`. |
| `scheme-profile` | — | missing | — | — |  |
| `scheme-coverage` | — | missing | — | — |  |
| `yank-profile` | — | missing | — | — |  |
| `scheme-toggle-breakpoint` | `C-c C-b` (Scheme mode) | missing | — | — | heist-edit binds `C-c C-b` to `s7st-eval-buffer` in Scheme buffers. |
| `switch-to-scheme` | `C-c C-z` (Scheme mode) | renamed | `run-s7st` | `C-c C-z` (<scheme>) |  |
| `scheme-watch` | — | missing | — | — |  |
| `scheme-watch-variable` | — | missing | — | — |  |
| `scheme-unwatch` | — | missing | — | — |  |
| `scheme-apropos` | — | missing | — | — |  |
| `scheme-repl-complete` | `TAB` (inferior Scheme), `C-M-i` (inferior Scheme), `M-TAB` (inferior Scheme) | renamed (keys differ) | `s7st-complete` | `TAB` (*s7st*), `M-TAB` (*s7st*), `M-TAB` (<scheme>) | In *s7st*. `C-M-i` is unbound. |
| `toggle-scheme-instrument` | — | missing | — | — |  |
| `toggle-scheme-instrument-variables` | — | missing | — | — |  |
| `yank-attach` | — | missing | — | — |  |

### Flow analysis

| Yank command | Yank keys | In heist-edit | heist-edit command | heist-edit keys | Notes |
| --- | --- | --- | --- | --- | --- |
| `flow-include-via` | — | missing | — | — |  |
| `next-flow-warning` | `C-c C-n` | missing | — | — |  |
| `flow-why-unknown` | — | missing | — | — |  |
| `flow-analysis-status` | — | missing | — | — |  |
| `flow-memory` | — | missing | — | — |  |
| `flow-loads` | — | missing | — | — |  |
| `flow-run-loads` | — | missing | — | — |  |

## Only in heist-edit

These commands have no Yank counterpart:

- **Paredit:**
  - `paredit-mode`, which turns the rest on;
  - `paredit-open-round` `(`, `paredit-close-round` `)`,
    `paredit-doublequote` `"`;
  - `paredit-backward-delete`, `paredit-forward-delete`,
    `paredit-kill`;
  - `paredit-forward-slurp-sexp` `C-<right>`,
    `paredit-forward-barf-sexp` `C-<left>`;
  - `paredit-splice-sexp` `M-s`, `paredit-raise-sexp` `M-r`,
    `paredit-wrap-round` `M-(`.
- **The CFA:** `cfa-at-point` `C-c f`, `cfa-callees` `C-c e`,
  `cfa-callers` `C-c r`, `cfa-contexts` `C-c d`.
- **FX-26's checker:** `type-at-point` `C-c t`, and `eldoc-mode`, which
  shows types as point moves.
- **Uses of a name:** `next-use` `M-n` and `previous-use` `M-p`, which
  visit the uses `M-?` marked; `xref-mark-references`, the marking alone.
- **Help:**
  - `apropos` and `apropos-command` `C-h a`;
  - `where-is` `C-h w`;
  - `help` and `help-for-help` `C-h ?`, `C-h C-h`;
  - `describe-function` `C-h f`.
- **Files:** `save-some-buffers` `C-x s`, `list-directory` `C-x C-d`,
  and `revert-buffer`.
- **s7st's REPL:**
  - `s7st` and `run-s7st`;
  - `s7st-send-input`, `s7st-interrupt`;
  - `s7st-previous-input`, `s7st-next-input`.
- **Testing:** `fail-on-purpose` `C-c !`, a command that fails, to show
  the editor carries on.
