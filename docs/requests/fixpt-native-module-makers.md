# Request to Fixpt: native code for files that make modules

Status: done by Fixpt in 2d706414 (2026-10-28; Fixpt `DONE.md` §145),
pulled by Heist's c8eacb3c. No file runs as cellular code now; typing in
a burst is 7 µs a key, as with globals; start-up is 6.1 s, against 4.4 s.
Drafted 2026-10-28 by Heist, against Fixpt 5731f52e.

## What Heist tried

The editor (`editor/`, 15 files, ~7000 lines) runs as one program of
globals: `fixpt run base.fx buffer.fx … main.fx`. On branch
`editor-modules` each file is instead a `load-input` file of the
conductor's shape, a function of the modules made from the files before
it, each typed by `load-input-moduleof`, its body
`(module (hide (include m-base) …) …the file as it was…)`. `editor.fx`
makes each once, in order. Both checkers accept it, and every UI test
passes. Converting the files took two renames (`flow.fx`'s `span`
shadowed `screen.fx`'s) and wrapping the ~200 top-level registration
calls (`define-command!`, …) as hidden definitions. `load-moduleof`,
`include` and `hide` did what the design said.

## What it costs

10 of the 15 files now run as cellular code:

```
; not in the native convention yet, so `%shared:input:buffer.fx` runs as cellular code:
;   `lambda/lambda@1001:540` makes a closure of `lambda/lambda/lambda@1001:19549` has no register code
; … `%shared:input:frame.fx` runs as cellular code: `lambda/lambda@1001:1275`: a frame too large
```

- **a frame too large** (frame, process, files, help, eldoc, main): the
  maker's frame holds every item of the module, more than the 4080-byte
  limit (`direct.rs:2020`).
- **no register code** (buffer, sexp, index, calls): an item that is a
  procedure is a closure over the module's other items, and a closure
  over more than `register-regs` (8) has no register code
  (`direct.rs:1823`). At the top level those items were globals and were
  not captured.

| | globals (`main`) | modules (`editor-modules`) |
| --- | --- | --- |
| start-up, to the first screen | 4.4 s | 8.4 s |
| typing, a burst of 200 keys (`tests/bench-typing.fx`) | 7 µs a key | 39 µs a key |
| typing, 200 keys one at a time | 430 µs a key | 518 µs a key |

## What Heist asks

Native code for a `load-input` file whose value is a `lambda` around a
`module`, at the speed its procedures had as globals. Either:

1. Compile the items of a module a maker makes the way globals are: as
   slots of the module (or of an environment record) that the item
   procedures reach through one pointer, not as captured variables each.
   Then neither limit is met however many items a file has.
2. Or lift the two limits: closures over more than 8 variables getting
   register code (an environment record past 8), and frames past 4080
   bytes.

(1) is what Heist would prefer: with (2) each closure still copies what
it captures, and a file of 150 items makes 150 closures each over many of
them.

Also worth knowing: start-up is about twice as long even apart from
cellular code; `fixpt check editor.fx` takes 6.9 s. Each file's
parameters are typed by `load-input-moduleof` of every file before it, so
the types grow as the square of the files (the module types printed by
`fixpt check` are 3.2 MB). Heist could pass fewer modules, or `restrict`
them; whether Fixpt can make the walk cheaper is a second question.
