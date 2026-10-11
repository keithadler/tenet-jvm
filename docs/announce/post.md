# Announcement post (X Premium, long post)

Attach the four images in order: `1-hero.png`, `2-derive-compare.png`, `3-libraries.png`, `4-evidence.png`.

Before posting, update the two lines marked **[UPDATE]** if the Mathlib run or the Lean Kernel Arena submission has moved on.

---

## Post text

I've open-sourced tenet-jvm: an independent Lean 4 kernel, written in Java.

A kernel is the small program that decides whether a Lean proof is valid. Every theorem you trust rests on it. Lean's own is written in C++. The more independent implementations check the same proof, the fewer bugs can hide in all of them at once. So this is not a flag-planting exercise. I maintain it alongside Tenet (the C#/.NET kernel) and the rest of the Lean verification chain.

How it works

It reads the output of lean4export and re-checks every declaration from scratch. For inductive types it does not believe the export. It takes only the types and constructor types, derives the recursors, recursor rules and bookkeeping flags itself (nested and mutual inductives included), and rejects the file if anything differs. Derive, then compare.

What it has checked, with every declaration accepted and nothing taken on trust

• Init: 59,349 constants
• Std: 99,619
• The whole Lean library: 171,705 constants, 2,860 inductive groups, in under a minute
• con-leche, cedar and cslib from the Lean Kernel Arena: 27,959, 148,832 and 394,284 constants

Why "verified" means something

A kernel that accepted everything would print the same words. So:
• 197 of 197 decided Lean Kernel Arena tests are correct locally, with none wrongly accepted and none wrongly rejected. That includes the soundness bugs that were found in real kernels.
• Mutation tests corrupt a valid export 16 ways, and 6 more inputs that are not exports at all. All are rejected.
• It fails closed. Testing found two of my own bugs: a crash that exited as "accepted", and an empty input accepted as a valid file. Both are fixed and now tested.

Mathlib exposed more. It found a false rejection (a type hidden behind a definition) and a slowness bug (comparing arguments in the wrong order made one declaration take 10+ minutes; now 3 seconds). [UPDATE: state the Mathlib result here once the run finishes.]

What it is not: formally verified. It is tested, which is evidence and not proof. The README has a section on exactly what you still have to trust, and docs/divergences.md lists every place it decides something differently from Lean's kernel.

Java 21, no dependencies, Apache-2.0. `make` and you're running.

Next: the Lean Kernel Arena submission. [UPDATE: link the PR once it is open.]

https://github.com/keithadler/tenet-jvm

#Lean4 #FormalVerification #TheoremProving

---

## Alt text for the images

1. **hero** — Dark card reading "tenet-jvm: an independent Lean 4 kernel written in Java", with a terminal panel showing 171,705 constants and 2,860 inductive groups checked, "all verified", exit code 0.
2. **derive-compare** — Three boxes joined by arrows: "The export says" (constructors, recursor types, recursor rules, flags), "The kernel derives" (from the types and constructor types only), "Any difference is a rejection".
3. **libraries** — Bar chart of constants verified: Init 59,349 (about 25 s), Std 99,619 (45 s), Lean 171,705 (55 s), con-leche 27,959 (35 s), cedar 148,832 (50 s), cslib 394,284 (455 s).
4. **evidence** — Four statistics: 197/197 Lean Kernel Arena tests decided correctly; 0 proofs wrongly accepted; 22 mutation and bad-input tests all rejected; the checker fails closed.

---

## Claims checklist (everything above is backed by a run in this repo)

- Init / Std / Lean counts: `docs/status.md`
- con-leche / cedar / cslib counts: `docs/status.md`
- 197/197, 0 wrongly accepted or rejected: `docs/testing.md` (`tools/arena_check.py`)
- 16 mutants + 6 malformed inputs: `tests/negative.py`
- Bugs found in my own code: `docs/testing.md`
- Not claimed: Mathlib complete, an arena ranking, or that it is faster than another kernel.
