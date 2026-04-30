# Verifying a simplified xdelta3 in Isabelle/HOL with AutoCorres

## Scope — what "simplified xdelta3" means

xdelta3 is a big codebase (~15k LoC) implementing VCDIFF (RFC 3284) plus its own
extensions, secondary compression, rolling-hash matcher, and streaming I/O. The
plan is to verify a **simplified decoder** first, then decide whether to tackle
the encoder.

Suggested cuts for v1:

- **Decoder only** — encoder has search heuristics that are irrelevant to
  correctness.
- **No secondary compression** (drop DJW/FGK/LZMA). Just raw VCDIFF.
- **Fixed code table** (default table §5.4 of RFC 3284), no application-defined
  tables.
- **In-memory buffers only** — no streaming, no file I/O, no `xd3_stream`
  state machine.
- **Core instructions only**: ADD, COPY, RUN — no RUN-with-near-cache shortcuts
  beyond what the default table requires.

The core of the simplified C is probably 300–800 LoC — a tractable AutoCorres
target.

## Properties to prove

In increasing difficulty:

1. **Memory safety & absence of UB** (AutoCorres + WP gives most of this for
   free once the code parses).
2. **Termination** on any well-formed input.
3. **Bounded output size** (decoded target length = declared target window
   length).
4. **Functional correctness** — `decode(patch, src) = tgt` against a
   mathematical VCDIFF spec written in Isabelle/HOL.
5. **Round-trip** (stretch) — `decode(encode(src, tgt), src) = tgt`. Only makes
   sense if we do the encoder too.

Aim for 1–4 on the decoder. #5 is a separate project.

## Work plan

1. **Bring-up** — install Isabelle/AutoCorres, run the AutoCorres tutorial
   (`examples/`) to confirm everything builds.
2. **Carve out the C** — write `cdelta.c` containing just the simplified
   decoder. Constrain it to the AutoCorres C subset (no function pointers, no
   variadic, no `longjmp`, restricted pointer arithmetic). Test it against the
   reference xdelta3 on a corpus of patches so we know the C is correct before
   we verify it.
3. **Formal VCDIFF spec** — write an Isabelle/HOL functional specification of
   the decoder: `decode_spec :: byte list ⇒ byte list ⇒ byte list option`.
   Keep it executable via `code_generator` so we can QuickCheck it against the
   C on the same corpus.
4. **Run AutoCorres** — translate `cdelta.c` into a monadic Isabelle
   definition.
5. **Refinement proof** — prove the AutoCorres-generated function refines
   `decode_spec`. Bulk of the effort lives here: loop invariants for the
   instruction dispatch loop, invariants on the address cache, bounds on the
   output pointer.
6. **Memory safety / no-fail** — discharge the `no_fail` and guard obligations
   AutoCorres leaves behind.
7. **Write up** — document the spec, the assumptions (e.g. "input buffer is
   well-formed and non-aliasing with output"), and the gaps.

Realistic effort: 2–6 weeks for someone new to AutoCorres, much of it spent on
loop invariants for the decode loop.

## Main risks

- **AutoCorres C subset**: xdelta3 uses unions, bit-packing, and function
  pointers in the instruction table. The simplification has to eliminate these.
  Budget time for "the C won't parse" loops.
- **Spec granularity**: if `decode_spec` mirrors the C too closely, the "proof"
  becomes tautological; too abstract and refinement gets painful. Aim for a
  spec written as if RFC 3284 were the only input.
- **Address cache** (near/same arrays in VCDIFF COPY): small but stateful —
  classic source of off-by-one errors and a good target to actually catch bugs.

---

## Tools to install

Need **Isabelle/HOL** and **AutoCorres**. AutoCorres is version-locked to a
specific Isabelle release, so the order matters.

Before installing, check <https://trustworthy.systems/projects/TS/autocorres>
(or the `seL4/l4v` GitHub repo) for the current AutoCorres release and the
**exact Isabelle version** it requires. The commands below assume a
hypothetical `AutoCorres-N.NN` that targets `Isabelle<VERSION>`.

### 1. Isabelle/HOL

```bash
# From https://isabelle.in.tum.de/ — download the Linux tarball for the
# version AutoCorres requires.
cd ~/Downloads
wget https://isabelle.in.tum.de/dist/Isabelle<VERSION>_linux.tar.gz
tar -xzf Isabelle<VERSION>_linux.tar.gz -C ~/
# Add to PATH (fish):
fish_add_path ~/Isabelle<VERSION>/bin
```

Verify with `isabelle version`.

### 2. AutoCorres

```bash
cd ~/Programming
# Either clone the l4v repo (large) and use its AutoCorres subtree,
# or grab the standalone AutoCorres release tarball from trustworthy.systems.
wget <autocorres-release-url>
tar -xzf autocorres-*.tar.gz
cd autocorres-*/
# Build the heap image once — takes 10–30 min:
isabelle build -d . -b AutoCorres
# Run the tutorial to confirm:
isabelle jedit -d . -l AutoCorres examples/TraverseNoFail.thy
```

### 3. Supporting tools

- **`gcc`** and **`make`** — to compile the reference C and run it against
  xdelta3 test vectors. Probably already installed; otherwise
  `sudo apt install build-essential`.
- **`mlton`** or **Poly/ML** — bundled inside the Isabelle tarball, nothing to
  install separately.
- **`xdelta3`** reference binary for generating test patches:
  `sudo apt install xdelta3`.
- (Optional) **`python3`** for a small harness that feeds patches through both
  the C decoder and the Isabelle-exported spec.

### Open questions before install

1. Install locations — `~/Isabelle<VERSION>` and `~/Programming/autocorres-*`,
   or elsewhere?
2. Which xdelta3 version/commit as the reference?
3. Decoder first (recommended) or encoder?
4. Isabelle familiarity level — more scaffolding/tutorial-style proofs, or
   assume fluency?
