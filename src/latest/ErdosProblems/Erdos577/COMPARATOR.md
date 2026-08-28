# Erdős 577 Comparator setup

## Canonical import layout

The Comparator-facing theorem `Erdos577.erdos_577` has been consolidated into
`src/latest/ErdosProblems/Erdos577.lean`. The separate
`Erdos577Comparator.lean` wrapper is no longer needed, and the configuration
now uses `ErdosProblems.Erdos577` as its solution module. All supporting
files remain under `src/latest/ErdosProblems/Erdos577/`.

The report below records the original e3 verification before that layout
change; its old wrapper paths and commands are historical.

## Local import verification

The source development was committed on e3 as `ba09e5b43` (`Add Erdos577.`).
The local import includes the main file and all 851 supporting Lean modules,
plus the challenge and configuration. `ErdosProblems/All.lean` imports the
main file, but that aggregate module was not built or run.

The following focused commands passed in `src/latest`:

```sh
lake env lean -o .lake/build/lib/lean/ErdosProblems/Erdos577.olean ErdosProblems/Erdos577.lean
lake env lean ComparatorChallenges/ErdosProblems/Erdos577.lean
lake env lean ErdosProblems/Erdos577/Verification.lean
```

The main-file check reused e3's compiled supporting-module artifacts. The
full verification module produced 2,032 axiom reports: 2,030 use only
`propext`, `Classical.choice`, and `Quot.sound`; two use no axioms. Separate
checks of the new `erdos_577` export and the three original main results
also report only those three standard axioms. The challenge has its single
expected `sorry` warning. Source scans found no placeholders, new axiom
declarations, unsafe or opaque declarations, native proof evaluation, or
`set_option` directives in the solution's Lean files.

The JSON configuration, unique Lake registration, and scoped whitespace
checks passed. Running the configured Comparator command locally stopped
with `Comparator requires landrun in PATH or COMPARATOR_LANDRUN to be set.`
Full Comparator acceptance therefore remains unverified.

## Original e3 verification

Date: 2026-08-28. The setup is registered and both Lean modules compile.
**Comparator acceptance has not been established:** the standard runner stops
because `landrun` is unavailable. The completed mathematical proof and its
previous validation remain unchanged.

## Files

Paths below are relative to the repository root.

| File | Purpose |
| --- | --- |
| `src/latest/ComparatorChallenges/ErdosProblems/Erdos577.lean` | Independent challenge; imports only Mathlib and contains the one standard challenge `sorry` expressly authorized by the user. |
| `src/latest/ComparatorChallenges/ErdosProblems/Erdos577.json` | Compares `Erdos577.erdos_577`, permits only the three standard axioms, and enables Nanoda. |
| `src/latest/ErdosProblems/Erdos577Comparator.lean` | Fully proved wrapper around `Erdos577.exists_disjoint_four_cycles`; includes `#print axioms`. |
| `src/latest/ComparatorChallenges/lakefile.toml` | Adds exactly one `Erdos577` root to the Erdős challenge library. Other tasks' changes are preserved. |
| `src/latest/ErdosProblems/Erdos577/COMPARATOR.md` | This verification and environment report. |
| `tmp/erdos577/verify_comparator.py` | Static setup checks and comparison against the completed proof's SHA-256 manifest. It is not a proof checker. |

The challenge and wrapper have textually identical explicit theorem statements:
for every natural `k`, if `Fintype.card V = 4 * k` and `2 * k ≤ G.minDegree`,
there is an embedding `Fin k × Fin 4 ↪ V` whose four cyclic adjacencies hold
for every cycle. Global injectivity supplies distinct vertices and disjoint
cycles. No inducedness is required, and `k = 0` is included. The solution
wrapper has no placeholder or new axiom.

## Checks that passed

Working directory: `/root/code/lean-proofs/src/latest`.

```sh
/root/.config/elan/toolchains/leanprover--lean4---v4.33.0/bin/lake build Erdos577 ErdosProblems.Erdos577Comparator
/root/.config/elan/toolchains/leanprover--lean4---v4.33.0/bin/lake env lean ErdosProblems/Erdos577Comparator.lean
```

Both exit 0. The build reports 9,559 jobs. The only challenge warning is its
authorized `sorry`. Existing BoundedGaps/AINTLIB dirty-checkout warnings remain.
The wrapper's axiom report is exactly:

```text
'Erdos577.erdos_577' depends on axioms: [propext, Classical.choice, Quot.sound]
```

Working directory: `/root/code/lean-proofs`.

```sh
python3 tmp/erdos577/verify_comparator.py
git diff --check -- src/latest/ComparatorChallenges/ErdosProblems/Erdos577.lean src/latest/ComparatorChallenges/ErdosProblems/Erdos577.json src/latest/ComparatorChallenges/lakefile.toml src/latest/ErdosProblems/Erdos577Comparator.lean src/latest/ErdosProblems/Erdos577/COMPARATOR.md
git diff --cached --name-only -- src/latest/ComparatorChallenges/ErdosProblems/Erdos577.lean src/latest/ComparatorChallenges/ErdosProblems/Erdos577.json src/latest/ComparatorChallenges/lakefile.toml src/latest/ErdosProblems/Erdos577Comparator.lean src/latest/ErdosProblems/Erdos577/COMPARATOR.md
```

These checks exit 0; the cached-diff command prints nothing. Static checks
verify configuration values, identical statement text, Mathlib-only challenge
imports, unique registration, whitespace, the single authorized challenge
placeholder, and absence of solution placeholders and computational options.
All 853 hashes from the completed proof manifest are unchanged: 852 Lean files
and the TeX source. No files were staged or committed, no computational limits
were raised, and no proof sources or shared dependency configurations changed.

## Standard runner: not yet accepted

Working directory: `/root/code/lean-proofs/src/latest`.

```sh
ComparatorChallenges/run.sh ComparatorChallenges/ErdosProblems/Erdos577.json
```

Exit 1, with:

```text
Comparator requires landrun in PATH or COMPARATOR_LANDRUN to be set.
```

Runtime inspection also found no `nanoda_bin` in `PATH`, UID 0, and no systemd
user session. This prerequisite probe exits 1:

```sh
systemd-run --property=RestrictAddressFamilies=~AF_UNIX --user --pipe --wait -- /usr/bin/true
```

```text
Failed to connect to bus: No medium found
```

The pinned Comparator README requires an unprivileged user and its documented
sandbox setup for the stated security guarantee. To complete validation, run
the registered command in such an environment with real `landrun`, the
compatible exporter, Nanoda, and a working systemd user session. No fake
sandbox, disabled Nanoda check, expanded axiom list, or manufactured success
cache was used. A successful Lean build is not reported as Comparator success.

## Checker bootstrap investigation

Initially the runner's `lake build @Comparator/comparator @lean4export/lean4export`
failed because the surrounding workspace also resolved `Comparator.*` modules
under BoundedGaps and Waring, where those files do not exist. The exporter
nevertheless built. Building the existing pinned Comparator package in its own
workspace avoids that module conflict, without editing package configurations:

```sh
cd /root/code/lean-proofs/src/latest/.lake/packages/Comparator
/root/.config/elan/toolchains/leanprover--lean4---v4.33.0/bin/lake --packages=/root/code/lean-proofs/tmp/erdos577/comparator-packages.json build comparator
```

This command ultimately exits 0, with 15 jobs. Its task-local package override
points to the already present exporter checkout at the revision required by
Comparator's manifest. It changes only the checker build's package resolution,
not the challenge, solution, or Comparator verification configuration.

An initial standalone link failed with a bus error while the project volume
had only 8 KiB free. Only generated Comparator/exporter `build/bin` directories
were relocated to `/root/.cache/erdos577-01a03c40-comparator/`, preserving their
original paths with symlinks. Linking then passed and approximately 267 MiB was
freed on the project volume. No source or existing proof artifact was removed.

Evidence is in `tmp/erdos577/validation/comparator-build.txt`,
`comparator-wrapper-direct.txt`, `comparator-static-audit.json`, and
`comparator-run.txt`. The original `FINAL_REPORT.md` and its proof audit are
preserved separately.
