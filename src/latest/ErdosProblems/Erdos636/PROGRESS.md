# Erdős 636 formalization progress

## Current phase

Complete.  The detailed TeX proof and the unconditional Lean formalization of
the Kwan--Sudakov resolution are implemented and verified end to end.

## Verified

- `tex/636.tex` contains the complete source-audited proof and Leanization plan.
- The shared `Erdos88.BooleanSlices` and `Erdos88.Esseen` dependencies build.
- `Erdos636.Structural`, `Erdos636.StructuralRandom`,
  `Erdos636.AugmentationFull`, `Erdos636.OuterSwitching`, and the helper
  modules listed in the TeX plan type-check without forbidden placeholders.
- The public theorem statements are unconditional; no deep-input hypothesis is
  exposed in `Erdos636.erdos636`.
- `Erdos636.StructuralIntegration.eventually_nonempty_structuralWitness_of_ksRich_fixedAmbient`
  constructs the fixed-ambient structural witness unconditionally.
- `Erdos636.AugmentationIntegration.exists_eventual_pointwiseWindows_of_structuralWitness`
  constructs the graph-facing balanced augmentation and pointwise windows with
  no schedule, event, probability, callback, or numerical premises exposed.
- `Erdos636.KwanSudakov.ramseyFreePointwiseWindows` and
  `Erdos636.KwanSudakov.hasRoundedAssembly_ramseyFree` close the Kwan--Sudakov
  chain, and `Erdos636.erdos636` states the unconditional profile-family bound.
- `lake build ErdosProblems.Erdos636` completes successfully (8790 jobs).
- The forbidden-placeholder and computational-limit scans, trailing-whitespace
  scan, and `git diff --check` are clean.
- The public theorem, its rpow/profile-count variants, and the structural and
  augmentation endpoints have axiom footprint exactly
  `[propext, Classical.choice, Quot.sound]`.

## Resolved exactness points

- Fixed-slice persistence and anti-concentration are proved on the exact sample
  spaces used downstream.
- The structural branch retains support-cardinality persistence and the exact
  finite candidate-family loss.
- Partial exposure uses independent bad-set and collision thresholds.
- Full exposure uses the high-to-low switching orientation, includes internal
  cell edges, translates the literal path by one cell contribution, and treats
  aggregate deletion deviation as a genuine geometric failure.
- Shared deletion and marked packing use the first separated subsequence, so
  the raw-increment error budget has the required square-root scale.
- All rounding, bounded-parameter, and small-constant choices are internal to
  the unconditional endpoints.

## Verification command

`lake build ErdosProblems.Erdos636`
