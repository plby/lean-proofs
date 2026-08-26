/-
Copyright 2026 The Lean-Proofs Authors.
Licensed under the Apache License, Version 2.0.
-/
import ErdosProblems.Erdos76.PippengerSpencerAllOrderZero
import ErdosProblems.Erdos76.PippengerSpencerOuterIteration
import ErdosProblems.Erdos76.KahnDiscretization

/-!
# Unconditional hypergraph rounding

The exact-regular inner marginal supplies the probabilistic input to the
fresh-completion outer iteration. The resulting edge coloring gives a large
matching, and integer-copy discretization gives weighted matching.
-/

namespace Erdos76

/-- The near-regular Pippenger--Spencer edge-coloring theorem. -/
theorem nearRegularPippengerSpencerEdgeColoring :
    NearRegularPippengerSpencerEdgeColoring :=
  FiniteHypergraph.sharpExactRegularTwoSidedFixedLengthInnerMarginal_to_nearRegular
    FiniteHypergraph.sharpExactRegularTwoSidedFixedLengthInnerMarginal

/-- The maximum-degree matching form of Pippenger--Spencer. -/
theorem pippengerSpencerMatching : PippengerSpencerMatching :=
  nearRegularPippengerSpencerEdgeColoring_to_pippengerSpencerMatching
    nearRegularPippengerSpencerEdgeColoring

/-- Weighted hypergraph matching with the additive error used for Erdős 76. -/
theorem kahnWeightedMatching : KahnWeightedMatching :=
  kahnWeightedMatching_of_multiplicative
    (pippengerSpencerMatching_to_kahnMultiplicative pippengerSpencerMatching)

end Erdos76
