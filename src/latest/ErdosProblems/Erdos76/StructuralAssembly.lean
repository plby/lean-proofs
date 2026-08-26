/-
Copyright 2026 The Lean-Proofs Authors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    http://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/
import ErdosProblems.Erdos76.AlmostBipartiteStabilityExtension
import ErdosProblems.Erdos76.AlmostBipartiteProposition42
import ErdosProblems.Erdos76.AlmostCompleteAssembly

/-!
# Assembly of the Gruslys--Letzter structural ingredients

This module records the acyclic implication from the three substantive
finite-graph ingredients to the sharp fractional theorem.  In particular,
the part-size estimate is a proved consequence of the almost-complete
decomposition theorem rather than an additional hypothesis.
-/

namespace Erdos76

noncomputable section

/-- The stability theorem, the companion almost-complete decomposition
theorem, and Proposition 4.2 together imply the sharp fractional packing
theorem of Gruslys--Letzter. -/
theorem gruslysLetzterFractional_of_components
    (hstable : FractionalStabilityDichotomy)
    (hAC : AlmostCompleteFractionalDecomposition)
    (hcross : AlmostBipartiteCrossPacking) :
    GruslysLetzterFractional := by
  apply gruslysLetzterFractional_of_structural hstable
  apply almostBipartiteSharpBound_of_internalPairBound
  apply almostBipartiteInternalPairBound_of_crossAndResidual
  exact almostBipartiteCrossAndResidual_of_components hAC
    (almostBipartitePartSizeBound hAC) hcross

/-- Certificate-oriented assembly.  The cross-packing input returns the
actual edge-disjoint family of monochromatic triangles required by
Proposition 4.2. -/
theorem gruslysLetzterFractional_of_integralCrossPacking
    (hstable : FractionalStabilityDichotomy)
    (hAC : AlmostCompleteFractionalDecomposition)
    (hcross : AlmostBipartiteIntegralCrossPacking) :
    GruslysLetzterFractional :=
  gruslysLetzterFractional_of_components hstable hAC
    (almostBipartiteCrossPacking_of_integral hcross)

/-- Expanded finite-structure boundary: the general stability dichotomy is
itself obtained from the finite classification and the pentagon-extension
table.  The human almost-bipartite extension lemma is now a proved consequence
of the companion decomposition theorem; the matching-avoiding Proposition 4.2
is likewise derived from that theorem by the corrected capacity argument. -/
theorem gruslysLetzterFractional_of_finiteStructuralComponents
    (hclass : FiniteStabilityClassification)
    (hpent : PentagonExtensionStep)
    (hAC : AlmostCompleteFractionalDecomposition) :
    GruslysLetzterFractional := by
  let hcross := almostBipartiteIntegralCrossPackingAvoiding_of_almostComplete hAC
  exact gruslysLetzterFractional_of_integralCrossPacking
    (fractionalStabilityDichotomy_of_classification_extension
      hclass hpent
        (almostBipartiteStabilityExtension_of_components hAC hcross))
    hAC (almostBipartiteIntegralCrossPacking_of_avoiding hcross)

/-- The same finite-structure boundary with the companion almost-complete
theorem expanded into its strong certificate bases.  Its exact bases at
orders `7`--`10`, structural induction step D5--D8, and Proposition 4.2 are
already kernel checked. -/
theorem gruslysLetzterFractional_of_finiteComponents
    (hclass : FiniteStabilityClassification)
    (hpent : PentagonExtensionStep)
    (hbases : AlmostCompleteStrongCertificateBases) :
    GruslysLetzterFractional := by
  let hAC := almostCompleteFractionalDecomposition_of_components hbases
  exact gruslysLetzterFractional_of_finiteStructuralComponents
    hclass hpent hAC

end

end Erdos76
