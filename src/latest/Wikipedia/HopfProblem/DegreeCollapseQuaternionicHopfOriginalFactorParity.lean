import Wikipedia.HopfProblem.DegreeCollapseQuaternionicHopfFiniteFactorContraction
import Wikipedia.HopfProblem.DegreeCollapseConstantLiftedHopfFrameTwist

/-!
# Both exact original Hopf-square factor parities are one

Use the checked finite contractions, the actual inverse-chart and normal
orthonormalization comparisons, and the original source-twist obstruction.
These are the geometric factor parities in the original regular-fiber atlas,
for every fixed value of the other factor and every radial fallback point.
-/

noncomputable section

namespace Wikipedia.HopfProblem.DegreeCollapse.QuaternionicHopfOriginalFactorParity

open NoExoticSixSphere QuaternionicHopf
open QuaternionicHopfFiberFactors QuaternionicHopfPairedFiniteOperators
open QuaternionicHopfFiniteFactorContraction SphereFiniteChartContraction

theorem leftParity_one (a : Sphere 16) (r : Sphere 3) : leftParity a r = 1 := by
  obtain ⟨b, hb⟩ := leftMap_contracts a r
  have h : ((fixedCoordinates (0 : V 16)).comp (leftMap a r)).Homotopic
      (ContinuousMap.const _ (fixedCoordinates (0 : V 16) b)) := by
    simpa only [ContinuousMap.comp_const] using
      (ContinuousMap.Homotopic.refl (fixedCoordinates (k := 14) (0 : V 16))).comp hb
  rw [QuaternionicHopfFiniteFactorOperators.leftParity_eq_fixed]
  exact ConstantLiftedHopfFrameTwist.twisted_parity_of_contraction _ _ h

theorem rightParity_one (a : Sphere 16) (q : Sphere 3) : rightParity a q = 1 := by
  obtain ⟨b, hb⟩ := rightMap_contracts a q
  have h : ((fixedCoordinates (0 : V 16)).comp (rightMap a q)).Homotopic
      (ContinuousMap.const _ (fixedCoordinates (0 : V 16) b)) := by
    simpa only [ContinuousMap.comp_const] using
      (ContinuousMap.Homotopic.refl (fixedCoordinates (k := 14) (0 : V 16))).comp hb
  rw [QuaternionicHopfFiniteFactorOperators.rightParity_eq_fixed]
  exact ConstantLiftedHopfFrameTwist.twisted_parity_of_contraction _ _ h

end Wikipedia.HopfProblem.DegreeCollapse.QuaternionicHopfOriginalFactorParity
