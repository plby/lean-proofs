import Wikipedia.HopfProblem.DegreeCollapseIntegralTorsionSingular
import Wikipedia.HopfProblem.DegreeCollapseIntegralSevenFourthHomology

/-!
# The original cap and torsion-evaluation pairing in dimension seven

The proved fourth-homology vanishing and the original cap isomorphism
identify the third homology of a compact simply connected seven-manifold
with its rational-mod-integer character module. The forward map is the
constructed torsion evaluation of the inverse original cap, so it is not
an arbitrary module isomorphism. Symmetry is proved in the separate
IntegralSevenLinkingSymmetry module. The original exterior meridian
comparison is proved in SevenMeridianLinking and specialized to the
supplied reflected filling in ReflectedMeridianLinking.
-/

noncomputable section

open scoped Manifold ContDiff

namespace Wikipedia.HopfProblem.DegreeCollapse.IntegralSevenLinking

open SingularMayerVietoris SingularCohomologyFree IntegralTorsionEvaluation

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Fact (Module.finrank ℝ E = 7)]
  (M : Type) [TopologicalSpace M] [T2Space M] [ChartedSpace E M] [CompactSpace M]
  [IsManifold 𝓘(ℝ, E) ∞ M] [SimplyConnectedSpace M]
  [Subsingleton (SingularHomology M 2)] [Finite (SingularHomology M 3)]

def linkingEquiv :
    SingularHomology M 3 ≃ₗ[ℤ] (SingularHomology M 3 →ₗ[ℤ] RationalResidue.Value) := by
  let : Subsingleton (SingularHomology M 4) :=
    IntegralSevenDuality.fourth_homology_subsingleton (E := E) M
  exact (IntegralCompactSupportCap.absoluteDualityEquiv (E := E) 4 M 4 3 rfl).symm.trans
    (singularTorsionEvaluationEquiv M 3)

def linking :
    SingularHomology M 3 →ₗ[ℤ] (SingularHomology M 3 →ₗ[ℤ] RationalResidue.Value) :=
  (linkingEquiv (E := E) M).toLinearMap

theorem linking_bijective : Function.Bijective (linking (E := E) M) :=
  (linkingEquiv (E := E) M).bijective

theorem linking_original_cap (a : SingularCohomology M 4) (b : SingularHomology M 3) :
    letI : Subsingleton (SingularHomology M 4) :=
      IntegralSevenDuality.fourth_homology_subsingleton (E := E) M;
    linking (E := E) M (IntegralCompactSupportCap.absoluteDualityMap (E := E) 4 M 4 3 rfl a) b =
      singularTorsionEvaluation M 3 a b := by
  let : Subsingleton (SingularHomology M 4) :=
    IntegralSevenDuality.fourth_homology_subsingleton (E := E) M
  change singularTorsionEvaluation M 3
    ((IntegralCompactSupportCap.absoluteDualityEquiv (E := E) 4 M 4 3 rfl).symm
      (IntegralCompactSupportCap.absoluteDualityEquiv (E := E) 4 M 4 3 rfl a)) b = _
  rw [LinearEquiv.symm_apply_apply]

theorem linking_left_nondegenerate (a : SingularHomology M 3)
    (ha : ∀ b, linking (E := E) M a b = 0) : a = 0 := by
  apply (linkingEquiv (E := E) M).injective
  change linking (E := E) M a = linking (E := E) M 0
  rw [map_zero]
  exact LinearMap.ext ha

end Wikipedia.HopfProblem.DegreeCollapse.IntegralSevenLinking
