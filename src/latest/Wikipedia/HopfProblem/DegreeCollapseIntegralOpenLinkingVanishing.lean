import Wikipedia.HopfProblem.DegreeCollapseIntegralRelativeForgetZero
import Wikipedia.HopfProblem.DegreeCollapseIntegralOpenManifoldDuality
import Wikipedia.HopfProblem.DegreeCollapseIntegralSevenLinking

/-!
# The original closed linking pairing vanishes away from an open subset

Compact-support representatives and the original forgetting map show
that an extended open-supported class pulls back to zero along a map
avoiding the open subset. Original open cap duality represents every
homology class of that open subset. Original cap naturality and torsion
evaluation then prove the vanishing of the original closed linking value.
-/

noncomputable section

open TopologicalSpace
open scoped Manifold ContDiff

namespace Wikipedia.HopfProblem.DegreeCollapse.IntegralCompactSupportCohomology

open SingularCohomologyFree

variable {M X : Type} [TopologicalSpace M] [T2Space M] [CompactSpace M]
  [TopologicalSpace X] (U : Set M) (hU : IsOpen U)
  (f : C(X, M)) (hf : ∀ x, f x ∉ U)

include hf in
theorem absolute_inclusion_pullback_zero (p : ℕ) (a : Cohomology U p) :
    singularCohomologyPullback f p (absoluteEquiv M p (inclusion U hU p a)) = 0 := by
  obtain ⟨K, c, rfl⟩ := exists_representative U p a
  let c' : Component M p (imageCompact U K) :=
    IntegralOpenSupport.extension U hU (K : Set U) K.isCompact p c
  change singularCohomologyPullback f p (absoluteEquiv M p (of M p (imageCompact U K) c')) = 0
  rw [absoluteEquiv_of]
  apply RelativeIntegralCap.cohomologyForget_pullback_zero
  intro x hx
  obtain ⟨u, _, hu⟩ := hx
  exact hf x (hu ▸ u.property)

end Wikipedia.HopfProblem.DegreeCollapse.IntegralCompactSupportCohomology

namespace Wikipedia.HopfProblem.DegreeCollapse.IntegralSevenLinking

open SingularMayerVietoris SingularCohomologyFree IntegralTorsionEvaluation

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Fact (Module.finrank ℝ E = 7)]
  (M : Type) [TopologicalSpace M] [T2Space M] [ChartedSpace E M] [CompactSpace M]
  [IsManifold 𝓘(ℝ, E) ∞ M] [SimplyConnectedSpace M]
  [Subsingleton (SingularHomology M 2)] [Finite (SingularHomology M 3)]
  {X : Type} [TopologicalSpace X] [Finite (SingularHomology X 3)]
  [Subsingleton (SingularHomology X 4)] (U : Opens M)
  (f : C(X, M)) (hf : ∀ x, f x ∉ U)

include hf in
theorem linking_open_away_zero (a : SingularHomology U 3) (b : SingularHomology X 3) :
    linking (E := E) M (singularHomologyMap (subtypeInclusion (U : Set M)) 3 a)
      (singularHomologyMap f 3 b) = 0 := by
  obtain ⟨c, rfl⟩ := (IntegralOpenFundamentalClass.dualityMap_bijective
    (E := E) 4 U 4 3 rfl).2 a
  rw [IntegralOpenFundamentalClass.dualityMap_inclusion]
  let α := IntegralCompactSupportCohomology.absoluteEquiv M 4
    (IntegralCompactSupportCohomology.inclusion (U : Set M) U.isOpen 4 c)
  have hcap : IntegralCompactSupportCap.absoluteDualityMap (E := E) 4 M 4 3 rfl α =
      IntegralCompactSupportCap.dualityMap (E := E) 4 M 4 3 rfl
        (IntegralCompactSupportCohomology.inclusion (U : Set M) U.isOpen 4 c) := by
    change IntegralCompactSupportCap.dualityMap (E := E) 4 M 4 3 rfl
      ((IntegralCompactSupportCohomology.absoluteEquiv M 4).symm
        (IntegralCompactSupportCohomology.absoluteEquiv M 4
          (IntegralCompactSupportCohomology.inclusion (U : Set M) U.isOpen 4 c))) = _
    rw [LinearEquiv.symm_apply_apply]
  let : Subsingleton (SingularHomology M 4) :=
    IntegralSevenDuality.fourth_homology_subsingleton (E := E) M
  rw [← hcap, linking_original_cap, ← singularTorsionEvaluation_naturality]
  have hzero : singularCohomologyPullback f 4 α = 0 :=
    IntegralCompactSupportCohomology.absolute_inclusion_pullback_zero
      (U : Set M) U.isOpen f hf 4 c
  rw [hzero, map_zero, LinearMap.zero_apply]

end Wikipedia.HopfProblem.DegreeCollapse.IntegralSevenLinking
