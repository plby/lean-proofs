import Wikipedia.NoExoticSixSphere.CorankOneGeneric
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
import Mathlib.Topology.DiscreteSubset

/-!
# Isolated singular points in a corank-one chart

When source and residual dimensions agree, a regular residual zero is
isolated by the actual inverse function theorem. Compact sets contained in
the chart therefore contain only finitely many singular points. No global
cover of all rank strata is assumed here.
-/

noncomputable section

open Set Function Module
open scoped ContDiff

namespace NoExoticSixSphere.CorankOne

variable {X E F : Type} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [FiniteDimensional ℝ X] [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
  [FiniteDimensional ℝ F]

def chartSingularSet (D : X → BlockMap E F) : Set X :=
  {x | D x ∈ chart ∧ ¬ Injective (D x)}

theorem chartSingularSet_isDiscrete (D : X → BlockMap E F) (hD : ContDiff ℝ ∞ D)
    (hd : finrank ℝ X = finrank ℝ F)
    (hreg : ∀ x, D x ∈ chart → residual (D x) = 0 →
      Surjective (fderiv ℝ (fun y ↦ residual (D y)) x)) :
    IsDiscrete (chartSingularSet D) := by
  rw [isDiscrete_iff_forall_mem_exists_isOpen]
  intro x hx
  have hx0 : residual (D x) = 0 := (singular_iff_residual_zero hx.1).mp hx.2
  let R : X → F := fun y ↦ residual (D y)
  have hs : Surjective (fderiv ℝ R x) := hreg x hx.1 hx0
  have hi : Injective (fderiv ℝ R x) :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hd).mpr hs
  let L : X ≃L[ℝ] F :=
    (LinearEquiv.ofBijective (fderiv ℝ R x).toLinearMap ⟨hi, hs⟩).toContinuousLinearEquiv
  have hR : ContDiffAt ℝ ∞ R x :=
    (contDiffAt_residual (D x) (leading_invertible hx.1)).comp x hD.contDiffAt
  have hL : HasFDerivAt R L.toContinuousLinearMap x :=
    (hR.differentiableAt (by simp)).hasFDerivAt
  let e := hR.toOpenPartialHomeomorph R hL (by simp)
  have he : x ∈ e.source := hR.mem_toOpenPartialHomeomorph_source hL (by simp)
  refine ⟨e.source, e.open_source, ?_⟩
  ext y
  constructor
  · rintro ⟨hy, hyc⟩
    apply Set.mem_singleton_iff.mpr
    apply e.injOn hy he
    exact ((singular_iff_residual_zero hyc.1).mp hyc.2).trans hx0.symm
  · intro hy
    rcases Set.mem_singleton_iff.mp hy with rfl
    exact ⟨he, hx⟩

theorem finite_singularSet_inter (D : X → BlockMap E F) (hD : ContDiff ℝ ∞ D)
    (hd : finrank ℝ X = finrank ℝ F)
    (hreg : ∀ x, D x ∈ chart → residual (D x) = 0 →
      Surjective (fderiv ℝ (fun y ↦ residual (D y)) x))
    {K : Set X} (hK : IsCompact K) (hchart : ∀ x ∈ K, D x ∈ chart) :
    (K ∩ {x | ¬ Injective (D x)}).Finite := by
  have hc : IsClosed {x | ¬ Injective (D x)} :=
    (ContinuousLinearMap.isOpen_injective.preimage hD.continuous).isClosed_compl
  apply (hK.inter_right hc).finite
  apply (chartSingularSet_isDiscrete D hD hd hreg).mono
  intro x hx
  exact ⟨hchart x hx.1, hx.2⟩

theorem dense_isolated_translations (D : X → BlockMap E F) (hD : ContDiff ℝ ∞ D)
    (hd : finrank ℝ X = finrank ℝ F) :
    Dense {A : BlockMap E F | IsDiscrete (chartSingularSet (fun x ↦ D x + A))} :=
  (dense_regular_translations D hD).mono fun A hA ↦
    chartSingularSet_isDiscrete (fun x ↦ D x + A) (hD.add contDiff_const) hd hA

end NoExoticSixSphere.CorankOne
