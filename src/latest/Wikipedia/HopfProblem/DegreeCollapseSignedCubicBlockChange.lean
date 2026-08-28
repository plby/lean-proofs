import Wikipedia.HopfProblem.DegreeCollapseCubicFieldAutomorphisms
import Wikipedia.HopfProblem.DegreeCollapseCubicFlowCylinder
import Wikipedia.HopfProblem.DegreeCollapseNativeRationalFieldChart
import Wikipedia.SmoothSixDPoincare.SignedSplitCoordinates

/-!
# Absorbing the actual split holonomy blocks into a cubic endpoint chart

The signed splitting identifies both the rate operator and its exponential
flow. Arbitrary invertible changes within its two blocks commute with both.
Their actual forward chart change preserves the cubic native field and
has the exact transformed endpoint-slice formula.
-/

noncomputable section

open Set Function Manifold
open scoped Topology ContDiff
open Wikipedia.SmoothSixDPoincare

namespace Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation

variable {m : ℕ}

open Classical in
theorem signed_split_transverse_rate (σ : Fin m → ℝ)
    (hσ : ∀ i, σ i = -1 ∨ σ i = 1) (z : Fin m → ℝ) :
    MorseHandle.splitCoordinates σ (fun i => σ i * z i) =
      ((-1 : ℝ) • (MorseHandle.splitCoordinates σ z).1,
        (1 : ℝ) • (MorseHandle.splitCoordinates σ z).2) := by
  apply Prod.ext
  · ext i
    simp [i.2]
  · ext i
    simp [(hσ i.1).resolve_left i.2]

open Classical in
theorem signed_split_transverse_exponential (σ : Fin m → ℝ)
    (hσ : ∀ i, σ i = -1 ∨ σ i = 1) (t : ℝ) (z : Fin m → ℝ) :
    MorseHandle.splitCoordinates σ (fun i => Real.exp (-σ i * t) * z i) =
      (Real.exp t • (MorseHandle.splitCoordinates σ z).1,
        Real.exp (-t) • (MorseHandle.splitCoordinates σ z).2) := by
  apply Prod.ext
  · ext i
    simp [i.2]
  · ext i
    simp [(hσ i.1).resolve_left i.2]

open Classical in
theorem signed_block_change_cubic_cylinder (σ : Fin m → ℝ)
    (hσ : ∀ i, σ i = -1 ∨ σ i = 1)
    (P : MorseHandle.NegativeSpace σ ≃L[ℝ] MorseHandle.NegativeSpace σ)
    (S : MorseHandle.PositiveSpace σ ≃L[ℝ] MorseHandle.PositiveSpace σ)
    (a t : ℝ) (z : Fin m → ℝ) :
    transverseFieldChange (splitTransverseChange (MorseHandle.splitCoordinates σ) P S)
      (cubicFlowCylinder σ a (z, t)) =
    cubicFlowCylinder σ a (splitTransverseChange (MorseHandle.splitCoordinates σ) P S z, t) := by
  apply Prod.ext
  · rfl
  · exact splitTransverseChange_commutes (fun i => Real.exp (-σ i * t))
      (MorseHandle.splitCoordinates σ) (Real.exp t) (Real.exp (-t))
      (signed_split_transverse_exponential σ hσ t) P S z

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace M] [ChartedSpace E M]

open Classical in
theorem exists_signed_block_changed_cubic_chart (σ : Fin m → ℝ)
    (hσ : ∀ i, σ i = -1 ∨ σ i = 1)
    (P : MorseHandle.NegativeSpace σ ≃L[ℝ] MorseHandle.NegativeSpace σ)
    (S : MorseHandle.PositiveSpace σ ≃L[ℝ] MorseHandle.PositiveSpace σ)
    (Φ : PartialDiffeomorph 𝓘(ℝ, Model m) 𝓘(ℝ, E) (Model m) M ∞)
    (V : (x : M) → TangentSpace 𝓘(ℝ, E) x) (τ : ℝ)
    (hmodel : ∀ y ∈ Φ.target, V y = nativeCubicDescent σ Φ τ y) :
    ∃ Ψ : PartialDiffeomorph 𝓘(ℝ, Model m) 𝓘(ℝ, E) (Model m) M ∞,
      Ψ.target = Φ.target ∧
      (∀ s : ℝ, ((s, (0 : Fin m → ℝ)) ∈ Ψ.source ↔ (s, 0) ∈ Φ.source)) ∧
      (∀ s : ℝ, Ψ (s, 0) = Φ (s, 0)) ∧
      (∀ y ∈ Ψ.target, V y = nativeCubicDescent σ Ψ τ y) ∧
      ∀ (a t : ℝ) (u : MorseHandle.NegativeSpace σ × MorseHandle.PositiveSpace σ),
        Ψ (cubicFlowCylinder σ a ((MorseHandle.splitCoordinates σ).symm u, t)) =
        Φ (cubicFlowCylinder σ a ((MorseHandle.splitCoordinates σ).symm (P u.1, S u.2), t)) := by
  let T := splitTransverseChange (MorseHandle.splitCoordinates σ) P S
  let D := transverseFieldChange T
  let Ψ := D.toDiffeomorph.toPartialDiffeomorph.trans Φ
  have htarget : Ψ.target = Φ.target := by
    ext y
    change (y ∈ Φ.target ∧ Φ.symm y ∈ (univ : Set (Model m))) ↔ y ∈ Φ.target
    simp only [mem_univ, and_true]
  have hDaxis (s : ℝ) : D (s, 0) = (s, 0) := by
    change (s, T 0) = (s, 0)
    rw [map_zero]
  have hpush (p : Model m) (_ : p ∈ D.toDiffeomorph.toPartialDiffeomorph.source) :
      fderiv ℝ D.toDiffeomorph.toPartialDiffeomorph p (cubicDescent σ τ p) =
        cubicDescent σ τ (D p) := by
    change fderiv ℝ D p (cubicDescent σ τ p) = _
    rw [D.fderiv]
    exact transverseFieldChange_cubicDescent σ T
      (splitTransverseChange_commutes σ (MorseHandle.splitCoordinates σ) (-1) 1
        (signed_split_transverse_rate σ hσ) P S) τ p
  refine ⟨Ψ, htarget, ?_, ?_, ?_, ?_⟩
  · intro s
    change ((s, (0 : Fin m → ℝ)) ∈ univ ∧ D (s, 0) ∈ Φ.source) ↔ (s, 0) ∈ Φ.source
    rw [hDaxis]
    simp only [mem_univ, true_and]
  · intro s
    change Φ (D (s, 0)) = Φ (s, 0)
    rw [hDaxis]
  · intro y hy
    rw [hmodel y (htarget ▸ hy)]
    exact (partialChartField_of_model_conjugacy D.toDiffeomorph.toPartialDiffeomorph Φ
      (cubicDescent σ τ) (cubicDescent σ τ) hpush hy).symm
  · intro a t u
    change Φ (D (cubicFlowCylinder σ a ((MorseHandle.splitCoordinates σ).symm u, t))) = _
    rw [signed_block_change_cubic_cylinder σ hσ P S]
    have hT : T ((MorseHandle.splitCoordinates σ).symm u) =
        (MorseHandle.splitCoordinates σ).symm (P u.1, S u.2) := by
      simp only [T, splitTransverseChange, ContinuousLinearEquiv.trans_apply,
        ContinuousLinearEquiv.apply_symm_apply, ContinuousLinearEquiv.prodCongr_apply]
    change Φ (cubicFlowCylinder σ a (T ((MorseHandle.splitCoordinates σ).symm u), t)) = _
    rw [hT]

end Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation
