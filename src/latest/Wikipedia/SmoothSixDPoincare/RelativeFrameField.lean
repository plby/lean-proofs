import Wikipedia.SmoothSixDPoincare.FrameFieldPerturbation
import Mathlib.Geometry.Manifold.PartitionOfUnity
import Mathlib.Analysis.Normed.Module.ContinuousInverse

/-!
# Full-rank two-column fields relative to a prescribed closed locus

A smooth cutoff vanishes on a neighborhood of the fixed closed set and is
one near the compact rank-deficient locus. The weighted bad-parameter
argument removes every remaining kernel without changing any fixed germ.
-/

noncomputable section

open Set Function Filter Topology
open scoped ContDiff Manifold

namespace Wikipedia.SmoothSixDPoincare.FrameField

open PlaneImmersion (Plane linearMap)

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]

/-- A scalar-weighted perturbation removes kernels where the weight is nonzero. -/
theorem exists_weighted_fullRank_perturbation {L : Plane → (Plane →L[ℝ] F)}
    {β : Plane → ℝ} (hL : ContDiff ℝ ∞ L) (hβ : ContDiff ℝ ∞ β)
    (hdim : 4 ≤ Module.finrank ℝ F) {K : Set Plane}
    (hzero : ∀ x ∈ K, β x = 0 → Injective (L x)) {ε : ℝ} (hε : 0 < ε) :
    ∃ A : F × F, ‖A‖ < ε ∧ ContDiff ℝ ∞ (fun x => L x + β x • linearMap A) ∧
      ∀ x ∈ K, Injective (L x + β x • linearMap A) := by
  let U := {x : Plane | β x ≠ 0}
  let S : Plane → (Plane →L[ℝ] F) := fun x => (β x)⁻¹ • L x
  have hU : IsOpen U := isOpen_ne_fun hβ.continuous continuous_const
  have hS : ContDiffOn ℝ ∞ S U :=
    (hβ.contDiffOn.inv (fun _ hx => hx)).smul hL.contDiffOn
  obtain ⟨A, hA, hiA⟩ := exists_small_fullRank_perturbation hU hS hdim hε
  refine ⟨A, hA, hL.add (hβ.smul contDiff_const), ?_⟩
  intro x hx
  by_cases hβx : β x = 0
  · rw [hβx, zero_smul, add_zero]
    exact hzero x hx hβx
  · have hid : L x + β x • linearMap A = β x • (S x + linearMap A) := by
      rw [smul_add]
      change L x + β x • linearMap A = β x • ((β x)⁻¹ • L x) + β x • linearMap A
      rw [smul_inv_smul₀ hβx]
    rw [hid]
    intro v w hvw
    exact hiA x hβx ((smul_right_injective F hβx) hvw)

/-- Repair a two-column field on a compact region while retaining a whole neighborhood
of the prescribed closed set, including every original boundary germ. -/
theorem exists_fullRank_field_rel_closed {L : Plane → (Plane →L[ℝ] F)}
    (hL : ContDiff ℝ ∞ L) (hdim : 4 ≤ Module.finrank ℝ F)
    {K C : Set Plane} (hK : IsCompact K) (hC : IsClosed C)
    (hi : ∀ x ∈ K ∩ C, Injective (L x)) :
    ∃ L' : Plane → (Plane →L[ℝ] F), ContDiff ℝ ∞ L' ∧ L' =ᶠ[𝓝ˢ C] L ∧
      ∀ x ∈ K, Injective (L' x) := by
  let B := K ∩ {x : Plane | ¬Injective (L x)}
  have hgood : IsOpen {x : Plane | Injective (L x)} :=
    ContinuousLinearMap.isOpen_injective.preimage hL.continuous
  have hB : IsCompact B := hK.inter_right hgood.isClosed_compl
  have hdisj : Disjoint C B := disjoint_left.mpr (fun x hxC hxB => hxB.2 (hi x ⟨hxB.1, hxC⟩))
  obtain ⟨β, hβ0, hβ1, _⟩ := exists_contMDiffMap_zero_one_nhds_of_isClosed
    𝓘(ℝ, Plane) hC hB.isClosed hdisj (n := ⊤)
  have hzero : ∀ x ∈ K, β x = 0 → Injective (L x) := by
    intro x hx hβx
    by_contra hnot
    have h1 : β x = 1 := hβ1.self_of_nhdsSet x ⟨hx, hnot⟩
    rw [hβx] at h1
    exact zero_ne_one h1
  obtain ⟨A, _, hA, hiA⟩ := exists_weighted_fullRank_perturbation hL β.contMDiff.contDiff
    hdim hzero (show (0 : ℝ) < 1 by norm_num)
  refine ⟨fun x => L x + β x • linearMap A, hA, ?_, hiA⟩
  filter_upwards [hβ0] with x hx
  rw [hx, zero_smul, add_zero]

end Wikipedia.SmoothSixDPoincare.FrameField
