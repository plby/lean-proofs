import Wikipedia.SmoothSixDPoincare.LocalFrameFieldExtension
import Wikipedia.SmoothSixDPoincare.SmoothImageAvoidance

/-!
# Relative extension of a nonzero normal vector over a planar disk

A cutoff vanishes near the prescribed closed locus and is one near the compact
zero set. The low-dimensional smooth-image argument removes every remaining
zero. In a three-dimensional normal model this extends one prescribed normal
column across the two-dimensional disk while retaining its complete boundary germ.
-/

noncomputable section

open Set Function Filter Topology
open scoped ContDiff Manifold

namespace Wikipedia.SmoothSixDPoincare.FrameField

variable {P F : Type*}
  [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]

/-- Remove all zeros on the compact region, retaining a whole neighborhood of the fixed set. -/
theorem exists_nonzero_field_rel_closed {v : P → F} (hv : ContDiff ℝ ∞ v)
    (hdim : Module.finrank ℝ P < Module.finrank ℝ F)
    {K C : Set P} (hK : IsCompact K) (hC : IsClosed C)
    (hne : ∀ x ∈ K ∩ C, v x ≠ 0) :
    ∃ v' : P → F, ContDiff ℝ ∞ v' ∧ v' =ᶠ[𝓝ˢ C] v ∧ ∀ x ∈ K, v' x ≠ 0 := by
  let B : Set P := K ∩ v ⁻¹' {0}
  have hB : IsCompact B := hK.inter_right (isClosed_singleton.preimage hv.continuous)
  have hdisj : Disjoint C B := disjoint_left.mpr (fun x hxC hxB => hne x ⟨hxB.1, hxC⟩ hxB.2)
  obtain ⟨β, hβ0, hβ1, -⟩ := exists_contMDiffMap_zero_one_nhds_of_isClosed
    𝓘(ℝ, P) hC hB.isClosed hdisj (n := ⊤)
  have hfixed : ∀ x ∈ K, β x = 0 → v x ≠ 0 := by
    intro x hx hβx hvx
    have heq : β x = 1 := hβ1.self_of_nhdsSet x ⟨hx, hvx⟩
    exact zero_ne_one (hβx.symm.trans heq)
  let Z := EuclideanSpace ℝ (Fin 0)
  let g : Z → F := fun _ => 0
  have hg : ContMDiff 𝓘(ℝ, Z) 𝓘(ℝ, F) ∞ g := contMDiff_const
  have hdim' : Module.finrank ℝ P + Module.finrank ℝ Z < Module.finrank ℝ F := by
    simpa only [Z, finrank_euclideanSpace_fin, add_zero] using hdim
  obtain ⟨a, -, ha⟩ := exists_small_localized_image_avoidance hv.contMDiff hg β.contMDiff
    hdim' (show (0 : ℝ) < 1 by norm_num)
  refine ⟨fun x => v x + β x • a, hv.add (β.contMDiff.contDiff.smul contDiff_const), ?_, ?_⟩
  · filter_upwards [hβ0] with x hx
    rw [hx, zero_smul, add_zero]
  · intro x hx
    by_cases hβx : β x = 0
    · simpa only [hβx, zero_smul, add_zero] using hfixed x hx hβx
    · exact ha x hβx (0 : Z)

open PlaneImmersion (Plane)

omit [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P] in
/-- Extend a locally prescribed nonzero planar field in normal dimension at least three. -/
theorem exists_nonzero_extension_of_local_field {v : Plane → F}
    {U C K : Set Plane} (hU : IsOpen U) (hv : ContDiffOn ℝ ∞ v U)
    (hC : IsClosed C) (hCU : C ⊆ U) (hK : IsCompact K)
    (hne : ∀ x ∈ K ∩ C, v x ≠ 0) (hdim : 3 ≤ Module.finrank ℝ F) :
    ∃ v' : Plane → F, ContDiff ℝ ∞ v' ∧ v' =ᶠ[𝓝ˢ C] v ∧ ∀ x ∈ K, v' x ≠ 0 := by
  obtain ⟨v₀, hv₀, heq⟩ := exists_global_field_with_closed_germ hU hv hC hCU
  have hne₀ : ∀ x ∈ K ∩ C, v₀ x ≠ 0 := by
    intro x hx
    rw [heq.self_of_nhdsSet hx.2]
    exact hne x hx
  have hdim' : Module.finrank ℝ Plane < Module.finrank ℝ F := by
    change Module.finrank ℝ (ℝ × ℝ) < Module.finrank ℝ F
    simp only [Module.finrank_prod, Module.finrank_self]
    omega
  obtain ⟨v', hv', hgerm, hne'⟩ := exists_nonzero_field_rel_closed hv₀ hdim' hK hC hne₀
  exact ⟨v', hv', hgerm.trans heq, hne'⟩

end Wikipedia.SmoothSixDPoincare.FrameField
