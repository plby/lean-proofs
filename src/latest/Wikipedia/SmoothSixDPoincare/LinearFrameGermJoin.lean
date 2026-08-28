import Wikipedia.SmoothSixDPoincare.OneColumnFrameExtension
import Wikipedia.SmoothSixDPoincare.OpenCurveEndpointGerms

/-!
# Smooth one-dimensional invertible coefficient joins with prescribed germs

In dimension one every endomorphism is its determinant times the identity.
Same-sign endpoint determinants therefore give a straight path inside one
actual open determinant component. Relative smooth joining retains both
whole endpoint germs and stays invertible everywhere.
-/

noncomputable section

open Set Function Filter Topology
open scoped ContDiff

namespace Wikipedia.SmoothSixDPoincare.FrameField

variable {D : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D] [FiniteDimensional ℝ D]

omit [FiniteDimensional ℝ D] in
/-- In rank one, the determinant is the scalar multiplying the identity. -/
theorem eq_det_smul_id_of_finrank_one (hdim : Module.finrank ℝ D = 1) (A : D →L[ℝ] D) :
    A.toLinearMap = A.toLinearMap.det • LinearMap.id := by
  obtain ⟨a, ha, -⟩ := A.toLinearMap.existsUnique_eq_smul_id_of_finrank_eq_one hdim
  have hdet : A.toLinearMap.det = a := by
    rw [ha, LinearMap.det_smul, hdim, pow_one, LinearMap.det_id, mul_one]
  rw [hdet]
  exact ha

omit [FiniteDimensional ℝ D] in
/-- Determinants are linear on the one-dimensional endomorphism space. -/
theorem det_smul_add_of_finrank_one (hdim : Module.finrank ℝ D = 1)
    (A B : D →L[ℝ] D) (a b : ℝ) :
    (a • A + b • B).toLinearMap.det = a * A.toLinearMap.det + b * B.toLinearMap.det := by
  have hlin : (a • A + b • B).toLinearMap =
      (a * A.toLinearMap.det + b * B.toLinearMap.det) • LinearMap.id := by
    calc
      _ = a • (A.toLinearMap.det • LinearMap.id) +
          b • (B.toLinearMap.det • LinearMap.id) :=
        congrArg₂ (fun L K : D →ₗ[ℝ] D => a • L + b • K)
          (eq_det_smul_id_of_finrank_one hdim A) (eq_det_smul_id_of_finrank_one hdim B)
      _ = _ := by rw [smul_smul, smul_smul, ← add_smul]
  rw [hlin, LinearMap.det_smul, hdim, pow_one, LinearMap.det_id, mul_one]

/-- Same-sign determinants give a global smooth invertible join in rank one,
retaining both complete original endpoint germs. -/
theorem exists_smooth_invertible_join_of_finrank_one (hdim : Module.finrank ℝ D = 1)
    {a b : ℝ → (D →L[ℝ] D)} {U V : Set ℝ}
    (ha : ContDiffOn ℝ ∞ a U) (hb : ContDiffOn ℝ ∞ b V)
    (hU : IsOpen U) (hV : IsOpen V) (h0U : (0 : ℝ) ∈ U) (h1V : (1 : ℝ) ∈ V)
    (hsign : 0 < (a 0).toLinearMap.det * (b 1).toLinearMap.det) :
    ∃ L : ℝ → (D →L[ℝ] D), ContDiff ℝ ∞ L ∧
      (∀ t, Bijective (L t)) ∧
      (∀ t, 0 < (a 0).toLinearMap.det * (L t).toLinearMap.det) ∧
      (L =ᶠ[𝓝 (0 : ℝ)] a) ∧ (L =ᶠ[𝓝 (1 : ℝ)] b) := by
  let σ := (a 0).toLinearMap.det
  let S : TopologicalSpace.Opens (D →L[ℝ] D) :=
    ⟨{L | 0 < σ * L.toLinearMap.det},
      isOpen_lt continuous_const (continuous_const.mul ContinuousLinearMap.continuous_det)⟩
  have ha0ne : (a 0).toLinearMap.det ≠ 0 := by
    intro hz
    rw [hz, zero_mul] at hsign
    exact lt_irrefl _ hsign
  have hpos : 0 < σ * (a 0).toLinearMap.det := mul_self_pos.mpr ha0ne
  have ha0 : a 0 ∈ S := hpos
  have hb1 : b 1 ∈ S := hsign
  let γ : Path (⟨a 0, ha0⟩ : S) (⟨b 1, hb1⟩ : S) := {
    toFun := fun t => ⟨(1 - (t : ℝ)) • a 0 + (t : ℝ) • b 1, by
      change 0 < σ * ((1 - (t : ℝ)) • a 0 + (t : ℝ) • b 1).toLinearMap.det
      rw [det_smul_add_of_finrank_one hdim]
      have heq : σ * ((1 - (t : ℝ)) * (a 0).toLinearMap.det +
          (t : ℝ) * (b 1).toLinearMap.det) =
          (1 - (t : ℝ)) * (σ * (a 0).toLinearMap.det) +
            (t : ℝ) * (σ * (b 1).toLinearMap.det) := by ring
      rw [heq]
      by_cases ht : (t : ℝ) = 0
      · simpa only [ht, sub_zero, one_mul, zero_mul, add_zero] using hpos
      · have htpos : 0 < (t : ℝ) := lt_of_le_of_ne t.property.1 (Ne.symm ht)
        exact add_pos_of_nonneg_of_pos
          (mul_nonneg (sub_nonneg.mpr t.property.2) hpos.le) (mul_pos htpos hsign)⟩
    continuous_toFun := by
      apply Continuous.subtype_mk
      fun_prop
    source' := by
      apply Subtype.ext
      simp
    target' := by
      apply Subtype.ext
      simp }
  obtain ⟨L, hL, hmem, hleft, hright⟩ := exists_smooth_open_curve_with_endpoint_germs S
    ha hb hU hV h0U h1V ha0 hb1 γ
  have hpositive (t : ℝ) : 0 < (a 0).toLinearMap.det * (L t).toLinearMap.det := hmem t
  refine ⟨L, hL, ?_, hpositive, hleft, hright⟩
  intro t
  have hdet : (L t).toLinearMap.det ≠ 0 := by
    intro hz
    have hp := hpositive t
    rw [hz, mul_zero] at hp
    exact lt_irrefl _ hp
  have hker : (L t).toLinearMap.ker = ⊥ := by
    by_contra hk
    exact hdet (LinearMap.det_eq_zero_iff_ker_ne_bot.mpr hk)
  have hi : Injective (L t) := LinearMap.ker_eq_bot.mp hker
  exact ⟨hi, (LinearMap.injective_iff_surjective_of_finrank_eq_finrank rfl).mp hi⟩

end Wikipedia.SmoothSixDPoincare.FrameField
