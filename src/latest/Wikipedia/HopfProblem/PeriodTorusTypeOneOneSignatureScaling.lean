import Wikipedia.HopfProblem.PeriodTorusTypeOneOneEta

/-!
# Nonzero real scaling of signature `(1,1)`

A negative real scalar exchanges the positive and negative vectors of an
orthogonal basis. A nonzero scalar also preserves both radicals, and hence
nondegeneracy.
-/

noncomputable section

namespace Wikipedia.HopfProblem.PeriodTorusTypeOneOne

theorem HasSignatureOneOne.real_smul
    {H : ComplexPlane₂ →ₗ[ℂ] ComplexPlane₂ →ₗ⋆[ℂ] ℂ}
    (hH : HasSignatureOneOne H) {r : ℝ} (hr : r ≠ 0) :
    HasSignatureOneOne (r • H) := by
  obtain ⟨b, hp, hn, h01, h10⟩ := hH
  rcases lt_or_gt_of_ne hr with hr | hr
  · refine ⟨b.reindex (Equiv.swap 0 1), ?_, ?_, ?_, ?_⟩
    · simpa [Module.Basis.reindex_apply, LinearMap.smul_apply] using
        mul_pos_of_neg_of_neg hr hn
    · simpa [Module.Basis.reindex_apply, LinearMap.smul_apply] using
        mul_neg_of_neg_of_pos hr hp
    · simp [Module.Basis.reindex_apply, LinearMap.smul_apply, h10]
    · simp [Module.Basis.reindex_apply, LinearMap.smul_apply, h01]
  · refine ⟨b, ?_, ?_, ?_, ?_⟩
    · simpa [LinearMap.smul_apply] using mul_pos hr hp
    · simpa [LinearMap.smul_apply] using mul_neg_of_pos_of_neg hr hn
    · simp [LinearMap.smul_apply, h01]
    · simp [LinearMap.smul_apply, h10]

theorem sesquilinear_real_smul_nondegenerate_iff
    (H : ComplexPlane₂ →ₗ[ℂ] ComplexPlane₂ →ₗ⋆[ℂ] ℂ)
    {r : ℝ} (hr : r ≠ 0) : (r • H).Nondegenerate ↔ H.Nondegenerate := by
  simp only [LinearMap.Nondegenerate, LinearMap.SeparatingLeft, LinearMap.SeparatingRight,
    LinearMap.smul_apply, smul_eq_zero_iff_right hr]

theorem sesquilinear_real_smul_nondegenerate
    (H : ComplexPlane₂ →ₗ[ℂ] ComplexPlane₂ →ₗ⋆[ℂ] ℂ)
    (hH : H.Nondegenerate) {r : ℝ} (hr : r ≠ 0) : (r • H).Nondegenerate :=
  (sesquilinear_real_smul_nondegenerate_iff H hr).mpr hH

theorem realForm_real_smul_nondegenerate_iff (E : RealForm)
    {r : ℝ} (hr : r ≠ 0) : (r • E).Nondegenerate ↔ E.Nondegenerate := by
  simp only [LinearMap.Nondegenerate, LinearMap.SeparatingLeft, LinearMap.SeparatingRight,
    LinearMap.smul_apply, smul_eq_zero_iff_right hr]

end Wikipedia.HopfProblem.PeriodTorusTypeOneOne
