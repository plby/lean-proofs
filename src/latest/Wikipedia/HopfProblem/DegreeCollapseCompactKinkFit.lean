import Wikipedia.HopfProblem.DegreeCollapseScaledPlaneKink

/-!
# One positive scale fits both compact support and the full model trace

Compact norm bounds give a common small scalar for the source support and
the bounded-time target trace. The resulting scale is constructed from the
actual chart neighborhoods; no fitting or support assumption is supplied.
-/

noncomputable section

open Set Function Metric
open scoped ContDiff

namespace Wikipedia.HopfProblem.DegreeCollapse.SupportedCusp

open NoExoticSixSphere.GLOrthonormalization

theorem exists_positive_scalar_fit {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    {K : Set E} {C : Set F} (hK : IsCompact K) (hC : IsCompact C)
    {r s : ℝ} (hr : 0 < r) (hs : 0 < s) :
    ∃ ε : ℝ, 0 < ε ∧ (fun x : E ↦ ε • x) '' K ⊆ ball 0 r ∧
      (fun y : F ↦ ε • y) '' C ⊆ ball 0 s := by
  obtain ⟨R, hR, hKR⟩ := hK.isBounded.exists_pos_norm_le
  obtain ⟨S, hS, hCS⟩ := hC.isBounded.exists_pos_norm_le
  obtain ⟨ε, hε, hsmall⟩ := exists_between (lt_min (div_pos hr hR) (div_pos hs hS))
  have hεR : ε * R < r := (lt_div_iff₀ hR).mp (hsmall.trans_le (min_le_left _ _))
  have hεS : ε * S < s := (lt_div_iff₀ hS).mp (hsmall.trans_le (min_le_right _ _))
  refine ⟨ε, hε, ?_, ?_⟩
  · rintro _ ⟨x, hx, rfl⟩
    change dist (ε • x) 0 < r
    rw [dist_zero_right, norm_smul, Real.norm_eq_abs, abs_of_pos hε]
    exact (mul_le_mul_of_nonneg_left (hKR x hx) hε.le).trans_lt hεR
  · rintro _ ⟨x, hx, rfl⟩
    change dist (ε • x) 0 < s
    rw [dist_zero_right, norm_smul, Real.norm_eq_abs, abs_of_pos hε]
    exact (mul_le_mul_of_nonneg_left (hCS x hx) hε.le).trans_lt hεS

theorem exists_scaled_kink_fit (β : Cutoff) {r : ℝ} (hr : 0 < r)
    {O : Set (Vector 6)} (hO : IsOpen O) (h0O : (0 : Vector 6) ∈ O) :
    ∃ ε : ℝ, 0 < ε ∧ scaledSupport β ε ⊆ ball (0 : Vector 3) r ∧
      ∀ t ∈ Icc (-1 : ℝ) 1, ∀ x ∈ scaledSupport β ε, scaledMap β ε t x ∈ O := by
  obtain ⟨s, hs, hball⟩ := Metric.mem_nhds_iff.mp (hO.mem_nhds h0O)
  obtain ⟨ε, hε, hsrc, htrace⟩ := exists_positive_scalar_fit
    (isCompact_longSupport β) (isCompact_longMap_trace β) hr hs
  refine ⟨ε, hε, hsrc, ?_⟩
  intro t ht x hx
  obtain ⟨y, hy, rfl⟩ := hx
  rw [scaledMap_smul β hε.ne']
  apply hball
  apply htrace
  exact ⟨longMap β t y, ⟨(t, y), ⟨ht, hy⟩, rfl⟩, rfl⟩

end Wikipedia.HopfProblem.DegreeCollapse.SupportedCusp
