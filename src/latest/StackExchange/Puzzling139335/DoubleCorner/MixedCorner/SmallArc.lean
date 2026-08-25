import Wikipedia.SchoenfliesTheorem.GeneralCrosscut
import Wikipedia.SchoenfliesTheorem.JordanSeparates

/-!
# Small arcs on a Jordan boundary

Every neighborhood of an arc endpoint contains a nondegenerate initial
subarc. A cut pair then gives such an arc at every point of a Jordan curve,
without any straightness or polygonality assumption.
-/

open Set Metric

namespace Schoenflies

/-- A small initial subarc stays inside a prescribed ball around its first endpoint. -/
theorem IsArcBetween.exists_subarc_subset_ball {A : Set Plane} {v b : Plane}
    (hA : IsArcBetween A v b) {r : ℝ} (hr : 0 < r) :
    ∃ a U, IsArcBetween U v a ∧ U ⊆ A ∩ ball v r := by
  obtain ⟨f, hfc, hfi, hfim, hf0, _⟩ := hA
  obtain ⟨δ, hδ, hclose⟩ :=
    continuousWithinAt_iff.mp (hfc 0 zero_mem_I) r hr
  let t : ℝ := min (δ / 2) (1 / 2)
  have htpos : 0 < t := lt_min (by linarith) (by norm_num)
  have ht1 : t ≤ 1 := (min_le_right _ _).trans (by norm_num)
  have htδ : t < δ := (min_le_left _ _).trans_lt (by linarith)
  refine ⟨f t, f '' Icc 0 t, ?_, ?_⟩
  · have h := isArcBetween_subarc_of_injOn_I hfc hfi zero_mem_I
      ⟨htpos.le, ht1⟩ htpos.ne
    simpa only [uIcc_of_le htpos.le, hf0] using h
  · rintro x ⟨s, hs, rfl⟩
    have hsI : s ∈ unitInterval := ⟨hs.1, hs.2.trans ht1⟩
    refine ⟨hfim ▸ mem_image_of_mem f hsI, ?_⟩
    have hsδ : dist s 0 < δ := by
      rw [Real.dist_eq, sub_zero, abs_of_nonneg hs.1]
      exact hs.2.trans_lt htδ
    exact mem_ball.mpr (by simpa only [hf0] using hclose hsI hsδ)

/-- Every ball around a point of a Jordan curve contains an arc starting
at that point. The arc is nondegenerate by `IsArcBetween`. -/
theorem IsJordanCurve.exists_small_arc {C : Set Plane} (hC : IsJordanCurve C)
    {v : Plane} (hv : v ∈ C) {r : ℝ} (hr : 0 < r) :
    ∃ a A, IsArcBetween A v a ∧ A ⊆ C ∩ ball v r := by
  obtain ⟨x, hx, y, hy, hxy⟩ := hC.exists_ne
  have hex : ∃ q ∈ C, v ≠ q := by
    by_cases hvx : v = x
    · exact ⟨y, hy, hvx ▸ hxy⟩
    · exact ⟨x, hx, hvx⟩
  obtain ⟨q, hq, hvq⟩ := hex
  obtain ⟨D, E, hcut⟩ := exists_isCutPair hC hv hq hvq
  obtain ⟨a, A, hA, hsub⟩ := hcut.fst.exists_subarc_subset_ball hr
  exact ⟨a, A, hA, fun p hp => ⟨hcut.fst_subset (hsub hp).1, (hsub hp).2⟩⟩

end Schoenflies
