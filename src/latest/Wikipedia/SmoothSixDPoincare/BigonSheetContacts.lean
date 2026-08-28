import Wikipedia.SmoothSixDPoincare.TubularBigonArcDifferential

/-!
# Exact contacts of the original bigon with the two full sheets

Interior avoidance and the retained clean strip data determine every contact:
the first sheet meets the disk precisely on its lower edge, and the second
precisely on its upper edge. The other strip meets a sheet only at the corners.
-/

open Set Function
open scoped ContDiff Manifold

namespace Wikipedia.SmoothSixDPoincare.TubularBigon

open WhitneyPairModel

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace M] [ChartedSpace E M]
  {S T : Set M} {a b : ℝ → M} {k₀ k₁ l₀ l₁ : (ℝ × ℝ) → M} {h : ℝ}
  {k : CleanStripPatch (E := E) S T a k₀ k₁}
  {l : CleanStripPatch (E := E) T S b l₀ l₁}
  {n : ℕ} (tube : TubularBigon (E := E) S T a b k.map l.map h n)

theorem lower_center_mem_sheet {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    tube.map (2 * t - 1, 0) ∈ S := by
  rw [tube.lower t ht, ← k.center t ht]
  exact (k.first_sheet (t, 0)
    (k.contains_strip ⟨ht, neg_nonpos.mpr k.width_pos.le, k.width_pos.le⟩)).mpr rfl

theorem upper_center_mem_sheet {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    tube.map (upperBoundaryArc h t) ∈ T := by
  change tube.map (2 * t - 1, h * (1 - (2 * t - 1) ^ 2)) ∈ T
  rw [tube.upper t ht, ← l.center t ht]
  exact (l.first_sheet (t, 0)
    (l.contains_strip ⟨ht, neg_nonpos.mpr l.width_pos.le, l.width_pos.le⟩)).mpr rfl

theorem map_mem_first_iff {p : ℝ × ℝ} (hp : p ∈ bigon h) : tube.map p ∈ S ↔ p.2 = 0 := by
  constructor
  · intro hpS
    have hfront : p ∈ frontier (bigon h) := by
      rw [frontier, (isClosed_bigon h).closure_eq]
      exact ⟨hp, fun hi => tube.interior_avoids p hi (Or.inl hpS)⟩
    obtain ⟨t, ht, rfl | rfl⟩ :=
      (mem_frontier_bigon_iff_exists_time tube.height_pos p).mp hfront
    · rfl
    · have hlt : (t, (0 : ℝ)) ∈ l.domain :=
        l.contains_strip ⟨ht, neg_nonpos.mpr l.width_pos.le, l.width_pos.le⟩
      rw [tube.upper t ht, ← l.center t ht] at hpS
      rcases (l.second_sheet (t, 0) hlt).mp hpS with ht0 | ht1
      · change t = 0 at ht0
        rw [ht0]
        norm_num
      · change t = 1 at ht1
        rw [ht1]
        norm_num
  · intro hpzero
    have hpr := bigon_subset_rectangle tube.height_pos hp
    have ht : arcTime p ∈ Icc (0 : ℝ) 1 := by
      change 0 ≤ (p.1 + 1) / 2 ∧ (p.1 + 1) / 2 ≤ 1
      constructor <;> linarith [hpr.1.1, hpr.1.2]
    have hbase : p.1 = 2 * arcTime p - 1 := by dsimp [arcTime]; ring
    have heq : p = (2 * arcTime p - 1, 0) := Prod.ext hbase hpzero
    rw [heq]
    exact tube.lower_center_mem_sheet ht

theorem map_mem_second_iff {p : ℝ × ℝ} (hp : p ∈ bigon h) :
    tube.map p ∈ T ↔ p.2 = h * (1 - p.1 ^ 2) := by
  constructor
  · intro hpT
    have hfront : p ∈ frontier (bigon h) := by
      rw [frontier, (isClosed_bigon h).closure_eq]
      exact ⟨hp, fun hi => tube.interior_avoids p hi (Or.inr hpT)⟩
    obtain ⟨t, ht, rfl | rfl⟩ :=
      (mem_frontier_bigon_iff_exists_time tube.height_pos p).mp hfront
    · have hkt : (t, (0 : ℝ)) ∈ k.domain :=
        k.contains_strip ⟨ht, neg_nonpos.mpr k.width_pos.le, k.width_pos.le⟩
      rw [tube.lower t ht, ← k.center t ht] at hpT
      rcases (k.second_sheet (t, 0) hkt).mp hpT with ht0 | ht1
      · change t = 0 at ht0
        rw [ht0]
        norm_num
      · change t = 1 at ht1
        rw [ht1]
        norm_num
    · rfl
  · intro hpupper
    have hpr := bigon_subset_rectangle tube.height_pos hp
    have ht : arcTime p ∈ Icc (0 : ℝ) 1 := by
      change 0 ≤ (p.1 + 1) / 2 ∧ (p.1 + 1) / 2 ≤ 1
      constructor <;> linarith [hpr.1.1, hpr.1.2]
    have hbase : p.1 = 2 * arcTime p - 1 := by dsimp [arcTime]; ring
    have heq : p = upperBoundaryArc h (arcTime p) := by
      apply Prod.ext hbase
      change p.2 = h * (1 - (2 * arcTime p - 1) ^ 2)
      rw [← hbase]
      exact hpupper
    rw [heq]
    exact tube.upper_center_mem_sheet ht

end Wikipedia.SmoothSixDPoincare.TubularBigon
