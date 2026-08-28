import Wikipedia.SmoothSixDPoincare.WhitneyBigon

/-!
# Exact time parametrizations of the complete bigon frontier

The frontier is the union of the two unit-interval arcs. This includes both
corners and supports transferring native arc injectivity to the full boundary.
-/

open Set Function

namespace Wikipedia.SmoothSixDPoincare.WhitneyPairModel

theorem mem_frontier_bigon_iff_exists_time {h : ℝ} (hh : 0 < h) (p : ℝ × ℝ) :
    p ∈ frontier (bigon h) ↔ ∃ t ∈ Icc (0 : ℝ) 1,
      p = (2 * t - 1, 0) ∨ p = (2 * t - 1, h * (1 - (2 * t - 1) ^ 2)) := by
  constructor
  · intro hp
    obtain ⟨hpK, hpedge⟩ := (mem_frontier_bigon_iff h p).mp hp
    have hpr := bigon_subset_rectangle hh hpK
    let t := (p.1 + 1) / 2
    have ht : t ∈ Icc (0 : ℝ) 1 := by
      dsimp [t]
      constructor <;> linarith [hpr.1.1, hpr.1.2]
    have hbase : p.1 = 2 * t - 1 := by dsimp [t]; ring
    refine ⟨t, ht, ?_⟩
    rcases hpedge with hpzero | hpupper
    · exact Or.inl (Prod.ext hbase hpzero)
    · right
      apply Prod.ext hbase
      rw [← hbase]
      exact hpupper
  · rintro ⟨t, ht, rfl | rfl⟩
    · apply (mem_frontier_bigon_iff h _).mpr
      refine ⟨lowerArc_mem_bigon hh.le ?_, Or.inl rfl⟩
      rw [abs_le]
      constructor <;> linarith [ht.1, ht.2]
    · apply (mem_frontier_bigon_iff h _).mpr
      refine ⟨upperArc_mem_bigon hh.le ?_, Or.inr rfl⟩
      rw [abs_le]
      constructor <;> linarith [ht.1, ht.2]

/-- Embedded edge arcs meeting only at matching endpoints give an injective full boundary map. -/
theorem injOn_frontier_bigon_of_arcs {M : Type*} {h : ℝ} (hh : 0 < h)
    {f : (ℝ × ℝ) → M} {a b : ℝ → M}
    (ha : InjOn a (Icc (0 : ℝ) 1)) (hb : InjOn b (Icc (0 : ℝ) 1))
    (hlower : ∀ t ∈ Icc (0 : ℝ) 1, f (2 * t - 1, 0) = a t)
    (hupper : ∀ t ∈ Icc (0 : ℝ) 1, f (2 * t - 1, h * (1 - (2 * t - 1) ^ 2)) = b t)
    (hcoinc : ∀ t ∈ Icc (0 : ℝ) 1, ∀ s ∈ Icc (0 : ℝ) 1, a t = b s →
      (t = 0 ∧ s = 0) ∨ (t = 1 ∧ s = 1)) : InjOn f (frontier (bigon h)) := by
  have hcross {t s : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) (hs : s ∈ Icc (0 : ℝ) 1)
      (heq : a t = b s) :
      (2 * t - 1, (0 : ℝ)) = (2 * s - 1, h * (1 - (2 * s - 1) ^ 2)) := by
    rcases hcoinc t ht s hs heq with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> norm_num
  intro p hp q hq heq
  obtain ⟨t, ht, hp'⟩ := (mem_frontier_bigon_iff_exists_time hh p).mp hp
  obtain ⟨s, hs, hq'⟩ := (mem_frontier_bigon_iff_exists_time hh q).mp hq
  rcases hp' with rfl | rfl <;> rcases hq' with rfl | rfl
  · rw [hlower t ht, hlower s hs] at heq
    rw [ha ht hs heq]
  · rw [hlower t ht, hupper s hs] at heq
    exact hcross ht hs heq
  · rw [hupper t ht, hlower s hs] at heq
    exact (hcross hs ht heq.symm).symm
  · rw [hupper t ht, hupper s hs] at heq
    rw [hb ht hs heq]

end Wikipedia.SmoothSixDPoincare.WhitneyPairModel
