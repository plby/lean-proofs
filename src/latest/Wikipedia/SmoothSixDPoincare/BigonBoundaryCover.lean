import Wikipedia.SmoothSixDPoincare.WhitneyBigon

/-!
# A two-patch open cover of the whole cornered bigon boundary

The lower and upper patches overlap only in a prescribed neighborhood of the
two endpoints. Each patch still contains its entire boundary arc, including
both endpoints, and lies in the supplied coordinate domain for that arc.
-/

open Set Function

namespace Wikipedia.SmoothSixDPoincare.WhitneyPairModel

/-- Shrink edge neighborhoods so that their overlap is confined to the two corner patches. -/
theorem exists_bigon_boundary_cover {h : ℝ} (hh : 0 < h)
    {D E O : Set (ℝ × ℝ)} (hD : IsOpen D) (hE : IsOpen E) (hO : IsOpen O)
    (hleft : (-1, 0) ∈ O) (hright : (1, 0) ∈ O)
    (hlower : MapsTo (fun t : ℝ => (2 * t - 1, 0)) (Icc 0 1) D)
    (hupper : MapsTo (fun t : ℝ => (2 * t - 1, h * (1 - (2 * t - 1) ^ 2))) (Icc 0 1) E) :
    ∃ U : Set (ℝ × ℝ), ∃ V : Set (ℝ × ℝ), IsOpen U ∧ IsOpen V ∧
      U ⊆ D ∧ V ⊆ E ∧ U ∩ V ⊆ O ∧
      MapsTo (fun t : ℝ => (2 * t - 1, 0)) (Icc 0 1) U ∧
      MapsTo (fun t : ℝ => (2 * t - 1, h * (1 - (2 * t - 1) ^ 2))) (Icc 0 1) V ∧
      frontier (bigon h) ⊆ U ∪ V := by
  let B : Set (ℝ × ℝ) := {p | p.2 < h * (1 - p.1 ^ 2) / 2}
  let T : Set (ℝ × ℝ) := {p | h * (1 - p.1 ^ 2) / 2 < p.2}
  have hB : IsOpen B := isOpen_lt continuous_snd (by fun_prop)
  have hT : IsOpen T := isOpen_lt (by fun_prop) continuous_snd
  let U := D ∩ (O ∪ B)
  let V := E ∩ (O ∪ T)
  have hU : IsOpen U := hD.inter (hO.union hB)
  have hV : IsOpen V := hE.inter (hO.union hT)
  have hheight {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) :
      0 < h * (1 - (2 * t - 1) ^ 2) := by
    calc
      0 < 4 * h * t * (1 - t) :=
        mul_pos (mul_pos (mul_pos (by norm_num) hh) ht.1) (sub_pos.mpr ht.2)
      _ = h * (1 - (2 * t - 1) ^ 2) := by ring
  have hlowU : MapsTo (fun t : ℝ => (2 * t - 1, 0)) (Icc 0 1) U := by
    intro t ht
    refine ⟨hlower ht, ?_⟩
    by_cases ht0 : t = 0
    · subst t
      exact Or.inl (by simpa using hleft)
    by_cases ht1 : t = 1
    · subst t
      exact Or.inl (by convert hright using 1; norm_num)
    right
    have hh' := hheight ⟨lt_of_le_of_ne ht.1 (Ne.symm ht0), lt_of_le_of_ne ht.2 ht1⟩
    change (0 : ℝ) < h * (1 - (2 * t - 1) ^ 2) / 2
    linarith
  have huppV : MapsTo (fun t : ℝ => (2 * t - 1, h * (1 - (2 * t - 1) ^ 2)))
      (Icc 0 1) V := by
    intro t ht
    refine ⟨hupper ht, ?_⟩
    by_cases ht0 : t = 0
    · subst t
      exact Or.inl (by simpa using hleft)
    by_cases ht1 : t = 1
    · subst t
      exact Or.inl (by convert hright using 1; norm_num)
    right
    have hh' := hheight ⟨lt_of_le_of_ne ht.1 (Ne.symm ht0), lt_of_le_of_ne ht.2 ht1⟩
    change h * (1 - (2 * t - 1) ^ 2) / 2 < h * (1 - (2 * t - 1) ^ 2)
    linarith
  refine ⟨U, V, hU, hV, inter_subset_left, inter_subset_left, ?_, hlowU, huppV, ?_⟩
  · intro p hp
    rcases hp.1.2 with hpO | hpB
    · exact hpO
    rcases hp.2.2 with hpO | hpT
    · exact hpO
    have hpB' : p.2 < h * (1 - p.1 ^ 2) / 2 := hpB
    have hpT' : h * (1 - p.1 ^ 2) / 2 < p.2 := hpT
    exact (lt_asymm hpB' hpT').elim
  · intro p hp
    obtain ⟨hpK, hpedge⟩ := (mem_frontier_bigon_iff h p).mp hp
    have hpr := bigon_subset_rectangle hh hpK
    let t := (p.1 + 1) / 2
    have ht : t ∈ Icc (0 : ℝ) 1 := by
      dsimp [t]
      constructor <;> linarith [hpr.1.1, hpr.1.2]
    have hbase : p.1 = 2 * t - 1 := by dsimp [t]; ring
    rcases hpedge with hpzero | hpupper
    · left
      have heq : p = (2 * t - 1, 0) := Prod.ext hbase hpzero
      rw [heq]
      exact hlowU ht
    · right
      have heq : p = (2 * t - 1, h * (1 - (2 * t - 1) ^ 2)) := by
        apply Prod.ext hbase
        rw [← hbase]
        exact hpupper
      rw [heq]
      exact huppV ht

end Wikipedia.SmoothSixDPoincare.WhitneyPairModel
