import StackExchange.Puzzling139335.N7.FullTypes

/-!
# Ownership at corners in the `2221` multiplicity case

The hypothesis that just one physical square corner has a unique owner
selects the `2221` corner multiplicities.  The other lemmas below concern
actual corner memberships and require no information about corner angles.
-/

namespace Puzzling139335.N7.TwoTwoTwoOne

variable {d : SquareDissection}

/-- In the seven-incidence configuration with one uniquely owned corner,
every physical corner has at most two owners. -/
theorem corner_count_le_two (C : PairConfiguration d)
    (hc : d.HasProtectedCenter)
    (hU : (Finset.univ.filter fun j : Fin 4 => d.cornerTileCount j = 1).card = 1)
    (j : Fin 4) : d.cornerTileCount j ≤ 2 := by
  rcases corner_count_card_patterns d hc C.incidence_count with h | h
  · have hnotThree : d.cornerTileCount j ≠ 3 := by
      intro hj
      have hmem : j ∈ (Finset.univ.filter fun k : Fin 4 => d.cornerTileCount k = 3) := by
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        exact hj
      have hempty := Finset.card_eq_zero.mp h.2.2
      rw [hempty] at hmem
      simp at hmem
    have hmax := d.cornerTileCount_le_three hc j
    omega
  · omega

/-- Two specified distinct owners exhaust a corner whose multiplicity
is at most two. -/
theorem other_owners_excluded_of_count_le_two (d : SquareDissection)
    {i k j : Fin 4} (hik : i ≠ k)
    (hi : corner j ∈ d.piece i) (hk : corner j ∈ d.piece k)
    (hj : d.cornerTileCount j ≤ 2) :
    ∀ l, l ≠ i → l ≠ k → corner j ∉ d.piece l := by
  classical
  intro l hli hlk hl
  have hsub : ({i, k, l} : Finset (Fin 4)) ⊆
      Finset.univ.filter (fun t => corner j ∈ d.piece t) := by
    intro t ht
    simp only [Finset.mem_insert, Finset.mem_singleton] at ht
    rcases ht with rfl | rfl | rfl <;>
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] <;> assumption
  have hcard : ({i, k, l} : Finset (Fin 4)).card = 3 :=
    Finset.card_triple_eq_three_iff.mpr ⟨hik, hli.symm, hlk.symm⟩
  have hle := Finset.card_le_card hsub
  change (Finset.univ.filter fun t => corner j ∈ d.piece t).card ≤ 2 at hj
  omega

/-- Starting with either owner of a multiplicity-two corner yields the
other owner, together with the exclusion of every remaining piece. -/
theorem exists_other_owner_of_count_two (d : SquareDissection)
    {i j : Fin 4} (hi : corner j ∈ d.piece i)
    (hj : d.cornerTileCount j = 2) :
    ∃ k, k ≠ i ∧ corner j ∈ d.piece k ∧
      ∀ l, l ≠ i → l ≠ k → corner j ∉ d.piece l := by
  classical
  have hcard : 1 < (Finset.univ.filter fun k => corner j ∈ d.piece k).card := by
    change 1 < d.cornerTileCount j
    omega
  obtain ⟨k, hk, hki⟩ := Finset.exists_mem_ne hcard i
  have hkpiece : corner j ∈ d.piece k := (Finset.mem_filter.mp hk).2
  exact ⟨k, hki, hkpiece,
    other_owners_excluded_of_count_le_two d hki.symm hi hkpiece hj.le⟩

/-- Among three indices avoiding two distinct members of `Fin 4`, two
indices coincide. -/
theorem three_avoiding_two_repeat :
    ∀ (u v x y z : Fin 4), u ≠ v →
      x ≠ u → x ≠ v → y ≠ u → y ≠ v → z ≠ u → z ≠ v →
      x = y ∨ x = z ∨ y = z := by
  intro u v x y z huv hxu hxv hyu hyv hzu hzv
  by_contra! hdistinct
  have hthree : ({x, y, z} : Finset (Fin 4)).card = 3 :=
    Finset.card_triple_eq_three_iff.mpr hdistinct
  have hsub : ({x, y, z} : Finset (Fin 4)) ⊆ Finset.univ \ {u, v} := by
    intro t ht
    simp only [Finset.mem_insert, Finset.mem_singleton] at ht
    rcases ht with rfl | rfl | rfl <;> simp [hxu, hxv, hyu, hyv, hzu, hzv]
  have htwo : ((Finset.univ : Finset (Fin 4)) \ {u, v}).card = 2 := by
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ _)]
    simp [huv]
  have hle := Finset.card_le_card hsub
  omega

end Puzzling139335.N7.TwoTwoTwoOne
