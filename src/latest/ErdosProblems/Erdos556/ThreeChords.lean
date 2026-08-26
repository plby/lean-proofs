import ErdosProblems.Erdos556.OddCycleDouble

/-! Three-chords in an odd cycle with no monochromatic predecessor cycle. -/

namespace Erdos556

open SimpleGraph Fin.NatCast

def swapThreeSkipFourIndex (k : ℕ) : ℕ := if k = 0 then 0 else if k ≤ 3 then 4 - k else k + 1

theorem swapThreeSkipFourIndex_injective : Function.Injective swapThreeSkipFourIndex := by
  intro a b h
  unfold swapThreeSkipFourIndex at h
  split_ifs at h <;> omega

theorem swapThreeSkipFourIndex_lt (m k : ℕ) (hm : 7 ≤ m) (hk : k < m - 1) :
    swapThreeSkipFourIndex k < m := by
  unfold swapThreeSkipFourIndex
  split_ifs <;> omega

theorem exists_cycle_of_three_and_four_chord {V : Type*} {G : SimpleGraph V} {m : ℕ}
    [NeZero m] (hm : 7 ≤ m) (f : (cycleGraph m).Copy G)
    (h03 : G.Adj (f 0) (f 3)) (h15 : G.Adj (f 1) (f 5)) :
    ∃ (v : V) (c : G.Walk v v), c.IsCycle ∧ c.length = m - 1 := by
  apply exists_cycle_of_indexed_vertices G (m - 1) (by omega)
    (fun k => f (swapThreeSkipFourIndex k : Fin m))
  · intro a ha b hb hab
    have hi := congrArg Fin.val (f.injective hab)
    simp only [Fin.val_natCast,
      Nat.mod_eq_of_lt (swapThreeSkipFourIndex_lt m a hm ha),
      Nat.mod_eq_of_lt (swapThreeSkipFourIndex_lt m b hm hb)] at hi
    exact swapThreeSkipFourIndex_injective hi
  · intro k hk
    by_cases hk0 : k = 0
    · subst k
      simpa [swapThreeSkipFourIndex] using h03
    by_cases hk1 : k = 1
    · subst k
      have h := (f.toHom.map_rel (cycleGraph_adj_add_one (by omega : 2 ≤ m) (2 : Fin m))).symm
      have he : (2 : Fin m) + 1 = 3 := (Nat.cast_add 2 1).symm
      simpa [swapThreeSkipFourIndex, he] using h
    by_cases hk2 : k = 2
    · subst k
      have h := (f.toHom.map_rel (cycleGraph_adj_add_one (by omega : 2 ≤ m) (1 : Fin m))).symm
      have he : (1 : Fin m) + 1 = 2 := (Nat.cast_add 1 1).symm
      simpa [swapThreeSkipFourIndex, he] using h
    by_cases hk3 : k = 3
    · subst k
      simpa [swapThreeSkipFourIndex] using h15
    · have hkgt : 3 < k := by omega
      have h := f.toHom.map_rel (cycleGraph_adj_add_one (by omega : 2 ≤ m) (↑(k + 1) : Fin m))
      simpa [swapThreeSkipFourIndex, hk0, show ¬ k ≤ 3 by omega,
        show ¬ k + 1 ≤ 3 by omega, Nat.cast_add] using h
  · have hlast : swapThreeSkipFourIndex (m - 1 - 1) = m - 1 := by
      unfold swapThreeSkipFourIndex
      split_ifs <;> omega
    have hzero : swapThreeSkipFourIndex 0 = 0 := by simp [swapThreeSkipFourIndex]
    rw [hlast, hzero]
    change G.Adj (f.toHom (↑(m - 1) : Fin m)) (f.toHom (0 : Fin m))
    have hwrap : (↑(m - 1) : Fin m) + 1 = 0 := by
      change (↑(m - 1) : Fin m) + (↑(1 : ℕ) : Fin m) = 0
      rw [← Nat.cast_add, Nat.sub_add_cancel (by omega : 1 ≤ m)]
      simp
    simpa only [hwrap] using
      f.toHom.map_rel (cycleGraph_adj_add_one (by omega : 2 ≤ m) (↑(m - 1) : Fin m))

theorem three_chords_of_no_predecessor_cycles {V : Type*} {G : SimpleGraph V} {m : ℕ}
    [NeZero m] (hm : 7 ≤ m) (hodd : Odd m) (f : (cycleGraph m).Copy G)
    (hno : ¬ cycleGraph (m - 1) ⊑ G) (hnoc : ¬ cycleGraph (m - 1) ⊑ Gᶜ)
    (i : Fin m) : Gᶜ.Adj (f i) (f (i + 3)) := by
  rw [compl_adj]
  refine ⟨?_, ?_⟩
  · intro h
    have hi := f.injective h
    have ht : (3 : Fin m) = 0 := by
      apply add_left_cancel (a := i)
      simpa only [add_zero] using hi.symm
    have ht' : 3 % m = 0 := congrArg Fin.val ht
    rw [Nat.mod_eq_of_lt (by omega : 3 < m)] at ht'
    omega
  · intro h
    let g := rotateCycleCopy f i
    have h03 : G.Adj (g 0) (g 3) := by
      simpa only [g, rotateCycleCopy_apply, add_zero] using h
    have h15 := four_chords_of_no_predecessor_cycles (by omega : 5 ≤ m) hodd g hno hnoc 1
    have he : (1 : Fin m) + 4 = 5 := (Nat.cast_add 1 4).symm
    rw [he] at h15
    exact hno ((cycleGraph_isContained_iff (by omega : 2 < m - 1)).mpr
      (exists_cycle_of_three_and_four_chord hm g h03 h15))

#print axioms three_chords_of_no_predecessor_cycles

end Erdos556
