import ErdosProblems.Erdos556.CycleCopyOperations

/-! Following every second vertex of an odd labelled cycle. -/

namespace Erdos556

open SimpleGraph Fin.NatCast

theorem fin_double_injective_of_odd {m : ℕ} [NeZero m] (hm : Odd m) :
    Function.Injective (fun i : Fin m => i + i) := by
  intro i j hij
  obtain ⟨r, hr⟩ := hm
  have hi := i.isLt
  have hj := j.isLt
  have he := congrArg Fin.val hij
  simp only [Fin.val_add] at he
  have hmod (x : ℕ) (hx : x < m) : (x + x) % m =
      if x + x < m then x + x else x + x - m := by
    split_ifs with h
    · exact Nat.mod_eq_of_lt h
    · rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]
  rw [hmod i.val hi, hmod j.val hj] at he
  apply Fin.ext
  split_ifs at he <;> omega

theorem cycleGraph_adj_iff_add_one {m : ℕ} [NeZero m] (hm : 2 ≤ m) (i j : Fin m) :
    (cycleGraph m).Adj i j ↔ i = j + 1 ∨ j = i + 1 := by
  obtain ⟨k, hkm⟩ : ∃ k, m = k + 2 := ⟨m - 2, by omega⟩
  subst m
  rw [cycleGraph_adj]
  simp only [sub_eq_iff_eq_add, add_comm]

def doubleCycleCopy {V : Type*} {G H : SimpleGraph V} {m : ℕ} [NeZero m]
    (hm : 2 ≤ m) (hodd : Odd m) (f : (cycleGraph m).Copy G)
    (hstep : ∀ i : Fin m, H.Adj (f i) (f (i + 2))) : (cycleGraph m).Copy H where
  toHom :=
    { toFun := fun i => f (i + i)
      map_rel' := by
        intro i j hij
        rcases (cycleGraph_adj_iff_add_one hm i j).mp hij with h | h
        · subst i
          have he : (j + 1) + (j + 1) = (j + j) + 2 := by
            calc
              _ = (j + j) + ((1 : Fin m) + 1) := by abel
              _ = _ := congrArg ((j + j) + ·) (Nat.cast_add 1 1).symm
          rw [he]
          exact (hstep (j + j)).symm
        · subst j
          have he : (i + 1) + (i + 1) = (i + i) + 2 := by
            calc
              _ = (i + i) + ((1 : Fin m) + 1) := by abel
              _ = _ := congrArg ((i + i) + ·) (Nat.cast_add 1 1).symm
          rw [he]
          exact hstep (i + i) }
  injective' := f.injective.comp (fin_double_injective_of_odd hodd)

@[simp] theorem doubleCycleCopy_apply {V : Type*} {G H : SimpleGraph V} {m : ℕ} [NeZero m]
    (hm : 2 ≤ m) (hodd : Odd m) (f : (cycleGraph m).Copy G)
    (hstep : ∀ i : Fin m, H.Adj (f i) (f (i + 2))) (i : Fin m) :
    doubleCycleCopy hm hodd f hstep i = f (i + i) := rfl

theorem four_chords_of_no_predecessor_cycles {V : Type*} {G : SimpleGraph V} {m : ℕ}
    [NeZero m] (hm : 5 ≤ m) (hodd : Odd m) (f : (cycleGraph m).Copy G)
    (hno : ¬ cycleGraph (m - 1) ⊑ G) (hnoc : ¬ cycleGraph (m - 1) ⊑ Gᶜ)
    (i : Fin m) : G.Adj (f i) (f (i + 4)) := by
  have hstep := complement_short_chords_of_cycle_copy (by omega : 4 ≤ m) f hno
  let g := doubleCycleCopy (by omega : 2 ≤ m) hodd f hstep
  have hsurj : Function.Surjective (fun j : Fin m => j + j) :=
    (Finite.injective_iff_surjective).mp (fin_double_injective_of_odd hodd)
  obtain ⟨j, hj⟩ := hsurj i
  change j + j = i at hj
  have h := complement_short_chords_of_cycle_copy (by omega : 4 ≤ m) g hnoc j
  change Gᶜᶜ.Adj (f (j + j)) (f ((j + 2) + (j + 2))) at h
  have he : (j + 2) + (j + 2) = (j + j) + 4 := by
    calc
      _ = (j + j) + ((2 : Fin m) + 2) := by abel
      _ = _ := congrArg ((j + j) + ·) (Nat.cast_add 2 2).symm
  rw [he, hj] at h
  simpa only [compl_compl] using h

#print axioms four_chords_of_no_predecessor_cycles

end Erdos556
