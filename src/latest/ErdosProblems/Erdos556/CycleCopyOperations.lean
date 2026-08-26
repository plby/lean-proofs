import ErdosProblems.Erdos556.ChordCycles

/-! Rotation and short-chord constraints for a labelled cycle copy. -/

namespace Erdos556

open SimpleGraph Fin.NatCast

theorem cycleGraph_adj_add_one {m : ℕ} [NeZero m] (hm : 2 ≤ m) (i : Fin m) :
    (cycleGraph m).Adj i (i + 1) := by
  rw [cycleGraph_adj']
  right
  rw [add_sub_cancel_left]
  change 1 % m = 1
  exact Nat.mod_eq_of_lt (by omega)

def rotateCycleCopy {V : Type*} {G : SimpleGraph V} {m : ℕ} [NeZero m]
    (f : (cycleGraph m).Copy G) (i : Fin m) : (cycleGraph m).Copy G where
  toHom :=
    { toFun := fun j => f (i + j)
      map_rel' := by
        intro a b h
        apply f.toHom.map_rel
        simpa only [cycleGraph_adj', add_sub_add_left_eq_sub] using h }
  injective' := f.injective.comp (add_right_injective i)

@[simp] theorem rotateCycleCopy_apply {V : Type*} {G : SimpleGraph V} {m : ℕ} [NeZero m]
    (f : (cycleGraph m).Copy G) (i j : Fin m) : rotateCycleCopy f i j = f (i + j) := rfl

def skipOneIndex (k : ℕ) : ℕ := if k = 0 then 0 else k + 1

theorem skipOneIndex_lt (m k : ℕ) (hm : 2 ≤ m) (hk : k < m - 1) : skipOneIndex k < m := by
  unfold skipOneIndex
  split_ifs <;> omega

theorem skipOneIndex_injective : Function.Injective skipOneIndex := by
  intro a b h
  unfold skipOneIndex at h
  split_ifs at h <;> omega

theorem exists_cycle_of_copy_short_chord {V : Type*} {G : SimpleGraph V} {m : ℕ}
    [NeZero m] (hm : 4 ≤ m) (f : (cycleGraph m).Copy G) (h : G.Adj (f 0) (f 2)) :
    ∃ (v : V) (c : G.Walk v v), c.IsCycle ∧ c.length = m - 1 := by
  apply exists_cycle_of_indexed_vertices G (m - 1) (by omega)
    (fun k => f (↑(skipOneIndex k) : Fin m))
  · intro a ha b hb hab
    have hi := congrArg Fin.val (f.injective hab)
    simp only [Fin.val_natCast,
      Nat.mod_eq_of_lt (skipOneIndex_lt m a (by omega) ha),
      Nat.mod_eq_of_lt (skipOneIndex_lt m b (by omega) hb)] at hi
    exact skipOneIndex_injective hi
  · intro k hk
    by_cases hk0 : k = 0
    · subst k
      simpa [skipOneIndex] using h
    · have hs := f.toHom.map_rel (cycleGraph_adj_add_one (by omega : 2 ≤ m) (↑(k + 1) : Fin m))
      simpa [skipOneIndex, hk0, Nat.cast_add] using hs
  · have hlast : skipOneIndex (m - 1 - 1) = m - 1 := by unfold skipOneIndex; split_ifs <;> omega
    have hwrap : (↑(m - 1) : Fin m) + 1 = 0 := by
      change (↑(m - 1) : Fin m) + (↑(1 : ℕ) : Fin m) = 0
      rw [← Nat.cast_add, Nat.sub_add_cancel (by omega : 1 ≤ m)]
      simp
    have hs := f.toHom.map_rel (cycleGraph_adj_add_one (by omega : 2 ≤ m) (↑(m - 1) : Fin m))
    have hzero : skipOneIndex 0 = 0 := by simp [skipOneIndex]
    rw [hlast, hzero]
    change G.Adj (f.toHom (↑(m - 1) : Fin m)) (f.toHom (0 : Fin m))
    simpa only [hwrap] using hs

theorem complement_short_chords_of_cycle_copy {V : Type*} {G : SimpleGraph V} {m : ℕ}
    [NeZero m] (hm : 4 ≤ m) (f : (cycleGraph m).Copy G)
    (hno : ¬ cycleGraph (m - 1) ⊑ G) (i : Fin m) :
    Gᶜ.Adj (f i) (f (i + 2)) := by
  rw [compl_adj]
  refine ⟨?_, ?_⟩
  · intro h
    have hi := f.injective h
    have ht : (2 : Fin m) = 0 := by
      apply add_left_cancel (a := i)
      simpa only [add_zero] using hi.symm
    have ht' : 2 % m = 0 := congrArg Fin.val ht
    rw [Nat.mod_eq_of_lt (by omega : 2 < m)] at ht'
    omega
  · intro h
    have hrot : G.Adj (rotateCycleCopy f i 0) (rotateCycleCopy f i 2) := by
      simpa only [rotateCycleCopy_apply, add_zero] using h
    exact hno ((cycleGraph_isContained_iff (by omega : 2 < m - 1)).mpr
      (exists_cycle_of_copy_short_chord hm (rotateCycleCopy f i) hrot))

#print axioms complement_short_chords_of_cycle_copy

end Erdos556
