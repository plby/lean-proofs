import ErdosProblems.Erdos556.CycleCopyOperations

/-! Two-chord rerouting for arbitrary cyclic labels, and reflection of labels. -/

namespace Erdos556

open SimpleGraph Fin.NatCast

def reverseCycleCopy {V : Type*} {G : SimpleGraph V} {m : ℕ} [NeZero m]
    (f : (cycleGraph m).Copy G) : (cycleGraph m).Copy G where
  toHom :=
    { toFun := fun i => f (-i)
      map_rel' := by
        intro a b h
        apply f.toHom.map_rel
        simpa only [cycleGraph_adj', neg_sub_neg, or_comm] using h }
  injective' := f.injective.comp neg_injective

@[simp] theorem reverseCycleCopy_apply {V : Type*} {G : SimpleGraph V} {m : ℕ} [NeZero m]
    (f : (cycleGraph m).Copy G) (i : Fin m) : reverseCycleCopy f i = f (-i) := rfl

theorem fin_neg_cast_of_add_eq {m : ℕ} [NeZero m] (a b : ℕ) (h : a + b = m) :
    -(a : Fin m) = (b : Fin m) := by
  apply neg_eq_iff_add_eq_zero.mpr
  rw [← Nat.cast_add, h, Fin.natCast_self]

theorem exists_cycle_of_copy_two_chords_skip_one {V : Type*} {G : SimpleGraph V} {m : ℕ}
    [NeZero m] (f : (cycleGraph m).Copy G) (j : ℕ) (hj : 2 ≤ j) (hjm : j + 1 < m)
    (hfirst : G.Adj (f 0) (f (j : Fin m)))
    (hsecond : G.Adj (f 2) (f (↑(j + 1) : Fin m))) :
    ∃ (v : V) (c : G.Walk v v), c.IsCycle ∧ c.length = m - 1 := by
  apply exists_cycle_of_indexed_vertices G (m - 1) (by omega)
    (fun k => f (reverseSkipIndex j k : Fin m))
  · intro a ha b hb hab
    have hi := congrArg Fin.val (f.injective hab)
    simp only [Fin.val_natCast,
      Nat.mod_eq_of_lt (reverseSkipIndex_lt m j a hj hjm ha),
      Nat.mod_eq_of_lt (reverseSkipIndex_lt m j b hj hjm hb)] at hi
    exact reverseSkipIndex_injective j hj hi
  · intro k hk
    by_cases hk0 : k = 0
    · subst k
      simpa [reverseSkipIndex, show 1 < j by omega] using hfirst
    by_cases hkj : k + 1 < j
    · have hstep := (f.toHom.map_rel
        (cycleGraph_adj_add_one (by omega : 2 ≤ m) (↑(j - k) : Fin m))).symm
      have h₁ : reverseSkipIndex j k = j - k + 1 := by unfold reverseSkipIndex; split_ifs <;> omega
      have h₂ : reverseSkipIndex j (k + 1) = j - k := by simp [reverseSkipIndex, hkj]
      simpa only [h₁, h₂, Nat.cast_add, Nat.cast_one, Copy.toHom_apply] using hstep
    by_cases hke : k + 1 = j
    · have h₁ : reverseSkipIndex j k = 2 := by unfold reverseSkipIndex; split_ifs <;> omega
      have h₂ : reverseSkipIndex j (k + 1) = j + 1 := by unfold reverseSkipIndex; split_ifs <;> omega
      simpa only [h₁, h₂, Nat.cast_ofNat] using hsecond
    · have h₁ : reverseSkipIndex j k = k + 1 := by unfold reverseSkipIndex; split_ifs <;> omega
      have h₂ : reverseSkipIndex j (k + 1) = (k + 1) + 1 := by unfold reverseSkipIndex; split_ifs <;> omega
      have hstep := f.toHom.map_rel
        (cycleGraph_adj_add_one (by omega : 2 ≤ m) (↑(k + 1) : Fin m))
      simpa only [h₁, h₂, Nat.cast_add, Nat.cast_one, Copy.toHom_apply] using hstep
  · have hlast : reverseSkipIndex j (m - 1 - 1) = m - 1 := by
      unfold reverseSkipIndex
      split_ifs <;> omega
    have hzero : reverseSkipIndex j 0 = 0 := by simp [reverseSkipIndex]
    rw [hlast, hzero]
    change G.Adj (f.toHom (↑(m - 1) : Fin m)) (f.toHom (0 : Fin m))
    have hwrap : (↑(m - 1) : Fin m) + 1 = 0 := by
      change (↑(m - 1) : Fin m) + (↑(1 : ℕ) : Fin m) = 0
      rw [← Nat.cast_add, Nat.sub_add_cancel (by omega : 1 ≤ m)]
      simp
    simpa only [hwrap] using
      f.toHom.map_rel (cycleGraph_adj_add_one (by omega : 2 ≤ m) (↑(m - 1) : Fin m))

theorem complement_cross_chord_of_cycle_copy {V : Type*} {G : SimpleGraph V} {m : ℕ}
    [NeZero m] (f : (cycleGraph m).Copy G) (j : ℕ) (hj : 2 ≤ j) (hjm : j + 1 < m)
    (hno : ¬ cycleGraph (m - 1) ⊑ G) (hfirst : G.Adj (f 0) (f (j : Fin m))) :
    Gᶜ.Adj (f 2) (f (↑(j + 1) : Fin m)) := by
  rw [compl_adj]
  refine ⟨?_, ?_⟩
  · intro he
    have he' := congrArg Fin.val (f.injective he)
    change 2 % m = (j + 1) % m at he'
    rw [Nat.mod_eq_of_lt (by omega : 2 < m), Nat.mod_eq_of_lt hjm] at he'
    omega
  · intro hsecond
    exact hno ((cycleGraph_isContained_iff (by omega : 2 < m - 1)).mpr
      (exists_cycle_of_copy_two_chords_skip_one f j hj hjm hfirst hsecond))

#print axioms complement_cross_chord_of_cycle_copy

end Erdos556
