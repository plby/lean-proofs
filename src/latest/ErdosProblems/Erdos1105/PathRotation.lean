import ErdosProblems.Erdos1105.CycleEdges

namespace Erdos1105

open SimpleGraph

/-- Reverse the interior interval `1,...,q`, fixing the other positions. -/
def reverseInterior {n : ℕ} (q : Fin (n + 3)) (i : Fin (n + 3)) : Fin (n + 3) :=
  ⟨if i.val = 0 then 0 else if i.val ≤ q.val then q.val + 1 - i.val else i.val, by
    split_ifs <;> omega⟩

theorem reverseInterior_involutive {n : ℕ} (q : Fin (n + 3)) :
    Function.Involutive (reverseInterior q) := by
  intro i
  apply Fin.ext
  simp only [reverseInterior]
  split_ifs <;> omega

theorem reverseInterior_injective {n : ℕ} (q : Fin (n + 3)) :
    Function.Injective (reverseInterior q) := (reverseInterior_involutive q).injective

/-- Consecutive cyclic adjacencies give a cycle copy. -/
def cycleCopyOfConsecutive {n : ℕ} {V : Type*} (G : SimpleGraph V)
    (v : Fin (n + 3) ↪ V) (hadj : ∀ i, G.Adj (v i) (v (i + 1))) :
    (cycleGraph (n + 3)).Copy G where
  toHom :=
    { toFun := v
      map_rel' := by
        intro i j hij
        rw [cycleGraph_adj] at hij
        rcases hij with hij | hij
        · have hi : i = j + 1 := by simpa [add_comm] using sub_eq_iff_eq_add.mp hij
          rw [hi]
          exact (hadj j).symm
        · have hj : j = i + 1 := by simpa [add_comm] using sub_eq_iff_eq_add.mp hij
          rw [hj]
          exact hadj i }
  injective' := v.injective

/-- The two-chord path rotation: replace the first path edge by a chord
to `q`, reverse the initial interior segment, and rejoin at `q+1`. -/
def rotatedCycleCopy {n : ℕ} (G : SimpleGraph (Fin (n + 3)))
    (q : Fin (n + 3)) (hq : 2 ≤ q.val) (hqend : q.val < n + 2)
    (hfirst : G.Adj 0 q) (hjoin : G.Adj 1 (q + 1))
    (hpath : ∀ i j : Fin (n + 3), 1 ≤ i.val → j.val = i.val + 1 → G.Adj i j)
    (hlast : G.Adj (Fin.last (n + 2)) 0) : (cycleGraph (n + 3)).Copy G :=
  cycleCopyOfConsecutive G ⟨reverseInterior q, reverseInterior_injective q⟩ (by
    intro i
    change G.Adj (reverseInterior q i) (reverseInterior q (i + 1))
    have hival : i.val < n + 3 := i.isLt
    have hqval : (q + 1).val = q.val + 1 := by
      rw [Fin.val_add, Fin.val_one, Nat.mod_eq_of_lt (by omega)]
    by_cases hi0 : i.val = 0
    · have hleft : reverseInterior q i = 0 := by
        apply Fin.ext
        simp [reverseInterior, hi0]
      have hright : reverseInterior q (i + 1) = q := by
        apply Fin.ext
        simp only [reverseInterior, Fin.val_add, Fin.val_one, hi0, zero_add]
        rw [Nat.mod_eq_of_lt (by omega)]
        simp [show 1 ≤ q.val by omega]
      rw [hleft, hright]
      exact hfirst
    · by_cases hilast : i.val = n + 2
      · have hleft : reverseInterior q i = Fin.last (n + 2) := by
          apply Fin.ext
          simp only [reverseInterior, if_neg hi0, if_neg (show ¬i.val ≤ q.val by omega),
            Fin.val_last]
          exact hilast
        have hright : reverseInterior q (i + 1) = 0 := by
          apply Fin.ext
          simp [reverseInterior, Fin.val_add, hilast]
        rw [hleft, hright]
        exact hlast
      · have hisucc : (i + 1).val = i.val + 1 := by
          rw [Fin.val_add, Fin.val_one, Nat.mod_eq_of_lt (by omega)]
        by_cases hiq : i.val < q.val
        · have hleftval : (reverseInterior q i).val = q.val + 1 - i.val := by
            simp only [reverseInterior, if_neg hi0, if_pos (le_of_lt hiq)]
          have hrightval : (reverseInterior q (i + 1)).val = q.val + 1 - (i.val + 1) := by
            simp only [reverseInterior, hisucc,
              if_neg (show i.val + 1 ≠ 0 by omega), if_pos (show i.val + 1 ≤ q.val by omega)]
          apply (hpath (reverseInterior q (i + 1)) (reverseInterior q i) ?_ ?_).symm
          · rw [hrightval]
            clear hqval hisucc hleftval hrightval
            omega
          · rw [hleftval, hrightval]
            clear hqval hisucc hleftval hrightval
            omega
        · by_cases hieq : i.val = q.val
          · have hleft : reverseInterior q i = 1 := by
              apply Fin.ext
              simp only [reverseInterior, if_neg hi0, if_pos (show i.val ≤ q.val by omega),
                Fin.val_one]
              omega
            have hright : reverseInterior q (i + 1) = q + 1 := by
              apply Fin.ext
              simp [reverseInterior, hisucc, hqval, hieq]
            rw [hleft, hright]
            exact hjoin
          · apply hpath
            · simp only [reverseInterior]
              split_ifs <;> omega
            · simp only [reverseInterior, hisucc]
              split_ifs <;> omega)

end Erdos1105
