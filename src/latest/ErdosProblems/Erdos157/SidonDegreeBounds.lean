import ErdosProblems.Erdos157.PrefixParameters
import ErdosProblems.Erdos157.ElementaryBounds

/-! The numerical contradiction for the four construction levels. -/

namespace Erdos157.Elementary

theorem levelDegree_le_shift (n m : ℕ) (hn : 3 ≤ n) (hnm : n + 1 ≤ m) :
    (levelDegree n : ℝ) ≤ (7 / 20 : ℝ) * (m : ℝ) ^ 2 := by
  have h := levelDegree_lt_next_window n hn
  have hcast : (n : ℝ) + 1 ≤ m := by exact_mod_cast hnm
  have hsq : ((n : ℝ) + 1) ^ 2 ≤ (m : ℝ) ^ 2 := by gcongr
  linarith

theorem four_level_degree_contradiction (a b c d : ℕ)
    (ha : 400 ≤ a) (hb : 400 ≤ b) (hc : 400 ≤ c) (hd : 400 ≤ d) (hba : b ≤ a)
    (hac : a ≤ c + 1) (hca : c ≤ a + 1) (hbd : b ≤ d + 3) (hdb : d ≤ b + 3)
    (hprod : (min b d) ^ 2 ≤ max (levelDegree a + levelDegree b) (levelDegree c + levelDegree d))
    (hsingle : (min a c - (max b d + 2)) *
      (2 * (max b d + 2) + (min a c - (max b d + 2))) ≤ max (levelDegree a) (levelDegree c)) :
    False := by
  have hA := levelDegree_le_shift a (a + 2) (by omega) (by omega)
  have hB := levelDegree_le_shift b (b + 5) (by omega) (by omega)
  have hC := levelDegree_le_shift c (a + 2) (by omega) (by omega)
  have hD := levelDegree_le_shift d (b + 5) (by omega) (by omega)
  simp only [Nat.cast_add, Nat.cast_ofNat] at hA hB hC hD
  have ha' : (400 : ℝ) ≤ a := by exact_mod_cast ha
  have hb' : (400 : ℝ) ≤ b := by exact_mod_cast hb
  have hmin : (b : ℝ) - 4 ≤ (min b d : ℕ) := by
    have hn : b ≤ min b d + 4 := by omega
    have hr : (b : ℝ) ≤ (min b d : ℕ) + 4 := by exact_mod_cast hn
    linarith
  have hminsq : ((b : ℝ) - 4) ^ 2 ≤ ((min b d : ℕ) : ℝ) ^ 2 := by
    apply pow_le_pow_left₀ (by linarith) hmin
  have hp : ((min b d : ℕ) : ℝ) ^ 2 ≤
      (7 / 20 : ℝ) * (((a : ℝ) + 2) ^ 2 + ((b : ℝ) + 5) ^ 2) := by
    rcases le_max_iff.mp hprod with hp | hp
    · have hr : ((min b d : ℕ) : ℝ) ^ 2 ≤ (levelDegree a : ℝ) + levelDegree b := by exact_mod_cast hp
      linarith
    · have hr : ((min b d : ℕ) : ℝ) ^ 2 ≤ (levelDegree c : ℝ) + levelDegree d := by exact_mod_cast hp
      linarith
  let s : ℕ := max b d + 2
  let t : ℕ := min a c
  let E : ℕ := (t - s) * (2 * s + (t - s))
  have hE : (E : ℝ) ≤ (7 / 20 : ℝ) * ((a : ℝ) + 2) ^ 2 := by
    change E ≤ max (levelDegree a) (levelDegree c) at hsingle
    rcases le_max_iff.mp hsingle with he | he
    · have hr : (E : ℝ) ≤ levelDegree a := by exact_mod_cast he
      exact hr.trans hA
    · have hr : (E : ℝ) ≤ levelDegree c := by exact_mod_cast he
      exact hr.trans hC
  have ht : (a : ℝ) - 1 ≤ (t : ℝ) := by
    have hn : a ≤ t + 1 := by dsimp only [t]; omega
    have hr : (a : ℝ) ≤ (t : ℝ) + 1 := by exact_mod_cast hn
    linarith
  have hs : (s : ℝ) ≤ (b : ℝ) + 7 := by
    have hn : s ≤ b + 7 := by dsimp only [s]; omega
    exact_mod_cast hn
  have ht2 : ((a : ℝ) - 1) ^ 2 ≤ (t : ℝ) ^ 2 := by
    apply pow_le_pow_left₀ (by linarith) ht
  have hs2 : (s : ℝ) ^ 2 ≤ ((b : ℝ) + 7) ^ 2 := by
    apply pow_le_pow_left₀ (by positivity) hs
  have hdiff : ((a : ℝ) - 1) ^ 2 - ((b : ℝ) + 7) ^ 2 ≤ E := by
    by_cases hst : s ≤ t
    · have hnat : E + s ^ 2 = t ^ 2 := by
        dsimp only [E]
        have h := Nat.sub_add_cancel hst
        nlinarith
      have hr : (E : ℝ) + (s : ℝ) ^ 2 = (t : ℝ) ^ 2 := by exact_mod_cast hnat
      linarith
    · have hts : (t : ℝ) ≤ s := by exact_mod_cast (show t ≤ s by omega)
      have hts2 : (t : ℝ) ^ 2 ≤ (s : ℝ) ^ 2 := by gcongr
      have hEpos : (0 : ℝ) ≤ E := Nat.cast_nonneg _
      linarith
  exact scale_contradiction a b ha' (by exact_mod_cast hba) (hminsq.trans hp) (hdiff.trans hE)

end Erdos157.Elementary
