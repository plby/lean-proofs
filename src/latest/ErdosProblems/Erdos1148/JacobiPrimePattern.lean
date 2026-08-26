import ErdosProblems.Erdos1148.QuadraticDirichletCharacter
import Mathlib.Data.Nat.ChineseRemainder

/-! # Prescribing a single negative Jacobi factor by Chinese remaindering -/

namespace Erdos1148.DukeArithmetic

lemma exists_jacobi_neg_one_mod_odd_prime {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) :
    ∃ k : ℕ, jacobiSym (k : ℤ) p = -1 := by
  let : Fact p.Prime := ⟨hp⟩
  obtain ⟨x, hx⟩ := quadraticChar_exists_neg_one
    (F := ZMod p) (by simpa only [ZMod.ringChar_zmod_n] using hp2)
  refine ⟨x.val, ?_⟩
  rw [← jacobiSym.legendreSym.to_jacobiSym p]
  simpa only [legendreSym, Int.cast_natCast, ZMod.natCast_zmod_val] using hx

lemma jacobiSym_nat_modEq_left {n k p : ℕ} (h : n ≡ k [MOD p]) :
    jacobiSym (n : ℤ) p = jacobiSym (k : ℤ) p := by
  apply jacobiSym.mod_left'
  simpa only [Int.natCast_mod] using congrArg (Nat.cast : ℕ → ℤ) h

lemma quadraticPatternModulus_coprime {p l : ℕ} (hp : p.Prime) (hl : l.Prime) (hpl : p ≠ l) :
    (if p = 2 then 8 else p).Coprime (if l = 2 then 8 else l) := by
  by_cases hp2 : p = 2
  · subst p
    have hl2 : l ≠ 2 := Ne.symm hpl
    simp only [if_pos rfl, if_neg hl2]
    have h := ((Nat.coprime_primes Nat.prime_two hl).mpr hpl).pow_left 3
    norm_num only [show (2 : ℕ) ^ 3 = 8 by norm_num] at h
    exact h
  · by_cases hl2 : l = 2
    · subst l
      simp only [if_neg hp2, if_pos rfl]
      have h := ((Nat.coprime_primes hp Nat.prime_two).mpr hp2).pow_right 3
      norm_num only [show (2 : ℕ) ^ 3 = 8 by norm_num] at h
      exact h
    · simpa only [if_neg hp2, if_neg hl2] using (Nat.coprime_primes hp hl).mpr hpl

theorem exists_jacobi_prime_pattern (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime)
    {p : ℕ} (hpS : p ∈ S) :
    ∃ n : ℕ, Odd n ∧ ∀ l ∈ S, jacobiSym (l : ℤ) n = if l = p then -1 else 1 := by
  classical
  obtain ⟨k, hk⟩ : ∃ k : ℕ, p ≠ 2 → jacobiSym (k : ℤ) p = -1 := by
    by_cases hp2 : p = 2
    · exact ⟨0, fun h => (h hp2).elim⟩
    · obtain ⟨k, hk⟩ := exists_jacobi_neg_one_mod_odd_prime (hS p hpS) hp2
      exact ⟨k, fun _ => hk⟩
  let T := insert 2 S
  let m := fun l : ℕ => if l = 2 then 8 else l
  let v := fun l : ℕ => if l = 2 then (if p = 2 then 5 else 1) else (if l = p then k else 1)
  have hT : ∀ l ∈ T, l.Prime := by
    intro l hl
    rcases Finset.mem_insert.mp hl with rfl | hl
    · exact Nat.prime_two
    · exact hS l hl
  have hm : ∀ l ∈ T, m l ≠ 0 := by
    intro l hl
    dsimp only [m]
    split_ifs
    · norm_num
    · exact (hT l hl).ne_zero
  have hpair : Set.Pairwise (T : Set ℕ) (fun l t => (m l).Coprime (m t)) := by
    intro l hl t ht hlt
    exact quadraticPatternModulus_coprime (hT l hl) (hT t ht) hlt
  obtain ⟨n, hn⟩ := Nat.chineseRemainderOfFinset v m T hm hpair
  have hn8 : n % 8 = if p = 2 then 5 else 1 := by
    have h := hn 2 (Finset.mem_insert_self 2 S)
    change n % 8 = (if p = 2 then 5 else 1) % 8 at h
    split_ifs at h ⊢ <;> simpa using h
  have hn4 : n % 4 = 1 := by
    rw [← Nat.mod_mod_of_dvd n (by norm_num : 4 ∣ 8), hn8]
    split_ifs <;> norm_num
  have hnOdd : Odd n := Nat.odd_iff.mpr (Nat.odd_of_mod_four_eq_one hn4)
  refine ⟨n, hnOdd, ?_⟩
  intro l hl
  by_cases hl2 : l = 2
  · subst l
    rw [show ((2 : ℕ) : ℤ) = 2 by norm_num, jacobiSym.at_two hnOdd,
      ZMod.χ₈_nat_mod_eight, hn8]
    by_cases hp2 : p = 2
    · subst p
      norm_num [ZMod.χ₈]
    · simp only [if_neg hp2, if_neg (Ne.symm hp2)]
      rfl
  · have hlOdd := (hS l hl).odd_of_ne_two hl2
    rw [jacobiSym.quadratic_reciprocity_one_mod_four' hlOdd hn4]
    have h := hn l (Finset.mem_insert_of_mem hl)
    change n % (if l = 2 then 8 else l) =
      (if l = 2 then (if p = 2 then 5 else 1) else (if l = p then k else 1)) %
        (if l = 2 then 8 else l) at h
    simp only [if_neg hl2] at h
    rw [jacobiSym_nat_modEq_left h]
    by_cases hlp : l = p
    · subst l
      simp only [if_pos rfl]
      exact hk hl2
    · simp only [if_neg hlp, Nat.cast_one, jacobiSym.one_left]

end Erdos1148.DukeArithmetic
