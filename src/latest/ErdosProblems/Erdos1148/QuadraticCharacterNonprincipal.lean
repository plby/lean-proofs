import ErdosProblems.Erdos1148.JacobiPrimePattern

/-! # Nonprincipality and Siegel's bound for the radicand character -/

namespace Erdos1148.DukeArithmetic

lemma exists_odd_factorization_of_not_isSquare {a : ℕ} (ha : a ≠ 0)
    (hns : ¬IsSquare a) : ∃ p ∈ a.primeFactors, Odd (a.factorization p) := by
  classical
  by_contra h
  push Not at h
  apply hns
  rw [Nat.prod_primeFactors_pow_factorization ha]
  apply Finset.isSquare_prod
  intro p hp
  obtain ⟨k, hk⟩ := Nat.not_odd_iff_even.mp (h p hp)
  exact ⟨p ^ k, by rw [hk, pow_add]⟩

def jacobiNatLeftHom (n : ℕ) : ℕ →* ℤ where
  toFun a := jacobiSym (a : ℤ) n
  map_one' := by simp only [Nat.cast_one, jacobiSym.one_left]
  map_mul' a b := by simp only [Nat.cast_mul, jacobiSym.mul_left]

theorem exists_jacobi_neg_one_of_not_isSquare {a : ℕ} (ha : a ≠ 0)
    (hns : ¬IsSquare a) : ∃ n : ℕ, Odd n ∧ jacobiSym (a : ℤ) n = -1 := by
  classical
  obtain ⟨p, hp, he⟩ := exists_odd_factorization_of_not_isSquare ha hns
  obtain ⟨n, hn, hpattern⟩ := exists_jacobi_prime_pattern a.primeFactors
    (fun l hl => (Nat.mem_primeFactors.mp hl).1) hp
  refine ⟨n, hn, ?_⟩
  change jacobiNatLeftHom n a = -1
  rw [Nat.prod_primeFactors_pow_factorization ha, map_prod]
  simp only [map_pow]
  have hprod : (∏ l ∈ a.primeFactors, jacobiNatLeftHom n l ^ a.factorization l) =
      jacobiNatLeftHom n p ^ a.factorization p := by
    apply Finset.prod_eq_single p
    · intro l hl hlp
      change jacobiSym (l : ℤ) n ^ a.factorization l = 1
      rw [hpattern l hl, if_neg hlp, one_pow]
    · exact fun h => (h hp).elim
  rw [hprod]
  change jacobiSym (p : ℤ) n ^ a.factorization p = -1
  rw [hpattern p hp, if_pos rfl, he.neg_one_pow]

theorem quadraticDirichletCharacter_ne_one (a : ℕ) [NeZero a] (hns : ¬IsSquare a) :
    quadraticDirichletCharacter a ≠ 1 := by
  obtain ⟨n, hn, hneg⟩ := exists_jacobi_neg_one_of_not_isSquare (NeZero.ne a) hns
  have hval : quadraticDirichletCharacter a n = -1 := by
    rw [quadraticDirichletCharacter_apply_nat, quadraticCharacterValue, if_pos hn, hneg]
    norm_num
  intro h
  rw [h] at hval
  by_cases hu : IsUnit (n : ZMod (4 * a))
  · rw [MulChar.one_apply hu] at hval
    norm_num at hval
  · rw [MulChar.map_nonunit _ hu] at hval
    norm_num at hval

theorem exists_quadraticDirichlet_siegel_lower_bound {ε : ℝ} (hε : 0 < ε) :
    ∃ c : ℝ, 0 < c ∧ ∀ (a : ℕ) [NeZero a], ¬IsSquare a →
      c * (a : ℝ) ^ (-ε) ≤ realDirichletValue (quadraticDirichletCharacter a) 1 := by
  obtain ⟨C, hC, hSiegel⟩ := exists_realDirichlet_siegel_lower_bound hε
  refine ⟨C * (4 : ℝ) ^ (-ε), mul_pos hC (Real.rpow_pos_of_pos (by norm_num) _), ?_⟩
  intro a ha hns
  have h := hSiegel (4 * a) (Nat.mul_pos (by norm_num) (NeZero.pos a))
    (quadraticDirichletCharacter a)
    (quadraticDirichletCharacter_ne_one a hns)
  simpa only [Nat.cast_mul, Nat.cast_ofNat, Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 4)
    (Nat.cast_nonneg a), mul_assoc] using h

end Erdos1148.DukeArithmetic
