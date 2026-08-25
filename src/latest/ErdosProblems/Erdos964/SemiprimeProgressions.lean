import ErdosProblems.Erdos964.Basic

/-!
# Unconditional semiprimes in an arithmetic progression

Dirichlet's theorem suffices for a single primitive linear form. This also
settles the repeated-coefficient case of `GoldstonGrahamPintzYildirimStatement`.
The remaining case concerns three distinct linear forms simultaneously.
-/

namespace Erdos964

/-- Every primitive arithmetic progression with positive step contains
arbitrarily large products of two distinct primes exceeding `C`. -/
theorem exists_semiprime_linear_gt (a b C N : ℕ) (ha : 0 < a)
    (hab : b.Coprime a) :
    ∃ x > N, a * x + b ∈ E2 C := by
  obtain ⟨p, hpC, hp, hpmod⟩ := Nat.forall_exists_prime_gt_and_modEq C
    (ne_of_gt ha) (Nat.coprime_one_left a)
  obtain ⟨q, hqbound, hq, hqmod⟩ := Nat.forall_exists_prime_gt_and_modEq
    (max p (a * N + b)) (ne_of_gt ha) hab
  have hpq : p < q := lt_of_le_of_lt (le_max_left _ _) hqbound
  have hlarge : a * N + b < p * q := by
    have hqN := lt_of_le_of_lt (le_max_right _ _) hqbound
    nlinarith [hp.two_le]
  have hmod : p * q ≡ b [MOD a] := by
    simpa only [one_mul] using hpmod.mul hqmod
  have hdiv : a ∣ p * q - b := (Nat.modEq_iff_dvd' (by omega)).mp hmod.symm
  let x := (p * q - b) / a
  have heq : a * x + b = p * q := by
    dsimp [x]
    rw [Nat.mul_div_cancel' hdiv, Nat.sub_add_cancel (by omega)]
  refine ⟨x, ?_, p, q, hp, hq, ne_of_lt hpq, hpC, lt_trans hpC hpq, heq⟩
  nlinarith

theorem infinite_semiprime_linear (a b C : ℕ) (ha : 0 < a)
    (hab : b.Coprime a) : {x : ℕ | a * x + b ∈ E2 C}.Infinite := by
  apply Set.infinite_iff_exists_gt.mpr
  intro N
  obtain ⟨x, hx, hE⟩ := exists_semiprime_linear_gt a b C N ha hab
  exact ⟨x, hE, hx⟩

/-- Equal coefficients force the corresponding prescribed divisors to be one. -/
theorem prescribed_divisors_eq_one_of_eq (a r : Fin 3 → ℕ)
    (hdiff : ∀ i j, i ≠ j → (r i).Coprime
      (if a i > a j then a i - a j else a j - a i))
    {i j : Fin 3} (hij : i ≠ j) (heq : a i = a j) :
    r i = 1 ∧ r j = 1 := by
  have hi := hdiff i j hij
  have hj := hdiff j i hij.symm
  simpa only [heq, gt_iff_lt, lt_self_iff_false, ↓reduceIte, Nat.sub_self,
    Nat.coprime_zero_right] using And.intro hi hj

/-- The GPY conclusion is unconditional when two leading coefficients agree. -/
theorem gpy_of_repeated_coefficient (a r : Fin 3 → ℕ)
    (ha : ∀ i, 0 < a i)
    (hdiff : ∀ i j, i ≠ j → (r i).Coprime
      (if a i > a j then a i - a j else a j - a i))
    (hrepeat : ¬Function.Injective a) (C : ℕ) :
    ∃ i j, i < j ∧ {x : ℕ | r i ∣ L (a i) x ∧ r j ∣ L (a j) x ∧
      L (a i) x / r i ∈ E2 C ∧ L (a j) x / r j ∈ E2 C}.Infinite := by
  obtain ⟨i, j, heq, hij⟩ := Function.not_injective_iff.mp hrepeat
  have hordered : ∃ i j, i < j ∧ a i = a j := by
    rcases lt_or_gt_of_ne hij with hlt | hgt
    · exact ⟨i, j, hlt, heq⟩
    · exact ⟨j, i, hgt, heq.symm⟩
  obtain ⟨i, j, hij, heq⟩ := hordered
  obtain ⟨hri, hrj⟩ := prescribed_divisors_eq_one_of_eq a r hdiff (ne_of_lt hij) heq
  refine ⟨i, j, hij, ?_⟩
  simpa only [hri, hrj, one_dvd, Nat.div_one, heq, true_and, and_self, L] using
    infinite_semiprime_linear (a j) 1 C (ha j) (Nat.coprime_one_left _)

end Erdos964
