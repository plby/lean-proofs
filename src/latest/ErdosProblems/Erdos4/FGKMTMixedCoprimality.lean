import ErdosProblems.Erdos4.FGKMTProductCoprimality

/-! Shared-prime losses for independent, not necessarily identical, divisor laws. -/

open scoped BigOperators

namespace Erdos4.FGKMT

variable {I : Type*} [Fintype I] [DecidableEq I] {R : ℕ}

theorem independent_divisor_pair_probability (μ : I → FiniteLaw (Fin (R + 1)))
    {d : ℕ} (hdiv : ∀ i, (μ i).prob (fun n => d ∣ (n : ℕ)) ≤ (d.totient : ℝ)⁻¹)
    {i j : I} (hij : i ≠ j) :
    (FiniteLaw.independent μ).prob (fun a => d ∣ (a i : ℕ) ∧ d ∣ (a j : ℕ)) ≤
      ((d.totient : ℝ)⁻¹) ^ 2 := by
  rw [FiniteLaw.independent_prob_pair μ hij
    (fun n : Fin (R + 1) => d ∣ (n : ℕ)) (fun n : Fin (R + 1) => d ∣ (n : ℕ))]
  simpa only [sq] using mul_le_mul (hdiv i) (hdiv j)
    ((μ j).prob_nonneg _) (inv_nonneg.mpr (Nat.cast_nonneg d.totient))

theorem independent_prime_collision (μ : I → FiniteLaw (Fin (R + 1)))
    {p : ℕ} (hp : p.Prime)
    (hdiv : ∀ i, (μ i).prob (fun n => p ∣ (n : ℕ)) ≤ (p.totient : ℝ)⁻¹) :
    (FiniteLaw.independent μ).prob
      (fun a => ∃ i j : I, i ≠ j ∧ p ∣ (a i : ℕ) ∧ p ∣ (a j : ℕ)) ≤
        (Fintype.card I : ℝ) ^ 2 * (((p : ℝ) - 1)⁻¹) ^ 2 := by
  classical
  let ν := FiniteLaw.independent μ
  have hpoint (i j : I) : ν.prob (fun a => i ≠ j ∧ p ∣ (a i : ℕ) ∧ p ∣ (a j : ℕ)) ≤
      (((p : ℝ) - 1)⁻¹) ^ 2 := by
    by_cases hij : i = j
    · subst j
      simp only [ne_eq, not_true_eq_false, false_and, FiniteLaw.prob_false]
      positivity
    · have hh := (ν.prob_mono (fun (a : I → Fin (R + 1))
        (h : i ≠ j ∧ p ∣ (a i : ℕ) ∧ p ∣ (a j : ℕ)) => h.2)).trans
        (independent_divisor_pair_probability μ hdiv hij)
      simpa only [Nat.totient_prime hp, Nat.cast_sub hp.one_le, Nat.cast_one] using hh
  calc
    _ ≤ ∑ i : I, ν.prob (fun a => ∃ j : I, i ≠ j ∧ p ∣ (a i : ℕ) ∧ p ∣ (a j : ℕ)) :=
      ν.prob_exists_le _
    _ ≤ ∑ i : I, ∑ j : I, ν.prob (fun a => i ≠ j ∧ p ∣ (a i : ℕ) ∧ p ∣ (a j : ℕ)) :=
      Finset.sum_le_sum (fun i _ => ν.prob_exists_le _)
    _ ≤ ∑ _i : I, ∑ _j : I, (((p : ℝ) - 1)⁻¹) ^ 2 :=
      Finset.sum_le_sum (fun i _ => Finset.sum_le_sum (fun j _ => hpoint i j))
    _ = _ := by simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]; ring

theorem independent_bad_coprime_imp_collision (μ : I → FiniteLaw (Fin (R + 1)))
    {W K : ℕ}
    (hsupport : ∀ i n, 0 < (μ i).weight n → 0 < (n : ℕ) ∧ (n : ℕ).Coprime W)
    (hpre : ∀ p : ℕ, p.Prime → p ≤ K → p ∣ W)
    (a : I → Fin (R + 1)) (ha : 0 < (FiniteLaw.independent μ).weight a)
    (hbad : ¬Pairwise (fun i j => (a i : ℕ).Coprime (a j : ℕ))) :
    ∃ p ∈ (Nat.primesLE R).filter (fun p => K < p),
      ∃ i j : I, i ≠ j ∧ p ∣ (a i : ℕ) ∧ p ∣ (a j : ℕ) := by
  classical
  by_contra hnone
  apply hbad
  intro i j hij
  by_contra hnc
  obtain ⟨p, hp, hpi, hpj⟩ := Nat.Prime.not_coprime_iff_dvd.mp hnc
  have hs := hsupport i (a i) (FiniteLaw.independent_support μ a ha i)
  have hpR : p ≤ R := (Nat.le_of_dvd hs.1 hpi).trans (Nat.le_of_lt_succ (a i).isLt)
  have hKp : K < p := by
    by_contra hle
    have hpW := hpre p hp (by omega)
    have hpcop := hs.2.of_dvd hpi hpW
    exact hp.ne_one (by simpa using hpcop)
  exact hnone ⟨p, Finset.mem_filter.mpr ⟨Nat.mem_primesLE.mpr ⟨hpR, hp⟩, hKp⟩,
    i, j, hij, hpi, hpj⟩

theorem independent_bad_coprime_probability (μ : I → FiniteLaw (Fin (R + 1)))
    {W K : ℕ} (hK : 2 ≤ K)
    (hsupport : ∀ i n, 0 < (μ i).weight n → 0 < (n : ℕ) ∧ (n : ℕ).Coprime W)
    (hpre : ∀ p : ℕ, p.Prime → p ≤ K → p ∣ W)
    (hdiv : ∀ i p, p.Prime → (μ i).prob (fun n => p ∣ (n : ℕ)) ≤ (p.totient : ℝ)⁻¹) :
    (FiniteLaw.independent μ).prob
      (fun a => ¬Pairwise (fun i j => (a i : ℕ).Coprime (a j : ℕ))) ≤
        (Fintype.card I : ℝ) ^ 2 / ((K - 1 : ℕ) : ℝ) := by
  classical
  let ν := FiniteLaw.independent μ
  let P := (Nat.primesLE R).filter (fun p => K < p)
  have hpoint : ν.prob (fun a => ¬Pairwise (fun i j => (a i : ℕ).Coprime (a j : ℕ))) ≤
      ν.prob (fun a => ∃ p ∈ P, ∃ i j : I, i ≠ j ∧ p ∣ (a i : ℕ) ∧ p ∣ (a j : ℕ)) :=
    ν.prob_mono_support (fun a ha hbad =>
      independent_bad_coprime_imp_collision μ hsupport hpre a ha hbad)
  calc
    _ ≤ ν.prob (fun a => ∃ p ∈ P, ∃ i j : I, i ≠ j ∧ p ∣ (a i : ℕ) ∧ p ∣ (a j : ℕ)) := hpoint
    _ ≤ ∑ p ∈ P, ν.prob (fun a => ∃ i j : I, i ≠ j ∧ p ∣ (a i : ℕ) ∧ p ∣ (a j : ℕ)) :=
      ν.prob_exists_finset_le P _
    _ ≤ ∑ p ∈ P, (Fintype.card I : ℝ) ^ 2 * (((p : ℝ) - 1)⁻¹) ^ 2 := by
      apply Finset.sum_le_sum
      intro p hp
      have hprime := Nat.prime_of_mem_primesLE (Finset.mem_filter.mp hp).1
      exact independent_prime_collision μ hprime (fun i => hdiv i p hprime)
    _ = (Fintype.card I : ℝ) ^ 2 * ∑ p ∈ P, (((p : ℝ) - 1)⁻¹) ^ 2 := by rw [Finset.mul_sum]
    _ ≤ (Fintype.card I : ℝ) ^ 2 * (((K - 1 : ℕ) : ℝ))⁻¹ :=
      mul_le_mul_of_nonneg_left (finite_shifted_reciprocal_square_tail hK P
        (fun p hp => (Finset.mem_filter.mp hp).2)) (sq_nonneg _)
    _ = _ := by rw [div_eq_mul_inv]

end Erdos4.FGKMT
