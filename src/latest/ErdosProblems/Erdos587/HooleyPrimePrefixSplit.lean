import ErdosProblems.Erdos587.HooleyGrowth

/-!
# Splitting at the first prime factor that crosses a size threshold

Repeated primes are kept as separate entries. This is legitimate here
because the Delta growth inequality does not require coprime factors,
and avoids a separate exceptional case for large prime powers.
-/

namespace Erdos587

lemma delta_list_prod_threshold_split (L : List ℕ) {a D : ℕ} (ha : a ≤ D)
    (hlarge : D < a * L.prod) :
    ∃ L₁ : List ℕ, ∃ p : ℕ, ∃ L₂ : List ℕ,
      L = L₁ ++ p :: L₂ ∧ a * L₁.prod ≤ D ∧ D < a * L₁.prod * p := by
  induction L generalizing a with
  | nil => simp only [List.prod_nil, mul_one] at hlarge; omega
  | cons p L ih =>
    by_cases hp : D < a * p
    · exact ⟨[], p, L, rfl, by simpa using ha, by simpa using hp⟩
    · have hnext : D < (a * p) * L.prod := by
        simpa only [List.prod_cons, mul_assoc] using hlarge
      obtain ⟨L₁, q, L₂, hL, hsmall, hcross⟩ := ih (le_of_not_gt hp) hnext
      refine ⟨p :: L₁, q, L₂, by simp only [List.cons_append, hL], ?_, ?_⟩
      · simpa only [List.prod_cons, mul_assoc] using hsmall
      · simpa only [List.prod_cons, mul_assoc] using hcross

theorem exists_delta_prime_prefix_split {n D : ℕ} (hD : 1 ≤ D) (hnD : D < n) :
    ∃ a b p : ℕ, n = a * b ∧ 0 < a ∧ 0 < b ∧ p.Prime ∧
      a ≤ D ∧ D < a * p ∧
      (∀ q ∈ a.primeFactors, q ≤ p) ∧ (∀ q ∈ b.primeFactors, p ≤ q) := by
  have hn : n ≠ 0 := by omega
  have hprod : D < 1 * n.primeFactorsList.prod := by
    rwa [one_mul, Nat.prod_primeFactorsList hn]
  obtain ⟨L₁, p, L₂, hL, haD, hcross⟩ :=
    delta_list_prod_threshold_split n.primeFactorsList hD hprod
  simp only [one_mul] at haD hcross
  let a : ℕ := L₁.prod
  let b : ℕ := (p :: L₂).prod
  have hmul : n = a * b := by
    rw [← Nat.prod_primeFactorsList hn, hL, List.prod_append]
  have ha : a ≠ 0 := by intro h; rw [h, zero_mul] at hmul; exact hn hmul
  have hb : b ≠ 0 := by intro h; rw [h, mul_zero] at hmul; exact hn hmul
  have hprime₁ : ∀ q ∈ L₁, q.Prime := by
    intro q hq
    apply Nat.prime_of_mem_primeFactorsList
    rw [hL]
    exact List.mem_append.mpr (Or.inl hq)
  have hprime₂ : ∀ q ∈ p :: L₂, q.Prime := by
    intro q hq
    apply Nat.prime_of_mem_primeFactorsList
    rw [hL]
    exact List.mem_append.mpr (Or.inr hq)
  have hsort := (Nat.primeFactorsList_sorted n).pairwise
  rw [hL, List.pairwise_append] at hsort
  refine ⟨a, b, p, hmul, Nat.pos_of_ne_zero ha, Nat.pos_of_ne_zero hb,
    hprime₂ p (List.mem_cons_self ..), haD, hcross, ?_, ?_⟩
  · intro q hq
    have hqlist : q ∈ a.primeFactorsList :=
      Nat.mem_primeFactorsList'.mpr (Nat.mem_primeFactors.mp hq)
    have hqin : q ∈ L₁ := (Nat.primeFactorsList_unique (n := a) rfl hprime₁).mem_iff.mpr hqlist
    exact hsort.2.2 q hqin p (List.mem_cons_self ..)
  · intro q hq
    have hqlist : q ∈ b.primeFactorsList :=
      Nat.mem_primeFactorsList'.mpr (Nat.mem_primeFactors.mp hq)
    have hqin : q ∈ p :: L₂ :=
      (Nat.primeFactorsList_unique (n := b) rfl hprime₂).mem_iff.mpr hqlist
    rcases List.mem_cons.mp hqin with heq | hqtail
    · exact heq ▸ le_rfl
    · exact (List.pairwise_cons.mp hsort.2.1).1 q hqtail

/-- Every positive integer has either a bounded smooth part and a rough
cofactor, or a larger smooth prefix whose next prime is below the cutoff.
The second alternative is exactly the one to which the Rankin tail applies. -/
theorem delta_prime_prefix_dichotomy {n R : ℕ} (hn : 0 < n) (hR : 1 ≤ R) :
    (∃ a b : ℕ, n = a * b ∧ 0 < a ∧ 0 < b ∧ a ≤ R ^ 2 ∧
      (∀ q ∈ b.primeFactors, R < q)) ∨
    (∃ a b p : ℕ, n = a * b ∧ 0 < a ∧ 0 < b ∧ p.Prime ∧
      R < a ∧ a ≤ R ^ 2 ∧ p ≤ R ∧
      (∀ q ∈ a.primeFactors, q ≤ p) ∧ (∀ q ∈ b.primeFactors, p ≤ q)) := by
  by_cases hsmall : n ≤ R ^ 2
  · exact Or.inl ⟨n, 1, by simp, hn, by omega, hsmall, by simp⟩
  · obtain ⟨a, b, p, hmul, ha, hb, hp, haR, hcross, hsmooth, hrough⟩ :=
      exists_delta_prime_prefix_split (Nat.one_le_pow 2 R hR) (lt_of_not_ge hsmall)
    by_cases hpR : R < p
    · exact Or.inl ⟨a, b, hmul, ha, hb, haR, fun q hq => hpR.trans_le (hrough q hq)⟩
    · apply Or.inr
      refine ⟨a, b, p, hmul, ha, hb, hp, ?_, haR, le_of_not_gt hpR, hsmooth, hrough⟩
      by_contra haSmall
      have hprod := Nat.mul_le_mul (le_of_not_gt haSmall) (le_of_not_gt hpR)
      nlinarith

end Erdos587
