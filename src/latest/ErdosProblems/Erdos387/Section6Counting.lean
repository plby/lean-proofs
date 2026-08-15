/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos387.Section6Bridge

/-!
# Exact finite counting interface for BNPZ Section 6

The analytic part of Sections 6--10 compares a sifted set `S` with its subset
`E` of integers whose binomial coefficient has a divisor in `(n / B, n]`.
This file gives those sets literal finite-set definitions and proves that the
strict cardinality inequality `E.card < S.card` supplies the exact
counterexample needed by Erdős Problem 387.
-/

namespace Erdos387

/-- An integer has no prime divisor strictly below `z`. -/
def IsZRough (z m : ℕ) : Prop :=
  ∀ p : ℕ, p.Prime → p < z → ¬p ∣ m

/-- Natural-number form of the assertion that `n.choose k` has a divisor in
the real interval `(n / B, n]`. -/
def HasFixedBNearDivisor (B n k : ℕ) : Prop :=
  ∃ d : ℕ, n < B * d ∧ d ≤ n ∧ d ∣ n.choose k

/-- The literal finite set denoted by `S` in BNPZ (6.3), on the public
covering progression. -/
noncomputable def SiftedCandidates {B K : ℕ}
    (S : CoverBPZ.BPZSection6Input B K) (X z : ℕ) : Finset ℕ :=
  by
    classical
    exact (Finset.Ioc (X / 2) X).filter fun n =>
      S.k < n ∧ (CoverBPZ.Nk_formula S.k : ℤ) ∣ (n : ℤ) - S.α ∧
        IsZRough z (n.choose S.k)

/-- The literal bad subset denoted by `E` in BNPZ (6.5). -/
noncomputable def BadCandidates {B K : ℕ}
    (S : CoverBPZ.BPZSection6Input B K) (X z : ℕ) : Finset ℕ :=
  by
    classical
    exact (SiftedCandidates S X z).filter fun n =>
      HasFixedBNearDivisor B n S.k

/-- For positive `B`, the real endpoint used in the formal-conjectures
statement is exactly the cross-multiplied natural inequality `n < B * d`. -/
theorem mem_Ioc_natCast_div_iff {B n d : ℕ} (hB : 0 < B) :
    (d : ℝ) ∈ Set.Ioc ((n : ℝ) / B) n ↔ n < B * d ∧ d ≤ n := by
  have hBreal : (0 : ℝ) < B := by exact_mod_cast hB
  constructor
  · rintro ⟨hlo, hhi⟩
    constructor
    · have hmul : (n : ℝ) < (d : ℝ) * B :=
        (div_lt_iff₀ hBreal).mp hlo
      have hmul' : (n : ℝ) < ((B * d : ℕ) : ℝ) := by
        simpa [mul_comm] using hmul
      exact_mod_cast hmul'
    · exact_mod_cast hhi
  · rintro ⟨hlo, hhi⟩
    constructor
    · apply (div_lt_iff₀ hBreal).mpr
      have hlo' : (n : ℝ) < ((B * d : ℕ) : ℝ) := by exact_mod_cast hlo
      simpa [mul_comm] using hlo'
    · exact_mod_cast hhi

/-- If a finite product is larger than a common upper bound for every one of
its factors, at least two factors are nontrivial. -/
theorem exists_two_ne_one_of_prod_gt_bound
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (f : ι → ℕ) {N : ℕ} (hN : 1 ≤ N) (hle : ∀ i, f i ≤ N)
    (hlt : N < ∏ i, f i) :
    ∃ i j : ι, i ≠ j ∧ f i ≠ 1 ∧ f j ≠ 1 := by
  have hprodNe : (∏ i, f i) ≠ 1 := by omega
  obtain ⟨i, _, hfi⟩ :=
    Finset.exists_ne_one_of_prod_ne_one (s := Finset.univ) hprodNe
  by_contra hpairs
  have hall : ∀ j ∈ (Finset.univ : Finset ι), j ≠ i → f j = 1 := by
    intro j _ hji
    by_contra hfj
    exact hpairs ⟨i, j, hji.symm, hfi, hfj⟩
  have hprodEq : (∏ j, f j) = f i := by
    exact Finset.prod_eq_single i hall (by simp)
  rw [hprodEq] at hlt
  exact (Nat.not_lt_of_ge (hle i)) hlt

/-- In a `z`-rough binomial coefficient, every non-unit residual-divisor
component is at least `z`. -/
theorem CoverDivisorTuple.factor_ge_of_ne_one_of_rough
    {n k z : ℕ} {D : CoverFactorization n k}
    (hkn : k ≤ n) (hrough : IsZRough z (n.choose k))
    (E : CoverDivisorTuple D) (i : Fin k) (hne : E.factor i ≠ 1) :
    z ≤ E.factor i := by
  have hfactorDvd : E.factor i ∣ n.choose k :=
    (E.divides i).trans (coverQuotient_dvd_choose D i.isLt)
  have hchoosePos : 0 < n.choose k := Nat.choose_pos hkn
  have hfactorPos : 0 < E.factor i :=
    Nat.pos_of_dvd_of_pos hfactorDvd hchoosePos
  obtain ⟨p, hp, hpFactor⟩ := Nat.exists_prime_and_dvd hne
  have hzp : z ≤ p := by
    by_contra hpz
    exact hrough p hp (Nat.lt_of_not_ge hpz) (hpFactor.trans hfactorDvd)
  exact hzp.trans (Nat.le_of_dvd hfactorPos hpFactor)

/-- A bad divisor supplies the exact tuple data used by the five BNPZ error
classes: component divisibility, pairwise coprimality, and at least two
nontrivial components. -/
theorem nearDivisor_has_residualTuple
    {B K n : ℕ} (S : CoverBPZ.BPZSection6Input B K) (hB : 0 < B)
    (hn : S.k < n)
    (hprog : (CoverBPZ.Nk_formula S.k : ℤ) ∣ (n : ℤ) - S.α)
    (hnear : HasFixedBNearDivisor B n S.k) :
    let D := S.toCoverFactorization hn hprog
    ∃ d : ℕ, ∃ E : CoverDivisorTuple D,
      n < B * d ∧ d ≤ n ∧ E.value = d ∧
      (∀ i : Fin S.k, E.factor i ∣ n - i) ∧
      (∀ i j : Fin S.k, i ≠ j → Nat.Coprime (E.factor i) (E.factor j)) ∧
      ∃ i j : Fin S.k, i ≠ j ∧ E.factor i ≠ 1 ∧ E.factor j ≠ 1 := by
  dsimp
  let D := S.toCoverFactorization hn hprog
  obtain ⟨d, hnd, hdn, hdvd⟩ := hnear
  obtain ⟨E, hvalue⟩ := CoverDivisorTuple.exists_value_eq (D := D) hdvd
  have hcomponentDvd : ∀ i : Fin S.k, E.factor i ∣ n - i := by
    intro i
    exact (E.divides i).trans (coverQuotient_dvd_term D i.isLt)
  have hcomponentPairwise :
      ∀ i j : Fin S.k, i ≠ j → Nat.Coprime (E.factor i) (E.factor j) := by
    intro i j hij
    exact Nat.Coprime.of_dvd_right (E.divides j)
      (Nat.Coprime.of_dvd_left (E.divides i)
        (S.coverQuotients_pairwise_coprime hn hprog i i.isLt j j.isLt
          (fun hval => hij (Fin.ext hval))))
  have hN : 1 ≤ n / B := by
    have hkPos : 0 < S.k := by
      have := S.hk3
      omega
    let i0 : Fin S.k := ⟨0, hkPos⟩
    have htermPos : 0 < n - (i0 : ℕ) := by omega
    have hgLe : D.g i0 ≤ n - (i0 : ℕ) :=
      Nat.le_of_dvd htermPos (D.divides_term i0 i0.isLt)
    have hBLe : B ≤ n := by
      calc
        B ≤ D.g i0 := S.coverQuotient_ge_B hn hprog i0.isLt
        _ ≤ n - (i0 : ℕ) := hgLe
        _ ≤ n := Nat.sub_le n i0
    exact (Nat.one_le_div_iff hB).mpr hBLe
  have hcomponentLe : ∀ i : Fin S.k, E.factor i ≤ n / B := by
    intro i
    have htermPos : 0 < n - (i : ℕ) := by omega
    have hgPos : 0 < D.g i :=
      Nat.pos_of_dvd_of_pos (D.divides_term i i.isLt) htermPos
    have hgLe : D.g i ≤ n - (i : ℕ) :=
      Nat.le_of_dvd htermPos (D.divides_term i i.isLt)
    have hquotPos : 0 < (n - (i : ℕ)) / D.g i := Nat.div_pos hgLe hgPos
    calc
      E.factor i ≤ (n - (i : ℕ)) / D.g i :=
        Nat.le_of_dvd hquotPos (E.divides i)
      _ ≤ n / B := S.coverQuotient_le_div hB hn hprog i.isLt
  have hprodGt : n / B < ∏ i, E.factor i := by
    change n / B < E.value
    rw [hvalue]
    apply (Nat.div_lt_iff_lt_mul hB).mpr
    simpa [mul_comm] using hnd
  have htwo := exists_two_ne_one_of_prod_gt_bound E.factor hN hcomponentLe hprodGt
  exact ⟨d, E, hnd, hdn, hvalue, hcomponentDvd, hcomponentPairwise, htwo⟩

/-- The exact `S - E > 0` reduction: a strict cardinality bound produces a
member of the sifted progression with no divisor in the forbidden real
interval. -/
theorem exists_counterexample_of_bad_card_lt
    {B K X z : ℕ} (S : CoverBPZ.BPZSection6Input B K)
    (hB : 0 < B)
    (hcard : (BadCandidates S X z).card < (SiftedCandidates S X z).card) :
    ∃ n : ℕ,
      n ∈ Finset.Ioc (X / 2) X ∧ S.k < n ∧
      (CoverBPZ.Nk_formula S.k : ℤ) ∣ (n : ℤ) - S.α ∧
      IsZRough z (n.choose S.k) ∧
      ∀ d : ℕ, (d : ℝ) ∈ Set.Ioc ((n : ℝ) / B) n →
        ¬d ∣ n.choose S.k := by
  classical
  have hnsubset : ¬SiftedCandidates S X z ⊆ BadCandidates S X z := by
    intro hsub
    have hle := Finset.card_le_card hsub
    omega
  obtain ⟨n, hnS, hnBad⟩ := Finset.not_subset.mp hnsubset
  have hnData := hnS
  rw [SiftedCandidates, Finset.mem_filter] at hnData
  refine ⟨n, hnData.1, hnData.2.1, hnData.2.2.1, hnData.2.2.2, ?_⟩
  intro d hdI hdvd
  apply hnBad
  rw [BadCandidates, Finset.mem_filter]
  refine ⟨hnS, d, ?_, ?_, hdvd⟩
  · exact (mem_Ioc_natCast_div_iff hB).mp hdI |>.1
  · exact (mem_Ioc_natCast_div_iff hB).mp hdI |>.2

end Erdos387
