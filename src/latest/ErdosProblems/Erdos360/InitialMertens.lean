/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos360.LowerParameters
import BoundedGaps.PrimeNumberTheorem.Proof.MainTheorem

/-!
# Erdős 360: the initial-prime Mertens comparison

This file proves the finite Euler-product bookkeeping behind CFP (34).  The
two remaining numerical inputs are deliberately exposed as inequalities on
the last selected prime and on the reciprocal mass of target-prime factors
beyond it.  Subsequent lemmas discharge those inequalities asymptotically.
-/

namespace Erdos360

open Filter Asymptotics
open scoped BigOperators Asymptotics

noncomputable section

/-- The first `h` primes, including `2` when `h > 0`. -/
def firstPrimes (h : ℕ) : Finset ℕ :=
  (Finset.range h).image primeAt

/-- Prime factors of `n` which occur after the first `h` primes. -/
def lateTargetPrimes (n h : ℕ) : Finset ℕ :=
  n.primeFactors \ firstPrimes h

/-- The ordinary Euler product over the target primes after the cutoff. -/
noncomputable def lateTargetEulerProduct (n h : ℕ) : ℝ :=
  ∏ p ∈ lateTargetPrimes n h, (1 - (p : ℝ)⁻¹)

lemma mem_firstPrimes {h p : ℕ} :
    p ∈ firstPrimes h ↔ ∃ i < h, primeAt i = p := by
  simp [firstPrimes]

lemma firstPrimes_prime {h p : ℕ} (hp : p ∈ firstPrimes h) : p.Prime := by
  obtain ⟨i, _hi, rfl⟩ := mem_firstPrimes.mp hp
  exact Nat.prime_nth_prime i

lemma firstPrimes_eq_primesLE_primeAt_pred {h : ℕ} (hh : 0 < h) :
    firstPrimes h = (Finset.range (primeAt (h - 1) + 1)).filter Nat.Prime := by
  ext p
  constructor
  · intro hp
    obtain ⟨i, hi, rfl⟩ := mem_firstPrimes.mp hp
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_range.mpr ?_, Nat.prime_nth_prime i⟩
    exact Nat.lt_succ_of_le
      ((Nat.nth_strictMono Nat.infinite_setOfPred_prime).monotone (by omega))
  · intro hp
    obtain ⟨hple, hpprime⟩ := Finset.mem_filter.mp hp
    have hple' := Finset.mem_range.mp hple
    let i := Nat.count Nat.Prime p
    have hip : primeAt i = p := Nat.nth_count hpprime
    have hih : i < h := by
      by_contra hnot
      have hle : h ≤ i := Nat.le_of_not_gt hnot
      have hlast : h - 1 < i := by omega
      have hstrict :=
        (Nat.nth_strictMono Nat.infinite_setOfPred_prime) hlast
      change primeAt (h - 1) < primeAt i at hstrict
      rw [hip] at hstrict
      omega
    exact mem_firstPrimes.mpr ⟨i, hih, hip⟩

lemma firstPrimes_zero_mem {h : ℕ} (hh : 0 < h) : 2 ∈ firstPrimes h := by
  exact mem_firstPrimes.mpr ⟨0, hh, Nat.nth_prime_zero_eq_two⟩

lemma firstPrimes_filter_not_dvd_eq_insert_or_odd
    {n h : ℕ} (hh : 0 < h) :
    (firstPrimes h).filter (fun p ↦ ¬p ∣ n) =
      if 2 ∣ n then oddFirstMissingPrimes n h
      else {2} ∪ oddFirstMissingPrimes n h := by
  ext p
  by_cases h2n : 2 ∣ n
  · rw [Finset.mem_filter]
    simp only [h2n, if_pos]
    constructor
    · rintro ⟨hpfirst, hpnot⟩
      have hpne : p ≠ 2 := fun hp2 ↦ hpnot (hp2 ▸ h2n)
      apply mem_oddFirstMissingPrimes.mpr
      exact ⟨mem_firstPrimes.mp hpfirst,
        (firstPrimes_prime hpfirst).two_le.lt_of_ne (Ne.symm hpne), hpnot⟩
    · intro hp
      obtain ⟨hpfirst, _hp2, hpnot⟩ := mem_oddFirstMissingPrimes.mp hp
      exact ⟨mem_firstPrimes.mpr hpfirst, hpnot⟩
  · rw [Finset.mem_filter]
    simp only [h2n, if_false, Finset.mem_union, Finset.mem_singleton]
    constructor
    · rintro ⟨hpfirst, hpnot⟩
      by_cases hp2 : p = 2
      · exact Or.inl hp2
      · apply Or.inr
        apply mem_oddFirstMissingPrimes.mpr
        exact ⟨mem_firstPrimes.mp hpfirst,
          (firstPrimes_prime hpfirst).two_le.lt_of_ne (Ne.symm hp2), hpnot⟩
    · rintro (rfl | hp)
      · exact ⟨mem_firstPrimes.mpr ⟨0, hh, Nat.nth_prime_zero_eq_two⟩, h2n⟩
      · obtain ⟨hpfirst, _hp2, hpnot⟩ := mem_oddFirstMissingPrimes.mp hp
        exact ⟨mem_firstPrimes.mpr hpfirst, hpnot⟩

/-- The product over all missing first primes (including `2`) is no larger
than Core's odd-prime product. -/
lemma allMissingFirstProduct_le_initialMissingEulerProduct
    {n h : ℕ} (hh : 0 < h) :
    (∏ p ∈ (firstPrimes h).filter (fun p ↦ ¬p ∣ n),
        (1 - (p : ℝ)⁻¹)) ≤ initialMissingEulerProduct n h := by
  rw [firstPrimes_filter_not_dvd_eq_insert_or_odd hh]
  by_cases h2n : 2 ∣ n
  · simp only [h2n, if_pos]
    rw [initialMissingEulerProduct_eq_prod_oddFirstMissingPrimes hh]
    apply le_rfl
  · simp only [h2n, if_false]
    have h2not : 2 ∉ oddFirstMissingPrimes n h := by
      intro hp
      exact (mem_oddFirstMissingPrimes.mp hp).2.1.false
    rw [Finset.prod_union (by simpa [Finset.disjoint_left] using h2not)]
    norm_num
    rw [initialMissingEulerProduct_eq_prod_oddFirstMissingPrimes hh]
    change (1 / 2 : ℝ) *
        (∏ p ∈ oddFirstMissingPrimes n h, (1 - (p : ℝ)⁻¹)) ≤
      ∏ p ∈ oddFirstMissingPrimes n h, (1 - (p : ℝ)⁻¹)
    have hprod0 : 0 ≤ ∏ p ∈ oddFirstMissingPrimes n h,
        (1 - (p : ℝ)⁻¹) := by
      have hpos := (initialMissingEulerProduct_pos n h).le
      rw [initialMissingEulerProduct_eq_prod_oddFirstMissingPrimes hh] at hpos
      simpa only [Erdos851.oneShiftDensity] using hpos
    nlinarith

lemma primeFactors_filter_dvd_firstPrimes {n h : ℕ} (hn : 0 < n) :
    n.primeFactors ∩ firstPrimes h =
      (firstPrimes h).filter (fun p ↦ p ∣ n) := by
  ext p
  simp only [Finset.mem_inter, Finset.mem_filter]
  constructor
  · rintro ⟨hp, hfirst⟩
    exact ⟨hfirst, (Nat.mem_primeFactors.mp hp).2.1⟩
  · rintro ⟨hfirst, hpn⟩
    exact ⟨Nat.mem_primeFactors.mpr ⟨firstPrimes_prime hfirst, hpn, hn.ne'⟩,
      hfirst⟩

lemma firstPrimes_union_primeFactors_decomposition {n h : ℕ} :
    firstPrimes h ∪ n.primeFactors =
      firstPrimes h ∪ lateTargetPrimes n h := by
  ext p
  simp [lateTargetPrimes]

lemma firstPrimes_disjoint_lateTargetPrimes (n h : ℕ) :
    Disjoint (firstPrimes h) (lateTargetPrimes n h) := by
  rw [Finset.disjoint_left]
  intro p hp hlate
  exact (Finset.mem_sdiff.mp hlate).2 hp

/-- Exact factorization of the union product into the initial Mertens product
and the late target-prime product. -/
lemma firstUnionEulerProduct_eq_initial_mul_late (n h : ℕ) :
    (∏ p ∈ firstPrimes h ∪ n.primeFactors, (1 - (p : ℝ)⁻¹)) =
      (∏ p ∈ firstPrimes h, (1 - (p : ℝ)⁻¹)) *
        lateTargetEulerProduct n h := by
  rw [firstPrimes_union_primeFactors_decomposition,
    Finset.prod_union (firstPrimes_disjoint_lateTargetPrimes n h)]
  rfl

lemma firstPrimes_product_eq_prodP {h : ℕ} (hh : 0 < h) :
    (∏ p ∈ firstPrimes h, (1 - (p : ℝ)⁻¹)) =
      prodP (primeAt (h - 1)) := by
  rw [firstPrimes_eq_primesLE_primeAt_pred hh]
  simp only [prodP, one_div]

lemma lateTargetEulerProduct_lower_of_reciprocal_sum
    {n h : ℕ}
    (hsum : ∑ p ∈ lateTargetPrimes n h, (p : ℝ)⁻¹ ≤ 1 / 8) :
    (7 / 8 : ℝ) ≤ lateTargetEulerProduct n h := by
  have hprod : 1 - ∑ p ∈ lateTargetPrimes n h, (p : ℝ)⁻¹ ≤
      ∏ p ∈ lateTargetPrimes n h, (1 - (p : ℝ)⁻¹) := by
    have aux : ∀ (s : Finset ℕ),
        (∀ p ∈ s, p.Prime) →
        1 - ∑ p ∈ s, (p : ℝ)⁻¹ ≤
          ∏ p ∈ s, (1 - (p : ℝ)⁻¹) := by
      intro s hs
      induction s using Finset.induction with
      | empty => simp
      | @insert a s ha ih =>
        rw [Finset.sum_insert ha, Finset.prod_insert ha]
        have ha0 : 0 ≤ (a : ℝ)⁻¹ := by positivity
        have ha1 : (a : ℝ)⁻¹ ≤ 1 := by
          have haprime := hs a (by simp)
          exact (inv_le_one₀ (by exact_mod_cast haprime.pos)).2
            (by exact_mod_cast haprime.one_le)
        have hsum0 : 0 ≤ ∑ p ∈ s, (p : ℝ)⁻¹ := by positivity
        have ih' := ih (fun p hp ↦ hs p (by simp [hp]))
        calc
          1 - ((a : ℝ)⁻¹ + ∑ p ∈ s, (p : ℝ)⁻¹) ≤
              (1 - (a : ℝ)⁻¹) *
                (1 - ∑ p ∈ s, (p : ℝ)⁻¹) := by nlinarith
          _ ≤ (1 - (a : ℝ)⁻¹) *
                ∏ p ∈ s, (1 - (p : ℝ)⁻¹) :=
            mul_le_mul_of_nonneg_left ih' (sub_nonneg.mpr ha1)
    apply aux
    intro p hp
    exact Nat.prime_of_mem_primeFactors (Finset.mem_sdiff.mp hp).1
  change (7 / 8 : ℝ) ≤ ∏ p ∈ lateTargetPrimes n h, (1 - (p : ℝ)⁻¹)
  linarith

/-- Every late target prime lies strictly beyond the final selected prime. -/
lemma primeAt_pred_lt_of_mem_lateTargetPrimes
    {n h p : ℕ} (hh : 0 < h) (hp : p ∈ lateTargetPrimes n h) :
    primeAt (h - 1) < p := by
  have hpprime := Nat.prime_of_mem_primeFactors (Finset.mem_sdiff.mp hp).1
  have hpnot := (Finset.mem_sdiff.mp hp).2
  let i := Nat.count Nat.Prime p
  have hip : primeAt i = p := Nat.nth_count hpprime
  have hhi : h ≤ i := by
    by_contra hnot
    have hilt : i < h := Nat.lt_of_not_ge hnot
    exact hpnot (mem_firstPrimes.mpr ⟨i, hilt, hip⟩)
  have hpredlt : h - 1 < i := by omega
  have hstrict :=
    (Nat.nth_strictMono Nat.infinite_setOfPred_prime) hpredlt
  change primeAt (h - 1) < primeAt i at hstrict
  simpa only [hip] using hstrict

/-- An entirely finite sufficient condition for the `1/8` tail budget.
The proof uses only that the product of the late distinct prime factors
divides `n`. -/
lemma lateTarget_reciprocal_sum_le_eighth
    {n h : ℕ} (hn : 0 < n) (hh : 2 ≤ h)
    (hnumeric : 8 * Real.log (n : ℝ) ≤
      (primeAt (h - 1) : ℝ) *
        Real.log (primeAt (h - 1) : ℝ)) :
    ∑ p ∈ lateTargetPrimes n h, (p : ℝ)⁻¹ ≤ 1 / 8 := by
  let q := primeAt (h - 1)
  let T := lateTargetPrimes n h
  have hhpos : 0 < h := by omega
  have hq3 : 3 ≤ q := by
    dsimp [q]
    exact (Nat.nth_strictMono Nat.infinite_setOfPred_prime).monotone
      (by omega : 1 ≤ h - 1) |>.trans' (by norm_num)
  have hqpos : (0 : ℝ) < q := by exact_mod_cast (show 0 < q by omega)
  have hlogq : 0 < Real.log (q : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < q by omega))
  have hTprime : ∀ p ∈ T, p.Prime := by
    intro p hp
    have hp' : p ∈ lateTargetPrimes n h := by simpa only [T] using hp
    exact Nat.prime_of_mem_primeFactors
      (Finset.mem_sdiff.mp hp').1
  have hqle : ∀ p ∈ T, q ≤ p := by
    intro p hp
    exact (primeAt_pred_lt_of_mem_lateTargetPrimes hhpos
      (by simpa only [T] using hp)).le
  have hprodDvd : (∏ p ∈ T, p) ∣ n := by
    apply (Finset.prod_dvd_prod_of_subset T n.primeFactors id ?_).trans
      (Nat.prod_primeFactors_dvd n)
    intro p hp
    have hp' : p ∈ lateTargetPrimes n h := by simpa only [T] using hp
    exact (Finset.mem_sdiff.mp hp').1
  have hprodPos : 0 < ∏ p ∈ T, p := by
    exact Finset.prod_pos fun p hp ↦ (hTprime p hp).pos
  have hprodLe : ∏ p ∈ T, p ≤ n :=
    Nat.le_of_dvd hn hprodDvd
  have hlogProdLe :
      Real.log ((∏ p ∈ T, p : ℕ) : ℝ) ≤ Real.log (n : ℝ) := by
    gcongr
  have hlogProdEq :
      Real.log ((∏ p ∈ T, p : ℕ) : ℝ) =
        ∑ p ∈ T, Real.log (p : ℝ) := by
    rw [Nat.cast_prod, Real.log_prod]
    intro p hp
    exact_mod_cast (hTprime p hp).ne_zero
  have hcardLog : (T.card : ℝ) * Real.log (q : ℝ) ≤
      Real.log (n : ℝ) := by
    calc
      (T.card : ℝ) * Real.log (q : ℝ) =
          ∑ _p ∈ T, Real.log (q : ℝ) := by simp
      _ ≤ ∑ p ∈ T, Real.log (p : ℝ) := by
        apply Finset.sum_le_sum
        intro p hp
        exact Real.strictMonoOn_log.monotoneOn
          (by simpa only [Set.mem_Ioi] using hqpos)
          (by
            simp only [Set.mem_Ioi]
            exact_mod_cast (hTprime p hp).pos)
          (by exact_mod_cast hqle p hp)
      _ = Real.log ((∏ p ∈ T, p : ℕ) : ℝ) := hlogProdEq.symm
      _ ≤ Real.log (n : ℝ) := hlogProdLe
  have hcardEight : 8 * (T.card : ℝ) ≤ q := by
    have hnum : 8 * Real.log (n : ℝ) ≤
        (q : ℝ) * Real.log (q : ℝ) := by
      simpa [q] using hnumeric
    nlinarith
  have hsum : ∑ p ∈ T, (p : ℝ)⁻¹ ≤
      (T.card : ℝ) * (q : ℝ)⁻¹ := by
    simpa [nsmul_eq_mul] using
      (Finset.sum_le_card_nsmul T (fun p ↦ (p : ℝ)⁻¹) (q : ℝ)⁻¹
        (fun p hp ↦ (inv_le_inv₀ (by exact_mod_cast (hTprime p hp).pos) hqpos).2
          (by exact_mod_cast hqle p hp)))
  change ∑ p ∈ T, (p : ℝ)⁻¹ ≤ 1 / 8
  calc
    ∑ p ∈ T, (p : ℝ)⁻¹ ≤
        (T.card : ℝ) * (q : ℝ)⁻¹ := hsum
    _ ≤ 1 / 8 := by
      rw [← div_eq_mul_inv]
      exact (div_le_iff₀ hqpos).2 (by nlinarith)

/-- The same tail budget with the more convenient color-count condition
`8 log n ≤ h log h`; the last selected prime is at least `h`. -/
lemma lateTarget_reciprocal_sum_le_eighth_of_color_log
    {n h : ℕ} (hn : 0 < n) (hh : 2 ≤ h)
    (hcolorLog : 8 * Real.log (n : ℝ) ≤
      (h : ℝ) * Real.log (h : ℝ)) :
    ∑ p ∈ lateTargetPrimes n h, (p : ℝ)⁻¹ ≤ 1 / 8 := by
  apply lateTarget_reciprocal_sum_le_eighth hn hh
  have hqge : h ≤ primeAt (h - 1) := by
    have hp := Nat.add_two_le_nth_prime (h - 1)
    change h - 1 + 2 ≤ primeAt (h - 1) at hp
    omega
  have hlogh : 0 ≤ Real.log (h : ℝ) :=
    (Real.log_pos (by exact_mod_cast (show 1 < h by omega))).le
  have hlogmono : Real.log (h : ℝ) ≤
      Real.log (primeAt (h - 1) : ℝ) := by
    gcongr
  calc
    8 * Real.log (n : ℝ) ≤ (h : ℝ) * Real.log (h : ℝ) :=
      hcolorLog
    _ ≤ (primeAt (h - 1) : ℝ) *
        Real.log (primeAt (h - 1) : ℝ) := by
      exact mul_le_mul (by exact_mod_cast hqge) hlogmono hlogh
        (by positivity)

/-- CFP's threshold `10 log n / log log n ≤ h` implies the preceding
color-log inequality once `log h ≥ (4/5) log log n`. -/
lemma color_log_tail_numeric_of_cfp_threshold
    {n h : ℕ}
    (_hlogn : 0 ≤ Real.log (n : ℝ))
    (hloglogn : 0 < Real.log (Real.log (n : ℝ)))
    (hthreshold : 10 * Real.log (n : ℝ) /
        Real.log (Real.log (n : ℝ)) ≤ (h : ℝ))
    (hlogh : (4 / 5 : ℝ) * Real.log (Real.log (n : ℝ)) ≤
        Real.log (h : ℝ)) :
    8 * Real.log (n : ℝ) ≤ (h : ℝ) * Real.log (h : ℝ) := by
  have hthreshold' : 10 * Real.log (n : ℝ) ≤
      (h : ℝ) * Real.log (Real.log (n : ℝ)) := by
    have := (div_le_iff₀ hloglogn).mp hthreshold
    nlinarith
  have hh0 : 0 ≤ (h : ℝ) := by positivity
  nlinarith [mul_le_mul_of_nonneg_left hlogh hh0]

/-- The logarithmic slack used in CFP's tail estimate follows already from
the displayed threshold.  The elementary inequality
`log L ≤ 5 L^(1/5)` absorbs the `log log n` denominator. -/
lemma four_fifths_loglog_le_log_of_cfp_threshold
    {n h : ℕ}
    (hlogn : 0 < Real.log (n : ℝ))
    (hloglogn : 0 < Real.log (Real.log (n : ℝ)))
    (hthreshold : 10 * Real.log (n : ℝ) /
        Real.log (Real.log (n : ℝ)) ≤ (h : ℝ)) :
    (4 / 5 : ℝ) * Real.log (Real.log (n : ℝ)) ≤
      Real.log (h : ℝ) := by
  let L := Real.log (n : ℝ)
  let P := Real.rpow L (4 / 5 : ℝ)
  let Q := Real.rpow L (1 / 5 : ℝ)
  have hL : 0 < L := by simpa only [L] using hlogn
  have hLL : 0 < Real.log L := by simpa only [L] using hloglogn
  have hlogPower : Real.log L ≤ 5 * Q := by
    have hraw := Real.log_le_rpow_div hL.le
      (show (0 : ℝ) < 1 / 5 by norm_num)
    change Real.log L ≤ Real.rpow L (1 / 5 : ℝ) /
      (1 / 5 : ℝ) at hraw
    calc
      Real.log L ≤ Real.rpow L (1 / 5 : ℝ) /
          (1 / 5 : ℝ) := hraw
      _ = 5 * Q := by
        dsimp only [Q]
        ring
  have hPQ : P * Q = L := by
    dsimp only [P, Q]
    calc
      Real.rpow L (4 / 5 : ℝ) * Real.rpow L (1 / 5 : ℝ) =
          Real.rpow L ((4 / 5 : ℝ) + 1 / 5) :=
        (Real.rpow_add hL _ _).symm
      _ = Real.rpow L (1 : ℝ) := by norm_num
      _ = L := Real.rpow_one L
  have hpowerThreshold : P ≤
      10 * Real.log (n : ℝ) /
        Real.log (Real.log (n : ℝ)) := by
    rw [le_div_iff₀ hloglogn]
    change P * Real.log L ≤ 10 * L
    calc
      P * Real.log L ≤ P * (5 * Q) :=
        mul_le_mul_of_nonneg_left hlogPower (Real.rpow_nonneg hL.le _)
      _ = 5 * (P * Q) := by ring
      _ = 5 * L := by rw [hPQ]
      _ ≤ 10 * L := by nlinarith
  have hPh : P ≤ (h : ℝ) := hpowerThreshold.trans hthreshold
  have hPpos : 0 < P := Real.rpow_pos_of_pos hL _
  have hhR : 0 < (h : ℝ) := hPpos.trans_le hPh
  have hlogMono : Real.log P ≤ Real.log (h : ℝ) :=
    Real.strictMonoOn_log.monotoneOn
      (by simpa only [Set.mem_Ioi] using hPpos)
      (by simpa only [Set.mem_Ioi] using hhR) hPh
  calc
    (4 / 5 : ℝ) * Real.log (Real.log (n : ℝ)) =
        Real.log P := by
      dsimp only [P, L]
      symm
      exact Real.log_rpow hlogn (4 / 5 : ℝ)
    _ ≤ Real.log (h : ℝ) := hlogMono

/-! ## Eventual control of the final selected prime -/

lemma primeCounting_primeAt_pred_eq {h : ℕ} (hh : 0 < h) :
    Nat.primeCounting (primeAt (h - 1)) = h := by
  rw [Nat.primeCounting_eq_primeCounting'_succ]
  change Nat.count Nat.Prime (primeAt (h - 1) + 1) = h
  rw [Nat.count_nth_succ_of_infinite Nat.infinite_setOfPred_prime]
  omega

lemma eventually_primeCounting_half_lower :
    ∀ᶠ x : ℕ in atTop,
      (1 / 2 : ℝ) * ((x : ℝ) / Real.log (x : ℝ)) ≤
        (Nat.primeCounting x : ℝ) := by
  have hpnt :=
    BoundedGaps.PrimeNumberTheorem.primeCounting_natCast_isEquivalent
  have herr := hpnt.isLittleO.def (show (0 : ℝ) < 1 / 2 by norm_num)
  have hmainPos : ∀ᶠ x : ℕ in atTop,
      0 ≤ (x : ℝ) / Real.log (x : ℝ) := by
    filter_upwards [eventually_ge_atTop 3] with x hx
    positivity
  filter_upwards [herr, hmainPos] with x hx hpos
  simp only [Pi.sub_apply, Real.norm_eq_abs, abs_of_nonneg hpos] at hx
  have hneg := neg_abs_le
    ((Nat.primeCounting x : ℝ) - (x : ℝ) / Real.log (x : ℝ))
  nlinarith

lemma primeAt_pred_tendsto_atTop :
    Tendsto (fun h : ℕ ↦ primeAt (h - 1)) atTop atTop := by
  exact (Nat.nth_strictMono Nat.infinite_setOfPred_prime).tendsto_atTop.comp
    (Filter.tendsto_sub_atTop_nat 1)

/-- A PNT consequence in exactly the logarithmic form consumed by the finite
CFP product estimate. -/
lemma eventually_log_primeAt_pred_le_seven_sixths :
    ∀ᶠ h : ℕ in atTop,
      Real.log (primeAt (h - 1) : ℝ) ≤
        (7 / 6 : ℝ) * Real.log (h : ℝ) := by
  have hpnt := primeAt_pred_tendsto_atTop.eventually
    eventually_primeCounting_half_lower
  have htTop :=
    ((tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 12)).comp
      tendsto_natCast_atTop_atTop).eventually
        (eventually_ge_atTop (100 : ℝ))
  filter_upwards [eventually_ge_atTop 3, hpnt, htTop] with h hh hpnt ht
  let p := primeAt (h - 1)
  let t := Real.rpow (h : ℝ) (1 / 12 : ℝ)
  have hhR : (0 : ℝ) < h := by positivity
  have hpPrime : p.Prime := Nat.prime_nth_prime (h - 1)
  have hpR : (0 : ℝ) < p := by exact_mod_cast hpPrime.pos
  have hlogh : 0 < Real.log (h : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < h by omega))
  have hlogp : 0 < Real.log (p : ℝ) :=
    Real.log_pos (by exact_mod_cast hpPrime.one_lt)
  have hpi : (Nat.primeCounting p : ℝ) = h := by
    exact_mod_cast primeCounting_primeAt_pred_eq (show 0 < h by omega)
  have hlinear : (p : ℝ) ≤ 2 * h * Real.log (p : ℝ) := by
    change (1 / 2 : ℝ) * ((p : ℝ) / Real.log (p : ℝ)) ≤
      (Nat.primeCounting p : ℝ) at hpnt
    rw [hpi] at hpnt
    have hpdiv : (p : ℝ) / Real.log (p : ℝ) ≤ 2 * h := by
      nlinarith
    have := (div_le_iff₀ hlogp).mp hpdiv
    nlinarith
  have hlogSqrt : Real.log (p : ℝ) ≤ 2 * Real.sqrt (p : ℝ) := by
    have hraw := Real.log_le_rpow_div hpR.le
      (show (0 : ℝ) < 1 / 2 by norm_num)
    rw [← Real.sqrt_eq_rpow] at hraw
    norm_num [div_eq_mul_inv] at hraw ⊢
    nlinarith
  have hsqrtPos : 0 < Real.sqrt (p : ℝ) := Real.sqrt_pos.2 hpR
  have hsqrtSq : (Real.sqrt (p : ℝ)) ^ 2 = p :=
    Real.sq_sqrt hpR.le
  have hsqrtBound : Real.sqrt (p : ℝ) ≤ 4 * h := by
    have hpSqrt : (p : ℝ) ≤ 4 * h * Real.sqrt (p : ℝ) := by
      nlinarith [mul_le_mul_of_nonneg_left hlogSqrt
        (show (0 : ℝ) ≤ 2 * h by positivity)]
    nlinarith
  have hpQuad : (p : ℝ) ≤ 16 * (h : ℝ) ^ 2 := by
    nlinarith
  have hlogQuad : Real.log (p : ℝ) ≤
      Real.log (16 : ℝ) + 2 * Real.log (h : ℝ) := by
    have hmono : Real.log (p : ℝ) ≤
        Real.log (16 * (h : ℝ) ^ 2) := by
      exact Real.strictMonoOn_log.monotoneOn
        (by simpa only [Set.mem_Ioi] using hpR)
        (by simp only [Set.mem_Ioi]; positivity)
        hpQuad
    rw [Real.log_mul (by norm_num : (16 : ℝ) ≠ 0) (by positivity),
      Real.log_pow] at hmono
    norm_num at hmono ⊢
    exact hmono
  have hloghT : Real.log (h : ℝ) ≤ 12 * t := by
    have hraw := Real.log_le_rpow_div hhR.le
      (show (0 : ℝ) < 1 / 12 by norm_num)
    change Real.log (h : ℝ) ≤
      Real.rpow (h : ℝ) (1 / 12 : ℝ) / (1 / 12 : ℝ) at hraw
    dsimp only [t]
    norm_num [div_eq_mul_inv] at hraw
    simpa [mul_comm] using hraw
  have ht100 : (100 : ℝ) ≤ t := by simpa [t] using ht
  have ht0 : 0 ≤ t := Real.rpow_nonneg hhR.le _
  have hlog16 : Real.log (16 : ℝ) ≤ 15 := by
    nlinarith [Real.log_le_sub_one_of_pos (show (0 : ℝ) < 16 by norm_num)]
  have htSq : t ^ 2 = Real.rpow (h : ℝ) (1 / 6 : ℝ) := by
    dsimp [t]
    calc
      (Real.rpow (h : ℝ) (1 / 12 : ℝ)) ^ 2 =
          Real.rpow (Real.rpow (h : ℝ) (1 / 12 : ℝ)) (2 : ℝ) := by
        symm
        exact Real.rpow_natCast _ 2
      _ = Real.rpow (h : ℝ) ((1 / 12 : ℝ) * 2) :=
        (Real.rpow_mul hhR.le _ _).symm
      _ = Real.rpow (h : ℝ) (1 / 6 : ℝ) := by norm_num
  have hcoeff : 2 * (Real.log (16 : ℝ) + 2 * Real.log (h : ℝ)) ≤
      Real.rpow (h : ℝ) (1 / 6 : ℝ) := by
    rw [← htSq]
    nlinarith
  have hpPower : (p : ℝ) ≤
      Real.rpow (h : ℝ) (7 / 6 : ℝ) := by
    have hpInter : (p : ℝ) ≤
        (h : ℝ) * Real.rpow (h : ℝ) (1 / 6 : ℝ) := by
      calc
        (p : ℝ) ≤ 2 * h * Real.log (p : ℝ) := hlinear
        _ ≤ (h : ℝ) *
            (2 * (Real.log (16 : ℝ) + 2 * Real.log (h : ℝ))) := by
          nlinarith [mul_le_mul_of_nonneg_left hlogQuad
            (show (0 : ℝ) ≤ 2 * h by positivity)]
        _ ≤ (h : ℝ) * Real.rpow (h : ℝ) (1 / 6 : ℝ) :=
          mul_le_mul_of_nonneg_left hcoeff hhR.le
    calc
      (p : ℝ) ≤ (h : ℝ) * Real.rpow (h : ℝ) (1 / 6 : ℝ) :=
        hpInter
      _ = Real.rpow (h : ℝ) (7 / 6 : ℝ) := by
        calc
          (h : ℝ) * Real.rpow (h : ℝ) (1 / 6 : ℝ) =
              Real.rpow (h : ℝ) (1 : ℝ) *
                Real.rpow (h : ℝ) (1 / 6 : ℝ) := by
            exact congrArg
              (fun x : ℝ ↦ x * Real.rpow (h : ℝ) (1 / 6 : ℝ))
              (Real.rpow_one (h : ℝ)).symm
          _ = Real.rpow (h : ℝ) ((1 : ℝ) + 1 / 6) :=
            (Real.rpow_add hhR _ _).symm
          _ = Real.rpow (h : ℝ) (7 / 6 : ℝ) := by norm_num
  change Real.log (p : ℝ) ≤ (7 / 6 : ℝ) * Real.log (h : ℝ)
  calc
    Real.log (p : ℝ) ≤ Real.log (Real.rpow (h : ℝ) (7 / 6 : ℝ)) := by
      exact Real.strictMonoOn_log.monotoneOn
        (by simpa only [Set.mem_Ioi] using hpR)
        (by
          simp only [Set.mem_Ioi]
          exact Real.rpow_pos_of_pos hhR _)
        hpPower
    _ = (7 / 6 : ℝ) * Real.log (h : ℝ) := by
      exact Real.log_rpow hhR (7 / 6 : ℝ)

/-- Cancelling the target-prime Euler factors leaves precisely the product
over first primes which do not divide the target. -/
lemma totientRatio_mul_firstUnionProduct_eq_allMissing
    {n h : ℕ} (hn : 0 < n) :
    ((n : ℝ) / Nat.totient n) *
        (∏ p ∈ firstPrimes h ∪ n.primeFactors,
          (1 - (p : ℝ)⁻¹)) =
      ∏ p ∈ (firstPrimes h).filter (fun p ↦ ¬p ∣ n),
        (1 - (p : ℝ)⁻¹) := by
  let M := (firstPrimes h).filter (fun p ↦ ¬p ∣ n)
  let T := n.primeFactors
  have hunion : firstPrimes h ∪ n.primeFactors = M ∪ T := by
    ext p
    simp only [Finset.mem_union, Finset.mem_filter, M, T]
    constructor
    · rintro (hpI | hpT)
      · by_cases hpn : p ∣ n
        · exact Or.inr (Nat.mem_primeFactors.mpr
            ⟨firstPrimes_prime hpI, hpn, hn.ne'⟩)
        · exact Or.inl ⟨hpI, hpn⟩
      · exact Or.inr hpT
    · rintro (⟨hpI, _hpn⟩ | hpT)
      · exact Or.inl hpI
      · exact Or.inr hpT
  have hdisj : Disjoint M T := by
    rw [Finset.disjoint_left]
    intro p hpM hpT
    exact (Finset.mem_filter.mp hpM).2
      (Nat.mem_primeFactors.mp hpT).2.1
  have hcancel :
      (∏ p ∈ T, ((p : ℝ) / ((p : ℝ) - 1))) *
          (∏ p ∈ T, (1 - (p : ℝ)⁻¹)) = 1 := by
    rw [← Finset.prod_mul_distrib]
    apply Finset.prod_eq_one
    intro p hp
    have hpprime := Nat.prime_of_mem_primeFactors (by simpa [T] using hp)
    rw [← Erdos4.oneShift_inverseFactor_eq_primeRatio hpprime]
    simp only [Erdos851.oneShiftDensity]
    exact inv_mul_cancel₀ (by
      exact (Erdos851.oneShift_localFactor_pos hpprime).ne')
  rw [Erdos4.cofactor_ratio_eq_primeFactors_product n hn.ne', hunion,
    Finset.prod_union hdisj]
  change (∏ p ∈ T, (p : ℝ) / ((p : ℝ) - 1)) *
      ((∏ p ∈ M, (1 - (p : ℝ)⁻¹)) *
        ∏ p ∈ T, (1 - (p : ℝ)⁻¹)) =
      ∏ p ∈ M, (1 - (p : ℝ)⁻¹)
  calc
    _ = (∏ p ∈ M, (1 - (p : ℝ)⁻¹)) *
        ((∏ p ∈ T, (p : ℝ) / ((p : ℝ) - 1)) *
          ∏ p ∈ T, (1 - (p : ℝ)⁻¹)) := by ring
    _ = _ := by rw [hcancel, mul_one]

/-- Finite form of CFP (34).  The constants `7/6` and `1/8` were selected so
that the explicit Mertens constant `3` gives exactly the desired `4`. -/
lemma initialMissingMertensBounds_of_cutoff_and_tail
    {n h : ℕ} (hn : 0 < n) (hh : 3 ≤ h)
    (hcut : Real.log (primeAt (h - 1) : ℝ) ≤
      (7 / 6 : ℝ) * Real.log (h : ℝ))
    (htail : ∑ p ∈ lateTargetPrimes n h, (p : ℝ)⁻¹ ≤ 1 / 8) :
    InitialMissingMertensBounds n h := by
  let q := primeAt (h - 1)
  have hhpos : 0 < h := by omega
  have hlogh : 0 < Real.log (h : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < h by omega))
  have hq3 : 3 ≤ q := by
    dsimp [q]
    exact (Nat.nth_strictMono Nat.infinite_setOfPred_prime).monotone
      (by omega : 1 ≤ h - 1) |>.trans' (by norm_num)
  have hlogq : 0 < Real.log (q : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < q by omega))
  have hMertens : 1 / (3 * Real.log (q : ℝ)) ≤ prodP q :=
    mertens_third_theorem q hq3
  have hMertensNonneg : 0 ≤ prodP q :=
    (by positivity : 0 ≤ 1 / (3 * Real.log (q : ℝ))).trans hMertens
  have htailProd : (7 / 8 : ℝ) ≤ lateTargetEulerProduct n h :=
    lateTargetEulerProduct_lower_of_reciprocal_sum htail
  have hunionLower :
      7 / (24 * Real.log (q : ℝ)) ≤
        ∏ p ∈ firstPrimes h ∪ n.primeFactors,
          (1 - (p : ℝ)⁻¹) := by
    calc
      7 / (24 * Real.log (q : ℝ)) =
          (1 / (3 * Real.log (q : ℝ))) * (7 / 8) := by
        field_simp [hlogq.ne']
        norm_num
      _ ≤ prodP q * (7 / 8) :=
        mul_le_mul_of_nonneg_right hMertens (by norm_num)
      _ ≤ prodP q * lateTargetEulerProduct n h :=
        mul_le_mul_of_nonneg_left htailProd hMertensNonneg
      _ = ∏ p ∈ firstPrimes h ∪ n.primeFactors,
          (1 - (p : ℝ)⁻¹) := by
        rw [firstUnionEulerProduct_eq_initial_mul_late,
          firstPrimes_product_eq_prodP hhpos]
  have hratioPos : 0 < (n : ℝ) / Nat.totient n := by
    exact div_pos (by exact_mod_cast hn)
      (by exact_mod_cast Nat.totient_pos.mpr hn)
  have hscaled := mul_le_mul_of_nonneg_left hunionLower hratioPos.le
  rw [totientRatio_mul_firstUnionProduct_eq_allMissing hn] at hscaled
  have hVlowerAtQ :
      ((n : ℝ) / Nat.totient n) *
          (7 / (24 * Real.log (q : ℝ))) ≤
        initialMissingEulerProduct n h :=
    hscaled.trans (allMissingFirstProduct_le_initialMissingEulerProduct hhpos)
  have hrecip :
      1 / (4 * Real.log (h : ℝ)) ≤
        7 / (24 * Real.log (q : ℝ)) := by
    rw [div_le_div_iff₀ (mul_pos (by norm_num) hlogh)
      (mul_pos (by norm_num) hlogq)]
    nlinarith
  have hlower :
      ((n : ℝ) / Nat.totient n) /
          (4 * Real.log (h : ℝ)) ≤
        initialMissingEulerProduct n h := by
    calc
      ((n : ℝ) / Nat.totient n) /
          (4 * Real.log (h : ℝ)) =
          ((n : ℝ) / Nat.totient n) *
            (1 / (4 * Real.log (h : ℝ))) := by ring
      _ ≤ ((n : ℝ) / Nat.totient n) *
          (7 / (24 * Real.log (q : ℝ))) :=
        mul_le_mul_of_nonneg_left hrecip hratioPos.le
      _ ≤ initialMissingEulerProduct n h := hVlowerAtQ
  have hqge : h ≤ q := by
    change h ≤ primeAt (h - 1)
    have := Nat.add_two_le_nth_prime (h - 1)
    change h - 1 + 2 ≤ primeAt (h - 1) at this
    omega
  have hlogle : Real.log (h : ℝ) ≤ Real.log (q : ℝ) := by
    gcongr
  have hupperQ := initialMissingEulerProduct_upper (n := n) hn
    (h := h) (by omega : 2 ≤ h)
  have hupper : initialMissingEulerProduct n h ≤
      2 * ((n : ℝ) / Nat.totient n) / Real.log (h : ℝ) := by
    calc
      initialMissingEulerProduct n h ≤
          2 * ((n : ℝ) / Nat.totient n) /
            Real.log (primeAt (h - 1) : ℝ) := hupperQ
      _ ≤ 2 * ((n : ℝ) / Nat.totient n) /
            Real.log (h : ℝ) := by
        exact div_le_div_of_nonneg_left (by positivity) hlogh
          (by simpa [q] using hlogle)
  exact ⟨hlogh, hlower, hupper⟩

/-! ## Specialization to the diagonal color parameter -/

lemma eventually_four_fifths_loglog_le_log_lowerColorCount
    {c : ℝ} (hc : 0 < c) :
    ∀ᶠ n : ℕ in atTop,
      (4 / 5 : ℝ) * Real.log (Real.log (n : ℝ)) ≤
        Real.log (lowerColorCount c n : ℝ) := by
  have hlog := tendsto_log_coe_at_top.eventually
    (eventually_gt_atTop (0 : ℝ))
  have hloglog := tendsto_log_log_coe_at_top.eventually
    (eventually_gt_atTop (0 : ℝ))
  filter_upwards [hlog, hloglog,
    eventually_ten_log_div_loglog_le_lowerColorCount hc] with
      n hnlog hnloglog hnthreshold
  exact four_fifths_loglog_le_log_of_cfp_threshold
    hnlog hnloglog hnthreshold

lemma eventually_lateTarget_reciprocal_sum_lowerColorCount
    {c : ℝ} (hc : 0 < c) :
    ∀ᶠ n : ℕ in atTop,
      ∑ p ∈ lateTargetPrimes n (lowerColorCount c n),
        (p : ℝ)⁻¹ ≤ 1 / 8 := by
  have hlog := tendsto_log_coe_at_top.eventually
    (eventually_gt_atTop (0 : ℝ))
  have hloglog := tendsto_log_log_coe_at_top.eventually
    (eventually_gt_atTop (0 : ℝ))
  filter_upwards [eventually_gt_atTop 0,
    eventually_three_le_lowerColorCount hc, hlog, hloglog,
    eventually_ten_log_div_loglog_le_lowerColorCount hc,
    eventually_four_fifths_loglog_le_log_lowerColorCount hc] with
      n hn hncolors hnlog hnloglog hnthreshold hncolorLog
  apply lateTarget_reciprocal_sum_le_eighth_of_color_log hn (by omega)
  exact color_log_tail_numeric_of_cfp_threshold hnlog.le hnloglog
    hnthreshold hncolorLog

/-- CFP equation (34), with `r` specialized to the integral diagonal color
parameter used by the lower-bound construction. -/
lemma eventually_initialMissingMertensBounds_lowerColorCount
    {c : ℝ} (hc : 0 < c) :
    ∀ᶠ n : ℕ in atTop,
      InitialMissingMertensBounds n (lowerColorCount c n) := by
  have hcut := (lowerColorCount_tendsto_atTop hc).eventually
    eventually_log_primeAt_pred_le_seven_sixths
  filter_upwards [eventually_gt_atTop 0,
    eventually_three_le_lowerColorCount hc, hcut,
    eventually_lateTarget_reciprocal_sum_lowerColorCount hc] with
      n hn hncolors hncut hntail
  exact initialMissingMertensBounds_of_cutoff_and_tail hn hncolors
    hncut hntail

end

end Erdos360
