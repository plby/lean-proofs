/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos896.Ford.ReductionCore
import ErdosProblems.Erdos896.Ford.ABPSplit
import ErdosProblems.Erdos896.Ford.Sieve
import ErdosProblems.Erdos896.Ford.LogUnionPrimeSum
import ErdosProblems.Erdos896.Ford.Denominator

/-!
# The arithmetic reduction in Ford's upper bound

This file formalizes the finite, lossless part of Lemma 3.2 in Ford's short
proof of the multiplication-table estimate.  A positive integer is split
canonically into its exponent-one (squarefree) part and its exponent-at-least
two (squarefull) part.  A divisor of the original integer then splits between
the two coprime parts.  This gives the precise finite cover underlying Ford's
first displayed upper bound for `H(x,y,2y)`.

The later analytic estimates (the squarefull tail, the rough-number sieve,
and the prime reciprocal sum over the logarithmic divisor union) use this
cover as their arithmetic input.
-/

namespace Erdos896.Ford

open scoped BigOperators

/-! ## Canonical squarefree--squarefull decomposition -/

/-- The part of `n` formed by prime powers whose exponent in `n` is exactly
one. -/
def squarefreeComponent (n : ℕ) : ℕ :=
  (n.factorization.filter fun p ↦ n.factorization p = 1).prod (fun p k ↦ p ^ k)

/-- The complementary part of `n`, formed by prime powers whose exponent is
not one.  For positive `n`, every prime occurring here has exponent at least
two. -/
def squarefullComponent (n : ℕ) : ℕ :=
  (n.factorization.filter fun p ↦ n.factorization p ≠ 1).prod (fun p k ↦ p ^ k)

private lemma squarefreeFactorization_le (n : ℕ) :
    n.factorization.filter (fun p ↦ n.factorization p = 1) ≤ n.factorization := by
  intro p
  by_cases hp : n.factorization p = 1 <;>
    simp [hp]

private lemma squarefullFactorization_le (n : ℕ) :
    n.factorization.filter (fun p ↦ n.factorization p ≠ 1) ≤ n.factorization := by
  intro p
  by_cases hp : n.factorization p = 1 <;>
    simp [hp]

@[simp]
theorem factorization_squarefreeComponent (n : ℕ) :
    (squarefreeComponent n).factorization =
      n.factorization.filter (fun p ↦ n.factorization p = 1) := by
  exact Nat.factorization_prod_pow_eq_self_of_le_factorization
    (squarefreeFactorization_le n)

@[simp]
theorem factorization_squarefullComponent (n : ℕ) :
    (squarefullComponent n).factorization =
      n.factorization.filter (fun p ↦ n.factorization p ≠ 1) := by
  exact Nat.factorization_prod_pow_eq_self_of_le_factorization
    (squarefullFactorization_le n)

theorem squarefreeComponent_mul_squarefullComponent {n : ℕ} (hn : n ≠ 0) :
    squarefreeComponent n * squarefullComponent n = n := by
  rw [squarefreeComponent, squarefullComponent,
    Finsupp.prod_filter_mul_prod_filter_not]
  exact Nat.prod_factorization_pow_eq_self hn

theorem squarefree_squarefreeComponent (n : ℕ) :
    Squarefree (squarefreeComponent n) := by
  apply Nat.squarefree_of_factorization_le_one
  · unfold squarefreeComponent
    apply Finsupp.prod_ne_zero_iff.mpr
    intro p hp
    have hpsupport : p ∈ n.factorization.support :=
      Finsupp.support_mono (squarefreeFactorization_le n) hp
    exact pow_ne_zero _ (Nat.prime_of_mem_primeFactors hpsupport).ne_zero
  · intro p
    rw [factorization_squarefreeComponent]
    by_cases hp : n.factorization p = 1 <;>
      simp [hp]

theorem pos_squarefreeComponent (n : ℕ) : 0 < squarefreeComponent n := by
  exact Nat.pos_of_ne_zero (squarefree_squarefreeComponent n).ne_zero

theorem pos_squarefullComponent (n : ℕ) : 0 < squarefullComponent n := by
  have hne : squarefullComponent n ≠ 0 := by
    unfold squarefullComponent
    apply Finsupp.prod_ne_zero_iff.mpr
    intro p hp
    have hpsupport : p ∈ n.factorization.support :=
      Finsupp.support_mono (squarefullFactorization_le n) hp
    exact pow_ne_zero _ (Nat.prime_of_mem_primeFactors hpsupport).ne_zero
  exact Nat.pos_of_ne_zero hne

theorem squarefull_squarefullComponent (n : ℕ) :
    Squarefull (squarefullComponent n) := by
  refine ⟨pos_squarefullComponent n, ?_⟩
  intro p hpmem
  have hp : p.Prime := Nat.prime_of_mem_primeFactors hpmem
  have hpdvd : p ∣ squarefullComponent n := Nat.dvd_of_mem_primeFactors hpmem
  have hne : squarefullComponent n ≠ 0 := (pos_squarefullComponent n).ne'
  have hone : 1 ≤ (squarefullComponent n).factorization p :=
    (hp.dvd_iff_one_le_factorization hne).mp hpdvd
  have hnotone : n.factorization p ≠ 1 := by
    intro h
    simpa [factorization_squarefullComponent, Finsupp.filter_apply, h] using hone
  have htwo : 2 ≤ n.factorization p := by
    have hone' : 1 ≤ n.factorization p := by
      simpa [factorization_squarefullComponent, Finsupp.filter_apply, hnotone] using hone
    omega
  apply (hp.pow_dvd_iff_le_factorization hne).mpr
  simpa [factorization_squarefullComponent, Finsupp.filter_apply, hnotone] using htwo

theorem coprime_components (n : ℕ) :
    Nat.Coprime (squarefreeComponent n) (squarefullComponent n) := by
  by_contra h
  obtain ⟨p, hp, hpsf, hpsfull⟩ := Nat.Prime.not_coprime_iff_dvd.mp h
  have hsfne : squarefreeComponent n ≠ 0 := (pos_squarefreeComponent n).ne'
  have hfullne : squarefullComponent n ≠ 0 := (pos_squarefullComponent n).ne'
  have hsfac : 1 ≤ (squarefreeComponent n).factorization p :=
    (hp.dvd_iff_one_le_factorization hsfne).mp hpsf
  have hfullfac : 1 ≤ (squarefullComponent n).factorization p :=
    (hp.dvd_iff_one_le_factorization hfullne).mp hpsfull
  by_cases hpn : n.factorization p = 1
  · simpa [factorization_squarefullComponent, Finsupp.filter_apply, hpn] using hfullfac
  · simpa [factorization_squarefreeComponent, Finsupp.filter_apply, hpn] using hsfac

/-- A divisor of a product of the two canonical coprime components splits as
the product of one divisor of each component.  The concrete factors are gcds,
so the statement does not use a choice principle. -/
theorem divisor_split_components {n d : ℕ} (hn : n ≠ 0) (hd : d ∣ n) :
    ∃ e f : ℕ,
      e ∣ squarefreeComponent n ∧
      f ∣ squarefullComponent n ∧
      d = e * f := by
  let e := Nat.gcd d (squarefreeComponent n)
  let f := Nat.gcd d (squarefullComponent n)
  refine ⟨e, f, Nat.gcd_dvd_right _ _, Nat.gcd_dvd_right _ _, ?_⟩
  have hprod : d ∣ squarefreeComponent n * squarefullComponent n := by
    simpa [squarefreeComponent_mul_squarefullComponent hn] using hd
  exact (Nat.gcd_mul_gcd_eq_iff_dvd_mul_of_coprime (coprime_components n)).mpr hprod |>.symm

/-! ## Passing a divisor window to the logarithmic union -/

/-- If `d ∣ a` and `p*d` lies in `(y,2y]`, then the logarithmic parameter
`log y - log p` lies in Ford's divisor union `ℒ(a;log 2)`. -/
theorem log_sub_log_mem_logDivisorUnion
    {a d p y : ℕ} (ha : a ≠ 0) (hp : 0 < p) (hy : 0 < y)
    (hda : d ∣ a) (hlower : y < p * d) (hupper : p * d ≤ 2 * y) :
    Real.log (y : ℝ) - Real.log (p : ℝ) ∈
      logDivisorUnion a (Real.log 2) := by
  have hd : 0 < d := by
    by_contra hd0
    have : d = 0 := Nat.eq_zero_of_not_pos hd0
    subst d
    simp at hlower
  have hpmul : (0 : ℝ) < p := by exact_mod_cast hp
  have hymul : (0 : ℝ) < y := by exact_mod_cast hy
  have hdmul : (0 : ℝ) < d := by exact_mod_cast hd
  have hdivLower : (y : ℝ) / p < d := by
    apply (div_lt_iff₀ hpmul).mpr
    have hcast : (y : ℝ) < p * d := by exact_mod_cast hlower
    simpa [mul_comm] using hcast
  have hdivUpper : (d : ℝ) ≤ 2 * y / p := by
    apply (le_div_iff₀ hpmul).mpr
    have hcast : (p : ℝ) * d ≤ 2 * y := by exact_mod_cast hupper
    simpa [mul_comm] using hcast
  have hlogLower : Real.log (y : ℝ) - Real.log (p : ℝ) < Real.log d := by
    rw [← Real.log_div (Nat.cast_ne_zero.mpr hy.ne') (Nat.cast_ne_zero.mpr hp.ne')]
    exact Real.strictMonoOn_log (div_pos hymul hpmul) hdmul hdivLower
  have hlogUpper : Real.log (d : ℝ) ≤
      Real.log 2 + (Real.log (y : ℝ) - Real.log (p : ℝ)) := by
    have hposTwoYDiv : (0 : ℝ) < 2 * y / p := by positivity
    have hmono := Real.strictMonoOn_log.monotoneOn hdmul hposTwoYDiv hdivUpper
    calc
      Real.log (d : ℝ) ≤ Real.log (2 * (y : ℝ) / p) := hmono
      _ = Real.log 2 + (Real.log (y : ℝ) - Real.log (p : ℝ)) := by
        rw [Real.log_div (by positivity) (Nat.cast_ne_zero.mpr hp.ne'),
          Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) (Nat.cast_ne_zero.mpr hy.ne')]
        ring
  apply mem_logDivisorUnion.mpr
  refine ⟨d, Nat.mem_divisors.mpr ⟨hda, ha⟩, ?_, hlogLower⟩
  linarith

/-- The complementary factor in Ford's local dyadic argument can occupy an
interval of ratio four.  Splitting it at the midpoint shows that one of the
two translates (`c=1` or `c=2`) belongs to `ℒ(a;log 2)`. -/
theorem exists_one_or_two_log_mem_logDivisorUnion
    {a d p y : ℕ} (ha : a ≠ 0) (hp : 0 < p) (hy : 0 < y)
    (hda : d ∣ a) (hlower : y < p * d) (hupper : p * d ≤ 4 * y) :
    ∃ c ∈ ({1, 2} : Finset ℕ),
      Real.log (c * y : ℕ) - Real.log (p : ℕ) ∈
        logDivisorUnion a (Real.log 2) := by
  by_cases hmid : p * d ≤ 2 * y
  · refine ⟨1, by simp, ?_⟩
    simpa using log_sub_log_mem_logDivisorUnion ha hp hy hda hlower hmid
  · refine ⟨2, by simp, ?_⟩
    apply log_sub_log_mem_logDivisorUnion ha hp (by omega) hda
    · omega
    · omega

/-! ## The finite cover behind Ford's formula (3.2) -/

/-- Ford's finite squarefree cover.  The outer index is the squarefull part
`q`; the next index is the part `f` of a divisor which lies in `q`; and the
innermost squarefree number has a divisor in `(y/f,z/f]`.  Multiplication by
`q` reconstructs integers at the original scale. -/
def squarefreeReductionCover (x y z : ℕ) : Finset ℕ :=
  (squarefullSet x).biUnion fun q ↦
    q.divisors.biUnion fun f ↦
      (HStarSet (x / q) (y / f) (z / f)).image fun m ↦ m * q

theorem mem_squarefreeReductionCover_of_mem_HSet
    {x y z n : ℕ} (hn : n ∈ HSet x y z) :
    n ∈ squarefreeReductionCover x y z := by
  obtain ⟨hn1, hnx, d, hdn, hyd, hdz⟩ := mem_HSet.mp hn
  have hn0 : n ≠ 0 := Nat.one_le_iff_ne_zero.mp hn1
  obtain ⟨e, f, he, hf, hdef⟩ := divisor_split_components hn0 hdn
  let m := squarefreeComponent n
  let q := squarefullComponent n
  have hmq : m * q = n := squarefreeComponent_mul_squarefullComponent hn0
  have hmpos : 0 < m := pos_squarefreeComponent n
  have hqpos : 0 < q := pos_squarefullComponent n
  have hqdivn : q ∣ n := ⟨m, by simpa [mul_comm] using hmq.symm⟩
  have hqle : q ≤ x := (Nat.le_of_dvd hn1 hqdivn).trans hnx
  have hqmem : q ∈ squarefullSet x := by
    exact mem_squarefullSet.mpr
      ⟨hqpos, hqle, squarefull_squarefullComponent n⟩
  have hfpos : 0 < f := Nat.pos_of_dvd_of_pos hf hqpos
  have hfmem : f ∈ q.divisors := Nat.mem_divisors.mpr ⟨hf, hqpos.ne'⟩
  have hmle : m ≤ x / q := by
    apply (Nat.le_div_iff_mul_le hqpos).mpr
    simpa [hmq] using hnx
  have hmstar : m ∈ HStarSet (x / q) (y / f) (z / f) := by
    apply mem_HStarSet.mpr
    refine ⟨hmpos, hmle, squarefree_squarefreeComponent n, e, he, ?_, ?_⟩
    · apply (Nat.div_lt_iff_lt_mul hfpos).mpr
      simpa [hdef, mul_comm] using hyd
    · apply (Nat.le_div_iff_mul_le hfpos).mpr
      simpa [hdef, mul_comm] using hdz
  rw [squarefreeReductionCover]
  apply Finset.mem_biUnion.mpr
  refine ⟨q, hqmem, ?_⟩
  apply Finset.mem_biUnion.mpr
  refine ⟨f, hfmem, ?_⟩
  apply Finset.mem_image.mpr
  exact ⟨m, hmstar, hmq⟩

theorem HSet_subset_squarefreeReductionCover (x y z : ℕ) :
    HSet x y z ⊆ squarefreeReductionCover x y z := by
  intro n hn
  exact mem_squarefreeReductionCover_of_mem_HSet hn

/-- The exact finite double-sum inequality which precedes all analytic
estimates in Ford's Lemma 3.2. -/
theorem H_le_sum_squarefull_HStar (x y z : ℕ) :
    H x y z ≤
      ∑ q ∈ squarefullSet x, ∑ f ∈ q.divisors,
        HStar (x / q) (y / f) (z / f) := by
  calc
    H x y z = (HSet x y z).card := rfl
    _ ≤ (squarefreeReductionCover x y z).card :=
      Finset.card_le_card (HSet_subset_squarefreeReductionCover x y z)
    _ ≤ ∑ q ∈ squarefullSet x,
        ((q.divisors.biUnion fun f ↦
          (HStarSet (x / q) (y / f) (z / f)).image fun m ↦ m * q).card) := by
      exact Finset.card_biUnion_le
    _ ≤ ∑ q ∈ squarefullSet x, ∑ f ∈ q.divisors,
        ((HStarSet (x / q) (y / f) (z / f)).image fun m ↦ m * q).card := by
      exact Finset.sum_le_sum fun q _ ↦ Finset.card_biUnion_le
    _ ≤ ∑ q ∈ squarefullSet x, ∑ f ∈ q.divisors,
        HStar (x / q) (y / f) (z / f) := by
      exact Finset.sum_le_sum fun q _ ↦
        Finset.sum_le_sum fun f _ ↦ Finset.card_image_le

/-! ## Separating the squarefull tail -/

/-- Members of `HSet` whose canonical squarefull component exceeds `K`. -/
def largeSquarefullHSet (x y z K : ℕ) : Finset ℕ :=
  (HSet x y z).filter fun n ↦ K < squarefullComponent n

/-- A cover which forgets the divisor-window condition and retains only the
squarefull part.  Its `q`-th fibre has at most `x/q` elements. -/
def largeSquarefullCover (x K : ℕ) : Finset ℕ :=
  (squarefullTailSet x K).biUnion fun q ↦
    (Finset.Icc 1 (x / q)).image fun m ↦ m * q

theorem largeSquarefullHSet_subset_cover (x y z K : ℕ) :
    largeSquarefullHSet x y z K ⊆ largeSquarefullCover x K := by
  intro n hn
  obtain ⟨hnH, hnlarge⟩ := Finset.mem_filter.mp hn
  obtain ⟨hn1, hnx, _d, _hdn, _hyd, _hdz⟩ := mem_HSet.mp hnH
  have hn0 : n ≠ 0 := Nat.one_le_iff_ne_zero.mp hn1
  let m := squarefreeComponent n
  let q := squarefullComponent n
  have hmq : m * q = n := squarefreeComponent_mul_squarefullComponent hn0
  have hmpos : 0 < m := pos_squarefreeComponent n
  have hqpos : 0 < q := pos_squarefullComponent n
  have hqdivn : q ∣ n := ⟨m, by simpa [mul_comm] using hmq.symm⟩
  have hqle : q ≤ x := (Nat.le_of_dvd hn1 hqdivn).trans hnx
  have hqmem : q ∈ squarefullTailSet x K := by
    apply Finset.mem_filter.mpr
    exact ⟨mem_squarefullSet.mpr
      ⟨hqpos, hqle, squarefull_squarefullComponent n⟩, hnlarge⟩
  have hmle : m ≤ x / q := by
    apply (Nat.le_div_iff_mul_le hqpos).mpr
    simpa [hmq] using hnx
  rw [largeSquarefullCover]
  apply Finset.mem_biUnion.mpr
  refine ⟨q, hqmem, ?_⟩
  exact Finset.mem_image.mpr ⟨m, Finset.mem_Icc.mpr ⟨hmpos, hmle⟩, hmq⟩

/-- The exact reciprocal-squarefull tail bound used before Ford invokes the
analytic estimate `∑_{q>K,squarefull} 1/q ≪ K⁻¹²`. -/
theorem card_largeSquarefullHSet_le_sum_div (x y z K : ℕ) :
    (largeSquarefullHSet x y z K).card ≤
      ∑ q ∈ squarefullTailSet x K, x / q := by
  calc
    (largeSquarefullHSet x y z K).card ≤
        (largeSquarefullCover x K).card :=
      Finset.card_le_card (largeSquarefullHSet_subset_cover x y z K)
    _ ≤ ∑ q ∈ squarefullTailSet x K,
        ((Finset.Icc 1 (x / q)).image fun m ↦ m * q).card := by
      exact Finset.card_biUnion_le
    _ ≤ ∑ q ∈ squarefullTailSet x K,
        (Finset.Icc 1 (x / q)).card := by
      exact Finset.sum_le_sum fun q _ ↦ Finset.card_image_le
    _ = ∑ q ∈ squarefullTailSet x K, x / q := by
      apply Finset.sum_congr rfl
      intro q _
      simp

/-! ## The local `a b p` cover and its weighted sum -/

/-- The integral version of Ford's lower cut-off
`max(P⁺(a), v / a)`.  The extra `2` makes every logarithm in the analytic
estimates strictly positive. -/
noncomputable def fordLocalQ (a : ℕ) (v : ℝ) : ℕ :=
  max 2 (max (splitLargestPrime a) (Nat.ceil (v / (a : ℝ))))

/-- The finite weighted logarithmic-union sum produced by the local
arithmetic reduction. -/
noncomputable def fordLocalWeight (T : ℕ) (v : ℝ) : ℝ :=
  ∑ a ∈ squarefreeSmoothSupport 1 T,
    L a (Real.log 2) /
      ((a : ℝ) * Real.log (fordLocalQ a v : ℕ) ^ 2)

/-- Integers represented by one of Ford's local triples `a b p`.  The prime
`p` lies over a prescribed translate of `ℒ(a;log 2)`, while `b` is
`p`-rough and larger than `p`. -/
noncomputable def fordLocalCover (x T : ℕ) (v u : ℝ) : Finset ℕ := by
  classical
  exact (squarefreeSmoothSupport 1 T).biUnion fun a ↦
    (logUnionPrimes T (fordLocalQ a v) a u).biUnion fun p ↦
      ((roughNumbersUpTo (x / (a * p)) p).filter fun b ↦ p < b).image
        fun b ↦ a * b * p

/-- The upper dyadic shell of the squarefree divisor-window set. -/
def HStarDyadicShell (x y : ℕ) : Finset ℕ :=
  (HStarSet x y (2 * y)).filter fun n ↦ x / 2 < n

@[simp]
theorem mem_HStarDyadicShell {n x y : ℕ} :
    n ∈ HStarDyadicShell x y ↔
      n ∈ HStarSet x y (2 * y) ∧ x / 2 < n := by
  simp [HStarDyadicShell]

theorem fordLocalQ_two_le (a : ℕ) (v : ℝ) : 2 ≤ fordLocalQ a v := by
  exact le_max_left _ _

theorem fordLocalWeight_nonneg (T : ℕ) (v : ℝ) :
    0 ≤ fordLocalWeight T v := by
  classical
  unfold fordLocalWeight
  apply Finset.sum_nonneg
  intro a ha
  have haPos : 0 < a := by
    obtain ⟨P, _hP, hprod⟩ := mem_squarefreeSmoothSupport_iff.mp ha
    rw [← hprod]
    exact Finset.prod_pos fun p hp ↦
      (mem_primeInterval.mp (_hP hp)).1.pos
  have hlogQ : 0 < Real.log (fordLocalQ a v : ℕ) :=
    Real.log_pos (by exact_mod_cast
      (show 1 < fordLocalQ a v from lt_of_lt_of_le (by omega) (fordLocalQ_two_le a v)))
  exact div_nonneg (L_nonneg _ _) (mul_nonneg (by positivity) (sq_nonneg _))

theorem splitLargestPrime_eq_largestPrimeFactor (a : ℕ) :
    splitLargestPrime a = largestPrimeFactor a := by
  rfl

private theorem primeInterval_one_eq_primesLE (T : ℕ) :
    primeInterval 1 T = Nat.primesLE T := by
  ext p
  rw [mem_primeInterval, Nat.mem_primesLE]
  constructor
  · rintro ⟨hp, _hpOne, hpT⟩
    exact ⟨hpT, hp⟩
  · rintro ⟨hpT, hp⟩
    exact ⟨hp, hp.one_lt, hpT⟩

private theorem primeSubsetProd_injective_on (T : ℕ) :
    Set.InjOn primeSubsetProd (fordPrimeSubsets T) := by
  intro s hs t ht hst
  have hsSub : s ⊆ Nat.primesLE T := Finset.mem_powerset.mp hs
  have htSub : t ⊆ Nat.primesLE T := Finset.mem_powerset.mp ht
  rw [← Nat.primeFactors_prod (fun p hp ↦
      Nat.prime_of_mem_primesLE (hsSub hp)),
    ← Nat.primeFactors_prod (fun p hp ↦
      Nat.prime_of_mem_primesLE (htSub hp))]
  exact congrArg Nat.primeFactors hst

private theorem one_le_largestPrimeFactor (a : ℕ) :
    1 ≤ largestPrimeFactor a := by
  unfold largestPrimeFactor
  split_ifs with h
  · have hmem := Finset.max'_mem a.primeFactors h
    exact (Nat.prime_of_mem_primeFactors hmem).one_lt.le
  · rfl

/-- A local denominator is comparable with the source denominator in
`fordDenominatorSum` whenever `T ≤ 4v`, which is exactly the relation in all
three dyadic-shell terms. -/
theorem fordLocalWeight_le_denominator
    {T : ℕ} {v : ℝ} (hT : 2 ≤ T) (_hv : 0 < v)
    (hTv : (T : ℝ) ≤ 4 * v) :
    fordLocalWeight T v ≤ 16 * fordDenominatorSum T := by
  classical
  rw [fordLocalWeight, squarefreeSmoothSupport, primeInterval_one_eq_primesLE]
  rw [Finset.sum_image]
  · rw [fordDenominatorSum_eq, fordPrimeSubsets]
    calc
      (∑ s ∈ (Nat.primesLE T).powerset,
          L (∏ p ∈ s, p) (Real.log 2) /
            (((∏ p ∈ s, p : ℕ) : ℝ) *
              Real.log (fordLocalQ (∏ p ∈ s, p) v : ℕ) ^ 2)) ≤
          ∑ s ∈ (Nat.primesLE T).powerset,
            16 * fordDenominatorTerm T s := by
        apply Finset.sum_le_sum
        intro s hs
        let a := primeSubsetProd s
        let Q := fordLocalQ a v
        let R : ℝ := (largestPrimeFactor a : ℝ) + (T : ℝ) / a
        have hsSub : s ⊆ Nat.primesLE T := Finset.mem_powerset.mp hs
        have haPos : 0 < a := by
          dsimp [a, primeSubsetProd]
          exact Finset.prod_pos fun p hp ↦
            (Nat.prime_of_mem_primesLE (hsSub hp)).pos
        have haR : (0 : ℝ) < a := by exact_mod_cast haPos
        have hQ2 : 2 ≤ Q := fordLocalQ_two_le a v
        have hQR : (2 : ℝ) ≤ Q := by exact_mod_cast hQ2
        have hlogQ : 0 < Real.log (Q : ℝ) :=
          Real.log_pos (by linarith)
        have hlpfQ : (largestPrimeFactor a : ℝ) ≤ Q := by
          exact_mod_cast (le_trans (by
            rw [← splitLargestPrime_eq_largestPrimeFactor]
            exact le_max_left _ _) (le_max_right 2 _))
        have hvceil : v / (a : ℝ) ≤ (Nat.ceil (v / (a : ℝ)) : ℝ) := by
          exact_mod_cast Nat.le_ceil (v / (a : ℝ))
        have hceilQ : (Nat.ceil (v / (a : ℝ)) : ℝ) ≤ Q := by
          exact_mod_cast (le_trans (le_max_right _ _) (le_max_right 2 _))
        have hTdiv : (T : ℝ) / a ≤ 4 * Q := by
          calc
            (T : ℝ) / a ≤ (4 * v) / a :=
              div_le_div_of_nonneg_right hTv haR.le
            _ = 4 * (v / a) := by ring
            _ ≤ 4 * (Nat.ceil (v / (a : ℝ)) : ℝ) := by gcongr
            _ ≤ 4 * Q := by gcongr
        have hRQ : R ≤ 5 * Q := by
          dsimp [R]
          linarith
        have hQpow : 5 * (Q : ℝ) ≤ (Q : ℝ) ^ 4 := by
          calc
            5 * (Q : ℝ) ≤ 8 * Q := by nlinarith
            _ = (2 : ℝ) ^ 3 * Q := by norm_num
            _ ≤ (Q : ℝ) ^ 3 * Q := by gcongr
            _ = (Q : ℝ) ^ 4 := by ring
        have hRPos : 0 < R := by
          dsimp [R]
          have hlpf : (1 : ℝ) ≤ largestPrimeFactor a := by
            exact_mod_cast one_le_largestPrimeFactor a
          positivity
        have hROne : 1 < R := by
          dsimp [R]
          have hlpf : (1 : ℝ) ≤ largestPrimeFactor a := by
            exact_mod_cast one_le_largestPrimeFactor a
          have hTpos : (0 : ℝ) < (T : ℝ) / a := by positivity
          linarith
        have hlogR : 0 < Real.log R := Real.log_pos hROne
        have hlogBound : Real.log R ≤ 4 * Real.log Q := by
          calc
            Real.log R ≤ Real.log ((Q : ℝ) ^ 4) :=
              Real.strictMonoOn_log.monotoneOn hRPos
                (show (Q : ℝ) ^ 4 ∈ Set.Ioi 0 by
                  change (0 : ℝ) < (Q : ℝ) ^ 4
                  exact pow_pos (by linarith) _)
                (hRQ.trans hQpow)
            _ = 4 * Real.log Q := by rw [Real.log_pow]; norm_num
        have hsq : Real.log R ^ 2 ≤ 16 * Real.log Q ^ 2 := by
          nlinarith [sq_nonneg (4 * Real.log Q - Real.log R)]
        have hL : 0 ≤ L a (Real.log 2) := L_nonneg _ _
        change L a (Real.log 2) / ((a : ℝ) * Real.log Q ^ 2) ≤
          16 * (L a (Real.log 2) /
            ((a : ℝ) * Real.log R ^ 2))
        field_simp [haR.ne', hlogQ.ne', hlogR.ne']
        nlinarith
      _ = 16 * ∑ s ∈ (Nat.primesLE T).powerset,
          fordDenominatorTerm T s := by rw [Finset.mul_sum]
  · intro s hs t ht hst
    exact primeSubsetProd_injective_on T hs ht hst

theorem fordDenominatorSum_nonneg (T : ℕ) : 0 ≤ fordDenominatorSum T := by
  classical
  rw [fordDenominatorSum_eq]
  apply Finset.sum_nonneg
  intro s hs
  unfold fordDenominatorTerm
  exact div_nonneg (L_nonneg _ _)
    (mul_nonneg (by positivity) (sq_nonneg _))

/-- The `b` component of an `ABPSplit` is a member of the rough set at the
corresponding quotient scale. -/
theorem ABPSplit.b_mem_roughNumbersUpTo
    {n selected x : ℕ} (w : ABPSplit n selected) (hnx : n ≤ x) :
    w.b ∈ roughNumbersUpTo (x / (w.a * w.p)) w.p := by
  rw [mem_roughNumbersUpTo]
  have haPos : 0 < w.a := Nat.pos_of_ne_zero w.squarefree_a.ne_zero
  have hbPos : 0 < w.b := Nat.pos_of_ne_zero w.squarefree_b.ne_zero
  have hpPos : 0 < w.p := w.prime_p.pos
  refine ⟨hbPos, ?_, ?_⟩
  · apply (Nat.le_div_iff_mul_le (Nat.mul_pos haPos hpPos)).mpr
    calc
      w.b * (w.a * w.p) = w.a * w.b * w.p := by ring
      _ = n := w.n_eq.symm
      _ ≤ x := hnx
  · intro q hq hqp hqb
    have hqmem : q ∈ w.b.primeFactors :=
      Nat.mem_primeFactors.mpr ⟨hq, hqb, w.squarefree_b.ne_zero⟩
    have hpq := w.primes_b_gt q hqmem
    omega

/-- The squarefree `a` component belongs to Ford's finite smooth support as
soon as the distinguished prime is at most `T`. -/
theorem ABPSplit.a_mem_squarefreeSmoothSupport
    {n selected T : ℕ} (w : ABPSplit n selected) (hpT : w.p ≤ T) :
    w.a ∈ squarefreeSmoothSupport 1 T := by
  rw [mem_squarefreeSmoothSupport_iff]
  refine ⟨w.a.primeFactors, ?_, Nat.prod_primeFactors_of_squarefree w.squarefree_a⟩
  intro q hq
  rw [mem_primeInterval]
  exact ⟨Nat.prime_of_mem_primeFactors hq,
    (Nat.prime_of_mem_primeFactors hq).one_lt,
    (w.primes_a_lt q hq).le.trans hpT⟩

/-- Real-endpoint form of `ABPSplit.log_mem_logDivisorUnion`. -/
theorem ABPSplit.log_sub_log_mem_logDivisorUnion_real
    {n selected : ℕ} (w : ABPSplit n selected) {v : ℝ}
    (hv : 0 < v) (hlower : v < selected) (hupper : (selected : ℝ) ≤ 2 * v) :
    Real.log v - Real.log (w.p : ℝ) ∈
      logDivisorUnion w.a (Real.log 2) := by
  rw [mem_logDivisorUnion]
  have ha0 : w.a ≠ 0 := w.squarefree_a.ne_zero
  have hdMem : w.d ∈ w.a.divisors :=
    Nat.mem_divisors.mpr ⟨w.d_dvd_a, ha0⟩
  have hpR : (0 : ℝ) < w.p := by exact_mod_cast w.prime_p.pos
  have hdPos : 0 < w.d := by
    have hsPosR : (0 : ℝ) < selected := hv.trans hlower
    have hsPos : 0 < selected := by exact_mod_cast hsPosR
    have : 0 < w.d * w.p := by simpa [← w.selected_eq] using hsPos
    exact pos_of_mul_pos_left this (Nat.zero_le _)
  have hdR : (0 : ℝ) < w.d := by exact_mod_cast hdPos
  have hselCast : (selected : ℝ) = (w.d : ℝ) * w.p := by
    exact_mod_cast w.selected_eq
  refine ⟨w.d, hdMem, ?_, ?_⟩
  · have hlog := Real.strictMonoOn_log.monotoneOn
      (mul_pos hdR hpR) (mul_pos (show (0 : ℝ) < 2 by norm_num) hv)
      (by simpa [hselCast] using hupper)
    rw [Real.log_mul (by positivity) (by positivity),
      Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hv.ne'] at hlog
    linarith
  · have hlog := Real.strictMonoOn_log hv (mul_pos hdR hpR)
      (by simpa [hselCast] using hlower)
    rw [Real.log_mul hdR.ne' hpR.ne'] at hlog
    linarith

/-- The source lower bound `v < selected = d*p`, together with `d ∣ a`,
places `p` above the integral cut-off used in `fordLocalQ`. -/
theorem ABPSplit.fordLocalQ_le
    {n selected : ℕ} (w : ABPSplit n selected) {v : ℝ}
    (hlower : v < selected) : fordLocalQ w.a v ≤ w.p := by
  have haPos : 0 < w.a := Nat.pos_of_ne_zero w.squarefree_a.ne_zero
  have haR : (0 : ℝ) < w.a := by exact_mod_cast haPos
  have hdLe : w.d ≤ w.a := Nat.le_of_dvd haPos w.d_dvd_a
  have hselLe : selected ≤ w.a * w.p := by
    calc
      selected = w.d * w.p := w.selected_eq
      _ ≤ w.a * w.p := Nat.mul_le_mul_right w.p hdLe
  have hvap : v / (w.a : ℝ) ≤ (w.p : ℝ) := by
    rw [div_le_iff₀ haR]
    exact hlower.le.trans (by
      have : (selected : ℝ) ≤ (w.a : ℝ) * w.p := by exact_mod_cast hselLe
      simpa [mul_comm] using this)
  have hceil : Nat.ceil (v / (w.a : ℝ)) ≤ w.p :=
    Nat.ceil_le.mpr hvap
  have hlargest : splitLargestPrime w.a ≤ w.p := by
    by_cases haOne : w.a = 1
    · simp [haOne, splitLargestPrime, w.prime_p.one_lt.le]
    · have haGt : 1 < w.a := by omega
      exact (w.primes_a_lt _ (splitLargestPrime_mem haGt)).le
  simp only [fordLocalQ, max_le_iff]
  exact ⟨w.prime_p.two_le, hlargest, hceil⟩

/-- Cardinality of a local cover before applying the sieve and the
logarithmic-union prime estimate. -/
theorem card_fordLocalCover_le (x T : ℕ) (v u : ℝ) :
    (fordLocalCover x T v u).card ≤
      ∑ a ∈ squarefreeSmoothSupport 1 T,
        ∑ p ∈ logUnionPrimes T (fordLocalQ a v) a u,
          ((roughNumbersUpTo (x / (a * p)) p).filter fun b ↦ p < b).card := by
  classical
  unfold fordLocalCover
  calc
    ((squarefreeSmoothSupport 1 T).biUnion fun a ↦
        (logUnionPrimes T (fordLocalQ a v) a u).biUnion fun p ↦
          ((roughNumbersUpTo (x / (a * p)) p).filter fun b ↦ p < b).image
            fun b ↦ a * b * p).card ≤
        ∑ a ∈ squarefreeSmoothSupport 1 T,
          (((logUnionPrimes T (fordLocalQ a v) a u).biUnion fun p ↦
            ((roughNumbersUpTo (x / (a * p)) p).filter fun b ↦ p < b).image
              fun b ↦ a * b * p).card) := Finset.card_biUnion_le
    _ ≤ ∑ a ∈ squarefreeSmoothSupport 1 T,
        ∑ p ∈ logUnionPrimes T (fordLocalQ a v) a u,
          ((((roughNumbersUpTo (x / (a * p)) p).filter fun b ↦ p < b).image
            fun b ↦ a * b * p).card) := by
      exact Finset.sum_le_sum fun a _ ↦ Finset.card_biUnion_le
    _ ≤ ∑ a ∈ squarefreeSmoothSupport 1 T,
        ∑ p ∈ logUnionPrimes T (fordLocalQ a v) a u,
          ((roughNumbersUpTo (x / (a * p)) p).filter fun b ↦ p < b).card := by
      apply Finset.sum_le_sum
      intro a ha
      apply Finset.sum_le_sum
      intro p hp
      exact Finset.card_image_le

/-- An `ABPSplit` whose selected factor occupies `(v,2v]` gives membership
in the corresponding local cover. -/
theorem ABPSplit.mem_fordLocalCover
    {n selected x T : ℕ} (w : ABPSplit n selected) {v : ℝ}
    (hnx : n ≤ x) (hpT : w.p ≤ T) (hv : 0 < v)
    (hlower : v < selected) (hupper : (selected : ℝ) ≤ 2 * v) :
    n ∈ fordLocalCover x T v (Real.log v) := by
  classical
  have haMem := w.a_mem_squarefreeSmoothSupport hpT
  have hq := w.fordLocalQ_le hlower
  have hlog := w.log_sub_log_mem_logDivisorUnion_real hv hlower hupper
  have hpMem : w.p ∈
      logUnionPrimes T (fordLocalQ w.a v) w.a (Real.log v) := by
    exact mem_logUnionPrimes.mpr ⟨w.prime_p, hpT, hq, hlog⟩
  have hbMem := w.b_mem_roughNumbersUpTo hnx
  unfold fordLocalCover
  apply Finset.mem_biUnion.mpr
  refine ⟨w.a, haMem, ?_⟩
  apply Finset.mem_biUnion.mpr
  refine ⟨w.p, hpMem, ?_⟩
  apply Finset.mem_image.mpr
  refine ⟨w.b, Finset.mem_filter.mpr ⟨hbMem, w.p_lt_b⟩, ?_⟩
  exact w.n_eq.symm

/-- For the ratio-four complementary interval, splitting at its midpoint
places the integer in one of the two ratio-two local covers. -/
theorem ABPSplit.mem_fordLocalCover_ratioFour
    {n selected x T : ℕ} (w : ABPSplit n selected) {v : ℝ}
    (hnx : n ≤ x) (hpT : w.p ≤ T) (hv : 0 < v)
    (hlower : v < selected) (hupper : (selected : ℝ) ≤ 4 * v) :
    n ∈ fordLocalCover x T v (Real.log v) ∪
      fordLocalCover x T (2 * v) (Real.log (2 * v)) := by
  by_cases hmid : (selected : ℝ) ≤ 2 * v
  · exact Finset.mem_union_left _
      (w.mem_fordLocalCover hnx hpT hv hlower hmid)
  · apply Finset.mem_union_right
    apply w.mem_fordLocalCover hnx hpT (mul_pos (by norm_num) hv)
    · exact lt_of_not_ge hmid
    · nlinarith

/-- The three local covers arising from the two factors of a squarefree
integer in a dyadic `x`-shell. -/
noncomputable def fordDyadicShellCover (x y : ℕ) : Finset ℕ := by
  let v₂ : ℝ := (x : ℝ) / (4 * (y : ℝ))
  exact fordLocalCover x (2 * y) (y : ℝ) (Real.log (y : ℝ)) ∪
    (fordLocalCover x (x / y) v₂ (Real.log v₂) ∪
      fordLocalCover x (x / y) (2 * v₂) (Real.log (2 * v₂)))

/-- Source-faithful arithmetic cover for Ford's local estimate (3.3). -/
theorem HStarDyadicShell_subset_fordDyadicShellCover
    {x y : ℕ} (hy : 3 ≤ y) (hxy : 8 * y ≤ x) :
    HStarDyadicShell x y ⊆ fordDyadicShellCover x y := by
  classical
  intro n hn
  obtain ⟨hnStar, hnHalf⟩ := mem_HStarDyadicShell.mp hn
  obtain ⟨hnPos, hnx, hnSq, d, hdn, hyd, hd2y⟩ := mem_HStarSet.mp hnStar
  let e := n / d
  have hdPos : 0 < d := Nat.pos_of_dvd_of_pos hdn hnPos
  have hde : d * e = n := by
    exact Nat.mul_div_cancel' hdn
  have hdGt : 1 < d := by omega
  have hePos : 0 < e := by
    by_contra he0
    have : e = 0 := Nat.eq_zero_of_not_pos he0
    rw [this, Nat.mul_zero] at hde
    omega
  have hfouryHalf : 4 * y ≤ x / 2 := by
    apply (Nat.le_div_iff_mul_le (by norm_num : 0 < 2)).mpr
    nlinarith
  have heGt : 1 < e := by
    by_contra he1
    have heEq : e = 1 := by omega
    have hnEq : n = d := by simpa [heEq] using hde.symm
    omega
  have habp := abpSplit_of_squarefree_factorization hnSq hde hdGt heGt
  have hyR : (0 : ℝ) < (y : ℝ) := by positivity
  have hxPos : 0 < x := by omega
  have hxR : (0 : ℝ) < (x : ℝ) := by exact_mod_cast hxPos
  have heYle : e * y ≤ x := by
    have : e * y < e * d := (Nat.mul_lt_mul_left hePos).2 hyd
    calc
      e * y ≤ e * d := this.le
      _ = n := by simpa [mul_comm] using hde
      _ ≤ x := hnx
  have heLe : e ≤ x / y := by
    apply (Nat.le_div_iff_mul_le (by omega : 0 < y)).mpr
    simpa [mul_comm] using heYle
  have hv₂pos : (0 : ℝ) < (x : ℝ) / (4 * (y : ℝ)) := by positivity
  have hv₂lower : (x : ℝ) / (4 * (y : ℝ)) < (e : ℝ) := by
    have hnHalfR : (x : ℝ) / 2 < n := by
      have hxmod : x ≤ 2 * (x / 2) + 1 := by omega
      have hnNat : x < 2 * n := by omega
      exact (div_lt_iff₀ (by norm_num : (0 : ℝ) < 2)).mpr (by
        have : (x : ℝ) < 2 * n := by exact_mod_cast hnNat
        simpa [mul_comm] using this)
    have hdR : (d : ℝ) ≤ 2 * y := by exact_mod_cast hd2y
    have hdeR : (n : ℝ) = d * e := by exact_mod_cast hde.symm
    rw [hdeR] at hnHalfR
    apply (div_lt_iff₀ (mul_pos (by norm_num) hyR)).mpr
    nlinarith [show (0 : ℝ) ≤ e by positivity]
  have hv₂upper : (e : ℝ) ≤ 4 * ((x : ℝ) / (4 * (y : ℝ))) := by
    have heYR : (e : ℝ) * y ≤ x := by exact_mod_cast heYle
    field_simp [hyR.ne']
    nlinarith
  rcases habp with hleft | hright
  · obtain ⟨w⟩ := hleft
    have hpT : w.p ≤ 2 * y :=
      (Nat.le_of_dvd (by omega : 0 < d)
        ⟨w.d, by simpa [mul_comm] using w.selected_eq⟩).trans hd2y
    have hmem := w.mem_fordLocalCover hnx hpT hyR
      (by exact_mod_cast hyd) (by exact_mod_cast hd2y)
    exact Finset.mem_union_left _ hmem
  · obtain ⟨w⟩ := hright
    have hpE : w.p ≤ e :=
      Nat.le_of_dvd hePos ⟨w.d, by simpa [mul_comm] using w.selected_eq⟩
    have hmem := w.mem_fordLocalCover_ratioFour hnx (hpE.trans heLe)
      hv₂pos hv₂lower hv₂upper
    exact Finset.mem_union_right _ hmem

/-- Pure cardinal form of the preceding shell cover. -/
theorem card_HStarDyadicShell_le_localCovers
    {x y : ℕ} (hy : 3 ≤ y) (hxy : 8 * y ≤ x) :
    (HStarDyadicShell x y).card ≤
      (fordLocalCover x (2 * y) (y : ℝ) (Real.log (y : ℝ))).card +
      (fordLocalCover x (x / y) ((x : ℝ) / (4 * y))
        (Real.log ((x : ℝ) / (4 * y)))).card +
      (fordLocalCover x (x / y) (2 * ((x : ℝ) / (4 * y)))
        (Real.log (2 * ((x : ℝ) / (4 * y))))).card := by
  calc
    (HStarDyadicShell x y).card ≤ (fordDyadicShellCover x y).card :=
      Finset.card_le_card (HStarDyadicShell_subset_fordDyadicShellCover hy hxy)
    _ ≤ (fordLocalCover x (2 * y) (y : ℝ) (Real.log (y : ℝ))).card +
        ((fordLocalCover x (x / y) ((x : ℝ) / (4 * y))
          (Real.log ((x : ℝ) / (4 * y))) ∪
        fordLocalCover x (x / y) (2 * ((x : ℝ) / (4 * y)))
          (Real.log (2 * ((x : ℝ) / (4 * y))))).card) := by
      exact Finset.card_union_le _ _
    _ ≤ (fordLocalCover x (2 * y) (y : ℝ) (Real.log (y : ℝ))).card +
        (fordLocalCover x (x / y) ((x : ℝ) / (4 * y))
          (Real.log ((x : ℝ) / (4 * y)))).card +
        (fordLocalCover x (x / y) (2 * ((x : ℝ) / (4 * y)))
          (Real.log (2 * ((x : ℝ) / (4 * y))))).card := by
      simpa [Nat.add_assoc] using Nat.add_le_add_left
        (Finset.card_union_le
          (fordLocalCover x (x / y) ((x : ℝ) / (4 * y))
            (Real.log ((x : ℝ) / (4 * y))))
          (fordLocalCover x (x / y) (2 * ((x : ℝ) / (4 * y)))
            (Real.log (2 * ((x : ℝ) / (4 * y))))))
        (fordLocalCover x (2 * y) (y : ℝ) (Real.log (y : ℝ))).card

private theorem pos_of_mem_squarefreeSmoothSupport
    {a s T : ℕ} (ha : a ∈ squarefreeSmoothSupport s T) : 0 < a := by
  obtain ⟨P, hP, hprod⟩ := mem_squarefreeSmoothSupport_iff.mp ha
  rw [← hprod]
  exact Finset.prod_pos fun p hp ↦ (mem_primeInterval.mp (hP hp)).1.pos

/-- Analytic estimate for one local cover, assuming a uniform rough-number
bound.  This is the exact composition of the sieve with
`sum_inv_logUnionPrimes_le`. -/
theorem card_fordLocalCover_le_weight_of_rough
    {C : ℝ} (hC : 0 ≤ C)
    (hrough : ∀ X z : ℕ, 2 ≤ z →
      (((roughNumbersUpTo X z).filter fun b ↦ z < b).card : ℝ) ≤
        C * (X : ℝ) / Real.log z)
    (x T : ℕ) (v u : ℝ) :
    ((fordLocalCover x T v u).card : ℝ) ≤
      (C * (4 * Real.log 4 / Real.log 2)) * (x : ℝ) *
        fordLocalWeight T v := by
  classical
  have hcardNat := card_fordLocalCover_le x T v u
  have hcard : ((fordLocalCover x T v u).card : ℝ) ≤
      ∑ a ∈ squarefreeSmoothSupport 1 T,
        ∑ p ∈ logUnionPrimes T (fordLocalQ a v) a u,
          (((roughNumbersUpTo (x / (a * p)) p).filter fun b ↦ p < b).card : ℝ) := by
    exact_mod_cast hcardNat
  calc
    ((fordLocalCover x T v u).card : ℝ) ≤
        ∑ a ∈ squarefreeSmoothSupport 1 T,
          ∑ p ∈ logUnionPrimes T (fordLocalQ a v) a u,
            (((roughNumbersUpTo (x / (a * p)) p).filter fun b ↦ p < b).card : ℝ) := hcard
    _ ≤ ∑ a ∈ squarefreeSmoothSupport 1 T,
        ((C * (4 * Real.log 4 / Real.log 2)) * (x : ℝ) *
          (L a (Real.log 2) /
            ((a : ℝ) * Real.log (fordLocalQ a v : ℕ) ^ 2))) := by
      apply Finset.sum_le_sum
      intro a ha
      have haPos := pos_of_mem_squarefreeSmoothSupport ha
      have haR : (0 : ℝ) < a := by exact_mod_cast haPos
      let Q := fordLocalQ a v
      have hQ2 : 2 ≤ Q := fordLocalQ_two_le a v
      have hlogQ : 0 < Real.log (Q : ℝ) :=
        Real.log_pos (by exact_mod_cast (show 1 < Q by omega))
      let A : ℝ := C * (x : ℝ) / (a : ℝ) / Real.log Q
      have hA : 0 ≤ A := by dsimp [A]; positivity
      calc
        (∑ p ∈ logUnionPrimes T Q a u,
            (((roughNumbersUpTo (x / (a * p)) p).filter fun b ↦ p < b).card : ℝ)) ≤
            ∑ p ∈ logUnionPrimes T Q a u, A * (p : ℝ)⁻¹ := by
          apply Finset.sum_le_sum
          intro p hp
          have hpData := mem_logUnionPrimes.mp hp
          have hpR : (0 : ℝ) < p := by exact_mod_cast hpData.1.pos
          have hlogp : 0 < Real.log (p : ℝ) :=
            Real.log_pos (by exact_mod_cast hpData.1.one_lt)
          have hlogLe : Real.log (Q : ℝ) ≤ Real.log (p : ℝ) :=
            Real.strictMonoOn_log.monotoneOn
              (show (Q : ℝ) ∈ Set.Ioi 0 by
                change (0 : ℝ) < (Q : ℝ)
                exact_mod_cast (show 0 < Q by omega)) hpR
              (by exact_mod_cast hpData.2.2.1)
          calc
            (((roughNumbersUpTo (x / (a * p)) p).filter fun b ↦ p < b).card : ℝ) ≤
                C * ((x / (a * p) : ℕ) : ℝ) / Real.log p :=
              hrough _ _ hpData.1.two_le
            _ ≤ C * ((x : ℝ) / ((a * p : ℕ) : ℝ)) / Real.log p := by
              gcongr
              exact Nat.cast_div_le
            _ ≤ C * ((x : ℝ) / ((a * p : ℕ) : ℝ)) / Real.log Q := by
              exact div_le_div_of_nonneg_left (by positivity) hlogQ hlogLe
            _ = A * (p : ℝ)⁻¹ := by
              dsimp [A]
              push_cast
              field_simp [haR.ne', hpR.ne', hlogQ.ne']
        _ = A * ∑ p ∈ logUnionPrimes T Q a u, (p : ℝ)⁻¹ := by
          rw [Finset.mul_sum]
        _ ≤ A * ((4 * Real.log 4 / Real.log 2) *
            L a (Real.log 2) / Real.log Q) := by
          exact mul_le_mul_of_nonneg_left
            (sum_inv_logUnionPrimes_le T Q a u haPos hQ2) hA
        _ = (C * (4 * Real.log 4 / Real.log 2)) * (x : ℝ) *
            (L a (Real.log 2) /
              ((a : ℝ) * Real.log (fordLocalQ a v : ℕ) ^ 2)) := by
          dsimp [A, Q]
          field_simp [haR.ne', hlogQ.ne']
    _ = (C * (4 * Real.log 4 / Real.log 2)) * (x : ℝ) *
        fordLocalWeight T v := by
      rw [fordLocalWeight]
      rw [Finset.mul_sum]

private theorem card_roughAbove_le (X z : ℕ) :
    ((roughNumbersUpTo X z).filter fun b ↦ z < b).card ≤ X := by
  classical
  calc
    ((roughNumbersUpTo X z).filter fun b ↦ z < b).card ≤
        (roughNumbersUpTo X z).card := Finset.card_filter_le _ _
    _ ≤ (Finset.Icc 1 X).card := by
      unfold roughNumbersUpTo
      exact Finset.card_filter_le _ _
    _ ≤ X := by simp

/-- Uniform all-scale rough-number estimate in the precise filtered form
used by `fordLocalCover`.  The large-prime range is Selberg's sieve; the
finitely many smaller primes are absorbed into the constant. -/
theorem exists_roughAbove_card_le_div_log :
    ∃ C : ℝ, 0 < C ∧ ∀ X z : ℕ, 2 ≤ z →
      (((roughNumbersUpTo X z).filter fun b ↦ z < b).card : ℝ) ≤
        C * (X : ℝ) / Real.log z := by
  obtain ⟨C₀, hC₀, N₀, hsieve⟩ :=
    exists_roughNumbersUpTo_card_le_div_log
  let M := max N₀ 3
  let C := C₀ + Real.log M
  have hM3 : 3 ≤ M := le_max_right _ _
  have hlogM : 0 < Real.log (M : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < M by omega))
  have hC : 0 < C := by dsimp [C]; linarith
  refine ⟨C, hC, ?_⟩
  intro X z hz
  have hzPos : 0 < z := by omega
  have hlogz : 0 < Real.log (z : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < z by omega))
  by_cases hzM : M ≤ z
  · by_cases hzX : z ≤ X
    · have hbase := hsieve (X := X) (z := z)
          ((le_max_left N₀ 3).trans hzM) hzX
      have hsub :
          (((roughNumbersUpTo X z).filter fun b ↦ z < b).card : ℝ) ≤
            ((roughNumbersUpTo X z).card : ℝ) := by
        exact_mod_cast Finset.card_filter_le (roughNumbersUpTo X z) (fun b ↦ z < b)
      calc
        (((roughNumbersUpTo X z).filter fun b ↦ z < b).card : ℝ) ≤
            ((roughNumbersUpTo X z).card : ℝ) := hsub
        _ ≤ C₀ * (X : ℝ) / Real.log z := hbase
        _ ≤ C * (X : ℝ) / Real.log z := by
          have hC₀C : C₀ ≤ C := by dsimp [C]; linarith
          exact div_le_div_of_nonneg_right
            (mul_le_mul_of_nonneg_right hC₀C (by positivity)) hlogz.le
    · have hempty :
          (roughNumbersUpTo X z).filter (fun b ↦ z < b) = ∅ := by
        ext b
        simp only [Finset.mem_filter, mem_roughNumbersUpTo, Finset.notMem_empty,
          iff_false, not_and_or]
        omega
      rw [hempty]
      simp only [Finset.card_empty, Nat.cast_zero]
      exact div_nonneg (mul_nonneg hC.le (by positivity)) hlogz.le
  · have hzLeM : z ≤ M := by omega
    have hlogLe : Real.log (z : ℝ) ≤ Real.log (M : ℝ) :=
      Real.strictMonoOn_log.monotoneOn
        (show (z : ℝ) ∈ Set.Ioi 0 by change (0 : ℝ) < z; positivity)
        (show (M : ℝ) ∈ Set.Ioi 0 by change (0 : ℝ) < M; positivity)
        (by exact_mod_cast hzLeM)
    have hcard := card_roughAbove_le X z
    have hcardR :
        (((roughNumbersUpTo X z).filter fun b ↦ z < b).card : ℝ) ≤ X := by
      exact_mod_cast hcard
    calc
      (((roughNumbersUpTo X z).filter fun b ↦ z < b).card : ℝ) ≤ (X : ℝ) := hcardR
      _ ≤ C * (X : ℝ) / Real.log z := by
        rw [le_div_iff₀ hlogz]
        have hlogC : Real.log (z : ℝ) ≤ C := by
          dsimp [C]
          linarith
        nlinarith [show (0 : ℝ) ≤ X by positivity]

/-- The weighted sum naturally attached to a dyadic squarefree shell. -/
noncomputable def fordDyadicShellWeight (x y : ℕ) : ℝ :=
  let v₂ : ℝ := (x : ℝ) / (4 * (y : ℝ))
  fordLocalWeight (2 * y) (y : ℝ) +
    fordLocalWeight (x / y) v₂ +
    fordLocalWeight (x / y) (2 * v₂)

theorem fordDyadicShellWeight_nonneg (x y : ℕ) :
    0 ≤ fordDyadicShellWeight x y := by
  dsimp [fordDyadicShellWeight]
  exact add_nonneg
    (add_nonneg (fordLocalWeight_nonneg _ _) (fordLocalWeight_nonneg _ _))
    (fordLocalWeight_nonneg _ _)

/-- The denominator sum needed for one dyadic shell. -/
noncomputable def fordDyadicDenominatorWeight (x y : ℕ) : ℝ :=
  fordDenominatorSum (2 * y) + 2 * fordDenominatorSum (x / y)

theorem fordDyadicDenominatorWeight_nonneg (x y : ℕ) :
    0 ≤ fordDyadicDenominatorWeight x y := by
  unfold fordDyadicDenominatorWeight
  exact add_nonneg (fordDenominatorSum_nonneg _)
    (mul_nonneg (by norm_num) (fordDenominatorSum_nonneg _))

/-- Clean bridge from the three source-local sums in a dyadic shell to the
public denominator sum of `Denominator.lean`. -/
theorem fordDyadicShellWeight_le_denominator
    {x y : ℕ} (hy : 3 ≤ y) (hxy : 8 * y ≤ x) :
    fordDyadicShellWeight x y ≤
      16 * fordDyadicDenominatorWeight x y := by
  have hyPos : 0 < y := by omega
  have hyR : (0 : ℝ) < y := by exact_mod_cast hyPos
  have hxPos : 0 < x := by omega
  have hxR : (0 : ℝ) < x := by exact_mod_cast hxPos
  have hT₂ : 2 ≤ x / y := by
    apply (Nat.le_div_iff_mul_le hyPos).mpr
    omega
  let v₂ : ℝ := (x : ℝ) / (4 * (y : ℝ))
  have hv₂ : 0 < v₂ := by dsimp [v₂]; positivity
  have hTv₂ : ((x / y : ℕ) : ℝ) ≤ 4 * v₂ := by
    calc
      ((x / y : ℕ) : ℝ) ≤ (x : ℝ) / y := Nat.cast_div_le
      _ = 4 * v₂ := by
        dsimp [v₂]
        field_simp [hyR.ne']
  have h₁ := fordLocalWeight_le_denominator (T := 2 * y) (v := (y : ℝ))
    (by omega) hyR (by norm_num; linarith)
  have h₂ := fordLocalWeight_le_denominator (T := x / y) (v := v₂)
    hT₂ hv₂ hTv₂
  have h₃ := fordLocalWeight_le_denominator (T := x / y) (v := 2 * v₂)
    hT₂ (by positivity) (hTv₂.trans (by nlinarith))
  dsimp [fordDyadicShellWeight, fordDyadicDenominatorWeight, v₂]
  linarith

/-- Full local form of Ford's Lemma 3.2: the cardinality of one dyadic
squarefree shell is at most an absolute constant times `x` times its
weighted logarithmic-union sum. -/
theorem exists_card_HStarDyadicShell_le_weight :
    ∃ C : ℝ, 0 < C ∧ ∀ {x y : ℕ}, 3 ≤ y → 8 * y ≤ x →
      ((HStarDyadicShell x y).card : ℝ) ≤
        C * (x : ℝ) * fordDyadicShellWeight x y := by
  obtain ⟨C₀, hC₀, hrough⟩ := exists_roughAbove_card_le_div_log
  let K : ℝ := 4 * Real.log 4 / Real.log 2
  let C := C₀ * K
  have hK : 0 < K := by dsimp [K]; positivity
  have hC : 0 < C := mul_pos hC₀ hK
  refine ⟨C, hC, ?_⟩
  intro x y hy hxy
  have hcard := card_HStarDyadicShell_le_localCovers hy hxy
  have hcardR : ((HStarDyadicShell x y).card : ℝ) ≤
      ((fordLocalCover x (2 * y) (y : ℝ) (Real.log (y : ℝ))).card : ℝ) +
      ((fordLocalCover x (x / y) ((x : ℝ) / (4 * y))
        (Real.log ((x : ℝ) / (4 * y)))).card : ℝ) +
      ((fordLocalCover x (x / y) (2 * ((x : ℝ) / (4 * y)))
        (Real.log (2 * ((x : ℝ) / (4 * y))))).card : ℝ) := by
    exact_mod_cast hcard
  have h₁ := card_fordLocalCover_le_weight_of_rough hC₀.le hrough
    x (2 * y) (y : ℝ) (Real.log (y : ℝ))
  have h₂ := card_fordLocalCover_le_weight_of_rough hC₀.le hrough
    x (x / y) ((x : ℝ) / (4 * y)) (Real.log ((x : ℝ) / (4 * y)))
  have h₃ := card_fordLocalCover_le_weight_of_rough hC₀.le hrough
    x (x / y) (2 * ((x : ℝ) / (4 * y)))
      (Real.log (2 * ((x : ℝ) / (4 * y))))
  calc
    ((HStarDyadicShell x y).card : ℝ) ≤ _ := hcardR
    _ ≤ (C₀ * K) * (x : ℝ) * fordLocalWeight (2 * y) (y : ℝ) +
        (C₀ * K) * (x : ℝ) * fordLocalWeight (x / y) ((x : ℝ) / (4 * y)) +
        (C₀ * K) * (x : ℝ) *
          fordLocalWeight (x / y) (2 * ((x : ℝ) / (4 * y))) := by
      exact add_le_add (add_le_add (by simpa [K] using h₁) (by simpa [K] using h₂))
        (by simpa [K] using h₃)
    _ = C * (x : ℝ) * fordDyadicShellWeight x y := by
      simp only [fordDyadicShellWeight]
      dsimp [C]
      ring

/-! ## Dyadic assembly and the full `H` reduction -/

/-- Dyadic cover of a squarefree divisor-window set.  Scales below `8y`
are collected in the first interval; all remaining integers lie in a
genuine upper dyadic shell. -/
def fordHStarDyadicCover (x y : ℕ) : Finset ℕ :=
  Finset.Icc 1 (8 * y) ∪
    ((Finset.range (x + 1)).filter fun k ↦ 8 * y ≤ x / 2 ^ k).biUnion
      fun k ↦ HStarDyadicShell (x / 2 ^ k) y

private theorem index_le_two_pow (k : ℕ) : k ≤ 2 ^ k := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [pow_succ]
      have hpowPos : 0 < (2 : ℕ) ^ k := pow_pos (by norm_num) _
      omega

theorem HStarSet_subset_fordHStarDyadicCover (x y : ℕ) :
    HStarSet x y (2 * y) ⊆ fordHStarDyadicCover x y := by
  classical
  intro n hn
  obtain ⟨hnPos, hnx, hnSq, d, hdn, hyd, hd2y⟩ := mem_HStarSet.mp hn
  by_cases hnSmall : n ≤ 8 * y
  · exact Finset.mem_union_left _ (Finset.mem_Icc.mpr ⟨hnPos, hnSmall⟩)
  · apply Finset.mem_union_right
    let q := x / n
    let k := Nat.log2 q
    have hqPos : 0 < q := by
      apply Nat.div_pos
      · exact hnx
      · exact hnPos
    have hq0 : q ≠ 0 := hqPos.ne'
    have hpowLeQ : 2 ^ k ≤ q := by
      exact Nat.log2_self_le hq0
    have hqUpper : q < 2 ^ (k + 1) := by
      simpa [pow_succ, mul_comm] using Nat.lt_log2_self (n := q)
    have hqLeX : q ≤ x := Nat.div_le_self _ _
    have hkLeX : k ≤ x := (index_le_two_pow k).trans (hpowLeQ.trans hqLeX)
    have hkMem : k ∈
        (Finset.range (x + 1)).filter (fun r ↦ 8 * y ≤ x / 2 ^ r) := by
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_range.mpr (by omega), ?_⟩
      have hnScale : n ≤ x / 2 ^ k := by
        apply (Nat.le_div_iff_mul_le (pow_pos (by norm_num) _)).mpr
        have hmul : 2 ^ k * n ≤ q * n := Nat.mul_le_mul_right n hpowLeQ
        simpa [mul_comm] using hmul.trans (Nat.div_mul_le_self x n)
      have hnLarge : 8 * y ≤ n := by omega
      exact hnLarge.trans hnScale
    apply Finset.mem_biUnion.mpr
    refine ⟨k, hkMem, ?_⟩
    apply mem_HStarDyadicShell.mpr
    constructor
    · apply mem_HStarSet.mpr
      refine ⟨hnPos, ?_, hnSq, d, hdn, hyd, hd2y⟩
      apply (Nat.le_div_iff_mul_le (pow_pos (by norm_num) _)).mpr
      have hmul : 2 ^ k * n ≤ q * n := Nat.mul_le_mul_right n hpowLeQ
      simpa [mul_comm] using hmul.trans (Nat.div_mul_le_self x n)
    · have hxlt : x < 2 ^ (k + 1) * n := by
        exact (Nat.div_lt_iff_lt_mul hnPos).mp hqUpper
      have hdivlt : x / 2 ^ (k + 1) < n := by
        apply (Nat.div_lt_iff_lt_mul (pow_pos (by norm_num) _)).mpr
        simpa [mul_comm] using hxlt
      rw [show x / 2 ^ k / 2 = x / 2 ^ (k + 1) by
        rw [Nat.div_div_eq_div_mul, pow_succ]]
      exact hdivlt

theorem card_HStarSet_le_dyadicShells (x y : ℕ) :
    (HStarSet x y (2 * y)).card ≤
      8 * y +
        ∑ k ∈ (Finset.range (x + 1)).filter (fun k ↦ 8 * y ≤ x / 2 ^ k),
          (HStarDyadicShell (x / 2 ^ k) y).card := by
  calc
    (HStarSet x y (2 * y)).card ≤ (fordHStarDyadicCover x y).card :=
      Finset.card_le_card (HStarSet_subset_fordHStarDyadicCover x y)
    _ ≤ (Finset.Icc 1 (8 * y)).card +
        (((Finset.range (x + 1)).filter fun k ↦ 8 * y ≤ x / 2 ^ k).biUnion
          fun k ↦ HStarDyadicShell (x / 2 ^ k) y).card := Finset.card_union_le _ _
    _ ≤ 8 * y +
        ∑ k ∈ (Finset.range (x + 1)).filter (fun k ↦ 8 * y ≤ x / 2 ^ k),
          (HStarDyadicShell (x / 2 ^ k) y).card := by
      gcongr
      · simp
      · exact Finset.card_biUnion_le

private theorem HStar_le_x (x y : ℕ) : HStar x y (2 * y) ≤ x := by
  calc
    HStar x y (2 * y) ≤ H x y (2 * y) := HStar_le_H _ _ _
    _ = (HSet x y (2 * y)).card := rfl
    _ ≤ (Finset.Icc 1 x).card := by
      apply Finset.card_le_card
      intro n hn
      obtain ⟨hn1, hnx, _⟩ := mem_HSet.mp hn
      exact Finset.mem_Icc.mpr ⟨hn1, hnx⟩
    _ ≤ x := by simp

/-- Complete finite weight after dyadic assembly.  Outside the analytic
range the value `1` records the elementary bound `H* ≤ x`. -/
noncomputable def fordHStarReductionWeight (x y : ℕ) : ℝ :=
  if 3 ≤ y ∧ 8 * y ≤ x then
    (8 * y : ℕ) / (x : ℝ) +
      ∑ k ∈ (Finset.range (x + 1)).filter (fun k ↦ 8 * y ≤ x / 2 ^ k),
        (((x / 2 ^ k : ℕ) : ℝ) / (x : ℝ)) *
          fordDyadicShellWeight (x / 2 ^ k) y
  else 1

theorem fordHStarReductionWeight_nonneg (x y : ℕ) :
    0 ≤ fordHStarReductionWeight x y := by
  classical
  unfold fordHStarReductionWeight
  split_ifs with h
  · exact add_nonneg (by positivity)
      (Finset.sum_nonneg fun k hk ↦ mul_nonneg (by positivity)
        (fordDyadicShellWeight_nonneg _ _))
  · norm_num

/-- Denominator-sum version of `fordHStarReductionWeight`. -/
noncomputable def fordHStarDenominatorWeight (x y : ℕ) : ℝ :=
  if 3 ≤ y ∧ 8 * y ≤ x then
    (8 * y : ℕ) / (x : ℝ) +
      ∑ k ∈ (Finset.range (x + 1)).filter (fun k ↦ 8 * y ≤ x / 2 ^ k),
        (((x / 2 ^ k : ℕ) : ℝ) / (x : ℝ)) *
          fordDyadicDenominatorWeight (x / 2 ^ k) y
  else 1

theorem fordHStarDenominatorWeight_nonneg (x y : ℕ) :
    0 ≤ fordHStarDenominatorWeight x y := by
  classical
  unfold fordHStarDenominatorWeight
  split_ifs with h
  · exact add_nonneg (by positivity)
      (Finset.sum_nonneg fun k hk ↦ mul_nonneg (by positivity)
        (fordDyadicDenominatorWeight_nonneg _ _))
  · norm_num

/-- Consumer-facing denominator bridge for the entire dyadic squarefree
assembly. -/
theorem fordHStarReductionWeight_le_denominatorWeight (x y : ℕ) :
    fordHStarReductionWeight x y ≤
      16 * fordHStarDenominatorWeight x y := by
  classical
  by_cases hrange : 3 ≤ y ∧ 8 * y ≤ x
  · rw [fordHStarReductionWeight, if_pos hrange,
      fordHStarDenominatorWeight, if_pos hrange, mul_add, Finset.mul_sum]
    apply add_le_add
    · have hbase : 0 ≤ ((8 * y : ℕ) : ℝ) / (x : ℝ) := by positivity
      nlinarith
    · apply Finset.sum_le_sum
      intro k hk
      have hcoeff : 0 ≤ ((x / 2 ^ k : ℕ) : ℝ) / (x : ℝ) := by positivity
      have hs := fordDyadicShellWeight_le_denominator hrange.1
        (Finset.mem_filter.mp hk).2
      calc
        ((x / 2 ^ k : ℕ) : ℝ) / (x : ℝ) *
            fordDyadicShellWeight (x / 2 ^ k) y ≤
          ((x / 2 ^ k : ℕ) : ℝ) / (x : ℝ) *
            (16 * fordDyadicDenominatorWeight (x / 2 ^ k) y) :=
          mul_le_mul_of_nonneg_left hs hcoeff
        _ = 16 * (((x / 2 ^ k : ℕ) : ℝ) / (x : ℝ) *
            fordDyadicDenominatorWeight (x / 2 ^ k) y) := by ring
  · rw [fordHStarReductionWeight, if_neg hrange,
      fordHStarDenominatorWeight, if_neg hrange]
    norm_num

/-- Dyadic assembly of the local weighted reduction, valid at every natural
scale. -/
theorem exists_HStar_le_reductionWeight :
    ∃ C : ℝ, 0 < C ∧ ∀ x y : ℕ,
      (HStar x y (2 * y) : ℝ) ≤
        C * (x : ℝ) * fordHStarReductionWeight x y := by
  obtain ⟨C₀, hC₀, hshell⟩ := exists_card_HStarDyadicShell_le_weight
  let C := max 1 C₀
  have hC : 0 < C := lt_of_lt_of_le (by norm_num) (le_max_left _ _)
  have hC₀C : C₀ ≤ C := le_max_right _ _
  refine ⟨C, hC, ?_⟩
  intro x y
  by_cases hrange : 3 ≤ y ∧ 8 * y ≤ x
  · have hxPos : 0 < x := by omega
    have hxR : (0 : ℝ) < x := by exact_mod_cast hxPos
    have hcard := card_HStarSet_le_dyadicShells x y
    have hcardR : (HStar x y (2 * y) : ℝ) ≤
        (8 * y : ℕ) +
          ∑ k ∈ (Finset.range (x + 1)).filter (fun k ↦ 8 * y ≤ x / 2 ^ k),
            ((HStarDyadicShell (x / 2 ^ k) y).card : ℝ) := by
      exact_mod_cast hcard
    calc
      (HStar x y (2 * y) : ℝ) ≤ _ := hcardR
      _ ≤ (8 * y : ℕ) +
          ∑ k ∈ (Finset.range (x + 1)).filter (fun k ↦ 8 * y ≤ x / 2 ^ k),
            C₀ * ((x / 2 ^ k : ℕ) : ℝ) *
              fordDyadicShellWeight (x / 2 ^ k) y := by
        gcongr with k hk
        exact hshell hrange.1 (Finset.mem_filter.mp hk).2
      _ ≤ C * (x : ℝ) * ((8 * y : ℕ) / (x : ℝ) +
          ∑ k ∈ (Finset.range (x + 1)).filter (fun k ↦ 8 * y ≤ x / 2 ^ k),
            (((x / 2 ^ k : ℕ) : ℝ) / (x : ℝ)) *
              fordDyadicShellWeight (x / 2 ^ k) y) := by
        rw [mul_add, Finset.mul_sum]
        apply add_le_add
        · field_simp [hxR.ne']
          have hCOne : 1 ≤ C := le_max_left _ _
          nlinarith [show (0 : ℝ) ≤ (8 * y : ℕ) by positivity]
        · apply Finset.sum_le_sum
          intro k hk
          have hW := fordDyadicShellWeight_nonneg (x / 2 ^ k) y
          rw [show C * (x : ℝ) *
              (((x / 2 ^ k : ℕ) : ℝ) / (x : ℝ) *
                fordDyadicShellWeight (x / 2 ^ k) y) =
              C * ((x / 2 ^ k : ℕ) : ℝ) *
                fordDyadicShellWeight (x / 2 ^ k) y by
            field_simp [hxR.ne']]
          exact mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right hC₀C (by positivity)) hW
      _ = C * (x : ℝ) * fordHStarReductionWeight x y := by
        rw [fordHStarReductionWeight, if_pos hrange]
  · have htriv : (HStar x y (2 * y) : ℝ) ≤ (x : ℝ) := by
      exact_mod_cast HStar_le_x x y
    rw [fordHStarReductionWeight, if_neg hrange]
    simp only [mul_one]
    exact htriv.trans (by
      have hCOne : 1 ≤ C := le_max_left _ _
      nlinarith [show (0 : ℝ) ≤ x by positivity])

/-- Positive multiples of `d` up to `x`, parametrized by their quotient. -/
def multiplesUpTo (x d : ℕ) : Finset ℕ :=
  (Finset.Icc 1 (x / d)).image fun m ↦ m * d

private theorem endpoint_HStarSet_subset (x y : ℕ) :
    HStarSet x y (2 * y + 1) ⊆
      HStarSet x y (2 * y) ∪ multiplesUpTo x (2 * y + 1) := by
  intro n hn
  obtain ⟨hnPos, hnx, hnSq, d, hdn, hyd, hdUpper⟩ := mem_HStarSet.mp hn
  by_cases hdMid : d ≤ 2 * y
  · exact Finset.mem_union_left _
      (mem_HStarSet.mpr ⟨hnPos, hnx, hnSq, d, hdn, hyd, hdMid⟩)
  · apply Finset.mem_union_right
    have hdEq : d = 2 * y + 1 := by omega
    subst d
    have hdPos : 0 < 2 * y + 1 := by omega
    have hquotPos : 0 < n / (2 * y + 1) := Nat.div_pos (Nat.le_of_dvd hnPos hdn) hdPos
    have hquotLe : n / (2 * y + 1) ≤ x / (2 * y + 1) :=
      Nat.div_le_div_right hnx
    apply Finset.mem_image.mpr
    refine ⟨n / (2 * y + 1), Finset.mem_Icc.mpr ⟨hquotPos, hquotLe⟩, ?_⟩
    exact Nat.div_mul_cancel hdn

private theorem HStar_endpoint_le (x y : ℕ) :
    HStar x y (2 * y + 1) ≤ HStar x y (2 * y) + x / (2 * y + 1) := by
  calc
    HStar x y (2 * y + 1) ≤
        (HStarSet x y (2 * y) ∪ multiplesUpTo x (2 * y + 1)).card :=
      Finset.card_le_card (endpoint_HStarSet_subset x y)
    _ ≤ (HStarSet x y (2 * y)).card +
        (multiplesUpTo x (2 * y + 1)).card := Finset.card_union_le _ _
    _ ≤ HStar x y (2 * y) + (Finset.Icc 1 (x / (2 * y + 1))).card := by
      exact Nat.add_le_add_left Finset.card_image_le _
    _ = HStar x y (2 * y) + x / (2 * y + 1) := by simp

private theorem HStar_mono_upper {x y z z' : ℕ} (hzz : z ≤ z') :
    HStar x y z ≤ HStar x y z' := by
  apply Finset.card_le_card
  intro n hn
  obtain ⟨hnPos, hnx, hnSq, d, hdn, hyd, hdz⟩ := mem_HStarSet.mp hn
  exact mem_HStarSet.mpr ⟨hnPos, hnx, hnSq, d, hdn, hyd, hdz.trans hzz⟩

private theorem twice_div_le (y f : ℕ) (hf : 0 < f) :
    2 * y / f ≤ 2 * (y / f) + 1 := by
  have hmod : y % f < f := Nat.mod_lt _ hf
  have hyEq : y = f * (y / f) + y % f := (Nat.div_add_mod y f).symm
  have hlt : 2 * y < (2 * (y / f) + 2) * f := by
    calc
      2 * y = 2 * (f * (y / f) + y % f) :=
        congrArg (fun z : ℕ ↦ 2 * z) hyEq
      _ < (2 * (y / f) + 2) * f := by nlinarith
  have hdivlt : 2 * y / f < 2 * (y / f) + 2 :=
    (Nat.div_lt_iff_lt_mul hf).mpr (by simpa [mul_comm] using hlt)
  omega

/-- The complete finite weighted-`L` expression after restoring the
squarefull part.  The reciprocal `q` is the scale loss from
`x ↦ x/q`; the inner sum runs over the possible squarefull pieces of the
window divisor. -/
noncomputable def fordHReductionWeight (x y : ℕ) : ℝ :=
  ∑ q ∈ squarefullSet x, ∑ f ∈ q.divisors,
    (q : ℝ)⁻¹ *
      (fordHStarReductionWeight (x / q) (y / f) +
        ((2 * (y / f) + 1 : ℕ) : ℝ)⁻¹)

theorem fordHReductionWeight_nonneg (x y : ℕ) :
    0 ≤ fordHReductionWeight x y := by
  classical
  unfold fordHReductionWeight
  exact Finset.sum_nonneg fun q hq ↦ Finset.sum_nonneg fun f hf ↦
    mul_nonneg (inv_nonneg.mpr (by positivity))
      (add_nonneg (fordHStarReductionWeight_nonneg _ _)
        (inv_nonneg.mpr (by positivity)))

/-- Final consumer-facing weight, expressed solely through
`fordDenominatorSum` plus the elementary bottom-shell and endpoint terms. -/
noncomputable def fordHReductionDenominatorWeight (x y : ℕ) : ℝ :=
  ∑ q ∈ squarefullSet x, ∑ f ∈ q.divisors,
    (q : ℝ)⁻¹ *
      (fordHStarDenominatorWeight (x / q) (y / f) +
        ((2 * (y / f) + 1 : ℕ) : ℝ)⁻¹)

theorem fordHReductionDenominatorWeight_nonneg (x y : ℕ) :
    0 ≤ fordHReductionDenominatorWeight x y := by
  classical
  unfold fordHReductionDenominatorWeight
  exact Finset.sum_nonneg fun q hq ↦ Finset.sum_nonneg fun f hf ↦
    mul_nonneg (inv_nonneg.mpr (by positivity))
      (add_nonneg (fordHStarDenominatorWeight_nonneg _ _)
        (inv_nonneg.mpr (by positivity)))

theorem fordHReductionWeight_le_denominatorWeight (x y : ℕ) :
    fordHReductionWeight x y ≤
      16 * fordHReductionDenominatorWeight x y := by
  classical
  rw [fordHReductionWeight, fordHReductionDenominatorWeight,
    Finset.mul_sum]
  apply Finset.sum_le_sum
  intro q hq
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro f hf
  have hqInv : 0 ≤ (q : ℝ)⁻¹ := inv_nonneg.mpr (by positivity)
  have hend : 0 ≤ (((2 * (y / f) + 1 : ℕ) : ℝ))⁻¹ :=
    inv_nonneg.mpr (by positivity)
  have hstar := fordHStarReductionWeight_le_denominatorWeight
    (x / q) (y / f)
  calc
    (q : ℝ)⁻¹ *
        (fordHStarReductionWeight (x / q) (y / f) +
          ((2 * (y / f) + 1 : ℕ) : ℝ)⁻¹) ≤
      (q : ℝ)⁻¹ *
        (16 * fordHStarDenominatorWeight (x / q) (y / f) +
          16 * ((2 * (y / f) + 1 : ℕ) : ℝ)⁻¹) := by
      gcongr
      nlinarith
    _ = 16 * ((q : ℝ)⁻¹ *
        (fordHStarDenominatorWeight (x / q) (y / f) +
          ((2 * (y / f) + 1 : ℕ) : ℝ)⁻¹)) := by ring

/-- Ford Lemma 3.2 in a fully explicit finite weighted form.  All constants
are absolute.  Expanding `fordHReductionWeight` gives only finite sums of
terms `L(a;log 2)/(a log(Q)^2)`, together with the elementary bottom-shell
term. -/
theorem exists_H_le_fordHReductionWeight :
    ∃ C : ℝ, 0 < C ∧ ∀ x y : ℕ,
      (H x y (2 * y) : ℝ) ≤
        C * (x : ℝ) * fordHReductionWeight x y := by
  obtain ⟨C₀, hC₀, hstar⟩ := exists_HStar_le_reductionWeight
  let C := max 1 C₀
  have hC : 0 < C := lt_of_lt_of_le (by norm_num) (le_max_left _ _)
  have hCOne : 1 ≤ C := le_max_left _ _
  have hC₀C : C₀ ≤ C := le_max_right _ _
  refine ⟨C, hC, ?_⟩
  intro x y
  have hnat := H_le_sum_squarefull_HStar x y (2 * y)
  have hcast : (H x y (2 * y) : ℝ) ≤
      ∑ q ∈ squarefullSet x, ∑ f ∈ q.divisors,
        (HStar (x / q) (y / f) ((2 * y) / f) : ℝ) := by
    exact_mod_cast hnat
  calc
    (H x y (2 * y) : ℝ) ≤
        ∑ q ∈ squarefullSet x, ∑ f ∈ q.divisors,
          (HStar (x / q) (y / f) ((2 * y) / f) : ℝ) := hcast
    _ ≤ ∑ q ∈ squarefullSet x, ∑ f ∈ q.divisors,
        C * (x : ℝ) *
          ((q : ℝ)⁻¹ *
            (fordHStarReductionWeight (x / q) (y / f) +
              ((2 * (y / f) + 1 : ℕ) : ℝ)⁻¹)) := by
      apply Finset.sum_le_sum
      intro q hq
      have hqData := mem_squarefullSet.mp hq
      have hqR : (0 : ℝ) < q := by exact_mod_cast hqData.1
      apply Finset.sum_le_sum
      intro f hf
      have hfDvd : f ∣ q := Nat.dvd_of_mem_divisors hf
      have hfPos : 0 < f := Nat.pos_of_dvd_of_pos hfDvd hqData.1
      let X := x / q
      let Y := y / f
      let D := 2 * Y + 1
      have hupper : (2 * y) / f ≤ D := by
        simpa [X, Y, D] using twice_div_le y f hfPos
      have hmono : HStar X Y ((2 * y) / f) ≤ HStar X Y D :=
        HStar_mono_upper hupper
      have hend : HStar X Y D ≤ HStar X Y (2 * Y) + X / D := by
        simpa [D] using HStar_endpoint_le X Y
      have hnatLocal : HStar X Y ((2 * y) / f) ≤
          HStar X Y (2 * Y) + X / D := hmono.trans hend
      have hlocalCast : (HStar X Y ((2 * y) / f) : ℝ) ≤
          (HStar X Y (2 * Y) : ℝ) + ((X / D : ℕ) : ℝ) := by
        exact_mod_cast hnatLocal
      have hDPos : 0 < D := by dsimp [D]; omega
      have hDR : (0 : ℝ) < D := by exact_mod_cast hDPos
      have hXR : (0 : ℝ) ≤ X := by positivity
      have hW := fordHStarReductionWeight_nonneg X Y
      calc
        (HStar (x / q) (y / f) ((2 * y) / f) : ℝ) =
            (HStar X Y ((2 * y) / f) : ℝ) := rfl
        _ ≤ (HStar X Y (2 * Y) : ℝ) + ((X / D : ℕ) : ℝ) := hlocalCast
        _ ≤ C₀ * (X : ℝ) * fordHStarReductionWeight X Y +
              (X : ℝ) / D := by
          exact add_le_add (hstar X Y) Nat.cast_div_le
        _ ≤ C * (X : ℝ) *
              (fordHStarReductionWeight X Y + (D : ℝ)⁻¹) := by
          rw [mul_add]
          apply add_le_add
          · exact mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_right hC₀C hXR) hW
          · rw [div_eq_mul_inv]
            have hXC : (X : ℝ) ≤ C * X := by
              nlinarith
            exact mul_le_mul_of_nonneg_right hXC (inv_nonneg.mpr hDR.le)
        _ ≤ C * ((x : ℝ) / q) *
              (fordHStarReductionWeight X Y + (D : ℝ)⁻¹) := by
          have hdiv : (X : ℝ) ≤ (x : ℝ) / q := Nat.cast_div_le
          exact mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left hdiv hC.le)
            (add_nonneg hW (inv_nonneg.mpr hDR.le))
        _ = C * (x : ℝ) *
              ((q : ℝ)⁻¹ *
                (fordHStarReductionWeight (x / q) (y / f) +
                  ((2 * (y / f) + 1 : ℕ) : ℝ)⁻¹)) := by
          dsimp [X, Y, D]
          field_simp [hqR.ne']
    _ = C * (x : ℝ) * fordHReductionWeight x y := by
      rw [fordHReductionWeight, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro q hq
      rw [Finset.mul_sum]

/-- Ford Lemma 3.2 with the local `L/log²` sums already transported to the
public `fordDenominatorSum` API. -/
theorem exists_H_le_fordHReductionDenominatorWeight :
    ∃ C : ℝ, 0 < C ∧ ∀ x y : ℕ,
      (H x y (2 * y) : ℝ) ≤
        C * (x : ℝ) * fordHReductionDenominatorWeight x y := by
  obtain ⟨C₀, hC₀, hbase⟩ := exists_H_le_fordHReductionWeight
  refine ⟨16 * C₀, by positivity, ?_⟩
  intro x y
  calc
    (H x y (2 * y) : ℝ) ≤
        C₀ * (x : ℝ) * fordHReductionWeight x y := hbase x y
    _ ≤ C₀ * (x : ℝ) *
        (16 * fordHReductionDenominatorWeight x y) := by
      exact mul_le_mul_of_nonneg_left
        (fordHReductionWeight_le_denominatorWeight x y)
        (mul_nonneg hC₀.le (by positivity))
    _ = (16 * C₀) * (x : ℝ) *
        fordHReductionDenominatorWeight x y := by ring

/-- Real-valued form of the squarefull tail estimate, ready to combine with
`squarefullReciprocalTail_le`. -/
theorem card_largeSquarefullHSet_le_mul_reciprocalTail
    (x y z K : ℕ) :
    ((largeSquarefullHSet x y z K).card : ℝ) ≤
      (x : ℝ) * squarefullReciprocalTail K x := by
  have hnat := card_largeSquarefullHSet_le_sum_div x y z K
  have hcast : ((largeSquarefullHSet x y z K).card : ℝ) ≤
      ∑ q ∈ squarefullTailSet x K, ((x / q : ℕ) : ℝ) := by
    exact_mod_cast hnat
  calc
    ((largeSquarefullHSet x y z K).card : ℝ) ≤
        ∑ q ∈ squarefullTailSet x K, ((x / q : ℕ) : ℝ) := hcast
    _ ≤ ∑ q ∈ squarefullTailSet x K, (x : ℝ) * (q : ℝ)⁻¹ := by
      apply Finset.sum_le_sum
      intro q hq
      simpa [div_eq_mul_inv] using
        (Nat.cast_div_le (α := ℝ) (m := x) (n := q))
    _ = (x : ℝ) * squarefullReciprocalTail K x := by
      rw [squarefullReciprocalTail, Finset.mul_sum]

/-- Quantitative squarefull-tail error used in the first stage of Ford's
reduction. -/
theorem card_largeSquarefullHSet_le_sqrt_tail
    {x y z K : ℕ} (hK : 0 < K) :
    ((largeSquarefullHSet x y z K).card : ℝ) ≤
      (x : ℝ) * (squarefullTailConstant / Real.sqrt K) := by
  calc
    ((largeSquarefullHSet x y z K).card : ℝ) ≤
        (x : ℝ) * squarefullReciprocalTail K x :=
      card_largeSquarefullHSet_le_mul_reciprocalTail x y z K
    _ ≤ (x : ℝ) * (squarefullTailConstant / Real.sqrt K) := by
      gcongr
      exact squarefullReciprocalTail_le hK

end Erdos896.Ford
