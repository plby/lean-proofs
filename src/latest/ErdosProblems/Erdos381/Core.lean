/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import Mathlib.Analysis.Asymptotics.AsymptoticEquivalent
import Mathlib.Analysis.Asymptotics.SpecificAsymptotics
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Data.Finset.Interval
import Mathlib.Data.Nat.Log
import Mathlib.Data.Nat.Factorization.Divisors
import Mathlib.NumberTheory.ArithmeticFunction.Misc
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.DiophantineApproximation.Basic
import PrimeNumberTheoremAnd.Consequences
import Mathlib.Tactic

/-!
# Erdős Problem 381

For a positive integer `n`, let `tau n` be its number of positive divisors.
The predicate `HighlyComposite n` says that `n` is a strict record for `tau`,
and `Q N` counts such records in the literal interval `[1, N]`.

Erdős asked whether `Q N ≫ₖ (log N)^k` for every positive natural `k`.
Nicolas proved a fixed polynomial-logarithmic upper bound, so the answer is
negative.  The detailed mathematical reconstruction and dependency audit are
in `tex/381.tex`.
-/

namespace Erdos381

open Filter Asymptotics
open scoped Topology BigOperators

/-! ## Literal finite statement -/

/-- The usual divisor-counting function.  The positivity hypotheses in the
development keep the special Mathlib value of `Nat.divisors 0` irrelevant. -/
def tau (n : ℕ) : ℕ := n.divisors.card

/-- A positive integer is highly composite when it is a strict record for
the divisor-counting function. -/
def HighlyComposite (n : ℕ) : Prop :=
  0 < n ∧ ∀ m : ℕ, 0 < m → m < n → tau m < tau n

noncomputable instance highlyCompositeDecidable (n : ℕ) : Decidable (HighlyComposite n) :=
  Classical.dec _

/-- The number of highly composite integers in the literal closed interval
`[1, N]`. -/
noncomputable def Q (N : ℕ) : ℕ :=
  ((Finset.Icc 1 N).filter HighlyComposite).card

/-- The logarithmic power occurring in the question. -/
noncomputable def logPower (k n : ℕ) : ℝ := Real.log (n : ℝ) ^ k

/-- `Q ≫ (log N)^k`, expressed with Mathlib's orientation of `IsBigO`. -/
def LogPowerLower (k : ℕ) : Prop :=
  (fun n : ℕ ↦ logPower k n) =O[atTop] (fun n : ℕ ↦ (Q n : ℝ))

/-- The exact universal assertion asked in Erdős Problem 381. -/
def Erdos381Claim : Prop :=
  ∀ k : ℕ, 1 ≤ k → LogPowerLower k

/-- The fixed polynomial-logarithmic upper bound proved by Nicolas. -/
def NicolasPolynomialUpperBound : Prop :=
  ∃ C : ℕ, (fun n : ℕ ↦ (Q n : ℝ)) =O[atTop]
    (fun n : ℕ ↦ logPower C n)

@[simp] theorem highlyComposite_one : HighlyComposite 1 := by
  refine ⟨by norm_num, ?_⟩
  intro m hm hm1
  omega

theorem highlyComposite_pos {n : ℕ} (hn : HighlyComposite n) : 0 < n := hn.1

theorem tau_pos {n : ℕ} (hn : n ≠ 0) : 0 < tau n := by
  rw [tau]
  exact Finset.card_pos.mpr ⟨1, Nat.one_mem_divisors.mpr hn⟩

/-! ## Prime-exponent coordinates

Nicolas's proof works in the finitely supported vector of prime exponents.
The following definitions and lemmas put both the integer itself and its
divisor count into those coordinates. -/

/-- Reconstruct an integer from a finitely supported exponent vector. -/
def fromFactorization (f : ℕ →₀ ℕ) : ℕ := f.prod (fun p a ↦ p ^ a)

/-- The product of one plus every nonzero exponent. -/
def divisorProduct (f : ℕ →₀ ℕ) : ℕ := f.prod (fun _ a ↦ a + 1)

@[simp] theorem fromFactorization_zero : fromFactorization 0 = 1 := by
  simp [fromFactorization]

@[simp] theorem fromFactorization_single (p a : ℕ) :
    fromFactorization (Finsupp.single p a) = p ^ a := by
  simp [fromFactorization]

theorem fromFactorization_add (f g : ℕ →₀ ℕ) :
    fromFactorization (f + g) = fromFactorization f * fromFactorization g := by
  simp [fromFactorization, Finsupp.prod_add_index', pow_add]

@[simp] theorem fromFactorization_factorization {n : ℕ} (hn : n ≠ 0) :
    fromFactorization n.factorization = n := by
  simpa [fromFactorization] using Nat.prod_factorization_pow_eq_self hn

theorem factorization_fromFactorization {f : ℕ →₀ ℕ}
    (hf : ∀ p ∈ f.support, p.Prime) :
    (fromFactorization f).factorization = f := by
  simpa [fromFactorization] using Nat.prod_pow_factorization_eq_self hf

theorem fromFactorization_pos {f : ℕ →₀ ℕ}
    (hf : ∀ p ∈ f.support, p.Prime) : 0 < fromFactorization f := by
  rw [Nat.pos_iff_ne_zero]
  exact Finsupp.prod_ne_zero_iff.mpr fun p hp ↦
    pow_ne_zero _ (hf p hp).ne_zero

/-- The usual formula `tau(n) = ∏ₚ (vₚ(n)+1)`, with the product represented
as a `Finsupp.prod`. -/
theorem tau_eq_divisorProduct_factorization {n : ℕ} (hn : n ≠ 0) :
    tau n = divisorProduct n.factorization := by
  simpa [tau, divisorProduct, Nat.prod_factorization_eq_prod_primeFactors] using
    Nat.card_divisors hn

theorem tau_fromFactorization {f : ℕ →₀ ℕ}
    (hf : ∀ p ∈ f.support, p.Prime) :
    tau (fromFactorization f) = divisorProduct f := by
  rw [tau_eq_divisorProduct_factorization (fromFactorization_pos hf).ne',
    factorization_fromFactorization hf]

/-- Logarithmic form of the divisor-product formula. -/
theorem log_tau_eq_sum_factorization {n : ℕ} (hn : n ≠ 0) :
    Real.log (tau n : ℝ) =
      n.factorization.sum (fun _ a ↦ Real.log (a + 1 : ℕ)) := by
  rw [tau_eq_divisorProduct_factorization hn, divisorProduct,
    Nat.cast_finsuppProd]
  apply Finsupp.log_prod
  intro p hp
  exfalso
  have : (0 : ℝ) < ((n.factorization p + 1 : ℕ) : ℝ) := by positivity
  linarith

theorem log_nat_eq_sum_factorization_on (n : ℕ) (S : Finset ℕ)
    (hS : n.primeFactors ⊆ S) :
    Real.log n = ∑ p ∈ S, (n.factorization p : ℝ) * Real.log p := by
  rw [Real.log_nat_eq_sum_factorization]
  exact Finsupp.sum_of_support_subset n.factorization hS _ (by simp)

theorem log_tau_eq_sum_factorization_on {n : ℕ} (hn : n ≠ 0)
    (S : Finset ℕ) (hS : n.primeFactors ⊆ S) :
    Real.log (tau n : ℝ) =
      ∑ p ∈ S, Real.log (n.factorization p + 1 : ℕ) := by
  rw [log_tau_eq_sum_factorization hn]
  exact Finsupp.sum_of_support_subset n.factorization hS _ (by simp)

/-- Permuting the prime labels does not change the divisor product. -/
theorem divisorProduct_equivMapDomain (e : Equiv.Perm ℕ) (f : ℕ →₀ ℕ) :
    divisorProduct (Finsupp.equivMapDomain e f) = divisorProduct f := by
  simp [divisorProduct, Finsupp.prod_equivMapDomain]

/-- Exchange the exponents carried by two prime labels. -/
def swapFactorization (p q : ℕ) (f : ℕ →₀ ℕ) : ℕ →₀ ℕ :=
  Finsupp.equivMapDomain (Equiv.swap p q) f

@[simp] theorem swapFactorization_apply_left (p q : ℕ) (f : ℕ →₀ ℕ) :
    swapFactorization p q f p = f q := by
  simp [swapFactorization, Finsupp.equivMapDomain_apply]

@[simp] theorem swapFactorization_apply_right (p q : ℕ) (f : ℕ →₀ ℕ) :
    swapFactorization p q f q = f p := by
  simp [swapFactorization, Finsupp.equivMapDomain_apply]

theorem swapFactorization_prime_support {p q : ℕ} (hp : p.Prime) (hq : q.Prime)
    {f : ℕ →₀ ℕ} (hf : ∀ r ∈ f.support, r.Prime) :
    ∀ r ∈ (swapFactorization p q f).support, r.Prime := by
  intro r hr
  by_cases hrp : r = p
  · simpa [hrp] using hp
  by_cases hrq : r = q
  · simpa [hrq] using hq
  have hswap : Equiv.swap p q r ∈ f.support := by
    simpa [swapFactorization, Finsupp.mem_support_iff,
      Finsupp.equivMapDomain_apply] using hr
  simpa [Equiv.swap_apply_of_ne_of_ne hrp hrq] using hf _ hswap

theorem tau_fromFactorization_swap {p q : ℕ} (hp : p.Prime) (hq : q.Prime)
    {f : ℕ →₀ ℕ} (hf : ∀ r ∈ f.support, r.Prime) :
    tau (fromFactorization (swapFactorization p q f)) = tau (fromFactorization f) := by
  rw [tau_fromFactorization (swapFactorization_prime_support hp hq hf),
    tau_fromFactorization hf]
  exact divisorProduct_equivMapDomain (Equiv.swap p q) f

theorem pow_swap_lt {p q a b : ℕ} (hp : p.Prime) (hpq : p < q) (hab : a < b) :
    p ^ b * q ^ a < p ^ a * q ^ b := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_lt hab
  have hpow : p ^ (d + 1) < q ^ (d + 1) :=
    Nat.pow_lt_pow_left hpq (by omega)
  have hcommon : 0 < p ^ a * q ^ a := by
    have hq : 0 < q := hp.pos.trans hpq
    exact Nat.mul_pos (Nat.pow_pos hp.pos) (Nat.pow_pos hq)
  calc
    p ^ (a + d + 1) * q ^ a = (p ^ a * q ^ a) * p ^ (d + 1) := by
      simp only [show a + d + 1 = a + (d + 1) by omega, pow_add]
      ac_rfl
    _ < (p ^ a * q ^ a) * q ^ (d + 1) :=
      Nat.mul_lt_mul_of_pos_left hpow hcommon
    _ = p ^ a * q ^ (a + d + 1) := by
      simp only [show a + d + 1 = a + (d + 1) by omega, pow_add]
      ac_rfl

theorem swapFactorization_balance {p q : ℕ} (hpq : p ≠ q) (f : ℕ →₀ ℕ) :
    swapFactorization p q f + Finsupp.single p (f p) + Finsupp.single q (f q) =
      f + Finsupp.single p (f q) + Finsupp.single q (f p) := by
  ext r
  by_cases hrp : r = p
  · subst r
    simp [hpq]
    omega
  by_cases hrq : r = q
  · subst r
    simp [hpq]
    omega
  simp [swapFactorization, Finsupp.equivMapDomain_apply,
    Equiv.swap_apply_of_ne_of_ne hrp hrq, hrp, hrq]

theorem fromFactorization_swap_mul {p q : ℕ} (hpq : p ≠ q) (f : ℕ →₀ ℕ) :
    fromFactorization (swapFactorization p q f) * (p ^ f p * q ^ f q) =
      fromFactorization f * (p ^ f q * q ^ f p) := by
  have h := congrArg fromFactorization (swapFactorization_balance hpq f)
  simpa only [fromFactorization_add, fromFactorization_single, mul_assoc] using h

theorem fromFactorization_swap_lt {p q : ℕ} (hp : p.Prime) (hpq : p < q)
    {f : ℕ →₀ ℕ} (hexp : f p < f q)
    (hf : ∀ r ∈ f.support, r.Prime) :
    fromFactorization (swapFactorization p q f) < fromFactorization f := by
  have hbalance := fromFactorization_swap_mul hpq.ne f
  have hselected : p ^ f q * q ^ f p < p ^ f p * q ^ f q :=
    pow_swap_lt hp hpq hexp
  have hpos : 0 < fromFactorization f := fromFactorization_pos hf
  by_contra hnot
  have hle : fromFactorization f ≤ fromFactorization (swapFactorization p q f) :=
    Nat.le_of_not_gt hnot
  have hmul_le := Nat.mul_le_mul_right (p ^ f p * q ^ f q) hle
  have hmul_lt := mul_lt_mul_of_pos_left hselected hpos
  omega

/-- Prime exponents of a highly composite number are nonincreasing as the
prime labels increase.  This is the basic rearrangement argument: swapping
an inverted pair preserves `tau` and strictly decreases the integer. -/
theorem highlyComposite_factorization_antitone {n p q : ℕ} (hn : HighlyComposite n)
    (hp : p.Prime) (hq : q.Prime) (hpq : p < q) :
    n.factorization q ≤ n.factorization p := by
  by_contra hnot
  have hexp : n.factorization p < n.factorization q := Nat.lt_of_not_ge hnot
  let f : ℕ →₀ ℕ := n.factorization
  let m : ℕ := fromFactorization (swapFactorization p q f)
  have hf : ∀ r ∈ f.support, r.Prime := fun r hr ↦
    Nat.prime_of_mem_primeFactors hr
  have hmpos : 0 < m :=
    fromFactorization_pos (swapFactorization_prime_support hp hq hf)
  have hmlt : m < n := by
    rw [← fromFactorization_factorization hn.1.ne']
    exact fromFactorization_swap_lt hp hpq hexp hf
  have htau : tau m = tau n := by
    calc
      tau m = tau (fromFactorization f) := tau_fromFactorization_swap hp hq hf
      _ = tau n := by rw [fromFactorization_factorization hn.1.ne']
  exact (hn.2 m hmpos hmlt).ne htau

/-- Consequently the prime divisors of a highly composite number form an
initial segment of the primes. -/
theorem prime_dvd_of_lt_prime_dvd {n p q : ℕ} (hn : HighlyComposite n)
    (hp : p.Prime) (hq : q.Prime) (hpq : p < q) (hqn : q ∣ n) : p ∣ n := by
  have hqexp : 0 < n.factorization q :=
    hq.factorization_pos_of_dvd hn.1.ne' hqn
  have hmono := highlyComposite_factorization_antitone hn hp hq hpq
  exact Nat.dvd_of_factorization_pos (Nat.ne_of_gt (hqexp.trans_le hmono))

/-- The exponent at the smallest prime dominates every prime coordinate of a
highly composite number. -/
theorem highlyComposite_factorization_le_two {n p : ℕ}
    (hn : HighlyComposite n) (hp : p.Prime) :
    n.factorization p ≤ n.factorization 2 := by
  rcases hp.eq_two_or_odd' with rfl | hpOdd
  · exact le_rfl
  · obtain ⟨r, hr⟩ := hpOdd
    have hpLt : 2 < p := by
      have := hp.one_lt
      omega
    exact highlyComposite_factorization_antitone hn Nat.prime_two hp hpLt

/-- The largest prime whose exponent is at least `k`.  Returning zero when
the level is empty makes the boundary vector total and convenient for finite
encoding. -/
noncomputable def exponentBoundary (n k : ℕ) : ℕ :=
  Nat.findGreatest (fun p ↦ p.Prime ∧ k ≤ n.factorization p) n

theorem exponentBoundary_le (n k : ℕ) : exponentBoundary n k ≤ n :=
  Nat.findGreatest_le n

/-- For a highly composite number, the level-`k` primes are exactly the
initial prime segment ending at `exponentBoundary n k`. -/
theorem prime_le_exponentBoundary_iff {n p k : ℕ}
    (hn : HighlyComposite n) (hp : p.Prime) (hk : 0 < k) :
    p ≤ exponentBoundary n k ↔ k ≤ n.factorization p := by
  constructor
  · intro hpBoundary
    have hBoundaryPos : 0 < exponentBoundary n k :=
      lt_of_lt_of_le hp.pos hpBoundary
    have hspec :
        (exponentBoundary n k).Prime ∧
          k ≤ n.factorization (exponentBoundary n k) := by
      exact Nat.findGreatest_of_ne_zero rfl hBoundaryPos.ne'
    rcases lt_or_eq_of_le hpBoundary with hpLt | hpEq
    · exact hspec.2.trans
        (highlyComposite_factorization_antitone hn hp hspec.1 hpLt)
    · simpa [hpEq] using hspec.2
  · intro hkp
    have hpFactorization : 0 < n.factorization p := hk.trans_le hkp
    have hpDvd : p ∣ n := Nat.dvd_of_factorization_pos hpFactorization.ne'
    have hpLeN : p ≤ n := Nat.le_of_dvd hn.1 hpDvd
    exact Nat.le_findGreatest hpLeN ⟨hp, hkp⟩

/-- The full level-boundary vector, together with the exponent at `2`,
determines a highly composite integer.  This is the injectivity theorem used
by the eventual finite certificate; it avoids any appeal to an informal
partition encoding. -/
theorem highlyComposite_eq_of_exponentBoundary_eq {n m : ℕ}
    (hn : HighlyComposite n) (hm : HighlyComposite m)
    (h2 : n.factorization 2 = m.factorization 2)
    (hBoundary : ∀ k : ℕ, 0 < k → k ≤ n.factorization 2 →
      exponentBoundary n k = exponentBoundary m k) :
    n = m := by
  apply Nat.factorization_inj hn.1.ne' hm.1.ne'
  ext p
  by_cases hp : p.Prime
  · apply Nat.le_antisymm
    · by_cases ha : n.factorization p = 0
      · omega
      · have haPos : 0 < n.factorization p := Nat.pos_of_ne_zero ha
        have haTwo : n.factorization p ≤ n.factorization 2 :=
          highlyComposite_factorization_le_two hn hp
        have hpBoundary :
            p ≤ exponentBoundary n (n.factorization p) :=
          (prime_le_exponentBoundary_iff hn hp haPos).2 le_rfl
        rw [hBoundary _ haPos haTwo] at hpBoundary
        exact (prime_le_exponentBoundary_iff hm hp haPos).1 hpBoundary
    · by_cases hb : m.factorization p = 0
      · omega
      · have hbPos : 0 < m.factorization p := Nat.pos_of_ne_zero hb
        have hbTwoM : m.factorization p ≤ m.factorization 2 :=
          highlyComposite_factorization_le_two hm hp
        have hbTwoN : m.factorization p ≤ n.factorization 2 := by
          rw [h2]
          exact hbTwoM
        have hpBoundary :
            p ≤ exponentBoundary m (m.factorization p) :=
          (prime_le_exponentBoundary_iff hm hp hbPos).2 le_rfl
        rw [← hBoundary _ hbPos hbTwoN] at hpBoundary
        exact (prime_le_exponentBoundary_iff hn hp hbPos).1 hpBoundary
  · simp [Nat.factorization_eq_zero_of_not_prime, hp]

/-! ## Superior numbers and benefit

The logarithmic formulation below is exactly the quotient formulation used
by Ramanujan and Nicolas, but is better suited to additive primewise
decomposition.  Positivity hypotheses ensure that every logarithm is taken
at a positive real number. -/

/-- Nicolas's benefit of `M` relative to the superior anchor `N`. -/
noncomputable def benefit (ε : ℝ) (N M : ℕ) : ℝ :=
  ε * Real.log ((M : ℝ) / (N : ℝ)) -
    Real.log ((tau M : ℝ) / (tau N : ℝ))

/-- Contribution of one prime when its exponent changes from `a` in the
anchor to `b` in the comparison integer. -/
noncomputable def localBenefit (ε : ℝ) (p a b : ℕ) : ℝ :=
  ε * ((b : ℝ) - (a : ℝ)) * Real.log p -
    Real.log (((b + 1 : ℕ) : ℝ) / ((a + 1 : ℕ) : ℝ))

/-- The finite sum of local contributions over every prime occurring in
either integer. -/
noncomputable def factorizationBenefit (ε : ℝ) (N M : ℕ) : ℝ :=
  ∑ p ∈ N.primeFactors ∪ M.primeFactors,
    localBenefit ε p (N.factorization p) (M.factorization p)

theorem localBenefit_raise (ε : ℝ) (p a : ℕ) :
    localBenefit ε p a (a + 1) =
      ε * Real.log p - Real.log (1 + 1 / ((a + 1 : ℕ) : ℝ)) := by
  have hden : ((a + 1 : ℕ) : ℝ) ≠ 0 := by positivity
  have hratio :
      (((a + 1 + 1 : ℕ) : ℝ) / ((a + 1 : ℕ) : ℝ)) =
        1 + 1 / ((a + 1 : ℕ) : ℝ) := by
    push_cast
    field_simp
  rw [localBenefit, hratio]
  push_cast
  ring

theorem localBenefit_lower (ε : ℝ) (p a : ℕ) :
    localBenefit ε p (a + 1) a =
      Real.log (1 + 1 / ((a + 1 : ℕ) : ℝ)) - ε * Real.log p := by
  have hden : ((a + 1 : ℕ) : ℝ) ≠ 0 := by positivity
  have hratio :
      (((a + 1 : ℕ) : ℝ) / ((a + 1 + 1 : ℕ) : ℝ)) =
        (1 + 1 / ((a + 1 : ℕ) : ℝ))⁻¹ := by
    push_cast
    field_simp
  rw [localBenefit, hratio, Real.log_inv]
  push_cast
  ring

/-- Additivity of local benefit along an intermediate exponent. -/
theorem localBenefit_cocycle (ε : ℝ) (p a b c : ℕ) :
    localBenefit ε p a c =
      localBenefit ε p a b + localBenefit ε p b c := by
  have ha : (((a + 1 : ℕ) : ℝ)) ≠ 0 := by positivity
  have hb : (((b + 1 : ℕ) : ℝ)) ≠ 0 := by positivity
  have hc : (((c + 1 : ℕ) : ℝ)) ≠ 0 := by positivity
  rw [localBenefit, localBenefit, localBenefit,
    Real.log_div hc ha, Real.log_div hb ha, Real.log_div hc hb]
  push_cast
  ring

/-- The multiplicative objective whose logarithmic loss is `benefit`. -/
noncomputable def superiorScore (ε : ℝ) (n : ℕ) : ℝ :=
  (tau n : ℝ) * Real.exp (-ε * Real.log (n : ℝ))

/-- A logarithmic characterization of a superior highly composite number.
It is equivalent to saying that `tau M / M^ε` is globally maximal at `N`. -/
def Superior (ε : ℝ) (N : ℕ) : Prop :=
  0 < N ∧ ∀ M : ℕ, 0 < M → 0 ≤ benefit ε N M

noncomputable instance superiorDecidable (ε : ℝ) (N : ℕ) :
    Decidable (Superior ε N) := Classical.dec _

/-- Primewise optimality of one exponent for the superior objective. -/
def PrimeExponentOptimal (ε : ℝ) (p a : ℕ) : Prop :=
  ∀ b : ℕ, 0 ≤ localBenefit ε p a b

/-- Ramanujan's canonical exponent `⌊1 / (p^ε - 1)⌋`. -/
noncomputable def canonicalExponent (ε : ℝ) (p : ℕ) : ℕ :=
  ⌊1 / ((p : ℝ) ^ ε - 1)⌋₊

theorem canonicalExponent_floor_bounds {ε : ℝ} (hε : 0 < ε) {p : ℕ}
    (hp : p.Prime) :
    (canonicalExponent ε p : ℝ) ≤ 1 / ((p : ℝ) ^ ε - 1) ∧
      1 / ((p : ℝ) ^ ε - 1) < canonicalExponent ε p + 1 := by
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
  have hy : (1 : ℝ) < (p : ℝ) ^ ε := Real.one_lt_rpow hp1 hε
  have hx : 0 ≤ 1 / ((p : ℝ) ^ ε - 1) := by positivity
  constructor
  · exact Nat.floor_le hx
  · simpa [canonicalExponent] using
      (Nat.lt_floor_add_one (1 / ((p : ℝ) ^ ε - 1)))

theorem canonicalExponent_raise_threshold {ε : ℝ} (hε : 0 < ε) {p : ℕ}
    (hp : p.Prime) :
    Real.log (1 + 1 / ((canonicalExponent ε p + 1 : ℕ) : ℝ)) ≤
      ε * Real.log p := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
  have hy : (1 : ℝ) < (p : ℝ) ^ ε := Real.one_lt_rpow hp1 hε
  have hden : 0 < (p : ℝ) ^ ε - 1 := sub_pos.mpr hy
  have ha1 : 0 < ((canonicalExponent ε p + 1 : ℕ) : ℝ) := by positivity
  have hfloor := (canonicalExponent_floor_bounds hε hp).2
  have hfloor' : 1 / ((p : ℝ) ^ ε - 1) <
      ((canonicalExponent ε p + 1 : ℕ) : ℝ) := by
    push_cast
    exact hfloor
  have hmul : 1 < ((canonicalExponent ε p + 1 : ℕ) : ℝ) *
      ((p : ℝ) ^ ε - 1) := (div_lt_iff₀ hden).mp hfloor'
  have hinv : 1 / ((canonicalExponent ε p + 1 : ℕ) : ℝ) ≤
      (p : ℝ) ^ ε - 1 := by
    apply (div_le_iff₀ ha1).2
    nlinarith
  rw [← Real.log_rpow hp0 ε]
  apply Real.log_le_log
  · positivity
  · linarith

theorem canonicalExponent_raise_threshold_strict {ε : ℝ} (hε : 0 < ε)
    {p : ℕ} (hp : p.Prime) :
    Real.log (1 + 1 / ((canonicalExponent ε p + 1 : ℕ) : ℝ)) <
      ε * Real.log p := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
  have hy : (1 : ℝ) < (p : ℝ) ^ ε := Real.one_lt_rpow hp1 hε
  have hden : 0 < (p : ℝ) ^ ε - 1 := sub_pos.mpr hy
  have ha1 : 0 < ((canonicalExponent ε p + 1 : ℕ) : ℝ) := by positivity
  have hfloor := (canonicalExponent_floor_bounds hε hp).2
  have hfloor' : 1 / ((p : ℝ) ^ ε - 1) <
      ((canonicalExponent ε p + 1 : ℕ) : ℝ) := by
    push_cast
    exact hfloor
  have hmul : 1 < ((canonicalExponent ε p + 1 : ℕ) : ℝ) *
      ((p : ℝ) ^ ε - 1) := (div_lt_iff₀ hden).mp hfloor'
  have hinv : 1 / ((canonicalExponent ε p + 1 : ℕ) : ℝ) <
      (p : ℝ) ^ ε - 1 := by
    rw [div_lt_iff₀ ha1]
    nlinarith
  rw [← Real.log_rpow hp0 ε]
  apply Real.strictMonoOn_log
  · exact Set.mem_Ioi.mpr (by positivity)
  · exact Set.mem_Ioi.mpr (Real.rpow_pos_of_pos hp0 ε)
  · linarith

theorem canonicalExponent_lower_threshold {ε : ℝ} (hε : 0 < ε) {p : ℕ}
    (hp : p.Prime) (ha : 0 < canonicalExponent ε p) :
    ε * Real.log p ≤
      Real.log (1 + 1 / (canonicalExponent ε p : ℝ)) := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
  have hy : (1 : ℝ) < (p : ℝ) ^ ε := Real.one_lt_rpow hp1 hε
  have hden : 0 < (p : ℝ) ^ ε - 1 := sub_pos.mpr hy
  have hareal : 0 < (canonicalExponent ε p : ℝ) := by exact_mod_cast ha
  have hfloor := (canonicalExponent_floor_bounds hε hp).1
  have hmul : (canonicalExponent ε p : ℝ) * ((p : ℝ) ^ ε - 1) ≤ 1 :=
    (le_div_iff₀ hden).mp hfloor
  have hinv : (p : ℝ) ^ ε - 1 ≤ 1 / (canonicalExponent ε p : ℝ) := by
    apply (le_div_iff₀ hareal).2
    nlinarith
  rw [← Real.log_rpow hp0 ε]
  apply Real.log_le_log
  · exact Real.rpow_pos_of_pos hp0 ε
  · linarith

theorem log_one_add_inv_succ_antitone {a b : ℕ} (hab : a ≤ b) :
    Real.log (1 + 1 / ((b + 1 : ℕ) : ℝ)) ≤
      Real.log (1 + 1 / ((a + 1 : ℕ) : ℝ)) := by
  have ha : (0 : ℝ) < ((a + 1 : ℕ) : ℝ) := by positivity
  have hab' : ((a + 1 : ℕ) : ℝ) ≤ ((b + 1 : ℕ) : ℝ) := by
    exact_mod_cast Nat.add_le_add_right hab 1
  apply Real.log_le_log
  · positivity
  · exact add_le_add_right (one_div_le_one_div_of_le ha hab') 1

theorem log_one_add_inv_nat_antitone {a b : ℕ} (ha : 0 < a) (hab : a ≤ b) :
    Real.log (1 + 1 / (b : ℝ)) ≤ Real.log (1 + 1 / (a : ℝ)) := by
  have ha' : (0 : ℝ) < a := by exact_mod_cast ha
  have hab' : (a : ℝ) ≤ (b : ℝ) := by exact_mod_cast hab
  apply Real.log_le_log
  · positivity
  · exact add_le_add_right (one_div_le_one_div_of_le ha' hab') 1

theorem log_one_add_inv_nat_strictAnti {a b : ℕ} (ha : 0 < a) (hab : a < b) :
    Real.log (1 + 1 / (b : ℝ)) < Real.log (1 + 1 / (a : ℝ)) := by
  have ha' : (0 : ℝ) < a := by exact_mod_cast ha
  have hab' : (a : ℝ) < (b : ℝ) := by exact_mod_cast hab
  apply Real.strictMonoOn_log
  · exact Set.mem_Ioi.mpr (by positivity)
  · exact Set.mem_Ioi.mpr (by positivity)
  · exact add_lt_add_right (one_div_lt_one_div_of_lt ha' hab') 1

theorem PrimeExponentOptimal.raise_threshold {ε : ℝ} {p a : ℕ}
    (hopt : PrimeExponentOptimal ε p a) :
    Real.log (1 + 1 / ((a + 1 : ℕ) : ℝ)) ≤ ε * Real.log p := by
  have hlocal := hopt (a + 1)
  rw [localBenefit_raise] at hlocal
  linarith

theorem PrimeExponentOptimal.lower_threshold {ε : ℝ} {p a : ℕ}
    (hopt : PrimeExponentOptimal ε p a) (ha : 0 < a) :
    ε * Real.log p ≤ Real.log (1 + 1 / (a : ℝ)) := by
  have hlocal := hopt (a - 1)
  have hsucc : a - 1 + 1 = a := Nat.sub_add_cancel ha
  have hlocal' : 0 ≤ localBenefit ε p (a - 1 + 1) (a - 1) := by
    simpa only [hsucc] using hlocal
  rw [localBenefit_lower] at hlocal'
  simp only [hsucc] at hlocal'
  linarith

/-- Once an optimal exponent has been passed upwards, every further unit
raise has nonnegative local benefit. -/
theorem PrimeExponentOptimal.raise_step_nonneg {ε : ℝ} {p a b : ℕ}
    (hopt : PrimeExponentOptimal ε p a) (hab : a ≤ b) :
    0 ≤ localBenefit ε p b (b + 1) := by
  rw [localBenefit_raise]
  have hthreshold := hopt.raise_threshold
  have hmono := log_one_add_inv_succ_antitone hab
  linarith

/-- Below an optimal positive exponent, every further unit lowering has
nonnegative local benefit. -/
theorem PrimeExponentOptimal.lower_step_nonneg {ε : ℝ} {p a b : ℕ}
    (hopt : PrimeExponentOptimal ε p a) (hba : b < a) :
    0 ≤ localBenefit ε p (b + 1) b := by
  rw [localBenefit_lower]
  have ha : 0 < a := (Nat.zero_le b).trans_lt hba
  have hthreshold := hopt.lower_threshold ha
  have hmono := log_one_add_inv_nat_antitone (Nat.succ_pos b)
    (Nat.succ_le_iff.mpr hba)
  linarith

theorem PrimeExponentOptimal.raise_segment_nonneg {ε : ℝ} {p a b c : ℕ}
    (hopt : PrimeExponentOptimal ε p a) (hab : a ≤ b) (hbc : b ≤ c) :
    0 ≤ localBenefit ε p b c := by
  exact Nat.le_induction (m := b)
    (by simp [localBenefit])
    (fun n hbn ih ↦ by
      rw [localBenefit_cocycle ε p b n (n + 1)]
      exact add_nonneg ih
        (hopt.raise_step_nonneg (hab.trans hbn)))
    c hbc

theorem PrimeExponentOptimal.lower_segment_nonneg {ε : ℝ} {p a b c : ℕ}
    (hopt : PrimeExponentOptimal ε p a) (hba : b ≤ a) (hcb : c ≤ b) :
    0 ≤ localBenefit ε p b c := by
  exact Nat.decreasingInduction (n := b)
    (motive := fun c _ ↦ 0 ≤ localBenefit ε p b c)
    (fun k hkb ih ↦ by
      rw [localBenefit_cocycle ε p b (k + 1) k]
      exact add_nonneg ih
        (hopt.lower_step_nonneg (Nat.lt_of_lt_of_le hkb hba)))
    (by simp [localBenefit]) hcb

/-- Moving an optimal exponent upwards by at least two incurs the explicit
strict convexity loss between the first two unit divisor ratios. -/
theorem PrimeExponentOptimal.two_raise_loss_le {ε : ℝ} {p a b : ℕ}
    (hopt : PrimeExponentOptimal ε p a) (hab : a + 2 ≤ b) :
    Real.log (1 + 1 / ((a + 1 : ℕ) : ℝ)) -
        Real.log (1 + 1 / ((a + 2 : ℕ) : ℝ)) ≤
      localBenefit ε p a b := by
  have hfirst : 0 ≤ localBenefit ε p a (a + 1) := hopt (a + 1)
  have hsecond :
      Real.log (1 + 1 / ((a + 1 : ℕ) : ℝ)) -
          Real.log (1 + 1 / ((a + 2 : ℕ) : ℝ)) ≤
        localBenefit ε p (a + 1) (a + 2) := by
    rw [localBenefit_raise]
    have hthreshold := hopt.raise_threshold
    linarith
  have htail : 0 ≤ localBenefit ε p (a + 2) b :=
    hopt.raise_segment_nonneg (by omega) hab
  rw [localBenefit_cocycle ε p a (a + 1) b,
    localBenefit_cocycle ε p (a + 1) (a + 2) b]
  linarith

/-- Moving an optimal exponent downwards by at least two has the analogous
explicit convexity loss. -/
theorem PrimeExponentOptimal.two_lower_loss_le {ε : ℝ} {p a b : ℕ}
    (hopt : PrimeExponentOptimal ε p a) (hab : b + 2 ≤ a) :
    Real.log (1 + 1 / ((a - 1 : ℕ) : ℝ)) -
        Real.log (1 + 1 / (a : ℝ)) ≤
      localBenefit ε p a b := by
  have hfirst : 0 ≤ localBenefit ε p a (a - 1) := hopt (a - 1)
  have hsecond :
      Real.log (1 + 1 / ((a - 1 : ℕ) : ℝ)) -
          Real.log (1 + 1 / (a : ℝ)) ≤
        localBenefit ε p (a - 1) (a - 2) := by
    have hstep := hopt.lower_step_nonneg (b := a - 2) (by omega)
    have hthreshold := hopt.lower_threshold (by omega : 0 < a)
    have hsucc1 : a - 2 + 1 = a - 1 := by omega
    rw [localBenefit_lower] at hstep
    simp only [hsucc1] at hstep
    have hformula :
        localBenefit ε p (a - 1) (a - 2) =
          Real.log (1 + 1 / ((a - 1 : ℕ) : ℝ)) -
            ε * Real.log p := by
      simpa only [hsucc1] using localBenefit_lower ε p (a - 2)
    rw [hformula]
    linarith
  have htail : 0 ≤ localBenefit ε p (a - 2) b :=
    hopt.lower_segment_nonneg (by omega) (by omega)
  rw [localBenefit_cocycle ε p a (a - 1) b,
    localBenefit_cocycle ε p (a - 1) (a - 2) b]
  linarith

/-- The first two upward steps are separated by at least the reciprocal
square shown here.  This makes the strict-convexity loss quantitative without
Taylor expansions. -/
theorem two_raise_loss_reciprocal_square_le (a : ℕ) :
    1 / (((a : ℝ) + 2) ^ 2) ≤
      Real.log (1 + 1 / ((a + 1 : ℕ) : ℝ)) -
        Real.log (1 + 1 / ((a + 2 : ℕ) : ℝ)) := by
  rw [← Real.log_div (by positivity :
      (1 + 1 / ((a + 1 : ℕ) : ℝ)) ≠ 0)
    (by positivity : (1 + 1 / ((a + 2 : ℕ) : ℝ)) ≠ 0)]
  have hratio :
      (1 + 1 / ((a + 1 : ℕ) : ℝ)) /
          (1 + 1 / ((a + 2 : ℕ) : ℝ)) =
        1 + 1 / (((a : ℝ) + 1) * ((a : ℝ) + 3)) := by
    push_cast
    field_simp
    ring
  rw [hratio]
  have hbase : 0 < 1 + 1 / (((a : ℝ) + 1) * ((a : ℝ) + 3)) := by
    positivity
  have hlog := Real.one_sub_inv_le_log_of_pos hbase
  calc
    1 / (((a : ℝ) + 2) ^ 2) =
        1 - (1 + 1 / (((a : ℝ) + 1) * ((a : ℝ) + 3)))⁻¹ := by
          field_simp
          ring
    _ ≤ Real.log (1 + 1 / (((a : ℝ) + 1) * ((a : ℝ) + 3))) := hlog

/-- The analogous reciprocal-square lower bound for two downward steps. -/
theorem two_lower_loss_reciprocal_square_le {a : ℕ} (ha : 2 ≤ a) :
    1 / ((a : ℝ) ^ 2) ≤
      Real.log (1 + 1 / ((a - 1 : ℕ) : ℝ)) -
        Real.log (1 + 1 / (a : ℝ)) := by
  have haR : (2 : ℝ) ≤ a := by exact_mod_cast ha
  have ha1 : (0 : ℝ) < (a : ℝ) - 1 := by linarith
  have ha0 : (0 : ℝ) < a := by positivity
  have haP : (0 : ℝ) < (a : ℝ) + 1 := by positivity
  have hcast : ((a - 1 : ℕ) : ℝ) = (a : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega)]
    norm_num
  rw [← Real.log_div (by rw [hcast]; positivity :
      (1 + 1 / ((a - 1 : ℕ) : ℝ)) ≠ 0)
    (by positivity : (1 + 1 / (a : ℝ)) ≠ 0)]
  have hratio :
      (1 + 1 / ((a - 1 : ℕ) : ℝ)) / (1 + 1 / (a : ℝ)) =
        1 + 1 / (((a : ℝ) - 1) * ((a : ℝ) + 1)) := by
    rw [hcast]
    field_simp
    ring
  rw [hratio]
  have hbase : 0 < 1 + 1 / (((a : ℝ) - 1) * ((a : ℝ) + 1)) := by
    positivity
  have hlog := Real.one_sub_inv_le_log_of_pos hbase
  calc
    1 / ((a : ℝ) ^ 2) =
        1 - (1 + 1 / (((a : ℝ) - 1) * ((a : ℝ) + 1)))⁻¹ := by
          field_simp
          ring
    _ ≤ Real.log (1 + 1 / (((a : ℝ) - 1) * ((a : ℝ) + 1))) := hlog

/-- A fixed power saving eventually beats the reciprocal-square loss at
every exponent of logarithmic size. -/
theorem eventually_const_mul_rpow_neg_lt_inv_log_sq
    (C γ : ℝ) (hC : 0 ≤ C) (hγ : 0 < γ) :
    ∀ᶠ x : ℝ in atTop,
      C * x ^ (-γ) < 1 / ((3 * Real.log x + 2) ^ 2) := by
  have heps : 0 < 1 / (25 * (C + 1)) := by positivity
  have hlittle := isLittleO_log_rpow_rpow_atTop 2 hγ
  rw [isLittleO_iff] at hlittle
  filter_upwards [hlittle heps,
      Real.tendsto_log_atTop.eventually (eventually_ge_atTop (1 : ℝ)),
      eventually_gt_atTop (0 : ℝ)] with x hsmall hlog hx
  have hxpow : 0 < x ^ γ := Real.rpow_pos_of_pos hx γ
  have hlog0 : 0 ≤ Real.log x := zero_le_one.trans hlog
  have hsmall' : Real.log x ^ 2 ≤
      (1 / (25 * (C + 1))) * x ^ γ := by
    simpa only [Real.rpow_two, Real.norm_eq_abs,
      abs_of_nonneg (pow_nonneg hlog0 2), abs_of_pos hxpow] using hsmall
  have haff : (3 * Real.log x + 2) ^ 2 ≤ 25 * Real.log x ^ 2 := by
    nlinarith [sq_nonneg (Real.log x - 1)]
  have haff' : (3 * Real.log x + 2) ^ 2 ≤ x ^ γ / (C + 1) := by
    calc
      (3 * Real.log x + 2) ^ 2 ≤ 25 * Real.log x ^ 2 := haff
      _ ≤ 25 * ((1 / (25 * (C + 1))) * x ^ γ) := by gcongr
      _ = x ^ γ / (C + 1) := by field_simp
  have hprod : (C * x ^ (-γ)) * (3 * Real.log x + 2) ^ 2 < 1 := by
    rw [Real.rpow_neg hx.le]
    calc
      (C * (x ^ γ)⁻¹) * (3 * Real.log x + 2) ^ 2 ≤
          (C * (x ^ γ)⁻¹) * (x ^ γ / (C + 1)) := by gcongr
      _ = C / (C + 1) := by field_simp
      _ < 1 := by
        rw [div_lt_one (by linarith : 0 < C + 1)]
        linarith
  have haffpos : 0 < (3 * Real.log x + 2) ^ 2 := by positivity
  rw [lt_div_iff₀ haffpos]
  exact hprod

/-- One logarithm times a strictly negative residual real power tends to
zero.  The displayed normalization is the one obtained after replacing
`1 / ε` by `log x / log 2`. -/
theorem tendsto_rpow_mul_powerBenefit_div_log_two
    (C γ α : ℝ) (hαγ : α < γ) :
    Tendsto
      (fun x : ℝ ↦
        x ^ α * (C * x ^ (-γ) * Real.log x / Real.log 2))
      atTop (𝓝 0) := by
  have hs : 0 < γ - α := sub_pos.mpr hαγ
  have hbase : Tendsto
      (fun x : ℝ ↦ Real.log x / x ^ (γ - α)) atTop (𝓝 0) :=
    (isLittleO_log_rpow_atTop hs).tendsto_div_nhds_zero
  have hmul := hbase.const_mul (C / Real.log 2)
  have hmul' : Tendsto
      (fun x : ℝ ↦ (C / Real.log 2) *
        (Real.log x / x ^ (γ - α))) atTop (𝓝 0) := by
    simpa using hmul
  apply hmul'.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
  symm
  calc
    x ^ α * (C * x ^ (-γ) * Real.log x / Real.log 2) =
        (C / Real.log 2) * Real.log x * (x ^ α * x ^ (-γ)) := by ring
    _ = (C / Real.log 2) * Real.log x * x ^ (-(γ - α)) := by
      rw [← Real.rpow_add hx]
      congr 2
      ring
    _ = (C / Real.log 2) * (Real.log x / x ^ (γ - α)) := by
      rw [Real.rpow_neg hx.le]
      ring

theorem eventually_powerBenefit_zone_width_lt_one
    (C γ α : ℝ) (hC : 0 ≤ C) (hγ : 0 < γ) (hαγ : α < γ) :
    ∀ᶠ x : ℝ in atTop,
      0 ≤ C * x ^ (-γ) * Real.log x / Real.log 2 ∧
      C * x ^ (-γ) * Real.log x / Real.log 2 ≤ 1 ∧
      4 * x ^ α *
        (C * x ^ (-γ) * Real.log x / Real.log 2) < 1 := by
  have ht := tendsto_rpow_mul_powerBenefit_div_log_two C γ 0 (by linarith)
  have hw := tendsto_rpow_mul_powerBenefit_div_log_two (4 * C) γ α hαγ
  filter_upwards [eventually_gt_atTop (1 : ℝ),
      ht.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1)),
      hw.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1))]
      with x hx htOne hwOne
  have hlogx : 0 ≤ Real.log x := (Real.log_pos hx).le
  have hxpos : 0 < x := zero_lt_one.trans hx
  have htNonneg :
      0 ≤ C * x ^ (-γ) * Real.log x / Real.log 2 := by positivity
  have hxZero : x ^ (0 : ℝ) = 1 := Real.rpow_zero x
  have htOne' : C * x ^ (-γ) * Real.log x / Real.log 2 < 1 := by
    simpa only [hxZero, one_mul] using htOne
  have hwOne' :
      4 * x ^ α *
          (C * x ^ (-γ) * Real.log x / Real.log 2) < 1 := by
    have heq :
        x ^ α * ((4 * C) * x ^ (-γ) * Real.log x / Real.log 2) =
          4 * x ^ α *
            (C * x ^ (-γ) * Real.log x / Real.log 2) := by ring
    rwa [heq] at hwOne
  exact ⟨htNonneg, htOne'.le, hwOne'⟩

theorem canonicalExponent_raise_step_nonneg {ε : ℝ} (hε : 0 < ε) {p b : ℕ}
    (hp : p.Prime) (hab : canonicalExponent ε p ≤ b) :
    0 ≤ localBenefit ε p b (b + 1) := by
  rw [localBenefit_raise]
  have hthreshold := canonicalExponent_raise_threshold hε hp
  have hmono := log_one_add_inv_succ_antitone hab
  linarith

theorem canonicalExponent_lower_step_nonneg {ε : ℝ} (hε : 0 < ε) {p b : ℕ}
    (hp : p.Prime) (hba : b < canonicalExponent ε p) :
    0 ≤ localBenefit ε p (b + 1) b := by
  rw [localBenefit_lower]
  have ha : 0 < canonicalExponent ε p := hba.trans_le' (Nat.zero_le b)
  have hthreshold := canonicalExponent_lower_threshold hε hp ha
  have hsucc : b + 1 ≤ canonicalExponent ε p := hba
  have hden : (0 : ℝ) < (b + 1 : ℕ) := by positivity
  have hcast : ((b + 1 : ℕ) : ℝ) ≤ (canonicalExponent ε p : ℝ) := by
    exact_mod_cast hsucc
  have hinv : 1 / (canonicalExponent ε p : ℝ) ≤ 1 / ((b + 1 : ℕ) : ℝ) :=
    one_div_le_one_div_of_le hden hcast
  have hmono : Real.log (1 + 1 / (canonicalExponent ε p : ℝ)) ≤
      Real.log (1 + 1 / ((b + 1 : ℕ) : ℝ)) := by
    apply Real.log_le_log
    · positivity
    · exact add_le_add_right hinv 1
  linarith

theorem canonicalExponent_primewiseOptimal {ε : ℝ} (hε : 0 < ε) {p : ℕ}
    (hp : p.Prime) :
    PrimeExponentOptimal ε p (canonicalExponent ε p) := by
  intro b
  rcases le_total (canonicalExponent ε p) b with hab | hba
  · exact Nat.le_induction (m := canonicalExponent ε p)
      (by simp [localBenefit])
      (fun n han ih ↦ by
        rw [localBenefit_cocycle ε p (canonicalExponent ε p) n (n + 1)]
        exact add_nonneg ih (canonicalExponent_raise_step_nonneg hε hp han))
      b hab
  · exact Nat.decreasingInduction (n := canonicalExponent ε p)
      (motive := fun n _ ↦ 0 ≤ localBenefit ε p (canonicalExponent ε p) n)
      (fun k hk ih ↦ by
        rw [localBenefit_cocycle ε p (canonicalExponent ε p) (k + 1) k]
        exact add_nonneg ih (canonicalExponent_lower_step_nonneg hε hp hk))
      (by simp [localBenefit]) hba

/-- The only locally optimal exponents are the canonical floor exponent and,
at an equality threshold, its immediate predecessor.  This is the exact
coordinatewise description of all tied superior numbers. -/
theorem primeExponentOptimal_iff_canonical_or_tiedLower {ε : ℝ}
    (hε : 0 < ε) {p b : ℕ} (hp : p.Prime) :
    PrimeExponentOptimal ε p b ↔
      b = canonicalExponent ε p ∨
        (b + 1 = canonicalExponent ε p ∧
          ε * Real.log p =
            Real.log (1 + 1 / (canonicalExponent ε p : ℝ))) := by
  let a := canonicalExponent ε p
  constructor
  · intro hopt
    have hba : b ≤ a := by
      by_contra hnot
      have hab : a < b := Nat.lt_of_not_ge hnot
      have hbpos : 0 < b := lt_of_le_of_lt (Nat.zero_le a) hab
      have hlower := hopt.lower_threshold hbpos
      have hraise := canonicalExponent_raise_threshold_strict hε hp
      have hmono := log_one_add_inv_nat_antitone (Nat.succ_pos a) hab
      dsimp [a] at hab hbpos hlower hraise hmono ⊢
      linarith
    have hab : a ≤ b + 1 := by
      by_contra hnot
      have hlt : b + 1 < a := Nat.lt_of_not_ge hnot
      have ha : 0 < a := (Nat.succ_pos b).trans hlt
      have hraise := hopt.raise_threshold
      have hlower := canonicalExponent_lower_threshold hε hp (by
        simpa [a] using ha)
      have hstrict := log_one_add_inv_nat_strictAnti (Nat.succ_pos b) hlt
      dsimp [a] at hlt ha hraise hlower hstrict ⊢
      linarith
    by_cases hbaeq : b = a
    · exact Or.inl hbaeq
    · right
      have hraise := hopt.raise_threshold
      have hlower := canonicalExponent_lower_threshold hε hp (by omega)
      have hsucc : b + 1 = a := by omega
      have hsucc' : b + 1 = canonicalExponent ε p := by simpa [a] using hsucc
      refine ⟨hsucc', ?_⟩
      rw [← hsucc'] at hlower ⊢
      linarith
  · rintro (rfl | ⟨hpred, heq⟩)
    · exact canonicalExponent_primewiseOptimal hε hp
    · intro c
      let a := canonicalExponent ε p
      have hb : b + 1 = a := hpred
      have heq' : ε * Real.log p = Real.log (1 + 1 / (a : ℝ)) := by
        simpa [a] using heq
      have hzero : localBenefit ε p a b = 0 := by
        have hformula := localBenefit_lower ε p b
        rw [hb] at hformula
        rw [hformula, heq']
        ring
      have hcanonical : 0 ≤ localBenefit ε p a c := by
        dsimp [a]
        exact canonicalExponent_primewiseOptimal hε hp c
      have hcocycle := localBenefit_cocycle ε p a b c
      rw [hzero, zero_add] at hcocycle
      rwa [← hcocycle]

theorem canonicalExponent_eq_zero_of_two_lt_rpow {ε : ℝ} {p : ℕ}
    (hp : 2 < (p : ℝ) ^ ε) : canonicalExponent ε p = 0 := by
  rw [canonicalExponent, Nat.floor_eq_zero]
  have hden : 0 < (p : ℝ) ^ ε - 1 := by linarith
  rw [div_lt_one₀ hden]
  linarith

/-- An explicit finite support cutoff for the canonical exponent vector. -/
noncomputable def canonicalSupportBound (ε : ℝ) : ℕ :=
  ⌈Real.exp (Real.log 2 / ε)⌉₊ + 1

theorem two_lt_rpow_of_canonicalSupportBound_le {ε : ℝ} (hε : 0 < ε)
    {p : ℕ} (hp : canonicalSupportBound ε ≤ p) :
    2 < (p : ℝ) ^ ε := by
  have hscalePos : 0 < Real.exp (Real.log 2 / ε) := Real.exp_pos _
  have hscaleCeil : Real.exp (Real.log 2 / ε) ≤
      (⌈Real.exp (Real.log 2 / ε)⌉₊ : ℝ) := Nat.le_ceil _
  have hceilSucc : (⌈Real.exp (Real.log 2 / ε)⌉₊ : ℝ) <
      (canonicalSupportBound ε : ℝ) := by
    rw [canonicalSupportBound]
    exact_mod_cast Nat.lt_succ_self ⌈Real.exp (Real.log 2 / ε)⌉₊
  have hscaleP : Real.exp (Real.log 2 / ε) < (p : ℝ) := by
    exact hscaleCeil.trans_lt (hceilSucc.trans_le (by exact_mod_cast hp))
  have hpPos : (0 : ℝ) < p := hscalePos.trans hscaleP
  have hlog : Real.log 2 / ε < Real.log p := by
    simpa using Real.log_lt_log hscalePos hscaleP
  have hlogScaled : Real.log 2 < Real.log p * ε :=
    (div_lt_iff₀ hε).mp hlog
  rw [Real.rpow_def_of_pos hpPos, ← Real.exp_log (by norm_num : (0 : ℝ) < 2)]
  exact Real.exp_lt_exp.mpr hlogScaled

theorem canonicalExponent_eq_zero_of_canonicalSupportBound_le {ε : ℝ}
    (hε : 0 < ε) {p : ℕ} (hp : canonicalSupportBound ε ≤ p) :
    canonicalExponent ε p = 0 :=
  canonicalExponent_eq_zero_of_two_lt_rpow
    (two_lt_rpow_of_canonicalSupportBound_le hε hp)

theorem canonicalExponent_antitone {ε δ : ℝ} (hε : 0 < ε) (hεδ : ε ≤ δ)
    {p : ℕ} (hp : p.Prime) :
    canonicalExponent δ p ≤ canonicalExponent ε p := by
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
  have hpowε : (1 : ℝ) < (p : ℝ) ^ ε := Real.one_lt_rpow hp1 hε
  have hδ : 0 < δ := hε.trans_le hεδ
  have hpowδ : (1 : ℝ) < (p : ℝ) ^ δ := Real.one_lt_rpow hp1 hδ
  have hpow : (p : ℝ) ^ ε ≤ (p : ℝ) ^ δ :=
    Real.rpow_le_rpow_of_exponent_le hp1.le hεδ
  have hinv : 1 / ((p : ℝ) ^ δ - 1) ≤ 1 / ((p : ℝ) ^ ε - 1) :=
    one_div_le_one_div_of_le (sub_pos.mpr hpowε) (sub_le_sub_right hpow 1)
  exact Nat.floor_mono hinv

/-- The finitely supported vector of canonical exponents, zeroed away from
the primes. -/
noncomputable def canonicalFactorization (ε : ℝ) (hε : 0 < ε) : ℕ →₀ ℕ :=
  Finsupp.onFinset (Finset.range (canonicalSupportBound ε))
    (fun p ↦ if p.Prime then canonicalExponent ε p else 0) (by
      intro p hpne
      by_contra hpRange
      have hpge : canonicalSupportBound ε ≤ p := by
        simpa [Finset.mem_range, not_lt] using hpRange
      by_cases hpPrime : p.Prime
      · exact hpne (by simp [hpPrime,
          canonicalExponent_eq_zero_of_canonicalSupportBound_le hε hpge])
      · exact hpne (by simp [hpPrime]))

@[simp] theorem canonicalFactorization_apply (ε : ℝ) (hε : 0 < ε) (p : ℕ) :
    canonicalFactorization ε hε p =
      if p.Prime then canonicalExponent ε p else 0 := by
  simp [canonicalFactorization]

theorem canonicalFactorization_prime_support (ε : ℝ) (hε : 0 < ε) :
    ∀ p ∈ (canonicalFactorization ε hε).support, p.Prime := by
  intro p hp
  have hpne := Finsupp.mem_support_iff.mp hp
  by_cases hpPrime : p.Prime
  · exact hpPrime
  · simp [canonicalFactorization_apply, hpPrime] at hpne

theorem canonicalFactorization_antitone {ε δ : ℝ} (hε : 0 < ε) (hεδ : ε ≤ δ) :
    canonicalFactorization δ (hε.trans_le hεδ) ≤ canonicalFactorization ε hε := by
  intro p
  by_cases hp : p.Prime
  · simpa only [canonicalFactorization_apply, if_pos hp] using
      canonicalExponent_antitone hε hεδ hp
  · simp only [canonicalFactorization_apply, if_neg hp]
    exact le_rfl

/-- The canonical superior highly composite integer at parameter `ε`. -/
noncomputable def canonicalSuperior (ε : ℝ) (hε : 0 < ε) : ℕ :=
  fromFactorization (canonicalFactorization ε hε)

theorem canonicalSuperior_dvd_of_le_parameter {ε δ : ℝ} (hε : 0 < ε)
    (hεδ : ε ≤ δ) :
    canonicalSuperior δ (hε.trans_le hεδ) ∣ canonicalSuperior ε hε := by
  rw [canonicalSuperior, canonicalSuperior]
  apply Nat.prod_pow_dvd_of_le_factorization
  rw [factorization_fromFactorization (canonicalFactorization_prime_support ε hε)]
  exact canonicalFactorization_antitone hε hεδ

theorem superior_benefit_nonneg {ε : ℝ} {N M : ℕ} (hN : Superior ε N)
    (hM : 0 < M) : 0 ≤ benefit ε N M := hN.2 M hM

theorem superiorScore_pos (ε : ℝ) {n : ℕ} (hn : n ≠ 0) :
    0 < superiorScore ε n := by
  exact mul_pos (by exact_mod_cast tau_pos hn) (Real.exp_pos _)

/-- The global benefit is exactly the sum of its primewise contributions. -/
theorem benefit_eq_factorizationBenefit {ε : ℝ} {N M : ℕ}
    (hN : N ≠ 0) (hM : M ≠ 0) :
    benefit ε N M = factorizationBenefit ε N M := by
  let S : Finset ℕ := N.primeFactors ∪ M.primeFactors
  have hlogN : Real.log N =
      ∑ p ∈ S, (N.factorization p : ℝ) * Real.log p :=
    log_nat_eq_sum_factorization_on N S Finset.subset_union_left
  have hlogM : Real.log M =
      ∑ p ∈ S, (M.factorization p : ℝ) * Real.log p :=
    log_nat_eq_sum_factorization_on M S Finset.subset_union_right
  have hlogTauN : Real.log (tau N : ℝ) =
      ∑ p ∈ S, Real.log (N.factorization p + 1 : ℕ) :=
    log_tau_eq_sum_factorization_on hN S Finset.subset_union_left
  have hlogTauM : Real.log (tau M : ℝ) =
      ∑ p ∈ S, Real.log (M.factorization p + 1 : ℕ) :=
    log_tau_eq_sum_factorization_on hM S Finset.subset_union_right
  have hNreal : (N : ℝ) ≠ 0 := by exact_mod_cast hN
  have hMreal : (M : ℝ) ≠ 0 := by exact_mod_cast hM
  have htauN : (tau N : ℝ) ≠ 0 := by exact_mod_cast (tau_pos hN).ne'
  have htauM : (tau M : ℝ) ≠ 0 := by exact_mod_cast (tau_pos hM).ne'
  rw [benefit, Real.log_div hMreal hNreal, Real.log_div htauM htauN,
    hlogM, hlogN, hlogTauM, hlogTauN]
  change _ = ∑ p ∈ S, localBenefit ε p (N.factorization p) (M.factorization p)
  simp only [localBenefit]
  have hlogSuccDiv (a b : ℕ) :
      Real.log (((b + 1 : ℕ) : ℝ) / ((a + 1 : ℕ) : ℝ)) =
        Real.log (b + 1 : ℕ) - Real.log (a + 1 : ℕ) := by
    rw [Real.log_div]
    · exact_mod_cast Nat.succ_ne_zero b
    · exact_mod_cast Nat.succ_ne_zero a
  simp_rw [hlogSuccDiv]
  push_cast
  have hpoint (p : ℕ) :
      ε * ((M.factorization p : ℝ) - (N.factorization p : ℝ)) * Real.log p =
        ε * ((M.factorization p : ℝ) * Real.log p) -
          ε * ((N.factorization p : ℝ) * Real.log p) := by ring
  simp_rw [hpoint]
  repeat rw [Finset.sum_sub_distrib]
  repeat rw [← Finset.mul_sum]
  ring

theorem benefit_eq_log_superiorScore_sub {ε : ℝ} {N M : ℕ}
    (hN : N ≠ 0) (hM : M ≠ 0) :
    benefit ε N M =
      Real.log (superiorScore ε N) - Real.log (superiorScore ε M) := by
  have htauN : (tau N : ℝ) ≠ 0 := by exact_mod_cast (tau_pos hN).ne'
  have htauM : (tau M : ℝ) ≠ 0 := by exact_mod_cast (tau_pos hM).ne'
  have hNreal : (N : ℝ) ≠ 0 := by exact_mod_cast hN
  have hMreal : (M : ℝ) ≠ 0 := by exact_mod_cast hM
  rw [benefit, superiorScore, superiorScore,
    Real.log_mul htauN (Real.exp_ne_zero _),
    Real.log_mul htauM (Real.exp_ne_zero _), Real.log_exp, Real.log_exp,
    Real.log_div hMreal hNreal, Real.log_div htauM htauN]
  ring

theorem superior_iff_score_max {ε : ℝ} {N : ℕ} :
    Superior ε N ↔
      0 < N ∧ ∀ M : ℕ, 0 < M → superiorScore ε M ≤ superiorScore ε N := by
  constructor
  · intro hN
    refine ⟨hN.1, ?_⟩
    intro M hM
    have hbenefit := hN.2 M hM
    rw [benefit_eq_log_superiorScore_sub hN.1.ne' hM.ne', sub_nonneg,
      Real.log_le_log_iff (superiorScore_pos ε hM.ne')
        (superiorScore_pos ε hN.1.ne')] at hbenefit
    exact hbenefit
  · rintro ⟨hN, hmax⟩
    refine ⟨hN, ?_⟩
    intro M hM
    rw [benefit_eq_log_superiorScore_sub hN.ne' hM.ne', sub_nonneg,
      Real.log_le_log_iff (superiorScore_pos ε hM.ne')
        (superiorScore_pos ε hN.ne')]
    exact hmax M hM

/-- Global optimality forces every prime exponent to be locally optimal.
This is the source of the nonnegativity of each summand in Nicolas's
benefit decomposition. -/
theorem localBenefit_nonneg_of_superior {ε : ℝ} {N p : ℕ}
    (hN : Superior ε N) (hp : p.Prime) (b : ℕ) :
    0 ≤ localBenefit ε p (N.factorization p) b := by
  let f : ℕ →₀ ℕ := N.factorization.update p b
  have hf : ∀ r ∈ f.support, r.Prime := by
    intro r hr
    have hr' : r ∈ insert p N.factorization.support :=
      Finsupp.support_update_subset (f := N.factorization) (a := p) (b := b) hr
    rcases Finset.mem_insert.mp hr' with rfl | hrN
    · exact hp
    · exact Nat.prime_of_mem_primeFactors hrN
  let M : ℕ := fromFactorization f
  have hMpos : 0 < M := fromFactorization_pos hf
  have hMfact : M.factorization = f := factorization_fromFactorization hf
  have hbenefit : 0 ≤ benefit ε N M := hN.2 M hMpos
  rw [benefit_eq_factorizationBenefit hN.1.ne' hMpos.ne'] at hbenefit
  have hsum : factorizationBenefit ε N M =
      localBenefit ε p (N.factorization p) b := by
    rw [factorizationBenefit]
    rw [← Nat.support_factorization N, ← Nat.support_factorization M, hMfact]
    by_cases hpmem : p ∈ N.factorization.support ∪ f.support
    · rw [Finset.sum_eq_single_of_mem p hpmem]
      · simp [f]
      · intro r hr hrp
        have hfr : f r = N.factorization r := by
          simp [f, Finsupp.update_apply, hrp]
        simp [hfr, localBenefit]
    · have hpN : p ∉ N.factorization.support := by
        intro hpN
        exact hpmem (Finset.mem_union_left _ hpN)
      have hpf : p ∉ f.support := by
        intro hpf
        exact hpmem (Finset.mem_union_right _ hpf)
      have ha : N.factorization p = 0 := Finsupp.notMem_support_iff.mp hpN
      have hb : b = 0 := by
        have := Finsupp.notMem_support_iff.mp hpf
        simpa [f] using this
      have hf_eq : f = N.factorization := by
        dsimp [f]
        rw [hb]
        simpa [ha] using Finsupp.update_self N.factorization p
      simp [hf_eq, ha, hb, localBenefit]
  rwa [hsum] at hbenefit

theorem Superior.primeExponentOptimal {ε : ℝ} {N p : ℕ}
    (hN : Superior ε N) (hp : p.Prime) :
    PrimeExponentOptimal ε p (N.factorization p) := by
  intro b
  exact localBenefit_nonneg_of_superior hN hp b

/-- Conversely, independently optimal exponents assemble to a superior
integer.  This is the formal primewise maximization principle. -/
theorem superior_from_primewise_optimal {ε : ℝ} {f : ℕ →₀ ℕ}
    (hf : ∀ p ∈ f.support, p.Prime)
    (hopt : ∀ p : ℕ, p.Prime → PrimeExponentOptimal ε p (f p)) :
    Superior ε (fromFactorization f) := by
  have hNpos : 0 < fromFactorization f := fromFactorization_pos hf
  refine ⟨hNpos, ?_⟩
  intro M hM
  rw [benefit_eq_factorizationBenefit hNpos.ne' hM.ne', factorizationBenefit,
    factorization_fromFactorization hf]
  apply Finset.sum_nonneg
  intro p hpUnion
  have hp : p.Prime := by
    rcases Finset.mem_union.mp hpUnion with hpN | hpM
    · exact Nat.prime_of_mem_primeFactors hpN
    · exact Nat.prime_of_mem_primeFactors hpM
  exact hopt p hp (M.factorization p)

/-- Each local contribution is not only nonnegative; it is bounded by the
whole benefit of the comparison integer. -/
theorem localBenefit_le_benefit_of_superior {ε : ℝ} {N M p : ℕ}
    (hN : Superior ε N) (hM : 0 < M) :
    localBenefit ε p (N.factorization p) (M.factorization p) ≤ benefit ε N M := by
  rw [benefit_eq_factorizationBenefit hN.1.ne' hM.ne', factorizationBenefit]
  let S : Finset ℕ := N.primeFactors ∪ M.primeFactors
  change localBenefit ε p (N.factorization p) (M.factorization p) ≤
    ∑ r ∈ S, localBenefit ε r (N.factorization r) (M.factorization r)
  have hterms : ∀ r ∈ S,
      0 ≤ localBenefit ε r (N.factorization r) (M.factorization r) := by
    intro r hr
    have hrprime : r.Prime := by
      rcases Finset.mem_union.mp hr with hrN | hrM
      · exact Nat.prime_of_mem_primeFactors hrN
      · exact Nat.prime_of_mem_primeFactors hrM
    exact localBenefit_nonneg_of_superior hN hrprime (M.factorization r)
  by_cases hpS : p ∈ S
  · apply Finset.single_le_sum (s := S) (f := fun r ↦
      localBenefit ε r (N.factorization r) (M.factorization r))
    · exact hterms
    · exact hpS
  · have hpN : p ∉ N.factorization.support := by
      rw [Nat.support_factorization]
      intro hpN
      exact hpS (Finset.mem_union_left _ hpN)
    have hpM : p ∉ M.factorization.support := by
      rw [Nat.support_factorization]
      intro hpM
      exact hpS (Finset.mem_union_right _ hpM)
    have ha : N.factorization p = 0 := Finsupp.notMem_support_iff.mp hpN
    have hb : M.factorization p = 0 := Finsupp.notMem_support_iff.mp hpM
    simpa [ha, hb, localBenefit] using Finset.sum_nonneg hterms

/-- A benefit smaller than both two-step convexity losses forces the exponent
of a comparison integer to stay within one of the superior exponent. -/
theorem factorization_within_one_of_benefit_lt_two_step_losses
    {ε : ℝ} {N M p : ℕ} (hN : Superior ε N) (hM : 0 < M)
    (hp : p.Prime)
    (hup : benefit ε N M <
      Real.log (1 + 1 / ((N.factorization p + 1 : ℕ) : ℝ)) -
        Real.log (1 + 1 / ((N.factorization p + 2 : ℕ) : ℝ)))
    (hdown : benefit ε N M <
      Real.log (1 + 1 / ((N.factorization p - 1 : ℕ) : ℝ)) -
        Real.log (1 + 1 / (N.factorization p : ℝ))) :
    M.factorization p ≤ N.factorization p + 1 ∧
      N.factorization p ≤ M.factorization p + 1 := by
  let a := N.factorization p
  let b := M.factorization p
  have hopt : PrimeExponentOptimal ε p a := by
    intro c
    exact localBenefit_nonneg_of_superior hN hp c
  have hlocal := localBenefit_le_benefit_of_superior (p := p) hN hM
  constructor
  · by_contra hnot
    have hab : a + 2 ≤ b := by omega
    have hloss := hopt.two_raise_loss_le hab
    dsimp [a, b] at hloss hlocal ⊢
    linarith
  · by_contra hnot
    have hab : b + 2 ≤ a := by omega
    have hloss := hopt.two_lower_loss_le hab
    dsimp [a, b] at hloss hlocal ⊢
    linarith

/-- Exact upper localization inequality when one prime exponent is raised by
one relative to a superior anchor. -/
theorem factorization_raise_zone {ε : ℝ} {N M p : ℕ}
    (hN : Superior ε N) (hM : 0 < M)
    (hp : p.Prime)
    (hraise : M.factorization p = N.factorization p + 1) :
    0 ≤ ε * Real.log p -
        Real.log (1 + 1 / ((N.factorization p + 1 : ℕ) : ℝ)) ∧
      ε * Real.log p -
          Real.log (1 + 1 / ((N.factorization p + 1 : ℕ) : ℝ)) ≤
        benefit ε N M := by
  have hnonneg := localBenefit_nonneg_of_superior hN hp
    (N.factorization p + 1)
  have hle := localBenefit_le_benefit_of_superior (p := p) hN hM
  rw [hraise, localBenefit_raise] at hle
  rw [localBenefit_raise] at hnonneg
  exact ⟨hnonneg, hle⟩

/-- Exact upper localization inequality when one prime exponent is lowered by
one relative to a superior anchor. -/
theorem factorization_lower_zone {ε : ℝ} {N M p : ℕ}
    (hN : Superior ε N) (hM : 0 < M)
    (hp : p.Prime)
    (hlower : M.factorization p + 1 = N.factorization p) :
    0 ≤ Real.log (1 + 1 / (N.factorization p : ℝ)) -
        ε * Real.log p ∧
      Real.log (1 + 1 / (N.factorization p : ℝ)) -
          ε * Real.log p ≤ benefit ε N M := by
  have ha : 0 < N.factorization p := by omega
  have hpred : N.factorization p - 1 + 1 = N.factorization p :=
    Nat.sub_add_cancel ha
  have hMpred : M.factorization p = N.factorization p - 1 := by omega
  have hnonneg := localBenefit_nonneg_of_superior hN hp
    (N.factorization p - 1)
  have hle := localBenefit_le_benefit_of_superior (p := p) hN hM
  have hnonneg' :
      0 ≤ localBenefit ε p (N.factorization p - 1 + 1)
        (N.factorization p - 1) := by
    simpa only [hpred] using hnonneg
  rw [localBenefit_lower] at hnonneg'
  simp only [hpred] at hnonneg'
  rw [hMpred] at hle
  have hle' :
      localBenefit ε p (N.factorization p - 1 + 1)
          (N.factorization p - 1) ≤ benefit ε N M := by
    simpa only [hpred] using hle
  rw [localBenefit_lower] at hle'
  simp only [hpred] at hle'
  exact ⟨hnonneg', hle'⟩

/-- If level membership of a prime changes between a superior anchor and a
comparison integer whose exponents are within one, then that prime lies in
the exact benefit-width zone around the level threshold.  This is the
pointwise statement behind the finite boundary certificate. -/
theorem abs_threshold_error_le_benefit_of_level_change
    {ε : ℝ} {N M p k : ℕ}
    (hN : Superior ε N) (hM : 0 < M) (hp : p.Prime) (_hk : 0 < k)
    (hwithin : M.factorization p ≤ N.factorization p + 1 ∧
      N.factorization p ≤ M.factorization p + 1)
    (hchange :
      (k ≤ M.factorization p ∧ ¬k ≤ N.factorization p) ∨
        (k ≤ N.factorization p ∧ ¬k ≤ M.factorization p)) :
    |ε * Real.log p - Real.log (1 + 1 / (k : ℝ))| ≤
      benefit ε N M := by
  rcases hchange with hraise | hlower
  · have haEq : N.factorization p + 1 = k := by omega
    have hbEq : M.factorization p = k := by omega
    have hstep : M.factorization p = N.factorization p + 1 := by omega
    obtain ⟨hzero, hle⟩ := factorization_raise_zone hN hM hp hstep
    rw [haEq] at hzero hle
    rw [abs_of_nonneg hzero]
    simpa only [Nat.cast_ofNat] using hle
  · have haEq : N.factorization p = k := by omega
    have hbEq : M.factorization p + 1 = k := by omega
    have hstep : M.factorization p + 1 = N.factorization p := by omega
    obtain ⟨hzero, hle⟩ := factorization_lower_zone hN hM hp hstep
    rw [haEq] at hzero hle
    have hnonpos :
        ε * Real.log p - Real.log (1 + 1 / (k : ℝ)) ≤ 0 := by
      linarith
    rw [abs_of_nonpos hnonpos]
    linarith

theorem Superior.raise_threshold {ε : ℝ} {N p : ℕ} (hN : Superior ε N)
    (hp : p.Prime) :
    Real.log (1 + 1 / ((N.factorization p + 1 : ℕ) : ℝ)) ≤
      ε * Real.log p := by
  have hlocal := localBenefit_nonneg_of_superior hN hp (N.factorization p + 1)
  rw [localBenefit_raise] at hlocal
  linarith

theorem Superior.lower_threshold {ε : ℝ} {N p : ℕ} (hN : Superior ε N)
    (hp : p.Prime) (hpos : 0 < N.factorization p) :
    ε * Real.log p ≤ Real.log (1 + 1 / (N.factorization p : ℝ)) := by
  have hlocal := localBenefit_nonneg_of_superior hN hp (N.factorization p - 1)
  have hsucc : N.factorization p - 1 + 1 = N.factorization p :=
    Nat.sub_add_cancel hpos
  have hlocal' :
      0 ≤ localBenefit ε p (N.factorization p - 1 + 1) (N.factorization p - 1) := by
    simpa only [hsucc] using hlocal
  rw [localBenefit_lower] at hlocal'
  simp only [hsucc] at hlocal'
  linarith

/-- Nicolas's record-property comparison for benefits. -/
theorem benefit_comparison {ε : ℝ} (hε : 0 ≤ ε) {N A M M' : ℕ}
    (hN : 0 < N) (hA : HighlyComposite A) (hM : 0 < M) (hM' : 0 < M')
    (hMA : tau M ≤ tau A) (hAM' : tau A ≤ tau M') :
    benefit ε N A ≤ benefit ε N M' +
      Real.log ((tau M' : ℝ) / (tau M : ℝ)) := by
  have hAleM' : A ≤ M' := by
    by_contra hnot
    have hlt : M' < A := Nat.lt_of_not_ge hnot
    have := hA.2 M' hM' hlt
    omega
  have hlogA : Real.log (A : ℝ) ≤ Real.log (M' : ℝ) := by
    apply Real.log_le_log
    · exact_mod_cast hA.1
    · exact_mod_cast hAleM'
  have hlogTau : Real.log (tau M : ℝ) ≤ Real.log (tau A : ℝ) := by
    apply Real.log_le_log
    · exact_mod_cast tau_pos hM.ne'
    · exact_mod_cast hMA
  have hscaled :
      ε * (Real.log (A : ℝ) - Real.log (N : ℝ)) ≤
        ε * (Real.log (M' : ℝ) - Real.log (N : ℝ)) := by
    exact mul_le_mul_of_nonneg_left (sub_le_sub_right hlogA _) hε
  have hN0 : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  have hA0 : (A : ℝ) ≠ 0 := by exact_mod_cast hA.1.ne'
  have hM'0 : (M' : ℝ) ≠ 0 := by exact_mod_cast hM'.ne'
  have htauN0 : (tau N : ℝ) ≠ 0 := by exact_mod_cast (tau_pos hN.ne').ne'
  have htauA0 : (tau A : ℝ) ≠ 0 := by exact_mod_cast (tau_pos hA.1.ne').ne'
  have htauM0 : (tau M : ℝ) ≠ 0 := by exact_mod_cast (tau_pos hM.ne').ne'
  have htauM'0 : (tau M' : ℝ) ≠ 0 := by exact_mod_cast (tau_pos hM'.ne').ne'
  rw [benefit, benefit, Real.log_div hA0 hN0, Real.log_div hM'0 hN0,
    Real.log_div htauA0 htauN0, Real.log_div htauM'0 htauN0,
    Real.log_div htauM'0 htauM0]
  linarith

/-- A superior number at a positive parameter is a strict divisor-count
record.  The strictness comes from the strict decrease of `M^ε` when
`M < N`. -/
theorem Superior.highlyComposite {ε : ℝ} (hε : 0 < ε) {N : ℕ}
    (hN : Superior ε N) : HighlyComposite N := by
  refine ⟨hN.1, ?_⟩
  intro M hM hMN
  by_contra hnot
  have htau : tau N ≤ tau M := Nat.le_of_not_gt hnot
  have htauN : 0 < (tau N : ℝ) := by
    exact_mod_cast tau_pos hN.1.ne'
  have hratioTau : 1 ≤ (tau M : ℝ) / (tau N : ℝ) := by
    rw [one_le_div₀ htauN]
    exact_mod_cast htau
  have hlogTau : 0 ≤ Real.log ((tau M : ℝ) / (tau N : ℝ)) :=
    Real.log_nonneg hratioTau
  have hNreal : 0 < (N : ℝ) := by exact_mod_cast hN.1
  have hMreal : 0 < (M : ℝ) := by exact_mod_cast hM
  have hratioPos : 0 < (M : ℝ) / (N : ℝ) := div_pos hMreal hNreal
  have hratioLt : (M : ℝ) / (N : ℝ) < 1 := by
    rw [div_lt_one₀ hNreal]
    exact_mod_cast hMN
  have hlogRatio : Real.log ((M : ℝ) / (N : ℝ)) < 0 :=
    Real.log_neg hratioPos hratioLt
  have hbenefitNeg : benefit ε N M < 0 := by
    rw [benefit]
    nlinarith [mul_neg_of_pos_of_neg hε hlogRatio]
  exact (not_lt_of_ge (hN.2 M hM)) hbenefitNeg

theorem canonicalSuperior_isSuperior (ε : ℝ) (hε : 0 < ε) :
    Superior ε (canonicalSuperior ε hε) := by
  rw [canonicalSuperior]
  apply superior_from_primewise_optimal (canonicalFactorization_prime_support ε hε)
  intro p hp
  simpa [canonicalFactorization_apply, hp] using
    canonicalExponent_primewiseOptimal hε hp

/-- The integer `1` starts the full superior sequence (for example at
parameter `2`). -/
theorem superior_one : Superior 2 1 := by
  have hε : (0 : ℝ) < 2 := by norm_num
  have hexponent : ∀ p : ℕ, p.Prime → canonicalExponent 2 p = 0 := by
    intro p hp
    apply canonicalExponent_eq_zero_of_two_lt_rpow
    rw [Real.rpow_two]
    have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
    nlinarith
  have hfactorization : canonicalFactorization 2 hε = 0 := by
    ext p
    by_cases hp : p.Prime
    · simp [canonicalFactorization_apply, hp, hexponent p hp]
    · simp [canonicalFactorization_apply, hp]
  have hcanonical : canonicalSuperior 2 hε = 1 := by
    rw [canonicalSuperior, hfactorization, fromFactorization_zero]
  simpa only [hcanonical] using canonicalSuperior_isSuperior 2 hε

theorem canonicalSuperior_highlyComposite (ε : ℝ) (hε : 0 < ε) :
    HighlyComposite (canonicalSuperior ε hε) :=
  (canonicalSuperior_isSuperior ε hε).highlyComposite hε

@[simp] theorem factorization_canonicalSuperior (ε : ℝ) (hε : 0 < ε) :
    (canonicalSuperior ε hε).factorization = canonicalFactorization ε hε := by
  rw [canonicalSuperior]
  exact factorization_fromFactorization (canonicalFactorization_prime_support ε hε)

/-- Every coordinate of an arbitrary superior number is either the canonical
coordinate or the tied coordinate immediately below it. -/
theorem Superior.factorization_eq_canonical_or_tiedLower {ε : ℝ}
    (hε : 0 < ε) {N p : ℕ} (hN : Superior ε N) (hp : p.Prime) :
    N.factorization p = canonicalExponent ε p ∨
      (N.factorization p + 1 = canonicalExponent ε p ∧
        ε * Real.log p =
          Real.log (1 + 1 / (canonicalExponent ε p : ℝ))) := by
  exact (primeExponentOptimal_iff_canonical_or_tiedLower hε hp).1
    (hN.primeExponentOptimal hp)

theorem Superior.factorization_le_canonicalFactorization {ε : ℝ}
    (hε : 0 < ε) {N : ℕ} (hN : Superior ε N) :
    N.factorization ≤ canonicalFactorization ε hε := by
  intro p
  by_cases hp : p.Prime
  · rcases hN.factorization_eq_canonical_or_tiedLower hε hp with h | h
    · simp [canonicalFactorization_apply, hp, h]
    · rw [canonicalFactorization_apply, if_pos hp]
      omega
  · simp [canonicalFactorization_apply, hp]

/-- At a fixed positive parameter every superior number divides the canonical
(upper, floor-convention) superior number. -/
theorem Superior.dvd_canonicalSuperior {ε : ℝ} (hε : 0 < ε)
    {N : ℕ} (hN : Superior ε N) : N ∣ canonicalSuperior ε hε := by
  rw [← Nat.factorization_le_iff_dvd hN.1.ne'
    (canonicalSuperior_isSuperior ε hε).1.ne', factorization_canonicalSuperior]
  exact hN.factorization_le_canonicalFactorization hε

/-- Prime coordinates at which both adjacent canonical exponents are
optimal.  The support condition makes this a finite set. -/
noncomputable def tiedPrimes (ε : ℝ) (hε : 0 < ε) : Finset ℕ :=
  (canonicalFactorization ε hε).support.filter fun p ↦
    ε * Real.log p =
      Real.log (1 + 1 / (canonicalExponent ε p : ℝ))

/-- The set of canonical prime coordinates lowered in a given integer. -/
noncomputable def loweringCode (ε : ℝ) (hε : 0 < ε) (N : ℕ) : Finset ℕ :=
  (canonicalFactorization ε hε).support.filter fun p ↦
    N.factorization p < canonicalExponent ε p

theorem mem_loweringCode_iff_of_superior {ε : ℝ} (hε : 0 < ε)
    {N p : ℕ} (hN : Superior ε N) (hp : p.Prime) :
    p ∈ loweringCode ε hε N ↔
      N.factorization p + 1 = canonicalExponent ε p := by
  constructor
  · intro hmem
    rw [loweringCode, Finset.mem_filter] at hmem
    rcases hN.factorization_eq_canonical_or_tiedLower hε hp with heq | hlower
    · omega
    · exact hlower.1
  · intro hlower
    rw [loweringCode, Finset.mem_filter]
    have hapos : 0 < canonicalExponent ε p := by omega
    refine ⟨?_, by omega⟩
    rw [Finsupp.mem_support_iff, canonicalFactorization_apply, if_pos hp]
    exact hapos.ne'

theorem loweringCode_subset_tiedPrimes {ε : ℝ} (hε : 0 < ε)
    {N : ℕ} (hN : Superior ε N) :
    loweringCode ε hε N ⊆ tiedPrimes ε hε := by
  intro p hpCode
  rw [loweringCode, Finset.mem_filter] at hpCode
  have hp : p.Prime := canonicalFactorization_prime_support ε hε p hpCode.1
  rw [tiedPrimes, Finset.mem_filter]
  refine ⟨hpCode.1, ?_⟩
  rcases hN.factorization_eq_canonical_or_tiedLower hε hp with heq | hlower
  · omega
  · exact hlower.2

theorem loweringCode_injOn_superior (ε : ℝ) (hε : 0 < ε) :
    Set.InjOn (loweringCode ε hε) {N : ℕ | Superior ε N} := by
  intro A hA B hB hcode
  apply Nat.eq_of_factorization_eq hA.1.ne' hB.1.ne'
  intro p
  by_cases hp : p.Prime
  · have hmemA := mem_loweringCode_iff_of_superior hε hA hp
    have hmemB := mem_loweringCode_iff_of_superior hε hB hp
    have hsame :
        (A.factorization p + 1 = canonicalExponent ε p) ↔
          B.factorization p + 1 = canonicalExponent ε p := by
      rw [← hmemA, ← hmemB, hcode]
    rcases hA.factorization_eq_canonical_or_tiedLower hε hp with hAc | hAl <;>
      rcases hB.factorization_eq_canonical_or_tiedLower hε hp with hBc | hBl
    · omega
    · exfalso
      exact hsame.mp (by omega) |>.not_lt (by omega)
    · exfalso
      exact hsame.mpr (by omega) |>.not_lt (by omega)
    · omega
  · simp [hp]

/-- The literal finite set of all superior integers at one parameter. -/
noncomputable def superiorNumbersAt (ε : ℝ) (hε : 0 < ε) : Finset ℕ :=
  (canonicalSuperior ε hε).divisors.filter (Superior ε)

theorem mem_superiorNumbersAt_iff {ε : ℝ} (hε : 0 < ε) {N : ℕ} :
    N ∈ superiorNumbersAt ε hε ↔ Superior ε N := by
  constructor
  · intro hN
    exact (Finset.mem_filter.mp hN).2
  · intro hN
    rw [superiorNumbersAt, Finset.mem_filter]
    exact ⟨Nat.mem_divisors.mpr ⟨hN.dvd_canonicalSuperior hε,
      (canonicalSuperior_isSuperior ε hε).1.ne'⟩, hN⟩

/-- All superior integers at one parameter are encoded injectively by the
subset of tied prime coordinates at which the lower exponent was chosen. -/
theorem card_superiorNumbersAt_le_two_pow_tiedPrimes (ε : ℝ) (hε : 0 < ε) :
    (superiorNumbersAt ε hε).card ≤ 2 ^ (tiedPrimes ε hε).card := by
  calc
    (superiorNumbersAt ε hε).card ≤ (tiedPrimes ε hε).powerset.card := by
      apply Finset.card_le_card_of_injOn (loweringCode ε hε)
      · intro N hN
        exact Finset.mem_powerset.mpr (loweringCode_subset_tiedPrimes hε
          ((mem_superiorNumbersAt_iff hε).1 hN))
      · intro A hA B hB hcode
        exact loweringCode_injOn_superior ε hε
          ((mem_superiorNumbersAt_iff hε).1 hA)
          ((mem_superiorNumbersAt_iff hε).1 hB) hcode
    _ = 2 ^ (tiedPrimes ε hε).card := Finset.card_powerset _

theorem canonicalExponent_anti_prime {ε : ℝ} (hε : 0 < ε)
    {p q : ℕ} (hp : 2 ≤ p) (hpq : p ≤ q) :
    canonicalExponent ε q ≤ canonicalExponent ε p := by
  rw [canonicalExponent, canonicalExponent]
  apply Nat.floor_mono
  have hp0 : (0 : ℝ) ≤ p := by positivity
  have hp1 : (1 : ℝ) < p := by exact_mod_cast (lt_of_lt_of_le (by omega : 1 < 2) hp)
  have hpq' : (p : ℝ) ≤ q := by exact_mod_cast hpq
  have hrpow : (p : ℝ) ^ ε ≤ (q : ℝ) ^ ε :=
    Real.rpow_le_rpow hp0 hpq' hε.le
  apply one_div_le_one_div_of_le
  · exact sub_pos.mpr (Real.one_lt_rpow hp1 hε)
  · linarith

/-- At one parameter, distinct tied primes have distinct canonical
exponents.  Hence there are no more tied coordinates than the exponent of
the smallest prime. -/
theorem card_tiedPrimes_le_canonicalExponent_two (ε : ℝ) (hε : 0 < ε) :
    (tiedPrimes ε hε).card ≤ canonicalExponent ε 2 := by
  let I := Finset.Icc 1 (canonicalExponent ε 2)
  have hcardI : I.card = canonicalExponent ε 2 := by
    simp [I]
  calc
    (tiedPrimes ε hε).card ≤ I.card := by
      apply Finset.card_le_card_of_injOn (canonicalExponent ε)
      · intro p hpTie
        change canonicalExponent ε p ∈ I
        rw [Finset.mem_Icc]
        have hpTie' : p ∈ tiedPrimes ε hε := hpTie
        rw [tiedPrimes, Finset.mem_filter] at hpTie'
        have hpPrime := canonicalFactorization_prime_support ε hε p hpTie'.1
        have hapos : 0 < canonicalExponent ε p := by
          have hne := Finsupp.mem_support_iff.mp hpTie'.1
          rw [canonicalFactorization_apply, if_pos hpPrime] at hne
          omega
        exact ⟨hapos, canonicalExponent_anti_prime hε (by omega) hpPrime.two_le⟩
      · intro p hpTie q hqTie heq
        have hpTie' : p ∈ tiedPrimes ε hε := hpTie
        have hqTie' : q ∈ tiedPrimes ε hε := hqTie
        rw [tiedPrimes, Finset.mem_filter] at hpTie' hqTie'
        have hpPrime := canonicalFactorization_prime_support ε hε p hpTie'.1
        have hqPrime := canonicalFactorization_prime_support ε hε q hqTie'.1
        have hlog : Real.log p = Real.log q := by
          have hpEq := hpTie'.2
          have hqEq := hqTie'.2
          rw [heq] at hpEq
          nlinarith
        have hpPos : (0 : ℝ) < p := by exact_mod_cast hpPrime.pos
        have hqPos : (0 : ℝ) < q := by exact_mod_cast hqPrime.pos
        exact_mod_cast Real.strictMonoOn_log.injOn hpPos hqPos hlog
    _ = canonicalExponent ε 2 := hcardI

theorem canonicalExponent_injOn_tiedPrimes (ε : ℝ) (hε : 0 < ε) :
    Set.InjOn (canonicalExponent ε) (tiedPrimes ε hε) := by
  intro p hpTie q hqTie heq
  have hpTie' : p ∈ tiedPrimes ε hε := hpTie
  have hqTie' : q ∈ tiedPrimes ε hε := hqTie
  rw [tiedPrimes, Finset.mem_filter] at hpTie' hqTie'
  have hpPrime := canonicalFactorization_prime_support ε hε p hpTie'.1
  have hqPrime := canonicalFactorization_prime_support ε hε q hqTie'.1
  have hlog : Real.log p = Real.log q := by
    have hpEq := hpTie'.2
    have hqEq := hqTie'.2
    rw [heq] at hpEq
    nlinarith
  have hpPos : (0 : ℝ) < p := by exact_mod_cast hpPrime.pos
  have hqPos : (0 : ℝ) < q := by exact_mod_cast hqPrime.pos
  exact_mod_cast Real.strictMonoOn_log.injOn hpPos hqPos hlog

noncomputable def loweringExponentCode (ε : ℝ) (hε : 0 < ε)
    (N : ℕ) : Finset ℕ :=
  (loweringCode ε hε N).image (canonicalExponent ε)

theorem loweringExponentCode_injOn_superior (ε : ℝ) (hε : 0 < ε) :
    Set.InjOn (loweringExponentCode ε hε) {N : ℕ | Superior ε N} := by
  intro A hA B hB hcode
  apply loweringCode_injOn_superior ε hε hA hB
  apply (Finset.image_eq_image_iff_of_injOn
    (canonicalExponent_injOn_tiedPrimes ε hε)
    (loweringCode_subset_tiedPrimes hε hA)
    (loweringCode_subset_tiedPrimes hε hB)).1
  exact hcode

@[simp] theorem loweringExponentCode_canonicalSuperior_eq_empty
    (ε : ℝ) (hε : 0 < ε) :
    loweringExponentCode ε hε (canonicalSuperior ε hε) = ∅ := by
  rw [loweringExponentCode]
  suffices loweringCode ε hε (canonicalSuperior ε hε) = ∅ by simp [this]
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro p hpLower
  rw [loweringCode, Finset.mem_filter,
    factorization_canonicalSuperior] at hpLower
  have hp := canonicalFactorization_prime_support ε hε p hpLower.1
  rw [canonicalFactorization_apply, if_pos hp] at hpLower
  omega

theorem Superior.eq_canonicalSuperior_of_loweringExponentCode_eq_empty
    {ε : ℝ} (hε : 0 < ε) {N : ℕ} (hN : Superior ε N)
    (hcode : loweringExponentCode ε hε N = ∅) :
    N = canonicalSuperior ε hε := by
  apply loweringExponentCode_injOn_superior ε hε hN
    (canonicalSuperior_isSuperior ε hε)
  simpa using hcode

theorem card_superiorNumbersAt_le_two_pow_canonicalExponent_two
    (ε : ℝ) (hε : 0 < ε) :
    (superiorNumbersAt ε hε).card ≤ 2 ^ canonicalExponent ε 2 := by
  exact (card_superiorNumbersAt_le_two_pow_tiedPrimes ε hε).trans
    (pow_le_pow_right' (by norm_num : 1 ≤ (2 : ℕ))
      (card_tiedPrimes_le_canonicalExponent_two ε hε))

/-! ## Critical parameters and the two tied maximizers

The exponent at `p` changes from `k` to `k - 1` at the exact parameter
`log (1 + 1 / k) / log p`.  Our floor convention selects the larger
exponent at the critical parameter.  The smaller exponent is an equally
good local maximizer, because the intervening local benefit is zero. -/

/-- The parameter at which the exponent of `p` can change from `k` to
`k - 1`. -/
noncomputable def criticalParameter (p k : ℕ) : ℝ :=
  Real.log (1 + 1 / (k : ℝ)) / Real.log p

theorem criticalParameter_pos {p k : ℕ} (hp : p.Prime) (hk : 0 < k) :
    0 < criticalParameter p k := by
  rw [criticalParameter]
  apply div_pos
  · apply Real.log_pos
    have hk' : (0 : ℝ) < k := by exact_mod_cast hk
    have : (0 : ℝ) < 1 / (k : ℝ) := one_div_pos.mpr hk'
    linarith
  · exact Real.log_pos (by exact_mod_cast hp.one_lt)

theorem criticalParameter_mul_log {p k : ℕ} (hp : p.Prime) :
    criticalParameter p k * Real.log p =
      Real.log (1 + 1 / (k : ℝ)) := by
  rw [criticalParameter]
  exact div_mul_cancel₀ _ (ne_of_gt (Real.log_pos (by exact_mod_cast hp.one_lt)))

theorem parameter_eq_criticalParameter_of_mem_loweringCode
    {ε : ℝ} (hε : 0 < ε) {N p : ℕ} (hN : Superior ε N)
    (hpLower : p ∈ loweringCode ε hε N) :
    ε = criticalParameter p (canonicalExponent ε p) := by
  have hpTie := loweringCode_subset_tiedPrimes hε hN hpLower
  rw [tiedPrimes, Finset.mem_filter] at hpTie
  have hp := canonicalFactorization_prime_support ε hε p hpTie.1
  rw [criticalParameter]
  apply (eq_div_iff (ne_of_gt (Real.log_pos (by exact_mod_cast hp.one_lt)))).2
  exact hpTie.2

theorem rpow_criticalParameter {p k : ℕ} (hp : p.Prime) (hk : 0 < k) :
    (p : ℝ) ^ criticalParameter p k = 1 + 1 / (k : ℝ) := by
  have hp' : (0 : ℝ) < p := by exact_mod_cast hp.pos
  rw [Real.rpow_def_of_pos hp', mul_comm, criticalParameter_mul_log hp,
    Real.exp_log]
  have hk' : (0 : ℝ) < k := by exact_mod_cast hk
  positivity

/-- Nicolas's `k`-th threshold scale, written directly rather than through
the auxiliary scale `x = 2^(1/ε)`. -/
noncomputable def thresholdScale (ε : ℝ) (k : ℕ) : ℝ :=
  (1 + 1 / (k : ℝ)) ^ (1 / ε)

theorem thresholdScale_pos {ε : ℝ} {k : ℕ} (hk : 0 < k) :
    0 < thresholdScale ε k := by
  rw [thresholdScale]
  have hk' : (0 : ℝ) < k := by exact_mod_cast hk
  exact Real.rpow_pos_of_pos (by positivity) _

theorem thresholdScale_rpow {ε : ℝ} (hε : 0 < ε) {k : ℕ} (hk : 0 < k) :
    (thresholdScale ε k) ^ ε = 1 + 1 / (k : ℝ) := by
  have hk' : (0 : ℝ) < k := by exact_mod_cast hk
  have hbase : 0 ≤ 1 + 1 / (k : ℝ) := by positivity
  rw [thresholdScale, ← Real.rpow_mul hbase]
  have hmul : 1 / ε * ε = 1 := by field_simp
  rw [hmul, Real.rpow_one]

theorem one_lt_thresholdScale_one {ε : ℝ} (hε : 0 < ε) :
    1 < thresholdScale ε 1 := by
  rw [thresholdScale]
  norm_num only [Nat.cast_one, div_one, one_add_one_eq_two]
  exact Real.one_lt_rpow (by norm_num) (one_div_pos.mpr hε)

/-- Every threshold is an exact fixed power of the first threshold.  This is
the identity behind Nicolas's low/middle/high level split. -/
theorem thresholdScale_eq_one_rpow {ε : ℝ} (hε : 0 < ε)
    {k : ℕ} (hk : 0 < k) :
    thresholdScale ε k =
      (thresholdScale ε 1) ^
        (Real.log (1 + 1 / (k : ℝ)) / Real.log 2) := by
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  have hb : 0 < (1 + 1 / (k : ℝ)) := by positivity
  have htwo : (0 : ℝ) < 2 := by norm_num
  have hscale : 0 < thresholdScale ε 1 := thresholdScale_pos (by omega)
  rw [thresholdScale, Real.rpow_def_of_pos hb,
    Real.rpow_def_of_pos hscale]
  rw [thresholdScale]
  norm_num only [Nat.cast_one, div_one, one_add_one_eq_two]
  rw [Real.log_rpow htwo]
  congr 1
  field_simp

theorem log_thresholdScale_one {ε : ℝ} (_hε : 0 < ε) :
    Real.log (thresholdScale ε 1) = (1 / ε) * Real.log 2 := by
  rw [thresholdScale]
  norm_num only [Nat.cast_one, div_one, one_add_one_eq_two]
  exact Real.log_rpow (by norm_num) _

theorem log_thresholdScale {ε : ℝ} (_hε : 0 < ε)
    {k : ℕ} (hk : 0 < k) :
    Real.log (thresholdScale ε k) =
      (1 / ε) * Real.log (1 + 1 / (k : ℝ)) := by
  have hbase : 0 < (1 + 1 / (k : ℝ)) := by positivity
  rw [thresholdScale]
  exact Real.log_rpow hbase _

/-- The finite set of primes in a benefit-width logarithmic neighborhood of
the level-`k` threshold.  The exponential upper cutoff is a consequence of
the same inequality and makes finiteness definitional. -/
noncomputable def thresholdZone (ε B : ℝ) (k : ℕ) : Finset ℕ :=
  (Nat.primesLE
      ⌈thresholdScale ε k * Real.exp (B / ε)⌉₊).filter
    (fun p ↦
      |ε * Real.log p - Real.log (1 + 1 / (k : ℝ))| ≤ B)

theorem mem_thresholdZone_of_abs_error_le {ε B : ℝ} {k p : ℕ}
    (hε : 0 < ε) (hk : 0 < k) (hp : p.Prime)
    (herror :
      |ε * Real.log p - Real.log (1 + 1 / (k : ℝ))| ≤ B) :
    p ∈ thresholdZone ε B k := by
  have hupper :
      ε * Real.log p ≤ Real.log (1 + 1 / (k : ℝ)) + B := by
    have := (abs_le.mp herror).2
    linarith
  have hlogp : Real.log p ≤
      (Real.log (1 + 1 / (k : ℝ)) + B) / ε := by
    rw [le_div_iff₀ hε]
    simpa only [mul_comm] using hupper
  have hscalePos : 0 < thresholdScale ε k := thresholdScale_pos hk
  have hExp :
      Real.exp ((Real.log (1 + 1 / (k : ℝ)) + B) / ε) =
        thresholdScale ε k * Real.exp (B / ε) := by
    calc
      Real.exp ((Real.log (1 + 1 / (k : ℝ)) + B) / ε) =
          Real.exp ((1 / ε) * Real.log (1 + 1 / (k : ℝ)) + B / ε) := by
            congr 1
            field_simp
      _ = Real.exp ((1 / ε) * Real.log (1 + 1 / (k : ℝ))) *
          Real.exp (B / ε) := Real.exp_add _ _
      _ = thresholdScale ε k * Real.exp (B / ε) := by
        rw [← log_thresholdScale hε hk, Real.exp_log hscalePos]
  have hpPosR : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hpBoundR : (p : ℝ) ≤ thresholdScale ε k * Real.exp (B / ε) := by
    calc
      (p : ℝ) = Real.exp (Real.log p) := (Real.exp_log hpPosR).symm
      _ ≤ Real.exp
          ((Real.log (1 + 1 / (k : ℝ)) + B) / ε) :=
        Real.exp_le_exp.mpr hlogp
      _ = thresholdScale ε k * Real.exp (B / ε) := hExp
  have hpCeilR : (p : ℝ) ≤
      (⌈thresholdScale ε k * Real.exp (B / ε)⌉₊ : ℝ) :=
    hpBoundR.trans (Nat.le_ceil _)
  have hpCeil : p ≤
      ⌈thresholdScale ε k * Real.exp (B / ε)⌉₊ := by
    exact_mod_cast hpCeilR
  rw [thresholdZone, Finset.mem_filter, Nat.mem_primesLE]
  exact ⟨⟨hpCeil, hp⟩, herror⟩

theorem thresholdScale_exp_bounds_of_abs_error_le
    {ε B : ℝ} {k p : ℕ}
    (hε : 0 < ε) (hk : 0 < k) (hp : p.Prime)
    (herror :
      |ε * Real.log p - Real.log (1 + 1 / (k : ℝ))| ≤ B) :
    thresholdScale ε k * Real.exp (-B / ε) ≤ (p : ℝ) ∧
      (p : ℝ) ≤ thresholdScale ε k * Real.exp (B / ε) := by
  have hscalePos : 0 < thresholdScale ε k := thresholdScale_pos hk
  have hpPosR : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hlower :
      Real.log (1 + 1 / (k : ℝ)) - B ≤ ε * Real.log p := by
    have := (abs_le.mp herror).1
    linarith
  have hupper :
      ε * Real.log p ≤ Real.log (1 + 1 / (k : ℝ)) + B := by
    have := (abs_le.mp herror).2
    linarith
  have hlogLower :
      (Real.log (1 + 1 / (k : ℝ)) - B) / ε ≤ Real.log p := by
    rw [div_le_iff₀ hε]
    simpa only [mul_comm] using hlower
  have hlogUpper : Real.log p ≤
      (Real.log (1 + 1 / (k : ℝ)) + B) / ε := by
    rw [le_div_iff₀ hε]
    simpa only [mul_comm] using hupper
  have hExpLower :
      Real.exp ((Real.log (1 + 1 / (k : ℝ)) - B) / ε) =
        thresholdScale ε k * Real.exp (-B / ε) := by
    calc
      Real.exp ((Real.log (1 + 1 / (k : ℝ)) - B) / ε) =
          Real.exp ((1 / ε) * Real.log (1 + 1 / (k : ℝ)) + (-B / ε)) := by
            congr 1
            ring
      _ = Real.exp ((1 / ε) * Real.log (1 + 1 / (k : ℝ))) *
          Real.exp (-B / ε) := Real.exp_add _ _
      _ = thresholdScale ε k * Real.exp (-B / ε) := by
        rw [← log_thresholdScale hε hk, Real.exp_log hscalePos]
  have hExpUpper :
      Real.exp ((Real.log (1 + 1 / (k : ℝ)) + B) / ε) =
        thresholdScale ε k * Real.exp (B / ε) := by
    calc
      Real.exp ((Real.log (1 + 1 / (k : ℝ)) + B) / ε) =
          Real.exp ((1 / ε) * Real.log (1 + 1 / (k : ℝ)) + B / ε) := by
            congr 1
            field_simp
      _ = Real.exp ((1 / ε) * Real.log (1 + 1 / (k : ℝ))) *
          Real.exp (B / ε) := Real.exp_add _ _
      _ = thresholdScale ε k * Real.exp (B / ε) := by
        rw [← log_thresholdScale hε hk, Real.exp_log hscalePos]
  constructor
  · rw [← hExpLower, ← Real.exp_log hpPosR]
    exact Real.exp_le_exp.mpr hlogLower
  · rw [← hExpUpper, ← Real.exp_log hpPosR]
    exact Real.exp_le_exp.mpr hlogUpper

theorem thresholdScale_exp_bounds_of_mem_thresholdZone
    {ε B : ℝ} {k p : ℕ}
    (hε : 0 < ε) (hk : 0 < k) (hp : p ∈ thresholdZone ε B k) :
    thresholdScale ε k * Real.exp (-B / ε) ≤ (p : ℝ) ∧
      (p : ℝ) ≤ thresholdScale ε k * Real.exp (B / ε) := by
  rw [thresholdZone, Finset.mem_filter] at hp
  have hpPrime : p.Prime := Nat.prime_of_mem_primesLE hp.1
  exact thresholdScale_exp_bounds_of_abs_error_le hε hk hpPrime hp.2

/-- A threshold zone narrower than one real unit contains at most one prime. -/
theorem thresholdZone_card_le_one
    {ε B : ℝ} {k : ℕ}
    (hε : 0 < ε) (hk : 0 < k)
    (ht0 : 0 ≤ B / ε) (ht1 : B / ε ≤ 1)
    (hwidth : 4 * thresholdScale ε k * (B / ε) < 1) :
    (thresholdZone ε B k).card ≤ 1 := by
  rw [Finset.card_le_one]
  intro p hp q hq
  obtain ⟨hpLower, hpUpper⟩ :=
    thresholdScale_exp_bounds_of_mem_thresholdZone hε hk hp
  obtain ⟨hqLower, hqUpper⟩ :=
    thresholdScale_exp_bounds_of_mem_thresholdZone hε hk hq
  let t := B / ε
  have ht0' : 0 ≤ t := by simpa [t] using ht0
  have htAbs : |t| ≤ 1 := by simpa [abs_of_nonneg ht0'] using ht1
  have hnegAbs : |-t| ≤ 1 := by simpa using htAbs
  have hExpUpper : Real.exp t - 1 ≤ 2 * t := by
    have h := Real.abs_exp_sub_one_le htAbs
    rw [abs_of_nonneg (by
      exact sub_nonneg.mpr (Real.one_le_exp ht0'))] at h
    simpa [abs_of_nonneg ht0'] using h
  have hExpLower : 1 - Real.exp (-t) ≤ 2 * t := by
    have h := Real.abs_exp_sub_one_le hnegAbs
    rw [abs_of_nonpos (by
      exact sub_nonpos.mpr (Real.exp_le_one_iff.mpr (neg_nonpos.mpr ht0')))] at h
    simpa [abs_of_nonneg ht0'] using h
  have hgap :
      thresholdScale ε k * Real.exp t -
          thresholdScale ε k * Real.exp (-t) < 1 := by
    have hscale : 0 ≤ thresholdScale ε k := (thresholdScale_pos hk).le
    calc
      thresholdScale ε k * Real.exp t -
          thresholdScale ε k * Real.exp (-t) =
          thresholdScale ε k *
            ((Real.exp t - 1) + (1 - Real.exp (-t))) := by ring
      _ ≤ thresholdScale ε k * (4 * t) := by
        gcongr
        linarith
      _ = 4 * thresholdScale ε k * (B / ε) := by simp [t]; ring
      _ < 1 := hwidth
  rcases le_total p q with hpq | hqp
  · have hqLt : (q : ℝ) < p + 1 := by
      dsimp [t] at hgap
      have hpLower' :
          thresholdScale ε k * Real.exp (-(B / ε)) ≤ (p : ℝ) := by
        simpa [neg_div] using hpLower
      linarith
    have hqLtNat : q < p + 1 := by exact_mod_cast hqLt
    omega
  · have hpLt : (p : ℝ) < q + 1 := by
      dsimp [t] at hgap
      have hqLower' :
          thresholdScale ε k * Real.exp (-(B / ε)) ≤ (q : ℝ) := by
        simpa [neg_div] using hqLower
      linarith
    have hpLtNat : p < q + 1 := by exact_mod_cast hpLt
    omega

/-- Crude bound for the finitely many low-level zones. -/
theorem thresholdZone_card_le_three_mul_ceil
    {ε B : ℝ} {k : ℕ}
    (hε : 0 < ε) (hk : 0 < k) (ht1 : B / ε ≤ 1) :
    (thresholdZone ε B k).card ≤
      3 * ⌈thresholdScale ε 1⌉₊ + 1 := by
  let x := thresholdScale ε 1
  let R := ⌈x⌉₊
  let U := ⌈thresholdScale ε k * Real.exp (B / ε)⌉₊
  have hkOne : 1 ≤ k := hk
  have hscaleLe : thresholdScale ε k ≤ x := by
    dsimp [x]
    rw [thresholdScale, thresholdScale]
    apply Real.rpow_le_rpow
    · have hkR : (0 : ℝ) < k := by exact_mod_cast hk
      positivity
    · have hkR : (0 : ℝ) < k := by exact_mod_cast hk
      norm_num
      have hkOneR : (1 : ℝ) ≤ k := by exact_mod_cast hkOne
      have hinv : 1 / (k : ℝ) ≤ 1 := by
        simpa using
          one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 1) hkOneR
      simp only [one_div] at hinv
      linarith
    · exact one_div_nonneg.mpr hε.le
  have hexpLe : Real.exp (B / ε) ≤ Real.exp 1 :=
    Real.exp_le_exp.mpr ht1
  have hexpThree : Real.exp (B / ε) ≤ 3 :=
    hexpLe.trans Real.exp_one_lt_three.le
  have hxLeR : x ≤ (R : ℝ) := by
    dsimp [R]
    exact Nat.le_ceil x
  have hupper :
      thresholdScale ε k * Real.exp (B / ε) ≤ (3 * R : ℕ) := by
    norm_num only [Nat.cast_mul, Nat.cast_ofNat]
    calc
      thresholdScale ε k * Real.exp (B / ε) ≤ x * Real.exp (B / ε) := by
        gcongr
      _ ≤ x * 3 :=
        mul_le_mul_of_nonneg_left hexpThree
          (by simpa [x] using (thresholdScale_pos (by omega : 0 < 1)).le)
      _ ≤ (R : ℝ) * 3 := mul_le_mul_of_nonneg_right hxLeR (by norm_num)
      _ = 3 * (R : ℝ) := by ring
  have hU : U ≤ 3 * R := by
    dsimp [U]
    exact Nat.ceil_le.mpr hupper
  have hfilter : thresholdZone ε B k ⊆ Nat.primesLE U := by
    intro p hp
    exact (Finset.mem_filter.mp hp).1
  have hprimes : (Nat.primesLE U).card ≤ U + 1 := by
    calc
      (Nat.primesLE U).card ≤ (Finset.range (U + 1)).card := by
        apply Finset.card_le_card
        intro p hp
        rw [Finset.mem_range]
        exact Nat.lt_succ_of_le (Nat.le_of_mem_primesLE hp)
      _ = U + 1 := Finset.card_range _
  calc
    (thresholdZone ε B k).card ≤ (Nat.primesLE U).card :=
      Finset.card_le_card hfilter
    _ ≤ U + 1 := hprimes
    _ ≤ 3 * R + 1 := Nat.add_le_add_right hU 1
    _ = 3 * ⌈thresholdScale ε 1⌉₊ + 1 := by rfl

/-- Prime coordinates whose exponent is at least a given level. -/
noncomputable def exponentLevelPrimes (n k : ℕ) : Finset ℕ :=
  n.primeFactors.filter (fun p ↦ k ≤ n.factorization p)

theorem mem_exponentLevelPrimes_iff {n p k : ℕ}
    (hn : 0 < n) (hk : 0 < k) :
    p ∈ exponentLevelPrimes n k ↔
      p.Prime ∧ k ≤ n.factorization p := by
  constructor
  · intro hmem
    have h := Finset.mem_filter.mp hmem
    exact ⟨Nat.prime_of_mem_primeFactors h.1, h.2⟩
  · rintro ⟨hp, hfactor⟩
    have hpPos : 0 < n.factorization p := hk.trans_le hfactor
    have hpDvd : p ∣ n := Nat.dvd_of_factorization_pos hpPos.ne'
    exact Finset.mem_filter.mpr
      ⟨(Nat.mem_primeFactors_of_ne_zero hn.ne').2 ⟨hp, hpDvd⟩, hfactor⟩

/-- Symmetric difference of the level-prime initial segments. -/
noncomputable def levelChangePrimes (N M k : ℕ) : Finset ℕ :=
  (exponentLevelPrimes N k \ exponentLevelPrimes M k) ∪
    (exponentLevelPrimes M k \ exponentLevelPrimes N k)

theorem mem_levelChangePrimes_iff {N M p k : ℕ}
    (hN : 0 < N) (hM : 0 < M) (hk : 0 < k) :
    p ∈ levelChangePrimes N M k ↔
      p.Prime ∧
        ((k ≤ M.factorization p ∧ ¬k ≤ N.factorization p) ∨
          (k ≤ N.factorization p ∧ ¬k ≤ M.factorization p)) := by
  rw [levelChangePrimes, Finset.mem_union, Finset.mem_sdiff,
    Finset.mem_sdiff, mem_exponentLevelPrimes_iff hN hk,
    mem_exponentLevelPrimes_iff hM hk]
  aesop

/-- Rank of the last prime occurring at level `k`. -/
noncomputable def exponentLevelRank (n k : ℕ) : ℕ :=
  (exponentLevelPrimes n k).card

theorem exponentLevelPrimes_eq_primesLE_exponentBoundary
    {n k : ℕ} (hn : HighlyComposite n) (hk : 0 < k) :
    exponentLevelPrimes n k = Nat.primesLE (exponentBoundary n k) := by
  ext p
  rw [mem_exponentLevelPrimes_iff hn.1 hk, Nat.mem_primesLE]
  constructor
  · rintro ⟨hp, hfactor⟩
    exact ⟨(prime_le_exponentBoundary_iff hn hp hk).2 hfactor, hp⟩
  · rintro ⟨hpBoundary, hp⟩
    exact ⟨hp, (prime_le_exponentBoundary_iff hn hp hk).1 hpBoundary⟩

theorem exponentLevelRank_eq_primeCounting_exponentBoundary
    {n k : ℕ} (hn : HighlyComposite n) (hk : 0 < k) :
    exponentLevelRank n k = Nat.primeCounting (exponentBoundary n k) := by
  rw [exponentLevelRank,
    exponentLevelPrimes_eq_primesLE_exponentBoundary hn hk,
    Nat.primesLE_card_eq_primeCounting]

theorem exponentBoundary_eq_zero_or_prime (n k : ℕ) :
    exponentBoundary n k = 0 ∨ (exponentBoundary n k).Prime := by
  by_cases hzero : exponentBoundary n k = 0
  · exact Or.inl hzero
  · exact Or.inr (Nat.findGreatest_of_ne_zero rfl hzero).1

/-- Prime-counting rank is injective on the possible boundary values (zero
or a prime). -/
theorem primeCounting_inj_of_eq_zero_or_prime {p q : ℕ}
    (hp : p = 0 ∨ p.Prime) (hq : q = 0 ∨ q.Prime)
    (hrank : Nat.primeCounting p = Nat.primeCounting q) : p = q := by
  rcases hp with rfl | hp
  · rcases hq with rfl | hq
    · rfl
    · exfalso
      have hqMem : q ∈ Nat.primesLE q := by simp [Nat.mem_primesLE, hq]
      have hqCard : 0 < (Nat.primesLE q).card :=
        Finset.card_pos.mpr ⟨q, hqMem⟩
      rw [Nat.primesLE_card_eq_primeCounting] at hqCard
      have hzero : Nat.primeCounting q = 0 := by simpa using hrank.symm
      omega
  · rcases hq with rfl | hq
    · exfalso
      have hpMem : p ∈ Nat.primesLE p := by simp [Nat.mem_primesLE, hp]
      have hpCard : 0 < (Nat.primesLE p).card :=
        Finset.card_pos.mpr ⟨p, hpMem⟩
      rw [Nat.primesLE_card_eq_primeCounting] at hpCard
      have hzero : Nat.primeCounting p = 0 := by simpa using hrank
      omega
    · rcases lt_trichotomy p q with hpq | hpq | hqp
      · have hsub : Nat.primesLE p ⊆ Nat.primesLE q := by
          intro r hr
          rw [Nat.mem_primesLE] at hr ⊢
          exact ⟨hr.1.trans hpq.le, hr.2⟩
        have hstrict : Nat.primesLE p ⊂ Nat.primesLE q := by
          refine Finset.ssubset_iff_subset_ne.mpr ⟨hsub, ?_⟩
          intro heq
          have hqMem : q ∈ Nat.primesLE q := by
            simp [Nat.mem_primesLE, hq]
          rw [← heq, Nat.mem_primesLE] at hqMem
          omega
        have hcard := Finset.card_lt_card hstrict
        rw [Nat.primesLE_card_eq_primeCounting,
          Nat.primesLE_card_eq_primeCounting, hrank] at hcard
        exact (lt_irrefl _ hcard).elim
      · exact hpq
      · have hsub : Nat.primesLE q ⊆ Nat.primesLE p := by
          intro r hr
          rw [Nat.mem_primesLE] at hr ⊢
          exact ⟨hr.1.trans hqp.le, hr.2⟩
        have hstrict : Nat.primesLE q ⊂ Nat.primesLE p := by
          refine Finset.ssubset_iff_subset_ne.mpr ⟨hsub, ?_⟩
          intro heq
          have hpMem : p ∈ Nat.primesLE p := by
            simp [Nat.mem_primesLE, hp]
          rw [← heq, Nat.mem_primesLE] at hpMem
          omega
        have hcard := Finset.card_lt_card hstrict
        rw [Nat.primesLE_card_eq_primeCounting,
          Nat.primesLE_card_eq_primeCounting, hrank] at hcard
        exact (lt_irrefl _ hcard).elim

/-- The exponent at `2` and all finite level ranks form an injective code for
highly composite integers. -/
theorem highlyComposite_eq_of_exponentLevelRank_eq {n m : ℕ}
    (hn : HighlyComposite n) (hm : HighlyComposite m)
    (h2 : n.factorization 2 = m.factorization 2)
    (hRank : ∀ k : ℕ, 0 < k → k ≤ n.factorization 2 →
      exponentLevelRank n k = exponentLevelRank m k) :
    n = m := by
  apply highlyComposite_eq_of_exponentBoundary_eq hn hm h2
  intro k hk hkTwo
  apply primeCounting_inj_of_eq_zero_or_prime
      (exponentBoundary_eq_zero_or_prime n k)
      (exponentBoundary_eq_zero_or_prime m k)
  rw [← exponentLevelRank_eq_primeCounting_exponentBoundary hn hk,
    ← exponentLevelRank_eq_primeCounting_exponentBoundary hm hk]
  exact hRank k hk hkTwo

theorem exponentLevelRank_le_add_levelChangePrimes_card
    (N M k : ℕ) :
    exponentLevelRank M k ≤
      (levelChangePrimes N M k).card + exponentLevelRank N k := by
  let S := exponentLevelPrimes M k
  let T := exponentLevelPrimes N k
  have hdiff : S \ T ⊆ levelChangePrimes N M k := by
    intro p hp
    exact Finset.mem_union_right _ hp
  calc
    exponentLevelRank M k = S.card := rfl
    _ ≤ (S \ T).card + T.card := Finset.card_le_card_sdiff_add_card
    _ ≤ (levelChangePrimes N M k).card + T.card := by
      gcongr
    _ = (levelChangePrimes N M k).card + exponentLevelRank N k := rfl

theorem exponentLevelRank_pair_bounds_of_change_subset
    {N M k : ℕ} {Z : Finset ℕ}
    (hsubset : levelChangePrimes N M k ⊆ Z) :
    exponentLevelRank M k ≤ Z.card + exponentLevelRank N k ∧
      exponentLevelRank N k ≤ Z.card + exponentLevelRank M k := by
  have hcard : (levelChangePrimes N M k).card ≤ Z.card :=
    Finset.card_le_card hsubset
  constructor
  · exact (exponentLevelRank_le_add_levelChangePrimes_card N M k).trans
      (Nat.add_le_add_right hcard _)
  · exact (exponentLevelRank_le_add_levelChangePrimes_card M N k).trans <| by
      have hsymm : levelChangePrimes M N k = levelChangePrimes N M k := by
        simp only [levelChangePrimes]
        rw [Finset.union_comm]
      rw [hsymm]
      exact Nat.add_le_add_right hcard _

/-- The finite rank window allowed by a threshold zone. -/
noncomputable def exponentLevelRankWindow (N k z : ℕ) : Finset ℕ :=
  Finset.Icc (exponentLevelRank N k - z) (exponentLevelRank N k + z)

theorem mem_exponentLevelRankWindow_of_pair_bounds
    {N M k z : ℕ}
    (hMN : exponentLevelRank M k ≤ z + exponentLevelRank N k)
    (hNM : exponentLevelRank N k ≤ z + exponentLevelRank M k) :
    exponentLevelRank M k ∈ exponentLevelRankWindow N k z := by
  rw [exponentLevelRankWindow, Finset.mem_Icc]
  omega

theorem card_exponentLevelRankWindow_le (N k z : ℕ) :
    (exponentLevelRankWindow N k z).card ≤ 2 * z + 1 := by
  rw [exponentLevelRankWindow, Nat.card_Icc]
  omega

/-- Finite code consisting of the exponent at `2` (coordinate zero) and the
level-prime ranks (positive coordinates). -/
noncomputable def exponentRankCertificate (L A : ℕ) : Fin (L + 1) → ℕ :=
  fun i ↦ if i.1 = 0 then A.factorization 2 else exponentLevelRank A i.1

theorem exponentRankCertificate_injOn_highlyComposite
    {L n m : ℕ} (hn : HighlyComposite n) (hm : HighlyComposite m)
    (hnL : n.factorization 2 ≤ L) (_hmL : m.factorization 2 ≤ L)
    (hcode : exponentRankCertificate L n = exponentRankCertificate L m) :
    n = m := by
  let i0 : Fin (L + 1) := ⟨0, by omega⟩
  have h2 := congrFun hcode i0
  have h2' : n.factorization 2 = m.factorization 2 := by
    simpa [exponentRankCertificate, i0] using h2
  apply highlyComposite_eq_of_exponentLevelRank_eq hn hm h2'
  intro k hk hkTwo
  have hkL : k ≤ L := hkTwo.trans hnL
  let ik : Fin (L + 1) := ⟨k, by omega⟩
  have hrank := congrFun hcode ik
  simpa [exponentRankCertificate, ik, hk.ne'] using hrank

/-- Coordinatewise finite choice space for the preceding certificate. -/
noncomputable def exponentRankAllowed
    (N L : ℕ) (z : ℕ → ℕ) (i : Fin (L + 1)) : Finset ℕ :=
  if i.1 = 0 then Finset.range (L + 1)
  else exponentLevelRankWindow N i.1 (z i.1)

theorem prod_exponentRankAllowed_le (N L : ℕ) (z : ℕ → ℕ) :
    (∏ i : Fin (L + 1), (exponentRankAllowed N L z i).card) ≤
      (L + 1) * ∏ i : Fin L, (2 * z (i.1 + 1) + 1) := by
  rw [Fin.prod_univ_succ]
  have hzero :
      (exponentRankAllowed N L z (0 : Fin (L + 1))).card = L + 1 := by
    simp [exponentRankAllowed]
  rw [hzero]
  gcongr with i
  have hi : (i.succ : Fin (L + 1)).1 ≠ 0 := by simp
  rw [exponentRankAllowed, if_neg hi]
  simpa using
    card_exponentLevelRankWindow_le N (i.1 + 1) (z (i.1 + 1))

theorem fin_prod_le_low_high_pow
    {L k₀ A B : ℕ} (f : Fin L → ℕ)
    (hA : 0 < A) (hB : 0 < B)
    (hlow : ∀ i : Fin L, i.1 < k₀ → f i ≤ A)
    (hhigh : ∀ i : Fin L, k₀ ≤ i.1 → f i ≤ B) :
    (∏ i : Fin L, f i) ≤ A ^ k₀ * B ^ L := by
  let low : Finset (Fin L) := Finset.univ.filter (fun i ↦ i.1 < k₀)
  have hlowSubset : low ⊆ (Finset.univ : Finset (Fin L)) :=
    Finset.filter_subset _ _
  have hlowCard : low.card ≤ k₀ := by
    calc
      low.card ≤ (Finset.range k₀).card := by
        apply Finset.card_le_card_of_injOn (fun i : Fin L ↦ i.1)
        · intro i hi
          change i.1 ∈ Finset.range k₀
          rw [Finset.mem_range]
          exact (Finset.mem_filter.mp hi).2
        · intro i hi j hj hij
          exact Fin.ext hij
      _ = k₀ := Finset.card_range k₀
  have hcompCard :
      ((Finset.univ : Finset (Fin L)) \ low).card ≤ L := by
    calc
      ((Finset.univ : Finset (Fin L)) \ low).card ≤
          (Finset.univ : Finset (Fin L)).card :=
        Finset.card_le_card (Finset.sdiff_subset)
      _ = L := Fintype.card_fin L
  have hprodLow : (∏ i ∈ low, f i) ≤ A ^ k₀ := by
    calc
      (∏ i ∈ low, f i) ≤ ∏ _i ∈ low, A := by
        apply Finset.prod_le_prod'
        intro i hi
        exact hlow i (Finset.mem_filter.mp hi).2
      _ = A ^ low.card := by simp
      _ ≤ A ^ k₀ := Nat.pow_le_pow_right hA hlowCard
  have hprodHigh :
      (∏ i ∈ (Finset.univ : Finset (Fin L)) \ low, f i) ≤ B ^ L := by
    calc
      (∏ i ∈ (Finset.univ : Finset (Fin L)) \ low, f i) ≤
          ∏ _i ∈ (Finset.univ : Finset (Fin L)) \ low, B := by
        apply Finset.prod_le_prod'
        intro i hi
        have hiNot : ¬i.1 < k₀ := by
          intro hilt
          exact (Finset.mem_sdiff.mp hi).2
            (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hilt⟩)
        exact hhigh i (Nat.le_of_not_gt hiNot)
      _ = B ^ ((Finset.univ : Finset (Fin L)) \ low).card := by simp
      _ ≤ B ^ L := Nat.pow_le_pow_right hB hcompCard
  have hsplit := Finset.prod_sdiff (f := f) hlowSubset
  calc
    (∏ i : Fin L, f i) =
        (∏ i ∈ (Finset.univ : Finset (Fin L)) \ low, f i) *
          ∏ i ∈ low, f i := hsplit.symm
    _ ≤ B ^ L * A ^ k₀ := Nat.mul_le_mul hprodHigh hprodLow
    _ = A ^ k₀ * B ^ L := Nat.mul_comm _ _

theorem prod_thresholdZone_factor_le
    {ε B : ℝ} {L k₀ R : ℕ}
    (hlow : ∀ i : Fin L, i.1 < k₀ →
      (thresholdZone ε B (i.1 + 1)).card ≤ 3 * R + 1)
    (hhigh : ∀ i : Fin L, k₀ ≤ i.1 →
      (thresholdZone ε B (i.1 + 1)).card ≤ 1) :
    (∏ i : Fin L, (2 * (thresholdZone ε B (i.1 + 1)).card + 1)) ≤
      (6 * R + 3) ^ k₀ * 3 ^ L := by
  apply fin_prod_le_low_high_pow
      (fun i : Fin L ↦ 2 * (thresholdZone ε B (i.1 + 1)).card + 1)
      (by omega) (by omega)
  · intro i hi
    have := hlow i hi
    omega
  · intro i hi
    have := hhigh i hi
    omega

/-- Generic finite certificate bound.  Analytic work enters only through the
cardinalities `z k` of the allowed rank-change sets. -/
theorem card_le_prod_exponentRankAllowed
    {S : Finset ℕ} {N L : ℕ} {z : ℕ → ℕ}
    (hHC : ∀ A ∈ S, HighlyComposite A)
    (hL : ∀ A ∈ S, A.factorization 2 ≤ L)
    (hWindow : ∀ A ∈ S, ∀ k : ℕ, 0 < k → k ≤ L →
      exponentLevelRank A k ∈ exponentLevelRankWindow N k (z k)) :
    S.card ≤ ∏ i : Fin (L + 1), (exponentRankAllowed N L z i).card := by
  let target : Finset (Fin (L + 1) → ℕ) :=
    Fintype.piFinset (exponentRankAllowed N L z)
  calc
    S.card ≤ target.card := by
      apply Finset.card_le_card_of_injOn (exponentRankCertificate L)
      · intro A hA
        change exponentRankCertificate L A ∈
          Fintype.piFinset (exponentRankAllowed N L z)
        rw [Fintype.mem_piFinset]
        intro i
        by_cases hi : i.1 = 0
        · simp [exponentRankCertificate, exponentRankAllowed, hi,
            hL A hA]
        · rw [exponentRankCertificate, exponentRankAllowed, if_neg hi,
            if_neg hi]
          have hiL : i.1 ≤ L := by omega
          exact hWindow A hA i.1 (Nat.pos_of_ne_zero hi) hiL
      · intro A hA B hB hcode
        exact exponentRankCertificate_injOn_highlyComposite
          (hHC A hA) (hHC B hB) (hL A hA) (hL B hB) hcode
    _ = ∏ i : Fin (L + 1), (exponentRankAllowed N L z i).card := by
      rw [show target = Fintype.piFinset (exponentRankAllowed N L z) by rfl,
        Fintype.card_piFinset]

theorem levelChangePrimes_subset_thresholdZone
    {ε B : ℝ} {N M k : ℕ}
    (hε : 0 < ε) (hN : Superior ε N) (hM : 0 < M) (hk : 0 < k)
    (hbenefit : benefit ε N M ≤ B)
    (hwithin : ∀ p : ℕ, p.Prime →
      M.factorization p ≤ N.factorization p + 1 ∧
        N.factorization p ≤ M.factorization p + 1) :
    levelChangePrimes N M k ⊆ thresholdZone ε B k := by
  intro p hpChange
  have hpData := (mem_levelChangePrimes_iff hN.1 hM hk).1 hpChange
  apply mem_thresholdZone_of_abs_error_le hε hk hpData.1
  exact (abs_threshold_error_le_benefit_of_level_change
    hN hM hpData.1 hk (hwithin p hpData.1) hpData.2).trans hbenefit

/-- Threshold scales decrease as the exponent level increases. -/
theorem thresholdScale_antitone_level {ε : ℝ} (hε : 0 < ε)
    {k l : ℕ} (hk : 0 < k) (hkl : k ≤ l) :
    thresholdScale ε l ≤ thresholdScale ε k := by
  have hl : 0 < l := hk.trans_le hkl
  rw [thresholdScale, thresholdScale]
  apply Real.rpow_le_rpow
  · have hlR : (0 : ℝ) < l := by exact_mod_cast hl
    positivity
  · have hkR : (0 : ℝ) < k := by exact_mod_cast hk
    have hlR : (0 : ℝ) < l := by exact_mod_cast hl
    have hcast : (k : ℝ) ≤ l := by exact_mod_cast hkl
    gcongr
  · exact one_div_nonneg.mpr hε.le

theorem exists_level_log_ratio_lt_half {γ : ℝ} (hγ : 0 < γ) :
    ∃ k₀ : ℕ,
      Real.log (1 + 1 / ((k₀ + 1 : ℕ) : ℝ)) / Real.log 2 < γ / 2 := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have htarget : 0 < (γ / 2) * Real.log 2 := mul_pos (by positivity) hlog2
  obtain ⟨k₀, hk₀⟩ := exists_nat_one_div_lt htarget
  refine ⟨k₀, ?_⟩
  have hbase : 0 < 1 + 1 / ((k₀ + 1 : ℕ) : ℝ) := by positivity
  have hlogLe := Real.log_le_sub_one_of_pos hbase
  have hlogLe' :
      Real.log (1 + 1 / ((k₀ + 1 : ℕ) : ℝ)) ≤
        1 / ((k₀ + 1 : ℕ) : ℝ) := by
    linarith
  have hk₀' :
      1 / ((k₀ + 1 : ℕ) : ℝ) < (γ / 2) * Real.log 2 := by
    simpa only [Nat.cast_add, Nat.cast_one] using hk₀
  rw [div_lt_iff₀ hlog2]
  exact hlogLe'.trans_lt hk₀'

/-- Above one fixed level, every power-benefit threshold zone contains at
most one prime, uniformly for all sufficiently large first thresholds. -/
theorem eventually_thresholdZone_card_le_one_of_power
    (C γ : ℝ) (hC : 0 ≤ C) (hγ : 0 < γ) :
    ∃ k₀ : ℕ, ∃ X₀ : ℝ, ∀ ε : ℝ, ∀ k : ℕ,
      0 < ε → X₀ ≤ thresholdScale ε 1 → k₀ < k →
      (thresholdZone ε
        (C * (thresholdScale ε 1) ^ (-γ)) k).card ≤ 1 := by
  obtain ⟨k₀, hk₀⟩ := exists_level_log_ratio_lt_half hγ
  let α := Real.log (1 + 1 / ((k₀ + 1 : ℕ) : ℝ)) / Real.log 2
  have hαγ : α < γ := by
    dsimp [α]
    linarith
  obtain ⟨X₀, hlarge⟩ := Filter.eventually_atTop.1
    (eventually_powerBenefit_zone_width_lt_one C γ α hC hγ hαγ)
  refine ⟨k₀, X₀, ?_⟩
  intro ε k hε hx hk
  let x := thresholdScale ε 1
  let B := C * x ^ (-γ)
  have hdata := hlarge x (by simpa [x] using hx)
  have hlog2ne : Real.log 2 ≠ 0 := (Real.log_pos (by norm_num)).ne'
  have htEq : B / ε =
      C * x ^ (-γ) * Real.log x / Real.log 2 := by
    dsimp [B]
    rw [log_thresholdScale_one hε]
    field_simp
  have ht0 : 0 ≤ B / ε := by rw [htEq]; exact hdata.1
  have ht1 : B / ε ≤ 1 := by rw [htEq]; exact hdata.2.1
  have hkLe : k₀ + 1 ≤ k := by omega
  have hscaleLe : thresholdScale ε k ≤ thresholdScale ε (k₀ + 1) :=
    thresholdScale_antitone_level hε (by omega) hkLe
  have hscaleEq : thresholdScale ε (k₀ + 1) = x ^ α := by
    simpa [x, α] using
      (thresholdScale_eq_one_rpow hε (show 0 < k₀ + 1 by omega))
  have hscalePow : thresholdScale ε k ≤ x ^ α := by
    rwa [hscaleEq] at hscaleLe
  have hwidth : 4 * thresholdScale ε k * (B / ε) < 1 := by
    calc
      4 * thresholdScale ε k * (B / ε) ≤
          4 * x ^ α * (B / ε) := by gcongr
      _ = 4 * x ^ α *
          (C * x ^ (-γ) * Real.log x / Real.log 2) := by rw [htEq]
      _ < 1 := hdata.2.2
  simpa [B, x] using thresholdZone_card_le_one hε (by omega) ht0 ht1 hwidth

/-- At the coarse transition level `ceil (log x)`, every remaining threshold
is absolutely bounded.  The constant `exp 2` is intentionally loose; it lets
the local count treat all still-higher levels using only finitely many small
prime coordinates. -/
theorem thresholdScale_ceil_log_le_exp_two {ε : ℝ} (hε : 0 < ε) :
    thresholdScale ε ⌈Real.log (thresholdScale ε 1)⌉₊ ≤ Real.exp 2 := by
  let x := thresholdScale ε 1
  have hx1 : 1 < x := one_lt_thresholdScale_one hε
  have hlogx : 0 < Real.log x := Real.log_pos hx1
  let K : ℕ := ⌈Real.log x⌉₊
  have hK : 0 < K := by
    rw [Nat.pos_iff_ne_zero]
    intro hzero
    have hceil : Real.log x ≤ (K : ℝ) := Nat.le_ceil _
    rw [hzero, Nat.cast_zero] at hceil
    linarith
  have hKreal : Real.log x ≤ (K : ℝ) := Nat.le_ceil _
  have hKR : (0 : ℝ) < K := by exact_mod_cast hK
  rw [show ⌈Real.log (thresholdScale ε 1)⌉₊ = K by rfl]
  rw [thresholdScale, Real.rpow_def_of_pos (by positivity)]
  apply Real.exp_le_exp.mpr
  have hlogbase : Real.log (1 + 1 / (K : ℝ)) ≤ 1 / (K : ℝ) := by
    have h := Real.log_le_sub_one_of_pos
      (show (0 : ℝ) < 1 + 1 / (K : ℝ) by positivity)
    linarith
  have hlogidentity : Real.log x = (1 / ε) * Real.log 2 := by
    simpa only [x] using log_thresholdScale_one hε
  have honeeps : 1 / ε = Real.log x / Real.log 2 := by
    rw [hlogidentity, mul_div_cancel_right₀]
    exact (Real.log_pos (by norm_num)).ne'
  rw [honeeps]
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hratio : Real.log x / (K : ℝ) ≤ 1 := by
    rw [div_le_one₀ hKR]
    exact hKreal
  have hmain : Real.log (1 + 1 / (K : ℝ)) *
      (Real.log x / Real.log 2) ≤ 1 / Real.log 2 := by
    calc
      Real.log (1 + 1 / (K : ℝ)) * (Real.log x / Real.log 2) ≤
          (1 / (K : ℝ)) * (Real.log x / Real.log 2) := by gcongr
      _ = (Real.log x / (K : ℝ)) * (1 / Real.log 2) := by ring
      _ ≤ 1 * (1 / Real.log 2) := by gcongr
      _ = 1 / Real.log 2 := one_mul _
  have hinvlog2 : 1 / Real.log 2 < 2 := by
    rw [div_lt_iff₀ hlog2]
    nlinarith [Real.log_two_gt_d9]
  exact hmain.trans hinvlog2.le

theorem thresholdScale_le_exp_two_of_ceil_log_le {ε : ℝ} (hε : 0 < ε)
    {k : ℕ} (hk : ⌈Real.log (thresholdScale ε 1)⌉₊ ≤ k) :
    thresholdScale ε k ≤ Real.exp 2 := by
  let K : ℕ := ⌈Real.log (thresholdScale ε 1)⌉₊
  have hx1 := one_lt_thresholdScale_one hε
  have hlogx : 0 < Real.log (thresholdScale ε 1) := Real.log_pos hx1
  have hK : 0 < K := by
    rw [Nat.pos_iff_ne_zero]
    intro hzero
    have hceil : Real.log (thresholdScale ε 1) ≤ (K : ℝ) := Nat.le_ceil _
    rw [hzero, Nat.cast_zero] at hceil
    linarith
  calc
    thresholdScale ε k ≤ thresholdScale ε K :=
      thresholdScale_antitone_level hε hK hk
    _ ≤ Real.exp 2 := thresholdScale_ceil_log_le_exp_two hε

theorem thresholdScale_antitone_parameter {ε δ : ℝ} (hε : 0 < ε)
    (hεδ : ε ≤ δ) {k : ℕ} (hk : 0 < k) :
    thresholdScale δ k ≤ thresholdScale ε k := by
  rw [thresholdScale, thresholdScale]
  have hk' : (0 : ℝ) < k := by exact_mod_cast hk
  apply Real.rpow_le_rpow_of_exponent_le (by
    have : (0 : ℝ) ≤ 1 / (k : ℝ) := by positivity
    linarith)
  exact one_div_le_one_div_of_le hε hεδ

/-- The exponent at `2` is only logarithmic in the first threshold scale.
The deliberately coarse constant `3` keeps the later finite count integral. -/
theorem canonicalExponent_two_cast_le_three_mul_log_thresholdScale
    {ε : ℝ} (hε : 0 < ε) :
    (canonicalExponent ε 2 : ℝ) ≤
      3 * Real.log (thresholdScale ε 1) := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hfloor := (canonicalExponent_floor_bounds hε Nat.prime_two).1
  have hrpowLower : ε * Real.log 2 ≤ (2 : ℝ) ^ ε - 1 := by
    have hexp := Real.add_one_le_exp (ε * Real.log 2)
    rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2)]
    have hmain : ε * Real.log 2 ≤ Real.exp (ε * Real.log 2) - 1 := by
      linarith
    simpa only [mul_comm] using hmain
  have hinv : 1 / ((2 : ℝ) ^ ε - 1) ≤ 1 / (ε * Real.log 2) := by
    exact one_div_le_one_div_of_le (mul_pos hε hlog2) hrpowLower
  have hlog2gt : (2 / 3 : ℝ) < Real.log 2 := by
    have h := Real.log_two_gt_d9
    norm_num at h ⊢
    linarith
  have honeDiv : 1 / Real.log 2 ≤ 3 * Real.log 2 := by
    rw [div_le_iff₀ hlog2]
    nlinarith
  have hinvFactor :
      1 / (ε * Real.log 2) ≤ (1 / ε) * (3 * Real.log 2) := by
    calc
      1 / (ε * Real.log 2) = (1 / ε) * (1 / Real.log 2) := by
        field_simp
      _ ≤ (1 / ε) * (3 * Real.log 2) := by
        exact mul_le_mul_of_nonneg_left honeDiv (by positivity)
  have hlogScale :
      Real.log (thresholdScale ε 1) = (1 / ε) * Real.log 2 := by
    rw [thresholdScale]
    norm_num only [Nat.cast_one, div_one, one_add_one_eq_two]
    exact Real.log_rpow (by norm_num) _
  calc
    (canonicalExponent ε 2 : ℝ) ≤ 1 / ((2 : ℝ) ^ ε - 1) := hfloor
    _ ≤ 1 / (ε * Real.log 2) := hinv
    _ ≤ (1 / ε) * (3 * Real.log 2) := hinvFactor
    _ = 3 * Real.log (thresholdScale ε 1) := by rw [hlogScale]; ring

/-- Once the total benefit is below the reciprocal-square convexity scale,
every prime exponent of the comparison integer differs from the superior
anchor exponent by at most one.  The exponent of `2` controls all coordinates,
and its logarithmic bound explains the deliberately coarse affine denominator
`3 * log x + 2`. -/
theorem factorization_within_one_of_power_benefit_bound
    {C γ ε : ℝ} {N M p : ℕ}
    (hε : 0 < ε) (hN : Superior ε N) (hM : 0 < M) (hp : p.Prime)
    (hbenefit : benefit ε N M ≤
      C * (thresholdScale ε 1) ^ (-γ))
    (hsmall : C * (thresholdScale ε 1) ^ (-γ) <
      1 / ((3 * Real.log (thresholdScale ε 1) + 2) ^ 2)) :
    M.factorization p ≤ N.factorization p + 1 ∧
      N.factorization p ≤ M.factorization p + 1 := by
  let x := thresholdScale ε 1
  let a := N.factorization p
  let b := M.factorization p
  have hp2 : 2 ≤ p := hp.two_le
  have haCanonical : a ≤ canonicalExponent ε 2 := by
    calc
      a ≤ canonicalExponent ε p := by
        have hpoint := hN.factorization_le_canonicalFactorization hε p
        simpa [a, canonicalFactorization_apply, hp] using hpoint
      _ ≤ canonicalExponent ε 2 :=
        canonicalExponent_anti_prime hε (by norm_num) hp2
  have haLog : (a : ℝ) ≤ 3 * Real.log x := by
    calc
      (a : ℝ) ≤ canonicalExponent ε 2 := by exact_mod_cast haCanonical
      _ ≤ 3 * Real.log x := by
        simpa [x] using canonicalExponent_two_cast_le_three_mul_log_thresholdScale hε
  have hx1 : 1 < x := by simpa [x] using one_lt_thresholdScale_one hε
  have hlogx : 0 < Real.log x := Real.log_pos hx1
  have haffPos : 0 < (3 * Real.log x + 2) ^ 2 := by positivity
  have hopt : PrimeExponentOptimal ε p a := by
    simpa [a] using hN.primeExponentOptimal hp
  have hlocal : localBenefit ε p a b ≤ benefit ε N M := by
    simpa [a, b] using localBenefit_le_benefit_of_superior (p := p) hN hM
  have hsmall' : benefit ε N M <
      1 / ((3 * Real.log x + 2) ^ 2) := by
    exact hbenefit.trans_lt (by simpa [x] using hsmall)
  constructor
  · by_contra hnot
    have hab : a + 2 ≤ b := by omega
    have hloss := hopt.two_raise_loss_le hab
    have hdenom :
        ((a : ℝ) + 2) ^ 2 ≤ (3 * Real.log x + 2) ^ 2 := by
      rw [sq_le_sq₀ (by positivity : 0 ≤ (a : ℝ) + 2)
        (by positivity : 0 ≤ 3 * Real.log x + 2)]
      linarith
    have hinv :
        1 / ((3 * Real.log x + 2) ^ 2) ≤ 1 / (((a : ℝ) + 2) ^ 2) :=
      one_div_le_one_div_of_le (by positivity) hdenom
    have hrec := two_raise_loss_reciprocal_square_le a
    dsimp [a, b] at hloss hlocal ⊢
    have : benefit ε N M <
        Real.log (1 + 1 / ((a + 1 : ℕ) : ℝ)) -
          Real.log (1 + 1 / ((a + 2 : ℕ) : ℝ)) :=
      hsmall'.trans_le (hinv.trans hrec)
    linarith
  · by_cases haSmall : a ≤ 1
    · omega
    · have ha2 : 2 ≤ a := by omega
      by_contra hnot
      have hab : b + 2 ≤ a := by omega
      have hloss := hopt.two_lower_loss_le hab
      have hdenom : (a : ℝ) ^ 2 ≤
          (3 * Real.log x + 2) ^ 2 := by
        rw [sq_le_sq₀ (by positivity : 0 ≤ (a : ℝ))
          (by positivity : 0 ≤ 3 * Real.log x + 2)]
        linarith
      have hinv :
          1 / ((3 * Real.log x + 2) ^ 2) ≤ 1 / ((a : ℝ) ^ 2) :=
        one_div_le_one_div_of_le (by positivity) hdenom
      have hrec := two_lower_loss_reciprocal_square_le ha2
      dsimp [a, b] at hloss hlocal ⊢
      have : benefit ε N M <
          Real.log (1 + 1 / ((a - 1 : ℕ) : ℝ)) -
            Real.log (1 + 1 / (a : ℝ)) :=
        hsmall'.trans_le (hinv.trans hrec)
      linarith

/-- Coarse integral cap for the exponent at `2` in a localized comparison
integer. -/
noncomputable def localExponentLimit (ε : ℝ) : ℕ :=
  ⌈3 * Real.log (thresholdScale ε 1)⌉₊ + 1

theorem factorization_two_le_localExponentLimit
    {ε : ℝ} {N M : ℕ} (hε : 0 < ε) (hN : Superior ε N)
    (hwithin : M.factorization 2 ≤ N.factorization 2 + 1) :
    M.factorization 2 ≤ localExponentLimit ε := by
  have hNCanonical : N.factorization 2 ≤ canonicalExponent ε 2 := by
    have hpoint := hN.factorization_le_canonicalFactorization hε 2
    simpa [canonicalFactorization_apply, Nat.prime_two] using hpoint
  have hCanonicalCeil : canonicalExponent ε 2 ≤
      ⌈3 * Real.log (thresholdScale ε 1)⌉₊ := by
    have hreal := canonicalExponent_two_cast_le_three_mul_log_thresholdScale hε
    have hceil : 3 * Real.log (thresholdScale ε 1) ≤
        (⌈3 * Real.log (thresholdScale ε 1)⌉₊ : ℝ) := Nat.le_ceil _
    exact_mod_cast hreal.trans hceil
  dsimp [localExponentLimit]
  omega

/-- The extra coordinate recording the exponent at `2` also has polynomial
size in the first threshold. -/
theorem localExponentLimit_add_one_le_ceil_cube
    {ε : ℝ} (hε : 0 < ε) :
    localExponentLimit ε + 1 ≤ ⌈thresholdScale ε 1⌉₊ ^ 3 := by
  let x := thresholdScale ε 1
  let R := ⌈x⌉₊
  let L := localExponentLimit ε
  have hx1 : 1 < x := by simpa [x] using one_lt_thresholdScale_one hε
  have hxPos : 0 < x := zero_lt_one.trans hx1
  have hlogx : 0 < Real.log x := Real.log_pos hx1
  have hxR : x ≤ (R : ℝ) := by
    dsimp [R]
    exact Nat.le_ceil x
  have hRtwo : 2 ≤ R := by
    have hRone : (1 : ℝ) < R := hx1.trans_le hxR
    exact_mod_cast hRone
  have hLlt : (L : ℝ) < 3 * Real.log x + 2 := by
    have hy : 0 ≤ 3 * Real.log x := mul_nonneg (by norm_num) hlogx.le
    have hceil := Nat.ceil_lt_add_one hy
    dsimp [L, localExponentLimit]
    push_cast
    linarith
  have hlog : Real.log x < x - 1 :=
    Real.log_lt_sub_one_of_pos hxPos hx1.ne'
  have hthreeR : (3 : ℝ) * R ≤ (R : ℝ) ^ 3 := by
    have hRreal : (2 : ℝ) ≤ R := by exact_mod_cast hRtwo
    nlinarith [sq_nonneg ((R : ℝ) - 2)]
  have hreal : ((L + 1 : ℕ) : ℝ) ≤ (R : ℝ) ^ 3 := by
    push_cast
    calc
      (L : ℝ) + 1 ≤ 3 * Real.log x + 3 := by linarith
      _ ≤ 3 * x := by linarith
      _ ≤ 3 * (R : ℝ) := by gcongr
      _ ≤ (R : ℝ) ^ 3 := hthreeR
  exact_mod_cast hreal

theorem three_pow_localExponentLimit_le_ceil_pow
    {ε : ℝ} (hε : 0 < ε) :
    3 ^ localExponentLimit ε ≤ ⌈thresholdScale ε 1⌉₊ ^ 13 := by
  let x := thresholdScale ε 1
  let R := ⌈x⌉₊
  let L := localExponentLimit ε
  have hx1 : 1 < x := by simpa [x] using one_lt_thresholdScale_one hε
  have hxPos : 0 < x := zero_lt_one.trans hx1
  have hlogx : 0 < Real.log x := Real.log_pos hx1
  have hxR : x ≤ (R : ℝ) := by
    dsimp [R]
    exact Nat.le_ceil x
  have hRtwo : 2 ≤ R := by
    have hRone : (1 : ℝ) < R := hx1.trans_le hxR
    exact_mod_cast hRone
  have hLlt : (L : ℝ) < 3 * Real.log x + 2 := by
    have hy : 0 ≤ 3 * Real.log x := by positivity
    have hceil := Nat.ceil_lt_add_one hy
    dsimp [L, localExponentLimit]
    push_cast
    linarith
  have hlogThree : Real.log 3 ≤ 2 :=
    (Real.log_three_lt_d9.trans (by norm_num)).le
  have harg : Real.log 3 * (L : ℝ) ≤ 6 * Real.log x + 4 := by
    calc
      Real.log 3 * (L : ℝ) ≤ 2 * (L : ℝ) :=
        mul_le_mul_of_nonneg_right hlogThree (by positivity)
      _ ≤ 2 * (3 * Real.log x + 2) := by gcongr
      _ = 6 * Real.log x + 4 := by ring
  have hexpFour : Real.exp 4 ≤ 81 := by
    calc
      Real.exp 4 = Real.exp 1 ^ 4 := by
        simpa using Real.exp_nat_mul (1 : ℝ) 4
      _ ≤ (3 : ℝ) ^ 4 :=
        pow_le_pow_left₀ (Real.exp_pos 1).le Real.exp_one_lt_three.le 4
      _ = 81 := by norm_num
  have hreal : ((3 ^ L : ℕ) : ℝ) ≤ (R : ℝ) ^ 13 := by
    have hxPow : x ^ 6 ≤ (R : ℝ) ^ 6 :=
      pow_le_pow_left₀ hxPos.le hxR 6
    have hconst : (81 : ℝ) ≤ (R : ℝ) ^ 7 := by
      have hpow : (2 : ℝ) ^ 7 ≤ (R : ℝ) ^ 7 := by
        apply pow_le_pow_left₀ (by norm_num) (by exact_mod_cast hRtwo)
      norm_num at hpow ⊢
      linarith
    calc
      ((3 ^ L : ℕ) : ℝ) = (3 : ℝ) ^ L := by norm_num
      _ = (3 : ℝ) ^ (L : ℝ) := (Real.rpow_natCast 3 L).symm
      _ = Real.exp (Real.log 3 * (L : ℝ)) := by
        rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 3)]
      _ ≤ Real.exp (6 * Real.log x + 4) := Real.exp_le_exp.mpr harg
      _ = x ^ 6 * Real.exp 4 := by
        rw [Real.exp_add]
        congr 1
        calc
          Real.exp (6 * Real.log x) = Real.exp (Real.log x) ^ 6 := by
            simpa using Real.exp_nat_mul (Real.log x) 6
          _ = x ^ 6 := by rw [Real.exp_log hxPos]
      _ ≤ 81 * x ^ 6 := by nlinarith [show 0 ≤ x ^ 6 by positivity]
      _ ≤ (R : ℝ) ^ 7 * (R : ℝ) ^ 6 := by
        exact mul_le_mul hconst hxPow (by positivity) (by positivity)
      _ = (R : ℝ) ^ 13 := by rw [← pow_add]
  exact_mod_cast hreal

theorem two_pow_canonicalExponent_two_le_thresholdScale_cube
    {ε : ℝ} (hε : 0 < ε) :
    ((2 ^ canonicalExponent ε 2 : ℕ) : ℝ) ≤
      (thresholdScale ε 1) ^ 3 := by
  let x := thresholdScale ε 1
  have hxpos : 0 < x := thresholdScale_pos (by omega)
  have hxone : 1 < x := by
    dsimp [x]
    rw [thresholdScale]
    norm_num only [Nat.cast_one, div_one, one_add_one_eq_two]
    exact Real.one_lt_rpow (by norm_num) (one_div_pos.mpr hε)
  have hlogx : 0 ≤ Real.log x := (Real.log_pos hxone).le
  have ha : (canonicalExponent ε 2 : ℝ) ≤ 3 * Real.log x := by
    simpa [x] using canonicalExponent_two_cast_le_three_mul_log_thresholdScale hε
  have hlog2le : Real.log 2 ≤ 1 := by
    exact (Real.log_two_lt_d9.trans (by norm_num)).le
  calc
    ((2 ^ canonicalExponent ε 2 : ℕ) : ℝ) =
        (2 : ℝ) ^ canonicalExponent ε 2 := by norm_num
    _ = (2 : ℝ) ^ (canonicalExponent ε 2 : ℝ) :=
      (Real.rpow_natCast 2 (canonicalExponent ε 2)).symm
    _ ≤ (2 : ℝ) ^ (3 * Real.log x) :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num) ha
    _ = Real.exp (Real.log 2 * (3 * Real.log x)) := by
      rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2)]
    _ ≤ Real.exp (3 * Real.log x) := by
      apply Real.exp_le_exp.mpr
      nlinarith
    _ = x ^ 3 := by
      calc
        Real.exp (3 * Real.log x) = Real.exp (Real.log x) ^ 3 := by
          simpa using Real.exp_nat_mul (Real.log x) 3
        _ = x ^ 3 := by rw [Real.exp_log hxpos]
    _ = (thresholdScale ε 1) ^ 3 := rfl

theorem card_superiorNumbersAt_le_threshold_bound_cube {ε : ℝ}
    (hε : 0 < ε) {B : ℕ} (hB : thresholdScale ε 1 ≤ (B : ℝ)) :
    (superiorNumbersAt ε hε).card ≤ B ^ 3 := by
  have hcard :
      ((superiorNumbersAt ε hε).card : ℝ) ≤
        ((2 ^ canonicalExponent ε 2 : ℕ) : ℝ) := by
    exact_mod_cast card_superiorNumbersAt_le_two_pow_canonicalExponent_two ε hε
  have hscale := two_pow_canonicalExponent_two_le_thresholdScale_cube hε
  have hcubes : (thresholdScale ε 1) ^ 3 ≤ (B : ℝ) ^ 3 := by
    gcongr
    exact (thresholdScale_pos (by omega)).le
  have htotal :
      ((superiorNumbersAt ε hε).card : ℝ) ≤ ((B ^ 3 : ℕ) : ℝ) := by
    norm_num only [Nat.cast_pow]
    exact hcard.trans (hscale.trans hcubes)
  exact_mod_cast htotal

theorem canonicalExponent_two_le_log_threshold_bound_cube {ε : ℝ}
    (hε : 0 < ε) {B : ℕ} (hB : thresholdScale ε 1 ≤ (B : ℝ)) :
    canonicalExponent ε 2 ≤ Nat.log 2 (B ^ 3) := by
  have hscale := two_pow_canonicalExponent_two_le_thresholdScale_cube hε
  have hcubes : (thresholdScale ε 1) ^ 3 ≤ (B : ℝ) ^ 3 := by
    gcongr
    exact (thresholdScale_pos (by omega)).le
  have hpow : 2 ^ canonicalExponent ε 2 ≤ B ^ 3 := by
    exact_mod_cast hscale.trans hcubes
  exact Nat.le_log_of_pow_le Nat.one_lt_two hpow

theorem thresholdScale_lt_iff_rpow_lt {ε y : ℝ} (hε : 0 < ε)
    {k : ℕ} (hk : 0 < k) (hy : 0 ≤ y) :
    thresholdScale ε k < y ↔ 1 + 1 / (k : ℝ) < y ^ ε := by
  rw [← Real.rpow_lt_rpow_iff (thresholdScale_pos hk).le hy hε,
    thresholdScale_rpow hε hk]

theorem le_thresholdScale_iff_rpow_le {ε y : ℝ} (hε : 0 < ε)
    {k : ℕ} (hk : 0 < k) (hy : 0 ≤ y) :
    y ≤ thresholdScale ε k ↔ y ^ ε ≤ 1 + 1 / (k : ℝ) := by
  rw [← Real.rpow_le_rpow_iff hy (thresholdScale_pos hk).le hε,
    thresholdScale_rpow hε hk]

theorem criticalParameter_lt_iff_thresholdScale_lt {ε : ℝ}
    (hε : 0 < ε) {p k : ℕ} (hp : p.Prime) (hk : 0 < k) :
    criticalParameter p k < ε ↔ thresholdScale ε k < p := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hlogp : 0 < Real.log p := Real.log_pos (by exact_mod_cast hp.one_lt)
  have hk' : (0 : ℝ) < k := by exact_mod_cast hk
  rw [criticalParameter, div_lt_iff₀ hlogp, ← Real.log_rpow hp0 ε,
    Real.log_lt_log_iff (by positivity : (0 : ℝ) < 1 + 1 / (k : ℝ))
      (Real.rpow_pos_of_pos hp0 ε)]
  exact (thresholdScale_lt_iff_rpow_lt hε hk hp0.le).symm

theorem le_criticalParameter_iff_le_thresholdScale {ε : ℝ}
    (hε : 0 < ε) {p k : ℕ} (hp : p.Prime) (hk : 0 < k) :
    ε ≤ criticalParameter p k ↔ (p : ℝ) ≤ thresholdScale ε k := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hlogp : 0 < Real.log p := Real.log_pos (by exact_mod_cast hp.one_lt)
  have hk' : (0 : ℝ) < k := by exact_mod_cast hk
  rw [criticalParameter, le_div_iff₀ hlogp, ← Real.log_rpow hp0 ε,
    Real.log_le_log_iff (Real.rpow_pos_of_pos hp0 ε)
      (by positivity : (0 : ℝ) < 1 + 1 / (k : ℝ))]
  exact (le_thresholdScale_iff_rpow_le hε hk hp0.le).symm

/-- At a critical parameter the floor convention chooses the larger of
the two tied exponents. -/
theorem canonicalExponent_criticalParameter {p k : ℕ} (hp : p.Prime)
    (hk : 0 < k) :
    canonicalExponent (criticalParameter p k) p = k := by
  rw [canonicalExponent, rpow_criticalParameter hp hk]
  have hk0 : (k : ℝ) ≠ 0 := by exact_mod_cast hk.ne'
  have hquot : 1 / (1 + 1 / (k : ℝ) - 1) = (k : ℝ) := by
    field_simp
    ring
  rw [hquot]
  exact Nat.floor_natCast k

/-- A positive exponent `k` occurs at `p` precisely up to its critical
parameter. -/
theorem le_canonicalExponent_iff_le_criticalParameter {ε : ℝ}
    (hε : 0 < ε) {p k : ℕ} (hp : p.Prime) (hk : 0 < k) :
    k ≤ canonicalExponent ε p ↔ ε ≤ criticalParameter p k := by
  have hlogp : 0 < Real.log p := Real.log_pos (by exact_mod_cast hp.one_lt)
  rw [criticalParameter, le_div_iff₀ hlogp]
  constructor
  · intro hka
    have ha : 0 < canonicalExponent ε p := hk.trans_le hka
    exact (canonicalExponent_lower_threshold hε hp ha).trans
      (log_one_add_inv_nat_antitone hk hka)
  · intro hparameter
    by_contra hnot
    have hak : canonicalExponent ε p < k := Nat.lt_of_not_ge hnot
    have hsucc : canonicalExponent ε p + 1 ≤ k := hak
    have hraise := canonicalExponent_raise_threshold_strict hε hp
    have hmono := log_one_add_inv_nat_antitone
      (Nat.succ_pos (canonicalExponent ε p)) hsucc
    linarith

/-- Exact half-open interval description of a canonical exponent. -/
theorem canonicalExponent_eq_iff_criticalParameter_interval {ε : ℝ}
    (hε : 0 < ε) {p k : ℕ} (hp : p.Prime) (hk : 0 < k) :
    canonicalExponent ε p = k ↔
      criticalParameter p (k + 1) < ε ∧ ε ≤ criticalParameter p k := by
  constructor
  · intro heq
    constructor
    · by_contra hnot
      have hparameter : ε ≤ criticalParameter p (k + 1) := le_of_not_gt hnot
      have hexp : k + 1 ≤ canonicalExponent ε p :=
        (le_canonicalExponent_iff_le_criticalParameter hε hp (by omega)).2 hparameter
      omega
    · apply (le_canonicalExponent_iff_le_criticalParameter hε hp hk).1
      omega
  · rintro ⟨hlower, hupper⟩
    have hge : k ≤ canonicalExponent ε p :=
      (le_canonicalExponent_iff_le_criticalParameter hε hp hk).2 hupper
    have hnot : ¬k + 1 ≤ canonicalExponent ε p := by
      intro hsucc
      have hparameter : ε ≤ criticalParameter p (k + 1) :=
        (le_canonicalExponent_iff_le_criticalParameter hε hp (by omega)).1 hsucc
      exact (not_le_of_gt hlower) hparameter
    omega

/-- Nicolas's threshold formula
`a_p(ε) = k ↔ x_{k+1} < p ≤ x_k`. -/
theorem canonicalExponent_eq_iff_thresholdScale_interval {ε : ℝ}
    (hε : 0 < ε) {p k : ℕ} (hp : p.Prime) (hk : 0 < k) :
    canonicalExponent ε p = k ↔
      thresholdScale ε (k + 1) < p ∧ (p : ℝ) ≤ thresholdScale ε k := by
  rw [canonicalExponent_eq_iff_criticalParameter_interval hε hp hk,
    criticalParameter_lt_iff_thresholdScale_lt hε hp (by omega),
    le_criticalParameter_iff_le_thresholdScale hε hp hk]

theorem canonicalExponent_pos_iff_le_thresholdScale_one {ε : ℝ}
    (hε : 0 < ε) {p : ℕ} (hp : p.Prime) :
    0 < canonicalExponent ε p ↔ (p : ℝ) ≤ thresholdScale ε 1 := by
  rw [show 0 < canonicalExponent ε p ↔ 1 ≤ canonicalExponent ε p by omega,
    le_canonicalExponent_iff_le_criticalParameter hε hp (by omega),
    le_criticalParameter_iff_le_thresholdScale hε hp (by omega)]

/-- A deliberately coarse uniform exponent bound.  It is more than enough
for the polynomial critical-pair count and avoids optimizing constants. -/
theorem canonicalExponent_le_ceil_thresholdScale_sq {ε : ℝ}
    (hε : 0 < ε) {p : ℕ} (hp : p.Prime) :
    canonicalExponent ε p ≤ ⌈(thresholdScale ε 1) ^ 2⌉₊ := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlogp : Real.log 2 ≤ Real.log p := by
    exact Real.log_le_log (by norm_num) hp2
  have hpow : ε * Real.log p ≤ (p : ℝ) ^ ε - 1 := by
    rw [Real.rpow_def_of_pos hp0]
    nlinarith [Real.add_one_le_exp (Real.log p * ε)]
  have hεlogp : 0 < ε * Real.log p :=
    mul_pos hε (Real.log_pos (by exact_mod_cast hp.one_lt))
  have hεlog2 : 0 < ε * Real.log 2 := mul_pos hε hlog2
  have hrecipP : 1 / ((p : ℝ) ^ ε - 1) ≤ 1 / (ε * Real.log p) :=
    one_div_le_one_div_of_le hεlogp hpow
  have hrecip2 : 1 / (ε * Real.log p) ≤ 1 / (ε * Real.log 2) := by
    apply one_div_le_one_div_of_le hεlog2
    exact mul_le_mul_of_nonneg_left hlogp hε.le
  let t : ℝ := 1 / ε
  have ht : 0 < t := one_div_pos.mpr hε
  have hlog2half : (1 / 2 : ℝ) < Real.log 2 :=
    (by norm_num : (1 / 2 : ℝ) < 0.6931471803).trans Real.log_two_gt_d9
  have hlinear : t / Real.log 2 ≤ 4 * Real.log 2 * t := by
    rw [div_le_iff₀ hlog2]
    nlinarith [sq_nonneg (Real.log 2 - 1 / 2)]
  have hexpLower : 4 * Real.log 2 * t ≤ Real.exp (2 * Real.log 2 * t) := by
    have h := (Real.two_mul_le_exp :
      2 * (2 * Real.log 2 * t) ≤ Real.exp (2 * Real.log 2 * t))
    linarith
  have hscaleExp : Real.exp (2 * Real.log 2 * t) =
      (thresholdScale ε 1) ^ 2 := by
    rw [thresholdScale]
    norm_num
    rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2), pow_two,
      ← Real.exp_add]
    dsimp [t]
    congr 1
    ring
  have hrecipScale : 1 / (ε * Real.log 2) ≤ (thresholdScale ε 1) ^ 2 := by
    calc
      1 / (ε * Real.log 2) = t / Real.log 2 := by dsimp [t]; field_simp
      _ ≤ 4 * Real.log 2 * t := hlinear
      _ ≤ Real.exp (2 * Real.log 2 * t) := hexpLower
      _ = (thresholdScale ε 1) ^ 2 := hscaleExp
  have hfloor := (canonicalExponent_floor_bounds hε hp).1
  have hceil : (thresholdScale ε 1) ^ 2 ≤
      (⌈(thresholdScale ε 1) ^ 2⌉₊ : ℝ) := Nat.le_ceil _
  exact_mod_cast hfloor.trans (hrecipP.trans (hrecip2.trans (hrecipScale.trans hceil)))

theorem canonicalExponent_le_nat_bound_sq {ε : ℝ} (hε : 0 < ε)
    {B p : ℕ} (hp : p.Prime) (hB : thresholdScale ε 1 ≤ (B : ℝ)) :
    canonicalExponent ε p ≤ B ^ 2 := by
  refine (canonicalExponent_le_ceil_thresholdScale_sq hε hp).trans ?_
  rw [Nat.ceil_le]
  have hs : (thresholdScale ε 1) ^ 2 ≤ (B : ℝ) ^ 2 := by
    have hx : 0 ≤ thresholdScale ε 1 := (thresholdScale_pos (by omega)).le
    have hB0 : (0 : ℝ) ≤ B := by positivity
    nlinarith
  exact_mod_cast hs

/-- Exactly the primes up to the first threshold occur in the canonical
superior integer. -/
theorem prime_dvd_canonicalSuperior_iff_le_thresholdScale_one {ε : ℝ}
    (hε : 0 < ε) {p : ℕ} (hp : p.Prime) :
    p ∣ canonicalSuperior ε hε ↔ (p : ℝ) ≤ thresholdScale ε 1 := by
  rw [hp.dvd_iff_one_le_factorization
      (canonicalSuperior_isSuperior ε hε).1.ne',
    factorization_canonicalSuperior, canonicalFactorization_apply, if_pos hp,
    show 1 ≤ canonicalExponent ε p ↔ 0 < canonicalExponent ε p by omega,
    canonicalExponent_pos_iff_le_thresholdScale_one hε hp]

/-- Every prime strictly below the first threshold divides every superior
maximizer, not just the canonical one.  Only a tied prime exactly on the
boundary can be lowered from exponent one to zero. -/
theorem Superior.prime_dvd_of_lt_thresholdScale_one {ε : ℝ}
    (hε : 0 < ε) {N p : ℕ} (hN : Superior ε N) (hp : p.Prime)
    (hpScale : (p : ℝ) < thresholdScale ε 1) : p ∣ N := by
  rw [hp.dvd_iff_one_le_factorization hN.1.ne']
  have haPos : 0 < canonicalExponent ε p :=
    (canonicalExponent_pos_iff_le_thresholdScale_one hε hp).2 hpScale.le
  rcases hN.factorization_eq_canonical_or_tiedLower hε hp with hcanonical | hlower
  · rw [hcanonical]
    omega
  · by_contra hnot
    have hbzero : N.factorization p = 0 := by omega
    have haone : canonicalExponent ε p = 1 := by omega
    have htie : ε * Real.log p = Real.log 2 := by
      have h := hlower.2
      rw [haone] at h
      norm_num at h
      exact h
    have hpPos : (0 : ℝ) < p := by exact_mod_cast hp.pos
    have hpPow : (p : ℝ) ^ ε = 2 := by
      rw [Real.rpow_def_of_pos hpPos, mul_comm, htie, Real.exp_log]
      norm_num
    have hxPow : (thresholdScale ε 1) ^ ε = 2 := by
      have h := thresholdScale_rpow hε (by omega : 0 < (1 : ℕ))
      norm_num at h
      exact h
    have hpEq : (p : ℝ) = thresholdScale ε 1 :=
      (Real.rpow_left_inj hpPos.le (thresholdScale_pos (by omega)).le hε.ne').1
        (hpPow.trans hxPow.symm)
    linarith

theorem primorial_floor_thresholdScale_dvd_superior_mul_floor {ε : ℝ}
    (hε : 0 < ε) {N : ℕ} (hN : Superior ε N) :
    primorial ⌊thresholdScale ε 1⌋₊ ∣
      N * ⌊thresholdScale ε 1⌋₊ := by
  rw [primorial_eq_prod_primesLE]
  apply Finset.prod_primes_dvd (N * ⌊thresholdScale ε 1⌋₊)
  · intro p hp
    exact (Nat.prime_of_mem_primesLE hp).prime
  · intro p hpMem
    have hp := Nat.prime_of_mem_primesLE hpMem
    have hpFloor : p ≤ ⌊thresholdScale ε 1⌋₊ := Nat.le_of_mem_primesLE hpMem
    have hpScale : (p : ℝ) ≤ thresholdScale ε 1 := by
      have : (p : ℝ) ≤ (⌊thresholdScale ε 1⌋₊ : ℝ) := by exact_mod_cast hpFloor
      exact this.trans (Nat.floor_le (thresholdScale_pos (by omega)).le)
    by_cases hlt : (p : ℝ) < thresholdScale ε 1
    · exact dvd_mul_of_dvd_left (hN.prime_dvd_of_lt_thresholdScale_one hε hp hlt) _
    · have hpEq : (p : ℝ) = thresholdScale ε 1 :=
        le_antisymm hpScale (le_of_not_gt hlt)
      have hfloorLe : ⌊thresholdScale ε 1⌋₊ ≤ p := by
        exact_mod_cast (Nat.floor_le (thresholdScale_pos (by omega)).le).trans_eq hpEq.symm
      have hfloorEq : ⌊thresholdScale ε 1⌋₊ = p :=
        le_antisymm hfloorLe hpFloor
      exact dvd_mul_of_dvd_right (by simp [hfloorEq]) N

/-- Chebyshev-scale lower bound for an arbitrary (possibly tied,
noncanonical) superior integer.  The extra logarithm pays for the one
boundary prime which may be absent. -/
theorem theta_thresholdScale_le_log_superior_add_log_thresholdScale
    {ε : ℝ} (hε : 0 < ε) {N : ℕ} (hN : Superior ε N) :
    Chebyshev.theta (thresholdScale ε 1) ≤
      Real.log N + Real.log (thresholdScale ε 1) := by
  let x := thresholdScale ε 1
  have hxpos : 0 < x := thresholdScale_pos (by omega)
  have hxone : 1 < x := one_lt_thresholdScale_one hε
  have hfloorPos : 0 < ⌊x⌋₊ := by
    apply lt_of_lt_of_le Nat.zero_lt_one
    apply Nat.le_floor
    norm_num
    exact hxone.le
  have hprodPos : 0 < N * ⌊x⌋₊ := Nat.mul_pos hN.1 hfloorPos
  have hdvd : primorial ⌊x⌋₊ ∣ N * ⌊x⌋₊ := by
    simpa [x] using primorial_floor_thresholdScale_dvd_superior_mul_floor hε hN
  have hfloorLog : Real.log (⌊x⌋₊ : ℕ) ≤ Real.log x := by
    apply Real.log_le_log
    · exact_mod_cast hfloorPos
    · exact Nat.floor_le hxpos.le
  rw [Chebyshev.theta_eq_log_primorial]
  calc
    Real.log (primorial ⌊x⌋₊) ≤ Real.log (N * ⌊x⌋₊) := by
      apply Real.log_le_log
      · exact_mod_cast primorial_pos ⌊x⌋₊
      · exact_mod_cast Nat.le_of_dvd hprodPos hdvd
    _ = Real.log N + Real.log (⌊x⌋₊ : ℕ) := by
      rw [Real.log_mul]
      · exact_mod_cast hN.1.ne'
      · exact_mod_cast hfloorPos.ne'
    _ ≤ Real.log N + Real.log x := by linarith
    _ = Real.log N + Real.log (thresholdScale ε 1) := rfl

theorem primorial_floor_thresholdScale_dvd_canonicalSuperior {ε : ℝ}
    (hε : 0 < ε) :
    primorial ⌊thresholdScale ε 1⌋₊ ∣ canonicalSuperior ε hε := by
  rw [primorial_eq_prod_primesLE]
  apply Finset.prod_primes_dvd (canonicalSuperior ε hε)
  · intro p hp
    exact (Nat.prime_of_mem_primesLE hp).prime
  · intro p hp
    have hpPrime := Nat.prime_of_mem_primesLE hp
    apply (prime_dvd_canonicalSuperior_iff_le_thresholdScale_one hε hpPrime).2
    have hpFloor : (p : ℝ) ≤ (⌊thresholdScale ε 1⌋₊ : ℝ) := by
      exact_mod_cast Nat.le_of_mem_primesLE hp
    exact hpFloor.trans (Nat.floor_le (thresholdScale_pos (by omega)).le)

/-- The first threshold is at most the logarithmic size of the canonical
integer in Chebyshev's `θ` scale. -/
theorem theta_thresholdScale_le_log_canonicalSuperior {ε : ℝ}
    (hε : 0 < ε) :
    Chebyshev.theta (thresholdScale ε 1) ≤
      Real.log (canonicalSuperior ε hε) := by
  rw [Chebyshev.theta_eq_log_primorial]
  apply Real.log_le_log
  · exact_mod_cast primorial_pos ⌊thresholdScale ε 1⌋₊
  · exact_mod_cast Nat.le_of_dvd (canonicalSuperior_isSuperior ε hε).1
      (primorial_floor_thresholdScale_dvd_canonicalSuperior hε)

/-- An axiom-free consequence of the project PNT: eventually `x` is bounded
by a fixed multiple of `θ(x)`. -/
theorem eventually_self_le_const_mul_theta :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ x : ℝ in atTop, x ≤ C * Chebyshev.theta x := by
  obtain ⟨c, hc⟩ := chebyshev_asymptotic.isBigO_symm.bound
  let C : ℝ := max c 1
  refine ⟨C, zero_lt_one.trans_le (le_max_right c 1), ?_⟩
  filter_upwards [hc, eventually_ge_atTop (0 : ℝ)] with x hx hx0
  have hx' : x ≤ c * Chebyshev.theta x := by
    simpa [Real.norm_of_nonneg hx0,
      Real.norm_of_nonneg (Chebyshev.theta_nonneg x)] using hx
  exact hx'.trans (mul_le_mul_of_nonneg_right (le_max_left c 1)
    (Chebyshev.theta_nonneg x))

theorem tendsto_thresholdScale_one_nhdsGT_zero :
    Tendsto (fun ε : ℝ ↦ thresholdScale ε 1) (𝓝[>] 0) atTop := by
  have h := (tendsto_rpow_atTop_of_base_gt_one 2 (by norm_num)).comp
    tendsto_inv_nhdsGT_zero
  convert h using 1
  ext ε
  norm_num [thresholdScale, one_div]

/-- Consequently the threshold scale attached to a canonical superior
integer is `O(log N)` as the parameter tends to zero. -/
theorem eventually_thresholdScale_le_const_mul_log_canonicalSuperior :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ ε : ℝ in 𝓝[>] 0,
      ∀ hε : 0 < ε,
        thresholdScale ε 1 ≤ C * Real.log (canonicalSuperior ε hε) := by
  obtain ⟨C, hC, htheta⟩ := eventually_self_le_const_mul_theta
  refine ⟨C, hC, ?_⟩
  filter_upwards [tendsto_thresholdScale_one_nhdsGT_zero.eventually htheta,
    self_mem_nhdsWithin] with ε hscale hε
  intro hεpos
  exact hscale.trans (mul_le_mul_of_nonneg_left
    (theta_thresholdScale_le_log_canonicalSuperior hεpos) hC.le)

/-- The same logarithmic scale bound for every tied maximizer.  The proof
absorbs the one possible missing boundary prime using `log x = o(x)`. -/
theorem eventually_thresholdScale_le_const_mul_log_superior :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ ε : ℝ in 𝓝[>] 0,
      ∀ N : ℕ, Superior ε N →
        thresholdScale ε 1 ≤ C * Real.log N := by
  obtain ⟨C, hC, htheta⟩ := eventually_self_le_const_mul_theta
  have hcoeff : 0 < (1 / (2 * C) : ℝ) := by positivity
  have hlog := Real.isLittleO_log_id_atTop.bound hcoeff
  have hlarge : ∀ᶠ x : ℝ in atTop,
      x ≤ C * Chebyshev.theta x ∧
        ‖Real.log x‖ ≤ (1 / (2 * C)) * ‖x‖ ∧ 1 ≤ x := by
    filter_upwards [htheta, hlog, eventually_ge_atTop (1 : ℝ)] with x hx hlogx hxone
    exact ⟨hx, hlogx, hxone⟩
  refine ⟨2 * C, mul_pos (by norm_num) hC, ?_⟩
  filter_upwards [tendsto_thresholdScale_one_nhdsGT_zero.eventually hlarge,
    self_mem_nhdsWithin] with ε hx hεmem
  intro N hN
  have hε : 0 < ε := hεmem
  let x := thresholdScale ε 1
  have hxpos : 0 < x := thresholdScale_pos (by omega)
  have hlogNonneg : 0 ≤ Real.log x := Real.log_nonneg hx.2.2
  have hlogSmall : Real.log x ≤ (1 / (2 * C)) * x := by
    change Real.log (thresholdScale ε 1) ≤
      (1 / (2 * C)) * thresholdScale ε 1
    simpa only [Real.norm_eq_abs,
      abs_of_nonneg (by simpa [x] using hlogNonneg),
      abs_of_nonneg (by simpa [x] using hxpos.le)] using hx.2.1
  have hthetaN :=
    theta_thresholdScale_le_log_superior_add_log_thresholdScale hε hN
  dsimp [x] at hxpos hlogNonneg hlogSmall hthetaN ⊢
  have hmain := hx.1.trans (mul_le_mul_of_nonneg_left hthetaN hC.le)
  have hClog : C * Real.log (thresholdScale ε 1) ≤
      thresholdScale ε 1 / 2 := by
    calc
      C * Real.log (thresholdScale ε 1) ≤
          C * ((1 / (2 * C)) * thresholdScale ε 1) :=
        mul_le_mul_of_nonneg_left hlogSmall hC.le
      _ = thresholdScale ε 1 / 2 := by field_simp
  nlinarith

/-- Uniform version for all positive parameters: parameters away from zero
contribute only a fixed threshold, while the small-parameter range is
controlled logarithmically. -/
theorem thresholdScale_le_const_add_const_mul_log_superior :
    ∃ C B : ℝ, 0 < C ∧ 0 < B ∧
      ∀ (ε : ℝ), 0 < ε → ∀ N : ℕ, Superior ε N →
        thresholdScale ε 1 ≤ B + C * Real.log N := by
  obtain ⟨C, hC, hsmall⟩ :=
    eventually_thresholdScale_le_const_mul_log_superior
  have hnhds : ∀ᶠ ε : ℝ in 𝓝 0,
      ε ∈ Set.Ioi 0 →
        ∀ N : ℕ, Superior ε N →
          thresholdScale ε 1 ≤ C * Real.log N :=
    (eventually_nhdsWithin_iff).1 hsmall
  rw [Metric.eventually_nhds_iff] at hnhds
  obtain ⟨δ, hδ, hδprop⟩ := hnhds
  let η := δ / 2
  have hη : 0 < η := half_pos hδ
  let B := thresholdScale η 1
  have hB : 0 < B := thresholdScale_pos (by omega)
  refine ⟨C, B, hC, hB, ?_⟩
  intro ε hε N hN
  have hlogN : 0 ≤ Real.log N :=
    Real.log_nonneg (by exact_mod_cast hN.1)
  by_cases hεδ : ε < δ
  · have hdist : dist ε 0 < δ := by
      simpa [Real.dist_eq, abs_of_pos hε] using hεδ
    have hbound := hδprop hdist hε N hN
    exact hbound.trans (le_add_of_nonneg_left hB.le)
  · have hηε : η ≤ ε := by
      dsimp [η]
      have hδε : δ ≤ ε := le_of_not_gt hεδ
      linarith
    have hbound : thresholdScale ε 1 ≤ B := by
      dsimp [B]
      exact thresholdScale_antitone_parameter hη hηε (by omega)
    exact hbound.trans (le_add_of_nonneg_right
      (mul_nonneg hC.le hlogN))

/-- Lowering the critical exponent by one has exactly zero local benefit. -/
theorem localBenefit_criticalParameter_lower_eq_zero {p k : ℕ}
    (hp : p.Prime) (hk : 0 < k) :
    localBenefit (criticalParameter p k) p k (k - 1) = 0 := by
  have hpred : k - 1 + 1 = k := Nat.sub_add_cancel hk
  have h := localBenefit_lower (criticalParameter p k) p (k - 1)
  simp only [hpred] at h
  rw [h, criticalParameter_mul_log hp]
  ring

/-- The lower exponent at a critical parameter is locally optimal as well. -/
theorem criticalPredecessor_primeExponentOptimal {p k : ℕ}
    (hp : p.Prime) (hk : 0 < k) :
    PrimeExponentOptimal (criticalParameter p k) p (k - 1) := by
  intro b
  have hopt := canonicalExponent_primewiseOptimal
    (criticalParameter_pos hp hk) hp b
  rw [canonicalExponent_criticalParameter hp hk] at hopt
  have hcocycle := localBenefit_cocycle
    (criticalParameter p k) p k (k - 1) b
  rw [localBenefit_criticalParameter_lower_eq_zero hp hk, zero_add] at hcocycle
  rwa [← hcocycle]

/-- The lower tied exponent vector at a critical parameter. -/
noncomputable def criticalLowerFactorization (p k : ℕ) (hp : p.Prime)
    (hk : 0 < k) : ℕ →₀ ℕ :=
  (canonicalFactorization (criticalParameter p k)
    (criticalParameter_pos hp hk)).update p (k - 1)

@[simp] theorem criticalLowerFactorization_apply_same {p k : ℕ}
    (hp : p.Prime) (hk : 0 < k) :
    criticalLowerFactorization p k hp hk p = k - 1 := by
  simp [criticalLowerFactorization]

theorem criticalLowerFactorization_apply_ne {p k q : ℕ}
    (hp : p.Prime) (hk : 0 < k) (hqp : q ≠ p) :
    criticalLowerFactorization p k hp hk q =
      canonicalFactorization (criticalParameter p k)
        (criticalParameter_pos hp hk) q := by
  simp [criticalLowerFactorization, hqp]

theorem criticalLowerFactorization_prime_support {p k : ℕ}
    (hp : p.Prime) (hk : 0 < k) :
    ∀ q ∈ (criticalLowerFactorization p k hp hk).support, q.Prime := by
  intro q hq
  change q ∈ ((canonicalFactorization (criticalParameter p k)
    (criticalParameter_pos hp hk)).update p (k - 1)).support at hq
  have hmem : q ∈ insert p
      (canonicalFactorization (criticalParameter p k)
        (criticalParameter_pos hp hk)).support :=
    Finsupp.support_update_subset
      (f := canonicalFactorization (criticalParameter p k)
        (criticalParameter_pos hp hk)) (a := p) (b := k - 1) hq
  rcases Finset.mem_insert.mp hmem with rfl | hqCanonical
  · exact hp
  · exact canonicalFactorization_prime_support
      (criticalParameter p k) (criticalParameter_pos hp hk) q hqCanonical

theorem criticalLowerFactorization_primewiseOptimal {p k : ℕ}
    (hp : p.Prime) (hk : 0 < k) :
    ∀ q : ℕ, q.Prime →
      PrimeExponentOptimal (criticalParameter p k) q
        (criticalLowerFactorization p k hp hk q) := by
  intro q hq
  by_cases hqp : q = p
  · subst q
    simpa only [criticalLowerFactorization_apply_same] using
      criticalPredecessor_primeExponentOptimal hp hk
  · rw [criticalLowerFactorization_apply_ne hp hk hqp,
      canonicalFactorization_apply, if_pos hq]
    exact canonicalExponent_primewiseOptimal (criticalParameter_pos hp hk) hq

/-- The smaller of the two tied superior integers at a critical parameter. -/
noncomputable def criticalLowerSuperior (p k : ℕ) (hp : p.Prime)
    (hk : 0 < k) : ℕ :=
  fromFactorization (criticalLowerFactorization p k hp hk)

theorem criticalLowerSuperior_isSuperior {p k : ℕ}
    (hp : p.Prime) (hk : 0 < k) :
    Superior (criticalParameter p k) (criticalLowerSuperior p k hp hk) := by
  rw [criticalLowerSuperior]
  exact superior_from_primewise_optimal
    (criticalLowerFactorization_prime_support hp hk)
    (criticalLowerFactorization_primewiseOptimal hp hk)

theorem criticalLowerSuperior_highlyComposite {p k : ℕ}
    (hp : p.Prime) (hk : 0 < k) :
    HighlyComposite (criticalLowerSuperior p k hp hk) :=
  (criticalLowerSuperior_isSuperior hp hk).highlyComposite
    (criticalParameter_pos hp hk)

theorem criticalLowerFactorization_add_single {p k : ℕ}
    (hp : p.Prime) (hk : 0 < k) :
    criticalLowerFactorization p k hp hk + Finsupp.single p 1 =
      canonicalFactorization (criticalParameter p k)
        (criticalParameter_pos hp hk) := by
  ext q
  by_cases hqp : q = p
  · subst q
    simp [criticalLowerFactorization, canonicalFactorization_apply, hp,
      canonicalExponent_criticalParameter hp hk, Nat.sub_add_cancel hk]
  · simp [criticalLowerFactorization, hqp]

/-- The two tied integers differ by exactly the critical prime. -/
theorem criticalLowerSuperior_mul_prime {p k : ℕ}
    (hp : p.Prime) (hk : 0 < k) :
    criticalLowerSuperior p k hp hk * p =
      canonicalSuperior (criticalParameter p k) (criticalParameter_pos hp hk) := by
  have h := congrArg fromFactorization
    (criticalLowerFactorization_add_single hp hk)
  simpa [criticalLowerSuperior, canonicalSuperior, fromFactorization_add] using h

theorem criticalLowerSuperior_lt_canonical {p k : ℕ}
    (hp : p.Prime) (hk : 0 < k) :
    criticalLowerSuperior p k hp hk <
      canonicalSuperior (criticalParameter p k) (criticalParameter_pos hp hk) := by
  rw [← criticalLowerSuperior_mul_prime hp hk]
  exact lt_mul_of_one_lt_right
    (criticalLowerSuperior_isSuperior hp hk).1 hp.one_lt

/-! ### A finite rank for bounded critical transitions -/

/-- Candidate critical pairs with prime at most `B` and positive exponent at
most `K`. -/
def criticalPairs (B K : ℕ) : Finset (ℕ × ℕ) :=
  (Nat.primesLE B).product (Finset.Icc 1 K)

/-- Number of bounded critical parameters strictly below `ε`. -/
noncomputable def criticalRank (B K : ℕ) (ε : ℝ) : ℕ :=
  ((criticalPairs B K).filter
    (fun pk ↦ criticalParameter pk.1 pk.2 < ε)).card

theorem criticalRank_le_card (B K : ℕ) (ε : ℝ) :
    criticalRank B K ε ≤ (criticalPairs B K).card := by
  exact Finset.card_filter_le _ _

theorem criticalRank_mono (B K : ℕ) : Monotone (criticalRank B K) := by
  intro ε δ hεδ
  apply Finset.card_le_card
  intro pk hpk
  simp only [Finset.mem_filter] at hpk ⊢
  exact ⟨hpk.1, hpk.2.trans_le hεδ⟩

theorem criticalRank_lt_of_crossing {B K p k : ℕ} {ε δ : ℝ}
    (hpB : p ≤ B) (hp : p.Prime) (hk : 1 ≤ k) (hkK : k ≤ K)
    (hleft : ε ≤ criticalParameter p k)
    (hright : criticalParameter p k < δ) :
    criticalRank B K ε < criticalRank B K δ := by
  let A := (criticalPairs B K).filter
    (fun pk ↦ criticalParameter pk.1 pk.2 < ε)
  let D := (criticalPairs B K).filter
    (fun pk ↦ criticalParameter pk.1 pk.2 < δ)
  have hεδ : ε < δ := hleft.trans_lt hright
  have hsubset : A ⊆ D := by
    intro pk hpk
    rw [Finset.mem_filter] at hpk ⊢
    exact ⟨hpk.1, hpk.2.trans hεδ⟩
  have hpair : (p, k) ∈ criticalPairs B K := by
    simp [criticalPairs, Nat.mem_primesLE, hpB, hp, hk, hkK]
  have hmemD : (p, k) ∈ D := by
    simp [D, hpair, hright]
  have hnotmemA : (p, k) ∉ A := by
    simp [A, hpair, not_lt.mpr hleft]
  have hstrict : A ⊂ D := Finset.ssubset_iff_subset_ne.mpr ⟨hsubset, by
    intro heq
    exact hnotmemA (heq ▸ hmemD)⟩
  exact Finset.card_lt_card hstrict

/-- Within fixed prime and exponent bounds, the critical rank determines the
entire canonical exponent vector. -/
theorem canonicalFactorization_eq_of_criticalRank_eq {B K : ℕ} {ε δ : ℝ}
    (hε : 0 < ε) (hδ : 0 < δ)
    (hBε : thresholdScale ε 1 ≤ (B : ℝ))
    (hBδ : thresholdScale δ 1 ≤ (B : ℝ))
    (hKε : ∀ p : ℕ, p.Prime → canonicalExponent ε p ≤ K)
    (hKδ : ∀ p : ℕ, p.Prime → canonicalExponent δ p ≤ K)
    (hrank : criticalRank B K ε = criticalRank B K δ) :
    canonicalFactorization ε hε = canonicalFactorization δ hδ := by
  have eq_of_le : ∀ {a b : ℝ} (ha : 0 < a) (hb : 0 < b), a ≤ b →
      thresholdScale a 1 ≤ (B : ℝ) →
      (∀ p : ℕ, p.Prime → canonicalExponent a p ≤ K) →
      criticalRank B K a = criticalRank B K b →
      canonicalFactorization a ha = canonicalFactorization b hb := by
    intro a b ha hb hab hBa hKa hr
    by_contra hne
    have hle : canonicalFactorization b hb ≤ canonicalFactorization a ha := by
      simpa only using canonicalFactorization_antitone ha hab
    have hexists : ∃ p : ℕ,
        canonicalFactorization b hb p ≠ canonicalFactorization a ha p := by
      by_contra hall
      apply hne
      ext p
      by_contra hpne
      exact hall ⟨p, fun h ↦ hpne h.symm⟩
    obtain ⟨p, hpne⟩ := hexists
    have hlt : canonicalFactorization b hb p < canonicalFactorization a ha p :=
      lt_of_le_of_ne (hle p) hpne
    have hpPrime : p.Prime := by
      by_contra hp
      simp [canonicalFactorization_apply, hp] at hlt
    have hltExp : canonicalExponent b p < canonicalExponent a p := by
      simpa [canonicalFactorization_apply, hpPrime] using hlt
    let k := canonicalExponent a p
    have hk : 1 ≤ k := by dsimp [k]; omega
    have hkK : k ≤ K := hKa p hpPrime
    have hpScale : (p : ℝ) ≤ thresholdScale a 1 :=
      (canonicalExponent_pos_iff_le_thresholdScale_one ha hpPrime).1 (by
        dsimp [k] at hk
        omega)
    have hpB : p ≤ B := by
      exact_mod_cast hpScale.trans hBa
    have hleft : a ≤ criticalParameter p k := by
      apply (le_canonicalExponent_iff_le_criticalParameter ha hpPrime (by omega)).1
      exact le_rfl
    have hright : criticalParameter p k < b := by
      by_contra hnot
      have hbcrit : b ≤ criticalParameter p k := le_of_not_gt hnot
      have hkleb : k ≤ canonicalExponent b p :=
        (le_canonicalExponent_iff_le_criticalParameter hb hpPrime (by omega)).2 hbcrit
      exact (not_le_of_gt hltExp) hkleb
    have hrlt := criticalRank_lt_of_crossing hpB hpPrime hk hkK hleft hright
    exact (ne_of_lt hrlt) hr
  rcases le_total ε δ with hεδ | hδε
  · exact eq_of_le hε hδ hεδ hBε hKε hrank
  · exact (eq_of_le hδ hε hδε hBδ hKδ hrank.symm).symm

/-- Positive parameters whose first threshold is at most `B`. -/
def BoundedCanonicalParameter (B : ℕ) :=
  {ε : ℝ // 0 < ε ∧ thresholdScale ε 1 ≤ (B : ℝ)}

noncomputable def boundedCanonicalFactorization {B : ℕ}
    (u : BoundedCanonicalParameter B) : ℕ →₀ ℕ :=
  canonicalFactorization u.1 u.2.1

noncomputable def boundedCriticalRank {B : ℕ}
    (u : BoundedCanonicalParameter B) : ℕ :=
  criticalRank B (B ^ 2) u.1

/-- Choose the canonical factorization represented by a rank, if that rank is
realized by a bounded parameter. -/
noncomputable def boundedFactorizationAtRank (B r : ℕ) : ℕ →₀ ℕ :=
  by
    classical
    exact if h : ∃ u : BoundedCanonicalParameter B, boundedCriticalRank u = r then
      boundedCanonicalFactorization (Classical.choose h)
    else 0

theorem boundedFactorizationAtRank_eq {B : ℕ}
    (u : BoundedCanonicalParameter B) :
    boundedFactorizationAtRank B (boundedCriticalRank u) =
      boundedCanonicalFactorization u := by
  classical
  rw [boundedFactorizationAtRank]
  split_ifs with h
  · let v : BoundedCanonicalParameter B := Classical.choose h
    have hvrank : boundedCriticalRank v = boundedCriticalRank u :=
      Classical.choose_spec h
    exact canonicalFactorization_eq_of_criticalRank_eq
      v.2.1 u.2.1 v.2.2 u.2.2
      (fun p hp ↦ canonicalExponent_le_nat_bound_sq v.2.1 hp v.2.2)
      (fun p hp ↦ canonicalExponent_le_nat_bound_sq u.2.1 hp u.2.2)
      hvrank
  · exact False.elim (h ⟨u, rfl⟩)

/-- A concrete finite set containing every canonical exponent vector whose
first threshold is at most `B`. -/
noncomputable def boundedCanonicalFactorizations (B : ℕ) : Finset (ℕ →₀ ℕ) :=
  by
    classical
    exact (Finset.range ((criticalPairs B (B ^ 2)).card + 1)).image
      (boundedFactorizationAtRank B)

theorem boundedCanonicalFactorization_mem {B : ℕ}
    (u : BoundedCanonicalParameter B) :
    boundedCanonicalFactorization u ∈ boundedCanonicalFactorizations B := by
  classical
  rw [boundedCanonicalFactorizations, Finset.mem_image]
  refine ⟨boundedCriticalRank u, ?_, ?_⟩
  · rw [Finset.mem_range]
    exact Nat.lt_succ_of_le (criticalRank_le_card B (B ^ 2) u.1)
  · exact boundedFactorizationAtRank_eq u

theorem card_boundedCanonicalFactorizations_le (B : ℕ) :
    (boundedCanonicalFactorizations B).card ≤
      (criticalPairs B (B ^ 2)).card + 1 := by
  classical
  rw [boundedCanonicalFactorizations]
  simpa using (Finset.card_image_le
    (s := Finset.range ((criticalPairs B (B ^ 2)).card + 1))
    (f := boundedFactorizationAtRank B))

theorem card_criticalPairs (B K : ℕ) :
    (criticalPairs B K).card = Nat.primeCounting B * K := by
  simp [criticalPairs, Nat.primesLE_card_eq_primeCounting]

theorem card_boundedCanonicalFactorizations_polynomial (B : ℕ) :
    (boundedCanonicalFactorizations B).card ≤ (B + 1) * B ^ 2 + 1 := by
  have hpi : Nat.primeCounting B ≤ B + 1 := by
    rw [← Nat.primesLE_card_eq_primeCounting]
    have hsubset : Nat.primesLE B ⊆ Finset.range (B + 1) := by
      intro p hp
      exact Finset.mem_range.mpr (Nat.lt_succ_of_le (Nat.le_of_mem_primesLE hp))
    exact (Finset.card_le_card hsubset).trans_eq (Finset.card_range (B + 1))
  calc
    (boundedCanonicalFactorizations B).card ≤
        (criticalPairs B (B ^ 2)).card + 1 :=
      card_boundedCanonicalFactorizations_le B
    _ = Nat.primeCounting B * B ^ 2 + 1 := by rw [card_criticalPairs]
    _ ≤ (B + 1) * B ^ 2 + 1 := by gcongr

/-! ### The full bounded superior sequence

The canonical rank alone misses simultaneous tied choices.  We now add the
set of lowered *exponent values* as a second code.  Tied primes have distinct
exponent values, and their number is logarithmic in the threshold, so this
still gives a polynomial finite family. -/

def BoundedSuperior (B N : ℕ) : Prop :=
  ∃ ε : ℝ, 0 < ε ∧ thresholdScale ε 1 ≤ (B : ℝ) ∧ Superior ε N

noncomputable instance boundedSuperiorDecidable (B N : ℕ) :
    Decidable (BoundedSuperior B N) := Classical.dec _

noncomputable def boundedSuperiorParameter (B N : ℕ) : {ε : ℝ // 0 < ε} :=
  if h : BoundedSuperior B N then
    ⟨Classical.choose h, (Classical.choose_spec h).1⟩
  else ⟨1, by norm_num⟩

theorem boundedSuperiorParameter_spec {B N : ℕ} (hN : BoundedSuperior B N) :
    thresholdScale (boundedSuperiorParameter B N).1 1 ≤ (B : ℝ) ∧
      Superior (boundedSuperiorParameter B N).1 N := by
  rw [boundedSuperiorParameter, dif_pos hN]
  exact (Classical.choose_spec hN).2

def boundedExponentLimit (B : ℕ) : ℕ := Nat.log 2 (B ^ 3)

noncomputable def boundedSuperiorCode (B N : ℕ) : ℕ × Finset ℕ :=
  let u := boundedSuperiorParameter B N
  (criticalRank B (boundedExponentLimit B) u.1,
    loweringExponentCode u.1 u.2 N)

noncomputable def boundedSuperiorCodes (B : ℕ) : Finset (ℕ × Finset ℕ) :=
  (Finset.range ((criticalPairs B (boundedExponentLimit B)).card + 1)).product
    ((Finset.Icc 1 (boundedExponentLimit B)).powerset)

theorem boundedSuperiorCode_mem {B N : ℕ} (hN : BoundedSuperior B N) :
    boundedSuperiorCode B N ∈ boundedSuperiorCodes B := by
  let u := boundedSuperiorParameter B N
  have hu := boundedSuperiorParameter_spec hN
  have ha2 : canonicalExponent u.1 2 ≤ boundedExponentLimit B := by
    exact canonicalExponent_two_le_log_threshold_bound_cube u.2 hu.1
  rw [boundedSuperiorCode, boundedSuperiorCodes]
  change (criticalRank B (boundedExponentLimit B) u.1,
      loweringExponentCode u.1 u.2 N) ∈
    (Finset.range ((criticalPairs B (boundedExponentLimit B)).card + 1)).product
      ((Finset.Icc 1 (boundedExponentLimit B)).powerset)
  have hfirst : criticalRank B (boundedExponentLimit B) u.1 ∈
      Finset.range ((criticalPairs B (boundedExponentLimit B)).card + 1) := by
    rw [Finset.mem_range]
    exact Nat.lt_succ_of_le (criticalRank_le_card B (boundedExponentLimit B) u.1)
  have hsecond : loweringExponentCode u.1 u.2 N ∈
      (Finset.Icc 1 (boundedExponentLimit B)).powerset := by
    rw [Finset.mem_powerset]
    intro k hkCode
    rw [loweringExponentCode, Finset.mem_image] at hkCode
    obtain ⟨p, hpLower, rfl⟩ := hkCode
    rw [Finset.mem_Icc]
    have hpTie := loweringCode_subset_tiedPrimes u.2 hu.2 hpLower
    rw [tiedPrimes, Finset.mem_filter] at hpTie
    have hp := canonicalFactorization_prime_support u.1 u.2 p hpTie.1
    have hkpos : 0 < canonicalExponent u.1 p := by
      have hne := Finsupp.mem_support_iff.mp hpTie.1
      rw [canonicalFactorization_apply, if_pos hp] at hne
      omega
    exact ⟨hkpos,
      (canonicalExponent_anti_prime u.2 (by omega) hp.two_le).trans ha2⟩
  exact (@Finset.mem_product ℕ (Finset ℕ)
    (Finset.range ((criticalPairs B (boundedExponentLimit B)).card + 1))
    ((Finset.Icc 1 (boundedExponentLimit B)).powerset)
    (criticalRank B (boundedExponentLimit B) u.1,
      loweringExponentCode u.1 u.2 N)).2 ⟨hfirst, hsecond⟩

theorem boundedSuperiorCode_injOn (B : ℕ) :
    Set.InjOn (boundedSuperiorCode B) {N : ℕ | BoundedSuperior B N} := by
  intro A hA B' hB' hcode
  let u := boundedSuperiorParameter B A
  let v := boundedSuperiorParameter B B'
  have hu := boundedSuperiorParameter_spec hA
  have hv := boundedSuperiorParameter_spec hB'
  have hcode' :
      (criticalRank B (boundedExponentLimit B) u.1,
          loweringExponentCode u.1 u.2 A) =
        (criticalRank B (boundedExponentLimit B) v.1,
          loweringExponentCode v.1 v.2 B') := by
    simpa [boundedSuperiorCode, u, v] using hcode
  have hrank : criticalRank B (boundedExponentLimit B) u.1 =
      criticalRank B (boundedExponentLimit B) v.1 :=
    congrArg Prod.fst hcode'
  have hlowering : loweringExponentCode u.1 u.2 A =
      loweringExponentCode v.1 v.2 B' :=
    congrArg Prod.snd hcode'
  have ha2u : canonicalExponent u.1 2 ≤ boundedExponentLimit B :=
    canonicalExponent_two_le_log_threshold_bound_cube u.2 hu.1
  have ha2v : canonicalExponent v.1 2 ≤ boundedExponentLimit B :=
    canonicalExponent_two_le_log_threshold_bound_cube v.2 hv.1
  have hKu : ∀ p : ℕ, p.Prime →
      canonicalExponent u.1 p ≤ boundedExponentLimit B := by
    intro p hp
    exact (canonicalExponent_anti_prime u.2 (by omega) hp.two_le).trans ha2u
  have hKv : ∀ p : ℕ, p.Prime →
      canonicalExponent v.1 p ≤ boundedExponentLimit B := by
    intro p hp
    exact (canonicalExponent_anti_prime v.2 (by omega) hp.two_le).trans ha2v
  have hcanonical : canonicalFactorization u.1 u.2 =
      canonicalFactorization v.1 v.2 :=
    canonicalFactorization_eq_of_criticalRank_eq u.2 v.2 hu.1 hv.1
      hKu hKv hrank
  by_cases hempty : loweringExponentCode u.1 u.2 A = ∅
  · have hempty' : loweringExponentCode v.1 v.2 B' = ∅ := by
      rw [← hlowering]
      exact hempty
    have hAeq := hu.2.eq_canonicalSuperior_of_loweringExponentCode_eq_empty
      u.2 hempty
    have hBeq := hv.2.eq_canonicalSuperior_of_loweringExponentCode_eq_empty
      v.2 hempty'
    rw [hAeq, hBeq]
    apply Nat.eq_of_factorization_eq
      (canonicalSuperior_isSuperior u.1 u.2).1.ne'
      (canonicalSuperior_isSuperior v.1 v.2).1.ne'
    intro p
    simpa only [factorization_canonicalSuperior] using
      congrArg (fun f : ℕ →₀ ℕ ↦ f p) hcanonical
  · obtain ⟨k, hkA⟩ := Finset.nonempty_iff_ne_empty.mpr hempty
    have hkB : k ∈ loweringExponentCode v.1 v.2 B' := by
      rw [← hlowering]
      exact hkA
    rw [loweringExponentCode, Finset.mem_image] at hkA hkB
    obtain ⟨p, hpLower, hpk⟩ := hkA
    obtain ⟨q, hqLower, hqk⟩ := hkB
    have hpTie := loweringCode_subset_tiedPrimes u.2 hu.2 hpLower
    have hqTie := loweringCode_subset_tiedPrimes v.2 hv.2 hqLower
    rw [tiedPrimes, Finset.mem_filter] at hpTie hqTie
    have hp := canonicalFactorization_prime_support u.1 u.2 p hpTie.1
    have hq := canonicalFactorization_prime_support v.1 v.2 q hqTie.1
    have hkp : 1 ≤ k := by
      have hne := Finsupp.mem_support_iff.mp hpTie.1
      rw [canonicalFactorization_apply, if_pos hp] at hne
      rw [← hpk]
      omega
    have hkq : 1 ≤ k := by
      have hne := Finsupp.mem_support_iff.mp hqTie.1
      rw [canonicalFactorization_apply, if_pos hq] at hne
      rw [← hqk]
      omega
    have hpB : p ≤ B := by
      have hpScale : (p : ℝ) ≤ thresholdScale u.1 1 :=
        (canonicalExponent_pos_iff_le_thresholdScale_one u.2 hp).1 (by
          rw [hpk]
          omega)
      exact_mod_cast hpScale.trans hu.1
    have hqB : q ≤ B := by
      have hqScale : (q : ℝ) ≤ thresholdScale v.1 1 :=
        (canonicalExponent_pos_iff_le_thresholdScale_one v.2 hq).1 (by
          rw [hqk]
          omega)
      exact_mod_cast hqScale.trans hv.1
    have hkLimit : k ≤ boundedExponentLimit B := by
      rw [← hpk]
      exact hKu p hp
    have huCritical : u.1 = criticalParameter p k := by
      have h := parameter_eq_criticalParameter_of_mem_loweringCode u.2 hu.2 hpLower
      rwa [hpk] at h
    have hvCritical : v.1 = criticalParameter q k := by
      have h := parameter_eq_criticalParameter_of_mem_loweringCode v.2 hv.2 hqLower
      rwa [hqk] at h
    have huv : u.1 = v.1 := by
      apply le_antisymm
      · by_contra hnot
        have hvu : v.1 < u.1 := lt_of_not_ge hnot
        have hrlt := criticalRank_lt_of_crossing hqB hq hkq hkLimit
          hvCritical.le (hvCritical ▸ hvu)
        omega
      · by_contra hnot
        have huv' : u.1 < v.1 := lt_of_not_ge hnot
        have hrlt := criticalRank_lt_of_crossing hpB hp hkp hkLimit
          huCritical.le (huCritical ▸ huv')
        omega
    have huvSubtype : u = v := Subtype.ext huv
    have hvSuperior : Superior u.1 B' := by
      rw [huv]
      exact hv.2
    have hlowering' : loweringExponentCode u.1 u.2 A =
        loweringExponentCode u.1 u.2 B' := by
      simpa only [huvSubtype] using hlowering
    exact loweringExponentCode_injOn_superior u.1 u.2 hu.2
      hvSuperior hlowering'

def boundedSuperiorSet (B : ℕ) : Set ℕ := {N : ℕ | BoundedSuperior B N}

theorem boundedSuperiorSet_finite (B : ℕ) :
    (boundedSuperiorSet B).Finite := by
  exact Set.Finite.of_injOn
    (fun N hN ↦ boundedSuperiorCode_mem hN)
    (boundedSuperiorCode_injOn B)
    (boundedSuperiorCodes B).finite_toSet

theorem ncard_boundedSuperiorSet_le_codes (B : ℕ) :
    (boundedSuperiorSet B).ncard ≤ (boundedSuperiorCodes B).card := by
  have htarget :
      ((↑(boundedSuperiorCodes B) : Set (ℕ × Finset ℕ))).Finite :=
    (boundedSuperiorCodes B).finite_toSet
  have hle := Set.ncard_le_ncard_of_injOn (boundedSuperiorCode B)
    (s := boundedSuperiorSet B)
    (t := (↑(boundedSuperiorCodes B) : Set (ℕ × Finset ℕ)))
    (fun N hN ↦ boundedSuperiorCode_mem hN)
    (boundedSuperiorCode_injOn B) htarget
  simpa using hle

theorem card_boundedSuperiorCodes (B : ℕ) :
    (boundedSuperiorCodes B).card =
      ((criticalPairs B (boundedExponentLimit B)).card + 1) *
        2 ^ boundedExponentLimit B := by
  simp [boundedSuperiorCodes]

/-- Polynomial enumeration of the full superior sequence, including every
simultaneously tied maximizer.  This is the finite form needed for the final
summation over superior intervals. -/
theorem ncard_boundedSuperiorSet_polynomial (B : ℕ) :
    (boundedSuperiorSet B).ncard ≤ (B + 1) ^ 8 := by
  by_cases hB : B ≤ 1
  · have hempty : boundedSuperiorSet B = ∅ := by
      ext N
      constructor
      · rintro ⟨ε, hε, hscale, hN⟩
        have hone := one_lt_thresholdScale_one hε
        have : (B : ℝ) ≤ 1 := by exact_mod_cast hB
        exact (not_lt_of_ge (hscale.trans this)) hone
      · intro h
        exact False.elim (Set.notMem_empty N h)
    simp [hempty]
  · have hBtwo : 2 ≤ B := by omega
    have hBne : B ^ 3 ≠ 0 := pow_ne_zero 3 (by omega)
    have hpi : Nat.primeCounting B ≤ B + 1 := by
      rw [← Nat.primesLE_card_eq_primeCounting]
      have hsubset : Nat.primesLE B ⊆ Finset.range (B + 1) := by
        intro p hp
        exact Finset.mem_range.mpr
          (Nat.lt_succ_of_le (Nat.le_of_mem_primesLE hp))
      exact (Finset.card_le_card hsubset).trans_eq (Finset.card_range (B + 1))
    have hlimit : boundedExponentLimit B ≤ B ^ 3 := by
      exact Nat.log_le_self 2 (B ^ 3)
    have hpairs : (criticalPairs B (boundedExponentLimit B)).card ≤
        (B + 1) * B ^ 3 := by
      rw [card_criticalPairs]
      exact Nat.mul_le_mul hpi hlimit
    have hpowers : 2 ^ boundedExponentLimit B ≤ B ^ 3 := by
      exact Nat.pow_log_le_self 2 hBne
    calc
      (boundedSuperiorSet B).ncard ≤ (boundedSuperiorCodes B).card :=
        ncard_boundedSuperiorSet_le_codes B
      _ = ((criticalPairs B (boundedExponentLimit B)).card + 1) *
          2 ^ boundedExponentLimit B := card_boundedSuperiorCodes B
      _ ≤ (((B + 1) * B ^ 3) + 1) * B ^ 3 :=
        Nat.mul_le_mul (Nat.add_le_add_right hpairs 1) hpowers
      _ ≤ (B + 1) ^ 8 := by nlinarith [show 2 ≤ B + 1 by omega]

/-! ### Global enumeration by the size of the superior integer -/

/-- An integer which is superior for at least one positive parameter. -/
def SuperiorNumber (N : ℕ) : Prop :=
  ∃ ε : ℝ, 0 < ε ∧ Superior ε N

noncomputable instance superiorNumberDecidable (N : ℕ) :
    Decidable (SuperiorNumber N) := Classical.dec _

/-- The full superior sequence is unbounded.  This uses only the elementary
primorial contained in a canonical superior integer and the divergence of the
first threshold as the parameter tends to zero. -/
theorem exists_superiorNumber_gt (A : ℕ) :
    ∃ N : ℕ, A < N ∧ SuperiorNumber N := by
  have hlarge : ∀ᶠ ε : ℝ in 𝓝[>] 0,
      (A + 1 : ℝ) < thresholdScale ε 1 :=
    tendsto_thresholdScale_one_nhdsGT_zero.eventually
      (eventually_gt_atTop (A + 1 : ℝ))
  have hpositive : ∀ᶠ ε : ℝ in 𝓝[>] 0, 0 < ε :=
    self_mem_nhdsWithin
  obtain ⟨ε, hx, hε⟩ := (hlarge.and hpositive).exists
  let N := canonicalSuperior ε hε
  have hfloor : A + 1 ≤ ⌊thresholdScale ε 1⌋₊ := by
    rw [Nat.le_floor_iff' (Nat.add_one_ne_zero A)]
    norm_num only [Nat.cast_add, Nat.cast_one]
    exact hx.le
  have hfloorPrimorial :
      ⌊thresholdScale ε 1⌋₊ ≤ primorial ⌊thresholdScale ε 1⌋₊ :=
    le_primorial_self
  have hprimorialN : primorial ⌊thresholdScale ε 1⌋₊ ≤ N := by
    exact Nat.le_of_dvd (canonicalSuperior_isSuperior ε hε).1
      (primorial_floor_thresholdScale_dvd_canonicalSuperior hε)
  refine ⟨N, ?_, ε, hε, canonicalSuperior_isSuperior ε hε⟩
  exact Nat.lt_of_lt_of_le (Nat.lt_succ_self A)
    (hfloor.trans (hfloorPrimorial.trans hprimorialN))

/-- The last superior integer not exceeding `A`.  For `A ≥ 1` the defining
set is nonempty because it contains `1`. -/
noncomputable def previousSuperior (A : ℕ) : ℕ :=
  Nat.findGreatest SuperiorNumber A

theorem previousSuperior_le (A : ℕ) : previousSuperior A ≤ A :=
  Nat.findGreatest_le A

theorem previousSuperior_isSuperior {A : ℕ} (hA : 1 ≤ A) :
    SuperiorNumber (previousSuperior A) := by
  apply Nat.findGreatest_spec (m := 1) hA
  exact ⟨2, by norm_num, superior_one⟩

theorem le_previousSuperior {A N : ℕ} (hNA : N ≤ A)
    (hN : SuperiorNumber N) : N ≤ previousSuperior A :=
  Nat.le_findGreatest hNA hN

/-- The first superior integer strictly larger than `A`. -/
noncomputable def nextSuperior (A : ℕ) : ℕ :=
  Nat.find (exists_superiorNumber_gt A)

theorem lt_nextSuperior (A : ℕ) : A < nextSuperior A :=
  (Nat.find_spec (exists_superiorNumber_gt A)).1

theorem nextSuperior_isSuperior (A : ℕ) : SuperiorNumber (nextSuperior A) :=
  (Nat.find_spec (exists_superiorNumber_gt A)).2

theorem nextSuperior_le {A N : ℕ} (hAN : A < N)
    (hN : SuperiorNumber N) : nextSuperior A ≤ N :=
  Nat.find_min' (exists_superiorNumber_gt A) ⟨hAN, hN⟩

/-- Every positive integer lies before the successor of its last superior
anchor.  This is the exact interval assignment used in Nicolas's summation. -/
theorem lt_nextSuperior_previousSuperior (A : ℕ) :
    A < nextSuperior (previousSuperior A) := by
  by_contra hnot
  have hnextA : nextSuperior (previousSuperior A) ≤ A :=
    Nat.le_of_not_gt hnot
  have hnextPrev : nextSuperior (previousSuperior A) ≤ previousSuperior A :=
    le_previousSuperior hnextA
      (nextSuperior_isSuperior (previousSuperior A))
  exact (not_lt_of_ge hnextPrev)
    (lt_nextSuperior (previousSuperior A))

/-- There is no superior integer strictly between an anchor and its
successor. -/
theorem no_superior_between_next {A N : ℕ}
    (hAN : A < N) (hN : N < nextSuperior A) : ¬SuperiorNumber N := by
  intro hSuperior
  have := nextSuperior_le hAN hSuperior
  omega

/-- The full superior sequence cut off by the ordinary size of its terms. -/
def superiorNumbersUpTo (X : ℕ) : Set ℕ :=
  {N : ℕ | N ≤ X ∧ SuperiorNumber N}

theorem superiorNumbersUpTo_finite (X : ℕ) :
    (superiorNumbersUpTo X).Finite := by
  apply (Set.finite_Iic X).subset
  intro N hN
  exact hN.1

/-- Finset form of the superior sequence up to `X`. -/
noncomputable def superiorFinsetUpTo (X : ℕ) : Finset ℕ :=
  (Finset.range (X + 1)).filter SuperiorNumber

theorem mem_superiorFinsetUpTo_iff {X N : ℕ} :
    N ∈ superiorFinsetUpTo X ↔ N ≤ X ∧ SuperiorNumber N := by
  simp [superiorFinsetUpTo]

theorem card_superiorFinsetUpTo (X : ℕ) :
    (superiorFinsetUpTo X).card = (superiorNumbersUpTo X).ncard := by
  have heq : (↑(superiorFinsetUpTo X) : Set ℕ) =
      superiorNumbersUpTo X := by
    ext N
    simp [mem_superiorFinsetUpTo_iff, superiorNumbersUpTo]
  rw [← Set.ncard_coe_finset, heq]

/-- Highly composite integers in the half-open interval from one superior
anchor to its successor. -/
noncomputable def highlyCompositeSuperiorInterval (N : ℕ) : Finset ℕ :=
  (Finset.Ico N (nextSuperior N)).filter HighlyComposite

theorem mem_highlyCompositeSuperiorInterval_iff {N A : ℕ} :
    A ∈ highlyCompositeSuperiorInterval N ↔
      N ≤ A ∧ A < nextSuperior N ∧ HighlyComposite A := by
  simp [highlyCompositeSuperiorInterval, and_assoc]

/-- Exact product bound for one superior interval.  Each positive coordinate
is a rank window whose radius is the number of primes in the corresponding
threshold zone; coordinate zero records the exponent at `2`. -/
theorem highlyCompositeSuperiorInterval_card_le_rankProduct
    {ε B : ℝ} {N L : ℕ} (hε : 0 < ε) (hN : Superior ε N)
    (hBenefit : ∀ A ∈ highlyCompositeSuperiorInterval N,
      benefit ε N A ≤ B)
    (hWithin : ∀ A ∈ highlyCompositeSuperiorInterval N,
      ∀ p : ℕ, p.Prime →
        A.factorization p ≤ N.factorization p + 1 ∧
          N.factorization p ≤ A.factorization p + 1)
    (hExponent : ∀ A ∈ highlyCompositeSuperiorInterval N,
      A.factorization 2 ≤ L) :
    (highlyCompositeSuperiorInterval N).card ≤
      ∏ i : Fin (L + 1),
        (exponentRankAllowed N L
          (fun k ↦ (thresholdZone ε B k).card) i).card := by
  apply card_le_prod_exponentRankAllowed
  · intro A hA
    exact (mem_highlyCompositeSuperiorInterval_iff.1 hA).2.2
  · exact hExponent
  · intro A hA k hk hkL
    have hAHC := (mem_highlyCompositeSuperiorInterval_iff.1 hA).2.2
    have hsubset : levelChangePrimes N A k ⊆ thresholdZone ε B k :=
      levelChangePrimes_subset_thresholdZone hε hN hAHC.1 hk
        (hBenefit A hA) (hWithin A hA)
    obtain ⟨hAN, hNA⟩ :=
      exponentLevelRank_pair_bounds_of_change_subset hsubset
    exact mem_exponentLevelRankWindow_of_pair_bounds hAN hNA

theorem highlyCompositeSuperiorInterval_card_le_zoneProduct
    {ε B : ℝ} {N L : ℕ} (hε : 0 < ε) (hN : Superior ε N)
    (hBenefit : ∀ A ∈ highlyCompositeSuperiorInterval N,
      benefit ε N A ≤ B)
    (hWithin : ∀ A ∈ highlyCompositeSuperiorInterval N,
      ∀ p : ℕ, p.Prime →
        A.factorization p ≤ N.factorization p + 1 ∧
          N.factorization p ≤ A.factorization p + 1)
    (hExponent : ∀ A ∈ highlyCompositeSuperiorInterval N,
      A.factorization 2 ≤ L) :
    (highlyCompositeSuperiorInterval N).card ≤
      (L + 1) * ∏ i : Fin L,
        (2 * (thresholdZone ε B (i.1 + 1)).card + 1) := by
  exact (highlyCompositeSuperiorInterval_card_le_rankProduct
    hε hN hBenefit hWithin hExponent).trans
      (prod_exponentRankAllowed_le N L
        (fun k ↦ (thresholdZone ε B k).card))

/-- The literal count `Q X` is bounded by the sum of the local counts over
all superior anchors at most `X`. -/
theorem Q_le_sum_highlyCompositeSuperiorInterval (X : ℕ) :
    Q X ≤ ∑ N ∈ superiorFinsetUpTo X,
      (highlyCompositeSuperiorInterval N).card := by
  rw [Q]
  calc
    ((Finset.Icc 1 X).filter HighlyComposite).card ≤
        ((superiorFinsetUpTo X).biUnion
          highlyCompositeSuperiorInterval).card := by
      apply Finset.card_le_card
      intro A hA
      rw [Finset.mem_filter, Finset.mem_Icc] at hA
      rw [Finset.mem_biUnion]
      let N := previousSuperior A
      have hNSuperior : SuperiorNumber N :=
        previousSuperior_isSuperior hA.1.1
      have hNmem : N ∈ superiorFinsetUpTo X := by
        rw [mem_superiorFinsetUpTo_iff]
        exact ⟨(previousSuperior_le A).trans hA.1.2, hNSuperior⟩
      refine ⟨N, hNmem, ?_⟩
      rw [mem_highlyCompositeSuperiorInterval_iff]
      exact ⟨previousSuperior_le A,
        lt_nextSuperior_previousSuperior A, hA.2⟩
    _ ≤ ∑ N ∈ superiorFinsetUpTo X,
        (highlyCompositeSuperiorInterval N).card :=
      Finset.card_biUnion_le

/-- A uniform bound for every local superior interval immediately gives the
corresponding product bound for `Q`. -/
theorem Q_le_card_superiorFinset_mul_of_local_bound {X K : ℕ}
    (hlocal : ∀ N ∈ superiorFinsetUpTo X,
      (highlyCompositeSuperiorInterval N).card ≤ K) :
    Q X ≤ (superiorFinsetUpTo X).card * K := by
  calc
    Q X ≤ ∑ N ∈ superiorFinsetUpTo X,
        (highlyCompositeSuperiorInterval N).card :=
      Q_le_sum_highlyCompositeSuperiorInterval X
    _ ≤ ∑ _N ∈ superiorFinsetUpTo X, K := by
      apply Finset.sum_le_sum
      intro N hN
      exact hlocal N hN
    _ = (superiorFinsetUpTo X).card * K := by simp

/-- Maximum local highly-composite count among superior anchors up to `X`. -/
noncomputable def maxSuperiorIntervalCount (X : ℕ) : ℕ :=
  (superiorFinsetUpTo X).sup
    (fun N ↦ (highlyCompositeSuperiorInterval N).card)

/-- Uniform finite bound for intervals whose superior anchor has first
threshold at most `R`. -/
noncomputable def boundedSuperiorIntervalMax (R : ℕ) : ℕ :=
  (boundedSuperiorSet_finite R).toFinset.sup
    (fun N ↦ (highlyCompositeSuperiorInterval N).card)

theorem highlyCompositeSuperiorInterval_card_le_boundedMax
    {R N : ℕ} (hN : BoundedSuperior R N) :
    (highlyCompositeSuperiorInterval N).card ≤
      boundedSuperiorIntervalMax R := by
  rw [boundedSuperiorIntervalMax]
  exact Finset.le_sup
    (s := (boundedSuperiorSet_finite R).toFinset)
    (f := fun N ↦ (highlyCompositeSuperiorInterval N).card)
    (by simpa [boundedSuperiorSet] using hN)

theorem highlyCompositeSuperiorInterval_card_le_max {X N : ℕ}
    (hN : N ∈ superiorFinsetUpTo X) :
    (highlyCompositeSuperiorInterval N).card ≤
      maxSuperiorIntervalCount X := by
  exact Finset.le_sup
    (s := superiorFinsetUpTo X)
    (f := fun N ↦ (highlyCompositeSuperiorInterval N).card) hN

theorem Q_le_superior_card_mul_maxSuperiorIntervalCount (X : ℕ) :
    Q X ≤ (superiorFinsetUpTo X).card * maxSuperiorIntervalCount X := by
  apply Q_le_card_superiorFinset_mul_of_local_bound
  intro N hN
  exact highlyCompositeSuperiorInterval_card_le_max hN

/-- Nicolas's quantitative local input, stated independently of the later
finite encoding.  It says that every highly composite integer assigned to a
large superior anchor has benefit bounded by one fixed negative power of the
anchor's first threshold. -/
def NicolasPowerBenefitBound : Prop :=
  ∃ C γ X₀ : ℝ, 0 ≤ C ∧ 0 < γ ∧
    ∀ ε : ℝ, ∀ N A : ℕ,
      0 < ε → Superior ε N →
      X₀ ≤ thresholdScale ε 1 →
      N ≤ A → A < nextSuperior N → HighlyComposite A →
      benefit ε N A ≤ C * (thresholdScale ε 1) ^ (-γ)

/-- A power-saving benefit estimate uniformly yields the squarefree-change
conclusion after one threshold cutoff.  This packages the asymptotic
comparison and the primewise convexity theorem into the form needed by the
finite local certificate. -/
theorem eventual_factorization_within_one_of_nicolasPowerBenefitBound
    (hpower : NicolasPowerBenefitBound) :
    ∃ X₀ : ℝ, ∀ ε : ℝ, ∀ N A : ℕ,
      0 < ε → Superior ε N →
      X₀ ≤ thresholdScale ε 1 →
      N ≤ A → A < nextSuperior N → HighlyComposite A →
      ∀ p : ℕ, p.Prime →
        A.factorization p ≤ N.factorization p + 1 ∧
          N.factorization p ≤ A.factorization p + 1 := by
  obtain ⟨C, γ, XB, hC, hγ, hbenefit⟩ := hpower
  obtain ⟨XL, hloss⟩ := Filter.eventually_atTop.1
    (eventually_const_mul_rpow_neg_lt_inv_log_sq C γ hC hγ)
  refine ⟨max XB XL, ?_⟩
  intro ε N A hε hN hx hNA hANext hA p hp
  apply factorization_within_one_of_power_benefit_bound hε hN hA.1 hp
  · exact hbenefit ε N A hε hN
      ((le_max_left XB XL).trans hx) hNA hANext hA
  · exact hloss _ ((le_max_right XB XL).trans hx)

/-- The power-saving benefit estimate implies a completely explicit
polynomial bound for every sufficiently large superior interval.  The fixed
low levels cost `(9R)^k₀`; every remaining level has at most three choices,
and their total cost is absorbed by `R^13`. -/
theorem eventually_highlyCompositeSuperiorInterval_card_le_power
    (hpower : NicolasPowerBenefitBound) :
    ∃ k₀ : ℕ, ∃ X₀ : ℝ, ∀ ε : ℝ, ∀ N : ℕ,
      0 < ε → Superior ε N → X₀ ≤ thresholdScale ε 1 →
      (highlyCompositeSuperiorInterval N).card ≤
        9 ^ k₀ * ⌈thresholdScale ε 1⌉₊ ^ (k₀ + 16) := by
  obtain ⟨XL, hwithin⟩ :=
    eventual_factorization_within_one_of_nicolasPowerBenefitBound hpower
  obtain ⟨C, γ, XB, hC, hγ, hbenefit⟩ := hpower
  obtain ⟨k₀, XZ, hzone⟩ :=
    eventually_thresholdZone_card_le_one_of_power C γ hC hγ
  obtain ⟨XW, hwidth⟩ := Filter.eventually_atTop.1
    (eventually_powerBenefit_zone_width_lt_one C γ 0 hC hγ hγ)
  refine ⟨k₀, max XB (max XL (max XZ XW)), ?_⟩
  intro ε N hε hN hx
  let x := thresholdScale ε 1
  let R : ℕ := ⌈x⌉₊
  let L := localExponentLimit ε
  let B := C * x ^ (-γ)
  change max XB (max XL (max XZ XW)) ≤ x at hx
  have hxXB : XB ≤ x := by
    exact (le_max_left XB _).trans hx
  have hxXL : XL ≤ x := by
    exact (le_max_left XL _).trans ((le_max_right XB _).trans hx)
  have hxXZ : XZ ≤ x := by
    exact (le_max_left XZ XW).trans ((le_max_right XL _).trans
      ((le_max_right XB _).trans hx))
  have hxXW : XW ≤ x := by
    exact (le_max_right XZ XW).trans ((le_max_right XL _).trans
      ((le_max_right XB _).trans hx))
  have hx1 : 1 < x := by simpa [x] using one_lt_thresholdScale_one hε
  have hxR : x ≤ (R : ℝ) := by
    dsimp [R]
    exact Nat.le_ceil x
  have hRtwo : 2 ≤ R := by
    have : (1 : ℝ) < R := hx1.trans_le hxR
    exact_mod_cast this
  have hwidthData := hwidth x hxXW
  have htEq : B / ε =
      C * x ^ (-γ) * Real.log x / Real.log 2 := by
    dsimp [B]
    rw [show Real.log x = (1 / ε) * Real.log 2 by
      simpa [x] using log_thresholdScale_one hε]
    field_simp
  have ht1 : B / ε ≤ 1 := by
    rw [htEq]
    exact hwidthData.2.1
  have hBenefit : ∀ A ∈ highlyCompositeSuperiorInterval N,
      benefit ε N A ≤ B := by
    intro A hA
    obtain ⟨hNA, hANext, hAHC⟩ :=
      mem_highlyCompositeSuperiorInterval_iff.1 hA
    simpa [B, x] using hbenefit ε N A hε hN hxXB hNA hANext hAHC
  have hWithin : ∀ A ∈ highlyCompositeSuperiorInterval N,
      ∀ p : ℕ, p.Prime →
        A.factorization p ≤ N.factorization p + 1 ∧
          N.factorization p ≤ A.factorization p + 1 := by
    intro A hA p hp
    obtain ⟨hNA, hANext, hAHC⟩ :=
      mem_highlyCompositeSuperiorInterval_iff.1 hA
    exact hwithin ε N A hε hN hxXL hNA hANext hAHC p hp
  have hExponent : ∀ A ∈ highlyCompositeSuperiorInterval N,
      A.factorization 2 ≤ L := by
    intro A hA
    exact factorization_two_le_localExponentLimit hε hN
      ((hWithin A hA 2 Nat.prime_two).1)
  have hProduct :
      (∏ i : Fin L, (2 * (thresholdZone ε B (i.1 + 1)).card + 1)) ≤
        (6 * R + 3) ^ k₀ * 3 ^ L := by
    apply prod_thresholdZone_factor_le
    · intro i hi
      simpa [R, x] using
        thresholdZone_card_le_three_mul_ceil hε (by omega : 0 < i.1 + 1) ht1
    · intro i hi
      simpa [B, x] using hzone ε (i.1 + 1) hε hxXZ (by omega)
  have hInterval := highlyCompositeSuperiorInterval_card_le_zoneProduct
    hε hN hBenefit hWithin hExponent
  have hCoordinate : L + 1 ≤ R ^ 3 := by
    simpa [L, R, x] using localExponentLimit_add_one_le_ceil_cube hε
  have hTernary : 3 ^ L ≤ R ^ 13 := by
    simpa [L, R, x] using three_pow_localExponentLimit_le_ceil_pow hε
  have hLowBase : 6 * R + 3 ≤ 9 * R := by omega
  have hLowPower : (6 * R + 3) ^ k₀ ≤ (9 * R) ^ k₀ := by
    gcongr
  calc
    (highlyCompositeSuperiorInterval N).card ≤
        (L + 1) * ∏ i : Fin L,
          (2 * (thresholdZone ε B (i.1 + 1)).card + 1) := hInterval
    _ ≤ (L + 1) * ((6 * R + 3) ^ k₀ * 3 ^ L) := by gcongr
    _ ≤ R ^ 3 * ((9 * R) ^ k₀ * R ^ 13) := by gcongr
    _ = 9 ^ k₀ * R ^ (k₀ + 16) := by
      rw [mul_pow]
      simp only [pow_add]
      ring
    _ = 9 ^ k₀ * ⌈thresholdScale ε 1⌉₊ ^ (k₀ + 16) := by
      rfl

/-- Nicolas's local theorem, isolated in the exact asymptotic form needed by
the already-formalized global summation. -/
def NicolasLocalPolynomialBound : Prop :=
  ∃ c : ℕ, (fun X : ℕ ↦ (maxSuperiorIntervalCount X : ℝ)) =O[atTop]
    (fun X : ℕ ↦ logPower c X)

/-- The quantitative benefit estimate implies Nicolas's local polynomial
bound.  Small first thresholds form a finite family; large ones are covered
by the rank-zone estimate above and the uniform logarithmic bound for the
first threshold of a superior number. -/
theorem nicolasLocalPolynomialBound_of_powerBenefitBound
    (hpower : NicolasPowerBenefitBound) : NicolasLocalPolynomialBound := by
  obtain ⟨k₀, X₀, hlarge⟩ :=
    eventually_highlyCompositeSuperiorInterval_card_le_power hpower
  obtain ⟨C, B, hC, hB, hscale⟩ :=
    thresholdScale_le_const_add_const_mul_log_superior
  let R₀ : ℕ := ⌈max X₀ 0⌉₊
  let D : ℕ := boundedSuperiorIntervalMax R₀
  let E : ℝ := B + C + 2
  let e : ℕ := k₀ + 16
  have hE : 0 < E := by dsimp [E]; linarith
  refine ⟨e, ?_⟩
  rw [isBigO_iff]
  refine ⟨(D : ℝ) + (9 ^ k₀ : ℕ) * (E + 1) ^ e, ?_⟩
  filter_upwards [(Real.tendsto_log_atTop.comp
      tendsto_natCast_atTop_atTop).eventually
      (eventually_ge_atTop (1 : ℝ))] with X hlogX
  change 1 ≤ Real.log X at hlogX
  have hX : 1 ≤ X := by
    by_contra hnot
    have hXzero : X = 0 := by omega
    subst X
    norm_num at hlogX
  have hXreal : (0 : ℝ) < X := by exact_mod_cast (show 0 < X by omega)
  let T : ℕ := ⌈E * Real.log X⌉₊
  have hElogNonneg : 0 ≤ E * Real.log X := by positivity
  have hTlt : (T : ℝ) < E * Real.log X + 1 := by
    dsimp [T]
    exact Nat.ceil_lt_add_one hElogNonneg
  have hTbound : (T : ℝ) ≤ (E + 1) * Real.log X := by
    have hlogNonneg : 0 ≤ Real.log X := by linarith
    linarith
  have hsupNat : maxSuperiorIntervalCount X ≤
      D + 9 ^ k₀ * T ^ e := by
    rw [maxSuperiorIntervalCount]
    apply Finset.sup_le
    intro N hNmem
    obtain ⟨hNX, ε, hε, hN⟩ :=
      (mem_superiorFinsetUpTo_iff.1 hNmem)
    have hNreal : (0 : ℝ) < N := by exact_mod_cast hN.1
    have hlogNX : Real.log N ≤ Real.log X :=
      Real.strictMonoOn_log.monotoneOn hNreal hXreal
        (by exact_mod_cast hNX)
    have hscaleX : thresholdScale ε 1 ≤ E * Real.log X := by
      have hbase := hscale ε hε N hN
      have hlogNonneg : 0 ≤ Real.log X := by linarith
      have hBterm : 0 ≤ B * (Real.log X - 1) := by positivity
      calc
        thresholdScale ε 1 ≤ B + C * Real.log N := hbase
        _ ≤ B + C * Real.log X := by gcongr
        _ ≤ E * Real.log X := by
          dsimp [E]
          nlinarith
    by_cases hx : X₀ ≤ thresholdScale ε 1
    · have hmain := hlarge ε N hε hN hx
      have hceil : ⌈thresholdScale ε 1⌉₊ ≤ T := by
        dsimp [T]
        exact Nat.ceil_mono hscaleX
      calc
        (highlyCompositeSuperiorInterval N).card ≤
            9 ^ k₀ * ⌈thresholdScale ε 1⌉₊ ^ e := by
          simpa [e] using hmain
        _ ≤ 9 ^ k₀ * T ^ e := by gcongr
        _ ≤ D + 9 ^ k₀ * T ^ e := Nat.le_add_left _ _
    · have hbounded : BoundedSuperior R₀ N := by
        refine ⟨ε, hε, ?_, hN⟩
        calc
          thresholdScale ε 1 ≤ X₀ := le_of_not_ge hx
          _ ≤ max X₀ 0 := le_max_left _ _
          _ ≤ (R₀ : ℝ) := by
            dsimp [R₀]
            exact Nat.le_ceil _
      exact (highlyCompositeSuperiorInterval_card_le_boundedMax hbounded).trans
        (Nat.le_add_right _ _)
  have hsupReal : (maxSuperiorIntervalCount X : ℝ) ≤
      (D : ℝ) + (9 ^ k₀ : ℕ) * (T : ℝ) ^ e := by
    exact_mod_cast hsupNat
  have hlogPowOne : (1 : ℝ) ≤ Real.log X ^ e := by
    have := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1) hlogX e
    simpa using this
  have hTPow : (T : ℝ) ^ e ≤
      ((E + 1) * Real.log X) ^ e :=
    pow_le_pow_left₀ (by positivity) hTbound e
  have hmain : (maxSuperiorIntervalCount X : ℝ) ≤
      ((D : ℝ) + (9 ^ k₀ : ℕ) * (E + 1) ^ e) *
        Real.log X ^ e := by
    calc
      (maxSuperiorIntervalCount X : ℝ) ≤
          (D : ℝ) + (9 ^ k₀ : ℕ) * (T : ℝ) ^ e := hsupReal
      _ ≤ (D : ℝ) * Real.log X ^ e +
          (9 ^ k₀ : ℕ) * ((E + 1) * Real.log X) ^ e := by
        exact add_le_add
          (by
            calc
              (D : ℝ) = (D : ℝ) * 1 := by ring
              _ ≤ (D : ℝ) * Real.log X ^ e := by gcongr)
          (mul_le_mul_of_nonneg_left hTPow (by positivity))
      _ = ((D : ℝ) + (9 ^ k₀ : ℕ) * (E + 1) ^ e) *
          Real.log X ^ e := by rw [mul_pow]; ring
  have hmaxNonneg : 0 ≤ (maxSuperiorIntervalCount X : ℝ) := by positivity
  have hlogPowNonneg : 0 ≤ Real.log X ^ e := by positivity
  have hconstNonneg :
      0 ≤ (D : ℝ) + (9 ^ k₀ : ℕ) * (E + 1) ^ e := by positivity
  simpa only [Real.norm_eq_abs, abs_of_nonneg hmaxNonneg,
    logPower, abs_of_nonneg hlogPowNonneg,
    abs_of_nonneg hconstNonneg] using hmain

/-! ## The rotation in Nicolas's trial family

The divisor ratios used in the quantitative local argument are rotations by
`log (3/2) / log 2`.  Before introducing any quantitative irrationality
measure, we record here the elementary, axiom-free nonvanishing argument and
the exact Dirichlet approximation supplied by Mathlib.  The polynomial lower
bound for these linear forms is the genuinely deeper Feldman input.
-/

/-- The rotation angle occurring when a prime exponent is raised from one to
two and another is lowered from one to zero. -/
noncomputable def nicolasTheta : ℝ := Real.log (3 / 2) / Real.log 2

theorem nicolasTheta_pos : 0 < nicolasTheta := by
  rw [nicolasTheta]
  positivity

theorem nicolasTheta_lt_one : nicolasTheta < 1 := by
  rw [nicolasTheta, div_lt_one (Real.log_pos (by norm_num : (1 : ℝ) < 2))]
  exact Real.strictMonoOn_log (by norm_num) (by norm_num) (by norm_num)

/-- Elementary multiplicative independence of `2` and `3`: no nonzero
natural multiple of `nicolasTheta` is an integer. -/
theorem nicolasTheta_linear_ne_zero (u : ℤ) (v : ℕ) (hv : 0 < v) :
    (v : ℝ) * nicolasTheta - (u : ℝ) ≠ 0 := by
  intro hzero
  have heq : (v : ℝ) * nicolasTheta = (u : ℝ) := sub_eq_zero.mp hzero
  have huR : (0 : ℝ) < (u : ℝ) := by
    rw [← heq]
    exact mul_pos (by exact_mod_cast hv) nicolasTheta_pos
  have hu : 0 < u := by exact_mod_cast huR
  let w : ℕ := u.toNat
  have huw : u = (w : ℤ) := by
    simp only [w, Int.toNat_of_nonneg hu.le]
  rw [huw] at heq
  norm_num only [Int.cast_natCast] at heq
  have hlog2 : Real.log (2 : ℝ) ≠ 0 := (Real.log_pos (by norm_num)).ne'
  have hlogs : (v : ℝ) * Real.log (3 / 2 : ℝ) =
      (w : ℝ) * Real.log 2 := by
    rw [nicolasTheta] at heq
    apply (div_eq_iff hlog2).mp
    rw [mul_div_assoc]
    simpa [mul_comm] using heq
  have hpowsR : ((3 / 2 : ℝ) ^ v) = (2 : ℝ) ^ w := by
    apply Real.strictMonoOn_log.injOn
    · exact Set.mem_Ioi.mpr (pow_pos (by norm_num) _)
    · exact Set.mem_Ioi.mpr (pow_pos (by norm_num) _)
    · simpa only [Real.log_pow] using hlogs
  have hclearR : (3 : ℝ) ^ v = (2 : ℝ) ^ (w + v) := by
    calc
      (3 : ℝ) ^ v = ((3 / 2 : ℝ) ^ v) * (2 : ℝ) ^ v := by
        rw [div_pow]
        field_simp
      _ = (2 : ℝ) ^ w * (2 : ℝ) ^ v := by rw [hpowsR]
      _ = (2 : ℝ) ^ (w + v) := by rw [pow_add]
  have hclear : 3 ^ v = 2 ^ (w + v) := by exact_mod_cast hclearR
  have hthreeDvd : 3 ∣ 3 ^ v := dvd_pow_self 3 hv.ne'
  have hthreeDvdTwo : 3 ∣ 2 ^ (w + v) := hclear ▸ hthreeDvd
  have hthreeDvdTwoBase : 3 ∣ 2 :=
    Nat.prime_three.dvd_of_dvd_pow hthreeDvdTwo
  norm_num at hthreeDvdTwoBase

/-- Dirichlet supplies a nonzero approximation to the Nicolas angle with
denominator at most `H`; nonvanishing is discharged by the preceding
multiplicative-independence lemma. -/
theorem exists_nicolasTheta_dirichlet (H : ℕ) (hH : 0 < H) :
    ∃ u : ℤ, ∃ v : ℕ, 0 < v ∧ v ≤ H ∧
      0 < |(v : ℝ) * nicolasTheta - (u : ℝ)| ∧
      |(v : ℝ) * nicolasTheta - (u : ℝ)| ≤ 1 / (H + 1) := by
  obtain ⟨v, hv, hvH, happrox⟩ :=
    Real.exists_nat_abs_mul_sub_round_le nicolasTheta hH
  refine ⟨round ((v : ℝ) * nicolasTheta), v, hv, hvH, ?_, happrox⟩
  exact abs_pos.mpr (nicolasTheta_linear_ne_zero _ v hv)

/-- The specialized polynomial irrationality measure used by Nicolas.  This is
a proposition, not an assumed declaration; the unconditional local theorem
must ultimately construct its witnesses from Feldman's theorem. -/
def NicolasFeldmanEstimate : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∃ K : ℕ, ∀ u : ℤ, ∀ v : ℕ, 0 < v →
    c / (v : ℝ) ^ K ≤ |(v : ℝ) * nicolasTheta - (u : ℝ)|

/-- Flooring `t / δ` gives the elementary mesh estimate used to turn one
small nonzero rotation step into a covering progression. -/
theorem floorMultipleCover {δ t : ℝ} (hδ : 0 < δ) (ht : 0 ≤ t) :
    let m := ⌊t / δ⌋₊
    0 ≤ t - (m : ℝ) * δ ∧
      t - (m : ℝ) * δ < δ ∧
      (m : ℝ) ≤ t / δ := by
  let m := ⌊t / δ⌋₊
  have hdiv : 0 ≤ t / δ := div_nonneg ht hδ.le
  have hmle : (m : ℝ) ≤ t / δ := Nat.floor_le hdiv
  have hmle' : (m : ℝ) * δ ≤ t := by
    rwa [le_div_iff₀ hδ] at hmle
  have hlt : t / δ < (m : ℝ) + 1 := by
    simpa [m] using Nat.lt_floor_add_one (t / δ)
  have hlt' : t < ((m : ℝ) + 1) * δ := by
    rwa [div_lt_iff₀ hδ] at hlt
  exact ⟨sub_nonneg.mpr hmle', by linarith, hmle⟩

/-- A polynomial lower bound for the linear forms, combined with Dirichlet,
gives an explicit polynomial-size signed rotation net.  This replaces the
continued-fraction max-gap subargument in Nicolas by a shorter equivalent
construction: take multiples of one Dirichlet step and reverse its sign when
necessary. -/
theorem signedRotationCover
    {θ c : ℝ} {K L : ℕ}
    (hc : 0 < c) (hL : 0 < L)
    (hlower : ∀ u : ℤ, ∀ q : ℕ, 0 < q →
      c / (q : ℝ) ^ K ≤ |(q : ℝ) * θ - (u : ℝ)|) :
    ∀ t : ℝ, 0 ≤ t → t ≤ 1 →
      ∃ h j : ℤ,
        |(h : ℝ)| ≤ (L : ℝ) ^ (K + 1) / c ∧
        |(h : ℝ) * θ - (j : ℝ) - t| ≤ 1 / (L + 1 : ℕ) := by
  intro t ht0 ht1
  obtain ⟨q, hq, hqL, hdupper⟩ :=
    Real.exists_nat_abs_mul_sub_round_le θ hL
  let u : ℤ := round ((q : ℝ) * θ)
  have hdpos : 0 < |(q : ℝ) * θ - (u : ℝ)| := by
    apply lt_of_lt_of_le
      (div_pos hc (pow_pos (show (0 : ℝ) < q by exact_mod_cast hq) K))
    exact hlower u q hq
  let d : ℝ := (q : ℝ) * θ - (u : ℝ)
  let δ : ℝ := |d|
  let m : ℕ := ⌊t / δ⌋₊
  have hδ : 0 < δ := by simpa [δ, d] using hdpos
  obtain ⟨hrem0, hremδ, hmle⟩ := floorMultipleCover hδ ht0
  change 0 ≤ t - (m : ℝ) * δ at hrem0
  change t - (m : ℝ) * δ < δ at hremδ
  change (m : ℝ) ≤ t / δ at hmle
  have hqposR : (0 : ℝ) < q := by exact_mod_cast hq
  have hqleR : (q : ℝ) ≤ L := by exact_mod_cast hqL
  have hlower' : c / (q : ℝ) ^ K ≤ δ := by
    simpa [δ, d] using hlower u q hq
  have hmδ : (m : ℝ) * δ ≤ 1 := by
    have h := mul_le_mul_of_nonneg_right hmle hδ.le
    rw [div_mul_cancel₀ _ hδ.ne'] at h
    exact h.trans ht1
  have hmq : (m : ℝ) * q ≤ (L : ℝ) ^ (K + 1) / c := by
    have hpowpos : 0 < (q : ℝ) ^ K := pow_pos hqposR K
    have hcq : c ≤ δ * (q : ℝ) ^ K := by
      rwa [div_le_iff₀ hpowpos] at hlower'
    have hmc : (m : ℝ) * c ≤ (q : ℝ) ^ K := by
      calc
        (m : ℝ) * c ≤ (m : ℝ) * (δ * (q : ℝ) ^ K) := by gcongr
        _ = ((m : ℝ) * δ) * (q : ℝ) ^ K := by ring
        _ ≤ 1 * (q : ℝ) ^ K := by gcongr
        _ = (q : ℝ) ^ K := one_mul _
    have hmqc : ((m : ℝ) * q) * c ≤ (q : ℝ) ^ (K + 1) := by
      calc
        ((m : ℝ) * q) * c = ((m : ℝ) * c) * q := by ring
        _ ≤ (q : ℝ) ^ K * q := by gcongr
        _ = (q : ℝ) ^ (K + 1) := by rw [pow_succ]
    have hpowmono : (q : ℝ) ^ (K + 1) ≤ (L : ℝ) ^ (K + 1) :=
      pow_le_pow_left₀ hqposR.le hqleR _
    rw [le_div_iff₀ hc]
    exact hmqc.trans hpowmono
  by_cases hd : 0 ≤ d
  · refine ⟨(m * q : ℕ), m * u, ?_, ?_⟩
    · norm_num only [Int.cast_natCast, Nat.cast_mul, Int.cast_mul]
      rw [abs_of_nonneg (mul_nonneg (Nat.cast_nonneg _) hqposR.le)]
      exact hmq
    · have hdabs : δ = d := by simp [δ, abs_of_nonneg hd]
      have heq : (((m * q : ℕ) : ℤ) : ℝ) * θ - (((m : ℤ) * u : ℤ) : ℝ) =
          (m : ℝ) * δ := by
        push_cast
        rw [hdabs]
        dsimp [d]
        ring
      rw [heq, abs_sub_comm, abs_of_nonneg hrem0]
      exact hremδ.le.trans (by simpa [δ, d] using hdupper)
  · have hdlt : d < 0 := lt_of_not_ge hd
    refine ⟨-((m * q : ℕ) : ℤ), -(m * u), ?_, ?_⟩
    · norm_num only [Int.cast_neg, Int.cast_natCast, abs_neg]
      rw [abs_of_nonneg]
      · simpa only [Nat.cast_mul] using hmq
      · positivity
    · have hdabs : δ = -d := by simp [δ, abs_of_neg hdlt]
      have heq : ((-((m * q : ℕ) : ℤ) : ℤ) : ℝ) * θ - ((-(m * u) : ℤ) : ℝ) =
          (m : ℝ) * δ := by
        push_cast
        rw [hdabs]
        dsimp [d]
        ring
      rw [heq, abs_sub_comm, abs_of_nonneg hrem0]
      exact hremδ.le.trans (by simpa [δ, d] using hdupper)

theorem nicolasSignedRotationCover
    (hF : NicolasFeldmanEstimate) :
    ∃ c : ℝ, 0 < c ∧ ∃ K : ℕ, ∀ L : ℕ, 0 < L →
      ∀ t : ℝ, 0 ≤ t → t ≤ 1 →
        ∃ h j : ℤ,
          |(h : ℝ)| ≤ (L : ℝ) ^ (K + 1) / c ∧
          |(h : ℝ) * nicolasTheta - (j : ℝ) - t| ≤
            1 / (L + 1 : ℕ) := by
  obtain ⟨c, hc, K, hK⟩ := hF
  exact ⟨c, hc, K, fun L hL ↦ signedRotationCover hc hL hK⟩

/-- The threshold bound for an arbitrary superior integer turns the finite
threshold enumeration into a polynomial bound for the full superior sequence
up to `X`.  The displayed natural ceiling is retained here so no asymptotic
rounding is hidden. -/
theorem exists_ncard_superiorNumbersUpTo_le_polynomial :
    ∃ C B : ℝ, 0 < C ∧ 0 < B ∧
      ∀ X : ℕ, 1 ≤ X →
        (superiorNumbersUpTo X).ncard ≤
          (⌈B + C * Real.log X⌉₊ + 1) ^ 8 := by
  obtain ⟨C, B, hC, hB, hscale⟩ :=
    thresholdScale_le_const_add_const_mul_log_superior
  refine ⟨C, B, hC, hB, ?_⟩
  intro X hX
  let R : ℕ := ⌈B + C * Real.log X⌉₊
  have hsubset : superiorNumbersUpTo X ⊆ boundedSuperiorSet R := by
    intro N hN
    obtain ⟨hNX, ε, hε, hSuperior⟩ := hN
    have hNpos : 0 < N := hSuperior.1
    have hNreal : (0 : ℝ) < N := by exact_mod_cast hNpos
    have hXreal : (0 : ℝ) < X := by exact_mod_cast hX
    have hlog : Real.log N ≤ Real.log X := by
      exact Real.strictMonoOn_log.monotoneOn
        hNreal hXreal
        (by exact_mod_cast hNX)
    have hthreshold : thresholdScale ε 1 ≤ B + C * Real.log X := by
      apply (hscale ε hε N hSuperior).trans
      gcongr
    have hceil : B + C * Real.log X ≤ (R : ℝ) := by
      dsimp [R]
      exact Nat.le_ceil _
    exact ⟨ε, hε, hthreshold.trans hceil, hSuperior⟩
  calc
    (superiorNumbersUpTo X).ncard ≤ (boundedSuperiorSet R).ncard :=
      Set.ncard_le_ncard hsubset
        (boundedSuperiorSet_finite R)
    _ ≤ (R + 1) ^ 8 := ncard_boundedSuperiorSet_polynomial R
    _ = (⌈B + C * Real.log X⌉₊ + 1) ^ 8 := by rfl

/-- In asymptotic notation, the full superior sequence has at most eighth
power logarithmic growth. -/
theorem superiorNumbersUpTo_isBigO_logPower :
    (fun X : ℕ ↦ ((superiorNumbersUpTo X).ncard : ℝ)) =O[atTop]
      (fun X : ℕ ↦ logPower 8 X) := by
  obtain ⟨C, B, hC, hB, hcount⟩ :=
    exists_ncard_superiorNumbersUpTo_le_polynomial
  let D := B + C + 2
  have hD : 0 < D := by dsimp [D]; linarith
  rw [isBigO_iff]
  refine ⟨D ^ 8, ?_⟩
  filter_upwards [(Real.tendsto_log_atTop.comp
      tendsto_natCast_atTop_atTop).eventually
      (eventually_ge_atTop (1 : ℝ))] with X hlog
  change 1 ≤ Real.log X at hlog
  have hX : 1 ≤ X := by
    by_contra hnot
    have hXzero : X = 0 := by omega
    subst X
    norm_num at hlog
  let R : ℕ := ⌈B + C * Real.log X⌉₊
  have hrnonneg : 0 ≤ B + C * Real.log X := by
    positivity
  have hRlt : (R : ℝ) < B + C * Real.log X + 1 := by
    dsimp [R]
    exact Nat.ceil_lt_add_one hrnonneg
  have hRbound : (R : ℝ) + 1 ≤ D * Real.log X := by
    dsimp [D]
    nlinarith [mul_nonneg (by linarith : 0 ≤ B + 2)
      (sub_nonneg.mpr hlog)]
  have hcount' : ((superiorNumbersUpTo X).ncard : ℝ) ≤
      ((R + 1 : ℕ) : ℝ) ^ 8 := by
    exact_mod_cast hcount X hX
  have hRnonneg : 0 ≤ (R : ℝ) + 1 := by positivity
  have hlognonneg : 0 ≤ Real.log X := hlog.trans' zero_le_one
  have hmain : ((superiorNumbersUpTo X).ncard : ℝ) ≤
      D ^ 8 * Real.log X ^ 8 := by
    calc
      ((superiorNumbersUpTo X).ncard : ℝ) ≤ ((R : ℝ) + 1) ^ 8 := by
        simpa [Nat.cast_add, Nat.cast_one] using hcount'
      _ ≤ (D * Real.log X) ^ 8 := pow_le_pow_left₀ hRnonneg hRbound 8
      _ = D ^ 8 * Real.log X ^ 8 := by rw [mul_pow]
  have hcountnonneg :
      0 ≤ ((superiorNumbersUpTo X).ncard : ℝ) := by positivity
  simpa only [Real.norm_eq_abs, abs_of_nonneg hcountnonneg,
    logPower, abs_of_nonneg (pow_nonneg hlognonneg 8),
    abs_of_nonneg (pow_nonneg hD.le 8)] using hmain

/-- Nicolas's local polynomial bound plus the verified eighth-power
enumeration of the full superior sequence gives the required global
polynomial-logarithmic upper bound. -/
theorem nicolasPolynomialUpperBound_of_local
    (hlocal : NicolasLocalPolynomialBound) :
    NicolasPolynomialUpperBound := by
  obtain ⟨c, hlocal⟩ := hlocal
  have hcard :
      (fun X : ℕ ↦ ((superiorFinsetUpTo X).card : ℝ)) =O[atTop]
        (fun X : ℕ ↦ logPower 8 X) := by
    simpa only [card_superiorFinsetUpTo] using
      superiorNumbersUpTo_isBigO_logPower
  have hQproduct :
      (fun X : ℕ ↦ (Q X : ℝ)) =O[atTop]
        (fun X : ℕ ↦
          ((superiorFinsetUpTo X).card : ℝ) *
            (maxSuperiorIntervalCount X : ℝ)) := by
    rw [isBigO_iff]
    refine ⟨1, Filter.Eventually.of_forall ?_⟩
    intro X
    have hbound := Q_le_superior_card_mul_maxSuperiorIntervalCount X
    have hbound' :
        (Q X : ℝ) ≤
          ((superiorFinsetUpTo X).card : ℝ) *
            (maxSuperiorIntervalCount X : ℝ) := by
      exact_mod_cast hbound
    have hQnonneg : 0 ≤ (Q X : ℝ) := by positivity
    have hproductNonneg :
        0 ≤ ((superiorFinsetUpTo X).card : ℝ) *
          (maxSuperiorIntervalCount X : ℝ) := by positivity
    simpa only [Real.norm_eq_abs, abs_of_nonneg hQnonneg,
      abs_of_nonneg hproductNonneg, one_mul] using hbound'
  have hproduct :
      (fun X : ℕ ↦
        ((superiorFinsetUpTo X).card : ℝ) *
          (maxSuperiorIntervalCount X : ℝ)) =O[atTop]
        (fun X : ℕ ↦ logPower 8 X * logPower c X) :=
    hcard.mul hlocal
  have hpowers :
      (fun X : ℕ ↦ logPower 8 X * logPower c X) =
        (fun X : ℕ ↦ logPower (8 + c) X) := by
    funext X
    simp [logPower, pow_add]
  rw [hpowers] at hproduct
  exact ⟨8 + c, hQproduct.trans hproduct⟩

theorem mem_counted_iff {n N : ℕ} :
    n ∈ (Finset.Icc 1 N).filter HighlyComposite ↔
      1 ≤ n ∧ n ≤ N ∧ HighlyComposite n := by
  simp [and_assoc]

theorem Q_mono : Monotone Q := by
  intro M N hMN
  apply Finset.card_le_card
  intro n hn
  rw [mem_counted_iff] at hn ⊢
  exact ⟨hn.1, hn.2.1.trans hMN, hn.2.2⟩

theorem one_le_Q {N : ℕ} (hN : 1 ≤ N) : 1 ≤ Q N := by
  rw [Q]
  exact Finset.card_pos.mpr ⟨1, by simp [hN]⟩

/-! ## The final asymptotic bridge

This section is independent of Nicolas's number-theoretic argument.  It
formalizes the exact logical reason why one fixed upper logarithmic power
refutes the proposed lower bound for every power.
-/

theorem tendsto_log_nat_atTop :
    Tendsto (fun n : ℕ ↦ Real.log (n : ℝ)) atTop atTop :=
  Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop

theorem logPower_isLittleO_succ (C : ℕ) :
    (fun n : ℕ ↦ logPower C n) =o[atTop]
      (fun n : ℕ ↦ logPower (C + 1) n) := by
  change ((fun x : ℝ ↦ x ^ C) ∘ (fun n : ℕ ↦ Real.log (n : ℝ))) =o[atTop]
    ((fun x : ℝ ↦ x ^ (C + 1)) ∘ (fun n : ℕ ↦ Real.log (n : ℝ)))
  exact (isLittleO_pow_pow_atTop_of_lt (𝕜 := ℝ) (Nat.lt_succ_self C)).comp_tendsto
    tendsto_log_nat_atTop

theorem eventually_logPower_ne_zero (C : ℕ) :
    ∀ᶠ n : ℕ in atTop, logPower C n ≠ 0 := by
  filter_upwards [tendsto_log_nat_atTop.eventually (eventually_gt_atTop 0)] with n hn
  exact pow_ne_zero C hn.ne'

theorem not_logPower_succ_isBigO (C : ℕ) :
    ¬(fun n : ℕ ↦ logPower (C + 1) n) =O[atTop]
      (fun n : ℕ ↦ logPower C n) := by
  exact (logPower_isLittleO_succ C).not_isBigO
    (Filter.Eventually.frequently (eventually_logPower_ne_zero C))

/-- Any fixed polynomial-logarithmic upper bound for `Q` refutes the exact
universal assertion in Problem 381, at the next natural exponent. -/
theorem not_erdos381Claim_of_nicolasPolynomialUpperBound
    (hNicolas : NicolasPolynomialUpperBound) : ¬ Erdos381Claim := by
  rintro hclaim
  obtain ⟨C, hupper⟩ := hNicolas
  have hlower : (fun n : ℕ ↦ logPower (C + 1) n) =O[atTop]
      (fun n : ℕ ↦ (Q n : ℝ)) :=
    hclaim (C + 1) (by omega)
  exact not_logPower_succ_isBigO C (hlower.trans hupper)

theorem not_erdos381Claim_of_localPolynomialBound
    (hlocal : NicolasLocalPolynomialBound) : ¬ Erdos381Claim :=
  not_erdos381Claim_of_nicolasPolynomialUpperBound
    (nicolasPolynomialUpperBound_of_local hlocal)

end Erdos381
