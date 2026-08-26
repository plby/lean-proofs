import ErdosProblems.Erdos520.SmoothContribution
import ErdosProblems.Erdos520.ThinScheduleChebyshev

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open Finset
open scoped BigOperators

namespace Erdos
namespace Problem520

/-!
# Chebyshev bounds for the Rankin Euler product

For `sigma = 1 - delta`, Rankin's method leaves the finite product

`prod_{p < y} (1 - p^(-sigma))^(-1)`.

Bounding every `p^delta` by `y^delta` loses a factor `log log y`, which is
too expensive at the critical schedule.  The elementary repair is to split
the primes at an intermediate point `a`.  The primes up to `a` cost
`a^delta` times a reciprocal-prime prefix, while the primes in `(a,y]` cost
`y^delta` times only the reciprocal mass of that block.  Chebyshev's theorem
controls both quantities without a prime number theorem.
-/

/-- The finite Euler product in Rankin's smooth-number bound. -/
noncomputable def smoothRankinEulerProduct (sigma : ℝ) (y : ℕ) : ℝ :=
  ∏ p ∈ y.primesBelow, (1 - (p : ℝ) ^ (-sigma))⁻¹

/-- The corresponding first-order prime sum. -/
noncomputable def smoothRankinPrimeSum (sigma : ℝ) (y : ℕ) : ℝ :=
  ∑ p ∈ y.primesBelow, (p : ℝ) ^ (-sigma)

/-- Each geometric Euler factor is bounded by an exponential.  The explicit
constant is uniform in the prime because every prime is at least `2`. -/
theorem smoothRankinEulerProduct_le_exp_primeSum
    {sigma : ℝ} (hsigma : 0 < sigma) (y : ℕ) :
    smoothRankinEulerProduct sigma y ≤
      Real.exp
        ((1 - (2 : ℝ) ^ (-sigma))⁻¹ * smoothRankinPrimeSum sigma y) := by
  classical
  let q : ℝ := (2 : ℝ) ^ (-sigma)
  have hqnonneg : 0 ≤ q := Real.rpow_nonneg (by norm_num) _
  have hqlt : q < 1 := by
    dsimp [q]
    rw [Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2)]
    exact inv_lt_one_of_one_lt₀
      (Real.one_lt_rpow (by norm_num : (1 : ℝ) < 2) hsigma)
  have hden : 0 < 1 - q := sub_pos.mpr hqlt
  have hfactor (p : ℕ) (hp : p ∈ y.primesBelow) :
      (1 - (p : ℝ) ^ (-sigma))⁻¹ ≤
        Real.exp ((1 - q)⁻¹ * (p : ℝ) ^ (-sigma)) := by
    have hpprime : p.Prime := Nat.prime_of_mem_primesBelow hp
    have hpR : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hpprime.two_le
    have hpPos : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hpprime.pos
    let x : ℝ := (p : ℝ) ^ (-sigma)
    have hxnonneg : 0 ≤ x := Real.rpow_nonneg hpPos.le _
    have hxq : x ≤ q := by
      dsimp [x, q]
      exact Real.rpow_le_rpow_of_nonpos (by norm_num) hpR (by linarith)
    have hdx : 0 < 1 - x := sub_pos.mpr (hxq.trans_lt hqlt)
    have hfrac : x / (1 - x) ≤ x / (1 - q) :=
      div_le_div_of_nonneg_left hxnonneg hden (by linarith)
    calc
      (1 - (p : ℝ) ^ (-sigma))⁻¹ = 1 + x / (1 - x) := by
        change (1 - x)⁻¹ = 1 + x / (1 - x)
        field_simp [hdx.ne']
        ring
      _ ≤ 1 + x / (1 - q) := by linarith
      _ ≤ Real.exp (x / (1 - q)) := by
        simpa [add_comm] using! Real.add_one_le_exp (x / (1 - q))
      _ = Real.exp ((1 - q)⁻¹ * (p : ℝ) ^ (-sigma)) := by
        congr 1
        dsimp [x]
        ring
  unfold smoothRankinEulerProduct smoothRankinPrimeSum
  calc
    (∏ p ∈ y.primesBelow, (1 - (p : ℝ) ^ (-sigma))⁻¹)
        ≤ ∏ p ∈ y.primesBelow,
            Real.exp ((1 - q)⁻¹ * (p : ℝ) ^ (-sigma)) := by
      apply Finset.prod_le_prod
      · intro p hp
        have hpprime : p.Prime := Nat.prime_of_mem_primesBelow hp
        have hpPos : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hpprime.pos
        have hpR : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hpprime.two_le
        have hxq : (p : ℝ) ^ (-sigma) ≤ q :=
          Real.rpow_le_rpow_of_nonpos (by norm_num) hpR (by linarith)
        have : 0 < 1 - (p : ℝ) ^ (-sigma) :=
          sub_pos.mpr (hxq.trans_lt hqlt)
        positivity
      · intro p hp
        exact hfactor p hp
    _ = Real.exp
        ((1 - q)⁻¹ * ∑ p ∈ y.primesBelow, (p : ℝ) ^ (-sigma)) := by
      rw [← Real.exp_sum]
      congr 1
      rw [Finset.mul_sum]
    _ = Real.exp
        ((1 - (2 : ℝ) ^ (-sigma))⁻¹ *
          ∑ p ∈ y.primesBelow, (p : ℝ) ^ (-sigma)) := by
      rfl

private theorem prime_rpow_rankin_eq
    {delta : ℝ} {p : ℕ} (hp : p.Prime) :
    (p : ℝ) ^ (-(1 - delta)) =
      (p : ℝ) ^ delta * (p : ℝ)⁻¹ := by
  have hpPos : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hp.pos
  rw [show -(1 - delta) = delta - 1 by ring,
    Real.rpow_sub hpPos, Real.rpow_one, div_eq_mul_inv]

/-- Splitting at `a` removes the otherwise fatal `y^delta * log log y`
loss.  The slight enlargement from primes `< y` to primes `≤ y` is harmless
and makes the old/fresh-prime decomposition exact. -/
theorem smoothRankinPrimeSum_one_sub_le_split
    {delta : ℝ} (hdelta : 0 ≤ delta) {a y : ℕ} (hay : a ≤ y) :
    smoothRankinPrimeSum (1 - delta) y ≤
      (a : ℝ) ^ delta * primeReciprocalPrefix a +
        (y : ℝ) ^ delta * freshReciprocalSum a y := by
  classical
  have hsubset : y.primesBelow ⊆ (y + 1).primesBelow := by
    intro p hp
    have hpinfo := Nat.mem_primesBelow.mp hp
    exact Nat.mem_primesBelow.mpr ⟨by omega, hpinfo.2⟩
  have henlarge :
      (∑ p ∈ y.primesBelow, (p : ℝ) ^ (-(1 - delta))) ≤
        ∑ p ∈ (y + 1).primesBelow, (p : ℝ) ^ (-(1 - delta)) := by
    exact Finset.sum_le_sum_of_subset_of_nonneg hsubset (by
      intro p _hp _hnot
      exact Real.rpow_nonneg (Nat.cast_nonneg p) _)
  have hlow :
      (∑ p ∈ (a + 1).primesBelow, (p : ℝ) ^ (-(1 - delta))) ≤
        (a : ℝ) ^ delta * primeReciprocalPrefix a := by
    unfold primeReciprocalPrefix
    rw [Finset.mul_sum]
    gcongr with p hp
    have hpprime : p.Prime := Nat.prime_of_mem_primesBelow hp
    have hpa : p ≤ a := Nat.le_of_lt_succ (Nat.mem_primesBelow.mp hp).1
    rw [prime_rpow_rankin_eq hpprime]
    exact mul_le_mul_of_nonneg_right
      (Real.rpow_le_rpow (Nat.cast_nonneg p) (by exact_mod_cast hpa) hdelta)
      (inv_nonneg.mpr (Nat.cast_nonneg p))
  have hhigh :
      (∑ p ∈ freshPrimes a y, (p : ℝ) ^ (-(1 - delta))) ≤
        (y : ℝ) ^ delta * freshReciprocalSum a y := by
    unfold freshReciprocalSum
    rw [Finset.mul_sum]
    gcongr with p hp
    have hpinfo := mem_freshPrimes.mp hp
    rw [prime_rpow_rankin_eq hpinfo.1]
    exact mul_le_mul_of_nonneg_right
      (Real.rpow_le_rpow (Nat.cast_nonneg p)
        (by exact_mod_cast hpinfo.2.2) hdelta)
      (inv_nonneg.mpr (Nat.cast_nonneg p))
  unfold smoothRankinPrimeSum
  calc
    (∑ p ∈ y.primesBelow, (p : ℝ) ^ (-(1 - delta)))
        ≤ ∑ p ∈ (y + 1).primesBelow,
            (p : ℝ) ^ (-(1 - delta)) := henlarge
    _ = (∑ p ∈ (a + 1).primesBelow,
            (p : ℝ) ^ (-(1 - delta))) +
          ∑ p ∈ freshPrimes a y, (p : ℝ) ^ (-(1 - delta)) := by
      rw [primesBelow_succ_eq_union_freshPrimes hay,
        sum_union (primesBelow_succ_disjoint_freshPrimes a y)]
    _ ≤ (a : ℝ) ^ delta * primeReciprocalPrefix a +
          (y : ℝ) ^ delta * freshReciprocalSum a y :=
      add_le_add hlow hhigh

/-- Chebyshev controls a reciprocal-prime prefix, with all dependence on the
fixed initial segment retained explicitly. -/
theorem primeReciprocalPrefix_le_of_primeCountingUpperBound
    {C : ℝ} {N a : ℕ}
    (hC : 0 ≤ C) (hP : PrimeCountingUpperBound C N)
    (hNa : N ≤ a) (hN : 2 ≤ N) :
    primeReciprocalPrefix a ≤
      primeReciprocalPrefix N +
        C * (logLogNat a - logLogNat N) +
          2 * C / Real.log (N : ℝ) := by
  have heq := freshReciprocalSum_eq_prefix_sub hNa
  have hfresh := freshReciprocalSum_le_of_primeCountingUpperBound
    hC hP (le_refl N) hN hNa
  linarith [heq]

/-- Fully explicit Chebyshev estimate for the split prime sum. -/
theorem smoothRankinPrimeSum_one_sub_le_chebyshevSplit
    {delta C : ℝ} (hdelta : 0 ≤ delta) {N a y : ℕ}
    (hC : 0 ≤ C) (hP : PrimeCountingUpperBound C N)
    (hN : 2 ≤ N) (hNa : N ≤ a) (hay : a ≤ y) :
    smoothRankinPrimeSum (1 - delta) y ≤
      (a : ℝ) ^ delta *
          (primeReciprocalPrefix N +
            C * (logLogNat a - logLogNat N) +
              2 * C / Real.log (N : ℝ)) +
        (y : ℝ) ^ delta *
          (C * (logLogNat y - logLogNat a) +
            2 * C / Real.log (a : ℝ)) := by
  have hprefix := primeReciprocalPrefix_le_of_primeCountingUpperBound
    hC hP hNa hN
  have hfresh := freshReciprocalSum_le_of_primeCountingUpperBound
    hC hP hNa (hN.trans hNa) hay
  calc
    smoothRankinPrimeSum (1 - delta) y ≤
        (a : ℝ) ^ delta * primeReciprocalPrefix a +
          (y : ℝ) ^ delta * freshReciprocalSum a y :=
      smoothRankinPrimeSum_one_sub_le_split hdelta hay
    _ ≤ (a : ℝ) ^ delta *
          (primeReciprocalPrefix N +
            C * (logLogNat a - logLogNat N) +
              2 * C / Real.log (N : ℝ)) +
        (y : ℝ) ^ delta *
          (C * (logLogNat y - logLogNat a) +
            2 * C / Real.log (a : ℝ)) := by
      exact add_le_add
        (mul_le_mul_of_nonneg_left hprefix (Real.rpow_nonneg (Nat.cast_nonneg a) _))
        (mul_le_mul_of_nonneg_left hfresh (Real.rpow_nonneg (Nat.cast_nonneg y) _))

/-- The finite Rankin product with no analytic hypothesis beyond a Chebyshev
prime-counting upper bound. -/
theorem smoothRankinEulerProduct_one_sub_le_chebyshevSplit
    {delta C : ℝ} (hdelta : 0 ≤ delta) (hdeltaOne : delta < 1)
    {N a y : ℕ} (hC : 0 ≤ C) (hP : PrimeCountingUpperBound C N)
    (hN : 2 ≤ N) (hNa : N ≤ a) (hay : a ≤ y) :
    smoothRankinEulerProduct (1 - delta) y ≤
      Real.exp ((1 - (2 : ℝ) ^ (-(1 - delta)))⁻¹ *
        ((a : ℝ) ^ delta *
            (primeReciprocalPrefix N +
              C * (logLogNat a - logLogNat N) +
                2 * C / Real.log (N : ℝ)) +
          (y : ℝ) ^ delta *
            (C * (logLogNat y - logLogNat a) +
              2 * C / Real.log (a : ℝ)))) := by
  have hsigma : 0 < 1 - delta := sub_pos.mpr hdeltaOne
  have hq : 0 < (1 - (2 : ℝ) ^ (-(1 - delta)))⁻¹ := by
    rw [inv_pos, sub_pos]
    rw [Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2)]
    exact inv_lt_one_of_one_lt₀
      (Real.one_lt_rpow (by norm_num : (1 : ℝ) < 2) hsigma)
  calc
    smoothRankinEulerProduct (1 - delta) y ≤
        Real.exp ((1 - (2 : ℝ) ^ (-(1 - delta)))⁻¹ *
          smoothRankinPrimeSum (1 - delta) y) :=
      smoothRankinEulerProduct_le_exp_primeSum hsigma y
    _ ≤ Real.exp ((1 - (2 : ℝ) ^ (-(1 - delta)))⁻¹ *
        ((a : ℝ) ^ delta *
            (primeReciprocalPrefix N +
              C * (logLogNat a - logLogNat N) +
                2 * C / Real.log (N : ℝ)) +
          (y : ℝ) ^ delta *
            (C * (logLogNat y - logLogNat a) +
              2 * C / Real.log (a : ℝ)))) := by
      apply Real.exp_le_exp.mpr
      exact mul_le_mul_of_nonneg_left
        (smoothRankinPrimeSum_one_sub_le_chebyshevSplit
          hdelta hC hP hN hNa hay) hq.le

/-- Rankin's smooth-number count with the Chebyshev split substituted.  This
is an unconditional finite estimate once the existential Chebyshev constants
from `exists_primeCountingUpperBound` are chosen. -/
theorem card_smoothNumbersUpTo_le_rankinChebyshevSplit
    {delta C : ℝ} (hdelta : 0 ≤ delta) (hdeltaOne : delta < 1)
    (z : ℕ) {N a y : ℕ} (hC : 0 ≤ C)
    (hP : PrimeCountingUpperBound C N)
    (hN : 2 ≤ N) (hNa : N ≤ a) (hay : a ≤ y) :
    ((Nat.smoothNumbersUpTo z y).card : ℝ) ≤
      (z : ℝ) ^ (1 - delta) *
        Real.exp ((1 - (2 : ℝ) ^ (-(1 - delta)))⁻¹ *
          ((a : ℝ) ^ delta *
              (primeReciprocalPrefix N +
                C * (logLogNat a - logLogNat N) +
                  2 * C / Real.log (N : ℝ)) +
            (y : ℝ) ^ delta *
              (C * (logLogNat y - logLogNat a) +
                2 * C / Real.log (a : ℝ)))) := by
  calc
    ((Nat.smoothNumbersUpTo z y).card : ℝ) ≤
        (z : ℝ) ^ (1 - delta) * smoothRankinEulerProduct (1 - delta) y := by
      simpa [smoothRankinEulerProduct] using!
        card_smoothNumbersUpTo_le_rankinProduct
          (sub_pos.mpr hdeltaOne) z y
    _ ≤ (z : ℝ) ^ (1 - delta) *
        Real.exp ((1 - (2 : ℝ) ^ (-(1 - delta)))⁻¹ *
          ((a : ℝ) ^ delta *
              (primeReciprocalPrefix N +
                C * (logLogNat a - logLogNat N) +
                  2 * C / Real.log (N : ℝ)) +
            (y : ℝ) ^ delta *
              (C * (logLogNat y - logLogNat a) +
                2 * C / Real.log (a : ℝ)))) := by
      exact mul_le_mul_of_nonneg_left
        (smoothRankinEulerProduct_one_sub_le_chebyshevSplit
          hdelta hdeltaOne hC hP hN hNa hay)
        (Real.rpow_nonneg (Nat.cast_nonneg z) _)

/-!
## A concrete half-logarithmic split

When `y = 2^(2*m)` we may take `a = 2^m`.  The upper reciprocal-prime
block then has the absolute `log log` width `log 2`, while its Rankin weight
is `y^delta`; the lower prefix carries only the square-root-scale weight
`a^delta`.  This is the elementary shape needed on Caich's doubly
exponential cutoff.
-/

theorem logLogNat_two_pow_eq {m : ℕ} (hm : 0 < m) :
    logLogNat (2 ^ m) =
      Real.log (m : ℝ) + Real.log (Real.log 2) := by
  have hmR : (m : ℝ) ≠ 0 := by exact_mod_cast hm.ne'
  have hlogTwo : Real.log (2 : ℝ) ≠ 0 :=
    (Real.log_pos (by norm_num)).ne'
  unfold logLogNat
  rw [show (((2 ^ m : ℕ) : ℝ)) = (2 : ℝ) ^ m by norm_cast,
    Real.log_pow, Real.log_mul hmR hlogTwo]

theorem logLogNat_two_pow_two_mul_sub {m : ℕ} (hm : 0 < m) :
    logLogNat (2 ^ (2 * m)) - logLogNat (2 ^ m) = Real.log 2 := by
  rw [logLogNat_two_pow_eq (by omega : 0 < 2 * m), logLogNat_two_pow_eq hm]
  have hmR : (m : ℝ) ≠ 0 := by exact_mod_cast hm.ne'
  rw [Nat.cast_mul, Nat.cast_ofNat, Real.log_mul (by norm_num) hmR]
  ring

/-- Explicit square-root split estimate for a power-of-two endpoint. -/
theorem smoothRankinEulerProduct_one_sub_le_chebyshevHalfPower
    {delta C : ℝ} (hdelta : 0 ≤ delta) (hdeltaOne : delta < 1)
    {N m : ℕ} (hm : 0 < m) (hC : 0 ≤ C)
    (hP : PrimeCountingUpperBound C N) (hN : 2 ≤ N)
    (hNm : N ≤ 2 ^ m) :
    smoothRankinEulerProduct (1 - delta) (2 ^ (2 * m)) ≤
      Real.exp ((1 - (2 : ℝ) ^ (-(1 - delta)))⁻¹ *
        (((2 ^ m : ℕ) : ℝ) ^ delta *
            (primeReciprocalPrefix N +
              C * (logLogNat (2 ^ m) - logLogNat N) +
                2 * C / Real.log (N : ℝ)) +
          (((2 ^ (2 * m) : ℕ) : ℝ) ^ delta *
            (C * Real.log 2 +
              2 * C / Real.log ((2 ^ m : ℕ) : ℝ))))) := by
  have hay : 2 ^ m ≤ 2 ^ (2 * m) := by
    exact Nat.pow_le_pow_right (by norm_num) (by omega)
  have h := smoothRankinEulerProduct_one_sub_le_chebyshevSplit
    hdelta hdeltaOne hC hP hN hNm hay
  rw [logLogNat_two_pow_two_mul_sub hm] at h
  exact h

/-- Smooth-number cardinality bound with the same half-logarithmic split. -/
theorem card_smoothNumbersUpTo_le_rankinChebyshevHalfPower
    {delta C : ℝ} (hdelta : 0 ≤ delta) (hdeltaOne : delta < 1)
    (z : ℕ) {N m : ℕ} (hm : 0 < m) (hC : 0 ≤ C)
    (hP : PrimeCountingUpperBound C N) (hN : 2 ≤ N)
    (hNm : N ≤ 2 ^ m) :
    ((Nat.smoothNumbersUpTo z (2 ^ (2 * m))).card : ℝ) ≤
      (z : ℝ) ^ (1 - delta) *
        Real.exp ((1 - (2 : ℝ) ^ (-(1 - delta)))⁻¹ *
          (((2 ^ m : ℕ) : ℝ) ^ delta *
              (primeReciprocalPrefix N +
                C * (logLogNat (2 ^ m) - logLogNat N) +
                  2 * C / Real.log (N : ℝ)) +
            (((2 ^ (2 * m) : ℕ) : ℝ) ^ delta *
              (C * Real.log 2 +
                2 * C / Real.log ((2 ^ m : ℕ) : ℝ))))) := by
  have hay : 2 ^ m ≤ 2 ^ (2 * m) := by
    exact Nat.pow_le_pow_right (by norm_num) (by omega)
  have h := card_smoothNumbersUpTo_le_rankinChebyshevSplit
    hdelta hdeltaOne z hC hP hN hNm hay
  rw [logLogNat_two_pow_two_mul_sub hm] at h
  exact h

theorem card_smoothNumbersUpTo_mono_smoothness
    (z : ℕ) {y Y : ℕ} (hyY : y ≤ Y) :
    (Nat.smoothNumbersUpTo z y).card ≤
      (Nat.smoothNumbersUpTo z Y).card := by
  apply Finset.card_le_card
  intro n hn
  rw [Nat.mem_smoothNumbersUpTo] at hn ⊢
  exact ⟨hn.1, Nat.smoothNumbers_mono hyY hn.2⟩

/-- The half-power estimate also applies after enlarging an arbitrary
smoothness cutoff to the next convenient power-of-two square.  In
particular this absorbs the `cutoff + 1` convention used by `Psi`. -/
theorem card_smoothNumbersUpTo_le_rankinChebyshevHalfPower_of_le
    {delta C : ℝ} (hdelta : 0 ≤ delta) (hdeltaOne : delta < 1)
    (z y : ℕ) {N m : ℕ} (hy : y ≤ 2 ^ (2 * m)) (hm : 0 < m)
    (hC : 0 ≤ C) (hP : PrimeCountingUpperBound C N) (hN : 2 ≤ N)
    (hNm : N ≤ 2 ^ m) :
    ((Nat.smoothNumbersUpTo z y).card : ℝ) ≤
      (z : ℝ) ^ (1 - delta) *
        Real.exp ((1 - (2 : ℝ) ^ (-(1 - delta)))⁻¹ *
          (((2 ^ m : ℕ) : ℝ) ^ delta *
              (primeReciprocalPrefix N +
                C * (logLogNat (2 ^ m) - logLogNat N) +
                  2 * C / Real.log (N : ℝ)) +
            (((2 ^ (2 * m) : ℕ) : ℝ) ^ delta *
              (C * Real.log 2 +
                2 * C / Real.log ((2 ^ m : ℕ) : ℝ))))) := by
  calc
    ((Nat.smoothNumbersUpTo z y).card : ℝ) ≤
        (Nat.smoothNumbersUpTo z (2 ^ (2 * m))).card := by
      exact_mod_cast card_smoothNumbersUpTo_mono_smoothness z hy
    _ ≤ (z : ℝ) ^ (1 - delta) *
        Real.exp ((1 - (2 : ℝ) ^ (-(1 - delta)))⁻¹ *
          (((2 ^ m : ℕ) : ℝ) ^ delta *
              (primeReciprocalPrefix N +
                C * (logLogNat (2 ^ m) - logLogNat N) +
                  2 * C / Real.log (N : ℝ)) +
            (((2 ^ (2 * m) : ℕ) : ℝ) ^ delta *
              (C * Real.log 2 +
                2 * C / Real.log ((2 ^ m : ℕ) : ℝ))))) :=
      card_smoothNumbersUpTo_le_rankinChebyshevHalfPower
        hdelta hdeltaOne z hm hC hP hN hNm

theorem two_pow_cutoff_succ_le_halfPower (E : ℕ) :
    2 ^ E + 1 ≤ 2 ^ (2 * (E / 2 + 1)) := by
  have hone : 1 ≤ 2 ^ E := one_le_pow₀ (by norm_num)
  have hexp : E + 1 ≤ 2 * (E / 2 + 1) := by omega
  calc
    2 ^ E + 1 ≤ 2 ^ E + 2 ^ E := Nat.add_le_add_left hone _
    _ = 2 ^ (E + 1) := by rw [pow_succ]; ring
    _ ≤ 2 ^ (2 * (E / 2 + 1)) :=
      Nat.pow_le_pow_right (by norm_num) hexp

theorem self_le_two_pow_half_add_one (n : ℕ) :
    n ≤ 2 ^ (n / 2 + 1) := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
      by_cases hn : n ≤ 3
      · interval_cases n <;> norm_num
      · have hn4 : 4 ≤ n := by omega
        have hprev : n - 2 < n := by omega
        have hih := ih (n - 2) hprev
        have hdiv : n / 2 + 1 = (n - 2) / 2 + 2 := by omega
        rw [hdiv, show (n - 2) / 2 + 2 = ((n - 2) / 2 + 1) + 1 by omega,
          pow_succ]
        calc
          n ≤ 2 * (n - 2) := by omega
          _ ≤ 2 * 2 ^ ((n - 2) / 2 + 1) := Nat.mul_le_mul_left 2 hih
          _ = 2 ^ ((n - 2) / 2 + 1) * 2 := by ring

theorem le_two_pow_half_add_one_of_le {N E : ℕ} (hNE : N ≤ E) :
    N ≤ 2 ^ (E / 2 + 1) := by
  calc
    N ≤ 2 ^ (N / 2 + 1) := self_le_two_pow_half_add_one N
    _ ≤ 2 ^ (E / 2 + 1) := by
      exact Nat.pow_le_pow_right (by norm_num) (Nat.add_le_add_right
        (Nat.div_le_div_right hNE) 1)

/-- Direct form for the `Psi` convention when the smooth cutoff itself is
the power of two `2^E`: its smooth-number parameter is `2^E + 1`, and the
preceding lemma enlarges this by only a bounded factor to a square power. -/
theorem card_smoothNumbersUpTo_two_pow_succ_le_rankinChebyshev
    {delta C : ℝ} (hdelta : 0 ≤ delta) (hdeltaOne : delta < 1)
    (z E : ℕ) {N : ℕ} (hC : 0 ≤ C)
    (hP : PrimeCountingUpperBound C N) (hN : 2 ≤ N)
    (hNE : N ≤ 2 ^ (E / 2 + 1)) :
    ((Nat.smoothNumbersUpTo z (2 ^ E + 1)).card : ℝ) ≤
      (z : ℝ) ^ (1 - delta) *
        Real.exp ((1 - (2 : ℝ) ^ (-(1 - delta)))⁻¹ *
          (((2 ^ (E / 2 + 1) : ℕ) : ℝ) ^ delta *
              (primeReciprocalPrefix N +
                C * (logLogNat (2 ^ (E / 2 + 1)) - logLogNat N) +
                  2 * C / Real.log (N : ℝ)) +
            (((2 ^ (2 * (E / 2 + 1)) : ℕ) : ℝ) ^ delta *
              (C * Real.log 2 +
                2 * C /
                  Real.log ((2 ^ (E / 2 + 1) : ℕ) : ℝ))))) := by
  exact card_smoothNumbersUpTo_le_rankinChebyshevHalfPower_of_le
    hdelta hdeltaOne z (2 ^ E + 1) (two_pow_cutoff_succ_le_halfPower E)
      (by omega) hC hP hN hNE

/-- There are absolute constants for the preceding cardinality estimate.
This is the premise-free public form: the Chebyshev data are selected using
Mathlib's theorem `exists_primeCountingUpperBound`. -/
theorem exists_unconditional_smoothRankinHalfPower_cardinalityBound :
    ∃ C : ℝ, 0 < C ∧ ∃ N : ℕ, 2 ≤ N ∧
      ∀ {delta : ℝ} (z y : ℕ) {m : ℕ},
        0 ≤ delta → delta < 1 → y ≤ 2 ^ (2 * m) → 0 < m → N ≤ 2 ^ m →
        ((Nat.smoothNumbersUpTo z y).card : ℝ) ≤
          (z : ℝ) ^ (1 - delta) *
            Real.exp ((1 - (2 : ℝ) ^ (-(1 - delta)))⁻¹ *
              (((2 ^ m : ℕ) : ℝ) ^ delta *
                  (primeReciprocalPrefix N +
                    C * (logLogNat (2 ^ m) - logLogNat N) +
                      2 * C / Real.log (N : ℝ)) +
                (((2 ^ (2 * m) : ℕ) : ℝ) ^ delta *
                  (C * Real.log 2 +
                    2 * C / Real.log ((2 ^ m : ℕ) : ℝ))))) := by
  obtain ⟨C, hC, N, hN, hP⟩ := exists_primeCountingUpperBound
  refine ⟨C, hC, N, hN, ?_⟩
  intro delta z y m hdelta hdeltaOne hym hm hNm
  exact card_smoothNumbersUpTo_le_rankinChebyshevHalfPower_of_le
    hdelta hdeltaOne z y hym hm hC.le hP hN hNm

end Problem520
end Erdos
