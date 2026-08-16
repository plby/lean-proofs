import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.NumberTheory.EulerProduct.DirichletLSeries
import Mathlib.NumberTheory.Harmonic.Bounds
import Mathlib.Topology.Algebra.InfiniteSum.Field

/-!
# Polylogarithmic bounds for a finite prime Euler product

This file bounds

`∏ p ∈ Nat.primesLE R, (1 + A / p)`.

The elementary comparison with the full harmonic sum gives an exponential
bound.  More importantly for Fourier-tail estimates, shifting the Euler
product of the Riemann zeta function to

`s = 1 + 1 / log R`

gives a polynomial bound in `log R`.  This avoids requiring a separately
formalized Mertens theorem.
-/

namespace Wikipedia.SzemeredisTheorem

open Filter Set
open scoped BigOperators Topology

/-- The finite prime product whose growth is needed in the sieve tail. -/
noncomputable def primeHarmonicProduct (A : ℝ) (R : ℕ) : ℝ :=
  ∏ p ∈ Nat.primesLE R, (1 + A / (p : ℝ))

theorem primeHarmonicProduct_nonneg
    {A : ℝ} (hA : 0 ≤ A) (R : ℕ) :
    0 ≤ primeHarmonicProduct A R := by
  unfold primeHarmonicProduct
  exact Finset.prod_nonneg fun p _ => by positivity

/-- On the real half-line to the right of one, the zeta function has the
elementary integral-test bound `ζ(s) ≤ 1 + 1 / (s - 1)`. -/
theorem norm_riemannZeta_ofReal_le_one_add_inv_sub_one
    {s : ℝ} (hs : 1 < s) :
    ‖riemannZeta (s : ℂ)‖ ≤ 1 + (s - 1)⁻¹ := by
  have hsC : 1 < ((s : ℂ).re) := by simpa
  have hs0C : (s : ℂ) ≠ 0 := by
    exact_mod_cast (ne_of_gt (lt_trans zero_lt_one hs))
  have hneg : -s ≠ 0 :=
    neg_ne_zero.mpr (ne_of_gt (lt_trans zero_lt_one hs))
  have hzero : (0 : ℝ) ^ (-s) = 0 :=
    Real.zero_rpow hneg
  have hsumC :=
    summable_riemannZetaSummand (s := (s : ℂ)) hsC
  have hsumR : Summable (fun n : ℕ => (n : ℝ) ^ (-s)) := by
    exact Real.summable_nat_rpow.mpr (by linarith)
  have hsumSucc :
      Summable (fun n : ℕ => (Nat.succ n : ℝ) ^ (-s)) :=
    hsumR.comp_injective Nat.succ_injective
  have htail :
      ∑' n : ℕ, (Nat.succ (Nat.succ n) : ℝ) ^ (-s) ≤
        ∫ x : ℝ in Set.Ioi ((1 : ℕ) : ℝ), x ^ (-s) := by
    simpa only [Nat.succ_eq_add_one, Nat.add_assoc] using
      AntitoneOn.tsum_comp_add_le_integral
      (f := fun x : ℝ => x ^ (-s)) 1
      ((Real.antitoneOn_rpow_Ioi_of_exponent_nonpos
        (by linarith)).mono
          (by
            intro x hx
            exact (show (0 : ℝ) < x from
              lt_of_lt_of_le (by norm_num) hx)))
      (integrableOn_Ioi_rpow_of_lt
        (by linarith) (by norm_num : (0 : ℝ) < ((1 : ℕ) : ℝ)))
      (fun x hx => Real.rpow_nonneg
        (le_of_lt (lt_trans (by norm_num) hx)) _)
  calc
    ‖riemannZeta (s : ℂ)‖ =
        ‖∑' n : ℕ,
          riemannZetaSummandHom
            hs0C n‖ := by
      rw [tsum_riemannZetaSummand hsC]
    _ ≤ ∑' n : ℕ,
        ‖riemannZetaSummandHom
          hs0C n‖ :=
      norm_tsum_le_tsum_norm hsumC
    _ = ∑' n : ℕ, (n : ℝ) ^ (-s) := by
      apply tsum_congr
      intro n
      rw [riemannZetaSummandHom]
      simp only [MonoidWithZeroHom.coe_mk, ZeroHom.coe_mk]
      rw [← Complex.ofReal_natCast,
        Complex.norm_cpow_eq_rpow_re_of_nonneg
          (Nat.cast_nonneg n)
          (by
            change -s ≠ 0
            exact neg_ne_zero.mpr
              (ne_of_gt (lt_trans zero_lt_one hs)))]
      simp
    _ = 1 + ∑' n : ℕ,
        (Nat.succ (Nat.succ n) : ℝ) ^ (-s) := by
      rw [hsumR.tsum_eq_zero_add]
      rw [show ((0 : ℕ) : ℝ) ^ (-s) = 0 by simpa using hzero]
      simp only [zero_add]
      change (∑' n : ℕ, (Nat.succ n : ℝ) ^ (-s)) =
        1 + ∑' n : ℕ, (Nat.succ (Nat.succ n) : ℝ) ^ (-s)
      rw [hsumSucc.tsum_eq_zero_add]
      norm_num
    _ ≤ 1 + ∫ x : ℝ in Set.Ioi ((1 : ℕ) : ℝ), x ^ (-s) :=
      by gcongr
    _ = 1 + (s - 1)⁻¹ := by
      rw [integral_Ioi_rpow_of_lt
        (a := -s) (c := ((1 : ℕ) : ℝ))
        (by linarith) (by norm_num)]
      norm_num [Real.one_rpow]
      have hden : -s + 1 = -(s - 1) := by ring
      rw [hden]
      simp only [neg_div_neg_eq, one_div]

/-- A real Euler factor is also the norm of the corresponding complex
Euler factor. -/
theorem norm_primeEulerFactor_ofReal
    {p : ℕ} (hp : 2 ≤ p) {s : ℝ} (hs : 0 < s) :
    ‖(1 - (p : ℂ) ^ (-((s : ℝ) : ℂ)))⁻¹‖ =
      (1 - (p : ℝ) ^ (-s))⁻¹ := by
  have hpR : (0 : ℝ) ≤ p := by positivity
  have hpOne : (1 : ℝ) < p := by exact_mod_cast hp
  have hxlt : (p : ℝ) ^ (-s) < 1 := by
    rw [Real.rpow_lt_one_iff (by positivity)]
    exact Or.inr (Or.inl ⟨hpOne, by linarith⟩)
  have hpos : 0 < 1 - (p : ℝ) ^ (-s) := sub_pos.mpr hxlt
  have hcast :
      (1 - (p : ℂ) ^ (-((s : ℝ) : ℂ)))⁻¹ =
        (((1 - (p : ℝ) ^ (-s))⁻¹ : ℝ) : ℂ) := by
    rw [Complex.ofReal_inv, Complex.ofReal_sub,
      Complex.ofReal_one, Complex.ofReal_cpow hpR]
    simp
  rw [hcast, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (inv_pos.mpr hpos)]

/-- If `p ≤ R`, shifting the exponent from `1` to
`1 + 1 / log R` loses at most the factor `3 > exp 1`. -/
theorem inv_natCast_le_three_mul_shifted_rpow
    {p R : ℕ} (hp : 2 ≤ p) (hpR : p ≤ R) :
    (p : ℝ)⁻¹ ≤
      3 * (p : ℝ) ^ (-(1 + (Real.log R)⁻¹)) := by
  have hpPos : (0 : ℝ) < p := by positivity
  have hRone : (1 : ℝ) ≤ R := by
    exact_mod_cast (le_trans (by omega : 1 ≤ p) hpR)
  have hlog : 0 ≤ Real.log R := Real.log_nonneg hRone
  have hpow :
      (p : ℝ) ^ (Real.log R)⁻¹ ≤ Real.exp 1 := by
    calc
      (p : ℝ) ^ (Real.log R)⁻¹ ≤
          (R : ℝ) ^ (Real.log R)⁻¹ :=
        Real.rpow_le_rpow (by positivity) (by exact_mod_cast hpR)
          (inv_nonneg.mpr hlog)
      _ ≤ Real.exp 1 := Real.rpow_inv_log_le_exp_one
  have hpow3 : (p : ℝ) ^ (Real.log R)⁻¹ ≤ 3 :=
    hpow.trans Real.exp_one_lt_three.le
  calc
    (p : ℝ)⁻¹ = (p : ℝ) ^ (-1 : ℝ) := by
      rw [Real.rpow_neg (le_of_lt hpPos), Real.rpow_one]
    _ = (p : ℝ) ^ (Real.log R)⁻¹ *
        (p : ℝ) ^ (-(1 + (Real.log R)⁻¹)) := by
      rw [← Real.rpow_add hpPos]
      congr 1
      ring
    _ ≤ 3 * (p : ℝ) ^ (-(1 + (Real.log R)⁻¹)) :=
      mul_le_mul_of_nonneg_right hpow3 (by positivity)

/-- Pointwise comparison of the factor `1 + A / p` with a fixed natural
power of the shifted zeta Euler factor. -/
theorem one_add_nat_div_le_shiftedEulerFactor_pow
    (A : ℕ) {p R : ℕ} (hp : 2 ≤ p) (hpR : p ≤ R) :
    1 + (A : ℝ) / (p : ℝ) ≤
      ((1 - (p : ℝ) ^ (-(1 + (Real.log R)⁻¹)))⁻¹) ^
        (3 * A) := by
  let x : ℝ := (p : ℝ) ^ (-(1 + (Real.log R)⁻¹))
  have hRtwo : 2 ≤ R := hp.trans hpR
  have hRone : (1 : ℝ) < R := by exact_mod_cast hRtwo
  have hshift : 0 < 1 + (Real.log R)⁻¹ := by
    have : 0 < Real.log R := Real.log_pos hRone
    positivity
  have hxnonneg : 0 ≤ x := by
    dsimp [x]
    positivity
  have hxlt : x < 1 := by
    dsimp [x]
    rw [Real.rpow_lt_one_iff (by positivity)]
    exact Or.inr (Or.inl ⟨(by exact_mod_cast hp : (1 : ℝ) < p),
      neg_lt_zero.mpr hshift⟩)
  have hden : 0 < 1 - x := sub_pos.mpr hxlt
  have hbase : 1 + x ≤ (1 - x)⁻¹ := by
    rw [inv_eq_one_div, le_div_iff₀ hden]
    nlinarith [sq_nonneg x]
  have hone :
      1 + (p : ℝ)⁻¹ ≤ (1 + x) ^ 3 := by
    calc
      1 + (p : ℝ)⁻¹ ≤ 1 + 3 * x := by
        gcongr
        simpa only [x] using
          inv_natCast_le_three_mul_shifted_rpow hp hpR
      _ ≤ (1 + x) ^ 3 := by
        simpa using
          (one_add_mul_le_pow (R := ℝ) (a := x)
            (by linarith) 3)
  calc
    1 + (A : ℝ) / (p : ℝ) =
        1 + (A : ℝ) * (p : ℝ)⁻¹ := by
      rw [div_eq_mul_inv]
    _ ≤ (1 + (p : ℝ)⁻¹) ^ A :=
      one_add_mul_le_pow
        (by
          have hinv : 0 ≤ (p : ℝ)⁻¹ := by positivity
          linarith) A
    _ ≤ ((1 + x) ^ 3) ^ A :=
      pow_le_pow_left₀ (by positivity) hone A
    _ = (1 + x) ^ (3 * A) := by
      rw [pow_mul]
    _ ≤ ((1 - x)⁻¹) ^ (3 * A) :=
      pow_le_pow_left₀ (by linarith) hbase (3 * A)

theorem one_le_norm_primeEulerFactor_ofReal
    {p : ℕ} (hp : 2 ≤ p) {s : ℝ} (hs : 0 < s) :
    1 ≤ ‖(1 - (p : ℂ) ^ (-((s : ℝ) : ℂ)))⁻¹‖ := by
  rw [norm_primeEulerFactor_ofReal hp hs]
  have hxlt : (p : ℝ) ^ (-s) < 1 := by
    rw [Real.rpow_lt_one_iff (by positivity)]
    exact Or.inr (Or.inl
      ⟨(by exact_mod_cast hp : (1 : ℝ) < p), by linarith⟩)
  exact (one_le_inv₀ (sub_pos.mpr hxlt)).2
    (by
      have hxnonneg :=
        Real.rpow_nonneg (show (0 : ℝ) ≤ p by positivity) (-s)
      linarith)

theorem one_add_nat_div_le_norm_shiftedPrimeEulerFactor_pow
    (A : ℕ) {p R : ℕ} (hp : 2 ≤ p) (hpR : p ≤ R) :
    1 + (A : ℝ) / (p : ℝ) ≤
      ‖(1 - (p : ℂ) ^
        (-(((1 + (Real.log R)⁻¹ : ℝ)) : ℂ)))⁻¹‖ ^ (3 * A) := by
  have hRtwo : 2 ≤ R := hp.trans hpR
  have hRone : (1 : ℝ) < R := by exact_mod_cast hRtwo
  have hshift : 0 < 1 + (Real.log R)⁻¹ := by
    have : 0 < Real.log R := Real.log_pos hRone
    positivity
  rw [norm_primeEulerFactor_ofReal hp hshift]
  exact one_add_nat_div_le_shiftedEulerFactor_pow A hp hpR

/-- The primes at most `R`, retyped as elements of `Nat.Primes`. -/
noncomputable def primesLEAsPrimes (R : ℕ) : Finset Nat.Primes :=
  (Nat.primesLE R).attach.map
    { toFun := fun p =>
        ⟨p.1, Nat.prime_of_mem_primesLE p.2⟩
      inj' := by
        intro p q h
        apply Subtype.ext
        exact congrArg (fun z : Nat.Primes => (z : ℕ)) h }

theorem prod_primesLEAsPrimes
    (R : ℕ) (f : ℕ → ℝ) :
    (∏ p ∈ primesLEAsPrimes R, f p) =
      ∏ p ∈ Nat.primesLE R, f p := by
  classical
  unfold primesLEAsPrimes
  rw [Finset.prod_map]
  exact Finset.prod_attach _ f

theorem le_of_mem_primesLEAsPrimes
    {R : ℕ} {p : Nat.Primes}
    (hp : p ∈ primesLEAsPrimes R) :
    (p : ℕ) ≤ R := by
  classical
  unfold primesLEAsPrimes at hp
  rcases Finset.mem_map.mp hp with ⟨q, _hq, hq⟩
  calc
    (p : ℕ) = q.1 :=
      congrArg (fun z : Nat.Primes => (z : ℕ)) hq.symm
    _ ≤ R := Nat.le_of_mem_primesLE q.2

/-- The finite prime product is bounded by a fixed natural power of the
Riemann zeta function at `1 + 1 / log R`. -/
theorem primeHarmonicProduct_nat_le_norm_zeta_pow
    (A R : ℕ) (hR : 2 ≤ R) :
    primeHarmonicProduct (A : ℝ) R ≤
      ‖riemannZeta
        ((((1 + (Real.log R)⁻¹ : ℝ)) : ℂ))‖ ^ (3 * A) := by
  classical
  have hRone : (1 : ℝ) < R := by exact_mod_cast hR
  have hlog : 0 < Real.log R := Real.log_pos hRone
  have hshift : 0 < 1 + (Real.log R)⁻¹ := by positivity
  have hsC :
      1 < ((((1 + (Real.log R)⁻¹ : ℝ)) : ℂ)).re := by
    change (1 : ℝ) < 1 + (Real.log R)⁻¹
    have hinv : 0 < (Real.log R)⁻¹ := inv_pos.mpr hlog
    linarith
  have hzeta :
      HasProd
        (fun p : Nat.Primes =>
          ‖(1 - (p : ℂ) ^
            (-(((1 + (Real.log R)⁻¹ : ℝ)) : ℂ)))⁻¹‖ ^ (3 * A))
        (‖riemannZeta
          ((((1 + (Real.log R)⁻¹ : ℝ)) : ℂ))‖ ^ (3 * A)) :=
    (riemannZeta_eulerProduct_hasProd hsC).norm.pow (3 * A)
  calc
    primeHarmonicProduct (A : ℝ) R =
        ∏ p ∈ primesLEAsPrimes R,
          (1 + (A : ℝ) / (p : ℝ)) := by
      exact (prod_primesLEAsPrimes R
        (fun p => 1 + (A : ℝ) / (p : ℝ))).symm
    _ ≤ ∏ p ∈ primesLEAsPrimes R,
        ‖(1 - (p : ℂ) ^
          (-(((1 + (Real.log R)⁻¹ : ℝ)) : ℂ)))⁻¹‖ ^ (3 * A) := by
      apply Finset.prod_le_prod
      · intro p _hp
        positivity
      · intro p hp
        exact one_add_nat_div_le_norm_shiftedPrimeEulerFactor_pow
          A p.prop.two_le (le_of_mem_primesLEAsPrimes hp)
    _ ≤ ‖riemannZeta
          ((((1 + (Real.log R)⁻¹ : ℝ)) : ℂ))‖ ^ (3 * A) := by
      apply ge_of_tendsto hzeta
      filter_upwards [eventually_ge_atTop (primesLEAsPrimes R)] with t ht
      apply Finset.prod_le_prod_of_subset_of_one_le ht
      · intro p _hp
        positivity
      · intro p _hpt _hps
        exact one_le_pow₀
          (one_le_norm_primeEulerFactor_ofReal
            p.prop.two_le hshift)

/-- The prime reciprocal sum is bounded by the full harmonic sum.  This is
the best logarithmic-in-`R` estimate available without using prime
distribution. -/
theorem sum_primesLE_inv_le_one_add_log (R : ℕ) :
    (∑ p ∈ Nat.primesLE R, (p : ℝ)⁻¹) ≤
      1 + Real.log R := by
  have hsubset : Nat.primesLE R ⊆ Finset.Icc 1 R := by
    intro p hp
    exact Finset.mem_Icc.mpr
      ⟨(Nat.prime_of_mem_primesLE hp).one_le,
        Nat.le_of_mem_primesLE hp⟩
  calc
    (∑ p ∈ Nat.primesLE R, (p : ℝ)⁻¹) ≤
        ∑ p ∈ Finset.Icc 1 R, (p : ℝ)⁻¹ :=
      Finset.sum_le_sum_of_subset_of_nonneg hsubset
        (fun p _hp _ => by positivity)
    _ = (harmonic R : ℝ) := by
      simp only [harmonic_eq_sum_Icc, Rat.cast_sum,
        Rat.cast_inv, Rat.cast_natCast]
    _ ≤ 1 + Real.log R := harmonic_le_one_add_log R

/-- A completely elementary bound, valid for every nonnegative real
coefficient.  It is useful as a fallback, but grows like `R^A`. -/
theorem primeHarmonicProduct_le_exp_one_add_log
    {A : ℝ} (hA : 0 ≤ A) (R : ℕ) :
    primeHarmonicProduct A R ≤
      Real.exp (A * (1 + Real.log R)) := by
  have hsum :
      (∑ p ∈ Nat.primesLE R, A / (p : ℝ)) =
        A * ∑ p ∈ Nat.primesLE R, (p : ℝ)⁻¹ := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro p _hp
    rw [div_eq_mul_inv]
  calc
    primeHarmonicProduct A R ≤
        Real.exp (∑ p ∈ Nat.primesLE R, A / (p : ℝ)) := by
      unfold primeHarmonicProduct
      exact Real.prod_one_add_le_exp_sum _
        (fun p => div_nonneg hA (by positivity))
    _ = Real.exp
        (A * ∑ p ∈ Nat.primesLE R, (p : ℝ)⁻¹) := by
      rw [hsum]
    _ ≤ Real.exp (A * (1 + Real.log R)) := by
      rw [Real.exp_le_exp]
      exact mul_le_mul_of_nonneg_left
        (sum_primesLE_inv_le_one_add_log R) hA

/-- Explicit polylogarithmic growth for a natural coefficient. -/
theorem primeHarmonicProduct_nat_le_one_add_log_pow
    (A R : ℕ) (hR : 2 ≤ R) :
    primeHarmonicProduct (A : ℝ) R ≤
      (1 + Real.log R) ^ (3 * A) := by
  have hRone : (1 : ℝ) < R := by exact_mod_cast hR
  have hlog : 0 < Real.log R := Real.log_pos hRone
  have hs : (1 : ℝ) < 1 + (Real.log R)⁻¹ := by
    have : 0 < (Real.log R)⁻¹ := inv_pos.mpr hlog
    linarith
  have hzeta :
      ‖riemannZeta
        ((((1 + (Real.log R)⁻¹ : ℝ)) : ℂ))‖ ≤
        1 + Real.log R := by
    calc
      ‖riemannZeta
          ((((1 + (Real.log R)⁻¹ : ℝ)) : ℂ))‖ ≤
          1 + ((1 + (Real.log R)⁻¹) - 1)⁻¹ :=
        norm_riemannZeta_ofReal_le_one_add_inv_sub_one hs
      _ = 1 + Real.log R := by
        rw [add_sub_cancel_left, inv_inv]
  exact (primeHarmonicProduct_nat_le_norm_zeta_pow A R hR).trans
    (pow_le_pow_left₀ (norm_nonneg _) hzeta (3 * A))

/-- Real-coefficient version, with the natural ceiling in the exponent. -/
theorem primeHarmonicProduct_le_one_add_log_pow_natCeil
    {A : ℝ} (hA : 0 ≤ A) (R : ℕ) (hR : 2 ≤ R) :
    primeHarmonicProduct A R ≤
      (1 + Real.log R) ^ (3 * ⌈A⌉₊) := by
  calc
    primeHarmonicProduct A R ≤
        primeHarmonicProduct (⌈A⌉₊ : ℝ) R := by
      unfold primeHarmonicProduct
      apply Finset.prod_le_prod
      · intro p _hp
        positivity
      · intro p hp
        gcongr
        exact Nat.le_ceil A
    _ ≤ (1 + Real.log R) ^ (3 * ⌈A⌉₊) :=
      primeHarmonicProduct_nat_le_one_add_log_pow ⌈A⌉₊ R hR

theorem prod_primesLE_one_add_nat_div_le_one_add_log_pow
    (A R : ℕ) (hR : 2 ≤ R) :
    (∏ p ∈ Nat.primesLE R,
      (1 + (A : ℝ) / (p : ℝ))) ≤
        (1 + Real.log R) ^ (3 * A) := by
  simpa only [primeHarmonicProduct] using
    primeHarmonicProduct_nat_le_one_add_log_pow A R hR

theorem prod_primesLE_one_add_div_le_one_add_log_pow_natCeil
    {A : ℝ} (hA : 0 ≤ A) (R : ℕ) (hR : 2 ≤ R) :
    (∏ p ∈ Nat.primesLE R,
      (1 + A / (p : ℝ))) ≤
        (1 + Real.log R) ^ (3 * ⌈A⌉₊) := by
  simpa only [primeHarmonicProduct] using
    primeHarmonicProduct_le_one_add_log_pow_natCeil hA R hR

end Wikipedia.SzemeredisTheorem
