import ErdosProblems.Erdos1140.External.Erdos587.Main
import ErdosProblems.Erdos1141
import ErdosProblems.Erdos1140.Erdos1140Base
import BoundedGaps.BombieriVinogradov.Analytic.QuadraticZetaLFunctionComparison

/-!
# Erdős Problem 1140: Burgess and quadratic-zeta argument

This module proves the axiom-free analytic input used to resolve Problem 1140:
every sufficiently large prime has a sufficiently small prime modulus on
which `2*x^2 ≡ n` is solvable.  It combines the fourth-moment Burgess bound,
an Euler-hyperbola decomposition, and the Siegel lower bound proved in
`ErdosProblems.Erdos1140.Erdos1140Base`.
-/

namespace Erdos1140

open scoped BigOperators

open MeasureTheory Set

open Erdos587

open BoundedGaps.Maynard

open ArithmeticFunction

open Filter

private theorem eventually_const_mul_nat_rpow_le_const_mul_nat_rpow
    {C d a b : ℝ} (_hC : 0 ≤ C) (hd : 0 < d) (hab : a < b) :
    ∀ᶠ m : ℕ in atTop,
      C * (m : ℝ) ^ a ≤ d * (m : ℝ) ^ b := by
  have hpow : Tendsto (fun m : ℕ ↦ (m : ℝ) ^ (b - a)) atTop atTop :=
    (tendsto_rpow_atTop (sub_pos.mpr hab)).comp
      (tendsto_natCast_atTop_atTop (R := ℝ))
  have hlarge := hpow.eventually (eventually_ge_atTop (C / d))
  filter_upwards [hlarge, eventually_ge_atTop 1] with m hm hm1
  have hmpos : 0 < (m : ℝ) := by exact_mod_cast (show 0 < m by omega)
  have hratio : C ≤ d * (m : ℝ) ^ (b - a) := by
    simpa only [mul_comm] using (div_le_iff₀ hd).mp hm
  calc
    C * (m : ℝ) ^ a ≤ (d * (m : ℝ) ^ (b - a)) * (m : ℝ) ^ a := by
      gcongr
    _ = d * ((m : ℝ) ^ (b - a) * (m : ℝ) ^ a) := by ring
    _ = d * (m : ℝ) ^ b := by
      rw [← Real.rpow_add hmpos]
      congr 2
      ring

private theorem eventually_const_mul_log_sq_le_rpow
    {c d a : ℝ} (hc : 0 < c) (hd : 0 < d) (ha : 0 < a) :
    ∀ᶠ m : ℕ in atTop,
      c * Real.log (m : ℝ) ^ 2 ≤ d * (m : ℝ) ^ a := by
  have hsmall :=
    (isLittleO_log_rpow_rpow_atTop (2 : ℝ)
      (show (0 : ℝ) < a / 2 by linarith)).comp_tendsto
      (tendsto_natCast_atTop_atTop (R := ℝ))
  have hlog := hsmall.bound (show (0 : ℝ) < 1 by positivity)
  have hrpow : Tendsto (fun m : ℕ ↦ (m : ℝ) ^ (a / 2)) atTop atTop :=
    (tendsto_rpow_atTop (by linarith : 0 < a / 2)).comp
      (tendsto_natCast_atTop_atTop (R := ℝ))
  have hlarge := hrpow.eventually (eventually_ge_atTop (c / d))
  filter_upwards [hlog, hlarge, eventually_ge_atTop 2] with m hlog hlarge hm
  have hmpos : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
  have hlogpos : 0 < Real.log (m : ℝ) := Real.log_pos (by exact_mod_cast hm)
  have hhalfpos : 0 < (m : ℝ) ^ (a / 2) := Real.rpow_pos_of_pos hmpos _
  simp only [Function.comp_apply, Real.norm_eq_abs] at hlog
  rw [abs_of_pos (Real.rpow_pos_of_pos hlogpos _), abs_of_pos hhalfpos] at hlog
  have hcoef : c ≤ d * (m : ℝ) ^ (a / 2) := by
    simpa only [mul_comm] using (div_le_iff₀ hd).mp hlarge
  have hlog' : Real.log (m : ℝ) ^ 2 ≤ (m : ℝ) ^ (a / 2) := by
    simpa only [Real.rpow_two, one_mul] using hlog
  calc
    c * Real.log (m : ℝ) ^ 2 ≤ c * (m : ℝ) ^ (a / 2) := by gcongr
    _ ≤ d * ((m : ℝ) ^ (a / 2) * (m : ℝ) ^ (a / 2)) := by
      calc
        c * (m : ℝ) ^ (a / 2) ≤
            (d * (m : ℝ) ^ (a / 2)) * (m : ℝ) ^ (a / 2) :=
          mul_le_mul_of_nonneg_right hcoef hhalfpos.le
        _ = _ := by ring
    _ = d * (m : ℝ) ^ a := by
      rw [← Real.rpow_add hmpos]
      congr 2
      ring

/-- A slowly growing dyadic saving used in the fourth-moment Burgess bound. -/
def saving (q : ℕ) : ℕ := 2 ^ (Nat.log 2 q / 512)

lemma saving_pos (q : ℕ) : 0 < saving q := by
  simp [saving]

lemma saving_pow_512_le {q : ℕ} (hq : q ≠ 0) : saving q ^ 512 ≤ q := by
  calc
    saving q ^ 512 = 2 ^ ((Nat.log 2 q / 512) * 512) := by
      rw [saving, pow_mul]
    _ ≤ 2 ^ Nat.log 2 q :=
      Nat.pow_le_pow_right (by omega) (Nat.div_mul_le_self _ _)
    _ ≤ q := Nat.pow_log_le_self 2 hq

lemma saving_cast_le_rpow {q : ℕ} (hq : q ≠ 0) :
    (saving q : ℝ) ≤ (q : ℝ) ^ ((512 : ℝ)⁻¹) := by
  have hreal : (saving q : ℝ) ^ 512 ≤ (q : ℝ) := by
    exact_mod_cast saving_pow_512_le hq
  have hr := Real.rpow_le_rpow (by positivity : 0 ≤ (saving q : ℝ) ^ 512)
    hreal (by positivity : (0 : ℝ) ≤ (512 : ℝ)⁻¹)
  calc
    (saving q : ℝ) =
        ((saving q : ℝ) ^ 512) ^ ((512 : ℝ)⁻¹) := by
      exact (Real.pow_rpow_inv_natCast (x := (saving q : ℝ))
        (n := 512) (by positivity) (by norm_num)).symm
    _ ≤ (q : ℝ) ^ ((512 : ℝ)⁻¹) := hr

lemma rpow_one_div_512_lt_two_mul_saving (q : ℕ) :
    (q : ℝ) ^ ((512 : ℝ)⁻¹) < 2 * saving q := by
  apply lt_of_pow_lt_pow_left₀ 512 (by positivity)
  have hleft : ((q : ℝ) ^ ((512 : ℝ)⁻¹)) ^ 512 = (q : ℝ) :=
    Real.rpow_inv_natCast_pow (by positivity) (by norm_num)
  rw [hleft]
  have hnat : q < (2 * saving q) ^ 512 := by
    calc
      q < 2 ^ (Nat.log 2 q).succ := Nat.lt_pow_succ_log_self (by omega) q
      _ ≤ 2 ^ (512 * (Nat.log 2 q / 512 + 1)) := by
        apply Nat.pow_le_pow_right (by omega)
        have := Nat.mod_lt (Nat.log 2 q) (by omega : 0 < 512)
        omega
      _ = (2 * saving q) ^ 512 := by
        rw [saving, mul_pow, ← pow_mul, ← pow_add]
        congr 1
        ring
  exact_mod_cast hnat

lemma burgessDyadicShift_cast_le_rpow {q : ℕ} (hq : q ≠ 0) :
    (burgessDyadicShift q : ℝ) ≤ (q : ℝ) ^ ((8 : ℝ)⁻¹) := by
  have hreal : (burgessDyadicShift q : ℝ) ^ 8 ≤ (q : ℝ) := by
    exact_mod_cast burgessDyadicShift_pow_eight_le hq
  have hr := Real.rpow_le_rpow
    (by positivity : 0 ≤ (burgessDyadicShift q : ℝ) ^ 8)
    hreal (by positivity : (0 : ℝ) ≤ (8 : ℝ)⁻¹)
  calc
    (burgessDyadicShift q : ℝ) =
        ((burgessDyadicShift q : ℝ) ^ 8) ^ ((8 : ℝ)⁻¹) := by
      exact (Real.pow_rpow_inv_natCast (x := (burgessDyadicShift q : ℝ))
        (n := 8) (by positivity) (by norm_num)).symm
    _ ≤ (q : ℝ) ^ ((8 : ℝ)⁻¹) := hr

lemma rpow_one_eighth_lt_two_mul_burgessDyadicShift (q : ℕ) :
    (q : ℝ) ^ ((8 : ℝ)⁻¹) < 2 * burgessDyadicShift q := by
  apply lt_of_pow_lt_pow_left₀ 8 (by positivity)
  have hleft : ((q : ℝ) ^ ((8 : ℝ)⁻¹)) ^ 8 = (q : ℝ) :=
    Real.rpow_inv_natCast_pow (by positivity) (by norm_num)
  rw [hleft]
  norm_num only [mul_pow]
  have hraw : (q : ℝ) < 256 * (burgessDyadicShift q : ℝ) ^ 8 := by
    exact_mod_cast lt_two_hundred_fifty_six_mul_burgessDyadicShift_pow_eight q
  norm_num at hraw ⊢
  exact hraw

lemma saving_pow_five_le_rpow_one_div_64 {q : ℕ} (hq : q ≠ 0) :
    (saving q : ℝ) ^ 5 ≤ (q : ℝ) ^ ((64 : ℝ)⁻¹) := by
  have hpow512 : saving q ^ 512 ≤ q := saving_pow_512_le hq
  have hreal : (saving q : ℝ) ^ 512 ≤ (q : ℝ) := by
    exact_mod_cast hpow512
  have hqpos : (0 : ℝ) < q := by positivity
  have hsnonneg : (0 : ℝ) ≤ saving q := by positivity
  have hroot : (saving q : ℝ) ^ 8 ≤ (q : ℝ) ^ ((64 : ℝ)⁻¹) := by
    have hr := Real.rpow_le_rpow (by positivity : 0 ≤ (saving q : ℝ) ^ 512)
      hreal (by positivity : (0 : ℝ) ≤ (64 : ℝ)⁻¹)
    have hid :
        ((saving q : ℝ) ^ 512) ^ ((64 : ℝ)⁻¹) =
          (saving q : ℝ) ^ 8 := by
      rw [show 512 = 8 * 64 by norm_num, pow_mul]
      exact Real.pow_rpow_inv_natCast (by positivity) (by norm_num)
    calc
      (saving q : ℝ) ^ 8 =
          ((saving q : ℝ) ^ 512) ^ ((64 : ℝ)⁻¹) := hid.symm
      _ ≤ (q : ℝ) ^ ((64 : ℝ)⁻¹) := by
        exact hr
  exact (pow_le_pow_right₀ (by exact_mod_cast saving_pos q) (by omega : 5 ≤ 8)).trans hroot

/-- The ready Burgess certificate specialized to one odd prime conductor. -/
lemma singleton_burgess_bound
    {p H J M : ℕ} (hp : p.Prime) (hJ : 0 < J)
    (hp3 : 3 ≤ p) (hH3 : 3 ≤ H) (hHp : H < p)
    (hrelaxed : (p : ℝ) ≤ (H : ℝ) ^ 2 * (p : ℝ) ^ ((64 : ℝ)⁻¹))
    (hfit :
      (2 * 4 ^ ({p} : Finset ℕ).card) *
        burgessDenominatorLossExtra ({p} : Finset ℕ).card J
          (burgessDyadicShift p) ≤ H)
    (hsmall :
      2 * (burgessDenominatorCountExtra ({p} : Finset ℕ).card J
        (burgessDyadicShift p) H * H) < p)
    (hloss2 :
      (2 : ℝ) ^ (10 * ({p} : Finset ℕ).card) * (J : ℝ) ^ 5 ≤
        (p : ℝ) ^ ((64 : ℝ)⁻¹))
    (hloss23 :
      (2 : ℝ) ^ (10 * ({p} : Finset ℕ).card) * (J : ℝ) ^ 5 *
        (3 : ℝ) ^ ({p} : Finset ℕ).card ≤
        (p : ℝ) ^ ((64 : ℝ)⁻¹))
    (hgrowth :
      3 * (2 : ℝ) ^ 53 * (((p : ℝ) ^ ((64 : ℝ)⁻¹)) ^ 4) ≤
        burgessDyadicShift p) :
    |∑ i ∈ Finset.range H,
      quadraticPrimeFactorProduct {p} (M + i)| ≤
        (H : ℝ) / (32 * J) := by
  have hcert := coprimeBurgessCertificate_of_relaxed_dyadic_range
    ({p} : Finset ℕ) (by simpa using hp) hJ
      (by simpa [primeSetModulus] using hp3) hH3
      (by simpa [primeSetModulus] using hHp)
      (by simpa [primeSetModulus] using hrelaxed)
      (by simpa [primeSetModulus] using hfit)
      (by simpa [primeSetModulus] using hsmall)
      (by simpa [primeSetModulus] using hloss2)
      (by simpa [primeSetModulus] using hloss23)
      (by simpa [primeSetModulus] using hgrowth)
  rcases hcert with
    ⟨U, V, hU, hV, hHq, hUq, hVq, hUV, hnowrap, hstrict⟩
  have hodd : ∀ r ∈ ({p} : Finset ℕ), r ≠ 2 := by
    intro r hr
    have hrp : r = p := by simpa using hr
    subst r
    omega
  have hbound := abs_quadraticPrimeFactorProduct_sum_lt_of_coprime_burgess
    ({p} : Finset ℕ) (by simpa using hp) (M := M)
    (B := (H : ℝ) / (16 * (2 : ℝ) ^ ({p} : Finset ℕ).card * J))
    (by omega) hU hV (by positivity) hHq hUq hVq hodd hUV hnowrap hstrict
  calc
    |∑ i ∈ Finset.range H, quadraticPrimeFactorProduct {p} (M + i)| ≤
        (H : ℝ) / (16 * (2 : ℝ) ^ ({p} : Finset ℕ).card * J) := hbound.le
    _ = (H : ℝ) / (32 * J) := by
      simp only [Finset.card_singleton, pow_one]
      ring

/-- Uniform one-prime Burgess saving in the range needed by the reciprocal
tail and smoothed-convolution estimates. -/
theorem eventually_singleton_burgess_bound :
    ∀ᶠ p : ℕ in atTop, ∀ (hp : p.Prime) (H M : ℕ),
      (p : ℝ) ^ ((63 : ℝ) / 128) ≤ H →
      (H : ℝ) ≤ 2 * Real.sqrt (p : ℝ) * saving p * Real.log (p : ℝ) →
      3 ≤ H → H < p →
      |∑ i ∈ Finset.range H,
        quadraticPrimeFactorProduct {p} (M + i)| ≤
          (H : ℝ) / (32 * saving p) := by
  obtain ⟨Qg, hQg⟩ := exists_burgessFourthGrowthThreshold
  have hfitAsymp := eventually_const_mul_nat_rpow_le_const_mul_nat_rpow
    (C := 8192) (d := 1)
    (a := (512 : ℝ)⁻¹ + (8 : ℝ)⁻¹) (b := (63 : ℝ) / 128)
    (by positivity) (by positivity) (by norm_num)
  have hloss2 := eventually_const_mul_nat_rpow_le_const_mul_nat_rpow
    (C := 1024) (d := 1) (a := 5 * (512 : ℝ)⁻¹)
    (b := (64 : ℝ)⁻¹) (by positivity) (by positivity) (by norm_num)
  have hloss23 := eventually_const_mul_nat_rpow_le_const_mul_nat_rpow
    (C := 3072) (d := 1) (a := 5 * (512 : ℝ)⁻¹)
    (b := (64 : ℝ)⁻¹) (by positivity) (by positivity) (by norm_num)
  have hnowrapLog := eventually_const_mul_log_sq_le_rpow
    (c := 16) (d := 1)
    (a := (8 : ℝ)⁻¹ - (512 : ℝ)⁻¹)
    (by positivity) (by positivity) (by norm_num)
  filter_upwards [hfitAsymp, hloss2, hloss23, hnowrapLog,
    eventually_ge_atTop (max 3 Qg)] with p hfitAsymp hloss2
      hloss23 hnowrapLog hpLarge
  intro hp H M hrootLower hHupper hH3 hHp
  have hp0 : p ≠ 0 := hp.ne_zero
  have hpRealPos : (0 : ℝ) < p := by positivity
  have hlogPos : 0 < Real.log (p : ℝ) :=
    Real.log_pos (by exact_mod_cast hp.one_lt)
  have hJpos : 0 < saving p := saving_pos p
  have hVpos : 0 < burgessDyadicShift p := burgessDyadicShift_pos p
  have hJupper := saving_cast_le_rpow hp0
  have hVupper := burgessDyadicShift_cast_le_rpow hp0
  have hJVupper :
      (saving p : ℝ) * burgessDyadicShift p ≤
        (p : ℝ) ^ ((512 : ℝ)⁻¹ + (8 : ℝ)⁻¹) := by
    calc
      (saving p : ℝ) * burgessDyadicShift p ≤
          (p : ℝ) ^ ((512 : ℝ)⁻¹) * (p : ℝ) ^ ((8 : ℝ)⁻¹) :=
        mul_le_mul hJupper hVupper (by positivity) (by positivity)
      _ = (p : ℝ) ^ ((512 : ℝ)⁻¹ + (8 : ℝ)⁻¹) :=
        (Real.rpow_add hpRealPos _ _).symm
  have hrelaxed :
      (p : ℝ) ≤ (H : ℝ) ^ 2 * (p : ℝ) ^ ((64 : ℝ)⁻¹) := by
    have hsquare := pow_le_pow_left₀ (by positivity) hrootLower 2
    calc
      (p : ℝ) =
          ((p : ℝ) ^ ((63 : ℝ) / 128)) ^ 2 *
            (p : ℝ) ^ ((64 : ℝ)⁻¹) := by
        rw [(Real.rpow_mul_natCast hpRealPos.le _ 2).symm,
          ← Real.rpow_add hpRealPos]
        congr 2
        norm_num
      _ ≤ (H : ℝ) ^ 2 * (p : ℝ) ^ ((64 : ℝ)⁻¹) := by gcongr
  have hfit :
      (2 * 4 ^ ({p} : Finset ℕ).card) *
        burgessDenominatorLossExtra ({p} : Finset ℕ).card (saving p)
          (burgessDyadicShift p) ≤ H := by
    have hbig :
        8192 * ((saving p : ℝ) * burgessDyadicShift p) ≤
          (p : ℝ) ^ ((63 : ℝ) / 128) := by
      calc
        8192 * ((saving p : ℝ) * burgessDyadicShift p) ≤
            8192 *
              (p : ℝ) ^ ((512 : ℝ)⁻¹ + (8 : ℝ)⁻¹) := by gcongr
        _ ≤ (p : ℝ) ^ ((63 : ℝ) / 128) := by simpa using hfitAsymp
    have hreal :
        (8192 : ℝ) * ((saving p : ℝ) * burgessDyadicShift p) ≤ H := by
      exact hbig.trans hrootLower
    have hnat : 8192 * (saving p * burgessDyadicShift p) ≤ H := by
      exact_mod_cast hreal
    calc
      (2 * 4 ^ ({p} : Finset ℕ).card) *
          burgessDenominatorLossExtra ({p} : Finset ℕ).card (saving p)
            (burgessDyadicShift p) =
          8192 * (saving p * burgessDyadicShift p) := by
        simp [burgessDenominatorLossExtra]
        ring
      _ ≤ H := hnat
  have hJpow5 :
      (saving p : ℝ) ^ 5 ≤ (p : ℝ) ^ (5 * (512 : ℝ)⁻¹) := by
    calc
      (saving p : ℝ) ^ 5 ≤ ((p : ℝ) ^ ((512 : ℝ)⁻¹)) ^ 5 :=
        pow_le_pow_left₀ (by positivity) hJupper 5
      _ = (p : ℝ) ^ ((512 : ℝ)⁻¹ * 5) :=
        (Real.rpow_mul_natCast hpRealPos.le _ 5).symm
      _ = (p : ℝ) ^ (5 * (512 : ℝ)⁻¹) := by ring
  have hloss2' :
      (2 : ℝ) ^ (10 * ({p} : Finset ℕ).card) *
          (saving p : ℝ) ^ 5 ≤ (p : ℝ) ^ ((64 : ℝ)⁻¹) := by
    calc
      (2 : ℝ) ^ (10 * ({p} : Finset ℕ).card) *
          (saving p : ℝ) ^ 5 = 1024 * (saving p : ℝ) ^ 5 := by
        rw [Finset.card_singleton]
        norm_num
      _ ≤ 1024 * (p : ℝ) ^ (5 * (512 : ℝ)⁻¹) := by gcongr
      _ ≤ (p : ℝ) ^ ((64 : ℝ)⁻¹) := by simpa using hloss2
  have hloss23' :
      (2 : ℝ) ^ (10 * ({p} : Finset ℕ).card) *
          (saving p : ℝ) ^ 5 * (3 : ℝ) ^ ({p} : Finset ℕ).card ≤
        (p : ℝ) ^ ((64 : ℝ)⁻¹) := by
    calc
      (2 : ℝ) ^ (10 * ({p} : Finset ℕ).card) *
          (saving p : ℝ) ^ 5 * (3 : ℝ) ^ ({p} : Finset ℕ).card =
          3072 * (saving p : ℝ) ^ 5 := by
        rw [Finset.card_singleton]
        norm_num
        ring
      _ ≤ 3072 * (p : ℝ) ^ (5 * (512 : ℝ)⁻¹) := by gcongr
      _ ≤ (p : ℝ) ^ ((64 : ℝ)⁻¹) := by simpa using hloss23
  have hJL :
      8 * (saving p : ℝ) * Real.log (p : ℝ) ^ 2 <
        1024 * burgessDyadicShift p := by
    have hlogCombined :
        16 * ((saving p : ℝ) * Real.log (p : ℝ) ^ 2) ≤
          (p : ℝ) ^ ((8 : ℝ)⁻¹) := by
      calc
        16 * ((saving p : ℝ) * Real.log (p : ℝ) ^ 2) =
            (saving p : ℝ) * (16 * Real.log (p : ℝ) ^ 2) := by ring
        _ ≤
            (p : ℝ) ^ ((512 : ℝ)⁻¹) *
              (16 * Real.log (p : ℝ) ^ 2) := by
          exact mul_le_mul_of_nonneg_right hJupper (by positivity)
        _ ≤ (p : ℝ) ^ ((512 : ℝ)⁻¹) *
              (p : ℝ) ^ ((8 : ℝ)⁻¹ - (512 : ℝ)⁻¹) := by
          gcongr
          simpa using hnowrapLog
        _ = (p : ℝ) ^ ((8 : ℝ)⁻¹) := by
          rw [← Real.rpow_add hpRealPos]
          congr 2
          ring
    have hshiftLower := rpow_one_eighth_lt_two_mul_burgessDyadicShift p
    nlinarith
  have hsmall :
      2 * (burgessDenominatorCountExtra ({p} : Finset ℕ).card
          (saving p) (burgessDyadicShift p) H * H) < p := by
    have hsqrtSq : Real.sqrt (p : ℝ) ^ 2 = (p : ℝ) :=
      Real.sq_sqrt hpRealPos.le
    have hJrealPos : (0 : ℝ) < saving p := by exact_mod_cast hJpos
    have hHsq :
        (H : ℝ) ^ 2 ≤
          (2 * Real.sqrt (p : ℝ) * saving p * Real.log (p : ℝ)) ^ 2 :=
      pow_le_pow_left₀ (by positivity) hHupper 2
    have hsqReal :
        (2 : ℝ) * (H : ℝ) ^ 2 <
          (p : ℝ) *
            burgessDenominatorLossExtra ({p} : Finset ℕ).card
              (saving p) (burgessDyadicShift p) := by
      have hm := mul_lt_mul_of_pos_left hJL
        (mul_pos hpRealPos hJrealPos)
      calc
        (2 : ℝ) * (H : ℝ) ^ 2 ≤
            2 * (2 * Real.sqrt (p : ℝ) * saving p *
              Real.log (p : ℝ)) ^ 2 := by gcongr
        _ = 8 * Real.sqrt (p : ℝ) ^ 2 * (saving p : ℝ) ^ 2 *
              Real.log (p : ℝ) ^ 2 := by ring
        _ = 8 * (p : ℝ) * (saving p : ℝ) ^ 2 *
              Real.log (p : ℝ) ^ 2 := by rw [hsqrtSq]
        _ < (p : ℝ) * (saving p : ℝ) *
              (1024 * burgessDyadicShift p) := by
          calc
            8 * (p : ℝ) * (saving p : ℝ) ^ 2 *
                Real.log (p : ℝ) ^ 2 =
                (p : ℝ) * (saving p : ℝ) *
                  (8 * (saving p : ℝ) * Real.log (p : ℝ) ^ 2) := by ring
            _ < _ := hm
        _ = (p : ℝ) *
            burgessDenominatorLossExtra ({p} : Finset ℕ).card
              (saving p) (burgessDyadicShift p) := by
          simp [burgessDenominatorLossExtra]
          push_cast
          ring
    have hsqNat :
        2 * H ^ 2 < p *
          burgessDenominatorLossExtra ({p} : Finset ℕ).card
            (saving p) (burgessDyadicShift p) := by
      exact_mod_cast hsqReal
    exact burgessDenominatorCountExtra_noWrap_of_sq_lt
      ({p} : Finset ℕ).card (saving p) (burgessDyadicShift p) H p
      hJpos hVpos hsqNat
  have hgrowth := hQg p ((Nat.le_max_right 3 Qg).trans hpLarge)
  exact singleton_burgess_bound hp hJpos
    (by omega) hH3 hHp hrelaxed hfit hsmall hloss2' hloss23' hgrowth

/-- Completion handles the intervals beyond the Burgess amplifier range,
leaving a uniform relative saving for every sufficiently long interval. -/
theorem eventually_singleton_interval_bound :
    ∀ᶠ p : ℕ in atTop, ∀ (hp : p.Prime) (H M : ℕ),
      (p : ℝ) ^ ((63 : ℝ) / 128) ≤ H →
      3 ≤ H → H < p →
      |∑ i ∈ Finset.range H,
        quadraticPrimeFactorProduct {p} (M + i)| ≤
          (H : ℝ) / (2 * saving p) := by
  filter_upwards [eventually_singleton_burgess_bound] with p hburgess
  intro hp H M hroot hH3 hHp
  by_cases hupper :
      (H : ℝ) ≤ 2 * Real.sqrt (p : ℝ) * saving p * Real.log (p : ℝ)
  · exact (hburgess hp H M hroot hupper hH3 hHp).trans (by
      have hJ : (0 : ℝ) < saving p := by exact_mod_cast saving_pos p
      apply div_le_div_of_nonneg_left (by positivity) (by positivity)
      nlinarith)
  · have hodd : ∀ r ∈ ({p} : Finset ℕ), r ≠ 2 := by
      intro r hr
      have : r = p := by simpa using hr
      subst r
      omega
    have hcompletion := abs_sum_quadraticPrimeFactorProduct_le_completion_long
      ({p} : Finset ℕ) (by simpa using hp) hodd (by simp) M H
    have hstrict :
        Real.log (p : ℝ) * Real.sqrt (p : ℝ) <
          (H : ℝ) / (2 * saving p) := by
      have hJreal : (0 : ℝ) < saving p := by exact_mod_cast saving_pos p
      apply (lt_div_iff₀ (by positivity : (0 : ℝ) < 2 * saving p)).2
      have := lt_of_not_ge hupper
      nlinarith
    have hcompletion' :
        |∑ i ∈ Finset.range H,
          quadraticPrimeFactorProduct {p} (M + i)| ≤
            Real.log (p : ℝ) * Real.sqrt (p : ℝ) := by
      simpa [primeSetModulus] using hcompletion
    exact hcompletion'.trans hstrict.le

noncomputable def progressionCoefficient (p a : ℕ) : ℝ :=
  ((jacobiSym (2 : ℤ) a * (-1 : ℤ) ^ (p / 2 * (a / 2)) : ℤ) : ℝ)

lemma abs_progressionCoefficient_eq_one {p a : ℕ} (ha : Odd a) :
    |progressionCoefficient p a| = 1 := by
  have hcop : Int.gcd (2 : ℤ) a = 1 := by
    simpa [Int.gcd_eq_natAbs, Nat.coprime_comm] using
      (Nat.coprime_two_right.mpr ha)
  rcases jacobiSym.eq_one_or_neg_one hcop with h | h <;>
    simp [progressionCoefficient, h]

lemma attachedQuadraticCharacter_progression
    {p a i : ℕ} (hp : p.Prime) (hpodd : p ≠ 2)
    (haodd : Odd a) (ha8 : a < 8) :
    ((Erdos1141.attachedQuadraticCharacter (2 * p) (8 * p)
        (by exact ⟨1, by ring⟩) (8 * i + a) : ℤ) : ℝ) =
      progressionCoefficient p a *
        quadraticPrimeFactorProduct {p} (8 * i + a) := by
  let k := 8 * i + a
  have hkodd : Odd k := by
    exact Even.add_odd (by exact ⟨4 * i, by ring⟩) haodd
  have hk8 : k % 8 = a := by
    dsimp [k]
    omega
  have hcop8 : Nat.Coprime k 8 := by
    rw [show 8 = 2 ^ 3 by norm_num, Nat.coprime_pow_right_iff (by omega) k 2]
    exact Nat.coprime_two_right.mpr hkodd
  letI : Fact p.Prime := ⟨hp⟩
  by_cases hcop : Nat.Coprime k (8 * p)
  · have hJ2 : jacobiSym (2 : ℤ) k = jacobiSym (2 : ℤ) a := by
      calc
        jacobiSym (2 : ℤ) k = jacobiSym (2 : ℤ) (k % (4 * 2)) :=
          jacobiSym.mod_right' 2 hkodd
        _ = jacobiSym (2 : ℤ) a := by norm_num [hk8]
    have hkhalf : k / 2 = 4 * i + a / 2 := by
      dsimp [k]
      omega
    have hsign :
        (-1 : ℤ) ^ (p / 2 * (k / 2)) =
          (-1 : ℤ) ^ (p / 2 * (a / 2)) := by
      rw [hkhalf]
      rw [Nat.mul_add, pow_add]
      have heven : Even (p / 2 * (4 * i)) := by
        refine ⟨(p / 2) * (2 * i), ?_⟩
        ring
      rw [Even.neg_one_pow heven, one_mul]
    have hqr := jacobiSym.quadratic_reciprocity (a := p) (b := k)
      (hp.odd_of_ne_two hpodd) hkodd
    have hleg :
        ((jacobiSym (k : ℤ) p : ℤ) : ℝ) =
          quadraticPrimeFactorProduct {p} k := by
      rw [← jacobiSym.legendreSym.to_jacobiSym]
      simp only [quadraticPrimeFactorProduct, Finset.prod_singleton,
        primeQuadraticCharReal_of_prime hp]
      simp [legendreSym, quadraticCharReal]
    rw [Erdos1141.attachedQuadraticCharacter_apply_coprime
      (by exact ⟨1, by ring⟩) hcop]
    change ((jacobiSym ((2 * p : ℕ) : ℤ) k : ℤ) : ℝ) = _
    rw [show ((2 * p : ℕ) : ℤ) = (2 : ℤ) * p by norm_num,
      jacobiSym.mul_left, hJ2, hqr, hsign]
    dsimp [progressionCoefficient]
    rw [← hleg]
    push_cast
    ring
  · have hnotcopp : ¬Nat.Coprime k p := by
      intro hkp
      exact hcop ((Nat.coprime_mul_iff_right).2 ⟨hcop8, hkp⟩)
    have hpdvd : p ∣ k := by
      by_contra hnotdvd
      exact hnotcopp ((hp.coprime_iff_not_dvd.mpr hnotdvd).symm)
    have hkzero : (k : ZMod p) = 0 :=
      (ZMod.natCast_eq_zero_iff k p).2 hpdvd
    rw [Erdos1141.attachedQuadraticCharacter_apply_not_coprime
      (by exact ⟨1, by ring⟩) hcop]
    have hqzero : quadraticPrimeFactorProduct {p} k = 0 := by
      simp [quadraticPrimeFactorProduct, primeQuadraticCharReal, hp,
        quadraticCharReal, hkzero]
    rw [hqzero, mul_zero]
    norm_num

/-- On each of the four odd residue classes modulo eight, the character
attached to `2p` inherits the same uniform Burgess saving as the Legendre
character modulo `p`. -/
theorem eventually_attached_progression_bound :
    ∀ᶠ p : ℕ in atTop, ∀ (hp : p.Prime) (H a : ℕ),
      Odd a → a < 8 →
      (p : ℝ) ^ ((63 : ℝ) / 128) ≤ H →
      3 ≤ H → H < p →
      |∑ i ∈ Finset.range H,
        ((Erdos1141.attachedQuadraticCharacter (2 * p) (8 * p)
          (by exact ⟨1, by ring⟩) (8 * i + a) : ℤ) : ℝ)| ≤
        (H : ℝ) / (2 * saving p) := by
  filter_upwards [eventually_singleton_interval_bound,
    eventually_ge_atTop (3 : ℕ)] with p hinterval hp3
  intro hp H a haodd ha8 hroot hH3 hHp
  letI : Fact p.Prime := ⟨hp⟩
  have hpodd : p ≠ 2 := by omega
  let M : ℕ := (((8 : ZMod p)⁻¹ * (a : ZMod p))).val
  have h8ne : (8 : ZMod p) ≠ 0 := by
    have hcop : Nat.Coprime 8 p := by
      rw [show 8 = 2 ^ 3 by norm_num,
        Nat.coprime_pow_left_iff (by omega) 2 p]
      exact (Nat.coprime_two_right.mpr (hp.odd_of_ne_two (by omega))).symm
    exact ((ZMod.isUnit_iff_coprime 8 p).2 hcop).ne_zero
  have hDM : a ≡ 8 * M [MOD p] := by
    rw [← ZMod.natCast_eq_natCast_iff]
    dsimp [M]
    rw [Nat.cast_mul, ZMod.natCast_zmod_val]
    change (a : ZMod p) = (8 : ZMod p) * ((8 : ZMod p)⁻¹ * (a : ZMod p))
    rw [← mul_assoc, mul_inv_cancel₀ h8ne, one_mul]
  have hDM' : a ≡ 8 * M [MOD primeSetModulus {p}] := by
    simpa [primeSetModulus] using hDM
  have haffine :
      |∑ i ∈ Finset.range H,
        quadraticPrimeFactorProduct {p} (a + 8 * i)| ≤
        (H : ℝ) / (2 * saving p) := by
    exact abs_sum_quadraticPrimeFactorProduct_affine_le
      (s := {p}) (by simpa using hp) hDM'
      (hinterval hp H M hroot hH3 hHp)
  calc
    |∑ i ∈ Finset.range H,
        ((Erdos1141.attachedQuadraticCharacter (2 * p) (8 * p)
          (by exact ⟨1, by ring⟩) (8 * i + a) : ℤ) : ℝ)| =
        |progressionCoefficient p a *
          ∑ i ∈ Finset.range H,
            quadraticPrimeFactorProduct {p} (a + 8 * i)| := by
      congr 1
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      rw [attachedQuadraticCharacter_progression hp hpodd haodd ha8]
      congr 2
      omega
    _ = |∑ i ∈ Finset.range H,
          quadraticPrimeFactorProduct {p} (a + 8 * i)| := by
      rw [abs_mul, abs_progressionCoefficient_eq_one haodd, one_mul]
    _ ≤ (H : ℝ) / (2 * saving p) := haffine

lemma abs_quadraticCharacterMod_cast_le_one
    {m n : ℕ} (χ : Erdos1141.QuadraticCharacterMod m) :
    |((χ n : ℤ) : ℝ)| ≤ 1 := by
  by_cases hcop : Nat.Coprime n m
  · rcases χ.map_coprime hcop with hχ | hχ <;> simp [hχ]
  · simp [χ.map_non_coprime hcop]

lemma attachedQuadraticCharacter_even_zero
    {p n : ℕ} (hn : Even n) :
    Erdos1141.attachedQuadraticCharacter (2 * p) (8 * p)
      (by exact ⟨1, by ring⟩) n = 0 := by
  rw [Erdos1141.attachedQuadraticCharacter_apply_not_coprime]
  intro hcop
  have hcop2 : Nat.Coprime n 2 :=
    hcop.coprime_dvd_right (by omega : 2 ∣ 8 * p)
  rcases hn with ⟨r, hr⟩
  rcases Nat.coprime_two_right.mp hcop2 with ⟨s, hs⟩
  omega

lemma sum_range_eight_mul
    {A : Type*} [AddCommMonoid A] (f : ℕ → A) (H : ℕ) :
    (∑ k ∈ Finset.range (8 * H), f k) =
      ∑ a ∈ Finset.range 8, ∑ i ∈ Finset.range H, f (8 * i + a) := by
  induction H with
  | zero => simp
  | succ H ih =>
      rw [Nat.mul_succ, Finset.sum_range_add, ih]
      have hexpand :
          (∑ a ∈ Finset.range 8,
            ∑ i ∈ Finset.range (H + 1), f (8 * i + a)) =
          ∑ a ∈ Finset.range 8,
            ((∑ i ∈ Finset.range H, f (8 * i + a)) + f (8 * H + a)) := by
        apply Finset.sum_congr rfl
        intro a ha
        rw [Finset.sum_range_succ]
      rw [hexpand, Finset.sum_add_distrib]

/-- A prefix made of complete blocks of eight has a power-saving character
sum once its number of blocks is in the uniform Burgess range. -/
theorem eventually_attached_complete_blocks_bound :
    ∀ᶠ p : ℕ in atTop, ∀ (hp : p.Prime) (H : ℕ),
      (p : ℝ) ^ ((63 : ℝ) / 128) ≤ H →
      3 ≤ H → H < p →
      |∑ k ∈ Finset.range (8 * H),
        ((Erdos1141.attachedQuadraticCharacter (2 * p) (8 * p)
          (by exact ⟨1, by ring⟩) k : ℤ) : ℝ)| ≤
        4 * (H : ℝ) / saving p := by
  filter_upwards [eventually_attached_progression_bound] with p hprogression
  intro hp H hroot hH3 hHp
  let χ := Erdos1141.attachedQuadraticCharacter (2 * p) (8 * p)
    (by exact ⟨1, by ring⟩)
  have hterm : ∀ a ∈ Finset.range 8,
      |∑ i ∈ Finset.range H, ((χ (8 * i + a) : ℤ) : ℝ)| ≤
        (H : ℝ) / (2 * saving p) := by
    intro a ha
    have ha8 : a < 8 := Finset.mem_range.mp ha
    rcases Nat.even_or_odd a with haeven | haodd
    · have hz : ∀ i : ℕ, χ (8 * i + a) = 0 := by
        intro i
        apply attachedQuadraticCharacter_even_zero
        rcases haeven with ⟨b, hb⟩
        exact ⟨4 * i + b, by omega⟩
      simp_rw [hz]
      simp only [Int.cast_zero, Finset.sum_const_zero, abs_zero]
      positivity
    · simpa [χ] using hprogression hp H a haodd ha8 hroot hH3 hHp
  rw [sum_range_eight_mul]
  calc
    |∑ a ∈ Finset.range 8,
        ∑ i ∈ Finset.range H, ((χ (8 * i + a) : ℤ) : ℝ)| ≤
        ∑ a ∈ Finset.range 8,
          |∑ i ∈ Finset.range H, ((χ (8 * i + a) : ℤ) : ℝ)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ a ∈ Finset.range 8, ((H : ℝ) / (2 * saving p)) := by
      exact Finset.sum_le_sum hterm
    _ = 4 * (H : ℝ) / saving p := by
      have hJpos : (0 : ℝ) < saving p := by exact_mod_cast saving_pos p
      have hJ : (saving p : ℝ) ≠ 0 := ne_of_gt hJpos
      simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      field_simp
      ring

/-- The incomplete final block costs at most eight, so every sufficiently
long prefix inherits the complete-block saving. -/
theorem eventually_attached_prefix_bound :
    ∀ᶠ p : ℕ in atTop, ∀ (hp : p.Prime) (N : ℕ),
      (p : ℝ) ^ ((63 : ℝ) / 128) ≤ ((N / 8 : ℕ) : ℝ) →
      3 ≤ N / 8 → N / 8 < p →
      |∑ k ∈ Finset.range N,
        ((Erdos1141.attachedQuadraticCharacter (2 * p) (8 * p)
          (by exact ⟨1, by ring⟩) k : ℤ) : ℝ)| ≤
        4 * ((N / 8 : ℕ) : ℝ) / saving p + 8 := by
  filter_upwards [eventually_attached_complete_blocks_bound] with p hblocks
  intro hp N hroot hH3 hHp
  let χ := Erdos1141.attachedQuadraticCharacter (2 * p) (8 * p)
    (by exact ⟨1, by ring⟩)
  let H := N / 8
  let R := N % 8
  have hN : N = 8 * H + R := by
    dsimp [H, R]
    omega
  have hR : R < 8 := by
    dsimp [R]
    omega
  have hsplit :
      (∑ k ∈ Finset.range N, ((χ k : ℤ) : ℝ)) =
        (∑ k ∈ Finset.range (8 * H), ((χ k : ℤ) : ℝ)) +
          ∑ i ∈ Finset.range R, ((χ (8 * H + i) : ℤ) : ℝ) := by
    conv_lhs => rw [hN, Finset.sum_range_add]
  have hrem :
      |∑ i ∈ Finset.range R, ((χ (8 * H + i) : ℤ) : ℝ)| ≤ 8 := by
    calc
      |∑ i ∈ Finset.range R, ((χ (8 * H + i) : ℤ) : ℝ)| ≤
          ∑ i ∈ Finset.range R, |((χ (8 * H + i) : ℤ) : ℝ)| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _i ∈ Finset.range R, (1 : ℝ) := by
        apply Finset.sum_le_sum
        intro i hi
        exact abs_quadraticCharacterMod_cast_le_one χ
      _ = (R : ℝ) := by simp
      _ ≤ 8 := by exact_mod_cast hR.le
  rw [hsplit]
  calc
    |(∑ k ∈ Finset.range (8 * H), ((χ k : ℤ) : ℝ)) +
        ∑ i ∈ Finset.range R, ((χ (8 * H + i) : ℤ) : ℝ)| ≤
        |∑ k ∈ Finset.range (8 * H), ((χ k : ℤ) : ℝ)| +
          |∑ i ∈ Finset.range R, ((χ (8 * H + i) : ℤ) : ℝ)| :=
      abs_add_le _ _
    _ ≤ 4 * (H : ℝ) / saving p + 8 := by
      exact add_le_add (by simpa [χ, H] using hblocks hp H hroot hH3 hHp) hrem
    _ = 4 * ((N / 8 : ℕ) : ℝ) / saving p + 8 := by rfl

noncomputable def prefixError (p : ℕ) : ℝ :=
  32 + 8 * (p : ℝ) ^ ((63 : ℝ) / 128)

/-- A single bound valid both below and above the Burgess threshold.  Below
the threshold it uses the termwise bound; above it uses the preceding prefix
estimate. -/
theorem eventually_attached_prefix_uniform :
    ∀ᶠ p : ℕ in atTop, ∀ (hp : p.Prime) (N : ℕ), N ≤ p →
      |∑ k ∈ Finset.range N,
        ((Erdos1141.attachedQuadraticCharacter (2 * p) (8 * p)
          (by exact ⟨1, by ring⟩) k : ℤ) : ℝ)| ≤
        4 * (N : ℝ) / saving p + prefixError p := by
  have hpowa : ∀ᶠ p : ℕ in atTop,
      (3 : ℝ) ≤ (p : ℝ) ^ ((63 : ℝ) / 128) := by
    have ht := (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < (63 : ℝ) / 128)).comp
      (tendsto_natCast_atTop_atTop (R := ℝ))
    exact ht.eventually (eventually_ge_atTop 3)
  filter_upwards [eventually_attached_prefix_bound, hpowa] with p hprefix hpow3
  intro hp N hNp
  let χ := Erdos1141.attachedQuadraticCharacter (2 * p) (8 * p)
    (by exact ⟨1, by ring⟩)
  by_cases hroot :
      (p : ℝ) ^ ((63 : ℝ) / 128) ≤ ((N / 8 : ℕ) : ℝ)
  · have hH3 : 3 ≤ N / 8 := by
      by_contra hnot
      have hsmall : N / 8 ≤ 2 := by omega
      have hsmall' : ((N / 8 : ℕ) : ℝ) < 3 := by exact_mod_cast (show N / 8 < 3 by omega)
      linarith
    have hHp : N / 8 < p := by
      by_cases hN0 : N = 0
      · omega
      · exact (Nat.div_lt_self (Nat.pos_of_ne_zero hN0) (by omega)).trans_le hNp
    have hsaved := hprefix hp N hroot hH3 hHp
    calc
      |∑ k ∈ Finset.range N, ((χ k : ℤ) : ℝ)| ≤
          4 * ((N / 8 : ℕ) : ℝ) / saving p + 8 := by simpa [χ] using hsaved
      _ ≤ 4 * (N : ℝ) / saving p + prefixError p := by
        have hJ : (0 : ℝ) < saving p := by exact_mod_cast saving_pos p
        have hdiv : ((N / 8 : ℕ) : ℝ) ≤ N := by
          exact_mod_cast Nat.div_le_self N 8
        dsimp [prefixError]
        have hratio :
            4 * ((N / 8 : ℕ) : ℝ) / saving p ≤
              4 * (N : ℝ) / saving p := by
          exact div_le_div_of_nonneg_right (by gcongr) hJ.le
        have hpow : 0 ≤ (p : ℝ) ^ ((63 : ℝ) / 128) := by positivity
        linarith
  · have htrivial :
        |∑ k ∈ Finset.range N, ((χ k : ℤ) : ℝ)| ≤ (N : ℝ) := by
      calc
        |∑ k ∈ Finset.range N, ((χ k : ℤ) : ℝ)| ≤
            ∑ k ∈ Finset.range N, |((χ k : ℤ) : ℝ)| :=
          Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ _k ∈ Finset.range N, (1 : ℝ) := by
          apply Finset.sum_le_sum
          intro k hk
          exact abs_quadraticCharacterMod_cast_le_one χ
        _ = (N : ℝ) := by simp
    have hNsmall : (N : ℝ) ≤ prefixError p := by
      have hdecomp : N ≤ 8 * (N / 8) + 7 := by omega
      have hfloor : ((N / 8 : ℕ) : ℝ) <
          (p : ℝ) ^ ((63 : ℝ) / 128) := lt_of_not_ge hroot
      have hcast : (N : ℝ) ≤ 8 * ((N / 8 : ℕ) : ℝ) + 7 := by
        exact_mod_cast hdecomp
      dsimp [prefixError]
      nlinarith
    exact htrivial.trans (by
      have hJ : (0 : ℝ) < saving p := by exact_mod_cast saving_pos p
      have hnonneg : 0 ≤ 4 * (N : ℝ) / saving p := by positivity
      linarith)

lemma sum_range_natCast_mul_eq
    (c : ℕ → ℝ) (N : ℕ) :
    (∑ n ∈ Finset.range N, (n : ℝ) * c n) =
      (N : ℝ) * (∑ n ∈ Finset.range N, c n) -
        ∑ k ∈ Finset.range N, ∑ n ∈ Finset.range (k + 1), c n := by
  induction N with
  | zero => simp
  | succ N ih =>
      rw [Finset.sum_range_succ, Finset.sum_range_succ,
        Finset.sum_range_succ, ih]
      have hlast : (∑ n ∈ Finset.range (N + 1), c n) =
          (∑ n ∈ Finset.range N, c n) + c N :=
        Finset.sum_range_succ c N
      rw [hlast]
      push_cast
      ring

/-- Summation by parts converts the uniform unweighted prefix estimate into
a weighted-prefix estimate. -/
theorem eventually_attached_weighted_prefix :
    ∀ᶠ p : ℕ in atTop, ∀ (hp : p.Prime) (y : ℕ), y + 1 < p → 0 < y →
      |∑ n ∈ Finset.Icc 1 y,
        (n : ℝ) *
          ((Erdos1141.attachedQuadraticCharacter (2 * p) (8 * p)
            (by exact ⟨1, by ring⟩) n : ℤ) : ℝ)| ≤
        8 * (y + 1 : ℕ) ^ 2 / saving p +
          2 * prefixError p * (y + 1 : ℕ) := by
  filter_upwards [eventually_attached_prefix_uniform] with p huniform
  intro hp y hyp hy
  let χ := Erdos1141.attachedQuadraticCharacter (2 * p) (8 * p)
    (by exact ⟨1, by ring⟩)
  let A : ℕ → ℝ := fun N ↦ ∑ n ∈ Finset.range N, ((χ n : ℤ) : ℝ)
  have hA : ∀ N ≤ y + 1,
      |A N| ≤ 4 * (N : ℝ) / saving p + prefixError p := by
    intro N hN
    apply huniform hp N
    exact hN.trans (Nat.le_of_lt hyp)
  have hrewrite :
      (∑ n ∈ Finset.Icc 1 y, (n : ℝ) * ((χ n : ℤ) : ℝ)) =
        (∑ n ∈ Finset.range (y + 1), (n : ℝ) * ((χ n : ℤ) : ℝ)) := by
    calc
      (∑ n ∈ Finset.Icc 1 y, (n : ℝ) * ((χ n : ℤ) : ℝ)) =
          ∑ n ∈ Finset.Ioc 0 y, (n : ℝ) * ((χ n : ℤ) : ℝ) := by
        rw [← Finset.Icc_add_one_left_eq_Ioc]
        norm_num
      _ = ∑ n ∈ Finset.Icc 0 y, (n : ℝ) * ((χ n : ℤ) : ℝ) := by
        rw [Finset.Icc_eq_cons_Ioc (by omega : 0 ≤ y), Finset.sum_cons]
        simp
      _ = ∑ n ∈ Finset.range (y + 1),
          (n : ℝ) * ((χ n : ℤ) : ℝ) := by
        rw [Nat.range_succ_eq_Icc_zero]
  rw [hrewrite, sum_range_natCast_mul_eq]
  have hsumA :
      |∑ k ∈ Finset.range (y + 1), A (k + 1)| ≤
        (y + 1 : ℕ) *
          (4 * ((y + 1 : ℕ) : ℝ) / saving p + prefixError p) := by
    calc
      |∑ k ∈ Finset.range (y + 1), A (k + 1)| ≤
          ∑ k ∈ Finset.range (y + 1), |A (k + 1)| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _k ∈ Finset.range (y + 1),
          (4 * ((y + 1 : ℕ) : ℝ) / saving p + prefixError p) := by
        apply Finset.sum_le_sum
        intro k hk
        have hklt := Finset.mem_range.mp hk
        have hk' : k + 1 ≤ y + 1 := by omega
        exact (hA (k + 1) hk').trans (by
          have hJ : (0 : ℝ) < saving p := by exact_mod_cast saving_pos p
          have hcast : ((k + 1 : ℕ) : ℝ) ≤ (y + 1 : ℕ) := by exact_mod_cast hk'
          gcongr)
      _ = (y + 1 : ℕ) *
          (4 * ((y + 1 : ℕ) : ℝ) / saving p + prefixError p) := by
        simp
        ring
  change
    |((y + 1 : ℕ) : ℝ) * A (y + 1) -
      ∑ k ∈ Finset.range (y + 1), A (k + 1)| ≤ _
  calc
    |((y + 1 : ℕ) : ℝ) * A (y + 1) -
        ∑ k ∈ Finset.range (y + 1), A (k + 1)| ≤
        ((y + 1 : ℕ) : ℝ) * |A (y + 1)| +
          |∑ k ∈ Finset.range (y + 1), A (k + 1)| := by
      calc
        |((y + 1 : ℕ) : ℝ) * A (y + 1) -
            ∑ k ∈ Finset.range (y + 1), A (k + 1)| =
            |((y + 1 : ℕ) : ℝ) * A (y + 1) +
              -(∑ k ∈ Finset.range (y + 1), A (k + 1))| := by ring
        _ ≤ |((y + 1 : ℕ) : ℝ) * A (y + 1)| +
            |-(∑ k ∈ Finset.range (y + 1), A (k + 1))| := abs_add_le _ _
        _ = ((y + 1 : ℕ) : ℝ) * |A (y + 1)| +
            |∑ k ∈ Finset.range (y + 1), A (k + 1)| := by
          rw [abs_mul, abs_of_nonneg (by positivity), abs_neg]
    _ ≤ ((y + 1 : ℕ) : ℝ) *
          (4 * ((y + 1 : ℕ) : ℝ) / saving p + prefixError p) +
        ((y + 1 : ℕ) : ℝ) *
          (4 * ((y + 1 : ℕ) : ℝ) / saving p + prefixError p) := by
      gcongr
      exact hA (y + 1) le_rfl
    _ = 8 * (y + 1 : ℕ) ^ 2 / saving p +
          2 * prefixError p * (y + 1 : ℕ) := by
      push_cast
      ring

theorem eventually_attached_complex_weighted_prefix :
    ∀ᶠ p : ℕ in atTop, ∀ (hp : p.Prime) (y : ℕ), y + 1 < p → 0 < y →
      let χ₀ := Erdos1141.attachedQuadraticCharacter (2 * p) (8 * p)
        (by exact ⟨1, by ring⟩)
      letI : NeZero (8 * p) := ⟨mul_ne_zero (by norm_num) hp.ne_zero⟩
      let χ := χ₀.toDirichletCharacterComplex
      ‖∑ n ∈ Finset.Icc 1 y, (n : ℂ) * χ (n : ZMod (8 * p))‖ ≤
        8 * (y + 1 : ℕ) ^ 2 / saving p +
          2 * prefixError p * (y + 1 : ℕ) := by
  filter_upwards [eventually_attached_weighted_prefix] with p hweighted
  intro hp y hyp hy
  let χ₀ := Erdos1141.attachedQuadraticCharacter (2 * p) (8 * p)
    (by exact ⟨1, by ring⟩)
  letI : NeZero (8 * p) := ⟨mul_ne_zero (by norm_num) hp.ne_zero⟩
  let χ := χ₀.toDirichletCharacterComplex
  have hreal := hweighted hp y hyp hy
  have heq :
      (∑ n ∈ Finset.Icc 1 y, (n : ℂ) * χ (n : ZMod (8 * p))) =
        ((∑ n ∈ Finset.Icc 1 y,
          (n : ℝ) * ((χ₀ n : ℤ) : ℝ) : ℝ) : ℂ) := by
    rw [Complex.ofReal_sum]
    apply Finset.sum_congr rfl
    intro n hn
    rw [Erdos1141.QuadraticCharacterMod.toDirichletCharacterComplex_apply_nat]
    push_cast
    rfl
  change ‖∑ n ∈ Finset.Icc 1 y,
      (n : ℂ) * χ (n : ZMod (8 * p))‖ ≤ _
  rw [heq, Complex.norm_real, Real.norm_eq_abs]
  simpa [χ₀] using hreal

private lemma quadraticEulerCutoff_le_local (X : ℕ) (t : ℝ) :
    quadraticEulerCutoff X t ≤ X := by
  by_cases ht : t = 0 <;> simp [quadraticEulerCutoff, ht]

private lemma cast_quadraticEulerCutoff_le_div_local
    {X : ℕ} {t : ℝ} (ht : 0 < t) :
    (quadraticEulerCutoff X t : ℝ) ≤ (X : ℝ) / t := by
  rw [quadraticEulerCutoff, if_neg ht.ne']
  have hfloor : (min X ⌊(X : ℝ) / t⌋₊ : ℕ) ≤ ⌊(X : ℝ) / t⌋₊ :=
    min_le_right _ _
  have hfloor_le : (⌊(X : ℝ) / t⌋₊ : ℝ) ≤ (X : ℝ) / t :=
    Nat.floor_le (div_nonneg (by positivity) ht.le)
  exact (by exact_mod_cast hfloor :
    ((min X ⌊(X : ℝ) / t⌋₊ : ℕ) : ℝ) ≤ (⌊(X : ℝ) / t⌋₊ : ℝ)).trans hfloor_le

private lemma measurable_quadraticEulerCutoff_local (X : ℕ) :
    Measurable (quadraticEulerCutoff X) := by
  unfold quadraticEulerCutoff
  have hzero : MeasurableSet ({(0 : ℝ)} : Set ℝ) := measurableSet_singleton (0 : ℝ)
  apply Measurable.ite (by simpa only [Set.setOf_eq_eq_singleton] using hzero)
    measurable_const
  have hdiv : Measurable (fun t : ℝ ↦ (X : ℝ) / t) :=
    measurable_const.div measurable_id
  exact (measurable_of_countable (fun y : ℕ ↦ min X y)).comp hdiv.nat_floor

private lemma integrableOn_quadraticSwappedIntegrand_local
    {q X : ℕ} [NeZero q] (hq : 1 < q)
    (chi : DirichletCharacter ℂ q) (hchi : chi ≠ 1) :
    IntegrableOn
      (fun t : ℝ ↦ ((Int.fract t : ℝ) : ℂ) *
        ∑ a ∈ Finset.Icc 1 (quadraticEulerCutoff X t),
          (a : ℂ) * chi (a : ZMod q))
      (Set.Ioc 0 (X : ℝ)) := by
  let charPrefix : ℕ → ℂ := fun y ↦
    ∑ a ∈ Finset.Icc 1 y, (a : ℂ) * chi (a : ZMod q)
  let F : ℝ → ℂ := fun t ↦ ((Int.fract t : ℝ) : ℂ) *
    charPrefix (quadraticEulerCutoff X t)
  have hprefixMeas : Measurable (fun t ↦
      charPrefix (quadraticEulerCutoff X t)) :=
    (measurable_of_countable charPrefix).comp
      (measurable_quadraticEulerCutoff_local X)
  have hFMeas : Measurable F :=
    (Complex.continuous_ofReal.measurable.comp measurable_fract).mul hprefixMeas
  apply IntegrableOn.of_bound measure_Ioc_lt_top hFMeas.aestronglyMeasurable
    (4 * (X : ℝ) * Real.sqrt (q : ℝ) * Real.log (q : ℝ))
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
  change ‖((Int.fract t : ℝ) : ℂ) *
      charPrefix (quadraticEulerCutoff X t)‖ ≤ _
  rw [norm_mul]
  have hfract : ‖((Int.fract t : ℝ) : ℂ)‖ ≤ 1 := by
    rw [Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Int.fract_nonneg t)]
    exact (Int.fract_lt_one t).le
  have hprefix := norm_dirichletCharacterWeightedPrefixSum_le
    hq chi hchi (quadraticEulerCutoff X t)
  change ‖charPrefix (quadraticEulerCutoff X t)‖ ≤ _ at hprefix
  have hlog : 0 ≤ Real.log (q : ℝ) :=
    (Real.log_pos (by exact_mod_cast hq)).le
  have hscale : 0 ≤ Real.sqrt (q : ℝ) * Real.log (q : ℝ) :=
    mul_nonneg (Real.sqrt_nonneg _) hlog
  have hcut : (quadraticEulerCutoff X t : ℝ) ≤ (X : ℝ) := by
    exact_mod_cast quadraticEulerCutoff_le_local X t
  calc
    ‖((Int.fract t : ℝ) : ℂ)‖ *
        ‖charPrefix (quadraticEulerCutoff X t)‖ ≤
        1 * (4 * (quadraticEulerCutoff X t : ℝ) *
          Real.sqrt (q : ℝ) * Real.log (q : ℝ)) :=
      mul_le_mul hfract hprefix (norm_nonneg _) zero_le_one
    _ ≤ 4 * (X : ℝ) * Real.sqrt (q : ℝ) * Real.log (q : ℝ) := by
      nlinarith

private lemma integral_Ioc_inv_sq_local
    {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    (∫ t : ℝ in Ioc a b, (t ^ 2)⁻¹) = a⁻¹ - b⁻¹ := by
  have hdiff : ∀ t ∈ Set.uIcc a b,
      DifferentiableAt ℝ (fun u : ℝ ↦ u⁻¹) t := by
    intro t ht
    apply differentiableAt_inv
    have ht' : t ∈ Icc a b := by simpa [Set.uIcc_of_le hab] using ht
    exact (ha.trans_le ht'.1).ne'
  have hint : IntervalIntegrable
      (deriv (fun u : ℝ ↦ u⁻¹)) volume a b := by
    rw [show deriv (fun u : ℝ ↦ u⁻¹) = fun u ↦ -(u ^ 2)⁻¹ by
      funext u
      exact deriv_inv]
    apply ContinuousOn.intervalIntegrable
    apply ContinuousOn.neg
    apply ContinuousOn.inv₀
    · exact continuousOn_id.pow 2
    · intro t ht
      have ht' : t ∈ Icc a b := by simpa [Set.uIcc_of_le hab] using ht
      exact pow_ne_zero 2 (ha.trans_le ht'.1).ne'
  have hfund := intervalIntegral.integral_deriv_eq_sub hdiff hint
  rw [intervalIntegral.integral_of_le hab] at hfund
  rw [show deriv (fun u : ℝ ↦ u⁻¹) = fun u ↦ -(u ^ 2)⁻¹ by
    funext u
    exact deriv_inv] at hfund
  rw [integral_neg] at hfund
  linarith

private lemma hasDerivAt_complexOfReal_inv_local {t : ℝ} (ht : t ≠ 0) :
    HasDerivAt (fun u : ℝ ↦ ((u : ℂ)⁻¹)) (-((t : ℂ) ^ 2)⁻¹) t := by
  have hcomplex : HasDerivAt (fun z : ℂ ↦ z⁻¹)
      (-((t : ℂ) ^ 2)⁻¹) (t : ℂ) := hasDerivAt_inv (by exact_mod_cast ht)
  exact hcomplex.comp_ofReal

private lemma integrableOn_deriv_complexOfReal_inv_local
    {a b : ℝ} (ha : 0 < a) :
    IntegrableOn (deriv (fun u : ℝ ↦ ((u : ℂ)⁻¹))) (Icc a b) := by
  let g : ℝ → ℂ := fun t ↦ -((t : ℂ) ^ 2)⁻¹
  have hgContinuous : ContinuousOn g (Icc a b) := by
    apply ContinuousOn.neg
    apply ContinuousOn.inv₀
    · exact Complex.continuous_ofReal.continuousOn.pow 2
    · intro t ht
      exact pow_ne_zero 2 (by exact_mod_cast (ha.trans_le ht.1).ne')
  apply hgContinuous.integrableOn_Icc.congr_fun _ measurableSet_Icc
  intro t ht
  exact (hasDerivAt_complexOfReal_inv_local (ha.trans_le ht.1).ne').deriv.symm

/-- Abel summation with the Burgess prefix estimate controls the finite
reciprocal interval between the smoothing cutoff and one full prime period. -/
theorem eventually_attached_reciprocal_interval :
    ∀ᶠ p : ℕ in atTop, ∀ (hp : p.Prime) (x y : ℕ),
      0 < x → x ≤ y → y < p →
      let χ₀ := Erdos1141.attachedQuadraticCharacter (2 * p) (8 * p)
        (by exact ⟨1, by ring⟩)
      letI : NeZero (8 * p) := ⟨mul_ne_zero (by norm_num) hp.ne_zero⟩
      let χ := χ₀.toDirichletCharacterComplex
      ‖∑ n ∈ Finset.Ioc x y, χ (n : ZMod (8 * p)) / (n : ℂ)‖ ≤
        16 * (1 + Real.log (p : ℝ)) / saving p +
          2 * prefixError p / x := by
  filter_upwards [eventually_attached_prefix_uniform] with p huniform
  intro hp x y hx hxy hyp
  let χ₀ := Erdos1141.attachedQuadraticCharacter (2 * p) (8 * p)
    (by exact ⟨1, by ring⟩)
  letI : NeZero (8 * p) := ⟨mul_ne_zero (by norm_num) hp.ne_zero⟩
  let χ := χ₀.toDirichletCharacterComplex
  change ‖∑ n ∈ Finset.Ioc x y, χ (n : ZMod (8 * p)) / (n : ℂ)‖ ≤ _
  let A : ℝ → ℂ := fun t ↦
    ∑ n ∈ Finset.Icc 0 ⌊t⌋₊, χ (n : ZMod (8 * p))
  have hA : ∀ t ∈ Set.Icc (x : ℝ) y,
      ‖A t‖ ≤ 8 * t / saving p + prefixError p := by
    intro t ht
    have ht0 : 0 ≤ t := (by exact_mod_cast hx.le : (0 : ℝ) ≤ x).trans ht.1
    have hfloor : (⌊t⌋₊ : ℝ) ≤ t := Nat.floor_le ht0
    have hfloorY : ⌊t⌋₊ ≤ y := by
      exact_mod_cast hfloor.trans ht.2
    have hNp : ⌊t⌋₊ + 1 ≤ p := by omega
    have hreal := huniform hp (⌊t⌋₊ + 1) hNp
    have heq : A t =
        ((∑ n ∈ Finset.range (⌊t⌋₊ + 1),
          ((χ₀ n : ℤ) : ℝ) : ℝ) : ℂ) := by
      dsimp [A]
      rw [Nat.range_succ_eq_Icc_zero]
      rw [Complex.ofReal_sum]
      apply Finset.sum_congr rfl
      intro n hn
      rw [Erdos1141.QuadraticCharacterMod.toDirichletCharacterComplex_apply_nat]
      push_cast
      rfl
    have ht1 : (1 : ℝ) ≤ t := (by exact_mod_cast hx : (1 : ℝ) ≤ x).trans ht.1
    have hfloorOne : ((⌊t⌋₊ + 1 : ℕ) : ℝ) ≤ 2 * t := by
      push_cast
      linarith
    rw [heq, Complex.norm_real, Real.norm_eq_abs]
    calc
      |∑ n ∈ Finset.range (⌊t⌋₊ + 1), ((χ₀ n : ℤ) : ℝ)| ≤
          4 * ((⌊t⌋₊ + 1 : ℕ) : ℝ) / saving p + prefixError p := by
        simpa [χ₀] using hreal
      _ ≤ 8 * t / saving p + prefixError p := by
        have hJ : (0 : ℝ) < saving p := by exact_mod_cast saving_pos p
        have hnum : 4 * ((⌊t⌋₊ + 1 : ℕ) : ℝ) ≤ 8 * t := by nlinarith
        have hfrac := div_le_div_of_nonneg_right hnum hJ.le
        linarith
  have hxReal : (0 : ℝ) < x := by exact_mod_cast hx
  have hxyReal : (x : ℝ) ≤ y := by exact_mod_cast hxy
  have hyReal : (0 : ℝ) < y := hxReal.trans_le hxyReal
  have hfDiff : ∀ t ∈ Icc (x : ℝ) y,
      DifferentiableAt ℝ (fun u : ℝ ↦ ((u : ℂ)⁻¹)) t := by
    intro t ht
    exact (hasDerivAt_complexOfReal_inv_local
      (hxReal.trans_le ht.1).ne').differentiableAt
  have hfInt : IntegrableOn
      (deriv (fun u : ℝ ↦ ((u : ℂ)⁻¹))) (Icc (x : ℝ) y) :=
    integrableOn_deriv_complexOfReal_inv_local hxReal
  have habel := sum_mul_eq_sub_sub_integral_mul'
    (f := fun t : ℝ ↦ ((t : ℂ)⁻¹))
    (c := fun n : ℕ ↦ χ (n : ZMod (8 * p))) hxy hfDiff hfInt
  have hrepresentation :
      (∑ n ∈ Finset.Ioc x y, χ (n : ZMod (8 * p)) / (n : ℂ)) =
        ((y : ℂ)⁻¹ * A y - (x : ℂ)⁻¹ * A x) -
          ∫ t in Ioc (x : ℝ) y,
            deriv (fun u : ℝ ↦ ((u : ℂ)⁻¹)) t * A t := by
    simpa [A, div_eq_mul_inv, mul_comm] using habel
  have hActual : IntegrableOn
      (fun t : ℝ ↦ deriv (fun u : ℝ ↦ ((u : ℂ)⁻¹)) t * A t)
      (Ioc (x : ℝ) y) := by
    apply (integrableOn_mul_sum_Icc
      (fun n : ℕ ↦ χ (n : ZMod (8 * p))) hxReal.le hfInt).mono_set
    exact Ioc_subset_Icc_self
  have hInvSq : ContinuousOn (fun t : ℝ ↦ (t ^ 2)⁻¹) (Icc (x : ℝ) y) := by
    apply ContinuousOn.inv₀ (continuousOn_id.pow 2)
    intro t ht
    exact pow_ne_zero 2 (hxReal.trans_le ht.1).ne'
  have hInv : ContinuousOn (fun t : ℝ ↦ t⁻¹) (Icc (x : ℝ) y) := by
    apply ContinuousOn.inv₀ continuousOn_id
    intro t ht
    exact (hxReal.trans_le ht.1).ne'
  have hMajorant : IntegrableOn
      (fun t : ℝ ↦ (8 / saving p) * t⁻¹ + prefixError p * (t ^ 2)⁻¹)
      (Ioc (x : ℝ) y) := by
    exact (((hInv.const_mul (8 / (saving p : ℝ))).add
      (hInvSq.const_mul (prefixError p))).integrableOn_Icc).mono_set
        Ioc_subset_Icc_self
  have hPoint : ∀ t ∈ Ioc (x : ℝ) y,
      ‖deriv (fun u : ℝ ↦ ((u : ℂ)⁻¹)) t * A t‖ ≤
        (8 / saving p) * t⁻¹ + prefixError p * (t ^ 2)⁻¹ := by
    intro t ht
    have htPos : 0 < t := hxReal.trans ht.1
    rw [(hasDerivAt_complexOfReal_inv_local htPos.ne').deriv, norm_mul]
    have hderiv : ‖-((t : ℂ) ^ 2)⁻¹‖ = (t ^ 2)⁻¹ := by
      rw [norm_neg, norm_inv, norm_pow, Complex.norm_real,
        Real.norm_eq_abs, abs_of_pos htPos]
    rw [hderiv]
    have hAt := hA t ⟨ht.1.le, ht.2⟩
    have htInv : 0 ≤ t⁻¹ := inv_nonneg.mpr htPos.le
    calc
      (t ^ 2)⁻¹ * ‖A t‖ ≤
          (t ^ 2)⁻¹ * (8 * t / saving p + prefixError p) :=
        mul_le_mul_of_nonneg_left hAt (inv_nonneg.mpr (sq_nonneg t))
      _ = (8 / saving p) * t⁻¹ + prefixError p * (t ^ 2)⁻¹ := by
        field_simp [htPos.ne']
  have hIntegral :
      ‖∫ t in Ioc (x : ℝ) y,
          deriv (fun u : ℝ ↦ ((u : ℂ)⁻¹)) t * A t‖ ≤
        (8 / saving p) * (Real.log (y : ℝ) - Real.log (x : ℝ)) +
          prefixError p * ((x : ℝ)⁻¹ - (y : ℝ)⁻¹) := by
    calc
      ‖∫ t in Ioc (x : ℝ) y,
          deriv (fun u : ℝ ↦ ((u : ℂ)⁻¹)) t * A t‖ ≤
          ∫ t in Ioc (x : ℝ) y,
            ‖deriv (fun u : ℝ ↦ ((u : ℂ)⁻¹)) t * A t‖ :=
        norm_integral_le_integral_norm _
      _ ≤ ∫ t in Ioc (x : ℝ) y,
          ((8 / saving p) * t⁻¹ + prefixError p * (t ^ 2)⁻¹) := by
        apply setIntegral_mono_ae_restrict hActual.norm hMajorant
        filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
        exact hPoint t ht
      _ = (8 / saving p) * (Real.log (y : ℝ) - Real.log (x : ℝ)) +
          prefixError p * ((x : ℝ)⁻¹ - (y : ℝ)⁻¹) := by
        rw [integral_add]
        · rw [integral_const_mul, integral_const_mul,
            integral_Ioc_inv_sq_local hxReal hxyReal]
          rw [← intervalIntegral.integral_of_le hxyReal,
            integral_inv_of_pos hxReal hyReal]
          rw [Real.log_div hyReal.ne' hxReal.ne']
        · exact (hInv.const_mul (8 / (saving p : ℝ))).integrableOn_Icc.mono_set
            Ioc_subset_Icc_self
        · exact (hInvSq.const_mul (prefixError p)).integrableOn_Icc.mono_set
            Ioc_subset_Icc_self
  have hEndpoint (z : ℕ) (hzx : x ≤ z) (hzy : z ≤ y) :
      ‖(z : ℂ)⁻¹ * A z‖ ≤ 8 / saving p + prefixError p / z := by
    rw [norm_mul, norm_inv, Complex.norm_natCast]
    have hAz := hA z ⟨(by exact_mod_cast hzx), (by exact_mod_cast hzy)⟩
    have hzReal : (0 : ℝ) < z := by exact_mod_cast hx.trans_le hzx
    calc
      (z : ℝ)⁻¹ * ‖A z‖ ≤
          (z : ℝ)⁻¹ * (8 * (z : ℝ) / saving p + prefixError p) :=
        mul_le_mul_of_nonneg_left hAz (inv_nonneg.mpr hzReal.le)
      _ = 8 / saving p + prefixError p / z := by
        field_simp [hzReal.ne']
  have hEx := hEndpoint x le_rfl hxy
  have hEy := hEndpoint y hxy le_rfl
  rw [hrepresentation]
  have hlogx : 0 ≤ Real.log (x : ℝ) :=
    Real.log_nonneg (by exact_mod_cast hx : (1 : ℝ) ≤ x)
  have hlogyp : Real.log (y : ℝ) ≤ Real.log (p : ℝ) :=
    Real.strictMonoOn_log.monotoneOn (by exact_mod_cast (Nat.pos_of_ne_zero (by omega)) : (0 : ℝ) < y)
      (by exact_mod_cast hp.pos : (0 : ℝ) < p) (by exact_mod_cast hyp.le)
  have hJ : (0 : ℝ) < saving p := by exact_mod_cast saving_pos p
  have hD : 0 ≤ prefixError p := by dsimp [prefixError]; positivity
  have hxInv : 0 ≤ (x : ℝ)⁻¹ := inv_nonneg.mpr hxReal.le
  have hyInv : 0 ≤ (y : ℝ)⁻¹ := inv_nonneg.mpr hyReal.le
  calc
    ‖((y : ℂ)⁻¹ * A y - (x : ℂ)⁻¹ * A x) -
        ∫ t in Ioc (x : ℝ) y,
          deriv (fun u : ℝ ↦ ((u : ℂ)⁻¹)) t * A t‖ ≤
        (‖(y : ℂ)⁻¹ * A y‖ + ‖(x : ℂ)⁻¹ * A x‖) +
          ‖∫ t in Ioc (x : ℝ) y,
            deriv (fun u : ℝ ↦ ((u : ℂ)⁻¹)) t * A t‖ := by
      exact (norm_sub_le _ _).trans (add_le_add (norm_sub_le _ _) le_rfl)
    _ ≤ (8 / saving p + prefixError p / y) +
          (8 / saving p + prefixError p / x) +
          ((8 / saving p) * (Real.log (y : ℝ) - Real.log (x : ℝ)) +
            prefixError p * ((x : ℝ)⁻¹ - (y : ℝ)⁻¹)) :=
      add_le_add (add_le_add hEy hEx) hIntegral
    _ ≤ 16 * (1 + Real.log (p : ℝ)) / saving p +
          2 * prefixError p / x := by
      rw [div_eq_mul_inv (prefixError p) (y : ℝ),
        div_eq_mul_inv (prefixError p) (x : ℝ)]
      have hlogp : 0 ≤ Real.log (p : ℝ) := Real.log_nonneg (by exact_mod_cast hp.one_le)
      have hlogdiff : Real.log (y : ℝ) - Real.log (x : ℝ) ≤
          2 * Real.log (p : ℝ) := by linarith
      have hlogterm :
          (8 / (saving p : ℝ)) *
              (Real.log (y : ℝ) - Real.log (x : ℝ)) ≤
            (16 / (saving p : ℝ)) * Real.log (p : ℝ) := by
        calc
          (8 / (saving p : ℝ)) *
              (Real.log (y : ℝ) - Real.log (x : ℝ)) ≤
              (8 / (saving p : ℝ)) * (2 * Real.log (p : ℝ)) :=
            mul_le_mul_of_nonneg_left hlogdiff (by positivity)
          _ = (16 / (saving p : ℝ)) * Real.log (p : ℝ) := by ring
      calc
        (8 / saving p + prefixError p * (y : ℝ)⁻¹) +
            (8 / saving p + prefixError p * (x : ℝ)⁻¹) +
            ((8 / saving p) * (Real.log (y : ℝ) - Real.log (x : ℝ)) +
              prefixError p * ((x : ℝ)⁻¹ - (y : ℝ)⁻¹)) =
            16 / saving p +
              (8 / saving p) * (Real.log (y : ℝ) - Real.log (x : ℝ)) +
              2 * prefixError p / x := by ring
        _ ≤ 16 / saving p +
              (16 / saving p) * Real.log (p : ℝ) +
              2 * prefixError p / x := by gcongr
        _ = 16 * (1 + Real.log (p : ℝ)) / saving p +
              2 * prefixError p / x := by ring

theorem eventually_attached_LFunction_tail :
    ∀ᶠ p : ℕ in atTop, ∀ (hp : p.Prime) (X : ℕ),
      0 < X → X + 1 < p →
      let χ₀ := Erdos1141.attachedQuadraticCharacter (2 * p) (8 * p)
        (by exact ⟨1, by ring⟩)
      letI : NeZero (8 * p) := ⟨mul_ne_zero (by norm_num) hp.ne_zero⟩
      let χ := χ₀.toDirichletCharacterComplex
      χ ≠ 1 →
      ‖(∑ n ∈ Finset.Icc 1 X, χ (n : ZMod (8 * p)) / (n : ℂ)) -
          DirichletCharacter.LFunction χ (1 : ℂ)‖ ≤
        16 * (1 + Real.log (p : ℝ)) / saving p +
          2 * prefixError p / X +
          4 * Real.sqrt ((8 * p : ℕ) : ℝ) *
            Real.log ((8 * p : ℕ) : ℝ) / (p - 1 : ℕ) := by
  filter_upwards [eventually_attached_reciprocal_interval] with p hinterval
  intro hp X hX hXp
  let χ₀ := Erdos1141.attachedQuadraticCharacter (2 * p) (8 * p)
    (by exact ⟨1, by ring⟩)
  letI : NeZero (8 * p) := ⟨mul_ne_zero (by norm_num) hp.ne_zero⟩
  let χ := χ₀.toDirichletCharacterComplex
  change χ ≠ 1 → _
  intro hchi
  let P : ℕ → ℂ := fun y ↦
    ∑ n ∈ Finset.Icc 1 y, χ (n : ZMod (8 * p)) / (n : ℂ)
  have hXy : X ≤ p - 1 := by omega
  have htailEq : P (p - 1) - P X =
      ∑ n ∈ Finset.Ioc X (p - 1),
        χ (n : ZMod (8 * p)) / (n : ℂ) := by
    have hunion : Finset.Icc 1 X ∪ Finset.Ioc X (p - 1) =
        Finset.Icc 1 (p - 1) := by
      ext n
      simp only [Finset.mem_union, Finset.mem_Icc, Finset.mem_Ioc]
      constructor
      · rintro (hn | hn) <;> omega
      · intro hn
        by_cases hnx : n ≤ X
        · exact Or.inl ⟨hn.1, hnx⟩
        · exact Or.inr ⟨lt_of_not_ge hnx, hn.2⟩
    have hdis : Disjoint (Finset.Icc 1 X) (Finset.Ioc X (p - 1)) := by
      rw [Finset.disjoint_left]
      intro n hncc hnoc
      simp only [Finset.mem_Icc] at hncc
      simp only [Finset.mem_Ioc] at hnoc
      omega
    change (∑ n ∈ Finset.Icc 1 (p - 1),
        χ (n : ZMod (8 * p)) / (n : ℂ)) -
      (∑ n ∈ Finset.Icc 1 X,
        χ (n : ZMod (8 * p)) / (n : ℂ)) = _
    rw [← hunion, Finset.sum_union hdis]
    ring
  have hinter := hinterval hp X (p - 1) hX hXy (by omega)
  have hq : 1 < 8 * p := by nlinarith [hp.pos]
  have hp1 : 0 < p - 1 := by omega
  have htail := norm_LFunction_one_sub_dirichletCharacterReciprocalPrefix_le
    hq χ hchi (p - 1) hp1
  change ‖P X - DirichletCharacter.LFunction χ (1 : ℂ)‖ ≤ _
  calc
    ‖P X - DirichletCharacter.LFunction χ (1 : ℂ)‖ =
        ‖(P (p - 1) - P X) +
          (DirichletCharacter.LFunction χ (1 : ℂ) - P (p - 1))‖ := by
      rw [← norm_neg]
      congr 1
      ring
    _ ≤ ‖P (p - 1) - P X‖ +
          ‖DirichletCharacter.LFunction χ (1 : ℂ) - P (p - 1)‖ :=
      norm_add_le _ _
    _ ≤ (16 * (1 + Real.log (p : ℝ)) / saving p +
          2 * prefixError p / X) +
        (4 * Real.sqrt ((8 * p : ℕ) : ℝ) *
          Real.log ((8 * p : ℕ) : ℝ) / (p - 1 : ℕ)) := by
      rw [htailEq]
      exact add_le_add (by simpa [χ, χ₀] using hinter) htail
    _ = 16 * (1 + Real.log (p : ℝ)) / saving p +
          2 * prefixError p / X +
          4 * Real.sqrt ((8 * p : ℕ) : ℝ) *
            Real.log ((8 * p : ℕ) : ℝ) / (p - 1 : ℕ) := by ring

set_option backward.isDefEq.respectTransparency.types false in
lemma zetaMul_prime_pow_eq_geom
    {q r e : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (hr : r.Prime) :
    χ.zetaMul (r ^ e) =
      ∑ i ∈ Finset.range (e + 1), (χ (r : ZMod q)) ^ i := by
  simp only [DirichletCharacter.zetaMul, toArithmeticFunction,
    coe_zeta_mul_apply, coe_mk,
    Nat.sum_divisors_prime_pow hr, pow_eq_zero_iff', hr.ne_zero, ne_eq,
    false_and, ↓reduceIte, Nat.cast_pow, map_pow]

lemma attached_prime_value_eq_neg_one
    {p X r : ℕ} (hp : p.Prime) (hr : r.Prime) (hr2 : r ≠ 2)
    (hrX : r ≤ X) (hXp : X < p)
    (hnosplit :
      Erdos1141.attachedQuadraticCharacter (2 * p) (8 * p)
        (by exact ⟨1, by ring⟩) r ≠ 1) :
    Erdos1141.attachedQuadraticCharacter (2 * p) (8 * p)
      (by exact ⟨1, by ring⟩) r = -1 := by
  let χ₀ := Erdos1141.attachedQuadraticCharacter (2 * p) (8 * p)
    (by exact ⟨1, by ring⟩)
  have hcop8 : Nat.Coprime r 8 := by
    rw [show 8 = 2 ^ 3 by norm_num,
      Nat.coprime_pow_right_iff (by omega) r 2]
    exact hr.coprime_iff_not_dvd.mpr (by
      intro hdiv
      exact hr2 (Nat.dvd_prime Nat.prime_two |>.mp hdiv |>.resolve_left hr.ne_one))
  have hrp : r ≠ p := by omega
  have hcopp : Nat.Coprime r p := by
    exact hr.coprime_iff_not_dvd.mpr (by
      intro hdiv
      exact hrp (Nat.dvd_prime hp |>.mp hdiv |>.resolve_left hr.ne_one))
  have hcop : Nat.Coprime r (8 * p) := (Nat.coprime_mul_iff_right).2 ⟨hcop8, hcopp⟩
  rcases χ₀.map_coprime hcop with h | h
  · exact (hnosplit h).elim
  · exact h

set_option backward.isDefEq.respectTransparency.types false in
lemma attached_zetaMul_prime_pow_eq
    {p X r e : ℕ} (hp : p.Prime) (hr : r.Prime) (hrX : r ≤ X)
    (hXp : X < p)
    (hnosplit :
      Erdos1141.attachedQuadraticCharacter (2 * p) (8 * p)
        (by exact ⟨1, by ring⟩) r ≠ 1) :
    let χ₀ := Erdos1141.attachedQuadraticCharacter (2 * p) (8 * p)
      (by exact ⟨1, by ring⟩)
    letI : NeZero (8 * p) := ⟨mul_ne_zero (by norm_num) hp.ne_zero⟩
    let χ := χ₀.toDirichletCharacterComplex
    χ.zetaMul (r ^ e) = if r = 2 ∨ Even e then 1 else 0 := by
  let χ₀ := Erdos1141.attachedQuadraticCharacter (2 * p) (8 * p)
    (by exact ⟨1, by ring⟩)
  letI : NeZero (8 * p) := ⟨mul_ne_zero (by norm_num) hp.ne_zero⟩
  let χ := χ₀.toDirichletCharacterComplex
  change χ.zetaMul (r ^ e) = _
  rw [zetaMul_prime_pow_eq_geom χ hr]
  by_cases hr2 : r = 2
  · subst r
    have hχ2 : χ (2 : ZMod (8 * p)) = 0 := by
      have hperiod : χ₀ ((2 : ZMod (8 * p)).val) = χ₀ 2 := by
        apply χ₀.periodic
        rw [← ZMod.natCast_eq_natCast_iff]
        simp
      change (χ₀ ((2 : ZMod (8 * p)).val) : ℂ) = 0
      rw [hperiod]
      exact_mod_cast attachedQuadraticCharacter_even_zero (p := p) (n := 2) (by
        exact ⟨1, by omega⟩)
    simp [hχ2]
  · have hχr : χ (r : ZMod (8 * p)) = -1 := by
      have hperiod : χ₀ ((r : ZMod (8 * p)).val) = χ₀ r := by
        apply χ₀.periodic
        rw [← ZMod.natCast_eq_natCast_iff]
        simp
      change (χ₀ ((r : ZMod (8 * p)).val) : ℂ) = -1
      rw [hperiod]
      exact_mod_cast attached_prime_value_eq_neg_one hp hr hr2 hrX hXp hnosplit
    rw [hχr, neg_one_geom_sum]
    by_cases he : Even e
    · simp [hr2, he]
    · simp [hr2, he, (Nat.not_even_iff_odd.mp he).add_one]

lemma attached_zetaMul_nonzero_support
    {p X n : ℕ} (hp : p.Prime) (hn : 0 < n) (hnX : n ≤ X)
    (hXp : X < p)
    (hnosplit : ∀ r : ℕ, r.Prime → r ≤ X →
      Erdos1141.attachedQuadraticCharacter (2 * p) (8 * p)
        (by exact ⟨1, by ring⟩) r ≠ 1) :
    let χ₀ := Erdos1141.attachedQuadraticCharacter (2 * p) (8 * p)
      (by exact ⟨1, by ring⟩)
    letI : NeZero (8 * p) := ⟨mul_ne_zero (by norm_num) hp.ne_zero⟩
    let χ := χ₀.toDirichletCharacterComplex
    χ.zetaMul n ≠ 0 →
      χ.zetaMul n = 1 ∧ ∃ b : ℕ, n = b ^ 2 ∨ n = 2 * b ^ 2 := by
  classical
  let χ₀ := Erdos1141.attachedQuadraticCharacter (2 * p) (8 * p)
    (by exact ⟨1, by ring⟩)
  letI : NeZero (8 * p) := ⟨mul_ne_zero (by norm_num) hp.ne_zero⟩
  let χ := χ₀.toDirichletCharacterComplex
  change χ.zetaMul n ≠ 0 → _
  intro hnonzero
  have hfactor : χ.zetaMul n =
      ∏ r ∈ n.primeFactors, χ.zetaMul (r ^ n.factorization r) :=
    by
      simpa [Finsupp.prod] using
        ArithmeticFunction.IsMultiplicative.multiplicative_factorization χ.zetaMul
          χ.isMultiplicative_zetaMul hn.ne'
  have hlocal : ∀ r ∈ n.primeFactors,
      χ.zetaMul (r ^ n.factorization r) =
        if r = 2 ∨ Even (n.factorization r) then 1 else 0 := by
    intro r hr
    have hrp : r.Prime := Nat.prime_of_mem_primeFactors hr
    have hrdvd : r ∣ n := (Nat.mem_primeFactors.mp hr).2.1
    have hrn : r ≤ n := Nat.le_of_dvd hn hrdvd
    exact attached_zetaMul_prime_pow_eq hp hrp (hrn.trans hnX) hXp
      (hnosplit r hrp (hrn.trans hnX))
  have hall : ∀ r ∈ n.primeFactors,
      r = 2 ∨ Even (n.factorization r) := by
    intro r hr
    by_contra hbad
    apply hnonzero
    rw [hfactor]
    apply Finset.prod_eq_zero hr
    rw [hlocal r hr, if_neg hbad]
  have hcoeff : χ.zetaMul n = 1 := by
    rw [hfactor]
    apply Finset.prod_eq_one
    intro r hr
    rw [hlocal r hr, if_pos (hall r hr)]
  refine ⟨hcoeff, ?_⟩
  obtain ⟨a, b, ha, hb, hab, hasq⟩ := Nat.sq_mul_squarefree_of_pos hn
  have hsubset : a.primeFactors ⊆ {2} := by
    intro r hra
    have hrp : r.Prime := Nat.prime_of_mem_primeFactors hra
    have hradvd : r ∣ a := (Nat.mem_primeFactors.mp hra).2.1
    have hrn : r ∣ n := by
      rw [← hab]
      exact dvd_trans hradvd (dvd_mul_left a (b ^ 2))
    have hrmem : r ∈ n.primeFactors :=
      Nat.mem_primeFactors.mpr ⟨hrp, hrn, hn.ne'⟩
    rcases hall r hrmem with hr2 | heven
    · simpa [hr2]
    · have hfac : n.factorization r = 2 * b.factorization r + 1 := by
        rw [← hab, Nat.factorization_mul (pow_ne_zero 2 hb.ne') ha.ne',
          Finsupp.add_apply, Nat.factorization_pow,
          Finsupp.smul_apply, Nat.factorization_eq_one_of_squarefree hasq hrp hradvd]
        simp
      exfalso
      rcases heven with ⟨k, hk⟩
      rw [hfac] at hk
      omega
  rcases Finset.subset_singleton_iff.mp hsubset with haempty | hasingle
  · have ha1 : a = 1 := by
      rw [← Nat.prod_primeFactors_of_squarefree hasq, haempty]
      simp
    refine ⟨b, Or.inl ?_⟩
    rw [← hab, ha1]
    simp
  · have ha2 : a = 2 := by
      rw [← Nat.prod_primeFactors_of_squarefree hasq, hasingle]
      simp
    refine ⟨b, Or.inr ?_⟩
    rw [← hab, ha2]
    ring

lemma attached_smoothed_sum_norm_le
    {p X : ℕ} (hp : p.Prime) (hX : 0 < X) (hXp : X < p)
    (hnosplit : ∀ r : ℕ, r.Prime → r ≤ X →
      Erdos1141.attachedQuadraticCharacter (2 * p) (8 * p)
        (by exact ⟨1, by ring⟩) r ≠ 1) :
    let χ₀ := Erdos1141.attachedQuadraticCharacter (2 * p) (8 * p)
      (by exact ⟨1, by ring⟩)
    letI : NeZero (8 * p) := ⟨mul_ne_zero (by norm_num) hp.ne_zero⟩
    let χ := χ₀.toDirichletCharacterComplex
    ‖quadraticZetaLinearSmoothedSum χ X‖ ≤ 2 * (X.sqrt + 1 : ℕ) := by
  classical
  let χ₀ := Erdos1141.attachedQuadraticCharacter (2 * p) (8 * p)
    (by exact ⟨1, by ring⟩)
  letI : NeZero (8 * p) := ⟨mul_ne_zero (by norm_num) hp.ne_zero⟩
  let χ := χ₀.toDirichletCharacterComplex
  let indices := Finset.Icc 1 X
  let roots := Finset.range (X.sqrt + 1)
  let squares := roots.image (fun b : ℕ ↦ b ^ 2)
  let twiceSquares := roots.image (fun b : ℕ ↦ 2 * b ^ 2)
  let candidates := squares ∪ twiceSquares
  let weight : ℕ → ℂ := fun n ↦
    ((1 - (n : ℝ) / (X : ℝ) : ℝ) : ℂ)
  let term : ℕ → ℂ := fun n ↦ χ.zetaMul n * weight n
  have hcandidates : candidates.card ≤ 2 * (X.sqrt + 1) := by
    dsimp [candidates, squares, twiceSquares, roots]
    calc
      ((Finset.range (X.sqrt + 1)).image (fun b : ℕ ↦ b ^ 2) ∪
          (Finset.range (X.sqrt + 1)).image (fun b : ℕ ↦ 2 * b ^ 2)).card ≤
          ((Finset.range (X.sqrt + 1)).image (fun b : ℕ ↦ b ^ 2)).card +
            ((Finset.range (X.sqrt + 1)).image (fun b : ℕ ↦ 2 * b ^ 2)).card :=
        Finset.card_union_le _ _
      _ ≤ (Finset.range (X.sqrt + 1)).card +
            (Finset.range (X.sqrt + 1)).card :=
        add_le_add Finset.card_image_le Finset.card_image_le
      _ = 2 * (X.sqrt + 1) := by simp; omega
  have hsupport : ∀ n ∈ indices, χ.zetaMul n ≠ 0 → n ∈ candidates := by
    intro n hn hnonzero
    have hnbounds := Finset.mem_Icc.mp hn
    rcases (attached_zetaMul_nonzero_support hp (by omega) hnbounds.2 hXp
      hnosplit hnonzero).2 with ⟨b, hb | hb⟩
    · have hbroot : b ≤ X.sqrt := Nat.le_sqrt'.mpr (by simpa [hb] using hnbounds.2)
      apply Finset.mem_union_left twiceSquares
      exact Finset.mem_image.mpr ⟨b, by simp [roots, hbroot], hb.symm⟩
    · have hb2X : b ^ 2 ≤ X := by omega
      have hbroot : b ≤ X.sqrt := Nat.le_sqrt'.mpr hb2X
      apply Finset.mem_union_right squares
      exact Finset.mem_image.mpr ⟨b, by simp [roots, hbroot], hb.symm⟩
  have hterm : ∀ n ∈ indices, ‖term n‖ ≤ 1 := by
    intro n hn
    have hnbounds := Finset.mem_Icc.mp hn
    by_cases hzero : χ.zetaMul n = 0
    · simp [term, hzero]
    · have hcoeff := (attached_zetaMul_nonzero_support hp (by omega)
          hnbounds.2 hXp hnosplit hzero).1
      change χ.zetaMul n = 1 at hcoeff
      have hXreal : (0 : ℝ) < X := by exact_mod_cast hX
      have hratio0 : (0 : ℝ) ≤ (n : ℝ) / X := by positivity
      have hratio1 : (n : ℝ) / X ≤ 1 :=
        (div_le_one hXreal).2 (by exact_mod_cast hnbounds.2)
      have hweight : ‖weight n‖ ≤ 1 := by
        change ‖((1 - (n : ℝ) / (X : ℝ) : ℝ) : ℂ)‖ ≤ 1
        rw [Complex.norm_real, Real.norm_of_nonneg (sub_nonneg.mpr hratio1)]
        linarith
      change ‖χ.zetaMul n * weight n‖ ≤ 1
      rw [norm_mul, hcoeff, norm_one, one_mul]
      exact hweight
  have hsumEq :
      (∑ n ∈ indices, term n) = ∑ n ∈ indices ∩ candidates, term n := by
    symm
    apply Finset.sum_subset Finset.inter_subset_left
    intro n hnindices hnnot
    have hnotcand : n ∉ candidates := by
      intro hncand
      exact hnnot (Finset.mem_inter.mpr ⟨hnindices, hncand⟩)
    have hzero : χ.zetaMul n = 0 := by
      by_contra hnonzero
      exact hnotcand (hsupport n hnindices hnonzero)
    simp [term, hzero]
  change ‖∑ n ∈ indices, term n‖ ≤ _
  rw [hsumEq]
  calc
    ‖∑ n ∈ indices ∩ candidates, term n‖ ≤
        ∑ n ∈ indices ∩ candidates, ‖term n‖ := norm_sum_le _ _
    _ ≤ ∑ _n ∈ indices ∩ candidates, (1 : ℝ) := by
      apply Finset.sum_le_sum
      intro n hn
      exact hterm n (Finset.mem_inter.mp hn).1
    _ = ((indices ∩ candidates).card : ℝ) := by simp
    _ ≤ (candidates.card : ℝ) := by
      exact_mod_cast Finset.card_le_card Finset.inter_subset_right
    _ ≤ ((2 * (X.sqrt + 1) : ℕ) : ℝ) := by exact_mod_cast hcandidates
    _ = 2 * (X.sqrt + 1 : ℕ) := by norm_num

theorem eventually_attached_swapped_remainder_bound :
    ∀ᶠ p : ℕ in atTop, ∀ (hp : p.Prime) (X : ℕ), 0 < X → X + 1 < p →
      let χ₀ := Erdos1141.attachedQuadraticCharacter (2 * p) (8 * p)
        (by exact ⟨1, by ring⟩)
      letI : NeZero (8 * p) := ⟨mul_ne_zero (by norm_num) hp.ne_zero⟩
      let χ := χ₀.toDirichletCharacterComplex
      χ ≠ 1 →
      ‖quadraticZetaSwappedEulerRemainder χ X‖ ≤
        64 * (X : ℝ) / saving p +
          4 * prefixError p * (1 + Real.log (X : ℝ)) := by
  filter_upwards [eventually_attached_complex_weighted_prefix] with p hweighted
  intro hp X hX hXp
  let χ₀ := Erdos1141.attachedQuadraticCharacter (2 * p) (8 * p)
    (by exact ⟨1, by ring⟩)
  letI : NeZero (8 * p) := ⟨mul_ne_zero (by norm_num) hp.ne_zero⟩
  let χ := χ₀.toDirichletCharacterComplex
  change χ ≠ 1 → ‖quadraticZetaSwappedEulerRemainder χ X‖ ≤
    64 * (X : ℝ) / saving p +
      4 * prefixError p * (1 + Real.log (X : ℝ))
  intro hchi
  let C₁ : ℝ := 32 / saving p
  let C₂ : ℝ := 4 * prefixError p
  let charPrefix : ℕ → ℂ := fun y ↦
    ∑ a ∈ Finset.Icc 1 y, (a : ℂ) * χ (a : ZMod (8 * p))
  let F : ℝ → ℂ := fun t ↦ ((Int.fract t : ℝ) : ℂ) *
    charPrefix (quadraticEulerCutoff X t)
  have hC₁ : 0 ≤ C₁ := by dsimp [C₁]; positivity
  have hC₂ : 0 ≤ C₂ := by
    dsimp [C₂, prefixError]
    positivity
  have hprefix : ∀ y ≤ X, ‖charPrefix y‖ ≤ C₁ * (y : ℝ) ^ 2 + C₂ * y := by
    intro y hyX
    by_cases hy0 : y = 0
    · subst y
      simp [charPrefix]
    · have hy : 0 < y := Nat.pos_of_ne_zero hy0
      have hyp : y + 1 < p := (Nat.add_le_add_right hyX 1).trans_lt hXp
      have hw := hweighted hp y hyp hy
      change ‖charPrefix y‖ ≤ _
      have hyone : ((y + 1 : ℕ) : ℝ) ≤ 2 * (y : ℝ) := by
        exact_mod_cast (show y + 1 ≤ 2 * y by omega)
      have hJ : (0 : ℝ) < saving p := by exact_mod_cast saving_pos p
      calc
        ‖charPrefix y‖ ≤
            8 * ((y + 1 : ℕ) : ℝ) ^ 2 / saving p +
              2 * prefixError p * ((y + 1 : ℕ) : ℝ) := by
          simpa [charPrefix, χ, χ₀] using hw
        _ ≤ 8 * (2 * (y : ℝ)) ^ 2 / saving p +
              2 * prefixError p * (2 * (y : ℝ)) := by
          apply add_le_add
          · apply div_le_div_of_nonneg_right _ hJ.le
            exact mul_le_mul_of_nonneg_left
              (pow_le_pow_left₀ (by positivity) hyone 2) (by norm_num)
          · exact mul_le_mul_of_nonneg_left hyone (by
              dsimp [prefixError]
              positivity)
        _ = C₁ * (y : ℝ) ^ 2 + C₂ * y := by
          dsimp [C₁, C₂]
          ring
  have hq : 1 < 8 * p := by nlinarith [hp.pos]
  have hFint : IntegrableOn F (Set.Ioc 0 (X : ℝ)) := by
    simpa [F, charPrefix] using
      integrableOn_quadraticSwappedIntegrand_local hq χ hchi (X := X)
  have hXone : (1 : ℝ) ≤ X := by exact_mod_cast hX
  have hXreal : (0 : ℝ) < X := by exact_mod_cast hX
  have hpointFirst : ∀ t ∈ Set.Ioc (0 : ℝ) 1,
      ‖F t‖ ≤ C₁ * (X : ℝ) ^ 2 + C₂ * X := by
    intro t ht
    change ‖((Int.fract t : ℝ) : ℂ) *
      charPrefix (quadraticEulerCutoff X t)‖ ≤ _
    rw [norm_mul]
    have hfract : ‖((Int.fract t : ℝ) : ℂ)‖ ≤ 1 := by
      rw [Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (Int.fract_nonneg t)]
      exact (Int.fract_lt_one t).le
    have hcut : quadraticEulerCutoff X t ≤ X := quadraticEulerCutoff_le_local X t
    have hpref := hprefix (quadraticEulerCutoff X t) hcut
    calc
      ‖((Int.fract t : ℝ) : ℂ)‖ *
          ‖charPrefix (quadraticEulerCutoff X t)‖ ≤
          1 * (C₁ * (quadraticEulerCutoff X t : ℝ) ^ 2 +
            C₂ * quadraticEulerCutoff X t) :=
        mul_le_mul hfract hpref (norm_nonneg _) zero_le_one
      _ ≤ C₁ * (X : ℝ) ^ 2 + C₂ * X := by
        have hcut' : (quadraticEulerCutoff X t : ℝ) ≤ X := by exact_mod_cast hcut
        simp only [one_mul]
        gcongr
  have hpointSecond : ∀ t ∈ Set.Ioc (1 : ℝ) X,
      ‖F t‖ ≤ C₁ * (X : ℝ) ^ 2 * (t ^ 2)⁻¹ +
        C₂ * (X : ℝ) * t⁻¹ := by
    intro t ht
    have ht0 : 0 < t := zero_lt_one.trans ht.1
    change ‖((Int.fract t : ℝ) : ℂ) *
      charPrefix (quadraticEulerCutoff X t)‖ ≤ _
    rw [norm_mul]
    have hfract : ‖((Int.fract t : ℝ) : ℂ)‖ ≤ 1 := by
      rw [Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (Int.fract_nonneg t)]
      exact (Int.fract_lt_one t).le
    have hcutNat : quadraticEulerCutoff X t ≤ X := quadraticEulerCutoff_le_local X t
    have hpref := hprefix (quadraticEulerCutoff X t) hcutNat
    have hcut : (quadraticEulerCutoff X t : ℝ) ≤ (X : ℝ) / t :=
      cast_quadraticEulerCutoff_le_div_local ht0
    calc
      ‖((Int.fract t : ℝ) : ℂ)‖ *
          ‖charPrefix (quadraticEulerCutoff X t)‖ ≤
          1 * (C₁ * (quadraticEulerCutoff X t : ℝ) ^ 2 +
            C₂ * quadraticEulerCutoff X t) :=
        mul_le_mul hfract hpref (norm_nonneg _) zero_le_one
      _ ≤ C₁ * ((X : ℝ) / t) ^ 2 + C₂ * ((X : ℝ) / t) := by
        simp only [one_mul]
        gcongr
      _ = C₁ * (X : ℝ) ^ 2 * (t ^ 2)⁻¹ + C₂ * (X : ℝ) * t⁻¹ := by
        field_simp [ht0.ne']
  have hFirstInt : IntegrableOn (fun t ↦ ‖F t‖) (Set.Ioc (0 : ℝ) 1) :=
    (hFint.mono_set (Set.Ioc_subset_Ioc_right hXone)).norm
  have hSecondInt : IntegrableOn (fun t ↦ ‖F t‖) (Set.Ioc (1 : ℝ) X) :=
    (hFint.mono_set (Set.Ioc_subset_Ioc_left zero_le_one)).norm
  have hFirstMajor : IntegrableOn
      (fun _t : ℝ ↦ C₁ * (X : ℝ) ^ 2 + C₂ * X) (Set.Ioc (0 : ℝ) 1) :=
    integrableOn_const measure_Ioc_lt_top.ne
  have hInv : ContinuousOn (fun t : ℝ ↦ t⁻¹) (Set.Icc 1 X) := by
    apply ContinuousOn.inv₀ continuousOn_id
    intro t ht
    exact (zero_lt_one.trans_le ht.1).ne'
  have hInvSq : ContinuousOn (fun t : ℝ ↦ (t ^ 2)⁻¹) (Set.Icc 1 X) := by
    apply ContinuousOn.inv₀ (continuousOn_id.pow 2)
    intro t ht
    exact pow_ne_zero 2 (zero_lt_one.trans_le ht.1).ne'
  have hSecondMajor : IntegrableOn
      (fun t : ℝ ↦ C₁ * (X : ℝ) ^ 2 * (t ^ 2)⁻¹ +
        C₂ * (X : ℝ) * t⁻¹) (Set.Ioc (1 : ℝ) X) := by
    exact (((hInvSq.const_mul (C₁ * (X : ℝ) ^ 2)).add
      (hInv.const_mul (C₂ * (X : ℝ)))).integrableOn_Icc).mono_set
        Set.Ioc_subset_Icc_self
  have hFirst :
      (∫ t : ℝ in Set.Ioc 0 1, ‖F t‖) ≤
        C₁ * (X : ℝ) ^ 2 + C₂ * X := by
    calc
      (∫ t : ℝ in Set.Ioc 0 1, ‖F t‖) ≤
          ∫ _t : ℝ in Set.Ioc 0 1,
            (C₁ * (X : ℝ) ^ 2 + C₂ * X) := by
        apply setIntegral_mono_ae_restrict hFirstInt hFirstMajor
        filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
        exact hpointFirst t ht
      _ = C₁ * (X : ℝ) ^ 2 + C₂ * X := by
        rw [setIntegral_const, Measure.real_def, Real.volume_Ioc]
        norm_num [smul_eq_mul]
  have hSecond :
      (∫ t : ℝ in Set.Ioc 1 (X : ℝ), ‖F t‖) ≤
        C₁ * (X : ℝ) ^ 2 + C₂ * X * Real.log (X : ℝ) := by
    calc
      (∫ t : ℝ in Set.Ioc 1 (X : ℝ), ‖F t‖) ≤
          ∫ t : ℝ in Set.Ioc 1 (X : ℝ),
            (C₁ * (X : ℝ) ^ 2 * (t ^ 2)⁻¹ +
              C₂ * (X : ℝ) * t⁻¹) := by
        apply setIntegral_mono_ae_restrict hSecondInt hSecondMajor
        filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
        exact hpointSecond t ht
      _ = C₁ * (X : ℝ) ^ 2 * (1 - (X : ℝ)⁻¹) +
            C₂ * (X : ℝ) * Real.log (X : ℝ) := by
        rw [integral_add]
        · rw [integral_const_mul, integral_const_mul,
            integral_Ioc_inv_sq_local zero_lt_one hXone]
          rw [← intervalIntegral.integral_of_le hXone,
            integral_inv_of_pos zero_lt_one hXreal]
          simp only [inv_one, div_one]
        · exact (hInvSq.const_mul (C₁ * (X : ℝ) ^ 2)).integrableOn_Icc.mono_set
            Set.Ioc_subset_Icc_self
        · exact (hInv.const_mul (C₂ * (X : ℝ))).integrableOn_Icc.mono_set
            Set.Ioc_subset_Icc_self
      _ ≤ C₁ * (X : ℝ) ^ 2 + C₂ * X * Real.log (X : ℝ) := by
        have hcoeff : 0 ≤ C₁ * (X : ℝ) ^ 2 := mul_nonneg hC₁ (sq_nonneg _)
        have hinv : 0 ≤ (X : ℝ)⁻¹ := inv_nonneg.mpr hXreal.le
        nlinarith
  have hunion : Set.Ioc (0 : ℝ) (X : ℝ) =
      Set.Ioc (0 : ℝ) (1 : ℝ) ∪ Set.Ioc (1 : ℝ) (X : ℝ) := by
    ext t
    simp only [Set.mem_Ioc, Set.mem_union]
    constructor
    · intro ht
      by_cases ht1 : t ≤ 1
      · exact Or.inl ⟨ht.1, ht1⟩
      · exact Or.inr ⟨lt_of_not_ge ht1, ht.2⟩
    · rintro (ht | ht) <;> constructor
      · exact ht.1
      · exact ht.2.trans hXone
      · exact zero_lt_one.trans ht.1
      · exact ht.2
  have hdis : Disjoint (Set.Ioc (0 : ℝ) 1) (Set.Ioc 1 X) := by
    rw [Set.disjoint_left]
    intro t ht1 ht2
    exact (not_lt_of_ge ht1.2) ht2.1
  have hnormIntegral :
      ‖∫ t : ℝ in Set.Ioc 0 (X : ℝ), F t‖ ≤
        2 * C₁ * (X : ℝ) ^ 2 +
          C₂ * X * (1 + Real.log (X : ℝ)) := by
    calc
      ‖∫ t : ℝ in Set.Ioc 0 (X : ℝ), F t‖ ≤
          ∫ t : ℝ in Set.Ioc 0 (X : ℝ), ‖F t‖ :=
        norm_integral_le_integral_norm _
      _ = (∫ t : ℝ in Set.Ioc 0 1, ‖F t‖) +
          ∫ t : ℝ in Set.Ioc 1 (X : ℝ), ‖F t‖ := by
        rw [hunion, setIntegral_union hdis measurableSet_Ioc hFirstInt hSecondInt]
      _ ≤ (C₁ * (X : ℝ) ^ 2 + C₂ * X) +
          (C₁ * (X : ℝ) ^ 2 + C₂ * X * Real.log (X : ℝ)) :=
        add_le_add hFirst hSecond
      _ = 2 * C₁ * (X : ℝ) ^ 2 +
          C₂ * X * (1 + Real.log (X : ℝ)) := by ring
  unfold quadraticZetaSwappedEulerRemainder
  rw [norm_mul, norm_div, norm_one, Complex.norm_natCast]
  change (1 / (X : ℝ)) *
      ‖∫ t : ℝ in Set.Ioc 0 (X : ℝ), F t‖ ≤ _
  calc
    (1 / (X : ℝ)) * ‖∫ t : ℝ in Set.Ioc 0 (X : ℝ), F t‖ ≤
        (1 / (X : ℝ)) *
          (2 * C₁ * (X : ℝ) ^ 2 +
            C₂ * X * (1 + Real.log (X : ℝ))) :=
      mul_le_mul_of_nonneg_left hnormIntegral (by positivity)
    _ = 64 * (X : ℝ) / saving p +
          4 * prefixError p * (1 + Real.log (X : ℝ)) := by
      dsimp [C₁, C₂]
      field_simp [hXreal.ne']
      ring

noncomputable def attachedTailError (p X : ℕ) : ℝ :=
  16 * (1 + Real.log (p : ℝ)) / saving p +
    2 * prefixError p / X +
    4 * Real.sqrt ((8 * p : ℕ) : ℝ) *
      Real.log ((8 * p : ℕ) : ℝ) / (p - 1 : ℕ)

noncomputable def attachedRemainderError (p X : ℕ) : ℝ :=
  64 * (X : ℝ) / saving p +
    4 * prefixError p * (1 + Real.log (X : ℝ))

noncomputable def attachedComparisonError (p X : ℕ) : ℝ :=
  ((X : ℝ) / 2) * attachedTailError p X + attachedRemainderError p X

theorem eventually_attached_comparison :
    ∀ᶠ p : ℕ in atTop, ∀ (hp : p.Prime) (X : ℕ),
      0 < X → X + 1 < p →
      let χ₀ := Erdos1141.attachedQuadraticCharacter (2 * p) (8 * p)
        (by exact ⟨1, by ring⟩)
      letI : NeZero (8 * p) := ⟨mul_ne_zero (by norm_num) hp.ne_zero⟩
      let χ := χ₀.toDirichletCharacterComplex
      χ ≠ 1 →
      ‖quadraticZetaLinearSmoothedSum χ X -
          ((X : ℂ) / 2) * DirichletCharacter.LFunction χ (1 : ℂ)‖ ≤
        attachedComparisonError p X := by
  filter_upwards [eventually_attached_LFunction_tail,
    eventually_attached_swapped_remainder_bound] with p htail hrem
  intro hp X hX hXp
  let χ₀ := Erdos1141.attachedQuadraticCharacter (2 * p) (8 * p)
    (by exact ⟨1, by ring⟩)
  letI : NeZero (8 * p) := ⟨mul_ne_zero (by norm_num) hp.ne_zero⟩
  let χ := χ₀.toDirichletCharacterComplex
  change χ ≠ 1 → _
  intro hchi
  let P : ℂ := ∑ a ∈ Finset.Icc 1 X,
    χ (a : ZMod (8 * p)) / (a : ℂ)
  have htail' : ‖P - DirichletCharacter.LFunction χ (1 : ℂ)‖ ≤
      attachedTailError p X := by
    simpa [P, attachedTailError, χ, χ₀] using htail hp X hX hXp hchi
  have hrem' : ‖quadraticZetaSwappedEulerRemainder χ X‖ ≤
      attachedRemainderError p X := by
    simpa [attachedRemainderError, χ, χ₀] using hrem hp X hX hXp hchi
  have hscale : ‖((X : ℂ) / 2)‖ = (X : ℝ) / 2 := by
    rw [norm_div, Complex.norm_natCast]
    norm_num
  have hscaled : ‖((X : ℂ) / 2) *
        (P - DirichletCharacter.LFunction χ (1 : ℂ))‖ ≤
      ((X : ℝ) / 2) * attachedTailError p X := by
    rw [norm_mul, hscale]
    exact mul_le_mul_of_nonneg_left htail' (by positivity)
  have hmain := quadraticZetaLinearSmoothedSum_eq_directEulerRemainder χ hX
  have hswap := quadraticZetaDirectEulerRemainder_eq_swapped χ hX
  calc
    ‖quadraticZetaLinearSmoothedSum χ X -
        ((X : ℂ) / 2) * DirichletCharacter.LFunction χ (1 : ℂ)‖ =
        ‖((X : ℂ) / 2) *
            (P - DirichletCharacter.LFunction χ (1 : ℂ)) -
          quadraticZetaSwappedEulerRemainder χ X‖ := by
      rw [hmain, hswap]
      dsimp [P]
      ring
    _ ≤ ‖((X : ℂ) / 2) *
          (P - DirichletCharacter.LFunction χ (1 : ℂ))‖ +
        ‖quadraticZetaSwappedEulerRemainder χ X‖ := norm_sub_le _ _
    _ ≤ ((X : ℝ) / 2) * attachedTailError p X +
        attachedRemainderError p X := add_le_add hscaled hrem'
    _ = attachedComparisonError p X := rfl

lemma attached_character_test_value_neg_one
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) :
    Erdos1141.attachedQuadraticCharacter (2 * p) (8 * p)
      (by exact ⟨1, by ring⟩) (4 * p - 1) = -1 := by
  let a := 4 * p - 1
  have hpodd : Odd p := hp.eq_two_or_odd'.resolve_left hp2
  have haodd : Odd a := by
    rcases hpodd with ⟨k, hk⟩
    refine ⟨4 * k + 1, ?_⟩
    dsimp [a]
    omega
  have ha8 : a % 8 = 3 := by
    rcases hpodd with ⟨k, hk⟩
    dsimp [a]
    omega
  have ha4 : a % 4 = 3 := by omega
  have hcop4p : Nat.Coprime a (4 * p) := by
    dsimp [a]
    rw [Nat.coprime_self_sub_left (by nlinarith [hp.pos])]
    simp
  have hcop2 : Nat.Coprime a 2 := Nat.coprime_two_right.mpr haodd
  have hcop : Nat.Coprime a (8 * p) := by
    rw [show 8 * p = 2 * (4 * p) by ring, Nat.coprime_mul_iff_right]
    exact ⟨hcop2, hcop4p⟩
  rw [Erdos1141.attachedQuadraticCharacter_apply_coprime
    (by exact ⟨1, by ring⟩) hcop]
  have htwo : jacobiSym (2 : ℤ) a = -1 := by
    rw [jacobiSym.at_two haodd, ZMod.χ₈_nat_eq_if_mod_eight]
    have ha2 : a % 2 = 1 := Nat.odd_iff.mp haodd
    simp [ha2, ha8]
  have haInt : (a : ℤ) = 4 * (p : ℤ) - 1 := by
    dsimp [a]
    omega
  have hswapNeg : jacobiSym (a : ℤ) p = jacobiSym (-1 : ℤ) p := by
    apply jacobiSym.mod_left'
    rw [haInt]
    simp
  have hpJacobi : jacobiSym (p : ℤ) a = 1 := by
    rcases Nat.odd_mod_four_iff.mp (Nat.odd_iff.mp hpodd) with hp1 | hp3
    · rw [jacobiSym.quadratic_reciprocity_one_mod_four hp1 haodd,
          hswapNeg, jacobiSym.at_neg_one hpodd,
          ZMod.χ₄_nat_one_mod_four hp1]
    · rw [jacobiSym.quadratic_reciprocity_three_mod_four hp3 ha4,
          hswapNeg, jacobiSym.at_neg_one hpodd,
          ZMod.χ₄_nat_three_mod_four hp3]
      norm_num
  rw [show ((2 * p : ℕ) : ℤ) = (2 : ℤ) * (p : ℤ) by norm_num,
    jacobiSym.mul_left, htwo, hpJacobi]
  norm_num

lemma attached_character_complex_ne_one
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) :
    let χ₀ := Erdos1141.attachedQuadraticCharacter (2 * p) (8 * p)
      (by exact ⟨1, by ring⟩)
    letI : NeZero (8 * p) := ⟨mul_ne_zero (by norm_num) hp.ne_zero⟩
    χ₀.toDirichletCharacterComplex ≠ 1 := by
  let χ₀ := Erdos1141.attachedQuadraticCharacter (2 * p) (8 * p)
    (by exact ⟨1, by ring⟩)
  letI : NeZero (8 * p) := ⟨mul_ne_zero (by norm_num) hp.ne_zero⟩
  let χ := χ₀.toDirichletCharacterComplex
  change χ ≠ 1
  intro hprincipal
  have htest : χ₀ (4 * p - 1) = -1 :=
    attached_character_test_value_neg_one hp hp2
  have hcop : Nat.Coprime (4 * p - 1) (8 * p) := by
    by_contra hnot
    have hzero : χ₀ (4 * p - 1) = 0 :=
      χ₀.map_non_coprime hnot
    rw [hzero] at htest
    norm_num at htest
  have hunit : IsUnit ((4 * p - 1 : ℕ) : ZMod (8 * p)) :=
    (ZMod.isUnit_iff_coprime _ _).2 hcop
  have hone : χ ((4 * p - 1 : ℕ) : ZMod (8 * p)) = 1 := by
    rw [hprincipal]
    exact MulChar.one_apply hunit
  have hneg : χ ((4 * p - 1 : ℕ) : ZMod (8 * p)) = -1 := by
    rw [Erdos1141.QuadraticCharacterMod.toDirichletCharacterComplex_apply_nat]
    exact_mod_cast htest
  rw [hneg] at hone
  norm_num at hone

lemma attached_character_complex_sq_eq_one
    {p : ℕ} (hp : p.Prime) :
    let χ₀ := Erdos1141.attachedQuadraticCharacter (2 * p) (8 * p)
      (by exact ⟨1, by ring⟩)
    letI : NeZero (8 * p) := ⟨mul_ne_zero (by norm_num) hp.ne_zero⟩
    χ₀.toDirichletCharacterComplex ^ 2 = 1 := by
  let χ₀ := Erdos1141.attachedQuadraticCharacter (2 * p) (8 * p)
    (by exact ⟨1, by ring⟩)
  letI : NeZero (8 * p) := ⟨mul_ne_zero (by norm_num) hp.ne_zero⟩
  exact MulChar.isQuadratic_iff_sq_eq_one.mp
    χ₀.toDirichletCharacterComplex_isQuadratic

def pollackCutoff (p : ℕ) : ℕ := p.sqrt / 4

theorem eventually_pollackCutoff_bounds :
    ∀ᶠ p : ℕ in atTop,
      0 < pollackCutoff p ∧
      pollackCutoff p + 1 < p ∧
      2 * pollackCutoff p ^ 2 + pollackCutoff p < p ∧
      (p : ℝ) ^ (1 / 2 : ℝ) ≤ 8 * pollackCutoff p ∧
      (pollackCutoff p : ℝ) ≤ (p : ℝ) ^ (1 / 2 : ℝ) := by
  filter_upwards [eventually_ge_atTop 100] with p hp
  let s := p.sqrt
  let X := pollackCutoff p
  have hs10 : 10 ≤ s := by
    rw [show s = Nat.sqrt p by rfl, Nat.le_sqrt']
    norm_num
    exact hp
  have hX : X = s / 4 := rfl
  have hXpos : 0 < X := by rw [hX]; omega
  have h4X : 4 * X ≤ s := by rw [hX]; omega
  have hsX : s + 1 ≤ 8 * X := by rw [hX]; omega
  have hsSq : s ^ 2 ≤ p := Nat.sqrt_le' p
  have hsmall : 2 * X ^ 2 + X < s ^ 2 := by nlinarith
  have hsreal : (s : ℝ) ≤ Real.sqrt (p : ℝ) :=
    Real.nat_sqrt_le_real_sqrt
  have hsrealUpper : Real.sqrt (p : ℝ) ≤ (s + 1 : ℕ) :=
    by simpa [s] using (Real.real_sqrt_le_nat_sqrt_succ (a := p))
  refine ⟨hXpos, ?_, hsmall.trans_le hsSq, ?_, ?_⟩
  · nlinarith [hsSq]
  · rw [← Real.sqrt_eq_rpow]
    exact hsrealUpper.trans (by exact_mod_cast hsX)
  · rw [← Real.sqrt_eq_rpow]
    have hXs : (X : ℝ) ≤ (s : ℝ) := by
      exact_mod_cast (show X ≤ s by omega)
    exact hXs.trans hsreal

theorem eventually_pollack_log_bounds :
    ∀ᶠ p : ℕ in atTop,
      1 + Real.log (p : ℝ) ≤ (p : ℝ) ^ (1 / 4096 : ℝ) ∧
      1 + Real.log (pollackCutoff p : ℝ) ≤
        (p : ℝ) ^ (1 / 4096 : ℝ) ∧
      Real.log ((8 * p : ℕ) : ℝ) ≤ (p : ℝ) ^ (1 / 4096 : ℝ) := by
  have hlogSq := eventually_const_mul_log_sq_le_rpow
    (c := 2) (d := 1) (a := (1 / 4096 : ℝ))
    (by positivity) (by positivity) (by norm_num)
  filter_upwards [hlogSq, eventually_pollackCutoff_bounds,
    eventually_ge_atTop 8] with p hlogSq hcut hp8
  have hpReal : (0 : ℝ) < p := by positivity
  have hlogOne : (1 : ℝ) ≤ Real.log (p : ℝ) := by
    rw [Real.le_log_iff_exp_le hpReal]
    exact Real.exp_one_lt_three.le.trans (by exact_mod_cast (show 3 ≤ p by omega))
  have hbase : 1 + Real.log (p : ℝ) ≤ 2 * Real.log (p : ℝ) ^ 2 := by
    nlinarith [sq_nonneg (Real.log (p : ℝ) - 1)]
  have hpLog : 1 + Real.log (p : ℝ) ≤ (p : ℝ) ^ (1 / 4096 : ℝ) :=
    hbase.trans (by simpa using hlogSq)
  have hXReal : (0 : ℝ) < pollackCutoff p := by exact_mod_cast hcut.1
  have hXleP : (pollackCutoff p : ℝ) ≤ (p : ℝ) := by
    exact_mod_cast (show pollackCutoff p ≤ p by omega)
  have hlogX : Real.log (pollackCutoff p : ℝ) ≤ Real.log (p : ℝ) :=
    Real.log_le_log hXReal hXleP
  have hlog8le : Real.log (8 : ℝ) ≤ Real.log (p : ℝ) :=
    Real.log_le_log (by norm_num) (by exact_mod_cast hp8)
  have hlog8p : Real.log ((8 * p : ℕ) : ℝ) ≤
      (p : ℝ) ^ (1 / 4096 : ℝ) := by
    rw [show (((8 * p : ℕ) : ℝ)) = 8 * (p : ℝ) by norm_num,
      Real.log_mul (by norm_num) hpReal.ne']
    calc
      Real.log (8 : ℝ) + Real.log (p : ℝ) ≤ 2 * Real.log (p : ℝ) := by linarith
      _ ≤ 2 * Real.log (p : ℝ) ^ 2 := by nlinarith
      _ ≤ (p : ℝ) ^ (1 / 4096 : ℝ) := by simpa using hlogSq
  have hXLogBound : 1 + Real.log (pollackCutoff p : ℝ) ≤
      (p : ℝ) ^ (1 / 4096 : ℝ) := by linarith
  exact ⟨hpLog, hXLogBound, hlog8p⟩

theorem eventually_attachedComparisonError_le_rpow :
    ∀ᶠ p : ℕ in atTop,
      attachedComparisonError p (pollackCutoff p) ≤
        400 * (p : ℝ) ^ (2041 / 4096 : ℝ) := by
  filter_upwards [eventually_pollackCutoff_bounds,
    eventually_pollack_log_bounds, eventually_ge_atTop 8] with p hcut hlog hp8
  let X := pollackCutoff p
  let P : ℝ := p
  let A : ℝ := P ^ (1 / 2 : ℝ)
  let R : ℝ := P ^ (1 / 4096 : ℝ)
  let E : ℝ := P ^ (2041 / 4096 : ℝ)
  have hPpos : 0 < P := by dsimp [P]; positivity
  have hPone : 1 ≤ P := by
    dsimp [P]
    exact_mod_cast (show 1 ≤ p by omega)
  have hXpos : (0 : ℝ) < X := by exact_mod_cast hcut.1
  have hXupper : (X : ℝ) ≤ A := by simpa [X, A, P] using hcut.2.2.2.2
  have hLp : 1 + Real.log P ≤ R := by simpa [P, R] using hlog.1
  have hLx : 1 + Real.log (X : ℝ) ≤ R := by simpa [X, P, R] using hlog.2.1
  have hLq : Real.log ((8 * p : ℕ) : ℝ) ≤ R := by simpa [P, R] using hlog.2.2
  have hRpos : 0 < R := Real.rpow_pos_of_pos hPpos _
  have hEpos : 0 < E := Real.rpow_pos_of_pos hPpos _
  have hsavePos : (0 : ℝ) < saving p := by exact_mod_cast saving_pos p
  have hrootPos : 0 < P ^ (1 / 512 : ℝ) := Real.rpow_pos_of_pos hPpos _
  have hsaveLower : P ^ (1 / 512 : ℝ) < 2 * saving p := by
    simpa [P] using rpow_one_div_512_lt_two_mul_saving p
  have hsaveInv : 1 / (saving p : ℝ) ≤ 2 * P ^ (-(1 / 512 : ℝ)) := by
    have hdiv : 1 / (saving p : ℝ) ≤ 2 / P ^ (1 / 512 : ℝ) :=
      (div_le_div_iff₀ hsavePos hrootPos).2 (by linarith)
    calc
      1 / (saving p : ℝ) ≤ 2 / P ^ (1 / 512 : ℝ) := hdiv
      _ = 2 * P ^ (-(1 / 512 : ℝ)) := by
        rw [Real.rpow_neg hPpos.le]
        ring
  have hprefix0 : 0 ≤ prefixError p := by dsimp [prefixError]; positivity
  have hpowPrefixOne : 1 ≤ P ^ (63 / 128 : ℝ) :=
    Real.one_le_rpow hPone (by norm_num)
  have hprefix : prefixError p ≤ 40 * P ^ (63 / 128 : ℝ) := by
    dsimp [prefixError, P]
    nlinarith
  have hpow (a b : ℝ) (hab : a ≤ b) : P ^ a ≤ P ^ b :=
    Real.rpow_le_rpow_of_exponent_le hPone hab
  have hmulAneg : A * P ^ (-(1 / 512 : ℝ)) =
      P ^ (1 / 2 - 1 / 512 : ℝ) := by
    dsimp [A]
    rw [← Real.rpow_add hPpos]
    congr 1
  have hmulARneg : A * R * P ^ (-(1 / 512 : ℝ)) = E := by
    dsimp [A, R, E]
    rw [← Real.rpow_add hPpos, ← Real.rpow_add hPpos]
    congr 1
    ring
  have hmulPrefixR : P ^ (63 / 128 : ℝ) * R =
      P ^ (2017 / 4096 : ℝ) := by
    dsimp [R]
    rw [← Real.rpow_add hPpos]
    congr 1
    ring
  have hA_sq : A * A = P := by
    dsimp [A]
    calc
      P ^ (1 / 2 : ℝ) * P ^ (1 / 2 : ℝ) =
          P ^ ((1 / 2 : ℝ) + 1 / 2) := (Real.rpow_add hPpos _ _).symm
      _ = P ^ (1 : ℝ) := by norm_num
      _ = P := Real.rpow_one P
  have ht1 : ((X : ℝ) / 2) *
      (16 * (1 + Real.log (p : ℝ)) / saving p) ≤ 16 * E := by
    calc
      ((X : ℝ) / 2) * (16 * (1 + Real.log (p : ℝ)) / saving p) =
          8 * (X : ℝ) * (1 + Real.log P) * (1 / (saving p : ℝ)) := by
        dsimp [P]
        ring
      _ ≤ 8 * A * R * (2 * P ^ (-(1 / 512 : ℝ))) := by gcongr
      _ = 16 * E := by rw [← hmulARneg]; ring
  have ht2 : ((X : ℝ) / 2) * (2 * prefixError p / X) = prefixError p := by
    field_simp [hXpos.ne']
  have hsqrt8 : Real.sqrt (8 : ℝ) ≤ 3 := by
    nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 8), Real.sqrt_nonneg 8]
  have hsqrtq : Real.sqrt ((8 * p : ℕ) : ℝ) ≤ 3 * A := by
    calc
      Real.sqrt ((8 * p : ℕ) : ℝ) =
          Real.sqrt 8 * Real.sqrt P := by
        rw [show (((8 * p : ℕ) : ℝ)) = 8 * P by simp [P],
          Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 8)]
      _ ≤ 3 * Real.sqrt P :=
        mul_le_mul_of_nonneg_right hsqrt8 (Real.sqrt_nonneg _)
      _ = 3 * A := by rw [Real.sqrt_eq_rpow]
  have hpminus : (0 : ℝ) < (p - 1 : ℕ) := by exact_mod_cast (show 0 < p - 1 by omega)
  have hpratio : P / (p - 1 : ℕ) ≤ 2 := by
    rw [div_le_iff₀ hpminus]
    dsimp [P]
    exact_mod_cast (show p ≤ 2 * (p - 1) by omega)
  have ht3 : ((X : ℝ) / 2) *
      (4 * Real.sqrt ((8 * p : ℕ) : ℝ) *
        Real.log ((8 * p : ℕ) : ℝ) / (p - 1 : ℕ)) ≤ 12 * E := by
    calc
      ((X : ℝ) / 2) *
          (4 * Real.sqrt ((8 * p : ℕ) : ℝ) *
            Real.log ((8 * p : ℕ) : ℝ) / (p - 1 : ℕ)) =
          2 * (X : ℝ) * Real.sqrt ((8 * p : ℕ) : ℝ) *
            Real.log ((8 * p : ℕ) : ℝ) / (p - 1 : ℕ) := by ring
      _ ≤ 2 * A * (3 * A) * R / (p - 1 : ℕ) := by gcongr
      _ = 6 * (A * A) * R / (p - 1 : ℕ) := by ring
      _ = 6 * R * (P / (p - 1 : ℕ)) := by rw [hA_sq]; ring
      _ ≤ 6 * R * 2 :=
        mul_le_mul_of_nonneg_left hpratio (by positivity)
      _ = 12 * R := by ring
      _ ≤ 12 * E := by
        gcongr
        exact hpow _ _ (by norm_num)
  have ht4 : 64 * (X : ℝ) / saving p ≤ 128 * E := by
    calc
      64 * (X : ℝ) / saving p = 64 * (X : ℝ) * (1 / (saving p : ℝ)) := by ring
      _ ≤ 64 * A * (2 * P ^ (-(1 / 512 : ℝ))) := by gcongr
      _ = 128 * P ^ (1 / 2 - 1 / 512 : ℝ) := by rw [← hmulAneg]; ring
      _ ≤ 128 * E := by
        gcongr
        exact hpow _ _ (by norm_num)
  have ht5 : 4 * prefixError p * (1 + Real.log (X : ℝ)) ≤ 160 * E := by
    calc
      4 * prefixError p * (1 + Real.log (X : ℝ)) ≤
          4 * (40 * P ^ (63 / 128 : ℝ)) * R := by gcongr
      _ = 160 * P ^ (2017 / 4096 : ℝ) := by rw [← hmulPrefixR]; ring
      _ ≤ 160 * E := by
        gcongr
        exact hpow _ _ (by norm_num)
  have htPrefix : prefixError p ≤ 40 * E :=
    hprefix.trans (mul_le_mul_of_nonneg_left
      (hpow _ _ (by norm_num)) (by norm_num))
  rw [attachedComparisonError, attachedTailError, attachedRemainderError]
  change
    ((X : ℝ) / 2) *
        (16 * (1 + Real.log (p : ℝ)) / saving p +
          2 * prefixError p / X +
          4 * Real.sqrt ((8 * p : ℕ) : ℝ) *
            Real.log ((8 * p : ℕ) : ℝ) / (p - 1 : ℕ)) +
      (64 * (X : ℝ) / saving p +
        4 * prefixError p * (1 + Real.log (X : ℝ))) ≤ 400 * E
  calc
    ((X : ℝ) / 2) *
          (16 * (1 + Real.log (p : ℝ)) / saving p +
            2 * prefixError p / X +
            4 * Real.sqrt ((8 * p : ℕ) : ℝ) *
              Real.log ((8 * p : ℕ) : ℝ) / (p - 1 : ℕ)) +
        (64 * (X : ℝ) / saving p +
          4 * prefixError p * (1 + Real.log (X : ℝ))) =
        ((X : ℝ) / 2) * (16 * (1 + Real.log (p : ℝ)) / saving p) +
        ((X : ℝ) / 2) * (2 * prefixError p / X) +
        ((X : ℝ) / 2) *
          (4 * Real.sqrt ((8 * p : ℕ) : ℝ) *
            Real.log ((8 * p : ℕ) : ℝ) / (p - 1 : ℕ)) +
        64 * (X : ℝ) / saving p +
        4 * prefixError p * (1 + Real.log (X : ℝ)) := by ring
    _ ≤ 16 * E + prefixError p + 12 * E + 128 * E + 160 * E := by
      rw [ht2]
      gcongr
    _ ≤ 400 * E := by nlinarith

noncomputable def attachedMainLower (p : ℕ) : ℝ :=
  ((pollackCutoff p : ℝ) / 2) *
    ((8 * p : ℕ) : ℝ) ^ (-(1 / 1024 : ℝ))

theorem eventually_sparse_and_error_lt_main :
    ∀ᶠ p : ℕ in atTop,
      2 * (Nat.sqrt (pollackCutoff p) + 1 : ℕ) +
          attachedComparisonError p (pollackCutoff p) <
        attachedMainLower p := by
  have hcompare := eventually_const_mul_nat_rpow_le_const_mul_nat_rpow
    (C := 405) (d := (1 / 128 : ℝ))
    (a := (2041 / 4096 : ℝ)) (b := (2044 / 4096 : ℝ))
    (by positivity) (by positivity) (by norm_num)
  filter_upwards [eventually_pollackCutoff_bounds,
    eventually_attachedComparisonError_le_rpow, hcompare,
    eventually_ge_atTop 8] with p hcut herr hcompare hp8
  let X := pollackCutoff p
  let P : ℝ := p
  let A : ℝ := P ^ (1 / 2 : ℝ)
  let E : ℝ := P ^ (2041 / 4096 : ℝ)
  have hPpos : 0 < P := by dsimp [P]; positivity
  have hPone : 1 ≤ P := by
    dsimp [P]
    exact_mod_cast (show 1 ≤ p by omega)
  have hXpos : (0 : ℝ) < X := by exact_mod_cast hcut.1
  have hXupper : (X : ℝ) ≤ A := by simpa [X, A, P] using hcut.2.2.2.2
  have hXlower : A ≤ 8 * (X : ℝ) := by simpa [X, A, P] using hcut.2.2.2.1
  have hEpos : 0 < E := Real.rpow_pos_of_pos hPpos _
  have hpow (a b : ℝ) (hab : a ≤ b) : P ^ a ≤ P ^ b :=
    Real.rpow_le_rpow_of_exponent_le hPone hab
  have hsqrtA : Real.sqrt A = P ^ (1 / 4 : ℝ) := by
    dsimp [A]
    rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hPpos.le]
    congr 1
    ring
  have hsqrtX : (Nat.sqrt X : ℝ) ≤ P ^ (1 / 4 : ℝ) := by
    calc
      (Nat.sqrt X : ℝ) ≤ Real.sqrt (X : ℝ) :=
        Real.nat_sqrt_le_real_sqrt
      _ ≤ Real.sqrt A := Real.sqrt_le_sqrt hXupper
      _ = P ^ (1 / 4 : ℝ) := hsqrtA
  have hquarterOne : 1 ≤ P ^ (1 / 4 : ℝ) :=
    Real.one_le_rpow hPone (by norm_num)
  have hsparse : (2 * (Nat.sqrt X + 1 : ℕ) : ℕ) ≤ 4 * E := by
    have hsparseReal : ((2 * (Nat.sqrt X + 1 : ℕ) : ℕ) : ℝ) ≤
        4 * P ^ (1 / 4 : ℝ) := by
      push_cast
      nlinarith
    exact hsparseReal.trans
      (mul_le_mul_of_nonneg_left (hpow _ _ (by norm_num)) (by norm_num))
  have h8pow : (1 / 8 : ℝ) ≤ (8 : ℝ) ^ (-(1 / 1024 : ℝ)) := by
    calc
      (1 / 8 : ℝ) = (8 : ℝ) ^ (-(1 : ℝ)) := by
        rw [Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 8), Real.rpow_one]
        norm_num
      _ ≤ (8 : ℝ) ^ (-(1 / 1024 : ℝ)) :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
  have hqpow : (1 / 8 : ℝ) * P ^ (-(1 / 1024 : ℝ)) ≤
      ((8 * p : ℕ) : ℝ) ^ (-(1 / 1024 : ℝ)) := by
    rw [show (((8 * p : ℕ) : ℝ)) = 8 * P by simp [P],
      Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 8) hPpos.le]
    exact mul_le_mul_of_nonneg_right h8pow
      (Real.rpow_nonneg hPpos.le (-(1 / 1024 : ℝ)))
  have hmainPower :
      A * P ^ (-(1 / 1024 : ℝ)) = P ^ (2044 / 4096 : ℝ) := by
    dsimp [A]
    rw [← Real.rpow_add hPpos]
    congr 1
    ring
  have hmain : (1 / 128 : ℝ) * P ^ (2044 / 4096 : ℝ) ≤
      attachedMainLower p := by
    rw [attachedMainLower]
    change (1 / 128 : ℝ) * P ^ (2044 / 4096 : ℝ) ≤
      ((X : ℝ) / 2) * ((8 * p : ℕ) : ℝ) ^ (-(1 / 1024 : ℝ))
    calc
      (1 / 128 : ℝ) * P ^ (2044 / 4096 : ℝ) =
          (A / 16) * ((1 / 8 : ℝ) * P ^ (-(1 / 1024 : ℝ))) := by
        rw [← hmainPower]
        ring
      _ ≤ ((X : ℝ) / 2) * ((8 * p : ℕ) : ℝ) ^ (-(1 / 1024 : ℝ)) := by
        have hcoef : A / 16 ≤ (X : ℝ) / 2 := by linarith
        exact mul_le_mul hcoef hqpow (by positivity) (by positivity)
  have htotal :
      (2 * (Nat.sqrt X + 1 : ℕ) : ℕ) +
          attachedComparisonError p X ≤ 404 * E := by
    have herr' : attachedComparisonError p X ≤ 400 * E := by
      simpa [X, E, P] using herr
    nlinarith
  have hstrict : 404 * E < 405 * E := by nlinarith
  have hcompare' : 405 * E ≤ (1 / 128 : ℝ) * P ^ (2044 / 4096 : ℝ) := by
    simpa [E, P] using hcompare
  have hfinal := htotal.trans_lt (hstrict.trans_le (hcompare'.trans hmain))
  norm_num at hfinal ⊢
  simpa [X] using hfinal

theorem eventually_exists_attached_split_prime :
    ∀ᶠ p : ℕ in atTop, ∀ hp : p.Prime,
      ∃ ell : ℕ, ell.Prime ∧ ell ≤ pollackCutoff p ∧
        Erdos1141.attachedQuadraticCharacter (2 * p) (8 * p)
          (by exact ⟨1, by ring⟩) ell = 1 := by
  have hL := Erdos1140.eventually_quadratic_LFunction_one_re_ge_rpow
  have h8 : Tendsto (fun p : ℕ ↦ 8 * p) atTop atTop := by
    simpa only [Nat.nsmul_eq_mul, id_eq] using
      (tendsto_id.nsmul_atTop (M := ℕ) (n := 8)
        (show (0 : ℕ) < 8 by norm_num))
  have hL8 := h8.eventually hL
  filter_upwards [eventually_pollackCutoff_bounds,
    eventually_attached_comparison, eventually_sparse_and_error_lt_main,
    hL8, eventually_ge_atTop 3] with p hcut hcompare hsmall hLq hp3
  intro hp
  let X := pollackCutoff p
  let χ₀ := Erdos1141.attachedQuadraticCharacter (2 * p) (8 * p)
    (by exact ⟨1, by ring⟩)
  letI : NeZero (8 * p) := ⟨mul_ne_zero (by norm_num) hp.ne_zero⟩
  let χ := χ₀.toDirichletCharacterComplex
  have hp2 : p ≠ 2 := by omega
  have hχne : χ ≠ 1 := by
    simpa [χ, χ₀] using attached_character_complex_ne_one hp hp2
  have hχsq : χ ^ 2 = 1 := by
    simpa [χ, χ₀] using attached_character_complex_sq_eq_one hp
  have hLlower : ((8 * p : ℕ) : ℝ) ^ (-(1 / 1024 : ℝ)) ≤
      (DirichletCharacter.LFunction χ (1 : ℂ)).re := hLq χ hχne hχsq
  have hcomparison :
      ‖quadraticZetaLinearSmoothedSum χ X -
          ((X : ℂ) / 2) * DirichletCharacter.LFunction χ (1 : ℂ)‖ ≤
        attachedComparisonError p X := by
    simpa [X, χ, χ₀] using hcompare hp X hcut.1 hcut.2.1 hχne
  by_contra hno
  push_neg at hno
  have hnosplit : ∀ ell : ℕ, ell.Prime → ell ≤ X → χ₀ ell ≠ 1 := by
    intro ell hell hellX
    exact hno ell hell (by simpa [X] using hellX)
  have hsparse : ‖quadraticZetaLinearSmoothedSum χ X‖ ≤
      2 * (X.sqrt + 1 : ℕ) := by
    simpa [X, χ, χ₀] using
      attached_smoothed_sum_norm_le hp hcut.1
        (lt_trans (Nat.lt_succ_self X) hcut.2.1) hnosplit
  let L := DirichletCharacter.LFunction χ (1 : ℂ)
  let A : ℂ := ((X : ℂ) / 2) * L
  let T : ℂ := quadraticZetaLinearSmoothedSum χ X
  have hqpowNonneg : 0 ≤ ((8 * p : ℕ) : ℝ) ^ (-(1 / 1024 : ℝ)) :=
    Real.rpow_nonneg (by positivity) _
  have hXhalf : 0 ≤ (X : ℝ) / 2 := by positivity
  have hnormLower : attachedMainLower p ≤ ‖A‖ := by
    have hreNorm : L.re ≤ ‖L‖ := Complex.re_le_norm L
    have hscale : ‖((X : ℂ) / 2)‖ = (X : ℝ) / 2 := by
      rw [norm_div, Complex.norm_natCast]
      norm_num
    change attachedMainLower p ≤ ‖((X : ℂ) / 2) * L‖
    rw [norm_mul, hscale]
    rw [attachedMainLower]
    change ((X : ℝ) / 2) * ((8 * p : ℕ) : ℝ) ^ (-(1 / 1024 : ℝ)) ≤
      ((X : ℝ) / 2) * ‖L‖
    exact mul_le_mul_of_nonneg_left (hLlower.trans hreNorm) hXhalf
  have htriangle : ‖A‖ ≤ ‖T‖ + ‖T - A‖ := by
    calc
      ‖A‖ = ‖T - (T - A)‖ := by ring_nf
      _ ≤ ‖T‖ + ‖T - A‖ := norm_sub_le _ _
  have hupper : ‖A‖ ≤
      2 * (X.sqrt + 1 : ℕ) + attachedComparisonError p X := by
    calc
      ‖A‖ ≤ ‖T‖ + ‖T - A‖ := htriangle
      _ ≤ 2 * (X.sqrt + 1 : ℕ) + attachedComparisonError p X := by
        exact add_le_add hsparse (by simpa [T, A, L] using hcomparison)
  have : attachedMainLower p < attachedMainLower p :=
    hnormLower.trans_lt (hupper.trans_lt (by simpa [X] using hsmall))
  exact (lt_irrefl _ this)

private lemma quadResidueMod_of_isSquare_zmod {d ell : ℕ}
    (h : IsSquare (d : ZMod ell)) :
    Erdos1141.QuadResidueMod d ell := by
  rcases h with ⟨x, hx⟩
  cases ell with
  | zero =>
      refine ⟨x.val, ?_⟩
      rw [Nat.ModEq, Nat.mod_zero, Nat.mod_zero]
      simpa [pow_two] using congrArg ZMod.val hx.symm
  | succ ell =>
      refine ⟨x.val, ?_⟩
      rw [← ZMod.natCast_eq_natCast_iff]
      calc
        (((x.val ^ 2 : ℕ) : ZMod (ell + 1))) =
            (((x.val : ℕ) : ZMod (ell + 1)) ^ 2) := by simp
        _ = x ^ 2 := by simp
        _ = (d : ZMod (ell + 1)) := by simpa [pow_two] using hx.symm

lemma attached_quadratic_character_spec
    {d m ell : ℕ} (hdvd : 4 * d ∣ m)
    (hell : ell.Prime)
    (hχ : Erdos1141.attachedQuadraticCharacter d m hdvd ell = 1) :
    ell ≠ 2 ∧ ¬ ell ∣ m ∧ Erdos1141.QuadResidueMod d ell := by
  have hcop : Nat.Coprime ell m := by
    by_contra hnot
    have hzero : Erdos1141.attachedQuadraticCharacter d m hdvd ell = 0 := by
      simp [Erdos1141.attachedQuadraticCharacter, hnot]
    rw [hzero] at hχ
    norm_num at hχ
  have hellndvd : ¬ ell ∣ m := (hell.coprime_iff_not_dvd).1 hcop
  have hell2 : ell ≠ 2 := by
    intro hell2
    apply hellndvd
    simpa [hell2] using Erdos1141.two_dvd_of_four_d_dvd hdvd
  have hJacobi : jacobiSym (d : ℤ) ell = 1 := by
    rw [Erdos1141.attachedQuadraticCharacter_apply_coprime hdvd hcop] at hχ
    exact hχ
  letI : Fact ell.Prime := ⟨hell⟩
  have hsqInt : IsSquare ((d : ℤ) : ZMod ell) :=
    ZMod.isSquare_of_jacobiSym_eq_one (a := (d : ℤ)) (p := ell) hJacobi
  have hsq : IsSquare (d : ZMod ell) := by
    rcases hsqInt with ⟨x, hx⟩
    refine ⟨x, ?_⟩
    simpa using hx
  exact ⟨hell2, hellndvd, quadResidueMod_of_isSquare_zmod hsq⟩

lemma solvable_two_of_attached_value_one
    {p ell : ℕ} (hell : ell.Prime)
    (hχ : Erdos1141.attachedQuadraticCharacter (2 * p) (8 * p)
      (by exact ⟨1, by ring⟩) ell = 1) :
    Erdos1140.Solvable2X2EqNMod p ell := by
  obtain ⟨_hell2, hellndvd, hres⟩ :=
    attached_quadratic_character_spec
      (d := 2 * p) (m := 8 * p) (ell := ell)
      (by exact ⟨1, by ring⟩) hell hχ
  have helln : ¬ ell ∣ 2 * p := by
    intro hdvd
    apply hellndvd
    exact dvd_trans hdvd (by exact ⟨4, by ring⟩)
  have hsolv := Erdos1141.solvable_of_squarefree_part
    (a := 2) (n := p) (u := 1) (d := 2 * p) (p := ell)
    (by ring) hell helln hres
  simpa [Erdos1140.Solvable2X2EqNMod,
    Erdos1141.SolvableAX2EqNMod] using hsolv

theorem eventually_small_solvable_prime :
    ∀ᶠ n : ℕ in atTop, n.Prime →
      ∃ ell : ℕ, ell.Prime ∧ 2 * ell ^ 2 + ell < n ∧
        Erdos1140.Solvable2X2EqNMod n ell := by
  filter_upwards [eventually_exists_attached_split_prime,
    eventually_pollackCutoff_bounds] with n hsplit hcut
  intro hn
  obtain ⟨ell, hell, hellX, hχ⟩ := hsplit hn
  refine ⟨ell, hell, ?_, solvable_two_of_attached_value_one hell hχ⟩
  have hsquare : ell ^ 2 ≤ pollackCutoff n ^ 2 :=
    Nat.pow_le_pow_left hellX 2
  nlinarith [hcut.2.2.1]

end Erdos1140
