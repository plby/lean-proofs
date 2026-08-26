import ErdosProblems.Erdos67b.EulerPrincipal
import ErdosProblems.Erdos67b.EulerQuantitative
import ErdosProblems.Erdos67b.TruncatedEulerLSeries

/-!
# Lower bound for the singular series

Finite pretentious distance from `h` to `1` prevents the singular Euler
product from losing more than a fixed multiplicative constant relative to
zeta.  This file proves the resulting lower bound of order `log X` at Tao's
exponent.
-/

open scoped BigOperators Topology
open Complex Finset Filter Asymptotics

namespace Erdos67b.EulerLower

noncomputable section

open Erdos67b.EulerResidue
open Erdos67b.EulerQuantitative
open Erdos67b.TruncatedEulerLSeries

def weightedEulerLogTerm (h : ℕ →*₀ ℂ) (u : ℝ)
    (p : Nat.Primes) : ℂ :=
  -Complex.log (1 - h p * (p : ℂ) ^ (-(u : ℂ)))

def zetaEulerLogTerm (u : ℝ) (p : Nat.Primes) : ℂ :=
  -Complex.log (1 - (p : ℂ) ^ (-(u : ℂ)))

/-- Local real-part comparison.  Its linear loss is precisely the
pretentious-distance summand; both logarithmic Taylor remainders are
quadratic. -/
theorem weightedEulerLogTerm_re_add_error_ge
    {h : ℕ →*₀ ℂ} (hh : HasUnitNorm h)
    {u : ℝ} (hu : 1 < u) (p : Nat.Primes) :
    (zetaEulerLogTerm u p).re -
        ((1 - (h p).re) * (p : ℝ) ^ (-u) +
          2 * ((p : ℝ) ^ (-u)) ^ 2) ≤
      (weightedEulerLogTerm h u p).re := by
  let zR : ℝ := (p : ℝ) ^ (-u)
  let z : ℂ := (p : ℂ) ^ (-(u : ℂ))
  let a : ℂ := h p * z
  let ra : ℂ := -Complex.log (1 - a) - a
  let rb : ℂ := -Complex.log (1 - z) - z
  have hzNorm : ‖z‖ = zR := by
    simpa only [z, zR] using norm_prime_cpow_neg_real u p
  have hzHalf : ‖z‖ ≤ 1 / 2 :=
    hzNorm.trans_le (prime_rpow_neg_le_half hu p)
  have haNorm : ‖a‖ = ‖z‖ := by
    simp only [a, norm_mul, hh p.prop.ne_zero, one_mul]
  have hra : ‖ra‖ ≤ ‖z‖ ^ 2 := by
    exact (norm_neg_log_one_sub_sub_self_le_sq
      (haNorm.le.trans hzHalf)).trans_eq (by rw [haNorm])
  have hrb : ‖rb‖ ≤ ‖z‖ ^ 2 :=
    norm_neg_log_one_sub_sub_self_le_sq hzHalf
  have hzCast : z = (zR : ℂ) := by
    dsimp only [z, zR]
    rw [show -(u : ℂ) = ((-u : ℝ) : ℂ) by push_cast; ring]
    exact (Complex.ofReal_cpow (Nat.cast_nonneg p) (-u)).symm
  have haRe : a.re = (h p).re * zR := by
    simp only [a, hzCast, mul_re, ofReal_re, ofReal_im, mul_zero, sub_zero]
  have hweighted : weightedEulerLogTerm h u p = a + ra := by
    unfold weightedEulerLogTerm
    dsimp only [ra, a, z]
    ring
  have hzeta : zetaEulerLogTerm u p = z + rb := by
    unfold zetaEulerLogTerm
    dsimp only [rb, z]
    ring
  rw [hweighted, hzeta]
  simp only [add_re, hzCast, ofReal_re, haRe]
  have hraRe : -‖ra‖ ≤ ra.re := by
    have h := Complex.re_le_norm (-ra)
    simp only [neg_re, norm_neg] at h
    linarith
  have hrbRe : rb.re ≤ ‖rb‖ := Complex.re_le_norm rb
  rw [hzNorm] at hra hrb
  dsimp only [zR]
  nlinarith

theorem summable_weightedEulerLogTerm {h : ℕ →*₀ ℂ}
    (hh : HasUnitNorm h) {u : ℝ} (hu : 1 < u) :
    Summable (weightedEulerLogTerm h u) := by
  have hs : (1 : ℝ) < ((u : ℂ)).re := by simpa
  have hraw : Summable (fun p : Nat.Primes ↦
      h p * (p : ℂ) ^ (-(u : ℂ))) := by
    have hnat := (summable_norm_weightedSummandHom hh hs).of_norm
    have hsub := hnat.subtype Nat.Prime
    refine hsub.congr ?_
    intro p
    change weightedSummandHom h _ p = _
    exact weightedSummandHom_apply h _ p
  exact hraw.clog_one_sub.neg

theorem summable_zetaEulerLogTerm {u : ℝ} (hu : 1 < u) :
    Summable (zetaEulerLogTerm u) := by
  have hs : (1 : ℝ) < ((u : ℂ)).re := by simpa
  have hraw : Summable (fun p : Nat.Primes ↦
      (p : ℂ) ^ (-(u : ℂ))) := by
    have hnat := (summable_riemannZetaSummand hs).of_norm
    have hsub := hnat.subtype Nat.Prime
    refine hsub.congr ?_
    intro p
    change riemannZetaSummandHom _ p = _
    rfl
  exact hraw.clog_one_sub.neg

def pretentiousLinearTerm (h : ℕ →*₀ ℂ) (u : ℝ)
    (p : Nat.Primes) : ℝ :=
  (1 - (h p).re) * (p : ℝ) ^ (-u)

/-- Finite pretentious distance bounds the complete linear real-part loss,
uniformly for every real exponent to the right of one. -/
theorem summable_pretentiousLinearTerm_and_tsum_le
    {h : ℕ →*₀ ℂ} (hh : HasUnitNorm h) {D u : ℝ}
    (hD : ∀ X : ℕ, pretentiousMass h X ≤ D) (hu : 1 < u) :
    Summable (pretentiousLinearTerm h u) ∧
      (∑' p : Nat.Primes, pretentiousLinearTerm h u p) ≤ D := by
  have hdist := summable_primeDistanceSquare_and_tsum_le hh hD
  have hmajor : ∀ p : Nat.Primes,
      pretentiousLinearTerm h u p ≤ (1 / 2 : ℝ) * primeDistanceSquare h p := by
    intro p
    have hpOne : (1 : ℝ) ≤ p := by exact_mod_cast p.prop.one_le
    have hpow : (p : ℝ) ^ (-u) ≤ (p : ℝ) ^ (-1 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le hpOne (by linarith)
    have hnonneg : 0 ≤ 1 - (h p).re := by
      exact sub_nonneg.mpr ((h p).re_le_norm.trans_eq (hh p.prop.ne_zero))
    have hid : 1 - (h p).re = ‖h p - 1‖ ^ 2 / 2 := by
      have hsquare := norm_sub_one_sq hh p.prop.ne_zero
      linarith
    unfold pretentiousLinearTerm primeDistanceSquare
    rw [hid]
    calc
      ‖h p - 1‖ ^ 2 / 2 * (p : ℝ) ^ (-u) ≤
          ‖h p - 1‖ ^ 2 / 2 * (p : ℝ) ^ (-1 : ℝ) := by
        exact mul_le_mul_of_nonneg_left hpow (by positivity)
      _ = (1 / 2 : ℝ) * (‖h p - 1‖ ^ 2 / (p : ℝ)) := by
        rw [Real.rpow_neg_one]
        ring
  have hmajorSummable : Summable
      (fun p : Nat.Primes ↦ (1 / 2 : ℝ) * primeDistanceSquare h p) :=
    hdist.1.mul_left (1 / 2 : ℝ)
  have hlinear : Summable (pretentiousLinearTerm h u) :=
    hmajorSummable.of_nonneg_of_le
      (fun p ↦ by
        unfold pretentiousLinearTerm
        exact mul_nonneg
          (sub_nonneg.mpr ((h p).re_le_norm.trans_eq (hh p.prop.ne_zero)))
          (Real.rpow_nonneg (by positivity) _))
      hmajor
  refine ⟨hlinear, ?_⟩
  calc
    (∑' p : Nat.Primes, pretentiousLinearTerm h u p) ≤
        ∑' p : Nat.Primes, (1 / 2 : ℝ) * primeDistanceSquare h p :=
      Summable.tsum_le_tsum hmajor hlinear hmajorSummable
    _ = (1 / 2 : ℝ) *
        ∑' p : Nat.Primes, primeDistanceSquare h p :=
      hdist.1.tsum_mul_left (1 / 2 : ℝ)
    _ ≤ (1 / 2 : ℝ) * (2 * D) :=
      mul_le_mul_of_nonneg_left hdist.2 (by norm_num)
    _ = D := by ring

/-- Complete real-part comparison of the two Euler logarithms. -/
theorem tsum_weightedEulerLog_re_ge_zeta_sub
    {h : ℕ →*₀ ℂ} (hh : HasUnitNorm h) {D u : ℝ}
    (hD : ∀ X : ℕ, pretentiousMass h X ≤ D) (hu : 1 < u) :
    (∑' p : Nat.Primes, zetaEulerLogTerm u p).re -
        (D + primeQuadraticConstant) ≤
      (∑' p : Nat.Primes, weightedEulerLogTerm h u p).re := by
  have hw := summable_weightedEulerLogTerm hh hu
  have hz := summable_zetaEulerLogTerm hu
  have hlin := summable_pretentiousLinearTerm_and_tsum_le hh hD hu
  have hquad := summable_primeQuadraticError hu
  let err : Nat.Primes → ℝ := fun p ↦
    pretentiousLinearTerm h u p + 2 * ((p : ℝ) ^ (-u)) ^ 2
  have herr : Summable err := hlin.1.add hquad
  have hwre : Summable (fun p : Nat.Primes ↦
      (weightedEulerLogTerm h u p).re) := by
    exact (hw.map Complex.reCLM Complex.reCLM.continuous).congr
      (fun _ ↦ rfl)
  have hzre : Summable (fun p : Nat.Primes ↦
      (zetaEulerLogTerm u p).re) := by
    exact (hz.map Complex.reCLM Complex.reCLM.continuous).congr
      (fun _ ↦ rfl)
  have hsum :
      (∑' p : Nat.Primes, (zetaEulerLogTerm u p).re) -
          (∑' p : Nat.Primes, err p) ≤
        ∑' p : Nat.Primes, (weightedEulerLogTerm h u p).re := by
    rw [← hzre.tsum_sub herr]
    refine Summable.tsum_le_tsum ?_ (hzre.sub herr) hwre
    intro p
    exact weightedEulerLogTerm_re_add_error_ge hh hu p
  have herrBound : (∑' p : Nat.Primes, err p) ≤
      D + primeQuadraticConstant := by
    dsimp only [err]
    rw [hlin.1.tsum_add hquad]
    exact add_le_add hlin.2 (tsum_primeQuadraticError_le_constant hu)
  rw [← Complex.re_tsum hz, ← Complex.re_tsum hw] at hsum
  exact (sub_le_sub_left herrBound _).trans hsum

theorem exp_tsum_weightedEulerLog {h : ℕ →*₀ ℂ}
    (hh : HasUnitNorm h) {u : ℝ} (hu : 1 < u) :
    Complex.exp (∑' p : Nat.Primes, weightedEulerLogTerm h u p) =
      LSeries h (u : ℂ) := by
  simpa only [weightedEulerLogTerm] using
    weightedEulerProduct_exp_log hh (by simpa using hu)

theorem exp_tsum_zetaEulerLog {u : ℝ} (hu : 1 < u) :
    Complex.exp (∑' p : Nat.Primes, zetaEulerLogTerm u p) =
      riemannZeta (u : ℂ) := by
  simpa only [zetaEulerLogTerm] using
    riemannZeta_eulerProduct_exp_log (by simpa using hu)

/-- Multiplicative comparison of the singular series with zeta. -/
theorem exp_neg_mul_norm_riemannZeta_le_norm_LSeries
    {h : ℕ →*₀ ℂ} (hh : HasUnitNorm h) {D u : ℝ}
    (hD : ∀ X : ℕ, pretentiousMass h X ≤ D) (hu : 1 < u) :
    Real.exp (-(D + primeQuadraticConstant)) *
        ‖riemannZeta (u : ℂ)‖ ≤
      ‖LSeries h (u : ℂ)‖ := by
  rw [← exp_tsum_weightedEulerLog hh hu,
    ← exp_tsum_zetaEulerLog hu, Complex.norm_exp, Complex.norm_exp]
  have hre := tsum_weightedEulerLog_re_ge_zeta_sub hh hD hu
  rw [← Real.exp_add]
  apply Real.exp_le_exp.mpr
  linarith

/-! ## The same-scale comparison used in Section 4

The compactness/pretentiousness argument only controls the distance through
the particular scale `X` selected later in the proof.  The primes above `X`
cannot be discarded, since `singularSeries` is the complete Euler product.
At Tao's exponent their total weight is nevertheless bounded by the absolute
constant `shiftedEulerTailConstant`. -/

/-- At Tao's exponent, a pretentious-mass bound through `X` controls the
complete linear loss.  The uncontrolled primes above `X` cost only an
absolute constant. -/
theorem tsum_pretentiousLinearTerm_tao_le
    {h : ℕ →*₀ ℂ} (hh : HasUnitNorm h) {D : ℝ} {X : ℕ}
    (hX : 4 ≤ X) (hD : pretentiousMass h X ≤ D) :
    (∑' p : Nat.Primes, pretentiousLinearTerm h (taoExponent X) p) ≤
      D + 2 * shiftedEulerTailConstant := by
  have hX1 : 1 < X := by omega
  have hu : 1 < taoExponent X := one_lt_taoExponent hX1
  have hsum : Summable (pretentiousLinearTerm h (taoExponent X)) := by
    have hs : Summable (fun p : Nat.Primes ↦
        2 * (p : ℝ) ^ (-taoExponent X)) :=
      ((Real.summable_nat_rpow.mpr (by
        linarith : -taoExponent X < -1)).subtype Nat.Prime).mul_left 2
    refine hs.of_nonneg_of_le ?_ ?_
    · intro p
      unfold pretentiousLinearTerm
      exact mul_nonneg
        (sub_nonneg.mpr ((h p).re_le_norm.trans_eq (hh p.prop.ne_zero)))
        (Real.rpow_nonneg (by positivity) _)
    · intro p
      unfold pretentiousLinearTerm
      have hre : 1 - (h p).re ≤ 2 := by
        have hneg : -1 ≤ (h p).re := by
          have habs := Complex.abs_re_le_norm (h p)
          rw [hh p.prop.ne_zero] at habs
          exact (abs_le.mp habs).1
        linarith
      exact mul_le_mul_of_nonneg_right hre
        (Real.rpow_nonneg (by positivity) _)
  have hsplit := hsum.sum_add_tsum_subtype_compl (primeSubtypesUpTo X)
  rw [← hsplit]
  have hhead :
      ∑ p ∈ primeSubtypesUpTo X,
          pretentiousLinearTerm h (taoExponent X) p ≤
        pretentiousMass h X := by
    calc
      ∑ p ∈ primeSubtypesUpTo X,
          pretentiousLinearTerm h (taoExponent X) p ≤
          ∑ p ∈ primeSubtypesUpTo X,
            (1 - (h p).re) / (p : ℝ) := by
        apply Finset.sum_le_sum
        intro p hp
        unfold pretentiousLinearTerm
        have hpOne : (1 : ℝ) ≤ p := by exact_mod_cast p.prop.one_le
        have hpow : (p : ℝ) ^ (-taoExponent X) ≤
            (p : ℝ) ^ (-1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le hpOne (by linarith)
        have hnonneg : 0 ≤ 1 - (h p).re :=
          sub_nonneg.mpr
            ((h p).re_le_norm.trans_eq (hh p.prop.ne_zero))
        calc
          (1 - (h p).re) * (p : ℝ) ^ (-taoExponent X) ≤
              (1 - (h p).re) * (p : ℝ) ^ (-1 : ℝ) :=
            mul_le_mul_of_nonneg_left hpow hnonneg
          _ = (1 - (h p).re) / (p : ℝ) := by
            rw [Real.rpow_neg_one]
            ring
      _ = pretentiousMass h X := by
        unfold pretentiousMass
        classical
        apply Finset.sum_bij (fun p _ ↦ p.1)
        · intro p hp
          exact Nat.mem_primesLE.mpr
            ⟨mem_primeSubtypesUpTo.mp hp, p.prop⟩
        · intro p₁ hp₁ p₂ hp₂ heq
          exact Subtype.ext heq
        · intro p hp
          refine ⟨⟨p, (Nat.mem_primesLE.mp hp).2⟩, ?_, rfl⟩
          exact mem_primeSubtypesUpTo.mpr (Nat.mem_primesLE.mp hp).1
        · intro p hp
          rfl
  have htail :
      (∑' p : {p : Nat.Primes // p ∉ primeSubtypesUpTo X},
          pretentiousLinearTerm h (taoExponent X) p.1) ≤
        2 * shiftedEulerTailConstant := by
    have htailSum := hsum.subtype
      (fun p : Nat.Primes ↦ p ∉ primeSubtypesUpTo X)
    have hweightSum : Summable
        (fun p : {p : Nat.Primes // p ∉ primeSubtypesUpTo X} ↦
          2 * shiftedPrimeWeight X p.1) :=
      ((summable_shiftedPrimeWeight (show 2 ≤ X by omega)).subtype
        (fun p : Nat.Primes ↦ p ∉ primeSubtypesUpTo X)).mul_left 2
    refine (Summable.tsum_le_tsum ?_ htailSum hweightSum).trans ?_
    · intro p
      unfold pretentiousLinearTerm shiftedPrimeWeight
      have hre : 1 - (h p.1).re ≤ 2 := by
        have habs := Complex.abs_re_le_norm (h p.1)
        rw [hh p.1.prop.ne_zero] at habs
        linarith [abs_le.mp habs |>.1]
      have hexp : -taoExponent X = -(1 : ℝ) - (Real.log (X : ℝ))⁻¹ := by
        unfold taoExponent
        ring
      rw [hexp]
      exact mul_le_mul_of_nonneg_right hre
        (Real.rpow_nonneg (by positivity) _)
    · have hbase :=
        (summable_shiftedPrimeWeight (show 2 ≤ X by omega)).subtype
          (fun p : Nat.Primes ↦ p ∉ primeSubtypesUpTo X)
      rw [tsum_mul_left]
      change 2 * shiftedEulerTail X ≤ 2 * shiftedEulerTailConstant
      exact mul_le_mul_of_nonneg_left (shiftedEulerTail_le_constant hX)
        (by norm_num)
  linarith

/-- Complete Euler-log comparison from only the same-scale distance bound. -/
theorem tsum_weightedEulerLog_re_ge_zeta_sub_sameScale
    {h : ℕ →*₀ ℂ} (hh : HasUnitNorm h) {D : ℝ} {X : ℕ}
    (hX : 4 ≤ X) (hD : pretentiousMass h X ≤ D) :
    (∑' p : Nat.Primes, zetaEulerLogTerm (taoExponent X) p).re -
        (D + 2 * shiftedEulerTailConstant + primeQuadraticConstant) ≤
      (∑' p : Nat.Primes,
        weightedEulerLogTerm h (taoExponent X) p).re := by
  have hu : 1 < taoExponent X := one_lt_taoExponent (by omega)
  have hw := summable_weightedEulerLogTerm hh hu
  have hz := summable_zetaEulerLogTerm hu
  have hlin : Summable (pretentiousLinearTerm h (taoExponent X)) := by
    have hs : Summable (fun p : Nat.Primes ↦
        2 * (p : ℝ) ^ (-taoExponent X)) :=
      ((Real.summable_nat_rpow.mpr (by
        linarith : -taoExponent X < -1)).subtype Nat.Prime).mul_left 2
    refine hs.of_nonneg_of_le ?_ ?_
    · intro p
      unfold pretentiousLinearTerm
      exact mul_nonneg
        (sub_nonneg.mpr ((h p).re_le_norm.trans_eq (hh p.prop.ne_zero)))
        (Real.rpow_nonneg (by positivity) _)
    · intro p
      unfold pretentiousLinearTerm
      have habs := Complex.abs_re_le_norm (h p)
      rw [hh p.prop.ne_zero] at habs
      have hre : 1 - (h p).re ≤ 2 := by
        linarith [abs_le.mp habs |>.1]
      exact mul_le_mul_of_nonneg_right hre
        (Real.rpow_nonneg (by positivity) _)
  have hlinBound := tsum_pretentiousLinearTerm_tao_le hh hX hD
  have hquad := summable_primeQuadraticError hu
  let err : Nat.Primes → ℝ := fun p ↦
    pretentiousLinearTerm h (taoExponent X) p +
      2 * ((p : ℝ) ^ (-taoExponent X)) ^ 2
  have herr : Summable err := hlin.add hquad
  have hwre : Summable (fun p : Nat.Primes ↦
      (weightedEulerLogTerm h (taoExponent X) p).re) :=
    (hw.map Complex.reCLM Complex.reCLM.continuous).congr (fun _ ↦ rfl)
  have hzre : Summable (fun p : Nat.Primes ↦
      (zetaEulerLogTerm (taoExponent X) p).re) :=
    (hz.map Complex.reCLM Complex.reCLM.continuous).congr (fun _ ↦ rfl)
  have hsum :
      (∑' p : Nat.Primes, (zetaEulerLogTerm (taoExponent X) p).re) -
          (∑' p : Nat.Primes, err p) ≤
        ∑' p : Nat.Primes,
          (weightedEulerLogTerm h (taoExponent X) p).re := by
    rw [← hzre.tsum_sub herr]
    refine Summable.tsum_le_tsum ?_ (hzre.sub herr) hwre
    intro p
    exact weightedEulerLogTerm_re_add_error_ge hh hu p
  have herrBound : (∑' p : Nat.Primes, err p) ≤
      D + 2 * shiftedEulerTailConstant + primeQuadraticConstant := by
    dsimp only [err]
    rw [hlin.tsum_add hquad]
    linarith [tsum_primeQuadraticError_le_constant hu]
  rw [← Complex.re_tsum hz, ← Complex.re_tsum hw] at hsum
  exact (sub_le_sub_left herrBound _).trans hsum

/-- Multiplicative same-scale comparison. -/
theorem exp_neg_mul_norm_riemannZeta_le_norm_LSeries_sameScale
    {h : ℕ →*₀ ℂ} (hh : HasUnitNorm h) {D : ℝ} {X : ℕ}
    (hX : 4 ≤ X) (hD : pretentiousMass h X ≤ D) :
    Real.exp
          (-(D + 2 * shiftedEulerTailConstant + primeQuadraticConstant)) *
        ‖riemannZeta (taoExponent X : ℂ)‖ ≤
      ‖LSeries h (taoExponent X : ℂ)‖ := by
  have hu : 1 < taoExponent X := one_lt_taoExponent (by omega)
  rw [← exp_tsum_weightedEulerLog hh hu,
    ← exp_tsum_zetaEulerLog hu, Complex.norm_exp, Complex.norm_exp]
  have hre := tsum_weightedEulerLog_re_ge_zeta_sub_sameScale hh hX hD
  rw [← Real.exp_add]
  apply Real.exp_le_exp.mpr
  linarith

/-- On the real axis to the right of one, the norm of zeta is exactly its
positive real Dirichlet series. -/
theorem norm_riemannZeta_real_eq_realZetaSum {u : ℝ} (hu : 1 < u) :
    ‖riemannZeta (u : ℂ)‖ =
      ∑' n : ℕ, 1 / (n : ℝ) ^ u := by
  have hsum : Summable (fun n : ℕ ↦ 1 / (n : ℝ) ^ u) :=
    by simpa only [one_div] using Real.summable_nat_rpow_inv.mpr hu
  have hzeta : riemannZeta (u : ℂ) =
      ((∑' n : ℕ, 1 / (n : ℝ) ^ u : ℝ) : ℂ) := by
    rw [zeta_eq_tsum_one_div_nat_cpow (by simpa using hu)]
    rw [Complex.ofReal_tsum]
    apply tsum_congr
    intro n
    simp only [one_div, Complex.ofReal_inv, Complex.ofReal_cpow
      (Nat.cast_nonneg n), Complex.ofReal_natCast]
  rw [hzeta, norm_real, Real.norm_eq_abs,
    abs_of_nonneg (tsum_nonneg fun n ↦ by positivity)]

/-- Along Tao's exponents, zeta has at least half of its pole-size main
term. -/
theorem eventually_half_mul_log_le_norm_riemannZeta_tao :
    ∀ᶠ X : ℕ in Filter.atTop,
      (1 / 2 : ℝ) * Real.log (X : ℝ) ≤
        ‖riemannZeta (taoExponent X : ℂ)‖ := by
  have hscaled : ∀ᶠ X : ℕ in Filter.atTop,
      (1 / 2 : ℝ) ≤
        (taoExponent X - 1) *
          (∑' n : ℕ, 1 / (n : ℝ) ^ taoExponent X) :=
    tendsto_taoExponent_mul_realZetaSum.eventually
      (eventually_ge_nhds (by norm_num : (1 / 2 : ℝ) < 1))
  filter_upwards [hscaled, eventually_ge_atTop 2] with X hscaledX hX
  have hX1 : 1 < X := by omega
  have hlog : 0 < Real.log (X : ℝ) :=
    Real.log_pos (by exact_mod_cast hX1)
  have htao : taoExponent X - 1 = (Real.log (X : ℝ))⁻¹ := by
    unfold taoExponent
    ring
  rw [htao, inv_mul_eq_div] at hscaledX
  rw [norm_riemannZeta_real_eq_realZetaSum (one_lt_taoExponent hX1)]
  exact (le_div_iff₀ hlog).mp hscaledX

/-- The singular series is eventually bounded below by a positive constant
times `log X`.  The constant depends only on the pretentious-distance bound
`D`, not on `X`. -/
theorem exists_pos_eventually_mul_log_le_norm_singularSeries_of_global
    {h : ℕ →*₀ ℂ} (hh : HasUnitNorm h) {D : ℝ}
    (hD : ∀ X : ℕ, pretentiousMass h X ≤ D) :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ X : ℕ in Filter.atTop,
      c * Real.log (X : ℝ) ≤ ‖singularSeries h X‖ := by
  let c : ℝ := (1 / 2 : ℝ) *
    Real.exp (-(D + primeQuadraticConstant))
  refine ⟨c, mul_pos (by norm_num) (Real.exp_pos _), ?_⟩
  filter_upwards [eventually_half_mul_log_le_norm_riemannZeta_tao,
      eventually_ge_atTop 2] with X hzeta hX
  have hX1 : 1 < X := by omega
  have hcomparison := exp_neg_mul_norm_riemannZeta_le_norm_LSeries
    hh hD (one_lt_taoExponent hX1)
  dsimp only [c]
  unfold singularSeries
  calc
    (1 / 2 : ℝ) * Real.exp (-(D + primeQuadraticConstant)) *
        Real.log (X : ℝ) =
        Real.exp (-(D + primeQuadraticConstant)) *
          ((1 / 2 : ℝ) * Real.log (X : ℝ)) := by ring
    _ ≤ Real.exp (-(D + primeQuadraticConstant)) *
          ‖riemannZeta (taoExponent X : ℂ)‖ :=
      mul_le_mul_of_nonneg_left hzeta (Real.exp_pos _).le
    _ ≤ ‖LSeries h (taoExponent X : ℂ)‖ := hcomparison

/-- Uniform same-scale form of the singular-series lower bound.  The scale
`X` is chosen before the completely multiplicative function `h`; only the
pretentious mass through that same `X` is assumed. -/
theorem exists_pos_eventually_mul_log_le_norm_singularSeries
    (D : ℝ) :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ X : ℕ in Filter.atTop,
      ∀ h : ℕ →*₀ ℂ, HasUnitNorm h →
        pretentiousMass h X ≤ D →
          c * Real.log (X : ℝ) ≤ ‖singularSeries h X‖ := by
  let c : ℝ := (1 / 2 : ℝ) *
    Real.exp
      (-(D + 2 * shiftedEulerTailConstant + primeQuadraticConstant))
  refine ⟨c, mul_pos (by norm_num) (Real.exp_pos _), ?_⟩
  filter_upwards [eventually_half_mul_log_le_norm_riemannZeta_tao,
      eventually_ge_atTop 4] with X hzeta hX
  intro h hh hD
  have hcomparison :=
    exp_neg_mul_norm_riemannZeta_le_norm_LSeries_sameScale hh hX hD
  dsimp only [c]
  unfold singularSeries
  calc
    (1 / 2 : ℝ) *
          Real.exp
              (-(D + 2 * shiftedEulerTailConstant + primeQuadraticConstant)) *
          Real.log (X : ℝ) =
        Real.exp
              (-(D + 2 * shiftedEulerTailConstant + primeQuadraticConstant)) *
          ((1 / 2 : ℝ) * Real.log (X : ℝ)) := by ring
    _ ≤ Real.exp
            (-(D + 2 * shiftedEulerTailConstant + primeQuadraticConstant)) *
          ‖riemannZeta (taoExponent X : ℂ)‖ :=
      mul_le_mul_of_nonneg_left hzeta (Real.exp_pos _).le
    _ ≤ ‖LSeries h (taoExponent X : ℂ)‖ := hcomparison

end

end Erdos67b.EulerLower
