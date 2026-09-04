import ErdosProblems.Erdos67b.EulerResidue
import ErdosProblems.Erdos67b.EulerSubpower
import ErdosProblems.Erdos67b.TruncatedEulerLSeries

/-!
# Quantitative principal and nonprincipal Euler products

This file compares the Euler logarithm of a unit-valued completely
multiplicative function with the corresponding Dirichlet-character Euler
logarithm.  The comparison is uniform at the real exponents used in Tao's
argument.  Combined with the boundedness of a fixed nonprincipal Dirichlet
`L`-function, it is the analytic input for residue equidistribution.
-/

open scoped BigOperators
open Complex Filter Finset Asymptotics

namespace Erdos67b.EulerQuantitative

noncomputable section

open Erdos67b.EulerResidue
open Erdos67b.TruncatedEulerLSeries

def twistedEulerLogTerm {r : ℕ} (h : ℕ →*₀ ℂ)
    (chi : DirichletCharacter ℂ r) (u : ℝ) (p : Nat.Primes) : ℂ :=
  -Complex.log (1 - h p * chi p * (p : ℂ) ^ (-(u : ℂ)))

def characterEulerLogTerm {r : ℕ}
    (chi : DirichletCharacter ℂ r) (u : ℝ) (p : Nat.Primes) : ℂ :=
  -Complex.log (1 - chi p * (p : ℂ) ^ (-(u : ℂ)))

lemma norm_prime_cpow_neg_real (u : ℝ) (p : Nat.Primes) :
    ‖(p : ℂ) ^ (-(u : ℂ))‖ = (p : ℝ) ^ (-u) := by
  rw [show -(u : ℂ) = ((-u : ℝ) : ℂ) by push_cast; ring]
  rw [Complex.norm_cpow_real, Complex.norm_natCast]

lemma prime_rpow_neg_le_half {u : ℝ} (hu : 1 < u) (p : Nat.Primes) :
    (p : ℝ) ^ (-u) ≤ 1 / 2 := by
  have hpTwo : (2 : ℝ) ≤ p := by exact_mod_cast p.prop.two_le
  have hpOne : (1 : ℝ) ≤ p := by linarith
  calc
    (p : ℝ) ^ (-u) ≤ (p : ℝ) ^ (-1 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le hpOne (by linarith)
    _ = ((p : ℝ))⁻¹ := Real.rpow_neg_one _
    _ ≤ (2 : ℝ)⁻¹ := by
      simpa only [one_div] using one_div_le_one_div_of_le (by norm_num) hpTwo
    _ = 1 / 2 := by norm_num

private lemma log_remainder_le_square {z : ℂ} (hz : ‖z‖ ≤ 1 / 2) :
    ‖-Complex.log (1 - z) - z‖ ≤ ‖z‖ ^ 2 := by
  have hzlt : ‖z‖ < 1 := lt_of_le_of_lt hz (by norm_num)
  refine (norm_neg_log_one_sub_sub_self_le hzlt).trans ?_
  have hinv : (1 - ‖z‖)⁻¹ ≤ 2 := by
    rw [inv_eq_one_div]
    have := one_div_le_one_div_of_le (show (0 : ℝ) < 1 / 2 by norm_num)
      (show (1 : ℝ) / 2 ≤ 1 - ‖z‖ by linarith)
    norm_num at this
    simpa only [one_div] using this
  calc
    ‖z‖ ^ 2 * (1 - ‖z‖)⁻¹ / 2 ≤ ‖z‖ ^ 2 * 2 / 2 := by
      gcongr
    _ = ‖z‖ ^ 2 := by ring

/-- Local comparison of the two Euler logarithms.  The linear term is the
pretentious prime difference; both Taylor remainders are dominated by the
same quadratic prime weight. -/
theorem norm_twistedEulerLogTerm_sub_character_le {r : ℕ}
    {h : ℕ →*₀ ℂ} (hh : HasUnitNorm h)
    (chi : DirichletCharacter ℂ r) {u : ℝ} (hu : 1 < u)
    (p : Nat.Primes) :
    ‖twistedEulerLogTerm h chi u p - characterEulerLogTerm chi u p‖ ≤
      weightedPrimeDifference h u p + 2 * ((p : ℝ) ^ (-u)) ^ 2 := by
  let z : ℂ := (p : ℂ) ^ (-(u : ℂ))
  let a : ℂ := h p * chi p * z
  let b : ℂ := chi p * z
  have hzNorm : ‖z‖ = (p : ℝ) ^ (-u) := by
    simpa only [z] using norm_prime_cpow_neg_real u p
  have hzHalf : ‖z‖ ≤ 1 / 2 := hzNorm.trans_le (prime_rpow_neg_le_half hu p)
  have hchi : ‖chi p‖ ≤ 1 := chi.norm_le_one p
  have ha : ‖a‖ ≤ ‖z‖ := by
    dsimp only [a]
    rw [norm_mul, norm_mul, hh p.prop.ne_zero]
    simpa only [one_mul] using mul_le_of_le_one_left (norm_nonneg z) hchi
  have hb : ‖b‖ ≤ ‖z‖ := by
    dsimp only [b]
    rw [norm_mul]
    exact mul_le_of_le_one_left (norm_nonneg z) hchi
  have haHalf : ‖a‖ ≤ 1 / 2 := ha.trans hzHalf
  have hbHalf : ‖b‖ ≤ 1 / 2 := hb.trans hzHalf
  have hrema : ‖-Complex.log (1 - a) - a‖ ≤ ‖z‖ ^ 2 :=
    (log_remainder_le_square haHalf).trans (by
      nlinarith [norm_nonneg a, norm_nonneg z])
  have hremb : ‖-Complex.log (1 - b) - b‖ ≤ ‖z‖ ^ 2 :=
    (log_remainder_le_square hbHalf).trans (by
      nlinarith [norm_nonneg b, norm_nonneg z])
  have hlin : ‖a - b‖ ≤ ‖h p - 1‖ * ‖z‖ := by
    have hab : a - b = (h p - 1) * chi p * z := by
      dsimp only [a, b]
      ring
    rw [hab, norm_mul, norm_mul]
    exact mul_le_mul_of_nonneg_right
      (mul_le_of_le_one_right (norm_nonneg (h p - 1)) hchi)
      (norm_nonneg z)
  have hdecomp :
      -Complex.log (1 - a) - (-Complex.log (1 - b)) =
        (-Complex.log (1 - a) - a) + (a - b) -
          (-Complex.log (1 - b) - b) := by ring
  change ‖-Complex.log (1 - a) - (-Complex.log (1 - b))‖ ≤ _
  rw [hdecomp]
  calc
    ‖(-Complex.log (1 - a) - a) + (a - b) -
        (-Complex.log (1 - b) - b)‖ ≤
        ‖-Complex.log (1 - a) - a‖ + ‖a - b‖ +
          ‖-Complex.log (1 - b) - b‖ := by
      refine (norm_sub_le _ _).trans ?_
      have hadd := norm_add_le (-Complex.log (1 - a) - a) (a - b)
      linarith
    _ ≤ ‖z‖ ^ 2 + (‖h p - 1‖ * ‖z‖) + ‖z‖ ^ 2 := by
      gcongr
    _ = weightedPrimeDifference h u p + 2 * ((p : ℝ) ^ (-u)) ^ 2 := by
      rw [hzNorm]
      unfold weightedPrimeDifference
      ring

theorem summable_twistedEulerLogTerm {r : ℕ} {h : ℕ →*₀ ℂ}
    (hh : HasUnitNorm h) (chi : DirichletCharacter ℂ r)
    {u : ℝ} (hu : 1 < u) :
    Summable (twistedEulerLogTerm h chi u) := by
  have hs : (1 : ℝ) < ((u : ℂ)).re := by simpa
  have hraw : Summable (fun p : Nat.Primes ↦
      h p * chi p * (p : ℂ) ^ (-(u : ℂ))) := by
    have hnat := (summable_norm_twistedWeightedSummandHom hh chi hs).of_norm
    have hsub := hnat.subtype Nat.Prime
    refine hsub.congr ?_
    intro p
    change twistedWeightedSummandHom h chi _ p = _
    exact twistedWeightedSummandHom_apply h chi _ p
  change Summable (fun p : Nat.Primes ↦
    -Complex.log (1 - h p * chi p * (p : ℂ) ^ (-(u : ℂ))))
  exact hraw.clog_one_sub.neg

theorem summable_characterEulerLogTerm {r : ℕ}
    (chi : DirichletCharacter ℂ r) {u : ℝ} (hu : 1 < u) :
    Summable (characterEulerLogTerm chi u) := by
  have hs : (1 : ℝ) < ((u : ℂ)).re := by simpa
  have hraw : Summable (fun p : Nat.Primes ↦
      chi p * (p : ℂ) ^ (-(u : ℂ))) := by
    have hnat := (summable_dirichletSummand chi hs).of_norm
    have hsub := hnat.subtype Nat.Prime
    refine hsub.congr ?_
    intro p
    change dirichletSummandHom chi _ p = _
    rfl
  change Summable (fun p : Nat.Primes ↦
    -Complex.log (1 - chi p * (p : ℂ) ^ (-(u : ℂ))))
  exact hraw.clog_one_sub.neg

theorem summable_primeQuadraticError {u : ℝ} (hu : 1 < u) :
    Summable (fun p : Nat.Primes ↦ 2 * ((p : ℝ) ^ (-u)) ^ 2) := by
  have hbase : Summable (fun p : Nat.Primes ↦ (p : ℝ) ^ (-2 * u)) :=
    (Real.summable_nat_rpow.mpr (by linarith : -2 * u < -1)).subtype Nat.Prime
  refine (hbase.mul_left 2).congr ?_
  intro p
  have hp0 : (0 : ℝ) ≤ p := by positivity
  congr 1
  rw [← Real.rpow_natCast]
  rw [← Real.rpow_mul hp0]
  congr 1
  ring

/-- A fixed absolute majorant for all quadratic Euler-log remainders. -/
def primeQuadraticConstant : ℝ :=
  ∑' p : Nat.Primes, 2 * (p : ℝ) ^ (-2 : ℝ)

theorem primeQuadraticConstant_nonneg : 0 ≤ primeQuadraticConstant := by
  exact tsum_nonneg fun p ↦ mul_nonneg (by norm_num) (Real.rpow_nonneg (by positivity) _)

theorem tsum_primeQuadraticError_le_constant {u : ℝ} (hu : 1 < u) :
    (∑' p : Nat.Primes, 2 * ((p : ℝ) ^ (-u)) ^ 2) ≤
      primeQuadraticConstant := by
  have hleft := summable_primeQuadraticError hu
  have hright : Summable (fun p : Nat.Primes ↦ 2 * (p : ℝ) ^ (-2 : ℝ)) :=
    ((Real.summable_nat_rpow.mpr (by norm_num : (-2 : ℝ) < -1)).subtype
      Nat.Prime).mul_left 2
  unfold primeQuadraticConstant
  refine Summable.tsum_le_tsum ?_ hleft hright
  intro p
  have hpOne : (1 : ℝ) ≤ p := by exact_mod_cast p.prop.one_le
  have hpow : (p : ℝ) ^ (-u) ≤ (p : ℝ) ^ (-1 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le hpOne (by linarith)
  have hnonneg : 0 ≤ (p : ℝ) ^ (-u) := Real.rpow_nonneg (by positivity) _
  have hsq : ((p : ℝ) ^ (-u)) ^ 2 ≤ ((p : ℝ) ^ (-1 : ℝ)) ^ 2 := by
    nlinarith [Real.rpow_nonneg (show (0 : ℝ) ≤ p by positivity) (-1 : ℝ)]
  calc
    2 * ((p : ℝ) ^ (-u)) ^ 2 ≤
        2 * ((p : ℝ) ^ (-1 : ℝ)) ^ 2 := by nlinarith
    _ = 2 * (p : ℝ) ^ (-2 : ℝ) := by
      have hp0 : (0 : ℝ) ≤ p := by positivity
      rw [← Real.rpow_natCast, ← Real.rpow_mul hp0]
      congr 2
      ring

/-- At Tao's exponent, control of the pretentious mass only through the
current scale controls the complete prime perturbation.  The primes above
the scale contribute an absolute constant. -/
theorem tsum_weightedPrimeDifference_tao_le
    {h : ℕ →*₀ ℂ} (hh : HasUnitNorm h) {D : ℝ} {X : ℕ}
    (hX : 4 ≤ X) (hD : pretentiousMass h X ≤ D) :
    (∑' p : Nat.Primes, weightedPrimeDifference h (taoExponent X) p) ≤
      Real.sqrt (2 * D *
        Real.log (riemannZeta
          ((2 * taoExponent X - 1 : ℝ) : ℂ)).re) +
        2 * shiftedEulerTailConstant := by
  have hu : 1 < taoExponent X := one_lt_taoExponent (by omega)
  have hsum := summable_weightedPrimeDifference hh hu
  have hsplit := hsum.sum_add_tsum_subtype_compl (primeSubtypesUpTo X)
  rw [← hsplit]
  have hhead :
      ∑ p ∈ primeSubtypesUpTo X,
          weightedPrimeDifference h (taoExponent X) p ≤
        Real.sqrt (2 * D *
          Real.log (riemannZeta
            ((2 * taoExponent X - 1 : ℝ) : ℂ)).re) := by
    let S := primeSubtypesUpTo X
    have hcs := Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul
      (R := ℝ) S
      (r := weightedPrimeDifference h (taoExponent X))
      (f := primeDistanceSquare h)
      (g := fun p : Nat.Primes ↦
        (p : ℝ) ^ (1 - 2 * taoExponent X))
      (fun p hp ↦ by unfold primeDistanceSquare; positivity)
      (fun p hp ↦ Real.rpow_nonneg (by positivity) _)
      (fun p hp ↦ by
        unfold weightedPrimeDifference primeDistanceSquare
        have hp0 : (0 : ℝ) < p := by exact_mod_cast p.prop.pos
        have hpow : ((p : ℝ) ^ (-taoExponent X)) ^ 2 =
            (p : ℝ) ^ (-1 : ℝ) *
              (p : ℝ) ^ (1 - 2 * taoExponent X) := by
          rw [← Real.rpow_natCast]
          rw [← Real.rpow_mul hp0.le]
          convert Real.rpow_add hp0 (-1 : ℝ)
            (1 - 2 * taoExponent X) using 1 <;> ring_nf
        rw [mul_pow, hpow, Real.rpow_neg_one]
        field_simp
        exact le_rfl)
    apply Real.le_sqrt_of_sq_le
    refine hcs.trans ?_
    have hdist :
        ∑ p ∈ S, primeDistanceSquare h p ≤ 2 * D := by
      have heq : ∑ p ∈ S, primeDistanceSquare h p =
          2 * pretentiousMass h X := by
        unfold S primeDistanceSquare pretentiousMass
        rw [Finset.mul_sum]
        classical
        apply Finset.sum_bij (fun p _ ↦ p.1)
        · intro p hp
          exact Nat.mem_primesLE.mpr
            ⟨mem_primeSubtypesUpTo.mp hp, p.prop⟩
        · intro p₁ hp₁ p₂ hp₂ heq
          exact Subtype.ext heq
        · intro p hp
          refine ⟨⟨p, (Nat.mem_primesLE.mp hp).2⟩, ?_, ?_⟩
          · exact mem_primeSubtypesUpTo.mpr (Nat.mem_primesLE.mp hp).1
          · rfl
        · intro p hp
          rw [norm_sub_one_sq hh p.prop.ne_zero]
          ring
      rw [heq]
      exact mul_le_mul_of_nonneg_left hD (by norm_num)
    have hpowSum :
        ∑ p ∈ S, (p : ℝ) ^ (1 - 2 * taoExponent X) ≤
          Real.log (riemannZeta
            ((2 * taoExponent X - 1 : ℝ) : ℂ)).re := by
      have hall := tsum_primes_rpow_le_log_riemannZeta
        (show 1 < 2 * taoExponent X - 1 by linarith)
      have hsummable : Summable (fun p : Nat.Primes ↦
          (p : ℝ) ^ (1 - 2 * taoExponent X)) :=
        (Real.summable_nat_rpow.mpr (by
          linarith : 1 - 2 * taoExponent X < -1)).subtype Nat.Prime
      calc
        ∑ p ∈ S, (p : ℝ) ^ (1 - 2 * taoExponent X) ≤
            ∑' p : Nat.Primes,
              (p : ℝ) ^ (1 - 2 * taoExponent X) :=
          hsummable.sum_le_tsum S
            (fun p hp ↦ Real.rpow_nonneg (by positivity) _)
        _ ≤ Real.log (riemannZeta
              ((2 * taoExponent X - 1 : ℝ) : ℂ)).re := by
          simpa only [show -(2 * taoExponent X - 1) =
            1 - 2 * taoExponent X by ring] using hall
    calc
      (∑ p ∈ S, primeDistanceSquare h p) *
          ∑ p ∈ S, (p : ℝ) ^ (1 - 2 * taoExponent X) ≤
          (2 * D) *
            ∑ p ∈ S, (p : ℝ) ^ (1 - 2 * taoExponent X) :=
        mul_le_mul_of_nonneg_right hdist
          (Finset.sum_nonneg fun p _ ↦ Real.rpow_nonneg (by positivity) _)
      _ ≤ (2 * D) * Real.log (riemannZeta
            ((2 * taoExponent X - 1 : ℝ) : ℂ)).re := by
        have hD0 : 0 ≤ D :=
          (pretentiousMass_nonneg hh X).trans hD
        exact mul_le_mul_of_nonneg_left hpowSum
          (mul_nonneg (by norm_num) hD0)
  have htail :
      (∑' p : {p : Nat.Primes // p ∉ primeSubtypesUpTo X},
          weightedPrimeDifference h (taoExponent X) p.1) ≤
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
      unfold weightedPrimeDifference shiftedPrimeWeight
      have hnorm : ‖h p.1 - 1‖ ≤ 2 := by
        calc
          ‖h p.1 - 1‖ ≤ ‖h p.1‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
          _ = 2 := by rw [hh p.1.prop.ne_zero]; norm_num
      have hexp : -taoExponent X =
          -(1 : ℝ) - (Real.log (X : ℝ))⁻¹ := by
        unfold taoExponent
        ring
      rw [hexp]
      exact mul_le_mul_of_nonneg_right hnorm
        (Real.rpow_nonneg (by positivity) _)
    · rw [tsum_mul_left]
      change 2 * shiftedEulerTail X ≤ 2 * shiftedEulerTailConstant
      exact mul_le_mul_of_nonneg_left (shiftedEulerTail_le_constant hX)
        (by norm_num)
  linarith

/-- Quantitative bound for the difference of the complete Euler logarithms. -/
theorem norm_tsum_twistedEulerLog_sub_character_le {r : ℕ}
    {h : ℕ →*₀ ℂ} (hh : HasUnitNorm h)
    (chi : DirichletCharacter ℂ r) {u : ℝ} (hu : 1 < u) :
    ‖(∑' p : Nat.Primes, twistedEulerLogTerm h chi u p) -
        (∑' p : Nat.Primes, characterEulerLogTerm chi u p)‖ ≤
      (∑' p : Nat.Primes, weightedPrimeDifference h u p) +
        ∑' p : Nat.Primes, 2 * ((p : ℝ) ^ (-u)) ^ 2 := by
  have htwist := summable_twistedEulerLogTerm hh chi hu
  have hchar := summable_characterEulerLogTerm chi hu
  have hdiff := htwist.sub hchar
  have hquad := summable_primeQuadraticError hu
  have hweight := summable_weightedPrimeDifference hh hu
  rw [← htwist.tsum_sub hchar]
  refine (norm_tsum_le_tsum_norm hdiff.norm).trans ?_
  refine Summable.tsum_le_tsum
    (fun p ↦ norm_twistedEulerLogTerm_sub_character_le hh chi hu p)
    hdiff.norm (hweight.add hquad) |>.trans_eq ?_
  exact hweight.tsum_add hquad

/-- Comparison of a twisted completely multiplicative `L`-series with the
ordinary Dirichlet `L`-series of the same character. -/
theorem norm_twistLSeries_le_exp_logDifference_mul {r : ℕ}
    {h : ℕ →*₀ ℂ} (hh : HasUnitNorm h)
    (chi : DirichletCharacter ℂ r) {u : ℝ} (hu : 1 < u) :
    ‖LSeries (twistCoefficient h chi) (u : ℂ)‖ ≤
      Real.exp
          ((∑' p : Nat.Primes, weightedPrimeDifference h u p) +
            ∑' p : Nat.Primes, 2 * ((p : ℝ) ^ (-u)) ^ 2) *
        ‖LSeries (fun n : ℕ ↦ chi n) (u : ℂ)‖ := by
  let A : ℂ := ∑' p : Nat.Primes, twistedEulerLogTerm h chi u p
  let B : ℂ := ∑' p : Nat.Primes, characterEulerLogTerm chi u p
  have hs : (1 : ℝ) < ((u : ℂ)).re := by simpa
  have htwist : Complex.exp A = LSeries (twistCoefficient h chi) (u : ℂ) := by
    simpa only [A, twistedEulerLogTerm] using
      twistedEulerProduct_exp_log hh chi hs
  have hchar : Complex.exp B = LSeries (fun n : ℕ ↦ chi n) (u : ℂ) := by
    simpa only [B, characterEulerLogTerm] using
      DirichletCharacter.LSeries_eulerProduct_exp_log chi hs
  have hfactor : Complex.exp A = Complex.exp (A - B) * Complex.exp B := by
    rw [← Complex.exp_add]
    congr 1
    ring
  rw [← htwist, ← hchar, hfactor, norm_mul, Complex.norm_exp]
  apply mul_le_mul_of_nonneg_right _ (norm_nonneg (Complex.exp B))
  apply Real.exp_le_exp.mpr
  calc
    (A - B).re ≤ ‖A - B‖ := Complex.re_le_norm _
    _ ≤ (∑' p : Nat.Primes, weightedPrimeDifference h u p) +
          ∑' p : Nat.Primes, 2 * ((p : ℝ) ^ (-u)) ^ 2 :=
      norm_tsum_twistedEulerLog_sub_character_le hh chi hu

theorem norm_twistLSeries_le_exp_sqrt_logZeta_add_quadratic {r : ℕ}
    {h : ℕ →*₀ ℂ} (hh : HasUnitNorm h) {D : ℝ}
    (hD : ∀ X : ℕ, pretentiousMass h X ≤ D)
    (chi : DirichletCharacter ℂ r) {u : ℝ} (hu : 1 < u) :
    ‖LSeries (twistCoefficient h chi) (u : ℂ)‖ ≤
      Real.exp
          (Real.sqrt (2 * D *
              Real.log (riemannZeta ((2 * u - 1 : ℝ) : ℂ)).re) +
            ∑' p : Nat.Primes, 2 * ((p : ℝ) ^ (-u)) ^ 2) *
        ‖LSeries (fun n : ℕ ↦ chi n) (u : ℂ)‖ := by
  refine (norm_twistLSeries_le_exp_logDifference_mul hh chi hu).trans ?_
  apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
  apply Real.exp_le_exp.mpr
  simpa only [add_comm] using
    add_le_add_right (tsum_weightedPrimeDifference_le_logZeta hh hD hu)
      (∑' p : Nat.Primes, 2 * ((p : ℝ) ^ (-u)) ^ 2)

/-- Same-scale version of the twisted `L`-series comparison. -/
theorem norm_twistLSeries_le_exp_sameScale {r : ℕ}
    {h : ℕ →*₀ ℂ} (hh : HasUnitNorm h)
    (chi : DirichletCharacter ℂ r) {D : ℝ} {X : ℕ}
    (hX : 4 ≤ X) (hD : pretentiousMass h X ≤ D) :
    ‖LSeries (twistCoefficient h chi) (taoExponent X : ℂ)‖ ≤
      Real.exp
          (Real.sqrt (2 * D *
              Real.log (riemannZeta
                ((2 * taoExponent X - 1 : ℝ) : ℂ)).re) +
            2 * shiftedEulerTailConstant + primeQuadraticConstant) *
        ‖LSeries (fun n : ℕ ↦ chi n) (taoExponent X : ℂ)‖ := by
  have hu : 1 < taoExponent X := one_lt_taoExponent (by omega)
  refine (norm_twistLSeries_le_exp_logDifference_mul hh chi hu).trans ?_
  apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
  apply Real.exp_le_exp.mpr
  have hlinear := tsum_weightedPrimeDifference_tao_le hh hX hD
  have hquad := tsum_primeQuadraticError_le_constant hu
  linarith

/-- The explicit exponent in the nonprincipal-twist estimate at Tao's
choice `u = 1 + 1 / log X`. -/
def pretentiousEulerExponent (D : ℝ) (X : ℕ) : ℝ :=
  Real.sqrt (2 * D *
    Real.log (riemannZeta
      ((2 * taoExponent X - 1 : ℝ) : ℂ)).re)

def nonprincipalEulerError (B D : ℝ) (X : ℕ) : ℝ :=
  Real.exp (pretentiousEulerExponent D X +
    2 * shiftedEulerTailConstant + primeQuadraticConstant) * B

theorem tendsto_two_taoExponent_sub_one :
    Tendsto (fun X : ℕ ↦ 2 * taoExponent X - 1) atTop (nhds 1) := by
  have hinv : Tendsto (fun X : ℕ ↦ (Real.log (X : ℝ))⁻¹) atTop (nhds 0) :=
    EulerSubpower.tendsto_log_nat_atTop.inv_tendsto_atTop
  have htao : Tendsto (fun X : ℕ ↦ taoExponent X) atTop (nhds 1) := by
    simpa only [taoExponent, add_zero] using tendsto_const_nhds.add hinv
  convert (htao.const_mul 2).sub tendsto_const_nhds using 1 <;> norm_num

theorem tendsto_two_taoExponent_sub_one_complex_within :
    Tendsto (fun X : ℕ ↦ ((2 * taoExponent X - 1 : ℝ) : ℂ)) atTop
      (nhdsWithin (1 : ℂ) {1}ᶜ) := by
  rw [tendsto_nhdsWithin_iff]
  constructor
  · simpa using tendsto_two_taoExponent_sub_one.ofReal
  · filter_upwards [eventually_ge_atTop 2] with X hX
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
    have hlog : 0 < Real.log (X : ℝ) :=
      Real.log_pos (by exact_mod_cast (show 1 < X by omega))
    have hgt : 1 < 2 * taoExponent X - 1 := by
      unfold taoExponent
      have : 0 < (Real.log (X : ℝ))⁻¹ := inv_pos.mpr hlog
      linarith
    exact_mod_cast hgt.ne'

/-- Near `1` from the right, zeta at `2 * taoExponent X - 1` is at most a
fixed multiple of `log X`. -/
theorem exists_eventually_zeta_re_le_mul_log :
    ∃ A : ℝ, 0 < A ∧ ∀ᶠ X : ℕ in atTop,
      (riemannZeta ((2 * taoExponent X - 1 : ℝ) : ℂ)).re ≤
        A * Real.log (X : ℝ) := by
  have hconv := tendsto_riemannZeta_sub_one_div.comp
    tendsto_two_taoExponent_sub_one_complex_within
  have hnorm := hconv.norm
  have hbounded := hnorm.isBoundedUnder_le
  change ∃ K : ℝ, ∀ᶠ X : ℕ in atTop,
      ‖riemannZeta ((2 * taoExponent X - 1 : ℝ) : ℂ) -
        1 / (((2 * taoExponent X - 1 : ℝ) : ℂ) - 1)‖ ≤ K at hbounded
  obtain ⟨K, hK⟩ := hbounded
  let A : ℝ := |K| + 1
  have hA : 0 < A := by dsimp [A]; positivity
  refine ⟨A, hA, ?_⟩
  filter_upwards [hK,
      EulerSubpower.tendsto_log_nat_atTop.eventually
        (eventually_ge_atTop (max 1 (2 * |K|)))] with X hdiff hlog
  have hlogPos : 0 < Real.log (X : ℝ) := lt_of_lt_of_le (by norm_num) hlog
  have hden :
      (((2 * taoExponent X - 1 : ℝ) : ℂ) - 1) =
        (2 * (Real.log (X : ℝ))⁻¹ : ℝ) := by
    norm_cast
    unfold taoExponent
    ring
  have hinvRe :
      (1 / (((2 * taoExponent X - 1 : ℝ) : ℂ) - 1)).re =
        Real.log (X : ℝ) / 2 := by
    rw [hden]
    simp only [one_div, ← Complex.ofReal_inv, Complex.ofReal_re]
    field_simp
  have hre := Complex.re_le_norm
    (riemannZeta ((2 * taoExponent X - 1 : ℝ) : ℂ) -
      1 / (((2 * taoExponent X - 1 : ℝ) : ℂ) - 1))
  simp only [Complex.sub_re, hinvRe] at hre
  have hzeta :
      (riemannZeta ((2 * taoExponent X - 1 : ℝ) : ℂ)).re ≤
        |K| + Real.log (X : ℝ) / 2 := by
    calc
      _ ≤ ‖riemannZeta ((2 * taoExponent X - 1 : ℝ) : ℂ) -
          1 / (((2 * taoExponent X - 1 : ℝ) : ℂ) - 1)‖ +
            Real.log (X : ℝ) / 2 := by linarith
      _ ≤ |K| + Real.log (X : ℝ) / 2 := by
        gcongr
        exact hdiff.trans (le_abs_self K)
  dsimp only [A]
  have hlogOne : 1 ≤ Real.log (X : ℝ) := (le_max_left _ _).trans hlog
  have habsMul : |K| ≤ |K| * Real.log (X : ℝ) := by
    nlinarith [mul_nonneg (abs_nonneg K) (sub_nonneg.mpr hlogOne)]
  calc
    _ ≤ |K| + Real.log (X : ℝ) / 2 := hzeta
    _ ≤ |K| * Real.log (X : ℝ) + Real.log (X : ℝ) := by
      gcongr <;> linarith
    _ = (|K| + 1) * Real.log (X : ℝ) := by ring

theorem eventually_log_zeta_re_le_two_log_log :
    ∀ᶠ X : ℕ in atTop,
      Real.log (riemannZeta
        ((2 * taoExponent X - 1 : ℝ) : ℂ)).re ≤
        2 * Real.log (Real.log (X : ℝ)) := by
  obtain ⟨A, hA, hbound⟩ := exists_eventually_zeta_re_le_mul_log
  filter_upwards [hbound,
      EulerSubpower.tendsto_log_log_nat_atTop.eventually
        (eventually_ge_atTop (max 0 (Real.log A))),
      eventually_ge_atTop 2] with X hzeta hloglog hX
  have hlogX : 0 < Real.log (X : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < X by omega))
  have hs : 1 < 2 * taoExponent X - 1 := by
    unfold taoExponent
    have : 0 < (Real.log (X : ℝ))⁻¹ := inv_pos.mpr hlogX
    linarith
  have hzetaPos : 0 < (riemannZeta
      ((2 * taoExponent X - 1 : ℝ) : ℂ)).re :=
    riemannZeta_re_pos_of_one_lt hs
  calc
    Real.log (riemannZeta
        ((2 * taoExponent X - 1 : ℝ) : ℂ)).re ≤
        Real.log (A * Real.log (X : ℝ)) := by
      exact Real.strictMonoOn_log.monotoneOn hzetaPos
        (mul_pos hA hlogX) hzeta
    _ = Real.log A + Real.log (Real.log (X : ℝ)) := by
      rw [Real.log_mul hA.ne' hlogX.ne']
    _ ≤ 2 * Real.log (Real.log (X : ℝ)) := by
      have : Real.log A ≤ Real.log (Real.log (X : ℝ)) :=
        le_trans (le_max_right 0 (Real.log A)) hloglog
      linarith

theorem eventually_pretentiousEulerExponent_le_subpowerExponent
    {D : ℝ} (hD0 : 0 ≤ D) :
    ∀ᶠ X : ℕ in atTop,
      pretentiousEulerExponent D X ≤
        Real.sqrt (4 * D) *
          Real.sqrt (Real.log (Real.log (X : ℝ))) := by
  filter_upwards [eventually_log_zeta_re_le_two_log_log,
      EulerSubpower.tendsto_log_log_nat_atTop.eventually
        (eventually_ge_atTop 0)] with X hzeta hloglog
  unfold pretentiousEulerExponent
  have hmul :
      2 * D * Real.log (riemannZeta
          ((2 * taoExponent X - 1 : ℝ) : ℂ)).re ≤
        (4 * D) * Real.log (Real.log (X : ℝ)) := by
    nlinarith
  calc
    Real.sqrt (2 * D * Real.log (riemannZeta
        ((2 * taoExponent X - 1 : ℝ) : ℂ)).re) ≤
        Real.sqrt ((4 * D) * Real.log (Real.log (X : ℝ))) :=
      Real.sqrt_le_sqrt hmul
    _ = Real.sqrt (4 * D) *
        Real.sqrt (Real.log (Real.log (X : ℝ))) := by
      rw [Real.sqrt_mul (mul_nonneg (by norm_num) hD0)]

/-- The explicit nonprincipal Euler error is negligible compared with the
singular-series scale `log X`. -/
theorem nonprincipalEulerError_isLittleO_log
    {D B : ℝ} (hD0 : 0 ≤ D) (hB : 0 ≤ B) :
    (nonprincipalEulerError B D) =o[atTop]
      (fun X : ℕ ↦ Real.log (X : ℝ)) := by
  let C : ℝ := Real.sqrt (4 * D)
  let K : ℝ :=
    Real.exp (2 * shiftedEulerTailConstant + primeQuadraticConstant) * B
  have hK : 0 ≤ K := mul_nonneg (Real.exp_pos _).le hB
  have hmajor : ∀ᶠ X : ℕ in atTop,
      nonprincipalEulerError B D X ≤ K * EulerSubpower.subpowerError C X := by
    filter_upwards [eventually_pretentiousEulerExponent_le_subpowerExponent hD0]
      with X hX
    unfold nonprincipalEulerError EulerSubpower.subpowerError
    dsimp only [K, C]
    have hexp :
        Real.exp (pretentiousEulerExponent D X +
            2 * shiftedEulerTailConstant + primeQuadraticConstant) ≤
          Real.exp (Real.sqrt (4 * D) *
            Real.sqrt (Real.log (Real.log (X : ℝ))) +
              2 * shiftedEulerTailConstant + primeQuadraticConstant) :=
      Real.exp_le_exp.mpr (by linarith)
    calc
      Real.exp (pretentiousEulerExponent D X +
          2 * shiftedEulerTailConstant + primeQuadraticConstant) * B ≤
          Real.exp (Real.sqrt (4 * D) *
            Real.sqrt (Real.log (Real.log (X : ℝ))) +
              2 * shiftedEulerTailConstant + primeQuadraticConstant) * B :=
        mul_le_mul_of_nonneg_right hexp hB
      _ = Real.exp (2 * shiftedEulerTailConstant + primeQuadraticConstant) * B *
          Real.exp (Real.sqrt (4 * D) *
            Real.sqrt (Real.log (Real.log (X : ℝ)))) := by
        rw [show Real.sqrt (4 * D) *
            Real.sqrt (Real.log (Real.log (X : ℝ))) +
              2 * shiftedEulerTailConstant + primeQuadraticConstant =
            (2 * shiftedEulerTailConstant + primeQuadraticConstant) +
              Real.sqrt (4 * D) *
                Real.sqrt (Real.log (Real.log (X : ℝ))) by ring,
          Real.exp_add]
        ring
  refine Asymptotics.IsLittleO.of_bound ?_
  intro epsilon hepsilon
  have hsmall :=
    ((EulerSubpower.subpowerError_isLittleO_log C).const_mul_left K).bound hepsilon
  filter_upwards [hmajor, hsmall,
      EulerSubpower.tendsto_log_nat_atTop.eventually (eventually_ge_atTop 0)]
      with X hmajorX hsmallX hlog
  rw [Real.norm_of_nonneg hlog]
  have herr0 : 0 ≤ nonprincipalEulerError B D X := by
    unfold nonprincipalEulerError
    positivity
  rw [Real.norm_of_nonneg herr0]
  exact hmajorX.trans (by
    have hleft0 : 0 ≤ K * EulerSubpower.subpowerError C X := by
      exact mul_nonneg hK (Real.exp_pos _).le
    simpa only [Real.norm_eq_abs, abs_of_nonneg hleft0,
      abs_of_nonneg hlog] using hsmallX)

/-- At a fixed modulus all nonprincipal twists satisfy one explicit,
unconditional bound.  The constant `B` depends only on the modulus; all
dependence on `h`, its pretentious bound `D`, and `X` is displayed. -/
theorem exists_nonprincipalTwistsBounded_taoExponent {r : ℕ} [NeZero r]
    {h : ℕ →*₀ ℂ} (hh : HasUnitNorm h) {D : ℝ}
    (hD : ∀ X : ℕ, pretentiousMass h X ≤ D) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ X : ℕ, 2 ≤ X →
      NonprincipalTwistsBounded h r (taoExponent X)
        (nonprincipalEulerError B D X) := by
  classical
  have hExists : ∀ chi : DirichletCharacter ℂ r,
      ∃ B : ℝ, 0 ≤ B ∧ (chi ≠ 1 → ∀ X : ℕ, 2 ≤ X →
        ‖LSeries (fun n : ℕ ↦ chi n) (taoExponent X)‖ ≤ B) := by
    intro chi
    by_cases hchi : chi ≠ 1
    · obtain ⟨B, hB0, hB⟩ := exists_nonprincipal_characterLSeries_bound chi hchi
      exact ⟨B, hB0, fun _ ↦ hB⟩
    · exact ⟨0, le_rfl, fun hne ↦ (hchi hne).elim⟩
  choose b hb0 hb using hExists
  let B : ℝ := ∑ chi : DirichletCharacter ℂ r, b chi
  have hB0 : 0 ≤ B := Finset.sum_nonneg fun chi _ ↦ hb0 chi
  refine ⟨B, hB0, ?_⟩
  intro X hX chi hchi
  have hu : 1 < taoExponent X :=
    one_lt_taoExponent (lt_of_lt_of_le one_lt_two hX)
  have hordinary :
      ‖LSeries (fun n : ℕ ↦ chi n) (taoExponent X)‖ ≤ B := by
    refine (hb chi hchi X hX).trans ?_
    exact Finset.single_le_sum (fun psi _ ↦ hb0 psi) (Finset.mem_univ chi)
  have hcomparison :=
    norm_twistLSeries_le_exp_sqrt_logZeta_add_quadratic hh hD chi hu
  have hquad := tsum_primeQuadraticError_le_constant hu
  refine hcomparison.trans ?_
  unfold nonprincipalEulerError pretentiousEulerExponent
  have hexp :
      Real.exp
          (Real.sqrt (2 * D *
              Real.log (riemannZeta
                ((2 * taoExponent X - 1 : ℝ) : ℂ)).re) +
            ∑' p : Nat.Primes,
              2 * ((p : ℝ) ^ (-taoExponent X)) ^ 2) ≤
        Real.exp
          (Real.sqrt (2 * D *
              Real.log (riemannZeta
                ((2 * taoExponent X - 1 : ℝ) : ℂ)).re) +
            2 * shiftedEulerTailConstant + primeQuadraticConstant) :=
    by
      apply Real.exp_le_exp.mpr
      have htail0 : 0 ≤ 2 * shiftedEulerTailConstant :=
        mul_nonneg (by norm_num) shiftedEulerTailConstant_nonneg
      linarith
  exact mul_le_mul hexp hordinary (norm_nonneg _) (Real.exp_pos _).le

/-- One constant works simultaneously for every (nonzero) divisor of the
fixed modulus `q^k`.  This is the uniform form consumed by the residue
decomposition. -/
theorem exists_uniform_nonprincipalTwistsBounded_divisors
    (q k : ℕ) (hq0 : q ≠ 0) {h : ℕ →*₀ ℂ}
    (hh : HasUnitNorm h) {D : ℝ}
    (hD : ∀ X : ℕ, pretentiousMass h X ≤ D) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ r : ℕ, r ∣ q ^ k → r ≠ 0 →
      ∀ X : ℕ, 2 ≤ X →
        NonprincipalTwistsBounded h r (taoExponent X)
          (nonprincipalEulerError B D X) := by
  classical
  have hExists : ∀ r : ℕ, ∃ b : ℝ, 0 ≤ b ∧
      (r ≠ 0 → ∀ X : ℕ, 2 ≤ X →
        NonprincipalTwistsBounded h r (taoExponent X)
          (nonprincipalEulerError b D X)) := by
    intro r
    by_cases hr0 : r ≠ 0
    · let : NeZero r := ⟨hr0⟩
      obtain ⟨b, hb0, hb⟩ :=
        exists_nonprincipalTwistsBounded_taoExponent (r := r) hh hD
      exact ⟨b, hb0, fun _ ↦ hb⟩
    · exact ⟨0, le_rfl, fun hr ↦ (hr0 hr).elim⟩
  choose b hb0 hb using hExists
  let B : ℝ := ∑ r ∈ (q ^ k).divisors, b r
  have hqk0 : q ^ k ≠ 0 := pow_ne_zero _ hq0
  have hB0 : 0 ≤ B := Finset.sum_nonneg fun r _ ↦ hb0 r
  refine ⟨B, hB0, ?_⟩
  intro r hr hr0 X hX chi hchi
  have hrmem : r ∈ (q ^ k).divisors := Nat.mem_divisors.mpr ⟨hr, hqk0⟩
  have hrB : b r ≤ B :=
    Finset.single_le_sum (fun t _ ↦ hb0 t) hrmem
  have hsmall := hb r hr0 X hX chi hchi
  refine hsmall.trans ?_
  unfold nonprincipalEulerError
  exact mul_le_mul_of_nonneg_left hrB (Real.exp_pos _).le

/-! ## Uniform same-scale nonprincipal package -/

/-- At a fixed modulus one constant works for every scale and every
unit-norm coefficient satisfying the pretentious bound at that same scale. -/
theorem exists_nonprincipalTwistsBounded_taoExponent_sameScale
    {r : ℕ} [NeZero r] (D : ℝ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ X : ℕ, 4 ≤ X →
      ∀ h : ℕ →*₀ ℂ, HasUnitNorm h → pretentiousMass h X ≤ D →
        NonprincipalTwistsBounded h r (taoExponent X)
          (nonprincipalEulerError B D X) := by
  classical
  have hExists : ∀ chi : DirichletCharacter ℂ r,
      ∃ b : ℝ, 0 ≤ b ∧ (chi ≠ 1 → ∀ X : ℕ, 2 ≤ X →
        ‖LSeries (fun n : ℕ ↦ chi n) (taoExponent X)‖ ≤ b) := by
    intro chi
    by_cases hchi : chi ≠ 1
    · obtain ⟨b, hb0, hb⟩ :=
        exists_nonprincipal_characterLSeries_bound chi hchi
      exact ⟨b, hb0, fun _ ↦ hb⟩
    · exact ⟨0, le_rfl, fun hne ↦ (hchi hne).elim⟩
  choose b hb0 hb using hExists
  let B : ℝ := ∑ chi : DirichletCharacter ℂ r, b chi
  have hB0 : 0 ≤ B := Finset.sum_nonneg fun chi _ ↦ hb0 chi
  refine ⟨B, hB0, ?_⟩
  intro X hX h hh hD chi hchi
  have hordinary :
      ‖LSeries (fun n : ℕ ↦ chi n) (taoExponent X)‖ ≤ B := by
    refine (hb chi hchi X (by omega)).trans ?_
    exact Finset.single_le_sum (fun psi _ ↦ hb0 psi) (Finset.mem_univ chi)
  have hcomparison := norm_twistLSeries_le_exp_sameScale hh chi hX hD
  refine hcomparison.trans ?_
  unfold nonprincipalEulerError pretentiousEulerExponent
  exact mul_le_mul_of_nonneg_left hordinary (Real.exp_pos _).le

/-- One constant works simultaneously for all nonzero divisors of `q^k`,
uniformly in both the later scale and the later coefficient. -/
theorem exists_uniform_nonprincipalTwistsBounded_divisors_sameScale
    (q k : ℕ) (hq0 : q ≠ 0) (D : ℝ) :
    ∃ B : ℝ, 0 ≤ B ∧
      ∀ r : ℕ, r ∣ q ^ k → r ≠ 0 →
        ∀ X : ℕ, 4 ≤ X →
          ∀ h : ℕ →*₀ ℂ, HasUnitNorm h →
            pretentiousMass h X ≤ D →
              NonprincipalTwistsBounded h r (taoExponent X)
                (nonprincipalEulerError B D X) := by
  classical
  have hExists : ∀ r : ℕ, ∃ b : ℝ, 0 ≤ b ∧
      (r ≠ 0 → ∀ X : ℕ, 4 ≤ X →
        ∀ h : ℕ →*₀ ℂ, HasUnitNorm h →
          pretentiousMass h X ≤ D →
            NonprincipalTwistsBounded h r (taoExponent X)
              (nonprincipalEulerError b D X)) := by
    intro r
    by_cases hr0 : r ≠ 0
    · let : NeZero r := ⟨hr0⟩
      obtain ⟨b, hb0, hb⟩ :=
        exists_nonprincipalTwistsBounded_taoExponent_sameScale (r := r) D
      exact ⟨b, hb0, fun _ ↦ hb⟩
    · exact ⟨0, le_rfl, fun hr ↦ (hr0 hr).elim⟩
  choose b hb0 hb using hExists
  let B : ℝ := ∑ r ∈ (q ^ k).divisors, b r
  have hqk0 : q ^ k ≠ 0 := pow_ne_zero _ hq0
  have hB0 : 0 ≤ B := Finset.sum_nonneg fun r _ ↦ hb0 r
  refine ⟨B, hB0, ?_⟩
  intro r hr hr0 X hX h hh hD chi hchi
  have hrmem : r ∈ (q ^ k).divisors := Nat.mem_divisors.mpr ⟨hr, hqk0⟩
  have hrB : b r ≤ B :=
    Finset.single_le_sum (fun t _ ↦ hb0 t) hrmem
  have hsmall := hb r hr0 X hX h hh hD chi hchi
  refine hsmall.trans ?_
  unfold nonprincipalEulerError
  exact mul_le_mul_of_nonneg_left hrB (Real.exp_pos _).le

end

end Erdos67b.EulerQuantitative
