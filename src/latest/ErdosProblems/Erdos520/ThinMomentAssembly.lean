import ErdosProblems.Erdos520.BonamiModel
import ErdosProblems.Erdos520.Doob
import ErdosProblems.Erdos520.MinkowskiIntegral
import ErdosProblems.Erdos520.ScalingIntegral
import ErdosProblems.Erdos520.ThinEuler

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open Finset MeasureTheory Set
open scoped BigOperators

namespace Erdos
namespace Problem520

/-!
# Analytic assembly of the thin-block moment estimate

This file isolates the paper-independent inequality chain in equations
(17)--(24).  The probability-fiber identification is deliberately an explicit
hypothesis: once a conditional moment has been represented on the finite fresh
Rademacher cube, `hdoob`, `hbonami`, and `hminkowski` are respectively the
fiberwise forms of Doob, Bonami, and integral Minkowski.  The rest of the
argument is proved here, including the inverse-square scaling, the exact finite
Euler product, and absorption into `exp (C * r / ell)`.
-/

/-- Doob + Bonami + Minkowski, before using the inverse-square scaling law.

`maxMoment z` and `terminalMoment z` are the squared `L^(2r)` roots in (17),
and `coefficientSq S z` is the old-coordinate coefficient square in (19).
The conclusion is exactly the finite-sum form of (20).  All Bochner
integrability assumptions are stated explicitly so that no nonintegrable
default value can enter the argument.
-/
theorem doob_bonami_minkowski_to_scaled_sum
    {r a b : ℕ}
    {momentRoot : ℝ}
    {maxMoment terminalMoment : ℝ → ℝ}
    {coefficientSq : Finset ℕ → ℝ → ℝ}
    (hlog : 0 < Real.log (b : ℝ))
    (hminkowski :
      momentRoot ≤ (Real.log (b : ℝ))⁻¹ *
        ∫ z in Ioi (0 : ℝ), maxMoment z / z ^ 2)
    (hdoob : ∀ z ∈ Ioi (0 : ℝ), maxMoment z ≤ 4 * terminalMoment z)
    (hbonami : ∀ z ∈ Ioi (0 : ℝ),
      terminalMoment z ≤
        ∑ S ∈ (freshPrimes a b).powerset,
          (((2 * r - 1 : ℕ) : ℝ) ^ S.card) * coefficientSq S z)
    (hmax_integrable :
      IntegrableOn (fun z => maxMoment z / z ^ 2) (Ioi (0 : ℝ)))
    (hcoeff_integrable : ∀ S ∈ (freshPrimes a b).powerset,
      IntegrableOn (fun z => coefficientSq S z / z ^ 2) (Ioi (0 : ℝ))) :
    momentRoot ≤ 4 * (Real.log (b : ℝ))⁻¹ *
      ∑ S ∈ (freshPrimes a b).powerset,
        (((2 * r - 1 : ℕ) : ℝ) ^ S.card) *
          ∫ z in Ioi (0 : ℝ), coefficientSq S z / z ^ 2 := by
  let P := (freshPrimes a b).powerset
  let weight : Finset ℕ → ℝ := fun S =>
    (((2 * r - 1 : ℕ) : ℝ) ^ S.card)
  have hsum_integrable : IntegrableOn
      (fun z => 4 * ∑ S ∈ P, weight S * (coefficientSq S z / z ^ 2))
      (Ioi (0 : ℝ)) := by
    apply Integrable.const_mul
    apply integrable_finset_sum P
    intro S hS
    apply Integrable.const_mul
    exact hcoeff_integrable S hS
  have hintegral :
      (∫ z in Ioi (0 : ℝ), maxMoment z / z ^ 2) ≤
        ∫ z in Ioi (0 : ℝ),
          4 * ∑ S ∈ P, weight S * (coefficientSq S z / z ^ 2) := by
    apply setIntegral_mono_on hmax_integrable hsum_integrable measurableSet_Ioi
    intro z hz
    have hz2 : 0 ≤ z ^ 2 := sq_nonneg z
    calc
      maxMoment z / z ^ 2 ≤ (4 * terminalMoment z) / z ^ 2 :=
        div_le_div_of_nonneg_right (hdoob z hz) hz2
      _ ≤ (4 * ∑ S ∈ P, weight S * coefficientSq S z) / z ^ 2 := by
        exact div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_left (hbonami z hz) (by norm_num)) hz2
      _ = 4 * ∑ S ∈ P, weight S * (coefficientSq S z / z ^ 2) := by
        simp only [P, weight]
        simp only [div_eq_mul_inv]
        calc
          (4 * ∑ S ∈ (freshPrimes a b).powerset,
              (((2 * r - 1 : ℕ) : ℝ) ^ S.card) * coefficientSq S z) *
                (z ^ 2)⁻¹ =
              4 * ((∑ S ∈ (freshPrimes a b).powerset,
                (((2 * r - 1 : ℕ) : ℝ) ^ S.card) * coefficientSq S z) *
                  (z ^ 2)⁻¹) := by ring
          _ = 4 * ∑ S ∈ (freshPrimes a b).powerset,
              ((((2 * r - 1 : ℕ) : ℝ) ^ S.card) * coefficientSq S z) *
                (z ^ 2)⁻¹ := by rw [Finset.sum_mul]
          _ = 4 * ∑ S ∈ (freshPrimes a b).powerset,
              (((2 * r - 1 : ℕ) : ℝ) ^ S.card) *
                (coefficientSq S z * (z ^ 2)⁻¹) := by
            congr 1
            apply Finset.sum_congr rfl
            intro S hS
            ring
  calc
    momentRoot ≤ (Real.log (b : ℝ))⁻¹ *
        ∫ z in Ioi (0 : ℝ), maxMoment z / z ^ 2 := hminkowski
    _ ≤ (Real.log (b : ℝ))⁻¹ *
        ∫ z in Ioi (0 : ℝ),
          4 * ∑ S ∈ P, weight S * (coefficientSq S z / z ^ 2) :=
      mul_le_mul_of_nonneg_left hintegral (inv_nonneg.mpr hlog.le)
    _ = 4 * (Real.log (b : ℝ))⁻¹ *
        ∑ S ∈ P, weight S *
          ∫ z in Ioi (0 : ℝ), coefficientSq S z / z ^ 2 := by
      rw [integral_const_mul]
      rw [integral_finset_sum]
      · simp_rw [integral_const_mul]
        ring
      · intro S hS
        exact (hcoeff_integrable S hS).const_mul (weight S)

/-- Raw analytic assembly of equations (20)--(24).

The scaling hypothesis is equation (21), while `hparseval` is the only
paper-facing input, equation (24).  The reciprocal-prime hypothesis is the
Mertens-sized input in (23); equations (22) and the exponential Euler-product
bound are discharged by `sum_freshBonamiWeight_le_exp`.
-/
theorem thinMoment_analytic_assembly_raw
    {ell r a b : ℕ} (hell : 0 < ell)
    {momentRoot H I Cparseval Crecip : ℝ}
    {maxMoment terminalMoment : ℝ → ℝ}
    {coefficientSq : Finset ℕ → ℝ → ℝ}
    (hlog : 0 < Real.log (b : ℝ))
    (hI : 0 ≤ I) (hCparseval : 0 ≤ Cparseval)
    (hminkowski :
      momentRoot ≤ (Real.log (b : ℝ))⁻¹ *
        ∫ z in Ioi (0 : ℝ), maxMoment z / z ^ 2)
    (hdoob : ∀ z ∈ Ioi (0 : ℝ), maxMoment z ≤ 4 * terminalMoment z)
    (hbonami : ∀ z ∈ Ioi (0 : ℝ),
      terminalMoment z ≤
        ∑ S ∈ (freshPrimes a b).powerset,
          (((2 * r - 1 : ℕ) : ℝ) ^ S.card) * coefficientSq S z)
    (hmax_integrable :
      IntegrableOn (fun z => maxMoment z / z ^ 2) (Ioi (0 : ℝ)))
    (hcoeff_integrable : ∀ S ∈ (freshPrimes a b).powerset,
      IntegrableOn (fun z => coefficientSq S z / z ^ 2) (Ioi (0 : ℝ)))
    (hscale : ∀ S ∈ (freshPrimes a b).powerset,
      (∫ z in Ioi (0 : ℝ), coefficientSq S z / z ^ 2) =
        H / (freshProduct S : ℝ))
    (hparseval : H / Real.log (b : ℝ) ≤ Cparseval * I)
    (hrecip : freshReciprocalSum a b ≤ Crecip / ell) :
    momentRoot ≤
      4 * Cparseval * Real.exp (Crecip * (((2 * r - 1 : ℕ) : ℝ)) / ell) * I := by
  let t : ℝ := ((2 * r - 1 : ℕ) : ℝ)
  let W : ℝ := ∑ S ∈ (freshPrimes a b).powerset, freshBonamiWeight t S
  have ht : 0 ≤ t := by positivity
  have hW_nonneg : 0 ≤ W := by
    unfold W freshBonamiWeight
    apply Finset.sum_nonneg
    intro S hS
    exact div_nonneg (pow_nonneg ht _) (by positivity)
  have hW_exp : W ≤ Real.exp (Crecip * t / ell) := by
    exact sum_freshBonamiWeight_le_exp ht hell hrecip
  have h20 := doob_bonami_minkowski_to_scaled_sum
    hlog hminkowski hdoob hbonami hmax_integrable hcoeff_integrable
  calc
    momentRoot ≤ 4 * (Real.log (b : ℝ))⁻¹ *
        ∑ S ∈ (freshPrimes a b).powerset,
          t ^ S.card *
            ∫ z in Ioi (0 : ℝ), coefficientSq S z / z ^ 2 := by
      simpa only [t] using! h20
    _ = 4 * (H / Real.log (b : ℝ)) * W := by
      have hsumscale :
          (∑ S ∈ (freshPrimes a b).powerset,
              t ^ S.card *
                ∫ z in Ioi (0 : ℝ), coefficientSq S z / z ^ 2) =
            H * W := by
        unfold W freshBonamiWeight
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro S hS
        rw [hscale S hS]
        ring
      rw [hsumscale]
      ring
    _ ≤ 4 * (Cparseval * I) * W := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hparseval (by norm_num)) hW_nonneg
    _ ≤ 4 * (Cparseval * I) * Real.exp (Crecip * t / ell) := by
      exact mul_le_mul_of_nonneg_left hW_exp
        (mul_nonneg (by positivity) (mul_nonneg hCparseval hI))
    _ = 4 * Cparseval * Real.exp
        (Crecip * (((2 * r - 1 : ℕ) : ℝ)) / ell) * I := by
      unfold t
      ring

/-- One-constant form of the thin-block moment estimate (16).

Taking
`C = max (4 * Cparseval) (2 * Crecip)` simultaneously absorbs the Doob and
Parseval constants and uses `2r - 1 ≤ 2r`.  Thus the conclusion has exactly
the advertised `C * exp (C * r / ell) * I` shape.
-/
theorem thinMoment_analytic_assembly
    {ell r a b : ℕ} (hell : 0 < ell) (_hr : 2 ≤ r)
    {momentRoot H I Cparseval Crecip : ℝ}
    {maxMoment terminalMoment : ℝ → ℝ}
    {coefficientSq : Finset ℕ → ℝ → ℝ}
    (hlog : 0 < Real.log (b : ℝ))
    (hI : 0 ≤ I) (hCparseval : 0 ≤ Cparseval)
    (hCrecip : 0 ≤ Crecip)
    (hminkowski :
      momentRoot ≤ (Real.log (b : ℝ))⁻¹ *
        ∫ z in Ioi (0 : ℝ), maxMoment z / z ^ 2)
    (hdoob : ∀ z ∈ Ioi (0 : ℝ), maxMoment z ≤ 4 * terminalMoment z)
    (hbonami : ∀ z ∈ Ioi (0 : ℝ),
      terminalMoment z ≤
        ∑ S ∈ (freshPrimes a b).powerset,
          (((2 * r - 1 : ℕ) : ℝ) ^ S.card) * coefficientSq S z)
    (hmax_integrable :
      IntegrableOn (fun z => maxMoment z / z ^ 2) (Ioi (0 : ℝ)))
    (hcoeff_integrable : ∀ S ∈ (freshPrimes a b).powerset,
      IntegrableOn (fun z => coefficientSq S z / z ^ 2) (Ioi (0 : ℝ)))
    (hscale : ∀ S ∈ (freshPrimes a b).powerset,
      (∫ z in Ioi (0 : ℝ), coefficientSq S z / z ^ 2) =
        H / (freshProduct S : ℝ))
    (hparseval : H / Real.log (b : ℝ) ≤ Cparseval * I)
    (hrecip : freshReciprocalSum a b ≤ Crecip / ell) :
    let C := max (4 * Cparseval) (2 * Crecip)
    momentRoot ≤ C * Real.exp (C * r / ell) * I := by
  let C := max (4 * Cparseval) (2 * Crecip)
  have hraw := thinMoment_analytic_assembly_raw hell hlog hI hCparseval
    hminkowski hdoob hbonami hmax_integrable hcoeff_integrable
    hscale hparseval hrecip
  have hfront : 4 * Cparseval ≤ C := le_max_left _ _
  have hexponent :
      Crecip * (((2 * r - 1 : ℕ) : ℝ)) / ell ≤ C * r / ell := by
    have hdegree : ((2 * r - 1 : ℕ) : ℝ) ≤ 2 * (r : ℝ) := by
      exact_mod_cast (Nat.sub_le (2 * r) 1)
    have hC : 2 * Crecip ≤ C := le_max_right _ _
    have h₁ := mul_le_mul_of_nonneg_left hdegree hCrecip
    have h₂ := mul_le_mul_of_nonneg_right hC (by positivity : 0 ≤ (r : ℝ))
    have hnum : Crecip * (((2 * r - 1 : ℕ) : ℝ)) ≤ C * r := by
      calc
        Crecip * (((2 * r - 1 : ℕ) : ℝ)) ≤ Crecip * (2 * r) := h₁
        _ = (2 * Crecip) * r := by ring
        _ ≤ C * r := h₂
    exact div_le_div_of_nonneg_right hnum (by positivity : 0 ≤ (ell : ℝ))
  have hexp : Real.exp
      (Crecip * (((2 * r - 1 : ℕ) : ℝ)) / ell) ≤
      Real.exp (C * r / ell) := Real.exp_le_exp.mpr hexponent
  have hC_nonneg : 0 ≤ C := le_trans (mul_nonneg (by norm_num) hCparseval) hfront
  calc
    momentRoot ≤ 4 * Cparseval *
        Real.exp (Crecip * (((2 * r - 1 : ℕ) : ℝ)) / ell) * I := hraw
    _ ≤ C * Real.exp
        (Crecip * (((2 * r - 1 : ℕ) : ℝ)) / ell) * I := by
      gcongr
    _ ≤ C * Real.exp (C * r / ell) * I := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hexp hC_nonneg) hI

/-- Concrete inverse-square-scaled form of the analytic assembly.

Here every coefficient is a dilation `baseSq (z / freshProduct S)`.  The
scaling hypothesis of `thinMoment_analytic_assembly` is therefore discharged
by `integral_comp_div_mul_inv_sq_Ioi`; the positivity of the dilation follows
from the fact that `S` consists only of primes.  In an application,
`baseSq w = |Ψ(w,a)|²` and its displayed integral is `H_a`.
-/
theorem thinMoment_analytic_assembly_of_dilations
    {ell r a b : ℕ} (hell : 0 < ell) (hr : 2 ≤ r)
    {momentRoot I Cparseval Crecip : ℝ}
    {maxMoment terminalMoment baseSq : ℝ → ℝ}
    (hlog : 0 < Real.log (b : ℝ))
    (hI : 0 ≤ I) (hCparseval : 0 ≤ Cparseval)
    (hCrecip : 0 ≤ Crecip)
    (hminkowski :
      momentRoot ≤ (Real.log (b : ℝ))⁻¹ *
        ∫ z in Ioi (0 : ℝ), maxMoment z / z ^ 2)
    (hdoob : ∀ z ∈ Ioi (0 : ℝ), maxMoment z ≤ 4 * terminalMoment z)
    (hbonami : ∀ z ∈ Ioi (0 : ℝ),
      terminalMoment z ≤
        ∑ S ∈ (freshPrimes a b).powerset,
          (((2 * r - 1 : ℕ) : ℝ) ^ S.card) *
            baseSq (z / (freshProduct S : ℝ)))
    (hmax_integrable :
      IntegrableOn (fun z => maxMoment z / z ^ 2) (Ioi (0 : ℝ)))
    (hcoeff_integrable : ∀ S ∈ (freshPrimes a b).powerset,
      IntegrableOn
        (fun z => baseSq (z / (freshProduct S : ℝ)) / z ^ 2)
        (Ioi (0 : ℝ)))
    (hparseval :
      (∫ w in Ioi (0 : ℝ), baseSq w / w ^ 2) /
          Real.log (b : ℝ) ≤ Cparseval * I)
    (hrecip : freshReciprocalSum a b ≤ Crecip / ell) :
    let C := max (4 * Cparseval) (2 * Crecip)
    momentRoot ≤ C * Real.exp (C * r / ell) * I := by
  let H : ℝ := ∫ w in Ioi (0 : ℝ), baseSq w / w ^ 2
  have hscale : ∀ S ∈ (freshPrimes a b).powerset,
      (∫ z in Ioi (0 : ℝ),
          baseSq (z / (freshProduct S : ℝ)) / z ^ 2) =
        H / (freshProduct S : ℝ) := by
    intro S hS
    have hSsub : S ⊆ freshPrimes a b := Finset.mem_powerset.mp hS
    have hprime : ∀ p ∈ S, p.Prime := by
      intro p hp
      exact (mem_freshPrimes.mp (hSsub hp)).1
    have hdNat : 0 < freshProduct S := freshProduct_pos_of_primes hprime
    have hd : 0 < (freshProduct S : ℝ) := by exact_mod_cast hdNat
    calc
      (∫ z in Ioi (0 : ℝ),
          baseSq (z / (freshProduct S : ℝ)) / z ^ 2) =
          (freshProduct S : ℝ)⁻¹ *
            ∫ w in Ioi (0 : ℝ), baseSq w / w ^ 2 :=
        integral_comp_div_mul_inv_sq_Ioi baseSq hd
      _ = H / (freshProduct S : ℝ) := by
        unfold H
        ring
  exact thinMoment_analytic_assembly hell hr hlog hI hCparseval hCrecip
    hminkowski hdoob hbonami hmax_integrable hcoeff_integrable hscale
    hparseval hrecip

end Problem520
end Erdos
