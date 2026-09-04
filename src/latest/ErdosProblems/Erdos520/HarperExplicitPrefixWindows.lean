import ErdosProblems.Erdos520.HarperPrefixGoodRestrictedRecursion
import ErdosProblems.Erdos520.HarperScheduledSummableErrors

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open Finset MeasureTheory ProbabilityTheory Set Filter
open scoped BigOperators ENNReal NNReal

namespace Erdos.Problem520

/-!
# Explicit asymmetric prefix windows on a fixed noncentral band

At prefix length `ell`, the upper window is the exact fair Euler normalizer
multiplied by `exp (2*b_ell)`, while the lower window is `exp (-2*b_ell)`
divided by the exact inverse Euler normalizer.  Each path therefore costs
exactly two copies of `exp (-2*b_ell)`.  The canonical profile absorbs the
full prefix-family entropy and leaves a clean `exp (-2*B)` total budget,
with `B` free for the later two-index substitution `C / gap_j`.

For the barrier comparison we combine the cumulative reciprocal-mass error
with the scheduled off-diagonal drift interval.  All remaining assumptions
in the final endpoint are numerical inequalities involving the profile, the target
reverse-log barrier, and the explicit summable error tail.
-/

/-! ## Exact inverse normalizer and explicit windows -/

/-- Product formula for the fair first moment of the inverse varying Euler
energy over a scheduled prefix. -/
noncomputable def harperPrefixInverseEulerNormalizer
    (y start m : ℕ) (u : Fin m → ℝ) : ℝ :=
  ∏ i : Fin m, ∏ p ∈ harperScheduledPrimeBlock y (start + (i : ℕ)),
    harperInverseEulerPrimeMoment p.1 (u i)

theorem harperPrefixInverseEulerNormalizer_pos
    (y start m : ℕ) (u : Fin m → ℝ) :
    0 < harperPrefixInverseEulerNormalizer y start m u := by
  unfold harperPrefixInverseEulerNormalizer
  apply Finset.prod_pos
  intro i hi
  apply Finset.prod_pos
  intro p hp
  exact harperInverseEulerPrimeMoment_pos
    (Nat.prime_of_mem_primesBelow p.property) (u i)

theorem harperPrefixScheduledVaryingEulerReciprocal_eq_inverseProduct
    (y start m : ℕ) (u : Fin m → ℝ) (eta : HarperPrimeCube y) :
    harperPrefixScheduledVaryingEulerReciprocal y start m u eta =
      harperScheduledVaryingInverseEulerProduct y start m u eta := by
  unfold harperPrefixScheduledVaryingEulerReciprocal
    harperPrefixScheduledVaryingEulerEnergy
    harperScheduledVaryingEulerEnergy
    harperScheduledVaryingInverseEulerProduct
    harperInverseEulerBlockProduct
  rw [← Finset.prod_inv_distrib]
  apply Finset.prod_congr rfl
  intro i hi
  rw [Finset.prod_inv_distrib]

/-- Exact product evaluation of the reciprocal first moment. -/
theorem harperPrefixEulerReciprocalFirstMoment_eq_inverseNormalizer
    (y start m : ℕ) (u : Fin m → ℝ) :
    harperPrefixEulerReciprocalFirstMoment y start m u =
      harperPrefixInverseEulerNormalizer y start m u := by
  unfold harperPrefixEulerReciprocalFirstMoment
  calc
    (∫ eta, harperPrefixScheduledVaryingEulerReciprocal
          y start m u eta ∂harperFairCubeLaw y) =
        ∫ eta, harperScheduledVaryingInverseEulerProduct
          y start m u eta ∂harperFairCubeLaw y := by
      apply integral_congr_ae
      exact ae_of_all _ fun eta ↦
        harperPrefixScheduledVaryingEulerReciprocal_eq_inverseProduct
          y start m u eta
    _ = ∫ eta, harperVaryingInverseEulerProduct y
          (harperScheduledPrimeRangeFrom y start m)
          (harperScheduledPrimeHeight y start m u) eta
          ∂harperFairCubeLaw y := by
      apply integral_congr_ae
      exact ae_of_all _ fun eta ↦
        harperScheduledVaryingInverseEulerProduct_eq_rangeFrom
          y start m u eta
    _ = ∏ p ∈ harperScheduledPrimeRangeFrom y start m,
          harperInverseEulerPrimeMoment p.1
            (harperScheduledPrimeHeight y start m u p) :=
      integral_harperVaryingInverseEulerProduct y
        (harperScheduledPrimeRangeFrom y start m)
        (harperScheduledPrimeHeight y start m u)
    _ = harperPrefixInverseEulerNormalizer y start m u := by
      unfold harperScheduledPrimeRangeFrom
        harperPrefixInverseEulerNormalizer
      rw [Finset.prod_biUnion
        (pairwiseDisjoint_harperScheduledPrimeBlock_add y start m)]
      rw [Finset.prod_range]
      apply Finset.prod_congr rfl
      intro i hi
      apply Finset.prod_congr rfl
      intro p hp
      rw [harperScheduledPrimeHeight_eq y start m u i hp]

/-- Lower asymmetric window for a prefix-dependent height profile. -/
noncomputable def harperExplicitPrefixLowerWindow
    (y start : ℕ) (height : ℕ → ℝ)
    (m : ℕ) (u : Fin m → ℝ) : ℝ :=
  Real.exp (-2 * height m) /
    harperPrefixInverseEulerNormalizer y start m u

/-- Upper asymmetric window for the same prefix-dependent height profile. -/
noncomputable def harperExplicitPrefixUpperWindow
    (y start : ℕ) (height : ℕ → ℝ)
    (m : ℕ) (_u : Fin m → ℝ) : ℝ :=
  harperPrefixEulerNormalizer y start m * Real.exp (2 * height m)

theorem harperExplicitPrefixLowerWindow_pos
    (y start : ℕ) (height : ℕ → ℝ)
    (m : ℕ) (u : Fin m → ℝ) :
    0 < harperExplicitPrefixLowerWindow y start height m u := by
  unfold harperExplicitPrefixLowerWindow
  exact div_pos (Real.exp_pos _)
    (harperPrefixInverseEulerNormalizer_pos y start m u)

theorem harperExplicitPrefixUpperWindow_pos
    (y start : ℕ) (height : ℕ → ℝ)
    (m : ℕ) (u : Fin m → ℝ) :
    0 < harperExplicitPrefixUpperWindow y start height m u := by
  unfold harperExplicitPrefixUpperWindow
  exact mul_pos (harperPrefixEulerNormalizer_pos y start m) (Real.exp_pos _)

theorem log_harperExplicitPrefixLowerWindow
    (y start : ℕ) (height : ℕ → ℝ)
    (m : ℕ) (u : Fin m → ℝ) :
    Real.log (harperExplicitPrefixLowerWindow y start height m u) =
      -2 * height m -
        Real.log (harperPrefixInverseEulerNormalizer y start m u) := by
  unfold harperExplicitPrefixLowerWindow
  rw [Real.log_div (Real.exp_ne_zero _)
    (harperPrefixInverseEulerNormalizer_pos y start m u).ne',
    Real.log_exp]

theorem log_harperExplicitPrefixUpperWindow
    (y start : ℕ) (height : ℕ → ℝ)
    (m : ℕ) (u : Fin m → ℝ) :
    Real.log (harperExplicitPrefixUpperWindow y start height m u) =
      Real.log (harperPrefixEulerNormalizer y start m) + 2 * height m := by
  unfold harperExplicitPrefixUpperWindow
  rw [Real.log_mul (harperPrefixEulerNormalizer_pos y start m).ne'
    (Real.exp_ne_zero _), Real.log_exp]

/-! ## Exact Markov cost and the entropy bound -/

theorem harper_explicitPrefixWindow_onePath_cost
    (y start : ℕ) (height : ℕ → ℝ)
    (m : ℕ) (u : Fin m → ℝ) :
    harperPrefixEulerNormalizer y start m /
          harperExplicitPrefixUpperWindow y start height m u +
        harperPrefixInverseEulerNormalizer y start m u *
          harperExplicitPrefixLowerWindow y start height m u =
      2 * Real.exp (-2 * height m) := by
  have hnormalizer := (harperPrefixEulerNormalizer_pos y start m).ne'
  have hinverse :=
    (harperPrefixInverseEulerNormalizer_pos y start m u).ne'
  have hexp := (Real.exp_pos (2 * height m)).ne'
  have hexpNeg : (Real.exp (2 * height m))⁻¹ =
      Real.exp (-2 * height m) := by
    rw [← Real.exp_neg]
    congr 1
    ring
  unfold harperExplicitPrefixUpperWindow harperExplicitPrefixLowerWindow
  have hupper :
      harperPrefixEulerNormalizer y start m /
          (harperPrefixEulerNormalizer y start m * Real.exp (2 * height m)) =
        Real.exp (-2 * height m) := by
    rw [div_mul_eq_div_mul_one_div, div_self hnormalizer, one_mul,
      one_div]
    exact hexpNeg
  have hlower :
      harperPrefixInverseEulerNormalizer y start m u *
          (Real.exp (-2 * height m) /
            harperPrefixInverseEulerNormalizer y start m u) =
        Real.exp (-2 * height m) := by
    field_simp
  rw [hupper, hlower]
  ring

/-- Explicit prefix-family cardinality envelope, with the scale-dependent
power separated from the fixed `M`-factor. -/
def harperExplicitPrefixEntropyCoefficient (M : ℕ) : ℕ :=
  4096 * M + 1

/-- The dyadic square refinement is within a fixed factor of the literal
square.  This turns its contribution to the entropy height into a logarithmic
prefix cost. -/
theorem harperScheduledVerticalMeshRefinement_le_four_mul_succ_sq
    (m : ℕ) :
    harperScheduledVerticalMeshRefinement m ≤ 4 * (m + 1) ^ 2 := by
  by_cases hm : m ≤ 1
  · unfold harperScheduledVerticalMeshRefinement
    rw [Nat.clog_of_right_le_one hm]
    norm_num
    exact (one_le_pow₀ (by omega)).trans
      (Nat.le_mul_of_pos_left _ (by omega))
  · have hm' : 1 < m := lt_of_not_ge hm
    have hclog : 0 < Nat.clog 2 m := Nat.clog_pos (by omega) hm'
    have hpred : 2 ^ (Nat.clog 2 m).pred < m :=
      Nat.pow_pred_clog_lt_self (by omega) hm'
    have hpow : 2 ^ Nat.clog 2 m ≤ 2 * m := by
      rw [← Nat.succ_pred_eq_of_pos hclog, pow_succ]
      omega
    unfold harperScheduledVerticalMeshRefinement
    rw [show 2 * Nat.clog 2 m = Nat.clog 2 m * 2 by omega, pow_mul]
    calc
      (2 ^ Nat.clog 2 m) ^ 2 ≤ (2 * m) ^ 2 :=
        Nat.pow_le_pow_left hpow 2
      _ ≤ (2 * (m + 1)) ^ 2 :=
        Nat.pow_le_pow_left (by omega) 2
      _ = 4 * (m + 1) ^ 2 := by ring

theorem card_harperScheduledVerticalPrefixFamily_le_entropyCoefficient
    (start n m M : ℕ) :
    (harperScheduledVerticalPrefixFamily start n m M).card ≤
      harperExplicitPrefixEntropyCoefficient M *
        harperScheduledVerticalMeshRefinement m *
        2 ^ (start + m) := by
  have hcard :=
    card_harperScheduledVerticalPrefixFamily_le_explicit start n m M
  unfold harperExplicitPrefixEntropyCoefficient
  have hpow : 1 ≤ 2 ^ (start + m) := one_le_pow₀ (by omega)
  calc
    (harperScheduledVerticalPrefixFamily start n m M).card ≤
        2 * (M * (2048 * harperScheduledVerticalMeshRefinement m *
          2 ^ (start + m))) + 1 := hcard
    _ = 4096 * M * harperScheduledVerticalMeshRefinement m *
          2 ^ (start + m) + 1 := by ring
    _ ≤ 4096 * M * harperScheduledVerticalMeshRefinement m *
          2 ^ (start + m) +
        harperScheduledVerticalMeshRefinement m * 2 ^ (start + m) := by
      apply Nat.add_le_add_left
      exact Nat.mul_pos (harperScheduledVerticalMeshRefinement_pos m)
        (pow_pos (by omega) _)
    _ = (4096 * M + 1) * harperScheduledVerticalMeshRefinement m *
        2 ^ (start + m) := by ring

/-- Canonical prefix-dependent height.  `B` is deliberately free: later
applications substitute the two-index quantity `C / gap_j`. -/
noncomputable def harperExplicitPrefixEntropyHeight
    (start M : ℕ) (B : ℝ) (m : ℕ) : ℝ :=
  Real.log
      (((4 * harperExplicitPrefixEntropyCoefficient M *
        harperScheduledVerticalMeshRefinement m *
        2 ^ (start + m) * (m + 1) ^ 2 : ℕ) : ℝ)) / 2 + B

/-- Fixed part of the prefix entropy height.  All dependence on the prefix
length itself is separated in the next theorem. -/
noncomputable def harperExplicitPrefixEntropyBase
    (start M : ℕ) : ℝ :=
  Real.log 4 / 2 +
    Real.log (harperExplicitPrefixEntropyCoefficient M : ℝ) / 2 +
    Real.log 4 / 2 +
    (start : ℝ) * Real.log 2 / 2

/-- The explicit height has only the expected half-linear block entropy plus
a logarithmic prefix cost.  The coefficient `8` is intentionally aligned with
the reverse-log ballot boundary used downstream. -/
theorem harperExplicitPrefixEntropyHeight_le
    (start M : ℕ) (B : ℝ) (m : ℕ) :
    harperExplicitPrefixEntropyHeight start M B m ≤
      (m : ℝ) * Real.log 2 / 2 +
        harperExplicitPrefixEntropyBase start M +
        8 * Real.log ((m + 1 : ℕ) : ℝ) + B := by
  have hcoef : 0 < (harperExplicitPrefixEntropyCoefficient M : ℝ) := by
    exact_mod_cast (show 0 < harperExplicitPrefixEntropyCoefficient M by
      unfold harperExplicitPrefixEntropyCoefficient
      omega)
  have href : 0 < (harperScheduledVerticalMeshRefinement m : ℝ) := by
    exact_mod_cast harperScheduledVerticalMeshRefinement_pos m
  have hsucc : 0 < (((m + 1 : ℕ) : ℝ)) := by positivity
  have hrefLe :
      (harperScheduledVerticalMeshRefinement m : ℝ) ≤
        4 * (((m + 1 : ℕ) : ℝ) ^ 2) := by
    exact_mod_cast
      harperScheduledVerticalMeshRefinement_le_four_mul_succ_sq m
  have hlogRef :
      Real.log (harperScheduledVerticalMeshRefinement m : ℝ) ≤
        Real.log 4 + 2 * Real.log (((m + 1 : ℕ) : ℝ)) := by
    calc
      Real.log (harperScheduledVerticalMeshRefinement m : ℝ) ≤
          Real.log (4 * (((m + 1 : ℕ) : ℝ) ^ 2)) :=
        Real.strictMonoOn_log.monotoneOn href
          (mul_pos (by norm_num) (sq_pos_of_pos hsucc)) hrefLe
      _ = Real.log 4 + 2 * Real.log (((m + 1 : ℕ) : ℝ)) := by
        rw [Real.log_mul (by norm_num) (pow_ne_zero 2 hsucc.ne'),
          Real.log_pow]
        norm_num
  have hlogSucc : 0 ≤ Real.log (((m + 1 : ℕ) : ℝ)) := by
    exact Real.log_nonneg (by exact_mod_cast Nat.succ_le_succ (Nat.zero_le m))
  unfold harperExplicitPrefixEntropyHeight
    harperExplicitPrefixEntropyBase
  push_cast
  rw [Real.log_mul (by positivity)
    (pow_ne_zero 2 (by positivity : (m : ℝ) + 1 ≠ 0))]
  rw [Real.log_mul (by positivity) (by positivity)]
  rw [Real.log_mul (by positivity) href.ne']
  rw [Real.log_mul (by norm_num) hcoef.ne']
  rw [Real.log_pow, Real.log_pow]
  push_cast
  push_cast at hlogRef hlogSucc
  linarith

theorem exp_neg_two_mul_harperExplicitPrefixEntropyHeight
    (start M : ℕ) (B : ℝ) (m : ℕ) :
    Real.exp (-2 * harperExplicitPrefixEntropyHeight start M B m) =
      Real.exp (-2 * B) /
        ((4 * harperExplicitPrefixEntropyCoefficient M *
          harperScheduledVerticalMeshRefinement m *
          2 ^ (start + m) * (m + 1) ^ 2 : ℕ) : ℝ) := by
  let A : ℝ :=
    ((4 * harperExplicitPrefixEntropyCoefficient M *
      harperScheduledVerticalMeshRefinement m *
      2 ^ (start + m) * (m + 1) ^ 2 : ℕ) : ℝ)
  have hA : 0 < A := by
    dsimp only [A]
    exact_mod_cast (show
      0 < 4 * harperExplicitPrefixEntropyCoefficient M *
        harperScheduledVerticalMeshRefinement m * 2 ^ (start + m) *
          (m + 1) ^ 2 by
      have hcoef : 0 < harperExplicitPrefixEntropyCoefficient M := by
        unfold harperExplicitPrefixEntropyCoefficient
        omega
      exact Nat.mul_pos
        (Nat.mul_pos
          (Nat.mul_pos
            (Nat.mul_pos (by omega) hcoef)
            (harperScheduledVerticalMeshRefinement_pos m))
          (pow_pos (by omega) _))
        (pow_pos (by omega) _))
  unfold harperExplicitPrefixEntropyHeight
  change Real.exp (-2 * (Real.log A / 2 + B)) = Real.exp (-2 * B) / A
  rw [show -2 * (Real.log A / 2 + B) = -Real.log A + (-2 * B) by ring,
    Real.exp_add, Real.exp_neg, Real.exp_log hA, div_eq_mul_inv]
  ring

theorem harperPrefixEnergyWindowFirstMomentBudget_entropyHeight_le
    (y start n M : ℕ) (B : ℝ) :
    harperPrefixEnergyWindowFirstMomentBudget start n M
        (harperExplicitPrefixLowerWindow y start
          (harperExplicitPrefixEntropyHeight start M B))
        (harperExplicitPrefixUpperWindow y start
          (harperExplicitPrefixEntropyHeight start M B))
        (harperPrefixEulerNormalizer y start)
        (harperPrefixInverseEulerNormalizer y start) ≤
      Real.exp (-2 * B) := by
  unfold harperPrefixEnergyWindowFirstMomentBudget
  calc
    (∑ m ∈ Finset.Icc 1 n,
        ∑ u ∈ harperScheduledVerticalPrefixFamily start n m M,
          (harperPrefixEulerNormalizer y start m /
              harperExplicitPrefixUpperWindow y start
                (harperExplicitPrefixEntropyHeight start M B) m u +
            harperPrefixInverseEulerNormalizer y start m u *
              harperExplicitPrefixLowerWindow y start
                (harperExplicitPrefixEntropyHeight start M B) m u)) =
        ∑ m ∈ Finset.Icc 1 n,
          ∑ _u ∈ harperScheduledVerticalPrefixFamily start n m M,
            2 * Real.exp
              (-2 * harperExplicitPrefixEntropyHeight start M B m) := by
      apply Finset.sum_congr rfl
      intro m hm
      apply Finset.sum_congr rfl
      intro u hu
      exact harper_explicitPrefixWindow_onePath_cost y start
        (harperExplicitPrefixEntropyHeight start M B) m u
    _ ≤ ∑ _m ∈ Finset.Icc 1 n,
          Real.exp (-2 * B) /
            (2 * (((_m + 1 : ℕ) : ℝ) ^ 2)) := by
      apply Finset.sum_le_sum
      intro m hm
      rw [Finset.sum_const, nsmul_eq_mul,
        exp_neg_two_mul_harperExplicitPrefixEntropyHeight]
      let C : ℝ :=
        ((harperScheduledVerticalPrefixFamily start n m M).card : ℝ)
      let Q : ℝ :=
        ((harperExplicitPrefixEntropyCoefficient M *
          harperScheduledVerticalMeshRefinement m *
          2 ^ (start + m) : ℕ) : ℝ)
      have hCQ : C ≤ Q := by
        dsimp [C, Q]
        exact_mod_cast
          card_harperScheduledVerticalPrefixFamily_le_entropyCoefficient
            start n m M
      have hQ : 0 < Q := by
        dsimp only [Q]
        exact_mod_cast (show
          0 < harperExplicitPrefixEntropyCoefficient M *
            harperScheduledVerticalMeshRefinement m * 2 ^ (start + m) by
          have hcoef : 0 < harperExplicitPrefixEntropyCoefficient M := by
            unfold harperExplicitPrefixEntropyCoefficient
            omega
          exact Nat.mul_pos
            (Nat.mul_pos hcoef
              (harperScheduledVerticalMeshRefinement_pos m))
            (pow_pos (by omega) _))
      have hE : 0 ≤ Real.exp (-2 * B) := (Real.exp_pos _).le
      have hden :
          ((4 * harperExplicitPrefixEntropyCoefficient M *
            harperScheduledVerticalMeshRefinement m *
            2 ^ (start + m) * (m + 1) ^ 2 : ℕ) : ℝ) =
            4 * Q * ((m + 1 : ℕ) : ℝ) ^ 2 := by
        dsimp [Q]
        push_cast
        ring
      rw [hden]
      change C *
          (2 * (Real.exp (-2 * B) /
            (4 * Q * ((m + 1 : ℕ) : ℝ) ^ 2))) ≤
        Real.exp (-2 * B) / (2 * (((m + 1 : ℕ) : ℝ) ^ 2))
      have hratio : C / Q ≤ 1 := (div_le_one hQ).mpr hCQ
      calc
        C * (2 * (Real.exp (-2 * B) /
            (4 * Q * ((m + 1 : ℕ) : ℝ) ^ 2))) =
            (C / Q) *
              (Real.exp (-2 * B) /
                (2 * (((m + 1 : ℕ) : ℝ) ^ 2))) := by
          field_simp
          norm_num
        _ ≤ 1 * (Real.exp (-2 * B) /
              (2 * (((m + 1 : ℕ) : ℝ) ^ 2))) := by
          exact mul_le_mul_of_nonneg_right hratio
            (div_nonneg hE (by positivity))
        _ = _ := one_mul _
    _ ≤ Real.exp (-2 * B) := by
      have hE : 0 ≤ Real.exp (-2 * B) := (Real.exp_pos _).le
      have hsum :
          (∑ m ∈ Finset.Icc 1 n,
            ((((m : ℕ) : ℝ) ^ 2)⁻¹)) ≤ 2 := by
        have hset : Finset.Icc 1 n = Finset.Ioo 0 (n + 1) := by
          ext m
          simp only [Finset.mem_Icc, Finset.mem_Ioo]
          omega
        rw [hset]
        have h := sum_Ioo_inv_sq_le (α := ℝ) 0 (n + 1)
        norm_num at h
        exact h
      calc
        (∑ m ∈ Finset.Icc 1 n,
            Real.exp (-2 * B) /
              (2 * (((m + 1 : ℕ) : ℝ) ^ 2))) ≤
            ∑ m ∈ Finset.Icc 1 n,
              (Real.exp (-2 * B) / 2) *
                ((((m : ℕ) : ℝ) ^ 2)⁻¹) := by
          apply Finset.sum_le_sum
          intro m hm
          have hm1 : 1 ≤ m := (Finset.mem_Icc.mp hm).1
          have hm0 : (0 : ℝ) < m := by exact_mod_cast (lt_of_lt_of_le (by omega) hm1)
          have hsq : ((m : ℝ) ^ 2) ≤ ((m + 1 : ℕ) : ℝ) ^ 2 := by
            push_cast
            nlinarith
          rw [show (Real.exp (-2 * B) / 2) *
              ((((m : ℕ) : ℝ) ^ 2)⁻¹) =
                Real.exp (-2 * B) / (2 * ((m : ℝ) ^ 2)) by
            field_simp]
          exact div_le_div_of_nonneg_left hE (by positivity)
            (mul_le_mul_of_nonneg_left hsq (by norm_num))
        _ = (Real.exp (-2 * B) / 2) *
              (∑ m ∈ Finset.Icc 1 n,
                ((((m : ℕ) : ℝ) ^ 2)⁻¹)) := by
          rw [Finset.mul_sum]
        _ ≤ (Real.exp (-2 * B) / 2) * 2 :=
          mul_le_mul_of_nonneg_left hsum (by positivity)
        _ = Real.exp (-2 * B) := by ring

/-- The fair complement is exponentially small in the free base height
`B`, after prefix entropy is absorbed into the length-dependent profile. -/
theorem harperFairCubeLaw_real_compl_entropyPrefixGoodSet_le
    (y start n M : ℕ) (B : ℝ) :
    (harperFairCubeLaw y).real
        (harperPrefixEnergyWindowGoodSet y start n M
          (harperExplicitPrefixLowerWindow y start
            (harperExplicitPrefixEntropyHeight start M B))
          (harperExplicitPrefixUpperWindow y start
            (harperExplicitPrefixEntropyHeight start M B)))ᶜ ≤
      Real.exp (-2 * B) := by
  refine (harperFairCubeLaw_real_compl_prefixEnergyWindowGoodSet_le_firstMomentBudget
    y start n M
      (harperExplicitPrefixLowerWindow y start
        (harperExplicitPrefixEntropyHeight start M B))
      (harperExplicitPrefixUpperWindow y start
        (harperExplicitPrefixEntropyHeight start M B))
      (harperPrefixEulerNormalizer y start)
      (harperPrefixInverseEulerNormalizer y start)
      (fun m hm u hu ↦ harperExplicitPrefixLowerWindow_pos y start _ m u)
      (fun m hm u hu ↦ harperExplicitPrefixUpperWindow_pos y start _ m u)
      (fun m hm ↦ le_rfl)
      (fun m hm u hu ↦
        (harperPrefixEulerReciprocalFirstMoment_eq_inverseNormalizer
          y start m u).le)).trans
    (harperPrefixEnergyWindowFirstMomentBudget_entropyHeight_le
      y start n M B)

/-! ## Cumulative product and drift comparisons -/

/-- The logarithm of the exact fair Euler normalizer is bounded by the
cumulative reciprocal prime mass. -/
theorem log_harperPrefixEulerNormalizer_le_reciprocalMass_sum
    (y start m : ℕ) :
    Real.log (harperPrefixEulerNormalizer y start m) ≤
      ∑ i : Fin m,
        harperScheduledReciprocalMass y (start + (i : ℕ)) := by
  unfold harperPrefixEulerNormalizer
  rw [Real.log_prod]
  · calc
      (∑ p ∈ harperScheduledPrimeRangeFrom y start m,
          Real.log (1 + (p.1 : ℝ)⁻¹)) ≤
          ∑ p ∈ harperScheduledPrimeRangeFrom y start m,
            (p.1 : ℝ)⁻¹ := by
        apply Finset.sum_le_sum
        intro p hp
        have hp0 : (0 : ℝ) < p.1 := by
          exact_mod_cast (Nat.prime_of_mem_primesBelow p.property).pos
        have hpos : 0 < 1 + (p.1 : ℝ)⁻¹ := by positivity
        have hlog := Real.log_le_sub_one_of_pos hpos
        simpa only [add_sub_cancel_left] using! hlog
      _ = ∑ i : Fin m,
          harperScheduledReciprocalMass y (start + (i : ℕ)) := by
        unfold harperScheduledPrimeRangeFrom
          harperScheduledReciprocalMass
        rw [Finset.sum_biUnion
          (pairwiseDisjoint_harperScheduledPrimeBlock_add y start m)]
        exact (Fin.sum_univ_eq_sum_range
          (fun i : ℕ ↦
            ∑ p ∈ harperScheduledPrimeBlock y (start + i),
              (p.1 : ℝ)⁻¹) m).symm
  · intro p hp
    have hp0 : (0 : ℝ) < p.1 := by
      exact_mod_cast (Nat.prime_of_mem_primesBelow p.property).pos
    positivity

/-- A cumulative reciprocal-mass estimate immediately bounds the logarithm
of the product normalizer. -/
theorem log_harperPrefixEulerNormalizer_le_of_reciprocal_error
    (y start m : ℕ) (E : ℝ)
    (herror :
      |∑ i : Fin m,
          harperScheduledReciprocalMass y (start + (i : ℕ)) -
        (m : ℝ) * Real.log 2| ≤ E) :
    Real.log (harperPrefixEulerNormalizer y start m) ≤
      (m : ℝ) * Real.log 2 + E := by
  exact (log_harperPrefixEulerNormalizer_le_reciprocalMass_sum
    y start m).trans (by linarith [le_of_abs_le herror])

/-- The diagonal second-harmonic correction is controlled by twice the
summable inverse-square mass. -/
theorem harperScheduledDiagonalCorrection_le_two_squareMass
    (y j : ℕ) (t : ℝ) :
    harperScheduledDiagonalCorrection y j t ≤
      2 * harperScheduledSquareMass y j := by
  unfold harperScheduledDiagonalCorrection harperScheduledSquareMass
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro p hp
  have hp0 : (0 : ℝ) < p.1 := by
    exact_mod_cast (Nat.prime_of_mem_primesBelow p.property).pos
  have hnum0 : 0 ≤
      1 + Real.cos (2 * (t * Real.log (p.1 : ℝ))) := by
    linarith [Real.neg_one_le_cos (2 * (t * Real.log (p.1 : ℝ)))]
  have hnum2 :
      1 + Real.cos (2 * (t * Real.log (p.1 : ℝ))) ≤ 2 := by
    linarith [Real.cos_le_one (2 * (t * Real.log (p.1 : ℝ)))]
  have hden0 : 0 < (p.1 : ℝ) * (p.1 : ℝ) := mul_pos hp0 hp0
  have hden : (p.1 : ℝ) * (p.1 : ℝ) ≤
      (p.1 : ℝ) * (p.1 + 1) := by
    nlinarith
  calc
    (1 + Real.cos (2 * (t * Real.log (p.1 : ℝ)))) /
          ((p.1 : ℝ) * (p.1 + 1)) ≤
        2 / ((p.1 : ℝ) * (p.1 + 1)) :=
      div_le_div_of_nonneg_right hnum2 (by positivity)
    _ ≤ 2 / ((p.1 : ℝ) * (p.1 : ℝ)) :=
      div_le_div_of_nonneg_left (by norm_num) hden0 hden
    _ = 2 * (p.1 : ℝ)⁻¹ ^ 2 := by field_simp

/-- Deterministic sharp cumulative drift wrapper.  Once the local checkpoint
phase losses have a summable envelope `delta`, all arithmetic errors enter
additively rather than as a coarse loss in the linear drift slope. -/
theorem abs_harperScheduledVerticalCumulativeDrift_sub_log_two_le_of_errors
    (y start n : ℕ) (t : ℝ) (k : Fin n)
    (delta : Fin n → ℝ) (R O S D : ℝ)
    (hdelta0 : ∀ i ∈ Finset.Iic k, 0 ≤ delta i)
    (hdelta : (∑ i ∈ Finset.Iic k, delta i) ≤ D)
    (hmass : ∀ i ∈ Finset.Iic k,
      harperScheduledReciprocalMass y (start + (i : ℕ)) ≤ 3 / 2)
    (hscale : ∀ i ∈ Finset.Iic k,
      |harperScheduledVerticalCheckpoint start n t i - t| *
          Real.log (harperBlockEndpoint (start + (i : ℕ) + 1) : ℝ) ≤
        delta i)
    (hreciprocal :
      |∑ i ∈ Finset.Iic k,
          harperScheduledReciprocalMass y (start + (i : ℕ)) -
        ((k.val + 1 : ℕ) : ℝ) * Real.log 2| ≤ R)
    (hoscillation :
      (∑ i ∈ Finset.Iic k,
        |harperScheduledOscillationMass y (start + (i : ℕ)) (2 * t)|) ≤ O)
    (hsquare :
      (∑ i ∈ Finset.Iic k,
        harperScheduledSquareMass y (start + (i : ℕ))) ≤ S) :
    |harperScheduledVerticalCumulativeDrift y start n t k -
        ((k.val + 1 : ℕ) : ℝ) * Real.log 2| ≤
      R + (1 / 2 : ℝ) * O + 2 * S + (9 / 2 : ℝ) * D := by
  let actual : Fin n → ℝ := fun i ↦
    harperLogMainBlockMean y
      (harperScheduledPrimeBlock y (start + (i : ℕ))) t
      (harperScheduledVerticalCheckpoint start n t i)
  let diagonal : Fin n → ℝ := fun i ↦
    harperLogMainBlockMean y
      (harperScheduledPrimeBlock y (start + (i : ℕ))) t t
  let reciprocal : Fin n → ℝ := fun i ↦
    harperScheduledReciprocalMass y (start + (i : ℕ))
  have hoffPoint : ∀ i ∈ Finset.Iic k,
      |actual i - diagonal i| ≤ (9 / 2 : ℝ) * delta i := by
    intro i hi
    exact
      abs_harperScheduledLogMainBlockMean_sub_diagonal_le_nine_halves_mul
        y (start + (i : ℕ)) t
        (harperScheduledVerticalCheckpoint start n t i) (delta i)
        (hdelta0 i hi) (hmass i hi) (hscale i hi)
  have hoff :
      |(∑ i ∈ Finset.Iic k, actual i) -
          ∑ i ∈ Finset.Iic k, diagonal i| ≤
        (9 / 2 : ℝ) * D := by
    rw [← Finset.sum_sub_distrib]
    calc
      |∑ i ∈ Finset.Iic k, (actual i - diagonal i)| ≤
          ∑ i ∈ Finset.Iic k, |actual i - diagonal i| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ i ∈ Finset.Iic k, (9 / 2 : ℝ) * delta i :=
        Finset.sum_le_sum fun i hi ↦ hoffPoint i hi
      _ = (9 / 2 : ℝ) * ∑ i ∈ Finset.Iic k, delta i := by
        rw [Finset.mul_sum]
      _ ≤ (9 / 2 : ℝ) * D :=
        mul_le_mul_of_nonneg_left hdelta (by norm_num)
  have hdiagPoint : ∀ i ∈ Finset.Iic k,
      |diagonal i - reciprocal i| ≤
        (1 / 2 : ℝ) *
            |harperScheduledOscillationMass y
              (start + (i : ℕ)) (2 * t)| +
          2 * harperScheduledSquareMass y (start + (i : ℕ)) := by
    intro i hi
    have hcorr0 := harperScheduledDiagonalCorrection_nonneg
      y (start + (i : ℕ)) t
    have hcorr := harperScheduledDiagonalCorrection_le_two_squareMass
      y (start + (i : ℕ)) t
    rw [show diagonal i =
        reciprocal i + (1 / 2 : ℝ) *
            harperScheduledOscillationMass y (start + (i : ℕ)) (2 * t) -
          harperScheduledDiagonalCorrection y (start + (i : ℕ)) t by
      simpa only [actual, diagonal, reciprocal,
        harperScheduledReciprocalMass,
        harperScheduledOscillationMass] using!
          harperScheduledDiagonalMainMean_eq y (start + (i : ℕ)) t]
    rw [show reciprocal i + (1 / 2 : ℝ) *
          harperScheduledOscillationMass y (start + (i : ℕ)) (2 * t) -
        harperScheduledDiagonalCorrection y (start + (i : ℕ)) t -
        reciprocal i =
          (1 / 2 : ℝ) *
            harperScheduledOscillationMass y (start + (i : ℕ)) (2 * t) -
          harperScheduledDiagonalCorrection y (start + (i : ℕ)) t by ring]
    calc
      |(1 / 2 : ℝ) *
            harperScheduledOscillationMass y (start + (i : ℕ)) (2 * t) -
          harperScheduledDiagonalCorrection y (start + (i : ℕ)) t| ≤
          |(1 / 2 : ℝ) *
            harperScheduledOscillationMass y (start + (i : ℕ)) (2 * t)| +
          |harperScheduledDiagonalCorrection y (start + (i : ℕ)) t| :=
        abs_sub _ _
      _ = (1 / 2 : ℝ) *
            |harperScheduledOscillationMass y (start + (i : ℕ)) (2 * t)| +
          harperScheduledDiagonalCorrection y (start + (i : ℕ)) t := by
        rw [abs_mul, abs_of_nonneg (by norm_num), abs_of_nonneg hcorr0]
      _ ≤ _ := by
        simpa only [add_comm] using!
          add_le_add_left hcorr
            ((1 / 2 : ℝ) *
              |harperScheduledOscillationMass y
                (start + (i : ℕ)) (2 * t)|)
  have hdiag :
      |(∑ i ∈ Finset.Iic k, diagonal i) -
          ∑ i ∈ Finset.Iic k, reciprocal i| ≤
        (1 / 2 : ℝ) * O + 2 * S := by
    rw [← Finset.sum_sub_distrib]
    calc
      |∑ i ∈ Finset.Iic k, (diagonal i - reciprocal i)| ≤
          ∑ i ∈ Finset.Iic k, |diagonal i - reciprocal i| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ i ∈ Finset.Iic k,
          ((1 / 2 : ℝ) *
              |harperScheduledOscillationMass y
                (start + (i : ℕ)) (2 * t)| +
            2 * harperScheduledSquareMass y (start + (i : ℕ))) :=
        Finset.sum_le_sum fun i hi ↦ hdiagPoint i hi
      _ = (1 / 2 : ℝ) *
            (∑ i ∈ Finset.Iic k,
              |harperScheduledOscillationMass y
                (start + (i : ℕ)) (2 * t)|) +
          2 * (∑ i ∈ Finset.Iic k,
            harperScheduledSquareMass y (start + (i : ℕ))) := by
        simp only [Finset.sum_add_distrib]
        rw [Finset.mul_sum, Finset.mul_sum]
      _ ≤ (1 / 2 : ℝ) * O + 2 * S :=
        add_le_add
          (mul_le_mul_of_nonneg_left hoscillation (by norm_num))
          (mul_le_mul_of_nonneg_left hsquare (by norm_num))
  unfold harperScheduledVerticalCumulativeDrift
  change |∑ i ∈ Finset.Iic k, actual i -
      ((k.val + 1 : ℕ) : ℝ) * Real.log 2| ≤ _
  calc
    |(∑ i ∈ Finset.Iic k, actual i) -
        ((k.val + 1 : ℕ) : ℝ) * Real.log 2| ≤
      |(∑ i ∈ Finset.Iic k, actual i) -
        ∑ i ∈ Finset.Iic k, diagonal i| +
      |(∑ i ∈ Finset.Iic k, diagonal i) -
        ∑ i ∈ Finset.Iic k, reciprocal i| +
      |(∑ i ∈ Finset.Iic k, reciprocal i) -
        ((k.val + 1 : ℕ) : ℝ) * Real.log 2| := by
      calc
        _ = |((∑ i ∈ Finset.Iic k, actual i) -
                ∑ i ∈ Finset.Iic k, diagonal i) +
              ((∑ i ∈ Finset.Iic k, diagonal i) -
                ∑ i ∈ Finset.Iic k, reciprocal i) +
              ((∑ i ∈ Finset.Iic k, reciprocal i) -
                ((k.val + 1 : ℕ) : ℝ) * Real.log 2)| := by ring_nf
        _ ≤ _ := (abs_add_three _ _ _)
    _ ≤ _ := by
      linarith

/-! ## Automatic bridge premises for the explicit windows -/

/-- Relaxed lower barrier paired with the explicit lower energy window. -/
noncomputable def harperExplicitPrefixLowerBarrier
    (y start n : ℕ) (t : ℝ) (height driftUpper : ℕ → ℝ)
    (k : Fin n) : ℝ :=
  Real.log
      (harperExplicitPrefixLowerWindow y start height (k.val + 1)
        (harperScheduledVerticalPrefixAt start n t k)) / 2 -
    driftUpper (k.val + 1) -
    harperScheduledLogTaylorAllowance start

/-- Product-normalizer and cumulative-drift bounds reduce both bridge
premises to one numerical upper-barrier inequality. -/
theorem harperExplicitPrefixWindows_bridge_comparisons
    (y start n : ℕ) (t x c E : ℝ)
    (height driftLower driftUpper : ℕ → ℝ)
    (hproduct : ∀ k : Fin n,
      Real.log (harperPrefixEulerNormalizer y start (k.val + 1)) ≤
        ((k.val + 1 : ℕ) : ℝ) * Real.log 2 + E)
    (hdrift : ∀ k : Fin n,
      driftLower (k.val + 1) ≤
          harperScheduledVerticalCumulativeDrift y start n t k ∧
        harperScheduledVerticalCumulativeDrift y start n t k ≤
          driftUpper (k.val + 1))
    (hnumerical : ∀ k : Fin n,
      height (k.val + 1) +
          ((((k.val + 1 : ℕ) : ℝ) * Real.log 2 + E) / 2) +
          harperScheduledLogTaylorAllowance start ≤
        harperNormalizedReverseLogBarrier n x c k +
          driftLower (k.val + 1)) :
    (∀ k : Fin n,
      harperExplicitPrefixLowerBarrier y start n t height driftUpper k +
          harperScheduledVerticalCumulativeDrift y start n t k +
          harperScheduledLogTaylorAllowance start ≤
        Real.log
          (harperExplicitPrefixLowerWindow y start height (k.val + 1)
            (harperScheduledVerticalPrefixAt start n t k)) / 2) ∧
    (∀ k : Fin n,
      Real.log
          (harperExplicitPrefixUpperWindow y start height (k.val + 1)
            (harperScheduledVerticalPrefixAt start n t k)) / 2 ≤
        harperNormalizedReverseLogBarrier n x c k +
          harperScheduledVerticalCumulativeDrift y start n t k -
          harperScheduledLogTaylorAllowance start) := by
  constructor
  · intro k
    unfold harperExplicitPrefixLowerBarrier
    linarith [(hdrift k).2]
  · intro k
    rw [log_harperExplicitPrefixUpperWindow]
    have hp := hproduct k
    have hd := (hdrift k).1
    have hn := hnumerical k
    linarith

/-- The bridge naturally furnished by the prefix-local entropy allocation.
After cancellation of the linear normalizer and drift terms, the centered
upper barrier is a fixed base plus `8 * log (k+2)`.  In particular, no
full-length `log n` is introduced. -/
theorem harperExplicitPrefixWindows_positiveLogBridge_comparisons
    (y start n M : ℕ) (t B E D : ℝ)
    (hproduct : ∀ k : Fin n,
      Real.log (harperPrefixEulerNormalizer y start (k.val + 1)) ≤
        ((k.val + 1 : ℕ) : ℝ) * Real.log 2 + E)
    (hdrift : ∀ k : Fin n,
      |harperScheduledVerticalCumulativeDrift y start n t k -
          ((k.val + 1 : ℕ) : ℝ) * Real.log 2| ≤ D) :
    (∀ k : Fin n,
      harperExplicitPrefixLowerBarrier y start n t
          (harperExplicitPrefixEntropyHeight start M B)
          (fun m ↦ (m : ℝ) * Real.log 2 + D) k +
          harperScheduledVerticalCumulativeDrift y start n t k +
          harperScheduledLogTaylorAllowance start ≤
        Real.log
          (harperExplicitPrefixLowerWindow y start
            (harperExplicitPrefixEntropyHeight start M B) (k.val + 1)
            (harperScheduledVerticalPrefixAt start n t k)) / 2) ∧
    (∀ k : Fin n,
      Real.log
          (harperExplicitPrefixUpperWindow y start
            (harperExplicitPrefixEntropyHeight start M B) (k.val + 1)
            (harperScheduledVerticalPrefixAt start n t k)) / 2 ≤
        (harperExplicitPrefixEntropyBase start M + B + E / 2 + D +
            harperScheduledLogTaylorAllowance start +
          8 * Real.log ((k.val + 2 : ℕ) : ℝ)) +
          harperScheduledVerticalCumulativeDrift y start n t k -
          harperScheduledLogTaylorAllowance start) := by
  constructor
  · intro k
    unfold harperExplicitPrefixLowerBarrier
    have hd := le_of_abs_le (hdrift k)
    linarith
  · intro k
    rw [log_harperExplicitPrefixUpperWindow]
    have hp := hproduct k
    have hd := neg_le_of_abs_le (hdrift k)
    have hh := harperExplicitPrefixEntropyHeight_le
      start M B (k.val + 1)
    push_cast at hh hp hd ⊢
    ring_nf at hh hp hd ⊢
    linarith

end Erdos.Problem520
