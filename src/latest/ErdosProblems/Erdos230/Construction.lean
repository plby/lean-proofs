/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import ErdosProblems.Erdos230.Asymptotics
import ErdosProblems.Erdos230.GaussianCutoff
import ErdosProblems.Erdos230.GaussianPoisson
import ErdosProblems.Erdos230.Rounding

/-!
# The explicit Gaussian chirp for Erdős Problem 230

This file specializes the analytic and probabilistic estimates to the scales
`n = m^18`, `s = m^12`, `K = m^15`, and `r = m^6`.
-/

open scoped BigOperators Interval

namespace Erdos230

noncomputable section

open GaussianCutoff GaussianPoisson Correction MeasureTheory Set

/-- Number of nonconstant coefficients in the construction. -/
def constructionDegree (m : ℕ) : ℕ := m ^ 18

/-- Width of the Gaussian used to smooth the central interval. -/
def constructionScale (m : ℕ) : ℝ := (m : ℝ) ^ 12

/-- Size of each boundary strip removed before Gaussian smoothing. -/
def constructionMargin (m : ℕ) : ℕ := m ^ 15

/-- Damping ratio `s^2 / n`. -/
def constructionRatio (m : ℕ) : ℝ := (m : ℝ) ^ 6

/-- The number of interpolation grid points. -/
def constructionGrid (m : ℕ) : ℕ := constructionDegree m ^ 3

/-- The sub-unimodular Gaussian chirp coefficients. -/
def baseCoefficient (m : ℕ) : Fin (constructionDegree m + 1) → ℂ :=
  fun k =>
    (chi (constructionScale m) (constructionMargin m)
        (constructionDegree m) k.1 : ℂ) *
      e (((k.1 : ℝ) ^ 2) / (2 * constructionDegree m) - (k.1 : ℝ) / 2)

lemma two_margin_le_degree {m : ℕ} (hm : 2 ≤ m) :
    2 * constructionMargin m ≤ constructionDegree m := by
  simp only [constructionMargin, constructionDegree]
  calc
    2 * m ^ 15 ≤ m ^ 3 * m ^ 15 := by
      gcongr
      exact hm.trans (Nat.le_pow (a := m) (b := 3) (by norm_num))
    _ = m ^ 18 := by ring

lemma constructionScale_pos {m : ℕ} (hm : 2 ≤ m) :
    0 < constructionScale m := by
  simp only [constructionScale]
  positivity

lemma constructionRatio_pos {m : ℕ} (hm : 2 ≤ m) :
    0 < constructionRatio m := by
  simp only [constructionRatio]
  positivity

lemma constructionDegree_pos {m : ℕ} (hm : 2 ≤ m) :
    0 < constructionDegree m := by
  simp only [constructionDegree]
  positivity

lemma constructionGrid_pos {m : ℕ} (hm : 2 ≤ m) :
    0 < constructionGrid m := by
  exact pow_pos (constructionDegree_pos hm) 3

@[simp]
lemma norm_baseCoefficient {m : ℕ} (hm : 2 ≤ m)
    (k : Fin (constructionDegree m + 1)) :
    ‖baseCoefficient m k‖ =
      chi (constructionScale m) (constructionMargin m)
        (constructionDegree m) k.1 := by
  rw [baseCoefficient, norm_mul, norm_e, mul_one, Complex.norm_real,
    Real.norm_of_nonneg]
  exact chi_nonneg (constructionScale_pos hm) (two_margin_le_degree hm) k.1

lemma norm_baseCoefficient_le_one {m : ℕ} (hm : 2 ≤ m)
    (k : Fin (constructionDegree m + 1)) :
    ‖baseCoefficient m k‖ ≤ 1 := by
  rw [norm_baseCoefficient hm]
  exact chi_le_one (constructionScale_pos hm) (two_margin_le_degree hm) k.1

/-- The exact chord defect of the Gaussian chirp is the cutoff's loss of
squared mass. -/
lemma defect_baseCoefficient {m : ℕ} (hm : 2 ≤ m) :
    defect (baseCoefficient m) =
      ∑ k : Fin (constructionDegree m + 1),
        (1 - chi (constructionScale m) (constructionMargin m)
          (constructionDegree m) k.1 ^ 2) := by
  rw [defect]
  apply Finset.sum_congr rfl
  intro k _
  rw [norm_baseCoefficient hm]

lemma defect_baseCoefficient_nonneg {m : ℕ} (hm : 2 ≤ m) :
    0 ≤ defect (baseCoefficient m) := by
  rw [defect]
  exact Finset.sum_nonneg fun k _ =>
    defect_term_nonneg (norm_baseCoefficient_le_one hm k)

lemma defect_baseCoefficient_le_raw {m : ℕ} (hm : 2 ≤ m) :
    defect (baseCoefficient m) ≤
      4 * (constructionMargin m : ℝ) + 4 * (constructionScale m + 1) := by
  rw [defect_baseCoefficient hm]
  calc
    (∑ k : Fin (constructionDegree m + 1),
        (1 - chi (constructionScale m) (constructionMargin m)
          (constructionDegree m) k.1 ^ 2)) =
        ∑ k ∈ Finset.range (constructionDegree m + 1),
          (1 - chi (constructionScale m) (constructionMargin m)
            (constructionDegree m) k ^ 2) := by
      exact Fin.sum_univ_eq_sum_range
        (fun k : ℕ => 1 - chi (constructionScale m) (constructionMargin m)
          (constructionDegree m) k ^ 2) (constructionDegree m + 1)
    _ ≤ _ := sum_one_sub_chi_sq_range_le
      (constructionScale_pos hm) (two_margin_le_degree hm)

lemma defect_baseCoefficient_le {m : ℕ} (hm : 2 ≤ m) :
    defect (baseCoefficient m) ≤ 8 * (m : ℝ) ^ 15 := by
  have hmreal : (2 : ℝ) ≤ m := by exact_mod_cast hm
  have hmone : (1 : ℝ) ≤ m := by linarith
  have hm12 : (1 : ℝ) ≤ (m : ℝ) ^ 12 := one_le_pow₀ hmone
  have hm3 : (2 : ℝ) ≤ (m : ℝ) ^ 3 := by
    calc
      (2 : ℝ) ≤ m := hmreal
      _ = (m : ℝ) ^ 1 := by ring
      _ ≤ (m : ℝ) ^ 3 := pow_le_pow_right₀ hmone (by norm_num)
  have hscale : (m : ℝ) ^ 12 + 1 ≤ (m : ℝ) ^ 15 := by
    calc
      (m : ℝ) ^ 12 + 1 ≤ 2 * (m : ℝ) ^ 12 := by linarith
      _ ≤ (m : ℝ) ^ 3 * (m : ℝ) ^ 12 := by gcongr
      _ = (m : ℝ) ^ 15 := by ring
  calc
    defect (baseCoefficient m) ≤
        4 * (constructionMargin m : ℝ) +
          4 * (constructionScale m + 1) := defect_baseCoefficient_le_raw hm
    _ = 4 * (m : ℝ) ^ 15 + 4 * ((m : ℝ) ^ 12 + 1) := by
      simp [constructionMargin, constructionScale]
    _ ≤ 8 * (m : ℝ) ^ 15 := by nlinarith

lemma constructionGrid_cast (m : ℕ) :
    (constructionGrid m : ℝ) = (m : ℝ) ^ 54 := by
  simp only [constructionGrid, constructionDegree, Nat.cast_pow]
  ring

lemma constructionRatio_eq {m : ℕ} (hm : 2 ≤ m) :
    constructionScale m ^ 2 / (constructionDegree m : ℝ) =
      constructionRatio m := by
  have hm0 : (m : ℝ) ≠ 0 := by positivity
  simp only [constructionScale, constructionDegree, constructionRatio, Nat.cast_pow]
  field_simp

/-- The full, untruncated smoothed chirp at the construction parameters. -/
def constructionFullValue (m : ℕ) (theta : ℝ) : ℂ :=
  fullIntegerSmoothedChirp (constructionDegree m) (constructionScale m)
    (constructionMargin m) theta

/-- The integer-indexed coefficient series whose integral form is
`constructionFullValue`. -/
def integerChirpCoefficient (m : ℕ) (theta : ℝ) (k : ℤ) : ℂ :=
  (chi (constructionScale m) (constructionMargin m)
      (constructionDegree m) k : ℂ) *
    e (chirpPhase (constructionDegree m) theta k)

@[simp]
lemma norm_integerChirpCoefficient {m : ℕ} (hm : 2 ≤ m)
    (theta : ℝ) (k : ℤ) :
    ‖integerChirpCoefficient m theta k‖ =
      chi (constructionScale m) (constructionMargin m)
        (constructionDegree m) k := by
  rw [integerChirpCoefficient, norm_mul, norm_e, mul_one, Complex.norm_real,
    Real.norm_of_nonneg]
  exact chi_nonneg (constructionScale_pos hm) (two_margin_le_degree hm) k

lemma norm_integerChirpCoefficient_neg_add_one {m : ℕ} (hm : 2 ≤ m)
    (theta : ℝ) (j : ℕ) :
    ‖integerChirpCoefficient m theta (-(j + 1 : ℤ))‖ =
      outsideLeft (constructionScale m) (constructionMargin m)
        (constructionDegree m) j := by
  rw [norm_integerChirpCoefficient hm]
  simp [outsideLeft]

lemma norm_integerChirpCoefficient_degree_add_one {m : ℕ} (hm : 2 ≤ m)
    (theta : ℝ) (j : ℕ) :
    ‖integerChirpCoefficient m theta
        (constructionDegree m + j + 1 : ℤ)‖ =
      outsideRight (constructionScale m) (constructionMargin m)
        (constructionDegree m) j := by
  rw [norm_integerChirpCoefficient hm]
  simp [outsideRight]

lemma summable_norm_integerChirpCoefficient {m : ℕ} (hm : 2 ≤ m)
    (theta : ℝ) : Summable fun k : ℤ => ‖integerChirpCoefficient m theta k‖ := by
  apply Summable.of_add_one_of_neg_add_one
  · apply (summable_nat_add_iff (constructionDegree m)).mp
    have heq : (fun j : ℕ => ‖integerChirpCoefficient m theta
        (((j + constructionDegree m : ℕ) : ℤ) + 1)‖) =
        outsideRight (constructionScale m) (constructionMargin m)
          (constructionDegree m) := by
      funext j
      convert norm_integerChirpCoefficient_degree_add_one hm theta j using 1 <;>
        push_cast <;> ring
    rw [heq]
    exact summable_outsideRight (constructionScale_pos hm)
      (two_margin_le_degree hm)
  · have heq : (fun j : ℕ => ‖integerChirpCoefficient m theta
        (-((j : ℤ) + 1))‖) =
        outsideLeft (constructionScale m) (constructionMargin m)
          (constructionDegree m) := by
      funext j
      exact norm_integerChirpCoefficient_neg_add_one hm theta j
    rw [heq]
    exact summable_outsideLeft (constructionScale_pos hm)
      (two_margin_le_degree hm)

lemma summable_integerChirpCoefficient {m : ℕ} (hm : 2 ≤ m)
    (theta : ℝ) : Summable (integerChirpCoefficient m theta) :=
  (summable_norm_integerChirpCoefficient hm theta).of_norm

lemma gaussianKernel_eq_phi {s : ℝ} (hs : 0 < s) (x : ℝ) :
    gaussianKernel s x = phi s x := by
  simp only [gaussianKernel, phi]
  congr 2
  field_simp [hs.ne']

lemma gaussianCutoff_eq_chi {s : ℝ} (hs : 0 < s) {K n : ℕ}
    (hKn : 2 * K ≤ n) (k : ℤ) :
    gaussianCutoff s K n k = chi s K n k := by
  have hKn' : K ≤ n := by omega
  have hcast : ((n - K : ℕ) : ℝ) = (n : ℝ) - K := by
    exact Nat.cast_sub hKn'
  rw [gaussianCutoff, chi, hcast]
  apply intervalIntegral.integral_congr
  intro y _
  exact gaussianKernel_eq_phi hs ((k : ℝ) - y)

lemma intervalIntegral_norm_gaussianChirpAtom_eq_chi {m : ℕ}
    (hm : 2 ≤ m) (theta : ℝ) (k : ℤ) :
    (∫ y in (constructionMargin m : ℝ)..
        (constructionDegree m : ℝ) - constructionMargin m,
        ‖gaussianChirpAtom (constructionDegree m) (constructionScale m)
          theta y k‖) =
      chi (constructionScale m) (constructionMargin m)
        (constructionDegree m) k := by
  have hn : 0 < (constructionDegree m : ℝ) := by
    exact_mod_cast constructionDegree_pos hm
  have hs := constructionScale_pos hm
  have hKn' : constructionMargin m ≤ constructionDegree m := by
    have := two_margin_le_degree hm
    omega
  have hcast : (((constructionDegree m - constructionMargin m : ℕ) : ℝ)) =
      (constructionDegree m : ℝ) - constructionMargin m := by
    exact Nat.cast_sub hKn'
  rw [chi, hcast]
  apply intervalIntegral.integral_congr
  intro y _
  change ‖gaussianChirpAtom (constructionDegree m) (constructionScale m)
    theta y k‖ = phi (constructionScale m) ((k : ℝ) - y)
  rw [gaussianChirpAtom_eq_cutoffIntegrand _ _ _ _ _ hn hs,
    norm_mul, norm_e, mul_one, Complex.norm_real, Real.norm_of_nonneg]
  · exact gaussianKernel_eq_phi hs ((k : ℝ) - y)
  · exact mul_nonneg (inv_nonneg.mpr hs.le) (Real.exp_pos _).le

/-- The integral definition used for Poisson summation is exactly the
absolutely convergent integer coefficient series. -/
lemma constructionFullValue_eq_tsum {m : ℕ} (hm : 2 ≤ m) (theta : ℝ) :
    constructionFullValue m theta =
      ∑' k : ℤ, integerChirpCoefficient m theta k := by
  have hn : 0 < (constructionDegree m : ℝ) := by
    exact_mod_cast constructionDegree_pos hm
  have hs := constructionScale_pos hm
  have hK : (constructionMargin m : ℝ) ≤
      (constructionDegree m : ℝ) - constructionMargin m := by
    have hh : 2 * (constructionMargin m : ℝ) ≤ constructionDegree m := by
      exact_mod_cast two_margin_le_degree hm
    linarith
  have hFint (k : ℤ) : Integrable
      (fun y => gaussianChirpAtom (constructionDegree m) (constructionScale m)
        theta y k)
      (volume.restrict (Set.Ioc (constructionMargin m : ℝ)
        ((constructionDegree m : ℝ) - constructionMargin m))) := by
    have hi := (show Continuous (fun y =>
        gaussianChirpAtom (constructionDegree m) (constructionScale m)
          theta y k) by
      unfold gaussianChirpAtom
      fun_prop).intervalIntegrable (μ := volume)
        (constructionMargin m : ℝ)
          ((constructionDegree m : ℝ) - constructionMargin m)
    rw [intervalIntegrable_iff, uIoc_of_le hK] at hi
    exact hi
  have hmass : Summable (fun k : ℤ =>
      ∫ y in Set.Ioc (constructionMargin m : ℝ)
          ((constructionDegree m : ℝ) - constructionMargin m),
        ‖gaussianChirpAtom (constructionDegree m) (constructionScale m)
          theta y k‖) := by
    apply (summable_norm_integerChirpCoefficient hm theta).congr
    intro k
    rw [← intervalIntegral.integral_of_le hK]
    rw [intervalIntegral_norm_gaussianChirpAtom_eq_chi hm theta k]
    exact norm_integerChirpCoefficient hm theta k
  have hswap := MeasureTheory.integral_tsum_of_summable_integral_norm
    (μ := volume.restrict (Set.Ioc (constructionMargin m : ℝ)
      ((constructionDegree m : ℝ) - constructionMargin m))) hFint hmass
  calc
    constructionFullValue m theta =
        ∫ y in Set.Ioc (constructionMargin m : ℝ)
            ((constructionDegree m : ℝ) - constructionMargin m),
          ∑' k : ℤ, gaussianChirpAtom (constructionDegree m)
            (constructionScale m) theta y k := by
      rw [constructionFullValue, fullIntegerSmoothedChirp,
        intervalIntegral.integral_of_le hK]
    _ = ∑' k : ℤ,
        ∫ y in Set.Ioc (constructionMargin m : ℝ)
            ((constructionDegree m : ℝ) - constructionMargin m),
          gaussianChirpAtom (constructionDegree m) (constructionScale m)
            theta y k := hswap.symm
    _ = ∑' k : ℤ, integerChirpCoefficient m theta k := by
      apply tsum_congr
      intro k
      rw [← intervalIntegral.integral_of_le hK,
        intervalIntegral_gaussianChirpAtom _ _ _ _ _ hn hs,
        gaussianCutoff_eq_chi hs (two_margin_le_degree hm)]
      rfl

lemma e_add (x y : ℝ) : e (x + y) = e x * e y := by
  rw [e, e, e, ← Complex.exp_add]
  congr 1
  push_cast
  ring

lemma periodicPoint_pow_eq_e (theta : ℝ) (k : ℕ) :
    periodicPoint theta ^ k = e ((k : ℝ) * theta) := by
  rw [periodicPoint, unitPoint, e, ← Complex.exp_nat_mul]
  congr 1
  push_cast
  ring

lemma baseCoefficient_mul_periodicPoint_pow {m : ℕ} (hm : 2 ≤ m)
    (theta : ℝ) (k : Fin (constructionDegree m + 1)) :
    baseCoefficient m k * periodicPoint theta ^ k.1 =
      integerChirpCoefficient m theta k.1 := by
  rw [baseCoefficient, integerChirpCoefficient, periodicPoint_pow_eq_e,
    mul_assoc, ← e_add]
  congr 2
  simp only [chirpPhase]
  push_cast
  ring

lemma normalizedZerothValue_baseCoefficient {m : ℕ} (hm : 2 ≤ m)
    (theta : ℝ) :
    normalizedZerothValue (baseCoefficient m) theta =
      ∑ k ∈ Finset.range (constructionDegree m + 1),
        integerChirpCoefficient m theta k := by
  rw [normalizedZerothValue, Finset.sum_fin_eq_sum_range]
  apply Finset.sum_congr rfl
  intro k hk
  have hk' : k < constructionDegree m + 1 := Finset.mem_range.mp hk
  rw [dif_pos hk']
  exact baseCoefficient_mul_periodicPoint_pow hm theta ⟨k, hk'⟩

lemma summable_rightIntegerChirp {m : ℕ} (hm : 2 ≤ m) (theta : ℝ) :
    Summable (fun j : ℕ => integerChirpCoefficient m theta
      (constructionDegree m + j + 1 : ℤ)) := by
  apply Summable.of_norm
  apply (summable_outsideRight (constructionScale_pos hm)
    (two_margin_le_degree hm)).congr
  intro j
  exact (norm_integerChirpCoefficient_degree_add_one hm theta j).symm

lemma summable_leftIntegerChirp {m : ℕ} (hm : 2 ≤ m) (theta : ℝ) :
    Summable (fun j : ℕ => integerChirpCoefficient m theta (-(j + 1 : ℤ))) := by
  apply Summable.of_norm
  apply (summable_outsideLeft (constructionScale_pos hm)
    (two_margin_le_degree hm)).congr
  intro j
  exact (norm_integerChirpCoefficient_neg_add_one hm theta j).symm

lemma summable_positiveIntegerChirp {m : ℕ} (hm : 2 ≤ m) (theta : ℝ) :
    Summable (fun j : ℕ => integerChirpCoefficient m theta (j + 1)) := by
  apply (summable_nat_add_iff (constructionDegree m)).mp
  have hright := summable_rightIntegerChirp hm theta
  have heq : (fun j : ℕ => integerChirpCoefficient m theta
      (((j + constructionDegree m : ℕ) : ℤ) + 1)) =
      (fun j : ℕ => integerChirpCoefficient m theta
        (constructionDegree m + j + 1 : ℤ)) := by
    funext j
    congr 1
    push_cast
    ring
  rw [heq]
  exact hright

/-- Truncating the full integer chirp to the coefficients `0, ..., m^18`
costs less than one, uniformly in the angular variable. -/
lemma norm_base_sub_full_lt_one {m : ℕ} (hm : 2 ≤ m) (theta : ℝ) :
    ‖normalizedZerothValue (baseCoefficient m) theta -
        constructionFullValue m theta‖ < 1 := by
  let f : ℤ → ℂ := integerChirpCoefficient m theta
  let right : ℕ → ℂ := fun j => f (constructionDegree m + j + 1)
  let left : ℕ → ℂ := fun j => f (-(j + 1 : ℤ))
  have hpos : Summable (fun j : ℕ => f (j + 1)) :=
    summable_positiveIntegerChirp hm theta
  have hright : Summable right := summable_rightIntegerChirp hm theta
  have hleft : Summable left := summable_leftIntegerChirp hm theta
  have hsplit := hpos.sum_add_tsum_nat_add (constructionDegree m)
  have hfull := tsum_of_add_one_of_neg_add_one hpos hleft
  have hsplit' :
      (∑ i ∈ Finset.range (constructionDegree m), f (i + 1)) +
          (∑' j : ℕ, right j) = ∑' j : ℕ, f (j + 1) := by
    simpa [right, add_assoc, add_comm, add_left_comm] using hsplit
  have hfull' :
      (∑' k : ℤ, f k) = (∑' j : ℕ, f (j + 1)) + f 0 +
          ∑' j : ℕ, left j := by
    simpa [left, add_assoc, add_comm, add_left_comm] using hfull
  have hdecomp : normalizedZerothValue (baseCoefficient m) theta +
      (∑' j : ℕ, right j) + (∑' j : ℕ, left j) =
        constructionFullValue m theta := by
    rw [constructionFullValue_eq_tsum hm theta,
      normalizedZerothValue_baseCoefficient hm theta,
      Finset.sum_range_succ', hfull']
    rw [← hsplit']
    simp only [f, right, left]
    push_cast
    ring
  have hrightNormSumm : Summable (fun j : ℕ => ‖right j‖) := by
    apply (summable_outsideRight (constructionScale_pos hm)
      (two_margin_le_degree hm)).congr
    intro j
    exact (norm_integerChirpCoefficient_degree_add_one hm theta j).symm
  have hleftNormSumm : Summable (fun j : ℕ => ‖left j‖) := by
    apply (summable_outsideLeft (constructionScale_pos hm)
      (two_margin_le_degree hm)).congr
    intro j
    exact (norm_integerChirpCoefficient_neg_add_one hm theta j).symm
  have hrightNorm : ‖∑' j : ℕ, right j‖ ≤
      ∑' j : ℕ, outsideRight (constructionScale m) (constructionMargin m)
        (constructionDegree m) j := by
    calc
      ‖∑' j : ℕ, right j‖ ≤ ∑' j : ℕ, ‖right j‖ :=
        norm_tsum_le_tsum_norm hrightNormSumm
      _ = _ := by
        apply tsum_congr
        intro j
        exact norm_integerChirpCoefficient_degree_add_one hm theta j
  have hleftNorm : ‖∑' j : ℕ, left j‖ ≤
      ∑' j : ℕ, outsideLeft (constructionScale m) (constructionMargin m)
        (constructionDegree m) j := by
    calc
      ‖∑' j : ℕ, left j‖ ≤ ∑' j : ℕ, ‖left j‖ :=
        norm_tsum_le_tsum_norm hleftNormSumm
      _ = _ := by
        apply tsum_congr
        intro j
        exact norm_integerChirpCoefficient_neg_add_one hm theta j
  calc
    ‖normalizedZerothValue (baseCoefficient m) theta -
        constructionFullValue m theta‖ =
        ‖-(∑' j : ℕ, right j) - (∑' j : ℕ, left j)‖ := by
      congr 1
      rw [← hdecomp]
      ring
    _ = ‖(∑' j : ℕ, right j) + (∑' j : ℕ, left j)‖ := by
      rw [show -(∑' j : ℕ, right j) - (∑' j : ℕ, left j) =
          -((∑' j : ℕ, right j) + (∑' j : ℕ, left j)) by ring, norm_neg]
    _ ≤ ‖∑' j : ℕ, right j‖ + ‖∑' j : ℕ, left j‖ := norm_add_le _ _
    _ ≤ (∑' j : ℕ, outsideLeft (constructionScale m) (constructionMargin m)
          (constructionDegree m) j) +
        ∑' j : ℕ, outsideRight (constructionScale m) (constructionMargin m)
          (constructionDegree m) j := by linarith
    _ < 1 := by
      simpa [constructionScale, constructionMargin, constructionDegree,
        Nat.cast_pow] using tsum_outside_pow_lt_one hm

/-- The Poisson estimate at the chosen powers.  The exact main term is even
closer to `m^9`; the additive one is a convenient formal upper bound. -/
lemma norm_constructionFullValue_le {m : ℕ} (hm : 2 ≤ m) (theta : ℝ) :
    ‖constructionFullValue m theta‖ ≤ (m : ℝ) ^ 9 + 1 := by
  have hn : 0 < (constructionDegree m : ℝ) := by
    exact_mod_cast constructionDegree_pos hm
  have hs := constructionScale_pos hm
  have hK0 : 0 ≤ (constructionMargin m : ℝ) := by positivity
  have hK : (constructionMargin m : ℝ) ≤
      (constructionDegree m : ℝ) - constructionMargin m := by
    have hh : 2 * (constructionMargin m : ℝ) ≤ constructionDegree m := by
      exact_mod_cast two_margin_le_degree hm
    linarith
  have hmain := norm_fullIntegerSmoothedChirp_le_exact
    (constructionDegree m : ℝ) (constructionScale m)
      (constructionMargin m : ℝ) theta hn hs hK0 hK
  rw [constructionFullValue]
  calc
    ‖fullIntegerSmoothedChirp (constructionDegree m) (constructionScale m)
        (constructionMargin m) theta‖ ≤
        Real.sqrt (constructionDegree m : ℝ) *
          (1 + (constructionScale m ^ 2 /
            (constructionDegree m : ℝ))⁻¹ ^ 2) ^ (1 / 4 : ℝ) := hmain
    _ = (m : ℝ) ^ 9 *
          (1 + (constructionRatio m)⁻¹ ^ 2) ^ (1 / 4 : ℝ) := by
      rw [constructionRatio_eq hm, constructionDegree, sqrt_nat_pow_eighteen]
    _ ≤ (m : ℝ) ^ 9 * (1 + (constructionRatio m)⁻¹ ^ 2) := by
      gcongr
      apply Real.rpow_le_self_of_one_le
      · exact le_add_of_nonneg_right (sq_nonneg _)
      · norm_num
    _ = (m : ℝ) ^ 9 + 1 / (m : ℝ) ^ 3 := by
      have hm0 : (m : ℝ) ≠ 0 := by positivity
      simp only [constructionRatio]
      field_simp
    _ ≤ (m : ℝ) ^ 9 + 1 := by
      gcongr
      exact (div_le_one (by positivity)).2
        (one_le_pow₀ (by exact_mod_cast (show 1 ≤ m by omega)))

lemma norm_baseCoefficient_value_lt {m : ℕ} (hm : 2 ≤ m) (theta : ℝ) :
    ‖normalizedZerothValue (baseCoefficient m) theta‖ <
      (m : ℝ) ^ 9 + 2 := by
  calc
    ‖normalizedZerothValue (baseCoefficient m) theta‖ ≤
        ‖normalizedZerothValue (baseCoefficient m) theta -
          constructionFullValue m theta‖ + ‖constructionFullValue m theta‖ := by
      simpa [sub_add_cancel] using norm_add_le
        (normalizedZerothValue (baseCoefficient m) theta - constructionFullValue m theta)
        (constructionFullValue m theta)
    _ < 1 + ((m : ℝ) ^ 9 + 1) :=
      add_lt_add_of_lt_of_le (norm_base_sub_full_lt_one hm theta)
        (norm_constructionFullValue_le hm theta)
    _ = (m : ℝ) ^ 9 + 2 := by ring

lemma construction_interpolation_loss_lt_one {m : ℕ} (hm : 2 ≤ m) :
    4 * Real.pi * (constructionDegree m + 1) * constructionDegree m /
        constructionGrid m < 1 := by
  let N : ℝ := constructionDegree m
  have hNpos : 0 < N := by
    dsimp [N]
    exact_mod_cast constructionDegree_pos hm
  have hpow : 2 ^ 18 ≤ m ^ 18 := Nat.pow_le_pow_left hm 18
  have hN32 : (32 : ℝ) < N := by
    dsimp [N, constructionDegree]
    exact_mod_cast (show 32 < m ^ 18 by omega)
  have hG : (constructionGrid m : ℝ) = N ^ 3 := by
    rw [constructionGrid_cast]
    dsimp [N, constructionDegree]
    push_cast
    ring
  change 4 * Real.pi * (N + 1) * N / (constructionGrid m : ℝ) < 1
  rw [div_lt_iff₀ (by exact_mod_cast constructionGrid_pos hm)]
  simp only [one_mul]
  calc
    4 * Real.pi * (N + 1) * N < 16 * (N + 1) * N := by
      gcongr
      nlinarith [Real.pi_lt_four]
    _ ≤ 32 * N * N := by
      have : N + 1 ≤ 2 * N := by nlinarith
      calc
        16 * (N + 1) * N ≤ 16 * (2 * N) * N := by gcongr
        _ = 32 * N * N := by ring
    _ < N * N * N := by
      have hmid : 32 * N < N * N := mul_lt_mul_of_pos_right hN32 hNpos
      exact mul_lt_mul_of_pos_right hmid hNpos
    _ = (constructionGrid m : ℝ) := by rw [hG]; ring

/-- A degree-54 polynomial is eventually dominated by the exponential in
the finite-grid union bound. -/
lemma eventually_rounding_exponential_small :
    ∀ᶠ m : ℕ in Filter.atTop,
      4 * (m : ℝ) ^ 54 * Real.exp (-(m : ℝ) / 64) < 1 := by
  have ht : Filter.Tendsto (fun x : ℝ =>
      4 * (x ^ (54 : ℝ) * Real.exp (-(1 / 64 : ℝ) * x)))
      Filter.atTop (nhds 0) := by
    simpa using
      (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero 54 (1 / 64)
        (by norm_num)).const_mul 4
  have hnat := ht.comp tendsto_natCast_atTop_atTop
  have hev := hnat.eventually (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1))
  filter_upwards [hev, Filter.eventually_ge_atTop 1] with m hm hm1
  simpa [Real.rpow_natCast, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm]
    using hm

/-- The concrete union-bound hypothesis, reduced to the preceding elementary
exponential estimate. -/
lemma rounding_probability_small {m : ℕ} (hm : 2 ≤ m)
    (hdef : defect (baseCoefficient m) ≠ 0)
    (hexp : 4 * (m : ℝ) ^ 54 * Real.exp (-(m : ℝ) / 64) < 1) :
    constructionGrid m *
        (4 * Real.exp (-((m : ℝ) ^ 8) ^ 2 /
          (8 * defect (baseCoefficient m)))) < 1 := by
  have hDpos : 0 < defect (baseCoefficient m) :=
    lt_of_le_of_ne (defect_baseCoefficient_nonneg hm) (Ne.symm hdef)
  have hm0 : 0 ≤ (m : ℝ) := by positivity
  have hratio : (m : ℝ) / 64 ≤
      ((m : ℝ) ^ 8) ^ 2 / (8 * defect (baseCoefficient m)) := by
    rw [le_div_iff₀ (mul_pos (by norm_num) hDpos)]
    calc
      (m : ℝ) / 64 * (8 * defect (baseCoefficient m)) =
          (m : ℝ) * defect (baseCoefficient m) / 8 := by ring
      _ ≤ (m : ℝ) * (8 * (m : ℝ) ^ 15) / 8 := by
        gcongr
        exact defect_baseCoefficient_le hm
      _ = ((m : ℝ) ^ 8) ^ 2 := by ring
  have hexp_le :
      Real.exp (-((m : ℝ) ^ 8) ^ 2 /
          (8 * defect (baseCoefficient m))) ≤
        Real.exp (-(m : ℝ) / 64) := by
    apply Real.exp_le_exp.mpr
    calc
      -((m : ℝ) ^ 8) ^ 2 / (8 * defect (baseCoefficient m)) =
          -(((m : ℝ) ^ 8) ^ 2 / (8 * defect (baseCoefficient m))) := by ring
      _ ≤ -(m : ℝ) / 64 := by simpa only [neg_div] using neg_le_neg hratio
  calc
    constructionGrid m *
        (4 * Real.exp (-((m : ℝ) ^ 8) ^ 2 /
          (8 * defect (baseCoefficient m)))) ≤
        constructionGrid m * (4 * Real.exp (-(m : ℝ) / 64)) := by
      gcongr
    _ = 4 * (m : ℝ) ^ 54 * Real.exp (-(m : ℝ) / 64) := by
      rw [constructionGrid_cast]
      ring
    _ < 1 := hexp

/-- The Gaussian chirp and its finite chord correction provide arbitrarily
large examples with the concrete power bound used by `Asymptotics.lean`. -/
theorem hasPowerUpperExamples : HasPowerUpperExamples := by
  intro M
  have hev : ∀ᶠ m : ℕ in Filter.atTop,
      max 2 M ≤ m ∧
        4 * (m : ℝ) ^ 54 * Real.exp (-(m : ℝ) / 64) < 1 := by
    filter_upwards [Filter.eventually_ge_atTop (max 2 M),
      eventually_rounding_exponential_small] with m hm hsmall
    exact ⟨hm, hsmall⟩
  obtain ⟨m, hmM, hexp⟩ := hev.exists
  have hm : 2 ≤ m := (le_max_left 2 M).trans hmM
  have ha : ∀ i, ‖baseCoefficient m i‖ ≤ 1 :=
    norm_baseCoefficient_le_one hm
  have hm8 : (3 : ℝ) ≤ (m : ℝ) ^ 8 := by
    have hpow : 2 ^ 8 ≤ m ^ 8 := Nat.pow_le_pow_left hm 8
    exact_mod_cast (show 3 ≤ m ^ 8 by omega)
  refine ⟨m, hmM, ?_⟩
  change ∃ a : Fin (constructionDegree m + 1) → ℂ,
    IsUnimodular a ∧ ∀ theta : ℝ,
      ‖zerothValue a theta‖ ≤ (m : ℝ) ^ 9 + 2 * (m : ℝ) ^ 8
  by_cases hdef : defect (baseCoefficient m) = 0
  · obtain ⟨b, hb, hcorr⟩ :=
      exists_unit_rounding_circle_of_defect_eq_zero
        (baseCoefficient m) ha hdef
    refine ⟨b, hb, ?_⟩
    intro theta
    rw [← normalizedZerothValue_div_two_pi b theta]
    have hzero := hcorr (theta / (2 * Real.pi))
    have heq : normalizedZerothValue b (theta / (2 * Real.pi)) =
        normalizedZerothValue (baseCoefficient m) (theta / (2 * Real.pi)) := by
      exact sub_eq_zero.mp (norm_eq_zero.mp hzero)
    rw [heq]
    have hbase := norm_baseCoefficient_value_lt hm (theta / (2 * Real.pi))
    linarith
  · obtain ⟨b, hb, hcorr⟩ := exists_unit_rounding_circle_defect
      (baseCoefficient m) ha (constructionGrid_pos hm)
      (R := (m : ℝ) ^ 8) (by positivity)
      (rounding_probability_small hm hdef hexp)
    refine ⟨b, hb, ?_⟩
    intro theta
    rw [← normalizedZerothValue_div_two_pi b theta]
    let phi : ℝ := theta / (2 * Real.pi)
    have hinterp := construction_interpolation_loss_lt_one hm
    have hcorrection :
        ‖normalizedZerothValue b phi -
          normalizedZerothValue (baseCoefficient m) phi‖ <
            1 + (m : ℝ) ^ 8 := by
      calc
        ‖normalizedZerothValue b phi -
            normalizedZerothValue (baseCoefficient m) phi‖ <
            4 * Real.pi * (constructionDegree m + 1) * constructionDegree m /
              constructionGrid m + (m : ℝ) ^ 8 := hcorr phi
        _ < 1 + (m : ℝ) ^ 8 := add_lt_add_left hinterp _
    have hbase := norm_baseCoefficient_value_lt hm phi
    change ‖normalizedZerothValue b phi‖ ≤ _
    apply le_of_lt
    calc
      ‖normalizedZerothValue b phi‖ ≤
          ‖normalizedZerothValue b phi -
            normalizedZerothValue (baseCoefficient m) phi‖ +
              ‖normalizedZerothValue (baseCoefficient m) phi‖ := by
        simpa [sub_add_cancel] using norm_add_le
          (normalizedZerothValue b phi -
            normalizedZerothValue (baseCoefficient m) phi)
          (normalizedZerothValue (baseCoefficient m) phi)
      _ < (1 + (m : ℝ) ^ 8) + ((m : ℝ) ^ 9 + 2) :=
        add_lt_add hcorrection hbase
      _ ≤ (m : ℝ) ^ 9 + 2 * (m : ℝ) ^ 8 := by linarith

end

end Erdos230
