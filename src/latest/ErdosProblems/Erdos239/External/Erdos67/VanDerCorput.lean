import Mathlib

/-!
# Finite van der Corput differencing

This file contains a finite, quantitative form of the first differencing step
in van der Corput's method.  The abstract version applies to any family of
representatives of the same finite sum.  The additive-group version rewrites
the result in terms of the usual correlations

`sum x, a x * conj (a (x + r))`.

Taking the finite additive group to be a sufficiently large cyclic group and
extending an interval-supported sequence by zero gives the standard interval
form without boundary terms wrapping around.
-/

open scoped BigOperators
open Finset

namespace Erdos67

/-- Finite Cauchy--Schwarz for a sum of complex numbers. -/
theorem norm_sum_sq_le_card_mul_sum_norm_sq
    {ι : Type*} (s : Finset ι) (f : ι → ℂ) :
    ‖∑ i ∈ s, f i‖ ^ 2 ≤
      (s.card : ℝ) * ∑ i ∈ s, ‖f i‖ ^ 2 := by
  calc
    ‖∑ i ∈ s, f i‖ ^ 2 ≤ (∑ i ∈ s, ‖f i‖) ^ 2 := by
      gcongr
      exact norm_sum_le _ _
    _ ≤ (s.card : ℝ) * ∑ i ∈ s, ‖f i‖ ^ 2 :=
      sq_sum_le_card_mul_sum_sq

/-- Correlation of two members of a finite family of complex sequences. -/
noncomputable def finiteFamilyCorrelation
    {ι κ : Type*} (s : Finset ι) (u : κ → ι → ℂ) (h k : κ) : ℂ :=
  ∑ i ∈ s, u h i * (starRingEnd ℂ) (u k i)

/-- Exact expansion of the sum of squared norms of the pointwise family sum. -/
theorem sum_norm_familySum_sq_coe
    {ι κ : Type*} (s : Finset ι) (t : Finset κ) (u : κ → ι → ℂ) :
    ((∑ i ∈ s, ‖∑ h ∈ t, u h i‖ ^ 2 : ℝ) : ℂ) =
      ∑ h ∈ t, ∑ k ∈ t, finiteFamilyCorrelation s u h k := by
  unfold finiteFamilyCorrelation
  calc
    ((∑ i ∈ s, ‖∑ h ∈ t, u h i‖ ^ 2 : ℝ) : ℂ) =
        ∑ i ∈ s, (∑ h ∈ t, u h i) *
          (starRingEnd ℂ) (∑ k ∈ t, u k i) := by
      push_cast
      apply Finset.sum_congr rfl
      intro i hi
      simpa only [Complex.ofReal_pow] using
        (Complex.mul_conj' (∑ h ∈ t, u h i)).symm
    _ = ∑ h ∈ t, ∑ k ∈ t,
        ∑ i ∈ s, u h i * (starRingEnd ℂ) (u k i) := by
      conv_rhs => rw [Finset.sum_comm]
      simp only [map_sum, Finset.sum_mul, Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro h hh
      rw [Finset.sum_comm]

/-- Abstract finite van der Corput inequality.

For each `h ∈ t`, the sequence `u h` is required to have the same total `S`
on `s`.  Averaging those representatives, applying Cauchy--Schwarz in the
outer variable, and expanding the square bounds `S` by pair correlations. -/
theorem finite_vanDerCorput
    {ι κ : Type*} (s : Finset ι) (t : Finset κ)
    (u : κ → ι → ℂ) (S : ℂ)
    (hsum : ∀ h ∈ t, ∑ i ∈ s, u h i = S) :
    (t.card : ℝ) ^ 2 * ‖S‖ ^ 2 ≤
      (s.card : ℝ) *
        ∑ h ∈ t, ∑ k ∈ t, ‖finiteFamilyCorrelation s u h k‖ := by
  have havg : ∑ i ∈ s, ∑ h ∈ t, u h i = (t.card : ℂ) * S := by
    rw [Finset.sum_comm]
    calc
      (∑ h ∈ t, ∑ i ∈ s, u h i) = ∑ h ∈ t, S := by
        apply Finset.sum_congr rfl
        intro h hh
        exact hsum h hh
      _ = (t.card : ℂ) * S := by simp
  have hcs := norm_sum_sq_le_card_mul_sum_norm_sq
    s (fun i ↦ ∑ h ∈ t, u h i)
  have henergy :
      (∑ i ∈ s, ‖∑ h ∈ t, u h i‖ ^ 2 : ℝ) ≤
        ∑ h ∈ t, ∑ k ∈ t, ‖finiteFamilyCorrelation s u h k‖ := by
    let E : ℝ := ∑ i ∈ s, ‖∑ h ∈ t, u h i‖ ^ 2
    have hEnonneg : 0 ≤ E := by
      dsimp [E]
      positivity
    have hexpand := sum_norm_familySum_sq_coe s t u
    calc
      (∑ i ∈ s, ‖∑ h ∈ t, u h i‖ ^ 2 : ℝ) = ‖(E : ℂ)‖ := by
        rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hEnonneg]
      _ = ‖∑ h ∈ t, ∑ k ∈ t, finiteFamilyCorrelation s u h k‖ := by
        rw [hexpand]
      _ ≤ ∑ h ∈ t, ‖∑ k ∈ t, finiteFamilyCorrelation s u h k‖ :=
        norm_sum_le _ _
      _ ≤ ∑ h ∈ t, ∑ k ∈ t, ‖finiteFamilyCorrelation s u h k‖ := by
        exact Finset.sum_le_sum fun h hh ↦ norm_sum_le _ _
  calc
    (t.card : ℝ) ^ 2 * ‖S‖ ^ 2 = ‖(t.card : ℂ) * S‖ ^ 2 := by
      simp [pow_two]
      ring
    _ = ‖∑ i ∈ s, ∑ h ∈ t, u h i‖ ^ 2 := by rw [havg]
    _ ≤ (s.card : ℝ) * ∑ i ∈ s, ‖∑ h ∈ t, u h i‖ ^ 2 := hcs
    _ ≤ (s.card : ℝ) *
        ∑ h ∈ t, ∑ k ∈ t, ‖finiteFamilyCorrelation s u h k‖ := by
      gcongr

/-- The usual finite additive correlation at difference `r`. -/
noncomputable def additiveCorrelation
    {G : Type*} [Fintype G] [AddCommGroup G] (a : G → ℂ) (r : G) : ℂ :=
  ∑ x : G, a x * (starRingEnd ℂ) (a (x + r))

theorem finiteFamilyCorrelation_add_eq_additiveCorrelation
    {G : Type*} [Fintype G] [AddCommGroup G]
    (a : G → ℂ) (h k : G) :
    finiteFamilyCorrelation Finset.univ (fun h x ↦ a (x + h)) h k =
      additiveCorrelation a (k - h) := by
  unfold finiteFamilyCorrelation additiveCorrelation
  simpa [add_assoc] using
    Equiv.sum_comp (Equiv.addRight h)
      (fun y : G ↦ a y * (starRingEnd ℂ) (a (y + (k - h))))

theorem additiveCorrelation_zero
    {G : Type*} [Fintype G] [AddCommGroup G] (a : G → ℂ) :
    additiveCorrelation a 0 = ((∑ x : G, ‖a x‖ ^ 2 : ℝ) : ℂ) := by
  simp [additiveCorrelation, Complex.mul_conj']

theorem norm_additiveCorrelation_zero
    {G : Type*} [Fintype G] [AddCommGroup G] (a : G → ℂ) :
    ‖additiveCorrelation a 0‖ = ∑ x : G, ‖a x‖ ^ 2 := by
  rw [additiveCorrelation_zero, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg]
  positivity

/-- Finite-group van der Corput inequality in difference form. -/
theorem finite_vanDerCorput_addCommGroup
    {G : Type*} [Fintype G] [AddCommGroup G]
    (a : G → ℂ) (t : Finset G) :
    (t.card : ℝ) ^ 2 * ‖∑ x : G, a x‖ ^ 2 ≤
      (Fintype.card G : ℝ) *
        ∑ h ∈ t, ∑ k ∈ t, ‖additiveCorrelation a (k - h)‖ := by
  have h := finite_vanDerCorput Finset.univ t
    (fun h x ↦ a (x + h)) (∑ x : G, a x) (by
      intro h hh
      change (∑ x : G, a (x + h)) = ∑ x : G, a x
      exact Equiv.sum_comp (Equiv.addRight h) a)
  simpa [finiteFamilyCorrelation_add_eq_additiveCorrelation] using h

/-- Exact separation of the diagonal and off-diagonal terms in the finite
group van der Corput bound. -/
theorem sum_norm_additiveCorrelation_eq_diagonal_add
    {G : Type*} [Fintype G] [AddCommGroup G] [DecidableEq G]
    (a : G → ℂ) (t : Finset G) :
    (∑ h ∈ t, ∑ k ∈ t, ‖additiveCorrelation a (k - h)‖) =
      (t.card : ℝ) * (∑ x : G, ‖a x‖ ^ 2) +
        ∑ h ∈ t, ∑ k ∈ t.erase h, ‖additiveCorrelation a (k - h)‖ := by
  have hsplit : ∀ h ∈ t,
      (∑ k ∈ t, ‖additiveCorrelation a (k - h)‖) =
        (∑ x : G, ‖a x‖ ^ 2) +
          ∑ k ∈ t.erase h, ‖additiveCorrelation a (k - h)‖ := by
    intro h hh
    rw [← Finset.add_sum_erase t
      (fun k ↦ ‖additiveCorrelation a (k - h)‖) hh]
    rw [sub_self, norm_additiveCorrelation_zero]
  calc
    (∑ h ∈ t, ∑ k ∈ t, ‖additiveCorrelation a (k - h)‖) =
        ∑ h ∈ t, ((∑ x : G, ‖a x‖ ^ 2) +
          ∑ k ∈ t.erase h, ‖additiveCorrelation a (k - h)‖) := by
      apply Finset.sum_congr rfl
      intro h hh
      exact hsplit h hh
    _ = (t.card : ℝ) * (∑ x : G, ‖a x‖ ^ 2) +
        ∑ h ∈ t, ∑ k ∈ t.erase h,
          ‖additiveCorrelation a (k - h)‖ := by
      rw [Finset.sum_add_distrib]
      congr 1
      simp [nsmul_eq_mul]

/-- Classical finite-group van der Corput inequality with its diagonal term
displayed explicitly. -/
theorem finite_vanDerCorput_addCommGroup_offDiagonal
    {G : Type*} [Fintype G] [AddCommGroup G] [DecidableEq G]
    (a : G → ℂ) (t : Finset G) :
    (t.card : ℝ) ^ 2 * ‖∑ x : G, a x‖ ^ 2 ≤
      (Fintype.card G : ℝ) *
        ((t.card : ℝ) * (∑ x : G, ‖a x‖ ^ 2) +
          ∑ h ∈ t, ∑ k ∈ t.erase h,
            ‖additiveCorrelation a (k - h)‖) := by
  rw [← sum_norm_additiveCorrelation_eq_diagonal_add]
  exact finite_vanDerCorput_addCommGroup a t

end Erdos67
