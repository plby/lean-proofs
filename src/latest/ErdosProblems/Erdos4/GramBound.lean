import Mathlib.Analysis.Complex.Basic
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Tactic

/-!
# A finite Gram-matrix bound

This elementary estimate turns small off-diagonal correlations into a
mean-square bound. No distribution result for primes is imported here.
-/

open scoped BigOperators

namespace Erdos4.GramBound

variable {I : Type*} [Fintype I]

theorem sum_sq_le_card_mul_sum_sq (a : I → ℝ) :
    (∑ i, a i) ^ 2 ≤ (Fintype.card I : ℝ) * ∑ i, a i ^ 2 := by
  simpa only [one_mul, one_pow, Finset.sum_const, Finset.card_univ,
    nsmul_eq_mul, mul_one] using
    Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun _ : I => (1 : ℝ)) a

/-- A bound with a diagonal part `B` and an entrywise error `epsilon`. -/
theorem quadratic_form_le [DecidableEq I] (g : I → I → ℂ) (B epsilon : ℝ)
    (hepsilon : 0 ≤ epsilon)
    (hg : ∀ i j, ‖g i j‖ ≤ (if i = j then B else 0) + epsilon)
    (a : I → ℂ) :
    (∑ i, ∑ j, star (a i) * a j * g i j).re ≤
      (B + (Fintype.card I : ℝ) * epsilon) * ∑ i, ‖a i‖ ^ 2 := by
  classical
  have hterm : ∀ i j,
      (star (a i) * a j * g i j).re ≤
        ‖a i‖ * ‖a j‖ * ((if i = j then B else 0) + epsilon) := by
    intro i j
    calc
      (star (a i) * a j * g i j).re ≤ ‖star (a i) * a j * g i j‖ :=
        Complex.re_le_norm _
      _ = ‖a i‖ * ‖a j‖ * ‖g i j‖ := by simp only [norm_mul, norm_star]
      _ ≤ ‖a i‖ * ‖a j‖ * ((if i = j then B else 0) + epsilon) :=
        mul_le_mul_of_nonneg_left (hg i j) (mul_nonneg (norm_nonneg _) (norm_nonneg _))
  have hdiag : (∑ i, ∑ j, ‖a i‖ * ‖a j‖ * (if i = j then B else 0)) =
      B * ∑ i, ‖a i‖ ^ 2 := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _hi
    simp only [mul_ite, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte]
    ring
  have herr : (∑ i, ∑ j, ‖a i‖ * ‖a j‖ * epsilon) = epsilon * (∑ i, ‖a i‖) ^ 2 := by
    rw [pow_two, Finset.sum_mul, Finset.mul_sum]
    simp_rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _hi
    apply Finset.sum_congr rfl
    intro j _hj
    ring
  have htotal : (∑ i, ∑ j, ‖a i‖ * ‖a j‖ * ((if i = j then B else 0) + epsilon)) =
      B * (∑ i, ‖a i‖ ^ 2) + epsilon * (∑ i, ‖a i‖) ^ 2 := by
    simp_rw [mul_add, Finset.sum_add_distrib]
    rw [hdiag, herr]
  have hcs := mul_le_mul_of_nonneg_left (sum_sq_le_card_mul_sum_sq (fun i => ‖a i‖)) hepsilon
  calc
    (∑ i, ∑ j, star (a i) * a j * g i j).re =
        ∑ i, ∑ j, (star (a i) * a j * g i j).re := by simp
    _ ≤ ∑ i, ∑ j, ‖a i‖ * ‖a j‖ * ((if i = j then B else 0) + epsilon) :=
      Finset.sum_le_sum (fun i _hi => Finset.sum_le_sum (fun j _hj => hterm i j))
    _ = B * (∑ i, ‖a i‖ ^ 2) + epsilon * (∑ i, ‖a i‖) ^ 2 := htotal
    _ ≤ (B + (Fintype.card I : ℝ) * epsilon) * ∑ i, ‖a i‖ ^ 2 := by nlinarith

variable {P : Type*} [Fintype P]

noncomputable def weightedGram (w : P → ℝ) (f : I → P → ℂ) (i j : I) : ℂ :=
  ∑ p, (w p : ℂ) * star (f i p) * f j p

theorem weighted_mean_square_eq (w : P → ℝ) (f : I → P → ℂ) (a : I → ℂ) :
    (∑ p, w p * ‖∑ i, a i * f i p‖ ^ 2) =
      (∑ i, ∑ j, star (a i) * a j * weightedGram w f i j).re := by
  have hpoint : ∀ p, ((w p * ‖∑ i, a i * f i p‖ ^ 2 : ℝ) : ℂ) =
      ∑ i, ∑ j, star (a i) * a j * ((w p : ℂ) * star (f i p) * f j p) := by
    intro p
    push_cast
    rw [← Complex.conj_mul']
    simp_rw [map_sum, map_mul, starRingEnd_apply, Finset.sum_mul, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _hi
    apply Finset.sum_congr rfl
    intro j _hj
    ring
  have heq : ((∑ p, w p * ‖∑ i, a i * f i p‖ ^ 2 : ℝ) : ℂ) =
      ∑ i, ∑ j, star (a i) * a j * weightedGram w f i j := by
    rw [Complex.ofReal_sum]
    simp_rw [hpoint]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _hi
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j _hj
    rw [weightedGram, Finset.mul_sum]
  simpa only [Complex.ofReal_re] using congrArg Complex.re heq

/-- The weighted transform bound used after expanding a Selberg majorant. -/
theorem weighted_mean_square_le [DecidableEq I]
    (w : P → ℝ) (f : I → P → ℂ) (B epsilon : ℝ) (hepsilon : 0 ≤ epsilon)
    (hdiag : ∀ i, ‖weightedGram w f i i‖ ≤ B)
    (hoff : ∀ i j, i ≠ j → ‖weightedGram w f i j‖ ≤ epsilon)
    (a : I → ℂ) :
    (∑ p, w p * ‖∑ i, a i * f i p‖ ^ 2) ≤
      (B + (Fintype.card I : ℝ) * epsilon) * ∑ i, ‖a i‖ ^ 2 := by
  rw [weighted_mean_square_eq]
  apply quadratic_form_le _ B epsilon hepsilon _ a
  intro i j
  by_cases hij : i = j
  · subst j
    simp only [↓reduceIte]
    exact (hdiag i).trans (le_add_of_nonneg_right hepsilon)
  · simp only [if_neg hij, zero_add]
    exact hoff i j hij

/-- Finite Hilbert-space duality, proved directly using a test vector and
real Cauchy--Schwarz. It transfers the prime-supported bound to its dual. -/
theorem transform_duality (f : I → P → ℂ) (L : ℝ) (hL : 0 ≤ L)
    (hbound : ∀ b : I → ℂ,
      (∑ p, ‖∑ i, b i * f i p‖ ^ 2) ≤ L * ∑ i, ‖b i‖ ^ 2)
    (a : P → ℂ) :
    (∑ i, ‖∑ p, a p * star (f i p)‖ ^ 2) ≤ L * ∑ p, ‖a p‖ ^ 2 := by
  let S : I → ℂ := fun i => ∑ p, a p * star (f i p)
  let T : P → ℂ := fun p => ∑ i, S i * f i p
  let X : ℝ := ∑ i, ‖S i‖ ^ 2
  have hX : 0 ≤ X := Finset.sum_nonneg (fun i _hi => sq_nonneg _)
  have hS : ∀ i, star (S i) = ∑ p, star (a p) * f i p := by
    intro i
    simp only [S, star_sum, star_mul, star_star]
    apply Finset.sum_congr rfl
    intro p _hp
    ring
  have hinner : (∑ p, star (a p) * T p) = (X : ℂ) := by
    simp only [T, Finset.mul_sum]
    rw [Finset.sum_comm]
    have hterm : ∀ i, (∑ p, star (a p) * (S i * f i p)) = S i * star (S i) := by
      intro i
      rw [hS, Finset.mul_sum]
      exact Finset.sum_congr rfl (fun p _hp => by ring)
    simp_rw [hterm]
    change (∑ i, S i * star (S i)) = ((∑ i, ‖S i‖ ^ 2 : ℝ) : ℂ)
    rw [Complex.ofReal_sum]
    apply Finset.sum_congr rfl
    intro i _hi
    simpa only [Complex.ofReal_pow, starRingEnd_apply] using Complex.mul_conj' (S i)
  have hfirst : X ≤ ∑ p, ‖a p‖ * ‖T p‖ := by
    calc
      X = ‖∑ p, star (a p) * T p‖ := by
        rw [hinner, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hX]
      _ ≤ ∑ p, ‖star (a p) * T p‖ := norm_sum_le _ _
      _ = ∑ p, ‖a p‖ * ‖T p‖ := by simp only [norm_mul, norm_star]
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
    (fun p => ‖a p‖) (fun p => ‖T p‖)
  have hT : (∑ p, ‖T p‖ ^ 2) ≤ L * X := hbound S
  have hA : 0 ≤ ∑ p, ‖a p‖ ^ 2 := Finset.sum_nonneg (fun p _hp => sq_nonneg _)
  have hprod := mul_le_mul_of_nonneg_left hT hA
  have hsum0 : 0 ≤ ∑ p, ‖a p‖ * ‖T p‖ :=
    Finset.sum_nonneg (fun p _hp => mul_nonneg (norm_nonneg _) (norm_nonneg _))
  have hsq : X ^ 2 ≤ (L * ∑ p, ‖a p‖ ^ 2) * X := by
    nlinarith
  change X ≤ L * ∑ p, ‖a p‖ ^ 2
  by_cases hzero : X = 0
  · rw [hzero]
    exact mul_nonneg hL hA
  · have hpos : 0 < X := lt_of_le_of_ne hX (Ne.symm hzero)
    nlinarith

end Erdos4.GramBound
