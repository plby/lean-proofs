/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
import ErdosProblems.Erdos240.BakerIntegralExtrapolation
import ErdosProblems.Erdos240.BakerLemma3Concrete
import ErdosProblems.Erdos240.BakerParameters
import ErdosProblems.Erdos240.BakerSourceState
import ErdosProblems.Erdos240.InterpolationProducts
import ErdosProblems.Erdos240.Multiplicity
import Mathlib.Analysis.Complex.AbsMax
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.RingTheory.Polynomial.DegreeLT

/-!
# A concrete integral-grid interpolation step

This file removes the abstract interpolation upper bound from the integral
extrapolation step.  The first part constructs the confluent jet isomorphism
for polynomials of degree below `R*S`.  Its inverse operator norm is a fully
defined (and finite) coarse Hermite constant.  Consequently bounds for the
first `S` derivatives at `1, ..., R` give a proved bound for the Hermite
polynomial, rather than an assumption about that polynomial.

The second part inserts the literal repeated integral nodes, the circle of
radius `3*Rnext`, and the exact elementary product estimates in the Cauchy
remainder theorem.  The final theorem is the pointwise quantitative core of
source Lemma 4; the finite-grid wrapper has precisely the
`R (J+1), Sstep J` output used in the induction.
-/

open scoped BigOperators

open Complex Finset Function Metric Polynomial Set

noncomputable section

namespace Erdos240.BakerLemma4Concrete

open Erdos240.HermiteInterpolation
open Erdos240.InterpolationProducts
open Erdos240.BakerLemma3
open Erdos240.BakerLemma3Concrete
open Erdos240.BakerSourceState

/-- A coarse determinant estimate, used below for the explicit inverse
confluent-Vandermonde bound. -/
theorem norm_det_le_factorial_mul_pow
    {I : Type*} [Fintype I] [DecidableEq I]
    (A : Matrix I I ℂ) {M : ℝ} (_hM : 0 ≤ M)
    (hentry : ∀ i j, ‖A i j‖ ≤ M) :
    ‖A.det‖ ≤ (Fintype.card I).factorial * M ^ Fintype.card I := by
  rw [Matrix.det_apply]
  calc
    ‖∑ σ : Equiv.Perm I, Equiv.Perm.sign σ • ∏ i, A (σ i) i‖ ≤
        ∑ σ : Equiv.Perm I, ‖Equiv.Perm.sign σ • ∏ i, A (σ i) i‖ :=
      norm_sum_le _ _
    _ ≤ ∑ _σ : Equiv.Perm I, M ^ Fintype.card I := by
      apply Finset.sum_le_sum
      intro σ hσ
      have hprod :
        ∏ i, ‖A (σ i) i‖ ≤ ∏ _i : I, M :=
          Finset.prod_le_prod (fun _ _ ↦ norm_nonneg _) fun i _ ↦ hentry _ _
      have hprod' : ∏ i, ‖A (σ i) i‖ ≤ M ^ Fintype.card I := by
        simpa using hprod
      rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h <;>
        simpa [h, norm_prod] using hprod'
    _ = (Fintype.card I).factorial * M ^ Fintype.card I := by
      simp [Fintype.card_perm]

/-- Rows of the square confluent jet matrix: a node in `1, ..., R` and a
derivative order below `S`. -/
abbrev IntegralJetIndex (R S : ℕ) := Σ _ : Fin R, Fin S

/-- The integral nodes are pairwise distinct. -/
private theorem integralNode_injective (R : ℕ) :
    Function.Injective (fun i : Fin R ↦ ((i.1 + 1 : ℕ) : ℂ)) := by
  intro i j hij
  apply Fin.ext
  have hreal : (i.1 + 1 : ℝ) = (j.1 + 1 : ℝ) := by
    simpa using congrArg Complex.re hij
  have hnat : i.1 + 1 = j.1 + 1 := by exact_mod_cast hreal
  exact Nat.add_right_cancel hnat

/-- Lexicographic identification of the `R*S` jet rows with coefficient
indices below `R*S`. -/
def integralJetIndexEquivFin (R S : ℕ) :
    IntegralJetIndex R S ≃ Fin (R * S) :=
  (Equiv.sigmaEquivProd (Fin R) (Fin S)).trans finProdFinEquiv

/-- The square Hasse-derivative confluent Vandermonde matrix, with both rows
and columns indexed by `IntegralJetIndex`. -/
def integralHasseMatrix (R S : ℕ) :
    Matrix (IntegralJetIndex R S) (IntegralJetIndex R S) ℂ :=
  fun ik j ↦
    ((integralJetIndexEquivFin R S j).1.choose ik.2.1 : ℂ) *
      ((ik.1.1 + 1 : ℕ) : ℂ) ^
        ((integralJetIndexEquivFin R S j).1 - ik.2.1)

/-- The same matrix over the integers. -/
def integralHasseMatrixInt (R S : ℕ) :
    Matrix (IntegralJetIndex R S) (IntegralJetIndex R S) ℤ :=
  fun ik j ↦
    ((integralJetIndexEquivFin R S j).1.choose ik.2.1 : ℤ) *
      ((ik.1.1 + 1 : ℕ) : ℤ) ^
        ((integralJetIndexEquivFin R S j).1 - ik.2.1)

theorem integralHasseMatrix_eq_map_intCast (R S : ℕ) :
    integralHasseMatrix R S =
      (integralHasseMatrixInt R S).map (Int.castRingHom ℂ) := by
  ext ik j
  simp [integralHasseMatrix, integralHasseMatrixInt]

/-- The square Hasse matrix has trivial kernel. -/
theorem integralHasseMatrix_mulVec_injective (R S : ℕ) :
    Function.Injective (Matrix.mulVec (integralHasseMatrix R S)) := by
  intro c d hcd
  let e := integralJetIndexEquivFin R S
  let c' : Fin (R * S) → ℂ := fun j ↦ c (e.symm j)
  let d' : Fin (R * S) → ℂ := fun j ↦ d (e.symm j)
  have hmulc :
      Matrix.mulVec (Erdos240.Multiplicity.confluentVandermonde
        (fun i : Fin R ↦ ((i.1 + 1 : ℕ) : ℂ)) (fun _ ↦ S) (R * S)) c' =
      Matrix.mulVec (Erdos240.Multiplicity.confluentVandermonde
        (fun i : Fin R ↦ ((i.1 + 1 : ℕ) : ℂ)) (fun _ ↦ S) (R * S)) d' := by
    funext ik
    have hrow := congr_fun hcd ik
    simpa only [Matrix.mulVec, dotProduct, integralHasseMatrix,
      Erdos240.Multiplicity.confluentVandermonde_apply, c', d', e,
      Equiv.symm_apply_apply,
      ← Equiv.sum_comp (integralJetIndexEquivFin R S)] using hrow
  have hzero :
      Matrix.mulVec (Erdos240.Multiplicity.confluentVandermonde
        (fun i : Fin R ↦ ((i.1 + 1 : ℕ) : ℂ)) (fun _ ↦ S) (R * S)) (c' - d') = 0 := by
    rw [Matrix.mulVec_sub, hmulc, sub_self]
  have hcoeff : c' - d' = 0 :=
    Erdos240.Multiplicity.confluentVandermonde_mulVec_eq_zero
      (fun i : Fin R ↦ ((i.1 + 1 : ℕ) : ℂ)) (fun _ ↦ S) (R * S)
      (integralNode_injective R) (by simp) (c' - d') hzero
  funext j
  have hj := congr_fun hcoeff (integralJetIndexEquivFin R S j)
  simpa [c', d', e] using sub_eq_zero.mp hj

/-- The determinant of the square Hasse matrix is nonzero. -/
theorem integralHasseMatrix_det_ne_zero (R S : ℕ) :
    (integralHasseMatrix R S).det ≠ 0 := by
  intro hdet
  have hker : (Matrix.toLin' (integralHasseMatrix R S)).ker ≠ ⊥ := by
    rw [← LinearMap.det_eq_zero_iff_ker_ne_bot, LinearMap.det_toLin']
    exact hdet
  apply hker
  apply LinearMap.ker_eq_bot.mpr
  intro c d hcd
  apply integralHasseMatrix_mulVec_injective R S
  simpa only [Matrix.toLin'_apply] using hcd

/-- Since the confluent matrix has integral entries and nonzero determinant,
its complex determinant has absolute value at least one. -/
theorem one_le_norm_integralHasseMatrix_det (R S : ℕ) :
    1 ≤ ‖(integralHasseMatrix R S).det‖ := by
  let AZ := integralHasseMatrixInt R S
  have hmap : integralHasseMatrix R S = AZ.map (Int.castRingHom ℂ) :=
    integralHasseMatrix_eq_map_intCast R S
  have hdetmap : (integralHasseMatrix R S).det = (AZ.det : ℂ) := by
    rw [hmap]
    exact ((Int.castRingHom ℂ).map_det AZ).symm
  have hzne : AZ.det ≠ 0 := by
    intro hz
    apply integralHasseMatrix_det_ne_zero R S
    rw [hdetmap, hz]
    simp
  rw [hdetmap, Complex.norm_intCast]
  norm_cast
  exact Int.one_le_abs hzne

/-- A deliberately coarse but closed-form upper bound for every entry of
the integral confluent matrix. -/
theorem norm_integralHasseMatrix_entry_le (R S : ℕ)
    (i j : IntegralJetIndex R S) :
    ‖integralHasseMatrix R S i j‖ ≤
      ((2 * (R + 1) : ℕ) : ℝ) ^ (R * S) := by
  let n := (integralJetIndexEquivFin R S j).1
  let k := i.2.1
  have hn : n < R * S := (integralJetIndexEquivFin R S j).2
  have hkpow : n - k ≤ R * S := (Nat.sub_le n k).trans hn.le
  have hchoose : n.choose k ≤ 2 ^ (R * S) := by
    exact (Nat.choose_le_two_pow n k).trans
      (Nat.pow_le_pow_right (by omega : 0 < 2) hn.le)
  have hnode : i.1.1 + 1 ≤ R + 1 := by omega
  have hnodepow : (i.1.1 + 1) ^ (n - k) ≤ (R + 1) ^ (R * S) := by
    exact (Nat.pow_le_pow_left hnode _).trans
      (Nat.pow_le_pow_right (by omega : 0 < R + 1) hkpow)
  have hnat : n.choose k * (i.1.1 + 1) ^ (n - k) ≤
      (2 * (R + 1)) ^ (R * S) := by
    calc
      n.choose k * (i.1.1 + 1) ^ (n - k) ≤
          2 ^ (R * S) * (R + 1) ^ (R * S) :=
        Nat.mul_le_mul hchoose hnodepow
      _ = (2 * (R + 1)) ^ (R * S) := by rw [mul_pow]
  change ‖((n.choose k : ℕ) : ℂ) *
      (((i.1.1 + 1 : ℕ) : ℂ) ^ (n - k))‖ ≤
        ((2 * (R + 1) : ℕ) : ℝ) ^ (R * S)
  rw [norm_mul, norm_pow]
  simp only [Complex.norm_natCast]
  exact_mod_cast hnat

/-- Closed-form entry bound used for the adjugate estimate. -/
def coarseHasseEntryBound (R S : ℕ) : ℝ :=
  ((2 * (R + 1) : ℕ) : ℝ) ^ (R * S)

/-- Closed-form cofactor bound for the integral confluent matrix. -/
def coarseHasseAdjugateBound (R S : ℕ) : ℝ :=
  (R * S).factorial * coarseHasseEntryBound R S ^ (R * S)

theorem one_le_coarseHasseEntryBound (R S : ℕ) :
    1 ≤ coarseHasseEntryBound R S := by
  unfold coarseHasseEntryBound
  apply one_le_pow₀
  have hR : (0 : ℝ) ≤ R := by positivity
  push_cast
  linarith

theorem coarseHasseAdjugateBound_nonneg (R S : ℕ) :
    0 ≤ coarseHasseAdjugateBound R S := by
  unfold coarseHasseAdjugateBound
  exact mul_nonneg (by positivity) (pow_nonneg
    (zero_le_one.trans (one_le_coarseHasseEntryBound R S)) _)

/-- Every cofactor is bounded by the determinant expansion with the same
coarse entry bound. -/
theorem norm_integralHasseMatrix_adjugate_entry_le (R S : ℕ)
    (i j : IntegralJetIndex R S) :
    ‖(integralHasseMatrix R S).adjugate i j‖ ≤
      coarseHasseAdjugateBound R S := by
  rw [Matrix.adjugate_apply]
  unfold coarseHasseAdjugateBound
  have hentry : ∀ a b,
      ‖(integralHasseMatrix R S).updateRow j (Pi.single i 1) a b‖ ≤
        coarseHasseEntryBound R S := by
    intro a b
    rw [Matrix.updateRow_apply]
    split_ifs with ha
    · by_cases hb : b = i
      · subst b
        simp only [Pi.single_eq_same, norm_one]
        exact one_le_coarseHasseEntryBound R S
      · simp only [Pi.single_eq_of_ne hb, norm_zero]
        exact zero_le_one.trans (one_le_coarseHasseEntryBound R S)
    · exact norm_integralHasseMatrix_entry_le R S a b
  have hdet := norm_det_le_factorial_mul_pow
    ((integralHasseMatrix R S).updateRow j (Pi.single i 1))
    (zero_le_one.trans (one_le_coarseHasseEntryBound R S)) hentry
  simpa [IntegralJetIndex] using hdet

/-- Cramer's rule with the integral determinant lower bound gives a fully
explicit coefficient estimate from normalized jets. -/
theorem norm_coeff_le_of_integralHasseMatrix_mulVec
    {R S : ℕ} {c b : IntegralJetIndex R S → ℂ}
    {delta : ℝ} (_hdelta : 0 ≤ delta)
    (hmul : Matrix.mulVec (integralHasseMatrix R S) c = b)
    (hb : ∀ i, ‖b i‖ ≤ delta) (j : IntegralJetIndex R S) :
    ‖c j‖ ≤ (R * S : ℝ) * coarseHasseAdjugateBound R S * delta := by
  let A := integralHasseMatrix R S
  have hadj : Matrix.mulVec A.adjugate b = A.det • c := by
    rw [← hmul, Matrix.mulVec_mulVec, Matrix.adjugate_mul,
      Matrix.smul_mulVec, Matrix.one_mulVec]
  have hcoord := congr_fun hadj j
  have hdetlower : 1 ≤ ‖A.det‖ := one_le_norm_integralHasseMatrix_det R S
  calc
    ‖c j‖ ≤ ‖A.det‖ * ‖c j‖ := by
      exact le_mul_of_one_le_left (norm_nonneg _) hdetlower
    _ = ‖(A.det • c) j‖ := by simp
    _ = ‖∑ i, A.adjugate j i * b i‖ := by
      rw [← hcoord]
      rfl
    _ ≤ ∑ i, ‖A.adjugate j i * b i‖ := norm_sum_le _ _
    _ ≤ ∑ _i : IntegralJetIndex R S,
        coarseHasseAdjugateBound R S * delta := by
      apply Finset.sum_le_sum
      intro i hi
      rw [norm_mul]
      exact mul_le_mul
        (norm_integralHasseMatrix_adjugate_entry_le R S j i) (hb i)
        (norm_nonneg _) (coarseHasseAdjugateBound_nonneg R S)
    _ = (R * S : ℝ) * coarseHasseAdjugateBound R S * delta := by
      simp [IntegralJetIndex, mul_assoc]

/-- Coefficients below `R*S`, indexed in the same order as the jet rows. -/
def integralCoefficientVector (R S : ℕ) (P : ℂ[X]) :
    IntegralJetIndex R S → ℂ :=
  fun j ↦ P.coeff (integralJetIndexEquivFin R S j).1

/-- Multiplication by the confluent matrix computes all normalized jets of
a polynomial of degree below `R*S`. -/
theorem integralHasseMatrix_mulVec_integralCoefficientVector
    {R S : ℕ} {P : ℂ[X]}
    (hdeg : P ∈ Polynomial.degreeLT ℂ (R * S)) :
    Matrix.mulVec (integralHasseMatrix R S)
        (integralCoefficientVector R S P) =
      fun ik ↦ (Polynomial.hasseDeriv ik.2.1 P).eval
        ((ik.1.1 + 1 : ℕ) : ℂ) := by
  let d := R * S
  let cfin : Fin d → ℂ := fun n ↦ P.coeff n.1
  have hPof : Polynomial.ofFn d cfin = P := by
    ext n
    by_cases hn : n < d
    · simp [cfin, hn]
    · rw [Polynomial.ofFn_coeff_eq_zero_of_ge cfin (Nat.le_of_not_gt hn)]
      exact (((Polynomial.degree_lt_iff_coeff_zero P d).mp
        (Polynomial.mem_degreeLT.mp hdeg)) n (Nat.le_of_not_gt hn)).symm
  funext ik
  change ∑ j : IntegralJetIndex R S,
      ((integralJetIndexEquivFin R S j).1.choose ik.2.1 : ℂ) *
        (((ik.1.1 + 1 : ℕ) : ℂ) ^
          ((integralJetIndexEquivFin R S j).1 - ik.2.1)) *
        P.coeff (integralJetIndexEquivFin R S j).1 = _
  conv_rhs => rw [← hPof, Polynomial.ofFn_eq_sum_monomial]
  simp only [map_sum, Polynomial.eval_finsetSum,
    Polynomial.hasseDeriv_monomial, Polynomial.eval_monomial]
  rw [← Equiv.sum_comp (integralJetIndexEquivFin R S)]
  apply Finset.sum_congr rfl
  intro j hj
  simp [cfin, d]
  ring

/-- A closed-form (very coarse) uniform evaluation constant.  Unlike an
operator norm, this expression can be compared directly with the source
parameter inequalities. -/
def coarseHasseEvaluationBound (R S : ℕ) (rho : ℝ) : ℝ :=
  (R * S : ℝ) ^ 2 * coarseHasseAdjugateBound R S * rho ^ (R * S)

theorem coarseHasseEvaluationBound_nonneg (R S : ℕ) {rho : ℝ}
    (hrho : 0 ≤ rho) : 0 ≤ coarseHasseEvaluationBound R S rho := by
  unfold coarseHasseEvaluationBound
  exact mul_nonneg
    (mul_nonneg (sq_nonneg _) (coarseHasseAdjugateBound_nonneg R S))
    (pow_nonneg hrho _)

/-- Explicit normalized Hermite estimate obtained by expanding Cramer's
rule and then the monomial evaluation sum. -/
theorem norm_eval_le_coarseHasseEvaluationBound_mul
    {R S : ℕ} {P : ℂ[X]} (hdeg : P ∈ Polynomial.degreeLT ℂ (R * S))
    {z : ℂ} {rho delta : ℝ} (hrho : 1 ≤ rho) (hz : ‖z‖ ≤ rho)
    (hdelta : 0 ≤ delta)
    (hjet : ∀ i : Fin R, ∀ k : Fin S,
      ‖(Polynomial.hasseDeriv k.1 P).eval ((i.1 + 1 : ℕ) : ℂ)‖ ≤ delta) :
    ‖P.eval z‖ ≤ coarseHasseEvaluationBound R S rho * delta := by
  let d := R * S
  let cfin : Fin d → ℂ := fun n ↦ P.coeff n.1
  have hPof : Polynomial.ofFn d cfin = P := by
    ext n
    by_cases hn : n < d
    · simp [cfin, hn]
    · rw [Polynomial.ofFn_coeff_eq_zero_of_ge cfin (Nat.le_of_not_gt hn)]
      exact (((Polynomial.degree_lt_iff_coeff_zero P d).mp
        (Polynomial.mem_degreeLT.mp hdeg)) n (Nat.le_of_not_gt hn)).symm
  let b : IntegralJetIndex R S → ℂ := fun ik ↦
    (Polynomial.hasseDeriv ik.2.1 P).eval ((ik.1.1 + 1 : ℕ) : ℂ)
  have hmul : Matrix.mulVec (integralHasseMatrix R S)
      (integralCoefficientVector R S P) = b := by
    exact integralHasseMatrix_mulVec_integralCoefficientVector hdeg
  have hb : ∀ ik, ‖b ik‖ ≤ delta := fun ik ↦ hjet ik.1 ik.2
  have hcoeff : ∀ n : Fin d,
      ‖cfin n‖ ≤ (d : ℝ) * coarseHasseAdjugateBound R S * delta := by
    intro n
    have hc := norm_coeff_le_of_integralHasseMatrix_mulVec hdelta hmul hb
      ((integralJetIndexEquivFin R S).symm n)
    simpa [integralCoefficientVector, cfin, d] using hc
  have hpow : ∀ n : Fin d, ‖z ^ n.1‖ ≤ rho ^ d := by
    intro n
    rw [norm_pow]
    exact (pow_le_pow_left₀ (norm_nonneg z) hz n.1).trans
      (pow_le_pow_right₀ hrho n.2.le)
  rw [← hPof, Polynomial.ofFn_eq_sum_monomial, Polynomial.eval_finsetSum]
  simp only [Polynomial.eval_monomial]
  calc
    ‖∑ n : Fin d, cfin n * z ^ n.1‖ ≤
        ∑ n : Fin d, ‖cfin n * z ^ n.1‖ := norm_sum_le _ _
    _ ≤ ∑ _n : Fin d,
        ((d : ℝ) * coarseHasseAdjugateBound R S * delta) * rho ^ d := by
      apply Finset.sum_le_sum
      intro n hn
      rw [norm_mul]
      exact mul_le_mul (hcoeff n) (hpow n) (norm_nonneg _)
        (mul_nonneg
          (mul_nonneg (by positivity) (coarseHasseAdjugateBound_nonneg R S))
          hdelta)
    _ = coarseHasseEvaluationBound R S rho * delta := by
      simp [coarseHasseEvaluationBound, d]
      ring

/-- The ordinary-derivative jet map on polynomials of degree below `R*S`. -/
def integralJetMap (R S : ℕ) :
    Polynomial.degreeLT ℂ (R * S) →ₗ[ℂ] (IntegralJetIndex R S → ℂ) where
  toFun P ik :=
    ((Polynomial.derivative^[ik.2.1]) P.1).eval (ik.1.1 + 1 : ℕ)
  map_add' P Q := by
    ext ik
    simp
  map_smul' c P := by
    ext ik
    simp

/-- The confluent jet map is injective.  This is the precise finite-dimensional
form of uniqueness of Hermite interpolation. -/
theorem integralJetMap_injective (R S : ℕ) :
    Function.Injective (integralJetMap R S) := by
  intro P Q hPQ
  have hP : integralJetMap R S (P - Q) = 0 := by
    rw [map_sub, hPQ, sub_self]
  have hval : (P - Q).1 = 0 := by
    by_cases hzero : (P - Q).1 = 0
    · exact hzero
    apply Erdos240.Multiplicity.eq_zero_of_hasseDeriv_eval_eq_zero_of_natDegree_lt_sum
      (fun i : Fin R ↦ ((i.1 + 1 : ℕ) : ℂ)) (fun _ ↦ S) (P - Q).1
      (integralNode_injective R)
    · have hpdeg := (Polynomial.mem_degreeLT.mp (P - Q).2)
      rw [Polynomial.degree_eq_natDegree hzero] at hpdeg
      have hnat : (P - Q).1.natDegree < R * S := by exact_mod_cast hpdeg
      simpa using hnat
    · intro i k hk
      have hrow := congr_fun hP ⟨i, ⟨k, hk⟩⟩
      change ((Polynomial.derivative^[k]) (P - Q).1).eval
        ((i.1 + 1 : ℕ) : ℂ) = 0 at hrow
      have hfac := congr_fun
        (Polynomial.factorial_smul_hasseDeriv (R := ℂ) (k := k)) (P - Q).1
      have heval := congrArg (fun Q : ℂ[X] ↦ Q.eval ((i.1 + 1 : ℕ) : ℂ)) hfac
      simp only [LinearMap.smul_apply, eval_smul] at heval
      have heval' : ((k.factorial : ℕ) : ℂ) *
          (Polynomial.hasseDeriv k (P - Q).1).eval ((i.1 + 1 : ℕ) : ℂ) = 0 := by
        calc
          ((k.factorial : ℕ) : ℂ) *
              (Polynomial.hasseDeriv k (P - Q).1).eval ((i.1 + 1 : ℕ) : ℂ) =
              k.factorial •
                (Polynomial.hasseDeriv k (P - Q).1).eval ((i.1 + 1 : ℕ) : ℂ) := by
                  simp [nsmul_eq_mul]
          _ = ((Polynomial.derivative^[k]) (P - Q).1).eval
              ((i.1 + 1 : ℕ) : ℂ) := heval
          _ = 0 := hrow
      have hkfac : ((k.factorial : ℕ) : ℂ) ≠ 0 := by
        exact_mod_cast k.factorial_ne_zero
      exact (mul_eq_zero.mp heval').resolve_left hkfac
  apply Subtype.ext
  exact sub_eq_zero.mp hval

/-- The square ordinary-jet map as a linear equivalence. -/
def integralJetEquiv (R S : ℕ) :
    Polynomial.degreeLT ℂ (R * S) ≃ₗ[ℂ] (IntegralJetIndex R S → ℂ) :=
  LinearEquiv.ofInjectiveOfFinrankEq (integralJetMap R S)
    (integralJetMap_injective R S) (by
      calc
        Module.finrank ℂ (Polynomial.degreeLT ℂ (R * S)) = R * S := by
          simpa using (Polynomial.degreeLTEquiv ℂ (R * S)).finrank_eq
        _ = Module.finrank ℂ (IntegralJetIndex R S → ℂ) := by
          simp [IntegralJetIndex])

/-- Evaluation after inverting the square jet map. -/
def jetEvaluation (R S : ℕ) (z : ℂ) :
    (IntegralJetIndex R S → ℂ) →ₗ[ℂ] ℂ :=
  { toFun := fun v ↦ ((integralJetEquiv R S).symm v).1.eval z
    map_add' := by simp
    map_smul' := by simp }

/-- Continuous evaluation after inversion of the confluent jet map.  Both
spaces are finite-dimensional, so the inverse has a finite operator norm. -/
def jetEvaluationCLM (R S : ℕ) (z : ℂ) :
    (IntegralJetIndex R S → ℂ) →L[ℂ] ℂ :=
  ⟨jetEvaluation R S z, (jetEvaluation R S z).continuous_of_finiteDimensional⟩

/-- The explicit coarse Hermite constant used below.  It is the operator norm
of a completely defined inverse confluent-Vandermonde evaluation map. -/
def hermiteJetConstant (R S : ℕ) (z : ℂ) : ℝ :=
  ‖jetEvaluationCLM R S z‖

theorem hermiteJetConstant_nonneg (R S : ℕ) (z : ℂ) :
    0 ≤ hermiteJetConstant R S z := norm_nonneg _

/-- A polynomial of degree below `R*S` is controlled at every point by the
supremum of its ordinary derivative jets at the integral nodes. -/
theorem norm_eval_le_hermiteJetConstant_mul
    {R S : ℕ} {P : ℂ[X]} (hdeg : P ∈ Polynomial.degreeLT ℂ (R * S))
    {z : ℂ} {delta : ℝ} (hdelta : 0 ≤ delta)
    (hjet : ∀ i : Fin R, ∀ k : Fin S,
      ‖((Polynomial.derivative^[k.1]) P).eval ((i.1 + 1 : ℕ) : ℂ)‖ ≤ delta) :
    ‖P.eval z‖ ≤ hermiteJetConstant R S z * delta := by
  let Psub : Polynomial.degreeLT ℂ (R * S) := ⟨P, hdeg⟩
  have hjetNorm : ‖integralJetMap R S Psub‖ ≤ delta := by
    apply (pi_norm_le_iff_of_nonneg hdelta).2
    intro ik
    exact hjet ik.1 ik.2
  have heq :
      jetEvaluationCLM R S z (integralJetMap R S Psub) = P.eval z := by
    change (((integralJetEquiv R S).symm
      (integralJetMap R S Psub)).1.eval z) = P.eval z
    rw [show integralJetMap R S = (integralJetEquiv R S).toLinearMap by rfl]
    simp [Psub]
  rw [← heq]
  exact (ContinuousLinearMap.le_opNorm _ _).trans
    (mul_le_mul_of_nonneg_left hjetNorm (norm_nonneg _))

/-- Analytic iterated derivatives of a polynomial evaluation agree with
iterates of the formal polynomial derivative. -/
theorem iteratedDeriv_polynomial_eval (P : ℂ[X]) (k : ℕ) :
    iteratedDeriv k (fun z : ℂ ↦ P.eval z) =
      fun z ↦ ((Polynomial.derivative^[k]) P).eval z := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [iteratedDeriv_succ, ih]
      ext z
      rw [Polynomial.deriv]
      simp only [Function.iterate_succ_apply']

/-- The Newton--Hermite polynomial for `R` integral nodes and multiplicity
`S` has degree below the number `R*S` of jet conditions. -/
theorem polynomial_integralNodes_mem_degreeLT (f : ℂ → ℂ) (R S : ℕ) :
    polynomial f (integralNodes R S) ∈ Polynomial.degreeLT ℂ (R * S) := by
  rw [Polynomial.mem_degreeLT]
  by_cases hzero : polynomial f (integralNodes R S) = 0
  · rw [hzero, Polynomial.degree_zero]
    exact WithBot.bot_lt_coe _
  · rcases polynomial_eq_zero_or_natDegree_lt f (integralNodes R S) with h | hdeg
    · exact (hzero h).elim
    · rw [Polynomial.degree_eq_natDegree hzero]
      exact_mod_cast (by simpa [length_integralNodes] using hdeg)

/-- The repeated-node list contains the block belonging to each integral
node in its literal source order. -/
theorem integralNodes_eq_append_replicate_append
    {R S : ℕ} (i : Fin R) :
    ∃ after : List ℂ,
      integralNodes R S =
        integralNodes i.1 S ++ List.replicate S ((i.1 + 1 : ℕ) : ℂ) ++ after := by
  let afterNat :=
    (List.range (R - (i.1 + 1))).map fun j ↦ i.1 + 1 + j
  let after : List ℂ :=
    afterNat.flatMap fun j ↦ List.replicate S (j + 1 : ℕ)
  refine ⟨after, ?_⟩
  unfold integralNodes
  have hsplit : R = (i.1 + 1) + (R - (i.1 + 1)) := by omega
  conv_lhs => rw [hsplit, List.range_add, List.range_succ]
  simp only [List.flatMap_append, List.flatMap_singleton]
  change _ = _ ++ _ ++ afterNat.flatMap
    (fun j ↦ List.replicate S ((j + 1 : ℕ) : ℂ))
  congr 2

/-- Small ordinary jets of an entire function give a proved bound for its
Hermite interpolation polynomial.  No polynomial-value estimate is assumed. -/
theorem norm_polynomial_integralNodes_eval_le_of_small_jets
    {f : ℂ → ℂ} (hf : Differentiable ℂ f) {R S : ℕ}
    {z : ℂ} {delta : ℝ} (hdelta : 0 ≤ delta)
    (hsmall : ∀ i : Fin R, ∀ k : Fin S,
      ‖iteratedDeriv k.1 f ((i.1 + 1 : ℕ) : ℂ)‖ ≤ delta) :
    ‖(polynomial f (integralNodes R S)).eval z‖ ≤
      hermiteJetConstant R S z * delta := by
  apply norm_eval_le_hermiteJetConstant_mul
    (polynomial_integralNodes_mem_degreeLT f R S) hdelta
  intro i k
  rw [← congrFun (iteratedDeriv_polynomial_eval
    (polynomial f (integralNodes R S)) k.1) ((i.1 + 1 : ℕ) : ℂ)]
  obtain ⟨after, hsplit⟩ := integralNodes_eq_append_replicate_append (S := S) i
  rw [hsplit]
  rw [iteratedDeriv_eval_polynomial_eq_of_replicate_block hf
    (integralNodes i.1 S) after ((i.1 + 1 : ℕ) : ℂ) S k.1 k.2]
  exact hsmall i k

/-! ### Normalized (Hasse) jets

The estimates in the source are for `f^(k)/k!`.  The following parallel
jet equivalence is therefore built out of `Polynomial.hasseDeriv` itself.
This avoids introducing a spurious factor `S!` when the analytic estimates
are inserted into Hermite interpolation. -/

/-- The normalized-derivative jet map on polynomials of degree below
`R*S`. -/
def integralHasseJetMap (R S : ℕ) :
    Polynomial.degreeLT ℂ (R * S) →ₗ[ℂ] (IntegralJetIndex R S → ℂ) where
  toFun P ik :=
    (Polynomial.hasseDeriv ik.2.1 P.1).eval (ik.1.1 + 1 : ℕ)
  map_add' P Q := by
    ext ik
    simp
  map_smul' c P := by
    ext ik
    simp

/-- Uniqueness of Hermite interpolation, expressed directly with normalized
jets. -/
theorem integralHasseJetMap_injective (R S : ℕ) :
    Function.Injective (integralHasseJetMap R S) := by
  intro P Q hPQ
  have hzero : integralHasseJetMap R S (P - Q) = 0 := by
    rw [map_sub, hPQ, sub_self]
  have hpoly : (P - Q).1 = 0 := by
    by_cases hpq : (P - Q).1 = 0
    · exact hpq
    apply Erdos240.Multiplicity.eq_zero_of_hasseDeriv_eval_eq_zero_of_natDegree_lt_sum
      (fun i : Fin R ↦ ((i.1 + 1 : ℕ) : ℂ)) (fun _ ↦ S) (P - Q).1
      (integralNode_injective R)
    · have hpdeg := Polynomial.mem_degreeLT.mp (P - Q).2
      rw [Polynomial.degree_eq_natDegree hpq] at hpdeg
      have hnat : (P - Q).1.natDegree < R * S := by exact_mod_cast hpdeg
      simpa using hnat
    · intro i k hk
      have hrow := congr_fun hzero ⟨i, ⟨k, hk⟩⟩
      simpa [integralHasseJetMap] using hrow
  apply Subtype.ext
  exact sub_eq_zero.mp hpoly

/-- The square normalized-jet map as a linear equivalence. -/
def integralHasseJetEquiv (R S : ℕ) :
    Polynomial.degreeLT ℂ (R * S) ≃ₗ[ℂ] (IntegralJetIndex R S → ℂ) :=
  LinearEquiv.ofInjectiveOfFinrankEq (integralHasseJetMap R S)
    (integralHasseJetMap_injective R S) (by
      calc
        Module.finrank ℂ (Polynomial.degreeLT ℂ (R * S)) = R * S := by
          simpa using (Polynomial.degreeLTEquiv ℂ (R * S)).finrank_eq
        _ = Module.finrank ℂ (IntegralJetIndex R S → ℂ) := by
          simp [IntegralJetIndex])

/-- Evaluation after inversion of the normalized confluent jet map. -/
def hasseJetEvaluation (R S : ℕ) (z : ℂ) :
    (IntegralJetIndex R S → ℂ) →ₗ[ℂ] ℂ :=
  { toFun := fun v ↦ ((integralHasseJetEquiv R S).symm v).1.eval z
    map_add' := by simp
    map_smul' := by simp }

def hasseJetEvaluationCLM (R S : ℕ) (z : ℂ) :
    (IntegralJetIndex R S → ℂ) →L[ℂ] ℂ :=
  ⟨hasseJetEvaluation R S z,
    (hasseJetEvaluation R S z).continuous_of_finiteDimensional⟩

/-- A completely defined finite normalized-Hermite constant. -/
def hasseHermiteJetConstant (R S : ℕ) (z : ℂ) : ℝ :=
  ‖hasseJetEvaluationCLM R S z‖

theorem hasseHermiteJetConstant_nonneg (R S : ℕ) (z : ℂ) :
    0 ≤ hasseHermiteJetConstant R S z := norm_nonneg _

/-- Evaluation is controlled by the supremum of the normalized polynomial
jets. -/
theorem norm_eval_le_hasseHermiteJetConstant_mul
    {R S : ℕ} {P : ℂ[X]} (hdeg : P ∈ Polynomial.degreeLT ℂ (R * S))
    {z : ℂ} {delta : ℝ} (hdelta : 0 ≤ delta)
    (hjet : ∀ i : Fin R, ∀ k : Fin S,
      ‖(Polynomial.hasseDeriv k.1 P).eval ((i.1 + 1 : ℕ) : ℂ)‖ ≤ delta) :
    ‖P.eval z‖ ≤ hasseHermiteJetConstant R S z * delta := by
  let Psub : Polynomial.degreeLT ℂ (R * S) := ⟨P, hdeg⟩
  have hjetNorm : ‖integralHasseJetMap R S Psub‖ ≤ delta := by
    apply (pi_norm_le_iff_of_nonneg hdelta).2
    intro ik
    exact hjet ik.1 ik.2
  have heq :
      hasseJetEvaluationCLM R S z (integralHasseJetMap R S Psub) = P.eval z := by
    change (((integralHasseJetEquiv R S).symm
      (integralHasseJetMap R S Psub)).1.eval z) = P.eval z
    rw [show integralHasseJetMap R S =
      (integralHasseJetEquiv R S).toLinearMap by rfl]
    simp [Psub]
  rw [← heq]
  exact (ContinuousLinearMap.le_opNorm _ _).trans
    (mul_le_mul_of_nonneg_left hjetNorm (norm_nonneg _))

/-- Formal Hasse derivatives are analytic derivatives divided by `k!`. -/
theorem hasseDeriv_eval_eq_iteratedDeriv_div_factorial
    (P : ℂ[X]) (k : ℕ) (z : ℂ) :
    (Polynomial.hasseDeriv k P).eval z =
      iteratedDeriv k (fun w : ℂ ↦ P.eval w) z / (k.factorial : ℂ) := by
  rw [congrFun (iteratedDeriv_polynomial_eval P k) z]
  have hfac := congr_fun
    (Polynomial.factorial_smul_hasseDeriv (R := ℂ) (k := k)) P
  have heval := congrArg (fun Q : ℂ[X] ↦ Q.eval z) hfac
  simp only [LinearMap.smul_apply, eval_smul] at heval
  have heval' : ((k.factorial : ℕ) : ℂ) *
      (Polynomial.hasseDeriv k P).eval z =
        ((Polynomial.derivative^[k]) P).eval z := by
    simpa [nsmul_eq_mul] using heval
  rw [← heval']
  have hk : ((k.factorial : ℕ) : ℂ) ≠ 0 := by
    exact_mod_cast k.factorial_ne_zero
  exact (eq_div_iff hk).2 (by ring)

/-! ### A sharp elementary bound for the Hermite polynomial

The determinant estimate above is useful as a completely generic fallback,
but is much too wasteful for the source exponents: its logarithm is quadratic
in the number of jet conditions.  The following Newton-division argument
loses only an exponential whose logarithm is linear in that number.  At each
node it divides off `X-a`; normalized jets of the quotient grow by at most
the length of the remaining list because distinct integral nodes are at
distance at least one. -/

/-- All normalized polynomial jets prescribed by a repeated-node list are
bounded by `delta`. -/
def JetBoundOn (P : ℂ[X]) (nodes : List ℂ) (delta : ℝ) : Prop :=
  ∀ b k, k < nodes.count b → ‖(hasseDeriv k P).eval b‖ ≤ delta

/-- Removing the first Newton factor costs at most `length + 2` in the
remaining normalized jets. -/
theorem jetBoundOn_tail_div
    (P Q : ℂ[X]) (a : ℂ) (nodes : List ℂ) (delta : ℝ)
    (hdecomp : (X - C a) * Q = P - C (P.eval a))
    (hsep : ∀ b ∈ nodes, b ≠ a → 1 ≤ ‖b - a‖)
    (hdelta : 0 ≤ delta)
    (hjet : JetBoundOn P (a :: nodes) delta) :
    JetBoundOn Q nodes ((nodes.length + 2 : ℕ) * delta) := by
  intro b k hk
  by_cases hba : b = a
  · subst b
    have heq : (hasseDeriv k Q).eval a = (hasseDeriv (k + 1) P).eval a := by
      have ht := congrArg (fun U : ℂ[X] ↦ (taylor a U).coeff (k + 1)) hdecomp
      have hc (T : ℂ[X]) :
          ((X + C (0 : ℂ)) * T).coeff (k + 1) = T.coeff k := by
        rw [add_mul, coeff_add, coeff_X_mul, coeff_C_mul]
        simp
      rw [taylor_mul, map_sub, map_sub, taylor_X, taylor_C, taylor_C] at ht
      rw [show X + C a - C a = X + C (0 : ℂ) by simp] at ht
      rw [hc] at ht
      simpa [taylor_coeff] using ht
    rw [heq]
    calc
      _ ≤ delta := hjet a (k + 1) (by simp; omega)
      _ ≤ (nodes.length + 2 : ℕ) * delta := by
        exact le_mul_of_one_le_left hdelta (by
          push_cast
          have : (0 : ℝ) ≤ nodes.length := by positivity
          linarith)
  · have hbmem : b ∈ nodes := List.count_pos_iff.mp (Nat.zero_lt_of_lt hk)
    have hdenom : 1 ≤ ‖b - a‖ := hsep b hbmem hba
    have hcount : (a :: nodes).count b = nodes.count b := by
      simp [Ne.symm hba]
    have haux : ∀ j, j < nodes.count b →
        ‖(hasseDeriv j Q |>.eval b)‖ ≤ (j + 2 : ℕ) * delta := by
      intro j hj
      induction j with
      | zero =>
          have he := congrArg (fun U : ℂ[X] ↦ U.eval b) hdecomp
          have heq : (b - a) * Q.eval b = P.eval b - P.eval a := by
            simpa using he
          calc
            ‖(hasseDeriv 0 Q |>.eval b)‖ = ‖Q.eval b‖ := by simp
            _ ≤ ‖b - a‖ * ‖Q.eval b‖ :=
              le_mul_of_one_le_left (norm_nonneg _) hdenom
            _ = ‖P.eval b - P.eval a‖ := by rw [← norm_mul, heq]
            _ ≤ ‖P.eval b‖ + ‖P.eval a‖ := norm_sub_le _ _
            _ ≤ delta + delta := add_le_add
              (by simpa using hjet b 0 (by simpa [hcount] using hj))
              (by simpa only [hasseDeriv_zero, LinearMap.id_apply]
                using hjet a 0 (by simp))
            _ = (0 + 2 : ℕ) * delta := by norm_num; ring
      | succ j ih =>
          have hj' : j < nodes.count b := Nat.lt_of_succ_lt hj
          have hrec : (b - a) * (hasseDeriv (j + 1) Q).eval b +
                (hasseDeriv j Q).eval b = (hasseDeriv (j + 1) P).eval b := by
            have ht := congrArg
              (fun U : ℂ[X] ↦ (taylor b U).coeff (j + 1)) hdecomp
            have hc (T : ℂ[X]) :
                ((X + C (b - a)) * T).coeff (j + 1) =
                  T.coeff j + (b - a) * T.coeff (j + 1) := by
              rw [add_mul, coeff_add, coeff_X_mul, coeff_C_mul]
            rw [taylor_mul, map_sub, map_sub, taylor_X, taylor_C, taylor_C] at ht
            rw [show X + C b - C a = X + C (b - a) by rw [map_sub]; ring] at ht
            rw [hc] at ht
            simpa [taylor_coeff, add_comm] using ht
          have hprod : (b - a) * (hasseDeriv (j + 1) Q).eval b =
              (hasseDeriv (j + 1) P).eval b - (hasseDeriv j Q).eval b := by
            linear_combination hrec
          calc
            ‖hasseDeriv (j + 1) Q |>.eval b‖ ≤
                ‖b - a‖ * ‖hasseDeriv (j + 1) Q |>.eval b‖ :=
              le_mul_of_one_le_left (norm_nonneg _) hdenom
            _ = ‖(hasseDeriv (j + 1) P |>.eval b) -
                (hasseDeriv j Q |>.eval b)‖ := by rw [← norm_mul, hprod]
            _ ≤ ‖hasseDeriv (j + 1) P |>.eval b‖ +
                ‖hasseDeriv j Q |>.eval b‖ := norm_sub_le _ _
            _ ≤ delta + (j + 2 : ℕ) * delta := add_le_add
              (hjet b (j + 1) (by simpa [hcount] using hj)) (ih hj')
            _ = (j + 1 + 2 : ℕ) * delta := by push_cast; ring
    calc
      _ ≤ (k + 2 : ℕ) * delta := haux k hk
      _ ≤ (nodes.length + 2 : ℕ) * delta := by
        gcongr
        exact Nat.le_of_lt
          (lt_of_lt_of_le hk (List.count_le_length (a := b) (l := nodes)))

/-- Exact recursive Newton loss. -/
def jetEvaluationFactor : ℕ → ℝ → ℝ
  | 0, _ => 0
  | n + 1, A => 1 + A * (n + 2) * jetEvaluationFactor n A

theorem jetEvaluationFactor_nonneg (n : ℕ) {A : ℝ} (hA : 0 ≤ A) :
    0 ≤ jetEvaluationFactor n A := by
  induction n with
  | zero => simp [jetEvaluationFactor]
  | succ n ih => simp only [jetEvaluationFactor]; positivity

/-- Closed form for the recursive Newton loss.  Its logarithm is
`O(n log(n A))`, rather than the quadratic determinant loss. -/
theorem jetEvaluationFactor_le_pow (n : ℕ) {A : ℝ} (hA : 0 ≤ A) :
    jetEvaluationFactor n A ≤ (1 + (n + 1 : ℕ) * A) ^ n := by
  induction n with
  | zero => simp [jetEvaluationFactor]
  | succ n ih =>
      let B : ℝ := 1 + (n + 2 : ℕ) * A
      have hB1 : 1 ≤ B := by
        dsimp [B]
        exact le_add_of_nonneg_right (mul_nonneg (Nat.cast_nonneg _) hA)
      have hsmall : 1 + (n + 1 : ℕ) * A ≤ B := by
        dsimp [B]
        push_cast
        nlinarith
      have hp : (1 + (n + 1 : ℕ) * A) ^ n ≤ B ^ n := by gcongr
      have hone : 1 ≤ B ^ n := one_le_pow₀ hB1
      calc
        jetEvaluationFactor (n + 1) A =
            1 + A * (n + 2 : ℕ) * jetEvaluationFactor n A := by
          simp [jetEvaluationFactor]
        _ ≤ 1 + A * (n + 2 : ℕ) * (1 + (n + 1 : ℕ) * A) ^ n := by
          gcongr
        _ ≤ 1 + A * (n + 2 : ℕ) * B ^ n := by gcongr
        _ ≤ B * B ^ n := by
          dsimp [B] at hB1 hone ⊢
          push_cast at hone ⊢
          nlinarith
        _ = (1 + (n + 1 + 1 : ℕ) * A) ^ (n + 1) := by
          dsimp [B]
          push_cast
          rw [pow_succ]
          ring

/-- Evaluation of a polynomial of degree below the number of repeated nodes,
from its normalized jets, with the exact recursive Newton loss. -/
theorem norm_eval_le_jetEvaluationFactor
    (P : ℂ[X]) (nodes : List ℂ) (z : ℂ) (A delta : ℝ)
    (hA : 0 ≤ A) (hdelta : 0 ≤ delta)
    (hnodes : ∀ a ∈ nodes, ‖z - a‖ ≤ A)
    (hsep : ∀ a ∈ nodes, ∀ b ∈ nodes, b ≠ a → 1 ≤ ‖b - a‖)
    (hdeg : P.natDegree < nodes.length)
    (hjet : JetBoundOn P nodes delta) :
    ‖P.eval z‖ ≤ jetEvaluationFactor nodes.length A * delta := by
  induction nodes generalizing P delta with
  | nil => simp at hdeg
  | cons a nodes ih =>
      by_cases hnil : nodes = []
      · subst nodes
        have hPdeg : P.natDegree ≤ 0 := by simpa using hdeg
        have heval : P.eval z = P.eval a := by
          rw [eq_C_of_natDegree_le_zero hPdeg]
          simp
        rw [heval]
        simpa [jetEvaluationFactor] using hjet a 0 (by simp)
      · let Q : ℂ[X] := (P - C (P.eval a)) /ₘ (X - C a)
        have hroot : IsRoot (P - C (P.eval a)) a := by simp [IsRoot]
        have hdecomp : (X - C a) * Q = P - C (P.eval a) := by
          exact mul_divByMonic_eq_iff_isRoot.mpr hroot
        have hQdeg : Q.natDegree < nodes.length := by
          dsimp only [Q]
          rw [natDegree_divByMonic _ (monic_X_sub_C a), natDegree_X_sub_C]
          have hsub : (P - C (P.eval a)).natDegree ≤ P.natDegree := by
            calc
              _ ≤ max P.natDegree (C (P.eval a)).natDegree :=
                natDegree_sub_le P (C (P.eval a))
              _ ≤ P.natDegree := by simp
          have hnpos : 0 < nodes.length :=
            Nat.pos_of_ne_zero (by simpa using hnil)
          have hPle : P.natDegree ≤ nodes.length := by simpa using hdeg
          by_cases hs : (P - C (P.eval a)).natDegree = 0
          · simp [hs, hnpos]
          · have hspos : 0 < (P - C (P.eval a)).natDegree :=
              Nat.pos_of_ne_zero hs
            omega
        have hQjet : JetBoundOn Q nodes ((nodes.length + 2 : ℕ) * delta) :=
          jetBoundOn_tail_div P Q a nodes delta hdecomp
            (fun b hb hba ↦ hsep a (by simp) b (by simp [hb]) hba) hdelta hjet
        have hQbound := ih Q ((nodes.length + 2 : ℕ) * delta)
          (mul_nonneg (by positivity) hdelta)
          (fun b hb ↦ hnodes b (by simp [hb]))
          (fun b hb c hc hcb ↦ hsep b (by simp [hb]) c (by simp [hc]) hcb)
          hQdeg hQjet
        have he := congrArg (fun U : ℂ[X] ↦ U.eval z) hdecomp
        have heval : P.eval z = P.eval a + (z - a) * Q.eval z := by
          have he' : (z - a) * Q.eval z = P.eval z - P.eval a := by
            simpa using he
          linear_combination -he'
        rw [heval]
        calc
          _ ≤ ‖P.eval a‖ + ‖z - a‖ * ‖Q.eval z‖ := by
            exact (norm_add_le _ _).trans_eq
              (congrArg₂ (.+.) rfl (norm_mul _ _))
          _ ≤ delta + A *
                (jetEvaluationFactor nodes.length A *
                  ((nodes.length + 2 : ℕ) * delta)) := by
            gcongr
            · simpa only [hasseDeriv_zero, LinearMap.id_apply]
                using hjet a 0 (by simp)
            · exact hnodes a (by simp)
          _ = jetEvaluationFactor (a :: nodes).length A * delta := by
            simp only [List.length_cons, jetEvaluationFactor]
            push_cast
            ring

/-- Small normalized analytic jets give a Hermite-polynomial bound without
any factorial loss. -/
theorem norm_polynomial_integralNodes_eval_le_of_small_normalized_jets
    {f : ℂ → ℂ} (hf : Differentiable ℂ f) {R S : ℕ}
    {z : ℂ} {delta : ℝ} (hdelta : 0 ≤ delta)
    (hsmall : ∀ i : Fin R, ∀ k : Fin S,
      ‖iteratedDeriv k.1 f ((i.1 + 1 : ℕ) : ℂ) /
        (k.1.factorial : ℂ)‖ ≤ delta) :
    ‖(polynomial f (integralNodes R S)).eval z‖ ≤
      hasseHermiteJetConstant R S z * delta := by
  apply norm_eval_le_hasseHermiteJetConstant_mul
    (polynomial_integralNodes_mem_degreeLT f R S) hdelta
  intro i k
  rw [hasseDeriv_eval_eq_iteratedDeriv_div_factorial]
  obtain ⟨after, hsplit⟩ := integralNodes_eq_append_replicate_append (S := S) i
  rw [hsplit]
  rw [iteratedDeriv_eval_polynomial_eq_of_replicate_block hf
    (integralNodes i.1 S) after ((i.1 + 1 : ℕ) : ℂ) S k.1 k.2]
  exact hsmall i k

theorem mem_integralNodes_iff_data {R S : ℕ} {a : ℂ} :
    a ∈ integralNodes R S ↔
      ∃ i < R, S ≠ 0 ∧ a = ((i + 1 : ℕ) : ℂ) := by
  simp [integralNodes]

@[simp] theorem count_integralNodes_node
    {R S i : ℕ} (hi : i < R) :
    (integralNodes R S).count (((i + 1 : ℕ) : ℂ)) = S := by
  induction R generalizing i with
  | zero => omega
  | succ R ih =>
      rw [integralNodes, List.range_succ, List.flatMap_append, List.count_append]
      simp only [List.flatMap_singleton]
      by_cases hiR : i < R
      · rw [show (List.range R).flatMap
            (fun j ↦ List.replicate S (((j + 1 : ℕ) : ℂ))) =
            integralNodes R S by rfl, ih hiR]
        have hne : (((i + 1 : ℕ) : ℂ)) ≠ (((R + 1 : ℕ) : ℂ)) := by
          exact_mod_cast (by omega : i + 1 ≠ R + 1)
        have hne' : (i : ℂ) + 1 ≠ (R : ℂ) + 1 := by
          norm_num at hne ⊢
          exact hne
        rw [List.count_replicate]
        simp [Ne.symm hne']
      · have hir : i = R := by omega
        subst i
        have hnotmem : (((R + 1 : ℕ) : ℂ)) ∉ integralNodes R S := by
          simp [integralNodes]
        rw [show (List.range R).flatMap
            (fun j ↦ List.replicate S (((j + 1 : ℕ) : ℂ))) =
            integralNodes R S by rfl]
        have hz := List.count_eq_zero_of_not_mem hnotmem
        norm_num at hz ⊢
        simp [hz]

theorem one_le_norm_integral_nodes_sub_of_ne {i j : ℕ} (hij : j ≠ i) :
    1 ≤ ‖((j + 1 : ℕ) : ℂ) - ((i + 1 : ℕ) : ℂ)‖ := by
  have heq : (((j + 1 : ℕ) : ℂ) - ((i + 1 : ℕ) : ℂ)) =
      (((j : ℝ) - (i : ℝ) : ℝ) : ℂ) := by norm_num
  rw [heq, Complex.norm_real, Real.norm_eq_abs]
  by_cases hji : i < j
  · have hsub : (j : ℝ) - (i : ℝ) = ((j - i : ℕ) : ℝ) := by
      rw [Nat.cast_sub (Nat.le_of_lt hji)]
    rw [hsub, abs_of_nonneg (by positivity)]
    exact_mod_cast (show 1 ≤ j - i by omega)
  · have hij' : j < i := by omega
    have hsub : (j : ℝ) - (i : ℝ) = -((i - j : ℕ) : ℝ) := by
      rw [Nat.cast_sub (Nat.le_of_lt hij')]
      ring
    rw [hsub, abs_neg, abs_of_nonneg (by positivity)]
    exact_mod_cast (show 1 ≤ i - j by omega)

/-- The source-usable normalized Hermite loss.  Unlike the determinant
fallback, the exponent is exactly the number `R*S` of conditions. -/
def sharpHasseEvaluationBound (R S : ℕ) (rho : ℝ) : ℝ :=
  (1 + (R * S + 1 : ℕ) * (rho + R)) ^ (R * S)

theorem sharpHasseEvaluationBound_nonneg (R S : ℕ) {rho : ℝ}
    (hrho : 0 ≤ rho) : 0 ≤ sharpHasseEvaluationBound R S rho := by
  unfold sharpHasseEvaluationBound
  positivity

/-- Small normalized analytic jets control the integral-node Hermite
polynomial with a loss of logarithmic size `O(R*S*log(R*S*(rho+R)))`. -/
theorem norm_polynomial_integralNodes_eval_le_sharp_of_small_normalized_jets
    {f : ℂ → ℂ} (hf : Differentiable ℂ f) {R S : ℕ}
    {z : ℂ} {rho delta : ℝ} (hrho : 0 ≤ rho) (hz : ‖z‖ ≤ rho)
    (hdelta : 0 ≤ delta)
    (hsmall : ∀ i : Fin R, ∀ k : Fin S,
      ‖iteratedDeriv k.1 f ((i.1 + 1 : ℕ) : ℂ) /
        (k.1.factorial : ℂ)‖ ≤ delta) :
    ‖(polynomial f (integralNodes R S)).eval z‖ ≤
      sharpHasseEvaluationBound R S rho * delta := by
  let P : ℂ[X] := polynomial f (integralNodes R S)
  by_cases hP : P = 0
  · rw [show polynomial f (integralNodes R S) = 0 by exact hP]
    simp only [eval_zero, norm_zero]
    exact mul_nonneg (sharpHasseEvaluationBound_nonneg R S hrho) hdelta
  have hdeg : P.natDegree < (integralNodes R S).length := by
    rcases polynomial_eq_zero_or_natDegree_lt f (integralNodes R S) with hzero | hlt
    · exact (hP hzero).elim
    · exact hlt
  have hnodes : ∀ a ∈ integralNodes R S, ‖z - a‖ ≤ rho + R := by
    intro a ha
    rcases mem_integralNodes_iff_data.mp ha with ⟨i, hi, _hS, rfl⟩
    calc
      ‖z - ((i + 1 : ℕ) : ℂ)‖ ≤ ‖z‖ + ‖((i + 1 : ℕ) : ℂ)‖ :=
        norm_sub_le _ _
      _ ≤ rho + R := by
        rw [Complex.norm_natCast]
        gcongr
        exact_mod_cast (show i + 1 ≤ R by omega)
  have hsep : ∀ a ∈ integralNodes R S, ∀ b ∈ integralNodes R S,
      b ≠ a → 1 ≤ ‖b - a‖ := by
    intro a ha b hb hba
    rcases mem_integralNodes_iff_data.mp ha with ⟨i, hi, _hS, rfl⟩
    rcases mem_integralNodes_iff_data.mp hb with ⟨j, hj, _hS', rfl⟩
    apply one_le_norm_integral_nodes_sub_of_ne
    intro hji
    apply hba
    subst j
    rfl
  have hjet : JetBoundOn P (integralNodes R S) delta := by
    intro a k hk
    have ha : a ∈ integralNodes R S :=
      List.count_pos_iff.mp (Nat.zero_lt_of_lt hk)
    rcases mem_integralNodes_iff_data.mp ha with ⟨i, hi, hS, rfl⟩
    have hkS : k < S := by
      rw [count_integralNodes_node (S := S) hi] at hk
      exact hk
    dsimp only [P]
    rw [hasseDeriv_eval_eq_iteratedDeriv_div_factorial]
    obtain ⟨after, hsplit⟩ :=
      integralNodes_eq_append_replicate_append (S := S) ⟨i, hi⟩
    rw [hsplit]
    rw [iteratedDeriv_eval_polynomial_eq_of_replicate_block hf
      (integralNodes i S) after ((i + 1 : ℕ) : ℂ) S k hkS]
    exact hsmall ⟨i, hi⟩ ⟨k, hkS⟩
  have hrecursive := norm_eval_le_jetEvaluationFactor P (integralNodes R S) z
    (rho + R) delta (by positivity) hdelta hnodes hsep hdeg hjet
  calc
    ‖(polynomial f (integralNodes R S)).eval z‖ = ‖P.eval z‖ := rfl
    _ ≤ jetEvaluationFactor (integralNodes R S).length (rho + R) * delta :=
      hrecursive
    _ ≤ sharpHasseEvaluationBound R S rho * delta := by
      apply mul_le_mul_of_nonneg_right _ hdelta
      rw [length_integralNodes]
      exact jetEvaluationFactor_le_pow (R * S) (by positivity)

/-- The normalized analytic-jet theorem with the closed-form Cramer bound.
This is the version intended for source-level numerical budgets. -/
theorem norm_polynomial_integralNodes_eval_le_coarse_of_small_normalized_jets
    {f : ℂ → ℂ} (hf : Differentiable ℂ f) {R S : ℕ}
    {z : ℂ} {rho delta : ℝ} (hrho : 1 ≤ rho) (hz : ‖z‖ ≤ rho)
    (hdelta : 0 ≤ delta)
    (hsmall : ∀ i : Fin R, ∀ k : Fin S,
      ‖iteratedDeriv k.1 f ((i.1 + 1 : ℕ) : ℂ) /
        (k.1.factorial : ℂ)‖ ≤ delta) :
    ‖(polynomial f (integralNodes R S)).eval z‖ ≤
      coarseHasseEvaluationBound R S rho * delta := by
  apply norm_eval_le_coarseHasseEvaluationBound_mul
    (polynomial_integralNodes_mem_degreeLT f R S) hrho hz hdelta
  intro i k
  rw [hasseDeriv_eval_eq_iteratedDeriv_div_factorial]
  obtain ⟨after, hsplit⟩ := integralNodes_eq_append_replicate_append (S := S) i
  rw [hsplit]
  rw [iteratedDeriv_eval_polynomial_eq_of_replicate_block hf
    (integralNodes i.1 S) after ((i.1 + 1 : ℕ) : ℂ) S k.1 k.2]
  exact hsmall i k

/-! ### The factorial local-circle estimate in source equation (9) -/

/-- A node strictly to the left of the centre of a radius-`1/2` circle is
bounded below by half its integral distance from the centre. -/
theorem localCircle_left_factor_lower {z : ℂ} {r i : ℕ}
    (hi : i < r - 1) (hz : ‖z - (r : ℂ)‖ = 1 / 2) :
    ((r - (i + 1) : ℕ) : ℝ) / 2 ≤ ‖z - ((i + 1 : ℕ) : ℂ)‖ := by
  have hir : i + 1 < r := by omega
  have hdist : ‖((r : ℕ) : ℂ) - ((i + 1 : ℕ) : ℂ)‖ ≤
      ‖((r : ℕ) : ℂ) - z‖ + ‖z - ((i + 1 : ℕ) : ℂ)‖ := by
    calc
      ‖((r : ℕ) : ℂ) - ((i + 1 : ℕ) : ℂ)‖ =
          ‖(((r : ℕ) : ℂ) - z) - (((i + 1 : ℕ) : ℂ) - z)‖ := by
        congr 1 <;> ring
      _ ≤ ‖((r : ℕ) : ℂ) - z‖ + ‖((i + 1 : ℕ) : ℂ) - z‖ :=
        norm_sub_le _ _
      _ = ‖((r : ℕ) : ℂ) - z‖ + ‖z - ((i + 1 : ℕ) : ℂ)‖ := by
        simp only [norm_sub_rev]
  rw [norm_sub_rev ((r : ℕ) : ℂ) z, hz] at hdist
  have hcast : ‖((r : ℕ) : ℂ) - ((i + 1 : ℕ) : ℂ)‖ =
      ((r - (i + 1) : ℕ) : ℝ) := by
    rw [show ((r : ℕ) : ℂ) - ((i + 1 : ℕ) : ℂ) =
      (((r - (i + 1) : ℕ) : ℝ) : ℂ) by
        norm_num [Nat.cast_sub (Nat.le_of_lt hir)]]
    simp
  rw [hcast] at hdist
  have hone : (1 : ℝ) ≤ (r - (i + 1) : ℕ) := by
    exact_mod_cast (show 1 ≤ r - (i + 1) by omega)
  norm_num at hz hdist ⊢
  nlinarith

/-- The corresponding lower bound for a node to the right of the centre. -/
theorem localCircle_right_factor_lower {z : ℂ} {r j : ℕ}
    (hz : ‖z - (r : ℂ)‖ = 1 / 2) :
    ((j + 1 : ℕ) : ℝ) / 2 ≤ ‖z - ((r + j + 1 : ℕ) : ℂ)‖ := by
  have hdist : ‖((r + j + 1 : ℕ) : ℂ) - (r : ℂ)‖ ≤
      ‖((r + j + 1 : ℕ) : ℂ) - z‖ + ‖z - (r : ℂ)‖ := by
    calc
      ‖((r + j + 1 : ℕ) : ℂ) - (r : ℂ)‖ =
          ‖(((r + j + 1 : ℕ) : ℂ) - z) - ((r : ℂ) - z)‖ := by
        congr 1 <;> ring
      _ ≤ ‖((r + j + 1 : ℕ) : ℂ) - z‖ + ‖(r : ℂ) - z‖ :=
        norm_sub_le _ _
      _ = ‖((r + j + 1 : ℕ) : ℂ) - z‖ + ‖z - (r : ℂ)‖ := by
        simp only [norm_sub_rev]
  rw [norm_sub_rev ((r + j + 1 : ℕ) : ℂ) z, hz] at hdist
  have hcast : ‖((r + j + 1 : ℕ) : ℂ) - (r : ℂ)‖ =
      ((j + 1 : ℕ) : ℝ) := by
    rw [show ((r + j + 1 : ℕ) : ℂ) - (r : ℂ) =
      (((j + 1 : ℕ) : ℝ) : ℂ) by push_cast; ring]
    simp only [Complex.norm_real, Real.norm_eq_abs]
    rw [abs_of_nonneg (by positivity : (0 : ℝ) ≤ (j + 1 : ℕ))]
  rw [hcast] at hdist
  norm_num at hdist ⊢
  nlinarith

/-- Exact factorial lower bound for the unpowered nodal denominator on the
small circle around the integral node `r`. -/
theorem localCircle_denominator_lower {R r : ℕ} (hr : 1 ≤ r) (hrR : r ≤ R)
    {z : ℂ} (hz : ‖z - (r : ℂ)‖ = 1 / 2) :
    (1 / 2 : ℝ) ^ R * (r - 1).factorial * (R - r).factorial ≤
      ∏ i ∈ range R, ‖z - ((i + 1 : ℕ) : ℂ)‖ := by
  have hsplit : R = (r - 1) + 1 + (R - r) := by omega
  have hprod :
      (∏ i ∈ range R, ‖z - ((i + 1 : ℕ) : ℂ)‖) =
        (∏ i ∈ range (r - 1), ‖z - ((i + 1 : ℕ) : ℂ)‖) *
          ‖z - (r : ℂ)‖ *
          (∏ j ∈ range (R - r),
            ‖z - ((r + j + 1 : ℕ) : ℂ)‖) := by
    conv_lhs => rw [hsplit, prod_range_add, prod_range_succ]
    simp only [Nat.sub_add_cancel hr]
  rw [hprod]
  have hleft :
      (1 / 2 : ℝ) ^ (r - 1) * (r - 1).factorial ≤
        ∏ i ∈ range (r - 1), ‖z - ((i + 1 : ℕ) : ℂ)‖ := by
    rw [show (1 / 2 : ℝ) ^ (r - 1) * (r - 1).factorial =
      ∏ i ∈ range (r - 1), (((r - (i + 1) : ℕ) : ℝ) / 2) by
        simp_rw [div_eq_mul_inv]
        rw [prod_mul_distrib]
        have hprodsub :
            (∏ i ∈ range (r - 1), ((r - (i + 1) : ℕ) : ℝ)) =
              ∏ i ∈ range (r - 1), (((r - 1) - i : ℕ) : ℝ) := by
          apply prod_congr rfl
          intro i hi
          have hi' := mem_range.mp hi
          exact_mod_cast (show r - (i + 1) = (r - 1) - i by omega)
        rw [hprodsub, prod_range_cast_sub_eq_factorial]
        simp [mul_comm]]
    apply prod_le_prod
    · intro i hi
      positivity
    · intro i hi
      exact localCircle_left_factor_lower (mem_range.mp hi) hz
  have hright :
      (1 / 2 : ℝ) ^ (R - r) * (R - r).factorial ≤
        ∏ j ∈ range (R - r), ‖z - ((r + j + 1 : ℕ) : ℂ)‖ := by
    rw [show (1 / 2 : ℝ) ^ (R - r) * (R - r).factorial =
      ∏ j ∈ range (R - r), (((j + 1 : ℕ) : ℝ) / 2) by
        simp_rw [div_eq_mul_inv]
        rw [prod_mul_distrib, prod_range_cast_add_one_eq_factorial]
        simp [mul_comm]]
    apply prod_le_prod
    · intro i hi
      positivity
    · intro i hi
      exact localCircle_right_factor_lower hz
  have hcenter : ‖z - (r : ℂ)‖ = (1 / 2 : ℝ) := hz
  have hpow :
      (1 / 2 : ℝ) ^ R =
        (1 / 2 : ℝ) ^ (r - 1) * (1 / 2) *
          (1 / 2 : ℝ) ^ (R - r) := by
    calc
      (1 / 2 : ℝ) ^ R = (1 / 2 : ℝ) ^ ((r - 1) + 1 + (R - r)) := by
        exact congrArg (fun n : ℕ ↦ (1 / 2 : ℝ) ^ n) (by omega)
      _ = _ := by rw [pow_add, pow_add]; ring
  calc
    (1 / 2 : ℝ) ^ R * (r - 1).factorial * (R - r).factorial =
        ((1 / 2 : ℝ) ^ (r - 1) * (r - 1).factorial) * (1 / 2) *
          ((1 / 2 : ℝ) ^ (R - r) * (R - r).factorial) := by
      rw [hpow]
      ring
    _ ≤ (∏ i ∈ range (r - 1), ‖z - ((i + 1 : ℕ) : ℂ)‖) *
          ‖z - (r : ℂ)‖ *
          (∏ j ∈ range (R - r),
            ‖z - ((r + j + 1 : ℕ) : ℂ)‖) := by
      rw [hcenter]
      exact mul_le_mul (mul_le_mul hleft le_rfl (by positivity) (by positivity))
        hright (by positivity) (by positivity)

theorem nat_le_two_pow_for_localCircle (n : ℕ) : n ≤ 2 ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [pow_succ]
      calc
        n + 1 ≤ 2 ^ n + 2 ^ n := Nat.add_le_add ih Nat.one_le_two_pow
        _ = 2 ^ n * 2 := by ring

/-- The consecutive numerator is exactly a falling factorial. -/
theorem localCircle_numerator_eq {R l : ℕ} (hRl : R < l) :
    (∏ i ∈ range R, ‖(l : ℂ) - ((i + 1 : ℕ) : ℂ)‖) =
      (R.factorial : ℝ) * (Nat.choose (l - 1) R : ℕ) := by
  calc
    (∏ i ∈ range R, ‖(l : ℂ) - ((i + 1 : ℕ) : ℂ)‖) =
        ∏ i ∈ range R, ((l - (i + 1) : ℕ) : ℝ) := by
      apply prod_congr rfl
      intro i hi
      have hil : i + 1 ≤ l := by
        have hiR := mem_range.mp hi
        omega
      rw [show (l : ℂ) - ((i + 1 : ℕ) : ℂ) =
          (((l - (i + 1) : ℕ) : ℝ) : ℂ) by
        norm_num [Nat.cast_sub hil]]
      simp
    _ = ((l - 1).descFactorial R : ℕ) := by
      norm_cast
      rw [Nat.descFactorial_eq_prod_range]
      apply prod_congr rfl
      intro i hi
      have hiR := mem_range.mp hi
      exact show l - (i + 1) = (l - 1) - i by omega
    _ = (R.factorial : ℝ) * (Nat.choose (l - 1) R : ℕ) := by
      norm_cast
      exact Nat.descFactorial_eq_factorial_mul_choose (l - 1) R

theorem factorial_le_localCircle_factor_times_pow {R r : ℕ}
    (hr : 1 ≤ r) (hrR : r ≤ R) :
    (R.factorial : ℝ) ≤
      (2 : ℝ) ^ (2 * R) * (r - 1).factorial * (R - r).factorial := by
  have hRm1 : r - 1 ≤ R - 1 := by omega
  have hfacNat := Nat.choose_mul_factorial_mul_factorial hRm1
  have hsub : (R - 1) - (r - 1) = R - r := by omega
  rw [hsub] at hfacNat
  have hfac : (R.factorial : ℝ) =
      (R : ℝ) * (Nat.choose (R - 1) (r - 1) : ℕ) *
        (r - 1).factorial * (R - r).factorial := by
    norm_cast
    calc
      R.factorial = R * (R - 1).factorial := by
        exact (Nat.mul_factorial_pred (show R ≠ 0 by omega)).symm
      _ = R * ((R - 1).choose (r - 1) * (r - 1).factorial *
          (R - r).factorial) := by rw [hfacNat]
      _ = _ := by ring
  rw [hfac]
  have hRpow : (R : ℝ) ≤ (2 : ℝ) ^ R := by
    exact_mod_cast nat_le_two_pow_for_localCircle R
  have hchoose : ((R - 1).choose (r - 1) : ℝ) ≤
      (2 : ℝ) ^ (R - 1) := by
    exact_mod_cast Nat.choose_le_two_pow (R - 1) (r - 1)
  have hpow : (2 : ℝ) ^ R * (2 : ℝ) ^ (R - 1) ≤
      (2 : ℝ) ^ (2 * R) := by
    rw [← pow_add]
    exact pow_le_pow_right₀ (by norm_num) (by omega)
  calc
    (R : ℝ) * (R - 1).choose (r - 1) * (r - 1).factorial *
        (R - r).factorial ≤
      ((2 : ℝ) ^ R * (2 : ℝ) ^ (R - 1)) *
        (r - 1).factorial * (R - r).factorial := by gcongr
    _ ≤ (2 : ℝ) ^ (2 * R) *
        (r - 1).factorial * (R - r).factorial := by gcongr

theorem localCircle_numerator_upper {R r l : ℕ}
    (hr : 1 ≤ r) (hrR : r ≤ R) (hRl : R < l) :
    (∏ i ∈ range R, ‖(l : ℂ) - ((i + 1 : ℕ) : ℂ)‖) ≤
      (2 : ℝ) ^ (2 * R + l) * (r - 1).factorial *
        (R - r).factorial := by
  rw [localCircle_numerator_eq hRl]
  have hc : ((Nat.choose (l - 1) R : ℕ) : ℝ) ≤ (2 : ℝ) ^ l := by
    have hc' := Nat.choose_le_two_pow (l - 1) R
    exact_mod_cast hc'.trans
      (Nat.pow_le_pow_right (by omega) (show l - 1 ≤ l by omega))
  calc
    (R.factorial : ℝ) * (Nat.choose (l - 1) R : ℕ) ≤
        ((2 : ℝ) ^ (2 * R) * (r - 1).factorial *
          (R - r).factorial) * (2 : ℝ) ^ l := by
      gcongr
      exact factorial_le_localCircle_factor_times_pow hr hrR
    _ = _ := by rw [pow_add]; ring

/-- Source equation (9), unpowered: the factorials in the small-circle
denominator cancel those in the consecutive-node numerator. -/
theorem localCircle_nodal_base_ratio_bound {R r l : ℕ}
    (hr : 1 ≤ r) (hrR : r ≤ R) (hRl : R < l)
    {z : ℂ} (hz : ‖z - (r : ℂ)‖ = 1 / 2) :
    ‖(∏ i ∈ range R, ((l : ℂ) - ((i + 1 : ℕ) : ℂ))) /
        (∏ i ∈ range R, (z - ((i + 1 : ℕ) : ℂ)))‖ ≤
      (2 : ℝ) ^ (3 * R + l) := by
  rw [norm_div, norm_prod, norm_prod]
  have hden := localCircle_denominator_lower hr hrR hz
  have hden0 : 0 < ∏ i ∈ range R, ‖z - ((i + 1 : ℕ) : ℂ)‖ := by
    have hbase : 0 < (1 / 2 : ℝ) ^ R * (r - 1).factorial *
        (R - r).factorial := by positivity
    exact hbase.trans_le hden
  rw [div_le_iff₀ hden0]
  have hnum := localCircle_numerator_upper hr hrR hRl
  calc
    ∏ x ∈ range R, ‖(l : ℂ) - ((x + 1 : ℕ) : ℂ)‖ ≤
        (2 : ℝ) ^ (2 * R + l) * (r - 1).factorial *
          (R - r).factorial := hnum
    _ = (2 : ℝ) ^ (3 * R + l) *
        ((1 / 2 : ℝ) ^ R * (r - 1).factorial *
          (R - r).factorial) := by
      rw [show (1 / 2 : ℝ) ^ R = ((2 : ℝ) ^ R)⁻¹ by
        rw [one_div, inv_pow]]
      rw [show 3 * R + l = (2 * R + l) + R by omega, pow_add]
      field_simp
      rw [← pow_add, ← pow_add]
    _ ≤ (2 : ℝ) ^ (3 * R + l) *
        ∏ i ∈ range R, ‖z - ((i + 1 : ℕ) : ℂ)‖ := by
      gcongr

/-- Source equation (9), with the exact Hermite multiplicity.  Its exponent
is linear in `R` and `l`, so in particular it introduces no `log h` loss. -/
theorem localCircle_nodal_ratio_bound {R S r l : ℕ}
    (hr : 1 ≤ r) (hrR : r ≤ R) (hRl : R < l)
    {z : ℂ} (hz : ‖z - (r : ℂ)‖ = 1 / 2) :
    ‖(∏ i ∈ range R, ((l : ℂ) - ((i + 1 : ℕ) : ℂ)) ^ S) /
        (∏ i ∈ range R, (z - ((i + 1 : ℕ) : ℂ)) ^ S)‖ ≤
      (2 : ℝ) ^ ((3 * R + l) * S) := by
  rw [Finset.prod_pow, Finset.prod_pow, ← div_pow, norm_pow, pow_mul]
  exact pow_le_pow_left₀ (norm_nonneg _)
    (localCircle_nodal_base_ratio_bound hr hrR hRl hz) S

/-- The local residue kernel occurring in source equation (9). -/
def localCircleKernel (R S r l m : ℕ) (z : ℂ) : ℂ :=
  ((∏ i ∈ range R, ((l : ℂ) - ((i + 1 : ℕ) : ℂ)) ^ S) /
      (∏ i ∈ range R, (z - ((i + 1 : ℕ) : ℂ)) ^ S) *
    (z - (r : ℂ)) ^ m) / (z - (l : ℂ))

/-- After the radius `1/2` of the contour cancels the elementary
`1/2` lower bound for `|z-l|`, every normalized local integral is bounded
by the factorial nodal quotient alone. -/
theorem norm_normalized_localCircleKernel_integral_le
    {R S r l m : ℕ} (hr : 1 ≤ r) (hrR : r ≤ R) (hRl : R < l) :
    ‖(2 * Real.pi * I : ℂ)⁻¹ *
        ∮ z in C((r : ℂ), (1 / 2 : ℝ)), localCircleKernel R S r l m z‖ ≤
      (2 : ℝ) ^ ((3 * R + l) * S) := by
  have hkernel : ∀ z ∈ sphere (r : ℂ) (1 / 2 : ℝ),
      ‖localCircleKernel R S r l m z‖ ≤
        2 * (2 : ℝ) ^ ((3 * R + l) * S) := by
    intro z hz
    have hzhalf : ‖z - (r : ℂ)‖ = (1 / 2 : ℝ) := by
      simpa [mem_sphere, dist_eq_norm] using hz
    have hratio := localCircle_nodal_ratio_bound (S := S) hr hrR hRl hzhalf
    have hcentres : (1 : ℝ) ≤ ‖(l : ℂ) - (r : ℂ)‖ := by
      rw [show (l : ℂ) - (r : ℂ) = (((l - r : ℕ) : ℝ) : ℂ) by
        norm_num [Nat.cast_sub (Nat.le_of_lt (hrR.trans_lt hRl))]]
      simp only [Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (show (0 : ℝ) ≤ ((l - r : ℕ) : ℝ) by positivity)]
      exact_mod_cast (show 1 ≤ l - r by omega)
    have htriangle : ‖(l : ℂ) - (r : ℂ)‖ ≤
        ‖z - (l : ℂ)‖ + ‖z - (r : ℂ)‖ := by
      calc
        ‖(l : ℂ) - (r : ℂ)‖ =
            ‖((l : ℂ) - z) - ((r : ℂ) - z)‖ := by
          congr 1 <;> ring
        _ ≤ ‖(l : ℂ) - z‖ + ‖(r : ℂ) - z‖ := norm_sub_le _ _
        _ = ‖(l : ℂ) - z‖ + ‖z - (r : ℂ)‖ := by
          rw [norm_sub_rev (r : ℂ) z]
        _ = ‖z - (l : ℂ)‖ + ‖z - (r : ℂ)‖ := by
          rw [norm_sub_rev]
    have htarget : (1 / 2 : ℝ) ≤ ‖z - (l : ℂ)‖ := by
      rw [hzhalf] at htriangle
      norm_num at htriangle ⊢
      linarith
    have hpowSmall : ‖(z - (r : ℂ)) ^ m‖ ≤ 1 := by
      rw [norm_pow, hzhalf]
      exact pow_le_one₀ (by norm_num : (0 : ℝ) ≤ 1 / 2)
        (by norm_num : (1 / 2 : ℝ) ≤ 1)
    rw [localCircleKernel, norm_div, norm_mul]
    calc
      ‖((∏ i ∈ range R, ((l : ℂ) - ((i + 1 : ℕ) : ℂ)) ^ S) /
          (∏ i ∈ range R, (z - ((i + 1 : ℕ) : ℂ)) ^ S))‖ *
            ‖(z - (r : ℂ)) ^ m‖ / ‖z - (l : ℂ)‖ ≤
          ((2 : ℝ) ^ ((3 * R + l) * S) * 1) / (1 / 2) := by
        exact div_le_div₀ (by positivity)
          (mul_le_mul hratio hpowSmall (norm_nonneg _) (by positivity))
          (by norm_num) htarget
      _ = 2 * (2 : ℝ) ^ ((3 * R + l) * S) := by ring
  have hIntegral :=
    circleIntegral.norm_two_pi_i_inv_smul_integral_le_of_norm_le_const
      (show (0 : ℝ) ≤ 1 / 2 by norm_num) hkernel
  simpa [smul_eq_mul] using hIntegral

/-- The complete double sum of local corrections in equation (9).  The
number `R*S` of summands is absorbed into one additional power of two, so
the exponent remains linear in the interpolation radius. -/
theorem norm_sum_normalized_localCircleKernel_integral_le
    {R S l : ℕ} (hRl : R < l) {delta : ℝ} (hdelta : 0 ≤ delta)
    (c : Fin R → Fin S → ℂ)
    (hc : ∀ r m, ‖c r m‖ ≤ delta) :
    ‖∑ r : Fin R, ∑ m : Fin S, c r m *
        ((2 * Real.pi * I : ℂ)⁻¹ *
          ∮ z in C(((r.1 + 1 : ℕ) : ℂ), (1 / 2 : ℝ)),
            localCircleKernel R S (r.1 + 1) l m.1 z)‖ ≤
      (2 : ℝ) ^ (((3 * R + l) * S) + R * S) * delta := by
  have hterm : ∀ r : Fin R, ∀ m : Fin S,
      ‖c r m *
        ((2 * Real.pi * I : ℂ)⁻¹ *
          ∮ z in C(((r.1 + 1 : ℕ) : ℂ), (1 / 2 : ℝ)),
            localCircleKernel R S (r.1 + 1) l m.1 z)‖ ≤
        delta * (2 : ℝ) ^ ((3 * R + l) * S) := by
    intro r m
    rw [norm_mul]
    apply mul_le_mul (hc r m)
      (norm_normalized_localCircleKernel_integral_le
        (show 1 ≤ r.1 + 1 by omega)
        (show r.1 + 1 ≤ R by omega) hRl)
      (norm_nonneg _) hdelta
  calc
    ‖∑ r : Fin R, ∑ m : Fin S, c r m *
        ((2 * Real.pi * I : ℂ)⁻¹ *
          ∮ z in C(((r.1 + 1 : ℕ) : ℂ), (1 / 2 : ℝ)),
            localCircleKernel R S (r.1 + 1) l m.1 z)‖ ≤
        ∑ r : Fin R, ∑ m : Fin S,
          ‖c r m *
            ((2 * Real.pi * I : ℂ)⁻¹ *
              ∮ z in C(((r.1 + 1 : ℕ) : ℂ), (1 / 2 : ℝ)),
                localCircleKernel R S (r.1 + 1) l m.1 z)‖ := by
      exact (norm_sum_le _ _).trans (sum_le_sum fun r _ ↦ norm_sum_le _ _)
    _ ≤ ∑ _r : Fin R, ∑ _m : Fin S,
        delta * (2 : ℝ) ^ ((3 * R + l) * S) := by
      gcongr with r _ m _
      exact hterm r m
    _ = (R * S : ℕ) *
        (delta * (2 : ℝ) ^ ((3 * R + l) * S)) := by
      simp
      ring
    _ ≤ (2 : ℝ) ^ (R * S) *
        (delta * (2 : ℝ) ^ ((3 * R + l) * S)) := by
      gcongr
      exact_mod_cast nat_le_two_pow_for_localCircle (R * S)
    _ = (2 : ℝ) ^ (((3 * R + l) * S) + R * S) * delta := by
      rw [pow_add]
      ring

/-- Source equation (9) with an arbitrary local-contour loss.  The
factorial cancellation gives the exact exponent `B`, rather than forcing
the later specialization `B = A / 6`.  This form retains the strict
exponential slack needed when the nonzero outer-circle remainder is added
to the local residues. -/
theorem norm_sum_normalized_localCircleKernel_integral_le_exp_add
    {R S l : ℕ} (hRl : R < l) {A B delta : ℝ}
    (hdelta : 0 ≤ delta) (hsmall : delta ≤ Real.exp (-(2 / 3) * A))
    (hcontour :
      (2 : ℝ) ^ (((3 * R + l) * S) + R * S) ≤ Real.exp B)
    (c : Fin R → Fin S → ℂ)
    (hc : ∀ r m, ‖c r m‖ ≤ delta) :
    ‖∑ r : Fin R, ∑ m : Fin S, c r m *
        ((2 * Real.pi * I : ℂ)⁻¹ *
          ∮ z in C(((r.1 + 1 : ℕ) : ℂ), (1 / 2 : ℝ)),
            localCircleKernel R S (r.1 + 1) l m.1 z)‖ ≤
      Real.exp (-(2 / 3) * A + B) := by
  calc
    ‖∑ r : Fin R, ∑ m : Fin S, c r m *
        ((2 * Real.pi * I : ℂ)⁻¹ *
          ∮ z in C(((r.1 + 1 : ℕ) : ℂ), (1 / 2 : ℝ)),
            localCircleKernel R S (r.1 + 1) l m.1 z)‖ ≤
        (2 : ℝ) ^ (((3 * R + l) * S) + R * S) * delta :=
      norm_sum_normalized_localCircleKernel_integral_le hRl hdelta c hc
    _ ≤ Real.exp B * Real.exp (-(2 / 3) * A) := by
      exact mul_le_mul hcontour hsmall hdelta (by positivity)
    _ = Real.exp (-(2 / 3) * A + B) := by
      rw [← Real.exp_add]
      congr 1
      ring

/-- Source equation (9) in exponential form.  A `2/3`-exponent jet bound
and a `1/6`-exponent factorial-contour loss leave the required `1/2`
exponent. -/
theorem norm_sum_normalized_localCircleKernel_integral_le_exp
    {R S l : ℕ} (hRl : R < l) {A delta : ℝ} (hA : 0 ≤ A)
    (hdelta : 0 ≤ delta) (hsmall : delta ≤ Real.exp (-(2 / 3) * A))
    (hcontour :
      (2 : ℝ) ^ (((3 * R + l) * S) + R * S) ≤
        Real.exp ((1 / 6) * A))
    (c : Fin R → Fin S → ℂ)
    (hc : ∀ r m, ‖c r m‖ ≤ delta) :
    ‖∑ r : Fin R, ∑ m : Fin S, c r m *
        ((2 * Real.pi * I : ℂ)⁻¹ *
          ∮ z in C(((r.1 + 1 : ℕ) : ℂ), (1 / 2 : ℝ)),
            localCircleKernel R S (r.1 + 1) l m.1 z)‖ ≤
      Real.exp (-(1 / 2) * A) := by
  calc
    ‖∑ r : Fin R, ∑ m : Fin S, c r m *
        ((2 * Real.pi * I : ℂ)⁻¹ *
          ∮ z in C(((r.1 + 1 : ℕ) : ℂ), (1 / 2 : ℝ)),
            localCircleKernel R S (r.1 + 1) l m.1 z)‖ ≤
        (2 : ℝ) ^ (((3 * R + l) * S) + R * S) * delta :=
      norm_sum_normalized_localCircleKernel_integral_le hRl hdelta c hc
    _ ≤ Real.exp ((1 / 6) * A) * Real.exp (-(2 / 3) * A) := by
      exact mul_le_mul hcontour hsmall hdelta
        (by positivity)
    _ = Real.exp (-(1 / 2) * A) := by
      rw [← Real.exp_add]
      congr 1
      ring

/-! ### The literal integral-grid extrapolation step -/

/-- Every member of the repeated integral-node list is one of the integers
`1, ..., R`. -/
theorem mem_integralNodes_iff {R S : ℕ} {a : ℂ} :
    a ∈ integralNodes R S ↔
      ∃ i < R, S ≠ 0 ∧ a = ((i + 1 : ℕ) : ℂ) := by
  simp [integralNodes]

/-- Exact pointwise integral extrapolation with no assumed upper bound on
the Hermite polynomial.  Its two polynomial estimates are consequences of
the normalized input jets, and the boundary and target nodal products are
the literal `(2*Rnext)^(R*S)` and `Rnext^(R*S)` estimates.

This is the analytic endpoint of one source Lemma 4 recursion step.  The
arithmetic construction supplies `hsmall`, the boundary growth estimate,
and the Liouville alternative. -/
theorem integral_grid_extrapolation_pointwise
    {f g : ℂ → ℂ} (hf : Differentiable ℂ f)
    {Rold Rnext S l : ℕ} (hRnext : 0 < Rnext)
    (hRold : Rold ≤ Rnext) (hl : l ≤ Rnext)
    {F delta lower : ℝ} (hF : 0 ≤ F) (hdelta : 0 ≤ delta)
    (hsmall : ∀ i : Fin Rold, ∀ k : Fin S,
      ‖iteratedDeriv k.1 f ((i.1 + 1 : ℕ) : ℂ) /
        (k.1.factorial : ℂ)‖ ≤ delta)
    (hboundary : ∀ w : ℂ,
      ‖w‖ = 3 * (Rnext : ℝ) → ‖f w‖ ≤ F)
    (hliouville : g (l : ℂ) = 0 ∨ lower ≤ ‖f (l : ℂ)‖)
    (hbudget :
      sharpHasseEvaluationBound Rold S (3 * (Rnext : ℝ)) * delta +
        (Rnext : ℝ) ^ (Rold * S) *
          ((3 * (Rnext : ℝ)) *
            (((F + sharpHasseEvaluationBound Rold S
                (3 * (Rnext : ℝ)) * delta) /
                (2 * (Rnext : ℝ)) ^ (Rold * S)) /
              (3 * (Rnext : ℝ) - l))) < lower) :
    g (l : ℂ) = 0 := by
  let nodes := integralNodes Rold S
  let radius : ℝ := 3 * (Rnext : ℝ)
  let H : ℝ := sharpHasseEvaluationBound Rold S radius * delta
  let D : ℝ := (2 * (Rnext : ℝ)) ^ (Rold * S)
  have hradius : 0 < radius := by
    dsimp [radius]
    positivity
  have hrho : 1 ≤ radius := by
    dsimp [radius]
    have hRn : (1 : ℝ) ≤ Rnext := by exact_mod_cast hRnext
    linarith
  have hH : 0 ≤ H := mul_nonneg
    (sharpHasseEvaluationBound_nonneg Rold S hradius.le) hdelta
  have hD : 0 < D := by
    dsimp [D]
    positivity
  have htargetBall : (l : ℂ) ∈ ball 0 radius := by
    rw [mem_ball, dist_zero_right]
    simp only [Complex.norm_natCast]
    have hl' : (l : ℝ) ≤ Rnext := by exact_mod_cast hl
    dsimp [radius]
    have hRn : (0 : ℝ) < Rnext := by exact_mod_cast hRnext
    linarith
  have hnodes : ∀ a ∈ nodes, a ∈ ball (0 : ℂ) radius := by
    intro a ha
    rcases mem_integralNodes_iff.mp ha with ⟨i, hi, hS, rfl⟩
    rw [mem_ball, dist_zero_right, Complex.norm_natCast]
    have hiR : i + 1 ≤ Rold := by omega
    have hir : (i + 1 : ℝ) ≤ Rnext := by exact_mod_cast hiR.trans hRold
    have hRn : (0 : ℝ) < Rnext := by exact_mod_cast hRnext
    change ((i + 1 : ℕ) : ℝ) < radius
    have hstrict : (Rnext : ℝ) < radius := by
      change (Rnext : ℝ) < 3 * (Rnext : ℝ)
      linarith
    simpa only [Nat.cast_add, Nat.cast_one] using hir.trans_lt hstrict
  have hpolyTarget :
      ‖(polynomial f nodes).eval (l : ℂ)‖ ≤ H := by
    apply norm_polynomial_integralNodes_eval_le_sharp_of_small_normalized_jets
      hf hradius.le _ hdelta hsmall
    simp only [Complex.norm_natCast]
    have hl' : (l : ℝ) ≤ Rnext := by exact_mod_cast hl
    have hRn : (0 : ℝ) ≤ Rnext := by positivity
    dsimp [radius]
    linarith
  have hpolyBoundary : ∀ w ∈ sphere (0 : ℂ) radius,
      ‖(polynomial f nodes).eval w‖ ≤ H := by
    intro w hw
    apply norm_polynomial_integralNodes_eval_le_sharp_of_small_normalized_jets
      hf hradius.le _ hdelta hsmall
    rw [mem_sphere, dist_zero_right] at hw
    exact hw.le
  have hboundaryF : ∀ w ∈ sphere (0 : ℂ) radius, ‖f w‖ ≤ F := by
    intro w hw
    apply hboundary w
    simpa [mem_sphere, dist_zero_right, radius] using hw
  have hboundaryProduct : ∀ w ∈ sphere (0 : ℂ) radius,
      D ≤ nodeProductNorm nodes w := by
    intro w hw
    rw [← norm_nodeProduct, hermite_nodeProduct_integralNodes]
    unfold integralNodalProduct
    have hp := pow_card_le_norm_prod_pow
      (s := Finset.range Rold) (f := fun i ↦ w - (i + 1 : ℕ))
      (B := 2 * (Rnext : ℝ)) S (by positivity) (by
        intro i hi
        apply two_mul_le_norm_sub_natCast_of_norm_eq_three_mul
          (show i + 1 ≤ Rnext by
            exact (show i + 1 ≤ Rold by
              exact Nat.succ_le_iff.mpr (Finset.mem_range.mp hi)).trans hRold)
        simpa [mem_sphere, dist_zero_right, radius] using hw)
    simpa only [Finset.card_range, D] using hp
  have htargetProduct :
      nodeProductNorm nodes (l : ℂ) ≤ (Rnext : ℝ) ^ (Rold * S) := by
    rw [← norm_nodeProduct, hermite_nodeProduct_integralNodes]
    unfold integralNodalProduct
    have hp := norm_prod_pow_le_pow
      (s := Finset.range Rold) (f := fun i ↦ (l : ℂ) - (i + 1 : ℕ))
      (A := (Rnext : ℝ)) S (by positivity) (by
        intro i hi
        exact norm_natCast_sub_natCast_le hl
          (show i + 1 ≤ Rnext by
            exact (show i + 1 ≤ Rold by
              exact Nat.succ_le_iff.mpr (Finset.mem_range.mp hi)).trans hRold))
    simpa only [Finset.card_range] using hp
  have hgap : 0 < radius - dist (l : ℂ) 0 := by
    exact sub_pos.mpr (by simpa [dist_zero_right] using htargetBall)
  have hfactor : 0 ≤ radius * (((F + H) / D) /
      (radius - dist (l : ℂ) 0)) := by
    exact mul_nonneg hradius.le
      (div_nonneg (div_nonneg (add_nonneg hF hH) hD.le) hgap.le)
  apply Erdos240.BakerIntegralExtrapolation.vdpl_integral_extrapolation_step_of_boundary_bounds
    hf nodes hradius htargetBall hF hH hD hnodes hboundaryF hpolyBoundary
      hboundaryProduct hpolyTarget
  · calc
      H + nodeProductNorm nodes (l : ℂ) *
          (radius * (((F + H) / D) /
            (radius - dist (l : ℂ) 0))) ≤
        H + (Rnext : ℝ) ^ (Rold * S) *
          (radius * (((F + H) / D) /
            (radius - dist (l : ℂ) 0))) := by
              gcongr
      _ < lower := by
        simpa [H, D, radius, dist_zero_right, Complex.norm_natCast] using hbudget
  · exact hliouville

/-- Finite-grid source wrapper.  It starts from the exact level-`J`
vanishing assertion, asks for the normalized jet consequence of that seed
(equations (7)--(8) in the source), and concludes at the literal radius
`R (J+1)` and budget `Sstep J`.

All numerical assumptions are displayed closed-form inequalities involving
`sharpHasseEvaluationBound`; there is no hypothesis asserting a bound for
an interpolation polynomial. -/
theorem integral_grid_extrapolation_Slevel_to_Sstep
    {ι : Type*} [Fintype ι] (P : VDPLParameters ι) (J T : ℕ)
    {F G : ℂ → VDPLMultiIndex P.rank → ℂ}
    (outer jet lower : ℕ → VDPLMultiIndex P.rank → ℝ)
    (hseed : VanishesOn G 1 (P.R J) (P.Slevel J))
    (hFdiff : ∀ m, Differentiable ℂ (fun z ↦ F z m))
    (houter_nonneg : ∀ l m, 0 ≤ outer l m)
    (hjet_nonneg : ∀ l m, 0 ≤ jet l m)
    (hjetsOfSeed :
      VanishesOn G 1 (P.R J) (P.Slevel J) →
        ∀ l, 1 ≤ l → l ≤ P.R (J + 1) →
          ∀ m, VDPLMultiIndex.weight m ≤ P.Sstep J →
            ∀ i : Fin (P.R J), ∀ k : Fin T,
              ‖iteratedDeriv k.1 (fun z ↦ F z m)
                  ((i.1 + 1 : ℕ) : ℂ) /
                (k.1.factorial : ℂ)‖ ≤ jet l m)
    (hboundary : ∀ l, 1 ≤ l → l ≤ P.R (J + 1) →
      ∀ m, VDPLMultiIndex.weight m ≤ P.Sstep J →
        ∀ w : ℂ, ‖w‖ = 3 * (P.R (J + 1) : ℝ) →
          ‖F w m‖ ≤ outer l m)
    (hliouville : ∀ l, 1 ≤ l → l ≤ P.R (J + 1) →
      ∀ m, VDPLMultiIndex.weight m ≤ P.Sstep J →
        G (l : ℂ) m = 0 ∨ lower l m ≤ ‖F (l : ℂ) m‖)
    (hbudget : ∀ l, 1 ≤ l → l ≤ P.R (J + 1) →
      ∀ m, VDPLMultiIndex.weight m ≤ P.Sstep J →
        sharpHasseEvaluationBound (P.R J) T
              (3 * (P.R (J + 1) : ℝ)) * jet l m +
          (P.R (J + 1) : ℝ) ^ (P.R J * T) *
            ((3 * (P.R (J + 1) : ℝ)) *
              (((outer l m + sharpHasseEvaluationBound (P.R J) T
                    (3 * (P.R (J + 1) : ℝ)) * jet l m) /
                  (2 * (P.R (J + 1) : ℝ)) ^ (P.R J * T)) /
                (3 * (P.R (J + 1) : ℝ) - l))) < lower l m) :
    VanishesOn G 1 (P.R (J + 1)) (P.Sstep J) := by
  intro l hl hlR m hm
  simp only [Nat.cast_one, div_one]
  apply integral_grid_extrapolation_pointwise
    (f := fun z ↦ F z m) (g := fun z ↦ G z m) (hFdiff m)
    (P.R_pos (J + 1))
    (P.R_mono (Nat.le_succ J)) hlR
    (houter_nonneg l m) (hjet_nonneg l m)
    (hjetsOfSeed hseed l hl hlR m hm)
    (hboundary l hl hlR m hm)
    (hliouville l hl hlR m hm)
    (hbudget l hl hlR m hm)

/-! ### Corrected source-state specialization -/

/-- Half of the explicit Liouville lower bound in concrete Lemma 3. -/
def lemmaFourCertificateLower
    {oldRank : ℕ} {I K : Type*} [Field K] [NumberField K]
    {coord : SourceCoordinates oldRank I} {support : Finset I} {p : I → ℤ}
    {h : ℕ} {b : Fin oldRank → ℤ} {bLast : ℤ}
    {logAlpha : Fin oldRank → ℂ} {logAlphaLast : ℂ}
    {q N : ℕ} {z : ℂ} {m : VDPLMultiIndex (oldRank + 1)} {radicalRank : ℕ}
    (A : AlgebraicCertificateInputs (K := K) coord support p h b bLast
      logAlpha logAlphaLast q N z m radicalRank) : ℝ :=
  ((A.conjugateBound ^ (13 ^ radicalRank - 1))⁻¹ / ‖A.scale‖) / 2

/-- Entirety of the corrected split-scaled source auxiliary function. -/
theorem differentiable_vdplF_for_lemma4
    {oldRank : ℕ} {I : Type*}
    (coord : SourceCoordinates oldRank I) (support : Finset I) (p : I → ℤ)
    (h : ℕ) (b : Fin oldRank → ℤ) (bLast : ℤ)
    (logAlpha : Fin oldRank → ℂ) (q N : ℕ)
    (m : VDPLMultiIndex (oldRank + 1)) :
    Differentiable ℂ
      (fun z ↦ vdplF coord support p h b bLast logAlpha q N z m) := by
  classical
  simp only [vdplF, ExponentialPolynomial.ordinaryDerivative, pow_zero, mul_one,
    sourceCoefficient, auxiliaryFactor, scaledArgument, poweredDeltaHasseEval,
    Polynomial.eval₂_eq_eval_map]
  fun_prop

/-- The corrected source-state analytic family is entire.  Only its Delta
factor sees `z/q^N`; the exponential in `f` retains the unscaled variable,
as required by the source. -/
theorem differentiable_sourceState_f
    {oldRank : ℕ} {P : VDPLParameters (Fin oldRank)} {N : ℕ}
    (state : LevelState P N) (b : Fin oldRank → ℤ) (bLast : ℤ)
    (m : VDPLMultiIndex P.rank) :
    Differentiable ℂ (fun z ↦ BakerSourceState.f state b bLast z m) := by
  change Differentiable ℂ (fun z ↦
    vdplF (coordinatesForState state) state.support state.coeff P.h b bLast
      (oldLog P) P.q N z (toSourceMultiIndex P m))
  exact differentiable_vdplF_for_lemma4 (coordinatesForState state) state.support state.coeff P.h b bLast
    (oldLog P) P.q N (toSourceMultiIndex P m)

/-- Concrete source Lemma 4 endpoint for the corrected coefficient state.

The seed is the literal `Slevel N` integral vanishing assertion and the
conclusion is the literal `R (N+1), Sstep N` assertion.  The source's inner
equations (7)--(8) are isolated as `hjetsOfSeed`: critically, they bound
normalized derivatives.  Function growth and the target lower alternative
are not assumptions about `f` and `g`; they are derived from concrete Lemma
3 majorants and certificates. -/
theorem sourceState_lemma4_Slevel_to_Sstep
    {oldRank : ℕ} {K : Type*} [Field K] [NumberField K]
    (P : VDPLParameters (Fin oldRank)) (N T : ℕ)
    (state : LevelState P N) (b : Fin oldRank → ℤ) (bLast : ℤ)
    (outer jet : ℕ → VDPLMultiIndex P.rank → ℝ)
    (hseed : VanishesOn (BakerSourceState.g state b bLast)
      1 (P.R N) (P.Slevel N))
    (houter_nonneg : ∀ l m, 0 ≤ outer l m)
    (hjet_nonneg : ∀ l m, 0 ≤ jet l m)
    (hjetsOfSeed :
      VanishesOn (BakerSourceState.g state b bLast)
          1 (P.R N) (P.Slevel N) →
        ∀ l, 1 ≤ l → l ≤ P.R (N + 1) →
          ∀ m, VDPLMultiIndex.weight m ≤ P.Sstep N →
            ∀ i : Fin (P.R N), ∀ k : Fin T,
              ‖iteratedDeriv k.1
                  (fun z ↦ BakerSourceState.f state b bLast z m)
                  ((i.1 + 1 : ℕ) : ℂ) /
                (k.1.factorial : ℂ)‖ ≤ jet l m)
    (Mouter : ∀ (_l : ℕ) (m : VDPLMultiIndex P.rank) (w : ℂ),
      SourceMajorants P (coordinatesForState state) state.support state.coeff P.h b bLast
        (oldLog P) P.q N w (toSourceMultiIndex P m))
    (houterGrowth : ∀ l, 1 ≤ l → l ≤ P.R (N + 1) →
      ∀ m, VDPLMultiIndex.weight m ≤ P.Sstep N →
        ∀ w : ℂ, ‖w‖ = 3 * (P.R (N + 1) : ℝ) →
          (Mouter l m w).growth ≤ outer l m)
    (Mtarget : ∀ (l : ℕ) (m : VDPLMultiIndex P.rank),
      SourceMajorants P (coordinatesForState state) state.support state.coeff P.h b bLast
        (oldLog P) P.q N (l : ℂ) (toSourceMultiIndex P m))
    (Btarget : ∀ (l : ℕ) (_hl : 1 ≤ l) (_hlR : l ≤ P.R (N + 1))
      (m : VDPLMultiIndex P.rank) (_hm : VDPLMultiIndex.weight m ≤ P.Sstep N),
        SourceNumericalConditions (Mtarget l m))
    (Atarget : ∀ (l : ℕ) (m : VDPLMultiIndex P.rank),
      AlgebraicCertificateInputs (K := K) (coordinatesForState state) state.support state.coeff
        P.h b bLast (oldLog P) (lastLog P) P.q N (l : ℂ)
        (toSourceMultiIndex P m) 0)
    (hbLast : bLast ≠ 0)
    (hsmall : ∀ l (hl : 1 ≤ l) (hlR : l ≤ P.R (N + 1))
      m (hm : VDPLMultiIndex.weight m ≤ P.Sstep N),
        ‖logForm b bLast (oldLog P) (lastLog P)‖ ≤
          smallLinearFormBound P (Btarget l hl hlR m hm).sourceConstant)
    (herrorToLiouville : ∀ l (hl : 1 ≤ l) (hlR : l ≤ P.R (N + 1))
      m (hm : VDPLMultiIndex.weight m ≤ P.Sstep N),
        errorEnvelope P (Btarget l hl hlR m hm).sourceConstant
            (Btarget l hl hlR m hm).errorMultiplier ≤
          lemmaFourCertificateLower (K := K) (Atarget l m))
    (hbudget : ∀ l, 1 ≤ l → l ≤ P.R (N + 1) →
      ∀ m, VDPLMultiIndex.weight m ≤ P.Sstep N →
        sharpHasseEvaluationBound (P.R N) T
              (3 * (P.R (N + 1) : ℝ)) * jet l m +
          (P.R (N + 1) : ℝ) ^ (P.R N * T) *
            ((3 * (P.R (N + 1) : ℝ)) *
              (((outer l m + sharpHasseEvaluationBound (P.R N) T
                    (3 * (P.R (N + 1) : ℝ)) * jet l m) /
                  (2 * (P.R (N + 1) : ℝ)) ^ (P.R N * T)) /
                (3 * (P.R (N + 1) : ℝ) - l))) <
          lemmaFourCertificateLower (K := K) (Atarget l m)) :
    VanishesOn (BakerSourceState.g state b bLast)
      1 (P.R (N + 1)) (P.Sstep N) := by
  let lower : ℕ → VDPLMultiIndex P.rank → ℝ := fun l m ↦
    lemmaFourCertificateLower (K := K) (Atarget l m)
  apply integral_grid_extrapolation_Slevel_to_Sstep P N T
    outer jet lower hseed
  · exact differentiable_sourceState_f state b bLast
  · exact houter_nonneg
  · exact hjet_nonneg
  · exact hjetsOfSeed
  · intro l hl hlR m hm w hw
    change ‖vdplF (coordinatesForState state) state.support state.coeff P.h b bLast
      (oldLog P) P.q N w (toSourceMultiIndex P m)‖ ≤ outer l m
    exact (Mouter l m w).norm_vdplF_le_growth.trans
      (houterGrowth l hl hlR m hm w hw)
  · intro l hl hlR m hm
    have hq := quantitative_lemma3 (Mtarget l m) (Btarget l hl hlR m hm) (Atarget l m)
      hbLast (hsmall l hl hlR m hm) (herrorToLiouville l hl hlR m hm)
    change vdplG (coordinatesForState state) state.support state.coeff P.h b bLast
        (oldLog P) (lastLog P) P.q N (l : ℂ) (toSourceMultiIndex P m) = 0 ∨
      lemmaFourCertificateLower (K := K) (Atarget l m) ≤
        ‖vdplF (coordinatesForState state) state.support state.coeff P.h b bLast
          (oldLog P) P.q N (l : ℂ) (toSourceMultiIndex P m)‖
    exact hq.2.2
  · exact hbudget

end Erdos240.BakerLemma4Concrete

#print axioms Erdos240.BakerLemma4Concrete.integral_grid_extrapolation_pointwise
#print axioms Erdos240.BakerLemma4Concrete.norm_sum_normalized_localCircleKernel_integral_le_exp_add
#print axioms Erdos240.BakerLemma4Concrete.sourceState_lemma4_Slevel_to_Sstep
