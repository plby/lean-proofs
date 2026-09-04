/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Copyright 2026 The Formal Conjectures Authors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/

import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Data.Fintype.OfMap
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Nat.Choose.Vandermonde
import Mathlib.Logic.Equiv.Fintype
import Mathlib.Logic.Equiv.Set
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Erdős Problem 88: finite Fourier tools

This file supplies the characteristic-function bookkeeping for the finite
probability spaces used in the Kwan--Sah--Sauermann--Sawhney argument.  A
finite expectation is normalized counting measure.  In particular, the
lemmas below do not rely on a choice of an ambient measure space.
-/

open scoped BigOperators

namespace Erdos88
namespace Fourier

universe u v

/-- Expectation with respect to the uniform probability measure on a
nonempty finite type. -/
noncomputable def finExpectation (Ω : Type u) [Fintype Ω] [Nonempty Ω]
    {E : Type v} [DivisionRing E] (f : Ω → E) : E :=
  (∑ ω, f ω) / (Fintype.card Ω : E)

/-- Probability with respect to the uniform measure on a nonempty finite
type. -/
noncomputable def finProbability (Ω : Type u) [Fintype Ω] [Nonempty Ω]
    (P : Ω → Prop) : ℝ := by
  classical
  exact ((Finset.univ.filter P).card : ℝ) / Fintype.card Ω

/-- The characteristic function of a real random variable on a uniform
finite probability space. -/
noncomputable def finCharFun (Ω : Type u) [Fintype Ω] [Nonempty Ω]
    (X : Ω → ℝ) (t : ℝ) : ℂ :=
  finExpectation Ω (fun ω ↦ Complex.exp ((t * X ω : ℝ) * Complex.I))

/-- The Lévy concentration function of a real random variable on a uniform
finite probability space. -/
noncomputable def finConcentration (Ω : Type u) [Fintype Ω] [Nonempty Ω]
    (X : Ω → ℝ) (eps : ℝ) : ℝ :=
  sSup (Set.range fun x : ℝ ↦ finProbability Ω (fun ω ↦ |X ω - x| ≤ eps))

lemma card_ne_zero (Ω : Type u) [Fintype Ω] [Nonempty Ω] :
    (Fintype.card Ω : ℂ) ≠ 0 := by
  exact_mod_cast Fintype.card_ne_zero

@[simp] lemma finExpectation_const (Ω : Type u) [Fintype Ω] [Nonempty Ω]
    (z : ℂ) : finExpectation Ω (fun _ ↦ z) = z := by
  simp [finExpectation]

lemma finExpectation_add (Ω : Type u) [Fintype Ω] [Nonempty Ω]
    (f g : Ω → ℂ) :
    finExpectation Ω (fun ω ↦ f ω + g ω) =
      finExpectation Ω f + finExpectation Ω g := by
  simp [finExpectation, Finset.sum_add_distrib, add_div]

lemma finExpectation_const_mul (Ω : Type u) [Fintype Ω] [Nonempty Ω]
    (z : ℂ) (f : Ω → ℂ) :
    finExpectation Ω (fun ω ↦ z * f ω) = z * finExpectation Ω f := by
  rw [finExpectation, finExpectation]
  have hsum : (∑ ω, z * f ω) = z * ∑ ω, f ω := by
    simpa using
      (Finset.mul_sum (Finset.univ : Finset Ω) f z).symm
  rw [hsum]
  ring

/-- Uniform expectation is invariant under a permutation of the finite
sample space. -/
lemma finExpectation_comp_equiv (Ω : Type u) [Fintype Ω] [Nonempty Ω]
    (e : Ω ≃ Ω) (f : Ω → ℂ) :
    finExpectation Ω (fun ω ↦ f (e ω)) = finExpectation Ω f := by
  rw [finExpectation, finExpectation, e.sum_comp]

/-- Triangle inequality for normalized counting expectation. -/
lemma norm_finExpectation_le (Ω : Type u) [Fintype Ω] [Nonempty Ω]
    (f : Ω → ℂ) :
    ‖finExpectation Ω f‖ ≤
      (∑ ω, ‖f ω‖) / Fintype.card Ω := by
  rw [finExpectation, norm_div]
  have hsum : ‖∑ ω, f ω‖ ≤ ∑ ω, ‖f ω‖ := norm_sum_le _ _
  simpa [Complex.norm_natCast] using
    (div_le_div_of_nonneg_right hsum
      (norm_nonneg (Fintype.card Ω : ℂ)))

lemma finProbability_nonneg (Ω : Type u) [Fintype Ω] [Nonempty Ω]
    (P : Ω → Prop) : 0 ≤ finProbability Ω P := by
  classical
  rw [finProbability]
  positivity

lemma finProbability_le_one (Ω : Type u) [Fintype Ω] [Nonempty Ω]
    (P : Ω → Prop) : finProbability Ω P ≤ 1 := by
  classical
  rw [finProbability, div_le_one (by exact_mod_cast Fintype.card_pos)]
  exact_mod_cast Finset.card_le_card (Finset.filter_subset P Finset.univ)

@[simp] lemma finProbability_true (Ω : Type u) [Fintype Ω] [Nonempty Ω] :
    finProbability Ω (fun _ ↦ True) = 1 := by
  classical
  rw [finProbability]
  simp [ne_of_gt (by exact_mod_cast Fintype.card_pos :
    (0 : ℝ) < Fintype.card Ω)]

@[simp] lemma finProbability_false (Ω : Type u) [Fintype Ω] [Nonempty Ω] :
    finProbability Ω (fun _ ↦ False) = 0 := by
  classical
  rw [finProbability]
  simp

lemma finProbability_mono (Ω : Type u) [Fintype Ω] [Nonempty Ω]
    {P Q : Ω → Prop} (h : ∀ ω, P ω → Q ω) :
    finProbability Ω P ≤ finProbability Ω Q := by
  classical
  rw [finProbability, finProbability,
    div_le_div_iff_of_pos_right (by exact_mod_cast Fintype.card_pos :
      (0 : ℝ) < Fintype.card Ω)]
  exact_mod_cast Finset.card_le_card (by
    intro ω hω
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hω ⊢
    exact h ω hω)

lemma finConcentration_nonneg (Ω : Type u) [Fintype Ω] [Nonempty Ω]
    (X : Ω → ℝ) (eps : ℝ) : 0 ≤ finConcentration Ω X eps := by
  let values : Set ℝ :=
    Set.range fun x : ℝ ↦ finProbability Ω (fun ω ↦ |X ω - x| ≤ eps)
  have hbdd : BddAbove values := ⟨1, by
    rintro y ⟨x, rfl⟩
    exact finProbability_le_one Ω _⟩
  have hmem : finProbability Ω (fun ω ↦ |X ω| ≤ eps) ∈ values := by
    refine ⟨0, ?_⟩
    simp
  exact (finProbability_nonneg Ω _).trans
    (le_csSup hbdd hmem)

lemma finConcentration_le_one (Ω : Type u) [Fintype Ω] [Nonempty Ω]
    (X : Ω → ℝ) (eps : ℝ) : finConcentration Ω X eps ≤ 1 := by
  apply csSup_le
  · exact Set.range_nonempty _
  rintro y ⟨x, rfl⟩
  exact finProbability_le_one Ω _

@[simp] lemma finCharFun_zero (Ω : Type u) [Fintype Ω] [Nonempty Ω]
    (X : Ω → ℝ) : finCharFun Ω X 0 = 1 := by
  simp [finCharFun]

lemma norm_finCharFun_le_one (Ω : Type u) [Fintype Ω] [Nonempty Ω]
    (X : Ω → ℝ) (t : ℝ) : ‖finCharFun Ω X t‖ ≤ 1 := by
  rw [finCharFun, finExpectation, norm_div]
  have hsum :
      ‖∑ ω, Complex.exp ((t * X ω : ℝ) * Complex.I)‖ ≤
        ∑ ω, ‖Complex.exp ((t * X ω : ℝ) * Complex.I)‖ :=
    norm_sum_le _ _
  have hnorm : ∀ ω, ‖Complex.exp ((t * X ω : ℝ) * Complex.I)‖ = 1 := by
    intro ω
    rw [Complex.norm_exp]
    simp
  simp_rw [hnorm] at hsum
  simpa [card_ne_zero] using
    (div_le_div_of_nonneg_right hsum (norm_nonneg (Fintype.card Ω : ℂ)))

lemma finCharFun_add_const (Ω : Type u) [Fintype Ω] [Nonempty Ω]
    (X : Ω → ℝ) (c t : ℝ) :
    finCharFun Ω (fun ω ↦ X ω + c) t =
      Complex.exp ((t * c : ℝ) * Complex.I) * finCharFun Ω X t := by
  rw [finCharFun, finExpectation, finCharFun, finExpectation]
  have hsum :
      (∑ ω, Complex.exp ((t * (X ω + c) : ℝ) * Complex.I)) =
        Complex.exp ((t * c : ℝ) * Complex.I) *
          ∑ ω, Complex.exp ((t * X ω : ℝ) * Complex.I) := by
    have hpoint : ∀ ω,
        Complex.exp ((t * (X ω + c) : ℝ) * Complex.I) =
          Complex.exp ((t * c : ℝ) * Complex.I) *
            Complex.exp ((t * X ω : ℝ) * Complex.I) := by
      intro ω
      rw [← Complex.exp_add]
      congr 2
      push_cast
      ring
    simp_rw [hpoint]
    simpa using
      (Finset.mul_sum (Finset.univ : Finset Ω)
        (fun ω ↦ Complex.exp ((t * X ω : ℝ) * Complex.I))
        (Complex.exp ((t * c : ℝ) * Complex.I))).symm
  rw [hsum]
  ring

/-- A Rademacher sign encoded by a Boolean. -/
def rademacherSign (b : Bool) : ℝ := if b then 1 else -1

@[simp] lemma rademacherSign_false : rademacherSign false = -1 := rfl

@[simp] lemma rademacherSign_true : rademacherSign true = 1 := rfl

@[simp] lemma rademacherSign_sq (b : Bool) : rademacherSign b ^ 2 = 1 := by
  cases b <;> simp [rademacherSign]

lemma sum_bool_exp_rademacher (a : ℝ) :
    (∑ b : Bool, Complex.exp ((a * rademacherSign b : ℝ) * Complex.I)) =
      2 * Real.cos a := by
  simp [rademacherSign, Complex.exp_ofReal_mul_I]
  ring

/-- Exact characteristic-function factorization for a linear form of
independent Rademacher signs. -/
lemma sum_exp_rademacher_linear {I : Type u} [Fintype I] [DecidableEq I]
    (a : I → ℝ) :
    (∑ ξ : I → Bool,
        Complex.exp ((((∑ i, a i * rademacherSign (ξ i) : ℝ)) : ℂ) * Complex.I)) =
      (2 : ℂ) ^ Fintype.card I * ∏ i, (Real.cos (a i) : ℂ) := by
  calc
    (∑ ξ : I → Bool,
        Complex.exp ((((∑ i, a i * rademacherSign (ξ i) : ℝ)) : ℂ) * Complex.I)) =
        ∑ ξ : I → Bool, ∏ i,
          Complex.exp ((a i * rademacherSign (ξ i) : ℝ) * Complex.I) := by
            apply Finset.sum_congr rfl
            intro ξ _
            rw [← Complex.exp_sum Finset.univ]
            congr 1
            have hcast :
                (((∑ i, a i * rademacherSign (ξ i) : ℝ)) : ℂ) =
                  ∑ i, ((a i * rademacherSign (ξ i) : ℝ) : ℂ) := by
              push_cast
              rfl
            rw [hcast]
            simpa using
              (Finset.sum_mul (Finset.univ : Finset I)
                (fun i ↦ ((a i * rademacherSign (ξ i) : ℝ) : ℂ)) Complex.I)
    _ = ∏ i, ∑ b : Bool,
          Complex.exp ((a i * rademacherSign b : ℝ) * Complex.I) := by
            rw [Fintype.prod_sum]
    _ = ∏ i, (2 : ℂ) * Real.cos (a i) := by
            apply Finset.prod_congr rfl
            intro i _
            exact_mod_cast sum_bool_exp_rademacher (a i)
    _ = (2 : ℂ) ^ Fintype.card I * ∏ i, (Real.cos (a i) : ℂ) := by
            rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ]

/-- The normalized exact product formula. -/
lemma finCharFun_rademacher_linear {I : Type u} [Fintype I] [DecidableEq I]
    (a : I → ℝ) (t : ℝ) :
    finCharFun (I → Bool) (fun ξ ↦ ∑ i, a i * rademacherSign (ξ i)) t =
      ∏ i, (Real.cos (t * a i) : ℂ) := by
  rw [finCharFun, finExpectation]
  have hsum := sum_exp_rademacher_linear (fun i ↦ t * a i)
  have harg : ∀ ω : I → Bool,
      t * (∑ i, a i * rademacherSign (ω i)) =
        ∑ i, (t * a i) * rademacherSign (ω i) := by
    intro ω
    change t * Finset.univ.sum (fun i ↦ a i * rademacherSign (ω i)) =
      Finset.univ.sum (fun i ↦ (t * a i) * rademacherSign (ω i))
    simpa only [mul_assoc] using
      Finset.mul_sum (Finset.univ : Finset I)
        (fun i ↦ a i * rademacherSign (ω i)) t
  simp_rw [harg]
  rw [hsum]
  have hcard : (Fintype.card (I → Bool) : ℂ) =
      (2 : ℂ) ^ Fintype.card I := by
    simp
  rw [hcard]
  exact mul_div_cancel_left₀ _ (pow_ne_zero _ (by norm_num : (2 : ℂ) ≠ 0))

/-- Absolute-value form of independent Rademacher cancellation. -/
lemma norm_finCharFun_rademacher_linear {I : Type u} [Fintype I] [DecidableEq I]
    (a : I → ℝ) (t : ℝ) :
    ‖finCharFun (I → Bool) (fun ξ ↦ ∑ i, a i * rademacherSign (ξ i)) t‖ =
      ∏ i, |Real.cos (t * a i)| := by
  rw [finCharFun_rademacher_linear, norm_prod]
  apply Finset.prod_congr rfl
  intro i _
  simpa [Real.norm_eq_abs] using Complex.norm_real (Real.cos (t * a i))

/-- A centered representative of a class modulo `ℤ`.  This predicate is
the concrete form of `‖x‖_{ℝ/ℤ}` used by the cosine cancellation estimate. -/
def IsCenteredModOne (x d : ℝ) : Prop :=
  |d| ≤ 1 / 2 ∧ ∃ k : ℤ, x = k + d

lemma IsCenteredModOne.zero : IsCenteredModOne 0 0 := by
  refine ⟨by norm_num, 0, ?_⟩
  norm_num

lemma IsCenteredModOne.neg {x d : ℝ} (h : IsCenteredModOne x d) :
    IsCenteredModOne (-x) (-d) := by
  rcases h with ⟨hd, k, hk⟩
  refine ⟨?_, -k, ?_⟩
  · simpa using hd
  · rw [hk]
    push_cast
    ring

/-- The analytic part of the KSSS cosine cancellation estimate. -/
lemma abs_cos_le_exp_neg_sq_div_pi_sq {x : ℝ} (hx : |x| ≤ Real.pi / 2) :
    |Real.cos x| ≤ Real.exp (-(x / Real.pi) ^ 2) := by
  have hxIcc : x ∈ Set.Icc (-(Real.pi / 2)) (Real.pi / 2) := by
    simpa [abs_le] using hx
  rw [abs_of_nonneg (Real.cos_nonneg_of_mem_Icc hxIcc)]
  calc
    Real.cos x ≤ 1 - 2 / Real.pi ^ 2 * x ^ 2 :=
      Real.cos_le_one_sub_mul_cos_sq (hx.trans (by nlinarith [Real.pi_pos]))
    _ ≤ 1 - (x / Real.pi) ^ 2 := by
      have heq : 2 / Real.pi ^ 2 * x ^ 2 = 2 * (x / Real.pi) ^ 2 := by
        field_simp [ne_of_gt Real.pi_pos]
      rw [heq]
      nlinarith [sq_nonneg (x / Real.pi)]
    _ ≤ Real.exp (-(x / Real.pi) ^ 2) := Real.one_sub_le_exp_neg _

/-- KSSS (4.16), with the quotient distance supplied as its unique centered
representative. -/
lemma abs_cos_le_exp_neg_centeredModOne_sq {r d : ℝ}
    (h : IsCenteredModOne (r / Real.pi) d) :
    |Real.cos r| ≤ Real.exp (-d ^ 2) := by
  rcases h with ⟨hd, k, hk⟩
  have hpi : Real.pi ≠ 0 := ne_of_gt Real.pi_pos
  have hr : r = Real.pi * ((k : ℝ) + d) := by
    calc
      r = Real.pi * (r / Real.pi) := by field_simp
      _ = Real.pi * ((k : ℝ) + d) := by rw [hk]
  have hcos : |Real.cos r| = |Real.cos (Real.pi * d)| := by
    rw [hr]
    have heq : Real.pi * ((k : ℝ) + d) = Real.pi * d + k * Real.pi := by
      push_cast
      ring
    rw [heq, Real.cos_add_int_mul_pi]
    simp
  rw [hcos]
  have hlocal : |Real.pi * d| ≤ Real.pi / 2 := by
    rw [abs_mul, abs_of_pos Real.pi_pos]
    calc
      Real.pi * |d| ≤ Real.pi * (1 / 2) :=
        mul_le_mul_of_nonneg_left hd Real.pi_pos.le
      _ = Real.pi / 2 := by ring
  simpa [hpi] using abs_cos_le_exp_neg_sq_div_pi_sq hlocal

/-- The independent-coordinate cancellation estimate (KSSS (4.16)) for a
linear form of Rademacher signs.  The function `d` records the centered
representatives of the coefficients modulo `ℤ`. -/
lemma norm_finCharFun_rademacher_linear_le_exp_neg_sum_sq
    {I : Type u} [Fintype I] [DecidableEq I]
    (a d : I → ℝ) (t : ℝ)
    (hd : ∀ i, IsCenteredModOne (t * a i / Real.pi) (d i)) :
    ‖finCharFun (I → Bool) (fun ξ ↦ ∑ i, a i * rademacherSign (ξ i)) t‖ ≤
      Real.exp (-∑ i, d i ^ 2) := by
  rw [norm_finCharFun_rademacher_linear]
  calc
    (∏ i, |Real.cos (t * a i)|) ≤ ∏ i, Real.exp (-(d i) ^ 2) := by
      apply Finset.prod_le_prod
      · intro i _
        exact abs_nonneg _
      · intro i _
        have hi := abs_cos_le_exp_neg_centeredModOne_sq (hd i)
        simpa [mul_div_assoc] using hi
    _ = Real.exp (∑ i, -(d i) ^ 2) := by
      rw [Real.exp_sum]
    _ = Real.exp (-∑ i, d i ^ 2) := by
      congr 1
      rw [Finset.sum_neg_distrib]

/-- Adding a deterministic phase does not affect the independent-coordinate
cancellation bound. -/
lemma norm_finCharFun_affine_rademacher_le_exp_neg_sum_sq
    {I : Type u} [Fintype I] [DecidableEq I]
    (a d : I → ℝ) (b t : ℝ)
    (hd : ∀ i, IsCenteredModOne (t * a i / Real.pi) (d i)) :
    ‖finCharFun (I → Bool)
        (fun ξ ↦ (∑ i, a i * rademacherSign (ξ i)) + b) t‖ ≤
      Real.exp (-∑ i, d i ^ 2) := by
  rw [finCharFun_add_const, norm_mul, Complex.norm_exp]
  have hre : ((((t * b : ℝ) : ℂ) * Complex.I).re) = 0 := by
    rw [Complex.mul_re]
    simp
  rw [hre, Real.exp_zero, one_mul]
  exact norm_finCharFun_rademacher_linear_le_exp_neg_sum_sq a d t hd

/-- Hamming weight of a Boolean vector. -/
def boolWeight {I : Type u} [Fintype I] [DecidableEq I] (x : I → Bool) : ℕ :=
  (Finset.univ.filter fun i ↦ x i).card

/-- The Boolean slice of vectors of a prescribed Hamming weight. -/
def BoolSlice (I : Type u) [Fintype I] [DecidableEq I] (s : ℕ) :=
  {x : I → Bool // boolWeight x = s}

/-- An indexed collection of pairwise disjoint unordered pairs, represented
by an embedding of `K × Bool` into the vertex type. -/
abbrev PairEmbedding (K : Type v) (I : Type u) := K × Bool ↪ I

/-- Independently reverse any chosen collection of pair orientations. -/
def pairOrientationPerm {K : Type v} (σ : K → Bool) : Equiv.Perm (K × Bool) where
  toFun z := (z.1, if σ z.1 then !z.2 else z.2)
  invFun z := (z.1, if σ z.1 then !z.2 else z.2)
  left_inv := by
    rintro ⟨k, b⟩
    cases h : σ k <;> cases b <;> simp [h]
  right_inv := by
    rintro ⟨k, b⟩
    cases h : σ k <;> cases b <;> simp [h]

@[simp] lemma pairOrientationPerm_apply {K : Type v} (σ : K → Bool)
    (k : K) (b : Bool) :
    pairOrientationPerm σ (k, b) =
      (k, if σ k then !b else b) := rfl

@[simp] lemma pairOrientationPerm_symm {K : Type v} (σ : K → Bool) :
    (pairOrientationPerm σ).symm = pairOrientationPerm σ := by
  rfl

/-- The permutation of vertices obtained by reversing the pairs selected by
`σ`; vertices outside the embedded pairs are fixed. -/
noncomputable def pairVertexPerm {K : Type v} {I : Type u}
    [Fintype K] [DecidableEq I] (p : PairEmbedding K I) (σ : K → Bool) :
    Equiv.Perm I :=
  (pairOrientationPerm σ).viaFintypeEmbedding p

@[simp] lemma pairVertexPerm_apply_endpoint {K : Type v} {I : Type u}
    [Fintype K] [DecidableEq I] (p : PairEmbedding K I) (σ : K → Bool)
    (k : K) (b : Bool) :
    pairVertexPerm p σ (p (k, b)) =
      p (k, if σ k then !b else b) := by
  simp [pairVertexPerm]

/-- Pull a Boolean vector back along a pair-swap permutation. -/
noncomputable def pairSwap {K : Type v} {I : Type u}
    [Fintype K] [DecidableEq I] (p : PairEmbedding K I) (σ : K → Bool)
    (x : I → Bool) : I → Bool :=
  (pairVertexPerm p σ).arrowCongr (Equiv.refl Bool) x

@[simp] lemma pairSwap_apply {K : Type v} {I : Type u}
    [Fintype K] [DecidableEq I] (p : PairEmbedding K I) (σ : K → Bool)
    (x : I → Bool) (i : I) :
    pairSwap p σ x i = x ((pairVertexPerm p σ).symm i) := by
  rfl

@[simp] lemma pairSwap_apply_endpoint {K : Type v} {I : Type u}
    [Fintype K] [DecidableEq I] (p : PairEmbedding K I) (σ : K → Bool)
    (x : I → Bool) (k : K) (b : Bool) :
    pairSwap p σ x (p (k, b)) =
      x (p (k, if σ k then !b else b)) := by
  rw [pairSwap_apply]
  apply congrArg x
  apply (pairVertexPerm p σ).symm_apply_eq.mpr
  rw [pairVertexPerm_apply_endpoint]
  cases h : σ k <;> cases b <;> simp [h]

lemma boolWeight_eq_sum {I : Type u} [Fintype I] [DecidableEq I]
    (x : I → Bool) :
    boolWeight x = ∑ i, if x i then 1 else 0 := by
  classical
  rw [boolWeight, Finset.card_eq_sum_ones, Finset.sum_filter]

/-- Hamming weight is invariant under reindexing coordinates. -/
lemma boolWeight_arrowCongr {I : Type u} [Fintype I] [DecidableEq I]
    (e : Equiv.Perm I) (x : I → Bool) :
    boolWeight (e.arrowCongr (Equiv.refl Bool) x) = boolWeight x := by
  rw [boolWeight_eq_sum, boolWeight_eq_sum]
  exact e.symm.sum_comp (fun i ↦ if x i then 1 else 0)

@[simp] lemma boolWeight_pairSwap {K : Type v} {I : Type u}
    [Fintype K] [Fintype I] [DecidableEq I]
    (p : PairEmbedding K I) (σ : K → Bool) (x : I → Bool) :
    boolWeight (pairSwap p σ x) = boolWeight x := by
  exact boolWeight_arrowCongr (pairVertexPerm p σ) x

/-- Pair swapping restricts to a permutation of every Boolean slice. -/
noncomputable def slicePairSwap {K : Type v} {I : Type u}
    [Fintype K] [Fintype I] [DecidableEq I]
    (p : PairEmbedding K I) (σ : K → Bool) (s : ℕ) :
    Equiv.Perm (BoolSlice I s) :=
  ((pairVertexPerm p σ).arrowCongr (Equiv.refl Bool)).subtypeEquiv fun x ↦ by
    rw [boolWeight_arrowCongr]

@[simp] lemma slicePairSwap_val {K : Type v} {I : Type u}
    [Fintype K] [Fintype I] [DecidableEq I]
    (p : PairEmbedding K I) (σ : K → Bool) (s : ℕ) (x : BoolSlice I s) :
    (slicePairSwap p σ s x).1 = pairSwap p σ x.1 := rfl

/-- The `0`--`1` value of a Boolean, regarded as a real number. -/
def boolIndicator (b : Bool) : ℝ := if b then 1 else 0

@[simp] lemma boolIndicator_false : boolIndicator false = 0 := rfl

@[simp] lemma boolIndicator_true : boolIndicator true = 1 := rfl

/-- Number of embedded pairs having exactly one selected endpoint. -/
def singletonPairCount {K : Type v} {I : Type u}
    [Fintype K] [DecidableEq K] (p : PairEmbedding K I) (x : I → Bool) : ℕ :=
  (Finset.univ.filter fun k ↦ x (p (k, false)) ≠ x (p (k, true))).card

/-- Rademacher coefficient produced by independently swapping a pair. -/
noncomputable def pairRademacherCoeff {K : Type v} {I : Type u}
    (p : PairEmbedding K I) (a : I → ℝ) (x : I → Bool) (k : K) : ℝ :=
  (a (p (k, true)) - a (p (k, false))) *
    (boolIndicator (x (p (k, false))) - boolIndicator (x (p (k, true)))) / 2

/-- The centered modular representative of a pair coefficient, with its sign
chosen according to which endpoint of the pair is selected. -/
def pairCenteredRep {K : Type v} {I : Type u}
    (p : PairEmbedding K I) (q : K → ℝ) (x : I → Bool) (k : K) : ℝ :=
  if x (p (k, false)) = x (p (k, true)) then 0
  else if x (p (k, false)) then -q k else q k

lemma pairRademacherCoeff_centered {K : Type v} {I : Type u}
    (p : PairEmbedding K I) (a : I → ℝ) (q : K → ℝ) (x : I → Bool)
    (k : K)
    (hq : IsCenteredModOne
      ((a (p (k, false)) - a (p (k, true))) / (2 * Real.pi)) (q k)) :
    IsCenteredModOne (pairRademacherCoeff p a x k / Real.pi)
      (pairCenteredRep p q x k) := by
  have hpi : Real.pi ≠ 0 := ne_of_gt Real.pi_pos
  cases hleft : x (p (k, false)) <;>
    cases hright : x (p (k, true))
  · simpa [pairRademacherCoeff, pairCenteredRep, hleft, hright,
      boolIndicator] using IsCenteredModOne.zero
  · have heq :
        pairRademacherCoeff p a x k / Real.pi =
          (a (p (k, false)) - a (p (k, true))) / (2 * Real.pi) := by
        simp [pairRademacherCoeff, hleft, hright, boolIndicator]
        field_simp <;> ring
    simpa [pairCenteredRep, hleft, hright, heq] using hq
  · have heq :
        pairRademacherCoeff p a x k / Real.pi =
          -((a (p (k, false)) - a (p (k, true))) / (2 * Real.pi)) := by
        simp [pairRademacherCoeff, hleft, hright, boolIndicator]
        field_simp <;> ring
    simpa [pairCenteredRep, hleft, hright, heq] using hq.neg
  · simpa [pairRademacherCoeff, pairCenteredRep, hleft, hright,
      boolIndicator] using IsCenteredModOne.zero

lemma pairCenteredRep_sq_ge {K : Type v} {I : Type u}
    [Fintype K] [DecidableEq K]
    (p : PairEmbedding K I) (q : K → ℝ) (x : I → Bool) {delta : ℝ}
    (hdelta : 0 ≤ delta)
    (hq : ∀ k, delta ≤ |q k|) :
    (singletonPairCount p x : ℝ) * delta ^ 2 ≤
      ∑ k, pairCenteredRep p q x k ^ 2 := by
  classical
  let singles : Finset K := Finset.univ.filter fun k ↦
    x (p (k, false)) ≠ x (p (k, true))
  change (singles.card : ℝ) * delta ^ 2 ≤ _
  have hcard :
      (singles.card : ℝ) =
        ∑ k, if x (p (k, false)) ≠ x (p (k, true)) then (1 : ℝ) else 0 := by
    calc
      (singles.card : ℝ) = Finset.sum singles (fun _ ↦ (1 : ℝ)) := by simp
      _ = ∑ k, if x (p (k, false)) ≠ x (p (k, true)) then (1 : ℝ) else 0 := by
        simp only [singles, Finset.sum_filter]
  rw [hcard]
  rw [Finset.sum_mul]
  apply Finset.sum_le_sum
  intro k _
  by_cases heq : x (p (k, false)) = x (p (k, true))
  · simp [heq, pairCenteredRep]
  · have hne : x (p (k, false)) ≠ x (p (k, true)) := heq
    have hsq : delta ^ 2 ≤ (q k) ^ 2 := by
      nlinarith [sq_nonneg (|q k| - delta), abs_nonneg (q k), hq k,
        sq_abs (q k)]
    cases hleft : x (p (k, false)) <;>
      cases hright : x (p (k, true)) <;>
      simp_all [pairCenteredRep, hsq]

private lemma sum_eq_sum_pairEmbedding_of_eq_zero
    {K : Type v} {I : Type u} [Fintype K] [Fintype I] [DecidableEq I]
    (p : PairEmbedding K I) (f : I → ℝ)
    (hf : ∀ i, i ∉ Set.range p → f i = 0) :
    (∑ i, f i) = ∑ z : K × Bool, f (p z) := by
  classical
  let s : Finset I := Finset.univ.map p
  calc
    (∑ i, f i) = ∑ i ∈ s, f i := by
      symm
      apply Finset.sum_subset (by simp [s])
      intro i _ his
      apply hf i
      intro hi
      rcases hi with ⟨z, rfl⟩
      exact his (by simp [s])
    _ = ∑ z : K × Bool, f (p z) := by
      simp [s]

/-- Exact change of a linear phase under independent pair swaps. -/
lemma pairSwap_linear_phase {K : Type v} {I : Type u}
    [Fintype K] [Fintype I] [DecidableEq I]
    (p : PairEmbedding K I) (a : I → ℝ) (x : I → Bool) (σ : K → Bool) :
    (∑ i, a i * boolIndicator (pairSwap p σ x i)) =
      (∑ i, a i * boolIndicator (x i)) +
        ∑ k, if σ k then 2 * pairRademacherCoeff p a x k else 0 := by
  classical
  let e : Equiv.Perm I := pairVertexPerm p σ
  have hreindex :
      (∑ i, a i * boolIndicator (pairSwap p σ x i)) =
        ∑ i, a (e i) * boolIndicator (x i) := by
    calc
      (∑ i, a i * boolIndicator (pairSwap p σ x i)) =
          ∑ i, a i * boolIndicator (x (e.symm i)) := by rfl
      _ = ∑ i, a (e i) * boolIndicator (x i) := by
        exact (Fintype.sum_equiv e
          (fun i ↦ a (e i) * boolIndicator (x i))
          (fun j ↦ a j * boolIndicator (x (e.symm j)))
          (fun i ↦ by simp)).symm
  rw [hreindex]
  have hdiff :
      (∑ i, (a (e i) - a i) * boolIndicator (x i)) =
        ∑ k, if σ k then 2 * pairRademacherCoeff p a x k else 0 := by
    calc
      (∑ i, (a (e i) - a i) * boolIndicator (x i)) =
          ∑ z : K × Bool,
            (a (e (p z)) - a (p z)) * boolIndicator (x (p z)) := by
        apply sum_eq_sum_pairEmbedding_of_eq_zero p
        intro i hi
        have hei : e i = i := by
          exact Equiv.Perm.viaFintypeEmbedding_apply_notMem_range
            (pairOrientationPerm σ) p hi
        rw [hei, sub_self, zero_mul]
      _ = ∑ k, if σ k then 2 * pairRademacherCoeff p a x k else 0 := by
        rw [Fintype.sum_prod_type]
        apply Finset.sum_congr rfl
        intro k _
        cases hs : σ k <;>
          cases hl : x (p (k, false)) <;>
          cases hr : x (p (k, true)) <;>
          simp [e, pairVertexPerm, pairRademacherCoeff, boolIndicator,
            hs, hl, hr] <;> ring
  calc
    (∑ i, a (e i) * boolIndicator (x i)) =
        (∑ i, a i * boolIndicator (x i)) +
          ∑ i, (a (e i) - a i) * boolIndicator (x i) := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro i _
      ring
    _ = _ := by rw [hdiff]

/-- Rademacher-affine form of the pair-swap phase. -/
lemma pairSwap_linear_phase_rademacher {K : Type v} {I : Type u}
    [Fintype K] [Fintype I] [DecidableEq I]
    (p : PairEmbedding K I) (a : I → ℝ) (x : I → Bool) (σ : K → Bool) :
    (∑ i, a i * boolIndicator (pairSwap p σ x i)) =
      (∑ k, pairRademacherCoeff p a x k * rademacherSign (σ k)) +
        ((∑ i, a i * boolIndicator (x i)) +
          ∑ k, pairRademacherCoeff p a x k) := by
  rw [pairSwap_linear_phase]
  have hsum :
      (∑ k, if σ k then 2 * pairRademacherCoeff p a x k else 0) =
        (∑ k, pairRademacherCoeff p a x k * rademacherSign (σ k)) +
          ∑ k, pairRademacherCoeff p a x k := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro k _
    cases h : σ k <;> simp [h, rademacherSign] <;> ring
  rw [hsum]
  ring

/-- Averaging a function over any family of permutations does not change
its uniform expectation.  This is the finite orbit-averaging identity used
in the proof of the slice characteristic estimate. -/
lemma finExpectation_average_equiv_family
    {Ω : Type u} {Γ : Type v} [Fintype Ω] [Nonempty Ω]
    [Fintype Γ] [Nonempty Γ] (e : Γ → Equiv.Perm Ω) (f : Ω → ℂ) :
    finExpectation Ω f =
      finExpectation Ω (fun ω ↦ finExpectation Γ (fun γ ↦ f (e γ ω))) := by
  have hsum :
      (∑ ω, ∑ γ, f (e γ ω)) =
        (Fintype.card Γ : ℂ) * ∑ ω, f ω := by
    calc
      (∑ ω, ∑ γ, f (e γ ω)) = ∑ γ, ∑ ω, f (e γ ω) :=
        Finset.sum_comm
      _ = ∑ γ, ∑ ω, f ω := by
        apply Finset.sum_congr rfl
        intro γ _
        exact Fintype.sum_equiv (e γ) (fun ω ↦ f (e γ ω)) f (fun ω ↦ rfl)
      _ = (Fintype.card Γ : ℂ) * ∑ ω, f ω := by simp
  rw [finExpectation, finExpectation]
  simp_rw [finExpectation]
  simp_rw [div_eq_mul_inv]
  rw [← Finset.sum_mul, hsum]
  field_simp [card_ne_zero Ω, card_ne_zero Γ]

/-- Pointwise triangle-inequality consequence of orbit averaging. -/
lemma norm_finExpectation_le_average_orbit_norm
    {Ω : Type u} {Γ : Type v} [Fintype Ω] [Nonempty Ω]
    [Fintype Γ] [Nonempty Γ] (e : Γ → Equiv.Perm Ω) (f : Ω → ℂ) :
    ‖finExpectation Ω f‖ ≤
      (∑ ω, ‖finExpectation Γ (fun γ ↦ f (e γ ω))‖) /
        Fintype.card Ω := by
  rw [finExpectation_average_equiv_family e f]
  exact norm_finExpectation_le Ω _

/-- Pair-orbit cancellation for one fixed Boolean vector.  The bound is in
terms of the exact number of singleton pairs in that vector. -/
lemma norm_pairSwap_orbit_average_le {K : Type v} {I : Type u}
    [Fintype K] [DecidableEq K] [Fintype I] [DecidableEq I]
    (p : PairEmbedding K I) (a : I → ℝ) (q : K → ℝ) (x : I → Bool)
    {delta : ℝ}
    (hdelta : 0 ≤ delta)
    (hqcenter : ∀ k, IsCenteredModOne
      ((a (p (k, false)) - a (p (k, true))) / (2 * Real.pi)) (q k))
    (hqdelta : ∀ k, delta ≤ |q k|) :
    ‖finExpectation (K → Bool) (fun σ ↦
        Complex.exp (((∑ i, a i * boolIndicator (pairSwap p σ x i) : ℝ) : ℂ) *
          Complex.I))‖ ≤
      Real.exp (-(singletonPairCount p x : ℝ) * delta ^ 2) := by
  let coeff : K → ℝ := pairRademacherCoeff p a x
  let rep : K → ℝ := pairCenteredRep p q x
  let base : ℝ :=
    (∑ i, a i * boolIndicator (x i)) + ∑ k, pairRademacherCoeff p a x k
  have hrewrite :
      finExpectation (K → Bool) (fun σ ↦
          Complex.exp (((∑ i, a i * boolIndicator (pairSwap p σ x i) : ℝ) : ℂ) *
            Complex.I)) =
        finCharFun (K → Bool)
          (fun σ ↦ (∑ k, coeff k * rademacherSign (σ k)) + base) 1 := by
    rw [finCharFun]
    apply congrArg (fun z : ℂ ↦ z / (Fintype.card (K → Bool) : ℂ))
    apply Finset.sum_congr rfl
    intro σ _
    simp only [one_mul]
    apply congrArg Complex.exp
    apply congrArg (fun z : ℂ ↦ z * Complex.I)
    exact_mod_cast pairSwap_linear_phase_rademacher p a x σ
  rw [hrewrite]
  calc
    ‖finCharFun (K → Bool)
        (fun σ ↦ (∑ k, coeff k * rademacherSign (σ k)) + base) 1‖ ≤
        Real.exp (-∑ k, rep k ^ 2) := by
      apply norm_finCharFun_affine_rademacher_le_exp_neg_sum_sq coeff rep base 1
      intro k
      simpa [coeff, rep] using
        pairRademacherCoeff_centered p a q x k (hqcenter k)
    _ ≤ Real.exp (-(singletonPairCount p x : ℝ) * delta ^ 2) := by
      apply Real.exp_le_exp.mpr
      simpa only [neg_mul] using
        neg_le_neg (pairCenteredRep_sq_ge p q x hdelta hqdelta)

noncomputable instance {I : Type u} [Fintype I] [DecidableEq I] (s : ℕ) :
    Fintype (BoolSlice I s) := by
  letI : Fintype (I → Bool) := Pi.instFintype
  exact Fintype.ofInjective Subtype.val Subtype.val_injective

/-- Boolean functions are equivalent to their true-coordinate finsets. -/
def boolFunEquivFinset (I : Type u) [Fintype I] [DecidableEq I] :
    (I → Bool) ≃ Finset I where
  toFun x := Finset.univ.filter fun i ↦ x i
  invFun S := fun i ↦ decide (i ∈ S)
  left_inv x := by
    funext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    cases x i <;> simp
  right_inv S := by
    ext i
    simp

@[simp] lemma boolFunEquivFinset_card
    (I : Type u) [Fintype I] [DecidableEq I] (x : I → Bool) :
    (boolFunEquivFinset I x).card = boolWeight x := rfl

/-- A Boolean slice is equivalent to the finsets of the same cardinality. -/
def boolSliceEquivFinsetLen
    (I : Type u) [Fintype I] [DecidableEq I] (s : ℕ) :
    BoolSlice I s ≃ {S : Finset I // S.card = s} :=
  (boolFunEquivFinset I).subtypeEquiv fun _ ↦ Iff.rfl

@[simp] lemma card_boolSlice
    (I : Type u) [Fintype I] [DecidableEq I] (s : ℕ) :
    Fintype.card (BoolSlice I s) = Nat.choose (Fintype.card I) s := by
  rw [Fintype.card_congr (boolSliceEquivFinsetLen I s)]
  exact Fintype.card_finset_len s

/-- Extend Boolean data from a coordinate set and its complement. -/
def extendBool {I : Type u} [Fintype I] [DecidableEq I]
    (J : Finset I) (y : J → Bool) (z : {i : I // i ∉ J} → Bool) : I → Bool :=
  fun i ↦ if hi : i ∈ J then y ⟨i, hi⟩ else z ⟨i, hi⟩

@[simp] lemma extendBool_apply_mem {I : Type u} [Fintype I] [DecidableEq I]
    (J : Finset I) (y : J → Bool) (z : {i : I // i ∉ J} → Bool) (i : J) :
    extendBool J y z i = y i := by
  simp [extendBool, i.prop]

@[simp] lemma extendBool_apply_notMem {I : Type u} [Fintype I] [DecidableEq I]
    (J : Finset I) (y : J → Bool) (z : {i : I // i ∉ J} → Bool)
    (i : {i : I // i ∉ J}) :
    extendBool J y z i = z i := by
  simp [extendBool, i.prop]

lemma boolWeight_extendBool {I : Type u} [Fintype I] [DecidableEq I]
    (J : Finset I) (y : J → Bool) (z : {i : I // i ∉ J} → Bool) :
    boolWeight (extendBool J y z) = boolWeight y + boolWeight z := by
  classical
  simp only [boolWeight_eq_sum]
  let e : J ⊕ {i : I // i ∉ J} ≃ I := Equiv.sumCompl (fun i ↦ i ∈ J)
  calc
    (∑ i : I, if extendBool J y z i then 1 else 0) =
        ∑ w : J ⊕ {i : I // i ∉ J},
          if extendBool J y z (e w) then 1 else 0 := by
      exact (e.sum_comp (fun i ↦ if extendBool J y z i then 1 else 0)).symm
    _ = (∑ i : J, if y i then 1 else 0) +
        ∑ i : {i : I // i ∉ J}, if z i then 1 else 0 := by
      rw [Fintype.sum_sum_type]
      congr 1 <;> apply Finset.sum_congr rfl <;> intro i hi
      · simp [e]
      · simp [e]

/-- Slice points extending fixed Boolean data on `J`. -/
def BoolSliceExtensions {I : Type u} [Fintype I] [DecidableEq I]
    (J : Finset I) (y : J → Bool) (s : ℕ) :=
  {x : BoolSlice I s // ∀ i : J, x.1 i = y i}

noncomputable instance {I : Type u} [Fintype I] [DecidableEq I]
    (J : Finset I) (y : J → Bool) (s : ℕ) :
    Fintype (BoolSliceExtensions J y s) :=
  Fintype.ofInjective Subtype.val Subtype.val_injective

/-- Completing fixed Boolean data is a slice on the unfixed coordinates. -/
def boolSliceExtensionsEquiv {I : Type u} [Fintype I] [DecidableEq I]
    (J : Finset I) (y : J → Bool) (s : ℕ) (hy : boolWeight y ≤ s) :
    BoolSliceExtensions J y s ≃ BoolSlice {i : I // i ∉ J} (s - boolWeight y) where
  toFun x := ⟨fun i ↦ x.1.1 i, by
    have hsplit := boolWeight_extendBool J y
      (fun i : {i : I // i ∉ J} ↦ x.1.1 i)
    have hxext : extendBool J y
        (fun i : {i : I // i ∉ J} ↦ x.1.1 i) = x.1.1 := by
      funext i
      by_cases hi : i ∈ J
      · simpa [extendBool, hi] using (x.2 ⟨i, hi⟩).symm
      · simp [extendBool, hi]
    rw [hxext, x.1.2] at hsplit
    exact ((Nat.sub_eq_iff_eq_add' hy).2 hsplit).symm⟩
  invFun z := ⟨⟨extendBool J y z.1, by
      rw [boolWeight_extendBool, z.2, Nat.add_sub_of_le hy]⟩,
    fun i ↦ extendBool_apply_mem J y z.1 i⟩
  left_inv x := by
    apply Subtype.ext
    apply Subtype.ext
    funext i
    by_cases hi : i ∈ J
    · simpa [extendBool, hi] using (x.2 ⟨i, hi⟩).symm
    · simp [extendBool, hi]
  right_inv z := by
    apply Subtype.ext
    funext i
    simp [extendBool, i.prop]

lemma card_boolSliceExtensions {I : Type u} [Fintype I] [DecidableEq I]
    (J : Finset I) (y : J → Bool) (s : ℕ) (hy : boolWeight y ≤ s) :
    Fintype.card (BoolSliceExtensions J y s) =
      Nat.choose (Fintype.card I - J.card) (s - boolWeight y) := by
  classical
  rw [Fintype.card_congr (boolSliceExtensionsEquiv J y s hy), card_boolSlice]
  congr 2
  simpa using Fintype.card_subtype_compl (fun i : I ↦ i ∈ J)

/-- A term shifted down by `k`, interpreted as zero when the requested
index is negative. -/
def lowerTerm (k : ℕ) (f : ℕ → ℝ) (s : ℕ) : ℝ :=
  if k ≤ s then f (s - k) else 0

/-- Weighted Boolean-slice partition function for `m` distinguished pairs
and `r` unpaired points.  Every singleton pair contributes a factor `z`. -/
noncomputable def pairedSlicePartition : ℕ → ℕ → ℕ → ℝ → ℝ
  | 0, r, s, _ => Nat.choose r s
  | m + 1, r, s, z =>
      pairedSlicePartition m r s z +
        2 * z * lowerTerm 1 (fun t ↦ pairedSlicePartition m r t z) s +
        lowerTerm 2 (fun t ↦ pairedSlicePartition m r t z) s

@[simp] lemma pairedSlicePartition_zero (r s : ℕ) (z : ℝ) :
    pairedSlicePartition 0 r s z = Nat.choose r s := rfl

@[simp] lemma pairedSlicePartition_succ (m r s : ℕ) (z : ℝ) :
    pairedSlicePartition (m + 1) r s z =
      pairedSlicePartition m r s z +
        2 * z * lowerTerm 1 (fun t ↦ pairedSlicePartition m r t z) s +
        lowerTerm 2 (fun t ↦ pairedSlicePartition m r t z) s := rfl

/-- Two-step Pascal identity, in the truncated-subtraction form needed by
the singleton-pair recurrence. -/
lemma choose_add_two (n s : ℕ) :
    Nat.choose (n + 2) s =
      Nat.choose n s +
        2 * lowerTerm 1 (fun t ↦ (Nat.choose n t : ℝ)) s +
        lowerTerm 2 (fun t ↦ (Nat.choose n t : ℝ)) s := by
  cases s with
  | zero => simp [lowerTerm]
  | succ s =>
      cases s with
      | zero =>
          simp [Nat.choose_succ_succ, lowerTerm]
          push_cast
          ring
      | succ s =>
          simp only [lowerTerm, Nat.reduceLeDiff, ↓reduceIte, Nat.add_sub_cancel]
          rw [show n + 2 = (n + 1) + 1 by omega]
          rw [Nat.choose_succ_succ (n + 1) (s + 1)]
          rw [Nat.choose_succ_succ n s]
          rw [Nat.choose_succ_succ n (s + 1)]
          push_cast
          ring

/-- Exact binomial-ratio identity for the probability that a fixed pair is
met in exactly one point. -/
lemma choose_middle_identity (N s : ℕ) (hs : 1 ≤ s) (hsN : s ≤ N) :
    Nat.choose N s * s * (N - s) =
      Nat.choose (N - 2) (s - 1) * N * (N - 1) := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hs
  obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le hsN
  cases n with
  | zero =>
      cases k with
      | zero => simp
      | succ k =>
          have ht : 1 + (k + 1) - 2 = k := by omega
          have hb : 1 + (k + 1) - 1 = k + 1 := by omega
          simp only [Nat.add_zero]
          rw [ht, hb, Nat.choose_eq_zero_of_lt (Nat.lt_succ_self k)]
          simp
  | succ n =>
      have hsub : n + k + 2 - (k + 1) = n + 1 := by omega
      have hcanon :
          (n + k + 2).choose (k + 1) * (k + 1) * (n + 1) =
            (n + k).choose k * (n + k + 2) * (n + k + 1) := by
        calc
          (n + k + 2).choose (k + 1) * (k + 1) * (n + 1) =
              ((n + k + 2).choose (k + 1) *
                (n + k + 2 - (k + 1))) * (k + 1) := by rw [hsub]; ring
          _ = (((n + k + 1).choose (k + 1)) * (n + k + 2)) *
                (k + 1) := by
            rw [← Nat.choose_mul_succ_eq]
          _ = ((n + k + 1) * (n + k).choose k) * (n + k + 2) := by
            rw [mul_assoc, mul_comm (n + k + 2) (k + 1), ← mul_assoc]
            rw [← Nat.add_one_mul_choose_eq]
          _ = (n + k).choose k * (n + k + 2) * (n + k + 1) := by ring
      have hdiff : 1 + k + (n + 1) - (1 + k) = n + 1 := by omega
      have hminus : 1 + k + (n + 1) - 2 = n + k := by omega
      rw [hdiff, hminus]
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hcanon

/-- A reserve of at least `A` selected and `A` unselected points gives an
explicit lower bound on the singleton probability. -/
lemma choose_middle_lower_of_reserve
    {A N T s : ℕ} (hA : 1 ≤ A) (hsel : A ≤ s)
    (hunsel : A ≤ N - s) (hNT : N ≤ T) :
    (2 * (A : ℝ) ^ 2 / (T : ℝ) ^ 2) * Nat.choose N s ≤
      2 * lowerTerm 1 (fun t ↦ (Nat.choose (N - 2) t : ℝ)) s := by
  have hs : 1 ≤ s := hA.trans hsel
  have hsN : s ≤ N := by omega
  have hT : 0 < (T : ℝ) := by
    exact_mod_cast lt_of_lt_of_le (by omega : 0 < N) hNT
  have hreserve : A * A ≤ s * (N - s) := Nat.mul_le_mul hsel hunsel
  have hdenom : N * (N - 1) ≤ T * T := by
    exact Nat.mul_le_mul hNT (le_trans (Nat.sub_le N 1) hNT)
  have hid := choose_middle_identity N s hs hsN
  have hchoose : 0 ≤ (Nat.choose (N - 2) (s - 1) : ℝ) := by positivity
  rw [lowerTerm, if_pos hs]
  rw [div_mul_eq_mul_div]
  apply (div_le_iff₀ (sq_pos_of_pos hT)).2
  norm_cast at hreserve hdenom hid ⊢
  nlinarith
/-- Recursive validity condition for a uniform lower bound `p` on the
conditional probability that each newly exposed pair is a singleton. -/
def PairedSliceStepBound (p : ℝ) : ℕ → ℕ → ℕ → Prop
  | 0, _, _ => True
  | m + 1, r, s =>
      p * Nat.choose (r + 2 * (m + 1)) s ≤
          2 * lowerTerm 1
            (fun t ↦ (Nat.choose (r + 2 * m) t : ℝ)) s ∧
        PairedSliceStepBound p m r s ∧
        PairedSliceStepBound p m r (s - 1) ∧
        PairedSliceStepBound p m r (s - 2)

/-- A reserve which survives all pair exposures verifies every node of the
recursive conditional-probability bound. -/
lemma pairedSliceStepBound_of_reserve
    (m r s A T : ℕ) (hA : 1 ≤ A)
    (hsel : A + 2 * m ≤ s)
    (hunsel : A + 2 * m ≤ r + 2 * m - s)
    (hTotal : r + 2 * m ≤ T) :
    PairedSliceStepBound (2 * (A : ℝ) ^ 2 / (T : ℝ) ^ 2) m r s := by
  induction m generalizing s with
  | zero => simp [PairedSliceStepBound]
  | succ m ih =>
      rw [PairedSliceStepBound]
      have hN : r + 2 * (m + 1) - 2 = r + 2 * m := by omega
      refine ⟨?_, ?_, ?_, ?_⟩
      · simpa [hN] using
          (choose_middle_lower_of_reserve hA
            (show A ≤ s by omega)
            (show A ≤ r + 2 * (m + 1) - s by omega) hTotal)
      · apply ih <;> omega
      · apply ih <;> omega
      · apply ih <;> omega

/-- Exact recurrence/Chernoff lemma for distinguished pairs on a slice. -/
lemma pairedSlicePartition_le
    (m r s : ℕ) {p z : ℝ}
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hz0 : 0 ≤ z) (hz1 : z ≤ 1)
    (hstep : PairedSliceStepBound p m r s) :
    pairedSlicePartition m r s z ≤
      (1 - p * (1 - z)) ^ m * Nat.choose (r + 2 * m) s := by
  induction m generalizing s with
  | zero => simp
  | succ m ih =>
      rcases hstep with ⟨hmid, hs0, hs1, hs2⟩
      have hq0 : 0 ≤ 1 - p * (1 - z) := by nlinarith
      have h0 := ih s hs0
      have h1 := ih (s - 1) hs1
      have h2 := ih (s - 2) hs2
      have h1' :
          lowerTerm 1 (fun t ↦ pairedSlicePartition m r t z) s ≤
            (1 - p * (1 - z)) ^ m *
              lowerTerm 1 (fun t ↦ (Nat.choose (r + 2 * m) t : ℝ)) s := by
        simp only [lowerTerm]
        split_ifs with h
        · exact h1
        · positivity
      have h2' :
          lowerTerm 2 (fun t ↦ pairedSlicePartition m r t z) s ≤
            (1 - p * (1 - z)) ^ m *
              lowerTerm 2 (fun t ↦ (Nat.choose (r + 2 * m) t : ℝ)) s := by
        simp only [lowerTerm]
        split_ifs with h
        · exact h2
        · positivity
      have hN : r + 2 * (m + 1) = (r + 2 * m) + 2 := by omega
      rw [hN] at hmid
      rw [pairedSlicePartition_succ]
      calc
        pairedSlicePartition m r s z +
              2 * z * lowerTerm 1 (fun t ↦ pairedSlicePartition m r t z) s +
              lowerTerm 2 (fun t ↦ pairedSlicePartition m r t z) s ≤
            (1 - p * (1 - z)) ^ m * Nat.choose (r + 2 * m) s +
              2 * z * ((1 - p * (1 - z)) ^ m *
                lowerTerm 1
                  (fun t ↦ (Nat.choose (r + 2 * m) t : ℝ)) s) +
              (1 - p * (1 - z)) ^ m *
                lowerTerm 2
                  (fun t ↦ (Nat.choose (r + 2 * m) t : ℝ)) s := by
          gcongr
        _ = (1 - p * (1 - z)) ^ m *
              (Nat.choose (r + 2 * m) s +
                2 * z * lowerTerm 1
                  (fun t ↦ (Nat.choose (r + 2 * m) t : ℝ)) s +
                lowerTerm 2
                  (fun t ↦ (Nat.choose (r + 2 * m) t : ℝ)) s) := by ring
        _ ≤ (1 - p * (1 - z)) ^ m *
              ((1 - p * (1 - z)) *
                Nat.choose ((r + 2 * m) + 2) s) := by
          apply mul_le_mul_of_nonneg_left _ (pow_nonneg hq0 _)
          have hpascal := choose_add_two (r + 2 * m) s
          have hmid' :
              p * (1 - z) * Nat.choose ((r + 2 * m) + 2) s ≤
                2 * (1 - z) * lowerTerm 1
                  (fun t ↦ (Nat.choose (r + 2 * m) t : ℝ)) s := by
            calc
              p * (1 - z) * Nat.choose ((r + 2 * m) + 2) s =
                  (p * Nat.choose ((r + 2 * m) + 2) s) * (1 - z) := by ring
              _ ≤ (2 * lowerTerm 1
                    (fun t ↦ (Nat.choose (r + 2 * m) t : ℝ)) s) * (1 - z) :=
                mul_le_mul_of_nonneg_right hmid (sub_nonneg.mpr hz1)
              _ = 2 * (1 - z) * lowerTerm 1
                    (fun t ↦ (Nat.choose (r + 2 * m) t : ℝ)) s := by ring
          push_cast at hpascal hmid' ⊢
          calc
            (Nat.choose (r + 2 * m) s : ℝ) +
                  2 * z * lowerTerm 1
                    (fun t ↦ (Nat.choose (r + 2 * m) t : ℝ)) s +
                  lowerTerm 2
                    (fun t ↦ (Nat.choose (r + 2 * m) t : ℝ)) s =
                Nat.choose ((r + 2 * m) + 2) s -
                  2 * (1 - z) * lowerTerm 1
                    (fun t ↦ (Nat.choose (r + 2 * m) t : ℝ)) s := by
              rw [hpascal]
              ring
            _ ≤ Nat.choose ((r + 2 * m) + 2) s -
                  p * (1 - z) * Nat.choose ((r + 2 * m) + 2) s := by
              exact sub_le_sub_left hmid' _
            _ = (1 - p * (1 - z)) *
                  Nat.choose ((r + 2 * m) + 2) s := by ring
        _ = (1 - p * (1 - z)) ^ (m + 1) *
              Nat.choose (r + 2 * (m + 1)) s := by
          push_cast
          rw [pow_succ]
          ring_nf

/-- Exponential form of the exact recurrence bound. -/
lemma pairedSlicePartition_le_exp
    (m r s : ℕ) {p u : ℝ}
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hu0 : 0 ≤ u)
    (hstep : PairedSliceStepBound p m r s) :
    pairedSlicePartition m r s (Real.exp (-u)) ≤
      Real.exp (-p * (1 - Real.exp (-u)) * m) *
        Nat.choose (r + 2 * m) s := by
  have hz0 : 0 ≤ Real.exp (-u) := (Real.exp_pos _).le
  have hz1 : Real.exp (-u) ≤ 1 := by
    rw [Real.exp_le_one_iff]
    linarith
  calc
    pairedSlicePartition m r s (Real.exp (-u)) ≤
        (1 - p * (1 - Real.exp (-u))) ^ m *
          Nat.choose (r + 2 * m) s :=
      pairedSlicePartition_le m r s hp0 hp1 hz0 hz1 hstep
    _ ≤ Real.exp (-p * (1 - Real.exp (-u)) * m) *
          Nat.choose (r + 2 * m) s := by
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      calc
        (1 - p * (1 - Real.exp (-u))) ^ m ≤
            Real.exp (-(p * (1 - Real.exp (-u))) * m) := by
          calc
            (1 - p * (1 - Real.exp (-u))) ^ m ≤
                Real.exp (-(p * (1 - Real.exp (-u)))) ^ m :=
              pow_le_pow_left₀
                (by nlinarith [show Real.exp (-u) ≤ 1 from hz1])
                (Real.one_sub_le_exp_neg (p * (1 - Real.exp (-u)))) m
            _ = Real.exp (-(p * (1 - Real.exp (-u))) * m) := by
              symm
              calc
                Real.exp (-(p * (1 - Real.exp (-u))) * (m : ℝ)) =
                    Real.exp ((m : ℝ) * (-(p * (1 - Real.exp (-u))))) := by
                  congr 1
                  ring
                _ = Real.exp (-(p * (1 - Real.exp (-u)))) ^ m :=
                  Real.exp_nat_mul _ _
        _ = Real.exp (-p * (1 - Real.exp (-u)) * m) := by
          congr 1
          ring

/-- On `[0,1]`, the loss `1 - exp (-u)` is at least `u / 2`. -/
lemma half_mul_le_one_sub_exp_neg {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u ≤ 1) :
    u / 2 ≤ 1 - Real.exp (-u) := by
  have hpos : 0 < 1 + u := by linarith
  have hexp : 1 + u ≤ Real.exp u := by
    simpa [add_comm] using Real.add_one_le_exp u
  have hinv : (Real.exp u)⁻¹ ≤ (1 + u)⁻¹ := by
    exact inv_anti₀ hpos hexp
  have hsquare : u ^ 2 ≤ u := by nlinarith
  have hfrac : (1 + u)⁻¹ ≤ 1 - u / 2 := by
    rw [← one_mul ((1 + u)⁻¹), mul_inv_le_iff₀ hpos]
    nlinarith
  rw [Real.exp_neg]
  linarith

/-- Fully discharged exponential estimate for the canonical recurrence, in
terms of an integer reserve surviving all exposed pairs. -/
lemma pairedSlicePartition_le_exp_of_reserve
    (m r s A T : ℕ) (u : ℝ)
    (hA : 1 ≤ A) (h2A : 2 * A ≤ T)
    (hsel : A + 2 * m ≤ s)
    (hunsel : A + 2 * m ≤ r + 2 * m - s)
    (hTotal : r + 2 * m ≤ T)
    (hu0 : 0 ≤ u) (hu1 : u ≤ 1) :
    pairedSlicePartition m r s (Real.exp (-u)) ≤
      Real.exp (-((A : ℝ) / T) ^ 2 * m * u) *
        Nat.choose (r + 2 * m) s := by
  let p : ℝ := 2 * (A : ℝ) ^ 2 / (T : ℝ) ^ 2
  have hT : 0 < (T : ℝ) := by
    exact_mod_cast lt_of_lt_of_le (by omega : 0 < 2 * A) h2A
  have hp0 : 0 ≤ p := by positivity
  have hsquares : 4 * (A : ℝ) ^ 2 ≤ (T : ℝ) ^ 2 := by
    have h2A' : (2 : ℝ) * A ≤ T := by exact_mod_cast h2A
    nlinarith [sq_nonneg ((T : ℝ) - 2 * A)]
  have hp1 : p ≤ 1 := by
    dsimp [p]
    apply (div_le_one (sq_pos_of_pos hT)).2
    nlinarith
  have hstep : PairedSliceStepBound p m r s := by
    exact pairedSliceStepBound_of_reserve m r s A T hA hsel hunsel hTotal
  have hbase := pairedSlicePartition_le_exp m r s hp0 hp1 hu0 hstep
  calc
    pairedSlicePartition m r s (Real.exp (-u)) ≤
        Real.exp (-p * (1 - Real.exp (-u)) * m) *
          Nat.choose (r + 2 * m) s := hbase
    _ ≤ Real.exp (-((A : ℝ) / T) ^ 2 * m * u) *
          Nat.choose (r + 2 * m) s := by
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      apply Real.exp_le_exp.mpr
      have hloss := half_mul_le_one_sub_exp_neg hu0 hu1
      dsimp [p]
      have hT2 : 0 < (T : ℝ) ^ 2 := sq_pos_of_pos hT
      field_simp [ne_of_gt hT]
      nlinarith

/-! A canonical assignment model for the slice recurrence. -/

abbrev PairPattern := Bool × Bool

def pairPatternWeight (b : PairPattern) : ℕ :=
  (if b.1 then 1 else 0) + (if b.2 then 1 else 0)

def pairPatternSingleton (b : PairPattern) : ℕ :=
  if b.1 ≠ b.2 then 1 else 0

def finSuccFunEquiv (m : ℕ) :
    (Fin (m + 1) → PairPattern) ≃ PairPattern × (Fin m → PairPattern) :=
  ((finSuccEquiv m).arrowCongr (Equiv.refl PairPattern)).trans
    Equiv.piOptionEquivProd

def pairAssignmentWeight : ∀ m : ℕ, (Fin m → PairPattern) → ℕ
  | 0, _ => 0
  | m + 1, y =>
      pairPatternWeight (finSuccFunEquiv m y).1 +
        pairAssignmentWeight m (finSuccFunEquiv m y).2

def pairAssignmentSingletons : ∀ m : ℕ, (Fin m → PairPattern) → ℕ
  | 0, _ => 0
  | m + 1, y =>
      pairPatternSingleton (finSuccFunEquiv m y).1 +
        pairAssignmentSingletons m (finSuccFunEquiv m y).2

noncomputable def pairAssignmentPartition (m r s : ℕ) (z : ℝ) : ℝ :=
  ∑ y : Fin m → PairPattern,
    z ^ pairAssignmentSingletons m y *
      lowerTerm (pairAssignmentWeight m y)
        (fun t ↦ (Nat.choose r t : ℝ)) s

lemma lowerTerm_add (a b : ℕ) (f : ℕ → ℝ) (s : ℕ) :
    lowerTerm (a + b) f s =
      lowerTerm a (fun t ↦ lowerTerm b f t) s := by
  by_cases hab : a + b ≤ s
  · have ha : a ≤ s := by omega
    have hb : b ≤ s - a := by omega
    simp [lowerTerm, hab, ha, hb, Nat.sub_sub]
  · by_cases ha : a ≤ s
    · have hb : ¬b ≤ s - a := by omega
      simp [lowerTerm, hab, ha, hb]
    · simp [lowerTerm, hab, ha]

lemma sum_mul_lowerTerm_add {X : Type*} [Fintype X]
    (a s : ℕ) (g : X → ℝ) (w : X → ℕ) (f : ℕ → ℝ) :
    (∑ x, g x * lowerTerm (a + w x) f s) =
      lowerTerm a (fun t ↦ ∑ x, g x * lowerTerm (w x) f t) s := by
  classical
  by_cases ha : a ≤ s
  · rw [lowerTerm, if_pos ha]
    apply Finset.sum_congr rfl
    intro x _
    rw [lowerTerm_add, lowerTerm, if_pos ha]
  · rw [lowerTerm, if_neg ha]
    apply Finset.sum_eq_zero
    intro x _
    have hax : ¬a + w x ≤ s := by omega
    simp [lowerTerm, hax]

/-- The canonical assignment sum satisfies the exact distinguished-pair
recurrence. -/
lemma pairAssignmentPartition_eq (m r s : ℕ) (z : ℝ) :
    pairAssignmentPartition m r s z = pairedSlicePartition m r s z := by
  induction m generalizing s with
  | zero =>
      simp [pairAssignmentPartition, pairAssignmentWeight,
        pairAssignmentSingletons, lowerTerm]
  | succ m ih =>
      rw [pairAssignmentPartition]
      calc
        (∑ y : Fin (m + 1) → PairPattern,
            z ^ pairAssignmentSingletons (m + 1) y *
              lowerTerm (pairAssignmentWeight (m + 1) y)
                (fun t ↦ (Nat.choose r t : ℝ)) s) =
            ∑ q : PairPattern × (Fin m → PairPattern),
              z ^ pairAssignmentSingletons (m + 1)
                    ((finSuccFunEquiv m).symm q) *
                lowerTerm (pairAssignmentWeight (m + 1)
                    ((finSuccFunEquiv m).symm q))
                  (fun t ↦ (Nat.choose r t : ℝ)) s := by
          exact Fintype.sum_equiv (finSuccFunEquiv m) _ _ (fun _ ↦ rfl)
        _ = ∑ b : PairPattern, ∑ y : Fin m → PairPattern,
              z ^ (pairPatternSingleton b + pairAssignmentSingletons m y) *
                lowerTerm (pairPatternWeight b + pairAssignmentWeight m y)
                  (fun t ↦ (Nat.choose r t : ℝ)) s := by
          rw [Fintype.sum_prod_type]
          apply Finset.sum_congr rfl
          intro b _
          apply Finset.sum_congr rfl
          intro y _
          simp [pairAssignmentSingletons, pairAssignmentWeight]
        _ = pairAssignmentPartition m r s z +
              2 * z * lowerTerm 1 (fun t ↦ pairAssignmentPartition m r t z) s +
              lowerTerm 2 (fun t ↦ pairAssignmentPartition m r t z) s := by
          have hhead : ∀ b : PairPattern,
              (∑ y : Fin m → PairPattern,
                z ^ (pairPatternSingleton b + pairAssignmentSingletons m y) *
                  lowerTerm (pairPatternWeight b + pairAssignmentWeight m y)
                    (fun t ↦ (Nat.choose r t : ℝ)) s) =
                z ^ pairPatternSingleton b *
                  lowerTerm (pairPatternWeight b)
                    (fun t ↦ pairAssignmentPartition m r t z) s := by
            intro b
            calc
              (∑ y : Fin m → PairPattern,
                  z ^ (pairPatternSingleton b + pairAssignmentSingletons m y) *
                    lowerTerm (pairPatternWeight b + pairAssignmentWeight m y)
                      (fun t ↦ (Nat.choose r t : ℝ)) s) =
                  z ^ pairPatternSingleton b *
                    ∑ y : Fin m → PairPattern,
                      z ^ pairAssignmentSingletons m y *
                        lowerTerm (pairPatternWeight b + pairAssignmentWeight m y)
                          (fun t ↦ (Nat.choose r t : ℝ)) s := by
                rw [Finset.mul_sum]
                apply Finset.sum_congr rfl
                intro y _
                rw [pow_add]
                ring
              _ = z ^ pairPatternSingleton b *
                    lowerTerm (pairPatternWeight b)
                      (fun t ↦ pairAssignmentPartition m r t z) s := by
                congr 1
                rw [sum_mul_lowerTerm_add]
                rfl
          calc
            (∑ b : PairPattern, ∑ y : Fin m → PairPattern,
                z ^ (pairPatternSingleton b + pairAssignmentSingletons m y) *
                  lowerTerm (pairPatternWeight b + pairAssignmentWeight m y)
                    (fun t ↦ (Nat.choose r t : ℝ)) s) =
                ∑ b : PairPattern, z ^ pairPatternSingleton b *
                  lowerTerm (pairPatternWeight b)
                    (fun t ↦ pairAssignmentPartition m r t z) s := by
              apply Finset.sum_congr rfl
              intro b _
              exact hhead b
            _ = _ := by
              rw [Fintype.sum_prod_type]
              simp only [Fintype.univ_bool, Finset.mem_singleton, Bool.true_eq_false, not_false_eq_true, Finset.sum_insert,
    Finset.sum_singleton]
              simp [pairPatternSingleton, pairPatternWeight, lowerTerm]
              split_ifs <;> ring
        _ = pairedSlicePartition m r s z +
              2 * z * lowerTerm 1 (fun t ↦ pairedSlicePartition m r t z) s +
              lowerTerm 2 (fun t ↦ pairedSlicePartition m r t z) s := by
          simp_rw [ih]
        _ = pairedSlicePartition (m + 1) r s z := rfl

/-- The finset of all endpoints of an embedded disjoint-pair family. -/
noncomputable def pairEndpointFinset {K : Type v} {I : Type u}
    [Fintype K] [Fintype I] [DecidableEq I] (p : PairEmbedding K I) : Finset I :=
  Finset.univ.map p

noncomputable def pairRangeEquiv {K : Type v} {I : Type u}
    [Fintype K] [Fintype I] [DecidableEq I] (p : PairEmbedding K I) :
    K × Bool ≃ pairEndpointFinset p :=
  Equiv.ofBijective
    (fun z ↦ ⟨p z, by simp [pairEndpointFinset]⟩)
    ⟨fun z w h ↦ p.injective (Subtype.ext_iff.mp h), fun i ↦ by
      rcases Finset.mem_map.mp i.prop with ⟨z, -, hz⟩
      exact ⟨z, Subtype.ext hz⟩⟩

@[simp] lemma pairRangeEquiv_apply {K : Type v} {I : Type u}
    [Fintype K] [Fintype I] [DecidableEq I] (p : PairEmbedding K I)
    (z : K × Bool) : (pairRangeEquiv p z : I) = p z := rfl

noncomputable def pairAssignmentOnRange {K : Type v} {I : Type u}
    [Fintype K] [Fintype I] [DecidableEq I] (p : PairEmbedding K I)
    (y : K × Bool → Bool) : pairEndpointFinset p → Bool :=
  fun i ↦ y ((pairRangeEquiv p).symm i)

@[simp] lemma pairAssignmentOnRange_apply {K : Type v} {I : Type u}
    [Fintype K] [Fintype I] [DecidableEq I] (p : PairEmbedding K I)
    (y : K × Bool → Bool) (z : K × Bool) :
    pairAssignmentOnRange p y (pairRangeEquiv p z) = y z := by
  simp [pairAssignmentOnRange]

def PairSliceExtensions {K : Type v} {I : Type u}
    [Fintype K] [Fintype I] [DecidableEq I]
    (p : PairEmbedding K I) (y : K × Bool → Bool) (s : ℕ) :=
  {x : BoolSlice I s // ∀ z, x.1 (p z) = y z}

noncomputable instance {K : Type v} {I : Type u}
    [Fintype K] [Fintype I] [DecidableEq I]
    (p : PairEmbedding K I) (y : K × Bool → Bool) (s : ℕ) :
    Fintype (PairSliceExtensions p y s) :=
  Fintype.ofInjective Subtype.val Subtype.val_injective

def pairSliceExtensionsEquiv {K : Type v} {I : Type u}
    [Fintype K] [Fintype I] [DecidableEq I]
    (p : PairEmbedding K I) (y : K × Bool → Bool) (s : ℕ) :
    PairSliceExtensions p y s ≃
      BoolSliceExtensions (pairEndpointFinset p) (pairAssignmentOnRange p y) s where
  toFun x := ⟨x.1, fun i ↦ by
    let z := (pairRangeEquiv p).symm i
    have hi : p z = i := by
      change ((pairRangeEquiv p z : pairEndpointFinset p) : I) = i
      rw [Equiv.apply_symm_apply]
    rw [← hi]
    exact x.2 z⟩
  invFun x := ⟨x.1, fun z ↦ by
    simpa using x.2 (pairRangeEquiv p z)⟩
  left_inv _ := rfl
  right_inv _ := rfl

lemma boolWeight_le_of_boolSliceExtension {I : Type u}
    [Fintype I] [DecidableEq I] (J : Finset I) (y : J → Bool) (s : ℕ)
    (x : BoolSliceExtensions J y s) : boolWeight y ≤ s := by
  let z : {i : I // i ∉ J} → Bool := fun i ↦ x.1.1 i
  have hw := boolWeight_extendBool J y z
  have hext : extendBool J y z = x.1.1 := by
    funext i
    by_cases hi : i ∈ J
    · simpa [extendBool, hi] using (x.2 ⟨i, hi⟩).symm
    · simp [extendBool, hi, z]
  rw [hext, x.1.2] at hw
  omega

lemma card_pairEndpointFinset {K : Type v} {I : Type u}
    [Fintype K] [Fintype I] [DecidableEq I] (p : PairEmbedding K I) :
    (pairEndpointFinset p).card = 2 * Fintype.card K := by
  simp [pairEndpointFinset, mul_comm]

/-- Exact number of slice completions of a prescribed assignment on all
pair endpoints. -/
lemma card_pairSliceExtensions {K : Type v} {I : Type u}
    [Fintype K] [Fintype I] [DecidableEq I]
    (p : PairEmbedding K I) (y : K × Bool → Bool) (s : ℕ) :
    (Fintype.card (PairSliceExtensions p y s) : ℝ) =
      lowerTerm (boolWeight (pairAssignmentOnRange p y))
        (fun t ↦ (Nat.choose (Fintype.card I - 2 * Fintype.card K) t : ℝ)) s := by
  classical
  by_cases hy : boolWeight (pairAssignmentOnRange p y) ≤ s
  · rw [lowerTerm, if_pos hy]
    norm_cast
    rw [Fintype.card_congr (pairSliceExtensionsEquiv p y s)]
    rw [card_boolSliceExtensions _ _ _ hy, card_pairEndpointFinset]
  · rw [lowerTerm, if_neg hy]
    have hempty : IsEmpty (PairSliceExtensions p y s) := ⟨fun x ↦ by
      apply hy
      exact boolWeight_le_of_boolSliceExtension _ _ _
        (pairSliceExtensionsEquiv p y s x)⟩
    rw [Fintype.card_eq_zero]
    norm_num

def pairEndpointAssignment {K : Type v} {I : Type u}
    (p : PairEmbedding K I) (x : I → Bool) : K × Bool → Bool :=
  fun z ↦ x (p z)

def endpointSingletonCount {K : Type v} [Fintype K] [DecidableEq K]
    (y : K × Bool → Bool) : ℕ :=
  (Finset.univ.filter fun k ↦ y (k, false) ≠ y (k, true)).card

@[simp] lemma endpointSingletonCount_assignment {K : Type v} {I : Type u}
    [Fintype K] [DecidableEq K] (p : PairEmbedding K I) (x : I → Bool) :
    endpointSingletonCount (pairEndpointAssignment p x) = singletonPairCount p x := rfl

lemma slice_singleton_power_sum_eq_assignment_sum
    {K : Type v} {I : Type u}
    [Fintype K] [DecidableEq K] [Fintype I] [DecidableEq I]
    (p : PairEmbedding K I) (s : ℕ) [Nonempty (BoolSlice I s)] (z : ℝ) :
    (∑ x : BoolSlice I s, z ^ singletonPairCount p x.1) =
      ∑ y : K × Bool → Bool,
        z ^ endpointSingletonCount y * Fintype.card (PairSliceExtensions p y s) := by
  classical
  have hfiber := Finset.sum_fiberwise_of_maps_to
    (s := (Finset.univ : Finset (BoolSlice I s)))
    (t := (Finset.univ : Finset (K × Bool → Bool)))
    (g := fun x ↦ pairEndpointAssignment p x.1)
    (fun _ _ ↦ Finset.mem_univ _)
    (fun x ↦ z ^ singletonPairCount p x.1)
  rw [← hfiber]
  apply Finset.sum_congr rfl
  intro y _
  have hcard :
      ((Finset.univ.filter fun x : BoolSlice I s ↦
          pairEndpointAssignment p x.1 = y).card) =
        Fintype.card (PairSliceExtensions p y s) := by
    let e : PairSliceExtensions p y s ≃
        {x : BoolSlice I s // x ∈ (Finset.univ.filter fun x ↦
          pairEndpointAssignment p x.1 = y)} := {
      toFun := fun x ↦ ⟨x.1, by
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        funext q
        exact x.2 q⟩
      invFun := fun x ↦ ⟨x.1, fun q ↦ by
        have hx : pairEndpointAssignment p x.1.1 = y := by
          simpa only [Finset.mem_filter, Finset.mem_univ, true_and] using x.2
        exact congrFun hx q⟩
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ rfl }
    rw [← Fintype.card_coe]
    exact (Fintype.card_congr e).symm
  change (∑ x ∈ Finset.univ.filter (fun x : BoolSlice I s ↦
      pairEndpointAssignment p x.1 = y), z ^ singletonPairCount p x.1) = _
  calc
    (∑ x ∈ Finset.univ.filter (fun x : BoolSlice I s ↦
        pairEndpointAssignment p x.1 = y), z ^ singletonPairCount p x.1) =
        ∑ _x ∈ Finset.univ.filter (fun x : BoolSlice I s ↦
            pairEndpointAssignment p x.1 = y),
          z ^ endpointSingletonCount y := by
      apply Finset.sum_congr rfl
      intro x hx
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx
      rw [← hx, endpointSingletonCount_assignment]
    _ = z ^ endpointSingletonCount y *
          (Finset.univ.filter fun x : BoolSlice I s ↦
            pairEndpointAssignment p x.1 = y).card := by
      rw [Finset.sum_const, nsmul_eq_mul]
      ring
    _ = z ^ endpointSingletonCount y *
          Fintype.card (PairSliceExtensions p y s) := by rw [hcard]

lemma pairAssignmentWeight_eq_sum (m : ℕ) (y : Fin m → PairPattern) :
    pairAssignmentWeight m y = ∑ i, pairPatternWeight (y i) := by
  induction m with
  | zero => simp [pairAssignmentWeight]
  | succ m ih =>
      rw [pairAssignmentWeight, Fin.sum_univ_succ]
      simp [finSuccFunEquiv, ih]

lemma pairAssignmentSingletons_eq_sum (m : ℕ) (y : Fin m → PairPattern) :
    pairAssignmentSingletons m y = ∑ i, pairPatternSingleton (y i) := by
  induction m with
  | zero => simp [pairAssignmentSingletons]
  | succ m ih =>
      rw [pairAssignmentSingletons, Fin.sum_univ_succ]
      simp [finSuccFunEquiv, ih]

noncomputable def endpointAssignmentEquivFin (K : Type v) [Fintype K] :
    (K × Bool → Bool) ≃ (Fin (Fintype.card K) → PairPattern) where
  toFun y i :=
    (y ((Fintype.equivFin K).symm i, false),
      y ((Fintype.equivFin K).symm i, true))
  invFun q z := if z.2 then (q (Fintype.equivFin K z.1)).2
    else (q (Fintype.equivFin K z.1)).1
  left_inv y := by
    funext z
    cases z with
    | mk k b => cases b <;> simp
  right_inv q := by
    funext i
    simp

lemma boolWeight_pairAssignmentOnRange_eq {K : Type v} {I : Type u}
    [Fintype K] [DecidableEq K] [Fintype I] [DecidableEq I]
    (p : PairEmbedding K I) (y : K × Bool → Bool) :
    boolWeight (pairAssignmentOnRange p y) =
      pairAssignmentWeight (Fintype.card K) (endpointAssignmentEquivFin K y) := by
  rw [boolWeight_eq_sum, pairAssignmentWeight_eq_sum]
  calc
    (∑ i : pairEndpointFinset p,
        if pairAssignmentOnRange p y i then 1 else 0) =
        ∑ z : K × Bool, if y z then 1 else 0 := by
      calc
        (∑ i : pairEndpointFinset p,
            if pairAssignmentOnRange p y i then 1 else 0) =
            ∑ z : K × Bool,
              if pairAssignmentOnRange p y (pairRangeEquiv p z) then 1 else 0 :=
          ((pairRangeEquiv p).sum_comp
            (fun i ↦ if pairAssignmentOnRange p y i then 1 else 0)).symm
        _ = _ := by simp
    _ = ∑ k : K,
          ((if y (k, false) then 1 else 0) +
            if y (k, true) then 1 else 0) := by
      rw [Fintype.sum_prod_type]
      apply Finset.sum_congr rfl
      intro k _
      rw [Fintype.sum_bool]
      ring
    _ = ∑ i : Fin (Fintype.card K),
          ((if y ((Fintype.equivFin K).symm i, false) then 1 else 0) +
            if y ((Fintype.equivFin K).symm i, true) then 1 else 0) := by
      exact ((Fintype.equivFin K).symm.sum_comp fun k ↦
        ((if y (k, false) then 1 else 0) +
          if y (k, true) then 1 else 0)).symm
    _ = ∑ i : Fin (Fintype.card K),
          pairPatternWeight (endpointAssignmentEquivFin K y i) := by
      apply Finset.sum_congr rfl
      intro i _
      rfl

lemma endpointSingletonCount_eq {K : Type v} [Fintype K] [DecidableEq K]
    (y : K × Bool → Bool) :
    endpointSingletonCount y =
      pairAssignmentSingletons (Fintype.card K) (endpointAssignmentEquivFin K y) := by
  rw [endpointSingletonCount, Finset.card_eq_sum_ones, Finset.sum_filter,
    pairAssignmentSingletons_eq_sum]
  calc
    (∑ k : K, if y (k, false) ≠ y (k, true) then 1 else 0) =
        ∑ i : Fin (Fintype.card K),
          if y ((Fintype.equivFin K).symm i, false) ≠
            y ((Fintype.equivFin K).symm i, true) then 1 else 0 := by
      exact ((Fintype.equivFin K).symm.sum_comp fun k ↦
        if y (k, false) ≠ y (k, true) then 1 else 0).symm
    _ = ∑ i : Fin (Fintype.card K),
          pairPatternSingleton (endpointAssignmentEquivFin K y i) := by
      apply Finset.sum_congr rfl
      intro i _
      rfl

lemma slice_singleton_power_sum_eq_pairedSlicePartition
    {K : Type v} {I : Type u}
    [Fintype K] [DecidableEq K] [Fintype I] [DecidableEq I]
    (p : PairEmbedding K I) (s : ℕ) [Nonempty (BoolSlice I s)] (z : ℝ) :
    (∑ x : BoolSlice I s, z ^ singletonPairCount p x.1) =
      pairedSlicePartition (Fintype.card K)
        (Fintype.card I - 2 * Fintype.card K) s z := by
  rw [slice_singleton_power_sum_eq_assignment_sum]
  simp_rw [card_pairSliceExtensions]
  calc
    (∑ y : K × Bool → Bool,
        z ^ endpointSingletonCount y *
          lowerTerm (boolWeight (pairAssignmentOnRange p y))
            (fun t ↦ (Nat.choose (Fintype.card I - 2 * Fintype.card K) t : ℝ)) s) =
      ∑ q : Fin (Fintype.card K) → PairPattern,
        z ^ pairAssignmentSingletons (Fintype.card K) q *
          lowerTerm (pairAssignmentWeight (Fintype.card K) q)
            (fun t ↦ (Nat.choose (Fintype.card I - 2 * Fintype.card K) t : ℝ)) s := by
      exact Fintype.sum_equiv (endpointAssignmentEquivFin K) _ _ fun y ↦ by
        rw [endpointSingletonCount_eq, boolWeight_pairAssignmentOnRange_eq]
    _ = pairAssignmentPartition (Fintype.card K)
          (Fintype.card I - 2 * Fintype.card K) s z := rfl
    _ = pairedSlicePartition (Fintype.card K)
          (Fintype.card I - 2 * Fintype.card K) s z :=
      pairAssignmentPartition_eq _ _ _ _

/-- Characteristic function of a linear form on a uniform Boolean slice. -/
noncomputable def sliceCharFun {I : Type u} [Fintype I] [DecidableEq I] (s : ℕ)
    [Nonempty (BoolSlice I s)] (a : I → ℝ) (t : ℝ) : ℂ :=
  finCharFun (BoolSlice I s) (fun x ↦ ∑ i, a i * (if x.1 i then 1 else 0)) t

/-- The normalized Laplace transform of the number of singleton embedded
pairs on a uniform Boolean slice. -/
noncomputable def sliceSingletonLaplace {K : Type v} {I : Type u}
    [Fintype K] [DecidableEq K] [Fintype I] [DecidableEq I]
    (p : PairEmbedding K I) (s : ℕ) [Nonempty (BoolSlice I s)] (u : ℝ) : ℝ :=
  (∑ x : BoolSlice I s, Real.exp (-(singletonPairCount p x.1 : ℝ) * u)) /
    Fintype.card (BoolSlice I s)

lemma sliceSingletonLaplace_eq_pairedSlicePartition
    {K : Type v} {I : Type u}
    [Fintype K] [DecidableEq K] [Fintype I] [DecidableEq I]
    (p : PairEmbedding K I) (s : ℕ) [Nonempty (BoolSlice I s)] (u : ℝ) :
    sliceSingletonLaplace p s u =
      pairedSlicePartition (Fintype.card K)
          (Fintype.card I - 2 * Fintype.card K) s (Real.exp (-u)) /
        Nat.choose (Fintype.card I) s := by
  rw [sliceSingletonLaplace, card_boolSlice]
  congr 1
  rw [← slice_singleton_power_sum_eq_pairedSlicePartition p s (Real.exp (-u))]
  apply Finset.sum_congr rfl
  intro x _
  rw [← Real.exp_nat_mul]
  congr 1
  push_cast
  ring

/-- Assumption-free slice Laplace estimate once an integer reserve remains
after exposing all prescribed pairs. -/
lemma sliceSingletonLaplace_le_exp_of_reserve
    {K : Type v} {I : Type u}
    [Fintype K] [DecidableEq K] [Fintype I] [DecidableEq I]
    (p : PairEmbedding K I) (s A : ℕ) [Nonempty (BoolSlice I s)] (u : ℝ)
    (hA : 1 ≤ A) (h2A : 2 * A ≤ Fintype.card I)
    (hsel : A + 2 * Fintype.card K ≤ s)
    (hunsel : A + 2 * Fintype.card K ≤ Fintype.card I - s)
    (hu0 : 0 ≤ u) (hu1 : u ≤ 1) :
    sliceSingletonLaplace p s u ≤
      Real.exp (-((A : ℝ) / Fintype.card I) ^ 2 * Fintype.card K * u) := by
  have hpairs : 2 * Fintype.card K ≤ Fintype.card I := by
    have hp := Fintype.card_le_of_injective p p.injective
    simpa [mul_comm] using hp
  have htotal :
      Fintype.card I - 2 * Fintype.card K + 2 * Fintype.card K =
        Fintype.card I := Nat.sub_add_cancel hpairs
  have hpart := pairedSlicePartition_le_exp_of_reserve
    (Fintype.card K) (Fintype.card I - 2 * Fintype.card K) s A
      (Fintype.card I) u hA h2A hsel (by simpa [htotal] using hunsel)
      (by omega) hu0 hu1
  rw [sliceSingletonLaplace_eq_pairedSlicePartition]
  have hchoose : (0 : ℝ) < Nat.choose (Fintype.card I) s := by
    rw [← card_boolSlice]
    exact_mod_cast (Fintype.card_pos : 0 < Fintype.card (BoolSlice I s))
  apply (div_le_iff₀ hchoose).2
  calc
    pairedSlicePartition (Fintype.card K)
          (Fintype.card I - 2 * Fintype.card K) s (Real.exp (-u)) ≤
        Real.exp (-((A : ℝ) / Fintype.card I) ^ 2 * Fintype.card K * u) *
          Nat.choose
            (Fintype.card I - 2 * Fintype.card K + 2 * Fintype.card K) s := hpart
    _ = Real.exp (-((A : ℝ) / Fintype.card I) ^ 2 * Fintype.card K * u) *
          Nat.choose (Fintype.card I) s := by rw [htotal]

/-- Exact Fourier-to-combinatorics reduction behind KSSS Lemma 4.8.  Pair
swapping makes the orientations conditionally independent; all remaining
work is the lower-tail estimate for the number of singleton pairs. -/
lemma norm_sliceCharFun_le_sliceSingletonLaplace
    {K : Type v} {I : Type u}
    [Fintype K] [DecidableEq K] [Fintype I] [DecidableEq I]
    (p : PairEmbedding K I) (s : ℕ) [Nonempty (BoolSlice I s)]
    (a : I → ℝ) (t delta : ℝ) (q : K → ℝ)
    (hdelta : 0 ≤ delta)
    (hqcenter : ∀ k, IsCenteredModOne
      (t * (a (p (k, false)) - a (p (k, true))) / (2 * Real.pi)) (q k))
    (hqdelta : ∀ k, delta ≤ |q k|) :
    ‖sliceCharFun s a t‖ ≤ sliceSingletonLaplace p s (delta ^ 2) := by
  let a' : I → ℝ := fun i ↦ t * a i
  let phase : BoolSlice I s → ℂ := fun x ↦
    Complex.exp (((∑ i, a' i * boolIndicator (x.1 i) : ℝ) : ℂ) * Complex.I)
  have hchar : sliceCharFun s a t = finExpectation (BoolSlice I s) phase := by
    rw [sliceCharFun, finCharFun]
    apply congrArg (fun z : ℂ ↦ z / (Fintype.card (BoolSlice I s) : ℂ))
    apply Finset.sum_congr rfl
    intro x _
    apply congrArg Complex.exp
    apply congrArg (fun z : ℂ ↦ z * Complex.I)
    norm_cast
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    cases h : x.1 i <;> simp [a', boolIndicator, h]
  rw [hchar]
  calc
    ‖finExpectation (BoolSlice I s) phase‖ ≤
        (∑ x : BoolSlice I s,
          ‖finExpectation (K → Bool)
            (fun σ ↦ phase (slicePairSwap p σ s x))‖) /
          Fintype.card (BoolSlice I s) :=
      norm_finExpectation_le_average_orbit_norm
        (fun σ ↦ slicePairSwap p σ s) phase
    _ ≤ (∑ x : BoolSlice I s,
          Real.exp (-(singletonPairCount p x.1 : ℝ) * delta ^ 2)) /
          Fintype.card (BoolSlice I s) := by
      apply div_le_div_of_nonneg_right
      · apply Finset.sum_le_sum
        intro x _
        simpa [phase, a'] using
          norm_pairSwap_orbit_average_le p a' q x.1
            hdelta (fun k ↦ by simpa [a', mul_sub] using hqcenter k) hqdelta
      · positivity
    _ = sliceSingletonLaplace p s (delta ^ 2) := by
      rw [sliceSingletonLaplace]

lemma norm_sliceCharFun_le_exp_of_reserve
    {K : Type v} {I : Type u}
    [Fintype K] [DecidableEq K] [Fintype I] [DecidableEq I]
    (p : PairEmbedding K I) (s A : ℕ) [Nonempty (BoolSlice I s)]
    (a : I → ℝ) (t delta : ℝ) (q : K → ℝ)
    (hA : 1 ≤ A) (h2A : 2 * A ≤ Fintype.card I)
    (hsel : A + 2 * Fintype.card K ≤ s)
    (hunsel : A + 2 * Fintype.card K ≤ Fintype.card I - s)
    (hdelta0 : 0 ≤ delta) (hdelta1 : delta ≤ 1)
    (hqcenter : ∀ k, IsCenteredModOne
      (t * (a (p (k, false)) - a (p (k, true))) / (2 * Real.pi)) (q k))
    (hqdelta : ∀ k, delta ≤ |q k|) :
    ‖sliceCharFun s a t‖ ≤
      Real.exp (-((A : ℝ) / Fintype.card I) ^ 2 *
        Fintype.card K * delta ^ 2) := by
  calc
    ‖sliceCharFun s a t‖ ≤ sliceSingletonLaplace p s (delta ^ 2) :=
      norm_sliceCharFun_le_sliceSingletonLaplace p s a t delta q
        hdelta0 hqcenter hqdelta
    _ ≤ Real.exp (-((A : ℝ) / Fintype.card I) ^ 2 *
          Fintype.card K * delta ^ 2) :=
      sliceSingletonLaplace_le_exp_of_reserve p s A (delta ^ 2)
        hA h2A hsel hunsel (sq_nonneg delta) (by nlinarith)

noncomputable def restrictPairEmbedding {K' : Type*} {K : Type v} {I : Type u}
    (p : PairEmbedding K I) (e : K' ↪ K) : PairEmbedding K' I :=
  (e.prodMap (Function.Embedding.refl Bool)).trans p

@[simp] lemma restrictPairEmbedding_apply {K' : Type*} {K : Type v} {I : Type u}
    (p : PairEmbedding K I) (e : K' ↪ K) (k : K') (b : Bool) :
    restrictPairEmbedding p e (k, b) = p (e k, b) := rfl

noncomputable def finEmbeddingOfCardLe (K : Type v) [Fintype K] {m : ℕ}
    (hm : m ≤ Fintype.card K) : Fin m ↪ K :=
  (Fin.castLEEmb hm).trans (Fintype.equivFin K).symm.toEmbedding

/-- KSSS Lemma 4.8, with completely explicit universal constants. -/
lemma norm_sliceCharFun_le_balanced
    {K : Type v} {I : Type u}
    [Fintype K] [DecidableEq K] [Fintype I] [DecidableEq I]
    (p : PairEmbedding K I) (s : ℕ) [Nonempty (BoolSlice I s)]
    (a : I → ℝ) (t delta c : ℝ) (q : K → ℝ)
    (hc0 : 0 < c) (hc1 : c ≤ 1 / 2)
    (hsel : c * Fintype.card I ≤ s)
    (hunsel : c * Fintype.card I ≤ Fintype.card I - s)
    (hdelta0 : 0 ≤ delta) (hdelta1 : delta ≤ 1 / 2)
    (hqcenter : ∀ k, IsCenteredModOne
      (t * (a (p (k, false)) - a (p (k, true))) / (2 * Real.pi)) (q k))
    (hqdelta : ∀ k, delta ≤ |q k|) :
    ‖sliceCharFun s a t‖ ≤
      Real.exp 1 * Real.exp (-(c ^ 3 / 256) * Fintype.card K * delta ^ 2) := by
  let N := Fintype.card I
  let M := Fintype.card K
  let Q := min s (N - s)
  let A := Q / 4
  let m := min M A
  have hpairs : 2 * M ≤ N := by
    have hp := Fintype.card_le_of_injective p p.injective
    simpa [M, N, mul_comm] using hp
  have hMN : M ≤ N := by omega
  have hQsel : Q ≤ s := min_le_left _ _
  have hQunsel : Q ≤ N - s := min_le_right _ _
  have hchoose : 0 < Nat.choose N s := by
    dsimp [N]
    rw [← card_boolSlice]
    exact Fintype.card_pos
  have hsN : s ≤ N := by
    by_contra hs
    have hz : Nat.choose N s = 0 :=
      Nat.choose_eq_zero_of_lt (Nat.lt_of_not_ge hs)
    omega
  have hcQ : c * (N : ℝ) ≤ Q := by
    have hselR : c * (N : ℝ) ≤ (s : ℝ) := by
      simpa [N] using hsel
    have hunselR : c * (N : ℝ) ≤ (N : ℝ) - s := by
      simpa [N] using hunsel
    change c * (N : ℝ) ≤ ((min s (N - s) : ℕ) : ℝ)
    rw [Nat.cast_min, Nat.cast_sub hsN]
    exact le_min hselR hunselR
  by_cases hlarge : 4 ≤ Q
  · have hA1 : 1 ≤ A := by omega
    have hAQ : 8 * A ≥ Q := by omega
    have h2A : 2 * A ≤ N := by omega
    have hmM : m ≤ M := min_le_left _ _
    have hmA : m ≤ A := min_le_right _ _
    have hreserve : A + 2 * m ≤ Q := by omega
    let e : Fin m ↪ K := finEmbeddingOfCardLe K hmM
    let p' : PairEmbedding (Fin m) I := restrictPairEmbedding p e
    let q' : Fin m → ℝ := fun k ↦ q (e k)
    have hbase :
        ‖sliceCharFun s a t‖ ≤
          Real.exp (-((A : ℝ) / N) ^ 2 * m * delta ^ 2) := by
      simpa [N, m, Fintype.card_fin] using
        (norm_sliceCharFun_le_exp_of_reserve p' s A a t delta q'
          hA1 (by simpa [N] using h2A)
          (by simpa [p', e, m] using hreserve.trans hQsel)
          (by simpa [p', e, m, N] using hreserve.trans hQunsel)
          hdelta0 (by linarith)
          (fun k ↦ by
            simpa [p', q', restrictPairEmbedding] using hqcenter (e k))
          (fun k ↦ hqdelta (e k)))
    have hNpos : 0 < (N : ℝ) := by
      exact_mod_cast (lt_of_lt_of_le (by omega : 0 < Q) (by omega : Q ≤ N))
    have hcA : c * (N : ℝ) ≤ 8 * A := by
      exact_mod_cast hcQ.trans (by exact_mod_cast hAQ)
    have hcdiv : c ≤ 8 * ((A : ℝ) / N) := by
      calc
        c ≤ (8 * (A : ℝ)) / N := (le_div_iff₀ hNpos).2 (by simpa using hcA)
        _ = 8 * ((A : ℝ) / N) := by ring
    have hcm : c * (M : ℝ) ≤ 4 * m := by
      by_cases hMA : M ≤ A
      · have hm : m = M := min_eq_left hMA
        rw [hm]
        have hc_le_one : c ≤ 1 := by linarith
        nlinarith
      · have hm : m = A := min_eq_right (Nat.le_of_not_ge hMA)
        rw [hm]
        have h2M : (2 : ℝ) * M ≤ N := by exact_mod_cast hpairs
        nlinarith
    have hsq : c ^ 2 ≤ 64 * ((A : ℝ) / N) ^ 2 := by
      nlinarith [sq_nonneg (8 * ((A : ℝ) / N) - c)]
    have hprod : c ^ 2 * (c * (M : ℝ)) ≤
        (64 * ((A : ℝ) / N) ^ 2) * (4 * m) :=
      mul_le_mul hsq hcm (mul_nonneg hc0.le (by positivity))
        (mul_nonneg (by norm_num) (sq_nonneg _))
    have hrate : (c ^ 3 / 256) * (M : ℝ) * delta ^ 2 ≤
        ((A : ℝ) / N) ^ 2 * m * delta ^ 2 := by
      have hd2 : 0 ≤ delta ^ 2 := sq_nonneg _
      nlinarith
    calc
      ‖sliceCharFun s a t‖ ≤
          Real.exp (-((A : ℝ) / N) ^ 2 * m * delta ^ 2) := hbase
      _ ≤ Real.exp 1 * Real.exp (-(c ^ 3 / 256) * M * delta ^ 2) := by
        rw [← Real.exp_add]
        apply Real.exp_le_exp.mpr
        linarith
      _ = _ := by simp [M]
  · have hQsmall : Q < 4 := Nat.lt_of_not_ge hlarge
    have hcNsmall : c * (N : ℝ) < 4 :=
      lt_of_le_of_lt hcQ (by exact_mod_cast hQsmall)
    have hcM : c * (M : ℝ) ≤ c * N :=
      mul_le_mul_of_nonneg_left (by exact_mod_cast hMN) hc0.le
    have hc2 : c ^ 2 ≤ 1 := by nlinarith [sq_nonneg (1 - c)]
    have hc3M : c ^ 3 * (M : ℝ) ≤ c * N := by
      have hh := mul_le_mul hc2 hcM
        (mul_nonneg hc0.le (by positivity)) (by norm_num)
      nlinarith
    have hd2 : delta ^ 2 ≤ 1 := by nlinarith [sq_nonneg (1 - delta)]
    have htarget : (c ^ 3 / 256) * (M : ℝ) * delta ^ 2 ≤ 1 := by
      have hh := mul_le_mul_of_nonneg_right hc3M (sq_nonneg delta)
      nlinarith
    calc
      ‖sliceCharFun s a t‖ ≤ 1 := norm_finCharFun_le_one _ _ _
      _ ≤ Real.exp 1 * Real.exp (-(c ^ 3 / 256) * M * delta ^ 2) := by
        have hexp :
            1 ≤ Real.exp (1 - (c ^ 3 / 256) * (M : ℝ) * delta ^ 2) := by
          calc
            1 = Real.exp 0 := by norm_num
            _ ≤ Real.exp (1 - (c ^ 3 / 256) * (M : ℝ) * delta ^ 2) :=
              Real.exp_le_exp.mpr (sub_nonneg.mpr htarget)
        calc
          1 ≤ Real.exp (1 - (c ^ 3 / 256) * (M : ℝ) * delta ^ 2) := hexp
          _ = Real.exp 1 * Real.exp (-(c ^ 3 / 256) * M * delta ^ 2) := by
            rw [← Real.exp_add]
            congr 1
            ring
      _ = _ := by simp [M]

/-- A deterministic truncation inequality: a lower-tail estimate for the
number of singleton pairs gives the corresponding Laplace-transform bound. -/
lemma sliceSingletonLaplace_le_exp_add_lowerTail
    {K : Type v} {I : Type u}
    [Fintype K] [DecidableEq K] [Fintype I] [DecidableEq I]
    (p : PairEmbedding K I) (s : ℕ) [Nonempty (BoolSlice I s)]
    (u : ℝ) (hu : 0 ≤ u) (L : ℕ) :
    sliceSingletonLaplace p s u ≤
      Real.exp (-(L : ℝ) * u) +
        finProbability (BoolSlice I s)
          (fun x ↦ singletonPairCount p x.1 < L) := by
  classical
  have hpoint : ∀ x : BoolSlice I s,
      Real.exp (-(singletonPairCount p x.1 : ℝ) * u) ≤
        Real.exp (-(L : ℝ) * u) +
          if singletonPairCount p x.1 < L then 1 else 0 := by
    intro x
    by_cases hx : singletonPairCount p x.1 < L
    · rw [if_pos hx]
      have hexp : Real.exp (-(singletonPairCount p x.1 : ℝ) * u) ≤ 1 := by
        rw [Real.exp_le_one_iff]
        exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (by positivity)) hu
      exact hexp.trans (le_add_of_nonneg_left (Real.exp_pos _).le)
    · rw [if_neg hx, add_zero]
      apply Real.exp_le_exp.mpr
      have hL : L ≤ singletonPairCount p x.1 := Nat.le_of_not_gt hx
      exact mul_le_mul_of_nonneg_right (neg_le_neg (by exact_mod_cast hL)) hu
  rw [sliceSingletonLaplace]
  let bad : Finset (BoolSlice I s) := Finset.univ.filter fun x ↦
    singletonPairCount p x.1 < L
  have hcardpos : (0 : ℝ) < Fintype.card (BoolSlice I s) := by
    exact_mod_cast Fintype.card_pos
  calc
    (∑ x : BoolSlice I s,
        Real.exp (-(singletonPairCount p x.1 : ℝ) * u)) /
        Fintype.card (BoolSlice I s) ≤
        ((Fintype.card (BoolSlice I s) : ℝ) * Real.exp (-(L : ℝ) * u) +
          (bad.card : ℝ)) / Fintype.card (BoolSlice I s) := by
      apply div_le_div_of_nonneg_right _ hcardpos.le
      calc
        (∑ x : BoolSlice I s,
            Real.exp (-(singletonPairCount p x.1 : ℝ) * u)) ≤
            ∑ x : BoolSlice I s,
              (Real.exp (-(L : ℝ) * u) +
                if singletonPairCount p x.1 < L then 1 else 0) :=
          Finset.sum_le_sum fun x _ ↦ hpoint x
        _ = (Fintype.card (BoolSlice I s) : ℝ) * Real.exp (-(L : ℝ) * u) +
            (bad.card : ℝ) := by
          rw [Finset.sum_add_distrib]
          simp [bad]
    _ = Real.exp (-(L : ℝ) * u) + (bad.card : ℝ) /
          Fintype.card (BoolSlice I s) := by
      field_simp [ne_of_gt hcardpos]
    _ = Real.exp (-(L : ℝ) * u) +
          finProbability (BoolSlice I s)
            (fun x ↦ singletonPairCount p x.1 < L) := by
      rw [finProbability]
      congr 3
      apply congrArg Finset.card
      ext x
      simp [bad]

/-- Assembly form of the slice characteristic estimate.  A proved Laplace
bound for singleton pairs can be plugged into the exact Fourier reduction
without hiding that remaining combinatorial input. -/
lemma norm_sliceCharFun_le_of_singleton_laplace_bound
    {K : Type v} {I : Type u}
    [Fintype K] [DecidableEq K] [Fintype I] [DecidableEq I]
    (p : PairEmbedding K I) (s : ℕ) [Nonempty (BoolSlice I s)]
    (a : I → ℝ) (t delta C kappa : ℝ) (q : K → ℝ)
    (hdelta : 0 ≤ delta)
    (hqcenter : ∀ k, IsCenteredModOne
      (t * (a (p (k, false)) - a (p (k, true))) / (2 * Real.pi)) (q k))
    (hqdelta : ∀ k, delta ≤ |q k|)
    (hlaplace : sliceSingletonLaplace p s (delta ^ 2) ≤
      C * Real.exp (-kappa * Fintype.card K * delta ^ 2)) :
    ‖sliceCharFun s a t‖ ≤
      C * Real.exp (-kappa * Fintype.card K * delta ^ 2) :=
  (norm_sliceCharFun_le_sliceSingletonLaplace p s a t delta q
    hdelta hqcenter hqdelta).trans hlaplace

lemma norm_sliceCharFun_le_one {I : Type u} [Fintype I] [DecidableEq I] (s : ℕ)
    [Nonempty (BoolSlice I s)] (a : I → ℝ) (t : ℝ) :
    ‖sliceCharFun s a t‖ ≤ 1 :=
  norm_finCharFun_le_one _ _ _

end Fourier
end Erdos88
