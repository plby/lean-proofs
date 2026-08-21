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

import ErdosProblems.Erdos88.Fourier
import ErdosProblems.Erdos88.Richness
import Mathlib.Algebra.Order.Chebyshev

/-!
# Erdős Problem 88: finite quadratic decoupling

This file proves the finite decoupling inequality used as equation (8.1) in
Kwan--Sah--Sauermann--Sawhney.  It is formulated for arbitrary nonempty
finite product spaces, so the later slice argument can instantiate it after
conditioning on a partition of the vertex set.
-/

open scoped BigOperators ComplexConjugate

namespace Erdos88
namespace QuadraticCancellation

open Fourier

universe u v w

lemma finExpectation_prod
    (Ω : Type u) (Ψ : Type v) [Fintype Ω] [Nonempty Ω]
    [Fintype Ψ] [Nonempty Ψ] {E : Type w} [Field E] [CharZero E]
    (f : Ω × Ψ → E) :
    finExpectation (Ω × Ψ) f =
      finExpectation Ω (fun i ↦ finExpectation Ψ (fun j ↦ f (i, j))) := by
  rw [finExpectation, finExpectation]
  simp only [Fintype.card_prod, Nat.cast_mul, Fintype.sum_prod_type,
    finExpectation, div_eq_mul_inv]
  rw [← Finset.sum_mul]
  field_simp [show (Fintype.card Ω : E) ≠ 0 by exact_mod_cast
    Fintype.card_ne_zero,
    show (Fintype.card Ψ : E) ≠ 0 by exact_mod_cast Fintype.card_ne_zero]

lemma finExpectation_equiv
    (Ω : Type u) (Ψ : Type v) [Fintype Ω] [Nonempty Ω]
    [Fintype Ψ] [Nonempty Ψ] {E : Type w} [DivisionRing E]
    (e : Ω ≃ Ψ) (f : Ψ → E) :
    finExpectation Ω (fun i ↦ f (e i)) = finExpectation Ψ f := by
  rw [finExpectation, finExpectation, e.sum_comp, Fintype.card_congr e]

lemma finExpectation_swap
    (Ω : Type u) (Ψ : Type v) [Fintype Ω] [Nonempty Ω]
    [Fintype Ψ] [Nonempty Ψ] {E : Type w} [Field E] [CharZero E]
    (f : Ω → Ψ → E) :
    finExpectation Ω (fun i ↦ finExpectation Ψ (fun j ↦ f i j)) =
      finExpectation Ψ (fun j ↦ finExpectation Ω (fun i ↦ f i j)) := by
  calc
    finExpectation Ω (fun i ↦ finExpectation Ψ (fun j ↦ f i j)) =
        finExpectation (Ω × Ψ) (fun p ↦ f p.1 p.2) :=
      (finExpectation_prod Ω Ψ (fun p ↦ f p.1 p.2)).symm
    _ = finExpectation (Ψ × Ω) (fun p ↦ f p.2 p.1) := by
      have h :=
        (finExpectation_equiv (Ψ × Ω) (Ω × Ψ) (Equiv.prodComm Ψ Ω)
          (fun p ↦ f p.1 p.2)).symm
      convert h using 1 <;> rfl
    _ = finExpectation Ψ (fun j ↦ finExpectation Ω (fun i ↦ f i j)) :=
      finExpectation_prod Ψ Ω (fun p ↦ f p.2 p.1)

lemma finExpectation_re
    (Ω : Type u) [Fintype Ω] [Nonempty Ω] (f : Ω → ℂ) :
    (finExpectation Ω f).re = finExpectation Ω (fun i ↦ (f i).re) := by
  rw [finExpectation, finExpectation]
  let c : ℝ := Fintype.card Ω
  have hc : c ≠ 0 := by
    dsimp only [c]
    exact_mod_cast Fintype.card_ne_zero
  change ((∑ i, f i) / (c : ℂ)).re = (∑ i, (f i).re) / c
  have hre : (∑ i, f i).re = ∑ i, (f i).re := by
    simpa using map_sum Complex.reCLM f (Finset.univ : Finset Ω)
  rw [Complex.div_re]
  simp only [Complex.ofReal_re, Complex.ofReal_im, mul_zero, add_zero,
    Complex.normSq_ofReal, map_sum]
  rw [hre]
  field_simp [hc]
  ring

lemma finExpectation_mono_real
    (Ω : Type u) [Fintype Ω] [Nonempty Ω] {f g : Ω → ℝ}
    (h : ∀ i, f i ≤ g i) : finExpectation Ω f ≤ finExpectation Ω g := by
  rw [finExpectation, finExpectation, div_le_div_iff_of_pos_right]
  · exact Finset.sum_le_sum fun i _ ↦ h i
  · exact_mod_cast Fintype.card_pos

lemma norm_finExpectation_sq_le
    (Ω : Type u) [Fintype Ω] [Nonempty Ω] (f : Ω → ℂ) :
    ‖finExpectation Ω f‖ ^ 2 ≤
      (∑ i, ‖f i‖ ^ 2) / Fintype.card Ω := by
  have hnorm := norm_finExpectation_le Ω f
  have hsq : ‖finExpectation Ω f‖ ^ 2 ≤
      ((∑ i, ‖f i‖) / Fintype.card Ω) ^ 2 :=
    (sq_le_sq₀ (norm_nonneg _) (by positivity)).2 hnorm
  exact hsq.trans (by
    rw [← Finset.card_univ]
    exact sum_div_card_sq_le_sum_sq_div_card)

lemma finExpectation_conj
    (Ω : Type u) [Fintype Ω] [Nonempty Ω] (f : Ω → ℂ) :
    finExpectation Ω (fun i ↦ conj (f i)) = conj (finExpectation Ω f) := by
  rw [finExpectation, finExpectation, map_div₀, map_sum]
  simp

lemma finExpectation_pair_mul_conj
    (Ω : Type u) [Fintype Ω] [Nonempty Ω] (f : Ω → ℂ) :
    finExpectation (Ω × Ω) (fun p ↦ f p.1 * conj (f p.2)) =
      (‖finExpectation Ω f‖ ^ 2 : ℂ) := by
  rw [finExpectation_prod]
  have hinner : ∀ i : Ω,
      finExpectation Ω (fun j ↦ f i * conj (f j)) =
        f i * conj (finExpectation Ω f) := by
    intro i
    rw [finExpectation_const_mul, finExpectation_conj]
  simp_rw [hinner]
  calc
    finExpectation Ω (fun i ↦ f i * conj (finExpectation Ω f)) =
        finExpectation Ω
          (fun i ↦ conj (finExpectation Ω f) * f i) := by
      congr 1
      funext i
      ring
    _ = conj (finExpectation Ω f) * finExpectation Ω f :=
      finExpectation_const_mul Ω _ f
    _ = (‖finExpectation Ω f‖ ^ 2 : ℂ) := by
      rw [Complex.conj_mul']

lemma phase_mul_conj_phase (t x y : ℝ) :
    Complex.exp ((t * x : ℝ) * Complex.I) *
        conj (Complex.exp ((t * y : ℝ) * Complex.I)) =
      Complex.exp ((t * (x - y) : ℝ) * Complex.I) := by
  rw [← Complex.exp_conj, ← Complex.exp_add]
  congr 1
  push_cast
  simp
  ring

/-- The square of a finite characteristic function is the real part of its
two-copy correlation. -/
lemma norm_finCharFun_sq_eq_pair_re
    (Ω : Type u) [Fintype Ω] [Nonempty Ω] (X : Ω → ℝ) (t : ℝ) :
    ‖finCharFun Ω X t‖ ^ 2 =
      finExpectation (Ω × Ω) (fun p ↦
        (Complex.exp ((t * (X p.1 - X p.2) : ℝ) * Complex.I)).re) := by
  let f : Ω → ℂ := fun i ↦
    Complex.exp ((t * X i : ℝ) * Complex.I)
  have hpair := finExpectation_pair_mul_conj Ω f
  have hpoint : (fun p : Ω × Ω ↦ f p.1 * conj (f p.2)) =
      fun p ↦ Complex.exp ((t * (X p.1 - X p.2) : ℝ) * Complex.I) := by
    funext p
    exact phase_mul_conj_phase t (X p.1) (X p.2)
  calc
    ‖finCharFun Ω X t‖ ^ 2 = ‖finExpectation Ω f‖ ^ 2 := by
      rfl
    _ = ((‖finExpectation Ω f‖ ^ 2 : ℂ)).re := by
      simp only [pow_two, Complex.mul_re, Complex.ofReal_re,
        Complex.ofReal_im, mul_zero, sub_zero]
    _ = (finExpectation (Ω × Ω)
        (fun p ↦ f p.1 * conj (f p.2))).re := by
      rw [hpair]
    _ = (finExpectation (Ω × Ω)
        (fun p ↦ Complex.exp
          ((t * (X p.1 - X p.2) : ℝ) * Complex.I))).re := by
      rw [hpoint]
    _ = finExpectation (Ω × Ω) (fun p ↦
        (Complex.exp ((t * (X p.1 - X p.2) : ℝ) * Complex.I)).re) :=
      finExpectation_re (Ω × Ω) _

/-- Finite decoupling inequality, equation (8.1) in Kwan--Sah--
Sauermann--Sawhney.  The two copies of the second coordinate are independent
and uniform. -/
theorem norm_finCharFun_sq_le_decoupled
    (Ω : Type u) (Ψ : Type v) [Fintype Ω] [Nonempty Ω]
    [Fintype Ψ] [Nonempty Ψ] (X : Ω → Ψ → ℝ) (t : ℝ) :
    ‖finCharFun (Ω × Ψ) (fun p ↦ X p.1 p.2) t‖ ^ 2 ≤
      finExpectation (Ψ × Ψ) (fun p ↦
        ‖finCharFun Ω (fun i ↦ X i p.1 - X i p.2) t‖) := by
  let f : Ω → ℂ := fun i ↦ finCharFun Ψ (X i) t
  have hprod : finCharFun (Ω × Ψ) (fun p ↦ X p.1 p.2) t =
      finExpectation Ω f := by
    rw [finCharFun, finExpectation_prod]
    rfl
  calc
    ‖finCharFun (Ω × Ψ) (fun p ↦ X p.1 p.2) t‖ ^ 2 =
        ‖finExpectation Ω f‖ ^ 2 := by rw [hprod]
    _ ≤ finExpectation Ω (fun i ↦ ‖f i‖ ^ 2) := by
      simpa only [finExpectation] using norm_finExpectation_sq_le Ω f
    _ = finExpectation Ω (fun i ↦
        finExpectation (Ψ × Ψ) (fun p ↦
          (Complex.exp
            ((t * (X i p.1 - X i p.2) : ℝ) * Complex.I)).re)) := by
      congr 1
      funext i
      exact norm_finCharFun_sq_eq_pair_re Ψ (X i) t
    _ = finExpectation (Ψ × Ψ) (fun p ↦
        finExpectation Ω (fun i ↦
          (Complex.exp
            ((t * (X i p.1 - X i p.2) : ℝ) * Complex.I)).re)) :=
      finExpectation_swap Ω (Ψ × Ψ) _
    _ ≤ finExpectation (Ψ × Ψ) (fun p ↦
        ‖finCharFun Ω (fun i ↦ X i p.1 - X i p.2) t‖) := by
      apply finExpectation_mono_real
      intro p
      rw [← finExpectation_re]
      exact Complex.re_le_norm _

lemma finExpectation_add_real
    (Ω : Type u) [Fintype Ω] [Nonempty Ω] (f g : Ω → ℝ) :
    finExpectation Ω (fun i ↦ f i + g i) =
      finExpectation Ω f + finExpectation Ω g := by
  rw [finExpectation, finExpectation, finExpectation,
    Finset.sum_add_distrib, add_div]

@[simp] lemma finExpectation_const_real
    (Ω : Type u) [Fintype Ω] [Nonempty Ω] (c : ℝ) :
    finExpectation Ω (fun _ ↦ c) = c := by
  simp [finExpectation]

lemma finExpectation_indicator
    (Ω : Type u) [Fintype Ω] [Nonempty Ω] (P : Ω → Prop)
    [DecidablePred P] :
    finExpectation Ω (fun i ↦ if P i then (1 : ℝ) else 0) =
      finProbability Ω P := by
  rw [finExpectation, finProbability]
  simp only [Finset.sum_boole]
  congr 1
  norm_cast
  congr 1
  ext i
  simp

/-- An expectation is bounded by its good-event bound plus the probability
of the exceptional event. -/
lemma finExpectation_le_add_probability
    (Ω : Type u) [Fintype Ω] [Nonempty Ω] (f : Ω → ℝ)
    (P : Ω → Prop) [DecidablePred P] {q ε : ℝ}
    (hq : 0 ≤ q) (hall : ∀ i, f i ≤ 1)
    (hgood : ∀ i, ¬P i → f i ≤ q)
    (hbad : finProbability Ω P ≤ ε) :
    finExpectation Ω f ≤ q + ε := by
  have hpoint : ∀ i, f i ≤ q + if P i then 1 else 0 := by
    intro i
    by_cases hi : P i
    · rw [if_pos hi]
      exact (hall i).trans (by linarith)
    · rw [if_neg hi, add_zero]
      exact hgood i hi
  calc
    finExpectation Ω f ≤
        finExpectation Ω (fun i ↦ q + if P i then (1 : ℝ) else 0) :=
      finExpectation_mono_real Ω hpoint
    _ = q + finProbability Ω P := by
      rw [finExpectation_add_real, finExpectation_const_real,
        finExpectation_indicator]
    _ ≤ q + ε := add_le_add_right hbad q

section SplitQuadratic

variable {I : Type u} {J : Type v} [Fintype I] [DecidableEq I]
  [Fintype J] [DecidableEq J]

/-- The coefficient of the `I`-coordinate left after subtracting two
outcomes on the `J` side of a split quadratic polynomial. -/
noncomputable def crossSliceCoefficient (A : I → J → ℝ)
    (y z : J → Bool) (i : I) : ℝ :=
  ∑ j, A i j * (boolIndicator (y j) - boolIndicator (z j))

/-- A quadratic polynomial after its variables have been split into two
parts.  The pure terms on each side are arbitrary; only the cross term is
used by decoupling. -/
noncomputable def splitQuadraticValue {s r : ℕ}
    (fI : BoolSlice I s → ℝ) (fJ : BoolSlice J r → ℝ)
    (A : I → J → ℝ) (x : BoolSlice I s) (y : BoolSlice J r) : ℝ :=
  fI x + fJ y +
    ∑ i, ∑ j, A i j * boolIndicator (x.1 i) * boolIndicator (y.1 j)

lemma splitQuadraticValue_sub {s r : ℕ}
    (fI : BoolSlice I s → ℝ) (fJ : BoolSlice J r → ℝ)
    (A : I → J → ℝ) (x : BoolSlice I s) (y z : BoolSlice J r) :
    splitQuadraticValue fI fJ A x y - splitQuadraticValue fI fJ A x z =
      (∑ i, crossSliceCoefficient A y.1 z.1 i * boolIndicator (x.1 i)) +
        (fJ y - fJ z) := by
  have hcross :
      (∑ i, ∑ j, A i j * boolIndicator (x.1 i) * boolIndicator (y.1 j)) -
          (∑ i, ∑ j, A i j * boolIndicator (x.1 i) * boolIndicator (z.1 j)) =
        ∑ i, crossSliceCoefficient A y.1 z.1 i * boolIndicator (x.1 i) := by
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _
    rw [crossSliceCoefficient, Finset.sum_mul]
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [splitQuadraticValue, splitQuadraticValue]
  rw [show
    (fI x + fJ y +
        ∑ i, ∑ j, A i j * boolIndicator (x.1 i) * boolIndicator (y.1 j)) -
      (fI x + fJ z +
        ∑ i, ∑ j, A i j * boolIndicator (x.1 i) * boolIndicator (z.1 j)) =
      (fJ y - fJ z) +
        ((∑ i, ∑ j, A i j * boolIndicator (x.1 i) * boolIndicator (y.1 j)) -
          (∑ i, ∑ j, A i j * boolIndicator (x.1 i) * boolIndicator (z.1 j))) by
      ring]
  rw [hcross]
  ring

lemma norm_finCharFun_splitQuadratic_sub_eq_sliceCharFun {s r : ℕ}
    [Nonempty (BoolSlice I s)] [Nonempty (BoolSlice J r)]
    (fI : BoolSlice I s → ℝ) (fJ : BoolSlice J r → ℝ)
    (A : I → J → ℝ) (y z : BoolSlice J r) (t : ℝ) :
    ‖finCharFun (BoolSlice I s)
        (fun x ↦ splitQuadraticValue fI fJ A x y -
          splitQuadraticValue fI fJ A x z) t‖ =
      ‖sliceCharFun s (crossSliceCoefficient A y.1 z.1) t‖ := by
  have hfun : (fun x : BoolSlice I s ↦
      splitQuadraticValue fI fJ A x y - splitQuadraticValue fI fJ A x z) =
      fun x ↦ (∑ i, crossSliceCoefficient A y.1 z.1 i *
        boolIndicator (x.1 i)) + (fJ y - fJ z) := by
    funext x
    exact splitQuadraticValue_sub fI fJ A x y z
  let linear : BoolSlice I s → ℝ := fun x ↦
    ∑ i, crossSliceCoefficient A y.1 z.1 i * boolIndicator (x.1 i)
  calc
    ‖finCharFun (BoolSlice I s)
        (fun x ↦ splitQuadraticValue fI fJ A x y -
          splitQuadraticValue fI fJ A x z) t‖ =
        ‖finCharFun (BoolSlice I s)
          (fun x ↦ linear x + (fJ y - fJ z)) t‖ := by rw [hfun]
    _ = ‖Complex.exp ((t * (fJ y - fJ z) : ℝ) * Complex.I) *
        finCharFun (BoolSlice I s) linear t‖ := by
      rw [finCharFun_add_const]
    _ = ‖finCharFun (BoolSlice I s) linear t‖ := by
      rw [norm_mul, Complex.norm_exp]
      simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
        Complex.I_re, Complex.I_im, mul_zero, mul_one, sub_self,
        Real.exp_zero, one_mul]
    _ = ‖sliceCharFun s (crossSliceCoefficient A y.1 z.1) t‖ := by
      rfl

/-- Equation (8.1) specialized to a split quadratic polynomial on two
independent fixed-size Boolean slices.  The pure quadratic terms disappear
and the surviving inner characteristic function is exactly linear. -/
theorem norm_splitQuadraticCharFun_sq_le {s r : ℕ}
    [Nonempty (BoolSlice I s)] [Nonempty (BoolSlice J r)]
    (fI : BoolSlice I s → ℝ) (fJ : BoolSlice J r → ℝ)
    (A : I → J → ℝ) (t : ℝ) :
    ‖finCharFun (BoolSlice I s × BoolSlice J r)
        (fun p ↦ splitQuadraticValue fI fJ A p.1 p.2) t‖ ^ 2 ≤
      finExpectation (BoolSlice J r × BoolSlice J r) (fun p ↦
        ‖sliceCharFun s (crossSliceCoefficient A p.1.1 p.2.1) t‖) := by
  calc
    ‖finCharFun (BoolSlice I s × BoolSlice J r)
        (fun p ↦ splitQuadraticValue fI fJ A p.1 p.2) t‖ ^ 2 ≤
      finExpectation (BoolSlice J r × BoolSlice J r) (fun p ↦
        ‖finCharFun (BoolSlice I s) (fun x ↦
          splitQuadraticValue fI fJ A x p.1 -
            splitQuadraticValue fI fJ A x p.2) t‖) :=
      norm_finCharFun_sq_le_decoupled (BoolSlice I s) (BoolSlice J r)
        (fun x y ↦ splitQuadraticValue fI fJ A x y) t
    _ = finExpectation (BoolSlice J r × BoolSlice J r) (fun p ↦
        ‖sliceCharFun s (crossSliceCoefficient A p.1.1 p.2.1) t‖) := by
      congr 1
      funext p
      exact norm_finCharFun_splitQuadratic_sub_eq_sliceCharFun
        fI fJ A p.1 p.2 t

/-- Good outcomes of the two-copy exposure give a small slice
characteristic function; exceptional outcomes cost only their probability. -/
theorem norm_splitQuadraticCharFun_sq_le_of_good {s r : ℕ}
    [Nonempty (BoolSlice I s)] [Nonempty (BoolSlice J r)]
    (fI : BoolSlice I s → ℝ) (fJ : BoolSlice J r → ℝ)
    (A : I → J → ℝ) (t : ℝ)
    (Good : BoolSlice J r × BoolSlice J r → Prop)
    [DecidablePred Good] {q ε : ℝ} (hq : 0 ≤ q)
    (hgood : ∀ p, Good p →
      ‖sliceCharFun s (crossSliceCoefficient A p.1.1 p.2.1) t‖ ≤ q)
    (hbad : finProbability (BoolSlice J r × BoolSlice J r)
      (fun p ↦ ¬Good p) ≤ ε) :
    ‖finCharFun (BoolSlice I s × BoolSlice J r)
        (fun p ↦ splitQuadraticValue fI fJ A p.1 p.2) t‖ ^ 2 ≤
      q + ε := by
  calc
    ‖finCharFun (BoolSlice I s × BoolSlice J r)
        (fun p ↦ splitQuadraticValue fI fJ A p.1 p.2) t‖ ^ 2 ≤
      finExpectation (BoolSlice J r × BoolSlice J r) (fun p ↦
        ‖sliceCharFun s (crossSliceCoefficient A p.1.1 p.2.1) t‖) :=
      norm_splitQuadraticCharFun_sq_le fI fJ A t
    _ ≤ q + ε := by
      apply finExpectation_le_add_probability
        (BoolSlice J r × BoolSlice J r)
        (fun p ↦ ‖sliceCharFun s
          (crossSliceCoefficient A p.1.1 p.2.1) t‖)
        (fun p ↦ ¬Good p)
      · exact hq
      · intro p
        exact norm_sliceCharFun_le_one s _ t
      · intro p hp
        exact hgood p (not_not.mp hp)
      · simpa only [not_not] using hbad

/-- The analytic conclusion of KSSS Claim 8.5: if all but an exceptional
fraction of the two-copy exposures yield many disjoint coefficient pairs
separated modulo one, Lemma 4.8 turns the decoupled linear slice into
exponential decay. -/
theorem norm_splitQuadraticCharFun_sq_le_balanced
    {K : Type w} [Fintype K] [DecidableEq K] {s r : ℕ}
    [Nonempty (BoolSlice I s)] [Nonempty (BoolSlice J r)]
    (fI : BoolSlice I s → ℝ) (fJ : BoolSlice J r → ℝ)
    (A : I → J → ℝ) (t delta c ε : ℝ)
    (Good : BoolSlice J r × BoolSlice J r → Prop)
    [DecidablePred Good]
    (pairing : ∀ p, Good p → PairEmbedding K I)
    (center : ∀ p, Good p → K → ℝ)
    (hc0 : 0 < c) (hc1 : c ≤ 1 / 2)
    (hsel : c * Fintype.card I ≤ s)
    (hunsel : c * Fintype.card I ≤ Fintype.card I - s)
    (hdelta0 : 0 ≤ delta) (hdelta1 : delta ≤ 1 / 2)
    (hcenter : ∀ p (hp : Good p) k,
      IsCenteredModOne
        (t * (crossSliceCoefficient A p.1.1 p.2.1
            (pairing p hp (k, false)) -
          crossSliceCoefficient A p.1.1 p.2.1
            (pairing p hp (k, true))) / (2 * Real.pi))
        (center p hp k))
    (hseparated : ∀ p (hp : Good p) k,
      delta ≤ |center p hp k|)
    (hbad : finProbability (BoolSlice J r × BoolSlice J r)
      (fun p ↦ ¬Good p) ≤ ε) :
    ‖finCharFun (BoolSlice I s × BoolSlice J r)
        (fun p ↦ splitQuadraticValue fI fJ A p.1 p.2) t‖ ^ 2 ≤
      Real.exp 1 * Real.exp
        (-(c ^ 3 / 256) * Fintype.card K * delta ^ 2) + ε := by
  apply norm_splitQuadraticCharFun_sq_le_of_good
    fI fJ A t Good
  · positivity
  · intro p hp
    exact norm_sliceCharFun_le_balanced (pairing p hp) s
      (crossSliceCoefficient A p.1.1 p.2.1) t delta c (center p hp)
      hc0 hc1 hsel hunsel hdelta0 hdelta1 (hcenter p hp)
        (hseparated p hp)
  · exact hbad

end SplitQuadratic

section RichTuples

variable {V : Type u} [Fintype V] [DecidableEq V]

lemma Rich.exists_nonexceptional_mem
    {G : SimpleGraph V} {δ ρ α : ℝ} (hrich : Rich G δ ρ α)
    {W U : Finset V} (hW : δ * Fintype.card V ≤ W.card)
    (hU : (Fintype.card V : ℝ) ^ α < U.card) :
    ∃ v ∈ U, v ∉ exceptionalVertices G W ρ := by
  by_contra hnone
  push Not at hnone
  have hsub : U ⊆ exceptionalVertices G W ρ := by
    intro v hv
    exact hnone v hv
  have hcard : (U.card : ℝ) ≤ (exceptionalVertices G W ρ).card := by
    exact_mod_cast Finset.card_le_card hsub
  exact (not_lt_of_ge (hcard.trans (hrich W hW))) hU

/-- A rich graph supplies a vertex having both many neighbors and many
nonneighbors in every sufficiently large residual set, provided the candidate
set is larger than the exceptional-vertex budget. -/
lemma Rich.exists_balanced_vertex
    {G : SimpleGraph V} {δ ρ α : ℝ} (hrich : Rich G δ ρ α)
    {W U : Finset V} (hW : δ * Fintype.card V ≤ W.card)
    (hU : (Fintype.card V : ℝ) ^ α < U.card) :
    ∃ v ∈ U,
      ρ * W.card < (neighborsIn G v W).card ∧
      ρ * W.card < (W \ neighborsIn G v W).card := by
  obtain ⟨v, hvU, hv⟩ :=
    Rich.exists_nonexceptional_mem (G := G) hrich hW hU
  simp only [mem_exceptionalVertices, not_or, not_le] at hv
  exact ⟨v, hvU, hv.1, hv.2⟩

/-- A data-carrying version of the iterative construction in equation (8.3).
`used` records the chosen tuple vertices and `W` is the common nonneighbor
residual after all choices made so far. -/
inductive DiverseNeighborhoodChain (G : SimpleGraph V) (ρ : ℝ)
    (U : Finset V) : (k : ℕ) → Finset V → Finset V → Type u
  | nil : DiverseNeighborhoodChain G ρ U 0 ∅ Finset.univ
  | cons {k : ℕ} {used W : Finset V}
      (tail : DiverseNeighborhoodChain G ρ U k used W)
      (v : V) (mem_candidate : v ∈ U) (fresh : v ∉ used)
      (neighbors_large :
        ρ * W.card < (neighborsIn G v W).card)
      (nonneighbors_large :
        ρ * W.card < (W \ neighborsIn G v W).card) :
      DiverseNeighborhoodChain G ρ U (k + 1) (insert v used)
        (W \ neighborsIn G v W)

lemma DiverseNeighborhoodChain.used_subset
    {G : SimpleGraph V} {ρ : ℝ} {U used W : Finset V} {k : ℕ}
    (chain : DiverseNeighborhoodChain G ρ U k used W) : used ⊆ U := by
  induction chain with
  | nil => simp
  | cons tail v hv _ _ _ ih => exact Finset.insert_subset hv ih

@[simp] lemma DiverseNeighborhoodChain.used_card
    {G : SimpleGraph V} {ρ : ℝ} {U used W : Finset V} {k : ℕ}
    (chain : DiverseNeighborhoodChain G ρ U k used W) : used.card = k := by
  induction chain with
  | nil => simp
  | cons tail v _ hv _ _ ih => simp [hv, ih]

lemma DiverseNeighborhoodChain.residual_card_lower
    {G : SimpleGraph V} {ρ : ℝ} {U used W : Finset V} {k : ℕ}
    (chain : DiverseNeighborhoodChain G ρ U k used W) (hρ : 0 ≤ ρ) :
    ρ ^ k * Fintype.card V ≤ W.card := by
  induction chain with
  | nil => simp
  | @cons k used W tail v hvU hv hneighbors hnonneighbors ih =>
      have hmul : ρ * (ρ ^ k * (Fintype.card V : ℝ)) ≤ ρ * W.card :=
        mul_le_mul_of_nonneg_left ih hρ
      have hnext : ρ * W.card ≤
          ((W \ neighborsIn G v W).card : ℝ) := hnonneighbors.le
      calc
        ρ ^ (k + 1) * Fintype.card V =
            ρ * (ρ ^ k * Fintype.card V) := by rw [pow_succ]; ring
        _ ≤ ρ * W.card := hmul
        _ ≤ (W \ neighborsIn G v W).card := hnext

/-- Exact finite iteration behind KSSS equation (8.3). The hypotheses keep
the two numerical resources visible: every possible residual is large enough
for richness, and the candidate set remains larger than the exceptional set
after `q` fresh choices. -/
theorem exists_diverseNeighborhoodChain
    {G : SimpleGraph V} {δ ρ α : ℝ} (hrich : Rich G δ ρ α)
    (U : Finset V) (q : ℕ) (hρ : 0 ≤ ρ)
    (hresidual : ∀ k ≤ q,
      δ * Fintype.card V ≤ ρ ^ k * Fintype.card V)
    (hsupply : (Fintype.card V : ℝ) ^ α + q < U.card) :
    ∃ used W, Nonempty (DiverseNeighborhoodChain G ρ U q used W) := by
  induction q with
  | zero =>
      exact ⟨∅, Finset.univ, ⟨DiverseNeighborhoodChain.nil⟩⟩
  | succ q ih =>
      have hresidual' : ∀ k ≤ q,
          δ * Fintype.card V ≤ ρ ^ k * Fintype.card V := by
        intro k hk
        exact hresidual k (hk.trans (Nat.le_succ q))
      have hsupply' : (Fintype.card V : ℝ) ^ α + q < U.card := by
        norm_num at hsupply ⊢
        linarith
      obtain ⟨used, W, ⟨chain⟩⟩ := ih hresidual' hsupply'
      have husedSub : used ⊆ U := chain.used_subset
      have husedCard : used.card = q := chain.used_card
      have hqU : q ≤ U.card := by
        rw [← husedCard]
        exact Finset.card_le_card husedSub
      have hremaining : (Fintype.card V : ℝ) ^ α < (U \ used).card := by
        rw [Finset.card_sdiff_of_subset husedSub, husedCard, Nat.cast_sub hqU]
        norm_num at hsupply ⊢
        linarith
      have hWlower := chain.residual_card_lower hρ
      have hW : δ * Fintype.card V ≤ W.card :=
        (hresidual q (Nat.le_succ q)).trans hWlower
      obtain ⟨v, hv, hneighbors, hnonneighbors⟩ :=
        Rich.exists_balanced_vertex (G := G) hrich hW hremaining
      have hvU : v ∈ U := (Finset.mem_sdiff.mp hv).1
      have hvfresh : v ∉ used := (Finset.mem_sdiff.mp hv).2
      exact ⟨insert v used, W \ neighborsIn G v W,
        ⟨DiverseNeighborhoodChain.cons chain v hvU hvfresh
          hneighbors hnonneighbors⟩⟩

end RichTuples

section RichTupleFamilies

variable {V : Type u} [Fintype V] [DecidableEq V]

open Classical

structure DiverseNeighborhoodStage (G : SimpleGraph V) (ρ : ℝ) where
  vertex : V
  priorResidual : Finset V
  neighbors_large :
    ρ * priorResidual.card < (neighborsIn G vertex priorResidual).card
  nonneighbors_large :
    ρ * priorResidual.card <
      (priorResidual \ neighborsIn G vertex priorResidual).card

noncomputable def DiverseNeighborhoodChain.stageAt
    {G : SimpleGraph V} {ρ : ℝ} {U used W : Finset V} {k : ℕ}
    (chain : DiverseNeighborhoodChain G ρ U k used W) :
    Fin k → DiverseNeighborhoodStage G ρ := by
  induction chain with
  | nil => exact Fin.elim0
  | @cons k used W tail v hvU hvfresh hn hnn ih =>
      exact Fin.lastCases
        { vertex := v
          priorResidual := W
          neighbors_large := hn
          nonneighbors_large := hnn }
        ih

@[simp] lemma DiverseNeighborhoodChain.stageAt_cons_castSucc_vertex
    {G : SimpleGraph V} {ρ : ℝ} {U used W : Finset V} {k : ℕ}
    (tail : DiverseNeighborhoodChain G ρ U k used W)
    (v : V) (hvU : v ∈ U) (hvfresh : v ∉ used)
    (hn : ρ * W.card < (neighborsIn G v W).card)
    (hnn : ρ * W.card < (W \ neighborsIn G v W).card)
    (i : Fin k) :
    ((DiverseNeighborhoodChain.cons tail v hvU hvfresh hn hnn).stageAt
      i.castSucc).vertex = (tail.stageAt i).vertex := by
  simp [DiverseNeighborhoodChain.stageAt]

@[simp] lemma DiverseNeighborhoodChain.stageAt_cons_last_vertex
    {G : SimpleGraph V} {ρ : ℝ} {U used W : Finset V} {k : ℕ}
    (tail : DiverseNeighborhoodChain G ρ U k used W)
    (v : V) (hvU : v ∈ U) (hvfresh : v ∉ used)
    (hn : ρ * W.card < (neighborsIn G v W).card)
    (hnn : ρ * W.card < (W \ neighborsIn G v W).card) :
    ((DiverseNeighborhoodChain.cons tail v hvU hvfresh hn hnn).stageAt
      (Fin.last k)).vertex = v := by
  simp [DiverseNeighborhoodChain.stageAt]

@[simp] lemma DiverseNeighborhoodChain.stageAt_cons_castSucc_priorResidual
    {G : SimpleGraph V} {ρ : ℝ} {U used W : Finset V} {k : ℕ}
    (tail : DiverseNeighborhoodChain G ρ U k used W)
    (v : V) (hvU : v ∈ U) (hvfresh : v ∉ used)
    (hn : ρ * W.card < (neighborsIn G v W).card)
    (hnn : ρ * W.card < (W \ neighborsIn G v W).card)
    (i : Fin k) :
    ((DiverseNeighborhoodChain.cons tail v hvU hvfresh hn hnn).stageAt
      i.castSucc).priorResidual = (tail.stageAt i).priorResidual := by
  simp [DiverseNeighborhoodChain.stageAt]

@[simp] lemma DiverseNeighborhoodChain.stageAt_cons_last_priorResidual
    {G : SimpleGraph V} {ρ : ℝ} {U used W : Finset V} {k : ℕ}
    (tail : DiverseNeighborhoodChain G ρ U k used W)
    (v : V) (hvU : v ∈ U) (hvfresh : v ∉ used)
    (hn : ρ * W.card < (neighborsIn G v W).card)
    (hnn : ρ * W.card < (W \ neighborsIn G v W).card) :
    ((DiverseNeighborhoodChain.cons tail v hvU hvfresh hn hnn).stageAt
      (Fin.last k)).priorResidual = W := by
  simp [DiverseNeighborhoodChain.stageAt]

lemma DiverseNeighborhoodChain.finalResidual_eq
    {G : SimpleGraph V} {ρ : ℝ} {U used W : Finset V} {k : ℕ}
    (chain : DiverseNeighborhoodChain G ρ U k used W) :
    W = Finset.univ.filter (fun x ↦
      ∀ i : Fin k, ¬G.Adj (chain.stageAt i).vertex x) := by
  induction chain with
  | nil => ext x; simp
  | @cons k used W tail v hvU hvfresh hn hnn ih =>
      ext x
      have ihx : x ∈ W ↔ ∀ i : Fin k, ¬G.Adj (tail.stageAt i).vertex x := by
        have hmem := congrArg (fun S : Finset V ↦ x ∈ S) ih
        simpa using hmem
      simp only [Finset.mem_sdiff, mem_neighborsIn, Finset.mem_filter,
        Finset.mem_univ, true_and, Fin.forall_fin_succ',
        DiverseNeighborhoodChain.stageAt_cons_castSucc_vertex,
        DiverseNeighborhoodChain.stageAt_cons_last_vertex]
      rw [ihx]
      tauto

lemma DiverseNeighborhoodChain.stageAt_priorResidual_eq
    {G : SimpleGraph V} {ρ : ℝ} {U used W : Finset V} {k : ℕ}
    (chain : DiverseNeighborhoodChain G ρ U k used W) (i : Fin k) :
    (chain.stageAt i).priorResidual = Finset.univ.filter (fun x ↦
      ∀ j : Fin k, j < i → ¬G.Adj (chain.stageAt j).vertex x) := by
  induction chain with
  | nil => exact Fin.elim0 i
  | @cons k used W tail v hvU hvfresh hn hnn ih =>
      refine Fin.lastCases ?_ (fun i ↦ ?_) i
      · rw [DiverseNeighborhoodChain.stageAt_cons_last_priorResidual]
        ext x
        have hfinalx : x ∈ W ↔
            ∀ j : Fin k, ¬G.Adj (tail.stageAt j).vertex x := by
          have hmem := congrArg (fun S : Finset V ↦ x ∈ S)
            tail.finalResidual_eq
          simpa using hmem
        simpa [Fin.forall_fin_succ'] using hfinalx
      · rw [DiverseNeighborhoodChain.stageAt_cons_castSucc_priorResidual,
          ih i]
        ext x
        simp only [Finset.mem_filter, Finset.mem_univ, true_and,
          Fin.forall_fin_succ',
          DiverseNeighborhoodChain.stageAt_cons_castSucc_vertex,
          DiverseNeighborhoodChain.stageAt_cons_last_vertex]
        constructor
        · intro h
          constructor
          · intro j hj
            exact h j hj
          · intro hbad
            exact ((not_lt_of_ge (Fin.le_last _)) hbad).elim
        · intro h j hj
          exact h.1 j hj

noncomputable def DiverseNeighborhoodChain.vertexAt
    {G : SimpleGraph V} {ρ : ℝ} {U used W : Finset V} {k : ℕ}
    (chain : DiverseNeighborhoodChain G ρ U k used W) (i : Fin k) : V :=
  (chain.stageAt i).vertex

@[simp] lemma DiverseNeighborhoodChain.vertexAt_cons_castSucc
    {G : SimpleGraph V} {ρ : ℝ} {U used W : Finset V} {k : ℕ}
    (tail : DiverseNeighborhoodChain G ρ U k used W)
    (v : V) (hvU : v ∈ U) (hvfresh : v ∉ used)
    (hn : ρ * W.card < (neighborsIn G v W).card)
    (hnn : ρ * W.card < (W \ neighborsIn G v W).card)
    (i : Fin k) :
    (DiverseNeighborhoodChain.cons tail v hvU hvfresh hn hnn).vertexAt
      i.castSucc = tail.vertexAt i := by
  simp [DiverseNeighborhoodChain.vertexAt]

@[simp] lemma DiverseNeighborhoodChain.vertexAt_cons_last
    {G : SimpleGraph V} {ρ : ℝ} {U used W : Finset V} {k : ℕ}
    (tail : DiverseNeighborhoodChain G ρ U k used W)
    (v : V) (hvU : v ∈ U) (hvfresh : v ∉ used)
    (hn : ρ * W.card < (neighborsIn G v W).card)
    (hnn : ρ * W.card < (W \ neighborsIn G v W).card) :
    (DiverseNeighborhoodChain.cons tail v hvU hvfresh hn hnn).vertexAt
      (Fin.last k) = v := by
  simp [DiverseNeighborhoodChain.vertexAt]

lemma DiverseNeighborhoodChain.vertexAt_mem_used
    {G : SimpleGraph V} {ρ : ℝ} {U used W : Finset V} {k : ℕ}
    (chain : DiverseNeighborhoodChain G ρ U k used W) (i : Fin k) :
    chain.vertexAt i ∈ used := by
  induction chain with
  | nil => exact Fin.elim0 i
  | @cons k used W tail v hvU hvfresh hn hnn ih =>
      refine Fin.lastCases ?_ (fun j ↦ ?_) i
      · simp [DiverseNeighborhoodChain.vertexAt]
      · simpa using Finset.mem_insert_of_mem (ih j)

lemma DiverseNeighborhoodChain.vertexAt_injective
    {G : SimpleGraph V} {ρ : ℝ} {U used W : Finset V} {k : ℕ}
    (chain : DiverseNeighborhoodChain G ρ U k used W) :
    Function.Injective chain.vertexAt := by
  induction chain with
  | nil => intro i; exact Fin.elim0 i
  | @cons k used W tail v hvU hvfresh hn hnn ih =>
      intro i
      refine Fin.lastCases ?_ (fun i ↦ ?_) i
      · intro j
        refine Fin.lastCases ?_ (fun j ↦ ?_) j
        · intro _
          rfl
        · intro hij
          exfalso
          apply hvfresh
          have hj : tail.vertexAt j ∈ used := tail.vertexAt_mem_used j
          have hij' : v = tail.vertexAt j := by simpa using hij
          simpa [← hij'] using hj
      · intro j
        refine Fin.lastCases ?_ (fun j ↦ ?_) j
        · intro hij
          exfalso
          apply hvfresh
          have hi : tail.vertexAt i ∈ used := tail.vertexAt_mem_used i
          have hij' : tail.vertexAt i = v := by simpa using hij
          simpa [← hij'] using hi
        · intro hij
          have hij' : tail.vertexAt i = tail.vertexAt j := by
            simpa using hij
          exact congrArg Fin.castSucc (ih hij')

noncomputable def DiverseNeighborhoodChain.priorSet
    {G : SimpleGraph V} {ρ : ℝ} {U used W : Finset V} {k : ℕ}
    (chain : DiverseNeighborhoodChain G ρ U k used W) (i : Fin k) :
    Finset V :=
  Finset.univ.filter (fun x ↦
    ∀ j : Fin k, j < i → ¬G.Adj (chain.vertexAt j) x)

noncomputable def DiverseNeighborhoodChain.newNeighborSet
    {G : SimpleGraph V} {ρ : ℝ} {U used W : Finset V} {k : ℕ}
    (chain : DiverseNeighborhoodChain G ρ U k used W) (i : Fin k) :
    Finset V :=
  neighborsIn G (chain.vertexAt i) (chain.priorSet i)

noncomputable def DiverseNeighborhoodChain.remainingSet
    {G : SimpleGraph V} {ρ : ℝ} {U used W : Finset V} {k : ℕ}
    (chain : DiverseNeighborhoodChain G ρ U k used W) (i : Fin k) :
    Finset V :=
  chain.priorSet i \ chain.newNeighborSet i

lemma DiverseNeighborhoodChain.priorSet_eq
    {G : SimpleGraph V} {ρ : ℝ} {U used W : Finset V} {k : ℕ}
    (chain : DiverseNeighborhoodChain G ρ U k used W) (i : Fin k) :
    chain.priorSet i = (chain.stageAt i).priorResidual := by
  exact (chain.stageAt_priorResidual_eq i).symm

lemma DiverseNeighborhoodChain.stageAt_priorResidual_card_lower
    {G : SimpleGraph V} {ρ : ℝ} {U used W : Finset V} {k : ℕ}
    (chain : DiverseNeighborhoodChain G ρ U k used W) (hρ : 0 ≤ ρ)
    (i : Fin k) :
    ρ ^ i.val * Fintype.card V ≤ (chain.stageAt i).priorResidual.card := by
  induction chain with
  | nil => exact Fin.elim0 i
  | @cons k used W tail v hvU hvfresh hn hnn ih =>
      refine Fin.lastCases ?_ (fun j ↦ ?_) i
      · simpa [DiverseNeighborhoodChain.stageAt] using
          tail.residual_card_lower hρ
      · simpa [DiverseNeighborhoodChain.stageAt] using ih j

lemma DiverseNeighborhoodChain.stageAt_neighbors_card_lower
    {G : SimpleGraph V} {ρ : ℝ} {U used W : Finset V} {k : ℕ}
    (chain : DiverseNeighborhoodChain G ρ U k used W) (hρ : 0 ≤ ρ)
    (i : Fin k) :
    ρ ^ (i.val + 1) * Fintype.card V <
      (neighborsIn G (chain.stageAt i).vertex
        (chain.stageAt i).priorResidual).card := by
  have hprior := chain.stageAt_priorResidual_card_lower hρ i
  calc
    ρ ^ (i.val + 1) * Fintype.card V =
        ρ * (ρ ^ i.val * Fintype.card V) := by rw [pow_succ]; ring
    _ ≤ ρ * (chain.stageAt i).priorResidual.card :=
      mul_le_mul_of_nonneg_left hprior hρ
    _ < (neighborsIn G (chain.stageAt i).vertex
          (chain.stageAt i).priorResidual).card :=
      (chain.stageAt i).neighbors_large

lemma DiverseNeighborhoodChain.stageAt_nonneighbors_card_lower
    {G : SimpleGraph V} {ρ : ℝ} {U used W : Finset V} {k : ℕ}
    (chain : DiverseNeighborhoodChain G ρ U k used W) (hρ : 0 ≤ ρ)
    (i : Fin k) :
    ρ ^ (i.val + 1) * Fintype.card V <
      ((chain.stageAt i).priorResidual \ neighborsIn G
        (chain.stageAt i).vertex (chain.stageAt i).priorResidual).card := by
  have hprior := chain.stageAt_priorResidual_card_lower hρ i
  calc
    ρ ^ (i.val + 1) * Fintype.card V =
        ρ * (ρ ^ i.val * Fintype.card V) := by rw [pow_succ]; ring
    _ ≤ ρ * (chain.stageAt i).priorResidual.card :=
      mul_le_mul_of_nonneg_left hprior hρ
    _ < ((chain.stageAt i).priorResidual \ neighborsIn G
          (chain.stageAt i).vertex (chain.stageAt i).priorResidual).card :=
      (chain.stageAt i).nonneighbors_large

/-- The first half of source equation (8.3), now stated with the explicit
set of vertices avoiding all previously chosen neighborhoods. -/
lemma DiverseNeighborhoodChain.card_newNeighborSet_lower
    {G : SimpleGraph V} {ρ : ℝ} {U used W : Finset V} {k : ℕ}
    (chain : DiverseNeighborhoodChain G ρ U k used W) (hρ : 0 ≤ ρ)
    (i : Fin k) :
    ρ ^ (i.val + 1) * Fintype.card V < (chain.newNeighborSet i).card := by
  rw [DiverseNeighborhoodChain.newNeighborSet,
    DiverseNeighborhoodChain.vertexAt, chain.priorSet_eq]
  exact chain.stageAt_neighbors_card_lower hρ i

/-- The second half of source equation (8.3), for the residual avoiding the
current vertex as well as every earlier one. -/
lemma DiverseNeighborhoodChain.card_remainingSet_lower
    {G : SimpleGraph V} {ρ : ℝ} {U used W : Finset V} {k : ℕ}
    (chain : DiverseNeighborhoodChain G ρ U k used W) (hρ : 0 ≤ ρ)
    (i : Fin k) :
    ρ ^ (i.val + 1) * Fintype.card V < (chain.remainingSet i).card := by
  rw [DiverseNeighborhoodChain.remainingSet,
    DiverseNeighborhoodChain.newNeighborSet,
    DiverseNeighborhoodChain.vertexAt, chain.priorSet_eq]
  exact chain.stageAt_nonneighbors_card_lower hρ i

noncomputable def DiverseNeighborhoodChain.mono
    {G : SimpleGraph V} {ρ : ℝ} {U U' used W : Finset V} {k : ℕ}
    (hUU' : U ⊆ U')
    (chain : DiverseNeighborhoodChain G ρ U k used W) :
    DiverseNeighborhoodChain G ρ U' k used W := by
  induction chain with
  | nil => exact DiverseNeighborhoodChain.nil
  | cons tail v hvU hvfresh hn hnn ih =>
      exact DiverseNeighborhoodChain.cons ih v (hUU' hvU) hvfresh hn hnn

/-- A finite collection of pairwise vertex-disjoint chains satisfying the
successive neighborhood/nonneighborhood lower bounds of equation (8.3). -/
inductive DiverseNeighborhoodFamily (G : SimpleGraph V) (ρ : ℝ)
    (R : Finset V) (q : ℕ) : (ℓ : ℕ) → Finset V → Type u
  | nil : DiverseNeighborhoodFamily G ρ R q 0 ∅
  | cons {ℓ : ℕ} {allUsed used W : Finset V}
      (family : DiverseNeighborhoodFamily G ρ R q ℓ allUsed)
      (chain : DiverseNeighborhoodChain G ρ R q used W)
      (disjoint : Disjoint allUsed used) :
      DiverseNeighborhoodFamily G ρ R q (ℓ + 1) (allUsed ∪ used)

structure DiverseNeighborhoodChainWitness (G : SimpleGraph V) (ρ : ℝ)
    (R : Finset V) (q : ℕ) where
  used : Finset V
  residual : Finset V
  chain : DiverseNeighborhoodChain G ρ R q used residual

noncomputable def DiverseNeighborhoodFamily.chainAt
    {G : SimpleGraph V} {ρ : ℝ} {R allUsed : Finset V} {q ℓ : ℕ}
    (family : DiverseNeighborhoodFamily G ρ R q ℓ allUsed) :
    Fin ℓ → DiverseNeighborhoodChainWitness G ρ R q := by
  induction family with
  | nil => exact Fin.elim0
  | @cons ℓ allUsed used W family chain hdisjoint ih =>
      exact Fin.lastCases
        { used := used, residual := W, chain := chain }
        ih

@[simp] lemma DiverseNeighborhoodFamily.chainAt_cons_castSucc
    {G : SimpleGraph V} {ρ : ℝ} {R allUsed used W : Finset V} {q ℓ : ℕ}
    (family : DiverseNeighborhoodFamily G ρ R q ℓ allUsed)
    (chain : DiverseNeighborhoodChain G ρ R q used W)
    (hdisjoint : Disjoint allUsed used) (i : Fin ℓ) :
    (DiverseNeighborhoodFamily.cons family chain hdisjoint).chainAt i.castSucc =
      family.chainAt i := by
  simp [DiverseNeighborhoodFamily.chainAt]

@[simp] lemma DiverseNeighborhoodFamily.chainAt_cons_last
    {G : SimpleGraph V} {ρ : ℝ} {R allUsed used W : Finset V} {q ℓ : ℕ}
    (family : DiverseNeighborhoodFamily G ρ R q ℓ allUsed)
    (chain : DiverseNeighborhoodChain G ρ R q used W)
    (hdisjoint : Disjoint allUsed used) :
    (DiverseNeighborhoodFamily.cons family chain hdisjoint).chainAt (Fin.last ℓ) =
      { used := used, residual := W, chain := chain } := by
  simp [DiverseNeighborhoodFamily.chainAt]

lemma DiverseNeighborhoodFamily.used_subset
    {G : SimpleGraph V} {ρ : ℝ} {R allUsed : Finset V} {q ℓ : ℕ}
    (family : DiverseNeighborhoodFamily G ρ R q ℓ allUsed) :
    allUsed ⊆ R := by
  induction family with
  | nil => simp
  | cons family chain hdisjoint ih =>
      exact Finset.union_subset ih chain.used_subset

lemma DiverseNeighborhoodFamily.chainAt_used_subset
    {G : SimpleGraph V} {ρ : ℝ} {R allUsed : Finset V} {q ℓ : ℕ}
    (family : DiverseNeighborhoodFamily G ρ R q ℓ allUsed)
    (i : Fin ℓ) :
    (family.chainAt i).used ⊆ allUsed := by
  induction family with
  | nil => exact Fin.elim0 i
  | @cons ℓ allUsed used W family chain hdisjoint ih =>
      refine Fin.lastCases ?_ (fun j ↦ ?_) i
      · simp
      · simpa using (ih j).trans Finset.subset_union_left

lemma DiverseNeighborhoodFamily.chainAt_disjoint
    {G : SimpleGraph V} {ρ : ℝ} {R allUsed : Finset V} {q ℓ : ℕ}
    (family : DiverseNeighborhoodFamily G ρ R q ℓ allUsed)
    {i j : Fin ℓ} (hij : i ≠ j) :
    Disjoint (family.chainAt i).used (family.chainAt j).used := by
  induction family with
  | nil => exact Fin.elim0 i
  | @cons ℓ allUsed used W family chain hdisjoint ih =>
      revert hij
      refine Fin.lastCases ?_ (fun i ↦ ?_) i
      · refine Fin.lastCases ?_ (fun j ↦ ?_) j
        · intro h
          exact (h rfl).elim
        · intro _
          simpa using hdisjoint.symm.mono Finset.Subset.rfl
            (family.chainAt_used_subset j)
      · refine Fin.lastCases ?_ (fun j ↦ ?_) j
        · intro _
          simpa using hdisjoint.mono (family.chainAt_used_subset i)
            Finset.Subset.rfl
        · intro h
          have hij' : i ≠ j := by
            intro h'
            apply h
            exact congrArg Fin.castSucc h'
          simpa using ih hij'

lemma card_sdiff_lower_of_add_le_of_lt
    {S D : Finset V} {a b : ℝ}
    (hbudget : a + D.card ≤ b) (hlower : b < S.card) :
    a < (S \ D).card := by
  have hcardNat : S.card ≤ (S \ D).card + D.card :=
    Finset.card_le_card_sdiff_add_card
  have hcard : (S.card : ℝ) ≤ (S \ D).card + D.card := by
    exact_mod_cast hcardNat
  linarith

/-- Removing all tuple vertices to form the eventual `J` side costs at most
the total support cardinality. This is the exact finite trimming step from
source equation (8.3) to equation (8.2). -/
lemma DiverseNeighborhoodFamily.card_newNeighborSet_sdiff_lower
    {G : SimpleGraph V} {ρ : ℝ} {R allUsed : Finset V} {q ℓ : ℕ}
    (family : DiverseNeighborhoodFamily G ρ R q ℓ allUsed)
    (hρ : 0 ≤ ρ) (a : Fin ℓ) (i : Fin q) {s : ℝ}
    (hs : s + allUsed.card ≤
      ρ ^ (i.val + 1) * Fintype.card V) :
    s < (((family.chainAt a).chain.newNeighborSet i) \ allUsed).card := by
  apply card_sdiff_lower_of_add_le_of_lt hs
  exact (family.chainAt a).chain.card_newNeighborSet_lower hρ i

lemma DiverseNeighborhoodFamily.card_remainingSet_sdiff_lower
    {G : SimpleGraph V} {ρ : ℝ} {R allUsed : Finset V} {q ℓ : ℕ}
    (family : DiverseNeighborhoodFamily G ρ R q ℓ allUsed)
    (hρ : 0 ≤ ρ) (a : Fin ℓ) (i : Fin q) {s : ℝ}
    (hs : s + allUsed.card ≤
      ρ ^ (i.val + 1) * Fintype.card V) :
    s < (((family.chainAt a).chain.remainingSet i) \ allUsed).card := by
  apply card_sdiff_lower_of_add_le_of_lt hs
  exact (family.chainAt a).chain.card_remainingSet_lower hρ i

@[simp] lemma DiverseNeighborhoodFamily.used_card
    {G : SimpleGraph V} {ρ : ℝ} {R allUsed : Finset V} {q ℓ : ℕ}
    (family : DiverseNeighborhoodFamily G ρ R q ℓ allUsed) :
    allUsed.card = ℓ * q := by
  induction family with
  | nil => simp
  | @cons ℓ allUsed used W family chain hdisjoint ih =>
      rw [Finset.card_union_of_disjoint hdisjoint, ih, chain.used_card]
      simp [Nat.succ_mul]

/-- The exact greedy packing step in the proof of KSSS Lemma 8.2. The
single real-valued supply inequality records that enough candidates remain
after reserving `q` vertices for every chain. -/
theorem exists_diverseNeighborhoodFamily
    {G : SimpleGraph V} {δ ρ α : ℝ} (hrich : Rich G δ ρ α)
    (R : Finset V) (q ℓ : ℕ) (hρ : 0 ≤ ρ)
    (hresidual : ∀ k ≤ q,
      δ * Fintype.card V ≤ ρ ^ k * Fintype.card V)
    (hsupply : (Fintype.card V : ℝ) ^ α + ℓ * q < R.card) :
    ∃ allUsed, Nonempty (DiverseNeighborhoodFamily G ρ R q ℓ allUsed) := by
  induction ℓ with
  | zero => exact ⟨∅, ⟨DiverseNeighborhoodFamily.nil⟩⟩
  | succ ℓ ih =>
      have hsupply' : (Fintype.card V : ℝ) ^ α + ℓ * q < R.card := by
        apply lt_of_le_of_lt _ hsupply
        gcongr
        exact_mod_cast Nat.le_succ ℓ
      obtain ⟨allUsed, ⟨family⟩⟩ := ih hsupply'
      have hsub : allUsed ⊆ R := family.used_subset
      have hcard : allUsed.card = ℓ * q := family.used_card
      have hle : ℓ * q ≤ R.card := by
        rw [← hcard]
        exact Finset.card_le_card hsub
      have hremaining : (Fintype.card V : ℝ) ^ α + q <
          (R \ allUsed).card := by
        rw [Finset.card_sdiff_of_subset hsub, hcard, Nat.cast_sub hle]
        norm_num at hsupply ⊢
        linarith
      obtain ⟨used, W, ⟨chain⟩⟩ :=
        exists_diverseNeighborhoodChain hrich (R \ allUsed) q hρ
          hresidual hremaining
      have hused : used ⊆ R \ allUsed := chain.used_subset
      have hdisjoint : Disjoint allUsed used := by
        rw [Finset.disjoint_left]
        intro v hvAll hvUsed
        exact (Finset.mem_sdiff.mp (hused hvUsed)).2 hvAll
      have chain' : DiverseNeighborhoodChain G ρ R q used W :=
        chain.mono (Finset.sdiff_subset)
      exact ⟨allUsed ∪ used,
        ⟨DiverseNeighborhoodFamily.cons family chain' hdisjoint⟩⟩

end RichTupleFamilies

end QuadraticCancellation
end Erdos88
