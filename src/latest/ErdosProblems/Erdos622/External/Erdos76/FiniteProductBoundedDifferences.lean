/-
Copyright 2026 The Lean-Proofs Authors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    http://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/
import Mathlib.Probability.Moments.SubGaussian
import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic

/-!
# Bounded differences for arbitrary explicit finite products

Each coordinate `i` has a finite outcome type `Omega i` and an explicitly
normalized mass function `w i`.  The product law and all expectations and
tail masses are finite sums.  We prove the centered MGF estimate and the
upper and lower forms of McDiarmid's inequality.
-/

open Finset MeasureTheory Real ProbabilityTheory
open scoped BigOperators ENNReal NNReal

namespace Erdos76

noncomputable section

namespace FiniteProduct

variable {I : Type*} [Fintype I] [DecidableEq I]
variable {Omega : I → Type*} [∀ i, Fintype (Omega i)]

/-- Explicit mass of an outcome of a finite product. -/
def mass (w : ∀ i, Omega i → ℝ) (x : ∀ i, Omega i) : ℝ :=
  ∏ i, w i (x i)

/-- Explicit finite expectation under the product mass. -/
def expectation (w : ∀ i, Omega i → ℝ) (F : (∀ i, Omega i) → ℝ) : ℝ :=
  ∑ x, mass w x * F x

/-- Mass of the upper level set of `F`. -/
def upperTailMass (w : ∀ i, Omega i → ℝ) (F : (∀ i, Omega i) → ℝ)
    (r : ℝ) : ℝ :=
  ∑ x with r ≤ F x, mass w x

/-- Mass of the lower level set of `F`. -/
def lowerTailMass (w : ∀ i, Omega i → ℝ) (F : (∀ i, Omega i) → ℝ)
    (r : ℝ) : ℝ :=
  ∑ x with F x ≤ r, mass w x

/-- Homogeneous specialization of `mass`, convenient when every coordinate
has the same finite outcome type. -/
def productMass {J A : Type*} [Fintype J] (w : A → ℝ) (x : J → A) : ℝ :=
  ∏ j, w (x j)

/-- Homogeneous explicit product expectation. -/
def productExpectation {J A : Type*} [Fintype J] [DecidableEq J] [Fintype A]
    (w : A → ℝ) (F : (J → A) → ℝ) : ℝ :=
  ∑ x, productMass w x * F x

/-- Homogeneous explicit upper-tail mass. -/
def productUpperTailMass {J A : Type*} [Fintype J] [DecidableEq J] [Fintype A]
    (w : A → ℝ) (F : (J → A) → ℝ) (r : ℝ) : ℝ :=
  ∑ x with r ≤ F x, productMass w x

/-- Homogeneous explicit lower-tail mass. -/
def productLowerTailMass {J A : Type*} [Fintype J] [DecidableEq J] [Fintype A]
    (w : A → ℝ) (F : (J → A) → ℝ) (r : ℝ) : ℝ :=
  ∑ x with F x ≤ r, productMass w x

/-- Changing coordinate `i` changes the output by at most `c i`. -/
def HasBoundedDifferences (F : (∀ i, Omega i) → ℝ) (c : I → ℝ) : Prop :=
  ∀ (i : I) (x : ∀ i, Omega i) (a : Omega i),
    |F (Function.update x i a) - F x| ≤ c i

/-- The explicit product masses sum to one. -/
lemma sum_mass (w : ∀ i, Omega i → ℝ) (hw : ∀ i, ∑ a, w i a = 1) :
    ∑ x, mass w x = 1 := by
  calc
    ∑ x, mass w x = ∏ i, ∑ a, w i a := by
      symm
      simpa [mass] using
        (Finset.prod_univ_sum (fun i ↦ (univ : Finset (Omega i))) w)
    _ = 1 := by simp [hw]

lemma mass_nonneg (w : ∀ i, Omega i → ℝ) (hw₀ : ∀ i a, 0 ≤ w i a)
    (x : ∀ i, Omega i) : 0 ≤ mass w x := by
  exact prod_nonneg fun i _ ↦ hw₀ i (x i)

private lemma finite_hoeffding
    {A : Type*} [Fintype A] {w : A → ℝ} {X : A → ℝ}
    {lo hi c s : ℝ} (hw₀ : ∀ a, 0 ≤ w a) (hw : ∑ a, w a = 1)
    (hX : ∀ a, X a ∈ Set.Icc lo hi) (hrange : hi - lo ≤ c) :
    ∑ a, w a * exp (s * (X a - ∑ b, w b * X b)) ≤
      exp (c ^ 2 * s ^ 2 / 8) := by
  letI : MeasurableSpace A := ⊤
  let μ : Measure A := Measure.sum fun a ↦ ENNReal.ofReal (w a) • Measure.dirac a
  have hwsum : HasSum w 1 := by
    convert hasSum_fintype w using 1
    exact hw.symm
  letI : IsProbabilityMeasure μ :=
    HasSum.isProbabilityMeasure_sum_dirac hw₀ hwsum
  have hXmeas : AEMeasurable X μ := by fun_prop
  have hXrange : ∀ᵐ a ∂μ, X a ∈ Set.Icc lo hi := by
    filter_upwards [] with a
    exact hX a
  have hsub := ProbabilityTheory.hasSubgaussianMGF_of_mem_Icc hXmeas hXrange
  have hmgf := hsub.mgf_le s
  have hne : Nonempty A := by
    by_contra hn
    haveI : IsEmpty A := not_nonempty_iff.mp hn
    simpa using hw
  let a₀ : A := Classical.choice hne
  have hlohi : lo ≤ hi := (hX a₀).1.trans (hX a₀).2
  have hintegral (f : A → ℝ) : ∫ a, f a ∂μ = ∑ a, w a * f a := by
    simp only [μ]
    rw [integral_sum_dirac (f := f) (fun _ ↦ ENNReal.ofReal_ne_top), tsum_fintype]
    apply sum_congr rfl
    intro a _
    rw [ENNReal.toReal_ofReal (hw₀ a)]
    simp
  rw [ProbabilityTheory.mgf, hintegral, hintegral] at hmgf
  push_cast at hmgf
  calc
    ∑ a, w a * exp (s * (X a - ∑ b, w b * X b)) ≤
        exp ((|hi - lo| / 2) ^ 2 * s ^ 2 / 2) := hmgf
    _ = exp ((hi - lo) ^ 2 * s ^ 2 / 8) := by
      congr 1
      rw [abs_of_nonneg (sub_nonneg.mpr hlohi)]
      ring
    _ ≤ exp (c ^ 2 * s ^ 2 / 8) := by
      apply exp_le_exp.mpr
      have hd₀ : 0 ≤ hi - lo := by
        exact sub_nonneg.mpr hlohi
      have hc₀ : 0 ≤ c := hd₀.trans hrange
      have hsquare : (hi - lo) ^ 2 ≤ c ^ 2 := by nlinarith
      gcongr

private lemma finite_hoeffding_of_pairwise
    {A : Type*} [Fintype A] {w : A → ℝ} {X : A → ℝ}
    {c s : ℝ} (hw₀ : ∀ a, 0 ≤ w a) (hw : ∑ a, w a = 1)
    (hX : ∀ a b, |X a - X b| ≤ c) :
    ∑ a, w a * exp (s * (X a - ∑ b, w b * X b)) ≤
      exp (c ^ 2 * s ^ 2 / 8) := by
  have hne : Nonempty A := by
    by_contra hn
    haveI : IsEmpty A := not_nonempty_iff.mp hn
    simpa using hw
  let S : Finset ℝ := univ.image X
  have hS : S.Nonempty := by
    change (univ.image X).Nonempty
    rw [image_nonempty]
    exact univ_nonempty
  let lo : ℝ := S.min' hS
  let hi : ℝ := S.max' hS
  have hmem (a : A) : X a ∈ Set.Icc lo hi := by
    constructor
    · exact S.min'_le (X a) (by simp [S])
    · exact S.le_max' (X a) (by simp [S])
  have hrange : hi - lo ≤ c := by
    obtain ⟨a, -, ha⟩ := mem_image.mp (S.min'_mem hS)
    obtain ⟨b, -, hb⟩ := mem_image.mp (S.max'_mem hS)
    calc
      hi - lo ≤ |hi - lo| := le_abs_self _
      _ = |X b - X a| := by rw [ha, hb]
      _ ≤ c := hX b a
  exact finite_hoeffding hw₀ hw hmem hrange

private lemma abs_weighted_sum_sub_le
    {A : Type*} [Fintype A] {w X Y : A → ℝ} {c : ℝ}
    (hw₀ : ∀ a, 0 ≤ w a) (hw : ∑ a, w a = 1)
    (hXY : ∀ a, |Y a - X a| ≤ c) :
    |(∑ a, w a * Y a) - ∑ a, w a * X a| ≤ c := by
  calc
    |(∑ a, w a * Y a) - ∑ a, w a * X a| =
        |∑ a, w a * (Y a - X a)| := by
      congr 1
      rw [← sum_sub_distrib]
      apply sum_congr rfl
      intro a _
      ring
    _ ≤ ∑ a, |w a * (Y a - X a)| := abs_sum_le_sum_abs _ _
    _ = ∑ a, w a * |Y a - X a| := by
      apply sum_congr rfl
      intro a _
      rw [abs_mul, abs_of_nonneg (hw₀ a)]
    _ ≤ ∑ a, w a * c := by
      exact sum_le_sum fun a _ ↦ mul_le_mul_of_nonneg_left (hXY a) (hw₀ a)
    _ = c := by rw [← sum_mul, hw, one_mul]

private theorem centered_mgf_le_fin
    {n : ℕ} {Omega : Fin n → Type*} [∀ i, Fintype (Omega i)]
    (w : ∀ i, Omega i → ℝ) (F : (∀ i, Omega i) → ℝ) (c : Fin n → ℝ)
    (hw₀ : ∀ i a, 0 ≤ w i a) (hw : ∀ i, ∑ a, w i a = 1)
    (hF : HasBoundedDifferences F c) (s : ℝ) :
    ∑ x, mass w x * exp (s * (F x - expectation w F)) ≤
      exp (s ^ 2 * (∑ i, c i ^ 2) / 8) := by
  induction n with
  | zero => simp [mass, expectation]
  | succ n ih =>
      let wt : ∀ i : Fin n, Omega i.succ → ℝ := fun i ↦ w i.succ
      let G : (∀ i : Fin n, Omega i.succ) → ℝ := fun y ↦
        ∑ a, w 0 a * F (Fin.cons a y)
      have hwt₀ : ∀ i a, 0 ≤ wt i a := fun i a ↦ hw₀ i.succ a
      have hwt : ∀ i, ∑ a, wt i a = 1 := fun i ↦ hw i.succ
      have hG : HasBoundedDifferences G (fun i ↦ c i.succ) := by
        intro i y b
        apply abs_weighted_sum_sub_le (hw₀ 0) (hw 0)
        intro a
        have heq : Fin.cons a (Function.update y i b) =
            Function.update (Fin.cons a y) i.succ b := Fin.cons_update a y i b
        rw [heq]
        exact hF i.succ (Fin.cons a y) b
      have hmean : expectation w F = expectation wt G := by
        unfold expectation
        calc
          ∑ x, mass w x * F x =
              ∑ z : Omega 0 × (∀ i : Fin n, Omega i.succ),
                mass w ((Fin.consEquiv Omega) z) * F ((Fin.consEquiv Omega) z) :=
            ((Fin.consEquiv Omega).sum_comp (fun x ↦ mass w x * F x)).symm
          _ = ∑ y, mass wt y * G y := by
            simp only [Fintype.sum_prod_type]
            change (∑ a, ∑ y, mass w (Fin.cons a y) * F (Fin.cons a y)) =
              ∑ y, mass wt y * G y
            rw [sum_comm]
            simp only [mass, Fin.prod_univ_succ, Fin.cons_zero, Fin.cons_succ, wt, G]
            apply sum_congr rfl
            intro y _
            rw [mul_sum]
            apply sum_congr rfl
            intro a _
            ring
      have hhead (y : ∀ i : Fin n, Omega i.succ) :
          ∑ a, w 0 a * exp (s * (F (Fin.cons a y) - G y)) ≤
            exp (c 0 ^ 2 * s ^ 2 / 8) := by
        apply finite_hoeffding_of_pairwise (hw₀ 0) (hw 0)
        intro a b
        have hab := hF 0 (Fin.cons b y) a
        have heq : Function.update (Fin.cons b y) 0 a = Fin.cons a y :=
          Fin.update_cons_zero b y a
        rw [heq] at hab
        exact hab
      have htail := ih wt G (fun i ↦ c i.succ) hwt₀ hwt hG
      rw [hmean]
      rw [← (Fin.consEquiv Omega).sum_comp]
      simp only [Fintype.sum_prod_type]
      rw [sum_comm]
      simp only [mass, Fin.prod_univ_succ, Fin.cons_zero, Fin.cons_succ, wt]
      calc
        ∑ y, ∑ a,
            (w 0 a * ∏ i, w i.succ (y i)) *
              exp (s * (F (Fin.cons a y) - expectation wt G)) =
            ∑ y, (∏ i, wt i (y i)) * exp (s * (G y - expectation wt G)) *
              (∑ a, w 0 a * exp (s * (F (Fin.cons a y) - G y))) := by
          apply sum_congr rfl
          intro y _
          rw [mul_sum]
          apply sum_congr rfl
          intro a _
          have hexp :
              exp (s * (F (Fin.cons a y) - expectation wt G)) =
                exp (s * (G y - expectation wt G)) *
                  exp (s * (F (Fin.cons a y) - G y)) := by
            rw [← exp_add]
            congr 1
            ring
          rw [hexp]
          simp only [wt]
          ring
        _ ≤ ∑ y, (∏ i, wt i (y i)) * exp (s * (G y - expectation wt G)) *
              exp (c 0 ^ 2 * s ^ 2 / 8) := by
          apply sum_le_sum
          intro y _
          exact mul_le_mul_of_nonneg_left (hhead y)
            (mul_nonneg (prod_nonneg fun i _ ↦ hwt₀ i (y i)) (exp_pos _).le)
        _ = exp (c 0 ^ 2 * s ^ 2 / 8) *
              (∑ y, mass wt y * exp (s * (G y - expectation wt G))) := by
          simp only [mass]
          rw [mul_sum]
          apply sum_congr rfl
          intro y _
          ring
        _ ≤ exp (c 0 ^ 2 * s ^ 2 / 8) *
              exp (s ^ 2 * (∑ i : Fin n, c i.succ ^ 2) / 8) := by
          exact mul_le_mul_of_nonneg_left htail (exp_pos _).le
        _ = exp (s ^ 2 * (∑ i : Fin (n + 1), c i ^ 2) / 8) := by
          rw [← exp_add, Fin.sum_univ_succ]
          congr 1
          ring

/-- Sharp centered moment-generating-function bound for an arbitrary
explicit finite product law. -/
theorem centered_mgf_le
    (w : ∀ i, Omega i → ℝ) (F : (∀ i, Omega i) → ℝ) (c : I → ℝ)
    (hw₀ : ∀ i a, 0 ≤ w i a) (hw : ∀ i, ∑ a, w i a = 1)
    (hF : HasBoundedDifferences F c) (s : ℝ) :
    ∑ x, mass w x * exp (s * (F x - expectation w F)) ≤
      exp (s ^ 2 * (∑ i, c i ^ 2) / 8) := by
  let e : I ≃ Fin (Fintype.card I) := Fintype.equivFin I
  let q : (∀ i, Omega i) ≃ (∀ k, Omega (e.symm k)) := e.piCongrLeft' Omega
  let wf : ∀ k, Omega (e.symm k) → ℝ := fun k ↦ w (e.symm k)
  let Ff : (∀ k, Omega (e.symm k)) → ℝ := fun y ↦ F (q.symm y)
  let cf : Fin (Fintype.card I) → ℝ := fun k ↦ c (e.symm k)
  have hwf₀ : ∀ k a, 0 ≤ wf k a := fun k a ↦ hw₀ (e.symm k) a
  have hwf : ∀ k, ∑ a, wf k a = 1 := fun k ↦ hw (e.symm k)
  have hFf : HasBoundedDifferences Ff cf := by
    intro k y a
    have hk := hF (e.symm k) (q.symm y) a
    change |F (q.symm (Function.update y k a)) - F (q.symm y)| ≤ c (e.symm k)
    rw [Function.piCongrLeft'_symm_update Omega e y k a]
    exact hk
  have hmass (x : ∀ i, Omega i) : mass wf (q x) = mass w x := by
    simp only [mass, wf, q, Equiv.piCongrLeft'_apply]
    exact e.symm.prod_comp (fun i ↦ w i (x i))
  have hmean : expectation wf Ff = expectation w F := by
    unfold expectation
    calc
      ∑ y, mass wf y * Ff y = ∑ x, mass wf (q x) * Ff (q x) :=
        (q.sum_comp fun y ↦ mass wf y * Ff y).symm
      _ = ∑ x, mass w x * F x := by
        apply sum_congr rfl
        intro x _
        rw [hmass]
        simp [Ff, q]
  have hfin := centered_mgf_le_fin wf Ff cf hwf₀ hwf hFf s
  calc
    ∑ x, mass w x * exp (s * (F x - expectation w F)) =
        ∑ x, mass wf (q x) * exp (s * (Ff (q x) - expectation wf Ff)) := by
      apply sum_congr rfl
      intro x _
      rw [hmass, hmean]
      simp [Ff, q]
    _ = ∑ y, mass wf y * exp (s * (Ff y - expectation wf Ff)) :=
      q.sum_comp fun y ↦ mass wf y * exp (s * (Ff y - expectation wf Ff))
    _ ≤ exp (s ^ 2 * (∑ k, cf k ^ 2) / 8) := hfin
    _ = exp (s ^ 2 * (∑ i, c i ^ 2) / 8) := by
      congr 1
      have hsum : ∑ k, cf k ^ 2 = ∑ i, c i ^ 2 := by
        simpa [cf] using e.symm.sum_comp (fun i ↦ c i ^ 2)
      rw [hsum]

/-- Exponential upper-tail estimate before optimizing the exponential
parameter. -/
theorem upperTailMass_le_exp
    (w : ∀ i, Omega i → ℝ) (F : (∀ i, Omega i) → ℝ) (c : I → ℝ)
    (hw₀ : ∀ i a, 0 ≤ w i a) (hw : ∀ i, ∑ a, w i a = 1)
    (hF : HasBoundedDifferences F c) {s t : ℝ} (hs : 0 ≤ s) :
    upperTailMass w F (expectation w F + t) ≤
      exp (s ^ 2 * (∑ i, c i ^ 2) / 8 - s * t) := by
  have hmgf := centered_mgf_le w F c hw₀ hw hF s
  have hweighted :
      exp (s * t) * upperTailMass w F (expectation w F + t) ≤
        ∑ x, mass w x * exp (s * (F x - expectation w F)) := by
    unfold upperTailMass
    calc
      exp (s * t) * ∑ x with expectation w F + t ≤ F x, mass w x =
          ∑ x with expectation w F + t ≤ F x, mass w x * exp (s * t) := by
        rw [mul_sum]
        apply sum_congr rfl
        intro x _
        ring
      _ ≤ ∑ x with expectation w F + t ≤ F x,
            mass w x * exp (s * (F x - expectation w F)) := by
        apply sum_le_sum
        intro x hx
        have hxt : t ≤ F x - expectation w F := by
          simp only [mem_filter, mem_univ, true_and] at hx
          linarith
        exact mul_le_mul_of_nonneg_left
          (exp_le_exp.mpr (mul_le_mul_of_nonneg_left hxt hs))
          (mass_nonneg w hw₀ x)
      _ ≤ ∑ x, mass w x * exp (s * (F x - expectation w F)) := by
        exact sum_le_sum_of_subset_of_nonneg (filter_subset _ _)
          (fun x _ _ ↦ mul_nonneg (mass_nonneg w hw₀ x) (exp_pos _).le)
  calc
    upperTailMass w F (expectation w F + t) =
        (exp (s * t) * upperTailMass w F (expectation w F + t)) / exp (s * t) := by
      field_simp
    _ ≤ exp (s ^ 2 * (∑ i, c i ^ 2) / 8) / exp (s * t) := by
      exact div_le_div_of_nonneg_right (hweighted.trans hmgf) (exp_pos _).le
    _ = exp (s ^ 2 * (∑ i, c i ^ 2) / 8 - s * t) := by
      rw [exp_sub]

/-- Exponential lower-tail estimate before optimizing the exponential
parameter. -/
theorem lowerTailMass_le_exp
    (w : ∀ i, Omega i → ℝ) (F : (∀ i, Omega i) → ℝ) (c : I → ℝ)
    (hw₀ : ∀ i a, 0 ≤ w i a) (hw : ∀ i, ∑ a, w i a = 1)
    (hF : HasBoundedDifferences F c) {s t : ℝ} (hs : 0 ≤ s) :
    lowerTailMass w F (expectation w F - t) ≤
      exp (s ^ 2 * (∑ i, c i ^ 2) / 8 - s * t) := by
  have hmgf := centered_mgf_le w F c hw₀ hw hF (-s)
  have hweighted :
      exp (s * t) * lowerTailMass w F (expectation w F - t) ≤
        ∑ x, mass w x * exp ((-s) * (F x - expectation w F)) := by
    unfold lowerTailMass
    calc
      exp (s * t) * ∑ x with F x ≤ expectation w F - t, mass w x =
          ∑ x with F x ≤ expectation w F - t, mass w x * exp (s * t) := by
        rw [mul_sum]
        apply sum_congr rfl
        intro x _
        ring
      _ ≤ ∑ x with F x ≤ expectation w F - t,
            mass w x * exp ((-s) * (F x - expectation w F)) := by
        apply sum_le_sum
        intro x hx
        have hxt : s * t ≤ (-s) * (F x - expectation w F) := by
          simp only [mem_filter, mem_univ, true_and] at hx
          nlinarith
        exact mul_le_mul_of_nonneg_left (exp_le_exp.mpr hxt) (mass_nonneg w hw₀ x)
      _ ≤ ∑ x, mass w x * exp ((-s) * (F x - expectation w F)) := by
        exact sum_le_sum_of_subset_of_nonneg (filter_subset _ _)
          (fun x _ _ ↦ mul_nonneg (mass_nonneg w hw₀ x) (exp_pos _).le)
  calc
    lowerTailMass w F (expectation w F - t) =
        (exp (s * t) * lowerTailMass w F (expectation w F - t)) / exp (s * t) := by
      field_simp
    _ ≤ exp ((-s) ^ 2 * (∑ i, c i ^ 2) / 8) / exp (s * t) := by
      exact div_le_div_of_nonneg_right (hweighted.trans hmgf) (exp_pos _).le
    _ = exp (s ^ 2 * (∑ i, c i ^ 2) / 8 - s * t) := by
      rw [exp_sub]
      congr 1
      ring

/-- Sharp McDiarmid upper tail for an arbitrary explicit finite product. -/
theorem upperTailMass_le_mcdiarmid
    (w : ∀ i, Omega i → ℝ) (F : (∀ i, Omega i) → ℝ) (c : I → ℝ)
    (hw₀ : ∀ i a, 0 ≤ w i a) (hw : ∀ i, ∑ a, w i a = 1)
    (hF : HasBoundedDifferences F c) {t : ℝ} (ht : 0 ≤ t)
    (hC : 0 < ∑ i, c i ^ 2) :
    upperTailMass w F (expectation w F + t) ≤
      exp (-2 * t ^ 2 / (∑ i, c i ^ 2)) := by
  let C := ∑ i, c i ^ 2
  have hs : 0 ≤ 4 * t / C := div_nonneg (mul_nonneg (by norm_num) ht) hC.le
  have h := upperTailMass_le_exp w F c hw₀ hw hF (t := t) hs
  calc
    upperTailMass w F (expectation w F + t) ≤
        exp ((4 * t / C) ^ 2 * C / 8 - (4 * t / C) * t) := by simpa [C] using h
    _ = exp (-2 * t ^ 2 / C) := by
      congr 1
      field_simp [ne_of_gt hC]
      ring
    _ = exp (-2 * t ^ 2 / (∑ i, c i ^ 2)) := rfl

/-- Sharp McDiarmid lower tail for an arbitrary explicit finite product. -/
theorem lowerTailMass_le_mcdiarmid
    (w : ∀ i, Omega i → ℝ) (F : (∀ i, Omega i) → ℝ) (c : I → ℝ)
    (hw₀ : ∀ i a, 0 ≤ w i a) (hw : ∀ i, ∑ a, w i a = 1)
    (hF : HasBoundedDifferences F c) {t : ℝ} (ht : 0 ≤ t)
    (hC : 0 < ∑ i, c i ^ 2) :
    lowerTailMass w F (expectation w F - t) ≤
      exp (-2 * t ^ 2 / (∑ i, c i ^ 2)) := by
  let C := ∑ i, c i ^ 2
  have hs : 0 ≤ 4 * t / C := div_nonneg (mul_nonneg (by norm_num) ht) hC.le
  have h := lowerTailMass_le_exp w F c hw₀ hw hF (t := t) hs
  calc
    lowerTailMass w F (expectation w F - t) ≤
        exp ((4 * t / C) ^ 2 * C / 8 - (4 * t / C) * t) := by simpa [C] using h
    _ = exp (-2 * t ^ 2 / C) := by
      congr 1
      field_simp [ne_of_gt hC]
      ring
    _ = exp (-2 * t ^ 2 / (∑ i, c i ^ 2)) := rfl

/-- If the two McDiarmid tails have total mass strictly below one, some explicit
product outcome lies strictly within the requested deviation. -/
theorem exists_abs_sub_expectation_lt
    (w : ∀ i, Omega i → ℝ) (F : (∀ i, Omega i) → ℝ) (c : I → ℝ)
    (hw₀ : ∀ i a, 0 ≤ w i a) (hw : ∀ i, ∑ a, w i a = 1)
    (hF : HasBoundedDifferences F c) {t : ℝ} (ht : 0 ≤ t)
    (hC : 0 < ∑ i, c i ^ 2)
    (hsmall : 2 * exp (-2 * t ^ 2 / (∑ i, c i ^ 2)) < 1) :
    ∃ x, |F x - expectation w F| < t := by
  by_contra hnone
  push Not at hnone
  have hcover (x : ∀ i, Omega i) :
      expectation w F + t ≤ F x ∨ F x ≤ expectation w F - t := by
    have hx : t ≤ |F x - expectation w F| := hnone x
    rcases le_abs.mp hx with hx | hx
    · left
      linarith
    · right
      linarith
  have htotal :
      1 ≤ upperTailMass w F (expectation w F + t) +
        lowerTailMass w F (expectation w F - t) := by
    calc
      1 = ∑ x, mass w x := (sum_mass w hw).symm
      _ ≤ ∑ x, ((if expectation w F + t ≤ F x then mass w x else 0) +
            if F x ≤ expectation w F - t then mass w x else 0) := by
        apply sum_le_sum
        intro x _
        rcases hcover x with hx | hx
        · simp only [hx, if_true]
          split_ifs <;> simp [mass_nonneg w hw₀ x]
        · simp only [hx, if_true]
          split_ifs <;> simp [mass_nonneg w hw₀ x]
      _ = upperTailMass w F (expectation w F + t) +
            lowerTailMass w F (expectation w F - t) := by
        rw [sum_add_distrib]
        simp only [upperTailMass, lowerTailMass, ← Finset.sum_filter]
  have hu := upperTailMass_le_mcdiarmid w F c hw₀ hw hF ht hC
  have hl := lowerTailMass_le_mcdiarmid w F c hw₀ hw hF ht hC
  have : 1 ≤ 2 * exp (-2 * t ^ 2 / (∑ i, c i ^ 2)) := by
    calc
      1 ≤ upperTailMass w F (expectation w F + t) +
          lowerTailMass w F (expectation w F - t) := htotal
      _ ≤ exp (-2 * t ^ 2 / (∑ i, c i ^ 2)) +
          exp (-2 * t ^ 2 / (∑ i, c i ^ 2)) := add_le_add hu hl
      _ = 2 * exp (-2 * t ^ 2 / (∑ i, c i ^ 2)) := by ring
  linarith

/-- Homogeneous-product form of the sharp McDiarmid upper tail.  This is the
direct interface for treating one whole randomized inner sample as each
coordinate of an outer batch. -/
theorem productUpperTailMass_le_mcdiarmid
    {J A : Type*} [Fintype J] [DecidableEq J] [Fintype A]
    (w : A → ℝ) (F : (J → A) → ℝ) (c : J → ℝ)
    (hw₀ : ∀ a, 0 ≤ w a) (hw : ∑ a, w a = 1)
    (hF : ∀ (j : J) (x : J → A) (a : A),
      |F (Function.update x j a) - F x| ≤ c j)
    {t : ℝ} (ht : 0 ≤ t) (hC : 0 < ∑ j, c j ^ 2) :
    productUpperTailMass w F (productExpectation w F + t) ≤
      exp (-2 * t ^ 2 / (∑ j, c j ^ 2)) := by
  change upperTailMass (Omega := fun _ : J ↦ A) (fun _ ↦ w) F
    (expectation (fun _ ↦ w) F + t) ≤ exp (-2 * t ^ 2 / (∑ j, c j ^ 2))
  exact upperTailMass_le_mcdiarmid (fun _ ↦ w) F c
    (fun _ ↦ hw₀) (fun _ ↦ hw) hF ht hC

/-- Homogeneous-product form of the sharp McDiarmid lower tail. -/
theorem productLowerTailMass_le_mcdiarmid
    {J A : Type*} [Fintype J] [DecidableEq J] [Fintype A]
    (w : A → ℝ) (F : (J → A) → ℝ) (c : J → ℝ)
    (hw₀ : ∀ a, 0 ≤ w a) (hw : ∑ a, w a = 1)
    (hF : ∀ (j : J) (x : J → A) (a : A),
      |F (Function.update x j a) - F x| ≤ c j)
    {t : ℝ} (ht : 0 ≤ t) (hC : 0 < ∑ j, c j ^ 2) :
    productLowerTailMass w F (productExpectation w F - t) ≤
      exp (-2 * t ^ 2 / (∑ j, c j ^ 2)) := by
  change lowerTailMass (Omega := fun _ : J ↦ A) (fun _ ↦ w) F
    (expectation (fun _ ↦ w) F - t) ≤ exp (-2 * t ^ 2 / (∑ j, c j ^ 2))
  exact lowerTailMass_le_mcdiarmid (fun _ ↦ w) F c
    (fun _ ↦ hw₀) (fun _ ↦ hw) hF ht hC

/-- Homogeneous-product two-sided sample extraction. -/
theorem exists_product_abs_sub_expectation_lt
    {J A : Type*} [Fintype J] [DecidableEq J] [Fintype A]
    (w : A → ℝ) (F : (J → A) → ℝ) (c : J → ℝ)
    (hw₀ : ∀ a, 0 ≤ w a) (hw : ∑ a, w a = 1)
    (hF : ∀ (j : J) (x : J → A) (a : A),
      |F (Function.update x j a) - F x| ≤ c j)
    {t : ℝ} (ht : 0 ≤ t) (hC : 0 < ∑ j, c j ^ 2)
    (hsmall : 2 * exp (-2 * t ^ 2 / (∑ j, c j ^ 2)) < 1) :
    ∃ x, |F x - productExpectation w F| < t := by
  change ∃ x, |F x - expectation (fun _ : J ↦ w) F| < t
  exact exists_abs_sub_expectation_lt (fun _ ↦ w) F c
    (fun _ ↦ hw₀) (fun _ ↦ hw) hF ht hC hsmall

end FiniteProduct

end

end Erdos76
