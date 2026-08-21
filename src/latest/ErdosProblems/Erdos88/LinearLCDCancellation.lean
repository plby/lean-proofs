/- leanprover/lean4:v4.33.0 mathlib v4.33.0 -/
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

import ErdosProblems.Erdos88.GraphLinearNormalization
import ErdosProblems.Erdos88.RLCD
import ErdosProblems.Erdos88.Fourier
import ErdosProblems.Erdos88.RademacherHypercontractivity
import Mathlib.Analysis.Calculus.Taylor

/-!
# Regularized-LCD cancellation for Erdős Problem 88

This file develops the analytic and arithmetic ingredients of KSSS Lemma
7.2.  It begins with the real-part-sensitive Taylor estimate of Lemma 7.4.
-/

open scoped BigOperators symmDiff

namespace Erdos88
namespace LinearLCDCancellation

lemma iteratedDeriv_cexp_real_mul (k : ℕ) (z : ℂ) :
    iteratedDeriv k (fun t : ℝ ↦ Complex.exp ((t : ℂ) * z)) =
      fun t : ℝ ↦ z ^ k * Complex.exp ((t : ℂ) * z) := by
  induction k with
  | zero => simp
  | succ k hk =>
      rw [iteratedDeriv_succ, hk]
      funext t
      have hcast : HasDerivAt (fun s : ℝ ↦ (s : ℂ)) 1 t :=
        Complex.ofRealCLM.hasDerivAt
      have hphase : HasDerivAt
          (fun s : ℝ ↦ Complex.exp ((s : ℂ) * z))
          (Complex.exp ((t : ℂ) * z) * z) t :=
        by simpa using (hcast.mul_const z).cexp
      rw [(hphase.const_mul (z ^ k)).deriv]
      ring

/-- KSSS Lemma 7.4: the complex exponential Taylor remainder, with the
real-part-sensitive envelope used in the regularized-LCD argument. -/
theorem norm_cexp_sub_taylor_le (K : ℕ) (z : ℂ) :
    ‖Complex.exp z -
        ∑ j ∈ Finset.range (K + 1), z ^ j / (j.factorial : ℂ)‖ ≤
      Real.exp (max 0 z.re) * ‖z‖ ^ (K + 1) / K.factorial := by
  let f : ℝ → ℂ := fun t ↦ Complex.exp ((t : ℂ) * z)
  let C : ℝ := Real.exp (max 0 z.re) * ‖z‖ ^ (K + 1)
  have hfInf : ContDiff ℝ ⊤ f := by
    dsimp only [f]
    exact (Complex.ofRealCLM.contDiff.mul
      (contDiff_const : ContDiff ℝ ⊤ (fun _ : ℝ ↦ z))).cexp
  have hfK : ContDiff ℝ (K + 1) f := hfInf.of_le (by simp)
  have hf : ContDiffOn ℝ (K + 1) f (Set.Icc 0 1) :=
    hfK.contDiffOn
  have hiter (k : ℕ) (t : ℝ) :
      iteratedDeriv k f t = z ^ k * Complex.exp ((t : ℂ) * z) := by
    exact congrFun (iteratedDeriv_cexp_real_mul k z) t
  have hC : ∀ y ∈ Set.Icc (0 : ℝ) 1,
      ‖iteratedDerivWithin (K + 1) f (Set.Icc 0 1) y‖ ≤ C := by
    intro y hy
    rw [iteratedDerivWithin_eq_iteratedDeriv (n := K + 1)
      (s := Set.Icc (0 : ℝ) 1) (uniqueDiffOn_Icc (by norm_num))
      hfK.contDiffAt hy]
    rw [hiter]
    have hre : (((y : ℂ) * z).re : ℝ) ≤ max 0 z.re := by
      simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
      by_cases hz : 0 ≤ z.re
      · rw [max_eq_right hz]
        nlinarith [hy.1, hy.2]
      · rw [max_eq_left (le_of_not_ge hz)]
        nlinarith [hy.1]
    dsimp only [C]
    rw [norm_mul, norm_pow, Complex.norm_exp]
    calc
      ‖z‖ ^ (K + 1) * Real.exp (↑y * z).re ≤
          ‖z‖ ^ (K + 1) * Real.exp (max 0 z.re) :=
        mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hre)
          (pow_nonneg (norm_nonneg z) _)
      _ = Real.exp (max 0 z.re) * ‖z‖ ^ (K + 1) := by ring
  have htaylor : taylorWithinEval f K (Set.Icc 0 1) 0 1 =
      ∑ j ∈ Finset.range (K + 1), z ^ j / (j.factorial : ℂ) := by
    rw [taylor_within_apply]
    apply Finset.sum_congr rfl
    intro j hj
    have hfj : ContDiff ℝ j f := hfInf.of_le (by simp)
    rw [iteratedDerivWithin_eq_iteratedDeriv (n := j)
      (s := Set.Icc (0 : ℝ) 1) (uniqueDiffOn_Icc (by norm_num))
      hfj.contDiffAt (by norm_num)]
    rw [hiter]
    simp [div_eq_mul_inv]
    ring
  have hrem := taylor_mean_remainder_bound (f := f) (n := K)
    (a := 0) (b := 1) (C := C) (x := 1) (by norm_num) hf (by norm_num) hC
  rw [htaylor] at hrem
  simpa [f, C] using hrem

/-- The signed representative of a real number in the centered fundamental
domain modulo the integers. -/
noncomputable def centeredResidue (x : ℝ) : ℝ := x - (round x : ℝ)

lemma abs_centeredResidue (x : ℝ) :
    |centeredResidue x| = RLCD.distToInt x := by
  rfl

lemma centeredResidue_isCenteredModOne (x : ℝ) :
    Fourier.IsCenteredModOne x (centeredResidue x) := by
  refine ⟨?_, round x, ?_⟩
  · simpa only [centeredResidue] using abs_sub_round x
  · simp only [centeredResidue]
    ring

lemma centeredResidue_sq (x : ℝ) :
    centeredResidue x ^ 2 = RLCD.distToInt x ^ 2 := by
  rw [← sq_abs, abs_centeredResidue]

/-- The independent Rademacher characteristic function decays at least as
the squared Euclidean distance of its coefficient vector from the integer
lattice.  This is the lattice-distance form of KSSS (4.16) used in Lemma
7.2. -/
theorem norm_rademacherLinear_le_exp_neg_latticeDist_sq
    {I : Type*} [Fintype I] [DecidableEq I]
    (a : I → ℝ) (t : ℝ) :
    ‖Fourier.finCharFun (I → Bool)
        (fun ξ ↦ ∑ i, a i * Fourier.rademacherSign (ξ i)) t‖ ≤
      Real.exp (-(RLCD.latticeDist (fun i ↦ t * a i / Real.pi)) ^ 2) := by
  have hbase := Fourier.norm_finCharFun_rademacher_linear_le_exp_neg_sum_sq
    a (fun i ↦ centeredResidue (t * a i / Real.pi)) t
    (fun i ↦ centeredResidue_isCenteredModOne (t * a i / Real.pi))
  calc
    ‖Fourier.finCharFun (I → Bool)
        (fun ξ ↦ ∑ i, a i * Fourier.rademacherSign (ξ i)) t‖ ≤
        Real.exp (-∑ i, centeredResidue (t * a i / Real.pi) ^ 2) := hbase
    _ = Real.exp (-(RLCD.latticeDist (fun i ↦ t * a i / Real.pi)) ^ 2) := by
      congr 2
      rw [RLCD.latticeDist]
      have hnonneg : 0 ≤ ∑ i, RLCD.distToInt (t * a i / Real.pi) ^ 2 :=
        Finset.sum_nonneg fun _ _ ↦ sq_nonneg _
      rw [Real.sq_sqrt hnonneg]
      apply Finset.sum_congr rfl
      intro i hi
      exact centeredResidue_sq _

/-- Below the least common denominator, a positive scale is not admissible;
hence its lattice distance is at least the defining logarithmic threshold. -/
lemma latticeDist_ge_logThreshold_of_lt_LCD
    {I : Type*} [Fintype I] {L θ : ℝ} {v : I → ℝ}
    (hθ : 0 < θ) (hbelow : θ < RLCD.LCD L v) :
    L * Real.sqrt (RLCD.logPlus (θ / L)) ≤
      RLCD.latticeDist (fun i ↦ θ * v i) := by
  by_contra hbad
  have hmem : θ ∈ RLCD.lcdScales L v :=
    ⟨hθ, lt_of_not_ge hbad⟩
  exact (not_lt_of_ge (RLCD.LCD_le_of_mem hmem)) hbelow

/-- The maximum in the regularized LCD supplies a coordinate restriction
on which every smaller positive scale has the defining lattice-distance
lower bound. -/
theorem exists_coordinateSet_latticeDist_ge_of_lt_regularizedLCDCard
    {n k : ℕ} (L : ℝ) (d : Fin n → ℝ) (hk : k ≤ n)
    {θ : ℝ} (hθ : 0 < θ)
    (hbelow : θ < RLCD.regularizedLCDCard L k d) :
    ∃ I : Finset (Fin n), I.card = k ∧
      L * Real.sqrt (RLCD.logPlus (θ / L)) ≤
        RLCD.latticeDist
          (fun i : I ↦ θ * RLCD.normalizedRestrict d I i) := by
  obtain ⟨I, hI, hmax⟩ :=
    RLCD.exists_coordinateSet_eq_regularizedLCDCard L d hk
  refine ⟨I, RLCD.mem_coordinateSets.mp hI, ?_⟩
  apply latticeDist_ge_logThreshold_of_lt_LCD hθ
  rwa [← hmax]

/-- Independent-coordinate cancellation on the restriction realizing the
regularized LCD.  This is the direct analytic consequence of the defining
LCD separation, before the Walsh/Taylor perturbation of KSSS Lemma 7.2. -/
theorem exists_coordinateSet_rademacher_decay_of_lt_regularizedLCDCard
    {n k : ℕ} (L : ℝ) (d : Fin n → ℝ) (hk : k ≤ n)
    {θ : ℝ} (hL : 0 ≤ L) (hθ : 0 < θ)
    (hbelow : θ < RLCD.regularizedLCDCard L k d) :
    ∃ I : Finset (Fin n), I.card = k ∧
      ‖Fourier.finCharFun (I → Bool)
          (fun ξ ↦ ∑ i : I,
            RLCD.normalizedRestrict d I i * Fourier.rademacherSign (ξ i))
          (Real.pi * θ)‖ ≤
        Real.exp (-(L * Real.sqrt (RLCD.logPlus (θ / L))) ^ 2) := by
  obtain ⟨I, hIcard, hdist⟩ :=
    exists_coordinateSet_latticeDist_ge_of_lt_regularizedLCDCard
      L d hk hθ hbelow
  refine ⟨I, hIcard, ?_⟩
  have hchar := norm_rademacherLinear_le_exp_neg_latticeDist_sq
    (RLCD.normalizedRestrict d I) (Real.pi * θ)
  have hpi : Real.pi ≠ 0 := ne_of_gt Real.pi_pos
  have hvec : (fun i : I ↦
      (Real.pi * θ) * RLCD.normalizedRestrict d I i / Real.pi) =
      (fun i : I ↦ θ * RLCD.normalizedRestrict d I i) := by
    funext i
    field_simp
  rw [hvec] at hchar
  apply hchar.trans
  apply Real.exp_le_exp.mpr
  apply neg_le_neg
  exact (sq_le_sq₀ (mul_nonneg hL (Real.sqrt_nonneg _))
    (RLCD.latticeDist_nonneg _)).2 hdist

/-- The logarithmic LCD envelope is exactly a negative real power once the
scale is at least `L`. -/
lemma exp_neg_logThreshold_sq {L θ : ℝ} (hL : 0 < L) (hLθ : L ≤ θ) :
    Real.exp (-(L * Real.sqrt (RLCD.logPlus (θ / L))) ^ 2) =
      (θ / L) ^ (-(L ^ 2 : ℝ)) := by
  have hqpos : 0 < θ / L := div_pos (hL.trans_le hLθ) hL
  have hqone : 1 ≤ θ / L := (le_div_iff₀ hL).2 (by simpa using hLθ)
  have hlog : 0 ≤ Real.log (θ / L) := Real.log_nonneg hqone
  rw [RLCD.logPlus_eq_log hqone, mul_pow, Real.sq_sqrt hlog,
    Real.rpow_def_of_pos hqpos]
  congr 1
  ring

/-- Power form of the preceding regularized-LCD characteristic decay. -/
theorem exists_coordinateSet_rademacher_decay_rpow
    {n k : ℕ} (L : ℝ) (d : Fin n → ℝ) (hk : k ≤ n)
    {θ : ℝ} (hL : 0 < L) (hLθ : L ≤ θ)
    (hbelow : θ < RLCD.regularizedLCDCard L k d) :
    ∃ I : Finset (Fin n), I.card = k ∧
      ‖Fourier.finCharFun (I → Bool)
          (fun ξ ↦ ∑ i : I,
            RLCD.normalizedRestrict d I i * Fourier.rademacherSign (ξ i))
          (Real.pi * θ)‖ ≤
        (θ / L) ^ (-(L ^ 2 : ℝ)) := by
  obtain ⟨I, hI, hdecay⟩ :=
    exists_coordinateSet_rademacher_decay_of_lt_regularizedLCDCard
      L d hk hL.le (hL.trans_le hLθ) hbelow
  refine ⟨I, hI, ?_⟩
  rwa [exp_neg_logThreshold_sq hL hLθ] at hdecay

/-- A polynomial lower bound on the LCD scale converts its negative-power
envelope into an arbitrary prescribed polynomial decay. -/
lemma rpow_decay_le {n : ℕ} {β L A q : ℝ}
    (hn : 1 ≤ n) (hbase : BooleanSlices.scale n β ≤ q)
    (hbudget : A ≤ β * L ^ 2) :
    q ^ (-(L ^ 2 : ℝ)) ≤ BooleanSlices.scale n (-A) := by
  have hnpos : (0 : ℝ) < n := by positivity
  have hnβpos : 0 < BooleanSlices.scale n β :=
    BooleanSlices.scale_pos (lt_of_lt_of_le Nat.zero_lt_one hn) β
  have hqpos : 0 < q := hnβpos.trans_le hbase
  calc
    q ^ (-(L ^ 2 : ℝ)) ≤
        (BooleanSlices.scale n β) ^ (-(L ^ 2 : ℝ)) :=
      Real.rpow_le_rpow_of_nonpos hnβpos hbase (neg_nonpos.mpr (sq_nonneg L))
    _ = BooleanSlices.scale n (β * (-(L ^ 2 : ℝ))) := by
      unfold BooleanSlices.scale
      exact (Real.rpow_mul hnpos.le β (-(L ^ 2 : ℝ))).symm
    _ ≤ BooleanSlices.scale n (-A) := by
      apply BooleanSlices.scale_mono_exponent hn
      nlinarith

/-- Polynomial-decay form of the regularized-LCD restriction estimate. -/
theorem exists_coordinateSet_rademacher_decay_scale
    {n k : ℕ} (L : ℝ) (d : Fin n → ℝ) (hk : k ≤ n)
    {θ β A : ℝ} (hn : 1 ≤ n) (hβ : 0 ≤ β) (hL : 0 < L)
    (hscale : BooleanSlices.scale n β ≤ θ / L)
    (hbudget : A ≤ β * L ^ 2)
    (hbelow : θ < RLCD.regularizedLCDCard L k d) :
    ∃ I : Finset (Fin n), I.card = k ∧
      ‖Fourier.finCharFun (I → Bool)
          (fun ξ ↦ ∑ i : I,
            RLCD.normalizedRestrict d I i * Fourier.rademacherSign (ξ i))
          (Real.pi * θ)‖ ≤ BooleanSlices.scale n (-A) := by
  have hnone : 1 ≤ BooleanSlices.scale n β := by
    exact Real.one_le_rpow (by exact_mod_cast hn) hβ
  have hLθ : L ≤ θ := by
    simpa using (le_div_iff₀ hL).mp (hnone.trans hscale)
  obtain ⟨I, hI, hdecay⟩ :=
    exists_coordinateSet_rademacher_decay_rpow L d hk hL hLθ hbelow
  refine ⟨I, hI, hdecay.trans ?_⟩
  exact rpow_decay_le hn hscale hbudget

/-- Triangle inequality for the explicit finite-dimensional Euclidean norm
used in the regularized-LCD definitions. -/
lemma euclidNorm_add_le {I : Type*} [Fintype I]
    (x y : I → ℝ) :
    RLCD.euclidNorm (fun i ↦ x i + y i) ≤
      RLCD.euclidNorm x + RLCD.euclidNorm y := by
  let X := ∑ i, x i ^ 2
  let Y := ∑ i, y i ^ 2
  have hX : 0 ≤ X := Finset.sum_nonneg fun _ _ ↦ sq_nonneg _
  have hY : 0 ≤ Y := Finset.sum_nonneg fun _ _ ↦ sq_nonneg _
  have hcross : (∑ i, x i * y i) ≤ Real.sqrt X * Real.sqrt Y := by
    simpa only [Finset.sum_filter, Finset.filter_true_of_mem,
      Finset.sum_const_zero, add_zero] using
      (Real.sum_mul_le_sqrt_mul_sqrt (Finset.univ : Finset I) x y)
  rw [RLCD.euclidNorm, RLCD.euclidNorm, RLCD.euclidNorm]
  apply (Real.sqrt_le_iff).2
  constructor
  · positivity
  · dsimp only [X, Y] at hcross ⊢
    have hxSq : Real.sqrt (∑ i, x i ^ 2) ^ 2 = ∑ i, x i ^ 2 :=
      Real.sq_sqrt hX
    have hySq : Real.sqrt (∑ i, y i ^ 2) ^ 2 = ∑ i, y i ^ 2 :=
      Real.sq_sqrt hY
    calc
      (∑ i, (x i + y i) ^ 2) =
          (∑ i, x i ^ 2) + 2 * (∑ i, x i * y i) +
            ∑ i, y i ^ 2 := by
        simp_rw [add_sq,
          show ∀ i, 2 * x i * y i = 2 * (x i * y i) by intro; ring]
        rw [Finset.sum_add_distrib, Finset.sum_add_distrib,
          ← Finset.mul_sum]
      _ ≤ (∑ i, x i ^ 2) +
          2 * (Real.sqrt (∑ i, x i ^ 2) *
            Real.sqrt (∑ i, y i ^ 2)) + ∑ i, y i ^ 2 := by
        gcongr
      _ = (Real.sqrt (∑ i, x i ^ 2) +
          Real.sqrt (∑ i, y i ^ 2)) ^ 2 := by
        nlinarith

/-- Perturbing a vector can reduce its distance from the integer lattice by
at most the Euclidean norm of the perturbation. -/
lemma latticeDist_add_lower {I : Type*} [Fintype I]
    (x y : I → ℝ) :
    RLCD.latticeDist x - RLCD.euclidNorm y ≤
      RLCD.latticeDist (fun i ↦ x i + y i) := by
  obtain ⟨z, hz⟩ :=
    RLCD.exists_integerVector_eq_latticeDist (fun i ↦ x i + y i)
  have hx := RLCD.latticeDist_le_integerVector x z
  have htri := euclidNorm_add_le
    (fun i ↦ (x i + y i) - RLCD.integerVectorCast z i)
    (fun i ↦ -y i)
  have hneg : RLCD.euclidNorm (fun i ↦ -y i) = RLCD.euclidNorm y := by
    simp [RLCD.euclidNorm]
  have hpoint : (fun i ↦ x i - RLCD.integerVectorCast z i) =
      (fun i ↦ ((x i + y i) - RLCD.integerVectorCast z i) + -y i) := by
    funext i
    ring
  rw [hpoint] at hx
  rw [hneg, ← hz] at htri
  linarith

/-- Every centered Rademacher linear form has zero unnormalized sum. -/
lemma sum_rademacherLinear_eq_zero {n : ℕ} (a : Fin n → ℝ) :
    (∑ x : Fin n → Bool,
      ∑ i, a i * Fourier.rademacherSign (x i)) = 0 := by
  classical
  rw [Finset.sum_comm]
  apply Finset.sum_eq_zero
  intro i hi
  rw [← Finset.mul_sum]
  have hsum :
      (∑ x : Fin n → Bool, Fourier.rademacherSign (x i)) = 0 := by
    let flip : (Fin n → Bool) ≃ (Fin n → Bool) :=
      Equiv.piCongrRight (fun j ↦
        if h : j = i then Equiv.boolNot else Equiv.refl Bool)
    have hneg (x : Fin n → Bool) :
        Fourier.rademacherSign (flip x i) =
          -Fourier.rademacherSign (x i) := by
      cases hxi : x i <;>
        simp [flip, hxi, Fourier.rademacherSign]
    have heq := flip.sum_comp (fun x ↦ Fourier.rademacherSign (x i))
    simp_rw [hneg] at heq
    rw [Finset.sum_neg_distrib] at heq
    linarith
  rw [hsum, mul_zero]

/-- A two-sided Hoeffding bound for a Rademacher linear form, in the exact
counting normalization needed for conditioning on the outside signs. -/
theorem card_rademacherLinear_abs_ge_le {n : ℕ}
    (a : Fin n → ℝ) (u : ℝ) (hu : 0 ≤ u) :
    ((Finset.univ.filter fun x : Fin n → Bool ↦
        u ≤ |∑ i, a i * Fourier.rademacherSign (x i)|).card : ℝ) ≤
      2 * (2 : ℝ) ^ n *
        Real.exp (-u ^ 2 / (2 * ∑ i, a i ^ 2)) := by
  classical
  let f : (Fin n → Bool) → ℝ := fun x ↦
    ∑ i, a i * Fourier.rademacherSign (x i)
  let b : Fin n → ℝ := fun i ↦ 2 * |a i|
  have hbd : ∀ i x y, (∀ j, j ≠ i → x j = y j) →
      |f x - f y| ≤ b i := by
    intro i x y hxy
    have hsum : f x - f y =
        a i * (Fourier.rademacherSign (x i) -
          Fourier.rademacherSign (y i)) := by
      dsimp only [f]
      rw [← Finset.sum_sub_distrib]
      calc
        (∑ j, (a j * Fourier.rademacherSign (x j) -
          a j * Fourier.rademacherSign (y j))) =
            ∑ j, if j = i then
              a i * (Fourier.rademacherSign (x i) -
                Fourier.rademacherSign (y i)) else 0 := by
          apply Finset.sum_congr rfl
          intro j hj
          by_cases hji : j = i
          · subst j
            simp
            ring
          · simp only [hji, if_false]
            rw [hxy j hji]
            ring
        _ = a i * (Fourier.rademacherSign (x i) -
              Fourier.rademacherSign (y i)) := by simp
    rw [hsum]
    dsimp only [b]
    rw [abs_mul]
    have hsign : |Fourier.rademacherSign (x i) -
        Fourier.rademacherSign (y i)| ≤ 2 := by
      cases x i <;> cases y i <;> norm_num
    nlinarith [abs_nonneg (a i)]
  have hb : ∀ i, 0 ≤ b i := fun i ↦ by dsimp [b]; positivity
  have hmean : (∑ x : Fin n → Bool, f x) / (2 : ℝ) ^ n = 0 := by
    rw [show (∑ x : Fin n → Bool, f x) = 0 by
      simpa only [f] using sum_rademacherLinear_eq_zero a]
    simp
  have hlower := Concentration.cube_lower_tail n f b hbd hb u hu
  have hupper := Concentration.cube_lower_tail n (fun x ↦ -f x) b
    (by
      intro i x y hxy
      simpa only [neg_sub_neg, abs_sub_comm] using hbd i x y hxy)
    hb u hu
  rw [hmean] at hlower
  have hmeanNeg :
      (∑ x : Fin n → Bool, -f x) / (2 : ℝ) ^ n = 0 := by
    rw [Finset.sum_neg_distrib,
      show (∑ x : Fin n → Bool, f x) = 0 by
        simpa only [f] using sum_rademacherLinear_eq_zero a]
    simp
  rw [hmeanNeg] at hupper
  have hbSq : (∑ i, b i ^ 2) = 4 * ∑ i, a i ^ 2 := by
    dsimp only [b]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    rw [mul_pow, sq_abs]
    ring
  rw [hbSq] at hlower hupper
  have hnorm : -2 * u ^ 2 / (4 * ∑ i, a i ^ 2) =
      -u ^ 2 / (2 * ∑ i, a i ^ 2) := by ring
  rw [hnorm] at hlower hupper
  let A := Finset.univ.filter fun x : Fin n → Bool ↦ f x ≤ -u
  let B := Finset.univ.filter fun x : Fin n → Bool ↦ -f x ≤ -u
  have hsub :
      (Finset.univ.filter fun x : Fin n → Bool ↦ u ≤ |f x|) ⊆
        A ∪ B := by
    intro x hx
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
    dsimp only [A, B]
    rw [Finset.mem_union]
    rw [le_abs] at hx
    rcases hx with hx | hx
    · exact Or.inr (by
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        linarith)
    · exact Or.inl (by
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        linarith)
  have hcard := Finset.card_le_card hsub
  have hunion := Finset.card_union_le A B
  have hA : (A.card : ℝ) ≤ (2 : ℝ) ^ n *
      Real.exp (-u ^ 2 / (2 * ∑ i, a i ^ 2)) := by
    simpa only [A, zero_sub] using hlower
  have hB : (B.card : ℝ) ≤ (2 : ℝ) ^ n *
      Real.exp (-u ^ 2 / (2 * ∑ i, a i ^ 2)) := by
    simpa only [B, zero_sub] using hupper
  change ((Finset.univ.filter fun x : Fin n → Bool ↦
    u ≤ |f x|).card : ℝ) ≤ _
  calc
    ((Finset.univ.filter fun x : Fin n → Bool ↦ u ≤ |f x|).card : ℝ) ≤
        ((A ∪ B).card : ℝ) := by exact_mod_cast hcard
    _ ≤ (A.card : ℝ) + B.card := by exact_mod_cast hunion
    _ ≤ ((2 : ℝ) ^ n * Real.exp (-u ^ 2 / (2 * ∑ i, a i ^ 2))) +
        ((2 : ℝ) ^ n * Real.exp (-u ^ 2 / (2 * ∑ i, a i ^ 2))) :=
      add_le_add hA hB
    _ = 2 * (2 : ℝ) ^ n *
        Real.exp (-u ^ 2 / (2 * ∑ i, a i ^ 2)) := by ring

/-- The two-sided Rademacher linear tail bound on an arbitrary finite
coordinate type. -/
theorem card_rademacherLinear_abs_ge_le_fintype
    {I : Type*} [Fintype I] [DecidableEq I]
    (a : I → ℝ) (u : ℝ) (hu : 0 ≤ u) :
    ((Finset.univ.filter fun x : I → Bool ↦
        u ≤ |∑ i, a i * Fourier.rademacherSign (x i)|).card : ℝ) ≤
      2 * (Fintype.card (I → Bool) : ℝ) *
        Real.exp (-u ^ 2 / (2 * ∑ i, a i ^ 2)) := by
  classical
  let e : I ≃ Fin (Fintype.card I) := Fintype.equivFin I
  let se : (I → Bool) ≃ (Fin (Fintype.card I) → Bool) :=
    Equiv.piCongrLeft (fun _ ↦ Bool) e
  let a' : Fin (Fintype.card I) → ℝ := fun j ↦ a (e.symm j)
  let P : (I → Bool) → Prop := fun x ↦
    u ≤ |∑ i, a i * Fourier.rademacherSign (x i)|
  let Q : (Fin (Fintype.card I) → Bool) → Prop := fun x ↦
    u ≤ |∑ j, a' j * Fourier.rademacherSign (x j)|
  have hpq (x : I → Bool) : P x ↔ Q (se x) := by
    dsimp only [P, Q]
    have hsum : (∑ j, a' j * Fourier.rademacherSign (se x j)) =
        ∑ i, a i * Fourier.rademacherSign (x i) := by
      rw [← e.sum_comp]
      apply Finset.sum_congr rfl
      intro i hi
      simp [a', se, e]
    rw [hsum]
  let ee : {x // P x} ≃ {x // Q x} := se.subtypeEquiv hpq
  have hcard : (Finset.univ.filter P).card =
      (Finset.univ.filter Q).card := by
    rw [← Fintype.card_subtype P, ← Fintype.card_subtype Q]
    exact Fintype.card_congr ee
  have hsq : (∑ j, a' j ^ 2) = ∑ i, a i ^ 2 := by
    rw [← e.sum_comp]
    apply Finset.sum_congr rfl
    intro i hi
    simp [a']
  have h := card_rademacherLinear_abs_ge_le a' u hu
  have hpow : (2 : ℝ) ^ Fintype.card I =
      (Fintype.card (I → Bool) : ℝ) := by
    simp only [Fintype.card_fun, Fintype.card_bool, Nat.cast_pow,
      Nat.cast_ofNat]
  change ((Finset.univ.filter P).card : ℝ) ≤ _
  rw [hcard]
  simpa only [Q, hsq, hpow] using h

/-- Coefficient contributed to an inside vertex by one fixed outside sign
after conditioning the graph quadratic. -/
noncomputable def graphCrossCoefficient {n : ℕ}
    (G : SimpleGraph (Fin n)) (I : Finset (Fin n))
    (i : I) (j : {v : Fin n // v ∉ I}) : ℝ :=
  (1 / 4 : ℝ) * RobustRank.graphAdjacencyMatrix G i.1 j.1

/-- The random cross-term linear coefficient at an inside vertex. -/
noncomputable def graphCrossLinear {n : ℕ}
    (G : SimpleGraph (Fin n)) (I : Finset (Fin n))
    (i : I) (z : {v : Fin n // v ∉ I} → Bool) : ℝ :=
  ∑ j, graphCrossCoefficient G I i j * Fourier.rademacherSign (z j)

/-- Every cross coefficient has variance proxy at most `n / 16`. -/
lemma graphCrossCoefficient_sq_sum_le {n : ℕ}
    (G : SimpleGraph (Fin n)) (I : Finset (Fin n)) (i : I) :
    (∑ j : {v : Fin n // v ∉ I},
      graphCrossCoefficient G I i j ^ 2) ≤ (n : ℝ) / 16 := by
  classical
  have hcard : Fintype.card {v : Fin n // v ∉ I} ≤ n := by
    calc
      Fintype.card {v : Fin n // v ∉ I} ≤ Fintype.card (Fin n) :=
        Fintype.card_le_of_injective Subtype.val Subtype.val_injective
      _ = n := Fintype.card_fin n
  calc
    (∑ j : {v : Fin n // v ∉ I},
      graphCrossCoefficient G I i j ^ 2) ≤
        ∑ _j : {v : Fin n // v ∉ I}, (1 / 16 : ℝ) := by
      apply Finset.sum_le_sum
      intro j hj
      by_cases hij : G.Adj i.1 j.1 <;>
        simp [graphCrossCoefficient,
          RobustRank.graphAdjacencyMatrix, hij] <;> norm_num
    _ = (Fintype.card {v : Fin n // v ∉ I} : ℝ) / 16 := by
      simp
      ring
    _ ≤ (n : ℝ) / 16 := by
      apply div_le_div_of_nonneg_right (by exact_mod_cast hcard)
      norm_num

/-- Exact two-sided Hoeffding tail for one conditioned graph cross
coefficient. -/
theorem graphCrossLinear_tail {n : ℕ}
    (G : SimpleGraph (Fin n)) (I : Finset (Fin n)) (i : I)
    (u : ℝ) (hu : 0 ≤ u) :
    ((Finset.univ.filter fun z : {v : Fin n // v ∉ I} → Bool ↦
      u ≤ |graphCrossLinear G I i z|).card : ℝ) ≤
      2 * (Fintype.card ({v : Fin n // v ∉ I} → Bool) : ℝ) *
        Real.exp (-u ^ 2 /
          (2 * ∑ j : {v : Fin n // v ∉ I},
            graphCrossCoefficient G I i j ^ 2)) := by
  unfold graphCrossLinear
  exact card_rademacherLinear_abs_ge_le_fintype
    (graphCrossCoefficient G I i) u hu

/-- Uniform form of the conditioned cross-term tail.  The graph coefficients
have total squared mass at most `n / 16`, so Hoeffding gives the exponent
`-8 * u^2 / n`.  The zero-mass case is handled exactly. -/
theorem graphCrossLinear_tail_uniform {n : ℕ}
    (G : SimpleGraph (Fin n)) (I : Finset (Fin n)) (i : I)
    (u : ℝ) (hn : 0 < n) (hu : 0 < u) :
    ((Finset.univ.filter fun z : {v : Fin n // v ∉ I} → Bool ↦
      u ≤ |graphCrossLinear G I i z|).card : ℝ) ≤
      2 * (Fintype.card ({v : Fin n // v ∉ I} → Bool) : ℝ) *
        Real.exp (-8 * u ^ 2 / n) := by
  let S := ∑ j : {v : Fin n // v ∉ I},
    graphCrossCoefficient G I i j ^ 2
  have hS : 0 ≤ S := Finset.sum_nonneg fun _ _ ↦ sq_nonneg _
  have hSn : S ≤ (n : ℝ) / 16 := graphCrossCoefficient_sq_sum_le G I i
  by_cases hS0 : S = 0
  · have hcoeff : ∀ j : {v : Fin n // v ∉ I},
        graphCrossCoefficient G I i j = 0 := by
      intro j
      have hsq : graphCrossCoefficient G I i j ^ 2 = 0 :=
        (Finset.sum_eq_zero_iff_of_nonneg
          (fun j _ ↦ sq_nonneg (graphCrossCoefficient G I i j))).mp hS0
            j (Finset.mem_univ j)
      nlinarith [sq_nonneg (graphCrossCoefficient G I i j)]
    have hlinear : ∀ z, graphCrossLinear G I i z = 0 := by
      intro z
      simp [graphCrossLinear, hcoeff]
    have hempty :
        (Finset.univ.filter fun z : {v : Fin n // v ∉ I} → Bool ↦
          u ≤ |graphCrossLinear G I i z|) = ∅ := by
      ext z
      simp [hlinear, not_le_of_gt hu]
    rw [hempty]
    simp only [Finset.card_empty, Nat.cast_zero]
    positivity
  · have hSpos : 0 < S := lt_of_le_of_ne hS (Ne.symm hS0)
    have hnR : (0 : ℝ) < n := by exact_mod_cast hn
    have hratio : 8 * u ^ 2 / (n : ℝ) ≤ u ^ 2 / (2 * S) := by
      apply (div_le_div_iff₀ hnR (mul_pos (by norm_num) hSpos)).2
      have h16 : 16 * S ≤ (n : ℝ) := by linarith
      nlinarith [sq_nonneg u]
    have hexp : Real.exp (-u ^ 2 / (2 * S)) ≤
        Real.exp (-8 * u ^ 2 / n) := by
      apply Real.exp_le_exp.mpr
      rw [show -u ^ 2 / (2 * S) = -(u ^ 2 / (2 * S)) by ring,
        show -8 * u ^ 2 / (n : ℝ) = -(8 * u ^ 2 / (n : ℝ)) by ring]
      exact neg_le_neg hratio
    have htail := graphCrossLinear_tail G I i u hu.le
    exact htail.trans (mul_le_mul_of_nonneg_left hexp (by positivity))

/-- Union bound for the exceptional outside assignments on which at least
one conditioned cross coefficient is large. -/
theorem graphCrossLinear_exists_tail {n : ℕ}
    (G : SimpleGraph (Fin n)) (I : Finset (Fin n))
    (u : ℝ) (hu : 0 ≤ u) :
    ((Finset.univ.filter fun z : {v : Fin n // v ∉ I} → Bool ↦
      ∃ i : I, u ≤ |graphCrossLinear G I i z|).card : ℝ) ≤
      ∑ i : I, 2 *
        (Fintype.card ({v : Fin n // v ∉ I} → Bool) : ℝ) *
          Real.exp (-u ^ 2 /
            (2 * ∑ j : {v : Fin n // v ∉ I},
              graphCrossCoefficient G I i j ^ 2)) := by
  classical
  let bad : I → Finset ({v : Fin n // v ∉ I} → Bool) := fun i ↦
    Finset.univ.filter fun z ↦ u ≤ |graphCrossLinear G I i z|
  have hset :
      (Finset.univ.filter fun z : {v : Fin n // v ∉ I} → Bool ↦
        ∃ i : I, u ≤ |graphCrossLinear G I i z|) =
        (Finset.univ : Finset I).biUnion bad := by
    ext z
    simp [bad]
  rw [hset]
  calc
    (((Finset.univ : Finset I).biUnion bad).card : ℝ) ≤
        ∑ i : I, ((bad i).card : ℝ) := by
      exact_mod_cast Finset.card_biUnion_le
    _ ≤ ∑ i : I, 2 *
        (Fintype.card ({v : Fin n // v ∉ I} → Bool) : ℝ) *
          Real.exp (-u ^ 2 /
            (2 * ∑ j : {v : Fin n // v ∉ I},
              graphCrossCoefficient G I i j ^ 2)) := by
      apply Finset.sum_le_sum
      intro i hi
      exact graphCrossLinear_tail G I i u hu

/-- Uniform union bound for all conditioned cross coefficients.  This is the
exceptional-set estimate used in the proof of KSSS Lemma 7.2. -/
theorem graphCrossLinear_exists_tail_uniform {n : ℕ}
    (G : SimpleGraph (Fin n)) (I : Finset (Fin n))
    (u : ℝ) (hn : 0 < n) (hu : 0 < u) :
    ((Finset.univ.filter fun z : {v : Fin n // v ∉ I} → Bool ↦
      ∃ i : I, u ≤ |graphCrossLinear G I i z|).card : ℝ) ≤
      2 * (I.card : ℝ) *
        (Fintype.card ({v : Fin n // v ∉ I} → Bool) : ℝ) *
          Real.exp (-8 * u ^ 2 / n) := by
  classical
  let bad : I → Finset ({v : Fin n // v ∉ I} → Bool) := fun i ↦
    Finset.univ.filter fun z ↦ u ≤ |graphCrossLinear G I i z|
  have hset :
      (Finset.univ.filter fun z : {v : Fin n // v ∉ I} → Bool ↦
        ∃ i : I, u ≤ |graphCrossLinear G I i z|) =
        (Finset.univ : Finset I).biUnion bad := by
    ext z
    simp [bad]
  rw [hset]
  calc
    (((Finset.univ : Finset I).biUnion bad).card : ℝ) ≤
        ∑ i : I, ((bad i).card : ℝ) := by
      exact_mod_cast Finset.card_biUnion_le
    _ ≤ ∑ _i : I, 2 *
        (Fintype.card ({v : Fin n // v ∉ I} → Bool) : ℝ) *
          Real.exp (-8 * u ^ 2 / n) := by
      apply Finset.sum_le_sum
      intro i hi
      exact graphCrossLinear_tail_uniform G I i u hn hu
    _ = 2 * (I.card : ℝ) *
        (Fintype.card ({v : Fin n // v ∉ I} → Bool) : ℝ) *
          Real.exp (-8 * u ^ 2 / n) := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_coe,
        nsmul_eq_mul]
      ring

open GraphQuadratic

lemma sum_subtype_add_compl {n : ℕ} (I : Finset (Fin n))
    (f : Fin n → ℝ) :
    (∑ i, f i) = (∑ i : I, f i.1) +
      ∑ j : {v : Fin n // v ∉ I}, f j.1 := by
  let e : I ⊕ {v : Fin n // v ∉ I} ≃ Fin n :=
    Equiv.sumCompl (fun i ↦ i ∈ I)
  calc
    (∑ i, f i) = ∑ w : I ⊕ {v : Fin n // v ∉ I}, f (e w) :=
      (e.sum_comp f).symm
    _ = (∑ i : I, f i.1) +
        ∑ j : {v : Fin n // v ∉ I}, f j.1 := by
      rw [Fintype.sum_sum_type]
      rfl

/-- Splitting a Boolean assignment into its coordinates on a finite set and
its complement. -/
def extendBoolEquiv {n : ℕ} (I : Finset (Fin n)) :
    ((I → Bool) × ({v : Fin n // v ∉ I} → Bool)) ≃ (Fin n → Bool) :=
  { toFun := fun p ↦ Fourier.extendBool I p.1 p.2
    invFun := fun x ↦ (fun i ↦ x i.1, fun j ↦ x j.1)
    left_inv := by
      intro p
      apply Prod.ext
      · funext i
        simp
      · funext j
        simp
    right_inv := by
      intro x
      funext i
      by_cases hi : i ∈ I <;> simp [Fourier.extendBool, hi] }

@[simp] lemma extendBoolEquiv_apply {n : ℕ} (I : Finset (Fin n))
    (y : I → Bool) (z : {v : Fin n // v ∉ I} → Bool) :
    extendBoolEquiv I (y, z) = Fourier.extendBool I y z := by
  rfl

/-- Fubini identity for uniform finite expectation after splitting Boolean
coordinates into a finite set and its complement. -/
theorem finExpectation_extendBool {n : ℕ} (I : Finset (Fin n))
    (f : (Fin n → Bool) → ℂ) :
    Fourier.finExpectation (Fin n → Bool) f =
      Fourier.finExpectation ({v : Fin n // v ∉ I} → Bool) (fun z ↦
        Fourier.finExpectation (I → Bool) (fun y ↦
          f (Fourier.extendBool I y z))) := by
  let e := extendBoolEquiv I
  have hsum : (∑ x : Fin n → Bool, f x) =
      ∑ z : {v : Fin n // v ∉ I} → Bool,
        ∑ y : I → Bool, f (Fourier.extendBool I y z) := by
    calc
      (∑ x : Fin n → Bool, f x) =
          ∑ p : (I → Bool) × ({v : Fin n // v ∉ I} → Bool), f (e p) :=
        (e.sum_comp f).symm
      _ = ∑ y : I → Bool,
          ∑ z : {v : Fin n // v ∉ I} → Bool,
            f (Fourier.extendBool I y z) := by
        rw [Fintype.sum_prod_type]
        apply Finset.sum_congr rfl
        intro y hy
        apply Finset.sum_congr rfl
        intro z hz
        rw [extendBoolEquiv_apply]
      _ = ∑ z : {v : Fin n // v ∉ I} → Bool,
          ∑ y : I → Bool, f (Fourier.extendBool I y z) :=
        Finset.sum_comm
  have hcard : Fintype.card (Fin n → Bool) =
      Fintype.card (I → Bool) *
        Fintype.card ({v : Fin n // v ∉ I} → Bool) := by
    rw [← Fintype.card_prod]
    exact Fintype.card_congr e.symm
  unfold Fourier.finExpectation
  rw [hsum, hcard, Nat.cast_mul, Finset.sum_div, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro z hz
  rw [div_div]

/-- The part of the graph Rademacher quadratic that is constant after the
outside signs are fixed. -/
noncomputable def graphConditionedOutside
    {n : ℕ} (G : SimpleGraph (Fin n)) (e₀ : ℝ) (c : Fin n → ℝ)
    (I : Finset (Fin n)) (z : {v : Fin n // v ∉ I} → Bool) : ℝ :=
  graphSliceConstant G e₀ c +
    (∑ j : {v : Fin n // v ∉ I},
      graphSliceLinear G c j.1 * Fourier.rademacherSign (z j)) +
    ∑ j : {v : Fin n // v ∉ I},
      ∑ k : {v : Fin n // v ∉ I},
        graphSliceMatrix G j.1 k.1 * Fourier.rademacherSign (z j) *
          Fourier.rademacherSign (z k)

/-- The inside linear coefficient after fixing all outside signs. -/
noncomputable def graphConditionedInsideLinear
    {n : ℕ} (G : SimpleGraph (Fin n)) (c : Fin n → ℝ)
    (I : Finset (Fin n)) (z : {v : Fin n // v ∉ I} → Bool)
    (i : I) : ℝ :=
  graphSliceLinear G c i.1 + graphCrossLinear G I i z

/-- Exact decomposition of the graph quadratic after conditioning on the
outside signs. -/
theorem rademacherQuadratic_extendBool_eq_conditioned
    {n : ℕ} (G : SimpleGraph (Fin n)) (e₀ : ℝ) (c : Fin n → ℝ)
    (I : Finset (Fin n)) (y : I → Bool)
    (z : {v : Fin n // v ∉ I} → Bool) :
    BooleanSlices.rademacherQuadratic
        (graphSliceConstant G e₀ c) (graphSliceLinear G c)
        (graphSliceMatrix G) (Fourier.extendBool I y z) =
      graphConditionedOutside G e₀ c I z +
        (∑ i : I, graphConditionedInsideLinear G c I z i *
          Fourier.rademacherSign (y i)) +
        ∑ i : I, ∑ j : I,
          graphSliceMatrix G i.1 j.1 * Fourier.rademacherSign (y i) *
            Fourier.rademacherSign (y j) := by
  let s : Fin n → ℝ := fun i ↦
    Fourier.rademacherSign (Fourier.extendBool I y z i)
  have hsIn (i : I) : s i.1 = Fourier.rademacherSign (y i) := by
    simp [s]
  have hsOut (j : {v : Fin n // v ∉ I}) :
      s j.1 = Fourier.rademacherSign (z j) := by
    simp [s]
  have hlin := sum_subtype_add_compl I
    (fun i ↦ graphSliceLinear G c i * s i)
  have hquadOuter := sum_subtype_add_compl I
    (fun i ↦ ∑ j, s i * graphSliceMatrix G i j * s j)
  have hquadIn (i : I) := sum_subtype_add_compl I
    (fun j ↦ s i.1 * graphSliceMatrix G i.1 j * s j)
  have hquadOut (i : {v : Fin n // v ∉ I}) :=
    sum_subtype_add_compl I
      (fun j ↦ s i.1 * graphSliceMatrix G i.1 j * s j)
  simp_rw [hquadIn] at hquadOuter
  simp_rw [hquadOut] at hquadOuter
  rw [show BooleanSlices.rademacherQuadratic
      (graphSliceConstant G e₀ c) (graphSliceLinear G c)
      (graphSliceMatrix G) (Fourier.extendBool I y z) =
      graphSliceConstant G e₀ c +
        (∑ i, graphSliceLinear G c i * s i) +
        ∑ i, ∑ j, s i * graphSliceMatrix G i j * s j by
    simp only [BooleanSlices.rademacherQuadratic,
      BooleanSlices.quadraticPolynomial, BooleanSlices.linearPart,
      BooleanSlices.quadraticPart, s]
    rfl]
  rw [hlin, hquadOuter]
  simp_rw [hsIn, hsOut]
  unfold graphConditionedOutside graphConditionedInsideLinear graphCrossLinear
  have hcrossSwap :
      (∑ j : {v : Fin n // v ∉ I}, ∑ i : I,
        Fourier.rademacherSign (z j) * graphSliceMatrix G j.1 i.1 *
          Fourier.rademacherSign (y i)) =
      ∑ i : I, ∑ j : {v : Fin n // v ∉ I},
        Fourier.rademacherSign (y i) * graphSliceMatrix G i.1 j.1 *
          Fourier.rademacherSign (z j) := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    rw [graphSliceMatrix_symmetric G j.1 i.1]
    ring
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
  rw [hcrossSwap]
  have hcoeff (i : I) (j : {v : Fin n // v ∉ I}) :
      graphCrossCoefficient G I i j =
        2 * graphSliceMatrix G i.1 j.1 := by
    unfold graphCrossCoefficient graphSliceMatrix
    ring
  have hcrossTwo :
      (∑ i : I, ∑ j : {v : Fin n // v ∉ I},
        Fourier.rademacherSign (y i) * graphSliceMatrix G i.1 j.1 *
          Fourier.rademacherSign (z j)) +
      (∑ i : I, ∑ j : {v : Fin n // v ∉ I},
        Fourier.rademacherSign (y i) * graphSliceMatrix G i.1 j.1 *
          Fourier.rademacherSign (z j)) =
      ∑ i : I,
        (∑ j : {v : Fin n // v ∉ I},
          graphCrossCoefficient G I i j * Fourier.rademacherSign (z j)) *
            Fourier.rademacherSign (y i) := by
    rw [← two_mul, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    rw [Finset.mul_sum, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro j hj
    rw [hcoeff]
    ring
  simp_rw [add_mul]
  rw [Finset.sum_add_distrib]
  rw [← hcrossTwo]
  have hquadInOrder :
      (∑ i : I, ∑ j : I,
        Fourier.rademacherSign (y i) * graphSliceMatrix G i.1 j.1 *
          Fourier.rademacherSign (y j)) =
      ∑ i : I, ∑ j : I,
        graphSliceMatrix G i.1 j.1 * Fourier.rademacherSign (y i) *
          Fourier.rademacherSign (y j) := by
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    ring
  have hquadOutOrder :
      (∑ i : {v : Fin n // v ∉ I},
        ∑ j : {v : Fin n // v ∉ I},
          Fourier.rademacherSign (z i) * graphSliceMatrix G i.1 j.1 *
            Fourier.rademacherSign (z j)) =
      ∑ i : {v : Fin n // v ∉ I},
        ∑ j : {v : Fin n // v ∉ I},
          graphSliceMatrix G i.1 j.1 * Fourier.rademacherSign (z i) *
            Fourier.rademacherSign (z j) := by
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    ring
  rw [hquadInOrder, hquadOutOrder]
  ring

/-- The characteristic function over the still-random inside coordinates
after the outside signs have been fixed. -/
noncomputable def graphConditionedCharacteristic
    {n : ℕ} (G : SimpleGraph (Fin n)) (c : Fin n → ℝ)
    (I : Finset (Fin n)) (z : {v : Fin n // v ∉ I} → Bool)
    (t : ℝ) : ℂ :=
  Fourier.finExpectation (I → Bool) (fun y ↦
    Complex.exp (((t *
      ((∑ i : I, graphConditionedInsideLinear G c I z i *
          Fourier.rademacherSign (y i)) +
        ∑ i : I, ∑ j : I,
          graphSliceMatrix G i.1 j.1 * Fourier.rademacherSign (y i) *
            Fourier.rademacherSign (y j)) : ℝ) : ℂ) * Complex.I))

/-- Exact conditional-expectation identity for the graph Rademacher
characteristic function. -/
theorem graphRademacherCharacteristic_eq_conditioned
    {n : ℕ} (G : SimpleGraph (Fin n)) (e₀ : ℝ) (c : Fin n → ℝ)
    (I : Finset (Fin n)) (t : ℝ) :
    Fourier.finExpectation (Fin n → Bool) (fun x ↦
      Complex.exp (((t * BooleanSlices.rademacherQuadratic
        (graphSliceConstant G e₀ c) (graphSliceLinear G c)
        (graphSliceMatrix G) x : ℝ) : ℂ) * Complex.I)) =
      Fourier.finExpectation ({v : Fin n // v ∉ I} → Bool) (fun z ↦
        Complex.exp (((t * graphConditionedOutside G e₀ c I z : ℝ) : ℂ) *
          Complex.I) * graphConditionedCharacteristic G c I z t) := by
  rw [finExpectation_extendBool]
  apply congrArg (Fourier.finExpectation ({v : Fin n // v ∉ I} → Bool))
  funext z
  unfold graphConditionedCharacteristic
  rw [← Fourier.finExpectation_const_mul]
  apply congrArg (Fourier.finExpectation (I → Bool))
  funext y
  rw [rademacherQuadratic_extendBool_eq_conditioned]
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

/-- Conditioning reduces the full characteristic norm to the average of the
conditional inside characteristic norms; the outside phase has norm one. -/
theorem norm_graphRademacherCharacteristic_le_conditioned_average
    {n : ℕ} (G : SimpleGraph (Fin n)) (e₀ : ℝ) (c : Fin n → ℝ)
    (I : Finset (Fin n)) (t : ℝ) :
    ‖Fourier.finExpectation (Fin n → Bool) (fun x ↦
      Complex.exp (((t * BooleanSlices.rademacherQuadratic
        (graphSliceConstant G e₀ c) (graphSliceLinear G c)
        (graphSliceMatrix G) x : ℝ) : ℂ) * Complex.I))‖ ≤
      (∑ z : {v : Fin n // v ∉ I} → Bool,
        ‖graphConditionedCharacteristic G c I z t‖) /
          Fintype.card ({v : Fin n // v ∉ I} → Bool) := by
  rw [graphRademacherCharacteristic_eq_conditioned]
  refine (Fourier.norm_finExpectation_le
    ({v : Fin n // v ∉ I} → Bool) _).trans ?_
  apply div_le_div_of_nonneg_right (by
    apply Finset.sum_le_sum
    intro z hz
    rw [norm_mul, Complex.norm_exp]
    simp)
  positivity

lemma norm_graphConditionedCharacteristic_le_one
    {n : ℕ} (G : SimpleGraph (Fin n)) (c : Fin n → ℝ)
    (I : Finset (Fin n)) (z : {v : Fin n // v ∉ I} → Bool)
    (t : ℝ) : ‖graphConditionedCharacteristic G c I z t‖ ≤ 1 := by
  unfold graphConditionedCharacteristic
  calc
    ‖Fourier.finExpectation (I → Bool) (fun y ↦
      Complex.exp (((t *
        ((∑ i : I, graphConditionedInsideLinear G c I z i *
            Fourier.rademacherSign (y i)) +
          ∑ i : I, ∑ j : I,
            graphSliceMatrix G i.1 j.1 * Fourier.rademacherSign (y i) *
              Fourier.rademacherSign (y j)) : ℝ) : ℂ) * Complex.I))‖ ≤
        (∑ _y : I → Bool, (1 : ℝ)) / Fintype.card (I → Bool) := by
      refine (Fourier.norm_finExpectation_le (I → Bool) _).trans_eq ?_
      congr 1
      apply Finset.sum_congr rfl
      intro y hy
      rw [Complex.norm_exp]
      simp
    _ = 1 := by simp

/-- A conditional bound valid off the exceptional cross-term event averages
to the same bound plus the exceptional probability. -/
theorem norm_graphRademacherCharacteristic_le_of_good
    {n : ℕ} (G : SimpleGraph (Fin n)) (e₀ : ℝ) (c : Fin n → ℝ)
    (I : Finset (Fin n)) (t u B : ℝ)
    (hn : 0 < n) (hu : 0 < u) (hB : 0 ≤ B)
    (hgood : ∀ z : {v : Fin n // v ∉ I} → Bool,
      (∀ i : I, |graphCrossLinear G I i z| < u) →
        ‖graphConditionedCharacteristic G c I z t‖ ≤ B) :
    ‖Fourier.finExpectation (Fin n → Bool) (fun x ↦
      Complex.exp (((t * BooleanSlices.rademacherQuadratic
        (graphSliceConstant G e₀ c) (graphSliceLinear G c)
        (graphSliceMatrix G) x : ℝ) : ℂ) * Complex.I))‖ ≤
      B + 2 * (I.card : ℝ) * Real.exp (-8 * u ^ 2 / n) := by
  let Ω := {v : Fin n // v ∉ I} → Bool
  let bad : Ω → Prop := fun z ↦
    ∃ i : I, u ≤ |graphCrossLinear G I i z|
  have hpoint (z : Ω) : ‖graphConditionedCharacteristic G c I z t‖ ≤
      B + if bad z then 1 else 0 := by
    by_cases hz : bad z
    · rw [if_pos hz]
      have hone := norm_graphConditionedCharacteristic_le_one G c I z t
      linarith
    · rw [if_neg hz, add_zero]
      apply hgood z
      intro i
      exact lt_of_not_ge fun hi ↦ hz ⟨i, hi⟩
  have hsum : (∑ z : Ω, ‖graphConditionedCharacteristic G c I z t‖) ≤
      Fintype.card Ω * B + ((Finset.univ.filter bad).card : ℝ) := by
    calc
      (∑ z : Ω, ‖graphConditionedCharacteristic G c I z t‖) ≤
          ∑ z : Ω, (B + if bad z then 1 else 0) :=
        Finset.sum_le_sum fun z hz ↦ hpoint z
      _ = Fintype.card Ω * B + ((Finset.univ.filter bad).card : ℝ) := by
        rw [Finset.sum_add_distrib]
        simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
        have hind : (∑ z : Ω, if bad z then (1 : ℝ) else 0) =
            ((Finset.univ.filter bad).card : ℝ) := by
          rw [← Finset.sum_filter]
          simp
        rw [hind]
  have hcardPos : (0 : ℝ) < Fintype.card Ω := by positivity
  have havg := norm_graphRademacherCharacteristic_le_conditioned_average
    G e₀ c I t
  calc
    ‖Fourier.finExpectation (Fin n → Bool) (fun x ↦
      Complex.exp (((t * BooleanSlices.rademacherQuadratic
        (graphSliceConstant G e₀ c) (graphSliceLinear G c)
        (graphSliceMatrix G) x : ℝ) : ℂ) * Complex.I))‖ ≤
        (∑ z : Ω, ‖graphConditionedCharacteristic G c I z t‖) /
          Fintype.card Ω := havg
    _ ≤ (Fintype.card Ω * B + ((Finset.univ.filter bad).card : ℝ)) /
          Fintype.card Ω := div_le_div_of_nonneg_right hsum hcardPos.le
    _ = B + ((Finset.univ.filter bad).card : ℝ) / Fintype.card Ω := by
      field_simp
    _ ≤ B + 2 * (I.card : ℝ) * Real.exp (-8 * u ^ 2 / n) := by
      suffices ((Finset.univ.filter bad).card : ℝ) / Fintype.card Ω ≤
          2 * (I.card : ℝ) * Real.exp (-8 * u ^ 2 / n) by linarith
      apply (div_le_iff₀ hcardPos).2
      have htail := graphCrossLinear_exists_tail_uniform G I u hn hu
      dsimp only [bad, Ω] at htail ⊢
      nlinarith

/-- Finite-expectation form of the Taylor reduction in KSSS (7.4).  The
quadratic phase is expanded through order `K`; because both phases are
purely imaginary, the remainder has no exponential loss. -/
theorem norm_finExpectation_cexp_add_le_taylor
    {Ω : Type*} [Fintype Ω] [Nonempty Ω]
    (K : ℕ) (u v : Ω → ℝ) :
    ‖Fourier.finExpectation Ω (fun ω ↦
        Complex.exp ((((u ω + v ω : ℝ) : ℂ) * Complex.I)))‖ ≤
      ‖Fourier.finExpectation Ω (fun ω ↦
        Complex.exp (((u ω : ℝ) : ℂ) * Complex.I) *
          ∑ j ∈ Finset.range (K + 1),
            ((((v ω : ℝ) : ℂ) * Complex.I) ^ j) /
              (j.factorial : ℂ))‖ +
        (∑ ω, |v ω| ^ (K + 1) / K.factorial) / Fintype.card Ω := by
  let P : Ω → ℂ := fun ω ↦
    ∑ j ∈ Finset.range (K + 1),
      ((((v ω : ℝ) : ℂ) * Complex.I) ^ j) / (j.factorial : ℂ)
  let R : Ω → ℂ := fun ω ↦
    Complex.exp ((((u ω + v ω : ℝ) : ℂ) * Complex.I)) -
      Complex.exp (((u ω : ℝ) : ℂ) * Complex.I) * P ω
  have hsplit :
      Fourier.finExpectation Ω (fun ω ↦
          Complex.exp ((((u ω + v ω : ℝ) : ℂ) * Complex.I))) =
        Fourier.finExpectation Ω (fun ω ↦
          Complex.exp (((u ω : ℝ) : ℂ) * Complex.I) * P ω) +
          Fourier.finExpectation Ω R := by
    rw [← Fourier.finExpectation_add]
    apply congrArg (Fourier.finExpectation Ω)
    funext ω
    simp only [R]
    ring
  rw [hsplit]
  calc
    ‖Fourier.finExpectation Ω (fun ω ↦
          Complex.exp (((u ω : ℝ) : ℂ) * Complex.I) * P ω) +
        Fourier.finExpectation Ω R‖ ≤
        ‖Fourier.finExpectation Ω (fun ω ↦
          Complex.exp (((u ω : ℝ) : ℂ) * Complex.I) * P ω)‖ +
          ‖Fourier.finExpectation Ω R‖ := norm_add_le _ _
    _ ≤ ‖Fourier.finExpectation Ω (fun ω ↦
          Complex.exp (((u ω : ℝ) : ℂ) * Complex.I) * P ω)‖ +
        (∑ ω, |v ω| ^ (K + 1) / K.factorial) / Fintype.card Ω := by
      apply add_le_add_right
      refine (Fourier.norm_finExpectation_le Ω R).trans ?_
      apply div_le_div_of_nonneg_right
      · apply Finset.sum_le_sum
        intro ω hω
        have hphase :
            Complex.exp ((((u ω + v ω : ℝ) : ℂ) * Complex.I)) =
              Complex.exp (((u ω : ℝ) : ℂ) * Complex.I) *
                Complex.exp (((v ω : ℝ) : ℂ) * Complex.I) := by
          rw [← Complex.exp_add]
          congr 2
          push_cast
          ring
        have hrem := norm_cexp_sub_taylor_le K
          (((v ω : ℝ) : ℂ) * Complex.I)
        have hP : P ω =
            ∑ j ∈ Finset.range (K + 1),
              ((((v ω : ℝ) : ℂ) * Complex.I) ^ j) /
                (j.factorial : ℂ) := rfl
        simp only [R]
        rw [hphase, ← mul_sub, norm_mul, Complex.norm_exp]
        simp only [Complex.mul_re, Complex.ofReal_re, Complex.I_re,
          mul_zero, Complex.ofReal_im, Complex.I_im, mul_one, sub_self,
          Real.exp_zero, one_mul, hP]
        simpa [Real.norm_eq_abs] using hrem
      · positivity

/-- A Walsh monomial in independent Rademacher signs. -/
def rademacherWalshMonomial {I : Type*} [Fintype I]
    (S : Finset I) (ξ : I → Bool) : ℂ :=
  ∏ i ∈ S, (Fourier.rademacherSign (ξ i) : ℂ)

lemma sum_bool_exp_rademacher_mul_walshFactor (a : ℝ)
    (p : Prop) [Decidable p] :
    (∑ b : Bool,
      Complex.exp ((a * Fourier.rademacherSign b : ℝ) * Complex.I) *
        (if p then (Fourier.rademacherSign b : ℂ) else 1)) =
      if p then 2 * Complex.I * Real.sin a else 2 * Real.cos a := by
  by_cases hp : p
  · simp only [if_pos hp]
    simp [Fourier.rademacherSign, Complex.exp_ofReal_mul_I]
    ring
  · simp only [if_neg hp, mul_one]
    simpa using Fourier.sum_bool_exp_rademacher a

lemma sum_exp_rademacher_linear_mul_walshMonomial
    {I : Type*} [Fintype I] [DecidableEq I]
    (a : I → ℝ) (S : Finset I) :
    (∑ ξ : I → Bool,
      Complex.exp ((((∑ i, a i * Fourier.rademacherSign (ξ i) : ℝ)) : ℂ) *
        Complex.I) * rademacherWalshMonomial S ξ) =
      ∏ i, ∑ b : Bool,
        Complex.exp ((a i * Fourier.rademacherSign b : ℝ) * Complex.I) *
          (if i ∈ S then (Fourier.rademacherSign b : ℂ) else 1) := by
  rw [Fintype.prod_sum]
  apply Finset.sum_congr rfl
  intro ξ hξ
  have hexp :
      Complex.exp ((((∑ i, a i * Fourier.rademacherSign (ξ i) : ℝ)) : ℂ) *
        Complex.I) =
        ∏ i, Complex.exp
          ((a i * Fourier.rademacherSign (ξ i) : ℝ) * Complex.I) := by
    rw [← Complex.exp_sum Finset.univ]
    congr 1
    push_cast
    rw [Finset.sum_mul]
  have hmono : rademacherWalshMonomial S ξ =
      ∏ i, if i ∈ S then (Fourier.rademacherSign (ξ i) : ℂ) else 1 := by
    rw [rademacherWalshMonomial]
    simpa using (Finset.prod_filter (s := (Finset.univ : Finset I))
      (p := fun i ↦ i ∈ S)
      (f := fun i ↦ (Fourier.rademacherSign (ξ i) : ℂ))).symm
  rw [hexp, hmono, ← Finset.prod_mul_distrib]

lemma finExpectation_exp_rademacher_linear_mul_walshMonomial
    {I : Type*} [Fintype I] [DecidableEq I]
    (a : I → ℝ) (S : Finset I) :
    Fourier.finExpectation (I → Bool) (fun ξ ↦
      Complex.exp ((((∑ i, a i * Fourier.rademacherSign (ξ i) : ℝ)) : ℂ) *
        Complex.I) * rademacherWalshMonomial S ξ) =
      ∏ i, if i ∈ S then Complex.I * Real.sin (a i) else Real.cos (a i) := by
  rw [Fourier.finExpectation,
    sum_exp_rademacher_linear_mul_walshMonomial]
  simp_rw [sum_bool_exp_rademacher_mul_walshFactor]
  have hfactor :
      (∏ i, if i ∈ S then
          (2 : ℂ) * Complex.I * Real.sin (a i) else 2 * Real.cos (a i)) =
        (2 : ℂ) ^ Fintype.card I *
          ∏ i, if i ∈ S then Complex.I * Real.sin (a i) else Real.cos (a i) := by
    rw [← Finset.card_univ, ← Finset.prod_const, ← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro i hi
    by_cases hiS : i ∈ S <;> simp [hiS, mul_assoc]
  rw [hfactor]
  have hcard : (Fintype.card (I → Bool) : ℂ) =
      (2 : ℂ) ^ Fintype.card I := by simp
  rw [hcard]
  exact mul_div_cancel_left₀ _ (pow_ne_zero _ (by norm_num : (2 : ℂ) ≠ 0))

/-- KSSS (7.7): a Walsh monomial can consume only its own coordinates;
all remaining independent Rademacher coordinates still contribute their
cosine/lattice cancellation. -/
theorem norm_finExpectation_exp_rademacher_linear_mul_walshMonomial_le
    {I : Type*} [Fintype I] [DecidableEq I]
    (a d : I → ℝ) (S : Finset I)
    (hd : ∀ i, Fourier.IsCenteredModOne (a i / Real.pi) (d i)) :
    ‖Fourier.finExpectation (I → Bool) (fun ξ ↦
      Complex.exp ((((∑ i, a i * Fourier.rademacherSign (ξ i) : ℝ)) : ℂ) *
        Complex.I) * rademacherWalshMonomial S ξ)‖ ≤
      Real.exp (-∑ i ∈ Finset.univ.filter (fun i ↦ i ∉ S), d i ^ 2) := by
  rw [finExpectation_exp_rademacher_linear_mul_walshMonomial, norm_prod]
  calc
    (∏ i, ‖if i ∈ S then
        Complex.I * Real.sin (a i) else (Real.cos (a i) : ℂ)‖) ≤
        ∏ i, if i ∈ S then 1 else Real.exp (-(d i) ^ 2) := by
      apply Finset.prod_le_prod
      · intro i hi
        exact norm_nonneg _
      · intro i hi
        by_cases hiS : i ∈ S
        · rw [if_pos hiS, if_pos hiS, norm_mul, Complex.norm_I,
            Complex.norm_real, one_mul, Real.norm_eq_abs]
          exact Real.abs_sin_le_one _
        · rw [if_neg hiS, if_neg hiS, Complex.norm_real, Real.norm_eq_abs]
          exact Fourier.abs_cos_le_exp_neg_centeredModOne_sq (hd i)
    _ = Real.exp (-∑ i ∈ Finset.univ.filter (fun i ↦ i ∉ S), d i ^ 2) := by
      have hfilter :
          (∏ i, if i ∈ S then 1 else Real.exp (-(d i) ^ 2)) =
            ∏ i ∈ Finset.univ.filter (fun i ↦ i ∉ S),
              Real.exp (-(d i) ^ 2) := by
        rw [Finset.prod_filter]
        apply Finset.prod_congr rfl
        intro i hi
        by_cases hiS : i ∈ S <;> simp [hiS]
      rw [hfilter, ← Real.exp_sum]
      congr 1
      rw [Finset.sum_neg_distrib]

/-- Source-shaped form of KSSS (7.7): deleting the coordinates appearing
in a Walsh monomial costs at most one unit in the squared lattice-distance
exponent per deleted coordinate. -/
theorem norm_finExpectation_exp_rademacher_linear_mul_walshMonomial_le_latticeDist
    {I : Type*} [Fintype I] [DecidableEq I]
    (a : I → ℝ) (S : Finset I) :
    ‖Fourier.finExpectation (I → Bool) (fun ξ ↦
      Complex.exp ((((∑ i, a i * Fourier.rademacherSign (ξ i) : ℝ)) : ℂ) *
        Complex.I) * rademacherWalshMonomial S ξ)‖ ≤
      Real.exp ((S.card : ℝ) -
        RLCD.latticeDist (fun i ↦ a i / Real.pi) ^ 2) := by
  let d : I → ℝ := fun i ↦ centeredResidue (a i / Real.pi)
  have hbase :=
    norm_finExpectation_exp_rademacher_linear_mul_walshMonomial_le
      a d S (fun i ↦ centeredResidue_isCenteredModOne (a i / Real.pi))
  refine hbase.trans (Real.exp_le_exp.mpr ?_)
  have htotal :
      RLCD.latticeDist (fun i ↦ a i / Real.pi) ^ 2 = ∑ i, d i ^ 2 := by
    rw [RLCD.latticeDist]
    have hnonneg : 0 ≤ ∑ i, RLCD.distToInt (a i / Real.pi) ^ 2 :=
      Finset.sum_nonneg fun _ _ ↦ sq_nonneg _
    rw [Real.sq_sqrt hnonneg]
    apply Finset.sum_congr rfl
    intro i hi
    exact (centeredResidue_sq (a i / Real.pi)).symm
  have hinside : (∑ i ∈ S, d i ^ 2) ≤ (S.card : ℝ) := by
    calc
      (∑ i ∈ S, d i ^ 2) ≤ ∑ i ∈ S, (1 : ℝ) := by
        apply Finset.sum_le_sum
        intro i hi
        change centeredResidue (a i / Real.pi) ^ 2 ≤ 1
        rw [centeredResidue_sq]
        have hnonneg := RLCD.distToInt_nonneg (a i / Real.pi)
        have hhalf := RLCD.distToInt_le_half (a i / Real.pi)
        nlinarith
      _ = (S.card : ℝ) := by simp
  have hsplit :
      (∑ i ∈ Finset.univ.filter (fun i ↦ i ∉ S), d i ^ 2) +
          ∑ i ∈ S, d i ^ 2 = ∑ i, d i ^ 2 := by
    have hfilter : Finset.univ.filter (fun i ↦ i ∉ S) = Finset.univ \ S := by
      ext i
      simp
    rw [hfilter]
    exact Finset.sum_sdiff (Finset.subset_univ S)
  rw [htotal]
  linarith

lemma finExpectation_sum
    {Ω J : Type*} [Fintype Ω] [Nonempty Ω] [Fintype J]
    (f : J → Ω → ℂ) :
    Fourier.finExpectation Ω (fun ω ↦ ∑ j, f j ω) =
      ∑ j, Fourier.finExpectation Ω (f j) := by
  rw [Fourier.finExpectation]
  simp_rw [Fourier.finExpectation]
  rw [Finset.sum_comm, Finset.sum_div]

/-- Summing the monomial estimate: a finite Walsh polynomial of degree at
most `m` cannot correlate with the linear Rademacher phase by more than
its coefficient `ℓ¹` mass times the remaining lattice decay. -/
theorem norm_finExpectation_exp_rademacher_linear_mul_walshSum_le
    {I J : Type*} [Fintype I] [DecidableEq I] [Fintype J]
    (a : I → ℝ) (c : J → ℂ) (support : J → Finset I)
    {m : ℕ} {A : ℝ}
    (hdegree : ∀ j, (support j).card ≤ m)
    (hdist : (m : ℝ) + A ≤
      RLCD.latticeDist (fun i ↦ a i / Real.pi) ^ 2) :
    ‖Fourier.finExpectation (I → Bool) (fun ξ ↦
      Complex.exp ((((∑ i, a i * Fourier.rademacherSign (ξ i) : ℝ)) : ℂ) *
        Complex.I) *
        ∑ j, c j * rademacherWalshMonomial (support j) ξ)‖ ≤
      (∑ j, ‖c j‖) * Real.exp (-A) := by
  have hpoint : (fun ξ : I → Bool ↦
      Complex.exp ((((∑ i, a i * Fourier.rademacherSign (ξ i) : ℝ)) : ℂ) *
        Complex.I) *
        ∑ j, c j * rademacherWalshMonomial (support j) ξ) =
      (fun ξ ↦ ∑ j, c j *
        (Complex.exp ((((∑ i, a i * Fourier.rademacherSign (ξ i) : ℝ)) : ℂ) *
          Complex.I) * rademacherWalshMonomial (support j) ξ)) := by
    funext ξ
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    ring
  rw [hpoint, finExpectation_sum]
  calc
    ‖∑ j, Fourier.finExpectation (I → Bool) (fun ξ ↦
        c j * (Complex.exp
          ((((∑ i, a i * Fourier.rademacherSign (ξ i) : ℝ)) : ℂ) * Complex.I) *
            rademacherWalshMonomial (support j) ξ))‖ ≤
        ∑ j, ‖Fourier.finExpectation (I → Bool) (fun ξ ↦
          c j * (Complex.exp
            ((((∑ i, a i * Fourier.rademacherSign (ξ i) : ℝ)) : ℂ) * Complex.I) *
              rademacherWalshMonomial (support j) ξ))‖ :=
      norm_sum_le _ _
    _ ≤ ∑ j, ‖c j‖ * Real.exp (-A) := by
      apply Finset.sum_le_sum
      intro j hj
      rw [Fourier.finExpectation_const_mul, norm_mul]
      apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
      refine (norm_finExpectation_exp_rademacher_linear_mul_walshMonomial_le_latticeDist
        a (support j)).trans ?_
      apply Real.exp_le_exp.mpr
      have hcard : ((support j).card : ℝ) ≤ m := by
        exact_mod_cast hdegree j
      linarith
    _ = (∑ j, ‖c j‖) * Real.exp (-A) := by
      rw [Finset.sum_mul]

lemma rademacherWalshMonomial_mul {I : Type*} [Fintype I] [DecidableEq I]
    (S T : Finset I) (ξ : I → Bool) :
    rademacherWalshMonomial S ξ * rademacherWalshMonomial T ξ =
      rademacherWalshMonomial (S ∆ T) ξ := by
  simp only [rademacherWalshMonomial]
  rw [← Finset.prod_inter_mul_prod_sdiff S T,
    ← Finset.prod_inter_mul_prod_sdiff T S]
  rw [Finset.inter_comm T S]
  have hcommon :
      (∏ i ∈ S ∩ T, (Fourier.rademacherSign (ξ i) : ℂ)) *
          ∏ i ∈ S ∩ T, (Fourier.rademacherSign (ξ i) : ℂ) = 1 := by
    rw [← Finset.prod_mul_distrib]
    apply Finset.prod_eq_one
    intro i hi
    norm_cast
    simpa [pow_two] using Fourier.rademacherSign_sq (ξ i)
  have hdisjoint : Disjoint (S \ T) (T \ S) := by
    exact Finset.disjoint_left.mpr (by simp +contextual)
  rw [Finset.symmDiff_def, Finset.prod_union hdisjoint]
  calc
    ((∏ i ∈ S ∩ T, (Fourier.rademacherSign (ξ i) : ℂ)) *
          ∏ i ∈ S \ T, (Fourier.rademacherSign (ξ i) : ℂ)) *
        ((∏ i ∈ S ∩ T, (Fourier.rademacherSign (ξ i) : ℂ)) *
          ∏ i ∈ T \ S, (Fourier.rademacherSign (ξ i) : ℂ)) =
        ((∏ i ∈ S ∩ T, (Fourier.rademacherSign (ξ i) : ℂ)) *
          ∏ i ∈ S ∩ T, (Fourier.rademacherSign (ξ i) : ℂ)) *
        ((∏ i ∈ S \ T, (Fourier.rademacherSign (ξ i) : ℂ)) *
          ∏ i ∈ T \ S, (Fourier.rademacherSign (ξ i) : ℂ)) := by ring
    _ = (∏ i ∈ S \ T, (Fourier.rademacherSign (ξ i) : ℂ)) *
          ∏ i ∈ T \ S, (Fourier.rademacherSign (ξ i) : ℂ) := by
      rw [hcommon, one_mul]

/-- Symmetric-difference support of a product of Walsh monomials. -/
def xorSupport {I J : Type*} [DecidableEq I] (support : J → Finset I) :
    {j : ℕ} → (Fin j → J) → Finset I
  | 0, _ => ∅
  | j + 1, q => support (q 0) ∆ xorSupport support (fun r ↦ q r.succ)

lemma xorSupport_card_le {I J : Type*} [DecidableEq I]
    (support : J → Finset I) {m : ℕ}
    (hdegree : ∀ q, (support q).card ≤ m) :
    ∀ {j : ℕ} (q : Fin j → J), (xorSupport support q).card ≤ j * m := by
  intro j
  induction j with
  | zero =>
      intro q
      simp [xorSupport]
  | succ j ih =>
      intro q
      calc
        (xorSupport support q).card ≤
            (support (q 0) ∪ xorSupport support (fun r ↦ q r.succ)).card :=
          Finset.card_le_card Finset.symmDiff_subset_union
        _ ≤ (support (q 0)).card +
            (xorSupport support (fun r ↦ q r.succ)).card :=
          Finset.card_union_le _ _
        _ ≤ m + j * m := Nat.add_le_add (hdegree _) (ih _)
        _ = (j + 1) * m := by simp [Nat.succ_mul, Nat.add_comm]

lemma prod_rademacherWalshMonomial_eq {I J : Type*}
    [Fintype I] [DecidableEq I]
    (support : J → Finset I) :
    ∀ {j : ℕ} (q : Fin j → J) (ξ : I → Bool),
      (∏ r, rademacherWalshMonomial (support (q r)) ξ) =
        rademacherWalshMonomial (xorSupport support q) ξ := by
  intro j
  induction j with
  | zero =>
      intro q ξ
      simp [xorSupport, rademacherWalshMonomial]
  | succ j ih =>
      intro q ξ
      rw [Fin.prod_univ_succ, xorSupport,
        ih (fun r ↦ q r.succ) ξ,
        rademacherWalshMonomial_mul]

lemma walshSum_pow {I J : Type*} [Fintype I] [DecidableEq I]
    [Fintype J] (c : J → ℂ) (support : J → Finset I)
    (ξ : I → Bool) (j : ℕ) :
    (∑ q, c q * rademacherWalshMonomial (support q) ξ) ^ j =
      ∑ q : Fin j → J,
        (∏ r, c (q r)) * rademacherWalshMonomial (xorSupport support q) ξ := by
  rw [Fintype.sum_pow]
  apply Finset.sum_congr rfl
  intro q hq
  rw [Finset.prod_mul_distrib, prod_rademacherWalshMonomial_eq]

/-- The dependent finite index set of monomials in a Taylor polynomial. -/
abbrev TaylorWalshIndex (K : ℕ) (J : Type*) :=
  Σ j : Fin (K + 1), Fin j → J

noncomputable def taylorWalshCoeff {K : ℕ} {J : Type*}
    (lam : ℂ) (c : J → ℂ) (q : TaylorWalshIndex K J) : ℂ :=
  lam ^ q.1.val / q.1.val.factorial * ∏ r, c (q.2 r)

def taylorWalshSupport {I J : Type*} [DecidableEq I]
    {K : ℕ} (support : J → Finset I) (q : TaylorWalshIndex K J) : Finset I :=
  xorSupport support q.2

lemma taylor_walshSum_eq {I J : Type*} [Fintype I] [DecidableEq I]
    [Fintype J] (K : ℕ) (lam : ℂ) (c : J → ℂ)
    (support : J → Finset I) (ξ : I → Bool) :
    (∑ j ∈ Finset.range (K + 1),
      (lam * ∑ q, c q * rademacherWalshMonomial (support q) ξ) ^ j /
        (j.factorial : ℂ)) =
      ∑ q : TaylorWalshIndex K J,
        taylorWalshCoeff lam c q *
          rademacherWalshMonomial (taylorWalshSupport support q) ξ := by
  rw [← Fin.sum_univ_eq_sum_range (fun j : ℕ ↦
    (lam * ∑ q, c q * rademacherWalshMonomial (support q) ξ) ^ j /
      (j.factorial : ℂ)) (K + 1)]
  rw [Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro j hj
  rw [mul_pow, walshSum_pow]
  rw [Finset.mul_sum, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro q hq
  simp only [taylorWalshCoeff, taylorWalshSupport]
  ring

lemma taylorWalshSupport_card_le {I J : Type*} [DecidableEq I]
    {K m : ℕ} (support : J → Finset I)
    (hdegree : ∀ q, (support q).card ≤ m)
    (q : TaylorWalshIndex K J) :
    (taylorWalshSupport support q).card ≤ K * m := by
  refine (xorSupport_card_le support hdegree q.2).trans ?_
  exact Nat.mul_le_mul_right m (Nat.le_of_lt_succ q.1.isLt)

lemma sum_norm_taylorWalshCoeff {K : ℕ} {J : Type*} [Fintype J]
    (lam : ℂ) (c : J → ℂ) :
    (∑ q : TaylorWalshIndex K J, ‖taylorWalshCoeff lam c q‖) =
      ∑ j : Fin (K + 1),
        (‖lam‖ * ∑ q, ‖c q‖) ^ j.val / j.val.factorial := by
  rw [Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro j hj
  simp only [taylorWalshCoeff, norm_mul, norm_div, norm_pow, norm_prod,
    Complex.norm_natCast]
  rw [← Finset.mul_sum]
  have hp := Fintype.sum_pow (fun q : J ↦ ‖c q‖) j.val
  rw [← hp]
  ring

/-- The Taylor polynomial in a degree-`m` Walsh sum has degree at most
`K*m`; combining its explicit expansion with KSSS (7.7) gives the exact
correlation bound used for the first term of (7.4). -/
theorem norm_finExpectation_exp_rademacher_linear_mul_taylor_walshSum_le
    {I J : Type*} [Fintype I] [DecidableEq I] [Fintype J]
    (K : ℕ) (lam : ℂ) (a : I → ℝ) (c : J → ℂ)
    (support : J → Finset I) {m : ℕ} {A : ℝ}
    (hdegree : ∀ q, (support q).card ≤ m)
    (hdist : ((K * m : ℕ) : ℝ) + A ≤
      RLCD.latticeDist (fun i ↦ a i / Real.pi) ^ 2) :
    ‖Fourier.finExpectation (I → Bool) (fun ξ ↦
      Complex.exp ((((∑ i, a i * Fourier.rademacherSign (ξ i) : ℝ)) : ℂ) *
        Complex.I) *
        ∑ j ∈ Finset.range (K + 1),
          (lam * ∑ q, c q * rademacherWalshMonomial (support q) ξ) ^ j /
            (j.factorial : ℂ))‖ ≤
      (∑ j : Fin (K + 1),
        (‖lam‖ * ∑ q, ‖c q‖) ^ j.val / j.val.factorial) *
          Real.exp (-A) := by
  have hpoint : (fun ξ : I → Bool ↦
      ∑ j ∈ Finset.range (K + 1),
        (lam * ∑ q, c q * rademacherWalshMonomial (support q) ξ) ^ j /
          (j.factorial : ℂ)) =
      (fun ξ ↦ ∑ q : TaylorWalshIndex K J,
        taylorWalshCoeff lam c q *
          rademacherWalshMonomial (taylorWalshSupport support q) ξ) := by
    funext ξ
    exact taylor_walshSum_eq K lam c support ξ
  have hwhole : (fun ξ : I → Bool ↦
      Complex.exp ((((∑ i, a i * Fourier.rademacherSign (ξ i) : ℝ)) : ℂ) *
        Complex.I) *
        ∑ j ∈ Finset.range (K + 1),
          (lam * ∑ q, c q * rademacherWalshMonomial (support q) ξ) ^ j /
            (j.factorial : ℂ)) =
      (fun ξ ↦ Complex.exp
        ((((∑ i, a i * Fourier.rademacherSign (ξ i) : ℝ)) : ℂ) * Complex.I) *
        ∑ q : TaylorWalshIndex K J,
          taylorWalshCoeff lam c q *
            rademacherWalshMonomial (taylorWalshSupport support q) ξ) := by
    funext ξ
    rw [congrFun hpoint ξ]
  rw [hwhole]
  have hbound :=
    norm_finExpectation_exp_rademacher_linear_mul_walshSum_le
      a (taylorWalshCoeff lam c) (taylorWalshSupport support)
      (m := K * m) (A := A)
      (fun q ↦ taylorWalshSupport_card_le support hdegree q) hdist
  rw [sum_norm_taylorWalshCoeff] at hbound
  exact hbound

/-- Equation (7.4) combined with the Walsh-correlation estimate (7.7).
Only the explicit Taylor remainder remains; in Lemma 7.2 it is bounded by
hypercontractivity of the internal quadratic form. -/
theorem norm_finExpectation_cexp_rademacherLinear_add_le_taylorCorrelation
    {I J : Type*} [Fintype I] [DecidableEq I] [Fintype J]
    (K : ℕ) (lam : ℂ) (a : I → ℝ) (v : (I → Bool) → ℝ)
    (c : J → ℂ) (support : J → Finset I) {m : ℕ} {A : ℝ}
    (hquad : ∀ ξ,
      ((v ξ : ℝ) : ℂ) * Complex.I =
        lam * ∑ q, c q * rademacherWalshMonomial (support q) ξ)
    (hdegree : ∀ q, (support q).card ≤ m)
    (hdist : ((K * m : ℕ) : ℝ) + A ≤
      RLCD.latticeDist (fun i ↦ a i / Real.pi) ^ 2) :
    ‖Fourier.finExpectation (I → Bool) (fun ξ ↦
      Complex.exp (((((∑ i, a i * Fourier.rademacherSign (ξ i)) + v ξ : ℝ) : ℂ) *
        Complex.I)))‖ ≤
      (∑ j : Fin (K + 1),
        (‖lam‖ * ∑ q, ‖c q‖) ^ j.val / j.val.factorial) *
          Real.exp (-A) +
        (∑ ξ, |v ξ| ^ (K + 1) / K.factorial) /
          Fintype.card (I → Bool) := by
  let u : (I → Bool) → ℝ := fun ξ ↦
    ∑ i, a i * Fourier.rademacherSign (ξ i)
  have htaylor := norm_finExpectation_cexp_add_le_taylor K u v
  have hfirst :
      ‖Fourier.finExpectation (I → Bool) (fun ξ ↦
        Complex.exp (((u ξ : ℝ) : ℂ) * Complex.I) *
          ∑ j ∈ Finset.range (K + 1),
            ((((v ξ : ℝ) : ℂ) * Complex.I) ^ j) /
              (j.factorial : ℂ))‖ ≤
        (∑ j : Fin (K + 1),
          (‖lam‖ * ∑ q, ‖c q‖) ^ j.val / j.val.factorial) *
            Real.exp (-A) := by
    have hfun : (fun ξ : I → Bool ↦
        Complex.exp (((u ξ : ℝ) : ℂ) * Complex.I) *
          ∑ j ∈ Finset.range (K + 1),
            ((((v ξ : ℝ) : ℂ) * Complex.I) ^ j) /
              (j.factorial : ℂ)) =
        (fun ξ ↦
          Complex.exp ((((∑ i, a i * Fourier.rademacherSign (ξ i) : ℝ)) : ℂ) *
            Complex.I) *
            ∑ j ∈ Finset.range (K + 1),
              (lam * ∑ q, c q * rademacherWalshMonomial (support q) ξ) ^ j /
                (j.factorial : ℂ)) := by
      funext ξ
      simp only [u]
      rw [hquad ξ]
    rw [hfun]
    exact norm_finExpectation_exp_rademacher_linear_mul_taylor_walshSum_le
      K lam a c support hdegree hdist
  calc
    ‖Fourier.finExpectation (I → Bool) (fun ξ ↦
        Complex.exp (((((∑ i, a i * Fourier.rademacherSign (ξ i)) + v ξ : ℝ) : ℂ) *
          Complex.I)))‖ =
        ‖Fourier.finExpectation (I → Bool) (fun ξ ↦
          Complex.exp ((((u ξ + v ξ : ℝ) : ℂ) * Complex.I)))‖ := by rfl
    _ ≤ ‖Fourier.finExpectation (I → Bool) (fun ξ ↦
          Complex.exp (((u ξ : ℝ) : ℂ) * Complex.I) *
            ∑ j ∈ Finset.range (K + 1),
              ((((v ξ : ℝ) : ℂ) * Complex.I) ^ j) /
                (j.factorial : ℂ))‖ +
          (∑ ξ, |v ξ| ^ (K + 1) / K.factorial) /
            Fintype.card (I → Bool) := htaylor
    _ ≤ (∑ j : Fin (K + 1),
          (‖lam‖ * ∑ q, ‖c q‖) ^ j.val / j.val.factorial) *
            Real.exp (-A) +
          (∑ ξ, |v ξ| ^ (K + 1) / K.factorial) /
            Fintype.card (I → Bool) := add_le_add_left hfirst _

open RademacherHypercontractivity
open RademacherHypercontractivity.CubePoly

/-- Equations (7.4) and (7.7) with the Taylor remainder discharged by
the finite-cube Bonami inequality for an explicit quadratic form. -/
theorem norm_finExpectation_cexp_rademacherLinear_add_quadratic_le
    {I J : Type*} [Fintype I] [DecidableEq I] [Fintype J]
    (r : ℕ) (lam : ℂ) (a : I → ℝ) (v : (I → Bool) → ℝ)
    (A : I → I → ℝ) (c : J → ℂ) (support : J → Finset I)
    {m : ℕ} {D : ℝ}
    (hv : ∀ ξ, v ξ = ∑ i, ∑ j,
      A i j * Fourier.rademacherSign (ξ i) * Fourier.rademacherSign (ξ j))
    (hquad : ∀ ξ,
      ((v ξ : ℝ) : ℂ) * Complex.I =
        lam * ∑ q, c q * rademacherWalshMonomial (support q) ξ)
    (hdegree : ∀ q, (support q).card ≤ m)
    (hdist : ((((2 ^ (r + 1) - 1) * m : ℕ) : ℝ) + D) ≤
      RLCD.latticeDist (fun i ↦ a i / Real.pi) ^ 2) :
    ‖Fourier.finExpectation (I → Bool) (fun ξ ↦
      Complex.exp (((((∑ i, a i * Fourier.rademacherSign (ξ i)) + v ξ : ℝ) : ℂ) *
        Complex.I)))‖ ≤
      (∑ j : Fin (2 ^ (r + 1)),
        (‖lam‖ * ∑ q, ‖c q‖) ^ j.val / j.val.factorial) *
          Real.exp (-D) +
        (9 ^ bonamiExponent 2 r * quadraticCubeMean A 2 ^ (2 ^ r)) /
          (2 ^ (r + 1) - 1).factorial := by
  let K := 2 ^ (r + 1) - 1
  have hK : K + 1 = 2 ^ (r + 1) := by
    dsimp only [K]
    have hpos : 0 < 2 ^ (r + 1) := by positivity
    omega
  have hbase := norm_finExpectation_cexp_rademacherLinear_add_le_taylorCorrelation
    K lam a v c support hquad hdegree hdist
  have hmoment := quadraticCubeAbsMean_two_pow_succ_le A r
  have hmoment' :
      ((∑ ξ, |v ξ| ^ (K + 1)) / Fintype.card (I → Bool)) ≤
        9 ^ bonamiExponent 2 r * quadraticCubeMean A 2 ^ (2 ^ r) := by
    rw [hK]
    simpa only [hv, quadraticCubeMean] using hmoment
  have hremEq :
      ((∑ ξ, |v ξ| ^ (K + 1) / K.factorial) /
          Fintype.card (I → Bool)) =
        (((∑ ξ, |v ξ| ^ (K + 1)) / Fintype.card (I → Bool)) /
          K.factorial) := by
    rw [Finset.sum_div]
    simp only [div_eq_mul_inv]
    simp_rw [mul_assoc]
    rw [← Finset.sum_mul]
    ring
  have hvsum :
      ((∑ ξ, |v ξ| ^ (K + 1) / K.factorial) /
          Fintype.card (I → Bool)) ≤
        (9 ^ bonamiExponent 2 r * quadraticCubeMean A 2 ^ (2 ^ r)) /
          K.factorial := by
    rw [hremEq]
    exact div_le_div_of_nonneg_right hmoment' (by positivity)
  rw [hK] at hbase
  rw [hK] at hvsum
  dsimp only [K] at hvsum
  exact hbase.trans (add_le_add le_rfl hvsum)

open GraphQuadratic

/-- Exact second moment of a symmetric, diagonal-free quadratic form on
the uniform Rademacher cube. -/
theorem quadraticCubeMean_two_eq_two_mul_frobeniusSq
    {n : ℕ} (F : Fin n → Fin n → ℝ)
    (hF : ∀ i j, F i j = F j i) (hdiag : ∀ i, F i i = 0) :
    quadraticCubeMean F 2 = 2 * BooleanSlices.frobeniusSq F := by
  classical
  let e : (Fin n → Bool) ≃ Finset (Fin n) :=
    BooleanSlices.boolFunEquivFinset
  have hsign (x : Fin n → Bool) :
      (fun i ↦ Fourier.rademacherSign (x i)) =
        BooleanSlices.signOfSet (e x) := by
    funext i
    cases hxi : x i <;>
      simp [e, BooleanSlices.boolFunEquivFinset,
        BooleanSlices.signOfSet, Fourier.rademacherSign, hxi]
  have hsum :
      (∑ x : Fin n → Bool,
        (∑ i, ∑ j, F i j * Fourier.rademacherSign (x i) *
          Fourier.rademacherSign (x j)) ^ 2) =
        ∑ S : Finset (Fin n),
          (BooleanSlices.quadraticPart F
            (BooleanSlices.signOfSet S)) ^ 2 := by
    calc
      (∑ x : Fin n → Bool,
        (∑ i, ∑ j, F i j * Fourier.rademacherSign (x i) *
          Fourier.rademacherSign (x j)) ^ 2) =
          ∑ x : Fin n → Bool,
            (BooleanSlices.quadraticPart F
              (BooleanSlices.signOfSet (e x))) ^ 2 := by
            apply Finset.sum_congr rfl
            intro x hx
            rw [← hsign x]
            simp only [BooleanSlices.quadraticPart]
            congr 1
            apply Finset.sum_congr rfl
            intro i hi
            apply Finset.sum_congr rfl
            intro j hj
            ring
      _ = ∑ S : Finset (Fin n),
          (BooleanSlices.quadraticPart F
            (BooleanSlices.signOfSet S)) ^ 2 :=
        e.sum_comp (fun S ↦
          (BooleanSlices.quadraticPart F
            (BooleanSlices.signOfSet S)) ^ 2)
  unfold quadraticCubeMean
  rw [hsum, Fintype.card_congr e]
  rw [← Fintype.expect_eq_sum_div_card]
  change BooleanSlices.uniformExpectation
      (fun S : Finset (Fin n) ↦
        (BooleanSlices.quadraticPart F
          (BooleanSlices.signOfSet S)) ^ 2) = _
  have hvar := BooleanSlices.rademacher_sliceQuadratic_variance_symmetric
    (0 : ℝ) (fun _ : Fin n ↦ 0) F hF
  rw [BooleanSlices.uniformVariance,
    BooleanSlices.rademacher_sliceQuadratic_mean] at hvar
  simpa [BooleanSlices.sliceQuadratic,
    BooleanSlices.quadraticPolynomial, BooleanSlices.linearPart,
    BooleanSlices.trace, hdiag, BooleanSlices.vectorSqNorm] using hvar

/-- The preceding orthogonality identity on an arbitrary finite coordinate
type, obtained by reindexing it with `Fin`. -/
theorem quadraticCubeMean_two_eq_two_mul_sum_sq
    {I : Type*} [Fintype I] [DecidableEq I]
    (F : I → I → ℝ)
    (hF : ∀ i j, F i j = F j i) (hdiag : ∀ i, F i i = 0) :
    quadraticCubeMean F 2 = 2 * ∑ i, ∑ j, F i j ^ 2 := by
  classical
  let e : I ≃ Fin (Fintype.card I) := Fintype.equivFin I
  let se : (I → Bool) ≃ (Fin (Fintype.card I) → Bool) :=
    Equiv.piCongrLeft (fun _ ↦ Bool) e
  let F' : Fin (Fintype.card I) → Fin (Fintype.card I) → ℝ :=
    fun i j ↦ F (e.symm i) (e.symm j)
  have hF' : ∀ i j, F' i j = F' j i := by
    intro i j
    exact hF _ _
  have hdiag' : ∀ i, F' i i = 0 := by
    intro i
    exact hdiag _
  have hmean : quadraticCubeMean F 2 = quadraticCubeMean F' 2 := by
    unfold quadraticCubeMean
    rw [← Fintype.card_congr se]
    congr 1
    have hs := se.sum_comp (fun x ↦
      (∑ i, ∑ j, F' i j * Fourier.rademacherSign (x i) *
        Fourier.rademacherSign (x j)) ^ 2)
    rw [← hs]
    apply Finset.sum_congr rfl
    intro x hx
    congr 1
    rw [← e.sum_comp]
    apply Finset.sum_congr rfl
    intro i hi
    rw [← e.sum_comp]
    apply Finset.sum_congr rfl
    intro j hj
    simp [F', se, e]
  have hfrob :
      (∑ i : Fin (Fintype.card I), ∑ j, F' i j ^ 2) =
        ∑ i : I, ∑ j, F i j ^ 2 := by
    rw [← e.sum_comp]
    apply Finset.sum_congr rfl
    intro i hi
    rw [← e.sum_comp]
    apply Finset.sum_congr rfl
    intro j hj
    simp [F']
  rw [hmean,
    quadraticCubeMean_two_eq_two_mul_frobeniusSq F' hF' hdiag']
  rw [BooleanSlices.frobeniusSq, hfrob]

/-- A pointwise coefficient bound controls the second moment of any
symmetric diagonal-free quadratic form. -/
theorem quadraticCubeMean_two_le_card_sq_mul
    {I : Type*} [Fintype I] [DecidableEq I]
    (F : I → I → ℝ) (b : ℝ)
    (hF : ∀ i j, F i j = F j i) (hdiag : ∀ i, F i i = 0)
    (hb : 0 ≤ b) (hbound : ∀ i j, |F i j| ≤ b) :
    quadraticCubeMean F 2 ≤
      2 * (Fintype.card I : ℝ) ^ 2 * b ^ 2 := by
  rw [quadraticCubeMean_two_eq_two_mul_sum_sq F hF hdiag]
  have hsq (i j : I) : F i j ^ 2 ≤ b ^ 2 := by
    simpa only [sq_abs] using
      (sq_le_sq₀ (abs_nonneg (F i j)) hb).2 (hbound i j)
  calc
    2 * ∑ i : I, ∑ j : I, F i j ^ 2 ≤
        2 * ∑ _i : I, ∑ _j : I, b ^ 2 := by
          apply mul_le_mul_of_nonneg_left _ (by norm_num)
          apply Finset.sum_le_sum
          intro i hi
          apply Finset.sum_le_sum
          intro j hj
          exact hsq i j
    _ = 2 * (Fintype.card I : ℝ) ^ 2 * b ^ 2 := by
      simp [pow_two]
      ring

open Classical in
/-- The internal graph quadratic has exactly one independent Walsh
coefficient of size `t / 4` for every edge. -/
theorem graphSliceMatrix_quadraticCubeMean_two
    {n : ℕ} (G : SimpleGraph (Fin n)) (t : ℝ) :
    quadraticCubeMean
        (fun i j ↦ t * graphSliceMatrix G i j) 2 =
      t ^ 2 * (G.edgeFinset.card : ℝ) / 16 := by
  classical
  let F : Fin n → Fin n → ℝ :=
    fun i j ↦ t * graphSliceMatrix G i j
  have hF : ∀ i j, F i j = F j i := by
    intro i j
    simp only [F]
    rw [graphSliceMatrix_symmetric G]
  have hdiag : ∀ i, F i i = 0 := by
    intro i
    simp [F, graphSliceMatrix_diagonal]
  rw [quadraticCubeMean_two_eq_two_mul_frobeniusSq F hF hdiag]
  have hfrob : BooleanSlices.frobeniusSq F =
      t ^ 2 * BooleanSlices.frobeniusSq (graphSliceMatrix G) := by
    simp only [BooleanSlices.frobeniusSq, F]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    ring
  rw [hfrob, frobeniusSq_graphSliceMatrix]
  ring

/-- Algebraic core of KSSS Lemma 7.3: positive induced density forces
the ambient effective linear coefficients to have cubic restricted mass. -/
theorem graphEffectiveLinear_restrict_sq_lower {n : ℕ}
    (G : SimpleGraph (Fin n)) (c : Fin n → ℝ) (I : Finset (Fin n))
    {a : ℝ} (ha : 0 ≤ a) (hI : 0 < I.card)
    (hc : ∀ i, 0 ≤ c i)
    (hedge : a * (I.card : ℝ) ^ 2 ≤ (AKSGraph.edgeCount G I : ℝ)) :
    a ^ 2 * (I.card : ℝ) ^ 3 ≤
      ∑ i : I, graphEffectiveLinear G c i.1 ^ 2 := by
  classical
  letI (i : Fin n) : Fintype ↑(G.neighborSet i) :=
    Subtype.fintype (Membership.mem (G.neighborSet i))
  let d : I → ℝ := fun i ↦ graphEffectiveLinear G c i.1
  have hd : ∀ i, 0 ≤ d i := by
    intro i
    exact add_nonneg (hc i.1) (div_nonneg (by positivity) (by norm_num))
  have hdegree (i : I) :
      (AKSGraph.degreeInto G i.1 I : ℝ) ≤ G.degree i.1 := by
    have hnat : AKSGraph.degreeInto G i.1 I ≤ G.degree i.1 := by
      rw [AKSGraph.degreeInto, ← G.card_neighborFinset_eq_degree]
      exact Finset.card_le_card
        (Finset.inter_subset_left : G.neighborFinset i.1 ∩ I ⊆ G.neighborFinset i.1)
    exact_mod_cast hnat
  have hsumDegree :
      (∑ i : I, (AKSGraph.degreeInto G i.1 I : ℝ)) =
        2 * (AKSGraph.edgeCount G I : ℝ) := by
    have hnat := AKSGraph.sum_degreeInto G I
    have hsub : (∑ i : I, AKSGraph.degreeInto G i.1 I) =
        ∑ i ∈ I, AKSGraph.degreeInto G i I := by
      symm
      exact Finset.sum_subtype I (by simp) _
    rw [← hsub] at hnat
    exact_mod_cast hnat
  have hsum : (AKSGraph.edgeCount G I : ℝ) ≤ ∑ i, d i := by
    calc
      (AKSGraph.edgeCount G I : ℝ) =
          (1 / 2 : ℝ) * ∑ i : I,
            (AKSGraph.degreeInto G i.1 I : ℝ) := by rw [hsumDegree]; ring
      _ ≤ (1 / 2 : ℝ) * ∑ i : I, (G.degree i.1 : ℝ) := by
        gcongr with i
        exact_mod_cast hdegree i
      _ ≤ ∑ i, d i := by
        rw [Finset.mul_sum]
        apply Finset.sum_le_sum
        intro i hi
        dsimp only [d, graphEffectiveLinear]
        rw [div_eq_mul_inv]
        have hci := hc i.1
        linarith
  have hsumNonneg : 0 ≤ ∑ i, d i := Finset.sum_nonneg fun i _ ↦ hd i
  have hedgeNonneg : 0 ≤ (AKSGraph.edgeCount G I : ℝ) := by positivity
  have hedgeSq : (a * (I.card : ℝ) ^ 2) ^ 2 ≤
      (AKSGraph.edgeCount G I : ℝ) ^ 2 :=
    (sq_le_sq₀ (mul_nonneg ha (sq_nonneg _)) hedgeNonneg).2 hedge
  have hsumSq : (AKSGraph.edgeCount G I : ℝ) ^ 2 ≤ (∑ i, d i) ^ 2 :=
    (sq_le_sq₀ hedgeNonneg hsumNonneg).2 hsum
  have hcauchy : (∑ i, d i) ^ 2 ≤
      (I.card : ℝ) * ∑ i, d i ^ 2 := by
    simpa only [Finset.card_univ, Fintype.card_coe] using
      (sq_sum_le_card_mul_sum_sq
        (s := (Finset.univ : Finset I)) (f := d))
  have hcardPos : (0 : ℝ) < I.card := by exact_mod_cast hI
  apply (mul_le_mul_iff_of_pos_right hcardPos).mp
  calc
    a ^ 2 * (I.card : ℝ) ^ 3 * (I.card : ℝ) =
        (a * (I.card : ℝ) ^ 2) ^ 2 := by ring
    _ ≤ (AKSGraph.edgeCount G I : ℝ) ^ 2 := hedgeSq
    _ ≤ (∑ i, d i) ^ 2 := hsumSq
    _ ≤ (I.card : ℝ) * ∑ i, d i ^ 2 := hcauchy
    _ = (∑ i, d i ^ 2) * (I.card : ℝ) := by ring

/-- KSSS Lemma 7.3 in eventual, source-shaped form.  The constant comes
from the proved Erdős--Szemerédi density theorem applied to the induced
Ramsey graph on `I`. -/
theorem ksssLemma73 (C : ℝ) (hC : 0 < C) :
    ∃ a : ℝ, 0 < a ∧ ∃ N : ℕ,
      ∀ {n : ℕ}, 1 ≤ n → N ≤ n →
      ∀ (G : SimpleGraph (Fin n)), RamseyFree C G →
      ∀ (c : Fin n → ℝ), (∀ i, 0 ≤ c i) →
      ∀ I : Finset (Fin n), N ≤ I.card → Real.sqrt n ≤ (I.card : ℝ) →
        a ^ 2 * (I.card : ℝ) ^ 3 ≤
          ∑ i : I, graphEffectiveLinear G c i.1 ^ 2 := by
  classical
  obtain ⟨a, ha, N, hDensity⟩ :=
    FiniteES.ramseyFree_edgeCount_density_lower
      (2 * C) (mul_pos (by norm_num) hC)
  refine ⟨a, ha, N, ?_⟩
  intro n hn hNn G hG c hc I hNI hSqrt
  let GI : SimpleGraph (↥(I : Set (Fin n))) := G.induce (I : Set (Fin n))
  let H : SimpleGraph (Fin I.card) :=
    GI.overFin (card_subtype_coe_finset I)
  have hRamsey : RamseyFree (2 * C) H := by
    exact AKSGraph.ramseyFree_induce_overFin_of_sqrt G I hC hn hG hSqrt
  have hDense := hDensity I.card hNI H hRamsey
  have hEdge : FiniteES.edgeCount H = AKSGraph.edgeCount G I := by
    calc
      FiniteES.edgeCount H = FiniteES.edgeCount GI :=
        edgeCount_overFin GI (card_subtype_coe_finset I)
      _ = (G.induce (I : Set (Fin n))).edgeFinset.card := rfl
      _ = AKSGraph.edgeCount G I := by
        symm
        simpa only [AKSGraph.edgeCount] using
          G.card_filter_edgeFinset_toFinset_subset I
  rw [hEdge] at hDense
  have hIpos : 0 < I.card := by
    have hnpos : (0 : ℝ) < n := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hn)
    have hsqrtPos : 0 < Real.sqrt n := Real.sqrt_pos.2 hnpos
    exact_mod_cast hsqrtPos.trans_le hSqrt
  exact graphEffectiveLinear_restrict_sq_lower G c I ha.le hIpos hc hDense

private def orderedPairSupport {I : Type*} [DecidableEq I]
    (q : I × I) : Finset I := {q.1, q.2}

private lemma orderedPairWalsh_eq {I : Type*} [Fintype I] [DecidableEq I]
    (A : I → I → ℝ) (hdiag : ∀ i, A i i = 0)
    (ξ : I → Bool) :
    (∑ q : I × I, ((A q.1 q.2 : ℝ) : ℂ) *
      rademacherWalshMonomial (orderedPairSupport q) ξ) =
      ((∑ i, ∑ j, A i j * Fourier.rademacherSign (ξ i) *
        Fourier.rademacherSign (ξ j) : ℝ) : ℂ) := by
  rw [Fintype.sum_prod_type]
  push_cast
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  by_cases hij : i = j
  · subst j
    simp [hdiag, orderedPairSupport]
  · simp [rademacherWalshMonomial, orderedPairSupport, hij]
    ring

/-- The Taylor/Walsh/Bonami estimate specialized to a conditioned graph
quadratic on the inside coordinates. -/
theorem norm_graphConditionedCharacteristic_le_taylor
    {n : ℕ} (G : SimpleGraph (Fin n)) (c : Fin n → ℝ)
    (I : Finset (Fin n)) (z : {v : Fin n // v ∉ I} → Bool)
    (t : ℝ) (r : ℕ) (D : ℝ)
    (hdist : ((((2 ^ (r + 1) - 1) * 2 : ℕ) : ℝ) + D) ≤
      RLCD.latticeDist (fun i : I ↦
        (t * graphConditionedInsideLinear G c I z i) / Real.pi) ^ 2) :
    ‖graphConditionedCharacteristic G c I z t‖ ≤
      (∑ j : Fin (2 ^ (r + 1)),
        (∑ q : I × I,
          ‖((t * graphSliceMatrix G q.1.1 q.2.1 : ℝ) : ℂ)‖) ^
            j.val / j.val.factorial) * Real.exp (-D) +
        (9 ^ bonamiExponent 2 r *
          quadraticCubeMean
            (fun i j : I ↦ t * graphSliceMatrix G i.1 j.1) 2 ^ (2 ^ r)) /
          (2 ^ (r + 1) - 1).factorial := by
  classical
  let a : I → ℝ := fun i ↦ t * graphConditionedInsideLinear G c I z i
  let A : I → I → ℝ := fun i j ↦ t * graphSliceMatrix G i.1 j.1
  let coeff : I × I → ℂ := fun q ↦ (A q.1 q.2 : ℂ)
  let support : I × I → Finset I := orderedPairSupport
  let v : (I → Bool) → ℝ := fun ξ ↦ ∑ i, ∑ j,
    A i j * Fourier.rademacherSign (ξ i) * Fourier.rademacherSign (ξ j)
  have hdiag : ∀ i, A i i = 0 := by
    intro i
    simp [A, graphSliceMatrix_diagonal]
  have hv : ∀ ξ, v ξ = ∑ i, ∑ j,
      A i j * Fourier.rademacherSign (ξ i) * Fourier.rademacherSign (ξ j) :=
    fun _ ↦ rfl
  have hquad : ∀ ξ,
      ((v ξ : ℝ) : ℂ) * Complex.I =
        Complex.I * ∑ q, coeff q * rademacherWalshMonomial (support q) ξ := by
    intro ξ
    rw [orderedPairWalsh_eq A hdiag ξ]
    ring
  have hdegree : ∀ q, (support q).card ≤ 2 := by
    intro q
    simpa [support, orderedPairSupport] using
      (Finset.card_insert_le q.1 ({q.2} : Finset I))
  have hbase := norm_finExpectation_cexp_rademacherLinear_add_quadratic_le
    r Complex.I a v A coeff support hv hquad hdegree hdist
  unfold graphConditionedCharacteristic
  have hpoint (ξ : I → Bool) :
      t * ((∑ i : I, graphConditionedInsideLinear G c I z i *
            Fourier.rademacherSign (ξ i)) +
          ∑ i : I, ∑ j : I,
            graphSliceMatrix G i.1 j.1 * Fourier.rademacherSign (ξ i) *
              Fourier.rademacherSign (ξ j)) =
        (∑ i, a i * Fourier.rademacherSign (ξ i)) + v ξ := by
    dsimp only [a, v, A]
    rw [mul_add, Finset.mul_sum]
    apply congrArg₂ (· + ·)
    · apply Finset.sum_congr rfl
      intro i hi
      ring
    · rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j hj
      ring
  have hfun : (fun ξ : I → Bool ↦
      Complex.exp (((t *
        ((∑ i : I, graphConditionedInsideLinear G c I z i *
            Fourier.rademacherSign (ξ i)) +
          ∑ i : I, ∑ j : I,
            graphSliceMatrix G i.1 j.1 * Fourier.rademacherSign (ξ i) *
              Fourier.rademacherSign (ξ j)) : ℝ) : ℂ) * Complex.I)) =
      (fun ξ ↦ Complex.exp (((((∑ i, a i * Fourier.rademacherSign (ξ i)) +
        v ξ : ℝ) : ℂ) * Complex.I))) := by
    funext ξ
    rw [hpoint ξ]
  rw [hfun]
  simpa only [Complex.norm_I, one_mul, coeff, A, support] using hbase

lemma graphSliceMatrix_abs_le_one_eighth {n : ℕ}
    (G : SimpleGraph (Fin n)) (i j : Fin n) :
    |graphSliceMatrix G i j| ≤ 1 / 8 := by
  rw [graphSliceMatrix_apply]
  split <;> norm_num

/-- The total coefficient mass of a conditioned internal graph quadratic. -/
theorem sum_norm_mul_graphSliceMatrix_le
    {n : ℕ} (G : SimpleGraph (Fin n))
    (I : Finset (Fin n)) (t : ℝ) :
    (∑ q : I × I,
      ‖((t * graphSliceMatrix G q.1.1 q.2.1 : ℝ) : ℂ)‖) ≤
        |t| * (I.card : ℝ) ^ 2 / 8 := by
  classical
  calc
    (∑ q : I × I,
      ‖((t * graphSliceMatrix G q.1.1 q.2.1 : ℝ) : ℂ)‖) ≤
        ∑ _q : I × I, |t| * (1 / 8 : ℝ) := by
          apply Finset.sum_le_sum
          intro q hq
          rw [Complex.norm_real, Real.norm_eq_abs, abs_mul]
          exact mul_le_mul_of_nonneg_left
            (graphSliceMatrix_abs_le_one_eighth G q.1.1 q.2.1) (abs_nonneg t)
    _ = |t| * (I.card : ℝ) ^ 2 / 8 := by
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
        Fintype.card_prod, Fintype.card_coe]
      push_cast
      ring

/-- The conditioned internal graph quadratic has second moment at most the
complete-graph coefficient bound. -/
theorem graphSliceMatrix_restrict_quadraticCubeMean_two_le
    {n : ℕ} (G : SimpleGraph (Fin n))
    (I : Finset (Fin n)) (t : ℝ) :
    quadraticCubeMean
        (fun i j : I ↦ t * graphSliceMatrix G i.1 j.1) 2 ≤
      t ^ 2 * (I.card : ℝ) ^ 2 / 32 := by
  classical
  let F : I → I → ℝ := fun i j ↦ t * graphSliceMatrix G i.1 j.1
  have hsymm : ∀ i j, F i j = F j i := by
    intro i j
    simp only [F]
    rw [graphSliceMatrix_symmetric]
  have hdiag : ∀ i, F i i = 0 := by
    intro i
    simp [F, graphSliceMatrix_diagonal]
  have hbound : ∀ i j, |F i j| ≤ |t| / 8 := by
    intro i j
    dsimp only [F]
    rw [abs_mul]
    have h := graphSliceMatrix_abs_le_one_eighth G i.1 j.1
    nlinarith [abs_nonneg t]
  have hbase := quadraticCubeMean_two_le_card_sq_mul
    F (|t| / 8) hsymm hdiag (by positivity) hbound
  dsimp only [F] at hbase ⊢
  rw [Fintype.card_coe] at hbase
  calc
    quadraticCubeMean
        (fun i j : I ↦ t * graphSliceMatrix G i.1 j.1) 2 ≤
        2 * (I.card : ℝ) ^ 2 * (|t| / 8) ^ 2 := hbase
    _ = t ^ 2 * (I.card : ℝ) ^ 2 / 32 := by
      rw [div_pow, sq_abs]
      norm_num
      ring

/-- Coarse coefficient form of the conditioned Taylor/Bonami bound. -/
theorem norm_graphConditionedCharacteristic_le_taylor_bound
    {n : ℕ} (G : SimpleGraph (Fin n)) (c : Fin n → ℝ)
    (I : Finset (Fin n)) (z : {v : Fin n // v ∉ I} → Bool)
    (t : ℝ) (r : ℕ) (D : ℝ)
    (hdist : ((((2 ^ (r + 1) - 1) * 2 : ℕ) : ℝ) + D) ≤
      RLCD.latticeDist (fun i : I ↦
        (t * graphConditionedInsideLinear G c I z i) / Real.pi) ^ 2) :
    ‖graphConditionedCharacteristic G c I z t‖ ≤
      (∑ j : Fin (2 ^ (r + 1)),
        (|t| * (I.card : ℝ) ^ 2 / 8) ^ j.val / j.val.factorial) *
          Real.exp (-D) +
        (9 ^ bonamiExponent 2 r *
          (t ^ 2 * (I.card : ℝ) ^ 2 / 32) ^ (2 ^ r)) /
          (2 ^ (r + 1) - 1).factorial := by
  have hbase := norm_graphConditionedCharacteristic_le_taylor
    G c I z t r D hdist
  have hcoeff := sum_norm_mul_graphSliceMatrix_le G I t
  have hmoment := graphSliceMatrix_restrict_quadraticCubeMean_two_le G I t
  have hmoment0 : 0 ≤ quadraticCubeMean
      (fun i j : I ↦ t * graphSliceMatrix G i.1 j.1) 2 := by
    unfold quadraticCubeMean
    positivity
  refine hbase.trans ?_
  gcongr

lemma euclidNorm_mul_le_abs_mul_sqrt_card_mul
    {I : Type*} [Fintype I] (a : ℝ) (x : I → ℝ) {u : ℝ}
    (hu : 0 ≤ u) (hx : ∀ i, |x i| ≤ u) :
    RLCD.euclidNorm (fun i ↦ a * x i) ≤
      |a| * Real.sqrt (Fintype.card I) * u := by
  rw [RLCD.euclidNorm]
  apply (Real.sqrt_le_iff).2
  constructor
  · positivity
  · have hsq (i : I) : (a * x i) ^ 2 ≤ (|a| * u) ^ 2 := by
      have hs := (sq_le_sq₀ (abs_nonneg (a * x i))
        (mul_nonneg (abs_nonneg a) hu)).2 (by
          rw [abs_mul]
          exact mul_le_mul_of_nonneg_left (hx i) (abs_nonneg a))
      simpa only [sq_abs] using hs
    have hsqrt : Real.sqrt (Fintype.card I) ^ 2 = (Fintype.card I : ℝ) :=
      Real.sq_sqrt (by positivity)
    calc
      (∑ i, (a * x i) ^ 2) ≤ ∑ _i : I, (|a| * u) ^ 2 :=
        Finset.sum_le_sum fun i hi ↦ hsq i
      _ = (Fintype.card I : ℝ) * (|a| * u) ^ 2 := by simp
      _ = (|a| * Real.sqrt (Fintype.card I) * u) ^ 2 := by
        nlinarith [hsqrt]

lemma euclidNorm_graphCrossLinear_scaled_le
    {n : ℕ} (G : SimpleGraph (Fin n)) (I : Finset (Fin n))
    (z : {v : Fin n // v ∉ I} → Bool) (t u : ℝ)
    (hu : 0 ≤ u) (hgood : ∀ i : I, |graphCrossLinear G I i z| ≤ u) :
    RLCD.euclidNorm (fun i : I ↦
      t * graphCrossLinear G I i z / Real.pi) ≤
      |t| * Real.sqrt I.card * u / Real.pi := by
  have hbase := euclidNorm_mul_le_abs_mul_sqrt_card_mul
    (t / Real.pi) (fun i : I ↦ graphCrossLinear G I i z) hu hgood
  have hpi : 0 < Real.pi := Real.pi_pos
  have hvec : (fun i : I ↦
      t * graphCrossLinear G I i z / Real.pi) =
      (fun i : I ↦ (t / Real.pi) * graphCrossLinear G I i z) := by
    funext i
    ring
  rw [hvec]
  rw [abs_div, abs_of_pos hpi, Fintype.card_coe] at hbase
  calc
    RLCD.euclidNorm (fun i : I ↦
        t / Real.pi * graphCrossLinear G I i z) ≤
        |t| / Real.pi * Real.sqrt I.card * u := hbase
    _ = |t| * Real.sqrt I.card * u / Real.pi := by ring

/-- A typical outside assignment can lower the inside linear lattice
distance only by its Euclidean cross-term size. -/
theorem latticeDist_graphConditionedInsideLinear_lower
    {n : ℕ} (G : SimpleGraph (Fin n)) (c : Fin n → ℝ)
    (I : Finset (Fin n)) (z : {v : Fin n // v ∉ I} → Bool)
    (t u B : ℝ) (hu : 0 ≤ u)
    (hgood : ∀ i : I, |graphCrossLinear G I i z| ≤ u)
    (hbase : B ≤ RLCD.latticeDist (fun i : I ↦
      t * graphSliceLinear G c i.1 / Real.pi)) :
    B - |t| * Real.sqrt I.card * u / Real.pi ≤
      RLCD.latticeDist (fun i : I ↦
        t * graphConditionedInsideLinear G c I z i / Real.pi) := by
  let x : I → ℝ := fun i ↦ t * graphSliceLinear G c i.1 / Real.pi
  let y : I → ℝ := fun i ↦ t * graphCrossLinear G I i z / Real.pi
  have hpert := latticeDist_add_lower x y
  have hy := euclidNorm_graphCrossLinear_scaled_le G I z t u hu hgood
  have hvec : (fun i : I ↦
      t * graphConditionedInsideLinear G c I z i / Real.pi) =
      (fun i ↦ x i + y i) := by
    funext i
    dsimp only [x, y, graphConditionedInsideLinear]
    ring
  rw [hvec]
  dsimp only [x, y] at hpert hy
  linarith

lemma graphSliceLinear_scaled_eq_normalized
    {n : ℕ} (G : SimpleGraph (Fin n)) (c : Fin n → ℝ)
    (I : Finset (Fin n)) (t : ℝ)
    (hnorm : RLCD.euclidNorm (RLCD.restrict
      (graphEffectiveLinear G c) I) ≠ 0) :
    (fun i : I ↦ t * graphSliceLinear G c i.1 / Real.pi) =
      (fun i : I ↦
        (t * RLCD.euclidNorm (RLCD.restrict
          (graphEffectiveLinear G c) I) / (2 * Real.pi)) *
          RLCD.normalizedRestrict (graphEffectiveLinear G c) I i) := by
  funext i
  rw [graphSliceLinear_eq_half_effective]
  simp only [RLCD.normalizedRestrict]
  have hpi : Real.pi ≠ 0 := ne_of_gt Real.pi_pos
  field_simp

lemma latticeDist_graphSliceLinear_ge_logThreshold_of_lt_LCD
    {n : ℕ} (G : SimpleGraph (Fin n)) (c : Fin n → ℝ)
    (I : Finset (Fin n)) (L t : ℝ)
    (ht : 0 < t)
    (hnorm : 0 < RLCD.euclidNorm (RLCD.restrict
      (graphEffectiveLinear G c) I))
    (hbelow :
      t * RLCD.euclidNorm (RLCD.restrict
        (graphEffectiveLinear G c) I) / (2 * Real.pi) <
        RLCD.LCD L (RLCD.normalizedRestrict
          (graphEffectiveLinear G c) I)) :
    L * Real.sqrt (RLCD.logPlus
      ((t * RLCD.euclidNorm (RLCD.restrict
        (graphEffectiveLinear G c) I) / (2 * Real.pi)) / L)) ≤
      RLCD.latticeDist (fun i : I ↦
        t * graphSliceLinear G c i.1 / Real.pi) := by
  have htheta : 0 < t * RLCD.euclidNorm (RLCD.restrict
      (graphEffectiveLinear G c) I) / (2 * Real.pi) := by positivity
  have hbase := latticeDist_ge_logThreshold_of_lt_LCD htheta hbelow
  rw [graphSliceLinear_scaled_eq_normalized G c I t hnorm.ne']
  exact hbase

theorem latticeDist_graphConditionedInsideLinear_ge_logThreshold_sub
    {n : ℕ} (G : SimpleGraph (Fin n)) (c : Fin n → ℝ)
    (I : Finset (Fin n)) (z : {v : Fin n // v ∉ I} → Bool)
    (L t u : ℝ) (ht : 0 < t) (hu : 0 ≤ u)
    (hnorm : 0 < RLCD.euclidNorm (RLCD.restrict
      (graphEffectiveLinear G c) I))
    (hbelow :
      t * RLCD.euclidNorm (RLCD.restrict
        (graphEffectiveLinear G c) I) / (2 * Real.pi) <
        RLCD.LCD L (RLCD.normalizedRestrict
          (graphEffectiveLinear G c) I))
    (hgood : ∀ i : I, |graphCrossLinear G I i z| ≤ u) :
    L * Real.sqrt (RLCD.logPlus
        ((t * RLCD.euclidNorm (RLCD.restrict
          (graphEffectiveLinear G c) I) / (2 * Real.pi)) / L)) -
        |t| * Real.sqrt I.card * u / Real.pi ≤
      RLCD.latticeDist (fun i : I ↦
        t * graphConditionedInsideLinear G c I z i / Real.pi) := by
  apply latticeDist_graphConditionedInsideLinear_lower
    G c I z t u _ hu hgood
  exact latticeDist_graphSliceLinear_ge_logThreshold_of_lt_LCD
    G c I L t ht hnorm hbelow

/-- The source-shaped conditioned cancellation estimate: an LCD separation
budget that survives the outside cross-term perturbation supplies the
Taylor/Bonami bound. -/
theorem norm_graphConditionedCharacteristic_le_of_LCD_budget
    {n : ℕ} (G : SimpleGraph (Fin n)) (c : Fin n → ℝ)
    (I : Finset (Fin n)) (z : {v : Fin n // v ∉ I} → Bool)
    (L t u D : ℝ) (r : ℕ) (ht : 0 < t) (hu : 0 ≤ u) (hD : 0 ≤ D)
    (hnorm : 0 < RLCD.euclidNorm (RLCD.restrict
      (graphEffectiveLinear G c) I))
    (hbelow :
      t * RLCD.euclidNorm (RLCD.restrict
        (graphEffectiveLinear G c) I) / (2 * Real.pi) <
        RLCD.LCD L (RLCD.normalizedRestrict
          (graphEffectiveLinear G c) I))
    (hgood : ∀ i : I, |graphCrossLinear G I i z| ≤ u)
    (hbudget :
      Real.sqrt (((((2 ^ (r + 1) - 1) * 2 : ℕ) : ℝ)) + D) +
          |t| * Real.sqrt I.card * u / Real.pi ≤
        L * Real.sqrt (RLCD.logPlus
          ((t * RLCD.euclidNorm (RLCD.restrict
            (graphEffectiveLinear G c) I) / (2 * Real.pi)) / L))) :
    ‖graphConditionedCharacteristic G c I z t‖ ≤
      (∑ j : Fin (2 ^ (r + 1)),
        (|t| * (I.card : ℝ) ^ 2 / 8) ^ j.val / j.val.factorial) *
          Real.exp (-D) +
        (9 ^ bonamiExponent 2 r *
          (t ^ 2 * (I.card : ℝ) ^ 2 / 32) ^ (2 ^ r)) /
          (2 ^ (r + 1) - 1).factorial := by
  have hsep :=
    latticeDist_graphConditionedInsideLinear_ge_logThreshold_sub
      G c I z L t u ht hu hnorm hbelow hgood
  have hsqrt :
      Real.sqrt (((((2 ^ (r + 1) - 1) * 2 : ℕ) : ℝ)) + D) ≤
        RLCD.latticeDist (fun i : I ↦
          t * graphConditionedInsideLinear G c I z i / Real.pi) := by
    linarith
  have harg : 0 ≤ ((((2 ^ (r + 1) - 1) * 2 : ℕ) : ℝ)) + D := by
    positivity
  have hdist : ((((2 ^ (r + 1) - 1) * 2 : ℕ) : ℝ) + D) ≤
      RLCD.latticeDist (fun i : I ↦
        t * graphConditionedInsideLinear G c I z i / Real.pi) ^ 2 := by
    calc
      ((((2 ^ (r + 1) - 1) * 2 : ℕ) : ℝ) + D) =
          Real.sqrt (((((2 ^ (r + 1) - 1) * 2 : ℕ) : ℝ)) + D) ^ 2 := by
            rw [Real.sq_sqrt harg]
      _ ≤ RLCD.latticeDist (fun i : I ↦
          t * graphConditionedInsideLinear G c I z i / Real.pi) ^ 2 :=
        (sq_le_sq₀ (Real.sqrt_nonneg _)
          (RLCD.latticeDist_nonneg _)).2 hsqrt
  exact norm_graphConditionedCharacteristic_le_taylor_bound
    G c I z t r D hdist

theorem finiteCharacteristic_sliceQuadratic_eq_rademacher
    {n : ℕ} (f₀ : ℝ) (f : Fin n → ℝ) (F : Fin n → Fin n → ℝ)
    (t : ℝ) :
    BooleanSlices.finiteCharacteristic
        (BooleanSlices.sliceQuadratic f₀ f F) t =
      Fourier.finExpectation (Fin n → Bool) (fun x ↦
        Complex.exp (((t * BooleanSlices.rademacherQuadratic f₀ f F x : ℝ) : ℂ) *
          Complex.I)) := by
  classical
  let e : (Fin n → Bool) ≃ Finset (Fin n) :=
    BooleanSlices.boolFunEquivFinset
  have hsign (x : Fin n → Bool) :
      BooleanSlices.signOfSet (e x) =
        (fun i ↦ Fourier.rademacherSign (x i)) := by
    funext i
    cases hxi : x i <;>
      simp [e, BooleanSlices.boolFunEquivFinset,
        BooleanSlices.signOfSet, Fourier.rademacherSign, hxi]
  have hvalue (x : Fin n → Bool) :
      BooleanSlices.sliceQuadratic f₀ f F (e x) =
        BooleanSlices.rademacherQuadratic f₀ f F x := by
    unfold BooleanSlices.sliceQuadratic BooleanSlices.rademacherQuadratic
    rw [hsign x]
    rfl
  unfold BooleanSlices.finiteCharacteristic Fourier.finExpectation
  rw [Fintype.expect_eq_sum_div_card]
  rw [← Fintype.card_congr e]
  congr 1
  rw [← e.sum_comp]
  apply Finset.sum_congr rfl
  intro x hx
  rw [hvalue x]
  congr 1
  ring

open Classical in
theorem finiteCharacteristic_perturbedEdgePolynomial_eq_graphRademacher
    {n : ℕ} (G : SimpleGraph (Fin n)) (e₀ : ℝ) (c : Fin n → ℝ)
    (t : ℝ) :
    BooleanSlices.finiteCharacteristic
        (Probability.perturbedEdgePolynomial G e₀ c) t =
      Fourier.finExpectation (Fin n → Bool) (fun x ↦
        Complex.exp (((t * BooleanSlices.rademacherQuadratic
          (graphSliceConstant G e₀ c) (graphSliceLinear G c)
          (graphSliceMatrix G) x : ℝ) : ℂ) * Complex.I)) := by
  have hP : Probability.perturbedEdgePolynomial G e₀ c =
      BooleanSlices.sliceQuadratic (graphSliceConstant G e₀ c)
        (graphSliceLinear G c) (graphSliceMatrix G) := by
    funext W
    exact (sliceQuadratic_graph_coefficients G e₀ c W).symm
  rw [hP]
  exact finiteCharacteristic_sliceQuadratic_eq_rademacher
    (graphSliceConstant G e₀ c) (graphSliceLinear G c)
      (graphSliceMatrix G) t

open Classical in
lemma norm_centeredGraphCharacteristic_eq_graphRademacher
    {n : ℕ} (G : SimpleGraph (Fin n)) (e₀ : ℝ) (c : Fin n → ℝ)
    (t : ℝ) :
    ‖GraphQuadratic.centeredGraphCharacteristic G e₀ c t‖ =
      ‖Fourier.finExpectation (Fin n → Bool) (fun x ↦
        Complex.exp (((t * BooleanSlices.rademacherQuadratic
          (graphSliceConstant G e₀ c) (graphSliceLinear G c)
          (graphSliceMatrix G) x : ℝ) : ℂ) * Complex.I))‖ := by
  rw [GraphQuadratic.centeredGraphCharacteristic,
    finiteCharacteristic_perturbedEdgePolynomial_eq_graphRademacher]
  rw [norm_mul, Complex.norm_exp]
  simp

open ComplexConjugate in
lemma finiteCharacteristic_neg {Ω : Type*} [Fintype Ω]
    (X : Ω → ℝ) (t : ℝ) :
    BooleanSlices.finiteCharacteristic X (-t) =
      conj (BooleanSlices.finiteCharacteristic X t) := by
  unfold BooleanSlices.finiteCharacteristic
  rw [Fintype.expect_eq_sum_div_card, Fintype.expect_eq_sum_div_card]
  rw [map_div₀, map_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro x hx
  rw [← Complex.exp_conj]
  congr 1
  push_cast
  simp
  simp

open ComplexConjugate in
lemma norm_centeredGraphCharacteristic_neg
    {n : ℕ} (G : SimpleGraph (Fin n)) (e₀ : ℝ) (c : Fin n → ℝ)
    (t : ℝ) :
    ‖GraphQuadratic.centeredGraphCharacteristic G e₀ c (-t)‖ =
      ‖GraphQuadratic.centeredGraphCharacteristic G e₀ c t‖ := by
  classical
  rw [GraphQuadratic.centeredGraphCharacteristic,
    GraphQuadratic.centeredGraphCharacteristic,
    finiteCharacteristic_neg]
  rw [show Complex.exp (-((((-t) * Probability.expectation (1 / 2 : ℝ)
      (Probability.perturbedEdgePolynomial G e₀ c) : ℝ) : ℂ) * Complex.I)) =
      conj (Complex.exp (-((((t) * Probability.expectation (1 / 2 : ℝ)
      (Probability.perturbedEdgePolynomial G e₀ c) : ℝ) : ℂ) * Complex.I))) by
    rw [← Complex.exp_conj]
    congr 1
    push_cast
    simp]
  rw [← map_mul]
  exact Complex.norm_conj _

/-- Full-cube cancellation obtained by conditioning on the LCD coordinates
and paying the exact Hoeffding exceptional probability. -/
theorem norm_centeredGraphCharacteristic_le_of_LCD_budget
    {n : ℕ} (G : SimpleGraph (Fin n)) (e₀ : ℝ) (c : Fin n → ℝ)
    (I : Finset (Fin n)) (L t u D : ℝ) (r : ℕ)
    (hn : 0 < n) (ht : 0 < t) (hu : 0 < u) (hD : 0 ≤ D)
    (hnorm : 0 < RLCD.euclidNorm (RLCD.restrict
      (graphEffectiveLinear G c) I))
    (hbelow :
      t * RLCD.euclidNorm (RLCD.restrict
        (graphEffectiveLinear G c) I) / (2 * Real.pi) <
        RLCD.LCD L (RLCD.normalizedRestrict
          (graphEffectiveLinear G c) I))
    (hbudget :
      Real.sqrt (((((2 ^ (r + 1) - 1) * 2 : ℕ) : ℝ)) + D) +
          |t| * Real.sqrt I.card * u / Real.pi ≤
        L * Real.sqrt (RLCD.logPlus
          ((t * RLCD.euclidNorm (RLCD.restrict
            (graphEffectiveLinear G c) I) / (2 * Real.pi)) / L))) :
    ‖centeredGraphCharacteristic G e₀ c t‖ ≤
      ((∑ j : Fin (2 ^ (r + 1)),
        (|t| * (I.card : ℝ) ^ 2 / 8) ^ j.val / j.val.factorial) *
          Real.exp (-D) +
        (9 ^ bonamiExponent 2 r *
          (t ^ 2 * (I.card : ℝ) ^ 2 / 32) ^ (2 ^ r)) /
          (2 ^ (r + 1) - 1).factorial) +
        2 * (I.card : ℝ) * Real.exp (-8 * u ^ 2 / n) := by
  let B : ℝ :=
    (∑ j : Fin (2 ^ (r + 1)),
      (|t| * (I.card : ℝ) ^ 2 / 8) ^ j.val / j.val.factorial) *
        Real.exp (-D) +
      (9 ^ bonamiExponent 2 r *
        (t ^ 2 * (I.card : ℝ) ^ 2 / 32) ^ (2 ^ r)) /
        (2 ^ (r + 1) - 1).factorial
  have hB : 0 ≤ B := by
    dsimp only [B]
    positivity
  have hfull := norm_graphRademacherCharacteristic_le_of_good
    G e₀ c I t u B hn hu hB (by
      intro z hz
      apply norm_graphConditionedCharacteristic_le_of_LCD_budget
        G c I z L t u D r ht hu.le hD hnorm hbelow
      · intro i
        exact (hz i).le
      · exact hbudget)
  rw [norm_centeredGraphCharacteristic_eq_graphRademacher G e₀ c t]
  exact hfull

theorem graphEffectiveLinear_restrict_norm_lower
    {n : ℕ} (G : SimpleGraph (Fin n)) (c : Fin n → ℝ)
    (I : Finset (Fin n)) {a : ℝ} (ha : 0 ≤ a) (hI : 0 < I.card)
    (hc : ∀ i, 0 ≤ c i)
    (hedge : a * (I.card : ℝ) ^ 2 ≤ (AKSGraph.edgeCount G I : ℝ)) :
    a * (I.card : ℝ) ^ ((3 : ℝ) / 2) ≤
      RLCD.euclidNorm (RLCD.restrict (graphEffectiveLinear G c) I) := by
  have hmass := graphEffectiveLinear_restrict_sq_lower
    G c I ha hI hc hedge
  have hnormSq :
      RLCD.euclidNorm (RLCD.restrict (graphEffectiveLinear G c) I) ^ 2 =
        ∑ i : I, graphEffectiveLinear G c i.1 ^ 2 := by
    rw [RLCD.euclidNorm, Real.sq_sqrt (Finset.sum_nonneg fun i hi ↦ sq_nonneg _)]
    rfl
  have hscaleSq :
      ((I.card : ℝ) ^ ((3 : ℝ) / 2)) ^ 2 = (I.card : ℝ) ^ 3 :=
    GraphQuadratic.n_rpow_three_halves_sq I.card
  apply (sq_le_sq₀ (mul_nonneg ha (Real.rpow_nonneg (by positivity) _))
    (RLCD.euclidNorm_nonneg _)).mp
  rw [mul_pow, hscaleSq, hnormSq]
  exact hmass

theorem graphEffectiveLinear_restrict_norm_upper
    {n : ℕ} (G : SimpleGraph (Fin n)) (c : Fin n → ℝ)
    (I : Finset (Fin n)) (H : ℝ) (hH : 0 ≤ H)
    (hcNonneg : ∀ i, 0 ≤ c i) (hcUpper : ∀ i, c i ≤ H * n) :
    RLCD.euclidNorm (RLCD.restrict (graphEffectiveLinear G c) I) ≤
      Real.sqrt I.card * ((H + 1 / 2) * n) := by
  classical
  letI (i : Fin n) : Fintype ↑(G.neighborSet i) :=
    Subtype.fintype (Membership.mem (G.neighborSet i))
  have hu : 0 ≤ (H + 1 / 2) * (n : ℝ) := by positivity
  have hpoint (i : I) :
      |RLCD.restrict (graphEffectiveLinear G c) I i| ≤
        (H + 1 / 2) * n := by
    have hdegNat : G.degree i.1 ≤ n :=
      Nat.le_of_lt (by simpa using G.degree_lt_card_verts i.1)
    have hdeg : (G.degree i.1 : ℝ) ≤ n := by exact_mod_cast hdegNat
    have hnonneg : 0 ≤ graphEffectiveLinear G c i.1 := by
      unfold graphEffectiveLinear
      exact add_nonneg (hcNonneg i.1)
        (div_nonneg (by positivity) (by norm_num))
    dsimp only [RLCD.restrict]
    rw [abs_of_nonneg hnonneg]
    dsimp only [graphEffectiveLinear]
    have hci := hcUpper i.1
    nlinarith
  have hbase := euclidNorm_mul_le_abs_mul_sqrt_card_mul
    (1 : ℝ) (RLCD.restrict (graphEffectiveLinear G c) I) hu hpoint
  simpa only [abs_one, one_mul, Fintype.card_coe] using hbase

lemma exists_two_pow_between (x : ℝ) (hx : 1 ≤ x) :
    ∃ r : ℕ, x ≤ ((2 ^ r : ℕ) : ℝ) ∧ ((2 ^ r : ℕ) : ℝ) < 4 * x := by
  let N := Nat.ceil x
  have hNpos : 0 < N := by
    dsimp only [N]
    rw [Nat.ceil_pos]
    linarith
  have hNpow : N ≤ 2 ^ N := N.lt_two_pow_self.le
  have hex : ∃ r : ℕ, N ≤ 2 ^ r := ⟨N, hNpow⟩
  let r := Nat.find hex
  have hr := Nat.find_spec hex
  refine ⟨r, ?_, ?_⟩
  · exact (Nat.le_ceil x).trans (by exact_mod_cast hr)
  · cases hrEq : r with
    | zero =>
        norm_num
        linarith
    | succ s =>
        have hfind : Nat.find hex = s + 1 := by
          simpa [r] using hrEq
        have hnot : ¬ N ≤ 2 ^ s := by
          exact Nat.find_min hex (by omega : s < Nat.find hex)
        have hsN : 2 ^ s < N := Nat.lt_of_not_ge hnot
        have hNlt : (N : ℝ) < x + 1 := by
          dsimp only [N]
          exact Nat.ceil_lt_add_one (by linarith)
        have hcast : ((2 ^ s : ℕ) : ℝ) < N := by exact_mod_cast hsN
        have hN2x : (N : ℝ) < 2 * x := by linarith
        simp only [pow_succ, Nat.cast_mul, Nat.cast_ofNat]
        nlinarith

lemma regularizationCard_cast_lower {n : ℕ} (γ : ℝ) :
    BooleanSlices.scale n (1 - γ) ≤ (RLCD.regularizationCard n γ : ℝ) := by
  exact Nat.le_ceil _

lemma regularizationCard_le_self {n : ℕ} {γ : ℝ}
    (hn : 1 ≤ n) (hγ0 : 0 ≤ γ) : RLCD.regularizationCard n γ ≤ n := by
  rw [RLCD.regularizationCard, Nat.ceil_le]
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  calc
    BooleanSlices.scale n (1 - γ) ≤ BooleanSlices.scale n 1 :=
      BooleanSlices.scale_mono_exponent hn (by linarith)
    _ = (n : ℝ) := by simp [BooleanSlices.scale]

lemma regularizationCard_cast_upper_two_scale {n : ℕ} {γ : ℝ}
    (hn : 1 ≤ n) (hγ1 : γ ≤ 1) :
    (RLCD.regularizationCard n γ : ℝ) <
      2 * BooleanSlices.scale n (1 - γ) := by
  have hpos : 0 < BooleanSlices.scale n (1 - γ) :=
    BooleanSlices.scale_pos (lt_of_lt_of_le Nat.zero_lt_one hn) _
  have hceil : (RLCD.regularizationCard n γ : ℝ) <
      BooleanSlices.scale n (1 - γ) + 1 := by
    unfold RLCD.regularizationCard
    exact Nat.ceil_lt_add_one (Real.rpow_nonneg (by positivity) _)
  have hone : 1 ≤ BooleanSlices.scale n (1 - γ) := by
    exact Real.one_le_rpow (by exact_mod_cast hn) (by linarith)
  linarith

lemma sqrt_regularizationCard_le_sqrt_two_mul_scale {n : ℕ} {γ : ℝ}
    (hn : 1 ≤ n) (hγ1 : γ ≤ 1) :
    Real.sqrt (RLCD.regularizationCard n γ) ≤
      Real.sqrt 2 * BooleanSlices.scale n ((1 - γ) / 2) := by
  have hcard := (regularizationCard_cast_upper_two_scale (γ := γ) hn hγ1).le
  have hsqrt := Real.sqrt_le_sqrt hcard
  have hnpos : 0 < n := lt_of_lt_of_le Nat.zero_lt_one hn
  calc
    Real.sqrt (RLCD.regularizationCard n γ) ≤
        Real.sqrt (2 * BooleanSlices.scale n (1 - γ)) := hsqrt
    _ = Real.sqrt 2 * Real.sqrt (BooleanSlices.scale n (1 - γ)) := by
      rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2)]
    _ = Real.sqrt 2 * BooleanSlices.scale n ((1 - γ) / 2) := by
      congr 1
      calc
        Real.sqrt (BooleanSlices.scale n (1 - γ)) =
            (BooleanSlices.scale n (1 - γ)) ^ ((1 : ℝ) / 2) :=
          Real.sqrt_eq_rpow _
        _ = Real.rpow (n : ℝ) ((1 - γ) * ((1 : ℝ) / 2)) := by
          change Real.rpow (Real.rpow (n : ℝ) (1 - γ)) ((1 : ℝ) / 2) = _
          exact (Real.rpow_mul (by positivity : (0 : ℝ) ≤ n)
            (1 - γ) ((1 : ℝ) / 2)).symm
        _ = BooleanSlices.scale n ((1 - γ) / 2) := by
          congr 1
          ring

lemma logPlus_mono_of_pos {x y : ℝ} (hx : 0 < x) (hxy : x ≤ y) :
    RLCD.logPlus x ≤ RLCD.logPlus y := by
  unfold RLCD.logPlus
  exact max_le_max le_rfl (Real.log_le_log hx hxy)

/-- Select the coordinate set attaining the regularized LCD, using uniform
lower and upper Euclidean bounds to discharge its scale conditions. -/
theorem exists_coordinateSet_centeredGraphCharacteristic_le_of_bounds
    {n k : ℕ} (G : SimpleGraph (Fin n)) (e₀ : ℝ) (c : Fin n → ℝ)
    (L t u D Rlo Rup : ℝ) (r : ℕ)
    (hk : k ≤ n) (hn : 0 < n) (hL : 0 < L) (ht : 0 < t)
    (hu : 0 < u) (hD : 0 ≤ D) (hRlo : 0 < Rlo)
    (hnormlo : ∀ I : Finset (Fin n), I.card = k →
      Rlo ≤ RLCD.euclidNorm (RLCD.restrict (graphEffectiveLinear G c) I))
    (hnormup : ∀ I : Finset (Fin n), I.card = k →
      RLCD.euclidNorm (RLCD.restrict (graphEffectiveLinear G c) I) ≤ Rup)
    (hbelow : t * Rup / (2 * Real.pi) <
      RLCD.regularizedLCDCard L k (graphEffectiveLinear G c))
    (hbudget :
      Real.sqrt (((((2 ^ (r + 1) - 1) * 2 : ℕ) : ℝ)) + D) +
          t * Real.sqrt k * u / Real.pi ≤
        L * Real.sqrt (RLCD.logPlus ((t * Rlo / (2 * Real.pi)) / L))) :
    ∃ I : Finset (Fin n), I.card = k ∧
      ‖centeredGraphCharacteristic G e₀ c t‖ ≤
        ((∑ j : Fin (2 ^ (r + 1)),
          (t * (k : ℝ) ^ 2 / 8) ^ j.val / j.val.factorial) *
            Real.exp (-D) +
          (9 ^ bonamiExponent 2 r *
            (t ^ 2 * (k : ℝ) ^ 2 / 32) ^ (2 ^ r)) /
            (2 ^ (r + 1) - 1).factorial) +
          2 * (k : ℝ) * Real.exp (-8 * u ^ 2 / n) := by
  obtain ⟨I, hIset, hmax⟩ :=
    RLCD.exists_coordinateSet_eq_regularizedLCDCard
      L (graphEffectiveLinear G c) hk
  have hI : I.card = k := RLCD.mem_coordinateSets.mp hIset
  have hnormloI := hnormlo I hI
  have hnormupI := hnormup I hI
  have hnormI : 0 < RLCD.euclidNorm
      (RLCD.restrict (graphEffectiveLinear G c) I) :=
    hRlo.trans_le hnormloI
  have hthetaUpper :
      t * RLCD.euclidNorm (RLCD.restrict
        (graphEffectiveLinear G c) I) / (2 * Real.pi) ≤
        t * Rup / (2 * Real.pi) := by
    gcongr
  have hbelowI :
      t * RLCD.euclidNorm (RLCD.restrict
        (graphEffectiveLinear G c) I) / (2 * Real.pi) <
        RLCD.LCD L (RLCD.normalizedRestrict
          (graphEffectiveLinear G c) I) := by
    rw [← hmax]
    exact hthetaUpper.trans_lt hbelow
  have hx : 0 < (t * Rlo / (2 * Real.pi)) / L := by positivity
  have harg : (t * Rlo / (2 * Real.pi)) / L ≤
      (t * RLCD.euclidNorm (RLCD.restrict
        (graphEffectiveLinear G c) I) / (2 * Real.pi)) / L := by
    gcongr
  have hlog := logPlus_mono_of_pos hx harg
  have hthreshold :
      L * Real.sqrt (RLCD.logPlus ((t * Rlo / (2 * Real.pi)) / L)) ≤
        L * Real.sqrt (RLCD.logPlus
          ((t * RLCD.euclidNorm (RLCD.restrict
            (graphEffectiveLinear G c) I) / (2 * Real.pi)) / L)) :=
    mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hlog) hL.le
  have hbudgetI :
      Real.sqrt (((((2 ^ (r + 1) - 1) * 2 : ℕ) : ℝ)) + D) +
          |t| * Real.sqrt I.card * u / Real.pi ≤
        L * Real.sqrt (RLCD.logPlus
          ((t * RLCD.euclidNorm (RLCD.restrict
            (graphEffectiveLinear G c) I) / (2 * Real.pi)) / L)) := by
    rw [abs_of_pos ht, hI]
    exact hbudget.trans hthreshold
  refine ⟨I, hI, ?_⟩
  have hfull := norm_centeredGraphCharacteristic_le_of_LCD_budget
    G e₀ c I L t u D r hn ht hu hD hnormI hbelowI hbudgetI
  simpa only [abs_of_pos ht, hI] using hfull


lemma scale_rpow_three_halves {n : ℕ} (hn : 0 < n) (a : ℝ) :
    (BooleanSlices.scale n a) ^ ((3 : ℝ) / 2) =
      BooleanSlices.scale n (3 * a / 2) := by
  unfold BooleanSlices.scale
  change Real.rpow (Real.rpow (n : ℝ) a) ((3 : ℝ) / 2) = _
  calc
    Real.rpow (Real.rpow (n : ℝ) a) ((3 : ℝ) / 2) =
        Real.rpow (n : ℝ) (a * ((3 : ℝ) / 2)) :=
      (Real.rpow_mul (by positivity : (0 : ℝ) ≤ n) a ((3 : ℝ) / 2)).symm
    _ = Real.rpow (n : ℝ) (3 * a / 2) := by congr 1 <;> ring

lemma sqrt_scale {n : ℕ} (hn : 0 < n) (a : ℝ) :
    Real.sqrt (BooleanSlices.scale n a) =
      BooleanSlices.scale n (a / 2) := by
  rw [Real.sqrt_eq_rpow]
  unfold BooleanSlices.scale
  change Real.rpow (Real.rpow (n : ℝ) a) ((1 : ℝ) / 2) = _
  calc
    Real.rpow (Real.rpow (n : ℝ) a) ((1 : ℝ) / 2) =
        Real.rpow (n : ℝ) (a * ((1 : ℝ) / 2)) :=
      (Real.rpow_mul (by positivity : (0 : ℝ) ≤ n) a ((1 : ℝ) / 2)).symm
    _ = Real.rpow (n : ℝ) (a / 2) := by congr 1 <;> ring

lemma normalized_lcd_theta_upper
    {n : ℕ} {gamma b H alpha sigma t lcd k : ℝ}
    (hn : 0 < n) (hgamma0 : 0 ≤ gamma) (hb : 0 < b)
    (hH : 0 ≤ H) (hsigma : b / 2 * BooleanSlices.scale n (3 / 2) ≤ sigma)
    (hk0 : 0 ≤ k) (hk : k ≤ 2 * BooleanSlices.scale n (1 - gamma))
    (ht : 0 ≤ t)
    (htupper : t ≤ alpha * BooleanSlices.scale n (gamma / 2) * lcd)
    (hlcd : 0 < lcd) (halpha : 0 ≤ alpha)
    (halphaSmall : alpha * (Real.sqrt 2 * (H + 1 / 2) / (Real.pi * b)) ≤ 1 / 2) :
    (t / sigma) * (Real.sqrt k * ((H + 1 / 2) * n)) /
        (2 * Real.pi) < lcd := by
  have hbasePos : 0 < b / 2 * BooleanSlices.scale n (3 / 2) :=
    mul_pos (div_pos hb (by norm_num)) (BooleanSlices.scale_pos hn _)
  have hsigmaPos : 0 < sigma := hbasePos.trans_le hsigma
  have hsqrtk : Real.sqrt k ≤
      Real.sqrt 2 * BooleanSlices.scale n ((1 - gamma) / 2) := by
    calc
      Real.sqrt k ≤ Real.sqrt (2 * BooleanSlices.scale n (1 - gamma)) :=
        Real.sqrt_le_sqrt hk
      _ = Real.sqrt 2 * Real.sqrt (BooleanSlices.scale n (1 - gamma)) := by
        rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2)]
      _ = Real.sqrt 2 * BooleanSlices.scale n ((1 - gamma) / 2) := by
        rw [sqrt_scale hn]
  have hsigInv : 1 / sigma ≤
      (2 / b) / BooleanSlices.scale n (3 / 2) := by
    calc
      1 / sigma ≤ 1 / (b / 2 * BooleanSlices.scale n (3 / 2)) :=
        one_div_le_one_div_of_le hbasePos hsigma
      _ = (2 / b) / BooleanSlices.scale n (3 / 2) := by
        field_simp [ne_of_gt hb, ne_of_gt (BooleanSlices.scale_pos hn _)]
  have hraw : t / sigma ≤
      t * ((2 / b) / BooleanSlices.scale n (3 / 2)) := by
    simpa only [div_eq_mul_inv, one_mul] using
      mul_le_mul_of_nonneg_left hsigInv ht
  have hscale :
      BooleanSlices.scale n (gamma / 2) *
          BooleanSlices.scale n ((1 - gamma) / 2) * (n : ℝ) /
          BooleanSlices.scale n (3 / 2) = 1 := by
    rw [show (n : ℝ) = BooleanSlices.scale n 1 by
      simp [BooleanSlices.scale]]
    rw [BooleanSlices.scale_mul hn, BooleanSlices.scale_mul hn]
    rw [show BooleanSlices.scale n (gamma / 2 + (1 - gamma) / 2 + 1) =
        BooleanSlices.scale n (3 / 2) by congr 1 <;> ring]
    field_simp [ne_of_gt (BooleanSlices.scale_pos hn (3 / 2))]
  calc
    (t / sigma) * (Real.sqrt k * ((H + 1 / 2) * n)) /
          (2 * Real.pi) ≤
        (t * ((2 / b) / BooleanSlices.scale n (3 / 2))) *
          (Real.sqrt k * ((H + 1 / 2) * n)) / (2 * Real.pi) := by
      gcongr
    _ ≤ (alpha * BooleanSlices.scale n (gamma / 2) * lcd) *
          ((2 / b) / BooleanSlices.scale n (3 / 2)) *
          (Real.sqrt k * ((H + 1 / 2) * n)) / (2 * Real.pi) := by
      have hq : 0 ≤ (2 / b) / BooleanSlices.scale n (3 / 2) :=
        div_nonneg (div_nonneg (by norm_num) hb.le)
          (BooleanSlices.scale_nonneg n _)
      gcongr
    _ ≤ (alpha * BooleanSlices.scale n (gamma / 2) * lcd) *
          ((2 / b) / BooleanSlices.scale n (3 / 2)) *
          (Real.sqrt 2 * BooleanSlices.scale n ((1 - gamma) / 2) *
            ((H + 1 / 2) * n)) / (2 * Real.pi) := by
      have hdiv : 0 ≤ (2 / b) / BooleanSlices.scale n (3 / 2) :=
        div_nonneg (div_nonneg (by norm_num) hb.le)
          (BooleanSlices.scale_nonneg n _)
      have hq : 0 ≤ alpha * BooleanSlices.scale n (gamma / 2) * lcd *
          ((2 / b) / BooleanSlices.scale n (3 / 2)) :=
        mul_nonneg (mul_nonneg (mul_nonneg halpha
          (BooleanSlices.scale_nonneg n _)) hlcd.le) hdiv
      gcongr
    _ = alpha * (Real.sqrt 2 * (H + 1 / 2) / (Real.pi * b)) * lcd *
          (BooleanSlices.scale n (gamma / 2) *
            BooleanSlices.scale n ((1 - gamma) / 2) * (n : ℝ) /
              BooleanSlices.scale n (3 / 2)) := by ring
    _ = alpha * (Real.sqrt 2 * (H + 1 / 2) / (Real.pi * b)) * lcd := by
      rw [hscale, mul_one]
    _ ≤ (1 / 2) * lcd := mul_le_mul_of_nonneg_right halphaSmall hlcd.le
    _ < lcd := by linarith

lemma normalized_lcd_theta_lower
    {n : ℕ} {gamma a R L sigma t k : ℝ}
    (hn : 0 < n) (ha : 0 < a) (hR : 0 < R) (hL : 0 < L)
    (hsigmaPos : 0 < sigma)
    (hsigma : sigma ≤ R * BooleanSlices.scale n (3 / 2))
    (ht : BooleanSlices.scale n (2 * gamma) ≤ t)
    (hk : BooleanSlices.scale n (1 - gamma) ≤ k) :
    (a / (2 * Real.pi * R * L)) * BooleanSlices.scale n (gamma / 2) ≤
      (((t / sigma) * (a * k ^ ((3 : ℝ) / 2))) / (2 * Real.pi)) / L := by
  have hRscale : 0 < R * BooleanSlices.scale n (3 / 2) :=
    mul_pos hR (BooleanSlices.scale_pos hn _)
  have hinv : 1 / (R * BooleanSlices.scale n (3 / 2)) ≤ 1 / sigma :=
    one_div_le_one_div_of_le hsigmaPos hsigma
  have hraw : BooleanSlices.scale n (2 * gamma) /
      (R * BooleanSlices.scale n (3 / 2)) ≤ t / sigma := by
    have hinv0 : 0 ≤ 1 / (R * BooleanSlices.scale n (3 / 2)) := by
      exact one_div_nonneg.mpr hRscale.le
    have ht0 : 0 ≤ t := (BooleanSlices.scale_nonneg n _).trans ht
    have hmul : BooleanSlices.scale n (2 * gamma) *
        (1 / (R * BooleanSlices.scale n (3 / 2))) ≤ t * (1 / sigma) :=
      mul_le_mul ht hinv hinv0 ht0
    simpa [div_eq_mul_inv] using hmul
  have hkpow : BooleanSlices.scale n (3 * (1 - gamma) / 2) ≤
      k ^ ((3 : ℝ) / 2) := by
    rw [← scale_rpow_three_halves hn]
    exact Real.rpow_le_rpow (BooleanSlices.scale_nonneg n _) hk (by norm_num)
  have hscale :
      (BooleanSlices.scale n (2 * gamma) *
        BooleanSlices.scale n (3 * (1 - gamma) / 2)) /
          BooleanSlices.scale n (3 / 2) =
          BooleanSlices.scale n (gamma / 2) := by
    rw [BooleanSlices.scale_mul hn]
    have hspos := BooleanSlices.scale_pos hn (3 / 2)
    rw [show 2 * gamma + 3 * (1 - gamma) / 2 = gamma / 2 + 3 / 2 by ring]
    rw [← BooleanSlices.scale_mul hn]
    field_simp [ne_of_gt hspos]
  calc
    (a / (2 * Real.pi * R * L)) * BooleanSlices.scale n (gamma / 2) =
        (a / (2 * Real.pi * R * L)) *
          ((BooleanSlices.scale n (2 * gamma) *
            BooleanSlices.scale n (3 * (1 - gamma) / 2)) /
              BooleanSlices.scale n (3 / 2)) := by rw [hscale]
    _ =
        ((BooleanSlices.scale n (2 * gamma) /
            (R * BooleanSlices.scale n (3 / 2))) *
          (a * BooleanSlices.scale n (3 * (1 - gamma) / 2)) /
            (2 * Real.pi)) / L := by ring
    _ ≤ (((t / sigma) * (a * k ^ ((3 : ℝ) / 2))) /
          (2 * Real.pi)) / L := by
      have haScale : 0 ≤ a * BooleanSlices.scale n
          (3 * (1 - gamma) / 2) :=
        mul_nonneg ha.le (BooleanSlices.scale_nonneg n _)
      have hraw0 : 0 ≤ t / sigma :=
        div_nonneg ((BooleanSlices.scale_nonneg n _).trans ht) hsigmaPos.le
      gcongr

lemma normalized_frequency_upper
    {n : ℕ} {b sigma t A q : ℝ}
    (hn : 0 < n) (hb : 0 < b)
    (hsigma : b / 2 * BooleanSlices.scale n (3 / 2) ≤ sigma)
    (ht0 : 0 ≤ t) (hA : 0 ≤ A)
    (ht : t ≤ A * BooleanSlices.scale n q) :
    t / sigma ≤ (2 * A / b) * BooleanSlices.scale n (q - 3 / 2) := by
  have hbasePos : 0 < b / 2 * BooleanSlices.scale n (3 / 2) :=
    mul_pos (div_pos hb (by norm_num)) (BooleanSlices.scale_pos hn _)
  have hsigInv : 1 / sigma ≤
      (2 / b) / BooleanSlices.scale n (3 / 2) := by
    calc
      1 / sigma ≤ 1 / (b / 2 * BooleanSlices.scale n (3 / 2)) :=
        one_div_le_one_div_of_le hbasePos hsigma
      _ = (2 / b) / BooleanSlices.scale n (3 / 2) := by
        field_simp [ne_of_gt hb, ne_of_gt (BooleanSlices.scale_pos hn _)]
  have hraw : t / sigma ≤
      (A * BooleanSlices.scale n q) *
        ((2 / b) / BooleanSlices.scale n (3 / 2)) := by
    have hsigmaPos : 0 < sigma := hbasePos.trans_le hsigma
    have hinv0 : 0 ≤ 1 / sigma := one_div_nonneg.mpr hsigmaPos.le
    have hAupper0 : 0 ≤ A * BooleanSlices.scale n q :=
      mul_nonneg hA (BooleanSlices.scale_nonneg n _)
    have hmul := mul_le_mul ht hsigInv
      hinv0 hAupper0
    simpa only [div_eq_mul_inv, one_mul] using hmul
  calc
    t / sigma ≤ (A * BooleanSlices.scale n q) *
        ((2 / b) / BooleanSlices.scale n (3 / 2)) := hraw
    _ = (2 * A / b) * BooleanSlices.scale n (q - 3 / 2) := by
      rw [show BooleanSlices.scale n q =
          BooleanSlices.scale n (q - 3 / 2) *
            BooleanSlices.scale n (3 / 2) by
        rw [BooleanSlices.scale_mul hn]
        congr 1
        ring]
      field_simp [ne_of_gt hb, ne_of_gt (BooleanSlices.scale_pos hn _)]

lemma normalized_cross_perturbation_upper
    {n : ℕ} {gamma b alpha sigma t k : ℝ}
    (hn : 0 < n) (hb : 0 < b) (halpha : 0 ≤ alpha)
    (hsigma : b / 2 * BooleanSlices.scale n (3 / 2) ≤ sigma)
    (ht0 : 0 ≤ t)
    (ht : t ≤ alpha * BooleanSlices.scale n (1 / 2 + gamma / 8))
    (hk0 : 0 ≤ k)
    (hk : k ≤ 2 * BooleanSlices.scale n (1 - gamma)) :
    (t / sigma) * Real.sqrt k *
        BooleanSlices.scale n (1 / 2 + gamma / 8) / Real.pi ≤
      (2 * alpha * Real.sqrt 2 / (Real.pi * b)) *
        BooleanSlices.scale n (-gamma / 4) := by
  have hraw := normalized_frequency_upper hn hb hsigma ht0 halpha ht
  have hsqrtk : Real.sqrt k ≤
      Real.sqrt 2 * BooleanSlices.scale n ((1 - gamma) / 2) := by
    calc
      Real.sqrt k ≤ Real.sqrt (2 * BooleanSlices.scale n (1 - gamma)) :=
        Real.sqrt_le_sqrt hk
      _ = Real.sqrt 2 * Real.sqrt (BooleanSlices.scale n (1 - gamma)) := by
        rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2)]
      _ = Real.sqrt 2 * BooleanSlices.scale n ((1 - gamma) / 2) := by
        rw [sqrt_scale hn]
  calc
    (t / sigma) * Real.sqrt k *
        BooleanSlices.scale n (1 / 2 + gamma / 8) / Real.pi ≤
      ((2 * alpha / b) * BooleanSlices.scale n
          ((1 / 2 + gamma / 8) - 3 / 2)) *
        (Real.sqrt 2 * BooleanSlices.scale n ((1 - gamma) / 2)) *
        BooleanSlices.scale n (1 / 2 + gamma / 8) / Real.pi := by
      have hscale0 : 0 ≤ BooleanSlices.scale n (1 / 2 + gamma / 8) :=
        BooleanSlices.scale_nonneg n _
      have hrawUpper0 : 0 ≤ (2 * alpha / b) *
          BooleanSlices.scale n ((1 / 2 + gamma / 8) - 3 / 2) :=
        mul_nonneg (div_nonneg (mul_nonneg (by norm_num) halpha) hb.le)
          (BooleanSlices.scale_nonneg n _)
      gcongr
    _ = (2 * alpha * Real.sqrt 2 / (Real.pi * b)) *
        BooleanSlices.scale n (-gamma / 4) := by
      calc
        ((2 * alpha / b) * BooleanSlices.scale n
            ((1 / 2 + gamma / 8) - 3 / 2)) *
          (Real.sqrt 2 * BooleanSlices.scale n ((1 - gamma) / 2)) *
          BooleanSlices.scale n (1 / 2 + gamma / 8) / Real.pi =
            (2 * alpha * Real.sqrt 2 / (Real.pi * b)) *
              (BooleanSlices.scale n ((1 / 2 + gamma / 8) - 3 / 2) *
                BooleanSlices.scale n ((1 - gamma) / 2) *
                BooleanSlices.scale n (1 / 2 + gamma / 8)) := by ring
        _ = (2 * alpha * Real.sqrt 2 / (Real.pi * b)) *
            BooleanSlices.scale n (-gamma / 4) := by
          rw [BooleanSlices.scale_mul hn, BooleanSlices.scale_mul hn]
          congr 1
          congr 1
          ring

lemma normalized_taylor_base_upper
    {n : ℕ} {gamma b alpha sigma t k : ℝ}
    (hn : 0 < n) (hb : 0 < b) (halpha : 0 ≤ alpha)
    (hsigma : b / 2 * BooleanSlices.scale n (3 / 2) ≤ sigma)
    (ht0 : 0 ≤ t)
    (ht : t ≤ alpha * BooleanSlices.scale n (1 / 2 + gamma / 8))
    (hk0 : 0 ≤ k)
    (hk : k ≤ 2 * BooleanSlices.scale n (1 - gamma)) :
    (t / sigma) ^ 2 * k ^ 2 / 32 ≤
      (alpha ^ 2 / (2 * b ^ 2)) *
        BooleanSlices.scale n (-7 * gamma / 4) := by
  have hraw := normalized_frequency_upper hn hb hsigma ht0 halpha ht
  have hraw0 : 0 ≤ t / sigma := by
    have hsig0 : 0 ≤ sigma :=
      (mul_nonneg (div_nonneg hb.le (by norm_num))
        (BooleanSlices.scale_nonneg n _)).trans hsigma
    exact div_nonneg ht0 hsig0
  have hrawUpper0 : 0 ≤ (2 * alpha / b) *
      BooleanSlices.scale n ((1 / 2 + gamma / 8) - 3 / 2) :=
    mul_nonneg (div_nonneg (mul_nonneg (by norm_num) halpha) hb.le)
      (BooleanSlices.scale_nonneg n _)
  have hrawSq := (sq_le_sq₀ hraw0 hrawUpper0).2 hraw
  have hkUpper0 : 0 ≤ 2 * BooleanSlices.scale n (1 - gamma) :=
    mul_nonneg (by norm_num) (BooleanSlices.scale_nonneg n _)
  have hkSq := (sq_le_sq₀ hk0 hkUpper0).2 hk
  calc
    (t / sigma) ^ 2 * k ^ 2 / 32 ≤
        (((2 * alpha / b) * BooleanSlices.scale n
          ((1 / 2 + gamma / 8) - 3 / 2)) ^ 2 *
          (2 * BooleanSlices.scale n (1 - gamma)) ^ 2) / 32 := by
      gcongr
    _ = (alpha ^ 2 / (2 * b ^ 2)) *
        BooleanSlices.scale n (-7 * gamma / 4) := by
      rw [mul_pow, mul_pow, BooleanSlices.scale_sq (Nat.zero_le n),
        BooleanSlices.scale_sq (Nat.zero_le n)]
      calc
        (2 * alpha / b) ^ 2 *
              BooleanSlices.scale n (((1 / 2 + gamma / 8) - 3 / 2) * 2) *
              (2 ^ 2 * BooleanSlices.scale n ((1 - gamma) * 2)) / 32 =
            (alpha ^ 2 / (2 * b ^ 2)) *
              (BooleanSlices.scale n (((1 / 2 + gamma / 8) - 3 / 2) * 2) *
                BooleanSlices.scale n ((1 - gamma) * 2)) := by
          field_simp [ne_of_gt hb]
          ring
        _ = (alpha ^ 2 / (2 * b ^ 2)) *
            BooleanSlices.scale n (-7 * gamma / 4) := by
          rw [BooleanSlices.scale_mul hn]
          congr 1
          congr 1
          ring

lemma normalized_taylor_linear_base_upper
    {n : ℕ} {gamma b alpha sigma t k : ℝ}
    (hn : 1 ≤ n) (hgamma : 0 ≤ gamma) (hb : 0 < b)
    (halpha : 0 ≤ alpha)
    (hsigma : b / 2 * BooleanSlices.scale n (3 / 2) ≤ sigma)
    (ht0 : 0 ≤ t)
    (ht : t ≤ alpha * BooleanSlices.scale n (1 / 2 + gamma / 8))
    (hk0 : 0 ≤ k)
    (hk : k ≤ 2 * BooleanSlices.scale n (1 - gamma)) :
    (t / sigma) * k ^ 2 / 8 ≤ (alpha / b) * n := by
  have hnpos : 0 < n := lt_of_lt_of_le Nat.zero_lt_one hn
  have hraw := normalized_frequency_upper hnpos hb hsigma ht0 halpha ht
  have hkUpper0 : 0 ≤ 2 * BooleanSlices.scale n (1 - gamma) :=
    mul_nonneg (by norm_num) (BooleanSlices.scale_nonneg n _)
  have hkSq := (sq_le_sq₀ hk0 hkUpper0).2 hk
  have hrawUpper0 : 0 ≤ (2 * alpha / b) *
      BooleanSlices.scale n ((1 / 2 + gamma / 8) - 3 / 2) :=
    mul_nonneg (div_nonneg (mul_nonneg (by norm_num) halpha) hb.le)
      (BooleanSlices.scale_nonneg n _)
  calc
    (t / sigma) * k ^ 2 / 8 ≤
        ((2 * alpha / b) * BooleanSlices.scale n
          ((1 / 2 + gamma / 8) - 3 / 2)) *
          (2 * BooleanSlices.scale n (1 - gamma)) ^ 2 / 8 := by
      gcongr
    _ = (alpha / b) * BooleanSlices.scale n (1 - 15 * gamma / 8) := by
      rw [mul_pow, BooleanSlices.scale_sq (Nat.zero_le n)]
      calc
        2 * alpha / b * BooleanSlices.scale n (1 / 2 + gamma / 8 - 3 / 2) *
              (2 ^ 2 * BooleanSlices.scale n ((1 - gamma) * 2)) / 8 =
            (alpha / b) *
              (BooleanSlices.scale n (1 / 2 + gamma / 8 - 3 / 2) *
                BooleanSlices.scale n ((1 - gamma) * 2)) := by
          field_simp [ne_of_gt hb]
          ring
        _ = (alpha / b) * BooleanSlices.scale n (1 - 15 * gamma / 8) := by
          rw [BooleanSlices.scale_mul hnpos]
          congr 1
          congr 1
          ring
    _ ≤ (alpha / b) * BooleanSlices.scale n 1 := by
      exact mul_le_mul_of_nonneg_left
        (BooleanSlices.scale_mono_exponent hn (by linarith))
        (div_nonneg halpha hb.le)
    _ = (alpha / b) * n := by simp [BooleanSlices.scale]

theorem graphEffectiveLinear_restrict_norm_lower_of_sq
    {n : ℕ} (G : SimpleGraph (Fin n)) (c : Fin n → ℝ)
    (I : Finset (Fin n)) {a : ℝ} (ha : 0 ≤ a)
    (hmass : a ^ 2 * (I.card : ℝ) ^ 3 ≤
      ∑ i : I, graphEffectiveLinear G c i.1 ^ 2) :
    a * (I.card : ℝ) ^ ((3 : ℝ) / 2) ≤
      RLCD.euclidNorm (RLCD.restrict (graphEffectiveLinear G c) I) := by
  have hnormSq :
      RLCD.euclidNorm (RLCD.restrict (graphEffectiveLinear G c) I) ^ 2 =
        ∑ i : I, graphEffectiveLinear G c i.1 ^ 2 := by
    rw [RLCD.euclidNorm, Real.sq_sqrt (Finset.sum_nonneg fun i hi ↦ sq_nonneg _)]
    rfl
  have hscaleSq :
      ((I.card : ℝ) ^ ((3 : ℝ) / 2)) ^ 2 = (I.card : ℝ) ^ 3 :=
    GraphQuadratic.n_rpow_three_halves_sq I.card
  apply (sq_le_sq₀ (mul_nonneg ha (Real.rpow_nonneg (by positivity) _))
    (RLCD.euclidNorm_nonneg _)).mp
  rw [mul_pow, hscaleSq, hnormSq]
  exact hmass

lemma taylor_sum_exp_log_bound
    (m n : ℕ) (x Q : ℝ) (hm : 0 < m) (hn : 1 ≤ n)
    (hx0 : 0 ≤ x) (hQ : 1 ≤ Q) (hx : x ≤ Q * n) :
    (∑ j : Fin m, x ^ j.val / j.val.factorial) *
        Real.exp (-((m + 6 : ℕ) : ℝ) * Real.log n) ≤
      (m : ℝ) * Q ^ m * BooleanSlices.scale n (-6) := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hn)
  have hQn : 1 ≤ Q * (n : ℝ) := by
    nlinarith [show (1 : ℝ) ≤ n by exact_mod_cast hn]
  have hterm (j : Fin m) :
      x ^ j.val / j.val.factorial ≤ (Q * (n : ℝ)) ^ m := by
    have hpow : x ^ j.val ≤ (Q * (n : ℝ)) ^ j.val :=
      pow_le_pow_left₀ hx0 hx _
    have hjm : j.val ≤ m := (Nat.lt_of_lt_of_le j.isLt le_rfl).le
    have hmono : (Q * (n : ℝ)) ^ j.val ≤ (Q * (n : ℝ)) ^ m :=
      pow_le_pow_right₀ hQn hjm
    have hfac : (1 : ℝ) ≤ j.val.factorial := by
      exact_mod_cast Nat.factorial_pos j.val
    calc
      x ^ j.val / j.val.factorial ≤ x ^ j.val := by
        exact div_le_self (pow_nonneg hx0 _) hfac
      _ ≤ (Q * (n : ℝ)) ^ j.val := hpow
      _ ≤ (Q * (n : ℝ)) ^ m := hmono
  have hsum : (∑ j : Fin m, x ^ j.val / j.val.factorial) ≤
      (m : ℝ) * (Q * (n : ℝ)) ^ m := by
    calc
      (∑ j : Fin m, x ^ j.val / j.val.factorial) ≤
          ∑ _j : Fin m, (Q * (n : ℝ)) ^ m := by
        exact Finset.sum_le_sum fun i hi ↦ hterm i
      _ = (m : ℝ) * (Q * (n : ℝ)) ^ m := by simp
  have hexp : Real.exp (-((m + 6 : ℕ) : ℝ) * Real.log n) =
      BooleanSlices.scale n (-((m + 6 : ℕ) : ℝ)) := by
    unfold BooleanSlices.scale
    calc
      Real.exp (-((m + 6 : ℕ) : ℝ) * Real.log n) =
          Real.exp (Real.log n * (-((m + 6 : ℕ) : ℝ))) := by
        congr 1
        ring
      _ = Real.rpow (n : ℝ) (-((m + 6 : ℕ) : ℝ)) :=
        (Real.rpow_def_of_pos hn0 _).symm
  calc
    (∑ j : Fin m, x ^ j.val / j.val.factorial) *
        Real.exp (-((m + 6 : ℕ) : ℝ) * Real.log n) ≤
      ((m : ℝ) * (Q * (n : ℝ)) ^ m) *
        Real.exp (-((m + 6 : ℕ) : ℝ) * Real.log n) :=
      mul_le_mul_of_nonneg_right hsum (Real.exp_pos _).le
    _ = (m : ℝ) * Q ^ m * BooleanSlices.scale n (-6) := by
      rw [hexp, mul_pow]
      rw [show ((n : ℝ) ^ m) = BooleanSlices.scale n (m : ℝ) by
        unfold BooleanSlices.scale
        exact (Real.rpow_natCast (n : ℝ) m).symm]
      calc
        ↑m * (Q ^ m * BooleanSlices.scale n (m : ℝ)) *
              BooleanSlices.scale n (-((m + 6 : ℕ) : ℝ)) =
            ↑m * Q ^ m *
              (BooleanSlices.scale n (m : ℝ) *
                BooleanSlices.scale n (-((m + 6 : ℕ) : ℝ))) := by ring
        _ = ↑m * Q ^ m * BooleanSlices.scale n (-6) := by
          rw [BooleanSlices.scale_mul (lt_of_lt_of_le Nat.zero_lt_one hn)]
          congr 2
          norm_num

lemma power_factorial_decay_bound
    (n p m : ℕ) (gamma x B Q : ℝ) (hn : 1 ≤ n)
    (hgamma : 0 ≤ gamma) (hx0 : 0 ≤ x) (hB : 0 ≤ B) (hQ : 0 ≤ Q)
    (hx : x ≤ B * BooleanSlices.scale n (-7 * gamma / 4))
    (hp : 10 ≤ gamma * p) :
    Q * x ^ p / m.factorial ≤
      Q * B ^ p * BooleanSlices.scale n (-5) := by
  have hnpos : 0 < n := lt_of_lt_of_le Nat.zero_lt_one hn
  have hupper0 : 0 ≤ B * BooleanSlices.scale n (-7 * gamma / 4) :=
    mul_nonneg hB (BooleanSlices.scale_nonneg n _)
  have hxpow : x ^ p ≤
      (B * BooleanSlices.scale n (-7 * gamma / 4)) ^ p :=
    pow_le_pow_left₀ hx0 hx p
  have hpowScale :
      (B * BooleanSlices.scale n (-7 * gamma / 4)) ^ p =
        B ^ p * BooleanSlices.scale n ((-7 * gamma / 4) * p) := by
    rw [mul_pow]
    congr 1
    unfold BooleanSlices.scale
    exact (Real.rpow_mul_natCast (x := (n : ℝ))
      (by positivity) (-7 * gamma / 4) p).symm
  have hexp : (-7 * gamma / 4) * p ≤ (-5 : ℝ) := by
    push_cast at hp
    nlinarith
  have hscale : BooleanSlices.scale n ((-7 * gamma / 4) * p) ≤
      BooleanSlices.scale n (-5) :=
    BooleanSlices.scale_mono_exponent hn hexp
  have hnum : Q * x ^ p ≤
      Q * B ^ p * BooleanSlices.scale n (-5) := by
    calc
      Q * x ^ p ≤ Q *
          (B * BooleanSlices.scale n (-7 * gamma / 4)) ^ p :=
        mul_le_mul_of_nonneg_left hxpow hQ
      _ = Q * B ^ p * BooleanSlices.scale n ((-7 * gamma / 4) * p) := by
        rw [hpowScale]
        ring
      _ ≤ Q * B ^ p * BooleanSlices.scale n (-5) := by
        exact mul_le_mul_of_nonneg_left hscale
          (mul_nonneg hQ (pow_nonneg hB _))
  have hfac : (1 : ℝ) ≤ m.factorial := by
    exact_mod_cast Nat.factorial_pos m
  calc
    Q * x ^ p / m.factorial ≤ Q * x ^ p := by
      exact div_le_self (mul_nonneg hQ (pow_nonneg hx0 _)) hfac
    _ ≤ Q * B ^ p * BooleanSlices.scale n (-5) := hnum

lemma eventually_exceptional_decay (p : ℝ) (hp : 0 < p) :
    ∀ᶠ n : ℕ in Filter.atTop, ∀ k : ℕ, k ≤ n →
      2 * (k : ℝ) * Real.exp (-8 * BooleanSlices.scale n p) ≤
        BooleanSlices.scale n (-5) := by
  let q := p / 6
  have hq : 0 < q := div_pos hp (by norm_num)
  have hlin := BooleanSlices.eventually_linear_le_exp_scale q hq
  have hpow := Switching.eventually_const_mul_natCast_rpow_le_rpow
    (6 / 8 : ℝ) q (p - q) (by dsimp only [q]; linarith)
  filter_upwards [Filter.eventually_ge_atTop 1, hlin, hpow]
    with n hn hlinN hpowN
  intro k hk
  have hnpos : 0 < n := lt_of_lt_of_le Nat.zero_lt_one hn
  have hscaleGrowth :
      6 * BooleanSlices.scale n q ≤ 8 * BooleanSlices.scale n p := by
    have hpowN' : (6 / 8 : ℝ) * BooleanSlices.scale n q ≤
        BooleanSlices.scale n p := by
      change (6 / 8 : ℝ) * BooleanSlices.scale n q ≤
        BooleanSlices.scale n (q + (p - q)) at hpowN
      simpa only [show q + (p - q) = p by ring] using hpowN
    linarith
  have hexpGrowth : Real.exp (6 * BooleanSlices.scale n q) ≤
      Real.exp (8 * BooleanSlices.scale n p) := Real.exp_le_exp.mpr hscaleGrowth
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hbase : 2 * (n : ℝ) ≤ 4 * (n : ℝ) + 6 := by linarith
  have hpowSix : (2 * (n : ℝ)) ^ 6 ≤
      (Real.exp (BooleanSlices.scale n q)) ^ 6 := by
    exact pow_le_pow_left₀ (by positivity) (hbase.trans hlinN) 6
  have hexpSix : (Real.exp (BooleanSlices.scale n q)) ^ 6 =
      Real.exp (6 * BooleanSlices.scale n q) := by
    rw [← Real.exp_nat_mul]
    congr 1
  have hnSix : 2 * (n : ℝ) ^ 6 ≤ (2 * (n : ℝ)) ^ 6 := by
    nlinarith [show 0 ≤ (n : ℝ) ^ 6 by positivity]
  have hdom : 2 * (n : ℝ) ^ 6 ≤
      Real.exp (8 * BooleanSlices.scale n p) := by
    calc
      2 * (n : ℝ) ^ 6 ≤ (2 * (n : ℝ)) ^ 6 := hnSix
      _ ≤ (Real.exp (BooleanSlices.scale n q)) ^ 6 := hpowSix
      _ = Real.exp (6 * BooleanSlices.scale n q) := hexpSix
      _ ≤ Real.exp (8 * BooleanSlices.scale n p) := hexpGrowth
  have hkR : (k : ℝ) ≤ n := by exact_mod_cast hk
  have hscaleFive : BooleanSlices.scale n 5 = (n : ℝ) ^ 5 := by
    unfold BooleanSlices.scale
    norm_num [Real.rpow_natCast]
  have hnum : 2 * (k : ℝ) * BooleanSlices.scale n 5 ≤
      Real.exp (8 * BooleanSlices.scale n p) := by
    rw [hscaleFive]
    calc
      2 * (k : ℝ) * (n : ℝ) ^ 5 ≤ 2 * (n : ℝ) * (n : ℝ) ^ 5 := by
        gcongr
      _ = 2 * (n : ℝ) ^ 6 := by ring
      _ ≤ Real.exp (8 * BooleanSlices.scale n p) := hdom
  have hdiv : (2 * (k : ℝ)) /
      Real.exp (8 * BooleanSlices.scale n p) ≤
        1 / BooleanSlices.scale n 5 := by
    rw [div_le_div_iff₀ (Real.exp_pos _) (BooleanSlices.scale_pos hnpos _)]
    simpa only [one_mul] using hnum
  calc
    2 * (k : ℝ) * Real.exp (-8 * BooleanSlices.scale n p) =
        (2 * (k : ℝ)) / Real.exp (8 * BooleanSlices.scale n p) := by
      rw [show -8 * BooleanSlices.scale n p =
          -(8 * BooleanSlices.scale n p) by ring]
      rw [Real.exp_neg]
      ring
    _ ≤ 1 / BooleanSlices.scale n 5 := hdiv
    _ = BooleanSlices.scale n (-5) := by
      unfold BooleanSlices.scale
      rw [one_div]
      exact (Real.rpow_neg (by positivity : (0 : ℝ) ≤ n) 5).symm

lemma eventually_lcd_log_budget
    (gamma L Ktheta Kcross : ℝ) (m : ℕ)
    (hgamma : 0 < gamma) (hL : 0 < L) (hKtheta : 0 < Ktheta)
    (hKcross : 0 ≤ Kcross)
    (hcoeff : (3 * m + 6 : ℕ) ≤ L ^ 2 * gamma / 16) :
    ∀ᶠ n : ℕ in Filter.atTop,
      Real.sqrt ((((m - 1) * 2 : ℕ) : ℝ) +
          ((m + 6 : ℕ) : ℝ) * Real.log n) +
        Kcross * BooleanSlices.scale n (-gamma / 4) ≤
      L * Real.sqrt (RLCD.logPlus
        (Ktheta * BooleanSlices.scale n (gamma / 2))) := by
  let q := gamma / 4
  have hq : 0 < q := div_pos hgamma (by norm_num)
  have hthetaGrow := BooleanSlices.eventually_const_le_scale
    (1 / Ktheta) q hq
  have hcrossGrow := BooleanSlices.eventually_const_le_scale
    Kcross q hq
  have hlogOne : ∀ᶠ n : ℕ in Filter.atTop, 1 ≤ Real.log n :=
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually
      (Filter.eventually_ge_atTop 1)
  filter_upwards [Filter.eventually_ge_atTop 1, hthetaGrow, hcrossGrow,
    hlogOne] with n hn hthetaN hcrossN hlogN
  have hnpos : 0 < n := lt_of_lt_of_le Nat.zero_lt_one hn
  have hnRpos : (0 : ℝ) < n := by exact_mod_cast hnpos
  have hqscalePos := BooleanSlices.scale_pos hnpos q
  have hthetaFactor : 1 ≤ Ktheta * BooleanSlices.scale n q := by
    calc
      1 = (1 / Ktheta) * Ktheta := by field_simp [ne_of_gt hKtheta]
      _ ≤ BooleanSlices.scale n q * Ktheta :=
        mul_le_mul_of_nonneg_right hthetaN hKtheta.le
      _ = Ktheta * BooleanSlices.scale n q := by ring
  have htheta : BooleanSlices.scale n q ≤
      Ktheta * BooleanSlices.scale n (gamma / 2) := by
    rw [show gamma / 2 = q + q by dsimp only [q] <;> ring,
      ← BooleanSlices.scale_mul hnpos]
    nlinarith [hqscalePos.le]
  have hlogScale : Real.log (BooleanSlices.scale n q) =
      q * Real.log n := by
    unfold BooleanSlices.scale
    exact Real.log_rpow hnRpos q
  have hlogTheta : q * Real.log n ≤
      RLCD.logPlus (Ktheta * BooleanSlices.scale n (gamma / 2)) := by
    have hthetaPos : 0 < Ktheta * BooleanSlices.scale n (gamma / 2) :=
      mul_pos hKtheta (BooleanSlices.scale_pos hnpos _)
    calc
      q * Real.log n = Real.log (BooleanSlices.scale n q) := hlogScale.symm
      _ ≤ Real.log (Ktheta * BooleanSlices.scale n (gamma / 2)) :=
        Real.log_le_log hqscalePos htheta
      _ ≤ RLCD.logPlus (Ktheta * BooleanSlices.scale n (gamma / 2)) := by
        exact le_max_right _ _
  have hcross : Kcross * BooleanSlices.scale n (-gamma / 4) ≤ 1 := by
    have hscaleInv : BooleanSlices.scale n q *
        BooleanSlices.scale n (-gamma / 4) = 1 := by
      rw [BooleanSlices.scale_mul hnpos]
      have hzero : q + -gamma / 4 = 0 := by dsimp only [q]; ring
      rw [hzero]
      simp [BooleanSlices.scale]
    calc
      Kcross * BooleanSlices.scale n (-gamma / 4) ≤
          BooleanSlices.scale n q * BooleanSlices.scale n (-gamma / 4) :=
        mul_le_mul_of_nonneg_right hcrossN (BooleanSlices.scale_nonneg n _)
      _ = 1 := hscaleInv
  have hinside0 : 0 ≤ ((((m - 1) * 2 : ℕ) : ℝ) +
      ((m + 6 : ℕ) : ℝ) * Real.log n) := by positivity
  have hinside : ((((m - 1) * 2 : ℕ) : ℝ) +
      ((m + 6 : ℕ) : ℝ) * Real.log n) ≤
      (L ^ 2 * gamma / 16) * Real.log n := by
    have hmSub : ((m - 1) * 2 : ℕ) ≤ 2 * m := by omega
    have hmSubR : ((((m - 1) * 2 : ℕ) : ℝ)) ≤ 2 * (m : ℝ) := by
      exact_mod_cast hmSub
    have hcoeffR : ((3 * m + 6 : ℕ) : ℝ) ≤ L ^ 2 * gamma / 16 := by
      exact_mod_cast hcoeff
    have hlog0 : 0 ≤ Real.log n := zero_le_one.trans hlogN
    push_cast at hcoeffR
    calc
      ((((m - 1) * 2 : ℕ) : ℝ) +
          ((m + 6 : ℕ) : ℝ) * Real.log n) ≤
          2 * (m : ℝ) + ((m : ℝ) + 6) * Real.log n := by
        convert add_le_add_right hmSubR (((m : ℝ) + 6) * Real.log n) using 1 <;>
          push_cast <;> ring
      _ ≤ ((3 * (m : ℝ) + 6) * Real.log n) := by
        nlinarith
      _ ≤ (L ^ 2 * gamma / 16) * Real.log n :=
        mul_le_mul_of_nonneg_right hcoeffR hlog0
  have htarget0 : 0 ≤ (L / 2) * Real.sqrt (q * Real.log n) := by positivity
  have hsqrtHalf : Real.sqrt ((((m - 1) * 2 : ℕ) : ℝ) +
      ((m + 6 : ℕ) : ℝ) * Real.log n) ≤
      (L / 2) * Real.sqrt (q * Real.log n) := by
    have hqlog0 : 0 ≤ q * Real.log n :=
      mul_nonneg hq.le (zero_le_one.trans hlogN)
    apply (sq_le_sq₀ (Real.sqrt_nonneg _) htarget0).mp
    rw [Real.sq_sqrt hinside0, mul_pow, Real.sq_sqrt hqlog0]
    dsimp only [q]
    nlinarith
  have hunitCoeff : 1 ≤ L ^ 2 * gamma / 16 := by
    have hthreeNat : 1 ≤ 3 * m + 6 := by omega
    have hthree : (1 : ℝ) ≤ ((3 * m + 6 : ℕ) : ℝ) := by exact_mod_cast hthreeNat
    exact hthree.trans (by exact_mod_cast hcoeff)
  have honeHalf : 1 ≤ (L / 2) * Real.sqrt (q * Real.log n) := by
    have hqlog0 : 0 ≤ q * Real.log n :=
      mul_nonneg hq.le (zero_le_one.trans hlogN)
    have hsq : 1 ≤ ((L / 2) * Real.sqrt (q * Real.log n)) ^ 2 := by
      rw [mul_pow, Real.sq_sqrt hqlog0]
      dsimp only [q]
      nlinarith
    nlinarith [sq_nonneg ((L / 2) * Real.sqrt (q * Real.log n) - 1)]
  have hsqrtLog : Real.sqrt (q * Real.log n) ≤
      Real.sqrt (RLCD.logPlus
        (Ktheta * BooleanSlices.scale n (gamma / 2))) :=
    Real.sqrt_le_sqrt hlogTheta
  calc
    Real.sqrt ((((m - 1) * 2 : ℕ) : ℝ) +
          ((m + 6 : ℕ) : ℝ) * Real.log n) +
        Kcross * BooleanSlices.scale n (-gamma / 4) ≤
      (L / 2) * Real.sqrt (q * Real.log n) + 1 :=
        add_le_add hsqrtHalf hcross
    _ ≤ (L / 2) * Real.sqrt (q * Real.log n) +
          (L / 2) * Real.sqrt (q * Real.log n) :=
      by linarith
    _ = L * Real.sqrt (q * Real.log n) := by ring
    _ ≤ L * Real.sqrt (RLCD.logPlus
          (Ktheta * BooleanSlices.scale n (gamma / 2))) :=
      mul_le_mul_of_nonneg_left hsqrtLog hL.le

lemma lcd_budget_coefficient
    (gamma L : ℝ) (r : ℕ) (hgamma : 0 < gamma)
    (hgammaUpper : gamma < 1 / 4)
    (hpowUpper : ((2 ^ r : ℕ) : ℝ) < 40 / gamma)
    (hL : 100 / gamma ≤ L) :
    (((3 * (2 ^ (r + 1)) + 6 : ℕ) : ℝ)) ≤ L ^ 2 * gamma / 16 := by
  have hpGamma : gamma * ((2 ^ r : ℕ) : ℝ) < 40 := by
    have := (lt_div_iff₀ hgamma).mp hpowUpper
    nlinarith
  have hLGamma : 100 ≤ L * gamma := by
    have := (div_le_iff₀ hgamma).mp hL
    nlinarith
  have hLGamma0 : 0 ≤ L * gamma := by linarith
  have hsq : (100 : ℝ) ^ 2 ≤ (L * gamma) ^ 2 :=
    (sq_le_sq₀ (by norm_num) hLGamma0).2 hLGamma
  have hwhole : (((3 * (2 ^ (r + 1)) + 6 : ℕ) : ℝ)) =
      6 * ((2 ^ r : ℕ) : ℝ) + 6 := by
    push_cast
    rw [pow_succ]
    push_cast
    ring
  have hleft : 16 * gamma * (((3 * (2 ^ (r + 1)) + 6 : ℕ) : ℝ)) <
      4000 := by
    rw [hwhole]
    calc
      16 * gamma * (6 * ((2 ^ r : ℕ) : ℝ) + 6) =
          96 * (gamma * ((2 ^ r : ℕ) : ℝ)) + 96 * gamma := by ring
      _ < 96 * 40 + 96 * (1 / 4 : ℝ) := by nlinarith
      _ < 4000 := by norm_num
  have hmul : 16 * gamma * (((3 * (2 ^ (r + 1)) + 6 : ℕ) : ℝ)) ≤
      (L * gamma) ^ 2 := by
    nlinarith
  have hden : 0 < 16 * gamma := mul_pos (by norm_num) hgamma
  have hdiv : (((3 * (2 ^ (r + 1)) + 6 : ℕ) : ℝ)) ≤
      (L * gamma) ^ 2 / (16 * gamma) := by
    rw [le_div_iff₀ hden]
    nlinarith
  convert hdiv using 1
  field_simp [ne_of_gt hgamma]

/-- Source-shaped formulation of KSSS Lemma 7.2. -/
def KSSSLemma72 : Prop :=
  ∀ C H gamma : ℝ, 0 < C → 0 ≤ H → 0 < gamma → gamma < 1 / 4 →
    let L : ℝ := (Nat.ceil (100 / gamma) : ℕ)
    ∃ alpha C' : ℝ, 0 < alpha ∧ 0 ≤ C' ∧
      ∀ᶠ n : ℕ in Filter.atTop,
        ∀ (G : SimpleGraph (Fin n)) (e₀ : ℝ) (c : Fin n → ℝ),
          RamseyFree C G →
          (∀ i, 0 ≤ c i ∧ c i ≤ H * n) →
          ∀ t : ℝ,
            BooleanSlices.scale n (2 * gamma) ≤ |t| →
            |t| ≤ alpha * min
              (BooleanSlices.scale n (gamma / 2) *
                RLCD.regularizedLCD L gamma (graphEffectiveLinear G c))
              (BooleanSlices.scale n (1 / 2 + gamma / 8)) →
            ‖centeredGraphCharacteristic G e₀ c
                (t / graphPerturbedSigma G e₀ c)‖ ≤
              C' * BooleanSlices.scale n (-5)

theorem ksssLemma72 : KSSSLemma72 := by
  classical
  intro C H gamma hC hH hgamma hgammaUpper
  dsimp only
  let L : ℝ := (Nat.ceil (100 / gamma) : ℕ)
  have hLlower : 100 / gamma ≤ L := by
    dsimp only [L]
    exact Nat.le_ceil _
  have hLpos : 0 < L := lt_of_lt_of_le (div_pos (by norm_num) hgamma) hLlower
  obtain ⟨a, ha, Na, hmass⟩ := ksssLemma73 C hC
  obtain ⟨b, hb, Nb, hdensity⟩ :=
    AKSGraph.ramseyFree_eventually_whole_density_lower C hC
  let R : ℝ := max 1 H
  have hR : 0 < R := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  have hHR : H ≤ R := le_max_right _ _
  have hx : 1 ≤ 10 / gamma := by
    have : gamma < 10 := hgammaUpper.trans (by norm_num)
    rw [le_div_iff₀ hgamma]
    linarith
  obtain ⟨r, hrLower, hrUpper⟩ := exists_two_pow_between (10 / gamma) hx
  let m : ℕ := 2 ^ (r + 1)
  have hmpos : 0 < m := by positivity
  have hmEq : 2 ^ (r + 1) = m := rfl
  have hrGamma : 10 ≤ gamma * ((2 ^ r : ℕ) : ℝ) := by
    have := (div_le_iff₀ hgamma).mp hrLower
    nlinarith
  have hrUpper40 : ((2 ^ r : ℕ) : ℝ) < 40 / gamma := by
    calc
      ((2 ^ r : ℕ) : ℝ) < 4 * (10 / gamma) := hrUpper
      _ = 40 / gamma := by ring
  have hbudgetCoeff : (((3 * m + 6 : ℕ) : ℝ)) ≤ L ^ 2 * gamma / 16 := by
    exact lcd_budget_coefficient gamma L r hgamma hgammaUpper hrUpper40 hLlower
  let q0 : ℝ := Real.sqrt 2 * (H + 1 / 2) / (Real.pi * b)
  have hq0 : 0 < q0 := by dsimp only [q0]; positivity
  let alpha : ℝ := 1 / (4 * q0)
  have halpha : 0 < alpha := by dsimp only [alpha]; positivity
  have halphaSmall : alpha * q0 ≤ 1 / 2 := by
    dsimp only [alpha]
    field_simp [ne_of_gt hq0]
    linarith
  let Ktheta : ℝ := a / (2 * Real.pi * R * L)
  have hKtheta : 0 < Ktheta := by dsimp only [Ktheta]; positivity
  let Kcross : ℝ := 2 * alpha * Real.sqrt 2 / (Real.pi * b)
  have hKcross : 0 ≤ Kcross := by dsimp only [Kcross]; positivity
  let Q : ℝ := max 1 (alpha / b)
  have hQ : 1 ≤ Q := le_max_left _ _
  have hQalpha : alpha / b ≤ Q := le_max_right _ _
  let B : ℝ := alpha ^ 2 / (2 * b ^ 2)
  have hB : 0 ≤ B := by dsimp only [B]; positivity
  let C' : ℝ := (m : ℝ) * Q ^ m +
      9 ^ bonamiExponent 2 r * B ^ (2 ^ r) + 1
  have hC' : 0 ≤ C' := by dsimp only [C']; positivity
  have hbudgetEvent := eventually_lcd_log_budget gamma L Ktheta Kcross m
    hgamma hLpos hKtheta hKcross hbudgetCoeff
  have hexceptionEvent := eventually_exceptional_decay (gamma / 4)
    (div_pos hgamma (by norm_num))
  have hNaCard := BooleanSlices.eventually_const_le_scale (Na : ℝ)
    (1 - gamma) (by linarith)
  refine ⟨alpha, C', halpha, hC', ?_⟩
  filter_upwards [Filter.eventually_ge_atTop 1,
    Filter.eventually_ge_atTop Na, Filter.eventually_ge_atTop Nb,
    hbudgetEvent, hexceptionEvent, hNaCard]
    with n hn hNan hNbn hbudgetN hexceptionN hNaScale
  intro G e₀ c hG hc t htLower htUpper
  have hnpos : 0 < n := lt_of_lt_of_le Nat.zero_lt_one hn
  let k : ℕ := RLCD.regularizationCard n gamma
  have hkN : Na ≤ k := by
    have hcast : (Na : ℝ) ≤ k :=
      hNaScale.trans (regularizationCard_cast_lower gamma)
    exact_mod_cast hcast
  have hkLower : BooleanSlices.scale n (1 - gamma) ≤ (k : ℝ) :=
    regularizationCard_cast_lower gamma
  have hkUpper : (k : ℝ) ≤ 2 * BooleanSlices.scale n (1 - gamma) :=
    (regularizationCard_cast_upper_two_scale hn (by linarith)).le
  have hkn : k ≤ n := regularizationCard_le_self hn hgamma.le
  have hsqrtScale : Real.sqrt n = BooleanSlices.scale n (1 / 2) := by
    rw [Real.sqrt_eq_rpow]
    rfl
  have hsqrtK : Real.sqrt n ≤ (k : ℝ) := by
    rw [hsqrtScale]
    exact (BooleanSlices.scale_mono_exponent hn (by linarith)).trans hkLower
  have hedge : b * (n : ℝ) ^ 2 ≤ (G.edgeFinset.card : ℝ) := by
    have hd := hdensity n hNbn G hG
    simpa [AKSGraph.edgeCount] using hd
  have hcNonneg : ∀ i, 0 ≤ c i := fun i ↦ (hc i).1
  have hcUpper : ∀ i, c i ≤ H * n := fun i ↦ (hc i).2
  have hcAbs : ∀ i, |c i| ≤ R * n := by
    intro i
    rw [abs_of_nonneg (hcNonneg i)]
    exact (hcUpper i).trans (mul_le_mul_of_nonneg_right hHR (by positivity))
  let sigma := graphPerturbedSigma G e₀ c
  have hsigmaLower : b / 2 * BooleanSlices.scale n (3 / 2) ≤ sigma := by
    dsimp only [sigma, BooleanSlices.scale]
    exact graphPerturbedSigma_lower G e₀ c hnpos hb.le hcNonneg hedge
  have hsigmaUpper : sigma ≤ R * BooleanSlices.scale n (3 / 2) := by
    dsimp only [sigma, BooleanSlices.scale]
    exact graphPerturbedSigma_upper G e₀ c R (le_max_left _ _) hcAbs
  have hsigmaPos : 0 < sigma :=
    graphPerturbedSigma_pos G e₀ c hnpos hb hcNonneg hedge
  let T : ℝ := |t|
  have hTpos : 0 < T :=
    (BooleanSlices.scale_pos hnpos (2 * gamma)).trans_le htLower
  change T ≤ alpha * min
      (BooleanSlices.scale n (gamma / 2) *
        RLCD.regularizedLCD L gamma (graphEffectiveLinear G c))
      (BooleanSlices.scale n (1 / 2 + gamma / 8)) at htUpper
  have hTupperLCD : T ≤ alpha * BooleanSlices.scale n (gamma / 2) *
      RLCD.regularizedLCD L gamma (graphEffectiveLinear G c) := by
    exact htUpper.trans (by
      simpa only [mul_assoc] using
        mul_le_mul_of_nonneg_left (min_le_left _ _) halpha.le)
  have hTupperPower : T ≤ alpha * BooleanSlices.scale n
      (1 / 2 + gamma / 8) :=
    htUpper.trans (mul_le_mul_of_nonneg_left (min_le_right _ _) halpha.le)
  have hLCDpos : 0 < RLCD.regularizedLCD L gamma
      (graphEffectiveLinear G c) := by
    by_contra hnot
    have hle : RLCD.regularizedLCD L gamma (graphEffectiveLinear G c) ≤ 0 :=
      le_of_not_gt hnot
    have : T ≤ 0 := hTupperLCD.trans (by
      have hs : 0 ≤ alpha * BooleanSlices.scale n (gamma / 2) :=
        mul_nonneg halpha.le (BooleanSlices.scale_nonneg n _)
      exact mul_nonpos_of_nonneg_of_nonpos hs hle)
    linarith
  have hmassI : ∀ I : Finset (Fin n), I.card = k →
      a ^ 2 * (I.card : ℝ) ^ 3 ≤
        ∑ i : I, graphEffectiveLinear G c i.1 ^ 2 := by
    intro I hI
    exact hmass hn hNan G hG c hcNonneg I (by simpa [hI]) (by simpa [hI] using hsqrtK)
  have hnormlo : ∀ I : Finset (Fin n), I.card = k →
      a * (k : ℝ) ^ ((3 : ℝ) / 2) ≤
        RLCD.euclidNorm (RLCD.restrict (graphEffectiveLinear G c) I) := by
    intro I hI
    rw [← hI]
    exact graphEffectiveLinear_restrict_norm_lower_of_sq G c I ha.le (hmassI I hI)
  have hnormup : ∀ I : Finset (Fin n), I.card = k →
      RLCD.euclidNorm (RLCD.restrict (graphEffectiveLinear G c) I) ≤
        Real.sqrt k * ((H + 1 / 2) * n) := by
    intro I hI
    simpa only [hI] using
      graphEffectiveLinear_restrict_norm_upper G c I H hH hcNonneg hcUpper
  have hbelow : (T / sigma) *
        (Real.sqrt k * ((H + 1 / 2) * n)) / (2 * Real.pi) <
      RLCD.regularizedLCDCard L k (graphEffectiveLinear G c) := by
    have hreg : RLCD.regularizedLCDCard L k (graphEffectiveLinear G c) =
        RLCD.regularizedLCD L gamma (graphEffectiveLinear G c) := rfl
    rw [hreg]
    exact normalized_lcd_theta_upper hnpos hgamma.le hb hH hsigmaLower
      (by positivity) hkUpper hTpos.le hTupperLCD hLCDpos halpha.le
      (by simpa only [q0] using halphaSmall)
  have hthetaLower : Ktheta * BooleanSlices.scale n (gamma / 2) ≤
      ((((T / sigma) * (a * (k : ℝ) ^ ((3 : ℝ) / 2))) /
        (2 * Real.pi)) / L) := by
    dsimp only [Ktheta]
    exact normalized_lcd_theta_lower hnpos ha hR hLpos hsigmaPos hsigmaUpper
      htLower hkLower
  have hcrossUpper :
      (T / sigma) * Real.sqrt k *
          BooleanSlices.scale n (1 / 2 + gamma / 8) / Real.pi ≤
        Kcross * BooleanSlices.scale n (-gamma / 4) := by
    dsimp only [Kcross]
    exact normalized_cross_perturbation_upper hnpos hb halpha.le hsigmaLower
      hTpos.le hTupperPower (by positivity) hkUpper
  have hbudget :
      Real.sqrt (((((2 ^ (r + 1) - 1) * 2 : ℕ) : ℝ)) +
          ((m + 6 : ℕ) : ℝ) * Real.log n) +
        (T / sigma) * Real.sqrt k *
          BooleanSlices.scale n (1 / 2 + gamma / 8) / Real.pi ≤
      L * Real.sqrt (RLCD.logPlus
        ((((T / sigma) * (a * (k : ℝ) ^ ((3 : ℝ) / 2))) /
          (2 * Real.pi)) / L)) := by
    rw [hmEq]
    calc
      Real.sqrt (((((m - 1) * 2 : ℕ) : ℝ)) +
          ((m + 6 : ℕ) : ℝ) * Real.log n) +
        (T / sigma) * Real.sqrt k *
          BooleanSlices.scale n (1 / 2 + gamma / 8) / Real.pi ≤
        Real.sqrt (((((m - 1) * 2 : ℕ) : ℝ)) +
          ((m + 6 : ℕ) : ℝ) * Real.log n) +
          Kcross * BooleanSlices.scale n (-gamma / 4) :=
        by simpa only [add_comm] using
          add_le_add_right hcrossUpper
            (Real.sqrt (((((m - 1) * 2 : ℕ) : ℝ)) +
              ((m + 6 : ℕ) : ℝ) * Real.log n))
      _ ≤ L * Real.sqrt (RLCD.logPlus
          (Ktheta * BooleanSlices.scale n (gamma / 2))) := hbudgetN
      _ ≤ L * Real.sqrt (RLCD.logPlus
          ((((T / sigma) * (a * (k : ℝ) ^ ((3 : ℝ) / 2))) /
            (2 * Real.pi)) / L)) := by
        apply mul_le_mul_of_nonneg_left _ hLpos.le
        apply Real.sqrt_le_sqrt
        exact logPlus_mono_of_pos
          (mul_pos hKtheta (BooleanSlices.scale_pos hnpos _)) hthetaLower
  obtain ⟨I, hI, hmain⟩ :=
    exists_coordinateSet_centeredGraphCharacteristic_le_of_bounds
      G e₀ c L (T / sigma) (BooleanSlices.scale n (1 / 2 + gamma / 8))
      (((m + 6 : ℕ) : ℝ) * Real.log n)
      (a * (k : ℝ) ^ ((3 : ℝ) / 2))
      (Real.sqrt k * ((H + 1 / 2) * n)) r hkn hnpos hLpos
      (div_pos hTpos hsigmaPos) (BooleanSlices.scale_pos hnpos _)
      (mul_nonneg (by positivity) (Real.log_nonneg (by exact_mod_cast hn)))
      (mul_pos ha (Real.rpow_pos_of_pos (by
        exact (BooleanSlices.scale_pos hnpos _).trans_le hkLower) _))
      hnormlo hnormup hbelow hbudget
  have hlinearBase : (T / sigma) * (k : ℝ) ^ 2 / 8 ≤
      (alpha / b) * n :=
    normalized_taylor_linear_base_upper hn hgamma.le hb halpha.le hsigmaLower
      hTpos.le hTupperPower (by positivity) hkUpper
  have hxQ : (T / sigma) * (k : ℝ) ^ 2 / 8 ≤ Q * n := by
    exact hlinearBase.trans (mul_le_mul_of_nonneg_right hQalpha (by positivity))
  have hfirst0 := taylor_sum_exp_log_bound m n
    ((T / sigma) * (k : ℝ) ^ 2 / 8) Q hmpos hn
    (by positivity) hQ hxQ
  have hfirst :
      (∑ j : Fin m,
        ((T / sigma) * (k : ℝ) ^ 2 / 8) ^ j.val / j.val.factorial) *
          Real.exp (-(((m + 6 : ℕ) : ℝ) * Real.log n)) ≤
        (m : ℝ) * Q ^ m * BooleanSlices.scale n (-5) := by
    calc
      _ ≤ (m : ℝ) * Q ^ m * BooleanSlices.scale n (-6) := by
        simpa only [neg_mul] using hfirst0
      _ ≤ (m : ℝ) * Q ^ m * BooleanSlices.scale n (-5) := by
        exact mul_le_mul_of_nonneg_left
          (BooleanSlices.scale_mono_exponent hn (by norm_num)) (by positivity)
  have hbase2 : (T / sigma) ^ 2 * (k : ℝ) ^ 2 / 32 ≤
      B * BooleanSlices.scale n (-7 * gamma / 4) := by
    dsimp only [B]
    exact normalized_taylor_base_upper hnpos hb halpha.le hsigmaLower
      hTpos.le hTupperPower (by positivity) hkUpper
  have hsecond := power_factorial_decay_bound n (2 ^ r) (m - 1) gamma
    ((T / sigma) ^ 2 * (k : ℝ) ^ 2 / 32) B
    (9 ^ bonamiExponent 2 r) hn hgamma.le (by positivity) hB (by positivity)
    hbase2 hrGamma
  have hthird := hexceptionN k hkn
  have hbound :
      ((∑ j : Fin m,
        ((T / sigma) * (k : ℝ) ^ 2 / 8) ^ j.val / j.val.factorial) *
          Real.exp (-(((m + 6 : ℕ) : ℝ) * Real.log n)) +
        (9 ^ bonamiExponent 2 r *
          (((T / sigma) ^ 2 * (k : ℝ) ^ 2 / 32) ^ (2 ^ r))) /
          (m - 1).factorial) +
        2 * (k : ℝ) * Real.exp (-8 *
          BooleanSlices.scale n (1 / 2 + gamma / 8) ^ 2 / n) ≤
        C' * BooleanSlices.scale n (-5) := by
    have huExp : BooleanSlices.scale n (1 / 2 + gamma / 8) ^ 2 / n =
        BooleanSlices.scale n (gamma / 4) := by
      rw [BooleanSlices.scale_sq (Nat.zero_le n)]
      rw [show (1 / 2 + gamma / 8) * 2 = 1 + gamma / 4 by ring]
      rw [← BooleanSlices.scale_mul hnpos]
      simp only [BooleanSlices.scale, Real.rpow_one]
      field_simp [show (n : ℝ) ≠ 0 by positivity]
      exact Real.rpow_one (n : ℝ)
    have htailExp : -8 * BooleanSlices.scale n (1 / 2 + gamma / 8) ^ 2 / n =
        -8 * BooleanSlices.scale n (gamma / 4) := by
      calc
        -8 * BooleanSlices.scale n (1 / 2 + gamma / 8) ^ 2 / n =
            -8 * (BooleanSlices.scale n (1 / 2 + gamma / 8) ^ 2 / n) := by ring
        _ = -8 * BooleanSlices.scale n (gamma / 4) := by rw [huExp]
    rw [htailExp]
    dsimp only [C']
    calc
      (∑ j : Fin m,
          ((T / sigma) * (k : ℝ) ^ 2 / 8) ^ j.val / j.val.factorial) *
            Real.exp (-(((m + 6 : ℕ) : ℝ) * Real.log n)) +
          (9 ^ bonamiExponent 2 r *
            (((T / sigma) ^ 2 * (k : ℝ) ^ 2 / 32) ^ (2 ^ r))) /
            (m - 1).factorial +
          2 * (k : ℝ) * Real.exp
            (-8 * BooleanSlices.scale n (gamma / 4)) ≤
        (m : ℝ) * Q ^ m * BooleanSlices.scale n (-5) +
          (9 ^ bonamiExponent 2 r * B ^ (2 ^ r) *
            BooleanSlices.scale n (-5)) +
          BooleanSlices.scale n (-5) :=
        add_le_add (add_le_add hfirst hsecond) hthird
      _ = ((m : ℝ) * Q ^ m + 9 ^ bonamiExponent 2 r * B ^ (2 ^ r) + 1) *
          BooleanSlices.scale n (-5) := by ring
  have hpos : ‖centeredGraphCharacteristic G e₀ c (T / sigma)‖ ≤
      C' * BooleanSlices.scale n (-5) := by
    exact hmain.trans (by
      simpa only [hI, hmEq] using hbound)
  by_cases ht0 : 0 ≤ t
  · simpa only [T, abs_of_nonneg ht0] using hpos
  · have htneg : t < 0 := lt_of_not_ge ht0
    have habs : T = -t := by simp [T, abs_of_neg htneg]
    have hfreq : t / sigma = -(T / sigma) := by rw [habs]; ring
    rw [hfreq, norm_centeredGraphCharacteristic_neg]
    exact hpos


/-- Raw-frequency form of KSSS Lemma 7.2. -/
def KSSSLemma72Raw : Prop :=
  ∀ C H gamma : ℝ, 0 < C → 0 ≤ H → 0 < gamma → gamma < 1 / 4 →
    let L : ℝ := (Nat.ceil (100 / gamma) : ℕ)
    ∃ alpha C' : ℝ, 0 < alpha ∧ 0 ≤ C' ∧
      ∀ᶠ n : ℕ in Filter.atTop,
        ∀ (G : SimpleGraph (Fin n)) (e₀ : ℝ) (c : Fin n → ℝ),
          RamseyFree C G →
          (∀ i, 0 ≤ c i ∧ c i ≤ H * n) →
          ∀ tau : ℝ,
            BooleanSlices.scale n (2 * gamma) /
                graphPerturbedSigma G e₀ c ≤ |tau| →
            |tau| ≤ alpha * min
                (BooleanSlices.scale n (gamma / 2) *
                  RLCD.regularizedLCD L gamma (graphEffectiveLinear G c))
                (BooleanSlices.scale n (1 / 2 + gamma / 8)) /
                  graphPerturbedSigma G e₀ c →
            ‖centeredGraphCharacteristic G e₀ c tau‖ ≤
              C' * BooleanSlices.scale n (-5)

theorem ksssLemma72_raw : KSSSLemma72Raw := by
  classical
  intro C H gamma hC hH hgamma hgammaUpper
  dsimp only
  obtain ⟨alpha, C', halpha, hC', hnormalized⟩ :=
    ksssLemma72 C H gamma hC hH hgamma hgammaUpper
  obtain ⟨b, hb, Nb, hdensity⟩ :=
    AKSGraph.ramseyFree_eventually_whole_density_lower C hC
  refine ⟨alpha, C', halpha, hC', ?_⟩
  filter_upwards [hnormalized, Filter.eventually_ge_atTop 1,
    Filter.eventually_ge_atTop Nb] with n hnormalizedN hn hNb
  intro G e₀ c hG hc tau htLower htUpper
  have hnpos : 0 < n := lt_of_lt_of_le Nat.zero_lt_one hn
  have hcNonneg : ∀ i, 0 ≤ c i := fun i ↦ (hc i).1
  have hedge : b * (n : ℝ) ^ 2 ≤ (G.edgeFinset.card : ℝ) := by
    have hd := hdensity n hNb G hG
    simpa [AKSGraph.edgeCount] using hd
  let sigma := graphPerturbedSigma G e₀ c
  have hsigma : 0 < sigma := by
    dsimp only [sigma]
    exact graphPerturbedSigma_pos G e₀ c hnpos hb hcNonneg hedge
  have habsmul : |sigma * tau| = sigma * |tau| := by
    rw [abs_mul, abs_of_pos hsigma]
  have hnormLower : BooleanSlices.scale n (2 * gamma) ≤ |sigma * tau| := by
    rw [habsmul]
    have h := (div_le_iff₀ hsigma).mp htLower
    nlinarith
  have hnormUpper : |sigma * tau| ≤ alpha * min
      (BooleanSlices.scale n (gamma / 2) *
        RLCD.regularizedLCD ((Nat.ceil (100 / gamma) : ℕ) : ℝ) gamma
          (graphEffectiveLinear G c))
      (BooleanSlices.scale n (1 / 2 + gamma / 8)) := by
    rw [habsmul]
    have h := (le_div_iff₀ hsigma).mp htUpper
    nlinarith
  have hmain := hnormalizedN G e₀ c hG hc (sigma * tau)
    hnormLower hnormUpper
  have hfreq : sigma * tau / graphPerturbedSigma G e₀ c = tau := by
    have hσ0 : graphPerturbedSigma G e₀ c ≠ 0 := by
      simpa only [sigma] using hsigma.ne'
    dsimp only [sigma]
    field_simp [hσ0]
  simpa only [hfreq] using hmain

lemma scale_half_plus_gamma_eighth_le_lcd_cutoff
    {n : ℕ} {gamma lcd : ℝ} (hn : 1 ≤ n) (hgamma : 0 ≤ gamma)
    (hlcd : BooleanSlices.scale n (1 / 2) ≤ lcd) :
    BooleanSlices.scale n (1 / 2 + gamma / 8) ≤
      BooleanSlices.scale n (gamma / 2) * lcd := by
  have hnpos : 0 < n := lt_of_lt_of_le Nat.zero_lt_one hn
  calc
    BooleanSlices.scale n (1 / 2 + gamma / 8) ≤
        BooleanSlices.scale n (gamma / 2 + 1 / 2) :=
      BooleanSlices.scale_mono_exponent hn (by linarith)
    _ = BooleanSlices.scale n (gamma / 2) *
        BooleanSlices.scale n (1 / 2) := by
      rw [BooleanSlices.scale_mul hnpos]
    _ ≤ BooleanSlices.scale n (gamma / 2) * lcd :=
      mul_le_mul_of_nonneg_left hlcd (BooleanSlices.scale_nonneg n _)

/-- The raw-frequency Lemma 7.2 band in the unstructured branch, where the
regularized LCD is at least `sqrt n`. -/
def KSSSLemma72RawUnstructured : Prop :=
  ∀ C H gamma : ℝ, 0 < C → 0 ≤ H → 0 < gamma → gamma < 1 / 4 →
    let L : ℝ := (Nat.ceil (100 / gamma) : ℕ)
    ∃ alpha C' : ℝ, 0 < alpha ∧ 0 ≤ C' ∧
      ∀ᶠ n : ℕ in Filter.atTop,
        ∀ (G : SimpleGraph (Fin n)) (e₀ : ℝ) (c : Fin n → ℝ),
          RamseyFree C G →
          (∀ i, 0 ≤ c i ∧ c i ≤ H * n) →
          BooleanSlices.scale n (1 / 2) ≤
            RLCD.regularizedLCD L gamma (graphEffectiveLinear G c) →
          ∀ tau : ℝ,
            BooleanSlices.scale n (2 * gamma) /
                graphPerturbedSigma G e₀ c ≤ |tau| →
            |tau| ≤ alpha * BooleanSlices.scale n
                (1 / 2 + gamma / 8) / graphPerturbedSigma G e₀ c →
            ‖centeredGraphCharacteristic G e₀ c tau‖ ≤
              C' * BooleanSlices.scale n (-5)

theorem ksssLemma72_raw_unstructured : KSSSLemma72RawUnstructured := by
  intro C H gamma hC hH hgamma hgammaUpper
  dsimp only
  obtain ⟨alpha, C', halpha, hC', hraw⟩ :=
    ksssLemma72_raw C H gamma hC hH hgamma hgammaUpper
  refine ⟨alpha, C', halpha, hC', ?_⟩
  filter_upwards [hraw, Filter.eventually_ge_atTop 1] with n hrawN hn
  intro G e₀ c hG hc hlcd tau htLower htUpper
  apply hrawN G e₀ c hG hc tau htLower
  have hcutoff := scale_half_plus_gamma_eighth_le_lcd_cutoff
    hn hgamma.le hlcd
  have hmin : min
      (BooleanSlices.scale n (gamma / 2) *
        RLCD.regularizedLCD ((Nat.ceil (100 / gamma) : ℕ) : ℝ) gamma
          (graphEffectiveLinear G c))
      (BooleanSlices.scale n (1 / 2 + gamma / 8)) =
        BooleanSlices.scale n (1 / 2 + gamma / 8) :=
    min_eq_right hcutoff
  simpa only [hmin] using htUpper

end LinearLCDCancellation
end Erdos88
