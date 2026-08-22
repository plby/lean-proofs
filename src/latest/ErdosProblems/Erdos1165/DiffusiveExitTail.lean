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

import ErdosProblems.Erdos1165.ExitTail
import ErdosProblems.Erdos1165.SecondMoment

/-!
# A diffusive exponential exit tail

The forced-path estimate in `ExitTail.lean` has an exponentially small
one-block escape probability.  Here we prove the correct diffusive scale by a
fourth-moment argument.  The horizontal displacement `X_n` satisfies

`E X_n^2 = n/2`,  `E X_n^4 = (3n^2-n)/4`.

Paley--Zygmund therefore gives probability at least `3/16` that a block of
`32(R+1)^2` steps has horizontal displacement at least `2R+1`.  Such a block
must exit `[-R,R]^2`, regardless of its starting point in the box.  Iterating
independent blocks yields an exponential tail on the scale `N/R^2`.
-/

open MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal

namespace Erdos1165
namespace DiffusiveExitTail

open ExitTail Annulus SecondMoment

/-! ## Horizontal increments and their moments -/

/-- The horizontal coordinate of one lattice increment. -/
def horizontalStep (d : Direction) : ℝ := (directionVector d).1

/-- Horizontal displacement during the first `n` increments. -/
def horizontalDisplacement (n : ℕ) (omega : StepPath) : ℝ :=
  ∑ j : Fin n, horizontalStep (omega j)

/-- The horizontal increment at deterministic time `n`. -/
def horizontalIncrement (n : ℕ) (omega : StepPath) : ℝ := horizontalStep (omega n)

lemma horizontalDisplacement_succ (n : ℕ) (omega : StepPath) :
    horizontalDisplacement (n + 1) omega =
      horizontalDisplacement n omega + horizontalIncrement n omega := by
  rw [horizontalDisplacement, Fin.sum_univ_castSucc]
  rfl

lemma horizontalDisplacement_eq_trajectory_fst (n : ℕ) (omega : StepPath) :
    horizontalDisplacement n omega = (trajectory omega n).1 := by
  rw [horizontalDisplacement, trajectory, Prod.fst_sum]
  push_cast
  exact Fin.sum_univ_eq_sum_range (fun j => horizontalStep (omega j)) n

lemma measurable_horizontalDisplacement (n : ℕ) :
    Measurable (horizontalDisplacement n) := by
  unfold horizontalDisplacement
  fun_prop

lemma measurable_horizontalIncrement (n : ℕ) : Measurable (horizontalIncrement n) := by
  exact (measurable_of_countable horizontalStep).comp (measurable_pi_apply n)

lemma abs_horizontalStep_le_one (d : Direction) : |horizontalStep d| ≤ 1 := by
  fin_cases d <;> norm_num [horizontalStep, directionVector]

lemma abs_horizontalDisplacement_le (n : ℕ) (omega : StepPath) :
    |horizontalDisplacement n omega| ≤ n := by
  rw [horizontalDisplacement]
  calc
    |∑ j : Fin n, horizontalStep (omega j)| ≤
        ∑ j : Fin n, |horizontalStep (omega j)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _j : Fin n, (1 : ℝ) := by
      exact Finset.sum_le_sum fun j _ => abs_horizontalStep_le_one (omega j)
    _ = n := by simp

lemma integrable_horizontalDisplacement_pow (n k : ℕ) :
    Integrable (fun omega => horizontalDisplacement n omega ^ k) fairSteps := by
  refine Integrable.of_bound
    ((measurable_horizontalDisplacement n).pow_const k).aestronglyMeasurable
    ((n : ℝ) ^ k) (ae_of_all _ fun omega => ?_)
  rw [Real.norm_eq_abs, abs_pow]
  exact pow_le_pow_left₀ (abs_nonneg _) (abs_horizontalDisplacement_le n omega) k

lemma integrable_horizontalIncrement_pow (n k : ℕ) :
    Integrable (fun omega => horizontalIncrement n omega ^ k) fairSteps := by
  refine Integrable.of_bound
    ((measurable_horizontalIncrement n).pow_const k).aestronglyMeasurable
    1 (ae_of_all _ fun omega => ?_)
  rw [Real.norm_eq_abs, abs_pow]
  simpa [horizontalIncrement] using pow_le_pow_left₀ (abs_nonneg _)
    (abs_horizontalStep_le_one (omega n)) k

lemma integrable_horizontal_mixed_pow (n i j : ℕ) :
    Integrable (fun omega =>
      horizontalDisplacement n omega ^ i * horizontalIncrement n omega ^ j) fairSteps := by
  refine Integrable.of_bound
    (((measurable_horizontalDisplacement n).pow_const i).mul
      ((measurable_horizontalIncrement n).pow_const j)).aestronglyMeasurable
    ((n : ℝ) ^ i) (ae_of_all _ fun omega => ?_)
  rw [Real.norm_eq_abs, abs_mul, abs_pow, abs_pow]
  calc
    |horizontalDisplacement n omega| ^ i * |horizontalIncrement n omega| ^ j ≤
        (n : ℝ) ^ i * 1 ^ j := by
      gcongr
      · exact abs_horizontalDisplacement_le n omega
      · exact abs_horizontalStep_le_one (omega n)
    _ = (n : ℝ) ^ i := by simp

/-- Past horizontal displacement and the next horizontal increment are
independent. -/
lemma indepFun_horizontalDisplacement_horizontalIncrement (n : ℕ) :
    IndepFun (horizontalDisplacement n) (horizontalIncrement n) fairSteps := by
  let prefixSum : (Fin n → Direction) → ℝ :=
    fun u => ∑ j : Fin n, horizontalStep (u j)
  let nextStep : (Fin 1 → Direction) → ℝ := fun u => horizontalStep (u 0)
  have h := (indepFun_stepPrefix_stepBlock n 1).comp
    (measurable_of_countable prefixSum) (measurable_of_countable nextStep)
  change IndepFun
    (fun x : StepPath => ∑ j : Fin n, horizontalStep (x j))
    (fun x : StepPath => horizontalStep (x n)) fairSteps
  simpa [prefixSum, nextStep, Function.comp_def, stepPrefix, stepBlock] using h

lemma integral_horizontal_mixed_pow (n i j : ℕ) :
    (∫ omega, horizontalDisplacement n omega ^ i *
        horizontalIncrement n omega ^ j ∂fairSteps) =
      (∫ omega, horizontalDisplacement n omega ^ i ∂fairSteps) *
        ∫ omega, horizontalIncrement n omega ^ j ∂fairSteps := by
  have hind := (indepFun_horizontalDisplacement_horizontalIncrement n).comp
    (by fun_prop : Measurable fun x : ℝ => x ^ i)
    (by fun_prop : Measurable fun x : ℝ => x ^ j)
  simpa [Function.comp_def] using hind.integral_mul_eq_mul_integral
    ((measurable_horizontalDisplacement n).pow_const i).aestronglyMeasurable
    ((measurable_horizontalIncrement n).pow_const j).aestronglyMeasurable

lemma integrable_horizontal_mul_increment (n : ℕ) :
    Integrable (fun omega =>
      horizontalDisplacement n omega * horizontalIncrement n omega) fairSteps := by
  simpa only [pow_one] using integrable_horizontal_mixed_pow n 1 1

lemma integrable_horizontal_sq_mul_increment (n : ℕ) :
    Integrable (fun omega =>
      horizontalDisplacement n omega ^ 2 * horizontalIncrement n omega) fairSteps := by
  simpa only [pow_one] using integrable_horizontal_mixed_pow n 2 1

lemma integrable_horizontal_mul_increment_sq (n : ℕ) :
    Integrable (fun omega =>
      horizontalDisplacement n omega * horizontalIncrement n omega ^ 2) fairSteps := by
  simpa only [pow_one] using integrable_horizontal_mixed_pow n 1 2

lemma integrable_horizontal_cube_mul_increment (n : ℕ) :
    Integrable (fun omega =>
      horizontalDisplacement n omega ^ 3 * horizontalIncrement n omega) fairSteps := by
  simpa only [pow_one] using integrable_horizontal_mixed_pow n 3 1

lemma integrable_horizontal_mul_increment_cube (n : ℕ) :
    Integrable (fun omega =>
      horizontalDisplacement n omega * horizontalIncrement n omega ^ 3) fairSteps := by
  simpa only [pow_one] using integrable_horizontal_mixed_pow n 1 3

lemma integral_horizontal_mul_increment (n : ℕ) :
    (∫ omega, horizontalDisplacement n omega * horizontalIncrement n omega ∂fairSteps) =
      (∫ omega, horizontalDisplacement n omega ∂fairSteps) *
        ∫ omega, horizontalIncrement n omega ∂fairSteps := by
  simpa only [pow_one] using integral_horizontal_mixed_pow n 1 1

lemma integral_horizontal_sq_mul_increment (n : ℕ) :
    (∫ omega, horizontalDisplacement n omega ^ 2 * horizontalIncrement n omega ∂fairSteps) =
      (∫ omega, horizontalDisplacement n omega ^ 2 ∂fairSteps) *
        ∫ omega, horizontalIncrement n omega ∂fairSteps := by
  simpa only [pow_one] using integral_horizontal_mixed_pow n 2 1

lemma integral_horizontal_mul_increment_sq (n : ℕ) :
    (∫ omega, horizontalDisplacement n omega * horizontalIncrement n omega ^ 2 ∂fairSteps) =
      (∫ omega, horizontalDisplacement n omega ∂fairSteps) *
        ∫ omega, horizontalIncrement n omega ^ 2 ∂fairSteps := by
  simpa only [pow_one] using integral_horizontal_mixed_pow n 1 2

lemma integral_horizontal_cube_mul_increment (n : ℕ) :
    (∫ omega, horizontalDisplacement n omega ^ 3 * horizontalIncrement n omega ∂fairSteps) =
      (∫ omega, horizontalDisplacement n omega ^ 3 ∂fairSteps) *
        ∫ omega, horizontalIncrement n omega ∂fairSteps := by
  simpa only [pow_one] using integral_horizontal_mixed_pow n 3 1

lemma integral_horizontal_mul_increment_cube (n : ℕ) :
    (∫ omega, horizontalDisplacement n omega * horizontalIncrement n omega ^ 3 ∂fairSteps) =
      (∫ omega, horizontalDisplacement n omega ∂fairSteps) *
        ∫ omega, horizontalIncrement n omega ^ 3 ∂fairSteps := by
  simpa only [pow_one] using integral_horizontal_mixed_pow n 1 3

lemma integral_horizontalIncrement_pow (n k : ℕ) :
    (∫ omega, horizontalIncrement n omega ^ k ∂fairSteps) =
      ∫ d, horizontalStep d ^ k ∂fairStep := by
  calc
    (∫ omega, horizontalIncrement n omega ^ k ∂fairSteps) =
        ∫ d, horizontalStep d ^ k ∂fairSteps.map (fun omega : StepPath => omega n) := by
      rw [integral_map_of_stronglyMeasurable (measurable_pi_apply n)
        ((measurable_of_countable fun d : Direction => horizontalStep d ^ k).stronglyMeasurable)]
      rfl
    _ = ∫ d, horizontalStep d ^ k ∂fairStep := by rw [fairSteps_map_eval]

@[simp] lemma integral_horizontalIncrement_one (n : ℕ) :
    (∫ omega, horizontalIncrement n omega ∂fairSteps) = 0 := by
  simpa only [pow_one] using (integral_horizontalIncrement_pow n 1).trans (by
    rw [integral_fairStep, Fin.sum_univ_four]
    norm_num [horizontalStep, directionVector])

@[simp] lemma integral_horizontalIncrement_two (n : ℕ) :
    (∫ omega, horizontalIncrement n omega ^ 2 ∂fairSteps) = 1 / 2 := by
  rw [integral_horizontalIncrement_pow, integral_fairStep, Fin.sum_univ_four]
  norm_num [horizontalStep, directionVector]

@[simp] lemma integral_horizontalIncrement_three (n : ℕ) :
    (∫ omega, horizontalIncrement n omega ^ 3 ∂fairSteps) = 0 := by
  rw [integral_horizontalIncrement_pow, integral_fairStep, Fin.sum_univ_four]
  norm_num [horizontalStep, directionVector]

@[simp] lemma integral_horizontalIncrement_four (n : ℕ) :
    (∫ omega, horizontalIncrement n omega ^ 4 ∂fairSteps) = 1 / 2 := by
  rw [integral_horizontalIncrement_pow, integral_fairStep, Fin.sum_univ_four]
  norm_num [horizontalStep, directionVector]

lemma integral_horizontalDisplacement_one (n : ℕ) :
    (∫ omega, horizontalDisplacement n omega ∂fairSteps) = 0 := by
  induction n with
  | zero => simp [horizontalDisplacement]
  | succ n ih =>
      simp_rw [horizontalDisplacement_succ]
      rw [integral_add (integrable_horizontalDisplacement_pow n 1 |>.congr
        (ae_of_all _ fun omega => by simp))
        (integrable_horizontalIncrement_pow n 1 |>.congr
          (ae_of_all _ fun omega => by simp))]
      rw [ih, integral_horizontalIncrement_one]
      norm_num

lemma integral_horizontalDisplacement_two (n : ℕ) :
    (∫ omega, horizontalDisplacement n omega ^ 2 ∂fairSteps) = n / 2 := by
  induction n with
  | zero => simp [horizontalDisplacement]
  | succ n ih =>
      have hexpand : (fun omega => horizontalDisplacement (n + 1) omega ^ 2) =
          fun omega => horizontalDisplacement n omega ^ 2 +
            2 * (horizontalDisplacement n omega * horizontalIncrement n omega) +
              horizontalIncrement n omega ^ 2 := by
        funext omega
        rw [horizontalDisplacement_succ]
        ring
      rw [hexpand, integral_add]
      · rw [integral_add]
        · rw [integral_const_mul, integral_horizontal_mul_increment,
            integral_horizontalDisplacement_one,
            integral_horizontalIncrement_one, ih, integral_horizontalIncrement_two]
          push_cast
          ring
        · exact integrable_horizontalDisplacement_pow n 2
        · exact (integrable_horizontal_mul_increment n).const_mul 2
      · exact (integrable_horizontalDisplacement_pow n 2).add
          ((integrable_horizontal_mul_increment n).const_mul 2)
      · exact integrable_horizontalIncrement_pow n 2

lemma integral_horizontalDisplacement_three (n : ℕ) :
    (∫ omega, horizontalDisplacement n omega ^ 3 ∂fairSteps) = 0 := by
  induction n with
  | zero => simp [horizontalDisplacement]
  | succ n ih =>
      have hexpand : (fun omega => horizontalDisplacement (n + 1) omega ^ 3) =
          fun omega => horizontalDisplacement n omega ^ 3 +
            3 * (horizontalDisplacement n omega ^ 2 * horizontalIncrement n omega) +
            3 * (horizontalDisplacement n omega * horizontalIncrement n omega ^ 2) +
            horizontalIncrement n omega ^ 3 := by
        funext omega
        rw [horizontalDisplacement_succ]
        ring
      rw [hexpand, integral_add]
      · rw [integral_add]
        · rw [integral_add]
          · rw [integral_const_mul, integral_const_mul,
              integral_horizontal_sq_mul_increment, integral_horizontal_mul_increment_sq,
              integral_horizontalIncrement_one, integral_horizontalDisplacement_one,
              integral_horizontalIncrement_two, ih, integral_horizontalIncrement_three]
            norm_num
          · exact integrable_horizontalDisplacement_pow n 3
          · exact (integrable_horizontal_sq_mul_increment n).const_mul 3
        · exact (integrable_horizontalDisplacement_pow n 3).add
            ((integrable_horizontal_sq_mul_increment n).const_mul 3)
        · exact (integrable_horizontal_mul_increment_sq n).const_mul 3
      · exact ((integrable_horizontalDisplacement_pow n 3).add
          ((integrable_horizontal_sq_mul_increment n).const_mul 3)).add
            ((integrable_horizontal_mul_increment_sq n).const_mul 3)
      · exact integrable_horizontalIncrement_pow n 3

/-- Exact fourth moment of the horizontal coordinate. -/
theorem integral_horizontalDisplacement_four (n : ℕ) :
    (∫ omega, horizontalDisplacement n omega ^ 4 ∂fairSteps) =
      (3 * (n : ℝ) ^ 2 - n) / 4 := by
  induction n with
  | zero => simp [horizontalDisplacement]
  | succ n ih =>
      have hexpand : (fun omega => horizontalDisplacement (n + 1) omega ^ 4) =
          fun omega => horizontalDisplacement n omega ^ 4 +
            4 * (horizontalDisplacement n omega ^ 3 * horizontalIncrement n omega) +
            6 * (horizontalDisplacement n omega ^ 2 * horizontalIncrement n omega ^ 2) +
            4 * (horizontalDisplacement n omega * horizontalIncrement n omega ^ 3) +
            horizontalIncrement n omega ^ 4 := by
        funext omega
        rw [horizontalDisplacement_succ]
        ring
      rw [hexpand, integral_add]
      · rw [integral_add]
        · rw [integral_add]
          · rw [integral_add]
            · rw [integral_const_mul, integral_const_mul, integral_const_mul,
                integral_horizontal_cube_mul_increment, integral_horizontal_mixed_pow,
                integral_horizontal_mul_increment_cube, integral_horizontalIncrement_one,
                integral_horizontalDisplacement_one, integral_horizontalIncrement_two,
                integral_horizontalIncrement_three, integral_horizontalDisplacement_two,
                ih, integral_horizontalIncrement_four]
              push_cast
              ring
            · exact integrable_horizontalDisplacement_pow n 4
            · exact (integrable_horizontal_cube_mul_increment n).const_mul 4
          · exact (integrable_horizontalDisplacement_pow n 4).add
              ((integrable_horizontal_cube_mul_increment n).const_mul 4)
          · exact (integrable_horizontal_mixed_pow n 2 2).const_mul 6
        · exact ((integrable_horizontalDisplacement_pow n 4).add
            ((integrable_horizontal_cube_mul_increment n).const_mul 4)).add
              ((integrable_horizontal_mixed_pow n 2 2).const_mul 6)
        · exact (integrable_horizontal_mul_increment_cube n).const_mul 4
      · exact (((integrable_horizontalDisplacement_pow n 4).add
          ((integrable_horizontal_cube_mul_increment n).const_mul 4)).add
            ((integrable_horizontal_mixed_pow n 2 2).const_mul 6)).add
              ((integrable_horizontal_mul_increment_cube n).const_mul 4)
      · exact integrable_horizontalIncrement_pow n 4

/-! ## One diffusive block has a fixed escape probability -/

/-- A block length of order `R^2`. -/
def diffusiveBlockLength (R : ℕ) : ℕ := 32 * (R + 1) ^ 2

lemma diffusiveBlockLength_pos (R : ℕ) : 0 < diffusiveBlockLength R := by
  simp [diffusiveBlockLength]

/-- A horizontal displacement large enough to force exit from `[-R,R]^2`. -/
def largeHorizontalDisplacement (R N : ℕ) : Set StepPath :=
  {omega | (2 * R + 1 : ℝ) ≤ |horizontalDisplacement N omega|}

lemma measurableSet_largeHorizontalDisplacement (R N : ℕ) :
    MeasurableSet (largeHorizontalDisplacement R N) := by
  exact measurableSet_le measurable_const (measurable_horizontalDisplacement N).abs

/-- Paley--Zygmund gives a scale-independent probability of moving farther
than the diameter of the box in one diffusive block. -/
theorem measureReal_largeHorizontalDisplacement_diffusiveBlock_lower (R : ℕ) :
    3 / 16 ≤ fairSteps.real
      (largeHorizontalDisplacement R (diffusiveBlockLength R)) := by
  let M := diffusiveBlockLength R
  let X : StepPath → ℝ := horizontalDisplacement M
  let Z : StepPath → ℝ := fun omega => X omega ^ 2
  have hM : (0 : ℝ) < M := by exact_mod_cast diffusiveBlockLength_pos R
  have hZ : 0 ≤ Z := fun omega => sq_nonneg _
  have hZmeas : Measurable Z := (measurable_horizontalDisplacement M).pow_const 2
  have hZint : Integrable Z fairSteps := integrable_horizontalDisplacement_pow M 2
  have hZ2 : Integrable (fun omega => Z omega ^ 2) fairSteps := by
    convert integrable_horizontalDisplacement_pow M 4 using 1
    funext omega
    dsimp [Z, X]
    ring
  have hmean : (∫ omega, Z omega ∂fairSteps) = M / 2 :=
    integral_horizontalDisplacement_two M
  have hsecond : (∫ omega, Z omega ^ 2 ∂fairSteps) =
      (3 * (M : ℝ) ^ 2 - M) / 4 := by
    rw [show (fun omega => Z omega ^ 2) =
      fun omega => horizontalDisplacement M omega ^ 4 by
        funext omega; dsimp [Z, X]; ring]
    exact integral_horizontalDisplacement_four M
  have hsecond_pos : 0 < ∫ omega, Z omega ^ 2 ∂fairSteps := by
    rw [hsecond]
    have hMone : (1 : ℝ) ≤ M := by exact_mod_cast (diffusiveBlockLength_pos R)
    nlinarith
  have hpaley := paleyZygmund_ratio (mu := fairSteps) Z hZ hZmeas hZint hZ2
    hsecond_pos (theta := (1 / 4 : ℝ)) (by norm_num) (by norm_num)
  have hratio : (3 / 16 : ℝ) ≤
      (((1 - (1 / 4 : ℝ)) * ∫ omega, Z omega ∂fairSteps) ^ 2) /
        (∫ omega, Z omega ^ 2 ∂fairSteps) := by
    rw [le_div_iff₀ hsecond_pos, hmean, hsecond]
    nlinarith [sq_nonneg (M : ℝ)]
  have hthreshold : {omega | (1 / 4 : ℝ) * (∫ omega, Z omega ∂fairSteps) ≤ Z omega} ⊆
      largeHorizontalDisplacement R M := by
    intro omega homega
    rw [hmean] at homega
    have hscale : ((2 * R + 1 : ℕ) : ℝ) ^ 2 ≤ (1 / 4 : ℝ) * (M / 2) := by
      dsimp [M, diffusiveBlockLength]
      push_cast
      have hR : (0 : ℝ) ≤ R := by positivity
      nlinarith [sq_nonneg (R : ℝ)]
    have hsquare : ((2 * R + 1 : ℕ) : ℝ) ^ 2 ≤ Z omega := hscale.trans homega
    push_cast at hsquare
    dsimp [largeHorizontalDisplacement, Z, X]
    apply (sq_le_sq₀ (by positivity) (abs_nonneg _)).mp
    simpa only [sq_abs] using hsquare
  exact hratio.trans (hpaley.trans (measureReal_mono hthreshold))

/-! ## Independent block amplification -/

/-- Horizontal displacement of a finite increment word. -/
def wordHorizontalDisplacement {N : ℕ} (u : Fin N → Direction) : ℝ :=
  ∑ j : Fin N, horizontalStep (u j)

/-- Finite block words which move horizontally by at least `2R+1`. -/
def largeHorizontalWords (R N : ℕ) : Set (Fin N → Direction) :=
  {u | (2 * R + 1 : ℝ) ≤ |wordHorizontalDisplacement u|}

lemma fairSteps_map_stepPrefix (N : ℕ) :
    fairSteps.map (stepPrefix N) = fairBlock N := by
  rw [← fairSteps_map_stepBlock 0 N]
  congr 1
  funext omega j
  simp [stepPrefix, stepBlock]

lemma fairBlock_largeHorizontalWords_lower (R : ℕ) :
    (3 / 16 : ℝ) ≤ (fairBlock (diffusiveBlockLength R)).real
      (largeHorizontalWords R (diffusiveBlockLength R)) := by
  have hmap := congrArg (fun mu : Measure (Fin (diffusiveBlockLength R) → Direction) =>
      mu.real (largeHorizontalWords R (diffusiveBlockLength R)))
    (fairSteps_map_stepPrefix (diffusiveBlockLength R))
  have hpre : stepPrefix (diffusiveBlockLength R) ⁻¹'
      largeHorizontalWords R (diffusiveBlockLength R) =
        largeHorizontalDisplacement R (diffusiveBlockLength R) := by
    ext omega
    rfl
  rw [map_measureReal_apply (measurable_stepPrefix _) (Set.to_countable _).measurableSet,
    hpre] at hmap
  rw [← hmap]
  exact measureReal_largeHorizontalDisplacement_diffusiveBlock_lower R

/-- Real-measure factorization for a prefix event and a disjoint following
block event. -/
lemma measureReal_stepPrefix_inter_stepBlock
    (n M : ℕ) (A : Set (Fin n → Direction)) (C : Set (Fin M → Direction))
    (hA : MeasurableSet A) (hC : MeasurableSet C) :
    fairSteps.real (stepPrefix n ⁻¹' A ∩ stepBlock n M ⁻¹' C) =
      fairSteps.real (stepPrefix n ⁻¹' A) * (fairBlock M).real C := by
  have hind :=
    (indepFun_stepPrefix_stepBlock n M).measure_inter_preimage_eq_mul A C hA hC
  have hblock : fairSteps.real (stepBlock n M ⁻¹' C) = (fairBlock M).real C := by
    calc
      fairSteps.real (stepBlock n M ⁻¹' C) =
          (fairSteps.map (stepBlock n M)).real C :=
        (map_measureReal_apply (μ := fairSteps) (measurable_stepBlock n M) hC).symm
      _ = (fairBlock M).real C := by rw [fairSteps_map_stepBlock]
  have hreal := congrArg ENNReal.toReal hind
  rw [ENNReal.toReal_mul] at hreal
  change fairSteps.real (stepPrefix n ⁻¹' A ∩ stepBlock n M ⁻¹' C) =
    fairSteps.real (stepPrefix n ⁻¹' A) * fairSteps.real (stepBlock n M ⁻¹' C) at hreal
  rw [hblock] at hreal
  exact hreal

/-- Survival for another diffusive block excludes a large horizontal block
word. -/
lemma stays_diffusive_succBlock_subset (a : Point) (R q : ℕ) :
    staysInCoordinateBoxThrough a R (diffusiveBlockLength R * (q + 1)) ⊆
      staysInCoordinateBoxThrough a R (diffusiveBlockLength R * q) ∩
        stepBlock (diffusiveBlockLength R * q) (diffusiveBlockLength R) ⁻¹'
          (largeHorizontalWords R (diffusiveBlockLength R))ᶜ := by
  intro omega homega
  let M := diffusiveBlockLength R
  let n := M * q
  have hnle : n ≤ M * (q + 1) := Nat.mul_le_mul_left M (Nat.le_succ q)
  have hprefix : omega ∈ staysInCoordinateBoxThrough a R n := fun k hk =>
    homega k (hk.trans (by simpa [n, M] using hnle))
  refine ⟨hprefix, ?_⟩
  intro hlarge
  have hnmem := hprefix n le_rfl
  have hendmem : a + trajectory omega (n + M) ∈ coordinateBox R := by
    apply homega
    simp [n, M, Nat.mul_succ]
  rw [mem_coordinateBox] at hnmem hendmem
  have hdisp : horizontalDisplacement M (shiftSteps n omega) =
      (trajectory omega (n + M)).1 - (trajectory omega n).1 := by
    rw [horizontalDisplacement_eq_trajectory_fst]
    have hz := congrArg Prod.fst (trajectory_add_sub_trajectory omega n M)
    change (trajectory omega (n + M)).1 - (trajectory omega n).1 =
      (trajectory (shiftSteps n omega) M).1 at hz
    exact_mod_cast hz.symm
  have hword : wordHorizontalDisplacement (stepBlock n M omega) =
      horizontalDisplacement M (shiftSteps n omega) := by
    rfl
  rw [show diffusiveBlockLength R * q = n by rfl,
    show diffusiveBlockLength R = M by rfl] at hlarge
  change (2 * R + 1 : ℝ) ≤
    |wordHorizontalDisplacement (stepBlock n M omega)| at hlarge
  rw [hword, hdisp] at hlarge
  have hx1 : |((a + trajectory omega (n + M)).1 : ℝ) -
      (a + trajectory omega n).1| ≤ 2 * R := by
    have hnlo : -(R : ℝ) ≤ ((a + trajectory omega n).1 : ℝ) := by
      exact_mod_cast hnmem.1
    have hnhi : ((a + trajectory omega n).1 : ℝ) ≤ R := by
      exact_mod_cast hnmem.2.1
    have hendlo : -(R : ℝ) ≤ ((a + trajectory omega (n + M)).1 : ℝ) := by
      exact_mod_cast hendmem.1
    have hendhi : ((a + trajectory omega (n + M)).1 : ℝ) ≤ R := by
      exact_mod_cast hendmem.2.1
    rw [abs_le]
    constructor <;> linarith
  have heq : ((a + trajectory omega (n + M)).1 : ℝ) -
      (a + trajectory omega n).1 =
      (trajectory omega (n + M)).1 - (trajectory omega n).1 := by
    have heqInt : (a + trajectory omega (n + M)).1 -
        (a + trajectory omega n).1 =
        (trajectory omega (n + M)).1 - (trajectory omega n).1 := by
      simp
    exact_mod_cast heqInt
  rw [heq] at hx1
  linarith

/-- Geometric survival bound with a fixed `13/16` failure factor per
diffusive block. -/
theorem measureReal_staysInCoordinateBoxThrough_diffusive_le_geometric
    (a : Point) (R q : ℕ) :
    fairSteps.real
        (staysInCoordinateBoxThrough a R (diffusiveBlockLength R * q)) ≤
      (13 / 16 : ℝ) ^ q := by
  induction q with
  | zero =>
      have h := measureReal_mono (μ := fairSteps)
        (show staysInCoordinateBoxThrough a R (diffusiveBlockLength R * 0) ⊆ Set.univ
          from Set.subset_univ _) (by finiteness)
      calc
        fairSteps.real
            (staysInCoordinateBoxThrough a R (diffusiveBlockLength R * 0)) ≤
            fairSteps.real Set.univ := h
        _ = (13 / 16 : ℝ) ^ 0 := by simp
  | succ q ih =>
      let n := diffusiveBlockLength R * q
      let M := diffusiveBlockLength R
      have hfactor : fairSteps.real
          (staysInCoordinateBoxThrough a R n ∩
            stepBlock n M ⁻¹' (largeHorizontalWords R M)ᶜ) =
          fairSteps.real (staysInCoordinateBoxThrough a R n) *
            (fairBlock M).real (largeHorizontalWords R M)ᶜ := by
        rw [staysInCoordinateBoxThrough_eq_preimage]
        exact measureReal_stepPrefix_inter_stepBlock n M
          (survivalPrefixSet a R n) (largeHorizontalWords R M)ᶜ
          (Set.to_countable _).measurableSet (Set.to_countable _).measurableSet
      have hcompl : (fairBlock M).real (largeHorizontalWords R M)ᶜ ≤ 13 / 16 := by
        rw [measureReal_compl (Set.to_countable _).measurableSet]
        have hlower := fairBlock_largeHorizontalWords_lower R
        have hone : (fairBlock M).real Set.univ = 1 := by simp
        rw [hone]
        dsimp [M]
        linarith
      calc
        fairSteps.real
            (staysInCoordinateBoxThrough a R (diffusiveBlockLength R * (q + 1))) ≤
            fairSteps.real
              (staysInCoordinateBoxThrough a R n ∩
                stepBlock n M ⁻¹' (largeHorizontalWords R M)ᶜ) := by
          exact measureReal_mono
            (by simpa [n, M] using stays_diffusive_succBlock_subset a R q)
            (by finiteness)
        _ = fairSteps.real (staysInCoordinateBoxThrough a R n) *
              (fairBlock M).real (largeHorizontalWords R M)ᶜ := hfactor
        _ ≤ (13 / 16 : ℝ) ^ q * (13 / 16 : ℝ) := by
          gcongr
        _ = (13 / 16 : ℝ) ^ (q + 1) := by rw [pow_succ]

/-- Exponential form at integer multiples of the diffusive block length. -/
theorem measureReal_staysInCoordinateBoxThrough_diffusive_le_exp
    (a : Point) (R q : ℕ) :
    fairSteps.real
        (staysInCoordinateBoxThrough a R (diffusiveBlockLength R * q)) ≤
      Real.exp (-(3 / 16 : ℝ) * q) := by
  calc
    fairSteps.real
        (staysInCoordinateBoxThrough a R (diffusiveBlockLength R * q)) ≤
        (13 / 16 : ℝ) ^ q :=
      measureReal_staysInCoordinateBoxThrough_diffusive_le_geometric a R q
    _ = (1 - (3 / 16 : ℝ)) ^ q := by
      congr 1
      norm_num
    _ ≤ (Real.exp (-(3 / 16 : ℝ))) ^ q := by
      exact pow_le_pow_left₀ (by norm_num) (Real.one_sub_le_exp_neg (3 / 16)) q
    _ = Real.exp (-(3 / 16 : ℝ) * q) := by
      rw [← Real.exp_nat_mul]
      congr 1
      ring

/-- Arbitrary-time diffusive exponential tail, with the number of complete
blocks made explicit. -/
theorem measureReal_staysInCoordinateBoxThrough_diffusive_le_exp_div
    (a : Point) (R N : ℕ) :
    fairSteps.real (staysInCoordinateBoxThrough a R N) ≤
      Real.exp (-(3 / 16 : ℝ) * (N / diffusiveBlockLength R : ℕ)) := by
  have htime : diffusiveBlockLength R * (N / diffusiveBlockLength R) ≤ N := by
    simpa [Nat.mul_comm] using Nat.div_mul_le_self N (diffusiveBlockLength R)
  calc
    fairSteps.real (staysInCoordinateBoxThrough a R N) ≤
        fairSteps.real (staysInCoordinateBoxThrough a R
          (diffusiveBlockLength R * (N / diffusiveBlockLength R))) := by
      exact measureReal_mono (fun omega homega k hk => homega k (hk.trans htime))
        (by finiteness)
    _ ≤ Real.exp (-(3 / 16 : ℝ) * (N / diffusiveBlockLength R : ℕ)) :=
      measureReal_staysInCoordinateBoxThrough_diffusive_le_exp a R _

/-- Closed-disc survival has the same diffusive tail because the disc is
contained in the coordinate box. -/
theorem measureReal_staysInClosedDiscThrough_diffusive_le_exp_div
    (a : Point) (R N : ℕ) :
    fairSteps.real (staysInClosedDiscThrough a R N) ≤
      Real.exp (-(3 / 16 : ℝ) * (N / diffusiveBlockLength R : ℕ)) :=
  (measureReal_mono (staysInClosedDiscThrough_subset_box a R N)).trans
    (measureReal_staysInCoordinateBoxThrough_diffusive_le_exp_div a R N)

end DiffusiveExitTail
end Erdos1165
