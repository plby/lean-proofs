/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex, Boris Alexeev
-/
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Normed.Group.Constructions
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic
import ErdosProblems.Erdos228.GaussianWalk
import ErdosProblems.Erdos228.Martingale
import ErdosProblems.Erdos228.ProjectionWalk

/-!
# The finite discrepancy input for Erdős Problem 228

This file isolates the finite-dimensional colouring result used in Section 4
of Balister--Bollobás--Morris--Sahasrabudhe--Tiba.  Vectors are represented by
functions on a finite coordinate type.  The norm on such a function is the
supremum norm, while `l2Norm` is defined explicitly.

The elementary lemmas below are independent of the probabilistic partial
colouring argument.  In particular, `nearestSign` gives the terminal estimate
used for dimensions at most `900`, and `l2Norm_le_sqrt_card_mul_norm` is the
norm comparison used at each partial-colouring step.
-/

open scoped BigOperators

noncomputable section

namespace Erdos228.Discrepancy

variable {I J : Type*} [Fintype I] [Fintype J]

/-- The coordinate dot product on a finite function space. -/
def dot (x v : I → ℝ) : ℝ := ∑ i, x i * v i

theorem dot_add_left (x y v : I → ℝ) :
    dot (x + y) v = dot x v + dot y v := by
  simp only [dot, Pi.add_apply, add_mul, Finset.sum_add_distrib]

theorem dot_sub_left (x y v : I → ℝ) :
    dot (x - y) v = dot x v - dot y v := by
  simp only [dot, Pi.sub_apply, sub_mul, Finset.sum_sub_distrib]

/-- Membership in the closed coordinate cube `[-1,1]^I`. -/
def InCube (x : I → ℝ) : Prop := ∀ i, |x i| ≤ 1

/-- A vertex of the coordinate cube. -/
def IsSign (x : I → ℝ) : Prop := ∀ i, x i = 1 ∨ x i = -1

/-- The Euclidean norm, kept separate from the supremum norm on functions. -/
def l2Norm (v : I → ℝ) : ℝ := Real.sqrt (∑ i, (v i) ^ 2)

/-- Regard an ordinary coordinate function as the corresponding Euclidean
vector used by the projected Gaussian walk. -/
def toWalkSpace (x : I → ℝ) : ProjectionWalk.WalkSpace I :=
  WithLp.toLp 2 x

@[simp] theorem toWalkSpace_apply (x : I → ℝ) (i : I) :
    toWalkSpace x i = x i := rfl

/-- Bridge between the elementary dot product in this file and Mathlib's
Euclidean inner product used by `ProjectionWalk`. -/
theorem inner_toWalkSpace (x v : I → ℝ) :
    inner ℝ (toWalkSpace v) (toWalkSpace x) = dot x v := by
  simp [toWalkSpace, PiLp.inner_apply, dot, RCLike.inner_apply]

/-- The explicit Euclidean norm agrees with the norm of the bundled walk
space. -/
theorem norm_toWalkSpace (v : I → ℝ) : ‖toWalkSpace v‖ = l2Norm v := by
  rw [EuclideanSpace.norm_eq]
  simp only [toWalkSpace_apply, Real.norm_eq_abs, sq_abs, l2Norm]

/-- The explicit Euclidean norm vanishes exactly on the zero row.  This is
the degenerate case needed when normalized discrepancy rows are converted
back to the unnormalized formulation. -/
theorem l2Norm_eq_zero_iff (v : I → ℝ) : l2Norm v = 0 ↔ v = 0 := by
  rw [← norm_toWalkSpace, norm_eq_zero]
  constructor
  · intro h
    funext i
    have hi := congrArg (fun x : ProjectionWalk.WalkSpace I ↦ x i) h
    simpa [toWalkSpace] using hi
  · rintro rfl
    rfl

/-- A zero-length discrepancy row contributes the zero linear form. -/
theorem dot_eq_zero_of_l2Norm_eq_zero (x v : I → ℝ)
    (hv : l2Norm v = 0) : dot x v = 0 := by
  rw [(l2Norm_eq_zero_iff v).mp hv]
  simp [dot]

theorem l2Norm_pos_iff (v : I → ℝ) : 0 < l2Norm v ↔ v ≠ 0 := by
  constructor
  · intro hv hzero
    subst v
    simp [l2Norm] at hv
  · intro hv
    exact lt_of_le_of_ne (Real.sqrt_nonneg _)
      (Ne.symm fun hzero ↦ hv ((l2Norm_eq_zero_iff v).mp hzero))

/-- Normalize a nonzero discrepancy row; the zero row is left zero by the
field convention for inversion. -/
def normalizedRow (v : I → ℝ) : I → ℝ :=
  fun i ↦ (l2Norm v)⁻¹ * v i

/-- Rescaling a normalized dot product recovers the original linear form. -/
theorem dot_normalizedRow_mul_l2Norm (x v : I → ℝ)
    (hv : l2Norm v ≠ 0) :
    dot x (normalizedRow v) * l2Norm v = dot x v := by
  simp only [dot, normalizedRow]
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i hi
  field_simp

/-- Variance proxy of a linear form of one projected Rademacher increment. -/
noncomputable def projectedVarianceProxy {K : Type*}
    (w : K → ProjectionWalk.WalkSpace I) (u : ProjectionWalk.WalkSpace I) : NNReal :=
  ∑ i : I, NNReal.mk ((ProjectionWalk.projectIncrement w u i) ^ 2)
    (sq_nonneg (ProjectionWalk.projectIncrement w u i))

/-- A projected random-sign increment is sub-Gaussian in every fixed
direction.  This is the conditional one-step estimate needed by the
Rademacher version of the edge walk. -/
theorem hasSubgaussianMGF_inner_projectedRademacher {K : Type*}
    (w : K → ProjectionWalk.WalkSpace I) (u : ProjectionWalk.WalkSpace I) :
    ProbabilityTheory.HasSubgaussianMGF
      (fun r : I → ℝ ↦ inner ℝ u
        (ProjectionWalk.projectIncrement w (toWalkSpace r)))
      (projectedVarianceProxy w u) (GaussianWalk.rademacherProduct I) := by
  let a : I → ℝ := fun i ↦ ProjectionWalk.projectIncrement w u i
  have h := GaussianWalk.hasSubgaussianMGF_weightedRademacherSum I a
  have hfun :
      (fun r : I → ℝ ↦ inner ℝ u
        (ProjectionWalk.projectIncrement w (toWalkSpace r))) =
        (fun r : I → ℝ ↦ ∑ i, a i * r i) := by
    funext r
    calc
      inner ℝ u (ProjectionWalk.projectIncrement w (toWalkSpace r)) =
          inner ℝ (ProjectionWalk.projectIncrement w u) (toWalkSpace r) := by
        symm
        exact (ProjectionWalk.incrementSubspace w).inner_starProjection_left_eq_right
          u (toWalkSpace r)
      _ = ∑ i, a i * r i := by
        simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial,
          toWalkSpace_apply, a]
        apply Finset.sum_congr rfl
        intro i _
        ring
  rw [hfun]
  convert h using 1
  apply Finset.sum_congr rfl
  intro i hi
  apply NNReal.eq
  rfl

/-- Orthogonal projection can only decrease the one-step variance proxy. -/
theorem coe_projectedVarianceProxy_le_norm_sq {K : Type*}
    (w : K → ProjectionWalk.WalkSpace I) (u : ProjectionWalk.WalkSpace I) :
    (projectedVarianceProxy w u : ℝ) ≤ ‖u‖ ^ 2 := by
  simp only [projectedVarianceProxy, NNReal.coe_sum, NNReal.coe_mk]
  rw [← EuclideanSpace.real_norm_sq_eq]
  have h := ProjectionWalk.norm_projectIncrement_le w u
  nlinarith [norm_nonneg (ProjectionWalk.projectIncrement w u), norm_nonneg u]

/-- Coordinates which have reached a face of the cube. -/
def fixedCoordinates [DecidableEq I] (x : I → ℝ) : Finset I :=
  Finset.univ.filter fun i ↦ |x i| = 1

/-- Dot product restricted to a finite set of coordinates. -/
def dotOn (F : Finset I) (x v : I → ℝ) : ℝ :=
  ∑ i ∈ F, x i * v i

/-- Restrict a vector to the coordinates in `F`. -/
def restrict (F : Finset I) (x : I → ℝ) : F → ℝ := fun i ↦ x i

/-- Restrict a vector to the coordinates outside `F`. -/
def restrictOutside [DecidableEq I] (F : Finset I) (x : I → ℝ) :
    ↥(Fᶜ : Finset I) → ℝ := fun i ↦ x i

/-- Glue vectors on a finite coordinate set and its complement. -/
def glue [DecidableEq I] (F : Finset I) (xF : F → ℝ)
    (xOutside : ↥(Fᶜ : Finset I) → ℝ) : I → ℝ :=
  fun i ↦ if hi : i ∈ F then xF ⟨i, hi⟩ else xOutside ⟨i, by simp [hi]⟩

theorem IsSign.inCube {x : I → ℝ} (hx : IsSign x) : InCube x := by
  intro i
  rcases hx i with hi | hi <;> simp [hi]

section Glue

variable [DecidableEq I] (F : Finset I)

@[simp] theorem glue_apply_mem (xF : F → ℝ)
    (xOutside : ↥(Fᶜ : Finset I) → ℝ) {i : I} (hi : i ∈ F) :
    glue F xF xOutside i = xF ⟨i, hi⟩ := by
  simp [glue, hi]

@[simp] theorem glue_apply_not_mem (xF : F → ℝ)
    (xOutside : ↥(Fᶜ : Finset I) → ℝ) {i : I} (hi : i ∉ F) :
    glue F xF xOutside i = xOutside ⟨i, by simp [hi]⟩ := by
  simp [glue, hi]

@[simp] theorem restrict_glue (xF : F → ℝ)
    (xOutside : ↥(Fᶜ : Finset I) → ℝ) :
    restrict F (glue F xF xOutside) = xF := by
  funext i
  simp [restrict]

@[simp] theorem restrictOutside_glue (xF : F → ℝ)
    (xOutside : ↥(Fᶜ : Finset I) → ℝ) :
    restrictOutside F (glue F xF xOutside) = xOutside := by
  funext i
  have hi : (i : I) ∉ F := Finset.mem_compl.mp i.property
  change glue F xF xOutside i = xOutside i
  rw [glue_apply_not_mem F xF xOutside hi]

@[simp] theorem glue_restrict (x : I → ℝ) :
    glue F (restrict F x) (restrictOutside F x) = x := by
  funext i
  by_cases hi : i ∈ F <;> simp [glue, restrict, restrictOutside, hi]

theorem isSign_restrict {x : I → ℝ} (hx : IsSign x) :
    IsSign (restrict F x) := fun i ↦ hx i

theorem isSign_restrictOutside {x : I → ℝ} (hx : IsSign x) :
    IsSign (restrictOutside F x) := fun i ↦ hx i

theorem isSign_glue {xF : F → ℝ} {xOutside : ↥(Fᶜ : Finset I) → ℝ}
    (hF : IsSign xF) (hOutside : IsSign xOutside) :
    IsSign (glue F xF xOutside) := by
  intro i
  by_cases hi : i ∈ F
  · simpa [glue, hi] using hF ⟨i, hi⟩
  · simpa [glue, hi] using hOutside ⟨i, Finset.mem_compl.mpr hi⟩

theorem inCube_restrict {x : I → ℝ} (hx : InCube x) :
    InCube (restrict F x) := fun i ↦ hx i

theorem inCube_restrictOutside {x : I → ℝ} (hx : InCube x) :
    InCube (restrictOutside F x) := fun i ↦ hx i

theorem inCube_glue {xF : F → ℝ} {xOutside : ↥(Fᶜ : Finset I) → ℝ}
    (hF : InCube xF) (hOutside : InCube xOutside) :
    InCube (glue F xF xOutside) := by
  intro i
  by_cases hi : i ∈ F
  · simpa [glue, hi] using hF ⟨i, hi⟩
  · simpa [glue, hi] using hOutside ⟨i, Finset.mem_compl.mpr hi⟩

end Glue

section RestrictedDot

variable [DecidableEq I]

theorem dot_eq_dotOn_add_dotOn_compl (F : Finset I) (x v : I → ℝ) :
    dot x v = dotOn F x v + dotOn Fᶜ x v := by
  simpa only [dot, dotOn] using
    (F.sum_add_sum_compl (fun i ↦ x i * v i)).symm

theorem dotOn_eq_dot_restrict (F : Finset I) (x v : I → ℝ) :
    dotOn F x v = dot (restrict F x) (restrict F v) := by
  rw [dotOn, dot, ← Finset.sum_attach]
  simp [restrict]

theorem dot_glue (F : Finset I) (xF : F → ℝ)
    (xOutside : ↥(Fᶜ : Finset I) → ℝ) (v : I → ℝ) :
    dot (glue F xF xOutside) v =
      dot xF (restrict F v) + dot xOutside (restrictOutside F v) := by
  rw [dot_eq_dotOn_add_dotOn_compl F]
  congr 1
  · rw [dotOn, dot, ← Finset.sum_attach]
    simp [glue, restrict]
  · rw [dotOn, dot, ← Finset.sum_attach]
    apply Finset.sum_congr rfl
    intro i _
    have hi : (i : I) ∉ F := Finset.mem_compl.mp i.property
    simp [glue, restrictOutside, hi]

theorem dot_restrict_add_outside (F : Finset I) (x v : I → ℝ) :
    dot x v = dot (restrict F x) (restrict F v) +
      dot (restrictOutside F x) (restrictOutside F v) := by
  simpa using dot_glue F (restrict F x) (restrictOutside F x) v

theorem dot_glue_sub_same_outside (F : Finset I) (xF yF : F → ℝ)
    (xOutside : ↥(Fᶜ : Finset I) → ℝ) (v : I → ℝ) :
    dot (glue F xF xOutside) v - dot (glue F yF xOutside) v =
      dot xF (restrict F v) - dot yF (restrict F v) := by
  rw [dot_glue, dot_glue]
  linarith

/-- Error decomposition used in the full-colouring induction: freezing `F`
at `x₁` and recolouring its complement adds exactly the complementary error. -/
theorem dot_glue_sub_reference (F : Finset I) (x₁ x₀ : I → ℝ)
    (y : ↥(Fᶜ : Finset I) → ℝ) (v : I → ℝ) :
    dot (glue F (restrict F x₁) y - x₀) v =
      dot (x₁ - x₀) v +
        dot (y - restrictOutside F x₁) (restrictOutside F v) := by
  rw [dot_sub_left, dot_sub_left, dot_sub_left, dot_glue,
    dot_restrict_add_outside F x₁ v]
  ring

theorem norm_restrict_le (F : Finset I) (v : I → ℝ) :
    ‖restrict F v‖ ≤ ‖v‖ := by
  rw [pi_norm_le_iff_of_nonneg (norm_nonneg v)]
  intro i
  simpa [restrict] using norm_le_pi_norm v (i : I)

theorem norm_restrictOutside_le (F : Finset I) (v : I → ℝ) :
    ‖restrictOutside F v‖ ≤ ‖v‖ := by
  rw [pi_norm_le_iff_of_nonneg (norm_nonneg v)]
  intro i
  simpa [restrictOutside] using norm_le_pi_norm v (i : I)

end RestrictedDot

/-- The exact conclusion of the Lovett--Meka partial-colouring theorem. -/
def HasPartialColoring [DecidableEq I]
    (v : J → I → ℝ) (x₀ : I → ℝ) (c : J → ℝ) : Prop :=
  ∃ x : I → ℝ,
    InCube x ∧
      Fintype.card I ≤ 2 * (fixedCoordinates x).card ∧
      ∀ j, |dot (x - x₀) (v j)| ≤ c j * l2Norm (v j)

/-- Convert the normalized-row conclusion naturally produced by the edge
walk into the exact unnormalized partial-colouring interface. -/
theorem hasPartialColoring_of_normalizedRows [DecidableEq I]
    (v : J → I → ℝ) (x₀ : I → ℝ) (c : J → ℝ)
    (h : ∃ x : I → ℝ,
      InCube x ∧
        Fintype.card I ≤ 2 * (fixedCoordinates x).card ∧
        ∀ j, |dot (x - x₀) (normalizedRow (v j))| ≤ c j) :
    HasPartialColoring v x₀ c := by
  obtain ⟨x, hxCube, hxCard, hxDiscrepancy⟩ := h
  refine ⟨x, hxCube, hxCard, ?_⟩
  intro j
  by_cases hv : l2Norm (v j) = 0
  · rw [dot_eq_zero_of_l2Norm_eq_zero (x - x₀) (v j) hv, hv]
    simp
  · have hscale := dot_normalizedRow_mul_l2Norm (x - x₀) (v j) hv
    have hnonneg : 0 ≤ l2Norm (v j) := Real.sqrt_nonneg _
    have habs : |l2Norm (v j)| = l2Norm (v j) := abs_of_nonneg hnonneg
    rw [← hscale, abs_mul, habs]
    exact mul_le_mul_of_nonneg_right (hxDiscrepancy j) hnonneg

/-- A formulation of the Lovett--Meka theorem uniform in finite index types.
The proposition is a named interface, rather than a global assumption, so
downstream deterministic arguments can state precisely which input remains
to be established. -/
def PartialColoringPrinciple (I J : Type*)
    [Fintype I] [Fintype J] [DecidableEq I] : Prop :=
  ∀ (v : J → I → ℝ) (x₀ : I → ℝ) (c : J → ℝ),
    InCube x₀ →
      (∀ j, 0 ≤ c j) →
      (∑ j, Real.exp (-(c j) ^ 2 / 16)) ≤ (Fintype.card I : ℝ) / 16 →
      HasPartialColoring v x₀ c

/-- The exact conclusion of the BBMST full-colouring corollary. -/
def HasFullColoring
    (v : J → I → ℝ) (x₀ : I → ℝ) (c : J → ℝ) : Prop :=
  ∃ x : I → ℝ, IsSign x ∧
    ∀ j,
      |dot (x - x₀) (v j)| ≤
        (c j + 30) * Real.sqrt (Fintype.card I) * ‖v j‖

/-- Freeze coordinates in `F` which have reached a face, recursively colour
the complement, and combine the two discrepancy estimates. -/
theorem exists_fullColoring_glue [DecidableEq I]
    (F : Finset I) (v : J → I → ℝ) (x₀ x₁ : I → ℝ)
    (a q : J → ℝ)
    (hfixed : F ⊆ fixedCoordinates x₁)
    (hfirst : ∀ j, |dot (x₁ - x₀) (v j)| ≤ q j)
    (ha : ∀ j, 0 ≤ a j)
    (hrecurse : HasFullColoring
      (fun j ↦ restrictOutside F (v j)) (restrictOutside F x₁) a) :
    ∃ x : I → ℝ, IsSign x ∧
      ∀ j, |dot (x - x₀) (v j)| ≤
        q j + (a j + 30) * Real.sqrt (Fintype.card ↥(Fᶜ : Finset I)) * ‖v j‖ := by
  obtain ⟨y, hySign, hy⟩ := hrecurse
  let x := glue F (restrict F x₁) y
  have hFSign : IsSign (restrict F x₁) := by
    intro i
    have hi := hfixed i.property
    have habs : |x₁ i| = 1 := (Finset.mem_filter.mp hi).2
    exact (abs_eq (by norm_num : (0 : ℝ) ≤ 1)).mp habs
  refine ⟨x, isSign_glue F hFSign hySign, ?_⟩
  intro j
  rw [show dot (x - x₀) (v j) =
      dot (x₁ - x₀) (v j) +
        dot (y - restrictOutside F x₁) (restrictOutside F (v j)) by
    exact dot_glue_sub_reference F x₁ x₀ y (v j)]
  calc
    |dot (x₁ - x₀) (v j) +
        dot (y - restrictOutside F x₁) (restrictOutside F (v j))|
        ≤ |dot (x₁ - x₀) (v j)| +
            |dot (y - restrictOutside F x₁) (restrictOutside F (v j))| :=
          by simpa only [Real.norm_eq_abs] using
            norm_add_le (dot (x₁ - x₀) (v j))
              (dot (y - restrictOutside F x₁) (restrictOutside F (v j)))
    _ ≤ q j +
          (a j + 30) * Real.sqrt (Fintype.card ↥(Fᶜ : Finset I)) *
            ‖restrictOutside F (v j)‖ := add_le_add (hfirst j) (hy j)
    _ ≤ q j +
          (a j + 30) * Real.sqrt (Fintype.card ↥(Fᶜ : Finset I)) * ‖v j‖ := by
      exact add_le_add le_rfl
        (mul_le_mul_of_nonneg_left (norm_restrictOutside_le F (v j))
          (mul_nonneg (by linarith [ha j]) (Real.sqrt_nonneg _)))

/-- Parameters fed to one Lovett--Meka step in BBMST's iteration. -/
def partialParameter (c : J → ℝ) : J → ℝ := fun j ↦ 2 * c j / 7

/-- Constraint parameters on the remaining `e` coordinates after a step
which began with `d` coordinates. -/
def recursiveParameter (d e : ℕ) (c : J → ℝ) : J → ℝ :=
  fun j ↦ Real.sqrt (c j ^ 2 + 196 * Real.log ((d : ℝ) / e))

theorem recursiveParameter_nonneg (d e : ℕ) (c : J → ℝ) :
    ∀ j, 0 ≤ recursiveParameter d e c j := fun _ ↦ Real.sqrt_nonneg _

theorem recursiveParameter_sq {d e : ℕ} (c : J → ℝ)
    (he : 0 < e) (hed : e ≤ d) (j : J) :
    (recursiveParameter d e c j) ^ 2 =
      c j ^ 2 + 196 * Real.log ((d : ℝ) / e) := by
  apply Real.sq_sqrt
  have he_real : 0 < (e : ℝ) := by exact_mod_cast he
  have hratio : (1 : ℝ) ≤ (d : ℝ) / e := by
    rw [le_div_iff₀ he_real]
    simpa using (show (e : ℝ) ≤ d by exact_mod_cast hed)
  exact add_nonneg (sq_nonneg _) (mul_nonneg (by norm_num) (Real.log_nonneg hratio))

theorem recursiveParameter_exponent {d e : ℕ} (c : J → ℝ)
    (he : 0 < e) (hed : e ≤ d) (j : J) :
    Real.exp (-((recursiveParameter d e c j) ^ 2) / 196) =
      Real.exp (-(c j) ^ 2 / 196) * ((e : ℝ) / d) := by
  have hd : 0 < d := he.trans_le hed
  have he_real : (e : ℝ) ≠ 0 := by exact_mod_cast he.ne'
  have hd_real : (d : ℝ) ≠ 0 := by exact_mod_cast hd.ne'
  have hratio_pos : 0 < (d : ℝ) / e := div_pos (by exact_mod_cast hd) (by exact_mod_cast he)
  rw [recursiveParameter_sq c he hed]
  calc
    Real.exp (-(c j ^ 2 + 196 * Real.log ((d : ℝ) / e)) / 196) =
        Real.exp (-(c j) ^ 2 / 196 + -Real.log ((d : ℝ) / e)) := by ring_nf
    _ = Real.exp (-(c j) ^ 2 / 196) *
        Real.exp (-Real.log ((d : ℝ) / e)) := Real.exp_add _ _
    _ = Real.exp (-(c j) ^ 2 / 196) * ((e : ℝ) / d) := by
      rw [Real.exp_neg, Real.exp_log hratio_pos]
      congr 1
      field_simp

/-- The entropy budget rescales exactly when the number of live coordinates
drops from `d` to `e`. -/
theorem recursiveParameter_budget {d e : ℕ} (c : J → ℝ)
    (he : 0 < e) (hed : e ≤ d)
    (hbudget : (∑ j, Real.exp (-(c j) ^ 2 / 196)) ≤ (d : ℝ) / 16) :
    (∑ j, Real.exp (-((recursiveParameter d e c j) ^ 2) / 196)) ≤
      (e : ℝ) / 16 := by
  have hd : 0 < d := he.trans_le hed
  have hratio_nonneg : 0 ≤ (e : ℝ) / d := by positivity
  simp_rw [recursiveParameter_exponent c he hed]
  rw [← Finset.sum_mul]
  calc
    (∑ j, Real.exp (-(c j) ^ 2 / 196)) * ((e : ℝ) / d)
        ≤ ((d : ℝ) / 16) * ((e : ℝ) / d) :=
          mul_le_mul_of_nonneg_right hbudget hratio_nonneg
    _ = (e : ℝ) / 16 := by
      have hd_real : (d : ℝ) ≠ 0 := by exact_mod_cast hd.ne'
      field_simp

theorem partialParameter_nonneg {c : J → ℝ} (hc : ∀ j, 0 ≤ c j) :
    ∀ j, 0 ≤ partialParameter c j := by
  intro j
  simp only [partialParameter]
  exact div_nonneg (mul_nonneg (by norm_num) (hc j)) (by norm_num)

theorem partialParameter_exponent (c : J → ℝ) (j : J) :
    -((partialParameter c j) ^ 2) / 16 = -(c j) ^ 2 / 196 := by
  simp only [partialParameter]
  ring

theorem partialParameter_budget {c : J → ℝ}
    (hbudget : (∑ j, Real.exp (-(c j) ^ 2 / 196)) ≤
      (Fintype.card I : ℝ) / 16) :
    (∑ j, Real.exp (-((partialParameter c j) ^ 2) / 16)) ≤
      (Fintype.card I : ℝ) / 16 := by
  simpa only [partialParameter_exponent] using hbudget

/-- One invocation of the partial-colouring principle with BBMST's scaled
parameters. -/
theorem partialColoring_step [DecidableEq I]
    (hLM : PartialColoringPrinciple I J)
    (v : J → I → ℝ) (x₀ : I → ℝ) (c : J → ℝ)
    (hx₀ : InCube x₀) (hc : ∀ j, 0 ≤ c j)
    (hbudget : (∑ j, Real.exp (-(c j) ^ 2 / 196)) ≤
      (Fintype.card I : ℝ) / 16) :
    HasPartialColoring v x₀ (partialParameter c) := by
  exact hLM v x₀ (partialParameter c) hx₀
    (partialParameter_nonneg hc) (partialParameter_budget hbudget)

/-- From a partial colouring, select exactly `⌈d/2⌉` fixed coordinates;
the complementary recursive problem then has cardinality `⌊d/2⌋`. -/
theorem exists_freezeSet [DecidableEq I] {x : I → ℝ}
    (hhalf : Fintype.card I ≤ 2 * (fixedCoordinates x).card) :
    ∃ F : Finset I, F ⊆ fixedCoordinates x ∧
      Fintype.card ↥(Fᶜ : Finset I) = Fintype.card I / 2 := by
  have hneed : Fintype.card I - Fintype.card I / 2 ≤ (fixedCoordinates x).card := by
    omega
  obtain ⟨F, hF, hFcard⟩ :=
    (fixedCoordinates x).exists_subset_card_eq hneed
  refine ⟨F, hF, ?_⟩
  simp only [Fintype.card_coe, Finset.card_compl, hFcard]
  omega

/-- The numerical inequality closing the inductive step in BBMST Corollary
4.2.  The recursive coordinate set has cardinality `⌊d/2⌋`; its new
constraint parameter is the square root appearing on the left. -/
theorem induction_constant_inequality (d : ℕ) (c : ℝ)
    (hd : 900 < d) (hc : 0 ≤ c) :
    2 * c / 7 * Real.sqrt d +
        (Real.sqrt (c ^ 2 + 196 * Real.log ((d : ℝ) / (d / 2 : ℕ))) + 30) *
          Real.sqrt (d / 2 : ℕ) ≤
      (c + 30) * Real.sqrt d := by
  have he_pos_nat : 0 < d / 2 := by omega
  have he_ge_nat : 450 ≤ d / 2 := by omega
  have hd_le_nat : d ≤ 2 * (d / 2) + 1 := by omega
  have he_pos : 0 < ((d / 2 : ℕ) : ℝ) := by exact_mod_cast he_pos_nat
  have he_ge : (450 : ℝ) ≤ (d / 2 : ℕ) := by exact_mod_cast he_ge_nat
  have hd_le : (d : ℝ) ≤ 2 * (d / 2 : ℕ) + 1 := by exact_mod_cast hd_le_nat
  have hd_pos_nat : 0 < d := by omega
  have hd_pos : 0 < (d : ℝ) := by exact_mod_cast hd_pos_nat
  have hratio_pos : 0 < (d : ℝ) / (d / 2 : ℕ) := div_pos hd_pos he_pos
  have hratio_le : (d : ℝ) / (d / 2 : ℕ) ≤ (901 : ℝ) / 450 := by
    rw [div_le_iff₀ he_pos]
    nlinarith
  have hlog_aux : Real.log ((901 : ℝ) / 450) ≤ Real.log 2 + 1 / 900 := by
    rw [show (901 : ℝ) / 450 = 2 * (901 / 900) by norm_num,
      Real.log_mul (by norm_num) (by norm_num)]
    gcongr
    have h := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 901 / 900 by norm_num)
    norm_num at h ⊢
    exact h
  have hlog : Real.log ((d : ℝ) / (d / 2 : ℕ)) ≤ (36 : ℝ) / 49 := by
    calc
      Real.log ((d : ℝ) / (d / 2 : ℕ))
          ≤ Real.log ((901 : ℝ) / 450) := Real.log_le_log hratio_pos hratio_le
      _ ≤ Real.log 2 + 1 / 900 := hlog_aux
      _ ≤ (36 : ℝ) / 49 := by
        have h := Real.log_two_lt_d9.le
        norm_num at h ⊢
        linarith
  have ha :
      Real.sqrt (c ^ 2 + 196 * Real.log ((d : ℝ) / (d / 2 : ℕ))) ≤ c + 12 := by
    rw [Real.sqrt_le_iff]
    constructor
    · linarith
    · nlinarith
  have he_le_nat : 2 * (d / 2) ≤ d := by omega
  have he_le : 2 * ((d / 2 : ℕ) : ℝ) ≤ d := by exact_mod_cast he_le_nat
  have hsqrt : Real.sqrt (d / 2 : ℕ) ≤ (71 : ℝ) / 100 * Real.sqrt d := by
    rw [Real.sqrt_le_iff]
    constructor
    · positivity
    · have hsqd := Real.sq_sqrt hd_pos.le
      nlinarith
  calc
    2 * c / 7 * Real.sqrt d +
          (Real.sqrt (c ^ 2 + 196 * Real.log ((d : ℝ) / (d / 2 : ℕ))) + 30) *
            Real.sqrt (d / 2 : ℕ)
        ≤ 2 * c / 7 * Real.sqrt d + (c + 42) * Real.sqrt (d / 2 : ℕ) := by
          exact add_le_add_right
            (mul_le_mul_of_nonneg_right (by linarith [ha]) (Real.sqrt_nonneg _)) _
    _ ≤ 2 * c / 7 * Real.sqrt d +
          (c + 42) * ((71 : ℝ) / 100 * Real.sqrt d) := by
          exact add_le_add_right (mul_le_mul_of_nonneg_left hsqrt (by linarith)) _
    _ = (2 * c / 7 + (c + 42) * ((71 : ℝ) / 100)) * Real.sqrt d := by ring
    _ ≤ (c + 30) * Real.sqrt d := by
          apply mul_le_mul_of_nonneg_right _ (Real.sqrt_nonneg _)
          nlinarith

@[simp] theorem dot_zero_left (v : I → ℝ) : dot 0 v = 0 := by
  simp [dot]

@[simp] theorem dot_zero_right (x : I → ℝ) : dot x 0 = 0 := by
  simp [dot]

theorem abs_dot_le_sum_abs_mul (x v : I → ℝ) :
    |dot x v| ≤ ∑ i, |x i| * |v i| := by
  rw [dot]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  exact Finset.sum_le_sum fun i _ ↦ by rw [abs_mul]

theorem abs_dot_le_card_mul_norm_of_abs_le
    {x v : I → ℝ} {a : ℝ} (ha : 0 ≤ a) (hx : ∀ i, |x i| ≤ a) :
    |dot x v| ≤ Fintype.card I * a * ‖v‖ := by
  calc
    |dot x v| ≤ ∑ i, |x i| * |v i| := abs_dot_le_sum_abs_mul x v
    _ ≤ ∑ _i : I, a * ‖v‖ := by
      refine Finset.sum_le_sum fun i _ ↦ mul_le_mul (hx i) (norm_le_pi_norm v i)
        (abs_nonneg _) ha
    _ = Fintype.card I * a * ‖v‖ := by simp [mul_assoc]

theorem sum_sq_le_card_mul_norm_sq (v : I → ℝ) :
    (∑ i, (v i) ^ 2) ≤ Fintype.card I * ‖v‖ ^ 2 := by
  calc
    (∑ i, (v i) ^ 2) ≤ ∑ _i : I, ‖v‖ ^ 2 := by
      refine Finset.sum_le_sum fun i _ ↦ ?_
      have hvi : |v i| ≤ ‖v‖ := by
        simpa only [Real.norm_eq_abs] using norm_le_pi_norm v i
      rw [← sq_abs]
      nlinarith [abs_nonneg (v i), norm_nonneg v,
        mul_nonneg (sub_nonneg.mpr hvi) (add_nonneg (norm_nonneg v) (abs_nonneg (v i)))]
    _ = Fintype.card I * ‖v‖ ^ 2 := by simp

theorem l2Norm_nonneg (v : I → ℝ) : 0 ≤ l2Norm v :=
  Real.sqrt_nonneg _

theorem l2Norm_le_sqrt_card_mul_norm (v : I → ℝ) :
    l2Norm v ≤ Real.sqrt (Fintype.card I) * ‖v‖ := by
  have hsum_nonneg : 0 ≤ ∑ i, (v i) ^ 2 :=
    Finset.sum_nonneg fun _ _ ↦ sq_nonneg _
  have hcard_nonneg : 0 ≤ (Fintype.card I : ℝ) := Nat.cast_nonneg _
  have hnorm_nonneg : 0 ≤ ‖v‖ := norm_nonneg _
  rw [l2Norm, ← Real.sqrt_sq hnorm_nonneg, ← Real.sqrt_mul hcard_nonneg]
  exact Real.sqrt_le_sqrt (sum_sq_le_card_mul_norm_sq v)

/-- Round a cube point coordinatewise to its nearest sign (choosing `1` at
zero). -/
def nearestSign (x : I → ℝ) : I → ℝ :=
  fun i ↦ if 0 ≤ x i then 1 else -1

theorem nearestSign_isSign (x : I → ℝ) : IsSign (nearestSign x) := by
  intro i
  simp only [nearestSign]
  split_ifs <;> simp

theorem abs_nearestSign_sub_le_one {x : I → ℝ} (hx : InCube x) (i : I) :
    |nearestSign x i - x i| ≤ 1 := by
  have hxi := hx i
  simp only [abs_le] at hxi
  simp only [nearestSign]
  split_ifs with h
  · rw [abs_of_nonneg]
    · linarith
    · linarith
  · rw [abs_of_nonpos]
    · linarith
    · linarith

theorem nearestSign_dot_sub_le_card_mul_norm
    {x : I → ℝ} (hx : InCube x) (v : I → ℝ) :
    |dot (nearestSign x - x) v| ≤ Fintype.card I * ‖v‖ := by
  change |dot (fun i ↦ nearestSign x i - x i) v| ≤ Fintype.card I * ‖v‖
  simpa using abs_dot_le_card_mul_norm_of_abs_le (v := v) (a := 1)
    (by norm_num) (abs_nearestSign_sub_le_one hx)

theorem fixedCoordinates_nearestSign [DecidableEq I] (x : I → ℝ) :
    fixedCoordinates (nearestSign x) = Finset.univ := by
  apply Finset.eq_univ_of_forall
  intro i
  simp only [fixedCoordinates, Finset.mem_filter, Finset.mem_univ, true_and]
  simp only [nearestSign]
  split_ifs <;> norm_num

/-- Lovett--Meka is elementary when all constraint vectors vanish.  This is
also the reduction used to discard zero rows before normalizing vectors. -/
theorem hasPartialColoring_zero_vectors [DecidableEq I]
    (x₀ : I → ℝ) (c : J → ℝ) (hx₀ : InCube x₀) (hc : ∀ j, 0 ≤ c j) :
    HasPartialColoring (fun _ ↦ (0 : I → ℝ)) x₀ c := by
  refine ⟨nearestSign x₀, ?_, ?_, ?_⟩
  · intro i
    rcases nearestSign_isSign x₀ i with hi | hi <;> simp [hi]
  · rw [fixedCoordinates_nearestSign]
    simp
    omega
  · intro j
    simp [dot, l2Norm]

/-- With no constraints, coordinatewise rounding is an exact partial
colouring. -/
theorem hasPartialColoring_of_isEmpty [DecidableEq I] [IsEmpty J]
    (v : J → I → ℝ) (x₀ : I → ℝ) (c : J → ℝ) (hx₀ : InCube x₀) :
    HasPartialColoring v x₀ c := by
  refine ⟨nearestSign x₀, ?_, ?_, ?_⟩
  · intro i
    rcases nearestSign_isSign x₀ i with hi | hi <;> simp [hi]
  · rw [fixedCoordinates_nearestSign]
    simp
    omega
  · exact isEmptyElim

theorem card_le_900_le_thirty_mul_sqrt_card
    (hcard : Fintype.card I ≤ 900) :
    (Fintype.card I : ℝ) ≤ 30 * Real.sqrt (Fintype.card I) := by
  have h0 : 0 ≤ (Fintype.card I : ℝ) := Nat.cast_nonneg _
  have hsqrt : Real.sqrt (Fintype.card I) ≤ 30 := by
    rw [Real.sqrt_le_iff]
    constructor
    · norm_num
    · norm_num
      exact_mod_cast hcard
  nlinarith [Real.sq_sqrt h0, Real.sqrt_nonneg (Fintype.card I)]

/-- The terminal (`d ≤ 900`) case of BBMST's full-colouring induction. -/
theorem hasFullColoring_of_card_le_900
    (v : J → I → ℝ) (x₀ : I → ℝ) (c : J → ℝ)
    (hx₀ : InCube x₀) (hc : ∀ j, 0 ≤ c j)
    (hcard : Fintype.card I ≤ 900) :
    HasFullColoring v x₀ c := by
  refine ⟨nearestSign x₀, nearestSign_isSign x₀, ?_⟩
  intro j
  have hround := nearestSign_dot_sub_le_card_mul_norm hx₀ (v j)
  have hdim := card_le_900_le_thirty_mul_sqrt_card (I := I) hcard
  calc
    |dot (nearestSign x₀ - x₀) (v j)|
        ≤ Fintype.card I * ‖v j‖ := hround
    _ ≤ 30 * Real.sqrt (Fintype.card I) * ‖v j‖ := by
      exact mul_le_mul_of_nonneg_right hdim (norm_nonneg _)
    _ ≤ (c j + 30) * Real.sqrt (Fintype.card I) * ‖v j‖ := by
      gcongr
      linarith [hc j]

end Erdos228.Discrepancy
