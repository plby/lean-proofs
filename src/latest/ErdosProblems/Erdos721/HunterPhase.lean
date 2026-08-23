/- leanprover/lean4:v4.33.0 -/
/-
Copyright 2026 The Formal Conjectures Authors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0
-/

import ErdosProblems.Erdos721.HunterTorus
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

/-!
# Full-rank phase maps on Hunter's torus

An integral square matrix with nonzero determinant induces a surjective
endomorphism of the real torus.  Consequently it preserves normalized Haar
measure, and the image of a small coordinate box has at least the volume of
that box.  The determinant may be very large: this observation is precisely
what prevents a loss depending on the size of a resonant integral basis.
-/

namespace Erdos721.HunterPhase

open Function MeasureTheory MeasureTheory.Measure Set
open scoped ENNReal MeasureTheory

open HunterTorus

/-- Cast an integral matrix to a real matrix. -/
def realMatrix {m : ℕ} (A : Matrix (Fin m) (Fin m) ℤ) :
    Matrix (Fin m) (Fin m) ℝ :=
  fun i j ↦ (A i j : ℝ)

@[simp] lemma realMatrix_apply {m : ℕ}
    (A : Matrix (Fin m) (Fin m) ℤ) (i j : Fin m) :
    realMatrix A i j = (A i j : ℝ) := rfl

lemma det_realMatrix {m : ℕ} (A : Matrix (Fin m) (Fin m) ℤ) :
    (realMatrix A).det = (A.det : ℝ) := by
  change (A.map fun x : ℤ ↦ (x : ℝ)).det = (A.det : ℝ)
  exact (Int.cast_det (R := ℝ) A).symm

/-- A nonsingular integral matrix gives a surjective homomorphism of unit
tori. -/
theorem phaseHom_surjective_of_det_ne_zero {m : ℕ}
    (A : Matrix (Fin m) (Fin m) ℤ) (hA : A.det ≠ 0) :
    Surjective (phaseHom A) := by
  have hdet : (realMatrix A).det ≠ 0 := by
    rw [det_realMatrix]
    exact_mod_cast hA
  have hunit : IsUnit (realMatrix A) :=
    (Matrix.isUnit_iff_isUnit_det (realMatrix A)).2
      (isUnit_iff_ne_zero.2 hdet)
  have hsurjReal : Surjective (realMatrix A).mulVec :=
    Matrix.mulVec_surjective_iff_isUnit.2 hunit
  intro y
  let yLift : Fin m → ℝ := fun i ↦ centeredCoord (y i)
  obtain ⟨x, hx⟩ := hsurjReal yLift
  refine ⟨project (WithLp.toLp 2 x), ?_⟩
  funext i
  change (∑ j, (A i j) • ((x j : ℝ) : AddCircle (1 : ℝ))) = y i
  rw [← AddCircle.coe_equivIco (p := (1 : ℝ))
    (a := -(1 / 2 : ℝ)) (y := y i)]
  change (∑ j, (A i j) • ((x j : ℝ) : AddCircle (1 : ℝ))) =
    ((centeredCoord (y i) : ℝ) : AddCircle (1 : ℝ))
  rw [← show (realMatrix A).mulVec x i = centeredCoord (y i) by
    exact congrFun hx i]
  simp [Matrix.mulVec, dotProduct, realMatrix]

theorem measurePreserving_phaseHom_of_det_ne_zero {m : ℕ}
    (A : Matrix (Fin m) (Fin m) ℤ) (hA : A.det ≠ 0) :
    MeasurePreserving (phaseHom A) :=
  measurePreserving_phaseHom A
    (phaseHom_surjective_of_det_ne_zero A hA)

/-- The phase image of a small compact coordinate box cannot have smaller
volume than the box itself. -/
lemma volume_phaseHom_image_centeredBox {m : ℕ}
    (A : Matrix (Fin m) (Fin m) ℤ) (hA : A.det ≠ 0)
    {r : ℝ} (hr0 : 0 ≤ r) (hr : 2 * r ≤ 1) :
    ENNReal.ofReal (2 * r) ^ m ≤
      volume (phaseHom A '' centeredBox m r) := by
  rw [← volume_centeredBox hr0 hr]
  exact measure_le_measure_image_of_compact
    (measurePreserving_phaseHom_of_det_ne_zero A hA)
    (continuous_phaseHom A) (centeredBox_compact m r)

/-! ### Coordinate minors of an independent phase family -/

/-- Cast a rectangular family of integral characters to a rational matrix. -/
def rationalMatrix {D m : ℕ} (ξ : Fin m → Fin D → ℤ) :
    Matrix (Fin m) (Fin D) ℚ :=
  fun i j ↦ (ξ i j : ℚ)

@[simp] lemma rationalMatrix_apply {D m : ℕ}
    (ξ : Fin m → Fin D → ℤ) (i : Fin m) (j : Fin D) :
    rationalMatrix ξ i j = (ξ i j : ℚ) := rfl

/-- Independent integral rows contain a nonsingular square coordinate minor.
The proof selects a basis from the columns of the rectangular matrix. -/
theorem exists_nonsingular_coordinate_minor {D m : ℕ}
    (ξ : Fin m → Fin D → ℤ)
    (hξ : LinearIndependent ℚ (rationalMatrix ξ).row) :
    ∃ j : Fin m ↪ Fin D,
      Matrix.det ((fun a b ↦ ξ a (j b)) :
        Matrix (Fin m) (Fin m) ℤ) ≠ 0 := by
  let X := rationalMatrix ξ
  have hrank : X.rank = m := by
    simpa [X] using hξ.rank_matrix
  have hfinrank : Module.finrank ℚ
      (Submodule.span ℚ (Set.range X.col)) = m := by
    rw [← Matrix.rank_eq_finrank_span_cols]
    exact hrank
  have hex := Submodule.exists_fun_fin_finrank_span_eq ℚ
    (Set.range X.col)
  rw [hfinrank] at hex
  obtain ⟨f, hfmem, _hfspan, hfind⟩ := hex
  choose j hj using hfmem
  have hjinj : Injective j := by
    intro a b hab
    apply hfind.injective
    rw [← hj a, ← hj b, hab]
  let je : Fin m ↪ Fin D := ⟨j, hjinj⟩
  let A : Matrix (Fin m) (Fin m) ℤ := fun a b ↦ ξ a (je b)
  let AQ : Matrix (Fin m) (Fin m) ℚ := fun a b ↦ (A a b : ℚ)
  have hcol : AQ.col = f := by
    funext b a
    change (ξ a (je b) : ℚ) = f b a
    rw [← hj b]
    rfl
  have hAQind : LinearIndependent ℚ AQ.col := by
    rw [hcol]
    exact hfind
  have hAQunit : IsUnit AQ :=
    Matrix.linearIndependent_cols_iff_isUnit.mp hAQind
  have hdetQ : AQ.det ≠ 0 :=
    isUnit_iff_ne_zero.mp
      ((Matrix.isUnit_iff_isUnit_det AQ).mp hAQunit)
  refine ⟨je, ?_⟩
  change A.det ≠ 0
  intro hdet
  apply hdetQ
  change (A.map fun x : ℤ ↦ (x : ℚ)).det = 0
  rw [← Int.cast_det (R := ℚ) A, hdet]
  norm_num

/-- Embed a coordinate torus using an injective choice of coordinates. -/
def coordinateEmbed {D m : ℕ} (j : Fin m ↪ Fin D)
    (z : Torus m) : Torus D :=
  fun i ↦ ∑ b, if j b = i then z b else 0

@[simp] lemma coordinateEmbed_apply_image {D m : ℕ}
    (j : Fin m ↪ Fin D) (z : Torus m) (b : Fin m) :
    coordinateEmbed j z (j b) = z b := by
  classical
  simp [coordinateEmbed, j.injective.eq_iff]

/-- Restricting a phase family to selected coordinates is composition with
the corresponding coordinate embedding. -/
lemma phaseHom_coordinateEmbed {D m : ℕ}
    (ξ : Fin m → Fin D → ℤ) (j : Fin m ↪ Fin D)
    (z : Torus m) :
    phaseHom ξ (coordinateEmbed j z) =
      phaseHom (fun a b ↦ ξ a (j b)) z := by
  classical
  funext a
  simp only [phaseHom_apply, integerDot_apply]
  simp_rw [coordinateEmbed, Finset.smul_sum]
  rw [Finset.sum_comm]
  congr 1
  funext b
  simp

/-- The centered Euclidean lift supported on selected coordinates. -/
noncomputable def coordinateLift {D m : ℕ} (j : Fin m ↪ Fin D)
    (z : Torus m) : EuclideanSpace ℝ (Fin D) :=
  WithLp.toLp 2 fun i ↦
    ∑ b, if j b = i then centeredCoord (z b) else 0

@[simp] lemma coordinateLift_apply_image {D m : ℕ}
    (j : Fin m ↪ Fin D) (z : Torus m) (b : Fin m) :
    coordinateLift j z (j b) = centeredCoord (z b) := by
  classical
  simp [coordinateLift, j.injective.eq_iff]

@[simp] lemma project_coordinateLift {D m : ℕ}
    (j : Fin m ↪ Fin D) (z : Torus m) :
    project (coordinateLift j z) = coordinateEmbed j z := by
  classical
  funext i
  simp only [project, coordinateLift, coordinateEmbed,
    WithLp.ofLp_toLp]
  change (QuotientAddGroup.mk' (AddSubgroup.zmultiples (1 : ℝ)))
      (∑ x, if j x = i then centeredCoord (z x) else 0) = _
  rw [_root_.map_sum]
  apply Finset.sum_congr rfl
  intro b hb
  split_ifs <;> simp [centeredCoord]

lemma coordinateLift_norm_sq {D m : ℕ} (j : Fin m ↪ Fin D)
    (z : Torus m) :
    ‖coordinateLift j z‖ ^ 2 =
      ∑ b, |centeredCoord (z b)| ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq]
  classical
  simp only [coordinateLift, WithLp.ofLp_toLp, Real.norm_eq_abs]
  let F : Fin D → ℝ := fun i ↦
    |∑ b, if j b = i then centeredCoord (z b) else 0| ^ 2
  have himage : ∑ i ∈ Finset.univ.image j, F i =
      ∑ b, F (j b) := by
    rw [Finset.sum_image]
    exact Set.injOn_of_injective j.injective
  have hfull : ∑ i, F i =
      ∑ i ∈ Finset.univ.image j, F i := by
    symm
    apply Finset.sum_subset (by simp)
    intro i hi hnot
    have hnone : ∀ b : Fin m, j b ≠ i := by
      intro b hbi
      apply hnot
      exact Finset.mem_image.mpr
        ⟨b, Finset.mem_univ _, hbi⟩
    simp [F, hnone]
  rw [show (∑ i,
      |∑ b, if j b = i then centeredCoord (z b) else 0| ^ 2) =
      ∑ i, F i by rfl, hfull, himage]
  apply Finset.sum_congr rfl
  intro b hb
  simp [F, j.injective.eq_iff]

lemma abs_centeredCoord_eq_norm (x : AddCircle (1 : ℝ)) :
    |centeredCoord x| = ‖x‖ := by
  have habs :
      ‖((centeredCoord x : ℝ) : AddCircle (1 : ℝ))‖ =
        |centeredCoord x| :=
    (AddCircle.norm_coe_eq_abs_iff (p := (1 : ℝ))
      (by norm_num)).2
      (by simpa using abs_centeredCoord_le_half x)
  calc
    |centeredCoord x| =
        ‖((centeredCoord x : ℝ) : AddCircle (1 : ℝ))‖ :=
      habs.symm
    _ = ‖x‖ := congrArg norm AddCircle.coe_equivIco

/-- A coordinate torus box of radius `r` lifts to the Euclidean ball of
radius `sqrt(m) * r`. -/
lemma coordinateLift_norm_le {D m : ℕ} (j : Fin m ↪ Fin D)
    {z : Torus m} {r : ℝ} (hr0 : 0 ≤ r)
    (hz : z ∈ centeredBox m r) :
    ‖coordinateLift j z‖ ≤ Real.sqrt m * r := by
  have hcoord : ∀ b : Fin m, |centeredCoord (z b)| ≤ r := by
    intro b
    rw [abs_centeredCoord_eq_norm]
    have hb := hz b (Set.mem_univ b)
    simpa [Metric.mem_closedBall, dist_eq_norm] using hb
  have hsq : ‖coordinateLift j z‖ ^ 2 ≤ (m : ℝ) * r ^ 2 := by
    rw [coordinateLift_norm_sq]
    calc
      ∑ b, |centeredCoord (z b)| ^ 2 ≤
          ∑ _b : Fin m, r ^ 2 := by
        apply Finset.sum_le_sum
        intro b hb
        exact (sq_le_sq₀ (abs_nonneg _) hr0).2 (hcoord b)
      _ = (m : ℝ) * r ^ 2 := by simp
  have hsqrt0 : 0 ≤ Real.sqrt (m : ℝ) := Real.sqrt_nonneg _
  have hsqrt_sq : Real.sqrt (m : ℝ) ^ 2 = (m : ℝ) :=
    Real.sq_sqrt (by positivity)
  have hnorm0 : 0 ≤ ‖coordinateLift j z‖ := norm_nonneg _
  apply (sq_le_sq₀ hnorm0 (mul_nonneg hsqrt0 hr0)).1
  rw [mul_pow, hsqrt_sq]
  exact hsq

/-- A rationally independent family of integer characters maps the ambient
torus onto the full phase torus. -/
theorem phaseHom_surjective_of_linearIndependent {D m : ℕ}
    (ξ : Fin m → Fin D → ℤ)
    (hξ : LinearIndependent ℚ (rationalMatrix ξ).row) :
    Surjective (phaseHom ξ) := by
  obtain ⟨j, hj⟩ := exists_nonsingular_coordinate_minor ξ hξ
  intro y
  obtain ⟨z, hz⟩ := phaseHom_surjective_of_det_ne_zero
    (fun a b ↦ ξ a (j b)) hj y
  refine ⟨coordinateEmbed j z, ?_⟩
  rw [phaseHom_coordinateEmbed, hz]

theorem measurePreserving_phaseHom_of_linearIndependent {D m : ℕ}
    (ξ : Fin m → Fin D → ℤ)
    (hξ : LinearIndependent ℚ (rationalMatrix ξ).row) :
    MeasurePreserving (phaseHom ξ) :=
  measurePreserving_phaseHom ξ
    (phaseHom_surjective_of_linearIndependent ξ hξ)

/-! ### Positive-measure sets of phase-compatible centers -/

/-- A center is good for `xStar` if its phase differs from the phase of
`xStar` by the phase image of a small coordinate box. -/
def goodCenterSet {D m : ℕ} (ξ : Fin m → Fin D → ℤ)
    (j : Fin m ↪ Fin D) (r : ℝ) (xStar : Torus D) : Set (Torus D) :=
  phaseHom ξ ⁻¹' ((fun y ↦ phaseHom ξ xStar + y) ''
    (phaseHom (fun a b ↦ ξ a (j b)) '' centeredBox m r))

lemma goodCenterTarget_compact {D m : ℕ}
    (ξ : Fin m → Fin D → ℤ) (j : Fin m ↪ Fin D)
    (r : ℝ) (xStar : Torus D) :
    IsCompact ((fun y ↦ phaseHom ξ xStar + y) ''
      (phaseHom (fun a b ↦ ξ a (j b)) '' centeredBox m r)) := by
  exact ((centeredBox_compact m r).image
    (continuous_phaseHom (fun a b ↦ ξ a (j b)))).image
      (continuous_const.add continuous_id)

/-- Exact Haar-volume lower bound for phase-compatible centers. -/
lemma volume_goodCenterSet {D m : ℕ}
    (ξ : Fin m → Fin D → ℤ)
    (hξ : LinearIndependent ℚ (rationalMatrix ξ).row)
    (j : Fin m ↪ Fin D)
    (hj : Matrix.det ((fun a b ↦ ξ a (j b)) :
      Matrix (Fin m) (Fin m) ℤ) ≠ 0)
    {r : ℝ} (hr0 : 0 ≤ r) (hr : 2 * r ≤ 1)
    (xStar : Torus D) :
    ENNReal.ofReal (2 * r) ^ m ≤
      volume (goodCenterSet ξ j r xStar) := by
  let A : Matrix (Fin m) (Fin m) ℤ :=
    fun a b ↦ ξ a (j b)
  let T : Set (Torus m) := phaseHom A '' centeredBox m r
  have hTcompact : IsCompact T :=
    (centeredBox_compact m r).image (continuous_phaseHom A)
  have htranslate :
      volume ((fun y ↦ phaseHom ξ xStar + y) '' T) = volume T := by
    rw [Set.image_add_left, measure_preimage_add]
  have hpreimage :
      volume (goodCenterSet ξ j r xStar) =
        volume ((fun y ↦ phaseHom ξ xStar + y) '' T) := by
    apply (measurePreserving_phaseHom_of_linearIndependent ξ hξ).measure_preimage
    exact (hTcompact.image
      (continuous_const.add continuous_id)).measurableSet.nullMeasurableSet
  rw [hpreimage, htranslate]
  exact volume_phaseHom_image_centeredBox A hj hr0 hr

/-- Every good center admits an explicitly small Euclidean correction which
annihilates all phases in the chosen independent family. -/
lemma exists_small_phase_correction_of_mem_goodCenterSet
    {D m : ℕ} (ξ : Fin m → Fin D → ℤ)
    (j : Fin m ↪ Fin D) {r : ℝ} (hr0 : 0 ≤ r)
    (xStar x : Torus D) (hx : x ∈ goodCenterSet ξ j r xStar) :
    ∃ u : EuclideanSpace ℝ (Fin D),
      ‖u‖ ≤ Real.sqrt m * r ∧
        phaseHom ξ (x + project u - xStar) = 0 := by
  rcases hx with ⟨y, ⟨z, hz, rfl⟩, hxy⟩
  refine ⟨-coordinateLift j z, ?_, ?_⟩
  · simpa using coordinateLift_norm_le j hr0 hz
  · rw [project_neg, map_sub, map_add, map_neg, project_coordinateLift,
      phaseHom_coordinateEmbed]
    change phaseHom ξ xStar + phaseHom (fun a b ↦ ξ a (j b)) z =
      phaseHom ξ x at hxy
    rw [← hxy]
    abel

end Erdos721.HunterPhase
