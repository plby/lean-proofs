/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/- Original license: Apache 2.0. Note: This file has been modified. -/
/-
This is a Lean formalization of a solution to Erdős Problem 1124.
https://www.erdosproblems.com/forum/thread/1124

Informal authors:
- Miklós Laczkovich

Formal authors:
- Codex
- GPT-5.6 Sol

URLs:
- https://github.com/plby/lean-proofs/blob/main/ErdosProblems/Erdos1124.md
-/
/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
import ErdosProblems.Erdos1124.Hall
import ErdosProblems.Erdos1124.AffineGlue
import ErdosProblems.Erdos1124.ConcreteDiscrepancy
import ErdosProblems.Erdos1124.Similarity
import ErdosProblems.Erdos1124.TorusAction
import ErdosProblems.Erdos1124.TorusLaczkovich
import ErdosProblems.Erdos1124.TorusTransfer

/-!
# Erdős Problem 1124

Tarski's circle-squaring problem asks whether a disk and a square of the same
area possess finite decompositions into pairwise congruent pieces.  Laczkovich
proved the stronger assertion that the motions can all be translations.

The mathematical reconstruction and a map of the formal proof are in
`tex/1124.tex`.
-/

open Set MeasureTheory Metric

namespace Erdos1124

noncomputable section

/-- The Euclidean plane used in the statement. -/
abbrev Plane := EuclideanSpace ℝ (Fin 2)

/-- The closed disk of radius `r` centered at the origin. -/
def disk (r : ℝ) : Set Plane := closedBall 0 r

/-- The side length of the square having the same area as `disk r`. -/
def squareSide (r : ℝ) : ℝ := Real.sqrt Real.pi * r

/-- The closed, origin-centered, axis-parallel square whose side length is
`sqrt π * r`.  `WithLp.ofLp` exposes the two coordinates of a point of the
Euclidean plane. -/
def square (r : ℝ) : Set Plane :=
  (@WithLp.ofLp 2 (Fin 2 → ℝ)) ⁻¹'
    Icc (fun _ ↦ -(squareSide r) / 2) (fun _ ↦ squareSide r / 2)

/-- Equidecomposability using translations only.  Mathlib's `Equidecomp`
stores a partial bijection and a finite set of acting group elements.  The
canonical action of `Multiplicative Plane` is vector addition. -/
def TranslationEquidecomposable (A B : Set Plane) : Prop :=
  ∃ e : Equidecomp Plane (Multiplicative Plane), e.source = A ∧ e.target = B

/-- The standard volume formula for the disk, in the exact normalization used
in the final statement. -/
lemma volume_disk (r : ℝ) (hr : 0 ≤ r) :
    volume (disk r) = ENNReal.ofReal (Real.pi * r ^ 2) := by
  rw [disk, EuclideanSpace.volume_closedBall_fin_two]
  rw [← ENNReal.ofReal_pow hr]
  rw [← ENNReal.ofReal_mul (sq_nonneg r)]
  congr 1
  ring

/-- The coordinate square has area `π r²`. -/
lemma volume_square (r : ℝ) (hr : 0 ≤ r) :
    volume (square r) = ENNReal.ofReal (Real.pi * r ^ 2) := by
  have hs : 0 ≤ squareSide r := mul_nonneg (Real.sqrt_nonneg _) hr
  rw [square, (PiLp.volume_preserving_ofLp (Fin 2)).measure_preimage
    measurableSet_Icc.nullMeasurableSet, Real.volume_Icc_pi]
  simp only [Fin.prod_univ_two]
  rw [show squareSide r / 2 - (-(squareSide r) / 2) = squareSide r by ring]
  rw [← pow_two, ← ENNReal.ofReal_pow hs]
  congr 1
  rw [squareSide, mul_pow, Real.sq_sqrt Real.pi_nonneg]

/-- The two sets in the theorem really do have equal area. -/
lemma volume_disk_eq_volume_square (r : ℝ) (hr : 0 ≤ r) :
    volume (disk r) = volume (square r) := by
  rw [volume_disk r hr, volume_square r hr]

/-! ## Similarity reduction -/

/-- A positive scalar sends the unit disk to the radius-`r` disk. -/
lemma image_smul_disk (r : ℝ) (hr : 0 < r) :
    (fun x : Plane ↦ r • x) '' disk 1 = disk r := by
  simpa [disk, Real.norm_eq_abs, abs_of_pos hr] using
    (Metric.smul_image_closedBall hr.ne' (0 : Plane) 1)

/-- The same scalar sends the equal-area unit square to the equal-area
radius-`r` square. -/
lemma image_smul_square (r : ℝ) (hr : 0 < r) :
    (fun x : Plane ↦ r • x) '' square 1 = square r := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    change (@WithLp.ofLp 2 (Fin 2 → ℝ) (r • y)) ∈
      Icc (fun _ ↦ -(squareSide r) / 2) (fun _ ↦ squareSide r / 2)
    change (@WithLp.ofLp 2 (Fin 2 → ℝ) y) ∈
      Icc (fun _ ↦ -(squareSide (1 : ℝ)) / 2) (fun _ ↦ squareSide 1 / 2) at hy
    change (∀ i, -(squareSide r) / 2 ≤ (r • y) i) ∧
      ∀ i, (r • y) i ≤ squareSide r / 2
    change (∀ i, -(squareSide (1 : ℝ)) / 2 ≤ y i) ∧
      ∀ i, y i ≤ squareSide 1 / 2 at hy
    constructor
    · intro i
      have h := mul_le_mul_of_nonneg_left (hy.1 i) hr.le
      dsimp [squareSide] at h ⊢
      nlinarith
    · intro i
      have h := mul_le_mul_of_nonneg_left (hy.2 i) hr.le
      dsimp [squareSide] at h ⊢
      nlinarith
  · intro hx
    refine ⟨r⁻¹ • x, ?_, smul_inv_smul₀ hr.ne' x⟩
    change (@WithLp.ofLp 2 (Fin 2 → ℝ) (r⁻¹ • x)) ∈
      Icc (fun _ ↦ -(squareSide (1 : ℝ)) / 2) (fun _ ↦ squareSide 1 / 2)
    change (@WithLp.ofLp 2 (Fin 2 → ℝ) x) ∈
      Icc (fun _ ↦ -(squareSide r) / 2) (fun _ ↦ squareSide r / 2) at hx
    change (∀ i, -(squareSide (1 : ℝ)) / 2 ≤ (r⁻¹ • x) i) ∧
      ∀ i, (r⁻¹ • x) i ≤ squareSide 1 / 2
    change (∀ i, -(squareSide r) / 2 ≤ x i) ∧
      ∀ i, x i ≤ squareSide r / 2 at hx
    constructor
    · intro i
      simp only [PiLp.smul_apply, squareSide, mul_one, smul_eq_mul]
      rw [inv_mul_eq_div]
      apply (le_div_iff₀ hr).2
      have hxi := hx.1 i
      dsimp [squareSide] at hxi
      nlinarith
    · intro i
      simp only [PiLp.smul_apply, squareSide, mul_one, smul_eq_mul]
      rw [inv_mul_eq_div]
      apply (div_le_iff₀ hr).2
      have hxi := hx.2 i
      dsimp [squareSide] at hxi
      nlinarith

/-! ## Finite-displacement matchings -/

/-- A bijection between two sets whose displacement at every source point is
chosen from one fixed finite set gives an equidecomposition by translations. -/
noncomputable def equidecompOfBijOn {A B : Set Plane} (f : Plane → Plane)
    (hf : BijOn f A B) (S : Finset Plane)
    (hS : ∀ x ∈ A, ∃ v ∈ S, f x = v + x) :
    Equidecomp Plane (Multiplicative Plane) where
  toPartialEquiv := hf.toPartialEquiv f A B
  isDecompOn' := by
    refine ⟨S.map Multiplicative.ofAdd.toEmbedding, ?_⟩
    intro x hx
    obtain ⟨v, hv, hfx⟩ := hS x hx
    refine ⟨Multiplicative.ofAdd v, Finset.mem_map.mpr ⟨v, hv, rfl⟩, ?_⟩
    simp [hfx]

@[simp] lemma equidecompOfBijOn_source {A B : Set Plane} (f : Plane → Plane)
    (hf : BijOn f A B) (S : Finset Plane)
    (hS : ∀ x ∈ A, ∃ v ∈ S, f x = v + x) :
    (equidecompOfBijOn f hf S hS).source = A := rfl

@[simp] lemma equidecompOfBijOn_target {A B : Set Plane} (f : Plane → Plane)
    (hf : BijOn f A B) (S : Finset Plane)
    (hS : ∀ x ∈ A, ∃ v ∈ S, f x = v + x) :
    (equidecompOfBijOn f hf S hS).target = B := rfl

/-- It is enough to solve the unit-radius instance: conjugation by a positive
similarity gives every other radius without changing finiteness of the
translation set. -/
lemma translationEquidecomposable_of_unit
    (h : TranslationEquidecomposable (disk 1) (square 1))
    (r : ℝ) (hr : 0 < r) :
    TranslationEquidecomposable (disk r) (square r) := by
  obtain ⟨e, heA, heB⟩ := h
  refine ⟨scaleEquidecomp e r hr.ne', ?_, ?_⟩
  · rw [scaleEquidecomp_source, heA, image_smul_disk r hr]
  · rw [scaleEquidecomp_target, heB, image_smul_square r hr]

/-! ## Circle squaring -/

/-- The unit disk and its equal-area square are equidecomposable by finitely
many translations. -/
theorem unit_translationEquidecomposable :
    TranslationEquidecomposable (disk 1) (square 1) := by
  obtain ⟨w, K, δ, hw, hK, hδ, hbound⟩ :=
    ConcreteDiscrepancy.exists_free_generators_uniform_concrete_dyadic_decay
  have hDisk : TorusLaczkovich.UniformMeanDyadicDensity w
      ConcreteSets.torusDisk ConcreteSets.embeddedMass K δ := by
    intro q x
    exact (hbound q x).1
  have hSquare : TorusLaczkovich.UniformMeanDyadicDensity w
      ConcreteSets.torusSquare ConcreteSets.embeddedMass K δ := by
    intro q x
    exact (hbound q x).2
  obtain ⟨D, e, heSource, heTarget, _heFinite⟩ :=
    TorusLaczkovich.exists_equidecomp_of_commonMeanDyadicDensity
      w hw ConcreteSets.torusDisk ConcreteSets.torusSquare
      ConcreteSets.embeddedMass K δ
      (by norm_num [ProductOrbit.productDimension])
      ConcreteSets.embeddedMass_pos hK.le hδ hDisk hSquare
  have heSource' : e.source =
      TorusTransfer.quotientMap ''
        (Geometry.torusEmbed '' Geometry.unitDisk) := by
    simpa [ConcreteSets.torusDisk, ConcreteSets.embeddedDisk] using heSource
  have heTarget' : e.target =
      TorusTransfer.quotientMap ''
        (Geometry.torusEmbed '' Geometry.equalAreaSquare) := by
    simpa [ConcreteSets.torusSquare, ConcreteSets.embeddedSquare] using heTarget
  obtain ⟨e', he'Source, he'Target⟩ :=
    AffineGlue.unit_geometry_equidecomp_of_torus e heSource' heTarget'
  refine ⟨e', ?_, ?_⟩
  · simpa [disk, Geometry.unitDisk] using he'Source
  · calc
      e'.target = Geometry.equalAreaSquare := he'Target
      _ = square 1 := by
        simpa [square, squareSide] using
          AffineGlue.coordinateSquare_one_eq_equalAreaSquare.symm

/-- **Erdős Problem 1124 (Tarski--Laczkovich).**  For every positive radius,
the closed disk and the closed square of the same area have finite
decompositions into pieces paired by translations, hence into congruent
pieces. -/
theorem erdos_1124 (r : ℝ) (hr : 0 < r) :
    TranslationEquidecomposable (disk r) (square r) :=
  translationEquidecomposable_of_unit unit_translationEquidecomposable r hr

end

end Erdos1124
