/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/- Original license: Apache 2.0. Note: This file has been modified. -/
/-
This is a Lean formalization of a solution to Erdős Problem 988.
https://www.erdosproblems.com/forum/thread/988

Informal authors:
- Wolfgang M. Schmidt

Formal authors:
- Codex
- GPT-5.6 Sol

URLs:
- https://github.com/plby/lean-proofs/blob/main/ErdosProblems/Erdos988.md
-/
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

import Mathlib

/-!
# Erdős Problem 988

For a finite subset `P` of the unit two-sphere, its spherical-cap discrepancy is

`sup_C | #(P ∩ C) - area(C) * #P |`.

We prove the quantitative estimate

`P.card ≤ 512 * sphericalCapDiscrepancy P ^ 4`,

and deduce that the infimum of the discrepancies of `n`-point sets tends to infinity.
The proof is the elementary Stolarsky/positive-kernel argument detailed in `tex/988.tex`.

*References:*
- [erdosproblems.com/988](https://www.erdosproblems.com/988)
- [Sc69b] W. M. Schmidt, *Irregularities of distribution. IV*, Invent. Math. 7
  (1969), 55--82.
- D. Bilyk and J. S. Brauchart, *On the lower bounds for the spherical cap
  discrepancy*, arXiv:2502.15984 (2025).
-/

open Filter Finset MeasureTheory Metric Set
open scoped BigOperators ComplexConjugate ENNReal NNReal Pointwise Topology

namespace Erdos988

noncomputable section

/-- Ambient Euclidean three-space. -/
abbrev E3 := EuclideanSpace ℝ (Fin 3)

/-- The unit two-sphere. -/
abbrev S2 := Metric.sphere (0 : E3) 1

/-- A fixed point of the unit two-sphere. -/
def northPole : S2 :=
  ⟨EuclideanSpace.single (0 : Fin 3) 1, by
    simp [Metric.mem_sphere, dist_zero_right]⟩

instance : Nonempty S2 := ⟨northPole⟩

/-- An explicit meridian used to witness that the two-sphere is infinite. -/
def meridianVector (t : ℝ) : E3 :=
  EuclideanSpace.single (0 : Fin 3) (Real.sqrt (1 - t ^ 2)) +
    EuclideanSpace.single (1 : Fin 3) t

def meridian (t : Set.Ioo (-1 : ℝ) 1) : S2 :=
  ⟨meridianVector t, by
    have ht0 : 0 ≤ 1 - (t : ℝ) ^ 2 := by
      rcases t.property with ⟨htneg, htpos⟩
      nlinarith
    rw [mem_sphere_zero_iff_norm, EuclideanSpace.norm_eq]
    simp [meridianVector, Fin.sum_univ_three, Real.sq_sqrt ht0]⟩

lemma meridian_injective : Function.Injective meridian := by
  intro s t hst
  apply Subtype.ext
  have hcoord := congrArg (fun x : E3 ↦ x (1 : Fin 3)) (congrArg Subtype.val hst)
  simpa [meridian, meridianVector] using hcoord

instance : Infinite S2 :=
  letI : Infinite (Set.Ioo (-1 : ℝ) 1) := Set.Ioo.infinite (by norm_num)
  Infinite.of_injective meridian meridian_injective

/-- The closed spherical cap with center `u` and inner-product threshold `t`. -/
def sphericalCap (u : S2) (t : ℝ) : Set S2 :=
  {x | t ≤ inner ℝ (x : E3) (u : E3)}

/-- The normalized area of a cap with threshold `t ∈ [-1,1]`. -/
def capArea (t : ℝ) : ℝ := (1 - t) / 2

/-- Finite surface measure on the unit sphere, constructed from ambient Haar measure. -/
def surfaceFiniteMeasure : FiniteMeasure S2 :=
  ⟨(volume : Measure E3).toSphere, inferInstance⟩

/-- Probability-normalized surface area on the unit sphere. -/
def surfaceProbability : ProbabilityMeasure S2 :=
  surfaceFiniteMeasure.normalize

/-- Real-valued normalized surface area. -/
def normalizedArea (A : Set S2) : ℝ := (surfaceProbability A : ℝ)

/-! ## Exact moments of normalized surface area -/

/-- A linear isometry of ambient three-space induces an equivalence of the sphere. -/
noncomputable def sphereEquiv (e : E3 ≃ₗᵢ[ℝ] E3) : S2 ≃ S2 where
  toFun x := ⟨e x, by simpa [Metric.mem_sphere] using x.property⟩
  invFun x := ⟨e.symm x, by simpa [Metric.mem_sphere] using x.property⟩
  left_inv x := Subtype.ext (e.symm_apply_apply x)
  right_inv x := Subtype.ext (e.apply_symm_apply x)

/-- The induced sphere equivalence is measurable in both directions. -/
noncomputable def sphereMeasurableEquiv (e : E3 ≃ₗᵢ[ℝ] E3) : S2 ≃ᵐ S2 where
  toEquiv := sphereEquiv e
  measurable_toFun := Measurable.subtype_mk
    (e.continuous.measurable.comp measurable_subtype_coe)
  measurable_invFun := Measurable.subtype_mk
    (e.symm.continuous.measurable.comp measurable_subtype_coe)

@[simp] lemma sphereEquiv_coe (e : E3 ≃ₗᵢ[ℝ] E3) (x : S2) :
    ((sphereEquiv e x : S2) : E3) = e x := rfl

@[simp] lemma sphereMeasurableEquiv_coe (e : E3 ≃ₗᵢ[ℝ] E3) (x : S2) :
    ((sphereMeasurableEquiv e x : S2) : E3) = e x := rfl

private lemma sphere_sector_eq_image (s : Set S2) :
    Set.Ioo (0 : ℝ) 1 • ((↑) '' s) =
      ((↑) : ({0}ᶜ : Set E3) → E3) ''
        ((homeomorphUnitSphereProd E3).symm ''
          (s ×ˢ Set.Iio ⟨1, by simp⟩)) := by
  ext x
  constructor
  · rintro ⟨t, ht, z, ⟨y, hy, rfl⟩, rfl⟩
    refine ⟨⟨t • y, ?_⟩, ⟨(y, ⟨t, ht.1⟩), ⟨hy, ht.2⟩, ?_⟩, rfl⟩
    · exact smul_ne_zero ht.1.ne' (ne_of_mem_sphere y.property one_ne_zero)
    · apply Subtype.ext
      simp
  · rintro ⟨z, ⟨p, ⟨hp₁, hp₂⟩, rfl⟩, rfl⟩
    refine ⟨p.2, ⟨p.2.property, hp₂⟩, p.1, ⟨p.1, hp₁, rfl⟩, ?_⟩
    simp

private lemma measurableSet_sphere_sector {s : Set S2} (hs : MeasurableSet s) :
    MeasurableSet (Set.Ioo (0 : ℝ) 1 • ((↑) '' s) : Set E3) := by
  rw [sphere_sector_eq_image]
  apply (MeasurableEmbedding.subtype_coe
    (measurableSet_singleton (0 : E3)).compl).measurableSet_image'
  apply (homeomorphUnitSphereProd E3).symm.measurableEmbedding.measurableSet_image'
  exact hs.prod measurableSet_Iio

private lemma sphere_sector_preimage (e : E3 ≃ₗᵢ[ℝ] E3) (s : Set S2) :
    e ⁻¹' (Set.Ioo (0 : ℝ) 1 • ((↑) '' s)) =
      Set.Ioo (0 : ℝ) 1 • ((↑) '' ((sphereEquiv e) ⁻¹' s)) := by
  ext x
  constructor
  · rintro ⟨t, ht, z, ⟨y, hys, rfl⟩, hxy⟩
    refine ⟨t, ht, e.symm y,
      ⟨⟨e.symm y, by simpa [Metric.mem_sphere] using y.property⟩, ?_, rfl⟩, ?_⟩
    · change sphereEquiv e
        ⟨e.symm y, by simpa [Metric.mem_sphere] using y.property⟩ ∈ s
      simpa only [sphereEquiv, Equiv.coe_fn_mk, LinearIsometryEquiv.apply_symm_apply]
        using hys
    · apply e.injective
      simpa using hxy
  · rintro ⟨t, ht, z, ⟨y, hy, rfl⟩, hxy⟩
    refine ⟨t, ht, sphereEquiv e y, ⟨sphereEquiv e y, hy, rfl⟩, ?_⟩
    simpa using congrArg e hxy

/-- Unnormalized surface measure is invariant under ambient orthogonal transformations. -/
private theorem rawSurface_measurePreserving (e : E3 ≃ₗᵢ[ℝ] E3) :
    MeasurePreserving (sphereEquiv e)
      (volume : Measure E3).toSphere (volume : Measure E3).toSphere := by
  have hemeas : Measurable (sphereEquiv e) := (sphereMeasurableEquiv e).measurable
  refine ⟨hemeas, ?_⟩
  ext s hs
  rw [Measure.map_apply hemeas hs,
    Measure.toSphere_apply' volume
      (hs.preimage hemeas),
    Measure.toSphere_apply' volume hs, ← sphere_sector_preimage e s]
  congr 1
  exact e.measurePreserving.measure_preimage
    (measurableSet_sphere_sector hs).nullMeasurableSet

/-- Normalized surface area is invariant under every ambient orthogonal transformation. -/
theorem surfaceProbability_measurePreserving (e : E3 ≃ₗᵢ[ℝ] E3) :
    MeasurePreserving (sphereMeasurableEquiv e)
      (surfaceProbability : Measure S2) (surfaceProbability : Measure S2) := by
  refine ⟨(sphereMeasurableEquiv e).measurable, ?_⟩
  ext A hA
  rw [Measure.map_apply (sphereMeasurableEquiv e).measurable hA]
  change (surfaceFiniteMeasure.normalize : Measure S2)
      ((sphereEquiv e) ⁻¹' A) =
    (surfaceFiniteMeasure.normalize : Measure S2) A
  rw [surfaceFiniteMeasure.toMeasure_normalize_eq_of_nonzero
    (by
      intro h
      apply (volume : Measure E3).toSphere_ne_zero
      exact congrArg FiniteMeasure.toMeasure h)]
  simp only [Measure.smul_apply, smul_eq_mul]
  congr 1
  exact (rawSurface_measurePreserving e).measure_preimage hA.nullMeasurableSet

private lemma coordinateSquare_integrable (i : Fin 3) :
    Integrable (fun x : S2 ↦ ((x : E3) i) ^ 2)
      (surfaceProbability : Measure S2) := by
  apply Continuous.integrable_of_hasCompactSupport
  · fun_prop
  · exact HasCompactSupport.of_compactSpace _

private lemma coordinateSquare_integral_eq (i j : Fin 3) :
    (∫ x : S2, ((x : E3) i) ^ 2 ∂(surfaceProbability : Measure S2)) =
      ∫ x : S2, ((x : E3) j) ^ 2 ∂(surfaceProbability : Measure S2) := by
  let τ : Equiv.Perm (Fin 3) := Equiv.swap i j
  let e : E3 ≃ₗᵢ[ℝ] E3 := LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ τ
  have h := (surfaceProbability_measurePreserving e).integral_comp'
    (fun x : S2 ↦ ((x : E3) i) ^ 2)
  rw [show ∫ x : S2, (((sphereMeasurableEquiv e x : S2) : E3) i) ^ 2
        ∂(surfaceProbability : Measure S2) =
      ∫ x : S2, ((x : E3) j) ^ 2 ∂(surfaceProbability : Measure S2) by
        apply integral_congr_ae
        filter_upwards [] with x
        simp [e, τ]] at h
  exact h.symm

private lemma sum_coordinateSquare (x : S2) : ∑ i : Fin 3, ((x : E3) i) ^ 2 = 1 := by
  rw [← EuclideanSpace.real_norm_sq_eq]
  have hx : ‖(x : E3)‖ = 1 := by
    simpa [Metric.mem_sphere, dist_zero_right] using x.property
  rw [hx, one_pow]

/-- The second moment of every unit coordinate on normalized `S²` is `1/3`. -/
theorem coordinateSquare_integral (i : Fin 3) :
    (∫ x : S2, ((x : E3) i) ^ 2 ∂(surfaceProbability : Measure S2)) = 1 / 3 := by
  have hsum :
      (∫ x : S2, (∑ j : Fin 3, ((x : E3) j) ^ 2)
        ∂(surfaceProbability : Measure S2)) = 1 := by
    rw [integral_congr_ae (Filter.Eventually.of_forall sum_coordinateSquare)]
    simp
  rw [integral_finsetSum Finset.univ (fun j _ ↦ coordinateSquare_integrable j)] at hsum
  have heq : ∀ j : Fin 3,
      (∫ x : S2, ((x : E3) j) ^ 2 ∂(surfaceProbability : Measure S2)) =
        ∫ x : S2, ((x : E3) i) ^ 2 ∂(surfaceProbability : Measure S2) :=
    fun j ↦ coordinateSquare_integral_eq j i
  simp_rw [heq] at hsum
  norm_num at hsum ⊢
  linarith

/-- Exact one-dimensional Gaussian integral used in the polar-coordinate computation. -/
private lemma integral_abs_mul_gaussian_real :
    (∫ x : ℝ, |x| * Real.exp (-x ^ 2)) = 1 := by
  calc
    _ = ∫ x : ℝ, (fun y : ℝ ↦ y * Real.exp (-y ^ 2)) |x| := by
      congr 1
      funext x
      change |x| * Real.exp (-x ^ 2) = |x| * Real.exp (-|x| ^ 2)
      rw [sq_abs]
    _ = 2 * ∫ x in Ioi (0 : ℝ), x * Real.exp (-x ^ 2) :=
      integral_comp_abs (f := fun y : ℝ ↦ y * Real.exp (-y ^ 2))
    _ = 2 * ((1 / (2 : ℝ)) * Real.Gamma ((1 + 1) / 2)) := by
      congr 1
      convert integral_rpow_mul_exp_neg_rpow (p := (2 : ℝ)) (q := (1 : ℝ))
        two_pos (by norm_num) using 1 <;> simp [Real.rpow_one, Real.rpow_two]
    _ = 1 := by norm_num [Real.Gamma_one]

private lemma integral_gaussian_real' :
    (∫ x : ℝ, Real.exp (-x ^ 2)) = Real.sqrt Real.pi := by
  simpa using integral_gaussian (1 : ℝ)

private lemma integral_abs_coord_gaussian_E3 :
    (∫ x : E3, |x.1 0| * Real.exp (-‖x‖ ^ 2)) = Real.pi := by
  rw [← (PiLp.volume_preserving_toLp (Fin 3)).integral_comp
    (MeasurableEquiv.toLp 2 (Fin 3 → ℝ)).measurableEmbedding]
  let g : Fin 3 → ℝ → ℝ := fun i x ↦
    if i = 0 then |x| * Real.exp (-x ^ 2) else Real.exp (-x ^ 2)
  calc
    (∫ x : Fin 3 → ℝ,
        |(WithLp.toLp 2 x).1 0| * Real.exp (-‖WithLp.toLp 2 x‖ ^ 2)) =
        ∫ x : Fin 3 → ℝ, ∏ i, g i (x i) := by
      apply integral_congr_ae
      filter_upwards with x
      dsimp [g]
      rw [PiLp.norm_sq_eq_of_L2]
      simp only [Real.norm_eq_abs, sq_abs, Fin.sum_univ_three, Fin.isValue]
      rw [show -(x 0 ^ 2 + x 1 ^ 2 + x 2 ^ 2) =
        -x 0 ^ 2 + (-x 1 ^ 2 + -x 2 ^ 2) by ring, Real.exp_add, Real.exp_add]
      rw [Fin.prod_univ_three]
      have h10 : (1 : Fin 3) ≠ 0 := by decide
      have h20 : (2 : Fin 3) ≠ 0 := by decide
      simp only [if_pos rfl, if_neg h10, if_neg h20, if_true]
      ring
    _ = ∏ i : Fin 3, ∫ x : ℝ, g i x := by
      exact integral_fintype_prod_volume_eq_prod g
    _ = Real.pi := by
      rw [Fin.prod_univ_three]
      have h10 : (1 : Fin 3) ≠ 0 := by decide
      have h20 : (2 : Fin 3) ≠ 0 := by decide
      simp only [g, if_pos rfl, if_neg h10, if_neg h20]
      simp_rw [integral_abs_mul_gaussian_real, integral_gaussian_real']
      nlinarith [Real.sq_sqrt Real.pi_nonneg]

private lemma integral_radial_abs_gaussian_E3 :
    (∫ r : Ioi (0 : ℝ), r.1 * Real.exp (-r.1 ^ 2) ∂Measure.volumeIoiPow 2) =
      1 / 2 := by
  simp only [Measure.volumeIoiPow, ENNReal.ofReal]
  rw [integral_withDensity_eq_integral_smul,
    integral_subtype_comap measurableSet_Ioi
      (fun a : ℝ ↦ Real.toNNReal (a ^ 2) • (a * Real.exp (-a ^ 2)))]
  · calc
      (∫ a in Ioi (0 : ℝ), Real.toNNReal (a ^ 2) •
          (a * Real.exp (-a ^ 2))) =
          ∫ a in Ioi (0 : ℝ), a ^ (3 : ℝ) * Real.exp (-a ^ (2 : ℝ)) := by
        apply setIntegral_congr_fun measurableSet_Ioi
        intro a ha
        change (Real.toNNReal (a ^ 2) : ℝ) * (a * Real.exp (-a ^ 2)) =
          a ^ (3 : ℝ) * Real.exp (-a ^ (2 : ℝ))
        rw [Real.coe_toNNReal _ (sq_nonneg a)]
        ring_nf
        calc
          a ^ (3 : ℕ) * Real.exp (-a ^ (2 : ℕ)) =
              a ^ (3 : ℝ) * Real.exp (-a ^ (2 : ℕ)) :=
            congrArg (fun z : ℝ ↦ z * Real.exp (-a ^ (2 : ℕ)))
              (Real.rpow_natCast a 3).symm
          _ = a ^ (3 : ℝ) * Real.exp (-a ^ (2 : ℝ)) :=
            congrArg (fun z : ℝ ↦ a ^ (3 : ℝ) * Real.exp (-z))
              (Real.rpow_natCast a 2).symm
      _ = (1 / (2 : ℝ)) * Real.Gamma (((3 : ℝ) + 1) / 2) := by
        exact integral_rpow_mul_exp_neg_rpow two_pos (by norm_num)
      _ = 1 / 2 := by norm_num [Real.Gamma_add_one, Real.Gamma_one]
  · exact (measurable_subtype_coe.pow_const 2).real_toNNReal

/-- Unnormalized surface integral of the absolute first coordinate. -/
private lemma integral_abs_coord_sphere_raw :
    (∫ x : S2, |x.1 0| ∂(volume : Measure E3).toSphere) = 2 * Real.pi := by
  let angular : S2 → ℝ := fun x ↦ |x.1 0|
  let radial : Ioi (0 : ℝ) → ℝ := fun r ↦ r.1 * Real.exp (-r.1 ^ 2)
  have hpolar := (volume : Measure E3).measurePreserving_homeomorphUnitSphereProd.integral_comp
    (homeomorphUnitSphereProd E3).measurableEmbedding
    (fun p : S2 × Ioi (0 : ℝ) ↦ angular p.1 * radial p.2)
  have hleft :
      (∫ x : E3, |x.1 0| * Real.exp (-‖x‖ ^ 2)) =
        ∫ x : ({(0 : E3)}ᶜ : Set E3),
          angular (homeomorphUnitSphereProd E3 x).1 *
            radial (homeomorphUnitSphereProd E3 x).2
              ∂((volume : Measure E3).comap ((↑) : ({(0 : E3)}ᶜ : Set E3) → E3)) := by
    calc
      _ = ∫ x : ({(0 : E3)}ᶜ : Set E3),
          |x.1.1 0| * Real.exp (-‖x.1‖ ^ 2)
            ∂((volume : Measure E3).comap ((↑) : ({(0 : E3)}ᶜ : Set E3) → E3)) := by
        rw [integral_subtype_comap (measurableSet_singleton (0 : E3)).compl
              (fun x : E3 ↦ |x.1 0| * Real.exp (-‖x‖ ^ 2)),
          restrict_compl_singleton]
      _ = _ := by
        apply integral_congr_ae
        filter_upwards with x
        have hx0 : x.1 ≠ 0 := by
          simpa only [Set.mem_compl_iff, Set.mem_singleton_iff] using x.property
        have hxnorm : 0 < ‖x.1‖ := norm_pos_iff.mpr hx0
        simp only [angular, radial, homeomorphUnitSphereProd_apply_fst_coe,
          homeomorphUnitSphereProd_apply_snd_coe]
        simp [PiLp.smul_apply, abs_mul, abs_inv, abs_of_pos hxnorm,
          inv_mul_cancel₀ hxnorm.ne']
        field_simp [hxnorm.ne']
  have hamb := integral_abs_coord_gaussian_E3
  rw [hleft, hpolar, integral_prod_mul] at hamb
  simp only [finrank_euclideanSpace_fin, Nat.reduceSubDiff] at hamb
  dsimp [angular, radial] at hamb
  rw [integral_radial_abs_gaussian_E3] at hamb
  norm_num at hamb ⊢
  linarith [hamb]

private lemma surfaceFiniteMeasure_ne_zero : surfaceFiniteMeasure ≠ 0 := by
  intro h
  apply (volume : Measure E3).toSphere_ne_zero
  exact congrArg FiniteMeasure.toMeasure h

private lemma sphere_raw_mass :
    (volume : Measure E3).toSphere.real univ = 4 * Real.pi := by
  rw [Measure.toSphere_real_apply_univ]
  simp only [finrank_euclideanSpace_fin, Nat.cast_ofNat]
  rw [measureReal_def,
    InnerProductSpace.volume_ball_of_dim_odd (E := E3) (k := 1) (by simp) 0 1]
  norm_num [ENNReal.toReal_ofReal, Real.pi_pos.le]
  rw [ENNReal.toReal_ofReal (by positivity : 0 ≤ Real.pi * 4 / 3)]
  ring

/-- The normalized mean absolute value of the first coordinate is `1/2`. -/
theorem coordinateAbs_integral :
    (∫ x : S2, |(x : E3) 0| ∂(surfaceProbability : Measure S2)) = 1 / 2 := by
  change (∫ x : S2, |(x : E3) 0|
    ∂(surfaceFiniteMeasure.normalize : Measure S2)) = 1 / 2
  rw [← surfaceFiniteMeasure.average_eq_integral_normalize
    surfaceFiniteMeasure_ne_zero (fun x : S2 ↦ |(x : E3) 0|)]
  rw [MeasureTheory.average_eq]
  change ((volume : Measure E3).toSphere.real univ)⁻¹ *
    (∫ x : S2, |(x : E3) 0| ∂(volume : Measure E3).toSphere) = 1 / 2
  rw [integral_abs_coord_sphere_raw, sphere_raw_mass]
  field_simp [Real.pi_ne_zero]
  <;> ring

private lemma northPole_inner (x : E3) : inner ℝ (northPole : E3) x = x 0 := by
  simp [northPole, EuclideanSpace.inner_single_left]

/-- For a unit vector, the second moment of its projection is `1/3`. -/
theorem unitInnerSquare_integral (u : E3) (hu : ‖u‖ = 1) :
    (∫ x : S2, (inner ℝ u (x : E3)) ^ 2
      ∂(surfaceProbability : Measure S2)) = 1 / 3 := by
  let e : E3 ≃ₗᵢ[ℝ] E3 := ((ℝ ∙ ((northPole : E3) - u))ᗮ).reflection
  have heu : e (northPole : E3) = u := by
    exact Submodule.reflection_sub (by simp [northPole, hu])
  have h := (surfaceProbability_measurePreserving e).integral_comp'
    (fun x : S2 ↦ (inner ℝ u (x : E3)) ^ 2)
  have hpoint (x : S2) :
      inner ℝ u ((sphereMeasurableEquiv e x : S2) : E3) = (x : E3) 0 := by
    rw [sphereMeasurableEquiv_coe, ← heu, LinearIsometryEquiv.inner_map_map]
    exact northPole_inner x
  rw [integral_congr_ae (Filter.Eventually.of_forall (fun x ↦
    congrArg (fun z : ℝ ↦ z ^ 2) (hpoint x)))] at h
  exact h.symm.trans (coordinateSquare_integral 0)

/-- Exact normalized absolute projection moment in every direction. -/
theorem innerAbs_integral (u : E3) :
    (∫ x : S2, |inner ℝ u (x : E3)| ∂(surfaceProbability : Measure S2)) =
      ‖u‖ / 2 := by
  rcases eq_or_ne u 0 with rfl | hu
  · simp
  let w : E3 := ‖u‖⁻¹ • u
  have hnorm : 0 < ‖u‖ := norm_pos_iff.mpr hu
  have hw : ‖w‖ = 1 := by
    simp [w, norm_smul, abs_of_pos hnorm, hnorm.ne']
  let e : E3 ≃ₗᵢ[ℝ] E3 := ((ℝ ∙ ((northPole : E3) - w))ᗮ).reflection
  have hew : e (northPole : E3) = w := by
    exact Submodule.reflection_sub (by simp [northPole, hw])
  have hinv := (surfaceProbability_measurePreserving e).integral_comp'
    (fun x : S2 ↦ |inner ℝ w (x : E3)|)
  have hunit :
      (∫ x : S2, |inner ℝ w (x : E3)| ∂(surfaceProbability : Measure S2)) =
        1 / 2 := by
    calc
      _ = ∫ x : S2,
          |inner ℝ w ((sphereMeasurableEquiv e x : S2) : E3)|
            ∂(surfaceProbability : Measure S2) := hinv.symm
      _ = ∫ x : S2, |(x : E3) 0| ∂(surfaceProbability : Measure S2) := by
        apply integral_congr_ae
        filter_upwards [] with x
        rw [sphereMeasurableEquiv_coe, ← hew, LinearIsometryEquiv.inner_map_map,
          northPole_inner]
      _ = 1 / 2 := coordinateAbs_integral
  have hu_rep : u = ‖u‖ • w := by simp [w, hnorm.ne']
  calc
    (∫ x : S2, |inner ℝ u (x : E3)| ∂(surfaceProbability : Measure S2)) =
        ∫ x : S2, ‖u‖ * |inner ℝ w (x : E3)|
          ∂(surfaceProbability : Measure S2) := by
      apply integral_congr_ae
      filter_upwards [] with x
      calc
        |inner ℝ u (x : E3)| = |‖u‖ * inner ℝ w (x : E3)| := by
          have hi := congrArg (fun z : E3 ↦ inner ℝ z (x : E3)) hu_rep
          rw [real_inner_smul_left] at hi
          exact congrArg abs hi
        _ = ‖u‖ * |inner ℝ w (x : E3)| := by
          rw [abs_mul, abs_of_nonneg (norm_nonneg u)]
    _ = ‖u‖ * (∫ x : S2, |inner ℝ w (x : E3)|
          ∂(surfaceProbability : Measure S2)) := by rw [integral_const_mul]
    _ = ‖u‖ / 2 := by rw [hunit]; ring

/-- Mean absolute difference of two coordinate projections equals half their chordal distance. -/
theorem innerDifferenceAbs_integral (x y : S2) :
    (∫ u : S2, |inner ℝ (x : E3) (u : E3) - inner ℝ (y : E3) (u : E3)|
      ∂(surfaceProbability : Measure S2)) = dist x y / 2 := by
  calc
    _ = ∫ u : S2, |inner ℝ ((x : E3) - (y : E3)) (u : E3)|
          ∂(surfaceProbability : Measure S2) := by
      apply integral_congr_ae
      filter_upwards [] with u
      simp only [inner_sub_left]
    _ = ‖(x : E3) - (y : E3)‖ / 2 := innerAbs_integral _
    _ = dist x y / 2 := by rw [Subtype.dist_eq, dist_eq_norm]

/-- The signed counting error of a cap. -/
noncomputable def signedCapError (P : Finset S2) (u : S2) (t : ℝ) : ℝ := by
  classical
  exact ((P.filter fun x ↦ x ∈ sphericalCap u t).card : ℝ) -
    capArea t * P.card

/-- The absolute counting error of a cap. -/
noncomputable def capError (P : Finset S2) (u : S2) (t : ℝ) : ℝ :=
  |signedCapError P u t|

/-- All absolute cap errors of `P`. -/
noncomputable def capErrorSet (P : Finset S2) : Set ℝ :=
  {r | ∃ u : S2, ∃ t : ℝ, t ∈ Set.Icc (-1 : ℝ) 1 ∧ r = capError P u t}

/-- Spherical-cap discrepancy.  The `sSup` is the precise meaning of the customary
maximum over the compact family of cap parameters. -/
noncomputable def sphericalCapDiscrepancy (P : Finset S2) : ℝ :=
  sSup (capErrorSet P)

/-- The infimum of spherical-cap discrepancies among `n`-point subsets. -/
noncomputable def minimumDiscrepancy (n : ℕ) : ℝ :=
  sInf {d : ℝ | ∃ P : Finset S2, P.card = n ∧ d = sphericalCapDiscrepancy P}

lemma sphere2_norm (x : S2) : ‖(x : E3)‖ = 1 := by
  simpa [Metric.mem_sphere, dist_zero_right] using x.property

lemma inner_mem_Icc (x u : S2) : inner ℝ (x : E3) (u : E3) ∈ Set.Icc (-1 : ℝ) 1 := by
  have h := abs_real_inner_le_norm (x : E3) (u : E3)
  rw [sphere2_norm x, sphere2_norm u, mul_one] at h
  exact (abs_le.mp h)

lemma measurableSet_sphericalCap (u : S2) (t : ℝ) :
    MeasurableSet (sphericalCap u t) := by
  apply (isClosed_le continuous_const
    (Continuous.inner continuous_subtype_val continuous_const)).measurableSet

lemma sphere2_dist_sq (u x : S2) :
    dist u x ^ 2 = 2 - 2 * inner ℝ (u : E3) (x : E3) := by
  rw [Subtype.dist_eq, dist_eq_norm, norm_sub_sq_real, sphere2_norm, sphere2_norm]
  ring

lemma mem_sphericalCap_iff_dist_sq_le (u x : S2) (t : ℝ) :
    x ∈ sphericalCap u t ↔ dist u x ^ 2 ≤ 2 - 2 * t := by
  change t ≤ inner ℝ (x : E3) (u : E3) ↔ _
  rw [sphere2_dist_sq]
  rw [real_inner_comm]
  constructor <;> intro h <;> linarith

lemma capArea_nonneg {t : ℝ} (ht : t ∈ Set.Icc (-1 : ℝ) 1) : 0 ≤ capArea t := by
  simp only [Set.mem_Icc] at ht
  unfold capArea
  linarith

lemma capArea_le_one {t : ℝ} (ht : t ∈ Set.Icc (-1 : ℝ) 1) : capArea t ≤ 1 := by
  simp only [Set.mem_Icc] at ht
  unfold capArea
  linarith

lemma normalizedArea_nonneg (A : Set S2) : 0 ≤ normalizedArea A := by
  unfold normalizedArea
  positivity

lemma normalizedArea_le_one (A : Set S2) : normalizedArea A ≤ 1 := by
  exact_mod_cast ProbabilityMeasure.apply_le_one surfaceProbability A

lemma capError_nonneg (P : Finset S2) (u : S2) (t : ℝ) : 0 ≤ capError P u t := by
  exact abs_nonneg _

lemma capError_le_card (P : Finset S2) (u : S2) {t : ℝ}
    (ht : t ∈ Set.Icc (-1 : ℝ) 1) : capError P u t ≤ P.card := by
  classical
  have hfilter := Finset.card_filter_le P (fun x ↦ x ∈ sphericalCap u t)
  have hfilter' :
      (((P.filter fun x ↦ x ∈ sphericalCap u t).card : ℕ) : ℝ) ≤ P.card := by
    exact_mod_cast hfilter
  have hfilter0 :
      (0 : ℝ) ≤ ((P.filter fun x ↦ x ∈ sphericalCap u t).card : ℕ) := by positivity
  have harea0 := capArea_nonneg ht
  have harea1 := capArea_le_one ht
  have hn : (0 : ℝ) ≤ P.card := by positivity
  rw [capError, abs_le]
  constructor <;> unfold signedCapError <;> nlinarith

lemma capErrorSet_nonempty (P : Finset S2) : (capErrorSet P).Nonempty := by
  exact ⟨capError P northPole 0, northPole, 0, by norm_num, rfl⟩

lemma capErrorSet_bddAbove (P : Finset S2) : BddAbove (capErrorSet P) := by
  refine ⟨P.card, ?_⟩
  rintro r ⟨u, t, ht, rfl⟩
  exact capError_le_card P u ht

lemma capError_le_discrepancy (P : Finset S2) (u : S2) {t : ℝ}
    (ht : t ∈ Set.Icc (-1 : ℝ) 1) :
    capError P u t ≤ sphericalCapDiscrepancy P := by
  apply le_csSup (capErrorSet_bddAbove P)
  exact ⟨u, t, ht, rfl⟩

lemma sphericalCapDiscrepancy_nonneg (P : Finset S2) :
    0 ≤ sphericalCapDiscrepancy P := by
  exact (capError_nonneg P northPole 0).trans
    (capError_le_discrepancy P northPole (by norm_num))

lemma sphericalCapDiscrepancy_le_card (P : Finset S2) :
    sphericalCapDiscrepancy P ≤ P.card := by
  apply csSup_le (capErrorSet_nonempty P)
  rintro r ⟨u, t, ht, rfl⟩
  exact capError_le_card P u ht

lemma fixedCardDiscrepancies_nonempty (n : ℕ) :
    {d : ℝ | ∃ P : Finset S2, P.card = n ∧
      d = sphericalCapDiscrepancy P}.Nonempty := by
  obtain ⟨P, hP⟩ := Finset.exists_card_eq (α := S2) n
  exact ⟨sphericalCapDiscrepancy P, P, hP, rfl⟩

lemma fixedCardDiscrepancies_bddBelow (n : ℕ) :
    BddBelow {d : ℝ | ∃ P : Finset S2, P.card = n ∧
      d = sphericalCapDiscrepancy P} := by
  refine ⟨0, ?_⟩
  rintro d ⟨P, -, rfl⟩
  exact sphericalCapDiscrepancy_nonneg P

lemma minimumDiscrepancy_nonneg (n : ℕ) : 0 ≤ minimumDiscrepancy n := by
  apply le_csInf (fixedCardDiscrepancies_nonempty n)
  rintro d ⟨P, -, rfl⟩
  exact sphericalCapDiscrepancy_nonneg P

lemma minimumDiscrepancy_le (P : Finset S2) :
    minimumDiscrepancy P.card ≤ sphericalCapDiscrepancy P := by
  exact csInf_le (fixedCardDiscrepancies_bddBelow P.card) ⟨P, rfl, rfl⟩

/-- A uniform fourth-power discrepancy estimate implies the desired divergence. -/
theorem minimumDiscrepancy_tendsto_of_card_le_512_mul_pow_four
    (hpoly : ∀ P : Finset S2,
      (P.card : ℝ) ≤ 512 * sphericalCapDiscrepancy P ^ 4) :
    Tendsto minimumDiscrepancy atTop atTop := by
  rw [Filter.tendsto_atTop]
  intro B
  obtain ⟨N : ℕ, hN⟩ := exists_nat_gt (512 * max B 0 ^ 4)
  filter_upwards [eventually_ge_atTop N] with n hn
  apply le_csInf (fixedCardDiscrepancies_nonempty n)
  rintro d ⟨P, hcard, rfl⟩
  by_contra hB
  have hDB : sphericalCapDiscrepancy P < B := lt_of_not_ge hB
  have hB0 : 0 < B := (sphericalCapDiscrepancy_nonneg P).trans_lt hDB
  have hpow : sphericalCapDiscrepancy P ^ 4 < B ^ 4 := by
    exact pow_lt_pow_left₀ hDB (sphericalCapDiscrepancy_nonneg P) (by norm_num)
  have hpolyP := hpoly P
  rw [hcard] at hpolyP
  have hnR : (N : ℝ) ≤ n := by exact_mod_cast hn
  rw [max_eq_left hB0.le] at hN
  nlinarith

/-! ## Distance energy -/

/-- The shifted and rescaled inner product used in the positive-kernel argument. -/
def normalizedDot (x y : S2) : ℝ := (1 + inner ℝ (x : E3) (y : E3)) / 2

lemma normalizedDot_nonneg (x y : S2) : 0 ≤ normalizedDot x y := by
  have h := (inner_mem_Icc x y).1
  unfold normalizedDot
  linarith

lemma normalizedDot_le_one (x y : S2) : normalizedDot x y ≤ 1 := by
  have h := (inner_mem_Icc x y).2
  unfold normalizedDot
  linarith

@[simp] lemma normalizedDot_self (x : S2) : normalizedDot x x = 1 := by
  rw [normalizedDot, real_inner_self_eq_norm_sq, sphere2_norm]
  norm_num

/-- The `k`-th shifted-inner-product energy of a finite point set. -/
noncomputable def powerSum (P : Finset S2) (k : ℕ) : ℝ :=
  ∑ x ∈ P, ∑ y ∈ P, normalizedDot x y ^ k

lemma powerSum_nonneg (P : Finset S2) (k : ℕ) : 0 ≤ powerSum P k := by
  unfold powerSum
  apply Finset.sum_nonneg
  intro x hx
  apply Finset.sum_nonneg
  intro y hy
  exact pow_nonneg (normalizedDot_nonneg x y) k

lemma card_le_powerSum (P : Finset S2) (k : ℕ) : (P.card : ℝ) ≤ powerSum P k := by
  classical
  calc
    (P.card : ℝ) = ∑ x ∈ P, (1 : ℝ) := by simp
    _ = ∑ x ∈ P, normalizedDot x x ^ k := by simp
    _ ≤ ∑ x ∈ P, ∑ y ∈ P, normalizedDot x y ^ k := by
      apply Finset.sum_le_sum
      intro x hx
      exact Finset.single_le_sum (fun y hy ↦ pow_nonneg (normalizedDot_nonneg x y) k) hx
    _ = powerSum P k := rfl

/-- Deficit of the sum of pairwise chordal distances from the continuous value `4/3`. -/
noncomputable def energyDeficit (P : Finset S2) : ℝ :=
  (4 / 3 : ℝ) * P.card ^ 2 - ∑ x ∈ P, ∑ y ∈ P, dist x y

/-! ## The one-dimensional Stolarsky kernel -/

/-- A cap indicator centered by the normalized cap area. -/
def centeredLowerIndicator (a t : ℝ) : ℝ :=
  (if t ≤ a then 1 else 0) - (1 - t) / 2

private lemma intervalIntegral_one_sub_div_two (a : ℝ) :
    ∫ t in (-1 : ℝ)..a, (1 - t) / 2 = 3 / 4 + a / 2 - a ^ 2 / 4 := by
  have h1 : IntervalIntegrable (fun _ : ℝ ↦ (1 : ℝ)) volume (-1) a :=
    continuous_const.intervalIntegrable _ _
  have hid : IntervalIntegrable (fun t : ℝ ↦ t) volume (-1) a :=
    continuous_id.intervalIntegrable _ _
  rw [intervalIntegral.integral_div, intervalIntegral.integral_sub h1 hid]
  simp only [intervalIntegral.integral_const, integral_id]
  ring

private lemma intervalIntegral_one_sub_div_two_sq :
    ∫ t in (-1 : ℝ)..1, ((1 - t) / 2) ^ 2 = 2 / 3 := by
  have hpow : ∫ t in (-1 : ℝ)..1, t ^ 2 = (2 / 3 : ℝ) := by
    rw [integral_pow]
    norm_num
  rw [show (fun t : ℝ ↦ ((1 - t) / 2) ^ 2) =
      fun t ↦ (1 - 2 * t + t ^ 2) / 4 by funext t; ring]
  have h1 : IntervalIntegrable (fun _ : ℝ ↦ (1 : ℝ)) volume (-1) 1 :=
    continuous_const.intervalIntegrable _ _
  have htwoId : IntervalIntegrable (fun t : ℝ ↦ 2 * t) volume (-1) 1 :=
    (continuous_const.mul continuous_id).intervalIntegrable _ _
  have hsq : IntervalIntegrable (fun t : ℝ ↦ t ^ 2) volume (-1) 1 :=
    (continuous_id.pow 2).intervalIntegrable _ _
  rw [intervalIntegral.integral_div,
    intervalIntegral.integral_add (h1.sub htwoId) hsq,
    intervalIntegral.integral_sub h1 htwoId]
  have htwo : ∫ t in (-1 : ℝ)..1, 2 * t = 0 := by
    rw [intervalIntegral.integral_const_mul, integral_id]
    norm_num
  simp only [intervalIntegral.integral_const, htwo, hpow]
  norm_num

private lemma intervalIntegral_lowerIndicator_mul_lowerIndicator
    {a b : ℝ} (ha : a ∈ Set.Icc (-1 : ℝ) 1) (hb : b ∈ Set.Icc (-1 : ℝ) 1) :
    ∫ t in (-1 : ℝ)..1,
      (if t ≤ a then (1 : ℝ) else 0) * (if t ≤ b then (1 : ℝ) else 0) =
        1 + min a b := by
  have hm : min a b ∈ Set.Icc (-1 : ℝ) 1 :=
    ⟨by simp [ha.1, hb.1], by simp [ha.2, hb.2]⟩
  have hfun : (fun t : ℝ ↦
      (if t ≤ a then (1 : ℝ) else 0) * (if t ≤ b then (1 : ℝ) else 0)) =
      {t : ℝ | t ≤ min a b}.indicator (fun _ ↦ (1 : ℝ)) := by
    funext t
    simp only [Set.indicator, Set.mem_setOf_eq]
    by_cases hta : t ≤ a <;> by_cases htb : t ≤ b <;> simp [hta, htb, le_min_iff]
  rw [hfun, intervalIntegral.integral_indicator hm]
  simp [add_comm]

private lemma intervalIntegral_lowerIndicator_mul_capMass
    {a : ℝ} (ha : a ∈ Set.Icc (-1 : ℝ) 1) :
    ∫ t in (-1 : ℝ)..1,
      (if t ≤ a then (1 : ℝ) else 0) * ((1 - t) / 2) =
        3 / 4 + a / 2 - a ^ 2 / 4 := by
  have hfun : (fun t : ℝ ↦
      (if t ≤ a then (1 : ℝ) else 0) * ((1 - t) / 2)) =
      {t : ℝ | t ≤ a}.indicator (fun t ↦ (1 - t) / 2) := by
    funext t
    simp only [Set.indicator, Set.mem_setOf_eq]
    by_cases ht : t ≤ a <;> simp [ht]
  rw [hfun, intervalIntegral.integral_indicator ha,
    intervalIntegral_one_sub_div_two]

/-- Exact covariance of two centered one-dimensional cap indicators. -/
theorem intervalIntegral_centeredLowerIndicator_mul
    {a b : ℝ} (ha : a ∈ Set.Icc (-1 : ℝ) 1) (hb : b ∈ Set.Icc (-1 : ℝ) 1) :
    ∫ t in (-1 : ℝ)..1,
      centeredLowerIndicator a t * centeredLowerIndicator b t =
        1 / 6 + (a ^ 2 + b ^ 2) / 4 - |a - b| / 2 := by
  rw [show (fun t : ℝ ↦ centeredLowerIndicator a t * centeredLowerIndicator b t) =
      fun t ↦
        ((if t ≤ a then (1 : ℝ) else 0) * (if t ≤ b then (1 : ℝ) else 0) -
          (if t ≤ a then (1 : ℝ) else 0) * ((1 - t) / 2)) -
          (if t ≤ b then (1 : ℝ) else 0) * ((1 - t) / 2) +
          ((1 - t) / 2) ^ 2 by funext t; simp only [centeredLowerIndicator]; ring]
  have qaanti : Antitone (fun t : ℝ ↦ if t ≤ a then (1 : ℝ) else 0) := by
    intro s t hst
    by_cases hsa : s ≤ a <;> by_cases hta : t ≤ a <;> simp [hsa, hta]
    exact False.elim (hsa (hst.trans hta))
  have qbanti : Antitone (fun t : ℝ ↦ if t ≤ b then (1 : ℝ) else 0) := by
    intro s t hst
    by_cases hsb : s ≤ b <;> by_cases htb : t ≤ b <;> simp [hsb, htb]
    exact False.elim (hsb (hst.trans htb))
  have habInt : IntervalIntegrable (fun t : ℝ ↦
      (if t ≤ a then (1 : ℝ) else 0) * (if t ≤ b then (1 : ℝ) else 0))
      volume (-1) 1 := by
    have hminanti : Antitone (fun t : ℝ ↦ if t ≤ min a b then (1 : ℝ) else 0) := by
      intro s t hst
      by_cases hs : s ≤ min a b <;> by_cases ht : t ≤ min a b <;> simp [hs, ht]
      exact False.elim (hs (hst.trans ht))
    apply hminanti.intervalIntegrable.congr
    intro t ht
    by_cases hta : t ≤ a <;> by_cases htb : t ≤ b <;> simp [hta, htb, le_min_iff]
  have hpcont : Continuous (fun t : ℝ ↦ (1 - t) / 2) :=
    (continuous_const.sub continuous_id).div_const 2
  have haCapInt : IntervalIntegrable (fun t : ℝ ↦
      (if t ≤ a then (1 : ℝ) else 0) * ((1 - t) / 2)) volume (-1) 1 :=
    qaanti.intervalIntegrable.mul_continuousOn hpcont.continuousOn
  have hbCapInt : IntervalIntegrable (fun t : ℝ ↦
      (if t ≤ b then (1 : ℝ) else 0) * ((1 - t) / 2)) volume (-1) 1 :=
    qbanti.intervalIntegrable.mul_continuousOn hpcont.continuousOn
  have hsqInt : IntervalIntegrable (fun t : ℝ ↦ ((1 - t) / 2) ^ 2) volume (-1) 1 :=
    (hpcont.pow 2).intervalIntegrable _ _
  rw [intervalIntegral.integral_add ((habInt.sub haCapInt).sub hbCapInt) hsqInt,
    intervalIntegral.integral_sub (habInt.sub haCapInt) hbCapInt,
    intervalIntegral.integral_sub habInt haCapInt,
    intervalIntegral_lowerIndicator_mul_lowerIndicator ha hb,
    intervalIntegral_lowerIndicator_mul_capMass ha,
    intervalIntegral_lowerIndicator_mul_capMass hb,
    intervalIntegral_one_sub_div_two_sq]
  rw [min_def]
  split_ifs with hab
  · rw [abs_of_nonpos (sub_nonpos.mpr hab)]
    ring
  · rw [abs_of_nonneg (sub_nonneg.mpr (le_of_not_ge hab))]
    ring

/-- The centered cap indicator contributed by one point. -/
def pointCapTerm (x u : S2) (t : ℝ) : ℝ :=
  centeredLowerIndicator (inner ℝ (x : E3) (u : E3)) t

/-- The analytic finite-sum form of the signed cap error. -/
noncomputable def analyticCapError (P : Finset S2) (u : S2) (t : ℝ) : ℝ :=
  ∑ x ∈ P, pointCapTerm x u t

lemma analyticCapError_eq_signedCapError (P : Finset S2) (u : S2) (t : ℝ) :
    analyticCapError P u t = signedCapError P u t := by
  classical
  unfold analyticCapError pointCapTerm centeredLowerIndicator signedCapError capArea
  simp only [Finset.sum_sub_distrib, Finset.sum_ite, Finset.sum_const,
    nsmul_eq_mul, sphericalCap, Set.mem_setOf_eq]
  push_cast
  ring

/-- Integrability companion to `intervalIntegral_centeredLowerIndicator_mul`. -/
theorem intervalIntegrable_centeredLowerIndicator_mul
    {a b : ℝ} (_ha : a ∈ Set.Icc (-1 : ℝ) 1) (_hb : b ∈ Set.Icc (-1 : ℝ) 1) :
    IntervalIntegrable
      (fun t ↦ centeredLowerIndicator a t * centeredLowerIndicator b t)
      volume (-1 : ℝ) 1 := by
  have qaanti : Antitone (fun t : ℝ ↦ if t ≤ a then (1 : ℝ) else 0) := by
    intro s t hst
    by_cases hsa : s ≤ a <;> by_cases hta : t ≤ a <;> simp [hsa, hta]
    exact False.elim (hsa (hst.trans hta))
  have qbanti : Antitone (fun t : ℝ ↦ if t ≤ b then (1 : ℝ) else 0) := by
    intro s t hst
    by_cases hsb : s ≤ b <;> by_cases htb : t ≤ b <;> simp [hsb, htb]
    exact False.elim (hsb (hst.trans htb))
  have habInt : IntervalIntegrable (fun t : ℝ ↦
      (if t ≤ a then (1 : ℝ) else 0) * (if t ≤ b then (1 : ℝ) else 0))
      volume (-1) 1 := by
    have hminanti : Antitone (fun t : ℝ ↦ if t ≤ min a b then (1 : ℝ) else 0) := by
      intro s t hst
      by_cases hs : s ≤ min a b <;> by_cases ht : t ≤ min a b <;> simp [hs, ht]
      exact False.elim (hs (hst.trans ht))
    apply hminanti.intervalIntegrable.congr
    intro t ht
    by_cases hta : t ≤ a <;> by_cases htb : t ≤ b <;> simp [hta, htb]
  have hpcont : Continuous (fun t : ℝ ↦ (1 - t) / 2) :=
    (continuous_const.sub continuous_id).div_const 2
  have haCapInt : IntervalIntegrable (fun t : ℝ ↦
      (if t ≤ a then (1 : ℝ) else 0) * ((1 - t) / 2)) volume (-1) 1 :=
    qaanti.intervalIntegrable.mul_continuousOn hpcont.continuousOn
  have hbCapInt : IntervalIntegrable (fun t : ℝ ↦
      (if t ≤ b then (1 : ℝ) else 0) * ((1 - t) / 2)) volume (-1) 1 :=
    qbanti.intervalIntegrable.mul_continuousOn hpcont.continuousOn
  have hsqInt : IntervalIntegrable (fun t : ℝ ↦ ((1 - t) / 2) ^ 2) volume (-1) 1 :=
    (hpcont.pow 2).intervalIntegrable _ _
  apply ((habInt.sub haCapInt).sub hbCapInt).add hsqInt |>.congr
  intro t ht
  simp only [centeredLowerIndicator]
  ring

/-! The remaining lemmas isolate the finite-sum algebra from the geometric measure theory. -/

variable {X U : Type*}

/-- A finite configuration's centered counting error, written as a finite sum. -/
def finiteDiscrepancyError (P : Finset X) (h : X → U → ℝ → ℝ) (u : U) (t : ℝ) : ℝ :=
  ∑ x ∈ P, h x u t

theorem intervalIntegral_finiteDiscrepancyError_sq
    (P : Finset X) (h : X → U → ℝ → ℝ)
    (hint : ∀ x ∈ P, ∀ y ∈ P, ∀ u,
      IntervalIntegrable (fun t ↦ h x u t * h y u t) volume (-1 : ℝ) 1) (u : U) :
    ∫ t in (-1 : ℝ)..1, (finiteDiscrepancyError P h u t) ^ 2 =
      ∑ x ∈ P, ∑ y ∈ P, ∫ t in (-1 : ℝ)..1, h x u t * h y u t := by
  rw [show (fun t ↦ (finiteDiscrepancyError P h u t) ^ 2) =
      fun t ↦ ∑ x ∈ P, ∑ y ∈ P, h x u t * h y u t by
        funext t
        simp only [finiteDiscrepancyError, pow_two, Finset.sum_mul_sum]]
  rw [intervalIntegral.integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro x hx
    rw [intervalIntegral.integral_finsetSum]
    exact fun y hy ↦ hint x hx y hy u
  · intro x hx
    apply (IntervalIntegrable.sum P fun y hy ↦ hint x hx y hy u).congr
    intro t ht
    simp

/-- Abstract finite-sum Stolarsky algebra: once the integrated two-point kernel is
`1 / 3 - d(x,y) / 4`, the squared discrepancy has the claimed energy form. -/
theorem finite_stolarsky_of_pair_kernel
    [MeasurableSpace U]
    (P : Finset X) (h : X → U → ℝ → ℝ) (d : X → X → ℝ)
    (σ : Measure U)
    (hint : ∀ x ∈ P, ∀ y ∈ P, ∀ u,
      IntervalIntegrable (fun t ↦ h x u t * h y u t) volume (-1 : ℝ) 1)
    (hpair : ∀ x ∈ P, ∀ y ∈ P,
      Integrable (fun u ↦ ∫ t in (-1 : ℝ)..1, h x u t * h y u t) σ)
    (hkernel : ∀ x ∈ P, ∀ y ∈ P,
      ∫ u, (∫ t in (-1 : ℝ)..1, h x u t * h y u t) ∂σ = 1 / 3 - d x y / 4) :
    ∫ u, (∫ t in (-1 : ℝ)..1, (finiteDiscrepancyError P h u t) ^ 2) ∂σ =
      ((P.card : ℝ) ^ 2) / 3 - (1 / 4) * ∑ x ∈ P, ∑ y ∈ P, d x y := by
  simp_rw [intervalIntegral_finiteDiscrepancyError_sq P h hint]
  have hinner (x : X) (hx : x ∈ P) :
      ∫ u, (∑ y ∈ P, ∫ t in (-1 : ℝ)..1, h x u t * h y u t) ∂σ =
        ∑ y ∈ P, ∫ u, (∫ t in (-1 : ℝ)..1, h x u t * h y u t) ∂σ := by
    rw [MeasureTheory.integral_finsetSum P]
    exact fun y hy ↦ hpair x hx y hy
  rw [MeasureTheory.integral_finsetSum P]
  · calc
      ∑ x ∈ P, ∫ u, (∑ y ∈ P, ∫ t in (-1 : ℝ)..1, h x u t * h y u t) ∂σ =
          ∑ x ∈ P, ∑ y ∈ P,
            ∫ u, (∫ t in (-1 : ℝ)..1, h x u t * h y u t) ∂σ := by
        apply Finset.sum_congr rfl
        intro x hx
        exact hinner x hx
      _ = ((P.card : ℝ) ^ 2) / 3 - (1 / 4) * ∑ x ∈ P, ∑ y ∈ P, d x y := by
        rw [show (∑ x ∈ P, ∑ y ∈ P,
            ∫ u, (∫ t in (-1 : ℝ)..1, h x u t * h y u t) ∂σ) =
            ∑ x ∈ P, ∑ y ∈ P, (1 / 3 - d x y / 4) by
          apply Finset.sum_congr rfl
          intro x hx
          apply Finset.sum_congr rfl
          intro y hy
          exact hkernel x hx y hy]
        simp only [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul]
        have hddiv :
            (∑ x ∈ P, ∑ y ∈ P, d x y) / (4 : ℝ) =
              ∑ x ∈ P, ∑ y ∈ P, d x y / (4 : ℝ) := by
          simp only [Finset.sum_div]
        rw [← hddiv]
        ring_nf
  · intro x hx
    exact integrable_finsetSum P fun y hy ↦ hpair x hx y hy

/-- A directly reusable form of the Stolarsky algebra whose geometric hypotheses are
the two spherical moments. The hypotheses say that every coordinate is in `[-1,1]`,
has second moment `1/3`, and that the mean absolute difference of two coordinates is
half their chordal distance. -/
theorem finite_stolarsky_of_coordinate_moments
    [MeasurableSpace U] (P : Finset X) (coord : X → U → ℝ) (d : X → X → ℝ)
    (σ : Measure U) [IsProbabilityMeasure σ]
    (hcoord : ∀ x ∈ P, ∀ u, coord x u ∈ Set.Icc (-1 : ℝ) 1)
    (hsqInt : ∀ x ∈ P, Integrable (fun u ↦ (coord x u) ^ 2) σ)
    (habsInt : ∀ x ∈ P, ∀ y ∈ P,
      Integrable (fun u ↦ |coord x u - coord y u|) σ)
    (hsq : ∀ x ∈ P, ∫ u, (coord x u) ^ 2 ∂σ = 1 / 3)
    (habs : ∀ x ∈ P, ∀ y ∈ P,
      ∫ u, |coord x u - coord y u| ∂σ = d x y / 2) :
    ∫ u, (∫ t in (-1 : ℝ)..1,
      (finiteDiscrepancyError P
        (fun x u t ↦ centeredLowerIndicator (coord x u) t) u t) ^ 2) ∂σ =
      ((P.card : ℝ) ^ 2) / 3 - (1 / 4) * ∑ x ∈ P, ∑ y ∈ P, d x y := by
  apply finite_stolarsky_of_pair_kernel P
    (fun x u t ↦ centeredLowerIndicator (coord x u) t) d σ
  · intro x hx y hy u
    exact intervalIntegrable_centeredLowerIndicator_mul
      (hcoord x hx u) (hcoord y hy u)
  · intro x hx y hy
    have hrhs : Integrable (fun u ↦
        1 / 6 + ((coord x u) ^ 2 + (coord y u) ^ 2) / 4 -
          |coord x u - coord y u| / 2) σ := by
      exact ((integrable_const (1 / 6 : ℝ)).add
        ((hsqInt x hx).add (hsqInt y hy) |>.div_const 4)).sub
          ((habsInt x hx y hy).div_const 2)
    apply hrhs.congr
    filter_upwards with u
    exact (intervalIntegral_centeredLowerIndicator_mul
      (hcoord x hx u) (hcoord y hy u)).symm
  · intro x hx y hy
    have hpointwise : (fun u ↦
        ∫ t in (-1 : ℝ)..1,
          centeredLowerIndicator (coord x u) t * centeredLowerIndicator (coord y u) t) =
        fun u ↦ 1 / 6 + ((coord x u) ^ 2 + (coord y u) ^ 2) / 4 -
          |coord x u - coord y u| / 2 := by
      funext u
      exact intervalIntegral_centeredLowerIndicator_mul
        (hcoord x hx u) (hcoord y hy u)
    rw [hpointwise]
    have hc : Integrable (fun _ : U ↦ (1 / 6 : ℝ)) σ := integrable_const (1 / 6 : ℝ)
    have hsumsq : Integrable (fun u ↦ (coord x u) ^ 2 + (coord y u) ^ 2) σ :=
      (hsqInt x hx).add (hsqInt y hy)
    have hsumsqDiv : Integrable
        (fun u ↦ ((coord x u) ^ 2 + (coord y u) ^ 2) / 4) σ :=
      hsumsq.div_const 4
    have habsDiv : Integrable (fun u ↦ |coord x u - coord y u| / 2) σ :=
      (habsInt x hx y hy).div_const 2
    have hleft : Integrable (fun u ↦
        1 / 6 + ((coord x u) ^ 2 + (coord y u) ^ 2) / 4) σ := by
      exact hc.add hsumsqDiv
    rw [MeasureTheory.integral_sub hleft habsDiv,
      MeasureTheory.integral_add hc hsumsqDiv,
      MeasureTheory.integral_div, MeasureTheory.integral_div,
      MeasureTheory.integral_add (hsqInt x hx) (hsqInt y hy),
      MeasureTheory.integral_div]
    simp only [MeasureTheory.integral_const, probReal_univ,
      hsq x hx, hsq y hy, habs x hx y hy]
    ring

/-! ## Finite even-moment arithmetic -/

/-- A squared Wallis-type lower bound for the central binomial coefficient. -/
theorem centralBinom_sq_lower_succ (k : ℕ) :
    (16 : ℝ) ^ (k + 1) ≤
      4 * (k + 1 : ℝ) * (Nat.centralBinom (k + 1) : ℝ) ^ 2 := by
  induction k with
  | zero => norm_num [Nat.centralBinom, Nat.choose]
  | succ k ih =>
      let n : ℕ := k + 1
      have hnR : (0 : ℝ) < n := by positivity
      have hrecNat := Nat.succ_mul_centralBinom_succ n
      have hrec :
          (n + 1 : ℝ) * (Nat.centralBinom (n + 1) : ℝ) =
            2 * (2 * (n : ℝ) + 1) * (Nat.centralBinom n : ℝ) := by
        exact_mod_cast hrecNat
      have hrec_sq :
          (n + 1 : ℝ) ^ 2 * (Nat.centralBinom (n + 1) : ℝ) ^ 2 =
            4 * (2 * (n : ℝ) + 1) ^ 2 * (Nat.centralBinom n : ℝ) ^ 2 := by
        calc
          (n + 1 : ℝ) ^ 2 * (Nat.centralBinom (n + 1) : ℝ) ^ 2 =
              ((n + 1 : ℝ) * (Nat.centralBinom (n + 1) : ℝ)) ^ 2 := by ring
          _ = (2 * (2 * (n : ℝ) + 1) * (Nat.centralBinom n : ℝ)) ^ 2 := by
            rw [hrec]
          _ = 4 * (2 * (n : ℝ) + 1) ^ 2 *
              (Nat.centralBinom n : ℝ) ^ 2 := by ring
      have hpoly : 4 * (n : ℝ) * (n + 1) ≤ (2 * (n : ℝ) + 1) ^ 2 := by
        nlinarith [sq_nonneg (1 : ℝ)]
      have hsquare : 0 < (n + 1 : ℝ) ^ 2 := by positivity
      apply le_of_mul_le_mul_right
      · calc
          (16 : ℝ) ^ (n + 1) * (n + 1 : ℝ) ^ 2 =
              16 * (16 : ℝ) ^ n * (n + 1 : ℝ) ^ 2 := by
            rw [pow_succ']
          _ ≤ 16 * (4 * (n : ℝ) * (Nat.centralBinom n : ℝ) ^ 2) *
              (n + 1 : ℝ) ^ 2 := by
            gcongr
            simpa [n] using ih
          _ = 16 * (n + 1 : ℝ) *
              (4 * (n : ℝ) * (n + 1)) * (Nat.centralBinom n : ℝ) ^ 2 := by ring
          _ ≤ 16 * (n + 1 : ℝ) * (2 * (n : ℝ) + 1) ^ 2 *
              (Nat.centralBinom n : ℝ) ^ 2 := by gcongr
          _ = 4 * (n + 1 : ℝ) *
              ((n + 1 : ℝ) ^ 2 * (Nat.centralBinom (n + 1) : ℝ) ^ 2) := by
            rw [hrec_sq]
            ring
          _ = (4 * (n + 1 : ℝ) * (Nat.centralBinom (n + 1) : ℝ) ^ 2) *
              (n + 1 : ℝ) ^ 2 := by ring
      · exact hsquare

/-- The positive coefficient of `t^m` in `1 - √(1-t)`, for `m > 0`. -/
def sqrtDistanceCoeff (m : ℕ) : ℝ :=
  (Nat.centralBinom m : ℝ) / ((2 * (m : ℝ) - 1) * (4 : ℝ) ^ m)

/-- An elementary Wallis bound gives the required `m^{-3/2}` coefficient size. -/
theorem sqrtDistanceCoeff_lower (m : ℕ) (hm : 0 < m) :
    1 / (4 * (m : ℝ) * Real.sqrt m) ≤ sqrtDistanceCoeff m := by
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hsqrt : 0 < Real.sqrt m := Real.sqrt_pos.2 hmR
  have hcentral_nonneg : 0 ≤ (Nat.centralBinom m : ℝ) := by positivity
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hm.ne'
  have hsq := centralBinom_sq_lower_succ k
  have hsqrt_sq : (Real.sqrt (k + 1 : ℝ)) ^ 2 = (k + 1 : ℝ) := by
    simpa using Real.sq_sqrt (by positivity : (0 : ℝ) ≤ k + 1)
  have hpow_sq :
      ((4 : ℝ) ^ (k + 1)) ^ 2 ≤
        (2 * Real.sqrt (k + 1 : ℝ) * (Nat.centralBinom (k + 1) : ℝ)) ^ 2 := by
    calc
      ((4 : ℝ) ^ (k + 1)) ^ 2 = (16 : ℝ) ^ (k + 1) := by
        rw [← pow_mul, show (16 : ℝ) = 4 ^ 2 by norm_num, ← pow_mul]
        congr 1
        omega
      _ ≤ 4 * (k + 1 : ℝ) * (Nat.centralBinom (k + 1) : ℝ) ^ 2 := hsq
      _ = (2 * Real.sqrt (k + 1 : ℝ) *
          (Nat.centralBinom (k + 1) : ℝ)) ^ 2 := by
        nlinarith
  have hpow :
      (4 : ℝ) ^ (k + 1) ≤
        2 * Real.sqrt (k + 1 : ℝ) * (Nat.centralBinom (k + 1) : ℝ) := by
    exact (sq_le_sq₀ (by positivity) (by positivity)).mp hpow_sq
  have hden_left : 0 < 4 * (k + 1 : ℝ) * Real.sqrt (k + 1 : ℝ) := by positivity
  have hden_right :
      0 < (2 * (k + 1 : ℝ) - 1) * (4 : ℝ) ^ (k + 1) := by
    apply mul_pos
    · have hkR : (0 : ℝ) ≤ k := by positivity
      norm_num
      nlinarith
    · positivity
  rw [sqrtDistanceCoeff]
  simp only [Nat.cast_succ]
  rw [div_le_div_iff₀ hden_left hden_right]
  calc
    1 * ((2 * (k + 1 : ℝ) - 1) * (4 : ℝ) ^ (k + 1)) ≤
        (2 * (k + 1 : ℝ)) *
          (2 * Real.sqrt (k + 1 : ℝ) * (Nat.centralBinom (k + 1) : ℝ)) := by
      rw [one_mul]
      gcongr
      nlinarith
    _ = (Nat.centralBinom (k + 1) : ℝ) *
        (4 * (k + 1 : ℝ) * Real.sqrt (k + 1 : ℝ)) := by ring

/-- The finite even block used in the `S²` energy argument. -/
def evenBlock (n : ℕ) : Finset ℕ := Finset.Icc n (2 * n)

/-- The explicit square-root coefficients satisfy the block hypothesis. -/
theorem sqrtDistanceCoeff_evenBlock
    (n : ℕ) (hn : 0 < n) (r : ℕ) (hr : r ∈ evenBlock n) :
    1 / (32 * (n : ℝ) * Real.sqrt n) ≤ sqrtDistanceCoeff (2 * r) := by
  have hr_bounds : n ≤ r ∧ r ≤ 2 * n := by simpa [evenBlock] using hr
  have hr_pos : 0 < r := hn.trans_le hr_bounds.1
  have hm_pos : 0 < 2 * r := Nat.mul_pos (by norm_num) hr_pos
  have hcoeff := sqrtDistanceCoeff_lower (2 * r) hm_pos
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hmR : (0 : ℝ) < 2 * r := by exact_mod_cast hm_pos
  have hm_le : (2 * r : ℝ) ≤ 4 * (n : ℝ) := by
    exact_mod_cast (show 2 * r ≤ 4 * n by omega)
  have hsqrt_n_sq : (Real.sqrt n) ^ 2 = (n : ℝ) :=
    Real.sq_sqrt (le_of_lt hnR)
  have hsqrt_four_n_sq : (Real.sqrt (4 * (n : ℝ))) ^ 2 = 4 * (n : ℝ) :=
    Real.sq_sqrt (by positivity)
  have hsqrt_four_n : Real.sqrt (4 * (n : ℝ)) = 2 * Real.sqrt n := by
    have h₁ := Real.sqrt_nonneg (4 * (n : ℝ))
    have h₂ := Real.sqrt_nonneg (n : ℝ)
    nlinarith
  have hsqrt_le : Real.sqrt (2 * r : ℝ) ≤ 2 * Real.sqrt n := by
    calc
      Real.sqrt (2 * r : ℝ) ≤ Real.sqrt (4 * (n : ℝ)) :=
        Real.sqrt_le_sqrt hm_le
      _ = 2 * Real.sqrt n := hsqrt_four_n
  have hden_pos : 0 < 4 * (2 * r : ℝ) * Real.sqrt (2 * r : ℝ) := by
    positivity
  have hden_le :
      4 * (2 * r : ℝ) * Real.sqrt (2 * r : ℝ) ≤
        32 * (n : ℝ) * Real.sqrt n := by
    calc
      4 * (2 * r : ℝ) * Real.sqrt (2 * r : ℝ) ≤
          4 * (4 * (n : ℝ)) * (2 * Real.sqrt n) := by gcongr
      _ = 32 * (n : ℝ) * Real.sqrt n := by ring
  have hcoeff' :
      1 / (4 * (2 * r : ℝ) * Real.sqrt (2 * r : ℝ)) ≤
        sqrtDistanceCoeff (2 * r) := by simpa using hcoeff
  exact (one_div_le_one_div_of_le hden_pos hden_le).trans hcoeff'

/-- The arithmetic core of the finite even-moment block. -/
theorem evenBlock_sum_lower
    (n : ℕ) (hn : 0 < n) (a excess : ℕ → ℝ)
    (ha : ∀ r ∈ evenBlock n,
      1 / (32 * (n : ℝ) * Real.sqrt n) ≤ a (2 * r))
    (he : ∀ r ∈ evenBlock n,
      1 / (2 * (n : ℝ)) ≤ excess (2 * r)) :
    1 / (64 * (n : ℝ) * Real.sqrt n) ≤
      ∑ r ∈ evenBlock n, a (2 * r) * excess (2 * r) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hsqrt : 0 < Real.sqrt n := Real.sqrt_pos.2 hnR
  have hterm : ∀ r ∈ evenBlock n,
      1 / (64 * (n : ℝ) ^ 2 * Real.sqrt n) ≤
        a (2 * r) * excess (2 * r) := by
    intro r hr
    have ha' := ha r hr
    have he' := he r hr
    have ha_nonneg : 0 ≤ a (2 * r) := le_trans (by positivity) ha'
    calc
      1 / (64 * (n : ℝ) ^ 2 * Real.sqrt n) =
          (1 / (32 * (n : ℝ) * Real.sqrt n)) *
            (1 / (2 * (n : ℝ))) := by field_simp; ring
      _ ≤ a (2 * r) * excess (2 * r) :=
        mul_le_mul ha' he' (by positivity) ha_nonneg
  have hsum :
      ∑ _r ∈ evenBlock n, (1 / (64 * (n : ℝ) ^ 2 * Real.sqrt n)) ≤
        ∑ r ∈ evenBlock n, a (2 * r) * excess (2 * r) :=
    Finset.sum_le_sum hterm
  have hcard : n ≤ (evenBlock n).card := by
    simp [evenBlock]
    omega
  calc
    1 / (64 * (n : ℝ) * Real.sqrt n) =
        (n : ℝ) * (1 / (64 * (n : ℝ) ^ 2 * Real.sqrt n)) := by
      field_simp
    _ ≤ ((evenBlock n).card : ℝ) *
        (1 / (64 * (n : ℝ) ^ 2 * Real.sqrt n)) := by
      gcongr
    _ = ∑ _r ∈ evenBlock n,
        (1 / (64 * (n : ℝ) ^ 2 * Real.sqrt n)) := by simp
    _ ≤ ∑ r ∈ evenBlock n, a (2 * r) * excess (2 * r) := hsum

/-- A finite Stolarsky block lower-bounds the squared `L²` discrepancy. -/
theorem d2sq_lower_of_evenBlock
    (n : ℕ) (hn : 0 < n) (a excess : ℕ → ℝ) (d2sq : ℝ)
    (ha : ∀ r ∈ evenBlock n,
      1 / (32 * (n : ℝ) * Real.sqrt n) ≤ a (2 * r))
    (he : ∀ r ∈ evenBlock n,
      1 / (2 * (n : ℝ)) ≤ excess (2 * r))
    (hStolarsky :
      (Real.sqrt 2 / 4) *
          (∑ r ∈ evenBlock n, a (2 * r) * excess (2 * r)) ≤ d2sq) :
    Real.sqrt 2 / (256 * (n : ℝ) * Real.sqrt n) ≤ d2sq := by
  have hsqrt2 : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg _
  have hblock := evenBlock_sum_lower n hn a excess ha he
  calc
    Real.sqrt 2 / (256 * (n : ℝ) * Real.sqrt n) =
        (Real.sqrt 2 / 4) * (1 / (64 * (n : ℝ) * Real.sqrt n)) := by
      field_simp
      ring
    _ ≤ (Real.sqrt 2 / 4) *
        (∑ r ∈ evenBlock n, a (2 * r) * excess (2 * r)) := by
      gcongr
    _ ≤ d2sq := hStolarsky

/-- The exact `S²` even moment and the empirical diagonal give a `1/(2n)` excess. -/
theorem evenMomentExcess_lower
    (n : ℕ) (hn : 0 < n) (empMoment : ℕ → ℝ)
    (r : ℕ) (hr : r ∈ evenBlock n)
    (hdiag : 1 / (n : ℝ) ≤ empMoment (2 * r)) :
    1 / (2 * (n : ℝ)) ≤
      empMoment (2 * r) - 1 / (((2 * r : ℕ) : ℝ) + 1) := by
  have hr_bounds : n ≤ r ∧ r ≤ 2 * n := by simpa [evenBlock] using hr
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hrR : (n : ℝ) ≤ r := by exact_mod_cast hr_bounds.1
  have hden_n : 0 < 2 * (n : ℝ) + 1 := by positivity
  have hden_r : 0 < 2 * (r : ℝ) + 1 := by positivity
  have hfrac : 1 / (2 * (r : ℝ) + 1) ≤ 1 / (2 * (n : ℝ) + 1) := by
    apply one_div_le_one_div_of_le hden_n
    linarith
  have hbase :
      1 / (2 * (n : ℝ)) ≤ 1 / (n : ℝ) - 1 / (2 * (n : ℝ) + 1) := by
    field_simp
    nlinarith
  have hcast : ((2 * r : ℕ) : ℝ) + 1 = 2 * (r : ℝ) + 1 := by norm_num
  rw [hcast]
  linarith

/-- Interface to the analytic layer using only diagonal moments and a finite Stolarsky block. -/
theorem d2sq_lower_of_diagonal_moments
    (n : ℕ) (hn : 0 < n) (empMoment : ℕ → ℝ) (d2sq : ℝ)
    (hdiag : ∀ r ∈ evenBlock n,
      1 / (n : ℝ) ≤ empMoment (2 * r))
    (hStolarsky :
      (Real.sqrt 2 / 4) *
          (∑ r ∈ evenBlock n,
            sqrtDistanceCoeff (2 * r) *
              (empMoment (2 * r) - 1 / (((2 * r : ℕ) : ℝ) + 1))) ≤ d2sq) :
    Real.sqrt 2 / (256 * (n : ℝ) * Real.sqrt n) ≤ d2sq := by
  let excess : ℕ → ℝ := fun m => empMoment m - 1 / ((m : ℝ) + 1)
  apply d2sq_lower_of_evenBlock n hn sqrtDistanceCoeff excess d2sq
  · intro r hr
    exact sqrtDistanceCoeff_evenBlock n hn r hr
  · intro r hr
    exact evenMomentExcess_lower n hn empMoment r hr (hdiag r hr)
  · simpa [excess] using hStolarsky

/-- Fourth-power form of the cap discrepancy conclusion. -/
theorem discrepancy_fourth_power_lower
    (n : ℕ) (hn : 0 < n) (D d2sq : ℝ)
    (hd2_lower :
      Real.sqrt 2 / (256 * (n : ℝ) * Real.sqrt n) ≤ d2sq)
    (hL2_sup : d2sq ≤ 2 * (D / n) ^ 2) :
    (n : ℝ) / 131072 ≤ D ^ 4 := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hsqrt_n : 0 < Real.sqrt n := Real.sqrt_pos.2 hnR
  have hsqrt_n_sq : (Real.sqrt n) ^ 2 = (n : ℝ) := by
    simpa using Real.sq_sqrt (le_of_lt hnR)
  have hsqrt2_sq : (Real.sqrt 2) ^ 2 = (2 : ℝ) := by norm_num
  have hmain :
      Real.sqrt 2 / (256 * (n : ℝ) * Real.sqrt n) ≤
        2 * (D / n) ^ 2 := hd2_lower.trans hL2_sup
  have hDsq :
      Real.sqrt 2 * Real.sqrt n / 512 ≤ D ^ 2 := by
    field_simp at hmain ⊢
    nlinarith
  have hleft_nonneg : 0 ≤ Real.sqrt 2 * Real.sqrt n / 512 := by positivity
  have hsquared := mul_self_le_mul_self hleft_nonneg hDsq
  field_simp at hsquared ⊢
  nlinarith [hsqrt_n_sq, hsqrt2_sq]

/-- Complete finite-block wrapper, conditional only on the analytic energy inequality. -/
theorem discrepancy_fourth_power_of_diagonal_moments
    (n : ℕ) (hn : 0 < n) (D d2sq : ℝ) (empMoment : ℕ → ℝ)
    (hdiag : ∀ r ∈ evenBlock n,
      1 / (n : ℝ) ≤ empMoment (2 * r))
    (hStolarsky :
      (Real.sqrt 2 / 4) *
          (∑ r ∈ evenBlock n,
            sqrtDistanceCoeff (2 * r) *
              (empMoment (2 * r) - 1 / (((2 * r : ℕ) : ℝ) + 1))) ≤ d2sq)
    (hL2_sup : d2sq ≤ 2 * (D / n) ^ 2) :
    (n : ℝ) / 131072 ≤ D ^ 4 := by
  apply discrepancy_fourth_power_lower n hn D d2sq
  · exact d2sq_lower_of_diagonal_moments n hn empMoment d2sq hdiag hStolarsky
  · exact hL2_sup

/-! ## Finite positive-kernel (Welch) bound -/

/-- The Bloch/Hopf map from a complex unit spinor to the two-sphere. -/
def welchHopf (z w : ℂ) : E3 :=
  WithLp.toLp 2 ![
    Complex.normSq z - Complex.normSq w,
    2 * (z * conj w).re,
    2 * (z * conj w).im]

/-- The Bloch coordinates turn the normalized spherical inner product into
the squared absolute complex inner product. -/
lemma welchHopf_kernel (z w Z W : ℂ)
    (hu : Complex.normSq z + Complex.normSq w = 1)
    (hv : Complex.normSq Z + Complex.normSq W = 1) :
    (1 + inner ℝ (welchHopf z w) (welchHopf Z W)) / 2 =
      Complex.normSq (z * conj Z + w * conj W) := by
  have huv :
      (Complex.normSq z + Complex.normSq w) *
        (Complex.normSq Z + Complex.normSq W) = 1 := by
    rw [hu, hv]
    norm_num
  simp only [welchHopf, EuclideanSpace.inner_eq_star_dotProduct, dotProduct,
    Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.cons_val_succ, Matrix.vecHead, Matrix.vecTail,
    Function.comp_apply, Fin.isValue, star_trivial, Complex.normSq_apply,
    Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im,
    Complex.conj_re, Complex.conj_im]
  simp only [Complex.normSq_apply] at huv
  ring_nf at hu hv huv ⊢
  nlinarith [huv]

private lemma sphere_coord_sq (x : S2) :
    (x : E3) 0 ^ 2 + (x : E3) 1 ^ 2 + (x : E3) 2 ^ 2 = 1 := by
  have hs : ‖(x : E3)‖ ^ 2 = 1 := by rw [sphere2_norm x]; norm_num
  rw [EuclideanSpace.real_norm_sq_eq] at hs
  simpa only [Fin.sum_univ_three] using hs

/-- An explicit inverse lift for the Hopf map.  The exceptional branch is
the south pole; elsewhere this is the standard affine chart on `ℂP¹`. -/
noncomputable def welchSpinorLift (x : S2) : ℂ × ℂ :=
  if h : (x : E3) 0 = -1 then
    (0, 1)
  else
    let s := Real.sqrt (((x : E3) 0 + 1) / 2)
    ((s : ℂ), ⟨(x : E3) 1 / (2 * s), -(x : E3) 2 / (2 * s)⟩)

/-- The explicit lift is unit and has the prescribed Bloch coordinates. -/
lemma welchSpinorLift_spec (x : S2) :
    Complex.normSq (welchSpinorLift x).1 +
        Complex.normSq (welchSpinorLift x).2 = 1 ∧
      welchHopf (welchSpinorLift x).1 (welchSpinorLift x).2 = (x : E3) := by
  have hcoord := sphere_coord_sq x
  by_cases ha : (x : E3) 0 = -1
  · have hb : (x : E3) 1 = 0 := by
      nlinarith [sq_nonneg ((x : E3) 2)]
    have hc : (x : E3) 2 = 0 := by
      nlinarith [sq_nonneg ((x : E3) 1)]
    constructor
    · simp [welchSpinorLift, ha, Complex.normSq]
    · ext j
      fin_cases j <;>
        simp [welchSpinorLift, ha, welchHopf, Matrix.cons_val_zero,
          Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_succ,
          Matrix.vecHead, Matrix.vecTail, Function.comp_apply, hb, hc,
          Complex.normSq]
  · have ha_sq : (x : E3) 0 ^ 2 ≤ 1 := by
      nlinarith [sq_nonneg ((x : E3) 1), sq_nonneg ((x : E3) 2)]
    have ha_ge : -1 ≤ (x : E3) 0 := by nlinarith
    have ha_gt : -1 < (x : E3) 0 := lt_of_le_of_ne ha_ge (Ne.symm ha)
    let s := Real.sqrt (((x : E3) 0 + 1) / 2)
    have hsarg : 0 ≤ ((x : E3) 0 + 1) / 2 := by linarith
    have hspos : 0 < s := Real.sqrt_pos.2 (by dsimp [s]; linarith)
    have hsne : s ≠ 0 := ne_of_gt hspos
    have hs2 : s ^ 2 = ((x : E3) 0 + 1) / 2 := by
      dsimp [s]
      exact Real.sq_sqrt hsarg
    have hlift : welchSpinorLift x =
        ((s : ℂ), ⟨(x : E3) 1 / (2 * s), -(x : E3) 2 / (2 * s)⟩) := by
      simp [welchSpinorLift, ha, s]
    constructor
    · rw [hlift]
      simp [Complex.normSq]
      field_simp [hsne]
      nlinarith
    · rw [hlift]
      ext j
      fin_cases j <;>
        simp [welchHopf, Matrix.cons_val_zero, Matrix.cons_val_one,
          Matrix.cons_val_two, Matrix.cons_val_succ, Matrix.vecHead,
          Matrix.vecTail, Function.comp_apply, Complex.normSq_apply] <;>
        field_simp [hsne] <;> nlinarith

private def welchMonomial {I : Type*} (z w : I → ℂ)
    (k r : ℕ) (i : I) : ℂ :=
  z i ^ r * w i ^ (k - r)

private lemma spinor_add_pow {I : Type*} (z w : I → ℂ)
    (k : ℕ) (i j : I) :
    (z i * conj (z j) + w i * conj (w j)) ^ k =
      ∑ r ∈ Finset.range (k + 1),
        (k.choose r : ℂ) * welchMonomial z w k r i *
          conj (welchMonomial z w k r j) := by
  rw [add_pow]
  apply Finset.sum_congr rfl
  intro r hr
  simp only [welchMonomial, map_mul, map_pow]
  ring

private lemma sum_four_comm {I R T : Type*} [Fintype I]
    (A : Finset R) (B : Finset T) (f : I → I → R → T → ℂ) :
    (∑ i : I, ∑ j : I, ∑ r ∈ A, ∑ s ∈ B, f i j r s) =
      ∑ r ∈ A, ∑ s ∈ B, ∑ i : I, ∑ j : I, f i j r s := by
  calc
    _ = ∑ i : I, ∑ r ∈ A, ∑ j : I, ∑ s ∈ B, f i j r s := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [Finset.sum_comm]
    _ = ∑ r ∈ A, ∑ i : I, ∑ j : I, ∑ s ∈ B, f i j r s := by
      rw [Finset.sum_comm]
    _ = ∑ r ∈ A, ∑ i : I, ∑ s ∈ B, ∑ j : I, f i j r s := by
      apply Finset.sum_congr rfl
      intro r hr
      apply Finset.sum_congr rfl
      intro i hi
      rw [Finset.sum_comm]
    _ = ∑ r ∈ A, ∑ s ∈ B, ∑ i : I, ∑ j : I, f i j r s := by
      apply Finset.sum_congr rfl
      intro r hr
      rw [Finset.sum_comm]

/-- Exact finite sum-of-squares expansion underlying the complex Welch bound. -/
lemma welch_sos_identity {I : Type*} [Fintype I]
    (z w : I → ℂ) (k : ℕ) :
    ∑ i : I, ∑ j : I,
        Complex.normSq (z i * conj (z j) + w i * conj (w j)) ^ k =
      ∑ r ∈ Finset.range (k + 1), ∑ s ∈ Finset.range (k + 1),
        (k.choose r : ℝ) * (k.choose s : ℝ) *
          Complex.normSq
            (∑ i : I, welchMonomial z w k r i *
              conj (welchMonomial z w k s i)) := by
  rw [← Complex.ofReal_inj]
  push_cast
  simp_rw [Complex.normSq_eq_conj_mul_self]
  simp_rw [mul_pow, ← map_pow, spinor_add_pow]
  simp_rw [map_sum, Finset.sum_mul_sum]
  simp only [map_mul, map_natCast, map_sum, map_pow]
  rw [sum_four_comm (Finset.range (k + 1)) (Finset.range (k + 1))]
  apply Finset.sum_congr rfl
  intro r hr
  apply Finset.sum_congr rfl
  intro s hs
  rw [mul_sum]
  simp_rw [mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  rw [starRingEnd_self_apply, starRingEnd_self_apply]
  ring

/-- The finite complex Welch bound in complex dimension two. -/
theorem complex_welch_bound {I : Type*} [Fintype I]
    (z w : I → ℂ) (k : ℕ)
    (hunit : ∀ i, Complex.normSq (z i) + Complex.normSq (w i) = 1) :
    (Fintype.card I : ℝ) ^ 2 / (k + 1) ≤
      ∑ i : I, ∑ j : I,
        Complex.normSq (z i * conj (z j) + w i * conj (w j)) ^ k := by
  let T : ℕ → ℝ := fun r ↦
    (k.choose r : ℝ) *
      ∑ i : I, Complex.normSq (welchMonomial z w k r i)
  have hTsum :
      ∑ r ∈ Finset.range (k + 1), T r = (Fintype.card I : ℝ) := by
    calc
      ∑ r ∈ Finset.range (k + 1), T r =
          ∑ i : I, ∑ r ∈ Finset.range (k + 1),
            (k.choose r : ℝ) *
              (Complex.normSq (z i) ^ r *
                Complex.normSq (w i) ^ (k - r)) := by
        simp only [T, welchMonomial, Complex.normSq_mul, map_pow]
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro r hr
        rw [mul_sum]
      _ = ∑ i : I,
          (Complex.normSq (z i) + Complex.normSq (w i)) ^ k := by
        apply Finset.sum_congr rfl
        intro i hi
        rw [add_pow]
        apply Finset.sum_congr rfl
        intro r hr
        ring
      _ = (Fintype.card I : ℝ) := by simp [hunit]
  have hCS : (Fintype.card I : ℝ) ^ 2 ≤
      (k + 1 : ℝ) * ∑ r ∈ Finset.range (k + 1), T r ^ 2 := by
    have h := sq_sum_le_card_mul_sum_sq
      (s := Finset.range (k + 1)) (f := T)
    simpa [hTsum] using h
  have hdiag : (Fintype.card I : ℝ) ^ 2 / (k + 1) ≤
      ∑ r ∈ Finset.range (k + 1), T r ^ 2 := by
    apply (div_le_iff₀ (by positivity : (0 : ℝ) < k + 1)).2
    simpa [mul_comm] using hCS
  calc
    (Fintype.card I : ℝ) ^ 2 / (k + 1) ≤
        ∑ r ∈ Finset.range (k + 1), T r ^ 2 := hdiag
    _ = ∑ r ∈ Finset.range (k + 1),
        (k.choose r : ℝ) * (k.choose r : ℝ) *
          Complex.normSq
            (∑ i : I, welchMonomial z w k r i *
              conj (welchMonomial z w k r i)) := by
      apply Finset.sum_congr rfl
      intro r hr
      simp only [T]
      rw [show (∑ i : I, welchMonomial z w k r i *
            conj (welchMonomial z w k r i)) =
          ((∑ i : I, Complex.normSq (welchMonomial z w k r i) : ℝ) : ℂ) by
        simp only [Complex.mul_conj]
        norm_cast]
      rw [Complex.normSq_ofReal]
      ring
    _ ≤ ∑ r ∈ Finset.range (k + 1), ∑ s ∈ Finset.range (k + 1),
        (k.choose r : ℝ) * (k.choose s : ℝ) *
          Complex.normSq
            (∑ i : I, welchMonomial z w k r i *
              conj (welchMonomial z w k s i)) := by
      apply Finset.sum_le_sum
      intro r hr
      refine Finset.single_le_sum
        (s := Finset.range (k + 1))
        (f := fun s ↦ (k.choose r : ℝ) * (k.choose s : ℝ) *
          Complex.normSq
            (∑ i : I, welchMonomial z w k r i *
              conj (welchMonomial z w k s i))) ?_ hr
      intro s hs
      exact mul_nonneg (mul_nonneg (by positivity) (by positivity))
        (Complex.normSq_nonneg _)
    _ = ∑ i : I, ∑ j : I,
        Complex.normSq (z i * conj (z j) + w i * conj (w j)) ^ k :=
      (welch_sos_identity z w k).symm

/-- The shifted spherical moments exceed their uniform-sphere moments. -/
theorem powerSum_welch_bound (P : Finset S2) (k : ℕ) :
    (P.card : ℝ) ^ 2 / (k + 1) ≤ powerSum P k := by
  classical
  let z : P → ℂ := fun i ↦ (welchSpinorLift i.1).1
  let w : P → ℂ := fun i ↦ (welchSpinorLift i.1).2
  have hunit : ∀ i, Complex.normSq (z i) + Complex.normSq (w i) = 1 := by
    intro i
    exact (welchSpinorLift_spec i.1).1
  have hkernel : ∀ i j,
      normalizedDot i.1 j.1 =
        Complex.normSq (z i * conj (z j) + w i * conj (w j)) := by
    intro i j
    rw [normalizedDot, ← (welchSpinorLift_spec i.1).2,
      ← (welchSpinorLift_spec j.1).2]
    exact welchHopf_kernel _ _ _ _
      (welchSpinorLift_spec i.1).1 (welchSpinorLift_spec j.1).1
  have h := complex_welch_bound z w k hunit
  simp_rw [← hkernel] at h
  have hsum :
      (∑ i : P, ∑ j : P, normalizedDot i.1 j.1 ^ k) = powerSum P k := by
    rw [powerSum]
    calc
      (∑ i : P, ∑ j : P, normalizedDot i.1 j.1 ^ k) =
          ∑ x ∈ P, ∑ j : P, normalizedDot x j.1 ^ k :=
        Finset.sum_coe_sort P
          (fun x : S2 ↦ ∑ j : P, normalizedDot x j.1 ^ k)
      _ = ∑ x ∈ P, ∑ y ∈ P, normalizedDot x y ^ k := by
        apply Finset.sum_congr rfl
        intro x hx
        exact Finset.sum_coe_sort P (fun y : S2 ↦ normalizedDot x y ^ k)
  calc
    (P.card : ℝ) ^ 2 / (k + 1) ≤
        ∑ i : P, ∑ j : P, normalizedDot i.1 j.1 ^ k := by
      simpa only [Fintype.card_coe] using h
    _ = powerSum P k := hsum

/-! ## The chord-distance series and its energy lower bound -/

/-- The central-binomial coefficient divided by `4 ^ n`. -/
noncomputable def wallisCoeff (n : ℕ) : ℝ :=
  (Nat.centralBinom n : ℝ) / 4 ^ n

@[simp] lemma wallisCoeff_zero : wallisCoeff 0 = 1 := by
  simp [wallisCoeff, Nat.centralBinom_zero]

lemma wallisCoeff_pos (n : ℕ) : 0 < wallisCoeff n := by
  unfold wallisCoeff
  exact div_pos (by exact_mod_cast Nat.centralBinom_pos n) (by positivity)

lemma wallisCoeff_nonneg (n : ℕ) : 0 ≤ wallisCoeff n :=
  (wallisCoeff_pos n).le

/-- Exact Wallis recurrence. -/
lemma wallisCoeff_succ (n : ℕ) :
    wallisCoeff (n + 1) = wallisCoeff n * (2 * (n : ℝ) + 1) / (2 * (n : ℝ) + 2) := by
  have h := Nat.succ_mul_centralBinom_succ n
  have h' : ((n + 1 : ℕ) : ℝ) * (Nat.centralBinom (n + 1) : ℝ) =
      2 * (2 * (n : ℝ) + 1) * (Nat.centralBinom n : ℝ) := by
    exact_mod_cast h
  unfold wallisCoeff
  rw [pow_succ]
  field_simp
  norm_num at h' ⊢
  nlinarith

/-- The elementary squared Wallis lower bound. -/
lemma one_le_four_mul_mul_wallisCoeff_sq :
    ∀ n : ℕ, 0 < n → 1 ≤ 4 * (n : ℝ) * wallisCoeff n ^ 2 := by
  intro n hn
  induction n with
  | zero => simp at hn
  | succ n ih =>
      by_cases hn0 : n = 0
      · subst n
        norm_num [wallisCoeff, Nat.centralBinom]
      · have hnpos : 0 < n := Nat.pos_of_ne_zero hn0
        have hih := ih hnpos
        rw [wallisCoeff_succ]
        let q : ℝ := (2 * (n : ℝ) + 1) / (2 * (n : ℝ) + 2)
        have hrat : (n : ℝ) ≤ ((n : ℝ) + 1) * q ^ 2 := by
          dsimp [q]
          field_simp
          nlinarith
        have hmul := mul_le_mul_of_nonneg_left hrat
          (show 0 ≤ 4 * wallisCoeff n ^ 2 by positivity)
        calc
          1 ≤ 4 * (n : ℝ) * wallisCoeff n ^ 2 := hih
          _ ≤ 4 * ((n : ℝ) + 1) * (wallisCoeff n * q) ^ 2 := by
            nlinarith [hmul]
          _ = 4 * (((n + 1 : ℕ) : ℝ)) *
                (wallisCoeff n * (2 * (n : ℝ) + 1) /
                  (2 * (n : ℝ) + 2)) ^ 2 := by
            norm_num [q, mul_div_assoc]

lemma wallisCoeff_sq_lower {n : ℕ} (hn : 0 < n) :
    1 / (4 * (n : ℝ)) ≤ wallisCoeff n ^ 2 := by
  have h := one_le_four_mul_mul_wallisCoeff_sq n hn
  rw [div_le_iff₀ (by positivity)]
  simpa [mul_assoc, mul_comm, mul_left_comm] using h

/-- A matching elementary upper bound, used to show coefficient convergence. -/
lemma wallisCoeff_sq_upper :
    ∀ n : ℕ, ((n : ℝ) + 1) * wallisCoeff n ^ 2 ≤ 1 := by
  intro n
  induction n with
  | zero => norm_num
  | succ n ih =>
      rw [wallisCoeff_succ]
      let q : ℝ := (2 * (n : ℝ) + 1) / (2 * (n : ℝ) + 2)
      have hrat : ((n : ℝ) + 2) * q ^ 2 ≤ (n : ℝ) + 1 := by
        dsimp [q]
        field_simp
        nlinarith
      have hmul := mul_le_mul_of_nonneg_right hrat (sq_nonneg (wallisCoeff n))
      calc
        (((n + 1 : ℕ) : ℝ) + 1) *
              (wallisCoeff n * (2 * (n : ℝ) + 1) /
                (2 * (n : ℝ) + 2)) ^ 2
            = ((n : ℝ) + 2) * q ^ 2 * wallisCoeff n ^ 2 := by
                norm_num [q, mul_div_assoc]
                ring
        _ ≤ ((n : ℝ) + 1) * wallisCoeff n ^ 2 := by
              nlinarith [hmul]
        _ ≤ 1 := ih

lemma wallisCoeff_le_inv_sqrt (n : ℕ) :
    wallisCoeff n ≤ (Real.sqrt ((n : ℝ) + 1))⁻¹ := by
  have hn : 0 < (n : ℝ) + 1 := by positivity
  have hs : 0 < Real.sqrt ((n : ℝ) + 1) := Real.sqrt_pos.2 hn
  apply (sq_le_sq₀ (wallisCoeff_nonneg n) (inv_nonneg.2 hs.le)).mp
  have hu := wallisCoeff_sq_upper n
  rw [inv_pow, Real.sq_sqrt hn.le]
  rw [← one_div]
  apply (le_div_iff₀ hn).2
  simpa [mul_assoc, mul_comm, mul_left_comm] using hu

lemma wallisCoeff_tendsto_zero : Tendsto wallisCoeff atTop (nhds 0) := by
  apply squeeze_zero wallisCoeff_nonneg wallisCoeff_le_inv_sqrt
  apply tendsto_inv_atTop_zero.comp
  apply Real.tendsto_sqrt_atTop.comp
  exact tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop

lemma ringChoose_succ (a : ℝ) (k : ℕ) :
    Ring.choose a (k + 1) = Ring.choose a k * (a - k) / (k + 1) := by
  rw [Ring.choose_eq_smul, Ring.choose_eq_smul, descPochhammer_succ_right]
  simp only [Polynomial.smeval_mul, Polynomial.smeval_sub, Polynomial.smeval_X,
    Polynomial.smeval_natCast, pow_zero, nsmul_one, smul_eq_mul]
  field_simp
  simp [Nat.factorial_succ]
  ring

/-- Positive coefficient in the chord-distance expansion, indexed from zero. -/
noncomputable def chordCoeff (r : ℕ) : ℝ :=
  2 * (wallisCoeff r - wallisCoeff (r + 1))

lemma chordCoeff_eq (r : ℕ) :
    chordCoeff r = wallisCoeff r / (r + 1) := by
  rw [chordCoeff, wallisCoeff_succ]
  field_simp
  ring

lemma chordCoeff_pos (r : ℕ) : 0 < chordCoeff r := by
  rw [chordCoeff_eq]
  exact div_pos (wallisCoeff_pos r) (by positivity)

lemma chordCoeff_succ (r : ℕ) :
    chordCoeff (r + 1) = chordCoeff r * (2 * (r : ℝ) + 1) /
      (2 * (r : ℝ) + 4) := by
  rw [chordCoeff_eq, chordCoeff_eq, wallisCoeff_succ]
  field_simp
  norm_num
  ring

lemma signedRingChoose_half_succ (r : ℕ) :
    Ring.choose (1 / 2 : ℝ) (r + 1) * (-1 : ℝ) ^ (r + 1) =
      -chordCoeff r / 2 := by
  induction r with
  | zero => norm_num [chordCoeff_eq, wallisCoeff]
  | succ r ih =>
      rw [ringChoose_succ, pow_succ]
      norm_num only [Nat.cast_add, Nat.cast_one]
      rw [show
        Ring.choose (1 / 2 : ℝ) (r + 1) * (1 / 2 - (r + 1 : ℝ)) /
              ((r + 1 : ℝ) + 1) * ((-1 : ℝ) ^ (r + 1) * -1) =
            (Ring.choose (1 / 2 : ℝ) (r + 1) * (-1 : ℝ) ^ (r + 1)) *
              (-(1 / 2 - (r + 1 : ℝ)) / ((r + 1 : ℝ) + 1)) by ring]
      rw [ih, chordCoeff_succ]
      field_simp
      norm_num
      ring

lemma hasSum_chordCoeff_mul_pow_of_lt_one {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1) :
    HasSum (fun r : ℕ ↦ chordCoeff r * q ^ (r + 1))
      (2 - 2 * Real.sqrt (1 - q)) := by
  have hy : (-q : ℝ) ∈ Metric.eball (0 : ℝ) (1 : ENNReal) := by
    rw [Metric.mem_eball, edist_dist]
    simp [Real.dist_eq, abs_of_nonneg hq0, hq1]
  have hbin :=
    (Real.one_add_rpow_hasFPowerSeriesOnBall_zero (a := (1 / 2 : ℝ))).hasSum_sub hy
  have htail := (hasSum_nat_add_iff' 1).mpr hbin
  have hscaled := htail.const_smul (-2 : ℝ)
  have hfun :
      (fun r : ℕ ↦ (-2 : ℝ) •
        ((binomialSeries ℝ (1 / 2 : ℝ) (r + 1)) fun _ ↦ -q - 0)) =
        (fun r : ℕ ↦ chordCoeff r * q ^ (r + 1)) := by
    funext r
    simp only [binomialSeries_apply, sub_zero, smul_eq_mul]
    rw [List.ofFn_const, List.prod_replicate]
    rw [neg_pow]
    calc
      -2 * (Ring.choose (1 / 2 : ℝ) (r + 1) *
            ((-1 : ℝ) ^ (r + 1) * q ^ (r + 1))) =
          -2 * (Ring.choose (1 / 2 : ℝ) (r + 1) *
            (-1 : ℝ) ^ (r + 1)) * q ^ (r + 1) := by ring
      _ = chordCoeff r * q ^ (r + 1) := by
        rw [signedRingChoose_half_succ]
        ring
  have hterms : HasSum (fun r : ℕ ↦ chordCoeff r * q ^ (r + 1))
      ((-2 : ℝ) • ((1 + -q) ^ (1 / 2 : ℝ) -
        ∑ i ∈ range 1, (binomialSeries ℝ (1 / 2 : ℝ) i) fun _ ↦ -q - 0)) := by
    rw [← hfun]
    exact hscaled
  convert hterms using 1
  simp only [sum_range_one, binomialSeries_apply, sub_zero, smul_eq_mul]
  rw [List.ofFn_const, List.prod_replicate, Ring.choose_zero_right, pow_zero]
  rw [← Real.sqrt_eq_rpow]
  ring

lemma sum_Ico_chordCoeff (m M : ℕ) (h : m ≤ M) :
    ∑ r ∈ Finset.Ico m M, chordCoeff r = 2 * (wallisCoeff m - wallisCoeff M) := by
  simp_rw [chordCoeff]
  rw [← mul_sum]
  induction M, h using Nat.le_induction with
  | base => simp
  | succ M h ih =>
      rw [sum_Ico_succ_top h, mul_add, ih]
      ring

lemma hasSum_chordCoeff_nat_add (m : ℕ) :
    HasSum (fun r : ℕ ↦ chordCoeff (m + r)) (2 * wallisCoeff m) := by
  rw [hasSum_iff_tendsto_nat_of_nonneg (fun _ ↦ (chordCoeff_pos _).le)]
  have hshift : Tendsto (fun N : ℕ ↦ wallisCoeff (m + N)) atTop (nhds 0) :=
    wallisCoeff_tendsto_zero.comp (by
      simpa [Nat.add_comm] using tendsto_add_atTop_nat m)
  convert (hshift.const_mul (-2)).const_add (2 * wallisCoeff m) using 1
  · funext N
    have hs := sum_Ico_chordCoeff m (m + N) (Nat.le_add_right m N)
    rw [sum_Ico_eq_sum_range] at hs
    calc
      ∑ i ∈ range N, chordCoeff (m + i) =
          2 * (wallisCoeff m - wallisCoeff (m + N)) := by
            simpa only [Nat.add_sub_cancel_left] using hs
      _ = 2 * wallisCoeff m + -2 * wallisCoeff (m + N) := by ring
  · ring

lemma hasSum_chordCoeff_mul_pow {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q ≤ 1) :
    HasSum (fun r : ℕ ↦ chordCoeff r * q ^ (r + 1))
      (2 - 2 * Real.sqrt (1 - q)) := by
  rcases hq1.eq_or_lt with rfl | hq1
  · simpa using hasSum_chordCoeff_nat_add 0
  · exact hasSum_chordCoeff_mul_pow_of_lt_one hq0 hq1

lemma chordCoeff_div_succ_succ (r : ℕ) :
    chordCoeff r / (r + 2) =
      (2 / 3 : ℝ) *
        (wallisCoeff r / (r + 1) - wallisCoeff (r + 1) / (r + 2)) := by
  rw [chordCoeff_eq, wallisCoeff_succ]
  field_simp
  ring

lemma sum_range_chordCoeff_div (N : ℕ) :
    ∑ r ∈ range N, chordCoeff r / (r + 2) =
      (2 / 3 : ℝ) * (1 - wallisCoeff N / (N + 1)) := by
  induction N with
  | zero => norm_num
  | succ N ih =>
      rw [sum_range_succ, ih, chordCoeff_div_succ_succ]
      norm_num only [Nat.cast_add, Nat.cast_one]
      ring

lemma hasSum_chordCoeff_div :
    HasSum (fun r : ℕ ↦ chordCoeff r / (r + 2)) (2 / 3 : ℝ) := by
  rw [hasSum_iff_tendsto_nat_of_nonneg (fun r ↦
    div_nonneg (chordCoeff_pos r).le (by positivity))]
  have hquot : Tendsto (fun N : ℕ ↦ wallisCoeff N / (N + 1)) atTop (nhds 0) := by
    exact squeeze_zero
      (fun N ↦ div_nonneg (wallisCoeff_nonneg N) (by positivity))
      (fun N ↦ by
        apply (div_le_iff₀ (by positivity : (0 : ℝ) < N + 1)).2
        have hN : (1 : ℝ) ≤ N + 1 := by
          exact_mod_cast Nat.succ_le_succ (Nat.zero_le N)
        calc
          wallisCoeff N = wallisCoeff N * 1 := by ring
          _ ≤ wallisCoeff N * ((N : ℝ) + 1) :=
            mul_le_mul_of_nonneg_left hN (wallisCoeff_nonneg N))
      wallisCoeff_tendsto_zero
  convert (hquot.const_mul (-2 / 3)).const_add (2 / 3) using 1
  · funext N
    rw [sum_range_chordCoeff_div]
    ring
  · ring

lemma hasSum_chordCoeff_mul_double_powerSum {X : Type*}
    (P : Finset X) (q : X → X → ℝ)
    (hq0 : ∀ x ∈ P, ∀ y ∈ P, 0 ≤ q x y)
    (hq1 : ∀ x ∈ P, ∀ y ∈ P, q x y ≤ 1) :
    HasSum
      (fun r : ℕ ↦
        chordCoeff r * ∑ x ∈ P, ∑ y ∈ P, q x y ^ (r + 1))
      (2 * (P.card : ℝ) ^ 2 -
        ∑ x ∈ P, ∑ y ∈ P, 2 * Real.sqrt (1 - q x y)) := by
  classical
  have hpoint (x : X) (hx : x ∈ P) (y : X) (hy : y ∈ P) :
      HasSum (fun r : ℕ ↦ chordCoeff r * q x y ^ (r + 1))
        (2 - 2 * Real.sqrt (1 - q x y)) :=
    hasSum_chordCoeff_mul_pow (hq0 x hx y hy) (hq1 x hx y hy)
  have hsum : HasSum
      (fun r : ℕ ↦
        ∑ x ∈ P, ∑ y ∈ P, chordCoeff r * q x y ^ (r + 1))
      (∑ x ∈ P, ∑ y ∈ P, (2 - 2 * Real.sqrt (1 - q x y))) := by
    apply hasSum_sum
    intro x hx
    apply hasSum_sum
    intro y hy
    exact hpoint x hx y hy
  convert hsum using 1
  · funext r
    simp only [mul_sum]
  · simp only [sum_sub_distrib, sum_const, nsmul_eq_mul]
    ring

lemma hasSum_energyDeficit_series {X : Type*}
    (P : Finset X) (q : X → X → ℝ)
    (hq0 : ∀ x ∈ P, ∀ y ∈ P, 0 ≤ q x y)
    (hq1 : ∀ x ∈ P, ∀ y ∈ P, q x y ≤ 1) :
    HasSum
      (fun r : ℕ ↦ chordCoeff r *
        ((∑ x ∈ P, ∑ y ∈ P, q x y ^ (r + 1)) -
          (P.card : ℝ) ^ 2 / (r + 2)))
      ((4 / 3 : ℝ) * (P.card : ℝ) ^ 2 -
        ∑ x ∈ P, ∑ y ∈ P, 2 * Real.sqrt (1 - q x y)) := by
  have hpower := hasSum_chordCoeff_mul_double_powerSum P q hq0 hq1
  have hbase := hasSum_chordCoeff_div.const_smul ((P.card : ℝ) ^ 2)
  have hsub := hpower.sub hbase
  have hfun :
      (fun r : ℕ ↦ chordCoeff r *
        ((∑ x ∈ P, ∑ y ∈ P, q x y ^ (r + 1)) -
          (P.card : ℝ) ^ 2 / (r + 2))) =
      (fun r : ℕ ↦
        chordCoeff r * (∑ x ∈ P, ∑ y ∈ P, q x y ^ (r + 1)) -
          (P.card : ℝ) ^ 2 • (chordCoeff r / (r + 2))) := by
    funext r
    simp only [smul_eq_mul]
    ring
  have hval :
      (4 / 3 : ℝ) * (P.card : ℝ) ^ 2 -
          ∑ x ∈ P, ∑ y ∈ P, 2 * Real.sqrt (1 - q x y) =
        (2 * (P.card : ℝ) ^ 2 -
          ∑ x ∈ P, ∑ y ∈ P, 2 * Real.sqrt (1 - q x y)) -
            (P.card : ℝ) ^ 2 • (2 / 3 : ℝ) := by
    simp only [smul_eq_mul]
    ring
  rw [hfun, hval]
  exact hsub

lemma finite_energy_tail_lower (power : ℕ → ℝ) {n M : ℕ} (hn : 0 < n)
    (hM : 2 * n - 2 ≤ M) (hdiag : ∀ k, (n : ℝ) ≤ power k) :
    (n : ℝ) * (wallisCoeff (2 * n - 2) - wallisCoeff M) ≤
      ∑ r ∈ Finset.Ico (2 * n - 2) M,
        chordCoeff r * (power (r + 1) - (n : ℝ) ^ 2 / (r + 2)) := by
  let m := 2 * n - 2
  have hgap (r : ℕ) (hr : r ∈ Finset.Ico m M) :
      (n : ℝ) / 2 ≤ power (r + 1) - (n : ℝ) ^ 2 / (r + 2) := by
    have hdenNat : 2 * n ≤ r + 2 := by
      simp only [Finset.mem_Ico] at hr
      dsimp [m] at hr
      omega
    have hden : (2 : ℝ) * n ≤ (r : ℝ) + 2 := by exact_mod_cast hdenNat
    have hpos : 0 < (r : ℝ) + 2 := by positivity
    have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
    have hfrac : (n : ℝ) ^ 2 / ((r : ℝ) + 2) ≤ (n : ℝ) / 2 := by
      rw [div_le_iff₀ hpos]
      have hx : 0 ≤ (n : ℝ) * (((r : ℝ) + 2) - 2 * n) :=
        mul_nonneg hnR.le (sub_nonneg.2 hden)
      nlinarith
    have hd := hdiag (r + 1)
    linarith
  calc
    (n : ℝ) * (wallisCoeff m - wallisCoeff M) =
        ∑ r ∈ Finset.Ico m M, chordCoeff r * ((n : ℝ) / 2) := by
          rw [← sum_mul, sum_Ico_chordCoeff m M hM]
          ring
    _ ≤ ∑ r ∈ Finset.Ico m M,
          chordCoeff r * (power (r + 1) - (n : ℝ) ^ 2 / (r + 2)) := by
      exact sum_le_sum fun r hr ↦
        mul_le_mul_of_nonneg_left (hgap r hr) (chordCoeff_pos r).le

lemma energy_lower_of_finite_tails {energy : ℝ} {n : ℕ} (hn : 0 < n)
    (henergy : ∀ M, 2 * n - 2 ≤ M →
      (n : ℝ) * (wallisCoeff (2 * n - 2) - wallisCoeff M) ≤ energy) :
    (n : ℝ) * wallisCoeff (2 * n - 2) ≤ energy := by
  have hlim : Tendsto
      (fun M : ℕ ↦ (n : ℝ) *
        (wallisCoeff (2 * n - 2) - wallisCoeff M)) atTop
      (nhds ((n : ℝ) * wallisCoeff (2 * n - 2))) := by
    convert (wallisCoeff_tendsto_zero.const_sub
      (wallisCoeff (2 * n - 2))).const_mul (n : ℝ) using 1 <;> ring
  apply le_of_tendsto hlim
  filter_upwards [eventually_ge_atTop (2 * n - 2)] with M hM
  exact henergy M hM

lemma dist_eq_two_mul_sqrt_one_sub_normalizedDot (x y : S2) :
    dist x y = 2 * Real.sqrt (1 - normalizedDot x y) := by
  have hq : 0 ≤ 1 - normalizedDot x y := sub_nonneg.mpr (normalizedDot_le_one x y)
  have hsqrt := Real.sq_sqrt hq
  have hdist := sphere2_dist_sq x y
  have hsq : dist x y ^ 2 = 4 * (1 - normalizedDot x y) := by
    rw [hdist]
    unfold normalizedDot
    ring
  have hd0 : 0 ≤ dist x y := dist_nonneg
  have hr0 : 0 ≤ Real.sqrt (1 - normalizedDot x y) := Real.sqrt_nonneg _
  nlinarith

lemma hasSum_energyDeficit (P : Finset S2) :
    HasSum
      (fun r : ℕ ↦ chordCoeff r *
        (powerSum P (r + 1) - (P.card : ℝ) ^ 2 / (r + 2)))
      (energyDeficit P) := by
  have h := hasSum_energyDeficit_series P normalizedDot
    (fun x _ y _ ↦ normalizedDot_nonneg x y)
    (fun x _ y _ ↦ normalizedDot_le_one x y)
  simpa only [powerSum, energyDeficit,
    dist_eq_two_mul_sqrt_one_sub_normalizedDot] using h

/-- The exact energy deficit is at least the first elementary Wallis tail. -/
theorem energyDeficit_lower (P : Finset S2) (hn : 0 < P.card) :
    (P.card : ℝ) * wallisCoeff (2 * P.card - 2) ≤ energyDeficit P := by
  apply energy_lower_of_finite_tails hn
  intro M hM
  calc
    (P.card : ℝ) *
        (wallisCoeff (2 * P.card - 2) - wallisCoeff M) ≤
        ∑ r ∈ Finset.Ico (2 * P.card - 2) M,
          chordCoeff r *
            (powerSum P (r + 1) - (P.card : ℝ) ^ 2 / (r + 2)) :=
      finite_energy_tail_lower (powerSum P) hn hM (card_le_powerSum P)
    _ ≤ energyDeficit P := by
      calc
        _ ≤ ∑' r : ℕ, chordCoeff r *
              (powerSum P (r + 1) - (P.card : ℝ) ^ 2 / (r + 2)) := by
          apply (hasSum_energyDeficit P).summable.sum_le_tsum
          intro r hr
          apply mul_nonneg (chordCoeff_pos r).le
          apply sub_nonneg.mpr
          have hw := powerSum_welch_bound P (r + 1)
          have hden : (((r + 1 : ℕ) : ℝ) + 1) = (r : ℝ) + 2 := by
            push_cast
            ring
          rw [hden] at hw
          exact hw
        _ = energyDeficit P := (hasSum_energyDeficit P).tsum_eq

/-! ## Stolarsky's identity and the discrepancy bound -/

lemma analyticCapError_intervalIntegrable_sq (P : Finset S2) (u : S2) :
    IntervalIntegrable (fun t : ℝ ↦ analyticCapError P u t ^ 2)
      volume (-1 : ℝ) 1 := by
  classical
  rw [show (fun t : ℝ ↦ analyticCapError P u t ^ 2) =
      fun t ↦ ∑ x ∈ P, ∑ y ∈ P, pointCapTerm x u t * pointCapTerm y u t by
        funext t
        simp only [analyticCapError, pow_two, Finset.sum_mul_sum]]
  have hs := IntervalIntegrable.sum P fun x hx ↦
    IntervalIntegrable.sum P fun y hy ↦
      intervalIntegrable_centeredLowerIndicator_mul (inner_mem_Icc x u)
        (inner_mem_Icc y u)
  apply hs.congr
  intro t ht
  simp only [pointCapTerm, Finset.sum_apply]

lemma analyticCapError_sq_le_discrepancy_sq (P : Finset S2) (u : S2) {t : ℝ}
    (ht : t ∈ Set.Icc (-1 : ℝ) 1) :
    analyticCapError P u t ^ 2 ≤ sphericalCapDiscrepancy P ^ 2 := by
  have habs : |analyticCapError P u t| ≤ sphericalCapDiscrepancy P := by
    rw [analyticCapError_eq_signedCapError]
    exact capError_le_discrepancy P u ht
  have hD := sphericalCapDiscrepancy_nonneg P
  have hs := (sq_le_sq₀ (abs_nonneg (analyticCapError P u t)) hD).2 habs
  simpa only [sq_abs] using hs

lemma intervalIntegral_analyticCapError_sq_le (P : Finset S2) (u : S2) :
    (∫ t in (-1 : ℝ)..1, analyticCapError P u t ^ 2) ≤
      2 * sphericalCapDiscrepancy P ^ 2 := by
  calc
    (∫ t in (-1 : ℝ)..1, analyticCapError P u t ^ 2) ≤
        ∫ _t in (-1 : ℝ)..1, sphericalCapDiscrepancy P ^ 2 := by
      apply intervalIntegral.integral_mono_on (by norm_num)
        (analyticCapError_intervalIntegrable_sq P u)
        ((continuous_const : Continuous (fun _ : ℝ ↦
          sphericalCapDiscrepancy P ^ 2)).intervalIntegrable _ _)
      intro t ht
      exact analyticCapError_sq_le_discrepancy_sq P u ht
    _ = 2 * sphericalCapDiscrepancy P ^ 2 := by
      rw [intervalIntegral.integral_const]
      norm_num

/-- Stolarsky's invariance identity for the raw spherical-cap counting error. -/
theorem finite_stolarsky (P : Finset S2) :
    (∫ u : S2, (∫ t in (-1 : ℝ)..1, analyticCapError P u t ^ 2)
        ∂(surfaceProbability : Measure S2)) = energyDeficit P / 4 := by
  have h := finite_stolarsky_of_coordinate_moments P
    (fun (x u : S2) ↦ inner ℝ (x : E3) (u : E3)) (fun x y ↦ dist x y)
    (surfaceProbability : Measure S2)
    (fun x _ u ↦ inner_mem_Icc x u)
    (fun x _ ↦ by
      have hc : Continuous (fun u : S2 ↦ inner ℝ (x : E3) (u : E3) ^ 2) :=
        (Continuous.inner continuous_const continuous_subtype_val).pow 2
      simpa only [integrableOn_univ] using
        hc.continuousOn.integrableOn_compact isCompact_univ)
    (fun x _ y _ ↦ by
      have hc : Continuous (fun u : S2 ↦
          |inner ℝ (x : E3) (u : E3) - inner ℝ (y : E3) (u : E3)|) :=
        ((Continuous.inner continuous_const continuous_subtype_val).sub
          (Continuous.inner continuous_const continuous_subtype_val)).abs
      simpa only [integrableOn_univ] using
        hc.continuousOn.integrableOn_compact isCompact_univ)
    (fun x _ ↦ unitInnerSquare_integral (x : E3) (sphere2_norm x))
    (fun x _ y _ ↦ innerDifferenceAbs_integral x y)
  calc
    _ = ((P.card : ℝ) ^ 2) / 3 -
        (1 / 4) * ∑ x ∈ P, ∑ y ∈ P, dist x y := by
      simpa only [finiteDiscrepancyError, pointCapTerm, analyticCapError] using h
    _ = energyDeficit P / 4 := by unfold energyDeficit; ring

lemma integrable_intervalIntegral_analyticCapError_sq (P : Finset S2) :
    Integrable (fun u : S2 ↦
      ∫ t in (-1 : ℝ)..1, analyticCapError P u t ^ 2)
      (surfaceProbability : Measure S2) := by
  classical
  have hpointwise : (fun u : S2 ↦
      ∫ t in (-1 : ℝ)..1, analyticCapError P u t ^ 2) =
      fun u : S2 ↦ ∑ x ∈ P, ∑ y ∈ P,
        (1 / 6 +
          ((inner ℝ (x : E3) (u : E3)) ^ 2 +
            (inner ℝ (y : E3) (u : E3)) ^ 2) / 4 -
          |inner ℝ (x : E3) (u : E3) - inner ℝ (y : E3) (u : E3)| / 2) := by
    funext u
    rw [show analyticCapError P u =
        finiteDiscrepancyError P pointCapTerm u by rfl]
    rw [intervalIntegral_finiteDiscrepancyError_sq P pointCapTerm]
    · apply Finset.sum_congr rfl
      intro x hx
      apply Finset.sum_congr rfl
      intro y hy
      exact intervalIntegral_centeredLowerIndicator_mul (inner_mem_Icc x u)
        (inner_mem_Icc y u)
    · intro x hx y hy v
      exact intervalIntegrable_centeredLowerIndicator_mul (inner_mem_Icc x v)
        (inner_mem_Icc y v)
  rw [hpointwise]
  have hsq (z : S2) : Integrable
      (fun u : S2 ↦ inner ℝ (z : E3) (u : E3) ^ 2)
      (surfaceProbability : Measure S2) := by
    have hc : Continuous (fun u : S2 ↦ inner ℝ (z : E3) (u : E3) ^ 2) :=
      (Continuous.inner continuous_const continuous_subtype_val).pow 2
    simpa only [integrableOn_univ] using
      hc.continuousOn.integrableOn_compact isCompact_univ
  have habs (z w : S2) : Integrable
      (fun u : S2 ↦
        |inner ℝ (z : E3) (u : E3) - inner ℝ (w : E3) (u : E3)|)
      (surfaceProbability : Measure S2) := by
    have hc : Continuous (fun u : S2 ↦
        |inner ℝ (z : E3) (u : E3) - inner ℝ (w : E3) (u : E3)|) :=
      ((Continuous.inner continuous_const continuous_subtype_val).sub
        (Continuous.inner continuous_const continuous_subtype_val)).abs
    simpa only [integrableOn_univ] using
      hc.continuousOn.integrableOn_compact isCompact_univ
  apply integrable_finsetSum P
  intro x hx
  apply integrable_finsetSum P
  intro y hy
  exact ((integrable_const (1 / 6 : ℝ)).add
    ((hsq x).add (hsq y) |>.div_const 4)).sub ((habs x y).div_const 2)

/-- The spherical distance-energy deficit is controlled by the squared cap discrepancy. -/
theorem energyDeficit_le_eight_mul_discrepancy_sq (P : Finset S2) :
    energyDeficit P ≤ 8 * sphericalCapDiscrepancy P ^ 2 := by
  have hconst : Integrable
      (fun _ : S2 ↦ 2 * sphericalCapDiscrepancy P ^ 2)
      (surfaceProbability : Measure S2) := integrable_const _
  have hle : (∫ u : S2, (∫ t in (-1 : ℝ)..1, analyticCapError P u t ^ 2)
      ∂(surfaceProbability : Measure S2)) ≤
      ∫ _u : S2, 2 * sphericalCapDiscrepancy P ^ 2
        ∂(surfaceProbability : Measure S2) := by
    apply MeasureTheory.integral_mono
      (integrable_intervalIntegral_analyticCapError_sq P) hconst
    intro u
    exact intervalIntegral_analyticCapError_sq_le P u
  rw [finite_stolarsky, MeasureTheory.integral_const, probReal_univ] at hle
  simp only [one_smul] at hle
  nlinarith

lemma energyDeficit_nonneg (P : Finset S2) : 0 ≤ energyDeficit P := by
  by_cases hn : P.card = 0
  · have hP : P = ∅ := Finset.card_eq_zero.mp hn
    subst P
    simp [energyDeficit]
  · have hnpos : 0 < P.card := Nat.pos_of_ne_zero hn
    exact (mul_nonneg (by positivity) (wallisCoeff_nonneg _)).trans
      (energyDeficit_lower P hnpos)

lemma card_div_eight_le_energyDeficit_sq (P : Finset S2) :
    (P.card : ℝ) / 8 ≤ energyDeficit P ^ 2 := by
  by_cases hn : P.card = 0
  · rw [hn]
    norm_num only [Nat.cast_zero, zero_div]
    exact sq_nonneg _
  have hnpos : 0 < P.card := Nat.pos_of_ne_zero hn
  have henergy := energyDeficit_lower P hnpos
  by_cases hone : P.card = 1
  · rw [hone] at henergy ⊢
    norm_num at henergy ⊢
    nlinarith
  have hn2 : 2 ≤ P.card := by omega
  let m := 2 * P.card - 2
  have hmpos : 0 < m := by dsimp [m]; omega
  have hmRpos : (0 : ℝ) < m := by exact_mod_cast hmpos
  have hnRpos : (0 : ℝ) < P.card := by exact_mod_cast hnpos
  have hmle : (m : ℝ) ≤ 2 * (P.card : ℝ) := by
    dsimp [m]
    exact_mod_cast Nat.sub_le (2 * P.card) 2
  have hfrac : 1 / (8 * (P.card : ℝ)) ≤ 1 / (4 * (m : ℝ)) := by
    apply (div_le_div_iff₀ (by positivity : (0 : ℝ) < 8 * P.card)
      (by positivity : (0 : ℝ) < 4 * m)).2
    nlinarith
  have hwallis : 1 / (8 * (P.card : ℝ)) ≤ wallisCoeff m ^ 2 :=
    hfrac.trans (wallisCoeff_sq_lower hmpos)
  have hmul := mul_le_mul_of_nonneg_left hwallis
    (sq_nonneg (P.card : ℝ))
  have hlower : (P.card : ℝ) / 8 ≤
      ((P.card : ℝ) * wallisCoeff m) ^ 2 := by
    calc
      (P.card : ℝ) / 8 = (P.card : ℝ) ^ 2 *
          (1 / (8 * (P.card : ℝ))) := by field_simp
      _ ≤ (P.card : ℝ) ^ 2 * wallisCoeff m ^ 2 := hmul
      _ = ((P.card : ℝ) * wallisCoeff m) ^ 2 := by ring
  have henergy' : (P.card : ℝ) * wallisCoeff m ≤ energyDeficit P := by
    simpa only [m] using henergy
  have hsquare := (sq_le_sq₀
    (mul_nonneg (by positivity) (wallisCoeff_nonneg m))
    (energyDeficit_nonneg P)).2 henergy'
  exact hlower.trans hsquare

/-- Quantitative form of Erdős Problem 988: every finite configuration satisfies
`|P| ≤ 512 D(P)^4`. In particular the optimal cap discrepancy is unbounded. -/
theorem card_le_512_mul_discrepancy_pow_four (P : Finset S2) :
    (P.card : ℝ) ≤ 512 * sphericalCapDiscrepancy P ^ 4 := by
  have hlower := card_div_eight_le_energyDeficit_sq P
  have hupper := energyDeficit_le_eight_mul_discrepancy_sq P
  have hsquare := (sq_le_sq₀ (energyDeficit_nonneg P)
    (mul_nonneg (by norm_num) (sq_nonneg (sphericalCapDiscrepancy P)))).2 hupper
  calc
    (P.card : ℝ) = 8 * ((P.card : ℝ) / 8) := by ring
    _ ≤ 8 * energyDeficit P ^ 2 := by gcongr
    _ ≤ 8 * (8 * sphericalCapDiscrepancy P ^ 2) ^ 2 := by gcongr
    _ = 512 * sphericalCapDiscrepancy P ^ 4 := by ring

/-- **Erdős Problem 988.** The least spherical-cap discrepancy among `n`-point
subsets of the unit two-sphere tends to infinity with `n`. -/
theorem erdos_988 : Tendsto minimumDiscrepancy atTop atTop :=
  minimumDiscrepancy_tendsto_of_card_le_512_mul_pow_four
    card_le_512_mul_discrepancy_pow_four


end

end Erdos988

#print axioms Erdos988.erdos_988
