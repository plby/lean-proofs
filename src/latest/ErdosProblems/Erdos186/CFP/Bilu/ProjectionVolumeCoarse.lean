/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
import ErdosProblems.Erdos186.CFP.Bilu.VolumeSections

/-!
# A coarse convex projection-volume estimate

This file proves the dimension-only substitute for Bilu's Lemma 6.6
which is enough when the ambient dimension is bounded.  In orthogonal
product coordinates, if a convex set contains a centered vertical
segment of radius `h`, then every fibre over half of its first-coordinate
projection contains an interval of length `h`.  Fubini therefore bounds
the projection volume by the ambient volume.

Unlike a statement of the Rogers--Shephard inequality, the result below
is proved directly from convexity and product measure.
-/

namespace Erdos186.CFP.Bilu.ProjectionVolumeCoarse

open scoped ENNReal Pointwise
open MeasureTheory Set

variable {d : ℕ}

abbrev Base (d : ℕ) := EuclideanSpace ℝ (Fin d)

/-- The fibre of a subset of `Base d × ℝ` over a base point. -/
def verticalSection (B : Set (Base d × ℝ)) (y : Base d) : Set ℝ :=
  {t | (y, t) ∈ B}

/-- The first-coordinate projection. -/
def baseProjection (B : Set (Base d × ℝ)) : Set (Base d) :=
  Prod.fst '' B

/-- The half-scaled first-coordinate projection. -/
def halfBaseProjection (B : Set (Base d × ℝ)) : Set (Base d) :=
  (2 : ℝ)⁻¹ • baseProjection B

/-- A lower bound for every fibre above a measurable base set integrates
to a product-volume lower bound. -/
theorem volume_mul_measure_le_prod_of_fiber_lower_bound
    {B : Set (Base d × ℝ)} {D : Set (Base d)} {h : ℝ}
    (hB : MeasurableSet B) (hD : MeasurableSet D)
    (hfiber : ∀ y ∈ D, ENNReal.ofReal h ≤ volume (verticalSection B y)) :
    ENNReal.ofReal h * volume D ≤ (volume.prod volume) B := by
  rw [Measure.prod_apply hB]
  calc
    ENNReal.ofReal h * volume D = ∫⁻ _y in D, ENNReal.ofReal h := by
      simp
    _ ≤ ∫⁻ y in D, volume (verticalSection B y) := by
      apply setLIntegral_mono' hD
      intro y hy
      exact hfiber y hy
    _ ≤ ∫⁻ y, volume (verticalSection B y) :=
      setLIntegral_le_lintegral _ _

/-- Midpoint convexity supplies an interval of length `h` in every fibre
over the half-scaled projection. -/
theorem fiber_halfBaseProjection_lower_bound
    {B : Set (Base d × ℝ)} {h : ℝ}
    (hh : 0 ≤ h) (hconv : Convex ℝ B)
    (hsegment : ∀ t ∈ Set.Icc (-h) h, ((0 : Base d), t) ∈ B) :
    ∀ y ∈ halfBaseProjection B,
      ENNReal.ofReal h ≤ volume (verticalSection B y) := by
  intro y hy
  rcases hy with ⟨z, hz, rfl⟩
  rcases hz with ⟨p, hpB, hpz⟩
  let s : ℝ := p.2
  have hp : p = (z, s) := by
    apply Prod.ext
    · exact hpz
    · exact rfl
  rw [hp] at hpB
  have hinterval : Set.Icc ((s - h) / 2) ((s + h) / 2) ⊆
      verticalSection B ((2 : ℝ)⁻¹ • z) := by
    intro t ht
    let q : ℝ := 2 * t - s
    have hq : q ∈ Set.Icc (-h) h := by
      constructor <;> dsimp only [q] <;> linarith [ht.1, ht.2]
    have hm := hconv hpB (hsegment q hq)
      (show 0 ≤ (2 : ℝ)⁻¹ by positivity)
      (show 0 ≤ (2 : ℝ)⁻¹ by positivity)
      (show (2 : ℝ)⁻¹ + (2 : ℝ)⁻¹ = 1 by norm_num)
    have htq : (2 : ℝ)⁻¹ * s + (2 : ℝ)⁻¹ * q = t := by
      dsimp only [q]
      ring
    change (((2 : ℝ)⁻¹ • z), t) ∈ B
    simpa [Prod.smul_mk, htq] using hm
  calc
    ENNReal.ofReal h = volume (Set.Icc ((s - h) / 2) ((s + h) / 2)) := by
      rw [Real.volume_Icc]
      congr 1
      ring_nf
    _ ≤ volume (verticalSection B ((2 : ℝ)⁻¹ • z)) :=
      measure_mono hinterval

/-- Coarse projection estimate in product coordinates. -/
theorem half_projection_volume_le_prod_volume
    {B : Set (Base d × ℝ)} {h : ℝ}
    (hh : 0 ≤ h) (hB : MeasurableSet B)
    (hhalf : MeasurableSet (halfBaseProjection B))
    (hconv : Convex ℝ B)
    (hsegment : ∀ t ∈ Set.Icc (-h) h, ((0 : Base d), t) ∈ B) :
    ENNReal.ofReal h * volume (halfBaseProjection B) ≤
      (volume.prod volume) B := by
  exact volume_mul_measure_le_prod_of_fiber_lower_bound hB hhalf
    (fiber_halfBaseProjection_lower_bound hh hconv hsegment)

/-- The same estimate with the volume scaling of the half-projection
made explicit. -/
theorem projection_volume_scaled_le_prod_volume
    {B : Set (Base d × ℝ)} {h : ℝ}
    (hh : 0 ≤ h) (hB : MeasurableSet B)
    (hhalf : MeasurableSet (halfBaseProjection B))
    (hconv : Convex ℝ B)
    (hsegment : ∀ t ∈ Set.Icc (-h) h, ((0 : Base d), t) ∈ B) :
    ENNReal.ofReal h *
        ((‖(2 : ℝ)⁻¹‖₊ ^ d) • volume (baseProjection B)) ≤
      (volume.prod volume) B := by
  have hmain := half_projection_volume_le_prod_volume
    hh hB hhalf hconv hsegment
  have hscale :
      volume (halfBaseProjection B) =
        (‖(2 : ℝ)⁻¹‖₊ ^ d) • volume (baseProjection B) := by
    rw [show (volume : Measure (Base d)) = μHE[d] by
      simpa using
        (InnerProductSpace.euclideanHausdorffMeasure_eq_volume
          (V := Base d)).symm]
    simpa only [halfBaseProjection] using
      (Measure.euclideanHausdorffMeasure_smul₀ (E := Base d) d
        (r := (2 : ℝ)⁻¹) (by norm_num) (baseProjection B))
  rwa [hscale] at hmain

/-- Compact convex bodies automatically satisfy the measurability
hypotheses in `projection_volume_scaled_le_prod_volume`. -/
theorem projection_volume_scaled_le_prod_volume_of_isCompact
    {B : Set (Base d × ℝ)} {h : ℝ}
    (hh : 0 ≤ h) (hcompact : IsCompact B)
    (hconv : Convex ℝ B)
    (hsegment : ∀ t ∈ Set.Icc (-h) h, ((0 : Base d), t) ∈ B) :
    ENNReal.ofReal h *
        ((‖(2 : ℝ)⁻¹‖₊ ^ d) • volume (baseProjection B)) ≤
      (volume.prod volume) B := by
  have hproj : IsCompact (baseProjection B) := by
    exact hcompact.image continuous_fst
  have hhalf : IsCompact (halfBaseProjection B) := by
    simpa only [halfBaseProjection] using hproj.smul (2 : ℝ)⁻¹
  exact projection_volume_scaled_le_prod_volume
    hh hcompact.measurableSet hhalf.measurableSet hconv hsegment

end Erdos186.CFP.Bilu.ProjectionVolumeCoarse

#print axioms Erdos186.CFP.Bilu.ProjectionVolumeCoarse.half_projection_volume_le_prod_volume
#print axioms Erdos186.CFP.Bilu.ProjectionVolumeCoarse.projection_volume_scaled_le_prod_volume
#print axioms Erdos186.CFP.Bilu.ProjectionVolumeCoarse.projection_volume_scaled_le_prod_volume_of_isCompact
