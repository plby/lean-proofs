import Wikipedia.NoExoticSixSphere.DiskBoundaryNullhomotopy
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Tactic.Module

/-!
# Straight segments from a round disk boundary point

An interior point of a Euclidean disk lies on a unique open segment
from a selected boundary point to another boundary point. The formulas
here use the original inner product and disk, and retain the segment's
time coordinate. This is the geometric input for the reduced-suspension
description of a disk with its boundary collapsed.
-/

noncomputable section

open Set Metric
open scoped unitInterval InnerProductSpace
open Wikipedia.HopfProblem.DegreeCollapse

namespace NoExoticSixSphere.RoundDiskBoundarySegments

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

abbrev Boundary := DiskCylinder.Sphere (E := E)
abbrev Disk := DiskCylinder.Disk (E := E)

def point (b : Boundary (E := E)) : C(unitInterval × Boundary (E := E), Disk (E := E)) :=
  (DiskBoundary.segment (DiskCylinder.boundaryToDisk b)).comp
    ⟨fun z ↦ (z.1, DiskCylinder.boundaryToDisk z.2),
      continuous_fst.prodMk (DiskCylinder.boundaryToDisk.continuous.comp continuous_snd)⟩

theorem point_val (b s : Boundary (E := E)) (t : unitInterval) :
    (point b (t, s)).val = (1 - (t : ℝ)) • s.val + (t : ℝ) • b.val := rfl

theorem point_zero (b s : Boundary (E := E)) :
    point b (0, s) = DiskCylinder.boundaryToDisk s :=
  DiskBoundary.segment_zero _ _

theorem point_one (b s : Boundary (E := E)) :
    point b (1, s) = DiskCylinder.boundaryToDisk b :=
  DiskBoundary.segment_one _ _

theorem point_base (b : Boundary (E := E)) (t : unitInterval) :
    point b (t, b) = DiskCylinder.boundaryToDisk b :=
  DiskBoundary.segment_fixed _ _

omit [InnerProductSpace ℝ E] in
theorem norm_boundary (s : Boundary (E := E)) : ‖s.val‖ = 1 :=
  mem_sphere_zero_iff_norm.mp s.property

theorem chord_sq (b s : Boundary (E := E)) :
    ‖s.val - b.val‖ ^ 2 = 2 * (1 - ⟪s.val, b.val⟫_ℝ) := by
  rw [norm_sub_sq_real, norm_boundary, norm_boundary]
  ring

theorem point_sub (b s : Boundary (E := E)) (t : unitInterval) :
    (point b (t, s)).val - b.val = (1 - (t : ℝ)) • (s.val - b.val) := by
  rw [point_val]
  module

theorem point_inner (b s : Boundary (E := E)) (t : unitInterval) :
    ⟪(point b (t, s)).val, b.val⟫_ℝ =
      (1 - (t : ℝ)) * ⟪s.val, b.val⟫_ℝ + (t : ℝ) := by
  rw [point_val, inner_add_left, real_inner_smul_left, real_inner_smul_left,
    real_inner_self_eq_norm_sq, norm_boundary]
  ring

theorem point_chord_sq (b s : Boundary (E := E)) (t : unitInterval) :
    ‖(point b (t, s)).val - b.val‖ ^ 2 =
      2 * (1 - (t : ℝ)) * (1 - ⟪(point b (t, s)).val, b.val⟫_ℝ) := by
  rw [point_sub, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs, chord_sq, point_inner]
  ring

theorem point_norm_sq (b s : Boundary (E := E)) (t : unitInterval) :
    ‖(point b (t, s)).val‖ ^ 2 =
      1 - (t : ℝ) * (1 - (t : ℝ)) * ‖s.val - b.val‖ ^ 2 := by
  rw [point_val, norm_add_sq_real, norm_smul, norm_smul, Real.norm_eq_abs,
    Real.norm_eq_abs, mul_pow, mul_pow, sq_abs, sq_abs,
    real_inner_smul_left, real_inner_smul_right, norm_boundary, norm_boundary, chord_sq]
  ring

theorem point_mem_ball (b s : Boundary (E := E)) (t : unitInterval)
    (ht₀ : 0 < (t : ℝ)) (ht₁ : (t : ℝ) < 1) (hs : s ≠ b) :
    (point b (t, s)).val ∈ ball (0 : E) 1 := by
  have hsb : s.val - b.val ≠ 0 := sub_ne_zero.mpr (fun h ↦ hs (Subtype.ext h))
  have hp : 0 < (t : ℝ) * (1 - (t : ℝ)) * ‖s.val - b.val‖ ^ 2 :=
    mul_pos (mul_pos ht₀ (sub_pos.mpr ht₁)) (sq_pos_of_pos (norm_pos_iff.mpr hsb))
  have he := point_norm_sq b s t
  rw [mem_ball_zero_iff]
  nlinarith [norm_nonneg (point b (t, s)).val]

theorem point_mem_sphere_iff (b s : Boundary (E := E)) (t : unitInterval) :
    (point b (t, s)).val ∈ sphere (0 : E) 1 ↔ t = 0 ∨ t = 1 ∨ s = b := by
  constructor
  · intro h
    by_cases h₀ : t = 0
    · exact Or.inl h₀
    by_cases h₁ : t = 1
    · exact Or.inr (Or.inl h₁)
    by_cases hs : s = b
    · exact Or.inr (Or.inr hs)
    have hball := point_mem_ball b s t
      (lt_of_le_of_ne t.property.1 (fun he ↦ h₀ (Subtype.ext he.symm)))
      (lt_of_le_of_ne t.property.2 (fun he ↦ h₁ (Subtype.ext he))) hs
    exact False.elim ((not_lt_of_ge (mem_sphere.mp h).ge) hball)
  · rintro (rfl | rfl | hs)
    · rw [point_zero]
      exact s.property
    · rw [point_one]
      exact b.property
    · subst s
      rw [point_base]
      exact b.property

theorem inner_lt_one_of_mem_ball (b : Boundary (E := E)) {x : E}
    (hx : x ∈ ball (0 : E) 1) : ⟪x, b.val⟫_ℝ < 1 := by
  have hi := real_inner_le_norm x b.val
  rw [norm_boundary, mul_one] at hi
  exact hi.trans_lt (mem_ball_zero_iff.mp hx)

theorem point_injective_interior (b s r : Boundary (E := E)) (t u : unitInterval)
    (ht₀ : 0 < (t : ℝ)) (ht₁ : (t : ℝ) < 1) (hs : s ≠ b)
    (he : point b (t, s) = point b (u, r)) : t = u ∧ s = r := by
  have hball := point_mem_ball b s t ht₀ ht₁ hs
  have hi := inner_lt_one_of_mem_ball b hball
  have ht := point_chord_sq b s t
  have hu := point_chord_sq b r u
  rw [← he] at hu
  have htu : (t : ℝ) = u := by nlinarith
  have htu' : t = u := Subtype.ext htu
  refine ⟨htu', ?_⟩
  subst u
  have hv := congrArg Subtype.val he
  rw [point_val, point_val] at hv
  have hsm := add_right_cancel hv
  apply Subtype.ext
  exact smul_right_injective E (sub_ne_zero.mpr (ne_of_gt ht₁)) hsm

end NoExoticSixSphere.RoundDiskBoundarySegments
