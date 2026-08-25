import StackExchange.Puzzling139335.SquareSymmetry.Basic
import StackExchange.Puzzling139335.JordanRegion
import Mathlib.Topology.Connected.Basic

/-!
# A disjoint reflected pair occupies opposite half-squares

Connectedness of the interior prevents a Jordan piece from crossing the
fixed line of the reflection that takes it to a disjoint-interior copy.
Regular closedness extends the resulting half-plane bound to the piece.
-/

open Set

namespace Puzzling139335.N4Midline

noncomputable section

/-- Reflection in the vertical midline of the unit square. -/
def midlineReflection : Plane ≃ᵃⁱ[ℝ] Plane := SquareSymmetry.cornerFlip 1

@[simp] theorem midlineReflection_apply (p : Plane) :
    midlineReflection p = !₂[1 - p 0, p 1] := by
  ext i
  fin_cases i <;>
    norm_num [midlineReflection, SquareSymmetry.cornerFlipPoint, corner, Fin.ext_iff]

theorem midlineReflection_fixed_iff (p : Plane) :
    midlineReflection p = p ↔ p 0 = (1 / 2 : ℝ) := by
  constructor
  · intro h
    have h₀ := congrArg (fun q : Plane => q 0) h
    simp only [midlineReflection_apply, Matrix.cons_val_zero] at h₀
    linarith
  · intro hp
    ext i
    fin_cases i
    · rw [midlineReflection_apply]
      change 1 - p 0 = p 0
      linarith
    · rw [midlineReflection_apply]
      rfl

/-- The closed left half of the square. -/
def leftHalfSquare : Set Plane :=
  {p | p 0 ∈ Icc (0 : ℝ) (1 / 2) ∧ p 1 ∈ Icc (0 : ℝ) 1}

theorem interior_avoids_midline {P : Set Plane}
    (hdis : Disjoint (interior P) (interior (midlineReflection '' P)))
    {p : Plane} (hp : p ∈ interior P) : p 0 ≠ (1 / 2 : ℝ) := by
  intro hfix
  exact (not_mem_interior_of_fixed_congruence midlineReflection rfl hdis
    ((midlineReflection_fixed_iff p).mpr hfix)).1 hp

theorem interior_left_of_reflection_disjoint {P : Set Plane}
    (hP : IsJordanRegion P) (hzero : (0 : Plane) ∈ P)
    (hdis : Disjoint (interior P) (interior (midlineReflection '' P))) :
    ∀ p ∈ interior P, p 0 < (1 / 2 : ℝ) := by
  have hcoord : Continuous (fun p : Plane => p 0) := (EuclideanSpace.proj 0).continuous
  rcases hP.isConnected_interior.isPreconnected.mapsTo_Ioi_or_Iio
      hcoord.continuousOn (fun p hp => interior_avoids_midline hdis hp) with hright | hleft
  · have hsub : P ⊆ {p : Plane | (1 / 2 : ℝ) ≤ p 0} := by
      rw [← hP.closure_interior]
      exact closure_minimal (fun p hp => show (1 / 2 : ℝ) ≤ p 0 from (hright hp).le)
        (isClosed_le continuous_const hcoord)
    have h := hsub hzero
    norm_num at h
  · exact hleft

theorem reflected_pair_subset_left {P : Set Plane}
    (hP : IsJordanRegion P) (hSquare : P ⊆ unitSquare) (hzero : (0 : Plane) ∈ P)
    (hdis : Disjoint (interior P) (interior (midlineReflection '' P))) :
    P ⊆ leftHalfSquare := by
  have hleft : P ⊆ {p : Plane | p 0 ≤ (1 / 2 : ℝ)} := by
    rw [← hP.closure_interior]
    exact closure_minimal
      (fun p hp => (interior_left_of_reflection_disjoint hP hzero hdis p hp).le)
      (isClosed_le (EuclideanSpace.proj 0).continuous continuous_const)
  intro p hp
  exact ⟨⟨(hSquare hp).1.1, hleft hp⟩, (hSquare hp).2⟩

theorem reflected_image_subset_right {P : Set Plane} (hP : P ⊆ leftHalfSquare) :
    midlineReflection '' P ⊆ {p : Plane | (1 / 2 : ℝ) ≤ p 0} := by
  rintro _ ⟨p, hp, rfl⟩
  change (1 / 2 : ℝ) ≤ (midlineReflection p) 0
  rw [midlineReflection_apply]
  change (1 / 2 : ℝ) ≤ 1 - p 0
  linarith [(hP hp).1.2]

theorem squareCenter_not_mem_reflected_pair {P : Set Plane}
    (hdis : Disjoint (interior P) (interior (midlineReflection '' P))) :
    squareCenter ∉ interior P ∧ squareCenter ∉ interior (midlineReflection '' P) :=
  not_mem_interior_of_fixed_congruence midlineReflection rfl hdis
    ((midlineReflection_fixed_iff squareCenter).mpr rfl)

end

end Puzzling139335.N4Midline
