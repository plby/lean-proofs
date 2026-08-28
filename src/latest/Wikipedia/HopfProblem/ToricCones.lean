import Wikipedia.HopfProblem.ToricFan
import Mathlib.Geometry.Convex.Cone.Basic
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.Analysis.Normed.Module.FiniteDimension

/-!
# The simplicial cones over the integral triangulation

This file proves the unimodular cone description and the support assertion
in Lemma 4.2(i) of `tex/s6.tex`. The common-face and Hausdorff gluing arguments
are separate from this support calculation.
-/

noncomputable section

open Set Topology
open scoped Matrix

namespace Wikipedia.HopfProblem.ToricFan.Triangle

abbrev RealCoordinates := Fin 3 → ℝ

def coordinates (s : Triangle) : RealCoordinates →ₗ[ℝ] RealCoordinates :=
  (s.dual.map (Int.castRingHom ℝ)).mulVecLin

def generate (s : Triangle) : RealCoordinates →ₗ[ℝ] RealCoordinates :=
  (s.rays.map (Int.castRingHom ℝ)).mulVecLin

theorem coordinates_lower (a b : ℤ) (x : RealCoordinates) :
    coordinates ⟨a, b, false⟩ x =
      ![(1 + (a : ℝ) + b) * x 2 - x 0 - x 1, x 0 - a * x 2, x 1 - b * x 2] := by
  ext i
  fin_cases i <;>
    simp [coordinates, dual, Matrix.mulVec,
      dotProduct, Fin.sum_univ_succ] <;> ring

theorem coordinates_upper (a b : ℤ) (x : RealCoordinates) :
    coordinates ⟨a, b, true⟩ x =
      ![((b : ℝ) + 1) * x 2 - x 1, ((a : ℝ) + 1) * x 2 - x 0,
        x 0 + x 1 - (1 + (a : ℝ) + b) * x 2] := by
  ext i
  fin_cases i <;>
    simp [coordinates, dual, Matrix.mulVec,
      dotProduct, Fin.sum_univ_succ] <;> ring

theorem generate_coordinates (s : Triangle) (x : RealCoordinates) :
    s.generate (s.coordinates x) = x := by
  change (s.rays.map (Int.castRingHom ℝ)) *ᵥ
    ((s.dual.map (Int.castRingHom ℝ)) *ᵥ x) = x
  rw [Matrix.mulVec_mulVec, ← Matrix.map_mul, rays_dual]
  simp

theorem coordinates_generate (s : Triangle) (x : RealCoordinates) :
    s.coordinates (s.generate x) = x := by
  change (s.dual.map (Int.castRingHom ℝ)) *ᵥ
    ((s.rays.map (Int.castRingHom ℝ)) *ᵥ x) = x
  rw [Matrix.mulVec_mulVec, ← Matrix.map_mul, dual_rays]
  simp

theorem coordinates_sum (s : Triangle) (x : RealCoordinates) :
    ∑ i, s.coordinates x i = x 2 := by
  obtain ⟨a, b, upper⟩ := s
  cases upper <;>
    simp [coordinates_lower, coordinates_upper, Fin.sum_univ_succ] <;> ring

/-- The closed nonnegative span of the three height-one primitive rays. -/
def cone (s : Triangle) : ConvexCone ℝ RealCoordinates where
  carrier := {x | ∀ i, 0 ≤ s.coordinates x i}
  smul_mem' := by
    intro c hc x hx i
    simpa using mul_nonneg hc.le (hx i)
  add_mem' := by
    intro x hx y hy i
    simpa using add_nonneg (hx i) (hy i)

@[simp] theorem mem_cone (s : Triangle) (x : RealCoordinates) :
    x ∈ s.cone ↔ ∀ i, 0 ≤ s.coordinates x i := Iff.rfl

theorem zero_mem_cone (s : Triangle) : (0 : RealCoordinates) ∈ s.cone := by
  simp

theorem cone_closed (s : Triangle) : IsClosed (s.cone : Set RealCoordinates) := by
  change IsClosed {x | ∀ i, 0 ≤ s.coordinates x i}
  simp only [Set.ofPred_forall]
  apply isClosed_iInter
  intro i
  exact isClosed_le continuous_const
    ((continuous_apply i).comp s.coordinates.continuous_of_finiteDimensional)

theorem mem_cone_iff_generated (s : Triangle) (x : RealCoordinates) :
    x ∈ s.cone ↔ ∃ c : RealCoordinates, (∀ i, 0 ≤ c i) ∧ s.generate c = x := by
  constructor
  · intro hx
    exact ⟨s.coordinates x, hx, s.generate_coordinates x⟩
  · rintro ⟨c, hc, rfl⟩
    simpa only [mem_cone, coordinates_generate] using hc

theorem height_nonneg (s : Triangle) {x : RealCoordinates} (hx : x ∈ s.cone) :
    0 ≤ x 2 := by
  rw [← coordinates_sum s x]
  exact Finset.sum_nonneg fun i _ => hx i

theorem eq_zero_of_height_zero (s : Triangle) {x : RealCoordinates}
    (hx : x ∈ s.cone) (hzero : x 2 = 0) : x = 0 := by
  have hsum : ∑ i, s.coordinates x i = 0 := (s.coordinates_sum x).trans hzero
  have hc : s.coordinates x = 0 := by
    ext i
    exact (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => hx j)).mp hsum i
      (Finset.mem_univ i)
  rw [← generate_coordinates s x, hc, map_zero]

theorem cone_strongly_convex (s : Triangle) {x : RealCoordinates}
    (hx : x ∈ s.cone) (hnx : -x ∈ s.cone) : x = 0 := by
  apply s.eq_zero_of_height_zero hx
  have hp := s.height_nonneg hx
  have hn := s.height_nonneg hnx
  simpa using le_antisymm (neg_nonneg.mp hn) hp

/-- Every point of positive height belongs to one of the two integral
triangles over the square selected by its two floor coordinates. -/
theorem exists_cone_of_height_pos {x : RealCoordinates} (hh : 0 < x 2) :
    ∃ s : Triangle, x ∈ s.cone := by
  let a := ⌊x 0 / x 2⌋
  let b := ⌊x 1 / x 2⌋
  have ha : (a : ℝ) * x 2 ≤ x 0 := (le_div_iff₀ hh).mp (Int.floor_le _)
  have hb : (b : ℝ) * x 2 ≤ x 1 := (le_div_iff₀ hh).mp (Int.floor_le _)
  have ha' : x 0 < ((a : ℝ) + 1) * x 2 :=
    (div_lt_iff₀ hh).mp (Int.lt_floor_add_one _)
  have hb' : x 1 < ((b : ℝ) + 1) * x 2 :=
    (div_lt_iff₀ hh).mp (Int.lt_floor_add_one _)
  by_cases hsum : x 0 + x 1 ≤ (1 + (a : ℝ) + b) * x 2
  · refine ⟨⟨a, b, false⟩, ?_⟩
    rw [mem_cone, coordinates_lower]
    intro i
    fin_cases i <;> dsimp <;> linarith
  · refine ⟨⟨a, b, true⟩, ?_⟩
    rw [mem_cone, coordinates_upper]
    intro i
    fin_cases i <;> dsimp <;> linarith

/-- The support is exactly the open upper half-space together with the origin. -/
theorem cone_support (x : RealCoordinates) :
    (∃ s : Triangle, x ∈ s.cone) ↔ 0 < x 2 ∨ x = 0 := by
  constructor
  · rintro ⟨s, hs⟩
    by_cases hh : x 2 = 0
    · exact Or.inr (s.eq_zero_of_height_zero hs hh)
    · exact Or.inl (lt_of_le_of_ne (s.height_nonneg hs) (Ne.symm hh))
  · rintro (hh | rfl)
    · exact exists_cone_of_height_pos hh
    · exact ⟨⟨0, 0, false⟩, zero_mem_cone _⟩

end Wikipedia.HopfProblem.ToricFan.Triangle
