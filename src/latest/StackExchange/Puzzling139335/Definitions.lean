import Mathlib.Analysis.Normed.Affine.Isometry
import Wikipedia.SchoenfliesTheorem.CrosscutCells

/-!
# Four congruent Jordan regions in a square

The plane has its Euclidean metric, not the maximum metric on `ℝ × ℝ`.
A piece is the closure of the bounded complementary region of a simple
closed curve. No convexity, boundary rectifiability, or zero-boundary-area
condition is imposed. Congruences include orientation-reversing affine
isometries of the whole plane.

These are the hypotheses of the written proof. In particular, none of the
geometric reductions or case exclusions is included in the definition of a
dissection.
-/

open Set

namespace Puzzling139335

noncomputable section

/-- The Euclidean plane, compatible with the existing Jordan/Schoenflies API. -/
abbrev Plane := EuclideanSpace ℝ (Fin 2)

/-- The closed unit square. -/
def unitSquare : Set Plane :=
  {p | p 0 ∈ Icc (0 : ℝ) 1 ∧ p 1 ∈ Icc (0 : ℝ) 1}

/-- The point whose neighborhood is required to belong to one piece. -/
def squareCenter : Plane := !₂[(1 / 2 : ℝ), (1 / 2 : ℝ)]

/-- Square corners in counterclockwise order: bottom left, bottom right,
top right, and top left. -/
def corner (i : Fin 4) : Plane :=
  !₂[if i = 1 ∨ i = 2 then 1 else 0, if i = 2 ∨ i = 3 then 1 else 0]

/-- The filled region bounded by one simple closed curve. -/
def IsJordanRegion (P : Set Plane) : Prop :=
  ∃ C : Set Plane, Schoenflies.IsJordanCurve C ∧ P = closure (Schoenflies.inside C)

/-- Euclidean congruence; reflections are allowed. -/
def Congruent (P Q : Set Plane) : Prop :=
  ∃ e : Plane ≃ᵃⁱ[ℝ] Plane, e '' P = Q

/-- Exactly four congruent closed Jordan regions, covering the square with
pairwise disjoint interiors. Shared boundary points are allowed. -/
structure SquareDissection where
  piece : Fin 4 → Set Plane
  jordan : ∀ i, IsJordanRegion (piece i)
  congruent : ∀ i j, Congruent (piece i) (piece j)
  covers : (⋃ i, piece i) = unitSquare
  disjoint_interiors : Pairwise fun i j => Disjoint (interior (piece i)) (interior (piece j))

/-- The prohibited configuration: an open neighborhood of the center in one piece. -/
def SquareDissection.HasProtectedCenter (d : SquareDissection) : Prop :=
  ∃ i, squareCenter ∈ interior (d.piece i)

/-- The full target, kept separate from every dissection hypothesis. -/
def SquareCenterTheorem : Prop :=
  ∀ d : SquareDissection, ¬ d.HasProtectedCenter

@[simp] theorem squareCenter_apply_zero : squareCenter 0 = (1 / 2 : ℝ) := rfl

@[simp] theorem squareCenter_apply_one : squareCenter 1 = (1 / 2 : ℝ) := rfl

theorem squareCenter_mem_unitSquare : squareCenter ∈ unitSquare := by
  norm_num [unitSquare, squareCenter]

theorem corner_mem_unitSquare (i : Fin 4) : corner i ∈ unitSquare := by
  by_cases hx : i = 1 ∨ i = 2 <;> by_cases hy : i = 2 ∨ i = 3 <;>
    simp [unitSquare, corner, hx, hy]

theorem corner_injective : Function.Injective corner := by
  intro i j hij
  have hzero := congrArg (fun p : Plane => p 0) hij
  have hone := congrArg (fun p : Plane => p 1) hij
  fin_cases i <;> fin_cases j <;> simp_all [corner, Fin.ext_iff]

@[simp] theorem corner_inj {i j : Fin 4} : corner i = corner j ↔ i = j :=
  corner_injective.eq_iff

theorem SquareDissection.piece_subset (d : SquareDissection) (i : Fin 4) :
    d.piece i ⊆ unitSquare := by
  intro p hp
  rw [← d.covers]
  exact mem_iUnion.mpr ⟨i, hp⟩

theorem SquareDissection.exists_piece_mem (d : SquareDissection) {p : Plane}
    (hp : p ∈ unitSquare) : ∃ i, p ∈ d.piece i := by
  rw [← d.covers] at hp
  exact mem_iUnion.mp hp

end

end Puzzling139335
