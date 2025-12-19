import Mathlib

notation "ℝ²" => EuclideanSpace ℝ (Fin 2)

variable {V P : Type*} {n : ℕ}
variable [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MetricSpace P] [NormedAddTorsor V P]
variable [Module.Oriented ℝ V (Fin 2)] [Fact (Module.finrank ℝ V = 2)] {p : Fin n → P}

/-- Oriented angles make sense in 2d.

Note: this can't blindly be added to mathlib as it creates an "instance diamond"
with an instance for modules satisfying `is_empty`. -/
noncomputable instance Module.orientedEuclideanSpaceFinTwo : Module.Oriented ℝ ℝ² (Fin 2) :=
  ⟨Basis.orientation <| Pi.basisFun _ _⟩

/-- Two dimensional euclidean space is two-dimensional. -/
instance fact_finrank_euclideanSpace_fin_two : Fact (Module.finrank ℝ ℝ² = 2) :=
  ⟨finrank_euclideanSpace_fin⟩

/-- The statement that a sequence of points form a counter-clockwise convex polygon. -/
def IsCcwConvexPolygon (p : Fin n → P) : Prop :=
  ∀ ⦃i j k⦄, i < j → j < k → (EuclideanGeometry.oangle (p i) (p j) (p k)).sign = 1

/-- Erdős problem 189 asked whether the below holds for all rectangles. -/
def Erdos189For (P : ℝ² → ℝ² → ℝ² → ℝ² → Prop) (A : ℝ² → ℝ² → ℝ² → ℝ² → ℝ) :=
    ∀ᵉ (n > 0) (colouring : ℝ² → Fin n), ∃ colour, ∀ area > (0 : ℝ), ∃ a b c d,
      {a, b, c, d} ⊆ colouring⁻¹' {colour} ∧
      IsCcwConvexPolygon ![a, b, c, d] ∧
      A a b c d = area ∧
      P a b c d

theorem erdos_189 :
    Erdos189For
      (fun a b c d ↦
        line[ℝ, a, b].direction ⟂ line[ℝ, b, c].direction ∧
        line[ℝ, b, c].direction ⟂ line[ℝ, c, d].direction ∧
        line[ℝ, c, d].direction ⟂ line[ℝ, d, a].direction)
      (fun a b c d ↦ dist a b * dist b c) ↔ False := by
  sorry
