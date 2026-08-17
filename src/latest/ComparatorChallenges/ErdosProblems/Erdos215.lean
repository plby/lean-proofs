import Mathlib

noncomputable section

attribute [local instance] Classical.propDecidable

namespace Erdos215

abbrev Point : Type := EuclideanSpace ℝ (Fin 2)

end Erdos215

namespace Erdos215

abbrev IntPoint : Type := Fin 2 → ℤ

end Erdos215

namespace Erdos215

def intPoint (z : IntPoint) : Point :=
  WithLp.toLp 2 (fun i ↦ (z i : ℝ))

end Erdos215

namespace Erdos215

def integerLattice : Set Point := Set.range intPoint

end Erdos215

namespace Erdos215

def rotate (c s : ℝ) (p : Point) : Point :=
  WithLp.toLp 2 fun i : Fin 2 ↦
    if i = 0 then c * p 0 - s * p 1 else s * p 0 + c * p 1

end Erdos215

namespace Erdos215

def motion (t : Point) (c s : ℝ) (p : Point) : Point :=
  t + rotate c s p

end Erdos215

namespace Erdos215

def movedSet (S : Set Point) (t : Point) (c s : ℝ) : Set Point :=
  motion t c s '' S

end Erdos215

namespace Erdos215

def IsSteinhaus (S : Set Point) : Prop :=
  ∀ (t : Point) (c s : ℝ), c ^ 2 + s ^ 2 = 1 →
    ∃! z : Point, z ∈ integerLattice ∧ z ∈ movedSet S t c s

end Erdos215

namespace Erdos215

theorem erdos215 : ∃ S : Set Point, IsSteinhaus S := by
  sorry

end Erdos215

end
