/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import Mathlib

open RealInnerProductSpace

namespace Erdos353.Koizumi

noncomputable def area2 (A B C : EuclideanSpace ℝ (Fin 2)) : ℝ :=
  |(B 0 - A 0) * (C 1 - A 1) - (B 1 - A 1) * (C 0 - A 0)| / 2
noncomputable def quadArea (A B C D : EuclideanSpace ℝ (Fin 2)) : ℝ :=
  |(A 0 * B 1 - B 0 * A 1) + (B 0 * C 1 - C 0 * B 1)
    + (C 0 * D 1 - D 0 * C 1) + (D 0 * A 1 - A 0 * D 1)| / 2
def IsoscelesTriangleArea1 (A B C : EuclideanSpace ℝ (Fin 2)) : Prop :=
  area2 A B C = 1 ∧ (dist A B = dist A C ∨ dist B A = dist B C ∨ dist C A = dist C B)
def RightTriangleArea1 (A B C : EuclideanSpace ℝ (Fin 2)) : Prop :=
  area2 A B C = 1 ∧ (⟪B - A, C - A⟫ = 0 ∨ ⟪A - B, C - B⟫ = 0 ∨ ⟪A - C, B - C⟫ = 0)
noncomputable def orient (A B C : EuclideanSpace ℝ (Fin 2)) : ℝ :=
  (B 0 - A 0) * (C 1 - A 1) - (B 1 - A 1) * (C 0 - A 0)

def ConvexQuad (A B C D : EuclideanSpace ℝ (Fin 2)) : Prop :=
  (0 < orient A B C ∧ 0 < orient B C D ∧ 0 < orient C D A ∧ 0 < orient D A B) ∨
  (orient A B C < 0 ∧ orient B C D < 0 ∧ orient C D A < 0 ∧ orient D A B < 0)

def IsoTrapArea1 (A B C D : EuclideanSpace ℝ (Fin 2)) : Prop :=
  (quadArea A B C D = 1 ∧
  ((B 0 - A 0) * (C 1 - D 1) = (B 1 - A 1) * (C 0 - D 0)) ∧
  dist A D = dist B C ∧ dist A C = dist B D ∧
  A ≠ B ∧ B ≠ C ∧ C ≠ D ∧ D ≠ A ∧ A ≠ C ∧ B ≠ D) ∧ ConvexQuad A B C D

end Erdos353.Koizumi
