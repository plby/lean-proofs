/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import Mathlib

open MeasureTheory RealInnerProductSpace

namespace Erdos353

namespace Koizumi

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

end Koizumi

namespace CyclicQuad

abbrev Pt := EuclideanSpace ℝ (Fin 2)

noncomputable def orient (X Y Z : Pt) : ℝ :=
  (Y 0 - X 0) * (Z 1 - X 1) - (Z 0 - X 0) * (Y 1 - X 1)

noncomputable def quadArea (P Q R S : Pt) : ℝ :=
  ((P 0 * Q 1 - Q 0 * P 1) + (Q 0 * R 1 - R 0 * Q 1) +
   (R 0 * S 1 - S 0 * R 1) + (S 0 * P 1 - P 0 * S 1)) / 2

def Concyclic4 (P Q R S : Pt) : Prop :=
  ∃ (O : Pt) (r : ℝ), 0 < r ∧ dist P O = r ∧ dist Q O = r ∧ dist R O = r ∧ dist S O = r

def ConvexQuadCCW (P Q R S : Pt) : Prop :=
  0 < orient P Q R ∧ 0 < orient Q R S ∧ 0 < orient R S P ∧ 0 < orient S P Q

def UnitCyclicQuad (P Q R S : Pt) : Prop :=
  Concyclic4 P Q R S ∧ ConvexQuadCCW P Q R S ∧ quadArea P Q R S = 1

end CyclicQuad

namespace Kovac

noncomputable def cross (u v : EuclideanSpace ℝ (Fin 2)) : ℝ := u 0 * v 1 - u 1 * v 0

end Kovac

theorem erdos_353 :
    (∀ S : Set (EuclideanSpace ℝ (Fin 2)), MeasurableSet S → volume S = ⊤ →
      (∃ A B C D, A ∈ S ∧ B ∈ S ∧ C ∈ S ∧ D ∈ S ∧ Koizumi.IsoTrapArea1 A B C D) ∧
      (∃ A B C, A ∈ S ∧ B ∈ S ∧ C ∈ S ∧ Koizumi.IsoscelesTriangleArea1 A B C) ∧
      (∃ A B C, A ∈ S ∧ B ∈ S ∧ C ∈ S ∧ Koizumi.RightTriangleArea1 A B C) ∧
      (∃ A B C D, A ∈ S ∧ B ∈ S ∧ C ∈ S ∧ D ∈ S ∧ CyclicQuad.UnitCyclicQuad A B C D)) ∧
    (∃ S : Set (EuclideanSpace ℝ (Fin 2)), MeasurableSet S ∧ volume S = ⊤ ∧
      ∀ (n : ℕ) (C : ZMod n → EuclideanSpace ℝ (Fin 2)), 3 ≤ n →
        (∀ i j : ZMod n, j ≠ i → j ≠ i + 1 →
          0 < Kovac.cross (C (i + 1) - C i) (C j - C i)) →
        (∃ a : ℝ, 0 < a ∧ ∀ i : ZMod n, dist (C i) (C (i + 1)) = a) →
        (∀ i : ZMod n, C i ∈ S) → volume (convexHull ℝ (Set.range C)) < 1) := by
  sorry

end Erdos353
