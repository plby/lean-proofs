/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import Mathlib

namespace Erdos353.CyclicQuad

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

end Erdos353.CyclicQuad
