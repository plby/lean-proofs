/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import Mathlib

open scoped BigOperators
open Finset

namespace Erdos94

abbrev Point := EuclideanSpace ℝ (Fin 2)
noncomputable section

def DistSet (P : Finset Point) : Finset ℝ :=
  (P.offDiag.image (fun pq => dist pq.1 pq.2))
def distSym2 (z : Sym2 Point) : ℝ :=
  Sym2.lift ⟨fun a b => dist a b, by
    intro a b
    simp [dist_comm]⟩ z
def f (P : Finset Point) (u : ℝ) : ℕ :=
  ((P.sym2.filter (fun z => ¬ Sym2.IsDiag z ∧ distSym2 z = u)).card)
def S (P : Finset Point) : ℝ :=
  ∑ u ∈ DistSet P, ((f P u : ℝ)^2)
syntax "S(" term ")=O(n^3)" : term
def NoThreeCollinear (P : Finset Point) : Prop :=
  ∀ ⦃x y z : Point⦄, x ∈ P → y ∈ P → z ∈ P →
    x ≠ y → y ≠ z → x ≠ z → ¬ Collinear ℝ ({x, y, z} : Set Point)
def ConvexPosition (P : Finset Point) : Prop :=
  (P : Set Point) ⊆ (convexHull ℝ (P : Set Point)).extremePoints ℝ
end
end Erdos94


open scoped BigOperators
open Finset

namespace Erdos94

open scoped Classical in
theorem erdos94_convex_no3collinear (P : Finset Point)
    (hconv : ConvexPosition P) (hnc : NoThreeCollinear P) :
    S P ≤ (3 / 4 : ℝ) * (P.card : ℝ)^2 * ((P.card : ℝ) - 1) := by
  sorry

end Erdos94
