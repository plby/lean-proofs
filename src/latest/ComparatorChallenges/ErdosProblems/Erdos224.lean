import Mathlib

open scoped BigOperators
open scoped Real
open scoped RealInnerProductSpace
open scoped Pointwise
open MeasureTheory
open Filter

namespace Erdos224

noncomputable section

variable {d : ℕ}

abbrev E (d : ℕ) := EuclideanSpace ℝ (Fin d)
local instance (d : ℕ) : MeasurableSpace (E d) := borel (E d)
local instance (d : ℕ) : BorelSpace (E d) := ⟨rfl⟩
local instance (S : AffineSubspace ℝ (E d)) :
    NormedAddTorsor S.direction S.direction :=
  SeminormedAddCommGroup.toNormedAddTorsor

def ObtuseAt {d : ℕ} (x y z : E d) : Prop :=
  ⟪y - x, z - x⟫ < 0
end

end Erdos224

attribute [local instance] Classical.propDecidable

open scoped BigOperators
open scoped Real
open scoped RealInnerProductSpace
open scoped Pointwise
open MeasureTheory
open Filter

namespace Erdos224

theorem exists_obtuse_of_card_succ_pow_two
  (A : Finset (E d))
  (hcard : A.card = (2 ^ d) + 1) :
  ∃ x y z : E d, x ∈ A ∧ y ∈ A ∧ z ∈ A ∧
    x ≠ y ∧ x ≠ z ∧ y ≠ z ∧
    ObtuseAt (d := d) x y z := by
  sorry

end Erdos224
