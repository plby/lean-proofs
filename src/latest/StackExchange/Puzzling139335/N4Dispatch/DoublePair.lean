import StackExchange.Puzzling139335.N4Dispatch.DoublePair.RepeatedTypes
import StackExchange.Puzzling139335.N4Dispatch.DoublePair.Normalize

/-!
# Routing the four-incidence `2200` branch

Two distinct double-corner tiles use a common intrinsic point and hence
have an actual relative square symmetry.  Their uniquely owned physical
corner pairs lie on opposite sides.  Unless the selected pieces are an
actual central half-turn pair, an actual coordinate change and relabeling
give the horizontal reflected outer-pair configuration.

The dichotomy below has no half-turn exclusion hypothesis.  Its corollaries
keep any such exclusion explicit for assembly with the separate half-turn
theorem.
-/

open Set

namespace Puzzling139335.N4Dispatch.DoublePair

/-- Normalize the two-double-corner branch once the actual central half-turn
identity for the selected pair has been excluded. -/
theorem exists_configuration (d : SquareDissection)
    (hc : d.HasProtectedCenter) (hN : d.cornerIncidenceCount = 4)
    {i j : Fin 4} (hij : i ≠ j)
    (hi : d.tileCornerCount i = 2) (hj : d.tileCornerCount j = 2)
    (hno : AffineIsometryEquiv.pointReflection ℝ squareCenter '' d.piece i ≠ d.piece j) :
    ∃ d' : SquareDissection, d'.HasProtectedCenter ∧ N4OuterPair.Configuration d' :=
  exists_configuration_of_square_pair d hc hN hij hi
    (d.relativePlacement i j) (d.relativePlacement_image i j)
    (relativePlacement_preserves_square d hc hN hi hj) hno

/-- Exhaustive geometric routing of the `2200` branch, without assuming the
central half-turn obstruction in advance. -/
theorem halfTurn_pair_or_configuration (d : SquareDissection)
    (hc : d.HasProtectedCenter) (hN : d.cornerIncidenceCount = 4)
    {i j : Fin 4} (hij : i ≠ j)
    (hi : d.tileCornerCount i = 2) (hj : d.tileCornerCount j = 2) :
    AffineIsometryEquiv.pointReflection ℝ squareCenter '' d.piece i = d.piece j ∨
      ∃ d' : SquareDissection, d'.HasProtectedCenter ∧ N4OuterPair.Configuration d' := by
  by_cases hhalf :
      AffineIsometryEquiv.pointReflection ℝ squareCenter '' d.piece i = d.piece j
  · exact Or.inl hhalf
  · exact Or.inr (exists_configuration d hc hN hij hi hj hhalf)

/-- Dispatch from the existential degree pattern produced by finite counting. -/
theorem exists_configuration_of_selected_double_pair (d : SquareDissection)
    (hc : d.HasProtectedCenter) (hN : d.cornerIncidenceCount = 4)
    (hno : ∀ i j : Fin 4, i ≠ j →
      AffineIsometryEquiv.pointReflection ℝ squareCenter '' d.piece i ≠ d.piece j)
    (hpair : ∃ i j : Fin 4, i ≠ j ∧
      d.tileCornerCount i = 2 ∧ d.tileCornerCount j = 2) :
    ∃ d' : SquareDissection, d'.HasProtectedCenter ∧ N4OuterPair.Configuration d' := by
  obtain ⟨i, j, hij, hi, hj⟩ := hpair
  exact exists_configuration d hc hN hij hi hj (hno i j hij)

end Puzzling139335.N4Dispatch.DoublePair
