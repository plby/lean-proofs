import StackExchange.Puzzling139335.N4Dispatch.FiniteRouting
import StackExchange.Puzzling139335.N4Dispatch.OneCorner.Forms
import StackExchange.Puzzling139335.N4Dispatch.OneCorner.RepeatedType
import StackExchange.Puzzling139335.N4Dispatch.OneCorner.Normalization
import StackExchange.Puzzling139335.N4Dispatch.OneCorner.MidlinePair
import StackExchange.Puzzling139335.N4Diagonal
import StackExchange.Puzzling139335.HalfTurnPair

/-!
# Excluding four single-corner pieces

The bound on used intrinsic types forces a repeated actual square-corner
placement. A common square symmetry normalizes its two corners. The
exhaustive square-isometry forms then give a reflected pair or a central
half-turn pair. The reflected cases are the proved midline and diagonal
obstructions; the remaining half-turn is excluded by its actual-pair
theorem.
-/

open Set

namespace Puzzling139335.N4Dispatch.OneCorner

open ReflectionSeparation

theorem halfTurn_pair_of_labeled_corners (d : SquareDissection)
    (hc : d.HasProtectedCenter)
    (hcorners : ∀ j i : Fin 4, corner j ∈ d.piece i ↔ j = i) :
    ∃ i j : Fin 4, i ≠ j ∧
      AffineIsometryEquiv.pointReflection ℝ squareCenter '' d.piece i = d.piece j := by
  have hN := d.cornerIncidenceCount_eq_four_of_each_tile_one
    (each_tile_one_of_labeled_corners d hcorners)
  obtain ⟨a, b, hab, e, he, _, heS⟩ :=
    exists_square_corner_pair d hc hN (fun j => (hcorners j j).mpr rfl)
  obtain ⟨D, e', k, hD, hcornersD, hk, hpair, hcorner, heS', hhalf⟩ :=
    Normalization.exists_normalized_pair d hc hcorners e heS hab he
  have hND := D.cornerIncidenceCount_eq_four_of_each_tile_one
    (each_tile_one_of_labeled_corners D hcornersD)
  have hOwnersD (j : Fin 4) : corner j ∈ D.piece j := (hcornersD j j).mpr rfl
  rcases hk with rfl | rfl
  · have hvertical := vertical_of_bottom_corner_pair D hD (by decide : (0 : Fin 4) ≠ 1)
      e' hpair heS'.subset hcorner
    rw [hvertical] at hpair
    exact (midline_pair_not_protected D hND hOwnersD hpair hD).elim
  · rcases opposite_corner_map_forms e' heS'.subset hcorner with hcentral | hdiagonal
    · have hehalf := hhalf hcentral
      exact ⟨a, b, hab, by simpa only [hehalf] using he⟩
    · rw [hdiagonal] at hpair
      exact (D.not_hasProtectedCenter_of_one_corner_antiDiagonal_pair
        hND hOwnersD hpair hD).elim

/-- The labeling normalization is an actual permutation, so any remaining
half-turn identity is an identity between original pieces. -/
theorem halfTurn_pair_of_each_tile_one (d : SquareDissection)
    (hc : d.HasProtectedCenter) (hdeg : ∀ i, d.tileCornerCount i = 1) :
    ∃ i j : Fin 4, i ≠ j ∧
      AffineIsometryEquiv.pointReflection ℝ squareCenter '' d.piece i = d.piece j := by
  obtain ⟨σ, hσ⟩ := one_corner_normalization d hdeg
  obtain ⟨i, j, hij, hpair⟩ := halfTurn_pair_of_labeled_corners (d.reindex σ)
    ((d.reindex_hasProtectedCenter σ).mpr hc) hσ
  exact ⟨σ i, σ j, σ.injective.ne hij, hpair⟩

/-- The actual `1111` corner-incidence case is impossible. -/
theorem not_hasProtectedCenter_of_each_tile_one (d : SquareDissection)
    (hdeg : ∀ i, d.tileCornerCount i = 1) : ¬ d.HasProtectedCenter := by
  intro hc
  obtain ⟨i, j, hij, hpair⟩ := halfTurn_pair_of_each_tile_one d hc hdeg
  exact d.not_hasProtectedCenter_of_halfTurn_pair hij hpair hc

end Puzzling139335.N4Dispatch.OneCorner
