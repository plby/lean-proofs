import StackExchange.Puzzling139335.N4Dispatch.DoublePair.Normalize.Transport
import StackExchange.Puzzling139335.N4Dispatch.DoublePair.Normalize.Orientation
import StackExchange.Puzzling139335.N4Dispatch.DoublePair.Normalize.Reindex
import StackExchange.Puzzling139335.N8.Pairs.Local

/-!
# Normalizing an actual square-symmetry pair with a full corner side

Unique ownership of all four physical corners forces the image of a
double-corner side to be the opposite side.  After a common square symmetry,
the only possible congruences are horizontal reflection and the central
half-turn.  Excluding the latter gives the actual reflected outer pair.

The conclusion is an actual transformed and relabeled dissection.  No
intrinsic-corner choices or assumptions about convex hull segments occur.
-/

open Set

namespace Puzzling139335.N4Dispatch.DoublePair

open Normalize

theorem exists_configuration_of_adjacent_square_pair (d : SquareDissection)
    (hc : d.HasProtectedCenter)
    (hu : ∀ (i j a : Fin 4), corner a ∈ d.piece i → corner a ∈ d.piece j → i = j)
    {i j : Fin 4} (hij : i ≠ j) (s : Fin 4)
    (hfirst : corner s ∈ d.piece i) (hsecond : corner (s + 1) ∈ d.piece i)
    (e : Plane ≃ᵃⁱ[ℝ] Plane) (he : e '' d.piece i = d.piece j)
    (heS : e '' unitSquare = unitSquare)
    (hno : AffineIsometryEquiv.pointReflection ℝ squareCenter '' d.piece i ≠ d.piece j) :
    ∃ d' : SquareDissection, d'.HasProtectedCenter ∧ N4OuterPair.Configuration d' := by
  obtain ⟨f, hfS, hf0, hf1⟩ := exists_side_normalizing_isometry s
  let D := d.map f hfS
  let g := conjugate f e
  have hDc : D.HasProtectedCenter := (d.map_hasProtectedCenter f hfS).mpr hc
  have hDu : ∀ (a b k : Fin 4), corner k ∈ D.piece a →
      corner k ∈ D.piece b → a = b := unique_corner_owners_map d f hfS hu
  have hBL : corner 0 ∈ D.piece i := (corner_mem_map_iff d f hfS hf0 i).mpr hfirst
  have hBR : corner 1 ∈ D.piece i := (corner_mem_map_iff d f hfS hf1 i).mpr hsecond
  have hgS : g '' unitSquare = unitSquare := conjugate_preserves_square f e hfS heS
  have hgP : g '' D.piece i = D.piece j := conjugate_image_piece d f e hfS he
  have hnot (a b : Fin 4) (ha : corner a ∈ D.piece i)
      (hb : corner b ∈ D.piece i) : g (corner a) ≠ corner b := by
    intro hab
    apply hij
    apply hDu i j b hb
    rw [← hab, ← hgP]
    exact mem_image_of_mem g ha
  have hgrefl : g = ReflectionSeparation.horizontal := by
    rcases eq_horizontal_or_pointReflection_of_bottom_disjoint g hgS
      (hnot 0 0 hBL hBL) (hnot 0 1 hBL hBR)
      (hnot 1 0 hBR hBL) (hnot 1 1 hBR hBR) with hhor | hhalf
    · exact hhor
    · have hnoD := no_center_reflection_pair_map d f hfS hno
      exact (hnoD (by rwa [← hhalf])).elim
  have hreflected : ReflectionSeparation.horizontal '' D.piece i = D.piece j := by
    rwa [← hgrefl]
  have hh0 : ReflectionSeparation.horizontal (corner 0) = corner 3 := by
    ext a
    fin_cases a <;> norm_num [corner, Fin.ext_iff]
  have hh1 : ReflectionSeparation.horizontal (corner 1) = corner 2 := by
    ext a
    fin_cases a <;> norm_num [corner, Fin.ext_iff]
  have hTL : corner 3 ∈ D.piece j := by
    rw [← hh0, ← hreflected]
    exact mem_image_of_mem ReflectionSeparation.horizontal hBL
  have hTR : corner 2 ∈ D.piece j := by
    rw [← hh1, ← hreflected]
    exact mem_image_of_mem ReflectionSeparation.horizontal hBR
  have hcornerless : ∀ k : Fin 4, k ≠ i → k ≠ j →
      ∀ a : Fin 4, corner a ∉ D.piece k := by
    intro k hki hkj a ha
    fin_cases a
    · exact hki (hDu k i 0 ha hBL)
    · exact hki (hDu k i 1 ha hBR)
    · exact hkj (hDu k j 2 ha hTR)
    · exact hkj (hDu k j 3 ha hTL)
  exact exists_configuration_of_horizontal_pair D hDc hij hBL hBR hreflected hcornerless

/-- Four incidences discharge unique corner ownership, and a two-corner
piece supplies the adjacent side.  The only extra exclusion is the actual
central half-turn identity for this selected pair. -/
theorem exists_configuration_of_square_pair (d : SquareDissection)
    (hc : d.HasProtectedCenter) (hN : d.cornerIncidenceCount = 4)
    {i j : Fin 4} (hij : i ≠ j) (hi : d.tileCornerCount i = 2)
    (e : Plane ≃ᵃⁱ[ℝ] Plane) (he : e '' d.piece i = d.piece j)
    (heS : e '' unitSquare = unitSquare)
    (hno : AffineIsometryEquiv.pointReflection ℝ squareCenter '' d.piece i ≠ d.piece j) :
    ∃ d' : SquareDissection, d'.HasProtectedCenter ∧ N4OuterPair.Configuration d' := by
  obtain ⟨s, hs⟩ := N8.exists_local_side_of_count_two d hc i hi
  have hu : ∀ (a b k : Fin 4), corner k ∈ d.piece a → corner k ∈ d.piece b → a = b := by
    intro a b k ha hb
    by_contra hab
    exact d.unique_corner_owner_of_four_incidences hN ha b (Ne.symm hab) hb
  exact exists_configuration_of_adjacent_square_pair d hc hu hij s
    ((hs s).mpr (Or.inl rfl)) ((hs (s + 1)).mpr (Or.inr rfl)) e he heS hno

end Puzzling139335.N4Dispatch.DoublePair
