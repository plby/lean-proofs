import StackExchange.Puzzling139335.HalfTurnRemainder.JordanUnion.ContactConnectivity
import StackExchange.Puzzling139335.HalfTurnRemainder.JordanUnion.ConnectedSubset
import StackExchange.Puzzling139335.HalfTurnRemainder.JordanUnion.FromArc

/-!
# The actual two-tile remainder is a Jordan region

Two closed Jordan regions with disjoint interiors form a Jordan region when
their union has connected interior and connected complement.  Their whole
intersection is a single nondegenerate proper Jordan crosscut, and the two
original regions are exactly its closed sides.

The contact set is not assumed connected or arc-shaped: inversion and the
Jordan crosscut theorem prove its connectedness, and a punctured planar ball
excludes a singleton.  Compact connected proper subsets of Jordan curves are
then arcs.  No finite-interface or polygonal hypothesis is needed.

The final corollary applies these facts to pieces 0 and 1 of an actual
`SquareDissection`; the two connectivity conclusions are its only additional
inputs.
-/

open Set Schoenflies

namespace Puzzling139335.HalfTurnRemainder

/-- The whole common set is one nondegenerate arc, with no such arc assumed
in the hypotheses. -/
theorem exists_inter_isArcBetween_of_connected_interior_compl
    {A D : Set Plane} (hA : IsJordanRegion A) (hD : IsJordanRegion D)
    (hdis : Disjoint (interior A) (interior D))
    (hint : IsConnected (interior (A ∪ D))) (hcompl : IsConnected (A ∪ D)ᶜ) :
    ∃ p q : Plane, IsArcBetween (A ∩ D) p q := by
  apply hA.frontier_isJordanCurve.exists_isArcBetween_compact_connected_subset
    (hA.isCompact.inter hD.isCompact)
    (isConnected_inter_of_connected_interior_compl_union hA hD hdis hint hcompl)
    (fun _ hx => (inter_subset_frontiers_of_disjoint_interiors hA hD hdis hx).1)
    (inter_ne_frontier_of_disjoint_interiors hA hD hdis)
    (inter_nontrivial_of_connected_interior_union hA hD hdis hint)

/-- Connected interior and complement recover the Jordan union and the
actual crosscut sides.  Neither the Jordan conclusion nor a connected/arc
intersection is an input. -/
theorem jordan_union_of_connected_interior_compl
    {A D : Set Plane} (hA : IsJordanRegion A) (hD : IsJordanRegion D)
    (hdis : Disjoint (interior A) (interior D))
    (hint : IsConnected (interior (A ∪ D))) (hcompl : IsConnected (A ∪ D)ᶜ) :
    IsJordanRegion (A ∪ D) ∧ ∃ p q M N,
      JordanCrosscut (frontier (A ∪ D)) (A ∩ D) p q ∧
      IsCutPair (frontier (A ∪ D)) p q M N ∧
      A = closure (inside (M ∪ (A ∩ D))) ∧
      D = closure (inside (N ∪ (A ∩ D))) := by
  obtain ⟨p, q, hI⟩ :=
    exists_inter_isArcBetween_of_connected_interior_compl hA hD hdis hint hcompl
  exact JordanUnion.glue_of_isArc_inter hA hD hdis hI.isArc hint hcompl

theorem isJordanRegion_union_of_connected_interior_compl
    {A D : Set Plane} (hA : IsJordanRegion A) (hD : IsJordanRegion D)
    (hdis : Disjoint (interior A) (interior D))
    (hint : IsConnected (interior (A ∪ D))) (hcompl : IsConnected (A ∪ D)ᶜ) :
    IsJordanRegion (A ∪ D) :=
  (jordan_union_of_connected_interior_compl hA hD hdis hint hcompl).1

theorem exists_jordanCrosscut_inter_of_connected_interior_compl
    {A D : Set Plane} (hA : IsJordanRegion A) (hD : IsJordanRegion D)
    (hdis : Disjoint (interior A) (interior D))
    (hint : IsConnected (interior (A ∪ D))) (hcompl : IsConnected (A ∪ D)ᶜ) :
    ∃ p q M N,
      JordanCrosscut (frontier (A ∪ D)) (A ∩ D) p q ∧
      IsCutPair (frontier (A ∪ D)) p q M N ∧
      A = closure (inside (M ∪ (A ∩ D))) ∧
      D = closure (inside (N ∪ (A ∩ D))) :=
  (jordan_union_of_connected_interior_compl hA hD hdis hint hcompl).2

end Puzzling139335.HalfTurnRemainder

namespace Puzzling139335.SquareDissection

/-- The topological conclusion for the actual retained pieces of a square
dissection, using only the two separately proved connectivity conclusions. -/
theorem pair_remainder_jordan_of_connected (d : SquareDissection)
    (hint : IsConnected (interior (d.piece 0 ∪ d.piece 1)))
    (hcompl : IsConnected (d.piece 0 ∪ d.piece 1)ᶜ) :
    IsJordanRegion (d.piece 0 ∪ d.piece 1) ∧ ∃ p q M N,
      JordanCrosscut (frontier (d.piece 0 ∪ d.piece 1))
        (d.piece 0 ∩ d.piece 1) p q ∧
      IsCutPair (frontier (d.piece 0 ∪ d.piece 1)) p q M N ∧
      d.piece 0 = closure (inside (M ∪ (d.piece 0 ∩ d.piece 1))) ∧
      d.piece 1 = closure (inside (N ∪ (d.piece 0 ∩ d.piece 1))) :=
  HalfTurnRemainder.jordan_union_of_connected_interior_compl
    (d.jordan 0) (d.jordan 1) (d.disjoint_interiors (by decide)) hint hcompl

end Puzzling139335.SquareDissection
