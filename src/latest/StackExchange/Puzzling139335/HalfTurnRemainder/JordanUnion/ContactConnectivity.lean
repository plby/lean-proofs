import StackExchange.Puzzling139335.HalfTurnRemainder.JordanUnion.Elementary
import StackExchange.Puzzling139335.HalfTurnRemainder.JordanUnion.Inversion
import StackExchange.Puzzling139335.HalfTurnRemainder.JordanUnion.Nested

/-!
# Connected complement forces connected contacts

Invert about an interior point of the first Jordan region.  Its exterior,
with infinity added, is a Jordan disk.  A simple interior access arc in the
second region becomes a crosscut of that disk.  The connected remainder
forces one complete outer boundary arc into the second region.  Inverting
back joins any two contact points within the contact set itself.

This argument does not need finite interfaces or an Euler formula.
-/

open Set Schoenflies

namespace Puzzling139335.HalfTurnRemainder

/-- Every two different contact points can be joined within the contact set,
provided the complement of the union is connected. -/
theorem exists_contact_arc_of_connected_compl_union
    {A D : Set Plane} {p q : Plane}
    (hA : IsJordanRegion A) (hD : IsJordanRegion D)
    (hdis : Disjoint (interior A) (interior D))
    (hconn : IsConnected (A ∪ D)ᶜ)
    (hp : p ∈ A ∩ D) (hq : q ∈ A ∩ D) (hpq : p ≠ q) :
    ∃ T : Set Plane, IsArcBetween T p q ∧ T ⊆ A ∩ D := by
  obtain ⟨a, ha⟩ := hA.interior_nonempty
  have haD : a ∉ D :=
    fun haD => Set.disjoint_left.mp (hD.disjoint_interior_left hdis) ha haD
  have haC : a ∉ frontier A := fun haC => haC.2 ha
  have hpfront := inter_subset_frontiers_of_disjoint_interiors hA hD hdis hp
  have hqfront := inter_subset_frontiers_of_disjoint_interiors hA hD hdis hq
  obtain ⟨P, hP, hPint, hPD⟩ :=
    exists_arc_between_frontier_through_interior hD hpfront.2 hqfront.2 hpq
  have hP' := hP.invert_image (fun haP => haD (hPD haP))
  have hC' := hA.frontier_isJordanCurve.invert_image haC
  have hX : JordanCrosscut (invert a '' frontier A) (invert a '' P)
      (invert a p) (invert a q) := by
    refine ⟨hC', hP', mem_image_of_mem _ hpfront.1,
      mem_image_of_mem _ hqfront.1, ?_⟩
    rintro x ⟨⟨y, hy, rfl⟩, hends⟩
    apply invert_interior_subset_inside_of_disjoint hA hdis ha
    refine ⟨y, hPint ⟨hy, ?_⟩, rfl⟩
    rintro (rfl | rfl)
    · exact hends (Or.inl rfl)
    · exact hends (Or.inr rfl)
  obtain ⟨M, N, hcut⟩ := exists_isCutPair hC'
    (mem_image_of_mem _ hpfront.1) (mem_image_of_mem _ hqfront.1)
    ((invert_injective a).ne hpq)
  have hDclosed : IsClosed (invert a '' D) :=
    (isCompact_invert_image hD.isCompact haD).isClosed
  have hrem := isConnected_inside_invert_frontier_sdiff_image hA hD.isCompact ha haD hconn
  have htransport (R : Set Plane)
      (hR : IsArcBetween R (invert a p) (invert a q))
      (hRA : R ⊆ invert a '' frontier A) (hRD : R ⊆ invert a '' D) :
      ∃ T : Set Plane, IsArcBetween T p q ∧ T ⊆ A ∩ D := by
    have haR : a ∉ R := fun haR => notMem_invert_image haC (hRA haR)
    refine ⟨invert a '' R, ?_, ?_⟩
    · simpa only [invert_invert] using hR.invert_image haR
    · rintro x ⟨y, hy, rfl⟩
      obtain ⟨z, hz, hzy⟩ := hRA hy
      obtain ⟨w, hw, hwy⟩ := hRD hy
      constructor
      · rw [← hzy, invert_invert]
        exact hA.isClosed.closure_eq ▸ hz.1
      · rw [← hwy, invert_invert]
        exact hw
  rcases outer_arc_subset_of_connected_remainder hX hcut hDclosed
      (image_mono hPD) hrem.isPreconnected with hMD | hND
  · exact htransport M hcut.fst hcut.fst_subset hMD
  · exact htransport N hcut.snd hcut.snd_subset hND

/-- The contact set of two disjoint-interior Jordan regions is preconnected
whenever their union has connected complement. -/
theorem isPreconnected_inter_of_connected_compl_union
    {A D : Set Plane} (hA : IsJordanRegion A) (hD : IsJordanRegion D)
    (hdis : Disjoint (interior A) (interior D))
    (hconn : IsConnected (A ∪ D)ᶜ) : IsPreconnected (A ∩ D) := by
  apply isPreconnected_of_forall_pair
  intro p hp q hq
  by_cases hpq : p = q
  · subst q
    exact ⟨{p}, singleton_subset_iff.mpr hp, rfl, rfl, isPreconnected_singleton⟩
  · obtain ⟨T, hT, hTsub⟩ :=
      exists_contact_arc_of_connected_compl_union hA hD hdis hconn hp hq hpq
    exact ⟨T, hTsub, hT.left_mem, hT.right_mem, hT.isArc.isConnected.isPreconnected⟩

theorem isConnected_inter_of_connected_interior_compl_union
    {A D : Set Plane} (hA : IsJordanRegion A) (hD : IsJordanRegion D)
    (hdis : Disjoint (interior A) (interior D))
    (hint : IsConnected (interior (A ∪ D))) (hcompl : IsConnected (A ∪ D)ᶜ) :
    IsConnected (A ∩ D) :=
  ⟨inter_nonempty_of_connected_interior_union hA hD hint,
    isPreconnected_inter_of_connected_compl_union hA hD hdis hcompl⟩

end Puzzling139335.HalfTurnRemainder
