import StackExchange.Puzzling139335.JordanTransport

/-!
# Jordan curves interchanged by a plane homeomorphism

Two disjoint Jordan curves whose bounded regions meet must be nested.  A plane
homeomorphism interchanging the curves cannot preserve such a strict nesting.
We prove the needed obstruction directly from connectedness of the two Jordan
regions, unboundedness of the exterior, and the frontier identities.
-/

open Set

namespace Schoenflies

namespace IsSeparating

/-- A connected set missing a Jordan curve lies wholly in its inside or outside. -/
theorem subset_inside_or_outside_of_isConnected {C S : Set Plane}
    (hC : IsSeparating C) (hS : IsConnected S) (hdis : Disjoint S C) :
    S ⊆ inside C ∨ S ⊆ outside C := by
  obtain ⟨W, V, hpair, hsub⟩ :=
    hC.exists_isRegionPair_subset hS.isPreconnected hS.nonempty hdis
  rcases hpair with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact Or.inl hsub
  · exact Or.inr hsub

/-- An exterior which misses a second Jordan curve lies in its exterior:
the alternative would make an unbounded set bounded. -/
theorem outside_subset_outside_of_disjoint {C D : Set Plane}
    (hC : IsSeparating C) (hD : IsSeparating D)
    (hdis : Disjoint (outside C) D) : outside C ⊆ outside D := by
  rcases hD.subset_inside_or_outside_of_isConnected hC.isConnected_outside hdis with
    hinside | houtside
  · exact False.elim (hC.not_isBounded_outside (hD.isBounded_inside.subset hinside))
  · exact houtside

/-- Two Jordan curves cannot each lie in the bounded region of the other. -/
theorem not_mutual_curve_subset_inside {C D : Set Plane}
    (hC : IsSeparating C) (hD : IsSeparating D)
    (hCD : C ⊆ inside D) (hDC : D ⊆ inside C) : False := by
  have hdis : Disjoint (outside C) D :=
    disjoint_inside_outside.symm.mono_right hDC
  have hout := hC.outside_subset_outside_of_disjoint hD hdis
  have habs := hC.absorption hD (IsRegionOf.outside C) (IsRegionOf.outside D) hout
  obtain ⟨x, hx⟩ := hC.isJordanCurve.nonempty
  exact disjoint_left.1 disjoint_inside_outside (hCD hx)
    (habs ⟨hx, inside_subset_compl (hCD hx)⟩)

end IsSeparating

namespace IsJordanCurve

/-- A plane homeomorphism cannot interchange disjoint Jordan curves whose
bounded regions meet.  In particular this applies to a centrally symmetric
curve and its quarter-turn image. -/
theorem not_disjoint_image_of_image_image_eq {C : Set Plane}
    (hC : IsJordanCurve C) (e : Plane ≃ₜ Plane)
    (hperiod : e '' (e '' C) = C)
    (hcommon : (inside C ∩ inside (e '' C)).Nonempty) :
    ¬ Disjoint C (e '' C) := by
  have hsepC := jordan_curve_theorem hC
  have hsepD := jordan_curve_theorem (hC.image_homeomorph e)
  intro hdis
  rcases hsepD.subset_inside_or_outside_of_isConnected hC.isConnected hdis with
    hinside | houtside
  · have hreverse : e '' C ⊆ inside C := by
      calc
        e '' C ⊆ e '' inside (e '' C) := image_mono hinside
        _ = inside C := by rw [homeomorph_image_inside, hperiod]
    exact hsepC.not_mutual_curve_subset_inside hsepD hinside hreverse
  · have hreverse : e '' C ⊆ outside C := by
      calc
        e '' C ⊆ e '' outside (e '' C) := image_mono houtside
        _ = outside C := by rw [homeomorph_image_outside, hperiod]
    have hinside_dis : Disjoint (inside C) (e '' C) :=
      disjoint_inside_outside.mono_right hreverse
    have hcover : inside C ⊆ inside (e '' C) ∪ outside (e '' C) := by
      rw [inside_union_outside]
      intro x hx
      exact disjoint_left.1 hinside_dis hx
    have hsub : inside C ⊆ inside (e '' C) :=
      hsepC.isConnected_inside.isPreconnected.subset_left_of_subset_union
        hsepD.isOpen_inside hsepD.isOpen_outside disjoint_inside_outside hcover hcommon
    have habs := hsepC.absorption hsepD (IsRegionOf.inside C)
      (IsRegionOf.inside (e '' C)) hsub
    obtain ⟨x, hx⟩ := hC.nonempty
    exact disjoint_left.1 disjoint_inside_outside
      (habs ⟨hx, disjoint_left.1 hdis hx⟩) (houtside hx)

/-- Fixed-center form of the nesting obstruction. -/
theorem not_disjoint_image_of_fixed_mem_inside {C : Set Plane} {c : Plane}
    (hC : IsJordanCurve C) (e : Plane ≃ₜ Plane)
    (hperiod : e '' (e '' C) = C) (hc : c ∈ inside C) (hfix : e c = c) :
    ¬ Disjoint C (e '' C) := by
  apply hC.not_disjoint_image_of_image_image_eq e hperiod
  refine ⟨c, hc, ?_⟩
  simpa only [hfix] using (homeomorph_mem_inside_iff e).2 hc

end IsJordanCurve

end Schoenflies
