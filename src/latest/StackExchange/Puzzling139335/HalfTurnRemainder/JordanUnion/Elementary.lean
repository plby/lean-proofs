import StackExchange.Puzzling139335.JordanCurveRigidity
import Wikipedia.SchoenfliesTheorem.SkeletonAccess

/-!
# The contact set of two Jordan regions

The common set lies on both boundaries and is a proper subset of each.
Connectedness of the union's interior excludes both an empty contact set
and a single contact point.  The latter uses a punctured planar ball.
-/

open Set Schoenflies Metric

namespace Puzzling139335.HalfTurnRemainder

theorem inter_subset_frontiers_of_disjoint_interiors
    {A D : Set Plane} (hA : IsJordanRegion A) (hD : IsJordanRegion D)
    (hdis : Disjoint (interior A) (interior D)) :
    A ∩ D ⊆ frontier A ∩ frontier D := by
  intro x hx
  constructor
  · exact ⟨subset_closure hx.1,
      fun hxint => Set.disjoint_left.mp (hD.disjoint_interior_left hdis) hxint hx.2⟩
  · exact ⟨subset_closure hx.2,
      fun hxint => Set.disjoint_left.mp (hA.disjoint_interior_left hdis.symm) hxint hx.1⟩

theorem inter_ne_frontier_of_disjoint_interiors
    {A D : Set Plane} (hA : IsJordanRegion A) (hD : IsJordanRegion D)
    (hdis : Disjoint (interior A) (interior D)) :
    A ∩ D ≠ frontier A := by
  intro heq
  have hfront : frontier A ⊆ frontier D := by
    intro x hx
    exact (inter_subset_frontiers_of_disjoint_interiors hA hD hdis (heq.symm ▸ hx)).2
  have hAD : A = D := hA.eq_of_frontier_subset hD hfront
  obtain ⟨x, hx⟩ := hA.interior_nonempty
  exact Set.disjoint_left.mp hdis hx (hAD ▸ hx)

theorem inter_nonempty_of_connected_interior_union
    {A D : Set Plane} (hA : IsJordanRegion A) (hD : IsJordanRegion D)
    (hconn : IsConnected (interior (A ∪ D))) : (A ∩ D).Nonempty := by
  by_contra hnone
  have hcover : interior (A ∪ D) ⊆ Aᶜ ∪ Dᶜ := by
    intro x _
    by_cases hxA : x ∈ A
    · exact Or.inr (fun hxD => hnone ⟨x, hxA, hxD⟩)
    · exact Or.inl hxA
  obtain ⟨a, ha⟩ := hA.interior_nonempty
  obtain ⟨d, hd⟩ := hD.interior_nonempty
  obtain ⟨x, hx, hxA, hxD⟩ := hconn.isPreconnected Aᶜ Dᶜ
    hA.isClosed.isOpen_compl hD.isClosed.isOpen_compl hcover
    ⟨d, interior_mono subset_union_right hd,
      fun hdA => hnone ⟨d, hdA, interior_subset hd⟩⟩
    ⟨a, interior_mono subset_union_left ha,
      fun haD => hnone ⟨a, interior_subset ha, haD⟩⟩
  exact (interior_subset hx).elim hxA hxD

private theorem interior_union_sdiff_singleton_subset
    {A D : Set Plane} {p : Plane} (hA : IsClosed A) (hD : IsClosed D)
    (hcontact : A ∩ D ⊆ {p}) :
    interior (A ∪ D) \ {p} ⊆ interior A ∪ interior D := by
  have hleft : interior (A ∪ D) ∩ Dᶜ ⊆ interior A := by
    apply interior_maximal _ (isOpen_interior.inter hD.isOpen_compl)
    intro x hx
    exact (interior_subset hx.1).resolve_right hx.2
  have hright : interior (A ∪ D) ∩ Aᶜ ⊆ interior D := by
    apply interior_maximal _ (isOpen_interior.inter hA.isOpen_compl)
    intro x hx
    exact (interior_subset hx.1).resolve_left hx.2
  intro x hx
  rcases interior_subset hx.1 with hxA | hxD
  · exact Or.inl (hleft ⟨hx.1, fun hxD => hx.2 (hcontact ⟨hxA, hxD⟩)⟩)
  · exact Or.inr (hright ⟨hx.1, fun hxA => hx.2 (hcontact ⟨hxA, hxD⟩)⟩)

/-- A singleton seam cannot connect two nonempty planar interiors. -/
theorem inter_nontrivial_of_connected_interior_union
    {A D : Set Plane} (hA : IsJordanRegion A) (hD : IsJordanRegion D)
    (hdis : Disjoint (interior A) (interior D))
    (hconn : IsConnected (interior (A ∪ D))) : (A ∩ D).Nontrivial := by
  obtain ⟨p, hp⟩ := inter_nonempty_of_connected_interior_union hA hD hconn
  by_contra hnontrivial
  have hcontact : A ∩ D ⊆ {p} := by
    intro x hx
    by_contra hxnot
    exact hnontrivial ⟨p, hp, x, hx, fun hpx => hxnot (mem_singleton_iff.mpr hpx.symm)⟩
  have hcover := interior_union_sdiff_singleton_subset hA.isClosed hD.isClosed hcontact
  have hpfront := inter_subset_frontiers_of_disjoint_interiors hA hD hdis hp
  by_cases hpU : p ∈ interior (A ∪ D)
  · obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp isOpen_interior p hpU
    have hcoverball : ball p r \ {p} ⊆ interior A ∪ interior D :=
      fun x hx => hcover ⟨hball hx.1, hx.2⟩
    have hpA : p ∈ closure (interior A) := hA.closure_interior.symm ▸ hp.1
    have hpD : p ∈ closure (interior D) := hD.closure_interior.symm ▸ hp.2
    obtain ⟨a, ha, hpa⟩ := Metric.mem_closure_iff.mp hpA r hr
    obtain ⟨d, hd, hpd⟩ := Metric.mem_closure_iff.mp hpD r hr
    have haBall : a ∈ ball p r \ {p} := by
      refine ⟨by simpa only [mem_ball, dist_comm] using hpa, ?_⟩
      rintro rfl
      exact hpfront.1.2 ha
    have hdBall : d ∈ ball p r \ {p} := by
      refine ⟨by simpa only [mem_ball, dist_comm] using hpd, ?_⟩
      rintro rfl
      exact hpfront.2.2 hd
    rcases (isConnected_ball_diff_singleton hr).isPreconnected.subset_or_subset
        isOpen_interior isOpen_interior hdis hcoverball with hleft | hright
    · exact Set.disjoint_left.mp hdis (hleft hdBall) hd
    · exact Set.disjoint_left.mp hdis ha (hright haBall)
  · have hcoverall : interior (A ∪ D) ⊆ interior A ∪ interior D := by
      intro x hx
      apply hcover
      refine ⟨hx, ?_⟩
      rintro rfl
      exact hpU hx
    rcases hconn.isPreconnected.subset_or_subset
        isOpen_interior isOpen_interior hdis hcoverall with hleft | hright
    · obtain ⟨d, hd⟩ := hD.interior_nonempty
      exact Set.disjoint_left.mp hdis (hleft (interior_mono subset_union_right hd)) hd
    · obtain ⟨a, ha⟩ := hA.interior_nonempty
      exact Set.disjoint_left.mp hdis ha (hright (interior_mono subset_union_left ha))

end Puzzling139335.HalfTurnRemainder
