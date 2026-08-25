import StackExchange.Puzzling139335.JordanSubarc
import Wikipedia.SchoenfliesTheorem.RealizeSubdiv

/-!
# Maximal boundary arcs between a fixed vertex set

Two arcs on one Jordan curve whose endpoints belong to a fixed vertex set
and whose interiors avoid that set agree whenever they share a nonvertex
point.  This identifies the two copies of each interface arc.
-/

open Set

namespace Schoenflies

theorem IsCutPair.connected_subset_fst_of_avoids_endpoints
    {C A B Q : Set Plane} {p q x : Plane} (hcut : IsCutPair C p q A B)
    (hQ : IsPreconnected Q) (hQC : Q ⊆ C)
    (havoid : Disjoint Q ({p, q} : Set Plane)) (hxQ : x ∈ Q) (hxA : x ∈ A) :
    Q ⊆ A := by
  have hxB : x ∉ B := by
    intro hxB
    exact Set.disjoint_left.mp havoid hxQ (hcut.inter_eq ▸ ⟨hxA, hxB⟩)
  have hcover : Q ⊆ Aᶜ ∪ Bᶜ := by
    intro y hy
    by_cases hyA : y ∈ A
    · exact Or.inr (fun hyB => Set.disjoint_left.mp havoid hy
        (hcut.inter_eq ▸ ⟨hyA, hyB⟩))
    · exact Or.inl hyA
  intro y hy
  by_contra hyA
  obtain ⟨z, hzQ, hzA, hzB⟩ := hQ Aᶜ Bᶜ
    hcut.fst.isArc.isClosed.isOpen_compl hcut.snd.isArc.isClosed.isOpen_compl
    hcover ⟨y, hy, hyA⟩ ⟨x, hxQ, hxB⟩
  have hzC := hQC hzQ
  rw [← hcut.union_eq] at hzC
  exact hzC.elim hzA hzB

private theorem arc_subset_of_open_arc_avoids_vertices
    {C A B E : Set Plane} {a b c d x : Plane}
    (hC : IsJordanCurve C) (hA : IsArcBetween A a b) (hB : IsArcBetween B c d)
    (hAC : A ⊆ C) (hBC : B ⊆ C) (ha : a ∈ E) (hb : b ∈ E)
    (hBavoid : Disjoint (B \ {c, d}) E) (hxB : x ∈ B \ {c, d}) (hxA : x ∈ A) :
    B ⊆ A := by
  obtain ⟨A', hcut⟩ := hC.exists_cutPair_of_subset_arc hA hAC
  have havoid : Disjoint (B \ {c, d}) ({a, b} : Set Plane) :=
    hBavoid.mono_right (pair_subset ha hb)
  have hsub : B \ {c, d} ⊆ A :=
    hcut.connected_subset_fst_of_avoids_endpoints hB.isPreconnected_diff
      (fun _ hx => hBC hx.1) havoid hxB hxA
  have hclosure := closure_mono hsub
  rwa [hB.closure_diff_eq, hA.isArc.isClosed.closure_eq] at hclosure

/-- Two maximal arcs between a common vertex set cannot overlap away from
that set without being the same arc. -/
theorem IsJordanCurve.arc_eq_of_common_point_off_vertices
    {C A B E : Set Plane} {a b c d x : Plane}
    (hC : IsJordanCurve C) (hA : IsArcBetween A a b) (hB : IsArcBetween B c d)
    (hAC : A ⊆ C) (hBC : B ⊆ C)
    (ha : a ∈ E) (hb : b ∈ E) (hc : c ∈ E) (hd : d ∈ E)
    (hAavoid : Disjoint (A \ {a, b}) E) (hBavoid : Disjoint (B \ {c, d}) E)
    (hxA : x ∈ A) (hxB : x ∈ B) (hxnot : x ∉ E) : A = B := by
  have hxAo : x ∈ A \ {a, b} := by
    refine ⟨hxA, ?_⟩
    rintro (rfl | rfl)
    exacts [hxnot ha, hxnot hb]
  have hxBo : x ∈ B \ {c, d} := by
    refine ⟨hxB, ?_⟩
    rintro (rfl | rfl)
    exacts [hxnot hc, hxnot hd]
  exact Subset.antisymm
    (arc_subset_of_open_arc_avoids_vertices hC hB hA hBC hAC hc hd hAavoid hxAo hxB)
    (arc_subset_of_open_arc_avoids_vertices hC hA hB hAC hBC ha hb hBavoid hxBo hxA)

end Schoenflies
