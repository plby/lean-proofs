import ErdosProblems.Erdos19.Core

/-! # Counting edges crossing two vertex sets

Linearity makes a pair of distinct vertices identify at most one edge.
The common-neighbor bound below only assumes a minimum rank on the family
being counted, not on the ambient hypergraph.
-/

namespace Erdos19.SetHypergraph

open Finset

variable {X : Type*} [Fintype X]

theorem card_crossing_disjoint_sets_le (H : SetHypergraph X)
    (hlinear : H.IsLinear) (A B : Set X) (hAB : Disjoint A B)
    (S : Finset H) (hA : ∀ e ∈ S, (A ∩ e.1).Nonempty)
    (hB : ∀ e ∈ S, (B ∩ e.1).Nonempty) :
    S.card ≤ A.ncard * B.ncard := by
  classical
  let a (e : S) : X := Classical.choose (hA e.1 e.2)
  let b (e : S) : X := Classical.choose (hB e.1 e.2)
  have ha (e : S) : a e ∈ A ∩ e.1.1 := Classical.choose_spec (hA e.1 e.2)
  have hb (e : S) : b e ∈ B ∩ e.1.1 := Classical.choose_spec (hB e.1 e.2)
  let code (e : S) : A × B := (⟨a e, (ha e).1⟩, ⟨b e, (hb e).1⟩)
  have hinj : Function.Injective code := by
    intro e f hef
    have haeq : a e = a f := congrArg (fun p : A × B ↦ p.1.1) hef
    have hbeq : b e = b f := congrArg (fun p : A × B ↦ p.2.1) hef
    apply Subtype.ext
    apply Subtype.ext
    by_contra hsets
    have hsub := hlinear e.1.2 f.1.2 hsets
    have hae : a e ∈ e.1.1 ∩ f.1.1 := ⟨(ha e).2, haeq ▸ (ha f).2⟩
    have hbe : b e ∈ e.1.1 ∩ f.1.1 := ⟨(hb e).2, hbeq ▸ (hb f).2⟩
    have hab := hsub hae hbe
    exact Set.disjoint_left.mp hAB (ha e).1 (hab ▸ (hb e).1)
  have hcard := Fintype.card_le_of_injective code hinj
  simpa only [Fintype.card_coe, Fintype.card_prod, Set.fintypeCard_eq_ncard] using hcard

theorem card_common_neighbors_of_disjoint_le (H : SetHypergraph X)
    (hlinear : H.IsLinear) (e f : H) (hdis : Disjoint e.1 f.1)
    (S : Finset H) (hS : ∀ g ∈ S, g ∈ H.commonNeighborEdges e f) :
    S.card ≤ e.1.ncard * f.1.ncard := by
  exact H.card_crossing_disjoint_sets_le hlinear e.1 f.1 hdis S
    (fun g hg ↦ (hS g hg).1.2) (fun g hg ↦ (hS g hg).2.2)

theorem card_common_neighbors_of_min_rank_le (H : SetHypergraph X)
    (hlinear : H.IsLinear) (e f : H) (hef : e ≠ f)
    (hinter : (e.1 ∩ f.1).Nonempty) (S : Finset H)
    (hS : ∀ g ∈ S, g ∈ H.commonNeighborEdges e f)
    (r : ℕ) (hr : 2 ≤ r) (hmin : ∀ g ∈ S, r ≤ g.1.ncard) :
    S.card ≤ (e.1.ncard - 1) * (f.1.ncard - 1) +
      (Fintype.card X - 1) / (r - 1) := by
  classical
  obtain ⟨w, hwe, hwf⟩ := hinter
  let T := S.filter fun g ↦ w ∈ g.1
  let U := S.filter fun g ↦ w ∉ g.1
  have hT : T.card ≤ (Fintype.card X - 1) / (r - 1) := by
    apply (Nat.le_div_iff_mul_le (by omega : 0 < r - 1)).2
    have hb := H.incidentSubfamily_ncard_mul_sub_one_le hlinear (T : Set H) w r
      (fun g hg ↦ (mem_filter.mp hg).2)
      (fun g hg ↦ hmin g (mem_filter.mp hg).1)
    simpa only [Set.ncard_coe_finset] using hb
  have hdis : Disjoint (e.1 \ {w}) (f.1 \ {w}) := by
    apply Set.disjoint_left.mpr
    intro x hxe hxf
    have hxw := hlinear e.2 f.2 (fun h ↦ hef (Subtype.ext h))
      ⟨hxe.1, hxf.1⟩ ⟨hwe, hwf⟩
    exact hxe.2 (by simpa using hxw)
  have hU : U.card ≤ (e.1.ncard - 1) * (f.1.ncard - 1) := by
    have hcross := H.card_crossing_disjoint_sets_le hlinear
      (e.1 \ {w}) (f.1 \ {w}) hdis U
      (by
        intro g hg
        obtain ⟨hgS, hgw⟩ := mem_filter.mp hg
        obtain ⟨x, hxe, hxg⟩ := (hS g hgS).1.2
        exact ⟨x, ⟨hxe, by simpa only [Set.mem_singleton_iff] using
          (show x ≠ w from fun hxw ↦ hgw (hxw ▸ hxg))⟩, hxg⟩)
      (by
        intro g hg
        obtain ⟨hgS, hgw⟩ := mem_filter.mp hg
        obtain ⟨x, hxf, hxg⟩ := (hS g hgS).2.2
        exact ⟨x, ⟨hxf, by simpa only [Set.mem_singleton_iff] using
          (show x ≠ w from fun hxw ↦ hgw (hxw ▸ hxg))⟩, hxg⟩)
    have hecard : (e.1 \ {w}).ncard = e.1.ncard - 1 := by
      rw [Set.ncard_sdiff (Set.singleton_subset_iff.mpr hwe), Set.ncard_singleton]
    have hfcard : (f.1 \ {w}).ncard = f.1.ncard - 1 := by
      rw [Set.ncard_sdiff (Set.singleton_subset_iff.mpr hwf), Set.ncard_singleton]
    simpa only [hecard, hfcard] using hcross
  have hsplit : T.card + U.card = S.card := card_filter_add_card_filter_not _
  omega

#print axioms card_crossing_disjoint_sets_le
#print axioms card_common_neighbors_of_min_rank_le

end Erdos19.SetHypergraph
