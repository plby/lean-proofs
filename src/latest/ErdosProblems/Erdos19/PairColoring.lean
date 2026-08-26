import ErdosProblems.Erdos19.PairCompletion
import Mathlib.Combinatorics.SimpleGraph.Coloring.EdgeLabeling

/-! # Transferring graph edge labels to two-element hyperedges -/

namespace Erdos19

open _root_.SimpleGraph

variable {V : Type*}

noncomputable def pairCode (e : Set V) (he : e.ncard = 2) : Sym2 V :=
  Classical.choose (show ∃ q : Sym2 V, (q : Set V) = e from by
    obtain ⟨x, y, _, hxy⟩ := Set.ncard_eq_two.mp he
    exact ⟨s(x, y), by simpa only [Sym2.coe_mk] using hxy.symm⟩)

theorem coe_pairCode (e : Set V) (he : e.ncard = 2) :
    (pairCode e he : Set V) = e := by
  unfold pairCode
  exact Classical.choose_spec (p := fun q : Sym2 V ↦ (q : Set V) = e) _

theorem pairCode_eq_pair {e : Set V} (he : e.ncard = 2) (x y : V)
    (hxy : e = {x, y}) : pairCode e he = s(x, y) := by
  apply SetLike.coe_injective
  rw [coe_pairCode, hxy, Sym2.coe_mk]

theorem exists_pair_at [Fintype V] {e : Set V} (he : e.ncard = 2) {x : V} (hx : x ∈ e) :
    ∃ y, x ≠ y ∧ e = {x, y} := by
  obtain ⟨y, hy, hyx⟩ := Set.exists_ne_of_one_lt_ncard (by omega : 1 < e.ncard) x
  exact ⟨y, hyx.symm, SetHypergraph.eq_pair_of_ncard_eq_two he hyx.symm hx hy⟩

namespace SetHypergraph

theorem pairCode_mem_twoGraph (H : SetHypergraph V) (e : H) (he : e.1.ncard = 2) :
    pairCode e.1 he ∈ H.twoGraph.edgeSet := by
  obtain ⟨x, y, hxy, hexy⟩ := Set.ncard_eq_two.mp he
  rw [pairCode_eq_pair he x y hexy]
  have hadj : H.twoGraph.Adj x y := ⟨hxy, hexy ▸ e.2⟩
  simpa only [mem_edgeSet] using hadj

noncomputable def pairLabel {K : Type*} (H : SetHypergraph V)
    (c : H.twoGraph.EdgeLabeling K) (e : H) (he : e.1.ncard = 2) : K :=
  c ⟨pairCode e.1 he, H.pairCode_mem_twoGraph e he⟩

theorem pairLabel_eq_get {K : Type*} (H : SetHypergraph V)
    (c : H.twoGraph.EdgeLabeling K) (e : H) (he : e.1.ncard = 2)
    (x y : V) (hxy : H.twoGraph.Adj x y) (hexy : e.1 = {x, y}) :
    H.pairLabel c e he = c.get x y hxy := by
  unfold pairLabel EdgeLabeling.get
  congr 1
  exact Subtype.ext (pairCode_eq_pair he x y hexy)

theorem edgeColoring_of_large_part_and_pairLabeling [Fintype V] {I K : Type*}
    (H J : SetHypergraph V) (hJH : J ⊆ H)
    (hrest : ∀ e : H, e.1 ∉ J → e.1.ncard = 2)
    (large : J.EdgeColoring I) (pairs : H.twoGraph.EdgeLabeling (I ⊕ K))
    (hpairs : ∀ x y z (hxy : H.twoGraph.Adj x y) (hxz : H.twoGraph.Adj x z),
      pairs.get x y hxy = pairs.get x z hxz → y = z)
    (havoid : ∀ e : J, ∀ x ∈ e.1, ∀ y (hxy : H.twoGraph.Adj x y),
      pairs.get x y hxy ≠ Sum.inl (large.color e)) :
    Nonempty (H.EdgeColoring (I ⊕ K)) := by
  classical
  let color : H → I ⊕ K := fun e ↦ if h : e.1 ∈ J then
    Sum.inl (large.color ⟨e.1, h⟩) else H.pairLabel pairs e (hrest e h)
  refine ⟨⟨color, ?_⟩⟩
  intro e f hef hinter hsame
  obtain ⟨x, hxe, hxf⟩ := hinter
  by_cases heJ : e.1 ∈ J <;> by_cases hfJ : f.1 ∈ J
  · have heq : large.color ⟨e.1, heJ⟩ = large.color ⟨f.1, hfJ⟩ := by
      simpa only [color, dif_pos heJ, dif_pos hfJ, Sum.inl.injEq] using hsame
    exact large.valid (fun h ↦ hef (Subtype.ext (congrArg (fun e : J ↦ e.1) h)))
      ⟨x, hxe, hxf⟩ heq
  · obtain ⟨y, hxy, hfxy⟩ := exists_pair_at (hrest f hfJ) hxf
    have hpair : H.twoGraph.Adj x y := ⟨hxy, hfxy ▸ f.2⟩
    have heq : pairs.get x y hpair = Sum.inl (large.color ⟨e.1, heJ⟩) := by
      have h := hsame.symm
      simpa only [color, dif_pos heJ, dif_neg hfJ,
        H.pairLabel_eq_get pairs f (hrest f hfJ) x y hpair hfxy] using h
    exact havoid ⟨e.1, heJ⟩ x hxe y hpair heq
  · obtain ⟨y, hxy, hexy⟩ := exists_pair_at (hrest e heJ) hxe
    have hpair : H.twoGraph.Adj x y := ⟨hxy, hexy ▸ e.2⟩
    have heq : pairs.get x y hpair = Sum.inl (large.color ⟨f.1, hfJ⟩) := by
      simpa only [color, dif_neg heJ, dif_pos hfJ,
        H.pairLabel_eq_get pairs e (hrest e heJ) x y hpair hexy] using hsame
    exact havoid ⟨f.1, hfJ⟩ x hxf y hpair heq
  · obtain ⟨y, hxy, hexy⟩ := exists_pair_at (hrest e heJ) hxe
    obtain ⟨z, hxz, hfxz⟩ := exists_pair_at (hrest f hfJ) hxf
    have hpairE : H.twoGraph.Adj x y := ⟨hxy, hexy ▸ e.2⟩
    have hpairF : H.twoGraph.Adj x z := ⟨hxz, hfxz ▸ f.2⟩
    have heq : pairs.get x y hpairE = pairs.get x z hpairF := by
      simpa only [color, dif_neg heJ, dif_neg hfJ,
        H.pairLabel_eq_get pairs e (hrest e heJ) x y hpairE hexy,
        H.pairLabel_eq_get pairs f (hrest f hfJ) x z hpairF hfxz] using hsame
    have hyz := hpairs x y z hpairE hpairF heq
    apply hef
    apply Subtype.ext
    rw [hexy, hfxz, hyz]

#print axioms edgeColoring_of_large_part_and_pairLabeling

end SetHypergraph
end Erdos19
