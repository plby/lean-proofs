/- Transport of the avoiding-packing conclusion through graph reductions. -/
import ErdosProblems.Erdos73.ContractAvoidance
import ErdosProblems.Erdos73.PackingCopy
import ErdosProblems.Erdos73.RootedPartition

namespace Erdos73Infrastructure.SimpleGraph.LinkageNormalization
open TreewidthSparsifier
variable {V I : Type*} [DecidableEq V]
variable {G H : _root_.SimpleGraph V} {A B : Finset V} {Q : I → Finset V} {k : ℕ}

def HasColumnAvoidingPacking (G : _root_.SimpleGraph V) (A B : Finset V)
    (Q : I → Finset V) (k : ℕ) : Prop :=
  ∃ i, ∃ P : PathPacking G (A \ Q i) (B \ Q i), k ≤ P.card ∧
    ∀ r, Disjoint (P.path r).vertexSet (Q i)

theorem HasColumnAvoidingPacking.mono (hGH : G ≤ H)
    (h : HasColumnAvoidingPacking G A B Q k) : HasColumnAvoidingPacking H A B Q k := by
  obtain ⟨i, P, hk, hd⟩ := h
  refine ⟨i, P.mapLe hGH, hk, fun r => ?_⟩
  change Disjoint ((P.path r).mapLe hGH).vertexSet (Q i)
  rw [GraphPath.mapLe_vertexSet]
  exact hd r

theorem HasColumnAvoidingPacking.widen {A' B' : Finset V}
    (hA : A ⊆ A') (hB : B ⊆ B') (h : HasColumnAvoidingPacking G A B Q k) :
    HasColumnAvoidingPacking G A' B' Q k := by
  obtain ⟨i, P, hk, hd⟩ := h
  exact ⟨i, P.widenTerminals (Finset.sdiff_subset_sdiff_left (Q i) hA)
    (Finset.sdiff_subset_sdiff_left (Q i) hB), hk, hd⟩

theorem hasColumnAvoidingPacking_of_disjoint (P : PathPacking G A B) (i : I)
    (hk : k ≤ P.card) (hd : ∀ r, Disjoint (P.path r).vertexSet (Q i)) :
    HasColumnAvoidingPacking G A B Q k := by
  have hs (r : P.Index) : (P.path r).source ∉ Q i :=
    fun h => Finset.disjoint_left.mp (hd r) (P.path r).source_mem_vertexSet h
  have ht (r : P.Index) : (P.path r).target ∉ Q i :=
    fun h => Finset.disjoint_left.mp (hd r) (P.path r).target_mem_vertexSet h
  let R : PathPacking G (A \ Q i) (B \ Q i) := {
    Index := P.Index
    path := P.path
    connects := by
      intro r
      rcases P.connects r with h | h
      · exact Or.inl ⟨Finset.mem_sdiff.mpr ⟨h.1, hs r⟩,
          Finset.mem_sdiff.mpr ⟨h.2, ht r⟩⟩
      · exact Or.inr ⟨Finset.mem_sdiff.mpr ⟨h.1, hs r⟩,
          Finset.mem_sdiff.mpr ⟨h.2, ht r⟩⟩
    node_disjoint := P.node_disjoint }
  exact ⟨i, R, hk, hd⟩

theorem HasColumnAvoidingPacking.of_contract {a b : V} (hab : G.Adj a b)
    (h : HasColumnAvoidingPacking (contractEdgeGraph G hab)
      (edgeContractImageSet (a := a) (b := b) A) (edgeContractImageSet B)
      (fun i => edgeContractImageSet (Q i)) k) :
    HasColumnAvoidingPacking G A B Q k := by
  obtain ⟨i, P, hk, hd⟩ := h
  obtain ⟨R, hcard, hR⟩ := exists_lift_avoiding hab A B (Q i) P hd
  exact ⟨i, R, hcard ▸ hk, hR⟩

/-- An avoiding packing in a vertex-restricted graph is one in the host. -/
theorem HasColumnAvoidingPacking.of_induce (U : Finset V)
    (hA : A ⊆ U) (hB : B ⊆ U) (hQ : ∀ i, Q i ⊆ U)
    (h : HasColumnAvoidingPacking (G.induce {x | x ∈ U})
      (PathPacking.subtypeFinset A U hA) (PathPacking.subtypeFinset B U hB)
      (fun i => PathPacking.subtypeFinset (Q i) U (hQ i)) k) :
    HasColumnAvoidingPacking G A B Q k := by
  obtain ⟨i, P, hk, hd⟩ := h
  let e : (G.induce {x | x ∈ U}).Copy G :=
    (_root_.SimpleGraph.Embedding.induce {x | x ∈ U}).toCopy
  have hsub (S : Finset V) (hS : S ⊆ U) :
      ((PathPacking.subtypeFinset S U hS \ PathPacking.subtypeFinset (Q i) U (hQ i)).map
        e.toEmbedding) ⊆ S \ Q i := by
    intro x hx
    obtain ⟨y, hy, rfl⟩ := Finset.mem_map.mp hx
    obtain ⟨hyS, hyQ⟩ := Finset.mem_sdiff.mp hy
    exact Finset.mem_sdiff.mpr
      ⟨(PathPacking.mem_subtypeFinset hS y).mp hyS,
        fun h => hyQ ((PathPacking.mem_subtypeFinset (hQ i) y).mpr h)⟩
  refine ⟨i, (P.mapCopy e).widenTerminals (hsub A hA) (hsub B hB), hk, ?_⟩
  intro r
  rw [Finset.disjoint_left]
  intro x hx hxQ
  obtain ⟨y, hy, hyx⟩ := (GraphPath.mem_mapCopy_vertexSet (P.path r) e x).mp hx
  have hyQ : y ∈ PathPacking.subtypeFinset (Q i) U (hQ i) := by
    apply (PathPacking.mem_subtypeFinset (hQ i) y).mpr
    change y.val = x at hyx
    rw [hyx]
    exact hxQ
  exact Finset.disjoint_left.mp (hd r) hy hyQ

end Erdos73Infrastructure.SimpleGraph.LinkageNormalization

namespace Erdos73Infrastructure.SimpleGraph
variable {V : Type*} [DecidableEq V] {G : _root_.SimpleGraph V}

theorem connected_finset_singleton_or_adj (Q : Finset V)
    (hQ : (G.induce {x | x ∈ Q}).Connected) (v : V) (hv : v ∈ Q) :
    Q = {v} ∨ ∃ w ∈ Q, G.Adj v w := by
  classical
  by_cases hsub : Q ⊆ {v}
  · exact Or.inl (Finset.Subset.antisymm hsub (Finset.singleton_subset_iff.mpr hv))
  · obtain ⟨w, hw, hwv⟩ := Finset.not_subset.mp hsub
    have hne : (⟨v, hv⟩ : {x // x ∈ Q}) ≠ ⟨w, hw⟩ := by
      intro h
      exact hwv (Finset.mem_singleton.mpr (congrArg Subtype.val h).symm)
    obtain ⟨p⟩ := hQ.preconnected ⟨v, hv⟩ ⟨w, hw⟩
    exact Or.inr ⟨p.snd.val, p.snd.property, p.adj_snd (p.not_nil_of_ne hne)⟩

namespace PerfectPathPacking
variable {A B : Finset V}

theorem left_subset_vertexSet (P : PerfectPathPacking G A B) :
    A ⊆ P.toPathPacking.vertexSet := by
  intro x hx
  obtain ⟨i, hi⟩ := P.source_bijective.2 ⟨x, hx⟩
  have he : (P.path i).source = x := congrArg Subtype.val hi
  exact P.toPathPacking.mem_vertexSet.mpr
    ⟨i, he ▸ (P.path i).source_mem_vertexSet⟩

theorem right_subset_vertexSet (P : PerfectPathPacking G A B) :
    B ⊆ P.toPathPacking.vertexSet := by
  intro x hx
  obtain ⟨i, hi⟩ := P.target_bijective.2 ⟨x, hx⟩
  have he : (P.path i).target = x := congrArg Subtype.val hi
  exact P.toPathPacking.mem_vertexSet.mpr
    ⟨i, he ▸ (P.path i).target_mem_vertexSet⟩

end PerfectPathPacking
end Erdos73Infrastructure.SimpleGraph
