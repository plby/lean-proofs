import ErdosProblems.Erdos19.PairColoring
import ErdosProblems.Erdos19.GraphMatching

/-! # A disjoint matching family as a colored pair hypergraph -/

namespace Erdos19

open _root_.SimpleGraph

variable {V I : Type*} {G : _root_.SimpleGraph V}

def matchingEdges (M : G.Subgraph) : SetHypergraph V :=
  {e | ∃ x y, M.Adj x y ∧ e = {x, y}}

theorem matchingEdges_pair_iff (M : G.Subgraph) (x y : V) :
    ({x, y} : Set V) ∈ matchingEdges M ↔ M.Adj x y := by
  constructor
  · rintro ⟨u, v, huv, heq⟩
    rcases Set.pair_eq_pair_iff.mp heq with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact huv
    · exact huv.symm
  · intro h
    exact ⟨x, y, h, rfl⟩

theorem matchingEdges_size (M : G.Subgraph) {e : Set V} (he : e ∈ matchingEdges M) :
    e.ncard = 2 := by
  obtain ⟨x, y, hxy, rfl⟩ := he
  exact Set.ncard_pair hxy.adj_sub.ne

theorem matchingEdges_vertex_mem (M : G.Subgraph) {e : Set V}
    (he : e ∈ matchingEdges M) {v : V} (hv : v ∈ e) : v ∈ M.verts := by
  obtain ⟨x, y, hxy, rfl⟩ := he
  rcases hv with rfl | rfl
  · exact hxy.fst_mem
  · exact hxy.snd_mem

theorem matchingEdges_intersect_eq [Fintype V] (M : G.Subgraph) (hM : M.IsMatching)
    {e f : Set V} (he : e ∈ matchingEdges M) (hf : f ∈ matchingEdges M)
    (hinter : (e ∩ f).Nonempty) : e = f := by
  obtain ⟨v, hve, hvf⟩ := hinter
  obtain ⟨x, _, hex⟩ := exists_pair_at (matchingEdges_size M he) hve
  obtain ⟨y, _, hfy⟩ := exists_pair_at (matchingEdges_size M hf) hvf
  have hx : M.Adj v x := (matchingEdges_pair_iff M v x).mp (hex ▸ he)
  have hy : M.Adj v y := (matchingEdges_pair_iff M v y).mp (hfy ▸ hf)
  have hxy := hM.eq_of_adj_left hx hy
  rw [hex, hfy, hxy]

def matchingFamilyHypergraph (M : I → G.Subgraph) : SetHypergraph V :=
  ⋃ i, matchingEdges (M i)

theorem matchingFamily_pair_iff (M : I → G.Subgraph) (x y : V) :
    ({x, y} : Set V) ∈ matchingFamilyHypergraph M ↔ ∃ i, (M i).Adj x y := by
  simp only [matchingFamilyHypergraph, Set.mem_iUnion, matchingEdges_pair_iff]

theorem matchingFamily_twoGraph (M : I → G.Subgraph) :
    (matchingFamilyHypergraph M).twoGraph = ⨆ i, (M i).spanningCoe := by
  ext x y
  rw [SetHypergraph.twoGraph_adj, matchingFamily_pair_iff, iSup_adj]
  constructor
  · exact fun h ↦ h.2
  · rintro ⟨i, hi⟩
    exact ⟨hi.adj_sub.ne, i, hi⟩

theorem matchingFamily_subset (H : SetHypergraph V) (M : I → H.twoGraph.Subgraph) :
    matchingFamilyHypergraph M ⊆ H := by
  intro e he
  obtain ⟨i, hi⟩ := Set.mem_iUnion.mp he
  obtain ⟨x, y, hxy, rfl⟩ := hi
  exact hxy.adj_sub.2

theorem matchingFamily_disjoint_of_graph_disjoint (J : SetHypergraph V)
    (M : I → G.Subgraph) (hdis : Disjoint J.twoGraph (⨆ i, (M i).spanningCoe)) :
    Disjoint J (matchingFamilyHypergraph M) := by
  apply Set.disjoint_left.mpr
  intro e heJ heM
  obtain ⟨i, hi⟩ := Set.mem_iUnion.mp heM
  obtain ⟨x, y, hxy, rfl⟩ := hi
  exact _root_.SimpleGraph.disjoint_left.mp hdis x y ⟨hxy.adj_sub.ne, heJ⟩
    (iSup_adj.mpr ⟨i, hxy⟩)

theorem exists_matching_family_hypergraph_coloring [Fintype V]
    (M : I → G.Subgraph) (hM : ∀ i, (M i).IsMatching)
    (hdis : Pairwise fun i j ↦ Disjoint (M i).spanningCoe (M j).spanningCoe) :
    ∃ c : (matchingFamilyHypergraph M).EdgeColoring I,
      (∀ (e : matchingFamilyHypergraph M) i, e.1 ∈ matchingEdges (M i) → c e = i) ∧
      (∀ i, (matchingFamilyHypergraph M).coveredVertices {e | c e = i} = (M i).verts) := by
  classical
  let H := matchingFamilyHypergraph M
  have hex (e : H) : ∃ i, e.1 ∈ matchingEdges (M i) := Set.mem_iUnion.mp e.2
  choose color hcolor using hex
  have hproper : ∀ {e f : H}, e ≠ f → (e.1 ∩ f.1).Nonempty → color e ≠ color f := by
    intro e f hef hinter heq
    apply hef
    apply Subtype.ext
    apply matchingEdges_intersect_eq (M (color e)) (hM _) (hcolor e) _ hinter
    simpa only [heq] using hcolor f
  let c : H.EdgeColoring I := ⟨color, @hproper⟩
  have hindex (e : H) (i : I) (he : e.1 ∈ matchingEdges (M i)) : c e = i := by
    by_contra hne
    obtain ⟨x, y, hxy, hexy⟩ := he
    have hother : (M (c e)).Adj x y := (matchingEdges_pair_iff _ x y).mp (hexy ▸ hcolor e)
    exact _root_.SimpleGraph.disjoint_left.mp (hdis hne) x y hother hxy
  refine ⟨c, hindex, ?_⟩
  intro i
  ext v
  constructor
  · intro hv
    obtain ⟨e, he⟩ := Set.mem_iUnion.mp hv
    obtain ⟨hei, hve⟩ := Set.mem_iUnion.mp he
    have heM : e.1 ∈ matchingEdges (M i) := by
      simpa only [show color e = i from hei] using hcolor e
    exact matchingEdges_vertex_mem _ heM hve
  · intro hv
    obtain ⟨w, hvw, _⟩ := hM i hv
    have heM : ({v, w} : Set V) ∈ matchingEdges (M i) :=
      (matchingEdges_pair_iff _ v w).mpr hvw
    let e : H := ⟨{v, w}, Set.mem_iUnion.mpr ⟨i, heM⟩⟩
    exact Set.mem_iUnion.mpr ⟨e, Set.mem_iUnion.mpr ⟨hindex e i heM, Or.inl rfl⟩⟩

#print axioms exists_matching_family_hypergraph_coloring

end Erdos19
