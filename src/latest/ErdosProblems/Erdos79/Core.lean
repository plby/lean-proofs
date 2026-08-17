/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import Util.Ramsey

/-!
# Finite-graph and Ramsey foundations for Erdős Problem 79

The problem concerns ordinary (not necessarily induced) subgraphs.  To quantify over finite
graphs without carrying a vertex type and a `Fintype` instance everywhere, we use canonical
codes: a graph with `n` vertices is represented by a simple graph on `Fin n`.

`RamseyAt F H N` says that every red/blue colouring of the edges of `K_N` has a red copy of
`F` or a blue copy of `H`.  A colouring is represented by its red graph `C`; its blue graph is
then `Cᶜ`.  Thus the definition is the usual (non-induced) graph Ramsey property.
-/

open scoped SimpleGraph

noncomputable section

namespace Erdos79

/-- A canonical code for a finite simple graph: the first component is the number of vertices
and the second is a graph on `Fin` of that number. -/
abbrev GraphCode := Σ n : ℕ, SimpleGraph (Fin n)

namespace GraphCode

/-- The number of vertices of a coded graph. -/
abbrev vertexCount (G : GraphCode) : ℕ := G.1

/-- The simple graph carried by a code. -/
abbrev graph (G : GraphCode) : SimpleGraph (Fin G.vertexCount) := G.2

/-- The number of (unordered) edges of a coded graph. -/
noncomputable def edgeCount (G : GraphCode) : ℕ :=
  Nat.card G.graph.edgeSet

@[simp] theorem vertexCount_mk (n : ℕ) (G : SimpleGraph (Fin n)) :
    GraphCode.vertexCount (⟨n, G⟩ : GraphCode) = n := rfl

@[simp] theorem graph_mk (n : ℕ) (G : SimpleGraph (Fin n)) :
    GraphCode.graph (⟨n, G⟩ : GraphCode) = G := rfl

@[simp] theorem edgeCount_mk (n : ℕ) (G : SimpleGraph (Fin n)) :
    GraphCode.edgeCount (⟨n, G⟩ : GraphCode) = Nat.card G.edgeSet := rfl

/-- On choosing a decidable adjacency relation, `edgeCount` is the cardinality of Mathlib's
finite edge set. -/
theorem edgeCount_eq_card_edgeFinset (G : GraphCode) [DecidableRel G.graph.Adj] :
    G.edgeCount = G.graph.edgeFinset.card := by
  rw [edgeCount, Nat.card_eq_fintype_card, SimpleGraph.card_edgeSet]

end GraphCode

/-- Ordinary, non-induced containment of coded finite graphs.  `IsContained F G` means that
`G` has a (not necessarily induced) subgraph isomorphic to `F`. -/
abbrev IsContained (F G : GraphCode) : Prop := F.graph ⊑ G.graph

/-- Isomorphism of coded finite graphs. -/
abbrev Isomorphic (F G : GraphCode) : Prop := Nonempty (F.graph ≃g G.graph)

namespace IsContained

@[refl] theorem refl (G : GraphCode) : IsContained G G :=
  SimpleGraph.IsContained.refl G.graph

theorem rfl {G : GraphCode} : IsContained G G := refl G

@[trans] theorem trans {F G H : GraphCode} (hFG : IsContained F G)
    (hGH : IsContained G H) : IsContained F H :=
  SimpleGraph.IsContained.trans hFG hGH

/-- Containment cannot decrease the number of available vertices. -/
theorem vertexCount_le {F G : GraphCode} (h : IsContained F G) :
    F.vertexCount ≤ G.vertexCount := by
  rcases h with ⟨f⟩
  simpa using Fintype.card_le_of_embedding f.toEmbedding

/-- Containment cannot decrease the number of edges. -/
theorem edgeCount_le {F G : GraphCode} (h : IsContained F G) :
    F.edgeCount ≤ G.edgeCount := by
  rcases h with ⟨f⟩
  exact Finite.card_le_of_embedding f.mapEdgeSet

end IsContained

namespace Isomorphic

@[refl] theorem refl (G : GraphCode) : Isomorphic G G :=
  ⟨SimpleGraph.Iso.refl⟩

theorem rfl {G : GraphCode} : Isomorphic G G := refl G

@[symm] theorem symm {F G : GraphCode} (h : Isomorphic F G) : Isomorphic G F := by
  rcases h with ⟨e⟩
  exact ⟨e.symm⟩

@[trans] theorem trans {F G H : GraphCode} (hFG : Isomorphic F G)
    (hGH : Isomorphic G H) : Isomorphic F H := by
  rcases hFG with ⟨eFG⟩
  rcases hGH with ⟨eGH⟩
  exact ⟨eGH.comp eFG⟩

theorem isContained {F G : GraphCode} (h : Isomorphic F G) : IsContained F G := by
  rcases h with ⟨e⟩
  exact e.isContained

theorem isContained' {F G : GraphCode} (h : Isomorphic F G) : IsContained G F :=
  h.symm.isContained

/-- Isomorphic coded graphs have the same number of vertices. -/
theorem vertexCount_eq {F G : GraphCode} (h : Isomorphic F G) :
    F.vertexCount = G.vertexCount := by
  rcases h with ⟨e⟩
  simpa using Fintype.card_congr e.toEquiv

/-- Isomorphic coded graphs have the same number of edges. -/
theorem edgeCount_eq {F G : GraphCode} (h : Isomorphic F G) :
    F.edgeCount = G.edgeCount := by
  apply Nat.le_antisymm
  · exact h.isContained.edgeCount_le
  · exact h.isContained'.edgeCount_le

end Isomorphic

/-- The usual graph Ramsey property at the *exact* ambient order `N`.

Every graph `C` on `Fin N` is viewed as the red graph of a two-colouring of `K_N`; `Cᶜ` is
the blue graph.  Copies are ordinary, non-induced copies. -/
def RamseyAt (F H : GraphCode) (N : ℕ) : Prop :=
  ∀ C : SimpleGraph (Fin N), F.graph ⊑ C ∨ H.graph ⊑ Cᶜ

namespace RamseyAt

/-- Making the first forbidden graph smaller preserves a Ramsey assertion. -/
theorem mono_left {F F' H : GraphCode} {N : ℕ} (hFF' : IsContained F' F)
    (h : RamseyAt F H N) : RamseyAt F' H N := by
  intro C
  exact (h C).imp (fun hFC ↦ SimpleGraph.IsContained.trans hFF' hFC) id

/-- Making the second forbidden graph smaller preserves a Ramsey assertion. -/
theorem mono_right {F H H' : GraphCode} {N : ℕ} (hHH' : IsContained H' H)
    (h : RamseyAt F H N) : RamseyAt F H' N := by
  intro C
  exact (h C).imp id (fun hHC ↦ SimpleGraph.IsContained.trans hHH' hHC)

/-- Simultaneous antitonicity in the two forbidden graphs. -/
theorem mono {F F' H H' : GraphCode} {N : ℕ} (hFF' : IsContained F' F)
    (hHH' : IsContained H' H) (h : RamseyAt F H N) : RamseyAt F' H' N :=
  (h.mono_left hFF').mono_right hHH'

/-- Replacing the first forbidden graph by an isomorphic graph changes nothing. -/
theorem congr_left {F F' H : GraphCode} {N : ℕ} (hFF' : Isomorphic F F') :
    RamseyAt F H N ↔ RamseyAt F' H N := by
  constructor
  · exact mono_left hFF'.isContained'
  · exact mono_left hFF'.isContained

/-- Replacing the second forbidden graph by an isomorphic graph changes nothing. -/
theorem congr_right {F H H' : GraphCode} {N : ℕ} (hHH' : Isomorphic H H') :
    RamseyAt F H N ↔ RamseyAt F H' N := by
  constructor
  · exact mono_right hHH'.isContained'
  · exact mono_right hHH'.isContained

/-- Isomorphism invariance in both forbidden graphs. -/
theorem congr {F F' H H' : GraphCode} {N : ℕ} (hFF' : Isomorphic F F')
    (hHH' : Isomorphic H H') : RamseyAt F H N ↔ RamseyAt F' H' N := by
  rw [congr_left hFF', congr_right hHH']

/-- The graph Ramsey property is symmetric in its two forbidden graphs. -/
theorem comm (F H : GraphCode) (N : ℕ) : RamseyAt F H N ↔ RamseyAt H F N := by
  constructor <;> intro h C
  · simpa only [compl_compl] using (h Cᶜ).symm
  · simpa only [compl_compl] using (h Cᶜ).symm

/-- Once the Ramsey property holds, it continues to hold after adding ambient vertices. -/
theorem mono_vertices {F H : GraphCode} {N M : ℕ} (hNM : N ≤ M)
    (h : RamseyAt F H N) : RamseyAt F H M := by
  intro C
  let f : Fin N ↪ Fin M := Fin.castLEEmb hNM
  rcases h (C.comap f) with hF | hH
  · left
    exact hF.trans (SimpleGraph.Embedding.comap f C).isContained
  · right
    have hcomp : (C.comap f)ᶜ = Cᶜ.comap f := by
      ext u v
      simp only [SimpleGraph.compl_adj, SimpleGraph.comap_adj]
      rw [f.injective.ne_iff]
    have hHC : H.graph ⊑ Cᶜ.comap f := by
      simpa only [hcomp] using hH
    exact hHC.trans (SimpleGraph.Embedding.comap f Cᶜ).isContained

end RamseyAt

/-- Every pair of coded finite graphs has a finite Ramsey bound. -/
theorem ramseyAt_exists (F H : GraphCode) : ∃ N, RamseyAt F H N := by
  obtain ⟨N, hN⟩ := Ramsey.ramseyProperty_exists F.vertexCount H.vertexCount
  refine ⟨N, ?_⟩
  intro C
  have hor : ¬ C.CliqueFree F.vertexCount ∨ ¬ C.IndepSetFree H.vertexCount :=
    not_and_or.mp (hN C)
  rcases hor with hred | hblue
  · left
    have htop : (⊤ : SimpleGraph (Fin F.vertexCount)) ⊑ C := by
      simpa only [SimpleGraph.completeGraph_eq_top] using
        (SimpleGraph.not_cliqueFree_iff_top_isContained F.vertexCount).mp hred
    exact (SimpleGraph.IsContained.of_le le_top).trans htop
  · right
    have hblue' : ¬ Cᶜ.CliqueFree H.vertexCount := by
      simpa only [SimpleGraph.cliqueFree_compl] using hblue
    have htop : (⊤ : SimpleGraph (Fin H.vertexCount)) ⊑ Cᶜ := by
      simpa only [SimpleGraph.completeGraph_eq_top] using
        (SimpleGraph.not_cliqueFree_iff_top_isContained H.vertexCount).mp hblue'
    exact (SimpleGraph.IsContained.of_le le_top).trans htop

/-- The least ambient order at which the graph Ramsey property holds. -/
noncomputable def graphRamseyNumber (F H : GraphCode) : ℕ :=
  by
    classical
    exact Nat.find (ramseyAt_exists F H)

theorem graphRamseyNumber_spec (F H : GraphCode) :
    RamseyAt F H (graphRamseyNumber F H) := by
  classical
  simpa only [graphRamseyNumber] using Nat.find_spec (ramseyAt_exists F H)

theorem graphRamseyNumber_le_of_ramseyAt {F H : GraphCode} {N : ℕ}
    (h : RamseyAt F H N) : graphRamseyNumber F H ≤ N := by
  classical
  simpa only [graphRamseyNumber] using Nat.find_min' (ramseyAt_exists F H) h

theorem ramseyAt_of_graphRamseyNumber_le {F H : GraphCode} {N : ℕ}
    (h : graphRamseyNumber F H ≤ N) : RamseyAt F H N :=
  (graphRamseyNumber_spec F H).mono_vertices h

theorem ramseyAt_iff_graphRamseyNumber_le {F H : GraphCode} {N : ℕ} :
    RamseyAt F H N ↔ graphRamseyNumber F H ≤ N :=
  ⟨graphRamseyNumber_le_of_ramseyAt, ramseyAt_of_graphRamseyNumber_le⟩

/-- Isomorphism invariance of the graph Ramsey number in both arguments. -/
theorem graphRamseyNumber_congr {F F' H H' : GraphCode} (hFF' : Isomorphic F F')
    (hHH' : Isomorphic H H') : graphRamseyNumber F H = graphRamseyNumber F' H' := by
  apply Nat.le_antisymm
  · apply graphRamseyNumber_le_of_ramseyAt
    exact (RamseyAt.congr hFF' hHH').mpr (graphRamseyNumber_spec F' H')
  · apply graphRamseyNumber_le_of_ramseyAt
    exact (RamseyAt.congr hFF' hHH').mp (graphRamseyNumber_spec F H)

/-- Symmetry of the graph Ramsey number. -/
theorem graphRamseyNumber_comm (F H : GraphCode) :
    graphRamseyNumber F H = graphRamseyNumber H F := by
  apply Nat.le_antisymm
  · apply graphRamseyNumber_le_of_ramseyAt
    exact (RamseyAt.comm F H _).mpr (graphRamseyNumber_spec H F)
  · apply graphRamseyNumber_le_of_ramseyAt
    exact (RamseyAt.comm F H _).mp (graphRamseyNumber_spec F H)

/-- The canonical code of a complete graph. -/
def completeCode (n : ℕ) : GraphCode := ⟨n, ⊤⟩

/-- On complete forbidden graphs, `RamseyAt` is exactly the `Util.Ramsey` property. -/
theorem ramseyAt_completeCode_iff (k l N : ℕ) :
    RamseyAt (completeCode k) (completeCode l) N ↔ Ramsey.RamseyProperty k l N := by
  constructor
  · intro h C hfree
    rcases h C with hred | hblue
    · exact SimpleGraph.IsContained.not_cliqueFree hred hfree.1
    · have hnot : ¬ Cᶜ.CliqueFree l :=
        SimpleGraph.IsContained.not_cliqueFree hblue
      exact hnot (by simpa only [SimpleGraph.cliqueFree_compl] using hfree.2)
  · intro h C
    have hor : ¬ C.CliqueFree k ∨ ¬ C.IndepSetFree l := not_and_or.mp (h C)
    rcases hor with hred | hblue
    · left
      simpa [completeCode, SimpleGraph.completeGraph_eq_top] using
        (SimpleGraph.not_cliqueFree_iff_top_isContained k).mp hred
    · right
      have hblue' : ¬ Cᶜ.CliqueFree l := by
        simpa only [SimpleGraph.cliqueFree_compl] using hblue
      simpa [completeCode, SimpleGraph.completeGraph_eq_top] using
        (SimpleGraph.not_cliqueFree_iff_top_isContained l).mp hblue'

/-- The generalized graph Ramsey number extends the off-diagonal Ramsey number in `Util.Ramsey`. -/
theorem graphRamseyNumber_completeCode (k l : ℕ) :
    graphRamseyNumber (completeCode k) (completeCode l) = Ramsey.ramseyNumber k l := by
  apply Nat.le_antisymm
  · apply graphRamseyNumber_le_of_ramseyAt
    exact (ramseyAt_completeCode_iff k l _).mpr (Ramsey.ramseyNumber_spec k l)
  · apply Ramsey.ramseyNumber_le_of_property
    exact (ramseyAt_completeCode_iff k l _).mp
      (graphRamseyNumber_spec (completeCode k) (completeCode l))

/-- A coded graph has no isolated vertices.  The empty graph satisfies this predicate
vacuously, as is standard. -/
def NoIsolated (G : GraphCode) : Prop :=
  ∀ v, ¬ G.graph.IsIsolated v

namespace NoIsolated

/-- Absence of isolated vertices is invariant under graph isomorphism. -/
theorem congr {F G : GraphCode} (hFG : Isomorphic F G) : NoIsolated F ↔ NoIsolated G := by
  rcases hFG with ⟨e⟩
  constructor
  · intro h w
    let v := e.symm w
    obtain ⟨u, hvu⟩ := F.graph.exists_adj_iff_not_isIsolated.mpr (h v)
    apply G.graph.exists_adj_iff_not_isIsolated.mp
    exact ⟨e u, by simpa [v] using e.map_rel_iff.mpr hvu⟩
  · intro h v
    let w := e v
    obtain ⟨u, hwu⟩ := G.graph.exists_adj_iff_not_isIsolated.mpr (h w)
    apply F.graph.exists_adj_iff_not_isIsolated.mp
    exact ⟨e.symm u, by simpa [w] using e.symm.map_rel_iff.mpr hwu⟩

/-- A finite graph without isolated vertices has at most twice as many vertices as edges. -/
theorem vertexCount_le_twice_edgeCount {G : GraphCode} (hG : NoIsolated G) :
    G.vertexCount ≤ 2 * G.edgeCount := by
  classical
  calc
    G.vertexCount = ∑ _v : Fin G.vertexCount, 1 := by simp
    _ ≤ ∑ v : Fin G.vertexCount, G.graph.degree v := by
      apply Finset.sum_le_sum
      intro v _hv
      exact (G.graph.degree_pos v).mpr (hG v)
    _ = 2 * G.graph.edgeFinset.card := G.graph.sum_degrees_eq_twice_card_edges
    _ = 2 * G.edgeCount := by rw [G.edgeCount_eq_card_edgeFinset]

end NoIsolated

/-- `F` is Ramsey size linear if one natural constant works uniformly for every coded graph
`H` without isolated vertices, with the Ramsey assertion holding already at the exact order
`C * e(H)`. -/
def RamseySizeLinear (F : GraphCode) : Prop :=
  ∃ C : ℕ, ∀ H : GraphCode, NoIsolated H → RamseyAt F H (C * H.edgeCount)

namespace RamseySizeLinear

/-- An equivalent least-Ramsey-number formulation of Ramsey size linearity. -/
theorem iff_graphRamseyNumber_le {F : GraphCode} :
    RamseySizeLinear F ↔
      ∃ C : ℕ, ∀ H : GraphCode, NoIsolated H →
        graphRamseyNumber F H ≤ C * H.edgeCount := by
  simp only [RamseySizeLinear, ramseyAt_iff_graphRamseyNumber_le]

/-- If `F'` is contained in a Ramsey-size-linear graph `F`, then `F'` is Ramsey size linear. -/
theorem mono {F F' : GraphCode} (hF'F : IsContained F' F) (hF : RamseySizeLinear F) :
    RamseySizeLinear F' := by
  rcases hF with ⟨C, hC⟩
  exact ⟨C, fun H hH ↦ (hC H hH).mono_left hF'F⟩

/-- Ramsey size linearity is invariant under graph isomorphism. -/
theorem congr {F F' : GraphCode} (hFF' : Isomorphic F F') :
    RamseySizeLinear F ↔ RamseySizeLinear F' := by
  constructor
  · exact mono hFF'.isContained'
  · exact mono hFF'.isContained

end RamseySizeLinear

end Erdos79
