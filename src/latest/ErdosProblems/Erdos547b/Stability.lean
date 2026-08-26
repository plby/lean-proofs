/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Combinatorics.SimpleGraph.Regularity.Uniform
import Mathlib.Combinatorics.SimpleGraph.Matching

/-!
# Initial edge pruning in Zhao's stability argument
-/

open scoped SimpleGraph

noncomputable section

namespace Erdos547b.ZhaoStability

open SimpleGraph

/-- Keep exactly those edges of `G` having at least one endpoint in `L`.
This is the edge-pruning operation used at the start of Zhao's stability
argument, with `L` the set of vertices of degree at least the target size. -/
def pruneSmallEdges {α : Type*} (G : SimpleGraph α) (L : Set α) : SimpleGraph α where
  Adj u v := G.Adj u v ∧ (u ∈ L ∨ v ∈ L)
  symm := ⟨fun _ _ h => ⟨h.1.symm, h.2.elim Or.inr Or.inl⟩⟩
  loopless := ⟨fun u h => G.loopless.irrefl u h.1⟩

instance pruneSmallEdges.instDecidableRelAdj {α : Type*} (G : SimpleGraph α)
    [DecidableRel G.Adj] (L : Set α) [DecidablePred (· ∈ L)] :
    DecidableRel (pruneSmallEdges G L).Adj :=
  inferInstanceAs (DecidableRel fun u v => G.Adj u v ∧ (u ∈ L ∨ v ∈ L))

@[simp] theorem pruneSmallEdges_adj {α : Type*} (G : SimpleGraph α) (L : Set α)
    (u v : α) : (pruneSmallEdges G L).Adj u v ↔ G.Adj u v ∧ (u ∈ L ∨ v ∈ L) :=
  Iff.rfl

theorem pruneSmallEdges_le {α : Type*} (G : SimpleGraph α) (L : Set α) :
    pruneSmallEdges G L ≤ G := by
  intro u v huv
  exact huv.1

theorem pruneSmallEdges_not_adj_of_not_mem {α : Type*} (G : SimpleGraph α)
    (L : Set α) {u v : α} (hu : u ∉ L) (hv : v ∉ L) :
    ¬(pruneSmallEdges G L).Adj u v := by
  simp [hu, hv]

theorem pruneSmallEdges_degree_eq_of_mem {α : Type*} [Fintype α]
    (G : SimpleGraph α) [DecidableRel G.Adj] (L : Set α) [DecidablePred (· ∈ L)]
    {v : α} (hv : v ∈ L) :
    (pruneSmallEdges G L).degree v = G.degree v := by
  have hneighbors : (pruneSmallEdges G L).neighborFinset v = G.neighborFinset v := by
    ext w
    simp [hv]
  simpa only [card_neighborFinset_eq_degree] using congrArg Finset.card hneighbors

/-- Deleting all edges between vertices below degree `k` preserves exactly
the vertices whose original degree is at least `k`. -/
theorem highDegree_iff_pruneSmallEdges_highDegree {α : Type*} [Fintype α]
    (G : SimpleGraph α) [DecidableRel G.Adj] (k : ℕ) (v : α) :
    k ≤ (pruneSmallEdges G {w | k ≤ G.degree w}).degree v ↔ k ≤ G.degree v := by
  classical
  constructor
  · intro hv
    exact hv.trans (degree_le_of_le (v := v) (pruneSmallEdges_le G {w | k ≤ G.degree w}))
  · intro hv
    rw [pruneSmallEdges_degree_eq_of_mem G {w | k ≤ G.degree w} hv]
    exact hv

theorem highDegree_vertices_pruneSmallEdges {α : Type*} [Fintype α]
    (G : SimpleGraph α) [DecidableRel G.Adj] (k : ℕ) :
    (Finset.univ.filter fun v => k ≤
        (pruneSmallEdges G {w | k ≤ G.degree w}).degree v) =
      Finset.univ.filter fun v => k ≤ G.degree v := by
  classical
  ext v
  simp [highDegree_iff_pruneSmallEdges_highDegree]

theorem highDegree_card_pruneSmallEdges {α : Type*} [Fintype α]
    (G : SimpleGraph α) [DecidableRel G.Adj] (k : ℕ) :
    (Finset.univ.filter fun v => k ≤
        (pruneSmallEdges G {w | k ≤ G.degree w}).degree v).card =
      (Finset.univ.filter fun v => k ≤ G.degree v).card := by
  rw [highDegree_vertices_pruneSmallEdges]

/-- In the even-host specialization used for Zhao's theorem, pruning
small--small edges preserves the hypothesis `ℓ(G) ≥ n` verbatim. -/
theorem evenHost_highDegree_count_preserved (n : ℕ) (G : SimpleGraph (Fin (2 * n)))
    [DecidableRel G.Adj]
    (hlarge : n ≤ (Finset.univ.filter fun v => n ≤ G.degree v).card) :
    n ≤ (Finset.univ.filter fun v => n ≤
      (pruneSmallEdges G {w | n ≤ G.degree w}).degree v).card := by
  rw [highDegree_card_pruneSmallEdges]
  exact hlarge

/-!
## The reduced cluster graph and the counting core of Zhao's Claim 6.1

The actual regularity lemma will eventually produce the predicates called
`regular` and `dense` below.  Keeping them as explicit parameters makes the
following part independent of a particular regularity-lemma API: an edge is
put in the reduced graph exactly when its pair is both regular and dense.
-/

/-- The reduced graph associated with symmetric predicates saying that a
pair of clusters is regular and has density above the chosen cutoff. -/
def reducedClusterGraph {ι : Type*} (regular dense : ι → ι → Prop)
    (hregular : ∀ ⦃i j⦄, regular i j → regular j i)
    (hdense : ∀ ⦃i j⦄, dense i j → dense j i) : SimpleGraph ι where
  Adj i j := i ≠ j ∧ regular i j ∧ dense i j
  symm := ⟨fun _ _ hij =>
    ⟨hij.1.symm, hregular hij.2.1, hdense hij.2.2⟩⟩
  loopless := ⟨fun _ hii => hii.1 rfl⟩

@[simp] theorem reducedClusterGraph_adj {ι : Type*} (regular dense : ι → ι → Prop)
    (hregular : ∀ ⦃i j⦄, regular i j → regular j i)
    (hdense : ∀ ⦃i j⦄, dense i j → dense j i) (i j : ι) :
    (reducedClusterGraph regular dense hregular hdense).Adj i j ↔
      i ≠ j ∧ regular i j ∧ dense i j :=
  Iff.rfl

/-- The concrete reduced graph attached to a family of clusters in Mathlib's
regularity language.  Its edges are precisely distinct `ε`-uniform pairs of
edge density at least `d`. -/
def regularityReducedGraph {V ι : Type*} (G : SimpleGraph V)
    [DecidableRel G.Adj] (C : ι → Finset V) (ε d : ℚ) : SimpleGraph ι :=
  reducedClusterGraph
    (fun i j => G.IsUniform ε (C i) (C j))
    (fun i j => d ≤ G.edgeDensity (C i) (C j))
    (fun {_ _} h => SimpleGraph.IsUniform.symm h)
    (fun {_ _} h => by rwa [G.edgeDensity_comm])

@[simp] theorem regularityReducedGraph_adj {V ι : Type*} (G : SimpleGraph V)
    [DecidableRel G.Adj] (C : ι → Finset V) (ε d : ℚ) (i j : ι) :
    (regularityReducedGraph G C ε d).Adj i j ↔
      i ≠ j ∧ G.IsUniform ε (C i) (C j) ∧
        d ≤ G.edgeDensity (C i) (C j) :=
  Iff.rfl

/-- A cluster assignment sends each ordinary vertex to a cluster index and
sends each exceptional vertex to `none`. -/
abbrev ClusterAssignment (V ι : Type*) := V → Option ι

/-- The exceptional class of a cluster assignment. -/
def exceptionalVertices {V ι : Type*} [Fintype V] [DecidableEq ι]
    (P : ClusterAssignment V ι) : Finset V :=
  Finset.univ.filter fun v => P v = none

/-- The vertices assigned to cluster `i`. -/
def clusterVertices {V ι : Type*} [Fintype V] [DecidableEq ι]
    (P : ClusterAssignment V ι) (i : ι) : Finset V :=
  Finset.univ.filter fun v => P v = some i

@[simp] theorem mem_exceptionalVertices {V ι : Type*} [Fintype V] [DecidableEq ι]
    (P : ClusterAssignment V ι) (v : V) :
    v ∈ exceptionalVertices P ↔ P v = none := by
  simp [exceptionalVertices]

@[simp] theorem mem_clusterVertices {V ι : Type*} [Fintype V] [DecidableEq ι]
    (P : ClusterAssignment V ι) (i : ι) (v : V) :
    v ∈ clusterVertices P i ↔ P v = some i := by
  simp [clusterVertices]

/-- The clusters which contain at least one vertex of `L`.  In Claim 6.1,
`L` is the set of vertices whose degree is at least the tree size. -/
def clustersMeeting {V ι : Type*} [Fintype V] [Fintype ι]
    [DecidableEq V] [DecidableEq ι]
    (P : ClusterAssignment V ι) (L : Finset V) : Finset ι :=
  Finset.univ.filter fun i => (clusterVertices P i ∩ L).Nonempty

@[simp] theorem mem_clustersMeeting {V ι : Type*} [Fintype V] [Fintype ι]
    [DecidableEq V] [DecidableEq ι] (P : ClusterAssignment V ι) (L : Finset V)
    (i : ι) :
    i ∈ clustersMeeting P L ↔ ∃ v ∈ L, P v = some i := by
  rw [clustersMeeting, Finset.mem_filter]
  simp only [Finset.mem_univ, true_and]
  constructor
  · rintro ⟨v, hv⟩
    have ⟨hvcluster, hvL⟩ := Finset.mem_inter.mp hv
    exact ⟨v, hvL, (mem_clusterVertices P i v).mp hvcluster⟩
  · rintro ⟨v, hvL, hvP⟩
    exact ⟨v, Finset.mem_inter.mpr ⟨(mem_clusterVertices P i v).mpr hvP, hvL⟩⟩

/-- The degree-form cleaned graph respects the reduced graph: any cleaned
edge between two nonexceptional classes comes from an edge of the reduced
cluster graph. -/
def EdgesRespectReducedGraph {V ι : Type*} (P : ClusterAssignment V ι)
    (H : SimpleGraph V) (R : SimpleGraph ι) : Prop :=
  ∀ ⦃u v : V⦄ ⦃i j : ι⦄,
    P u = some i → P v = some j → H.Adj u v → R.Adj i j

/-- The numerical output from the degree-form regularity lemma used below:
passing from `G` to the cleaned graph `H` deletes at most `loss` incident
edges at every vertex. -/
def DegreeLossAtMost {V : Type*} [Fintype V] (G H : SimpleGraph V)
    [DecidableRel G.Adj] [DecidableRel H.Adj] (loss : ℕ) : Prop :=
  ∀ v, G.degree v ≤ H.degree v + loss

/-- A threshold-degree vertex of the original graph retains degree at least
`threshold - loss` in the degree-form cleaned graph. -/
theorem cleaned_degree_ge_threshold_sub_loss
    {V : Type*} [Fintype V] (G H : SimpleGraph V)
    [DecidableRel G.Adj] [DecidableRel H.Adj]
    (loss threshold : ℕ) (hloss : DegreeLossAtMost G H loss)
    {v : V} (hv : threshold ≤ G.degree v) :
    threshold - loss ≤ H.degree v := by
  have := hloss v
  omega

/-- Every cleaned neighbor of a vertex in cluster `i` is either exceptional
or belongs to a cluster adjacent to `i` in the reduced graph. -/
theorem neighborFinset_subset_exceptional_union_reduced
    {V ι : Type*} [Fintype V] [Fintype ι] [DecidableEq V] [DecidableEq ι]
    (P : ClusterAssignment V ι) (H : SimpleGraph V) (R : SimpleGraph ι)
    [DecidableRel H.Adj] [DecidableRel R.Adj]
    (hrespect : EdgesRespectReducedGraph P H R) {v : V} {i : ι}
    (hv : P v = some i) :
    H.neighborFinset v ⊆ exceptionalVertices P ∪
      (R.neighborFinset i).biUnion (clusterVertices P) := by
  intro w hw
  have hadj : H.Adj v w := by simpa using hw
  cases hwP : P w with
  | none =>
      exact Finset.mem_union_left _ ((mem_exceptionalVertices P w).mpr hwP)
  | some j =>
      apply Finset.mem_union_right
      apply Finset.mem_biUnion.mpr
      refine ⟨j, ?_, (mem_clusterVertices P j w).mpr hwP⟩
      simpa using hrespect hv hwP hadj

/-- Exact counting form of the cluster-degree transfer in Claim 6.1(1).
If clusters have size at most `m`, a cleaned degree can use at most all
exceptional vertices plus `m` vertices per reduced neighbor. -/
theorem degree_le_exceptional_add_reduced_degree_mul
    {V ι : Type*} [Fintype V] [Fintype ι] [DecidableEq V] [DecidableEq ι]
    (P : ClusterAssignment V ι) (H : SimpleGraph V) (R : SimpleGraph ι)
    [DecidableRel H.Adj] [DecidableRel R.Adj]
    (hrespect : EdgesRespectReducedGraph P H R) (m : ℕ)
    (hcluster : ∀ i, (clusterVertices P i).card ≤ m)
    {v : V} {i : ι} (hv : P v = some i) :
    H.degree v ≤ (exceptionalVertices P).card + R.degree i * m := by
  calc
    H.degree v = (H.neighborFinset v).card := rfl
    _ ≤ (exceptionalVertices P ∪
        (R.neighborFinset i).biUnion (clusterVertices P)).card :=
      Finset.card_le_card
        (neighborFinset_subset_exceptional_union_reduced P H R hrespect hv)
    _ ≤ (exceptionalVertices P).card +
        ((R.neighborFinset i).biUnion (clusterVertices P)).card :=
      Finset.card_union_le _ _
    _ ≤ (exceptionalVertices P).card + (R.neighborFinset i).card * m := by
      exact Nat.add_le_add_left
        (Finset.card_biUnion_le_card_mul _ _ m fun j _ => hcluster j) _
    _ = (exceptionalVertices P).card + R.degree i * m := by
      rw [card_neighborFinset_eq_degree]

/-- Subtraction form of the preceding transfer: a degree lower bound forces
many reduced-neighbor slots. -/
theorem threshold_sub_exceptional_le_reduced_degree_mul
    {V ι : Type*} [Fintype V] [Fintype ι] [DecidableEq V] [DecidableEq ι]
    (P : ClusterAssignment V ι) (H : SimpleGraph V) (R : SimpleGraph ι)
    [DecidableRel H.Adj] [DecidableRel R.Adj]
    (hrespect : EdgesRespectReducedGraph P H R) (m threshold : ℕ)
    (hcluster : ∀ i, (clusterVertices P i).card ≤ m)
    {v : V} {i : ι} (hv : P v = some i) (hdegree : threshold ≤ H.degree v) :
    threshold - (exceptionalVertices P).card ≤ R.degree i * m := by
  have hupper := degree_le_exceptional_add_reduced_degree_mul
    P H R hrespect m hcluster hv
  omega

/-- The first reduced-degree conclusion of Claim 6.1, stated without
rounding constants: every cluster meeting the threshold-degree set has enough
reduced-neighbor capacity to account for that degree. -/
theorem reduced_degree_capacity_of_mem_clustersMeeting_highDegree
    {V ι : Type*} [Fintype V] [Fintype ι] [DecidableEq V] [DecidableEq ι]
    (P : ClusterAssignment V ι) (H : SimpleGraph V) (R : SimpleGraph ι)
    [DecidableRel H.Adj] [DecidableRel R.Adj]
    (hrespect : EdgesRespectReducedGraph P H R) (m threshold : ℕ)
    (hcluster : ∀ i, (clusterVertices P i).card ≤ m)
    {i : ι}
    (hi : i ∈ clustersMeeting P
      (Finset.univ.filter fun v => threshold ≤ H.degree v)) :
    threshold - (exceptionalVertices P).card ≤ R.degree i * m := by
  rw [mem_clustersMeeting] at hi
  obtain ⟨v, hvdegree, hvP⟩ := hi
  have hdegree : threshold ≤ H.degree v := by simpa using hvdegree
  exact threshold_sub_exceptional_le_reduced_degree_mul
    P H R hrespect m threshold hcluster hvP hdegree

/-- Degree-form version of Claim 6.1(1).  A cluster meeting the original
threshold-degree set has enough reduced-neighbor capacity after accounting
for both the degree loss and the exceptional class. -/
theorem reduced_degree_capacity_of_degreeForm
    {V ι : Type*} [Fintype V] [Fintype ι] [DecidableEq V] [DecidableEq ι]
    (P : ClusterAssignment V ι) (G H : SimpleGraph V) (R : SimpleGraph ι)
    [DecidableRel G.Adj] [DecidableRel H.Adj] [DecidableRel R.Adj]
    (hrespect : EdgesRespectReducedGraph P H R) (m threshold loss : ℕ)
    (hcluster : ∀ i, (clusterVertices P i).card ≤ m)
    (hloss : DegreeLossAtMost G H loss) {i : ι}
    (hi : i ∈ clustersMeeting P
      (Finset.univ.filter fun v => threshold ≤ G.degree v)) :
    (threshold - loss) - (exceptionalVertices P).card ≤ R.degree i * m := by
  rw [mem_clustersMeeting] at hi
  obtain ⟨v, hvdegree, hvP⟩ := hi
  have hdegreeG : threshold ≤ G.degree v := by simpa using hvdegree
  have hdegreeH : threshold - loss ≤ H.degree v :=
    cleaned_degree_ge_threshold_sub_loss G H loss threshold hloss hdegreeG
  exact threshold_sub_exceptional_le_reduced_degree_mul
    P H R hrespect m (threshold - loss) hcluster hvP hdegreeH

/-- Every selected vertex is exceptional or lies in a cluster which meets
the selected set.  This is the set-theoretic core of Claim 6.1(2). -/
theorem subset_exceptional_union_clustersMeeting
    {V ι : Type*} [Fintype V] [Fintype ι] [DecidableEq V] [DecidableEq ι]
    (P : ClusterAssignment V ι) (L : Finset V) :
    L ⊆ exceptionalVertices P ∪
      (clustersMeeting P L).biUnion (clusterVertices P) := by
  intro v hvL
  cases hvP : P v with
  | none =>
      exact Finset.mem_union_left _ ((mem_exceptionalVertices P v).mpr hvP)
  | some i =>
      apply Finset.mem_union_right
      apply Finset.mem_biUnion.mpr
      refine ⟨i, ?_, (mem_clusterVertices P i v).mpr hvP⟩
      rw [mem_clustersMeeting]
      exact ⟨v, hvL, hvP⟩

/-- Exact counting form of Claim 6.1(2): if every cluster has at most `m`
vertices, then a selected set can occupy at most the exceptional class plus
`m` vertices for every cluster it meets. -/
theorem card_le_exceptional_add_clustersMeeting_mul
    {V ι : Type*} [Fintype V] [Fintype ι] [DecidableEq V] [DecidableEq ι]
    (P : ClusterAssignment V ι) (L : Finset V) (m : ℕ)
    (hcluster : ∀ i, (clusterVertices P i).card ≤ m) :
    L.card ≤ (exceptionalVertices P).card + (clustersMeeting P L).card * m := by
  calc
    L.card ≤ (exceptionalVertices P ∪
        (clustersMeeting P L).biUnion (clusterVertices P)).card :=
      Finset.card_le_card (subset_exceptional_union_clustersMeeting P L)
    _ ≤ (exceptionalVertices P).card +
        ((clustersMeeting P L).biUnion (clusterVertices P)).card :=
      Finset.card_union_le _ _
    _ ≤ (exceptionalVertices P).card + (clustersMeeting P L).card * m := by
      exact Nat.add_le_add_left
        (Finset.card_biUnion_le_card_mul _ _ m fun i _ => hcluster i) _

/-- Specialized high-degree-count consequence for an even Ramsey host.  At
least `n` threshold-degree vertices force at least `n - |V₀|` nonexceptional
cluster slots among the threshold-large clusters. -/
theorem evenHost_large_clusters_capacity
    {ι : Type*} [Fintype ι] [DecidableEq ι] (n m : ℕ)
    (P : ClusterAssignment (Fin (2 * n)) ι) (H : SimpleGraph (Fin (2 * n)))
    [DecidableRel H.Adj]
    (hcluster : ∀ i, (clusterVertices P i).card ≤ m)
    (hlarge : n ≤ (Finset.univ.filter fun v => n ≤ H.degree v).card) :
    n - (exceptionalVertices P).card ≤
      (clustersMeeting P (Finset.univ.filter fun v => n ≤ H.degree v)).card * m := by
  have hupper := card_le_exceptional_add_clustersMeeting_mul P
    (Finset.univ.filter fun v => n ≤ H.degree v) m hcluster
  omega

/-- Claim 6.1(2) in the specialized host notation, with the large clusters
defined using degrees in the original host graph.  Notice that this counting
conclusion needs no degree-loss hypothesis. -/
theorem evenHost_original_highDegree_large_clusters_capacity
    {ι : Type*} [Fintype ι] [DecidableEq ι] (n m : ℕ)
    (P : ClusterAssignment (Fin (2 * n)) ι) (G : SimpleGraph (Fin (2 * n)))
    [DecidableRel G.Adj]
    (hcluster : ∀ i, (clusterVertices P i).card ≤ m)
    (hlarge : n ≤ (Finset.univ.filter fun v => n ≤ G.degree v).card) :
    n - (exceptionalVertices P).card ≤
      (clustersMeeting P (Finset.univ.filter fun v => n ≤ G.degree v)).card * m :=
  evenHost_large_clusters_capacity n m P G hcluster hlarge

/-- The two exact capacity conclusions forming the arithmetic core of the
specialized Claim 6.1.  The first is the reduced minimum-degree conclusion
for every large cluster; the second says that there are enough large-cluster
slots to contain the `n` high-degree vertices outside the exceptional set. -/
theorem evenHost_degreeForm_claim6_1_capacity
    {ι : Type*} [Fintype ι] [DecidableEq ι] (n m loss : ℕ)
    (P : ClusterAssignment (Fin (2 * n)) ι)
    (G H : SimpleGraph (Fin (2 * n))) (R : SimpleGraph ι)
    [DecidableRel G.Adj] [DecidableRel H.Adj] [DecidableRel R.Adj]
    (hrespect : EdgesRespectReducedGraph P H R)
    (hcluster : ∀ i, (clusterVertices P i).card ≤ m)
    (hloss : DegreeLossAtMost G H loss)
    (hlarge : n ≤ (Finset.univ.filter fun v => n ≤ G.degree v).card) :
    (∀ i ∈ clustersMeeting P (Finset.univ.filter fun v => n ≤ G.degree v),
        (n - loss) - (exceptionalVertices P).card ≤ R.degree i * m) ∧
      n - (exceptionalVertices P).card ≤
        (clustersMeeting P
          (Finset.univ.filter fun v => n ≤ G.degree v)).card * m := by
  constructor
  · intro i hi
    exact reduced_degree_capacity_of_degreeForm
      P G H R hrespect m n loss hcluster hloss hi
  · exact evenHost_original_highDegree_large_clusters_capacity
      n m P G hcluster hlarge


/-!
## Forest gluing (the interface used by Lemma 6.3)

The analytic regular-pair work in Zhao's Lemmas 5.8 and 6.3 constructs one
injective vertex map in stages.  The following certificate records exactly
the finite graph obligations left after those stages: the source edges are
covered by the two forest parts and their linking edges, and the common map
preserves each of those three edge classes.
-/

/-- Data sufficient to glue two embedded forest parts and their linking
edges into one non-induced copy of the original tree. -/
structure ForestGluingCertificate {τ V : Type*}
    (T : SimpleGraph τ) (G : SimpleGraph V) where
  map : τ ↪ V
  partA : SimpleGraph τ
  partB : SimpleGraph τ
  links : SimpleGraph τ
  edgeCover : T ≤ partA ⊔ partB ⊔ links
  map_partA : ∀ ⦃x y⦄, partA.Adj x y → G.Adj (map x) (map y)
  map_partB : ∀ ⦃x y⦄, partB.Adj x y → G.Adj (map x) (map y)
  map_links : ∀ ⦃x y⦄, links.Adj x y → G.Adj (map x) (map y)

/-- A forest-gluing certificate gives a genuine Mathlib non-induced copy. -/
def ForestGluingCertificate.toCopy {τ V : Type*} {T : SimpleGraph τ}
    {G : SimpleGraph V} (C : ForestGluingCertificate T G) : Copy T G where
  toHom :=
    { toFun := C.map
      map_rel' := by
        intro x y hxy
        have hcover := C.edgeCover hxy
        simp only [sup_adj] at hcover
        rcases hcover with (hA | hB) | hlink
        · exact C.map_partA hA
        · exact C.map_partB hB
        · exact C.map_links hlink }
  injective' := C.map.injective

/-- Concrete Lemma 6.3 gluing conclusion, including its root-location
conclusion.  All regular-pair choices are isolated in the certificate and in
`hroots`; the conclusion itself contains no unproved embedding oracle. -/
theorem zhaoLemma6_3_of_forestGluingCertificate
    {τ V : Type*} [DecidableEq V] {T : SimpleGraph τ} {G : SimpleGraph V}
    (C : ForestGluingCertificate T G) (roots : Finset τ)
    (A₀ B₀ : Finset V)
    (hroots : ∀ r ∈ roots, C.map r ∈ A₀ ∪ B₀) :
    ∃ f : Copy T G, ∀ r ∈ roots, f r ∈ A₀ ∪ B₀ := by
  refine ⟨C.toCopy, ?_⟩
  intro r hr
  change C.map r ∈ A₀ ∪ B₀
  exact hroots r hr

/-!
## Matchings, Claim 6.7, and the capacity passed to Lemma 6.5
-/

/-- The clusters covered by a matching subgraph. -/
noncomputable def matchingSupport {ι : Type*} [Fintype ι]
    {R : SimpleGraph ι} (M : R.Subgraph) : Finset ι :=
  M.verts.toFinite.toFinset

@[simp] theorem mem_matchingSupport {ι : Type*} [Fintype ι]
    {R : SimpleGraph ι} (M : R.Subgraph) (v : ι) :
    v ∈ matchingSupport M ↔ v ∈ M.verts := by
  simp [matchingSupport, Set.Finite.mem_toFinset]

/-- The number of reduced neighbors of `u` covered by the matching.  This is
the unweighted cluster-level precursor of Zhao's `deg(u,M)`. -/
noncomputable def matchingNeighborCount {ι : Type*} [Fintype ι]
    [DecidableEq ι] (R : SimpleGraph ι) [DecidableRel R.Adj]
    (M : R.Subgraph) (u : ι) : ℕ :=
  (R.neighborFinset u ∩ matchingSupport M).card

/-- Vertices on matching edges whose two endpoints are both adjacent to
`u`; this is the vertex-set covered by Zhao's `M₂(u)`. -/
def matchingDoubleNeighborSet {ι : Type*} (R : SimpleGraph ι)
    (M : R.Subgraph) (u : ι) : Set ι :=
  {v | v ∈ M.verts ∧ ∃ w, M.Adj v w ∧ R.Adj u v ∧ R.Adj u w}

/-- A direct finite formulation of the three conclusions of Claim 6.7. -/
structure Claim67Certificate {ι : Type*} [Fintype ι] [DecidableEq ι]
    (R : SimpleGraph ι) [DecidableRel R.Adj] (L : Finset ι) (miss : ℕ) where
  O : Finset ι
  M : R.Subgraph
  isMatching : M.IsMatching
  adjacentLarge : ∃ A ∈ L ∩ O, ∃ B ∈ L ∩ O, R.Adj A B
  neighbors_missed : ∀ U ∈ O,
    (R.neighborFinset U \ matchingSupport M).card ≤ miss
  doubleNeighbor_outside : ∀ U ∈ O,
    (matchingDoubleNeighborSet R M U \ (O : Set ι)).ncard ≤ 1

/-- If a matching misses at most `miss` vertices globally, and the large
clusters are not independent, the first branch in Zhao's proof of Claim 6.7
is obtained by taking `O` to be the entire reduced vertex set. -/
noncomputable def claim67Certificate_of_nearPerfectMatching
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (R : SimpleGraph ι) [DecidableRel R.Adj] (L : Finset ι) (miss : ℕ)
    (M : R.Subgraph) (hM : M.IsMatching)
    (hglobal : (Finset.univ \ matchingSupport M).card ≤ miss)
    (hlargeEdge : ∃ A ∈ L, ∃ B ∈ L, R.Adj A B) :
    Claim67Certificate R L miss where
  O := Finset.univ
  M := M
  isMatching := hM
  adjacentLarge := by
    obtain ⟨A, hAL, B, hBL, hAB⟩ := hlargeEdge
    exact ⟨A, by simp [hAL], B, by simp [hBL], hAB⟩
  neighbors_missed := by
    intro U _
    apply (Finset.card_le_card ?_).trans hglobal
    intro v hv
    simp only [Finset.mem_sdiff, Finset.mem_univ, true_and] at hv ⊢
    exact hv.2
  doubleNeighbor_outside := by
    intro U _
    simp

/-- The elementary accounting identity behind Claim 6.7(2): uncovered
neighbors plus covered neighbors partition the whole reduced neighborhood. -/
theorem degree_le_matchingNeighborCount_add_missed
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (R : SimpleGraph ι) [DecidableRel R.Adj] (M : R.Subgraph)
    (u : ι) (miss : ℕ)
    (hmiss : (R.neighborFinset u \ matchingSupport M).card ≤ miss) :
    R.degree u ≤ matchingNeighborCount R M u + miss := by
  have hpartition := Finset.card_sdiff_add_card_inter
    (R.neighborFinset u) (matchingSupport M)
  rw [card_neighborFinset_eq_degree] at hpartition
  unfold matchingNeighborCount
  omega

/-- A Claim 6.7 certificate converts a reduced-degree lower bound into
matching-covered capacity, in the exact subtraction form used in (6.12). -/
theorem claim67_reducedDegree_sub_miss_le_matchingNeighborCount
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {R : SimpleGraph ι} [DecidableRel R.Adj] {L : Finset ι} {miss D : ℕ}
    (C : Claim67Certificate R L miss) {u : ι} (hu : u ∈ C.O)
    (hdegree : D ≤ R.degree u) :
    D - miss ≤ matchingNeighborCount R C.M u := by
  have hcount := degree_le_matchingNeighborCount_add_missed
    R C.M u miss (C.neighbors_missed u hu)
  omega

/-- The pair of adjacent large clusters and their matching-covered capacities
which Claim 6.7 supplies to Lemma 6.5. -/
theorem claim67_exists_adjacentLarge_with_capacity
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {R : SimpleGraph ι} [DecidableRel R.Adj] {L : Finset ι} {miss D : ℕ}
    (C : Claim67Certificate R L miss)
    (hlargeDegree : ∀ u ∈ L ∩ C.O, D ≤ R.degree u) :
    ∃ A ∈ L ∩ C.O, ∃ B ∈ L ∩ C.O,
      R.Adj A B ∧
      D - miss ≤ matchingNeighborCount R C.M A ∧
      D - miss ≤ matchingNeighborCount R C.M B := by
  obtain ⟨A, hA, B, hB, hAB⟩ := C.adjacentLarge
  refine ⟨A, hA, B, hB, hAB, ?_, ?_⟩
  · exact claim67_reducedDegree_sub_miss_le_matchingNeighborCount
      C (Finset.mem_inter.mp hA).2 (hlargeDegree A hA)
  · exact claim67_reducedDegree_sub_miss_le_matchingNeighborCount
      C (Finset.mem_inter.mp hB).2 (hlargeDegree B hB)

/-- Cluster-size scaling of the preceding inequality.  This is the
unweighted form of the capacity inequality passed to Lemma 6.5. -/
theorem claim67_matching_cluster_slots_capacity
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {R : SimpleGraph ι} [DecidableRel R.Adj] {L : Finset ι} {miss D : ℕ}
    (C : Claim67Certificate R L miss) {u : ι} (hu : u ∈ C.O)
    (hdegree : D ≤ R.degree u) (clusterSize : ℕ) :
    (D - miss) * clusterSize ≤
      matchingNeighborCount R C.M u * clusterSize := by
  exact Nat.mul_le_mul_right clusterSize
    (claim67_reducedDegree_sub_miss_le_matchingNeighborCount C hu hdegree)

/-- A natural-valued weighted reduced degree.  Taking `weight u v` to be
the number of available host vertices represented by the reduced edge
`uv` recovers the degree quantities used in Lemma 6.5. -/
def weightedReducedDegree {ι : Type*} [Fintype ι]
    (R : SimpleGraph ι) [DecidableRel R.Adj]
    (weight : ι → ι → ℕ) (u : ι) : ℕ :=
  ∑ v ∈ R.neighborFinset u, weight u v

/-- The part of the weighted reduced degree supported on clusters covered
by a matching. -/
noncomputable def matchingWeightedCapacity {ι : Type*} [Fintype ι]
    [DecidableEq ι] (R : SimpleGraph ι) [DecidableRel R.Adj]
    (M : R.Subgraph) (weight : ι → ι → ℕ) (u : ι) : ℕ :=
  ∑ v ∈ R.neighborFinset u ∩ matchingSupport M, weight u v

/-- Weighted form of the neighbor accounting behind (6.12): if each missed
cluster costs at most `clusterSize`, then `miss` missed clusters cost at most
`miss * clusterSize`. -/
theorem weightedReducedDegree_le_matchingCapacity_add_missed
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (R : SimpleGraph ι) [DecidableRel R.Adj] (M : R.Subgraph)
    (weight : ι → ι → ℕ) (u : ι) (miss clusterSize : ℕ)
    (hweight : ∀ v ∈ R.neighborFinset u, weight u v ≤ clusterSize)
    (hmiss : (R.neighborFinset u \ matchingSupport M).card ≤ miss) :
    weightedReducedDegree R weight u ≤
      matchingWeightedCapacity R M weight u + miss * clusterSize := by
  let S := R.neighborFinset u
  let Q := matchingSupport M
  calc
    weightedReducedDegree R weight u = ∑ v ∈ S, weight u v := rfl
    _ = (∑ v ∈ S ∩ Q, weight u v) + (∑ v ∈ S \ Q, weight u v) :=
      (Finset.sum_inter_add_sum_sdiff S Q (weight u)).symm
    _ ≤ (∑ v ∈ S ∩ Q, weight u v) + (S \ Q).card * clusterSize := by
      apply Nat.add_le_add_left
      simpa using Finset.sum_le_card_nsmul (S \ Q) (weight u) clusterSize
        (fun v hv => hweight v (Finset.mem_sdiff.mp hv).1)
    _ ≤ (∑ v ∈ S ∩ Q, weight u v) + miss * clusterSize := by
      exact Nat.add_le_add_left (Nat.mul_le_mul_right clusterSize hmiss) _
    _ = matchingWeightedCapacity R M weight u + miss * clusterSize := rfl

/-- Subtraction form of the weighted capacity estimate, exactly matching
the arithmetic use of Claim 6.7 in Zhao's display (6.12). -/
theorem claim67_weightedDegree_sub_error_le_matchingCapacity
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {R : SimpleGraph ι} [DecidableRel R.Adj] {L : Finset ι} {miss D : ℕ}
    (C : Claim67Certificate R L miss) (weight : ι → ι → ℕ)
    {u : ι} (hu : u ∈ C.O) (clusterSize : ℕ)
    (hweight : ∀ v ∈ R.neighborFinset u, weight u v ≤ clusterSize)
    (hdegree : D ≤ weightedReducedDegree R weight u) :
    D - miss * clusterSize ≤ matchingWeightedCapacity R C.M weight u := by
  have hupper := weightedReducedDegree_le_matchingCapacity_add_missed
    R C.M weight u miss clusterSize hweight (C.neighbors_missed u hu)
  omega

/-- Weighted-capacity version of the adjacent-pair output sent from
Claim 6.7 to Lemma 6.5. -/
theorem claim67_exists_adjacentLarge_with_weighted_capacity
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {R : SimpleGraph ι} [DecidableRel R.Adj] {L : Finset ι} {miss D : ℕ}
    (C : Claim67Certificate R L miss) (weight : ι → ι → ℕ)
    (clusterSize : ℕ)
    (hweight : ∀ u ∈ L ∩ C.O, ∀ v ∈ R.neighborFinset u,
      weight u v ≤ clusterSize)
    (hlargeDegree : ∀ u ∈ L ∩ C.O,
      D ≤ weightedReducedDegree R weight u) :
    ∃ A ∈ L ∩ C.O, ∃ B ∈ L ∩ C.O,
      R.Adj A B ∧
      D - miss * clusterSize ≤ matchingWeightedCapacity R C.M weight A ∧
      D - miss * clusterSize ≤ matchingWeightedCapacity R C.M weight B := by
  obtain ⟨A, hA, B, hB, hAB⟩ := C.adjacentLarge
  refine ⟨A, hA, B, hB, hAB, ?_, ?_⟩
  · exact claim67_weightedDegree_sub_error_le_matchingCapacity
      C weight (Finset.mem_inter.mp hA).2 clusterSize (hweight A hA)
        (hlargeDegree A hA)
  · exact claim67_weightedDegree_sub_error_le_matchingCapacity
      C weight (Finset.mem_inter.mp hB).2 clusterSize (hweight B hB)
        (hlargeDegree B hB)

/-!
The remaining analytic assertion of Lemma 6.5 is that regular pairs realize
the numerical capacity as an actual forest embedding.  We expose that single
interface explicitly, so all later uses can remain independent of the
internal representation of an ordered forest.
-/

/-- Abstract interface for the already-prepared forest embedding supplied by
Zhao's Lemma 5.8.  It deliberately quantifies over the exact source and host
graphs, rather than asserting an unrestricted global theorem. -/
def ForestCapacityEmbeddingProperty {τ V : Type*}
    (T : SimpleGraph τ) (G : SimpleGraph V) (capacityA capacityB : ℕ) : Prop :=
  ∀ partA partB : SimpleGraph τ,
    T ≤ partA ⊔ partB →
    Nat.card partA.edgeSet ≤ capacityA →
    Nat.card partB.edgeSet ≤ capacityB →
    T ⊑ G

/-- Lemma 6.5 Part 1 at its clean interface: once the two forest sizes fit
the matching capacities, the forest-capacity embedding property gives the
desired tree copy. -/
theorem zhaoLemma6_5_part1_of_capacity
    {τ V : Type*} [Fintype τ]
    (T : SimpleGraph τ) (G : SimpleGraph V)
    (partA partB : SimpleGraph τ) (capacityA capacityB : ℕ)
    (hproperty : ForestCapacityEmbeddingProperty T G capacityA capacityB)
    (hcover : T ≤ partA ⊔ partB)
    (hA : Nat.card partA.edgeSet ≤ capacityA)
    (hB : Nat.card partB.edgeSet ≤ capacityB) :
    T ⊑ G :=
  hproperty partA partB hcover hA hB

/-- End-to-end interface from Claim 6.7 to Lemma 6.5 Part 1.  The matching
certificate supplies adjacent large clusters and their two numerical
capacities; if the two forest parts fit below the common lower bound, the
regular-pair embedding property finishes the tree copy. -/
theorem zhaoLemma6_5_of_claim67_weightedCapacity
    {ι τ V : Type*} [Fintype ι] [DecidableEq ι] [Fintype τ]
    {R : SimpleGraph ι} [DecidableRel R.Adj] {L : Finset ι} {miss D : ℕ}
    (C : Claim67Certificate R L miss) (weight : ι → ι → ℕ)
    (clusterSize : ℕ)
    (hweight : ∀ u ∈ L ∩ C.O, ∀ v ∈ R.neighborFinset u,
      weight u v ≤ clusterSize)
    (hlargeDegree : ∀ u ∈ L ∩ C.O,
      D ≤ weightedReducedDegree R weight u)
    (T : SimpleGraph τ) (G : SimpleGraph V)
    (partA partB : SimpleGraph τ)
    (hcover : T ≤ partA ⊔ partB)
    (hsizeA : Nat.card partA.edgeSet ≤ D - miss * clusterSize)
    (hsizeB : Nat.card partB.edgeSet ≤ D - miss * clusterSize)
    (hproperty : ∀ A ∈ L ∩ C.O, ∀ B ∈ L ∩ C.O, R.Adj A B →
      ForestCapacityEmbeddingProperty T G
        (matchingWeightedCapacity R C.M weight A)
        (matchingWeightedCapacity R C.M weight B)) :
    T ⊑ G := by
  obtain ⟨A, hA, B, hB, hAB, hcapA, hcapB⟩ :=
    claim67_exists_adjacentLarge_with_weighted_capacity
      C weight clusterSize hweight hlargeDegree
  exact zhaoLemma6_5_part1_of_capacity T G partA partB
    (matchingWeightedCapacity R C.M weight A)
    (matchingWeightedCapacity R C.M weight B)
    (hproperty A hA B hB hAB) hcover
    (hsizeA.trans hcapA) (hsizeB.trans hcapB)


end Erdos547b.ZhaoStability

#print axioms Erdos547b.ZhaoStability.evenHost_highDegree_count_preserved
#print axioms Erdos547b.ZhaoStability.claim67_exists_adjacentLarge_with_weighted_capacity
