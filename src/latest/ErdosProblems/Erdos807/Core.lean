/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import Mathlib

/-!
# Biclique partitions of finite simple graphs

This file supplies the deterministic graph-theoretic infrastructure used in the
formalization of Erdős Problem 807.  A `Biclique G` is an actual complete
bipartite subgraph of `G`, specified by its two (disjoint) shores.  A biclique
partition is a list of such subgraphs whose edge sets are pairwise disjoint and
whose union is exactly the edge set of `G`.
-/

open Finset
open scoped SimpleGraph

noncomputable section

namespace Erdos807

variable {V : Type*} [Fintype V] [DecidableEq V]

attribute [local instance] Classical.propDecidable

/-- A canonical, noncomputable finite edge set.  Unlike `SimpleGraph.edgeFinset`,
this definition does not expose a chosen decidability instance in its type. -/
noncomputable def graphEdges (G : SimpleGraph V) : Finset (Sym2 V) := by
  classical
  exact G.edgeFinset

@[simp] lemma mem_graphEdges {G : SimpleGraph V} {e : Sym2 V} :
    e ∈ graphEdges G ↔ e ∈ G.edgeSet := by
  classical
  simp [graphEdges]

@[simp] lemma coe_graphEdges (G : SimpleGraph V) :
    (graphEdges G : Set (Sym2 V)) = G.edgeSet := by
  ext e
  simp

/-- A complete bipartite subgraph of `G`, with its two shores explicitly recorded. -/
structure Biclique (G : SimpleGraph V) where
  left : Finset V
  right : Finset V
  disjoint : Disjoint left right
  complete : ∀ u ∈ left, ∀ v ∈ right, G.Adj u v

namespace Biclique

variable {G : SimpleGraph V}

/-- Build a biclique from set-valued shores.  This is the bridge used when a
graph construction is naturally presented with `Set` shores (for example via
`SimpleGraph.between`). -/
noncomputable def ofSets (G : SimpleGraph V) (L R : Set V) (hLR : Disjoint L R)
    (hcomplete : ∀ u ∈ L, ∀ v ∈ R, G.Adj u v) : Biclique G := by
  classical
  exact
    { left := L.toFinset
      right := R.toFinset
      disjoint := by
        rw [Finset.disjoint_left]
        intro v hvL hvR
        exact Set.disjoint_left.mp hLR (Set.mem_toFinset.mp hvL) (Set.mem_toFinset.mp hvR)
      complete := by
        intro u hu v hv
        exact hcomplete u (Set.mem_toFinset.mp hu) v (Set.mem_toFinset.mp hv) }

@[simp] lemma ofSets_left (G : SimpleGraph V) (L R : Set V) (hLR : Disjoint L R)
    (hcomplete : ∀ u ∈ L, ∀ v ∈ R, G.Adj u v) :
    (ofSets G L R hLR hcomplete).left = L.toFinset := by
  classical
  rfl

@[simp] lemma ofSets_right (G : SimpleGraph V) (L R : Set V) (hLR : Disjoint L R)
    (hcomplete : ∀ u ∈ L, ∀ v ∈ R, G.Adj u v) :
    (ofSets G L R hLR hcomplete).right = R.toFinset := by
  classical
  rfl

/-- The unordered edge set of a biclique. -/
def edges (B : Biclique G) : Finset (Sym2 V) :=
  B.left.image₂ (fun u v ↦ s(u, v)) B.right

@[simp] lemma mem_edges {B : Biclique G} {e : Sym2 V} :
    e ∈ B.edges ↔ ∃ u ∈ B.left, ∃ v ∈ B.right, s(u, v) = e := by
  simp [edges]

@[simp] lemma mem_edges_ofSets (G : SimpleGraph V) (L R : Set V)
    (hLR : Disjoint L R) (hcomplete : ∀ u ∈ L, ∀ v ∈ R, G.Adj u v)
    {e : Sym2 V} :
    e ∈ (ofSets G L R hLR hcomplete).edges ↔
      ∃ u ∈ L, ∃ v ∈ R, s(u, v) = e := by
  classical
  simp only [mem_edges, ofSets_left, ofSets_right, Set.mem_toFinset]

lemma edges_subset_graphEdges (B : Biclique G) :
    B.edges ⊆ graphEdges G := by
  intro e he
  rw [mem_edges] at he
  obtain ⟨u, hu, v, hv, rfl⟩ := he
  rw [mem_graphEdges, SimpleGraph.mem_edgeSet]
  exact B.complete u hu v hv

/-- The star with centre `v` and leaves `G`-neighbours of `v` lying in `S`. -/
def star (G : SimpleGraph V) [DecidableRel G.Adj] (v : V) (S : Finset V) : Biclique G where
  left := {v}
  right := G.neighborFinset v ∩ S
  disjoint := by
    rw [Finset.disjoint_left]
    simp
  complete := by
    intro u hu w hw
    simp only [Finset.mem_singleton] at hu
    subst u
    exact (G.mem_neighborFinset v w).mp (Finset.mem_inter.mp hw).1

@[simp] lemma mem_star_edges [DecidableRel G.Adj] {v w : V} {S : Finset V} :
    s(v, w) ∈ (star G v S).edges ↔ w ∈ S ∧ G.Adj v w := by
  constructor
  · simp only [mem_edges, star, Finset.mem_singleton, Finset.mem_inter,
      SimpleGraph.mem_neighborFinset]
    rintro ⟨u, rfl, x, ⟨hxG, hxS⟩, he⟩
    have h := Sym2.eq_iff.mp he
    rcases h with (h | h)
    · exact ⟨h.2 ▸ hxS, h.2 ▸ hxG⟩
    · exact False.elim (G.loopless.irrefl _ (h.2 ▸ hxG))
  · rintro ⟨hwS, hvw⟩
    exact mem_edges.mpr ⟨v, Finset.mem_singleton.mpr rfl, w, by
      exact Finset.mem_inter.mpr ⟨(G.mem_neighborFinset v w).mpr hvw, hwS⟩, rfl⟩

/-- A single graph edge, viewed as a one-edge complete bipartite graph. -/
def singletonEdge (G : SimpleGraph V) {u v : V} (huv : G.Adj u v) : Biclique G where
  left := {u}
  right := {v}
  disjoint := by simp [huv.ne]
  complete := by
    intro a ha b hb
    simp only [Finset.mem_singleton] at ha hb
    subst a
    subst b
    exact huv

@[simp] lemma edges_singletonEdge (G : SimpleGraph V) {u v : V} (huv : G.Adj u v) :
    (singletonEdge G huv).edges = {s(u, v)} := by
  ext e
  simp [singletonEdge, edges]

end Biclique

/-- The union of the edge finsets of a list of bicliques. -/
def coveredEdges {G : SimpleGraph V} (p : List (Biclique G)) : Finset (Sym2 V) :=
  p.foldr (fun B E ↦ B.edges ∪ E) ∅

@[simp] lemma coveredEdges_nil {G : SimpleGraph V} :
    coveredEdges ([] : List (Biclique G)) = ∅ := rfl

@[simp] lemma coveredEdges_cons {G : SimpleGraph V} (B : Biclique G)
    (p : List (Biclique G)) :
    coveredEdges (B :: p) = B.edges ∪ coveredEdges p := rfl

@[simp] lemma mem_coveredEdges {G : SimpleGraph V} {p : List (Biclique G)}
    {e : Sym2 V} :
    e ∈ coveredEdges p ↔ ∃ B ∈ p, e ∈ B.edges := by
  induction p with
  | nil => simp
  | cons B p ih => simp [ih]

/-- A list of bicliques partitions a specified finite set of edges. -/
def IsPartitionOn {G : SimpleGraph V} (E : Finset (Sym2 V))
    (p : List (Biclique G)) : Prop :=
  p.Pairwise (fun B C ↦ Disjoint B.edges C.edges) ∧ coveredEdges p = E

/-- A list of bicliques partitions all edges of `G`. -/
def IsBicliquePartition (G : SimpleGraph V)
    (p : List (Biclique G)) : Prop :=
  IsPartitionOn (graphEdges G) p

/-- Edges of `G` having both endpoints in `S`. -/
def edgesOn (G : SimpleGraph V) [DecidableRel G.Adj] (S : Finset V) : Finset (Sym2 V) :=
  (graphEdges G).filter fun e ↦ e.toFinset ⊆ S

@[simp] lemma mem_edgesOn {G : SimpleGraph V} [DecidableRel G.Adj]
    {S : Finset V} {e : Sym2 V} :
    e ∈ edgesOn G S ↔ e ∈ graphEdges G ∧ e.toFinset ⊆ S := by
  simp [edgesOn]

@[simp] lemma edgesOn_univ (G : SimpleGraph V) [DecidableRel G.Adj] :
    edgesOn G univ = graphEdges G := by
  ext e
  simp

lemma edgesOn_mono {G : SimpleGraph V} [DecidableRel G.Adj] {S T : Finset V}
    (hST : S ⊆ T) : edgesOn G S ⊆ edgesOn G T := by
  intro e he
  rw [mem_edgesOn] at he ⊢
  exact ⟨he.1, he.2.trans hST⟩

lemma Biclique.edges_subset_coveredEdges {G : SimpleGraph V} {B : Biclique G}
    {p : List (Biclique G)} (hB : B ∈ p) : B.edges ⊆ coveredEdges p := by
  induction p with
  | nil => simp at hB
  | cons C p ih =>
      simp only [List.mem_cons] at hB
      rw [coveredEdges_cons]
      rcases hB with rfl | hB
      · exact Finset.subset_union_left
      · exact (ih hB).trans Finset.subset_union_right

lemma IsPartitionOn.cons {G : SimpleGraph V} {E : Finset (Sym2 V)}
    {p : List (Biclique G)} (hp : IsPartitionOn E p) (B : Biclique G)
    (hd : Disjoint B.edges E) : IsPartitionOn (B.edges ∪ E) (B :: p) := by
  refine ⟨?_, by simp only [coveredEdges_cons, hp.2]⟩
  rw [List.pairwise_cons]
  refine ⟨?_, hp.1⟩
  intro C hC
  rw [Finset.disjoint_left] at hd ⊢
  intro e heB heC
  exact hd heB (hp.2 ▸ Biclique.edges_subset_coveredEdges hC heC)

/-- Every finite graph edge set has the tautological partition into one-edge
bicliques.  The additional clause records that every member really has one edge. -/
lemma exists_singletonEdge_partitionOn (G : SimpleGraph V) (E : Finset (Sym2 V))
    (hE : E ⊆ graphEdges G) :
    ∃ p : List (Biclique G), IsPartitionOn E p ∧
      (∀ B ∈ p, B.edges.card = 1) ∧ p.length = E.card := by
  induction E using Finset.induction_on with
  | empty =>
      exact ⟨[], by simp [IsPartitionOn], by simp, by simp⟩
  | @insert e E he ih =>
      have heG : e ∈ graphEdges G := hE (Finset.mem_insert_self e E)
      have hEG : E ⊆ graphEdges G :=
        fun x hx ↦ hE (Finset.mem_insert_of_mem hx)
      obtain ⟨p, hp, hsingle, hcard⟩ := ih hEG
      induction e using Sym2.inductionOn with
      | _ u v =>
          have huv : G.Adj u v := by
            simpa only [mem_graphEdges, SimpleGraph.mem_edgeSet] using heG
          let B : Biclique G := Biclique.singletonEdge G huv
          have hd : Disjoint B.edges E := by
            simpa [B, Biclique.edges_singletonEdge] using
              (Finset.disjoint_singleton_left.mpr he)
          refine ⟨B :: p, ?_, ?_, ?_⟩
          · simpa [B, Biclique.edges_singletonEdge] using hp.cons B hd
          · intro C hC
            simp only [List.mem_cons] at hC
            rcases hC with rfl | hC
            · simp [B, Biclique.edges_singletonEdge]
            · exact hsingle C hC
          · simp [hcard, Finset.card_insert_of_notMem he]

/-- The global singleton-edge partition. -/
lemma exists_singletonEdge_bicliquePartition (G : SimpleGraph V) :
    ∃ p : List (Biclique G), IsBicliquePartition G p ∧
      (∀ B ∈ p, B.edges.card = 1) ∧ p.length = (graphEdges G).card := by
  simpa [IsBicliquePartition] using
    exists_singletonEdge_partitionOn G (graphEdges G) (fun _ h ↦ h)

lemma disjoint_graphEdges_of_disjoint {H K : SimpleGraph V} (hHK : Disjoint H K) :
    Disjoint (graphEdges H) (graphEdges K) := by
  rw [← Finset.disjoint_coe, coe_graphEdges, coe_graphEdges,
    SimpleGraph.disjoint_edgeSet]
  exact hHK

lemma finset_sup_adj_iff (P : Finset (SimpleGraph V)) (u v : V) :
    (P.sup id).Adj u v ↔ ∃ H ∈ P, H.Adj u v := by
  induction P using Finset.induction_on with
  | empty => simp
  | @insert H P hH ih =>
      rw [Finset.sup_insert, SimpleGraph.sup_adj, ih]
      simp only [id_eq, Finset.mem_insert, exists_eq_or_imp]

/-- A graph which is literally `between L R ⊤` becomes a Core biclique
with exactly the same edge finset inside any ambient supergraph. -/
lemma exists_biclique_edges_eq_graphEdges_of_between
    {G H : SimpleGraph V} {L R : Set V} (hLR : Disjoint L R)
    (hbetween : H = SimpleGraph.between L R ⊤) (hHG : H ≤ G) :
    ∃ B : Biclique G, B.edges = graphEdges H := by
  have hcomplete : ∀ u ∈ L, ∀ v ∈ R, G.Adj u v := by
    intro u hu v hv
    apply hHG
    rw [hbetween, SimpleGraph.between_adj]
    exact ⟨by
      intro huv
      subst v
      exact Set.disjoint_left.mp hLR hu hv, Or.inl ⟨hu, hv⟩⟩
  let B : Biclique G := Biclique.ofSets G L R hLR hcomplete
  refine ⟨B, ?_⟩
  ext e
  induction e using Sym2.inductionOn with
  | _ a b =>
      rw [Biclique.mem_edges_ofSets, mem_graphEdges, SimpleGraph.mem_edgeSet,
        hbetween, SimpleGraph.between_adj]
      constructor
      · rintro ⟨u, hu, v, hv, he⟩
        have huv : u ≠ v := fun huv ↦
          Set.disjoint_left.mp hLR hu (huv ▸ hv)
        rw [Sym2.eq_iff] at he
        rcases he with (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
        · exact ⟨huv, Or.inl ⟨hu, hv⟩⟩
        · exact ⟨huv.symm, Or.inr ⟨hv, hu⟩⟩
      · rintro ⟨_, h | h⟩
        · exact ⟨a, h.1, b, h.2, rfl⟩
        · exact ⟨b, h.2, a, h.1, Sym2.eq_swap⟩

/-- Convert a finite edge-disjoint `SimpleGraph.between` decomposition into
an exact Core biclique partition, without mentioning any particular graph
construction such as `StructuredFamily`. -/
theorem exists_bicliquePartition_of_finset_between
    (G : SimpleGraph V) (P : Finset (SimpleGraph V))
    (hpieces : ∀ H ∈ P, ∃ L R : Set V, Disjoint L R ∧
      H = SimpleGraph.between L R ⊤)
    (hpair : ∀ H K, H ∈ P → K ∈ P → H ≠ K → Disjoint H K)
    (hsup : P.sup id = G) :
    ∃ p : List (Biclique G), IsBicliquePartition G p ∧ p.length = P.card := by
  have hle : ∀ H : {H // H ∈ P}, H.1 ≤ G := by
    intro H
    rw [← hsup]
    exact Finset.le_sup (f := id) H.property
  have hex : ∀ H : {H // H ∈ P},
      ∃ B : Biclique G, B.edges = graphEdges H.1 := by
    intro H
    obtain ⟨L, R, hLR, hbetween⟩ := hpieces H.1 H.property
    exact exists_biclique_edges_eq_graphEdges_of_between hLR hbetween (hle H)
  choose B hB using hex
  let p : List (Biclique G) := P.attach.toList.map B
  refine ⟨p, ?_, ?_⟩
  · constructor
    · dsimp [p]
      rw [List.pairwise_map]
      apply P.attach.nodup_toList.pairwise_of_forall_ne
      intro H hHP K hKP hHK
      rw [hB H, hB K]
      apply disjoint_graphEdges_of_disjoint
      apply hpair H.1 K.1 H.property K.property
      intro h
      exact hHK (Subtype.ext h)
    · ext e
      rw [mem_coveredEdges]
      constructor
      · rintro ⟨C, hCp, heC⟩
        simp only [p, List.mem_map] at hCp
        obtain ⟨H, hHP, rfl⟩ := hCp
        rw [hB H, mem_graphEdges] at heC
        rw [mem_graphEdges]
        exact (SimpleGraph.edgeSet_subset_edgeSet.mpr (hle H)) heC
      · intro heG
        induction e using Sym2.inductionOn with
        | _ u v =>
            have hadjG : G.Adj u v := by
              simpa only [mem_graphEdges, SimpleGraph.mem_edgeSet] using heG
            have hadjSup : (P.sup id).Adj u v := by
              rw [hsup]
              exact hadjG
            obtain ⟨H, hHP, hHadj⟩ := (finset_sup_adj_iff P u v).mp hadjSup
            let H' : {H // H ∈ P} := ⟨H, hHP⟩
            refine ⟨B H', ?_, ?_⟩
            · simp [p, H']
            · rw [hB H', mem_graphEdges, SimpleGraph.mem_edgeSet]
              exact hHadj
  · simp [p]

lemma star_edges_eq_sdiff_edgesOn (G : SimpleGraph V) [DecidableRel G.Adj]
    (v : V) (S : Finset V) (hvS : v ∉ S) :
    (Biclique.star G v S).edges = edgesOn G (insert v S) \ edgesOn G S := by
  ext e
  induction e using Sym2.inductionOn with
  | _ a b =>
      simp only [Biclique.mem_edges, Biclique.star, Finset.mem_singleton,
        Finset.mem_inter, SimpleGraph.mem_neighborFinset, mem_sdiff, mem_edgesOn,
        mem_graphEdges, SimpleGraph.mem_edgeSet, Sym2.toFinset_mk_eq,
        Finset.insert_subset_iff, Finset.singleton_subset_iff, Finset.mem_insert]
      constructor
      · rintro ⟨u, huv, w, ⟨huw, hwS⟩, he⟩
        subst u
        rw [Sym2.eq_iff] at he
        rcases he with (⟨hva, hwb⟩ | ⟨hvb, hwa⟩)
        · subst a
          subst b
          exact ⟨⟨huw, ⟨Or.inl rfl, Or.inr hwS⟩⟩,
            fun h ↦ hvS h.2.1⟩
        · subst b
          subst a
          exact ⟨⟨huw.symm, ⟨Or.inr hwS, Or.inl rfl⟩⟩,
            fun h ↦ hvS h.2.2⟩
      · rintro ⟨⟨hab, ⟨ha, hb⟩⟩, hn⟩
        rcases ha with hva | haS
        · subst a
          exact ⟨v, rfl, b, ⟨hab, hb.resolve_left (fun h ↦ hab.ne h.symm)⟩, rfl⟩
        · rcases hb with hvb | hbS
          · rw [hvb] at hab ⊢
            exact ⟨v, rfl, a, ⟨hab.symm, haS⟩, Sym2.eq_swap⟩
          · exact False.elim (hn ⟨hab, ⟨haS, hbS⟩⟩)

lemma edgesOn_insert_eq (G : SimpleGraph V) [DecidableRel G.Adj]
    (v : V) (S : Finset V) (hvS : v ∉ S) :
    edgesOn G (insert v S) = (Biclique.star G v S).edges ∪ edgesOn G S := by
  rw [star_edges_eq_sdiff_edgesOn G v S hvS, Finset.sdiff_union_of_subset]
  exact edgesOn_mono (Finset.subset_insert v S)

lemma star_edges_disjoint_edgesOn (G : SimpleGraph V) [DecidableRel G.Adj]
    (v : V) (S : Finset V) (hvS : v ∉ S) :
    Disjoint (Biclique.star G v S).edges (edgesOn G S) := by
  rw [star_edges_eq_sdiff_edgesOn G v S hvS]
  exact Finset.sdiff_disjoint

/-- Add one new vertex to a partition, using its incident star as one new biclique. -/
lemma IsPartitionOn.extend_insert {G : SimpleGraph V} [DecidableRel G.Adj]
    {S : Finset V} {p : List (Biclique G)} (hp : IsPartitionOn (edgesOn G S) p)
    (v : V) (hvS : v ∉ S) :
    IsPartitionOn (edgesOn G (insert v S)) (Biclique.star G v S :: p) := by
  rw [edgesOn_insert_eq G v S hvS]
  exact hp.cons _ (star_edges_disjoint_edgesOn G v S hvS)

/-- Extend a partition on `S` across a disjoint set `T`, one star per new vertex. -/
lemma exists_partitionOn_union {G : SimpleGraph V} [DecidableRel G.Adj]
    {S T : Finset V} (hST : Disjoint S T) {p : List (Biclique G)}
    (hp : IsPartitionOn (edgesOn G S) p) :
    ∃ q : List (Biclique G),
      IsPartitionOn (edgesOn G (S ∪ T)) q ∧ q.length = p.length + T.card := by
  induction T using Finset.induction_on with
  | empty =>
      exact ⟨p, by simpa using hp, by simp⟩
  | @insert v T hvT ih =>
      have hvS : v ∉ S := by
        intro hv
        exact (Finset.disjoint_left.mp hST) hv (Finset.mem_insert_self v T)
      have hST' : Disjoint S T :=
        hST.mono_right (Finset.subset_insert v T)
      obtain ⟨q, hq, hqcard⟩ := ih hST'
      have hvST : v ∉ S ∪ T := by simp [hvS, hvT]
      refine ⟨Biclique.star G v (S ∪ T) :: q, ?_, ?_⟩
      · simpa [Finset.union_insert] using hq.extend_insert v hvST
      · simp [hqcard, Finset.card_insert_of_notMem hvT, Nat.add_assoc, Nat.add_comm,
          Nat.add_left_comm]

/-- A partition on an induced vertex set extends to all vertices with one star
for each vertex outside that set. -/
lemma exists_bicliquePartition_of_partitionOn {G : SimpleGraph V} [DecidableRel G.Adj]
    {S : Finset V} {p : List (Biclique G)} (hp : IsPartitionOn (edgesOn G S) p) :
    ∃ q : List (Biclique G), IsBicliquePartition G q ∧
      q.length = p.length + (Fintype.card V - S.card) := by
  have hdis : Disjoint S (univ \ S) := Finset.disjoint_sdiff
  obtain ⟨q, hq, hqcard⟩ := exists_partitionOn_union hdis hp
  refine ⟨q, ?_, ?_⟩
  · have hSuniv : S ∪ (univ \ S) = (univ : Finset V) := by
      rw [Finset.union_comm, Finset.sdiff_union_of_subset (Finset.subset_univ S)]
    simpa [IsBicliquePartition, hSuniv] using hq
  · rw [hqcard, Finset.card_sdiff_of_subset (Finset.subset_univ S), Finset.card_univ]

lemma edgesOn_eq_empty_of_isIndepSet {G : SimpleGraph V} [DecidableRel G.Adj]
    {S : Finset V} (hS : G.IsIndepSet (S : Set V)) : edgesOn G S = ∅ := by
  ext e
  induction e using Sym2.inductionOn with
  | _ a b =>
      simp only [mem_edgesOn, mem_graphEdges, SimpleGraph.mem_edgeSet,
        Sym2.toFinset_mk_eq, Finset.insert_subset_iff, Finset.singleton_subset_iff,
        Finset.notMem_empty, iff_false]
      rintro ⟨hab, haS, hbS⟩
      exact hS haS hbS hab.ne hab

/-- The standard star partition associated to an independent set. -/
lemma exists_star_bicliquePartition_of_isIndepSet
    {G : SimpleGraph V} [DecidableRel G.Adj] {S : Finset V}
    (hS : G.IsIndepSet (S : Set V)) :
    ∃ p : List (Biclique G), IsBicliquePartition G p ∧
      p.length = Fintype.card V - S.card := by
  have hp : IsPartitionOn (edgesOn G S) ([] : List (Biclique G)) := by
    constructor
    · simp
    · simpa [edgesOn_eq_empty_of_isIndepSet hS]
  obtain ⟨p, hp, hcard⟩ := exists_bicliquePartition_of_partitionOn hp
  exact ⟨p, hp, by simpa using hcard⟩

lemma exists_bicliquePartition (G : SimpleGraph V) :
    ∃ p : List (Biclique G), IsBicliquePartition G p := by
  obtain ⟨p, hp, _, _⟩ := exists_singletonEdge_bicliquePartition G
  exact ⟨p, hp⟩

/-- The bipartition number: the least length of an edge-disjoint biclique partition.
It is independent of any chosen decidability instance for adjacency. -/
noncomputable def bipartitionNumber (G : SimpleGraph V) : ℕ :=
  sInf {n : ℕ | ∃ p : List (Biclique G),
    IsBicliquePartition G p ∧ p.length = n}

lemma exists_bicliquePartition_card_eq (G : SimpleGraph V) :
    ∃ p : List (Biclique G),
      IsBicliquePartition G p ∧ p.length = bipartitionNumber G := by
  change sInf {n : ℕ | ∃ p : List (Biclique G),
    IsBicliquePartition G p ∧ p.length = n} ∈
      {n : ℕ | ∃ p : List (Biclique G),
        IsBicliquePartition G p ∧ p.length = n}
  apply csInf_mem
  obtain ⟨p, hp⟩ := exists_bicliquePartition G
  exact ⟨p.length, p, hp, rfl⟩

lemma bipartitionNumber_le_of_partition {G : SimpleGraph V}
    {p : List (Biclique G)} (hp : IsBicliquePartition G p) :
    bipartitionNumber G ≤ p.length :=
  csInf_le' ⟨p, hp, rfl⟩

lemma bipartitionNumber_minimal (G : SimpleGraph V) :
    (∃ p : List (Biclique G), IsBicliquePartition G p ∧
        p.length = bipartitionNumber G) ∧
      ∀ p : List (Biclique G), IsBicliquePartition G p →
        bipartitionNumber G ≤ p.length :=
  ⟨exists_bicliquePartition_card_eq G, fun _ hp ↦ bipartitionNumber_le_of_partition hp⟩

/-- The tautological upper bound by the number of edges. -/
lemma bipartitionNumber_le_card_graphEdges (G : SimpleGraph V) :
    bipartitionNumber G ≤ (graphEdges G).card := by
  obtain ⟨p, hp, _, hcard⟩ := exists_singletonEdge_bicliquePartition G
  rw [← hcard]
  exact bipartitionNumber_le_of_partition hp

/-- Direct numerical consequence of a finite edge-disjoint `between`
certificate. -/
theorem bipartitionNumber_le_card_of_finset_between
    (G : SimpleGraph V) (P : Finset (SimpleGraph V))
    (hpieces : ∀ H ∈ P, ∃ L R : Set V, Disjoint L R ∧
      H = SimpleGraph.between L R ⊤)
    (hpair : ∀ H K, H ∈ P → K ∈ P → H ≠ K → Disjoint H K)
    (hsup : P.sup id = G) : bipartitionNumber G ≤ P.card := by
  obtain ⟨p, hp, hcard⟩ :=
    exists_bicliquePartition_of_finset_between G P hpieces hpair hsup
  rw [← hcard]
  exact bipartitionNumber_le_of_partition hp

/-- Deterministic lifting in its most reusable ambient-edge form: any
partition of all edges with both endpoints in `S` extends by at most one star
for each vertex outside `S`. -/
theorem bipartitionNumber_le_card_sub_add_of_partitionOn
    {G : SimpleGraph V} [DecidableRel G.Adj] {S : Finset V}
    {p : List (Biclique G)} {r : ℕ} (hp : IsPartitionOn (edgesOn G S) p)
    (hpr : p.length ≤ r) :
    bipartitionNumber G ≤ Fintype.card V - S.card + r := by
  obtain ⟨q, hq, hqcard⟩ := exists_bicliquePartition_of_partitionOn hp
  calc
    bipartitionNumber G ≤ q.length := bipartitionNumber_le_of_partition hq
    _ = p.length + (Fintype.card V - S.card) := hqcard
    _ ≤ r + (Fintype.card V - S.card) := Nat.add_le_add_right hpr _
    _ = Fintype.card V - S.card + r := Nat.add_comm _ _

theorem bipartitionNumber_le_card_sub_add_of_partitionOn_eq
    {G : SimpleGraph V} [DecidableRel G.Adj] {S : Finset V}
    {p : List (Biclique G)} {r : ℕ} (hp : IsPartitionOn (edgesOn G S) p)
    (hpr : p.length = r) :
    bipartitionNumber G ≤ Fintype.card V - S.card + r :=
  bipartitionNumber_le_card_sub_add_of_partitionOn hp hpr.le

/-- The star upper bound from any independent set. -/
lemma bipartitionNumber_le_card_sub_card_of_isIndepSet
    {G : SimpleGraph V} [DecidableRel G.Adj] {S : Finset V}
    (hS : G.IsIndepSet (S : Set V)) :
    bipartitionNumber G ≤ Fintype.card V - S.card := by
  obtain ⟨p, hp, hcard⟩ := exists_star_bicliquePartition_of_isIndepSet hS
  rw [← hcard]
  exact bipartitionNumber_le_of_partition hp

/-! ### Lifting partitions of induced subgraphs -/

/-- The canonical embedding of the vertex type of an induced subgraph. -/
def inducedVertexEmbedding (S : Finset V) :
    {v : V // v ∈ (S : Set V)} ↪ V :=
  Function.Embedding.subtype _

namespace Biclique

/-- Regard a biclique of an induced subgraph as a biclique of the ambient graph. -/
def ofInduce {G : SimpleGraph V} (S : Finset V)
    (B : Biclique (G.induce (S : Set V))) : Biclique G where
  left := B.left.image Subtype.val
  right := B.right.image Subtype.val
  disjoint := by
    rw [Finset.disjoint_left]
    intro v hvL hvR
    simp only [Finset.mem_image] at hvL hvR
    obtain ⟨u, hu, rfl⟩ := hvL
    obtain ⟨w, hw, huw⟩ := hvR
    have : u = w := Subtype.ext huw.symm
    subst w
    exact (Finset.disjoint_left.mp B.disjoint) hu hw
  complete := by
    intro u hu v hv
    simp only [Finset.mem_image] at hu hv
    obtain ⟨u', hu', rfl⟩ := hu
    obtain ⟨v', hv', rfl⟩ := hv
    exact (SimpleGraph.induce_adj.mp (B.complete u' hu' v' hv'))

lemma edges_ofInduce {G : SimpleGraph V} (S : Finset V)
    (B : Biclique (G.induce (S : Set V))) :
    (ofInduce S B).edges = B.edges.map (inducedVertexEmbedding S).sym2Map := by
  ext e
  constructor
  · rw [mem_edges]
    rintro ⟨u, hu, v, hv, rfl⟩
    simp only [ofInduce, Finset.mem_image] at hu hv
    obtain ⟨u', hu', rfl⟩ := hu
    obtain ⟨v', hv', rfl⟩ := hv
    rw [Finset.mem_map]
    exact ⟨s(u', v'), mem_edges.mpr ⟨u', hu', v', hv', rfl⟩, rfl⟩
  · rw [Finset.mem_map]
    rintro ⟨e, he, rfl⟩
    rw [mem_edges] at he ⊢
    obtain ⟨u, hu, v, hv, rfl⟩ := he
    exact ⟨u.1, Finset.mem_image.mpr ⟨u, hu, rfl⟩,
      v.1, Finset.mem_image.mpr ⟨v, hv, rfl⟩, rfl⟩

end Biclique

lemma coveredEdges_map_ofInduce {G : SimpleGraph V} (S : Finset V)
    (p : List (Biclique (G.induce (S : Set V)))) :
    coveredEdges (p.map (Biclique.ofInduce S)) =
      (coveredEdges p).map (inducedVertexEmbedding S).sym2Map := by
  induction p with
  | nil => simp
  | cons B p ih =>
      simp only [List.map_cons, coveredEdges_cons, Biclique.edges_ofInduce, ih,
        Finset.map_union]

lemma edgesOn_eq_map_induce_graphEdges (G : SimpleGraph V) [DecidableRel G.Adj]
    (S : Finset V) :
    edgesOn G S = (graphEdges (G.induce (S : Set V))).map
      (inducedVertexEmbedding S).sym2Map := by
  ext e
  constructor
  · induction e using Sym2.inductionOn with
    | _ a b =>
        rw [mem_edgesOn]
        simp only [mem_graphEdges, SimpleGraph.mem_edgeSet,
          Sym2.toFinset_mk_eq, Finset.insert_subset_iff, Finset.singleton_subset_iff]
        rintro ⟨hab, haS, hbS⟩
        rw [Finset.mem_map]
        refine ⟨s(⟨a, haS⟩, ⟨b, hbS⟩), ?_, rfl⟩
        simpa only [mem_graphEdges, SimpleGraph.mem_edgeSet,
          SimpleGraph.induce_adj]
  · rw [Finset.mem_map]
    rintro ⟨e, he, rfl⟩
    induction e using Sym2.inductionOn with
    | _ a b =>
        change s(a.1, b.1) ∈ edgesOn G S
        have hab : G.Adj a.1 b.1 :=
          SimpleGraph.induce_adj.mp
            (show (G.induce (S : Set V)).Adj a b from mem_graphEdges.mp he)
        rw [mem_edgesOn]
        simpa only [mem_graphEdges, SimpleGraph.mem_edgeSet,
          Sym2.toFinset_mk_eq, Finset.insert_subset_iff,
          Finset.singleton_subset_iff] using ⟨hab, a.property, b.property⟩

/-- An edge-disjoint partition of an induced subgraph is an edge-disjoint
partition of the corresponding ambient edge set. -/
lemma IsBicliquePartition.map_induce {G : SimpleGraph V} [DecidableRel G.Adj]
    {S : Finset V} {p : List (Biclique (G.induce (S : Set V)))}
    (hp : IsBicliquePartition (G.induce (S : Set V)) p) :
    IsPartitionOn (edgesOn G S) (p.map (Biclique.ofInduce S)) := by
  constructor
  · rw [List.pairwise_map]
    simpa only [Biclique.edges_ofInduce, Finset.disjoint_map] using hp.1
  · rw [coveredEdges_map_ofInduce, hp.2]
    exact (edgesOn_eq_map_induce_graphEdges G S).symm

/-- **Deterministic induced-subgraph lifting.**  If the subgraph induced by
`S` has a biclique partition of length `r`, adding the other vertices as
stars gives a partition of `G` of length at most `|V| - |S| + r`. -/
theorem bipartitionNumber_le_card_sub_add_of_induce_partition
    {G : SimpleGraph V} [DecidableRel G.Adj] {S : Finset V}
    {p : List (Biclique (G.induce (S : Set V)))}
    (hp : IsBicliquePartition (G.induce (S : Set V)) p) :
    bipartitionNumber G ≤ Fintype.card V - S.card + p.length := by
  have hp' := hp.map_induce (G := G)
  obtain ⟨q, hq, hqcard⟩ := exists_bicliquePartition_of_partitionOn hp'
  apply (bipartitionNumber_le_of_partition hq).trans_eq
  rw [hqcard, List.length_map, Nat.add_comm]

/-- Numerical form of deterministic lifting, with the induced vertex and
partition cardinalities named `k` and `r`. -/
theorem bipartitionNumber_le_card_sub_add_of_induced_k_partition_r
    {G : SimpleGraph V} [DecidableRel G.Adj] {S : Finset V} {k r : ℕ}
    {p : List (Biclique (G.induce (S : Set V)))}
    (hS : S.card = k) (hp : IsBicliquePartition (G.induce (S : Set V)) p)
    (hpr : p.length = r) :
    bipartitionNumber G ≤ Fintype.card V - k + r := by
  simpa [← hS, ← hpr] using
    bipartitionNumber_le_card_sub_add_of_induce_partition hp

/-- Lifting expressed using the optimal partition of the induced subgraph. -/
theorem bipartitionNumber_le_card_sub_add_induce
    (G : SimpleGraph V) [DecidableRel G.Adj] (S : Finset V) :
    bipartitionNumber G ≤ Fintype.card V - S.card +
      bipartitionNumber (G.induce (S : Set V)) := by
  obtain ⟨p, hp, hcard⟩ :=
    exists_bicliquePartition_card_eq (G.induce (S : Set V))
  simpa [hcard] using
    bipartitionNumber_le_card_sub_add_of_induce_partition (G := G) hp

/-! ### Lifting along an arbitrary vertex embedding -/

section Comap

variable {W : Type*} [Fintype W] [DecidableEq W]

/-- The finite range of a vertex embedding. -/
def embeddingRangeFinset (e : W ↪ V) : Finset V :=
  Finset.univ.map e

@[simp] lemma card_embeddingRangeFinset (e : W ↪ V) :
    (embeddingRangeFinset e).card = Fintype.card W := by
  simp [embeddingRangeFinset]

namespace Biclique

/-- Transport a biclique in a pulled-back graph into the ambient graph. -/
def ofComap {G : SimpleGraph V} (e : W ↪ V) (B : Biclique (G.comap e)) : Biclique G where
  left := B.left.map e
  right := B.right.map e
  disjoint := (Finset.disjoint_map e).mpr B.disjoint
  complete := by
    intro u hu v hv
    rw [Finset.mem_map] at hu hv
    obtain ⟨u', hu', rfl⟩ := hu
    obtain ⟨v', hv', rfl⟩ := hv
    exact B.complete u' hu' v' hv'

lemma edges_ofComap {G : SimpleGraph V} (e : W ↪ V) (B : Biclique (G.comap e)) :
    (ofComap e B).edges = B.edges.map e.sym2Map := by
  ext x
  constructor
  · rw [mem_edges]
    rintro ⟨u, hu, v, hv, rfl⟩
    simp only [ofComap, Finset.mem_map] at hu hv
    obtain ⟨u', hu', rfl⟩ := hu
    obtain ⟨v', hv', rfl⟩ := hv
    rw [Finset.mem_map]
    exact ⟨s(u', v'), mem_edges.mpr ⟨u', hu', v', hv', rfl⟩, rfl⟩
  · rw [Finset.mem_map]
    rintro ⟨x, hx, rfl⟩
    rw [mem_edges] at hx ⊢
    obtain ⟨u, hu, v, hv, rfl⟩ := hx
    exact ⟨e u, Finset.mem_map.mpr ⟨u, hu, rfl⟩,
      e v, Finset.mem_map.mpr ⟨v, hv, rfl⟩, rfl⟩

end Biclique

lemma coveredEdges_map_ofComap {G : SimpleGraph V} (e : W ↪ V)
    (p : List (Biclique (G.comap e))) :
    coveredEdges (p.map (Biclique.ofComap e)) = (coveredEdges p).map e.sym2Map := by
  induction p with
  | nil => simp
  | cons B p ih =>
      simp only [List.map_cons, coveredEdges_cons, Biclique.edges_ofComap, ih,
        Finset.map_union]

lemma edgesOn_embeddingRangeFinset_eq_map_comap_graphEdges
    (G : SimpleGraph V) [DecidableRel G.Adj] (e : W ↪ V) :
    edgesOn G (embeddingRangeFinset e) = (graphEdges (G.comap e)).map e.sym2Map := by
  ext x
  constructor
  · induction x using Sym2.inductionOn with
    | _ a b =>
        rw [mem_edgesOn]
        simp only [mem_graphEdges, SimpleGraph.mem_edgeSet, Sym2.toFinset_mk_eq,
          Finset.insert_subset_iff, Finset.singleton_subset_iff]
        rintro ⟨hab, ha, hb⟩
        rw [embeddingRangeFinset, Finset.mem_map] at ha hb
        obtain ⟨a', _, rfl⟩ := ha
        obtain ⟨b', _, rfl⟩ := hb
        rw [Finset.mem_map]
        refine ⟨s(a', b'), ?_, rfl⟩
        simpa only [mem_graphEdges, SimpleGraph.mem_edgeSet]
  · rw [Finset.mem_map]
    rintro ⟨x, hx, rfl⟩
    induction x using Sym2.inductionOn with
    | _ a b =>
        change s(e a, e b) ∈ edgesOn G (embeddingRangeFinset e)
        have hab : G.Adj (e a) (e b) := by
          simpa only [mem_graphEdges, SimpleGraph.mem_edgeSet,
            SimpleGraph.comap_adj] using hx
        rw [mem_edgesOn]
        simpa only [mem_graphEdges, SimpleGraph.mem_edgeSet,
          Sym2.toFinset_mk_eq, Finset.insert_subset_iff, Finset.singleton_subset_iff,
          embeddingRangeFinset, Finset.mem_map, Finset.mem_univ, true_and] using
          ⟨hab, ⟨a, rfl⟩, ⟨b, rfl⟩⟩

lemma IsBicliquePartition.map_comap {G : SimpleGraph V} [DecidableRel G.Adj]
    (e : W ↪ V) {p : List (Biclique (G.comap e))}
    (hp : IsBicliquePartition (G.comap e) p) :
    IsPartitionOn (edgesOn G (embeddingRangeFinset e))
      (p.map (Biclique.ofComap e)) := by
  constructor
  · rw [List.pairwise_map]
    simpa only [Biclique.edges_ofComap, Finset.disjoint_map] using hp.1
  · rw [coveredEdges_map_ofComap, hp.2]
    exact (edgesOn_embeddingRangeFinset_eq_map_comap_graphEdges G e).symm

/-- Pullback/embedding form of deterministic lifting.  A partition of
`G.comap e` extends to `G` with at most one star for each vertex outside the
range of `e`. -/
theorem bipartitionNumber_le_card_sub_add_comap
    (G : SimpleGraph V) (e : W ↪ V) :
    bipartitionNumber G ≤ Fintype.card V - Fintype.card W +
      bipartitionNumber (G.comap e) := by
  classical
  obtain ⟨p, hp, hcard⟩ := exists_bicliquePartition_card_eq (G.comap e)
  have hp' := hp.map_comap (G := G) e
  have h := bipartitionNumber_le_card_sub_add_of_partitionOn_eq
    (r := bipartitionNumber (G.comap e)) hp' (by simpa using hcard)
  simpa using h

end Comap

end Erdos807
