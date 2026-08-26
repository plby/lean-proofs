/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos547b.Claim67
import ErdosProblems.Erdos547b.Section6Dichotomy

open scoped SimpleGraph

noncomputable section

namespace Erdos547b.ZhaoEvenReducedPadding

open Finset SimpleGraph
open ZhaoStability ZhaoSection6Dichotomy

/-- The least even natural number greater than or equal to `card ι`. -/
def paddedCard (ι : Type*) [Fintype ι] : ℕ :=
  2 * ((Fintype.card ι + 1) / 2)

def paddedHalf (ι : Type*) [Fintype ι] : ℕ :=
  (Fintype.card ι + 1) / 2

theorem paddedCard_eq_two_mul (ι : Type*) [Fintype ι] :
    paddedCard ι = 2 * paddedHalf ι := rfl

theorem card_le_paddedCard (ι : Type*) [Fintype ι] :
    Fintype.card ι ≤ paddedCard ι := by
  unfold paddedCard
  omega

theorem paddedCard_le_card_add_one (ι : Type*) [Fintype ι] :
    paddedCard ι ≤ Fintype.card ι + 1 := by
  unfold paddedCard
  omega

theorem paddedCard_sub_card_le_one (ι : Type*) [Fintype ι] :
    paddedCard ι - Fintype.card ι ≤ 1 := by
  have := paddedCard_le_card_add_one ι
  omega

/-- The original indices together with zero or one new dummy index. -/
abbrev EvenPadding (ι : Type*) [Fintype ι] :=
  Sum ι (Fin (paddedCard ι - Fintype.card ι))

def padEmbedding {ι : Type*} [Fintype ι] : ι ↪ EvenPadding ι :=
  ⟨Sum.inl, Sum.inl_injective⟩

@[simp] theorem padEmbedding_apply {ι : Type*} [Fintype ι] (i : ι) :
    padEmbedding i = (Sum.inl i : EvenPadding ι) := rfl

theorem card_evenPadding (ι : Type*) [Fintype ι] :
    Fintype.card (EvenPadding ι) = 2 * paddedHalf ι := by
  simp only [EvenPadding, Fintype.card_sum, Fintype.card_fin]
  rw [← paddedCard_eq_two_mul]
  exact Nat.add_sub_of_le (card_le_paddedCard ι)

theorem card_dummy_le_one (ι : Type*) [Fintype ι] :
    Fintype.card (Fin (paddedCard ι - Fintype.card ι)) ≤ 1 := by
  simpa using paddedCard_sub_card_le_one ι

/-- Embed a finset of original indices into the padded index type. -/
def padFinset {ι : Type*} [Fintype ι] [DecidableEq ι]
    (I : Finset ι) : Finset (EvenPadding ι) :=
  I.map padEmbedding

@[simp] theorem mem_padFinset_inl {ι : Type*} [Fintype ι] [DecidableEq ι]
    {I : Finset ι} {i : ι} :
    (Sum.inl i : EvenPadding ι) ∈ padFinset I ↔ i ∈ I := by
  simp [padFinset, padEmbedding]

@[simp] theorem not_mem_padFinset_inr {ι : Type*} [Fintype ι]
    [DecidableEq ι] {I : Finset ι}
    (j : Fin (paddedCard ι - Fintype.card ι)) :
    (Sum.inr j : EvenPadding ι) ∉ padFinset I := by
  simp [padFinset, padEmbedding]

@[simp] theorem card_padFinset {ι : Type*} [Fintype ι] [DecidableEq ι]
    (I : Finset ι) : (padFinset I).card = I.card := by
  simp [padFinset]

theorem padFinset_mono {ι : Type*} [Fintype ι] [DecidableEq ι]
    {I J : Finset ι} (hIJ : I ⊆ J) : padFinset I ⊆ padFinset J := by
  intro x hx
  obtain ⟨i, hi, rfl⟩ := Finset.mem_map.mp hx
  exact Finset.mem_map.mpr ⟨i, hIJ hi, rfl⟩

theorem padFinset_disjoint {ι : Type*} [Fintype ι] [DecidableEq ι]
    {I J : Finset ι} (hIJ : Disjoint I J) :
    Disjoint (padFinset I) (padFinset J) := by
  rw [Finset.disjoint_left] at hIJ ⊢
  rintro x hxI hxJ
  obtain ⟨i, hiI, hix⟩ := Finset.mem_map.mp hxI
  obtain ⟨j, hjJ, hjx⟩ := Finset.mem_map.mp hxJ
  have hij : i = j := (padEmbedding.injective (hix.trans hjx.symm))
  subst j
  exact hIJ hiI hjJ

/-- Extend the reduced graph, leaving every dummy index isolated. -/
def padGraph {ι : Type*} [Fintype ι]
    (R : SimpleGraph ι) : SimpleGraph (EvenPadding ι) :=
  R.map padEmbedding

instance padGraph.instDecidableRel {ι : Type*} [Fintype ι] [DecidableEq ι]
    (R : SimpleGraph ι) [DecidableRel R.Adj] :
    DecidableRel (padGraph R).Adj := by
  unfold padGraph
  infer_instance

@[simp] theorem padGraph_adj_inl {ι : Type*} [Fintype ι]
    [DecidableEq ι] (R : SimpleGraph ι) (i j : ι) :
    (padGraph R).Adj (Sum.inl i) (Sum.inl j) ↔ R.Adj i j := by
  exact SimpleGraph.map_adj_apply

@[simp] theorem padGraph_not_adj_inr_left {ι : Type*} [Fintype ι]
    [DecidableEq ι] (R : SimpleGraph ι)
    (d : Fin (paddedCard ι - Fintype.card ι)) (x : EvenPadding ι) :
    ¬(padGraph R).Adj (Sum.inr d) x := by
  rw [padGraph, SimpleGraph.map_adj padEmbedding R]
  rintro ⟨i, j, hij, hi, hj⟩
  cases hi

@[simp] theorem padGraph_not_adj_inr_right {ι : Type*} [Fintype ι]
    [DecidableEq ι] (R : SimpleGraph ι)
    (x : EvenPadding ι) (d : Fin (paddedCard ι - Fintype.card ι)) :
    ¬(padGraph R).Adj x (Sum.inr d) := by
  exact fun h => padGraph_not_adj_inr_left R d x h.symm

theorem neighborFinset_padGraph_inl {ι : Type*} [Fintype ι]
    [DecidableEq ι] (R : SimpleGraph ι) [DecidableRel R.Adj] (i : ι) :
    (padGraph R).neighborFinset (Sum.inl i) =
      (R.neighborFinset i).map padEmbedding := by
  ext x
  cases x with
  | inl j => simp [SimpleGraph.mem_neighborFinset]
  | inr d => simp [SimpleGraph.mem_neighborFinset]

@[simp] theorem degree_padGraph_inl {ι : Type*} [Fintype ι]
    [DecidableEq ι] (R : SimpleGraph ι) [DecidableRel R.Adj] (i : ι) :
    (padGraph R).degree (Sum.inl i) = R.degree i := by
  change ((padGraph R).neighborFinset (Sum.inl i)).card =
    (R.neighborFinset i).card
  rw [neighborFinset_padGraph_inl]
  simp

@[simp] theorem degree_padGraph_inr {ι : Type*} [Fintype ι]
    [DecidableEq ι] (R : SimpleGraph ι) [DecidableRel R.Adj]
    (d : Fin (paddedCard ι - Fintype.card ι)) :
    (padGraph R).degree (Sum.inr d) = 0 := by
  rw [← (padGraph R).card_neighborFinset_eq_degree]
  rw [Finset.card_eq_zero]
  ext x
  simp [SimpleGraph.mem_neighborFinset]

def pairInclude {ι : Type*} [Fintype ι] :
    ι × ι ↪ EvenPadding ι × EvenPadding ι :=
  padEmbedding.prodMap padEmbedding

theorem interedges_padGraph {ι : Type*} [Fintype ι] [DecidableEq ι]
    (R : SimpleGraph ι) [DecidableRel R.Adj] (I J : Finset ι) :
    (padGraph R).interedges (padFinset I) (padFinset J) =
      (R.interedges I J).map pairInclude := by
  ext p
  cases p with
  | mk x y =>
      cases x with
      | inl i =>
          cases y with
          | inl j => simp [SimpleGraph.mem_interedges_iff, pairInclude]
          | inr d => simp [SimpleGraph.mem_interedges_iff, pairInclude]
      | inr d => simp [SimpleGraph.mem_interedges_iff, pairInclude]

@[simp] theorem card_interedges_padGraph {ι : Type*} [Fintype ι]
    [DecidableEq ι] (R : SimpleGraph ι) [DecidableRel R.Adj]
    (I J : Finset ι) :
    ((padGraph R).interedges (padFinset I) (padFinset J)).card =
      (R.interedges I J).card := by
  rw [interedges_padGraph]
  simp

theorem interedges_padGraph_complement {ι : Type*} [Fintype ι]
    [DecidableEq ι] (R : SimpleGraph ι) [DecidableRel R.Adj]
    (I : Finset ι) :
    ((padGraph R).interedges (padFinset I)
      (Finset.univ \ padFinset I)).card =
        (R.interedges I (Finset.univ \ I)).card := by
  let J := Finset.univ \ I
  have hsub : (padGraph R).interedges (padFinset I)
      (Finset.univ \ padFinset I) ⊆
        (padGraph R).interedges (padFinset I) (padFinset J) := by
    intro p hp
    have hp' := (SimpleGraph.mem_interedges_iff (padGraph R)).mp hp
    obtain ⟨j, hj, hy⟩ := Finset.mem_map.mp <|
      (by
        have hadj := hp'.2.2
        rw [padGraph, SimpleGraph.map_adj padEmbedding R] at hadj
        obtain ⟨i, j, hij, hix, hjy⟩ := hadj
        exact Finset.mem_map.mpr ⟨j, Finset.mem_univ _, hjy⟩ :
          p.2 ∈ padFinset (Finset.univ : Finset ι))
    have hjnot : j ∉ I := by
      intro hjI
      exact (Finset.mem_sdiff.mp hp'.2.1).2
        (Finset.mem_map.mpr ⟨j, hjI, hy⟩)
    apply (SimpleGraph.mem_interedges_iff (padGraph R)).mpr
    exact ⟨hp'.1, Finset.mem_map.mpr
      ⟨j, Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hjnot⟩, hy⟩, hp'.2.2⟩
  have hrev : (padGraph R).interedges (padFinset I) (padFinset J) ⊆
      (padGraph R).interedges (padFinset I)
        (Finset.univ \ padFinset I) := by
    intro p hp
    have hp' := (SimpleGraph.mem_interedges_iff (padGraph R)).mp hp
    apply (SimpleGraph.mem_interedges_iff (padGraph R)).mpr
    refine ⟨hp'.1, Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, ?_⟩, hp'.2.2⟩
    intro hyI
    obtain ⟨j, hjJ, hjy⟩ := Finset.mem_map.mp hp'.2.1
    obtain ⟨i, hiI, hiy⟩ := Finset.mem_map.mp hyI
    have hji : j = i := padEmbedding.injective (hjy.trans hiy.symm)
    subst i
    exact (Finset.mem_sdiff.mp hjJ).2 hiI
  rw [Finset.Subset.antisymm hsub hrev]
  exact card_interedges_padGraph R I J

/-- Extend a cluster assignment; dummy indices receive no vertices. -/
def padAssignment {V ι : Type*} [Fintype ι]
    (P : ClusterAssignment V ι) : ClusterAssignment V (EvenPadding ι) :=
  fun v => (P v).map Sum.inl

def padCluster {V ι : Type*} [Fintype ι]
    (C : ι → Finset V) : EvenPadding ι → Finset V
  | Sum.inl i => C i
  | Sum.inr _ => ∅

/-- Padding commutes with formation of the concrete regularity reduced graph,
provided the density cutoff is positive.  Thus the new vertices are not only
isolated in the transported graph: they are literally the empty-cluster
vertices of the padded regularity reduced graph. -/
theorem padGraph_regularityReducedGraph
    {V ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (C : ι → Finset V) (epsilon d : ℚ) (hd : 0 < d) :
    padGraph (regularityReducedGraph G C epsilon d) =
      regularityReducedGraph G (padCluster C) epsilon d := by
  ext x y
  cases x with
  | inl i =>
      cases y with
      | inl j => simp [padCluster]
      | inr e =>
          simp [padCluster, regularityReducedGraph_adj,
            G.edgeDensity_empty_right, not_le_of_gt hd]
  | inr e =>
      cases y with
      | inl j =>
          simp [padCluster, regularityReducedGraph_adj,
            G.edgeDensity_empty_left, not_le_of_gt hd]
      | inr f =>
          simp [padCluster, regularityReducedGraph_adj,
            G.edgeDensity_empty_left, not_le_of_gt hd]

@[simp] theorem exceptionalVertices_padAssignment
    {V ι : Type*} [Fintype V] [Fintype ι]
    [DecidableEq V] [DecidableEq ι] (P : ClusterAssignment V ι) :
    exceptionalVertices (padAssignment P) = exceptionalVertices P := by
  ext v
  simp [padAssignment, mem_exceptionalVertices]

@[simp] theorem clusterVertices_padAssignment_inl
    {V ι : Type*} [Fintype V] [Fintype ι]
    [DecidableEq V] [DecidableEq ι] (P : ClusterAssignment V ι) (i : ι) :
    clusterVertices (padAssignment P) (Sum.inl i) = clusterVertices P i := by
  ext v
  simp [padAssignment, mem_clusterVertices]

@[simp] theorem clusterVertices_padAssignment_inr
    {V ι : Type*} [Fintype V] [Fintype ι]
    [DecidableEq V] [DecidableEq ι] (P : ClusterAssignment V ι)
    (d : Fin (paddedCard ι - Fintype.card ι)) :
    clusterVertices (padAssignment P) (Sum.inr d) = ∅ := by
  ext v
  simp [padAssignment, mem_clusterVertices]

theorem clusterVertices_padAssignment
    {V ι : Type*} [Fintype V] [Fintype ι]
    [DecidableEq V] [DecidableEq ι] (P : ClusterAssignment V ι) :
    clusterVertices (padAssignment P) = padCluster (clusterVertices P) := by
  funext i
  cases i <;> simp [padCluster]

theorem padGraph_regularityReducedGraph_clusterVertices
    {V ι : Type*} [Fintype V] [Fintype ι]
    [DecidableEq V] [DecidableEq ι]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (P : ClusterAssignment V ι) (epsilon d : ℚ) (hd : 0 < d) :
    padGraph (regularityReducedGraph G (clusterVertices P) epsilon d) =
      regularityReducedGraph G
        (clusterVertices (padAssignment P)) epsilon d := by
  rw [clusterVertices_padAssignment]
  exact padGraph_regularityReducedGraph G (clusterVertices P) epsilon d hd

@[simp] theorem clusterUnion_padFinset
    {V ι : Type*} [Fintype V] [Fintype ι]
    [DecidableEq V] [DecidableEq ι]
    (P : ClusterAssignment V ι) (I : Finset ι) :
    clusterUnion (padAssignment P) (padFinset I) = clusterUnion P I := by
  ext v
  simp [mem_clusterUnion, padAssignment]

@[simp] theorem clusterUnion_padComplement
    {V ι : Type*} [Fintype V] [Fintype ι]
    [DecidableEq V] [DecidableEq ι]
    (P : ClusterAssignment V ι) (I : Finset ι) :
    clusterUnion (padAssignment P) (Finset.univ \ padFinset I) =
      clusterUnion P (Finset.univ \ I) := by
  ext v
  simp only [mem_clusterUnion, Finset.mem_sdiff, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨x, hxnot, hvx⟩
    cases x with
    | inl i =>
        refine ⟨i, ?_, ?_⟩
        · simpa using hxnot
        · simpa [padAssignment] using hvx
    | inr d => simp [padAssignment] at hvx
  · rintro ⟨i, hi, hvi⟩
    refine ⟨Sum.inl i, ?_, ?_⟩
    · simpa using hi
    · simpa [padAssignment] using hvi

/-- Every cleaned host edge still respects the padded reduced graph. -/
theorem edgesRespect_pad
    {V ι : Type*} [Fintype ι] [DecidableEq ι]
    (P : ClusterAssignment V ι) (H : SimpleGraph V) (R : SimpleGraph ι)
    (hrespect : EdgesRespectReducedGraph P H R) :
    EdgesRespectReducedGraph (padAssignment P) H (padGraph R) := by
  intro u v i j hui hvj huv
  cases i with
  | inl i =>
      cases j with
      | inl j =>
          rw [padGraph_adj_inl]
          apply hrespect
          · simpa [padAssignment] using hui
          · simpa [padAssignment] using hvj
          · exact huv
      | inr d => simp [padAssignment] at hvj
  | inr d => simp [padAssignment] at hui

/-- Direct Claim 6.7 consumer on the padded graph. -/
theorem exists_claim67Certificate_of_padding
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (R : SimpleGraph ι) [DecidableRel R.Adj]
    (L : Finset ι) (c : ℕ)
    (hL_card : paddedHalf ι - c ≤ L.card)
    (hL_degree : ∀ v ∈ L, paddedHalf ι - c ≤ R.degree v)
    (hL_nonindependent : ¬ R.IsIndepSet (L : Set ι)) :
    Nonempty (Claim67Certificate (padGraph R) (padFinset L) (2 * c + 1)) := by
  apply ZhaoStability.exists_claim67Certificate_of_reducedGraph
    (padGraph R) (padFinset L) (paddedHalf ι) c
  · exact card_evenPadding ι
  · simpa using hL_card
  · intro v hv
    cases v with
    | inl i =>
        simpa using hL_degree i (by simpa using hv)
    | inr d => simp at hv
  · intro hind
    apply hL_nonindependent
    rw [SimpleGraph.isIndepSet_iff] at hind ⊢
    intro i hi j hj hij
    have hni : ¬ (padGraph R).Adj (Sum.inl i) (Sum.inl j) :=
      hind
        (show Sum.inl i ∈ (padFinset L : Set (EvenPadding ι)) by simpa using hi)
        (show Sum.inl j ∈ (padFinset L : Set (EvenPadding ι)) by simpa using hj)
        (fun h => hij (Sum.inl_injective h))
    simpa using hni

#print axioms card_evenPadding
#print axioms degree_padGraph_inl
#print axioms card_interedges_padGraph
#print axioms interedges_padGraph_complement
#print axioms clusterUnion_padFinset
#print axioms clusterUnion_padComplement
#print axioms padGraph_regularityReducedGraph_clusterVertices
#print axioms edgesRespect_pad
#print axioms exists_claim67Certificate_of_padding

end Erdos547b.ZhaoEvenReducedPadding
