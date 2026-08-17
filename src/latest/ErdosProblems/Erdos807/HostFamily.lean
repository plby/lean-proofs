import ErdosProblems.Erdos807.StructuredFamily
import ErdosProblems.Erdos807.Probability
import ErdosProblems.Erdos807.Core

/-!
# Structured witnesses inside a labelled host graph

This file transports the canonical family from `Fin (100 * r)` into labelled
host graphs.  Besides the increasing enumeration of an arbitrary vertex set,
it provides the globally stable bucket slots used by the overlap argument.
The full set of internal edge coordinates is prescribed, so its exact
probability follows from `RandomGraph.probability_prescribed`.  Injectivity of
the canonical matrix presentation then lets us sum the mutually exclusive
matrix events.
-/

open scoped BigOperators

namespace Erdos807
namespace HostFamily

open StructuredFamily

/-! ## Edge coordinates transported by an embedding -/

/-- Transport a non-diagonal unordered edge through an embedding. -/
def liftEdge {k n : ℕ} (e : Fin k ↪ Fin n) (a : RandomGraph.Edge k) :
    RandomGraph.Edge n :=
  ⟨Sym2.map e a.1, by
    intro h
    exact a.2 ((Sym2.isDiag_map e.injective).1 h)⟩

lemma liftEdge_injective {k n : ℕ} (e : Fin k ↪ Fin n) :
    Function.Injective (liftEdge e) := by
  intro a b hab
  apply Subtype.ext
  apply Sym2.map.injective e.injective
  exact congrArg Subtype.val hab

/-- The complete block of edge coordinates supported on the range of `e`. -/
def embeddingEdges {k n : ℕ} (e : Fin k ↪ Fin n) :
    Finset (RandomGraph.Edge n) :=
  Finset.univ.image (liftEdge e)

@[simp] theorem card_embeddingEdges {k n : ℕ} (e : Fin k ↪ Fin n) :
    (embeddingEdges e).card = k.choose 2 := by
  rw [embeddingEdges, Finset.card_image_iff.mpr]
  · have h := RandomGraph.card_allEdges k
    rw [RandomGraph.allEdges, Erdos565.RandomGraph.edgeUniverse] at h
    exact h
  · intro a _ b _ hab
    exact liftEdge_injective e hab

@[simp] lemma liftEdge_mem_embeddingEdges {k n : ℕ} (e : Fin k ↪ Fin n)
    (a : RandomGraph.Edge k) : liftEdge e a ∈ embeddingEdges e := by
  simp [embeddingEdges]

/-- The coordinates in `embeddingEdges e` which are edges of the transported
graph `H.map e`. -/
noncomputable def fixedEdges {k n : ℕ} (e : Fin k ↪ Fin n)
    (H : SimpleGraph (Fin k)) : Finset (RandomGraph.Edge n) := by
  classical
  exact (embeddingEdges e).filter fun a ↦ a.1 ∈ (H.map e).edgeSet

lemma fixedEdges_subset_embeddingEdges {k n : ℕ} (e : Fin k ↪ Fin n)
    (H : SimpleGraph (Fin k)) : fixedEdges e H ⊆ embeddingEdges e := by
  classical
  exact Finset.filter_subset _ _

@[simp] lemma liftEdge_mem_fixedEdges_iff {k n : ℕ} (e : Fin k ↪ Fin n)
    (H : SimpleGraph (Fin k)) (a : RandomGraph.Edge k) :
    liftEdge e a ∈ fixedEdges e H ↔ a.1 ∈ H.edgeSet := by
  classical
  rw [fixedEdges, Finset.mem_filter]
  simp only [liftEdge_mem_embeddingEdges, true_and]
  rcases a with ⟨a, ha⟩
  induction a using Sym2.inductionOn with
  | _ u v =>
      simp [liftEdge, SimpleGraph.mem_edgeSet]

@[simp] lemma liftEdge_mem_edges_iff {k n : ℕ} (e : Fin k ↪ Fin n)
    (G : SimpleGraph (Fin n)) (a : RandomGraph.Edge k) :
    liftEdge e a ∈ RandomGraph.edges G ↔ a.1 ∈ (G.comap e).edgeSet := by
  rw [RandomGraph.mem_edges]
  rcases a with ⟨a, ha⟩
  induction a using Sym2.inductionOn with
  | _ u v =>
      simp [liftEdge, SimpleGraph.mem_edgeSet]

/-- Prescribing the complete transported coordinate block is exactly equality
of the pulled-back graph with `H`. -/
theorem comap_eq_iff_prescribed {k n : ℕ} (e : Fin k ↪ Fin n)
    (H : SimpleGraph (Fin k)) (G : SimpleGraph (Fin n)) :
    G.comap e = H ↔
      RandomGraph.Prescribed (embeddingEdges e) (fixedEdges e H) G := by
  classical
  constructor
  · intro hGH
    rw [RandomGraph.Prescribed]
    ext a
    constructor
    · intro ha
      rw [Erdos565.RandomGraph.restrict, Finset.mem_inter] at ha
      rcases Finset.mem_image.mp ha.2 with ⟨b, -, rfl⟩
      rw [liftEdge_mem_fixedEdges_iff]
      rw [liftEdge_mem_edges_iff, hGH] at ha
      exact ha.1
    · intro ha
      have ha' := (Finset.mem_filter.mp ha)
      refine Finset.mem_inter.mpr ⟨?_, ha'.1⟩
      rcases Finset.mem_image.mp ha'.1 with ⟨b, -, hb⟩
      subst a
      rw [liftEdge_mem_fixedEdges_iff] at ha
      rw [liftEdge_mem_edges_iff, hGH]
      exact ha
  · intro hP
    apply SimpleGraph.ext
    funext u v
    by_cases huv : u = v
    · subst v
      simp
    let a : RandomGraph.Edge k := ⟨s(u, v), by
      simpa [Sym2.mk_isDiag_iff] using huv⟩
    have haBlock : liftEdge e a ∈ embeddingEdges e := liftEdge_mem_embeddingEdges e a
    rw [RandomGraph.Prescribed] at hP
    have hmem := congrArg (fun S : Finset (RandomGraph.Edge n) ↦ liftEdge e a ∈ S) hP
    rw [Erdos565.RandomGraph.restrict] at hmem
    simp only [Finset.mem_inter, haBlock, and_true,
      liftEdge_mem_fixedEdges_iff] at hmem
    rw [liftEdge_mem_edges_iff] at hmem
    simpa [a, SimpleGraph.mem_edgeSet] using hmem

/-! ## A fixed `100r`-set -/

/-- The increasing enumeration of a finset of the required size. -/
noncomputable def orderedEmbedding {n r : ℕ} (K : Finset (Fin n))
    (hK : K.card = 100 * r) : Fin (100 * r) ↪ Fin n :=
  (K.orderEmbOfFin hK).toEmbedding

/-- The event that the increasing labelling of `K` induces the graph
presented by the specified Boolean matrix. -/
def MatrixEvent {n r : ℕ} (K : Finset (Fin n)) (hK : K.card = 100 * r)
    (M : Matrix r) (G : SimpleGraph (Fin n)) : Prop :=
  G.comap (orderedEmbedding K hK) = graph M

/-- A fixed set supports one of the canonical structured graphs. -/
def FixedSetEvent {n r : ℕ} (K : Finset (Fin n)) (hK : K.card = 100 * r)
    (G : SimpleGraph (Fin n)) : Prop :=
  ∃ M : Matrix r, MatrixEvent K hK M G

/-- Different matrices give disjoint fixed-set events. -/
theorem matrixEvent_injective {n r : ℕ} {K : Finset (Fin n)}
    {hK : K.card = 100 * r} {M N : Matrix r} {G : SimpleGraph (Fin n)}
    (hM : MatrixEvent K hK M G) (hN : MatrixEvent K hK N G) : M = N := by
  apply graph_injective r
  exact hM.symm.trans hN

theorem matrixEvent_disjoint {n r : ℕ} {K : Finset (Fin n)}
    {hK : K.card = 100 * r} {M N : Matrix r} (hMN : M ≠ N) :
    Disjoint {G | MatrixEvent K hK M G} {G | MatrixEvent K hK N G} := by
  rw [Set.disjoint_left]
  intro G hM hN
  exact hMN (matrixEvent_injective hM hN)

theorem matrixEvent_iff_prescribed {n r : ℕ} (K : Finset (Fin n))
    (hK : K.card = 100 * r) (M : Matrix r) (G : SimpleGraph (Fin n)) :
    MatrixEvent K hK M G ↔
      RandomGraph.Prescribed (embeddingEdges (orderedEmbedding K hK))
        (fixedEdges (orderedEmbedding K hK) (graph M)) G := by
  exact comap_eq_iff_prescribed _ _ _

theorem eventCard_matrixEvent {n r : ℕ} (K : Finset (Fin n))
    (hK : K.card = 100 * r) (M : Matrix r) :
    RandomGraph.eventCard n (MatrixEvent K hK M) =
      2 ^ (n.choose 2 - (100 * r).choose 2) := by
  rw [show MatrixEvent K hK M =
      RandomGraph.Prescribed (embeddingEdges (orderedEmbedding K hK))
        (fixedEdges (orderedEmbedding K hK) (graph M)) from
    funext fun G ↦ propext (matrixEvent_iff_prescribed K hK M G)]
  simpa using RandomGraph.card_prescribed
    (fixedEdges_subset_embeddingEdges (orderedEmbedding K hK) (graph M))

theorem probability_matrixEvent {n r : ℕ} (K : Finset (Fin n))
    (hK : K.card = 100 * r) (M : Matrix r) :
    RandomGraph.probability n (MatrixEvent K hK M) =
      (1 / 2 : ℝ) ^ (100 * r).choose 2 := by
  rw [show MatrixEvent K hK M =
      RandomGraph.Prescribed (embeddingEdges (orderedEmbedding K hK))
        (fixedEdges (orderedEmbedding K hK) (graph M)) from
    funext fun G ↦ propext (matrixEvent_iff_prescribed K hK M G)]
  simpa using RandomGraph.probability_prescribed
    (fixedEdges_subset_embeddingEdges (orderedEmbedding K hK) (graph M))

/-! ## Globally stable bucket choices

The increasing enumeration above is convenient for arbitrary finsets, but it
does not preserve the roles of vertices when two finsets overlap.  The ABH
second-moment argument instead uses the following stable slots.  Coordinate
`i : Fin (100*r)` always chooses one vertex from the `i`th consecutive bucket.
-/

/-- Number of canonical template vertices. -/
abbrev templateOrder (r : ℕ) : ℕ := 100 * r

/-- Common bucket size. -/
abbrev bucketSize (n r : ℕ) : ℕ := n / templateOrder r

/-- One chosen offset in every one of the `100*r` global buckets. -/
abbrev Choice (n r : ℕ) := Fin (templateOrder r) → Fin (bucketSize n r)

@[simp] theorem card_choice (n r : ℕ) :
    Fintype.card (Choice n r) = bucketSize n r ^ templateOrder r := by
  simp [Choice, bucketSize, templateOrder]

/-- The stable embedding associated with a bucket choice. -/
def slotEmbedding {n r : ℕ} (c : Choice n r) :
    Fin (templateOrder r) ↪ Fin n where
  toFun i := ⟨i.1 * bucketSize n r + (c i).1, by
    have hdiv := Nat.div_mul_le_self n (templateOrder r)
    have hi := i.2
    have hc := (c i).2
    calc
      i.1 * bucketSize n r + (c i).1 <
          i.1 * bucketSize n r + bucketSize n r := Nat.add_lt_add_left hc _
      _ = (i.1 + 1) * bucketSize n r := by ring
      _ ≤ templateOrder r * bucketSize n r :=
        Nat.mul_le_mul_right _ (Nat.succ_le_of_lt hi)
      _ = bucketSize n r * templateOrder r := Nat.mul_comm _ _
      _ ≤ n := hdiv⟩
  inj' := by
    intro i j hij
    have hp : finProdFinEquiv (i, c i) = finProdFinEquiv (j, c j) := by
      apply Fin.ext
      simpa [finProdFinEquiv, Nat.add_comm, Nat.mul_comm] using congrArg Fin.val hij
    exact congrArg Prod.fst (finProdFinEquiv.injective hp)

@[simp] theorem slotEmbedding_apply_val {n r : ℕ} (c : Choice n r)
    (i : Fin (templateOrder r)) :
    (slotEmbedding c i).1 = i.1 * bucketSize n r + (c i).1 := rfl

/-- The set of host vertices selected by `c`. -/
noncomputable def choiceVertexSet {n r : ℕ} (c : Choice n r) : Finset (Fin n) := by
  classical
  exact Finset.univ.image (slotEmbedding c)

@[simp] theorem card_choiceVertexSet {n r : ℕ} (c : Choice n r) :
    (choiceVertexSet c).card = templateOrder r := by
  classical
  rw [choiceVertexSet, Finset.card_image_of_injective _ (slotEmbedding c).injective]
  simp

@[simp] lemma slotEmbedding_mem_choiceVertexSet {n r : ℕ} (c : Choice n r)
    (i : Fin (templateOrder r)) : slotEmbedding c i ∈ choiceVertexSet c := by
  classical
  simp [choiceVertexSet]

/-- A specified canonical matrix occurs on a stable bucket choice. -/
def SlotMatrixEvent {n r : ℕ} (c : Choice n r) (M : Matrix r)
    (G : SimpleGraph (Fin n)) : Prop :=
  G.comap (slotEmbedding c) = graph M

/-- Some canonical matrix occurs on a stable bucket choice. -/
def FixedChoiceEvent {n r : ℕ} (c : Choice n r)
    (G : SimpleGraph (Fin n)) : Prop :=
  ∃ M : Matrix r, SlotMatrixEvent c M G

theorem slotMatrixEvent_injective {n r : ℕ} {c : Choice n r}
    {M N : Matrix r} {G : SimpleGraph (Fin n)}
    (hM : SlotMatrixEvent c M G) (hN : SlotMatrixEvent c N G) : M = N := by
  apply graph_injective r
  exact hM.symm.trans hN

theorem slotMatrixEvent_disjoint {n r : ℕ} {c : Choice n r}
    {M N : Matrix r} (hMN : M ≠ N) :
    Disjoint {G | SlotMatrixEvent c M G} {G | SlotMatrixEvent c N G} := by
  rw [Set.disjoint_left]
  intro G hM hN
  exact hMN (slotMatrixEvent_injective hM hN)

theorem slotMatrixEvent_iff_prescribed {n r : ℕ} (c : Choice n r)
    (M : Matrix r) (G : SimpleGraph (Fin n)) :
    SlotMatrixEvent c M G ↔
      RandomGraph.Prescribed (embeddingEdges (slotEmbedding c))
        (fixedEdges (slotEmbedding c) (graph M)) G := by
  exact comap_eq_iff_prescribed _ _ _

theorem eventCard_slotMatrixEvent {n r : ℕ} (c : Choice n r) (M : Matrix r) :
    RandomGraph.eventCard n (SlotMatrixEvent c M) =
      2 ^ (n.choose 2 - (templateOrder r).choose 2) := by
  rw [show SlotMatrixEvent c M =
      RandomGraph.Prescribed (embeddingEdges (slotEmbedding c))
        (fixedEdges (slotEmbedding c) (graph M)) from
    funext fun G ↦ propext (slotMatrixEvent_iff_prescribed c M G)]
  simpa using RandomGraph.card_prescribed
    (fixedEdges_subset_embeddingEdges (slotEmbedding c) (graph M))

theorem probability_slotMatrixEvent {n r : ℕ} (c : Choice n r) (M : Matrix r) :
    RandomGraph.probability n (SlotMatrixEvent c M) =
      (1 / 2 : ℝ) ^ (templateOrder r).choose 2 := by
  rw [show SlotMatrixEvent c M =
      RandomGraph.Prescribed (embeddingEdges (slotEmbedding c))
        (fixedEdges (slotEmbedding c) (graph M)) from
    funext fun G ↦ propext (slotMatrixEvent_iff_prescribed c M G)]
  simpa using RandomGraph.probability_prescribed
    (fixedEdges_subset_embeddingEdges (slotEmbedding c) (graph M))

/-- Exact number of host graphs in the fixed-choice family. -/
theorem eventCard_fixedChoiceEvent {n r : ℕ} (c : Choice n r) :
    RandomGraph.eventCard n (FixedChoiceEvent c) =
      2 ^ (90 * r * r) * 2 ^ (n.choose 2 - (templateOrder r).choose 2) := by
  classical
  unfold RandomGraph.eventCard
  have hset : {G : SimpleGraph (Fin n) | FixedChoiceEvent c G} =
      ⋃ M : Matrix r, {G | SlotMatrixEvent c M G} := by
    ext G
    simp [FixedChoiceEvent]
  rw [hset, Set.ncard_iUnion_of_finite]
  · change (∑ᶠ M : Matrix r, RandomGraph.eventCard n (SlotMatrixEvent c M)) = _
    rw [finsum_eq_sum_of_fintype]
    simp_rw [eventCard_slotMatrixEvent]
    rw [Finset.sum_const]
    simp [pow_mul]
  · intro M
    toFinite_tac
  · intro M N hMN
    exact slotMatrixEvent_disjoint hMN

/-- Exact fixed-choice probability. -/
theorem probability_fixedChoiceEvent {n r : ℕ} (c : Choice n r) :
    RandomGraph.probability n (FixedChoiceEvent c) =
      (2 : ℝ) ^ (90 * r * r) * (1 / 2 : ℝ) ^ (templateOrder r).choose 2 := by
  rw [RandomGraph.probability, eventCard_fixedChoiceEvent]
  have hle : (templateOrder r).choose 2 ≤ n.choose 2 := by
    rw [← card_embeddingEdges (slotEmbedding c), ← RandomGraph.card_allEdges n]
    exact Finset.card_le_card (by
      intro a _
      simp [RandomGraph.allEdges, Erdos565.RandomGraph.edgeUniverse])
  push_cast
  rw [show (1 / 2 : ℝ) ^ (templateOrder r).choose 2 =
      1 / 2 ^ (templateOrder r).choose 2 by simp]
  field_simp
  exact_mod_cast (show
    2 ^ (n.choose 2 - (templateOrder r).choose 2) *
        2 ^ (templateOrder r).choose 2 = 2 ^ n.choose 2 by
    rw [← pow_add, Nat.sub_add_cancel hle])

/-! ## Witness counts and the first moment -/

/-- The number of stable bucket choices which witness a structured induced
subgraph in `G`. -/
noncomputable def witnessCount (n r : ℕ) (G : SimpleGraph (Fin n)) : ℕ := by
  classical
  exact (Finset.univ.filter fun c : Choice n r ↦ FixedChoiceEvent c G).card

@[simp] theorem witnessCount_pos_iff {n r : ℕ} {G : SimpleGraph (Fin n)} :
    0 < witnessCount n r G ↔ ∃ c : Choice n r, FixedChoiceEvent c G := by
  classical
  rw [witnessCount, Finset.card_pos]
  constructor
  · rintro ⟨c, hc⟩
    exact ⟨c, (Finset.mem_filter.mp hc).2⟩
  · rintro ⟨c, hc⟩
    exact ⟨c, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hc⟩⟩

/-- Exact double-counting identity underlying the first moment. -/
theorem sum_witnessCount (n r : ℕ) :
    ∑ G : SimpleGraph (Fin n), witnessCount n r G =
      bucketSize n r ^ templateOrder r *
        (2 ^ (90 * r * r) *
          2 ^ (n.choose 2 - (templateOrder r).choose 2)) := by
  classical
  calc
    ∑ G : SimpleGraph (Fin n), witnessCount n r G =
        ∑ G : SimpleGraph (Fin n),
          ∑ c : Choice n r, if FixedChoiceEvent c G then 1 else 0 := by
            apply Finset.sum_congr rfl
            intro G _
            rw [witnessCount, Finset.card_eq_sum_ones, Finset.sum_filter]
    _ = ∑ c : Choice n r,
          ∑ G : SimpleGraph (Fin n), if FixedChoiceEvent c G then 1 else 0 := by
            rw [Finset.sum_comm]
    _ = ∑ _c : Choice n r,
          2 ^ (90 * r * r) *
            2 ^ (n.choose 2 - (templateOrder r).choose 2) := by
            apply Finset.sum_congr rfl
            intro c _
            rw [← eventCard_fixedChoiceEvent c]
            change (∑ G : SimpleGraph (Fin n),
                if FixedChoiceEvent c G then 1 else 0) =
              Set.ncard {G | FixedChoiceEvent c G}
            calc
              (∑ G : SimpleGraph (Fin n),
                  if FixedChoiceEvent c G then (1 : ℕ) else 0) =
                  ((Finset.univ : Finset (SimpleGraph (Fin n))).filter
                    (FixedChoiceEvent c)).card := by simp
              _ = Set.ncard {G | FixedChoiceEvent c G} := by
                rw [← Set.ncard_coe_finset]
                congr 1
                ext G
                simp
    _ = bucketSize n r ^ templateOrder r *
          (2 ^ (90 * r * r) *
            2 ^ (n.choose 2 - (templateOrder r).choose 2)) := by
            simp

/-! ## The deterministic biclique certificate -/

/-- A row of the Boolean matrix, regarded as a biclique of the canonical
structured graph. -/
noncomputable def rowBiclique (M : Matrix r) (i : Fin r) :
    Biclique (graph M) :=
  Biclique.ofSets (graph M) (leftBlock r i) (rightSupport M i)
    (leftBlock_disjoint_rightSupport M i i) (by
      intro u hu v hv
      have huv : u ≠ v := by
        intro huv
        subst v
        exact Set.disjoint_left.mp (leftBlock_disjoint_rightSupport M i i) hu hv
      exact (show piece M i ≤ graph M from le_iSup (piece M) i)
        ((SimpleGraph.between_adj).2 ⟨huv, Or.inl ⟨hu, hv⟩⟩))

lemma rowBiclique_edges (M : Matrix r) (i : Fin r) :
    (rowBiclique M i).edges = graphEdges (piece M i) := by
  classical
  ext e
  induction e using Sym2.inductionOn with
  | _ u v =>
      change s(u, v) ∈ (Biclique.ofSets (graph M) (leftBlock r i)
        (rightSupport M i) _ _).edges ↔ _
      rw [Biclique.mem_edges_ofSets, mem_graphEdges, SimpleGraph.mem_edgeSet]
      rw [piece, SimpleGraph.between_adj]
      constructor
      · rintro ⟨a, ha, b, hb, hab⟩
        rw [Sym2.eq_iff] at hab
        rcases hab with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · exact ⟨fun h ↦ Set.disjoint_left.mp
              (leftBlock_disjoint_rightSupport M i i) ha (h ▸ hb), Or.inl ⟨ha, hb⟩⟩
        · exact ⟨fun h ↦ Set.disjoint_left.mp
              (leftBlock_disjoint_rightSupport M i i) ha (h.symm ▸ hb), Or.inr ⟨hb, ha⟩⟩
      · rintro ⟨huv, huv' | huv'⟩
        · exact ⟨u, huv'.1, v, huv'.2, rfl⟩
        · exact ⟨v, huv'.2, u, huv'.1, Sym2.eq_swap⟩

/-- The displayed list of the `r` canonical row bicliques. -/
noncomputable def canonicalPartition (M : Matrix r) :
    List (Biclique (graph M)) :=
  List.ofFn (rowBiclique M)

@[simp] theorem canonicalPartition_length (M : Matrix r) :
    (canonicalPartition M).length = r := by
  simp [canonicalPartition]

lemma mem_coveredEdges_iff {G : SimpleGraph V} [Fintype V] [DecidableEq V]
    (p : List (Biclique G)) (e : Sym2 V) :
    e ∈ coveredEdges p ↔ ∃ B ∈ p, e ∈ B.edges := by
  induction p with
  | nil => simp
  | cons B p ih =>
      rw [coveredEdges_cons, Finset.mem_union, ih]
      constructor
      · intro h
        rcases h with h | ⟨C, hC, he⟩
        · exact ⟨B, by simp, h⟩
        · exact ⟨C, by simp [hC], he⟩
      · rintro ⟨C, hC, he⟩
        rw [List.mem_cons] at hC
        rcases hC with rfl | hC
        · exact Or.inl he
        · exact Or.inr ⟨C, hC, he⟩

theorem canonicalPartition_isBicliquePartition (M : Matrix r) :
    IsBicliquePartition (graph M) (canonicalPartition M) := by
  classical
  constructor
  · rw [canonicalPartition, List.pairwise_ofFn]
    intro i j hij
    rw [rowBiclique_edges, rowBiclique_edges, Finset.disjoint_left]
    intro e hei hej
    rw [mem_graphEdges] at hei hej
    exact Set.disjoint_left.mp
      (SimpleGraph.disjoint_edgeSet.mpr (piece_disjoint (ne_of_lt hij))) hei hej
  · ext e
    rw [mem_coveredEdges_iff, mem_graphEdges]
    induction e using Sym2.inductionOn with
    | _ u v =>
        rw [SimpleGraph.mem_edgeSet]
        have hgraph : (graph M).Adj u v ↔ ∃ i, (piece M i).Adj u v := by
          rw [graph_eq_iSup_piece, SimpleGraph.iSup_adj]
        rw [hgraph]
        constructor
        · rintro ⟨B, hB, heB⟩
          rw [canonicalPartition] at hB
          rcases List.mem_ofFn.mp hB with ⟨i, rfl⟩
          rw [rowBiclique_edges, mem_graphEdges, SimpleGraph.mem_edgeSet] at heB
          exact ⟨i, heB⟩
        · rintro ⟨i, hi⟩
          exact ⟨rowBiclique M i, by simp [canonicalPartition], by
            rw [rowBiclique_edges, mem_graphEdges, SimpleGraph.mem_edgeSet]
            exact hi⟩

theorem structured_graph_bipartitionNumber_le (M : Matrix r) :
    bipartitionNumber (graph M) ≤ r := by
  calc
    bipartitionNumber (graph M) ≤ (canonicalPartition M).length :=
      bipartitionNumber_le_of_partition (canonicalPartition_isBicliquePartition M)
    _ = r := canonicalPartition_length M

/-! ### Transporting a partition across a vertex equivalence -/

namespace Biclique

/-- Relabel a biclique along an equivalence which identifies the pullback of
the target graph with the source graph. -/
noncomputable def relabel {A B : Type*} [Fintype A] [DecidableEq A]
    [Fintype B] [DecidableEq B] {GA : SimpleGraph A} {GB : SimpleGraph B}
    (f : A ≃ B) (h : GB.comap f = GA) (C : Biclique GA) : Biclique GB where
  left := C.left.map f.toEmbedding
  right := C.right.map f.toEmbedding
  disjoint := by
    rw [Finset.disjoint_map]
    exact C.disjoint
  complete := by
    intro u hu v hv
    rw [Finset.mem_map] at hu hv
    rcases hu with ⟨u', hu', rfl⟩
    rcases hv with ⟨v', hv', rfl⟩
    change (GB.comap f).Adj u' v'
    rw [h]
    exact C.complete u' hu' v' hv'

lemma edges_relabel {A B : Type*} [Fintype A] [DecidableEq A]
    [Fintype B] [DecidableEq B] {GA : SimpleGraph A} {GB : SimpleGraph B}
    (f : A ≃ B) (h : GB.comap f = GA) (C : Biclique GA) :
    (relabel f h C).edges = C.edges.map f.toEmbedding.sym2Map := by
  ext e
  constructor
  · rw [Biclique.mem_edges]
    rintro ⟨u, hu, v, hv, rfl⟩
    simp only [relabel, Finset.mem_map] at hu hv
    rcases hu with ⟨u', hu', rfl⟩
    rcases hv with ⟨v', hv', rfl⟩
    rw [Finset.mem_map]
    exact ⟨s(u', v'), Biclique.mem_edges.mpr ⟨u', hu', v', hv', rfl⟩, rfl⟩
  · rw [Finset.mem_map]
    rintro ⟨e, he, rfl⟩
    rw [Biclique.mem_edges] at he ⊢
    rcases he with ⟨u, hu, v, hv, rfl⟩
    exact ⟨f u, Finset.mem_map.mpr ⟨u, hu, rfl⟩,
      f v, Finset.mem_map.mpr ⟨v, hv, rfl⟩, rfl⟩

end Biclique

lemma coveredEdges_map_relabel {A B : Type*} [Fintype A] [DecidableEq A]
    [Fintype B] [DecidableEq B] {GA : SimpleGraph A} {GB : SimpleGraph B}
    (f : A ≃ B) (h : GB.comap f = GA) (p : List (Biclique GA)) :
    coveredEdges (p.map (Biclique.relabel f h)) =
      (coveredEdges p).map f.toEmbedding.sym2Map := by
  induction p with
  | nil => simp
  | cons C p ih =>
      rw [List.map_cons, coveredEdges_cons, coveredEdges_cons,
        Biclique.edges_relabel, ih, Finset.map_union]

lemma graphEdges_relabel {A B : Type*} [Fintype A] [DecidableEq A]
    [Fintype B] [DecidableEq B] {GA : SimpleGraph A} {GB : SimpleGraph B}
    (f : A ≃ B) (h : GB.comap f = GA) :
    graphEdges GB = (graphEdges GA).map f.toEmbedding.sym2Map := by
  classical
  change GB.comap f.toEmbedding = GA at h
  have hmap : GA.map f.toEmbedding = GB := by
    calc
      GA.map f.toEmbedding = (GB.comap f.toEmbedding).map f.toEmbedding := by rw [h]
      _ = (GB.map f.symm.toEmbedding).map f.toEmbedding := by
        rw [SimpleGraph.map_symm]
      _ = GB := by
        rw [SimpleGraph.map_map]
        have hcomp :
            (f.toEmbedding : A → B) ∘ (f.symm.toEmbedding : B → A) = id := by
          funext x
          exact f.apply_symm_apply x
        rw [hcomp, SimpleGraph.map_id]
  ext e
  rw [mem_graphEdges]
  constructor
  · intro he
    have he' : e ∈ (GA.map f.toEmbedding).edgeSet := by
      rw [hmap]
      exact he
    rw [SimpleGraph.edgeSet_map] at he'
    rcases he' with ⟨a, ha, rfl⟩
    rw [Finset.mem_map]
    exact ⟨a, mem_graphEdges.mpr ha, rfl⟩
  · rw [Finset.mem_map]
    rintro ⟨a, ha, rfl⟩
    have ha' : a ∈ GA.edgeSet := mem_graphEdges.mp ha
    have : f.toEmbedding.sym2Map a ∈ (GA.map f.toEmbedding).edgeSet := by
      rw [SimpleGraph.edgeSet_map]
      exact ⟨a, ha', rfl⟩
    rw [hmap] at this
    exact this

/-- Biclique partitions are invariant under relabelling by a vertex
equivalence. -/
theorem IsBicliquePartition.relabel {A B : Type*} [Fintype A] [DecidableEq A]
    [Fintype B] [DecidableEq B] {GA : SimpleGraph A} {GB : SimpleGraph B}
    {p : List (Biclique GA)} (f : A ≃ B) (h : GB.comap f = GA)
    (hp : IsBicliquePartition GA p) :
    IsBicliquePartition GB (p.map (Biclique.relabel f h)) := by
  constructor
  · rw [List.pairwise_map]
    apply hp.1.imp
    intro C D hCD
    rw [Biclique.edges_relabel, Biclique.edges_relabel, Finset.disjoint_map]
    exact hCD
  · rw [coveredEdges_map_relabel, hp.2, ← graphEdges_relabel f h]

/-! ### Applying the transport to a bucket choice -/

/-- Canonical equivalence between template coordinates and the subtype of
vertices selected by a choice. -/
noncomputable def choiceEquiv {n r : ℕ} (c : Choice n r) :
    Fin (templateOrder r) ≃ {v : Fin n // v ∈ (choiceVertexSet c : Set (Fin n))} where
  toFun i := ⟨slotEmbedding c i, slotEmbedding_mem_choiceVertexSet c i⟩
  invFun v := (Equiv.ofInjective (slotEmbedding c) (slotEmbedding c).injective).symm
    ⟨v.1, by
      rcases Finset.mem_image.mp v.2 with ⟨i, -, hi⟩
      exact ⟨i, hi⟩⟩
  left_inv i := by
    exact Equiv.ofInjective_symm_apply (slotEmbedding c).injective i
  right_inv v := by
    apply Subtype.ext
    exact Equiv.apply_ofInjective_symm (slotEmbedding c).injective
      ⟨v.1, by
        rcases Finset.mem_image.mp v.2 with ⟨i, -, hi⟩
        exact ⟨i, hi⟩⟩

@[simp] theorem choiceEquiv_apply_val {n r : ℕ} (c : Choice n r)
    (i : Fin (templateOrder r)) : (choiceEquiv c i).1 = slotEmbedding c i := by
  rfl

theorem induce_comap_choiceEquiv {n r : ℕ} (c : Choice n r)
    (G : SimpleGraph (Fin n)) :
    (G.induce (choiceVertexSet c : Set (Fin n))).comap (choiceEquiv c) =
      G.comap (slotEmbedding c) := by
  ext u v
  change G.Adj (choiceEquiv c u).1 (choiceEquiv c v).1 ↔
    G.Adj (slotEmbedding c u) (slotEmbedding c v)
  rw [choiceEquiv_apply_val, choiceEquiv_apply_val]

/-- A fixed slot-matrix witness supplies an explicit `r`-piece partition of
the induced graph on the selected vertices. -/
theorem exists_induced_bicliquePartition_of_slotMatrixEvent
    {n r : ℕ} {c : Choice n r} {M : Matrix r} {G : SimpleGraph (Fin n)}
    (hMG : SlotMatrixEvent c M G) :
    ∃ p : List (Biclique (G.induce (choiceVertexSet c : Set (Fin n)))),
      IsBicliquePartition (G.induce (choiceVertexSet c : Set (Fin n))) p ∧
        p.length = r := by
  classical
  have hpull :
      (G.induce (choiceVertexSet c : Set (Fin n))).comap (choiceEquiv c) = graph M :=
    (induce_comap_choiceEquiv c G).trans hMG
  let p := (canonicalPartition M).map
    (Biclique.relabel (choiceEquiv c) hpull)
  refine ⟨p, ?_, ?_⟩
  · exact IsBicliquePartition.relabel (choiceEquiv c) hpull
      (canonicalPartition_isBicliquePartition M)
  · simp [p, canonicalPartition_length]

/-- Deterministic host bound from one specified slot-matrix witness. -/
theorem bipartitionNumber_le_of_slotMatrixEvent
    {n r : ℕ} {c : Choice n r} {M : Matrix r} {G : SimpleGraph (Fin n)}
    (hMG : SlotMatrixEvent c M G) :
    bipartitionNumber G ≤ n - templateOrder r + r := by
  classical
  obtain ⟨p, hp, hplen⟩ :=
    exists_induced_bicliquePartition_of_slotMatrixEvent hMG
  simpa using bipartitionNumber_le_card_sub_add_of_induced_k_partition_r
    (G := G) (S := choiceVertexSet c) (k := templateOrder r) (r := r)
    (card_choiceVertexSet c) hp hplen

/-- Positivity of the witness count gives the deterministic bound consumed by
the probabilistic core. -/
theorem bipartitionNumber_le_of_witnessCount_pos
    {n r : ℕ} {G : SimpleGraph (Fin n)} (hpos : 0 < witnessCount n r G) :
    bipartitionNumber G ≤ n - templateOrder r + r := by
  rcases witnessCount_pos_iff.mp hpos with ⟨c, M, hMG⟩
  exact bipartitionNumber_le_of_slotMatrixEvent hMG

end HostFamily
end Erdos807
