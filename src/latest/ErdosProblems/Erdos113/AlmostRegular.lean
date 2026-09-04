import ErdosProblems.Erdos113.Pruning
import ErdosProblems.Erdos113.Cycles

open scoped BigOperators SimpleGraph

namespace Erdos113AlmostRegular

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V]

open Erdos113Pruning Erdos113Cycles

/-- A maximum-weight `b`-subset.  Every point outside it has weight at most
every point inside it, and hence `b` times its weight is bounded by the total
weight of the subset. -/
theorem exists_top_subset {V : Type*} [Fintype V] [DecidableEq V]
    (w : V → ℕ) (b : ℕ) (hb : b ≤ Fintype.card V) :
    ∃ B : Finset V, B.card = b ∧
      ∀ x ∉ B, b * w x ≤ ∑ y ∈ B, w y := by
  classical
  let candidates := (Finset.univ : Finset V).powersetCard b
  have hcand : candidates.Nonempty := by
    obtain ⟨B, hBsub, hBcard⟩ := Finset.exists_subset_card_eq hb
    exact ⟨B, by simpa [candidates, hBcard] using hBsub⟩
  obtain ⟨B, hBcand, hBmax⟩ :=
    Finset.exists_max_image candidates (fun A ↦ ∑ y ∈ A, w y) hcand
  have hBcard : B.card = b := (Finset.mem_powersetCard.mp hBcand).2
  refine ⟨B, hBcard, ?_⟩
  intro x hx
  have hpoint : ∀ y ∈ B, w x ≤ w y := by
    intro y hy
    by_contra! hyx
    let B' := insert x (B.erase y)
    have hB'card : B'.card = b := by
      dsimp [B']
      rw [Finset.card_insert_of_notMem]
      · rw [Finset.card_erase_of_mem hy, hBcard]
        have : 0 < b := by
          rw [← hBcard, Finset.card_pos]
          exact ⟨y, hy⟩
        omega
      · simp [hx]
    have hB'mem : B' ∈ candidates := by
      rw [Finset.mem_powersetCard]
      exact ⟨Finset.subset_univ _, hB'card⟩
    have hle := hBmax B' hB'mem
    have hsum : (∑ z ∈ B, w z) < ∑ z ∈ B', w z := by
      have herase : (∑ z ∈ B.erase y, w z) + w y = ∑ z ∈ B, w z :=
        Finset.sum_erase_add _ _ hy
      have hxerase : x ∉ B.erase y := by simp [hx]
      rw [show (∑ z ∈ B', w z) = w x + ∑ z ∈ B.erase y, w z by
        dsimp [B']
        exact Finset.sum_insert hxerase]
      omega
    omega
  calc
    b * w x = ∑ _y ∈ B, w x := by simp [hBcard]
    _ ≤ ∑ y ∈ B, w y := Finset.sum_le_sum fun y hy ↦ hpoint y hy

def dartsFrom (G : SimpleGraph V) [DecidableRel G.Adj]
    (B : Finset V) : Finset (V × V) :=
  Finset.univ.filter fun p ↦ p.1 ∈ B ∧ G.Adj p.1 p.2

@[simp] lemma mem_dartsFrom {G : SimpleGraph V} [DecidableRel G.Adj]
    {B : Finset V} {p : V × V} :
    p ∈ dartsFrom G B ↔ p.1 ∈ B ∧ G.Adj p.1 p.2 := by
  simp [dartsFrom]

lemma card_dartsFrom (G : SimpleGraph V) [DecidableRel G.Adj]
    (B : Finset V) :
    (dartsFrom G B).card = ∑ v ∈ B, G.degree v := by
  classical
  rw [dartsFrom, Finset.card_filter]
  rw [show (Finset.univ : Finset (V × V)) =
    (Finset.univ : Finset V).product Finset.univ by ext; simp]
  calc
    (∑ p ∈ (Finset.univ : Finset V).product Finset.univ,
        (if p.1 ∈ B ∧ G.Adj p.1 p.2 then (1 : ℕ) else 0)) =
        ∑ x ∈ (Finset.univ : Finset V), ∑ y ∈ (Finset.univ : Finset V),
          (if x ∈ B ∧ G.Adj x y then (1 : ℕ) else 0) := by
      exact Finset.sum_product _ _ _
    _ = ∑ x ∈ B, ∑ y : V,
          (if G.Adj x y then (1 : ℕ) else 0) := by
      calc
        (∑ x : V, ∑ y : V,
            (if x ∈ B ∧ G.Adj x y then (1 : ℕ) else 0)) =
            ∑ x : V, if x ∈ B then
              (∑ y : V, if G.Adj x y then (1 : ℕ) else 0) else 0 := by
          apply Finset.sum_congr rfl
          intro x hx
          by_cases hxB : x ∈ B <;> simp [hxB]
        _ = ∑ x ∈ B, ∑ y : V,
              (if G.Adj x y then (1 : ℕ) else 0) := by
          rw [← Finset.sum_filter]
          simp
    _ = ∑ x ∈ B, G.degree x := by
      apply Finset.sum_congr rfl
      intro x hx
      rw [← Finset.card_filter, show
        (Finset.univ.filter fun y ↦ G.Adj x y) = G.neighborFinset x by ext; simp]
      exact G.card_neighborFinset_eq_degree x

def dartsToPart (G : SimpleGraph V) [DecidableRel G.Adj]
    (B : Finset V) (P : Finpartition (Finset.univ : Finset V))
    (C : Finset V) : Finset (V × V) :=
  (dartsFrom G B).filter fun p ↦
    P.part p.2 = C

@[simp] lemma mem_dartsToPart {G : SimpleGraph V} [DecidableRel G.Adj]
    {B : Finset V} {P : Finpartition (Finset.univ : Finset V)}
    {C : Finset V} {p : V × V} :
    p ∈ dartsToPart G B P C ↔
      p.1 ∈ B ∧ G.Adj p.1 p.2 ∧
        P.part p.2 = C := by
  simp [dartsToPart, and_assoc]

lemma exists_part_with_many_darts
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (B : Finset V) (P : Finpartition (Finset.univ : Finset V))
    (hP : P.parts.Nonempty) :
    ∃ C ∈ P.parts,
      (dartsFrom G B).card ≤ P.parts.card * (dartsToPart G B P C).card := by
  classical
  let weight : Finset V → ℕ := fun C ↦ (dartsToPart G B P C).card
  obtain ⟨C, hCP, hCmax⟩ := Finset.exists_max_image P.parts weight hP
  refine ⟨C, hCP, ?_⟩
  have hsum : (dartsFrom G B).card =
      ∑ C ∈ P.parts, (dartsToPart G B P C).card := by
    rw [Finset.card_eq_sum_card_fiberwise
      (s := dartsFrom G B) (t := P.parts)
      (f := fun p ↦ P.part p.2)]
    · rfl
    · intro p hp
      exact P.part_mem.mpr (Finset.mem_univ _)
  rw [hsum]
  calc
    ∑ D ∈ P.parts, (dartsToPart G B P D).card ≤
        ∑ _D ∈ P.parts, weight C := by
      apply Finset.sum_le_sum
      intro D hDP
      exact hCmax D hDP
    _ = P.parts.card * (dartsToPart G B P C).card := by simp [weight]

/-- Darts from `B` whose other endpoint lies in a part `C` inject into the
oriented edges of the induced graph on `B ∪ C`. -/
lemma card_dartsToPart_le_twice_induced_edges
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (B : Finset V) (P : Finpartition (Finset.univ : Finset V))
    {C : Finset V} (hCP : C ∈ P.parts) :
    (dartsToPart G B P C).card ≤
      2 * (G.induce (↑(B ∪ C) : Set V)).edgeFinset.card := by
  classical
  let S := B ∪ C
  let A := G.induce (↑S : Set V)
  let D := dartsToPart G B P C
  let target := (Finset.univ : Finset (S × S)).filter fun p ↦ A.Adj p.1 p.2
  let f : ↑D → S × S := fun p ↦
    (⟨p.1.1, Finset.mem_union_left C (mem_dartsToPart.mp p.2).1⟩,
      ⟨p.1.2, Finset.mem_union_right B (by
        have hpart := P.mem_part (Finset.mem_univ p.1.2)
        rw [(mem_dartsToPart.mp p.2).2.2] at hpart
        exact hpart)⟩)
  have hfmem : ∀ p, f p ∈ target := by
    intro p
    rw [Finset.mem_filter]
    refine ⟨Finset.mem_univ _, ?_⟩
    exact (mem_dartsToPart.mp p.2).2.1
  have hfinj : Function.Injective f := by
    intro p q hpq
    apply Subtype.ext
    apply Prod.ext
    · exact congrArg (fun z ↦ z.1.1) hpq
    · exact congrArg (fun z ↦ z.2.1) hpq
  have hcard : D.card ≤ target.card := by
    rw [← Fintype.card_coe, ← Fintype.card_coe]
    exact Fintype.card_le_of_injective
      (fun p ↦ ⟨f p, hfmem p⟩) (fun p q h ↦ hfinj (congrArg Subtype.val h))
  calc
    D.card ≤ target.card := hcard
    _ = 2 * A.edgeFinset.card := by
      simpa [target] using A.two_mul_card_edgeFinset.symm
    _ = 2 * (G.induce (↑(B ∪ C) : Set V)).edgeFinset.card := rfl

def incidentEdges (G : SimpleGraph V) [DecidableRel G.Adj]
    (B : Finset V) : Finset (Sym2 V) :=
  B.biUnion fun v ↦ G.incidenceFinset v

lemma incidentEdges_subset_edgeFinset
    (G : SimpleGraph V) [DecidableRel G.Adj] (B : Finset V) :
    incidentEdges G B ⊆ G.edgeFinset := by
  intro e he
  obtain ⟨v, hvB, hev⟩ := Finset.mem_biUnion.mp he
  exact G.incidenceFinset_subset v hev

lemma card_incidentEdges_le_sum_degrees
    (G : SimpleGraph V) [DecidableRel G.Adj] (B : Finset V) :
    (incidentEdges G B).card ≤ ∑ v ∈ B, G.degree v := by
  classical
  calc
    (incidentEdges G B).card ≤ ∑ v ∈ B, (G.incidenceFinset v).card := by
      exact Finset.card_biUnion_le
    _ = ∑ v ∈ B, G.degree v := by
      apply Finset.sum_congr rfl
      intro v hv
      exact G.card_incidenceFinset_eq_degree v

def outsideEdges (G : SimpleGraph V) [DecidableRel G.Adj]
    (B : Finset V) : Finset (Sym2 V) :=
  G.edgeFinset \ incidentEdges G B

lemma outsideEdges_subset_edgeFinset
    (G : SimpleGraph V) [DecidableRel G.Adj] (B : Finset V) :
    outsideEdges G B ⊆ G.edgeFinset := Finset.sdiff_subset

lemma card_edgeFinset_le_outside_add_sum_degrees
    (G : SimpleGraph V) [DecidableRel G.Adj] (B : Finset V) :
    G.edgeFinset.card ≤ (outsideEdges G B).card + ∑ v ∈ B, G.degree v := by
  have hsplit := Finset.card_sdiff_add_card_inter G.edgeFinset (incidentEdges G B)
  calc
    G.edgeFinset.card = (outsideEdges G B).card +
        (G.edgeFinset ∩ incidentEdges G B).card := hsplit.symm
    _ ≤ (outsideEdges G B).card + (incidentEdges G B).card := by
      gcongr
      exact (Finset.inter_subset_right :
        G.edgeFinset ∩ incidentEdges G B ⊆ incidentEdges G B)
    _ ≤ (outsideEdges G B).card + ∑ v ∈ B, G.degree v := by
      gcongr
      exact card_incidentEdges_le_sum_degrees G B

lemma endpoint_not_mem_of_edge_outside
    (G : SimpleGraph V) [DecidableRel G.Adj] (B : Finset V)
    {e : Sym2 V} (he : e ∈ outsideEdges G B) {v : V} (hv : v ∈ e) :
    v ∉ B := by
  intro hvB
  have heinc : e ∈ incidentEdges G B := by
    rw [incidentEdges, Finset.mem_biUnion]
    refine ⟨v, hvB, ?_⟩
    rw [G.mem_incidenceFinset]
    exact ⟨(by simpa using outsideEdges_subset_edgeFinset G B he), hv⟩
  exact (Finset.mem_sdiff.mp he).2 heinc

lemma incidenceFinset_graphOfEdges_inter
    {G : SimpleGraph V} [DecidableRel G.Adj]
    {D E : Finset (Sym2 V)} (hD : D ⊆ G.edgeFinset) (hED : E ⊆ D)
    (v : V) :
    E ∩ (graphOfEdges D).incidenceFinset v =
      (graphOfEdges E).incidenceFinset v := by
  have hE : E ⊆ G.edgeFinset := hED.trans hD
  rw [(graphOfEdges D).incidenceFinset_eq_filter,
    (graphOfEdges E).incidenceFinset_eq_filter,
    edgeFinset_graphOfEdges_of_subset hD,
    edgeFinset_graphOfEdges_of_subset hE]
  ext e
  simp only [Finset.mem_inter, Finset.mem_filter]
  tauto

/-- The number of selected edges incident with a vertex.  We use this
set-theoretic form while maximizing a degree-capped edge set. -/
def selectedDegree (E : Finset (Sym2 V)) (v : V) : ℕ :=
  (E.filter fun e ↦ v ∈ e).card

lemma selectedDegree_eq_graph_degree
    {G : SimpleGraph V} [DecidableRel G.Adj]
    {E : Finset (Sym2 V)} (hE : E ⊆ G.edgeFinset) (v : V) :
    selectedDegree E v = (graphOfEdges E).degree v := by
  rw [← (graphOfEdges E).card_incidenceFinset_eq_degree,
    (graphOfEdges E).incidenceFinset_eq_filter,
    edgeFinset_graphOfEdges_of_subset hE]
  rfl

lemma selectedDegree_insert_of_mem
    {E : Finset (Sym2 V)} {e : Sym2 V} (he : e ∉ E)
    {v : V} (hv : v ∈ e) :
    selectedDegree (insert e E) v = selectedDegree E v + 1 := by
  simp [selectedDegree, Finset.filter_insert, hv, he]

lemma selectedDegree_insert_of_not_mem
    {E : Finset (Sym2 V)} {e : Sym2 V} (he : e ∉ E)
    {v : V} (hv : v ∉ e) :
    selectedDegree (insert e E) v = selectedDegree E v := by
  simp [selectedDegree, Finset.filter_insert, hv, he]

/-- Edge sets whose degrees are everywhere at most `D`. -/
def DegreeCapped (D : ℕ) (E : Finset (Sym2 V)) : Prop :=
  ∀ v, selectedDegree E v ≤ D

lemma degreeCapped_empty (D : ℕ) : DegreeCapped (V := V) D ∅ := by
  intro v
  simp [DegreeCapped, selectedDegree]

/-- A maximum-cardinality degree-capped edge set is inclusion-maximal: every
omitted edge has a saturated endpoint. -/
theorem exists_maximal_degreeCapped
    (G : SimpleGraph V) [DecidableRel G.Adj] (D : ℕ) :
    ∃ E : Finset (Sym2 V),
      E ⊆ G.edgeFinset ∧
      DegreeCapped D E ∧
      ∀ e ∈ G.edgeFinset, e ∉ E →
        ∃ v ∈ e, D ≤ selectedDegree E v := by
  classical
  let good := G.edgeFinset.powerset.filter fun E ↦ DegreeCapped D E
  have hgood : good.Nonempty := ⟨∅, by simp [good, degreeCapped_empty]⟩
  obtain ⟨E, hEgood, hEmax⟩ :=
    Finset.exists_max_image good Finset.card hgood
  have hEsub : E ⊆ G.edgeFinset :=
    Finset.mem_powerset.mp (Finset.mem_filter.mp hEgood).1
  have hEcap : DegreeCapped D E := (Finset.mem_filter.mp hEgood).2
  refine ⟨E, hEsub, hEcap, ?_⟩
  intro e heG heE
  by_contra hsat
  push_neg at hsat
  have hinsertCap : DegreeCapped D (insert e E) := by
    intro v
    by_cases hv : v ∈ e
    · rw [selectedDegree_insert_of_mem heE hv]
      have := hsat v hv
      omega
    · rw [selectedDegree_insert_of_not_mem heE hv]
      exact hEcap v
  have hinsertGood : insert e E ∈ good := by
    rw [Finset.mem_filter]
    refine ⟨Finset.mem_powerset.mpr ?_, hinsertCap⟩
    intro f hf
    rw [Finset.mem_insert] at hf
    rcases hf with rfl | hf
    · exact heG
    · exact hEsub hf
  have hle := hEmax (insert e E) hinsertGood
  rw [Finset.card_insert_of_notMem heE] at hle
  omega

def saturatedVertices (D : ℕ) (E : Finset (Sym2 V)) : Finset V :=
  Finset.univ.filter fun v ↦ D ≤ selectedDegree E v

@[simp] lemma mem_saturatedVertices {D : ℕ} {E : Finset (Sym2 V)} {v : V} :
    v ∈ saturatedVertices D E ↔ D ≤ selectedDegree E v := by
  simp [saturatedVertices]

lemma edgeFinset_subset_selected_union_incidentSaturated
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {D : ℕ} {E : Finset (Sym2 V)}
    (hEsub : E ⊆ G.edgeFinset)
    (hmax : ∀ e ∈ G.edgeFinset, e ∉ E →
      ∃ v ∈ e, D ≤ selectedDegree E v) :
    G.edgeFinset ⊆ E ∪ incidentEdges G (saturatedVertices D E) := by
  intro e heG
  by_cases heE : e ∈ E
  · exact Finset.mem_union_left _ heE
  · obtain ⟨v, hve, hvsat⟩ := hmax e heG heE
    apply Finset.mem_union_right
    rw [incidentEdges, Finset.mem_biUnion]
    refine ⟨v, mem_saturatedVertices.mpr hvsat, ?_⟩
    rw [G.mem_incidenceFinset]
    exact ⟨(by simpa using heG), hve⟩

lemma saturated_mul_cap_le_twice_selected
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {D : ℕ} {E : Finset (Sym2 V)} (hEsub : E ⊆ G.edgeFinset) :
    (saturatedVertices D E).card * D ≤ 2 * E.card := by
  classical
  calc
    (saturatedVertices D E).card * D =
        ∑ _v ∈ saturatedVertices D E, D := by simp
    _ ≤ ∑ v ∈ saturatedVertices D E, selectedDegree E v := by
      apply Finset.sum_le_sum
      intro v hv
      exact mem_saturatedVertices.mp hv
    _ ≤ ∑ v : V, selectedDegree E v := by
      apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
      intro v hvU hvS
      omega
    _ = ∑ v : V, (graphOfEdges E).degree v := by
      apply Finset.sum_congr rfl
      intro v hv
      exact selectedDegree_eq_graph_degree hEsub v
    _ = 2 * (graphOfEdges E).edgeFinset.card :=
      (graphOfEdges E).sum_degrees_eq_twice_card_edges
    _ = 2 * E.card := by rw [edgeFinset_graphOfEdges_of_subset hEsub]

lemma card_edgeFinset_le_selected_add_saturated_degrees
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {D : ℕ} {E : Finset (Sym2 V)}
    (hEsub : E ⊆ G.edgeFinset)
    (hmax : ∀ e ∈ G.edgeFinset, e ∉ E →
      ∃ v ∈ e, D ≤ selectedDegree E v) :
    G.edgeFinset.card ≤ E.card +
      ∑ v ∈ saturatedVertices D E, G.degree v := by
  calc
    G.edgeFinset.card ≤
        (E ∪ incidentEdges G (saturatedVertices D E)).card :=
      Finset.card_le_card
        (edgeFinset_subset_selected_union_incidentSaturated G hEsub hmax)
    _ ≤ E.card + (incidentEdges G (saturatedVertices D E)).card :=
      Finset.card_union_le _ _
    _ ≤ E.card + ∑ v ∈ saturatedVertices D E, G.degree v := by
      gcongr
      exact card_incidentEdges_le_sum_degrees G _

lemma degree_mul_card_le_of_almost_regular
    (G : SimpleGraph V) [DecidableRel G.Adj] {K : ℕ}
    (hreg : ∀ x y, G.degree x ≤ K * G.degree y) (x : V) :
    Fintype.card V * G.degree x ≤ 2 * K * G.edgeFinset.card := by
  calc
    Fintype.card V * G.degree x = ∑ _y : V, G.degree x := by simp
    _ ≤ ∑ y : V, K * G.degree y := by
      apply Finset.sum_le_sum
      intro y hy
      exact hreg x y
    _ = K * ∑ y : V, G.degree y := by rw [Finset.mul_sum]
    _ = K * (2 * G.edgeFinset.card) := by
      rw [G.sum_degrees_eq_twice_card_edges]
    _ = 2 * K * G.edgeFinset.card := by ring

lemma card_mul_sum_degrees_le_of_almost_regular
    (G : SimpleGraph V) [DecidableRel G.Adj] {K : ℕ}
    (hreg : ∀ x y, G.degree x ≤ K * G.degree y) (S : Finset V) :
    Fintype.card V * (∑ v ∈ S, G.degree v) ≤
      S.card * (2 * K * G.edgeFinset.card) := by
  calc
    Fintype.card V * (∑ v ∈ S, G.degree v) =
        ∑ v ∈ S, Fintype.card V * G.degree v := by
      rw [Finset.mul_sum]
    _ ≤ ∑ _v ∈ S, 2 * K * G.edgeFinset.card := by
      apply Finset.sum_le_sum
      intro v hv
      exact degree_mul_card_le_of_almost_regular G hreg v
    _ = S.card * (2 * K * G.edgeFinset.card) := by simp

/-- Deterministic bounded-degree sparsification.  The constants are chosen so
that the maximal capped set cannot have fewer than `t` edges: otherwise its
saturated vertices cover the omitted edges, but their total incidence is too
small. -/
theorem exists_dense_degreeCapped_subset
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (K D t : ℕ) (hK : 0 < K) (ht : 0 < t)
    (hedges : 4 * t ≤ G.edgeFinset.card)
    (hcap : 8 * K * t ≤ D * Fintype.card V)
    (hreg : ∀ x y, G.degree x ≤ K * G.degree y) :
    ∃ E : Finset (Sym2 V),
      E ⊆ G.edgeFinset ∧
      t ≤ E.card ∧
      ∀ v, (graphOfEdges E).degree v ≤ D := by
  classical
  obtain ⟨E, hEsub, hEcap, hEmax⟩ := exists_maximal_degreeCapped G D
  refine ⟨E, hEsub, ?_, ?_⟩
  · by_contra hEt
    have hElt : E.card < t := Nat.lt_of_not_ge hEt
    let S := saturatedVertices D E
    have hcover := card_edgeFinset_le_selected_add_saturated_degrees
      G hEsub hEmax
    have hsat := saturated_mul_cap_le_twice_selected G
      (D := D) (E := E) hEsub
    have hsum := card_mul_sum_degrees_le_of_almost_regular G hreg S
    have hDmul :
        D * Fintype.card V * (∑ v ∈ S, G.degree v) ≤
          4 * K * E.card * G.edgeFinset.card := by
      calc
        D * Fintype.card V * (∑ v ∈ S, G.degree v) =
            D * (Fintype.card V * (∑ v ∈ S, G.degree v)) := by ring
        _ ≤ D * (S.card * (2 * K * G.edgeFinset.card)) := by gcongr
        _ = (S.card * D) * (2 * K * G.edgeFinset.card) := by ring
        _ ≤ (2 * E.card) * (2 * K * G.edgeFinset.card) := by gcongr
        _ = 4 * K * E.card * G.edgeFinset.card := by ring
    have hcoverMul :
        D * Fintype.card V * G.edgeFinset.card ≤
          D * Fintype.card V * E.card +
            4 * K * E.card * G.edgeFinset.card := by
      calc
        D * Fintype.card V * G.edgeFinset.card ≤
            D * Fintype.card V *
              (E.card + ∑ v ∈ S, G.degree v) := by gcongr
        _ = D * Fintype.card V * E.card +
            D * Fintype.card V * (∑ v ∈ S, G.degree v) := by ring
        _ ≤ D * Fintype.card V * E.card +
            4 * K * E.card * G.edgeFinset.card := by gcongr
    have hDmpos : 0 < D * Fintype.card V := by
      have : 0 < 8 * K * t := by positivity
      exact this.trans_le hcap
    have hepos : 0 < G.edgeFinset.card := by
      exact (by positivity : 0 < 4 * t).trans_le hedges
    have hupper :
        D * Fintype.card V * G.edgeFinset.card ≤
          D * Fintype.card V * t + 4 * K * t * G.edgeFinset.card := by
      exact hcoverMul.trans (add_le_add
        (Nat.mul_le_mul_left (D * Fintype.card V) hElt.le)
        (Nat.mul_le_mul_right G.edgeFinset.card
          (Nat.mul_le_mul_left (4 * K) hElt.le)))
    have hquarter :
        4 * (D * Fintype.card V * t) ≤
          D * Fintype.card V * G.edgeFinset.card := by
      calc
        4 * (D * Fintype.card V * t) =
            D * Fintype.card V * (4 * t) := by ring
        _ ≤ D * Fintype.card V * G.edgeFinset.card := by gcongr
    have hhalf :
        2 * (4 * K * t * G.edgeFinset.card) ≤
          D * Fintype.card V * G.edgeFinset.card := by
      calc
        2 * (4 * K * t * G.edgeFinset.card) =
            (8 * K * t) * G.edgeFinset.card := by ring
        _ ≤ (D * Fintype.card V) * G.edgeFinset.card := by gcongr
        _ = D * Fintype.card V * G.edgeFinset.card := by ring
    have hfourUpper := Nat.mul_le_mul_left 4 hupper
    have hthree :
        4 * (D * Fintype.card V * t +
            4 * K * t * G.edgeFinset.card) ≤
          3 * (D * Fintype.card V * G.edgeFinset.card) := by
      nlinarith
    have hbad :
        4 * (D * Fintype.card V * G.edgeFinset.card) ≤
          3 * (D * Fintype.card V * G.edgeFinset.card) :=
      hfourUpper.trans hthree
    have : 0 < D * Fintype.card V * G.edgeFinset.card := by positivity
    omega
  · intro v
    rw [← selectedDegree_eq_graph_degree hEsub v]
    exact hEcap v

def blockCount : ℕ := 2 ^ (100 : ℕ)

def shrinkFactor : ℕ := blockCount / 4

def edgeLossFactor : ℕ := 4 * blockCount

def regularFactor : ℕ := 32 * blockCount

lemma blockCount_pos : 0 < blockCount := by
  norm_num [blockCount]

lemma blockCount_two_le : 2 ≤ blockCount := by
  norm_num [blockCount]

lemma shrinkFactor_two_le : 2 ≤ shrinkFactor := by
  norm_num [shrinkFactor, blockCount]

lemma edgeLoss_power_le_shrink_power :
    edgeLossFactor ^ 21 ≤ shrinkFactor ^ 22 := by
  norm_num [edgeLossFactor, shrinkFactor, blockCount, pow_succ]

lemma edgeLoss_density_power_le :
    edgeLossFactor ^ 21 ≤ shrinkFactor ^ 31 := by
  exact edgeLoss_power_le_shrink_power.trans (by
    have hs : 1 ≤ shrinkFactor := le_trans (by omega) shrinkFactor_two_le
    have h := pow_le_pow_right₀ hs
      (by omega : 22 ≤ 31)
    simpa using h)

lemma linear_density_of_large {n e : ℕ}
    (hn : blockCount ≤ n) (hdense : n ^ 31 < e ^ 21) :
    32 * n ≤ e := by
  by_contra! he
  have hep : e ^ 21 ≤ (32 * n) ^ 21 := pow_le_pow_left' he.le 21
  have hpow : n ^ 21 * n ^ 10 < 32 ^ 21 * n ^ 21 := by
    simpa [← pow_add, mul_pow, mul_comm] using hdense.trans_le hep
  have hnpos : 0 < n := blockCount_pos.trans_le hn
  have hsmall : n ^ 10 < 32 ^ 21 := by
    have hp : 0 < n ^ 21 := pow_pos hnpos 21
    apply (Nat.mul_lt_mul_left hp).mp
    simpa [mul_comm] using hpow
  have hlarge : blockCount ^ 10 ≤ n ^ 10 := pow_le_pow_left' hn 10
  have : blockCount ^ 10 < 32 ^ 21 := hlarge.trans_lt hsmall
  norm_num [blockCount, pow_succ] at this

lemma quotientBlock_pos (n : ℕ) : 0 < n / blockCount + 1 := by
  exact Nat.zero_lt_succ _

lemma quotientBlock_le_card {n : ℕ} (hn : blockCount ≤ n) :
    n / blockCount + 1 ≤ n := by
  have htwo := blockCount_two_le
  have hdiv : n / blockCount ≤ n / 2 :=
    Nat.div_le_div_left htwo (by omega)
  have hn2 : n / 2 + 1 ≤ n := by
    have : 2 ≤ n := htwo.trans hn
    omega
  omega

lemma card_le_blockCount_mul_quotientBlock (n : ℕ) :
    n ≤ blockCount * (n / blockCount + 1) :=
  (Nat.lt_mul_div_succ n blockCount_pos).le

lemma blockCount_mul_quotientBlock_le_twice {n : ℕ}
    (hn : blockCount ≤ n) :
    blockCount * (n / blockCount + 1) ≤ 2 * n := by
  have hdiv := Nat.div_mul_le_self n blockCount
  have : n / blockCount * blockCount + blockCount ≤ n + n :=
    Nat.add_le_add hdiv hn
  calc
    blockCount * (n / blockCount + 1) =
        n / blockCount * blockCount + blockCount := by ring
    _ ≤ n + n := this
    _ = 2 * n := by omega

lemma shrink_union_bound {n b c : ℕ} (hn : blockCount ≤ n)
    (hb : b ≤ n / blockCount + 1) (hc : c ≤ n / blockCount + 1) :
    shrinkFactor * (b + c) ≤ n := by
  have hMdiv : blockCount = 4 * shrinkFactor := by
    norm_num [blockCount, shrinkFactor]
  have hsum : b + c ≤ 2 * (n / blockCount + 1) := by omega
  have hbase := blockCount_mul_quotientBlock_le_twice hn
  have hhalf : 2 * shrinkFactor * (n / blockCount + 1) ≤ n := by
    apply Nat.le_of_mul_le_mul_left (c := 2) _ (by omega)
    calc
      2 * (2 * shrinkFactor * (n / blockCount + 1)) =
          blockCount * (n / blockCount + 1) := by rw [hMdiv]; ring
      _ ≤ 2 * n := hbase
  exact (Nat.mul_le_mul_left shrinkFactor hsum).trans (by
    simpa [mul_assoc, mul_comm, mul_left_comm] using hhalf)

lemma rpow_density_of_power_density {m e : ℕ}
    (h : m ^ 31 < (4 * e) ^ 21) :
    (m : ℝ) ^ ((31 : ℝ) / 21) < 4 * e := by
  have hcast : (m : ℝ) ^ (31 : ℕ) < (4 * (e : ℝ)) ^ (21 : ℕ) := by
    exact_mod_cast h
  have hroot := Real.rpow_lt_rpow (by positivity :
      0 ≤ (m : ℝ) ^ (31 : ℕ)) hcast (by norm_num : (0 : ℝ) < 1 / 21)
  calc
    (m : ℝ) ^ ((31 : ℝ) / 21) =
        ((m : ℝ) ^ (31 : ℕ)) ^ ((1 : ℝ) / 21) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (Nat.cast_nonneg m)]
      norm_num
    _ < ((4 * (e : ℝ)) ^ (21 : ℕ)) ^ ((1 : ℝ) / 21) := hroot
    _ = 4 * e := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity :
        (0 : ℝ) ≤ 4 * e)]
      norm_num

lemma power_density_of_rpow_density {n e : ℕ}
    (h : (n : ℝ) ^ ((31 : ℝ) / 21) < e) :
    n ^ 31 < e ^ 21 := by
  have hp := Real.rpow_lt_rpow
    (Real.rpow_nonneg (Nat.cast_nonneg n) _)
    h (by norm_num : (0 : ℝ) < 21)
  have hreal : ((n ^ 31 : ℕ) : ℝ) < ((e ^ 21 : ℕ) : ℝ) := by
    calc
      ((n ^ 31 : ℕ) : ℝ) =
          ((n : ℝ) ^ ((31 : ℝ) / 21)) ^ (21 : ℝ) := by
        push_cast
        rw [← Real.rpow_mul (Nat.cast_nonneg n)]
        norm_num
      _ < (e : ℝ) ^ (21 : ℝ) := hp
      _ = ((e ^ 21 : ℕ) : ℝ) := by
        norm_num [Real.rpow_natCast]
  exact_mod_cast hreal

noncomputable def densityTarget (m : ℕ) : ℕ :=
  ⌈(m : ℝ) ^ ((31 : ℝ) / 21) / 64⌉₊

noncomputable def degreeCapTarget (K m : ℕ) : ℕ :=
  ⌈(8 * K * densityTarget m : ℕ) / (m : ℝ)⌉₊

lemma densityTarget_pos {m : ℕ} (hm : 0 < m) : 0 < densityTarget m := by
  rw [densityTarget, Nat.ceil_pos]
  positivity

lemma densityTarget_cast_lt {m : ℕ} (hm : 64 ≤ m) :
    (densityTarget m : ℝ) <
      (m : ℝ) ^ ((31 : ℝ) / 21) / 32 := by
  let x : ℝ := (m : ℝ) ^ ((31 : ℝ) / 21)
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast (by omega : 1 ≤ m)
  have hexp : (1 : ℝ) ≤ (31 : ℝ) / 21 := by norm_num
  have hx64 : (64 : ℝ) ≤ x := by
    calc
      (64 : ℝ) ≤ m := by exact_mod_cast hm
      _ ≤ x := Real.self_le_rpow_of_one_le hm1 hexp
  calc
    (densityTarget m : ℝ) < x / 64 + 1 := by
      simpa [densityTarget, x] using
        (Nat.ceil_lt_add_one (show 0 ≤
          (m : ℝ) ^ ((31 : ℝ) / 21) / 64 by positivity))
    _ ≤ x / 32 := by nlinarith

lemma four_mul_densityTarget_le {m e : ℕ} (hm : 64 ≤ m)
    (hdense : m ^ 31 < (4 * e) ^ 21) :
    4 * densityTarget m ≤ e := by
  let x : ℝ := (m : ℝ) ^ ((31 : ℝ) / 21)
  have htlt : (densityTarget m : ℝ) < x / 32 := by
    simpa [x] using densityTarget_cast_lt hm
  have hxe : x < 4 * (e : ℝ) := by
    simpa [x] using rpow_density_of_power_density hdense
  have hreal : (4 * densityTarget m : ℕ) < (e : ℝ) := by
    push_cast
    nlinarith
  exact_mod_cast hreal.le

lemma degreeCapTarget_mul_card {K m : ℕ} (hm : 0 < m) :
    8 * K * densityTarget m ≤ degreeCapTarget K m * m := by
  have hceil : ((8 * K * densityTarget m : ℕ) : ℝ) / m ≤
      (degreeCapTarget K m : ℝ) := by
    exact Nat.le_ceil _
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hreal : ((8 * K * densityTarget m : ℕ) : ℝ) ≤
      (degreeCapTarget K m : ℝ) * m := by
    calc
      ((8 * K * densityTarget m : ℕ) : ℝ) =
          (((8 * K * densityTarget m : ℕ) : ℝ) / m) * m := by field_simp
      _ ≤ (degreeCapTarget K m : ℝ) * m := by gcongr
  exact_mod_cast hreal

lemma degreeCapTarget_cast_lt (K m : ℕ) (hm : 64 ≤ m) :
    (degreeCapTarget K m : ℝ) <
      ((K : ℝ) + 1) * (m : ℝ) ^ ((10 : ℝ) / 21) := by
  let x : ℝ := (m : ℝ) ^ ((31 : ℝ) / 21)
  let z : ℝ := (m : ℝ) ^ ((10 : ℝ) / 21)
  have hmpos : (0 : ℝ) < m := by exact_mod_cast (by omega : 0 < m)
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast (by omega : 1 ≤ m)
  have hz1 : (1 : ℝ) ≤ z := by
    exact Real.one_le_rpow hm1 (by norm_num)
  have htz : (densityTarget m : ℝ) < x / 32 := by
    simpa [x] using densityTarget_cast_lt hm
  have hxdiv : x / (m : ℝ) = z := by
    rw [← Real.rpow_sub_one hmpos.ne']
    dsimp [x, z]
    congr 1
    norm_num
  let y : ℝ := ((8 * K * densityTarget m : ℕ) : ℝ) / m
  have hyle : y ≤ (K : ℝ) / 4 * z := by
    dsimp [y]
    push_cast
    calc
      8 * (K : ℝ) * (densityTarget m : ℝ) / m ≤
          8 * (K : ℝ) * (x / 32) / m := by
        by_cases hK : K = 0
        · simp [hK]
        · have hfac : (0 : ℝ) < 8 * K := by positivity
          exact (div_lt_div_of_pos_right
            (mul_lt_mul_of_pos_left htz hfac) hmpos).le
      _ = (K : ℝ) / 4 * z := by rw [← hxdiv]; ring
  have hceil : (degreeCapTarget K m : ℝ) < y + 1 := by
    simpa [degreeCapTarget, y] using
      (Nat.ceil_lt_add_one (show 0 ≤
        ((8 * K * densityTarget m : ℕ) : ℝ) / m by positivity))
  have hK0 : (0 : ℝ) ≤ K := by positivity
  nlinarith

/-- The output package of the deterministic Erdős--Simonovits
regularization descent.  Its vertex type may change at each induced-subgraph
step, while `contained` remembers the embedding into the original host. -/
structure RegularCore {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] where
  W : Type u
  [fintypeW : Fintype W]
  [decEqW : DecidableEq W]
  graph : SimpleGraph W
  [decAdj : DecidableRel graph.Adj]
  contained : graph ⊑ G
  edges_nonempty : graph.edgeFinset.Nonempty
  density : Fintype.card W ^ 31 < (4 * graph.edgeFinset.card) ^ 21
  almost_regular : ∀ x y, graph.degree x ≤ regularFactor * graph.degree y
  transfer : G.edgeFinset.card ^ 21 * Fintype.card W ^ 22 ≤
    (4 * graph.edgeFinset.card) ^ 21 * Fintype.card V ^ 22

def RegularCore.order
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj] (K : RegularCore G) : ℕ :=
  @Fintype.card K.W K.fintypeW

/-- The bounded-degree graph delivered by regularization followed by
deterministic sparsification. -/
structure SparseCore {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] where
  W : Type u
  [fintypeW : Fintype W]
  [decEqW : DecidableEq W]
  graph : SimpleGraph W
  [decAdj : DecidableRel graph.Adj]
  contained : graph ⊑ G
  order_large : 64 ≤ Fintype.card W
  edges_nonempty : graph.edgeFinset.Nonempty
  edge_lower : (Fintype.card W : ℝ) ^ ((31 : ℝ) / 21) / 64 ≤
    (graph.edgeFinset.card : ℝ)
  degree_upper : ∀ x,
    (graph.degree x : ℝ) ≤
      (regularFactor + 1 : ℕ) *
        (Fintype.card W : ℝ) ^ ((10 : ℝ) / 21)
  host_growth : G.edgeFinset.card ^ 21 ≤
    4 ^ 21 * Fintype.card W ^ 20 * Fintype.card V ^ 22

def SparseCore.order
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj] (K : SparseCore G) : ℕ :=
  @Fintype.card K.W K.fintypeW

def SparseCore.maximumDegree
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj] (K : SparseCore G) : ℕ :=
  @SimpleGraph.maxDegree K.W K.graph K.fintypeW K.decAdj

lemma SparseCore.maxDegree_upper
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj] (K : SparseCore G) :
    (K.maximumDegree : ℝ) ≤
      (regularFactor + 1 : ℕ) *
        (K.order : ℝ) ^ ((10 : ℝ) / 21) := by
  let : Fintype K.W := K.fintypeW
  let : DecidableEq K.W := K.decEqW
  let : DecidableRel K.graph.Adj := K.decAdj
  let : Nonempty K.W := Fintype.card_pos_iff.mp (by
    have := K.order_large
    omega)
  obtain ⟨v, hv⟩ := K.graph.exists_maximal_degree_vertex
  rw [show K.maximumDegree = K.graph.maxDegree by rfl, hv]
  simpa [SparseCore.order] using K.degree_upper v

lemma RegularCore.host_growth
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (K : RegularCore G) (hm : 0 < K.order) :
    G.edgeFinset.card ^ 21 ≤
      4 ^ 21 * K.order ^ 20 * Fintype.card V ^ 22 := by
  let : Fintype K.W := K.fintypeW
  let : DecidableEq K.W := K.decEqW
  let : DecidableRel K.graph.Adj := K.decAdj
  let m := Fintype.card K.W
  have hedge : K.graph.edgeFinset.card ≤ m ^ 2 := by
    calc
      K.graph.edgeFinset.card ≤ m.choose 2 :=
        K.graph.card_edgeFinset_le_card_choose_two
      _ = m * (m - 1) / 2 := Nat.choose_two_right m
      _ ≤ m * (m - 1) := Nat.div_le_self _ _
      _ ≤ m * m := by gcongr; omega
      _ = m ^ 2 := by ring
  have htransfer := K.transfer
  have hmul :
      G.edgeFinset.card ^ 21 * m ^ 22 ≤
        (4 ^ 21 * m ^ 20 * Fintype.card V ^ 22) * m ^ 22 := by
    calc
      G.edgeFinset.card ^ 21 * m ^ 22 ≤
          (4 * K.graph.edgeFinset.card) ^ 21 *
            Fintype.card V ^ 22 := by simpa [m] using htransfer
      _ ≤ (4 * m ^ 2) ^ 21 * Fintype.card V ^ 22 := by gcongr
      _ = (4 ^ 21 * m ^ 20 * Fintype.card V ^ 22) * m ^ 22 := by ring
  exact le_of_mul_le_mul_right hmul (pow_pos (by simpa [m, RegularCore.order] using hm) 22)

theorem RegularCore.exists_sparseCore
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (K : RegularCore G) (hm : 64 ≤ K.order) :
    Nonempty (SparseCore G) := by
  classical
  let : Fintype K.W := K.fintypeW
  let : DecidableEq K.W := K.decEqW
  let : DecidableRel K.graph.Adj := K.decAdj
  let m := Fintype.card K.W
  let t := densityTarget m
  let D := degreeCapTarget regularFactor m
  have hmpos : 0 < m := by
    have : 64 ≤ m := by simpa [m, RegularCore.order] using hm
    omega
  have htpos : 0 < t := densityTarget_pos hmpos
  have hfour : 4 * t ≤ K.graph.edgeFinset.card := by
    apply four_mul_densityTarget_le (by simpa [m, RegularCore.order] using hm)
    simpa [t, m] using K.density
  have hcap : 8 * regularFactor * t ≤ D * m := by
    simpa [D, t] using
      (degreeCapTarget_mul_card (K := regularFactor) (m := m) hmpos)
  obtain ⟨E, hEsub, htE, hEdeg⟩ := exists_dense_degreeCapped_subset
    K.graph regularFactor D t (by
      dsimp [regularFactor, blockCount]
      positivity) htpos hfour hcap K.almost_regular
  let F := graphOfEdges E
  have hFedges : F.edgeFinset = E := by
    dsimp [F]
    exact edgeFinset_graphOfEdges_of_subset hEsub
  have hcontainedCore : F ⊑ K.graph :=
    SimpleGraph.IsContained.of_le (graphOfEdges_le hEsub)
  refine ⟨{
    W := K.W
    graph := F
    contained := hcontainedCore.trans K.contained
    order_large := by simpa [m, RegularCore.order] using hm
    edges_nonempty := by
      rw [hFedges]
      exact Finset.card_pos.mp (htpos.trans_le htE)
    edge_lower := ?_
    degree_upper := ?_
    host_growth := by
      simpa [m, RegularCore.order] using
        (RegularCore.host_growth K
          (by simpa [m, RegularCore.order] using hmpos)) }⟩
  · rw [hFedges]
    calc
      (Fintype.card K.W : ℝ) ^ ((31 : ℝ) / 21) / 64 ≤
          (densityTarget m : ℝ) := by
        change (Fintype.card K.W : ℝ) ^ ((31 : ℝ) / 21) / 64 ≤
          (↑⌈(Fintype.card K.W : ℝ) ^ ((31 : ℝ) / 21) / 64⌉₊ : ℝ)
        exact Nat.le_ceil _
      _ ≤ (E.card : ℝ) := by exact_mod_cast htE
  · intro x
    have hxD : (F.degree x : ℝ) ≤ D := by
      exact_mod_cast hEdeg x
    have hDupper := degreeCapTarget_cast_lt regularFactor m
      (by simpa [m, RegularCore.order] using hm)
    exact hxD.trans (by
      simpa [D, m] using hDupper.le)

theorem regularCore_of_small
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hsmall : Fintype.card V < blockCount)
    (hdense : Fintype.card V ^ 31 < G.edgeFinset.card ^ 21) :
    Nonempty (RegularCore G) := by
  classical
  let A := G.induce G.support
  have hedge : G.edgeFinset.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro hzero
    rw [hzero] at hdense
    simp at hdense
  have hAedge : A.edgeFinset.card = G.edgeFinset.card := by
    exact G.card_edgeFinset_induce_support
  have hWle : Fintype.card G.support ≤ Fintype.card V := Fintype.card_subtype_le _
  have hreg : ∀ x y, A.degree x ≤ regularFactor * A.degree y := by
    intro x y
    change (G.induce G.support).degree x ≤
      regularFactor * (G.induce G.support).degree y
    rw [G.degree_induce_support, G.degree_induce_support]
    have hx : G.degree x.1 < Fintype.card V := G.degree_lt_card_verts x.1
    have hy : 0 < G.degree y.1 := by
      rw [SimpleGraph.degree_pos_iff_mem_support]
      exact y.2
    have hfactor : Fintype.card V ≤ regularFactor := by
      dsimp [regularFactor]
      omega
    nlinarith
  exact ⟨{
    W := G.support
    graph := A
    contained := ⟨(SimpleGraph.Embedding.induce G.support).toCopy⟩
    edges_nonempty := by
      apply Finset.card_pos.mp
      rw [hAedge]
      exact Finset.card_pos.mpr hedge
    density := by
      rw [hAedge]
      exact (pow_le_pow_left' hWle 31).trans_lt
        (hdense.trans_le (pow_le_pow_left' (by omega) 21))
    almost_regular := hreg
    transfer := by
      rw [hAedge]
      calc
        G.edgeFinset.card ^ 21 * Fintype.card G.support ^ 22 ≤
            G.edgeFinset.card ^ 21 * Fintype.card V ^ 22 := by
          gcongr
        _ ≤ (4 * G.edgeFinset.card) ^ 21 * Fintype.card V ^ 22 := by
          gcongr
          omega }⟩

noncomputable def edgeSupportGraph (E : Finset (Sym2 V)) :
    SimpleGraph (graphOfEdges E).support :=
  (graphOfEdges E).induce (graphOfEdges E).support

noncomputable instance edgeSupportGraph_decidableRel (E : Finset (Sym2 V)) :
    DecidableRel (edgeSupportGraph E).Adj := Classical.decRel _

theorem regularCore_of_top_sparse
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (B : Finset V)
    (hlarge : blockCount ≤ Fintype.card V)
    (hdense : Fintype.card V ^ 31 < G.edgeFinset.card ^ 21)
    (hBcard : B.card = Fintype.card V / blockCount + 1)
    (htop : ∀ x ∉ B, B.card * G.degree x ≤ ∑ y ∈ B, G.degree y)
    (hsparse : 2 * (∑ y ∈ B, G.degree y) ≤ G.edgeFinset.card) :
    Nonempty (RegularCore G) := by
  classical
  let n := Fintype.card V
  let e := G.edgeFinset.card
  let D := outsideEdges G B
  let H := graphOfEdges D
  let t := e / (16 * n)
  have hnpos : 0 < n := blockCount_pos.trans_le hlarge
  have helinear : 32 * n ≤ e := linear_density_of_large hlarge hdense
  have hepos : 0 < e := by omega
  have htpos : 0 < t := by
    dsimp [t]
    apply Nat.div_pos
    · omega
    · positivity
  have hDsub : D ⊆ G.edgeFinset := outsideEdges_subset_edgeFinset G B
  have heD : e ≤ 2 * D.card := by
    have hsplit := card_edgeFinset_le_outside_add_sum_degrees G B
    dsimp [e, D] at hsplit ⊢
    omega
  obtain ⟨E, hED, hcard, hstable⟩ :=
    exists_pruned_indexed D (Finset.univ : Finset V)
      (fun v ↦ H.incidenceFinset v) (fun _ ↦ t)
  have hcost : ∑ _v : V, (t - 1) ≤ e / 16 := by
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    calc
      n * (t - 1) ≤ n * t := by gcongr; omega
      _ ≤ e / 16 := by
        rw [Nat.le_div_iff_mul_le (by omega : 0 < 16)]
        dsimp [t]
        calc
          n * (e / (16 * n)) * 16 = e / (16 * n) * (16 * n) := by ring
          _ ≤ e := Nat.div_mul_le_self _ _
  have heE : e ≤ 4 * E.card := by
    have hcard' : D.card ≤ E.card + e / 16 := hcard.trans (by
      simpa using Nat.add_le_add_left hcost E.card)
    have heighth : 8 * (e / 16) ≤ e := by
      calc
        8 * (e / 16) ≤ 8 * (e / 8) :=
          Nat.mul_le_mul_left 8 (Nat.div_le_div_left (a := e) (by omega) (by omega))
        _ ≤ e := Nat.mul_div_le _ _
    omega
  have hEne : E.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro hzero
    rw [hzero] at heE
    simp at heE
    omega
  have hEsubG : E ⊆ G.edgeFinset := hED.trans hDsub
  let A₀ := graphOfEdges E
  let A := edgeSupportGraph E
  have hAedge : A.edgeFinset.card = E.card := by
    calc
      A.edgeFinset.card = A₀.edgeFinset.card := by
        exact A₀.card_edgeFinset_induce_support
      _ = E.card := by
        exact congrArg Finset.card (edgeFinset_graphOfEdges_of_subset hEsubG)
  have hdegree (v : A₀.support) : A.degree v = A₀.degree v.1 := by
    exact A₀.degree_induce_support v
  have hmin (v : A₀.support) : t ≤ A.degree v := by
    have hvpos : 0 < A₀.degree v.1 := by
      rw [SimpleGraph.degree_pos_iff_mem_support]
      exact v.2
    have hincne : (E ∩ H.incidenceFinset v.1).Nonempty := by
      rw [show E ∩ H.incidenceFinset v.1 = A₀.incidenceFinset v.1 by
        exact incidenceFinset_graphOfEdges_inter hDsub hED v.1]
      rw [← Finset.card_pos, A₀.card_incidenceFinset_eq_degree]
      exact hvpos
    have hs := hstable v.1 (Finset.mem_univ _) hincne
    rw [show E ∩ H.incidenceFinset v.1 = A₀.incidenceFinset v.1 by
      exact incidenceFinset_graphOfEdges_inter hDsub hED v.1,
      A₀.card_incidenceFinset_eq_degree] at hs
    simpa [hdegree v] using hs
  have hmax (v : A₀.support) : A.degree v ≤ regularFactor * t := by
    have hvnot : v.1 ∉ B := by
      have hvpos : 0 < A₀.degree v.1 := by
        rw [SimpleGraph.degree_pos_iff_mem_support]
        exact v.2
      obtain ⟨w, hvw⟩ := (A₀.degree_pos_iff_exists_adj v.1).mp hvpos
      have hedge : s(v.1, w) ∈ E := (graphOfEdges_adj_iff.mp hvw).1
      exact endpoint_not_mem_of_edge_outside G B (hED hedge)
        (by simp)
    have hdegmono : A₀.degree v.1 ≤ G.degree v.1 :=
      SimpleGraph.degree_le_of_le (v := v.1) (graphOfEdges_le hEsubG)
    have htopv := htop v.1 hvnot
    have hsum : ∑ y ∈ B, G.degree y ≤ e := by
      dsimp [e]
      omega
    have hbpos : 0 < B.card := by rw [hBcard]; exact quotientBlock_pos n
    have hnb : n ≤ blockCount * B.card := by
      rw [hBcard]
      exact card_le_blockCount_mul_quotientBlock n
    have heupper : e < 32 * n * t := by
      have hdiv := Nat.lt_mul_div_succ e (by positivity : 0 < 16 * n)
      have htge : 2 ≤ t := by
        dsimp [t]
        rw [Nat.le_div_iff_mul_le (by positivity : 0 < 16 * n)]
        nlinarith
      dsimp [t] at hdiv ⊢
      nlinarith
    have hbd : B.card * A.degree v ≤ e := by
      rw [hdegree]
      exact (Nat.mul_le_mul_left B.card hdegmono).trans (htopv.trans hsum)
    have hrf : regularFactor = 32 * blockCount := rfl
    rw [hrf]
    apply Nat.le_of_mul_le_mul_left (c := B.card) _ hbpos
    calc
      B.card * A.degree v ≤ e := hbd
      _ ≤ 32 * n * t := heupper.le
      _ ≤ B.card * (32 * blockCount * t) := by
        nlinarith
  exact ⟨{
    W := A₀.support
    graph := A
    contained := by
      have hAA₀ : A ⊑ A₀ := by
        simpa [A, A₀, edgeSupportGraph] using
          (show (A₀.induce A₀.support) ⊑ A₀ from
            ⟨(SimpleGraph.Embedding.induce A₀.support).toCopy⟩)
      exact hAA₀.trans_le (graphOfEdges_le hEsubG)
    edges_nonempty := by
      apply Finset.card_pos.mp
      rw [hAedge]
      exact Finset.card_pos.mpr hEne
    density := by
      have hWle : Fintype.card A₀.support ≤ n := Fintype.card_subtype_le _
      rw [hAedge]
      exact (pow_le_pow_left' hWle 31).trans_lt
        (hdense.trans_le (pow_le_pow_left' heE 21))
    almost_regular := fun x y ↦ (hmax x).trans
      (Nat.mul_le_mul_left regularFactor (hmin y))
    transfer := by
      have hWle : Fintype.card A₀.support ≤ n := Fintype.card_subtype_le _
      rw [hAedge]
      calc
        e ^ 21 * Fintype.card A₀.support ^ 22 ≤ e ^ 21 * n ^ 22 := by
          gcongr
        _ ≤ (4 * E.card) ^ 21 * n ^ 22 := by gcongr }⟩

/-- The dense alternative of the top-block dichotomy.  It finds a much
smaller induced graph, loses at most `edgeLossFactor` in edge count, and
preserves the `31/21` density inequality. -/
theorem exists_dense_induced_step
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (B : Finset V)
    (hlarge : blockCount ≤ Fintype.card V)
    (hdense : Fintype.card V ^ 31 < G.edgeFinset.card ^ 21)
    (hBcard : B.card = Fintype.card V / blockCount + 1)
    (hdenseTop : G.edgeFinset.card < 2 * (∑ y ∈ B, G.degree y)) :
    ∃ S : Finset V,
      S.Nonempty ∧
      shrinkFactor * S.card ≤ Fintype.card V ∧
      S.card < Fintype.card V ∧
      G.edgeFinset.card <
        edgeLossFactor * (G.induce (↑S : Set V)).edgeFinset.card ∧
      S.card ^ 31 < (G.induce (↑S : Set V)).edgeFinset.card ^ 21 := by
  classical
  let n := Fintype.card V
  let e := G.edgeFinset.card
  obtain ⟨P, hPeq, hPcard⟩ :=
    Finpartition.exists_equipartition_card_eq (Finset.univ : Finset V)
      blockCount_pos.ne' hlarge
  have hPne : P.parts.Nonempty := by
    rw [← Finset.card_pos, hPcard]
    exact blockCount_pos
  obtain ⟨C, hCP, hmany⟩ := exists_part_with_many_darts G B P hPne
  let S := B ∪ C
  let A := G.induce (↑S : Set V)
  have hCcard : C.card ≤ n / blockCount + 1 := by
    have h := hPeq.card_part_le_average_add_one hCP
    rw [hPcard] at h
    simpa [n] using h
  have hScard : S.card ≤ B.card + C.card := Finset.card_union_le B C
  have hshrink : shrinkFactor * S.card ≤ n := by
    apply (Nat.mul_le_mul_left shrinkFactor hScard).trans
    apply shrink_union_bound hlarge
    · rw [hBcard]
    · exact hCcard
  have hedgeLoss : e < edgeLossFactor * A.edgeFinset.card := by
    have hdarts : (dartsFrom G B).card = ∑ y ∈ B, G.degree y :=
      card_dartsFrom G B
    have hto := card_dartsToPart_le_twice_induced_edges G B P hCP
    dsimp [e, edgeLossFactor]
    rw [← hPcard]
    calc
      G.edgeFinset.card < 2 * (∑ y ∈ B, G.degree y) := hdenseTop
      _ = 2 * (dartsFrom G B).card := by rw [hdarts]
      _ ≤ 2 * (P.parts.card * (dartsToPart G B P C).card) := by gcongr
      _ ≤ 4 * P.parts.card * A.edgeFinset.card := by
        dsimp [A, S] at hto ⊢
        nlinarith
      _ = 4 * P.parts.card *
          (G.induce (↑(B ∪ C) : Set V)).edgeFinset.card := rfl
  have hApos : 0 < A.edgeFinset.card := by
    have hepos : 0 < e := by
      by_contra! hezero
      have heq : e = 0 := by omega
      dsimp [e, n] at heq ⊢
      rw [heq] at hdense
      simp at hdense
    by_contra! hzero
    have heq : A.edgeFinset.card = 0 := by omega
    rw [heq] at hedgeLoss
    simp at hedgeLoss
  have hSne : S.Nonempty := by
    obtain ⟨edge, hedge⟩ := Finset.card_pos.mp hApos
    induction edge using Sym2.inductionOn with
    | _ x y =>
        have hxy : A.Adj x y := A.mem_edgeFinset.mp hedge
        exact ⟨x.1, x.2⟩
  have hSlt : S.card < n := by
    have hs2 := shrinkFactor_two_le
    have hSpos := Finset.card_pos.mpr hSne
    have htwo : 2 * S.card ≤ n :=
      (Nat.mul_le_mul_right S.card hs2).trans hshrink
    omega
  have hSdense : S.card ^ 31 < A.edgeFinset.card ^ 21 := by
    have hlossPow : e ^ 21 ≤
        edgeLossFactor ^ 21 * A.edgeFinset.card ^ 21 := by
      rw [← mul_pow]
      exact pow_le_pow_left' hedgeLoss.le 21
    have hshrinkPow : shrinkFactor ^ 31 * S.card ^ 31 ≤ n ^ 31 := by
      rw [← mul_pow]
      exact pow_le_pow_left' hshrink 31
    have hchain : shrinkFactor ^ 31 * S.card ^ 31 <
        shrinkFactor ^ 31 * A.edgeFinset.card ^ 21 := by
      calc
        shrinkFactor ^ 31 * S.card ^ 31 ≤ n ^ 31 := hshrinkPow
        _ < e ^ 21 := by simpa [n, e] using hdense
        _ ≤ edgeLossFactor ^ 21 * A.edgeFinset.card ^ 21 := hlossPow
        _ ≤ shrinkFactor ^ 31 * A.edgeFinset.card ^ 21 := by
          exact Nat.mul_le_mul_right _ edgeLoss_density_power_le
    have hspos : 0 < shrinkFactor := (by
      exact (by omega : 0 < 2).trans_le shrinkFactor_two_le)
    exact (Nat.mul_lt_mul_left (pow_pos hspos 31)).mp hchain
  exact ⟨S, hSne, hshrink, hSlt, by simpa [S, A, n, e] using hedgeLoss,
    by simpa [S, A] using hSdense⟩

/-- Deterministic Erdős--Simonovits regularization, specialized to the
exponent `31/21`. -/
theorem exists_regularCore
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hdense : Fintype.card V ^ 31 < G.edgeFinset.card ^ 21) :
    Nonempty (RegularCore G) := by
  classical
  induction hn : Fintype.card V using Nat.strong_induction_on generalizing V with
  | h n ih =>
      by_cases hsmall : n < blockCount
      · exact regularCore_of_small G (by simpa [hn] using hsmall) (by simpa [hn] using hdense)
      · have hlarge : blockCount ≤ n := le_of_not_gt hsmall
        let b := n / blockCount + 1
        have hb : b ≤ Fintype.card V := by
          rw [hn]
          exact quotientBlock_le_card hlarge
        obtain ⟨B, hBcard, htop⟩ :=
          exists_top_subset (fun v ↦ G.degree v) b hb
        by_cases hsparse : 2 * (∑ y ∈ B, G.degree y) ≤ G.edgeFinset.card
        · exact regularCore_of_top_sparse G B (by simpa [hn] using hlarge)
            (by simpa [hn] using hdense) (by simpa [b, hn] using hBcard)
            (by
              intro x hx
              rw [hBcard]
              exact htop x hx) hsparse
        · have hdenseTop : G.edgeFinset.card <
              2 * (∑ y ∈ B, G.degree y) := lt_of_not_ge hsparse
          obtain ⟨S, hSne, hshrink, hSlt, hedgeLoss, hSdense⟩ :=
            exists_dense_induced_step G B (by simpa [hn] using hlarge)
              (by simpa [hn] using hdense) (by simpa [b, hn] using hBcard)
              hdenseTop
          let A := G.induce (↑S : Set V)
          have hSlt' : S.card < n := by simpa [hn] using hSlt
          have hrec : Nonempty (RegularCore A) := by
            apply ih S.card hSlt' (V := ↑S) A
            · simpa [A] using hSdense
            · exact Fintype.card_coe S
          obtain ⟨K⟩ := hrec
          let : Fintype K.W := K.fintypeW
          let : DecidableEq K.W := K.decEqW
          let : DecidableRel K.graph.Adj := K.decAdj
          have hAG : A ⊑ G := by
            simpa [A] using
              (show (G.induce (↑S : Set V)) ⊑ G from
                ⟨(SimpleGraph.Embedding.induce (↑S : Set V)).toCopy⟩)
          refine ⟨{
            W := K.W
            graph := K.graph
            contained := K.contained.trans hAG
            edges_nonempty := K.edges_nonempty
            density := K.density
            almost_regular := K.almost_regular
            transfer := ?_ }⟩
          let e := G.edgeFinset.card
          let e' := A.edgeFinset.card
          let f := K.graph.edgeFinset.card
          let m := Fintype.card K.W
          let n' := S.card
          have hepow : e ^ 21 ≤ edgeLossFactor ^ 21 * e' ^ 21 := by
            rw [← mul_pow]
            exact pow_le_pow_left' hedgeLoss.le 21
          have hnpow : shrinkFactor ^ 22 * n' ^ 22 ≤ n ^ 22 := by
            rw [← mul_pow]
            exact pow_le_pow_left' (by simpa [n', hn] using hshrink) 22
          have htransfer := K.transfer
          dsimp [e', f, m, n', A] at htransfer ⊢
          dsimp [e, e', f, m, n', A] at hepow hnpow
          calc
            G.edgeFinset.card ^ 21 * Fintype.card K.W ^ 22 ≤
                (edgeLossFactor ^ 21 * A.edgeFinset.card ^ 21) *
                  Fintype.card K.W ^ 22 := by gcongr
            _ = edgeLossFactor ^ 21 *
                (A.edgeFinset.card ^ 21 * Fintype.card K.W ^ 22) := by ring
            _ ≤ edgeLossFactor ^ 21 *
                ((4 * K.graph.edgeFinset.card) ^ 21 * S.card ^ 22) := by
              apply Nat.mul_le_mul_left
              simpa using htransfer
            _ ≤ shrinkFactor ^ 22 *
                ((4 * K.graph.edgeFinset.card) ^ 21 * S.card ^ 22) := by
              exact Nat.mul_le_mul_right _ edgeLoss_power_le_shrink_power
            _ = (4 * K.graph.edgeFinset.card) ^ 21 *
                (shrinkFactor ^ 22 * S.card ^ 22) := by ring
            _ ≤ (4 * K.graph.edgeFinset.card) ^ 21 * n ^ 22 := by
              exact Nat.mul_le_mul_left _ hnpow
            _ = (4 * K.graph.edgeFinset.card) ^ 21 * Fintype.card V ^ 22 := by
              rw [hn]

def sparseCoreHostThreshold : ℕ := 4 ^ 21 * 64 ^ 20 + 1

/-- A host above the `31/21` density scale and beyond one explicit finite
threshold has a bounded-degree sparse core.  The threshold only excludes the
possibility that the regularization descent ends on fewer than 64 vertices. -/
theorem exists_sparseCore_of_large_host
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hlarge : sparseCoreHostThreshold ≤ Fintype.card V)
    (hdense : (Fintype.card V : ℝ) ^ ((31 : ℝ) / 21) <
      (G.edgeFinset.card : ℝ)) :
    Nonempty (SparseCore G) := by
  classical
  have hdensePow : Fintype.card V ^ 31 < G.edgeFinset.card ^ 21 :=
    power_density_of_rpow_density hdense
  obtain ⟨K⟩ := exists_regularCore G hdensePow
  let : Fintype K.W := K.fintypeW
  let : DecidableEq K.W := K.decEqW
  let : DecidableRel K.graph.Adj := K.decAdj
  have hmpos : 0 < K.order := by
    obtain ⟨e, he⟩ := K.edges_nonempty
    induction e using Sym2.inductionOn with
    | _ x y =>
        have : 0 < Fintype.card K.W := Fintype.card_pos_iff.mpr ⟨x⟩
        simpa [RegularCore.order] using this
  by_cases hm : 64 ≤ K.order
  · exact K.exists_sparseCore hm
  · have hm64 : K.order ≤ 64 := by omega
    have hgrowth := K.host_growth hmpos
    let C : ℕ := 4 ^ 21 * 64 ^ 20
    have hmPow : K.order ^ 20 ≤ 64 ^ 20 := pow_le_pow_left' hm64 20
    have hchain : Fintype.card V ^ 31 < C * Fintype.card V ^ 22 := by
      calc
        Fintype.card V ^ 31 < G.edgeFinset.card ^ 21 := hdensePow
        _ ≤ 4 ^ 21 * K.order ^ 20 * Fintype.card V ^ 22 := hgrowth
        _ ≤ (4 ^ 21 * 64 ^ 20) * Fintype.card V ^ 22 := by gcongr
        _ = C * Fintype.card V ^ 22 := rfl
    have hnpos : 0 < Fintype.card V := by
      have : 0 < sparseCoreHostThreshold := by
        dsimp [sparseCoreHostThreshold]
        positivity
      exact this.trans_le hlarge
    have hcancel : Fintype.card V ^ 9 < C := by
      apply lt_of_mul_lt_mul_right (a := Fintype.card V ^ 22) _
        (Nat.zero_le _)
      simpa [← pow_add] using hchain
    have hnlepow : Fintype.card V ≤ Fintype.card V ^ 9 := by
      calc
        Fintype.card V = Fintype.card V ^ 1 := by simp
        _ ≤ Fintype.card V ^ 9 :=
          pow_le_pow_right₀ (by omega : 1 ≤ Fintype.card V) (by omega)
    have hCN : C + 1 ≤ Fintype.card V := by
      simpa [C, sparseCoreHostThreshold] using hlarge
    omega

end

end Erdos113AlmostRegular
