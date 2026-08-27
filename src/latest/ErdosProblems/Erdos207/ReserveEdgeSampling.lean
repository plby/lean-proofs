/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.MasterIterationData

/-!
# Independent sampling of crossing reserve edges

This is the finite probability space used at the start of KSSS Proposition
10.6.  Only edges of `G` crossing the indicated vertex set can be retained,
and every fixed collection of such edges has exactly the expected product
probability.
-/

namespace Erdos207

open Finset
open scoped NNReal

noncomputable section

/-- A symmetric pair has at least one endpoint in `U` and at least one
endpoint outside `U`. -/
def IsCrossingEdge
    {V : Type*} [DecidableEq V] (U : Finset V) (e : Sym2 V) : Prop :=
  (e.toFinset ∩ U).Nonempty ∧ (e.toFinset \ U).Nonempty

/-- Edges of `G` crossing from `U` to its complement. -/
noncomputable def crossingEdges
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (U : Finset V) : Finset (Sym2 V) := by
  classical
  exact (graphEdges G).filter (IsCrossingEdge U)

@[simp]
lemma mem_crossingEdges_iff
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {U : Finset V} {e : Sym2 V} :
    e ∈ crossingEdges G U ↔ e ∈ G.edgeSet ∧ IsCrossingEdge U e := by
  classical
  simp [crossingEdges]

/-- The Bernoulli parameter is `r` on crossing edges and zero elsewhere. -/
def reserveEdgeProbability
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (U : Finset V) (r : ℝ≥0) (e : Sym2 V) : ℝ≥0 :=
  if e ∈ crossingEdges G U then r else 0

lemma reserveEdgeProbability_le_one
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (U : Finset V) {r : ℝ≥0} (hr : r ≤ 1)
    (e : Sym2 V) : reserveEdgeProbability G U r e ≤ 1 := by
  unfold reserveEdgeProbability
  split_ifs
  · exact hr
  · exact zero_le_one

/-- Independent reserve-edge bits. -/
def reserveEdgeLaw
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (U : Finset V) (r : ℝ≥0) (hr : r ≤ 1) :
    FiniteLaw (Sym2 V → Bool) :=
  FiniteLaw.independentBits (reserveEdgeProbability G U r)
    (reserveEdgeProbability_le_one G U hr)

/-- The finite set selected by the reserve-edge bits, restricted
definitionally to the relevant crossing edges. -/
def reserveEdges
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (U : Finset V) (ω : Sym2 V → Bool) :
    Finset (Sym2 V) :=
  (crossingEdges G U).filter fun e ↦ ω e = true

@[simp]
lemma mem_reserveEdges_iff
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {U : Finset V} {ω : Sym2 V → Bool}
    {e : Sym2 V} :
    e ∈ reserveEdges G U ω ↔
      e ∈ crossingEdges G U ∧ ω e = true := by
  classical
  simp [reserveEdges]

lemma reserveEdges_subset_crossingEdges
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (U : Finset V) (ω : Sym2 V → Bool) :
    reserveEdges G U ω ⊆ crossingEdges G U :=
  filter_subset _ _

lemma reserveEdges_subset_graphEdges
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (U : Finset V) (ω : Sym2 V → Bool) :
    reserveEdges G U ω ⊆ graphEdges G := by
  intro e he
  exact mem_graphEdges_iff.mpr
    (mem_crossingEdges_iff.mp (reserveEdges_subset_crossingEdges G U ω he)).1

/-- At density one every crossing edge is selected at every positive-mass
outcome.  This support statement is stronger than the corresponding
probability-one equality and is stable under all subsequent conditionings. -/
theorem reserveEdgeLaw_one_supported_full
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (U : Finset V) :
    (reserveEdgeLaw G U 1 (by norm_num)).SupportedOn fun bits ↦
      reserveEdges G U bits = crossingEdges G U := by
  intro bits hmass
  apply Subset.antisymm
  · exact reserveEdges_subset_crossingEdges G U bits
  · intro e he
    rw [mem_reserveEdges_iff]
    refine ⟨he, ?_⟩
    by_contra hfalse
    have hbit : bits e = false := Bool.eq_false_of_not_eq_true hfalse
    have hfactor : FiniteLaw.bernoulliBitMass
        (reserveEdgeProbability G U 1 e) (bits e) = 0 := by
      simp [reserveEdgeProbability, he, hbit,
        FiniteLaw.bernoulliBitMass]
    have hzero : (reserveEdgeLaw G U 1 (by norm_num)).mass bits = 0 := by
      rw [reserveEdgeLaw, FiniteLaw.independentBits_mass]
      exact Finset.prod_eq_zero (Finset.mem_univ e) hfactor
    rw [hzero] at hmass
    exact (lt_irrefl 0 hmass).elim

/-- Exact product probability for simultaneous inclusion of fixed crossing
edges in the reserve. -/
theorem reserveEdgeLaw_probability_subset_reserveEdges
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (U : Finset V) (r : ℝ≥0) (hr : r ≤ 1)
    (T : Finset (Sym2 V)) (hT : T ⊆ crossingEdges G U) :
    (reserveEdgeLaw G U r hr).probability
        (fun ω ↦ T ⊆ reserveEdges G U ω) = r ^ T.card := by
  have hevent : (fun ω ↦ T ⊆ reserveEdges G U ω) =
      (fun ω ↦ ∀ e ∈ T, ω e = true) := by
    funext ω
    apply propext
    constructor
    · intro h e he
      exact (mem_reserveEdges_iff.mp (h he)).2
    · intro h e he
      exact mem_reserveEdges_iff.mpr ⟨hT he, h e he⟩
  rw [hevent]
  unfold reserveEdgeLaw
  rw [FiniteLaw.independentBits_probability_forall_true]
  calc
    ∏ e ∈ T, reserveEdgeProbability G U r e = ∏ _e ∈ T, r := by
      apply prod_congr rfl
      intro e he
      simp [reserveEdgeProbability, hT he]
    _ = r ^ T.card := by simp

/-- Exact product probability for simultaneous exclusion of fixed crossing
edges from the reserve. -/
theorem reserveEdgeLaw_probability_disjoint_reserveEdges
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (U : Finset V) (r : ℝ≥0) (hr : r ≤ 1)
    (T : Finset (Sym2 V)) (hT : T ⊆ crossingEdges G U) :
    (reserveEdgeLaw G U r hr).probability
        (fun ω ↦ Disjoint T (reserveEdges G U ω)) =
      (1 - r) ^ T.card := by
  have hevent : (fun ω ↦ Disjoint T (reserveEdges G U ω)) =
      (fun ω ↦ ∀ e ∈ T, ω e = false) := by
    funext ω
    apply propext
    rw [Finset.disjoint_left]
    constructor
    · intro h e he
      cases heq : ω e
      · rfl
      · exact (h he (mem_reserveEdges_iff.mpr ⟨hT he, heq⟩)).elim
    · intro h e heT heR
      have htrue := (mem_reserveEdges_iff.mp heR).2
      rw [h e heT] at htrue
      simp at htrue
  rw [hevent]
  unfold reserveEdgeLaw
  rw [FiniteLaw.independentBits_probability_forall_false]
  calc
    ∏ e ∈ T, (1 - reserveEdgeProbability G U r e) =
        ∏ _e ∈ T, (1 - r) := by
      apply prod_congr rfl
      intro e he
      simp [reserveEdgeProbability, hT he]
    _ = (1 - r) ^ T.card := by simp

/-- A binomial upper-tail union bound, stated in the form used for reserve
degrees and codegrees. -/
theorem reserveEdgeLaw_probability_card_inter_ge_le
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (U : Finset V) (r : ℝ≥0) (hr : r ≤ 1)
    (S : Finset (Sym2 V)) (hS : S ⊆ crossingEdges G U) (k : ℕ) :
    (reserveEdgeLaw G U r hr).probability
        (fun ω ↦ k ≤ (S ∩ reserveEdges G U ω).card) ≤
      (Nat.choose S.card k : ℝ≥0) * r ^ k := by
  let L := reserveEdgeLaw G U r hr
  let P : Finset (Sym2 V) → (Sym2 V → Bool) → Prop :=
    fun T ω ↦ T ⊆ reserveEdges G U ω
  calc
    L.probability
        (fun ω ↦ k ≤ (S ∩ reserveEdges G U ω).card) ≤
      L.probability
        (fun ω ↦ ∃ T ∈ S.powersetCard k, P T ω) := by
          apply L.probability_mono
          intro ω hcard
          obtain ⟨T, hTsub, hTcard⟩ :=
            exists_subset_card_eq hcard
          refine ⟨T, mem_powersetCard.mpr ⟨?_, hTcard⟩, ?_⟩
          · exact hTsub.trans inter_subset_left
          · exact hTsub.trans inter_subset_right
    _ ≤ ∑ T ∈ S.powersetCard k, L.probability (P T) :=
      L.probability_exists_le (S.powersetCard k) P
    _ = ∑ _T ∈ S.powersetCard k, r ^ k := by
      apply sum_congr rfl
      intro T hT
      have hTdata := mem_powersetCard.mp hT
      rw [show L.probability (P T) = r ^ T.card by
        exact reserveEdgeLaw_probability_subset_reserveEdges
          G U r hr T (hTdata.1.trans hS)]
      rw [hTdata.2]
    _ = (Nat.choose S.card k : ℝ≥0) * r ^ k := by
      simp [card_powersetCard]

/-- A binomial lower-tail union bound, obtained by exposing a prescribed
set of absent reserve edges. -/
theorem reserveEdgeLaw_probability_card_inter_le_le
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (U : Finset V) (r : ℝ≥0) (hr : r ≤ 1)
    (S : Finset (Sym2 V)) (hS : S ⊆ crossingEdges G U) (k : ℕ) :
    (reserveEdgeLaw G U r hr).probability
        (fun ω ↦ (S ∩ reserveEdges G U ω).card ≤ k) ≤
      (Nat.choose S.card (S.card - k) : ℝ≥0) *
        (1 - r) ^ (S.card - k) := by
  let L := reserveEdgeLaw G U r hr
  let absentCount := S.card - k
  let P : Finset (Sym2 V) → (Sym2 V → Bool) → Prop :=
    fun T ω ↦ Disjoint T (reserveEdges G U ω)
  calc
    L.probability
        (fun ω ↦ (S ∩ reserveEdges G U ω).card ≤ k) ≤
      L.probability
        (fun ω ↦ ∃ T ∈ S.powersetCard absentCount, P T ω) := by
          apply L.probability_mono
          intro ω hcard
          have hpartition := card_sdiff_add_card_inter S
            (reserveEdges G U ω)
          have habsent : absentCount ≤
              (S \ reserveEdges G U ω).card := by
            dsimp only [absentCount]
            omega
          obtain ⟨T, hTsub, hTcard⟩ :=
            exists_subset_card_eq habsent
          refine ⟨T, mem_powersetCard.mpr ⟨?_, hTcard⟩, ?_⟩
          · exact hTsub.trans (sdiff_subset)
          · change Disjoint T (reserveEdges G U ω)
            rw [Finset.disjoint_left]
            intro e heT heR
            exact (mem_sdiff.mp (hTsub heT)).2 heR
    _ ≤ ∑ T ∈ S.powersetCard absentCount, L.probability (P T) :=
      L.probability_exists_le (S.powersetCard absentCount) P
    _ = ∑ _T ∈ S.powersetCard absentCount, (1 - r) ^ absentCount := by
      apply sum_congr rfl
      intro T hT
      have hTdata := mem_powersetCard.mp hT
      rw [show L.probability (P T) = (1 - r) ^ T.card by
        exact reserveEdgeLaw_probability_disjoint_reserveEdges
          G U r hr T (hTdata.1.trans hS)]
      rw [hTdata.2]
    _ = (Nat.choose S.card (S.card - k) : ℝ≥0) *
        (1 - r) ^ (S.card - k) := by
      simp [absentCount, card_powersetCard]

/-- The reserve graph associated to an outcome. -/
def reserveGraph
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (U : Finset V) (ω : Sym2 V → Bool) :
    SimpleGraph V :=
  SimpleGraph.fromEdgeSet (reserveEdges G U ω : Set (Sym2 V))

lemma reserveEdges_loopless
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (U : Finset V) (ω : Sym2 V → Bool) :
    ∀ e ∈ reserveEdges G U ω, ¬ e.IsDiag := by
  intro e he
  apply G.not_isDiag_of_mem_edgeSet
  exact mem_graphEdges_iff.mp (reserveEdges_subset_graphEdges G U ω he)

lemma reserveGraph_edgeSet
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (U : Finset V) (ω : Sym2 V → Bool) :
    (reserveGraph G U ω).edgeSet =
      (reserveEdges G U ω : Set (Sym2 V)) := by
  unfold reserveGraph
  rw [SimpleGraph.edgeSet_fromEdgeSet]
  ext e
  simp only [Set.mem_sdiff, Finset.mem_coe, Sym2.mem_diagSet]
  constructor
  · exact fun h ↦ h.1
  · intro he
    exact ⟨he, reserveEdges_loopless G U ω e he⟩

/-- Every reserve graph is a subgraph of `G`. -/
lemma reserveGraph_le
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (U : Finset V) (ω : Sym2 V → Bool) :
    reserveGraph G U ω ≤ G := by
  rw [← SimpleGraph.edgeSet_subset_edgeSet]
  rw [reserveGraph_edgeSet]
  intro e he
  exact mem_graphEdges_iff.mp (reserveEdges_subset_graphEdges G U ω he)

end

end Erdos207
