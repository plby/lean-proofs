import ErdosProblems.Erdos565.RandomGraph
import Mathlib.Topology.Algebra.Order.LiminfLimsup

/-!
# The uniform random graph for Erdős Problem 807

This file gives a finite, exact model of `G(n, 1 / 2)`.  An event is a
predicate on labelled simple graphs on `Fin n`, and its probability is its
cardinality divided by the number `2 ^ (n.choose 2)` of such graphs.  This
avoids installing a global measurable-space instance on `SimpleGraph` while
retaining the usual probability identities and a `Tendsto`-based definition
of "with high probability".

The last section records exact counts for events prescribing arbitrary values
of a finite family of edge coordinates.
-/

open Filter
open scoped Topology

namespace Erdos807
namespace RandomGraph

/-! ## The finite uniform probability -/

/-- An event in the labelled random graph on `Fin n`. -/
abbrev Event (n : ℕ) := SimpleGraph (Fin n) → Prop

/-- The number of labelled graphs in an event.  Decidability is deliberately
hidden: all sample spaces in this file are finite. -/
noncomputable def eventCard (n : ℕ) (P : Event n) : ℕ := by
  exact Set.ncard {G | P G}

/-- The exact uniform probability of an event in `G(n, 1 / 2)`. -/
noncomputable def probability (n : ℕ) (P : Event n) : ℝ :=
  (eventCard n P : ℝ) / (2 ^ n.choose 2 : ℕ)

/-- A sequence of graph properties holds asymptotically almost surely, or
with high probability, when its exact uniform probability tends to one. -/
def AlmostSurely (P : (n : ℕ) → Event n) : Prop :=
  Tendsto (fun n ↦ probability n (P n)) atTop (𝓝 1)

/-- Standard short name for `AlmostSurely`. -/
abbrev Whp := AlmostSurely

/-- Lower-case spelling convenient inside theorem statements. -/
abbrev whp := AlmostSurely

/-- The number of labelled simple graphs on `Fin n`. -/
@[simp] theorem card_simpleGraph (n : ℕ) :
    Fintype.card (SimpleGraph (Fin n)) = 2 ^ n.choose 2 := by
  simpa using (Erdos565.RandomGraph.card_simpleGraph (V := Fin n))

@[simp] theorem eventCard_true (n : ℕ) :
    eventCard n (fun _ ↦ True) = 2 ^ n.choose 2 := by
  simp [eventCard, Nat.card_eq_fintype_card, card_simpleGraph]

@[simp] theorem eventCard_false (n : ℕ) :
    eventCard n (fun _ ↦ False) = 0 := by
  simp [eventCard]

theorem eventCard_mono {n : ℕ} {P Q : Event n} (h : ∀ G, P G → Q G) :
    eventCard n P ≤ eventCard n Q := by
  unfold eventCard
  exact Set.ncard_le_ncard h

theorem eventCard_le_total (n : ℕ) (P : Event n) :
    eventCard n P ≤ 2 ^ n.choose 2 := by
  simpa only [eventCard_true] using
    (eventCard_mono (n := n) (P := P) (Q := fun _ ↦ True) (fun _ _ ↦ trivial))

@[simp] theorem probability_true (n : ℕ) :
    probability n (fun _ ↦ True) = 1 := by
  simp [probability]

@[simp] theorem probability_false (n : ℕ) :
    probability n (fun _ ↦ False) = 0 := by
  simp [probability]

theorem probability_nonneg (n : ℕ) (P : Event n) : 0 ≤ probability n P := by
  exact div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)

theorem probability_le_one (n : ℕ) (P : Event n) : probability n P ≤ 1 := by
  rw [probability, div_le_one]
  · exact_mod_cast eventCard_le_total n P
  · positivity

theorem probability_mem_Icc (n : ℕ) (P : Event n) : probability n P ∈ Set.Icc 0 1 :=
  ⟨probability_nonneg n P, probability_le_one n P⟩

theorem probability_mono {n : ℕ} {P Q : Event n} (h : ∀ G, P G → Q G) :
    probability n P ≤ probability n Q := by
  unfold probability
  gcongr
  exact_mod_cast eventCard_mono h

/-! ## Boolean operations on events -/

theorem eventCard_compl (n : ℕ) (P : Event n) :
    eventCard n (fun G ↦ ¬ P G) = 2 ^ n.choose 2 - eventCard n P := by
  unfold eventCard
  simpa only [Set.compl_ofPred, Nat.card_eq_fintype_card, card_simpleGraph] using
    Set.ncard_compl {G : SimpleGraph (Fin n) | P G}

theorem probability_compl (n : ℕ) (P : Event n) :
    probability n (fun G ↦ ¬ P G) = 1 - probability n P := by
  rw [probability, probability, eventCard_compl]
  have hle := eventCard_le_total n P
  rw [Nat.cast_sub hle]
  field_simp

theorem eventCard_union_le (n : ℕ) (P Q : Event n) :
    eventCard n (fun G ↦ P G ∨ Q G) ≤ eventCard n P + eventCard n Q := by
  unfold eventCard
  exact Set.ncard_union_le {G : SimpleGraph (Fin n) | P G} {G | Q G}

theorem probability_union_le (n : ℕ) (P Q : Event n) :
    probability n (fun G ↦ P G ∨ Q G) ≤ probability n P + probability n Q := by
  unfold probability
  rw [← add_div]
  gcongr
  exact_mod_cast eventCard_union_le n P Q

theorem probability_inter_le_left (n : ℕ) (P Q : Event n) :
    probability n (fun G ↦ P G ∧ Q G) ≤ probability n P :=
  probability_mono (fun _ h ↦ h.1)

theorem probability_inter_le_right (n : ℕ) (P Q : Event n) :
    probability n (fun G ↦ P G ∧ Q G) ≤ probability n Q :=
  probability_mono (fun _ h ↦ h.2)

theorem probability_union_add_inter (n : ℕ) (P Q : Event n) :
    probability n (fun G ↦ P G ∨ Q G) +
        probability n (fun G ↦ P G ∧ Q G) =
      probability n P + probability n Q := by
  have hc : eventCard n (fun G ↦ P G ∨ Q G) +
      eventCard n (fun G ↦ P G ∧ Q G) = eventCard n P + eventCard n Q := by
    unfold eventCard
    exact Set.ncard_union_add_ncard_inter
      {G : SimpleGraph (Fin n) | P G} {G | Q G}
  unfold probability
  rw [← add_div, ← add_div]
  congr 1
  exact_mod_cast hc

theorem one_sub_probability_le_probability_compl {n : ℕ} {P Q : Event n}
    (h : ∀ G, ¬ P G → Q G) :
    1 - probability n P ≤ probability n Q := by
  rw [← probability_compl]
  exact probability_mono h

theorem probability_inter_ge (n : ℕ) (P Q : Event n) :
    probability n P + probability n Q - 1 ≤
      probability n (fun G ↦ P G ∧ Q G) := by
  have h := probability_union_add_inter n P Q
  have hu := probability_le_one n (fun G ↦ P G ∨ Q G)
  linarith

/-! ### Finite union bounds -/

theorem eventCard_exists_le_sum {n : ℕ} {I : Type*} [DecidableEq I]
    (s : Finset I) (P : I → Event n) :
    eventCard n (fun G ↦ ∃ i ∈ s, P i G) ≤ ∑ i ∈ s, eventCard n (P i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [eventCard]
  | @insert a s ha ih =>
      have hmono : eventCard n (fun G ↦ ∃ i ∈ insert a s, P i G) ≤
          eventCard n (fun G ↦ P a G ∨ ∃ i ∈ s, P i G) := by
        apply eventCard_mono
        intro G hG
        simpa [ha] using hG
      calc
        eventCard n (fun G ↦ ∃ i ∈ insert a s, P i G) ≤
            eventCard n (fun G ↦ P a G ∨ ∃ i ∈ s, P i G) := hmono
        _ ≤ eventCard n (P a) + eventCard n (fun G ↦ ∃ i ∈ s, P i G) :=
          eventCard_union_le n _ _
        _ ≤ eventCard n (P a) + ∑ i ∈ s, eventCard n (P i) :=
          Nat.add_le_add_left ih _
        _ = ∑ i ∈ insert a s, eventCard n (P i) := by simp [ha]

theorem probability_exists_le_sum {n : ℕ} {I : Type*} [DecidableEq I]
    (s : Finset I) (P : I → Event n) :
    probability n (fun G ↦ ∃ i ∈ s, P i G) ≤
      ∑ i ∈ s, probability n (P i) := by
  classical
  unfold probability
  rw [← Finset.sum_div]
  gcongr
  exact_mod_cast eventCard_exists_le_sum s P

/-! ## With-high-probability helpers -/

theorem almostSurely_iff_compl_tendsto_zero (P : (n : ℕ) → Event n) :
    AlmostSurely P ↔
      Tendsto (fun n ↦ probability n (fun G ↦ ¬ P n G)) atTop (𝓝 0) := by
  rw [AlmostSurely]
  constructor
  · intro h
    have h' := (tendsto_const_nhds.sub h :
      Tendsto (fun n : ℕ ↦ 1 - probability n (P n)) atTop (𝓝 (1 - 1)))
    simpa only [probability_compl, sub_self] using h'
  · intro h
    have h' := (tendsto_const_nhds.sub h :
      Tendsto (fun n : ℕ ↦ 1 - probability n (fun G ↦ ¬ P n G)) atTop
        (𝓝 (1 - 0)))
    convert h' using 1 <;> simp [probability_compl]

theorem AlmostSurely.mono {P Q : (n : ℕ) → Event n} (hP : AlmostSurely P)
    (hPQ : ∀ᶠ n in atTop, ∀ G, P n G → Q n G) : AlmostSurely Q := by
  rw [almostSurely_iff_compl_tendsto_zero] at hP ⊢
  apply squeeze_zero'
    (Filter.Eventually.of_forall fun n ↦ probability_nonneg n (fun G ↦ ¬ Q n G))
    _ hP
  filter_upwards [hPQ] with n hn
  exact probability_mono (fun G hQ hPG ↦ hQ (hn G hPG))

/-! ## Edge coordinates and prescribed-edge events -/

/-- A possible edge of a graph on `Fin n`: a non-diagonal unordered pair. -/
abbrev Edge (n : ℕ) := Erdos565.RandomGraph.Edge (Fin n)

/-- The finite universe of possible edges on `Fin n`. -/
def allEdges (n : ℕ) : Finset (Edge n) := Erdos565.RandomGraph.edgeUniverse (Fin n)

/-- Recover the finite set of edges of a labelled graph. -/
noncomputable def edges (G : SimpleGraph (Fin n)) : Finset (Edge n) :=
  Erdos565.RandomGraph.edgesOfGraph G

/-- Build a graph from a finite set of valid edge coordinates. -/
def graphOfEdges (S : Finset (Edge n)) : SimpleGraph (Fin n) :=
  Erdos565.RandomGraph.graphOfEdges S

@[simp] theorem card_allEdges (n : ℕ) : (allEdges n).card = n.choose 2 := by
  simp [allEdges]

@[simp] theorem mem_edges {G : SimpleGraph (Fin n)} {e : Edge n} :
    e ∈ edges G ↔ e.1 ∈ G.edgeSet := by
  simp [edges]

@[simp] theorem edges_graphOfEdges (S : Finset (Edge n)) :
    edges (graphOfEdges S) = S := by
  simp [edges, graphOfEdges]

@[simp] theorem graphOfEdges_edges (G : SimpleGraph (Fin n)) :
    graphOfEdges (edges G) = G := by
  simp [edges, graphOfEdges]

theorem edges_subset_allEdges (G : SimpleGraph (Fin n)) : edges G ⊆ allEdges n := by
  intro e _
  simp [allEdges, Erdos565.RandomGraph.edgeUniverse]

/-- The number of edge-coordinate subsets satisfying a predicate. -/
noncomputable def edgeEventCard (n : ℕ) (P : Finset (Edge n) → Prop) : ℕ := by
  exact Set.ncard {S | S ⊆ allEdges n ∧ P S}

/-- Counting graph events may be transported exactly to the Boolean space of
edge-coordinate subsets. -/
theorem eventCard_eq_edgeCard (n : ℕ) (P : Finset (Edge n) → Prop) :
    eventCard n (fun G ↦ P (edges G)) =
      edgeEventCard n P := by
  classical
  unfold eventCard edgeEventCard
  apply Set.ncard_congr (fun G _ ↦ edges G)
  · intro G hG
    exact ⟨edges_subset_allEdges G, hG⟩
  · intro G _ H _ h
    simpa only [graphOfEdges_edges] using congrArg graphOfEdges h
  · intro S hS
    refine ⟨graphOfEdges S, ?_, edges_graphOfEdges S⟩
    show P (edges (graphOfEdges S))
    simpa only [edges_graphOfEdges] using hS.2

/-- `Prescribed A B G` says that the edge coordinates of `G`, restricted to
`A`, are exactly `B`.  The hypothesis `B ⊆ A` in the counting theorems says
that this prescription is consistent. -/
def Prescribed (A B : Finset (Edge n)) (G : SimpleGraph (Fin n)) : Prop :=
  Erdos565.RandomGraph.restrict A (edges G) = B

/-- Exactly `2^(N-|A|)` graphs realize any consistent prescription on `A`. -/
theorem card_prescribed {n : ℕ} {A B : Finset (Edge n)}
    (hB : B ⊆ A) :
    eventCard n (Prescribed A B) = 2 ^ (n.choose 2 - A.card) := by
  change eventCard n (fun G ↦
    Erdos565.RandomGraph.restrict A (edges G) = B) = _
  calc
    eventCard n (fun G ↦ Erdos565.RandomGraph.restrict A (edges G) = B) =
        edgeEventCard n (fun S ↦ Erdos565.RandomGraph.restrict A S = B) :=
      eventCard_eq_edgeCard n
        (fun S : Finset (Edge n) ↦ Erdos565.RandomGraph.restrict A S = B)
    _ = 2 ^ (n.choose 2 - A.card) := by
      unfold edgeEventCard
      change Set.ncard {S : Finset (Edge n) |
        S ⊆ allEdges n ∧ Erdos565.RandomGraph.restrict A S = B} = _
      have heq :
          {S : Finset (Edge n) |
            S ⊆ allEdges n ∧ Erdos565.RandomGraph.restrict A S = B} =
            ((allEdges n).powerset.filter
              (fun S ↦ Erdos565.RandomGraph.restrict A S = B) :
                Set (Finset (Edge n))) := by
        ext S
        simp
      calc
        Set.ncard {S : Finset (Edge n) |
            S ⊆ allEdges n ∧ Erdos565.RandomGraph.restrict A S = B} =
            Set.ncard ((allEdges n).powerset.filter
              (fun S ↦ Erdos565.RandomGraph.restrict A S = B) :
                Set (Finset (Edge n))) := congrArg Set.ncard heq
        _ = ((allEdges n).powerset.filter
              (fun S ↦ Erdos565.RandomGraph.restrict A S = B)).card :=
          Set.ncard_coe_finset _
        _ = 2 ^ (n.choose 2 - A.card) := by
          simpa [allEdges] using
            Erdos565.RandomGraph.card_restrict_fiber (allEdges n) A B
              (by simp [allEdges, Erdos565.RandomGraph.edgeUniverse]) hB

/-- Exact probability of any consistent assignment of `|A|` edge bits. -/
theorem probability_prescribed {n : ℕ} {A B : Finset (Edge n)}
    (hB : B ⊆ A) :
    probability n (Prescribed A B) = (1 / 2 : ℝ) ^ A.card := by
  rw [probability, card_prescribed hB]
  have hA : A.card ≤ n.choose 2 := by
    rw [← card_allEdges n]
    exact Finset.card_le_card (by
      intro e _
      simp [allEdges, Erdos565.RandomGraph.edgeUniverse])
  rw [show (1 / 2 : ℝ) ^ A.card = 1 / 2 ^ A.card by simp]
  field_simp
  exact_mod_cast (show 2 ^ (n.choose 2 - A.card) * 2 ^ A.card = 2 ^ n.choose 2 by
    rw [← pow_add, Nat.sub_add_cancel hA])

/-- Event that every edge in `A` is present. -/
def Contains (A : Finset (Edge n)) (G : SimpleGraph (Fin n)) : Prop :=
  A ⊆ edges G

theorem contains_iff_prescribed_self {n : ℕ} {A : Finset (Edge n)}
    {G : SimpleGraph (Fin n)} : Contains A G ↔ Prescribed A A G := by
  rw [Contains, Prescribed, Erdos565.RandomGraph.restrict]
  exact Finset.inter_eq_right.symm

theorem card_contains (A : Finset (Edge n)) :
    eventCard n (Contains A) = 2 ^ (n.choose 2 - A.card) := by
  rw [show Contains A = Prescribed A A from funext fun G ↦ propext contains_iff_prescribed_self]
  exact card_prescribed (by rfl)

theorem probability_contains (A : Finset (Edge n)) :
    probability n (Contains A) = (1 / 2 : ℝ) ^ A.card := by
  rw [show Contains A = Prescribed A A from funext fun G ↦ propext contains_iff_prescribed_self]
  exact probability_prescribed (by rfl)

/-- Event that every edge in `A` is absent. -/
def Avoids (A : Finset (Edge n)) (G : SimpleGraph (Fin n)) : Prop :=
  Disjoint A (edges G)

theorem avoids_iff_prescribed_empty {n : ℕ} {A : Finset (Edge n)}
    {G : SimpleGraph (Fin n)} : Avoids A G ↔ Prescribed A ∅ G := by
  simp [Avoids, Prescribed, Erdos565.RandomGraph.restrict,
    Finset.disjoint_iff_inter_eq_empty, Finset.inter_comm]

theorem card_avoids (A : Finset (Edge n)) :
    eventCard n (Avoids A) = 2 ^ (n.choose 2 - A.card) := by
  rw [show Avoids A = Prescribed A ∅ from funext fun G ↦ propext avoids_iff_prescribed_empty]
  exact card_prescribed (by simp)

theorem probability_avoids (A : Finset (Edge n)) :
    probability n (Avoids A) = (1 / 2 : ℝ) ^ A.card := by
  rw [show Avoids A = Prescribed A ∅ from funext fun G ↦ propext avoids_iff_prescribed_empty]
  exact probability_prescribed (by simp)

end RandomGraph
end Erdos807
