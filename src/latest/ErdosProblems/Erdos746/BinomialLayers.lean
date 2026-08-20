import ErdosProblems.Erdos746.Model
import ErdosProblems.Erdos746.Monotonicity
import ErdosProblems.Erdos746.BinomialBounds

/-!
# Decomposing the binomial random graph into uniform edge-count layers

The finite Bernoulli subset model is the edge-set presentation of the
binomial random graph.  This file proves, by an exact finite regrouping by
cardinality, that every event probability is a binomially weighted average
of its uniform fixed-cardinality probabilities.  For an increasing event,
the identity gives the standard transfer from `G(n,p)` to `G(n,m)`.
-/

open scoped BigOperators

namespace Erdos746

noncomputable section

attribute [local instance] Classical.propDecidable

/-- Bernoulli weight of a subset of `U`. -/
def bernoulliSubsetWeight {α : Type*} (U : Finset α) (p : ℝ)
    (A : Finset α) : ℝ :=
  p ^ A.card * (1 - p) ^ (U.card - A.card)

/-- The exact finite Bernoulli mass of an event on subsets of `U`. -/
def bernoulliEventMass {α : Type*} [DecidableEq α] (U : Finset α)
    (p : ℝ) (P : Finset α → Prop) : ℝ := by
  classical
  exact ∑ A ∈ U.powerset.filter P, bernoulliSubsetWeight U p A

/-- Exact decomposition of a finite Bernoulli subset event into its uniform
fixed-cardinality layers. -/
theorem bernoulliEventMass_eq_sum_binomialTerm_mul_layerProbability
    {α : Type*} [DecidableEq α] (U : Finset α) (p : ℝ)
    (P : Finset α → Prop) :
    bernoulliEventMass U p P =
      ∑ j ∈ Finset.range (U.card + 1),
        binomialTerm U.card p j * layerProbability U P j := by
  classical
  unfold bernoulliEventMass
  rw [Finset.sum_filter, Finset.sum_powerset]
  apply Finset.sum_congr rfl
  intro j hj
  have hjle : j ≤ U.card := by
    simpa only [Finset.mem_range] using Nat.le_of_lt_succ (Finset.mem_range.mp hj)
  have hchoose : (U.card.choose j : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.choose_pos hjle).ne'
  rw [← Finset.sum_filter]
  have hconst :
      (∑ A ∈ (U.powersetCard j).filter P,
          bernoulliSubsetWeight U p A) =
        (((U.powersetCard j).filter P).card : ℝ) *
          (p ^ j * (1 - p) ^ (U.card - j)) := by
    calc
      (∑ A ∈ (U.powersetCard j).filter P,
          bernoulliSubsetWeight U p A) =
          ∑ _A ∈ (U.powersetCard j).filter P,
            (p ^ j * (1 - p) ^ (U.card - j)) := by
        apply Finset.sum_congr rfl
        intro A hA
        rw [bernoulliSubsetWeight]
        have hcard : A.card = j :=
          (Finset.mem_powersetCard.mp (Finset.mem_filter.mp hA).1).2
        rw [hcard]
      _ = (((U.powersetCard j).filter P).card : ℝ) *
          (p ^ j * (1 - p) ^ (U.card - j)) := by simp
  rw [hconst]
  unfold binomialTerm layerProbability LocalLYM.goodSets
  field_simp

/-- Bernoulli probability of a graph property, in the finite edge-subset
presentation of `SimpleGraph.binomialRandom`. -/
def binomialGraphPropertyProbability (n : ℕ) (p : ℝ)
    (Q : SimpleGraph (Fin n) → Prop) : ℝ :=
  bernoulliEventMass (Finset.univ : Finset (Edge n)) p
    (fun A ↦ Q (graphOfEdges A))

/-- The graph-property specialization of the exact layer decomposition. -/
theorem binomialGraphPropertyProbability_eq_sum (n : ℕ) (p : ℝ)
    (Q : SimpleGraph (Fin n) → Prop) :
    binomialGraphPropertyProbability n p Q =
      ∑ j ∈ Finset.range (edgeCount n + 1),
        binomialTerm (edgeCount n) p j * graphPropertyProbability n j Q := by
  rw [binomialGraphPropertyProbability,
    bernoulliEventMass_eq_sum_binomialTerm_mul_layerProbability]
  simp only [Finset.card_univ, card_edge]
  apply Finset.sum_congr rfl
  intro j _hj
  rw [graphPropertyProbability_eq_layerProbability]

/-- On a nonempty Boolean-lattice layer, an event and its complement have
probabilities adding to one. -/
theorem layerProbability_add_compl {α : Type*} [DecidableEq α]
    (U : Finset α) (P : Finset α → Prop) {j : ℕ} (hj : j ≤ U.card) :
    layerProbability U P j + layerProbability U (fun A ↦ ¬ P A) j = 1 := by
  classical
  have hchoose : (U.card.choose j : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.choose_pos hj).ne'
  unfold layerProbability LocalLYM.goodSets
  rw [← add_div, ← Nat.cast_add,
    Finset.card_filter_add_card_filter_not, Finset.card_powersetCard]
  exact div_self hchoose

/-- Failure on a valid fixed layer is one minus success. -/
theorem graphPropertyFailure_eq_one_sub {n m : ℕ}
    (Q : SimpleGraph (Fin n) → Prop) (hm : m ≤ edgeCount n) :
    graphPropertyProbability n m (fun G ↦ ¬ Q G) =
      1 - graphPropertyProbability n m Q := by
  rw [graphPropertyProbability_eq_layerProbability,
    graphPropertyProbability_eq_layerProbability]
  have h := layerProbability_add_compl
    (Finset.univ : Finset (Edge n)) (fun A ↦ Q (graphOfEdges A))
    (j := m) (by
      change m ≤ Fintype.card (Edge n)
      rw [card_edge]
      exact hm)
  linarith

/-- Failure probability of a graph property in the binomial edge model. -/
def binomialGraphPropertyFailure (n : ℕ) (p : ℝ)
    (Q : SimpleGraph (Fin n) → Prop) : ℝ :=
  binomialGraphPropertyProbability n p (fun G ↦ ¬ Q G)

/-- Failure probability on the uniform `m`-edge layer. -/
def graphPropertyFailure (n m : ℕ)
    (Q : SimpleGraph (Fin n) → Prop) : ℝ :=
  graphPropertyProbability n m (fun G ↦ ¬ Q G)

/-- The binomial failure probability is the weighted average of the uniform
layer failure probabilities. -/
theorem binomialGraphPropertyFailure_eq_sum (n : ℕ) (p : ℝ)
    (Q : SimpleGraph (Fin n) → Prop) :
    binomialGraphPropertyFailure n p Q =
      ∑ j ∈ Finset.range (edgeCount n + 1),
        binomialTerm (edgeCount n) p j * graphPropertyFailure n j Q := by
  simpa only [binomialGraphPropertyFailure, graphPropertyFailure] using
    binomialGraphPropertyProbability_eq_sum n p (fun G ↦ ¬ Q G)

/-- Every Boolean-lattice layer probability is nonnegative. -/
theorem layerProbability_nonneg {α : Type*} [DecidableEq α]
    (U : Finset α) (P : Finset α → Prop) (j : ℕ) :
    0 ≤ layerProbability U P j := by
  unfold layerProbability
  positivity

/-- Failures of an increasing event become no more likely on a higher valid
layer. -/
theorem layerProbability_compl_antitone {α : Type*} [DecidableEq α]
    (U : Finset α) (P : Finset α → Prop)
    (hP : ∀ ⦃A B : Finset α⦄, A ⊆ B → P A → P B)
    {j m : ℕ} (hjm : j ≤ m) (hm : m ≤ U.card) :
    layerProbability U (fun A ↦ ¬ P A) m ≤
      layerProbability U (fun A ↦ ¬ P A) j := by
  have hj : j ≤ U.card := hjm.trans hm
  have hmono := layerProbability_mono U P hP hjm hm
  have hjcompl := layerProbability_add_compl U P hj
  have hmcompl := layerProbability_add_compl U P hm
  linarith

/-- The lower and upper binomial tails at consecutive cutoffs partition the
whole probability space. -/
theorem binomialLowerTail_add_upperTail (N m : ℕ) (p : ℝ) (hm : m ≤ N) :
    binomialLowerTail N (m + 1) p +
      binomialUpperTail N (m + 1) p = 1 := by
  have hfilter :
      (Finset.range (N + 1)).filter (m + 1 ≤ ·) =
        Finset.Ico (m + 1) (N + 1) := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico]
    omega
  unfold binomialLowerTail binomialUpperTail
  rw [hfilter,
    Finset.sum_range_add_sum_Ico (fun j ↦ binomialTerm N p j)
      (Nat.succ_le_succ hm),
    sum_binomialTerm]

/-- The basic transfer inequality.  For an increasing event, all failure
layers at or below `m` have density at least the failure density at `m`.
Consequently the binomial failure mass dominates that density times
`P(X ≤ m)`. -/
theorem layerFailure_mul_lowerTail_le_bernoulliFailure
    {α : Type*} [DecidableEq α] (U : Finset α) (P : Finset α → Prop)
    (hP : ∀ ⦃A B : Finset α⦄, A ⊆ B → P A → P B)
    (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) {m : ℕ} (hm : m ≤ U.card) :
    layerProbability U (fun A ↦ ¬ P A) m *
        binomialLowerTail U.card (m + 1) p ≤
      bernoulliEventMass U p (fun A ↦ ¬ P A) := by
  calc
    layerProbability U (fun A ↦ ¬ P A) m *
          binomialLowerTail U.card (m + 1) p =
        ∑ j ∈ Finset.range (m + 1),
          binomialTerm U.card p j *
            layerProbability U (fun A ↦ ¬ P A) m := by
      unfold binomialLowerTail
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _hj
      ring
    _ ≤ ∑ j ∈ Finset.range (m + 1),
          binomialTerm U.card p j *
            layerProbability U (fun A ↦ ¬ P A) j := by
      apply Finset.sum_le_sum
      intro j hj
      have hjlt : j < m + 1 := Finset.mem_range.mp hj
      have hjm : j ≤ m := by omega
      exact mul_le_mul_of_nonneg_left
        (layerProbability_compl_antitone U P hP hjm hm)
        (binomialTerm_nonneg hp0 hp1)
    _ ≤ ∑ j ∈ Finset.range (U.card + 1),
          binomialTerm U.card p j *
            layerProbability U (fun A ↦ ¬ P A) j := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
        (Finset.range_mono (Nat.succ_le_succ hm))
      intro j _hj _hnot
      exact mul_nonneg (binomialTerm_nonneg hp0 hp1)
        (layerProbability_nonneg U (fun A ↦ ¬ P A) j)
    _ = bernoulliEventMass U p (fun A ↦ ¬ P A) :=
      (bernoulliEventMass_eq_sum_binomialTerm_mul_layerProbability
        U p (fun A ↦ ¬ P A)).symm

/-- Graph-property form of the basic transfer inequality. -/
theorem graphPropertyFailure_mul_lowerTail_le_binomialFailure
    {n m : ℕ} (Q : SimpleGraph (Fin n) → Prop)
    (hQ : ∀ ⦃G H : SimpleGraph (Fin n)⦄, G ≤ H → Q G → Q H)
    (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hm : m ≤ edgeCount n) :
    graphPropertyFailure n m Q *
        binomialLowerTail (edgeCount n) (m + 1) p ≤
      binomialGraphPropertyFailure n p Q := by
  have h := layerFailure_mul_lowerTail_le_bernoulliFailure
    (Finset.univ : Finset (Edge n))
    (fun A ↦ Q (graphOfEdges A))
    (fun _A _B hAB hA ↦ hQ (graphOfEdges_mono hAB) hA)
    p hp0 hp1 (m := m) (by
      change m ≤ Fintype.card (Edge n)
      rw [card_edge]
      exact hm)
  simpa only [graphPropertyFailure, binomialGraphPropertyFailure,
    binomialGraphPropertyProbability, graphPropertyProbability_eq_layerProbability,
    Finset.card_univ, card_edge] using h

/-- Transfer in quotient form when the binomial lower-tail probability is
positive. -/
theorem graphPropertyFailure_le_binomialFailure_div_lowerTail
    {n m : ℕ} (Q : SimpleGraph (Fin n) → Prop)
    (hQ : ∀ ⦃G H : SimpleGraph (Fin n)⦄, G ≤ H → Q G → Q H)
    (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hm : m ≤ edgeCount n)
    (hlower : 0 < binomialLowerTail (edgeCount n) (m + 1) p) :
    graphPropertyFailure n m Q ≤
      binomialGraphPropertyFailure n p Q /
        binomialLowerTail (edgeCount n) (m + 1) p := by
  rw [le_div_iff₀ hlower]
  exact graphPropertyFailure_mul_lowerTail_le_binomialFailure
    Q hQ p hp0 hp1 hm

/-- Convenient transfer when the probability of having more than `m` edges
is at most one half. -/
theorem graphPropertyFailure_le_two_mul_binomialFailure
    {n m : ℕ} (Q : SimpleGraph (Fin n) → Prop)
    (hQ : ∀ ⦃G H : SimpleGraph (Fin n)⦄, G ≤ H → Q G → Q H)
    (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hm : m ≤ edgeCount n)
    (htail : binomialUpperTail (edgeCount n) (m + 1) p ≤ (1 : ℝ) / 2) :
    graphPropertyFailure n m Q ≤
      2 * binomialGraphPropertyFailure n p Q := by
  have hsplit := binomialLowerTail_add_upperTail
    (edgeCount n) m p hm
  have hlower : (1 : ℝ) / 2 ≤
      binomialLowerTail (edgeCount n) (m + 1) p := by
    linarith
  have hmul := graphPropertyFailure_mul_lowerTail_le_binomialFailure
    Q hQ p hp0 hp1 hm
  have hfail0 : 0 ≤ graphPropertyFailure n m Q := by
    exact uniformProbability_nonneg _
  nlinarith

end

end Erdos746
