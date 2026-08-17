import ErdosProblems.Erdos182.Probability
import ErdosProblems.Erdos182.Roof

/-!
# Almost-regular extraction for Erdős Problem 182

This file formalizes the alteration step of Janzer--Sudakov, Lemma 3.7,
and packages its deterministic consequence used in Lemma 3.5.  Bipartite
graphs are represented by `BipartiteGraph`, so all statements are about the
actual two parts and do not acquire artificial isolated ambient vertices.
-/

namespace Erdos182

open Finset
open scoped BigOperators NNReal

noncomputable section

namespace BipartiteGraph

variable {A B : Type*} [Fintype A] [Fintype B]

/-- The degree function on the disjoint union of the two vertex classes. -/
def vertexDegree (G : BipartiteGraph A B) : A ⊕ B → ℕ
  | Sum.inl a => G.leftDegree a
  | Sum.inr b => G.rightDegree b

/-- The number of non-isolated vertices.  This is the denominator used for
the average degree of an extracted graph. -/
def supportCard (G : BipartiteGraph A B) : ℕ :=
  (Finset.univ.filter fun a => 0 < G.leftDegree a).card +
    (Finset.univ.filter fun b => 0 < G.rightDegree b).card

/-- Support-relative `K`-almost-regularity.  The formulation compares every
degree with every positive degree and hence ignores precisely the isolated
vertices. -/
def IsAlmostRegular (G : BipartiteGraph A B) (K : ℕ) : Prop :=
  0 < G.edgeCount ∧
    ∀ u v : A ⊕ B, 0 < G.vertexDegree v →
      G.vertexDegree u ≤ K * G.vertexDegree v

/-- Delete all edges at left vertices whose current degree is at least `M`.
The strict inequality is useful because it gives the integral bound
`degree ≤ M - 1`, while the weaker bound `degree ≤ M` is normally used
downstream. -/
def deleteHeavyLeft (G : BipartiteGraph A B) (M : ℕ) :
    BipartiteGraph A B :=
  ⟨fun a b => G.Adj a b ∧ G.leftDegree a < M⟩

@[simp]
theorem deleteHeavyLeft_adj (G : BipartiteGraph A B) (M : ℕ)
    (a : A) (b : B) :
    (G.deleteHeavyLeft M).Adj a b ↔
      G.Adj a b ∧ G.leftDegree a < M :=
  Iff.rfl

theorem deleteHeavyLeft_le (G : BipartiteGraph A B) (M : ℕ) :
    G.deleteHeavyLeft M ≤ G := by
  intro a b hab
  exact hab.1

theorem restrictRight_supportedOn {G : BipartiteGraph A B}
    {A₀ : Finset A} {B₀ S : Finset B} (hG : G.SupportedOn A₀ B₀)
    (_hS : S ⊆ B₀) : (G.restrictRight S).SupportedOn A₀ S := by
  intro a b hab
  exact ⟨(hG hab.1).1, hab.2⟩

theorem deleteHeavyLeft_supportedOn {G : BipartiteGraph A B}
    {A₀ : Finset A} {B₀ : Finset B} {M : ℕ}
    (hG : G.SupportedOn A₀ B₀) :
    (G.deleteHeavyLeft M).SupportedOn A₀ B₀ := by
  intro a b hab
  exact hG hab.1

/-- Number of neighbors of `a` lying in the displayed right set. -/
noncomputable def leftDegreeOn (G : BipartiteGraph A B) (S : Finset B) (a : A) : ℕ :=
  by classical exact ((G.rightNeighbors a).filter fun b => b ∈ S).card

theorem leftDegree_restrictRight (G : BipartiteGraph A B)
    (S : Finset B) (a : A) :
    (G.restrictRight S).leftDegree a = G.leftDegreeOn S a := by
  classical
  simp only [leftDegree, rightNeighbors, restrictRight_adj, leftDegreeOn]
  congr 1
  ext b
  simp [and_comm]

theorem leftDegree_deleteHeavyLeft (G : BipartiteGraph A B)
    (M : ℕ) (a : A) :
    (G.deleteHeavyLeft M).leftDegree a =
      if G.leftDegree a < M then G.leftDegree a else 0 := by
  classical
  by_cases h : G.leftDegree a < M
  · have h' : (Finset.univ.filter fun b => G.Adj a b).card < M := by
      simpa [leftDegree, rightNeighbors] using h
    simp only [leftDegree, rightNeighbors, deleteHeavyLeft_adj]
    simp [h']
  · have h' : ¬ (Finset.univ.filter fun b => G.Adj a b).card < M := by
      simpa [leftDegree, rightNeighbors] using h
    simp only [leftDegree, rightNeighbors, deleteHeavyLeft_adj]
    simp [h']

theorem leftDegree_deleteHeavyLeft_le (G : BipartiteGraph A B)
    (M : ℕ) (a : A) :
    (G.deleteHeavyLeft M).leftDegree a ≤ M := by
  rw [leftDegree_deleteHeavyLeft]
  split_ifs with h
  · omega
  · exact Nat.zero_le _

theorem rightDegree_restrictRight_le (G : BipartiteGraph A B)
    (S : Finset B) (b : B) :
    (G.restrictRight S).rightDegree b ≤ G.rightDegree b := by
  classical
  apply Finset.card_le_card
  intro a ha
  apply (mem_leftNeighbors G a b).mpr
  exact ((mem_leftNeighbors (G.restrictRight S) a b).mp ha).1

theorem rightDegree_deleteHeavyLeft_le (G : BipartiteGraph A B)
    (M : ℕ) (b : B) :
    (G.deleteHeavyLeft M).rightDegree b ≤ G.rightDegree b := by
  classical
  apply Finset.card_le_card
  intro a ha
  apply (mem_leftNeighbors G a b).mpr
  exact ((mem_leftNeighbors (G.deleteHeavyLeft M) a b).mp ha).1

theorem supportCard_le_card_add_card_of_supportedOn
    {G : BipartiteGraph A B} {A₀ : Finset A} {B₀ : Finset B}
    (hG : G.SupportedOn A₀ B₀) :
    G.supportCard ≤ A₀.card + B₀.card := by
  classical
  unfold supportCard
  gcongr
  · intro a ha
    simp only [mem_filter, mem_univ, true_and] at ha
    by_contra ha₀
    have hzero : G.leftDegree a = 0 := by
      rw [leftDegree, Finset.card_eq_zero]
      apply Finset.not_nonempty_iff_eq_empty.mp
      rintro ⟨b, hb⟩
      exact ha₀ (hG ((mem_rightNeighbors G a b).mp hb)).1
    omega
  · intro b hb
    simp only [mem_filter, mem_univ, true_and] at hb
    by_contra hb₀
    have hzero : G.rightDegree b = 0 := by
      rw [rightDegree, Finset.card_eq_zero]
      apply Finset.not_nonempty_iff_eq_empty.mp
      rintro ⟨a, ha⟩
      exact hb₀ (hG ((mem_leftNeighbors G a b).mp ha)).2
    omega

/-- The natural-number form of the assertion that the average degree is at
least `d/2`: `2e/v ≥ d/2` is equivalent to `d v ≤ 4e`. -/
def HasAverageDegreeAtLeastHalf (G : BipartiteGraph A B) (d : ℕ) : Prop :=
  d * G.supportCard ≤ 4 * G.edgeCount

section Sampling

variable (G : BipartiteGraph A B) (B₀ : Finset B)

/-- Forget the membership certificates on a finite set of vertices in `B₀`. -/
def selectedRightVertices (S : Finset ↑B₀) : Finset B :=
  S.map ⟨Subtype.val, Subtype.val_injective⟩

/-- Degree at `a` after retaining precisely the right vertices in `S`. -/
def sampledLeftDegree (a : A) (S : Finset ↑B₀) : ℕ :=
  by
    classical
    exact (S.filter fun b => G.Adj a b.1).card

/-- Number of edges left after right-vertex sampling and deletion of every
left star whose sampled degree reaches `M`. -/
def alteredEdgeCount (M : ℕ) (S : Finset ↑B₀) : ℕ :=
  ∑ a : A, if sampledLeftDegree G B₀ a S < M
    then sampledLeftDegree G B₀ a S else 0

/-- Edges removed by the alteration. -/
def removedEdgeCount (M : ℕ) (S : Finset ↑B₀) : ℕ :=
  ∑ a : A, if M ≤ sampledLeftDegree G B₀ a S
    then sampledLeftDegree G B₀ a S else 0

/-- Number of sampled edges before the alteration. -/
def sampledEdgeCount (S : Finset ↑B₀) : ℕ :=
  ∑ a : A, sampledLeftDegree G B₀ a S

theorem sampledEdgeCount_eq_altered_add_removed (M : ℕ) (S : Finset ↑B₀) :
    sampledEdgeCount G B₀ S =
      alteredEdgeCount G B₀ M S + removedEdgeCount G B₀ M S := by
  classical
  unfold sampledEdgeCount alteredEdgeCount removedEdgeCount
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro a _
  by_cases h : sampledLeftDegree G B₀ a S < M
  · simp [h, Nat.not_le_of_gt h]
  · simp [h, Nat.le_of_not_gt h]

/-- The actual graph produced by the alteration. -/
def alteredGraph (M : ℕ) (S : Finset ↑B₀) : BipartiteGraph A B :=
  (G.restrictRight (selectedRightVertices B₀ S)).deleteHeavyLeft M

@[simp]
theorem mem_selectedRightVertices (S : Finset ↑B₀) (b : B) :
    b ∈ selectedRightVertices B₀ S ↔ ∃ hb : b ∈ B₀, (⟨b, hb⟩ : ↑B₀) ∈ S := by
  classical
  simp [selectedRightVertices]

theorem selectedRightVertices_subset (S : Finset ↑B₀) :
    selectedRightVertices B₀ S ⊆ B₀ := by
  classical
  intro b hb
  obtain ⟨hb₀, _⟩ := (mem_selectedRightVertices B₀ S b).mp hb
  exact hb₀

theorem card_selectedRightVertices (S : Finset ↑B₀) :
    (selectedRightVertices B₀ S).card = S.card := by
  classical
  exact Finset.card_map _

theorem sampledLeftDegree_eq_restrictRight_leftDegree
    (a : A) (S : Finset ↑B₀) :
    sampledLeftDegree G B₀ a S =
      (G.restrictRight (selectedRightVertices B₀ S)).leftDegree a := by
  classical
  rw [leftDegree_restrictRight]
  unfold leftDegreeOn
  unfold sampledLeftDegree
  rw [← Finset.card_map ⟨Subtype.val, Subtype.val_injective⟩]
  congr 1
  ext b
  simp [selectedRightVertices, mem_rightNeighbors, and_comm]

theorem edgeCount_alteredGraph (M : ℕ) (S : Finset ↑B₀) :
    (G.alteredGraph B₀ M S).edgeCount = alteredEdgeCount G B₀ M S := by
  classical
  rw [edgeCount_eq_sum_leftDegree]
  apply Finset.sum_congr rfl
  intro a _
  rw [alteredGraph, leftDegree_deleteHeavyLeft,
    ← sampledLeftDegree_eq_restrictRight_leftDegree]

theorem alteredGraph_le (M : ℕ) (S : Finset ↑B₀) :
    G.alteredGraph B₀ M S ≤ G := by
  intro a b hab
  exact hab.1.1

theorem alteredGraph_supportedOn {A₀ : Finset A}
    (hG : G.SupportedOn A₀ B₀) (M : ℕ) (S : Finset ↑B₀) :
    (G.alteredGraph B₀ M S).SupportedOn A₀ (selectedRightVertices B₀ S) := by
  apply deleteHeavyLeft_supportedOn
  exact restrictRight_supportedOn hG (selectedRightVertices_subset B₀ S)

theorem alteredGraph_leftDegree_le (M : ℕ) (S : Finset ↑B₀) (a : A) :
    (G.alteredGraph B₀ M S).leftDegree a ≤ M :=
  leftDegree_deleteHeavyLeft_le _ _ _

theorem alteredGraph_rightDegree_le (M : ℕ) (S : Finset ↑B₀) (b : B) :
    (G.alteredGraph B₀ M S).rightDegree b ≤ G.rightDegree b :=
  (rightDegree_deleteHeavyLeft_le _ _ _).trans
    (rightDegree_restrictRight_le _ _ _)

theorem sampledLeftDegree_univ {A₀ : Finset A}
    (hG : G.SupportedOn A₀ B₀) (a : A) :
    sampledLeftDegree G B₀ a Finset.univ = G.leftDegree a := by
  classical
  unfold sampledLeftDegree
  rw [← Finset.card_map ⟨Subtype.val, Subtype.val_injective⟩]
  congr 1
  ext b
  simp only [Finset.mem_map, Finset.mem_filter, Finset.mem_univ, true_and,
    mem_rightNeighbors]
  constructor
  · rintro ⟨c, hc, rfl⟩
    exact hc
  · intro hab
    exact ⟨⟨b, (hG hab).2⟩, hab, rfl⟩

/-- The neighbors of `a`, regarded as vertices of the active right part. -/
def activeRightNeighbors (a : A) : Finset ↑B₀ := by
  classical
  exact Finset.univ.filter fun b => G.Adj a b.1

theorem card_activeRightNeighbors {A₀ : Finset A}
    (hG : G.SupportedOn A₀ B₀) (a : A) :
    (activeRightNeighbors G B₀ a).card = G.leftDegree a := by
  classical
  simpa [activeRightNeighbors, sampledLeftDegree] using
    sampledLeftDegree_univ G B₀ hG a

theorem bernoulli_expect_sampledLeftDegree {A₀ : Finset A}
    (hG : G.SupportedOn A₀ B₀) (p : ℝ≥0) (hp : p ≤ 1) (a : A) :
    weightedExpectation (bernoulliWeight p)
        (fun S : Finset ↑B₀ => (sampledLeftDegree G B₀ a S : ℝ≥0)) =
      p * G.leftDegree a := by
  classical
  have hfun : (fun S : Finset ↑B₀ => (sampledLeftDegree G B₀ a S : ℝ≥0)) =
      fun S => (((activeRightNeighbors G B₀ a).filter fun b => b ∈ S).card : ℝ≥0) := by
    funext S
    norm_cast
    unfold sampledLeftDegree activeRightNeighbors
    congr 1
    ext b
    simp [and_comm]
  rw [hfun]
  rw [bernoulli_expect_inter_card p hp, card_activeRightNeighbors G B₀ hG]

theorem bernoulli_expect_sampledLeftDegree_sq {A₀ : Finset A}
    (hG : G.SupportedOn A₀ B₀) (p : ℝ≥0) (hp : p ≤ 1) (a : A) :
    weightedExpectation (bernoulliWeight p)
        (fun S : Finset ↑B₀ => (sampledLeftDegree G B₀ a S : ℝ≥0) ^ 2) =
      p * G.leftDegree a + p ^ 2 * G.leftDegree a * (G.leftDegree a - 1) := by
  classical
  have hfun : (fun S : Finset ↑B₀ => (sampledLeftDegree G B₀ a S : ℝ≥0) ^ 2) =
      fun S => (((activeRightNeighbors G B₀ a).filter fun b => b ∈ S).card : ℝ≥0) ^ 2 := by
    funext S
    congr 1
    norm_cast
    unfold sampledLeftDegree activeRightNeighbors
    congr 1
    ext b
    simp [and_comm]
  rw [hfun]
  rw [bernoulli_expect_inter_card_sq p hp, card_activeRightNeighbors G B₀ hG]

theorem bernoulli_expect_sampledEdgeCount {A₀ : Finset A}
    (hG : G.SupportedOn A₀ B₀) (p : ℝ≥0) (hp : p ≤ 1) :
    weightedExpectation (bernoulliWeight p)
        (fun S : Finset ↑B₀ => (sampledEdgeCount G B₀ S : ℝ≥0)) =
      p * G.edgeCount := by
  classical
  simp_rw [sampledEdgeCount, Nat.cast_sum]
  calc
    weightedExpectation (bernoulliWeight p)
        (fun S : Finset ↑B₀ => ∑ a : A,
          (sampledLeftDegree G B₀ a S : ℝ≥0)) =
        ∑ a : A, weightedExpectation (bernoulliWeight p)
          (fun S : Finset ↑B₀ => (sampledLeftDegree G B₀ a S : ℝ≥0)) := by
      unfold weightedExpectation
      simp_rw [Finset.mul_sum]
      exact Finset.sum_comm
    _ = ∑ a : A, p * G.leftDegree a := by
      apply Finset.sum_congr rfl
      intro a _
      exact bernoulli_expect_sampledLeftDegree G B₀ hG p hp a
    _ = p * G.edgeCount := by
      rw [← Finset.mul_sum]
      congr 1
      norm_cast
      exact (edgeCount_eq_sum_leftDegree G).symm

theorem threshold_mul_expect_removed_le_expect_sq_sum
    (p : ℝ≥0) (M : ℕ) :
    (M : ℝ≥0) * weightedExpectation (bernoulliWeight p)
        (fun S : Finset ↑B₀ => (removedEdgeCount G B₀ M S : ℝ≥0)) ≤
      ∑ a : A, weightedExpectation (bernoulliWeight p)
        (fun S : Finset ↑B₀ => ((sampledLeftDegree G B₀ a S : ℝ≥0) ^ 2)) := by
  classical
  unfold removedEdgeCount weightedExpectation
  simp_rw [Nat.cast_sum, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_le_sum
  intro a _
  apply Finset.sum_le_sum
  intro S _
  by_cases h : M ≤ sampledLeftDegree G B₀ a S
  · simp only [h, if_true]
    have hMx : (M : ℝ≥0) * sampledLeftDegree G B₀ a S ≤
        (sampledLeftDegree G B₀ a S : ℝ≥0) ^ 2 := by
      norm_cast
      simpa [pow_two] using Nat.mul_le_mul_right (sampledLeftDegree G B₀ a S) h
    calc
      (M : ℝ≥0) * (bernoulliWeight p S * sampledLeftDegree G B₀ a S) =
          bernoulliWeight p S * ((M : ℝ≥0) * sampledLeftDegree G B₀ a S) := by ring
      _ ≤ bernoulliWeight p S * ((sampledLeftDegree G B₀ a S : ℝ≥0) ^ 2) := by
        gcongr
  · simp [h]

end Sampling

end BipartiteGraph

end

end Erdos182
