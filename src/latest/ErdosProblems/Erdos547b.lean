/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Combinatorics.SimpleGraph.Copy
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Tactic
import ErdosProblems.Erdos547b.SourceZhaoRamseyHost

/-!
# Erdős Problem 547

The unqualified database sentence is not literally true at order one: the
Ramsey host prescribed by `2 * n - 2` is empty, whereas the unique one-vertex
tree cannot embed in an empty graph.  The corrected assertion, with `2 ≤ n`,
is the still-open all-order tree Ramsey conjecture.  Zhao's published theorem
proves its sufficiently-large form.

This file proves Zhao's unconditional sufficiently-large Ramsey conclusion
in `eventually_erdos_547`, using the full checked source-host development.
It also records the literal statement and its order-one counterexample,
and the exact reduction from the corresponding Erdős--Sós assertion.
The corrected all-order conjecture is not claimed.
-/

open scoped SimpleGraph

noncomputable section

namespace Erdos547b

open Finset SimpleGraph

/-- Every red/blue coloring of the complete graph on `N` vertices has a
monochromatic copy of `T`; the red graph is `G` and the blue graph is `Gᶜ`. -/
def TreeRamseyProperty {n : ℕ} (T : SimpleGraph (Fin n)) (N : ℕ) : Prop :=
  by
    classical
    exact ∀ G : SimpleGraph (Fin N), T ⊑ G ∨ T ⊑ Gᶜ

/-- The order-`n` instance of the displayed bound in Problem 547. -/
def Erdos547At (n : ℕ) : Prop :=
  ∀ T : SimpleGraph (Fin n), T.IsTree →
    TreeRamseyProperty T (2 * n - 2)

/-- The literal, unqualified assertion printed in the problem database. -/
def LiteralErdos547 : Prop := ∀ n : ℕ, Erdos547At n

/-- The standard nontrivial-order correction.  This is open in full
generality; no theorem below claims this proposition. -/
def CorrectedErdos547 : Prop := ∀ n : ℕ, 2 ≤ n → Erdos547At n

/-- The unconditional conclusion established by Zhao is an eventual one. -/
def EventuallyErdos547 : Prop :=
  ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n → Erdos547At n

/-- The one-vertex tree does not embed in any graph on no vertices. -/
theorem oneVertexTree_not_isContained_finZero
    (G : SimpleGraph (Fin 0)) :
    ¬(⊥ : SimpleGraph (Fin 1)) ⊑ G := by
  intro h
  have hcard := (bot_isContained_iff_card_le (B := G)).mp h
  simp at hcard

/-- Consequently the literal version of Problem 547 is false at `n = 1`. -/
theorem not_literalErdos547 : ¬LiteralErdos547 := by
  intro h
  have htree : (⊥ : SimpleGraph (Fin 1)).IsTree :=
    SimpleGraph.IsTree.of_subsingleton
  have hramsey := h 1 (⊥ : SimpleGraph (Fin 1)) htree
    (⊥ : SimpleGraph (Fin 0))
  rcases hramsey with hred | hblue
  · exact oneVertexTree_not_isContained_finZero (⊥ : SimpleGraph (Fin 0)) hred
  · exact oneVertexTree_not_isContained_finZero
      ((⊥ : SimpleGraph (Fin 0))ᶜ) hblue

/-! ## The honest Erdős--Sós reduction -/

/-- The exact Erdős--Sós embedding statement needed for a fixed `n`-vertex
tree.  Its strict inequality is the usual average-degree formulation. -/
def ErdosSosFor {n : ℕ} (T : SimpleGraph (Fin n)) : Prop :=
  ∀ {V : Type} [Fintype V] (H : SimpleGraph V) [DecidableRel H.Adj],
    (n - 2) * Fintype.card V < 2 * H.edgeFinset.card → T ⊑ H

private theorem card_edges_add_card_edges_compl
    {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] :
    G.edgeFinset.card + Gᶜ.edgeFinset.card = (Fintype.card V).choose 2 := by
  classical
  have hdisjoint : Disjoint G.edgeFinset Gᶜ.edgeFinset := by
    rw [SimpleGraph.disjoint_edgeFinset]
    exact disjoint_compl_right
  have hunion : G.edgeFinset ∪ Gᶜ.edgeFinset =
      (⊤ : SimpleGraph V).edgeFinset := by
    ext e
    simp only [Finset.mem_union, SimpleGraph.mem_edgeFinset]
    induction e using Sym2.inductionOn with
    | hf x y =>
        simp only [SimpleGraph.mem_edgeSet, SimpleGraph.compl_adj,
          SimpleGraph.top_adj]
        constructor
        · rintro (hxy | ⟨hne, _⟩)
          · exact G.ne_of_adj hxy
          · exact hne
        · intro hne
          by_cases hxy : G.Adj x y
          · exact Or.inl hxy
          · exact Or.inr ⟨hne, hxy⟩
  calc
    G.edgeFinset.card + Gᶜ.edgeFinset.card =
        (G.edgeFinset ∪ Gᶜ.edgeFinset).card :=
      (Finset.card_union_of_disjoint hdisjoint).symm
    _ = ((⊤ : SimpleGraph V).edgeFinset).card := congrArg Finset.card hunion
    _ = (Fintype.card V).choose 2 :=
      SimpleGraph.card_edgeFinset_top_eq_card_choose_two

private theorem twice_choose_two (m : ℕ) :
    2 * m.choose 2 = m * (m - 1) := by
  rw [Nat.choose_two_right]
  have heven : Even (m * (m - 1)) := Nat.even_mul_pred_self m
  rw [mul_comm, Nat.div_two_mul_two_of_even heven]

/-- Burr and Erdős's observation: the Erdős--Sós assertion for `T` implies
the claimed Ramsey bound for `T`. -/
theorem treeRamseyProperty_of_erdosSosFor
    {n : ℕ} (hn : 2 ≤ n) (T : SimpleGraph (Fin n))
    (hES : ErdosSosFor T) :
    TreeRamseyProperty T (2 * n - 2) := by
  classical
  intro G
  let M := 2 * n - 2
  let threshold := (n - 2) * M
  by_cases hred : threshold < 2 * G.edgeFinset.card
  · exact Or.inl (hES G (by
      simpa only [Fintype.card_fin, threshold, M] using hred))
  · right
    apply hES Gᶜ
    suffices threshold < 2 * Gᶜ.edgeFinset.card by
      simpa only [Fintype.card_fin, threshold, M] using this
    have hred_le : 2 * G.edgeFinset.card ≤ threshold := Nat.le_of_not_gt hred
    by_contra hblue
    have hblue_le : 2 * Gᶜ.edgeFinset.card ≤ threshold :=
      Nat.le_of_not_gt hblue
    have hsum := card_edges_add_card_edges_compl G
    have hsumM : G.edgeFinset.card + Gᶜ.edgeFinset.card = M.choose 2 := by
      simpa only [Fintype.card_fin, M] using hsum
    have htotal : 2 * M.choose 2 ≤ 2 * threshold := by
      rw [← hsumM]
      omega
    have hstrict : 2 * threshold < 2 * M.choose 2 := by
      change
        2 * ((n - 2) * (2 * n - 2)) <
          2 * (2 * n - 2).choose 2
      rw [twice_choose_two]
      have hhostPos : 0 < 2 * n - 2 := by omega
      have hcoeff : 2 * (n - 2) < 2 * n - 2 - 1 := by omega
      have hmul := Nat.mul_lt_mul_of_pos_right hcoeff hhostPos
      simpa only [mul_assoc, mul_comm, mul_left_comm] using hmul
    omega

/-- Pointwise conditional form of the corrected conjecture. -/
theorem erdos547At_of_erdosSos
    (n : ℕ) (hn : 2 ≤ n)
    (hES : ∀ T : SimpleGraph (Fin n), T.IsTree → ErdosSosFor T) :
    Erdos547At n := by
  intro T hT
  exact treeRamseyProperty_of_erdosSosFor hn T (hES T hT)

/-! ## The finite high-degree bridge used with Zhao's theorem -/

/-- Vertices whose degree reaches a prescribed threshold, with its finite
decision procedure fixed once so later statements are independent of
typeclass-instance choices. -/
def highDegreeVertices {N : ℕ} (G : SimpleGraph (Fin N)) (k : ℕ) :
    Finset (Fin N) := by
  classical
  exact Finset.univ.filter fun v => k ≤ G.degree v

/-- The specialization of Zhao's high-degree tree theorem needed at tree
order `n`. -/
def ZhaoRamseyHostProperty (n : ℕ) : Prop :=
  by
    classical
    exact ∀ G : SimpleGraph (Fin (2 * n - 2)),
      n - 1 ≤ (highDegreeVertices G (n - 1)).card →
        ∀ T : SimpleGraph (Fin n), T.IsTree → T ⊑ G

/-- Eventual availability of the preceding high-degree property. -/
def ZhaoRamseyHostEventualProperty : Prop :=
  ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n → ZhaoRamseyHostProperty n

/-- On the Ramsey host, one of a graph and its complement has at least
`n-1` vertices of degree at least `n-1`. -/
theorem highDegree_dichotomy
    {n : ℕ} (hn : 2 ≤ n) (G : SimpleGraph (Fin (2 * n - 2))) :
    by
      classical
      exact
        n - 1 ≤ (highDegreeVertices G (n - 1)).card ∨
        n - 1 ≤ (highDegreeVertices Gᶜ (n - 1)).card := by
  classical
  let : DecidableRel Gᶜ.Adj := Classical.decRel _
  let q := n - 1
  let redHigh := highDegreeVertices G q
  let blueHigh := highDegreeVertices Gᶜ q
  by_cases hred : q ≤ redHigh.card
  · exact Or.inl (by simpa only [q, redHigh] using hred)
  · right
    have hredCard : redHigh.card ≤ q - 1 := by omega
    let low := Finset.univ \ redHigh
    have hlowCard : q ≤ low.card := by
      have hcard : (Finset.univ : Finset (Fin (2 * n - 2))).card = 2 * q := by
        simp only [Finset.card_univ, Fintype.card_fin, q]
        omega
      dsimp only [low]
      rw [Finset.card_sdiff_of_subset (Finset.subset_univ redHigh), hcard]
      omega
    have hsubset : low ⊆ blueHigh := by
      intro v hv
      have hvNotRed : v ∉ redHigh := (Finset.mem_sdiff.mp hv).2
      have hvDegree : G.degree v ≤ q - 1 := by
        have : ¬q ≤ G.degree v := by
          simpa only [redHigh, highDegreeVertices, Finset.mem_filter,
            Finset.mem_univ, true_and]
            using hvNotRed
        omega
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ v, ?_⟩
      rw [G.degree_compl]
      simp only [Fintype.card_fin, q] at hvDegree ⊢
      omega
    have : q ≤ blueHigh.card :=
      hlowCard.trans (Finset.card_le_card hsubset)
    simpa only [q, blueHigh] using this

/-- The purely finite complement argument converting Zhao's high-degree
theorem at order `n` into the Ramsey conclusion at that order. -/
theorem erdos547At_of_zhaoRamseyHostProperty
    (n : ℕ) (hn : 2 ≤ n) (hZhao : ZhaoRamseyHostProperty n) :
    Erdos547At n := by
  classical
  intro T hT G
  rcases highDegree_dichotomy hn G with hred | hblue
  · exact Or.inl (hZhao G hred T hT)
  · exact Or.inr (hZhao Gᶜ hblue T hT)

/-- An eventual Zhao high-degree theorem gives exactly the sufficiently-large
form of Problem 547, with the threshold enlarged only to exclude `n < 2`. -/
theorem eventuallyErdos547_of_zhaoRamseyHostEventualProperty
    (hZhao : ZhaoRamseyHostEventualProperty) : EventuallyErdos547 := by
  rcases hZhao with ⟨n₀, hn₀⟩
  refine ⟨max 2 n₀, ?_⟩
  intro n hn
  exact erdos547At_of_zhaoRamseyHostProperty n
    (le_trans (le_max_left 2 n₀) hn)
    (hn₀ n (le_trans (le_max_right 2 n₀) hn))

/-- The actual source-host construction proves the eventual embedding
property without an embedding or extremal-case hypothesis. -/
theorem zhaoRamseyHostEventualProperty : ZhaoRamseyHostEventualProperty := by
  classical
  obtain ⟨n₀, h⟩ := ZhaoSourceZhaoRamseyHost.eventual_tree_containment
  refine ⟨n₀, ?_⟩
  intro n hn G hlarge T hT
  exact h n hn G hlarge T hT

/-- The established resolution of Erdős Problem 547: every sufficiently
large tree has diagonal Ramsey number at most twice its order minus two.
The quantifier is uniform over all trees of each sufficiently large order. -/
theorem eventually_erdos_547 : EventuallyErdos547 :=
  eventuallyErdos547_of_zhaoRamseyHostEventualProperty zhaoRamseyHostEventualProperty

/-- The established tree Ramsey bound, uniformly for sufficiently large orders. -/
theorem erdos_547 :
    ∃ n₀ : ℕ, ∀ n ≥ n₀, ∀ T : SimpleGraph (Fin n), T.IsTree →
      ∀ G : SimpleGraph (Fin (2 * n - 2)), T ⊑ G ∨ T ⊑ Gᶜ :=
  eventually_erdos_547

/-- The unrestricted version fails for the one-vertex tree. -/
theorem not_erdos_547 :
    ¬ ∀ n : ℕ, ∀ T : SimpleGraph (Fin n), T.IsTree →
      ∀ G : SimpleGraph (Fin (2 * n - 2)), T ⊑ G ∨ T ⊑ Gᶜ := by
  simpa [LiteralErdos547, Erdos547At, TreeRamseyProperty] using
    not_literalErdos547

#print axioms not_literalErdos547
#print axioms treeRamseyProperty_of_erdosSosFor
#print axioms erdos547At_of_erdosSos
#print axioms highDegree_dichotomy
#print axioms erdos547At_of_zhaoRamseyHostProperty
#print axioms eventuallyErdos547_of_zhaoRamseyHostEventualProperty
#print axioms zhaoRamseyHostEventualProperty
#print axioms eventually_erdos_547

end Erdos547b
