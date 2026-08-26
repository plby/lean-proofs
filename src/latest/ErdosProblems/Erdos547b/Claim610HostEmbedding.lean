/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos547b.Claim610HostDensity
import ErdosProblems.Erdos547b.Claim610LeafCoreEmbedding

/-!
# The non-EC1 large-leaf alternative in Zhao's Claim 6.10

This composes the balanced-host density calculation with the literal
leaf-core completion theorem.
-/

open scoped SimpleGraph

noncomputable section

namespace Erdos547b.ZhaoClaim610HostEmbedding

open Finset Fintype SimpleGraph
open Erdos547b.ZhaoClaim68
open Erdos547b.ZhaoClaim610HostDensity
open Erdos547b.ZhaoClaim610LeafCoreEmbedding

universe u

/-- A tree with a sufficiently small non-leaf core embeds in every Ramsey
host outside EC1. -/
theorem isContained_of_leaf_bound_of_not_extremalCaseOne
    {n k : ℕ} (hn : 2 ≤ n) (beta : ℚ)
    (G : SimpleGraph (Fin (2 * n - 2))) [DecidableRel G.Adj]
    (hlarge : n - 1 ≤
      #(Finset.univ.filter fun v ↦ n - 1 ≤ G.degree v))
    (hnotEC1 : ¬ZhaoExtremalCaseOne beta G)
    (hnumeric : (2 * k * ((n - 1 : ℕ) : ℚ)) ≤
      beta * ((n - 1 : ℕ) : ℚ) * ((n - 1 : ℕ) : ℚ))
    {A : Type u} [Fintype A] [DecidableEq A]
    (T : SimpleGraph A) [DecidableRel T.Adj]
    (hT : T.IsTree) (hcard : 3 ≤ Fintype.card A)
    (horder : Fintype.card A - 1 ≤ n - 1)
    (hleaf : Fintype.card A ≤ k + 1 + #(graphLeaves T)) :
    T.IsContained G := by
  obtain ⟨X, hlargeX, U, hUne, hmin⟩ :=
    exists_large_induced_minDegree_of_not_extremalCaseOne hn beta G
      hlarge hnotEC1 hnumeric
  apply isContained_of_leaf_bound_and_twoStage_induced_minDegree G hT hcard
    k hleaf X _ U hUne hmin
  intro x hx
  exact horder.trans (hlargeX x hx)

/-- Contrapositive form: a non-embeddable tree outside EC1 has fewer leaves
than its order minus the admissible core size. -/
theorem card_graphLeaves_lt_sub_of_not_isContained
    {n k : ℕ} (hn : 2 ≤ n) (beta : ℚ)
    (G : SimpleGraph (Fin (2 * n - 2))) [DecidableRel G.Adj]
    (hlarge : n - 1 ≤
      #(Finset.univ.filter fun v ↦ n - 1 ≤ G.degree v))
    (hnotEC1 : ¬ZhaoExtremalCaseOne beta G)
    (hnumeric : (2 * k * ((n - 1 : ℕ) : ℚ)) ≤
      beta * ((n - 1 : ℕ) : ℚ) * ((n - 1 : ℕ) : ℚ))
    {A : Type u} [Fintype A] [DecidableEq A]
    (T : SimpleGraph A) [DecidableRel T.Adj]
    (hT : T.IsTree) (hcard : 3 ≤ Fintype.card A)
    (horder : Fintype.card A - 1 ≤ n - 1)
    (hnotContained : ¬T.IsContained G) :
    #(graphLeaves T) < Fintype.card A - (k + 1) := by
  by_contra h
  have hleaf : Fintype.card A ≤ k + 1 + #(graphLeaves T) := by omega
  exact hnotContained
    (isContained_of_leaf_bound_of_not_extremalCaseOne hn beta G hlarge
      hnotEC1 hnumeric T hT hcard horder hleaf)

end Erdos547b.ZhaoClaim610HostEmbedding

#print axioms Erdos547b.ZhaoClaim610HostEmbedding.isContained_of_leaf_bound_of_not_extremalCaseOne
#print axioms Erdos547b.ZhaoClaim610HostEmbedding.card_graphLeaves_lt_sub_of_not_isContained
