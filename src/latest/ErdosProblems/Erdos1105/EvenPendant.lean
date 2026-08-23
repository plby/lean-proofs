import ErdosProblems.Erdos1105.PendantReduction
import ErdosProblems.Erdos1105.PathFormulaArithmetic

namespace Erdos1105

open SimpleGraph

lemma even_pendant_order_bound (n l q : ℕ) (hl : 3 ≤ l) (hn : 2 * l + 2 ≤ n)
    (hq : pathFormula n (2 * l + 2) < q)
    (hupper : q ≤ pathExtremalEdges n (2 * l + 1) 1) : n ≤ 3 * l := by
  have hlinear := even_path_linear_term n l (by omega) (by omega)
  rw [pathFormula_even] at hq
  have hlin : pathExtremalEdges n (2 * l + 1) (l - 1) ≤ pathExtremalEdges n (2 * l + 1) 1 := by
    have h := (le_max_right _ _).trans_lt hq
    omega
  have h₁ := pathExtremalEdges_twice n (2 * l + 1) 1 (by omega) (by omega)
  have hd := pathExtremalEdges_twice n (2 * l + 1) (l - 1) (by omega) (by omega)
  have hl' : (3 : ℚ) ≤ l := by exact_mod_cast hl
  have hlin' : (pathExtremalEdges n (2 * l + 1) (l - 1) : ℚ) ≤
      pathExtremalEdges n (2 * l + 1) 1 := by exact_mod_cast hlin
  have hpred : ((l - 1 : ℕ) : ℚ) = l - 1 := by rw [Nat.cast_sub (by omega), Nat.cast_one]
  simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one, hpred] at h₁ hd
  by_contra! hlarge
  have hn' : (3 : ℚ) * l + 1 ≤ n := by
    exact_mod_cast (show 3 * l + 1 ≤ n by omega)
  have hm₁ := mul_nonneg (show (0 : ℚ) ≤ l - 2 by linarith)
    (show (0 : ℚ) ≤ n - (3 * l + 1) by linarith)
  have hm₂ := mul_pos (show (0 : ℚ) < l - 1 by linarith)
    (show (0 : ℚ) < l - 2 by linarith)
  nlinarith

/-- Once all connected representatives have the pendant-clique shape,
the even-path case reduces by deletion just as the odd-path case does. -/
theorem connected_even_pendant_reduction {V C : Type*} [Fintype V] [Fintype C]
    (c : (⊤ : SimpleGraph V).edgeSet → C) {l : ℕ} (hl : 3 ≤ l)
    (hn : 2 * l + 2 ≤ Fintype.card V)
    (hq : pathFormula (Fintype.card V) (2 * l + 2) < Fintype.card C)
    (hshapes : ∀ Q : SimpleGraph V, IsFullRepresentative c Q → Q.Preconnected →
      PendantCliqueShape Q (2 * l + 2))
    (R : SimpleGraph V) (hR : IsFullRepresentative c R) (hconn : R.Preconnected) :
    2 * l + 2 < Fintype.card V ∧ ∃ v, ∃ Q : SimpleGraph {w // w ≠ v},
      IsFullRepresentative (restrictVertexColoring c v) Q ∧ Q.Preconnected := by
  classical
  have hshape := hshapes R hR hconn
  have hupper := hshape.edge_bound (by omega) hn
  rw [hR.card_edges] at hupper
  have hupper' : Fintype.card C ≤ pathExtremalEdges (Fintype.card V) (2 * l + 1) 1 := by
    simpa only [show 2 * l + 2 - 1 = 2 * l + 1 by omega] using hupper
  have hsmall := even_pendant_order_bound (Fintype.card V) l (Fintype.card C) hl hn hq hupper'
  apply connected_pendant_reduction c (by omega) hn (by omega) ?_ hshapes R hR hconn
  have h := (le_max_left _ _).trans_lt (show
    max ((2 * l + 2 - 2).choose 2 + 1) _ < Fintype.card C from hq)
  omega

end Erdos1105

#print axioms Erdos1105.connected_even_pendant_reduction
