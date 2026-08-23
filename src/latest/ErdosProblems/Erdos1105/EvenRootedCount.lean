import ErdosProblems.Erdos1105.RootedPathEdges
import ErdosProblems.Erdos1105.PathFormulaArithmetic

namespace Erdos1105

open SimpleGraph

lemma rooted_count_le_even_formula (n l q : ℕ) (hl : 3 ≤ l) (hn : 2 * l + 2 ≤ n)
    (hq : 2 * q ≤ (l + 1) * (n - 1)) : q ≤ pathFormula n (2 * l + 2) := by
  rw [pathFormula_even]
  apply le_trans ?_ (le_max_right _ _)
  have hq' : (2 : ℚ) * q ≤ (l + 1) * (n - 1 : ℕ) := by exact_mod_cast hq
  have hl' : (3 : ℚ) ≤ l := by exact_mod_cast hl
  have hn' : (2 : ℚ) * l + 2 ≤ n := by exact_mod_cast hn
  have h₁ : ((n - 1 : ℕ) : ℚ) = n - 1 := by rw [Nat.cast_sub (by omega), Nat.cast_one]
  have h₂ : ((l - 1 : ℕ) : ℚ) = l - 1 := by rw [Nat.cast_sub (by omega), Nat.cast_one]
  have h₃ : ((n - l + 1 : ℕ) : ℚ) = n - l + 1 := by
    rw [Nat.cast_add, Nat.cast_sub (by omega), Nat.cast_one]
  rw [h₁] at hq'
  have hchoose := Nat.cast_choose_two ℚ (l - 1)
  rw [h₂] at hchoose
  have hm := mul_nonneg (show (0 : ℚ) ≤ l - 3 by linarith)
    (show (0 : ℚ) ≤ n - (2 * l + 2) by linarith)
  have hlm := mul_nonneg (show (0 : ℚ) ≤ l - 3 by linarith)
    (show (0 : ℚ) ≤ l + 1 by linarith)
  have h : (q : ℚ) ≤ ((l - 1).choose 2 : ℚ) +
      (l - 1 : ℕ) * (n - l + 1 : ℕ) + 2 := by
    rw [h₂, h₃]
    nlinarith
  exact_mod_cast h

theorem even_path_bound_of_rooted_path_bound {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hconn : G.Preconnected)
    (v : V) {l : ℕ} (hl : 3 ≤ l) (hn : 2 * l + 2 ≤ Fintype.card V)
    (hpath : ∀ w, ∀ p : G.Walk v w, p.IsPath → p.length ≤ l) :
    G.edgeFinset.card ≤ pathFormula (Fintype.card V) (2 * l + 2) :=
  rooted_count_le_even_formula _ _ _ hl hn
    (edges_le_of_rooted_path_bound G hconn v (by omega) hpath)

end Erdos1105

#print axioms Erdos1105.even_path_bound_of_rooted_path_bound
