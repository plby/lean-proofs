/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import Mathlib

open scoped ENNReal

namespace Erdos1129

/-- An ordered choice of `n` distinct interpolation nodes in `[-1, 1]`.

Writing the nodes in increasing order loses no configurations: the Lebesgue
function is invariant under a permutation of its summands. -/
structure NodeConfiguration (n : ℕ) where
  nodes : Fin n → ℝ
  strictMono_nodes : StrictMono nodes
  nodes_mem : ∀ i, nodes i ∈ Set.Icc (-1 : ℝ) 1

instance {n : ℕ} : CoeFun (NodeConfiguration n) (fun _ ↦ Fin n → ℝ) :=
  ⟨NodeConfiguration.nodes⟩

/-- The `k`th fundamental polynomial for Lagrange interpolation. -/
noncomputable def lagrangeBasis {n : ℕ} (X : NodeConfiguration n)
    (k : Fin n) (x : ℝ) : ℝ :=
  ∏ i ∈ Finset.univ.erase k, (x - X i) / (X k - X i)

/-- The Lebesgue function `x ↦ ∑ k, |l_k(x)|`. -/
noncomputable def lebesgueFunction {n : ℕ} (X : NodeConfiguration n)
    (x : ℝ) : ℝ :=
  ∑ k : Fin n, |lagrangeBasis X k x|

/-- The Lebesgue constant on `[-1,1]`.

We use the complete-lattice supremum in `ℝ≥0∞`.  Since the summands are
nonnegative and continuous, this is the `ENNReal` image of the usual real
maximum. -/
noncomputable def lebesgueConstant {n : ℕ} (X : NodeConfiguration n) : ℝ≥0∞ :=
  ⨆ x : Set.Icc (-1 : ℝ) 1, ENNReal.ofReal (lebesgueFunction X x)

/-- A node configuration is globally optimal among configurations of the same
cardinality. -/
def IsOptimal {n : ℕ} (X : NodeConfiguration n) : Prop :=
  ∀ Y : NodeConfiguration n, lebesgueConstant X ≤ lebesgueConstant Y

/-- The symmetric triple `(-a, 0, a)`. -/
def symmetricThreeNodes (a : ℝ) (ha : 0 < a) (ha1 : a ≤ 1) :
    NodeConfiguration 3 where
  nodes := ![-a, 0, a]
  strictMono_nodes := by
    apply Fin.strictMono_iff_lt_succ.2
    intro i
    fin_cases i
    · change -a < 0
      linarith
    · change 0 < a
      exact ha
  nodes_mem := by
    intro i
    fin_cases i
    · change -1 ≤ -a ∧ -a ≤ 1
      constructor <;> linarith
    · change -1 ≤ (0 : ℝ) ∧ (0 : ℝ) ≤ 1
      norm_num
    · change -1 ≤ a ∧ a ≤ 1
      constructor <;> linarith

/-- The canonical triple `(-1,0,1)`. -/
def standardThreeNodes : NodeConfiguration 3 :=
  symmetricThreeNodes 1 (by norm_num) (by norm_num)

/-- A distinct contracted triple which is still globally optimal. -/
noncomputable def contractedThreeNodes : NodeConfiguration 3 :=
  symmetricThreeNodes (49 / 50 : ℝ) (by norm_num) (by norm_num)

theorem erdos_1129 :
    standardThreeNodes ≠ contractedThreeNodes ∧
      lebesgueConstant standardThreeNodes = ENNReal.ofReal (5 / 4 : ℝ) ∧
      lebesgueConstant contractedThreeNodes = ENNReal.ofReal (5 / 4 : ℝ) ∧
      IsOptimal standardThreeNodes ∧ IsOptimal contractedThreeNodes := by
  sorry

end Erdos1129
