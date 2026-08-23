/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
This is a Lean formalization of a solution to Erdős Problem 1129.
https://www.erdosproblems.com/forum/thread/1129

Informal authors:
- Carl de Boor
- Allan Pinkus

Formal authors:
- Codex
- GPT-5.6 Sol

URLs:
- https://github.com/plby/lean-proofs/blob/main/ErdosProblems/Erdos1129.md
-/
/-
This file formalizes a correction to the unconstrained formulation of Erdős
Problem 1129.  The de Boor--Pinkus uniqueness theorem concerns *canonical*
nodes (the endpoints are fixed).  With only the requirement that the nodes lie
in `[-1, 1]`, minimizers are not unique.  We prove the exact universal lower
bound for three nodes and exhibit two distinct minimizers.

The accompanying mathematical write-up is `tex/1129.tex`.
-/

import Mathlib

namespace Erdos1129

open scoped BigOperators ENNReal
open Finset Set

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

lemma lebesgueFunction_nonneg {n : ℕ} (X : NodeConfiguration n) (x : ℝ) :
    0 ≤ lebesgueFunction X x := by
  exact Finset.sum_nonneg fun _ _ ↦ abs_nonneg _

lemma ofReal_le_lebesgueConstant {n : ℕ} (X : NodeConfiguration n)
    {x : ℝ} (hx : x ∈ Set.Icc (-1 : ℝ) 1) :
    ENNReal.ofReal (lebesgueFunction X x) ≤ lebesgueConstant X := by
  exact le_iSup (fun y : Set.Icc (-1 : ℝ) 1 ↦
    ENNReal.ofReal (lebesgueFunction X y)) ⟨x, hx⟩

/-! ## Three-node midpoint formulae -/

private lemma three_nodes_values (X : NodeConfiguration 3) :
    X 0 < X 1 ∧ X 1 < X 2 := by
  constructor
  · exact X.strictMono_nodes (by decide)
  · exact X.strictMono_nodes (by decide)

private lemma left_midpoint_mem (X : NodeConfiguration 3) :
    (X 0 + X 1) / 2 ∈ Set.Icc (-1 : ℝ) 1 := by
  rcases X.nodes_mem 0 with ⟨h0l, h0r⟩
  rcases X.nodes_mem 1 with ⟨h1l, h1r⟩
  constructor <;> linarith

private lemma right_midpoint_mem (X : NodeConfiguration 3) :
    (X 1 + X 2) / 2 ∈ Set.Icc (-1 : ℝ) 1 := by
  rcases X.nodes_mem 1 with ⟨h1l, h1r⟩
  rcases X.nodes_mem 2 with ⟨h2l, h2r⟩
  constructor <;> linarith

private lemma left_midpoint_formula (X : NodeConfiguration 3) :
    lebesgueFunction X ((X 0 + X 1) / 2) =
      1 + (X 1 - X 0) ^ 2 /
        (2 * (X 2 - X 1) * (X 2 - X 0)) := by
  rcases three_nodes_values X with ⟨h01, h12⟩
  have h02 : X 0 < X 2 := h01.trans h12
  have hL0 : 0 ≤ lagrangeBasis X 0 ((X 0 + X 1) / 2) := by
    simp [lagrangeBasis,
      show Finset.univ.erase (0 : Fin 3) = {1, 2} by decide]
    apply div_nonneg
    · exact mul_nonneg_of_nonpos_of_nonpos (by linarith) (by linarith)
    · exact mul_nonneg_of_nonpos_of_nonpos (by linarith) (by linarith)
  have hL1 : 0 ≤ lagrangeBasis X 1 ((X 0 + X 1) / 2) := by
    simp [lagrangeBasis,
      show Finset.univ.erase (1 : Fin 3) = {0, 2} by decide]
    exact div_nonneg_of_nonpos
      (mul_nonpos_of_nonneg_of_nonpos (by linarith) (by linarith))
      (mul_nonpos_of_nonneg_of_nonpos (by linarith) (by linarith))
  have hL2 : lagrangeBasis X 2 ((X 0 + X 1) / 2) ≤ 0 := by
    simp [lagrangeBasis,
      show Finset.univ.erase (2 : Fin 3) = {0, 1} by decide]
    exact div_nonpos_of_nonpos_of_nonneg
      (mul_nonpos_of_nonneg_of_nonpos (by linarith) (by linarith))
      (mul_nonneg (by linarith) (by linarith))
  rw [lebesgueFunction, Fin.sum_univ_three, abs_of_nonneg hL0,
    abs_of_nonneg hL1, abs_of_nonpos hL2]
  simp [lagrangeBasis,
    show Finset.univ.erase (0 : Fin 3) = {1, 2} by decide,
    show Finset.univ.erase (1 : Fin 3) = {0, 2} by decide,
    show Finset.univ.erase (2 : Fin 3) = {0, 1} by decide]
  field_simp [sub_ne_zero.mpr h01.ne, sub_ne_zero.mpr h01.ne',
    sub_ne_zero.mpr h12.ne, sub_ne_zero.mpr h12.ne',
    sub_ne_zero.mpr h02.ne, sub_ne_zero.mpr h02.ne']
  ring

private lemma right_midpoint_formula (X : NodeConfiguration 3) :
    lebesgueFunction X ((X 1 + X 2) / 2) =
      1 + (X 2 - X 1) ^ 2 /
        (2 * (X 1 - X 0) * (X 2 - X 0)) := by
  rcases three_nodes_values X with ⟨h01, h12⟩
  have h02 : X 0 < X 2 := h01.trans h12
  have hL0 : lagrangeBasis X 0 ((X 1 + X 2) / 2) ≤ 0 := by
    simp [lagrangeBasis,
      show Finset.univ.erase (0 : Fin 3) = {1, 2} by decide]
    exact div_nonpos_of_nonpos_of_nonneg
      (mul_nonpos_of_nonneg_of_nonpos (by linarith) (by linarith))
      (mul_nonneg_of_nonpos_of_nonpos (by linarith) (by linarith))
  have hL1 : 0 ≤ lagrangeBasis X 1 ((X 1 + X 2) / 2) := by
    simp [lagrangeBasis,
      show Finset.univ.erase (1 : Fin 3) = {0, 2} by decide]
    exact div_nonneg_of_nonpos
      (mul_nonpos_of_nonneg_of_nonpos (by linarith) (by linarith))
      (mul_nonpos_of_nonneg_of_nonpos (by linarith) (by linarith))
  have hL2 : 0 ≤ lagrangeBasis X 2 ((X 1 + X 2) / 2) := by
    simp [lagrangeBasis,
      show Finset.univ.erase (2 : Fin 3) = {0, 1} by decide]
    exact div_nonneg
      (mul_nonneg (by linarith) (by linarith))
      (mul_nonneg (by linarith) (by linarith))
  rw [lebesgueFunction, Fin.sum_univ_three, abs_of_nonpos hL0,
    abs_of_nonneg hL1, abs_of_nonneg hL2]
  simp [lagrangeBasis,
    show Finset.univ.erase (0 : Fin 3) = {1, 2} by decide,
    show Finset.univ.erase (1 : Fin 3) = {0, 2} by decide,
    show Finset.univ.erase (2 : Fin 3) = {0, 1} by decide]
  field_simp [sub_ne_zero.mpr h01.ne, sub_ne_zero.mpr h01.ne',
    sub_ne_zero.mpr h12.ne, sub_ne_zero.mpr h12.ne',
    sub_ne_zero.mpr h02.ne, sub_ne_zero.mpr h02.ne']
  ring

/-- Bernstein's sharp elementary lower bound for three free nodes: every
three-node Lebesgue constant is at least `5/4`. -/
theorem three_node_lower_bound (X : NodeConfiguration 3) :
    ENNReal.ofReal (5 / 4 : ℝ) ≤ lebesgueConstant X := by
  rcases three_nodes_values X with ⟨h01, h12⟩
  have h02 : X 0 < X 2 := h01.trans h12
  by_cases hgap : X 2 - X 1 ≤ X 1 - X 0
  · have hden : 0 < 2 * (X 2 - X 1) * (X 2 - X 0) := by positivity
    have hprod :
        0 ≤ ((X 1 - X 0) - (X 2 - X 1)) *
          (2 * (X 1 - X 0) + (X 2 - X 1)) := by positivity
    have hfrac :
        (1 / 4 : ℝ) ≤ (X 1 - X 0) ^ 2 /
          (2 * (X 2 - X 1) * (X 2 - X 0)) := by
      apply (le_div_iff₀ hden).2
      nlinarith
    have hreal :
        (5 / 4 : ℝ) ≤ lebesgueFunction X ((X 0 + X 1) / 2) := by
      rw [left_midpoint_formula]
      linarith
    exact (ENNReal.ofReal_le_ofReal hreal).trans
      (ofReal_le_lebesgueConstant X (left_midpoint_mem X))
  · have hgap' : X 1 - X 0 ≤ X 2 - X 1 := le_of_not_ge hgap
    have hden : 0 < 2 * (X 1 - X 0) * (X 2 - X 0) := by positivity
    have hprod :
        0 ≤ ((X 2 - X 1) - (X 1 - X 0)) *
          (2 * (X 2 - X 1) + (X 1 - X 0)) := by positivity
    have hfrac :
        (1 / 4 : ℝ) ≤ (X 2 - X 1) ^ 2 /
          (2 * (X 1 - X 0) * (X 2 - X 0)) := by
      apply (le_div_iff₀ hden).2
      nlinarith
    have hreal :
        (5 / 4 : ℝ) ≤ lebesgueFunction X ((X 1 + X 2) / 2) := by
      rw [right_midpoint_formula]
      linarith
    exact (ENNReal.ofReal_le_ofReal hreal).trans
      (ofReal_le_lebesgueConstant X (right_midpoint_mem X))

/-! ## Symmetric three-node configurations -/

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

@[simp] lemma symmetricThreeNodes_zero (a : ℝ) (ha : 0 < a) (ha1 : a ≤ 1) :
    symmetricThreeNodes a ha ha1 0 = -a := rfl

@[simp] lemma symmetricThreeNodes_one (a : ℝ) (ha : 0 < a) (ha1 : a ≤ 1) :
    symmetricThreeNodes a ha ha1 1 = 0 := rfl

@[simp] lemma symmetricThreeNodes_two (a : ℝ) (ha : 0 < a) (ha1 : a ≤ 1) :
    symmetricThreeNodes a ha ha1 2 = a := rfl

private lemma symmetric_basis_zero (a : ℝ) (ha : 0 < a) (ha1 : a ≤ 1) (x : ℝ) :
    lagrangeBasis (symmetricThreeNodes a ha ha1) 0 x =
      x * (x - a) / (2 * a ^ 2) := by
  simp [lagrangeBasis,
    show Finset.univ.erase (0 : Fin 3) = {1, 2} by decide]
  field_simp [ha.ne']
  ring

private lemma symmetric_basis_one (a : ℝ) (ha : 0 < a) (ha1 : a ≤ 1) (x : ℝ) :
    lagrangeBasis (symmetricThreeNodes a ha ha1) 1 x =
      1 - x ^ 2 / a ^ 2 := by
  simp [lagrangeBasis,
    show Finset.univ.erase (1 : Fin 3) = {0, 2} by decide]
  field_simp [ha.ne']
  ring

private lemma symmetric_basis_two (a : ℝ) (ha : 0 < a) (ha1 : a ≤ 1) (x : ℝ) :
    lagrangeBasis (symmetricThreeNodes a ha ha1) 2 x =
      x * (x + a) / (2 * a ^ 2) := by
  simp [lagrangeBasis,
    show Finset.univ.erase (2 : Fin 3) = {0, 1} by decide]
  field_simp [ha.ne']
  ring

private lemma symmetric_lebesgue_explicit (a : ℝ) (ha : 0 < a)
    (ha1 : a ≤ 1) (x : ℝ) :
    lebesgueFunction (symmetricThreeNodes a ha ha1) x =
      |x * (x - a) / (2 * a ^ 2)| +
      |1 - x ^ 2 / a ^ 2| +
      |x * (x + a) / (2 * a ^ 2)| := by
  rw [lebesgueFunction, Fin.sum_univ_three, symmetric_basis_zero,
    symmetric_basis_one, symmetric_basis_two]

private lemma one_add_sub_sq_le (u : ℝ) :
    1 + u - u ^ 2 ≤ 5 / 4 := by
  nlinarith [sq_nonneg (u - 1 / 2)]

private lemma one_sub_sub_sq_le (u : ℝ) :
    1 - u - u ^ 2 ≤ 5 / 4 := by
  nlinarith [sq_nonneg (u + 1 / 2)]

/-- If `a² ≥ 8/9`, the symmetric triple has Lebesgue function at most
`5/4` everywhere on `[-1,1]`. -/
private lemma symmetric_lebesgue_le_five_fourths (a : ℝ) (ha : 0 < a)
    (ha1 : a ≤ 1) (haSq : (8 / 9 : ℝ) ≤ a ^ 2)
    {x : ℝ} (hx : x ∈ Set.Icc (-1 : ℝ) 1) :
    lebesgueFunction (symmetricThreeNodes a ha ha1) x ≤ 5 / 4 := by
  rw [symmetric_lebesgue_explicit]
  have ha2 : 0 < a ^ 2 := sq_pos_of_pos ha
  have hden : 0 < 2 * a ^ 2 := mul_pos (by norm_num) ha2
  have hxSq : x ^ 2 ≤ 1 := by
    have hp : 0 ≤ (x + 1) * (1 - x) :=
      mul_nonneg (by linarith [hx.1]) (by linarith [hx.2])
    nlinarith
  have houter : 2 * x ^ 2 / a ^ 2 - 1 ≤ 5 / 4 := by
    have hratio : 2 * x ^ 2 / a ^ 2 ≤ 9 / 4 := by
      apply (div_le_iff₀ ha2).2
      nlinarith
    linarith
  by_cases hleft : x < -a
  · have hx0 : x ≤ 0 := by linarith
    have hxa : x - a ≤ 0 := by linarith
    have hxpa : x + a ≤ 0 := by linarith
    have h0 : 0 ≤ x * (x - a) / (2 * a ^ 2) :=
      div_nonneg (mul_nonneg_of_nonpos_of_nonpos hx0 hxa) hden.le
    have h2 : 0 ≤ x * (x + a) / (2 * a ^ 2) :=
      div_nonneg (mul_nonneg_of_nonpos_of_nonpos hx0 hxpa) hden.le
    have ha2le : a ^ 2 ≤ x ^ 2 := by
      have hp : 0 ≤ (x + a) * (x - a) :=
        mul_nonneg_of_nonpos_of_nonpos hxpa hxa
      nlinarith
    have h1 : 1 - x ^ 2 / a ^ 2 ≤ 0 := by
      have : 1 ≤ x ^ 2 / a ^ 2 := (le_div_iff₀ ha2).2 (by nlinarith)
      linarith
    rw [abs_of_nonneg h0, abs_of_nonpos h1, abs_of_nonneg h2]
    calc
      x * (x - a) / (2 * a ^ 2) - (1 - x ^ 2 / a ^ 2) +
          x * (x + a) / (2 * a ^ 2) = 2 * x ^ 2 / a ^ 2 - 1 := by
            field_simp [ha.ne']
            ring
      _ ≤ 5 / 4 := houter
  · have hleft' : -a ≤ x := le_of_not_gt hleft
    by_cases hx0 : x ≤ 0
    · have hxa : x - a ≤ 0 := by linarith
      have hxpa : 0 ≤ x + a := by linarith
      have h0 : 0 ≤ x * (x - a) / (2 * a ^ 2) :=
        div_nonneg (mul_nonneg_of_nonpos_of_nonpos hx0 hxa) hden.le
      have h2 : x * (x + a) / (2 * a ^ 2) ≤ 0 :=
        div_nonpos_of_nonpos_of_nonneg
          (mul_nonpos_of_nonpos_of_nonneg hx0 hxpa) hden.le
      have hx2le : x ^ 2 ≤ a ^ 2 := by
        have hp : 0 ≤ (x + a) * (a - x) :=
          mul_nonneg hxpa (by linarith)
        nlinarith
      have h1 : 0 ≤ 1 - x ^ 2 / a ^ 2 := by
        have : x ^ 2 / a ^ 2 ≤ 1 := (div_le_iff₀ ha2).2 (by nlinarith)
        linarith
      rw [abs_of_nonneg h0, abs_of_nonneg h1, abs_of_nonpos h2]
      calc
        x * (x - a) / (2 * a ^ 2) + (1 - x ^ 2 / a ^ 2) -
            x * (x + a) / (2 * a ^ 2) =
            1 - (x / a) - (x / a) ^ 2 := by
              field_simp [ha.ne']
              ring
        _ ≤ 5 / 4 := one_sub_sub_sq_le (x / a)
    · have hx0' : 0 ≤ x := le_of_not_ge hx0
      by_cases hright : x ≤ a
      · have hxa : x - a ≤ 0 := sub_nonpos.mpr hright
        have hxpa : 0 ≤ x + a := by linarith
        have h0 : x * (x - a) / (2 * a ^ 2) ≤ 0 :=
          div_nonpos_of_nonpos_of_nonneg
            (mul_nonpos_of_nonneg_of_nonpos hx0' hxa) hden.le
        have h2 : 0 ≤ x * (x + a) / (2 * a ^ 2) :=
          div_nonneg (mul_nonneg hx0' hxpa) hden.le
        have hx2le : x ^ 2 ≤ a ^ 2 := by nlinarith
        have h1 : 0 ≤ 1 - x ^ 2 / a ^ 2 := by
          have : x ^ 2 / a ^ 2 ≤ 1 := (div_le_iff₀ ha2).2 (by nlinarith)
          linarith
        rw [abs_of_nonpos h0, abs_of_nonneg h1, abs_of_nonneg h2]
        calc
          -(x * (x - a) / (2 * a ^ 2)) + (1 - x ^ 2 / a ^ 2) +
              x * (x + a) / (2 * a ^ 2) =
              1 + (x / a) - (x / a) ^ 2 := by
                field_simp [ha.ne']
                ring
          _ ≤ 5 / 4 := one_add_sub_sq_le (x / a)
      · have hright' : a ≤ x := le_of_not_ge hright
        have hxa : 0 ≤ x - a := sub_nonneg.mpr hright'
        have hxpa : 0 ≤ x + a := by linarith
        have h0 : 0 ≤ x * (x - a) / (2 * a ^ 2) :=
          div_nonneg (mul_nonneg hx0' hxa) hden.le
        have h2 : 0 ≤ x * (x + a) / (2 * a ^ 2) :=
          div_nonneg (mul_nonneg hx0' hxpa) hden.le
        have ha2le : a ^ 2 ≤ x ^ 2 := by nlinarith
        have h1 : 1 - x ^ 2 / a ^ 2 ≤ 0 := by
          have : 1 ≤ x ^ 2 / a ^ 2 := (le_div_iff₀ ha2).2 (by nlinarith)
          linarith
        rw [abs_of_nonneg h0, abs_of_nonpos h1, abs_of_nonneg h2]
        calc
          x * (x - a) / (2 * a ^ 2) - (1 - x ^ 2 / a ^ 2) +
              x * (x + a) / (2 * a ^ 2) = 2 * x ^ 2 / a ^ 2 - 1 := by
                field_simp [ha.ne']
                ring
          _ ≤ 5 / 4 := houter

/-- Every sufficiently wide symmetric triple has the sharp constant `5/4`. -/
theorem lebesgueConstant_symmetricThreeNodes (a : ℝ) (ha : 0 < a)
    (ha1 : a ≤ 1) (haSq : (8 / 9 : ℝ) ≤ a ^ 2) :
    lebesgueConstant (symmetricThreeNodes a ha ha1) =
      ENNReal.ofReal (5 / 4 : ℝ) := by
  apply le_antisymm
  · apply iSup_le
    intro x
    exact ENNReal.ofReal_le_ofReal
      (symmetric_lebesgue_le_five_fourths a ha ha1 haSq x.property)
  · exact three_node_lower_bound (symmetricThreeNodes a ha ha1)

/-- The canonical triple `(-1,0,1)`. -/
def standardThreeNodes : NodeConfiguration 3 :=
  symmetricThreeNodes 1 (by norm_num) (by norm_num)

/-- A distinct contracted triple which is still globally optimal. -/
noncomputable def contractedThreeNodes : NodeConfiguration 3 :=
  symmetricThreeNodes (49 / 50 : ℝ) (by norm_num) (by norm_num)

@[simp] theorem lebesgueConstant_standardThreeNodes :
    lebesgueConstant standardThreeNodes = ENNReal.ofReal (5 / 4 : ℝ) := by
  exact lebesgueConstant_symmetricThreeNodes 1 (by norm_num) (by norm_num) (by norm_num)

@[simp] theorem lebesgueConstant_contractedThreeNodes :
    lebesgueConstant contractedThreeNodes = ENNReal.ofReal (5 / 4 : ℝ) := by
  exact lebesgueConstant_symmetricThreeNodes (49 / 50 : ℝ)
    (by norm_num) (by norm_num) (by norm_num)

theorem standardThreeNodes_isOptimal : IsOptimal standardThreeNodes := by
  intro Y
  rw [lebesgueConstant_standardThreeNodes]
  exact three_node_lower_bound Y

theorem contractedThreeNodes_isOptimal : IsOptimal contractedThreeNodes := by
  intro Y
  rw [lebesgueConstant_contractedThreeNodes]
  exact three_node_lower_bound Y

theorem standardThreeNodes_ne_contractedThreeNodes :
    standardThreeNodes ≠ contractedThreeNodes := by
  intro h
  have h0 := congrArg (fun X : NodeConfiguration 3 ↦ X 0) h
  norm_num [standardThreeNodes, contractedThreeNodes] at h0

/-- **Resolution of the unconstrained uniqueness claim in Erdős Problem 1129.**

For the problem exactly as stated, with three arbitrary nodes in `[-1,1]`, the
minimum Lebesgue constant is `5/4`, but the minimizer is not unique.  The two
explicit configurations below are distinct and both globally minimize the exact
Lebesgue constant defined from the fundamental Lagrange polynomials. -/
theorem erdos_1129 :
    standardThreeNodes ≠ contractedThreeNodes ∧
      lebesgueConstant standardThreeNodes = ENNReal.ofReal (5 / 4 : ℝ) ∧
      lebesgueConstant contractedThreeNodes = ENNReal.ofReal (5 / 4 : ℝ) ∧
      IsOptimal standardThreeNodes ∧ IsOptimal contractedThreeNodes := by
  exact ⟨standardThreeNodes_ne_contractedThreeNodes,
    lebesgueConstant_standardThreeNodes,
    lebesgueConstant_contractedThreeNodes,
    standardThreeNodes_isOptimal,
    contractedThreeNodes_isOptimal⟩

end Erdos1129

#print axioms Erdos1129.erdos_1129
