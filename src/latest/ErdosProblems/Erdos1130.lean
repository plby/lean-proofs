/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
This is a Lean formalization of a solution to Erdős Problem 1130.
https://www.erdosproblems.com/forum/thread/1130

Informal authors:
- Carl de Boor
- Allan Pinkus

Formal authors:
- Codex
- GPT-5.6 Sol

URLs:
- https://github.com/plby/lean-proofs/blob/main/ErdosProblems/Erdos1130.md
-/
/-
This file formalizes the literal free-node formulation of Erdős Problem 1130.

The resolution quoted on the problem page conflates this formulation with the
canonical theorem of de Boor and Pinkus, in which the two endpoints are fixed
interpolation nodes.  For free nodes, equioscillation does not characterize all
maximizers.  We prove this rigorously for three nodes: the configuration
`(-1/2, 0, 1/2)` globally maximizes `upsilon`, but its four local peaks are not
all equal.

The accompanying mathematical reconstruction is `tex/1130.tex`.
-/

import Mathlib

namespace Erdos1130

open scoped BigOperators
open Finset Set

/-- An ordered choice of `n` distinct interpolation nodes in `[-1, 1]`. -/
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

/-- The interpolation nodes with the two ambient endpoints adjoined. -/
def augmentedNodes {n : ℕ} (X : NodeConfiguration n) : Fin (n + 2) → ℝ :=
  Fin.cons (-1) (Fin.snoc X.nodes 1)

lemma augmentedNodes_monotone {n : ℕ} (X : NodeConfiguration n) :
    Monotone (augmentedNodes X) := by
  cases n with
  | zero =>
      rw [Fin.monotone_iff_le_succ]
      intro i
      fin_cases i
      norm_num [augmentedNodes, Fin.snoc]
  | succ m =>
      have hs : Monotone (Fin.snoc X.nodes 1) := by
        rw [← Fin.insertNth_last']
        exact Fin.insertNth_last_monotone X.strictMono_nodes.monotone 1
          (X.nodes_mem (Fin.last m)).2
      unfold augmentedNodes
      rw [← Fin.insertNth_zero']
      apply Fin.insertNth_zero_monotone hs (-1)
      simpa using (X.nodes_mem (0 : Fin (m + 1))).1

lemma continuous_lagrangeBasis {n : ℕ} (X : NodeConfiguration n) (k : Fin n) :
    Continuous (lagrangeBasis X k) := by
  unfold lagrangeBasis
  fun_prop

lemma continuous_lebesgueFunction {n : ℕ} (X : NodeConfiguration n) :
    Continuous (lebesgueFunction X) := by
  unfold lebesgueFunction
  exact continuous_finsetSum _ fun i _ ↦ (continuous_lagrangeBasis X i).abs

/-- The maximum of the Lebesgue function on the `i`th interval between
successive augmented nodes. -/
noncomputable def localPeak {n : ℕ} (X : NodeConfiguration n)
    (i : Fin (n + 1)) : ℝ :=
  sSup (lebesgueFunction X ''
    Set.Icc (augmentedNodes X i.castSucc) (augmentedNodes X i.succ))

/-- The minimum of all `n+1` local peaks in the literal statement. -/
noncomputable def upsilon {n : ℕ} (X : NodeConfiguration n) : ℝ :=
  Finset.univ.inf' Finset.univ_nonempty (localPeak X)

/-- The equality condition asserted in the supplied resolution. -/
def GapPeaksEqual {n : ℕ} (X : NodeConfiguration n) : Prop :=
  ∀ i j, localPeak X i = localPeak X j

/-- Global maximality for the literal free-node max--min problem. -/
def IsUpsilonMaximizer {n : ℕ} (X : NodeConfiguration n) : Prop :=
  ∀ Y : NodeConfiguration n, upsilon Y ≤ upsilon X

lemma localPeak_le_of_forall {n : ℕ} (X : NodeConfiguration n)
    (i : Fin (n + 1)) (a : ℝ)
    (h : ∀ x ∈ Set.Icc (augmentedNodes X i.castSucc) (augmentedNodes X i.succ),
      lebesgueFunction X x ≤ a) :
    localPeak X i ≤ a := by
  apply csSup_le
  · have hab := augmentedNodes_monotone X i.castSucc_le_succ
    exact ⟨lebesgueFunction X (augmentedNodes X i.castSucc),
      ⟨augmentedNodes X i.castSucc, ⟨le_rfl, hab⟩, rfl⟩⟩
  · rintro y ⟨x, hx, rfl⟩
    exact h x hx

lemma le_localPeak {n : ℕ} (X : NodeConfiguration n) (i : Fin (n + 1))
    {x : ℝ}
    (hx : x ∈ Set.Icc (augmentedNodes X i.castSucc) (augmentedNodes X i.succ)) :
    lebesgueFunction X x ≤ localPeak X i := by
  have hab := augmentedNodes_monotone X i.castSucc_le_succ
  obtain ⟨y, hy, hmax⟩ := isCompact_Icc.exists_isMaxOn
    (Set.nonempty_Icc.mpr hab) (continuous_lebesgueFunction X).continuousOn
  have hg : IsGreatest
      (lebesgueFunction X ''
        Set.Icc (augmentedNodes X i.castSucc) (augmentedNodes X i.succ))
      (lebesgueFunction X y) := by
    constructor
    · exact ⟨y, hy, rfl⟩
    · rintro z ⟨w, hw, rfl⟩
      exact hmax hw
  change lebesgueFunction X x ≤ sSup
    (lebesgueFunction X ''
      Set.Icc (augmentedNodes X i.castSucc) (augmentedNodes X i.succ))
  rw [hg.csSup_eq]
  exact hmax hx

lemma upsilon_le_localPeak {n : ℕ} (X : NodeConfiguration n) (i : Fin (n + 1)) :
    upsilon X ≤ localPeak X i := by
  exact Finset.inf'_le _ (Finset.mem_univ i)

/-! ## The universal three-node upper bound -/

private lemma three_nodes_lt (X : NodeConfiguration 3) :
    X 0 < X 1 ∧ X 1 < X 2 := by
  exact ⟨X.strictMono_nodes (by decide), X.strictMono_nodes (by decide)⟩

private lemma lagrangeBasis_zero_three (X : NodeConfiguration 3) (x : ℝ) :
    lagrangeBasis X 0 x =
      (x - X 1) * (x - X 2) / ((X 0 - X 1) * (X 0 - X 2)) := by
  have h : (Finset.univ.erase (0 : Fin 3)) = {1, 2} := by decide
  rw [lagrangeBasis, h]
  simp [div_eq_mul_inv]
  ring

private lemma lagrangeBasis_one_three (X : NodeConfiguration 3) (x : ℝ) :
    lagrangeBasis X 1 x =
      (x - X 0) * (x - X 2) / ((X 1 - X 0) * (X 1 - X 2)) := by
  have h : (Finset.univ.erase (1 : Fin 3)) = {0, 2} := by decide
  rw [lagrangeBasis, h]
  simp [div_eq_mul_inv]
  ring

private lemma lagrangeBasis_two_three (X : NodeConfiguration 3) (x : ℝ) :
    lagrangeBasis X 2 x =
      (x - X 0) * (x - X 1) / ((X 2 - X 0) * (X 2 - X 1)) := by
  have h : (Finset.univ.erase (2 : Fin 3)) = {0, 1} := by decide
  rw [lagrangeBasis, h]
  simp [div_eq_mul_inv]
  ring

private lemma lebesgueFunction_left_gap (X : NodeConfiguration 3) (x : ℝ)
    (hx : x ∈ Set.Icc (X 0) (X 1)) :
    lebesgueFunction X x =
      1 + 2 * (x - X 0) * (X 1 - x) / ((X 2 - X 0) * (X 2 - X 1)) := by
  obtain ⟨h01, h12⟩ := three_nodes_lt X
  have h02 : X 0 < X 2 := h01.trans h12
  have hl0 : 0 ≤ lagrangeBasis X 0 x := by
    rw [lagrangeBasis_zero_three]
    exact div_nonneg
      (mul_nonneg_of_nonpos_of_nonpos
        (sub_nonpos.mpr hx.2) (sub_nonpos.mpr (hx.2.trans h12.le)))
      (mul_nonneg_of_nonpos_of_nonpos
        (sub_nonpos.mpr h01.le) (sub_nonpos.mpr h02.le))
  have hl1 : 0 ≤ lagrangeBasis X 1 x := by
    rw [lagrangeBasis_one_three]
    exact div_nonneg_of_nonpos
      (mul_nonpos_of_nonneg_of_nonpos
        (sub_nonneg.mpr hx.1) (sub_nonpos.mpr (hx.2.trans h12.le)))
      (mul_nonpos_of_nonneg_of_nonpos
        (sub_nonneg.mpr h01.le) (sub_nonpos.mpr h12.le))
  have hl2 : lagrangeBasis X 2 x ≤ 0 := by
    rw [lagrangeBasis_two_three]
    exact div_nonpos_of_nonpos_of_nonneg
      (mul_nonpos_of_nonneg_of_nonpos
        (sub_nonneg.mpr hx.1) (sub_nonpos.mpr hx.2))
      (mul_nonneg (sub_nonneg.mpr h02.le) (sub_nonneg.mpr h12.le))
  have h01n : X 0 - X 1 ≠ 0 := sub_ne_zero.mpr h01.ne
  have h02n : X 0 - X 2 ≠ 0 := sub_ne_zero.mpr h02.ne
  have h10n : X 1 - X 0 ≠ 0 := sub_ne_zero.mpr h01.ne'
  have h12n : X 1 - X 2 ≠ 0 := sub_ne_zero.mpr h12.ne
  have h20n : X 2 - X 0 ≠ 0 := sub_ne_zero.mpr h02.ne'
  have h21n : X 2 - X 1 ≠ 0 := sub_ne_zero.mpr h12.ne'
  rw [lebesgueFunction, Fin.sum_univ_three, abs_of_nonneg hl0,
    abs_of_nonneg hl1, abs_of_nonpos hl2,
    lagrangeBasis_zero_three, lagrangeBasis_one_three, lagrangeBasis_two_three]
  field_simp [h01n, h02n, h10n, h12n, h20n, h21n]
  ring

private lemma lebesgueFunction_right_gap (X : NodeConfiguration 3) (x : ℝ)
    (hx : x ∈ Set.Icc (X 1) (X 2)) :
    lebesgueFunction X x =
      1 + 2 * (x - X 1) * (X 2 - x) / ((X 1 - X 0) * (X 2 - X 0)) := by
  obtain ⟨h01, h12⟩ := three_nodes_lt X
  have h02 : X 0 < X 2 := h01.trans h12
  have hl0 : lagrangeBasis X 0 x ≤ 0 := by
    rw [lagrangeBasis_zero_three]
    exact div_nonpos_of_nonpos_of_nonneg
      (mul_nonpos_of_nonneg_of_nonpos
        (sub_nonneg.mpr hx.1) (sub_nonpos.mpr hx.2))
      (mul_nonneg_of_nonpos_of_nonpos
        (sub_nonpos.mpr h01.le) (sub_nonpos.mpr h02.le))
  have hl1 : 0 ≤ lagrangeBasis X 1 x := by
    rw [lagrangeBasis_one_three]
    exact div_nonneg_of_nonpos
      (mul_nonpos_of_nonneg_of_nonpos
        (sub_nonneg.mpr (h01.le.trans hx.1)) (sub_nonpos.mpr hx.2))
      (mul_nonpos_of_nonneg_of_nonpos
        (sub_nonneg.mpr h01.le) (sub_nonpos.mpr h12.le))
  have hl2 : 0 ≤ lagrangeBasis X 2 x := by
    rw [lagrangeBasis_two_three]
    exact div_nonneg
      (mul_nonneg
        (sub_nonneg.mpr (h01.le.trans hx.1)) (sub_nonneg.mpr hx.1))
      (mul_nonneg (sub_nonneg.mpr h02.le) (sub_nonneg.mpr h12.le))
  have h01n : X 0 - X 1 ≠ 0 := sub_ne_zero.mpr h01.ne
  have h02n : X 0 - X 2 ≠ 0 := sub_ne_zero.mpr h02.ne
  have h10n : X 1 - X 0 ≠ 0 := sub_ne_zero.mpr h01.ne'
  have h12n : X 1 - X 2 ≠ 0 := sub_ne_zero.mpr h12.ne
  have h20n : X 2 - X 0 ≠ 0 := sub_ne_zero.mpr h02.ne'
  have h21n : X 2 - X 1 ≠ 0 := sub_ne_zero.mpr h12.ne'
  rw [lebesgueFunction, Fin.sum_univ_three, abs_of_nonpos hl0,
    abs_of_nonneg hl1, abs_of_nonneg hl2,
    lagrangeBasis_zero_three, lagrangeBasis_one_three, lagrangeBasis_two_three]
  field_simp [h01n, h02n, h10n, h12n, h20n, h21n]
  ring

private lemma lebesgueFunction_left_gap_le_five_fourths
    (X : NodeConfiguration 3)
    (hgap : X 1 - X 0 ≤ X 2 - X 1)
    (x : ℝ) (hx : x ∈ Set.Icc (X 0) (X 1)) :
    lebesgueFunction X x ≤ (5 : ℝ) / 4 := by
  obtain ⟨h01, h12⟩ := three_nodes_lt X
  have h02 : X 0 < X 2 := h01.trans h12
  have hden : 0 < (X 2 - X 0) * (X 2 - X 1) :=
    mul_pos (sub_pos.mpr h02) (sub_pos.mpr h12)
  rw [lebesgueFunction_left_gap X x hx]
  have hquad : 4 * (x - X 0) * (X 1 - x) ≤ (X 1 - X 0) ^ 2 := by
    nlinarith [sq_nonneg (2 * x - X 0 - X 1)]
  have hdom :
      2 * (X 1 - X 0) ^ 2 ≤ (X 2 - X 0) * (X 2 - X 1) := by
    have hnonneg :
        0 ≤ (X 2 - X 1 - (X 1 - X 0)) *
          ((X 2 - X 1) + 2 * (X 1 - X 0)) :=
      mul_nonneg (sub_nonneg.mpr hgap) (by nlinarith)
    nlinarith
  have hfrac :
      2 * (x - X 0) * (X 1 - x) /
          ((X 2 - X 0) * (X 2 - X 1)) ≤ (1 : ℝ) / 4 := by
    rw [div_le_iff₀ hden]
    nlinarith
  linarith

private lemma lebesgueFunction_right_gap_le_five_fourths
    (X : NodeConfiguration 3)
    (hgap : X 2 - X 1 ≤ X 1 - X 0)
    (x : ℝ) (hx : x ∈ Set.Icc (X 1) (X 2)) :
    lebesgueFunction X x ≤ (5 : ℝ) / 4 := by
  obtain ⟨h01, h12⟩ := three_nodes_lt X
  have h02 : X 0 < X 2 := h01.trans h12
  have hden : 0 < (X 1 - X 0) * (X 2 - X 0) :=
    mul_pos (sub_pos.mpr h01) (sub_pos.mpr h02)
  rw [lebesgueFunction_right_gap X x hx]
  have hquad : 4 * (x - X 1) * (X 2 - x) ≤ (X 2 - X 1) ^ 2 := by
    nlinarith [sq_nonneg (2 * x - X 1 - X 2)]
  have hdom :
      2 * (X 2 - X 1) ^ 2 ≤ (X 1 - X 0) * (X 2 - X 0) := by
    have hnonneg :
        0 ≤ (X 1 - X 0 - (X 2 - X 1)) *
          ((X 1 - X 0) + 2 * (X 2 - X 1)) :=
      mul_nonneg (sub_nonneg.mpr hgap) (by nlinarith)
    nlinarith
  have hfrac :
      2 * (x - X 1) * (X 2 - x) /
          ((X 1 - X 0) * (X 2 - X 0)) ≤ (1 : ℝ) / 4 := by
    rw [div_le_iff₀ hden]
    nlinarith
  linarith

private lemma localPeak_one_le_five_fourths (X : NodeConfiguration 3)
    (hgap : X 1 - X 0 ≤ X 2 - X 1) :
    localPeak X 1 ≤ (5 : ℝ) / 4 := by
  apply localPeak_le_of_forall
  intro x hx
  have hx' : x ∈ Set.Icc (X 0) (X 1) := by
    change x ∈ Set.Icc (X 0) (X 1) at hx
    exact hx
  exact lebesgueFunction_left_gap_le_five_fourths X hgap x hx'

private lemma localPeak_two_le_five_fourths (X : NodeConfiguration 3)
    (hgap : X 2 - X 1 ≤ X 1 - X 0) :
    localPeak X 2 ≤ (5 : ℝ) / 4 := by
  apply localPeak_le_of_forall
  intro x hx
  have hx' : x ∈ Set.Icc (X 1) (X 2) := by
    change x ∈ Set.Icc (X 1) (X 2) at hx
    exact hx
  exact lebesgueFunction_right_gap_le_five_fourths X hgap x hx'

/-- For every three-node system, the literal max--min quantity is at most `5/4`. -/
theorem upsilon_three_le (X : NodeConfiguration 3) :
    upsilon X ≤ (5 : ℝ) / 4 := by
  by_cases hgap : X 1 - X 0 ≤ X 2 - X 1
  · exact (upsilon_le_localPeak X 1).trans
      (localPeak_one_le_five_fourths X hgap)
  · exact (upsilon_le_localPeak X 2).trans
      (localPeak_two_le_five_fourths X (le_of_not_ge hgap))

/-! ## A maximizing triple which does not equioscillate -/

/-- The centered triple of half-width `1/2`. -/
noncomputable def halfNodes : NodeConfiguration 3 where
  nodes := ![-(1 / 2 : ℝ), 0, (1 / 2 : ℝ)]
  strictMono_nodes := by
    apply Fin.strictMono_iff_lt_succ.2
    intro i
    fin_cases i
    · change -(1 / 2 : ℝ) < 0
      norm_num
    · change (0 : ℝ) < 1 / 2
      norm_num
  nodes_mem := by
    intro i
    fin_cases i <;> norm_num

private lemma half_basis_zero (x : ℝ) :
    lagrangeBasis halfNodes 0 x = 2 * x ^ 2 - x := by
  simp [lagrangeBasis, halfNodes,
    show Finset.univ.erase (0 : Fin 3) = {1, 2} by decide]
  ring

private lemma half_basis_one (x : ℝ) :
    lagrangeBasis halfNodes 1 x = 1 - 4 * x ^ 2 := by
  simp [lagrangeBasis, halfNodes,
    show Finset.univ.erase (1 : Fin 3) = {0, 2} by decide]
  ring

private lemma half_basis_two (x : ℝ) :
    lagrangeBasis halfNodes 2 x = 2 * x ^ 2 + x := by
  simp [lagrangeBasis, halfNodes,
    show Finset.univ.erase (2 : Fin 3) = {0, 1} by decide]
  ring

private lemma half_lebesgue_outer_left {x : ℝ}
    (hx : x ∈ Set.Icc (-1 : ℝ) (-(1 / 2 : ℝ))) :
    lebesgueFunction halfNodes x = 8 * x ^ 2 - 1 := by
  have h0 : 0 ≤ 2 * x ^ 2 - x := by
    nlinarith [mul_nonneg_of_nonpos_of_nonpos (show x ≤ 0 by linarith [hx.2])
      (show 2 * x - 1 ≤ 0 by linarith [hx.2])]
  have h1 : 1 - 4 * x ^ 2 ≤ 0 := by
    nlinarith [mul_nonneg_of_nonpos_of_nonpos
      (show 2 * x + 1 ≤ 0 by linarith [hx.2])
      (show 2 * x - 1 ≤ 0 by linarith [hx.2])]
  have h2 : 0 ≤ 2 * x ^ 2 + x := by
    nlinarith [mul_nonneg_of_nonpos_of_nonpos (show x ≤ 0 by linarith [hx.2])
      (show 2 * x + 1 ≤ 0 by linarith [hx.2])]
  rw [lebesgueFunction, Fin.sum_univ_three, half_basis_zero,
    half_basis_one, half_basis_two, abs_of_nonneg h0, abs_of_nonpos h1,
    abs_of_nonneg h2]
  ring

private lemma half_lebesgue_inner_left {x : ℝ}
    (hx : x ∈ Set.Icc (-(1 / 2 : ℝ)) 0) :
    lebesgueFunction halfNodes x = 1 - 2 * x - 4 * x ^ 2 := by
  have h0 : 0 ≤ 2 * x ^ 2 - x := by
    nlinarith [mul_nonneg_of_nonpos_of_nonpos (show x ≤ 0 by exact hx.2)
      (show 2 * x - 1 ≤ 0 by linarith [hx.2])]
  have h1 : 0 ≤ 1 - 4 * x ^ 2 := by
    nlinarith [mul_nonneg (show 0 ≤ x + 1 / 2 by linarith [hx.1])
      (show 0 ≤ 1 / 2 - x by linarith [hx.2])]
  have h2 : 2 * x ^ 2 + x ≤ 0 := by
    nlinarith [mul_nonneg (show 0 ≤ x + 1 / 2 by linarith [hx.1])
      (show 0 ≤ -x by linarith [hx.2])]
  rw [lebesgueFunction, Fin.sum_univ_three, half_basis_zero,
    half_basis_one, half_basis_two, abs_of_nonneg h0, abs_of_nonneg h1,
    abs_of_nonpos h2]
  ring

private lemma half_lebesgue_inner_right {x : ℝ}
    (hx : x ∈ Set.Icc (0 : ℝ) (1 / 2 : ℝ)) :
    lebesgueFunction halfNodes x = 1 + 2 * x - 4 * x ^ 2 := by
  have h0 : 2 * x ^ 2 - x ≤ 0 := by
    nlinarith [mul_nonneg (show 0 ≤ x by exact hx.1)
      (show 0 ≤ 1 / 2 - x by linarith [hx.2])]
  have h1 : 0 ≤ 1 - 4 * x ^ 2 := by
    nlinarith [mul_nonneg (show 0 ≤ x + 1 / 2 by linarith [hx.1])
      (show 0 ≤ 1 / 2 - x by linarith [hx.2])]
  have h2 : 0 ≤ 2 * x ^ 2 + x := by nlinarith [sq_nonneg x]
  rw [lebesgueFunction, Fin.sum_univ_three, half_basis_zero,
    half_basis_one, half_basis_two, abs_of_nonpos h0, abs_of_nonneg h1,
    abs_of_nonneg h2]
  ring

private lemma half_lebesgue_outer_right {x : ℝ}
    (hx : x ∈ Set.Icc (1 / 2 : ℝ) 1) :
    lebesgueFunction halfNodes x = 8 * x ^ 2 - 1 := by
  have h0 : 0 ≤ 2 * x ^ 2 - x := by
    nlinarith [mul_nonneg (show 0 ≤ x by linarith [hx.1])
      (show 0 ≤ 2 * x - 1 by linarith [hx.1])]
  have h1 : 1 - 4 * x ^ 2 ≤ 0 := by
    nlinarith [mul_nonneg (show 0 ≤ 2 * x - 1 by linarith [hx.1])
      (show 0 ≤ 2 * x + 1 by linarith [hx.1])]
  have h2 : 0 ≤ 2 * x ^ 2 + x := by
    nlinarith [mul_nonneg (show 0 ≤ x by linarith [hx.1])
      (show 0 ≤ 2 * x + 1 by linarith [hx.1])]
  rw [lebesgueFunction, Fin.sum_univ_three, half_basis_zero,
    half_basis_one, half_basis_two, abs_of_nonneg h0, abs_of_nonpos h1,
    abs_of_nonneg h2]
  ring

lemma localPeak_half_zero : localPeak halfNodes 0 = 7 := by
  change sSup (lebesgueFunction halfNodes ''
    Set.Icc (-1 : ℝ) (-(1 / 2 : ℝ))) = 7
  apply le_antisymm
  · apply csSup_le
    · exact ⟨lebesgueFunction halfNodes (-1), -1, by norm_num, rfl⟩
    · rintro y ⟨x, hx, rfl⟩
      rw [half_lebesgue_outer_left hx]
      nlinarith [mul_nonneg (show 0 ≤ x + 1 by linarith [hx.1])
        (show 0 ≤ 1 - x by linarith [hx.2])]
  · apply le_csSup
    · refine ⟨7, ?_⟩
      rintro y ⟨x, hx, rfl⟩
      rw [half_lebesgue_outer_left hx]
      nlinarith [mul_nonneg (show 0 ≤ x + 1 by linarith [hx.1])
        (show 0 ≤ 1 - x by linarith [hx.2])]
    · refine ⟨-1, by norm_num, ?_⟩
      norm_num [half_lebesgue_outer_left (show (-1 : ℝ) ∈
        Set.Icc (-1 : ℝ) (-(1 / 2 : ℝ)) by norm_num)]

lemma localPeak_half_one : localPeak halfNodes 1 = 5 / 4 := by
  change sSup (lebesgueFunction halfNodes ''
    Set.Icc (-(1 / 2 : ℝ)) 0) = 5 / 4
  apply le_antisymm
  · apply csSup_le
    · exact ⟨lebesgueFunction halfNodes 0, 0, by norm_num, rfl⟩
    · rintro y ⟨x, hx, rfl⟩
      rw [half_lebesgue_inner_left hx]
      nlinarith [sq_nonneg (x + 1 / 4)]
  · apply le_csSup
    · refine ⟨5 / 4, ?_⟩
      rintro y ⟨x, hx, rfl⟩
      rw [half_lebesgue_inner_left hx]
      nlinarith [sq_nonneg (x + 1 / 4)]
    · refine ⟨-(1 / 4 : ℝ), by norm_num, ?_⟩
      norm_num [half_lebesgue_inner_left (show (-(1 / 4 : ℝ)) ∈
        Set.Icc (-(1 / 2 : ℝ)) 0 by norm_num)]

lemma localPeak_half_two : localPeak halfNodes 2 = 5 / 4 := by
  change sSup (lebesgueFunction halfNodes ''
    Set.Icc (0 : ℝ) (1 / 2 : ℝ)) = 5 / 4
  apply le_antisymm
  · apply csSup_le
    · exact ⟨lebesgueFunction halfNodes 0, 0, by norm_num, rfl⟩
    · rintro y ⟨x, hx, rfl⟩
      rw [half_lebesgue_inner_right hx]
      nlinarith [sq_nonneg (x - 1 / 4)]
  · apply le_csSup
    · refine ⟨5 / 4, ?_⟩
      rintro y ⟨x, hx, rfl⟩
      rw [half_lebesgue_inner_right hx]
      nlinarith [sq_nonneg (x - 1 / 4)]
    · refine ⟨(1 / 4 : ℝ), by norm_num, ?_⟩
      norm_num [half_lebesgue_inner_right (show ((1 / 4 : ℝ)) ∈
        Set.Icc (0 : ℝ) (1 / 2 : ℝ) by norm_num)]

lemma localPeak_half_three : localPeak halfNodes 3 = 7 := by
  change sSup (lebesgueFunction halfNodes '' Set.Icc (1 / 2 : ℝ) 1) = 7
  apply le_antisymm
  · apply csSup_le
    · exact ⟨lebesgueFunction halfNodes 1, 1, by norm_num, rfl⟩
    · rintro y ⟨x, hx, rfl⟩
      rw [half_lebesgue_outer_right hx]
      nlinarith [mul_nonneg (show 0 ≤ x + 1 by linarith [hx.1])
        (show 0 ≤ 1 - x by linarith [hx.2])]
  · apply le_csSup
    · refine ⟨7, ?_⟩
      rintro y ⟨x, hx, rfl⟩
      rw [half_lebesgue_outer_right hx]
      nlinarith [mul_nonneg (show 0 ≤ x + 1 by linarith [hx.1])
        (show 0 ≤ 1 - x by linarith [hx.2])]
    · refine ⟨1, by norm_num, ?_⟩
      norm_num [half_lebesgue_outer_right (show (1 : ℝ) ∈
        Set.Icc (1 / 2 : ℝ) 1 by norm_num)]

lemma upsilon_halfNodes : upsilon halfNodes = 5 / 4 := by
  apply le_antisymm
  · calc
      upsilon halfNodes ≤ localPeak halfNodes 1 :=
        Finset.inf'_le _ (Finset.mem_univ (1 : Fin 4))
      _ = 5 / 4 := localPeak_half_one
  · rw [upsilon]
    apply Finset.le_inf'
    intro i hi
    fin_cases i
    · norm_num [localPeak_half_zero]
    · simpa using localPeak_half_one.ge
    · simpa using localPeak_half_two.ge
    · change (5 / 4 : ℝ) ≤ localPeak halfNodes (3 : Fin 4)
      rw [localPeak_half_three]
      norm_num

lemma not_GapPeaksEqual_halfNodes : ¬ GapPeaksEqual halfNodes := by
  intro h
  have h01 := h 0 1
  rw [localPeak_half_zero, localPeak_half_one] at h01
  norm_num at h01

/-- The literal free-node three-point problem has a global maximizer whose
four augmented-gap peaks are not all equal.  This disproves the
characterization quoted in the supplied resolution. -/
theorem erdos_1130_free_node_characterization_false :
    ∃ X : NodeConfiguration 3,
      IsUpsilonMaximizer X ∧ ¬ GapPeaksEqual X := by
  refine ⟨halfNodes, ?_, not_GapPeaksEqual_halfNodes⟩
  intro Y
  rw [upsilon_halfNodes]
  exact upsilon_three_le Y

end Erdos1130

#print axioms Erdos1130.erdos_1130_free_node_characterization_false
