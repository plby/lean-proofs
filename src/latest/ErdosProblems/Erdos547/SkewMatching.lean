import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Tactic

/-!
# Fractional allocations used in the positive-proportion embedding argument

The oriented weights are controlled by their load at each vertex. We do not
impose a separate bound of one on an oriented edge: the load bound gives the
needed finite bound, and this convention is closed under adding compatible
allocations. Ordinary fractional matchings retain the usual normalization.

The matching and embedding existence theorems are not assumed in this file.
-/

noncomputable section

namespace Erdos547.DPRS

open Finset SimpleGraph
open scoped BigOperators

variable {V : Type*} [Fintype V] {G : SimpleGraph V}

/-- A fractional matching, represented symmetrically on ordered pairs and
extended by zero to nonedges. -/
structure FractionalMatching (G : SimpleGraph V) where
  weight : V → V → ℝ
  symmetric : ∀ u v, weight u v = weight v u
  nonnegative : ∀ u v, 0 ≤ weight u v
  supported : ∀ u v, ¬ G.Adj u v → weight u v = 0
  capacity : ∀ u, ∑ v, weight u v ≤ 1

namespace FractionalMatching

def load (μ : FractionalMatching G) (v : V) : ℝ := ∑ u, μ.weight v u

/-- Each unoriented edge is counted twice in the ordered-pair representation. -/
def total (μ : FractionalMatching G) : ℝ := (∑ u, ∑ v, μ.weight u v) / 2

theorem load_nonneg (μ : FractionalMatching G) (v : V) : 0 ≤ μ.load v :=
  Finset.sum_nonneg fun u _ ↦ μ.nonnegative v u

theorem load_le_one (μ : FractionalMatching G) (v : V) : μ.load v ≤ 1 := μ.capacity v

theorem sum_load (μ : FractionalMatching G) : ∑ v, μ.load v = 2 * μ.total := by
  dsimp [load, total]
  ring

theorem weight_le_one (μ : FractionalMatching G) (u v : V) : μ.weight u v ≤ 1 := by
  have h : μ.weight u v ≤ ∑ w, μ.weight u w :=
    Finset.single_le_sum (fun w _ ↦ μ.nonnegative u w) (Finset.mem_univ v)
  exact h.trans (μ.capacity u)

end FractionalMatching

/-- An oriented fractional allocation with ratio `γ` between the two ends of
each oriented edge. The capacity inequality is written without denominators. -/
structure SkewMatching (G : SimpleGraph V) (γ : ℝ) where
  skew_nonneg : 0 ≤ γ
  weight : V → V → ℝ
  nonnegative : ∀ u v, 0 ≤ weight u v
  supported : ∀ u v, ¬ G.Adj u v → weight u v = 0
  capacity : ∀ u, (∑ v, weight u v) + γ * (∑ v, weight v u) ≤ 1 + γ

namespace SkewMatching

variable {γ δ : ℝ}

def outLoad (σ : SkewMatching G γ) (u : V) : ℝ := (∑ v, σ.weight u v) / (1 + γ)

def inLoad (σ : SkewMatching G γ) (u : V) : ℝ := γ * (∑ v, σ.weight v u) / (1 + γ)

def load (σ : SkewMatching G γ) (u : V) : ℝ := σ.outLoad u + σ.inLoad u

def total (σ : SkewMatching G γ) : ℝ := ∑ u, ∑ v, σ.weight u v

theorem denominator_pos (σ : SkewMatching G γ) : 0 < 1 + γ := by
  have h := σ.skew_nonneg
  linarith

theorem outLoad_nonneg (σ : SkewMatching G γ) (u : V) : 0 ≤ σ.outLoad u :=
  div_nonneg (Finset.sum_nonneg fun v _ ↦ σ.nonnegative u v) σ.denominator_pos.le

theorem inLoad_nonneg (σ : SkewMatching G γ) (u : V) : 0 ≤ σ.inLoad u :=
  div_nonneg (mul_nonneg σ.skew_nonneg
    (Finset.sum_nonneg fun v _ ↦ σ.nonnegative v u)) σ.denominator_pos.le

theorem load_nonneg (σ : SkewMatching G γ) (u : V) : 0 ≤ σ.load u :=
  add_nonneg (σ.outLoad_nonneg u) (σ.inLoad_nonneg u)

theorem load_le_one (σ : SkewMatching G γ) (u : V) : σ.load u ≤ 1 := by
  change (∑ v, σ.weight u v) / (1 + γ) + γ * (∑ v, σ.weight v u) / (1 + γ) ≤ 1
  rw [← add_div]
  exact (div_le_one σ.denominator_pos).mpr (σ.capacity u)

theorem sum_outLoad (σ : SkewMatching G γ) : ∑ u, σ.outLoad u = σ.total / (1 + γ) := by
  simp only [outLoad, total, Finset.sum_div]

theorem sum_inLoad (σ : SkewMatching G γ) : ∑ u, σ.inLoad u = γ * σ.total / (1 + γ) := by
  simp only [inLoad, ← Finset.sum_div, ← Finset.mul_sum]
  congr 2
  exact Finset.sum_comm

/-- The total oriented weight equals the total vertex load, for every skew. -/
theorem sum_load (σ : SkewMatching G γ) : ∑ u, σ.load u = σ.total := by
  simp only [load, Finset.sum_add_distrib, sum_outLoad, sum_inLoad]
  field_simp [ne_of_gt σ.denominator_pos]

theorem total_le_card (σ : SkewMatching G γ) : σ.total ≤ Fintype.card V := by
  rw [← σ.sum_load]
  calc
    _ ≤ ∑ _u : V, (1 : ℝ) := Finset.sum_le_sum fun u _ ↦ σ.load_le_one u
    _ = _ := by simp

/-- The vertex constraints provide a finite bound on each arc weight. -/
theorem weight_le_denominator (σ : SkewMatching G γ) (u v : V) : σ.weight u v ≤ 1 + γ := by
  have hrow : σ.weight u v ≤ ∑ w, σ.weight u w :=
    Finset.single_le_sum (fun w _ ↦ σ.nonnegative u w) (Finset.mem_univ v)
  have hin : 0 ≤ γ * ∑ w, σ.weight w u :=
    mul_nonneg σ.skew_nonneg (Finset.sum_nonneg fun w _ ↦ σ.nonnegative w u)
  have hcap := σ.capacity u
  linarith

/-- Scaling down preserves all vertex capacities. -/
def scale (σ : SkewMatching G γ) (t : ℝ) (ht : 0 ≤ t) (htone : t ≤ 1) : SkewMatching G γ where
  skew_nonneg := σ.skew_nonneg
  weight u v := t * σ.weight u v
  nonnegative u v := mul_nonneg ht (σ.nonnegative u v)
  supported u v h := by rw [σ.supported u v h, mul_zero]
  capacity u := by
    simp only [← Finset.mul_sum]
    have h₁ := mul_le_mul_of_nonneg_left (σ.capacity u) ht
    have h₂ := mul_le_mul_of_nonneg_right htone σ.denominator_pos.le
    nlinarith only [h₁, h₂]

@[simp] theorem scale_outLoad (σ : SkewMatching G γ) (t : ℝ) (ht : 0 ≤ t) (htone : t ≤ 1)
    (u : V) : (σ.scale t ht htone).outLoad u = t * σ.outLoad u := by
  simp only [outLoad, scale, ← Finset.mul_sum]
  ring

@[simp] theorem scale_inLoad (σ : SkewMatching G γ) (t : ℝ) (ht : 0 ≤ t) (htone : t ≤ 1)
    (u : V) : (σ.scale t ht htone).inLoad u = t * σ.inLoad u := by
  simp only [inLoad, scale, ← Finset.mul_sum]
  ring

@[simp] theorem scale_load (σ : SkewMatching G γ) (t : ℝ) (ht : 0 ≤ t) (htone : t ≤ 1)
    (u : V) : (σ.scale t ht htone).load u = t * σ.load u := by
  simp only [load, scale_outLoad, scale_inLoad]
  ring

@[simp] theorem scale_total (σ : SkewMatching G γ) (t : ℝ) (ht : 0 ≤ t) (htone : t ≤ 1) :
    (σ.scale t ht htone).total = t * σ.total := by
  simp only [total, scale, Finset.mul_sum]

/-- Forget the orientation in a balanced allocation. -/
def toFractional (σ : SkewMatching G 1) : FractionalMatching G where
  weight u v := (σ.weight u v + σ.weight v u) / 2
  symmetric u v := by ring
  nonnegative u v := div_nonneg (add_nonneg (σ.nonnegative u v) (σ.nonnegative v u)) (by norm_num)
  supported u v h := by
    rw [σ.supported u v h, σ.supported v u (fun hvu ↦ h hvu.symm)]
    norm_num
  capacity u := by
    rw [← Finset.sum_div, Finset.sum_add_distrib]
    have h := σ.capacity u
    norm_num at h
    linarith

theorem toFractional_load (σ : SkewMatching G 1) (u : V) : σ.toFractional.load u = σ.load u := by
  simp only [FractionalMatching.load, toFractional, load, outLoad, inLoad,
    ← Finset.sum_div, Finset.sum_add_distrib]
  norm_num
  ring

theorem toFractional_total (σ : SkewMatching G 1) : σ.toFractional.total = σ.total / 2 := by
  have h := σ.toFractional.sum_load
  simp only [toFractional_load, σ.sum_load] at h
  linarith

end SkewMatching

end Erdos547.DPRS

#print axioms Erdos547.DPRS.SkewMatching.sum_load
#print axioms Erdos547.DPRS.SkewMatching.toFractional_total
