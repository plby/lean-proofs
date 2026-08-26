import ErdosProblems.Erdos547.SkewMatching

/-!
# Directed edge weights, saturation and truncation

The underlying adjacency is symmetric, but weights may be asymmetric after
subtracting vertex loads. No matching existence assertion is assumed here.
-/

noncomputable section

namespace Erdos547.DPRS

open Finset SimpleGraph
open scoped BigOperators

variable {V : Type*} {G : SimpleGraph V}

structure EdgeWeights (G : SimpleGraph V) where
  weight : V → V → ℝ
  nonnegative : ∀ u v, 0 ≤ weight u v
  at_most_one : ∀ u v, weight u v ≤ 1
  supported : ∀ u v, ¬ G.Adj u v → weight u v = 0

namespace EdgeWeights

variable [Fintype V]

def degree (w : EdgeWeights G) (u : V) : ℝ := ∑ v, w.weight u v

def degreeOn (w : EdgeWeights G) (S : Finset V) (u : V) : ℝ := ∑ v ∈ S, w.weight u v

def saturation (w : EdgeWeights G) (load : V → ℝ) (u : V) : ℝ :=
  ∑ v, min (w.weight u v) (load v)

theorem degree_nonneg (w : EdgeWeights G) (u : V) : 0 ≤ w.degree u :=
  Finset.sum_nonneg fun v _ ↦ w.nonnegative u v

theorem degree_le_card (w : EdgeWeights G) (u : V) : w.degree u ≤ Fintype.card V := by
  calc
    _ ≤ ∑ _v : V, (1 : ℝ) := Finset.sum_le_sum fun v _ ↦ w.at_most_one u v
    _ = _ := by simp

theorem saturation_nonneg (w : EdgeWeights G) (load : V → ℝ)
    (hload : ∀ v, 0 ≤ load v) (u : V) : 0 ≤ w.saturation load u :=
  Finset.sum_nonneg fun v _ ↦ le_min (w.nonnegative u v) (hload v)

theorem saturation_le_degree (w : EdgeWeights G) (load : V → ℝ) (u : V) :
    w.saturation load u ≤ w.degree u := Finset.sum_le_sum fun _v _ ↦ min_le_left _ _

theorem saturation_le_sum_load (w : EdgeWeights G) (load : V → ℝ) (u : V) :
    w.saturation load u ≤ ∑ v, load v := Finset.sum_le_sum fun _v _ ↦ min_le_right _ _

/-- Subtract an already assigned load at the destination of each arc. -/
def truncate (w : EdgeWeights G) (load : V → ℝ) (hload : ∀ v, 0 ≤ load v) : EdgeWeights G where
  weight u v := max 0 (w.weight u v - load v)
  nonnegative u v := le_max_left _ _
  at_most_one u v := max_le (by norm_num) (by have h := w.at_most_one u v; linarith [hload v])
  supported u v h := by
    rw [w.supported u v h]
    exact max_eq_left (by linarith [hload v])

omit [Fintype V] in
theorem truncate_weight_le (w : EdgeWeights G) (load : V → ℝ)
    (hload : ∀ v, 0 ≤ load v) (u v : V) : (w.truncate load hload).weight u v ≤ w.weight u v := by
  exact max_le (w.nonnegative u v) (sub_le_self _ (hload v))

theorem degree_truncate_add_saturation (w : EdgeWeights G) (load : V → ℝ)
    (hload : ∀ v, 0 ≤ load v) (u : V) :
    (w.truncate load hload).degree u + w.saturation load u = w.degree u := by
  simp only [degree, saturation, truncate, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro v _
  by_cases h : w.weight u v ≤ load v
  · rw [min_eq_left h, max_eq_left (by linarith)]
    ring
  · rw [min_eq_right (le_of_not_ge h), max_eq_right (by linarith)]
    ring

theorem min_add_min_truncated (w a b : ℝ) (hab : a ≤ b) :
    min w a + min (max 0 (w - a)) (b - a) = min w b := by
  by_cases hwa : w ≤ a
  · rw [min_eq_left hwa, max_eq_left (by linarith),
      min_eq_left (by linarith), min_eq_left (hwa.trans hab)]
    ring
  · have haw : a ≤ w := le_of_not_ge hwa
    rw [min_eq_right haw, max_eq_right (by linarith)]
    by_cases hbw : b ≤ w
    · rw [min_eq_right (by linarith), min_eq_right hbw]
      ring
    · rw [min_eq_left (by linarith), min_eq_left (le_of_not_ge hbw)]
      ring

/-- Saturation splits exactly across an initial allocation and its remainder. -/
theorem saturation_truncate_add (w : EdgeWeights G) (a b : V → ℝ)
    (ha : ∀ v, 0 ≤ a v) (hab : ∀ v, a v ≤ b v) (u : V) :
    w.saturation a u + (w.truncate a ha).saturation (fun v ↦ b v - a v) u =
      w.saturation b u := by
  simp only [saturation, truncate, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro v _
  exact min_add_min_truncated (w.weight u v) (a v) (b v) (hab v)

end EdgeWeights

end Erdos547.DPRS

#print axioms Erdos547.DPRS.EdgeWeights.degree_truncate_add_saturation
#print axioms Erdos547.DPRS.EdgeWeights.saturation_truncate_add
