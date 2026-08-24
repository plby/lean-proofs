/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/- Original license: Apache 2.0. Note: This file has been modified. -/
/-
This is a Lean formalization of a solution to Erdős Problem 466.
https://www.erdosproblems.com/forum/thread/466

Informal authors:
- Ronald Graham

Formal authors:
- Codex
- GPT-5.6 Sol

URLs:
- https://github.com/plby/lean-proofs/blob/main/ErdosProblems/Erdos466.md
-/
/-
Copyright (c) 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license.
-/

import Mathlib

/-!
# Erdős Problem 466

Let `N X δ` be the maximum cardinality of a finite set of points in the closed
Euclidean disk of radius `X` whose pairwise distances are at least `δ` away
from every integer.  Graham proved that `N X (1 / 10)` tends to infinity.

We formalize the elementary parabola construction
`P m = (2^m, 4^m)`.  Its pairwise distances lie strictly between
`a + 1/10` and `a + 9/10` for suitable integers `a`.
-/

open Filter Metric Set
open scoped ENNReal NNReal Topology

namespace Erdos466

noncomputable section

/-- The Euclidean plane. -/
abbrev Plane := EuclideanSpace ℝ (Fin 2)

/-- Distance of a real number to the nearest integer. -/
def distToInt (x : ℝ) : ℝ := |x - (round x : ℝ)|

lemma distToInt_nonneg (x : ℝ) : 0 ≤ distToInt x := by
  exact abs_nonneg _

/-- The chosen nearest integer is at least as close as every integer. -/
lemma distToInt_le (x : ℝ) (z : ℤ) : distToInt x ≤ |x - (z : ℝ)| := by
  exact round_le x z

lemma distToInt_le_self {x : ℝ} (hx : 0 ≤ x) : distToInt x ≤ x := by
  simpa [abs_of_nonneg hx] using distToInt_le x 0

/-- A number strictly inside the interval from `a + δ` to `a + 1 - δ`
is more than `δ` away from every integer. -/
lemma distToInt_gt_of_between {x δ : ℝ} (a : ℤ)
    (hleft : (a : ℝ) + δ < x) (hright : x < (a : ℝ) + 1 - δ) :
    δ < distToInt x := by
  rw [distToInt]
  let z : ℤ := round x
  have hz : z ≤ a ∨ a + 1 ≤ z := by omega
  rcases hz with hza | haz
  · have hza' : (z : ℝ) ≤ (a : ℝ) := by exact_mod_cast hza
    calc
      δ < x - (z : ℝ) := by linarith
      _ ≤ |x - (z : ℝ)| := le_abs_self _
  · have haz' : (a : ℝ) + 1 ≤ (z : ℝ) := by exact_mod_cast haz
    calc
      δ < -(x - (z : ℝ)) := by linarith
      _ ≤ |x - (z : ℝ)| := neg_le_abs _

/-- The square-root interval estimate used in Graham's construction. -/
lemma sqrt_sq_add_away (a : ℤ) (r : ℝ) (ha : 1 ≤ a)
    (hlo : (3 / 10 : ℝ) * a ≤ r) (hhi : r ≤ (9 / 5 : ℝ) * a) :
    (1 / 10 : ℝ) < distToInt (Real.sqrt ((a : ℝ) ^ 2 + r)) := by
  have haR : (1 : ℝ) ≤ (a : ℝ) := by exact_mod_cast ha
  have hr : 0 ≤ r := by nlinarith
  have hbase : 0 ≤ (a : ℝ) ^ 2 + r := by positivity
  have hs0 : 0 ≤ Real.sqrt ((a : ℝ) ^ 2 + r) := Real.sqrt_nonneg _
  have hs2 : Real.sqrt ((a : ℝ) ^ 2 + r) ^ 2 = (a : ℝ) ^ 2 + r :=
    Real.sq_sqrt hbase
  apply distToInt_gt_of_between a
  · nlinarith
  · nlinarith

/-- Graham's integer points on the parabola `y = x²`. -/
def grahamPoint (m : ℕ) : Plane := !₂[(2 : ℝ) ^ m, (4 : ℝ) ^ m]

@[simp] lemma grahamPoint_zero (m : ℕ) : grahamPoint m 0 = (2 : ℝ) ^ m := by
  simp [grahamPoint]

@[simp] lemma grahamPoint_one (m : ℕ) : grahamPoint m 1 = (4 : ℝ) ^ m := by
  simp [grahamPoint]

lemma grahamPoint_injective : Function.Injective grahamPoint := by
  intro i j hij
  have hcoord := congrArg (fun p : Plane ↦ p 0) hij
  simpa using (pow_right_strictMono₀ (by norm_num : (1 : ℝ) < 2)).injective hcoord

/-- The exact squared-distance formula for two points of the construction. -/
lemma grahamPoint_dist {i j : ℕ} :
    dist (grahamPoint i) (grahamPoint j) =
      Real.sqrt ((((4 : ℤ) ^ j - (4 : ℤ) ^ i : ℤ) : ℝ) ^ 2 +
        ((2 : ℝ) ^ j - (2 : ℝ) ^ i) ^ 2) := by
  rw [EuclideanSpace.dist_eq]
  simp only [Fin.sum_univ_two, grahamPoint_zero, grahamPoint_one, Real.dist_eq]
  rw [sq_abs, sq_abs]
  norm_num
  ring_nf

/-- Distinct points in the construction have distance more than `1/10`
from every integer. -/
lemma grahamPoint_away {i j : ℕ} (hij : i < j) :
    (1 / 10 : ℝ) < distToInt (dist (grahamPoint i) (grahamPoint j)) := by
  let a : ℤ := (4 : ℤ) ^ j - (4 : ℤ) ^ i
  let u : ℝ := (2 : ℝ) ^ i
  let v : ℝ := (2 : ℝ) ^ j
  have hp4 : (4 : ℤ) ^ i < (4 : ℤ) ^ j :=
    (pow_right_strictMono₀ (by norm_num : (1 : ℤ) < 4)) hij
  have ha : 1 ≤ a := by
    dsimp [a]
    omega
  have hu0 : 0 ≤ u := by positivity
  have hv0 : 0 ≤ v := by positivity
  have huv : 2 * u ≤ v := by
    dsimp [u, v]
    calc
      2 * (2 : ℝ) ^ i = (2 : ℝ) ^ (i + 1) := by rw [pow_succ]; ring
      _ ≤ (2 : ℝ) ^ j :=
        (pow_right_strictMono₀ (by norm_num : (1 : ℝ) < 2)).monotone
          (Nat.succ_le_iff.2 hij)
  have hpow (k : ℕ) : (4 : ℝ) ^ k = ((2 : ℝ) ^ k) ^ 2 := by
    calc
      (4 : ℝ) ^ k = ((2 : ℝ) ^ 2) ^ k := by norm_num
      _ = (2 : ℝ) ^ (2 * k) := by rw [pow_mul]
      _ = (2 : ℝ) ^ (k * 2) := by rw [mul_comm]
      _ = ((2 : ℝ) ^ k) ^ 2 := by rw [pow_mul]
  have ha_real : (a : ℝ) = v ^ 2 - u ^ 2 := by
    dsimp [a, u, v]
    push_cast
    rw [hpow, hpow]
  have hdiff : 0 ≤ v - u := by linarith
  have hlinear : 0 ≤ 7 * v - 13 * u := by linarith
  rw [grahamPoint_dist]
  change (1 / 10 : ℝ) < distToInt (Real.sqrt ((a : ℝ) ^ 2 + (v - u) ^ 2))
  apply sqrt_sq_add_away a ((v - u) ^ 2) ha
  · rw [ha_real]
    nlinarith [mul_nonneg hdiff hlinear]
  · rw [ha_real]
    have hprod : 0 ≤ u * (v - u) := mul_nonneg hu0 hdiff
    nlinarith

/-- The first `n` construction points fit in the disk of radius `2 * 4^n`. -/
lemma grahamPoint_mem_closedBall {m n : ℕ} (hmn : m < n) :
    grahamPoint m ∈ closedBall (grahamPoint 0) (2 * (4 : ℝ) ^ n) := by
  have hm4 : (4 : ℝ) ^ m ≤ (4 : ℝ) ^ n :=
    (pow_right_strictMono₀ (by norm_num : (1 : ℝ) < 4)).monotone hmn.le
  have h24 : (2 : ℝ) ^ m ≤ (4 : ℝ) ^ m := by
    gcongr
    norm_num
  have h2m0 : 0 ≤ (2 : ℝ) ^ m := by positivity
  have h4m0 : 0 ≤ (4 : ℝ) ^ m := by positivity
  have h4n0 : 0 ≤ (4 : ℝ) ^ n := by positivity
  have h2m1 : 1 ≤ (2 : ℝ) ^ m := one_le_pow₀ (by norm_num)
  have h4m1 : 1 ≤ (4 : ℝ) ^ m := one_le_pow₀ (by norm_num)
  have h2sq : ((2 : ℝ) ^ m - 1) ^ 2 ≤ ((4 : ℝ) ^ n) ^ 2 := by
    have hleft : 0 ≤ (4 : ℝ) ^ n - ((2 : ℝ) ^ m - 1) := by linarith
    have hright : 0 ≤ (4 : ℝ) ^ n + ((2 : ℝ) ^ m - 1) := by linarith
    nlinarith [mul_nonneg hleft hright]
  have h4sq : ((4 : ℝ) ^ m - 1) ^ 2 ≤ ((4 : ℝ) ^ n) ^ 2 := by
    have hleft : 0 ≤ (4 : ℝ) ^ n - ((4 : ℝ) ^ m - 1) := by linarith
    have hright : 0 ≤ (4 : ℝ) ^ n + ((4 : ℝ) ^ m - 1) := by linarith
    nlinarith [mul_nonneg hleft hright]
  rw [mem_closedBall, grahamPoint_dist]
  norm_num
  rw [Real.sqrt_le_iff]
  constructor
  · positivity
  · nlinarith

/-- `Realizable X δ n` says that `n` distinct indexed points fit in some
closed disk of radius `X`, with every pairwise distance at least `δ` away
from the nearest integer. -/
def Realizable (X δ : ℝ) (n : ℕ) : Prop :=
  ∃ (c : Plane) (P : Fin n → Plane), Function.Injective P ∧
    (∀ i, P i ∈ closedBall c X) ∧
    ∀ i j, i ≠ j → δ ≤ distToInt (dist (P i) (P j))

/-- The set of cardinalities of admissible configurations. -/
def admissibleSizes (X δ : ℝ) : Set ℕ := {n | Realizable X δ n}

/-- The maximum cardinality in Erdős Problem 466.  Finiteness and attainment
for positive `δ` are proved below. -/
def N (X δ : ℝ) : ℕ := sSup (admissibleSizes X δ)

lemma zero_realizable (X δ : ℝ) : Realizable X δ 0 := by
  refine ⟨0, (fun i ↦ i.elim0), ?_, ?_, ?_⟩
  · intro i
    exact i.elim0
  · intro i
    exact i.elim0
  · intro i
    exact i.elim0

lemma admissibleSizes_nonempty (X δ : ℝ) : (admissibleSizes X δ).Nonempty := by
  exact ⟨0, zero_realizable X δ⟩

/-- Compactness gives a uniform finite bound on the size of an admissible
configuration.  We translate its center to the origin and inject the points
into a fixed finite `δ/3`-net of the closed disk. -/
lemma admissibleSizes_bddAbove (X : ℝ) {δ : ℝ} (hδ : 0 < δ) :
    BddAbove (admissibleSizes X δ) := by
  obtain ⟨t, _htsub, htfin, hcover⟩ :=
    finite_cover_balls_of_compact (isCompact_closedBall (0 : Plane) X)
      (by positivity : 0 < δ / 3)
  let _ : Fintype t := htfin.fintype
  refine ⟨Fintype.card t, ?_⟩
  intro n hn
  rcases hn with ⟨c, P, hPinj, hPmem, hsep⟩
  have htranslated (i : Fin n) : P i - c ∈ closedBall (0 : Plane) X := by
    rw [mem_closedBall]
    simpa [dist_eq_norm] using hPmem i
  have hchoice (i : Fin n) : ∃ y ∈ t, dist (P i - c) y < δ / 3 := by
    rcases Set.mem_iUnion.mp (hcover (htranslated i)) with ⟨y, hy⟩
    rcases Set.mem_iUnion.mp hy with ⟨hyt, hyball⟩
    exact ⟨y, hyt, hyball⟩
  choose f hfmem hfclose using hchoice
  let g : Fin n → t := fun i ↦ ⟨f i, hfmem i⟩
  have hginj : Function.Injective g := by
    intro i j hij
    by_contra hne
    have hfij : f i = f j := congrArg Subtype.val hij
    have hdistlt : dist (P i) (P j) < δ := by
      calc
        dist (P i) (P j) = dist (P i - c) (P j - c) := by rw [dist_sub_right]
        _ ≤ dist (P i - c) (f i) + dist (f i) (P j - c) := dist_triangle ..
        _ < δ / 3 + δ / 3 := by
          apply add_lt_add (hfclose i)
          rw [dist_comm, hfij]
          exact hfclose j
        _ < δ := by linarith
    have hdistge : δ ≤ dist (P i) (P j) :=
      (hsep i j hne).trans (distToInt_le_self dist_nonneg)
    exact (not_lt_of_ge hdistge) hdistlt
  simpa using Fintype.card_le_of_injective g hginj

lemma realizable_le_N {X δ : ℝ} (hδ : 0 < δ) {n : ℕ} (hn : Realizable X δ n) :
    n ≤ N X δ := by
  exact le_csSup (admissibleSizes_bddAbove X hδ) hn

/-- Thus the supremum defining `N` is attained: it really is the maximum
number of points in the problem statement. -/
lemma N_realizable (X : ℝ) {δ : ℝ} (hδ : 0 < δ) : Realizable X δ (N X δ) := by
  exact Nat.sSup_mem (admissibleSizes_nonempty X δ) (admissibleSizes_bddAbove X hδ)

lemma Realizable.mono_radius {X Y δ : ℝ} {n : ℕ} (h : Realizable X δ n) (hXY : X ≤ Y) :
    Realizable Y δ n := by
  rcases h with ⟨c, P, hPinj, hPmem, hsep⟩
  exact ⟨c, P, hPinj, fun i ↦ closedBall_subset_closedBall hXY (hPmem i), hsep⟩

/-- Graham's first `n` points form an admissible configuration at the explicit
radius `2 * 4^n`. -/
lemma graham_realizable (n : ℕ) :
    Realizable (2 * (4 : ℝ) ^ n) (1 / 10 : ℝ) n := by
  let P : Fin n → Plane := fun i ↦ grahamPoint i
  refine ⟨grahamPoint 0, P, ?_, ?_, ?_⟩
  · intro i j hij
    exact Fin.ext (grahamPoint_injective hij)
  · intro i
    exact grahamPoint_mem_closedBall i.isLt
  · intro i j hij
    have hv : (i : ℕ) ≠ (j : ℕ) := fun h ↦ hij (Fin.ext h)
    rcases lt_or_gt_of_ne hv with hijv | hjiv
    · exact (grahamPoint_away hijv).le
    · simpa [dist_comm] using (grahamPoint_away hjiv).le

lemma graham_lower_bound (n : ℕ) :
    n ≤ N (2 * (4 : ℝ) ^ n) (1 / 10 : ℝ) := by
  exact realizable_le_N (by norm_num) (graham_realizable n)

lemma graham_lower_bound_of_radius {X : ℝ} (n : ℕ) (hX : 2 * (4 : ℝ) ^ n ≤ X) :
    n ≤ N X (1 / 10 : ℝ) := by
  exact realizable_le_N (by norm_num) ((graham_realizable n).mono_radius hX)

/-- Resolution of Erdős Problem 466: for the fixed positive separation
`δ = 1/10`, the exact maximum `N(X,δ)` tends to infinity with the radius. -/
theorem erdos_466 :
    ∃ δ : ℝ, 0 < δ ∧ Tendsto (fun X : ℝ ↦ N X δ) atTop atTop := by
  refine ⟨1 / 10, by norm_num, ?_⟩
  refine tendsto_atTop.2 fun n ↦ ?_
  filter_upwards [eventually_ge_atTop (2 * (4 : ℝ) ^ n)] with X hX
  exact graham_lower_bound_of_radius n hX

#print axioms erdos_466

end

end Erdos466

alias _root_.Erdos466.erdos466 := _root_.Erdos466.erdos_466
