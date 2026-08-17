/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

import ErdosProblems.Erdos223.Basic

/-!
# Lenz configurations for Erdős Problem 223

This file gives the lower-bound construction in every dimension `d ≥ 4`.
For `p = d / 2`, vertices are distributed by residue class among `p`
pairwise orthogonal coordinate planes.  In each plane they lie on the positive
quarter of the circle of radius `1 / √2`.  Consequently every pair in
different parts is at distance one and every pair in the same part is at
distance at most one.
-/

open scoped BigOperators

namespace Erdos223

noncomputable section

namespace Lenz

/-- The even coordinate belonging to the `i`th coordinate plane. -/
def evenIndex {d p : ℕ} (hp : 2 * p ≤ d) (i : Fin p) : Fin d :=
  ⟨2 * i, by omega⟩

/-- The odd coordinate belonging to the `i`th coordinate plane. -/
def oddIndex {d p : ℕ} (hp : 2 * p ≤ d) (i : Fin p) : Fin d :=
  ⟨2 * i + 1, by omega⟩

lemma evenIndex_injective {d p : ℕ} (hp : 2 * p ≤ d) :
    Function.Injective (evenIndex hp) := by
  intro i j hij
  have hijv := congrArg Fin.val hij
  dsimp [evenIndex] at hijv
  apply Fin.ext
  omega

lemma oddIndex_injective {d p : ℕ} (hp : 2 * p ≤ d) :
    Function.Injective (oddIndex hp) := by
  intro i j hij
  have hijv := congrArg Fin.val hij
  dsimp [oddIndex] at hijv
  apply Fin.ext
  omega

lemma evenIndex_ne_oddIndex {d p : ℕ} (hp : 2 * p ≤ d) (i j : Fin p) :
    evenIndex hp i ≠ oddIndex hp j := by
  intro hij
  have hijv := congrArg Fin.val hij
  dsimp [evenIndex, oddIndex] at hijv
  omega

lemma oddIndex_ne_evenIndex {d p : ℕ} (hp : 2 * p ≤ d) (i j : Fin p) :
    oddIndex hp i ≠ evenIndex hp j := by
  exact (evenIndex_ne_oddIndex hp j i).symm

/-- A distinct parameter in `(0,1)` attached to each vertex. -/
def parameter {n : ℕ} (v : Fin n) : ℝ := ((v : ℕ) + 1 : ℝ) / (n + 1 : ℝ)

lemma parameter_pos {n : ℕ} (v : Fin n) : 0 < parameter v := by
  unfold parameter
  positivity

lemma parameter_lt_one {n : ℕ} (v : Fin n) : parameter v < 1 := by
  unfold parameter
  rw [div_lt_one (by positivity : (0 : ℝ) < n + 1)]
  exact_mod_cast Nat.add_lt_add_right v.isLt 1

lemma parameter_nonneg {n : ℕ} (v : Fin n) : 0 ≤ parameter v := (parameter_pos v).le

lemma parameter_sq_le_one {n : ℕ} (v : Fin n) : parameter v ^ 2 ≤ 1 := by
  nlinarith [parameter_nonneg v, parameter_lt_one v]

lemma parameter_injective {n : ℕ} : Function.Injective (@parameter n) := by
  intro v w hvw
  unfold parameter at hvw
  have hn : (n + 1 : ℝ) ≠ 0 := by positivity
  field_simp [hn] at hvw
  apply Fin.ext
  have hvw' : (v : ℕ) + 1 = (w : ℕ) + 1 := by exact_mod_cast hvw
  omega

/-- First coordinate of the positive quarter-circle parametrization. -/
def firstCoordinate (t : ℝ) : ℝ := Real.sqrt ((1 - t ^ 2) / 2)

/-- Second coordinate of the positive quarter-circle parametrization. -/
def secondCoordinate (t : ℝ) : ℝ := t / Real.sqrt 2

lemma firstCoordinate_nonneg (t : ℝ) : 0 ≤ firstCoordinate t := Real.sqrt_nonneg _

lemma secondCoordinate_nonneg {t : ℝ} (ht : 0 ≤ t) : 0 ≤ secondCoordinate t := by
  unfold secondCoordinate
  positivity

lemma secondCoordinate_injective : Function.Injective secondCoordinate := by
  intro s t h
  unfold secondCoordinate at h
  have hsqrt : Real.sqrt (2 : ℝ) ≠ 0 := by positivity
  field_simp [hsqrt] at h
  exact h

lemma coordinates_sq_add {t : ℝ} (ht : t ^ 2 ≤ 1) :
    firstCoordinate t ^ 2 + secondCoordinate t ^ 2 = 1 / 2 := by
  have hrad : 0 ≤ (1 - t ^ 2) / 2 := by positivity
  have hsqrt : Real.sqrt (2 : ℝ) ^ 2 = 2 := by norm_num
  rw [firstCoordinate, Real.sq_sqrt hrad, secondCoordinate, div_pow, hsqrt]
  ring

/-- The residue class (and hence coordinate plane) assigned to a vertex. -/
def part {n p : ℕ} (hp : 0 < p) (v : Fin n) : Fin p :=
  ⟨v % p, Nat.mod_lt _ hp⟩

@[simp] lemma part_val {n p : ℕ} (hp : 0 < p) (v : Fin n) :
    (part hp v : ℕ) = v % p := rfl

lemma part_ne_iff {n p : ℕ} (hp : 0 < p) (v w : Fin n) :
    part hp v ≠ part hp w ↔ v % p ≠ w % p := by
  simp [part, Fin.ext_iff]

/-- The point on the positive quarter-circle assigned to a vertex. -/
def point {d n p : ℕ} (hdp : 2 * p ≤ d) (hp : 0 < p) (v : Fin n) :
    EuclideanSpace ℝ (Fin d) :=
  EuclideanSpace.single (evenIndex hdp (part hp v)) (firstCoordinate (parameter v)) +
    EuclideanSpace.single (oddIndex hdp (part hp v)) (secondCoordinate (parameter v))

lemma point_apply_even {d n p : ℕ} (hdp : 2 * p ≤ d) (hp : 0 < p)
    (v : Fin n) :
    point hdp hp v (evenIndex hdp (part hp v)) = firstCoordinate (parameter v) := by
  simp [point, evenIndex_ne_oddIndex]

lemma point_apply_odd {d n p : ℕ} (hdp : 2 * p ≤ d) (hp : 0 < p)
    (v : Fin n) :
    point hdp hp v (oddIndex hdp (part hp v)) = secondCoordinate (parameter v) := by
  simp [point, oddIndex_ne_evenIndex]

lemma inner_point_point_same_part {d n p : ℕ} (hdp : 2 * p ≤ d) (hp : 0 < p)
    {v w : Fin n} (hpart : part hp v = part hp w) :
    inner ℝ (point hdp hp v) (point hdp hp w) =
      firstCoordinate (parameter v) * firstCoordinate (parameter w) +
        secondCoordinate (parameter v) * secondCoordinate (parameter w) := by
  simp [point, hpart, inner_add_left, inner_add_right,
    EuclideanSpace.inner_single_left,
    evenIndex_ne_oddIndex, oddIndex_ne_evenIndex]

lemma inner_point_point_of_ne_part {d n p : ℕ} (hdp : 2 * p ≤ d) (hp : 0 < p)
    {v w : Fin n} (hpart : part hp v ≠ part hp w) :
    inner ℝ (point hdp hp v) (point hdp hp w) = 0 := by
  have hee : evenIndex hdp (part hp v) ≠ evenIndex hdp (part hp w) :=
    fun h ↦ hpart (evenIndex_injective hdp h)
  have hoo : oddIndex hdp (part hp v) ≠ oddIndex hdp (part hp w) :=
    fun h ↦ hpart (oddIndex_injective hdp h)
  simp [point, inner_add_left, inner_add_right, EuclideanSpace.inner_single_left,
    hee, hoo, evenIndex_ne_oddIndex, oddIndex_ne_evenIndex]

lemma inner_point_self {d n p : ℕ} (hdp : 2 * p ≤ d) (hp : 0 < p) (v : Fin n) :
    inner ℝ (point hdp hp v) (point hdp hp v) = 1 / 2 := by
  rw [inner_point_point_same_part hdp hp rfl]
  simpa [pow_two] using coordinates_sq_add (parameter_sq_le_one v)

lemma norm_point_sq {d n p : ℕ} (hdp : 2 * p ≤ d) (hp : 0 < p) (v : Fin n) :
    ‖point hdp hp v‖ ^ 2 = 1 / 2 := by
  rw [← real_inner_self_eq_norm_sq]
  exact inner_point_self hdp hp v

lemma dist_point_sq {d n p : ℕ} (hdp : 2 * p ≤ d) (hp : 0 < p) (v w : Fin n) :
    dist (point hdp hp v) (point hdp hp w) ^ 2 =
      1 - 2 * inner ℝ (point hdp hp v) (point hdp hp w) := by
  rw [dist_eq_norm, ← real_inner_self_eq_norm_sq]
  simp only [inner_sub_left, inner_sub_right]
  rw [inner_point_self hdp hp v, inner_point_self hdp hp w]
  have hsymm : inner ℝ (point hdp hp w) (point hdp hp v) =
      inner ℝ (point hdp hp v) (point hdp hp w) := real_inner_comm _ _
  rw [hsymm]
  ring

lemma inner_point_point_nonneg {d n p : ℕ} (hdp : 2 * p ≤ d) (hp : 0 < p)
    (v w : Fin n) : 0 ≤ inner ℝ (point hdp hp v) (point hdp hp w) := by
  by_cases hpart : part hp v = part hp w
  · rw [inner_point_point_same_part hdp hp hpart]
    exact add_nonneg
      (mul_nonneg (firstCoordinate_nonneg _) (firstCoordinate_nonneg _))
      (mul_nonneg (secondCoordinate_nonneg (parameter_nonneg _))
        (secondCoordinate_nonneg (parameter_nonneg _)))
  · rw [inner_point_point_of_ne_part hdp hp hpart]

lemma dist_point_le_one {d n p : ℕ} (hdp : 2 * p ≤ d) (hp : 0 < p) (v w : Fin n) :
    dist (point hdp hp v) (point hdp hp w) ≤ 1 := by
  have hsq := dist_point_sq hdp hp v w
  have hi := inner_point_point_nonneg hdp hp v w
  have hd : 0 ≤ dist (point hdp hp v) (point hdp hp w) := dist_nonneg
  nlinarith

lemma dist_point_eq_one_of_ne_part {d n p : ℕ} (hdp : 2 * p ≤ d) (hp : 0 < p)
    {v w : Fin n} (hpart : part hp v ≠ part hp w) :
    dist (point hdp hp v) (point hdp hp w) = 1 := by
  have hsq := dist_point_sq hdp hp v w
  rw [inner_point_point_of_ne_part hdp hp hpart] at hsq
  have hd : 0 ≤ dist (point hdp hp v) (point hdp hp w) := dist_nonneg
  nlinarith

lemma dist_point_eq_one_of_turanGraph_adj {d n p : ℕ} (hdp : 2 * p ≤ d) (hp : 0 < p)
    {v w : Fin n} (hvw : (SimpleGraph.turanGraph n p).Adj v w) :
    dist (point hdp hp v) (point hdp hp w) = 1 := by
  apply dist_point_eq_one_of_ne_part hdp hp
  rw [part_ne_iff hp]
  exact hvw

lemma point_injective {d n p : ℕ} (hdp : 2 * p ≤ d) (hp : 0 < p) :
    Function.Injective (@point d n p hdp hp) := by
  intro v w hvw
  have hinner : inner ℝ (point hdp hp v) (point hdp hp w) = 1 / 2 := by
    rw [hvw]
    exact inner_point_self hdp hp w
  have hpart : part hp v = part hp w := by
    by_contra hne
    rw [inner_point_point_of_ne_part hdp hp hne] at hinner
    norm_num at hinner
  have hcoord := congrArg
    (fun z : EuclideanSpace ℝ (Fin d) ↦ z (oddIndex hdp (part hp v))) hvw
  rw [point_apply_odd hdp hp v] at hcoord
  rw [hpart, point_apply_odd hdp hp w] at hcoord
  exact parameter_injective (secondCoordinate_injective hcoord)

/-- The finite Lenz configuration indexed by `Fin n`. -/
def configuration {d n p : ℕ} (hdp : 2 * p ≤ d) (hp : 0 < p) :
    Finset (EuclideanSpace ℝ (Fin d)) :=
  Finset.univ.image (fun v : Fin n ↦ point hdp hp v)

lemma card_configuration {d n p : ℕ} (hdp : 2 * p ≤ d) (hp : 0 < p) :
    (configuration (n := n) hdp hp).card = n := by
  rw [configuration,
    Finset.card_image_iff.mpr (point_injective hdp hp).injOn]
  simp

lemma mem_configuration {d n p : ℕ} (hdp : 2 * p ≤ d) (hp : 0 < p)
    (v : Fin n) : point hdp hp v ∈ configuration (n := n) hdp hp := by
  simp [configuration]

lemma configuration_pairwise_dist_le_one {d n p : ℕ} (hdp : 2 * p ≤ d) (hp : 0 < p) :
    ∀ x ∈ configuration (n := n) hdp hp,
      ∀ y ∈ configuration (n := n) hdp hp, dist x y ≤ 1 := by
  simp only [configuration, Finset.mem_image, Finset.mem_univ, true_and]
  rintro x ⟨v, rfl⟩ y ⟨w, rfl⟩
  exact dist_point_le_one hdp hp v w

lemma isDiameterOne_configuration {d n p : ℕ} (hdp : 2 * p ≤ d) (hp : 0 < p)
    (hp2 : 2 ≤ p) (hn : 2 ≤ n) : IsDiameterOne (configuration (n := n) hdp hp) := by
  rw [isDiameterOne_iff]
  refine ⟨configuration_pairwise_dist_le_one hdp hp, ?_⟩
  let v : Fin n := ⟨0, by omega⟩
  let w : Fin n := ⟨1, by omega⟩
  refine ⟨point hdp hp v, mem_configuration hdp hp v,
    point hdp hp w, mem_configuration hdp hp w, ?_⟩
  apply dist_point_eq_one_of_ne_part hdp hp
  rw [part_ne_iff hp]
  dsimp [v, w]
  rw [Nat.mod_eq_of_lt (by omega : 1 < p)]
  norm_num

/-- The embedding of the Turán graph's vertices into the Lenz configuration. -/
def vertexEmbedding {d n p : ℕ} (hdp : 2 * p ≤ d) (hp : 0 < p) :
    Fin n ↪ {x // x ∈ configuration (n := n) hdp hp} where
  toFun v := ⟨point hdp hp v, mem_configuration hdp hp v⟩
  inj' _ _ h := point_injective hdp hp (Subtype.ext_iff.mp h)

lemma map_turanGraph_le_diameterGraph {d n p : ℕ} (hdp : 2 * p ≤ d) (hp : 0 < p) :
    (SimpleGraph.turanGraph n p).map (vertexEmbedding hdp hp) ≤
      diameterGraph (configuration (n := n) hdp hp) := by
  intro x y hxy
  rw [SimpleGraph.map_adj] at hxy
  obtain ⟨v, w, hvw, rfl, rfl⟩ := hxy
  exact dist_point_eq_one_of_turanGraph_adj hdp hp hvw

/-- Every edge of the balanced `p`-partite Turán graph occurs as a unit
distance in the Lenz configuration. -/
lemma card_edgeFinset_turanGraph_le_diameterPairCount {d n p : ℕ}
    (hdp : 2 * p ≤ d) (hp : 0 < p) :
    (SimpleGraph.turanGraph n p).edgeFinset.card ≤
      diameterPairCount (configuration (n := n) hdp hp) := by
  rw [diameterPairCount]
  refine Finset.card_le_card_of_injOn
    (Sym2.map (vertexEmbedding hdp hp)) ?_
    (Sym2.map.injective (vertexEmbedding hdp hp).injective).injOn
  intro e he
  have he' : e ∈ (SimpleGraph.turanGraph n p).edgeSet := by
    simpa only [SimpleGraph.coe_edgeFinset] using he
  have hmap : Sym2.map (vertexEmbedding hdp hp) e ∈
      ((SimpleGraph.turanGraph n p).map (vertexEmbedding hdp hp)).edgeSet := by
    rw [SimpleGraph.edgeSet_map]
    exact ⟨e, he', rfl⟩
  have htarget : Sym2.map (vertexEmbedding hdp hp) e ∈
      (diameterGraph (configuration (n := n) hdp hp)).edgeSet :=
    SimpleGraph.edgeSet_mono (map_turanGraph_le_diameterGraph hdp hp) hmap
  simpa only [SimpleGraph.coe_edgeFinset] using htarget

/-- The Lenz construction realizes at least the balanced Turán number in
every dimension at least four. -/
theorem turanNumber_le_f {d n : ℕ} (hd : 4 ≤ d) (hn : 2 ≤ n) :
    (SimpleGraph.turanGraph n (d / 2)).edgeFinset.card ≤ f d n := by
  have hdp : 2 * (d / 2) ≤ d := by
    have h := Nat.div_mul_le_self d 2
    omega
  have hp : 0 < d / 2 := by omega
  have hp2 : 2 ≤ d / 2 := by omega
  apply (card_edgeFinset_turanGraph_le_diameterPairCount hdp hp).trans
  exact diameterPairCount_le_f
    (card_configuration hdp hp)
    (isDiameterOne_configuration hdp hp hp2 hn)

end Lenz

end

end Erdos223
