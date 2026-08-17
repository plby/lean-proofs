/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

import ErdosProblems.Erdos223.Basic
import ErdosProblems.Erdos223.SphericalEuler.Combinatorial
import ErdosProblems.Erdos223.SphericalEuler.Crosscut
import Mathlib.Combinatorics.SimpleGraph.Bipartite
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Finite
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Analysis.Convex.PathConnected
import Mathlib.Analysis.Normed.Module.Normalize
import Mathlib.Geometry.Convex.Cone.Pointed
import Mathlib.GroupTheory.Perm.Cycle.Type
import Mathlib.Tactic

/-!
# Spherical Euler certificates

This file contains the finite combinatorial part of the spherical double-cover
argument used in the three-dimensional case of Erdős Problem 223.

A rotation of the darts of a graph, together with its edge-reversal
involution, determines the face permutation.  A `SphereRotationCertificate`
records the two substantive properties of a cellular drawing on a sphere:

* all darts belong to a face boundary and every face has the asserted minimum
  length;
* the Euler equality, summed over the connected components.

The main result below is deliberately independent of geometry.  It converts a
certificate for the bipartite double cover of a finite graph into the sharp
linear edge bound needed by the Vázsonyi argument.  Thus the geometric part of
the proof can construct one finite object and leave all counting to this file.
-/

open scoped BigOperators

namespace SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Reversal of an oriented edge, regarded as a permutation of the darts. -/
noncomputable def dartFlip (G : SimpleGraph V) : Equiv.Perm G.Dart where
  toFun := Dart.symm
  invFun := Dart.symm
  left_inv := Dart.symm_symm
  right_inv := Dart.symm_symm

/-- The face permutation associated to a cyclic rotation of the darts at the
vertices.  Our convention first reverses a dart and then applies the rotation. -/
noncomputable def facePerm (G : SimpleGraph V) (rotation : Equiv.Perm G.Dart) :
    Equiv.Perm G.Dart :=
  rotation * dartFlip G

/-- The finite data from a cellular spherical rotation system used by the
Euler count.  `face_support` rules out one-cycles that are omitted by
`Equiv.Perm.cycleType`; `face_cycle_ge_four` is the bipartite face-length
  condition.  The last field is the sum of the spherical Euler equalities for
the connected components.  Notice that `cycleType.card` counts boundary
cycles, not connected components of the complement; this distinction matters
for a disconnected graph. -/
structure SphereRotationCertificate (G : SimpleGraph V) [DecidableRel G.Adj] where
  rotation : Equiv.Perm G.Dart
  face_support : (facePerm G rotation).support = Finset.univ
  face_cycle_ge_four : ∀ k ∈ (facePerm G rotation).cycleType, 4 ≤ k
  euler :
    Fintype.card V + (facePerm G rotation).cycleType.card =
      G.edgeFinset.card + 2 * Fintype.card G.ConnectedComponent

private theorem four_mul_card_le_sum {s : Multiset ℕ}
    (h : ∀ k ∈ s, 4 ≤ k) : 4 * s.card ≤ s.sum := by
  induction s using Multiset.induction_on with
  | empty => simp
  | @cons a s ih =>
      simp only [Multiset.card_cons, Multiset.sum_cons, mul_add]
      have ha := h a (by simp)
      have hs := ih fun k hk ↦ h k (by simp [hk])
      omega

/-- Euler's equality and face length at least four imply the usual sharp
bipartite spherical bound `E + 4 ≤ 2 V`. -/
theorem SphereRotationCertificate.edge_add_four_le_two_mul_vertex
    {G : SimpleGraph V} [DecidableRel G.Adj] [Nonempty V]
    (C : SphereRotationCertificate G) :
    G.edgeFinset.card + 4 ≤ 2 * Fintype.card V := by
  have hface :
      4 * (facePerm G C.rotation).cycleType.card ≤ 2 * G.edgeFinset.card := by
    refine (four_mul_card_le_sum C.face_cycle_ge_four).trans_eq ?_
    rw [Equiv.Perm.sum_cycleType, C.face_support, Finset.card_univ,
      dart_card_eq_twice_card_edges]
  have heuler := C.euler
  have hcomponent : 0 < Fintype.card G.ConnectedComponent := Fintype.card_pos
  omega

/-- A spherical certificate for the canonical bipartite double cover of `G`
implies `E(G) + 2 ≤ 2 V(G)`.  The factor two is discharged using Mathlib's
exact edge and vertex counts for the double cover. -/
theorem edge_add_two_le_two_mul_vertex_of_doubleCover_certificate
    {G : SimpleGraph V} [DecidableRel G.Adj] [Nonempty V]
    (C : SphereRotationCertificate G.bipartiteDoubleCover) :
    G.edgeFinset.card + 2 ≤ 2 * Fintype.card V := by
  have h := C.edge_add_four_le_two_mul_vertex
  rw [card_edgeFinset_bipartiteDoubleCover] at h
  simp only [Fintype.card_sum] at h
  omega

end SimpleGraph

/-! ## Swanepoel's spherical cone regions -/

open scoped RealInnerProductSpace

namespace Erdos223.SphericalEuler

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

private lemma norm_sub_sq (a b : E) :
    ‖a - b‖ ^ 2 = ‖a‖ ^ 2 + ‖b‖ ^ 2 - 2 * inner ℝ a b := by
  rw [← real_inner_self_eq_norm_sq]
  simp only [inner_sub_left, inner_sub_right]
  rw [real_inner_comm b a, real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq]
  ring

/-- Diameter-neighbour directions based at the same point make an angle of at
most sixty degrees.  This quantitative positivity is what keeps normalized
segments in a cone star away from the origin. -/
theorem inner_neighborDirections_ge_half
    {d : ℕ} {A : Finset (Point d)} (hA : IsDiameterOne A)
    {x y z : {w // w ∈ A}}
    (hxy : (diameterGraph A).Adj x y)
    (hxz : (diameterGraph A).Adj x z) :
    (1 / 2 : ℝ) ≤ inner ℝ ((y : Point d) - (x : Point d))
      ((z : Point d) - (x : Point d)) := by
  let u : Point d := (y : Point d) - (x : Point d)
  let v : Point d := (z : Point d) - (x : Point d)
  have hu : ‖u‖ = 1 := by
    have hdist := (diameterGraph_adj A x y).mp hxy
    simpa [u, dist_eq_norm, norm_sub_rev] using hdist
  have hv : ‖v‖ = 1 := by
    have hdist := (diameterGraph_adj A x z).mp hxz
    simpa [v, dist_eq_norm, norm_sub_rev] using hdist
  have huv : ‖u - v‖ ≤ 1 := by
    have hdist := hA.dist_le y.prop z.prop
    have heq : u - v = (y : Point d) - (z : Point d) := by
      simp only [u, v]
      abel
    rw [heq]
    simpa [dist_eq_norm] using hdist
  have huv_sq : ‖u - v‖ ^ 2 ≤ 1 := by
    nlinarith [norm_nonneg (u - v)]
  have hsq := norm_sub_sq_real u v
  rw [hu, hv] at hsq
  change (1 / 2 : ℝ) ≤ inner ℝ u v
  nlinarith

/-- Swanepoel's cone lemma, stated directly using `PointedCone.hull`. -/
theorem norm_sub_le_one_of_mem_pointedCone_hull
    {s : Set E} {u y : E}
    (hs : ∀ x ∈ s, ‖x‖ = 1)
    (hu : u ∈ PointedCone.hull ℝ s)
    (hunit : ‖u‖ = 1)
    (hy : ∀ x ∈ s, ‖y - x‖ ≤ 1) :
    ‖y - u‖ ≤ 1 := by
  rw [PointedCone.mem_hull_set] at hu
  obtain ⟨c, hcs, hc0, hsum⟩ := hu
  let L : ℝ := ∑ x ∈ c.support, c x
  have hc_norm (x : E) (hx : x ∈ c.support) : ‖c x • x‖ = c x := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (hc0 x), hs x (hcs hx), mul_one]
  have hL : 1 ≤ L := by
    rw [← hunit, ← hsum]
    calc
      ‖c.sum (fun x a ↦ a • x)‖ ≤ ∑ x ∈ c.support, ‖c x • x‖ := by
        simpa [Finsupp.sum] using norm_sum_le c.support fun x ↦ c x • x
      _ = L := by
        apply Finset.sum_congr rfl
        intro x hx
        exact hc_norm x hx
  have hgen (x : E) (hx : x ∈ c.support) :
      ‖y‖ ^ 2 ≤ 2 * inner ℝ x y := by
    have hdist := hy x (hcs hx)
    have hdist0 : 0 ≤ ‖y - x‖ := norm_nonneg _
    have hdistSq : ‖y - x‖ ^ 2 ≤ 1 := by nlinarith
    rw [norm_sub_sq, hs x (hcs hx)] at hdistSq
    rw [real_inner_comm y x]
    nlinarith
  have hweighted : L * ‖y‖ ^ 2 ≤ 2 * inner ℝ u y := by
    have hterm : ∀ x ∈ c.support,
        c x * ‖y‖ ^ 2 ≤ c x * (2 * inner ℝ x y) := by
      intro x hx
      exact mul_le_mul_of_nonneg_left (hgen x hx) (hc0 x)
    have hsumle := Finset.sum_le_sum hterm
    have hinner :
        inner ℝ u y = ∑ x ∈ c.support, c x * inner ℝ x y := by
      rw [← hsum]
      simp [Finsupp.sum, sum_inner, inner_smul_left]
    calc
      L * ‖y‖ ^ 2 = ∑ x ∈ c.support, c x * ‖y‖ ^ 2 := by
        simp [L, Finset.sum_mul]
      _ ≤ ∑ x ∈ c.support, c x * (2 * inner ℝ x y) := hsumle
      _ = 2 * inner ℝ u y := by
        rw [hinner, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro x hx
        ring
  have hsq : ‖y - u‖ ^ 2 ≤ 1 := by
    rw [norm_sub_sq, hunit]
    rw [show inner ℝ y u = inner ℝ u y by exact real_inner_comm _ _]
    have hynonneg : 0 ≤ ‖y‖ ^ 2 := sq_nonneg _
    norm_num
    nlinarith
  have hnorm : 0 ≤ ‖y - u‖ := norm_nonneg _
  nlinarith

private theorem eq_zero_of_norm_add_le_one_of_norm_sub_le_one
    {z u : E} (hu : ‖u‖ = 1)
    (hadd : ‖z + u‖ ≤ 1) (hsub : ‖z - u‖ ≤ 1) :
    z = 0 := by
  have hadd_sq : ‖z + u‖ ^ 2 ≤ 1 := by
    nlinarith [norm_nonneg (z + u)]
  have hsub_sq : ‖z - u‖ ^ 2 ≤ 1 := by
    nlinarith [norm_nonneg (z - u)]
  have hpara := parallelogram_law_with_norm ℝ z u
  rw [hu] at hpara
  have hz : ‖z‖ = 0 := by
    nlinarith [sq_nonneg ‖z‖]
  exact norm_eq_zero.mp hz

private theorem eq_neg_of_norm_le_one_of_norm_add_two_le_one
    {z u : E} (hu : ‖u‖ = 1)
    (hz : ‖z‖ ≤ 1) (hadd : ‖z + 2 • u‖ ≤ 1) :
    z = -u := by
  have hz_sq : ‖z‖ ^ 2 ≤ 1 := by
    nlinarith [norm_nonneg z]
  have hadd_sq : ‖z + 2 • u‖ ^ 2 ≤ 1 := by
    nlinarith [norm_nonneg (z + 2 • u)]
  have hpara := parallelogram_law_with_norm ℝ (z + u) u
  have hplus : (z + u) + u = z + 2 • u := by
    simp only [two_smul]
    abel
  have hminus : (z + u) - u = z := by abel
  rw [hplus, hminus, hu] at hpara
  have hmid : ‖z + u‖ = 0 := by
    nlinarith [sq_nonneg ‖z + u‖]
  exact add_eq_zero_iff_eq_neg.mp (norm_eq_zero.mp hmid)

/-- Unit directions from `x` to its diameter-one neighbours in `A`. -/
def diameterDirections (A : Set E) (x : E) : Set E :=
  {v | ∃ a ∈ A, ‖a - x‖ = 1 ∧ v = a - x}

/-- The unit-sphere section of the nonnegative cone generated by the diameter
directions at `x`. -/
def diameterConeRegion (A : Set E) (x : E) : Set E :=
  {u | ‖u‖ = 1 ∧ u ∈ PointedCone.hull ℝ (diameterDirections A x)}

omit [InnerProductSpace ℝ E] in
lemma norm_eq_one_of_mem_diameterDirections
    {A : Set E} {x v : E} (hv : v ∈ diameterDirections A x) :
    ‖v‖ = 1 := by
  obtain ⟨a, ha, hav, rfl⟩ := hv
  exact hav

/-- A region point at `x` inherits the diameter bound from every point of
`A`, after translating the test point by `x`. -/
lemma norm_sub_region_le_one
    {A : Set E} {x u a : E}
    (ha : a ∈ A)
    (hdiam : ∀ p ∈ A, ∀ q ∈ A, ‖p - q‖ ≤ 1)
    (hu : u ∈ diameterConeRegion A x) :
    ‖(a - x) - u‖ ≤ 1 := by
  apply norm_sub_le_one_of_mem_pointedCone_hull
      (fun v hv ↦ norm_eq_one_of_mem_diameterDirections hv) hu.2 hu.1
  intro v hv
  obtain ⟨b, hb, hbunit, rfl⟩ := hv
  have hab := hdiam a ha b hb
  have heq : (a - x) - (b - x) = a - b := by abel
  rw [heq]
  exact hab

/-- Same-colour spherical cone regions based at distinct points are disjoint. -/
theorem eq_of_mem_two_diameterConeRegions
    {A : Set E} {x y u : E}
    (hx : x ∈ A) (hy : y ∈ A)
    (hdiam : ∀ p ∈ A, ∀ q ∈ A, ‖p - q‖ ≤ 1)
    (hux : u ∈ diameterConeRegion A x)
    (huy : u ∈ diameterConeRegion A y) :
    x = y := by
  have hxbound := norm_sub_region_le_one hx hdiam huy
  have hybound := norm_sub_region_le_one hy hdiam hux
  have hadd : ‖(x - y) + u‖ ≤ 1 := by
    have heq : (x - y) + u = -((y - x) - u) := by abel
    rw [heq, norm_neg]
    exact hybound
  have hsub : ‖(x - y) - u‖ ≤ 1 := hxbound
  have hz : x - y = 0 :=
    eq_zero_of_norm_add_le_one_of_norm_sub_le_one hux.1 hadd hsub
  exact sub_eq_zero.mp hz

theorem diameterConeRegions_disjoint
    {A : Set E} {x y : E}
    (hx : x ∈ A) (hy : y ∈ A) (hxy : x ≠ y)
    (hdiam : ∀ p ∈ A, ∀ q ∈ A, ‖p - q‖ ≤ 1) :
    Disjoint (diameterConeRegion A x) (diameterConeRegion A y) := by
  rw [Set.disjoint_left]
  intro u hux huy
  exact hxy (eq_of_mem_two_diameterConeRegions hx hy hdiam hux huy)

private lemma norm_shift_sub_direction_le_one
    {A : Set E} {x y u v : E}
    (hdiam : ∀ p ∈ A, ∀ q ∈ A, ‖p - q‖ ≤ 1)
    (hux : u ∈ diameterConeRegion A x)
    (hv : v ∈ diameterDirections A y) :
    ‖(x + u - y) - v‖ ≤ 1 := by
  obtain ⟨b, hb, hbunit, rfl⟩ := hv
  have hbnd := norm_sub_region_le_one hb hdiam hux
  have hbnd' : ‖x + u - b‖ ≤ 1 := by
    have heq : x + u - b = -(b - x - u) := by abel
    rw [heq, norm_neg]
    exact hbnd
  have heq : (x + u - y) - (b - y) = x + u - b := by abel
  rw [heq]
  exact hbnd'

/-- If a unit vector lies in the region at `x` and its negative lies in the
region at `y`, then it is exactly the direction `y - x`. -/
theorem eq_direction_of_mem_region_and_neg_mem_region
    {A : Set E} {x y u : E}
    (hx : x ∈ A) (hy : y ∈ A)
    (hdiam : ∀ p ∈ A, ∀ q ∈ A, ‖p - q‖ ≤ 1)
    (hux : u ∈ diameterConeRegion A x)
    (hnuy : -u ∈ diameterConeRegion A y) :
    u = y - x ∧ ‖x - y‖ = 1 := by
  have htwo : ‖(x - y) + 2 • u‖ ≤ 1 := by
    have hcone := norm_sub_le_one_of_mem_pointedCone_hull
      (s := diameterDirections A y) (u := -u) (y := x + u - y)
      (fun v hv ↦ norm_eq_one_of_mem_diameterDirections hv) hnuy.2 hnuy.1
      (fun v hv ↦ norm_shift_sub_direction_le_one hdiam hux hv)
    have heq : (x - y) + 2 • u = (x + u - y) - (-u) := by
      simp only [two_smul]
      abel
    rw [heq]
    exact hcone
  have hxy_le : ‖x - y‖ ≤ 1 := hdiam x hx y hy
  have hz : x - y = -u :=
    eq_neg_of_norm_le_one_of_norm_add_two_le_one hux.1 hxy_le htwo
  constructor
  · calc
      u = -(-u) := by simp
      _ = -(x - y) := congrArg Neg.neg hz.symm
      _ = y - x := neg_sub x y
  · rw [hz, norm_neg, hux.1]

/-- Exact singleton form of the opposite-colour intersection lemma. -/
theorem diameterConeRegion_inter_neg_eq_singleton
    {A : Set E} {x y : E}
    (hx : x ∈ A) (hy : y ∈ A)
    (hdiam : ∀ p ∈ A, ∀ q ∈ A, ‖p - q‖ ≤ 1)
    (hne : (diameterConeRegion A x ∩ -diameterConeRegion A y).Nonempty) :
    ‖x - y‖ = 1 ∧
      diameterConeRegion A x ∩ -diameterConeRegion A y = {y - x} := by
  obtain ⟨u, hux, huy⟩ := hne
  have hnuy : -u ∈ diameterConeRegion A y := by
    simpa only [Set.mem_neg, neg_neg] using huy
  obtain ⟨hu, hxy⟩ :=
    eq_direction_of_mem_region_and_neg_mem_region hx hy hdiam hux hnuy
  refine ⟨hxy, Set.Subset.antisymm ?_ ?_⟩
  · intro v hv
    obtain ⟨hvx, hvy⟩ := hv
    have hnvy : -v ∈ diameterConeRegion A y := by
      simpa only [Set.mem_neg, neg_neg] using hvy
    have hvdir :=
      (eq_direction_of_mem_region_and_neg_mem_region hx hy hdiam hvx hnvy).1
    exact Set.mem_singleton_iff.mpr hvdir
  · intro v hv
    rw [Set.mem_singleton_iff] at hv
    subst v
    exact ⟨by simpa [hu] using hux, by simpa [hu] using huy⟩


/-! ## Explicit short spherical arcs -/

open unitInterval

/-- The unnormalized chord underlying the short spherical arc. -/
def chordPoint (a b : E) (t : I) : E :=
  (1 - (t : ℝ)) • a + (t : ℝ) • b

lemma chordPoint_eq_segment (a b : E) (t : I) :
    chordPoint a b t = Path.segment a b t := by
  simp only [chordPoint, Path.segment_apply, AffineMap.lineMap_apply_module]

@[simp] lemma chordPoint_zero (a b : E) : chordPoint a b 0 = a := by
  simp [chordPoint]

@[simp] lemma chordPoint_one (a b : E) : chordPoint a b 1 = b := by
  simp [chordPoint]

/-- A positive inner product is a convenient, strong certificate that the
short chord does not pass through the origin. -/
lemma chordPoint_ne_zero_of_inner_pos
    {a b : E} (ha : ‖a‖ = 1) (hab : 0 < inner ℝ a b) (t : I) :
    chordPoint a b t ≠ 0 := by
  intro hzero
  have hinner := congrArg (inner ℝ a) hzero
  have haa : inner ℝ a a = 1 := by
    rw [real_inner_self_eq_norm_sq, ha]
    norm_num
  simp only [chordPoint, inner_add_right, inner_smul_right, haa, inner_zero_right] at hinner
  have ht0 : 0 ≤ (t : ℝ) := t.2.1
  have ht1 : (t : ℝ) ≤ 1 := t.2.2
  by_cases ht : (t : ℝ) = 1
  · rw [ht] at hinner
    nlinarith
  · have htlt : (t : ℝ) < 1 := lt_of_le_of_ne ht1 ht
    have hfirst : 0 < 1 - (t : ℝ) := sub_pos.mpr htlt
    have hsecond : 0 ≤ (t : ℝ) * inner ℝ a b := mul_nonneg ht0 hab.le
    nlinarith

/-- Normalization is continuous along any chord which avoids zero. -/
private lemma continuous_normalize_chord
    {a b : E} (hne : ∀ t : I, chordPoint a b t ≠ 0) :
    Continuous (fun t : I ↦ NormedSpace.normalize (chordPoint a b t)) := by
  rw [show (fun t : I ↦ NormedSpace.normalize (chordPoint a b t)) =
      fun t : I ↦ ‖chordPoint a b t‖⁻¹ • chordPoint a b t by
    funext t
    rfl]
  have hchord : Continuous (chordPoint a b) := by
    unfold chordPoint
    fun_prop
  exact hchord.norm.inv₀ (fun t ↦ norm_ne_zero_iff.mpr (hne t)) |>.smul hchord

/-- The normalized positive-linear-combination arc from `a` to `b`.
The positivity hypothesis selects the short arc and proves it never meets
the normalization singularity at zero. -/
noncomputable def shortSphereArc (a b : E)
    (ha : ‖a‖ = 1) (hb : ‖b‖ = 1) (hab : 0 < inner ℝ a b) :
    Path a b where
  toFun t := NormedSpace.normalize (chordPoint a b t)
  continuous_toFun :=
    continuous_normalize_chord (chordPoint_ne_zero_of_inner_pos ha hab)
  source' := by simp [NormedSpace.normalize_eq_self_of_norm_eq_one ha]
  target' := by simp [NormedSpace.normalize_eq_self_of_norm_eq_one hb]

@[simp] lemma shortSphereArc_apply (a b : E)
    (ha : ‖a‖ = 1) (hb : ‖b‖ = 1) (hab : 0 < inner ℝ a b) (t : I) :
    shortSphereArc a b ha hb hab t =
      NormedSpace.normalize (chordPoint a b t) := rfl

lemma norm_shortSphereArc (a b : E)
    (ha : ‖a‖ = 1) (hb : ‖b‖ = 1) (hab : 0 < inner ℝ a b) (t : I) :
    ‖shortSphereArc a b ha hb hab t‖ = 1 := by
  exact NormedSpace.norm_normalize (chordPoint_ne_zero_of_inner_pos ha hab t)

/-- Every point of the normalized chord remains in the same pointed cone. -/
lemma shortSphereArc_mem_pointedCone
    {C : PointedCone ℝ E} {a b : E}
    (ha : ‖a‖ = 1) (hb : ‖b‖ = 1) (hab : 0 < inner ℝ a b)
    (haC : a ∈ C) (hbC : b ∈ C) (t : I) :
    shortSphereArc a b ha hb hab t ∈ C := by
  have hraw : chordPoint a b t ∈ C := by
    apply C.add_mem
    · exact C.smul_mem (sub_nonneg.mpr t.2.2) haC
    · exact C.smul_mem t.2.1 hbC
  rw [shortSphereArc_apply, NormedSpace.normalize]
  exact C.smul_mem (inv_nonneg.mpr (norm_nonneg _)) hraw

/-- In particular, a short arc between two points of a diameter cone region
stays entirely in that region. -/
lemma shortSphereArc_mem_diameterConeRegion
    {A : Set E} {x a b : E}
    (ha : a ∈ diameterConeRegion A x)
    (hb : b ∈ diameterConeRegion A x)
    (hab : 0 < inner ℝ a b) (t : I) :
    shortSphereArc a b ha.1 hb.1 hab t ∈ diameterConeRegion A x := by
  exact ⟨norm_shortSphereArc a b ha.1 hb.1 hab t,
    shortSphereArc_mem_pointedCone ha.1 hb.1 hab ha.2 hb.2 t⟩

/-! ## Perspective arcs with exact intersection control -/

/-- Perspective projection from the strict open `w`-hemisphere to the
affine section `inner w x = 1`. -/
noncomputable def hemisphereProject (w x : E) : E :=
  (inner ℝ w x)⁻¹ • x

lemma inner_hemisphereProject_eq_one
    {w x : E} (hx : 0 < inner ℝ w x) :
    inner ℝ w (hemisphereProject w x) = 1 := by
  rw [hemisphereProject, inner_smul_right]
  exact inv_mul_cancel₀ hx.ne'

lemma normalize_hemisphereProject
    {w x : E} (hx : 0 < inner ℝ w x) :
    NormedSpace.normalize (hemisphereProject w x) =
      NormedSpace.normalize x := by
  exact NormedSpace.normalize_smul_of_pos (inv_pos.mpr hx) x

lemma hemisphereProject_ne_of_unit_ne
    {w x y : E}
    (hxpos : 0 < inner ℝ w x) (hypos : 0 < inner ℝ w y)
    (hxunit : ‖x‖ = 1) (hyunit : ‖y‖ = 1) (hxy : x ≠ y) :
    hemisphereProject w x ≠ hemisphereProject w y := by
  intro hproj
  have hnorm : NormedSpace.normalize x = NormedSpace.normalize y := by
    rw [← normalize_hemisphereProject hxpos,
      ← normalize_hemisphereProject hypos, hproj]
  rw [NormedSpace.normalize_eq_self_of_norm_eq_one hxunit,
    NormedSpace.normalize_eq_self_of_norm_eq_one hyunit] at hnorm
  exact hxy hnorm

lemma inner_chordPoint_of_eq_one
    {w a b : E} (ha : inner ℝ w a = 1) (hb : inner ℝ w b = 1) (t : I) :
    inner ℝ w (chordPoint a b t) = 1 := by
  simp [chordPoint, inner_add_right, inner_smul_right, ha, hb]

lemma chordPoint_ne_zero_of_inner_eq_one
    {w a b : E} (ha : inner ℝ w a = 1) (hb : inner ℝ w b = 1) (t : I) :
    chordPoint a b t ≠ 0 := by
  intro hzero
  have hone := inner_chordPoint_of_eq_one ha hb t
  rw [hzero, inner_zero_right] at hone
  norm_num at hone

/-- The radial normalization of a straight segment in the affine hemisphere
section.  Unlike the raw normalized chord, this formulation makes all
intersection arguments affine. -/
noncomputable def hemisphereSphereArc (w r u : E)
    (hrpos : 0 < inner ℝ w r) (hupos : 0 < inner ℝ w u)
    (hrunit : ‖r‖ = 1) (huunit : ‖u‖ = 1) : Path r u where
  toFun t := NormedSpace.normalize
    (chordPoint (hemisphereProject w r) (hemisphereProject w u) t)
  continuous_toFun := continuous_normalize_chord fun t ↦
    chordPoint_ne_zero_of_inner_eq_one
      (inner_hemisphereProject_eq_one hrpos)
      (inner_hemisphereProject_eq_one hupos) t
  source' := by
    simp [normalize_hemisphereProject hrpos,
      NormedSpace.normalize_eq_self_of_norm_eq_one hrunit]
  target' := by
    simp [normalize_hemisphereProject hupos,
      NormedSpace.normalize_eq_self_of_norm_eq_one huunit]

@[simp] lemma hemisphereSphereArc_apply (w r u : E)
    (hrpos : 0 < inner ℝ w r) (hupos : 0 < inner ℝ w u)
    (hrunit : ‖r‖ = 1) (huunit : ‖u‖ = 1) (t : I) :
    hemisphereSphereArc w r u hrpos hupos hrunit huunit t =
      NormedSpace.normalize
        (chordPoint (hemisphereProject w r) (hemisphereProject w u) t) := rfl

lemma norm_hemisphereSphereArc (w r u : E)
    (hrpos : 0 < inner ℝ w r) (hupos : 0 < inner ℝ w u)
    (hrunit : ‖r‖ = 1) (huunit : ‖u‖ = 1) (t : I) :
    ‖hemisphereSphereArc w r u hrpos hupos hrunit huunit t‖ = 1 := by
  exact NormedSpace.norm_normalize
    (chordPoint_ne_zero_of_inner_eq_one
      (inner_hemisphereProject_eq_one hrpos)
      (inner_hemisphereProject_eq_one hupos) t)

/-- Perspective arcs preserve any pointed cone containing their endpoints. -/
lemma hemisphereSphereArc_mem_pointedCone
    {C : PointedCone ℝ E} {w r u : E}
    (hrpos : 0 < inner ℝ w r) (hupos : 0 < inner ℝ w u)
    (hrunit : ‖r‖ = 1) (huunit : ‖u‖ = 1)
    (hrC : r ∈ C) (huC : u ∈ C) (t : I) :
    hemisphereSphereArc w r u hrpos hupos hrunit huunit t ∈ C := by
  have hpr : hemisphereProject w r ∈ C :=
    C.smul_mem (inv_nonneg.mpr hrpos.le) hrC
  have hpu : hemisphereProject w u ∈ C :=
    C.smul_mem (inv_nonneg.mpr hupos.le) huC
  have hraw : chordPoint (hemisphereProject w r) (hemisphereProject w u) t ∈ C :=
    C.add_mem (C.smul_mem (sub_nonneg.mpr t.2.2) hpr)
      (C.smul_mem t.2.1 hpu)
  rw [hemisphereSphereArc_apply, NormedSpace.normalize]
  exact C.smul_mem (inv_nonneg.mpr (norm_nonneg _)) hraw

lemma hemisphereSphereArc_mem_diameterConeRegion
    {A : Set E} {x w r u : E}
    (hr : r ∈ diameterConeRegion A x)
    (hu : u ∈ diameterConeRegion A x)
    (hrpos : 0 < inner ℝ w r) (hupos : 0 < inner ℝ w u) (t : I) :
    hemisphereSphereArc w r u hrpos hupos hr.1 hu.1 t ∈
      diameterConeRegion A x := by
  exact ⟨norm_hemisphereSphereArc w r u hrpos hupos hr.1 hu.1 t,
    hemisphereSphereArc_mem_pointedCone hrpos hupos hr.1 hu.1 hr.2 hu.2 t⟩

/-- Normalization is injective on the affine section `inner w x = 1`. -/
theorem eq_of_normalize_eq_of_inner_eq_one
    {w a b : E}
    (ha : inner ℝ w a = 1) (hb : inner ℝ w b = 1)
    (h : NormedSpace.normalize a = NormedSpace.normalize b) :
    a = b := by
  have ha0 : a ≠ 0 := by
    intro hzero
    rw [hzero, inner_zero_right] at ha
    norm_num at ha
  have hb0 : b ≠ 0 := by
    intro hzero
    rw [hzero, inner_zero_right] at hb
    norm_num at hb
  have hnorm : ‖a‖ = ‖b‖ := by
    have hinv : ‖a‖⁻¹ = ‖b‖⁻¹ := by
      have hi := congrArg (fun z : E ↦ inner ℝ w z) h
      simpa [NormedSpace.normalize, inner_smul_right, ha, hb] using hi
    exact inv_injective hinv
  calc
    a = ‖a‖ • NormedSpace.normalize a := (NormedSpace.norm_smul_normalize a).symm
    _ = ‖b‖ • NormedSpace.normalize b := by rw [hnorm, h]
    _ = b := NormedSpace.norm_smul_normalize b

private lemma hemisphereSphereArc_raw_eq_of_eq
    {w r u v : E}
    (hrpos : 0 < inner ℝ w r)
    (hupos : 0 < inner ℝ w u) (hvpos : 0 < inner ℝ w v)
    (hrunit : ‖r‖ = 1) (huunit : ‖u‖ = 1) (hvunit : ‖v‖ = 1)
    {t s : I}
    (hmeet : hemisphereSphereArc w r u hrpos hupos hrunit huunit t =
      hemisphereSphereArc w r v hrpos hvpos hrunit hvunit s) :
    chordPoint (hemisphereProject w r) (hemisphereProject w u) t =
      chordPoint (hemisphereProject w r) (hemisphereProject w v) s := by
  apply eq_of_normalize_eq_of_inner_eq_one
    (inner_chordPoint_of_eq_one
      (inner_hemisphereProject_eq_one hrpos)
      (inner_hemisphereProject_eq_one hupos) t)
    (inner_chordPoint_of_eq_one
      (inner_hemisphereProject_eq_one hrpos)
      (inner_hemisphereProject_eq_one hvpos) s)
  exact hmeet

/-- A nonconstant perspective arc has an injective parameterization. -/
theorem hemisphereSphereArc_injective
    {w r u : E}
    (hrpos : 0 < inner ℝ w r) (hupos : 0 < inner ℝ w u)
    (hrunit : ‖r‖ = 1) (huunit : ‖u‖ = 1) (hru : r ≠ u) :
    Function.Injective (hemisphereSphereArc w r u hrpos hupos hrunit huunit) := by
  intro t s hmeet
  have hraw := hemisphereSphereArc_raw_eq_of_eq
    hrpos hupos hupos hrunit huunit huunit hmeet
  have hpne : hemisphereProject w r ≠ hemisphereProject w u :=
    hemisphereProject_ne_of_unit_ne hrpos hupos hrunit huunit hru
  apply Path.segment_injective_of_ne hpne
  simpa only [← chordPoint_eq_segment] using hraw

private lemma chordPoint_eq_iff_smul_sub_eq_smul_sub
    {r u v : E} {t s : I} :
    chordPoint r u t = chordPoint r v s ↔
      (t : ℝ) • (u - r) = (s : ℝ) • (v - r) := by
  have hrewrite (x : E) (q : I) :
      chordPoint r x q = r + (q : ℝ) • (x - r) := by
    simp only [chordPoint, smul_sub, sub_smul, one_smul]
    module
  rw [hrewrite u t, hrewrite v s, add_left_cancel_iff]

/-- If two radial arcs in a strict hemisphere have no positively-collinear
projected endpoint rays, they meet only at their common base point.  This is
the exact finite certificate needed to make the star of a drawn graph vertex
an embedded star. -/
theorem hemisphereSphereArcs_meet_only_at_base
    {w r u v : E}
    (hrpos : 0 < inner ℝ w r)
    (hupos : 0 < inner ℝ w u) (hvpos : 0 < inner ℝ w v)
    (hrunit : ‖r‖ = 1) (huunit : ‖u‖ = 1) (hvunit : ‖v‖ = 1)
    (hru : r ≠ u) (hrv : r ≠ v)
    (hno : ¬ ∃ a b : ℝ, 0 < a ∧ 0 < b ∧
      a • (hemisphereProject w u - hemisphereProject w r) =
        b • (hemisphereProject w v - hemisphereProject w r))
    {t s : I}
    (hmeet : hemisphereSphereArc w r u hrpos hupos hrunit huunit t =
      hemisphereSphereArc w r v hrpos hvpos hrunit hvunit s) :
    t = 0 ∧ s = 0 := by
  have hraw := hemisphereSphereArc_raw_eq_of_eq
    hrpos hupos hvpos hrunit huunit hvunit hmeet
  have hlin := chordPoint_eq_iff_smul_sub_eq_smul_sub.mp hraw
  by_cases ht0 : (t : ℝ) = 0
  · have hs0 : (s : ℝ) = 0 := by
      rw [ht0, zero_smul] at hlin
      have hpne : hemisphereProject w v - hemisphereProject w r ≠ 0 :=
        sub_ne_zero.mpr
          (hemisphereProject_ne_of_unit_ne hvpos hrpos hvunit hrunit hrv.symm)
      exact (smul_eq_zero.mp hlin.symm).resolve_right hpne
    exact ⟨Subtype.ext ht0, Subtype.ext hs0⟩
  · by_cases hs0 : (s : ℝ) = 0
    · rw [hs0, zero_smul] at hlin
      have hpne : hemisphereProject w u - hemisphereProject w r ≠ 0 :=
        sub_ne_zero.mpr
          (hemisphereProject_ne_of_unit_ne hupos hrpos huunit hrunit hru.symm)
      exact (ht0 ((smul_eq_zero.mp hlin).resolve_right hpne)).elim
    · exact (hno ⟨(t : ℝ), (s : ℝ),
        lt_of_le_of_ne t.2.1 (Ne.symm ht0),
        lt_of_le_of_ne s.2.1 (Ne.symm hs0), hlin⟩).elim

/-- Arcs assigned to two different same-color diameter-cone regions are
pointwise disjoint.  Together with `hemisphereSphereArcs_meet_only_at_base`,
this separates distinct graph vertices and distinct edges in each vertex
star. -/
theorem hemisphereSphereArcs_ne_of_distinct_regions
    {A : Set E} {x y : E}
    (hx : x ∈ A) (hy : y ∈ A) (hxy : x ≠ y)
    (hdiam : ∀ p ∈ A, ∀ q ∈ A, ‖p - q‖ ≤ 1)
    {wx rx ux wy ry uy : E}
    (hrx : rx ∈ diameterConeRegion A x)
    (hux : ux ∈ diameterConeRegion A x)
    (hry : ry ∈ diameterConeRegion A y)
    (huy : uy ∈ diameterConeRegion A y)
    (hrxpos : 0 < inner ℝ wx rx) (huxpos : 0 < inner ℝ wx ux)
    (hrypos : 0 < inner ℝ wy ry) (huypos : 0 < inner ℝ wy uy)
    (t s : I) :
    hemisphereSphereArc wx rx ux hrxpos huxpos hrx.1 hux.1 t ≠
      hemisphereSphereArc wy ry uy hrypos huypos hry.1 huy.1 s := by
  intro hmeet
  have hleft := hemisphereSphereArc_mem_diameterConeRegion
    hrx hux hrxpos huxpos t
  have hright := hemisphereSphereArc_mem_diameterConeRegion
    hry huy hrypos huypos s
  have hright' :
      hemisphereSphereArc wx rx ux hrxpos huxpos hrx.1 hux.1 t ∈
        diameterConeRegion A y := by
    rw [hmeet]
    exact hright
  exact hxy (eq_of_mem_two_diameterConeRegions hx hy hdiam hleft hright')


end Erdos223.SphericalEuler

/-! ## Extreme rays after peeling low-degree vertices -/

open Metric
open scoped EuclideanGeometry SimpleGraph

namespace Erdos223.SphericalEuler

noncomputable section

/-- A unit generator `u` is not in the nonnegative cone of other unit
generators if a witness `a` is at distance one from `u`, at distance at most
one from every other generator, and is nonzero. -/
theorem unit_not_mem_conicHull_of_witness
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {S : Set E} {u a : E}
    (hu : ‖u‖ = 1) (ha : a ≠ 0) (hau : ‖a - u‖ = 1)
    (hunit : ∀ v ∈ S, ‖v‖ = 1)
    (hadist : ∀ v ∈ S, ‖a - v‖ ≤ 1)
    (hne : ∀ v ∈ S, v ≠ u) :
    u ∉ PointedCone.hull ℝ S := by
  classical
  intro hmem
  rw [PointedCone.mem_hull_set] at hmem
  obtain ⟨c, hcsupp, hc0, hcsum⟩ := hmem
  let q : ℝ := ∑ v ∈ c.support, c v
  have hsupp_mem (v : E) (hv : v ∈ c.support) : v ∈ S :=
    hcsupp (by simpa using hv)
  have hq_nonneg : 0 ≤ q :=
    Finset.sum_nonneg fun v _ ↦ hc0 v
  have hnorm_le : ‖u‖ ≤ q := by
    rw [← hcsum]
    calc
      ‖c.sum (fun v r ↦ r • v)‖ = ‖∑ v ∈ c.support, c v • v‖ := by rfl
      _ ≤ ∑ v ∈ c.support, ‖c v • v‖ := norm_sum_le _ _
      _ = q := by
        apply Finset.sum_congr rfl
        intro v hv
        rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (hc0 v),
          hunit v (hsupp_mem v hv), mul_one]
  have hq_ge : 1 ≤ q := by simpa [hu] using hnorm_le
  have ha_norm_pos : 0 < ‖a‖ := norm_pos_iff.mpr ha
  have hau_inner : 2 * inner ℝ a u = ‖a‖ ^ 2 := by
    have h := norm_sub_sq_real a u
    rw [hau, hu] at h
    nlinarith
  have hav_inner (v : E) (hv : v ∈ c.support) :
      ‖a‖ ^ 2 ≤ 2 * inner ℝ a v := by
    have h := norm_sub_sq_real a v
    have hd := hadist v (hsupp_mem v hv)
    rw [hunit v (hsupp_mem v hv)] at h
    have hd2 : ‖a - v‖ ^ 2 ≤ 1 := by
      nlinarith [mul_self_le_mul_self (norm_nonneg (a - v)) hd]
    nlinarith
  have hinner_sum : inner ℝ a u =
      ∑ v ∈ c.support, c v * inner ℝ a v := by
    rw [← hcsum]
    simp only [Finsupp.inner_sum, real_inner_smul_right]
    rfl
  have hweighted : ‖a‖ ^ 2 * q ≤
      ∑ v ∈ c.support, c v * (2 * inner ℝ a v) := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun v hv ↦ by
      simpa [mul_comm] using
        mul_le_mul_of_nonneg_left (hav_inner v hv) (hc0 v)
  have hweighted_eq :
      (∑ v ∈ c.support, c v * (2 * inner ℝ a v)) = ‖a‖ ^ 2 := by
    calc
      (∑ v ∈ c.support, c v * (2 * inner ℝ a v)) =
          2 * ∑ v ∈ c.support, c v * inner ℝ a v := by
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro v hv
            ring
      _ = 2 * inner ℝ a u := by rw [hinner_sum]
      _ = ‖a‖ ^ 2 := hau_inner
  have hq_le : q ≤ 1 := by
    rw [hweighted_eq] at hweighted
    nlinarith [sq_pos_of_pos ha_norm_pos]
  have hq : q = 1 := le_antisymm hq_le hq_ge
  have hsupp_nonempty : c.support.Nonempty := by
    by_contra h
    have hempty : c.support = ∅ := Finset.not_nonempty_iff_eq_empty.mp h
    simp [q, hempty] at hq
  obtain ⟨v, hv⟩ := hsupp_nonempty
  have hcv_ne : c v ≠ 0 := Finsupp.mem_support_iff.mp hv
  have hcv : 0 < c v := lt_of_le_of_ne (hc0 v) (Ne.symm hcv_ne)
  have hv_ne : v ≠ u := hne v (hsupp_mem v hv)
  have hdistpos : 0 < ‖v - u‖ ^ 2 :=
    sq_pos_of_pos (norm_pos_iff.mpr (sub_ne_zero.mpr hv_ne))
  have hsum_dist_pos : 0 <
      ∑ z ∈ c.support, c z * ‖z - u‖ ^ 2 := by
    exact (mul_pos hcv hdistpos).trans_le
      (Finset.single_le_sum
        (fun z hz ↦ mul_nonneg (hc0 z) (sq_nonneg ‖z - u‖)) hv)
  have hsum_dist_zero :
      (∑ z ∈ c.support, c z * ‖z - u‖ ^ 2) = 0 := by
    simp_rw [norm_sub_sq_real]
    calc
      (∑ z ∈ c.support,
          c z * (‖z‖ ^ 2 - 2 * inner ℝ z u + ‖u‖ ^ 2)) =
          ∑ z ∈ c.support, c z * (2 - 2 * inner ℝ z u) := by
            apply Finset.sum_congr rfl
            intro z hz
            rw [hunit z (hsupp_mem z hz), hu]
            ring
      _ = 2 * q - 2 * inner ℝ u u := by
            have hsum_inner :
                (∑ z ∈ c.support, c z * inner ℝ z u) = inner ℝ u u := by
              rw [← hcsum]
              simp only [Finsupp.sum_inner, real_inner_smul_left]
              rfl
            calc
              (∑ z ∈ c.support, c z * (2 - 2 * inner ℝ z u)) =
                  ∑ z ∈ c.support,
                    (2 * c z - 2 * (c z * inner ℝ z u)) := by
                      apply Finset.sum_congr rfl
                      intro z hz
                      ring
              _ = 2 * (∑ z ∈ c.support, c z) -
                    2 * (∑ z ∈ c.support, c z * inner ℝ z u) := by
                      rw [Finset.sum_sub_distrib, Finset.mul_sum, Finset.mul_sum]
              _ = 2 * q - 2 * inner ℝ u u := by rw [hsum_inner]
      _ = 0 := by
            rw [hq, real_inner_self_eq_norm_sq, hu]
            norm_num
  linarith

/-- The diameter-neighbour directions at `x`, with the direction towards `y`
removed. -/
def otherNeighborDirections {d : ℕ} (A : Finset (Point d))
    (x y : {z // z ∈ A}) : Set (Point d) :=
  {v | ∃ z : {z // z ∈ A},
    (diameterGraph A).Adj x z ∧ z ≠ y ∧
      v = (z : Point d) - (x : Point d)}

/-- After all vertices have degree at least two, every diameter-neighbour
direction is an extreme ray of its spherical cone region. -/
theorem neighborDirection_not_mem_other_conicHull
    {d : ℕ} {A : Finset (Point d)} (hA : IsDiameterOne A)
    (hmin : ∀ v : {z // z ∈ A}, 2 ≤ (diameterGraph A).degree v)
    {x y : {z // z ∈ A}} (hxy : (diameterGraph A).Adj x y) :
    (y : Point d) - (x : Point d) ∉
      PointedCone.hull ℝ (otherNeighborDirections A x y) := by
  classical
  have hycard : 1 < ((diameterGraph A).neighborFinset y).card := by
    change 1 < (diameterGraph A).degree y
    exact lt_of_lt_of_le (by norm_num) (hmin y)
  obtain ⟨w₁, hw₁, w₂, hw₂, hw₁w₂⟩ := Finset.one_lt_card.mp hycard
  obtain ⟨w, hw, hwx⟩ :
      ∃ w ∈ (diameterGraph A).neighborFinset y, w ≠ x := by
    by_cases hw₁x : w₁ = x
    · exact ⟨w₂, hw₂, fun hw₂x ↦ hw₁w₂ (hw₁x.trans hw₂x.symm)⟩
    · exact ⟨w₁, hw₁, hw₁x⟩
  have hyw : (diameterGraph A).Adj y w :=
    ((diameterGraph A).mem_neighborFinset y w).mp hw
  apply unit_not_mem_conicHull_of_witness
      (a := (w : Point d) - (x : Point d))
  · have hdist : dist (y : Point d) (x : Point d) = 1 := by
      simpa [dist_comm] using (diameterGraph_adj A x y).mp hxy
    simpa [dist_eq_norm] using hdist
  · exact sub_ne_zero.mpr (Subtype.coe_injective.ne hwx)
  · have hdist : dist (w : Point d) (y : Point d) = 1 := by
      simpa [dist_comm] using (diameterGraph_adj A y w).mp hyw
    simpa only [sub_sub_sub_cancel_right, dist_eq_norm] using hdist
  · rintro v ⟨z, hxz, hzy, rfl⟩
    have hdist : dist (z : Point d) (x : Point d) = 1 := by
      simpa [dist_comm] using (diameterGraph_adj A x z).mp hxz
    simpa [dist_eq_norm] using hdist
  · rintro v ⟨z, hxz, hzy, rfl⟩
    have hd := hA.dist_le w.prop z.prop
    simpa only [sub_sub_sub_cancel_right, dist_eq_norm] using hd
  · rintro v ⟨z, hxz, hzy, rfl⟩ heq
    apply hzy
    apply Subtype.ext
    exact sub_left_injective heq

end

end Erdos223.SphericalEuler


open Metric Set
open scoped BigOperators EuclideanGeometry RealInnerProductSpace SimpleGraph

namespace Erdos223.SphericalEuler

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable {I : Type*}

/-- All indexed points other than the one with index `i`. -/
def otherIndexedPoints (p : I → E) (i : I) : Set E :=
  {x | ∃ j : I, j ≠ i ∧ x = p j}

/-- The unnormalised radial segment from a base point to an indexed endpoint. -/
def radialSectionPoint (b : E) (p : I → E) (i : I) (t : ℝ) : E :=
  (1 - t) • b + t • p i

/-- The radial segment projected to the unit sphere. -/
def sphericalRadialArc (b : E) (p : I → E) (i : I) (t : ℝ) : E :=
  NormedSpace.normalize (radialSectionPoint b p i t)

lemma radialSectionPoint_linear_eq_one
    (phi : E →ₗ[ℝ] ℝ) {b : E} {p : I → E}
    (hb : phi b = 1) (hp : ∀ i, phi (p i) = 1) (i : I) (t : ℝ) :
    phi (radialSectionPoint b p i t) = 1 := by
  simp [radialSectionPoint, map_add, map_smul, hb, hp]

lemma radialSectionPoint_ne_zero
    (phi : E →ₗ[ℝ] ℝ) {b : E} {p : I → E}
    (hb : phi b = 1) (hp : ∀ i, phi (p i) = 1) (i : I) (t : ℝ) :
    radialSectionPoint b p i t ≠ 0 := by
  intro hzero
  have h := radialSectionPoint_linear_eq_one phi hb hp i t
  rw [hzero, map_zero] at h
  norm_num at h

lemma normalize_eq_normalize_of_linear_eq_one
    (phi : E →ₗ[ℝ] ℝ) {x y : E}
    (hx : phi x = 1) (hy : phi y = 1)
    (hxy : NormedSpace.normalize x = NormedSpace.normalize y) : x = y := by
  have hxscale : ‖x‖ * phi (NormedSpace.normalize x) = 1 := by
    change ‖x‖ • phi (NormedSpace.normalize x) = 1
    rw [← map_smul, NormedSpace.norm_smul_normalize, hx]
  have hyscale : ‖y‖ * phi (NormedSpace.normalize y) = 1 := by
    change ‖y‖ • phi (NormedSpace.normalize y) = 1
    rw [← map_smul, NormedSpace.norm_smul_normalize, hy]
  have hnorm : ‖x‖ = ‖y‖ := by
    rw [hxy] at hxscale
    have hphi_ne : phi (NormedSpace.normalize y) ≠ 0 := by
      intro hzero
      rw [hzero, mul_zero] at hyscale
      norm_num at hyscale
    exact mul_right_cancel₀ hphi_ne (hxscale.trans hyscale.symm)
  calc
    x = ‖x‖ • NormedSpace.normalize x :=
      (NormedSpace.norm_smul_normalize x).symm
    _ = ‖y‖ • NormedSpace.normalize y := by rw [hnorm, hxy]
    _ = y := NormedSpace.norm_smul_normalize y

lemma sphericalRadialArc_eq_iff_section_eq
    (phi : E →ₗ[ℝ] ℝ) {b : E} {p : I → E}
    (hb : phi b = 1) (hp : ∀ i, phi (p i) = 1)
    {i j : I} {t s : ℝ} :
    sphericalRadialArc b p i t = sphericalRadialArc b p j s ↔
      radialSectionPoint b p i t = radialSectionPoint b p j s := by
  constructor
  · exact normalize_eq_normalize_of_linear_eq_one phi
      (radialSectionPoint_linear_eq_one phi hb hp i t)
      (radialSectionPoint_linear_eq_one phi hb hp j s)
  · intro h
    exact congrArg NormedSpace.normalize h

/-- If every indexed endpoint is outside the cone of the other endpoints and
the base has a positive coefficient strictly below one at every endpoint,
then distinct radial arcs only meet at their common base. -/
theorem sphericalRadialArc_ne_of_extreme
    (phi : E →ₗ[ℝ] ℝ) {b : E} {p : I → E}
    (hb : phi b = 1) (hp : ∀ i, phi (p i) = 1)
    (hext : ∀ i, p i ∉ PointedCone.hull ℝ (otherIndexedPoints p i))
    (hbase : ∀ i, ∃ a : ℝ, ∃ z : E,
      0 < a ∧ a < 1 ∧
      z ∈ PointedCone.hull ℝ (otherIndexedPoints p i) ∧
      b = a • p i + z)
    {i j : I} (hij : i ≠ j) {t s : ℝ} (ht : 0 < t) (hs : 0 < s) :
    sphericalRadialArc b p i t ≠ sphericalRadialArc b p j s := by
  intro harc
  have hsection : radialSectionPoint b p i t = radialSectionPoint b p j s :=
    (sphericalRadialArc_eq_iff_section_eq phi hb hp).mp harc
  rcases le_total t s with hts | hst
  · obtain ⟨a, z, ha, ha1, hz, hbdec⟩ := hbase j
    let C := PointedCone.hull ℝ (otherIndexedPoints p j)
    have hpi : p i ∈ C := PointedCone.subset_hull
      ⟨i, hij, rfl⟩
    have hcoeff : 0 < s - (s - t) * a := by
      nlinarith [mul_pos hs (sub_pos.mpr ha1), mul_pos ht ha]
    have hrel :
        (s - (s - t) * a) • p j = t • p i + (s - t) • z := by
      rw [radialSectionPoint, radialSectionPoint, hbdec] at hsection
      calc
        (s - (s - t) * a) • p j =
            ((1 - s) • (a • p j + z) + s • p j) +
              (s - t) • z - (1 - t) • (a • p j + z) := by module
        _ = ((1 - t) • (a • p j + z) + t • p i) +
              (s - t) • z - (1 - t) • (a • p j + z) := by rw [← hsection]
        _ = t • p i + (s - t) • z := by module
    have hrhs : t • p i + (s - t) • z ∈ C :=
      C.add_mem (C.smul_mem ht.le hpi)
        (C.smul_mem (sub_nonneg.mpr hts) hz)
    have hleft : (s - (s - t) * a) • p j ∈ C := by
      rw [hrel]
      exact hrhs
    exact hext j ((C.smul_mem_iff hcoeff).mp hleft)
  · obtain ⟨a, z, ha, ha1, hz, hbdec⟩ := hbase i
    let C := PointedCone.hull ℝ (otherIndexedPoints p i)
    have hpj : p j ∈ C := PointedCone.subset_hull
      ⟨j, Ne.symm hij, rfl⟩
    have hcoeff : 0 < t - (t - s) * a := by
      nlinarith [mul_pos ht (sub_pos.mpr ha1), mul_pos hs ha]
    have hrel :
        (t - (t - s) * a) • p i = s • p j + (t - s) • z := by
      rw [radialSectionPoint, radialSectionPoint, hbdec] at hsection
      calc
        (t - (t - s) * a) • p i =
            ((1 - t) • (a • p i + z) + t • p i) +
              (t - s) • z - (1 - s) • (a • p i + z) := by module
        _ = ((1 - s) • (a • p i + z) + s • p j) +
              (t - s) • z - (1 - s) • (a • p i + z) := by rw [hsection]
        _ = s • p j + (t - s) • z := by module
    have hrhs : s • p j + (t - s) • z ∈ C :=
      C.add_mem (C.smul_mem hs.le hpj)
        (C.smul_mem (sub_nonneg.mpr hst) hz)
    have hleft : (t - (t - s) * a) • p i ∈ C := by
      rw [hrel]
      exact hrhs
    exact hext i ((C.smul_mem_iff hcoeff).mp hleft)

/-- Every single radial arc in the fan is simple. -/
theorem sphericalRadialArc_injective_of_extreme
    (phi : E →ₗ[ℝ] ℝ) {b : E} {p : I → E}
    (hb : phi b = 1) (hp : ∀ i, phi (p i) = 1)
    (hext : ∀ i, p i ∉ PointedCone.hull ℝ (otherIndexedPoints p i))
    (hbase : ∀ i, ∃ a : ℝ, ∃ z : E,
      0 < a ∧ a < 1 ∧
      z ∈ PointedCone.hull ℝ (otherIndexedPoints p i) ∧
      b = a • p i + z)
    (i : I) : Function.Injective (sphericalRadialArc b p i) := by
  have hbpi : b ≠ p i := by
    intro hbeq
    obtain ⟨a, z, ha, ha1, hz, hbdec⟩ := hbase i
    let C := PointedCone.hull ℝ (otherIndexedPoints p i)
    have hrel : (1 - a) • p i = z := by
      rw [hbeq] at hbdec
      calc
        (1 - a) • p i = p i - a • p i := by module
        _ = z := (sub_eq_iff_eq_add').2 hbdec
    have hleft : (1 - a) • p i ∈ C := by rw [hrel]; exact hz
    exact hext i ((C.smul_mem_iff (sub_pos.mpr ha1)).mp hleft)
  intro t s harc
  have hsection : radialSectionPoint b p i t = radialSectionPoint b p i s :=
    (sphericalRadialArc_eq_iff_section_eq phi hb hp).mp harc
  apply AffineMap.lineMap_injective ℝ hbpi
  simpa [radialSectionPoint, AffineMap.lineMap_apply_module] using hsection

/-! ## A canonical strictly interior base -/

variable [Fintype I]

/-- Arithmetic mean of the indexed affine-section points. -/
def radialAverageBase (p : I → E) : E :=
  ((Fintype.card I : ℝ)⁻¹) • ∑ i : I, p i

lemma radialAverageBase_linear_eq_one
    (phi : E →ₗ[ℝ] ℝ) {p : I → E}
    (hp : ∀ i, phi (p i) = 1) [Nonempty I] :
    phi (radialAverageBase p) = 1 := by
  have hcard : (Fintype.card I : ℝ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  simp [radialAverageBase, map_smul, map_sum, hp, hcard]

/-- The arithmetic mean has a positive coefficient smaller than one at each
endpoint, and its remaining part belongs to the cone of the other points. -/
lemma radialAverageBase_decomposition [Nontrivial I] (p : I → E) (i : I) :
    ∃ a : ℝ, ∃ z : E,
      0 < a ∧ a < 1 ∧
      z ∈ PointedCone.hull ℝ (otherIndexedPoints p i) ∧
      radialAverageBase p = a • p i + z := by
  classical
  let n : ℝ := Fintype.card I
  let a : ℝ := n⁻¹
  let z : E := a • ∑ j ∈ (Finset.univ.erase i), p j
  have hnpos : 0 < n := by
    change (0 : ℝ) < Fintype.card I
    exact_mod_cast Fintype.card_pos
  have hn1 : 1 < n := by
    change (1 : ℝ) < Fintype.card I
    exact_mod_cast Fintype.one_lt_card
  have ha : 0 < a := inv_pos.mpr hnpos
  have han : a * n = 1 := inv_mul_cancel₀ hnpos.ne'
  have ha1 : a < 1 := by nlinarith
  refine ⟨a, z, ha, ha1, ?_, ?_⟩
  · let C := PointedCone.hull ℝ (otherIndexedPoints p i)
    have hsum : (∑ j ∈ (Finset.univ.erase i), p j) ∈ C := by
      apply C.sum_mem
      intro j hj
      have hji : j ≠ i := (Finset.mem_erase.mp hj).1
      exact PointedCone.subset_hull ⟨j, hji, rfl⟩
    exact C.smul_mem ha.le hsum
  · rw [radialAverageBase]
    change n⁻¹ • (∑ j : I, p j) =
      a • p i + a • ∑ j ∈ (Finset.univ.erase i), p j
    rw [show n⁻¹ = a by rfl]
    rw [← Finset.sum_erase_add _ _ (Finset.mem_univ i)]
    module

/-! ## Positive affine sections and transport of extremality -/

/-- Rescale a vector to the affine hyperplane `phi = 1`. -/
def positiveSectionPoint (phi : E →ₗ[ℝ] ℝ) (u : E) : E :=
  (phi u)⁻¹ • u

@[simp]
lemma positiveSectionPoint_linear_eq_one
    (phi : E →ₗ[ℝ] ℝ) {u : E} (hu : 0 < phi u) :
    phi (positiveSectionPoint phi u) = 1 := by
  simp [positiveSectionPoint, map_smul, hu.ne']

lemma normalize_positiveSectionPoint
    (phi : E →ₗ[ℝ] ℝ) {u : E} (hu : 0 < phi u) :
    NormedSpace.normalize (positiveSectionPoint phi u) =
      NormedSpace.normalize u := by
  exact NormedSpace.normalize_smul_of_pos (inv_pos.mpr hu) u

/-- Positive rescaling preserves the property of being outside the cone of
all other indexed generators. -/
lemma positiveSectionPoint_not_mem_other_cone
    (phi : E →ₗ[ℝ] ℝ) {u : I → E}
    (hphi : ∀ i, 0 < phi (u i))
    (hext : ∀ i, u i ∉ PointedCone.hull ℝ (otherIndexedPoints u i))
    (i : I) :
    positiveSectionPoint phi (u i) ∉
      PointedCone.hull ℝ
        (otherIndexedPoints (fun j ↦ positiveSectionPoint phi (u j)) i) := by
  intro hmem
  let C := PointedCone.hull ℝ (otherIndexedPoints u i)
  have hle : PointedCone.hull ℝ
      (otherIndexedPoints (fun j ↦ positiveSectionPoint phi (u j)) i) ≤ C := by
    apply Submodule.span_le.mpr
    rintro x ⟨j, hji, rfl⟩
    exact C.smul_mem (inv_pos.mpr (hphi j)).le
      (PointedCone.subset_hull ⟨j, hji, rfl⟩)
  have hpC : positiveSectionPoint phi (u i) ∈ C := hle hmem
  have huC : (phi (u i)) • positiveSectionPoint phi (u i) ∈ C :=
    C.smul_mem (hphi i).le hpC
  have heq : (phi (u i)) • positiveSectionPoint phi (u i) = u i := by
    simp [positiveSectionPoint, smul_smul, (hphi i).ne']
  rw [heq] at huC
  exact hext i huC

/-! ## Sphere containment and continuity -/

omit [Fintype I] in
lemma sphericalRadialArc_mem_sphereCone
    (phi : E →ₗ[ℝ] ℝ) {C : PointedCone ℝ E} {b : E} {p : I → E}
    (hphi_b : phi b = 1) (hphi_p : ∀ i, phi (p i) = 1)
    (hb : b ∈ C) (hp : ∀ i, p i ∈ C)
    (i : I) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    ‖sphericalRadialArc b p i t‖ = 1 ∧ sphericalRadialArc b p i t ∈ C := by
  have hq0 : radialSectionPoint b p i t ≠ 0 :=
    radialSectionPoint_ne_zero phi hphi_b hphi_p i t
  have hqC : radialSectionPoint b p i t ∈ C := by
    exact C.add_mem (C.smul_mem (sub_nonneg.mpr ht1) hb)
      (C.smul_mem ht0 (hp i))
  constructor
  · exact NormedSpace.norm_normalize hq0
  · rw [sphericalRadialArc, NormedSpace.normalize]
    exact C.smul_mem (inv_nonneg.mpr (norm_nonneg _)) hqC

omit [Fintype I] in
lemma continuous_sphericalRadialArc
    (phi : E →ₗ[ℝ] ℝ) {b : E} {p : I → E}
    (hb : phi b = 1) (hp : ∀ i, phi (p i) = 1) (i : I) :
    Continuous (fun t : ℝ ↦ sphericalRadialArc b p i t) := by
  have hq : Continuous (fun t : ℝ ↦ radialSectionPoint b p i t) := by
    unfold radialSectionPoint
    fun_prop
  rw [show (fun t : ℝ ↦ sphericalRadialArc b p i t) =
      fun t : ℝ ↦ ‖radialSectionPoint b p i t‖⁻¹ •
        radialSectionPoint b p i t by rfl]
  exact (hq.norm.inv₀ (fun t ↦
    norm_ne_zero_iff.mpr (radialSectionPoint_ne_zero phi hb hp i t))).smul hq

/-- The continuous spherical radial arc as a bundled path. -/
def sphericalRadialPath
    (phi : E →ₗ[ℝ] ℝ) (b : E) (p : I → E)
    (hb : phi b = 1) (hp : ∀ i, phi (p i) = 1) (i : I) :
    Path (NormedSpace.normalize b) (NormedSpace.normalize (p i)) where
  toFun t := sphericalRadialArc b p i (t : ℝ)
  continuous_toFun :=
    (continuous_sphericalRadialArc phi hb hp i).comp continuous_subtype_val
  source' := by simp [sphericalRadialArc, radialSectionPoint]
  target' := by simp [sphericalRadialArc, radialSectionPoint]

/-! ## The assembled canonical radial fan -/

def positiveSectionFamily (phi : E →ₗ[ℝ] ℝ) (u : I → E) : I → E :=
  fun i ↦ positiveSectionPoint phi (u i)

def canonicalRadialBase (phi : E →ₗ[ℝ] ℝ) (u : I → E) : E :=
  radialAverageBase (positiveSectionFamily phi u)

def canonicalSphericalRadialArc
    (phi : E →ₗ[ℝ] ℝ) (u : I → E) (i : I) (t : ℝ) : E :=
  sphericalRadialArc (canonicalRadialBase phi u)
    (positiveSectionFamily phi u) i t

theorem canonicalSphericalRadialArc_pairwise
    [Nontrivial I] (phi : E →ₗ[ℝ] ℝ) (u : I → E)
    (hphi : ∀ i, 0 < phi (u i))
    (hext : ∀ i, u i ∉ PointedCone.hull ℝ (otherIndexedPoints u i))
    {i j : I} (hij : i ≠ j) {t s : ℝ} (ht : 0 < t) (hs : 0 < s) :
    canonicalSphericalRadialArc phi u i t ≠
      canonicalSphericalRadialArc phi u j s := by
  let p := positiveSectionFamily phi u
  have hp : ∀ i, phi (p i) = 1 := fun i ↦
    positiveSectionPoint_linear_eq_one phi (hphi i)
  have hb : phi (radialAverageBase p) = 1 :=
    radialAverageBase_linear_eq_one phi hp
  apply sphericalRadialArc_ne_of_extreme phi hb hp
  · intro k
    exact positiveSectionPoint_not_mem_other_cone phi hphi hext k
  · exact radialAverageBase_decomposition p
  · exact hij
  · exact ht
  · exact hs

theorem canonicalSphericalRadialArc_mem_sphereCone
    [Nonempty I] (phi : E →ₗ[ℝ] ℝ) (u : I → E)
    (hphi : ∀ i, 0 < phi (u i)) (C : PointedCone ℝ E)
    (huC : ∀ i, u i ∈ C) (i : I) {t : ℝ}
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    ‖canonicalSphericalRadialArc phi u i t‖ = 1 ∧
      canonicalSphericalRadialArc phi u i t ∈ C := by
  let p := positiveSectionFamily phi u
  have hp_phi : ∀ i, phi (p i) = 1 := fun i ↦
    positiveSectionPoint_linear_eq_one phi (hphi i)
  have hpC : ∀ i, p i ∈ C := fun i ↦
    C.smul_mem (inv_pos.mpr (hphi i)).le (huC i)
  have hb_phi : phi (radialAverageBase p) = 1 :=
    radialAverageBase_linear_eq_one phi hp_phi
  have hbC : radialAverageBase p ∈ C := by
    apply C.smul_mem (inv_nonneg.mpr (by positivity))
    exact C.sum_mem fun i _ ↦ hpC i
  exact sphericalRadialArc_mem_sphereCone phi hb_phi hp_phi hbC hpC i ht0 ht1

@[simp]
lemma canonicalSphericalRadialArc_zero
    (phi : E →ₗ[ℝ] ℝ) (u : I → E) (i : I) :
    canonicalSphericalRadialArc phi u i 0 =
      NormedSpace.normalize (canonicalRadialBase phi u) := by
  simp [canonicalSphericalRadialArc, sphericalRadialArc, radialSectionPoint]

@[simp]
lemma canonicalSphericalRadialArc_one
    (phi : E →ₗ[ℝ] ℝ) (u : I → E)
    (hphi : ∀ i, 0 < phi (u i)) (hunit : ∀ i, ‖u i‖ = 1) (i : I) :
    canonicalSphericalRadialArc phi u i 1 = u i := by
  simp only [canonicalSphericalRadialArc, sphericalRadialArc, radialSectionPoint,
    one_smul, sub_self, zero_smul, zero_add]
  change NormedSpace.normalize (positiveSectionPoint phi (u i)) = u i
  rw [normalize_positiveSectionPoint phi (hphi i),
    NormedSpace.normalize_eq_self_of_norm_eq_one (hunit i)]

/-! ## Specialisation to a diameter cone region -/

namespace DiameterRadialFan

abbrev NeighborIndex {d : ℕ} (A : Finset (Point d))
    (x : {z // z ∈ A}) := (diameterGraph A).neighborSet x

def direction {d : ℕ} {A : Finset (Point d)} {x : {z // z ∈ A}}
    (i : NeighborIndex A x) : Point d :=
  (i.1 : Point d) - (x : Point d)

def directionSum {d : ℕ} (A : Finset (Point d)) (x : {z // z ∈ A}) : Point d :=
  ∑ i : NeighborIndex A x, direction i

def directionFunctional {d : ℕ} (A : Finset (Point d))
    (x : {z // z ∈ A}) : Point d →ₗ[ℝ] ℝ :=
  (innerₗ (Point d)) (directionSum A x)

lemma direction_unit {d : ℕ} {A : Finset (Point d)}
    {x : {z // z ∈ A}} (i : NeighborIndex A x) :
    ‖direction i‖ = 1 := by
  have hdist : dist (i.1 : Point d) (x : Point d) = 1 := by
    simpa [dist_comm] using (diameterGraph_adj A x i.1).mp i.2
  simpa [direction, dist_eq_norm] using hdist

private lemma half_le_inner_of_unit_of_sub_norm_le_one
    {u v : E} (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (hd : ‖u - v‖ ≤ 1) :
    (1 / 2 : ℝ) ≤ inner ℝ u v := by
  have hsquare : ‖u - v‖ ^ 2 ≤ 1 := by
    nlinarith [mul_self_le_mul_self (norm_nonneg (u - v)) hd]
  have h := norm_sub_sq_real u v
  rw [hu, hv] at h
  nlinarith

lemma direction_inner_ge_half {d : ℕ} {A : Finset (Point d)}
    (hA : IsDiameterOne A) {x : {z // z ∈ A}}
    (i j : NeighborIndex A x) :
    (1 / 2 : ℝ) ≤ inner ℝ (direction i) (direction j) := by
  apply half_le_inner_of_unit_of_sub_norm_le_one (direction_unit i) (direction_unit j)
  have hd := hA.dist_le i.1.prop j.1.prop
  simpa only [direction, sub_sub_sub_cancel_right, dist_eq_norm] using hd

lemma neighborIndex_nontrivial {d : ℕ} {A : Finset (Point d)}
    (hmin : ∀ v : {z // z ∈ A}, 2 ≤ (diameterGraph A).degree v)
    (x : {z // z ∈ A}) : Nontrivial (NeighborIndex A x) := by
  rw [← Fintype.one_lt_card_iff_nontrivial]
  rw [(diameterGraph A).card_neighborSet_eq_degree]
  exact lt_of_lt_of_le (by norm_num) (hmin x)

lemma directionFunctional_pos {d : ℕ} {A : Finset (Point d)}
    (hA : IsDiameterOne A)
    (hmin : ∀ v : {z // z ∈ A}, 2 ≤ (diameterGraph A).degree v)
    (x : {z // z ∈ A}) (i : NeighborIndex A x) :
    0 < directionFunctional A x (direction i) := by
  letI : Nontrivial (NeighborIndex A x) := neighborIndex_nontrivial hmin x
  have hsum : (∑ _j : NeighborIndex A x, (1 / 2 : ℝ)) ≤
      ∑ j : NeighborIndex A x, inner ℝ (direction j) (direction i) :=
    Finset.sum_le_sum fun j _ ↦ direction_inner_ge_half hA j i
  have hleft : 0 < ∑ _j : NeighborIndex A x, (1 / 2 : ℝ) := by
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    positivity
  apply hleft.trans_le
  simpa [directionFunctional, directionSum, sum_inner] using hsum

lemma otherIndexedDirections_eq {d : ℕ} {A : Finset (Point d)}
    {x : {z // z ∈ A}} (i : NeighborIndex A x) :
    otherIndexedPoints (fun j : NeighborIndex A x ↦ direction j) i =
      otherNeighborDirections A x i.1 := by
  ext v
  constructor
  · rintro ⟨j, hji, rfl⟩
    exact ⟨j.1, j.2, fun h ↦ hji (Subtype.ext h), rfl⟩
  · rintro ⟨z, hxz, hzi, rfl⟩
    let j : NeighborIndex A x := ⟨z, hxz⟩
    refine ⟨j, ?_, rfl⟩
    intro hji
    apply hzi
    exact congrArg Subtype.val hji

lemma direction_not_mem_otherIndexed_cone {d : ℕ} {A : Finset (Point d)}
    (hA : IsDiameterOne A)
    (hmin : ∀ v : {z // z ∈ A}, 2 ≤ (diameterGraph A).degree v)
    {x : {z // z ∈ A}} (i : NeighborIndex A x) :
    direction i ∉ PointedCone.hull ℝ
      (otherIndexedPoints (fun j : NeighborIndex A x ↦ direction j) i) := by
  rw [otherIndexedDirections_eq i]
  exact neighborDirection_not_mem_other_conicHull hA hmin i.2

/-- The canonical local spherical fan at a diameter-graph vertex. -/
def arc {d : ℕ} (A : Finset (Point d)) (x : {z // z ∈ A})
    (i : NeighborIndex A x) (t : ℝ) : Point d :=
  canonicalSphericalRadialArc (directionFunctional A x)
    (fun j : NeighborIndex A x ↦ direction j) i t

def base {d : ℕ} (A : Finset (Point d)) (x : {z // z ∈ A}) : Point d :=
  canonicalRadialBase (directionFunctional A x)
    (fun j : NeighborIndex A x ↦ direction j)

theorem arc_pairwise_interior_disjoint {d : ℕ} {A : Finset (Point d)}
    (hA : IsDiameterOne A)
    (hmin : ∀ v : {z // z ∈ A}, 2 ≤ (diameterGraph A).degree v)
    {x : {z // z ∈ A}} {i j : NeighborIndex A x} (hij : i ≠ j)
    {t s : ℝ} (ht : 0 < t) (hs : 0 < s) :
    arc A x i t ≠ arc A x j s := by
  letI : Nontrivial (NeighborIndex A x) := neighborIndex_nontrivial hmin x
  exact canonicalSphericalRadialArc_pairwise
    (directionFunctional A x) (fun k : NeighborIndex A x ↦ direction k)
    (directionFunctional_pos hA hmin x)
    (direction_not_mem_otherIndexed_cone hA hmin) hij ht hs

theorem arc_injective {d : ℕ} {A : Finset (Point d)}
    (hA : IsDiameterOne A)
    (hmin : ∀ v : {z // z ∈ A}, 2 ≤ (diameterGraph A).degree v)
    {x : {z // z ∈ A}} (i : NeighborIndex A x) :
    Function.Injective (arc A x i) := by
  letI : Nontrivial (NeighborIndex A x) := neighborIndex_nontrivial hmin x
  let phi := directionFunctional A x
  let u := fun k : NeighborIndex A x ↦ direction k
  let p := positiveSectionFamily phi u
  have hphi : ∀ k, 0 < phi (u k) := directionFunctional_pos hA hmin x
  have hp : ∀ k, phi (p k) = 1 := fun k ↦
    positiveSectionPoint_linear_eq_one phi (hphi k)
  have hb : phi (radialAverageBase p) = 1 :=
    radialAverageBase_linear_eq_one phi hp
  apply sphericalRadialArc_injective_of_extreme phi hb hp
  · intro k
    exact positiveSectionPoint_not_mem_other_cone phi hphi
      (direction_not_mem_otherIndexed_cone hA hmin) k
  · exact radialAverageBase_decomposition p

theorem arc_mem_diameterConeRegion {d : ℕ} {A : Finset (Point d)}
    (hA : IsDiameterOne A)
    (hmin : ∀ v : {z // z ∈ A}, 2 ≤ (diameterGraph A).degree v)
    {x : {z // z ∈ A}} (i : NeighborIndex A x)
    {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    arc A x i t ∈ diameterConeRegion (↑A : Set (Point d)) (x : Point d) := by
  letI : Nontrivial (NeighborIndex A x) := neighborIndex_nontrivial hmin x
  let C := PointedCone.hull ℝ
    (diameterDirections (↑A : Set (Point d)) (x : Point d))
  have huC : ∀ k : NeighborIndex A x, direction k ∈ C := by
    intro k
    apply PointedCone.subset_hull
    exact ⟨k.1, k.1.prop, direction_unit k, rfl⟩
  have h := canonicalSphericalRadialArc_mem_sphereCone
    (directionFunctional A x) (fun k : NeighborIndex A x ↦ direction k)
    (directionFunctional_pos hA hmin x) C huC i ht0 ht1
  exact h

@[simp]
theorem arc_zero {d : ℕ} (A : Finset (Point d)) (x : {z // z ∈ A})
    (i : NeighborIndex A x) : arc A x i 0 = NormedSpace.normalize (base A x) := by
  exact canonicalSphericalRadialArc_zero _ _ i

@[simp]
theorem arc_one {d : ℕ} {A : Finset (Point d)}
    (hA : IsDiameterOne A)
    (hmin : ∀ v : {z // z ∈ A}, 2 ≤ (diameterGraph A).degree v)
    {x : {z // z ∈ A}} (i : NeighborIndex A x) :
    arc A x i 1 = direction i := by
  exact canonicalSphericalRadialArc_one _ _
    (directionFunctional_pos hA hmin x) direction_unit i

theorem continuous_arc {d : ℕ} {A : Finset (Point d)}
    (hA : IsDiameterOne A)
    (hmin : ∀ v : {z // z ∈ A}, 2 ≤ (diameterGraph A).degree v)
    {x : {z // z ∈ A}} (i : NeighborIndex A x) :
    Continuous (arc A x i) := by
  letI : Nontrivial (NeighborIndex A x) := neighborIndex_nontrivial hmin x
  let phi := directionFunctional A x
  let u := fun k : NeighborIndex A x ↦ direction k
  let p := positiveSectionFamily phi u
  have hphi : ∀ k, 0 < phi (u k) := directionFunctional_pos hA hmin x
  have hp : ∀ k, phi (p k) = 1 := fun k ↦
    positiveSectionPoint_linear_eq_one phi (hphi k)
  have hb : phi (radialAverageBase p) = 1 :=
    radialAverageBase_linear_eq_one phi hp
  exact continuous_sphericalRadialArc phi hb hp i

/-- A bundled accessible arc from the common interior base to a diameter
direction. -/
def path {d : ℕ} {A : Finset (Point d)}
    (hA : IsDiameterOne A)
    (hmin : ∀ v : {z // z ∈ A}, 2 ≤ (diameterGraph A).degree v)
    {x : {z // z ∈ A}} (i : NeighborIndex A x) :
    Path (NormedSpace.normalize (base A x)) (direction i) where
  toFun t := arc A x i (t : ℝ)
  continuous_toFun := (continuous_arc hA hmin i).comp continuous_subtype_val
  source' := arc_zero A x i
  target' := arc_one hA hmin i

theorem path_range_subset_region {d : ℕ} {A : Finset (Point d)}
    (hA : IsDiameterOne A)
    (hmin : ∀ v : {z // z ∈ A}, 2 ≤ (diameterGraph A).degree v)
    {x : {z // z ∈ A}} (i : NeighborIndex A x) :
    Set.range (path hA hmin i) ⊆
      diameterConeRegion (↑A : Set (Point d)) (x : Point d) := by
  rintro y ⟨t, rfl⟩
  exact arc_mem_diameterConeRegion hA hmin i t.prop.1 t.prop.2

/-- Distinct local drawing arcs have exactly their common base in common. -/
theorem path_ranges_inter_eq_singleton {d : ℕ} {A : Finset (Point d)}
    (hA : IsDiameterOne A)
    (hmin : ∀ v : {z // z ∈ A}, 2 ≤ (diameterGraph A).degree v)
    {x : {z // z ∈ A}} {i j : NeighborIndex A x} (hij : i ≠ j) :
    Set.range (path hA hmin i) ∩ Set.range (path hA hmin j) =
      {NormedSpace.normalize (base A x)} := by
  apply Set.Subset.antisymm
  · rintro z ⟨⟨t, rfl⟩, ⟨s, hts⟩⟩
    change arc A x j (s : ℝ) = arc A x i (t : ℝ) at hts
    by_cases ht0 : t = 0
    · subst t
      simp only [Set.mem_singleton_iff]
      exact arc_zero A x i
    by_cases hs0 : s = 0
    · subst s
      simp only [Set.mem_singleton_iff]
      change arc A x i (t : ℝ) = NormedSpace.normalize (base A x)
      rw [← hts]
      exact arc_zero A x j
    have htval : (t : ℝ) ≠ 0 := fun h ↦ ht0 (Subtype.ext h)
    have hsval : (s : ℝ) ≠ 0 := fun h ↦ hs0 (Subtype.ext h)
    have htpos : 0 < (t : ℝ) := lt_of_le_of_ne t.prop.1 (Ne.symm htval)
    have hspos : 0 < (s : ℝ) := lt_of_le_of_ne s.prop.1 (Ne.symm hsval)
    exact False.elim ((arc_pairwise_interior_disjoint hA hmin hij htpos hspos) hts.symm)
  · intro z hz
    rw [Set.mem_singleton_iff] at hz
    subst z
    constructor
    · refine ⟨0, ?_⟩
      exact arc_zero A x i
    · refine ⟨0, ?_⟩
      exact arc_zero A x j

end DiameterRadialFan

end

end Erdos223.SphericalEuler
