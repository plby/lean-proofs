/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
import ErdosProblems.Erdos186.PZ.ConvexDensity.AxisBoxes
import ErdosProblems.Erdos186.PZ.ConvexDensity.ConvexApproximation

/-!
# Higher-dimensional occupied graph slabs

This file connects the all-dimensional prescribed-cell approximation theorem
to the geometric object used in the Pham--Zakharov density increment.  Among
any prescribed nonempty family of occupied base-grid cells, it selects one
whose points on a bounded concave graph lie in an explicit convex affine
slab.  The result retains the coefficient bound needed when the slab is later
thickened by the original small spatial cells.
-/

open Set MeasureTheory
open scoped ENNReal BigOperators

namespace Erdos186.PZ.ConvexDensity

set_option autoImplicit false

noncomputable section

open Subgradient

/-- The Euclidean realization of a base cell used by
`Subgradient.pzGridCell`. -/
def graphBaseCellND {n m : ℕ} (v : Fin n → Fin m) :
    Set (EuclideanPoint n) :=
  closedAxisBox (pzFinGridPoint v)
    (fun i ↦ pzFinGridPoint v i + 1 / (m : ℝ))

@[simp]
theorem mem_graphBaseCellND_iff {n m : ℕ} {v : Fin n → Fin m}
    {x : EuclideanPoint n} :
    x ∈ graphBaseCellND v ↔ WithLp.ofLp x ∈ pzGridCell v := by
  constructor
  · intro hx
    exact ⟨fun i ↦ (hx i).1, fun i ↦ (hx i).2⟩
  · rintro ⟨hlower, hupper⟩ i
    exact ⟨hlower i, hupper i⟩

/-- Points whose base projection lies in a specified finite grid cell. -/
def graphPointsOverCellND {n m : ℕ}
    (X : Finset (EuclideanPoint n × ℝ)) (v : Fin n → Fin m) :
    Finset (EuclideanPoint n × ℝ) := by
  classical
  exact X.filter fun z ↦ z.1 ∈ graphBaseCellND v

@[simp]
theorem mem_graphPointsOverCellND_iff {n m : ℕ}
    {X : Finset (EuclideanPoint n × ℝ)} {v : Fin n → Fin m}
    {z : EuclideanPoint n × ℝ} :
    z ∈ graphPointsOverCellND X v ↔
      z ∈ X ∧ z.1 ∈ graphBaseCellND v := by
  simp [graphPointsOverCellND]

/-- Points of a finite graph set lying in an arbitrary region. -/
def graphPointsInND {n : ℕ} (X : Finset (EuclideanPoint n × ℝ))
    (S : Set (EuclideanPoint n × ℝ)) :
    Finset (EuclideanPoint n × ℝ) := by
  classical
  exact X.filter fun z ↦ z ∈ S

@[simp]
theorem mem_graphPointsInND_iff {n : ℕ}
    {X : Finset (EuclideanPoint n × ℝ)}
    {S : Set (EuclideanPoint n × ℝ)} {z : EuclideanPoint n × ℝ} :
    z ∈ graphPointsInND X S ↔ z ∈ X ∧ z ∈ S := by
  simp [graphPointsInND]

/-- Reflection of a tangent affine model for `f = 1 - h`; its graph is the
affine model for the concave function `h`. -/
def reflectedTangentAffine {n : ℕ} (f : (Fin n → ℝ) → ℝ)
    (v p : Fin n → ℝ) : EuclideanPoint n →ᵃ[ℝ] ℝ where
  toFun x := 1 - ConvexApproxND.tangentAffine f v p (WithLp.ofLp x)
  linear :=
    { toFun := fun x ↦ -∑ i, p i * coordinate x i
      map_add' := by
        intro x y
        simp only [coordinate, WithLp.ofLp_add, Pi.add_apply]
        simp_rw [mul_add]
        rw [Finset.sum_add_distrib]
        ring
      map_smul' := by
        intro a x
        simp only [coordinate, WithLp.ofLp_smul, Pi.smul_apply,
          smul_eq_mul, RingHom.id_apply]
        have hsum : (∑ i, p i * (a * WithLp.ofLp x i)) =
            a * ∑ i, p i * WithLp.ofLp x i := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro i hi
          ring
        rw [hsum]
        ring }
  map_vadd' x y := by
    change
      1 - (f v + ∑ i, p i * (WithLp.ofLp (y + x) i - v i)) =
        (-∑ i, p i * WithLp.ofLp y i) +
          (1 - (f v + ∑ i, p i * (WithLp.ofLp x i - v i)))
    simp only [WithLp.ofLp_add, Pi.add_apply]
    simp only [mul_sub, mul_add, Finset.sum_add_distrib,
      Finset.sum_sub_distrib]
    ring

@[simp]
theorem reflectedTangentAffine_apply {n : ℕ}
    (f : (Fin n → ℝ) → ℝ) (v p : Fin n → ℝ)
    (x : EuclideanPoint n) :
    reflectedTangentAffine f v p x =
      1 - ConvexApproxND.tangentAffine f v p (WithLp.ofLp x) :=
  rfl

/-- **Higher-dimensional occupied-graph slab theorem.**

For `n ≥ 2`, let a finite set lie on a `[0,1]`-valued concave graph over
the unit `n`-cube.  Suppose every cell in a prescribed nonempty family `I`
contains at least `K` points.  One of those cells admits a supporting affine
model whose coefficient size is at most `2/c`, and every graph point over the
cell lies in the affine slab of half-width

`4 (n+1)^4 m^(n-2) / (c |I|)`.

The conclusion includes convexity, the retained point count, and the exact
Lebesgue volume of the slab. -/
theorem exists_occupied_graph_cell_affine_slab_nd
    {n m K : ℕ} (hn : 2 ≤ n) (hm : 0 < m) {c : ℝ}
    (hc : 2 * ((n : ℝ) + 1) / (m : ℝ) < c)
    {h : (Fin n → ℝ) → ℝ}
    (hconcave : ConcaveOn ℝ (pzExpandedBox n c) h)
    (hrange : ∀ x ∈ pzExpandedBox n c, h x ∈ Set.Icc (0 : ℝ) 1)
    (X : Finset (EuclideanPoint n × ℝ))
    (hgraph : ∀ z ∈ X, z.2 = h (WithLp.ofLp z.1))
    (I : Finset (Fin n → Fin m)) (hI : I.Nonempty)
    (hoccupied : ∀ v ∈ I, K ≤ (graphPointsOverCellND X v).card) :
    ∃ v ∈ I, ∃ p : Fin n → ℝ,
      let epsilon :=
        4 * ((n : ℝ) + 1) ^ 4 * (m : ℝ) ^ (n - 2) /
          (c * (I.card : ℝ))
      let L := reflectedTangentAffine (fun x ↦ 1 - h x)
        (pzFinGridPoint v) p
      let slab := affineGraphSlab (graphBaseCellND v) L epsilon
      (∀ i, |p i| ≤ 2 / c) ∧
        (graphPointsOverCellND X v : Set (EuclideanPoint n × ℝ)) ⊆ slab ∧
        Convex ℝ slab ∧
        K ≤ (graphPointsInND X slab).card ∧
        volume slab =
          (∏ i : Fin n, ENNReal.ofReal ((m : ℝ)⁻¹)) *
            ENNReal.ofReal (2 * epsilon) := by
  let f : (Fin n → ℝ) → ℝ := fun x ↦ 1 - h x
  have hf : ConvexOn ℝ (pzExpandedBox n c) f := by
    apply (hconcave.neg.add_const (1 : ℝ)).congr
    intro x hx
    simp only [f, Pi.add_apply, Pi.neg_apply]
    ring
  have hfrange : ∀ x ∈ pzExpandedBox n c, f x ∈ Set.Icc (0 : ℝ) 1 := by
    intro x hx
    have hh := hrange x hx
    dsimp only [f]
    exact ⟨sub_nonneg.mpr hh.2, by linarith [hh.1]⟩
  obtain ⟨v, hvI, p, hsupport, hp, happrox⟩ :=
    exists_gridCell_tangentAffine_approximation_with_coeff_bound
      hn hm hc hf hfrange I hI
  refine ⟨v, hvI, p, ?_⟩
  dsimp only
  let epsilon : ℝ :=
    4 * ((n : ℝ) + 1) ^ 4 * (m : ℝ) ^ (n - 2) /
      (c * (I.card : ℝ))
  let L : EuclideanPoint n →ᵃ[ℝ] ℝ :=
    reflectedTangentAffine f (pzFinGridPoint v) p
  let slab : Set (EuclideanPoint n × ℝ) :=
    affineGraphSlab (graphBaseCellND v) L epsilon
  have hcpos : 0 < c := by
    have : 0 < 2 * ((n : ℝ) + 1) / (m : ℝ) := by positivity
    linarith
  have hIcard : 0 < (I.card : ℝ) := by
    exact_mod_cast hI.card_pos
  have hepsilon : 0 ≤ epsilon := by
    dsimp only [epsilon]
    positivity
  have hsubset :
      (graphPointsOverCellND X v : Set (EuclideanPoint n × ℝ)) ⊆ slab := by
    intro z hz
    have hz' := mem_graphPointsOverCellND_iff.mp hz
    have hzcell : WithLp.ofLp z.1 ∈ pzGridCell v :=
      mem_graphBaseCellND_iff.mp hz'.2
    have happ := happrox (WithLp.ofLp z.1) hzcell
    have habs : |h (WithLp.ofLp z.1) - L z.1| ≤ epsilon := by
      change |h (WithLp.ofLp z.1) -
        (1 - ConvexApproxND.tangentAffine f (pzFinGridPoint v) p
          (WithLp.ofLp z.1))| ≤ epsilon
      rw [show h (WithLp.ofLp z.1) -
          (1 - ConvexApproxND.tangentAffine f (pzFinGridPoint v) p
            (WithLp.ofLp z.1)) =
        -(f (WithLp.ofLp z.1) -
          ConvexApproxND.tangentAffine f (pzFinGridPoint v) p
            (WithLp.ofLp z.1)) by
        dsimp only [f]
        ring, abs_neg]
      exact happ
    have hzgraph := hgraph z hz'.1
    refine ⟨hz'.2, ?_, ?_⟩
    · rw [hzgraph]
      linarith [(abs_le.mp habs).1]
    · rw [hzgraph]
      linarith [(abs_le.mp habs).2]
  refine ⟨hp, hsubset, ?_, ?_, ?_⟩
  · exact convex_affineGraphSlab
      (convex_closedAxisBox (pzFinGridPoint v)
        (fun i ↦ pzFinGridPoint v i + 1 / (m : ℝ))) L epsilon
  · apply (hoccupied v hvI).trans
    apply Finset.card_le_card
    intro z hz
    rw [mem_graphPointsInND_iff]
    exact ⟨(mem_graphPointsOverCellND_iff.mp hz).1, hsubset hz⟩
  · change volume (affineGraphSlab (graphBaseCellND v) L epsilon) = _
    rw [show graphBaseCellND v =
        closedAxisBox (pzFinGridPoint v)
          (fun i ↦ pzFinGridPoint v i + 1 / (m : ℝ)) by rfl]
    rw [volume_affineGraphSlab_closedAxisBox
      (pzFinGridPoint v)
      (fun i ↦ pzFinGridPoint v i + 1 / (m : ℝ)) L hepsilon]
    congr 2
    funext i
    congr 1
    rw [show pzFinGridPoint v i + 1 / (m : ℝ) - pzFinGridPoint v i =
      (m : ℝ)⁻¹ by
      rw [one_div]
      ring]

end

end Erdos186.PZ.ConvexDensity
