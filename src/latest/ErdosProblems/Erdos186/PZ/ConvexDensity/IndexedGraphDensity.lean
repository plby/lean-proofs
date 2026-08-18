/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
import ErdosProblems.Erdos186.PZ.ConvexDensity.GraphDensity2DAmbient

/-! # Label-preserving occupied graph slabs -/

open Set MeasureTheory
open scoped ENNReal BigOperators

namespace Erdos186.PZ.ConvexDensity

set_option autoImplicit false
noncomputable section

open Subgradient Erdos186.ConvexApprox

def indexedLabelsOverCellND {ι : Type*} [DecidableEq ι] {n m : ℕ}
    (J : Finset ι) (z : ι → EuclideanPoint (n + 1))
    (v : Fin n → Fin m) : Finset ι := by
  classical
  exact J.filter fun i ↦ baseCoordinates (z i) ∈ graphBaseCellND v

@[simp]
theorem mem_indexedLabelsOverCellND_iff
    {ι : Type*} [DecidableEq ι] {n m : ℕ}
    {J : Finset ι} {z : ι → EuclideanPoint (n + 1)}
    {v : Fin n → Fin m} {i : ι} :
    i ∈ indexedLabelsOverCellND J z v ↔
      i ∈ J ∧ baseCoordinates (z i) ∈ graphBaseCellND v := by
  classical
  simp [indexedLabelsOverCellND]

/-- The higher-dimensional graph slab, with the second grid formed from
source labels rather than an image finset of their witnesses. -/
theorem exists_indexed_upperBoundary_affine_slab_nd
    {ι : Type*} [DecidableEq ι] {n m K : ℕ}
    (hn : 2 ≤ n) (hm : 0 < m) {c : ℝ}
    (hc : 2 * ((n : ℝ) + 1) / (m : ℝ) < c)
    {h : (Fin n → ℝ) → ℝ}
    (hconcave : ConcaveOn ℝ (pzExpandedBox n c) h)
    (hrange : ∀ x ∈ pzExpandedBox n c, h x ∈ Set.Icc (0 : ℝ) 1)
    (J : Finset ι) (z : ι → EuclideanPoint (n + 1))
    (hgraph : ∀ i ∈ J,
      lastCoordinate (z i) = h (WithLp.ofLp (baseCoordinates (z i))))
    (I : Finset (Fin n → Fin m)) (hI : I.Nonempty)
    (hoccupied : ∀ v ∈ I, K ≤ (indexedLabelsOverCellND J z v).card) :
    ∃ v ∈ I, ∃ p : Fin n → ℝ,
      let epsilon :=
        4 * ((n : ℝ) + 1) ^ 4 * (m : ℝ) ^ (n - 2) /
          (c * (I.card : ℝ))
      let L := reflectedTangentAffine (fun x ↦ 1 - h x)
        (pzFinGridPoint v) p
      let slab := affineGraphSlab (graphBaseCellND v) L epsilon
      (∀ i, |p i| ≤ 2 / c) ∧
        (∀ i ∈ indexedLabelsOverCellND J z v,
          lastCoordinateCLE n (z i) ∈ slab) ∧
        Convex ℝ slab ∧
        K ≤ (indexedLabelsOverCellND J z v).card ∧
        volume slab =
          (∏ _i : Fin n, ENNReal.ofReal ((m : ℝ)⁻¹)) *
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
  obtain ⟨v, hvI, p, _hsupport, hp, happrox⟩ :=
    exists_gridCell_tangentAffine_approximation_with_coeff_bound
      hn hm hc hf hfrange I hI
  refine ⟨v, hvI, p, hp, ?_, ?_, hoccupied v hvI, ?_⟩
  · intro i hi
    have hi' := mem_indexedLabelsOverCellND_iff.mp hi
    have hzcell : WithLp.ofLp (baseCoordinates (z i)) ∈ pzGridCell v :=
      mem_graphBaseCellND_iff.mp hi'.2
    have happ := happrox _ hzcell
    have habs :
        |h (WithLp.ofLp (baseCoordinates (z i))) -
          reflectedTangentAffine f (pzFinGridPoint v) p
            (baseCoordinates (z i))| ≤
          4 * ((n : ℝ) + 1) ^ 4 * (m : ℝ) ^ (n - 2) /
            (c * (I.card : ℝ)) := by
      change |h (WithLp.ofLp (baseCoordinates (z i))) -
        (1 - ConvexApproxND.tangentAffine f (pzFinGridPoint v) p
          (WithLp.ofLp (baseCoordinates (z i))))| ≤ _
      rw [show h (WithLp.ofLp (baseCoordinates (z i))) -
          (1 - ConvexApproxND.tangentAffine f (pzFinGridPoint v) p
            (WithLp.ofLp (baseCoordinates (z i)))) =
        -(f (WithLp.ofLp (baseCoordinates (z i))) -
          ConvexApproxND.tangentAffine f (pzFinGridPoint v) p
            (WithLp.ofLp (baseCoordinates (z i)))) by
          dsimp only [f]
          ring, abs_neg]
      exact happ
    rw [lastCoordinateCLE_apply]
    refine ⟨hi'.2, ?_, ?_⟩
    · rw [hgraph i hi'.1]
      linarith [(abs_le.mp habs).1]
    · rw [hgraph i hi'.1]
      linarith [(abs_le.mp habs).2]
  · exact convex_affineGraphSlab
      (convex_closedAxisBox (pzFinGridPoint v)
        (fun i ↦ pzFinGridPoint v i + 1 / (m : ℝ)))
      (reflectedTangentAffine f (pzFinGridPoint v) p) _
  · have hcpos : 0 < c := by
      have : 0 < 2 * ((n : ℝ) + 1) / (m : ℝ) := by positivity
      linarith
    have hIcard : 0 < (I.card : ℝ) := by exact_mod_cast hI.card_pos
    have hepsilon : 0 ≤
        4 * ((n : ℝ) + 1) ^ 4 * (m : ℝ) ^ (n - 2) /
          (c * (I.card : ℝ)) := by positivity
    change volume (affineGraphSlab
      (closedAxisBox (pzFinGridPoint v)
        (fun i ↦ pzFinGridPoint v i + 1 / (m : ℝ)))
      (reflectedTangentAffine f (pzFinGridPoint v) p)
      (4 * ((n : ℝ) + 1) ^ 4 * (m : ℝ) ^ (n - 2) /
        (c * (I.card : ℝ)))) = _
    rw [volume_affineGraphSlab_closedAxisBox
      (pzFinGridPoint v)
      (fun i ↦ pzFinGridPoint v i + 1 / (m : ℝ))
      (reflectedTangentAffine f (pzFinGridPoint v) p) hepsilon]
    congr 2
    funext i
    congr 1
    rw [show pzFinGridPoint v i + 1 / (m : ℝ) - pzFinGridPoint v i =
      (m : ℝ)⁻¹ by rw [one_div]; ring]

def indexedLabelsOverCell1D {ι : Type*} [DecidableEq ι]
    (J : Finset ι) (z : ι → EuclideanPoint 2) (m k : ℕ) : Finset ι := by
  classical
  exact J.filter fun i ↦ baseCoordinates (z i) ∈ graphBaseCell m k

@[simp]
theorem mem_indexedLabelsOverCell1D_iff
    {ι : Type*} [DecidableEq ι] {J : Finset ι}
    {z : ι → EuclideanPoint 2} {m k : ℕ} {i : ι} :
    i ∈ indexedLabelsOverCell1D J z m k ↔
      i ∈ J ∧ baseCoordinates (z i) ∈ graphBaseCell m k := by
  classical
  simp [indexedLabelsOverCell1D]

/-- The planar graph slab with occupancy and containment stated on source
labels, so coincident boundary witnesses do not collapse. -/
theorem exists_indexed_upperBoundary_affine_slab_2d
    {ι : Type*} [DecidableEq ι] {m K : ℕ}
    (hm : 0 < m) {c : ℝ} (hmargin : (m : ℝ)⁻¹ < c)
    {h : ℝ → ℝ}
    (hconcave : ConcaveOn ℝ (Set.Icc (-c) (1 + c)) h)
    (hrange : ∀ x ∈ Set.Icc (-c) (1 + c), 0 ≤ h x ∧ h x ≤ 1)
    (J : Finset ι) (z : ι → EuclideanPoint 2)
    (hgraph : ∀ i ∈ J,
      lastCoordinate (z i) = h (coordinate (baseCoordinates (z i)) 0))
    (I : Finset ℕ) (hI : I.Nonempty) (hIgrid : I ⊆ Finset.range m)
    (hoccupied : ∀ k ∈ I, K ≤ (indexedLabelsOverCell1D J z m k).card) :
    ∃ k ∈ I,
      let epsilon := 2 / (c * (m : ℝ) * (I.card : ℝ))
      let L := graphCellSecant h m k
      let slab := affineGraphSlab (graphBaseCell m k) L epsilon
      (∀ i, |affineCoordinateCoefficient L i| ≤ 1 / c) ∧
        (∀ i ∈ indexedLabelsOverCell1D J z m k,
          lastCoordinateCLE 1 (z i) ∈ slab) ∧
        Convex ℝ slab ∧
        K ≤ (indexedLabelsOverCell1D J z m k).card ∧
        volume slab = ENNReal.ofReal ((m : ℝ)⁻¹) *
          ENNReal.ofReal (4 / (c * (m : ℝ) * (I.card : ℝ))) := by
  let f : ℝ → ℝ := fun x ↦ 1 - h x
  have hf : ConvexOn ℝ (Set.Icc (-c) (1 + c)) f := by
    apply (hconcave.neg.add_const (1 : ℝ)).congr
    intro x hx
    simp only [f, Pi.add_apply, Pi.neg_apply]
    ring
  have hfrange : ∀ x ∈ Set.Icc (-c) (1 + c), 0 ≤ f x ∧ f x ≤ 1 := by
    intro x hx
    have hh := hrange x hx
    dsimp only [f]
    constructor <;> linarith
  obtain ⟨k, hkI, happrox⟩ :=
    exists_cell_affine_approximation hm hmargin hf hfrange I hI hIgrid
  refine ⟨k, hkI, ?_, ?_, ?_, hoccupied k hkI, ?_⟩
  · intro i
    have hi : i = (0 : Fin 1) := Subsingleton.elim _ _
    subst i
    exact abs_affineCoordinateCoefficient_graphCellSecant_le hm hmargin
      (Finset.mem_range.mp (hIgrid hkI)) hconcave hrange
  · intro i hi
    have hi' := mem_indexedLabelsOverCell1D_iff.mp hi
    have hx := mem_graphBaseCell_iff.mp hi'.2
    have happ := happrox (coordinate (baseCoordinates (z i)) 0) hx
    have habs :
        |h (coordinate (baseCoordinates (z i)) 0) -
          graphCellSecant h m k (baseCoordinates (z i))| ≤
          2 / (c * (m : ℝ) * (I.card : ℝ)) := by
      rw [graphCellSecant_apply]
      rw [show h (coordinate (baseCoordinates (z i)) 0) -
            (1 - cellSecant f m k (coordinate (baseCoordinates (z i)) 0)) =
          -(f (coordinate (baseCoordinates (z i)) 0) -
            cellSecant f m k (coordinate (baseCoordinates (z i)) 0)) by
            dsimp only [f]
            ring, abs_neg]
      exact happ
    rw [lastCoordinateCLE_apply]
    refine ⟨hi'.2, ?_, ?_⟩
    · rw [hgraph i hi'.1]
      linarith [(abs_le.mp habs).1]
    · rw [hgraph i hi'.1]
      linarith [(abs_le.mp habs).2]
  · exact convex_affineGraphSlab
      (convex_closedAxisBox (fun _ : Fin 1 ↦ gridPoint m k)
        (fun _ : Fin 1 ↦ gridPoint m (k + 1)))
      (graphCellSecant h m k) _
  · have hc : 0 < c :=
      lt_of_le_of_lt (inv_nonneg.mpr (by positivity)) hmargin
    have hcard : 0 < (I.card : ℝ) := by exact_mod_cast hI.card_pos
    have hepsilon : 0 ≤ 2 / (c * (m : ℝ) * (I.card : ℝ)) := by positivity
    change volume (affineGraphSlab
      (closedAxisBox (fun _ : Fin 1 ↦ gridPoint m k)
        (fun _ : Fin 1 ↦ gridPoint m (k + 1)))
      (graphCellSecant h m k)
      (2 / (c * (m : ℝ) * (I.card : ℝ)))) = _
    rw [volume_affineGraphSlab_closedAxisBox
      (fun _ : Fin 1 ↦ gridPoint m k)
      (fun _ : Fin 1 ↦ gridPoint m (k + 1))
      (graphCellSecant h m k) hepsilon]
    simp only [Fin.prod_univ_succ, Fin.prod_univ_zero, mul_one]
    rw [gridPoint_succ hm]
    rw [show gridPoint m k + (m : ℝ)⁻¹ - gridPoint m k =
      (m : ℝ)⁻¹ by ring]
    rw [show (2 : ℝ) * (2 / (c * (m : ℝ) * (I.card : ℝ))) =
      4 / (c * (m : ℝ) * (I.card : ℝ)) by ring]

end
end Erdos186.PZ.ConvexDensity
