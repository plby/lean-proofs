/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
import ErdosProblems.Erdos186.ConvexApprox
import ErdosProblems.Erdos186.PZ.ConvexDensity.AxisBoxes

/-!
# A two-dimensional graph-slab density increment

This file is the planar (`d = 2`) instance of the graph approximation step
before Lemma 2 in Pham--Zakharov.  A finite family of points lies on the graph
of a bounded concave function.  A prescribed nonempty collection of grid
intervals is occupied by at least `K` points per interval.  Applying the
one-dimensional prescribed-cell approximation lemma to `1 - h` selects one
of those occupied intervals on which the graph lies in an explicit affine
slab.

The conclusion records all of the geometric information needed by the density
increment: the slab is convex, it contains every point over the selected cell,
it therefore contains at least `K` points, and its Euclidean area is exactly
base length times thickness.
-/

open Set MeasureTheory
open scoped ENNReal

namespace Erdos186.PZ.ConvexDensity

set_option autoImplicit false

noncomputable section

open Erdos186.ConvexApprox

/-- The `k`-th interval in the `m`-grid, viewed as an axis box in the
one-dimensional base of the planar graph. -/
def graphBaseCell (m k : ℕ) : Set (EuclideanPoint 1) :=
  closedAxisBox (fun _ => gridPoint m k) (fun _ => gridPoint m (k + 1))

@[simp]
theorem mem_graphBaseCell_iff {m k : ℕ} {x : EuclideanPoint 1} :
    x ∈ graphBaseCell m k ↔
      coordinate x 0 ∈ Set.Icc (gridPoint m k) (gridPoint m (k + 1)) := by
  simp [graphBaseCell, closedAxisBox, Set.mem_Icc]

/-- The points of `X` whose base coordinate belongs to the `k`-th grid
interval.  The separate graph hypothesis in the main theorem ensures that
their second coordinates equal `h` at their base coordinates. -/
def graphPointsOverCell (X : Finset (EuclideanPoint 1 × ℝ))
    (m k : ℕ) : Finset (EuclideanPoint 1 × ℝ) := by
  classical
  exact X.filter fun p => p.1 ∈ graphBaseCell m k

@[simp]
theorem mem_graphPointsOverCell_iff
    {X : Finset (EuclideanPoint 1 × ℝ)} {m k : ℕ}
    {p : EuclideanPoint 1 × ℝ} :
    p ∈ graphPointsOverCell X m k ↔
      p ∈ X ∧ p.1 ∈ graphBaseCell m k := by
  simp [graphPointsOverCell]

/-- The points of a planar finite set which lie in a specified region. -/
def planarPointsIn (X : Finset (EuclideanPoint 1 × ℝ))
    (S : Set (EuclideanPoint 1 × ℝ)) : Finset (EuclideanPoint 1 × ℝ) := by
  classical
  exact X.filter fun p => p ∈ S

@[simp]
theorem mem_planarPointsIn_iff
    {X : Finset (EuclideanPoint 1 × ℝ)}
    {S : Set (EuclideanPoint 1 × ℝ)} {p : EuclideanPoint 1 × ℝ} :
    p ∈ planarPointsIn X S ↔ p ∈ X ∧ p ∈ S := by
  simp [planarPointsIn]

/-- The affine function whose graph is the reflection about height `1/2` of
the secant line for the convex function `1 - h`. -/
def graphCellSecant (h : ℝ → ℝ) (m k : ℕ) :
    EuclideanPoint 1 →ᵃ[ℝ] ℝ where
  toFun x :=
    1 - cellSecant (fun t => 1 - h t) m k (coordinate x 0)
  linear := {
    toFun := fun x =>
      -gridSlope (fun t => 1 - h t) m (k + 1) * coordinate x 0
    map_add' := by
      intro x y
      simp only [coordinate, WithLp.ofLp_add, Pi.add_apply]
      ring
    map_smul' := by
      intro r x
      simp only [coordinate, WithLp.ofLp_smul, Pi.smul_apply, smul_eq_mul,
        RingHom.id_apply]
      ring }
  map_vadd' p v := by
    change
      1 - cellSecant (fun t => 1 - h t) m k
          (coordinate (v + p) 0) =
        (-gridSlope (fun t => 1 - h t) m (k + 1) * coordinate v 0) +
          (1 - cellSecant (fun t => 1 - h t) m k (coordinate p 0))
    simp only [cellSecant, coordinate, WithLp.ofLp_add, Pi.add_apply]
    ring

@[simp]
theorem graphCellSecant_apply (h : ℝ → ℝ) (m k : ℕ)
    (x : EuclideanPoint 1) :
    graphCellSecant h m k x =
      1 - cellSecant (fun t => 1 - h t) m k (coordinate x 0) :=
  rfl

/-- **Planar occupied-graph slab theorem.**

Let `h : [-c,1+c] -> [0,1]` be concave and let every interval indexed by the
nonempty prescribed family `I` contain at least `K` points of `X`.  If all
points of `X` lie on the graph of `h`, then one prescribed interval has the
following explicit density increment.  The entire cell fibre of `X` is
contained in the affine slab of half-width

`2 / (c * m * I.card)`,

the slab is convex, it contains at least `K` points, and its Euclidean area is
exactly `(1/m)` times its vertical thickness.
-/
theorem exists_occupied_graph_cell_affine_slab
    {h : ℝ → ℝ} {c : ℝ} {m K : ℕ}
    (hm : 0 < m) (hmargin : (m : ℝ)⁻¹ < c)
    (hconcave : ConcaveOn ℝ (Set.Icc (-c) (1 + c)) h)
    (hrange : ∀ x ∈ Set.Icc (-c) (1 + c), 0 ≤ h x ∧ h x ≤ 1)
    (X : Finset (EuclideanPoint 1 × ℝ))
    (hgraph : ∀ p ∈ X, p.2 = h (coordinate p.1 0))
    (I : Finset ℕ) (hI : I.Nonempty) (hIgrid : I ⊆ Finset.range m)
    (hoccupied : ∀ k ∈ I, K ≤ (graphPointsOverCell X m k).card) :
    ∃ k ∈ I,
      let epsilon := 2 / (c * (m : ℝ) * (I.card : ℝ))
      let slab := affineGraphSlab (graphBaseCell m k)
        (graphCellSecant h m k) epsilon
      (graphPointsOverCell X m k : Set (EuclideanPoint 1 × ℝ)) ⊆ slab ∧
        Convex ℝ slab ∧
        K ≤ (planarPointsIn X slab).card ∧
        volume slab =
          ENNReal.ofReal ((m : ℝ)⁻¹) *
            ENNReal.ofReal (4 / (c * (m : ℝ) * (I.card : ℝ))) := by
  have hfconvex :
      ConvexOn ℝ (Set.Icc (-c) (1 + c)) (fun x => 1 - h x) := by
    apply (hconcave.neg.add_const (1 : ℝ)).congr
    intro x hx
    simp only [Pi.add_apply, Pi.neg_apply]
    ring
  have hfrange : ∀ x ∈ Set.Icc (-c) (1 + c),
      0 ≤ (1 - h x) ∧ (1 - h x) ≤ 1 := by
    intro x hx
    have hh := hrange x hx
    constructor <;> linarith
  obtain ⟨k, hkI, hkapprox⟩ :=
    exists_cell_affine_approximation hm hmargin hfconvex hfrange I hI hIgrid
  refine ⟨k, hkI, ?_⟩
  dsimp only
  have hc : 0 < c := by
    have hinv : 0 ≤ (m : ℝ)⁻¹ := inv_nonneg.mpr (by positivity)
    linarith
  have hcard : 0 < (I.card : ℝ) := by
    exact_mod_cast hI.card_pos
  have hepsilon : 0 ≤ 2 / (c * (m : ℝ) * (I.card : ℝ)) := by
    positivity
  have hsubset :
      (graphPointsOverCell X m k : Set (EuclideanPoint 1 × ℝ)) ⊆
        affineGraphSlab (graphBaseCell m k) (graphCellSecant h m k)
          (2 / (c * (m : ℝ) * (I.card : ℝ))) := by
    intro p hp
    have hp' := mem_graphPointsOverCell_iff.mp hp
    have hpbase := mem_graphBaseCell_iff.mp hp'.2
    have happ := hkapprox (coordinate p.1 0) hpbase
    have habs :
        |h (coordinate p.1 0) - graphCellSecant h m k p.1| ≤
          2 / (c * (m : ℝ) * (I.card : ℝ)) := by
      rw [graphCellSecant_apply]
      rw [show
        h (coordinate p.1 0) -
              (1 - cellSecant (fun t => 1 - h t) m k (coordinate p.1 0)) =
            -((1 - h (coordinate p.1 0)) -
              cellSecant (fun t => 1 - h t) m k (coordinate p.1 0)) by ring,
        abs_neg]
      exact happ
    have hpgraph := hgraph p hp'.1
    refine ⟨hp'.2, ?_, ?_⟩
    · rw [hpgraph]
      have := (abs_le.mp habs).1
      linarith
    · rw [hpgraph]
      have := (abs_le.mp habs).2
      linarith
  refine ⟨hsubset, ?_, ?_, ?_⟩
  · exact convex_affineGraphSlab
      (convex_closedAxisBox (fun _ : Fin 1 => gridPoint m k)
        (fun _ : Fin 1 => gridPoint m (k + 1)))
      (graphCellSecant h m k) _
  · apply (hoccupied k hkI).trans
    apply Finset.card_le_card
    intro p hp
    rw [mem_planarPointsIn_iff]
    exact ⟨(mem_graphPointsOverCell_iff.mp hp).1, hsubset hp⟩
  · change
      volume (affineGraphSlab
        (closedAxisBox (fun _ : Fin 1 => gridPoint m k)
          (fun _ : Fin 1 => gridPoint m (k + 1)))
        (graphCellSecant h m k)
        (2 / (c * (m : ℝ) * (I.card : ℝ)))) = _
    rw [volume_affineGraphSlab_closedAxisBox
      (fun _ : Fin 1 => gridPoint m k)
      (fun _ : Fin 1 => gridPoint m (k + 1))
      (graphCellSecant h m k) hepsilon]
    simp only [Fin.prod_univ_succ, Fin.prod_univ_zero, mul_one]
    rw [gridPoint_succ hm]
    rw [show gridPoint m k + (m : ℝ)⁻¹ - gridPoint m k =
      (m : ℝ)⁻¹ by ring]
    rw [show
      (2 : ℝ) * (2 / (c * (m : ℝ) * (I.card : ℝ))) =
        4 / (c * (m : ℝ) * (I.card : ℝ)) by ring]

end

end Erdos186.PZ.ConvexDensity
