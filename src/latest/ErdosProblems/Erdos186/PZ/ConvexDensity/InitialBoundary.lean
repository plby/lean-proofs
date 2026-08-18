/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
import ErdosProblems.Erdos186.PZ.ConvexDensity.BoundaryWitnesses
import ErdosProblems.Erdos186.PZ.ConvexDensity.GridPartition
import ErdosProblems.Erdos186.PZ.ConvexDensity.RetainedFibers

/-! # From a heavy normalized grid shell to common-hull boundary witnesses -/

open Set

namespace Erdos186.PZ.ConvexDensity

set_option autoImplicit false
noncomputable section

open GridPartition

/-- A canonical point of a nonempty assignment fibre, with zero as the
irrelevant fallback outside the retained shell. -/
def gridFiberRepresentative {d : ℕ}
    (X : Finset (EuclideanPoint d)) (mesh : ℝ) (k : Fin d → ℕ) :
    EuclideanPoint d := by
  classical
  exact if h : (gridAssignmentFiberFinset X mesh k).Nonempty then h.choose else 0

theorem gridFiberRepresentative_mem {d : ℕ}
    {X : Finset (EuclideanPoint d)} {mesh : ℝ} {k : Fin d → ℕ}
    (hne : (gridAssignmentFiberFinset X mesh k).Nonempty) :
    gridFiberRepresentative X mesh k ∈ gridAssignmentFiberFinset X mesh k := by
  classical
  simp only [gridFiberRepresentative, dif_pos hne]
  exact hne.choose_spec

/-- The common hull used for the boundary witnesses is literally the retained
convex hull of the disjoint union of the selected assignment fibres.  This
identity lets both the small-volume branch and the final clipping constructor
use the same finite retained set. -/
theorem commonAssignmentFiberHull_eq_retainedConvexHull {d : ℕ}
    (X : Finset (EuclideanPoint d))
    (J : Finset (Fin d → ℕ)) (mesh : ℝ) :
    commonCellHull J
        (fun k ↦ (gridAssignmentFiberFinset X mesh k :
          Set (EuclideanPoint d))) =
      retainedConvexHull
        (retainedFiberUnion J (gridAssignmentFiberFinset X mesh)) := by
  have heq : retainedCells J
      (fun k ↦ (gridAssignmentFiberFinset X mesh k : Set (EuclideanPoint d))) =
      (retainedFiberUnion J (gridAssignmentFiberFinset X mesh) :
        Set (EuclideanPoint d)) := by
    ext z
    simp [mem_retainedCells_iff, mem_retainedFiberUnion]
  rw [commonCellHull, heq]
  rfl

/-- The common hull of finitely many finite assignment fibres is compact. -/
theorem isCompact_commonAssignmentFiberHull {d : ℕ}
    (X : Finset (EuclideanPoint d))
    (J : Finset (Fin d → ℕ)) (mesh : ℝ) :
    IsCompact (commonCellHull J
      (fun k ↦ (gridAssignmentFiberFinset X mesh k : Set (EuclideanPoint d)))) := by
  rw [commonAssignmentFiberHull_eq_retainedConvexHull]
  exact (retainedFiberUnion J
    (gridAssignmentFiberFinset X mesh)).finite_toSet.isCompact_convexHull ℝ

/-- Every cell of a positive-mass shell has a representative in `X` and in
its closed geometric grid box. -/
theorem gridFiberRepresentative_properties {d : ℕ}
    {X : Finset (EuclideanPoint d)} {mesh delta : ℝ}
    (hmesh : 0 < mesh) (hdelta : 0 < delta)
    (hXne : X.Nonempty)
    (hXcube : (X : Set (EuclideanPoint d)) ⊆ normalizedCube d)
    {J : Finset (Fin d → ℕ)}
    (hheavy : ∀ k ∈ J,
      delta * (X.card : ℝ) <
        DyadicCells.occupancy X (gridIndex mesh) k) :
    (∀ k ∈ J, gridFiberRepresentative X mesh k ∈ X) ∧
      (∀ k ∈ J,
        gridFiberRepresentative X mesh k ∈
          gridAssignmentFiberFinset X mesh k) := by
  have hcardPos : (0 : ℝ) < X.card := by
    exact_mod_cast Finset.card_pos.mpr hXne
  have hnonempty : ∀ k ∈ J,
      (gridAssignmentFiberFinset X mesh k).Nonempty := by
    intro k hk
    apply Finset.card_pos.mp
    rw [card_gridAssignmentFiberFinset]
    have hoccR : (0 : ℝ) <
        DyadicCells.occupancy X (gridIndex mesh) k :=
      (mul_pos hdelta hcardPos).trans (hheavy k hk)
    exact_mod_cast hoccR
  constructor
  · intro k hk
    exact (mem_gridAssignmentFiberFinset_iff.mp
      (gridFiberRepresentative_mem (hnonempty k hk))).1
  · intro k hk
    exact gridFiberRepresentative_mem (hnonempty k hk)

/-- Exact geometric output of the first regularized shell: one localized
frontier witness for every retained cell label, all on the frontier of one
common compact convex hull. -/
theorem exists_commonGridHull_boundaryWitnesses
    {d : ℕ} (hd : 0 < d)
    {X : Finset (EuclideanPoint d)} {mesh delta : ℝ}
    (hmesh : 0 < mesh) (hdelta : 0 < delta)
    (hXne : X.Nonempty)
    (hXcube : (X : Set (EuclideanPoint d)) ⊆ normalizedCube d)
    (hposition : ConvexGeometry.IsDeltaConvexPosition delta X)
    {J : Finset (Fin d → ℕ)}
    (hheavy : ∀ k ∈ J,
      delta * (X.card : ℝ) <
        DyadicCells.occupancy X (gridIndex mesh) k) :
    ∃ witness : {k // k ∈ J} → EuclideanPoint d,
      ∀ k : {k // k ∈ J},
        witness k ∈ Metric.closedBall (gridCenter mesh k.1)
          (3 * (Real.sqrt (d : ℝ) * (mesh / 2))) ∧
        witness k ∈ frontier (commonCellHull J
          (fun i ↦ (gridAssignmentFiberFinset X mesh i :
            Set (EuclideanPoint d)))) := by
  let rho : ℝ := Real.sqrt (d : ℝ) * (mesh / 2)
  have hrho : 0 < rho := by
    dsimp only [rho]
    positivity
  obtain ⟨haX, haC⟩ := gridFiberRepresentative_properties
    hmesh hdelta hXne hXcube hheavy
  apply exists_indexed_commonHullBoundaryWitnesses_of_heavy_cells
    (X := X) (delta := delta) (r := rho) (I := J)
    (C := fun k ↦ (gridAssignmentFiberFinset X mesh k :
      Set (EuclideanPoint d)))
    (Y := gridAssignmentFiberFinset X mesh)
    (center := gridCenter mesh)
    (a := gridFiberRepresentative X mesh)
  · exact hrho
  · exact hposition
  · exact haX
  · exact haC
  · intro k _hk
    exact gridAssignmentFiberFinset_subset X mesh k
  · intro k _hk z hz
    exact hz
  · intro k hk
    simpa [card_gridAssignmentFiberFinset] using hheavy k hk
  · intro k _hk z hz
    have hz' := (mem_gridAssignmentFiberFinset_iff.mp hz)
    have hzcell : z ∈ gridCell mesh k := by
      simpa [hz'.2] using mem_gridCell_gridIndex hmesh z (hXcube hz'.1)
    rw [Metric.mem_closedBall, dist_eq_norm]
    simpa only [rho] using norm_sub_gridCenter_le hmesh.le hzcell
  · exact isCompact_commonAssignmentFiberHull X J mesh

end
end Erdos186.PZ.ConvexDensity
