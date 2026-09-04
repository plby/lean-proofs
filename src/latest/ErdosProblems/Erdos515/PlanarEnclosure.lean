/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
import Wikipedia.SchoenfliesTheorem.SquareCycle
import Wikipedia.SchoenfliesTheorem.FaceCyclesLand

/-!
# Jordan enclosures of planar paths

A compact path carried by an open subset of the plane is surrounded by a polygonal Jordan
curve carried by the same open set.  The construction covers a sufficiently fine subdivision
of the path by small axis-parallel squares.  Their overlaid boundaries form a finite
two-connected plane graph.  The cycle bounding its unbounded face is the required curve.
-/

open Bornology Metric Set unitInterval
open scoped Graph

namespace Schoenflies

/-- A continuous planar path image contained in an open set admits a Jordan enclosure whose
carrier is contained in that open set.  No injectivity of the path is required. -/
theorem exists_jordan_enclosure_of_continuousOn
    {D : Set Plane} (hD : IsOpen D) {α : ℝ → Plane} (hα : ContinuousOn α I)
    (hαD : α '' I ⊆ D) :
    ∃ C : Set Plane, IsJordanCurve C ∧ α '' I ⊆ C ∪ inside C ∧ C ⊆ D := by
  have hcompact : IsCompact (α '' I) :=
    isCompact_image_of_subset_I hα subset_rfl isCompact_I.isClosed
  obtain ⟨ρ, hρ, hthick⟩ := Plane.exists_thickening_subset hcompact hD hαD
  set r : ℝ := ρ / 4 with hr_def
  have hr : 0 < r := by rw [hr_def]; linarith
  obtain ⟨N, hN, hmesh⟩ := exists_mesh hα hr 1 (by omega)
  simp only [one_mul] at hmesh
  let c : ℕ → Plane := fun j => α (sample N j)
  have hc (j : ℕ) : c j = α (sample N j) := rfl
  have hstep : ∀ q < N, Plane.supDist (c q) (c (q + 1)) < r := by
    intro q hq
    have hs : sample N (q + 1) ∈ Icc (sample N q) (sample N (q + 1)) :=
      ⟨sample_mono (Nat.le_succ q), le_rfl⟩
    rw [hc, hc]
    have hm : dist (α (sample N (q + 1))) (α (sample N q)) < r :=
      hmesh q hq (sample N (q + 1)) hs
    have hle : Plane.supDist (α (sample N q)) (α (sample N (q + 1))) ≤
        dist (α (sample N q)) (α (sample N (q + 1))) :=
      Plane.supDist_eq_dist_le _ _
    rw [dist_comm] at hm
    exact hle.trans_lt hm
  let H : Graph Plane Piece := familyChain c N N r 0
  have hH2 : H.IsTwoConnected := by
    dsimp only [H]
    exact familyChain_isTwoConnected squaresTwoConnected hr (by simp) hstep
  have hHle : H ≤ familyOverlay c N r := by
    dsimp only [H]
    exact familyChain_le
  have hdraw : Graph.IsDrawing H segmentDrawing :=
    (familyOverlay_isDrawing (c := c) (N := N) hr).mono hHle
  let : H.Finite := by
    dsimp only [H]
    exact familyChain_finite
  have hpoly : ∀ g ∈ E(H), IsPolygonal (Graph.edgeArc segmentDrawing g) := by
    intro g hg
    rw [edgeArc_segmentDrawing]
    exact isPolygonal_segment g.1 g.2
  have hsqrt : Real.sqrt 2 < 2 := by
    nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2), Real.sqrt_nonneg 2]
  have hpointD : Graph.pointSet H segmentDrawing ⊆ D := by
    intro z hz
    obtain ⟨j, hj0, hjN, hzj⟩ :=
      exists_mem_frontier_of_mem_pointSet_familyChain (c := c) (N := N) (m := N)
        (r := r) (i := 0) hz
    have hjN' : j ≤ N := by simpa using hjN
    have hzsup : Plane.supDist z (c j) = r := by
      rw [Plane.frontier_closedSquare] at hzj
      exact hzj
    have hsupnorm : Plane.supNorm (z - c j) = r := by
      exact hzsup
    apply hthick
    rw [mem_thickening_iff]
    refine ⟨c j, ⟨sample N j, sample_mem_I hjN', (hc j).symm⟩, ?_⟩
    rw [dist_eq_norm]
    calc
      ‖z - c j‖ ≤ Real.sqrt 2 * Plane.supNorm (z - c j) :=
        Plane.norm_le_sqrt_two_mul_supNorm _
      _ = Real.sqrt 2 * r := by rw [hsupnorm]
      _ < 2 * r := mul_lt_mul_of_pos_right hsqrt hr
      _ < ρ := by rw [hr_def]; linarith
  obtain ⟨base, hbase, hbase_unbounded⟩ := Graph.exists_unbounded_face hdraw
  obtain ⟨e, u, v, W, hface⟩ := Graph.face_cycles' hdraw hpoly hH2 base hbase
  let C : Set Plane := Graph.edgesCover segmentDrawing (e :: W)
  have hC : IsJordanCurve C := by
    dsimp only [C]
    exact hdraw.cycle_isJordanCurve hface.isCycle
  have hface_outside : Graph.face H segmentDrawing base = outside C := by
    rcases hface.eq_inside_or_outside with hin | hout
    · exfalso
      apply hbase_unbounded
      rw [hin]
      exact hface.isSeparating.isBounded_inside
    · exact hout
  have hCpoint : C ⊆ Graph.pointSet H segmentDrawing := by
    dsimp only [C]
    exact Graph.edgesCover_subset_pointSet fun g hg => hface.isCycle.mem_edgeSet_cons hg
  have hCD : C ⊆ D := hCpoint.trans hpointD
  have himage : α '' I ⊆ C ∪ inside C := by
    intro z hz
    have hcover := image_subset_iUnion_closedSquare (α := α) (n := N) hN hmesh hz
    obtain ⟨j, hj, hzj⟩ := Set.mem_iUnion₂.1 hcover
    rw [Finset.mem_range] at hj
    have hjN : j ≤ N := (Nat.le_of_lt hj)
    have hzsup : Plane.supDist z (c j) ≤ r := by
      rw [hc]
      exact hzj
    rcases lt_or_eq_of_le hzsup with hzopen | hzfront
    · have hfr : frontier (Plane.closedSquare (c j) r) ⊆
          Graph.pointSet H segmentDrawing := by
        rw [← pointSet_familySquare (c := c) (N := N) hr hjN]
        apply Graph.pointSet_mono
        dsimp only [H]
        exact Graph.le_chainUnion (G := familyOverlay c N r)
          (fun _ _ _ => familySquare_le) (by omega) (by omega)
      have hz_not_face : z ∉ Graph.face H segmentDrawing base :=
        notMem_face_of_mem_openSquare hfr hbase_unbounded hzopen
      have hz_not_outside : z ∉ outside C := by rwa [← hface_outside]
      by_cases hzC : z ∈ C
      · exact Or.inl hzC
      · have hzregions : z ∈ inside C ∪ outside C := by
          rw [inside_union_outside]
          exact hzC
        exact Or.inr (hzregions.resolve_right hz_not_outside)
    · have hzfr : z ∈ frontier (Plane.closedSquare (c j) r) := by
        rw [Plane.frontier_closedSquare]
        exact hzfront
      have hzpoint : z ∈ Graph.pointSet H segmentDrawing := by
        have hzsq : z ∈ Graph.pointSet (familySquare c N r j) segmentDrawing := by
          rw [pointSet_familySquare (c := c) (N := N) hr hjN]
          exact hzfr
        exact Graph.pointSet_mono (by
          dsimp only [H]
          exact Graph.le_chainUnion (G := familyOverlay c N r)
            (fun _ _ _ => familySquare_le) (by omega) (by omega)) hzsq
      by_cases hzC : z ∈ C
      · exact Or.inl hzC
      · have hz_not_outside : z ∉ outside C := by
          intro hzout
          have hzface : z ∈ Graph.face H segmentDrawing base := hface_outside.symm ▸ hzout
          exact (Graph.face_subset_exterior H segmentDrawing base hzface) hzpoint
        have hzregions : z ∈ inside C ∪ outside C := by
          rw [inside_union_outside]
          exact hzC
        exact Or.inr (hzregions.resolve_right hz_not_outside)
  exact ⟨C, hC, himage, hCD⟩

end Schoenflies
