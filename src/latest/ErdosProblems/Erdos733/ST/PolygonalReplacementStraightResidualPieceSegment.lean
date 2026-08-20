import ErdosProblems.Erdos733.ST.PolygonalReplacementResidualPieceData
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Order.IntermediateValue

open Classical
noncomputable section

universe u

-- [TABLET NODE: PolygonalReplacementStraightResidualPieceSegment]
lemma PolygonalReplacementStraightResidualPieceSegment {V : Type u} [Fintype V]
    (G : SimpleGraph V) [Fintype G.edgeSet]
    (D : GeometricArcDrawing G)
    (controlDisks : PolygonalReplacementControlDiskData G D)
    (boundaryPoints : PolygonalReplacementBoundaryPointData.{u, u} G D controlDisks)
    (edgeEndpoints :
      PolygonalReplacementEdgeBoundaryEndpointData G D controlDisks boundaryPoints)
    (residualPieceData :
      PolygonalReplacementResidualPieceData G D controlDisks boundaryPoints
        edgeEndpoints)
    (i : residualPieceData.pieceIndex)
    (hstraight :
      (D.edgeSource (residualPieceData.owner i) ≠
          D.edgeTarget (residualPieceData.owner i)) ∧
        D.edgeCarrier (residualPieceData.owner i) =
          segment ℝ (D.edgeSource (residualPieceData.owner i))
            (D.edgeTarget (residualPieceData.owner i)) ∧
        D.edgeRelativeInterior (residualPieceData.owner i) =
          openSegment ℝ (D.edgeSource (residualPieceData.owner i))
            (D.edgeTarget (residualPieceData.owner i))) :
    residualPieceData.originalPiece i =
      segment ℝ (residualPieceData.source i) (residualPieceData.target i) := by
-- BODY
  classical
  let e := residualPieceData.owner i
  let gamma : Set.Icc (0 : ℝ) 1 → EuclideanSpace ℝ (Fin 2) :=
    residualPieceData.edgeParam e
  let A : EuclideanSpace ℝ (Fin 2) := D.edgeSource e
  let B : EuclideanSpace ℝ (Fin 2) := D.edgeTarget e
  rcases residualPieceData.edgeParam_spec e with
    ⟨hgamma_cont, hgamma_inj, hgamma_source, hgamma_target,
      hgamma_carrier, _hgamma_rel⟩
  have hAB : A ≠ B := by
    simpa [A, B, e] using hstraight.1
  have hgamma_range : Set.range gamma = segment ℝ A B := by
    calc
      Set.range gamma = D.edgeCarrier e := by
        simpa [gamma] using hgamma_carrier.symm
      _ = segment ℝ A B := by
        simpa [A, B, e] using hstraight.2.1
  have hinterval_image :
      gamma '' Set.Icc (residualPieceData.sourceParam i)
          (residualPieceData.targetParam i) =
        segment ℝ (gamma (residualPieceData.sourceParam i))
          (gamma (residualPieceData.targetParam i)) := by
    let coord : EuclideanSpace ℝ (Fin 2) → ℝ := fun p =>
      inner ℝ (p - A) (B - A) / (‖B - A‖ ^ 2)
    have coord_cont : Continuous coord := by
      dsimp [coord]
      fun_prop
    have lineMap_coord_of_mem :
        ∀ {p : EuclideanSpace ℝ (Fin 2)}, p ∈ segment ℝ A B →
          AffineMap.lineMap A B (coord p) = p := by
      intro p hp
      dsimp [coord]
      rw [segment_eq_image_lineMap] at hp
      rcases hp with ⟨theta, _htheta, rfl⟩
      have hnorm : ‖B - A‖ ≠ 0 := by
        have hBA : B - A ≠ 0 := sub_ne_zero.mpr hAB.symm
        exact norm_ne_zero_iff.mpr hBA
      have hnorm_sq : ‖B - A‖ ^ 2 ≠ 0 := pow_ne_zero 2 hnorm
      have hcoord :
          inner ℝ (AffineMap.lineMap A B theta - A) (B - A) /
              (‖B - A‖ ^ 2) =
            theta := by
        rw [AffineMap.lineMap_apply_module]
        have hsub : (1 - theta) • A + theta • B - A =
            theta • (B - A) := by
          module
        rw [hsub, real_inner_smul_left, real_inner_self_eq_norm_mul_norm]
        field_simp [hnorm, hnorm_sq]
      rw [hcoord]
    have gamma_mem_segment : ∀ u, gamma u ∈ segment ℝ A B := by
      intro u
      rw [← hgamma_range]
      exact ⟨u, rfl⟩
    have gamma_eq_lineMap_coord :
        ∀ u, gamma u = AffineMap.lineMap A B (coord (gamma u)) := by
      intro u
      exact (lineMap_coord_of_mem (gamma_mem_segment u)).symm
    let f : Set.Icc (0 : ℝ) 1 → ℝ := fun u => coord (gamma u)
    have f_cont : Continuous f := coord_cont.comp hgamma_cont
    have f_inj : Function.Injective f := by
      intro u v huv
      apply hgamma_inj
      have hline :
          AffineMap.lineMap A B (coord (gamma u)) =
            AffineMap.lineMap A B (coord (gamma v)) := by
        simpa [f] using congrArg (fun x => AffineMap.lineMap A B x) huv
      exact (gamma_eq_lineMap_coord u).trans
        (hline.trans (gamma_eq_lineMap_coord v).symm)
    have f_bot : f ⊥ = 0 := by
      dsimp [f, coord]
      rw [show gamma ⊥ = A by
        have hbot : (⊥ : Set.Icc (0 : ℝ) 1) = ⟨0, by simp⟩ := by
          ext
          simp
        rw [hbot]
        simpa [gamma, A] using hgamma_source]
      simp
    have f_top : f ⊤ = 1 := by
      dsimp [f, coord]
      rw [show gamma ⊤ = B by
        have htop : (⊤ : Set.Icc (0 : ℝ) 1) = ⟨1, by simp⟩ := by
          ext
          simp
        rw [htop]
        simpa [gamma, B] using hgamma_target]
      have hnorm : ‖B - A‖ ≠ 0 := by
        have hBA : B - A ≠ 0 := sub_ne_zero.mpr hAB.symm
        exact norm_ne_zero_iff.mpr hBA
      have hnorm_sq : ‖B - A‖ ^ 2 ≠ 0 := pow_ne_zero 2 hnorm
      rw [real_inner_self_eq_norm_mul_norm]
      field_simp [hnorm, hnorm_sq]
    have f_strict : StrictMono f := by
      exact Continuous.strictMono_of_inj_boundedOrder f_cont
        (by simp [f_bot, f_top]) f_inj
    have hsource_le_target :
        residualPieceData.sourceParam i ≤ residualPieceData.targetParam i :=
      (residualPieceData.sourceParam_lt_targetParam i).le
    have f_image :
        f '' Set.Icc (residualPieceData.sourceParam i)
            (residualPieceData.targetParam i) =
          Set.Icc (f (residualPieceData.sourceParam i))
            (f (residualPieceData.targetParam i)) := by
      exact ContinuousOn.image_Icc_of_monotoneOn hsource_le_target
        f_cont.continuousOn (f_strict.monotone.monotoneOn _)
    rw [segment_eq_image_lineMap]
    calc
      gamma '' Set.Icc (residualPieceData.sourceParam i)
          (residualPieceData.targetParam i) =
          (fun theta : ℝ => AffineMap.lineMap A B theta) ''
            (f '' Set.Icc (residualPieceData.sourceParam i)
              (residualPieceData.targetParam i)) := by
        ext p
        constructor
        · rintro ⟨u, hu, rfl⟩
          exact ⟨f u, ⟨u, hu, rfl⟩, (gamma_eq_lineMap_coord u).symm⟩
        · rintro ⟨theta, ⟨u, hu, rfl⟩, hp⟩
          have hline : AffineMap.lineMap A B (coord (gamma u)) = p := by
            simpa [f] using hp
          exact ⟨u, hu, (gamma_eq_lineMap_coord u).trans hline⟩
      _ = (fun theta : ℝ => AffineMap.lineMap A B theta) ''
            Set.Icc (f (residualPieceData.sourceParam i))
              (f (residualPieceData.targetParam i)) := by
        rw [f_image]
      _ = AffineMap.lineMap (gamma (residualPieceData.sourceParam i))
            (gamma (residualPieceData.targetParam i)) '' Set.Icc (0 : ℝ) 1 := by
        have hf_le :
            f (residualPieceData.sourceParam i) ≤
              f (residualPieceData.targetParam i) :=
          f_strict.monotone hsource_le_target
        change (AffineMap.lineMap A B : ℝ → EuclideanSpace ℝ (Fin 2)) ''
            Set.Icc (f (residualPieceData.sourceParam i))
              (f (residualPieceData.targetParam i)) =
          (AffineMap.lineMap (gamma (residualPieceData.sourceParam i))
              (gamma (residualPieceData.targetParam i)) :
              ℝ → EuclideanSpace ℝ (Fin 2)) '' Set.Icc (0 : ℝ) 1
        rw [← segment_eq_Icc hf_le, image_segment]
        rw [gamma_eq_lineMap_coord (residualPieceData.sourceParam i),
          gamma_eq_lineMap_coord (residualPieceData.targetParam i)]
        rw [segment_eq_image_lineMap]
  calc
    residualPieceData.originalPiece i =
        gamma '' Set.Icc (residualPieceData.sourceParam i)
          (residualPieceData.targetParam i) := by
      simpa [gamma, e] using residualPieceData.originalPiece_eq_parameter_interval i
    _ = segment ℝ (gamma (residualPieceData.sourceParam i))
        (gamma (residualPieceData.targetParam i)) := hinterval_image
    _ = segment ℝ (residualPieceData.source i)
        (residualPieceData.target i) := by
      rw [residualPieceData.source_eq_edgeParam i,
        residualPieceData.target_eq_edgeParam i]
