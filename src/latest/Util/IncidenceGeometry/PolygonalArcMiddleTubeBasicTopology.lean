import Util.IncidenceGeometry.PolygonalArcCollarOrientedSeparatedTubeData
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.Topology.Algebra.Module.FiniteDimension

open Classical
noncomputable section

lemma PolygonalArcMiddleTubeBasicTopology
    (γ : PolygonalArc) {η : ℝ}
    (controlRadii : PolygonalArcCollarControlRadii γ η)
    (middleSegments : PolygonalArcCollarMiddleSegmentData γ controlRadii)
    (forbiddenMargins :
      PolygonalArcCollarMiddleForbiddenMargins γ controlRadii middleSegments)
    (orientedTubes :
      PolygonalArcCollarOrientedSeparatedTubeData γ controlRadii middleSegments
        forbiddenMargins) :
    (∀ (j : ℕ) (hj : j + 1 < γ.vertices.length),
      IsOpen (orientedTubes.toPolygonalArcCollarSeparatedTubeData.tube j hj)) ∧
    (∀ (j : ℕ) (hj : j + 1 < γ.vertices.length),
      IsOpen (orientedTubes.toPolygonalArcCollarSeparatedTubeData.leftHalf j hj)) ∧
    (∀ (j : ℕ) (hj : j + 1 < γ.vertices.length),
      IsOpen (orientedTubes.toPolygonalArcCollarSeparatedTubeData.rightHalf j hj)) ∧
    (∀ (j : ℕ) (hj : j + 1 < γ.vertices.length),
      IsConnected (orientedTubes.toPolygonalArcCollarSeparatedTubeData.leftHalf j hj)) ∧
    (∀ (j : ℕ) (hj : j + 1 < γ.vertices.length),
      IsConnected (orientedTubes.toPolygonalArcCollarSeparatedTubeData.rightHalf j hj)) := by
  let sep := orientedTubes.toPolygonalArcCollarSeparatedTubeData
  have lower_lt_upper :
      ∀ (j : ℕ) (hj : j + 1 < γ.vertices.length),
        sep.lowerParam j hj < sep.upperParam j hj := by
    intro j hj
    exact (sep.lowerParam_lt_left_parameter j hj).trans
      ((middleSegments.left_parameter_lt_right_parameter j hj).trans
        (sep.right_parameter_lt_upperParam j hj))
  have segment_dist_pos :
      ∀ (j : ℕ) (hj : j + 1 < γ.vertices.length),
        0 < dist γ.vertices[j] γ.vertices[j + 1] := by
    intro j hj
    have hsum_pos :
        0 <
          controlRadii.radius ⟨j, Nat.lt_of_succ_lt hj⟩ +
            controlRadii.radius ⟨j + 1, hj⟩ :=
      add_pos (controlRadii.radius_pos _) (controlRadii.radius_pos _)
    exact hsum_pos.trans (controlRadii.adjacent_radii_sum_lt hj)
  have open_image_of_second :
      ∀ (j : ℕ) (hj : j + 1 < γ.vertices.length) (a b : ℝ), a < b →
        IsOpen
          {z | ∃ t : ℝ, t ∈ Set.Ioo (sep.lowerParam j hj) (sep.upperParam j hj) ∧
            ∃ s : ℝ, s ∈ Set.Ioo a b ∧
              z =
                AffineMap.lineMap γ.vertices[j] γ.vertices[j + 1] t +
                  s • sep.normal j hj} := by
    intro j hj a b hab
    let v : EuclideanSpace ℝ (Fin 2) := γ.vertices[j + 1] - γ.vertices[j]
    have hv_norm : ‖v‖ = dist γ.vertices[j] γ.vertices[j + 1] := by
      calc
        ‖v‖ = ‖-(γ.vertices[j] - γ.vertices[j + 1])‖ := by
          congr 1
          simp [v]
        _ = ‖γ.vertices[j] - γ.vertices[j + 1]‖ := norm_neg _
        _ = dist γ.vertices[j] γ.vertices[j + 1] := by
          rw [dist_eq_norm]
    have hv_ne : v ≠ 0 := by
      intro hv0
      have : (0 : ℝ) = dist γ.vertices[j] γ.vertices[j + 1] := by
        simpa [hv0] using hv_norm
      exact (ne_of_gt (segment_dist_pos j hj)) this.symm
    have hn_ne : sep.normal j hj ≠ 0 := by
      intro hn0
      have : (0 : ℝ) = dist γ.vertices[j] γ.vertices[j + 1] := by
        simpa [hn0] using (sep.normal_norm_eq_segment_length j hj)
      exact (ne_of_gt (segment_dist_pos j hj)) this.symm
    let basisVec : Fin 2 → EuclideanSpace ℝ (Fin 2) :=
      ![v, sep.normal j hj]
    have hli : LinearIndependent ℝ basisVec := by
      refine linearIndependent_of_ne_zero_of_inner_eq_zero ?hne ?hortho
      · intro i
        fin_cases i
        · simpa [basisVec] using hv_ne
        · simpa [basisVec] using hn_ne
      · intro i k hik
        fin_cases i <;> fin_cases k
        · simp at hik
        · simpa [basisVec, v] using sep.normal_orthogonal j hj
        · rw [real_inner_comm]
          simpa [basisVec, v] using sep.normal_orthogonal j hj
        · simp at hik
    let B : Module.Basis (Fin 2) ℝ (EuclideanSpace ℝ (Fin 2)) :=
      basisOfLinearIndependentOfCardEqFinrank hli (by simp)
    let L : (ℝ × ℝ) →ₗ[ℝ] EuclideanSpace ℝ (Fin 2) :=
    {
      toFun x := x.1 • v + x.2 • sep.normal j hj
      map_add' x y := by
        ext i
        simp [add_smul, add_comm, add_left_comm, add_assoc]
      map_smul' c x := by
        ext i
        simp [mul_smul, smul_add]
    }
    have hsurj : Function.Surjective L := by
      intro y
      refine ⟨((B.repr y) 0, (B.repr y) 1), ?_⟩
      change (B.repr y) 0 • v + (B.repr y) 1 • sep.normal j hj = y
      have hsum := B.sum_repr y
      simpa [B, basisVec, Fin.sum_univ_two] using hsum
    have hsource_open :
        IsOpen
          ((Set.Ioo (sep.lowerParam j hj) (sep.upperParam j hj)) ×ˢ
            (Set.Ioo a b)) := by
      exact isOpen_Ioo.prod isOpen_Ioo
    have hFopen : IsOpenMap (fun x : ℝ × ℝ =>
        γ.vertices[j] + L x) := by
      exact (isOpenMap_add_left γ.vertices[j]).comp
        (LinearMap.isOpenMap_of_finiteDimensional L hsurj)
    have himg :
        (fun x : ℝ × ℝ => γ.vertices[j] + L x) ''
          ((Set.Ioo (sep.lowerParam j hj) (sep.upperParam j hj)) ×ˢ
            (Set.Ioo a b)) =
          {z | ∃ t : ℝ, t ∈ Set.Ioo (sep.lowerParam j hj) (sep.upperParam j hj) ∧
            ∃ s : ℝ, s ∈ Set.Ioo a b ∧
              z =
                AffineMap.lineMap γ.vertices[j] γ.vertices[j + 1] t +
                  s • sep.normal j hj} := by
      ext z
      constructor
      · rintro ⟨x, hx, rfl⟩
        refine ⟨x.1, hx.1, x.2, hx.2, ?_⟩
        ext i
        simp [L, v, AffineMap.lineMap_apply_module, sub_eq_add_neg, smul_add,
          add_smul, add_left_comm, add_comm]
      · rintro ⟨t, ht, s, hs, rfl⟩
        refine ⟨(t, s), ⟨ht, hs⟩, ?_⟩
        ext i
        simp [L, v, AffineMap.lineMap_apply_module, sub_eq_add_neg, smul_add,
          add_smul, add_left_comm, add_comm]
    rw [← himg]
    exact hFopen _ hsource_open
  have connected_image_of_second :
      ∀ (j : ℕ) (hj : j + 1 < γ.vertices.length) (a b : ℝ), a < b →
        IsConnected
          {z | ∃ t : ℝ, t ∈ Set.Ioo (sep.lowerParam j hj) (sep.upperParam j hj) ∧
            ∃ s : ℝ, s ∈ Set.Ioo a b ∧
              z =
                AffineMap.lineMap γ.vertices[j] γ.vertices[j + 1] t +
                  s • sep.normal j hj} := by
    intro j hj a b hab
    let F : ℝ × ℝ → EuclideanSpace ℝ (Fin 2) :=
      fun x =>
        AffineMap.lineMap γ.vertices[j] γ.vertices[j + 1] x.1 +
          x.2 • sep.normal j hj
    have hconn_source :
        IsConnected
          ((Set.Ioo (sep.lowerParam j hj) (sep.upperParam j hj)) ×ˢ
            (Set.Ioo a b)) := by
      exact (isConnected_Ioo (lower_lt_upper j hj)).prod (isConnected_Ioo hab)
    have hcont : ContinuousOn F
        ((Set.Ioo (sep.lowerParam j hj) (sep.upperParam j hj)) ×ˢ
          (Set.Ioo a b)) := by
      fun_prop
    have himg :
        F ''
          ((Set.Ioo (sep.lowerParam j hj) (sep.upperParam j hj)) ×ˢ
            (Set.Ioo a b)) =
          {z | ∃ t : ℝ, t ∈ Set.Ioo (sep.lowerParam j hj) (sep.upperParam j hj) ∧
            ∃ s : ℝ, s ∈ Set.Ioo a b ∧
              z =
                AffineMap.lineMap γ.vertices[j] γ.vertices[j + 1] t +
                  s • sep.normal j hj} := by
      ext z
      constructor
      · rintro ⟨x, hx, rfl⟩
        exact ⟨x.1, hx.1, x.2, hx.2, rfl⟩
      · rintro ⟨t, ht, s, hs, rfl⟩
        exact ⟨(t, s), ⟨ht, hs⟩, rfl⟩
    rw [← himg]
    exact hconn_source.image F hcont
  change
      (∀ (j : ℕ) (hj : j + 1 < γ.vertices.length), IsOpen (sep.tube j hj)) ∧
      (∀ (j : ℕ) (hj : j + 1 < γ.vertices.length), IsOpen (sep.leftHalf j hj)) ∧
      (∀ (j : ℕ) (hj : j + 1 < γ.vertices.length), IsOpen (sep.rightHalf j hj)) ∧
      (∀ (j : ℕ) (hj : j + 1 < γ.vertices.length), IsConnected (sep.leftHalf j hj)) ∧
      (∀ (j : ℕ) (hj : j + 1 < γ.vertices.length), IsConnected (sep.rightHalf j hj))
  refine ⟨?tube_open, ?left_open, ?right_open, ?left_connected, ?right_connected⟩
  · intro j hj
    rw [sep.tube_eq j hj]
    exact open_image_of_second j hj (-(sep.halfWidth j hj)) (sep.halfWidth j hj) (by
      linarith [sep.halfWidth_pos j hj])
  · intro j hj
    rw [sep.leftHalf_eq j hj]
    exact open_image_of_second j hj 0 (sep.halfWidth j hj) (sep.halfWidth_pos j hj)
  · intro j hj
    rw [sep.rightHalf_eq j hj]
    exact open_image_of_second j hj (-(sep.halfWidth j hj)) 0 (by
      linarith [sep.halfWidth_pos j hj])
  · intro j hj
    rw [sep.leftHalf_eq j hj]
    exact connected_image_of_second j hj 0 (sep.halfWidth j hj) (sep.halfWidth_pos j hj)
  · intro j hj
    rw [sep.rightHalf_eq j hj]
    exact connected_image_of_second j hj (-(sep.halfWidth j hj)) 0 (by
      linarith [sep.halfWidth_pos j hj])
