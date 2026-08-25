import Util.IncidenceGeometry.PolygonalArcCollarVertexLocalPieceData
import Util.IncidenceGeometry.PolygonalArcVertexMemCarrier

open Classical
noncomputable section


lemma PolygonalArcCollarVertexLocalPieceDataExists (γ : PolygonalArc) {η : ℝ}
    (controlRadii : PolygonalArcCollarControlRadii γ η)
    (middleSegments : PolygonalArcCollarMiddleSegmentData γ controlRadii)
    (forbiddenMargins :
      PolygonalArcCollarMiddleForbiddenMargins γ controlRadii middleSegments)
    (separatedTubes :
      PolygonalArcCollarSeparatedTubeData γ controlRadii middleSegments
        forbiddenMargins) :
    Nonempty
      (PolygonalArcCollarVertexLocalPieceData γ controlRadii middleSegments
        forbiddenMargins separatedTubes) := by
  let vertexDisk : Fin γ.vertices.length → Set (EuclideanSpace ℝ (Fin 2)) :=
    fun i => Metric.ball γ.vertices[i.1] (controlRadii.radius i)
  let endpointPiece : Fin γ.vertices.length → Set (EuclideanSpace ℝ (Fin 2)) :=
    fun i => vertexDisk i \ ({γ.vertices[i.1]} : Set (EuclideanSpace ℝ (Fin 2)))
  let leftLocalPiece : Fin γ.vertices.length → Set (EuclideanSpace ℝ (Fin 2)) :=
    fun i =>
      {z | (∃ hj : i.1 + 1 < γ.vertices.length,
              z ∈ vertexDisk i ∧ z ∈ separatedTubes.leftHalf i.1 hj) ∨
            (∃ (j : ℕ) (hj : j + 1 < γ.vertices.length),
              j + 1 = i.1 ∧ z ∈ vertexDisk i ∧
                z ∈ separatedTubes.leftHalf j hj)}
  let rightLocalPiece : Fin γ.vertices.length → Set (EuclideanSpace ℝ (Fin 2)) :=
    fun i =>
      {z | (∃ hj : i.1 + 1 < γ.vertices.length,
              z ∈ vertexDisk i ∧ z ∈ separatedTubes.rightHalf i.1 hj) ∨
            (∃ (j : ℕ) (hj : j + 1 < γ.vertices.length),
              j + 1 = i.1 ∧ z ∈ vertexDisk i ∧
                z ∈ separatedTubes.rightHalf j hj)}
  let outgoingLeftAttachment :
      (j : ℕ) → j + 1 < γ.vertices.length →
        Set (EuclideanSpace ℝ (Fin 2)) :=
    fun j hj =>
      vertexDisk ⟨j, Nat.lt_of_succ_lt hj⟩ ∩ separatedTubes.leftHalf j hj
  let outgoingRightAttachment :
      (j : ℕ) → j + 1 < γ.vertices.length →
        Set (EuclideanSpace ℝ (Fin 2)) :=
    fun j hj =>
      vertexDisk ⟨j, Nat.lt_of_succ_lt hj⟩ ∩ separatedTubes.rightHalf j hj
  let incomingLeftAttachment :
      (j : ℕ) → j + 1 < γ.vertices.length →
        Set (EuclideanSpace ℝ (Fin 2)) :=
    fun j hj => vertexDisk ⟨j + 1, hj⟩ ∩ separatedTubes.leftHalf j hj
  let incomingRightAttachment :
      (j : ℕ) → j + 1 < γ.vertices.length →
        Set (EuclideanSpace ℝ (Fin 2)) :=
    fun j hj => vertexDisk ⟨j + 1, hj⟩ ∩ separatedTubes.rightHalf j hj
  let segmentLength : (j : ℕ) → j + 1 < γ.vertices.length → ℝ := fun j _ =>
    dist γ.vertices[j] γ.vertices[j + 1]
  let leftParam : (j : ℕ) → j + 1 < γ.vertices.length → ℝ := fun j hj =>
    controlRadii.radius ⟨j, Nat.lt_of_succ_lt hj⟩ / segmentLength j hj
  let rightParam : (j : ℕ) → j + 1 < γ.vertices.length → ℝ := fun j hj =>
    1 - controlRadii.radius ⟨j + 1, hj⟩ / segmentLength j hj
  have segmentLength_pos :
      ∀ (j : ℕ) (hj : j + 1 < γ.vertices.length),
        0 < segmentLength j hj := by
    intro j hj
    have hsum := controlRadii.adjacent_radii_sum_lt (j := j) hj
    have hleft :
        0 < controlRadii.radius ⟨j, Nat.lt_of_succ_lt hj⟩ :=
      controlRadii.radius_pos ⟨j, Nat.lt_of_succ_lt hj⟩
    have hright : 0 < controlRadii.radius ⟨j + 1, hj⟩ :=
      controlRadii.radius_pos ⟨j + 1, hj⟩
    dsimp [segmentLength]
    nlinarith
  have leftParam_pos :
      ∀ (j : ℕ) (hj : j + 1 < γ.vertices.length), 0 < leftParam j hj := by
    intro j hj
    dsimp [leftParam]
    exact div_pos (controlRadii.radius_pos ⟨j, Nat.lt_of_succ_lt hj⟩)
      (segmentLength_pos j hj)
  have leftParam_lt_rightParam :
      ∀ (j : ℕ) (hj : j + 1 < γ.vertices.length),
        leftParam j hj < rightParam j hj := by
    intro j hj
    simpa [leftParam, rightParam, segmentLength] using
      middleSegments.left_parameter_lt_right_parameter j hj
  have rightParam_lt_one :
      ∀ (j : ℕ) (hj : j + 1 < γ.vertices.length),
        rightParam j hj < 1 := by
    intro j hj
    simpa [rightParam, segmentLength] using
      middleSegments.right_parameter_lt_one j hj
  have lowerParam_lt_leftParam :
      ∀ (j : ℕ) (hj : j + 1 < γ.vertices.length),
        separatedTubes.lowerParam j hj < leftParam j hj := by
    intro j hj
    simpa [leftParam, segmentLength] using
      separatedTubes.lowerParam_lt_left_parameter j hj
  have rightParam_lt_upperParam :
      ∀ (j : ℕ) (hj : j + 1 < γ.vertices.length),
        rightParam j hj < separatedTubes.upperParam j hj := by
    intro j hj
    simpa [rightParam, segmentLength] using
      separatedTubes.right_parameter_lt_upperParam j hj
  have dist_lineMap_lineMap_local :
      ∀ (A B : EuclideanSpace ℝ (Fin 2)) (c₁ c₂ : ℝ),
        dist (AffineMap.lineMap A B c₁) (AffineMap.lineMap A B c₂) =
          dist c₁ c₂ * dist A B := by
    intro A B c₁ c₂
    rw [dist_eq_norm, Real.dist_eq, dist_eq_norm]
    have hvec :
        AffineMap.lineMap A B c₁ - AffineMap.lineMap A B c₂ =
          (c₁ - c₂) • (B - A) := by
      apply PiLp.ext
      intro k
      simp [AffineMap.lineMap_apply_module]
      ring
    rw [hvec, norm_smul, Real.norm_eq_abs]
    have hnorm : ‖B - A‖ = ‖A - B‖ := by
      have hneg : B - A = -(A - B) := by
        abel
      rw [hneg, norm_neg]
    rw [hnorm]
  have outgoing_point_mem_vertexDisk :
      ∀ (j : ℕ) (hj : j + 1 < γ.vertices.length) (t s : ℝ),
        0 < t → t < leftParam j hj → |s| < leftParam j hj - t →
          AffineMap.lineMap γ.vertices[j] γ.vertices[j + 1] t +
              s • separatedTubes.normal j hj ∈
            vertexDisk ⟨j, Nat.lt_of_succ_lt hj⟩ := by
    intro j hj t s htpos htleft hsleft
    rw [Metric.mem_ball]
    let A : EuclideanSpace ℝ (Fin 2) := γ.vertices[j]
    let B : EuclideanSpace ℝ (Fin 2) := γ.vertices[j + 1]
    let q : EuclideanSpace ℝ (Fin 2) := AffineMap.lineMap A B t
    let z : EuclideanSpace ℝ (Fin 2) := q + s • separatedTubes.normal j hj
    have hDpos : 0 < segmentLength j hj := segmentLength_pos j hj
    have hzq :
        dist z q = |s| * segmentLength j hj := by
      have hsub : z - q = s • separatedTubes.normal j hj := by
        simp [z, q]
      rw [dist_eq_norm, hsub, norm_smul, Real.norm_eq_abs,
        separatedTubes.normal_norm_eq_segment_length j hj]
    have hqA : dist q A = t * segmentLength j hj := by
      have hdist := dist_lineMap_lineMap_local A B t 0
      have hdistt : dist t 0 = t := by
        rw [Real.dist_eq, sub_zero, abs_of_pos htpos]
      simpa [q, A, B, segmentLength, hdistt] using hdist
    have htri : dist z A ≤ dist z q + dist q A := dist_triangle z q A
    have hleft_mul :
        leftParam j hj * segmentLength j hj =
          controlRadii.radius ⟨j, Nat.lt_of_succ_lt hj⟩ := by
      dsimp [leftParam]
      field_simp [ne_of_gt hDpos]
    have hsum :
        (|s| + t) * segmentLength j hj <
          controlRadii.radius ⟨j, Nat.lt_of_succ_lt hj⟩ := by
      have hlt : |s| + t < leftParam j hj := by linarith
      nlinarith
    have hzA :
        dist z A < controlRadii.radius ⟨j, Nat.lt_of_succ_lt hj⟩ := by
      calc
        dist z A ≤ dist z q + dist q A := htri
        _ = (|s| + t) * segmentLength j hj := by
          rw [hzq, hqA]
          ring
        _ < controlRadii.radius ⟨j, Nat.lt_of_succ_lt hj⟩ := hsum
    simpa [vertexDisk, A, B, q, z, segmentLength] using hzA
  have incoming_point_mem_vertexDisk :
      ∀ (j : ℕ) (hj : j + 1 < γ.vertices.length) (t s : ℝ),
        t < 1 → rightParam j hj < t → |s| < t - rightParam j hj →
          AffineMap.lineMap γ.vertices[j] γ.vertices[j + 1] t +
              s • separatedTubes.normal j hj ∈
            vertexDisk ⟨j + 1, hj⟩ := by
    intro j hj t s htone hrightt hsright
    rw [Metric.mem_ball]
    let A : EuclideanSpace ℝ (Fin 2) := γ.vertices[j]
    let B : EuclideanSpace ℝ (Fin 2) := γ.vertices[j + 1]
    let q : EuclideanSpace ℝ (Fin 2) := AffineMap.lineMap A B t
    let z : EuclideanSpace ℝ (Fin 2) := q + s • separatedTubes.normal j hj
    have hDpos : 0 < segmentLength j hj := segmentLength_pos j hj
    have hzq :
        dist z q = |s| * segmentLength j hj := by
      have hsub : z - q = s • separatedTubes.normal j hj := by
        simp [z, q]
      rw [dist_eq_norm, hsub, norm_smul, Real.norm_eq_abs,
        separatedTubes.normal_norm_eq_segment_length j hj]
    have hqB : dist q B = (1 - t) * segmentLength j hj := by
      have hdist := dist_lineMap_lineMap_local A B t 1
      have hdistt : dist t 1 = 1 - t := by
        rw [Real.dist_eq, abs_of_neg (sub_neg.mpr htone)]
        ring
      simpa [q, A, B, segmentLength, hdistt] using hdist
    have htri : dist z B ≤ dist z q + dist q B := dist_triangle z q B
    have hright_mul :
        (1 - rightParam j hj) * segmentLength j hj =
          controlRadii.radius ⟨j + 1, hj⟩ := by
      dsimp [rightParam]
      field_simp [ne_of_gt hDpos]
      ring
    have hsum :
        (|s| + (1 - t)) * segmentLength j hj <
          controlRadii.radius ⟨j + 1, hj⟩ := by
      have hlt : |s| + (1 - t) < 1 - rightParam j hj := by linarith
      nlinarith
    have hzB :
        dist z B < controlRadii.radius ⟨j + 1, hj⟩ := by
      calc
        dist z B ≤ dist z q + dist q B := htri
        _ = (|s| + (1 - t)) * segmentLength j hj := by
          rw [hzq, hqB]
          ring
        _ < controlRadii.radius ⟨j + 1, hj⟩ := hsum
    simpa [vertexDisk, A, B, q, z, segmentLength] using hzB
  have outgoing_germ_subset_endpointPiece :
      ∀ (j : ℕ) (hj : j + 1 < γ.vertices.length),
        (AffineMap.lineMap γ.vertices[j] γ.vertices[j + 1]) ''
            Set.Ioo (0 : ℝ) (leftParam j hj) ⊆
          endpointPiece ⟨j, Nat.lt_of_succ_lt hj⟩ := by
    intro j hj z hz
    rcases hz with ⟨t, ht, rfl⟩
    have hmem :=
      outgoing_point_mem_vertexDisk j hj t 0 ht.1 ht.2 (by simpa using ht.2)
    have hne : AffineMap.lineMap γ.vertices[j] γ.vertices[j + 1] t ≠
        γ.vertices[j] := by
      intro h
      have hDpos : 0 < segmentLength j hj := segmentLength_pos j hj
      have hdist :=
        dist_lineMap_lineMap_local γ.vertices[j] γ.vertices[j + 1] t 0
      have hdistt : dist t 0 = t := by
        rw [Real.dist_eq, sub_zero, abs_of_pos ht.1]
      have hdistline :
          dist (AffineMap.lineMap γ.vertices[j] γ.vertices[j + 1] t)
            γ.vertices[j] =
            t * segmentLength j hj := by
        simpa [segmentLength, hdistt] using hdist
      have hpos :
          0 <
            dist (AffineMap.lineMap γ.vertices[j] γ.vertices[j + 1] t)
              γ.vertices[j] := by
        rw [hdistline]
        exact mul_pos ht.1 hDpos
      rw [h, dist_self] at hpos
      exact (lt_irrefl (0 : ℝ)) hpos
    exact ⟨by simpa using hmem, by simpa using hne⟩
  have incoming_germ_subset_endpointPiece :
      ∀ (j : ℕ) (hj : j + 1 < γ.vertices.length),
        (AffineMap.lineMap γ.vertices[j] γ.vertices[j + 1]) ''
            Set.Ioo (rightParam j hj) (1 : ℝ) ⊆
          endpointPiece ⟨j + 1, hj⟩ := by
    intro j hj z hz
    rcases hz with ⟨t, ht, rfl⟩
    have hmem :=
      incoming_point_mem_vertexDisk j hj t 0 ht.2 ht.1 (by simpa using ht.1)
    have hne : AffineMap.lineMap γ.vertices[j] γ.vertices[j + 1] t ≠
        γ.vertices[j + 1] := by
      intro h
      have ht_lt_one : t < 1 := ht.2
      have hDpos : 0 < segmentLength j hj := segmentLength_pos j hj
      have hdist :=
        dist_lineMap_lineMap_local γ.vertices[j] γ.vertices[j + 1] t 1
      have hdistt : dist t 1 = 1 - t := by
        rw [Real.dist_eq, abs_of_neg (by linarith : t - 1 < 0)]
        ring
      have hdistline :
          dist (AffineMap.lineMap γ.vertices[j] γ.vertices[j + 1] t)
            γ.vertices[j + 1] =
            (1 - t) * segmentLength j hj := by
        simpa [segmentLength, hdistt] using hdist
      have hone_minus_pos : 0 < 1 - t := by linarith
      have hpos :
          0 <
            dist (AffineMap.lineMap γ.vertices[j] γ.vertices[j + 1] t)
              γ.vertices[j + 1] := by
        rw [hdistline]
        exact mul_pos hone_minus_pos hDpos
      rw [h, dist_self] at hpos
      exact (lt_irrefl (0 : ℝ)) hpos
    exact ⟨by simpa using hmem, by simpa using hne⟩
  have outgoing_left_attachment_nonempty :
      ∀ (j : ℕ) (hj : j + 1 < γ.vertices.length),
        (outgoingLeftAttachment j hj).Nonempty := by
    intro j hj
    let a := leftParam j hj
    let ℓ := separatedTubes.lowerParam j hj
    let t : ℝ := (ℓ + a) / 2
    let gap : ℝ := a - t
    let eps : ℝ := min (separatedTubes.halfWidth j hj / 2) (gap / 2)
    have hℓa : ℓ < a := by simpa [a, ℓ] using lowerParam_lt_leftParam j hj
    have htℓ : ℓ < t := by dsimp [t]; linarith
    have hta : t < a := by dsimp [t]; linarith
    have hgap_pos : 0 < gap := by dsimp [gap]; linarith
    have heps_pos : 0 < eps := by
      dsimp [eps]
      exact lt_min (half_pos (separatedTubes.halfWidth_pos j hj))
        (half_pos hgap_pos)
    have heps_lt_width : eps < separatedTubes.halfWidth j hj := by
      have hle : eps ≤ separatedTubes.halfWidth j hj / 2 := by
        dsimp [eps]
        exact min_le_left _ _
      nlinarith [separatedTubes.halfWidth_pos j hj]
    have heps_lt_gap : eps < gap := by
      have hle : eps ≤ gap / 2 := by
        dsimp [eps]
        exact min_le_right _ _
      nlinarith [hgap_pos]
    let z :=
      AffineMap.lineMap γ.vertices[j] γ.vertices[j + 1] t +
        eps • separatedTubes.normal j hj
    refine ⟨z, ?_⟩
    dsimp [outgoingLeftAttachment]
    constructor
    · exact outgoing_point_mem_vertexDisk j hj t eps
        ((separatedTubes.lowerParam_pos j hj).trans htℓ) (by simpa [a] using hta)
        (by rwa [abs_of_pos heps_pos])
    · rw [separatedTubes.leftHalf_eq j hj]
      refine ⟨t, ?_, eps, ?_, rfl⟩
      · have hta_left : t < leftParam j hj := by simpa [a] using hta
        exact ⟨htℓ, hta_left.trans
          ((leftParam_lt_rightParam j hj).trans
            (rightParam_lt_upperParam j hj))⟩
      · exact ⟨heps_pos, heps_lt_width⟩
  have outgoing_right_attachment_nonempty :
      ∀ (j : ℕ) (hj : j + 1 < γ.vertices.length),
        (outgoingRightAttachment j hj).Nonempty := by
    intro j hj
    let a := leftParam j hj
    let ℓ := separatedTubes.lowerParam j hj
    let t : ℝ := (ℓ + a) / 2
    let gap : ℝ := a - t
    let eps : ℝ := min (separatedTubes.halfWidth j hj / 2) (gap / 2)
    have hℓa : ℓ < a := by simpa [a, ℓ] using lowerParam_lt_leftParam j hj
    have htℓ : ℓ < t := by dsimp [t]; linarith
    have hta : t < a := by dsimp [t]; linarith
    have hgap_pos : 0 < gap := by dsimp [gap]; linarith
    have heps_pos : 0 < eps := by
      dsimp [eps]
      exact lt_min (half_pos (separatedTubes.halfWidth_pos j hj))
        (half_pos hgap_pos)
    have heps_lt_width : eps < separatedTubes.halfWidth j hj := by
      have hle : eps ≤ separatedTubes.halfWidth j hj / 2 := by
        dsimp [eps]
        exact min_le_left _ _
      nlinarith [separatedTubes.halfWidth_pos j hj]
    have heps_lt_gap : eps < gap := by
      have hle : eps ≤ gap / 2 := by
        dsimp [eps]
        exact min_le_right _ _
      nlinarith [hgap_pos]
    let z :=
      AffineMap.lineMap γ.vertices[j] γ.vertices[j + 1] t +
        (-eps) • separatedTubes.normal j hj
    refine ⟨z, ?_⟩
    dsimp [outgoingRightAttachment]
    constructor
    · exact outgoing_point_mem_vertexDisk j hj t (-eps)
        ((separatedTubes.lowerParam_pos j hj).trans htℓ) (by simpa [a] using hta)
        (by simpa [abs_of_pos heps_pos] using heps_lt_gap)
    · rw [separatedTubes.rightHalf_eq j hj]
      refine ⟨t, ?_, -eps, ?_, rfl⟩
      · have hta_left : t < leftParam j hj := by simpa [a] using hta
        exact ⟨htℓ, hta_left.trans
          ((leftParam_lt_rightParam j hj).trans
            (rightParam_lt_upperParam j hj))⟩
      · exact ⟨by linarith, by linarith⟩
  have incoming_left_attachment_nonempty :
      ∀ (j : ℕ) (hj : j + 1 < γ.vertices.length),
        (incomingLeftAttachment j hj).Nonempty := by
    intro j hj
    let b := rightParam j hj
    let u := separatedTubes.upperParam j hj
    let t : ℝ := (b + u) / 2
    let gap : ℝ := t - b
    let eps : ℝ := min (separatedTubes.halfWidth j hj / 2) (gap / 2)
    have hbu : b < u := by simpa [b, u] using rightParam_lt_upperParam j hj
    have hbt : b < t := by dsimp [t]; linarith
    have htu : t < u := by dsimp [t]; linarith
    have htone : t < 1 := htu.trans (separatedTubes.upperParam_lt_one j hj)
    have hgap_pos : 0 < gap := by dsimp [gap]; linarith
    have heps_pos : 0 < eps := by
      dsimp [eps]
      exact lt_min (half_pos (separatedTubes.halfWidth_pos j hj))
        (half_pos hgap_pos)
    have heps_lt_width : eps < separatedTubes.halfWidth j hj := by
      have hle : eps ≤ separatedTubes.halfWidth j hj / 2 := by
        dsimp [eps]
        exact min_le_left _ _
      nlinarith [separatedTubes.halfWidth_pos j hj]
    have heps_lt_gap : eps < gap := by
      have hle : eps ≤ gap / 2 := by
        dsimp [eps]
        exact min_le_right _ _
      nlinarith [hgap_pos]
    let z :=
      AffineMap.lineMap γ.vertices[j] γ.vertices[j + 1] t +
        eps • separatedTubes.normal j hj
    refine ⟨z, ?_⟩
    dsimp [incomingLeftAttachment]
    constructor
    · exact incoming_point_mem_vertexDisk j hj t eps htone (by simpa [b] using hbt)
        (by rwa [abs_of_pos heps_pos])
    · rw [separatedTubes.leftHalf_eq j hj]
      refine ⟨t, ?_, eps, ?_, rfl⟩
      · have hbt_right : rightParam j hj < t := by simpa [b] using hbt
        exact ⟨(lowerParam_lt_leftParam j hj).trans
          ((leftParam_lt_rightParam j hj).trans hbt_right), htu⟩
      · exact ⟨heps_pos, heps_lt_width⟩
  have incoming_right_attachment_nonempty :
      ∀ (j : ℕ) (hj : j + 1 < γ.vertices.length),
        (incomingRightAttachment j hj).Nonempty := by
    intro j hj
    let b := rightParam j hj
    let u := separatedTubes.upperParam j hj
    let t : ℝ := (b + u) / 2
    let gap : ℝ := t - b
    let eps : ℝ := min (separatedTubes.halfWidth j hj / 2) (gap / 2)
    have hbu : b < u := by simpa [b, u] using rightParam_lt_upperParam j hj
    have hbt : b < t := by dsimp [t]; linarith
    have htu : t < u := by dsimp [t]; linarith
    have htone : t < 1 := htu.trans (separatedTubes.upperParam_lt_one j hj)
    have hgap_pos : 0 < gap := by dsimp [gap]; linarith
    have heps_pos : 0 < eps := by
      dsimp [eps]
      exact lt_min (half_pos (separatedTubes.halfWidth_pos j hj))
        (half_pos hgap_pos)
    have heps_lt_width : eps < separatedTubes.halfWidth j hj := by
      have hle : eps ≤ separatedTubes.halfWidth j hj / 2 := by
        dsimp [eps]
        exact min_le_left _ _
      nlinarith [separatedTubes.halfWidth_pos j hj]
    have heps_lt_gap : eps < gap := by
      have hle : eps ≤ gap / 2 := by
        dsimp [eps]
        exact min_le_right _ _
      nlinarith [hgap_pos]
    let z :=
      AffineMap.lineMap γ.vertices[j] γ.vertices[j + 1] t +
        (-eps) • separatedTubes.normal j hj
    refine ⟨z, ?_⟩
    dsimp [incomingRightAttachment]
    constructor
    · exact incoming_point_mem_vertexDisk j hj t (-eps) htone (by simpa [b] using hbt)
        (by simpa [abs_of_pos heps_pos] using heps_lt_gap)
    · rw [separatedTubes.rightHalf_eq j hj]
      refine ⟨t, ?_, -eps, ?_, rfl⟩
      · have hbt_right : rightParam j hj < t := by simpa [b] using hbt
        exact ⟨(lowerParam_lt_leftParam j hj).trans
          ((leftParam_lt_rightParam j hj).trans hbt_right), htu⟩
      · exact ⟨by linarith, by linarith⟩
  refine ⟨
    { vertexDisk := vertexDisk
      endpointPiece := endpointPiece
      leftLocalPiece := leftLocalPiece
      rightLocalPiece := rightLocalPiece
      outgoingLeftAttachment := outgoingLeftAttachment
      outgoingRightAttachment := outgoingRightAttachment
      incomingLeftAttachment := incomingLeftAttachment
      incomingRightAttachment := incomingRightAttachment
      vertexDisk_eq := ?_
      endpointPiece_eq := ?_
      vertexDisk_open := ?_
      endpointPiece_open := ?_
      endpointPiece_omits_vertex := ?_
      vertexDisk_subset_closed_control_disk := ?_
      vertexDisk_subset_eta_neighborhood := ?_
      vertexDisk_disjoint_nonincident_segments := ?_
      vertexDisk_carrier_subset_incident_segments := ?_
      vertexDisk_disjoint_other_control_disks := ?_
      vertexDisk_disjoint_nonincident_tubes := ?_
      outgoing_germ_subset_endpointPiece := ?_
      incoming_germ_subset_endpointPiece := ?_
      leftLocalPiece_eq := ?_
      rightLocalPiece_eq := ?_
      leftLocalPiece_subset_disk := ?_
      rightLocalPiece_subset_disk := ?_
      outgoingLeftAttachment_eq := ?_
      outgoingRightAttachment_eq := ?_
      incomingLeftAttachment_eq := ?_
      incomingRightAttachment_eq := ?_
      outgoingLeftAttachment_nonempty := outgoing_left_attachment_nonempty
      outgoingRightAttachment_nonempty := outgoing_right_attachment_nonempty
      incomingLeftAttachment_nonempty := incoming_left_attachment_nonempty
      incomingRightAttachment_nonempty := incoming_right_attachment_nonempty
      outgoingLeftAttachment_subset_leftLocalPiece := ?_
      outgoingRightAttachment_subset_rightLocalPiece := ?_
      incomingLeftAttachment_subset_leftLocalPiece := ?_
      incomingRightAttachment_subset_rightLocalPiece := ?_ }⟩
  · intro i
    rfl
  · intro i
    rfl
  · intro i
    exact Metric.isOpen_ball
  · intro i
    dsimp [endpointPiece]
    exact
      (show IsOpen (Metric.ball γ.vertices[i.1] (controlRadii.radius i)) from
        Metric.isOpen_ball).sdiff isClosed_singleton
  · intro i hi
    exact hi.2 rfl
  · intro i z hz
    exact Metric.ball_subset_closedBall hz
  · intro i z hz
    have hcenter : γ.vertices[i.1] ∈ γ.carrier :=
      PolygonalArcVertexMemCarrier γ (List.getElem_mem (l := γ.vertices) i.2)
    refine ⟨γ.vertices[i.1], hcenter, ?_⟩
    have hdist : dist z γ.vertices[i.1] < controlRadii.radius i := by
      simpa [vertexDisk, Metric.mem_ball] using hz
    exact hdist.trans (controlRadii.radius_lt_eta i)
  · intro i j hj hij hijs
    rw [Set.disjoint_left]
    intro z hzDisk hzSeg
    exact Set.disjoint_left.mp
      (controlRadii.nonincident_segment_disjoint (i := i) (j := j) hj hij hijs)
      (Metric.ball_subset_closedBall hzDisk) hzSeg
  · intro i z hzDisk hzCarrier
    rw [γ.carrier_eq] at hzCarrier
    rcases hzCarrier with ⟨j, hj, hzSeg⟩
    by_cases hinc : i.1 = j ∨ i.1 = j + 1
    · exact ⟨j, hj, hzSeg, hinc⟩
    · exfalso
      have hij : i.1 ≠ j := by
        intro h
        exact hinc (Or.inl h)
      have hijs : i.1 ≠ j + 1 := by
        intro h
        exact hinc (Or.inr h)
      exact Set.disjoint_left.mp
        (controlRadii.nonincident_segment_disjoint (i := i) (j := j) hj hij hijs)
        (Metric.ball_subset_closedBall hzDisk) hzSeg
  · intro i k hik
    rw [Set.disjoint_left]
    intro z hzDisk hzClosed
    exact Set.disjoint_left.mp
      (controlRadii.control_disks_disjoint (i := i) (j := k) hik)
      (Metric.ball_subset_closedBall hzDisk) hzClosed
  · intro i j hj hij hijs
    rw [Set.disjoint_left]
    intro z hzDisk hzTube
    exact Set.disjoint_left.mp
      (separatedTubes.tube_disjoint_nonincident_control_disks j hj i hij hijs)
      hzTube (Metric.ball_subset_closedBall hzDisk)
  · intro j hj
    simpa [leftParam, segmentLength] using
      outgoing_germ_subset_endpointPiece j hj
  · intro j hj
    simpa [rightParam, segmentLength] using
      incoming_germ_subset_endpointPiece j hj
  · intro i
    rfl
  · intro i
    rfl
  · intro i z hz
    dsimp [leftLocalPiece] at hz
    rcases hz with ⟨hj, hzDisk, _⟩ | ⟨j, hj, hji, hzDisk, _⟩
    · exact hzDisk
    · exact hzDisk
  · intro i z hz
    dsimp [rightLocalPiece] at hz
    rcases hz with ⟨hj, hzDisk, _⟩ | ⟨j, hj, hji, hzDisk, _⟩
    · exact hzDisk
    · exact hzDisk
  · intro j hj
    rfl
  · intro j hj
    rfl
  · intro j hj
    rfl
  · intro j hj
    rfl
  · intro j hj z hz
    dsimp [outgoingLeftAttachment, leftLocalPiece] at hz ⊢
    exact Or.inl ⟨hj, hz.1, hz.2⟩
  · intro j hj z hz
    dsimp [outgoingRightAttachment, rightLocalPiece] at hz ⊢
    exact Or.inl ⟨hj, hz.1, hz.2⟩
  · intro j hj z hz
    dsimp [incomingLeftAttachment, leftLocalPiece] at hz ⊢
    exact Or.inr ⟨j, hj, rfl, hz.1, hz.2⟩
  · intro j hj z hz
    dsimp [incomingRightAttachment, rightLocalPiece] at hz ⊢
    exact Or.inr ⟨j, hj, rfl, hz.1, hz.2⟩
