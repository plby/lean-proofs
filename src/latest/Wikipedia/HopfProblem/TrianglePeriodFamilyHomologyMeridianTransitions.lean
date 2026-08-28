import Wikipedia.HopfProblem.TrianglePeriodFamilyHomologyMeridianTransitionsLifting

/-!
# Geometric identification of the slit-cover deck transitions

The two slit sections are compared with the actual lifted semicircles.
Their reflected endpoints were proved from the half-triangle boundary
geometry. Uniqueness of covering lifts therefore identifies the overlap
transitions with the stated triangle generators, including their signs.

When the normalization orientation is nonpositive the left transition is
the first generator and the right transition is the inverse second
generator. Positive normalization reverses both choices. The middle
transition is the identity in either case.
-/

noncomputable section

open Set Topology

namespace Wikipedia.HopfProblem.TrianglePeriodFamily.Homology

open SpecialPeriods SpecialPeriods.Triangle RiemannMapping Meridians

/-- Endpoint comparison for an actual upper-slit lift, with its base point explicit. -/
theorem upperLift_endpoint (b : SlitBaseLift) (x : upperBase) {z : TriangleRegularPoint}
    (p : Path b.val z) (hp : ∀ t, triangleRegularProject (p t) ∈ upperBase)
    (hx : x.val = triangleRegularProject z) : upperLift b x = z := by
  have hx' : x = ⟨triangleRegularProject (p 1), hp 1⟩ :=
    Subtype.ext (hx.trans (congrArg triangleRegularProject p.target.symm))
  calc
    upperLift b x = upperLift b ⟨triangleRegularProject (p 1), hp 1⟩ :=
      congrArg (upperLift b) hx'
    _ = p 1 := upperLift_path b p hp 1
    _ = z := p.target

/-- Endpoint comparison for an actual lower-slit lift, with its base point explicit. -/
theorem lowerLift_endpoint (b : SlitBaseLift) (x : lowerBase) {z : TriangleRegularPoint}
    (p : Path b.val z) (hp : ∀ t, triangleRegularProject (p t) ∈ lowerBase)
    (hx : x.val = triangleRegularProject z) : lowerLift b x = z := by
  have hx' : x = ⟨triangleRegularProject (p 1), hp 1⟩ :=
    Subtype.ext (hx.trans (congrArg triangleRegularProject p.target.symm))
  calc
    lowerLift b x = lowerLift b ⟨triangleRegularProject (p 1), hp 1⟩ :=
      congrArg (lowerLift b) hx'
    _ = p 1 := lowerLift_path b p hp 1
    _ = z := p.target

/-- The actual left semicircle endpoint, viewed in the left overlap component. -/
def meridianLeftOverlapPoint : overlapBase 0 := by
  refine ⟨triangleRegularProject normalizedRegularMeridianLeftPoint, ?_⟩
  rw [mem_regularOpen, normalizedRegularMeridianLeftPoint_coordinate]
  change (-1 / 2 : ℂ) ∈ overlapStrip 0
  norm_num [overlapStrip]

/-- The actual right semicircle endpoint, viewed in the right overlap component. -/
def meridianRightOverlapPoint : overlapBase 2 := by
  refine ⟨triangleRegularProject normalizedRegularMeridianRightPoint, ?_⟩
  rw [mem_regularOpen, normalizedRegularMeridianRightPoint_coordinate]
  change (3 / 2 : ℂ) ∈ overlapStrip 2
  norm_num [overlapStrip]

@[simp] theorem meridianLeftOverlapPoint_val :
    meridianLeftOverlapPoint.val =
      triangleRegularProject normalizedRegularMeridianLeftPoint := rfl

@[simp] theorem meridianRightOverlapPoint_val :
    meridianRightOverlapPoint.val =
      triangleRegularProject normalizedRegularMeridianRightPoint := rfl

/-- The actual deck transition with the canonical geometric starting lift. -/
def normalizedOverlapTransition (i : Fin 3) : TriangleGroup :=
  overlapTransition normalizedSlitBaseLift i

/-- Positive normalization places the zero half-circle in the upper slit. -/
theorem normalizedOverlapTransition_left_of_pos (ho : 0 < normalizationOrientation) :
    normalizedOverlapTransition 0 = triangleGenerator₁⁻¹ := by
  apply overlapTransition_eq_of_apply normalizedSlitBaseLift 0
    triangleGenerator₁⁻¹ meridianLeftOverlapPoint
  have hU : upperLiftOnOverlap normalizedSlitBaseLift 0 meridianLeftOverlapPoint =
      normalizedRegularMeridianLeftPoint := by
    change upperLift normalizedSlitBaseLift
      ⟨triangleRegularProject normalizedRegularMeridianLeftPoint, _⟩ = _
    have hp (t : unitInterval) : triangleRegularProject (liftedZeroHalfPath t) ∈ upperBase := by
      rw [mem_regularOpen, liftedZeroHalfPath_coordinate, zeroHalfPath, if_pos ho]
      exact upperZeroPath_mem_upperSlitPlane t
    apply upperLift_endpoint normalizedSlitBaseLift _ liftedZeroHalfPath hp
    rfl
  have hL : lowerLiftOnOverlap normalizedSlitBaseLift 0 meridianLeftOverlapPoint =
      triangleGenerator₁⁻¹ • normalizedRegularMeridianLeftPoint := by
    change lowerLift normalizedSlitBaseLift
      ⟨triangleRegularProject normalizedRegularMeridianLeftPoint, _⟩ = _
    have hp (t : unitInterval) : triangleRegularProject (reflectedZeroHalfPath t) ∈ lowerBase := by
      rw [mem_regularOpen, reflectedZeroHalfPath_coordinate, oppositeZeroPath, if_pos ho]
      exact lowerZeroPath_mem_lowerSlitPlane t
    apply lowerLift_endpoint normalizedSlitBaseLift _ reflectedZeroHalfPath hp
    exact (triangleRegularProject_covering.map_smul _).symm
  rw [hU, hL]

/-- Nonpositive normalization places the reflected zero half-circle in the upper slit. -/
theorem normalizedOverlapTransition_left_of_nonpos (ho : normalizationOrientation ≤ 0) :
    normalizedOverlapTransition 0 = triangleGenerator₁ := by
  have hn : ¬ 0 < normalizationOrientation := not_lt.mpr ho
  apply overlapTransition_eq_of_apply normalizedSlitBaseLift 0
    triangleGenerator₁ meridianLeftOverlapPoint
  have hU : upperLiftOnOverlap normalizedSlitBaseLift 0 meridianLeftOverlapPoint =
      triangleGenerator₁⁻¹ • normalizedRegularMeridianLeftPoint := by
    change upperLift normalizedSlitBaseLift
      ⟨triangleRegularProject normalizedRegularMeridianLeftPoint, _⟩ = _
    have hp (t : unitInterval) : triangleRegularProject (reflectedZeroHalfPath t) ∈ upperBase := by
      rw [mem_regularOpen, reflectedZeroHalfPath_coordinate, oppositeZeroPath, if_neg hn]
      exact upperZeroPath_mem_upperSlitPlane t
    apply upperLift_endpoint normalizedSlitBaseLift _ reflectedZeroHalfPath hp
    exact (triangleRegularProject_covering.map_smul _).symm
  have hL : lowerLiftOnOverlap normalizedSlitBaseLift 0 meridianLeftOverlapPoint =
      normalizedRegularMeridianLeftPoint := by
    change lowerLift normalizedSlitBaseLift
      ⟨triangleRegularProject normalizedRegularMeridianLeftPoint, _⟩ = _
    have hp (t : unitInterval) : triangleRegularProject (liftedZeroHalfPath t) ∈ lowerBase := by
      rw [mem_regularOpen, liftedZeroHalfPath_coordinate, zeroHalfPath, if_neg hn]
      exact lowerZeroPath_mem_lowerSlitPlane t
    apply lowerLift_endpoint normalizedSlitBaseLift _ liftedZeroHalfPath hp
    rfl
  rw [hU, hL, smul_inv_smul]

/-- Positive normalization places the one half-circle in the upper slit. -/
theorem normalizedOverlapTransition_right_of_pos (ho : 0 < normalizationOrientation) :
    normalizedOverlapTransition 2 = triangleGenerator₂ := by
  apply overlapTransition_eq_of_apply normalizedSlitBaseLift 2
    triangleGenerator₂ meridianRightOverlapPoint
  have hU : upperLiftOnOverlap normalizedSlitBaseLift 2 meridianRightOverlapPoint =
      normalizedRegularMeridianRightPoint := by
    change upperLift normalizedSlitBaseLift
      ⟨triangleRegularProject normalizedRegularMeridianRightPoint, _⟩ = _
    have hp (t : unitInterval) : triangleRegularProject (liftedOneHalfPath t) ∈ upperBase := by
      rw [mem_regularOpen, liftedOneHalfPath_coordinate, oneHalfPath, if_pos ho]
      exact upperOnePath_mem_upperSlitPlane t
    apply upperLift_endpoint normalizedSlitBaseLift _ liftedOneHalfPath hp
    rfl
  have hL : lowerLiftOnOverlap normalizedSlitBaseLift 2 meridianRightOverlapPoint =
      triangleGenerator₂ • normalizedRegularMeridianRightPoint := by
    change lowerLift normalizedSlitBaseLift
      ⟨triangleRegularProject normalizedRegularMeridianRightPoint, _⟩ = _
    have hp (t : unitInterval) : triangleRegularProject (reflectedOneHalfPath t) ∈ lowerBase := by
      rw [mem_regularOpen, reflectedOneHalfPath_coordinate, oppositeOnePath, if_pos ho]
      exact lowerOnePath_mem_lowerSlitPlane t
    apply lowerLift_endpoint normalizedSlitBaseLift _ reflectedOneHalfPath hp
    exact (triangleRegularProject_covering.map_smul _).symm
  rw [hU, hL]

/-- Nonpositive normalization places the reflected one half-circle in the upper slit. -/
theorem normalizedOverlapTransition_right_of_nonpos (ho : normalizationOrientation ≤ 0) :
    normalizedOverlapTransition 2 = triangleGenerator₂⁻¹ := by
  have hn : ¬ 0 < normalizationOrientation := not_lt.mpr ho
  apply overlapTransition_eq_of_apply normalizedSlitBaseLift 2
    triangleGenerator₂⁻¹ meridianRightOverlapPoint
  have hU : upperLiftOnOverlap normalizedSlitBaseLift 2 meridianRightOverlapPoint =
      triangleGenerator₂ • normalizedRegularMeridianRightPoint := by
    change upperLift normalizedSlitBaseLift
      ⟨triangleRegularProject normalizedRegularMeridianRightPoint, _⟩ = _
    have hp (t : unitInterval) : triangleRegularProject (reflectedOneHalfPath t) ∈ upperBase := by
      rw [mem_regularOpen, reflectedOneHalfPath_coordinate, oppositeOnePath, if_neg hn]
      exact upperOnePath_mem_upperSlitPlane t
    apply upperLift_endpoint normalizedSlitBaseLift _ reflectedOneHalfPath hp
    exact (triangleRegularProject_covering.map_smul _).symm
  have hL : lowerLiftOnOverlap normalizedSlitBaseLift 2 meridianRightOverlapPoint =
      normalizedRegularMeridianRightPoint := by
    change lowerLift normalizedSlitBaseLift
      ⟨triangleRegularProject normalizedRegularMeridianRightPoint, _⟩ = _
    have hp (t : unitInterval) : triangleRegularProject (liftedOneHalfPath t) ∈ lowerBase := by
      rw [mem_regularOpen, liftedOneHalfPath_coordinate, oneHalfPath, if_neg hn]
      exact lowerOnePath_mem_lowerSlitPlane t
    apply lowerLift_endpoint normalizedSlitBaseLift _ liftedOneHalfPath hp
    rfl
  rw [hU, hL, inv_smul_smul]

/-- The actual left transition, with both possible normalization orientations explicit. -/
theorem normalizedOverlapTransition_left :
    normalizedOverlapTransition 0 =
      if 0 < normalizationOrientation then triangleGenerator₁⁻¹ else triangleGenerator₁ := by
  by_cases ho : 0 < normalizationOrientation
  · rw [if_pos ho]
    exact normalizedOverlapTransition_left_of_pos ho
  · rw [if_neg ho]
    exact normalizedOverlapTransition_left_of_nonpos (le_of_not_gt ho)

/-- The middle actual transition remains the identity at the canonical geometric basepoint. -/
@[simp] theorem normalizedOverlapTransition_middle : normalizedOverlapTransition 1 = 1 :=
  overlapTransition_middle normalizedSlitBaseLift

/-- The actual right transition has the opposite inverse convention to the left one. -/
theorem normalizedOverlapTransition_right :
    normalizedOverlapTransition 2 =
      if 0 < normalizationOrientation then triangleGenerator₂ else triangleGenerator₂⁻¹ := by
  by_cases ho : 0 < normalizationOrientation
  · rw [if_pos ho]
    exact normalizedOverlapTransition_right_of_pos ho
  · rw [if_neg ho]
    exact normalizedOverlapTransition_right_of_nonpos (le_of_not_gt ho)

/-- The three actual slit-chart transitions in left, middle, right order. -/
theorem normalizedOverlapTransition_eq (i : Fin 3) :
    normalizedOverlapTransition i =
      ![if 0 < normalizationOrientation then triangleGenerator₁⁻¹ else triangleGenerator₁,
        1,
        if 0 < normalizationOrientation then triangleGenerator₂ else triangleGenerator₂⁻¹] i := by
  fin_cases i
  · exact normalizedOverlapTransition_left
  · exact normalizedOverlapTransition_middle
  · exact normalizedOverlapTransition_right

/-- The identified constants compare the actual sections at every overlap point. -/
theorem normalizedOverlapTransition_apply (i : Fin 3) (x : overlapBase i) :
    normalizedOverlapTransition i • upperLiftOnOverlap normalizedSlitBaseLift i x =
      lowerLiftOnOverlap normalizedSlitBaseLift i x :=
  overlapTransition_apply normalizedSlitBaseLift i x

end Wikipedia.HopfProblem.TrianglePeriodFamily.Homology
