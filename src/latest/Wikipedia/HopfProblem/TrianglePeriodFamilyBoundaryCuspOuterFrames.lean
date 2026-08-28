import Wikipedia.HopfProblem.TrianglePeriodFamilyBoundaryCuspOuterFramesCore
import Wikipedia.HopfProblem.TrianglePeriodFamilyBoundaryOrientation

/-!
# Actual quarter frames and cusp endpoint of the clockwise outer lift

Uniqueness of covering lifts is applied on the three closed parameter
intervals. The normalized lower section starts the lift. The proved left
transition gives the first-generator frame throughout the upper piece;
the proved right transition gives the product frame on the final lower
piece. Thus both actual overlap values have the same upper-section frame,
and the actual endpoint is the inverse cusp generator.
-/

noncomputable section

open Set Topology

namespace Wikipedia.HopfProblem.TrianglePeriodFamily.Boundary.Cusp

open SpecialPeriods SpecialPeriods.Triangle Homology

private theorem outerLift_interval_unique {a b : ℝ}
    (s : C(Icc a b, TriangleRegularPoint))
    (hs : ∀ t, triangleRegularProject (s t) = outerClockwiseRegularCurve t)
    (t₀ : Icc a b) (h₀ : outerClockwiseLift t₀ = s t₀) (t : Icc a b) :
    outerClockwiseLift t = s t := by
  let : PreconnectedSpace (Icc a b) := Subtype.preconnectedSpace isPreconnected_Icc
  exact congrFun (triangleRegularProject_covering.isCoveringMap.eq_of_comp_eq
    (outerClockwiseLift.continuous.comp continuous_subtype_val) s.continuous
    (by
      funext u
      exact (outerClockwiseLift_projection u).trans (hs u).symm) t₀ h₀) t

/-- The initial quarter is literally the normalized lower slit section. -/
theorem outerClockwiseLift_lower_initial (t : ℝ) (ht₀ : 0 ≤ t) (ht₁ : t ≤ 1 / 4) :
    outerClockwiseLift t = lowerLift normalizedSlitBaseLift
      ⟨outerClockwiseRegularCurve t, outerClockwiseRegularCurve_mem_lower_piece t
        ht₀ (by linarith) (Or.inl ht₁)⟩ := by
  let q : C(Icc (0 : ℝ) (1 / 4), lowerBase) :=
    ⟨fun s => ⟨outerClockwiseRegularCurve s,
      outerClockwiseRegularCurve_mem_lower_piece s s.property.1
        (by linarith [s.property.2]) (Or.inl s.property.2)⟩,
      (outerClockwiseRegularCurve.continuous.comp continuous_subtype_val).subtype_mk _⟩
  apply outerLift_interval_unique ((lowerLift normalizedSlitBaseLift).comp q)
    (fun s => lowerLift_project normalizedSlitBaseLift (q s))
    (⟨0, by constructor <;> norm_num⟩ : Icc (0 : ℝ) (1 / 4)) _
    (⟨t, ht₀, ht₁⟩ : Icc (0 : ℝ) (1 / 4))
  rw [outerClockwiseLift_zero]
  change lowerLift normalizedSlitBaseLift outerClockwiseLowerBasepoint =
    lowerLift normalizedSlitBaseLift (q ⟨0, by constructor <;> norm_num⟩)
  apply congrArg (lowerLift normalizedSlitBaseLift)
  apply Subtype.ext
  exact outerClockwiseRegularCurve_zero.symm

/-- The first actual overlap point is in the positive first-generator upper frame. -/
theorem outerClockwiseLift_quarter_frame :
    outerClockwiseLift (1 / 4) = triangleGenerator₁ •
      upperLiftOnOverlap normalizedSlitBaseLift 0 outerClockwiseQuarterPoint := by
  have h := normalizedOverlapTransition_apply 0 outerClockwiseQuarterPoint
  rw [normalizedOverlapTransition_left_of_nonpos normalizationOrientation_nonpos] at h
  calc
    outerClockwiseLift (1 / 4) =
        lowerLiftOnOverlap normalizedSlitBaseLift 0 outerClockwiseQuarterPoint :=
      outerClockwiseLift_lower_initial _ (by norm_num) le_rfl
    _ = triangleGenerator₁ •
        upperLiftOnOverlap normalizedSlitBaseLift 0 outerClockwiseQuarterPoint := h.symm

/-- Uniqueness preserves that same first-generator frame along the entire upper piece. -/
theorem outerClockwiseLift_upper_middle (t : ℝ)
    (ht₀ : 1 / 4 ≤ t) (ht₁ : t ≤ 3 / 4) :
    outerClockwiseLift t = triangleGenerator₁ • upperLift normalizedSlitBaseLift
      ⟨outerClockwiseRegularCurve t,
        outerClockwiseRegularCurve_mem_upper_piece t ht₀ ht₁⟩ := by
  let q : C(Icc (1 / 4 : ℝ) (3 / 4), upperBase) :=
    ⟨fun s => ⟨outerClockwiseRegularCurve s,
      outerClockwiseRegularCurve_mem_upper_piece s s.property.1 s.property.2⟩,
      (outerClockwiseRegularCurve.continuous.comp continuous_subtype_val).subtype_mk _⟩
  let s : C(Icc (1 / 4 : ℝ) (3 / 4), TriangleRegularPoint) :=
    ⟨fun u => triangleGenerator₁ • upperLift normalizedSlitBaseLift (q u),
      (triangleRegularProject_covering.continuous_const_smul triangleGenerator₁).comp
        ((upperLift normalizedSlitBaseLift).continuous.comp q.continuous)⟩
  apply outerLift_interval_unique s _
    (⟨1 / 4, by constructor <;> norm_num⟩ : Icc (1 / 4 : ℝ) (3 / 4)) _
    (⟨t, ht₀, ht₁⟩ : Icc (1 / 4 : ℝ) (3 / 4))
  · intro u
    exact (triangleRegularProject_covering.map_smul triangleGenerator₁).trans
      (upperLift_project normalizedSlitBaseLift (q u))
  · exact outerClockwiseLift_quarter_frame

/-- The second overlap point has exactly the same positive first-generator upper frame. -/
theorem outerClockwiseLift_threeQuarters_frame :
    outerClockwiseLift (3 / 4) = triangleGenerator₁ •
      upperLiftOnOverlap normalizedSlitBaseLift 2 outerClockwiseThreeQuarterPoint :=
  outerClockwiseLift_upper_middle _ (by norm_num) le_rfl

private theorem outerClockwiseLift_threeQuarters_lower :
    outerClockwiseLift (3 / 4) = (triangleGenerator₁ * triangleGenerator₂) •
      lowerLiftOnOverlap normalizedSlitBaseLift 2 outerClockwiseThreeQuarterPoint := by
  have h := normalizedOverlapTransition_apply 2 outerClockwiseThreeQuarterPoint
  rw [normalizedOverlapTransition_right_of_nonpos normalizationOrientation_nonpos] at h
  have he := congrArg (fun z : TriangleRegularPoint => triangleGenerator₂ • z) h
  simp only [smul_inv_smul] at he
  rw [outerClockwiseLift_threeQuarters_frame, mul_smul, ← he]

/-- The final lower quarter carries the actual product of the two deck generators. -/
theorem outerClockwiseLift_lower_final (t : ℝ)
    (ht₀ : 3 / 4 ≤ t) (ht₁ : t ≤ 1) :
    outerClockwiseLift t = (triangleGenerator₁ * triangleGenerator₂) •
      lowerLift normalizedSlitBaseLift
        ⟨outerClockwiseRegularCurve t, outerClockwiseRegularCurve_mem_lower_piece t
          (by linarith) ht₁ (Or.inr ht₀)⟩ := by
  let q : C(Icc (3 / 4 : ℝ) 1, lowerBase) :=
    ⟨fun s => ⟨outerClockwiseRegularCurve s,
      outerClockwiseRegularCurve_mem_lower_piece s (by linarith [s.property.1])
        s.property.2 (Or.inr s.property.1)⟩,
      (outerClockwiseRegularCurve.continuous.comp continuous_subtype_val).subtype_mk _⟩
  let s : C(Icc (3 / 4 : ℝ) 1, TriangleRegularPoint) :=
    ⟨fun u => (triangleGenerator₁ * triangleGenerator₂) •
      lowerLift normalizedSlitBaseLift (q u),
      (triangleRegularProject_covering.continuous_const_smul
        (triangleGenerator₁ * triangleGenerator₂)).comp
          ((lowerLift normalizedSlitBaseLift).continuous.comp q.continuous)⟩
  apply outerLift_interval_unique s _
    (⟨3 / 4, by constructor <;> norm_num⟩ : Icc (3 / 4 : ℝ) 1) _
    (⟨t, ht₀, ht₁⟩ : Icc (3 / 4 : ℝ) 1)
  · intro u
    exact (triangleRegularProject_covering.map_smul (triangleGenerator₁ * triangleGenerator₂)).trans
      (lowerLift_project normalizedSlitBaseLift (q u))
  · exact outerClockwiseLift_threeQuarters_lower

/-- The endpoint is derived from the actual slit lifts and equals the inverse cusp deck action. -/
theorem outerClockwiseLift_one :
    outerClockwiseLift 1 = triangleCuspGenerator⁻¹ • outerClockwiseBaseLift := by
  have h := outerClockwiseLift_lower_final 1 (by norm_num) le_rfl
  have hb : lowerLift normalizedSlitBaseLift
      ⟨outerClockwiseRegularCurve 1, outerClockwiseRegularCurve_mem_lower_piece 1
        (by norm_num) le_rfl (Or.inr (by norm_num))⟩ = outerClockwiseBaseLift := by
    apply congrArg (lowerLift normalizedSlitBaseLift)
    apply Subtype.ext
    exact outerClockwiseRegularCurve_one
  rw [hb] at h
  simpa only [triangleCuspGenerator, inv_inv] using h

/-- The proved single endpoint fixes every real-time integer translate of the actual lift. -/
theorem outerClockwiseLift_translate (k : ℤ) (t : ℝ) :
    outerClockwiseLift (t + k) = (triangleCuspGenerator ^ (-k)) • outerClockwiseLift t := by
  apply realCurveLift_translate outerClockwiseRegularCurve outerClockwiseBaseLift
    (outerClockwiseBaseLift_project.trans outerClockwiseRegularCurve_zero.symm)
    outerClockwiseRegularCurve_periodic triangleCuspGenerator _ k t
  exact outerClockwiseLift_one

/-- One positive real period has the same inverse-cusp convention as the native boundary. -/
theorem outerClockwiseLift_add_one (t : ℝ) :
    outerClockwiseLift (t + 1) = triangleCuspGenerator⁻¹ • outerClockwiseLift t := by
  simpa only [Int.cast_one, zpow_neg_one] using outerClockwiseLift_translate 1 t

/-- The actual projection over the shortened upper cylinder lies in the upper slit. -/
theorem outerClockwiseLift_projection_mem_upperBase (t : ℝ)
    (ht₀ : 1 / 8 < t) (ht₁ : t < 7 / 8) :
    triangleRegularProject (outerClockwiseLift t) ∈ upperBase := by
  rw [outerClockwiseLift_projection]
  exact outerClockwiseRegularCurve_mem_upperBase t ht₀ ht₁

/-- The actual projection over the shortened lower cylinder lies in the lower slit. -/
theorem outerClockwiseLift_projection_mem_lowerBase (t : ℝ)
    (ht₀ : -(3 / 8) < t) (ht₁ : t < 3 / 8) :
    triangleRegularProject (outerClockwiseLift t) ∈ lowerBase := by
  rw [outerClockwiseLift_projection]
  exact outerClockwiseRegularCurve_mem_lowerBase t ht₀ ht₁

end Wikipedia.HopfProblem.TrianglePeriodFamily.Boundary.Cusp
