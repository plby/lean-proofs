import Wikipedia.HopfProblem.ConifoldPolarRegionsLevels
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Topology.Homeomorph.Lemmas

/-!
# Compact sublevels of the literal determinant-one matrix model

The squared Frobenius norm becomes `2 + 4 ‖b‖²` in the explicit polar
coordinates.  Its sublevels therefore identify with closed Euclidean
three-balls times the original unit three-sphere.  All sets use their native
subspace topologies, and both directions retain the original matrix formulas.
-/

namespace Wikipedia.HopfProblem.ConifoldPolar

open ConifoldStandardBoundary

/-- A radial Frobenius sublevel in the original determinant-one matrix group. -/
def frobeniusSublevel (ρ : ℝ) : Set SpecialLinear :=
  {M | frobeniusSq M.val ≤ 2 + 4 * ρ ^ 2}

theorem mem_frobeniusSublevel_iff (ρ : ℝ) (hρ : 0 ≤ ρ) (M : SpecialLinear) :
    M ∈ frobeniusSublevel ρ ↔ ‖(forward M).1‖ ≤ ρ := by
  change frobeniusSq M.val ≤ 2 + 4 * ρ ^ 2 ↔ _
  rw [frobeniusSq_eq, ← sq_le_sq₀ (norm_nonneg _) hρ]
  constructor <;> intro h <;> linarith

/-- Splitting the first-coordinate radius condition from the product. -/
private def sublevelProductHomeomorph (ρ : ℝ) :
    {q : Base × NormalSphere // ‖q.1‖ ≤ ρ} ≃ₜ
      ↥(Metric.closedBall (0 : Base) ρ) × NormalSphere where
  toFun q := (⟨q.val.1, by
    simpa only [Metric.mem_closedBall, dist_zero_right] using q.property⟩, q.val.2)
  invFun q := ⟨(q.1.val, q.2), by
    simpa only [Metric.mem_closedBall, dist_zero_right] using q.1.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := (continuous_subtype_val.fst.subtype_mk _).prodMk
    continuous_subtype_val.snd
  continuous_invFun := ((continuous_subtype_val.comp continuous_fst).prodMk
    continuous_snd).subtype_mk _

/-- Restricting the explicit polar homeomorphism to a native Frobenius sublevel. -/
noncomputable def sublevelHomeomorph (ρ : ℝ) (hρ : 0 ≤ ρ) :
    ↥(frobeniusSublevel ρ) ≃ₜ ↥(Metric.closedBall (0 : Base) ρ) × NormalSphere :=
  (homeomorph.subtype (mem_frobeniusSublevel_iff ρ hρ)).trans
    (sublevelProductHomeomorph ρ)

@[simp] theorem sublevelHomeomorph_fst_val (ρ : ℝ) (hρ : 0 ≤ ρ)
    (M : ↥(frobeniusSublevel ρ)) :
    (sublevelHomeomorph ρ hρ M).1.val =
      baseCoordinates (positivePart M.val.val) := rfl

@[simp] theorem sublevelHomeomorph_snd_val (ρ : ℝ) (hρ : 0 ≤ ρ)
    (M : ↥(frobeniusSublevel ρ)) :
    (sublevelHomeomorph ρ hρ M).2.val =
      normalCoordinates (unitaryPart M.val.val) := rfl

@[simp] theorem sublevelHomeomorph_symm_val_val (ρ : ℝ) (hρ : 0 ≤ ρ)
    (q : ↥(Metric.closedBall (0 : Base) ρ) × NormalSphere) :
    ((sublevelHomeomorph ρ hρ).symm q).val.val =
      positiveMatrix q.1.val * unitaryMatrix q.2.val := rfl

/-- Compactness is proved for the sublevel's existing subspace topology. -/
theorem isCompact_frobeniusSublevel (ρ : ℝ) (hρ : 0 ≤ ρ) :
    IsCompact (frobeniusSublevel ρ) :=
  isCompact_iff_compactSpace.mpr (sublevelHomeomorph ρ hρ).symm.compactSpace

/-- The actual right diagonal circle map preserves every Frobenius sublevel. -/
noncomputable def sublevelCircleAction (ρ : ℝ) (u : ℂ) (hu : ‖u‖ = 1)
    (M : ↥(frobeniusSublevel ρ)) : ↥(frobeniusSublevel ρ) :=
  ⟨circleAction u hu M.val, by
    change frobeniusSq (rightCircle u M.val.val) ≤ 2 + 4 * ρ ^ 2
    rw [frobeniusSq_rightCircle u hu]
    exact M.property⟩

@[simp] theorem sublevelCircleAction_val_val (ρ : ℝ) (u : ℂ) (hu : ‖u‖ = 1)
    (M : ↥(frobeniusSublevel ρ)) :
    (sublevelCircleAction ρ u hu M).val.val = rightCircle u M.val.val := rfl

/-- The sublevel homeomorphism fixes the closed-ball coordinate under the circle action. -/
theorem sublevelHomeomorph_circleAction (ρ : ℝ) (hρ : 0 ≤ ρ) (u : ℂ) (hu : ‖u‖ = 1)
    (M : ↥(frobeniusSublevel ρ)) :
    sublevelHomeomorph ρ hρ (sublevelCircleAction ρ u hu M) =
      ((sublevelHomeomorph ρ hρ M).1,
        sphereRotation u hu (sublevelHomeomorph ρ hρ M).2) := by
  have h := forward_circleAction u hu M.val
  have hfst := congrArg Prod.fst h
  have hsnd := congrArg Prod.snd h
  apply Prod.ext
  · apply Subtype.ext
    exact hfst
  · exact hsnd

/-- A Frobenius sublevel indexed by its literal numerical bound. -/
def frobeniusBound (R : ℝ) : Set SpecialLinear := {M | frobeniusSq M.val ≤ R}

/-- The exact Euclidean radius associated to the squared Frobenius bound. -/
noncomputable def boundRadius (R : ℝ) : ℝ := Real.sqrt ((R - 2) / 4)

theorem boundRadius_nonneg (R : ℝ) : 0 ≤ boundRadius R := Real.sqrt_nonneg _

theorem two_add_four_boundRadius_sq (R : ℝ) (hR : 2 ≤ R) :
    2 + 4 * boundRadius R ^ 2 = R := by
  rw [boundRadius, Real.sq_sqrt (by linarith : 0 ≤ (R - 2) / 4)]
  ring

theorem frobeniusBound_eq_sublevel (R : ℝ) (hR : 2 ≤ R) :
    frobeniusBound R = frobeniusSublevel (boundRadius R) := by
  ext M
  simp only [frobeniusBound, frobeniusSublevel, Set.mem_ofPred_eq,
    two_add_four_boundRadius_sq R hR]

/-- Any squared Frobenius bound at least two yields the stated closed-ball product. -/
noncomputable def boundHomeomorph (R : ℝ) (hR : 2 ≤ R) :
    ↥(frobeniusBound R) ≃ₜ ↥(Metric.closedBall (0 : Base) (boundRadius R)) × NormalSphere :=
  (Homeomorph.setCongr (frobeniusBound_eq_sublevel R hR)).trans
    (sublevelHomeomorph (boundRadius R) (boundRadius_nonneg R))

@[simp] theorem boundHomeomorph_fst_val (R : ℝ) (hR : 2 ≤ R)
    (M : ↥(frobeniusBound R)) :
    (boundHomeomorph R hR M).1.val = baseCoordinates (positivePart M.val.val) := rfl

@[simp] theorem boundHomeomorph_snd_val (R : ℝ) (hR : 2 ≤ R)
    (M : ↥(frobeniusBound R)) :
    (boundHomeomorph R hR M).2.val = normalCoordinates (unitaryPart M.val.val) := rfl

@[simp] theorem boundHomeomorph_symm_val_val (R : ℝ) (hR : 2 ≤ R)
    (q : ↥(Metric.closedBall (0 : Base) (boundRadius R)) × NormalSphere) :
    ((boundHomeomorph R hR).symm q).val.val =
      positiveMatrix q.1.val * unitaryMatrix q.2.val := rfl

/-- The original circle map restricts to a sublevel with any literal numerical bound. -/
noncomputable def boundCircleAction (R : ℝ) (u : ℂ) (hu : ‖u‖ = 1)
    (M : ↥(frobeniusBound R)) : ↥(frobeniusBound R) :=
  ⟨circleAction u hu M.val, by
    change frobeniusSq (rightCircle u M.val.val) ≤ R
    rw [frobeniusSq_rightCircle u hu]
    exact M.property⟩

@[simp] theorem boundCircleAction_val_val (R : ℝ) (u : ℂ) (hu : ‖u‖ = 1)
    (M : ↥(frobeniusBound R)) :
    (boundCircleAction R u hu M).val.val = rightCircle u M.val.val := rfl

theorem boundHomeomorph_circleAction (R : ℝ) (hR : 2 ≤ R) (u : ℂ) (hu : ‖u‖ = 1)
    (M : ↥(frobeniusBound R)) :
    boundHomeomorph R hR (boundCircleAction R u hu M) =
      ((boundHomeomorph R hR M).1,
        sphereRotation u hu (boundHomeomorph R hR M).2) := by
  have h := forward_circleAction u hu M.val
  have hfst := congrArg Prod.fst h
  have hsnd := congrArg Prod.snd h
  apply Prod.ext
  · apply Subtype.ext
    exact hfst
  · exact hsnd

/-- Every finite Frobenius sublevel is compact, including the empty bounds below two. -/
theorem isCompact_frobeniusBound (R : ℝ) : IsCompact (frobeniusBound R) := by
  by_cases hR : 2 ≤ R
  · rw [frobeniusBound_eq_sublevel R hR]
    exact isCompact_frobeniusSublevel (boundRadius R) (boundRadius_nonneg R)
  · have he : frobeniusBound R = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      intro M hM
      exact hR ((two_le_frobeniusSq M).trans hM)
    rw [he]
    exact isCompact_empty

end Wikipedia.HopfProblem.ConifoldPolar
