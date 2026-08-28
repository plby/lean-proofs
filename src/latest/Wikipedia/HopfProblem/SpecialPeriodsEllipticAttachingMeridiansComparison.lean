import Wikipedia.HopfProblem.SpecialPeriodsEllipticAttachingMeridiansAnalyticCircle
import Wikipedia.HopfProblem.SpecialPeriodsEllipticAttachingMeridiansCircle
import Wikipedia.HopfProblem.SpecialPeriodsEllipticAttachingMeridiansHomotopyOperations
import Wikipedia.HopfProblem.TrianglePeriodFamilyFundamentalGroupMeridianLifts

/-!
# Actual peripheral comparison with the fixed jointly free meridians

Compose the actual small analytic-circle deformation with the explicit
round-circle deformation, then pull the entire continuous square back
through the actual regular-plane homeomorphism. The resulting tail is a
genuine path in the original regular base. Its final loop is the fixed
compatible meridian, or its inverse, with one common orientation choice
for both punctures. An arbitrary additional basepoint path contributes
only the explicitly displayed conjugating loop.
-/

noncomputable section

open Set Topology

namespace Wikipedia.HopfProblem.SpecialPeriods.EllipticAttachingMeridians

open Triangle TrianglePeriodFamily.Meridians RiemannMapping

/-- The clockwise representative of the already fixed compatible basis.
The same normalization choice governs both generators. -/
def clockwiseRegularMeridian (b : Bool) :
    Path (triangleRegularProject normalizedRegularMeridianBasepoint)
      (triangleRegularProject normalizedRegularMeridianBasepoint) :=
  if normalizationReversesMeridians then compatibleRegularMeridian b
  else (compatibleRegularMeridian b).symm

/-- The orientation is checked on every point of the actual paths. -/
theorem clockwiseRegularMeridian_coordinate (b : Bool) (t : unitInterval) :
    triangleRegularPlaneHomeomorph (clockwiseRegularMeridian b t) =
      fixedClockwiseMeridian b t := by
  by_cases ho : 0 < normalizationOrientation
  · have h := compatibleRegularMeridian_coordinate b t
    rw [compatiblePlanarMeridian_eq, if_pos ho] at h
    simpa only [clockwiseRegularMeridian, normalizationReversesMeridians,
      decide_eq_true_eq.mpr ho, ↓reduceIte, fixedClockwiseMeridian] using h
  · have h := compatibleRegularMeridian_coordinate b (unitInterval.symm t)
    rw [compatiblePlanarMeridian_eq, if_neg ho] at h
    simpa only [clockwiseRegularMeridian, normalizationReversesMeridians,
      decide_eq_false_iff_not.mpr ho, Bool.false_eq_true, ↓reduceIte,
      fixedClockwiseMeridian, Path.symm_apply, Function.comp_apply] using h

/-- The genuine clockwise class has the common sign required by the
fixed jointly free basis, without replacing either generator. -/
theorem clockwiseRegularMeridian_class (b : Bool) :
    FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk (clockwiseRegularMeridian b)) =
      if normalizationReversesMeridians then compatibleRegularMeridianClass b
      else (compatibleRegularMeridianClass b)⁻¹ := by
  by_cases h : normalizationReversesMeridians = true
  · simp only [clockwiseRegularMeridian, h, ↓reduceIte]
    rfl
  · have hn : normalizationReversesMeridians = false := Bool.eq_false_iff.mpr h
    simp only [clockwiseRegularMeridian, hn, Bool.false_eq_true, ↓reduceIte]
    rw [FundamentalGroup.inv_def]
    exact Path.Homotopic.Quotient.mk_symm _

namespace LinearizationControl

variable {f : ℂ → ℂ} (D : LinearizationControl f)
  (b : Bool) (hc : f 0 = center b) (A : ℂ) (hA : A ≠ 0) (hAr : ‖A‖ < D.radius)

/-- Both stages are actual continuous loop squares: analytic to linear,
then the explicit coefficient deformation to the fixed clockwise loop. -/
def analyticMeridianSquare :
    LoopSquare (D.analyticCirclePath b hc A hA hAr) (fixedClockwiseMeridian b) :=
  (D.analyticCircleSquare b hc A hA hAr).trans
    (clockwiseCircleSquare b (deriv f 0 * A) (D.linearCoefficient_ne_zero A hA)
      (D.linearCoefficient_norm_lt_one A hAr))

@[simp] theorem analyticMeridianSquare_tail :
    (D.analyticMeridianSquare b hc A hA hAr).tail =
      (D.analyticCircleSquare b hc A hA hAr).tail.trans
        (clockwiseCircleTail b (deriv f 0 * A) (D.linearCoefficient_ne_zero A hA)
          (D.linearCoefficient_norm_lt_one A hAr)) :=
  LoopSquare.tail_trans _ _

variable {a : TriangleRegularQuotient} (p : Path a a)
  (hp : ∀ t : unitInterval,
    (triangleRegularPlaneHomeomorph (p t) : ℂ) = f (A * clockwiseUnit t))

/-- Pull the actual two-stage deformation back to the original regular
base, retaining the fixed source basepoint and the fixed meridian loop. -/
def regularMeridianSquare : LoopSquare p (clockwiseRegularMeridian b) := by
  let S := D.analyticMeridianSquare b hc A hA hAr
  refine {
    map := ⟨fun tu => triangleRegularPlaneHomeomorph.symm (S.map tu),
      triangleRegularPlaneHomeomorph.symm.continuous.comp S.map.continuous⟩
    initial := ?_
    final := ?_
    closed := ?_ }
  · intro t
    have he : S.map (0, t) = triangleRegularPlaneHomeomorph (p t) := by
      apply Subtype.ext
      exact (congrArg Subtype.val (S.initial t)).trans (hp t).symm
    change triangleRegularPlaneHomeomorph.symm (S.map (0, t)) = p t
    rw [he, triangleRegularPlaneHomeomorph.symm_apply_apply]
  · intro t
    change triangleRegularPlaneHomeomorph.symm (S.map (1, t)) = clockwiseRegularMeridian b t
    rw [S.final t, ← clockwiseRegularMeridian_coordinate b t,
      triangleRegularPlaneHomeomorph.symm_apply_apply]
  · intro t
    exact congrArg triangleRegularPlaneHomeomorph.symm (S.closed t)

/-- The resulting path from the local basepoint to the fixed common
basepoint is the actual moving basepoint of the constructed square. -/
def regularMeridianTail :
    Path a (triangleRegularProject normalizedRegularMeridianBasepoint) :=
  (D.regularMeridianSquare b hc A hA hAr p hp).tail

@[simp] theorem regularMeridianTail_coordinate (t : unitInterval) :
    triangleRegularPlaneHomeomorph (D.regularMeridianTail b hc A hA hAr p hp t) =
      (D.analyticMeridianSquare b hc A hA hAr).tail t :=
  triangleRegularPlaneHomeomorph.apply_symm_apply _

/-- Genuine based peripheral conjugacy in the original regular base. -/
theorem regularMeridian_homotopic_conjugate :
    p.Homotopic ((D.regularMeridianTail b hc A hA hAr p hp).trans
      ((clockwiseRegularMeridian b).trans (D.regularMeridianTail b hc A hA hAr p hp).symm)) :=
  (D.regularMeridianSquare b hc A hA hAr p hp).homotopic_conjugate

/-- Any independently chosen attaching tail contributes exactly this
conjugating based loop; it is not asserted to be a preferred generator. -/
theorem regularMeridian_whisker_conjugate
    (τ : Path (triangleRegularProject normalizedRegularMeridianBasepoint) a) :
    (τ.trans (p.trans τ.symm)).Homotopic
      ((τ.trans (D.regularMeridianTail b hc A hA hAr p hp)).trans
        ((clockwiseRegularMeridian b).trans
          (τ.trans (D.regularMeridianTail b hc A hA hAr p hp)).symm)) :=
  (D.regularMeridianSquare b hc A hA hAr p hp).homotopic_whisker_conjugate τ

/-- The corresponding actual fundamental-group path-change formula,
including the common orientation sign for both fixed basis letters. -/
theorem regularMeridian_fundamentalGroup_pathChange :
    FundamentalGroup.fundamentalGroupMulEquivOfPath
        (D.regularMeridianTail b hc A hA hAr p hp)
        (FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk p)) =
      if normalizationReversesMeridians then compatibleRegularMeridianClass b
      else (compatibleRegularMeridianClass b)⁻¹ :=
  (D.regularMeridianSquare b hc A hA hAr p hp).fundamentalGroup_pathChange.trans
    (clockwiseRegularMeridian_class b)

end LinearizationControl

end Wikipedia.HopfProblem.SpecialPeriods.EllipticAttachingMeridians
