import Wikipedia.HopfProblem.SpecialPeriodsEllipticAttachingMeridiansCircleBasic
import Wikipedia.HopfProblem.SpecialPeriodsEllipticAttachingMeridiansCircleCoefficient
import Wikipedia.HopfProblem.SpecialPeriodsEllipticAttachingMeridiansHomotopy
import Wikipedia.HopfProblem.TriangleRegularBaseFundamentalGroupGenerators

/-!
# Clockwise attaching circles and the fixed positive meridian basis

Exponentiating the affine interpolation of two fixed logarithms moves a
nonzero small circle coefficient to the original meridian coefficient.
The resulting continuous square stays in the literal twice-punctured
plane. Its moving basepoint is retained as an actual path, and the square
proves based conjugacy with the inverse of the fixed positive meridian.
-/

noncomputable section

open Set Topology

namespace Wikipedia.HopfProblem.SpecialPeriods.EllipticAttachingMeridians

open Triangle

/-- The explicit continuous family of clockwise loops joining any
nonzero small coefficient to the original fixed meridian coefficient. -/
def clockwiseCircleSquare (b : Bool) (A : ℂ) (hA : A ≠ 0) (hAn : ‖A‖ < 1) :
    LoopSquare (clockwiseCirclePath b A hA hAn) (fixedClockwiseMeridian b) where
  map :=
    { toFun st :=
        ⟨clockwiseCircle b (coefficientInterpolation A (anchor b) st.1) st.2,
          clockwiseCircle_mem b _
            (coefficientInterpolation_ne_zero A (anchor b) st.1)
            (coefficientInterpolation_norm_lt_one A (anchor b) st.1 hA
              (anchor_ne_zero b) hAn (norm_anchor_lt_one b)) st.2⟩
      continuous_toFun :=
        (continuous_const.add
          (((coefficientInterpolation_continuous A (anchor b)).comp continuous_fst).mul
            (clockwiseUnit_continuous.comp continuous_snd))).subtype_mk _ }
  initial t := by
    apply Subtype.ext
    change clockwiseCircle b (coefficientInterpolation A (anchor b) 0) t =
      clockwiseCircle b A t
    rw [coefficientInterpolation_zero A (anchor b) hA]
  final t := by
    apply Subtype.ext
    change clockwiseCircle b (coefficientInterpolation A (anchor b) 1) t =
      (fixedClockwiseMeridian b t : ℂ)
    rw [coefficientInterpolation_one A (anchor b) (anchor_ne_zero b)]
    exact (fixedClockwiseMeridian_coe b t).symm
  closed s := by
    apply Subtype.ext
    exact (clockwiseCircle_zero b (coefficientInterpolation A (anchor b) s)).trans
      (clockwiseCircle_one b (coefficientInterpolation A (anchor b) s)).symm

@[simp] theorem clockwiseCircleSquare_map_coe (b : Bool) (A : ℂ)
    (hA : A ≠ 0) (hAn : ‖A‖ < 1) (s t : unitInterval) :
    ((clockwiseCircleSquare b A hA hAn).map (s, t) : ℂ) =
      clockwiseCircle b (coefficientInterpolation A (anchor b) s) t := rfl

/-- The actual basepoint path traced by the coefficient interpolation. -/
def clockwiseCircleTail (b : Bool) (A : ℂ) (hA : A ≠ 0) (hAn : ‖A‖ < 1) :
    Path (circleBasepoint b A hA hAn) meridianBasepoint :=
  (clockwiseCircleSquare b A hA hAn).tail

@[simp] theorem clockwiseCircleTail_coe (b : Bool) (A : ℂ)
    (hA : A ≠ 0) (hAn : ‖A‖ < 1) (s : unitInterval) :
    (clockwiseCircleTail b A hA hAn s : ℂ) =
      center b + coefficientInterpolation A (anchor b) s :=
  clockwiseCircle_zero b (coefficientInterpolation A (anchor b) s)

/-- The based conjugacy follows from the actual continuous square, with
its explicit basepoint path and the original fixed clockwise meridian. -/
theorem clockwiseCircle_homotopic_conjugate (b : Bool) (A : ℂ)
    (hA : A ≠ 0) (hAn : ‖A‖ < 1) :
    (clockwiseCirclePath b A hA hAn).Homotopic
      ((clockwiseCircleTail b A hA hAn).trans
        ((fixedClockwiseMeridian b).trans (clockwiseCircleTail b A hA hAn).symm)) :=
  (clockwiseCircleSquare b A hA hAn).homotopic_conjugate

/-- The fixed clockwise loop is exactly the inverse of the original
positive meridian class used by the chosen free basis. -/
theorem fixedClockwiseMeridian_class (b : Bool) :
    FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk (fixedClockwiseMeridian b)) =
      (meridianClass b)⁻¹ := by
  rw [FundamentalGroup.inv_def]
  change Path.Homotopic.Quotient.mk
      ((if b then positiveMeridianOne else positiveMeridianZero).symm) =
    (Path.Homotopic.Quotient.mk
      (if b then positiveMeridianOne else positiveMeridianZero)).symm
  exact Path.Homotopic.Quotient.mk_symm _

/-- Changing the basepoint along the actual coefficient path sends the
small clockwise circle to the inverse of the fixed positive meridian. -/
theorem clockwiseCircle_fundamentalGroup_pathChange (b : Bool) (A : ℂ)
    (hA : A ≠ 0) (hAn : ‖A‖ < 1) :
    FundamentalGroup.fundamentalGroupMulEquivOfPath (clockwiseCircleTail b A hA hAn)
        (FundamentalGroup.fromPath
          (Path.Homotopic.Quotient.mk (clockwiseCirclePath b A hA hAn))) =
      (meridianClass b)⁻¹ :=
  (clockwiseCircleSquare b A hA hAn).fundamentalGroup_pathChange.trans
    (fixedClockwiseMeridian_class b)

end Wikipedia.HopfProblem.SpecialPeriods.EllipticAttachingMeridians
