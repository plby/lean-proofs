import Wikipedia.HopfProblem.CuspBoundaryTopVanishingPeriods
import Wikipedia.HopfProblem.CuspBoundaryTopVanishingCircle
import Wikipedia.HopfProblem.CuspBoundaryTopVanishingBoundary

/-!
# The actual gamma-zero boundary collapses over the zero base circle

The original restricted mapping torus is represented by all real angular
coordinates and the genuine gamma-zero period subtorus. Its image in a
closed cusp tube is the previously computed logarithmic-period point.
The one prescribed endpoint on the entire norm circle therefore has
zero first base coordinate on every boundary point. The proof uses the
actual mapping-torus quotient and torus-coordinate surjectivity; no
endpoint support condition is assumed.
-/

noncomputable section

open Set Topology
open scoped ContinuousMap

namespace Wikipedia.HopfProblem.CuspBoundaryTopVanishing

open ToricSpace CuspUniformization CuspRetraction CuspControlledRetraction CuspCollapse
open SpecialPeriods.CuspFamily ThreefoldOverlapMappingTorus.Cusp ThreefoldHomologyCuspFibre
open CuspCentralHomology PeriodTorusHigherHomology CuspBoundaryTopVanishingCircle

/-- The actual restricted boundary representative is the original period-cover point. -/
theorem gammaBoundaryToClosed_realCoordinates
    (D : Data) (h : Height D.radius) (η : ℝ)
    (hη : ‖heightParameter D h‖ ≤ η) (hηr : η < D.radius)
    (t : ℝ) (x : Fin 3 → ℝ) :
    gammaBoundaryToClosed D h η hη
        (MappingTorus.mk CuspBoundaryGammaZero.restrictedMonodromy
          (t, coordinateProjection 3 x)) =
      closedQuotientMap D.correction hηr
        (periodPointPunctured D η (logPoint D.radius D.radius_pos t h)
          ((logPoint_exponential_norm D h t).trans_le hη) (Fin.cons 0 x)).1 := by
  apply Subtype.ext
  rw [gammaBoundaryToClosed_coe, periodPointPunctured_quotient]
  exact gammaBoundaryToFull_realCoordinates D h t x

/-- The single whole-circle endpoint evaluates on all real boundary representatives. -/
theorem retraction_gammaBoundaryToClosed_realCoordinates
    (D : Data) (h : Height D.radius) (η : ℝ)
    (hη : ‖heightParameter D h‖ ≤ η) (hηr : η < D.radius)
    (R : C(ClosedQuotient D.correction D.radius η,
      QuotientCentralFibre D.correction D.radius))
    (hEnd : HasPrescribedCircleEndpoint D.correction D.radius D.radius_pos η
      ‖heightParameter D h‖ R)
    (t : ℝ) (x : Fin 3 → ℝ) :
    R (gammaBoundaryToClosed D h η hη
        (MappingTorus.mk CuspBoundaryGammaZero.restrictedMonodromy
          (t, coordinateProjection 3 x))) =
      centralProject D.correction D.radius D.radius_pos
        (straightenedPrescribedCollapse D.correction η
          (periodPointPunctured D η (logPoint D.radius D.radius_pos t h)
            ((logPoint_exponential_norm D h t).trans_le hη) (Fin.cons 0 x))) := by
  rw [gammaBoundaryToClosed_realCoordinates D h η hη hηr]
  apply hEnd hηr
  rw [periodPointPunctured_coe, time_totalExponentialPoint]
  exact logPoint_exponential_norm D h t

/-- The geometrically computed joint period identity forces the entire collapsed
gamma-zero mapping torus to lie over the literal zero-first-coordinate circle. -/
theorem retraction_gammaBoundary_base_zero
    (D : Data) (δ : ℝ)
    (hbase : ∀ (η : ℝ) (s : LogBase D.radius), ‖exponential (s : ℂ)‖ < δ →
      ∀ (hη : ‖exponential (s : ℂ)‖ ≤ η) (x : RealPlane₄),
        baseTorusProjection D.correction D.radius D.radius_pos
          (centralProject D.correction D.radius D.radius_pos
            (straightenedPrescribedCollapse D.correction η
              (periodPointPunctured D η s hη x))) =
          coordinateProjection 2 ![x 0, x 1])
    (h : Height D.radius) (η : ℝ)
    (hη : ‖heightParameter D h‖ ≤ η) (hηr : η < D.radius)
    (hδ : ‖heightParameter D h‖ < δ)
    (R : C(ClosedQuotient D.correction D.radius η,
      QuotientCentralFibre D.correction D.radius))
    (hEnd : HasPrescribedCircleEndpoint D.correction D.radius D.radius_pos η
      ‖heightParameter D h‖ R)
    (q : CuspBoundaryGammaZero.Boundary) :
    baseTorusProjection D.correction D.radius D.radius_pos
      (R (gammaBoundaryToClosed D h η hη q)) 0 = 0 := by
  obtain ⟨⟨t, y⟩, rfl⟩ :=
    MappingTorus.mk_surjective CuspBoundaryGammaZero.restrictedMonodromy q
  obtain ⟨x, rfl⟩ := coordinateProjection_surjective 3 y
  rw [retraction_gammaBoundaryToClosed_realCoordinates D h η hη hηr R hEnd]
  have hb := hbase η (logPoint D.radius D.radius_pos t h)
    ((logPoint_exponential_norm D h t).trans_lt hδ)
    ((logPoint_exponential_norm D h t).trans_le hη) (Fin.cons 0 x)
  simpa using congrFun hb (0 : Fin 2)

end Wikipedia.HopfProblem.CuspBoundaryTopVanishing
