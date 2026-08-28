import Wikipedia.HopfProblem.TrianglePeriodFamilyBoundaryFibreTransport
import Wikipedia.HopfProblem.TrianglePeriodFamilyBoundaryCuspNative
import Wikipedia.HopfProblem.TrianglePeriodFamilyBoundaryEllipticGaugeLinearizationNative

/-!
# A common actual fibre map for the three original boundaries

The cusp boundary has its literal unchanged time-zero fibre.  For each
elliptic boundary, the proved whole-boundary gauge homotopy has zero linear
translation at time zero.  Genuine paths in the regular covering base then
identify all three original fibre maps with the same normalized marked
fibre inclusion, in every singular homology degree.
-/

noncomputable section

namespace Wikipedia.HopfProblem.TrianglePeriodFamily.Boundary

open Elliptic SpecialPeriods SpecialPeriods.Triangle
open ThreefoldOverlapMappingTorus SingularMayerVietoris PeriodTorusHigherHomology
open MappingTorusHomology Homology EllipticGaugeLinearization

local notation "Dsp" =>
  regularData specialPeriodMap specialPeriodMap_generator₁ specialPeriodMap_generator₂

/-- The original cusp fibre is literally the unchanged torus over its actual base point. -/
theorem fibreToRegularFamily_cusp_eq_point :
    fibreToRegularFamily none =
      pointFamilyFibreInclusion Dsp
        (Cusp.baseLift ThreefoldOverlapMappingTorus.Cusp.specialHeight 0) := by
  apply ContinuousMap.ext
  intro x
  exact Cusp.boundaryToRegularFamily_mk 0 x

/-- At time zero the proved linearized elliptic gauge is exactly zero. -/
theorem linearRegularBoundaryMap_fibre_eq_point (j : Kind) :
    (linearRegularBoundaryMap j 0).comp
        (MappingTorus.HomologyCover.fibreInclusion (flatTorusAffine j j.twist)) =
      pointFamilyFibreInclusion Dsp (nativeShiftedBase j 0 0) := by
  apply ContinuousMap.ext
  intro x
  change linearRegularBoundaryMap j 0
    (MappingTorus.mk (flatTorusAffine j j.twist) (0, x)) =
      (Dsp).quotient (nativeShiftedBase j 0 0, x)
  rw [linearRegularBoundaryMap_mk]
  simp only [zero_div, zero_smul, map_zero, add_zero]

/-- Restricting the genuine full boundary homotopy identifies the original elliptic fibre.
The time-dependent gauge was linearized before this time-zero restriction. -/
theorem fibreToRegularFamily_elliptic_homotopic_point (j : Kind) :
    (fibreToRegularFamily (some j)).Homotopic
      (pointFamilyFibreInclusion Dsp (nativeShiftedBase j 0 0)) := by
  obtain ⟨H⟩ := boundaryToRegularFamily_homotopic_linear j 0
  exact ⟨(H.comp (ContinuousMap.Homotopy.refl
    (MappingTorus.HomologyCover.fibreInclusion (flatTorusAffine j j.twist)))).cast
      rfl (linearRegularBoundaryMap_fibre_eq_point j)⟩

/-- All three literal original fibre maps induce the same normalized marked map in every degree. -/
theorem fibreToRegularFamily_homology_common (i : SpecialPeriods.Threefold.Puncture) (n : ℕ) :
    singularHomologyMap (fibreToRegularFamily i) n =
      singularHomologyMap (familyFibreInclusion Dsp normalizedSlitBaseLift) n := by
  cases i with
  | none =>
      rw [fibreToRegularFamily_cusp_eq_point]
      exact pointFamilyFibreInclusion_homology_eq_normalized Dsp _ n
  | some j =>
      exact (homotopic_homologyMap (fibreToRegularFamily_elliptic_homotopic_point j) n).trans
        (pointFamilyFibreInclusion_homology_eq_normalized Dsp _ n)

/-- The original regular attachment coefficient on each actual Wang fibre is this same map. -/
theorem boundaryRegularHomologyMap_common_fibre (i : SpecialPeriods.Threefold.Puncture) (n : ℕ) :
    (boundaryRegularHomologyMap i n).comp (fibreHomologyMap (monodromy i) n) =
      singularHomologyMap (familyFibreInclusion Dsp normalizedSlitBaseLift) n :=
  (ThreefoldOverlapMappingTorus.boundaryRegularHomologyMap_fibre i n).trans
    (fibreToRegularFamily_homology_common i n)

/-- The equality retains the actual positive fibre class, without a change of marking or sign. -/
theorem boundaryRegularHomologyMap_common_fibre_apply
    (i : SpecialPeriods.Threefold.Puncture) (n : ℕ) (a : SingularHomology RealTorus₄ n) :
    boundaryRegularHomologyMap i n (fibreHomologyMap (monodromy i) n a) =
      singularHomologyMap (familyFibreInclusion Dsp normalizedSlitBaseLift) n a :=
  LinearMap.congr_fun (boundaryRegularHomologyMap_common_fibre i n) a

end Wikipedia.HopfProblem.TrianglePeriodFamily.Boundary
