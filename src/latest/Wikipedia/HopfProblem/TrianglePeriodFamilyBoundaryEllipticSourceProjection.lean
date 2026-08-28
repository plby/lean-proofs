import Wikipedia.HopfProblem.TrianglePeriodFamilyBoundaryEllipticColumns

/-!
# Actual elliptic boundary coefficients in the source kernel

Naturality of the actual singular Mayer--Vietoris connecting maps is now
applied to the genuine slit-preserving boundary map.  The two actual
intersection columns and the proved orientation give the first and second
source-kernel coordinates respectively.  All analytic tails and native
gauge translations have been treated by the preceding geometric proofs;
no boundary matrix or fundamental-group label is assumed to identify a
homology map.
-/

noncomputable section

namespace Wikipedia.HopfProblem.TrianglePeriodFamily.Boundary

open SpecialPeriods SpecialPeriods.Triangle Elliptic Homology
open SpecialPeriods.Threefold.EllipticGeometry
open SingularMayerVietoris PeriodTorusHigherHomology
open TrianglePeriodFamilyHomologyAlgebra ThreefoldOverlapMappingTorus

local notation "Dsp" =>
  regularData specialPeriodMap specialPeriodMap_generator₁ specialPeriodMap_generator₂

/-- The proved normalization orientation gives this unconditional actual
change from slit coordinates to the two fixed source meridians. -/
theorem normalizedSourceDomainEquiv_nonpos (n : ℕ)
    (x : SingularHomology RealTorus₄ n × SingularHomology RealTorus₄ n) :
    normalizedSourceDomainEquiv n x =
      (x.1, -(generatorHomologyEquiv true n).symm x.2) := by
  rw [normalizedSourceDomainEquiv,
    if_neg (not_lt.mpr normalizationOrientation_nonpos), inverseSecondCoordinate_apply]

/-- The inverse source generator fixes the same actual Wang-boundary classes. -/
theorem ellipticWangBoundary_generator_inv_fixed (j : Kind) (v : Lattice) (n : ℕ)
    (a : SingularHomology (MappingTorus.Torus (flatTorusAffine j v)) (n + 1)) :
    triangleHomologyEquiv (ellipticGenerator j)⁻¹ n
        (MappingTorusHomology.wangBoundary (flatTorusAffine j v) n a) =
      MappingTorusHomology.wangBoundary (flatTorusAffine j v) n a := by
  rw [triangleHomologyEquiv_inv]
  apply (triangleHomologyEquiv (ellipticGenerator j) n).injective
  rw [LinearEquiv.apply_symm_apply, ellipticWangBoundary_generator_fixed]

/-- The literal original elliptic coefficient, before simplifying the
already geometrically identified component indices. -/
theorem ellipticBoundary_sourceKernelProjection_components (j : Kind) (n : ℕ)
    (a : SingularHomology (MappingTorus.Torus (flatTorusAffine j j.twist)) (n + 1)) :
    (sourceKernelProjection Dsp n (boundaryRegularHomologyMap (some j) (n + 1) a) :
      SingularHomology RealTorus₄ n × SingularHomology RealTorus₄ n) =
      normalizedSourceDomainEquiv n
        (-componentCoordinates (ellipticLowerColumnIndex j)
          (MappingTorusHomology.wangBoundary (flatTorusAffine j j.twist) n a) +
        componentCoordinates (ellipticUpperColumnIndex j)
          (MappingTorusHomology.wangBoundary (flatTorusAffine j j.twist) n a)).2 := by
  refine (congrArg
    (fun z : SingularHomology (Dsp).Space (n + 1) =>
      (sourceKernelProjection Dsp n z :
        SingularHomology RealTorus₄ n × SingularHomology RealTorus₄ n))
    (LinearMap.congr_fun (boundaryRegularHomologyMap_slit j (n + 1)) a)).trans ?_
  refine (sourceKernelProjection_wangBoundary Dsp (flatTorusAffine j j.twist)
    (ellipticSlitBoundaryMap j) (ellipticSlitBoundaryMap_upper j)
    (ellipticSlitBoundaryMap_lower j) n a).trans ?_
  rw [intersectionComparison_antidiagonal,
    intersectionComparison_lowerColumn, intersectionComparison_upperColumn]
  change normalizedSourceDomainEquiv n
    (-Homology.intersectionHomologyEquiv Dsp normalizedSlitBaseLift n
      (singularHomologyMap (ellipticLowerColumn j) n
        (MappingTorusHomology.wangBoundary (flatTorusAffine j j.twist) n a)) +
    Homology.intersectionHomologyEquiv Dsp normalizedSlitBaseLift n
      (singularHomologyMap (ellipticUpperColumn j) n
        (MappingTorusHomology.wangBoundary (flatTorusAffine j j.twist) n a))).2 = _
  rw [ellipticLowerColumn_wangBoundary, ellipticUpperColumn_wangBoundary]

/-- The actual elliptic attachment has precisely one nonzero source-kernel
coordinate, and that coordinate is its actual Wang connecting class. -/
theorem ellipticBoundary_sourceKernelProjection (j : Kind) (n : ℕ)
    (a : SingularHomology (MappingTorus.Torus (flatTorusAffine j j.twist)) (n + 1)) :
    (sourceKernelProjection Dsp n (boundaryRegularHomologyMap (some j) (n + 1) a) :
      SingularHomology RealTorus₄ n × SingularHomology RealTorus₄ n) =
      if attachingMeridianIndex j then
        (0, MappingTorusHomology.wangBoundary (flatTorusAffine j j.twist) n a)
      else (MappingTorusHomology.wangBoundary (flatTorusAffine j j.twist) n a, 0) := by
  rw [ellipticBoundary_sourceKernelProjection_components, normalizedSourceDomainEquiv_nonpos]
  cases j with
  | three =>
    simp [ellipticLowerColumnIndex, ellipticUpperColumnIndex, attachingMeridianIndex]
  | four =>
    have hw := ellipticWangBoundary_generator_inv_fixed .four Kind.four.twist n a
    rw [triangleHomologyEquiv_inv] at hw
    change (generatorHomologyEquiv true n).symm
      (MappingTorusHomology.wangBoundary (flatTorusAffine .four Kind.four.twist) n a) =
        MappingTorusHomology.wangBoundary (flatTorusAffine .four Kind.four.twist) n a at hw
    simpa [ellipticLowerColumnIndex, ellipticUpperColumnIndex, attachingMeridianIndex] using hw

/-- The order-three actual cap contributes its Wang class to the first source meridian. -/
theorem ellipticThreeBoundary_sourceKernelProjection (n : ℕ)
    (a : SingularHomology
      (MappingTorus.Torus (flatTorusAffine .three Kind.three.twist)) (n + 1)) :
    (sourceKernelProjection Dsp n
      (boundaryRegularHomologyMap (some Kind.three) (n + 1) a) :
      SingularHomology RealTorus₄ n × SingularHomology RealTorus₄ n) =
      (MappingTorusHomology.wangBoundary (flatTorusAffine .three Kind.three.twist) n a, 0) :=
  ellipticBoundary_sourceKernelProjection .three n a

/-- The order-four actual cap contributes its Wang class to the second source meridian. -/
theorem ellipticFourBoundary_sourceKernelProjection (n : ℕ)
    (a : SingularHomology
      (MappingTorus.Torus (flatTorusAffine .four Kind.four.twist)) (n + 1)) :
    (sourceKernelProjection Dsp n
      (boundaryRegularHomologyMap (some Kind.four) (n + 1) a) :
      SingularHomology RealTorus₄ n × SingularHomology RealTorus₄ n) =
      (0, MappingTorusHomology.wangBoundary (flatTorusAffine .four Kind.four.twist) n a) :=
  ellipticBoundary_sourceKernelProjection .four n a

end Wikipedia.HopfProblem.TrianglePeriodFamily.Boundary
