import Wikipedia.HopfProblem.SpecialPeriodsTriangleQuotientEllipticNeighborhoods
import Wikipedia.HopfProblem.EllipticEquivariantFillings
import Wikipedia.HopfProblem.SpecialPeriodsConstruction

/-!
# Elliptic fillings from the actual global period map

The local periods are the exact restriction of a supplied global period
map through the inverse of the actual elliptic neighborhood chart.  Its
two global generator equations imply the required local rotation law.
The resulting filling is the finite orbit quotient of this restricted
period family, with the complex atlas selected from those same periods.
-/

noncomputable section

open Set UpperHalfPlane
open scoped Topology ContDiff Manifold OnePoint Matrix

namespace Wikipedia.HopfProblem.SpecialPeriods.EllipticFilling

attribute [local instance] triangleGeometricAction

/-- The inverse actual elliptic chart intertwines rotation with the
generator of the actual stabilizer. -/
theorem ellipticNeighborhoodChart_symm_generator (j : Elliptic.Kind) (z : Disc) :
    letI := Triangle.ellipticNeighborhoodAction j
    (Triangle.ellipticNeighborhoodChart j).symm (Elliptic.familyRotation j z) =
      Triangle.ellipticStabilizerGenerator j • (Triangle.ellipticNeighborhoodChart j).symm z := by
  let := Triangle.ellipticNeighborhoodAction j
  apply (Triangle.ellipticNeighborhoodChart j).injective
  change Triangle.ellipticNeighborhoodChart j
      ((Triangle.ellipticNeighborhoodChart j).symm (Elliptic.familyRotation j z)) =
    Triangle.ellipticNeighborhoodChart j
      (Triangle.ellipticStabilizerGenerator j • (Triangle.ellipticNeighborhoodChart j).symm z)
  rw [Diffeomorph.apply_symm_apply, Triangle.ellipticNeighborhoodChart_generator,
    Diffeomorph.apply_symm_apply]

/-- The same inverse-chart covariance in the native upper half-plane. -/
theorem ellipticNeighborhoodChart_symm_generatorSL (j : Elliptic.Kind) (z : Disc) :
    ((Triangle.ellipticNeighborhoodChart j).symm (Elliptic.familyRotation j z) : ℍ) =
      Triangle.ellipticGeneratorSL j • ((Triangle.ellipticNeighborhoodChart j).symm z : ℍ) := by
  let := Triangle.ellipticNeighborhoodAction j
  have h := congrArg (Subtype.val : Triangle.ellipticNeighborhood j → ℍ)
    (ellipticNeighborhoodChart_symm_generator j z)
  simpa only [Triangle.ellipticNeighborhood_smul_val,
    Triangle.ellipticStabilizerGenerator_val, Triangle.ellipticGenerator_smul] using h

/-- The actual full-disc lift into the global period-map source. -/
def neighborhoodLift (j : Elliptic.Kind) (z : Disc) : ℍ :=
  ((Triangle.ellipticNeighborhoodChart j).symm z : ℍ)

@[simp] theorem neighborhoodLift_def (j : Elliptic.Kind) (z : Disc) :
    neighborhoodLift j z = ((Triangle.ellipticNeighborhoodChart j).symm z : ℍ) := rfl

theorem neighborhoodLift_holomorphic (j : Elliptic.Kind) :
    ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω (neighborhoodLift j) :=
  contMDiff_subtype_val.comp (Triangle.ellipticNeighborhoodChart j).symm.contMDiff

@[simp] theorem neighborhoodLift_zero (j : Elliptic.Kind) :
    neighborhoodLift j discZero = Triangle.ellipticCenter j := by
  change ((Triangle.ellipticNeighborhoodChart j).symm discZero : ℍ) = _
  rw [← Triangle.ellipticNeighborhoodChart_center j, Diffeomorph.symm_apply_apply]
  rfl

theorem neighborhoodLift_rotation (j : Elliptic.Kind) (z : Disc) :
    neighborhoodLift j (Elliptic.familyRotation j z) =
      Triangle.ellipticGeneratorSL j • neighborhoodLift j z :=
  ellipticNeighborhoodChart_symm_generatorSL j z

variable (P : HolomorphicPeriodMap ℂ ℍ)

/-- Exact restriction of the global holomorphic period map, with no
separately supplied local family. -/
def localPeriods (j : Elliptic.Kind) : HolomorphicPeriodMap ℂ Disc where
  point z := P.point (neighborhoodLift j z)
  holomorphic_tau := P.holomorphic_tau.comp (neighborhoodLift_holomorphic j)
  holomorphic_mu := P.holomorphic_mu.comp (neighborhoodLift_holomorphic j)
  holomorphic_beta := P.holomorphic_beta.comp (neighborhoodLift_holomorphic j)

@[simp] theorem localPeriods_point (j : Elliptic.Kind) (z : Disc) :
    (localPeriods P j).point z = P.point (neighborhoodLift j z) := rfl

@[simp] theorem localPeriods_point_zero (j : Elliptic.Kind) :
    (localPeriods P j).point discZero = P.point (Triangle.ellipticCenter j) := by
  rw [localPeriods_point, neighborhoodLift_zero]

variable
  (h₁ : ∀ z : ℍ, P.point (Triangle.generatorOneSL • z) = (P.point z).step₁)
  (h₂ : ∀ z : ℍ, P.point (Triangle.generatorTwoSL • z) = (P.point z).step₂)

include h₁ h₂ in
/-- The local rotation law follows from the actual global generator laws. -/
theorem localPeriods_covariance (j : Elliptic.Kind) (z : Disc) :
    (localPeriods P j).point (Elliptic.familyRotation j z) =
      Elliptic.periodStep j ((localPeriods P j).point z) := by
  simp only [localPeriods_point, neighborhoodLift_rotation]
  cases j
  · exact h₁ _
  · exact h₂ _

/-- The actual restricted period family satisfies the elliptic input data. -/
def localData (j : Elliptic.Kind) : Elliptic.Equivariant.Data j where
  periods := localPeriods P j
  covariance := localPeriods_covariance P h₁ h₂ j

@[simp] theorem localData_periods (j : Elliptic.Kind) :
    (localData P h₁ h₂ j).periods = localPeriods P j := rfl

@[simp] theorem localData_point (j : Elliptic.Kind) (z : Disc) :
    (localData P h₁ h₂ j).periods.point z = P.point (neighborhoodLift j z) := rfl

/-- Its central fixed period is the actual global period at the elliptic point. -/
@[simp] theorem localData_centralPeriod_val (j : Elliptic.Kind) :
    (localData P h₁ h₂ j).centralPeriod.val = P.point (Triangle.ellipticCenter j) :=
  localPeriods_point_zero P j

/-- The full filling for the prescribed main admissible affine twist. -/
abbrev fillingSpace (j : Elliptic.Kind) :=
  (localData P h₁ h₂ j).Space j.twist (Elliptic.mainTwist_admissible j)

/-- The actual finite-orbit projection from the restricted period family. -/
def fillingQuotient (j : Elliptic.Kind) :
    (localPeriods P j).TotalSpace → fillingSpace P h₁ h₂ j :=
  (localData P h₁ h₂ j).quotient j.twist (Elliptic.mainTwist_admissible j)

/-- The actual descended power map, including its central fibre. -/
def fillingProjection (j : Elliptic.Kind) : fillingSpace P h₁ h₂ j → Disc :=
  (localData P h₁ h₂ j).projection j.twist (Elliptic.mainTwist_admissible j)

@[simp] theorem fillingProjection_quotient (j : Elliptic.Kind)
    (x : (localPeriods P j).TotalSpace) :
    fillingProjection P h₁ h₂ j (fillingQuotient P h₁ h₂ j x) =
      Elliptic.discPower j.order j.order_pos x.1 := rfl

/-- The selected quotient atlas comes from the actual restricted periods. -/
@[instance_reducible] def fillingChartedSpace (j : Elliptic.Kind) :
    ChartedSpace Elliptic.FamilyModel (fillingSpace P h₁ h₂ j) :=
  (localData P h₁ h₂ j).chartedSpace j.twist (Elliptic.mainTwist_admissible j)

theorem filling_isManifold (j : Elliptic.Kind) :
    letI := fillingChartedSpace P h₁ h₂ j
    IsManifold (modelWithCornersSelf ℂ Elliptic.FamilyModel) ω (fillingSpace P h₁ h₂ j) :=
  (localData P h₁ h₂ j).isManifold j.twist (Elliptic.mainTwist_admissible j)

theorem fillingQuotient_isCoveringMap (j : Elliptic.Kind) :
    IsCoveringMap (fillingQuotient P h₁ h₂ j) :=
  (localData P h₁ h₂ j).quotient_isCoveringMap j.twist (Elliptic.mainTwist_admissible j)

theorem fillingQuotient_surjective (j : Elliptic.Kind) :
    Function.Surjective (fillingQuotient P h₁ h₂ j) :=
  (localData P h₁ h₂ j).quotient_surjective j.twist (Elliptic.mainTwist_admissible j)

theorem fillingQuotient_holomorphic (j : Elliptic.Kind) :
    letI := (localPeriods P j).totalChartedSpace
    letI := fillingChartedSpace P h₁ h₂ j
    ContMDiff (modelWithCornersSelf ℂ Elliptic.FamilyModel)
      (modelWithCornersSelf ℂ Elliptic.FamilyModel) ω (fillingQuotient P h₁ h₂ j) :=
  (localData P h₁ h₂ j).quotient_holomorphic j.twist (Elliptic.mainTwist_admissible j)

theorem fillingProjection_proper (j : Elliptic.Kind) :
    IsProperMap (fillingProjection P h₁ h₂ j) :=
  (localData P h₁ h₂ j).projection_proper j.twist (Elliptic.mainTwist_admissible j)

theorem fillingProjection_surjective (j : Elliptic.Kind) :
    Function.Surjective (fillingProjection P h₁ h₂ j) :=
  (localData P h₁ h₂ j).projection_surjective j.twist (Elliptic.mainTwist_admissible j)

theorem fillingProjection_continuous (j : Elliptic.Kind) :
    Continuous (fillingProjection P h₁ h₂ j) :=
  (localData P h₁ h₂ j).projection_continuous j.twist (Elliptic.mainTwist_admissible j)

theorem fillingProjection_holomorphic (j : Elliptic.Kind) :
    letI := fillingChartedSpace P h₁ h₂ j
    ContMDiff (modelWithCornersSelf ℂ Elliptic.FamilyModel) 𝓘(ℂ) ω
      (fillingProjection P h₁ h₂ j) :=
  (localData P h₁ h₂ j).projection_holomorphic j.twist (Elliptic.mainTwist_admissible j)

theorem fillingProjection_fibre_compact (j : Elliptic.Kind) (b : Disc) :
    IsCompact (fillingProjection P h₁ h₂ j ⁻¹' {b}) :=
  (localData P h₁ h₂ j).projection_fibre_compact j.twist (Elliptic.mainTwist_admissible j) b

theorem fillingProjection_central_fibre (j : Elliptic.Kind) :
    fillingProjection P h₁ h₂ j ⁻¹' {Elliptic.discZero} =
      fillingQuotient P h₁ h₂ j ''
        {x : (localPeriods P j).TotalSpace | x.1 = Elliptic.discZero} :=
  (localData P h₁ h₂ j).projection_central_fibre j.twist (Elliptic.mainTwist_admissible j)

section Sphere

attribute [local instance] triangleCompactifiedChartedSpace

variable (π : Diffeomorph 𝓘(ℂ) 𝓘(ℂ)
  TriangleCompactifiedOrbitSpace RiemannSphere ω)
  (hπ : π triangleCuspPoint = (∞ : RiemannSphere))
  (h₀ : π (triangleOpenInclusion triangleOrbitCenterOne) = ((0 : ℂ) : RiemannSphere))
  (h₁ : π (triangleOpenInclusion triangleOrbitCenterTwo) = ((1 : ℂ) : RiemannSphere))

/-- Specialization to the global period map constructed from the actual
normalized sphere equivalence; no local period or covariance is an input. -/
def localDataOfSphere (j : Elliptic.Kind) : Elliptic.Equivariant.Data j :=
  localData (Construction.periodMapOfSphere π hπ h₀ h₁)
    (Construction.periodMapOfSphere_generator₁ π hπ h₀ h₁)
    (Construction.periodMapOfSphere_generator₂ π hπ h₀ h₁) j

@[simp] theorem localDataOfSphere_point (j : Elliptic.Kind) (z : Disc) :
    (localDataOfSphere π hπ h₀ h₁ j).periods.point z =
      (Construction.periodMapOfSphere π hπ h₀ h₁).point (neighborhoodLift j z) := rfl

end Sphere

end Wikipedia.HopfProblem.SpecialPeriods.EllipticFilling
