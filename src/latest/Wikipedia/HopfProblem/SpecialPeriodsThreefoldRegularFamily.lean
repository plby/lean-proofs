import Wikipedia.HopfProblem.SpecialPeriodsThreefoldRegular
import Wikipedia.HopfProblem.SpecialPeriodsConstruction
import Wikipedia.HopfProblem.TrianglePeriodFamilyGeometry

/-!
# The actual torus family over the regular compactified-base patch

The total space and its analytic atlas are those of the constructed diagonal
quotient period family.  Only its base is identified with the actual open
regular patch of the compactified triangle quotient.  Properness, surjectivity,
holomorphicity, and the zero section are preserved by this biholomorphism.

The final construction supplies the actual global period map obtained from a
normalized sphere biholomorphism, rather than assuming period functions or
their generator equations.
-/

noncomputable section

open Function Set Topology UpperHalfPlane
open scoped ContDiff Manifold OnePoint

namespace Wikipedia.HopfProblem.SpecialPeriods.Threefold

attribute [local instance] triangleRegularQuotientChartedSpace
  triangleOrbitChartedSpace triangleCompactifiedChartedSpace

variable (P : HolomorphicPeriodMap ℂ ℍ)
  (h₁ : ∀ z : ℍ, P.point (Triangle.generatorOneSL • z) = (P.point z).step₁)
  (h₂ : ∀ z : ℍ, P.point (Triangle.generatorTwoSL • z) = (P.point z).step₂)

/-- The actual diagonal-quotient family data, with all regular-covering
hypotheses already discharged by the triangle action. -/
abbrev regularFamilyData : TrianglePeriodFamily.Data ℂ TriangleRegularPoint :=
  TrianglePeriodFamily.regularData P h₁ h₂

/-- The total space is the original quotient space, without a transported
or replaced complex structure. -/
abbrev RegularFamily : Type := (regularFamilyData P h₁ h₂).Space

/-- The original analytic quotient atlas on the regular family. -/
@[instance_reducible] def regularFamilyChartedSpace :
    ChartedSpace (ℂ × ComplexPlane₂) (RegularFamily P h₁ h₂) :=
  (regularFamilyData P h₁ h₂).chartedSpace (TrianglePeriodFamily.regularCovering P h₁ h₂)

theorem regularFamily_t2Space : T2Space (RegularFamily P h₁ h₂) :=
  (regularFamilyData P h₁ h₂).spaceT2Space_of_properlyDiscontinuous
    (TrianglePeriodFamily.regularCovering P h₁ h₂)

theorem regularFamily_secondCountable : SecondCountableTopology (RegularFamily P h₁ h₂) :=
  (regularFamilyData P h₁ h₂).spaceSecondCountable
    (TrianglePeriodFamily.regularCovering P h₁ h₂)

theorem regularFamily_isManifold :
    letI := regularFamilyChartedSpace P h₁ h₂
    IsManifold (modelWithCornersSelf ℂ (ℂ × ComplexPlane₂)) ω (RegularFamily P h₁ h₂) :=
  (regularFamilyData P h₁ h₂).isManifold (TrianglePeriodFamily.regularCovering P h₁ h₂)

/-- The actual family projection to the regular open patch. -/
def regularFamilyProjection : RegularFamily P h₁ h₂ → regularPatch :=
  regularBiholomorph ∘ (regularFamilyData P h₁ h₂).projection

theorem regularFamilyProjection_proper : IsProperMap (regularFamilyProjection P h₁ h₂) :=
  regularBiholomorph.toHomeomorph.isProperMap.comp
    ((regularFamilyData P h₁ h₂).projection_proper
      (TrianglePeriodFamily.regularCovering P h₁ h₂))

theorem regularFamilyProjection_surjective : Surjective (regularFamilyProjection P h₁ h₂) :=
  regularBiholomorph.surjective.comp (regularFamilyData P h₁ h₂).projection_surjective

theorem regularFamilyProjection_continuous : Continuous (regularFamilyProjection P h₁ h₂) :=
  regularBiholomorph.continuous.comp (regularFamilyData P h₁ h₂).projection_continuous

theorem regularFamilyProjection_holomorphic :
    letI := regularFamilyChartedSpace P h₁ h₂
    ContMDiff (modelWithCornersSelf ℂ (ℂ × ComplexPlane₂)) 𝓘(ℂ) ω
      (regularFamilyProjection P h₁ h₂) := by
  let := regularFamilyChartedSpace P h₁ h₂
  exact regularBiholomorph.contMDiff.comp
    ((regularFamilyData P h₁ h₂).projection_holomorphic
      (TrianglePeriodFamily.regularCovering P h₁ h₂))

/-- The same actual projection, now with values in the compactified base. -/
def regularFamilyProjectionToBase : RegularFamily P h₁ h₂ → TriangleCompactifiedOrbitSpace :=
  fun x => (regularFamilyProjection P h₁ h₂ x : TriangleCompactifiedOrbitSpace)

theorem regularFamilyProjectionToBase_holomorphic :
    letI := regularFamilyChartedSpace P h₁ h₂
    ContMDiff (modelWithCornersSelf ℂ (ℂ × ComplexPlane₂)) 𝓘(ℂ) ω
      (regularFamilyProjectionToBase P h₁ h₂) := by
  let := regularFamilyChartedSpace P h₁ h₂
  exact (contMDiff_subtype_val (U := regularPatch)).comp
    (regularFamilyProjection_holomorphic P h₁ h₂)

@[simp] theorem regularFamilyProjectionToBase_quotient
    (x : (regularFamilyData P h₁ h₂).TotalSpace) :
    regularFamilyProjectionToBase P h₁ h₂ ((regularFamilyData P h₁ h₂).quotient x) =
      triangleCompactifiedProjection x.1.val := by
  change (regularBiholomorph (triangleRegularProject x.1) :
    TriangleCompactifiedOrbitSpace) = _
  exact regularBiholomorph_project x.1

theorem range_regularFamilyProjectionToBase :
    range (regularFamilyProjectionToBase P h₁ h₂) = (regularPatch : Set _) := by
  ext x
  constructor
  · rintro ⟨y, rfl⟩
    exact (regularFamilyProjection P h₁ h₂ y).property
  · intro hx
    obtain ⟨y, hy⟩ := regularFamilyProjection_surjective P h₁ h₂ ⟨x, hx⟩
    exact ⟨y, congrArg Subtype.val hy⟩

/-- The actual descended zero section, with its input re-expressed in the
native regular patch. -/
def regularFamilyZeroSection : regularPatch → RegularFamily P h₁ h₂ :=
  (regularFamilyData P h₁ h₂).zeroSection ∘ regularBiholomorph.symm

@[simp] theorem regularFamilyProjection_zeroSection (x : regularPatch) :
    regularFamilyProjection P h₁ h₂ (regularFamilyZeroSection P h₁ h₂ x) = x := by
  change regularBiholomorph
    ((regularFamilyData P h₁ h₂).projection
      ((regularFamilyData P h₁ h₂).zeroSection (regularBiholomorph.symm x))) = x
  exact (congrArg regularBiholomorph
    ((regularFamilyData P h₁ h₂).projection_zeroSection (regularBiholomorph.symm x))).trans
      (regularBiholomorph.apply_symm_apply x)

theorem regularFamilyZeroSection_leftInverse :
    LeftInverse (regularFamilyProjection P h₁ h₂) (regularFamilyZeroSection P h₁ h₂) :=
  regularFamilyProjection_zeroSection P h₁ h₂

theorem regularFamilyZeroSection_continuous : Continuous (regularFamilyZeroSection P h₁ h₂) :=
  (regularFamilyData P h₁ h₂).zeroSection_continuous.comp
    regularBiholomorph.symm.continuous

theorem regularFamilyZeroSection_holomorphic :
    letI := regularFamilyChartedSpace P h₁ h₂
    ContMDiff 𝓘(ℂ) (modelWithCornersSelf ℂ (ℂ × ComplexPlane₂)) ω
      (regularFamilyZeroSection P h₁ h₂) := by
  let := regularFamilyChartedSpace P h₁ h₂
  have hzero : ContMDiff 𝓘(ℂ) (modelWithCornersSelf ℂ (ℂ × ComplexPlane₂)) ω
      (fun x : TriangleRegularQuotient => (regularFamilyData P h₁ h₂).zeroSection x) :=
    (regularFamilyData P h₁ h₂).zeroSection_holomorphic
      (TrianglePeriodFamily.regularCovering P h₁ h₂)
  exact hzero.comp regularBiholomorph.symm.contMDiff

theorem regularFamilyZeroSection_isClosedEmbedding :
    IsClosedEmbedding (regularFamilyZeroSection P h₁ h₂) := by
  let := regularFamily_t2Space P h₁ h₂
  exact (regularFamilyData P h₁ h₂).zeroSection_isClosedEmbedding.comp
    regularBiholomorph.symm.toHomeomorph.isClosedEmbedding

section Sphere

variable (π : Diffeomorph 𝓘(ℂ) 𝓘(ℂ) TriangleCompactifiedOrbitSpace RiemannSphere ω)
  (hπ : π triangleCuspPoint = (∞ : RiemannSphere))
  (h₀ : π (triangleOpenInclusion triangleOrbitCenterOne) = ((0 : ℂ) : RiemannSphere))
  (h₁ : π (triangleOpenInclusion triangleOrbitCenterTwo) = ((1 : ℂ) : RiemannSphere))

/-- Actual regular-family data from the constructed admissible periods of a
normalized quotient sphere biholomorphism.  No period laws remain as inputs. -/
abbrev regularFamilyDataOfSphere : TrianglePeriodFamily.Data ℂ TriangleRegularPoint :=
  regularFamilyData (Construction.periodMapOfSphere π hπ h₀ h₁)
    (Construction.periodMapOfSphere_generator₁ π hπ h₀ h₁)
    (Construction.periodMapOfSphere_generator₂ π hπ h₀ h₁)

abbrev RegularFamilyOfSphere : Type := (regularFamilyDataOfSphere π hπ h₀ h₁).Space

/-- The native quotient atlas of the constructed sphere-input regular family. -/
@[instance_reducible] def regularFamilyOfSphereChartedSpace :
    ChartedSpace (ℂ × ComplexPlane₂) (RegularFamilyOfSphere π hπ h₀ h₁) :=
  regularFamilyChartedSpace (Construction.periodMapOfSphere π hπ h₀ h₁)
    (Construction.periodMapOfSphere_generator₁ π hπ h₀ h₁)
    (Construction.periodMapOfSphere_generator₂ π hπ h₀ h₁)

/-- The actual sphere-input family's projection to the regular patch. -/
def regularFamilyProjectionOfSphere : RegularFamilyOfSphere π hπ h₀ h₁ → regularPatch :=
  regularFamilyProjection (Construction.periodMapOfSphere π hπ h₀ h₁)
    (Construction.periodMapOfSphere_generator₁ π hπ h₀ h₁)
    (Construction.periodMapOfSphere_generator₂ π hπ h₀ h₁)

/-- Its actual zero section. -/
def regularFamilyZeroSectionOfSphere : regularPatch → RegularFamilyOfSphere π hπ h₀ h₁ :=
  regularFamilyZeroSection (Construction.periodMapOfSphere π hπ h₀ h₁)
    (Construction.periodMapOfSphere_generator₁ π hπ h₀ h₁)
    (Construction.periodMapOfSphere_generator₂ π hπ h₀ h₁)

/-- The actual constructed regular family is a Hausdorff second-countable
complex threefold, proper and surjective over the native regular patch, with
its holomorphic zero section.  All period and generator data have been supplied
by the global analytic construction. -/
theorem regularFamilyOfSphere_construction :
    letI := regularFamilyOfSphereChartedSpace π hπ h₀ h₁
    T2Space (RegularFamilyOfSphere π hπ h₀ h₁) ∧
      SecondCountableTopology (RegularFamilyOfSphere π hπ h₀ h₁) ∧
      IsManifold (modelWithCornersSelf ℂ (ℂ × ComplexPlane₂)) ω
        (RegularFamilyOfSphere π hπ h₀ h₁) ∧
      IsProperMap (regularFamilyProjectionOfSphere π hπ h₀ h₁) ∧
      Surjective (regularFamilyProjectionOfSphere π hπ h₀ h₁) ∧
      ContMDiff (modelWithCornersSelf ℂ (ℂ × ComplexPlane₂)) 𝓘(ℂ) ω
        (regularFamilyProjectionOfSphere π hπ h₀ h₁) ∧
      ContMDiff 𝓘(ℂ) (modelWithCornersSelf ℂ (ℂ × ComplexPlane₂)) ω
        (regularFamilyZeroSectionOfSphere π hπ h₀ h₁) ∧
      LeftInverse (regularFamilyProjectionOfSphere π hπ h₀ h₁)
        (regularFamilyZeroSectionOfSphere π hπ h₀ h₁) := by
  let P := Construction.periodMapOfSphere π hπ h₀ h₁
  let hgen₁ := Construction.periodMapOfSphere_generator₁ π hπ h₀ h₁
  let hgen₂ := Construction.periodMapOfSphere_generator₂ π hπ h₀ h₁
  exact ⟨regularFamily_t2Space P hgen₁ hgen₂,
    regularFamily_secondCountable P hgen₁ hgen₂,
    regularFamily_isManifold P hgen₁ hgen₂,
    regularFamilyProjection_proper P hgen₁ hgen₂,
    regularFamilyProjection_surjective P hgen₁ hgen₂,
    regularFamilyProjection_holomorphic P hgen₁ hgen₂,
    regularFamilyZeroSection_holomorphic P hgen₁ hgen₂,
    regularFamilyZeroSection_leftInverse P hgen₁ hgen₂⟩

end Sphere

end Wikipedia.HopfProblem.SpecialPeriods.Threefold
