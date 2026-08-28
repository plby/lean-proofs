import Wikipedia.HopfProblem.SpecialPeriodsThreefoldAutomorphismsRigiditySequence
import Wikipedia.HopfProblem.HolomorphicAutomorphismTangentDetector

/-!
# The native-field obstruction to normalized automorphisms

The actual normalized displacement limits glue to a holomorphic section
of the original tangent bundle. Their preserved scalar detector
annihilates this field, whereas the same detector evaluates to one on
the genuine vertical generator. The proved classification of all native
fields therefore makes every such coordinate limit zero.
-/

noncomputable section

open Set Filter Topology
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.SpecialPeriods.Threefold.Automorphisms

open HolomorphicAutomorphism.Displacement
open HolomorphicAutomorphismTangentGluing HolomorphicAutomorphismTangentLimits

local notation "Model" => ℂ × ComplexPlane₂
local notation "IF" => modelWithCornersSelf ℂ Model

attribute [local instance] Threefold.chartedSpace Threefold.space_isManifold
  Threefold.space_compact Threefold.space_t2Space Threefold.space_secondCountable

/-- The actual outer coordinate domains cover the original threefold. -/
theorem rigidityAtlas_chartDomain_cover (x : Threefold.Space) :
    ∃ i : rigidityAtlas.Index,
      x ∈ chartDomain (rigidityAtlas.center i)
        (rigidityAtlas.outerCoordinates i : Set Model) := by
  obtain ⟨i, hi⟩ := rigidityAtlas.covered x
  exact ⟨i, rigidityAtlas.innerOpen_subset_outerOpen i hi⟩

/-- Every actual holomorphic coordinate limit of a normalized sequence
vanishes. Its native tangent-field compatibility is derived from the
original automorphisms, not imposed as a hypothesis. -/
theorem NormalizedSequence.coordinate_limits_eq_zero (S : NormalizedSequence)
    (h : rigidityAtlas.Index → Model → Model)
    (hd : ∀ i, DifferentiableOn ℂ (h i) (rigidityAtlas.outerCoordinates i))
    (hlim : ∀ i, TendstoLocallyUniformlyOn
      (fun n => normalized rigidityAtlas (S.maps n) i) (h i) atTop
      (rigidityAtlas.outerCoordinates i)) :
    ∀ i z, z ∈ rigidityAtlas.outerCoordinates i → h i z = 0 := by
  let cn : ℕ → ℂ := fun n => (delta rigidityAtlas (S.maps n) : ℂ)⁻¹
  have hlim' : ∀ i, TendstoLocallyUniformlyOn
      (normalizedCoordinate S.maps cn (rigidityAtlas.center i)) (h i) atTop
      (rigidityAtlas.outerCoordinates i) := hlim
  let v : Threefold.HolomorphicVectorFields.Field :=
    fieldOfNativeCoordinateLimits S.tends_one rigidityAtlas.center
      rigidityAtlas.outerCoordinates rigidityAtlas_chartDomain_cover h hd hlim'
  have hfix : ∀ᶠ n in atTop,
      detector (S.maps n normalizationPoint) = detector normalizationPoint :=
    Eventually.of_forall fun n => (S.detector_zero n).trans detector_point.symm
  have hvdet : mfderiv IF 𝓘(ℂ) detector normalizationPoint (v normalizationPoint) = 0 :=
    HolomorphicAutomorphismTangentDetector.fieldOfNativeCoordinateLimits_mfderiv_eq_zero
      S.tends_one rigidityAtlas.center rigidityAtlas.outerCoordinates
      rigidityAtlas_chartDomain_cover h hd hlim' detector_holomorphicAt hfix
  obtain ⟨c, hc⟩ :=
    Threefold.HolomorphicVectorFields.Classification.exists_eq_smul_generator v
  have hc0 : c = 0 := by
    rw [hc] at hvdet
    change mfderiv IF 𝓘(ℂ) detector normalizationPoint
      (c • VerticalAction.generator normalizationPoint) = 0 at hvdet
    rw [map_smul, detector_mfderiv_generator] at hvdet
    change c * (1 : ℂ) = 0 at hvdet
    simpa only [mul_one] using hvdet
  have hv0 : v = 0 := by rw [hc, hc0, zero_smul]
  have hne := fieldOfNativeCoordinateLimits_ne_zero_iff S.tends_one
    rigidityAtlas.center rigidityAtlas.outerCoordinates rigidityAtlas_chartDomain_cover
    h hd hlim' rigidityAtlas.outerCoordinates_subset_target
  intro i z hz
  by_contra hnz
  exact (hne.mpr ⟨i, z, hz, hnz⟩) hv0

end Wikipedia.HopfProblem.SpecialPeriods.Threefold.Automorphisms
