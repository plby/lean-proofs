import Wikipedia.HopfProblem.SpecialPeriodsThreefoldHolomorphicVectorFieldsClassificationRegular
import Wikipedia.HopfProblem.SpecialPeriodsThreefoldHolomorphicFormsDetectionDensity
import Wikipedia.HopfProblem.SpecialPeriodsThreefoldVerticalActionGenerator

/-!
# Native fields are detected by the actual regular vector cover

The cover has a genuine invertible differential and its image is the
proved dense regular locus. Equality of its native lifted coefficients
therefore detects equality of the original holomorphic tangent sections.
The constructed flow generator has precisely the original constant e₂
coefficient, with no change of normalization.
-/

noncomputable section

open Set Topology Bundle
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.SpecialPeriods.Threefold.HolomorphicVectorFields.Classification

open HolomorphicForms.RegularCover

local notation "IF" => modelWithCornersSelf ℂ (ℂ × ComplexPlane₂)

attribute [local instance] Threefold.chartedSpace Threefold.space_isManifold
  Threefold.space_t2Space HolomorphicForms.RegularCover.coverChartedSpace
  HolomorphicForms.RegularCover.cover_isManifold

/-- Density is used in the original tangent-bundle topology. -/
theorem field_eq_of_regular (v w : Threefold.HolomorphicVectorFields.Field)
    (h : ∀ y ∈ Threefold.regularLocus, v y = w y) : v = w := by
  apply ContMDiffSection.ext
  intro y
  have hfreq := (mem_closure_iff_frequently.mp (Threefold.regularLocus_dense y)).mono
    (fun x hx => show
      Wikipedia.HopfProblem.HolomorphicVectorFields.inCoordinates
          (ℂ × ComplexPlane₂) Threefold.Space v y x =
        Wikipedia.HopfProblem.HolomorphicVectorFields.inCoordinates
          (ℂ × ComplexPlane₂) Threefold.Space w y x from by
      unfold Wikipedia.HopfProblem.HolomorphicVectorFields.inCoordinates
      rw [h x hx])
  have he := tendsto_nhds_unique_of_frequently_eq
    (Wikipedia.HopfProblem.HolomorphicVectorFields.inCoordinates_holomorphicAt
      (ℂ × ComplexPlane₂) Threefold.Space v y).continuousAt
    (Wikipedia.HopfProblem.HolomorphicVectorFields.inCoordinates_holomorphicAt
      (ℂ × ComplexPlane₂) Threefold.Space w y).continuousAt hfreq
  exact (Wikipedia.HopfProblem.HolomorphicVectorFields.inCoordinates_self
    (ℂ × ComplexPlane₂) Threefold.Space v y).symm.trans
      (he.trans (Wikipedia.HopfProblem.HolomorphicVectorFields.inCoordinates_self
        (ℂ × ComplexPlane₂) Threefold.Space w y))

theorem field_eq_of_regularCoefficients (v w : Threefold.HolomorphicVectorFields.Field)
    (h : ∀ x : Cover, regularCoefficients v x = regularCoefficients w x) : v = w := by
  apply field_eq_of_regular v w
  intro y hy
  have hy' : y ∈ range globalCover := by
    rw [range_globalCover]
    exact hy
  obtain ⟨x, rfl⟩ := hy'
  calc
    v (globalCover x) = mfderiv IF IF globalCover x (regularCoefficients v x) :=
      (regularLift_map v x).symm
    _ = mfderiv IF IF globalCover x (regularCoefficients w x) :=
      congrArg (mfderiv IF IF globalCover x) (h x)
    _ = w (globalCover x) := regularLift_map w x

theorem regularCoefficients_smul (c : ℂ) (v : Threefold.HolomorphicVectorFields.Field)
    (x : Cover) : regularCoefficients (c • v) x = c • regularCoefficients v x := by
  change (mfderiv IF IF globalCover x).inverse (c • v (globalCover x)) =
    c • (mfderiv IF IF globalCover x).inverse (v (globalCover x))
  exact (mfderiv IF IF globalCover x).inverse.map_smul c (v (globalCover x))

/-- The actual time generator is exactly e₂ in the original period vectors. -/
theorem regularCoefficients_generator (x : Cover) :
    regularCoefficients VerticalAction.generator x = (0, (![0, 1] : ComplexPlane₂)) := by
  apply (pullback_eq_iff globalCover globalCover_isLocalDiffeomorph
    VerticalAction.generator x (0, (![0, 1] : ComplexPlane₂))).mpr
  exact (VerticalAction.generator_globalCover x).symm

/-- A constant second-direction normal form identifies the original
global field with the corresponding scalar multiple of the genuine generator. -/
theorem field_eq_smul_generator_of_regularVertical (v : Threefold.HolomorphicVectorFields.Field)
    (c : ℂ) (h : ∀ z, regularVertical v z = (![0, c] : ComplexPlane₂)) :
    v = c • VerticalAction.generator := by
  apply field_eq_of_regularCoefficients
  rintro ⟨z, ζ⟩
  rw [regularCoefficients_eq, h z, regularCoefficients_smul, regularCoefficients_generator]
  apply Prod.ext
  · simp
  · funext i
    fin_cases i <;> simp

/-- The native generator's nonzero regular coefficient detects its scalar. -/
theorem smul_generator_injective :
    Function.Injective (fun c : ℂ => c • VerticalAction.generator) := by
  intro c d h
  let x : Cover := Classical.choice (inferInstance : Nonempty Cover)
  have he := congrArg
    (fun v : Threefold.HolomorphicVectorFields.Field => (regularCoefficients v x).2 1) h
  simpa only [regularCoefficients_smul, regularCoefficients_generator,
    Prod.smul_snd, Pi.smul_apply, smul_eq_mul, Matrix.cons_val_one, Matrix.cons_val_zero,
    mul_one] using he

end Wikipedia.HopfProblem.SpecialPeriods.Threefold.HolomorphicVectorFields.Classification
