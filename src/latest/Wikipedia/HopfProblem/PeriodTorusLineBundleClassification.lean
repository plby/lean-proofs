import Wikipedia.HopfProblem.PeriodTorusLineBundleClassificationFactorNormalForm
import Wikipedia.HopfProblem.PeriodTorusLineBundleClassificationFactorDescentNative
import Wikipedia.HopfProblem.PeriodTorusLineBundleClassificationSectionTheta

/-!
# Appell--Humbert classification of arbitrary native period-torus line bundles

The input is an arbitrary genuine native holomorphic complex line bundle
over the actual period torus. The universal-cover frame, factor of
automorphy, normal-form data, and analytic bundle isomorphism are all
constructed by the imported theorems. None is an input premise.

The resulting classification retains the full unitary semicharacter, and
transports the original native holomorphic sections to genuine entire
theta functions. No statement about arbitrary meromorphic functions or
polar Cartier divisors is assumed or encoded by this correspondence.
-/

noncomputable section

open Bundle
open scoped ContDiff

namespace Wikipedia.HopfProblem.PeriodTorusLineBundleClassification

open PeriodTorusAppellHumbert PeriodTorusLineBundleClassificationNative
open PeriodTorusLineBundleClassificationUniqueness

local notation "IC" => modelWithCornersSelf ℂ ComplexPlane₂

variable (p : PeriodDomain) (V : p.Torus → Type*)
    [∀ x, AddCommMonoid (V x)] [∀ x, Module ℂ (V x)]
    [∀ x, TopologicalSpace (V x)] [TopologicalSpace (TotalSpace ℂ V)]
    [FiberBundle ℂ V] [VectorBundle ℂ ℂ V] [ContMDiffVectorBundle ω ℂ V IC]

/-- Every independently given native holomorphic complex line bundle on
the actual period torus has an actual unitary Appell--Humbert presentation. -/
theorem exists_native_unitaryDatum_bundleIso :
    ∃ D : UnitaryDatum p,
      Nonempty (AnalyticBundleIso IC (Core.data D.factor).core.Fiber V) := by
  obtain ⟨F, ⟨eF⟩⟩ :=
    PeriodTorusLineBundleClassificationFactorDescent.exists_native_factor_presentation p V
  obtain ⟨D, ⟨eD⟩⟩ := exists_unitaryDatum_bundleIso F
  exact ⟨D, ⟨eD.trans eF⟩⟩

/-- Full existence and uniqueness for arbitrary native holomorphic line
bundles, not only for bundles supplied with factors or covering frames. -/
theorem existsUnique_native_unitaryDatum_bundleIso :
    ∃! D : UnitaryDatum p,
      Nonempty (AnalyticBundleIso IC (Core.data D.factor).core.Fiber V) := by
  obtain ⟨D, ⟨e⟩⟩ := exists_native_unitaryDatum_bundleIso p V
  refine ⟨D, ⟨e⟩, ?_⟩
  rintro D' ⟨e'⟩
  exact unitaryDatum_eq_of_bundleIso D' D (e'.trans e.symm)

/-- The uniquely determined genuine unitary data of the original bundle. -/
def nativeUnitaryDatum : UnitaryDatum p :=
  (existsUnique_native_unitaryDatum_bundleIso p V).choose

/-- An actual native analytic, fibrewise complex-linear isomorphism from
the constructed Appell--Humbert bundle to the original bundle. -/
def nativeAppellHumbertIso :
    AnalyticBundleIso IC (Core.data (nativeUnitaryDatum p V).factor).core.Fiber V :=
  Classical.choice (existsUnique_native_unitaryDatum_bundleIso p V).choose_spec.1

theorem nativeUnitaryDatum_unique (D : UnitaryDatum p)
    (e : AnalyticBundleIso IC (Core.data D.factor).core.Fiber V) :
    D = nativeUnitaryDatum p V :=
  (existsUnique_native_unitaryDatum_bundleIso p V).choose_spec.2 D ⟨e⟩

/-- The constructed data depend only on the actual native analytic bundle
isomorphism class. -/
theorem nativeUnitaryDatum_eq_of_bundleIso (W : p.Torus → Type*)
    [∀ x, AddCommMonoid (W x)] [∀ x, Module ℂ (W x)]
    [∀ x, TopologicalSpace (W x)] [TopologicalSpace (TotalSpace ℂ W)]
    [FiberBundle ℂ W] [VectorBundle ℂ ℂ W] [ContMDiffVectorBundle ω ℂ W IC]
    (e : AnalyticBundleIso IC V W) : nativeUnitaryDatum p V = nativeUnitaryDatum p W :=
  nativeUnitaryDatum_unique p W _ ((nativeAppellHumbertIso p V).trans e)

/-- Two arbitrary native line bundles are analytically isomorphic exactly
when their full unitary Appell--Humbert data agree. -/
theorem nativeUnitaryDatum_eq_iff_nonempty_bundleIso (W : p.Torus → Type*)
    [∀ x, AddCommMonoid (W x)] [∀ x, Module ℂ (W x)]
    [∀ x, TopologicalSpace (W x)] [TopologicalSpace (TotalSpace ℂ W)]
    [FiberBundle ℂ W] [VectorBundle ℂ ℂ W] [ContMDiffVectorBundle ω ℂ W IC] :
    nativeUnitaryDatum p V = nativeUnitaryDatum p W ↔ Nonempty (AnalyticBundleIso IC V W) := by
  constructor
  · intro h
    have eW : AnalyticBundleIso IC (Core.data (nativeUnitaryDatum p V).factor).core.Fiber W := by
      rw [h]
      exact nativeAppellHumbertIso p W
    exact ⟨(nativeAppellHumbertIso p V).symm.trans eW⟩
  · rintro ⟨e⟩
    exact nativeUnitaryDatum_eq_of_bundleIso p V W e

/-- The classification acts on genuine native holomorphic sections. -/
def nativeSectionEquivTheta :
    ContMDiffSection IC ℂ ω V ≃ EntireThetaFunction (nativeUnitaryDatum p V).factor :=
  sectionEquivThetaOfNativeIso _ (nativeAppellHumbertIso p V)

theorem nativeSectionEquivTheta_covering (s : ContMDiffSection IC ℂ ω V)
    (z : ComplexPlane₂) :
    (nativeAppellHumbertIso p V).diffeomorph
      (Core.fromAssociated (nativeUnitaryDatum p V).factor
        (associatedMap (nativeUnitaryDatum p V).factor
          (z, (nativeSectionEquivTheta p V s).val z))) =
      ⟨p.lattice.mkQ z, s (p.lattice.mkQ z)⟩ :=
  sectionEquivThetaOfNativeIso_covering _ _ s z

/-- Starting with genuine unitary data and its native constructed bundle
recovers exactly the original datum, including its semicharacter. -/
theorem nativeUnitaryDatum_of_unitaryFactor (D : UnitaryDatum p) :
    nativeUnitaryDatum p (Core.data D.factor).core.Fiber = D := by
  symm
  exact nativeUnitaryDatum_unique p (Core.data D.factor).core.Fiber D
    (AnalyticBundleIso.refl _)

end Wikipedia.HopfProblem.PeriodTorusLineBundleClassification
