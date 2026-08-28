import Wikipedia.HopfProblem.SpecialPeriodsThreefoldCanonicalGlobalComparisonAgreement
import Wikipedia.HopfProblem.SpecialPeriodsThreefoldCanonicalGlobalBaseTwistResults

/-!
# The actual global canonical-bundle formula

The genuine alternating-cotangent canonical bundle of the constructed
compact threefold is holomorphically isomorphic to the genuine tensor
bundle `f* O(-infinity) tensor O(2 S2)`.  The base factor is identified
with the actual sphere ideal sheaf on all chart subopens; the effective
factor has its proved order-two section.  All local comparisons and
their overlap equalities have been proved from the original periods,
chart differentials, and canonical sections.

This file proves the bundle formula in Proposition 9.11.  It does not
identify a relative canonical pushforward or assert the separate
non-torsion conclusion.
-/

noncomputable section

open Set Topology Bundle
open scoped ContDiff TensorProduct

namespace Wikipedia.HopfProblem.SpecialPeriods.Threefold.Canonical.GlobalComparison

open TrianglePeriodFamily.Canonical

attribute [local instance] Threefold.chartedSpace Threefold.space_isManifold

local notation "Iκ" => ModelWithCorners.prod
  (modelWithCornersSelf ℂ Model) (modelWithCornersSelf ℂ ℂ)

/-- The actual canonical line is the actual pulled-back ideal line
tensored with the actual effective order-two Cartier line. -/
def canonicalBundleBiholomorph : Diffeomorph Iκ Iκ Threefold.Canonical.bundle.TotalSpace
    GlobalPrescribedDivisor.bundle.TotalSpace ω :=
  NativePresentation.bundleBiholomorph.trans globalGauge.diffeomorph.symm

/-- Its continuous complex-linear map on each literal original fibre. -/
def canonicalFiberEquiv (x : Threefold.Space) :
    Threefold.Canonical.bundle.Fiber x ≃L[ℂ] GlobalPrescribedDivisor.bundle.Fiber x :=
  (NativePresentation.fiberEquiv x).trans (globalGauge.fiberEquiv x).symm

@[simp] theorem canonicalBundleBiholomorph_proj (p : Threefold.Canonical.bundle.TotalSpace) :
    (canonicalBundleBiholomorph p).proj = p.proj := rfl

@[simp] theorem canonicalBundleBiholomorph_symm_proj
    (p : GlobalPrescribedDivisor.bundle.TotalSpace) :
    (canonicalBundleBiholomorph.symm p).proj = p.proj := rfl

@[simp] theorem canonicalBundleBiholomorph_mk (x : Threefold.Space)
    (v : Threefold.Canonical.bundle.Fiber x) :
    canonicalBundleBiholomorph ⟨x, v⟩ = ⟨x, canonicalFiberEquiv x v⟩ := rfl

@[simp] theorem canonicalBundleBiholomorph_symm_mk (x : Threefold.Space)
    (v : GlobalPrescribedDivisor.bundle.Fiber x) :
    canonicalBundleBiholomorph.symm ⟨x, v⟩ = ⟨x, (canonicalFiberEquiv x).symm v⟩ := rfl

theorem canonicalBundleBiholomorph_add (x : Threefold.Space)
    (v w : Threefold.Canonical.bundle.Fiber x) :
    id (α := ℂ) (canonicalBundleBiholomorph ⟨x, v + w⟩).2 =
      id (α := ℂ) (canonicalBundleBiholomorph ⟨x, v⟩).2 +
        id (α := ℂ) (canonicalBundleBiholomorph ⟨x, w⟩).2 :=
  (canonicalFiberEquiv x).map_add v w

theorem canonicalBundleBiholomorph_smul (x : Threefold.Space) (c : ℂ)
    (v : Threefold.Canonical.bundle.Fiber x) :
    id (α := ℂ) (canonicalBundleBiholomorph ⟨x, c • v⟩).2 =
      c • id (α := ℂ) (canonicalBundleBiholomorph ⟨x, v⟩).2 :=
  (canonicalFiberEquiv x).map_smul c v

/-- The source fibre is the full space of continuous alternating
three-covectors on the actual global tangent space. -/
def intrinsicDivisorEquiv (x : Threefold.Space) :
    Threefold.Canonical.IntrinsicTopCovector x ≃L[ℂ]
      GlobalPrescribedDivisor.bundle.Fiber x :=
  (Threefold.Canonical.intrinsicEquiv x).symm.trans (canonicalFiberEquiv x)

@[simp] theorem intrinsicDivisorEquiv_apply (x : Threefold.Space)
    (v : Threefold.Canonical.bundle.Fiber x) :
    intrinsicDivisorEquiv x (Threefold.Canonical.intrinsicEquiv x v) =
      canonicalFiberEquiv x v := by
  change canonicalFiberEquiv x
    ((Threefold.Canonical.intrinsicEquiv x).symm (Threefold.Canonical.intrinsicEquiv x v)) = _
  rw [ContinuousLinearEquiv.symm_apply_apply]

/-- The formula identifies the actual top-covector fibre with the full
algebraic tensor product of the two original factor fibres. -/
def intrinsicTensorEquiv (x : Threefold.Space) :
    Threefold.Canonical.IntrinsicTopCovector x ≃ₗ[ℂ]
      GlobalBasePullback.bundle.Fiber x ⊗[ℂ] GlobalEllipticDivisor.divisorBundle.Fiber x :=
  (intrinsicDivisorEquiv x).toLinearEquiv.trans (GlobalPrescribedDivisor.fiberTensorEquiv x).symm

/-- A direct existence statement for the genuine holomorphic bundle
isomorphism, with no supplied gluing or canonical-bundle hypothesis. -/
theorem canonical_bundle_formula :
    ∃ e : Diffeomorph Iκ Iκ Threefold.Canonical.bundle.TotalSpace
        GlobalPrescribedDivisor.bundle.TotalSpace ω,
      (∀ p, (e p).proj = p.proj) ∧
      ∀ x, ∃ φ : Threefold.Canonical.bundle.Fiber x ≃L[ℂ]
          GlobalPrescribedDivisor.bundle.Fiber x,
        ∀ v, e ⟨x, v⟩ = ⟨x, φ v⟩ :=
  ⟨canonicalBundleBiholomorph, canonicalBundleBiholomorph_proj,
    fun x => ⟨canonicalFiberEquiv x, canonicalBundleBiholomorph_mk x⟩⟩

/-- The bundle formula preserves the actual normalized form on the
entire dense generic open, not only its transition character. -/
theorem canonicalBundleBiholomorph_genericSection (x : GlobalFiniteRegularSection.domain) :
    canonicalBundleBiholomorph (GlobalFiniteRegularSection.genericSectionMap x) =
      GlobalPrescribedDivisor.cartier.rawSectionMap x.val := by
  apply globalGauge.diffeomorph.injective
  exact (globalGauge.diffeomorph.apply_symm_apply
    (NativePresentation.bundleBiholomorph (GlobalFiniteRegularSection.genericSectionMap x))).trans
      (globalGauge_rawSection x.property).symm

theorem canonicalBundleBiholomorph_symm_rawSection {x : Threefold.Space}
    (hx : x ∈ cover .generic) :
    canonicalBundleBiholomorph.symm (GlobalPrescribedDivisor.cartier.rawSectionMap x) =
      GlobalFiniteRegularSection.genericSectionMap ⟨x, hx⟩ :=
  (congrArg NativePresentation.bundleBiholomorph.symm (globalGauge_rawSection hx)).trans
    (NativePresentation.bundleBiholomorph.symm_apply_apply _)

end Wikipedia.HopfProblem.SpecialPeriods.Threefold.Canonical.GlobalComparison
