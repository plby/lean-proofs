import Wikipedia.HopfProblem.SpecialPeriodsThreefoldCanonicalPushforwardDescentLinear
import Wikipedia.HopfProblem.SpecialPeriodsThreefoldCanonicalPushforwardReconstruction
import Wikipedia.HopfProblem.SpecialPeriodsThreefoldCanonicalPushforwardSectionsDense

/-!
# Native canonical sections are the actual O(-infinity) ideal sections

Descent and native reconstruction are inverse on every original sphere
open. The proof uses the literal normalized canonical form on the dense
generic preimage and equality of actual native sections in their original
bundle charts. The resulting equivalence is O(U)-linear and natural for
all literal restrictions in both directions.
-/

noncomputable section

open Set TopologicalSpace
open scoped ContDiff Manifold OnePoint

namespace Wikipedia.HopfProblem.SpecialPeriods.Threefold.Canonical.Pushforward

open HolomorphicFunctionSheaf.SphereH1

attribute [local instance] Threefold.chartedSpace Threefold.space_isManifold

local notation "IF" => modelWithCornersSelf ℂ (ℂ × ComplexPlane₂)

/-- Reconstruction after descent recovers the original native section,
including on both exceptional fibres. -/
theorem sectionOfIdeal_idealSection (U : Opens RiemannSphere) (s : PreimageSection U) :
    Reconstruction.sectionOfIdeal U (Descent.idealSection U s) = s := by
  apply NativeBundleSections.Section.ext_of_dense Threefold.Canonical.bundle IF
    (Generic.preimage_genericPart_dense U)
  intro x hx
  have hg : Threefold.projectionSphere x.val ∈ Generic.genericBase :=
    (GlobalFiniteRegularSection.mem_domain x.val).mp hx
  rw [Reconstruction.sectionOfIdeal_apply_of_ne_infty U (Descent.idealSection U s) x hg.1]
  exact Descent.coefficient_smul_rawSection U s ⟨x.val, ⟨x.property, hg⟩⟩

/-- Descent after reconstruction recovers the original actual ideal
function, rather than only an abstractly isomorphic scalar section. -/
theorem idealSection_sectionOfIdeal (U : Opens RiemannSphere) (h : NegativeOneSection U) :
    Descent.idealSection U (Reconstruction.sectionOfIdeal U h) = h := by
  apply Subtype.ext
  apply CanonicalPushforwardExtension.section_eq_of_dense 𝓘(ℂ) RiemannSphere
    Generic.genericBase_dense U
  intro p hp
  let pg : Generic.genericPart U := ⟨p.val, ⟨p.property, hp⟩⟩
  obtain ⟨x, hx⟩ := Threefold.baseProjection_surjective (Generic.genericPart U) pg
  have hc := Descent.coefficient_smul_rawSection U (Reconstruction.sectionOfIdeal U h) x
  have hr := Reconstruction.sectionOfIdeal_apply_of_ne_infty U h
    (Generic.preimagePoint U x) x.property.2.1
  have hn : id (α := ℂ) (GlobalMeromorphicSection.rawSection x.val) ≠ 0 :=
    GlobalMeromorphicSection.rawSection_ne_zero (Generic.domainPoint U x).property
  have he : Descent.coefficient U (Reconstruction.sectionOfIdeal U h)
      (Threefold.baseProjection U (Generic.preimagePoint U x)) =
        h.val (Threefold.baseProjection U (Generic.preimagePoint U x)) :=
    mul_right_cancel₀ hn (hc.trans hr)
  have hb := congrArg (Generic.basePoint U) hx
  change Threefold.baseProjection U (Generic.preimagePoint U x) = p at hb
  rw [hb] at he
  exact he

/-- The genuine O(U)-linear canonical pushforward identification on every
base open, between original native sections and the literal vanishing ideal. -/
def canonicalSectionIdealEquiv (U : Opens RiemannSphere) :
    PreimageSection U ≃ₗ[Threefold.BaseSection U] NegativeOneSection U where
  __ := Descent.idealLinearMap U
  invFun := Reconstruction.sectionOfIdeal U
  left_inv := sectionOfIdeal_idealSection U
  right_inv := idealSection_sectionOfIdeal U

@[simp] theorem canonicalSectionIdealEquiv_apply (U : Opens RiemannSphere)
    (s : PreimageSection U) : canonicalSectionIdealEquiv U s = Descent.idealSection U s := rfl

@[simp] theorem canonicalSectionIdealEquiv_symm_apply (U : Opens RiemannSphere)
    (h : NegativeOneSection U) :
    (canonicalSectionIdealEquiv U).symm h = Reconstruction.sectionOfIdeal U h := rfl

/-- Every original canonical section is recovered by its actual ideal
coefficient times Ω throughout the entire generic preimage. -/
theorem canonicalSectionIdealEquiv_recovery (U : Opens RiemannSphere)
    (s : PreimageSection U) (x : Threefold.basePreimage (Generic.genericPart U)) :
    (canonicalSectionIdealEquiv U s).val
        (Threefold.baseProjection U (Generic.preimagePoint U x)) •
      GlobalMeromorphicSection.rawSection x.val = s (Generic.preimagePoint U x) :=
  Descent.coefficient_smul_rawSection U s x

/-- The inverse is the literal finite formula, including at the elliptic zero surface. -/
theorem canonicalSectionIdealEquiv_symm_finite (U : Opens RiemannSphere)
    (h : NegativeOneSection U) (x : Threefold.basePreimage U)
    (hx : Threefold.projectionSphere x.val ≠ (∞ : RiemannSphere)) :
    (canonicalSectionIdealEquiv U).symm h x =
      h.val (Threefold.baseProjection U x) • GlobalMeromorphicSection.rawSection x.val :=
  Reconstruction.sectionOfIdeal_apply_of_ne_infty U h x hx

/-- The section equivalences commute with every actual base restriction. -/
theorem canonicalSectionIdealEquiv_restrict {U V : Opens RiemannSphere} (h : U ≤ V)
    (s : PreimageSection V) :
    canonicalSectionIdealEquiv U (restrictPreimageSection h s) =
      negativeOneRestriction h (canonicalSectionIdealEquiv V s) :=
  Descent.idealSection_restrict h s

/-- The actual reconstruction equivalences are natural in the same direction. -/
theorem canonicalSectionIdealEquiv_symm_restrict {U V : Opens RiemannSphere} (h : U ≤ V)
    (s : NegativeOneSection V) :
    (canonicalSectionIdealEquiv U).symm (negativeOneRestriction h s) =
      restrictPreimageSection h ((canonicalSectionIdealEquiv V).symm s) := by
  apply (canonicalSectionIdealEquiv U).injective
  rw [LinearEquiv.apply_symm_apply, canonicalSectionIdealEquiv_restrict,
    LinearEquiv.apply_symm_apply]

end Wikipedia.HopfProblem.SpecialPeriods.Threefold.Canonical.Pushforward
