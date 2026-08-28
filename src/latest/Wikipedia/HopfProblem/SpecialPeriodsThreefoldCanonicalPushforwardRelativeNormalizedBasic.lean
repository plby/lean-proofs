import Wikipedia.HopfProblem.SpecialPeriodsThreefoldCanonicalPushforwardRelativePositive

/-!
# The normalized actual relative canonical section

The genuine positive-line section is transported back through the proved
relative canonical direct-image equivalence. This gives actual native
relative canonical sections on every full base preimage, compatible with
literal restriction. The finite-chart formula is proved separately.
-/

noncomputable section

open TopologicalSpace Opposite
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.SpecialPeriods.Threefold.Canonical.Pushforward.Relative

attribute [local instance] Threefold.chartedSpace Threefold.space_isManifold

local notation "IF" => modelWithCornersSelf ℂ (ℂ × ComplexPlane₂)

/-- The original relative canonical section corresponding to the actual positive section. -/
def normalizedSection (U : Opens RiemannSphere) : Section U :=
  (canonicalSectionPositiveEquiv U).symm (Positive.sectionOn U)

/-- Its literal map into the original relative canonical bundle total space. -/
def normalizedSectionMap (U : Opens RiemannSphere) (x : Threefold.basePreimage U) :
    RelativeBundle.bundle.TotalSpace := ⟨x.val, normalizedSection U x⟩

@[simp] theorem normalizedSectionMap_proj (U : Opens RiemannSphere)
    (x : Threefold.basePreimage U) : (normalizedSectionMap U x).proj = x.val := rfl

theorem normalizedSectionMap_holomorphic (U : Opens RiemannSphere) :
    ContMDiff IF ((IF).prod 𝓘(ℂ)) ω (normalizedSectionMap U) :=
  (normalizedSection U).contMDiff_toFun

/-- The actual direct-image comparison recovers the prescribed native positive section. -/
@[simp] theorem normalizedSection_positive (U : Opens RiemannSphere) :
    canonicalSectionPositiveEquiv U (normalizedSection U) = Positive.sectionOn U :=
  (canonicalSectionPositiveEquiv U).apply_symm_apply (Positive.sectionOn U)

@[simp] theorem normalizedSection_positive_apply (U : Opens RiemannSphere) (p : U) :
    canonicalSectionPositiveEquiv U (normalizedSection U) p = Positive.sectionValue p :=
  congrArg (fun s : Positive.Section U => s p) (normalizedSection_positive U)

/-- These are the literal restrictions of one global native relative canonical section. -/
theorem normalizedSection_restrict {U V : Opens RiemannSphere} (h : U ≤ V) :
    NativeBundleSections.Section.restrict RelativeBundle.bundle IF
        (Threefold.basePreimage_mono h) (normalizedSection V) = normalizedSection U :=
  (canonicalSectionPositiveEquiv_symm_restrict h (Positive.sectionOn V)).trans
    (congrArg (canonicalSectionPositiveEquiv U).symm (Positive.sectionOn_restrict h))

/-- The same normalization is preserved by the actual sheaf isomorphism. -/
theorem normalizedSection_sheaf_image (U : Opens RiemannSphere) :
    relativeCanonicalDirectImageIso.hom.hom.app (op U) (normalizedSection U) =
      Positive.sheafSection U := normalizedSection_positive U

/-- The normalized section over the full original sphere preimage. -/
def normalizedGlobalSection : Section ⊤ := normalizedSection ⊤

theorem normalizedGlobalSection_restrict (U : Opens RiemannSphere) :
    NativeBundleSections.Section.restrict RelativeBundle.bundle IF
        (Threefold.basePreimage_mono (show U ≤ ⊤ from le_top)) normalizedGlobalSection =
      normalizedSection U := normalizedSection_restrict le_top

end Wikipedia.HopfProblem.SpecialPeriods.Threefold.Canonical.Pushforward.Relative
