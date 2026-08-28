import Wikipedia.HopfProblem.SpecialPeriodsThreefoldCanonicalPushforwardGenericRatioBasic
import Wikipedia.HopfProblem.SpecialPeriodsThreefoldCanonicalPushforwardSectionsNative

/-!
# Holomorphic ratios of original canonical sections

The native line-bundle ratio theorem applies to the actual alternating-
cotangent canonical bundle of the constructed threefold.  The resulting
scalar function and the recovery equality use the original fibres.
-/

noncomputable section

open TopologicalSpace
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.SpecialPeriods.Threefold.Canonical.Pushforward

open TrianglePeriodFamily.Canonical

attribute [local instance] Threefold.chartedSpace Threefold.space_isManifold

local notation "IF" => modelWithCornersSelf ℂ Model

/-- The actual scalar ratio of two original canonical sections. -/
def ratio (V : Opens Threefold.Space) (s t : Section V) : V → ℂ :=
  NativeBundleSections.ratio Threefold.Canonical.bundle IF V s t

theorem ratio_smul (V : Opens Threefold.Space) (s t : Section V)
    (ht : ∀ x, t x ≠ 0) (x : V) : ratio V s t x • t x = s x :=
  NativeBundleSections.ratio_smul Threefold.Canonical.bundle IF V s t ht x

theorem ratio_unique (V : Opens Threefold.Space) (s t : Section V)
    (ht : ∀ x, t x ≠ 0) (f : V → ℂ)
    (hf : ∀ x, f x • t x = s x) : f = ratio V s t :=
  NativeBundleSections.ratio_unique Threefold.Canonical.bundle IF V s t ht f hf

/-- Holomorphicity is with respect to the original threefold charts. -/
theorem ratio_holomorphic (V : Opens Threefold.Space) (s t : Section V)
    (ht : ∀ x, t x ≠ 0) : ContMDiff IF 𝓘(ℂ) ω (ratio V s t) :=
  NativeBundleSections.ratio_holomorphic Threefold.Canonical.bundle IF V s t ht

/-- The genuine holomorphic scalar section determined by native division. -/
def ratioSection (V : Opens Threefold.Space) (s t : Section V)
    (ht : ∀ x, t x ≠ 0) : HolomorphicFunctionSheaf.Section IF Threefold.Space V :=
  ⟨ratio V s t, ratio_holomorphic V s t ht⟩

@[simp] theorem ratioSection_apply (V : Opens Threefold.Space) (s t : Section V)
    (ht : ∀ x, t x ≠ 0) (x : V) : ratioSection V s t ht x = ratio V s t x := rfl

theorem ratio_restrict {V W : Opens Threefold.Space} (h : V ≤ W)
    (s t : Section W) (x : V) :
    ratio V (restrictSection h s) (restrictSection h t) x =
      ratio W s t ⟨x.val, h x.property⟩ := rfl

end Wikipedia.HopfProblem.SpecialPeriods.Threefold.Canonical.Pushforward
