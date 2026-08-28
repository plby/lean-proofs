import Wikipedia.HopfProblem.PeriodTorusLineBundleClassificationHolomorphicFrameNative
import Wikipedia.HopfProblem.PeriodTorusLineBundleClassificationTopologicalCover

/-!
# Genuine holomorphic triviality of every actual universal-cover pullback

For an arbitrary native holomorphic complex line bundle on the actual period
torus, this file constructs a nowhere-zero holomorphic section of Mathlib's
original pullback along the actual quotient projection. The smooth frame,
closed antiholomorphic form, global primitive, and holomorphic correction
have all been proved, not required as input data.
-/

noncomputable section

open Set Bundle
open scoped ContDiff

namespace Wikipedia.HopfProblem.PeriodTorusLineBundleClassificationHolomorphicFrame

open PeriodTorusLineBundleClassificationTopological

local notation "Iℂ" => modelWithCornersSelf ℂ ComplexPlane₂
local notation "I₁" => modelWithCornersSelf ℂ ℂ

variable (p : PeriodDomain) (V : p.Torus → Type*)
    [∀ x, AddCommMonoid (V x)] [∀ x, Module ℂ (V x)]
    [∀ x, TopologicalSpace (V x)] [TopologicalSpace (TotalSpace ℂ V)]
    [FiberBundle ℂ V] [VectorBundle ℂ ℂ V] [ContMDiffVectorBundle ω ℂ V Iℂ]

/-- An actual native holomorphic frame of the universal-cover pullback. -/
def pullbackHolomorphicSection : ContMDiffSection Iℂ ℂ ω (universalCoverPullback p V) :=
  nativeHolomorphicSection (universalCoverPullback p V)

theorem pullbackHolomorphicSection_ne_zero (x : ComplexPlane₂) :
    pullbackHolomorphicSection p V x ≠ 0 :=
  nativeHolomorphicSection_ne_zero (universalCoverPullback p V) x

/-- The genuine existence theorem has only the actual native holomorphic
line-bundle structure as input, not a frame or a trivialization premise. -/
theorem exists_pullback_holomorphic_nonzero_section :
    ∃ s : ContMDiffSection Iℂ ℂ ω (universalCoverPullback p V), ∀ x, s x ≠ 0 :=
  ⟨pullbackHolomorphicSection p V, pullbackHolomorphicSection_ne_zero p V⟩

def pullbackProductDiffeomorph :
    Diffeomorph ((Iℂ).prod I₁) ((Iℂ).prod I₁)
      (TotalSpace ℂ (universalCoverPullback p V)) (ComplexPlane₂ × ℂ) ω :=
  nativeProductDiffeomorph (universalCoverPullback p V)

theorem pullbackProductDiffeomorph_preserves_base
    (v : TotalSpace ℂ (universalCoverPullback p V)) :
    (pullbackProductDiffeomorph p V v).1 = v.proj :=
  nativeProductDiffeomorph_preserves_base (universalCoverPullback p V) v

theorem pullbackProductDiffeomorph_add (x : ComplexPlane₂)
    (v w : universalCoverPullback p V x) :
    (pullbackProductDiffeomorph p V ⟨x, v + w⟩).2 =
      (pullbackProductDiffeomorph p V ⟨x, v⟩).2 +
        (pullbackProductDiffeomorph p V ⟨x, w⟩).2 :=
  nativeProductDiffeomorph_add (universalCoverPullback p V) x v w

theorem pullbackProductDiffeomorph_smul (x : ComplexPlane₂) (c : ℂ)
    (v : universalCoverPullback p V x) :
    (pullbackProductDiffeomorph p V ⟨x, c • v⟩).2 =
      c • (pullbackProductDiffeomorph p V ⟨x, v⟩).2 :=
  nativeProductDiffeomorph_smul (universalCoverPullback p V) x c v

end Wikipedia.HopfProblem.PeriodTorusLineBundleClassificationHolomorphicFrame
