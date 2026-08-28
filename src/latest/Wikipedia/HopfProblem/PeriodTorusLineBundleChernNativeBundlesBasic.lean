import Wikipedia.HopfProblem.PeriodTorusLineBundleChernNativePresentation

/-!
# Bundling original native holomorphic line bundles

This small wrapper records the original fibre family, its topology, and
the native holomorphic vector-bundle structures.  It contains no factor,
frame, characteristic class, or classification hypothesis.  It permits
the image of the genuine first Chern class to be expressed as a set.
-/

noncomputable section

open Bundle
open scoped ContDiff

namespace Wikipedia.HopfProblem.PeriodTorusLineBundle.ChernNative

open PeriodTorusAppellHumbert PeriodTorusLineBundleClassificationNative

universe u

/-- An original native holomorphic complex line bundle, with no presentation data. -/
structure NativeLineBundle (p : PeriodDomain) where
  Fiber : p.Torus → Type u
  [addCommMonoid : ∀ x, AddCommMonoid (Fiber x)]
  [module : ∀ x, Module ℂ (Fiber x)]
  [fiberTopology : ∀ x, TopologicalSpace (Fiber x)]
  [totalTopology : TopologicalSpace (TotalSpace ℂ Fiber)]
  [fiberBundle : FiberBundle ℂ Fiber]
  [vectorBundle : VectorBundle ℂ ℂ Fiber]
  [holomorphic : ContMDiffVectorBundle ω ℂ Fiber (modelWithCornersSelf ℂ ComplexPlane₂)]

attribute [instance] NativeLineBundle.addCommMonoid NativeLineBundle.module
  NativeLineBundle.fiberTopology NativeLineBundle.totalTopology NativeLineBundle.fiberBundle
  NativeLineBundle.vectorBundle NativeLineBundle.holomorphic

namespace NativeLineBundle

variable (p : PeriodDomain)

/-- The wrapper preserves every original native bundle instance. -/
def ofFamily (V : p.Torus → Type u)
    [∀ x, AddCommMonoid (V x)] [∀ x, Module ℂ (V x)]
    [∀ x, TopologicalSpace (V x)] [TopologicalSpace (TotalSpace ℂ V)]
    [FiberBundle ℂ V] [VectorBundle ℂ ℂ V]
    [ContMDiffVectorBundle ω ℂ V (modelWithCornersSelf ℂ ComplexPlane₂)] :
    NativeLineBundle.{u} p where
  Fiber := V

/-- Every actual factor supplies an original native holomorphic line bundle. -/
def ofFactor (F : FactorOfAutomorphy p) : NativeLineBundle.{0} p :=
  ofFamily p (Core.data F).core.Fiber

@[simp] theorem ofFamily_fiber (V : p.Torus → Type u)
    [∀ x, AddCommMonoid (V x)] [∀ x, Module ℂ (V x)]
    [∀ x, TopologicalSpace (V x)] [TopologicalSpace (TotalSpace ℂ V)]
    [FiberBundle ℂ V] [VectorBundle ℂ ℂ V]
    [ContMDiffVectorBundle ω ℂ V (modelWithCornersSelf ℂ ComplexPlane₂)] :
    (ofFamily p V).Fiber = V := rfl

@[simp] theorem ofFactor_fiber (F : FactorOfAutomorphy p) :
    (ofFactor p F).Fiber = (Core.data F).core.Fiber := rfl

/-- The relation uses genuine analytic isomorphisms of original native bundles. -/
def isoSetoid : Setoid (NativeLineBundle.{u} p) where
  r V W := Nonempty (AnalyticBundleIso (modelWithCornersSelf ℂ ComplexPlane₂) V.Fiber W.Fiber)
  iseqv :=
    ⟨fun V => ⟨AnalyticBundleIso.refl V.Fiber⟩,
      fun ⟨e⟩ => ⟨e.symm⟩,
      fun ⟨e⟩ ⟨f⟩ => ⟨e.trans f⟩⟩

/-- Actual native holomorphic line bundles modulo their analytic fibre-linear isomorphisms.
No group law or tensor construction is introduced by this quotient. -/
def IsoClasses := Quotient (isoSetoid.{u} p)

/-- The original native bundle determines its actual isomorphism class. -/
def toIsoClasses (V : NativeLineBundle.{u} p) : IsoClasses.{u} p :=
  Quotient.mk _ V

theorem toIsoClasses_eq_iff (V W : NativeLineBundle.{u} p) :
    toIsoClasses p V = toIsoClasses p W ↔
      Nonempty (AnalyticBundleIso (modelWithCornersSelf ℂ ComplexPlane₂) V.Fiber W.Fiber) :=
  Quotient.eq

end NativeLineBundle

end Wikipedia.HopfProblem.PeriodTorusLineBundle.ChernNative
