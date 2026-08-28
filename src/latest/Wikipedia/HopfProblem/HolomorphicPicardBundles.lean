import Wikipedia.HopfProblem.PeriodTorusLineBundleClassificationNativeIso

/-!
# Original native holomorphic line bundles and their isomorphism classes

The objects record the original fibre family and the native topological,
linear and holomorphic bundle structures. No transition presentation,
frame, cohomology class, or classification premise is part of an object.
The quotient is by actual holomorphic fibre-linear isomorphisms. A group
law or a comparison with sheaf cohomology is not asserted by this file.
-/

noncomputable section

open Bundle
open scoped ContDiff

namespace Wikipedia.HopfProblem.HolomorphicPicard

open PeriodTorusLineBundleClassificationNative

universe u

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [TopologicalSpace H] (I : ModelWithCorners ℂ E H)
    (M : Type) [TopologicalSpace M] [ChartedSpace H M]

/-- An arbitrary original native holomorphic complex line bundle. -/
structure LineBundle where
  Fiber : M → Type u
  [addCommMonoid : ∀ x, AddCommMonoid (Fiber x)]
  [module : ∀ x, Module ℂ (Fiber x)]
  [fiberTopology : ∀ x, TopologicalSpace (Fiber x)]
  [totalTopology : TopologicalSpace (TotalSpace ℂ Fiber)]
  [fiberBundle : FiberBundle ℂ Fiber]
  [vectorBundle : VectorBundle ℂ ℂ Fiber]
  [holomorphic : ContMDiffVectorBundle ω ℂ Fiber I]

attribute [instance] LineBundle.addCommMonoid LineBundle.module
  LineBundle.fiberTopology LineBundle.totalTopology LineBundle.fiberBundle
  LineBundle.vectorBundle LineBundle.holomorphic

namespace LineBundle

/-- Bundle an original family without replacing any of its native instances. -/
def ofFamily (V : M → Type u)
    [∀ x, AddCommMonoid (V x)] [∀ x, Module ℂ (V x)]
    [∀ x, TopologicalSpace (V x)] [TopologicalSpace (TotalSpace ℂ V)]
    [FiberBundle ℂ V] [VectorBundle ℂ ℂ V] [ContMDiffVectorBundle ω ℂ V I] :
    LineBundle.{u} I M where
  Fiber := V

@[simp] theorem ofFamily_fiber (V : M → Type u)
    [∀ x, AddCommMonoid (V x)] [∀ x, Module ℂ (V x)]
    [∀ x, TopologicalSpace (V x)] [TopologicalSpace (TotalSpace ℂ V)]
    [FiberBundle ℂ V] [VectorBundle ℂ ℂ V] [ContMDiffVectorBundle ω ℂ V I] :
    (ofFamily I M V).Fiber = V := rfl

/-- The equivalence relation is the existence of a genuine analytic
diffeomorphism of the original total spaces with complex-linear fibre maps. -/
def isoSetoid : Setoid (LineBundle.{u} I M) where
  r V W := Nonempty (AnalyticBundleIso I V.Fiber W.Fiber)
  iseqv :=
    ⟨fun V => ⟨AnalyticBundleIso.refl V.Fiber⟩,
      fun ⟨e⟩ => ⟨e.symm⟩,
      fun ⟨e⟩ ⟨f⟩ => ⟨e.trans f⟩⟩

/-- The actual isomorphism classes of original holomorphic line bundles.
This definition does not identify them with cohomology. -/
def IsoClasses := Quotient (isoSetoid.{u} I M)

def toIsoClasses (V : LineBundle.{u} I M) : IsoClasses.{u} I M := Quotient.mk _ V

theorem toIsoClasses_eq_iff (V W : LineBundle.{u} I M) :
    toIsoClasses I M V = toIsoClasses I M W ↔
      Nonempty (AnalyticBundleIso I V.Fiber W.Fiber) := Quotient.eq

theorem toIsoClasses_surjective : Function.Surjective (toIsoClasses.{u} I M) :=
  Quotient.mk_surjective

end LineBundle

end Wikipedia.HopfProblem.HolomorphicPicard
