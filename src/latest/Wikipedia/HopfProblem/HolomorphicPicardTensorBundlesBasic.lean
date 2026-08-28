import Wikipedia.HopfProblem.HolomorphicPicardBundles
import Wikipedia.HopfProblem.HolomorphicPicardCechRefinement
import Wikipedia.HopfProblem.HolomorphicPicardNativeIsoGaugeBasic
import Wikipedia.HopfProblem.HolomorphicPicardNativeGluing

/-!
# Tensor and dual objects for arbitrary original native line bundles

The tensor cocycle is the sum of the two original native unit cocycles,
restricted to their actual common trivializing cover.  The dual cocycle
is the negative of the original native cocycle.  Gluing these genuine
sections produces actual native holomorphic line bundles; no cohomology
class or classification theorem enters these definitions.
-/

noncomputable section

open Bundle TopologicalSpace
open scoped ContDiff

namespace Wikipedia.HopfProblem.HolomorphicPicard

open HolomorphicExponentialSheaf HolomorphicPicardNative
open HolomorphicFunctionSheaf.SphereH1

universe u v

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [TopologicalSpace H] (I : ModelWithCorners ℂ E H)
  (M : Type) [TopologicalSpace M] [ChartedSpace H M]

namespace TensorBundles

variable (V : LineBundle.{u} I M) (W : LineBundle.{v} I M)

/-- The common cover is the intersection of the two original native covers. -/
abbrev commonCover : M × M → Opens M := isoGaugeCover M V.Fiber W.Fiber

theorem commonCover_covers (x : M) : ∃ a, x ∈ commonCover I M V W a :=
  isoGaugeCover_covers M V.Fiber W.Fiber x

/-- Literal restrictions of the original native cocycles, added in the
actual holomorphic unit sheaf. -/
def tensorCocycle : CechOneCocycle (unitsSheaf I M) (commonCover I M V W) :=
  Cech.refinement (unitsSheaf I M) Prod.fst
      (isoGaugeCover_le_left M V.Fiber W.Fiber) (nativeCocycle I M V.Fiber) +
    Cech.refinement (unitsSheaf I M) Prod.snd
      (isoGaugeCover_le_right M V.Fiber W.Fiber) (nativeCocycle I M W.Fiber)

/-- Actual scalar transition data of the tensor construction. -/
abbrev tensorData :=
  cocycleTransitionData I M (commonCover I M V W) (commonCover_covers I M V W)
    (tensorCocycle I M V W)

/-- The ordinary native `VectorBundleCore` of the tensor cocycle. -/
abbrev tensorCore := (tensorData I M V W).core

/-- The inverse of the original holomorphic unit cocycle. -/
abbrev dualCocycle : CechOneCocycle (unitsSheaf I M) (nativeCover M V.Fiber) :=
  -(nativeCocycle I M V.Fiber)

/-- Actual scalar transition data of the dual construction. -/
abbrev dualData :=
  cocycleTransitionData I M (nativeCover M V.Fiber) (nativeCover_covers M V.Fiber)
    (dualCocycle I M V)

/-- The ordinary native `VectorBundleCore` of the inverse cocycle. -/
abbrev dualCore := (dualData I M V).core

end TensorBundles

namespace LineBundle

/-- The actual native tensor object, constructed from the original two
bundles' transitions on their common cover. -/
def tensorBundle (V : LineBundle.{u} I M) (W : LineBundle.{v} I M) : LineBundle.{0} I M :=
  ofFamily I M (TensorBundles.tensorCore I M V W).Fiber

/-- The actual native dual object, constructed from inverse transitions. -/
def dualBundle (V : LineBundle.{u} I M) : LineBundle.{0} I M :=
  ofFamily I M (TensorBundles.dualCore I M V).Fiber

/-- The genuine native trivial complex line bundle is the unit object. -/
def trivialBundle : LineBundle.{0} I M := ofFamily I M (Bundle.Trivial M ℂ)

@[simp] theorem tensorBundle_fiber (V : LineBundle.{u} I M) (W : LineBundle.{v} I M) :
    (tensorBundle I M V W).Fiber = (TensorBundles.tensorCore I M V W).Fiber := rfl

@[simp] theorem dualBundle_fiber (V : LineBundle.{u} I M) :
    (dualBundle I M V).Fiber = (TensorBundles.dualCore I M V).Fiber := rfl

@[simp] theorem trivialBundle_fiber : (trivialBundle I M).Fiber = Bundle.Trivial M ℂ := rfl

end LineBundle

end Wikipedia.HopfProblem.HolomorphicPicard
