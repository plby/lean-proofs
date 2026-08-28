import Wikipedia.HopfProblem.HolomorphicPicardEquivalence
import Wikipedia.HopfProblem.HolomorphicPicardTensorBundlesBasic
import Wikipedia.HopfProblem.HolomorphicPicardTensorCoreTrivial
import Wikipedia.HopfProblem.HolomorphicPicardCechClassAdditive

/-!
# The actual tensor and dual objects have the expected genuine H¹ classes

Tensor and dual objects were constructed from the original native
transition functions, independently of cohomology. The proved refinement,
gluing and additivity theorems now identify their actual derived classes.
-/

noncomputable section

open Bundle TopologicalSpace CategoryTheory
open scoped ContDiff

namespace Wikipedia.HopfProblem.HolomorphicPicard.LineBundle

open HolomorphicExponentialSheaf HolomorphicPicardNative
  HolomorphicFunctionSheaf.SphereH1

universe u v

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [TopologicalSpace H] (I : ModelWithCorners ℂ E H)
    (M : Type) [TopologicalSpace M] [ChartedSpace H M]

/-- The original derived `Ext` group structure on the actual units sheaf.
This specialized instance also works before unfolding the native manifold
and topological-sheaf synonyms. -/
instance unitsCohomologyAddCommGroup (n : ℕ) :
    AddCommGroup (CategoryTheory.Sheaf.H.{0} (unitsSheaf I M) n) :=
  CategoryTheory.Abelian.Ext.instAddCommGroup

theorem cohomologyClass_tensorBundle (V : LineBundle.{u} I M) (W : LineBundle.{v} I M) :
    cohomologyClass I M (tensorBundle I M V W) =
      cohomologyClass I M V + cohomologyClass I M W := by
  have hglue := nativeClass_glued I M (TensorBundles.commonCover I M V W)
    (TensorBundles.commonCover_covers I M V W) (TensorBundles.tensorCocycle I M V W)
  have hadd := CechExtension.classOf_add
    (Cech.refinement (unitsSheaf I M) Prod.fst (isoGaugeCover_le_left M V.Fiber W.Fiber)
      (nativeCocycle I M V.Fiber))
    (Cech.refinement (unitsSheaf I M) Prod.snd (isoGaugeCover_le_right M V.Fiber W.Fiber)
      (nativeCocycle I M W.Fiber)) (TensorBundles.commonCover_covers I M V W)
  have hV := CechExtension.classOf_refinement Prod.fst (isoGaugeCover_le_left M V.Fiber W.Fiber)
    (nativeCocycle I M V.Fiber) (nativeCover_covers M V.Fiber)
    (TensorBundles.commonCover_covers I M V W)
  have hW := CechExtension.classOf_refinement Prod.snd (isoGaugeCover_le_right M V.Fiber W.Fiber)
    (nativeCocycle I M W.Fiber) (nativeCover_covers M W.Fiber)
    (TensorBundles.commonCover_covers I M V W)
  exact hglue.trans (hadd.trans (congrArg₂ (· + ·) hV hW))

theorem cohomologyClass_dualBundle (V : LineBundle.{u} I M) :
    cohomologyClass I M (dualBundle I M V) = -cohomologyClass I M V := by
  exact (nativeClass_glued I M (nativeCover M V.Fiber) (nativeCover_covers M V.Fiber)
    (-(nativeCocycle I M V.Fiber))).trans
    (CechExtension.classOf_neg (nativeCocycle I M V.Fiber) (nativeCover_covers M V.Fiber))

theorem cohomologyClass_trivialBundle : cohomologyClass I M (trivialBundle I M) = 0 := by
  let U : Unit → Opens M := fun _ => ⊤
  have hU : ∀ x : M, ∃ i, x ∈ U i := fun _ => ⟨(), trivial⟩
  let c : CechOneCocycle (unitsSheaf I M) U := 0
  have hiso := nativeClass_eq_of_iso I M (cocycleCore I M U hU c).Fiber
    (Bundle.Trivial M ℂ) (TensorCore.zeroTrivialIso I M U hU)
  exact hiso.symm.trans ((nativeClass_glued I M U hU c).trans (CechExtension.classOf_zero hU))

end Wikipedia.HopfProblem.HolomorphicPicard.LineBundle
