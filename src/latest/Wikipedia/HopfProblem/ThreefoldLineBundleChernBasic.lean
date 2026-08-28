import Wikipedia.HopfProblem.HolomorphicPicardChern
import Wikipedia.HopfProblem.ThreefoldPicardExponential

/-!
# The original threefold's line-bundle Chern map in singular cohomology

This map is the original native unit cocycle, followed by the genuine
exponential connecting homomorphism, followed by the actual integral
constant-sheaf--singular comparison. The codomain is the original integral
singular cohomology of the original glued space. No zero map or rank-defined
replacement is used in the construction.

The comparison with the separately constructed period-torus winding Chern
representatives is not asserted by this file.
-/

noncomputable section

open Bundle CategoryTheory
open scoped ContDiff

namespace Wikipedia.HopfProblem.SpecialPeriods.Threefold.LineBundleChern

open HolomorphicExponentialSheaf HolomorphicPicardNative SingularCohomologyFree
  PeriodTorusLineBundleClassificationNative

universe u v

attribute [local instance] chartedSpace

local notation "IF" => modelWithCornersSelf ℂ (ℂ × ComplexPlane₂)

/-- The first-Chern homomorphism is the genuine connecting map followed
by the actual coefficient-sheaf comparison, on native tensor classes. -/
def firstChernHom : PicardExponential.PicardGroup →+ SingularCohomology Space 2 :=
  PicardExponential.integerSheafH2Equiv.toAddMonoidHom.comp
    (HolomorphicPicard.Chern.firstChernHom IF Space)

/-- The exact three maps in the definition, with the original exponential
connecting homomorphism and the original singular comparison displayed. -/
theorem firstChernHom_apply (x : PicardExponential.PicardGroup) :
    firstChernHom x = ConstantSheafSingularComparison.threefoldIntegralSheafH2Equiv
      (PicardExponential.exponentialConnectingH1
        (HolomorphicPicard.LineBundle.isoClassCohomologyClass IF Space x)) := rfl

variable (V : Space → Type u)
    [∀ x, AddCommMonoid (V x)] [∀ x, Module ℂ (V x)]
    [∀ x, TopologicalSpace (V x)] [TopologicalSpace (TotalSpace ℂ V)]
    [FiberBundle ℂ V] [VectorBundle ℂ ℂ V] [ContMDiffVectorBundle ω ℂ V IF]

/-- The same actual singular Chern class for any original native fibre family. -/
def nativeFirstChernClass : SingularCohomology Space 2 :=
  PicardExponential.integerSheafH2Equiv (HolomorphicPicard.Chern.nativeFirstChernClass IF Space V)

/-- Literal evaluation on the original native unit cocycle and the
original normalized exponential extension; the final arrow is the proved
integral constant-sheaf--singular cohomology comparison. -/
theorem nativeFirstChernClass_eq_cocycle :
    nativeFirstChernClass V = ConstantSheafSingularComparison.threefoldIntegralSheafH2Equiv
      ((HolomorphicPicard.CechExtension.classOf (nativeCocycle IF Space V)
        (nativeCover_covers Space V)).comp (exponentialComplex_shortExact IF Space).extClass rfl) :=
  rfl

theorem nativeFirstChernClass_eq_connecting :
    nativeFirstChernClass V = PicardExponential.integerSheafH2Equiv
      (PicardExponential.exponentialConnectingH1 (HolomorphicPicard.nativeClass IF Space V)) := rfl

variable (W : Space → Type v)
    [∀ x, AddCommMonoid (W x)] [∀ x, Module ℂ (W x)]
    [∀ x, TopologicalSpace (W x)] [TopologicalSpace (TotalSpace ℂ W)]
    [FiberBundle ℂ W] [VectorBundle ℂ ℂ W] [ContMDiffVectorBundle ω ℂ W IF]

/-- Original native analytic fibre-linear isomorphisms preserve the actual class. -/
theorem nativeFirstChernClass_eq_of_iso (e : AnalyticBundleIso IF V W) :
    nativeFirstChernClass V = nativeFirstChernClass W :=
  congrArg PicardExponential.integerSheafH2Equiv
    (HolomorphicPicard.Chern.nativeFirstChernClass_eq_of_iso IF Space V W e)

/-- The actual class of a bundled original native line bundle. -/
def firstChernClass (L : HolomorphicPicard.LineBundle.{u} IF Space) : SingularCohomology Space 2 :=
  nativeFirstChernClass L.Fiber

@[simp] theorem firstChernClass_ofFamily :
    firstChernClass (HolomorphicPicard.LineBundle.ofFamily IF Space V) = nativeFirstChernClass V :=
  rfl

/-- The group homomorphism agrees with the class of each original bundle. -/
@[simp] theorem firstChernHom_toIsoClasses (L : HolomorphicPicard.LineBundle.{0} IF Space) :
    firstChernHom (HolomorphicPicard.LineBundle.toIsoClasses IF Space L) = firstChernClass L := rfl

theorem firstChernClass_tensorBundle (L : HolomorphicPicard.LineBundle.{u} IF Space)
    (K : HolomorphicPicard.LineBundle.{v} IF Space) :
    firstChernClass (HolomorphicPicard.LineBundle.tensorBundle IF Space L K) =
      firstChernClass L + firstChernClass K :=
  (congrArg PicardExponential.integerSheafH2Equiv
    (HolomorphicPicard.Chern.firstChernClass_tensorBundle IF Space L K)).trans
      (PicardExponential.integerSheafH2Equiv.map_add _ _)

theorem firstChernClass_dualBundle (L : HolomorphicPicard.LineBundle.{u} IF Space) :
    firstChernClass (HolomorphicPicard.LineBundle.dualBundle IF Space L) = -firstChernClass L :=
  (congrArg PicardExponential.integerSheafH2Equiv
    (HolomorphicPicard.Chern.firstChernClass_dualBundle IF Space L)).trans
      (PicardExponential.integerSheafH2Equiv.map_neg _)

theorem firstChernClass_trivialBundle :
    firstChernClass (HolomorphicPicard.LineBundle.trivialBundle IF Space) = 0 :=
  (congrArg PicardExponential.integerSheafH2Equiv
    (HolomorphicPicard.Chern.firstChernClass_trivialBundle IF Space)).trans
      PicardExponential.integerSheafH2Equiv.map_zero

theorem firstChernHom_add (x y : PicardExponential.PicardGroup) :
    firstChernHom (x + y) = firstChernHom x + firstChernHom y := map_add firstChernHom x y

theorem firstChernHom_zsmul (n : ℤ) (x : PicardExponential.PicardGroup) :
    firstChernHom (n • x) = n • firstChernHom x := map_zsmul firstChernHom n x

end Wikipedia.HopfProblem.SpecialPeriods.Threefold.LineBundleChern
