import Wikipedia.HopfProblem.HolomorphicPicardGroupBasic
import Wikipedia.HopfProblem.HolomorphicPicardTensorBundlesTensor
import Wikipedia.HopfProblem.HolomorphicPicardTensorBundlesDual

/-!
# The genuine native Picard group and its additive cohomology classification

The underlying objects are arbitrary original native holomorphic line
bundles modulo actual analytic fibre-linear isomorphisms. Addition was
defined from their actual tensor transitions, the inverse from their
actual dual transitions, and zero from the native trivial bundle. The
proved compatibility with genuine derived cohomology supplies the group
laws and upgrades the already proved set classification to an additive
equivalence. In particular, the concrete bundle operations have their
expected actual analytic isomorphisms.
-/

noncomputable section

namespace Wikipedia.HopfProblem.HolomorphicPicard.LineBundle

open HolomorphicExponentialSheaf PeriodTorusLineBundleClassificationNative

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [TopologicalSpace H] (I : ModelWithCorners ℂ E H)
    (M : Type) [TopologicalSpace M] [ChartedSpace H M]

/-- The native Picard group: the operations are the separately constructed
tensor, dual, and trivial native bundles, not transported operations. -/
instance isoClassesAddCommGroup : AddCommGroup (IsoClasses.{0} I M) where
  add_assoc x y z := by
    apply isoClassCohomologyClass_injective I M
    simp only [isoClassCohomologyClass_add, add_assoc]
  zero_add x := by
    apply isoClassCohomologyClass_injective I M
    simp only [isoClassCohomologyClass_add, isoClassCohomologyClass_zero, zero_add]
  add_zero x := by
    apply isoClassCohomologyClass_injective I M
    simp only [isoClassCohomologyClass_add, isoClassCohomologyClass_zero, add_zero]
  neg_add_cancel x := by
    apply isoClassCohomologyClass_injective I M
    simp only [isoClassCohomologyClass_add, isoClassCohomologyClass_neg,
      isoClassCohomologyClass_zero, neg_add_cancel]
  add_comm x y := by
    apply isoClassCohomologyClass_injective I M
    simp only [isoClassCohomologyClass_add, add_comm]
  nsmul := nsmulRec
  zsmul := zsmulRec

/-- Original holomorphic line bundles under actual tensor product are
additively classified by genuine derived cohomology of the original unit
sheaf. The forward map is the already constructed native cocycle class. -/
def classificationAddEquiv : IsoClasses.{0} I M ≃+
    CategoryTheory.Sheaf.H.{0} (unitsSheaf I M) 1 where
  toEquiv := classificationEquiv I M
  map_add' := isoClassCohomologyClass_add I M

@[simp] theorem classificationAddEquiv_toEquiv :
    (classificationAddEquiv I M).toEquiv = classificationEquiv I M := rfl

@[simp] theorem classificationAddEquiv_apply (x : IsoClasses.{0} I M) :
    classificationAddEquiv I M x = isoClassCohomologyClass I M x := rfl

@[simp] theorem classificationAddEquiv_toIsoClasses (V : LineBundle.{0} I M) :
    classificationAddEquiv I M (toIsoClasses I M V) = cohomologyClass I M V := rfl

/-- Vanishing of the genuine class gives an actual analytic fibre-linear
trivialization of the original native bundle. -/
theorem cohomologyClass_eq_zero_iff_trivial (V : LineBundle.{0} I M) :
    cohomologyClass I M V = 0 ↔
      Nonempty (AnalyticBundleIso I V.Fiber (Bundle.Trivial M ℂ)) := by
  rw [← cohomologyClass_trivialBundle I M]
  exact cohomologyClass_eq_iff_nonempty_iso I M V (trivialBundle I M)

theorem toIsoClasses_eq_zero_iff_trivial (V : LineBundle.{0} I M) :
    toIsoClasses I M V = 0 ↔
      Nonempty (AnalyticBundleIso I V.Fiber (Bundle.Trivial M ℂ)) :=
  toIsoClasses_eq_iff I M V (trivialBundle I M)

/-- Associativity is realized by an analytic isomorphism of the actual
constructed tensor bundles. -/
theorem nonempty_tensorBundle_assoc (U V W : LineBundle.{0} I M) :
    Nonempty (AnalyticBundleIso I (tensorBundle I M (tensorBundle I M U V) W).Fiber
      (tensorBundle I M U (tensorBundle I M V W)).Fiber) := by
  apply (toIsoClasses_eq_iff I M _ _).mp
  simp only [toIsoClasses_tensorBundle, add_assoc]

theorem nonempty_tensorBundle_comm (V W : LineBundle.{0} I M) :
    Nonempty (AnalyticBundleIso I (tensorBundle I M V W).Fiber
      (tensorBundle I M W V).Fiber) := by
  apply (toIsoClasses_eq_iff I M _ _).mp
  simp only [toIsoClasses_tensorBundle, add_comm]

theorem nonempty_trivial_tensorBundle (V : LineBundle.{0} I M) :
    Nonempty (AnalyticBundleIso I (tensorBundle I M (trivialBundle I M) V).Fiber V.Fiber) := by
  apply (toIsoClasses_eq_iff I M _ _).mp
  simp only [toIsoClasses_tensorBundle, toIsoClasses_trivialBundle, zero_add]

theorem nonempty_tensorBundle_trivial (V : LineBundle.{0} I M) :
    Nonempty (AnalyticBundleIso I (tensorBundle I M V (trivialBundle I M)).Fiber V.Fiber) := by
  apply (toIsoClasses_eq_iff I M _ _).mp
  simp only [toIsoClasses_tensorBundle, toIsoClasses_trivialBundle, add_zero]

/-- Tensoring the genuine dual with the original bundle is analytically
trivial as a native holomorphic line bundle. -/
theorem nonempty_dual_tensorBundle (V : LineBundle.{0} I M) :
    Nonempty (AnalyticBundleIso I (tensorBundle I M (dualBundle I M V) V).Fiber
      (Bundle.Trivial M ℂ)) := by
  apply (toIsoClasses_eq_zero_iff_trivial I M _).mp
  simp only [toIsoClasses_tensorBundle, toIsoClasses_dualBundle, neg_add_cancel]

theorem nonempty_tensorBundle_dual (V : LineBundle.{0} I M) :
    Nonempty (AnalyticBundleIso I (tensorBundle I M V (dualBundle I M V)).Fiber
      (Bundle.Trivial M ℂ)) := by
  apply (toIsoClasses_eq_zero_iff_trivial I M _).mp
  simp only [toIsoClasses_tensorBundle, toIsoClasses_dualBundle, add_neg_cancel]

theorem nonempty_doubleDualBundle (V : LineBundle.{0} I M) :
    Nonempty (AnalyticBundleIso I (dualBundle I M (dualBundle I M V)).Fiber V.Fiber) := by
  apply (toIsoClasses_eq_iff I M _ _).mp
  simp only [toIsoClasses_dualBundle, neg_neg]

end Wikipedia.HopfProblem.HolomorphicPicard.LineBundle
