import Wikipedia.HopfProblem.HolomorphicPicardTensorClass

/-!
# Tensor and dual operations on original native isomorphism classes

The operations are defined by the actual bundles constructed from the
original native transition functions. The proved classification theorem
shows that these constructions respect actual analytic bundle isomorphisms.
The operations are not pulled back from cohomology along an equivalence.
-/

noncomputable section

namespace Wikipedia.HopfProblem.HolomorphicPicard.LineBundle

open PeriodTorusLineBundleClassificationNative

universe u v

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [TopologicalSpace H] (I : ModelWithCorners ℂ E H)
    (M : Type) [TopologicalSpace M] [ChartedSpace H M]

/-- The actual tensor constructions of isomorphic original bundles are
themselves analytically fibre-linearly isomorphic. -/
theorem tensorBundle_congr (V V' : LineBundle.{u} I M) (W W' : LineBundle.{v} I M)
    (hV : Nonempty (AnalyticBundleIso I V.Fiber V'.Fiber))
    (hW : Nonempty (AnalyticBundleIso I W.Fiber W'.Fiber)) :
    Nonempty (AnalyticBundleIso I (tensorBundle I M V W).Fiber
      (tensorBundle I M V' W').Fiber) := by
  apply (cohomologyClass_eq_iff_nonempty_iso I M _ _).mp
  rw [cohomologyClass_tensorBundle, cohomologyClass_tensorBundle]
  exact congrArg₂ (· + ·)
    ((cohomologyClass_eq_iff_nonempty_iso I M V V').mpr hV)
    ((cohomologyClass_eq_iff_nonempty_iso I M W W').mpr hW)

/-- Actual dualization respects genuine analytic fibre-linear isomorphisms. -/
theorem dualBundle_congr (V V' : LineBundle.{u} I M)
    (hV : Nonempty (AnalyticBundleIso I V.Fiber V'.Fiber)) :
    Nonempty (AnalyticBundleIso I (dualBundle I M V).Fiber (dualBundle I M V').Fiber) := by
  apply (cohomologyClass_eq_iff_nonempty_iso I M _ _).mp
  rw [cohomologyClass_dualBundle, cohomologyClass_dualBundle]
  exact congrArg Neg.neg ((cohomologyClass_eq_iff_nonempty_iso I M V V').mpr hV)

/-- Tensor product, descended from the actual native bundle construction. -/
def tensorIsoClasses : IsoClasses.{0} I M → IsoClasses.{0} I M → IsoClasses.{0} I M :=
  Quotient.map₂ (sa := isoSetoid I M) (sb := isoSetoid I M) (sc := isoSetoid I M)
    (tensorBundle I M)
    (fun {V V'} hV {W W'} hW => tensorBundle_congr I M V V' W W' hV hW)

/-- Dualization, descended from the actual native inverse-transition bundle. -/
def dualIsoClasses : IsoClasses.{0} I M → IsoClasses.{0} I M :=
  Quotient.map (sa := isoSetoid I M) (sb := isoSetoid I M) (dualBundle I M)
    (fun {V V'} hV => dualBundle_congr I M V V' hV)

instance isoClassesAdd : Add (IsoClasses.{0} I M) := ⟨tensorIsoClasses I M⟩
instance isoClassesZero : Zero (IsoClasses.{0} I M) := ⟨toIsoClasses I M (trivialBundle I M)⟩
instance isoClassesNeg : Neg (IsoClasses.{0} I M) := ⟨dualIsoClasses I M⟩

/-- Addition is definitionally the class of the original tensor construction. -/
@[simp] theorem toIsoClasses_tensorBundle (V W : LineBundle.{0} I M) :
    toIsoClasses I M (tensorBundle I M V W) = toIsoClasses I M V + toIsoClasses I M W := rfl

/-- Negation is definitionally the class of the original dual construction. -/
@[simp] theorem toIsoClasses_dualBundle (V : LineBundle.{0} I M) :
    toIsoClasses I M (dualBundle I M V) = -toIsoClasses I M V := rfl

/-- The zero class is the original native trivial bundle. -/
@[simp] theorem toIsoClasses_trivialBundle : toIsoClasses I M (trivialBundle I M) = 0 := rfl

theorem isoClassCohomologyClass_add (x y : IsoClasses.{0} I M) :
    isoClassCohomologyClass I M (x + y) =
      isoClassCohomologyClass I M x + isoClassCohomologyClass I M y := by
  refine Quotient.inductionOn₂ x y ?_
  intro V W
  exact cohomologyClass_tensorBundle I M V W

theorem isoClassCohomologyClass_neg (x : IsoClasses.{0} I M) :
    isoClassCohomologyClass I M (-x) = -isoClassCohomologyClass I M x := by
  refine Quotient.inductionOn x ?_
  intro V
  exact cohomologyClass_dualBundle I M V

theorem isoClassCohomologyClass_zero : isoClassCohomologyClass I M (0 : IsoClasses.{0} I M) = 0 :=
  cohomologyClass_trivialBundle I M

end Wikipedia.HopfProblem.HolomorphicPicard.LineBundle
