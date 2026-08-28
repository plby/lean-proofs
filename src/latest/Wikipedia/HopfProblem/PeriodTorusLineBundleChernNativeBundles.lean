import Wikipedia.HopfProblem.PeriodTorusLineBundleChernNativeClass

/-!
# The genuine Chern map on native bundles and their actual isomorphism classes

The original native bundle wrapper has no characteristic-class field.
Its Chern map uses the now-proved analytic presentation theorem and the
native boundary-winding construction. It descends to the quotient by
actual analytic fibre-linear bundle isomorphisms.
-/

noncomputable section

namespace Wikipedia.HopfProblem.PeriodTorusLineBundle.ChernNative.NativeLineBundle

open PeriodTorusAppellHumbert PeriodTorusLineBundleClassificationNative
open SingularCohomologyFree

universe u

variable {p : PeriodDomain}

/-- The actual winding-defined first Chern class of a bundled original native line bundle. -/
def chernClass (V : NativeLineBundle.{u} p) : SingularCohomology p.Torus 2 :=
  ChernNative.firstChernClass p V.Fiber

theorem isFirstChernClass_chernClass (V : NativeLineBundle.{u} p) :
    IsFirstChernClass V.Fiber V.chernClass :=
  ChernNative.isFirstChernClass p V.Fiber

@[simp] theorem chernClass_ofFactor (F : FactorOfAutomorphy p) :
    (ofFactor p F).chernClass = Chern.firstChernClass F :=
  ChernNative.firstChernClass_factor p F

/-- This equality is induced by a genuine analytic isomorphism of original total spaces. -/
theorem chernClass_eq_of_iso {V W : NativeLineBundle.{u} p}
    (e : AnalyticBundleIso (modelWithCornersSelf ℂ ComplexPlane₂) V.Fiber W.Fiber) :
    V.chernClass = W.chernClass :=
  ChernNative.firstChernClass_bundleIso p V.Fiber W.Fiber e

/-- The genuine Chern class descends to actual native analytic isomorphism classes. -/
def isoClassChernClass (p : PeriodDomain) : IsoClasses.{u} p → SingularCohomology p.Torus 2 :=
  Quotient.lift chernClass (fun _ _ ⟨e⟩ => chernClass_eq_of_iso e)

@[simp] theorem isoClassChernClass_toIsoClasses (V : NativeLineBundle.{u} p) :
    isoClassChernClass p (toIsoClasses p V) = V.chernClass := rfl

/-- Taking actual bundle isomorphism classes changes no realized native cohomology class. -/
theorem range_isoClassChernClass (p : PeriodDomain) :
    Set.range (isoClassChernClass.{u} p) =
      Set.range (chernClass (p := p) : NativeLineBundle.{u} p → _) := by
  ext a
  constructor
  · rintro ⟨q, rfl⟩
    exact Quotient.inductionOn q (fun V => ⟨V, rfl⟩)
  · rintro ⟨V, rfl⟩
    exact ⟨toIsoClasses p V, rfl⟩

end Wikipedia.HopfProblem.PeriodTorusLineBundle.ChernNative.NativeLineBundle
