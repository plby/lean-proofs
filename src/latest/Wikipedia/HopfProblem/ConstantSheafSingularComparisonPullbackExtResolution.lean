import Wikipedia.HopfProblem.ConstantSheafSingularComparisonPushforwardExt

/-!
# Native degree-two comparison for an actual pushed resolution

Naturality of the same-base augmented resolution comparison and the
proved native finite-pushforward comparison determine the global
cohomology square. This lemma keeps the resolutions abstract; the
singular cochain sheaf resolution is supplied by the application.
-/

noncomputable section

open CategoryTheory

namespace Wikipedia.HopfProblem.ConstantSheafSingularComparison.PullbackExt

private theorem resolution_comparison {C : Type*} [Category C]
    {A B D E F : C} (a : A ⟶ B) (b : B ⟶ D) (e : D ⟶ E) (r : B ⟶ E)
    (u : A ⟶ D) (s : A ⟶ F) (c : F ⟶ E)
    (hab : a ≫ b = u) (hbr : b ≫ e = r) (hue : u ≫ e = s ≫ c) :
    a ≫ r = s ≫ c := by
  rw [← hbr, ← Category.assoc, hab, hue]

variable {X Y : TopCat.{0}} [T2Space X] (f : X ⟶ Y)
  (hf : IsClosedMap f) (hfinite : ∀ y : Y, (f ⁻¹' {y}).Finite)
  (R : LowExt.CochainResolution (TopCat.Sheaf AddCommGrpCat.{0} X))
  (S : LowExt.CochainResolution (TopCat.Sheaf AddCommGrpCat.{0} Y))

/-- A genuine native Ext map into an actual finite pushed resolution
commutes with the original degree-two resolution isomorphisms. -/
theorem resolution_h2_naturality
    [Subsingleton (CategoryTheory.Sheaf.H.{0} (R.K.X 0) 1)]
    [Subsingleton (CategoryTheory.Sheaf.H.{0} (R.K.X 0) 2)]
    [Subsingleton (CategoryTheory.Sheaf.H.{0} (R.K.X 1) 1)]
    [Subsingleton (CategoryTheory.Sheaf.H.{0} (S.K.X 0) 1)]
    [Subsingleton (CategoryTheory.Sheaf.H.{0} (S.K.X 0) 2)]
    [Subsingleton (CategoryTheory.Sheaf.H.{0} (S.K.X 1) 1)]
    (φ : S.Hom (PushforwardExt.pushforwardResolution f hf hfinite R))
    (a : AddCommGrpCat.of (CategoryTheory.Sheaf.H.{0} S.F 2) ⟶
      AddCommGrpCat.of (CategoryTheory.Sheaf.H.{0} R.F 2))
    (ha : a ≫ PushforwardExt.forwardHom f hf hfinite R.F 2 =
      (CategoryTheory.Sheaf.functorH _ 2).map φ.augmentation) :
    a ≫ R.h2Iso.hom =
      S.h2Iso.hom ≫ HomologicalComplex.homologyMap φ.globalMap 2 := by
  let P := PushforwardExt.pushforwardResolution f hf hfinite R
  let : Subsingleton (CategoryTheory.Sheaf.H.{0} (P.K.X 0) 1) :=
    PushforwardExt.pushforward_cohomology_subsingleton f hf hfinite (R.K.X 0) 1
  let : Subsingleton (CategoryTheory.Sheaf.H.{0} (P.K.X 0) 2) :=
    PushforwardExt.pushforward_cohomology_subsingleton f hf hfinite (R.K.X 0) 2
  let : Subsingleton (CategoryTheory.Sheaf.H.{0} (P.K.X 1) 1) :=
    PushforwardExt.pushforward_cohomology_subsingleton f hf hfinite (R.K.X 1) 1
  exact resolution_comparison a
    (PushforwardExt.forwardHom f hf hfinite R.F 2) P.h2Iso.hom R.h2Iso.hom
    ((CategoryTheory.Sheaf.functorH _ 2).map φ.augmentation)
    S.h2Iso.hom (HomologicalComplex.homologyMap φ.globalMap 2)
    ha (PushforwardExt.h2_forward_native f hf hfinite R) φ.h2Iso_naturality

end Wikipedia.HopfProblem.ConstantSheafSingularComparison.PullbackExt
