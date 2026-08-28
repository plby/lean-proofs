import Wikipedia.HopfProblem.ConstantSheafSingularComparisonPullbackExtBasic
import Wikipedia.HopfProblem.ConstantSheafSingularComparisonPullbackExtResolution

/-!
# Genuine Ext pullback agrees with the original global-section pullback

The actual finite-pushforward Ext comparison commutes with the native
acyclic-resolution comparison. Applying the existing naturality theorem
to the actual augmented pullback map therefore proves the global-section
square, without defining the native Ext map through singular cohomology.
-/

noncomputable section

open CategoryTheory

namespace Wikipedia.HopfProblem.ConstantSheafSingularComparison.PullbackExt

private theorem pullback_comparison {C : Type*} [Category C]
    {A B D E F : C} (a : A ⟶ B) (b : B ⟶ D) (e : D ⟶ E) (r : B ⟶ E)
    (u : A ⟶ D) (s : A ⟶ F) (c : F ⟶ E)
    (hab : a ≫ b = u) (hbr : b ≫ e = r) (hue : u ≫ e = s ≫ c) :
    a ≫ r = s ≫ c := by
  rw [← hbr, ← Category.assoc, hab, hue]

variable {X Y : TopCat.{0}} [CompactSpace X] [T2Space X]
  [CompactSpace Y] [T2Space Y] (f : X ⟶ Y)
  (hf : IsClosedMap f) (hfinite : ∀ y : Y, (f ⁻¹' {y}).Finite)
  (A : AddCommGrpCat.{0})

/-- The original native degree-one cohomology pullback commutes with
the actual resolution-to-global-cochain comparison. -/
theorem h1_global_naturality
    (hX : LocallyContractibleSpace X) (hY : LocallyContractibleSpace Y) :
    constantCohomologyPullback f hf hfinite A 1 ≫
      (constantSheafGlobalH1Iso X A hX).hom =
    (constantSheafGlobalH1Iso Y A hY).hom ≫
      HomologicalComplex.homologyMap (PullbackSheaf.globalSheafPullback f A) 1 := by
  let R := singularSheafResolution X A hX
  let S := singularSheafResolution Y A hY
  let P := PushforwardExt.pushforwardResolution f hf hfinite R
  let φ := resolutionPullback f hf hfinite A hX hY
  let : Subsingleton (CategoryTheory.Sheaf.H.{0} (R.K.X 0) 1) :=
    FineCochains.cochainSheaf_higher_subsingleton X A 0 0
  let : Subsingleton (CategoryTheory.Sheaf.H.{0} (S.K.X 0) 1) :=
    FineCochains.cochainSheaf_higher_subsingleton Y A 0 0
  let : Subsingleton (CategoryTheory.Sheaf.H.{0} (P.K.X 0) 1) :=
    PushforwardExt.pushforward_cohomology_subsingleton f hf hfinite (R.K.X 0) 1
  have hmap : φ.globalMap = PullbackSheaf.globalSheafPullback f A := by
    apply HomologicalComplex.Hom.ext
    funext n
    rfl
  have hnat : (CategoryTheory.Sheaf.functorH _ 1).map
      (PullbackSheaf.constantPullback f A) ≫ P.h1Iso.hom =
      S.h1Iso.hom ≫
        HomologicalComplex.homologyMap (PullbackSheaf.globalSheafPullback f A) 1 :=
    φ.h1Iso_naturality.trans
      (congrArg (fun g => S.h1Iso.hom ≫ HomologicalComplex.homologyMap g 1) hmap)
  exact pullback_comparison
    (constantCohomologyPullback f hf hfinite A 1)
    (PushforwardExt.forwardHom f hf hfinite R.F 1) P.h1Iso.hom R.h1Iso.hom
    ((CategoryTheory.Sheaf.functorH _ 1).map (PullbackSheaf.constantPullback f A))
    S.h1Iso.hom (HomologicalComplex.homologyMap (PullbackSheaf.globalSheafPullback f A) 1)
    (constantCohomologyPullback_forward f hf hfinite A 1)
    (PushforwardExt.h1_forward_native f hf hfinite R) hnat

/-- The same genuine global-cohomology square in degree two. All
acyclicity of the actual source, target, and pushforward terms is proved. -/
theorem h2_global_naturality
    (hX : LocallyContractibleSpace X) (hY : LocallyContractibleSpace Y) :
    constantCohomologyPullback f hf hfinite A 2 ≫
      (constantSheafGlobalH2Iso X A hX).hom =
    (constantSheafGlobalH2Iso Y A hY).hom ≫
      HomologicalComplex.homologyMap (PullbackSheaf.globalSheafPullback f A) 2 := by
  let R := singularSheafResolution X A hX
  let S := singularSheafResolution Y A hY
  let φ := resolutionPullback f hf hfinite A hX hY
  let : Subsingleton (CategoryTheory.Sheaf.H.{0} (R.K.X 0) 1) :=
    FineCochains.cochainSheaf_higher_subsingleton X A 0 0
  let : Subsingleton (CategoryTheory.Sheaf.H.{0} (R.K.X 0) 2) :=
    FineCochains.cochainSheaf_higher_subsingleton X A 0 1
  let : Subsingleton (CategoryTheory.Sheaf.H.{0} (R.K.X 1) 1) :=
    FineCochains.cochainSheaf_higher_subsingleton X A 1 0
  let : Subsingleton (CategoryTheory.Sheaf.H.{0} (S.K.X 0) 1) :=
    FineCochains.cochainSheaf_higher_subsingleton Y A 0 0
  let : Subsingleton (CategoryTheory.Sheaf.H.{0} (S.K.X 0) 2) :=
    FineCochains.cochainSheaf_higher_subsingleton Y A 0 1
  let : Subsingleton (CategoryTheory.Sheaf.H.{0} (S.K.X 1) 1) :=
    FineCochains.cochainSheaf_higher_subsingleton Y A 1 0
  have hn := resolution_h2_naturality f hf hfinite R S φ
    (constantCohomologyPullback f hf hfinite A 2)
    (constantCohomologyPullback_forward f hf hfinite A 2)
  have hmap : φ.globalMap = PullbackSheaf.globalSheafPullback f A := by
    apply HomologicalComplex.Hom.ext
    funext n
    rfl
  have hc := congrArg (fun g => HomologicalComplex.homologyMap g 2) hmap
  exact hn.trans (congrArg (fun g => S.h2Iso.hom ≫ g) hc)

end Wikipedia.HopfProblem.ConstantSheafSingularComparison.PullbackExt
