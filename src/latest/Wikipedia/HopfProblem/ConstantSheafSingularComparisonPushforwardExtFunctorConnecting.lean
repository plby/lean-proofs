import Wikipedia.HopfProblem.ConstantSheafSingularComparisonPushforwardExtFunctorBasic

/-!
# Connecting maps commute with the native exact-functor Ext map

The two short exact sequences use the actual kernel comparison, not
an identification of their middle kernels by definition.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian

namespace Wikipedia.HopfProblem.ConstantSheafSingularComparison.PushforwardExtFunctor

open CuspNormalization.SheafCohomologyResolution

universe v u v' u'

variable {C : Type u} [Category.{v} C] [Abelian C] [HasExt.{0} C]
  {D : Type u'} [Category.{v'} D] [Abelian D] [HasExt.{0} D]
  (G : C ⥤ D) [G.Additive] [PreservesFiniteLimits G] [PreservesFiniteColimits G]
  {V : C} {A : D} (η : A ⟶ G.obj V)

/-- Combine the native exact-functor comparison of connecting
classes with the native naturality for a map of short exact sequences. -/
theorem connecting_comparison_apply {S : ShortComplex C} {T : ShortComplex D}
    (hS : S.ShortExact) (hT : T.ShortExact) (φ : S.map G ⟶ T) (n : ℕ)
    (e : Ext.{0} V S.X₃ n) :
    connecting A hT n
        ((extFunctorObj A n).map φ.τ₃ (comparisonHom G η S.X₃ n e)) =
      (extFunctorObj A (n + 1)).map φ.τ₁
        (comparisonHom G η S.X₁ (n + 1) (connecting V hS n e)) := by
  exact (connecting_naturality A (hS.map_of_exact G) hT φ n
    (comparisonHom G η S.X₃ n e)).trans
      (congrArg ((extFunctorObj A (n + 1)).map φ.τ₁)
        (CuspNormalization.SheafCohomologyFinitePushforward.ExtComparison.comparison_connecting
          G η hS e).symm)

variable (R : AugmentedResolution C)

/-- The first connecting map respects the actual comparison on the
intermediate kernel, in every degree. -/
theorem connectingFirst_apply (n : ℕ) (e : Ext.{0} V R.K n) :
    connecting A (mappedResolution G R).first_shortExact n
        (kernelExtComparison G η R n e) =
      comparisonHom G η R.F (n + 1) (connecting V R.first_shortExact n e) :=
  (connecting_comparison_apply G η R.first_shortExact
    (mappedResolution G R).first_shortExact (firstMap G R) n e).trans
      (Ext.comp_mk₀_id _)

@[reassoc] theorem connectingFirst_naturality (n : ℕ) :
    kernelExtComparison G η R n ≫
        AddCommGrpCat.ofHom (connecting A (mappedResolution G R).first_shortExact n) =
      AddCommGrpCat.ofHom (connecting V R.first_shortExact n) ≫
        comparisonHom G η R.F (n + 1) := by
  ext e
  exact connectingFirst_apply G η R n e

/-- The second connecting map lands in the compared intermediate
kernel and commutes with the same native Ext comparison. -/
theorem connectingSecond_apply (n : ℕ) (e : Ext.{0} V R.complex.X₃ n) :
    connecting A (mappedResolution G R).second_shortExact n
        (comparisonHom G η R.complex.X₃ n e) =
      kernelExtComparison G η R (n + 1) (connecting V R.second_shortExact n e) :=
  (congrArg (connecting A (mappedResolution G R).second_shortExact n)
    (Ext.comp_mk₀_id (comparisonHom G η R.complex.X₃ n e)).symm).trans
      (connecting_comparison_apply G η R.second_shortExact
        (mappedResolution G R).second_shortExact (secondMap G R) n e)

@[reassoc] theorem connectingSecond_naturality (n : ℕ) :
    comparisonHom G η R.complex.X₃ n ≫
        AddCommGrpCat.ofHom (connecting A (mappedResolution G R).second_shortExact n) =
      AddCommGrpCat.ofHom (connecting V R.second_shortExact n) ≫
        kernelExtComparison G η R (n + 1) := by
  ext e
  exact connectingSecond_apply G η R n e

/-- Naturality of the degree-one connecting representatives. -/
@[reassoc] theorem connectingOne_naturality :
    kernelExtComparison G η R 0 ≫
        AddCommGrpCat.ofHom (connecting A (mappedResolution G R).first_shortExact 0) =
      AddCommGrpCat.ofHom (connecting V R.first_shortExact 0) ≫
        comparisonHom G η R.F 1 :=
  connectingFirst_naturality G η R 0

/-- Naturality of the actual composite connecting representatives of
degree-two Ext. -/
@[reassoc] theorem connectingTwo_naturality :
    comparisonHom G η R.complex.X₃ 0 ≫
        AddCommGrpCat.ofHom ((mappedResolution G R).connectingTwo A) =
      AddCommGrpCat.ofHom (R.connectingTwo V) ≫ comparisonHom G η R.F 2 := by
  ext e
  exact (congrArg (connecting A (mappedResolution G R).first_shortExact 1)
    (connectingSecond_apply G η R 0 e)).trans
      (connectingFirst_apply G η R 1 (connecting V R.second_shortExact 0 e))

end Wikipedia.HopfProblem.ConstantSheafSingularComparison.PushforwardExtFunctor
