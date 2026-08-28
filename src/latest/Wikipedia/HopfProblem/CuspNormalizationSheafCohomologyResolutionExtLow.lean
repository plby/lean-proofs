import Wikipedia.HopfProblem.CuspNormalizationSheafCohomologyResolutionData
import Wikipedia.HopfProblem.CuspNormalizationSheafCohomologyResolutionHomology

/-!
# Actual low-degree `Ext` of a length-two resolution

The long exact sequences identify degree one with the homology of the
degree-zero section complex and degree two with its actual cokernel.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian

namespace Wikipedia.HopfProblem.CuspNormalization.SheafCohomologyResolution

universe w v u

variable {C : Type u} [Category.{v} C] [Abelian C] [HasExt.{w} C]

/-- The actual two arrows immediately preceding a connecting target. -/
def connectingComplex (P : C) {S : ShortComplex C} (hS : S.ShortExact) (n : ℕ) :
    ShortComplex AddCommGrpCat.{w} :=
  ShortComplex.mk ((extFunctorObj P n).map S.g)
    (AddCommGrpCat.ofHom (connecting P hS n)) (by
      ext x
      exact (connecting_exact P hS n _).mpr ⟨x, rfl⟩)

theorem connectingComplex_exact (P : C) {S : ShortComplex C}
    (hS : S.ShortExact) (n : ℕ) : (connectingComplex P hS n).Exact :=
  Ext.covariant_sequence_exact₃' P hS n (n + 1) rfl

namespace AugmentedResolution

variable (R : AugmentedResolution C) (P : C)

/-- The actual complex of degree-zero `Ext` groups. -/
abbrev extZeroComplex : ShortComplex AddCommGrpCat.{w} :=
  R.complex.map (extFunctorObj P 0)

/-- Genuine degree one is left homology data for the degree-zero
section complex. Only degree-one acyclicity of the first term is used. -/
def extOneHomologyData [Subsingleton (Ext P R.complex.X₁ 1)] :
    (R.extZeroComplex P).LeftHomologyData := by
  let i : AddCommGrpCat.of (Ext P R.K 0) ⟶ (R.extZeroComplex P).X₂ :=
    (extFunctorObj P 0).map (kernel.ι R.complex.g)
  let a : (R.extZeroComplex P).X₁ ⟶ AddCommGrpCat.of (Ext P R.K 0) :=
    (extFunctorObj P 0).map R.toK
  let p : AddCommGrpCat.of (Ext P R.K 0) ⟶ AddCommGrpCat.of (Ext P R.F 1) :=
    AddCommGrpCat.ofHom (connecting P R.first_shortExact 0)
  have hiMono : Mono i := Ext.mono_postcomp_mk₀_of_mono P (kernel.ι R.complex.g)
  have hpEpi : Epi p := (AddCommGrpCat.epi_iff_surjective _).mpr
    (connecting_surjective P R.first_shortExact 0)
  have wi : i ≫ (R.extZeroComplex P).g = 0 := (R.second.map (extFunctorObj P 0)).zero
  have wa : a ≫ i = (R.extZeroComplex P).f := by
    change (extFunctorObj P 0).map R.toK ≫
      (extFunctorObj P 0).map (kernel.ι R.complex.g) = (extFunctorObj P 0).map R.complex.f
    rw [← Functor.map_comp, R.toK_ι]
  have wp : a ≫ p = 0 := (connectingComplex P R.first_shortExact 0).zero
  exact @leftHomologyDataOfExact AddCommGrpCat.{w} _ _
    (R.extZeroComplex P) (AddCommGrpCat.of (Ext P R.K 0)) (AddCommGrpCat.of (Ext P R.F 1))
    i a p wi wa wp
    (Ext.covariant_sequence_exact₂' P R.second_shortExact 0)
    (connectingComplex_exact P R.first_shortExact 0) hiMono hpEpi

/-- Genuine degree-one `Ext` equals Mathlib's actual homology of
the degree-zero section complex. -/
def extOneIso [Subsingleton (Ext P R.complex.X₁ 1)] :
    AddCommGrpCat.of (Ext P R.F 1) ≅ (R.extZeroComplex P).homology :=
  (R.extOneHomologyData P).homologyIso.symm

/-- The degree-one comparison sends an actual connecting class
to the corresponding actual homology class. -/
theorem extOneIso_connecting [Subsingleton (Ext P R.complex.X₁ 1)] :
    AddCommGrpCat.ofHom (connecting P R.first_shortExact 0) ≫ (R.extOneIso P).hom =
      (R.extOneHomologyData P).cyclesIso.inv ≫ (R.extZeroComplex P).homologyπ :=
  (R.extOneHomologyData P).π_comp_homologyIso_inv

/-- The actual composite of the two connecting maps in degrees zero
and one. Its codomain is the genuine degree-two `Ext` group. -/
def connectingTwo : Ext P R.complex.X₃ 0 →+ Ext P R.F 2 :=
  (connecting P R.first_shortExact 1).comp (connecting P R.second_shortExact 0)

@[simp] theorem connectingTwo_apply (x : Ext P R.complex.X₃ 0) :
    R.connectingTwo P x =
      connecting P R.first_shortExact 1 (connecting P R.second_shortExact 0 x) := rfl

theorem connectingTwo_surjective [Subsingleton (Ext P R.complex.X₁ 2)]
    [Subsingleton (Ext P R.complex.X₂ 1)] : Function.Surjective (R.connectingTwo P) :=
  (connecting_surjective P R.first_shortExact 1).comp
    (connecting_surjective P R.second_shortExact 0)

theorem connectingTwo_exact [Subsingleton (Ext P R.complex.X₁ 1)] :
    Function.Exact ((extFunctorObj P 0).map R.complex.g) (R.connectingTwo P) := by
  intro x
  change Ext P R.complex.X₃ 0 at x
  change connecting P R.first_shortExact 1 (connecting P R.second_shortExact 0 x) = 0 ↔ _
  rw [← map_zero (connecting P R.first_shortExact 1),
    (connecting_injective P R.first_shortExact 1).eq_iff]
  exact connecting_exact P R.second_shortExact 0 x

/-- The genuine degree-two target is a cokernel of the last
degree-zero section map. -/
def extTwoCokernelComplex : ShortComplex AddCommGrpCat.{w} :=
  ShortComplex.mk ((extFunctorObj P 0).map R.complex.g)
    (AddCommGrpCat.ofHom (R.connectingTwo P)) (by
      ext x
      change connecting P R.first_shortExact 1
        (connecting P R.second_shortExact 0
          ((extFunctorObj P 0).map R.complex.g x)) = 0
      have h : connecting P R.second_shortExact 0
          ((extFunctorObj P 0).map R.complex.g x) = 0 :=
        (connecting_exact P R.second_shortExact 0 _).mpr ⟨x, rfl⟩
      rw [h, map_zero])

theorem extTwoCokernelComplex_exact [Subsingleton (Ext P R.complex.X₁ 1)] :
    (R.extTwoCokernelComplex P).Exact :=
  (ShortComplex.ab_exact_iff_function_exact _).mpr (R.connectingTwo_exact P)

/-- The genuine degree-two `Ext` comparison with the actual categorical
cokernel of the last degree-zero section map. -/
def extTwoIso [Subsingleton (Ext P R.complex.X₁ 1)]
    [Subsingleton (Ext P R.complex.X₁ 2)] [Subsingleton (Ext P R.complex.X₂ 1)] :
    AddCommGrpCat.of (Ext P R.F 2) ≅ cokernel ((R.extZeroComplex P).g) := by
  have : Epi (R.extTwoCokernelComplex P).g :=
    (AddCommGrpCat.epi_iff_surjective _).mpr (R.connectingTwo_surjective P)
  exact IsColimit.coconePointUniqueUpToIso (R.extTwoCokernelComplex_exact P).gIsCokernel
    (colimit.isColimit (parallelPair ((R.extZeroComplex P).g) 0))

end AugmentedResolution

end Wikipedia.HopfProblem.CuspNormalization.SheafCohomologyResolution
