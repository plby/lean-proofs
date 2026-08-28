import Wikipedia.HopfProblem.CuspNormalizationSheafCohomologyResolutionExtLow
import Mathlib.Algebra.Homology.DerivedCategory.Ext.EnoughInjectives

/-!
# The exact low-degree sequence of an augmented complex

For an actual exact sequence `0 → F → J → Z → H → 0`, with `J`
injective, the native Ext long exact sequences give two exact short
complexes through the cokernel of `Hom(A,J) → Hom(A,Z)`.  We first use
degree-zero Ext for these Hom groups, retaining the genuine connecting
maps and native opcycles throughout.
-/

noncomputable section

open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits
open Wikipedia.HopfProblem.CuspNormalization.SheafCohomologyResolution

namespace Wikipedia.HopfProblem.SheafLerayLowDegrees.Abstract.Core

universe u

variable {C : Type u} [Category.{0} C] [Abelian C]

/-- A sequence beginning in a middle term descends to its actual opcycles. -/
def opcyclesRightComplex (S : ShortComplex C) {W : C} (h : S.X₃ ⟶ W)
    (hw : S.g ≫ h = 0) : ShortComplex C :=
  ShortComplex.mk S.fromOpcycles h (by
    rw [← cancel_epi S.pOpcycles, ← Category.assoc, S.p_fromOpcycles, hw, comp_zero])

theorem opcyclesRightComplex_exact (S : ShortComplex C) {W : C} (h : S.X₃ ⟶ W)
    (hw : S.g ≫ h = 0) (he : (ShortComplex.mk S.g h hw).Exact) :
    (opcyclesRightComplex S h hw).Exact := by
  let φ : ShortComplex.mk S.g h hw ⟶ opcyclesRightComplex S h hw :=
    { τ₁ := S.pOpcycles
      τ₂ := 𝟙 _
      τ₃ := 𝟙 _
      comm₁₂ := by simp [opcyclesRightComplex]
      comm₂₃ := by simp [opcyclesRightComplex] }
  have : Epi φ.τ₁ := inferInstanceAs (Epi S.pOpcycles)
  have : IsIso φ.τ₂ := inferInstanceAs (IsIso (𝟙 S.X₃))
  have : Mono φ.τ₃ := inferInstanceAs (Mono (𝟙 W))
  exact (ShortComplex.exact_iff_of_epi_of_isIso_of_mono φ).mp he

variable [HasExt.{0} C] (A : C) (R : AugmentedResolution C)

/-- The actual cokernel of the degree-zero section differential. -/
abbrev middle : AddCommGrpCat := (R.extZeroComplex A).opcycles

/-- The edge map is induced by the last arrow of the augmented complex. -/
def edgeMap : middle A R ⟶ AddCommGrpCat.of (Ext A R.complex.X₃ 0) :=
  (R.extZeroComplex A).fromOpcycles

/-- The transgression is the composite of two genuine Ext connecting maps. -/
def transgression : AddCommGrpCat.of (Ext A R.complex.X₃ 0) ⟶
    AddCommGrpCat.of (Ext A R.F 2) :=
  AddCommGrpCat.ofHom (R.connectingTwo A)

theorem edgeMap_transgression : edgeMap A R ≫ transgression A R = 0 :=
  (opcyclesRightComplex (R.extZeroComplex A) (transgression A R)
    (R.extTwoCokernelComplex A).zero).zero

/-- The right half of the low-degree sequence, before identifying degree-zero Ext with Hom. -/
def secondComplex : ShortComplex AddCommGrpCat :=
  ShortComplex.mk (edgeMap A R) (transgression A R) (edgeMap_transgression A R)

variable [Injective R.complex.X₁]

/-- Ext in degree one embeds in the actual opcycles of the section complex. -/
def firstMap : AddCommGrpCat.of (Ext A R.F 1) ⟶ middle A R := by
  letI := Ext.subsingleton_of_injective A R.complex.X₁ 0
  exact (R.extOneIso A).hom ≫ (R.extZeroComplex A).homologyι

theorem firstMap_edgeMap : firstMap A R ≫ edgeMap A R = 0 := by
  let := Ext.subsingleton_of_injective A R.complex.X₁ 0
  change ((R.extOneIso A).hom ≫ (R.extZeroComplex A).homologyι) ≫
    (R.extZeroComplex A).fromOpcycles = 0
  rw [Category.assoc, ShortComplex.homologyι_comp_fromOpcycles, comp_zero]

/-- The left half of the low-degree sequence. -/
def firstComplex : ShortComplex AddCommGrpCat :=
  ShortComplex.mk (firstMap A R) (edgeMap A R) (firstMap_edgeMap A R)

theorem firstMap_mono : Mono (firstMap A R) := by
  let := Ext.subsingleton_of_injective A R.complex.X₁ 0
  change Mono ((R.extOneIso A).hom ≫ (R.extZeroComplex A).homologyι)
  infer_instance

theorem firstComplex_exact : (firstComplex A R).Exact := by
  let := Ext.subsingleton_of_injective A R.complex.X₁ 0
  let S := R.extZeroComplex A
  let T := ShortComplex.mk S.homologyι S.fromOpcycles S.homologyι_comp_fromOpcycles
  have hT : T.Exact := T.exact_of_f_is_kernel S.homologyIsKernel
  let φ : firstComplex A R ⟶ T :=
    { τ₁ := (R.extOneIso A).hom
      τ₂ := 𝟙 _
      τ₃ := 𝟙 _
      comm₁₂ := by simp [firstComplex, firstMap, T, S]
      comm₂₃ := (Category.id_comp _).trans (Category.comp_id _).symm }
  have : Epi φ.τ₁ := inferInstanceAs (Epi (R.extOneIso A).hom)
  have : IsIso φ.τ₂ := inferInstanceAs (IsIso (𝟙 (middle A R)))
  have : Mono φ.τ₃ := inferInstanceAs (Mono (𝟙 (AddCommGrpCat.of (Ext A R.complex.X₃ 0))))
  exact (ShortComplex.exact_iff_of_epi_of_isIso_of_mono φ).mpr hT

theorem secondComplex_exact : (secondComplex A R).Exact := by
  let := Ext.subsingleton_of_injective A R.complex.X₁ 0
  exact opcyclesRightComplex_exact (R.extZeroComplex A) (transgression A R)
    (R.extTwoCokernelComplex A).zero (R.extTwoCokernelComplex_exact A)

end Wikipedia.HopfProblem.SheafLerayLowDegrees.Abstract.Core
