import Wikipedia.HopfProblem.PeriodFamilyHigherDirectImageGlobalStalk
import Mathlib.Algebra.Category.Grp.FilteredColimits

/-!
# Vanishing of original global classes in the genuine derived stalk

The actual stalk comparison and the native presheaf germ theorem show
that a global cohomology class has zero derived-stalk germ precisely
when its original restriction vanishes over some base neighborhood.
No fibre-cohomology, separation, finiteness, or base-change hypothesis
is imposed, and no replacement stalk is introduced.
-/

noncomputable section

open TopologicalSpace Opposite CategoryTheory CategoryTheory.Limits

namespace Wikipedia.HopfProblem.PeriodFamilyHigherDirectImage.GlobalRestriction

open CuspNormalization.SheafCohomologyFinitePushforward

variable {X Y : TopCat.{0}}

/-- A germ in the actual stalk of an additive presheaf is zero exactly
when its original section restricts to zero on a smaller neighborhood. -/
theorem presheaf_germ_eq_zero_iff (P : TopCat.Presheaf AddCommGrpCat.{0} Y)
    (y : Y) (U : Opens Y) (hy : y ∈ U) (s : P.obj (op U)) :
    P.germ U y hy s = 0 ↔
      ∃ (W : Opens Y) (_ : y ∈ W) (r : W ⟶ U), P.map r.op s = 0 := by
  constructor
  · intro hs
    obtain ⟨W, hyW, r, r', hr⟩ := P.germ_eq y hy hy s 0
      (hs.trans (map_zero (P.germ U y hy).hom).symm)
    exact ⟨W, hyW, r, hr.trans (map_zero (P.map r'.op).hom)⟩
  · rintro ⟨W, hyW, r, hr⟩
    exact (P.germ_res_apply r y hyW s).symm.trans
      ((congrArg (P.germ W y hyW) hr).trans (map_zero (P.germ W y hyW).hom))

/-- Vanishing in the genuine higher-direct-image stalk is equivalent
to actual cohomological vanishing over some original base neighborhood. -/
theorem globalStalkClass_eq_zero_iff (f : X ⟶ Y) (F : AbelianSheaf X) (y : Y)
    (n : ℕ) (a : CategoryTheory.Sheaf.H.{0} F n) :
    globalStalkClass f F y n a = 0 ↔
      ∃ U : Opens Y, y ∈ U ∧ restrictionMap F ((Opens.map f).obj U) n a = 0 := by
  constructor
  · intro ha
    let P : TopCat.Presheaf AddCommGrpCat.{0} Y :=
      FibreNeighborhood.sourceCohomologyPresheaf (F := F) f n
    let e := SheafHigherDirectImage.stalkCohomologyPresheafIso f F n y
    let s : P.obj (op (⊤ : Opens Y)) := restrictionMap F ((Opens.map f).obj ⊤) n a
    have hg : P.germ ⊤ y (by trivial) s = 0 :=
      (ConcreteCategory.congr_hom e.inv_hom_id (P.germ ⊤ y (by trivial) s)).symm.trans
        ((congrArg e.hom ha).trans (map_zero e.hom.hom))
    obtain ⟨U, hyU, r, hr⟩ :=
      (presheaf_germ_eq_zero_iff P y ⊤ (by trivial) s).mp hg
    exact ⟨U, hyU,
      (restrictionMap_restrict F ((Opens.map f).map r) n a).symm.trans hr⟩
  · rintro ⟨U, hyU, hU⟩
    exact (globalStalkClass_eq_neighborhood f F y n U hyU a).trans
      ((congrArg (FibreNeighborhood.derivedNeighborhoodGerm (F := F) f y n U hyU) hU).trans
        (map_zero (FibreNeighborhood.derivedNeighborhoodGerm (F := F) f y n U hyU).hom))

/-- A global class has a nonzero genuine stalk germ exactly when none
of its original neighborhood restrictions vanish. -/
theorem globalStalkClass_ne_zero_iff (f : X ⟶ Y) (F : AbelianSheaf X) (y : Y)
    (n : ℕ) (a : CategoryTheory.Sheaf.H.{0} F n) :
    globalStalkClass f F y n a ≠ 0 ↔
      ∀ U : Opens Y, y ∈ U → restrictionMap F ((Opens.map f).obj U) n a ≠ 0 := by
  constructor
  · intro ha U hyU hU
    exact ha ((globalStalkClass_eq_zero_iff f F y n a).mpr ⟨U, hyU, hU⟩)
  · intro h ha
    obtain ⟨U, hyU, hU⟩ := (globalStalkClass_eq_zero_iff f F y n a).mp ha
    exact h U hyU hU

end Wikipedia.HopfProblem.PeriodFamilyHigherDirectImage.GlobalRestriction
