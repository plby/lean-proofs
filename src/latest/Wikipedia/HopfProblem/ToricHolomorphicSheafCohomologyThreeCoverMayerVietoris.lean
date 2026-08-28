import Wikipedia.HopfProblem.ToricHolomorphicSheafCohomologyThreeCoverNaturality

/-!
# Low-degree consequences of the original Mayer--Vietoris sequence

These elementary exact-sequence arguments apply to the native cohomology
presheaf maps. They do not replace any group or connecting map.
-/

noncomputable section

open TopologicalSpace CategoryTheory CategoryTheory.Limits

namespace Wikipedia.HopfProblem.HolomorphicSheafCohomology.ThreeCover

variable {X : TopCat.{0}} (F : TopCat.Sheaf AddCommGrpCat.{0} X) (A B : Opens X)

theorem restrictionDifference_injective_of_left (n : ℕ)
    [Subsingleton (CategoryTheory.Sheaf.H'.{0} F n B)]
    (h : Function.Injective
      (cohomologyRestrict F n (show A ⊓ B ≤ A from inf_le_left))) :
    Function.Injective (MayerVietoris.restrictionDifference F A B n) := by
  apply (injective_iff_map_eq_zero (MayerVietoris.restrictionDifference F A B n).hom).mpr
  intro z hz
  let e := AddCommGrpCat.biprodIsoProd
    (CategoryTheory.Sheaf.H'.{0} F n (MayerVietoris.square A B).X₂)
    (CategoryTheory.Sheaf.H'.{0} F n (MayerVietoris.square A B).X₃)
  obtain ⟨⟨a, b⟩, rfl⟩ := e.addCommGroupIsoToAddEquiv.symm.surjective z
  have hb : b = 0 :=
    (show Subsingleton (CategoryTheory.Sheaf.H'.{0} F n B) from inferInstance).elim b 0
  have he : cohomologyRestrict F n (show A ⊓ B ≤ A from inf_le_left) a -
      cohomologyRestrict F n (show A ⊓ B ≤ B from inf_le_right) b = 0 :=
    Eq.trans ((MayerVietoris.square A B).fromBiprod_biprodIsoProd_inv_apply F a b).symm hz
  have hb' : cohomologyRestrict F n (show A ⊓ B ≤ B from inf_le_right) b = 0 :=
    Eq.trans (congrArg (cohomologyRestrict F n inf_le_right) hb) (map_zero _)
  have ha : a = 0 := h (Eq.trans ((sub_eq_zero.mp he).trans hb') (map_zero _).symm)
  have hab : (a, b) = (0, 0) := Prod.ext ha hb
  exact Eq.trans (congrArg e.inv.hom hab) (map_zero e.inv.hom)

theorem restrictionDifference_surjective_of_left (n : ℕ)
    (h : Function.Surjective
      (cohomologyRestrict F n (show A ⊓ B ≤ A from inf_le_left))) :
    Function.Surjective (MayerVietoris.restrictionDifference F A B n) := by
  intro x
  obtain ⟨a, ha⟩ := h x
  let e := AddCommGrpCat.biprodIsoProd
    (CategoryTheory.Sheaf.H'.{0} F n (MayerVietoris.square A B).X₂)
    (CategoryTheory.Sheaf.H'.{0} F n (MayerVietoris.square A B).X₃)
  refine ⟨e.inv ⟨a, 0⟩, ?_⟩
  exact Eq.trans ((MayerVietoris.square A B).fromBiprod_biprodIsoProd_inv_apply F a 0)
    (Eq.trans (congrArg (fun y => cohomologyRestrict F n inf_le_left a - y)
      (map_zero (cohomologyRestrict F n (show A ⊓ B ≤ B from inf_le_right))))
      ((sub_zero _).trans ha))

/-- The degree-one union group vanishes when the original degree-zero
difference is onto and the original degree-one difference is one-to-one. -/
theorem union_one_subsingleton_of_maps
    (h0 : Function.Surjective (MayerVietoris.restrictionDifference F A B 0))
    (h1 : Function.Injective (MayerVietoris.restrictionDifference F A B 1)) :
    Subsingleton (CategoryTheory.Sheaf.H'.{0} F 1 (A ⊔ B)) := by
  refine subsingleton_of_forall_eq 0 ?_
  intro a
  have ha : MayerVietoris.restrictionPair F A B 1 a = 0 :=
    h1 (Eq.trans
      (ConcreteCategory.congr_hom ((MayerVietoris.square A B).toBiprod_fromBiprod F 1) a)
      (map_zero _).symm)
  obtain ⟨b, hb⟩ := ((MayerVietoris.unionComplex F A B 0).ab_exact_iff.mp
    (MayerVietoris.unionComplex_exact F A B 0)) a ha
  obtain ⟨c, hc⟩ := h0 b
  exact Eq.trans hb.symm
    (Eq.trans (congrArg (MayerVietoris.connecting F A B 0) hc.symm)
      (ConcreteCategory.congr_hom ((MayerVietoris.square A B).fromBiprod_δ F 0 1 rfl) c))

/-- In any positive degree, component vanishing and surjectivity of
the preceding native difference map force union vanishing. -/
theorem union_successor_subsingleton_of_difference (n : ℕ)
    [Subsingleton (CategoryTheory.Sheaf.H'.{0} F (n + 1) A)]
    [Subsingleton (CategoryTheory.Sheaf.H'.{0} F (n + 1) B)]
    (h : Function.Surjective (MayerVietoris.restrictionDifference F A B n)) :
    Subsingleton (CategoryTheory.Sheaf.H'.{0} F (n + 1) (A ⊔ B)) := by
  refine subsingleton_of_forall_eq 0 ?_
  intro a
  obtain ⟨b, rfl⟩ := MayerVietoris.connecting_surjective F A B n a
  obtain ⟨c, rfl⟩ := h b
  exact ConcreteCategory.congr_hom
    ((MayerVietoris.square A B).fromBiprod_δ F n (n + 1) rfl) c

end Wikipedia.HopfProblem.HolomorphicSheafCohomology.ThreeCover
