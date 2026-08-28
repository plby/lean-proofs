import Wikipedia.HopfProblem.ToricHolomorphicSheafCohomologyHolomorphicRestrictionCohomology

/-!
# Coefficient maps through the actual holomorphic open comparison

An actual coefficient map from the ambient holomorphic sheaf into an
arbitrary sheaf induces a map on the original open cohomology groups.
The native open comparison identifies it with the literal restricted
coefficient map in every degree. Consequently, a coefficient square
with a local holomorphic multiplier gives the corresponding square on
the original cohomology groups, without extending the multiplier.
-/

noncomputable section

open CategoryTheory TopologicalSpace Opposite
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.PeriodFamilyHigherDirectImage.LocalBaseAction.Fibre

open HolomorphicSheafCohomology

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [TopologicalSpace H] (I : ModelWithCorners ℂ E H)
  {M : Type} [TopologicalSpace M] [ChartedSpace H M]

/-- The original coefficient map on an ambient open becomes the literal
restricted coefficient map under the genuine all-degree comparison. -/
theorem coefficient_open_comparison (U : Opens M)
    {L : TopCat.Sheaf AddCommGrpCat.{0} (TopCat.of M)}
    (η : HolomorphicFunctionSheaf.additiveSheaf I M ⟶ L)
    (q : ℕ) (x : CategoryTheory.Sheaf.H'.{0}
      (HolomorphicFunctionSheaf.additiveSheaf I M) q U) :
    OpenRestriction.cohomologyEquiv (X := TopCat.of M) U L q
        (((CategoryTheory.Sheaf.cohomologyPresheafFunctor
          (Opens.grothendieckTopology (TopCat.of M)) q).map η).app (op U) x) =
      CategoryTheory.Sheaf.H.map ((HolomorphicRestriction.sheafIso I U).inv ≫
        (OpenRestriction.restriction (X := TopCat.of M) U).map η) q
          (HolomorphicRestriction.cohomologyEquiv I U q x) := by
  let R := OpenRestriction.restriction (X := TopCat.of M) U
  let φ := HolomorphicRestriction.sheafIso I U
  let y := OpenRestriction.cohomologyEquiv (X := TopCat.of M) U
    (HolomorphicFunctionSheaf.additiveSheaf I M) q x
  have hh := congrArg (fun k : R.obj (HolomorphicFunctionSheaf.additiveSheaf I M) ⟶
      R.obj (HolomorphicFunctionSheaf.additiveSheaf I M) =>
        CategoryTheory.Sheaf.H.map k q y) φ.hom_inv_id
  have hi := (CategoryTheory.Sheaf.H.map_comp_apply φ.hom φ.inv y).symm.trans
    (hh.trans (CategoryTheory.Sheaf.H.map_id_apply y))
  have hn := OpenRestriction.cohomologyEquiv_naturality (X := TopCat.of M) U η q x
  have hc := CategoryTheory.Sheaf.H.map_comp_apply φ.inv (R.map η)
    (CategoryTheory.Sheaf.H.map φ.hom q y)
  exact hn.trans ((congrArg (CategoryTheory.Sheaf.H.map (R.map η) q) hi).symm.trans hc.symm)

/-- A literal square for a local multiplier intertwines its transported
action with an actual ambient coefficient map in every cohomological degree. -/
theorem coefficient_open_intertwining (U : Opens M)
    {L : TopCat.Sheaf AddCommGrpCat.{0} (TopCat.of M)}
    (η : HolomorphicFunctionSheaf.additiveSheaf I M ⟶ L)
    (m : HolomorphicFunctionSheaf.additiveSheaf I U ⟶
      HolomorphicFunctionSheaf.additiveSheaf I U)
    (ℓ : L ⟶ L)
    (hσ : m ≫ ((HolomorphicRestriction.sheafIso I U).inv ≫
        (OpenRestriction.restriction (X := TopCat.of M) U).map η) =
      ((HolomorphicRestriction.sheafIso I U).inv ≫
        (OpenRestriction.restriction (X := TopCat.of M) U).map η) ≫
          (OpenRestriction.restriction (X := TopCat.of M) U).map ℓ)
    (q : ℕ) (x : CategoryTheory.Sheaf.H'.{0}
      (HolomorphicFunctionSheaf.additiveSheaf I M) q U) :
    (((CategoryTheory.Sheaf.cohomologyPresheafFunctor
      (Opens.grothendieckTopology (TopCat.of M)) q).map η).app (op U))
        ((HolomorphicRestriction.cohomologyEquiv I U q).symm
          (CategoryTheory.Sheaf.H.map m q
            (HolomorphicRestriction.cohomologyEquiv I U q x))) =
      (((CategoryTheory.Sheaf.cohomologyPresheafFunctor
        (Opens.grothendieckTopology (TopCat.of M)) q).map ℓ).app (op U))
          ((((CategoryTheory.Sheaf.cohomologyPresheafFunctor
            (Opens.grothendieckTopology (TopCat.of M)) q).map η).app (op U)) x) := by
  let R := OpenRestriction.restriction (X := TopCat.of M) U
  let e := HolomorphicRestriction.cohomologyEquiv I U q
  let σ := (HolomorphicRestriction.sheafIso I U).inv ≫
    R.map η
  let y := e x
  let t := e.symm (CategoryTheory.Sheaf.H.map m q y)
  let ηq := ((CategoryTheory.Sheaf.cohomologyPresheafFunctor
    (Opens.grothendieckTopology (TopCat.of M)) q).map η).app (op U)
  have hl := coefficient_open_comparison I U η q t
  have he := congrArg (CategoryTheory.Sheaf.H.map σ q)
    (e.apply_symm_apply (CategoryTheory.Sheaf.H.map m q y))
  have hr := OpenRestriction.cohomologyEquiv_naturality (X := TopCat.of M) U ℓ q (ηq x)
  have hn := congrArg (CategoryTheory.Sheaf.H.map (R.map ℓ) q)
    (coefficient_open_comparison I U η q x)
  have hs := congrArg (fun k : HolomorphicFunctionSheaf.additiveSheaf I U ⟶
      R.obj L =>
        CategoryTheory.Sheaf.H.map k q y) hσ
  have hsq := (CategoryTheory.Sheaf.H.map_comp_apply m σ y).symm.trans
    (hs.trans (CategoryTheory.Sheaf.H.map_comp_apply σ (R.map ℓ) y))
  exact (OpenRestriction.cohomologyEquiv (X := TopCat.of M) U L q).injective
    ((hl.trans he).trans (hsq.trans (hr.trans hn).symm))

end Wikipedia.HopfProblem.PeriodFamilyHigherDirectImage.LocalBaseAction.Fibre
