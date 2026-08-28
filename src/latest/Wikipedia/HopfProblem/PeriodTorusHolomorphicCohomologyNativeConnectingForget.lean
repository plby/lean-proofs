import Wikipedia.HopfProblem.CuspNormalizationSheafCohomologyScalarResolutionForget

/-!
# Canonical cycle representatives under the genuine forgetful comparison

The canonical comparison between the actual homology of a complex of
complex vector spaces and its forgotten additive complex preserves the
original cycle projections. No representative or scalar structure is
chosen through a cohomology dimension computation.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace Wikipedia.HopfProblem.PeriodTorusHolomorphicCohomology.NativeConnecting

open CuspNormalization.SheafCohomologyScalarResolution

/-- The genuine forgetful homology comparison takes canonical cycle classes
to the corresponding canonical classes in the original linear complex. -/
theorem homologyForget_projection (S : ShortComplex (ModuleCat.{0} ℂ)) :
    (S.map linearForget).homologyπ ≫ (S.mapHomologyIso linearForget).hom =
      (S.mapCyclesIso linearForget).hom ≫ linearForget.map S.homologyπ := by
  let h := S.homologyData.left
  let eH : (S.map linearForget).homology ≅ linearForget.obj h.H :=
    (h.map linearForget).homologyIso
  let eK : (S.map linearForget).cycles ≅ linearForget.obj h.K :=
    (h.map linearForget).cyclesIso
  have hh : (S.mapHomologyIso linearForget).hom =
      eH.hom ≫ linearForget.map h.homologyIso.inv :=
    congrArg (fun e : (S.map linearForget).homology ≅ linearForget.obj S.homology => e.hom)
      (h.mapHomologyIso_eq linearForget)
  have hc : (S.mapCyclesIso linearForget).hom =
      eK.hom ≫ linearForget.map h.cyclesIso.inv :=
    congrArg (fun e : (S.map linearForget).cycles ≅ linearForget.obj S.cycles => e.hom)
      (h.mapCyclesIso_eq linearForget)
  have hp : (S.map linearForget).homologyπ ≫ eH.hom =
      eK.hom ≫ linearForget.map h.π :=
    (h.map linearForget).homologyπ_comp_homologyIso_hom
  rw [hh, hc, ← Category.assoc, hp, Category.assoc,
    ← linearForget.map_comp, h.π_comp_homologyIso_inv,
    linearForget.map_comp, Category.assoc]

/-- Pointwise form of the compatibility with the original cycle projection. -/
theorem homologyForget_projection_apply (S : ShortComplex (ModuleCat.{0} ℂ))
    (a : (S.map linearForget).cycles) :
    homologyForgetAddEquiv S ((S.map linearForget).homologyπ a) =
      S.homologyπ ((S.mapCyclesIso linearForget).hom a) :=
  ConcreteCategory.congr_hom (homologyForget_projection S) a

end Wikipedia.HopfProblem.PeriodTorusHolomorphicCohomology.NativeConnecting
