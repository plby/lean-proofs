import Wikipedia.HopfProblem.CuspNormalizationSheafCohomologyGlobalSectionsRanks

/-!
# Representatives in the actual global normalization complex

The cycle representatives are actual global curve sections. The final
quotient representative is the difference of the actual P and Q values.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits
open scoped ContDiff

namespace Wikipedia.HopfProblem.CuspNormalization.SheafCohomologyGlobalSections

open SheafResolution SheafCohomologyResolution CuspQuotient ToricCharts ToricSpace

variable (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ) (hε : 0 < ε)
  (hε1 : ε < 1)
  (hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 ε))
  (hR : SmallDrift C ε)

/-- The actual global cycles whose curve values are `(u,u+v,v)`. -/
def globalCycleParam : ModuleCat.of ℂ (Fin 2 → ℂ) ⟶
    (globalLinearComplex C ε hε hε1 hC hR).cycles :=
  coefficientHomologyData.cyclesIso.inv ≫
    (ShortComplex.cyclesMapIso (globalCoefficientComplexIso C ε hε hε1 hC hR)).inv

/-- The cycle parametrization represents actual constant sections on the three curves. -/
theorem globalCycleParam_iCycles :
    globalCycleParam C ε hε hε1 hC hR ≫
      (globalLinearComplex C ε hε hε1 hC hR).iCycles =
    ModuleCat.ofHom coefficientCycles ≫
      (boundaryGlobalLinearEquiv C ε hε hε1 hC hR).toModuleIso.inv := by
  change (coefficientHomologyData.cyclesIso.inv ≫
    ShortComplex.cyclesMap (globalCoefficientComplexIso C ε hε hε1 hC hR).inv) ≫
      (globalLinearComplex C ε hε hε1 hC hR).iCycles =
    coefficientHomologyData.i ≫ (globalCoefficientComplexIso C ε hε hε1 hC hR).inv.τ₂
  rw [Category.assoc, ShortComplex.cyclesMap_i, ← Category.assoc,
    coefficientHomologyData.cyclesIso_inv_comp_iCycles]

/-- The actual homology class of the represented global cycle has coordinates `(u,v)`. -/
theorem globalHomologyIso_class :
    globalCycleParam C ε hε hε1 hC hR ≫
      (globalLinearComplex C ε hε hε1 hC hR).homologyπ ≫
        (globalHomologyIso C ε hε hε1 hC hR).hom = 𝟙 _ := by
  change (coefficientHomologyData.cyclesIso.inv ≫
    ShortComplex.cyclesMap (globalCoefficientComplexIso C ε hε hε1 hC hR).inv) ≫
      (globalLinearComplex C ε hε hε1 hC hR).homologyπ ≫
        (ShortComplex.homologyMap (globalCoefficientComplexIso C ε hε hε1 hC hR).hom ≫
          coefficientHomologyData.homologyIso.hom) = coefficientHomologyData.π
  rw [Category.assoc, ← Category.assoc
    (globalLinearComplex C ε hε hε1 hC hR).homologyπ,
    ShortComplex.homologyπ_naturality]
  simp only [← Category.assoc, ← ShortComplex.cyclesMap_comp,
    Iso.inv_hom_id, ShortComplex.cyclesMap_id, Category.comp_id]
  exact coefficientHomologyIso_class

/-- On actual global sections, the cokernel coordinate is literally P minus Q. -/
theorem globalCokernelIso_class :
    cokernel.π (globalLinearComplex C ε hε hε1 hC hR).g ≫
        (globalCokernelIso C ε hε hε1 hC hR).hom =
      (tripleGlobalLinearEquiv C ε hε).toModuleIso.hom ≫
        ModuleCat.ofHom coefficientDifference := by
  dsimp only [globalCokernelIso, Iso.trans_hom, cokernel.mapIso, cokernel.map]
  rw [← Category.assoc, cokernel.π_desc, Category.assoc, coefficientCokernelIso_class]
  rfl

end Wikipedia.HopfProblem.CuspNormalization.SheafCohomologyGlobalSections
