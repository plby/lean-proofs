import Wikipedia.HopfProblem.CuspNormalizationSheafCohomologyAboveTwo
import Wikipedia.HopfProblem.ToricHolomorphicSheafCohomologyZeroRayCover

/-!
# Genuine holomorphic cohomology of the cusp surface

The actual normalization surface is holomorphically acyclic by its
constructed three-open blowup cover and actual analytic cocycle solvers.
The actual double curves and skyscrapers are likewise acyclic. Applying
the proved genuine Ext comparison to the actual normalization resolution
therefore computes the reduced structure sheaf's cohomology.

The complex scalar actions below come from the original pointwise
sheaf endomorphisms. The linear identifications and dimensions are for
Mathlib's actual `Sheaf.H`; cohomology is not defined by the coefficient
complex. No rational-surface, Stein, or acyclicity hypothesis is assumed.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits
open scoped ContDiff

namespace Wikipedia.HopfProblem.CuspNormalization.SheafCohomology

open SheafResolution SheafCohomologyGlobalSections
open CuspQuotient ToricCharts ToricSpace

variable (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ) (hε : 0 < ε)
  (hε1 : ε < 1)
  (hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 ε))
  (hR : SmallDrift C ε)

include hε1 hC hR

/-- The actual normalization term is acyclic in every positive degree,
by the actual toric-surface proof and finite closed pushforward. -/
theorem normalizationSheaf_higher_subsingleton (n : ℕ) :
    Subsingleton (CategoryTheory.Sheaf.H.{0} (normalizationSheaf C ε hε) (n + 1)) := by
  let e := normalizationHolomorphicCohomologyEquiv C ε hε hε1 hC hR (n + 1)
  have hs := HolomorphicSheafCohomology.ZeroRayCover.zeroRay_higher_subsingleton n
  exact ⟨fun a b => e.injective (hs.elim (e a) (e b))⟩

/-- Genuine H⁰ is complex-linearly the scalar field, with its original
scalar action induced by the reduced structure sheaf. -/
def reducedH0LinearEquiv :
    CategoryTheory.Sheaf.H.{0} (reducedSheaf C ε hε hε1 hC hR) 0 ≃ₗ[ℂ] ℂ :=
  SheafCohomologyScalarResolution.reducedH0LinearEquiv C ε hε hε1 hC hR

/-- Genuine H¹ is complex-linearly ℂ². The coordinates are the actual
two curve-cycle coordinates of the normalization resolution. -/
def reducedH1LinearEquiv :
    CategoryTheory.Sheaf.H.{0} (reducedSheaf C ε hε hε1 hC hR) 1 ≃ₗ[ℂ] (Fin 2 → ℂ) := by
  let := normalizationSheaf_higher_subsingleton C ε hε hε1 hC hR 0
  exact (SheafCohomologyScalarResolution.reducedH1GlobalLinearEquiv C ε hε hε1 hC hR).trans
    ((globalHomologyForgetLinearEquiv C ε hε hε1 hC hR).trans
      (globalHomologyIso C ε hε hε1 hC hR).toLinearEquiv)

/-- Genuine H² is complex-linearly ℂ. The final coefficient is the
actual P-minus-Q quotient of the two triple-point values. -/
def reducedH2LinearEquiv :
    CategoryTheory.Sheaf.H.{0} (reducedSheaf C ε hε hε1 hC hR) 2 ≃ₗ[ℂ] ℂ := by
  let := normalizationSheaf_higher_subsingleton C ε hε hε1 hC hR 0
  let := normalizationSheaf_higher_subsingleton C ε hε hε1 hC hR 1
  let := boundarySheaf_higher_subsingleton C ε hε hε1 hC hR 0
  exact (SheafCohomologyScalarResolution.reducedH2GlobalLinearEquiv C ε hε hε1 hC hR).trans
    ((globalCokernelForgetLinearEquiv C ε hε hε1 hC hR).trans
      (globalCokernelIso C ε hε hε1 hC hR).toLinearEquiv)

theorem reducedH0_finrank :
    Module.finrank ℂ (CategoryTheory.Sheaf.H.{0} (reducedSheaf C ε hε hε1 hC hR) 0) = 1 :=
  (reducedH0LinearEquiv C ε hε hε1 hC hR).finrank_eq.trans (Module.finrank_self ℂ)

theorem reducedH1_finrank :
    Module.finrank ℂ (CategoryTheory.Sheaf.H.{0} (reducedSheaf C ε hε hε1 hC hR) 1) = 2 :=
  (reducedH1LinearEquiv C ε hε hε1 hC hR).finrank_eq.trans (Module.finrank_fin_fun ℂ)

theorem reducedH2_finrank :
    Module.finrank ℂ (CategoryTheory.Sheaf.H.{0} (reducedSheaf C ε hε hε1 hC hR) 2) = 1 :=
  (reducedH2LinearEquiv C ε hε hε1 hC hR).finrank_eq.trans (Module.finrank_self ℂ)

theorem reducedSheaf_above_two_finrank (n : ℕ) :
    Module.finrank ℂ (CategoryTheory.Sheaf.H.{0}
      (reducedSheaf C ε hε hε1 hC hR) (n + 3)) = 0 := by
  let := reducedSheaf_above_two_subsingleton C ε hε hε1 hC hR n
  exact Module.finrank_zero_of_subsingleton

/-- The complete dimension calculation in every actual cohomological degree. -/
theorem reducedSheaf_finrank (n : ℕ) :
    Module.finrank ℂ (CategoryTheory.Sheaf.H.{0} (reducedSheaf C ε hε hε1 hC hR) n) =
      if n = 0 then 1 else if n = 1 then 2 else if n = 2 then 1 else 0 := by
  cases n with
  | zero => simpa using reducedH0_finrank C ε hε hε1 hC hR
  | succ n =>
    cases n with
    | zero => simpa using reducedH1_finrank C ε hε hε1 hC hR
    | succ n =>
      cases n with
      | zero => simpa using reducedH2_finrank C ε hε hε1 hC hR
      | succ n => simpa using reducedSheaf_above_two_finrank C ε hε hε1 hC hR n

/-- The Euler characteristic of the genuine, finitely supported
holomorphic cohomology is zero, as asserted in source Lemma 9.12(ii). -/
theorem reducedSheaf_eulerCharacteristic :
    (Module.finrank ℂ (CategoryTheory.Sheaf.H.{0}
        (reducedSheaf C ε hε hε1 hC hR) 0) : ℤ) -
      (Module.finrank ℂ (CategoryTheory.Sheaf.H.{0}
        (reducedSheaf C ε hε hε1 hC hR) 1) : ℤ) +
      (Module.finrank ℂ (CategoryTheory.Sheaf.H.{0}
        (reducedSheaf C ε hε hε1 hC hR) 2) : ℤ) = 0 := by
  rw [reducedH0_finrank, reducedH1_finrank, reducedH2_finrank]
  norm_num

end Wikipedia.HopfProblem.CuspNormalization.SheafCohomology
