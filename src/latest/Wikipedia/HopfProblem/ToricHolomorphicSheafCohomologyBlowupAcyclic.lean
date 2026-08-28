import Wikipedia.HopfProblem.ToricHolomorphicSheafCohomologyBlowupAcyclicComparison
import Wikipedia.HopfProblem.ToricHolomorphicSheafCohomologyBlowupH1
import Wikipedia.HopfProblem.ToricHolomorphicSheafCohomologyMayerVietoris
import Wikipedia.HopfProblem.ToricHolomorphicSheafCohomologyOpenDolbeault

/-!
# Genuine holomorphic acyclicity of the actual affine blowup

The actual two incidence charts are affine-acyclic, and their literal
intersection is biholomorphic to the actual punctured product. The proved
global Dolbeault solutions give acyclicity of that punctured product.
Genuine Mayer--Vietoris therefore gives vanishing in degrees at least two;
the proved actual blowup Cousin splitting supplies degree one.

All groups here are Mathlib's actual Ext-defined sheaf cohomology. There
are no vanishing, resolution-comparison, or analytic-solvability premises.
-/

noncomputable section

open CategoryTheory TopologicalSpace
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.HolomorphicSheafCohomology.BlowupAcyclic

open AffineBlowup ToricCharts

/-- The overlap coordinate domain is literally the punctured open used
by the proved global Dolbeault vanishing theorem. -/
theorem puncturedOpen_eq : puncturedOpen = OpenDolbeault.puncturedOpen := rfl

/-- Unconditional genuine holomorphic acyclicity of the actual chart intersection. -/
theorem overlap_higher_subsingleton (n : ℕ) :
    Subsingleton (CategoryTheory.Sheaf.H.{0}
      (HolomorphicFunctionSheaf.additiveSheaf 𝓘(ℂ, CoordinateSpace 2) overlapOpen)
      (n + 1)) := by
  let e := overlapCohomologyEquiv false (n + 1)
  have hp := OpenDolbeault.punctured_higher_subsingleton n
  exact ⟨fun a b => e.injective (hp.elim (e a) (e b))⟩

/-- The actual ambient-open group occurring in the genuine Mayer--Vietoris
sequence vanishes on the literal incidence-chart intersection. -/
theorem overlap_open_higher_subsingleton (n : ℕ) :
    Subsingleton (CategoryTheory.Sheaf.H'.{0} BlowupH1.blowupSheaf (n + 1) overlapOpen) := by
  let e := overlapOpenCohomologyEquiv false (n + 1)
  have hp := OpenDolbeault.punctured_higher_subsingleton n
  exact ⟨fun a b => e.injective (hp.elim (e a) (e b))⟩

/-- The actual sheaf restriction to the actual intersection is likewise
acyclic, without any assumed identification of holomorphic sheaves. -/
theorem overlap_restriction_higher_subsingleton (n : ℕ) :
    Subsingleton (CategoryTheory.Sheaf.H.{0}
      ((OpenRestriction.restriction (X := TopCat.of Space) overlapOpen).obj
        BlowupH1.blowupSheaf) (n + 1)) := by
  let e := overlapRestrictionCohomologyEquiv false (n + 1)
  have hp := OpenDolbeault.punctured_higher_subsingleton n
  exact ⟨fun a b => e.injective (hp.elim (e a) (e b))⟩

/-- Every positive genuine holomorphic cohomology group of the actual
affine incidence blowup is zero, with no additional hypothesis. -/
theorem blowup_higher_subsingleton (n : ℕ) :
    Subsingleton (CategoryTheory.Sheaf.H.{0} BlowupH1.blowupSheaf (n + 1)) := by
  cases n with
  | zero => exact BlowupH1.blowup_h1_subsingleton
  | succ n =>
      have := HolomorphicRestriction.incidence_higher_subsingleton false (n + 1)
      have := HolomorphicRestriction.incidence_higher_subsingleton true (n + 1)
      have : Subsingleton (CategoryTheory.Sheaf.H'.{0} BlowupH1.blowupSheaf (n + 1)
          (Charts.incidenceOpen false ⊓ Charts.incidenceOpen true)) :=
        overlap_open_higher_subsingleton n
      exact MayerVietoris.sheaf_subsingleton_of_union BlowupH1.blowupSheaf
        (Charts.incidenceOpen false) (Charts.incidenceOpen true) incidenceOpen_sup (n + 2)
          (MayerVietoris.union_successor_subsingleton BlowupH1.blowupSheaf
            (Charts.incidenceOpen false) (Charts.incidenceOpen true) (n + 1))

theorem blowup_higher_eq_zero (n : ℕ)
    (a : CategoryTheory.Sheaf.H.{0} BlowupH1.blowupSheaf (n + 1)) : a = 0 :=
  (blowup_higher_subsingleton n).elim a 0

end Wikipedia.HopfProblem.HolomorphicSheafCohomology.BlowupAcyclic
