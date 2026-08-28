import Wikipedia.HopfProblem.ToricHolomorphicSheafCohomologyZeroRayHigher
import Wikipedia.HopfProblem.CuspNormalizationSheafCohomologyCurves
import Wikipedia.HopfProblem.CuspNormalizationSheafCohomologyScalarResolution

/-!
# Genuine cusp holomorphic cohomology vanishes above degree two

Only the relevant three higher groups of the normalization resolution
are needed in each degree. The actual normalization surface has the
proved vanishing above degree two, the actual double curves are acyclic,
and the terminal actual skyscrapers are injective. Two genuine Ext
connecting maps prove the conclusion for the reduced structure sheaf.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian
open scoped ContDiff

namespace Wikipedia.HopfProblem.CuspNormalization.SheafCohomologyResolution

universe w v u

namespace AugmentedResolution

variable {C : Type u} [Category.{v} C] [Abelian C] [HasExt.{w} C]

/-- A length-two resolution needs only the three indicated vanishings
to annihilate a given actual higher Ext group. -/
theorem ext_subsingleton_degree_window (R : AugmentedResolution C) (P : C) (n : ℕ)
    (hA : Subsingleton (Ext P R.complex.X₁ (n + 3)))
    (hB : Subsingleton (Ext P R.complex.X₂ (n + 2)))
    (hD : Subsingleton (Ext P R.complex.X₃ (n + 1))) :
    Subsingleton (Ext P R.F (n + 3)) := by
  let := hA
  let := hB
  let := hD
  have hK : Subsingleton (Ext P R.K (n + 2)) := by
    constructor
    intro x y
    obtain ⟨x', rfl⟩ := connecting_surjective P R.second_shortExact (n + 1) x
    obtain ⟨y', rfl⟩ := connecting_surjective P R.second_shortExact (n + 1) y
    exact congrArg (connecting P R.second_shortExact (n + 1)) (Subsingleton.elim x' y')
  constructor
  intro x y
  obtain ⟨x', rfl⟩ := connecting_surjective P R.first_shortExact (n + 2) x
  obtain ⟨y', rfl⟩ := connecting_surjective P R.first_shortExact (n + 2) y
  exact congrArg (connecting P R.first_shortExact (n + 2)) (hK.elim x' y')

theorem h_subsingleton_degree_window {X : TopCat.{0}}
    (R : AugmentedResolution (TopCat.Sheaf AddCommGrpCat.{0} X)) (n : ℕ)
    [Subsingleton (CategoryTheory.Sheaf.H.{0} R.complex.X₁ (n + 3))]
    [Subsingleton (CategoryTheory.Sheaf.H.{0} R.complex.X₂ (n + 2))]
    [Subsingleton (CategoryTheory.Sheaf.H.{0} R.complex.X₃ (n + 1))] :
    Subsingleton (CategoryTheory.Sheaf.H.{0} R.F (n + 3)) :=
  R.ext_subsingleton_degree_window (unitSheaf X) n
    (inferInstanceAs (Subsingleton (CategoryTheory.Sheaf.H.{0} R.complex.X₁ (n + 3))))
    (inferInstanceAs (Subsingleton (CategoryTheory.Sheaf.H.{0} R.complex.X₂ (n + 2))))
    (inferInstanceAs (Subsingleton (CategoryTheory.Sheaf.H.{0} R.complex.X₃ (n + 1))))

end AugmentedResolution

end Wikipedia.HopfProblem.CuspNormalization.SheafCohomologyResolution

namespace Wikipedia.HopfProblem.CuspNormalization.SheafCohomology

open SheafResolution SheafCohomologyResolution
open CuspQuotient ToricCharts ToricSpace

variable (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ) (hε : 0 < ε)
  (hε1 : ε < 1)
  (hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 ε))
  (hR : SmallDrift C ε)

include hε1 hC hR

/-- Actual finite closed pushforward preserves the actual normalization
surface's proved vanishing in degrees above two. -/
theorem normalizationSheaf_above_two_subsingleton (n : ℕ) :
    Subsingleton (CategoryTheory.Sheaf.H.{0} (normalizationSheaf C ε hε) (n + 3)) := by
  let e := normalizationHolomorphicCohomologyEquiv C ε hε hε1 hC hR (n + 3)
  have hs := HolomorphicSheafCohomology.ZeroRayHigher.zeroRay_above_two_subsingleton n
  exact ⟨fun a b => e.injective (hs.elim (e a) (e b))⟩

/-- All actual higher groups of the reduced holomorphic structure sheaf
of the cusp surface vanish above degree two. -/
theorem reducedSheaf_above_two_subsingleton (n : ℕ) :
    Subsingleton (CategoryTheory.Sheaf.H.{0} (reducedSheaf C ε hε hε1 hC hR) (n + 3)) := by
  let R := normalizationAugmentedResolution C ε hε hε1 hC hR
  have : Subsingleton (CategoryTheory.Sheaf.H.{0} R.complex.X₁ (n + 3)) :=
    normalizationSheaf_above_two_subsingleton C ε hε hε1 hC hR n
  have : Subsingleton (CategoryTheory.Sheaf.H.{0} R.complex.X₂ (n + 2)) :=
    boundarySheaf_higher_subsingleton C ε hε hε1 hC hR (n + 1)
  have : Subsingleton (CategoryTheory.Sheaf.H.{0} R.complex.X₃ (n + 1)) :=
    tripleSheaf_higher_subsingleton C ε hε n
  exact R.h_subsingleton_degree_window n

theorem reducedSheaf_above_two_eq_zero (n : ℕ)
    (a : CategoryTheory.Sheaf.H.{0} (reducedSheaf C ε hε hε1 hC hR) (n + 3)) : a = 0 :=
  (reducedSheaf_above_two_subsingleton C ε hε hε1 hC hR n).elim a 0

end Wikipedia.HopfProblem.CuspNormalization.SheafCohomology
