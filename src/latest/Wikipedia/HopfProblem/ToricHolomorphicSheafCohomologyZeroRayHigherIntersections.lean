import Wikipedia.HopfProblem.ToricHolomorphicSheafCohomologyZeroRayCoverOverlaps

/-!
# Actual higher holomorphic acyclicity of the zero-ray cover intersections

The constructed pair and triple coordinate maps are actual
biholomorphisms. Genuine open-restriction and biholomorphic cohomology
comparisons transport the proved punctured-product vanishing to the
literal intersections of the three open incidence blowups in E₀.
-/

noncomputable section

open TopologicalSpace CategoryTheory
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.HolomorphicSheafCohomology.ZeroRayHigher

open ToricCharts ZeroRayCover

/-- The actual coordinate swap exchanges the two punctured-product opens. -/
def firstDomainBiholomorph :
    Diffeomorph 𝓘(ℂ, ℂ × ℂ) 𝓘(ℂ, ℂ × ℂ)
      OpenDolbeault.puncturedOpen firstDomain ω where
  toEquiv :=
    { toFun q := ⟨((q : ℂ × ℂ).2, (q : ℂ × ℂ).1), q.property⟩
      invFun q := ⟨((q : ℂ × ℂ).2, (q : ℂ × ℂ).1), q.property⟩
      left_inv q := Subtype.ext (Prod.eta _)
      right_inv q := Subtype.ext (Prod.eta _) }
  contMDiff_toFun q := by
    apply (ChartedSpace.liftPropWithinAt_subtypeVal_comp_iff ..).mp
    exact (((ContinuousLinearEquiv.prodComm ℂ ℂ ℂ).contDiff.contMDiff).comp
      contMDiff_subtype_val) q
  contMDiff_invFun q := by
    apply (ChartedSpace.liftPropWithinAt_subtypeVal_comp_iff ..).mp
    exact (((ContinuousLinearEquiv.prodComm ℂ ℂ ℂ).contDiff.contMDiff).comp
      contMDiff_subtype_val) q

/-- Actual cohomology of the first pair intersection is actual
cohomology of the punctured affine product. -/
def pair01CohomologyEquiv (n : ℕ) :
    CategoryTheory.Sheaf.H'.{0} componentSheaf n (pairOpen 0 1) ≃+
      CategoryTheory.Sheaf.H.{0}
        (HolomorphicFunctionSheaf.additiveSheaf 𝓘(ℂ, ℂ × ℂ) OpenDolbeault.puncturedOpen) n :=
  (HolomorphicRestriction.cohomologyEquiv 𝓘(ℂ, CoordinateSpace 2) (pairOpen 0 1) n).trans
    ((Biholomorph.cohomologyEquiv pair01Biholomorph n).trans
      (Biholomorph.cohomologyEquiv firstDomainBiholomorph n))

def pair02CohomologyEquiv (n : ℕ) :
    CategoryTheory.Sheaf.H'.{0} componentSheaf n (pairOpen 0 2) ≃+
      CategoryTheory.Sheaf.H.{0}
        (HolomorphicFunctionSheaf.additiveSheaf 𝓘(ℂ, ℂ × ℂ) OpenDolbeault.puncturedOpen) n :=
  (HolomorphicRestriction.cohomologyEquiv 𝓘(ℂ, CoordinateSpace 2) (pairOpen 0 2) n).trans
    (Biholomorph.cohomologyEquiv pair02Biholomorph n)

def pair12CohomologyEquiv (n : ℕ) :
    CategoryTheory.Sheaf.H'.{0} componentSheaf n (pairOpen 1 2) ≃+
      CategoryTheory.Sheaf.H.{0}
        (HolomorphicFunctionSheaf.additiveSheaf 𝓘(ℂ, ℂ × ℂ) OpenDolbeault.puncturedOpen) n :=
  (HolomorphicRestriction.cohomologyEquiv 𝓘(ℂ, CoordinateSpace 2) (pairOpen 1 2) n).trans
    (Biholomorph.cohomologyEquiv pair12Biholomorph n)

/-- The actual triple-intersection comparison uses the actual double-punctured product. -/
def tripleCohomologyEquiv (n : ℕ) :
    CategoryTheory.Sheaf.H'.{0} componentSheaf n tripleOpen ≃+
      CategoryTheory.Sheaf.H.{0}
        (HolomorphicFunctionSheaf.additiveSheaf 𝓘(ℂ, ℂ × ℂ)
          OpenDolbeault.doublePuncturedOpen) n :=
  (HolomorphicRestriction.cohomologyEquiv 𝓘(ℂ, CoordinateSpace 2) tripleOpen n).trans
    (Biholomorph.cohomologyEquiv tripleBiholomorph n)

theorem pair01_higher_subsingleton (n : ℕ) :
    Subsingleton (CategoryTheory.Sheaf.H'.{0} componentSheaf (n + 1) (pairOpen 0 1)) := by
  let e := pair01CohomologyEquiv (n + 1)
  exact ⟨fun a b => e.injective ((OpenDolbeault.punctured_higher_subsingleton n).elim
    (e a) (e b))⟩

theorem pair02_higher_subsingleton (n : ℕ) :
    Subsingleton (CategoryTheory.Sheaf.H'.{0} componentSheaf (n + 1) (pairOpen 0 2)) := by
  let e := pair02CohomologyEquiv (n + 1)
  exact ⟨fun a b => e.injective ((OpenDolbeault.punctured_higher_subsingleton n).elim
    (e a) (e b))⟩

theorem pair12_higher_subsingleton (n : ℕ) :
    Subsingleton (CategoryTheory.Sheaf.H'.{0} componentSheaf (n + 1) (pairOpen 1 2)) := by
  let e := pair12CohomologyEquiv (n + 1)
  exact ⟨fun a b => e.injective ((OpenDolbeault.punctured_higher_subsingleton n).elim
    (e a) (e b))⟩

theorem triple_higher_subsingleton (n : ℕ) :
    Subsingleton (CategoryTheory.Sheaf.H'.{0} componentSheaf (n + 1) tripleOpen) := by
  let e := tripleCohomologyEquiv (n + 1)
  exact ⟨fun a b => e.injective ((OpenDolbeault.doublePunctured_higher_subsingleton n).elim
    (e a) (e b))⟩

end Wikipedia.HopfProblem.HolomorphicSheafCohomology.ZeroRayHigher
