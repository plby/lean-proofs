import Wikipedia.HopfProblem.ToricBlowdownPunctured
import Wikipedia.HopfProblem.ToricHolomorphicSheafCohomologyBlowupAcyclic
import Wikipedia.HopfProblem.ToricHolomorphicSheafCohomologyThreeCoverBasic

/-!
# The actual three-open blowup cover of the zero-ray component

The three opens are the literal ranges of the three affine incidence
blowup embeddings. Their cohomology is the actual holomorphic sheaf
cohomology, transported through the proved actual biholomorphisms.
-/

noncomputable section

open Set TopologicalSpace CategoryTheory
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.HolomorphicSheafCohomology.ZeroRayCover

open ToricCharts ToricSpace ToricComponent

abbrev component := rayDivisor 0
abbrev componentSheaf := HolomorphicFunctionSheaf.additiveSheaf 𝓘(ℂ, CoordinateSpace 2) component

/-- The three actual open incidence blowups, with their existing inclusions. -/
abbrev cover : Fin 3 → Opens component := blowupOpenSet

theorem cover_jointly_surjective (x : component) : ∃ k, x ∈ cover k := by
  obtain ⟨k, y, rfl⟩ := blowupMap_jointly_surjective x
  exact ⟨k, mem_range_self y⟩

theorem cover_iSup : (⨆ k, cover k) = ⊤ := by
  apply top_unique
  intro x _
  exact Opens.mem_iSup.mpr (cover_jointly_surjective x)

/-- The literal ordered three-open union required by Mayer--Vietoris is all of E₀. -/
theorem coverOpen_eq_top : ThreeCover.coverOpen (X := TopCat.of component) cover = ⊤ := by
  apply top_unique
  intro x _
  obtain ⟨k, hk⟩ := cover_jointly_surjective x
  change (x ∈ cover 0 ∨ x ∈ cover 1) ∨ x ∈ cover 2
  fin_cases k
  · exact Or.inl (Or.inl hk)
  · exact Or.inl (Or.inr hk)
  · exact Or.inr hk

/-- Actual ambient-open cohomology is actual incidence-blowup cohomology. -/
def coverCohomologyEquiv (k : Fin 3) (n : ℕ) :
    CategoryTheory.Sheaf.H'.{0} componentSheaf n (cover k) ≃+
      CategoryTheory.Sheaf.H.{0} BlowupH1.blowupSheaf n :=
  (HolomorphicRestriction.cohomologyEquiv 𝓘(ℂ, CoordinateSpace 2) (cover k) n).trans
    (Biholomorph.cohomologyEquiv (blowupBiholomorph k) n)

/-- Each actual member of the three-open cover is holomorphically acyclic. -/
theorem cover_higher_subsingleton (k : Fin 3) (n : ℕ) :
    Subsingleton (CategoryTheory.Sheaf.H'.{0} componentSheaf (n + 1) (cover k)) := by
  let e := coverCohomologyEquiv k (n + 1)
  exact ⟨fun a b => e.injective ((BlowupAcyclic.blowup_higher_subsingleton n).elim (e a) (e b))⟩

end Wikipedia.HopfProblem.HolomorphicSheafCohomology.ZeroRayCover
