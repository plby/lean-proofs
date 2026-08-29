/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.SingularFiniteRepairProfileProgress
import ErdosProblems.Erdos599.SingularReroutedSafeBatchMachine

/-!
# Zorn iteration of residual hindrance profiles

A full wave is not evidence that a web is unhindered: the family of trivial
paths is a full wave in every web.  Thus a finite repair cannot be iterated
by maximizing arbitrary wave initial sets.  The sound state space used here
has two kinds of profiles:

* a top profile, certified by an actually unhindered carrier deletion; or
* the initial set of a maximal hindrance in a hindered carrier deletion.

If chains of attainable profiles have attainable upper bounds and every
maximal hindrance admits a strict attainable profile improvement, Zorn's
lemma forces a top profile.  This file proves that order-theoretic step and
connects its uniform form to the singular completed-row machine.  The two
construction-facing premises are deliberately separated: finite marked
switching supplies strict successor improvement, while a source-faithful
limit construction must supply chain upper bounds for varying carriers.
-/

noncomputable section

open Cardinal Set

namespace Erdos599
namespace CardinalInduction
namespace SingularResidualProfileZorn

open DWeb
open SingularFiniteRepairProfileProgress
open SingularReroutedSafeBatchMachine
open SingularSafeCompletedMachine
open SingularSafeDesignatedLinkage

universe u

variable {V : Type u}

/-- Every web, hindered or not, has a maximal wave with the full source as
its initial set: start from the trivial wave and take a maximal forward
extension.  Consequently arbitrary maximal-wave profiles cannot serve as
a progress measure for deletion safety. -/
theorem exists_fullInitial_maximalWave (G : DWeb V) :
    ∃ M : G.Wave, IsMax M ∧ G.initialSet M.1 = G.source := by
  let W₀ : G.Wave := ⟨G.trivialWave, G.isWave_trivialWave⟩
  obtain ⟨M, hW₀M, hMmax⟩ := G.exists_maximal_wave_extending W₀
  refine ⟨M, hMmax, ?_⟩
  rw [← G.initialSet_eq_of_forwardExtension hW₀M,
    G.initialSet_trivialWave]

/-- A profile realized by a target linkage.  The top case records genuine
residual unhinderedness.  Every non-top case is tied to a maximal
*hindrance*, rather than to an arbitrary maximal wave. -/
def ResidualRepairProfile (G : DWeb V) (P : Set G.DPath)
    (S : Set V) : Prop :=
  ((G.delete (G.vertexSet P)).IsUnhindered ∧
      S = (G.delete (G.vertexSet P)).source) ∨
    ∃ M : (G.delete (G.vertexSet P)).Wave,
      IsMax M ∧
      (G.delete (G.vertexSet P)).IsHindrance M.1 ∧
      S = (G.delete (G.vertexSet P)).initialSet M.1

/-- A residual profile is attainable for `A` when some `A`--target linkage
realizes it.  The linkage is allowed to be rerouted completely between
successor stages. -/
def AttainableResidualRepairProfile (G : DWeb V) (A S : Set V) : Prop :=
  ∃ P : Set G.DPath,
    IsLinkageBetween G A G.target P ∧ ResidualRepairProfile G P S

/-- Every target linkage realizes some repair profile.  In the hindered
case choose a maximal extension of an actual hindrance; choosing an
arbitrary maximal wave would be unsound here. -/
theorem exists_attainableResidualRepairProfile_of_linkage
    {G : DWeb V} {A : Set V} {P : Set G.DPath}
    (hP : IsLinkageBetween G A G.target P) :
    ∃ S : Set V, AttainableResidualRepairProfile G A S := by
  by_cases hsafe : (G.delete (G.vertexSet P)).IsUnhindered
  · refine ⟨(G.delete (G.vertexSet P)).source, P, hP, Or.inl ?_⟩
    exact ⟨hsafe, rfl⟩
  · have hhindered : (G.delete (G.vertexSet P)).IsHindered :=
      (G.delete (G.vertexSet P)).not_isUnhindered_iff_isHindered.mp hsafe
    obtain ⟨M, hMmax, hMh⟩ :=
      (G.delete (G.vertexSet P)).exists_maximal_hindrance hhindered
    refine ⟨(G.delete (G.vertexSet P)).initialSet M.1,
      P, hP, Or.inr ?_⟩
    exact ⟨M, hMmax, hMh, rfl⟩

/-- The exact limit premise for profile iteration.  It permits complete
rerouting of the target linkage and of the maximal hindrance at a limit;
only inclusion of the earlier profiles is retained. -/
def ResidualRepairProfileChainUpperBounds
    (G : DWeb V) (A : Set V) : Prop :=
  ∀ c : Set (Set V),
    c ⊆ {S | AttainableResidualRepairProfile G A S} →
    IsChain (· ⊆ ·) c → c.Nonempty →
      ∃ U, AttainableResidualRepairProfile G A U ∧
        ∀ S ∈ c, S ⊆ U

/-- The exact successor premise.  A finite marked repair of a maximal
residual hindrance must either reach a safe top profile or produce a new
maximal hindrance with a strictly larger initial profile.  Both outcomes
are uniformly expressed by attainability of `S`. -/
def ResidualRepairProfileStrictImprovement
    (G : DWeb V) (A : Set V) : Prop :=
  ∀ {P : Set G.DPath},
    IsLinkageBetween G A G.target P →
    ∀ M : (G.delete (G.vertexSet P)).Wave, IsMax M →
      (G.delete (G.vertexSet P)).IsHindrance M.1 →
      ∃ S : Set V,
        AttainableResidualRepairProfile G A S ∧
          (G.delete (G.vertexSet P)).initialSet M.1 ⊂ S

/-- Zorn's lemma turns chain rerouting and strict finite improvement into a
genuinely safe designated linkage.  Notice that the proof never concludes
safety from existence of one full wave: it terminates only in the explicit
unhindered branch of `ResidualRepairProfile`. -/
theorem exists_safeDesignatedLinkage_of_residualProfileZorn
    (G : DWeb V) {A : Set V} {P₀ : Set G.DPath}
    (hP₀ : IsLinkageBetween G A G.target P₀)
    (hupper : ResidualRepairProfileChainUpperBounds G A)
    (himprove : ResidualRepairProfileStrictImprovement G A) :
    Nonempty (SafeDesignatedLinkage G A) := by
  let Good : Set (Set V) :=
    {S | AttainableResidualRepairProfile G A S}
  obtain ⟨S₀, hS₀⟩ :=
    exists_attainableResidualRepairProfile_of_linkage hP₀
  obtain ⟨S, _hS₀S, hSmax⟩ := zorn_subset_nonempty Good (by
    intro c hc hchain hcne
    obtain ⟨U, hU, hUc⟩ := hupper c hc hchain hcne
    exact ⟨U, hU, hUc⟩) S₀ hS₀
  have hSgood : AttainableResidualRepairProfile G A S := hSmax.1
  obtain ⟨P, hP, hprofile⟩ := hSgood
  rcases hprofile with hsafe | ⟨M, hMmax, hMh, hSM⟩
  · exact ⟨{
      paths := P
      linkage := hP
      residual_unhindered := hsafe.1 }⟩
  · obtain ⟨S', hS'good, hstrict⟩ :=
      himprove hP M hMmax hMh
    have hSS' : S ⊆ S' := by
      rw [hSM]
      exact hstrict.1
    have hS'S : S' ⊆ S := hSmax.2 hS'good hSS'
    exact False.elim (hstrict.2 (hSM ▸ hS'S))

/-! ## Exactness of the two Zorn inputs -/

/-- Every realized profile lies in the source of its own carrier deletion.
For a top profile this is equality; for a hindrance profile it is the
initial-set clause of the wave. -/
theorem residualRepairProfile_subset_deleteSource
    {G : DWeb V} {P : Set G.DPath} {S : Set V}
    (hS : ResidualRepairProfile G P S) :
    S ⊆ (G.delete (G.vertexSet P)).source := by
  rcases hS with ⟨_hsafe, rfl⟩ | ⟨M, _hMmax, hMh, rfl⟩
  · exact Set.Subset.rfl
  · exact hMh.1.2.1

/-- A safe designated linkage supplies a greatest attainable profile.  The
source sets of all carrier deletions agree because normalized target
linkages with the same prescribed initial set delete the same ambient
sources. -/
theorem residualRepairProfileChainUpperBounds_of_safeDesignated
    {G : DWeb V} (hNorm : G.IsNormalized)
    {A : Set V} (hA : A ⊆ G.source)
    (L : SafeDesignatedLinkage G A) :
    ResidualRepairProfileChainUpperBounds G A := by
  intro c hc _hchain _hcne
  let U := (G.delete (G.vertexSet L.paths)).source
  have hU : AttainableResidualRepairProfile G A U := by
    exact ⟨L.paths, L.linkage, Or.inl ⟨L.residual_unhindered, rfl⟩⟩
  refine ⟨U, hU, ?_⟩
  intro S hSc
  obtain ⟨P, hP, hprofile⟩ := hc hSc
  have hsubset := residualRepairProfile_subset_deleteSource hprofile
  have hsources :
      (G.delete (G.vertexSet P)).source =
        (G.delete (G.vertexSet L.paths)).source :=
    delete_vertexSet_source_eq_of_targetLinkage_update
      hNorm hA hP L.linkage
  simpa only [U, hsources] using hsubset

/-- The same safe linkage is a strict upper profile for every maximal
hindrance.  This also shows why the successor premise must use maximal
hindrances rather than arbitrary maximal waves. -/
theorem residualRepairProfileStrictImprovement_of_safeDesignated
    {G : DWeb V} (hNorm : G.IsNormalized)
    {A : Set V} (hA : A ⊆ G.source)
    (L : SafeDesignatedLinkage G A) :
    ResidualRepairProfileStrictImprovement G A := by
  intro P hP M _hMmax hMh
  let U := (G.delete (G.vertexSet L.paths)).source
  have hU : AttainableResidualRepairProfile G A U := by
    exact ⟨L.paths, L.linkage, Or.inl ⟨L.residual_unhindered, rfl⟩⟩
  have hsources :
      (G.delete (G.vertexSet P)).source =
        (G.delete (G.vertexSet L.paths)).source :=
    delete_vertexSet_source_eq_of_targetLinkage_update
      hNorm hA hP L.linkage
  have hsubset :
      (G.delete (G.vertexSet P)).initialSet M.1 ⊆ U := by
    simpa only [U, ← hsources] using M.2.2.1
  refine ⟨U, hU, hsubset, ?_⟩
  intro hback
  apply hMh.2
  apply Set.Subset.antisymm M.2.2.1
  intro x hxSource
  apply hback
  simpa only [U, ← hsources] using hxSource

/-- Local audit: once one initial target linkage exists, the two profile
Zorn premises together are equivalent to existence of the final safe
designated linkage.  Hence the order-theoretic helper does not hide the
limit construction in a choice of arbitrary maximal waves. -/
theorem residualProfileZornInputs_iff_safeDesignated
    (G : DWeb V) (hNorm : G.IsNormalized)
    {A : Set V} (hA : A ⊆ G.source)
    {P₀ : Set G.DPath} (hP₀ : IsLinkageBetween G A G.target P₀) :
    (ResidualRepairProfileChainUpperBounds G A ∧
        ResidualRepairProfileStrictImprovement G A) ↔
      Nonempty (SafeDesignatedLinkage G A) := by
  constructor
  · rintro ⟨hupper, himprove⟩
    exact exists_safeDesignatedLinkage_of_residualProfileZorn
      G hP₀ hupper himprove
  · rintro ⟨L⟩
    exact ⟨residualRepairProfileChainUpperBounds_of_safeDesignated
        hNorm hA L,
      residualRepairProfileStrictImprovement_of_safeDesignated
        hNorm hA L⟩

/-! ## Uniform lower-cardinal and public-machine form -/

/-- The two Zorn inputs in every deleted residual and for every request set
below the induction cardinal. -/
def ResidualProfileZornSelectionBelow
    (G : DWeb V) (kappa : Cardinal.{u}) : Prop :=
  ∀ (X A : Set V), (G.delete X).IsUnhindered →
    A ⊆ (G.delete X).source → #A < kappa →
      ResidualRepairProfileChainUpperBounds (G.delete X) A ∧
        ResidualRepairProfileStrictImprovement (G.delete X) A

/-- Lower cardinal induction supplies the first target linkage.  Profile
Zorn then reroutes it until its carrier deletion is genuinely unhindered,
giving the exact safe batch required by the completed-row recursion. -/
theorem safeBatchSelectionBelow_of_residualProfileZorn
    {G : DWeb V} (hNorm : G.IsNormalized) {kappa : Cardinal.{u}}
    (hlower : UniversalCardinalInductionBelow V kappa)
    (hprofile : ResidualProfileZornSelectionBelow G kappa) :
    SafeBatchSelectionBelow G kappa := by
  intro X A hresidual hA hAcard
  let P₀ := lowerChosenLinkage hNorm hlower X A hresidual hA hAcard
  have hP₀ : IsLinkageBetween (G.delete X) A (G.delete X).target P₀ :=
    lowerChosenLinkage_spec hNorm hlower X A hresidual hA hAcard
  obtain ⟨hupper, himprove⟩ := hprofile X A hresidual hA hAcard
  obtain ⟨S⟩ := exists_safeDesignatedLinkage_of_residualProfileZorn
    (G.delete X) hP₀ hupper himprove
  exact ⟨SafeBatchInDeletion.ofSafeDesignated S⟩

/-- Conversely, safe-batch selection supplies the greatest safe profile in
each instance, hence both Zorn inputs. -/
theorem residualProfileZornSelectionBelow_of_safeBatchSelection
    {G : DWeb V} (hNorm : G.IsNormalized) {kappa : Cardinal.{u}}
    (hselect : SafeBatchSelectionBelow G kappa) :
    ResidualProfileZornSelectionBelow G kappa := by
  intro X A hresidual hA hAcard
  obtain ⟨B⟩ := hselect X A hresidual hA hAcard
  let L : SafeDesignatedLinkage (G.delete X) A := B.toSafeDesignated
  exact ⟨
    residualRepairProfileChainUpperBounds_of_safeDesignated
      (isNormalized_delete hNorm X) hA L,
    residualRepairProfileStrictImprovement_of_safeDesignated
      (isNormalized_delete hNorm X) hA L⟩

/-- Uniform audit: under lower induction (which supplies the provisional
target linkage), the residual-profile Zorn inputs are exactly as strong as
the safe-batch selector. -/
theorem residualProfileZornSelectionBelow_iff_safeBatchSelection
    {G : DWeb V} (hNorm : G.IsNormalized) {kappa : Cardinal.{u}}
    (hlower : UniversalCardinalInductionBelow V kappa) :
    ResidualProfileZornSelectionBelow G kappa ↔
      SafeBatchSelectionBelow G kappa := by
  exact ⟨safeBatchSelectionBelow_of_residualProfileZorn hNorm hlower,
    residualProfileZornSelectionBelow_of_safeBatchSelection hNorm⟩

/-- Public singular extension clause from the source-faithful residual
profile iteration. -/
theorem singularExtensionClauseAt_of_residualProfileZorn
    (kappa : Cardinal.{u}) (hkappa : aleph0 < kappa)
    (hsingular : kappa.IsSingular)
    (hlower : UniversalCardinalInductionBelow V kappa)
    (Gamma : DWeb V) (hGamma : Gamma.IsUnhindered)
    (hprofile : ResidualProfileZornSelectionBelow
      Gamma.normalized kappa) :
    ExtensionClauseAt Gamma kappa := by
  apply SingularSafeCompletedMachine.singularExtensionClauseAt_of_safeBatchSelection
    kappa hkappa hsingular Gamma hGamma
  exact safeBatchSelectionBelow_of_residualProfileZorn
    Gamma.normalized_isNormalized hlower hprofile

#print axioms exists_attainableResidualRepairProfile_of_linkage
#print axioms exists_fullInitial_maximalWave
#print axioms exists_safeDesignatedLinkage_of_residualProfileZorn
#print axioms residualProfileZornInputs_iff_safeDesignated
#print axioms safeBatchSelectionBelow_of_residualProfileZorn
#print axioms residualProfileZornSelectionBelow_iff_safeBatchSelection
#print axioms singularExtensionClauseAt_of_residualProfileZorn

end SingularResidualProfileZorn
end CardinalInduction
end Erdos599
