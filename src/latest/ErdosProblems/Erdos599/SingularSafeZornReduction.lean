/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.AlternativeMaximalLinkage
import ErdosProblems.Erdos599.SingularCertifiedSafeHistory

/-!
# A Zorn reduction for ambiently safe designated linkages

Order safely deletable target linkages by literal inclusion of their path
families.  The certified one-point theorem proves that a maximal candidate
must cover every requested source.  The only limit issue is the existence of
chain upper bounds.

For a chain of candidates, its literal union is automatically a finite
target linkage: finite character is memberwise, while pairwise disjointness
follows by comparing the two chain stages containing any two paths.  Thus the
only missing field for the union is that deleting its complete carrier is
unhindered.  This file isolates that continuity assertion and proves the
entire Zorn argument from it; it does not assume that arbitrary safe chains
have this property.
-/

noncomputable section

open Set

namespace Erdos599
namespace CardinalInduction
namespace SingularSafeZornReduction

open SingularCertifiedSafeHistory
open SingularSafeDesignatedLinkage

universe u

variable {V : Type u}

/-- A target linkage on some subset of the requested set whose whole carrier
is ambiently safely deletable.  The initial set is read from the path family,
so candidates with the same paths are definitionally comparable. -/
def IsSafeCandidate (G : DWeb V) (A : Set V) (P : Set G.DPath) : Prop :=
  G.initialSet P ⊆ A ∧
    IsLinkageBetween G (G.initialSet P) G.target P ∧
      (G.delete (G.vertexSet P)).IsUnhindered

/-- The exact upper-bound input needed by the literal-inclusion Zorn order. -/
def SafeCandidateChainUpperBounds (G : DWeb V) (A : Set V) : Prop :=
  ∀ c : Set (Set G.DPath),
    c ⊆ {P | IsSafeCandidate G A P} → IsChain (· ⊆ ·) c →
      ∃ U, IsSafeCandidate G A U ∧ ∀ P ∈ c, P ⊆ U

/-- The chain-union residual continuity assertion.  All other candidate
fields for `⋃₀ c` are proved below. -/
def SafeChainUnionResidualContinuity (G : DWeb V) (A : Set V) : Prop :=
  ∀ c : Set (Set G.DPath),
    c ⊆ {P | IsSafeCandidate G A P} → IsChain (· ⊆ ·) c →
      (G.delete (G.vertexSet (⋃₀ c))).IsUnhindered

theorem empty_isSafeCandidate
    (G : DWeb V) (hG : G.IsUnhindered) (A : Set V) :
    IsSafeCandidate G A ∅ := by
  refine ⟨by simp [DWeb.initialSet], ?_, ?_⟩
  · simpa [DWeb.initialSet] using empty_linkage G
  have hvertex : G.vertexSet (∅ : Set G.DPath) = ∅ := by
    ext x
    simp [DWeb.vertexSet]
  rw [hvertex]
  simpa using hG

/-- A literal chain union is still a linkage.  This is the complete
structural compactness part; no residual-safety assumption occurs here. -/
theorem sUnion_isLinkageBetween
    (G : DWeb V) (hNorm : G.IsNormalized) {A : Set V}
    (hA : A ⊆ G.source)
    {c : Set (Set G.DPath)}
    (hc : c ⊆ {P | IsSafeCandidate G A P})
    (hchain : IsChain (· ⊆ ·) c) :
    IsLinkageBetween G (G.initialSet (⋃₀ c)) G.target (⋃₀ c) := by
  have hwarp : G.IsWarp (⋃₀ c) := by
    intro p hp q hq hpq
    obtain ⟨P, hPc, hpP⟩ := Set.mem_sUnion.1 hp
    obtain ⟨Q, hQc, hqQ⟩ := Set.mem_sUnion.1 hq
    by_cases hPQeq : P = Q
    · subst Q
      exact (hc hPc).2.1.isWarp hpP hqQ hpq
    · rcases hchain hPc hQc hPQeq with hPQ | hQP
      · exact (hc hQc).2.1.isWarp (hPQ hpP) hqQ hpq
      · exact (hc hPc).2.1.isWarp hpP (hQP hqQ) hpq
  have hfinite : G.HasFiniteCharacter (⋃₀ c) := by
    intro p hp
    obtain ⟨P, hPc, hpP⟩ := Set.mem_sUnion.1 hp
    exact (hc hPc).2.1.finiteCharacter hpP
  have hinitial : G.initialSet (⋃₀ c) ⊆ G.source := by
    rintro x ⟨p, hp, rfl⟩
    obtain ⟨P, hPc, hpP⟩ := Set.mem_sUnion.1 hp
    have hpInitial : p.initial ∈ G.initialSet P := ⟨p, hpP, rfl⟩
    exact hA ((hc hPc).1 hpInitial)
  have hterminal : G.terminalFrontier (⋃₀ c) ⊆ G.target := by
    rintro x ⟨p, hp, hpx⟩
    obtain ⟨P, hPc, hpP⟩ := Set.mem_sUnion.1 hp
    exact (hc hPc).2.1.terminalFrontier_subset ⟨p, hpP, hpx⟩
  have hclean : G.IsCleanFiniteWarp (⋃₀ c) :=
    AlternativeMaximalLinkage.cleanFiniteWarp_of_normalized
      hNorm hwarp hfinite hinitial hterminal
  exact AlternativeMaximalLinkage.isLinkageBetween_of_cleanFiniteWarp_of_normalized
    hNorm hclean

/-- Initials of a chain union remain within the requested set. -/
theorem initialSet_sUnion_subset
    (G : DWeb V) {A : Set V} {c : Set (Set G.DPath)}
    (hc : c ⊆ {P | IsSafeCandidate G A P}) :
    G.initialSet (⋃₀ c) ⊆ A := by
  rintro x ⟨p, hp, rfl⟩
  obtain ⟨P, hPc, hpP⟩ := Set.mem_sUnion.1 hp
  exact (hc hPc).1 ⟨p, hpP, rfl⟩

/-- Residual continuity makes the literal union an upper candidate. -/
theorem safeCandidateChainUpperBounds_of_unionResidualContinuity
    (G : DWeb V) (hNorm : G.IsNormalized) (A : Set V)
    (hA : A ⊆ G.source)
    (hcontinuity : SafeChainUnionResidualContinuity G A) :
    SafeCandidateChainUpperBounds G A := by
  intro c hc hchain
  refine ⟨⋃₀ c, ⟨initialSet_sUnion_subset G hc,
    sUnion_isLinkageBetween G hNorm hA hc hchain,
    hcontinuity c hc hchain⟩, ?_⟩
  intro P hPc
  exact Set.subset_sUnion_of_mem hPc

/-- The certified one-point extension strictly enlarges any candidate which
does not yet cover all requested sources. -/
theorem exists_strict_safeCandidate_extension
    (G : DWeb V) (hNorm : G.IsNormalized)
    {A : Set V} (hA : A ⊆ G.source) {P : Set G.DPath}
    (hP : IsSafeCandidate G A P)
    (hmissing : G.initialSet P ≠ A) :
    ∃ Q, IsSafeCandidate G A Q ∧ P ⊆ Q ∧ ¬ Q ⊆ P := by
  have hnreverse : ¬ A ⊆ G.initialSet P := by
    intro hreverse
    exact hmissing (Set.Subset.antisymm hP.1 hreverse)
  obtain ⟨a, haA, haFresh⟩ := Set.not_subset.mp hnreverse
  let old : SafeDesignatedLinkage G (G.initialSet P) :=
    { paths := P
      linkage := hP.2.1
      residual_unhindered := hP.2.2 }
  have hOldSource : G.initialSet P ⊆ G.source := hP.1.trans hA
  obtain ⟨E⟩ := exists_certifiedSafeDesignatedExtension
    G hNorm old hOldSource (hA haA) haFresh
  refine ⟨E.extended.paths, ?_, E.old_subset_paths, ?_⟩
  · refine ⟨?_, ?_, E.extended.residual_unhindered⟩
    rw [E.extended.linkage.initialSet_eq]
    exact Set.insert_subset haA hP.1
    rw [E.extended.linkage.initialSet_eq]
    exact E.extended.linkage
  · intro hnewOld
    have haInitial : a ∈ G.initialSet E.extended.paths := by
      rw [E.extended.linkage.initialSet_eq]
      exact Set.mem_insert a _
    obtain ⟨q, hqNew, hqa⟩ := haInitial
    have hqOld : q ∈ P := hnewOld hqNew
    have haOld : a ∈ G.initialSet P := ⟨q, hqOld, hqa⟩
    exact haFresh haOld

/-- Zorn plus certified safe one-point extension.  Chain upper bounds are
the only global input. -/
theorem exists_safeDesignatedLinkage_of_chainUpperBounds
    (G : DWeb V) (hNorm : G.IsNormalized) (_hG : G.IsUnhindered)
    {A : Set V} (hA : A ⊆ G.source)
    (hchain : SafeCandidateChainUpperBounds G A) :
    Nonempty (SafeDesignatedLinkage G A) := by
  let Good : Set (Set G.DPath) := {P | IsSafeCandidate G A P}
  have hzorn : ∀ c ⊆ Good, IsChain (· ⊆ ·) c →
      ∃ U ∈ Good, ∀ P ∈ c, P ⊆ U := by
    intro c hc hcc
    obtain ⟨U, hU, hupper⟩ := hchain c hc hcc
    exact ⟨U, hU, hupper⟩
  obtain ⟨P, hP, hPmax⟩ := zorn_subset Good hzorn
  by_cases hcover : G.initialSet P = A
  · exact ⟨{
      paths := P
      linkage := hcover ▸ hP.2.1
      residual_unhindered := hP.2.2 }⟩
  · obtain ⟨Q, hQ, hPQ, hnQP⟩ :=
      exists_strict_safeCandidate_extension G hNorm hA hP hcover
    exact False.elim (hnQP (hPmax hQ hPQ))

/-- Fully reduced form: it is enough to prove residual unhinderedness for
literal unions of safe chains. -/
theorem exists_safeDesignatedLinkage_of_unionResidualContinuity
    (G : DWeb V) (hNorm : G.IsNormalized) (hG : G.IsUnhindered)
    {A : Set V} (hA : A ⊆ G.source)
    (hcontinuity : SafeChainUnionResidualContinuity G A) :
    Nonempty (SafeDesignatedLinkage G A) := by
  apply exists_safeDesignatedLinkage_of_chainUpperBounds G hNorm hG hA
  exact safeCandidateChainUpperBounds_of_unionResidualContinuity
    G hNorm A hA hcontinuity

#print axioms sUnion_isLinkageBetween
#print axioms exists_strict_safeCandidate_extension
#print axioms exists_safeDesignatedLinkage_of_unionResidualContinuity

end SingularSafeZornReduction
end CardinalInduction
end Erdos599
