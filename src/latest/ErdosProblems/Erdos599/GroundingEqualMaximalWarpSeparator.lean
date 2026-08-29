/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.Popular

/-!
# A maximal finite-warp separator for the equal branch

Strong popularity supplies a disjoint finite source--target warp, but not a
local stationary fan at every point of a popular separator.  For the equal
branch there is nevertheless a completely unconditional source of routes:
extend the supplied warp, by Zorn, to an inclusion-maximal finite warp.
The union of the vertices of a maximal warp separates its allowed sources
from the target.

The source-restricted form below is useful when one auxiliary source is
reserved.  If `A` is the set of sources allowed to start members of the
maximal warp and `R` covers the omitted sources, then
`finiteVertexSet M union R` separates the full source from the target.
Every non-`R` point of this separator lying on the warp has a literal prefix
route supplied by the unique member of `M` containing it.
-/

noncomputable section

open Set

namespace Erdos599
namespace Popular

open DirectedPath

universe u

variable {V : Type u} {Gamma : DWeb V}

/-- The vertices used by a concrete finite-path family. -/
def finiteVertexSet (P : Set (FinitePath Gamma.graph)) : Set V :=
  {x | exists p, p ∈ P ∧ x ∈ p.support}

@[simp] theorem mem_finiteVertexSet
    {P : Set (FinitePath Gamma.graph)} {x : V} :
    x ∈ finiteVertexSet P ↔ exists p, p ∈ P ∧ x ∈ p.support :=
  Iff.rfl

/-- A maximal finite warp whose paths may start only in `A` and must end in
`T`.  Maximality is stated in the local form used by the separator proof:
every further admissible path disjoint from the current carrier is already a
member of the warp. -/
structure MaximalRestrictedXSWarp
    (Gamma : DWeb V) (A T : Set V) extends FiniteWarp Gamma where
  starts_in_allowed : ∀ {p}, p ∈ paths → p.start ∈ A
  ends_in_target : ∀ {p}, p ∈ paths → p.finish ∈ T
  maximal_disjoint : ∀ (p : FinitePath Gamma.graph),
    p.start ∈ A → p.finish ∈ T →
    Disjoint p.support (finiteVertexSet paths) → p ∈ paths

namespace MaximalRestrictedXSWarp

variable {A T : Set V}

/-- Forget the source restriction when the allowed sources lie in the web
source. -/
def toXSWarp (M : MaximalRestrictedXSWarp Gamma A T)
    (hA : A ⊆ Gamma.source) : XSWarp Gamma T where
  paths := M.paths
  disjoint := M.disjoint
  starts_in_source hp := hA (M.starts_in_allowed hp)
  ends_in_target := M.ends_in_target

/-- Every member contributes all of its vertices to the finite carrier. -/
theorem support_subset_finiteVertexSet
    (M : MaximalRestrictedXSWarp Gamma A T) {p : FinitePath Gamma.graph}
    (hp : p ∈ M.paths) : p.support ⊆ finiteVertexSet M.paths := by
  intro x hx
  exact ⟨p, hp, hx⟩

/-- The carrier of a maximal restricted warp separates all allowed sources
from its target set. -/
theorem finiteVertexSet_isSeparatorFrom
    (M : MaximalRestrictedXSWarp Gamma A Gamma.target) :
    ∀ p : FinitePath Gamma.graph, p.start ∈ A →
      p.finish ∈ Gamma.target →
      (p.support ∩ finiteVertexSet M.paths).Nonempty := by
  intro p hpA hpT
  by_contra hempty
  have hdisjoint : Disjoint p.support (finiteVertexSet M.paths) := by
    rw [Set.disjoint_left]
    intro x hxp hxM
    exact hempty ⟨x, hxp, hxM⟩
  have hpM : p ∈ M.paths := M.maximal_disjoint p hpA hpT hdisjoint
  exact hempty ⟨p.start, p.start_mem_support,
    ⟨p, hpM, p.start_mem_support⟩⟩

/-- If `R` contains every source omitted from the allowed set `A`, adjoining
`R` to the maximal-warp carrier separates the full web source. -/
theorem finiteVertexSet_union_isSeparator
    (M : MaximalRestrictedXSWarp Gamma A Gamma.target) (R : Set V)
    (hsource : Gamma.source ⊆ A ∪ R) :
    IsSeparator Gamma (finiteVertexSet M.paths ∪ R) := by
  intro p hpSource hpTarget
  rcases hsource hpSource with hpA | hpR
  · obtain ⟨x, hxp, hxM⟩ :=
      M.finiteVertexSet_isSeparatorFrom p hpA hpTarget
    exact ⟨x, hxp, Or.inl hxM⟩
  · exact ⟨p.start, p.start_mem_support, Or.inr hpR⟩

/-- Reserve one source vertex.  A maximal warp on all the other sources,
together with the reserved singleton, separates the original source from
the target. -/
theorem finiteVertexSet_union_singleton_isSeparator
    (r : V)
    (M : MaximalRestrictedXSWarp Gamma (Gamma.source \ {r}) Gamma.target) :
    IsSeparator Gamma (finiteVertexSet M.paths ∪ {r}) := by
  apply M.finiteVertexSet_union_isSeparator {r}
  intro x hx
  by_cases hxr : x = r
  · exact Or.inr (hxr ▸ Set.mem_singleton r)
  · exact Or.inl ⟨hx, by simpa using hxr⟩

end MaximalRestrictedXSWarp

/-- Zorn extension of a seed warp, with a possibly smaller allowed source
set.  The seed is retained literally. -/
theorem XSWarp.exists_maximalRestricted_extension
    {A T : Set V} (P : XSWarp Gamma T)
    (hPA : ∀ {p}, p ∈ P.paths → p.start ∈ A) :
    ∃ M : MaximalRestrictedXSWarp Gamma A T, P.paths ⊆ M.paths := by
  let Good : Set (Set (FinitePath Gamma.graph)) :=
    {Q | P.paths ⊆ Q ∧
      Q.PairwiseDisjoint FinitePath.support ∧
      (∀ {p}, p ∈ Q → p.start ∈ A) ∧
      (∀ {p}, p ∈ Q → p.finish ∈ T)}
  have hseed : Good P.paths :=
    ⟨Set.Subset.rfl, P.disjoint, hPA, P.ends_in_target⟩
  obtain ⟨Q, hPQ, hQmax⟩ := zorn_subset_nonempty Good (by
    intro c hcGood hcChain hcne
    refine ⟨⋃₀ c, ?_, fun Q hQc ↦ Set.subset_sUnion_of_mem hQc⟩
    refine ⟨?_, ?_, ?_, ?_⟩
    · obtain ⟨Q, hQc⟩ := hcne
      exact (hcGood hQc).1.trans (Set.subset_sUnion_of_mem hQc)
    · intro p hp q hq hpq
      obtain ⟨Pset, hPc, hpP⟩ := Set.mem_sUnion.1 hp
      obtain ⟨Qset, hQc, hqQ⟩ := Set.mem_sUnion.1 hq
      by_cases hPQset : Pset = Qset
      · subst Qset
        exact (hcGood hPc).2.1 hpP hqQ hpq
      · rcases hcChain hPc hQc hPQset with hPQ | hQP
        · exact (hcGood hQc).2.1 (hPQ hpP) hqQ hpq
        · exact (hcGood hPc).2.1 hpP (hQP hqQ) hpq
    · intro p hp
      obtain ⟨Qset, hQc, hpQ⟩ := Set.mem_sUnion.1 hp
      exact (hcGood hQc).2.2.1 hpQ
    · intro p hp
      obtain ⟨Qset, hQc, hpQ⟩ := Set.mem_sUnion.1 hp
      exact (hcGood hQc).2.2.2 hpQ) P.paths hseed
  refine ⟨{
      paths := Q
      disjoint := hQmax.1.2.1
      starts_in_allowed := hQmax.1.2.2.1
      ends_in_target := hQmax.1.2.2.2
      maximal_disjoint := ?_ }, hPQ⟩
  intro p hpA hpT hpdisj
  let Q' : Set (FinitePath Gamma.graph) := insert p Q
  have hQ'disjoint : Q'.PairwiseDisjoint FinitePath.support := by
    intro q hq r hr hqr
    simp only [Q', Set.mem_insert_iff] at hq hr
    rcases hq with rfl | hqQ
    · rcases hr with rfl | hrQ
      · exact False.elim (hqr rfl)
      · exact Set.disjoint_left.2 fun x hxp hxr ↦
          Set.disjoint_left.1 hpdisj hxp ⟨r, hrQ, hxr⟩
    · rcases hr with rfl | hrQ
      · exact Set.disjoint_left.2 fun x hxq hxp ↦
          Set.disjoint_left.1 hpdisj hxp ⟨q, hqQ, hxq⟩
      · exact hQmax.1.2.1 hqQ hrQ hqr
  have hQ'good : Good Q' := by
    refine ⟨hQmax.1.1.trans (Set.subset_insert p Q), hQ'disjoint, ?_, ?_⟩
    · intro q hq
      rcases hq with rfl | hqQ
      · exact hpA
      · exact hQmax.1.2.2.1 hqQ
    · intro q hq
      rcases hq with rfl | hqQ
      · exact hpT
      · exact hQmax.1.2.2.2 hqQ
  have hQ'sub : Q' ⊆ Q := hQmax.2 hQ'good (Set.subset_insert p Q)
  exact hQ'sub (Set.mem_insert p Q)

/-- Unrestricted source specialization. -/
theorem XSWarp.exists_maximal_extension
    {T : Set V} (P : XSWarp Gamma T) :
    ∃ M : MaximalRestrictedXSWarp Gamma Gamma.source T,
      P.paths ⊆ M.paths :=
  P.exists_maximalRestricted_extension P.starts_in_source

end Popular
end Erdos599

#print axioms Erdos599.Popular.XSWarp.exists_maximalRestricted_extension
#print axioms Erdos599.Popular.MaximalRestrictedXSWarp.finiteVertexSet_union_isSeparator
