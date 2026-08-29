/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.GroundingEqualMaximalWarpSeparator

/-!
# Maximal auxiliary warps avoiding a reserved carrier

The equal grounding branch reserves one inessential ladder parent.  An
unrestricted maximal auxiliary warp can cross that parent after decoding,
which destroys the unused-source invariant.  The correct Zorn family
therefore contains only paths avoiding a prescribed auxiliary collision
carrier `X`.

The resulting carrier need not separate *all* source--target paths.  It has
the sharper property actually used by active closure: every admissible
source--target path avoiding `X` meets the maximal carrier.  Thus it can be
applied to the canonical clean route supplied by each essential hanging
component, while all selected routes remain disjoint from the reserved
parent after decoding.
-/

noncomputable section

open Set

namespace Erdos599
namespace Popular

open DirectedPath

universe u

variable {V : Type u} {Gamma : DWeb V}

namespace XSWarp

/-- Remove one literal member from a finite warp. -/
def erasePath {T : Set V} (P : XSWarp Gamma T)
    (q : FinitePath Gamma.graph) : XSWarp Gamma T where
  paths := P.paths \ {q}
  disjoint := by
    intro p hp r hr hpr
    exact P.disjoint hp.1 hr.1 hpr
  starts_in_source hp := P.starts_in_source hp.1
  ends_in_target hp := P.ends_in_target hp.1

@[simp] theorem mem_erasePath_paths
    {T : Set V} (P : XSWarp Gamma T) (q p : FinitePath Gamma.graph) :
    p ∈ (P.erasePath q).paths ↔ p ∈ P.paths ∧ p ≠ q := by
  simp [erasePath]

/-- After removing a member `q`, no remaining member starts at `q.start`.
This is the source restriction needed to reserve the original source encoded
by `q`. -/
theorem erasePath_starts_in_source_sdiff_singleton
    {T : Set V} (P : XSWarp Gamma T) {q : FinitePath Gamma.graph}
    (hq : q ∈ P.paths) {p : FinitePath Gamma.graph}
    (hp : p ∈ (P.erasePath q).paths) :
    p.start ∈ Gamma.source \ {q.start} := by
  refine ⟨P.starts_in_source hp.1, ?_⟩
  simpa only [Set.mem_singleton_iff] using fun hstart : p.start = q.start ↦
    hp.2 (P.eq_of_start_eq hp.1 hq hstart)

/-- If every member avoids `X` and `r ∈ X`, then every member starts at a
source different from `r`. -/
theorem starts_in_source_sdiff_singleton_of_avoids
    {T X : Set V} (P : XSWarp Gamma T) {r : V} (hrX : r ∈ X)
    (hPX : ∀ {p}, p ∈ P.paths → Disjoint p.support X)
    {p : FinitePath Gamma.graph} (hp : p ∈ P.paths) :
    p.start ∈ Gamma.source \ {r} := by
  refine ⟨P.starts_in_source hp, ?_⟩
  simpa only [Set.mem_singleton_iff] using fun hstart : p.start = r ↦
    Set.disjoint_left.1 (hPX hp) p.start_mem_support (hstart ▸ hrX)

end XSWarp

/-- A source-restricted maximal finite warp all of whose members avoid `X`.
Maximality is only asserted against further admissible paths avoiding `X`;
this is exactly what is needed for collision-safe active closure. -/
structure MaximalAvoidingRestrictedXSWarp
    (Gamma : DWeb V) (A T X : Set V) extends FiniteWarp Gamma where
  starts_in_allowed : ∀ {p}, p ∈ paths → p.start ∈ A
  ends_in_target : ∀ {p}, p ∈ paths → p.finish ∈ T
  paths_avoid : ∀ {p}, p ∈ paths → Disjoint p.support X
  maximal_disjoint : ∀ (p : FinitePath Gamma.graph),
    p.start ∈ A → p.finish ∈ T → Disjoint p.support X →
    Disjoint p.support (finiteVertexSet paths) → p ∈ paths

namespace MaximalAvoidingRestrictedXSWarp

variable {A T X : Set V}

/-- Every admissible clean source--target path meets the carrier of a
maximal avoiding warp. -/
theorem finiteVertexSet_meets
    (M : MaximalAvoidingRestrictedXSWarp Gamma A T X)
    (p : FinitePath Gamma.graph) (hpA : p.start ∈ A)
    (hpT : p.finish ∈ T) (hpX : Disjoint p.support X) :
    (p.support ∩ finiteVertexSet M.paths).Nonempty := by
  by_contra hempty
  have hdisjoint : Disjoint p.support (finiteVertexSet M.paths) := by
    rw [Set.disjoint_left]
    intro x hxp hxM
    exact hempty ⟨x, hxp, hxM⟩
  have hpM : p ∈ M.paths :=
    M.maximal_disjoint p hpA hpT hpX hdisjoint
  exact hempty ⟨p.start, p.start_mem_support,
    ⟨p, hpM, p.start_mem_support⟩⟩

/-- Every selected member remains disjoint from the prescribed collision
carrier. -/
theorem finiteVertexSet_disjoint
    (M : MaximalAvoidingRestrictedXSWarp Gamma A T X) :
    Disjoint (finiteVertexSet M.paths) X := by
  rw [Set.disjoint_left]
  rintro x ⟨p, hpM, hxp⟩ hxX
  exact Set.disjoint_left.1 (M.paths_avoid hpM) hxp hxX

end MaximalAvoidingRestrictedXSWarp

/-- Zorn-extend a seed warp inside the class of paths which avoid `X`.
The seed is retained literally. -/
theorem XSWarp.exists_maximalAvoidingRestricted_extension
    {A T X : Set V} (P : XSWarp Gamma T)
    (hPA : ∀ {p}, p ∈ P.paths → p.start ∈ A)
    (hPX : ∀ {p}, p ∈ P.paths → Disjoint p.support X) :
    ∃ M : MaximalAvoidingRestrictedXSWarp Gamma A T X,
      P.paths ⊆ M.paths := by
  let Good : Set (Set (FinitePath Gamma.graph)) :=
    {Q | P.paths ⊆ Q ∧
      Q.PairwiseDisjoint FinitePath.support ∧
      (∀ {p}, p ∈ Q → p.start ∈ A) ∧
      (∀ {p}, p ∈ Q → p.finish ∈ T) ∧
      (∀ {p}, p ∈ Q → Disjoint p.support X)}
  have hseed : Good P.paths :=
    ⟨Set.Subset.rfl, P.disjoint, hPA, P.ends_in_target, hPX⟩
  obtain ⟨Q, hPQ, hQmax⟩ := zorn_subset_nonempty Good (by
    intro c hcGood hcChain hcne
    refine ⟨⋃₀ c, ?_, fun Q hQc ↦ Set.subset_sUnion_of_mem hQc⟩
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
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
      exact (hcGood hQc).2.2.2.1 hpQ
    · intro p hp
      obtain ⟨Qset, hQc, hpQ⟩ := Set.mem_sUnion.1 hp
      exact (hcGood hQc).2.2.2.2 hpQ) P.paths hseed
  refine ⟨{
      paths := Q
      disjoint := hQmax.1.2.1
      starts_in_allowed := hQmax.1.2.2.1
      ends_in_target := hQmax.1.2.2.2.1
      paths_avoid := hQmax.1.2.2.2.2
      maximal_disjoint := ?_ }, hPQ⟩
  intro p hpA hpT hpX hpdisj
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
    refine ⟨hQmax.1.1.trans (Set.subset_insert p Q), hQ'disjoint,
      ?_, ?_, ?_⟩
    · intro q hq
      rcases hq with rfl | hqQ
      · exact hpA
      · exact hQmax.1.2.2.1 hqQ
    · intro q hq
      rcases hq with rfl | hqQ
      · exact hpT
      · exact hQmax.1.2.2.2.1 hqQ
    · intro q hq
      rcases hq with rfl | hqQ
      · exact hpX
      · exact hQmax.1.2.2.2.2 hqQ
  have hQ'sub : Q' ⊆ Q := hQmax.2 hQ'good (Set.subset_insert p Q)
  exact hQ'sub (Set.mem_insert p Q)

/-- Reserve one member of an avoiding seed warp and maximize all remaining
paths among sources different from its initial vertex. -/
theorem XSWarp.exists_maximalAvoiding_extension_erase
    {T X : Set V} (P : XSWarp Gamma T)
    {q : FinitePath Gamma.graph} (hq : q ∈ P.paths)
    (hPX : ∀ {p}, p ∈ P.paths → Disjoint p.support X) :
    ∃ M : MaximalAvoidingRestrictedXSWarp Gamma
        (Gamma.source \ {q.start}) T X,
      P.paths \ {q} ⊆ M.paths := by
  have hstarts : ∀ {p}, p ∈ (P.erasePath q).paths →
      p.start ∈ Gamma.source \ {q.start} := by
    intro p hp
    exact P.erasePath_starts_in_source_sdiff_singleton hq hp
  have havoids : ∀ {p}, p ∈ (P.erasePath q).paths →
      Disjoint p.support X := by
    intro p hp
    exact hPX hp.1
  simpa only [XSWarp.erasePath] using
    (P.erasePath q).exists_maximalAvoidingRestricted_extension
      hstarts havoids

/-- Maximize an avoiding seed while reserving a prescribed point of the
forbidden carrier as an unused source. -/
theorem XSWarp.exists_maximalAvoiding_reserving
    {T X : Set V} (P : XSWarp Gamma T) {r : V} (hrX : r ∈ X)
    (hPX : ∀ {p}, p ∈ P.paths → Disjoint p.support X) :
    ∃ M : MaximalAvoidingRestrictedXSWarp Gamma
        (Gamma.source \ {r}) T X,
      P.paths ⊆ M.paths := by
  exact P.exists_maximalAvoidingRestricted_extension
    (fun {_} hp ↦
      P.starts_in_source_sdiff_singleton_of_avoids hrX hPX hp)
    hPX

end Popular
end Erdos599

#print axioms Erdos599.Popular.XSWarp.exists_maximalAvoidingRestricted_extension
#print axioms Erdos599.Popular.XSWarp.exists_maximalAvoiding_extension_erase
#print axioms Erdos599.Popular.XSWarp.exists_maximalAvoiding_reserving
#print axioms Erdos599.Popular.MaximalAvoidingRestrictedXSWarp.finiteVertexSet_meets
#print axioms Erdos599.Popular.MaximalAvoidingRestrictedXSWarp.finiteVertexSet_disjoint
