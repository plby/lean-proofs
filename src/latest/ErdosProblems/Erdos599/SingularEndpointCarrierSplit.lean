/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.SingularSafeCarrierCardinal
import ErdosProblems.Erdos599.SingularSafeTreeResurrection

/-!
# Splitting a small linkage carrier at its two endpoint colours

The whole non-source carrier of a target linkage is not an admissible input
to the ordinary deletion--quotient arrow: it contains the used target
vertices, and those vertices give unavoidable trivial source--target paths
in the quotient.  This file records the exact replacement.

In a normalized web, a target linkage carrier consists of three explicit
parts: its prescribed source set, an internal set disjoint from both ambient
endpoint sets, and its terminal frontier.  Thus only the internal part is an
ordinary source/target-disjoint restoration problem.  The terminal part is
precisely the colour which a marked alternating exchange must retain.
-/

noncomputable section

open Cardinal Set

namespace Erdos599
namespace CardinalInduction
namespace SingularEndpointCarrierSplit

open SingularSafeCarrierCardinal SingularSafeTreeResurrection

universe u

variable {V : Type u}

/-- The part of a path-family carrier which is neither an ambient source nor
an ambient target. -/
def internalCarrier (G : DWeb V) (P : Set G.DPath) : Set V :=
  G.vertexSet P \ (G.source ∪ G.target)

/-- The internal carrier is disjoint from the ambient source. -/
theorem disjoint_source_internalCarrier (G : DWeb V) (P : Set G.DPath) :
    Disjoint G.source (internalCarrier G P) := by
  rw [Set.disjoint_left]
  rintro x hxSource hxInternal
  exact hxInternal.2 (Or.inl hxSource)

/-- The internal carrier is also disjoint from the ambient target. -/
theorem disjoint_target_internalCarrier (G : DWeb V) (P : Set G.DPath) :
    Disjoint G.target (internalCarrier G P) := by
  rw [Set.disjoint_left]
  rintro x hxTarget hxInternal
  exact hxInternal.2 (Or.inr hxTarget)

/-- In a normalized target linkage, the target-coloured part of the carrier
is exactly its terminal frontier. -/
theorem vertexSet_inter_target_eq_terminalFrontier
    {G : DWeb V} (hNorm : G.IsNormalized)
    {A : Set V} {P : Set G.DPath}
    (hP : IsLinkageBetween G A G.target P) :
    G.vertexSet P ∩ G.target = G.terminalFrontier P := by
  apply Set.Subset.antisymm
  · exact vertexSet_inter_target_subset_terminalFrontier hNorm hP
  · rintro x ⟨p, hpP, hpx⟩
    exact ⟨⟨p, hpP, G.terminal_mem_support hpx⟩,
      hP.terminalFrontier_subset ⟨p, hpP, hpx⟩⟩

/-- In a normalized target linkage, the source-coloured part of the carrier
is exactly its prescribed initial set. -/
theorem vertexSet_inter_source_eq_initial
    {G : DWeb V} (hNorm : G.IsNormalized)
    {A : Set V} (hA : A ⊆ G.source) {P : Set G.DPath}
    (hP : IsLinkageBetween G A G.target P) :
    G.vertexSet P ∩ G.source = A := by
  apply Set.Subset.antisymm
  · rintro x ⟨⟨p, hpP, hxp⟩, hxSource⟩
    have hxInitial : x = p.initial :=
      hNorm.eq_initial_of_mem_path p hxp hxSource
    rw [hxInitial, ← hP.initialSet_eq]
    exact ⟨p, hpP, rfl⟩
  · intro x hxA
    have hxInitial : x ∈ G.initialSet P := hP.initialSet_eq.symm ▸ hxA
    obtain ⟨p, hpP, rfl⟩ := hxInitial
    exact ⟨⟨p, hpP, p.initial_mem_support⟩, hA hxA⟩

/-- Exact three-colour decomposition of a normalized target-linkage carrier.
The union is not asserted disjoint because an ambient source may also be a
target; such a vertex is already handled by the endpoint colours. -/
theorem vertexSet_eq_initial_union_internal_union_terminal
    {G : DWeb V} (hNorm : G.IsNormalized)
    {A : Set V} (hA : A ⊆ G.source) {P : Set G.DPath}
    (hP : IsLinkageBetween G A G.target P) :
    G.vertexSet P =
      A ∪ internalCarrier G P ∪ G.terminalFrontier P := by
  ext x
  constructor
  · intro hx
    by_cases hxSource : x ∈ G.source
    · apply Or.inl
      apply Or.inl
      rw [← vertexSet_inter_source_eq_initial hNorm hA hP]
      exact ⟨hx, hxSource⟩
    · by_cases hxTarget : x ∈ G.target
      · apply Or.inr
        rw [← vertexSet_inter_target_eq_terminalFrontier hNorm hP]
        exact ⟨hx, hxTarget⟩
      · exact Or.inl (Or.inr ⟨hx, by simp [hxSource, hxTarget]⟩)
  · rintro (hxLeft | hxTerminal)
    · rcases hxLeft with hxA | hxInternal
      · rw [← vertexSet_inter_source_eq_initial hNorm hA hP] at hxA
        exact hxA.1
      · exact hxInternal.1
    · obtain ⟨p, hpP, hpx⟩ := hxTerminal
      exact ⟨p, hpP, G.terminal_mem_support hpx⟩

/-- After the automatic source restoration, the remaining carrier splits
into the genuinely internal set and precisely the non-source used target
frontier.  This is the corrected domain for a coloured general arrow. -/
theorem nonSourceCarrier_eq_internal_union_terminal_sdiff_source
    {G : DWeb V} (hNorm : G.IsNormalized)
    {A : Set V} (hA : A ⊆ G.source) {P : Set G.DPath}
    (hP : IsLinkageBetween G A G.target P) :
    G.vertexSet P \ G.source =
      internalCarrier G P ∪ (G.terminalFrontier P \ G.source) := by
  rw [vertexSet_eq_initial_union_internal_union_terminal hNorm hA hP]
  ext x
  simp only [Set.mem_sdiff, Set.mem_union]
  constructor
  · rintro ⟨hxLeft | hxTerminal, hxNotSource⟩
    · rcases hxLeft with hxA | hxInternal
      · exact False.elim (hxNotSource (hA hxA))
      · exact Or.inl hxInternal
    · exact Or.inr ⟨hxTerminal, hxNotSource⟩
  · rintro (hxInternal | ⟨hxTerminal, hxNotSource⟩)
    · exact ⟨Or.inl (Or.inr hxInternal),
        fun hxSource ↦ hxInternal.2 (Or.inl hxSource)⟩
    · exact ⟨Or.inr hxTerminal, hxNotSource⟩

/-- The genuinely internal carrier remains below the induction cardinal.
Unlike the whole non-source carrier, it is disjoint from both endpoint sets. -/
theorem mk_internalCarrier_lt
    {G : DWeb V} {A : Set V} {P : Set G.DPath}
    {kappa : Cardinal.{u}}
    (hkappa : aleph0 < kappa)
    (hP : IsLinkageBetween G A G.target P)
    (hA : #A < kappa) :
    #(internalCarrier G P) < kappa := by
  exact (Cardinal.mk_le_mk_of_subset Set.sdiff_subset).trans_lt
    (mk_vertexSet_lt_of_mk_initial_lt hkappa hP hA)

#print axioms vertexSet_inter_target_eq_terminalFrontier
#print axioms vertexSet_inter_source_eq_initial
#print axioms vertexSet_eq_initial_union_internal_union_terminal
#print axioms nonSourceCarrier_eq_internal_union_terminal_sdiff_source
#print axioms mk_internalCarrier_lt

end SingularEndpointCarrierSplit
end CardinalInduction
end Erdos599
