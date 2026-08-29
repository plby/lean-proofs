/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.ColouredSafeCapturedStageLinking

/-!
# Protected continuation through a weak native imaginary edge

A successor-sized hammock which has no equally large nondegenerate
subhammock has a successor-sized degenerate subhammock. Choosing from the
latter after reserving a small reference-closed carrier produces an actual
finite path between the old endpoints. The reference can contain rays.

The roofed version retains a fixed-stage carrier filter. It does not infer
uniform capture from member-dependent existential stage capture, and it
does not assert a simultaneous blueprint extension.
-/

noncomputable section

namespace Erdos599.Blueprint.ColouredSafeHammock

open Set Cardinal Order DirectedPath
open ColouredSafeReverseReachability ColouredSafeAmbientOccurrence

universe u

variable {V : Type u} {Gamma : DWeb V} {Y : Set Gamma.DPath} {s t : V}

/-- Any genuinely large filtered subfamily can be cut to the exact cardinal
needed by `HasCard`, retaining the original hammock's interior disjointness. -/
theorem Hammock.hasCard_of_large_filtered_subset
    {e : Option V} {extra : Occurrence Y s → Prop}
    {H K : Set (Occurrence Y s)} (hH : Hammock Y s e extra H)
    (hKH : K ⊆ H) {P : Occurrence Y s → Prop}
    (hP : ∀ A ∈ K, P A) {rho : Cardinal.{u}} (hcard : rho ≤ #K) :
    HasCard Y s e (fun A ↦ extra A ∧ P A) rho := by
  obtain ⟨J, hJK, hJcard⟩ := Cardinal.le_mk_iff_exists_subset.mp hcard
  refine ⟨J, ⟨?_, hH.2.subset (hJK.trans hKH)⟩, hJcard⟩
  intro A hA
  obtain ⟨hvalid, hend, hs, ht, hextra⟩ := hH.1 (hKH (hJK hA))
  exact ⟨hvalid, hend, hs, ht, hextra, hP A (hJK hA)⟩

/-- A finite partition cannot split an infinite successor-sized hammock
into two families of size at most its predecessor. -/
theorem HasCard.filter_or_filter_not
    {e : Option V} {extra : Occurrence Y s → Prop} {rho : Cardinal.{u}}
    (h : HasCard Y s e extra (succ rho)) (hrho : aleph0 ≤ rho)
    (P : Occurrence Y s → Prop) :
    HasCard Y s e (fun A ↦ extra A ∧ P A) (succ rho) ∨
      HasCard Y s e (fun A ↦ extra A ∧ ¬P A) (succ rho) := by
  obtain ⟨H, hH, hHcard⟩ := h
  let yes : Set (Occurrence Y s) := {A ∈ H | P A}
  let no : Set (Occurrence Y s) := {A ∈ H | ¬P A}
  by_cases hy : succ rho ≤ #yes
  · exact Or.inl (hH.hasCard_of_large_filtered_subset
      (fun _ hA ↦ hA.1) (fun _ hA ↦ hA.2) hy)
  by_cases hn : succ rho ≤ #no
  · exact Or.inr (hH.hasCard_of_large_filtered_subset
      (fun _ hA ↦ hA.1) (fun _ hA ↦ hA.2) hn)
  have hySmall : #yes ≤ rho := le_of_lt_succ (lt_of_not_ge hy)
  have hnSmall : #no ≤ rho := le_of_lt_succ (lt_of_not_ge hn)
  have hcover : H ⊆ yes ∪ no := by
    intro A hA
    by_cases hp : P A
    · exact Or.inl ⟨hA, hp⟩
    · exact Or.inr ⟨hA, hp⟩
  have hsmall : #H ≤ rho :=
    (Cardinal.mk_le_mk_of_subset hcover).trans
      ((Cardinal.mk_union_le _ _).trans (Cardinal.add_le_of_le hrho hySmall hnSmall))
  exact False.elim ((not_le_of_gt (Order.lt_succ rho)) (hHcard ▸ hsmall))

/-- Weakness excludes a large nondegenerate half, not degeneracy of an
arbitrarily chosen witness. The degenerate half is itself genuinely large. -/
theorem HasCard.hasCard_degenerate_of_not_nondegenerate
    {extra : Occurrence Y s → Prop} {rho : Cardinal.{u}}
    (h : HasCard Y s (some t) extra (succ rho)) (hrho : aleph0 ≤ rho)
    (hnot : ¬HasCard Y s (some t)
      (fun A ↦ extra A ∧ ¬A.HasFiniteSwitchedPathTo t) (succ rho)) :
    HasCard Y s (some t)
      (fun A ↦ extra A ∧ A.HasFiniteSwitchedPathTo t) (succ rho) := by
  exact (h.filter_or_filter_not hrho (fun A ↦ A.HasFiniteSwitchedPathTo t)).resolve_right hnot

/-- A weak filtered imaginary edge can be realized by an actual finite
path avoiding an arbitrary small protected set away from its old endpoints. -/
theorem HasCard.exists_degenerate_path_avoiding
    {extra : Occurrence Y s → Prop} {rho : Cardinal.{u}}
    (h : HasCard Y s (some t) extra (succ rho))
    (hY : Gamma.IsWarp Y) (hrho : aleph0 ≤ rho)
    (hnot : ¬HasCard Y s (some t)
      (fun A ↦ extra A ∧ ¬A.HasFiniteSwitchedPathTo t) (succ rho))
    {X : Set V} (hX : #X ≤ rho) :
    ∃ (A : Occurrence Y s) (p : FinitePath Gamma.graph),
      A ∈ goodRoutes Y s (some t) extra ∧ p.start = s ∧ p.finish = t ∧
      p.edgeSet ⊆ A.switchedEdges ∧ p.support ∩ X ⊆ {s, t} := by
  have hdeg := h.hasCard_degenerate_of_not_nondegenerate hrho hnot
  obtain ⟨A, hA, havoid⟩ :=
    hdeg.exists_goodRoute_avoiding_referenceClosure hY hrho hX
  obtain ⟨p, hps, hpt, hpE⟩ := hA.2.2.2.2.2
  have hcarrier := A.finitePath_support_subset_referenceClosure hY p hps hpE
  refine ⟨A, p, ⟨hA.1, hA.2.1, hA.2.2.1, hA.2.2.2.1, hA.2.2.2.2.1⟩,
    hps, hpt, hpE, ?_⟩
  intro x hx
  simpa only [endpoints_some] using havoid ⟨hcarrier hx.1, hx.2⟩

#print axioms Hammock.hasCard_of_large_filtered_subset
#print axioms HasCard.hasCard_degenerate_of_not_nondegenerate
#print axioms HasCard.exists_degenerate_path_avoiding

end Erdos599.Blueprint.ColouredSafeHammock

namespace Erdos599.ColouredSafeReverseReachability.CurrentSafeOccurrence

open Set Cardinal Order DirectedPath Ladder

universe u

variable {V : Type u} {Gamma : DWeb V} {kappa : Cardinal.{u}}
variable {L : Gamma.KappaLadder kappa} {a : Stage kappa}
variable {W : Set Gamma.DPath} {s : V}

/-- Native roof-supported switched paths inherit roof containment from
their terminal. This is inverse reference transport, not a causal word claim. -/
theorem finitePath_support_subset_roof
    (hL : DWeb.KappaLadder.Deferred.HalfwayGeometry L)
    (A : CurrentSafeOccurrence W L.limitWarp s)
    (hRoof : A.vertexSet ⊆ Gamma.roof (L.frontier a))
    {p : FinitePath Gamma.graph} (hpEdges : p.edgeSet ⊆ A.switchedEdges)
    (hfinishRoof : p.finish ∈ Gamma.roof (L.frontier a)) :
    p.support ⊆ Gamma.roof (L.frontier a) := by
  have h := finitePath_support_subset_roof_of_retypeLimitReference hL
    (A.retypeStageReference hL hRoof) (by simpa using hRoof)
    (p := p) (by simpa only [retypeLimitReference_retypeStageReference] using hpEdges)
    hfinishRoof
  exact h

#print axioms finitePath_support_subset_roof

end Erdos599.ColouredSafeReverseReachability.CurrentSafeOccurrence

namespace Erdos599.Blueprint.LinkageBlueprint.ClubStageGeometry

open Set Cardinal Order DirectedPath Ladder
open ColouredSafeReverseReachability ColouredSafeAmbientOccurrence ColouredSafeHammock

universe u

variable {V : Type u} {Gamma : DWeb V} {Y : Set Gamma.DPath} {kappa : Cardinal.{u}}

/-- The weak branch supplies an endpoint-preserving protected path inside
the actual displayed stage roof. Unlike the strong branch, it does not need
to restrict the reference to a finite-character subwarp. -/
theorem native_global_weak_hasCard_exists_path_avoiding
    (C : ClubStageGeometry Gamma Y kappa (succ kappa))
    {a : Stage (succ kappa)} {s t : V}
    {extra : Occurrence C.ladder.limitWarp s → Prop}
    (h : HasCard C.ladder.limitWarp s (some t) extra (succ kappa))
    (hroof : ∀ A, extra A → A.vertexSet ⊆ Gamma.roof (C.ladder.frontier a))
    (hnot : ¬HasCard C.ladder.limitWarp s (some t)
      (fun A ↦ extra A ∧ ¬A.HasFiniteSwitchedPathTo t) (succ kappa))
    {X : Set V} (hX : #X ≤ kappa) :
    ∃ (A : Occurrence C.ladder.limitWarp s) (p : FinitePath Gamma.graph),
      A ∈ goodRoutes C.ladder.limitWarp s (some t) extra ∧
      p.start = s ∧ p.finish = t ∧ p.edgeSet ⊆ A.switchedEdges ∧
      p.support ∩ X ⊆ {s, t} ∧ p.support ⊆ Gamma.roof (C.ladder.frontier a) := by
  obtain ⟨A, p, hA, hps, hpt, hpE, hpX⟩ := h.exists_degenerate_path_avoiding
    (C.legal.warpStages (finalStage (succ kappa))) C.capacity_infinite hnot hX
  have hARoof := hroof A hA.2.2.2.2
  have htA : t ∈ A.vertexSet := A.terminal_mem_vertexSet hA.2.1
  exact ⟨A, p, hA, hps, hpt, hpE, hpX,
    A.finitePath_support_subset_roof C.legal hARoof hpE (hpt.symm ▸ hARoof htA)⟩

#print axioms native_global_weak_hasCard_exists_path_avoiding

end Erdos599.Blueprint.LinkageBlueprint.ClubStageGeometry
