/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.ColouredSafeEndpointHammockClosure
import ErdosProblems.Erdos599.ColouredSafeHammockSmallInsideClosure

/-!
# Small endpoint and whole-reference closure inside a closed carrier

Use actual contained successor-cap witnesses, thinning them at each endpoint
pair. An omega iteration adds these small carriers and whole reference owners
meeting the current set. Global eligible routes need not all lie in the carrier.
-/

noncomputable section

namespace Erdos599.Blueprint.ColouredSafeEndpointHammock

open Set Cardinal Order DirectedPath
open ColouredSafeHammock ColouredSafeEndpointReference

universe u

variable {V : Type u} {Gamma : DWeb V} {Y : Set Gamma.DPath}
variable {extra : ∀ s e, Route Y s e → Prop} {rho : Cardinal.{u}} {Z : Set V}

theorem Closed.exists_pairCarrier (hZ : Closed Y extra (succ rho) Z)
    (hrho : aleph0 ≤ rho) {s : V} {e : Option V} (hends : endpoints s e ⊆ Z) :
    Nonempty (PairCarrier Y extra Z rho s e) := by
  obtain ⟨O, hOcard, hOZ, hO⟩ := (hZ s e hends).1.exists_small_within hrho
  cases e with
  | none => exact ⟨⟨O, hOcard, hOZ, hO, by simp⟩⟩
  | some t =>
      obtain ⟨N, hNcard, hNZ, hN⟩ := ((hZ s (some t) hends).2 t rfl).exists_small_within hrho
      refine ⟨⟨O ∪ N, ?_, Set.union_subset hOZ hNZ, hO.mono Set.subset_union_left, ?_⟩⟩
      · exact (Cardinal.mk_union_le _ _).trans (Cardinal.add_le_of_le hrho hOcard hNcard)
      · intro v hv
        have htv : t = v := Option.some.inj hv
        subst v
        exact hN.mono Set.subset_union_right

/-- The same small output is endpoint-hammock closed, whole-reference closed,
and contained in the supplied successor-cap closed carrier. -/
theorem Closed.exists_small_jointClosed_within (hZ : Closed Y extra (succ rho) Z)
    (hrho : aleph0 ≤ rho) (hY : Gamma.IsWarp Y)
    (href : ClosedUnderPaths Gamma Y Z)
    {seed : Set V} (hseed : #seed ≤ rho) (hseedZ : seed ⊆ Z) :
    ∃ X : Set V, seed ⊆ X ∧ #X ≤ rho ∧ X ⊆ Z ∧
      Closed Y extra rho X ∧ ClosedUnderPaths Gamma Y X := by
  have hpair : ∀ s e, ∃ K : Set V, #K ≤ rho ∧ K ⊆ Z ∧
      (endpoints s e ⊆ Z →
        ClosedAt (reference Y s e) s e (extra s e) rho K ∧
          ∀ t, e = some t → ClosedAt (reference Y s e) s e
            (fun A ↦ extra s e A ∧ ¬A.HasFiniteSwitchedPathTo t) rho K) := by
    intro s e
    by_cases hends : endpoints s e ⊆ Z
    · obtain ⟨K⟩ := hZ.exists_pairCarrier hrho hends
      exact ⟨K.carrier, K.card_le, K.subset_roof, fun _ ↦ ⟨K.ordinary, K.nondegenerate⟩⟩
    · exact ⟨∅, by simp, Set.empty_subset _, fun h ↦ (hends h).elim⟩
  choose K hKcard hKZ hKclosed using hpair
  let step : Set V → Set V := fun X ↦
    ((X ∪ ⋃ s : X, K s.1 none) ∪ ⋃ s : X, ⋃ t : X, K s.1 (some t.1)) ∪
      meetingVertices Gamma Y X
  have hinflate : ∀ X, X ⊆ step X := fun _ _ hx ↦ Or.inl (Or.inl (Or.inl hx))
  have hstepCard : ∀ X : Set V, #X ≤ rho → #(step X) ≤ rho := by
    intro X hX
    apply (Cardinal.mk_union_le _ _).trans
    apply Cardinal.add_le_of_le hrho
    · apply (Cardinal.mk_union_le _ _).trans
      apply Cardinal.add_le_of_le hrho
      · apply (Cardinal.mk_union_le _ _).trans
        apply Cardinal.add_le_of_le hrho hX
        exact DWeb.mk_iUnion_le_of_le hrho hX (fun s ↦ hKcard s.1 none)
      · apply DWeb.mk_iUnion_le_of_le hrho hX
        intro s
        exact DWeb.mk_iUnion_le_of_le hrho hX (fun t ↦ hKcard s.1 (some t.1))
    · exact mk_meetingVertices_le Gamma Y X hY hrho hX
  have hstepZ : ∀ X, X ⊆ Z → step X ⊆ Z := by
    intro X hX x hx
    rcases hx with ((hx | hx) | hx) | hx
    · exact hX hx
    · obtain ⟨s, hs⟩ := Set.mem_iUnion.mp hx
      exact hKZ s.1 none hs
    · obtain ⟨s, hs⟩ := Set.mem_iUnion.mp hx
      obtain ⟨t, ht⟩ := Set.mem_iUnion.mp hs
      exact hKZ s.1 (some t.1) ht
    · obtain ⟨p, hxp⟩ := Set.mem_iUnion.mp hx
      obtain ⟨v, hvp, hvX⟩ := p.2.2
      exact href p.1 p.2.1 ⟨v, hvp, hX hvX⟩ hxp
  let X := omegaClosure step seed
  have hstageCard := mk_closureStage_le hseed hstepCard
  have hstageZ := closureStage_subset_roof hseedZ hstepZ
  have hmono : Monotone (closureStage step seed) :=
    monotone_nat_of_le_succ (fun _ ↦ hinflate _)
  have hXZ : X ⊆ Z := by
    intro x hx
    obtain ⟨n, hn⟩ := Set.mem_iUnion.mp hx
    exact hstageZ n hn
  have hKX : ∀ s e, endpoints s e ⊆ X → K s e ⊆ X := by
    intro s e hends
    obtain ⟨ns, hs⟩ := Set.mem_iUnion.mp (hends (Or.inl rfl))
    cases e with
    | none =>
        intro x hx
        apply closureStage_subset_omegaClosure step seed (ns + 1)
        exact Or.inl (Or.inl (Or.inr (Set.mem_iUnion.mpr ⟨⟨s, hs⟩, hx⟩)))
    | some t =>
        obtain ⟨nt, ht⟩ := Set.mem_iUnion.mp (hends (Or.inr rfl))
        have hs' := hmono (Nat.le_max_left ns nt) hs
        have ht' := hmono (Nat.le_max_right ns nt) ht
        intro x hx
        apply closureStage_subset_omegaClosure step seed (max ns nt + 1)
        exact Or.inl (Or.inr (Set.mem_iUnion.mpr ⟨⟨s, hs'⟩,
          Set.mem_iUnion.mpr ⟨⟨t, ht'⟩, hx⟩⟩))
  refine ⟨X, closureStage_subset_omegaClosure step seed 0,
    DWeb.mk_iUnion_nat_le hrho hstageCard, hXZ, ?_, ?_⟩
  · intro s e hends
    have hc := hKclosed s e (hends.trans hXZ)
    exact ⟨hc.1.mono (hKX s e hends), fun t ht ↦ (hc.2 t ht).mono (hKX s e hends)⟩
  · intro p hp hmeet
    obtain ⟨x, hxp, hxX⟩ := hmeet
    obtain ⟨n, hxn⟩ := Set.mem_iUnion.mp hxX
    intro y hyp
    apply closureStage_subset_omegaClosure step seed (n + 1)
    exact Or.inr (support_subset_meetingVertices Gamma Y (closureStage step seed n)
      hp ⟨x, hxp, hxn⟩ hyp)

#print axioms Closed.exists_pairCarrier
#print axioms Closed.exists_small_jointClosed_within

end Erdos599.Blueprint.ColouredSafeEndpointHammock
