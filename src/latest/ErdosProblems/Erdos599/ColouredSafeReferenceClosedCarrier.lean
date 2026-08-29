/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.ColouredSafeCapturedClosure
import ErdosProblems.Erdos599.HalfwayMovingGlobalReferenceRoof

/-!
# Simultaneous native hammock and whole-reference closure

One omega construction inserts the selected native hammock carriers and all
reference owners meeting the current set. Both operations preserve the small
cardinal bound. A genuine route filter and reference-support containment keep
the construction inside the prescribed roof. Reference owners may be rays.
-/

noncomputable section

namespace Erdos599.Blueprint.ColouredSafeReferenceClosedCarrier

open Set Cardinal Order DirectedPath ColouredSafeAmbientOccurrence
open ColouredSafeHammockOmegaClosure
  (FilteredOmegaClosed familyVertices chosenOrdinaryFamily chosenOrdinaryFamily_spec
    chosenNondegenerateFamily chosenNondegenerateFamily_spec)

universe u

variable {V : Type u} {Gamma : DWeb V} {Y : Set Gamma.DPath}

private theorem familyVertices_subset_of_extra
    {s : V} {e : Option V} {extra : Occurrence Y s → Prop}
    {H : Set (Occurrence Y s)} {R : Set V}
    (hH : ColouredSafeHammock.Hammock Y s e extra H)
    (hR : ∀ A, extra A → A.vertexSet ⊆ R) : familyVertices H ⊆ R := by
  intro x hx
  obtain ⟨A, hxA⟩ := Set.mem_iUnion.mp hx
  exact hR A.1 (hH.1 A.2).2.2.2.2 hxA

private theorem nativeClosingStep_subset
    (Y : Set Gamma.DPath) (extra : ∀ s, Occurrence Y s → Prop)
    (rho : Cardinal.{u}) {X R : Set V} (hX : X ⊆ R)
    (hR : ∀ s A, extra s A → A.vertexSet ⊆ R) :
    ColouredSafeHammockOmegaClosure.closingStep Y extra rho X ⊆ R := by
  intro x hx
  rcases hx with ((hx | hx) | hx) | hx
  · exact hX hx
  · obtain ⟨s, hxs⟩ := Set.mem_iUnion.mp hx
    exact familyVertices_subset_of_extra
      (MaximalUpTo.mem (chosenOrdinaryFamily_spec Y extra rho s.1 none)) (hR s.1) hxs
  · obtain ⟨s, hxs⟩ := Set.mem_iUnion.mp hx
    obtain ⟨t, hxt⟩ := Set.mem_iUnion.mp hxs
    exact familyVertices_subset_of_extra
      (MaximalUpTo.mem (chosenOrdinaryFamily_spec Y extra rho s.1 (some t.1)))
      (hR s.1) hxt
  · obtain ⟨s, hxs⟩ := Set.mem_iUnion.mp hx
    obtain ⟨t, hxt⟩ := Set.mem_iUnion.mp hxs
    exact familyVertices_subset_of_extra
      (MaximalUpTo.mem (chosenNondegenerateFamily_spec Y extra rho s.1 t.1))
      (fun A hA ↦ hR s.1 A hA.1) hxt

/-- Actual simultaneous closure. The hypothesis on the filter is literal
carrier containment, not a presumed closed family or a future ladder row. -/
theorem exists_closed_superset
    (Y : Set Gamma.DPath) (extra : ∀ s, Occurrence Y s → Prop)
    {rho : Cardinal.{u}} (hrho : aleph0 ≤ rho)
    {X0 R : Set V} (hX0 : #X0 ≤ rho) (hX0R : X0 ⊆ R)
    (hY : Gamma.IsWarp Y) (hYroof : ∀ p ∈ Y, p.support ⊆ R)
    (hR : ∀ s A, extra s A → A.vertexSet ⊆ R) :
    ∃ Z : Set V, X0 ⊆ Z ∧ #Z ≤ rho ∧ Z ⊆ R ∧
      FilteredOmegaClosed Y extra rho Z ∧ ClosedUnderPaths Gamma Y Z := by
  let step : Set V → Set V := fun X ↦
    ColouredSafeHammockOmegaClosure.closingStep Y extra rho X ∪
      meetingVertices Gamma Y X
  let Z : Set V := omegaClosure step X0
  have hstepCard : ∀ X : Set V, #X ≤ rho → #(step X) ≤ rho := by
    intro X hX
    exact (Cardinal.mk_union_le _ _).trans (Cardinal.add_le_of_le hrho
      (ColouredSafeHammockOmegaClosure.mk_closingStep_le Y extra hrho hX)
      (mk_meetingVertices_le Gamma Y X hY hrho hX))
  have hstepRoof : ∀ X : Set V, X ⊆ R → step X ⊆ R := by
    intro X hX
    exact Set.union_subset (nativeClosingStep_subset Y extra rho hX hR)
      (meetingVertices_subset_roof Gamma Y X R hYroof)
  have hinflate : ∀ X : Set V, X ⊆ step X := by
    intro X x hx
    exact Or.inl (ColouredSafeHammockOmegaClosure.subset_closingStep Y extra rho X hx)
  have hmono : Monotone (closureStage step X0) := by
    apply monotone_nat_of_le_succ
    intro n
    exact hinflate (closureStage step X0 n)
  have hstageCard := mk_closureStage_le hX0 hstepCard
  have hstageRoof := closureStage_subset_roof hX0R hstepRoof
  have hZCard : #Z ≤ rho := by
    change #(⋃ n, closureStage step X0 n) ≤ rho
    let stages : ULift.{u} Nat → Set V := fun n ↦ closureStage step X0 n.down
    have heq : (⋃ n, closureStage step X0 n) = ⋃ n, stages n := by
      ext x
      simp [stages]
    rw [heq]
    apply (Cardinal.mk_iUnion_le _).trans
    apply Cardinal.mul_le_of_le hrho
    · simpa [Cardinal.mk_nat] using hrho
    · exact ciSup_le' (fun n ↦ hstageCard n.down)
  have hZRoof : Z ⊆ R := by
    intro x hx
    obtain ⟨n, hxn⟩ := Set.mem_iUnion.mp hx
    exact hstageRoof n hxn
  refine ⟨Z, closureStage_subset_omegaClosure step X0 0, hZCard, hZRoof, ?_, ?_⟩
  · constructor
    · intro s hs
      obtain ⟨n, hsn⟩ := Set.mem_iUnion.mp hs
      refine ⟨chosenOrdinaryFamily Y extra rho s none,
        chosenOrdinaryFamily_spec Y extra rho s none, ?_⟩
      intro A hA x hx
      apply closureStage_subset_omegaClosure step X0 (n + 1)
      exact Or.inl (Or.inl (Or.inl (Or.inr
        (Set.mem_iUnion.mpr ⟨⟨s, hsn⟩, Set.mem_iUnion.mpr ⟨⟨A, hA⟩, hx⟩⟩))))
    · intro s hs t ht
      obtain ⟨ns, hsn⟩ := Set.mem_iUnion.mp hs
      obtain ⟨nt, htn⟩ := Set.mem_iUnion.mp ht
      let n := max ns nt
      have hsN := hmono (Nat.le_max_left ns nt) hsn
      have htN := hmono (Nat.le_max_right ns nt) htn
      constructor
      · refine ⟨chosenOrdinaryFamily Y extra rho s (some t),
          chosenOrdinaryFamily_spec Y extra rho s (some t), ?_⟩
        intro A hA x hx
        apply closureStage_subset_omegaClosure step X0 (n + 1)
        exact Or.inl (Or.inl (Or.inr
          (Set.mem_iUnion.mpr ⟨⟨s, hsN⟩, Set.mem_iUnion.mpr ⟨⟨t, htN⟩,
            Set.mem_iUnion.mpr ⟨⟨A, hA⟩, hx⟩⟩⟩)))
      · refine ⟨chosenNondegenerateFamily Y extra rho s t,
          chosenNondegenerateFamily_spec Y extra rho s t, ?_⟩
        intro A hA x hx
        apply closureStage_subset_omegaClosure step X0 (n + 1)
        exact Or.inl (Or.inr
          (Set.mem_iUnion.mpr ⟨⟨s, hsN⟩, Set.mem_iUnion.mpr ⟨⟨t, htN⟩,
            Set.mem_iUnion.mpr ⟨⟨A, hA⟩, hx⟩⟩⟩))
  · intro p hpY hpMeet
    obtain ⟨x, hxp, hxZ⟩ := hpMeet
    obtain ⟨n, hxn⟩ := Set.mem_iUnion.mp hxZ
    intro y hyp
    apply closureStage_subset_omegaClosure step X0 (n + 1)
    exact Or.inr (support_subset_meetingVertices Gamma Y
      (closureStage step X0 n) hpY ⟨x, hxp, hxn⟩ hyp)

/-- For the actual deferred club geometry, the global reference lies in
the limiting roof. Choose the later club stage only after closure is built. -/
theorem exists_captured_referenceClosed_later
    {Y0 : Set Gamma.DPath} {kappa : Cardinal.{u}}
    (C : LinkageBlueprint.ClubStageGeometry Gamma Y0 kappa (succ kappa))
    {X0 : Set V} (hX0 : #X0 ≤ kappa) (hX0Roof : X0 ⊆ C.ladder.limitRoof) :
    ∃ Z : Set V, X0 ⊆ Z ∧ #Z ≤ kappa ∧ Z ⊆ C.ladder.limitRoof ∧
      FilteredOmegaClosed C.ladder.limitWarp
        (ColouredSafeHammock.CapturedByStageRoof C.ladder) kappa Z ∧
      ClosedUnderPaths Gamma C.ladder.limitWarp Z ∧
      Nonempty (LinkageBlueprint.LaterClubRoofCapture C Z) := by
  obtain ⟨Z, hsub, hcard, hroof, hclosed, href⟩ := exists_closed_superset
    C.ladder.limitWarp (ColouredSafeHammock.CapturedByStageRoof C.ladder)
    C.capacity_infinite hX0 hX0Roof
    (C.legal.warpStages (Ladder.finalStage (succ kappa)))
    C.limitWarp_support_subset_limitRoof
    (fun _ _ hA ↦ hA.vertexSet_subset_limitRoof)
  exact ⟨Z, hsub, hcard, hroof, hclosed, href,
    LinkageBlueprint.LaterClubRoofCapture.exists_of_subset_limitRoof C Z hcard hroof⟩

#print axioms exists_closed_superset
#print axioms exists_captured_referenceClosed_later

end Erdos599.Blueprint.ColouredSafeReferenceClosedCarrier
