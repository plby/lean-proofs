/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.ColouredSafeBalancedTerminalExtraction

/-!
# Removing a finite auxiliary-reference word without changing its terminal

The forward family is fixed. Auxiliary reference edges have designated
tails and avoid the original reference carrier. A finite safe word using
them yields an original safe word from some designated source to the same
terminal. Infinite auxiliary-reference words are a separate obligation.
-/

namespace Erdos599.Alternating.ColouredSafeFiniteAuxiliaryRemoval

open Set DirectedPath

universe u

variable {V : Type u} {Gamma : DWeb V} {W Y C : Set Gamma.DPath}

private theorem union_edges : familyEdges (Y ∪ C) = familyEdges Y ∪ familyEdges C :=
  RelationDecomposition.DWeb.familyEdges_union_local Gamma Y C

/-- A source-changing terminal factorization for actual finite safe words
over a disjoint auxiliary reference. All new forward edges were already
forward edges of the supplied word over the original fixed family. -/
theorem exists_originalSafeWord
    (hW : Gamma.IsWarp W) (hY : Gamma.IsWarp Y)
    (hWfin : Gamma.HasFiniteCharacter W) (hYfin : Gamma.HasFiniteCharacter Y)
    (hYC : Gamma.IsWarp (Y ∪ C))
    (hdisjoint : Disjoint (Gamma.vertexSet Y) (Gamma.vertexSet C))
    {J : Set V} (hCtails : ∀ {x y}, (x, y) ∈ familyEdges C → x ∈ J)
    (Q : FiniteColouredOccurrenceWord W (Y ∪ C)) (hQ : Q.IsIntervalSafe)
    (hstartJ : Q.vertex 0 ∈ J)
    (hstartOff : Q.vertex 0 ∉ Gamma.vertexSet (Y ∪ C))
    (hlastOff : Q.vertex (Fin.last Q.length) ∉ Gamma.vertexSet (Y ∪ C))
    (hne : Q.vertex 0 ≠ Q.vertex (Fin.last Q.length)) :
    ∃ s ∈ J, ∃ P : FiniteColouredOccurrenceWord W Y, P.IsIntervalSafe ∧
      P.vertex 0 = s ∧ P.vertex (Fin.last P.length) = Q.vertex (Fin.last Q.length) ∧
      P.forwardEdges ⊆ Q.forwardEdges := by
  let F := Q.forwardEdges
  let R := Q.backwardEdges ∩ familyEdges Y
  have hYV : Gamma.vertexSet Y ⊆ Gamma.vertexSet (Y ∪ C) := by
    rintro x ⟨p, hp, hx⟩
    exact ⟨p, Or.inl hp, hx⟩
  have hYedges : familyEdges Y ⊆ familyEdges (Y ∪ C) := by
    rw [union_edges]
    exact Set.subset_union_left
  have hbackOld : ∀ {a b : V}, (a, b) ∈ Q.backwardEdges →
      a ∈ Gamma.vertexSet Y ∨ b ∈ Gamma.vertexSet Y → (a, b) ∈ familyEdges Y := by
    intro a b he hcontact
    have heUnion := Q.backwardEdges_subset_familyEdges he
    rw [union_edges] at heUnion
    rcases heUnion with heY | heC
    · exact heY
    · have hends := familyEdges_subset_vertexSet_prod C heC
      rcases hcontact with ha | hb
      · exact False.elim (Set.disjoint_left.mp hdisjoint ha hends.1)
      · exact False.elim (Set.disjoint_left.mp hdisjoint hb hends.2)
  have hbalance : ∀ x ∈ Gamma.vertexSet Y, edgeBalance F x = edgeBalance R x := by
    intro x hx
    have hxFirst : x ≠ Q.vertex 0 := fun he ↦ hstartOff (he ▸ hYV hx)
    have hxLast : x ≠ Q.vertex (Fin.last Q.length) := fun he ↦ hlastOff (he ▸ hYV hx)
    have hword := Q.edgeBalance_forward_sub_backward hW hYC x
    simp only [propInt, if_neg hxFirst, if_neg hxLast] at hword
    have hOut : HasOutgoing Q.backwardEdges x ↔ HasOutgoing R x := by
      constructor
      · rintro ⟨y, he⟩
        exact ⟨y, he, hbackOld he (Or.inl hx)⟩
      · rintro ⟨y, he⟩
        exact ⟨y, he.1⟩
    have hIn : HasIncoming Q.backwardEdges x ↔ HasIncoming R x := by
      constructor
      · rintro ⟨y, he⟩
        exact ⟨y, he, hbackOld he (Or.inr hx)⟩
      · rintro ⟨y, he⟩
        exact ⟨y, he.1⟩
    have hsame : edgeBalance Q.backwardEdges x = edgeBalance R x := by
      simp only [edgeBalance, hOut, hIn]
    change edgeBalance Q.forwardEdges x = edgeBalance R x
    omega
  have hinterval : ∀ p ∈ Y, IsEdgeInterval (R ∩ p.edgeSet) p := by
    intro p hp
    have hpE : p.edgeSet ⊆ familyEdges Y := fun e he ↦
      Set.mem_iUnion.mpr ⟨p, Set.mem_iUnion.mpr ⟨hp, he⟩⟩
    change IsEdgeInterval ((Q.backwardEdges ∩ familyEdges Y) ∩ p.edgeSet) p
    rw [Set.inter_assoc, Set.inter_eq_right.mpr hpE]
    exact hQ.intervals p (Or.inl hp)
  have hin : ∀ {a b x : V}, (a, x) ∈ F → (b, x) ∈ familyEdges Y → (b, x) ∈ R :=
    fun he hf ↦ ⟨hQ.incoming_removed he (hYedges hf), hf⟩
  have hout : ∀ {x a b : V}, (x, a) ∈ F → (x, b) ∈ familyEdges Y → (x, b) ∈ R :=
    fun he hf ↦ ⟨hQ.outgoing_removed he (hYedges hf), hf⟩
  have hpure : ∀ {x y : V}, (x, y) ∈ F →
      y ∉ Gamma.initialSet Y ∧ x ∉ Gamma.terminalFrontier Y := by
    intro x y he
    have hp := hQ.endpoint_pure he
    constructor
    · rintro ⟨p, hpY, hpy⟩
      exact hp.1 ⟨p, Or.inl hpY, hpy⟩
    · rintro ⟨p, hpY, hpx⟩
      exact hp.2 ⟨p, Or.inl hpY, hpx⟩
  have hlastNoOut : ¬HasOutgoing Q.backwardEdges (Q.vertex (Fin.last Q.length)) := by
    rintro ⟨y, he⟩
    exact hlastOff (familyEdges_subset_vertexSet_prod (Y ∪ C)
      (Q.backwardEdges_subset_familyEdges he)).1
  have hlastNoIn : ¬HasIncoming Q.backwardEdges (Q.vertex (Fin.last Q.length)) := by
    rintro ⟨y, he⟩
    exact hlastOff (familyEdges_subset_vertexSet_prod (Y ∪ C)
      (Q.backwardEdges_subset_familyEdges he)).2
  have ht : edgeBalance F (Q.vertex (Fin.last Q.length)) = -1 := by
    have hword := Q.edgeBalance_forward_sub_backward hW hYC (Q.vertex (Fin.last Q.length))
    have hb : edgeBalance Q.backwardEdges (Q.vertex (Fin.last Q.length)) = 0 := by
      simp only [edgeBalance, hlastNoOut, hlastNoIn, propInt, if_false, sub_self]
    simp only [hb, propInt, if_neg hne.symm, sub_zero] at hword
    exact hword
  obtain ⟨s, hsOff, hsBalance, P, hP, hfirst, hlast, hPF⟩ :=
    ColouredSafeBalancedTerminalExtraction.exists_safeWord_to_negativeBoundary
      hW hY hWfin hYfin Q.forwardEdges_finite
      (Q.backwardEdges_finite.subset Set.inter_subset_left)
      Q.forwardEdges_subset_familyEdges Set.inter_subset_right hinterval hin hout hpure hbalance
      (fun htY ↦ hlastOff (hYV htY)) ht
  have hsJ : s ∈ J := by
    by_cases hsFirst : s = Q.vertex 0
    · exact hsFirst ▸ hstartJ
    have hsLast : s ≠ Q.vertex (Fin.last Q.length) := by
      intro he
      have hneg : edgeBalance F s = -1 := he.symm ▸ ht
      have hbad : (1 : ℤ) = -1 := hsBalance.symm.trans hneg
      omega
    have hword := Q.edgeBalance_forward_sub_backward hW hYC s
    have hsF : edgeBalance Q.forwardEdges s = 1 := hsBalance
    simp only [hsF, propInt, if_neg hsFirst, if_neg hsLast] at hword
    have hsBack : edgeBalance Q.backwardEdges s = 1 := by omega
    obtain ⟨⟨y, he⟩, _⟩ := edgeBalance_eq_one_iff.mp hsBack
    have heUnion := Q.backwardEdges_subset_familyEdges he
    rw [union_edges] at heUnion
    rcases heUnion with heY | heC
    · exact False.elim (hsOff (familyEdges_subset_vertexSet_prod Y heY).1)
    · exact hCtails heC
  exact ⟨s, hsJ, P, hP, hfirst, hlast, hPF⟩

/-- An uncovered nonterminal source has no augmented reverse-reachability
witness when the auxiliary reference covers all original safe terminal rows.
This conclusion concerns finite witnesses and needs no finite-carrier premise. -/
theorem not_reverseReachable_of_auxiliary_cover
    (hW : Gamma.IsWarp W) (hY : Gamma.IsWarp Y)
    (hWfin : Gamma.HasFiniteCharacter W) (hYfin : Gamma.HasFiniteCharacter Y)
    (hYC : Gamma.IsWarp (Y ∪ C))
    (hdisjoint : Disjoint (Gamma.vertexSet Y) (Gamma.vertexSet C))
    {J : Set (FiniteColouredOccurrenceWord.ExposedInitial W Y)}
    (hnonterminal : ∀ s ∈ J, s.1 ∉ Gamma.terminalFrontier W)
    (hCtails : ∀ {x y}, (x, y) ∈ familyEdges C → x ∈ Subtype.val '' J)
    (hcover : ColouredSafeReverseReachability.safeTerminalUnion J ⊆ Gamma.vertexSet C)
    {s : FiniteColouredOccurrenceWord.ExposedInitial W Y} (hsJ : s ∈ J)
    (hsOff : s.1 ∉ Gamma.vertexSet (Y ∪ C)) :
    s.1 ∉ ColouredSafeReverseReachability.reverseReachable W (Y ∪ C) s.1 := by
  rintro ⟨t, ht, _hroute⟩
  obtain ⟨htBoundary, Q, hQ, hfirst, hlast⟩ := ht
  have hne : Q.vertex 0 ≠ Q.vertex (Fin.last Q.length) := by
    intro heq
    have hst : s.1 = t := hfirst.symm.trans (heq.trans hlast)
    exact hnonterminal s hsJ (hst ▸ htBoundary.1)
  obtain ⟨u, huJ, P, hP, hPfirst, hPlast, _hPF⟩ :=
    exists_originalSafeWord hW hY hWfin hYfin hYC hdisjoint hCtails Q hQ
      (hfirst ▸ ⟨s, hsJ, rfl⟩) (hfirst ▸ hsOff) (hlast ▸ htBoundary.2) hne
  obtain ⟨r, hrJ, hru⟩ := huJ
  have htOld : t ∈ Gamma.terminalFrontier W \ Gamma.vertexSet Y := by
    refine ⟨htBoundary.1, ?_⟩
    rintro ⟨p, hp, htp⟩
    exact htBoundary.2 ⟨p, Or.inl hp, htp⟩
  have htSafe : t ∈ ColouredSafeReverseReachability.safelyReachable W Y r.1 :=
    ⟨htOld, P, hP, hPfirst.trans hru.symm, hPlast.trans hlast⟩
  have htC := hcover
    (ColouredSafeReverseReachability.mem_safeTerminalUnion_of_mem_safelyReachable hrJ htSafe)
  obtain ⟨p, hp, htp⟩ := htC
  exact htBoundary.2 ⟨p, Or.inr hp, htp⟩

/-- In a finite region, auxiliary reference paths covering all the old safe
terminal rows cannot leave a designated nonterminal source uncovered. This
uses the actual finite-word removal theorem, not an assumed Hall inequality. -/
theorem no_uncoveredSource_of_finite_auxiliary_cover
    (hW : Gamma.IsWarp W) (hY : Gamma.IsWarp Y)
    (hWfin : Gamma.HasFiniteCharacter W) (hYfin : Gamma.HasFiniteCharacter Y)
    (hYC : Gamma.IsWarp (Y ∪ C)) (hYCfin : Gamma.HasFiniteCharacter (Y ∪ C))
    (hWV : (Gamma.vertexSet W).Finite) (hYCV : (Gamma.vertexSet (Y ∪ C)).Finite)
    (hdisjoint : Disjoint (Gamma.vertexSet Y) (Gamma.vertexSet C))
    (hsource : Gamma.initialSet (Y ∪ C) ⊆ Gamma.initialSet W)
    (hterminal : Gamma.terminalFrontier W ∩ Gamma.vertexSet (Y ∪ C) ⊆
      Gamma.terminalFrontier (Y ∪ C))
    {J : Set (FiniteColouredOccurrenceWord.ExposedInitial W Y)}
    (hnonterminal : ∀ s ∈ J, s.1 ∉ Gamma.terminalFrontier W)
    (hCtails : ∀ {x y}, (x, y) ∈ familyEdges C → x ∈ Subtype.val '' J)
    (hcover : ColouredSafeReverseReachability.safeTerminalUnion J ⊆ Gamma.vertexSet C) :
    Subtype.val '' J ⊆ Gamma.vertexSet (Y ∪ C) := by
  rintro _ ⟨s, hsJ, rfl⟩
  by_contra hsOff
  have hno := ColouredSafeFiniteDuality.not_infiniteWord_of_finite_carriers hWV hYCV
  have hreach := ColouredSafeReverseReachability.mem_reverseReachable_of_no_safeInfinite
    hW hYC hWfin hYCfin hsource hterminal s.2.1 hsOff
      (fun ⟨Q, _, _⟩ ↦ hno ⟨Q⟩)
  exact not_reverseReachable_of_auxiliary_cover hW hY hWfin hYfin hYC hdisjoint
    hnonterminal hCtails hcover hsJ hsOff hreach

#print axioms exists_originalSafeWord
#print axioms not_reverseReachable_of_auxiliary_cover
#print axioms no_uncoveredSource_of_finite_auxiliary_cover

end Erdos599.Alternating.ColouredSafeFiniteAuxiliaryRemoval
