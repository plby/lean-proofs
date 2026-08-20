import ErdosProblems.Erdos957.WeightedRoleCollisions
import ErdosProblems.Erdos957.Case4KernelAggregation
import ErdosProblems.Erdos957.Case2Case4SameSide

/-!
# Produced weight-aware Case-2 aggregation

This module deliberately does not assert the false pairwise uniqueness of a
Case-2 secondary against a Case-4 split recipient.  It proves the two
pairwise statements that are valid (Case-2/direct and non-Case-2/non-Case-2)
and uses them only inside a three-source same-association argument.
-/

noncomputable section

namespace Erdos957Case2WeightedAssembly

open Erdos957GeometryCore
open Erdos957GeometryLocalRows
open Erdos957CaseClassification
open Erdos957CollisionInstantiation
open Erdos957CoherentRealizedRows
open Erdos957RoleCollisions
open Erdos957DirectSameSide
open Erdos957Case2RoleUniqueness
open Erdos957Case2SecondaryNoThree
open Erdos957Case4KernelAggregation
open Erdos957WeightedRoleCollisions
open Erdos957Overcharge

abbrev Point := Erdos957GeometryCore.Point

variable {A : Finset Point} {P : CyclicHullData A}
variable {W : DiameterWitnessData P} {F : P.FlatAlignedFrameData}

private lemma direct_ne_case2Secondary
    {role : PairCases.TargetRoleName} (h : IsDirectTargetRole role) :
    role ≠ .case2Secondary := by
  intro hr
  subst role
  simpa [IsDirectTargetRole] using h

private lemma direct_ne_case4SplitRight
    {role : PairCases.TargetRoleName} (h : IsDirectTargetRole role) :
    role ≠ .case4SplitRight := by
  intro hr
  subst role
  simpa [IsDirectTargetRole] using h

private lemma direct_of_not_exceptional
    {role : PairCases.TargetRoleName}
    (h2 : role ≠ .case2Secondary) (h4 : role ≠ .case4SplitRight) :
    IsDirectTargetRole role := by
  cases role <;> simp_all [IsDirectTargetRole]

/-- A same-associated direct arrival cannot be distinct from a Case-2
secondary.  This is the direct half of the older pairwise dispatcher and
does not use (or imply) Case-2/Case-4-split uniqueness. -/
theorem case2Secondary_direct_same_association_source_eq
    (hA : IsOneSeparated A)
    (Q : CommonCoherentRealizedSourceRows P W F.chart)
    {s t : Source P W} {v : Vertex A}
    (S : RealizedArrivalAt (F := F) Q.rows s v)
    (T : RealizedArrivalAt (F := F) Q.rows t v)
    (hsRole : S.target.role = .case2Secondary)
    (htDirect : IsDirectTargetRole T.target.role)
    (htWindow : t.1 ∈ Finset.univ.image (fun j : Fin 7 ↦
      (sevenShift P.next j (sourceIndex P W s.1 s.property)).1))
    (hassoc : S.descriptor.association = T.descriptor.association) :
    s = t := by
  by_contra hst
  have ht2 := direct_ne_case2Secondary htDirect
  have ht4 := direct_ne_case4SplitRight htDirect
  by_cases htPrimary : T.target.role = .case4Primary
  · exact Erdos957Case2SecondaryNoThree.no_case2Secondary_case4Primary_same_association_in_window
      S.target T.target S.descriptor T.descriptor hsRole htPrimary
        htWindow hassoc hst
  obtain ⟨B⟩ := nonempty_case2SecondaryArrivalFormula
    S.target S.descriptor hsRole
  have hadj := T.target.adj_source_of_directRole htDirect
  have horbit :=
    Case2SecondaryFormula.direct_competitor_eq_away_first_or_second
      B.formula F hadj htWindow hst
  have hflat := Erdos957GeometryLocalityBridge.sourceIndex_isFlat W s
  have hcone :
      -(B.formula.edgeFrame.toCanonical
          (sourceIndex P W t.1 t.property).1) 1 ≤
        (B.formula.edgeFrame.toCanonical
          (sourceIndex P W t.1 t.property).1) 0 / 5 := by
    rcases horbit with h | h
    · rw [h]
      exact Case2SecondaryFormula.away_cone_div_five B.formula F hflat 0
    · rw [h]
      exact Case2SecondaryFormula.away_cone_div_five B.formula F hflat 1
  have hy :
      (B.formula.edgeFrame.toCanonical
          (sourceIndex P W t.1 t.property).1) 1 < 0 := by
    rcases horbit with h | h
    · rw [h]
      exact (Case2SecondaryFormula.away_prefix_bounds
        B.formula F hflat 0).1
    · rw [h]
      exact (Case2SecondaryFormula.away_prefix_bounds
        B.formula F hflat 1).1
  exact Case2SecondaryFormula.no_direct_competitor_of_shallow_cone_of_fst_le
    hA B.formula (sourceIndex P W t.1 t.property).property hcone
      (coherent_case2Secondary_direct_fst_le hA Q S T B ht2 ht4
        htPrimary htWindow hassoc) hy hadj

/-- On the complement of Case-2 secondary, the checked direct/direct and
Case-4 residual kernels give pairwise same-association source uniqueness. -/
theorem nonCase2_same_association_source_eq
    (Q : CommonCoherentRealizedSourceRows P W F.chart)
    (locality : SourceLocalityCertificates P W F)
    (direct_direct : ∀ {s t : Source P W} {v : Vertex A}
      (S : RealizedArrivalAt (F := F) Q.rows s v)
      (T : RealizedArrivalAt (F := F) Q.rows t v),
      IsDirectTargetRole S.target.role →
      IsDirectTargetRole T.target.role →
      t.1 ∈ Finset.univ.image (fun j : Fin 7 ↦
        (sevenShift P.next j (sourceIndex P W s.1 s.property)).1) →
      S.descriptor.association = T.descriptor.association → s = t)
    (K4 : Case4SplitRightResidualKernels Q)
    {s t : Source P W} {v : Vertex A}
    (S : RealizedArrivalAt (F := F) Q.rows s v)
    (T : RealizedArrivalAt (F := F) Q.rows t v)
    (hs2 : S.target.role ≠ .case2Secondary)
    (ht2 : T.target.role ≠ .case2Secondary)
    (htWindow : t.1 ∈ Finset.univ.image (fun j : Fin 7 ↦
      (sevenShift P.next j (sourceIndex P W s.1 s.property)).1))
    (hassoc : S.descriptor.association = T.descriptor.association) :
    s = t := by
  by_cases hs4 : S.target.role = .case4SplitRight
  · by_cases ht4 : T.target.role = .case4SplitRight
    · exact K4.split_right_competitor S T hs4 ht4 htWindow hassoc
    · by_cases hst : s = t
      · exact hst
      · have htDirect : IsDirectTargetRole T.target.role :=
          direct_of_not_exceptional ht2 ht4
        have hnear :=
          Erdos957Case4CollisionLeaves.direct_competitor_reduces_to_near_two
            Q S.target T.target hs4 ht2 ht4 htWindow hst
        exact K4.direct_near_two S T hs4 htDirect hnear hassoc
  · have hsDirect : IsDirectTargetRole S.target.role :=
      direct_of_not_exceptional hs2 hs4
    by_cases ht4 : T.target.role = .case4SplitRight
    · by_cases hst : s = t
      · exact hst
      · have hsPos : 0 < sourceTokens P W F.chart
            (localCasesOfRealizedRows (F := F) Q.rows) s v := by
          simpa [sourceTokens, selectedCase, localCasesOfRealizedRows] using
            S.positive
        have htPos : 0 < sourceTokens P W F.chart
            (localCasesOfRealizedRows (F := F) Q.rows) t v := by
          simpa [sourceTokens, selectedCase, localCasesOfRealizedRows] using
            T.positive
        have hsWindow := locality.competing_source_in_window htPos hsPos
        have hnear :=
          Erdos957Case4CollisionLeaves.direct_competitor_reduces_to_near_two
            Q T.target S.target ht4 hs2 hs4 hsWindow (fun h ↦ hst h.symm)
        exact (K4.direct_near_two T S ht4 hsDirect hnear hassoc.symm).symm
    · have htDirect : IsDirectTargetRole T.target.role :=
        direct_of_not_exceptional ht2 ht4
      exact direct_direct S T hsDirect htDirect htWindow hassoc

/-- The Case-2 component of the no-five argument follows without the false
mixed pairwise statement: once neither competitor is Case 2, they collide
with each other under one of the checked non-Case-2 pairwise kernels. -/
theorem case2AnchoredSameAssociationTriple_of_pairwise
    (Q : CommonCoherentRealizedSourceRows P W F.chart)
    (locality : SourceLocalityCertificates P W F)
    (direct_direct : ∀ {s t : Source P W} {v : Vertex A}
      (S : RealizedArrivalAt (F := F) Q.rows s v)
      (T : RealizedArrivalAt (F := F) Q.rows t v),
      IsDirectTargetRole S.target.role →
      IsDirectTargetRole T.target.role →
      t.1 ∈ Finset.univ.image (fun j : Fin 7 ↦
        (sevenShift P.next j (sourceIndex P W s.1 s.property)).1) →
      S.descriptor.association = T.descriptor.association → s = t)
    (K4 : Case4SplitRightResidualKernels Q) :
    Case2AnchoredSameAssociationTriple (F := F) Q.rows := by
  intro s t u v S T U hsRole htAssoc huAssoc htWindow huWindow hst hsu htu
  by_cases ht2 : T.target.role = .case2Secondary
  · exact hst (case2Secondary_same_association_source_eq
      S T hsRole ht2 htWindow htAssoc.symm)
  by_cases hu2 : U.target.role = .case2Secondary
  · exact hsu (case2Secondary_same_association_source_eq
      S U hsRole hu2 huWindow huAssoc.symm)
  have htPos : 0 < sourceTokens P W F.chart
      (localCasesOfRealizedRows (F := F) Q.rows) t v := by
    simpa [sourceTokens, selectedCase, localCasesOfRealizedRows] using T.positive
  have huPos : 0 < sourceTokens P W F.chart
      (localCasesOfRealizedRows (F := F) Q.rows) u v := by
    simpa [sourceTokens, selectedCase, localCasesOfRealizedRows] using U.positive
  have huWindowFromT := locality.competing_source_in_window htPos huPos
  exact htu (nonCase2_same_association_source_eq Q locality direct_direct K4
    T U ht2 hu2 huWindowFromT (htAssoc.trans huAssoc.symm))

/-- In a distinct same-associated pair anchored at a Case-2 secondary, the
other row must be Case-4 split-right.  Case-2/Case-2, Case-2/direct, and the
whole Case-4 primary branch have already been eliminated independently. -/
theorem role_eq_case4SplitRight_of_case2_same_association
    (hA : IsOneSeparated A)
    (Q : CommonCoherentRealizedSourceRows P W F.chart)
    {s t : Source P W} {v : Vertex A}
    (S : RealizedArrivalAt (F := F) Q.rows s v)
    (T : RealizedArrivalAt (F := F) Q.rows t v)
    (hsRole : S.target.role = .case2Secondary)
    (htWindow : t.1 ∈ Finset.univ.image (fun j : Fin 7 ↦
      (sevenShift P.next j (sourceIndex P W s.1 s.property)).1))
    (hassoc : S.descriptor.association = T.descriptor.association)
    (hst : s ≠ t) :
    T.target.role = .case4SplitRight := by
  by_cases ht2 : T.target.role = .case2Secondary
  · exact (hst (case2Secondary_same_association_source_eq
      S T hsRole ht2 htWindow hassoc)).elim
  by_cases ht4 : T.target.role = .case4SplitRight
  · exact ht4
  have htDirect : IsDirectTargetRole T.target.role :=
    direct_of_not_exceptional ht2 ht4
  exact (hst (case2Secondary_direct_same_association_source_eq
    hA Q S T hsRole htDirect htWindow hassoc)).elim

private lemma four_association_cases
    (a b c d : ArrivalAssociation) :
    (b = a ∧ c = a) ∨ (b = a ∧ d = a) ∨
      (c = a ∧ d = a) ∨ (b = c ∧ d = b) ∨
      (b = a ∧ c = d) ∨ (c = a ∧ b = d) ∨
      (d = a ∧ b = c) := by
  cases a <;> cases b <;> cases c <;> cases d <;> simp

/-- The Case-2 anchored theorem plus non-Case-2 pairwise uniqueness excludes
three distinct arrivals carrying one common association. -/
private theorem same_association_triple_no_three
    (Q : CommonCoherentRealizedSourceRows P W F.chart)
    (locality : SourceLocalityCertificates P W F)
    (direct_direct : ∀ {s t : Source P W} {v : Vertex A}
      (S : RealizedArrivalAt (F := F) Q.rows s v)
      (T : RealizedArrivalAt (F := F) Q.rows t v),
      IsDirectTargetRole S.target.role →
      IsDirectTargetRole T.target.role →
      t.1 ∈ Finset.univ.image (fun j : Fin 7 ↦
        (sevenShift P.next j (sourceIndex P W s.1 s.property)).1) →
      S.descriptor.association = T.descriptor.association → s = t)
    (K4 : Case4SplitRightResidualKernels Q)
    {s t u : Source P W} {v : Vertex A}
    (S : RealizedArrivalAt (F := F) Q.rows s v)
    (T : RealizedArrivalAt (F := F) Q.rows t v)
    (U : RealizedArrivalAt (F := F) Q.rows u v)
    (htAssoc : T.descriptor.association = S.descriptor.association)
    (huAssoc : U.descriptor.association = S.descriptor.association)
    (htWindow : t.1 ∈ Finset.univ.image (fun j : Fin 7 ↦
      (sevenShift P.next j (sourceIndex P W s.1 s.property)).1))
    (huWindow : u.1 ∈ Finset.univ.image (fun j : Fin 7 ↦
      (sevenShift P.next j (sourceIndex P W s.1 s.property)).1))
    (hst : s ≠ t) (hsu : s ≠ u) (htu : t ≠ u) : False := by
  have hsPos : 0 < sourceTokens P W F.chart
      (localCasesOfRealizedRows (F := F) Q.rows) s v := by
    simpa [sourceTokens, selectedCase, localCasesOfRealizedRows] using S.positive
  have htPos : 0 < sourceTokens P W F.chart
      (localCasesOfRealizedRows (F := F) Q.rows) t v := by
    simpa [sourceTokens, selectedCase, localCasesOfRealizedRows] using T.positive
  have huPos : 0 < sourceTokens P W F.chart
      (localCasesOfRealizedRows (F := F) Q.rows) u v := by
    simpa [sourceTokens, selectedCase, localCasesOfRealizedRows] using U.positive
  have K2 : Case2AnchoredSameAssociationTriple (F := F) Q.rows :=
    case2AnchoredSameAssociationTriple_of_pairwise
      Q locality direct_direct K4
  by_cases hs2 : S.target.role = .case2Secondary
  · exact K2 S T U hs2 htAssoc huAssoc htWindow huWindow hst hsu htu
  by_cases ht2 : T.target.role = .case2Secondary
  · exact K2 T S U ht2 htAssoc.symm (huAssoc.trans htAssoc.symm)
      (locality.competing_source_in_window htPos hsPos)
      (locality.competing_source_in_window htPos huPos)
      hst.symm htu hsu
  by_cases hu2 : U.target.role = .case2Secondary
  · exact K2 U S T hu2 huAssoc.symm (htAssoc.trans huAssoc.symm)
      (locality.competing_source_in_window huPos hsPos)
      (locality.competing_source_in_window huPos htPos)
      hsu.symm htu.symm hst
  exact hst (nonCase2_same_association_source_eq Q locality direct_direct K4
    S T hs2 ht2 htWindow htAssoc.symm)

/-- Arithmetic/geometric core for one of the three possible `2+2`
association pairings.  Each pair contains exactly one Case-2 secondary and
one Case-4 split recipient, hence all four arrivals are half-weight.  The
only unsafe arithmetic column is degree five, discharged by the retained
Case-2/Case-2/split residual. -/
private theorem case2_quadruple_fits_of_association_pairing
    (hA : IsOneSeparated A)
    (Q : CommonCoherentRealizedSourceRows P W F.chart)
    (locality : SourceLocalityCertificates P W F)
    (direct_direct : ∀ {s t : Source P W} {v : Vertex A}
      (S : RealizedArrivalAt (F := F) Q.rows s v)
      (T : RealizedArrivalAt (F := F) Q.rows t v),
      IsDirectTargetRole S.target.role →
      IsDirectTargetRole T.target.role →
      t.1 ∈ Finset.univ.image (fun j : Fin 7 ↦
        (sevenShift P.next j (sourceIndex P W s.1 s.property)).1) →
      S.descriptor.association = T.descriptor.association → s = t)
    (K4 : Case4SplitRightResidualKernels Q)
    (K2 : Case2SecondarySplitDegreeFiveResiduals (F := F) Q.rows)
    {s t u d : Source P W} {v : Vertex A}
    (S : RealizedArrivalAt (F := F) Q.rows s v)
    (T : RealizedArrivalAt (F := F) Q.rows t v)
    (U : RealizedArrivalAt (F := F) Q.rows u v)
    (D : RealizedArrivalAt (F := F) Q.rows d v)
    (hsRole : S.target.role = .case2Secondary)
    (htWindow : t.1 ∈ Finset.univ.image (fun j : Fin 7 ↦
      (sevenShift P.next j (sourceIndex P W s.1 s.property)).1))
    (huWindow : u.1 ∈ Finset.univ.image (fun j : Fin 7 ↦
      (sevenShift P.next j (sourceIndex P W s.1 s.property)).1))
    (hdWindow : d.1 ∈ Finset.univ.image (fun j : Fin 7 ↦
      (sevenShift P.next j (sourceIndex P W s.1 s.property)).1))
    (hst : s ≠ t) (hsu : s ≠ u) (hsd : s ≠ d)
    (htu : t ≠ u) (htd : t ≠ d) (hud : u ≠ d)
    (htAssoc : T.descriptor.association = S.descriptor.association)
    (hudAssoc : U.descriptor.association = D.descriptor.association) :
    Fits ((unitDistanceGraph A).degree v)
      ((Q.rows s.1 s.property).localCase.tokens v +
        (Q.rows t.1 t.property).localCase.tokens v +
        (Q.rows u.1 u.property).localCase.tokens v +
        (Q.rows d.1 d.property).localCase.tokens v) := by
  have ht4 := role_eq_case4SplitRight_of_case2_same_association
    hA Q S T hsRole htWindow htAssoc.symm hst
  have huPos : 0 < sourceTokens P W F.chart
      (localCasesOfRealizedRows (F := F) Q.rows) u v := by
    simpa [sourceTokens, selectedCase, localCasesOfRealizedRows] using U.positive
  have hdPos : 0 < sourceTokens P W F.chart
      (localCasesOfRealizedRows (F := F) Q.rows) d v := by
    simpa [sourceTokens, selectedCase, localCasesOfRealizedRows] using D.positive
  have hdWindowFromU := locality.competing_source_in_window huPos hdPos
  have huWindowFromD := locality.competing_source_in_window hdPos huPos
  by_cases hu2 : U.target.role = .case2Secondary
  · have hd4 := role_eq_case4SplitRight_of_case2_same_association
      hA Q U D hu2 hdWindowFromU hudAssoc hud
    have hsHalf := RealizedPositiveTarget.token_eq_one_of_exceptional_secondary
      S.target (Or.inl hsRole)
    have htHalf := RealizedPositiveTarget.token_eq_one_of_exceptional_secondary
      T.target (Or.inr ht4)
    have huHalf := RealizedPositiveTarget.token_eq_one_of_exceptional_secondary
      U.target (Or.inl hu2)
    have hdHalf := RealizedPositiveTarget.token_eq_one_of_exceptional_secondary
      D.target (Or.inr hd4)
    have hdegree : (unitDistanceGraph A).degree v ≤ 5 := by
      rw [S.target.vertex_eq]
      exact S.target.target.degree_le_five
    by_cases hfour : (unitDistanceGraph A).degree v ≤ 4
    · unfold Fits
      omega
    · exact (K2.case2_split_right S U T hsRole hu2 ht4 (by omega)
        huWindow htWindow hsu hst htu.symm).elim
  · by_cases hd2 : D.target.role = .case2Secondary
    · have hu4 := role_eq_case4SplitRight_of_case2_same_association
        hA Q D U hd2 huWindowFromD hudAssoc.symm hud.symm
      have hsHalf := RealizedPositiveTarget.token_eq_one_of_exceptional_secondary
        S.target (Or.inl hsRole)
      have htHalf := RealizedPositiveTarget.token_eq_one_of_exceptional_secondary
        T.target (Or.inr ht4)
      have huHalf := RealizedPositiveTarget.token_eq_one_of_exceptional_secondary
        U.target (Or.inr hu4)
      have hdHalf := RealizedPositiveTarget.token_eq_one_of_exceptional_secondary
        D.target (Or.inl hd2)
      have hdegree : (unitDistanceGraph A).degree v ≤ 5 := by
        rw [S.target.vertex_eq]
        exact S.target.target.degree_le_five
      by_cases hfour : (unitDistanceGraph A).degree v ≤ 4
      · unfold Fits
        omega
      · exact (K2.case2_split_right S D T hsRole hd2 ht4 (by omega)
          hdWindow htWindow hsd hst htd.symm).elim
    · exact (hud (nonCase2_same_association_source_eq Q locality
        direct_direct K4 U D hu2 hd2 hdWindowFromU hudAssoc)).elim

/-- The complete Case-2-anchored quadruple capacity estimate.  Its only
genuine mixed geometric input is the already isolated degree-five
Case-2/Case-2/split residual; no Case-2/split pairwise uniqueness is used. -/
theorem case2AnchoredQuadrupleFits_of_pairwise_and_split_residuals
    (hA : IsOneSeparated A)
    (Q : CommonCoherentRealizedSourceRows P W F.chart)
    (locality : SourceLocalityCertificates P W F)
    (direct_direct : ∀ {s t : Source P W} {v : Vertex A}
      (S : RealizedArrivalAt (F := F) Q.rows s v)
      (T : RealizedArrivalAt (F := F) Q.rows t v),
      IsDirectTargetRole S.target.role →
      IsDirectTargetRole T.target.role →
      t.1 ∈ Finset.univ.image (fun j : Fin 7 ↦
        (sevenShift P.next j (sourceIndex P W s.1 s.property)).1) →
      S.descriptor.association = T.descriptor.association → s = t)
    (K4 : Case4SplitRightResidualKernels Q)
    (K2 : Case2SecondarySplitDegreeFiveResiduals (F := F) Q.rows) :
    Case2AnchoredQuadrupleFits (F := F) Q.rows := by
  intro s t u d v S T U D hsRole htWindow huWindow hdWindow
    hst hsu hsd htu htd hud
  rcases four_association_cases S.descriptor.association
      T.descriptor.association U.descriptor.association
      D.descriptor.association with
    hSTU | hSTD | hSUD | hTUD | hST_UD | hSU_TD | hSD_TU
  · exact (same_association_triple_no_three Q locality direct_direct K4
      S T U hSTU.1 hSTU.2 htWindow huWindow
      hst hsu htu).elim
  · exact (same_association_triple_no_three Q locality direct_direct K4
      S T D hSTD.1 hSTD.2 htWindow hdWindow
      hst hsd htd).elim
  · exact (same_association_triple_no_three Q locality direct_direct K4
      S U D hSUD.1 hSUD.2 huWindow hdWindow
      hsu hsd hud).elim
  · have htPos : 0 < sourceTokens P W F.chart
        (localCasesOfRealizedRows (F := F) Q.rows) t v := by
      simpa [sourceTokens, selectedCase, localCasesOfRealizedRows] using T.positive
    have huPos : 0 < sourceTokens P W F.chart
        (localCasesOfRealizedRows (F := F) Q.rows) u v := by
      simpa [sourceTokens, selectedCase, localCasesOfRealizedRows] using U.positive
    have hdPos : 0 < sourceTokens P W F.chart
        (localCasesOfRealizedRows (F := F) Q.rows) d v := by
      simpa [sourceTokens, selectedCase, localCasesOfRealizedRows] using D.positive
    exact (same_association_triple_no_three Q locality direct_direct K4
      T U D hTUD.1.symm hTUD.2
      (locality.competing_source_in_window htPos huPos)
      (locality.competing_source_in_window htPos hdPos)
      htu htd hud).elim
  · exact case2_quadruple_fits_of_association_pairing hA Q locality
      direct_direct K4 K2 S T U D hsRole htWindow huWindow hdWindow
        hst hsu hsd htu htd hud hST_UD.1 hST_UD.2
  · have hfit := case2_quadruple_fits_of_association_pairing hA Q locality
      direct_direct K4 K2 S U T D hsRole huWindow htWindow hdWindow
        hsu hst hsd htu.symm hud htd hSU_TD.1 hSU_TD.2
    unfold Fits at hfit ⊢
    omega
  · have hfit := case2_quadruple_fits_of_association_pairing hA Q locality
      direct_direct K4 K2 S D T U hsRole hdWindow htWindow huWindow
        hsd hst hsu htd.symm hud.symm htu hSD_TU.1 hSD_TU.2
    unfold Fits at hfit ⊢
    omega

/-- Produced-hull specialization of the Case-2 same-association triple. -/
noncomputable def producedCase2AnchoredSameAssociationTriple
    {A : Finset Point} (hA : IsOneSeparated A)
    (R : Erdos957.RadiallySortedCyclicHullOrder A)
    (L : Erdos957TurnSum.HullOrderBridge.LiftedCyclicHullOrder R.order)
    (W : DiameterWitnessData (ProducedHull R L))
    (K4 : Case4SplitRightResidualKernels
      (P := ProducedHull R L) (W := W) (F := ProducedFrame hA R L)
      (Erdos957CoherentRealizedRows.producedCommonCoherentRealizedSourceRows
        hA R L W)) :
    Case2AnchoredSameAssociationTriple
      (P := ProducedHull R L) (W := W) (F := ProducedFrame hA R L)
      (ProducedRows hA R L W) :=
  case2AnchoredSameAssociationTriple_of_pairwise
    (Erdos957CoherentRealizedRows.producedCommonCoherentRealizedSourceRows
      hA R L W)
    ⟨Erdos957GeometryTransfer.producedCyclicWindowGeometry hA R L W⟩
    (produced_direct_direct hA R L W) K4

/-- Produced-hull specialization of the Case-2 anchored four-source
capacity estimate.  Both fields of the degree-five split residual remain
available to the global weighted record; this constructor consumes only
its `case2_split_right` projection. -/
noncomputable def producedCase2AnchoredQuadrupleFits
    {A : Finset Point} (hA : IsOneSeparated A)
    (R : Erdos957.RadiallySortedCyclicHullOrder A)
    (L : Erdos957TurnSum.HullOrderBridge.LiftedCyclicHullOrder R.order)
    (W : DiameterWitnessData (ProducedHull R L))
    (K4 : Case4SplitRightResidualKernels
      (P := ProducedHull R L) (W := W) (F := ProducedFrame hA R L)
      (Erdos957CoherentRealizedRows.producedCommonCoherentRealizedSourceRows
        hA R L W))
    (K2 : Case2SecondarySplitDegreeFiveResiduals
      (P := ProducedHull R L) (W := W) (F := ProducedFrame hA R L)
      (ProducedRows hA R L W)) :
    Case2AnchoredQuadrupleFits
      (P := ProducedHull R L) (W := W) (F := ProducedFrame hA R L)
      (ProducedRows hA R L W) :=
  case2AnchoredQuadrupleFits_of_pairwise_and_split_residuals hA
    (Erdos957CoherentRealizedRows.producedCommonCoherentRealizedSourceRows
      hA R L W)
    ⟨Erdos957GeometryTransfer.producedCyclicWindowGeometry hA R L W⟩
    (produced_direct_direct hA R L W) K4 K2

end Erdos957Case2WeightedAssembly

namespace Erdos957Case2WeightedAssembly

#print axioms case2Secondary_direct_same_association_source_eq
#print axioms nonCase2_same_association_source_eq
#print axioms case2AnchoredSameAssociationTriple_of_pairwise
#print axioms case2AnchoredQuadrupleFits_of_pairwise_and_split_residuals
#print axioms producedCase2AnchoredSameAssociationTriple
#print axioms producedCase2AnchoredQuadrupleFits

end Erdos957Case2WeightedAssembly
