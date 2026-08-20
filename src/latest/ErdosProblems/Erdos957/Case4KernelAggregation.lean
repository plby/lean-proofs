import ErdosProblems.Erdos957.Case4CollisionLeaves
import ErdosProblems.Erdos957.RoleCollisions
import ErdosProblems.Erdos957.DirectSameSide
import ErdosProblems.Erdos957.Case2SecondaryNoThree
import ErdosProblems.Erdos957.GeometryTransfer

/-!
# Aggregation of the generalized Case-4 collision kernel

The checked metric leaves and pair coherence reduce every direct same-target
competitor to two near cyclic slots.  The first part retains a narrow
same-association interface useful for proving the genuine triple theorem;
it must not be extended to the false pairwise uniqueness of a Case-2 half
arrival against a Case-4 half arrival.  The final part works directly with
exceptional triples and assembles the two side-free secondary-role kernels.
No record in this file assumes a capacity or incoming-sum conclusion.
-/

noncomputable section

namespace Erdos957Case4KernelAggregation

open Erdos957GeometryCore
open Erdos957GeometryLocalRows
open Erdos957CaseClassification
open Erdos957CollisionInstantiation
open Erdos957CoherentRealizedRows
open Erdos957RoleCollisions
open Erdos957Case4CollisionLeaves

abbrev Point := Erdos957GeometryCore.Point

variable {A : Finset Point} {P : CyclicHullData A}
variable {W : DiameterWitnessData P} {F : P.FlatAlignedFrameData}

/-- The two actual cyclic positions left after the common-frame horizontal
gaps and incident-partner coherence: the next continuation through the
partner or the first vertex on the opposite side. -/
def DirectNearTwo
    (Q : CommonCoherentRealizedSourceRows P W F.chart)
    {s t : Source P W} {v : Vertex A}
    (S : RealizedArrivalAt (F := F) Q.rows s v)
    (hsrole : S.target.role = PairCases.TargetRoleName.case4SplitRight) : Prop :=
  let pair := Q.case4_pair s.1 s.property
    ⟨S.target.target, by simpa [hsrole] using S.target.target_at_role⟩
  let side := pair.twoExtreme.side
  sourceIndex P W t.1 t.property =
      incidentContinuationHullVertex P
        (sourceIndex P W s.1 s.property) side 1 ∨
    sourceIndex P W t.1 t.property =
      Erdos957Case4NoThree.awayHullVertex P
        (sourceIndex P W s.1 s.property) side 0

/-- The exact unresolved geometry after the checked finite and metric
reduction.  Each field is a source/role statement, never a capacity bound. -/
structure Case4SplitRightResidualKernels
    (Q : CommonCoherentRealizedSourceRows P W F.chart) where
  direct_near_two : ∀ {s t : Source P W} {v : Vertex A}
    (S : RealizedArrivalAt (F := F) Q.rows s v)
    (T : RealizedArrivalAt (F := F) Q.rows t v)
    (hsrole : S.target.role = .case4SplitRight),
    IsDirectTargetRole T.target.role →
    DirectNearTwo (t := t) Q S hsrole →
    S.descriptor.association = T.descriptor.association → s = t
  split_right_competitor : ∀ {s t : Source P W} {v : Vertex A}
    (S : RealizedArrivalAt (F := F) Q.rows s v)
    (T : RealizedArrivalAt (F := F) Q.rows t v),
    S.target.role = .case4SplitRight →
    T.target.role = .case4SplitRight →
    t.1 ∈ Finset.univ.image (fun j : Fin 7 ↦
      (sevenShift P.next j (sourceIndex P W s.1 s.property)).1) →
    S.descriptor.association = T.descriptor.association → s = t

namespace Case4SplitRightResidualKernels

/-- A role other than the two exceptional secondary roles is one of the
formula-derived direct roles.  Keeping this finite dispatch separate avoids
expanding the full arrival-descriptor context in the main proof. -/
private lemma direct_of_not_exceptional
    {role : PairCases.TargetRoleName}
    (h2 : role ≠ .case2Secondary) (h4 : role ≠ .case4SplitRight) :
    IsDirectTargetRole role := by
  cases role <;> simp_all [IsDirectTargetRole]

/-- The two residual Case-4 geometric leaves, the checked away-prefix
exclusions, and the reversed Case-2 kernel give exactly the production
pairwise Case-4 field. -/
theorem case4_split_right
    {Q : CommonCoherentRealizedSourceRows P W F.chart}
    (locality : SourceLocalityCertificates P W F)
    (case2_secondary : ∀ {s t : Source P W} {v : Vertex A}
      (S : RealizedArrivalAt (F := F) Q.rows s v)
      (T : RealizedArrivalAt (F := F) Q.rows t v),
      S.target.role = .case2Secondary →
      t.1 ∈ Finset.univ.image (fun j : Fin 7 ↦
        (sevenShift P.next j (sourceIndex P W s.1 s.property)).1) →
      S.descriptor.association = T.descriptor.association → s = t)
    (K : Case4SplitRightResidualKernels Q)
    {s t : Source P W} {v : Vertex A}
    (S : RealizedArrivalAt (F := F) Q.rows s v)
    (T : RealizedArrivalAt (F := F) Q.rows t v)
    (hsrole : S.target.role = .case4SplitRight)
    (htWindow : t.1 ∈ Finset.univ.image (fun j : Fin 7 ↦
      (sevenShift P.next j (sourceIndex P W s.1 s.property)).1))
    (hassoc : S.descriptor.association = T.descriptor.association) :
    s = t := by
  by_cases ht2 : T.target.role = .case2Secondary
  · have hsPos : 0 < sourceTokens P W F.chart
        (localCasesOfRealizedRows (F := F) Q.rows) s v := by
      simpa [sourceTokens, selectedCase, localCasesOfRealizedRows] using
        S.positive
    have htPos : 0 < sourceTokens P W F.chart
        (localCasesOfRealizedRows (F := F) Q.rows) t v := by
      simpa [sourceTokens, selectedCase, localCasesOfRealizedRows] using
        T.positive
    have hsFromTWindow := locality.competing_source_in_window htPos hsPos
    exact (case2_secondary T S ht2 hsFromTWindow hassoc.symm).symm
  by_cases ht4 : T.target.role = .case4SplitRight
  · exact K.split_right_competitor S T hsrole ht4 htWindow hassoc
  have htdirect : IsDirectTargetRole T.target.role :=
    direct_of_not_exceptional ht2 ht4
  by_cases hst : s = t
  · exact hst
  have hnear : DirectNearTwo (t := t) Q S hsrole := by
    exact Erdos957Case4CollisionLeaves.direct_competitor_reduces_to_near_two
      Q S.target T.target hsrole ht2 ht4 htWindow hst
  exact K.direct_near_two S T hsrole htdirect hnear hassoc

end Case4SplitRightResidualKernels

/-- Final record-level aggregation: once the direct/direct and Case-2
pairwise fields are supplied, the reduced Case-4 leaves fill the remaining
production field without strengthening its assumptions. -/
theorem roleAnchoredSameSideKernels
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
    (case2_secondary : ∀ {s t : Source P W} {v : Vertex A}
      (S : RealizedArrivalAt (F := F) Q.rows s v)
      (T : RealizedArrivalAt (F := F) Q.rows t v),
      S.target.role = .case2Secondary →
      t.1 ∈ Finset.univ.image (fun j : Fin 7 ↦
        (sevenShift P.next j (sourceIndex P W s.1 s.property)).1) →
      S.descriptor.association = T.descriptor.association → s = t)
    (case4 : Case4SplitRightResidualKernels Q) :
    RoleAnchoredSameSideKernels (F := F) Q.rows where
  direct_direct := direct_direct
  case2_secondary := case2_secondary
  case4_split_right := case4.case4_split_right locality case2_secondary

/-- Final collision witness assembled from the checked role dispatcher.
The Case-2/Case-4 mixed orientation is supplied by `locality`; the only
Case-4-specific inputs are the two fields of
`Case4SplitRightResidualKernels`. -/
theorem noThreeRoleCollisionWitnesses
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
    (case2_secondary : ∀ {s t : Source P W} {v : Vertex A}
      (S : RealizedArrivalAt (F := F) Q.rows s v)
      (T : RealizedArrivalAt (F := F) Q.rows t v),
      S.target.role = .case2Secondary →
      t.1 ∈ Finset.univ.image (fun j : Fin 7 ↦
        (sevenShift P.next j (sourceIndex P W s.1 s.property)).1) →
      S.descriptor.association = T.descriptor.association → s = t)
    (case4 : Case4SplitRightResidualKernels Q) :
    NoThreeRoleCollisionWitnesses P W F
      (localCasesOfRealizedRows (F := F) Q.rows) := by
  let anchored := roleAnchoredSameSideKernels Q locality
    direct_direct case2_secondary case4
  let secondary :=
    Erdos957RoleCollisions.RoleAnchoredSameSideKernels.secondaryRoleCollisionKernels
      locality anchored
  exact Erdos957RoleCollisions.SecondaryRoleCollisionKernels.noThreeRoleCollisionWitnesses
    hA locality secondary

/-! ## Honest exceptional-triple aggregation

Pairwise uniqueness is intentionally not used here: a Case-2 secondary and
a Case-4 split recipient can be two legitimate half arrivals at one target.
The production argument only excludes a third distinct contributor. -/

/-- The sole Case-4-specific triple residual after the checked direct/direct
metric exclusion and symmetry with the Case-2 anchored triple. -/
structure Case4SplitRightNoThreeResidual
    (Q : CommonCoherentRealizedSourceRows P W F.chart) where
  split_right_with_direct : ∀ {s t u : Source P W} {v : Vertex A}
    (S : RealizedArrivalAt (F := F) Q.rows s v)
    (T : RealizedArrivalAt (F := F) Q.rows t v)
    (U : RealizedArrivalAt (F := F) Q.rows u v),
    S.target.role = .case4SplitRight →
    T.target.role = .case4SplitRight →
    IsDirectTargetRole U.target.role →
    t.1 ∈ Finset.univ.image (fun j : Fin 7 ↦
      (sevenShift P.next j (sourceIndex P W s.1 s.property)).1) →
    u.1 ∈ Finset.univ.image (fun j : Fin 7 ↦
      (sevenShift P.next j (sourceIndex P W s.1 s.property)).1) →
    s ≠ t → s ≠ u → t ≠ u → False

  three_split_right : ∀ {s t u : Source P W} {v : Vertex A}
    (S : RealizedArrivalAt (F := F) Q.rows s v)
    (T : RealizedArrivalAt (F := F) Q.rows t v)
    (U : RealizedArrivalAt (F := F) Q.rows u v),
    S.target.role = .case4SplitRight →
    T.target.role = .case4SplitRight →
    U.target.role = .case4SplitRight →
    t.1 ∈ Finset.univ.image (fun j : Fin 7 ↦
      (sevenShift P.next j (sourceIndex P W s.1 s.property)).1) →
    u.1 ∈ Finset.univ.image (fun j : Fin 7 ↦
      (sevenShift P.next j (sourceIndex P W s.1 s.property)).1) →
    s ≠ t → s ≠ u → t ≠ u → False

/-- Once the two exceptional secondary roles have been removed, the finite
role classification is direct.  This is kept out of the large collision
context so simplification does not unfold the dependent realized rows. -/
private lemma direct_of_not_secondary_or_split
    {role : PairCases.TargetRoleName}
    (h2 : role ≠ .case2Secondary) (h4 : role ≠ .case4SplitRight) :
    IsDirectTargetRole role := by
  cases role <;> simp_all [IsDirectTargetRole]

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

/-- Three Boolean arrival associations contain an equal pair.  This tiny
finite fact is separated from the dependent row data used below. -/
private lemma three_associations_have_equal_pair
    (a b c : ArrivalAssociation) : a = b ∨ a = c ∨ b = c := by
  cases a <;> cases b <;> cases c <;> simp

/-- The true Case-4 triple residual follows from two narrow pairwise facts:
same-associated split recipients are unique, and a same-associated direct
competitor is unique.  Crucially this adapter makes no pairwise claim about
a Case-2 secondary against a Case-4 split recipient; that half-plus-half
collision is legitimate. -/
theorem case4SplitRightNoThreeResidual_of_pairwise
    (Q : CommonCoherentRealizedSourceRows P W F.chart)
    (locality : SourceLocalityCertificates P W F)
    (K : Case4SplitRightResidualKernels Q) :
    Case4SplitRightNoThreeResidual Q where
  split_right_with_direct := by
    intro s t u v S T U hsRole htRole huDirect htWindow huWindow hst hsu htu
    rcases three_associations_have_equal_pair
        S.descriptor.association T.descriptor.association
        U.descriptor.association with hST | hSU | hTU
    · exact hst (K.split_right_competitor S T hsRole htRole htWindow hST)
    · have hu2 := direct_ne_case2Secondary huDirect
      have hu4 := direct_ne_case4SplitRight huDirect
      have hnear :=
        Erdos957Case4CollisionLeaves.direct_competitor_reduces_to_near_two
          Q S.target U.target hsRole hu2 hu4 huWindow hsu
      exact hsu (K.direct_near_two S U hsRole huDirect hnear hSU)
    · have htPos : 0 < sourceTokens P W F.chart
          (localCasesOfRealizedRows (F := F) Q.rows) t v := by
        simpa [sourceTokens, selectedCase, localCasesOfRealizedRows] using
          T.positive
      have huPos : 0 < sourceTokens P W F.chart
          (localCasesOfRealizedRows (F := F) Q.rows) u v := by
        simpa [sourceTokens, selectedCase, localCasesOfRealizedRows] using
          U.positive
      have huFromT := locality.competing_source_in_window htPos huPos
      have hu2 := direct_ne_case2Secondary huDirect
      have hu4 := direct_ne_case4SplitRight huDirect
      have hnear :=
        Erdos957Case4CollisionLeaves.direct_competitor_reduces_to_near_two
          Q T.target U.target htRole hu2 hu4 huFromT htu
      exact htu (K.direct_near_two T U htRole huDirect hnear hTU)
  three_split_right := by
    intro s t u v S T U hsRole htRole huRole htWindow huWindow hst hsu htu
    rcases three_associations_have_equal_pair
        S.descriptor.association T.descriptor.association
        U.descriptor.association with hST | hSU | hTU
    · exact hst (K.split_right_competitor S T hsRole htRole htWindow hST)
    · exact hsu (K.split_right_competitor S U hsRole huRole huWindow hSU)
    · have htPos : 0 < sourceTokens P W F.chart
          (localCasesOfRealizedRows (F := F) Q.rows) t v := by
        simpa [sourceTokens, selectedCase, localCasesOfRealizedRows] using
          T.positive
      have huPos : 0 < sourceTokens P W F.chart
          (localCasesOfRealizedRows (F := F) Q.rows) u v := by
        simpa [sourceTokens, selectedCase, localCasesOfRealizedRows] using
          U.positive
      have huFromT := locality.competing_source_in_window htPos huPos
      exact htu
        (K.split_right_competitor T U htRole huRole huFromT hTU)

/-- Re-anchor at Case 2 when possible; if both competitors are direct, the
two-slot reduction makes them three hull steps apart. -/
theorem case4_split_right_no_three
    (Q : CommonCoherentRealizedSourceRows P W F.chart)
    (locality : SourceLocalityCertificates P W F)
    (case2NoThree : ∀ {s t u : Source P W} {v : Vertex A}
      (Ds : RealizedPositiveTarget (Q.rows s.1 s.property) v)
      (Dt : RealizedPositiveTarget (Q.rows t.1 t.property) v)
      (Du : RealizedPositiveTarget (Q.rows u.1 u.property) v),
      Ds.role = .case2Secondary →
      t.1 ∈ Finset.univ.image (fun j : Fin 7 ↦
        (sevenShift P.next j (sourceIndex P W s.1 s.property)).1) →
      u.1 ∈ Finset.univ.image (fun j : Fin 7 ↦
        (sevenShift P.next j (sourceIndex P W s.1 s.property)).1) →
      s ≠ t → s ≠ u → t ≠ u → False)
    (K : Case4SplitRightNoThreeResidual Q) :
    ∀ {s t u : Source P W} {v : Vertex A}
      (Ds : RealizedPositiveTarget (Q.rows s.1 s.property) v)
      (Dt : RealizedPositiveTarget (Q.rows t.1 t.property) v)
      (Du : RealizedPositiveTarget (Q.rows u.1 u.property) v),
      Ds.role = .case4SplitRight →
      t.1 ∈ Finset.univ.image (fun j : Fin 7 ↦
        (sevenShift P.next j (sourceIndex P W s.1 s.property)).1) →
      u.1 ∈ Finset.univ.image (fun j : Fin 7 ↦
        (sevenShift P.next j (sourceIndex P W s.1 s.property)).1) →
      s ≠ t → s ≠ u → t ≠ u → False := by
  intro s t u v Ds Dt Du hsRole htWindow huWindow hst hsu htu
  let S := realizedArrivalAtOfTarget (F := F) Q.rows s v Ds
  let T := realizedArrivalAtOfTarget (F := F) Q.rows t v Dt
  let U := realizedArrivalAtOfTarget (F := F) Q.rows u v Du
  have hsPos : 0 < sourceTokens P W F.chart
      (localCasesOfRealizedRows (F := F) Q.rows) s v := by
    simpa [sourceTokens, selectedCase, localCasesOfRealizedRows] using S.positive
  have htPos : 0 < sourceTokens P W F.chart
      (localCasesOfRealizedRows (F := F) Q.rows) t v := by
    simpa [sourceTokens, selectedCase, localCasesOfRealizedRows] using T.positive
  have huPos : 0 < sourceTokens P W F.chart
      (localCasesOfRealizedRows (F := F) Q.rows) u v := by
    simpa [sourceTokens, selectedCase, localCasesOfRealizedRows] using U.positive
  by_cases ht2 : Dt.role = .case2Secondary
  · exact case2NoThree Dt Ds Du ht2
      (locality.competing_source_in_window htPos hsPos)
      (locality.competing_source_in_window htPos huPos)
      hst.symm htu hsu
  by_cases hu2 : Du.role = .case2Secondary
  · exact case2NoThree Du Ds Dt hu2
      (locality.competing_source_in_window huPos hsPos)
      (locality.competing_source_in_window huPos htPos)
      hsu.symm htu.symm hst
  by_cases ht4 : Dt.role = .case4SplitRight
  · by_cases hu4 : Du.role = .case4SplitRight
    · exact K.three_split_right S T U hsRole ht4 hu4
        htWindow huWindow hst hsu htu
    · have huDirect : IsDirectTargetRole Du.role := by
        exact direct_of_not_secondary_or_split hu2 hu4
      exact K.split_right_with_direct S T U hsRole ht4 huDirect
        htWindow huWindow hst hsu htu
  by_cases hu4 : Du.role = .case4SplitRight
  · have htDirect : IsDirectTargetRole Dt.role := by
      exact direct_of_not_secondary_or_split ht2 ht4
    exact K.split_right_with_direct S U T hsRole hu4 htDirect
      huWindow htWindow hsu hst htu.symm
  exact Erdos957Case4CollisionLeaves.no_two_direct_competitors_of_split_right
    Q Ds Dt Du hsRole ht2 ht4 hu2 hu4 htWindow huWindow hst hsu htu

/-- True no-three record aggregation, permitting exceptional half+half
pairs while excluding any third source. -/
theorem secondaryRoleCollisionKernels
    (Q : CommonCoherentRealizedSourceRows P W F.chart)
    (locality : SourceLocalityCertificates P W F)
    (case2NoThree : ∀ {s t u : Source P W} {v : Vertex A}
      (Ds : RealizedPositiveTarget (Q.rows s.1 s.property) v)
      (Dt : RealizedPositiveTarget (Q.rows t.1 t.property) v)
      (Du : RealizedPositiveTarget (Q.rows u.1 u.property) v),
      Ds.role = .case2Secondary →
      t.1 ∈ Finset.univ.image (fun j : Fin 7 ↦
        (sevenShift P.next j (sourceIndex P W s.1 s.property)).1) →
      u.1 ∈ Finset.univ.image (fun j : Fin 7 ↦
        (sevenShift P.next j (sourceIndex P W s.1 s.property)).1) →
      s ≠ t → s ≠ u → t ≠ u → False)
    (K : Case4SplitRightNoThreeResidual Q) :
    SecondaryRoleCollisionKernels (F := F) Q.rows where
  case2_secondary_no_three := case2NoThree
  case4_split_right_no_three :=
    case4_split_right_no_three Q locality case2NoThree K

/-! ## Produced pairwise collision assembly -/

/-- On the canonical produced hull, the genuine cyclic window and all
direct/direct roles are already discharged.  The two small formula residual
records therefore assemble the exact paper-style two-sided collision
witness consumed by the production transfer theorem. -/
noncomputable def producedRoleCollisionWitnesses
    {A : Finset Point} (hA : IsOneSeparated A)
    (R : Erdos957.RadiallySortedCyclicHullOrder A)
    (L : Erdos957TurnSum.HullOrderBridge.LiftedCyclicHullOrder R.order)
    (W : DiameterWitnessData (Erdos957DirectSameSide.ProducedHull R L))
    (K2 : Erdos957Case2SecondaryNoThree.Case2SecondarySameSideResiduals
      (P := Erdos957DirectSameSide.ProducedHull R L) (W := W)
      (F := Erdos957DirectSameSide.ProducedFrame hA R L)
      (Erdos957DirectSameSide.ProducedRows hA R L W))
    (K4 : Case4SplitRightResidualKernels
      (P := Erdos957DirectSameSide.ProducedHull R L) (W := W)
      (F := Erdos957DirectSameSide.ProducedFrame hA R L)
      (Erdos957CoherentRealizedRows.producedCommonCoherentRealizedSourceRows
        hA R L W)) :
    RoleCollisionWitnesses
      (Erdos957DirectSameSide.ProducedHull R L) W
      (Erdos957DirectSameSide.ProducedFrame hA R L)
      (localCasesOfRealizedRows
        (F := Erdos957DirectSameSide.ProducedFrame hA R L)
        (Erdos957DirectSameSide.ProducedRows hA R L W)) := by
  let Q :=
    Erdos957CoherentRealizedRows.producedCommonCoherentRealizedSourceRows
      hA R L W
  let locality : SourceLocalityCertificates
      (Erdos957DirectSameSide.ProducedHull R L) W
      (Erdos957DirectSameSide.ProducedFrame hA R L) :=
    ⟨Erdos957GeometryTransfer.producedCyclicWindowGeometry hA R L W⟩
  have case2 : ∀
      {s t : Source (Erdos957DirectSameSide.ProducedHull R L) W}
      {v : Vertex A}
      (S : RealizedArrivalAt
        (F := Erdos957DirectSameSide.ProducedFrame hA R L)
        (Erdos957DirectSameSide.ProducedRows hA R L W) s v)
      (T : RealizedArrivalAt
        (F := Erdos957DirectSameSide.ProducedFrame hA R L)
        (Erdos957DirectSameSide.ProducedRows hA R L W) t v),
      S.target.role = .case2Secondary →
      t.1 ∈ Finset.univ.image (fun j : Fin 7 ↦
        (sevenShift (Erdos957DirectSameSide.ProducedHull R L).next j
          (sourceIndex (Erdos957DirectSameSide.ProducedHull R L) W
            s.1 s.property)).1) →
      S.descriptor.association = T.descriptor.association → s = t := by
    intro s t v S T hsRole htWindow hassoc
    exact Erdos957Case2SecondaryNoThree.Case2SecondarySameSideResiduals.case2_secondary_role_kernel
      hA K2 S T hsRole htWindow hassoc
  let anchored := roleAnchoredSameSideKernels Q locality
    (Erdos957DirectSameSide.produced_direct_direct hA R L W) case2 K4
  let cases :=
    Erdos957RoleCollisions.RoleAnchoredSameSideKernels.realizedSameSideKernels
      locality anchored
  exact Erdos957RoleCollisions.RealizedSameSideKernels.roleCollisionWitnesses
    locality cases

end Erdos957Case4KernelAggregation

#print axioms Erdos957Case4KernelAggregation.Case4SplitRightResidualKernels.case4_split_right
#print axioms Erdos957Case4KernelAggregation.roleAnchoredSameSideKernels
#print axioms Erdos957Case4KernelAggregation.noThreeRoleCollisionWitnesses
#print axioms Erdos957Case4KernelAggregation.case4SplitRightNoThreeResidual_of_pairwise
#print axioms Erdos957Case4KernelAggregation.case4_split_right_no_three
#print axioms Erdos957Case4KernelAggregation.secondaryRoleCollisionKernels
#print axioms Erdos957Case4KernelAggregation.producedRoleCollisionWitnesses
