import ErdosProblems.Erdos957.GeometryTransfer
import ErdosProblems.Erdos957.CoherentRealizedRows
import ErdosProblems.Erdos957.DirectSameSide
import ErdosProblems.Erdos957.Case2SecondaryNoThree
import ErdosProblems.Erdos957.Case4SplitClassification

/-!
# Weight-aware role collision aggregation for Erdős 957

This module dispatches the final collision statement without imposing false
blanket contributor uniqueness.  It allows safe triples and quadruples,
proves their exact `Fits` estimates, and derives the sharp no-five count from
the weaker theorem excluding three same-associated arrivals.
-/

noncomputable section

namespace Erdos957WeightedRoleCollisions

open Erdos957GeometryCore
open Erdos957GeometryLocalRows
open Erdos957CollisionInstantiation
open Erdos957CaseClassification
open Erdos957RoleCollisions
open Erdos957CoherentRealizedRows
open Erdos957Overcharge
open Erdos957Case2SecondaryNoThree
open Erdos957Case4SplitClassification

abbrev Point := Erdos957GeometryCore.Point

variable {A : Finset Point} {P : CyclicHullData A}
variable {W : DiameterWitnessData P} {F : P.FlatAlignedFrameData}

/-- The Case-2-anchored four-source local capacity theorem. -/
def Case2AnchoredQuadrupleFits
    (rows : HasRealizedSourceRows P W F.chart) : Prop :=
  ∀ {s t u d : Source P W} {v : Vertex A}
    (S : RealizedArrivalAt (F := F) rows s v)
    (T : RealizedArrivalAt (F := F) rows t v)
    (U : RealizedArrivalAt (F := F) rows u v)
    (D : RealizedArrivalAt (F := F) rows d v),
    S.target.role = .case2Secondary →
    t.1 ∈ Finset.univ.image (fun j : Fin 7 ↦
      (sevenShift P.next j (sourceIndex P W s.1 s.property)).1) →
    u.1 ∈ Finset.univ.image (fun j : Fin 7 ↦
      (sevenShift P.next j (sourceIndex P W s.1 s.property)).1) →
    d.1 ∈ Finset.univ.image (fun j : Fin 7 ↦
      (sevenShift P.next j (sourceIndex P W s.1 s.property)).1) →
    s ≠ t → s ≠ u → s ≠ d →
    t ≠ u → t ≠ d → u ≠ d →
    Fits ((unitDistanceGraph A).degree v)
      ((rows s.1 s.property).localCase.tokens v +
        (rows t.1 t.property).localCase.tokens v +
        (rows u.1 u.property).localCase.tokens v +
        (rows d.1 d.property).localCase.tokens v)

/-- The Case-2 part of the no-five argument: three distinct arrivals with
the anchor's association cannot include a Case-2 secondary anchor. -/
def Case2AnchoredSameAssociationTriple
    (rows : HasRealizedSourceRows P W F.chart) : Prop :=
  ∀ {s t u : Source P W} {v : Vertex A}
    (S : RealizedArrivalAt (F := F) rows s v)
    (T : RealizedArrivalAt (F := F) rows t v)
    (U : RealizedArrivalAt (F := F) rows u v),
    S.target.role = .case2Secondary →
    T.descriptor.association = S.descriptor.association →
    U.descriptor.association = S.descriptor.association →
    t.1 ∈ Finset.univ.image (fun j : Fin 7 ↦
      (sevenShift P.next j (sourceIndex P W s.1 s.property)).1) →
    u.1 ∈ Finset.univ.image (fun j : Fin 7 ↦
      (sevenShift P.next j (sourceIndex P W s.1 s.property)).1) →
    s ≠ t → s ≠ u → t ≠ u → False

/-- Exact geometric residue after the uniform direct-role dispatch. -/
structure WeightedRoleCollisionResiduals
    (Q : CommonCoherentRealizedSourceRows P W F.chart) where
  case2_degree_five :
    Case2SecondaryDegreeFiveResiduals (F := F) Q.rows
  case4_weighted : Case4WeightedCollisionResiduals Q
  case2_quadruple_fits : Case2AnchoredQuadrupleFits (F := F) Q.rows
  case2_same_association_triple :
    Case2AnchoredSameAssociationTriple (F := F) Q.rows

private lemma direct_of_not_exceptional
    {role : PairCases.TargetRoleName}
    (h2 : role ≠ .case2Secondary) (h4 : role ≠ .case4SplitRight) :
    IsDirectTargetRole role := by
  cases role <;> simp_all [IsDirectTargetRole]

private lemma three_associations_have_equal_pair
    (a b c : ArrivalAssociation) : a = b ∨ a = c ∨ b = c := by
  cases a <;> cases b <;> cases c <;> simp

/-- Bundle the exact selected enriched row underlying a positive global
source token. -/
noncomputable def arrivalOfPositive
    (Q : CommonCoherentRealizedSourceRows P W F.chart)
    (s : Source P W) (v : Vertex A)
    (h : 0 < sourceTokens P W F.chart
      (localCasesOfRealizedRows (F := F) Q.rows) s v) :
    RealizedArrivalAt (F := F) Q.rows s v := by
  apply realizedArrivalAtOfPositive (F := F) Q.rows s v
  simpa [sourceTokens, selectedCase, localCasesOfRealizedRows] using h

/-- Role dispatch for an actual triple.  A Case-2 or Case-4 exceptional
anchor is handled by its formula residual record.  If all three roles are
direct, two of their two-valued associations coincide, contradicting the
checked direct/direct uniqueness. -/
theorem triple_fits
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
    (K : WeightedRoleCollisionResiduals Q)
    {a b c : Source P W} {v : Vertex A}
    (ha : 0 < sourceTokens P W F.chart
      (localCasesOfRealizedRows (F := F) Q.rows) a v)
    (hb : 0 < sourceTokens P W F.chart
      (localCasesOfRealizedRows (F := F) Q.rows) b v)
    (hc : 0 < sourceTokens P W F.chart
      (localCasesOfRealizedRows (F := F) Q.rows) c v)
    (hbWindow : b.1 ∈ Finset.univ.image (fun j : Fin 7 ↦
      (sevenShift P.next j (sourceIndex P W a.1 a.property)).1))
    (hcWindow : c.1 ∈ Finset.univ.image (fun j : Fin 7 ↦
      (sevenShift P.next j (sourceIndex P W a.1 a.property)).1))
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    Fits ((unitDistanceGraph A).degree v)
      (sourceTokens P W F.chart
          (localCasesOfRealizedRows (F := F) Q.rows) a v +
        sourceTokens P W F.chart
          (localCasesOfRealizedRows (F := F) Q.rows) b v +
        sourceTokens P W F.chart
          (localCasesOfRealizedRows (F := F) Q.rows) c v) := by
  let S := arrivalOfPositive Q a v ha
  let T := arrivalOfPositive Q b v hb
  let U := arrivalOfPositive Q c v hc
  change 2 * (unitDistanceGraph A).degree v +
    ((Q.rows a.1 a.property).localCase.tokens v +
      (Q.rows b.1 b.property).localCase.tokens v +
      (Q.rows c.1 c.property).localCase.tokens v) ≤ 12
  by_cases hs2 : S.target.role = .case2Secondary
  · have hfit := case2_secondary_triple_fits_of_degree_five_residuals
      hA locality K.case2_degree_five S T U hs2 hbWindow hcWindow hab hac hbc
    omega
  by_cases ht2 : T.target.role = .case2Secondary
  · have haFromB := locality.competing_source_in_window hb ha
    have hcFromB := locality.competing_source_in_window hb hc
    have hfit := case2_secondary_triple_fits_of_degree_five_residuals
      hA locality K.case2_degree_five T S U ht2 haFromB hcFromB
        hab.symm hbc hac
    have hsum :
        (Q.rows b.1 b.property).localCase.tokens v +
            (Q.rows a.1 a.property).localCase.tokens v +
            (Q.rows c.1 c.property).localCase.tokens v =
          (Q.rows a.1 a.property).localCase.tokens v +
            (Q.rows b.1 b.property).localCase.tokens v +
            (Q.rows c.1 c.property).localCase.tokens v := by omega
    omega
  by_cases hu2 : U.target.role = .case2Secondary
  · have haFromC := locality.competing_source_in_window hc ha
    have hbFromC := locality.competing_source_in_window hc hb
    have hfit := case2_secondary_triple_fits_of_degree_five_residuals
      hA locality K.case2_degree_five U S T hu2 haFromC hbFromC
        hac.symm hbc.symm hab
    have hsum :
        (Q.rows c.1 c.property).localCase.tokens v +
            (Q.rows a.1 a.property).localCase.tokens v +
            (Q.rows b.1 b.property).localCase.tokens v =
          (Q.rows a.1 a.property).localCase.tokens v +
            (Q.rows b.1 b.property).localCase.tokens v +
            (Q.rows c.1 c.property).localCase.tokens v := by omega
    omega
  by_cases hs4 : S.target.role = .case4SplitRight
  · exact K.case4_weighted.triple_fits_of_no_case2_secondary hA
      S T U hs4 ht2 hu2 hbWindow hcWindow hab hac hbc
  by_cases ht4 : T.target.role = .case4SplitRight
  · have haFromB := locality.competing_source_in_window hb ha
    have hcFromB := locality.competing_source_in_window hb hc
    have hfit := K.case4_weighted.triple_fits_of_no_case2_secondary hA
      T S U ht4 hs2 hu2 haFromB hcFromB hab.symm hbc hac
    change 2 * (unitDistanceGraph A).degree v +
      ((Q.rows b.1 b.property).localCase.tokens v +
        (Q.rows a.1 a.property).localCase.tokens v +
        (Q.rows c.1 c.property).localCase.tokens v) ≤ 12 at hfit
    have hsum :
        (Q.rows b.1 b.property).localCase.tokens v +
            (Q.rows a.1 a.property).localCase.tokens v +
            (Q.rows c.1 c.property).localCase.tokens v =
          (Q.rows a.1 a.property).localCase.tokens v +
            (Q.rows b.1 b.property).localCase.tokens v +
            (Q.rows c.1 c.property).localCase.tokens v := by omega
    omega
  by_cases hu4 : U.target.role = .case4SplitRight
  · have haFromC := locality.competing_source_in_window hc ha
    have hbFromC := locality.competing_source_in_window hc hb
    have hfit := K.case4_weighted.triple_fits_of_no_case2_secondary hA
      U S T hu4 hs2 ht2 haFromC hbFromC hac.symm hbc.symm hab
    change 2 * (unitDistanceGraph A).degree v +
      ((Q.rows c.1 c.property).localCase.tokens v +
        (Q.rows a.1 a.property).localCase.tokens v +
        (Q.rows b.1 b.property).localCase.tokens v) ≤ 12 at hfit
    have hsum :
        (Q.rows c.1 c.property).localCase.tokens v +
            (Q.rows a.1 a.property).localCase.tokens v +
            (Q.rows b.1 b.property).localCase.tokens v =
          (Q.rows a.1 a.property).localCase.tokens v +
            (Q.rows b.1 b.property).localCase.tokens v +
            (Q.rows c.1 c.property).localCase.tokens v := by omega
    omega
  have hsDirect := direct_of_not_exceptional hs2 hs4
  have htDirect := direct_of_not_exceptional ht2 ht4
  have huDirect := direct_of_not_exceptional hu2 hu4
  rcases three_associations_have_equal_pair
      S.descriptor.association T.descriptor.association
      U.descriptor.association with hST | hSU | hTU
  · exact (hab (direct_direct S T hsDirect htDirect hbWindow hST)).elim
  · exact (hac (direct_direct S U hsDirect huDirect hcWindow hSU)).elim
  · have hcFromB := locality.competing_source_in_window hb hc
    exact (hbc (direct_direct T U htDirect huDirect hcFromB hTU)).elim

/-- A split-right anchored, no-Case-2 quadruple is either one of the two
retained safe shapes or contains two direct competitors, which is already
impossible. -/
private theorem case4_quadruple_fits_of_no_case2
    (Q : CommonCoherentRealizedSourceRows P W F.chart)
    (K : Case4WeightedCollisionResiduals Q)
    {s t u d : Source P W} {v : Vertex A}
    (S : RealizedArrivalAt (F := F) Q.rows s v)
    (T : RealizedArrivalAt (F := F) Q.rows t v)
    (U : RealizedArrivalAt (F := F) Q.rows u v)
    (D : RealizedArrivalAt (F := F) Q.rows d v)
    (hs4 : S.target.role = .case4SplitRight)
    (ht2 : T.target.role ≠ .case2Secondary)
    (hu2 : U.target.role ≠ .case2Secondary)
    (hd2 : D.target.role ≠ .case2Secondary)
    (htWindow : t.1 ∈ Finset.univ.image (fun j : Fin 7 ↦
      (sevenShift P.next j (sourceIndex P W s.1 s.property)).1))
    (huWindow : u.1 ∈ Finset.univ.image (fun j : Fin 7 ↦
      (sevenShift P.next j (sourceIndex P W s.1 s.property)).1))
    (hdWindow : d.1 ∈ Finset.univ.image (fun j : Fin 7 ↦
      (sevenShift P.next j (sourceIndex P W s.1 s.property)).1))
    (hst : s ≠ t) (hsu : s ≠ u) (hsd : s ≠ d)
    (htu : t ≠ u) (htd : t ≠ d) (hud : u ≠ d) :
    Fits ((unitDistanceGraph A).degree v)
      ((Q.rows s.1 s.property).localCase.tokens v +
        (Q.rows t.1 t.property).localCase.tokens v +
        (Q.rows u.1 u.property).localCase.tokens v +
        (Q.rows d.1 d.property).localCase.tokens v) := by
  by_cases ht4 : T.target.role = .case4SplitRight
  · by_cases hu4 : U.target.role = .case4SplitRight
    · by_cases hd4 : D.target.role = .case4SplitRight
      · exact K.four_split_right_quadruple_fits S T U D hs4 ht4 hu4 hd4
          htWindow huWindow hdWindow hst hsu hsd htu htd hud
      · exact K.three_split_right_one_direct_quadruple_fits S T U D
          hs4 ht4 hu4 (direct_of_not_exceptional hd2 hd4)
          htWindow huWindow hdWindow hst hsu hsd htu htd hud
    · by_cases hd4 : D.target.role = .case4SplitRight
      · have hfit := K.three_split_right_one_direct_quadruple_fits S T D U
          hs4 ht4 hd4 (direct_of_not_exceptional hu2 hu4)
          htWindow hdWindow huWindow hst hsd hsu htd htu hud.symm
        have hsum :
            (Q.rows s.1 s.property).localCase.tokens v +
                (Q.rows t.1 t.property).localCase.tokens v +
                (Q.rows d.1 d.property).localCase.tokens v +
                (Q.rows u.1 u.property).localCase.tokens v =
              (Q.rows s.1 s.property).localCase.tokens v +
                (Q.rows t.1 t.property).localCase.tokens v +
                (Q.rows u.1 u.property).localCase.tokens v +
                (Q.rows d.1 d.property).localCase.tokens v := by omega
        rw [hsum] at hfit
        exact hfit
      · exact (Erdos957Case4CollisionLeaves.no_two_direct_competitors_of_split_right
          Q S.target U.target D.target hs4 hu2 hu4 hd2 hd4
            huWindow hdWindow hsu hsd hud).elim
  · by_cases hu4 : U.target.role = .case4SplitRight
    · by_cases hd4 : D.target.role = .case4SplitRight
      · have hfit := K.three_split_right_one_direct_quadruple_fits S U D T
          hs4 hu4 hd4 (direct_of_not_exceptional ht2 ht4)
          huWindow hdWindow htWindow hsu hsd hst hud htu.symm htd.symm
        have hsum :
            (Q.rows s.1 s.property).localCase.tokens v +
                (Q.rows u.1 u.property).localCase.tokens v +
                (Q.rows d.1 d.property).localCase.tokens v +
                (Q.rows t.1 t.property).localCase.tokens v =
              (Q.rows s.1 s.property).localCase.tokens v +
                (Q.rows t.1 t.property).localCase.tokens v +
                (Q.rows u.1 u.property).localCase.tokens v +
                (Q.rows d.1 d.property).localCase.tokens v := by omega
        rw [hsum] at hfit
        exact hfit
      · exact (Erdos957Case4CollisionLeaves.no_two_direct_competitors_of_split_right
          Q S.target T.target D.target hs4 ht2 ht4 hd2 hd4
            htWindow hdWindow hst hsd htd).elim
    · exact (Erdos957Case4CollisionLeaves.no_two_direct_competitors_of_split_right
        Q S.target T.target U.target hs4 ht2 ht4 hu2 hu4
          htWindow huWindow hst hsu htu).elim

/-- Quadruple role dispatch, retaining safe four-source columns. -/
theorem quadruple_fits
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
    (K : WeightedRoleCollisionResiduals Q)
    {a b c d : Source P W} {v : Vertex A}
    (ha : 0 < sourceTokens P W F.chart
      (localCasesOfRealizedRows (F := F) Q.rows) a v)
    (hb : 0 < sourceTokens P W F.chart
      (localCasesOfRealizedRows (F := F) Q.rows) b v)
    (hc : 0 < sourceTokens P W F.chart
      (localCasesOfRealizedRows (F := F) Q.rows) c v)
    (hd : 0 < sourceTokens P W F.chart
      (localCasesOfRealizedRows (F := F) Q.rows) d v)
    (hbWindow : b.1 ∈ Finset.univ.image (fun j : Fin 7 ↦
      (sevenShift P.next j (sourceIndex P W a.1 a.property)).1))
    (hcWindow : c.1 ∈ Finset.univ.image (fun j : Fin 7 ↦
      (sevenShift P.next j (sourceIndex P W a.1 a.property)).1))
    (hdWindow : d.1 ∈ Finset.univ.image (fun j : Fin 7 ↦
      (sevenShift P.next j (sourceIndex P W a.1 a.property)).1))
    (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d)
    (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d) :
    Fits ((unitDistanceGraph A).degree v)
      (sourceTokens P W F.chart
          (localCasesOfRealizedRows (F := F) Q.rows) a v +
        sourceTokens P W F.chart
          (localCasesOfRealizedRows (F := F) Q.rows) b v +
        sourceTokens P W F.chart
          (localCasesOfRealizedRows (F := F) Q.rows) c v +
        sourceTokens P W F.chart
          (localCasesOfRealizedRows (F := F) Q.rows) d v) := by
  let S := arrivalOfPositive Q a v ha
  let T := arrivalOfPositive Q b v hb
  let U := arrivalOfPositive Q c v hc
  let D := arrivalOfPositive Q d v hd
  change Fits ((unitDistanceGraph A).degree v)
    ((Q.rows a.1 a.property).localCase.tokens v +
      (Q.rows b.1 b.property).localCase.tokens v +
      (Q.rows c.1 c.property).localCase.tokens v +
      (Q.rows d.1 d.property).localCase.tokens v)
  by_cases hs2 : S.target.role = .case2Secondary
  · exact K.case2_quadruple_fits S T U D hs2 hbWindow hcWindow hdWindow
      hab hac had hbc hbd hcd
  by_cases ht2 : T.target.role = .case2Secondary
  · have hfit := K.case2_quadruple_fits T S U D ht2
      (locality.competing_source_in_window hb ha)
      (locality.competing_source_in_window hb hc)
      (locality.competing_source_in_window hb hd)
      hab.symm hbc hbd hac had hcd
    have hsum :
        (Q.rows b.1 b.property).localCase.tokens v +
            (Q.rows a.1 a.property).localCase.tokens v +
            (Q.rows c.1 c.property).localCase.tokens v +
            (Q.rows d.1 d.property).localCase.tokens v =
          (Q.rows a.1 a.property).localCase.tokens v +
            (Q.rows b.1 b.property).localCase.tokens v +
            (Q.rows c.1 c.property).localCase.tokens v +
            (Q.rows d.1 d.property).localCase.tokens v := by omega
    rw [hsum] at hfit
    exact hfit
  by_cases hu2 : U.target.role = .case2Secondary
  · have hfit := K.case2_quadruple_fits U S T D hu2
      (locality.competing_source_in_window hc ha)
      (locality.competing_source_in_window hc hb)
      (locality.competing_source_in_window hc hd)
      hac.symm hbc.symm hcd hab had hbd
    have hsum :
        (Q.rows c.1 c.property).localCase.tokens v +
            (Q.rows a.1 a.property).localCase.tokens v +
            (Q.rows b.1 b.property).localCase.tokens v +
            (Q.rows d.1 d.property).localCase.tokens v =
          (Q.rows a.1 a.property).localCase.tokens v +
            (Q.rows b.1 b.property).localCase.tokens v +
            (Q.rows c.1 c.property).localCase.tokens v +
            (Q.rows d.1 d.property).localCase.tokens v := by omega
    rw [hsum] at hfit
    exact hfit
  by_cases hd2 : D.target.role = .case2Secondary
  · have hfit := K.case2_quadruple_fits D S T U hd2
      (locality.competing_source_in_window hd ha)
      (locality.competing_source_in_window hd hb)
      (locality.competing_source_in_window hd hc)
      had.symm hbd.symm hcd.symm hab hac hbc
    have hsum :
        (Q.rows d.1 d.property).localCase.tokens v +
            (Q.rows a.1 a.property).localCase.tokens v +
            (Q.rows b.1 b.property).localCase.tokens v +
            (Q.rows c.1 c.property).localCase.tokens v =
          (Q.rows a.1 a.property).localCase.tokens v +
            (Q.rows b.1 b.property).localCase.tokens v +
            (Q.rows c.1 c.property).localCase.tokens v +
            (Q.rows d.1 d.property).localCase.tokens v := by omega
    rw [hsum] at hfit
    exact hfit
  by_cases hs4 : S.target.role = .case4SplitRight
  · exact case4_quadruple_fits_of_no_case2 Q K.case4_weighted S T U D hs4
      ht2 hu2 hd2 hbWindow hcWindow hdWindow hab hac had hbc hbd hcd
  by_cases ht4 : T.target.role = .case4SplitRight
  · have hfit := case4_quadruple_fits_of_no_case2 Q K.case4_weighted T S U D ht4
      hs2 hu2 hd2
      (locality.competing_source_in_window hb ha)
      (locality.competing_source_in_window hb hc)
      (locality.competing_source_in_window hb hd)
      hab.symm hbc hbd hac had hcd
    have hsum :
        (Q.rows b.1 b.property).localCase.tokens v +
            (Q.rows a.1 a.property).localCase.tokens v +
            (Q.rows c.1 c.property).localCase.tokens v +
            (Q.rows d.1 d.property).localCase.tokens v =
          (Q.rows a.1 a.property).localCase.tokens v +
            (Q.rows b.1 b.property).localCase.tokens v +
            (Q.rows c.1 c.property).localCase.tokens v +
            (Q.rows d.1 d.property).localCase.tokens v := by omega
    rw [hsum] at hfit
    exact hfit
  by_cases hu4 : U.target.role = .case4SplitRight
  · have hfit := case4_quadruple_fits_of_no_case2 Q K.case4_weighted U S T D hu4
      hs2 ht2 hd2
      (locality.competing_source_in_window hc ha)
      (locality.competing_source_in_window hc hb)
      (locality.competing_source_in_window hc hd)
      hac.symm hbc.symm hcd hab had hbd
    have hsum :
        (Q.rows c.1 c.property).localCase.tokens v +
            (Q.rows a.1 a.property).localCase.tokens v +
            (Q.rows b.1 b.property).localCase.tokens v +
            (Q.rows d.1 d.property).localCase.tokens v =
          (Q.rows a.1 a.property).localCase.tokens v +
            (Q.rows b.1 b.property).localCase.tokens v +
            (Q.rows c.1 c.property).localCase.tokens v +
            (Q.rows d.1 d.property).localCase.tokens v := by omega
    rw [hsum] at hfit
    exact hfit
  by_cases hd4 : D.target.role = .case4SplitRight
  · have hfit := case4_quadruple_fits_of_no_case2 Q K.case4_weighted D S T U hd4
      hs2 ht2 hu2
      (locality.competing_source_in_window hd ha)
      (locality.competing_source_in_window hd hb)
      (locality.competing_source_in_window hd hc)
      had.symm hbd.symm hcd.symm hab hac hbc
    have hsum :
        (Q.rows d.1 d.property).localCase.tokens v +
            (Q.rows a.1 a.property).localCase.tokens v +
            (Q.rows b.1 b.property).localCase.tokens v +
            (Q.rows c.1 c.property).localCase.tokens v =
          (Q.rows a.1 a.property).localCase.tokens v +
            (Q.rows b.1 b.property).localCase.tokens v +
            (Q.rows c.1 c.property).localCase.tokens v +
            (Q.rows d.1 d.property).localCase.tokens v := by omega
    rw [hsum] at hfit
    exact hfit
  have hsDirect := direct_of_not_exceptional hs2 hs4
  have htDirect := direct_of_not_exceptional ht2 ht4
  have huDirect := direct_of_not_exceptional hu2 hu4
  rcases three_associations_have_equal_pair
      S.descriptor.association T.descriptor.association
      U.descriptor.association with hST | hSU | hTU
  · exact (hab (direct_direct S T hsDirect htDirect hbWindow hST)).elim
  · exact (hac (direct_direct S U hsDirect huDirect hcWindow hSU)).elim
  · exact (hbc (direct_direct T U htDirect huDirect
      (locality.competing_source_in_window hb hc) hTU)).elim

/-- Three distinct arrivals carrying one formula-derived association are
impossible.  This is the exact no-five primitive: the exceptional roles are
handled by their retained geometric records, while the direct branch uses
the checked direct/direct theorem. -/
theorem same_association_no_three
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
    (K : WeightedRoleCollisionResiduals Q)
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
  by_cases hs2 : S.target.role = .case2Secondary
  · exact K.case2_same_association_triple S T U hs2 htAssoc huAssoc
      htWindow huWindow hst hsu htu
  by_cases ht2 : T.target.role = .case2Secondary
  · exact K.case2_same_association_triple T S U ht2 htAssoc.symm
      (huAssoc.trans htAssoc.symm)
      (locality.competing_source_in_window htPos hsPos)
      (locality.competing_source_in_window htPos huPos)
      hst.symm htu hsu
  by_cases hu2 : U.target.role = .case2Secondary
  · exact K.case2_same_association_triple U S T hu2 huAssoc.symm
      (htAssoc.trans huAssoc.symm)
      (locality.competing_source_in_window huPos hsPos)
      (locality.competing_source_in_window huPos htPos)
      hsu.symm htu.symm hst
  by_cases hs4 : S.target.role = .case4SplitRight
  · by_cases ht4 : T.target.role = .case4SplitRight
    · by_cases hu4 : U.target.role = .case4SplitRight
      · exact K.case4_weighted.three_split_right_same_association
          S T U hs4 ht4 hu4 htAssoc huAssoc htWindow huWindow hst hsu htu
      · exact K.case4_weighted.two_split_right_one_direct_same_association
          S T U hs4 ht4 (direct_of_not_exceptional hu2 hu4)
          htAssoc huAssoc htWindow huWindow hst hsu htu
    · by_cases hu4 : U.target.role = .case4SplitRight
      · exact K.case4_weighted.two_split_right_one_direct_same_association
          S U T hs4 hu4 (direct_of_not_exceptional ht2 ht4)
          huAssoc htAssoc huWindow htWindow hsu hst htu.symm
      · exact Erdos957Case4CollisionLeaves.no_two_direct_competitors_of_split_right
          Q S.target T.target U.target hs4 ht2 ht4 hu2 hu4
            htWindow huWindow hst hsu htu
  by_cases ht4 : T.target.role = .case4SplitRight
  · by_cases hu4 : U.target.role = .case4SplitRight
    · exact K.case4_weighted.two_split_right_one_direct_same_association
        T U S ht4 hu4 (direct_of_not_exceptional hs2 hs4)
        (huAssoc.trans htAssoc.symm) htAssoc.symm
        (locality.competing_source_in_window htPos huPos)
        (locality.competing_source_in_window htPos hsPos)
        htu hst.symm hsu.symm
    · exact Erdos957Case4CollisionLeaves.no_two_direct_competitors_of_split_right
        Q T.target S.target U.target ht4 hs2 hs4 hu2 hu4
          (locality.competing_source_in_window htPos hsPos)
          (locality.competing_source_in_window htPos huPos)
          hst.symm htu hsu
  by_cases hu4 : U.target.role = .case4SplitRight
  · exact Erdos957Case4CollisionLeaves.no_two_direct_competitors_of_split_right
      Q U.target S.target T.target hu4 hs2 hs4 ht2 ht4
        (locality.competing_source_in_window huPos hsPos)
        (locality.competing_source_in_window huPos htPos)
        hsu.symm htu.symm hst
  exact hst (direct_direct S T (direct_of_not_exceptional hs2 hs4)
    (direct_of_not_exceptional ht2 ht4) htWindow htAssoc.symm)

/-- The no-five consequence of `same_association_no_three`.  The positive
source fiber is partitioned by the two formula-derived associations; each
part has cardinality at most two. -/
theorem contributors_card_le_four
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
    (K : WeightedRoleCollisionResiduals Q) (v : Vertex A) :
    (Finset.univ.filter fun s : Source P W ↦
      0 < sourceTokens P W F.chart
        (localCasesOfRealizedRows (F := F) Q.rows) s v).card ≤ 4 := by
  let incoming : Finset (Source P W) := Finset.univ.filter fun s ↦
    0 < sourceTokens P W F.chart
      (localCasesOfRealizedRows (F := F) Q.rows) s v
  let left : Finset (Source P W) := incoming.filter fun s ↦
    realizedArrivalSide (F := F) Q.rows s v = false
  let right : Finset (Source P W) := incoming.filter fun s ↦
    realizedArrivalSide (F := F) Q.rows s v = true
  have side_card_le_two : ∀ side : Bool,
      (incoming.filter fun s ↦
        realizedArrivalSide (F := F) Q.rows s v = side).card ≤ 2 := by
    intro side
    apply Nat.le_of_not_gt
    intro hcard
    have hcard' : 2 < (incoming.filter fun s ↦
        realizedArrivalSide (F := F) Q.rows s v = side).card := hcard
    rw [Finset.two_lt_card] at hcard'
    rcases hcard' with
      ⟨s, hs, t, ht, u, hu, hst, hsu, htu⟩
    have hsIn : s ∈ incoming := (Finset.mem_filter.mp hs).1
    have htIn : t ∈ incoming := (Finset.mem_filter.mp ht).1
    have huIn : u ∈ incoming := (Finset.mem_filter.mp hu).1
    have hsSide := (Finset.mem_filter.mp hs).2
    have htSide := (Finset.mem_filter.mp ht).2
    have huSide := (Finset.mem_filter.mp hu).2
    have hsPos : 0 < sourceTokens P W F.chart
        (localCasesOfRealizedRows (F := F) Q.rows) s v := by
      simpa [incoming] using hsIn
    have htPos : 0 < sourceTokens P W F.chart
        (localCasesOfRealizedRows (F := F) Q.rows) t v := by
      simpa [incoming] using htIn
    have huPos : 0 < sourceTokens P W F.chart
        (localCasesOfRealizedRows (F := F) Q.rows) u v := by
      simpa [incoming] using huIn
    have hsRow : 0 < (Q.rows s.1 s.property).localCase.tokens v := by
      simpa [sourceTokens, selectedCase, localCasesOfRealizedRows] using hsPos
    have htRow : 0 < (Q.rows t.1 t.property).localCase.tokens v := by
      simpa [sourceTokens, selectedCase, localCasesOfRealizedRows] using htPos
    have huRow : 0 < (Q.rows u.1 u.property).localCase.tokens v := by
      simpa [sourceTokens, selectedCase, localCasesOfRealizedRows] using huPos
    let S := realizedArrivalAtOfPositive (F := F) Q.rows s v hsRow
    let T := realizedArrivalAtOfPositive (F := F) Q.rows t v htRow
    let U := realizedArrivalAtOfPositive (F := F) Q.rows u v huRow
    have hsBool : arrivalAssociationBool S.descriptor.association = side := by
      rw [realizedArrivalSide_of_positive (F := F) Q.rows s v hsRow] at hsSide
      simpa [S] using hsSide
    have htBool : arrivalAssociationBool T.descriptor.association = side := by
      rw [realizedArrivalSide_of_positive (F := F) Q.rows t v htRow] at htSide
      simpa [T] using htSide
    have huBool : arrivalAssociationBool U.descriptor.association = side := by
      rw [realizedArrivalSide_of_positive (F := F) Q.rows u v huRow] at huSide
      simpa [U] using huSide
    have htAssoc : T.descriptor.association = S.descriptor.association :=
      arrivalAssociationBool_injective (htBool.trans hsBool.symm)
    have huAssoc : U.descriptor.association = S.descriptor.association :=
      arrivalAssociationBool_injective (huBool.trans hsBool.symm)
    exact same_association_no_three Q locality direct_direct K S T U
      htAssoc huAssoc
      (locality.competing_source_in_window hsPos htPos)
      (locality.competing_source_in_window hsPos huPos)
      hst hsu htu
  have hleft : left.card ≤ 2 := by
    simpa [left] using side_card_le_two false
  have hright : right.card ≤ 2 := by
    simpa [right] using side_card_le_two true
  have hcover : incoming ⊆ left ∪ right := by
    intro s hs
    have hcases : realizedArrivalSide (F := F) Q.rows s v = false ∨
        realizedArrivalSide (F := F) Q.rows s v = true := by
      cases realizedArrivalSide (F := F) Q.rows s v <;> simp
    rcases hcases with hfalse | htrue
    · exact Finset.mem_union_left right (Finset.mem_filter.mpr ⟨hs, hfalse⟩)
    · exact Finset.mem_union_right left (Finset.mem_filter.mpr ⟨hs, htrue⟩)
  change incoming.card ≤ 4
  calc
    incoming.card ≤ (left ∪ right).card := Finset.card_le_card hcover
    _ ≤ left.card + right.card := Finset.card_union_le left right
    _ ≤ 4 := by omega

/-- Final weight-aware collision record assembled from the role dispatcher. -/
noncomputable def weightedCollisionWitnesses
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
    (K : WeightedRoleCollisionResiduals Q) :
    WeightedCollisionWitnesses P W F
      (localCasesOfRealizedRows (F := F) Q.rows) where
  locality := locality
  contributors_card_le_four := contributors_card_le_four Q locality direct_direct K
  triple_fits_in_window := triple_fits hA Q locality direct_direct K
  quadruple_fits_in_window := quadruple_fits Q locality direct_direct K

/-- Produced-hull specialization.  After the genuine row selector, cyclic
window, and direct/direct theorem are fixed, the only remaining input is the
small role-geometric residual record above. -/
noncomputable def producedWeightedCollisionWitnesses
    {A : Finset Point} (hA : IsOneSeparated A)
    (R : Erdos957.RadiallySortedCyclicHullOrder A)
    (L : Erdos957TurnSum.HullOrderBridge.LiftedCyclicHullOrder R.order)
    (W : DiameterWitnessData (Erdos957DirectSameSide.ProducedHull R L))
    (K : WeightedRoleCollisionResiduals
      (P := Erdos957DirectSameSide.ProducedHull R L) (W := W)
      (F := Erdos957DirectSameSide.ProducedFrame hA R L)
      (Erdos957CoherentRealizedRows.producedCommonCoherentRealizedSourceRows
        hA R L W)) :
    WeightedCollisionWitnesses
      (Erdos957DirectSameSide.ProducedHull R L) W
      (Erdos957DirectSameSide.ProducedFrame hA R L)
      (localCasesOfRealizedRows (F :=
        Erdos957DirectSameSide.ProducedFrame hA R L)
        (Erdos957DirectSameSide.ProducedRows hA R L W)) :=
  weightedCollisionWitnesses hA
    (Erdos957CoherentRealizedRows.producedCommonCoherentRealizedSourceRows
      hA R L W)
    ⟨Erdos957GeometryTransfer.producedCyclicWindowGeometry hA R L W⟩
    (Erdos957DirectSameSide.produced_direct_direct hA R L W) K

end Erdos957WeightedRoleCollisions

#print axioms Erdos957WeightedRoleCollisions.triple_fits
#print axioms Erdos957WeightedRoleCollisions.quadruple_fits
#print axioms Erdos957WeightedRoleCollisions.same_association_no_three
#print axioms Erdos957WeightedRoleCollisions.contributors_card_le_four
#print axioms Erdos957WeightedRoleCollisions.weightedCollisionWitnesses
#print axioms Erdos957WeightedRoleCollisions.producedWeightedCollisionWitnesses
