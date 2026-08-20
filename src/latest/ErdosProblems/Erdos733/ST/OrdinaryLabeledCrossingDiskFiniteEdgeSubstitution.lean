import ErdosProblems.Erdos733.ST.OrdinaryCrossingLocalBranchSubstitutionDisjointDiskStability
import ErdosProblems.Erdos733.ST.OrdinaryLabeledCrossingDiskFillingFamily
import Mathlib.Tactic

open Classical
noncomputable section


-- [TABLET NODE: OrdinaryLabeledCrossingDiskFiniteEdgeSubstitution]
lemma OrdinaryLabeledCrossingDiskFiniteEdgeSubstitution {V : Type*} [Fintype V]
    (G : SimpleGraph V) [Fintype G.edgeSet]
    (D : OrdinaryPolygonalDrawing G)
    (F : OrdinaryLabeledCrossingDiskFamily G D)
    (L : OrdinaryLabeledCrossingDiskFillingFamily G D F)
    (e : G.edgeFinset) :
    let owned := Finset.univ.filter (fun x : {p // p ∈ D.crossingSet} =>
      (F.disk x).firstEdge = e ∨ (F.disk x).secondEdge = e)
    let side := fun x : {p // p ∈ D.crossingSet} =>
      if (F.disk x).firstEdge = e then (0 : Fin 2) else (1 : Fin 2)
    let openBalls := fun S : Finset {p // p ∈ D.crossingSet} =>
      ⋃ x ∈ (S : Set {p // p ∈ D.crossingSet}),
        Metric.ball x.1 (F.disk x).radius
    let closedBalls := fun S : Finset {p // p ∈ D.crossingSet} =>
      ⋃ x ∈ (S : Set {p // p ∈ D.crossingSet}),
        Metric.closedBall x.1 (F.disk x).radius
    let fillingCarrier := fun S : Finset {p // p ∈ D.crossingSet} =>
      ⋃ x ∈ (S : Set {p // p ∈ D.crossingSet}),
        (L.fillingArc x (side x)).carrier
    ∃ Q : PolygonalArc,
      Q.source = (D.edgeArc e).source ∧
        Q.target = (D.edgeArc e).target ∧
          Q.carrier =
            ((D.edgeArc e).carrier \ openBalls owned) ∪ fillingCarrier owned ∧
          Q.carrier \ openBalls owned =
            (D.edgeArc e).carrier \ openBalls owned ∧
          (∀ x ∈ owned,
            Metric.closedBall x.1 (F.disk x).radius ∩ Q.carrier =
              (L.fillingArc x (side x)).carrier) ∧
          (∀ z i (hi : i + 1 < (D.edgeArc e).vertices.length),
            z ∈ openSegment ℝ (D.edgeArc e).vertices[i]
                (D.edgeArc e).vertices[i + 1] →
              z ∉ closedBalls owned →
                ∃ j : ℕ, ∃ hj : j + 1 < Q.vertices.length,
                  z ∈ openSegment ℝ Q.vertices[j] Q.vertices[j + 1] ∧
                    ∃ c : ℝ, c ≠ 0 ∧
                      Q.vertices[j + 1] - Q.vertices[j] =
                        c • ((D.edgeArc e).vertices[i + 1] -
                          (D.edgeArc e).vertices[i])) ∧
          ∀ x ∈ owned, ∀ z m
              (hm : m + 1 < (L.fillingArc x (side x)).vertices.length),
            z ∈ openSegment ℝ (L.fillingArc x (side x)).vertices[m]
                (L.fillingArc x (side x)).vertices[m + 1] →
              ∃ j : ℕ, ∃ hj : j + 1 < Q.vertices.length,
                z ∈ openSegment ℝ Q.vertices[j] Q.vertices[j + 1] ∧
                  ∃ c : ℝ, c ≠ 0 ∧
                    Q.vertices[j + 1] - Q.vertices[j] =
                      c • ((L.fillingArc x (side x)).vertices[m + 1] -
                      (L.fillingArc x (side x)).vertices[m]) := by
-- BODY
  classical
  let owned := Finset.univ.filter (fun x : {p // p ∈ D.crossingSet} =>
    (F.disk x).firstEdge = e ∨ (F.disk x).secondEdge = e)
  let side := fun x : {p // p ∈ D.crossingSet} =>
    if (F.disk x).firstEdge = e then (0 : Fin 2) else (1 : Fin 2)
  let openBalls := fun S : Finset {p // p ∈ D.crossingSet} =>
    ⋃ x ∈ (S : Set {p // p ∈ D.crossingSet}),
      Metric.ball x.1 (F.disk x).radius
  let closedBalls := fun S : Finset {p // p ∈ D.crossingSet} =>
    ⋃ x ∈ (S : Set {p // p ∈ D.crossingSet}),
      Metric.closedBall x.1 (F.disk x).radius
  let fillingCarrier := fun S : Finset {p // p ∈ D.crossingSet} =>
    ⋃ x ∈ (S : Set {p // p ∈ D.crossingSet}),
      (L.fillingArc x (side x)).carrier
  change ∃ Q : PolygonalArc,
    Q.source = (D.edgeArc e).source ∧
      Q.target = (D.edgeArc e).target ∧
        Q.carrier =
          ((D.edgeArc e).carrier \ openBalls owned) ∪ fillingCarrier owned ∧
        Q.carrier \ openBalls owned =
          (D.edgeArc e).carrier \ openBalls owned ∧
        (∀ x ∈ owned,
          Metric.closedBall x.1 (F.disk x).radius ∩ Q.carrier =
            (L.fillingArc x (side x)).carrier) ∧
        (∀ z i (hi : i + 1 < (D.edgeArc e).vertices.length),
          z ∈ openSegment ℝ (D.edgeArc e).vertices[i]
              (D.edgeArc e).vertices[i + 1] →
            z ∉ closedBalls owned →
              ∃ j : ℕ, ∃ hj : j + 1 < Q.vertices.length,
                z ∈ openSegment ℝ Q.vertices[j] Q.vertices[j + 1] ∧
                  ∃ c : ℝ, c ≠ 0 ∧
                    Q.vertices[j + 1] - Q.vertices[j] =
                      c • ((D.edgeArc e).vertices[i + 1] -
                        (D.edgeArc e).vertices[i])) ∧
        ∀ x ∈ owned, ∀ z m
            (hm : m + 1 < (L.fillingArc x (side x)).vertices.length),
          z ∈ openSegment ℝ (L.fillingArc x (side x)).vertices[m]
              (L.fillingArc x (side x)).vertices[m + 1] →
            ∃ j : ℕ, ∃ hj : j + 1 < Q.vertices.length,
              z ∈ openSegment ℝ Q.vertices[j] Q.vertices[j + 1] ∧
                ∃ c : ℝ, c ≠ 0 ∧
                  Q.vertices[j + 1] - Q.vertices[j] =
                    c • ((L.fillingArc x (side x)).vertices[m + 1] -
                      (L.fillingArc x (side x)).vertices[m])
  have source_mem_carrier : ∀ R : PolygonalArc, R.source ∈ R.carrier := by
    intro R
    have hlen := R.length_ge_two
    rw [R.carrier_eq]
    refine ⟨0, by omega, ?_⟩
    have hzero : R.vertices[0] = R.source := by
      rw [← Option.some_inj, ← R.source_eq_head, List.head?_eq_getElem?,
        List.getElem?_eq_getElem (by omega)]
    rw [hzero]
    exact left_mem_segment ℝ _ _
  have target_mem_carrier : ∀ R : PolygonalArc, R.target ∈ R.carrier := by
    intro R
    rw [R.carrier_eq]
    let m := R.vertices.length - 2
    have hm : m + 1 < R.vertices.length := by
      have := R.length_ge_two
      dsimp only [m]
      omega
    refine ⟨m, hm, ?_⟩
    have hlast : R.vertices[m + 1] = R.target := by
      rw [← Option.some_inj, ← R.target_eq_last, List.getLast?_eq_getElem?,
        List.getElem?_eq_getElem (by omega)]
      congr 2
      dsimp only [m]
      omega
    rw [hlast]
    exact right_mem_segment ℝ _ _
  have initialBranch : ∀ x ∈ owned,
      ∃ branch : OrdinaryCrossingLocalBranchData (D.edgeArc e) x.1
          (F.disk x).radius,
        branch.beforeGate = (L.fillingArc x (side x)).source ∧
          branch.afterGate = (L.fillingArc x (side x)).target := by
    intro x hx
    have howner : (F.disk x).firstEdge = e ∨ (F.disk x).secondEdge = e :=
      (Finset.mem_filter.mp hx).2
    by_cases hfirst : (F.disk x).firstEdge = e
    · have hsecond : (F.disk x).secondEdge ≠ e := by
        intro hsecond
        exact (F.disk x).edges_ne (hfirst.trans hsecond.symm)
      subst e
      refine ⟨(F.disk x).firstBranch, ?_, ?_⟩
      · simpa only [side, if_pos rfl] using (L.source_zero x).symm
      · simpa only [side, if_pos rfl] using (L.target_zero x).symm
    · have hsecond : (F.disk x).secondEdge = e := howner.resolve_left hfirst
      subst e
      refine ⟨(F.disk x).secondBranch, ?_, ?_⟩
      · simpa only [side, if_neg hfirst] using (L.source_one x).symm
      · simpa only [side, if_neg hfirst] using (L.target_one x).symm
  have inductionState : ∀ S : Finset {p // p ∈ D.crossingSet}, S ⊆ owned →
      ∃ Q : PolygonalArc,
        Q.source = (D.edgeArc e).source ∧
          Q.target = (D.edgeArc e).target ∧
          Q.carrier =
            ((D.edgeArc e).carrier \ openBalls S) ∪ fillingCarrier S ∧
          Q.carrier \ openBalls S =
            (D.edgeArc e).carrier \ openBalls S ∧
          (∀ x ∈ S,
            Metric.closedBall x.1 (F.disk x).radius ∩ Q.carrier =
              (L.fillingArc x (side x)).carrier) ∧
          (∀ z i (hi : i + 1 < (D.edgeArc e).vertices.length),
            z ∈ openSegment ℝ (D.edgeArc e).vertices[i]
                (D.edgeArc e).vertices[i + 1] →
              z ∉ closedBalls S →
                ∃ j : ℕ, ∃ hj : j + 1 < Q.vertices.length,
                  z ∈ openSegment ℝ Q.vertices[j] Q.vertices[j + 1] ∧
                    ∃ c : ℝ, c ≠ 0 ∧
                      Q.vertices[j + 1] - Q.vertices[j] =
                        c • ((D.edgeArc e).vertices[i + 1] -
                          (D.edgeArc e).vertices[i])) ∧
          (∀ x ∈ S, ∀ z m
              (hm : m + 1 < (L.fillingArc x (side x)).vertices.length),
            z ∈ openSegment ℝ (L.fillingArc x (side x)).vertices[m]
                (L.fillingArc x (side x)).vertices[m + 1] →
              ∃ j : ℕ, ∃ hj : j + 1 < Q.vertices.length,
                z ∈ openSegment ℝ Q.vertices[j] Q.vertices[j + 1] ∧
                  ∃ c : ℝ, c ≠ 0 ∧
                    Q.vertices[j + 1] - Q.vertices[j] =
                      c • ((L.fillingArc x (side x)).vertices[m + 1] -
                        (L.fillingArc x (side x)).vertices[m])) ∧
          ∀ x ∈ owned, x ∉ S →
            ∃ branch : OrdinaryCrossingLocalBranchData Q x.1
                (F.disk x).radius,
              branch.beforeGate = (L.fillingArc x (side x)).source ∧
                branch.afterGate = (L.fillingArc x (side x)).target := by
    intro S
    induction S using Finset.induction_on with
    | empty =>
        intro _hsub
        refine ⟨D.edgeArc e, rfl, rfl, ?_, ?_, ?_, ?_, ?_, ?_⟩
        · simp [openBalls, fillingCarrier]
        · simp [openBalls]
        · simp
        · intro z i hi hz _hzOutside
          exact ⟨i, hi, hz, 1, one_ne_zero, by simp⟩
        · simp
        · intro x hx _hxempty
          exact initialBranch x hx
    | @insert x S hxS ih =>
        intro hsub
        have hxOwned : x ∈ owned := hsub (Finset.mem_insert_self x S)
        have hSsub : S ⊆ owned := by
          intro y hy
          exact hsub (Finset.mem_insert_of_mem hy)
        rcases ih hSsub with
          ⟨Q, hQsource, hQtarget, hQcarrier, hQoutside, hQlocal,
            hQoriginal, hQfilling, hQbranch⟩
        rcases hQbranch x hxOwned hxS with
          ⟨branch, hbranchSource, hbranchTarget⟩
        have hsourceOutside : Q.source ∉
            Metric.closedBall x.1 (F.disk x).radius := by
          rw [hQsource]
          rcases D.edgeArc_endpoints e with ⟨u, v, _huv, _he, hend⟩
          rcases hend with hend | hend
          · rw [hend.1]
            exact (F.disk x).no_vertex_in_closedBall u
          · rw [hend.1]
            exact (F.disk x).no_vertex_in_closedBall v
        have htargetOutside : Q.target ∉
            Metric.closedBall x.1 (F.disk x).radius := by
          rw [hQtarget]
          rcases D.edgeArc_endpoints e with ⟨u, v, _huv, _he, hend⟩
          rcases hend with hend | hend
          · rw [hend.2]
            exact (F.disk x).no_vertex_in_closedBall v
          · rw [hend.2]
            exact (F.disk x).no_vertex_in_closedBall u
        let Remaining := {y : {p // p ∈ D.crossingSet} //
          y ∈ owned ∧ y ∉ insert x S}
        have remainingBranchExists : ∀ y : Remaining,
            ∃ other : OrdinaryCrossingLocalBranchData Q y.1.1
                (F.disk y.1).radius,
              other.beforeGate = (L.fillingArc y.1 (side y.1)).source ∧
                other.afterGate = (L.fillingArc y.1 (side y.1)).target := by
          intro y
          exact hQbranch y.1 y.2.1 (fun hyS =>
            y.2.2 (Finset.mem_insert_of_mem hyS))
        let otherBranch : ∀ y : Remaining,
            OrdinaryCrossingLocalBranchData Q y.1.1
              (F.disk y.1).radius := fun y =>
          Classical.choose (remainingBranchExists y)
        have otherBranchSpec : ∀ y : Remaining,
            (otherBranch y).beforeGate =
                (L.fillingArc y.1 (side y.1)).source ∧
              (otherBranch y).afterGate =
                (L.fillingArc y.1 (side y.1)).target := by
          intro y
          exact Classical.choose_spec (remainingBranchExists y)
        have hdisjoint : ∀ y : Remaining,
            Disjoint (Metric.closedBall x.1 (F.disk x).radius)
              (Metric.closedBall y.1.1 (F.disk y.1).radius) := by
          intro y
          apply F.closedBalls_pairwise_disjoint
          intro hxy
          exact y.2.2 (by
            rw [← hxy]
            exact Finset.mem_insert_self x S)
        rcases OrdinaryCrossingLocalBranchSubstitutionDisjointDiskStability
            Q (L.fillingArc x (side x)) x.1 (F.disk x).radius branch
            (fun y : Remaining => y.1.1)
            (fun y : Remaining => (F.disk y.1).radius) otherBranch
            hsourceOutside htargetOutside hbranchSource.symm
            hbranchTarget.symm (L.carrier_subset_closedBall x (side x))
            (L.relativeInterior_subset_ball x (side x)) hdisjoint with
          ⟨Q', hQ'source, hQ'target, hcarrierOne, houtsideOne, _hinsideOne,
            _hbridgeInterior, hbridgeTransfer, holdTransfer, hremaining⟩
        have hopenInsert : openBalls (insert x S) =
            Metric.ball x.1 (F.disk x).radius ∪ openBalls S := by
          simp only [openBalls, Finset.coe_insert, Set.biUnion_insert]
        have hclosedInsert : closedBalls (insert x S) =
            Metric.closedBall x.1 (F.disk x).radius ∪ closedBalls S := by
          simp only [closedBalls, Finset.coe_insert, Set.biUnion_insert]
        have hfillInsert : fillingCarrier (insert x S) =
            (L.fillingArc x (side x)).carrier ∪ fillingCarrier S := by
          simp only [fillingCarrier, Finset.coe_insert, Set.biUnion_insert]
        have hfillSOutsideClosed : ∀ z, z ∈ fillingCarrier S →
            z ∉ Metric.closedBall x.1 (F.disk x).radius := by
          intro z hzFill hzX
          change z ∈ ⋃ y ∈ (S : Set {p // p ∈ D.crossingSet}),
            (L.fillingArc y (side y)).carrier at hzFill
          rcases Set.mem_iUnion.mp hzFill with ⟨y, hzFill⟩
          rcases Set.mem_iUnion.mp hzFill with ⟨hyS, hzFill⟩
          have hxy : x ≠ y := by
            intro hxy
            subst y
            exact hxS hyS
          exact (Set.disjoint_left.mp (F.closedBalls_pairwise_disjoint hxy)
            hzX) (L.carrier_subset_closedBall y (side y) hzFill)
        have hcarrierNext : Q'.carrier =
            ((D.edgeArc e).carrier \ openBalls (insert x S)) ∪
              fillingCarrier (insert x S) := by
          rw [hcarrierOne, hQcarrier, hopenInsert, hfillInsert]
          ext z
          simp only [Set.mem_union, Set.mem_diff]
          have hfillOutside : z ∈ fillingCarrier S →
              z ∉ Metric.ball x.1 (F.disk x).radius := fun hzFill hzBall =>
            hfillSOutsideClosed z hzFill (Metric.ball_subset_closedBall hzBall)
          tauto
        have houtsideNext : Q'.carrier \ openBalls (insert x S) =
            (D.edgeArc e).carrier \ openBalls (insert x S) := by
          ext z
          rw [hopenInsert]
          simp only [Set.mem_diff, Set.mem_union]
          have hone := Set.ext_iff.mp houtsideOne z
          have hprev := Set.ext_iff.mp hQoutside z
          constructor
          · rintro ⟨hzQ', hzNo⟩
            have hzNoBall : z ∉ Metric.ball x.1 (F.disk x).radius :=
              fun hz => hzNo (Or.inl hz)
            have hzNoOld : z ∉ openBalls S :=
              fun hz => hzNo (Or.inr hz)
            have hzQ : z ∈ Q.carrier :=
              (hone.mp ⟨hzQ', hzNoBall⟩).1
            have hzOrig : z ∈ (D.edgeArc e).carrier :=
              (hprev.mp ⟨hzQ, hzNoOld⟩).1
            exact ⟨hzOrig, hzNo⟩
          · rintro ⟨hzOrig, hzNo⟩
            have hzNoBall : z ∉ Metric.ball x.1 (F.disk x).radius :=
              fun hz => hzNo (Or.inl hz)
            have hzNoOld : z ∉ openBalls S :=
              fun hz => hzNo (Or.inr hz)
            have hzQ : z ∈ Q.carrier :=
              (hprev.mpr ⟨hzOrig, hzNoOld⟩).1
            have hzQ' : z ∈ Q'.carrier :=
              (hone.mpr ⟨hzQ, hzNoBall⟩).1
            exact ⟨hzQ', hzNo⟩
        have hlocalCurrent :
            Metric.closedBall x.1 (F.disk x).radius ∩ Q'.carrier =
              (L.fillingArc x (side x)).carrier := by
          apply Set.Subset.antisymm
          · rintro z ⟨hzClosed, hzQ'⟩
            rw [hcarrierOne] at hzQ'
            rcases hzQ' with hzOld | hzFill
            · have hzSphere : z ∈ Metric.sphere x.1 (F.disk x).radius := by
                rw [Metric.mem_sphere]
                apply le_antisymm (Metric.mem_closedBall.mp hzClosed)
                exact le_of_not_gt (fun hlt => hzOld.2 (Metric.mem_ball.mpr hlt))
              have hzGates : z = branch.beforeGate ∨ z = branch.afterGate := by
                have hzBoth : z ∈ Metric.sphere x.1 (F.disk x).radius ∩
                    Q.carrier := ⟨hzSphere, hzOld.1⟩
                rw [branch.sphere_carrier_eq] at hzBoth
                simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using hzBoth
              rcases hzGates with hzBefore | hzAfter
              · rw [hzBefore, hbranchSource]
                exact source_mem_carrier (L.fillingArc x (side x))
              · rw [hzAfter, hbranchTarget]
                exact target_mem_carrier (L.fillingArc x (side x))
            · exact hzFill
          · intro z hzFill
            refine ⟨L.carrier_subset_closedBall x (side x) hzFill, ?_⟩
            rw [hcarrierOne]
            exact Or.inr hzFill
        have hlocalNext : ∀ y ∈ insert x S,
            Metric.closedBall y.1 (F.disk y).radius ∩ Q'.carrier =
              (L.fillingArc y (side y)).carrier := by
          intro y hy
          rcases Finset.mem_insert.mp hy with hyx | hyS
          · subst y
            exact hlocalCurrent
          · have hxy : x ≠ y := by
              intro hxy
              subst y
              exact hxS hyS
            have hlocalPreserved :
                Metric.closedBall y.1 (F.disk y).radius ∩ Q'.carrier =
                  Metric.closedBall y.1 (F.disk y).radius ∩ Q.carrier := by
              apply Set.Subset.antisymm
              · rintro z ⟨hzY, hzQ'⟩
                rw [hcarrierOne] at hzQ'
                rcases hzQ' with hzOld | hzFill
                · exact ⟨hzY, hzOld.1⟩
                · exact False.elim ((Set.disjoint_left.mp
                    (F.closedBalls_pairwise_disjoint hxy)
                    (L.carrier_subset_closedBall x (side x) hzFill)) hzY)
              · rintro z ⟨hzY, hzQ⟩
                refine ⟨hzY, ?_⟩
                rw [hcarrierOne]
                apply Or.inl
                refine ⟨hzQ, ?_⟩
                intro hzBall
                exact (Set.disjoint_left.mp
                  (F.closedBalls_pairwise_disjoint hxy)
                  (Metric.ball_subset_closedBall hzBall)) hzY
            exact hlocalPreserved.trans (hQlocal y hyS)
        have horiginalNext :
            ∀ z i (hi : i + 1 < (D.edgeArc e).vertices.length),
              z ∈ openSegment ℝ (D.edgeArc e).vertices[i]
                  (D.edgeArc e).vertices[i + 1] →
                z ∉ closedBalls (insert x S) →
                  ∃ j : ℕ, ∃ hj : j + 1 < Q'.vertices.length,
                    z ∈ openSegment ℝ Q'.vertices[j] Q'.vertices[j + 1] ∧
                      ∃ c : ℝ, c ≠ 0 ∧
                        Q'.vertices[j + 1] - Q'.vertices[j] =
                          c • ((D.edgeArc e).vertices[i + 1] -
                            (D.edgeArc e).vertices[i]) := by
          intro z i hi hzOpen hzOutside
          have hzOutsideX : z ∉ Metric.closedBall x.1 (F.disk x).radius := by
            intro hzX
            apply hzOutside
            rw [hclosedInsert]
            exact Or.inl hzX
          have hzOutsideS : z ∉ closedBalls S := by
            intro hzS
            apply hzOutside
            rw [hclosedInsert]
            exact Or.inr hzS
          rcases hQoriginal z i hi hzOpen hzOutsideS with
            ⟨j, hj, hzQ, c₁, hc₁, hdir₁⟩
          rcases holdTransfer z j hj hzQ hzOutsideX with
            ⟨k, hk, hzQ', c₂, hc₂, hdir₂⟩
          refine ⟨k, hk, hzQ', c₂ * c₁, mul_ne_zero hc₂ hc₁, ?_⟩
          rw [hdir₂, hdir₁, smul_smul]
        have hfillingNext : ∀ y ∈ insert x S, ∀ z m
            (hm : m + 1 < (L.fillingArc y (side y)).vertices.length),
          z ∈ openSegment ℝ (L.fillingArc y (side y)).vertices[m]
              (L.fillingArc y (side y)).vertices[m + 1] →
            ∃ j : ℕ, ∃ hj : j + 1 < Q'.vertices.length,
              z ∈ openSegment ℝ Q'.vertices[j] Q'.vertices[j + 1] ∧
                ∃ c : ℝ, c ≠ 0 ∧
                  Q'.vertices[j + 1] - Q'.vertices[j] =
                    c • ((L.fillingArc y (side y)).vertices[m + 1] -
                      (L.fillingArc y (side y)).vertices[m]) := by
          intro y hy z m hm hzOpen
          rcases Finset.mem_insert.mp hy with hyx | hyS
          · subst y
            exact hbridgeTransfer z m hm hzOpen
          · have hxy : x ≠ y := by
              intro hxy
              subst y
              exact hxS hyS
            have hzCarrier : z ∈ (L.fillingArc y (side y)).carrier := by
              rw [(L.fillingArc y (side y)).carrier_eq]
              exact ⟨m, hm, openSegment_subset_segment ℝ _ _ hzOpen⟩
            have hzOutsideX : z ∉
                Metric.closedBall x.1 (F.disk x).radius := by
              intro hzX
              exact (Set.disjoint_left.mp
                (F.closedBalls_pairwise_disjoint hxy) hzX)
                (L.carrier_subset_closedBall y (side y) hzCarrier)
            rcases hQfilling y hyS z m hm hzOpen with
              ⟨j, hj, hzQ, c₁, hc₁, hdir₁⟩
            rcases holdTransfer z j hj hzQ hzOutsideX with
              ⟨k, hk, hzQ', c₂, hc₂, hdir₂⟩
            refine ⟨k, hk, hzQ', c₂ * c₁, mul_ne_zero hc₂ hc₁, ?_⟩
            rw [hdir₂, hdir₁, smul_smul]
        have hbranchNext : ∀ y ∈ owned, y ∉ insert x S →
            ∃ nextBranch : OrdinaryCrossingLocalBranchData Q' y.1
                (F.disk y).radius,
              nextBranch.beforeGate = (L.fillingArc y (side y)).source ∧
                nextBranch.afterGate = (L.fillingArc y (side y)).target := by
          intro y hyOwned hyRemaining
          let a : Remaining := ⟨y, hyOwned, hyRemaining⟩
          rcases hremaining a with
            ⟨_hclosed, _hsphere, _hbeforeLift, _hafterLift,
              nextBranch, hbefore, hafter⟩
          have hspec := otherBranchSpec a
          exact ⟨nextBranch, hbefore.trans hspec.1, hafter.trans hspec.2⟩
        exact ⟨Q', hQ'source.trans hQsource, hQ'target.trans hQtarget,
          hcarrierNext, houtsideNext, hlocalNext, horiginalNext,
          hfillingNext, hbranchNext⟩
  rcases inductionState owned (fun _ h => h) with
    ⟨Q, hsource, htarget, hcarrier, houtside, hlocal, horiginal,
      hfilling, _hbranches⟩
  exact ⟨Q, hsource, htarget, hcarrier, houtside, hlocal, horiginal, hfilling⟩
