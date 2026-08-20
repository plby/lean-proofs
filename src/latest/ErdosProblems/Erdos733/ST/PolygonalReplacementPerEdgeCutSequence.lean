import ErdosProblems.Erdos733.ST.PolygonalReplacementIntersectionDiskCutOrder

open Classical
noncomputable section

universe u

-- [TABLET NODE: PolygonalReplacementPerEdgeCutSequence]
lemma PolygonalReplacementPerEdgeCutSequence {V : Type u} [Fintype V]
    (G : SimpleGraph V) [Fintype G.edgeSet] (D : GeometricArcDrawing G)
    (controlDisks : PolygonalReplacementControlDiskData G D)
    (boundaryPoints : PolygonalReplacementBoundaryPointData.{u, u} G D controlDisks)
    (edgeEndpoints :
      PolygonalReplacementEdgeBoundaryEndpointData G D controlDisks boundaryPoints)
    (edgeParam :
      (e : G.edgeFinset) → Set.Icc (0 : ℝ) 1 → EuclideanSpace ℝ (Fin 2))
    (sourceBoundaryParam targetBoundaryParam : G.edgeFinset → Set.Icc (0 : ℝ) 1)
    (sourceBoundaryParam_eq :
      ∀ e, edgeParam e (sourceBoundaryParam e) =
        edgeEndpoints.sourceBoundaryPoint e)
    (targetBoundaryParam_eq :
      ∀ e, edgeParam e (targetBoundaryParam e) =
        edgeEndpoints.targetBoundaryPoint e)
    (intersectionCenterParam :
      ∀ {x : {p // p ∈ D.intersectionPoints}} {e : G.edgeFinset},
        x.1 ∈ D.edgeRelativeInterior e → Set.Icc (0 : ℝ) 1)
    (intersectionCenterParam_eq :
      ∀ {x : {p // p ∈ D.intersectionPoints}} {e : G.edgeFinset}
        (hx : x.1 ∈ D.edgeRelativeInterior e),
          edgeParam e (intersectionCenterParam hx) = x.1)
    (intersectionCenterParam_between_endpoint_params :
      ∀ {x : {p // p ∈ D.intersectionPoints}} {e : G.edgeFinset}
        (hx : x.1 ∈ D.edgeRelativeInterior e),
          sourceBoundaryParam e < intersectionCenterParam hx ∧
            intersectionCenterParam hx < targetBoundaryParam e)
    (intersectionLeftParam intersectionRightParam :
      ∀ {x : {p // p ∈ D.intersectionPoints}} {e : G.edgeFinset},
        x.1 ∈ D.edgeRelativeInterior e → Set.Icc (0 : ℝ) 1)
    (intersection_cut_order :
      ∀ {x : {p // p ∈ D.intersectionPoints}} {e : G.edgeFinset}
          (hx : x.1 ∈ D.edgeRelativeInterior e),
          intersectionLeftParam hx < intersectionCenterParam hx ∧
            intersectionCenterParam hx < intersectionRightParam hx)
    (intersection_cut_closedDisk :
      ∀ {x : {p // p ∈ D.intersectionPoints}} {e : G.edgeFinset}
          (hx : x.1 ∈ D.edgeRelativeInterior e)
          {u : Set.Icc (0 : ℝ) 1},
          intersectionLeftParam hx ≤ u →
            u ≤ intersectionRightParam hx →
              edgeParam e u ∈
                Metric.closedBall x.1 (controlDisks.intersectionRadius x))
    (intersection_cut_ordered_by_centers :
      ∀ {x y : {p // p ∈ D.intersectionPoints}} {e : G.edgeFinset}
          (hx : x.1 ∈ D.edgeRelativeInterior e)
          (hy : y.1 ∈ D.edgeRelativeInterior e),
          x ≠ y →
            intersectionCenterParam hx < intersectionCenterParam hy →
              intersectionRightParam hx < intersectionLeftParam hy) :
    ∀ e : G.edgeFinset,
      ∃ cuts : List {x : {p // p ∈ D.intersectionPoints} //
          x.1 ∈ D.edgeRelativeInterior e},
        cuts.Nodup ∧
          (∀ x : {x : {p // p ∈ D.intersectionPoints} //
              x.1 ∈ D.edgeRelativeInterior e}, x ∈ cuts) ∧
          (∀ i j (hi : i < cuts.length) (hj : j < cuts.length), i < j →
            intersectionCenterParam (cuts[i].2) <
              intersectionCenterParam (cuts[j].2)) ∧
          (∀ x : {x : {p // p ∈ D.intersectionPoints} //
              x.1 ∈ D.edgeRelativeInterior e}, x ∈ cuts →
            sourceBoundaryParam e < intersectionLeftParam x.2) ∧
          (∀ x : {x : {p // p ∈ D.intersectionPoints} //
              x.1 ∈ D.edgeRelativeInterior e}, x ∈ cuts →
            intersectionLeftParam x.2 < intersectionCenterParam x.2 ∧
              intersectionCenterParam x.2 < intersectionRightParam x.2) ∧
          (∀ x : {x : {p // p ∈ D.intersectionPoints} //
              x.1 ∈ D.edgeRelativeInterior e}, x ∈ cuts →
            intersectionRightParam x.2 < targetBoundaryParam e) ∧
          (∀ n (hn : n + 1 < cuts.length),
            intersectionRightParam (cuts[n].2) <
              intersectionLeftParam (cuts[n + 1].2)) := by
-- BODY
  classical
  intro e
  let Cut := {x : {p // p ∈ D.intersectionPoints} // x.1 ∈ D.edgeRelativeInterior e}
  let center : Cut → Set.Icc (0 : ℝ) 1 := fun x => intersectionCenterParam x.2
  let r : Cut → Cut → Prop := fun a b => center a ≤ center b
  have center_eq_to_cut_eq : ∀ {a b : Cut}, center a = center b → a = b := by
    intro a b hcenter
    apply Subtype.ext
    apply Subtype.ext
    calc
      a.1.1 = edgeParam e (center a) := by
        simpa [center] using (intersectionCenterParam_eq (x := a.1) (e := e) a.2).symm
      _ = edgeParam e (center b) := by rw [hcenter]
      _ = b.1.1 := by
        simpa [center] using intersectionCenterParam_eq (x := b.1) (e := e) b.2
  haveI : IsTrans Cut r := ⟨by intro a b c hab hbc; exact le_trans hab hbc⟩
  haveI : Std.Antisymm r := ⟨by
    intro a b hab hba
    exact center_eq_to_cut_eq (le_antisymm hab hba)⟩
  haveI : Std.Total r := ⟨by intro a b; exact le_total (center a) (center b)⟩
  let cuts : List Cut := (Finset.univ : Finset Cut).sort r
  have cuts_nodup : cuts.Nodup := by
    simpa [cuts] using Finset.sort_nodup (Finset.univ : Finset Cut) r
  have cuts_mem : ∀ x : Cut, x ∈ cuts := by
    intro x
    simpa [cuts] using
      (Finset.mem_sort (s := (Finset.univ : Finset Cut)) r (a := x)).2
        (Finset.mem_univ x)
  have cuts_pairwise : cuts.Pairwise r := by
    simpa [cuts] using Finset.pairwise_sort (Finset.univ : Finset Cut) r
  have center_strict :
      ∀ i j (hi : i < cuts.length) (hj : j < cuts.length), i < j →
        intersectionCenterParam (cuts[i].2) <
          intersectionCenterParam (cuts[j].2) := by
    intro i j hi hj hij
    have hle : center cuts[i] ≤ center cuts[j] := by
      have hfinlt : (⟨i, hi⟩ : Fin cuts.length) < ⟨j, hj⟩ := by
        exact hij
      simpa [r, center] using
        (List.Pairwise.rel_get_of_lt cuts_pairwise (a := ⟨i, hi⟩) (b := ⟨j, hj⟩) hfinlt)
    have hne_center : center cuts[i] ≠ center cuts[j] := by
      intro hcenter
      have hcuts_eq : cuts[i] = cuts[j] := center_eq_to_cut_eq hcenter
      have hidx : i = j := (List.Nodup.getElem_inj_iff cuts_nodup).mp hcuts_eq
      omega
    exact lt_of_le_of_ne hle hne_center
  have source_lt_left : ∀ x : Cut, x ∈ cuts →
      sourceBoundaryParam e < intersectionLeftParam x.2 := by
    intro x _hxmem
    by_contra hnot
    have hleft_le_source : intersectionLeftParam x.2 ≤ sourceBoundaryParam e :=
      le_of_not_gt hnot
    let sv : V := edgeEndpoints.edgeSourceVertex e
    have hsource_closed :
        edgeParam e (sourceBoundaryParam e) ∈
          Metric.closedBall (D.vertexPlacement sv) (controlDisks.vertexRadius sv) := by
      have hsphere :
          edgeParam e (sourceBoundaryParam e) ∈
            Metric.sphere (D.vertexPlacement sv) (controlDisks.vertexRadius sv) := by
        simpa [sv, sourceBoundaryParam_eq e] using
          (edgeEndpoints.sourceBoundary_on_control_boundary e).1
      exact Metric.sphere_subset_closedBall hsphere
    have hsource_le_right : sourceBoundaryParam e ≤ intersectionRightParam x.2 := by
      exact le_of_lt (lt_trans
        (intersectionCenterParam_between_endpoint_params x.2).1
        (intersection_cut_order x.2).2)
    have hsource_intersection_closed :
        edgeParam e (sourceBoundaryParam e) ∈
          Metric.closedBall x.1.1 (controlDisks.intersectionRadius x.1) :=
      intersection_cut_closedDisk x.2 hleft_le_source hsource_le_right
    exact (Set.disjoint_left.mp (controlDisks.vertex_intersection_disjoint sv x.1))
      hsource_closed hsource_intersection_closed
  have cut_order_all : ∀ x : Cut, x ∈ cuts →
      intersectionLeftParam x.2 < intersectionCenterParam x.2 ∧
        intersectionCenterParam x.2 < intersectionRightParam x.2 := by
    intro x _
    exact intersection_cut_order x.2
  have right_lt_target : ∀ x : Cut, x ∈ cuts →
      intersectionRightParam x.2 < targetBoundaryParam e := by
    intro x _hxmem
    by_contra hnot
    have htarget_le_right : targetBoundaryParam e ≤ intersectionRightParam x.2 :=
      le_of_not_gt hnot
    let tv : V := edgeEndpoints.edgeTargetVertex e
    have htarget_closed :
        edgeParam e (targetBoundaryParam e) ∈
          Metric.closedBall (D.vertexPlacement tv) (controlDisks.vertexRadius tv) := by
      have hsphere :
          edgeParam e (targetBoundaryParam e) ∈
            Metric.sphere (D.vertexPlacement tv) (controlDisks.vertexRadius tv) := by
        simpa [tv, targetBoundaryParam_eq e] using
          (edgeEndpoints.targetBoundary_on_control_boundary e).1
      exact Metric.sphere_subset_closedBall hsphere
    have hleft_le_target : intersectionLeftParam x.2 ≤ targetBoundaryParam e := by
      exact le_of_lt (lt_trans
        (intersection_cut_order x.2).1
        (intersectionCenterParam_between_endpoint_params x.2).2)
    have htarget_intersection_closed :
        edgeParam e (targetBoundaryParam e) ∈
          Metric.closedBall x.1.1 (controlDisks.intersectionRadius x.1) :=
      intersection_cut_closedDisk x.2 hleft_le_target htarget_le_right
    exact (Set.disjoint_left.mp (controlDisks.vertex_intersection_disjoint tv x.1))
      htarget_closed htarget_intersection_closed
  have consecutive_separation : ∀ n (hn : n + 1 < cuts.length),
      intersectionRightParam (cuts[n].2) <
        intersectionLeftParam (cuts[n + 1].2) := by
    intro n hn
    have hnlt : n < cuts.length := by omega
    have hcenter_lt := center_strict n (n + 1) hnlt hn (by omega)
    have hcuts_ne : cuts[n] ≠ cuts[n + 1] := by
      intro hcuts_eq
      have hidx : n = n + 1 := (List.Nodup.getElem_inj_iff cuts_nodup).mp hcuts_eq
      omega
    have hpoints_ne : (cuts[n]).1 ≠ (cuts[n + 1]).1 := by
      intro hpoints_eq
      exact hcuts_ne (Subtype.ext hpoints_eq)
    exact intersection_cut_ordered_by_centers (cuts[n].2) (cuts[n + 1].2)
      hpoints_ne hcenter_lt
  exact ⟨cuts, cuts_nodup, cuts_mem, center_strict, source_lt_left,
    cut_order_all, right_lt_target, consecutive_separation⟩
