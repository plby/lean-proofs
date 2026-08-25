import Mathlib.Tactic
import Util.IncidenceGeometry.CrossingFreeEdgeInteriorDisjoint
import Util.IncidenceGeometry.DartSuccessorFromLocalClockwiseNext
import Util.IncidenceGeometry.FinitePlanarClockwiseSuccessorSectors
import Util.IncidenceGeometry.OrdinaryDrawingSegmentDirectionsNotSamePositiveRay
import Util.IncidenceGeometry.PlanarClockwiseSweptTwoRayEndpointConesInSector
import Util.IncidenceGeometry.PlanarRot90Norm
import Util.IncidenceGeometry.PlanarRot90Orthogonal
import Util.IncidenceGeometry.PlanarSlitDiskEndpointConesAvoidRay
import Util.IncidenceGeometry.PlaneDrawingDartArcData
import Util.IncidenceGeometry.PlaneDrawingDartVertexLocalDiskIdentity
import Util.IncidenceGeometry.PlaneDrawingDartVertexSectorGeometry
import Util.IncidenceGeometry.PlaneDrawingDartVertexStarData
import Util.IncidenceGeometry.PolygonalArcInitialEndpointLeftCone
import Util.IncidenceGeometry.PolygonalArcReverse
import Util.IncidenceGeometry.PolygonalArcTerminalEndpointLeftCone

open Classical
noncomputable section

lemma PlaneDrawingDartGeometricClockwiseSectors {V : Type*} [Fintype V]
    (G : SimpleGraph V) [Fintype G.edgeSet] [DecidableRel G.Adj]
    (D : OrdinaryPolygonalDrawing G) (hD : D.crossingSet.card = 0)
    (A : PlaneDrawingDartArcData G D) :
    ∃ C : PlaneDrawingDartVertexSectorGeometry G D A,
      ∀ d : G.Dart,
        let rev : {e : G.Dart // e.toProd.1 = d.toProd.2} :=
          ⟨d.symm, by simp [SimpleGraph.Dart.symm]⟩
        let nxt : {e : G.Dart // e.toProd.1 = d.toProd.2} :=
          ⟨C.star.successor d, C.star.successor_tail d⟩
        ((∀ e : {e : G.Dart // e.toProd.1 = d.toProd.2}, e = rev) ∧
          C.successorSector d =
            Metric.ball (D.vertexPlacement d.toProd.2)
                (C.star.localDiskRadius d.toProd.2) \
              ({q | ∃ t : ℝ, 0 < t ∧
                q = D.vertexPlacement d.toProd.2 +
                  t • C.star.germDirection d.toProd.2 rev} ∪
                ({D.vertexPlacement d.toProd.2} :
                  Set (EuclideanSpace ℝ (Fin 2)))))
        ∨
        (∃ c s : ℝ,
          (s ≠ 0 ∨ c < 0) ∧
          C.star.germDirection d.toProd.2 nxt =
            c • C.star.germDirection d.toProd.2 rev -
              s • PlanarRot90 (C.star.germDirection d.toProd.2 rev) ∧
          C.successorSector d =
            (let base : EuclideanSpace ℝ (Fin 2) :=
              C.star.germDirection d.toProd.2 rev
             let baseChart : EuclideanSpace ℝ (Fin 2) →
                EuclideanSpace ℝ (Fin 2) :=
              fun z => D.vertexPlacement d.toProd.2 +
                z 0 • base + z 1 • PlanarRot90 base
             if 0 < s then
               baseChart ''
                {z : EuclideanSpace ℝ (Fin 2) |
                  z 0 ^ 2 + z 1 ^ 2 <
                    (C.star.localDiskRadius d.toProd.2 / ‖base‖) ^ 2 ∧
                  z 1 < 0 ∧ 0 < c * z 1 + s * z 0}
             else if s < 0 then
               baseChart ''
                {z : EuclideanSpace ℝ (Fin 2) |
                  z 0 ^ 2 + z 1 ^ 2 <
                    (C.star.localDiskRadius d.toProd.2 / ‖base‖) ^ 2 ∧
                  (z 1 < 0 ∨ 0 < c * z 1 + s * z 0)}
             else
               baseChart ''
                {z : EuclideanSpace ℝ (Fin 2) |
                  z 0 ^ 2 + z 1 ^ 2 <
                    (C.star.localDiskRadius d.toProd.2 / ‖base‖) ^ 2 ∧
                  z 1 < 0})) := by
  classical
  rcases PlaneDrawingDartVertexLocalDiskIdentity G D hD A with
    ⟨localDiskRadius, germDirection, radialGerm, hlocalDiskRadius_pos,
      hgermDirection_ne_zero, hgermDirection_eq_normalized_first,
      hradialGerm_eq_openSegment, hradialGerm_subset_dartArc,
      hlocalDisk_meets_drawing⟩
  have hposRayDistinct :
      ∀ (v : V) [Nonempty {d : G.Dart // d.toProd.1 = v}]
        {i j : {d : G.Dart // d.toProd.1 = v}},
        (∃ t : ℝ, 0 < t ∧ germDirection v j = t • germDirection v i) → i = j := by
    intro v _ i j hsame
    let firstDirection :
        {d : G.Dart // d.toProd.1 = v} → EuclideanSpace ℝ (Fin 2) :=
      fun d =>
        (A.dartArc d.1).vertices[1]'(Nat.lt_of_succ_le
          (A.dartArc d.1).length_ge_two) - D.vertexPlacement v
    have firstDirection_ne_zero :
        ∀ d : {d : G.Dart // d.toProd.1 = v}, firstDirection d ≠ 0 := by
      intro d hzero
      have hgd_zero : germDirection v d = 0 := by
        rw [hgermDirection_eq_normalized_first v d]
        simpa [firstDirection] using congrArg ((fun x => (‖x‖)⁻¹ • x)) hzero
      exact hgermDirection_ne_zero v d hgd_zero
    have hfirst_pos :
        ∃ a : ℝ, 0 < a ∧ firstDirection j = a • firstDirection i := by
      rcases hsame with ⟨t, ht, hsame⟩
      have hi_norm_pos : 0 < ‖firstDirection i‖ :=
        norm_pos_iff.mpr (firstDirection_ne_zero i)
      have hj_norm_pos : 0 < ‖firstDirection j‖ :=
        norm_pos_iff.mpr (firstDirection_ne_zero j)
      refine ⟨‖firstDirection j‖ * t * (‖firstDirection i‖)⁻¹, ?_, ?_⟩
      · positivity
      · calc
          firstDirection j =
              ‖firstDirection j‖ • ((‖firstDirection j‖)⁻¹ • firstDirection j) := by
                rw [smul_smul, mul_inv_cancel₀ (ne_of_gt hj_norm_pos), one_smul]
          _ = ‖firstDirection j‖ • germDirection v j := by
                rw [hgermDirection_eq_normalized_first v j]
          _ = ‖firstDirection j‖ • (t • germDirection v i) := by
                rw [hsame]
          _ = ‖firstDirection j‖ •
                (t • ((‖firstDirection i‖)⁻¹ • firstDirection i)) := by
                rw [hgermDirection_eq_normalized_first v i]
          _ = (‖firstDirection j‖ * t * (‖firstDirection i‖)⁻¹) •
                firstDirection i := by
                rw [smul_smul, smul_smul]
    have same_edge_implies_same_dart :
        A.dartEdge i.1 = A.dartEdge j.1 → i = j := by
      intro hedgeA
      apply Subtype.ext
      apply SimpleGraph.Dart.ext
      apply Prod.ext
      · exact i.2.trans j.2.symm
      · have hedge : i.1.edge = j.1.edge := by
          calc
            i.1.edge = (A.dartEdge i.1).1 := (A.dartEdge_eq i.1).symm
            _ = (A.dartEdge j.1).1 := by rw [hedgeA]
            _ = j.1.edge := A.dartEdge_eq j.1
        have hsym :
            Sym2.mk i.1.toProd.1 i.1.toProd.2 =
              Sym2.mk j.1.toProd.1 j.1.toProd.2 := by
          simpa [SimpleGraph.Dart.edge] using hedge
        rcases (Sym2.eq_iff.mp hsym) with hsame_prod | hswap_prod
        · exact hsame_prod.2
        · have htail : i.1.toProd.1 = j.1.toProd.1 := i.2.trans j.2.symm
          have hhead_eq_tail : j.1.toProd.2 = j.1.toProd.1 := by
            calc
              j.1.toProd.2 = i.1.toProd.1 := hswap_prod.1.symm
              _ = j.1.toProd.1 := htail
          have hloop : G.Adj j.1.toProd.1 j.1.toProd.1 := by
            simpa [hhead_eq_tail] using j.1.adj
          exact False.elim ((G.loopless.irrefl j.1.toProd.1) hloop)
    by_cases hedgeA : A.dartEdge i.1 = A.dartEdge j.1
    · exact same_edge_implies_same_dart hedgeA
    · have segment_of_dart :
          ∀ d : {d : G.Dart // d.toProd.1 = v},
            ∃ k : ℕ, ∃ hk : k + 1 < (D.edgeArc (A.dartEdge d.1)).vertices.length,
              segment ℝ (D.vertexPlacement v)
                  (D.vertexPlacement v + firstDirection d) =
                segment ℝ (D.edgeArc (A.dartEdge d.1)).vertices[k]
                  (D.edgeArc (A.dartEdge d.1)).vertices[k + 1] := by
        intro d
        let Γ : PolygonalArc := D.edgeArc (A.dartEdge d.1)
        rcases A.dartArc_orientation d.1 with horient | horient
        · rcases horient with ⟨hdart, hsource⟩
          have hfirstΓ : 0 + 1 < Γ.vertices.length := by
            have hlen := Γ.length_ge_two
            omega
          have hzeroΓ : 0 < Γ.vertices.length := by
            have hlen := Γ.length_ge_two
            omega
          have hsource0 : Γ.vertices[0] = Γ.source := by
            have hget : Γ.vertices[0]? = some Γ.vertices[0] :=
              List.getElem?_eq_getElem hzeroΓ
            rw [← List.head?_eq_getElem?, Γ.source_eq_head] at hget
            exact Option.some.inj hget.symm
          have hsource_v : Γ.source = D.vertexPlacement v := by
            simpa [Γ, d.2] using hsource
          refine ⟨0, hfirstΓ, ?_⟩
          have hadd :
              D.vertexPlacement v + firstDirection d = Γ.vertices[1]'hfirstΓ := by
            dsimp [firstDirection, Γ] at *
            rw [hdart]
            abel
          simpa [Γ, hsource0, hsource_v, hadd] using
            (rfl :
              segment ℝ Γ.vertices[0] Γ.vertices[0 + 1] =
                segment ℝ Γ.vertices[0] Γ.vertices[0 + 1])
        · rcases horient with ⟨hdart, htarget⟩
          let k : ℕ := Γ.vertices.length - 2
          have hk : k + 1 < Γ.vertices.length := by
            have hlen := Γ.length_ge_two
            dsimp [k]
            omega
          have hk_lt : k < Γ.vertices.length := Nat.lt_of_succ_lt hk
          have hlast_lt : Γ.vertices.length - 1 < Γ.vertices.length := by
            have hlen := Γ.length_ge_two
            omega
          have hlast_succ : k + 1 = Γ.vertices.length - 1 := by
            have hlen := Γ.length_ge_two
            dsimp [k]
            omega
          have htarget_last : Γ.vertices[k + 1] = Γ.target := by
            have hget :
                Γ.vertices[Γ.vertices.length - 1]? =
                  some Γ.vertices[Γ.vertices.length - 1] :=
              List.getElem?_eq_getElem hlast_lt
            rw [← List.getLast?_eq_getElem?, Γ.target_eq_last] at hget
            have hlast_vertex : Γ.vertices[Γ.vertices.length - 1] = Γ.target :=
              Option.some.inj hget.symm
            simpa [hlast_succ] using hlast_vertex
          have htarget_v : Γ.target = D.vertexPlacement v := by
            simpa [Γ, d.2] using htarget
          have hrev_first :
              (PolygonalArcReverse Γ).vertices[1]'(Nat.lt_of_succ_le
                  (PolygonalArcReverse Γ).length_ge_two) =
                Γ.vertices[k]'hk_lt := by
            have hrev_index : Γ.vertices.length - 1 - 1 = k := by
              have hlen := Γ.length_ge_two
              dsimp [k]
              omega
            simpa [PolygonalArcReverse, List.length_reverse, hrev_index] using
              (List.getElem_reverse (l := Γ.vertices) (i := 1))
          refine ⟨k, hk, ?_⟩
          have hadd :
              D.vertexPlacement v + firstDirection d = Γ.vertices[k]'hk_lt := by
            dsimp [firstDirection, Γ] at *
            rw [hdart, hrev_first]
            rw [← htarget_v]
            abel
          calc
            segment ℝ (D.vertexPlacement v) (D.vertexPlacement v + firstDirection d)
                = segment ℝ Γ.vertices[k + 1] Γ.vertices[k] := by
                    simpa [Γ, htarget_v, htarget_last, hadd]
            _ = segment ℝ Γ.vertices[k] Γ.vertices[k + 1] := by
                    rw [segment_symm]
      rcases segment_of_dart i with ⟨ki, hki, hsegi⟩
      rcases segment_of_dart j with ⟨kj, hkj, hsegj⟩
      have hnot :=
        OrdinaryDrawingSegmentDirectionsNotSamePositiveRay
          G D (e := A.dartEdge i.1) (f := A.dartEdge j.1) hedgeA
          hki hkj (firstDirection_ne_zero i) hsegi hsegj
      exact False.elim (hnot hfirst_pos)
  have finiteSectorAt :
      ∀ (v : V) (hv : Nonempty {d : G.Dart // d.toProd.1 = v}),
        ∃ clockwiseNext : Equiv.Perm {d : G.Dart // d.toProd.1 = v},
        ∃ fullClockwiseTurn : ℝ,
        ∃ clockwiseTurn :
          {d : G.Dart // d.toProd.1 = v} →
            {d : G.Dart // d.toProd.1 = v} → ℝ,
        ∃ sector : {d : G.Dart // d.toProd.1 = v} →
            Set (EuclideanSpace ℝ (Fin 2)),
          fullClockwiseTurn = 2 * Real.pi ∧
          0 < fullClockwiseTurn ∧
          (∀ i j : {d : G.Dart // d.toProd.1 = v}, 0 < clockwiseTurn i j) ∧
          (∀ i j : {d : G.Dart // d.toProd.1 = v},
            clockwiseTurn i j ≤ fullClockwiseTurn) ∧
          (∀ i j : {d : G.Dart // d.toProd.1 = v},
            clockwiseTurn i j = fullClockwiseTurn ↔ j = i) ∧
          (∀ i j : {d : G.Dart // d.toProd.1 = v}, j ≠ i →
            clockwiseTurn i (clockwiseNext i) ≤ clockwiseTurn i j) ∧
          (∀ i : {d : G.Dart // d.toProd.1 = v},
            clockwiseNext i = i ↔
              ∀ j : {d : G.Dart // d.toProd.1 = v}, j = i) ∧
          (∀ i : {d : G.Dart // d.toProd.1 = v},
            if h : clockwiseNext i = i then
              sector i =
                Metric.ball (D.vertexPlacement v) (localDiskRadius v) \
                  ({q | ∃ t : ℝ, 0 < t ∧
                    q = D.vertexPlacement v + t • germDirection v i} ∪
                    ({D.vertexPlacement v} :
                      Set (EuclideanSpace ℝ (Fin 2))))
            else
              ∃ c s : ℝ,
                (s ≠ 0 ∨ c < 0) ∧
                germDirection v (clockwiseNext i) =
                  c • germDirection v i - s • PlanarRot90 (germDirection v i) ∧
                sector i =
                  (let base : EuclideanSpace ℝ (Fin 2) := germDirection v i
                   let baseChart : EuclideanSpace ℝ (Fin 2) →
                      EuclideanSpace ℝ (Fin 2) :=
                    fun z => D.vertexPlacement v +
                      z 0 • base + z 1 • PlanarRot90 base
                   if 0 < s then
                     baseChart ''
                      {z : EuclideanSpace ℝ (Fin 2) |
                        z 0 ^ 2 + z 1 ^ 2 <
                          (localDiskRadius v / ‖base‖) ^ 2 ∧
                        z 1 < 0 ∧ 0 < c * z 1 + s * z 0}
                   else if s < 0 then
                     baseChart ''
                      {z : EuclideanSpace ℝ (Fin 2) |
                        z 0 ^ 2 + z 1 ^ 2 <
                          (localDiskRadius v / ‖base‖) ^ 2 ∧
                        (z 1 < 0 ∨ 0 < c * z 1 + s * z 0)}
                   else
                     baseChart ''
                      {z : EuclideanSpace ℝ (Fin 2) |
                        z 0 ^ 2 + z 1 ^ 2 <
                          (localDiskRadius v / ‖base‖) ^ 2 ∧
                        z 1 < 0})) ∧
          (∀ i : {d : G.Dart // d.toProd.1 = v},
            IsOpen (sector i) ∧ IsConnected (sector i)) ∧
          (∀ i : {d : G.Dart // d.toProd.1 = v},
            sector i ⊆ Metric.ball (D.vertexPlacement v) (localDiskRadius v)) ∧
          (∀ i j : {d : G.Dart // d.toProd.1 = v},
            Disjoint (sector i)
              {q | ∃ t : ℝ, 0 < t ∧
                q = D.vertexPlacement v + t • germDirection v j}) ∧
          (∀ q : EuclideanSpace ℝ (Fin 2),
            q ∈ Metric.ball (D.vertexPlacement v) (localDiskRadius v) →
              q ≠ D.vertexPlacement v →
                (∀ i : {d : G.Dart // d.toProd.1 = v},
                  q ∉ {x | ∃ t : ℝ, 0 < t ∧
                    x = D.vertexPlacement v + t • germDirection v i}) →
                  ∃ i : {d : G.Dart // d.toProd.1 = v}, q ∈ sector i) := by
    intro v hv
    letI : Nonempty {d : G.Dart // d.toProd.1 = v} := hv
    exact
      FinitePlanarClockwiseSuccessorSectors
        (p := D.vertexPlacement v) (ρ := localDiskRadius v)
        (u := germDirection v)
        (hρ := hlocalDiskRadius_pos v)
        (hu := hgermDirection_ne_zero v)
        (hposRayDistinct := hposRayDistinct v)
  choose localClockwiseNext localFullClockwiseTurn localClockwiseTurn
    localSector localSector_spec using finiteSectorAt
  let clockwiseNext :
      ∀ v : V, Equiv.Perm {d : G.Dart // d.toProd.1 = v} := fun v =>
    if hv : Nonempty {d : G.Dart // d.toProd.1 = v} then
      localClockwiseNext v hv
    else
      Equiv.refl _
  let fullClockwiseTurn : V → ℝ := fun v =>
    if hv : Nonempty {d : G.Dart // d.toProd.1 = v} then
      localFullClockwiseTurn v hv
    else
      2 * Real.pi
  let clockwiseTurn :
      ∀ v : V, {d : G.Dart // d.toProd.1 = v} →
        {d : G.Dart // d.toProd.1 = v} → ℝ := fun v =>
    if hv : Nonempty {d : G.Dart // d.toProd.1 = v} then
      localClockwiseTurn v hv
    else
      fun _ _ => 2 * Real.pi
  let sector :
      ∀ v : V, {d : G.Dart // d.toProd.1 = v} →
        Set (EuclideanSpace ℝ (Fin 2)) := fun v =>
    if hv : Nonempty {d : G.Dart // d.toProd.1 = v} then
      localSector v hv
    else
      fun _ => ∅
  have clockwiseNext_eq_of_nonempty
      (v : V) (hv : Nonempty {d : G.Dart // d.toProd.1 = v}) :
      clockwiseNext v = localClockwiseNext v hv := by
    dsimp [clockwiseNext]
    rw [dif_pos hv]
  have fullClockwiseTurn_eq_of_nonempty
      (v : V) (hv : Nonempty {d : G.Dart // d.toProd.1 = v}) :
      fullClockwiseTurn v = localFullClockwiseTurn v hv := by
    dsimp [fullClockwiseTurn]
    rw [dif_pos hv]
  have fullClockwiseTurn_eq_of_empty
      (v : V) (hv : ¬ Nonempty {d : G.Dart // d.toProd.1 = v}) :
      fullClockwiseTurn v = 2 * Real.pi := by
    dsimp [fullClockwiseTurn]
    rw [dif_neg hv]
  have clockwiseTurn_eq_of_nonempty
      (v : V) (hv : Nonempty {d : G.Dart // d.toProd.1 = v}) :
      clockwiseTurn v = localClockwiseTurn v hv := by
    dsimp [clockwiseTurn]
    rw [dif_pos hv]
  have sector_eq_of_nonempty
      (v : V) (hv : Nonempty {d : G.Dart // d.toProd.1 = v}) :
      sector v = localSector v hv := by
    dsimp [sector]
    rw [dif_pos hv]
  have clockwiseNext_eq_self_iff_isolated :
      ∀ (v : V) (d : {d : G.Dart // d.toProd.1 = v}),
        clockwiseNext v d = d ↔ ∀ e : {d : G.Dart // d.toProd.1 = v}, e = d := by
    intro v d
    have hv : Nonempty {d : G.Dart // d.toProd.1 = v} := ⟨d⟩
    rcases localSector_spec v hv with
      ⟨_hfull_eq, _hfull_pos, _hturn_pos, _hturn_le, _hturn_full,
        _hfirst_after, hfixed, _hsector_def, _hopen_connected, _hball,
        _hdisjoint, _hcover⟩
    rw [clockwiseNext_eq_of_nonempty v hv]
    exact hfixed d
  rcases DartSuccessorFromLocalClockwiseNext G clockwiseNext
      clockwiseNext_eq_self_iff_isolated with
    ⟨successor, hsuccessor_tail, hsuccessor_eq_clockwiseNext,
      hsuccessor_single_incident⟩
  let star : PlaneDrawingDartVertexStarData G D A :=
    { localDiskRadius := localDiskRadius
      localDiskRadius_pos := hlocalDiskRadius_pos
      germDirection := germDirection
      germDirection_ne_zero := hgermDirection_ne_zero
      germDirection_eq_normalized_firstSegment :=
        hgermDirection_eq_normalized_first
      radialGerm := radialGerm
      radialGerm_eq_openSegment := by
        intro v d
        exact ⟨localDiskRadius v, hlocalDiskRadius_pos v, le_rfl,
          hradialGerm_eq_openSegment v d⟩
      radialGerm_subset_dartArc := hradialGerm_subset_dartArc
      localDisk_meets_drawing_only_incident_germs := hlocalDisk_meets_drawing
      clockwiseNext := clockwiseNext
      fullClockwiseTurn := fullClockwiseTurn
      fullClockwiseTurn_pos := by
        intro v
        by_cases hv : Nonempty {d : G.Dart // d.toProd.1 = v}
        · rcases localSector_spec v hv with
            ⟨_hfull_eq, hfull_pos, _hturn_pos, _hturn_le, _hturn_full,
              _hfirst_after, _hfixed, _hsector_def, _hopen_connected, _hball,
              _hdisjoint, _hcover⟩
          rw [fullClockwiseTurn_eq_of_nonempty v hv]
          exact hfull_pos
        · have hpi : 0 < 2 * Real.pi :=
            mul_pos (by norm_num) Real.pi_pos
          rw [fullClockwiseTurn_eq_of_empty v hv]
          exact hpi
      clockwiseTurn := clockwiseTurn
      clockwiseTurn_pos := by
        intro v d e
        have hv : Nonempty {d : G.Dart // d.toProd.1 = v} := ⟨d⟩
        rcases localSector_spec v hv with
          ⟨_hfull_eq, _hfull_pos, hturn_pos, _hturn_le, _hturn_full,
            _hfirst_after, _hfixed, _hsector_def, _hopen_connected, _hball,
            _hdisjoint, _hcover⟩
        rw [clockwiseTurn_eq_of_nonempty v hv]
        exact hturn_pos d e
      clockwiseTurn_le_full := by
        intro v d e
        have hv : Nonempty {d : G.Dart // d.toProd.1 = v} := ⟨d⟩
        rcases localSector_spec v hv with
          ⟨_hfull_eq, _hfull_pos, _hturn_pos, hturn_le, _hturn_full,
            _hfirst_after, _hfixed, _hsector_def, _hopen_connected, _hball,
            _hdisjoint, _hcover⟩
        rw [clockwiseTurn_eq_of_nonempty v hv,
          fullClockwiseTurn_eq_of_nonempty v hv]
        exact hturn_le d e
      clockwiseTurn_full_iff_same := by
        intro v d e
        have hv : Nonempty {d : G.Dart // d.toProd.1 = v} := ⟨d⟩
        rcases localSector_spec v hv with
          ⟨_hfull_eq, _hfull_pos, _hturn_pos, _hturn_le, hturn_full,
            _hfirst_after, _hfixed, _hsector_def, _hopen_connected, _hball,
            _hdisjoint, _hcover⟩
        rw [clockwiseTurn_eq_of_nonempty v hv,
          fullClockwiseTurn_eq_of_nonempty v hv]
        exact hturn_full d e
      clockwiseNext_first_after := by
        intro v d e hne
        have hv : Nonempty {d : G.Dart // d.toProd.1 = v} := ⟨d⟩
        rcases localSector_spec v hv with
          ⟨_hfull_eq, _hfull_pos, _hturn_pos, _hturn_le, _hturn_full,
            hfirst_after, _hfixed, _hsector_def, _hopen_connected, _hball,
            _hdisjoint, _hcover⟩
        rw [clockwiseNext_eq_of_nonempty v hv, clockwiseTurn_eq_of_nonempty v hv]
        exact hfirst_after d e hne
      clockwiseNext_eq_self_iff_isolated := clockwiseNext_eq_self_iff_isolated
      successor := successor
      successor_tail := hsuccessor_tail
      successor_eq_clockwiseNext := hsuccessor_eq_clockwiseNext
      successor_single_incident := hsuccessor_single_incident }
  let successorSector : G.Dart → Set (EuclideanSpace ℝ (Fin 2)) := fun d =>
    sector d.toProd.2 ⟨d.symm, by simp [SimpleGraph.Dart.symm]⟩
  have successorSector_open_connected :
      ∀ d : G.Dart,
        IsOpen (successorSector d) ∧ IsConnected (successorSector d) := by
    intro d
    let rev : {e : G.Dart // e.toProd.1 = d.toProd.2} :=
      ⟨d.symm, by simp [SimpleGraph.Dart.symm]⟩
    have hv : Nonempty {e : G.Dart // e.toProd.1 = d.toProd.2} := ⟨rev⟩
    rcases localSector_spec d.toProd.2 hv with
      ⟨_hfull_eq, _hfull_pos, _hturn_pos, _hturn_le, _hturn_full,
        _hfirst_after, _hfixed, _hsector_def, hopen_connected, _hball,
        _hdisjoint, _hcover⟩
    change IsOpen (sector d.toProd.2 rev) ∧ IsConnected (sector d.toProd.2 rev)
    rw [sector_eq_of_nonempty d.toProd.2 hv]
    exact hopen_connected rev
  have successorSector_subset_localDisk :
      ∀ d : G.Dart,
        successorSector d ⊆
          Metric.ball (D.vertexPlacement d.toProd.2) (localDiskRadius d.toProd.2) := by
    intro d
    let rev : {e : G.Dart // e.toProd.1 = d.toProd.2} :=
      ⟨d.symm, by simp [SimpleGraph.Dart.symm]⟩
    have hv : Nonempty {e : G.Dart // e.toProd.1 = d.toProd.2} := ⟨rev⟩
    rcases localSector_spec d.toProd.2 hv with
      ⟨_hfull_eq, _hfull_pos, _hturn_pos, _hturn_le, _hturn_full,
        _hfirst_after, _hfixed, _hsector_def, _hopen_connected, hball,
        _hdisjoint, _hcover⟩
    change sector d.toProd.2 rev ⊆
      Metric.ball (D.vertexPlacement d.toProd.2) (localDiskRadius d.toProd.2)
    rw [sector_eq_of_nonempty d.toProd.2 hv]
    exact hball rev
  have radialGerm_subset_positive_ray :
      ∀ (v : V) (e : {e : G.Dart // e.toProd.1 = v}),
        radialGerm v e ⊆
          {q | ∃ t : ℝ, 0 < t ∧
            q = D.vertexPlacement v + t • germDirection v e} := by
    intro v e q hq
    rw [hradialGerm_eq_openSegment v e] at hq
    rw [openSegment_eq_image_lineMap] at hq
    rcases hq with ⟨a, ha, hq_eq⟩
    refine ⟨a * localDiskRadius v, mul_pos ha.1 (hlocalDiskRadius_pos v), ?_⟩
    rw [← hq_eq]
    rw [AffineMap.lineMap_apply_module]
    module
  have germDirection_norm_one :
      ∀ (v : V) (e : {e : G.Dart // e.toProd.1 = v}),
        ‖germDirection v e‖ = 1 := by
    intro v e
    let firstDirection : EuclideanSpace ℝ (Fin 2) :=
      (A.dartArc e.1).vertices[1]'(Nat.lt_of_succ_le
        (A.dartArc e.1).length_ge_two) - D.vertexPlacement v
    have hfirst_ne : firstDirection ≠ 0 := by
      intro hzero
      have hgd_zero : germDirection v e = 0 := by
        rw [hgermDirection_eq_normalized_first v e]
        simpa [firstDirection] using congrArg ((fun x => (‖x‖)⁻¹ • x)) hzero
      exact hgermDirection_ne_zero v e hgd_zero
    have hnorm_pos : 0 < ‖firstDirection‖ := norm_pos_iff.mpr hfirst_ne
    rw [hgermDirection_eq_normalized_first v e]
    simp [firstDirection, norm_smul, Real.norm_eq_abs, abs_of_pos
      (inv_pos.mpr hnorm_pos), inv_mul_cancel₀ (ne_of_gt hnorm_pos)]
  have initial_left_endpoint_subset_chart :
      ∀ (v : V) (e : {e : G.Dart // e.toProd.1 = v}) (r K : ℝ), 0 < r →
        PolygonalArcInitialEndpointLeftCone (A.dartArc e.1) r K ⊆
          (fun z : EuclideanSpace ℝ (Fin 2) =>
            D.vertexPlacement v +
              z 0 • germDirection v e + z 1 • PlanarRot90 (germDirection v e)) ''
          {z : EuclideanSpace ℝ (Fin 2) |
            0 < z 0 ∧ z 0 ^ 2 + z 1 ^ 2 <
              (r / ‖germDirection v e‖) ^ 2 ∧
            0 < z 1 ∧ z 1 < K * z 0} := by
    intro v e r K hr q hq
    let raw : EuclideanSpace ℝ (Fin 2) :=
      (A.dartArc e.1).vertices[1]'(Nat.lt_of_succ_le
        (A.dartArc e.1).length_ge_two) - D.vertexPlacement v
    have hraw_ne : raw ≠ 0 := by
      intro hzero
      have hgd_zero : germDirection v e = 0 := by
        rw [hgermDirection_eq_normalized_first v e]
        simpa [raw] using congrArg ((fun x => (‖x‖)⁻¹ • x)) hzero
      exact hgermDirection_ne_zero v e hgd_zero
    have hraw_norm_pos : 0 < ‖raw‖ := norm_pos_iff.mpr hraw_ne
    have hraw_eq : raw = ‖raw‖ • germDirection v e := by
      have hgd := hgermDirection_eq_normalized_first v e
      calc
        raw = ‖raw‖ • ((‖raw‖)⁻¹ • raw) := by
          rw [smul_smul, mul_inv_cancel₀ (ne_of_gt hraw_norm_pos), one_smul]
        _ = ‖raw‖ • germDirection v e := by
          rw [hgd]
    dsimp [PolygonalArcInitialEndpointLeftCone] at hq
    rcases hq with ⟨z, hz, hqeq⟩
    rcases hz with ⟨hz0, hzrad, hz1pos, hz1lt⟩
    let w : EuclideanSpace ℝ (Fin 2) := ‖raw‖ • z
    refine ⟨w, ?_, ?_⟩
    · refine ⟨?_, ?_, ?_, ?_⟩
      · dsimp [w]
        simpa [hraw_norm_pos] using hz0
      · have hdist_eq : dist (A.dartArc e.1).source
              ((A.dartArc e.1).vertices[1]'(Nat.lt_of_succ_le
                (A.dartArc e.1).length_ge_two)) = ‖raw‖ := by
          rw [dist_eq_norm]
          have hsource : (A.dartArc e.1).source = D.vertexPlacement v := by
            simpa [e.2] using A.dartArc_source e.1
          rw [hsource]
          have hnorm_neg :
              ‖D.vertexPlacement v -
                (A.dartArc e.1).vertices[1]'(Nat.lt_of_succ_le
                  (A.dartArc e.1).length_ge_two)‖ = ‖raw‖ := by
            dsimp [raw]
            rw [← norm_neg (D.vertexPlacement v -
              (A.dartArc e.1).vertices[1]'(Nat.lt_of_succ_le
                (A.dartArc e.1).length_ge_two))]
            congr 1
            abel
          exact hnorm_neg
        have hbase_norm : ‖germDirection v e‖ = 1 := germDirection_norm_one v e
        have hzrad' : z 0 ^ 2 + z 1 ^ 2 < (r / ‖raw‖) ^ 2 := by
          simpa [hdist_eq] using hzrad
        have hraw_sq_pos : 0 < ‖raw‖ ^ 2 := sq_pos_of_pos hraw_norm_pos
        have hwcoord :
            w 0 ^ 2 + w 1 ^ 2 = ‖raw‖ ^ 2 * (z 0 ^ 2 + z 1 ^ 2) := by
          simp [w]
          ring
        have htarget : ‖raw‖ ^ 2 * (z 0 ^ 2 + z 1 ^ 2) < r ^ 2 := by
          have hmul := mul_lt_mul_of_pos_left hzrad' hraw_sq_pos
          have hscale : ‖raw‖ ^ 2 * (r / ‖raw‖) ^ 2 = r ^ 2 := by
            field_simp [ne_of_gt hraw_norm_pos]
          simpa [hscale] using hmul
        have hbase_rhs : (r / ‖germDirection v e‖) ^ 2 = r ^ 2 := by
          rw [hbase_norm]
          norm_num
        rw [hwcoord, hbase_rhs]
        exact htarget
      · dsimp [w]
        simpa [hraw_norm_pos] using hz1pos
      · dsimp [w]
        have hmul := mul_lt_mul_of_pos_left hz1lt hraw_norm_pos
        simpa [mul_assoc, mul_comm, mul_left_comm] using hmul
    · rw [← hqeq]
      have hsource : (A.dartArc e.1).source = D.vertexPlacement v := by
        simpa [e.2] using A.dartArc_source e.1
      rw [hsource]
      dsimp [w]
      change D.vertexPlacement v +
          (‖raw‖ * z 0) • germDirection v e +
            (‖raw‖ * z 1) • PlanarRot90 (germDirection v e) =
        D.vertexPlacement v + z 0 • raw + z 1 • PlanarRot90 raw
      have hrot_scaled :
          PlanarRot90 (‖raw‖ • germDirection v e) =
            ‖raw‖ • PlanarRot90 (germDirection v e) := by
        apply PiLp.ext
        intro k
        fin_cases k <;> simp [PlanarRot90]
      conv_rhs => rw [hraw_eq, hrot_scaled]
      module
  have terminal_left_endpoint_subset_chart :
      ∀ (d : G.Dart) (r K : ℝ), 0 < r →
        let rev : {e : G.Dart // e.toProd.1 = d.toProd.2} :=
          ⟨d.symm, by simp [SimpleGraph.Dart.symm]⟩
        PolygonalArcTerminalEndpointLeftCone (A.dartArc d) r K ⊆
          (fun z : EuclideanSpace ℝ (Fin 2) =>
            D.vertexPlacement d.toProd.2 +
              z 0 • germDirection d.toProd.2 rev +
                z 1 • PlanarRot90 (germDirection d.toProd.2 rev)) ''
          {z : EuclideanSpace ℝ (Fin 2) |
            0 < z 0 ∧ z 0 ^ 2 + z 1 ^ 2 <
              (r / ‖germDirection d.toProd.2 rev‖) ^ 2 ∧
            -K * z 0 < z 1 ∧ z 1 < 0} := by
    intro d r K hr
    let rev : {e : G.Dart // e.toProd.1 = d.toProd.2} :=
      ⟨d.symm, by simp [SimpleGraph.Dart.symm]⟩
    change PolygonalArcTerminalEndpointLeftCone (A.dartArc d) r K ⊆
      (fun z : EuclideanSpace ℝ (Fin 2) =>
        D.vertexPlacement d.toProd.2 +
          z 0 • germDirection d.toProd.2 rev +
            z 1 • PlanarRot90 (germDirection d.toProd.2 rev)) ''
      {z : EuclideanSpace ℝ (Fin 2) |
        0 < z 0 ∧ z 0 ^ 2 + z 1 ^ 2 <
          (r / ‖germDirection d.toProd.2 rev‖) ^ 2 ∧
        -K * z 0 < z 1 ∧ z 1 < 0}
    intro q hq
    let hprev : (A.dartArc d).vertices.length - 2 < (A.dartArc d).vertices.length := by
      have hlen := (A.dartArc d).length_ge_two
      omega
    let raw : EuclideanSpace ℝ (Fin 2) :=
      (A.dartArc d).vertices[(A.dartArc d).vertices.length - 2]'hprev -
        D.vertexPlacement d.toProd.2
    have hrev_index :
        (PolygonalArcReverse (A.dartArc d)).vertices[1]'(Nat.lt_of_succ_le
            (PolygonalArcReverse (A.dartArc d)).length_ge_two) =
          (A.dartArc d).vertices[(A.dartArc d).vertices.length - 2]'hprev := by
      have hidx : (A.dartArc d).vertices.length - 1 - 1 =
          (A.dartArc d).vertices.length - 2 := by
        have hlen := (A.dartArc d).length_ge_two
        omega
      simpa [PolygonalArcReverse, List.length_reverse, hidx] using
        (List.getElem_reverse (l := (A.dartArc d).vertices) (i := 1))
    have hfirst_rev :
        (A.dartArc d.symm).vertices[1]'(Nat.lt_of_succ_le
            (A.dartArc d.symm).length_ge_two) - D.vertexPlacement d.toProd.2 =
          raw := by
      dsimp [raw]
      rw [A.dartArc_symm_eq_reverse d]
      rw [hrev_index]
    have hraw_ne : raw ≠ 0 := by
      intro hzero
      have hgd_zero : germDirection d.toProd.2 rev = 0 := by
        rw [hgermDirection_eq_normalized_first d.toProd.2 rev]
        rw [hfirst_rev]
        simpa [raw] using congrArg ((fun x => (‖x‖)⁻¹ • x)) hzero
      exact hgermDirection_ne_zero d.toProd.2 rev hgd_zero
    have hraw_norm_pos : 0 < ‖raw‖ := norm_pos_iff.mpr hraw_ne
    have hraw_eq : raw = ‖raw‖ • germDirection d.toProd.2 rev := by
      have hgd := hgermDirection_eq_normalized_first d.toProd.2 rev
      rw [hfirst_rev] at hgd
      calc
        raw = ‖raw‖ • ((‖raw‖)⁻¹ • raw) := by
          rw [smul_smul, mul_inv_cancel₀ (ne_of_gt hraw_norm_pos), one_smul]
        _ = ‖raw‖ • germDirection d.toProd.2 rev := by
          exact congrArg (fun x => ‖raw‖ • x) hgd.symm
    unfold PolygonalArcTerminalEndpointLeftCone at hq
    rcases hq with ⟨z, hz, hqeq⟩
    rcases hz with ⟨hz0, hzrad, hz1low, hz1neg⟩
    let w : EuclideanSpace ℝ (Fin 2) := ‖raw‖ • z
    refine ⟨w, ?_, ?_⟩
    · refine ⟨?_, ?_, ?_, ?_⟩
      · dsimp [w]
        simpa [hraw_norm_pos] using hz0
      · have hdist_eq : dist (A.dartArc d).target
              ((A.dartArc d).vertices[(A.dartArc d).vertices.length - 2]'hprev) =
            ‖raw‖ := by
          rw [dist_eq_norm]
          have htarget : (A.dartArc d).target = D.vertexPlacement d.toProd.2 :=
            A.dartArc_target d
          rw [htarget]
          have hnorm_neg :
              ‖D.vertexPlacement d.toProd.2 -
                (A.dartArc d).vertices[(A.dartArc d).vertices.length - 2]'hprev‖ =
                ‖raw‖ := by
            dsimp [raw]
            rw [← norm_neg (D.vertexPlacement d.toProd.2 -
              (A.dartArc d).vertices[(A.dartArc d).vertices.length - 2]'hprev)]
            congr 1
            abel
          exact hnorm_neg
        have hbase_norm : ‖germDirection d.toProd.2 rev‖ = 1 :=
          germDirection_norm_one d.toProd.2 rev
        have hzrad' : z 0 ^ 2 + z 1 ^ 2 < (r / ‖raw‖) ^ 2 := by
          simpa [hdist_eq] using hzrad
        have hraw_sq_pos : 0 < ‖raw‖ ^ 2 := sq_pos_of_pos hraw_norm_pos
        have hwcoord :
            w 0 ^ 2 + w 1 ^ 2 = ‖raw‖ ^ 2 * (z 0 ^ 2 + z 1 ^ 2) := by
          simp [w]
          ring
        have htarget_rad : ‖raw‖ ^ 2 * (z 0 ^ 2 + z 1 ^ 2) < r ^ 2 := by
          have hmul := mul_lt_mul_of_pos_left hzrad' hraw_sq_pos
          have hscale : ‖raw‖ ^ 2 * (r / ‖raw‖) ^ 2 = r ^ 2 := by
            field_simp [ne_of_gt hraw_norm_pos]
          simpa [hscale] using hmul
        have hbase_rhs : (r / ‖germDirection d.toProd.2 rev‖) ^ 2 = r ^ 2 := by
          rw [hbase_norm]
          norm_num
        rw [hwcoord, hbase_rhs]
        exact htarget_rad
      · dsimp [w]
        have hmul := mul_lt_mul_of_pos_left hz1low hraw_norm_pos
        simpa [mul_assoc, mul_comm, mul_left_comm] using hmul
      · dsimp [w]
        have hmul := mul_lt_mul_of_pos_left hz1neg hraw_norm_pos
        simpa using hmul
    · rw [← hqeq]
      have htarget : (A.dartArc d).target = D.vertexPlacement d.toProd.2 :=
        A.dartArc_target d
      rw [htarget]
      dsimp [w]
      change D.vertexPlacement d.toProd.2 +
          (‖raw‖ * z 0) • germDirection d.toProd.2 rev +
            (‖raw‖ * z 1) • PlanarRot90 (germDirection d.toProd.2 rev) =
        D.vertexPlacement d.toProd.2 + z 0 • raw + z 1 • PlanarRot90 raw
      have hrot_scaled :
          PlanarRot90 (‖raw‖ • germDirection d.toProd.2 rev) =
            ‖raw‖ • PlanarRot90 (germDirection d.toProd.2 rev) := by
        apply PiLp.ext
        intro k
        fin_cases k <;> simp [PlanarRot90]
      conv_rhs => rw [hraw_eq, hrot_scaled]
      module
  have positive_ray_in_ball_subset_radialGerm :
      ∀ (v : V) (e : {e : G.Dart // e.toProd.1 = v})
        (q : EuclideanSpace ℝ (Fin 2)),
        q ∈ Metric.ball (D.vertexPlacement v) (localDiskRadius v) →
          q ∈ {q | ∃ t : ℝ, 0 < t ∧
            q = D.vertexPlacement v + t • germDirection v e} →
            q ∈ radialGerm v e := by
    intro v e q hball hray
    rcases hray with ⟨t, ht, hq⟩
    have ht_lt_radius : t < localDiskRadius v := by
      have hdist : dist (D.vertexPlacement v) q < localDiskRadius v := by
        simpa [Metric.mem_ball, dist_comm] using hball
      rw [hq, dist_eq_norm] at hdist
      have hsub :
          D.vertexPlacement v - (D.vertexPlacement v + t • germDirection v e) =
            -t • germDirection v e := by
        module
      rw [hsub, norm_smul, germDirection_norm_one v e, Real.norm_eq_abs,
        mul_one] at hdist
      simpa [abs_neg, abs_of_pos ht] using hdist
    rw [hradialGerm_eq_openSegment v e]
    rw [openSegment_eq_image_lineMap]
    refine ⟨t / localDiskRadius v,
      ⟨div_pos ht (hlocalDiskRadius_pos v),
        (div_lt_one (hlocalDiskRadius_pos v)).2 ht_lt_radius⟩, ?_⟩
    rw [AffineMap.lineMap_apply_module]
    rw [hq]
    have hrad_ne : localDiskRadius v ≠ 0 := ne_of_gt (hlocalDiskRadius_pos v)
    have hscale : (t / localDiskRadius v) * localDiskRadius v = t := by
      field_simp [hrad_ne]
    calc
      (1 - t / localDiskRadius v) • D.vertexPlacement v +
          (t / localDiskRadius v) •
            (D.vertexPlacement v + localDiskRadius v • germDirection v e) =
        D.vertexPlacement v +
          ((t / localDiskRadius v) * localDiskRadius v) • germDirection v e := by
          module
      _ = D.vertexPlacement v + t • germDirection v e := by
          rw [hscale]
  have successorSector_disjoint_radialGerm :
      ∀ (d : G.Dart) (e : {e : G.Dart // e.toProd.1 = d.toProd.2}),
        Disjoint (successorSector d) (radialGerm d.toProd.2 e) := by
    intro d e
    let rev : {e : G.Dart // e.toProd.1 = d.toProd.2} :=
      ⟨d.symm, by simp [SimpleGraph.Dart.symm]⟩
    have hv : Nonempty {e : G.Dart // e.toProd.1 = d.toProd.2} := ⟨rev⟩
    rcases localSector_spec d.toProd.2 hv with
      ⟨_hfull_eq, _hfull_pos, _hturn_pos, _hturn_le, _hturn_full,
        _hfirst_after, _hfixed, _hsector_def, _hopen_connected, _hball,
        hdisjoint, _hcover⟩
    have hdis :
        Disjoint (sector d.toProd.2 rev)
          {q | ∃ t : ℝ, 0 < t ∧
            q = D.vertexPlacement d.toProd.2 +
              t • germDirection d.toProd.2 e} := by
      rw [sector_eq_of_nonempty d.toProd.2 hv]
      exact hdisjoint rev e
    change Disjoint (sector d.toProd.2 rev) (radialGerm d.toProd.2 e)
    exact hdis.mono_right (radialGerm_subset_positive_ray d.toProd.2 e)
  have successorSector_omits_vertex :
      ∀ d : G.Dart, D.vertexPlacement d.toProd.2 ∉ successorSector d := by
    intro d
    let rev : {e : G.Dart // e.toProd.1 = d.toProd.2} :=
      ⟨d.symm, by simp [SimpleGraph.Dart.symm]⟩
    have hv : Nonempty {e : G.Dart // e.toProd.1 = d.toProd.2} := ⟨rev⟩
    rcases localSector_spec d.toProd.2 hv with
      ⟨_hfull_eq, _hfull_pos, _hturn_pos, _hturn_le, _hturn_full,
        _hfirst_after, _hfixed, hsector_def, _hopen_connected, _hball,
        _hdisjoint, _hcover⟩
    change D.vertexPlacement d.toProd.2 ∉ sector d.toProd.2 rev
    rw [sector_eq_of_nonempty d.toProd.2 hv]
    by_cases hfix : (localClockwiseNext d.toProd.2 hv) rev = rev
    · have hdef := hsector_def rev
      simp [hfix] at hdef
      rw [hdef]
      simp
    · have hdef := hsector_def rev
      simp [hfix] at hdef
      rcases hdef with ⟨c, s, _hnot_pos, _hother_eq, hsector_eq⟩
      rw [hsector_eq]
      let base : EuclideanSpace ℝ (Fin 2) := germDirection d.toProd.2 rev
      let baseChart : EuclideanSpace ℝ (Fin 2) →
          EuclideanSpace ℝ (Fin 2) :=
        fun z => D.vertexPlacement d.toProd.2 +
          z 0 • base + z 1 • PlanarRot90 base
      have hbase : base ≠ 0 := by
        dsimp [base]
        exact hgermDirection_ne_zero d.toProd.2 rev
      have hcenter_coords :
          ∀ z : EuclideanSpace ℝ (Fin 2),
            baseChart z = D.vertexPlacement d.toProd.2 →
              z 0 = 0 ∧ z 1 = 0 := by
        intro z hz
        have hrepz :
            baseChart z - D.vertexPlacement d.toProd.2 =
              z 0 • base + z 1 • PlanarRot90 base := by
          dsimp [baseChart]
          abel
        have hrep0 :
            baseChart z - D.vertexPlacement d.toProd.2 =
              (0 : ℝ) • base + (0 : ℝ) • PlanarRot90 base := by
          rw [hz]
          simp
        have hzcoeff :=
          PlanarRot90CoefficientUniqueness (d := base)
            (v := baseChart z - D.vertexPlacement d.toProd.2) hbase hrepz
        have h0coeff :=
          PlanarRot90CoefficientUniqueness (d := base)
            (v := baseChart z - D.vertexPlacement d.toProd.2)
            (a := 0) (b := 0) hbase hrep0
        constructor
        · rw [hzcoeff.1, h0coeff.1]
        · rw [hzcoeff.2, h0coeff.2]
      by_cases hspos : 0 < s
      · simp [hspos]
        rintro z _hdisk hyneg _hlin hz_eq
        have hcoords := hcenter_coords z hz_eq
        linarith [hyneg, hcoords.2]
      · by_cases hsneg : s < 0
        · simp [base, baseChart, hspos, hsneg]
          rintro z _hdisk hside hz_eq
          have hcoords := hcenter_coords z hz_eq
          rcases hside with hyneg | hlin
          · linarith [hyneg, hcoords.2]
          · rw [hcoords.1, hcoords.2] at hlin
            norm_num at hlin
        · simp [base, baseChart, hspos, hsneg]
          rintro z _hdisk hyneg hz_eq
          have hcoords := hcenter_coords z hz_eq
          linarith [hyneg, hcoords.2]
  let C : PlaneDrawingDartVertexSectorGeometry G D A := {
    star := star
    successorSector := successorSector
    successorSector_isOpen := by
      intro d
      exact (successorSector_open_connected d).1
    successorSector_isConnected := by
      intro d
      exact (successorSector_open_connected d).2
    successorSector_subset_localDisk := by
      intro d
      simpa [star] using successorSector_subset_localDisk d
    successorSector_subset_complement := by
      intro d q hq hdraw
      have hball :
          q ∈ Metric.ball (D.vertexPlacement d.toProd.2)
              (localDiskRadius d.toProd.2) :=
        successorSector_subset_localDisk d hq
      have hlocal :
          q ∈ {D.vertexPlacement d.toProd.2} ∪
              ⋃ e : {e : G.Dart // e.toProd.1 = d.toProd.2},
                radialGerm d.toProd.2 e := by
        have hmem :
            q ∈ Metric.ball (D.vertexPlacement d.toProd.2)
                (localDiskRadius d.toProd.2) ∩
              OrdinaryDrawingImage G D := ⟨hball, hdraw⟩
        rwa [hlocalDisk_meets_drawing d.toProd.2] at hmem
      rcases hlocal with hvertex | hradial
      · rcases hvertex with rfl
        exact successorSector_omits_vertex d hq
      · rcases Set.mem_iUnion.mp hradial with ⟨e, hqradial⟩
        exact (successorSector_disjoint_radialGerm d e).notMem_of_mem_left hq hqradial
    successorSector_disjoint_radialGerm := by
      intro d e
      simpa [star] using successorSector_disjoint_radialGerm d e
    terminal_left_endpoint_sector_access := by
      intro d
      let rev : {e : G.Dart // e.toProd.1 = d.toProd.2} :=
        ⟨d.symm, by simp [SimpleGraph.Dart.symm]⟩
      have hv : Nonempty {e : G.Dart // e.toProd.1 = d.toProd.2} := ⟨rev⟩
      rcases localSector_spec d.toProd.2 hv with
        ⟨_hfull_eq, _hfull_pos, _hturn_pos, _hturn_le, _hturn_full,
          _hfirst_after, _hfixed, hsector_def, _hopen_connected, _hball,
          _hdisjoint, _hcover⟩
      by_cases hfix : (localClockwiseNext d.toProd.2 hv) rev = rev
      · have hdef := hsector_def rev
        simp [hfix] at hdef
        rcases
          PlanarSlitDiskEndpointConesAvoidRay
            (p := D.vertexPlacement d.toProd.2)
            (base := germDirection d.toProd.2 rev)
            (rho := localDiskRadius d.toProd.2)
            (hrho := hlocalDiskRadius_pos d.toProd.2)
            (hbase := hgermDirection_ne_zero d.toProd.2 rev) with
        ⟨_hopen, _hconn, r, K, hr, hK, hlower, _hupper⟩
        refine ⟨r, K, hr, hK, ?_⟩
        refine (terminal_left_endpoint_subset_chart d r K hr).trans ?_
        change
          (fun z : EuclideanSpace ℝ (Fin 2) =>
            D.vertexPlacement d.toProd.2 +
              z 0 • germDirection d.toProd.2 rev +
                z 1 • PlanarRot90 (germDirection d.toProd.2 rev)) ''
            {z : EuclideanSpace ℝ (Fin 2) |
              0 < z 0 ∧
                z 0 ^ 2 + z 1 ^ 2 <
                  (r / ‖germDirection d.toProd.2 rev‖) ^ 2 ∧
                -K * z 0 < z 1 ∧ z 1 < 0} ⊆ successorSector d
        dsimp [successorSector]
        change
          (fun z : EuclideanSpace ℝ (Fin 2) =>
            D.vertexPlacement d.toProd.2 +
              z 0 • germDirection d.toProd.2 rev +
                z 1 • PlanarRot90 (germDirection d.toProd.2 rev)) ''
            {z : EuclideanSpace ℝ (Fin 2) |
              0 < z 0 ∧
                z 0 ^ 2 + z 1 ^ 2 <
                  (r / ‖germDirection d.toProd.2 rev‖) ^ 2 ∧
                -K * z 0 < z 1 ∧ z 1 < 0} ⊆ sector d.toProd.2 rev
        rw [sector_eq_of_nonempty d.toProd.2 hv, hdef]
        simpa using hlower
      · have hdef := hsector_def rev
        simp [hfix] at hdef
        rcases hdef with ⟨c, s, hnot_pos, hother_eq, hsector_eq⟩
        rcases
          PlanarClockwiseSweptTwoRayEndpointConesInSector
            (p := D.vertexPlacement d.toProd.2)
            (base := germDirection d.toProd.2 rev)
            (other := germDirection d.toProd.2
              ((localClockwiseNext d.toProd.2 hv) rev))
            (rho := localDiskRadius d.toProd.2)
            (c := c) (s := s)
            (hrho := hlocalDiskRadius_pos d.toProd.2)
            (hbase := hgermDirection_ne_zero d.toProd.2 rev)
            (hother := hgermDirection_ne_zero d.toProd.2
              ((localClockwiseNext d.toProd.2 hv) rev))
            (hnot_pos_ray := hnot_pos)
            (hother_eq := hother_eq) with
        ⟨_hopen, _hconn, r, K, hr, hK, hlower, _hupper⟩
        refine ⟨r, K, hr, hK, ?_⟩
        refine (terminal_left_endpoint_subset_chart d r K hr).trans ?_
        change
          (fun z : EuclideanSpace ℝ (Fin 2) =>
            D.vertexPlacement d.toProd.2 +
              z 0 • germDirection d.toProd.2 rev +
                z 1 • PlanarRot90 (germDirection d.toProd.2 rev)) ''
            {z : EuclideanSpace ℝ (Fin 2) |
              0 < z 0 ∧
                z 0 ^ 2 + z 1 ^ 2 <
                  (r / ‖germDirection d.toProd.2 rev‖) ^ 2 ∧
                -K * z 0 < z 1 ∧ z 1 < 0} ⊆ successorSector d
        dsimp [successorSector]
        change
          (fun z : EuclideanSpace ℝ (Fin 2) =>
            D.vertexPlacement d.toProd.2 +
              z 0 • germDirection d.toProd.2 rev +
                z 1 • PlanarRot90 (germDirection d.toProd.2 rev)) ''
            {z : EuclideanSpace ℝ (Fin 2) |
              0 < z 0 ∧
                z 0 ^ 2 + z 1 ^ 2 <
                  (r / ‖germDirection d.toProd.2 rev‖) ^ 2 ∧
                -K * z 0 < z 1 ∧ z 1 < 0} ⊆ sector d.toProd.2 rev
        rw [sector_eq_of_nonempty d.toProd.2 hv, hsector_eq]
        simpa using hlower
    successor_initial_left_endpoint_sector_access := by
      intro d
      let rev : {e : G.Dart // e.toProd.1 = d.toProd.2} :=
        ⟨d.symm, by simp [SimpleGraph.Dart.symm]⟩
      have hv : Nonempty {e : G.Dart // e.toProd.1 = d.toProd.2} := ⟨rev⟩
      rcases localSector_spec d.toProd.2 hv with
        ⟨_hfull_eq, _hfull_pos, _hturn_pos, _hturn_le, _hturn_full,
          _hfirst_after, _hfixed, hsector_def, _hopen_connected, _hball,
          _hdisjoint, _hcover⟩
      by_cases hfix : (localClockwiseNext d.toProd.2 hv) rev = rev
      · have hdef := hsector_def rev
        simp [hfix] at hdef
        rcases
          PlanarSlitDiskEndpointConesAvoidRay
            (p := D.vertexPlacement d.toProd.2)
            (base := germDirection d.toProd.2 rev)
            (rho := localDiskRadius d.toProd.2)
            (hrho := hlocalDiskRadius_pos d.toProd.2)
            (hbase := hgermDirection_ne_zero d.toProd.2 rev) with
        ⟨_hopen, _hconn, r, K, hr, hK, _hlower, hupper⟩
        have hsucc_eq_symm : successor d = d.symm := by
          calc
            successor d = (clockwiseNext d.toProd.2 rev).1 := by
              simpa [rev] using hsuccessor_eq_clockwiseNext d
            _ = ((localClockwiseNext d.toProd.2 hv) rev).1 := by
              rw [clockwiseNext_eq_of_nonempty d.toProd.2 hv]
            _ = d.symm := by
              have hval := congrArg Subtype.val hfix
              simpa [rev] using hval
        refine ⟨r, K, hr, hK, ?_⟩
        change PolygonalArcInitialEndpointLeftCone (A.dartArc (successor d)) r K ⊆
          successorSector d
        rw [hsucc_eq_symm]
        refine (initial_left_endpoint_subset_chart d.toProd.2 rev r K hr).trans ?_
        change
          (fun z : EuclideanSpace ℝ (Fin 2) =>
            D.vertexPlacement d.toProd.2 +
              z 0 • germDirection d.toProd.2 rev +
                z 1 • PlanarRot90 (germDirection d.toProd.2 rev)) ''
            {z : EuclideanSpace ℝ (Fin 2) |
              0 < z 0 ∧
                z 0 ^ 2 + z 1 ^ 2 <
                  (r / ‖germDirection d.toProd.2 rev‖) ^ 2 ∧
                0 < z 1 ∧ z 1 < K * z 0} ⊆ successorSector d
        dsimp [successorSector]
        change
          (fun z : EuclideanSpace ℝ (Fin 2) =>
            D.vertexPlacement d.toProd.2 +
              z 0 • germDirection d.toProd.2 rev +
                z 1 • PlanarRot90 (germDirection d.toProd.2 rev)) ''
            {z : EuclideanSpace ℝ (Fin 2) |
              0 < z 0 ∧
                z 0 ^ 2 + z 1 ^ 2 <
                  (r / ‖germDirection d.toProd.2 rev‖) ^ 2 ∧
                0 < z 1 ∧ z 1 < K * z 0} ⊆ sector d.toProd.2 rev
        rw [sector_eq_of_nonempty d.toProd.2 hv, hdef]
        simpa using hupper
      · have hdef := hsector_def rev
        simp [hfix] at hdef
        rcases hdef with ⟨c, s, hnot_pos, hother_eq, hsector_eq⟩
        rcases
          PlanarClockwiseSweptTwoRayEndpointConesInSector
            (p := D.vertexPlacement d.toProd.2)
            (base := germDirection d.toProd.2 rev)
            (other := germDirection d.toProd.2
              ((localClockwiseNext d.toProd.2 hv) rev))
            (rho := localDiskRadius d.toProd.2)
            (c := c) (s := s)
            (hrho := hlocalDiskRadius_pos d.toProd.2)
            (hbase := hgermDirection_ne_zero d.toProd.2 rev)
            (hother := hgermDirection_ne_zero d.toProd.2
              ((localClockwiseNext d.toProd.2 hv) rev))
            (hnot_pos_ray := hnot_pos)
            (hother_eq := hother_eq) with
        ⟨_hopen, _hconn, r, K, hr, hK, _hlower, hupper⟩
        let nxt : {e : G.Dart // e.toProd.1 = d.toProd.2} :=
          ⟨successor d, hsuccessor_tail d⟩
        have hnxt_eq :
            nxt = (localClockwiseNext d.toProd.2 hv rev) := by
          apply Subtype.ext
          dsimp [nxt]
          calc
            successor d = (clockwiseNext d.toProd.2 rev).1 := by
              simpa [rev] using hsuccessor_eq_clockwiseNext d
            _ = ((localClockwiseNext d.toProd.2 hv) rev).1 := by
              rw [clockwiseNext_eq_of_nonempty d.toProd.2 hv]
        refine ⟨r, K, hr, hK, ?_⟩
        change PolygonalArcInitialEndpointLeftCone (A.dartArc (successor d)) r K ⊆
          successorSector d
        refine (initial_left_endpoint_subset_chart d.toProd.2 nxt r K hr).trans ?_
        change
          (fun z : EuclideanSpace ℝ (Fin 2) =>
            D.vertexPlacement d.toProd.2 +
              z 0 • germDirection d.toProd.2 nxt +
                z 1 • PlanarRot90 (germDirection d.toProd.2 nxt)) ''
            {z : EuclideanSpace ℝ (Fin 2) |
              0 < z 0 ∧
                z 0 ^ 2 + z 1 ^ 2 <
                  (r / ‖germDirection d.toProd.2 nxt‖) ^ 2 ∧
                0 < z 1 ∧ z 1 < K * z 0} ⊆ successorSector d
        rw [hnxt_eq]
        dsimp [successorSector]
        change
          (fun z : EuclideanSpace ℝ (Fin 2) =>
            D.vertexPlacement d.toProd.2 +
              z 0 • germDirection d.toProd.2
                  ((localClockwiseNext d.toProd.2 hv) rev) +
                z 1 • PlanarRot90
                  (germDirection d.toProd.2
                    ((localClockwiseNext d.toProd.2 hv) rev))) ''
            {z : EuclideanSpace ℝ (Fin 2) |
              0 < z 0 ∧
                z 0 ^ 2 + z 1 ^ 2 <
                  (r / ‖germDirection d.toProd.2
                    ((localClockwiseNext d.toProd.2 hv) rev)‖) ^ 2 ∧
                0 < z 1 ∧ z 1 < K * z 0} ⊆ sector d.toProd.2 rev
        rw [sector_eq_of_nonempty d.toProd.2 hv, hsector_eq]
        simpa using hupper
    vertex_sector_coverage := by
      intro v y hdhead hyball hyne hycompl
      rcases hdhead with ⟨d0, hd0_head⟩
      let out0 : {e : G.Dart // e.toProd.1 = v} :=
        ⟨d0.symm, by simpa [SimpleGraph.Dart.symm, hd0_head]⟩
      have hv : Nonempty {e : G.Dart // e.toProd.1 = v} := ⟨out0⟩
      rcases localSector_spec v hv with
        ⟨_hfull_eq, _hfull_pos, _hturn_pos, _hturn_le, _hturn_full,
          _hfirst_after, _hfixed, _hsector_def, _hopen_connected, _hball,
          _hdisjoint, hcover⟩
      have hnot_ray :
          ∀ i : {e : G.Dart // e.toProd.1 = v},
            y ∉ {x | ∃ t : ℝ, 0 < t ∧
              x = D.vertexPlacement v + t • germDirection v i} := by
        intro i hiray
        have hyrad :
            y ∈ radialGerm v i :=
          positive_ray_in_ball_subset_radialGerm v i y hyball hiray
        have hy_union :
            y ∈ ⋃ i : {e : G.Dart // e.toProd.1 = v}, radialGerm v i :=
          Set.mem_iUnion.mpr ⟨i, hyrad⟩
        have hydrawing :
            y ∈ OrdinaryDrawingImage G D := by
          have hy_inter :
              y ∈ Metric.ball (D.vertexPlacement v) (localDiskRadius v) ∩
                  OrdinaryDrawingImage G D := by
            rw [hlocalDisk_meets_drawing v]
            exact Or.inr hy_union
          exact hy_inter.2
        exact hycompl hydrawing
      rcases hcover y hyball hyne hnot_ray with ⟨i, hysector⟩
      rcases i with ⟨dart, hdart_tail⟩
      cases hdart_tail
      refine ⟨dart.symm, by simp [SimpleGraph.Dart.symm], ?_⟩
      have hy_global : y ∈ sector dart.toProd.1 ⟨dart, rfl⟩ := by
        rw [sector_eq_of_nonempty dart.toProd.1 hv]
        simpa using hysector
      simpa [successorSector, SimpleGraph.Dart.symm] using hy_global }
  refine ⟨C, ?_⟩
  intro d
  let rev : {e : G.Dart // e.toProd.1 = d.toProd.2} :=
    ⟨d.symm, by simp [SimpleGraph.Dart.symm]⟩
  let nxt : {e : G.Dart // e.toProd.1 = d.toProd.2} :=
    ⟨C.star.successor d, C.star.successor_tail d⟩
  have hv : Nonempty {e : G.Dart // e.toProd.1 = d.toProd.2} := ⟨rev⟩
  rcases localSector_spec d.toProd.2 hv with
    ⟨_hfull_eq, _hfull_pos, _hturn_pos, _hturn_le, _hturn_full,
      _hfirst_after, hfixed, hsector_def, _hopen_connected, _hball,
      _hdisjoint, _hcover⟩
  have hnxt_eq :
      nxt = (localClockwiseNext d.toProd.2 hv rev) := by
    apply Subtype.ext
    dsimp [nxt, C, star]
    calc
      successor d = (clockwiseNext d.toProd.2 rev).1 := by
        simpa [rev] using hsuccessor_eq_clockwiseNext d
      _ = (localClockwiseNext d.toProd.2 hv rev).1 := by
        rw [clockwiseNext_eq_of_nonempty d.toProd.2 hv]
  by_cases hfix : (localClockwiseNext d.toProd.2 hv) rev = rev
  · left
    constructor
    · intro e
      exact (hfixed rev).1 hfix e
    · have hdef := hsector_def rev
      simp [hfix] at hdef
      dsimp [C, successorSector, star]
      change sector d.toProd.2 rev =
        Metric.ball (D.vertexPlacement d.toProd.2) (localDiskRadius d.toProd.2) \
          ({q | ∃ t : ℝ, 0 < t ∧
            q = D.vertexPlacement d.toProd.2 + t • germDirection d.toProd.2 rev} ∪
            ({D.vertexPlacement d.toProd.2} :
              Set (EuclideanSpace ℝ (Fin 2))))
      rw [sector_eq_of_nonempty d.toProd.2 hv]
      simpa using hdef
  · right
    have hdef := hsector_def rev
    simp [hfix] at hdef
    rcases hdef with ⟨c, s, hnot_pos, hother_eq, hsector_eq⟩
    refine ⟨c, s, hnot_pos, ?_, ?_⟩
    · change germDirection d.toProd.2 nxt =
        c • germDirection d.toProd.2 rev -
          s • PlanarRot90 (germDirection d.toProd.2 rev)
      rw [hnxt_eq]
      exact hother_eq
    · dsimp [C, successorSector, star]
      change sector d.toProd.2 rev =
        (let base : EuclideanSpace ℝ (Fin 2) := germDirection d.toProd.2 rev
         let baseChart : EuclideanSpace ℝ (Fin 2) →
            EuclideanSpace ℝ (Fin 2) :=
          fun z => D.vertexPlacement d.toProd.2 +
            z 0 • base + z 1 • PlanarRot90 base
         if 0 < s then
           baseChart ''
            {z : EuclideanSpace ℝ (Fin 2) |
              z 0 ^ 2 + z 1 ^ 2 <
                (localDiskRadius d.toProd.2 / ‖base‖) ^ 2 ∧
              z 1 < 0 ∧ 0 < c * z 1 + s * z 0}
         else if s < 0 then
           baseChart ''
            {z : EuclideanSpace ℝ (Fin 2) |
              z 0 ^ 2 + z 1 ^ 2 <
                (localDiskRadius d.toProd.2 / ‖base‖) ^ 2 ∧
              (z 1 < 0 ∨ 0 < c * z 1 + s * z 0)}
         else
           baseChart ''
            {z : EuclideanSpace ℝ (Fin 2) |
              z 0 ^ 2 + z 1 ^ 2 <
                (localDiskRadius d.toProd.2 / ‖base‖) ^ 2 ∧
              z 1 < 0})
      rw [sector_eq_of_nonempty d.toProd.2 hv]
      exact hsector_eq
