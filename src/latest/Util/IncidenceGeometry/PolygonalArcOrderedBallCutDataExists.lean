import Util.IncidenceGeometry.PolygonalArcOrderedBallCutData
import Util.IncidenceGeometry.PolygonalArcFirstBallCutDataExists
import Util.IncidenceGeometry.PolygonalArcVertexMemCarrier
import Mathlib.Tactic

open Classical
noncomputable section

lemma PolygonalArcOrderedBallCutDataExists
    (Q : PolygonalArc)
    (p : EuclideanSpace ℝ (Fin 2)) (radius : ℝ) :
    Q.source ∉ Metric.closedBall p radius →
      Q.target ∉ Metric.closedBall p radius →
      (Q.carrier ∩ Metric.ball p radius).Nonempty →
      Nonempty (PolygonalArcOrderedBallCutData Q p radius) := by
  intro hsource htarget hhit
  have hhitRel : (Q.relativeInterior ∩ Metric.ball p radius).Nonempty := by
    rcases hhit with ⟨z, hzQ, hzBall⟩
    refine ⟨z, ?_, hzBall⟩
    rw [Q.relativeInterior_eq]
    refine ⟨hzQ, ?_⟩
    have hzSource : z ≠ Q.source := by
      intro hEq
      subst z
      exact hsource (Metric.ball_subset_closedBall hzBall)
    have hzTarget : z ≠ Q.target := by
      intro hEq
      subst z
      exact htarget (Metric.ball_subset_closedBall hzBall)
    simpa only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or] using
      And.intro hzSource hzTarget
  obtain ⟨A⟩ := PolygonalArcFirstBallCutDataExists Q p radius hsource
    (fun h => htarget (Metric.ball_subset_closedBall h)) hhitRel
  let R := PolygonalArcReverse A.cut.suffixArc
  have hRsource : R.source = Q.target := by
    dsimp [R, PolygonalArcReverse]
    exact A.cut.suffix_target
  have hRtarget : R.target = A.gate := by
    dsimp [R, PolygonalArcReverse]
    exact A.cut.suffix_source
  have hRsourceOutside : R.source ∉ Metric.closedBall p radius := by
    rw [hRsource]
    exact htarget
  have hRtargetOutsideOpen : R.target ∉ Metric.ball p radius := by
    rw [hRtarget]
    intro hball
    have hsphere := A.gate_mem_sphere
    rw [Metric.mem_sphere] at hsphere
    rw [Metric.mem_ball] at hball
    linarith
  have hRhit : (R.relativeInterior ∩ Metric.ball p radius).Nonempty := by
    rcases hhit with ⟨z, hzQ, hzBall⟩
    refine ⟨z, ?_, hzBall⟩
    have hzS := A.ball_part_in_suffix ⟨hzQ, hzBall⟩
    simpa [R, PolygonalArcReverse] using hzS
  obtain ⟨B⟩ := PolygonalArcFirstBallCutDataExists R p radius
    hRsourceOutside hRtargetOutsideOpen hRhit
  let P := A.cut.prefixArc
  let M := PolygonalArcReverse B.cut.suffixArc
  let S := PolygonalArcReverse B.cut.prefixArc
  have hsourceMem : ∀ (T : PolygonalArc), T.source ∈ T.carrier := by
    intro T
    have hlen := T.length_ge_two
    apply PolygonalArcVertexMemCarrier T
    have hhead := T.source_eq_head
    rw [List.head?_eq_getElem?] at hhead
    rw [List.getElem?_eq_getElem (by omega)] at hhead
    have := Option.some.inj hhead
    rw [← this]
    exact List.getElem_mem (by omega)
  have htargetMem : ∀ (T : PolygonalArc), T.target ∈ T.carrier := by
    intro T
    have hlen := T.length_ge_two
    apply PolygonalArcVertexMemCarrier T
    have hlast := T.target_eq_last
    rw [List.getLast?_eq_getLast_of_ne_nil (by
      exact List.ne_nil_of_length_pos (by omega))] at hlast
    have hget : T.vertices.getLast (by
        exact List.ne_nil_of_length_pos (by omega)) = T.target :=
      Option.some.inj hlast
    rw [← hget]
    exact List.getLast_mem (by exact List.ne_nil_of_length_pos (by omega))
  have hgateNe : A.gate ≠ B.gate := by
    intro hEq
    have hBrel := B.gate_mem_relativeInterior
    rw [R.relativeInterior_eq] at hBrel
    have hnotTarget := hBrel.2
    apply hnotTarget
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
    right
    exact hEq.symm.trans hRtarget.symm
  have hBcarrierS1 : B.gate ∈ A.cut.suffixArc.carrier := by
    have := B.gate_mem_relativeInterior
    rw [R.relativeInterior_eq] at this
    exact this.1
  have hBneQtarget : B.gate ≠ Q.target := by
    have hBrel := B.gate_mem_relativeInterior
    rw [R.relativeInterior_eq] at hBrel
    intro hEq
    apply hBrel.2
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
    left
    exact hEq.trans hRsource.symm
  have hBneQsource : B.gate ≠ Q.source := by
    intro hEq
    have hzP : B.gate ∈ A.cut.prefixArc.carrier := by
      rw [hEq]
      rw [← A.cut.prefix_source]
      exact hsourceMem A.cut.prefixArc
    have hzBoth : B.gate ∈ A.cut.prefixArc.carrier ∩
        A.cut.suffixArc.carrier := ⟨hzP, hBcarrierS1⟩
    rw [A.cut.carrier_intersection] at hzBoth
    have : B.gate = A.gate := by simpa using hzBoth
    exact hgateNe this.symm
  have hBrelQ : B.gate ∈ Q.relativeInterior := by
    rw [Q.relativeInterior_eq]
    refine ⟨A.cut.suffix_carrier_subset hBcarrierS1, ?_⟩
    simpa only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or] using
      And.intro hBneQsource hBneQtarget
  have hBclosureQ : B.gate ∈ closure (Q.carrier ∩ Metric.ball p radius) := by
    apply closure_mono (s := R.carrier ∩ Metric.ball p radius)
    · intro z hz
      exact ⟨A.cut.suffix_carrier_subset hz.1, hz.2⟩
    · exact B.gate_mem_closure_ball_part
  have hcarrierDecomp : Q.carrier = P.carrier ∪ M.carrier ∪ S.carrier := by
    dsimp [P, M, S, PolygonalArcReverse]
    rw [A.cut.carrier_decomposition]
    have hBdecomp := B.cut.carrier_decomposition
    change A.cut.suffixArc.carrier =
      B.cut.prefixArc.carrier ∪ B.cut.suffixArc.carrier at hBdecomp
    rw [hBdecomp]
    ext z
    simp only [Set.mem_union]
    tauto
  have hPMinter : P.carrier ∩ M.carrier = {A.gate} := by
    ext z
    constructor
    · rintro ⟨hzP, hzM⟩
      have hzM' : z ∈ B.cut.suffixArc.carrier := by
        simpa [M, PolygonalArcReverse] using hzM
      have hzBoth : z ∈ A.cut.prefixArc.carrier ∩
          A.cut.suffixArc.carrier :=
        ⟨hzP, B.cut.suffix_carrier_subset hzM'⟩
      rw [A.cut.carrier_intersection] at hzBoth
      exact hzBoth
    · intro hz
      have hzEq : z = A.gate := by simpa using hz
      subst z
      constructor
      · rw [← A.cut.prefix_target]
        exact htargetMem A.cut.prefixArc
      · dsimp [M, PolygonalArcReverse]
        have htargetB : B.cut.suffixArc.target = A.gate :=
          B.cut.suffix_target.trans hRtarget
        rw [← htargetB]
        exact htargetMem B.cut.suffixArc
  have hMSinter : M.carrier ∩ S.carrier = {B.gate} := by
    dsimp [M, S, PolygonalArcReverse]
    rw [Set.inter_comm]
    exact B.cut.carrier_intersection
  have hPSdisjoint : Disjoint P.carrier S.carrier := by
    rw [Set.disjoint_left]
    intro z hzP hzS
    have hzS1 : z ∈ A.cut.suffixArc.carrier := by
      exact B.cut.prefix_carrier_subset hzS
    have hzBoth : z ∈ A.cut.prefixArc.carrier ∩
        A.cut.suffixArc.carrier := ⟨hzP, hzS1⟩
    rw [A.cut.carrier_intersection] at hzBoth
    have hzGate : z = A.gate := by simpa using hzBoth
    have hAgateBPrefix : A.gate ∈ B.cut.prefixArc.carrier := hzGate ▸ hzS
    have hAgateBSuffix : A.gate ∈ B.cut.suffixArc.carrier := by
      have htargetB : B.cut.suffixArc.target = A.gate :=
        B.cut.suffix_target.trans hRtarget
      rw [← htargetB]
      exact htargetMem B.cut.suffixArc
    have hBboth : A.gate ∈ B.cut.prefixArc.carrier ∩
        B.cut.suffixArc.carrier := ⟨hAgateBPrefix, hAgateBSuffix⟩
    rw [B.cut.carrier_intersection] at hBboth
    have : A.gate = B.gate := by simpa using hBboth
    exact hgateNe this
  have hballMiddle : Q.carrier ∩ Metric.ball p radius ⊆ M.relativeInterior := by
    intro z hz
    have hzS1 := A.ball_part_in_suffix hz
    have hzS1carrier : z ∈ A.cut.suffixArc.carrier := by
      rw [A.cut.suffixArc.relativeInterior_eq] at hzS1
      exact hzS1.1
    have hzR : z ∈ R.carrier ∩ Metric.ball p radius := by
      exact ⟨hzS1carrier, hz.2⟩
    have hzB := B.ball_part_in_suffix hzR
    simpa [M, PolygonalArcReverse] using hzB
  have hmiddleMeets : (M.relativeInterior ∩ Metric.ball p radius).Nonempty := by
    rcases hhit with ⟨z, hzQ, hzBall⟩
    exact ⟨z, hballMiddle ⟨hzQ, hzBall⟩, hzBall⟩
  refine ⟨{
    qminus := A.gate
    qplus := B.gate
    prefixArc := P
    middleArc := M
    suffixArc := S
    qminus_ne_qplus := hgateNe
    qminus_mem_relativeInterior := A.gate_mem_relativeInterior
    qplus_mem_relativeInterior := hBrelQ
    qminus_mem_sphere := A.gate_mem_sphere
    qplus_mem_sphere := B.gate_mem_sphere
    qminus_mem_closure_ball_part := A.gate_mem_closure_ball_part
    qplus_mem_closure_ball_part := hBclosureQ
    source_not_mem_closedBall := hsource
    target_not_mem_closedBall := htarget
    prefix_source := A.cut.prefix_source
    prefix_target := A.cut.prefix_target
    middle_source := by
      dsimp [M, PolygonalArcReverse]
      exact B.cut.suffix_target.trans hRtarget
    middle_target := by
      dsimp [M, PolygonalArcReverse]
      exact B.cut.suffix_source
    suffix_source := by
      dsimp [S, PolygonalArcReverse]
      exact B.cut.prefix_target
    suffix_target := by
      dsimp [S, PolygonalArcReverse]
      exact B.cut.prefix_source.trans hRsource
    prefix_carrier_subset := A.cut.prefix_carrier_subset
    middle_carrier_subset := fun z hz =>
      A.cut.suffix_carrier_subset (B.cut.suffix_carrier_subset hz)
    suffix_carrier_subset := fun z hz =>
      A.cut.suffix_carrier_subset (B.cut.prefix_carrier_subset hz)
    carrier_decomposition := hcarrierDecomp
    prefix_middle_intersection := hPMinter
    middle_suffix_intersection := hMSinter
    prefix_suffix_disjoint := hPSdisjoint
    prefix_avoids_ball := A.prefix_avoids_ball
    suffix_avoids_ball := by
      simpa [S, PolygonalArcReverse] using B.prefix_avoids_ball
    ball_part_in_middle := hballMiddle
    middle_meets_ball := hmiddleMeets
    prefix_segment_transfer := ?_
    suffix_segment_transfer := ?_
    protected_first_vertices := ?_ }⟩
  · intro z i hi hzOpen hzP hzOutside
    have hzP' : z ∈ A.cut.prefixArc.carrier := by
      simpa [P] using hzP
    have hgateClosed : A.gate ∈ Metric.closedBall p radius := by
      rw [Metric.mem_closedBall]
      have hs := A.gate_mem_sphere
      rw [Metric.mem_sphere] at hs
      exact hs.le
    have hzGate : z ≠ A.gate := by
      intro hEq
      subst z
      exact hzOutside hgateClosed
    exact A.cut.prefix_segment_transfer z i hi hzOpen hzP' hzGate
  · intro z i hi hzOpen hzS hzOutside
    have hzBPrefix : z ∈ B.cut.prefixArc.carrier := by
      simpa [S, PolygonalArcReverse] using hzS
    have hzS1 : z ∈ A.cut.suffixArc.carrier := by
      exact B.cut.prefix_carrier_subset hzBPrefix
    have hAgateClosed : A.gate ∈ Metric.closedBall p radius := by
      rw [Metric.mem_closedBall]
      have hs := A.gate_mem_sphere
      rw [Metric.mem_sphere] at hs
      exact hs.le
    have hzAgate : z ≠ A.gate := by
      intro hEq
      subst z
      exact hzOutside hAgateClosed
    obtain ⟨j, hj, hzS1Open, c₁, hc₁, hdir₁⟩ :=
      A.cut.suffix_segment_transfer z i hi hzOpen hzS1 hzAgate
    let rj := A.cut.suffixArc.vertices.length - 2 - j
    have hrj : rj + 1 <
        (PolygonalArcReverse A.cut.suffixArc).vertices.length := by
      dsimp [rj, PolygonalArcReverse]
      simp
      omega
    have hrjLeft :
        (PolygonalArcReverse A.cut.suffixArc).vertices[rj] =
          A.cut.suffixArc.vertices[j + 1] := by
      have hrj0 : rj < A.cut.suffixArc.vertices.reverse.length := by
        simpa only [PolygonalArcReverse, List.length_reverse] using
          Nat.lt_of_succ_lt hrj
      change A.cut.suffixArc.vertices.reverse[rj]'hrj0 =
        A.cut.suffixArc.vertices[j + 1]
      rw [List.getElem_reverse hrj0]
      congr 1
      dsimp [rj]
      omega
    have hrjRight :
        (PolygonalArcReverse A.cut.suffixArc).vertices[rj + 1] =
          A.cut.suffixArc.vertices[j] := by
      have hrj1 : rj + 1 < A.cut.suffixArc.vertices.reverse.length := by
        simpa only [PolygonalArcReverse, List.length_reverse] using hrj
      change A.cut.suffixArc.vertices.reverse[rj + 1]'hrj1 =
        A.cut.suffixArc.vertices[j]
      rw [List.getElem_reverse hrj1]
      congr 1
      dsimp [rj]
      omega
    have hzROpen : z ∈ openSegment ℝ
        (PolygonalArcReverse A.cut.suffixArc).vertices[rj]
        (PolygonalArcReverse A.cut.suffixArc).vertices[rj + 1] := by
      simpa [hrjLeft, hrjRight, openSegment_symm ℝ] using hzS1Open
    have hRdir :
        (PolygonalArcReverse A.cut.suffixArc).vertices[rj + 1] -
            (PolygonalArcReverse A.cut.suffixArc).vertices[rj] =
          -(A.cut.suffixArc.vertices[j + 1] -
            A.cut.suffixArc.vertices[j]) := by
      rw [hrjLeft, hrjRight]
      module
    have hzROpen' : z ∈ openSegment ℝ R.vertices[rj] R.vertices[rj + 1] := by
      simpa [R] using hzROpen
    have hBgateClosed : B.gate ∈ Metric.closedBall p radius := by
      rw [Metric.mem_closedBall]
      have hs := B.gate_mem_sphere
      rw [Metric.mem_sphere] at hs
      exact hs.le
    have hzBgate : z ≠ B.gate := by
      intro hEq
      subst z
      exact hzOutside hBgateClosed
    obtain ⟨k, hk, hzBOpen, c₂, hc₂, hdir₂⟩ :=
      B.cut.prefix_segment_transfer z rj hrj hzROpen' hzBPrefix hzBgate
    let rk := B.cut.prefixArc.vertices.length - 2 - k
    have hrk : rk + 1 <
        (PolygonalArcReverse B.cut.prefixArc).vertices.length := by
      dsimp [rk, PolygonalArcReverse]
      simp
      omega
    have hrkLeft :
        (PolygonalArcReverse B.cut.prefixArc).vertices[rk] =
          B.cut.prefixArc.vertices[k + 1] := by
      have hrk0 : rk < B.cut.prefixArc.vertices.reverse.length := by
        simpa only [PolygonalArcReverse, List.length_reverse] using
          Nat.lt_of_succ_lt hrk
      change B.cut.prefixArc.vertices.reverse[rk]'hrk0 =
        B.cut.prefixArc.vertices[k + 1]
      rw [List.getElem_reverse hrk0]
      congr 1
      dsimp [rk]
      omega
    have hrkRight :
        (PolygonalArcReverse B.cut.prefixArc).vertices[rk + 1] =
          B.cut.prefixArc.vertices[k] := by
      have hrk1 : rk + 1 < B.cut.prefixArc.vertices.reverse.length := by
        simpa only [PolygonalArcReverse, List.length_reverse] using hrk
      change B.cut.prefixArc.vertices.reverse[rk + 1]'hrk1 =
        B.cut.prefixArc.vertices[k]
      rw [List.getElem_reverse hrk1]
      congr 1
      dsimp [rk]
      omega
    have hzFinalOpen : z ∈ openSegment ℝ
        (PolygonalArcReverse B.cut.prefixArc).vertices[rk]
        (PolygonalArcReverse B.cut.prefixArc).vertices[rk + 1] := by
      simpa [hrkLeft, hrkRight, openSegment_symm ℝ] using hzBOpen
    have hFinalDir :
        (PolygonalArcReverse B.cut.prefixArc).vertices[rk + 1] -
            (PolygonalArcReverse B.cut.prefixArc).vertices[rk] =
          -(B.cut.prefixArc.vertices[k + 1] -
            B.cut.prefixArc.vertices[k]) := by
      rw [hrkLeft, hrkRight]
      module
    refine ⟨rk, ?_, ?_, c₂ * c₁, mul_ne_zero hc₂ hc₁, ?_⟩
    · simpa [S] using hrk
    · simpa [S] using hzFinalOpen
    · have hRdir' : R.vertices[rj + 1] - R.vertices[rj] =
          -(A.cut.suffixArc.vertices[j + 1] - A.cut.suffixArc.vertices[j]) := by
        simpa [R] using hRdir
      have hFinalDir' : S.vertices[rk + 1] - S.vertices[rk] =
          -(B.cut.prefixArc.vertices[k + 1] - B.cut.prefixArc.vertices[k]) := by
        simpa [S] using hFinalDir
      rw [hFinalDir', hdir₂, hRdir', hdir₁]
      module
  · intro hi hfirst
    apply A.cut.protected_first_vertices hi
    intro hgateSeg
    have hgateClosed : A.gate ∈ Metric.closedBall p radius := by
      rw [Metric.mem_closedBall]
      have hs := A.gate_mem_sphere
      rw [Metric.mem_sphere] at hs
      exact hs.le
    exact Set.disjoint_left.mp hfirst hgateSeg hgateClosed
