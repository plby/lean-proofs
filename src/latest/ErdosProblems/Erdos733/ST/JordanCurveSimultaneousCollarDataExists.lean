import ErdosProblems.Erdos733.ST.JordanCurveSimultaneousCollarData
import ErdosProblems.Erdos733.ST.SimpleClosedCurveAsFinitePolygonalSet
import ErdosProblems.Erdos733.ST.PlanarClockwiseSweptTwoRayEndpointConesInSector
import ErdosProblems.Erdos733.ST.PolygonalArcCarrierCompact
import ErdosProblems.Erdos733.ST.PolygonalArcCollarCompatibleOrientedTubeDataExistsBelow
import ErdosProblems.Erdos733.ST.PolygonalArcCollarControlRadiiExistsBelow
import ErdosProblems.Erdos733.ST.PolygonalArcCollarLocalSideDataExistsWithEndpointLeftCones
import ErdosProblems.Erdos733.ST.PolygonalArcCollarMiddleForbiddenMarginsExists
import ErdosProblems.Erdos733.ST.PolygonalArcCollarMiddleSegmentDataExists
import ErdosProblems.Erdos733.ST.PolygonalArcEndpointIsolationExists
import ErdosProblems.Erdos733.ST.PolygonalArcEndpointLeftHalfTubeSubsetLeftCones
import ErdosProblems.Erdos733.ST.PolygonalArcInteriorTwoRaySectorChartTransport
import ErdosProblems.Erdos733.ST.PolygonalArcSideStripAssembly
import ErdosProblems.Erdos733.ST.PositiveSeparation

open Classical
noncomputable section

private lemma twoRay_coefficient_sq_sum_pos {c s : ℝ}
    (hpos : 0 < s ∨ s = 0 ∧ c < 0) :
    0 < c ^ 2 + s ^ 2 := by
  rcases hpos with hs | ⟨hs, hc⟩
  · exact add_pos_of_nonneg_of_pos (sq_nonneg c) (sq_pos_of_pos hs)
  · simpa [hs] using sq_pos_of_neg hc

private lemma rotated_cross_pos (c s x y : ℝ)
    (hcoeff : 0 < c ^ 2 + s ^ 2) (hy : 0 < y) :
    0 < c * (x * s + y * c) - s * (x * c - y * s) := by
  calc
    0 < (c ^ 2 + s ^ 2) * y := mul_pos hcoeff hy
    _ = c * (x * s + y * c) - s * (x * c - y * s) := by ring

private lemma rotated_cross_neg (c s x y : ℝ)
    (hcoeff : 0 < c ^ 2 + s ^ 2) (hy : y < 0) :
    c * (x * s + y * c) - s * (x * c - y * s) < 0 := by
  calc
    c * (x * s + y * c) - s * (x * c - y * s) =
        (c ^ 2 + s ^ 2) * y := by ring
    _ < 0 := mul_neg_of_pos_of_neg hcoeff hy

private lemma polygonalArc_terminal_dist_eq_norm_direction
    (Q : PolygonalArc) :
    dist Q.target
        (Q.vertices[Q.vertices.length - 2]'(by
          have hlen := Q.length_ge_two
          omega)) =
      ‖(Q.vertices[Q.vertices.length - 2]'(by
          have hlen := Q.length_ge_two
          omega)) - Q.target‖ := by
  rw [dist_eq_norm]
  have hneg : Q.target - (Q.vertices[Q.vertices.length - 2]'(by
        have hlen := Q.length_ge_two
        omega)) =
      -((Q.vertices[Q.vertices.length - 2]'(by
          have hlen := Q.length_ge_two
          omega)) - Q.target) := by
    abel
  rw [hneg, norm_neg]

private lemma polygonalArc_initial_dist_eq_norm_direction
    (Q : PolygonalArc) :
    dist Q.source
        (Q.vertices[1]'(Nat.lt_of_succ_le Q.length_ge_two)) =
      ‖(Q.vertices[1]'(Nat.lt_of_succ_le Q.length_ge_two)) - Q.source‖ := by
  rw [dist_eq_norm]
  have hneg : Q.source -
      (Q.vertices[1]'(Nat.lt_of_succ_le Q.length_ge_two)) =
      -((Q.vertices[1]'(Nat.lt_of_succ_le Q.length_ge_two)) - Q.source) := by
    abel
  rw [hneg, norm_neg]

private lemma planarChart_rotated_coordinates
    (p base other z : EuclideanSpace ℝ (Fin 2)) (c s : ℝ)
    (hrep : other = c • base + s • PlanarRot90 base)
    (hrot : PlanarRot90 other = (-s) • base + c • PlanarRot90 base) :
    let w : EuclideanSpace ℝ (Fin 2) := WithLp.toLp 2 (fun i : Fin 2 =>
      if i = 0 then z 0 * c - z 1 * s else z 0 * s + z 1 * c)
    p + w 0 • base + w 1 • PlanarRot90 base =
      p + z 0 • other + z 1 • PlanarRot90 other := by
  dsimp
  rw [hrot, hrep]
  apply PiLp.ext
  intro k
  fin_cases k <;> simp [PlanarRot90] <;> ring

private lemma set_diff_eq_diff_inter_self {X : Type*} (A B : Set X) :
    A \ B = A \ (A ∩ B) := by
  ext x
  simp only [Set.mem_diff, Set.mem_inter_iff]
  tauto

private lemma planarChart_origin_mem_closure
    (p d : EuclideanSpace ℝ (Fin 2))
    {S : Set (EuclideanSpace ℝ (Fin 2))}
    (hzero : (0 : EuclideanSpace ℝ (Fin 2)) ∈ closure S) :
    p ∈ closure ((fun z : EuclideanSpace ℝ (Fin 2) =>
      p + z 0 • d + z 1 • PlanarRot90 d) '' S) := by
  have hcont : Continuous (fun z : EuclideanSpace ℝ (Fin 2) =>
      p + z 0 • d + z 1 • PlanarRot90 d) := by fun_prop
  apply image_closure_subset_closure_image hcont
  exact ⟨0, hzero, by simp⟩

private lemma twoRay_directK_pos (c s : ℝ) :
    0 < (if 0 < s then s / (2 * (|c| + 1)) else 1) := by
  split_ifs with hs
  · positivity
  · norm_num

private lemma twoRay_abs_mul_directK_lt (c s : ℝ) (hs : 0 < s) :
    |c| * (if 0 < s then s / (2 * (|c| + 1)) else 1) < s := by
  have hden : 0 < 2 * (|c| + 1) := by positivity
  have hnum_lt : |c| < 2 * (|c| + 1) := by
    nlinarith [abs_nonneg c]
  rw [if_pos hs]
  calc
    |c| * (s / (2 * (|c| + 1))) =
        s * (|c| / (2 * (|c| + 1))) := by ring
    _ < s * 1 := mul_lt_mul_of_pos_left ((div_lt_one hden).2 hnum_lt) hs
    _ = s := by ring

private lemma twoRay_base_upper_cross_neg
    (c s directK K x y : ℝ)
    (hpos : 0 < s ∨ s = 0 ∧ c < 0) (hKle : K ≤ directK)
    (hdirect : ∀ hs : 0 < s, |c| * directK < s)
    (hx : 0 < x) (hy : 0 < y) (hyK : y < K * x) :
    c * y - s * x < 0 := by
  rcases hpos with hs | ⟨hs0, hc⟩
  · have hy' : y < directK * x :=
      lt_of_lt_of_le hyK (mul_le_mul_of_nonneg_right hKle hx.le)
    have hcabs : c * y ≤ |c| * y :=
      mul_le_mul_of_nonneg_right (le_abs_self c) hy.le
    have habsK : |c| * y ≤ |c| * (directK * x) :=
      mul_le_mul_of_nonneg_left hy'.le (abs_nonneg c)
    have hboundz : |c| * (directK * x) < s * x := by
      calc
        |c| * (directK * x) = (|c| * directK) * x := by ring
        _ < s * x := mul_lt_mul_of_pos_right (hdirect hs) hx
    linarith
  · rw [hs0]
    simpa using mul_neg_of_neg_of_pos hc hy

private lemma twoRay_other_lower_first_pos
    (c s directK K x y : ℝ)
    (hpos : 0 < s ∨ s = 0 ∧ c < 0) (hKle : K ≤ directK)
    (hdirect : ∀ hs : 0 < s, |c| * directK < s)
    (hx : 0 < x) (hy : y < 0) (hKy : -K * x < y) :
    0 < x * s + y * c := by
  rcases hpos with hs | ⟨hs0, hc⟩
  · have hlow : -directK * x < y := by
      have hle : -directK * x ≤ -K * x := by
        exact mul_le_mul_of_nonneg_right (neg_le_neg hKle) hx.le
      exact lt_of_le_of_lt hle hKy
    have habslow : |c| * (-directK * x) ≤ |c| * y :=
      mul_le_mul_of_nonneg_left hlow.le (abs_nonneg c)
    have habsc : |c| * y ≤ c * y :=
      mul_le_mul_of_nonpos_right (le_abs_self c) hy.le
    have hboundz : |c| * directK * x < s * x :=
      mul_lt_mul_of_pos_right (hdirect hs) hx
    nlinarith
  · rw [hs0]
    simpa [mul_comm] using mul_pos_of_neg_of_neg hy hc

private lemma quarter_lt_half {x : ℝ} (hx : 0 < x) : x / 4 < x / 2 := by
  linarith

private lemma swept_twoRay_cone_parameter_exists
    (p base other : EuclideanSpace ℝ (Fin 2)) (rho c s : ℝ)
    (hrho : 0 < rho) (hbase : base ≠ 0) (hother : other ≠ 0)
    (hnot_pos_ray : s ≠ 0 ∨ c < 0)
    (hother_eq : other = c • base - s • PlanarRot90 base) :
    ∃ K : ℝ, 0 < K := by
  have hswept := PlanarClockwiseSweptTwoRayEndpointConesInSector
    p base other rho c s hrho hbase hother hnot_pos_ray hother_eq
  dsimp only at hswept
  rcases hswept.2.2 with ⟨_coneR, coneK, _hconeR, hconeK, _⟩
  exact ⟨coneK, hconeK⟩

private lemma polygonalArcReverse_terminal_chart_eq_initial_chart
    (Q : PolygonalArc) (z q : EuclideanSpace ℝ (Fin 2))
    (hq :
      let R := PolygonalArcReverse Q
      let hprev : R.vertices.length - 2 < R.vertices.length := by
        have hlen := R.length_ge_two
        omega
      R.target + z 0 • (R.vertices[R.vertices.length - 2]'hprev - R.target) +
          z 1 • PlanarRot90 (R.vertices[R.vertices.length - 2]'hprev - R.target) = q) :
    Q.source +
        z 0 • ((Q.vertices[1]'(Nat.lt_of_succ_le Q.length_ge_two)) - Q.source) +
      z 1 • PlanarRot90
        ((Q.vertices[1]'(Nat.lt_of_succ_le Q.length_ge_two)) - Q.source) = q := by
  dsimp only at hq
  have hidx : Q.vertices.length - 1 - (Q.vertices.length - 2) = 1 := by
    have hlen := Q.length_ge_two
    omega
  simpa [PolygonalArcReverse, List.length_reverse, hidx] using hq

private lemma fin2_mem_ball_zero_of_sq_sum_lt
    (z : EuclideanSpace ℝ (Fin 2)) (a : ℝ) (ha : 0 ≤ a)
    (h : z 0 ^ 2 + z 1 ^ 2 < a ^ 2) :
    z ∈ Metric.ball 0 a := by
  rw [EuclideanSpace.ball_zero_eq (n := Fin 2) a ha]
  change (∑ i : Fin 2, z i ^ 2) < a ^ 2
  simpa only [Fin.sum_univ_two] using h

private lemma polygonalArcReverse_terminal_cone_normalize
    (Q : PolygonalArc) (hnext : 1 < Q.vertices.length) (r K : ℝ)
    (q : EuclideanSpace ℝ (Fin 2))
    (hq : q ∈ PolygonalArcTerminalEndpointLeftCone (PolygonalArcReverse Q) r K) :
    ∃ z : EuclideanSpace ℝ (Fin 2),
      (0 < z 0 ∧
        z 0 ^ 2 + z 1 ^ 2 <
          (r / dist Q.source (Q.vertices[1]'hnext)) ^ 2 ∧
        -K * z 0 < z 1 ∧ z 1 < 0) ∧
      Q.source + z 0 • ((Q.vertices[1]'hnext) - Q.source) +
        z 1 • PlanarRot90 ((Q.vertices[1]'hnext) - Q.source) = q := by
  rw [PolygonalArcTerminalEndpointLeftCone] at hq
  rcases hq with ⟨z, hz, hqeq⟩
  refine ⟨z, ?_, ?_⟩
  · have hidx : Q.vertices.length - 1 - (Q.vertices.length - 2) = 1 := by
      omega
    simpa [PolygonalArcReverse, List.length_reverse, hidx] using hz
  · exact polygonalArcReverse_terminal_chart_eq_initial_chart Q z q hqeq

private lemma jordan_bufferedCore_disjoint_other
    (J : SimpleClosedPolygonalCurve) (r : ℝ) (hr : 0 < r)
    (gamma delta : {Q : PolygonalArc // Q ∈ J.edgeArcs}) (hne : delta ≠ gamma) :
    Disjoint
      (gamma.1.carrier \
        (Metric.ball gamma.1.source (r / 2) ∪
          Metric.ball gamma.1.target (r / 2)))
      delta.1.carrier := by
  rw [Set.disjoint_left]
  intro x hxcore hxdelta
  have hxgamma : x ∈ gamma.1.carrier := hxcore.1
  by_cases hsucc : delta = J.successor gamma
  · rw [hsucc] at hxdelta
    have hxinter : x ∈ gamma.1.carrier ∩ (J.successor gamma).1.carrier :=
      ⟨hxgamma, hxdelta⟩
    rw [J.adjacent_intersection gamma] at hxinter
    change x = gamma.1.target at hxinter
    apply hxcore.2
    right
    rw [hxinter, Metric.mem_ball, dist_self]
    exact half_pos hr
  · by_cases hpred : J.successor delta = gamma
    · rw [← hpred] at hxgamma
      have hxinter : x ∈ delta.1.carrier ∩ (J.successor delta).1.carrier :=
        ⟨hxdelta, hxgamma⟩
      rw [J.adjacent_intersection delta] at hxinter
      change x = delta.1.target at hxinter
      have hxsource : x = gamma.1.source := by
        calc
          x = delta.1.target := hxinter
          _ = (J.successor delta).1.source := J.adjacent_endpoint delta
          _ = gamma.1.source := by rw [hpred]
      apply hxcore.2
      left
      rw [hxsource, Metric.mem_ball, dist_self]
      exact half_pos hr
    · exact Set.disjoint_left.mp
        (J.nonadjacent_disjoint gamma delta hne hsucc hpred) hxgamma hxdelta

private abbrev JordanCurveEdge (J : SimpleClosedPolygonalCurve) :=
  {Q : PolygonalArc // Q ∈ J.edgeArcs}

private structure JordanVertexSectorPreparation
    (J : SimpleClosedPolygonalCurve) where
  edge_nonempty : Nonempty (JordanCurveEdge J)
  presentation : FinitePolygonalSet
  presentation_carrier_eq : presentation.carrier = J.carrier
  arc_source_mem : ∀ Q : PolygonalArc, Q.source ∈ Q.carrier
  vertexR : ℝ
  vertexR_pos : 0 < vertexR
  vertexR_quarter_lt_half : vertexR / 4 < vertexR / 2
  endpointIsolation : ∀ gamma : JordanCurveEdge J,
    PolygonalArcEndpointIsolation gamma.1 vertexR vertexR
  vertexClosedDisks_disjoint : ∀ gamma delta : JordanCurveEdge J,
    gamma ≠ delta →
      Disjoint (Metric.closedBall gamma.1.target vertexR)
        (Metric.closedBall delta.1.target vertexR)
  vertexDisk_curve_eq : ∀ gamma : JordanCurveEdge J,
    Metric.ball gamma.1.target vertexR ∩ J.carrier =
      Metric.ball gamma.1.target vertexR ∩
        (gamma.1.carrier ∪ (J.successor gamma).1.carrier)
  leftVertexSector : JordanCurveEdge J → Set (EuclideanSpace ℝ (Fin 2))
  rightVertexSector : JordanCurveEdge J → Set (EuclideanSpace ℝ (Fin 2))
  vertexAperture : JordanCurveEdge J → ℝ
  hAperturePos : ∀ gamma, 0 < vertexAperture gamma
  hLne : ∀ gamma, (leftVertexSector gamma).Nonempty
  hRne : ∀ gamma, (rightVertexSector gamma).Nonempty
  hLopen : ∀ gamma, IsOpen (leftVertexSector gamma)
  hRopen : ∀ gamma, IsOpen (rightVertexSector gamma)
  hLconn : ∀ gamma, IsConnected (leftVertexSector gamma)
  hRconn : ∀ gamma, IsConnected (rightVertexSector gamma)
  hLdisk : ∀ gamma,
    leftVertexSector gamma ⊆ Metric.ball gamma.1.target vertexR
  hRdisk : ∀ gamma,
    rightVertexSector gamma ⊆ Metric.ball gamma.1.target vertexR
  hLcomp : ∀ gamma, leftVertexSector gamma ⊆ J.carrierᶜ
  hRcomp : ∀ gamma, rightVertexSector gamma ⊆ J.carrierᶜ
  hdisj : ∀ gamma, Disjoint (leftVertexSector gamma) (rightVertexSector gamma)
  hpartition : ∀ gamma,
    Metric.ball gamma.1.target vertexR \ J.carrier =
      leftVertexSector gamma ∪ rightVertexSector gamma
  hLclosure : ∀ gamma, gamma.1.target ∈ closure (leftVertexSector gamma)
  hRclosure : ∀ gamma, gamma.1.target ∈ closure (rightVertexSector gamma)
  hterminalLeft : ∀ gamma,
    PolygonalArcTerminalEndpointLeftCone gamma.1 vertexR (vertexAperture gamma) ⊆
      leftVertexSector gamma
  hsuccessorLeft : ∀ gamma,
    PolygonalArcInitialEndpointLeftCone (J.successor gamma).1 vertexR
        (vertexAperture gamma) ⊆ leftVertexSector gamma
  hterminalRight : ∀ gamma,
    PolygonalArcInitialEndpointLeftCone (PolygonalArcReverse gamma.1) vertexR
        (vertexAperture gamma) ⊆ rightVertexSector gamma
  hsuccessorRight : ∀ gamma,
    PolygonalArcTerminalEndpointLeftCone
        (PolygonalArcReverse (J.successor gamma).1) vertexR
        (vertexAperture gamma) ⊆ rightVertexSector gamma

private def terminalDirection {J : SimpleClosedPolygonalCurve}
    (gamma : JordanCurveEdge J) : EuclideanSpace ℝ (Fin 2) :=
  gamma.1.vertices[gamma.1.vertices.length - 2]'(by
    have hlen := gamma.1.length_ge_two
    omega) - gamma.1.target

private def initialDirection {J : SimpleClosedPolygonalCurve}
    (gamma : JordanCurveEdge J) : EuclideanSpace ℝ (Fin 2) :=
  gamma.1.vertices[1]'(Nat.lt_of_succ_le gamma.1.length_ge_two) - gamma.1.source

private lemma jordan_vertex_sector_exists
    (J : SimpleClosedPolygonalCurve) (gamma : JordanCurveEdge J)
    (vertexR : ℝ) (vertexR_pos : 0 < vertexR)
    (terminalDirection_ne : ∀ delta : JordanCurveEdge J,
      terminalDirection delta ≠ 0)
    (initialDirection_ne : ∀ delta : JordanCurveEdge J,
      initialDirection delta ≠ 0)
    (adjacent_directions_not_same : ∀ delta : JordanCurveEdge J,
      ¬ ∃ a : ℝ, 0 < a ∧
        initialDirection (J.successor delta) = a • terminalDirection delta)
    (origin_mem_twoRay_left_closure : ∀ (a c s : ℝ), 0 < a →
      (0 < s ∨ s = 0 ∧ c < 0) →
      (0 : EuclideanSpace ℝ (Fin 2)) ∈ closure
        {z | z ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) a ∧
          0 < z 1 ∧ c * z 1 - s * z 0 < 0})
    (origin_mem_twoRay_right_closure : ∀ (a c s : ℝ), 0 < a →
      (0 : EuclideanSpace ℝ (Fin 2)) ∈ closure
        {z | z ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) a ∧
          (z 1 < 0 ∨ 0 < c * z 1 - s * z 0)})
    (planarChart_injective : ∀ (p d : EuclideanSpace ℝ (Fin 2)), d ≠ 0 →
      Function.Injective (fun z : EuclideanSpace ℝ (Fin 2) =>
        p + z 0 • d + z 1 • PlanarRot90 d))
    (planarChart_radial_subset_ball :
      ∀ (p d : EuclideanSpace ℝ (Fin 2)) (R : ℝ), d ≠ 0 → 0 < R →
        (fun z : EuclideanSpace ℝ (Fin 2) =>
            p + z 0 • d + z 1 • PlanarRot90 d) ''
            {z | z 0 ^ 2 + z 1 ^ 2 < (R / ‖d‖) ^ 2} ⊆
          Metric.ball p R)
    (hRays :
      {q | q ∈ Metric.ball gamma.1.target vertexR ∧
        ∃ t : ℝ, 0 < t ∧
          q = gamma.1.target + t • terminalDirection gamma} ∪
      {q | q ∈ Metric.ball gamma.1.target vertexR ∧
        ∃ t : ℝ, 0 < t ∧
          q = gamma.1.target +
            t • initialDirection (J.successor gamma)} ∪
      ({gamma.1.target} : Set (EuclideanSpace ℝ (Fin 2))) =
        Metric.ball gamma.1.target vertexR ∩ J.carrier) :
    ∃ L R : Set (EuclideanSpace ℝ (Fin 2)), ∃ K : ℝ,
      0 < K ∧ L.Nonempty ∧ R.Nonempty ∧ IsOpen L ∧ IsOpen R ∧
        IsConnected L ∧ IsConnected R ∧
        L ⊆ Metric.ball gamma.1.target vertexR ∧
        R ⊆ Metric.ball gamma.1.target vertexR ∧
        L ⊆ J.carrierᶜ ∧ R ⊆ J.carrierᶜ ∧ Disjoint L R ∧
        Metric.ball gamma.1.target vertexR \ J.carrier = L ∪ R ∧
        gamma.1.target ∈ closure L ∧ gamma.1.target ∈ closure R ∧
        PolygonalArcTerminalEndpointLeftCone gamma.1 vertexR K ⊆ L ∧
        PolygonalArcInitialEndpointLeftCone (J.successor gamma).1 vertexR K ⊆ L ∧
        PolygonalArcInitialEndpointLeftCone (PolygonalArcReverse gamma.1)
            vertexR K ⊆ R ∧
        PolygonalArcTerminalEndpointLeftCone
            (PolygonalArcReverse (J.successor gamma).1) vertexR K ⊆ R := by
  let p := gamma.1.target
  let u := terminalDirection gamma
  let v := initialDirection (J.successor gamma)
  have vertex_ball_rays :
      {q | q ∈ Metric.ball p vertexR ∧
        ∃ t : ℝ, 0 < t ∧ q = p + t • u} ∪
      {q | q ∈ Metric.ball p vertexR ∧
        ∃ t : ℝ, 0 < t ∧ q = p + t • v} ∪
      ({p} : Set (EuclideanSpace ℝ (Fin 2))) =
        Metric.ball p vertexR ∩ J.carrier := by
    simpa [p, u, v] using hRays
  have terminal_len := gamma.1.length_ge_two
  have terminal_dist : dist gamma.1.target
      (gamma.1.vertices[gamma.1.vertices.length - 2]'(by omega)) = ‖u‖ := by
    simpa only [u, terminalDirection] using
      polygonalArc_terminal_dist_eq_norm_direction gamma.1
  have successor_len := (J.successor gamma).1.length_ge_two
  have successor_dist : dist (J.successor gamma).1.source
      ((J.successor gamma).1.vertices[1]'(Nat.lt_of_succ_le successor_len)) = ‖v‖ := by
    simpa only [v, initialDirection] using
      polygonalArc_initial_dist_eq_norm_direction (J.successor gamma).1
  have successor_direction : v =
      ((J.successor gamma).1.vertices[1]'(Nat.lt_of_succ_le successor_len)) -
        (J.successor gamma).1.source := rfl
  rcases PolygonalArcInteriorTwoRaySectorChartTransport p u v vertexR
      vertexR_pos (terminalDirection_ne gamma)
      (initialDirection_ne (J.successor gamma))
      (adjacent_directions_not_same gamma) with
    ⟨base, other, c, s, hbase, hrep, hpos, hsector⟩
  rcases hbase with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · let a : ℝ := vertexR / ‖u‖
    let chart : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 2) :=
      fun z => p + z 0 • u + z 1 • PlanarRot90 u
    let C : Set (EuclideanSpace ℝ (Fin 2)) := Metric.ball 0 a
    let Gbase : Set (EuclideanSpace ℝ (Fin 2)) :=
      {z | z ∈ C ∧ z 1 = 0 ∧ 0 < z 0}
    let Gother : Set (EuclideanSpace ℝ (Fin 2)) :=
      {z | z ∈ C ∧ ∃ t : ℝ, 0 < t ∧ z 0 = t * c ∧ z 1 = t * s}
    let Lmodel : Set (EuclideanSpace ℝ (Fin 2)) :=
      {z | z ∈ C ∧ 0 < z 1 ∧ c * z 1 - s * z 0 < 0}
    let Rmodel : Set (EuclideanSpace ℝ (Fin 2)) :=
      {z | z ∈ C ∧ (z 1 < 0 ∨ 0 < c * z 1 - s * z 0)}
    change
      0 < a ∧ IsOpen (chart '' C) ∧ IsOpen (chart '' Lmodel) ∧
        IsOpen (chart '' Rmodel) ∧ IsConnected (chart '' Lmodel) ∧
        IsConnected (chart '' Rmodel) ∧
        Disjoint (chart '' Lmodel) (chart '' Rmodel) ∧
        chart '' C = Metric.ball p vertexR ∧
        chart '' Gbase =
          {q | q ∈ Metric.ball p vertexR ∧
            ∃ t : ℝ, 0 < t ∧ q = p + t • u} ∧
        chart '' Gother =
          {q | q ∈ Metric.ball p vertexR ∧
            ∃ t : ℝ, 0 < t ∧ q = p + t • v} ∧
        Disjoint (chart '' Lmodel)
          ((chart '' Gbase) ∪ (chart '' Gother) ∪ ({p} : Set _)) ∧
        Disjoint (chart '' Rmodel)
          ((chart '' Gbase) ∪ (chart '' Gother) ∪ ({p} : Set _)) ∧
        Metric.ball p vertexR \
            ((chart '' Gbase) ∪ (chart '' Gother) ∪ ({p} : Set _)) =
          chart '' Lmodel ∪ chart '' Rmodel at hsector
    rcases hsector with
      ⟨ha, _hCopen, hLopen, hRopen, hLconn, hRconn, hdisj,
        hCeq, hGbase, hGother, _hLbad, _hRbad, hsplit⟩
    have hbad :
        (chart '' Gbase) ∪ (chart '' Gother) ∪ ({p} : Set _) =
          Metric.ball p vertexR ∩ J.carrier := by
      calc
        (chart '' Gbase) ∪ (chart '' Gother) ∪ ({p} : Set _) =
            {q | q ∈ Metric.ball p vertexR ∧
              ∃ t : ℝ, 0 < t ∧ q = p + t • u} ∪
            {q | q ∈ Metric.ball p vertexR ∧
              ∃ t : ℝ, 0 < t ∧ q = p + t • v} ∪ ({p} : Set _) := by
              rw [hGbase, hGother]
        _ = Metric.ball p vertexR ∩ J.carrier := by
          exact vertex_ball_rays
    have hpartition : Metric.ball p vertexR \ J.carrier =
        (chart '' Rmodel) ∪ (chart '' Lmodel) := by
      calc
        Metric.ball p vertexR \ J.carrier =
            Metric.ball p vertexR \ (Metric.ball p vertexR ∩ J.carrier) := by
              exact set_diff_eq_diff_inter_self _ _
        _ = Metric.ball p vertexR \
            ((chart '' Gbase) ∪ (chart '' Gother) ∪ ({p} : Set _)) := by
              rw [hbad]
        _ = (chart '' Rmodel) ∪ (chart '' Lmodel) := by
              rw [hsplit, Set.union_comm]
    have hLclosure : p ∈ closure (chart '' Lmodel) := by
      apply planarChart_origin_mem_closure p u
      change (0 : EuclideanSpace ℝ (Fin 2)) ∈ closure
        {z | z ∈ Metric.ball 0 a ∧ 0 < z 1 ∧ c * z 1 - s * z 0 < 0}
      exact origin_mem_twoRay_left_closure a c s ha hpos
    have hRclosure : p ∈ closure (chart '' Rmodel) := by
      apply planarChart_origin_mem_closure p u
      change (0 : EuclideanSpace ℝ (Fin 2)) ∈ closure
        {z | z ∈ Metric.ball 0 a ∧ (z 1 < 0 ∨ 0 < c * z 1 - s * z 0)}
      exact origin_mem_twoRay_right_closure a c s ha
    have hnot : -s ≠ 0 ∨ c < 0 := by
      rcases hpos with hs | ⟨hs, hc⟩
      · exact Or.inl (neg_ne_zero.mpr (ne_of_gt hs))
      · exact Or.inr hc
    rcases swept_twoRay_cone_parameter_exists
        p u v vertexR c (-s) vertexR_pos (terminalDirection_ne gamma)
        (initialDirection_ne (J.successor gamma)) hnot (by simpa using hrep) with
      ⟨coneK, hconeK⟩
    let directK : ℝ := if 0 < s then s / (2 * (|c| + 1)) else 1
    have directK_pos : 0 < directK := by
      exact twoRay_directK_pos c s
    let K := min coneK directK
    have hK : 0 < K := lt_min hconeK directK_pos
    have hdirect_bound (hs : 0 < s) : |c| * directK < s := by
      exact twoRay_abs_mul_directK_lt c s hs
    have base_upper_cross_neg (z : EuclideanSpace ℝ (Fin 2))
        (hz0 : 0 < z 0) (hz1 : 0 < z 1) (hzK : z 1 < K * z 0) :
        c * z 1 - s * z 0 < 0 := by
      exact twoRay_base_upper_cross_neg c s directK K (z 0) (z 1)
        hpos (min_le_right _ _) hdirect_bound hz0 hz1 hzK
    have other_lower_first_pos (z : EuclideanSpace ℝ (Fin 2))
        (hz0 : 0 < z 0) (hz1 : z 1 < 0) (hzK : -K * z 0 < z 1) :
        0 < z 0 * s + z 1 * c := by
      exact twoRay_other_lower_first_pos c s directK K (z 0) (z 1)
        hpos (min_le_right _ _) hdirect_bound hz0 hz1 hzK
    refine ⟨chart '' Rmodel, chart '' Lmodel, K, hK,
      (Set.Nonempty.of_closure ⟨p, hRclosure⟩),
      (Set.Nonempty.of_closure ⟨p, hLclosure⟩),
      hRopen, hLopen, hRconn, hLconn, ?_, ?_, ?_, ?_, hdisj.symm,
      hpartition, hRclosure, hLclosure, ?_, ?_, ?_, ?_⟩
    · intro q hq
      have hmem : q ∈ Metric.ball p vertexR \ J.carrier := by
        rw [hpartition]
        exact Or.inl hq
      exact hmem.1
    · intro q hq
      have hmem : q ∈ Metric.ball p vertexR \ J.carrier := by
        rw [hpartition]
        exact Or.inr hq
      exact hmem.1
    · intro q hq
      have hmem : q ∈ Metric.ball p vertexR \ J.carrier := by
        rw [hpartition]
        exact Or.inl hq
      exact hmem.2
    · intro q hq
      have hmem : q ∈ Metric.ball p vertexR \ J.carrier := by
        rw [hpartition]
        exact Or.inr hq
      exact hmem.2
    · rw [PolygonalArcTerminalEndpointLeftCone]
      rintro q ⟨z, hz, rfl⟩
      have hlen := gamma.1.length_ge_two
      refine ⟨z, ?_, rfl⟩
      refine ⟨?_, Or.inl hz.2.2.2⟩
      change z ∈ C
      have hdist : dist gamma.1.target
          gamma.1.vertices[gamma.1.vertices.length - 2] = ‖u‖ := by
        exact terminal_dist
      change z ∈ Metric.ball 0 a
      rw [EuclideanSpace.ball_zero_eq (n := Fin 2) a ha.le]
      simpa [Fin.sum_univ_two, a, hdist] using hz.2.1
    · rw [PolygonalArcInitialEndpointLeftCone]
      rintro q ⟨z, hz, rfl⟩
      have hlen := (J.successor gamma).1.length_ge_two
      have hsource : (J.successor gamma).1.source = p := by
        simpa [p] using (J.adjacent_endpoint gamma).symm
      have hdir : (J.successor gamma).1.vertices[1] -
          (J.successor gamma).1.source = v := by rfl
      have hdir' : (J.successor gamma).1.vertices[1] - p = v := by
        rw [← hsource]
        exact hdir
      rw [hsource]
      have hdist : dist (J.successor gamma).1.source
          (J.successor gamma).1.vertices[1] = ‖v‖ := by
        exact successor_dist
      have hqball :
          p + z 0 • v + z 1 • PlanarRot90 v ∈ Metric.ball p vertexR := by
        apply planarChart_radial_subset_ball p v vertexR
          (initialDirection_ne (J.successor gamma)) vertexR_pos
        have hrad := hz.2.1
        have hrad' : z 0 ^ 2 + z 1 ^ 2 < (vertexR / ‖v‖) ^ 2 :=
          (congrArg (fun r : ℝ => z 0 ^ 2 + z 1 ^ 2 < r)
            (congrArg (fun x : ℝ => (vertexR / x) ^ 2) hdist)).mp hrad
        exact ⟨z, hrad', rfl⟩
      have hqC : p + z 0 • v + z 1 • PlanarRot90 v ∈ chart '' C := by
        rw [hCeq]
        exact hqball
      rcases hqC with ⟨w, hwC, hwq⟩
      let w' : EuclideanSpace ℝ (Fin 2) := WithLp.toLp 2 (fun i : Fin 2 =>
        if i = 0 then z 0 * c - z 1 * s else z 0 * s + z 1 * c)
      have hrot : PlanarRot90 v = (-s) • u + c • PlanarRot90 u := by
        rw [hrep]
        exact PlanarRot90LinearCombination u c s
      have hwq' : chart w' = p + z 0 • v + z 1 • PlanarRot90 v := by
        exact planarChart_rotated_coordinates p u v z c s hrep hrot
      have hww : w = w' := planarChart_injective p u
        (terminalDirection_ne gamma) (hwq.trans hwq'.symm)
      refine ⟨w, ⟨hwC, Or.inr ?_⟩, ?_⟩
      · have hD : 0 < c ^ 2 + s ^ 2 :=
          twoRay_coefficient_sq_sum_pos hpos
        rw [hww]
        dsimp [w']
        simp
        exact sub_pos.mp
          (rotated_cross_pos c s (z 0) (z 1) hD hz.2.2.1)
      · simpa [v, initialDirection, hsource] using hwq
    · intro q hq
      rw [PolygonalArcInitialEndpointLeftCone] at hq
      rcases hq with ⟨z, hz, hqeq⟩
      have hlen := gamma.1.length_ge_two
      have hidx : gamma.1.vertices.length - 1 - 1 =
          gamma.1.vertices.length - 2 := by
        omega
      refine ⟨z, ?_, ?_⟩
      · refine ⟨?_, hz.2.2.1, base_upper_cross_neg z hz.1 hz.2.2.1 hz.2.2.2⟩
        have hdist : dist gamma.1.target
            gamma.1.vertices[gamma.1.vertices.length - 2] = ‖u‖ := by
          exact terminal_dist
        change z ∈ Metric.ball 0 a
        rw [EuclideanSpace.ball_zero_eq (n := Fin 2) a ha.le]
        simpa [Fin.sum_univ_two, a, PolygonalArcReverse,
          List.length_reverse, hidx, hdist] using hz.2.1
      · simpa [chart, p, u, terminalDirection, PolygonalArcReverse,
          List.length_reverse, hidx] using hqeq
    · intro q hq
      rw [PolygonalArcTerminalEndpointLeftCone] at hq
      rcases hq with ⟨z, hz, hqeq⟩
      let sigma := J.successor gamma
      have hsigma_source : sigma.1.source = p := by
        simpa [sigma, p] using (J.adjacent_endpoint gamma).symm
      have hsigma_len := sigma.1.length_ge_two
      have hidx : sigma.1.vertices.length - 1 -
          (sigma.1.vertices.length - 2) = 1 := by
        omega
      have hqeq' : q = p + z 0 • v + z 1 • PlanarRot90 v := by
        simpa [sigma, p, v, initialDirection, PolygonalArcReverse,
          List.length_reverse, hidx, hsigma_source] using hqeq.symm
      have hdist : dist sigma.1.source sigma.1.vertices[1] = ‖v‖ := by
        simpa only [sigma] using successor_dist
      have hqball : p + z 0 • v + z 1 • PlanarRot90 v ∈ Metric.ball p vertexR := by
        apply planarChart_radial_subset_ball p v vertexR
          (initialDirection_ne sigma) vertexR_pos
        have hrad' : z 0 ^ 2 + z 1 ^ 2 < (vertexR / ‖v‖) ^ 2 :=
          (congrArg (fun r : ℝ => z 0 ^ 2 + z 1 ^ 2 < r)
            (congrArg (fun x : ℝ => (vertexR / x) ^ 2) hdist)).mp
            (by simpa [sigma, PolygonalArcReverse, List.length_reverse, hidx] using hz.2.1)
        exact ⟨z, hrad', rfl⟩
      have hqC : p + z 0 • v + z 1 • PlanarRot90 v ∈ chart '' C := by
        rw [hCeq]
        exact hqball
      rcases hqC with ⟨w, hwC, hwq⟩
      let w' : EuclideanSpace ℝ (Fin 2) := WithLp.toLp 2 (fun i : Fin 2 =>
        if i = 0 then z 0 * c - z 1 * s else z 0 * s + z 1 * c)
      have hrot : PlanarRot90 v = (-s) • u + c • PlanarRot90 u := by
        rw [hrep]
        exact PlanarRot90LinearCombination u c s
      have hwq' : chart w' = p + z 0 • v + z 1 • PlanarRot90 v := by
        exact planarChart_rotated_coordinates p u v z c s hrep hrot
      have hww : w = w' := planarChart_injective p u
        (terminalDirection_ne gamma) (hwq.trans hwq'.symm)
      refine ⟨w, ⟨hwC, ?_, ?_⟩, ?_⟩
      · rw [hww]
        dsimp [w']
        exact other_lower_first_pos z hz.1 hz.2.2.2 hz.2.2.1
      · have hD : 0 < c ^ 2 + s ^ 2 :=
          twoRay_coefficient_sq_sum_pos hpos
        rw [hww]
        dsimp [w']
        simp
        exact sub_neg.mp
          (rotated_cross_neg c s (z 0) (z 1) hD hz.2.2.2)
      · exact hwq.trans hqeq'.symm
  · let a : ℝ := vertexR / ‖v‖
    let chart : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 2) :=
      fun z => p + z 0 • v + z 1 • PlanarRot90 v
    let C : Set (EuclideanSpace ℝ (Fin 2)) := Metric.ball 0 a
    let Gbase : Set (EuclideanSpace ℝ (Fin 2)) :=
      {z | z ∈ C ∧ z 1 = 0 ∧ 0 < z 0}
    let Gother : Set (EuclideanSpace ℝ (Fin 2)) :=
      {z | z ∈ C ∧ ∃ t : ℝ, 0 < t ∧ z 0 = t * c ∧ z 1 = t * s}
    let Lmodel : Set (EuclideanSpace ℝ (Fin 2)) :=
      {z | z ∈ C ∧ 0 < z 1 ∧ c * z 1 - s * z 0 < 0}
    let Rmodel : Set (EuclideanSpace ℝ (Fin 2)) :=
      {z | z ∈ C ∧ (z 1 < 0 ∨ 0 < c * z 1 - s * z 0)}
    change
      0 < a ∧ IsOpen (chart '' C) ∧ IsOpen (chart '' Lmodel) ∧
        IsOpen (chart '' Rmodel) ∧ IsConnected (chart '' Lmodel) ∧
        IsConnected (chart '' Rmodel) ∧
        Disjoint (chart '' Lmodel) (chart '' Rmodel) ∧
        chart '' C = Metric.ball p vertexR ∧
        chart '' Gbase =
          {q | q ∈ Metric.ball p vertexR ∧
            ∃ t : ℝ, 0 < t ∧ q = p + t • v} ∧
        chart '' Gother =
          {q | q ∈ Metric.ball p vertexR ∧
            ∃ t : ℝ, 0 < t ∧ q = p + t • u} ∧
        Disjoint (chart '' Lmodel)
          ((chart '' Gbase) ∪ (chart '' Gother) ∪ ({p} : Set _)) ∧
        Disjoint (chart '' Rmodel)
          ((chart '' Gbase) ∪ (chart '' Gother) ∪ ({p} : Set _)) ∧
        Metric.ball p vertexR \
            ((chart '' Gbase) ∪ (chart '' Gother) ∪ ({p} : Set _)) =
          chart '' Lmodel ∪ chart '' Rmodel at hsector
    rcases hsector with
      ⟨ha, _hCopen, hLopen, hRopen, hLconn, hRconn, hdisj,
        hCeq, hGbase, hGother, _hLbad, _hRbad, hsplit⟩
    have hbad :
        (chart '' Gbase) ∪ (chart '' Gother) ∪ ({p} : Set _) =
          Metric.ball p vertexR ∩ J.carrier := by
      calc
        (chart '' Gbase) ∪ (chart '' Gother) ∪ ({p} : Set _) =
            {q | q ∈ Metric.ball p vertexR ∧
              ∃ t : ℝ, 0 < t ∧ q = p + t • v} ∪
            {q | q ∈ Metric.ball p vertexR ∧
              ∃ t : ℝ, 0 < t ∧ q = p + t • u} ∪ ({p} : Set _) := by
              rw [hGbase, hGother]
        _ = {q | q ∈ Metric.ball p vertexR ∧
              ∃ t : ℝ, 0 < t ∧ q = p + t • u} ∪
            {q | q ∈ Metric.ball p vertexR ∧
              ∃ t : ℝ, 0 < t ∧ q = p + t • v} ∪ ({p} : Set _) := by
              ac_rfl
        _ = Metric.ball p vertexR ∩ J.carrier := by
          exact vertex_ball_rays
    have hpartition : Metric.ball p vertexR \ J.carrier =
        (chart '' Lmodel) ∪ (chart '' Rmodel) := by
      calc
        Metric.ball p vertexR \ J.carrier =
            Metric.ball p vertexR \ (Metric.ball p vertexR ∩ J.carrier) := by
              exact set_diff_eq_diff_inter_self _ _
        _ = Metric.ball p vertexR \
            ((chart '' Gbase) ∪ (chart '' Gother) ∪ ({p} : Set _)) := by
              rw [hbad]
        _ = (chart '' Lmodel) ∪ (chart '' Rmodel) := hsplit
    have hLclosure : p ∈ closure (chart '' Lmodel) := by
      apply planarChart_origin_mem_closure p v
      change (0 : EuclideanSpace ℝ (Fin 2)) ∈ closure
        {z | z ∈ Metric.ball 0 a ∧ 0 < z 1 ∧ c * z 1 - s * z 0 < 0}
      exact origin_mem_twoRay_left_closure a c s ha hpos
    have hRclosure : p ∈ closure (chart '' Rmodel) := by
      apply planarChart_origin_mem_closure p v
      change (0 : EuclideanSpace ℝ (Fin 2)) ∈ closure
        {z | z ∈ Metric.ball 0 a ∧ (z 1 < 0 ∨ 0 < c * z 1 - s * z 0)}
      exact origin_mem_twoRay_right_closure a c s ha
    have hnot : -s ≠ 0 ∨ c < 0 := by
      rcases hpos with hs | ⟨hs, hc⟩
      · exact Or.inl (neg_ne_zero.mpr (ne_of_gt hs))
      · exact Or.inr hc
    rcases swept_twoRay_cone_parameter_exists
        p v u vertexR c (-s) vertexR_pos
        (initialDirection_ne (J.successor gamma)) (terminalDirection_ne gamma)
        hnot (by simpa using hrep) with
      ⟨coneK, hconeK⟩
    let directK : ℝ := if 0 < s then s / (2 * (|c| + 1)) else 1
    have directK_pos : 0 < directK := by
      exact twoRay_directK_pos c s
    let K := min coneK directK
    have hK : 0 < K := lt_min hconeK directK_pos
    have hdirect_bound (hs : 0 < s) : |c| * directK < s := by
      exact twoRay_abs_mul_directK_lt c s hs
    have base_upper_cross_neg (z : EuclideanSpace ℝ (Fin 2))
        (hz0 : 0 < z 0) (hz1 : 0 < z 1) (hzK : z 1 < K * z 0) :
        c * z 1 - s * z 0 < 0 := by
      exact twoRay_base_upper_cross_neg c s directK K (z 0) (z 1)
        hpos (min_le_right _ _) hdirect_bound hz0 hz1 hzK
    have other_lower_first_pos (z : EuclideanSpace ℝ (Fin 2))
        (hz0 : 0 < z 0) (hz1 : z 1 < 0) (hzK : -K * z 0 < z 1) :
        0 < z 0 * s + z 1 * c := by
      exact twoRay_other_lower_first_pos c s directK K (z 0) (z 1)
        hpos (min_le_right _ _) hdirect_bound hz0 hz1 hzK
    refine ⟨chart '' Lmodel, chart '' Rmodel, K, hK,
      (Set.Nonempty.of_closure ⟨p, hLclosure⟩),
      (Set.Nonempty.of_closure ⟨p, hRclosure⟩),
      hLopen, hRopen, hLconn, hRconn, ?_, ?_, ?_, ?_, hdisj,
      hpartition, hLclosure, hRclosure, ?_, ?_, ?_, ?_⟩
    · intro q hq
      have hmem : q ∈ Metric.ball p vertexR \ J.carrier := by
        rw [hpartition]
        exact Or.inl hq
      exact hmem.1
    · intro q hq
      have hmem : q ∈ Metric.ball p vertexR \ J.carrier := by
        rw [hpartition]
        exact Or.inr hq
      exact hmem.1
    · intro q hq
      have hmem : q ∈ Metric.ball p vertexR \ J.carrier := by
        rw [hpartition]
        exact Or.inl hq
      exact hmem.2
    · intro q hq
      have hmem : q ∈ Metric.ball p vertexR \ J.carrier := by
        rw [hpartition]
        exact Or.inr hq
      exact hmem.2
    · rw [PolygonalArcTerminalEndpointLeftCone]
      rintro q ⟨z, hz, rfl⟩
      have hlen := gamma.1.length_ge_two
      have hqball : p + z 0 • u + z 1 • PlanarRot90 u ∈
          Metric.ball p vertexR := by
        apply planarChart_radial_subset_ball p u vertexR
          (terminalDirection_ne gamma) vertexR_pos
        have hrad' : z 0 ^ 2 + z 1 ^ 2 < (vertexR / ‖u‖) ^ 2 :=
          (congrArg (fun r : ℝ => z 0 ^ 2 + z 1 ^ 2 < r)
            (congrArg (fun x : ℝ => (vertexR / x) ^ 2) terminal_dist)).mp hz.2.1
        exact ⟨z, hrad', rfl⟩
      have hqC : p + z 0 • u + z 1 • PlanarRot90 u ∈ chart '' C := by
        rw [hCeq]
        exact hqball
      rcases hqC with ⟨w, hwC, hwq⟩
      let w' : EuclideanSpace ℝ (Fin 2) := WithLp.toLp 2 (fun i : Fin 2 =>
        if i = 0 then z 0 * c - z 1 * s else z 0 * s + z 1 * c)
      have hrot : PlanarRot90 u = (-s) • v + c • PlanarRot90 v := by
        rw [hrep]
        exact PlanarRot90LinearCombination v c s
      have hwq' : chart w' = p + z 0 • u + z 1 • PlanarRot90 u := by
        exact planarChart_rotated_coordinates p v u z c s hrep hrot
      have hww : w = w' := planarChart_injective p v
        (initialDirection_ne (J.successor gamma)) (hwq.trans hwq'.symm)
      refine ⟨w, ⟨hwC, ?_, ?_⟩, ?_⟩
      · rw [hww]
        dsimp [w']
        exact other_lower_first_pos z hz.1 hz.2.2.2 hz.2.2.1
      · have hD : 0 < c ^ 2 + s ^ 2 :=
          twoRay_coefficient_sq_sum_pos hpos
        rw [hww]
        dsimp [w']
        simp
        exact sub_neg.mp
          (rotated_cross_neg c s (z 0) (z 1) hD hz.2.2.2)
      · simpa [p, u, terminalDirection] using hwq
    · rw [PolygonalArcInitialEndpointLeftCone]
      rintro q ⟨z, hz, rfl⟩
      let sigma := J.successor gamma
      have hsigma_len := sigma.1.length_ge_two
      have hsource : sigma.1.source = p := by
        simpa [sigma, p] using (J.adjacent_endpoint gamma).symm
      have hdist : dist sigma.1.source sigma.1.vertices[1] = ‖v‖ := by
        simpa only [sigma] using successor_dist
      refine ⟨z, ?_, ?_⟩
      · refine ⟨?_, hz.2.2.1, base_upper_cross_neg z hz.1 hz.2.2.1 hz.2.2.2⟩
        have hrad' : z 0 ^ 2 + z 1 ^ 2 < (vertexR / ‖v‖) ^ 2 :=
          (congrArg (fun r : ℝ => z 0 ^ 2 + z 1 ^ 2 < r)
            (congrArg (fun x : ℝ => (vertexR / x) ^ 2) hdist)).mp hz.2.1
        apply fin2_mem_ball_zero_of_sq_sum_lt z a ha.le
        simpa only [a] using hrad'
      · simpa [chart, sigma, p, v, initialDirection, hsource]
    · intro q hq
      rw [PolygonalArcInitialEndpointLeftCone] at hq
      rcases hq with ⟨z, hz, hqeq⟩
      have hlen := gamma.1.length_ge_two
      have hidx : gamma.1.vertices.length - 1 - 1 =
          gamma.1.vertices.length - 2 := by omega
      have hqeq' : q = p + z 0 • u + z 1 • PlanarRot90 u := by
        simpa [p, u, terminalDirection, PolygonalArcReverse,
          List.length_reverse, hidx] using hqeq.symm
      have hqball : p + z 0 • u + z 1 • PlanarRot90 u ∈
          Metric.ball p vertexR := by
        apply planarChart_radial_subset_ball p u vertexR
          (terminalDirection_ne gamma) vertexR_pos
        have hradorig : z 0 ^ 2 + z 1 ^ 2 <
            (vertexR / dist gamma.1.target
              (gamma.1.vertices[gamma.1.vertices.length - 2]'(by omega))) ^ 2 := by
          simpa [PolygonalArcReverse, List.length_reverse, hidx] using hz.2.1
        have hrad' : z 0 ^ 2 + z 1 ^ 2 < (vertexR / ‖u‖) ^ 2 :=
          (congrArg (fun r : ℝ => z 0 ^ 2 + z 1 ^ 2 < r)
            (congrArg (fun x : ℝ => (vertexR / x) ^ 2) terminal_dist)).mp hradorig
        exact ⟨z, hrad', rfl⟩
      have hqC : p + z 0 • u + z 1 • PlanarRot90 u ∈ chart '' C := by
        rw [hCeq]
        exact hqball
      rcases hqC with ⟨w, hwC, hwq⟩
      let w' : EuclideanSpace ℝ (Fin 2) := WithLp.toLp 2 (fun i : Fin 2 =>
        if i = 0 then z 0 * c - z 1 * s else z 0 * s + z 1 * c)
      have hrot : PlanarRot90 u = (-s) • v + c • PlanarRot90 v := by
        rw [hrep]
        exact PlanarRot90LinearCombination v c s
      have hwq' : chart w' = p + z 0 • u + z 1 • PlanarRot90 u := by
        exact planarChart_rotated_coordinates p v u z c s hrep hrot
      have hww : w = w' := planarChart_injective p v
        (initialDirection_ne (J.successor gamma)) (hwq.trans hwq'.symm)
      refine ⟨w, ⟨hwC, Or.inr ?_⟩, ?_⟩
      · have hD : 0 < c ^ 2 + s ^ 2 :=
          twoRay_coefficient_sq_sum_pos hpos
        rw [hww]
        dsimp [w']
        simp
        exact sub_pos.mp
          (rotated_cross_pos c s (z 0) (z 1) hD hz.2.2.1)
      · exact hwq.trans hqeq'.symm
    · intro q hq
      rcases polygonalArcReverse_terminal_cone_normalize
          (J.successor gamma).1 successor_len vertexR K q hq with
        ⟨z, hz, hqeq⟩
      have hsource : (J.successor gamma).1.source = p := by
        simpa [p] using (J.adjacent_endpoint gamma).symm
      have hdist : dist (J.successor gamma).1.source
          (J.successor gamma).1.vertices[1] = ‖v‖ := by
        exact successor_dist
      refine ⟨z, ?_, ?_⟩
      · refine ⟨?_, Or.inl hz.2.2.2⟩
        have hradorig : z 0 ^ 2 + z 1 ^ 2 <
            (vertexR / dist (J.successor gamma).1.source
              (J.successor gamma).1.vertices[1]) ^ 2 := by
          exact hz.2.1
        have hrad' : z 0 ^ 2 + z 1 ^ 2 < (vertexR / ‖v‖) ^ 2 :=
          (congrArg (fun r : ℝ => z 0 ^ 2 + z 1 ^ 2 < r)
            (congrArg (fun x : ℝ => (vertexR / x) ^ 2) hdist)).mp hradorig
        apply fin2_mem_ball_zero_of_sq_sum_lt z a ha.le
        simpa only [a] using hrad'
      · change p + z 0 • v + z 1 • PlanarRot90 v = q
        rw [successor_direction]
        rw [← hsource]
        exact hqeq

-- [TABLET NODE: JordanCurveSimultaneousCollarDataExists]
private def jordanVertexSectorPreparation
    (J : SimpleClosedPolygonalCurve) :
    JordanVertexSectorPreparation J := by
-- BODY
  classical
  let Edge := {gamma : PolygonalArc // gamma ∈ J.edgeArcs}
  have edge_nonempty : Nonempty Edge := by
    rcases J.edgeArcs_nonempty with ⟨gamma, hgamma⟩
    exact ⟨⟨gamma, hgamma⟩⟩
  letI : Nonempty Edge := edge_nonempty
  let presentation : FinitePolygonalSet :=
    Classical.choose (SimpleClosedCurveAsFinitePolygonalSet J)
  have presentation_carrier_eq : presentation.carrier = J.carrier :=
    Classical.choose_spec (SimpleClosedCurveAsFinitePolygonalSet J)
  have arc_ends_ne (Q : PolygonalArc) : Q.source ≠ Q.target := by
    intro h
    have hlen := Q.length_ge_two
    have hzero : Q.vertices[0] = Q.source := by
      have hh := Q.source_eq_head
      rw [List.head?_eq_getElem?, List.getElem?_eq_getElem (by omega)] at hh
      exact Option.some.inj hh
    have hlast : Q.vertices[Q.vertices.length - 1] = Q.target := by
      have ht := Q.target_eq_last
      rw [List.getLast?_eq_getElem?, List.getElem?_eq_getElem (by omega)] at ht
      exact Option.some.inj ht
    have hidx := (Q.simple_vertices.getElem_inj_iff
      (i := 0) (j := Q.vertices.length - 1)
      (hi := by omega) (hj := by omega)).1 (by rw [hzero, hlast, h])
    omega
  have arc_source_mem (Q : PolygonalArc) : Q.source ∈ Q.carrier := by
    have hlen := Q.length_ge_two
    rw [Q.carrier_eq]
    have hfirst : 0 + 1 < Q.vertices.length := by omega
    refine ⟨0, hfirst, ?_⟩
    have hzero : Q.vertices[0] = Q.source := by
      have hh := Q.source_eq_head
      rw [List.head?_eq_getElem?, List.getElem?_eq_getElem (by omega)] at hh
      exact Option.some.inj hh
    simpa [hzero] using left_mem_segment ℝ Q.source Q.vertices[1]
  have arc_target_mem (Q : PolygonalArc) : Q.target ∈ Q.carrier := by
    have hlen := Q.length_ge_two
    rw [Q.carrier_eq]
    let i := Q.vertices.length - 2
    have hi : i + 1 < Q.vertices.length := by
      dsimp [i]
      omega
    refine ⟨i, hi, ?_⟩
    have hlast : Q.vertices[Q.vertices.length - 1] = Q.target := by
      have ht := Q.target_eq_last
      rw [List.getLast?_eq_getElem?, List.getElem?_eq_getElem (by omega)] at ht
      exact Option.some.inj ht
    have hi_succ : i + 1 = Q.vertices.length - 1 := by
      dsimp [i]
      omega
    simpa [hi_succ, hlast] using right_mem_segment ℝ Q.vertices[i] Q.target
  have target_injective : Function.Injective (fun gamma : Edge => gamma.1.target) := by
    intro gamma delta htarget
    change gamma.1.target = delta.1.target at htarget
    by_contra hne
    by_cases hsucc : delta = J.successor gamma
    · have hsource_target : delta.1.source = delta.1.target := by
        calc
          delta.1.source = gamma.1.target := by
            rw [hsucc, J.adjacent_endpoint gamma]
          _ = delta.1.target := htarget
      exact arc_ends_ne delta.1 hsource_target
    · by_cases hpred : J.successor delta = gamma
      · have hsource_target : gamma.1.source = gamma.1.target := by
          calc
            gamma.1.source = delta.1.target := by
              rw [← hpred, ← J.adjacent_endpoint delta]
            _ = gamma.1.target := htarget.symm
        exact arc_ends_ne gamma.1 hsource_target
      · have hdisj := J.nonadjacent_disjoint gamma delta (Ne.symm hne) hsucc hpred
        exact (Set.disjoint_left.mp hdisj (arc_target_mem gamma.1))
          (by rw [htarget]; exact arc_target_mem delta.1)
  have target_not_nonincident (gamma delta : Edge)
      (hne : delta ≠ gamma) (hsucc : delta ≠ J.successor gamma) :
      gamma.1.target ∉ delta.1.carrier := by
    intro hmem
    by_cases hpred : J.successor delta = gamma
    · have hinter : gamma.1.target ∈
          delta.1.carrier ∩ (J.successor delta).1.carrier := by
        refine ⟨hmem, ?_⟩
        rw [hpred]
        exact arc_target_mem gamma.1
      rw [J.adjacent_intersection delta] at hinter
      have heq : gamma.1.target = delta.1.target := by simpa using hinter
      have hsource_target : gamma.1.source = gamma.1.target := by
        calc
          gamma.1.source = delta.1.target := by
            rw [← hpred, ← J.adjacent_endpoint delta]
          _ = gamma.1.target := heq.symm
      exact arc_ends_ne gamma.1 hsource_target
    · have hdisj := J.nonadjacent_disjoint gamma delta hne hsucc hpred
      exact (Set.disjoint_left.mp hdisj (arc_target_mem gamma.1)) hmem
  let isoSource : Edge → ℝ := fun gamma =>
    Classical.choose (PolygonalArcEndpointIsolationExists gamma.1)
  let isoTarget : Edge → ℝ := fun gamma =>
    Classical.choose
      (Classical.choose_spec (PolygonalArcEndpointIsolationExists gamma.1))
  have iso (gamma : Edge) :
      PolygonalArcEndpointIsolation gamma.1 (isoSource gamma) (isoTarget gamma) := by
    exact Classical.choose_spec
      (Classical.choose_spec (PolygonalArcEndpointIsolationExists gamma.1))
  have carrier_separation (gamma delta : Edge)
      (hne : delta ≠ gamma) (hsucc : delta ≠ J.successor gamma) :
      ∃ d : ℝ, 0 < d ∧ ∀ z ∈ delta.1.carrier, d ≤ dist gamma.1.target z := by
    have hdisj : Disjoint ({gamma.1.target} : Set _) delta.1.carrier := by
      rw [Set.disjoint_left]
      intro z hz hzd
      have hz_eq : z = gamma.1.target := by simpa using hz
      exact target_not_nonincident gamma delta hne hsucc (hz_eq ▸ hzd)
    obtain ⟨d, hd, hbound⟩ := PositiveSeparation
      (Set.singleton_nonempty gamma.1.target) ⟨delta.1.source, arc_source_mem delta.1⟩
      isCompact_singleton (PolygonalArcCarrierCompact delta.1) hdisj
    exact ⟨d, hd, fun z hz => hbound gamma.1.target (by simp) z hz⟩
  let carrierMargin : Edge × Edge → ℝ := fun gd =>
    if h : gd.2 = gd.1 ∨ gd.2 = J.successor gd.1 then 1
    else Classical.choose (carrier_separation gd.1 gd.2
      (not_or.mp h).1 (not_or.mp h).2)
  have carrierMargin_pos (gd : Edge × Edge) : 0 < carrierMargin gd := by
    dsimp [carrierMargin]
    split
    · norm_num
    · exact (Classical.choose_spec (carrier_separation gd.1 gd.2
        (not_or.mp ‹¬ (gd.2 = gd.1 ∨ gd.2 = J.successor gd.1)›).1
        (not_or.mp ‹¬ (gd.2 = gd.1 ∨ gd.2 = J.successor gd.1)›).2)).1
  have carrierMargin_le (gamma delta : Edge)
      (hne : delta ≠ gamma) (hsucc : delta ≠ J.successor gamma)
      (z) (hz : z ∈ delta.1.carrier) :
      carrierMargin (gamma, delta) ≤ dist gamma.1.target z := by
    dsimp [carrierMargin]
    simp only [hne, hsucc, or_false, ↓reduceDIte]
    exact (Classical.choose_spec
      (carrier_separation gamma delta hne hsucc)).2 z hz
  have finite_small (f : Edge × Edge → ℝ) (hf : ∀ a, 0 < f a) :
      ∃ r : ℝ, 0 < r ∧ ∀ a, r < f a := by
    let values : Finset ℝ := Finset.univ.image f
    have hvalues : values.Nonempty := by
      let a : Edge × Edge := Classical.choice inferInstance
      exact ⟨f a, Finset.mem_image.mpr ⟨a, Finset.mem_univ a, rfl⟩⟩
    let m : ℝ := values.min' hvalues
    have hm_pos : 0 < m := by
      have hm_mem := Finset.min'_mem values hvalues
      rcases Finset.mem_image.mp hm_mem with ⟨a, _ha, haeq⟩
      change 0 < values.min' hvalues
      rw [← haeq]
      exact hf a
    refine ⟨m / 2, by linarith, ?_⟩
    intro a
    have hm_le : m ≤ f a := Finset.min'_le values (f a)
      (Finset.mem_image.mpr ⟨a, Finset.mem_univ a, rfl⟩)
    linarith
  let allBound : Edge × Edge → ℝ := fun gd =>
    min (isoSource gd.1) <|
      min (isoTarget gd.1) <|
        min (carrierMargin gd) <|
          if gd.1 = gd.2 then 1 else dist gd.1.1.target gd.2.1.target / 3
  have allBound_pos (gd : Edge × Edge) : 0 < allBound gd := by
    dsimp [allBound]
    have hs := (iso gd.1).source_pos
    have ht := (iso gd.1).target_pos
    have hc := carrierMargin_pos gd
    by_cases heq : gd.1 = gd.2
    · rw [if_pos heq]
      exact lt_min hs (lt_min ht (lt_min hc zero_lt_one))
    · have hd : 0 < dist gd.1.1.target gd.2.1.target :=
        dist_pos.mpr (target_injective.ne heq)
      rw [if_neg heq]
      exact lt_min hs (lt_min ht (lt_min hc (div_pos hd (by norm_num))))
  let vertexR : ℝ :=
    Classical.choose (finite_small (f := allBound) allBound_pos)
  have vertexR_spec :
      0 < vertexR ∧ ∀ a : Edge × Edge, vertexR < allBound a :=
    Classical.choose_spec (finite_small (f := allBound) allBound_pos)
  have vertexR_pos : 0 < vertexR := vertexR_spec.1
  have vertexR_lt : ∀ a : Edge × Edge, vertexR < allBound a :=
    vertexR_spec.2
  have vertexR_quarter_lt_half : vertexR / 4 < vertexR / 2 :=
    quarter_lt_half vertexR_pos
  have vertexR_lt_source (gamma : Edge) : vertexR < isoSource gamma := by
    exact (lt_min_iff.mp (vertexR_lt (gamma, gamma))).1
  have vertexR_lt_target (gamma : Edge) : vertexR < isoTarget gamma := by
    have h := vertexR_lt (gamma, gamma)
    dsimp [allBound] at h
    exact (lt_min_iff.mp (lt_min_iff.mp h).2).1
  have vertexR_lt_margin (gamma delta : Edge) :
      vertexR < carrierMargin (gamma, delta) := by
    have h := vertexR_lt (gamma, delta)
    dsimp [allBound] at h
    exact (lt_min_iff.mp (lt_min_iff.mp (lt_min_iff.mp h).2).2).1
  have vertexR_pair (gamma delta : Edge) (hne : gamma ≠ delta) :
      vertexR + vertexR < dist gamma.1.target delta.1.target := by
    have h := vertexR_lt (gamma, delta)
    dsimp [allBound] at h
    simp [hne] at h
    have hthird : vertexR < dist gamma.1.target delta.1.target / 3 :=
      h.2.2.2
    have hd : 0 < dist gamma.1.target delta.1.target :=
      dist_pos.mpr (target_injective.ne hne)
    linarith
  let vertexRadius : Edge → ℝ := fun _ => vertexR
  have endpointIsolation (gamma : Edge) :
      PolygonalArcEndpointIsolation gamma.1
        (vertexRadius (J.successor.symm gamma)) (vertexRadius gamma) := by
    have hIso := iso gamma
    have hsle : vertexR ≤ isoSource gamma := (vertexR_lt_source gamma).le
    have htle : vertexR ≤ isoTarget gamma := (vertexR_lt_target gamma).le
    refine
      { source_pos := by simpa [vertexRadius] using vertexR_pos
        target_pos := by simpa [vertexRadius] using vertexR_pos
        source_lt_initial_length := by
          simpa [vertexRadius] using (vertexR_lt_source gamma).trans
            hIso.source_lt_initial_length
        target_lt_terminal_length := by
          simpa [vertexRadius] using (vertexR_lt_target gamma).trans
            hIso.target_lt_terminal_length
        endpoint_closedBalls_disjoint := by
          exact hIso.endpoint_closedBalls_disjoint.mono
            (Metric.closedBall_subset_closedBall hsle)
            (Metric.closedBall_subset_closedBall htle)
        source_closedBall_carrier_subset_initial_segment := by
          dsimp
          intro z hz
          exact hIso.source_closedBall_carrier_subset_initial_segment
            ⟨Metric.closedBall_subset_closedBall hsle hz.1, hz.2⟩
        target_closedBall_carrier_subset_terminal_segment := by
          dsimp
          intro z hz
          exact hIso.target_closedBall_carrier_subset_terminal_segment
            ⟨Metric.closedBall_subset_closedBall htle hz.1, hz.2⟩ }
  have vertexClosedDisks_disjoint (gamma delta : Edge) (hne : gamma ≠ delta) :
      Disjoint (Metric.closedBall gamma.1.target (vertexRadius gamma))
        (Metric.closedBall delta.1.target (vertexRadius delta)) := by
    apply Metric.closedBall_disjoint_closedBall
    simpa [vertexRadius] using vertexR_pair gamma delta hne
  have vertexDisk_curve_eq (gamma : Edge) :
      Metric.ball gamma.1.target (vertexRadius gamma) ∩ J.carrier =
        Metric.ball gamma.1.target (vertexRadius gamma) ∩
          (gamma.1.carrier ∪ (J.successor gamma).1.carrier) := by
    ext z
    constructor
    · rintro ⟨hzball, hzJ⟩
      rw [J.carrier_eq] at hzJ
      rcases Set.mem_iUnion.mp hzJ with ⟨delta, hzdelta⟩
      refine ⟨hzball, ?_⟩
      by_cases heq : delta = gamma
      · exact Or.inl (heq ▸ hzdelta)
      · by_cases hsucc : delta = J.successor gamma
        · exact Or.inr (hsucc ▸ hzdelta)
        · exfalso
          have hm := carrierMargin_le gamma delta heq hsucc z hzdelta
          have hrm := vertexR_lt_margin gamma delta
          have hzdist : dist gamma.1.target z < vertexR := by
            simpa [vertexRadius, dist_comm] using hzball
          linarith
    · rintro ⟨hzball, hz⟩
      refine ⟨hzball, ?_⟩
      rw [J.carrier_eq]
      rcases hz with hz | hz
      · exact Set.mem_iUnion.mpr ⟨gamma, hz⟩
      · exact Set.mem_iUnion.mpr ⟨J.successor gamma, hz⟩
  have terminalDirection_ne (gamma : Edge) : terminalDirection gamma ≠ 0 := by
    have hdist : 0 < PolygonalArcTerminalEndpointSegmentLength gamma.1 :=
      (endpointIsolation gamma).target_pos.trans
        (endpointIsolation gamma).target_lt_terminal_length
    rw [PolygonalArcTerminalEndpointSegmentLength] at hdist
    exact sub_ne_zero.mpr (dist_pos.mp hdist).symm
  have initialDirection_ne (gamma : Edge) : initialDirection gamma ≠ 0 := by
    have hdist : 0 < PolygonalArcInitialEndpointSegmentLength gamma.1 :=
      (endpointIsolation gamma).source_pos.trans
        (endpointIsolation gamma).source_lt_initial_length
    rw [PolygonalArcInitialEndpointSegmentLength] at hdist
    exact sub_ne_zero.mpr (dist_pos.mp hdist).symm
  have terminal_ball_carrier_eq (gamma : Edge) :
      Metric.ball gamma.1.target vertexR ∩ gamma.1.carrier =
        {q | q ∈ Metric.ball gamma.1.target vertexR ∧
          (q = gamma.1.target ∨ ∃ t : ℝ, 0 < t ∧
            q = gamma.1.target + t • terminalDirection gamma)} := by
    have hlen := gamma.1.length_ge_two
    ext q
    constructor
    · rintro ⟨hqball, hqcarrier⟩
      have hqclosed : q ∈ Metric.closedBall gamma.1.target vertexR :=
        Metric.ball_subset_closedBall hqball
      have hqsegment :=
        (endpointIsolation gamma).target_closedBall_carrier_subset_terminal_segment
          ⟨hqclosed, hqcarrier⟩
      rw [segment_eq_image_lineMap] at hqsegment
      rcases hqsegment with ⟨t, ht, hq⟩
      refine ⟨hqball, ?_⟩
      by_cases ht0 : t = 0
      · left
        simpa [ht0, AffineMap.lineMap_apply_module] using hq.symm
      · right
        refine ⟨t, lt_of_le_of_ne ht.1 (Ne.symm ht0), ?_⟩
        rw [← hq]
        apply PiLp.ext
        intro k
        fin_cases k <;>
          simp [terminalDirection, AffineMap.lineMap_apply_module] <;> ring
    · rintro ⟨hqball, hqeq | ⟨t, ht, hqeq⟩⟩
      · exact ⟨hqball, hqeq ▸ arc_target_mem gamma.1⟩
      · refine ⟨hqball, ?_⟩
        have hnorm :
            dist (gamma.1.target + t • terminalDirection gamma) gamma.1.target =
              t * ‖terminalDirection gamma‖ := by
          rw [dist_eq_norm]
          have hsub : gamma.1.target + t • terminalDirection gamma - gamma.1.target =
              t • terminalDirection gamma := by abel
          rw [hsub, norm_smul, Real.norm_eq_abs, abs_of_pos ht]
        have hR_lt_norm : vertexR < ‖terminalDirection gamma‖ := by
          have h : vertexR < PolygonalArcTerminalEndpointSegmentLength gamma.1 := by
            simpa [vertexRadius] using
              (endpointIsolation gamma).target_lt_terminal_length
          rw [PolygonalArcTerminalEndpointSegmentLength, dist_eq_norm] at h
          have hneg : gamma.1.target -
              gamma.1.vertices[gamma.1.vertices.length - 2] =
                -(terminalDirection gamma) := by
            dsimp [terminalDirection]
            abel
          simpa [hneg] using h
        have ht_lt_one : t < 1 := by
          rw [hqeq, Metric.mem_ball, hnorm] at hqball
          have hnpos := norm_pos_iff.mpr (terminalDirection_ne gamma)
          nlinarith
        rw [gamma.1.carrier_eq]
        let j := gamma.1.vertices.length - 2
        have hj : j + 1 < gamma.1.vertices.length := by
          dsimp [j]
          omega
        have hjlast : gamma.1.vertices[j + 1] = gamma.1.target := by
          have htgt := gamma.1.target_eq_last
          rw [List.getLast?_eq_getElem?, List.getElem?_eq_getElem (by omega)] at htgt
          have hidx : j + 1 = gamma.1.vertices.length - 1 := by
            dsimp [j]
            omega
          simpa [hidx] using Option.some.inj htgt
        refine ⟨j, hj, ?_⟩
        rw [segment_eq_image_lineMap]
        refine ⟨1 - t, ⟨by linarith, by linarith⟩, ?_⟩
        rw [hqeq]
        apply PiLp.ext
        intro k
        fin_cases k <;>
          simp [j, terminalDirection, hjlast, AffineMap.lineMap_apply_module] <;> ring
  have initial_ball_carrier_eq (gamma : Edge) :
      Metric.ball gamma.1.source vertexR ∩ gamma.1.carrier =
        {q | q ∈ Metric.ball gamma.1.source vertexR ∧
          (q = gamma.1.source ∨ ∃ t : ℝ, 0 < t ∧
            q = gamma.1.source + t • initialDirection gamma)} := by
    have hlen := gamma.1.length_ge_two
    ext q
    constructor
    · rintro ⟨hqball, hqcarrier⟩
      have hqclosed : q ∈ Metric.closedBall gamma.1.source vertexR :=
        Metric.ball_subset_closedBall hqball
      have hqsegment :=
        (endpointIsolation gamma).source_closedBall_carrier_subset_initial_segment
          ⟨hqclosed, hqcarrier⟩
      rw [segment_eq_image_lineMap] at hqsegment
      rcases hqsegment with ⟨t, ht, hq⟩
      refine ⟨hqball, ?_⟩
      by_cases ht0 : t = 0
      · left
        simpa [ht0, AffineMap.lineMap_apply_module] using hq.symm
      · right
        refine ⟨t, lt_of_le_of_ne ht.1 (Ne.symm ht0), ?_⟩
        rw [← hq]
        apply PiLp.ext
        intro k
        fin_cases k <;>
          simp [initialDirection, AffineMap.lineMap_apply_module] <;> ring
    · rintro ⟨hqball, hqeq | ⟨t, ht, hqeq⟩⟩
      · exact ⟨hqball, hqeq ▸ arc_source_mem gamma.1⟩
      · refine ⟨hqball, ?_⟩
        have hnorm :
            dist (gamma.1.source + t • initialDirection gamma) gamma.1.source =
              t * ‖initialDirection gamma‖ := by
          rw [dist_eq_norm]
          have hsub : gamma.1.source + t • initialDirection gamma - gamma.1.source =
              t • initialDirection gamma := by abel
          rw [hsub, norm_smul, Real.norm_eq_abs, abs_of_pos ht]
        have hR_lt_norm : vertexR < ‖initialDirection gamma‖ := by
          have h : vertexR < PolygonalArcInitialEndpointSegmentLength gamma.1 := by
            simpa [vertexRadius] using
              (endpointIsolation gamma).source_lt_initial_length
          rw [PolygonalArcInitialEndpointSegmentLength, dist_eq_norm] at h
          have hneg : gamma.1.source - gamma.1.vertices[1] =
              -(initialDirection gamma) := by
            dsimp [initialDirection]
            abel
          calc
            vertexR < ‖gamma.1.source - gamma.1.vertices[1]‖ := h
            _ = ‖initialDirection gamma‖ := by rw [hneg, norm_neg]
        have ht_lt_one : t < 1 := by
          rw [hqeq, Metric.mem_ball, hnorm] at hqball
          have hnpos := norm_pos_iff.mpr (initialDirection_ne gamma)
          nlinarith
        rw [gamma.1.carrier_eq]
        have hfirst : 0 + 1 < gamma.1.vertices.length := by omega
        have hzero : gamma.1.vertices[0] = gamma.1.source := by
          have hsrc := gamma.1.source_eq_head
          rw [List.head?_eq_getElem?, List.getElem?_eq_getElem (by omega)] at hsrc
          exact Option.some.inj hsrc
        refine ⟨0, hfirst, ?_⟩
        rw [segment_eq_image_lineMap]
        refine ⟨t, ⟨ht.le, ht_lt_one.le⟩, ?_⟩
        rw [hqeq]
        apply PiLp.ext
        intro k
        fin_cases k <;>
          simp [initialDirection, hzero, AffineMap.lineMap_apply_module] <;> ring
  have adjacent_directions_not_same (gamma : Edge) :
      ¬ ∃ a : ℝ, 0 < a ∧
        initialDirection (J.successor gamma) = a • terminalDirection gamma := by
    rintro ⟨a, ha, hdir⟩
    let tau : ℝ := min (1 / 2 : ℝ) (1 / (2 * a))
    have htau_pos : 0 < tau := by
      dsimp [tau]
      exact lt_min (by norm_num) (one_div_pos.mpr (by positivity))
    have htau_lt_one : tau < 1 := by
      have hle : tau ≤ 1 / 2 := min_le_left _ _
      linarith
    have hataule : a * tau ≤ 1 / 2 := by
      have hle : tau ≤ 1 / (2 * a) := min_le_right _ _
      have := mul_le_mul_of_nonneg_left hle ha.le
      have hcalc : a * (1 / (2 * a)) = 1 / 2 := by
        field_simp [ne_of_gt ha]
      linarith
    have hatau_pos : 0 < a * tau := mul_pos ha htau_pos
    have hatau_lt_one : a * tau < 1 := by linarith
    let q : EuclideanSpace ℝ (Fin 2) :=
      gamma.1.target + tau • initialDirection (J.successor gamma)
    have q_mem_successor : q ∈ (J.successor gamma).1.carrier := by
      rw [(J.successor gamma).1.carrier_eq]
      have hfirst : 0 + 1 < (J.successor gamma).1.vertices.length := by
        have hlen := (J.successor gamma).1.length_ge_two
        omega
      refine ⟨0, hfirst, ?_⟩
      rw [segment_eq_image_lineMap]
      refine ⟨tau, ⟨htau_pos.le, htau_lt_one.le⟩, ?_⟩
      have hsource : (J.successor gamma).1.source = gamma.1.target :=
        (J.adjacent_endpoint gamma).symm
      have hzero : (J.successor gamma).1.vertices[0] =
          (J.successor gamma).1.source := by
        have hs := (J.successor gamma).1.source_eq_head
        rw [List.head?_eq_getElem?, List.getElem?_eq_getElem (by omega)] at hs
        exact Option.some.inj hs
      apply PiLp.ext
      intro k
      fin_cases k <;>
        simp [q, initialDirection, hsource, hzero,
          AffineMap.lineMap_apply_module] <;> ring
    have q_mem_gamma : q ∈ gamma.1.carrier := by
      rw [gamma.1.carrier_eq]
      let j := gamma.1.vertices.length - 2
      have hj : j + 1 < gamma.1.vertices.length := by
        have hlen := gamma.1.length_ge_two
        dsimp [j]
        omega
      refine ⟨j, hj, ?_⟩
      rw [segment_eq_image_lineMap]
      refine ⟨1 - a * tau, ⟨by linarith, by linarith⟩, ?_⟩
      have hjlast : gamma.1.vertices[j + 1] = gamma.1.target := by
        have ht := gamma.1.target_eq_last
        rw [List.getLast?_eq_getElem?, List.getElem?_eq_getElem (by omega)] at ht
        have hidx : j + 1 = gamma.1.vertices.length - 1 := by
          dsimp [j]
          omega
        simpa [hidx] using Option.some.inj ht
      apply PiLp.ext
      intro k
      have hdirk := congrArg (fun x : EuclideanSpace ℝ (Fin 2) => x k) hdir
      fin_cases k <;>
        simp [q, terminalDirection, initialDirection, hjlast,
          AffineMap.lineMap_apply_module] at hdirk ⊢ <;> nlinarith
    have q_eq_target : q = gamma.1.target := by
      have hqinter : q ∈ gamma.1.carrier ∩ (J.successor gamma).1.carrier :=
        ⟨q_mem_gamma, q_mem_successor⟩
      rw [J.adjacent_intersection gamma] at hqinter
      simpa using hqinter
    have hzero : tau • initialDirection (J.successor gamma) = 0 := by
      have : q - gamma.1.target = 0 := sub_eq_zero.mpr q_eq_target
      simpa [q] using this
    exact initialDirection_ne (J.successor gamma)
      ((smul_eq_zero.mp hzero).resolve_left (ne_of_gt htau_pos))
  have vertex_ball_curve_as_rays (gamma : Edge) :
      Metric.ball gamma.1.target vertexR ∩ J.carrier =
        {q | q ∈ Metric.ball gamma.1.target vertexR ∧
          ∃ t : ℝ, 0 < t ∧ q = gamma.1.target + t • terminalDirection gamma} ∪
        {q | q ∈ Metric.ball gamma.1.target vertexR ∧
          ∃ t : ℝ, 0 < t ∧
            q = gamma.1.target + t • initialDirection (J.successor gamma)} ∪
        ({gamma.1.target} : Set (EuclideanSpace ℝ (Fin 2))) := by
    have hsuccSource : (J.successor gamma).1.source = gamma.1.target :=
      (J.adjacent_endpoint gamma).symm
    ext q
    constructor
    · intro hq
      change q ∈ Metric.ball gamma.1.target (vertexRadius gamma) ∩ J.carrier at hq
      have hq' : q ∈ Metric.ball gamma.1.target vertexR ∩
          (gamma.1.carrier ∪ (J.successor gamma).1.carrier) := by
        rw [← vertexDisk_curve_eq gamma]
        exact hq
      rcases hq' with ⟨hqball, hqgamma | hqsucc⟩
      · have ht := Set.ext_iff.mp (terminal_ball_carrier_eq gamma) q |>.mp
          ⟨hqball, hqgamma⟩
        rcases ht.2 with hqp | ht
        · exact Or.inr (by simpa [hqp])
        · exact Or.inl (Or.inl ⟨hqball, ht⟩)
      · have hs := Set.ext_iff.mp (initial_ball_carrier_eq (J.successor gamma)) q |>.mp
          ⟨by simpa [hsuccSource] using hqball, hqsucc⟩
        rcases hs.2 with hqp | hs
        · exact Or.inr (by simpa [hsuccSource] using hqp)
        · exact Or.inl (Or.inr ⟨hqball, by simpa [hsuccSource] using hs⟩)
    · intro hq
      have hqball : q ∈ Metric.ball gamma.1.target vertexR := by
        rcases hq with (hq | hq) | hq
        · exact hq.1
        · exact hq.1
        · have hqp : q = gamma.1.target := by simpa using hq
          simpa [hqp] using vertexR_pos
      refine ⟨hqball, ?_⟩
      rw [J.carrier_eq]
      rcases hq with (hq | hq) | hq
      · apply Set.mem_iUnion.mpr
        refine ⟨gamma, ?_⟩
        exact ((Set.ext_iff.mp (terminal_ball_carrier_eq gamma) q).mpr
          ⟨hq.1, Or.inr hq.2⟩).2
      · apply Set.mem_iUnion.mpr
        refine ⟨J.successor gamma, ?_⟩
        exact ((Set.ext_iff.mp (initial_ball_carrier_eq (J.successor gamma)) q).mpr
          ⟨by simpa [hsuccSource] using hq.1,
            Or.inr (by simpa [hsuccSource] using hq.2)⟩).2
      · have hqp : q = gamma.1.target := by simpa using hq
        exact Set.mem_iUnion.mpr ⟨gamma, hqp ▸ arc_target_mem gamma.1⟩
  have origin_mem_twoRay_left_closure (a c s : ℝ) (ha : 0 < a)
      (hpos : 0 < s ∨ s = 0 ∧ c < 0) :
      (0 : EuclideanSpace ℝ (Fin 2)) ∈ closure
        {z | z ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) a ∧
          0 < z 1 ∧ c * z 1 - s * z 0 < 0} := by
    let w : EuclideanSpace ℝ (Fin 2) :=
      if 0 < s then
        WithLp.toLp 2 (fun i : Fin 2 => if i = 0 then c + 1 else s)
      else
        WithLp.toLp 2 (fun i : Fin 2 => if i = 0 then 0 else 1)
    have hw1 : 0 < w 1 := by
      dsimp [w]
      split_ifs with hs
      · simpa using hs
      · norm_num
    have hwcross : c * w 1 - s * w 0 < 0 := by
      dsimp [w]
      split_ifs with hs
      · simp
        nlinarith
      · simp
        rcases hpos with hs' | ⟨hs0, hc⟩
        · exact (hs hs').elim
        · nlinarith
    rw [Metric.mem_closure_iff]
    intro eps heps
    let B : ℝ := ‖w‖ + 1
    have hB : 0 < B := by positivity
    let d : ℝ := min (a / (2 * B)) (eps / (2 * B))
    have hd : 0 < d := by
      dsimp [d]
      positivity
    have hdB_a : d * B ≤ a / 2 := by
      have hle : d ≤ a / (2 * B) := min_le_left _ _
      calc
        d * B ≤ (a / (2 * B)) * B :=
          mul_le_mul_of_nonneg_right hle hB.le
        _ = a / 2 := by field_simp [hB.ne']
    have hdB_eps : d * B ≤ eps / 2 := by
      have hle : d ≤ eps / (2 * B) := min_le_right _ _
      calc
        d * B ≤ (eps / (2 * B)) * B :=
          mul_le_mul_of_nonneg_right hle hB.le
        _ = eps / 2 := by field_simp [hB.ne']
    let y := d • w
    refine ⟨y, ?_, ?_⟩
    · refine ⟨?_, ?_, ?_⟩
      · rw [Metric.mem_ball, dist_zero_right, norm_smul, Real.norm_eq_abs,
          abs_of_pos hd]
        have hwle : ‖w‖ ≤ B := by dsimp [B]; linarith [norm_nonneg w]
        have := mul_le_mul_of_nonneg_left hwle hd.le
        nlinarith
      · change 0 < d * w 1
        exact mul_pos hd hw1
      · change c * (d * w 1) - s * (d * w 0) < 0
        nlinarith [mul_pos hd (neg_pos.mpr hwcross)]
    · rw [dist_zero_left, norm_smul, Real.norm_eq_abs, abs_of_pos hd]
      have hwle : ‖w‖ ≤ B := by dsimp [B]; linarith [norm_nonneg w]
      have := mul_le_mul_of_nonneg_left hwle hd.le
      nlinarith
  have origin_mem_twoRay_right_closure (a c s : ℝ) (ha : 0 < a) :
      (0 : EuclideanSpace ℝ (Fin 2)) ∈ closure
        {z | z ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) a ∧
          (z 1 < 0 ∨ 0 < c * z 1 - s * z 0)} := by
    let w : EuclideanSpace ℝ (Fin 2) :=
      WithLp.toLp 2 (fun i : Fin 2 => if i = 0 then 0 else -1)
    rw [Metric.mem_closure_iff]
    intro eps heps
    let B : ℝ := ‖w‖ + 1
    have hB : 0 < B := by positivity
    let d : ℝ := min (a / (2 * B)) (eps / (2 * B))
    have hd : 0 < d := by
      dsimp [d]
      positivity
    have hdB_a : d * B ≤ a / 2 := by
      have hle : d ≤ a / (2 * B) := min_le_left _ _
      calc
        d * B ≤ (a / (2 * B)) * B :=
          mul_le_mul_of_nonneg_right hle hB.le
        _ = a / 2 := by field_simp [hB.ne']
    have hdB_eps : d * B ≤ eps / 2 := by
      have hle : d ≤ eps / (2 * B) := min_le_right _ _
      calc
        d * B ≤ (eps / (2 * B)) * B :=
          mul_le_mul_of_nonneg_right hle hB.le
        _ = eps / 2 := by field_simp [hB.ne']
    let y := d • w
    refine ⟨y, ?_, ?_⟩
    · refine ⟨?_, Or.inl ?_⟩
      · rw [Metric.mem_ball, dist_zero_right, norm_smul, Real.norm_eq_abs,
          abs_of_pos hd]
        have hwle : ‖w‖ ≤ B := by dsimp [B]; linarith [norm_nonneg w]
        have := mul_le_mul_of_nonneg_left hwle hd.le
        nlinarith
      · change d * w 1 < 0
        simp [w, hd]
    · rw [dist_zero_left, norm_smul, Real.norm_eq_abs, abs_of_pos hd]
      have hwle : ‖w‖ ≤ B := by dsimp [B]; linarith [norm_nonneg w]
      have := mul_le_mul_of_nonneg_left hwle hd.le
      nlinarith
  have planarChart_injective (p d : EuclideanSpace ℝ (Fin 2)) (hd : d ≠ 0) :
      Function.Injective (fun z : EuclideanSpace ℝ (Fin 2) =>
        p + z 0 • d + z 1 • PlanarRot90 d) := by
    intro z w hzw
    have hrep : (0 : EuclideanSpace ℝ (Fin 2)) =
        (z 0 - w 0) • d + (z 1 - w 1) • PlanarRot90 d := by
      have hzero :
          (p + z 0 • d + z 1 • PlanarRot90 d) -
              (p + w 0 • d + w 1 • PlanarRot90 d) = 0 :=
        sub_eq_zero.mpr hzw
      apply PiLp.ext
      intro k
      have hk := congrArg (fun x : EuclideanSpace ℝ (Fin 2) => x k) hzero
      fin_cases k <;> simp at hk ⊢ <;> linarith
    have hcoeff := PlanarRot90CoefficientUniqueness (d := d)
      (v := (0 : EuclideanSpace ℝ (Fin 2))) hd hrep
    apply PiLp.ext
    intro k
    fin_cases k
    · have hzero : z 0 - w 0 = 0 := by simpa using hcoeff.1
      exact sub_eq_zero.mp hzero
    · have hzero : z 1 - w 1 = 0 := by simpa using hcoeff.2
      exact sub_eq_zero.mp hzero
  have planarChart_radial_subset_ball
      (p d : EuclideanSpace ℝ (Fin 2)) (R : ℝ) (hd : d ≠ 0) (hR : 0 < R) :
      (fun z : EuclideanSpace ℝ (Fin 2) =>
          p + z 0 • d + z 1 • PlanarRot90 d) ''
          {z | z 0 ^ 2 + z 1 ^ 2 < (R / ‖d‖) ^ 2} ⊆
        Metric.ball p R := by
    rintro q ⟨z, hz, rfl⟩
    have horth : inner ℝ (z 0 • d) (z 1 • PlanarRot90 d) = 0 := by
      rw [inner_smul_left, inner_smul_right, PlanarRot90Orthogonal]
      ring
    have hnormsq : ‖z 0 • d + z 1 • PlanarRot90 d‖ ^ 2 =
        (z 0 ^ 2 + z 1 ^ 2) * ‖d‖ ^ 2 := by
      have hpyth := norm_add_sq_eq_norm_sq_add_norm_sq_real horth
      calc
        ‖z 0 • d + z 1 • PlanarRot90 d‖ ^ 2 =
            ‖z 0 • d + z 1 • PlanarRot90 d‖ *
              ‖z 0 • d + z 1 • PlanarRot90 d‖ := by rw [pow_two]
        _ = ‖z 0 • d‖ * ‖z 0 • d‖ +
            ‖z 1 • PlanarRot90 d‖ * ‖z 1 • PlanarRot90 d‖ := hpyth
        _ = (z 0 ^ 2 + z 1 ^ 2) * ‖d‖ ^ 2 := by
          rw [norm_smul, norm_smul, PlanarRot90Norm]
          rw [Real.norm_eq_abs, Real.norm_eq_abs]
          nlinarith [sq_abs (z 0), sq_abs (z 1)]
    have hdnorm : 0 < ‖d‖ := norm_pos_iff.mpr hd
    have hmul := mul_lt_mul_of_pos_right hz (sq_pos_of_pos hdnorm)
    have hscale : (R / ‖d‖) ^ 2 * ‖d‖ ^ 2 = R ^ 2 := by
      field_simp [ne_of_gt hdnorm]
    have hsq : ‖z 0 • d + z 1 • PlanarRot90 d‖ ^ 2 < R ^ 2 := by
      rw [hnormsq]
      simpa [hscale] using hmul
    rw [Metric.mem_ball, dist_eq_norm]
    have hsub : (p + z 0 • d + z 1 • PlanarRot90 d) - p =
        z 0 • d + z 1 • PlanarRot90 d := by abel
    rw [hsub]
    exact (sq_lt_sq₀ (norm_nonneg _) hR.le).mp hsq
  have vertex_sector_exists (gamma : Edge) :=
    jordan_vertex_sector_exists J gamma vertexR vertexR_pos
      terminalDirection_ne initialDirection_ne adjacent_directions_not_same
      origin_mem_twoRay_left_closure origin_mem_twoRay_right_closure
      planarChart_injective planarChart_radial_subset_ball (by
        simpa using (vertex_ball_curve_as_rays gamma).symm)
  choose leftVertexSector rightVertexSector vertexAperture
    hAperturePos hLne hRne hLopen hRopen hLconn hRconn hLdisk hRdisk
    hLcomp hRcomp hdisj hpartition hLclosure hRclosure hterminalLeft
    hsuccessorLeft hterminalRight hsuccessorRight using vertex_sector_exists
  exact {
    edge_nonempty := edge_nonempty
    presentation := presentation
    presentation_carrier_eq := presentation_carrier_eq
    arc_source_mem := arc_source_mem
    vertexR := vertexR
    vertexR_pos := vertexR_pos
    vertexR_quarter_lt_half := vertexR_quarter_lt_half
    endpointIsolation := by
      intro gamma
      simpa only [vertexRadius] using endpointIsolation gamma
    vertexClosedDisks_disjoint := by
      intro gamma delta hne
      simpa only [vertexRadius] using vertexClosedDisks_disjoint gamma delta hne
    vertexDisk_curve_eq := by
      intro gamma
      simpa only [vertexRadius] using vertexDisk_curve_eq gamma
    leftVertexSector := leftVertexSector
    rightVertexSector := rightVertexSector
    vertexAperture := vertexAperture
    hAperturePos := hAperturePos
    hLne := hLne
    hRne := hRne
    hLopen := hLopen
    hRopen := hRopen
    hLconn := hLconn
    hRconn := hRconn
    hLdisk := hLdisk
    hRdisk := hRdisk
    hLcomp := hLcomp
    hRcomp := hRcomp
    hdisj := hdisj
    hpartition := hpartition
    hLclosure := hLclosure
    hRclosure := hRclosure
    hterminalLeft := hterminalLeft
    hsuccessorLeft := hsuccessorLeft
    hterminalRight := hterminalRight
    hsuccessorRight := hsuccessorRight }

private lemma jordanCurveSimultaneousCollarDataExists_of_preparation
    (J : SimpleClosedPolygonalCurve) (prepared : JordanVertexSectorPreparation J) :
    Nonempty (JordanCurveSimultaneousCollarData J) := by
  classical
  let Edge := JordanCurveEdge J
  rcases prepared with
    ⟨edge_nonempty, presentation, presentation_carrier_eq, arc_source_mem,
      vertexR, vertexR_pos, vertexR_quarter_lt_half, endpointIsolation,
      vertexClosedDisks_disjoint, vertexDisk_curve_eq, leftVertexSector,
      rightVertexSector, vertexAperture, hAperturePos, hLne, hRne, hLopen,
      hRopen, hLconn, hRconn, hLdisk, hRdisk, hLcomp, hRcomp, hdisj,
      hpartition, hLclosure, hRclosure, hterminalLeft, hsuccessorLeft,
      hterminalRight, hsuccessorRight⟩
  letI : Nonempty Edge := edge_nonempty
  let vertexRadius : Edge → ℝ := fun _ => vertexR
  let targetAperture : Edge → ℝ := vertexAperture
  let sourceAperture : Edge → ℝ := fun gamma =>
    vertexAperture (J.successor.symm gamma)
  have sourceAperture_pos (gamma : Edge) : 0 < sourceAperture gamma := by
    exact hAperturePos (J.successor.symm gamma)
  have targetAperture_pos (gamma : Edge) : 0 < targetAperture gamma := by
    exact hAperturePos gamma
  let bufferedCore : Edge → Set (EuclideanSpace ℝ (Fin 2)) := fun gamma =>
    gamma.1.carrier \
      (Metric.ball gamma.1.source
          (vertexRadius (J.successor.symm gamma) / 2) ∪
        Metric.ball gamma.1.target (vertexRadius gamma / 2))
  have bufferedCore_compact (gamma : Edge) : IsCompact (bufferedCore gamma) := by
    dsimp [bufferedCore]
    exact (PolygonalArcCarrierCompact gamma.1).diff
      (Metric.isOpen_ball.union Metric.isOpen_ball)
  have bufferedCore_disjoint_other (gamma delta : Edge) (hne : delta ≠ gamma) :
      Disjoint (bufferedCore gamma) delta.1.carrier := by
    dsimp [bufferedCore, vertexRadius]
    exact jordan_bufferedCore_disjoint_other J vertexR vertexR_pos gamma delta hne
  have edge_carrier_nonempty (gamma : Edge) : gamma.1.carrier.Nonempty := by
    exact ⟨gamma.1.source, arc_source_mem gamma.1⟩
  let coreSeparation : Edge → Edge → ℝ := fun gamma delta =>
    if h : (bufferedCore gamma).Nonempty ∧ delta ≠ gamma then
      Classical.choose
        (PositiveSeparation h.1 (edge_carrier_nonempty delta)
          (bufferedCore_compact gamma) (PolygonalArcCarrierCompact delta.1)
          (bufferedCore_disjoint_other gamma delta h.2))
    else
      1
  have coreSeparation_spec (gamma delta : Edge)
      (h : (bufferedCore gamma).Nonempty ∧ delta ≠ gamma) :
      0 < coreSeparation gamma delta ∧
        ∀ p, p ∈ bufferedCore gamma → ∀ z, z ∈ delta.1.carrier →
          coreSeparation gamma delta ≤ dist p z := by
    dsimp only [coreSeparation]
    rw [dif_pos h]
    exact Classical.choose_spec
      (PositiveSeparation h.1 (edge_carrier_nonempty delta)
        (bufferedCore_compact gamma) (PolygonalArcCarrierCompact delta.1)
        (bufferedCore_disjoint_other gamma delta h.2))
  have coreSeparation_pos (gamma delta : Edge) :
      0 < coreSeparation gamma delta := by
    by_cases h : (bufferedCore gamma).Nonempty ∧ delta ≠ gamma
    · exact (coreSeparation_spec gamma delta h).1
    · dsimp only [coreSeparation]
      rw [dif_neg h]
      exact zero_lt_one
  have coreSeparation_le_dist (gamma delta : Edge)
      (hcore : (bufferedCore gamma).Nonempty) (hne : delta ≠ gamma) :
      ∀ p, p ∈ bufferedCore gamma → ∀ z, z ∈ delta.1.carrier →
        coreSeparation gamma delta ≤ dist p z := by
    exact (coreSeparation_spec gamma delta ⟨hcore, hne⟩).2
  let coreSeparationBound : Edge → ℝ := fun gamma =>
    (Finset.univ : Finset Edge).inf' Finset.univ_nonempty
      (coreSeparation gamma)
  have coreSeparationBound_pos (gamma : Edge) :
      0 < coreSeparationBound gamma := by
    dsimp [coreSeparationBound]
    exact (Finset.lt_inf'_iff _).2 (by
      intro delta _hdelta
      exact coreSeparation_pos gamma delta)
  have coreSeparationBound_le (gamma delta : Edge) :
      coreSeparationBound gamma ≤ coreSeparation gamma delta := by
    dsimp [coreSeparationBound]
    exact Finset.inf'_le (coreSeparation gamma) (Finset.mem_univ delta)
  let eta : Edge → ℝ := fun gamma =>
    min (vertexRadius (J.successor.symm gamma) / 4)
      (min (vertexRadius gamma / 4) (coreSeparationBound gamma / 2))
  have eta_pos (gamma : Edge) : 0 < eta gamma := by
    dsimp [eta]
    exact lt_min (by positivity)
      (lt_min (by positivity) (half_pos (coreSeparationBound_pos gamma)))
  have eta_lt_source_half (gamma : Edge) :
      eta gamma < vertexRadius (J.successor.symm gamma) / 2 := by
    have hle : eta gamma ≤ vertexRadius (J.successor.symm gamma) / 4 := by
      dsimp [eta]
      exact min_le_left _ _
    change eta gamma < vertexR / 2
    change eta gamma ≤ vertexR / 4 at hle
    apply lt_of_le_of_lt hle
    exact vertexR_quarter_lt_half
  have eta_lt_target_half (gamma : Edge) :
      eta gamma < vertexRadius gamma / 2 := by
    have hle : eta gamma ≤ vertexRadius gamma / 4 := by
      dsimp [eta]
      exact le_trans (min_le_right _ _) (min_le_left _ _)
    change eta gamma < vertexR / 2
    change eta gamma ≤ vertexR / 4 at hle
    apply lt_of_le_of_lt hle
    exact vertexR_quarter_lt_half
  have eta_lt_coreSeparation (gamma delta : Edge)
      (hcore : (bufferedCore gamma).Nonempty) (hne : delta ≠ gamma) :
      eta gamma < coreSeparation gamma delta := by
    have heta_le : eta gamma ≤ coreSeparationBound gamma / 2 := by
      dsimp [eta]
      exact le_trans (min_le_right _ _) (min_le_right _ _)
    have hbound := coreSeparationBound_le gamma delta
    have hsep := coreSeparation_pos gamma delta
    linarith
  let controlExists := fun gamma : Edge =>
    PolygonalArcCollarControlRadiiExistsBelow gamma.1 (eta gamma)
      (vertexRadius (J.successor.symm gamma)) (vertexRadius gamma)
      (eta_pos gamma) (by simpa [vertexRadius] using vertexR_pos)
      (by simpa [vertexRadius] using vertexR_pos) (endpointIsolation gamma)
  let controlRadii :
      ∀ gamma : Edge, PolygonalArcCollarControlRadii gamma.1 (eta gamma) :=
    fun gamma => Classical.choose (controlExists gamma)
  have controlSpec (gamma : Edge) :
      let hsource : 0 < gamma.1.vertices.length := by
        have hlen := gamma.1.length_ge_two
        omega
      let htarget : gamma.1.vertices.length - 1 < gamma.1.vertices.length := by
        have hlen := gamma.1.length_ge_two
        omega
      (controlRadii gamma).radius ⟨0, hsource⟩ <
          vertexRadius (J.successor.symm gamma) ∧
        (controlRadii gamma).radius
            ⟨gamma.1.vertices.length - 1, htarget⟩ < vertexRadius gamma ∧
          (∀ i : Fin gamma.1.vertices.length, i.1 ≠ 0 →
            Disjoint
              (Metric.ball gamma.1.vertices[i.1] ((controlRadii gamma).radius i))
              (Metric.ball gamma.1.source
                (vertexRadius (J.successor.symm gamma)))) ∧
            (∀ i : Fin gamma.1.vertices.length,
              i.1 + 1 ≠ gamma.1.vertices.length →
                Disjoint
                  (Metric.ball gamma.1.vertices[i.1]
                    ((controlRadii gamma).radius i))
                  (Metric.ball gamma.1.target (vertexRadius gamma))) := by
    dsimp [controlRadii, controlExists]
    exact Classical.choose_spec
      (PolygonalArcCollarControlRadiiExistsBelow gamma.1 (eta gamma)
        (vertexRadius (J.successor.symm gamma)) (vertexRadius gamma)
        (eta_pos gamma) (by simpa [vertexRadius] using vertexR_pos)
        (by simpa [vertexRadius] using vertexR_pos) (endpointIsolation gamma))
  let middleSegments :
      ∀ gamma : Edge,
        PolygonalArcCollarMiddleSegmentData gamma.1 (controlRadii gamma) :=
    fun gamma => Classical.choice
      (PolygonalArcCollarMiddleSegmentDataExists gamma.1 (controlRadii gamma))
  let forbiddenMargins :
      ∀ gamma : Edge,
        PolygonalArcCollarMiddleForbiddenMargins gamma.1 (controlRadii gamma)
          (middleSegments gamma) :=
    fun gamma => Classical.choice
      (PolygonalArcCollarMiddleForbiddenMarginsExists gamma.1
        (controlRadii gamma) (middleSegments gamma))
  let tubeExists := fun gamma : Edge =>
    PolygonalArcCollarCompatibleOrientedTubeDataExistsBelow gamma.1
      (controlRadii gamma) (middleSegments gamma) (forbiddenMargins gamma)
      (vertexRadius (J.successor.symm gamma)) (vertexRadius gamma)
      (sourceAperture gamma) (targetAperture gamma) (endpointIsolation gamma)
      (sourceAperture_pos gamma) (targetAperture_pos gamma)
  let compatibleTubes :
      ∀ gamma : Edge,
        PolygonalArcCollarCompatibleOrientedTubeData gamma.1
          (controlRadii gamma) (middleSegments gamma) (forbiddenMargins gamma) :=
    fun gamma => Classical.choose (tubeExists gamma)
  have tubeSpec (gamma : Edge) :
      let hfirst : 0 + 1 < gamma.1.vertices.length := by
        have hlen := gamma.1.length_ge_two
        omega
      let jlast : ℕ := gamma.1.vertices.length - 2
      let hlast : jlast + 1 < gamma.1.vertices.length := by
        have hlen := gamma.1.length_ge_two
        dsimp [jlast]
        omega
      (compatibleTubes gamma).initialConeBound 0 hfirst < sourceAperture gamma ∧
        (compatibleTubes gamma).terminalConeBound jlast hlast <
            targetAperture gamma ∧
          (∀ (j : ℕ) (hj : j + 1 < gamma.1.vertices.length), j ≠ 0 →
            Disjoint
              ((compatibleTubes gamma).orientedTubes.toPolygonalArcCollarSeparatedTubeData.tube
                j hj)
              (Metric.ball gamma.1.source
                (vertexRadius (J.successor.symm gamma)))) ∧
            (∀ (j : ℕ) (hj : j + 1 < gamma.1.vertices.length), j ≠ jlast →
              Disjoint
                ((compatibleTubes gamma).orientedTubes.toPolygonalArcCollarSeparatedTubeData.tube
                  j hj)
                (Metric.ball gamma.1.target (vertexRadius gamma))) := by
    dsimp [compatibleTubes, tubeExists]
    exact Classical.choose_spec
      (PolygonalArcCollarCompatibleOrientedTubeDataExistsBelow gamma.1
        (controlRadii gamma) (middleSegments gamma) (forbiddenMargins gamma)
        (vertexRadius (J.successor.symm gamma)) (vertexRadius gamma)
        (sourceAperture gamma) (targetAperture gamma) (endpointIsolation gamma)
        (sourceAperture_pos gamma) (targetAperture_pos gamma))
  let localExists := fun gamma : Edge =>
    PolygonalArcCollarLocalSideDataExistsWithEndpointLeftCones gamma.1
      (controlRadii gamma) (middleSegments gamma) (forbiddenMargins gamma)
      (compatibleTubes gamma) (vertexRadius (J.successor.symm gamma))
      (vertexRadius gamma) (sourceAperture gamma) (targetAperture gamma)
      (by simpa [vertexRadius] using vertexR_pos)
      (by simpa [vertexRadius] using vertexR_pos)
      (sourceAperture_pos gamma) (targetAperture_pos gamma)
      (by simpa using (controlSpec gamma).1)
      (by simpa using (controlSpec gamma).2.1)
      (by simpa using (tubeSpec gamma).1)
      (by simpa using (tubeSpec gamma).2.1)
      (by simpa using (controlSpec gamma).2.2.1)
      (by simpa using (controlSpec gamma).2.2.2)
  let vertexLocalPieces :
      ∀ gamma : Edge,
        PolygonalArcCollarVertexLocalPieceData gamma.1 (controlRadii gamma)
          (middleSegments gamma) (forbiddenMargins gamma)
          (compatibleTubes gamma).orientedTubes.toPolygonalArcCollarSeparatedTubeData :=
    fun gamma => Classical.choose (localExists gamma)
  let localSideData :
      ∀ gamma : Edge,
        PolygonalArcCollarLocalSideData gamma.1 (controlRadii gamma)
          (middleSegments gamma) (forbiddenMargins gamma)
          (compatibleTubes gamma).orientedTubes (vertexLocalPieces gamma) :=
    fun gamma => Classical.choose (Classical.choose_spec (localExists gamma))
  have localSpec (gamma : Edge) :
      let hsource : 0 < gamma.1.vertices.length := by
        have hlen := gamma.1.length_ge_two
        omega
      let itarget : ℕ := gamma.1.vertices.length - 1
      let htarget : itarget < gamma.1.vertices.length := by
        have hlen := gamma.1.length_ge_two
        dsimp [itarget]
        omega
      gamma.1.source ∉ (localSideData gamma).vertexCollar ⟨0, hsource⟩ ∧
        gamma.1.target ∉
            (localSideData gamma).vertexCollar ⟨itarget, htarget⟩ ∧
          ((localSideData gamma).vertexCollar ⟨0, hsource⟩ \
              gamma.1.relativeInterior ⊆
            PolygonalArcInitialEndpointCone gamma.1
              (vertexRadius (J.successor.symm gamma)) (sourceAperture gamma)) ∧
            ((localSideData gamma).vertexCollar ⟨itarget, htarget⟩ \
                gamma.1.relativeInterior ⊆
              PolygonalArcTerminalEndpointCone gamma.1 (vertexRadius gamma)
                (targetAperture gamma)) ∧
              (∀ i : Fin gamma.1.vertices.length, i.1 ≠ 0 →
                Disjoint ((localSideData gamma).vertexCollar i)
                  (Metric.ball gamma.1.source
                    (vertexRadius (J.successor.symm gamma)))) ∧
                (∀ i : Fin gamma.1.vertices.length,
                  i.1 + 1 ≠ gamma.1.vertices.length →
                    Disjoint ((localSideData gamma).vertexCollar i)
                      (Metric.ball gamma.1.target (vertexRadius gamma))) ∧
                  (localSideData gamma).leftSidePiece ⟨0, hsource⟩ ⊆
                    PolygonalArcInitialEndpointLeftCone gamma.1
                      (vertexRadius (J.successor.symm gamma))
                      (sourceAperture gamma) ∧
                    (localSideData gamma).leftSidePiece ⟨itarget, htarget⟩ ⊆
                      PolygonalArcTerminalEndpointLeftCone gamma.1
                        (vertexRadius gamma) (targetAperture gamma) ∧
                      (localSideData gamma).rightSidePiece ⟨0, hsource⟩ ⊆
                        PolygonalArcTerminalEndpointLeftCone
                          (PolygonalArcReverse gamma.1)
                          (vertexRadius (J.successor.symm gamma))
                          (sourceAperture gamma) ∧
                        (localSideData gamma).rightSidePiece
                            ⟨itarget, htarget⟩ ⊆
                          PolygonalArcInitialEndpointLeftCone
                            (PolygonalArcReverse gamma.1) (vertexRadius gamma)
                            (targetAperture gamma) := by
    dsimp [localSideData, vertexLocalPieces, localExists]
    exact Classical.choose_spec (Classical.choose_spec (localExists gamma))
  let stripExists := fun gamma : Edge =>
    PolygonalArcSideStripAssembly gamma.1 (controlRadii gamma)
      (middleSegments gamma) (forbiddenMargins gamma)
      (compatibleTubes gamma).orientedTubes (vertexLocalPieces gamma)
      (localSideData gamma)
  let sideStrips : ∀ gamma : Edge, PolygonalSideStrips gamma.1 :=
    fun gamma => Classical.choose (stripExists gamma)
  have stripSpec (gamma : Edge) :
      (sideStrips gamma).collar =
          ((⋃ (j : ℕ), ⋃ (hj : j + 1 < gamma.1.vertices.length),
              (compatibleTubes gamma).orientedTubes.toPolygonalArcCollarSeparatedTubeData.tube
                j hj) ∪
            (⋃ i : Fin gamma.1.vertices.length,
              (localSideData gamma).vertexCollar i)) ∧
        (sideStrips gamma).leftStrip =
          ((⋃ (j : ℕ), ⋃ (hj : j + 1 < gamma.1.vertices.length),
              (compatibleTubes gamma).orientedTubes.toPolygonalArcCollarSeparatedTubeData.leftHalf
                j hj) ∪
            (⋃ i : Fin gamma.1.vertices.length,
              (localSideData gamma).leftSidePiece i)) ∧
        (sideStrips gamma).rightStrip =
          ((⋃ (j : ℕ), ⋃ (hj : j + 1 < gamma.1.vertices.length),
              (compatibleTubes gamma).orientedTubes.toPolygonalArcCollarSeparatedTubeData.rightHalf
                j hj) ∪
            (⋃ i : Fin gamma.1.vertices.length,
              (localSideData gamma).rightSidePiece i)) ∧
        ∀ z ∈ (sideStrips gamma).collar,
          ∃ p ∈ gamma.1.carrier, dist z p < eta gamma := by
    dsimp [sideStrips, stripExists]
    exact Classical.choose_spec
      (PolygonalArcSideStripAssembly gamma.1 (controlRadii gamma)
        (middleSegments gamma) (forbiddenMargins gamma)
        (compatibleTubes gamma).orientedTubes (vertexLocalPieces gamma)
        (localSideData gamma))
  have localLeftPiece_subset_leftStrip (gamma : Edge)
      (i : Fin gamma.1.vertices.length) :
      (localSideData gamma).leftSidePiece i ⊆ (sideStrips gamma).leftStrip := by
    intro z hz
    rw [(stripSpec gamma).2.1]
    right
    exact Set.mem_iUnion.2 ⟨i, hz⟩
  have localRightPiece_subset_rightStrip (gamma : Edge)
      (i : Fin gamma.1.vertices.length) :
      (localSideData gamma).rightSidePiece i ⊆ (sideStrips gamma).rightStrip := by
    intro z hz
    rw [(stripSpec gamma).2.2.1]
    right
    exact Set.mem_iUnion.2 ⟨i, hz⟩
  have relativeInterior_disjoint_other (gamma delta : Edge)
      (hne : delta ≠ gamma) :
      Disjoint gamma.1.relativeInterior delta.1.carrier := by
    rw [Set.disjoint_left]
    intro z hzrel hzdelta
    rw [gamma.1.relativeInterior_eq] at hzrel
    by_cases hsucc : delta = J.successor gamma
    · have hzinter : z ∈ gamma.1.carrier ∩ (J.successor gamma).1.carrier := by
        exact ⟨hzrel.1, by simpa [hsucc] using hzdelta⟩
      rw [J.adjacent_intersection gamma] at hzinter
      have hztarget : z = gamma.1.target := by simpa using hzinter
      exact hzrel.2 (by simp [hztarget])
    · by_cases hpred : J.successor delta = gamma
      · have hzinter : z ∈ delta.1.carrier ∩ (J.successor delta).1.carrier := by
          exact ⟨hzdelta, by simpa [hpred] using hzrel.1⟩
        rw [J.adjacent_intersection delta] at hzinter
        have hzdeltaTarget : z = delta.1.target := by simpa using hzinter
        have hzsource : z = gamma.1.source := by
          calc
            z = delta.1.target := hzdeltaTarget
            _ = (J.successor delta).1.source := J.adjacent_endpoint delta
            _ = gamma.1.source := by rw [hpred]
        exact hzrel.2 (by simp [hzsource])
      · exact Set.disjoint_left.mp
          (J.nonadjacent_disjoint gamma delta hne hsucc hpred) hzrel.1 hzdelta
  have endpointHalfSpec (gamma : Edge)
      (hfirst : 0 + 1 < gamma.1.vertices.length)
      (hlast : (gamma.1.vertices.length - 2) + 1 < gamma.1.vertices.length) :
      ((compatibleTubes gamma).orientedTubes.toPolygonalArcCollarSeparatedTubeData.leftHalf
          0 hfirst ∩
            Metric.ball gamma.1.source (vertexRadius (J.successor.symm gamma)) ⊆
        PolygonalArcInitialEndpointLeftCone gamma.1
          (vertexRadius (J.successor.symm gamma)) (sourceAperture gamma)) ∧
        ((compatibleTubes gamma).orientedTubes.toPolygonalArcCollarSeparatedTubeData.leftHalf
            (gamma.1.vertices.length - 2) hlast ∩
              Metric.ball gamma.1.target (vertexRadius gamma) ⊆
          PolygonalArcTerminalEndpointLeftCone gamma.1
            (vertexRadius gamma) (targetAperture gamma)) ∧
          ((compatibleTubes gamma).orientedTubes.toPolygonalArcCollarSeparatedTubeData.rightHalf
              0 hfirst ∩
                Metric.ball gamma.1.source
                  (vertexRadius (J.successor.symm gamma)) ⊆
            PolygonalArcTerminalEndpointLeftCone (PolygonalArcReverse gamma.1)
              (vertexRadius (J.successor.symm gamma)) (sourceAperture gamma)) ∧
            ((compatibleTubes gamma).orientedTubes.toPolygonalArcCollarSeparatedTubeData.rightHalf
                (gamma.1.vertices.length - 2) hlast ∩
                  Metric.ball gamma.1.target (vertexRadius gamma) ⊆
              PolygonalArcInitialEndpointLeftCone (PolygonalArcReverse gamma.1)
                (vertexRadius gamma) (targetAperture gamma)) := by
    exact PolygonalArcEndpointLeftHalfTubeSubsetLeftCones gamma.1
      (controlRadii gamma) (middleSegments gamma) (forbiddenMargins gamma)
      (compatibleTubes gamma) (vertexRadius (J.successor.symm gamma))
      (vertexRadius gamma) (sourceAperture gamma) (targetAperture gamma)
      (endpointIsolation gamma) (sourceAperture_pos gamma)
      (targetAperture_pos gamma) hfirst hlast
      (by simpa using (tubeSpec gamma).1)
      (by simpa using (tubeSpec gamma).2.1)
  have collar_disjoint_other_edgeArcs (gamma delta : Edge)
      (hne : delta ≠ gamma) :
      Disjoint (sideStrips gamma).collar delta.1.carrier := by
    rw [Set.disjoint_left]
    intro z hzcollar hzdelta
    have hzJ : z ∈ J.carrier := by
      rw [J.carrier_eq]
      exact Set.mem_iUnion.2 ⟨delta, hzdelta⟩
    by_cases hzSource : z ∈ Metric.ball gamma.1.source
        (vertexRadius (J.successor.symm gamma))
    · let pred := J.successor.symm gamma
      have hzUnion : z ∈
          ((⋃ (j : ℕ), ⋃ (hj : j + 1 < gamma.1.vertices.length),
              (compatibleTubes gamma).orientedTubes.toPolygonalArcCollarSeparatedTubeData.tube
                j hj) ∪
            (⋃ i : Fin gamma.1.vertices.length,
              (localSideData gamma).vertexCollar i)) := by
        rw [← (stripSpec gamma).1]
        exact hzcollar
      rcases hzUnion with hzTubes | hzVertices
      · rcases Set.mem_iUnion.1 hzTubes with ⟨j, hzj⟩
        rcases Set.mem_iUnion.1 hzj with ⟨hj, hzTube⟩
        by_cases hj0 : j = 0
        · subst j
          by_cases hzRel : z ∈ gamma.1.relativeInterior
          · exact Set.disjoint_left.mp
              (relativeInterior_disjoint_other gamma delta hne) hzRel hzdelta
          · have hhalf : z ∈
                (compatibleTubes gamma).orientedTubes.toPolygonalArcCollarSeparatedTubeData.leftHalf
                    0 hj ∪
                  (compatibleTubes gamma).orientedTubes.toPolygonalArcCollarSeparatedTubeData.rightHalf
                    0 hj := by
              rw [← PolygonalArcMiddleTubeWithoutRelativeInterior gamma.1
                (controlRadii gamma) (middleSegments gamma) (forbiddenMargins gamma)
                (compatibleTubes gamma).orientedTubes (vertexLocalPieces gamma)
                (localSideData gamma) 0 hj]
              exact ⟨hzTube, hzRel⟩
            have hlast : (gamma.1.vertices.length - 2) + 1 <
                gamma.1.vertices.length := by
              have hlen := gamma.1.length_ge_two
              omega
            rcases hhalf with hzLeft | hzRight
            · have hzCone := (endpointHalfSpec gamma hj hlast).1 ⟨hzLeft, hzSource⟩
              have hzSector : z ∈ leftVertexSector pred := by
                apply hsuccessorLeft pred
                simpa [pred, vertexRadius, sourceAperture] using hzCone
              exact (hLcomp pred hzSector) hzJ
            · have hzCone := (endpointHalfSpec gamma hj hlast).2.2.1
                ⟨hzRight, hzSource⟩
              have hzSector : z ∈ rightVertexSector pred := by
                apply hsuccessorRight pred
                simpa [pred, vertexRadius, sourceAperture] using hzCone
              exact (hRcomp pred hzSector) hzJ
        · exact (Set.disjoint_left.mp ((tubeSpec gamma).2.2.1 j hj hj0))
            hzTube hzSource
      · rcases Set.mem_iUnion.1 hzVertices with ⟨i, hzVertex⟩
        by_cases hi0 : i.1 = 0
        · have hsource : 0 < gamma.1.vertices.length := by
            have hlen := gamma.1.length_ge_two
            omega
          have hi : i = ⟨0, hsource⟩ := Fin.ext hi0
          subst i
          by_cases hzRel : z ∈ gamma.1.relativeInterior
          · exact Set.disjoint_left.mp
              (relativeInterior_disjoint_other gamma delta hne) hzRel hzdelta
          · have hzSides : z ∈
                (localSideData gamma).leftSidePiece ⟨0, hsource⟩ ∪
                  (localSideData gamma).rightSidePiece ⟨0, hsource⟩ := by
              rw [← (localSideData gamma).vertexCollar_without_arc ⟨0, hsource⟩]
              exact ⟨hzVertex, hzRel⟩
            rcases hzSides with hzLeft | hzRight
            · have hzCone := (localSpec gamma).2.2.2.2.2.2.1 hzLeft
              have hzSector : z ∈ leftVertexSector pred := by
                apply hsuccessorLeft pred
                simpa [pred, vertexRadius, sourceAperture] using hzCone
              exact (hLcomp pred hzSector) hzJ
            · have hzCone := (localSpec gamma).2.2.2.2.2.2.2.2.1 hzRight
              have hzSector : z ∈ rightVertexSector pred := by
                apply hsuccessorRight pred
                simpa [pred, vertexRadius, sourceAperture] using hzCone
              exact (hRcomp pred hzSector) hzJ
        · exact (Set.disjoint_left.mp ((localSpec gamma).2.2.2.2.1 i hi0))
            hzVertex hzSource
    · by_cases hzTarget : z ∈ Metric.ball gamma.1.target (vertexRadius gamma)
      · have hzUnion : z ∈
            ((⋃ (j : ℕ), ⋃ (hj : j + 1 < gamma.1.vertices.length),
                (compatibleTubes gamma).orientedTubes.toPolygonalArcCollarSeparatedTubeData.tube
                  j hj) ∪
              (⋃ i : Fin gamma.1.vertices.length,
                (localSideData gamma).vertexCollar i)) := by
          rw [← (stripSpec gamma).1]
          exact hzcollar
        rcases hzUnion with hzTubes | hzVertices
        · rcases Set.mem_iUnion.1 hzTubes with ⟨j, hzj⟩
          rcases Set.mem_iUnion.1 hzj with ⟨hj, hzTube⟩
          let jlast : ℕ := gamma.1.vertices.length - 2
          have hlast : jlast + 1 < gamma.1.vertices.length := by
            have hlen := gamma.1.length_ge_two
            dsimp [jlast]
            omega
          by_cases hjlast : j = jlast
          · subst j
            by_cases hzRel : z ∈ gamma.1.relativeInterior
            · exact Set.disjoint_left.mp
                (relativeInterior_disjoint_other gamma delta hne) hzRel hzdelta
            · have hhalf : z ∈
                  (compatibleTubes gamma).orientedTubes.toPolygonalArcCollarSeparatedTubeData.leftHalf
                      jlast hlast ∪
                    (compatibleTubes gamma).orientedTubes.toPolygonalArcCollarSeparatedTubeData.rightHalf
                      jlast hlast := by
                rw [← PolygonalArcMiddleTubeWithoutRelativeInterior gamma.1
                  (controlRadii gamma) (middleSegments gamma)
                  (forbiddenMargins gamma) (compatibleTubes gamma).orientedTubes
                  (vertexLocalPieces gamma) (localSideData gamma) jlast hlast]
                exact ⟨by simpa [jlast] using hzTube, hzRel⟩
              rcases hhalf with hzLeft | hzRight
              · have hzCone := (endpointHalfSpec gamma (by omega) (by omega)).2.1
                    ⟨by simpa [jlast] using hzLeft, hzTarget⟩
                have hzSector : z ∈ leftVertexSector gamma := by
                  apply hterminalLeft gamma
                  simpa [vertexRadius, targetAperture] using hzCone
                exact (hLcomp gamma hzSector) hzJ
              · have hzCone := (endpointHalfSpec gamma (by omega) (by omega)).2.2.2
                    ⟨by simpa [jlast] using hzRight, hzTarget⟩
                have hzSector : z ∈ rightVertexSector gamma := by
                  apply hterminalRight gamma
                  simpa [vertexRadius, targetAperture] using hzCone
                exact (hRcomp gamma hzSector) hzJ
          · exact (Set.disjoint_left.mp ((tubeSpec gamma).2.2.2 j hj
                (by simpa [jlast] using hjlast))) hzTube hzTarget
        · rcases Set.mem_iUnion.1 hzVertices with ⟨i, hzVertex⟩
          by_cases hitarget : i.1 + 1 = gamma.1.vertices.length
          · have htarget : gamma.1.vertices.length - 1 < gamma.1.vertices.length := by
              have hlen := gamma.1.length_ge_two
              omega
            have hi : i = ⟨gamma.1.vertices.length - 1, htarget⟩ := by
              apply Fin.ext
              change i.1 = gamma.1.vertices.length - 1
              omega
            subst i
            by_cases hzRel : z ∈ gamma.1.relativeInterior
            · exact Set.disjoint_left.mp
                (relativeInterior_disjoint_other gamma delta hne) hzRel hzdelta
            · have hzSides : z ∈
                  (localSideData gamma).leftSidePiece
                      ⟨gamma.1.vertices.length - 1, htarget⟩ ∪
                    (localSideData gamma).rightSidePiece
                      ⟨gamma.1.vertices.length - 1, htarget⟩ := by
                rw [← (localSideData gamma).vertexCollar_without_arc
                  ⟨gamma.1.vertices.length - 1, htarget⟩]
                exact ⟨hzVertex, hzRel⟩
              rcases hzSides with hzLeft | hzRight
              · have hzCone := (localSpec gamma).2.2.2.2.2.2.2.1 hzLeft
                have hzSector : z ∈ leftVertexSector gamma := by
                  apply hterminalLeft gamma
                  simpa [vertexRadius, targetAperture] using hzCone
                exact (hLcomp gamma hzSector) hzJ
              · have hzCone := (localSpec gamma).2.2.2.2.2.2.2.2.2 hzRight
                have hzSector : z ∈ rightVertexSector gamma := by
                  apply hterminalRight gamma
                  simpa [vertexRadius, targetAperture] using hzCone
                exact (hRcomp gamma hzSector) hzJ
          · exact (Set.disjoint_left.mp
                ((localSpec gamma).2.2.2.2.2.1 i hitarget))
              hzVertex hzTarget
      · rcases (stripSpec gamma).2.2.2 z hzcollar with ⟨p, hpCarrier, hzp⟩
        have hzSourceDist : vertexRadius (J.successor.symm gamma) ≤
            dist z gamma.1.source := by
          rw [Metric.mem_ball] at hzSource
          exact le_of_not_gt hzSource
        have hzTargetDist : vertexRadius gamma ≤ dist z gamma.1.target := by
          rw [Metric.mem_ball] at hzTarget
          exact le_of_not_gt hzTarget
        have hpSourceDist : vertexRadius (J.successor.symm gamma) / 2 <
            dist p gamma.1.source := by
          have htri := dist_triangle z p gamma.1.source
          have heta := eta_lt_source_half gamma
          linarith [dist_comm z p]
        have hpTargetDist : vertexRadius gamma / 2 < dist p gamma.1.target := by
          have htri := dist_triangle z p gamma.1.target
          have heta := eta_lt_target_half gamma
          linarith [dist_comm z p]
        have hpCore : p ∈ bufferedCore gamma := by
          refine ⟨hpCarrier, ?_⟩
          intro hpBalls
          rcases hpBalls with hpSource | hpTarget
          · rw [Metric.mem_ball] at hpSource
            linarith [dist_comm p gamma.1.source]
          · rw [Metric.mem_ball] at hpTarget
            linarith [dist_comm p gamma.1.target]
        have hsep := coreSeparation_le_dist gamma delta ⟨p, hpCore⟩ hne
          p hpCore z hzdelta
        have heta := eta_lt_coreSeparation gamma delta ⟨p, hpCore⟩ hne
        linarith [dist_comm z p]
  have leftStrip_subset_curve_complement (gamma : Edge) :
      (sideStrips gamma).leftStrip ⊆ J.carrierᶜ := by
    intro z hzLeft hzJ
    rw [J.carrier_eq] at hzJ
    rcases Set.mem_iUnion.1 hzJ with ⟨delta, hzdelta⟩
    by_cases hdelta : delta = gamma
    · subst delta
      exact (Set.disjoint_left.mp (sideStrips gamma).left_disjoint_arc)
        hzLeft hzdelta
    · exact (Set.disjoint_left.mp
        (collar_disjoint_other_edgeArcs gamma delta hdelta)
          ((sideStrips gamma).left_subset_collar hzLeft)) hzdelta
  have rightStrip_subset_curve_complement (gamma : Edge) :
      (sideStrips gamma).rightStrip ⊆ J.carrierᶜ := by
    intro z hzRight hzJ
    rw [J.carrier_eq] at hzJ
    rcases Set.mem_iUnion.1 hzJ with ⟨delta, hzdelta⟩
    by_cases hdelta : delta = gamma
    · subst delta
      exact (Set.disjoint_left.mp (sideStrips gamma).right_disjoint_arc)
        hzRight hzdelta
    · exact (Set.disjoint_left.mp
        (collar_disjoint_other_edgeArcs gamma delta hdelta)
          ((sideStrips gamma).right_subset_collar hzRight)) hzdelta
  refine ⟨{
    presentation := presentation
    presentation_carrier_eq := presentation_carrier_eq
    vertexRadius := vertexRadius
    vertexRadius_pos := fun _ => vertexR_pos
    vertexClosedDisks_disjoint := vertexClosedDisks_disjoint
    endpointIsolation := endpointIsolation
    vertexDisk_curve_eq := vertexDisk_curve_eq
    leftVertexSector := leftVertexSector
    rightVertexSector := rightVertexSector
    leftVertexSector_nonempty := hLne
    rightVertexSector_nonempty := hRne
    leftVertexSector_open := hLopen
    rightVertexSector_open := hRopen
    leftVertexSector_connected := hLconn
    rightVertexSector_connected := hRconn
    leftVertexSector_subset_disk := by
      intro gamma
      simpa [vertexRadius] using hLdisk gamma
    rightVertexSector_subset_disk := by
      intro gamma
      simpa [vertexRadius] using hRdisk gamma
    leftVertexSector_subset_complement := hLcomp
    rightVertexSector_subset_complement := hRcomp
    vertexSectors_disjoint := hdisj
    vertexDisk_complement_partition := by
      intro gamma
      simpa [vertexRadius] using hpartition gamma
    vertex_mem_leftSector_closure := hLclosure
    vertex_mem_rightSector_closure := hRclosure
    sourceAperture := sourceAperture
    targetAperture := targetAperture
    sourceAperture_pos := sourceAperture_pos
    targetAperture_pos := targetAperture_pos
    terminalLeftCone_subset_leftSector := by
      intro gamma
      simpa [vertexRadius, targetAperture] using hterminalLeft gamma
    successorInitialLeftCone_subset_leftSector := by
      intro gamma
      simpa [vertexRadius, sourceAperture] using hsuccessorLeft gamma
    terminalRightCone_subset_rightSector := by
      intro gamma
      simpa [vertexRadius, targetAperture] using hterminalRight gamma
    successorInitialRightCone_subset_rightSector := by
      intro gamma
      simpa [vertexRadius, sourceAperture] using hsuccessorRight gamma
    eta := eta
    eta_pos := eta_pos
    eta_lt_sourceRadius := by
      intro gamma
      have hhalf := eta_lt_source_half gamma
      have hpos : 0 < vertexRadius (J.successor.symm gamma) := by
        simpa [vertexRadius] using vertexR_pos
      linarith
    eta_lt_targetRadius := by
      intro gamma
      have hhalf := eta_lt_target_half gamma
      have hpos : 0 < vertexRadius gamma := by
        simpa [vertexRadius] using vertexR_pos
      linarith
    controlRadii := controlRadii
    source_controlRadius_lt := by
      intro gamma hsource
      simpa using (controlSpec gamma).1
    target_controlRadius_lt := by
      intro gamma htarget
      simpa using (controlSpec gamma).2.1
    source_controlBall_disjoint := by
      intro gamma i hi
      exact (controlSpec gamma).2.2.1 i hi
    target_controlBall_disjoint := by
      intro gamma i hi
      exact (controlSpec gamma).2.2.2 i hi
    middleSegments := middleSegments
    forbiddenMargins := forbiddenMargins
    compatibleTubes := compatibleTubes
    initialConeBound_lt_sourceAperture := by
      intro gamma hfirst
      simpa using (tubeSpec gamma).1
    terminalConeBound_lt_targetAperture := by
      intro gamma hlast
      simpa using (tubeSpec gamma).2.1
    vertexLocalPieces := vertexLocalPieces
    localSideData := localSideData
    source_leftPiece_subset_initialCone := by
      intro gamma hsource
      simpa using (localSpec gamma).2.2.2.2.2.2.1
    target_leftPiece_subset_terminalCone := by
      intro gamma htarget
      simpa using (localSpec gamma).2.2.2.2.2.2.2.1
    source_rightPiece_subset_reverseCone := by
      intro gamma hsource
      simpa using (localSpec gamma).2.2.2.2.2.2.2.2.1
    target_rightPiece_subset_reverseCone := by
      intro gamma htarget
      simpa using (localSpec gamma).2.2.2.2.2.2.2.2.2
    sideStrips := sideStrips
    localLeftPiece_subset_leftStrip := localLeftPiece_subset_leftStrip
    localRightPiece_subset_rightStrip := localRightPiece_subset_rightStrip
    collar_near_edgeArc := by
      intro gamma z hz
      exact (stripSpec gamma).2.2.2 z hz
    collar_disjoint_other_edgeArcs := collar_disjoint_other_edgeArcs
    leftStrip_subset_curve_complement := leftStrip_subset_curve_complement
    rightStrip_subset_curve_complement := rightStrip_subset_curve_complement
    leftSector_meets_terminalStrip := by
      intro gamma
      let jlast : ℕ := gamma.1.vertices.length - 2
      have hlast : jlast + 1 < gamma.1.vertices.length := by
        have hlen := gamma.1.length_ge_two
        dsimp [jlast]
        omega
      rcases (vertexLocalPieces gamma).incomingLeftAttachment_nonempty jlast hlast with
        ⟨z, hz⟩
      have hzpiece0 :=
        (localSideData gamma).incomingLeftAttachment_subset_leftSidePiece
          jlast hlast hz
      have hidx : jlast + 1 = gamma.1.vertices.length - 1 := by
        dsimp [jlast]
        omega
      have hzpiece : z ∈ (localSideData gamma).leftSidePiece
          ⟨gamma.1.vertices.length - 1, by omega⟩ := by
        simpa [hidx] using hzpiece0
      refine ⟨z, ?_, localLeftPiece_subset_leftStrip gamma _ hzpiece⟩
      apply hterminalLeft gamma
      have hzcone := (localSpec gamma).2.2.2.2.2.2.2.1 hzpiece
      simpa [vertexRadius, targetAperture] using hzcone
    leftSector_meets_successorInitialStrip := by
      intro gamma
      let delta := J.successor gamma
      have hfirst : 0 + 1 < delta.1.vertices.length := by
        have hlen := delta.1.length_ge_two
        omega
      rcases (vertexLocalPieces delta).outgoingLeftAttachment_nonempty 0 hfirst with
        ⟨z, hz⟩
      have hzpiece :=
        (localSideData delta).outgoingLeftAttachment_subset_leftSidePiece
          0 hfirst hz
      refine ⟨z, ?_, localLeftPiece_subset_leftStrip delta _ hzpiece⟩
      apply hsuccessorLeft gamma
      have hzcone := (localSpec delta).2.2.2.2.2.2.1 hzpiece
      simpa [delta, vertexRadius, sourceAperture] using hzcone
    rightSector_meets_terminalStrip := by
      intro gamma
      let jlast : ℕ := gamma.1.vertices.length - 2
      have hlast : jlast + 1 < gamma.1.vertices.length := by
        have hlen := gamma.1.length_ge_two
        dsimp [jlast]
        omega
      rcases (vertexLocalPieces gamma).incomingRightAttachment_nonempty jlast hlast with
        ⟨z, hz⟩
      have hzpiece0 :=
        (localSideData gamma).incomingRightAttachment_subset_rightSidePiece
          jlast hlast hz
      have hidx : jlast + 1 = gamma.1.vertices.length - 1 := by
        dsimp [jlast]
        omega
      have hzpiece : z ∈ (localSideData gamma).rightSidePiece
          ⟨gamma.1.vertices.length - 1, by omega⟩ := by
        simpa [hidx] using hzpiece0
      refine ⟨z, ?_, localRightPiece_subset_rightStrip gamma _ hzpiece⟩
      apply hterminalRight gamma
      have hzcone := (localSpec gamma).2.2.2.2.2.2.2.2.2 hzpiece
      simpa [vertexRadius, targetAperture] using hzcone
    rightSector_meets_successorInitialStrip := by
      intro gamma
      let delta := J.successor gamma
      have hfirst : 0 + 1 < delta.1.vertices.length := by
        have hlen := delta.1.length_ge_two
        omega
      rcases (vertexLocalPieces delta).outgoingRightAttachment_nonempty 0 hfirst with
        ⟨z, hz⟩
      have hzpiece :=
        (localSideData delta).outgoingRightAttachment_subset_rightSidePiece
          0 hfirst hz
      refine ⟨z, ?_, localRightPiece_subset_rightStrip delta _ hzpiece⟩
      apply hsuccessorRight gamma
      have hzcone := (localSpec delta).2.2.2.2.2.2.2.2.1 hzpiece
      simpa [delta, vertexRadius, sourceAperture] using hzcone
  }⟩

-- [TABLET NODE: JordanCurveSimultaneousCollarDataExists]
lemma JordanCurveSimultaneousCollarDataExists
    (J : SimpleClosedPolygonalCurve) :
    Nonempty (JordanCurveSimultaneousCollarData J) :=
  jordanCurveSimultaneousCollarDataExists_of_preparation J
    (jordanVertexSectorPreparation J)
