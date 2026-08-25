import Mathlib.Tactic
import Util.IncidenceGeometry.CrossingFreeEdgeInteriorDisjoint
import Util.IncidenceGeometry.OrdinaryDrawingImageWithoutEdge
import Util.IncidenceGeometry.PlaneDrawingEndpointLocalGermCover
import Util.IncidenceGeometry.PlanarRot90ConeAvoidsFiniteRays
import Util.IncidenceGeometry.PolygonalArcEndpointDiskCappedTaperChartTransport
import Util.IncidenceGeometry.PolygonalArcEndpointIsolation
import Util.IncidenceGeometry.PolygonalArcEndpointIsolationExists
import Util.IncidenceGeometry.PolygonalArcInitialEndpointCone
import Util.IncidenceGeometry.PolygonalArcInitialEndpointSegmentLength
import Util.IncidenceGeometry.PolygonalArcTerminalEndpointCone
import Util.IncidenceGeometry.PolygonalArcTerminalEndpointSegmentLength

open Classical
noncomputable section

lemma PlaneDrawingSelectedEdgeEndpointGermApertures {V : Type*} [Fintype V]
    (G : SimpleGraph V) [Fintype G.edgeSet] [DecidableRel G.Adj]
    (D : OrdinaryPolygonalDrawing G) (hD : D.crossingSet.card = 0)
    (e : G.edgeFinset) (γ : PolygonalArc) :
    D.edgeArc e = γ →
      ∃ r₀ r₁ K₀ K₁ : ℝ,
        PolygonalArcEndpointIsolation γ r₀ r₁ ∧
          0 < K₀ ∧ 0 < K₁ ∧
            Disjoint (PolygonalArcInitialEndpointCone γ r₀ K₀)
              (OrdinaryDrawingImageWithoutEdge G D e) ∧
              Disjoint (PolygonalArcTerminalEndpointCone γ r₁ K₁)
                (OrdinaryDrawingImageWithoutEdge G D e) := by
  intro hγ
  classical
  obtain ⟨ρ₀, ρ₁, hρ₀_pos, hρ₁_pos, initialDirections, terminalDirections,
    hinitial_no_pos, hterminal_no_pos, hinitial_cover, hterminal_cover⟩ :=
    PlaneDrawingEndpointLocalGermCover G D e γ hγ
  obtain ⟨R₀, R₁, hIsoR⟩ := PolygonalArcEndpointIsolationExists γ
  let hfirst : 1 < γ.vertices.length := Nat.lt_of_succ_le γ.length_ge_two
  let hprev : γ.vertices.length - 2 < γ.vertices.length := by
    have hlen := γ.length_ge_two
    omega
  let d₀ : EuclideanSpace ℝ (Fin 2) := γ.vertices[1]'hfirst - γ.source
  let d₁ : EuclideanSpace ℝ (Fin 2) :=
    γ.vertices[γ.vertices.length - 2]'hprev - γ.target
  have hd₀ : d₀ ≠ 0 := by
    have hlen_pos : 0 < PolygonalArcInitialEndpointSegmentLength γ :=
      lt_trans hIsoR.source_pos hIsoR.source_lt_initial_length
    have hdist_pos : 0 < dist γ.source (γ.vertices[1]'hfirst) := by
      simpa [PolygonalArcInitialEndpointSegmentLength, hfirst] using hlen_pos
    intro hd
    have hdist_zero : dist γ.source (γ.vertices[1]'hfirst) = 0 := by
      rw [dist_eq_zero]
      exact (sub_eq_zero.mp hd).symm
    linarith
  have hd₁ : d₁ ≠ 0 := by
    have hlen_pos : 0 < PolygonalArcTerminalEndpointSegmentLength γ :=
      lt_trans hIsoR.target_pos hIsoR.target_lt_terminal_length
    have hdist_pos :
        0 < dist γ.target (γ.vertices[γ.vertices.length - 2]'hprev) := by
      simpa [PolygonalArcTerminalEndpointSegmentLength, hprev] using hlen_pos
    intro hd
    have hdist_zero :
        dist γ.target (γ.vertices[γ.vertices.length - 2]'hprev) = 0 := by
      rw [dist_eq_zero]
      exact (sub_eq_zero.mp hd).symm
    linarith
  have hinitial_no_pos' :
      ∀ v ∈ initialDirections, ¬ ∃ a : ℝ, 0 < a ∧ v = a • d₀ := by
    simpa [d₀, hfirst] using hinitial_no_pos
  have hterminal_no_pos' :
      ∀ v ∈ terminalDirections, ¬ ∃ a : ℝ, 0 < a ∧ v = a • d₁ := by
    simpa [d₁, hprev] using hterminal_no_pos
  obtain ⟨κ₀, hκ₀_pos, havoid₀⟩ :=
    PlanarRot90ConeAvoidsFiniteRays initialDirections d₀ hd₀ hinitial_no_pos'
  obtain ⟨κ₁, hκ₁_pos, havoid₁⟩ :=
    PlanarRot90ConeAvoidsFiniteRays terminalDirections d₁ hd₁ hterminal_no_pos'
  let K₀ : ℝ := κ₀ / 2
  let K₁ : ℝ := κ₁ / 2
  have hK₀_pos : 0 < K₀ := by
    dsimp [K₀]
    linarith
  have hK₁_pos : 0 < K₁ := by
    dsimp [K₁]
    linarith
  have hK₀_lt : K₀ < κ₀ := by
    dsimp [K₀]
    linarith
  have hK₁_lt : K₁ < κ₁ := by
    dsimp [K₁]
    linarith
  let r₀ : ℝ := min ρ₀ R₀
  let r₁ : ℝ := min ρ₁ R₁
  have hr₀_pos : 0 < r₀ := by
    dsimp [r₀]
    exact lt_min hρ₀_pos hIsoR.source_pos
  have hr₁_pos : 0 < r₁ := by
    dsimp [r₁]
    exact lt_min hρ₁_pos hIsoR.target_pos
  have hr₀_le_ρ₀ : r₀ ≤ ρ₀ := by
    dsimp [r₀]
    exact min_le_left ρ₀ R₀
  have hr₁_le_ρ₁ : r₁ ≤ ρ₁ := by
    dsimp [r₁]
    exact min_le_left ρ₁ R₁
  have hr₀_le_R₀ : r₀ ≤ R₀ := by
    dsimp [r₀]
    exact min_le_right ρ₀ R₀
  have hr₁_le_R₁ : r₁ ≤ R₁ := by
    dsimp [r₁]
    exact min_le_right ρ₁ R₁
  have hIso : PolygonalArcEndpointIsolation γ r₀ r₁ := by
    refine
      { source_pos := hr₀_pos
        target_pos := hr₁_pos
        source_lt_initial_length := ?_
        target_lt_terminal_length := ?_
        endpoint_closedBalls_disjoint := ?_
        source_closedBall_carrier_subset_initial_segment := ?_
        target_closedBall_carrier_subset_terminal_segment := ?_ }
    · exact lt_of_le_of_lt hr₀_le_R₀ hIsoR.source_lt_initial_length
    · exact lt_of_le_of_lt hr₁_le_R₁ hIsoR.target_lt_terminal_length
    · exact hIsoR.endpoint_closedBalls_disjoint.mono
        (Metric.closedBall_subset_closedBall hr₀_le_R₀)
        (Metric.closedBall_subset_closedBall hr₁_le_R₁)
    · exact fun ⦃y⦄ hy =>
        hIsoR.source_closedBall_carrier_subset_initial_segment
          ⟨Metric.closedBall_subset_closedBall hr₀_le_R₀ hy.1, hy.2⟩
    · exact fun ⦃y⦄ hy =>
        hIsoR.target_closedBall_carrier_subset_terminal_segment
          ⟨Metric.closedBall_subset_closedBall hr₁_le_R₁ hy.1, hy.2⟩
  have hp₀ : γ.vertices[1]'hfirst ≠ γ.source := by
    intro hp
    apply hd₀
    dsimp [d₀]
    rw [hp]
    simp
  have hp₁ : γ.vertices[γ.vertices.length - 2]'hprev ≠ γ.target := by
    intro hp
    apply hd₁
    dsimp [d₁]
    rw [hp]
    simp
  have htransport₀ :=
    PolygonalArcEndpointDiskCappedTaperChartTransport γ.source
      (γ.vertices[1]'hfirst) r₀ K₀ hp₀ hr₀_pos hK₀_pos
  have htransport₁ :=
    PolygonalArcEndpointDiskCappedTaperChartTransport γ.target
      (γ.vertices[γ.vertices.length - 2]'hprev) r₁ K₁ hp₁ hr₁_pos hK₁_pos
  rcases htransport₀ with
    ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, hcone_ball_raw₀,
      hsource_not_cone_raw, _, _, _⟩
  rcases htransport₁ with
    ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, hcone_ball_raw₁,
      htarget_not_cone_raw, _, _, _⟩
  have hcone_ball₀ :
      PolygonalArcInitialEndpointCone γ r₀ K₀ ⊆ Metric.ball γ.source r₀ := by
    rw [PolygonalArcInitialEndpointCone]
    simpa [hfirst, d₀] using hcone_ball_raw₀
  have hcone_ball₁ :
      PolygonalArcTerminalEndpointCone γ r₁ K₁ ⊆ Metric.ball γ.target r₁ := by
    rw [PolygonalArcTerminalEndpointCone]
    simpa [hprev, d₁] using hcone_ball_raw₁
  have hsource_not_cone :
      γ.source ∉ PolygonalArcInitialEndpointCone γ r₀ K₀ := by
    rw [PolygonalArcInitialEndpointCone]
    simpa [hfirst, d₀] using hsource_not_cone_raw
  have htarget_not_cone :
      γ.target ∉ PolygonalArcTerminalEndpointCone γ r₁ K₁ := by
    rw [PolygonalArcTerminalEndpointCone]
    simpa [hprev, d₁] using htarget_not_cone_raw
  have hdisj₀ :
      Disjoint (PolygonalArcInitialEndpointCone γ r₀ K₀)
        (OrdinaryDrawingImageWithoutEdge G D e) := by
    rw [Set.disjoint_left]
    intro y hycone hyimage
    have hyball_r₀ : y ∈ Metric.ball γ.source r₀ := hcone_ball₀ hycone
    have hyball_ρ₀ : y ∈ Metric.ball γ.source ρ₀ :=
      Metric.ball_subset_ball hr₀_le_ρ₀ hyball_r₀
    have hycover := hinitial_cover ⟨hyball_ρ₀, hyimage⟩
    rcases hycover with hyendpoint | hyray
    · have hy_eq : y = γ.source := by
        simpa using hyendpoint
      exact hsource_not_cone (by simpa [hy_eq] using hycone)
    · rw [PolygonalArcInitialEndpointCone] at hycone
      rcases hycone with ⟨z, hzC, hz_eq⟩
      rcases Set.mem_iUnion.mp hyray with ⟨v, hv_ray⟩
      rcases hv_ray with ⟨c, hc, hy_eq⟩
      dsimp at hzC
      have ht_pos : 0 < z 0 := hzC.1
      have hs_abs_K : |z 1| < K₀ * z 0 := by
        rw [abs_lt]
        constructor <;> linarith [hzC.2.2.1, hzC.2.2.2]
      have hs_abs_κ : |z 1| < κ₀ * z 0 := by
        exact lt_trans hs_abs_K (mul_lt_mul_of_pos_right hK₀_lt ht_pos)
      have hchart_eq_ray :
          γ.source + z 0 • d₀ + z 1 • PlanarRot90 d₀ =
            γ.source + c • v.1 := by
        calc
          γ.source + z 0 • d₀ + z 1 • PlanarRot90 d₀ = y := by
            simpa [d₀, hfirst] using hz_eq
          _ = γ.source + c • v.1 := hy_eq
      have hEq : c • v.1 = z 0 • d₀ + z 1 • PlanarRot90 d₀ := by
        have h :=
          congrArg (fun w : EuclideanSpace ℝ (Fin 2) => w - γ.source)
            hchart_eq_ray
        symm
        calc
          z 0 • d₀ + z 1 • PlanarRot90 d₀ =
              γ.source + z 0 • d₀ + z 1 • PlanarRot90 d₀ - γ.source := by
            abel
          _ = γ.source + c • v.1 - γ.source := h
          _ = c • v.1 := by
            abel
      exact (havoid₀ v.1 v.2 c (z 0) (z 1) hc ht_pos hs_abs_κ) hEq
  have hdisj₁ :
      Disjoint (PolygonalArcTerminalEndpointCone γ r₁ K₁)
        (OrdinaryDrawingImageWithoutEdge G D e) := by
    rw [Set.disjoint_left]
    intro y hycone hyimage
    have hyball_r₁ : y ∈ Metric.ball γ.target r₁ := hcone_ball₁ hycone
    have hyball_ρ₁ : y ∈ Metric.ball γ.target ρ₁ :=
      Metric.ball_subset_ball hr₁_le_ρ₁ hyball_r₁
    have hycover := hterminal_cover ⟨hyball_ρ₁, hyimage⟩
    rcases hycover with hyendpoint | hyray
    · have hy_eq : y = γ.target := by
        simpa using hyendpoint
      exact htarget_not_cone (by simpa [hy_eq] using hycone)
    · rw [PolygonalArcTerminalEndpointCone] at hycone
      rcases hycone with ⟨z, hzC, hz_eq⟩
      rcases Set.mem_iUnion.mp hyray with ⟨v, hv_ray⟩
      rcases hv_ray with ⟨c, hc, hy_eq⟩
      dsimp at hzC
      have ht_pos : 0 < z 0 := hzC.1
      have hs_abs_K : |z 1| < K₁ * z 0 := by
        rw [abs_lt]
        constructor <;> linarith [hzC.2.2.1, hzC.2.2.2]
      have hs_abs_κ : |z 1| < κ₁ * z 0 := by
        exact lt_trans hs_abs_K (mul_lt_mul_of_pos_right hK₁_lt ht_pos)
      have hchart_eq_ray :
          γ.target + z 0 • d₁ + z 1 • PlanarRot90 d₁ =
            γ.target + c • v.1 := by
        calc
          γ.target + z 0 • d₁ + z 1 • PlanarRot90 d₁ = y := by
            simpa [d₁, hprev] using hz_eq
          _ = γ.target + c • v.1 := hy_eq
      have hEq : c • v.1 = z 0 • d₁ + z 1 • PlanarRot90 d₁ := by
        have h :=
          congrArg (fun w : EuclideanSpace ℝ (Fin 2) => w - γ.target)
            hchart_eq_ray
        symm
        calc
          z 0 • d₁ + z 1 • PlanarRot90 d₁ =
              γ.target + z 0 • d₁ + z 1 • PlanarRot90 d₁ - γ.target := by
            abel
          _ = γ.target + c • v.1 - γ.target := h
          _ = c • v.1 := by
            abel
      exact (havoid₁ v.1 v.2 c (z 0) (z 1) hc ht_pos hs_abs_κ) hEq
  exact ⟨r₀, r₁, K₀, K₁, hIso, hK₀_pos, hK₁_pos, hdisj₀, hdisj₁⟩
