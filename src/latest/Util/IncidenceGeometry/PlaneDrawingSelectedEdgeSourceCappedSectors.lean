import Mathlib.Tactic
import Util.IncidenceGeometry.PlaneDrawingEndpointLocalGermCover
import Util.IncidenceGeometry.PlanarFiniteRayCappedSideSectors

open Classical
noncomputable section

lemma PlaneDrawingSelectedEdgeSourceCappedSectors {V : Type*} [Fintype V]
    (G : SimpleGraph V) [Fintype G.edgeSet] [DecidableRel G.Adj]
    (D : OrdinaryPolygonalDrawing G) (e : G.edgeFinset) (γ : PolygonalArc) :
    D.edgeArc e = γ →
      let hfirst : 1 < γ.vertices.length := Nat.lt_of_succ_le γ.length_ge_two
      let d₀ : EuclideanSpace ℝ (Fin 2) := γ.vertices[1]'hfirst - γ.source
      ∃ rMax κMax : ℝ, 0 < rMax ∧ 0 < κMax ∧
        ∀ localRadius localKappa : ℝ,
          0 < localRadius → localRadius ≤ rMax →
            0 < localKappa → localKappa ≤ κMax →
        let chart : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 2) :=
          fun z => γ.source + z 0 • d₀ + z 1 • PlanarRot90 d₀
        let a : ℝ := localRadius / ‖d₀‖
        let leftModel : Set (EuclideanSpace ℝ (Fin 2)) :=
          {z | 0 < z 0 ∧ z 0 ^ 2 + z 1 ^ 2 < a ^ 2 ∧
            0 < z 1 ∧ z 1 < localKappa * z 0}
        let rightModel : Set (EuclideanSpace ℝ (Fin 2)) :=
          {z | 0 < z 0 ∧ z 0 ^ 2 + z 1 ^ 2 < a ^ 2 ∧
            -localKappa * z 0 < z 1 ∧ z 1 < 0}
        ∃ leftSector rightSector : Set (EuclideanSpace ℝ (Fin 2)),
          leftSector = chart '' leftModel ∧
            rightSector = chart '' rightModel ∧
            IsOpen leftSector ∧ IsOpen rightSector ∧
            Convex ℝ leftSector ∧ Convex ℝ rightSector ∧
            leftSector ⊆ Metric.ball γ.source localRadius ∧
            rightSector ⊆ Metric.ball γ.source localRadius ∧
            γ.source ∈ closure leftSector ∧
            γ.source ∈ closure rightSector ∧
            γ.source ∉ leftSector ∧ γ.source ∉ rightSector ∧
            Disjoint leftSector (OrdinaryDrawingImageWithoutEdge G D e) ∧
            Disjoint rightSector (OrdinaryDrawingImageWithoutEdge G D e) := by
  intro hγ
  obtain ⟨r₀, _r₁, hr₀, _hr₁, initialDirections, _terminalDirections,
      hinitialNotParallel, _hterminalNotParallel, hinitialCover, _hterminalCover⟩ :=
    PlaneDrawingEndpointLocalGermCover G D e γ hγ
  let hfirst : 1 < γ.vertices.length := Nat.lt_of_succ_le γ.length_ge_two
  have hzero : 0 < γ.vertices.length := by
    have hlen := γ.length_ge_two
    omega
  have hsource : γ.vertices[0] = γ.source := by
    have hget : γ.vertices[0]? = some γ.vertices[0] :=
      List.getElem?_eq_getElem hzero
    rw [← List.head?_eq_getElem?, γ.source_eq_head] at hget
    exact Option.some.inj hget.symm
  let d₀ : EuclideanSpace ℝ (Fin 2) := γ.vertices[1]'hfirst - γ.source
  have hd₀ : d₀ ≠ 0 := by
    have hpNe : γ.vertices[1]'hfirst ≠ γ.source := by
      intro hp
      have hindices : (1 : ℕ) = 0 := by
        have hEq : γ.vertices[1]'hfirst = γ.vertices[0]'hzero := by
          simpa [hsource] using hp
        exact (γ.simple_vertices.getElem_inj_iff).mp hEq
      omega
    exact sub_ne_zero.mpr hpNe
  have hinitialNotParallel' : ∀ v ∈ initialDirections,
      ¬ ∃ c : ℝ, 0 < c ∧ v = c • d₀ := by
    simpa [d₀, hfirst] using hinitialNotParallel
  obtain ⟨κMax, hκMax, hsectorFamily⟩ :=
    PlanarFiniteRayCappedSideSectors initialDirections γ.source d₀ r₀
      hd₀ hr₀ hinitialNotParallel'
  refine ⟨r₀, κMax, hr₀, hκMax, ?_⟩
  intro localRadius localKappa hlocalRadius hlocalRadiusLe
    hlocalKappa hlocalKappaLe
  obtain ⟨leftSector, rightSector, hleftEq, hrightEq,
      hleftOpen, hrightOpen, hleftConvex, hrightConvex,
      hleftBall, hrightBall, hsourceClosureLeft, hsourceClosureRight,
      hsourceNotLeft, hsourceNotRight, hleftAvoid, hrightAvoid⟩ :=
    hsectorFamily localRadius localKappa hlocalRadius hlocalRadiusLe
      hlocalKappa hlocalKappaLe
  dsimp
  refine ⟨leftSector, rightSector, hleftEq, hrightEq,
    hleftOpen, hrightOpen, hleftConvex, hrightConvex,
    hleftBall, hrightBall, hsourceClosureLeft, hsourceClosureRight,
    hsourceNotLeft, hsourceNotRight, ?_, ?_⟩
  · rw [Set.disjoint_left]
    intro q hqLeft hqDrawing
    have hqRay := hinitialCover
      ⟨Metric.ball_subset_ball hlocalRadiusLe (hleftBall hqLeft), hqDrawing⟩
    have : q ∈ (∅ : Set (EuclideanSpace ℝ (Fin 2))) := by
      rw [← hleftAvoid]
      exact ⟨hqLeft, hqRay⟩
    simpa using this
  · rw [Set.disjoint_left]
    intro q hqRight hqDrawing
    have hqRay := hinitialCover
      ⟨Metric.ball_subset_ball hlocalRadiusLe (hrightBall hqRight), hqDrawing⟩
    have : q ∈ (∅ : Set (EuclideanSpace ℝ (Fin 2))) := by
      rw [← hrightAvoid]
      exact ⟨hqRight, hqRay⟩
    simpa using this
