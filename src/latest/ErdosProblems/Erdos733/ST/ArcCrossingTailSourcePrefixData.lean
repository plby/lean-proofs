import Mathlib.Tactic
import Mathlib.Analysis.Normed.Affine.Convex
import Mathlib.Analysis.Normed.Affine.AddTorsor
import ErdosProblems.Erdos733.ST.ArcCrossingOldPrefixDisjointTail
import ErdosProblems.Erdos733.ST.PolygonalArcCarrierCompact
import ErdosProblems.Erdos733.ST.PolygonalArcEndpointIsolationExists
import ErdosProblems.Erdos733.ST.PositiveSeparation

open Classical
noncomputable section

-- [TABLET NODE: ArcCrossingTailSourcePrefixData]
lemma ArcCrossingTailSourcePrefixData
    (K : Set (EuclideanSpace ℝ (Fin 2))) (δ τ : PolygonalArc)
    (j : ℕ) (c : EuclideanSpace ℝ (Fin 2))
    (hK : IsCompact K)
    (hj : j + 1 < δ.vertices.length)
    (hcOpen : c ∈ openSegment ℝ δ.vertices[j] δ.vertices[j + 1])
    (hτvertices : τ.vertices = c :: δ.vertices.drop (j + 1))
    (hτKdisjoint : Disjoint τ.carrier K) :
    ∃ (r₀ r₁ : ℝ) (d : EuclideanSpace ℝ (Fin 2)) (η : ℝ),
      PolygonalArcEndpointIsolation τ r₀ r₁ ∧
        d ∈ openSegment ℝ δ.vertices[j] c ∧
          dist c d < r₀ ∧
            segment ℝ d c ⊆ Metric.ball c r₀ ∧
              segment ℝ d c ⊆ segment ℝ c δ.vertices[j] ∧
                IsCompact
                  (K ∪ (ArcCrossingEarlierPrefix δ j hj ∪ segment ℝ δ.vertices[j] d)) ∧
                  Disjoint
                    (K ∪ (ArcCrossingEarlierPrefix δ j hj ∪ segment ℝ δ.vertices[j] d))
                    τ.carrier ∧
                    0 < η ∧
                      ∀ a, a ∈
                          (K ∪ (ArcCrossingEarlierPrefix δ j hj ∪ segment ℝ δ.vertices[j] d)) →
                        ∀ b, b ∈ τ.carrier → η ≤ dist a b := by
-- BODY
  have segment_compact :
      ∀ a b : EuclideanSpace ℝ (Fin 2), IsCompact (segment ℝ a b) := by
    intro a b
    rw [segment_eq_image' ℝ a b]
    exact
      (isCompact_Icc.image
        (by
          fun_prop :
            Continuous
              (fun θ : ℝ =>
                a + θ • (b - a))))
  have earlier_prefix_compact :
      IsCompact (ArcCrossingEarlierPrefix δ j hj) := by
    dsimp [ArcCrossingEarlierPrefix]
    exact isCompact_iUnion (fun i => segment_compact _ _)
  have old_prefix_compact :
      ∀ d : EuclideanSpace ℝ (Fin 2),
        IsCompact
          (K ∪ (ArcCrossingEarlierPrefix δ j hj ∪ segment ℝ δ.vertices[j] d)) := by
    intro d
    exact hK.union (earlier_prefix_compact.union (segment_compact _ _))
  have endpointIsolation_shrink_source :
      ∀ (τ : PolygonalArc) {R₀ R₁ r₀ : ℝ},
        PolygonalArcEndpointIsolation τ R₀ R₁ →
          0 < r₀ → r₀ ≤ R₀ → r₀ < R₀ →
            PolygonalArcEndpointIsolation τ r₀ R₁ := by
    intro τ R₀ R₁ r₀ hIso hr₀pos hr₀le hr₀lt
    refine
      { source_pos := hr₀pos
        target_pos := hIso.target_pos
        source_lt_initial_length := lt_of_lt_of_le hr₀lt hIso.source_lt_initial_length.le
        target_lt_terminal_length := hIso.target_lt_terminal_length
        endpoint_closedBalls_disjoint := ?_
        source_closedBall_carrier_subset_initial_segment := ?_
        target_closedBall_carrier_subset_terminal_segment :=
          hIso.target_closedBall_carrier_subset_terminal_segment }
    · exact hIso.endpoint_closedBalls_disjoint.mono_left
        (Metric.closedBall_subset_closedBall hr₀le)
    · dsimp
      intro z hz
      exact hIso.source_closedBall_carrier_subset_initial_segment
        ⟨Metric.closedBall_subset_closedBall hr₀le hz.1, hz.2⟩
  obtain ⟨R₀, R₁, hIso₀⟩ := PolygonalArcEndpointIsolationExists τ
  let r₀ : ℝ := R₀ / 2
  have hr₀pos : 0 < r₀ := by
    dsimp [r₀]
    linarith [hIso₀.source_pos]
  have hr₀le : r₀ ≤ R₀ := by
    dsimp [r₀]
    linarith [hIso₀.source_pos]
  have hr₀lt : r₀ < R₀ := by
    dsimp [r₀]
    linarith [hIso₀.source_pos]
  have hIso : PolygonalArcEndpointIsolation τ r₀ R₁ :=
    endpointIsolation_shrink_source τ hIso₀ hr₀pos hr₀le hr₀lt
  let u : EuclideanSpace ℝ (Fin 2) := δ.vertices[j]
  let v : EuclideanSpace ℝ (Fin 2) := δ.vertices[j + 1]
  have huv : u ≠ v := by
    dsimp [u, v]
    intro hEq
    have hidx : j = j + 1 :=
      (δ.simple_vertices.getElem_inj_iff
        (i := j) (j := j + 1)
        (hi := Nat.lt_of_succ_lt hj) (hj := hj)).1 hEq
    omega
  have hcu_ne : c ≠ u := by
    intro hcu
    have huOpen : u ∈ openSegment ℝ u v := by
      simpa [u, v, hcu] using hcOpen
    exact huv ((left_mem_openSegment_iff (𝕜 := ℝ) (x := u) (y := v)).1 huOpen)
  let D : ℝ := dist c u
  have hDpos : 0 < D := by
    dsimp [D]
    exact dist_pos.2 hcu_ne
  let s : ℝ := min (1 / 2 : ℝ) (r₀ / (2 * D))
  have hspos : 0 < s := by
    dsimp [s]
    apply lt_min
    · norm_num
    · positivity
  have hs_nonneg : 0 ≤ s := le_of_lt hspos
  have hslt1 : s < 1 := by
    have hsle : s ≤ (1 / 2 : ℝ) := by
      dsimp [s]
      exact min_le_left _ _
    nlinarith
  have hsle_bound : s ≤ r₀ / (2 * D) := by
    dsimp [s]
    exact min_le_right _ _
  let d : EuclideanSpace ℝ (Fin 2) := AffineMap.lineMap c u s
  have hdOpen_cu : d ∈ openSegment ℝ c u := by
    dsimp [d]
    exact lineMap_mem_openSegment (𝕜 := ℝ) c u ⟨hspos, hslt1⟩
  have hdOpen : d ∈ openSegment ℝ u c := by
    simpa [openSegment_symm] using hdOpen_cu
  have hdseg_uc : d ∈ segment ℝ u c :=
    openSegment_subset_segment ℝ u c hdOpen
  have hdist_dc : dist d c = s * D := by
    dsimp [d, D]
    rw [dist_lineMap_left]
    simp [Real.norm_of_nonneg hs_nonneg]
  have hsD_le_half : s * D ≤ r₀ / 2 := by
    have hmul := mul_le_mul_of_nonneg_right hsle_bound (le_of_lt hDpos)
    have hcalc : (r₀ / (2 * D)) * D = r₀ / 2 := by
      field_simp [hDpos.ne']
    simpa [hcalc] using hmul
  have hdist_cd_lt : dist c d < r₀ := by
    have hdc_lt : dist d c < r₀ := by
      rw [hdist_dc]
      nlinarith [hr₀pos, hsD_le_half]
    simpa [dist_comm] using hdc_lt
  have hd_ball : d ∈ Metric.ball c r₀ := by
    simpa [Metric.mem_ball] using (by simpa [dist_comm] using hdist_cd_lt)
  have hc_ball : c ∈ Metric.ball c r₀ := by
    simpa [Metric.mem_ball] using hr₀pos
  have hnear_ball : segment ℝ d c ⊆ Metric.ball c r₀ := by
    exact (convex_ball c r₀).segment_subset hd_ball hc_ball
  have hnear_negative : segment ℝ d c ⊆ segment ℝ c δ.vertices[j] := by
    intro z hz
    have hz_uc : z ∈ segment ℝ u c :=
      (convex_segment u c).segment_subset hdseg_uc (right_mem_segment ℝ u c) hz
    have hz_cu : z ∈ segment ℝ c u := by
      simpa [segment_symm] using hz_uc
    simpa [u] using hz_cu
  let Pfar : Set (EuclideanSpace ℝ (Fin 2)) :=
    ArcCrossingEarlierPrefix δ j hj ∪ segment ℝ δ.vertices[j] d
  have hPcompact :
      IsCompact (K ∪ Pfar) := by
    dsimp [Pfar]
    exact old_prefix_compact d
  have hPdisj_tail : Disjoint Pfar τ.carrier := by
    dsimp [Pfar]
    exact ArcCrossingOldPrefixDisjointTail δ τ j c d hj hcOpen hdOpen hτvertices
  have hKPdisj_tail : Disjoint (K ∪ Pfar) τ.carrier := by
    rw [Set.disjoint_left]
    intro z hz hzτ
    rcases hz with hzK | hzP
    · exact Set.disjoint_left.mp hτKdisjoint hzτ hzK
    · exact Set.disjoint_left.mp hPdisj_tail hzP hzτ
  have hPnonempty : (K ∪ Pfar).Nonempty := by
    refine ⟨δ.vertices[j], Or.inr ?_⟩
    dsimp [Pfar]
    exact Or.inr (left_mem_segment ℝ δ.vertices[j] d)
  have hτnonempty : τ.carrier.Nonempty := by
    have h0lt : 0 < τ.vertices.length := by
      have hlen := τ.length_ge_two
      omega
    have hfirst : 0 + 1 < τ.vertices.length := by
      have hlen := τ.length_ge_two
      omega
    have hsource0 : τ.vertices[0] = τ.source := by
      have hget : τ.vertices[0]? = some τ.vertices[0] :=
        List.getElem?_eq_getElem h0lt
      rw [← List.head?_eq_getElem?, τ.source_eq_head] at hget
      exact Option.some.inj hget.symm
    refine ⟨τ.source, ?_⟩
    rw [τ.carrier_eq]
    refine ⟨0, hfirst, ?_⟩
    simpa [hsource0] using left_mem_segment ℝ τ.vertices[0] τ.vertices[0 + 1]
  obtain ⟨η, hηpos, hηsep⟩ :=
    PositiveSeparation hPnonempty hτnonempty hPcompact (PolygonalArcCarrierCompact τ)
      hKPdisj_tail
  refine
    ⟨r₀, R₁, d, η, hIso, by simpa [u] using hdOpen, hdist_cd_lt,
      hnear_ball, by simpa [u] using hnear_negative, ?_⟩
  refine ⟨by simpa [Pfar] using hPcompact, by simpa [Pfar] using hKPdisj_tail,
    hηpos, ?_⟩
  intro a ha b hb
  exact hηsep a (by simpa [Pfar] using ha) b hb

