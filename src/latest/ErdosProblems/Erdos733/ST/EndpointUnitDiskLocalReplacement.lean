import ErdosProblems.Erdos733.ST.EndpointRectangularWireReplacement
import ErdosProblems.Erdos733.ST.EndpointUnitChordMultiplePointControl
import ErdosProblems.Erdos733.ST.EndpointUnitDiskLocalChordFrame
import ErdosProblems.Erdos733.ST.EndpointUnitDiskLocalConnectorSeparation
import ErdosProblems.Erdos733.ST.EndpointUnitDiskLocalFivePointVerticesAvoid
import ErdosProblems.Erdos733.ST.EndpointUnitDiskLocalSpliceNoShared
import ErdosProblems.Erdos733.ST.EndpointUnitDiskLocalSpliceNoTripleUnique
import ErdosProblems.Erdos733.ST.EndpointUnitDiskLocalSpliceTransverse
import ErdosProblems.Erdos733.ST.EndpointUnitDiskLocalTransportWireFamily
import ErdosProblems.Erdos733.ST.EndpointRectangularWireCrossingsOpen
import ErdosProblems.Erdos733.ST.EndpointUnitDiskLocalSpliceCrossingsOpen
import ErdosProblems.Erdos733.ST.OrdinaryCleanLocalCrossingOfOpenSegments

open Classical
noncomputable section

private def endpointUnitDiskPoint (x y : ℝ) : EuclideanSpace ℝ (Fin 2) :=
  WithLp.toLp 2 (fun k : Fin 2 => if k = 0 then x else y)

@[simp] private lemma endpointUnitDiskPoint_zero (x y : ℝ) :
    endpointUnitDiskPoint x y 0 = x := by
  simp [endpointUnitDiskPoint]

@[simp] private lemma endpointUnitDiskPoint_one (x y : ℝ) :
    endpointUnitDiskPoint x y 1 = y := by
  simp [endpointUnitDiskPoint]

private lemma endpointUnitDiskPointOnSlopeOpen
    {m α β τ : ℝ}
    (hα : 0 < α) (hβ : 0 < β) (hleft : -α < τ) (hright : τ < β) :
    endpointUnitDiskPoint τ (m * τ) ∈
      openSegment ℝ
        (endpointUnitDiskPoint (-α) (m * (-α)))
        (endpointUnitDiskPoint β (m * β)) := by
  rw [openSegment_eq_image_lineMap]
  refine ⟨(τ + α) / (α + β), ?_, ?_⟩
  · have hden : 0 < α + β := by linarith
    constructor
    · exact div_pos (by linarith) hden
    · rw [div_lt_one hden]
      linarith
  · apply PiLp.ext
    intro k
    fin_cases k
    · simp [endpointUnitDiskPoint, AffineMap.lineMap_apply_module]
      field_simp [ne_of_gt (by linarith : 0 < α + β)]
      ring
    · simp [endpointUnitDiskPoint, AffineMap.lineMap_apply_module]
      field_simp [ne_of_gt (by linarith : 0 < α + β)]
      ring

private lemma endpointUnitDiskSegmentIndexUnique
    (Q : PolygonalArc) (q : EuclideanSpace ℝ (Fin 2)) (s t : ℕ)
    (hs : s + 1 < Q.vertices.length) (ht : t + 1 < Q.vertices.length)
    (hqopen : q ∈ openSegment ℝ Q.vertices[s] Q.vertices[s + 1])
    (hqseg : q ∈ segment ℝ Q.vertices[t] Q.vertices[t + 1]) : s = t := by
  have hq_not_vertex : q ∉ Q.vertices := by
    intro hqmem
    obtain ⟨k, hk, hkeq⟩ := List.mem_iff_getElem.mp hqmem
    have hend_ne : Q.vertices[s] ≠ Q.vertices[s + 1] := by
      have hrel := Q.simple_vertices.rel_get_of_lt
        (a := ⟨s, by omega⟩) (b := ⟨s + 1, by omega⟩) (by simp)
      simpa [List.get_eq_getElem] using hrel
    by_cases hks : k = s
    · have hqeq : q = Q.vertices[s] := by simpa [hks] using hkeq.symm
      have hleft : Q.vertices[s] ∈ openSegment ℝ Q.vertices[s] Q.vertices[s + 1] := by
        simpa [hqeq] using hqopen
      exact hend_ne (left_mem_openSegment_iff.mp hleft)
    by_cases hks1 : k = s + 1
    · have hqeq : q = Q.vertices[s + 1] := by simpa [hks1] using hkeq.symm
      have hright : Q.vertices[s + 1] ∈ openSegment ℝ Q.vertices[s] Q.vertices[s + 1] := by
        simpa [hqeq] using hqopen
      exact hend_ne (right_mem_openSegment_iff.mp hright)
    exact Q.vertices_avoid_nonincident_interiors hs hk hks hks1
      (by simpa [hkeq] using hqopen)
  by_contra hst
  rcases lt_or_gt_of_ne hst with hlt | hgt
  · have hinter := Q.segment_intersections hs ht hlt
    have hqinter :
        q ∈ segment ℝ Q.vertices[s] Q.vertices[s + 1] ∩
          segment ℝ Q.vertices[t] Q.vertices[t + 1] :=
      ⟨openSegment_subset_segment ℝ _ _ hqopen, hqseg⟩
    rw [hinter] at hqinter
    split at hqinter
    · have hqeq : q = Q.vertices[t] := by simpa using hqinter
      exact hq_not_vertex (by rw [hqeq]; exact List.getElem_mem _)
    · exact hqinter
  · have hinter := Q.segment_intersections ht hs hgt
    have hqinter :
        q ∈ segment ℝ Q.vertices[t] Q.vertices[t + 1] ∩
          segment ℝ Q.vertices[s] Q.vertices[s + 1] :=
      ⟨hqseg, openSegment_subset_segment ℝ _ _ hqopen⟩
    rw [hinter] at hqinter
    split at hqinter
    · have hqeq : q = Q.vertices[s] := by simpa using hqinter
      exact hq_not_vertex (by rw [hqeq]; exact List.getElem_mem _)
    · exact hqinter

private abbrev endpointUnitDiskFivePointIntersections
    (p₀ p₁ p₂ p₃ p₄ : EuclideanSpace ℝ (Fin 2)) : Prop :=
  ∀ ⦃i j : ℕ⦄,
    (hi : i + 1 < [p₀, p₁, p₂, p₃, p₄].length) →
      (hj : j + 1 < [p₀, p₁, p₂, p₃, p₄].length) →
        i < j →
          (segment ℝ [p₀, p₁, p₂, p₃, p₄][i]
              [p₀, p₁, p₂, p₃, p₄][i + 1] ∩
            segment ℝ [p₀, p₁, p₂, p₃, p₄][j]
              [p₀, p₁, p₂, p₃, p₄][j + 1]) =
            if j = i + 1 then {[p₀, p₁, p₂, p₃, p₄][j]} else ∅

private abbrev endpointUnitDiskFivePointAvoid
    (p₀ p₁ p₂ p₃ p₄ : EuclideanSpace ℝ (Fin 2)) : Prop :=
  ∀ ⦃i k : ℕ⦄,
    (hi : i + 1 < [p₀, p₁, p₂, p₃, p₄].length) →
      (hk : k < [p₀, p₁, p₂, p₃, p₄].length) →
        k ≠ i → k ≠ i + 1 →
          [p₀, p₁, p₂, p₃, p₄][k] ∉
            openSegment ℝ [p₀, p₁, p₂, p₃, p₄][i]
              [p₀, p₁, p₂, p₃, p₄][i + 1]

private def endpointUnitDiskFivePointArc
    (p₀ p₁ p₂ p₃ p₄ : EuclideanSpace ℝ (Fin 2))
    (hsimple : [p₀, p₁, p₂, p₃, p₄].Nodup)
    (hintersections : endpointUnitDiskFivePointIntersections p₀ p₁ p₂ p₃ p₄)
    (havoid : endpointUnitDiskFivePointAvoid p₀ p₁ p₂ p₃ p₄) : PolygonalArc where
  vertices := [p₀, p₁, p₂, p₃, p₄]
  length_ge_two := by norm_num
  source := p₀
  target := p₄
  source_eq_head := by simp
  target_eq_last := by simp
  carrier :=
    {p | ∃ n : ℕ, ∃ hn : n + 1 < [p₀, p₁, p₂, p₃, p₄].length,
      p ∈ segment ℝ [p₀, p₁, p₂, p₃, p₄][n] [p₀, p₁, p₂, p₃, p₄][n + 1]}
  relativeInterior :=
    {p | ∃ n : ℕ, ∃ hn : n + 1 < [p₀, p₁, p₂, p₃, p₄].length,
      p ∈ segment ℝ [p₀, p₁, p₂, p₃, p₄][n] [p₀, p₁, p₂, p₃, p₄][n + 1]} \
      ({p₀, p₄} : Set (EuclideanSpace ℝ (Fin 2)))
  carrier_eq := by rfl
  relativeInterior_eq := by rfl
  simple_vertices := hsimple
  segment_intersections := hintersections
  vertices_avoid_nonincident_interiors := havoid

@[simp] private lemma endpointUnitDiskFivePointArc_vertices
    (p₀ p₁ p₂ p₃ p₄ : EuclideanSpace ℝ (Fin 2))
    (hsimple : [p₀, p₁, p₂, p₃, p₄].Nodup)
    (hintersections : endpointUnitDiskFivePointIntersections p₀ p₁ p₂ p₃ p₄)
    (havoid : endpointUnitDiskFivePointAvoid p₀ p₁ p₂ p₃ p₄) :
    (endpointUnitDiskFivePointArc p₀ p₁ p₂ p₃ p₄ hsimple hintersections havoid).vertices =
      [p₀, p₁, p₂, p₃, p₄] := rfl

@[simp] private lemma endpointUnitDiskFivePointArc_source
    (p₀ p₁ p₂ p₃ p₄ : EuclideanSpace ℝ (Fin 2))
    (hsimple : [p₀, p₁, p₂, p₃, p₄].Nodup)
    (hintersections : endpointUnitDiskFivePointIntersections p₀ p₁ p₂ p₃ p₄)
    (havoid : endpointUnitDiskFivePointAvoid p₀ p₁ p₂ p₃ p₄) :
    (endpointUnitDiskFivePointArc p₀ p₁ p₂ p₃ p₄ hsimple hintersections havoid).source = p₀ := rfl

@[simp] private lemma endpointUnitDiskFivePointArc_target
    (p₀ p₁ p₂ p₃ p₄ : EuclideanSpace ℝ (Fin 2))
    (hsimple : [p₀, p₁, p₂, p₃, p₄].Nodup)
    (hintersections : endpointUnitDiskFivePointIntersections p₀ p₁ p₂ p₃ p₄)
    (havoid : endpointUnitDiskFivePointAvoid p₀ p₁ p₂ p₃ p₄) :
    (endpointUnitDiskFivePointArc p₀ p₁ p₂ p₃ p₄ hsimple hintersections havoid).target = p₄ := rfl

@[simp] private lemma endpointUnitDiskFivePointArc_mem_carrier
    (p₀ p₁ p₂ p₃ p₄ p : EuclideanSpace ℝ (Fin 2))
    (hsimple : [p₀, p₁, p₂, p₃, p₄].Nodup)
    (hintersections : endpointUnitDiskFivePointIntersections p₀ p₁ p₂ p₃ p₄)
    (havoid : endpointUnitDiskFivePointAvoid p₀ p₁ p₂ p₃ p₄) :
    p ∈ (endpointUnitDiskFivePointArc p₀ p₁ p₂ p₃ p₄ hsimple hintersections havoid).carrier ↔
      ∃ n : ℕ, ∃ hn : n + 1 < [p₀, p₁, p₂, p₃, p₄].length,
        p ∈ segment ℝ [p₀, p₁, p₂, p₃, p₄][n] [p₀, p₁, p₂, p₃, p₄][n + 1] :=
  Iff.rfl

@[simp] private lemma endpointUnitDiskFivePointArc_mem_relativeInterior
    (p₀ p₁ p₂ p₃ p₄ p : EuclideanSpace ℝ (Fin 2))
    (hsimple : [p₀, p₁, p₂, p₃, p₄].Nodup)
    (hintersections : endpointUnitDiskFivePointIntersections p₀ p₁ p₂ p₃ p₄)
    (havoid : endpointUnitDiskFivePointAvoid p₀ p₁ p₂ p₃ p₄) :
    p ∈ (endpointUnitDiskFivePointArc p₀ p₁ p₂ p₃ p₄ hsimple hintersections havoid).relativeInterior ↔
      (∃ n : ℕ, ∃ hn : n + 1 < [p₀, p₁, p₂, p₃, p₄].length,
        p ∈ segment ℝ [p₀, p₁, p₂, p₃, p₄][n] [p₀, p₁, p₂, p₃, p₄][n + 1]) ∧
          p ∉ ({p₀, p₄} : Set (EuclideanSpace ℝ (Fin 2))) :=
  Iff.rfl

private lemma endpointUnitDiskSegmentLeftSubsegmentOpen
    {A B C p : EuclideanSpace ℝ (Fin 2)}
    (hC : C ∈ openSegment ℝ A B) (hp : p ∈ segment ℝ A C) (hp_ne : p ≠ A) :
    p ∈ openSegment ℝ A B := by
  rw [openSegment_eq_image_lineMap] at hC
  rcases hC with ⟨t, ht, htC⟩
  rw [segment_eq_image_lineMap] at hp
  rcases hp with ⟨s, hs, hsp⟩
  have hs_pos : 0 < s := by
    refine lt_of_le_of_ne hs.1 ?_
    intro hs_zero
    apply hp_ne
    rw [← hs_zero] at hsp
    simpa using hsp.symm
  rw [openSegment_eq_image_lineMap]
  refine ⟨s * t, ⟨mul_pos hs_pos ht.1, ?_⟩, ?_⟩
  · nlinarith [hs.2, ht.1, ht.2]
  · apply PiLp.ext
    intro k
    have hCcoord := congrArg (fun q : EuclideanSpace ℝ (Fin 2) => q k) htC
    have hpcoord := congrArg (fun q : EuclideanSpace ℝ (Fin 2) => q k) hsp
    simp [AffineMap.lineMap_apply_module] at hCcoord hpcoord ⊢
    nlinarith

private lemma endpointUnitDiskSegmentRightSubsegmentOpen
    {A B C p : EuclideanSpace ℝ (Fin 2)}
    (hC : C ∈ openSegment ℝ A B) (hp : p ∈ segment ℝ C B) (hp_ne : p ≠ B) :
    p ∈ openSegment ℝ A B := by
  rw [openSegment_eq_image_lineMap] at hC
  rcases hC with ⟨t, ht, htC⟩
  rw [segment_eq_image_lineMap] at hp
  rcases hp with ⟨s, hs, hsp⟩
  have hs_lt_one : s < 1 := by
    refine lt_of_le_of_ne hs.2 ?_
    intro hs_one
    apply hp_ne
    rw [hs_one] at hsp
    simpa using hsp.symm
  rw [openSegment_eq_image_lineMap]
  refine ⟨t + s * (1 - t), ⟨?_, ?_⟩, ?_⟩
  · nlinarith [hs.1, ht.1, ht.2]
  · nlinarith [hs.1, hs_lt_one, ht.1, ht.2]
  · apply PiLp.ext
    intro k
    have hCcoord := congrArg (fun q : EuclideanSpace ℝ (Fin 2) => q k) htC
    have hpcoord := congrArg (fun q : EuclideanSpace ℝ (Fin 2) => q k) hsp
    simp [AffineMap.lineMap_apply_module] at hCcoord hpcoord ⊢
    nlinarith

private lemma endpointUnitDiskSlopeRectangularSideData
    {κ : Type*} [Fintype κ] (r : ℝ) (hr : 0 < r)
    (m : κ → ℝ) (δ : ℝ) (hm : Function.Injective m) (hδ : 0 < δ) :
    ∃ ε H : ℝ,
      ∃ L R : κ → EuclideanSpace ℝ (Fin 2),
        0 < ε ∧
          ε < δ ∧
            0 < H ∧
              (∀ i, (L i) 0 = -ε) ∧
                (∀ i, (R i) 0 = ε) ∧
                  (∀ i, (L i) 1 = -(m i * ε)) ∧
                    (∀ i, (R i) 1 = m i * ε) ∧
                      (∀ i, |(L i) 1| < H) ∧
                        (∀ i, |(R i) 1| < H) ∧
                          Function.Injective L ∧
                            Function.Injective R ∧
                              (∀ i j,
                                (L i) 1 < (L j) 1 ↔ (R j) 1 < (R i) 1) ∧
                                ({p : EuclideanSpace ℝ (Fin 2) |
                                  -ε ≤ p 0 ∧ p 0 ≤ ε ∧ -H ≤ p 1 ∧ p 1 ≤ H} ⊆
                                    Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) r) := by
  let C : ℝ := (∑ i : κ, |m i|) + 1
  have hCpos : 0 < C := by
    have hsum_nonneg : 0 ≤ ∑ i : κ, |m i| := by
      exact Finset.sum_nonneg (fun i _ => abs_nonneg (m i))
    dsimp [C]
    linarith
  have hCge1 : 1 ≤ C := by
    have hsum_nonneg : 0 ≤ ∑ i : κ, |m i| := by
      exact Finset.sum_nonneg (fun i _ => abs_nonneg (m i))
    dsimp [C]
    linarith
  have hm_bound : ∀ i, |m i| < C := by
    intro i
    have hle_sum : |m i| ≤ ∑ j : κ, |m j| := by
      exact Finset.single_le_sum (fun j _ => abs_nonneg (m j)) (by simp)
    dsimp [C]
    linarith
  let ε₀ : ℝ := r / (2 * (C + 1))
  let ε : ℝ := min ε₀ (δ / 2)
  let H : ℝ := C * ε
  have hden_pos : 0 < 2 * (C + 1) := by positivity
  have hε₀pos : 0 < ε₀ := by
    dsimp [ε₀]
    exact div_pos hr hden_pos
  have hεpos : 0 < ε := by
    dsimp [ε]
    exact lt_min hε₀pos (by linarith)
  have hε_le_base : ε ≤ ε₀ := by
    dsimp [ε]
    exact min_le_left _ _
  have hε_ltδ : ε < δ := by
    have hε_le_half : ε ≤ δ / 2 := by
      dsimp [ε]
      exact min_le_right _ _
    linarith
  have hHpos : 0 < H := by
    dsimp [H]
    positivity
  let L : κ → EuclideanSpace ℝ (Fin 2) :=
    fun i => endpointUnitDiskPoint (-ε) (-(m i * ε))
  let R : κ → EuclideanSpace ℝ (Fin 2) :=
    fun i => endpointUnitDiskPoint ε (m i * ε)
  refine ⟨ε, H, L, R, hεpos, hε_ltδ, hHpos, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i
    simp [L]
  · intro i
    simp [R]
  · intro i
    simp [L]
  · intro i
    simp [R]
  · intro i
    have hmul : |m i * ε| < C * ε := by
      rw [abs_mul, abs_of_pos hεpos]
      exact mul_lt_mul_of_pos_right (hm_bound i) hεpos
    simpa [L, H, abs_neg] using hmul
  · intro i
    have hmul : |m i * ε| < C * ε := by
      rw [abs_mul, abs_of_pos hεpos]
      exact mul_lt_mul_of_pos_right (hm_bound i) hεpos
    simpa [R, H] using hmul
  · intro i j hij
    apply hm
    have hy := congrArg (fun p : EuclideanSpace ℝ (Fin 2) => p 1) hij
    have hy' : -(m i * ε) = -(m j * ε) := by
      simpa [L] using hy
    have hmul : m i * ε = m j * ε := by linarith
    exact mul_right_cancel₀ hεpos.ne' hmul
  · intro i j hij
    apply hm
    have hy := congrArg (fun p : EuclideanSpace ℝ (Fin 2) => p 1) hij
    have hmul : m i * ε = m j * ε := by
      simpa [R] using hy
    exact mul_right_cancel₀ hεpos.ne' hmul
  · intro i j
    simp [L, R]

  · intro p hp
    rcases hp with ⟨hx_low, hx_high, hy_low, hy_high⟩
    rw [Metric.mem_ball, dist_zero_right]
    have hx_abs : |p 0| ≤ ε := by
      exact abs_le.mpr ⟨by linarith, by linarith⟩
    have hy_abs : |p 1| ≤ H := by
      exact abs_le.mpr ⟨by linarith, by linarith⟩
    have hx_sq : (p 0) ^ 2 ≤ ε ^ 2 := by
      exact sq_le_sq.mpr (by simpa [abs_of_nonneg hεpos.le] using hx_abs)
    have hy_sq : (p 1) ^ 2 ≤ H ^ 2 := by
      exact sq_le_sq.mpr (by simpa [abs_of_nonneg hHpos.le] using hy_abs)
    have hnormsq := PiLp.norm_sq_eq_of_L2 (fun _ : Fin 2 => ℝ) p
    have hnormsq' : ‖p‖ ^ 2 = (p 0) ^ 2 + (p 1) ^ 2 := by
      simpa [EuclideanSpace, Fin.sum_univ_two, sq, Real.norm_eq_abs] using hnormsq
    have hCeps_le : (C + 1) * ε ≤ r / 2 := by
      have hC1_nonneg : 0 ≤ C + 1 := by linarith [hCpos]
      calc
        (C + 1) * ε ≤ (C + 1) * ε₀ := by
          exact mul_le_mul_of_nonneg_left hε_le_base hC1_nonneg
        _ = r / 2 := by
          dsimp [ε₀]
          field_simp [ne_of_gt hden_pos]
    have hsum_bound : ε ^ 2 + H ^ 2 ≤ ((C + 1) * ε) ^ 2 := by
      have hCnonneg : 0 ≤ C := le_of_lt hCpos
      dsimp [H]
      nlinarith [hCnonneg, hεpos]
    have hnorm_sq_le : ‖p‖ ^ 2 ≤ ((C + 1) * ε) ^ 2 := by
      rw [hnormsq']
      nlinarith
    have hr_sq_pos : 0 < r ^ 2 := sq_pos_of_pos hr
    have hhalf_sq_lt : ((C + 1) * ε) ^ 2 < r ^ 2 := by
      have hCeps_nonneg : 0 ≤ (C + 1) * ε := by positivity
      have hCeps_lt_r : (C + 1) * ε < r := by
        linarith [hCeps_le, hr]
      nlinarith [hCeps_nonneg, hCeps_lt_r, hr]
    have hnorm_sq_lt : ‖p‖ ^ 2 < r ^ 2 := lt_of_le_of_lt hnorm_sq_le hhalf_sq_lt
    have habs : |‖p‖| < |r| := sq_lt_sq.mp hnorm_sq_lt
    simpa [abs_of_nonneg (norm_nonneg p), abs_of_pos hr] using habs

private lemma endpointUnitDiskChordDiameterOriented
    {A B z : EuclideanSpace ℝ (Fin 2)} {ρ : ℝ}
    (hAB : A ≠ B) (hzopen : z ∈ openSegment ℝ A B) (hρpos : 0 < ρ)
    (hρA : ρ < dist z A) (hρB : ρ < dist z B) :
    ∃ u v : EuclideanSpace ℝ (Fin 2),
      u ∈ Metric.sphere z ρ ∧
        v ∈ Metric.sphere z ρ ∧
          u ∈ openSegment ℝ A z ∧
            v ∈ openSegment ℝ z B ∧
              z ∈ openSegment ℝ u v ∧
                Metric.closedBall z ρ ∩ segment ℝ A B = segment ℝ u v ∧
                  openSegment ℝ u v ⊆ Metric.ball z ρ := by
  rw [openSegment_eq_image_lineMap] at hzopen
  rcases hzopen with ⟨t, ht, hzt⟩
  subst z
  have dist_lineMap_lineMap_local :
      ∀ c₁ c₂ : ℝ,
        dist (AffineMap.lineMap A B c₁) (AffineMap.lineMap A B c₂) =
          dist c₁ c₂ * dist A B := by
    intro c₁ c₂
    rw [dist_eq_norm, Real.dist_eq, dist_eq_norm]
    have hvec :
        AffineMap.lineMap A B c₁ - AffineMap.lineMap A B c₂ =
          (c₁ - c₂) • (B - A) := by
      apply PiLp.ext
      intro k
      simp [AffineMap.lineMap_apply_module]
      ring
    rw [hvec, norm_smul, Real.norm_eq_abs]
    have hnorm : ‖B - A‖ = ‖A - B‖ := by
      have hneg : B - A = -(A - B) := by
        abel
      rw [hneg, norm_neg]
    rw [hnorm]
  let d : ℝ := dist A B
  have hd_pos : 0 < d := by
    dsimp [d]
    exact dist_pos.mpr hAB
  let ε : ℝ := ρ / d
  have hεpos : 0 < ε := div_pos hρpos hd_pos
  have hε_lt_t : ε < t := by
    dsimp [ε]
    rw [div_lt_iff₀ hd_pos]
    have hdist : dist (AffineMap.lineMap A B t) A = t * dist A B := by
      simpa [Real.dist_eq, abs_of_pos ht.1, mul_comm] using
        dist_lineMap_lineMap_local t 0
    simpa [d, hdist] using hρA
  have hε_lt_one_sub : ε < 1 - t := by
    dsimp [ε]
    rw [div_lt_iff₀ hd_pos]
    have hdist : dist (AffineMap.lineMap A B t) B = (1 - t) * dist A B := by
      calc
        dist (AffineMap.lineMap A B t) B =
            dist (AffineMap.lineMap A B t) (AffineMap.lineMap A B (1 : ℝ)) := by
          rw [AffineMap.lineMap_apply_one]
        _ = (1 - t) * dist A B := by
          rw [dist_lineMap_lineMap_local, Real.dist_eq]
          have habs : |t - 1| = 1 - t := by
            rw [abs_of_neg (sub_neg.mpr ht.2)]
            ring
          rw [habs]
    simpa [d, hdist] using hρB
  let u : EuclideanSpace ℝ (Fin 2) := AffineMap.lineMap A B (t - ε)
  let v : EuclideanSpace ℝ (Fin 2) := AffineMap.lineMap A B (t + ε)
  have hε_mul_d : ε * d = ρ := by
    dsimp [ε, d]
    exact div_mul_cancel₀ ρ hd_pos.ne'
  have hdist_left_param : dist (t - ε) t = ε := by
    rw [Real.dist_eq]
    have hneg : t - ε - t = -ε := by ring
    rw [hneg, abs_neg, abs_of_pos hεpos]
  have hdist_right_param : dist (t + ε) t = ε := by
    rw [Real.dist_eq]
    ring_nf
    exact abs_of_pos hεpos
  have hu_sphere : u ∈ Metric.sphere (AffineMap.lineMap A B t) ρ := by
    rw [Metric.mem_sphere]
    dsimp [u]
    rw [dist_lineMap_lineMap_local, hdist_left_param, hε_mul_d]
  have hv_sphere : v ∈ Metric.sphere (AffineMap.lineMap A B t) ρ := by
    rw [Metric.mem_sphere]
    dsimp [v]
    rw [dist_lineMap_lineMap_local, hdist_right_param, hε_mul_d]
  have hu_open : u ∈ openSegment ℝ A (AffineMap.lineMap A B t) := by
    rw [openSegment_eq_image_lineMap]
    refine ⟨(t - ε) / t, ?_, ?_⟩
    · constructor
      · exact div_pos (sub_pos.mpr hε_lt_t) ht.1
      · rw [div_lt_one ht.1]
        linarith [hεpos]
    · apply PiLp.ext
      intro k
      simp [u, AffineMap.lineMap_apply_module]
      field_simp [ne_of_gt ht.1]
      ring
  have hv_open : v ∈ openSegment ℝ (AffineMap.lineMap A B t) B := by
    rw [openSegment_eq_image_lineMap]
    refine ⟨ε / (1 - t), ?_, ?_⟩
    · have hden_pos : 0 < 1 - t := by linarith
      constructor
      · exact div_pos hεpos hden_pos
      · rw [div_lt_one hden_pos]
        exact hε_lt_one_sub
    · apply PiLp.ext
      intro k
      simp [v, AffineMap.lineMap_apply_module]
      have hden : 1 - t ≠ 0 := by linarith
      apply (mul_left_cancel₀ hden)
      field_simp [hden]
      ring
  have hz_open_uv : AffineMap.lineMap A B t ∈ openSegment ℝ u v := by
    rw [openSegment_eq_image_lineMap]
    refine ⟨(1 / 2 : ℝ), ⟨by norm_num, by norm_num⟩, ?_⟩
    apply PiLp.ext
    intro k
    simp [u, v, AffineMap.lineMap_apply_module]
    ring
  have hball_u : u ∈ Metric.closedBall (AffineMap.lineMap A B t) ρ := by
    rw [Metric.mem_closedBall]
    exact (Metric.mem_sphere.mp hu_sphere).le
  have hball_v : v ∈ Metric.closedBall (AffineMap.lineMap A B t) ρ := by
    rw [Metric.mem_closedBall]
    exact (Metric.mem_sphere.mp hv_sphere).le
  have hu_seg : u ∈ segment ℝ A B := by
    rw [segment_eq_image_lineMap]
    refine ⟨t - ε, ?_, rfl⟩
    exact ⟨by linarith, by linarith [ht.2, hεpos]⟩
  have hv_seg : v ∈ segment ℝ A B := by
    rw [segment_eq_image_lineMap]
    refine ⟨t + ε, ?_, rfl⟩
    exact ⟨by linarith [ht.1, hεpos], by linarith⟩
  have hsub_uv_ball :
      segment ℝ u v ⊆ Metric.closedBall (AffineMap.lineMap A B t) ρ :=
    (convex_closedBall (AffineMap.lineMap A B t) ρ).segment_subset hball_u hball_v
  have hsub_uv_seg : segment ℝ u v ⊆ segment ℝ A B :=
    (convex_segment A B).segment_subset hu_seg hv_seg
  have hinter :
      Metric.closedBall (AffineMap.lineMap A B t) ρ ∩ segment ℝ A B =
        segment ℝ u v := by
    apply Set.Subset.antisymm
    · rintro y ⟨hyball, hyseg⟩
      rw [segment_eq_image_lineMap] at hyseg
      rcases hyseg with ⟨s, hs, rfl⟩
      rw [segment_eq_image_lineMap]
      have hdist_le : dist s t ≤ ε := by
        rw [le_div_iff₀ hd_pos]
        have h := hyball
        rw [Metric.mem_closedBall, dist_lineMap_lineMap_local] at h
        simpa [ε, d, mul_comm] using h
      have habs : |s - t| ≤ ε := by
        simpa [Real.dist_eq] using hdist_le
      have hbounds := abs_sub_le_iff.mp habs
      have hs_lower : t - ε ≤ s := by linarith
      have hs_upper : s ≤ t + ε := by linarith
      let lam : ℝ := (s - (t - ε)) / (2 * ε)
      refine ⟨lam, ?_, ?_⟩
      · have hden_pos : 0 < 2 * ε := by positivity
        constructor
        · exact div_nonneg (sub_nonneg.mpr hs_lower) hden_pos.le
        · rw [div_le_iff₀ hden_pos]
          linarith
      · apply PiLp.ext
        intro k
        simp [lam, u, v, AffineMap.lineMap_apply_module]
        field_simp [hεpos.ne']
        ring
    · intro y hy
      exact ⟨hsub_uv_ball hy, hsub_uv_seg hy⟩
  have hopen_uv_ball :
      openSegment ℝ u v ⊆ Metric.ball (AffineMap.lineMap A B t) ρ := by
    intro y hy
    rw [openSegment_eq_image_lineMap] at hy
    rcases hy with ⟨s, hs, rfl⟩
    have hline :
        AffineMap.lineMap u v s =
          AffineMap.lineMap A B (t - ε + s * (2 * ε)) := by
      apply PiLp.ext
      intro k
      simp [u, v, AffineMap.lineMap_apply_module]
      ring
    rw [Metric.mem_ball, hline, dist_lineMap_lineMap_local]
    have hdist_param : dist (t - ε + s * (2 * ε)) t < ε := by
      rw [Real.dist_eq]
      have hdiff : t - ε + s * (2 * ε) - t = ε * (2 * s - 1) := by ring
      rw [hdiff, abs_mul, abs_of_pos hεpos]
      have habs : |2 * s - 1| < 1 := by
        rw [abs_lt]
        constructor <;> linarith [hs.1, hs.2]
      nlinarith [hεpos, abs_nonneg (2 * s - 1), habs]
    have hdist_scaled :
        dist (t - ε + s * (2 * ε)) t * dist A B < ε * d :=
      mul_lt_mul_of_pos_right hdist_param hd_pos
    simpa [d, hε_mul_d] using hdist_scaled
  exact ⟨u, v, hu_sphere, hv_sphere, hu_open, hv_open, hz_open_uv, hinter,
    hopen_uv_ball⟩


-- [TABLET NODE: EndpointUnitDiskLocalReplacement]
lemma EndpointUnitDiskLocalReplacement {ι : Type*} [Fintype ι]
    (a b : ι → EuclideanSpace ℝ (Fin 2))
    (ha : ∀ i, dist (a i) (0 : EuclideanSpace ℝ (Fin 2)) = 1)
    (hb : ∀ i, dist (b i) (0 : EuclideanSpace ℝ (Fin 2)) = 1)
    (hdistinct : Function.Injective (fun x : ι ⊕ ι => Sum.elim a b x))
    (z : EuclideanSpace ℝ (Fin 2)) (r : ℝ)
    (hz : z ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) 1)
    (hr : 0 < r)
    (hclosed :
      Metric.closedBall z r ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) 1) :
    let κ := {i : ι // z ∈ openSegment ℝ (a i) (b i)}
    ∃ u v : κ → EuclideanSpace ℝ (Fin 2),
      ∃ Ξ : κ → PolygonalArc,
        (∀ i : κ,
          u i ∈ Metric.sphere z r ∧
            v i ∈ Metric.sphere z r ∧
              u i ∈ openSegment ℝ (a i.1) z ∧
                v i ∈ openSegment ℝ z (b i.1) ∧
                  Metric.closedBall z r ∩ segment ℝ (a i.1) (b i.1) =
                    segment ℝ (u i) (v i)) ∧
          (∀ i : κ,
            (Ξ i).source = u i ∧
              (Ξ i).target = v i ∧
                (Ξ i).carrier ⊆ Metric.closedBall z r ∧
                  (Ξ i).relativeInterior ⊆ Metric.ball z r) ∧
            (∀ ⦃i j : κ⦄,
              i ≠ j →
                ¬ ∃ m n : ℕ,
                  ∃ (hm : m + 1 < (Ξ i).vertices.length)
                    (hn : n + 1 < (Ξ j).vertices.length),
                    ∃ p q : EuclideanSpace ℝ (Fin 2),
                      p ≠ q ∧
                        segment ℝ p q ⊆
                          segment ℝ (Ξ i).vertices[m] (Ξ i).vertices[m + 1] ∩
                            segment ℝ (Ξ j).vertices[n] (Ξ j).vertices[n + 1]) ∧
              (∀ ⦃i j k : κ⦄ ⦃p : EuclideanSpace ℝ (Fin 2)⦄,
                i ≠ j → i ≠ k → j ≠ k →
                  p ∈ (Ξ i).relativeInterior →
                    p ∈ (Ξ j).relativeInterior →
                      p ∈ (Ξ k).relativeInterior → False) ∧
                (∀ ⦃i j : κ⦄ ⦃p : EuclideanSpace ℝ (Fin 2)⦄,
                  i ≠ j →
                    p ∈ (Ξ i).relativeInterior →
                      p ∈ (Ξ j).relativeInterior →
                        ∃ m n : ℕ,
                          ∃ (hm : m + 1 < (Ξ i).vertices.length)
                            (hn : n + 1 < (Ξ j).vertices.length),
                            p ∈ segment ℝ (Ξ i).vertices[m] (Ξ i).vertices[m + 1] ∧
                              p ∈ segment ℝ (Ξ j).vertices[n] (Ξ j).vertices[n + 1] ∧
                                ¬ ∃ t : ℝ,
                                  (Ξ j).vertices[n + 1] - (Ξ j).vertices[n] =
                                    t • ((Ξ i).vertices[m + 1] - (Ξ i).vertices[m])) ∧
                  (∀ ⦃i j : κ⦄ ⦃p q : EuclideanSpace ℝ (Fin 2)⦄,
                    i ≠ j →
                      p ∈ (Ξ i).relativeInterior →
                        p ∈ (Ξ j).relativeInterior →
                          q ∈ (Ξ i).relativeInterior →
                            q ∈ (Ξ j).relativeInterior →
                              p = q) ∧
                  (∀ ⦃i j : κ⦄ ⦃p : EuclideanSpace ℝ (Fin 2)⦄,
                    i ≠ j →
                      p ∈ (Ξ i).relativeInterior →
                        p ∈ (Ξ j).relativeInterior →
                          Nonempty (OrdinaryCleanLocalCrossing Ξ i j p)) := by
-- BODY
  have hindexUnique := endpointUnitDiskSegmentIndexUnique
  let κ := {i : ι // z ∈ openSegment ℝ (a i) (b i)}
  change
    ∃ u v : κ → EuclideanSpace ℝ (Fin 2),
      ∃ Ξ : κ → PolygonalArc,
        (∀ i : κ,
          u i ∈ Metric.sphere z r ∧
            v i ∈ Metric.sphere z r ∧
              u i ∈ openSegment ℝ (a i.1) z ∧
                v i ∈ openSegment ℝ z (b i.1) ∧
                  Metric.closedBall z r ∩ segment ℝ (a i.1) (b i.1) =
                    segment ℝ (u i) (v i)) ∧
          (∀ i : κ,
            (Ξ i).source = u i ∧
              (Ξ i).target = v i ∧
                (Ξ i).carrier ⊆ Metric.closedBall z r ∧
                  (Ξ i).relativeInterior ⊆ Metric.ball z r) ∧
            (∀ ⦃i j : κ⦄,
              i ≠ j →
                ¬ ∃ m n : ℕ,
                  ∃ (hm : m + 1 < (Ξ i).vertices.length)
                    (hn : n + 1 < (Ξ j).vertices.length),
                    ∃ p q : EuclideanSpace ℝ (Fin 2),
                      p ≠ q ∧
                        segment ℝ p q ⊆
                          segment ℝ (Ξ i).vertices[m] (Ξ i).vertices[m + 1] ∩
                            segment ℝ (Ξ j).vertices[n] (Ξ j).vertices[n + 1]) ∧
              (∀ ⦃i j k : κ⦄ ⦃p : EuclideanSpace ℝ (Fin 2)⦄,
                i ≠ j → i ≠ k → j ≠ k →
                  p ∈ (Ξ i).relativeInterior →
                    p ∈ (Ξ j).relativeInterior →
                      p ∈ (Ξ k).relativeInterior → False) ∧
                (∀ ⦃i j : κ⦄ ⦃p : EuclideanSpace ℝ (Fin 2)⦄,
                  i ≠ j →
                    p ∈ (Ξ i).relativeInterior →
                      p ∈ (Ξ j).relativeInterior →
                        ∃ m n : ℕ,
                          ∃ (hm : m + 1 < (Ξ i).vertices.length)
                            (hn : n + 1 < (Ξ j).vertices.length),
                            p ∈ segment ℝ (Ξ i).vertices[m] (Ξ i).vertices[m + 1] ∧
                              p ∈ segment ℝ (Ξ j).vertices[n] (Ξ j).vertices[n + 1] ∧
                                ¬ ∃ t : ℝ,
                                  (Ξ j).vertices[n + 1] - (Ξ j).vertices[n] =
                                    t • ((Ξ i).vertices[m + 1] - (Ξ i).vertices[m])) ∧
                  (∀ ⦃i j : κ⦄ ⦃p q : EuclideanSpace ℝ (Fin 2)⦄,
                    i ≠ j →
                      p ∈ (Ξ i).relativeInterior →
                        p ∈ (Ξ j).relativeInterior →
                          q ∈ (Ξ i).relativeInterior →
                            q ∈ (Ξ j).relativeInterior →
                              p = q) ∧
                  (∀ ⦃i j : κ⦄ ⦃p : EuclideanSpace ℝ (Fin 2)⦄,
                    i ≠ j →
                      p ∈ (Ξ i).relativeInterior →
                        p ∈ (Ξ j).relativeInterior →
                          Nonempty (OrdinaryCleanLocalCrossing Ξ i j p))
  have hendpoint_ne : ∀ i, a i ≠ b i := by
    intro i h
    have hsum : (Sum.inl i : ι ⊕ ι) = Sum.inr i := by
      apply hdistinct
      simp [h]
    cases hsum
  have ha_outside : ∀ i, r < dist z (a i) := by
    intro i
    have hnot : a i ∉ Metric.closedBall z r := by
      intro hai
      have hball := hclosed hai
      have hdist_lt : dist (a i) (0 : EuclideanSpace ℝ (Fin 2)) < 1 := by
        simpa [Metric.mem_ball] using hball
      linarith [ha i]
    have hnot_le : ¬ dist (a i) z ≤ r := by
      intro hle
      exact hnot (by simpa [Metric.mem_closedBall] using hle)
    have hlt : r < dist (a i) z := lt_of_not_ge hnot_le
    simpa [dist_comm] using hlt
  have hb_outside : ∀ i, r < dist z (b i) := by
    intro i
    have hnot : b i ∉ Metric.closedBall z r := by
      intro hbi
      have hball := hclosed hbi
      have hdist_lt : dist (b i) (0 : EuclideanSpace ℝ (Fin 2)) < 1 := by
        simpa [Metric.mem_ball] using hball
      linarith [hb i]
    have hnot_le : ¬ dist (b i) z ≤ r := by
      intro hle
      exact hnot (by simpa [Metric.mem_closedBall] using hle)
    have hlt : r < dist (b i) z := lt_of_not_ge hnot_le
    simpa [dist_comm] using hlt
  have chord_diameter_oriented := @endpointUnitDiskChordDiameterOriented
  have hdiameter :
      ∀ i : κ,
        ∃ u v : EuclideanSpace ℝ (Fin 2),
          u ∈ Metric.sphere z r ∧
            v ∈ Metric.sphere z r ∧
              u ∈ openSegment ℝ (a i.1) z ∧
                v ∈ openSegment ℝ z (b i.1) ∧
                  z ∈ openSegment ℝ u v ∧
                    Metric.closedBall z r ∩ segment ℝ (a i.1) (b i.1) =
                      segment ℝ u v ∧
                      openSegment ℝ u v ⊆ Metric.ball z r := by
    intro i
    exact chord_diameter_oriented (hendpoint_ne i.1) i.2 hr
      (ha_outside i.1) (hb_outside i.1)
  choose u v huv using hdiameter
  refine ⟨u, v, ?_⟩
  have huv_u_sphere : ∀ i : κ, u i ∈ Metric.sphere z r := fun i => (huv i).1
  have huv_v_sphere : ∀ i : κ, v i ∈ Metric.sphere z r := fun i => (huv i).2.1
  have huv_left_open : ∀ i : κ, u i ∈ openSegment ℝ (a i.1) z :=
    fun i => (huv i).2.2.1
  have huv_right_open : ∀ i : κ, v i ∈ openSegment ℝ z (b i.1) :=
    fun i => (huv i).2.2.2.1
  have huv_center_open : ∀ i : κ, z ∈ openSegment ℝ (u i) (v i) :=
    fun i => (huv i).2.2.2.2.1
  have huv_inter :
      ∀ i : κ,
        Metric.closedBall z r ∩ segment ℝ (a i.1) (b i.1) =
          segment ℝ (u i) (v i) :=
    fun i => (huv i).2.2.2.2.2.1
  have huv_open_ball : ∀ i : κ, openSegment ℝ (u i) (v i) ⊆ Metric.ball z r :=
    fun i => (huv i).2.2.2.2.2.2
  have huv_boundary :
      ∀ i : κ,
        u i ∈ Metric.sphere z r ∧
          v i ∈ Metric.sphere z r ∧
            u i ∈ openSegment ℝ (a i.1) z ∧
              v i ∈ openSegment ℝ z (b i.1) ∧
                Metric.closedBall z r ∩ segment ℝ (a i.1) (b i.1) =
                  segment ℝ (u i) (v i) := by
    intro i
    exact ⟨huv_u_sphere i, huv_v_sphere i, huv_left_open i,
      huv_right_open i, huv_inter i⟩
  have hu_closed : ∀ i : κ, u i ∈ Metric.closedBall z r := by
    intro i
    rw [Metric.mem_closedBall]
    exact (Metric.mem_sphere.mp (huv_u_sphere i)).le
  have hv_closed : ∀ i : κ, v i ∈ Metric.closedBall z r := by
    intro i
    rw [Metric.mem_closedBall]
    exact (Metric.mem_sphere.mp (huv_v_sphere i)).le
  have huv_ne : ∀ i : κ, u i ≠ v i := by
    intro i hsame
    have hz_inter : z ∈ Metric.closedBall z r ∩ segment ℝ (a i.1) (b i.1) := by
      constructor
      · exact Metric.mem_closedBall_self hr.le
      · exact openSegment_subset_segment ℝ (a i.1) (b i.1) i.2
    have hz_uv : z ∈ segment ℝ (u i) (v i) := by
      simpa [huv_inter i] using hz_inter
    have hzu : z = u i := by
      simpa [hsame] using hz_uv
    have hdist : dist (u i) z = r := by
      exact Metric.mem_sphere.mp (huv_u_sphere i)
    have hdist0 : dist (u i) z = 0 := by
      simp [← hzu]
    linarith
  by_cases hκsmall : Fintype.card κ ≤ 1
  · haveI : Subsingleton κ := Fintype.card_le_one_iff_subsingleton.mp hκsmall
    have hstraight :
        ∀ i : κ,
          ∃ Γ : PolygonalArc,
            Γ.source = u i ∧
              Γ.target = v i ∧
                Γ.carrier = segment ℝ (u i) (v i) ∧
                  Γ.relativeInterior = openSegment ℝ (u i) (v i) := by
      intro i
      exact StraightSegmentPolygonalArc (u i) (v i) (huv_ne i)
    choose Ξ hΞ using hstraight
    refine ⟨Ξ, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · exact huv_boundary
    · intro i
      rcases hΞ i with ⟨hsource, htarget, hcarrier, hinterior⟩
      refine ⟨hsource, htarget, ?_, ?_⟩
      · intro p hp
        have hpseg : p ∈ segment ℝ (u i) (v i) := by
          simpa [hcarrier] using hp
        have hp_inter : p ∈ Metric.closedBall z r ∩ segment ℝ (a i.1) (b i.1) := by
          simpa [huv_inter i] using hpseg
        exact hp_inter.1
      · intro p hp
        have hpopen : p ∈ openSegment ℝ (u i) (v i) := by
          simpa [hinterior] using hp
        exact huv_open_ball i hpopen
    · intro i j hij
      exfalso
      exact hij (Subsingleton.elim i j)
    · intro i j k p hij _ _ _ _ _
      exact (hij (Subsingleton.elim i j)).elim
    · intro i j p hij _ _
      exact (hij (Subsingleton.elim i j)).elim
    · intro i j p q hij _ _ _ _
      exact (hij (Subsingleton.elim i j)).elim
    · intro i j p hij _ _
      exact (hij (Subsingleton.elim i j)).elim
  ·
    -- Non-small families require the paper's geometric rectangle: choose a
    -- coordinate frame whose vertical axis avoids all incident chord directions,
    -- put the rectangle side points on the actual segments `u i -- v i`, apply
    -- `EndpointRectangularWireReplacement`, and splice the resulting wire with
    -- the orientation determined by `u i` and `v i`.  The previous arbitrary
    -- finite-real model is intentionally not used here; its side points need not
    -- lie on the incident chord.
    let point : ℝ → ℝ → EuclideanSpace ℝ (Fin 2) := endpointUnitDiskPoint
    have slope_rectangular_side_data :=
      fun (m : κ → ℝ) (δ : ℝ) (hm : Function.Injective m) (hδ : 0 < δ) =>
        endpointUnitDiskSlopeRectangularSideData r hr m δ hm hδ
    have hchord_control := EndpointUnitChordMultiplePointControl a b ha hb hdistinct
    have hv_direction_scalar :
        ∀ i : κ, ∃ c : ℝ, c ≠ 0 ∧ v i - z = c • (b i.1 - a i.1) := by
      intro i
      have hzopen := i.2
      rw [openSegment_eq_image_lineMap] at hzopen
      rcases hzopen with ⟨τ, hτ, hzτ⟩
      have hvopen := huv_right_open i
      rw [openSegment_eq_image_lineMap] at hvopen
      rcases hvopen with ⟨σ, hσ, hvσ⟩
      refine ⟨σ * (1 - τ), ?_, ?_⟩
      · have hpos : 0 < σ * (1 - τ) := by
          exact mul_pos hσ.1 (by linarith [hτ.2])
        exact ne_of_gt hpos
      · apply PiLp.ext
        intro k
        have hzcoord := congrArg (fun p : EuclideanSpace ℝ (Fin 2) => p k) hzτ
        have hvcoord := congrArg (fun p : EuclideanSpace ℝ (Fin 2) => p k) hvσ
        simp [AffineMap.lineMap_apply_module, sub_eq_add_neg] at hzcoord hvcoord ⊢
        ring_nf at hzcoord hvcoord ⊢
        have hzscaled :
            σ * z k =
              σ * (-(τ * (a i.1) k) + τ * (b i.1) k + (a i.1) k) := by
          rw [← hzcoord]
        nlinarith [hvcoord, hzscaled]
    have hchord_nonscalar :
        ∀ ⦃i j : κ⦄, i ≠ j →
          ¬ ∃ c : ℝ, b j.1 - a j.1 = c • (b i.1 - a i.1) := by
      intro i j hij
      have hij_base : i.1 ≠ j.1 := by
        intro hbase
        exact hij (Subtype.ext hbase)
      exact hchord_control.2.2.2.2 (i := i.1) (j := j.1) (p := z)
        hij_base i.2 j.2
    have hdirection_nonparallel :
        ∀ ⦃i j : κ⦄, i ≠ j →
          ¬ ∃ c : ℝ, v j - z = c • (v i - z) := by
      intro i j hij hparallel
      rcases hv_direction_scalar i with ⟨ci, hci_ne, hvi⟩
      rcases hv_direction_scalar j with ⟨cj, hcj_ne, hvj⟩
      rcases hparallel with ⟨c, hpar⟩
      apply hchord_nonscalar hij
      refine ⟨(c * ci) / cj, ?_⟩
      have hvec : cj • (b j.1 - a j.1) = (c * ci) • (b i.1 - a i.1) := by
        calc
          cj • (b j.1 - a j.1) = v j - z := hvj.symm
          _ = c • (v i - z) := hpar
          _ = c • (ci • (b i.1 - a i.1)) := by rw [hvi]
          _ = (c * ci) • (b i.1 - a i.1) := by rw [mul_smul]
      apply PiLp.ext
      intro k
      have hcoord := congrArg (fun p : EuclideanSpace ℝ (Fin 2) => p k) hvec
      simp [sub_eq_add_neg] at hcoord ⊢
      field_simp [hcj_ne]
      nlinarith
    obtain ⟨toWorld, m, htoWorld_inj, hm_inj, hframe_zero, hframe_ball,
      hframe_closedBall, hframe_segment, hframe_openSegment, hframe_reflect,
      hframe_chords⟩ :=
        EndpointUnitDiskLocalChordFrame z r hr u v huv_center_open huv_ne
          hdirection_nonparallel
    choose α β hαβ using hframe_chords
    have hα_pos : ∀ i : κ, 0 < α i := fun i => (hαβ i).1
    have hβ_pos : ∀ i : κ, 0 < β i := fun i => (hαβ i).2.1
    have hframe_orient :
        ∀ i : κ,
          (u i = toWorld (point (-(α i)) (-(m i * α i))) ∧
              v i = toWorld (point (β i) (m i * β i))) ∨
            (u i = toWorld (point (β i) (m i * β i)) ∧
              v i = toWorld (point (-(α i)) (-(m i * α i)))) :=
      fun i => (hαβ i).2.2
    have hκ_nonempty : Nonempty κ := by
      rw [← Fintype.card_pos_iff]
      by_contra hnot
      have hle0 : Fintype.card κ ≤ 0 := Nat.le_of_not_gt hnot
      exact hκsmall (hle0.trans (Nat.zero_le 1))
    letI : Nonempty κ := hκ_nonempty
    let margin : κ → ℝ := fun i => min (α i) (β i)
    have hmargin_pos : ∀ i : κ, 0 < margin i := by
      intro i
      exact lt_min (hα_pos i) (hβ_pos i)
    have huniv_nonempty : (Finset.univ : Finset κ).Nonempty := Finset.univ_nonempty
    have hinf_margin_pos : 0 < Finset.univ.inf' huniv_nonempty margin := by
      rw [Finset.lt_inf'_iff]
      intro i _
      exact hmargin_pos i
    let δ : ℝ := (Finset.univ.inf' huniv_nonempty margin) / 2
    have hδpos : 0 < δ := by
      dsimp [δ]
      linarith
    have hδlt_margin : ∀ i : κ, δ < margin i := by
      intro i
      have hhalf_lt_inf : δ < Finset.univ.inf' huniv_nonempty margin := by
        dsimp [δ]
        linarith
      exact lt_of_lt_of_le hhalf_lt_inf (Finset.inf'_le margin (by simp))
    have hδlt : ∀ i : κ, δ < α i ∧ δ < β i := by
      intro i
      have hlt := hδlt_margin i
      exact ⟨lt_of_lt_of_le hlt (min_le_left _ _),
        lt_of_lt_of_le hlt (min_le_right _ _)⟩
    obtain ⟨ε, H, L, R, hε, hεδ, hH, hLx, hRx, hLy_eq, hRy_eq,
      hLy, hRy, hLinj, hRinj, horder, hrect_ball0⟩ :=
        slope_rectangular_side_data m δ hm_inj hδpos
    have hL_rect :
        ∀ i : κ,
          L i ∈
            {p : EuclideanSpace ℝ (Fin 2) |
              -ε ≤ p 0 ∧ p 0 ≤ ε ∧ -H ≤ p 1 ∧ p 1 ≤ H} := by
      intro i
      have hy := abs_lt.mp (hLy i)
      exact ⟨by linarith [hLx i], by linarith [hLx i, hε], by linarith, by linarith⟩
    have hR_rect :
        ∀ i : κ,
          R i ∈
            {p : EuclideanSpace ℝ (Fin 2) |
              -ε ≤ p 0 ∧ p 0 ≤ ε ∧ -H ≤ p 1 ∧ p 1 ≤ H} := by
      intro i
      have hy := abs_lt.mp (hRy i)
      exact ⟨by linarith [hRx i, hε], by linarith [hRx i], by linarith, by linarith⟩
    have hL_ball0 : ∀ i : κ, L i ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) r :=
      fun i => hrect_ball0 (hL_rect i)
    have hR_ball0 : ∀ i : κ, R i ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) r :=
      fun i => hrect_ball0 (hR_rect i)
    have hL_world_ball : ∀ i : κ, toWorld (L i) ∈ Metric.ball z r :=
      fun i => hframe_ball (L i) (hL_ball0 i)
    have hR_world_ball : ∀ i : κ, toWorld (R i) ∈ Metric.ball z r :=
      fun i => hframe_ball (R i) (hR_ball0 i)
    have point_on_slope_open :
        ∀ {m α β τ : ℝ},
          0 < α →
            0 < β →
              -α < τ →
                τ < β →
                  point τ (m * τ) ∈
                    openSegment ℝ (point (-α) (m * (-α))) (point β (m * β)) := by
      intro m α β τ hα hβ hleft hright
      exact endpointUnitDiskPointOnSlopeOpen hα hβ hleft hright
    have hside_open_standard :
        ∀ i : κ,
          L i ∈
              openSegment ℝ (point (-(α i)) (-(m i * α i)))
                (point (β i) (m i * β i)) ∧
            R i ∈
              openSegment ℝ (point (-(α i)) (-(m i * α i)))
                (point (β i) (m i * β i)) := by
      intro i
      have hε_lt_α : ε < α i := lt_trans hεδ (hδlt i).1
      have hε_lt_β : ε < β i := lt_trans hεδ (hδlt i).2
      constructor
      · have h :=
          point_on_slope_open (m := m i) (α := α i) (β := β i) (τ := -ε)
            (hα_pos i) (hβ_pos i) (by linarith) (by linarith [hβ_pos i, hε])
        have hLeq : L i = point (-ε) (-(m i * ε)) := by
          apply PiLp.ext
          intro k
          fin_cases k
          · simpa [point] using hLx i
          · simpa [point] using hLy_eq i
        simpa [hLeq, mul_neg] using h
      · have h :=
          point_on_slope_open (m := m i) (α := α i) (β := β i) (τ := ε)
            (hα_pos i) (hβ_pos i) (by linarith [hα_pos i, hε]) (by linarith)
        have hReq : R i = point ε (m i * ε) := by
          apply PiLp.ext
          intro k
          fin_cases k
          · simpa [point] using hRx i
          · simpa [point] using hRy_eq i
        simpa [hReq] using h
    have hside_world_open :
        ∀ i : κ,
          toWorld (L i) ∈ openSegment ℝ (u i) (v i) ∧
            toWorld (R i) ∈ openSegment ℝ (u i) (v i) := by
      intro i
      rcases hframe_orient i with hforward | hreverse
      · rcases hforward with ⟨hu, hv⟩
        constructor
        · have himage :
              toWorld (L i) ∈
                toWorld ''
                  openSegment ℝ (point (-(α i)) (-(m i * α i)))
                    (point (β i) (m i * β i)) := by
            exact ⟨L i, (hside_open_standard i).1, rfl⟩
          rw [hframe_openSegment] at himage
          simpa [hu, hv] using himage
        · have himage :
              toWorld (R i) ∈
                toWorld ''
                  openSegment ℝ (point (-(α i)) (-(m i * α i)))
                    (point (β i) (m i * β i)) := by
            exact ⟨R i, (hside_open_standard i).2, rfl⟩
          rw [hframe_openSegment] at himage
          simpa [hu, hv] using himage
      · rcases hreverse with ⟨hu, hv⟩
        constructor
        · have himage :
              toWorld (L i) ∈
                toWorld ''
                  openSegment ℝ (point (-(α i)) (-(m i * α i)))
                    (point (β i) (m i * β i)) := by
            exact ⟨L i, (hside_open_standard i).1, rfl⟩
          rw [hframe_openSegment] at himage
          simpa [hu, hv, openSegment_symm] using himage
        · have himage :
              toWorld (R i) ∈
                toWorld ''
                  openSegment ℝ (point (-(α i)) (-(m i * α i)))
                    (point (β i) (m i * β i)) := by
            exact ⟨R i, (hside_open_standard i).2, rfl⟩
          rw [hframe_openSegment] at himage
          simpa [hu, hv, openSegment_symm] using himage
    have hside_world_chord :
        ∀ i : κ,
          toWorld (L i) ∈
              Metric.closedBall z r ∩ segment ℝ (a i.1) (b i.1) ∧
            toWorld (R i) ∈
              Metric.closedBall z r ∩ segment ℝ (a i.1) (b i.1) := by
      intro i
      constructor
      · rw [huv_inter i]
        exact openSegment_subset_segment ℝ (u i) (v i) (hside_world_open i).1
      · rw [huv_inter i]
        exact openSegment_subset_segment ℝ (u i) (v i) (hside_world_open i).2
    obtain ⟨M, Γ, hM_inj, hM_coord, hM_order, hΓ_basic, hΓ_noShared,
      hΓ_noTriple, hΓ_transverse, hΓ_unique⟩ :=
        EndpointRectangularWireReplacement ε H L R hε hH hLx hRx hLy hRy
          hLinj hRinj horder
    have hΓ_open :
        ∀ ⦃i j : κ⦄ ⦃p : EuclideanSpace ℝ (Fin 2)⦄,
          i ≠ j →
            p ∈ (Γ i).relativeInterior →
              p ∈ (Γ j).relativeInterior →
                p ∈ openSegment ℝ (M i) (R i) ∧
                  p ∈ openSegment ℝ (M j) (R j) := by
      exact EndpointRectangularWireCrossingsOpen ε L M R Γ hε hLx hRx
        hLinj hM_inj (fun i => (hM_coord i).1) hM_order
        (fun i => (hΓ_basic i).1) (fun i => (hΓ_basic i).2.2.1)
    have hM_rect :
        ∀ i : κ,
          M i ∈
            {p : EuclideanSpace ℝ (Fin 2) |
              -ε ≤ p 0 ∧ p 0 ≤ ε ∧ -H ≤ p 1 ∧ p 1 ≤ H} := by
      intro i
      have hx := (hM_coord i).1
      have hy := abs_lt.mp (hM_coord i).2
      exact ⟨by linarith [hx, hε], by linarith [hx, hε],
        by linarith, by linarith⟩
    have hM_ball0 : ∀ i : κ, M i ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) r :=
      fun i => hrect_ball0 (hM_rect i)
    have hM_world_ball : ∀ i : κ, toWorld (M i) ∈ Metric.ball z r :=
      fun i => hframe_ball (M i) (hM_ball0 i)
    have hΓ_carrier_ball0 :
        ∀ i : κ, (Γ i).carrier ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) r := by
      intro i p hp
      exact hrect_ball0 ((hΓ_basic i).2.2.2.1 hp)
    have hΓ_relative_ball0 :
        ∀ i : κ, (Γ i).relativeInterior ⊆
          Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) r := by
      intro i p hp
      have hopen := (hΓ_basic i).2.2.2.2 hp
      exact hrect_ball0
        ⟨le_of_lt hopen.1, le_of_lt hopen.2.1,
          le_of_lt hopen.2.2.1, le_of_lt hopen.2.2.2⟩
    have hΓ_basic_ball :
        ∀ i : κ,
          (Γ i).source = L i ∧
            (Γ i).target = R i ∧
              (Γ i).carrier ⊆
                  Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) r ∧
                (Γ i).relativeInterior ⊆
                  Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) r := by
      intro i
      refine ⟨(hΓ_basic i).2.1, (hΓ_basic i).2.2.1, ?_, hΓ_relative_ball0 i⟩
      intro p hp
      have hp_ball : p ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) r :=
        hΓ_carrier_ball0 i hp
      rw [Metric.mem_closedBall]
      rw [Metric.mem_ball] at hp_ball
      exact le_of_lt hp_ball
    obtain ⟨Ω, hΩ_transported, hΩ_noShared, hΩ_noTriple, hΩ_transverse,
      hΩ_unique⟩ :=
        EndpointUnitDiskLocalTransportWireFamily toWorld z r L R Γ htoWorld_inj
          hframe_closedBall hframe_ball hframe_segment hframe_openSegment
          hframe_reflect hΓ_basic_ball hΓ_noShared hΓ_noTriple hΓ_transverse
          hΓ_unique
    have hΩ_open :
        ∀ ⦃i j : κ⦄ ⦃p : EuclideanSpace ℝ (Fin 2)⦄,
          i ≠ j →
            p ∈ (Ω i).relativeInterior →
              p ∈ (Ω j).relativeInterior →
                p ∈ openSegment ℝ (toWorld (M i)) (toWorld (R i)) ∧
                  p ∈ openSegment ℝ (toWorld (M j)) (toWorld (R j)) := by
      intro i j p hij hpi hpj
      rw [(hΩ_transported i).2.2.2.2.1] at hpi
      rw [(hΩ_transported j).2.2.2.2.1] at hpj
      rcases hpi with ⟨pi, hpi, rfl⟩
      rcases hpj with ⟨pj, hpj, hpj_eq⟩
      have hpij : pj = pi := htoWorld_inj hpj_eq
      subst pj
      have hopen := hΓ_open hij hpi hpj
      constructor
      · have himage :
            toWorld pi ∈ toWorld '' openSegment ℝ (M i) (R i) :=
          ⟨pi, hopen.1, rfl⟩
        rwa [hframe_openSegment] at himage
      · have himage :
            toWorld pi ∈ toWorld '' openSegment ℝ (M j) (R j) :=
          ⟨pi, hopen.2, rfl⟩
        rwa [hframe_openSegment] at himage
    have hΩ_vertices :
        ∀ i : κ,
          (Ω i).vertices = [toWorld (L i), toWorld (M i), toWorld (R i)] := by
      intro i
      calc
        (Ω i).vertices = (Γ i).vertices.map toWorld := (hΩ_transported i).1
        _ = [toWorld (L i), toWorld (M i), toWorld (R i)] := by
          simp [(hΓ_basic i).1]
    have hΩ_carrier_ball :
        ∀ i : κ, (Ω i).carrier ⊆ Metric.ball z r := by
      intro i p hp
      have hp_image : p ∈ toWorld '' (Γ i).carrier := by
        simpa [(hΩ_transported i).2.2.2.1] using hp
      rcases hp_image with ⟨q, hq, rfl⟩
      exact hframe_ball q (hΓ_carrier_ball0 i hq)
    have hεα : ∀ i : κ, ε < α i := fun i => lt_trans hεδ (hδlt i).1
    have hεβ : ∀ i : κ, ε < β i := fun i => lt_trans hεδ (hδlt i).2
    obtain ⟨hsep_LL, hsep_LR, hsep_RR, hsep_L_LM, hsep_L_MR,
      hsep_R_LM, hsep_R_MR⟩ :=
        EndpointUnitDiskLocalConnectorSeparation toWorld m α β ε L R M
          htoWorld_inj hframe_segment hm_inj hε hεα hεβ hLx hLy_eq hRx hRy_eq
          (fun i => (hM_coord i).1) hLinj hRinj
    have segment_left_subsegment_open := @endpointUnitDiskSegmentLeftSubsegmentOpen
    have segment_right_subsegment_open := @endpointUnitDiskSegmentRightSubsegmentOpen
    have mem_segment_preimage :
        ∀ {A B p : EuclideanSpace ℝ (Fin 2)},
          p ∈ segment ℝ (toWorld A) (toWorld B) →
            ∃ q : EuclideanSpace ℝ (Fin 2),
              q ∈ segment ℝ A B ∧ toWorld q = p := by
      intro A B p hp
      have hp' : p ∈ toWorld '' segment ℝ A B := by
        simpa [hframe_segment A B] using hp
      exact hp'
    have segment_coord_le :
        ∀ {A B q : EuclideanSpace ℝ (Fin 2)} {t : ℝ},
          A 0 ≤ t →
            B 0 ≤ t →
              q ∈ segment ℝ A B →
                q 0 ≤ t := by
      intro A B q t hA hB hq
      rcases hq with ⟨a, b, ha, hb, hab, hcomb⟩
      have hx : a * A 0 + b * B 0 = q 0 := by
        have hx' := congrArg (fun p : EuclideanSpace ℝ (Fin 2) => p 0) hcomb
        simpa using hx'
      have hA' : a * A 0 ≤ a * t := mul_le_mul_of_nonneg_left hA ha
      have hB' : b * B 0 ≤ b * t := mul_le_mul_of_nonneg_left hB hb
      calc
        q 0 = a * A 0 + b * B 0 := hx.symm
        _ ≤ a * t + b * t := add_le_add hA' hB'
        _ = t := by rw [← add_mul, hab, one_mul]
    have segment_coord_ge :
        ∀ {A B q : EuclideanSpace ℝ (Fin 2)} {t : ℝ},
          t ≤ A 0 →
            t ≤ B 0 →
              q ∈ segment ℝ A B →
                t ≤ q 0 := by
      intro A B q t hA hB hq
      rcases hq with ⟨a, b, ha, hb, hab, hcomb⟩
      have hx : a * A 0 + b * B 0 = q 0 := by
        have hx' := congrArg (fun p : EuclideanSpace ℝ (Fin 2) => p 0) hcomb
        simpa using hx'
      have hA' : a * t ≤ a * A 0 := mul_le_mul_of_nonneg_left hA ha
      have hB' : b * t ≤ b * B 0 := mul_le_mul_of_nonneg_left hB hb
      calc
        t = a * t + b * t := by rw [← add_mul, hab, one_mul]
        _ ≤ a * A 0 + b * B 0 := add_le_add hA' hB'
        _ = q 0 := hx
    have eq_right_of_mem_segment_coord :
        ∀ {A B q : EuclideanSpace ℝ (Fin 2)},
          A 0 < B 0 →
            q ∈ segment ℝ A B →
              q 0 = B 0 →
                q = B := by
      intro A B q hAB hq hq0
      rcases hq with ⟨a, b, ha, hb, hab, hcomb⟩
      have hxq : a * A 0 + b * B 0 = q 0 := by
        have hx' := congrArg (fun p : EuclideanSpace ℝ (Fin 2) => p 0) hcomb
        simpa using hx'
      have hx : a * A 0 + b * B 0 = B 0 := by
        rw [hxq, hq0]
      have ha0 : a = 0 := by
        by_contra ha_ne
        have ha_pos : 0 < a := by
          exact lt_of_le_of_ne ha (fun h0a => ha_ne h0a.symm)
        have hlt_left : a * A 0 < a * B 0 :=
          mul_lt_mul_of_pos_left hAB ha_pos
        have hlt_sum : a * A 0 + b * B 0 < a * B 0 + b * B 0 := by
          nlinarith [hlt_left]
        have hright : a * B 0 + b * B 0 = B 0 := by
          rw [← add_mul, hab, one_mul]
        rw [hx, hright] at hlt_sum
        exact (lt_irrefl (B 0)) hlt_sum
      have hb1 : b = 1 := by linarith
      have hBq : B = q := by
        simpa [ha0, hb1] using hcomb
      exact hBq.symm
    have transported_adjacent_inter :
        ∀ {A B C : EuclideanSpace ℝ (Fin 2)},
          A 0 < B 0 →
            B 0 < C 0 →
              segment ℝ (toWorld A) (toWorld B) ∩
                  segment ℝ (toWorld B) (toWorld C) =
                {toWorld B} := by
      intro A B C hAB hBC
      ext p
      constructor
      · intro hp
        rcases mem_segment_preimage hp.1 with ⟨q₁, hq₁, hq₁eq⟩
        rcases mem_segment_preimage hp.2 with ⟨q₂, hq₂, hq₂eq⟩
        have hq₂_eq_q₁ : q₂ = q₁ := htoWorld_inj (by rw [hq₂eq, hq₁eq])
        have hq₁_right : q₁ ∈ segment ℝ B C := by
          simpa [hq₂_eq_q₁] using hq₂
        have hle : q₁ 0 ≤ B 0 :=
          segment_coord_le (le_of_lt hAB) (le_refl (B 0)) hq₁
        have hge : B 0 ≤ q₁ 0 :=
          segment_coord_ge (le_refl (B 0)) (le_of_lt hBC) hq₁_right
        have hq0 : q₁ 0 = B 0 := le_antisymm hle hge
        have hqB : q₁ = B := eq_right_of_mem_segment_coord hAB hq₁ hq0
        rw [Set.mem_singleton_iff]
        rw [← hq₁eq, hqB]
      · intro hp
        rw [Set.mem_singleton_iff] at hp
        subst p
        exact ⟨right_mem_segment ℝ (toWorld A) (toWorld B),
          left_mem_segment ℝ (toWorld B) (toWorld C)⟩
    have transported_disjoint_of_x_gap :
        ∀ {A B C D : EuclideanSpace ℝ (Fin 2)} {s t : ℝ},
          A 0 ≤ s →
            B 0 ≤ s →
              t ≤ C 0 →
                t ≤ D 0 →
                  s < t →
                    segment ℝ (toWorld A) (toWorld B) ∩
                        segment ℝ (toWorld C) (toWorld D) =
                      ∅ := by
      intro A B C D s t hAs hBs htC htD hst
      ext p
      constructor
      · intro hp
        rcases mem_segment_preimage hp.1 with ⟨q₁, hq₁, hq₁eq⟩
        rcases mem_segment_preimage hp.2 with ⟨q₂, hq₂, hq₂eq⟩
        have hq₂_eq_q₁ : q₂ = q₁ := htoWorld_inj (by rw [hq₂eq, hq₁eq])
        have hq₁_right : q₁ ∈ segment ℝ C D := by
          simpa [hq₂_eq_q₁] using hq₂
        have hle : q₁ 0 ≤ s := segment_coord_le hAs hBs hq₁
        have hge : t ≤ q₁ 0 := segment_coord_ge htC htD hq₁_right
        exact (hst.not_ge (hge.trans hle)).elim
      · intro hp
        cases hp
    have openSegment_coord_between :
        ∀ {A B C : EuclideanSpace ℝ (Fin 2)},
          C ∈ openSegment ℝ A B →
            A 0 < B 0 →
              A 0 < C 0 ∧ C 0 < B 0 := by
      intro A B C hC hAB
      rw [openSegment_eq_image_lineMap] at hC
      rcases hC with ⟨t, ht, htC⟩
      have hcoord := congrArg (fun p : EuclideanSpace ℝ (Fin 2) => p 0) htC
      simp [AffineMap.lineMap_apply_module] at hcoord
      constructor <;> nlinarith [ht.1, ht.2, hAB, hcoord]
    have transported_coord_between :
        ∀ {A B C : EuclideanSpace ℝ (Fin 2)},
          toWorld C ∈ openSegment ℝ (toWorld A) (toWorld B) →
            A 0 < B 0 →
              A 0 < C 0 ∧ C 0 < B 0 := by
      intro A B C hC hAB
      have himage : toWorld C ∈ toWorld '' openSegment ℝ A B := by
        simpa [hframe_openSegment A B] using hC
      rcases himage with ⟨q, hq, hqeq⟩
      have hqC : q = C := htoWorld_inj hqeq
      simpa [hqC] using openSegment_coord_between hq hAB
    have transported_neg_coord_between :
        ∀ {A B C : EuclideanSpace ℝ (Fin 2)},
          toWorld C ∈ openSegment ℝ (toWorld A) (toWorld B) →
            (fun p : EuclideanSpace ℝ (Fin 2) => -p 0) A <
              (fun p : EuclideanSpace ℝ (Fin 2) => -p 0) B →
                (fun p : EuclideanSpace ℝ (Fin 2) => -p 0) A <
                  (fun p : EuclideanSpace ℝ (Fin 2) => -p 0) C ∧
                  (fun p : EuclideanSpace ℝ (Fin 2) => -p 0) C <
                    (fun p : EuclideanSpace ℝ (Fin 2) => -p 0) B := by
      intro A B C hC hAB
      have hBA : B 0 < A 0 := by linarith
      have hC' : toWorld C ∈ openSegment ℝ (toWorld B) (toWorld A) := by
        simpa [openSegment_symm] using hC
      have hbetween := transported_coord_between hC' hBA
      constructor <;> linarith
    let Ξ : κ → PolygonalArc := fun i =>
      if hforward :
          u i = toWorld (point (-(α i)) (-(m i * α i))) ∧
            v i = toWorld (point (β i) (m i * β i)) then
        endpointUnitDiskFivePointArc
          (u i) (toWorld (L i)) (toWorld (M i)) (toWorld (R i)) (v i)
          (by
            have huL : u i ≠ toWorld (L i) := by
              intro h
              have hu_dist : dist (u i) z = r := by
                exact Metric.mem_sphere.mp (huv_u_sphere i)
              have hL_dist : dist (toWorld (L i)) z < r := by
                simpa [Metric.mem_ball] using hL_world_ball i
              rw [h] at hu_dist
              linarith
            have huM : u i ≠ toWorld (M i) := by
              intro h
              have hu_dist : dist (u i) z = r := by
                exact Metric.mem_sphere.mp (huv_u_sphere i)
              have hM_dist : dist (toWorld (M i)) z < r := by
                simpa [Metric.mem_ball] using hM_world_ball i
              rw [h] at hu_dist
              linarith
            have huR : u i ≠ toWorld (R i) := by
              intro h
              have hu_dist : dist (u i) z = r := by
                exact Metric.mem_sphere.mp (huv_u_sphere i)
              have hR_dist : dist (toWorld (R i)) z < r := by
                simpa [Metric.mem_ball] using hR_world_ball i
              rw [h] at hu_dist
              linarith
            have huV : u i ≠ v i := huv_ne i
            have hLM : toWorld (L i) ≠ toWorld (M i) := by
              intro h
              have hpre : L i = M i := htoWorld_inj h
              have hx := congrArg (fun p : EuclideanSpace ℝ (Fin 2) => p 0) hpre
              linarith [hLx i, (hM_coord i).1, hε]
            have hLR : toWorld (L i) ≠ toWorld (R i) := by
              intro h
              have hpre : L i = R i := htoWorld_inj h
              have hx := congrArg (fun p : EuclideanSpace ℝ (Fin 2) => p 0) hpre
              linarith [hLx i, hRx i, hε]
            have hLv : toWorld (L i) ≠ v i := by
              intro h
              have hL_dist : dist (toWorld (L i)) z < r := by
                simpa [Metric.mem_ball] using hL_world_ball i
              have hv_dist : dist (v i) z = r := by
                exact Metric.mem_sphere.mp (huv_v_sphere i)
              rw [h] at hL_dist
              linarith
            have hMR : toWorld (M i) ≠ toWorld (R i) := by
              intro h
              have hpre : M i = R i := htoWorld_inj h
              have hx := congrArg (fun p : EuclideanSpace ℝ (Fin 2) => p 0) hpre
              linarith [(hM_coord i).1, hRx i, hε]
            have hMv : toWorld (M i) ≠ v i := by
              intro h
              have hM_dist : dist (toWorld (M i)) z < r := by
                simpa [Metric.mem_ball] using hM_world_ball i
              have hv_dist : dist (v i) z = r := by
                exact Metric.mem_sphere.mp (huv_v_sphere i)
              rw [h] at hM_dist
              linarith
            have hRv : toWorld (R i) ≠ v i := by
              intro h
              have hR_dist : dist (toWorld (R i)) z < r := by
                simpa [Metric.mem_ball] using hR_world_ball i
              have hv_dist : dist (v i) z = r := by
                exact Metric.mem_sphere.mp (huv_v_sphere i)
              rw [h] at hR_dist
              linarith
            simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil,
              List.nodup_nil, not_false_eq_true, true_and, false_or, huL, huM,
              huR, huV, hLM, hLR, hLv, hMR, hMv, hRv]
          )
          (by
            intro n k hn hk hnk
            let Aleft : EuclideanSpace ℝ (Fin 2) :=
              point (-(α i)) (-(m i * α i))
            let Bright : EuclideanSpace ℝ (Fin 2) :=
              point (β i) (m i * β i)
            have hεα : ε < α i := lt_trans hεδ (hδlt i).1
            have hεβ : ε < β i := lt_trans hεδ (hδlt i).2
            have hA0 : Aleft 0 = -α i := by simp [Aleft, point]
            have hB0 : Bright 0 = β i := by simp [Bright, point]
            have hA_L : Aleft 0 < (L i) 0 := by
              linarith [hA0, hLx i, hεα]
            have hL_M : (L i) 0 < (M i) 0 := by
              linarith [hLx i, (hM_coord i).1, hε]
            have hM_R : (M i) 0 < (R i) 0 := by
              linarith [(hM_coord i).1, hRx i, hε]
            have hR_B : (R i) 0 < Bright 0 := by
              linarith [hRx i, hB0, hεβ]
            have h01 :
                segment ℝ (toWorld Aleft) (toWorld (L i)) ∩
                    segment ℝ (toWorld (L i)) (toWorld (M i)) =
                  {toWorld (L i)} :=
              transported_adjacent_inter hA_L hL_M
            have h12 :
                segment ℝ (toWorld (L i)) (toWorld (M i)) ∩
                    segment ℝ (toWorld (M i)) (toWorld (R i)) =
                  {toWorld (M i)} :=
              transported_adjacent_inter hL_M hM_R
            have h23 :
                segment ℝ (toWorld (M i)) (toWorld (R i)) ∩
                    segment ℝ (toWorld (R i)) (toWorld Bright) =
                  {toWorld (R i)} :=
              transported_adjacent_inter hM_R hR_B
            have h02 :
                segment ℝ (toWorld Aleft) (toWorld (L i)) ∩
                    segment ℝ (toWorld (M i)) (toWorld (R i)) =
                  ∅ :=
              transported_disjoint_of_x_gap (A := Aleft) (B := L i)
                (C := M i) (D := R i) (s := -ε) (t := 0)
                (by linarith [hA0, hεα]) (by linarith [hLx i])
                (by linarith [(hM_coord i).1]) (by linarith [hRx i, hε])
                (by linarith [hε])
            have h03 :
                segment ℝ (toWorld Aleft) (toWorld (L i)) ∩
                    segment ℝ (toWorld (R i)) (toWorld Bright) =
                  ∅ :=
              transported_disjoint_of_x_gap (A := Aleft) (B := L i)
                (C := R i) (D := Bright) (s := -ε) (t := ε)
                (by linarith [hA0, hεα]) (by linarith [hLx i])
                (by linarith [hRx i]) (by linarith [hB0, hεβ])
                (by linarith [hε])
            have h13 :
                segment ℝ (toWorld (L i)) (toWorld (M i)) ∩
                    segment ℝ (toWorld (R i)) (toWorld Bright) =
                  ∅ :=
              transported_disjoint_of_x_gap (A := L i) (B := M i)
                (C := R i) (D := Bright) (s := 0) (t := ε)
                (by linarith [hLx i, hε]) (by linarith [(hM_coord i).1])
                (by linarith [hRx i]) (by linarith [hB0, hεβ])
                (by linarith [hε])
            have hpair :
                (n = 0 ∧ k = 1) ∨ (n = 0 ∧ k = 2) ∨
                  (n = 0 ∧ k = 3) ∨ (n = 1 ∧ k = 2) ∨
                    (n = 1 ∧ k = 3) ∨ (n = 2 ∧ k = 3) := by
              have hn' : n + 1 < 5 := by simpa using hn
              have hk' : k + 1 < 5 := by simpa using hk
              omega
            rcases hpair with
              ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
              ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
            · simpa [Aleft, hforward.1] using h01
            · simpa [Aleft, hforward.1] using h02
            · simpa [Aleft, Bright, hforward.1, hforward.2] using h03
            · simpa using h12
            · simpa [Bright, hforward.2] using h13
            · simpa [Bright, hforward.2] using h23
          )
          (by
            let Aleft : EuclideanSpace ℝ (Fin 2) :=
              point (-(α i)) (-(m i * α i))
            let Bright : EuclideanSpace ℝ (Fin 2) :=
              point (β i) (m i * β i)
            have hεα : ε < α i := lt_trans hεδ (hδlt i).1
            have hεβ : ε < β i := lt_trans hεδ (hδlt i).2
            have hA0 : Aleft 0 = -α i := by simp [Aleft, point]
            have hB0 : Bright 0 = β i := by simp [Bright, point]
            have hA_L : Aleft 0 < (L i) 0 := by
              linarith [hA0, hLx i, hεα]
            have hL_M : (L i) 0 < (M i) 0 := by
              linarith [hLx i, (hM_coord i).1, hε]
            have hM_R : (M i) 0 < (R i) 0 := by
              linarith [(hM_coord i).1, hRx i, hε]
            have hR_B : (R i) 0 < Bright 0 := by
              linarith [hRx i, hB0, hεβ]
            have hstrict :
                (fun p : EuclideanSpace ℝ (Fin 2) => p 0) Aleft <
                    (fun p : EuclideanSpace ℝ (Fin 2) => p 0) (L i) ∧
                  (fun p : EuclideanSpace ℝ (Fin 2) => p 0) (L i) <
                    (fun p : EuclideanSpace ℝ (Fin 2) => p 0) (M i) ∧
                    (fun p : EuclideanSpace ℝ (Fin 2) => p 0) (M i) <
                      (fun p : EuclideanSpace ℝ (Fin 2) => p 0) (R i) ∧
                      (fun p : EuclideanSpace ℝ (Fin 2) => p 0) (R i) <
                        (fun p : EuclideanSpace ℝ (Fin 2) => p 0) Bright :=
              ⟨hA_L, hL_M, hM_R, hR_B⟩
            simpa [endpointUnitDiskFivePointAvoid, Aleft, Bright,
              hforward.1, hforward.2] using
              EndpointUnitDiskLocalFivePointVerticesAvoid toWorld
                (fun p : EuclideanSpace ℝ (Fin 2) => p 0)
                Aleft (L i) (M i) (R i) Bright transported_coord_between
                hstrict)
      else
        endpointUnitDiskFivePointArc
          (u i) (toWorld (R i)) (toWorld (M i)) (toWorld (L i)) (v i)
          (by
            have huR : u i ≠ toWorld (R i) := by
              intro h
              have hu_dist : dist (u i) z = r := by
                exact Metric.mem_sphere.mp (huv_u_sphere i)
              have hR_dist : dist (toWorld (R i)) z < r := by
                simpa [Metric.mem_ball] using hR_world_ball i
              rw [h] at hu_dist
              linarith
            have huM : u i ≠ toWorld (M i) := by
              intro h
              have hu_dist : dist (u i) z = r := by
                exact Metric.mem_sphere.mp (huv_u_sphere i)
              have hM_dist : dist (toWorld (M i)) z < r := by
                simpa [Metric.mem_ball] using hM_world_ball i
              rw [h] at hu_dist
              linarith
            have huL : u i ≠ toWorld (L i) := by
              intro h
              have hu_dist : dist (u i) z = r := by
                exact Metric.mem_sphere.mp (huv_u_sphere i)
              have hL_dist : dist (toWorld (L i)) z < r := by
                simpa [Metric.mem_ball] using hL_world_ball i
              rw [h] at hu_dist
              linarith
            have huV : u i ≠ v i := huv_ne i
            have hRM : toWorld (R i) ≠ toWorld (M i) := by
              intro h
              have hpre : R i = M i := htoWorld_inj h
              have hx := congrArg (fun p : EuclideanSpace ℝ (Fin 2) => p 0) hpre
              linarith [hRx i, (hM_coord i).1, hε]
            have hRL : toWorld (R i) ≠ toWorld (L i) := by
              intro h
              have hpre : R i = L i := htoWorld_inj h
              have hx := congrArg (fun p : EuclideanSpace ℝ (Fin 2) => p 0) hpre
              linarith [hRx i, hLx i, hε]
            have hRv : toWorld (R i) ≠ v i := by
              intro h
              have hR_dist : dist (toWorld (R i)) z < r := by
                simpa [Metric.mem_ball] using hR_world_ball i
              have hv_dist : dist (v i) z = r := by
                exact Metric.mem_sphere.mp (huv_v_sphere i)
              rw [h] at hR_dist
              linarith
            have hML : toWorld (M i) ≠ toWorld (L i) := by
              intro h
              have hpre : M i = L i := htoWorld_inj h
              have hx := congrArg (fun p : EuclideanSpace ℝ (Fin 2) => p 0) hpre
              linarith [(hM_coord i).1, hLx i, hε]
            have hMv : toWorld (M i) ≠ v i := by
              intro h
              have hM_dist : dist (toWorld (M i)) z < r := by
                simpa [Metric.mem_ball] using hM_world_ball i
              have hv_dist : dist (v i) z = r := by
                exact Metric.mem_sphere.mp (huv_v_sphere i)
              rw [h] at hM_dist
              linarith
            have hLv : toWorld (L i) ≠ v i := by
              intro h
              have hL_dist : dist (toWorld (L i)) z < r := by
                simpa [Metric.mem_ball] using hL_world_ball i
              have hv_dist : dist (v i) z = r := by
                exact Metric.mem_sphere.mp (huv_v_sphere i)
              rw [h] at hL_dist
              linarith
            simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil,
              List.nodup_nil, not_false_eq_true, true_and, false_or, huR, huM,
              huL, huV, hRM, hRL, hRv, hML, hMv, hLv]
          )
          (by
            intro n k hn hk hnk
            let Aleft : EuclideanSpace ℝ (Fin 2) :=
              point (-(α i)) (-(m i * α i))
            let Bright : EuclideanSpace ℝ (Fin 2) :=
              point (β i) (m i * β i)
            have hreverse : u i = toWorld Bright ∧ v i = toWorld Aleft := by
              rcases hframe_orient i with horient | horient
              · exact False.elim (hforward horient)
              · simpa [Aleft, Bright] using horient
            have hεα : ε < α i := lt_trans hεδ (hδlt i).1
            have hεβ : ε < β i := lt_trans hεδ (hδlt i).2
            have hA0 : Aleft 0 = -α i := by simp [Aleft, point]
            have hB0 : Bright 0 = β i := by simp [Bright, point]
            have hA_L : Aleft 0 < (L i) 0 := by
              linarith [hA0, hLx i, hεα]
            have hL_M : (L i) 0 < (M i) 0 := by
              linarith [hLx i, (hM_coord i).1, hε]
            have hM_R : (M i) 0 < (R i) 0 := by
              linarith [(hM_coord i).1, hRx i, hε]
            have hR_B : (R i) 0 < Bright 0 := by
              linarith [hRx i, hB0, hεβ]
            have h01 :
                segment ℝ (toWorld Aleft) (toWorld (L i)) ∩
                    segment ℝ (toWorld (L i)) (toWorld (M i)) =
                  {toWorld (L i)} :=
              transported_adjacent_inter hA_L hL_M
            have h12 :
                segment ℝ (toWorld (L i)) (toWorld (M i)) ∩
                    segment ℝ (toWorld (M i)) (toWorld (R i)) =
                  {toWorld (M i)} :=
              transported_adjacent_inter hL_M hM_R
            have h23 :
                segment ℝ (toWorld (M i)) (toWorld (R i)) ∩
                    segment ℝ (toWorld (R i)) (toWorld Bright) =
                  {toWorld (R i)} :=
              transported_adjacent_inter hM_R hR_B
            have h02 :
                segment ℝ (toWorld Aleft) (toWorld (L i)) ∩
                    segment ℝ (toWorld (M i)) (toWorld (R i)) =
                  ∅ :=
              transported_disjoint_of_x_gap (A := Aleft) (B := L i)
                (C := M i) (D := R i) (s := -ε) (t := 0)
                (by linarith [hA0, hεα]) (by linarith [hLx i])
                (by linarith [(hM_coord i).1]) (by linarith [hRx i, hε])
                (by linarith [hε])
            have h03 :
                segment ℝ (toWorld Aleft) (toWorld (L i)) ∩
                    segment ℝ (toWorld (R i)) (toWorld Bright) =
                  ∅ :=
              transported_disjoint_of_x_gap (A := Aleft) (B := L i)
                (C := R i) (D := Bright) (s := -ε) (t := ε)
                (by linarith [hA0, hεα]) (by linarith [hLx i])
                (by linarith [hRx i]) (by linarith [hB0, hεβ])
                (by linarith [hε])
            have h13 :
                segment ℝ (toWorld (L i)) (toWorld (M i)) ∩
                    segment ℝ (toWorld (R i)) (toWorld Bright) =
                  ∅ :=
              transported_disjoint_of_x_gap (A := L i) (B := M i)
                (C := R i) (D := Bright) (s := 0) (t := ε)
                (by linarith [hLx i, hε]) (by linarith [(hM_coord i).1])
                (by linarith [hRx i]) (by linarith [hB0, hεβ])
                (by linarith [hε])
            have hpair :
                (n = 0 ∧ k = 1) ∨ (n = 0 ∧ k = 2) ∨
                  (n = 0 ∧ k = 3) ∨ (n = 1 ∧ k = 2) ∨
                    (n = 1 ∧ k = 3) ∨ (n = 2 ∧ k = 3) := by
              have hn' : n + 1 < 5 := by simpa using hn
              have hk' : k + 1 < 5 := by simpa using hk
              omega
            rcases hpair with
              ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
              ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
            · simpa [Bright, hreverse.1, segment_symm, Set.inter_comm] using h23
            · simpa [Bright, hreverse.1, segment_symm, Set.inter_comm] using h13
            · simpa [Aleft, Bright, hreverse.1, hreverse.2, segment_symm,
                Set.inter_comm] using h03
            · simpa [segment_symm, Set.inter_comm] using h12
            · simpa [Aleft, hreverse.2, segment_symm, Set.inter_comm] using h02
            · simpa [Aleft, hreverse.2, segment_symm, Set.inter_comm] using h01
          )
          (by
            let Aleft : EuclideanSpace ℝ (Fin 2) :=
              point (-(α i)) (-(m i * α i))
            let Bright : EuclideanSpace ℝ (Fin 2) :=
              point (β i) (m i * β i)
            have hreverse : u i = toWorld Bright ∧ v i = toWorld Aleft := by
              rcases hframe_orient i with horient | horient
              · exact False.elim (hforward horient)
              · simpa [Aleft, Bright] using horient
            have hεα : ε < α i := lt_trans hεδ (hδlt i).1
            have hεβ : ε < β i := lt_trans hεδ (hδlt i).2
            have hA0 : Aleft 0 = -α i := by simp [Aleft, point]
            have hB0 : Bright 0 = β i := by simp [Bright, point]
            have hA_L : Aleft 0 < (L i) 0 := by
              linarith [hA0, hLx i, hεα]
            have hL_M : (L i) 0 < (M i) 0 := by
              linarith [hLx i, (hM_coord i).1, hε]
            have hM_R : (M i) 0 < (R i) 0 := by
              linarith [(hM_coord i).1, hRx i, hε]
            have hR_B : (R i) 0 < Bright 0 := by
              linarith [hRx i, hB0, hεβ]
            have hstrict :
                (fun p : EuclideanSpace ℝ (Fin 2) => -p 0) Bright <
                    (fun p : EuclideanSpace ℝ (Fin 2) => -p 0) (R i) ∧
                  (fun p : EuclideanSpace ℝ (Fin 2) => -p 0) (R i) <
                    (fun p : EuclideanSpace ℝ (Fin 2) => -p 0) (M i) ∧
                    (fun p : EuclideanSpace ℝ (Fin 2) => -p 0) (M i) <
                      (fun p : EuclideanSpace ℝ (Fin 2) => -p 0) (L i) ∧
                      (fun p : EuclideanSpace ℝ (Fin 2) => -p 0) (L i) <
                        (fun p : EuclideanSpace ℝ (Fin 2) => -p 0) Aleft := by
              constructor
              · linarith [hR_B]
              constructor
              · linarith [hM_R]
              constructor
              · linarith [hL_M]
              · linarith [hA_L]
            simpa [endpointUnitDiskFivePointAvoid, Aleft, Bright,
              hreverse.1, hreverse.2] using
              EndpointUnitDiskLocalFivePointVerticesAvoid toWorld
                (fun p : EuclideanSpace ℝ (Fin 2) => -p 0)
                Bright (R i) (M i) (L i) Aleft transported_neg_coord_between
                hstrict)
    have hΞbasic :
        ∀ i : κ,
          (Ξ i).source = u i ∧
            (Ξ i).target = v i ∧
              (Ξ i).carrier ⊆ Metric.closedBall z r ∧
                (Ξ i).relativeInterior ⊆ Metric.ball z r := by
      intro i
      by_cases hforward :
          u i = toWorld (point (-(α i)) (-(m i * α i))) ∧
            v i = toWorld (point (β i) (m i * β i))
      · refine ⟨by simp [Ξ, hforward], by simp [Ξ, hforward], ?_, ?_⟩
        · intro p hp
          simp [Ξ, hforward] at hp
          rcases hp with ⟨n, hn, hpseg⟩
          have hn_cases : n = 0 ∨ n = 1 ∨ n = 2 ∨ n = 3 := by
            omega
          have hL_closed : toWorld (L i) ∈ Metric.closedBall z r := by
            rw [Metric.mem_closedBall]
            exact le_of_lt (by simpa [Metric.mem_ball] using hL_world_ball i)
          have hM_closed : toWorld (M i) ∈ Metric.closedBall z r := by
            rw [Metric.mem_closedBall]
            exact le_of_lt (by simpa [Metric.mem_ball] using hM_world_ball i)
          have hR_closed : toWorld (R i) ∈ Metric.closedBall z r := by
            rw [Metric.mem_closedBall]
            exact le_of_lt (by simpa [Metric.mem_ball] using hR_world_ball i)
          rcases hn_cases with rfl | rfl | rfl | rfl
          · exact (convex_closedBall z r).segment_subset (hu_closed i) hL_closed
              (by simpa [hforward.1] using hpseg)
          · exact (convex_closedBall z r).segment_subset hL_closed hM_closed
              (by simpa using hpseg)
          · exact (convex_closedBall z r).segment_subset hM_closed hR_closed
              (by simpa using hpseg)
          · exact (convex_closedBall z r).segment_subset hR_closed (hv_closed i)
              (by simpa [hforward.2] using hpseg)
        · intro p hp
          simp [Ξ, hforward] at hp
          rcases hp with ⟨⟨n, hn, hpseg⟩, hpnot⟩
          have hn_cases : n = 0 ∨ n = 1 ∨ n = 2 ∨ n = 3 := by
            omega
          rcases hn_cases with rfl | rfl | rfl | rfl
          · have hpopen :
                p ∈ openSegment ℝ (u i) (v i) :=
              segment_left_subsegment_open (hside_world_open i).1
                (by simpa [hforward.1] using hpseg)
                (by simpa [hforward.1] using hpnot.1)
            exact huv_open_ball i hpopen
          · have hpΩ : p ∈ (Ω i).carrier := by
              rw [(Ω i).carrier_eq]
              refine ⟨0, ?_, ?_⟩
              · simpa [hΩ_vertices i]
              · simpa [hΩ_vertices i] using hpseg
            exact hΩ_carrier_ball i hpΩ
          · have hpΩ : p ∈ (Ω i).carrier := by
              rw [(Ω i).carrier_eq]
              refine ⟨1, ?_, ?_⟩
              · simpa [hΩ_vertices i]
              · simpa [hΩ_vertices i] using hpseg
            exact hΩ_carrier_ball i hpΩ
          · have hpopen :
                p ∈ openSegment ℝ (u i) (v i) :=
              segment_right_subsegment_open (hside_world_open i).2
                (by simpa [hforward.2] using hpseg)
                (by simpa [hforward.2] using hpnot.2)
            exact huv_open_ball i hpopen
      · refine ⟨by simp [Ξ, hforward], by simp [Ξ, hforward], ?_, ?_⟩
        · intro p hp
          simp [Ξ, hforward] at hp
          rcases hp with ⟨n, hn, hpseg⟩
          have hn_cases : n = 0 ∨ n = 1 ∨ n = 2 ∨ n = 3 := by
            omega
          have hL_closed : toWorld (L i) ∈ Metric.closedBall z r := by
            rw [Metric.mem_closedBall]
            exact le_of_lt (by simpa [Metric.mem_ball] using hL_world_ball i)
          have hM_closed : toWorld (M i) ∈ Metric.closedBall z r := by
            rw [Metric.mem_closedBall]
            exact le_of_lt (by simpa [Metric.mem_ball] using hM_world_ball i)
          have hR_closed : toWorld (R i) ∈ Metric.closedBall z r := by
            rw [Metric.mem_closedBall]
            exact le_of_lt (by simpa [Metric.mem_ball] using hR_world_ball i)
          rcases hn_cases with rfl | rfl | rfl | rfl
          · exact (convex_closedBall z r).segment_subset (hu_closed i) hR_closed
              (by simpa using hpseg)
          · exact (convex_closedBall z r).segment_subset hR_closed hM_closed
              (by simpa using hpseg)
          · exact (convex_closedBall z r).segment_subset hM_closed hL_closed
              (by simpa using hpseg)
          · exact (convex_closedBall z r).segment_subset hL_closed (hv_closed i)
              (by simpa using hpseg)
        · intro p hp
          simp [Ξ, hforward] at hp
          rcases hp with ⟨⟨n, hn, hpseg⟩, hpnot⟩
          have hn_cases : n = 0 ∨ n = 1 ∨ n = 2 ∨ n = 3 := by
            omega
          rcases hn_cases with rfl | rfl | rfl | rfl
          · have hpopen :
                p ∈ openSegment ℝ (u i) (v i) :=
              segment_left_subsegment_open (hside_world_open i).2
                (by simpa using hpseg)
                (by simpa using hpnot.1)
            exact huv_open_ball i hpopen
          · have hpΩ : p ∈ (Ω i).carrier := by
              rw [(Ω i).carrier_eq]
              refine ⟨1, ?_, ?_⟩
              · simpa [hΩ_vertices i]
              · rw [segment_symm]
                simpa [hΩ_vertices i] using hpseg
            exact hΩ_carrier_ball i hpΩ
          · have hpΩ : p ∈ (Ω i).carrier := by
              rw [(Ω i).carrier_eq]
              refine ⟨0, ?_, ?_⟩
              · simpa [hΩ_vertices i]
              · rw [segment_symm]
                simpa [hΩ_vertices i] using hpseg
            exact hΩ_carrier_ball i hpΩ
          · have hpopen :
                p ∈ openSegment ℝ (u i) (v i) :=
              segment_right_subsegment_open (hside_world_open i).1
                (by simpa using hpseg)
                (by simpa using hpnot.2)
            exact huv_open_ball i hpopen
    have hΞ_orient :
        ∀ i : κ,
          ((Ξ i).vertices =
              [u i, toWorld (L i), toWorld (M i), toWorld (R i), v i] ∧
              u i = toWorld (point (-(α i)) (-(m i * α i))) ∧
                v i = toWorld (point (β i) (m i * β i))) ∨
            ((Ξ i).vertices =
              [u i, toWorld (R i), toWorld (M i), toWorld (L i), v i] ∧
              u i = toWorld (point (β i) (m i * β i)) ∧
                v i = toWorld (point (-(α i)) (-(m i * α i)))) := by
      intro i
      by_cases hforward :
          u i = toWorld (point (-(α i)) (-(m i * α i))) ∧
            v i = toWorld (point (β i) (m i * β i))
      · left
        refine ⟨?_, hforward.1, hforward.2⟩
        simp [Ξ, hforward]
      · right
        have hreverse :
            u i = toWorld (point (β i) (m i * β i)) ∧
              v i = toWorld (point (-(α i)) (-(m i * α i))) := by
          rcases hframe_orient i with horient | horient
          · exact False.elim (hforward horient)
          · exact horient
        refine ⟨?_, hreverse.1, hreverse.2⟩
        simp [Ξ, hforward]
    have hΞnoShared :=
      EndpointUnitDiskLocalSpliceNoShared
          (fun i : κ => toWorld (point (-(α i)) (-(m i * α i))))
          (fun i : κ => toWorld (L i))
          (fun i : κ => toWorld (M i))
          (fun i : κ => toWorld (R i))
          (fun i : κ => toWorld (point (β i) (m i * β i)))
          u v Ω Ξ hΞ_orient hΩ_vertices hsep_LL hsep_LR hsep_RR
        hsep_L_LM hsep_L_MR hsep_R_LM hsep_R_MR hΩ_noShared
    have hΞ_noTriple_unique :=
      EndpointUnitDiskLocalSpliceNoTripleUnique
        (fun i : κ => toWorld (point (-(α i)) (-(m i * α i))))
        (fun i : κ => toWorld (L i))
        (fun i : κ => toWorld (M i))
        (fun i : κ => toWorld (R i))
        (fun i : κ => toWorld (point (β i) (m i * β i)))
        u v Ω Ξ hΞ_orient hΩ_vertices
        (fun i : κ => (hΩ_transported i).2.1)
        (fun i : κ => (hΩ_transported i).2.2.1)
        hsep_LL hsep_LR hsep_RR hsep_L_LM hsep_L_MR hsep_R_LM hsep_R_MR
        hΩ_noTriple hΩ_unique
    have hΞnoTriple := hΞ_noTriple_unique.1
    have hΞtransverse :=
      EndpointUnitDiskLocalSpliceTransverse
          (fun i : κ => toWorld (point (-(α i)) (-(m i * α i))))
          (fun i : κ => toWorld (L i))
          (fun i : κ => toWorld (M i))
          (fun i : κ => toWorld (R i))
          (fun i : κ => toWorld (point (β i) (m i * β i)))
          u v Ω Ξ hΞ_orient hΩ_vertices
          (fun i : κ => (hΩ_transported i).2.1)
          (fun i : κ => (hΩ_transported i).2.2.1)
          hsep_LL hsep_LR hsep_RR hsep_L_LM hsep_L_MR hsep_R_LM hsep_R_MR
        hΩ_transverse
    have hΞopen :=
      EndpointUnitDiskLocalSpliceCrossingsOpen
        (fun i : κ => toWorld (point (-(α i)) (-(m i * α i))))
        (fun i : κ => toWorld (L i))
        (fun i : κ => toWorld (M i))
        (fun i : κ => toWorld (R i))
        (fun i : κ => toWorld (point (β i) (m i * β i)))
        u v Ω Ξ hΞ_orient hΩ_vertices
        (fun i : κ => (hΩ_transported i).2.1)
        (fun i : κ => (hΩ_transported i).2.2.1)
        hsep_LL hsep_LR hsep_RR hsep_L_LM hsep_L_MR hsep_R_LM hsep_R_MR
        hΩ_open
    have hΞunique := hΞ_noTriple_unique.2
    have hΞclean :
        ∀ ⦃i j : κ⦄ ⦃p : EuclideanSpace ℝ (Fin 2)⦄,
          i ≠ j →
            p ∈ (Ξ i).relativeInterior →
              p ∈ (Ξ j).relativeInterior →
                Nonempty (OrdinaryCleanLocalCrossing Ξ i j p) := by
      intro i j p hij hpi hpj
      rcases hΞopen hij hpi hpj with ⟨mi, mj, hmi, hmj, hpmi, hpmj⟩
      rcases hΞtransverse hij hpi hpj with
        ⟨mi', mj', hmi', hmj', hpmi', hpmj', hnonparallel⟩
      have hmi_eq : mi = mi' :=
        hindexUnique (Ξ i) p mi mi' hmi hmi' hpmi hpmi'
      have hmj_eq : mj = mj' :=
        hindexUnique (Ξ j) p mj mj' hmj hmj' hpmj hpmj'
      subst mi'
      subst mj'
      have hendpoint_free :
          ∀ k : κ, p ≠ (Ξ k).source ∧ p ≠ (Ξ k).target := by
        intro k
        have hpball : p ∈ Metric.ball z r := (hΞbasic i).2.2.2 hpi
        have hpdist : dist p z < r := by
          simpa [Metric.mem_ball] using hpball
        constructor
        · intro hpsource
          have hdist : dist p z = r := by
            rw [hpsource, (hΞbasic k).1]
            exact Metric.mem_sphere.mp (huv_u_sphere k)
          linarith
        · intro hptarget
          have hdist : dist p z = r := by
            rw [hptarget, (hΞbasic k).2.1]
            exact Metric.mem_sphere.mp (huv_v_sphere k)
          linarith
      obtain ⟨C, _hfirst, _hsecond⟩ :=
        OrdinaryCleanLocalCrossingOfOpenSegments Ξ i j p hij hpi hpj
          hΞnoTriple hendpoint_free
          (fun q hqi hqj => hΞunique hij hqi hqj hpi hpj)
          mi mj hmi hmj hpmi hpmj hnonparallel
      exact ⟨C⟩
    exact ⟨Ξ, huv_boundary, hΞbasic, hΞnoShared, hΞnoTriple, hΞtransverse,
      hΞunique, hΞclean⟩
