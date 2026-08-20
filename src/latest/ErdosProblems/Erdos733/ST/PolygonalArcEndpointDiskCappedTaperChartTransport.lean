import ErdosProblems.Erdos733.ST.PolygonalArcEndpointDiskCappedTaperModel
import ErdosProblems.Erdos733.ST.PlanarRot90CoefficientUniqueness

open Set
open Classical
noncomputable section

-- [TABLET NODE: PolygonalArcEndpointDiskCappedTaperChartTransport]
lemma PolygonalArcEndpointDiskCappedTaperChartTransport
    (p0 p1 : EuclideanSpace ℝ (Fin 2)) (r K : ℝ)
    (hp : p1 ≠ p0) (hr : 0 < r) (hK : 0 < K) :
    let d : EuclideanSpace ℝ (Fin 2) := p1 - p0
    let chart : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 2) :=
      fun z => p0 + z 0 • d + z 1 • PlanarRot90 d
    let a : ℝ := r / dist p0 p1
    let C : Set (EuclideanSpace ℝ (Fin 2)) :=
      {z | 0 < z 0 ∧ z 0 ^ 2 + z 1 ^ 2 < a ^ 2 ∧ -K * z 0 < z 1 ∧
        z 1 < K * z 0}
    let L : Set (EuclideanSpace ℝ (Fin 2)) :=
      {z | 0 < z 0 ∧ z 0 ^ 2 + z 1 ^ 2 < a ^ 2 ∧ 0 < z 1 ∧
        z 1 < K * z 0}
    let R : Set (EuclideanSpace ℝ (Fin 2)) :=
      {z | 0 < z 0 ∧ z 0 ^ 2 + z 1 ^ 2 < a ^ 2 ∧ -K * z 0 < z 1 ∧
        z 1 < 0}
    let G : Set (EuclideanSpace ℝ (Fin 2)) :=
      {z | 0 < z 0 ∧ z 0 < a ∧ z 1 = 0}
    0 < a ∧
      IsOpen C ∧ IsOpen L ∧ IsOpen R ∧
      IsConnected L ∧ IsConnected R ∧
      IsConnected (chart '' L) ∧ IsConnected (chart '' R) ∧
      Disjoint L R ∧ Disjoint (chart '' L) (chart '' R) ∧
      (0 : EuclideanSpace ℝ (Fin 2)) ∉ C ∧ G ⊆ C ∧ C \ G = L ∪ R ∧
      (∀ z : EuclideanSpace ℝ (Fin 2),
        z 0 ^ 2 + z 1 ^ 2 < a ^ 2 → chart z ∈ Metric.ball p0 r) ∧
      chart '' C ⊆ Metric.ball p0 r ∧
      p0 ∉ chart '' C ∧
      (∀ {t : ℝ}, 0 < t →
        chart (WithLp.toLp 2 (fun i : Fin 2 => if i = 0 then t else 0)) ≠ p0) ∧
      ((AffineMap.lineMap p0 p1) '' Set.Ioo (0 : ℝ) a ⊆ chart '' G) ∧
      chart '' C \ chart '' G = chart '' L ∪ chart '' R := by
-- BODY
  intro d chart a C L R G
  have hd : d ≠ 0 := by
    intro h
    apply hp
    simpa [d, sub_eq_zero] using h
  have hdist_pos : 0 < dist p0 p1 := dist_pos.mpr (Ne.symm hp)
  have hnormd_pos : 0 < ‖d‖ := norm_pos_iff.mpr hd
  have hdist_eq_normd : dist p0 p1 = ‖d‖ := by
    rw [dist_eq_norm]
    have hneg : p0 - p1 = -d := by
      dsimp [d]
      abel
    rw [hneg, norm_neg]
  have ha_pos : 0 < a := by
    dsimp [a]
    exact div_pos hr hdist_pos
  have hscale_sq : a ^ 2 * ‖d‖ ^ 2 = r ^ 2 := by
    dsimp [a]
    rw [hdist_eq_normd]
    field_simp [ne_of_gt hnormd_pos]
  have hnorm_sq :
      ∀ z : EuclideanSpace ℝ (Fin 2),
        ‖z 0 • d + z 1 • PlanarRot90 d‖ ^ 2 =
          (z 0 ^ 2 + z 1 ^ 2) * ‖d‖ ^ 2 := by
    intro z
    have horth : inner ℝ (z 0 • d) (z 1 • PlanarRot90 d) = 0 := by
      rw [inner_smul_left, inner_smul_right, PlanarRot90Orthogonal]
      ring
    have hpyth :
        ‖z 0 • d + z 1 • PlanarRot90 d‖ ^ 2 =
          ‖z 0 • d‖ ^ 2 + ‖z 1 • PlanarRot90 d‖ ^ 2 := by
      simpa [pow_two] using norm_add_sq_eq_norm_sq_add_norm_sq_real horth
    rw [hpyth, norm_smul, norm_smul, PlanarRot90Norm]
    rw [Real.norm_eq_abs, Real.norm_eq_abs]
    rw [mul_pow, mul_pow, sq_abs, sq_abs]
    ring
  have hchart_cont : Continuous chart := by
    dsimp [chart]
    fun_prop
  have hchart_zero : chart (0 : EuclideanSpace ℝ (Fin 2)) = p0 := by
    dsimp [chart]
    simp
  have hchart_inj : Function.Injective chart := by
    intro z w hzw
    have hrep :
        (0 : EuclideanSpace ℝ (Fin 2)) =
          (z 0 - w 0) • d + (z 1 - w 1) • PlanarRot90 d := by
      have hzero : chart z - chart w = (0 : EuclideanSpace ℝ (Fin 2)) :=
        sub_eq_zero.mpr hzw
      have hdiff :
          chart z - chart w =
            (z 0 - w 0) • d + (z 1 - w 1) • PlanarRot90 d := by
        apply PiLp.ext
        intro k
        fin_cases k <;> simp [chart] <;> ring
      rw [← hdiff]
      exact hzero.symm
    have hcoeff :=
      PlanarRot90CoefficientUniqueness (d := d)
        (v := (0 : EuclideanSpace ℝ (Fin 2))) hd hrep
    have hz0 : z 0 = w 0 := by
      have h : z 0 - w 0 = 0 := by
        simpa using hcoeff.1
      linarith
    have hz1 : z 1 = w 1 := by
      have h : z 1 - w 1 = 0 := by
        simpa using hcoeff.2
      linarith
    apply PiLp.ext
    intro k
    fin_cases k
    · exact hz0
    · exact hz1
  have hmodel :
      IsOpen C ∧ IsOpen L ∧ IsOpen R ∧
        IsConnected L ∧ IsConnected R ∧
        Disjoint L R ∧ (0 : EuclideanSpace ℝ (Fin 2)) ∉ C ∧
        G ⊆ C ∧ C \ G = L ∪ R := by
    simpa [C, L, R, G] using PolygonalArcEndpointDiskCappedTaperModel a K ha_pos hK
  rcases hmodel with
    ⟨hC_open, hL_open, hR_open, hL_conn, hR_conn, hLR_disj, h0_not_C, hG_sub_C,
      hsplit⟩
  have hdisk_to_ball :
      ∀ z : EuclideanSpace ℝ (Fin 2),
        z 0 ^ 2 + z 1 ^ 2 < a ^ 2 → chart z ∈ Metric.ball p0 r := by
    intro z hz
    rw [Metric.mem_ball, dist_eq_norm]
    have hsub :
        p0 + z 0 • d + z 1 • PlanarRot90 d - p0 =
          z 0 • d + z 1 • PlanarRot90 d := by
      abel
    dsimp [chart]
    rw [hsub]
    rw [← sq_lt_sq₀ (norm_nonneg _) (le_of_lt hr)]
    rw [hnorm_sq z]
    have hmul : (z 0 ^ 2 + z 1 ^ 2) * ‖d‖ ^ 2 < a ^ 2 * ‖d‖ ^ 2 :=
      mul_lt_mul_of_pos_right hz (sq_pos_of_pos hnormd_pos)
    simpa [hscale_sq] using hmul
  have himage_C_ball : chart '' C ⊆ Metric.ball p0 r := by
    rintro x ⟨z, hzC, rfl⟩
    dsimp [C] at hzC
    exact hdisk_to_ball z hzC.2.1
  have hp0_not_image_C : p0 ∉ chart '' C := by
    rintro ⟨z, hzC, hz⟩
    have hz_eq_zero : z = 0 := by
      apply hchart_inj
      simpa [hchart_zero] using hz
    dsimp [C] at hzC
    have : z 0 = 0 := by
      rw [hz_eq_zero]
      simp
    linarith
  have hcoord_omit :
      ∀ {t : ℝ}, 0 < t →
        chart (WithLp.toLp 2 (fun i : Fin 2 => if i = 0 then t else 0)) ≠ p0 := by
    intro t ht hchart
    have hcoord_eq_zero :
        WithLp.toLp 2 (fun i : Fin 2 => if i = 0 then t else 0) =
          (0 : EuclideanSpace ℝ (Fin 2)) := by
      apply hchart_inj
      simpa [hchart_zero] using hchart
    have ht_zero : t = 0 := by
      have h := congrArg (fun z : EuclideanSpace ℝ (Fin 2) => z 0) hcoord_eq_zero
      simpa using h
    linarith
  have hgerm :
      (AffineMap.lineMap p0 p1) '' Set.Ioo (0 : ℝ) a ⊆ chart '' G := by
    rintro x ⟨t, ht, rfl⟩
    refine ⟨WithLp.toLp 2 (fun i : Fin 2 => if i = 0 then t else 0), ?_, ?_⟩
    · dsimp
      constructor
      · simpa using ht.1
      constructor
      · simpa using ht.2
      · simp
    · dsimp [chart, d]
      apply PiLp.ext
      intro k
      fin_cases k <;> simp [AffineMap.lineMap_apply_module]
      · ring
      · ring
  have himage_disj : Disjoint (chart '' L) (chart '' R) := by
    rw [Set.disjoint_left]
    rintro x ⟨z, hzL, rfl⟩ ⟨w, hwR, hw_eq⟩
    have hwz : w = z := hchart_inj hw_eq
    rw [hwz] at hwR
    exact (Set.disjoint_left.mp hLR_disj hzL) hwR
  have himage_split : chart '' C \ chart '' G = chart '' L ∪ chart '' R := by
    ext x
    constructor
    · rintro ⟨⟨z, hzC, rfl⟩, hxnotG⟩
      have hznotG : z ∉ G := by
        intro hzG
        exact hxnotG ⟨z, hzG, rfl⟩
      have hzLR : z ∈ L ∪ R := by
        have hzCG : z ∈ C \ G := ⟨hzC, hznotG⟩
        simpa [hsplit] using hzCG
      rcases hzLR with hzL | hzR
      · exact Or.inl ⟨z, hzL, rfl⟩
      · exact Or.inr ⟨z, hzR, rfl⟩
    · rintro (⟨z, hzL, rfl⟩ | ⟨z, hzR, rfl⟩)
      · have hzCG : z ∈ C \ G := by
          have hzLR : z ∈ L ∪ R := Or.inl hzL
          simpa [hsplit] using hzLR
        refine ⟨⟨z, hzCG.1, rfl⟩, ?_⟩
        rintro ⟨g, hgG, hg_eq⟩
        have hgz : g = z := hchart_inj hg_eq
        rw [hgz] at hgG
        exact hzCG.2 hgG
      · have hzCG : z ∈ C \ G := by
          have hzLR : z ∈ L ∪ R := Or.inr hzR
          simpa [hsplit] using hzLR
        refine ⟨⟨z, hzCG.1, rfl⟩, ?_⟩
        rintro ⟨g, hgG, hg_eq⟩
        have hgz : g = z := hchart_inj hg_eq
        rw [hgz] at hgG
        exact hzCG.2 hgG
  exact ⟨ha_pos, hC_open, hL_open, hR_open, hL_conn, hR_conn,
    hL_conn.image chart hchart_cont.continuousOn,
    hR_conn.image chart hchart_cont.continuousOn,
    hLR_disj, himage_disj, h0_not_C, hG_sub_C, hsplit, hdisk_to_ball,
    himage_C_ball, hp0_not_image_C, hcoord_omit, hgerm, himage_split⟩

