import Util.IncidenceGeometry.PlanarRot90LinearCombination
import Util.IncidenceGeometry.PlanarRot90CoefficientUniqueness
import Util.IncidenceGeometry.PlanarRot90Decomposition
import Util.IncidenceGeometry.PlanarRot90Norm
import Util.IncidenceGeometry.PlanarRot90Orthogonal

open Classical
noncomputable section

lemma PlanarClockwiseTwoRayEndpointConesInSector
    (p base other : EuclideanSpace ℝ (Fin 2)) (rho c s : ℝ)
    (hrho : 0 < rho) (hbase : base ≠ 0) (hother : other ≠ 0)
    (hs : 0 < s)
    (hother_eq : other = c • base - s • PlanarRot90 base) :
    let baseChart : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 2) :=
      fun z => p + z 0 • base + z 1 • PlanarRot90 base
    let otherChart : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 2) :=
      fun z => p + z 0 • other + z 1 • PlanarRot90 other
    let sector : Set (EuclideanSpace ℝ (Fin 2)) :=
      baseChart ''
        {z | z 0 ^ 2 + z 1 ^ 2 < (rho / ‖base‖) ^ 2 ∧
          z 1 < 0 ∧ 0 < c * z 1 + s * z 0}
    IsOpen sector ∧ IsConnected sector ∧
      ∃ r K : ℝ, 0 < r ∧ 0 < K ∧
        baseChart ''
            {z | 0 < z 0 ∧ z 0 ^ 2 + z 1 ^ 2 < (r / ‖base‖) ^ 2 ∧
              -K * z 0 < z 1 ∧ z 1 < 0} ⊆ sector ∧
          otherChart ''
            {z | 0 < z 0 ∧ z 0 ^ 2 + z 1 ^ 2 < (r / ‖other‖) ^ 2 ∧
              0 < z 1 ∧ z 1 < K * z 0} ⊆ sector := by
  dsimp only
  let baseChart : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 2) :=
    fun z => p + z 0 • base + z 1 • PlanarRot90 base
  let otherChart : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 2) :=
    fun z => p + z 0 • other + z 1 • PlanarRot90 other
  let coordSet : Set (EuclideanSpace ℝ (Fin 2)) :=
    {z | z 0 ^ 2 + z 1 ^ 2 < (rho / ‖base‖) ^ 2 ∧
      z 1 < 0 ∧ 0 < c * z 1 + s * z 0}
  have hbase_norm_pos : 0 < ‖base‖ := norm_pos_iff.mpr hbase
  have hother_norm_pos : 0 < ‖other‖ := norm_pos_iff.mpr hother
  have hR_pos : 0 < rho / ‖base‖ := div_pos hrho hbase_norm_pos
  have hnormsq_coord (z : EuclideanSpace ℝ (Fin 2)) :
      z 0 ^ 2 + z 1 ^ 2 = ‖z‖ ^ 2 := by
    rw [← real_inner_self_eq_norm_sq, PiLp.inner_apply]
    simp
  have hdisk_eq :
      {z : EuclideanSpace ℝ (Fin 2) | z 0 ^ 2 + z 1 ^ 2 < (rho / ‖base‖) ^ 2} =
        Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) (rho / ‖base‖) := by
    ext z
    rw [Set.mem_setOf_eq, Metric.mem_ball]
    simp [hnormsq_coord z, (sq_lt_sq₀ (norm_nonneg z) (le_of_lt hR_pos))]
  have hcoord_open : IsOpen coordSet := by
    have hdisk :
        IsOpen {z : EuclideanSpace ℝ (Fin 2) |
          z 0 ^ 2 + z 1 ^ 2 < (rho / ‖base‖) ^ 2} := by
      exact isOpen_lt (by fun_prop) continuous_const
    have hyneg : IsOpen {z : EuclideanSpace ℝ (Fin 2) | z 1 < 0} := by
      exact isOpen_lt (by fun_prop) continuous_const
    have hboundary :
        IsOpen {z : EuclideanSpace ℝ (Fin 2) | 0 < c * z 1 + s * z 0} := by
      exact isOpen_lt continuous_const (by fun_prop)
    simpa [coordSet, Set.inter_def] using hdisk.inter (hyneg.inter hboundary)
  have chart_image_open (p d : EuclideanSpace ℝ (Fin 2)) (hd : d ≠ 0)
      (S : Set (EuclideanSpace ℝ (Fin 2))) (hS : IsOpen S) :
      IsOpen ((fun z : EuclideanSpace ℝ (Fin 2) =>
        p + z 0 • d + z 1 • PlanarRot90 d) '' S) := by
    let chart : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 2) :=
      fun z => p + z 0 • d + z 1 • PlanarRot90 d
    let invCoord : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 2) :=
      fun q => WithLp.toLp 2 (fun i : Fin 2 =>
        if i = 0 then inner ℝ (q - p) d / (‖d‖ ^ 2)
        else inner ℝ (q - p) (PlanarRot90 d) / (‖d‖ ^ 2))
    have hinv_cont : Continuous invCoord := by
      have hplain : Continuous fun q : EuclideanSpace ℝ (Fin 2) =>
          (fun i : Fin 2 =>
            if i = 0 then inner ℝ (q - p) d / (‖d‖ ^ 2)
            else inner ℝ (q - p) (PlanarRot90 d) / (‖d‖ ^ 2)) := by
        apply continuous_pi
        intro i
        by_cases hi : i = 0
        · simp [hi]
          fun_prop
        · simp [hi]
          fun_prop
      exact (PiLp.continuous_toLp (p := (2 : ENNReal))
        (β := fun _ : Fin 2 => ℝ)).comp hplain
    have hleft_inv :
        ∀ z : EuclideanSpace ℝ (Fin 2), invCoord (chart z) = z := by
      intro z
      have hrepz :
          chart z - p = z 0 • d + z 1 • PlanarRot90 d := by
        dsimp [chart]
        abel
      have hcoeff :=
        PlanarRot90CoefficientUniqueness (d := d) (v := chart z - p)
          hd hrepz
      apply PiLp.ext
      intro i
      fin_cases i
      · simpa [invCoord] using hcoeff.1.symm
      · simpa [invCoord] using hcoeff.2.symm
    have hright_inv :
        ∀ q : EuclideanSpace ℝ (Fin 2), chart (invCoord q) = q := by
      intro q
      have hdecomp :
          q - p = (invCoord q) 0 • d + (invCoord q) 1 • PlanarRot90 d := by
        simpa [invCoord] using PlanarRot90Decomposition d (q - p) hd
      calc
        chart (invCoord q) =
            p + ((invCoord q) 0 • d + (invCoord q) 1 • PlanarRot90 d) := by
          dsimp [chart]
          abel
        _ = p + (q - p) := by rw [← hdecomp]
        _ = q := by abel
    have himage_eq_preimage (T : Set (EuclideanSpace ℝ (Fin 2))) :
        chart '' T = invCoord ⁻¹' T := by
      ext q
      constructor
      · rintro ⟨z, hz, rfl⟩
        simpa [hleft_inv z] using hz
      · intro hq
        exact ⟨invCoord q, hq, hright_inv q⟩
    change IsOpen (chart '' S)
    rw [himage_eq_preimage S]
    exact hS.preimage hinv_cont
  have hsector_open : IsOpen (baseChart '' coordSet) := by
    simpa [baseChart] using chart_image_open p base hbase coordSet hcoord_open
  let K0 : ℝ := if c ≤ 0 then 1 else s / (2 * c)
  have hK0_pos : 0 < K0 := by
    dsimp [K0]
    by_cases hc : c ≤ 0
    · simp [hc]
    · have hcpos : 0 < c := lt_of_not_ge hc
      simp [hc, div_pos hs (mul_pos two_pos hcpos)]
  have haperture_base :
      ∀ {x y : ℝ}, 0 < x → -K0 * x < y → y < 0 → 0 < c * y + s * x := by
    intro x y hx hlow hy
    dsimp [K0] at hlow ⊢
    by_cases hc : c ≤ 0
    · have hcy_nonneg : 0 ≤ c * y := mul_nonneg_of_nonpos_of_nonpos hc (le_of_lt hy)
      have hsx_pos : 0 < s * x := mul_pos hs hx
      nlinarith
    · have hcpos : 0 < c := lt_of_not_ge hc
      simp only [gt_iff_lt] at hlow
      have hmul := mul_lt_mul_of_pos_left hlow hcpos
      have hcK : c * (s / (2 * c)) = s / 2 := by
        field_simp [ne_of_gt hcpos]
      nlinarith [hmul, mul_pos hs hx]
  have haperture_other :
      ∀ {u v : ℝ}, 0 < u → 0 < v → v < K0 * u → -u * s + v * c < 0 := by
    intro u v hu hv hupper
    dsimp [K0] at hupper ⊢
    by_cases hc : c ≤ 0
    · have hvc_nonpos : v * c ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (le_of_lt hv) hc
      have hus_pos : 0 < u * s := mul_pos hu hs
      nlinarith
    · have hcpos : 0 < c := lt_of_not_ge hc
      simp only [neg_mul, neg_add_lt_iff_lt_add, add_zero, gt_iff_lt] at hupper
      have hmul := mul_lt_mul_of_pos_left hupper hcpos
      have hcK : c * (s / (2 * c)) = s / 2 := by
        field_simp [ne_of_gt hcpos]
      nlinarith [hmul, mul_pos hu hs]
  have hcoord_conv : Convex ℝ coordSet := by
    have hdisk_conv :
        Convex ℝ {z : EuclideanSpace ℝ (Fin 2) |
          z 0 ^ 2 + z 1 ^ 2 < (rho / ‖base‖) ^ 2} := by
      simpa [hdisk_eq] using
        convex_ball (0 : EuclideanSpace ℝ (Fin 2)) (rho / ‖base‖)
    have hyneg_conv :
        Convex ℝ {z : EuclideanSpace ℝ (Fin 2) | z 1 < 0} := by
      refine convex_halfSpace_lt ?_ 0
      exact IsLinearMap.mk (by intro x y; simp) (by intro a x; simp)
    have hboundary_conv :
        Convex ℝ {z : EuclideanSpace ℝ (Fin 2) | 0 < c * z 1 + s * z 0} := by
      refine convex_halfSpace_gt ?_ 0
      refine IsLinearMap.mk ?_ ?_
      · intro x y
        simp
        ring
      · intro a x
        simp
        ring
    simpa [coordSet, Set.inter_def] using hdisk_conv.inter (hyneg_conv.inter hboundary_conv)
  have hcoord_nonempty : coordSet.Nonempty := by
    let m : ℝ := K0 / 2
    have hm_pos : 0 < m := by dsimp [m]; linarith
    have hden_pos : 0 < 2 * (1 + m) := by nlinarith
    let eps : ℝ := (rho / ‖base‖) / (2 * (1 + m))
    have heps_pos : 0 < eps := div_pos hR_pos hden_pos
    let z : EuclideanSpace ℝ (Fin 2) :=
      WithLp.toLp 2 (fun i : Fin 2 => if i = 0 then eps else -m * eps)
    refine ⟨z, ?_⟩
    have hrad : eps ^ 2 + (m * eps) ^ 2 < (rho / ‖base‖) ^ 2 := by
      have hden_ne : 2 * (1 + m) ≠ 0 := ne_of_gt hden_pos
      dsimp [eps]
      field_simp [hden_ne]
      nlinarith [sq_nonneg m, mul_pos hR_pos hR_pos]
    have hslope : 0 < s - c * m := by
      dsimp [m, K0]
      by_cases hc : c ≤ 0
      · simp [hc]
        nlinarith [hs, hc]
      · have hcpos : 0 < c := lt_of_not_ge hc
        simp [hc]
        field_simp [ne_of_gt hcpos]
        nlinarith [hs]
    refine ⟨?_, ?_, ?_⟩
    · simpa [z] using hrad
    · simp [z]
      nlinarith [hm_pos, heps_pos]
    · simp only [Fin.isValue]
      have hprod : 0 < eps * (s - c * m) := mul_pos heps_pos hslope
      nlinarith
  have hchart_cont : Continuous baseChart := by
    dsimp [baseChart]
    fun_prop
  have hsector_conn : IsConnected (baseChart '' coordSet) :=
    (hcoord_conv.isConnected hcoord_nonempty).image baseChart hchart_cont.continuousOn
  have hrot_other : PlanarRot90 other = s • base + c • PlanarRot90 base := by
    rw [hother_eq]
    simpa [sub_eq_add_neg] using PlanarRot90LinearCombination base c (-s)
  have hnorm_combo (x y : ℝ) :
      ‖x • base + y • PlanarRot90 base‖ ^ 2 =
        (x ^ 2 + y ^ 2) * ‖base‖ ^ 2 := by
    have horth : inner ℝ (x • base) (y • PlanarRot90 base) = 0 := by
      rw [inner_smul_left, inner_smul_right, PlanarRot90Orthogonal]
      ring
    have horth' : inner ℝ (y • PlanarRot90 base) (x • base) = 0 := by
      rw [real_inner_comm, horth]
    rw [← real_inner_self_eq_norm_sq]
    rw [inner_add_left, inner_add_right, inner_add_right, horth, horth']
    rw [real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq]
    rw [norm_smul, norm_smul, PlanarRot90Norm]
    rw [Real.norm_eq_abs, Real.norm_eq_abs]
    nlinarith [sq_abs x, sq_abs y]
  have hother_norm_sq : ‖other‖ ^ 2 = (c ^ 2 + s ^ 2) * ‖base‖ ^ 2 := by
    calc
      ‖other‖ ^ 2 = ‖c • base + (-s) • PlanarRot90 base‖ ^ 2 := by
        rw [hother_eq]
        simp [sub_eq_add_neg, neg_smul]
      _ = (c ^ 2 + (-s) ^ 2) * ‖base‖ ^ 2 := hnorm_combo c (-s)
      _ = (c ^ 2 + s ^ 2) * ‖base‖ ^ 2 := by ring
  have hcs_pos : 0 < c ^ 2 + s ^ 2 := by nlinarith [sq_nonneg c, sq_pos_of_pos hs]
  have hsmall_radius :
      (rho / 2 / ‖base‖) ^ 2 < (rho / ‖base‖) ^ 2 := by
    have hhalf_pos : 0 < rho / 2 := by linarith
    have hhalf_lt : rho / 2 < rho := by linarith
    have hdiv_lt : rho / 2 / ‖base‖ < rho / ‖base‖ :=
      div_lt_div_of_pos_right hhalf_lt hbase_norm_pos
    exact (sq_lt_sq₀ (le_of_lt (div_pos hhalf_pos hbase_norm_pos))
      (le_of_lt hR_pos)).mpr hdiv_lt
  refine ⟨?_, ?_, ?_⟩
  · simpa [baseChart, coordSet] using hsector_open
  · simpa [baseChart, coordSet] using hsector_conn
  · refine ⟨rho / 2, K0, by linarith, hK0_pos, ?_, ?_⟩
    · intro q hq
      rcases hq with ⟨z, hz, rfl⟩
      rcases hz with ⟨hzx, hzrad, hzy_low, hzy_neg⟩
      refine ⟨z, ?_, rfl⟩
      refine ⟨?_, hzy_neg, ?_⟩
      · exact lt_trans hzrad hsmall_radius
      · exact haperture_base hzx hzy_low hzy_neg
    · intro q hq
      rcases hq with ⟨z, hz, rfl⟩
      rcases hz with ⟨hzu, hzrad, hzvpos, hzvupper⟩
      let w : EuclideanSpace ℝ (Fin 2) := WithLp.toLp 2 (fun i : Fin 2 =>
        if i = 0 then z 0 * c + z 1 * s else -z 0 * s + z 1 * c)
      refine ⟨w, ?_, ?_⟩
      · refine ⟨?_, ?_, ?_⟩
        · have hw_sq :
              w 0 ^ 2 + w 1 ^ 2 = (z 0 ^ 2 + z 1 ^ 2) * (c ^ 2 + s ^ 2) := by
            simp [w]
            ring
          have hscale_eq :
              (rho / 2 / ‖other‖) ^ 2 * (c ^ 2 + s ^ 2) =
                (rho / 2 / ‖base‖) ^ 2 := by
            have hno_ne : ‖other‖ ≠ 0 := ne_of_gt hother_norm_pos
            have hnb_ne : ‖base‖ ≠ 0 := ne_of_gt hbase_norm_pos
            have hcs_ne : c ^ 2 + s ^ 2 ≠ 0 := ne_of_gt hcs_pos
            field_simp [hno_ne, hnb_ne, hcs_ne] at hother_norm_sq ⊢
            nlinarith
          have hscaled :
              (z 0 ^ 2 + z 1 ^ 2) * (c ^ 2 + s ^ 2) <
                (rho / 2 / ‖base‖) ^ 2 := by
            have hmul := mul_lt_mul_of_pos_right hzrad hcs_pos
            simpa [hscale_eq] using hmul
          rw [hw_sq]
          exact lt_trans hscaled hsmall_radius
        · simp [w]
          have hneg := haperture_other hzu hzvpos hzvupper
          nlinarith
        · simp [w]
          have hprod : 0 < z 1 * (c ^ 2 + s ^ 2) := mul_pos hzvpos hcs_pos
          nlinarith
      · apply PiLp.ext
        intro k
        fin_cases k <;>
          simp [w, hother_eq, PlanarRot90] <;>
          ring
