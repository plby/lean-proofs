import Util.IncidenceGeometry.PlanarClockwiseTwoRayEndpointConesInSector
import Util.IncidenceGeometry.PlanarRot90LinearCombination
import Util.IncidenceGeometry.PlanarRot90Norm
import Util.IncidenceGeometry.PlanarRot90Orthogonal

open Classical
noncomputable section

private lemma swept_chart_image_open
    (p d : EuclideanSpace ℝ (Fin 2)) (hd : d ≠ 0)
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
  have hleft_inv : ∀ z : EuclideanSpace ℝ (Fin 2), invCoord (chart z) = z := by
    intro z
    have hrepz : chart z - p = z 0 • d + z 1 • PlanarRot90 d := by
      dsimp [chart]
      abel
    have hcoeff :=
      PlanarRot90CoefficientUniqueness (d := d) (v := chart z - p) hd hrepz
    apply PiLp.ext
    intro i
    fin_cases i
    · simpa [invCoord] using hcoeff.1.symm
    · simpa [invCoord] using hcoeff.2.symm
  have hright_inv : ∀ q : EuclideanSpace ℝ (Fin 2), chart (invCoord q) = q := by
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

private lemma swept_chart_image_connected
    (p d : EuclideanSpace ℝ (Fin 2))
    (S : Set (EuclideanSpace ℝ (Fin 2))) (hS : IsConnected S) :
    IsConnected ((fun z : EuclideanSpace ℝ (Fin 2) =>
      p + z 0 • d + z 1 • PlanarRot90 d) '' S) := by
  have hchart_cont : Continuous fun z : EuclideanSpace ℝ (Fin 2) =>
      p + z 0 • d + z 1 • PlanarRot90 d := by
    fun_prop
  exact hS.image _ hchart_cont.continuousOn

private lemma swept_norm_combo
    (base : EuclideanSpace ℝ (Fin 2)) (x y : ℝ) :
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

private lemma swept_other_norm_sq
    (base other : EuclideanSpace ℝ (Fin 2)) (c s : ℝ)
    (hother_eq : other = c • base - s • PlanarRot90 base) :
    ‖other‖ ^ 2 = (c ^ 2 + s ^ 2) * ‖base‖ ^ 2 := by
  calc
    ‖other‖ ^ 2 = ‖c • base + (-s) • PlanarRot90 base‖ ^ 2 := by
      rw [hother_eq]
      simp [sub_eq_add_neg, neg_smul]
    _ = (c ^ 2 + (-s) ^ 2) * ‖base‖ ^ 2 := swept_norm_combo base c (-s)
    _ = (c ^ 2 + s ^ 2) * ‖base‖ ^ 2 := by ring

private lemma swept_disk_eq_ball (R : ℝ) (hR : 0 < R) :
    {z : EuclideanSpace ℝ (Fin 2) | z 0 ^ 2 + z 1 ^ 2 < R ^ 2} =
      Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) R := by
  have hnormsq_coord (z : EuclideanSpace ℝ (Fin 2)) :
      z 0 ^ 2 + z 1 ^ 2 = ‖z‖ ^ 2 := by
    rw [← real_inner_self_eq_norm_sq, PiLp.inner_apply]
    simp
  ext z
  rw [Set.mem_ofPred_eq, Metric.mem_ball]
  simp [hnormsq_coord z, (sq_lt_sq₀ (norm_nonneg z) hR.le)]

private lemma swept_small_radius
    (rho bnorm : ℝ) (hrho : 0 < rho) (hbnorm : 0 < bnorm) :
    (rho / 2 / bnorm) ^ 2 < (rho / bnorm) ^ 2 := by
  have hhalf_pos : 0 < rho / 2 := by linarith
  have hhalf_lt : rho / 2 < rho := by linarith
  have hdiv_lt : rho / 2 / bnorm < rho / bnorm :=
    div_lt_div_of_pos_right hhalf_lt hbnorm
  exact (sq_lt_sq₀ (div_pos hhalf_pos hbnorm).le (div_pos hrho hbnorm).le).mpr hdiv_lt

private def swept_coordinates (c s : ℝ) (z : EuclideanSpace ℝ (Fin 2)) :
    EuclideanSpace ℝ (Fin 2) :=
  WithLp.toLp 2 (fun i : Fin 2 =>
    if i = 0 then z 0 * c + z 1 * s else -z 0 * s + z 1 * c)

private lemma swept_coordinates_sq (c s : ℝ) (z : EuclideanSpace ℝ (Fin 2)) :
    (swept_coordinates c s z) 0 ^ 2 + (swept_coordinates c s z) 1 ^ 2 =
      (z 0 ^ 2 + z 1 ^ 2) * (c ^ 2 + s ^ 2) := by
  simp [swept_coordinates]
  ring

private lemma swept_coordinates_linear (c s : ℝ) (z : EuclideanSpace ℝ (Fin 2)) :
    c * (swept_coordinates c s z) 1 + s * (swept_coordinates c s z) 0 =
      z 1 * (c ^ 2 + s ^ 2) := by
  simp [swept_coordinates]
  ring

private lemma swept_coordinates_chart
    (p base other : EuclideanSpace ℝ (Fin 2)) (c s : ℝ)
    (hother_eq : other = c • base - s • PlanarRot90 base)
    (z : EuclideanSpace ℝ (Fin 2)) :
    p + (swept_coordinates c s z) 0 • base +
          (swept_coordinates c s z) 1 • PlanarRot90 base =
      p + z 0 • other + z 1 • PlanarRot90 other := by
  apply PiLp.ext
  intro k
  fin_cases k <;>
    simp [swept_coordinates, hother_eq, PlanarRot90] <;>
    ring

private lemma swept_coordinates_radius
    (rho bnorm onorm c s : ℝ)
    (hbnorm : 0 < bnorm) (honorm : 0 < onorm)
    (hcs : 0 < c ^ 2 + s ^ 2)
    (hnorm : onorm ^ 2 = (c ^ 2 + s ^ 2) * bnorm ^ 2)
    (z : EuclideanSpace ℝ (Fin 2))
    (hz : z 0 ^ 2 + z 1 ^ 2 < (rho / 2 / onorm) ^ 2) :
    (swept_coordinates c s z) 0 ^ 2 + (swept_coordinates c s z) 1 ^ 2 <
      (rho / 2 / bnorm) ^ 2 := by
  have hscale_eq :
      (rho / 2 / onorm) ^ 2 * (c ^ 2 + s ^ 2) =
        (rho / 2 / bnorm) ^ 2 := by
    have hno_ne : onorm ≠ 0 := ne_of_gt honorm
    have hnb_ne : bnorm ≠ 0 := ne_of_gt hbnorm
    have hcs_ne : c ^ 2 + s ^ 2 ≠ 0 := ne_of_gt hcs
    field_simp [hno_ne, hnb_ne, hcs_ne] at hnorm ⊢
    nlinarith
  rw [swept_coordinates_sq]
  have hmul := mul_lt_mul_of_pos_right hz hcs
  simpa [hscale_eq] using hmul

private lemma swept_negative_coord_open
    (R c s : ℝ) :
    IsOpen {z : EuclideanSpace ℝ (Fin 2) |
      z 0 ^ 2 + z 1 ^ 2 < R ^ 2 ∧
        (z 1 < 0 ∨ 0 < c * z 1 + s * z 0)} := by
  have hdisk_open :
      IsOpen {z : EuclideanSpace ℝ (Fin 2) | z 0 ^ 2 + z 1 ^ 2 < R ^ 2} :=
    isOpen_lt (by fun_prop) continuous_const
  have hyneg_open : IsOpen {z : EuclideanSpace ℝ (Fin 2) | z 1 < 0} :=
    isOpen_lt (by fun_prop) continuous_const
  have hboundary_open :
      IsOpen {z : EuclideanSpace ℝ (Fin 2) | 0 < c * z 1 + s * z 0} :=
    isOpen_lt continuous_const (by fun_prop)
  have heq :
      {z : EuclideanSpace ℝ (Fin 2) |
        z 0 ^ 2 + z 1 ^ 2 < R ^ 2 ∧
          (z 1 < 0 ∨ 0 < c * z 1 + s * z 0)} =
        {z | z 0 ^ 2 + z 1 ^ 2 < R ^ 2} ∩
          ({z | z 1 < 0} ∪ {z | 0 < c * z 1 + s * z 0}) := by
    ext z
    simp only [Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_union]
  rw [heq]
  exact hdisk_open.inter (hyneg_open.union hboundary_open)

private lemma swept_negative_coord_connected
    (R c s : ℝ) (hR : 0 < R) (hsneg : s < 0) :
    IsConnected {z : EuclideanSpace ℝ (Fin 2) |
      z 0 ^ 2 + z 1 ^ 2 < R ^ 2 ∧
        (z 1 < 0 ∨ 0 < c * z 1 + s * z 0)} := by
  let disk : Set (EuclideanSpace ℝ (Fin 2)) :=
    {z | z 0 ^ 2 + z 1 ^ 2 < R ^ 2}
  let lower : Set (EuclideanSpace ℝ (Fin 2)) := {z | z ∈ disk ∧ z 1 < 0}
  let cap : Set (EuclideanSpace ℝ (Fin 2)) :=
    {z | z ∈ disk ∧ 0 < c * z 1 + s * z 0}
  have hdisk_conv : Convex ℝ disk := by
    simpa [disk, swept_disk_eq_ball R hR] using
      convex_ball (0 : EuclideanSpace ℝ (Fin 2)) R
  have hyneg_conv : Convex ℝ {z : EuclideanSpace ℝ (Fin 2) | z 1 < 0} := by
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
  have hlower_conv : Convex ℝ lower := by
    simpa [lower, Set.inter_def] using hdisk_conv.inter hyneg_conv
  have hcap_conv : Convex ℝ cap := by
    simpa [cap, Set.inter_def] using hdisk_conv.inter hboundary_conv
  have hneg_s_pos : 0 < -s := neg_pos.mpr hsneg
  let M : ℝ := (|c| + 1) / (-s) + 1
  have hM_pos : 0 < M := by
    have hnum_pos : 0 < |c| + 1 :=
      add_pos_of_nonneg_of_pos (abs_nonneg c) zero_lt_one
    have hdiv_pos : 0 < (|c| + 1) / (-s) := div_pos hnum_pos hneg_s_pos
    dsimp [M]
    linarith
  have hMlarge : |c| + 1 < (-s) * M := by
    have hM_eq : (-s) * M = |c| + 1 + (-s) := by
      dsimp [M]
      rw [mul_add, mul_one, mul_comm (-s) ((|c| + 1) / (-s))]
      rw [div_mul_cancel₀ (|c| + 1) (ne_of_gt hneg_s_pos)]
    rw [hM_eq]
    linarith
  have hden_pos : 0 < 2 * (M + 1) := by nlinarith
  let eps : ℝ := R / (2 * (M + 1))
  have heps_pos : 0 < eps := div_pos hR hden_pos
  let zI : EuclideanSpace ℝ (Fin 2) :=
    WithLp.toLp 2 (fun i : Fin 2 => if i = 0 then -M * eps else -eps)
  have hzI_disk : zI ∈ disk := by
    have hden_ne : 2 * (M + 1) ≠ 0 := ne_of_gt hden_pos
    dsimp [disk, zI, eps]
    simp
    field_simp [hden_ne]
    nlinarith [sq_nonneg M, mul_pos hR hR, hM_pos]
  have hzI_yneg : zI 1 < 0 := by
    dsimp [zI]
    simp [heps_pos]
  have hzI_boundary : 0 < c * zI 1 + s * zI 0 := by
    have hlinear : 0 < -c - s * M := by
      have hc_le_abs : c ≤ |c| := le_abs_self c
      nlinarith [hMlarge, hc_le_abs]
    have hprod : 0 < eps * (-c - s * M) := mul_pos heps_pos hlinear
    dsimp [zI]
    simp
    nlinarith
  have hinter : (lower ∩ cap).Nonempty :=
    ⟨zI, ⟨⟨hzI_disk, hzI_yneg⟩, ⟨hzI_disk, hzI_boundary⟩⟩⟩
  have hlower_conn : IsConnected lower :=
    hlower_conv.isConnected ⟨zI, hzI_disk, hzI_yneg⟩
  have hcap_conn : IsConnected cap :=
    hcap_conv.isConnected ⟨zI, hzI_disk, hzI_boundary⟩
  have hunion : IsConnected (lower ∪ cap) :=
    IsConnected.union hinter hlower_conn hcap_conn
  have heq :
      {z : EuclideanSpace ℝ (Fin 2) |
        z 0 ^ 2 + z 1 ^ 2 < R ^ 2 ∧
          (z 1 < 0 ∨ 0 < c * z 1 + s * z 0)} = lower ∪ cap := by
    ext z
    simp only [lower, cap, disk, Set.mem_setOf_eq, Set.mem_union]
    tauto
  rw [heq]
  exact hunion

private lemma swept_negative_branch
    (p base other : EuclideanSpace ℝ (Fin 2)) (rho c s : ℝ)
    (hrho : 0 < rho) (hbase : base ≠ 0) (hother : other ≠ 0)
    (hsneg : s < 0)
    (hother_eq : other = c • base - s • PlanarRot90 base) :
    let baseChart : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 2) :=
      fun z => p + z 0 • base + z 1 • PlanarRot90 base
    let otherChart : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 2) :=
      fun z => p + z 0 • other + z 1 • PlanarRot90 other
    let sector : Set (EuclideanSpace ℝ (Fin 2)) :=
      baseChart '' {z | z 0 ^ 2 + z 1 ^ 2 < (rho / ‖base‖) ^ 2 ∧
        (z 1 < 0 ∨ 0 < c * z 1 + s * z 0)}
    IsOpen sector ∧ IsConnected sector ∧
      ∃ r K : ℝ, 0 < r ∧ 0 < K ∧
        baseChart '' {z | 0 < z 0 ∧ z 0 ^ 2 + z 1 ^ 2 < (r / ‖base‖) ^ 2 ∧
          -K * z 0 < z 1 ∧ z 1 < 0} ⊆ sector ∧
        otherChart '' {z | 0 < z 0 ∧ z 0 ^ 2 + z 1 ^ 2 < (r / ‖other‖) ^ 2 ∧
          0 < z 1 ∧ z 1 < K * z 0} ⊆ sector := by
  let baseChart : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 2) :=
    fun z => p + z 0 • base + z 1 • PlanarRot90 base
  let otherChart : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 2) :=
    fun z => p + z 0 • other + z 1 • PlanarRot90 other
  let coordSet : Set (EuclideanSpace ℝ (Fin 2)) :=
    {z | z 0 ^ 2 + z 1 ^ 2 < (rho / ‖base‖) ^ 2 ∧
      (z 1 < 0 ∨ 0 < c * z 1 + s * z 0)}
  have hbpos : 0 < ‖base‖ := norm_pos_iff.mpr hbase
  have hopos : 0 < ‖other‖ := norm_pos_iff.mpr hother
  have hRpos : 0 < rho / ‖base‖ := div_pos hrho hbpos
  have hopen : IsOpen coordSet := by
    simpa [coordSet] using swept_negative_coord_open (rho / ‖base‖) c s
  have hconn : IsConnected coordSet := by
    simpa [coordSet] using swept_negative_coord_connected (rho / ‖base‖) c s hRpos hsneg
  have hsector_open : IsOpen (baseChart '' coordSet) := by
    simpa [baseChart] using swept_chart_image_open p base hbase coordSet hopen
  have hsector_conn : IsConnected (baseChart '' coordSet) := by
    simpa [baseChart] using swept_chart_image_connected p base coordSet hconn
  have hsmall := swept_small_radius rho ‖base‖ hrho hbpos
  have hcs : 0 < c ^ 2 + s ^ 2 := by
    nlinarith [sq_nonneg c, sq_pos_of_ne_zero (ne_of_lt hsneg)]
  have hnorm := swept_other_norm_sq base other c s hother_eq
  refine ⟨hsector_open, hsector_conn, rho / 2, 1, by linarith, by norm_num, ?_, ?_⟩
  · rintro q ⟨z, ⟨_hzx, hzrad, _hzlow, hzneg⟩, rfl⟩
    exact ⟨z, ⟨lt_trans hzrad hsmall, Or.inl hzneg⟩, rfl⟩
  · rintro q ⟨z, ⟨_hzu, hzrad, hzvpos, _hzvupper⟩, rfl⟩
    let w := swept_coordinates c s z
    refine ⟨w, ⟨?_, ?_⟩, ?_⟩
    · exact lt_trans
        (swept_coordinates_radius rho ‖base‖ ‖other‖ c s hbpos hopos hcs hnorm z hzrad)
        hsmall
    · by_cases hwneg : w 1 < 0
      · exact Or.inl hwneg
      · apply Or.inr
        rw [show c * w 1 + s * w 0 = z 1 * (c ^ 2 + s ^ 2) by
          simpa [w] using swept_coordinates_linear c s z]
        exact mul_pos hzvpos hcs
    · simpa [w, baseChart, otherChart] using
        swept_coordinates_chart p base other c s hother_eq z

private lemma swept_zero_coord_open_connected
    (R : ℝ) (hR : 0 < R) :
    IsOpen {z : EuclideanSpace ℝ (Fin 2) | z 0 ^ 2 + z 1 ^ 2 < R ^ 2 ∧ z 1 < 0} ∧
    IsConnected {z : EuclideanSpace ℝ (Fin 2) |
      z 0 ^ 2 + z 1 ^ 2 < R ^ 2 ∧ z 1 < 0} := by
  let disk : Set (EuclideanSpace ℝ (Fin 2)) := {z | z 0 ^ 2 + z 1 ^ 2 < R ^ 2}
  let lower : Set (EuclideanSpace ℝ (Fin 2)) := {z | z ∈ disk ∧ z 1 < 0}
  have hdisk_open : IsOpen disk := by
    dsimp [disk]
    exact isOpen_lt (by fun_prop) continuous_const
  have hyneg_open : IsOpen {z : EuclideanSpace ℝ (Fin 2) | z 1 < 0} :=
    isOpen_lt (by fun_prop) continuous_const
  have hlower_open : IsOpen lower := by
    simpa [lower, Set.inter_def] using hdisk_open.inter hyneg_open
  have hdisk_conv : Convex ℝ disk := by
    simpa [disk, swept_disk_eq_ball R hR] using
      convex_ball (0 : EuclideanSpace ℝ (Fin 2)) R
  have hyneg_conv : Convex ℝ {z : EuclideanSpace ℝ (Fin 2) | z 1 < 0} := by
    refine convex_halfSpace_lt ?_ 0
    exact IsLinearMap.mk (by intro x y; simp) (by intro a x; simp)
  have hlower_conv : Convex ℝ lower := by
    simpa [lower, Set.inter_def] using hdisk_conv.inter hyneg_conv
  let zI : EuclideanSpace ℝ (Fin 2) :=
    WithLp.toLp 2 (fun i : Fin 2 => if i = 0 then 0 else -(R / 2))
  have hzI : zI ∈ lower := by
    refine ⟨?_, ?_⟩
    · dsimp [disk, zI]
      simp
      nlinarith
    · dsimp [zI]
      simp
      linarith
  exact ⟨by simpa [lower, disk] using hlower_open,
    by simpa [lower, disk] using hlower_conv.isConnected ⟨zI, hzI⟩⟩

private lemma swept_zero_branch
    (p base other : EuclideanSpace ℝ (Fin 2)) (rho c s : ℝ)
    (hrho : 0 < rho) (hbase : base ≠ 0) (hother : other ≠ 0)
    (hszero : s = 0) (hcneg : c < 0)
    (hother_eq : other = c • base - s • PlanarRot90 base) :
    let baseChart : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 2) :=
      fun z => p + z 0 • base + z 1 • PlanarRot90 base
    let otherChart : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 2) :=
      fun z => p + z 0 • other + z 1 • PlanarRot90 other
    let sector : Set (EuclideanSpace ℝ (Fin 2)) :=
      baseChart '' {z | z 0 ^ 2 + z 1 ^ 2 < (rho / ‖base‖) ^ 2 ∧ z 1 < 0}
    IsOpen sector ∧ IsConnected sector ∧
      ∃ r K : ℝ, 0 < r ∧ 0 < K ∧
        baseChart '' {z | 0 < z 0 ∧ z 0 ^ 2 + z 1 ^ 2 < (r / ‖base‖) ^ 2 ∧
          -K * z 0 < z 1 ∧ z 1 < 0} ⊆ sector ∧
        otherChart '' {z | 0 < z 0 ∧ z 0 ^ 2 + z 1 ^ 2 < (r / ‖other‖) ^ 2 ∧
          0 < z 1 ∧ z 1 < K * z 0} ⊆ sector := by
  let baseChart : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 2) :=
    fun z => p + z 0 • base + z 1 • PlanarRot90 base
  let otherChart : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 2) :=
    fun z => p + z 0 • other + z 1 • PlanarRot90 other
  let coordSet : Set (EuclideanSpace ℝ (Fin 2)) :=
    {z | z 0 ^ 2 + z 1 ^ 2 < (rho / ‖base‖) ^ 2 ∧ z 1 < 0}
  have hbpos : 0 < ‖base‖ := norm_pos_iff.mpr hbase
  have hopos : 0 < ‖other‖ := norm_pos_iff.mpr hother
  have hRpos : 0 < rho / ‖base‖ := div_pos hrho hbpos
  have hoc := swept_zero_coord_open_connected (rho / ‖base‖) hRpos
  have hsector_open : IsOpen (baseChart '' coordSet) := by
    apply swept_chart_image_open p base hbase
    simpa [coordSet] using hoc.1
  have hsector_conn : IsConnected (baseChart '' coordSet) := by
    apply swept_chart_image_connected p base
    simpa [coordSet] using hoc.2
  have hsmall := swept_small_radius rho ‖base‖ hrho hbpos
  have hcs : 0 < c ^ 2 + s ^ 2 := by
    nlinarith [sq_pos_of_ne_zero (ne_of_lt hcneg), sq_nonneg s]
  have hnorm := swept_other_norm_sq base other c s hother_eq
  refine ⟨hsector_open, hsector_conn, rho / 2, 1, by linarith, by norm_num, ?_, ?_⟩
  · rintro q ⟨z, ⟨_hzx, hzrad, _hzlow, hzneg⟩, rfl⟩
    exact ⟨z, ⟨lt_trans hzrad hsmall, hzneg⟩, rfl⟩
  · rintro q ⟨z, ⟨_hzu, hzrad, hzvpos, _hzvupper⟩, rfl⟩
    let w := swept_coordinates c s z
    refine ⟨w, ⟨?_, ?_⟩, ?_⟩
    · exact lt_trans
        (swept_coordinates_radius rho ‖base‖ ‖other‖ c s hbpos hopos hcs hnorm z hzrad)
        hsmall
    · have hwneg : w 1 < 0 := by
        simp [w, swept_coordinates, hszero]
        exact mul_neg_of_pos_of_neg hzvpos hcneg
      exact hwneg
    · simpa [w, baseChart, otherChart] using
        swept_coordinates_chart p base other c s hother_eq z

lemma PlanarClockwiseSweptTwoRayEndpointConesInSector
    (p base other : EuclideanSpace ℝ (Fin 2)) (rho c s : ℝ)
    (hrho : 0 < rho) (hbase : base ≠ 0) (hother : other ≠ 0)
    (hnot_pos_ray : s ≠ 0 ∨ c < 0)
    (hother_eq : other = c • base - s • PlanarRot90 base) :
    let baseChart : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 2) :=
      fun z => p + z 0 • base + z 1 • PlanarRot90 base
    let otherChart : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 2) :=
      fun z => p + z 0 • other + z 1 • PlanarRot90 other
    let sector : Set (EuclideanSpace ℝ (Fin 2)) :=
      if 0 < s then
        baseChart '' {z | z 0 ^ 2 + z 1 ^ 2 < (rho / ‖base‖) ^ 2 ∧
          z 1 < 0 ∧ 0 < c * z 1 + s * z 0}
      else if s < 0 then
        baseChart '' {z | z 0 ^ 2 + z 1 ^ 2 < (rho / ‖base‖) ^ 2 ∧
          (z 1 < 0 ∨ 0 < c * z 1 + s * z 0)}
      else
        baseChart '' {z | z 0 ^ 2 + z 1 ^ 2 < (rho / ‖base‖) ^ 2 ∧ z 1 < 0}
    IsOpen sector ∧ IsConnected sector ∧
      ∃ r K : ℝ, 0 < r ∧ 0 < K ∧
        baseChart '' {z | 0 < z 0 ∧ z 0 ^ 2 + z 1 ^ 2 < (r / ‖base‖) ^ 2 ∧
          -K * z 0 < z 1 ∧ z 1 < 0} ⊆ sector ∧
        otherChart '' {z | 0 < z 0 ∧ z 0 ^ 2 + z 1 ^ 2 < (r / ‖other‖) ^ 2 ∧
          0 < z 1 ∧ z 1 < K * z 0} ⊆ sector := by
  by_cases hspos : 0 < s
  · simpa [hspos] using
      PlanarClockwiseTwoRayEndpointConesInSector p base other rho c s
        hrho hbase hother hspos hother_eq
  · by_cases hsneg : s < 0
    · simpa [hspos, hsneg] using
        swept_negative_branch p base other rho c s hrho hbase hother hsneg hother_eq
    · have hszero : s = 0 := le_antisymm (not_lt.mp hspos) (not_lt.mp hsneg)
      have hcneg : c < 0 := by
        rcases hnot_pos_ray with hsne | hc
        · exact False.elim (hsne hszero)
        · exact hc
      simpa [hspos, hsneg] using
        swept_zero_branch p base other rho c s hrho hbase hother hszero hcneg hother_eq
