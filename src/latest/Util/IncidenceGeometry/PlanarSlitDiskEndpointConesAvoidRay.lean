import Util.IncidenceGeometry.PlanarRot90CoefficientUniqueness
import Util.IncidenceGeometry.PlanarRot90Decomposition
import Util.IncidenceGeometry.PlanarRot90Norm
import Util.IncidenceGeometry.PlanarRot90Orthogonal

open Classical
noncomputable section

lemma PlanarSlitDiskEndpointConesAvoidRay
    (p base : EuclideanSpace ℝ (Fin 2)) (rho : ℝ)
    (hrho : 0 < rho) (hbase : base ≠ 0) :
    let ray : Set (EuclideanSpace ℝ (Fin 2)) :=
      {q | ∃ t : ℝ, 0 < t ∧ q = p + t • base}
    let slit : Set (EuclideanSpace ℝ (Fin 2)) :=
      Metric.ball p rho \ (ray ∪ ({p} : Set (EuclideanSpace ℝ (Fin 2))))
    let chart : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 2) :=
      fun z => p + z 0 • base + z 1 • PlanarRot90 base
    IsOpen slit ∧ IsConnected slit ∧
      ∃ r K : ℝ, 0 < r ∧ 0 < K ∧
        chart ''
            {z | 0 < z 0 ∧ z 0 ^ 2 + z 1 ^ 2 < (r / ‖base‖) ^ 2 ∧
              -K * z 0 < z 1 ∧ z 1 < 0} ⊆ slit ∧
          chart ''
            {z | 0 < z 0 ∧ z 0 ^ 2 + z 1 ^ 2 < (r / ‖base‖) ^ 2 ∧
              0 < z 1 ∧ z 1 < K * z 0} ⊆ slit := by
  dsimp only
  let ray : Set (EuclideanSpace ℝ (Fin 2)) :=
    {q | ∃ t : ℝ, 0 < t ∧ q = p + t • base}
  let slit : Set (EuclideanSpace ℝ (Fin 2)) :=
    Metric.ball p rho \ (ray ∪ ({p} : Set (EuclideanSpace ℝ (Fin 2))))
  let chart : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 2) :=
    fun z => p + z 0 • base + z 1 • PlanarRot90 base
  let invCoord : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 2) :=
    fun q => WithLp.toLp 2 (fun i : Fin 2 =>
      if i = 0 then inner ℝ (q - p) base / (‖base‖ ^ 2)
      else inner ℝ (q - p) (PlanarRot90 base) / (‖base‖ ^ 2))
  let R : ℝ := rho / ‖base‖
  let coordSlit : Set (EuclideanSpace ℝ (Fin 2)) :=
    {z | z 0 ^ 2 + z 1 ^ 2 < R ^ 2 ∧ (z 1 ≠ 0 ∨ z 0 < 0)}
  change IsOpen slit ∧ IsConnected slit ∧
      ∃ r K : ℝ, 0 < r ∧ 0 < K ∧
        chart ''
            {z | 0 < z 0 ∧ z 0 ^ 2 + z 1 ^ 2 < (r / ‖base‖) ^ 2 ∧
              -K * z 0 < z 1 ∧ z 1 < 0} ⊆ slit ∧
          chart ''
            {z | 0 < z 0 ∧ z 0 ^ 2 + z 1 ^ 2 < (r / ‖base‖) ^ 2 ∧
              0 < z 1 ∧ z 1 < K * z 0} ⊆ slit
  have hbase_norm_pos : 0 < ‖base‖ := norm_pos_iff.mpr hbase
  have hR_pos : 0 < R := div_pos hrho hbase_norm_pos
  have hinv_cont : Continuous invCoord := by
    have hplain : Continuous fun q : EuclideanSpace ℝ (Fin 2) =>
        (fun i : Fin 2 =>
          if i = 0 then inner ℝ (q - p) base / (‖base‖ ^ 2)
          else inner ℝ (q - p) (PlanarRot90 base) / (‖base‖ ^ 2)) := by
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
        chart z - p = z 0 • base + z 1 • PlanarRot90 base := by
      dsimp [chart]
      abel
    have hcoeff :=
      PlanarRot90CoefficientUniqueness (d := base) (v := chart z - p)
        hbase hrepz
    apply PiLp.ext
    intro i
    fin_cases i
    · simpa [invCoord] using hcoeff.1.symm
    · simpa [invCoord] using hcoeff.2.symm
  have hright_inv :
      ∀ q : EuclideanSpace ℝ (Fin 2), chart (invCoord q) = q := by
    intro q
    have hdecomp :
        q - p = (invCoord q) 0 • base + (invCoord q) 1 • PlanarRot90 base := by
      simpa [invCoord] using PlanarRot90Decomposition base (q - p) hbase
    calc
      chart (invCoord q) =
          p + ((invCoord q) 0 • base + (invCoord q) 1 • PlanarRot90 base) := by
        dsimp [chart]
        abel
      _ = p + (q - p) := by rw [← hdecomp]
      _ = q := by abel
  have hcoord_norm_sq (z : EuclideanSpace ℝ (Fin 2)) :
      z 0 ^ 2 + z 1 ^ 2 = ‖z‖ ^ 2 := by
    rw [← real_inner_self_eq_norm_sq, PiLp.inner_apply]
    simp
  have hdisk_eq :
      {z : EuclideanSpace ℝ (Fin 2) | z 0 ^ 2 + z 1 ^ 2 < R ^ 2} =
        Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) R := by
    ext z
    rw [Set.mem_setOf_eq, Metric.mem_ball]
    simp [hcoord_norm_sq z, (sq_lt_sq₀ (norm_nonneg z) (le_of_lt hR_pos))]
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
  have hchart_norm_sq (z : EuclideanSpace ℝ (Fin 2)) :
      ‖chart z - p‖ ^ 2 = (z 0 ^ 2 + z 1 ^ 2) * ‖base‖ ^ 2 := by
    have hrepz :
        chart z - p = z 0 • base + z 1 • PlanarRot90 base := by
      dsimp [chart]
      abel
    rw [hrepz, hnorm_combo]
  have hchart_mem_ball_iff (z : EuclideanSpace ℝ (Fin 2)) :
      chart z ∈ Metric.ball p rho ↔ z 0 ^ 2 + z 1 ^ 2 < R ^ 2 := by
    rw [Metric.mem_ball, dist_eq_norm]
    constructor
    · intro hdist
      have hdist_sq : ‖chart z - p‖ ^ 2 < rho ^ 2 :=
        (sq_lt_sq₀ (norm_nonneg _) (le_of_lt hrho)).mpr hdist
      have hbase_sq_pos : 0 < ‖base‖ ^ 2 := sq_pos_of_pos hbase_norm_pos
      have hcoord_eq :
          z 0 ^ 2 + z 1 ^ 2 = ‖chart z - p‖ ^ 2 / ‖base‖ ^ 2 := by
        have hnorm := hchart_norm_sq z
        field_simp [ne_of_gt hbase_sq_pos]
        nlinarith
      have hR_sq : R ^ 2 = rho ^ 2 / ‖base‖ ^ 2 := by
        dsimp [R]
        field_simp [ne_of_gt hbase_norm_pos]
      rw [hcoord_eq, hR_sq]
      exact div_lt_div_of_pos_right hdist_sq hbase_sq_pos
    · intro hcoord
      have hbase_sq_pos : 0 < ‖base‖ ^ 2 := sq_pos_of_pos hbase_norm_pos
      have hR_sq_mul : R ^ 2 * ‖base‖ ^ 2 = rho ^ 2 := by
        dsimp [R]
        field_simp [ne_of_gt hbase_norm_pos]
      have hdist_sq : ‖chart z - p‖ ^ 2 < rho ^ 2 := by
        rw [hchart_norm_sq]
        have hmul := mul_lt_mul_of_pos_right hcoord hbase_sq_pos
        simpa [hR_sq_mul] using hmul
      exact (sq_lt_sq₀ (norm_nonneg _) (le_of_lt hrho)).mp hdist_sq
  have hchart_ray_iff_pos_axis (z : EuclideanSpace ℝ (Fin 2)) :
      chart z ∈ ray ↔ 0 < z 0 ∧ z 1 = 0 := by
    constructor
    · rintro ⟨t, ht, hq⟩
      have hrepz :
          chart z - p = z 0 • base + z 1 • PlanarRot90 base := by
        dsimp [chart]
        abel
      have hrept0 : chart z - p = t • base := by
        rw [hq]
        abel
      have hrept :
          chart z - p = t • base + (0 : ℝ) • PlanarRot90 base := by
        simpa using hrept0
      have hzcoeff :=
        PlanarRot90CoefficientUniqueness (d := base) (v := chart z - p)
          hbase hrepz
      have htcoeff :=
        PlanarRot90CoefficientUniqueness (d := base) (v := chart z - p)
          (a := t) (b := 0) hbase hrept
      have hx : z 0 = t := by
        rw [hzcoeff.1, htcoeff.1]
      have hy : z 1 = 0 := by
        rw [hzcoeff.2, htcoeff.2]
      exact ⟨by simpa [hx] using ht, hy⟩
    · rintro ⟨hx, hy⟩
      refine ⟨z 0, hx, ?_⟩
      dsimp [chart]
      rw [hy]
      simp
  have hchart_eq_p_iff (z : EuclideanSpace ℝ (Fin 2)) :
      chart z = p ↔ z 0 = 0 ∧ z 1 = 0 := by
    constructor
    · intro hq
      have hrepz :
          chart z - p = z 0 • base + z 1 • PlanarRot90 base := by
        dsimp [chart]
        abel
      have hrep0 :
          chart z - p = (0 : ℝ) • base + (0 : ℝ) • PlanarRot90 base := by
        rw [hq]
        simp
      have hzcoeff :=
        PlanarRot90CoefficientUniqueness (d := base) (v := chart z - p)
          hbase hrepz
      have h0coeff :=
        PlanarRot90CoefficientUniqueness (d := base) (v := chart z - p)
          (a := 0) (b := 0) hbase hrep0
      constructor
      · rw [hzcoeff.1, h0coeff.1]
      · rw [hzcoeff.2, h0coeff.2]
    · rintro ⟨hx, hy⟩
      dsimp [chart]
      rw [hx, hy]
      simp
  have hmem_slit_iff_coord (q : EuclideanSpace ℝ (Fin 2)) :
      q ∈ slit ↔ invCoord q ∈ coordSlit := by
    constructor
    · intro hq
      rcases hq with ⟨hball, hnotdel⟩
      have hcoord_ball : (invCoord q) 0 ^ 2 + (invCoord q) 1 ^ 2 < R ^ 2 := by
        have hchart_ball : chart (invCoord q) ∈ Metric.ball p rho := by
          simpa [hright_inv q] using hball
        exact (hchart_mem_ball_iff (invCoord q)).mp hchart_ball
      have haxis : (invCoord q) 1 ≠ 0 ∨ (invCoord q) 0 < 0 := by
        by_cases hy : (invCoord q) 1 = 0
        · right
          by_contra hnot_lt
          have hxnonneg : 0 ≤ (invCoord q) 0 := le_of_not_gt hnot_lt
          rcases eq_or_lt_of_le hxnonneg with hxzero | hxpos
          · have hq_eq_p : q = p := by
              have hpchart : chart (invCoord q) = p :=
                (hchart_eq_p_iff (invCoord q)).mpr ⟨hxzero.symm, hy⟩
              rw [← hright_inv q, hpchart]
            exact hnotdel (Or.inr hq_eq_p)
          · have hq_ray : q ∈ ray := by
              have hrchart : chart (invCoord q) ∈ ray :=
                (hchart_ray_iff_pos_axis (invCoord q)).mpr ⟨hxpos, hy⟩
              simpa [hright_inv q] using hrchart
            exact hnotdel (Or.inl hq_ray)
        · exact Or.inl hy
      exact ⟨hcoord_ball, haxis⟩
    · intro hz
      rcases hz with ⟨hzball, hzaxis⟩
      have hball : q ∈ Metric.ball p rho := by
        have hchart_ball : chart (invCoord q) ∈ Metric.ball p rho :=
          (hchart_mem_ball_iff (invCoord q)).mpr hzball
        simpa [hright_inv q] using hchart_ball
      have hnotdel : q ∉ ray ∪ ({p} : Set (EuclideanSpace ℝ (Fin 2))) := by
        intro hdel
        rcases hdel with hray | hp
        · have hrchart : chart (invCoord q) ∈ ray := by
            simpa [hright_inv q] using hray
          have hposaxis := (hchart_ray_iff_pos_axis (invCoord q)).mp hrchart
          rcases hzaxis with hyne | hxneg
          · exact hyne hposaxis.2
          · nlinarith [hposaxis.1, hxneg]
        · have hpchart : chart (invCoord q) = p := by
            simpa [hright_inv q] using hp
          have hzero := (hchart_eq_p_iff (invCoord q)).mp hpchart
          rcases hzaxis with hyne | hxneg
          · exact hyne hzero.2
          · nlinarith [hzero.1, hxneg]
      exact ⟨hball, hnotdel⟩
  have hslit_preimage_eq : slit = invCoord ⁻¹' coordSlit := by
    ext q
    exact hmem_slit_iff_coord q
  have hcoord_open : IsOpen coordSlit := by
    have hdisk_open :
        IsOpen {z : EuclideanSpace ℝ (Fin 2) | z 0 ^ 2 + z 1 ^ 2 < R ^ 2} := by
      exact isOpen_lt (by fun_prop) continuous_const
    have haxis_open :
        IsOpen {z : EuclideanSpace ℝ (Fin 2) | z 1 ≠ 0 ∨ z 0 < 0} := by
      have hneg : IsOpen {z : EuclideanSpace ℝ (Fin 2) | z 1 < 0} :=
        isOpen_lt (by fun_prop) continuous_const
      have hpos : IsOpen {z : EuclideanSpace ℝ (Fin 2) | 0 < z 1} :=
        isOpen_lt continuous_const (by fun_prop)
      have hxneg : IsOpen {z : EuclideanSpace ℝ (Fin 2) | z 0 < 0} :=
        isOpen_lt (by fun_prop) continuous_const
      have haxis_eq :
          {z : EuclideanSpace ℝ (Fin 2) | z 1 ≠ 0 ∨ z 0 < 0} =
            {z : EuclideanSpace ℝ (Fin 2) | z 1 < 0} ∪
              ({z : EuclideanSpace ℝ (Fin 2) | 0 < z 1} ∪
                {z : EuclideanSpace ℝ (Fin 2) | z 0 < 0}) := by
        ext z
        constructor
        · intro h
          rcases h with hyne | hx
          · rcases lt_trichotomy (z 1) 0 with hylt | hyeq | hygt
            · exact Or.inl hylt
            · exact False.elim (hyne hyeq)
            · exact Or.inr (Or.inl hygt)
          · exact Or.inr (Or.inr hx)
        · intro h
          rcases h with hylt | hrest
          · exact Or.inl (ne_of_lt hylt)
          · rcases hrest with hygt | hx
            · exact Or.inl (ne_of_gt hygt)
            · exact Or.inr hx
      simpa [haxis_eq] using hneg.union (hpos.union hxneg)
    simpa [coordSlit, Set.inter_def] using hdisk_open.inter haxis_open
  let aCoord : EuclideanSpace ℝ (Fin 2) :=
    WithLp.toLp 2 (fun i : Fin 2 => if i = 0 then -R / 2 else 0)
  have haCoord_mem : aCoord ∈ coordSlit := by
    constructor
    · simp [aCoord]
      nlinarith
    · right
      simp [aCoord]
      nlinarith
  have hcoord_star : StarConvex ℝ aCoord coordSlit := by
    intro z hz lam mu hlam hmu hsum
    rcases hz with ⟨hzdisk, hzaxis⟩
    constructor
    · have hdisk_conv :
          Convex ℝ {z : EuclideanSpace ℝ (Fin 2) | z 0 ^ 2 + z 1 ^ 2 < R ^ 2} := by
        simpa [hdisk_eq] using
          convex_ball (0 : EuclideanSpace ℝ (Fin 2)) R
      exact hdisk_conv haCoord_mem.1 hzdisk hlam hmu hsum
    · by_cases hmu_zero : mu = 0
      · right
        have hlam_one : lam = 1 := by nlinarith
        have hcoord :
            (lam • aCoord + mu • z) 0 = -R / 2 := by
          simp [aCoord, hmu_zero, hlam_one]
        rw [hcoord]
        nlinarith
      · have hmu_pos : 0 < mu := lt_of_le_of_ne hmu (Ne.symm hmu_zero)
        rcases hzaxis with hz1ne | hz0neg
        · left
          have hcoord :
              (lam • aCoord + mu • z) 1 = mu * z 1 := by
            simp [aCoord]
          rw [hcoord]
          exact mul_ne_zero (ne_of_gt hmu_pos) hz1ne
        · right
          have hcoord :
              (lam • aCoord + mu • z) 0 = lam * (-R / 2) + mu * z 0 := by
            simp [aCoord]
          rw [hcoord]
          have hleft_nonpos : lam * (-R / 2) ≤ 0 := by
            have : -R / 2 ≤ 0 := by nlinarith
            exact mul_nonpos_of_nonneg_of_nonpos hlam this
          have hright_neg : mu * z 0 < 0 :=
            mul_neg_of_pos_of_neg hmu_pos hz0neg
          nlinarith
  have hcoord_conn : IsConnected coordSlit :=
    (hcoord_star.isPathConnected haCoord_mem).isConnected
  have hchart_cont : Continuous chart := by
    dsimp [chart]
    fun_prop
  have hslit_image_eq : chart '' coordSlit = slit := by
    ext q
    constructor
    · rintro ⟨z, hz, rfl⟩
      exact (hmem_slit_iff_coord (chart z)).mpr (by simpa [hleft_inv z] using hz)
    · intro hq
      refine ⟨invCoord q, (hmem_slit_iff_coord q).mp hq, hright_inv q⟩
  have hslit_open : IsOpen slit := by
    rw [hslit_preimage_eq]
    exact hcoord_open.preimage hinv_cont
  have hslit_conn : IsConnected slit := by
    rw [← hslit_image_eq]
    exact hcoord_conn.image chart hchart_cont.continuousOn
  have hsmall_radius : (rho / 2 / ‖base‖) ^ 2 < R ^ 2 := by
    have hhalf_pos : 0 < rho / 2 := by linarith
    have hhalf_lt : rho / 2 < rho := by linarith
    have hdiv_lt : rho / 2 / ‖base‖ < R := by
      dsimp [R]
      exact div_lt_div_of_pos_right hhalf_lt hbase_norm_pos
    exact (sq_lt_sq₀ (le_of_lt (div_pos hhalf_pos hbase_norm_pos))
      (le_of_lt hR_pos)).mpr hdiv_lt
  refine ⟨hslit_open, hslit_conn, ?_⟩
  refine ⟨rho / 2, 1, by linarith, by norm_num, ?_, ?_⟩
  · intro q hq
    rcases hq with ⟨z, hz, rfl⟩
    rcases hz with ⟨hzx, hzrad, hzy_low, hzy_neg⟩
    apply (hmem_slit_iff_coord (chart z)).mpr
    have hzcoord : z ∈ coordSlit := by
      exact ⟨lt_trans hzrad hsmall_radius, Or.inl (ne_of_lt hzy_neg)⟩
    simpa [hleft_inv z] using hzcoord
  · intro q hq
    rcases hq with ⟨z, hz, rfl⟩
    rcases hz with ⟨hzx, hzrad, hzy_pos, hzy_upper⟩
    apply (hmem_slit_iff_coord (chart z)).mpr
    have hzcoord : z ∈ coordSlit := by
      exact ⟨lt_trans hzrad hsmall_radius, Or.inl (ne_of_gt hzy_pos)⟩
    simpa [hleft_inv z] using hzcoord
