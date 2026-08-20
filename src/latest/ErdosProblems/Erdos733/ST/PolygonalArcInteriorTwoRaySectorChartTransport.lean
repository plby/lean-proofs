import Mathlib.Analysis.Convex.PathConnected
import ErdosProblems.Erdos733.ST.PolygonalArcInteriorTwoRaySectorModel
import ErdosProblems.Erdos733.ST.PolygonalArcInteriorTwoRaySectorOrientationChoice
import ErdosProblems.Erdos733.ST.PlanarRot90CoefficientUniqueness

open Set
open Classical
noncomputable section


-- [TABLET NODE: PolygonalArcInteriorTwoRaySectorChartTransport]
lemma PolygonalArcInteriorTwoRaySectorChartTransport
    (p u v : EuclideanSpace ℝ (Fin 2)) (rho : ℝ)
    (hrho : 0 < rho) (hu : u ≠ 0) (hv : v ≠ 0)
    (hnot_same : ¬ ∃ t : ℝ, 0 < t ∧ v = t • u) :
    ∃ (base other : EuclideanSpace ℝ (Fin 2)) (c s : ℝ),
      ((base = u ∧ other = v) ∨ (base = v ∧ other = u)) ∧
        other = c • base + s • PlanarRot90 base ∧
        (0 < s ∨ s = 0 ∧ c < 0) ∧
        let a : ℝ := rho / ‖base‖
        let chart : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 2) :=
          fun z => p + z 0 • base + z 1 • PlanarRot90 base
        let C : Set (EuclideanSpace ℝ (Fin 2)) :=
          Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) a
        let Gbase : Set (EuclideanSpace ℝ (Fin 2)) :=
          {z | z ∈ C ∧ z 1 = 0 ∧ 0 < z 0}
        let Gother : Set (EuclideanSpace ℝ (Fin 2)) :=
          {z | z ∈ C ∧ ∃ t : ℝ, 0 < t ∧ z 0 = t * c ∧ z 1 = t * s}
        let L : Set (EuclideanSpace ℝ (Fin 2)) :=
          {z | z ∈ C ∧ 0 < z 1 ∧ c * z 1 - s * z 0 < 0}
        let R : Set (EuclideanSpace ℝ (Fin 2)) :=
          {z | z ∈ C ∧ (z 1 < 0 ∨ 0 < c * z 1 - s * z 0)}
        0 < a ∧
          IsOpen (chart '' C) ∧ IsOpen (chart '' L) ∧ IsOpen (chart '' R) ∧
          IsConnected (chart '' L) ∧ IsConnected (chart '' R) ∧
          Disjoint (chart '' L) (chart '' R) ∧
          chart '' C = Metric.ball p rho ∧
          chart '' Gbase =
            {q | q ∈ Metric.ball p rho ∧ ∃ t : ℝ, 0 < t ∧ q = p + t • base} ∧
          chart '' Gother =
            {q | q ∈ Metric.ball p rho ∧ ∃ t : ℝ, 0 < t ∧ q = p + t • other} ∧
          Disjoint (chart '' L)
            ((chart '' Gbase) ∪ (chart '' Gother) ∪
              ({p} : Set (EuclideanSpace ℝ (Fin 2)))) ∧
          Disjoint (chart '' R)
            ((chart '' Gbase) ∪ (chart '' Gother) ∪
              ({p} : Set (EuclideanSpace ℝ (Fin 2)))) ∧
          Metric.ball p rho \
              ((chart '' Gbase) ∪ (chart '' Gother) ∪
                ({p} : Set (EuclideanSpace ℝ (Fin 2)))) =
            chart '' L ∪ chart '' R := by
-- BODY
  have transport
      (base other : EuclideanSpace ℝ (Fin 2)) (c s : ℝ) (hbase : base ≠ 0)
      (hrep : other = c • base + s • PlanarRot90 base)
      (hpos : 0 < s ∨ s = 0 ∧ c < 0) :
      let a : ℝ := rho / ‖base‖
      let chart : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 2) :=
        fun z => p + z 0 • base + z 1 • PlanarRot90 base
      let C : Set (EuclideanSpace ℝ (Fin 2)) :=
        Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) a
      let Gbase : Set (EuclideanSpace ℝ (Fin 2)) :=
        {z | z ∈ C ∧ z 1 = 0 ∧ 0 < z 0}
      let Gother : Set (EuclideanSpace ℝ (Fin 2)) :=
        {z | z ∈ C ∧ ∃ t : ℝ, 0 < t ∧ z 0 = t * c ∧ z 1 = t * s}
      let L : Set (EuclideanSpace ℝ (Fin 2)) :=
        {z | z ∈ C ∧ 0 < z 1 ∧ c * z 1 - s * z 0 < 0}
      let R : Set (EuclideanSpace ℝ (Fin 2)) :=
        {z | z ∈ C ∧ (z 1 < 0 ∨ 0 < c * z 1 - s * z 0)}
      0 < a ∧
        IsOpen (chart '' C) ∧ IsOpen (chart '' L) ∧ IsOpen (chart '' R) ∧
        IsConnected (chart '' L) ∧ IsConnected (chart '' R) ∧
        Disjoint (chart '' L) (chart '' R) ∧
        chart '' C = Metric.ball p rho ∧
        chart '' Gbase =
          {q | q ∈ Metric.ball p rho ∧ ∃ t : ℝ, 0 < t ∧ q = p + t • base} ∧
        chart '' Gother =
          {q | q ∈ Metric.ball p rho ∧ ∃ t : ℝ, 0 < t ∧ q = p + t • other} ∧
        Disjoint (chart '' L)
          ((chart '' Gbase) ∪ (chart '' Gother) ∪
            ({p} : Set (EuclideanSpace ℝ (Fin 2)))) ∧
        Disjoint (chart '' R)
          ((chart '' Gbase) ∪ (chart '' Gother) ∪
            ({p} : Set (EuclideanSpace ℝ (Fin 2)))) ∧
        Metric.ball p rho \
            ((chart '' Gbase) ∪ (chart '' Gother) ∪
              ({p} : Set (EuclideanSpace ℝ (Fin 2)))) =
          chart '' L ∪ chart '' R := by
    intro a chart C Gbase Gother L R
    have hbase_norm_pos : 0 < ‖base‖ := norm_pos_iff.mpr hbase
    have ha : 0 < a := by
      dsimp [a]
      exact div_pos hrho hbase_norm_pos
    have hscale_sq : a ^ 2 * ‖base‖ ^ 2 = rho ^ 2 := by
      dsimp [a]
      field_simp [ne_of_gt hbase_norm_pos]
    have hball_eq : Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) a =
        {z : EuclideanSpace ℝ (Fin 2) | z 0 ^ 2 + z 1 ^ 2 < a ^ 2} := by
      simpa [Fin.sum_univ_two] using
        (EuclideanSpace.ball_zero_eq (n := Fin 2) a ha.le)
    have hnorm_sq :
        ∀ z : EuclideanSpace ℝ (Fin 2),
          ‖z 0 • base + z 1 • PlanarRot90 base‖ ^ 2 =
            (z 0 ^ 2 + z 1 ^ 2) * ‖base‖ ^ 2 := by
      intro z
      have horth : inner ℝ (z 0 • base) (z 1 • PlanarRot90 base) = 0 := by
        rw [inner_smul_left, inner_smul_right, PlanarRot90Orthogonal]
        ring
      have hpyth :
          ‖z 0 • base + z 1 • PlanarRot90 base‖ ^ 2 =
            ‖z 0 • base‖ ^ 2 + ‖z 1 • PlanarRot90 base‖ ^ 2 := by
        simpa [pow_two] using norm_add_sq_eq_norm_sq_add_norm_sq_real horth
      rw [hpyth, norm_smul, norm_smul, PlanarRot90Norm]
      rw [Real.norm_eq_abs, Real.norm_eq_abs]
      rw [mul_pow, mul_pow, sq_abs, sq_abs]
      ring
    have hcoord0 : Continuous fun z : EuclideanSpace ℝ (Fin 2) => z 0 :=
      PiLp.continuous_apply (p := (2 : ENNReal)) (β := fun _ : Fin 2 => ℝ) 0
    have hcoord1 : Continuous fun z : EuclideanSpace ℝ (Fin 2) => z 1 :=
      PiLp.continuous_apply (p := (2 : ENNReal)) (β := fun _ : Fin 2 => ℝ) 1
    let cross : EuclideanSpace ℝ (Fin 2) → ℝ := fun z => c * z 1 - s * z 0
    have hcross_cont : Continuous fun z : EuclideanSpace ℝ (Fin 2) => cross z := by
      dsimp [cross]
      exact (continuous_const.mul hcoord1).sub (continuous_const.mul hcoord0)
    have hC_open : IsOpen C := by
      dsimp [C]
      exact Metric.isOpen_ball
    have hL_open : IsOpen L := by
      dsimp [L, cross]
      exact hC_open.inter ((isOpen_lt continuous_const hcoord1).inter
        (isOpen_lt hcross_cont continuous_const))
    let Rneg : Set (EuclideanSpace ℝ (Fin 2)) := {z | z ∈ C ∧ z 1 < 0}
    let Rcross : Set (EuclideanSpace ℝ (Fin 2)) := {z | z ∈ C ∧ 0 < cross z}
    have hR_eq : R = Rneg ∪ Rcross := by
      ext z
      dsimp [R, Rneg, Rcross, cross]
      constructor
      · rintro ⟨hzC, hz | hz⟩
        · exact Or.inl ⟨hzC, hz⟩
        · exact Or.inr ⟨hzC, hz⟩
      · rintro (⟨hzC, hz⟩ | ⟨hzC, hz⟩)
        · exact ⟨hzC, Or.inl hz⟩
        · exact ⟨hzC, Or.inr hz⟩
    have hRneg_open : IsOpen Rneg := by
      dsimp [Rneg]
      exact hC_open.inter (isOpen_lt hcoord1 continuous_const)
    have hRcross_open : IsOpen Rcross := by
      dsimp [Rcross]
      exact hC_open.inter (isOpen_lt continuous_const hcross_cont)
    have hR_open : IsOpen R := by
      rw [hR_eq]
      exact hRneg_open.union hRcross_open
    let X : EuclideanSpace ℝ (Fin 2) →ₗ[ℝ] ℝ :=
      PiLp.projₗ (𝕜 := ℝ) (p := (2 : ENNReal)) (β := fun _ : Fin 2 => ℝ) 0
    let Y : EuclideanSpace ℝ (Fin 2) →ₗ[ℝ] ℝ :=
      PiLp.projₗ (𝕜 := ℝ) (p := (2 : ENNReal)) (β := fun _ : Fin 2 => ℝ) 1
    let Cross : EuclideanSpace ℝ (Fin 2) →ₗ[ℝ] ℝ := c • Y - s • X
    have hC_conv : Convex ℝ C := by
      dsimp [C]
      exact convex_ball _ _
    have hYgt : Convex ℝ {z : EuclideanSpace ℝ (Fin 2) | (0 : ℝ) < Y z} :=
      convex_halfSpace_gt Y.isLinear 0
    have hYlt : Convex ℝ {z : EuclideanSpace ℝ (Fin 2) | Y z < (0 : ℝ)} :=
      convex_halfSpace_lt Y.isLinear 0
    have hCrossGt :
        Convex ℝ {z : EuclideanSpace ℝ (Fin 2) | (0 : ℝ) < Cross z} :=
      convex_halfSpace_gt Cross.isLinear 0
    have hCrossLt :
        Convex ℝ {z : EuclideanSpace ℝ (Fin 2) | Cross z < (0 : ℝ)} :=
      convex_halfSpace_lt Cross.isLinear 0
    have hL_conv : Convex ℝ L := by
      simpa [L, cross, X, Y, Cross, Set.inter_def, sub_eq_add_neg, add_comm,
        add_left_comm, add_assoc] using
        ((hC_conv.inter hYgt).inter (hC_conv.inter hCrossLt))
    have hRneg_conv : Convex ℝ Rneg := by
      simpa [Rneg, Y, Set.inter_def] using (hC_conv.inter hYlt)
    have hRcross_conv : Convex ℝ Rcross := by
      simpa [Rcross, cross, X, Y, Cross, Set.inter_def, sub_eq_add_neg, add_comm,
        add_left_comm, add_assoc] using (hC_conv.inter hCrossGt)
    have scaled_mem (w : EuclideanSpace ℝ (Fin 2)) :
        let δ : ℝ := a / (2 * (‖w‖ + 1))
        0 < δ ∧ δ • w ∈ C := by
      intro δ
      have hden_pos : 0 < 2 * (‖w‖ + 1) := by positivity
      have hδ_pos : 0 < δ := by
        dsimp [δ]
        positivity
      constructor
      · exact hδ_pos
      · dsimp [C]
        rw [Metric.mem_ball, dist_zero_right, norm_smul]
        rw [Real.norm_eq_abs, abs_of_pos hδ_pos]
        dsimp [δ]
        rw [div_mul_eq_mul_div]
        rw [div_lt_iff₀ hden_pos]
        nlinarith [ha, norm_nonneg w]
    have hL_nonempty : L.Nonempty := by
      rcases hpos with hs | ⟨hs0, hc⟩
      · let w : EuclideanSpace ℝ (Fin 2) :=
          WithLp.toLp 2 (fun i : Fin 2 => if i = 0 then c + 1 else s)
        let δ : ℝ := a / (2 * (‖w‖ + 1))
        have hδ := scaled_mem w
        dsimp only at hδ
        refine ⟨δ • w, ?_⟩
        dsimp [L, cross]
        constructor
        · exact hδ.2
        constructor
        · simp [w]
          positivity
        · have hcross : cross (δ • w) = -δ * s := by
            dsimp [cross]
            simp [w]
            ring
          change cross (δ • w) < 0
          rw [hcross]
          nlinarith [hδ.1, hs]
      · let w : EuclideanSpace ℝ (Fin 2) :=
          WithLp.toLp 2 (fun i : Fin 2 => if i = 0 then 0 else 1)
        let δ : ℝ := a / (2 * (‖w‖ + 1))
        have hδ := scaled_mem w
        dsimp only at hδ
        refine ⟨δ • w, ?_⟩
        dsimp [L, cross]
        constructor
        · exact hδ.2
        constructor
        · simpa [w] using hδ.1
        · have hcross : cross (δ • w) = c * δ := by
            simpa [cross, w, hs0, mul_comm]
          change cross (δ • w) < 0
          rw [hcross]
          nlinarith [hδ.1, hc]
    have hRneg_nonempty : Rneg.Nonempty := by
      let w : EuclideanSpace ℝ (Fin 2) :=
        WithLp.toLp 2 (fun i : Fin 2 => if i = 0 then 0 else -1)
      let δ : ℝ := a / (2 * (‖w‖ + 1))
      have hδ := scaled_mem w
      dsimp only at hδ
      refine ⟨δ • w, ?_⟩
      dsimp [Rneg]
      constructor
      · exact hδ.2
      · simp [w]
        linarith [hδ.1]
    have hRcross_nonempty : Rcross.Nonempty := by
      rcases hpos with hs | ⟨hs0, hc⟩
      · let w : EuclideanSpace ℝ (Fin 2) :=
          WithLp.toLp 2 (fun i : Fin 2 => if i = 0 then -1 else 0)
        let δ : ℝ := a / (2 * (‖w‖ + 1))
        have hδ := scaled_mem w
        dsimp only at hδ
        refine ⟨δ • w, ?_⟩
        dsimp [Rcross, cross]
        constructor
        · exact hδ.2
        · have hcross : cross (δ • w) = s * δ := by
            simpa [cross, w, mul_comm]
          change 0 < cross (δ • w)
          rw [hcross]
          positivity
      · let w : EuclideanSpace ℝ (Fin 2) :=
          WithLp.toLp 2 (fun i : Fin 2 => if i = 0 then 0 else -1)
        let δ : ℝ := a / (2 * (‖w‖ + 1))
        have hδ := scaled_mem w
        dsimp only at hδ
        refine ⟨δ • w, ?_⟩
        dsimp [Rcross, cross]
        constructor
        · exact hδ.2
        · have hcross : cross (δ • w) = -c * δ := by
            simpa [cross, w, hs0, mul_comm]
          change 0 < cross (δ • w)
          rw [hcross]
          nlinarith [hδ.1, hc]
    have hR_inter_nonempty : (Rneg ∩ Rcross).Nonempty := by
      rcases hpos with hs | ⟨hs0, hc⟩
      · let w : EuclideanSpace ℝ (Fin 2) :=
          WithLp.toLp 2 (fun i : Fin 2 => if i = 0 then -(c + 1) else -s)
        let δ : ℝ := a / (2 * (‖w‖ + 1))
        have hδ := scaled_mem w
        dsimp only at hδ
        refine ⟨δ • w, ?_, ?_⟩
        · dsimp [Rneg]
          constructor
          · exact hδ.2
          · simp [w]
            nlinarith [hδ.1, hs]
        · dsimp [Rcross, cross]
          constructor
          · exact hδ.2
          · have hcross : cross (δ • w) = δ * s := by
              dsimp [cross]
              simp [w]
              ring
            change 0 < cross (δ • w)
            rw [hcross]
            positivity
      · let w : EuclideanSpace ℝ (Fin 2) :=
          WithLp.toLp 2 (fun i : Fin 2 => if i = 0 then 0 else -1)
        let δ : ℝ := a / (2 * (‖w‖ + 1))
        have hδ := scaled_mem w
        dsimp only at hδ
        refine ⟨δ • w, ?_, ?_⟩
        · dsimp [Rneg]
          constructor
          · exact hδ.2
          · simp [w]
            linarith [hδ.1]
        · dsimp [Rcross, cross]
          constructor
          · exact hδ.2
          · have hcross : cross (δ • w) = -c * δ := by
              simpa [cross, w, hs0, mul_comm]
            change 0 < cross (δ • w)
            rw [hcross]
            nlinarith [hδ.1, hc]
    have hL_connected : IsConnected L :=
      hL_conv.isConnected hL_nonempty
    have hRneg_connected : IsConnected Rneg :=
      hRneg_conv.isConnected hRneg_nonempty
    have hRcross_connected : IsConnected Rcross :=
      hRcross_conv.isConnected hRcross_nonempty
    have hR_connected : IsConnected R := by
      rw [hR_eq]
      exact IsConnected.union hR_inter_nonempty hRneg_connected hRcross_connected
    let Bad : Set (EuclideanSpace ℝ (Fin 2)) :=
      Gbase ∪ Gother ∪ ({0} : Set (EuclideanSpace ℝ (Fin 2)))
    have hcross_Gother {z : EuclideanSpace ℝ (Fin 2)} (hz : z ∈ Gother) :
        cross z = 0 := by
      dsimp [Gother] at hz
      rcases hz with ⟨_, t, _ht, hx, hy⟩
      dsimp [cross]
      rw [hx, hy]
      ring
    have hnot_yneg_Gother {z : EuclideanSpace ℝ (Fin 2)}
        (hyneg : z 1 < 0) (hz : z ∈ Gother) : False := by
      dsimp [Gother] at hz
      rcases hz with ⟨_, t, ht, _hx, hy⟩
      rcases hpos with hs | ⟨hs0, _hc⟩
      · rw [hy] at hyneg
        nlinarith
      · rw [hy, hs0] at hyneg
        nlinarith
    have hcross_Gbase_nonpos {z : EuclideanSpace ℝ (Fin 2)} (hz : z ∈ Gbase) :
        cross z ≤ 0 := by
      dsimp [Gbase] at hz
      rcases hz with ⟨_, hy0, hxpos⟩
      rcases hpos with hs | ⟨hs0, _hc⟩
      · dsimp [cross]
        rw [hy0]
        nlinarith
      · dsimp [cross]
        rw [hy0, hs0]
        linarith
    have hLR_disjoint : Disjoint L R := by
      rw [Set.disjoint_left]
      intro z hzL hzR
      dsimp [L, cross] at hzL
      dsimp [R, cross] at hzR
      rcases hzL with ⟨_, hypos, hqneg⟩
      rcases hzR with ⟨_, hyneg | hqpos⟩
      · linarith
      · linarith
    have hL_bad_disjoint : Disjoint L Bad := by
      rw [Set.disjoint_left]
      intro z hzL hzBad
      dsimp [L, cross] at hzL
      rcases hzL with ⟨_, hypos, hqneg⟩
      dsimp [Bad] at hzBad
      rcases hzBad with (hzGbase | hzGother) | hzZero
      · dsimp [Gbase] at hzGbase
        rcases hzGbase with ⟨_, hy0, _⟩
        linarith
      · have hq := hcross_Gother hzGother
        linarith
      · rw [Set.mem_singleton_iff] at hzZero
        subst z
        simp at hypos
    have hR_bad_disjoint : Disjoint R Bad := by
      rw [Set.disjoint_left]
      intro z hzR hzBad
      dsimp [R, cross] at hzR
      rcases hzR with ⟨_, hyneg | hqpos⟩
      · dsimp [Bad] at hzBad
        rcases hzBad with (hzGbase | hzGother) | hzZero
        · dsimp [Gbase] at hzGbase
          rcases hzGbase with ⟨_, hy0, _⟩
          linarith
        · exact hnot_yneg_Gother hyneg hzGother
        · rw [Set.mem_singleton_iff] at hzZero
          subst z
          simp at hyneg
      · dsimp [Bad] at hzBad
        rcases hzBad with (hzGbase | hzGother) | hzZero
        · have hq_nonpos := hcross_Gbase_nonpos hzGbase
          linarith
        · have hq := hcross_Gother hzGother
          linarith
        · rw [Set.mem_singleton_iff] at hzZero
          subst z
          simp [cross] at hqpos
    have hcover : C \ Bad = L ∪ R := by
      ext z
      constructor
      · intro hz
        rcases hz with ⟨hzC, hznotBad⟩
        have hnotGbase : z ∉ Gbase := by
          intro h
          exact hznotBad (by dsimp [Bad]; exact Or.inl (Or.inl h))
        have hnotGother : z ∉ Gother := by
          intro h
          exact hznotBad (by dsimp [Bad]; exact Or.inl (Or.inr h))
        have hnotZero : z ≠ 0 := by
          intro hzero
          exact hznotBad (by
            dsimp [Bad]
            exact Or.inr (by simpa [hzero]))
        rcases lt_trichotomy (z 1) 0 with hyneg | hyeq | hypos
        · right
          dsimp [R, cross]
          exact ⟨hzC, Or.inl hyneg⟩
        · rcases lt_trichotomy (z 0) 0 with hxneg | hxeq | hxpos
          · rcases hpos with hs | ⟨hs0, hc⟩
            · right
              dsimp [R, cross]
              constructor
              · exact hzC
              · right
                rw [hyeq]
                nlinarith
            · exfalso
              apply hnotGother
              refine ⟨hzC, z 0 / c, ?_, ?_, ?_⟩
              · exact div_pos_of_neg_of_neg hxneg hc
              · field_simp [ne_of_lt hc]
              · rw [hyeq, hs0, mul_zero]
          · exfalso
            apply hnotZero
            apply PiLp.ext
            intro i
            fin_cases i <;> simp [hxeq, hyeq]
          · exfalso
            apply hnotGbase
            dsimp [Gbase]
            exact ⟨hzC, hyeq, hxpos⟩
        · rcases lt_trichotomy (cross z) 0 with hqneg | hqeq | hqpos
          · left
            dsimp [L, cross]
            exact ⟨hzC, hypos, hqneg⟩
          · exfalso
            rcases hpos with hs | ⟨hs0, hc⟩
            · apply hnotGother
              refine ⟨hzC, z 1 / s, ?_, ?_, ?_⟩
              · exact div_pos hypos hs
              · have hqeq' : c * z 1 - s * z 0 = 0 := by
                  simpa [cross] using hqeq
                field_simp [ne_of_gt hs]
                nlinarith
              · field_simp [ne_of_gt hs]
            · have hqeq' : c * z 1 = 0 := by
                simpa [cross, hs0] using hqeq
              nlinarith
          · right
            dsimp [R, cross]
            exact ⟨hzC, Or.inr hqpos⟩
      · intro hz
        constructor
        · rcases hz with hzL | hzR
          · dsimp [L] at hzL
            exact hzL.1
          · dsimp [R] at hzR
            exact hzR.1
        · intro hzBad
          rcases hz with hzL | hzR
          · exact (Set.disjoint_left.mp hL_bad_disjoint) hzL hzBad
          · exact (Set.disjoint_left.mp hR_bad_disjoint) hzR hzBad
    have hchart_cont : Continuous chart := by
      dsimp [chart]
      fun_prop
    have hchart_zero : chart (0 : EuclideanSpace ℝ (Fin 2)) = p := by
      dsimp [chart]
      simp
    have hchart_inj : Function.Injective chart := by
      intro z w hzw
      have hrep0 :
          (0 : EuclideanSpace ℝ (Fin 2)) =
            (z 0 - w 0) • base + (z 1 - w 1) • PlanarRot90 base := by
        have hzero : chart z - chart w = (0 : EuclideanSpace ℝ (Fin 2)) :=
          sub_eq_zero.mpr hzw
        have hdiff :
            chart z - chart w =
              (z 0 - w 0) • base + (z 1 - w 1) • PlanarRot90 base := by
          apply PiLp.ext
          intro k
          fin_cases k <;> simp [chart] <;> ring
        rw [← hdiff]
        exact hzero.symm
      have hcoeff :=
        PlanarRot90CoefficientUniqueness (d := base)
          (v := (0 : EuclideanSpace ℝ (Fin 2))) hbase hrep0
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
    let invCoord : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 2) :=
      fun q => WithLp.toLp 2 (fun i : Fin 2 =>
        if i = 0 then inner ℝ (q - p) base / (‖base‖ ^ 2)
        else inner ℝ (q - p) (PlanarRot90 base) / (‖base‖ ^ 2))
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
    have himage_eq_preimage (S : Set (EuclideanSpace ℝ (Fin 2))) :
        chart '' S = invCoord ⁻¹' S := by
      ext q
      constructor
      · rintro ⟨z, hz, rfl⟩
        simpa [hleft_inv z] using hz
      · intro hq
        exact ⟨invCoord q, hq, hright_inv q⟩
    have hC_image_open : IsOpen (chart '' C) := by
      rw [himage_eq_preimage C]
      exact hC_open.preimage hinv_cont
    have hL_image_open : IsOpen (chart '' L) := by
      rw [himage_eq_preimage L]
      exact hL_open.preimage hinv_cont
    have hR_image_open : IsOpen (chart '' R) := by
      rw [himage_eq_preimage R]
      exact hR_open.preimage hinv_cont
    have image_disjoint
        {A B : Set (EuclideanSpace ℝ (Fin 2))} (hAB : Disjoint A B) :
        Disjoint (chart '' A) (chart '' B) := by
      rw [Set.disjoint_left]
      rintro q ⟨x, hxA, rfl⟩ ⟨y, hyB, hyx⟩
      have hy_eq : y = x := hchart_inj hyx
      rw [hy_eq] at hyB
      exact (Set.disjoint_left.mp hAB) hxA hyB
    have himage_LR_disjoint : Disjoint (chart '' L) (chart '' R) :=
      image_disjoint hLR_disjoint
    have hL_image_connected : IsConnected (chart '' L) :=
      hL_connected.image chart hchart_cont.continuousOn
    have hR_image_connected : IsConnected (chart '' R) :=
      hR_connected.image chart hchart_cont.continuousOn
    have image_C_subset_ball : chart '' C ⊆ Metric.ball p rho := by
      rintro q ⟨z, hzC, rfl⟩
      rw [Metric.mem_ball, dist_eq_norm]
      have hsub :
          p + z 0 • base + z 1 • PlanarRot90 base - p =
            z 0 • base + z 1 • PlanarRot90 base := by
        abel
      dsimp [chart]
      rw [hsub]
      rw [← sq_lt_sq₀ (norm_nonneg _) (le_of_lt hrho)]
      rw [hnorm_sq z]
      have hzsq : z 0 ^ 2 + z 1 ^ 2 < a ^ 2 := by
        simpa [C, hball_eq] using hzC
      have hmul : (z 0 ^ 2 + z 1 ^ 2) * ‖base‖ ^ 2 < a ^ 2 * ‖base‖ ^ 2 :=
        mul_lt_mul_of_pos_right hzsq (sq_pos_of_pos hbase_norm_pos)
      simpa [hscale_sq] using hmul
    have ball_subset_image_C : Metric.ball p rho ⊆ chart '' C := by
      intro q hq
      refine ⟨invCoord q, ?_, hright_inv q⟩
      dsimp [C]
      rw [hball_eq]
      rw [Metric.mem_ball, dist_eq_norm] at hq
      have hdecomp :
          q - p = (invCoord q) 0 • base + (invCoord q) 1 • PlanarRot90 base := by
        simpa [invCoord] using PlanarRot90Decomposition base (q - p) hbase
      have hsq_norm : ‖q - p‖ ^ 2 =
          ((invCoord q) 0 ^ 2 + (invCoord q) 1 ^ 2) * ‖base‖ ^ 2 := by
        rw [hdecomp, hnorm_sq]
      have hsq_lt : ‖q - p‖ ^ 2 < rho ^ 2 :=
        (sq_lt_sq₀ (norm_nonneg _) (le_of_lt hrho)).mpr hq
      have hmul : ((invCoord q) 0 ^ 2 + (invCoord q) 1 ^ 2) *
            ‖base‖ ^ 2 <
          a ^ 2 * ‖base‖ ^ 2 := by
        simpa [hsq_norm, hscale_sq] using hsq_lt
      have hbase_sq_pos : 0 < ‖base‖ ^ 2 := sq_pos_of_pos hbase_norm_pos
      exact lt_of_mul_lt_mul_right hmul (le_of_lt hbase_sq_pos)
    have himage_C_eq_ball : chart '' C = Metric.ball p rho :=
      Set.Subset.antisymm image_C_subset_ball ball_subset_image_C
    have himage_zero :
        chart '' ({0} : Set (EuclideanSpace ℝ (Fin 2))) =
          ({p} : Set (EuclideanSpace ℝ (Fin 2))) := by
      ext q
      constructor
      · rintro ⟨z, hz, rfl⟩
        rw [Set.mem_singleton_iff] at hz
        rw [hz, hchart_zero]
        exact Set.mem_singleton p
      · intro hq
        rw [Set.mem_singleton_iff] at hq
        refine ⟨0, Set.mem_singleton 0, ?_⟩
        rw [hq, hchart_zero]
    have hactualBad_eq_image :
        (chart '' Gbase) ∪ (chart '' Gother) ∪
            ({p} : Set (EuclideanSpace ℝ (Fin 2))) =
          chart '' Bad := by
      dsimp [Bad]
      rw [Set.image_union, Set.image_union, himage_zero]
    have hL_image_bad_disjoint :
        Disjoint (chart '' L)
          ((chart '' Gbase) ∪ (chart '' Gother) ∪
            ({p} : Set (EuclideanSpace ℝ (Fin 2)))) := by
      rw [hactualBad_eq_image]
      exact image_disjoint hL_bad_disjoint
    have hR_image_bad_disjoint :
        Disjoint (chart '' R)
          ((chart '' Gbase) ∪ (chart '' Gother) ∪
            ({p} : Set (EuclideanSpace ℝ (Fin 2)))) := by
      rw [hactualBad_eq_image]
      exact image_disjoint hR_bad_disjoint
    have himage_split :
        chart '' C \
            ((chart '' Gbase) ∪ (chart '' Gother) ∪
              ({p} : Set (EuclideanSpace ℝ (Fin 2)))) =
          chart '' L ∪ chart '' R := by
      rw [hactualBad_eq_image]
      ext q
      constructor
      · rintro ⟨⟨z, hzC, rfl⟩, hqnotBad⟩
        have hznotBad : z ∉ Bad := by
          intro hzBad
          exact hqnotBad ⟨z, hzBad, rfl⟩
        have hzLR : z ∈ L ∪ R := by
          have hzCBad : z ∈ C \ Bad := ⟨hzC, hznotBad⟩
          simpa [hcover] using hzCBad
        rcases hzLR with hzL | hzR
        · exact Or.inl ⟨z, hzL, rfl⟩
        · exact Or.inr ⟨z, hzR, rfl⟩
      · rintro (⟨z, hzL, rfl⟩ | ⟨z, hzR, rfl⟩)
        · have hzCBad : z ∈ C \ Bad := by
            have hzLR : z ∈ L ∪ R := Or.inl hzL
            simpa [hcover] using hzLR
          refine ⟨⟨z, hzCBad.1, rfl⟩, ?_⟩
          rintro ⟨w, hwBad, hw_eq⟩
          have hwz : w = z := hchart_inj hw_eq
          rw [hwz] at hwBad
          exact hzCBad.2 hwBad
        · have hzCBad : z ∈ C \ Bad := by
            have hzLR : z ∈ L ∪ R := Or.inr hzR
            simpa [hcover] using hzLR
          refine ⟨⟨z, hzCBad.1, rfl⟩, ?_⟩
          rintro ⟨w, hwBad, hw_eq⟩
          have hwz : w = z := hchart_inj hw_eq
          rw [hwz] at hwBad
          exact hzCBad.2 hwBad
    have hGbase_image :
        chart '' Gbase =
          {q | q ∈ Metric.ball p rho ∧ ∃ t : ℝ, 0 < t ∧ q = p + t • base} := by
      ext q
      constructor
      · rintro ⟨z, hzG, rfl⟩
        dsimp [Gbase] at hzG
        rcases hzG with ⟨hzC, hz1, hz0⟩
        constructor
        · exact image_C_subset_ball ⟨z, hzC, rfl⟩
        · refine ⟨z 0, hz0, ?_⟩
          dsimp [chart]
          rw [hz1]
          simp
      · rintro ⟨hqball, t, ht, hq⟩
        let zt : EuclideanSpace ℝ (Fin 2) :=
          WithLp.toLp 2 (fun i : Fin 2 => if i = 0 then t else 0)
        have hchart_zt : chart zt = p + t • base := by
          dsimp [chart, zt]
          simp
        have hztC : zt ∈ C := by
          rcases ball_subset_image_C hqball with ⟨w, hwC, hwq⟩
          have hwzt : w = zt := by
            apply hchart_inj
            rw [hwq, hq, hchart_zt]
          simpa [hwzt] using hwC
        refine ⟨zt, ?_, ?_⟩
        · dsimp [Gbase, zt]
          refine ⟨hztC, ?_, ?_⟩
          · simp
          · simpa using ht
        · rw [hchart_zt, hq]
    have hGother_image :
        chart '' Gother =
          {q | q ∈ Metric.ball p rho ∧ ∃ t : ℝ, 0 < t ∧ q = p + t • other} := by
      ext q
      constructor
      · rintro ⟨z, hzG, rfl⟩
        dsimp [Gother] at hzG
        rcases hzG with ⟨hzC, t, ht, hz0, hz1⟩
        constructor
        · exact image_C_subset_ball ⟨z, hzC, rfl⟩
        · refine ⟨t, ht, ?_⟩
          dsimp [chart]
          rw [hz0, hz1, hrep]
          module
      · rintro ⟨hqball, t, ht, hq⟩
        let zt : EuclideanSpace ℝ (Fin 2) :=
          WithLp.toLp 2 (fun i : Fin 2 => if i = 0 then t * c else t * s)
        have hchart_zt : chart zt = p + t • other := by
          dsimp [chart, zt]
          rw [hrep]
          simp
          module
        have hztC : zt ∈ C := by
          rcases ball_subset_image_C hqball with ⟨w, hwC, hwq⟩
          have hwzt : w = zt := by
            apply hchart_inj
            rw [hwq, hq, hchart_zt]
          simpa [hwzt] using hwC
        refine ⟨zt, ?_, ?_⟩
        · dsimp [Gother, zt]
          refine ⟨hztC, t, ht, ?_, ?_⟩ <;> simp
        · rw [hchart_zt, hq]
    have hactual_split :
        Metric.ball p rho \
            ((chart '' Gbase) ∪ (chart '' Gother) ∪
              ({p} : Set (EuclideanSpace ℝ (Fin 2)))) =
          chart '' L ∪ chart '' R := by
      rw [← himage_C_eq_ball]
      exact himage_split
    exact ⟨ha, hC_image_open, hL_image_open, hR_image_open, hL_image_connected,
      hR_image_connected, himage_LR_disjoint, himage_C_eq_ball, hGbase_image,
      hGother_image, hL_image_bad_disjoint, hR_image_bad_disjoint, hactual_split⟩
  rcases PolygonalArcInteriorTwoRaySectorOrientationChoice hu hv hnot_same with hchoice | hchoice
  · let c : ℝ := inner ℝ v u / (‖u‖ ^ 2)
    let s : ℝ := inner ℝ v (PlanarRot90 u) / (‖u‖ ^ 2)
    rcases hchoice with ⟨hrep, hpos⟩
    refine ⟨u, v, c, s, ?_, hrep, hpos, ?_⟩
    · exact Or.inl ⟨rfl, rfl⟩
    · exact transport u v c s hu hrep hpos
  · let c : ℝ := inner ℝ u v / (‖v‖ ^ 2)
    let s : ℝ := inner ℝ u (PlanarRot90 v) / (‖v‖ ^ 2)
    rcases hchoice with ⟨hrep, hspos⟩
    refine ⟨v, u, c, s, ?_, hrep, Or.inl hspos, ?_⟩
    · exact Or.inr ⟨rfl, rfl⟩
    · exact transport v u c s hv hrep (Or.inl hspos)
