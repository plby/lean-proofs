import Util.IncidenceGeometry.Basic

open Classical
noncomputable section

lemma EndpointUnitDiskLocalChordFrame {κ : Type*} [Fintype κ]
    (z : EuclideanSpace ℝ (Fin 2)) (r : ℝ) (_hr : 0 < r)
    (u v : κ → EuclideanSpace ℝ (Fin 2))
    (huv_center_open : ∀ i : κ, z ∈ openSegment ℝ (u i) (v i))
    (huv_ne : ∀ i : κ, u i ≠ v i)
    (hnonparallel :
      ∀ ⦃i j : κ⦄, i ≠ j →
        ¬ ∃ c : ℝ, v j - z = c • (v i - z)) :
    let point : ℝ → ℝ → EuclideanSpace ℝ (Fin 2) :=
      fun x y => WithLp.toLp 2 (fun k : Fin 2 => if k = 0 then x else y)
    ∃ toWorld : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 2),
      ∃ m : κ → ℝ,
        Function.Injective toWorld ∧
          Function.Injective m ∧
            toWorld (0 : EuclideanSpace ℝ (Fin 2)) = z ∧
              (∀ p : EuclideanSpace ℝ (Fin 2),
                p ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) r →
                  toWorld p ∈ Metric.ball z r) ∧
                (∀ p : EuclideanSpace ℝ (Fin 2),
                  p ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) r →
                    toWorld p ∈ Metric.closedBall z r) ∧
                  (∀ x y : EuclideanSpace ℝ (Fin 2),
                    toWorld '' segment ℝ x y =
                      segment ℝ (toWorld x) (toWorld y)) ∧
                    (∀ x y : EuclideanSpace ℝ (Fin 2),
                      toWorld '' openSegment ℝ x y =
                        openSegment ℝ (toWorld x) (toWorld y)) ∧
                      (∀ {p q p' q' : EuclideanSpace ℝ (Fin 2)} {c : ℝ},
                        toWorld q - toWorld p = c • (toWorld q' - toWorld p') →
                          q - p = c • (q' - p')) ∧
                        (∀ i : κ,
                          ∃ α β : ℝ,
                            0 < α ∧
                              0 < β ∧
                                ((u i = toWorld (point (-α) (-(m i * α))) ∧
                                    v i = toWorld (point β (m i * β))) ∨
                                  (u i = toWorld (point β (m i * β)) ∧
                                    v i = toWorld (point (-α) (-(m i * α)))))) := by
  intro point
  let direction : κ → EuclideanSpace ℝ (Fin 2) := fun i => v i - z
  have hv_ne_z : ∀ i : κ, v i ≠ z := by
    intro i hvz
    have hv_open : v i ∈ openSegment ℝ (u i) (v i) := by
      simpa [hvz] using huv_center_open i
    have huv_eq : u i = v i :=
      (right_mem_openSegment_iff (𝕜 := ℝ) (x := u i) (y := v i)).1 hv_open
    exact huv_ne i huv_eq
  have hdirection_ne : ∀ i : κ, direction i ≠ 0 := by
    intro i hdir
    exact hv_ne_z i (sub_eq_zero.mp (by simpa [direction] using hdir))
  let badSlope : κ → ℝ :=
    fun i =>
      if h : (direction i) 0 = 0 then 0 else (direction i) 1 / (direction i) 0
  obtain ⟨t, ht_bad⟩ :=
    Finset.exists_notMem ((Finset.univ.image badSlope) : Finset ℝ)
  have hdenom_ne :
      ∀ i : κ, (direction i) 1 - t * (direction i) 0 ≠ 0 := by
    intro i hzero
    by_cases hx : (direction i) 0 = 0
    · have hy : (direction i) 1 = 0 := by
        simpa [hx] using hzero
      have hdir_zero : direction i = 0 := by
        apply PiLp.ext
        intro k
        fin_cases k
        · exact hx
        · exact hy
      exact hdirection_ne i hdir_zero
    · have ht_eq : t = (direction i) 1 / (direction i) 0 := by
        field_simp [hx]
        nlinarith
      have hmem : badSlope i ∈ (Finset.univ.image badSlope : Finset ℝ) := by
        exact Finset.mem_image.mpr ⟨i, by simp, rfl⟩
      exact ht_bad (by simpa [badSlope, hx, ht_eq] using hmem)
  let s : ℝ := (|t| + 2)⁻¹
  have hden_pos : 0 < |t| + 2 := by positivity
  have hs_pos : 0 < s := by
    dsimp [s]
    exact inv_pos.mpr hden_pos
  let frameLin : EuclideanSpace ℝ (Fin 2) →ₗ[ℝ] EuclideanSpace ℝ (Fin 2) :=
    { toFun := fun p => point (s * p 1) (s * (p 0 + t * p 1))
      map_add' := by
        intro p q
        apply PiLp.ext
        intro k
        fin_cases k <;> simp [point]
        all_goals ring
      map_smul' := by
        intro c p
        apply PiLp.ext
        intro k
        fin_cases k <;> simp [point]
        all_goals ring }
  have hframeLin_inj : Function.Injective frameLin := by
    intro p q hpq
    apply PiLp.ext
    intro k
    have h0 := congrArg (fun w : EuclideanSpace ℝ (Fin 2) => w 0) hpq
    have h1 := congrArg (fun w : EuclideanSpace ℝ (Fin 2) => w 1) hpq
    have hp1q1 : p 1 = q 1 := by
      have h : s * p 1 = s * q 1 := by
        simpa [frameLin, point] using h0
      exact mul_left_cancel₀ hs_pos.ne' h
    have hp0q0 : p 0 = q 0 := by
      have h : s * (p 0 + t * p 1) = s * (q 0 + t * q 1) := by
        simpa [frameLin, point] using h1
      have h' : p 0 + t * p 1 = q 0 + t * q 1 :=
        mul_left_cancel₀ hs_pos.ne' h
      calc
        p 0 = (p 0 + t * p 1) - t * p 1 := by ring
        _ = (q 0 + t * q 1) - t * p 1 := by rw [h']
        _ = (q 0 + t * q 1) - t * q 1 := by rw [hp1q1]
        _ = q 0 := by ring
    fin_cases k
    · exact hp0q0
    · exact hp1q1
  have hframe_nonexpansive :
      ∀ p : EuclideanSpace ℝ (Fin 2), ‖frameLin p‖ ≤ ‖p‖ := by
    intro p
    have hp0 : |p 0| ≤ ‖p‖ := by
      have hnormsq := PiLp.norm_sq_eq_of_L2 (fun _ : Fin 2 => ℝ) p
      have hnormsq' : ‖p‖ ^ 2 = (p 0) ^ 2 + (p 1) ^ 2 := by
        simpa [EuclideanSpace, Fin.sum_univ_two, sq, Real.norm_eq_abs] using hnormsq
      have hsq : (p 0) ^ 2 ≤ ‖p‖ ^ 2 := by nlinarith [sq_nonneg (p 1)]
      have h := sq_le_sq.mp hsq
      simpa [abs_of_nonneg (norm_nonneg p)] using h
    have hp1 : |p 1| ≤ ‖p‖ := by
      have hnormsq := PiLp.norm_sq_eq_of_L2 (fun _ : Fin 2 => ℝ) p
      have hnormsq' : ‖p‖ ^ 2 = (p 0) ^ 2 + (p 1) ^ 2 := by
        simpa [EuclideanSpace, Fin.sum_univ_two, sq, Real.norm_eq_abs] using hnormsq
      have hsq : (p 1) ^ 2 ≤ ‖p‖ ^ 2 := by nlinarith [sq_nonneg (p 0)]
      have h := sq_le_sq.mp hsq
      simpa [abs_of_nonneg (norm_nonneg p)] using h
    have hnorm_le_sum :
        ‖frameLin p‖ ≤ |(frameLin p) 0| + |(frameLin p) 1| := by
      let q : EuclideanSpace ℝ (Fin 2) := frameLin p
      have hnormsq := PiLp.norm_sq_eq_of_L2 (fun _ : Fin 2 => ℝ) q
      have hnormsq' : ‖q‖ ^ 2 = (q 0) ^ 2 + (q 1) ^ 2 := by
        simpa [EuclideanSpace, Fin.sum_univ_two, sq, Real.norm_eq_abs] using hnormsq
      have hsq : ‖q‖ ^ 2 ≤ (|q 0| + |q 1|) ^ 2 := by
        rw [hnormsq']
        have h0sq : |q 0| ^ 2 = (q 0) ^ 2 := by rw [sq_abs]
        have h1sq : |q 1| ^ 2 = (q 1) ^ 2 := by rw [sq_abs]
        nlinarith [sq_nonneg (|q 0|), sq_nonneg (|q 1|),
          abs_nonneg (q 0), abs_nonneg (q 1), h0sq, h1sq]
      have h := sq_le_sq.mp hsq
      have habs_sum : |(|q 0| + |q 1|)| = |q 0| + |q 1| :=
        abs_of_nonneg (add_nonneg (abs_nonneg _) (abs_nonneg _))
      simpa [q, abs_of_nonneg (norm_nonneg q), habs_sum] using h
    have hsum_le : |(frameLin p) 0| + |(frameLin p) 1| ≤ ‖p‖ := by
      have hs_nonneg : 0 ≤ s := le_of_lt hs_pos
      have h₁ : |s * p 1| = s * |p 1| := by
        rw [abs_mul, abs_of_nonneg hs_nonneg]
      have h₂ : |s * (p 0 + t * p 1)| = s * |p 0 + t * p 1| := by
        rw [abs_mul, abs_of_nonneg hs_nonneg]
      have habs_add : |p 0 + t * p 1| ≤ |p 0| + |t| * |p 1| := by
        calc
          |p 0 + t * p 1| ≤ |p 0| + |t * p 1| := abs_add_le _ _
          _ = |p 0| + |t| * |p 1| := by rw [abs_mul]
      have hinner :
          |p 1| + |p 0 + t * p 1| ≤ (|t| + 2) * ‖p‖ := by
        calc
          |p 1| + |p 0 + t * p 1| ≤
              |p 1| + (|p 0| + |t| * |p 1|) := by
            exact add_le_add (le_refl _) habs_add
          _ ≤ ‖p‖ + (‖p‖ + |t| * ‖p‖) := by
            exact add_le_add hp1
              (add_le_add hp0 (mul_le_mul_of_nonneg_left hp1 (abs_nonneg t)))
          _ = (|t| + 2) * ‖p‖ := by ring
      have hmain :
          s * |p 1| + s * |p 0 + t * p 1| ≤
            s * ((|t| + 2) * ‖p‖) := by
        rw [← mul_add]
        exact mul_le_mul_of_nonneg_left hinner hs_nonneg
      have hsden : s * (|t| + 2) = 1 := by
        dsimp [s]
        exact inv_mul_cancel₀ (ne_of_gt hden_pos)
      have htarget : s * ((|t| + 2) * ‖p‖) = ‖p‖ := by
        rw [← mul_assoc, hsden, one_mul]
      calc
        |(frameLin p) 0| + |(frameLin p) 1| =
            |s * p 1| + |s * (p 0 + t * p 1)| := by
          simp [frameLin, point]
        _ = s * |p 1| + s * |p 0 + t * p 1| := by
          rw [h₁, h₂]
        _ ≤ ‖p‖ := hmain.trans_eq htarget
    exact hnorm_le_sum.trans hsum_le
  let frame : EuclideanSpace ℝ (Fin 2) →ᵃ[ℝ] EuclideanSpace ℝ (Fin 2) :=
    { toFun := fun p => z + frameLin p
      linear := frameLin
      map_vadd' := by
        intro p q
        simp [vadd_eq_add]
        abel }
  let toWorld : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 2) :=
    fun p => frame p
  let m : κ → ℝ := fun i => (direction i) 0 / ((direction i) 1 - t * (direction i) 0)
  have hframe_point :
      ∀ (i : κ) (τ : ℝ),
        frameLin (point τ (m i * τ)) =
          ((s * τ) / ((direction i) 1 - t * (direction i) 0)) • direction i := by
    intro i τ
    apply PiLp.ext
    intro k
    fin_cases k
    · simp [frameLin, point, m]
      field_simp [hdenom_ne i]
    · simp [frameLin, point, m]
      field_simp [hdenom_ne i]
      ring
  have hm_inj : Function.Injective m := by
    intro i j hij
    by_contra hne
    have hmi : m i = m j := hij
    have hcross : (direction i) 0 * (direction j) 1 =
        (direction j) 0 * (direction i) 1 := by
      have hdeni : (direction i) 1 - t * (direction i) 0 ≠ 0 := hdenom_ne i
      have hdenj : (direction j) 1 - t * (direction j) 0 ≠ 0 := hdenom_ne j
      have hi :
          (direction i) 0 =
            m i * ((direction i) 1 - t * (direction i) 0) := by
        dsimp [m]
        exact (div_mul_cancel₀ ((direction i) 0) hdeni).symm
      have hj :
          (direction j) 0 =
            m j * ((direction j) 1 - t * (direction j) 0) := by
        dsimp [m]
        exact (div_mul_cancel₀ ((direction j) 0) hdenj).symm
      have hprod :
          (direction i) 0 * ((direction j) 1 - t * (direction j) 0) =
            (direction j) 0 * ((direction i) 1 - t * (direction i) 0) := by
        calc
          (direction i) 0 * ((direction j) 1 - t * (direction j) 0) =
              (m i * ((direction i) 1 - t * (direction i) 0)) *
                ((direction j) 1 - t * (direction j) 0) := by
            nth_rewrite 1 [hi]
            rfl
          _ = (m j * ((direction j) 1 - t * (direction j) 0)) *
                ((direction i) 1 - t * (direction i) 0) := by
            rw [hmi]
            ring
          _ = (direction j) 0 * ((direction i) 1 - t * (direction i) 0) := by
            rw [← hj]
      nlinarith
    have hscalar : ∃ c : ℝ, direction j = c • direction i := by
      by_cases hx : (direction i) 0 = 0
      · have hyi : (direction i) 1 ≠ 0 := by
          intro hy
          apply hdirection_ne i
          apply PiLp.ext
          intro k
          fin_cases k
          · exact hx
          · exact hy
        have hxj : (direction j) 0 = 0 := by
          have hprod : (direction j) 0 * (direction i) 1 = 0 := by
            rw [← hcross, hx, zero_mul]
          exact (mul_eq_zero.mp hprod).resolve_right hyi
        refine ⟨(direction j) 1 / (direction i) 1, ?_⟩
        apply PiLp.ext
        intro k
        fin_cases k
        · simp [hx, hxj]
        · simp
          field_simp [hyi]
      · refine ⟨(direction j) 0 / (direction i) 0, ?_⟩
        apply PiLp.ext
        intro k
        fin_cases k
        · simp
          field_simp [hx]
        · simp
          field_simp [hx]
          nlinarith
    exact hnonparallel hne hscalar
  have htoWorld_inj : Function.Injective toWorld := by
    intro p q hpq
    apply hframeLin_inj
    have h : z + frameLin p = z + frameLin q := by
      simpa [toWorld, frame] using hpq
    exact add_left_cancel h
  have hreflect :
      ∀ {p q p' q' : EuclideanSpace ℝ (Fin 2)} {c : ℝ},
        toWorld q - toWorld p = c • (toWorld q' - toWorld p') →
          q - p = c • (q' - p') := by
    intro p q p' q' c h
    apply hframeLin_inj
    have hlin :
        frameLin (q - p) = c • frameLin (q' - p') := by
      calc
        frameLin (q - p) = toWorld q - toWorld p := by
          apply PiLp.ext
          intro k
          simp [toWorld, frame]
        _ = c • (toWorld q' - toWorld p') := h
        _ = c • frameLin (q' - p') := by
          congr 1
          apply PiLp.ext
          intro k
          simp [toWorld, frame]
    simpa using hlin
  have horient :
      ∀ i : κ,
        ∃ α β : ℝ,
          0 < α ∧
            0 < β ∧
              ((u i = toWorld (point (-α) (-(m i * α))) ∧
                  v i = toWorld (point β (m i * β))) ∨
                          (u i = toWorld (point β (m i * β)) ∧
                  v i = toWorld (point (-α) (-(m i * α))))) := by
    intro i
    have hcenter := huv_center_open i
    rw [openSegment_eq_image_lineMap] at hcenter
    rcases hcenter with ⟨lam, hlam, hzlam⟩
    let den : ℝ := (direction i) 1 - t * (direction i) 0
    have hden_ne : den ≠ 0 := by simpa [den] using hdenom_ne i
    have hlamden : 0 < 1 - lam := by linarith [hlam.2]
    have hu_eq :
        u i = z - (lam / (1 - lam)) • direction i := by
      apply PiLp.ext
      intro k
      have hzcoord := congrArg (fun p : EuclideanSpace ℝ (Fin 2) => p k) hzlam
      simp [AffineMap.lineMap_apply_module, direction] at hzcoord ⊢
      field_simp [ne_of_gt hlamden]
      ring_nf at hzcoord ⊢
      nlinarith
    have hv_eq : v i = z + (1 : ℝ) • direction i := by
      simp [direction]
    have hlamratio_pos : 0 < lam / (1 - lam) := div_pos hlam.1 hlamden
    have hsden_pos : 0 < s := hs_pos
    rcases lt_or_gt_of_ne hden_ne with hden_lt | hden_gt
    · let α : ℝ := -den / s
      let β : ℝ := (lam / (1 - lam)) * (-den / s)
      have hα : 0 < α := by
        dsimp [α]
        exact div_pos (neg_pos.mpr hden_lt) hs_pos
      have hβ : 0 < β := by
        dsimp [β]
        positivity
      refine ⟨α, β, hα, hβ, Or.inr ?_⟩
      constructor
      · have hcoeff : s * β / den = -(lam / (1 - lam)) := by
          dsimp [β]
          field_simp [hden_ne, hs_pos.ne']
        rw [hu_eq]
        dsimp [toWorld, frame]
        rw [hframe_point i β, hcoeff]
        simp [sub_eq_add_neg]
      · have hcoeff : s * (-α) / den = 1 := by
          dsimp [α]
          field_simp [hden_ne, hs_pos.ne']
        have hcoeff' : -(s * α) / den = 1 := by
          simpa [mul_neg] using hcoeff
        have hcoeff'' :
            -(s * α) / ((direction i) 1 - t * (direction i) 0) = 1 := by
          simpa [den] using hcoeff'
        rw [hv_eq]
        dsimp [toWorld, frame]
        have hfp := hframe_point i (-α)
        simpa [mul_neg, hcoeff''] using (congrArg (fun p => z + p) hfp).symm
    · let α : ℝ := (lam / (1 - lam)) * (den / s)
      let β : ℝ := den / s
      have hα : 0 < α := by
        dsimp [α]
        positivity
      have hβ : 0 < β := by
        dsimp [β]
        exact div_pos hden_gt hs_pos
      refine ⟨α, β, hα, hβ, Or.inl ?_⟩
      constructor
      · have hcoeff : s * (-α) / den = -(lam / (1 - lam)) := by
          dsimp [α]
          field_simp [hden_ne, hs_pos.ne']
        have hcoeff' : -(s * α) / den = -(lam / (1 - lam)) := by
          simpa [mul_neg] using hcoeff
        have hcoeff'' :
            -(s * α) / ((direction i) 1 + -(t * (direction i) 0)) =
              -(lam / (1 - lam)) := by
          simpa [den, sub_eq_add_neg] using hcoeff'
        rw [hu_eq]
        dsimp [toWorld, frame]
        have hfp := hframe_point i (-α)
        simpa [mul_neg, hcoeff'', sub_eq_add_neg] using
          (congrArg (fun p => z + p) hfp).symm
      · have hcoeff : s * β / den = 1 := by
          dsimp [β]
          field_simp [hden_ne, hs_pos.ne']
        rw [hv_eq]
        dsimp [toWorld, frame]
        rw [hframe_point i β, hcoeff]
  refine ⟨toWorld, m, htoWorld_inj, hm_inj, ?_, ?_, ?_, ?_, ?_, hreflect, horient⟩
  · apply PiLp.ext
    intro k
    simp [toWorld, frame, frameLin, point]
  · intro p hp
    rw [Metric.mem_ball] at hp ⊢
    have hp_norm : ‖p‖ < r := by
      simpa [dist_zero_right] using hp
    have hdist : dist (toWorld p) z = ‖frameLin p‖ := by
      rw [dist_eq_norm]
      congr 1
      apply PiLp.ext
      intro k
      simp [toWorld, frame]
    rw [hdist]
    exact lt_of_le_of_lt (hframe_nonexpansive p) hp_norm
  · intro p hp
    rw [Metric.mem_closedBall] at hp ⊢
    have hp_norm : ‖p‖ ≤ r := by
      simpa [dist_zero_right] using hp
    have hdist : dist (toWorld p) z = ‖frameLin p‖ := by
      rw [dist_eq_norm]
      congr 1
      apply PiLp.ext
      intro k
      simp [toWorld, frame]
    rw [hdist]
    exact le_trans (hframe_nonexpansive p) hp_norm
  · intro x y
    simpa [toWorld] using image_segment ℝ frame x y
  · intro x y
    simpa [toWorld] using image_openSegment ℝ frame x y
