import ErdosProblems.Erdos735.SylvesterGallai

open RealInnerProductSpace

namespace Erdos735DirectionalKelly

open SylvesterGallaiCore

variable {V P : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MetricSpace P]
  [NormedAddTorsor V P]

/-- Kelly's globally closest point--line configuration has an ordinary base line.
This is the constructive strengthening of Sylvester--Gallai needed for directional
arguments. -/
theorem exists_minimal_ordinary_line (S : Set P) (hfin : S.Finite)
    (hncol : ¬ Collinear ℝ S) :
    ∃ p ∈ S, ∃ a ∈ S, ∃ b ∈ S,
      a ≠ b ∧ p ∉ SylvesterGallai.lineThrough (V := V) a b ∧
      SylvesterGallai.IsOrdinaryLine (V := V) S a b ∧
      ∀ q ∈ S, ∀ c ∈ S, ∀ d ∈ S, c ≠ d →
        q ∉ SylvesterGallai.lineThrough (V := V) c d →
        SylvesterGallai.distToLine (V := V) p a b ≤
          SylvesterGallai.distToLine (V := V) q c d := by
  set T : Set (P × P × P) :=
    {x | x.1 ∈ S ∧ x.2.1 ∈ S ∧ x.2.2 ∈ S ∧ x.2.1 ≠ x.2.2 ∧
         x.1 ∉ SylvesterGallai.lineThrough (V := V) x.2.1 x.2.2} with hTdef
  have hTfin : T.Finite := by
    refine Set.Finite.subset (hfin.prod (hfin.prod hfin)) ?_
    rintro ⟨q, c, d⟩ ⟨h1, h2, h3, -, -⟩
    exact ⟨h1, h2, h3⟩
  have hTne : T.Nonempty := by
    by_contra hempty
    rw [Set.not_nonempty_iff_eq_empty] at hempty
    obtain ⟨a₀, ha₀, b₀, hb₀, hab₀⟩ :=
      SylvesterGallai.exists_ne_of_not_collinear (V := V) hncol
    refine hncol (SylvesterGallai.collinear_of_subset_line (V := V)
      (a := a₀) (b := b₀) fun q hq => ?_)
    by_contra hqL
    have hmemT : (q, a₀, b₀) ∈ T := ⟨hq, ha₀, hb₀, hab₀, hqL⟩
    rw [hempty] at hmemT
    exact hmemT
  obtain ⟨⟨p, a, b⟩, hmem, hmin⟩ :=
    Set.exists_min_image T
      (fun x => SylvesterGallai.distToLine (V := V) x.1 x.2.1 x.2.2) hTfin hTne
  obtain ⟨hpS, haS, hbS, hab, hpL⟩ := hmem
  have hord : SylvesterGallai.IsOrdinaryLine (V := V) S a b := by
    by_contra hnord
    obtain ⟨c, hcS, hcL, hca, hcb⟩ :=
      SylvesterGallai.exists_third (V := V) haS hbS hab hnord
    set e : V := b -ᵥ a with he_def
    have he : e ≠ 0 := by
      rw [he_def, vsub_ne_zero]
      exact fun h => hab h.symm
    set z : V := p -ᵥ a with hz_def
    set A : V := -(perp e z) with hA_def
    have hAperp : ⟪A, e⟫ = (0 : ℝ) := by
      have hne : ⟪e, e⟫ ≠ (0 : ℝ) := by
        simpa [real_inner_self_eq_norm_sq] using (norm_ne_zero_iff.mpr he)
      rw [hA_def, inner_neg_left, perp, inner_sub_left, real_inner_smul_left,
        div_mul_cancel₀ _ hne, sub_self, neg_zero]
    have hAnorm : ‖A‖ = SylvesterGallai.distToLine (V := V) p a b := by
      rw [hA_def, norm_neg, SylvesterGallai.distToLine]
    have hA : A ≠ 0 := by
      rw [← norm_ne_zero_iff, hAnorm]
      exact ne_of_gt (SylvesterGallai.distToLine_pos (V := V) hab hpL)
    set k : ℝ := ⟪z, e⟫ / ⟪e, e⟫ with hk_def
    have hAeq : A = k • e - z := by rw [hA_def, perp, hk_def]; abel
    have hline : ∀ x : P, x ∈ SylvesterGallai.lineThrough (V := V) a b →
        ∃ t : ℝ, (x -ᵥ p : V) = A + t • e := by
      intro x hx
      obtain ⟨cx, hcx⟩ :=
        (SylvesterGallai.mem_lineThrough_iff (V := V)).mp hx
      refine ⟨cx - k, ?_⟩
      have hxp : (x -ᵥ p : V) = (x -ᵥ a : V) - z := by
        rw [hz_def, vsub_sub_vsub_cancel_right]
      rw [hxp, hcx, hAeq, sub_smul]
      abel
    obtain ⟨ta, hta⟩ := hline a (left_mem_affineSpan_pair ℝ a b)
    obtain ⟨tb, htb⟩ := hline b (right_mem_affineSpan_pair ℝ a b)
    obtain ⟨tc, htc⟩ := hline c hcL
    have hinj : ∀ {x y : P} {tx ty : ℝ},
        (x -ᵥ p : V) = A + tx • e → (y -ᵥ p : V) = A + ty • e →
        x ≠ y → tx ≠ ty := by
      intro x y tx ty hx hy hxy htxy
      refine hxy (vsub_left_cancel (p := p) ?_)
      rw [hx, hy, htxy]
    have h_ab : ta ≠ tb := hinj hta htb hab
    have h_ac : ta ≠ tc := hinj hta htc (Ne.symm hca)
    have h_bc : tb ≠ tc := hinj htb htc (Ne.symm hcb)
    obtain ⟨x, y, hx, hy, hxy, hy0, hs0, hs1⟩ :=
      Pigeonhole.three h_ab h_ac h_bc
    have hpt : ∀ t : ℝ, (t = ta ∨ t = tb ∨ t = tc) →
        ∃ w ∈ S, (w -ᵥ p : V) = A + t • e := by
      rintro t (rfl | rfl | rfl)
      · exact ⟨a, haS, hta⟩
      · exact ⟨b, hbS, htb⟩
      · exact ⟨c, hcS, htc⟩
    obtain ⟨u, huS, hu⟩ := hpt x hx
    obtain ⟨v, hvS, hv⟩ := hpt y hy
    have hkelly : ‖perp (A + y • e) (A + (x / y * y) • e)‖ < ‖A‖ :=
      kelly hA he hy0 hAperp hs0 hs1
    rw [div_mul_cancel₀ _ hy0] at hkelly
    have hdist : SylvesterGallai.distToLine (V := V) u p v =
        ‖perp (A + y • e) (A + x • e)‖ := by
      rw [SylvesterGallai.distToLine, ← hu, ← hv]
    have hpv : p ≠ v := by
      intro h
      have h0 : A + y • e = 0 := by rw [← hv, ← h, vsub_self]
      have hz0 : ⟪A, A + y • e⟫ = (0 : ℝ) := by rw [h0, inner_zero_right]
      rw [inner_add_right, real_inner_smul_right, hAperp, mul_zero, add_zero,
        real_inner_self_eq_norm_sq] at hz0
      have : ‖A‖ = 0 := by nlinarith [norm_nonneg A]
      exact hA (norm_eq_zero.mp this)
    have huv : u ∉ SylvesterGallai.lineThrough (V := V) p v := by
      rw [SylvesterGallai.mem_lineThrough_iff (V := V), hu, hv]
      exact not_mem_line hA he hAperp hxy
    have hnew : (u, p, v) ∈ T := ⟨huS, hpS, hvS, hpv, huv⟩
    have hle := hmin (u, p, v) hnew
    simp only at hle
    rw [hdist] at hle
    rw [hAnorm] at hkelly
    linarith
  refine ⟨p, hpS, a, haS, b, hbS, hab, hpL, hord, ?_⟩
  intro q hq c hc d hd hcd hqL
  exact hmin (q, c, d) ⟨hq, hc, hd, hcd, hqL⟩

/-! Concrete vertical scaling. -/

abbrev Point := EuclideanSpace ℝ (Fin 2)

noncomputable def scaleYEquiv (M : ℝ) (hM : M ≠ 0) : Point ≃ₗ[ℝ] Point where
  toFun z := WithLp.toLp 2 fun i => if i = 0 then z i else M * z i
  invFun z := WithLp.toLp 2 fun i => if i = 0 then z i else z i / M
  left_inv z := by
    apply WithLp.ofLp_injective
    funext i
    fin_cases i <;> simp [hM]
  right_inv z := by
    apply WithLp.ofLp_injective
    funext i
    fin_cases i
    · simp
    · simp
      field_simp
  map_add' x y := by
    apply WithLp.ofLp_injective
    funext i
    fin_cases i <;> simp [mul_add]
  map_smul' c x := by
    apply WithLp.ofLp_injective
    funext i
    fin_cases i <;> simp <;> ring

lemma scaleY_fst (M : ℝ) (hM : M ≠ 0) (z : Point) :
    scaleYEquiv M hM z 0 = z 0 := by simp [scaleYEquiv]

lemma scaleY_snd (M : ℝ) (hM : M ≠ 0) (z : Point) :
    scaleYEquiv M hM z 1 = M * z 1 := by simp [scaleYEquiv]

lemma lineThrough_scaleY_iff (M : ℝ) (hM : M ≠ 0) {p a b : Point} :
    scaleYEquiv M hM p ∈
        SylvesterGallai.lineThrough (V := Point) (scaleYEquiv M hM a) (scaleYEquiv M hM b) ↔
      p ∈ SylvesterGallai.lineThrough (V := Point) a b := by
  rw [SylvesterGallai.mem_lineThrough_iff, SylvesterGallai.mem_lineThrough_iff]
  constructor
  · rintro ⟨c, hc⟩
    refine ⟨c, ?_⟩
    apply (scaleYEquiv M hM).injective
    simpa using hc
  · rintro ⟨c, hc⟩
    refine ⟨c, ?_⟩
    simpa using congrArg (scaleYEquiv M hM) hc

lemma not_collinear_scaleY_image (M : ℝ) (hM : M ≠ 0) {S : Set Point}
    (hncol : ¬ Collinear ℝ S) :
    ¬ Collinear ℝ (scaleYEquiv M hM '' S) := by
  intro himg
  rw [collinear_iff_exists_forall_eq_smul_vadd] at himg
  rw [collinear_iff_exists_forall_eq_smul_vadd] at hncol
  apply hncol
  rcases himg with ⟨a, v, hv⟩
  refine ⟨(scaleYEquiv M hM).symm a, (scaleYEquiv M hM).symm v, ?_⟩
  intro p hp
  obtain ⟨c, hc⟩ := hv (scaleYEquiv M hM p) ⟨p, hp, rfl⟩
  refine ⟨c, ?_⟩
  apply (scaleYEquiv M hM).injective
  simpa using hc

lemma ordinaryLine_scaleY_iff (M : ℝ) (hM : M ≠ 0) {S : Set Point} {a b : Point} :
    SylvesterGallai.IsOrdinaryLine (V := Point) (scaleYEquiv M hM '' S)
        (scaleYEquiv M hM a) (scaleYEquiv M hM b) ↔
      SylvesterGallai.IsOrdinaryLine (V := Point) S a b := by
  constructor
  · rintro ⟨haI, hbI, hab, hline⟩
    rcases haI with ⟨a', ha, hea⟩
    rcases hbI with ⟨b', hb, heb⟩
    have hea' : a' = a := (scaleYEquiv M hM).injective hea
    have heb' : b' = b := (scaleYEquiv M hM).injective heb
    subst a'; subst b'
    refine ⟨ha, hb, fun h ↦ hab (congrArg (scaleYEquiv M hM) h), ?_⟩
    intro c hcS hcL
    have hcL' := (lineThrough_scaleY_iff M hM).mpr hcL
    rcases hline (scaleYEquiv M hM c) ⟨c, hcS, rfl⟩ hcL' with hca | hcb
    · exact Or.inl ((scaleYEquiv M hM).injective hca)
    · exact Or.inr ((scaleYEquiv M hM).injective hcb)
  · rintro ⟨ha, hb, hab, hline⟩
    refine ⟨⟨a, ha, rfl⟩, ⟨b, hb, rfl⟩,
      fun h ↦ hab ((scaleYEquiv M hM).injective h), ?_⟩
    rintro _ ⟨c, hcS, rfl⟩ hcL
    have hcL' := (lineThrough_scaleY_iff M hM).mp hcL
    rcases hline c hcS hcL' with rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr rfl

lemma norm_perp_le_norm {W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℝ W]
    {w : W} (hw : w ≠ 0) (z : W) : ‖perp w z‖ ≤ ‖z‖ := by
  have hs := norm_perp_sq hw z
  have hsub : 0 ≤ ⟪z, w⟫ ^ 2 / ‖w‖ ^ 2 := by positivity
  have hsq : ‖perp w z‖ ^ 2 ≤ ‖z‖ ^ 2 := by linarith
  nlinarith [norm_nonneg (perp w z), norm_nonneg z]

lemma perp_sub_smul_self {W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℝ W]
    {w z : W} (hw : w ≠ 0) (c : ℝ) : perp w (z - c • w) = perp w z := by
  rw [sub_eq_add_neg, ← neg_smul, perp_add, perp_smul, perp_self hw, smul_zero, add_zero]

/-- A fixed nonhorizontal point--line configuration has uniformly bounded distance
under vertical scaling. -/
lemma dist_scaleY_le_intercept (M : ℝ) (hM : M ≠ 0) {q a b : Point}
    (hy : a 1 ≠ b 1) :
    SylvesterGallai.distToLine (V := Point) (scaleYEquiv M hM q)
        (scaleYEquiv M hM a) (scaleYEquiv M hM b) ≤
      |(q 0 - a 0) - ((q 1 - a 1) / (b 1 - a 1)) * (b 0 - a 0)| := by
  let E := scaleYEquiv M hM
  let c : ℝ := (q 1 - a 1) / (b 1 - a 1)
  let w : Point := E b - E a
  let z : Point := E q - E a
  have hab : a ≠ b := fun h ↦ hy (congrFun (congrArg WithLp.ofLp h) 1)
  have hw : w ≠ 0 := by
    exact sub_ne_zero.mpr (fun h ↦ hab (E.injective h).symm)
  have hz : z - c • w = E ((q - a) - c • (b - a)) := by
    simp [z, w, E, map_sub]
  rw [SylvesterGallai.distToLine]
  change ‖perp w z‖ ≤ _
  rw [← perp_sub_smul_self hw c]
  refine (norm_perp_le_norm hw (z - c • w)).trans_eq ?_
  rw [hz]
  rw [EuclideanSpace.norm_eq]
  simp only [Fin.sum_univ_two]
  have hcoord1 : E ((q - a) - c • (b - a)) 1 = 0 := by
    simp [E, scaleYEquiv, c]
    field_simp
    simp
  have hcoord0 : E ((q - a) - c • (b - a)) 0 =
      (q 0 - a 0) - ((q 1 - a 1) / (b 1 - a 1)) * (b 0 - a 0) := by
    simp [E, scaleYEquiv, c]
  rw [hcoord0, hcoord1]
  simp [Real.norm_eq_abs, Real.sqrt_sq_eq_abs]

/-- Exact distance to a horizontal line after vertical scaling. -/
lemma dist_scaleY_horizontal (M : ℝ) (hM : 0 < M) {q a b : Point}
    (hab : a ≠ b) (hy : a 1 = b 1) :
    SylvesterGallai.distToLine (V := Point) (scaleYEquiv M hM.ne' q)
        (scaleYEquiv M hM.ne' a) (scaleYEquiv M hM.ne' b) =
      M * |q 1 - a 1| := by
  have hx : b 0 - a 0 ≠ 0 := by
    intro hx0
    apply hab
    apply WithLp.ofLp_injective
    funext i
    fin_cases i
    · exact (sub_eq_zero.mp hx0).symm
    · exact hy
  rw [SylvesterGallai.distToLine]
  let w : Point := scaleYEquiv M hM.ne' b - scaleYEquiv M hM.ne' a
  let z : Point := scaleYEquiv M hM.ne' q - scaleYEquiv M hM.ne' a
  have hw0 : w 0 = b 0 - a 0 := by simp [w, scaleYEquiv]
  have hw1 : w 1 = 0 := by simp [w, scaleYEquiv, hy]
  have hz1 : z 1 = M * (q 1 - a 1) := by simp [z, scaleYEquiv]; ring
  have hinner : ⟪z, w⟫ = z 0 * w 0 := by
    rw [EuclideanSpace.inner_eq_star_dotProduct]
    simp [Fin.sum_univ_two, hw1, mul_comm]
  have hww : ⟪w, w⟫ = w 0 * w 0 := by
    rw [EuclideanSpace.inner_eq_star_dotProduct]
    simp [Fin.sum_univ_two, hw1]
  have hw0ne : w 0 ≠ 0 := by simpa [hw0] using hx
  have hperp0 : perp w z 0 = 0 := by
    simp only [perp]
    rw [hinner, hww]
    change z 0 - (z 0 * w 0 / (w 0 * w 0)) * w 0 = 0
    field_simp
    ring
  have hperp1 : perp w z 1 = M * (q 1 - a 1) := by
    simp only [perp]
    change z 1 - (⟪z, w⟫ / ⟪w, w⟫) * w 1 = _
    rw [hw1, mul_zero, sub_zero, hz1]
  change ‖perp w z‖ = _
  rw [EuclideanSpace.norm_eq]
  rw [Fin.sum_univ_two, hperp0, hperp1]
  simp [Real.norm_eq_abs, Real.sqrt_sq_eq_abs, abs_mul, abs_of_pos hM]

lemma mem_horizontal_line {p a b : Point} (hab : a ≠ b)
    (habY : a 1 = b 1) (hpaY : p 1 = a 1) :
    p ∈ SylvesterGallai.lineThrough (V := Point) a b := by
  rw [SylvesterGallai.mem_lineThrough_iff]
  have hx : b 0 - a 0 ≠ 0 := by
    intro hx0
    apply hab
    apply WithLp.ofLp_injective
    funext i
    fin_cases i
    · exact (sub_eq_zero.mp hx0).symm
    · exact habY
  refine ⟨(p 0 - a 0) / (b 0 - a 0), ?_⟩
  apply WithLp.ofLp_injective
  funext i
  fin_cases i
  · simp
    field_simp
  · simp [hpaY, habY]

/-- Directional Sylvester--Gallai for the horizontal point at infinity: a finite
noncollinear set has an ordinary line whose endpoints have different second
coordinates. -/
theorem exists_ordinary_nonhorizontal (S : Set Point) (hfin : S.Finite)
    (hncol : ¬ Collinear ℝ S) :
    ∃ a ∈ S, ∃ b ∈ S,
      SylvesterGallai.IsOrdinaryLine (V := Point) S a b ∧ a 1 ≠ b 1 := by
  have hyPair : ∃ a ∈ S, ∃ b ∈ S, a 1 ≠ b 1 := by
    by_contra h
    push Not at h
    obtain ⟨a, ha, b, hb, hab⟩ :=
      SylvesterGallai.exists_ne_of_not_collinear (V := Point) hncol
    apply hncol
    rw [collinear_iff_exists_forall_eq_smul_vadd]
    let ex : Point := WithLp.toLp 2 ![1, 0]
    refine ⟨a, ex, ?_⟩
    intro p hp
    refine ⟨p 0 - a 0, ?_⟩
    apply WithLp.ofLp_injective
    funext i
    fin_cases i
    · simp [ex]
    · have hY := h p hp a ha
      simp [ex, hY]
  obtain ⟨a, ha, b, hb, hyab⟩ := hyPair
  have hab : a ≠ b := fun h ↦ hyab (congrFun (congrArg WithLp.ofLp h) 1)
  have hoff : ∃ q ∈ S, q ∉ SylvesterGallai.lineThrough (V := Point) a b := by
    by_contra h
    push Not at h
    exact hncol (SylvesterGallai.collinear_of_subset_line (V := Point) h)
  obtain ⟨q, hq, hqoff⟩ := hoff
  set G : Set (Point × Point) :=
    {uv | uv.1 ∈ S ∧ uv.2 ∈ S ∧ uv.1 1 ≠ uv.2 1} with hGdef
  have hGfin : G.Finite := by
    refine Set.Finite.subset (hfin.prod hfin) ?_
    rintro ⟨u, v⟩ ⟨hu, hv, -⟩
    exact ⟨hu, hv⟩
  have hGne : G.Nonempty := ⟨(a, b), ha, hb, hyab⟩
  obtain ⟨⟨u, v⟩, huvG, hgapMin⟩ :=
    Set.exists_min_image G (fun uv => |uv.1 1 - uv.2 1|) hGfin hGne
  have huvY : u 1 ≠ v 1 := huvG.2.2
  let δ : ℝ := |u 1 - v 1|
  have hδ : 0 < δ := abs_pos.mpr (sub_ne_zero.mpr huvY)
  let K : ℝ :=
    |(q 0 - a 0) - ((q 1 - a 1) / (b 1 - a 1)) * (b 0 - a 0)|
  have hK : 0 ≤ K := abs_nonneg _
  let M : ℝ := (K + 1) / δ
  have hM : 0 < M := by
    dsimp [M]
    positivity
  let E := scaleYEquiv M hM.ne'
  let T : Set Point := E '' S
  have hTfin : T.Finite := hfin.image E
  have hTncol : ¬ Collinear ℝ T := not_collinear_scaleY_image M hM.ne' hncol
  obtain ⟨p', hp'T, a', ha'T, b', hb'T, ha'b', hp'off, hord, hminimal⟩ :=
    exists_minimal_ordinary_line T hTfin hTncol
  rcases hp'T with ⟨p, hpS, rfl⟩
  rcases ha'T with ⟨a₀, ha₀S, rfl⟩
  rcases hb'T with ⟨b₀, hb₀S, rfl⟩
  have ha₀b₀ : a₀ ≠ b₀ := fun h ↦ ha'b' (congrArg E h)
  have hnonhorizontal : a₀ 1 ≠ b₀ 1 := by
    intro hhorizontal
    have hpY : p 1 ≠ a₀ 1 := by
      intro hpa
      apply hp'off
      rw [lineThrough_scaleY_iff M hM.ne']
      exact mem_horizontal_line ha₀b₀ hhorizontal hpa
    have hpGap : (p, a₀) ∈ G := ⟨hpS, ha₀S, hpY⟩
    have hδle : δ ≤ |p 1 - a₀ 1| := hgapMin (p, a₀) hpGap
    have hlarge : K < M * |p 1 - a₀ 1| := by
      have hMδ : M * δ = K + 1 := by
        dsimp [M]
        field_simp
      have := mul_le_mul_of_nonneg_left hδle hM.le
      rw [hMδ] at this
      linarith
    have hfixedOff : E q ∉ SylvesterGallai.lineThrough (V := Point) (E a) (E b) := by
      rwa [lineThrough_scaleY_iff M hM.ne']
    have hminFixed := hminimal (E q) ⟨q, hq, rfl⟩ (E a) ⟨a, ha, rfl⟩
      (E b) ⟨b, hb, rfl⟩ (fun h ↦ hab (E.injective h)) hfixedOff
    have hfixedBound :
        SylvesterGallai.distToLine (V := Point) (E q) (E a) (E b) ≤ K := by
      exact dist_scaleY_le_intercept M hM.ne' hyab
    have hbase :
        SylvesterGallai.distToLine (V := Point) (E p) (E a₀) (E b₀) =
          M * |p 1 - a₀ 1| :=
      dist_scaleY_horizontal M hM ha₀b₀ hhorizontal
    rw [hbase] at hminFixed
    linarith
  refine ⟨a₀, ha₀S, b₀, hb₀S, ?_, hnonhorizontal⟩
  exact (ordinaryLine_scaleY_iff M hM.ne').mp hord

/-! A finite projective chart sending a prescribed external point to horizontal infinity. -/

abbrev PairPoint := Point

def pairDet (a b c : PairPoint) : ℝ :=
  (b 0 - a 0) * (c 1 - a 1) - (b 1 - a 1) * (c 0 - a 0)

def euclideanDet (a b c : Point) : ℝ :=
  (b 0 - a 0) * (c 1 - a 1) - (b 1 - a 1) * (c 0 - a 0)

def chartX (p : PairPoint) (t : ℝ) (q : PairPoint) : ℝ :=
  q 0 - p 0 + t * (q 1 - p 1)

def chartY (p q : PairPoint) : ℝ := q 1 - p 1

noncomputable def projectiveChart (p : PairPoint) (t : ℝ) (q : PairPoint) : Point :=
  WithLp.toLp 2 ![1 / chartX p t q, chartY p q / chartX p t q]

@[simp] lemma projectiveChart_apply_zero (p : PairPoint) (t : ℝ) (q : PairPoint) :
    projectiveChart p t q 0 = 1 / chartX p t q := by simp [projectiveChart]

@[simp] lemma projectiveChart_apply_one (p : PairPoint) (t : ℝ) (q : PairPoint) :
    projectiveChart p t q 1 = chartY p q / chartX p t q := by simp [projectiveChart]

lemma pairDet_eq_chartXY_det (p a b : PairPoint) :
    pairDet p a b = chartX p 0 a * chartY p b - chartY p a * chartX p 0 b := by
  simp [pairDet, chartX, chartY]

lemma pairDet_eq_sheared_det (p : PairPoint) (t : ℝ) (a b : PairPoint) :
    pairDet p a b = chartX p t a * chartY p b - chartY p a * chartX p t b := by
  simp [pairDet, chartX, chartY]
  ring

/-- The affine determinant in the projective chart is the old determinant divided
by the three homogeneous denominators. -/
lemma projectiveChart_det (p : PairPoint) (t : ℝ) {a b c : PairPoint}
    (ha : chartX p t a ≠ 0) (hb : chartX p t b ≠ 0) (hc : chartX p t c ≠ 0) :
    euclideanDet (projectiveChart p t a) (projectiveChart p t b)
        (projectiveChart p t c) =
      -pairDet a b c / (chartX p t a * chartX p t b * chartX p t c) := by
  simp only [euclideanDet, projectiveChart_apply_zero, projectiveChart_apply_one]
  field_simp [ha, hb, hc]
  simp [pairDet, chartX, chartY]
  ring

lemma projectiveChart_injective_on (p : PairPoint) (t : ℝ) {a b : PairPoint}
    (ha : chartX p t a ≠ 0) (hb : chartX p t b ≠ 0)
    (h : projectiveChart p t a = projectiveChart p t b) : a = b := by
  have h0 := congrFun (congrArg WithLp.ofLp h) 0
  have h1 := congrFun (congrArg WithLp.ofLp h) 1
  simp only [projectiveChart_apply_zero] at h0
  simp only [projectiveChart_apply_one] at h1
  have hX : chartX p t a = chartX p t b := by
    field_simp at h0
    exact h0.symm
  have hY : chartY p a = chartY p b := by
    rw [hX] at h1
    exact (div_left_inj' hb).mp h1
  have hx : a 0 = b 0 := by
    simp only [chartX, chartY] at hX hY
    have hcoord : a 0 - p 0 = b 0 - p 0 := by
      linear_combination hX - t * hY
    linarith
  have hy : a 1 = b 1 := by
    simp only [chartY] at hY
    linarith
  apply WithLp.ofLp_injective
  exact funext (Fin.forall_fin_two.2 ⟨hx, hy⟩)

lemma mem_lineThrough_iff_euclideanDet_zero {a b c : Point} (hab : a ≠ b) :
    c ∈ SylvesterGallai.lineThrough (V := Point) a b ↔ euclideanDet a b c = 0 := by
  rw [SylvesterGallai.mem_lineThrough_iff]
  constructor
  · rintro ⟨s, hs⟩
    have h0 := congrFun (congrArg WithLp.ofLp hs) 0
    have h1 := congrFun (congrArg WithLp.ofLp hs) 1
    change c 0 - a 0 = s * (b 0 - a 0) at h0
    change c 1 - a 1 = s * (b 1 - a 1) at h1
    unfold euclideanDet
    rw [h0, h1]
    ring
  · intro hdet
    by_cases hx : b 0 - a 0 = 0
    · have hy : b 1 - a 1 ≠ 0 := by
        intro hy
        apply hab
        apply WithLp.ofLp_injective
        funext i
        fin_cases i
        · exact (sub_eq_zero.mp hx).symm
        · exact (sub_eq_zero.mp hy).symm
      refine ⟨(c 1 - a 1) / (b 1 - a 1), ?_⟩
      apply WithLp.ofLp_injective
      funext i
      fin_cases i
      · change c 0 - a 0 = ((c 1 - a 1) / (b 1 - a 1)) * (b 0 - a 0)
        unfold euclideanDet at hdet
        rw [hx, mul_zero]
        rw [hx, zero_mul, zero_sub] at hdet
        have hprod : (b 1 - a 1) * (c 0 - a 0) = 0 := neg_eq_zero.mp hdet
        exact (mul_eq_zero.mp hprod).resolve_left hy
      · change c 1 - a 1 = ((c 1 - a 1) / (b 1 - a 1)) * (b 1 - a 1)
        field_simp
    · refine ⟨(c 0 - a 0) / (b 0 - a 0), ?_⟩
      apply WithLp.ofLp_injective
      funext i
      fin_cases i
      · change c 0 - a 0 = ((c 0 - a 0) / (b 0 - a 0)) * (b 0 - a 0)
        field_simp
      · change c 1 - a 1 = ((c 0 - a 0) / (b 0 - a 0)) * (b 1 - a 1)
        field_simp
        unfold euclideanDet at hdet
        nlinarith

/-- A finite set avoids some projective denominator through an external point. -/
lemma exists_chart_parameter (S : Finset PairPoint) {p : PairPoint} (hp : p ∉ S) :
    ∃ t : ℝ, ∀ q ∈ S, chartX p t q ≠ 0 := by
  let bad : Finset ℝ := S.image fun q ↦ -(q 0 - p 0) / (q 1 - p 1)
  obtain ⟨t, ht⟩ := (bad.finite_toSet).exists_notMem
  refine ⟨t, ?_⟩
  intro q hq hzero
  by_cases hy : q 1 - p 1 = 0
  · have hx : q 0 - p 0 = 0 := by
      unfold chartX at hzero
      rw [hy, mul_zero, add_zero] at hzero
      exact hzero
    apply hp
    have : q = p := by
      apply WithLp.ofLp_injective
      funext i
      fin_cases i
      · exact (sub_eq_zero.mp hx)
      · exact (sub_eq_zero.mp hy)
    simpa [this] using hq
  · apply ht
    rw [Finset.mem_coe, Finset.mem_image]
    refine ⟨q, hq, ?_⟩
    dsimp [chartX] at hzero
    symm
    apply (eq_div_iff hy).2
    nlinarith

def IsOrdinaryPairSet (S : Set PairPoint) (a b : PairPoint) : Prop :=
  a ∈ S ∧ b ∈ S ∧ a ≠ b ∧
    ∀ c ∈ S, pairDet a b c = 0 → c = a ∨ c = b

def IsNoncollinearSet (S : Set PairPoint) : Prop :=
  ∃ a ∈ S, ∃ b ∈ S, ∃ c ∈ S, pairDet a b c ≠ 0

/-- Unconditional avoiding-ordinary-line theorem in the determinant language used by
Erdős 735. -/
theorem exists_ordinary_avoiding_external_set (S : Finset PairPoint) {p : PairPoint}
    (hp : p ∉ S) (hncol : IsNoncollinearSet (S : Set PairPoint)) :
    ∃ a ∈ S, ∃ b ∈ S, IsOrdinaryPairSet (S : Set PairPoint) a b ∧ pairDet a b p ≠ 0 := by
  obtain ⟨t, ht⟩ := exists_chart_parameter S hp
  let F : PairPoint → Point := projectiveChart p t
  let T : Set Point := F '' (S : Set PairPoint)
  have hTfin : T.Finite := S.finite_toSet.image F
  rcases hncol with ⟨a, ha, b, hb, c, hc, habc⟩
  have haX := ht a ha
  have hbX := ht b hb
  have hcX := ht c hc
  have hab : a ≠ b := by
    intro h
    subst b
    exact habc (by simp [pairDet])
  have hFab : F a ≠ F b := by
    intro h
    exact hab (projectiveChart_injective_on p t haX hbX h)
  have hTncol : ¬ Collinear ℝ T := by
    intro hcol
    have hcLine := hcol.mem_affineSpan_of_mem_of_ne
      (show F a ∈ T from ⟨a, ha, rfl⟩) (show F b ∈ T from ⟨b, hb, rfl⟩)
      (show F c ∈ T from ⟨c, hc, rfl⟩) hFab
    have hdetChart := (mem_lineThrough_iff_euclideanDet_zero hFab).mp hcLine
    rw [projectiveChart_det p t haX hbX hcX] at hdetChart
    have hden : chartX p t a * chartX p t b * chartX p t c ≠ 0 := by
      exact mul_ne_zero (mul_ne_zero haX hbX) hcX
    have hnum : -pairDet a b c = 0 :=
      (div_eq_zero_iff.mp hdetChart).resolve_right hden
    exact habc (neg_eq_zero.mp hnum)
  obtain ⟨A, hAT, B, hBT, hord, hABY⟩ := exists_ordinary_nonhorizontal T hTfin hTncol
  rcases hAT with ⟨a₀, ha₀, rfl⟩
  rcases hBT with ⟨b₀, hb₀, rfl⟩
  have ha₀X := ht a₀ ha₀
  have hb₀X := ht b₀ hb₀
  have ha₀b₀ : a₀ ≠ b₀ := by
    intro h
    subst b₀
    exact hord.2.2.1 rfl
  have havoid : pairDet a₀ b₀ p ≠ 0 := by
    intro hdet
    have hslope : chartY p a₀ / chartX p t a₀ = chartY p b₀ / chartX p t b₀ := by
      apply (div_eq_div_iff ha₀X hb₀X).2
      have hdet' : pairDet p a₀ b₀ = 0 := by
        simp only [pairDet] at hdet ⊢
        nlinarith
      rw [pairDet_eq_sheared_det p t] at hdet'
      nlinarith
    exact hABY (by simpa [F, projectiveChart] using hslope)
  refine ⟨a₀, ha₀, b₀, hb₀, ?_, havoid⟩
  refine ⟨ha₀, hb₀, ha₀b₀, ?_⟩
  intro c₀ hc₀ hdet
  have hc₀X := ht c₀ hc₀
  have hchartDet : euclideanDet (F a₀) (F b₀) (F c₀) = 0 := by
    rw [projectiveChart_det p t ha₀X hb₀X hc₀X]
    simp [hdet]
  have hcLine := (mem_lineThrough_iff_euclideanDet_zero hord.2.2.1).mpr hchartDet
  rcases hord.2.2.2 (F c₀) ⟨c₀, hc₀, rfl⟩ hcLine with hca | hcb
  · exact Or.inl (projectiveChart_injective_on p t hc₀X ha₀X hca)
  · exact Or.inr (projectiveChart_injective_on p t hc₀X hb₀X hcb)

lemma isNoncollinearSet_of_not_collinear (S : Finset Point)
    (hncol : ¬ Collinear ℝ (S : Set Point)) : IsNoncollinearSet (S : Set PairPoint) := by
  obtain ⟨a, ha, b, hb, hab⟩ :=
    SylvesterGallai.exists_ne_of_not_collinear (V := Point) hncol
  by_contra h
  have hall : ∀ a ∈ S, ∀ b ∈ S, ∀ c ∈ S, pairDet a b c = 0 := by
    intro x hx y hy z hz
    by_contra hdet
    exact h ⟨x, hx, y, hy, z, hz, hdet⟩
  apply hncol
  refine SylvesterGallai.collinear_of_subset_line (V := Point) (a := a) (b := b) ?_
  intro c hc
  rw [mem_lineThrough_iff_euclideanDet_zero hab]
  exact hall a ha b hb c hc

/-- Production-facing form: the ordinary line is returned as an exact determinant
fiber, and its line avoids the prescribed external point. -/
theorem exists_ordinary_filter_avoiding_external (S : Finset Point) {p : Point}
    (hp : p ∉ S) (hncol : ¬ Collinear ℝ (S : Set Point)) :
    ∃ a ∈ S, ∃ b ∈ S, a ≠ b ∧
      S.filter (fun c ↦ euclideanDet a b c = 0) = {a, b} ∧
      euclideanDet a b p ≠ 0 := by
  obtain ⟨a, ha, b, hb, hord, havoid⟩ :=
    exists_ordinary_avoiding_external_set S hp
      (isNoncollinearSet_of_not_collinear S hncol)
  refine ⟨a, ha, b, hb, hord.2.2.1, ?_, havoid⟩
  ext c
  constructor
  · intro hc
    have hcS := (Finset.mem_filter.mp hc).1
    have hdet := (Finset.mem_filter.mp hc).2
    simpa only [Finset.mem_insert, Finset.mem_singleton] using hord.2.2.2 c hcS hdet
  · intro hc
    simp only [Finset.mem_insert, Finset.mem_singleton] at hc
    rcases hc with rfl | rfl
    · exact Finset.mem_filter.mpr ⟨ha, by simp [euclideanDet]⟩
    · exact Finset.mem_filter.mpr ⟨hb, by simp [euclideanDet]; ring⟩

end Erdos735DirectionalKelly
