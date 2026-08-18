import ErdosProblems.Erdos1118

open MeasureTheory Set Filter Laplacian InnerProductSpace
open scoped ENNReal Topology Pointwise InnerProductSpace
open Erdos1118

noncomputable def test_logPolarPoint (x θ : ℝ) : ℂ :=
  (x : ℂ) + (θ : ℂ) * Complex.I

theorem test_exp_logPolarPoint (x θ : ℝ) :
    Complex.exp (test_logPolarPoint x θ) = polarPoint (Real.exp x) θ := by
  simp [test_logPolarPoint, polarPoint, Complex.exp_add, Complex.exp_mul_I]

noncomputable def test_logPolarSlice (f : ℂ → ℂ) (x θ : ℝ) : ℝ :=
  logPolarLevel f (test_logPolarPoint x θ)

theorem test_logPolarSlice_pos_iff (f : ℂ → ℂ) (x θ : ℝ) :
    0 < test_logPolarSlice f x θ ↔
      polarPoint (Real.exp x) θ ∈ exceptionalSet f 1 := by
  rw [test_logPolarSlice, logPolarLevel_pos_iff, test_exp_logPolarPoint]
  rfl

theorem test_positive_logPolarSlice_set (f : ℂ → ℂ) (x : ℝ) :
    {θ | θ ∈ Set.Ioo (-Real.pi) Real.pi ∧ 0 < test_logPolarSlice f x θ} =
      angularSection (exceptionalSet f 1) (Real.exp x) := by
  ext θ
  simp only [angularSection, Set.mem_setOf_eq, and_congr_right_iff]
  intro _
  exact test_logPolarSlice_pos_iff f x θ

theorem test_logPolarSlice_periodic (f : ℂ → ℂ) (x θ : ℝ) :
    test_logPolarSlice f x (θ + 2 * Real.pi) = test_logPolarSlice f x θ := by
  change harmonicLogarithmicLevel f
      (Complex.exp (test_logPolarPoint x (θ + 2 * Real.pi))) =
    harmonicLogarithmicLevel f (Complex.exp (test_logPolarPoint x θ))
  rw [test_exp_logPolarPoint, test_exp_logPolarPoint]
  apply congrArg
  simp [polarPoint]

theorem test_contDiff_logPolarSlice_fst {f : ℂ → ℂ} (hf : IsEntire f) (θ : ℝ) :
    ContDiff ℝ 2 (fun x : ℝ ↦ test_logPolarSlice f x θ) := by
  have hin : ContDiff ℝ 2 (fun x : ℝ ↦ (θ : ℂ) * Complex.I + x • (1 : ℂ)) :=
    contDiff_const.add (contDiff_id.smul_const (1 : ℂ))
  have h := (contDiff_logPolarLevel hf).comp hin
  convert h using 1
  funext x
  simp [test_logPolarSlice, test_logPolarPoint, add_comm, smul_eq_mul]

theorem test_contDiff_logPolarSlice_snd {f : ℂ → ℂ} (hf : IsEntire f) (x : ℝ) :
    ContDiff ℝ 2 (test_logPolarSlice f x) := by
  have hin : ContDiff ℝ 2 (fun θ : ℝ ↦ (x : ℂ) + θ • Complex.I) :=
    contDiff_const.add (contDiff_id.smul_const Complex.I)
  exact (contDiff_logPolarLevel hf).comp hin

theorem test_iteratedDeriv_two_affine_line_at
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {F : E → ℝ} {x v : E} {t : ℝ} (hF : ContDiffAt ℝ 2 F (x + t • v)) :
    iteratedDeriv 2 (fun s : ℝ ↦ F (x + s • v)) t =
      iteratedFDeriv ℝ 2 F (x + t • v) ![v, v] := by
  let q : ℝ → ℝ := fun s ↦ F (x + s • v)
  have hline : Tendsto (fun s : ℝ ↦ x + s • v) (nhds t) (nhds (x + t • v)) :=
    (show Continuous (fun s : ℝ ↦ x + s • v) by fun_prop).tendsto t
  have hev : ∀ᶠ s : ℝ in nhds t, ContDiffAt ℝ 2 F (x + s • v) :=
    hline.eventually (hF.eventually (by norm_num))
  have hderiv : deriv q =ᶠ[nhds t]
      (fun s ↦ fderiv ℝ F (x + s • v) v) := by
    filter_upwards [hev] with s hs
    exact hs.differentiableAt two_ne_zero |>.deriv_comp_add_smul
  rw [show iteratedDeriv 2 q t = deriv (deriv q) t by
    rw [show (2 : ℕ) = 1 + 1 by norm_num, iteratedDeriv_succ, iteratedDeriv_one]]
  rw [hderiv.deriv_eq]
  have hF' : ContDiffAt ℝ ((1 : ℕ∞) + 1) F (x + t • v) := by
    convert hF using 1
    norm_num
  have hsecond := hF'.deriv_fderiv_add_smul (n := 1) (x := x) (y := v) (t := t)
  have hsecond' : deriv (fun s : ℝ ↦ fderiv ℝ F (x + s • v) v) t =
      iteratedFDeriv ℝ 2 F (x + t • v) (fun _ ↦ v) := by
    simpa only [iteratedFDeriv_one_apply, Nat.reduceAdd] using hsecond
  rw [hsecond']
  congr 1
  funext i
  fin_cases i <;> rfl

theorem test_logPolarSlice_second_derivatives_add {f : ℂ → ℂ}
    (hf : IsEntire f) (x θ : ℝ) :
    iteratedDeriv 2 (fun s : ℝ ↦ test_logPolarSlice f s θ) x +
        iteratedDeriv 2 (test_logPolarSlice f x) θ =
      Δ (logPolarLevel f) (test_logPolarPoint x θ) := by
  rw [congrFun (laplacian_eq_iteratedFDeriv_complexPlane (logPolarLevel f))
    (test_logPolarPoint x θ)]
  rw [show (fun s : ℝ ↦ test_logPolarSlice f s θ) =
      (fun s : ℝ ↦ logPolarLevel f ((θ : ℂ) * Complex.I + s • (1 : ℂ))) by
    funext s
    simp [test_logPolarSlice, test_logPolarPoint, add_comm]]
  rw [show test_logPolarSlice f x =
      (fun s : ℝ ↦ logPolarLevel f ((x : ℂ) + s • Complex.I)) by
    funext s
    simp [test_logPolarSlice, test_logPolarPoint]]
  have hx := test_iteratedDeriv_two_affine_line_at
    (F := logPolarLevel f) (x := (θ : ℂ) * Complex.I) (v := (1 : ℂ)) (t := x)
    (contDiff_logPolarLevel hf).contDiffAt
  have hx' : iteratedDeriv 2
      (fun s : ℝ ↦ logPolarLevel f ((θ : ℂ) * Complex.I + s • (1 : ℂ))) x =
      iteratedFDeriv ℝ 2 (logPolarLevel f) (test_logPolarPoint x θ) ![(1 : ℂ), 1] := by
    simpa [test_logPolarPoint, add_comm] using hx
  have hθ := test_iteratedDeriv_two_affine_line_at
    (F := logPolarLevel f) (x := (x : ℂ)) (v := Complex.I) (t := θ)
    (contDiff_logPolarLevel hf).contDiffAt
  have hθ' : iteratedDeriv 2
      (fun s : ℝ ↦ logPolarLevel f ((x : ℂ) + s • Complex.I)) θ =
      iteratedFDeriv ℝ 2 (logPolarLevel f) (test_logPolarPoint x θ)
        ![Complex.I, Complex.I] := by
    simpa [test_logPolarPoint] using hθ
  rw [hx', hθ']

theorem test_hasDerivAt_intervalIntegral_of_continuous_partial
    {F F' : ℝ → ℝ → ℝ} {a b x₀ : ℝ}
    (hF : Continuous (Function.uncurry F))
    (hF' : Continuous (Function.uncurry F'))
    (hdiff : ∀ x t, HasDerivAt (fun y ↦ F y t) (F' x t) x) :
    HasDerivAt (fun x ↦ ∫ t in a..b, F x t) (∫ t in a..b, F' x₀ t) x₀ := by
  let s : Set ℝ := Set.Ioo (x₀ - 1) (x₀ + 1)
  let K : Set (ℝ × ℝ) := Set.Icc (x₀ - 1) (x₀ + 1) ×ˢ Set.uIcc a b
  obtain ⟨C, hC⟩ := (isCompact_Icc.prod isCompact_uIcc).exists_bound_of_continuousOn
    hF'.continuousOn
  have hs : s ∈ nhds x₀ := by
    exact Ioo_mem_nhds (by linarith) (by linarith)
  have hF_meas : ∀ᶠ x in nhds x₀,
      AEStronglyMeasurable (F x) (volume.restrict (Set.uIoc a b)) := by
    filter_upwards with x
    exact (hF.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable.restrict
  have hF_int : IntervalIntegrable (F x₀) volume a b :=
    (hF.comp (continuous_const.prodMk continuous_id)).intervalIntegrable _ _
  have hF'_meas : AEStronglyMeasurable (F' x₀) (volume.restrict (Set.uIoc a b)) :=
    (hF'.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable.restrict
  have hbound : ∀ᵐ t ∂volume, t ∈ Set.uIoc a b →
      ∀ x ∈ s, ‖F' x t‖ ≤ C := by
    filter_upwards with t
    intro ht x hx
    apply hC (x, t)
    exact ⟨⟨hx.1.le, hx.2.le⟩, Set.uIoc_subset_uIcc ht⟩
  have hdiff' : ∀ᵐ t ∂volume, t ∈ Set.uIoc a b →
      ∀ x ∈ s, HasDerivAt (fun y ↦ F y t) (F' x t) x := by
    filter_upwards with t
    exact fun _ x _ ↦ hdiff x t
  exact (intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := F) (F' := F') (bound := fun _ ↦ C) hs hF_meas hF_int hF'_meas hbound
      intervalIntegrable_const hdiff').2

noncomputable def test_squareEnergy (U : ℝ → ℝ → ℝ) (a b x : ℝ) : ℝ :=
  ∫ t in a..b, U x t ^ 2

theorem test_hasDerivAt_squareEnergy {U Ux : ℝ → ℝ → ℝ}
    (hU : Continuous (Function.uncurry U))
    (hUx : Continuous (Function.uncurry Ux))
    (hdiff : ∀ x t, HasDerivAt (fun y ↦ U y t) (Ux x t) x)
    (a b x : ℝ) :
    HasDerivAt (test_squareEnergy U a b)
      (∫ t in a..b, 2 * (U x t * Ux x t)) x := by
  apply test_hasDerivAt_intervalIntegral_of_continuous_partial
      (F := fun y t ↦ U y t ^ 2)
      (F' := fun y t ↦ 2 * (U y t * Ux y t))
  · exact hU.pow 2
  · exact continuous_const.mul (hU.mul hUx)
  · intro y t
    have hu := hdiff y t
    convert hu.pow 2 using 1 <;>
      first | with_reducible_and_instances rfl | ring

theorem test_iteratedDeriv_two_squareEnergy {U Ux Uxx : ℝ → ℝ → ℝ}
    (hU : Continuous (Function.uncurry U))
    (hUx : Continuous (Function.uncurry Ux))
    (hUxx : Continuous (Function.uncurry Uxx))
    (hdiff : ∀ x t, HasDerivAt (fun y ↦ U y t) (Ux x t) x)
    (hdiffx : ∀ x t, HasDerivAt (fun y ↦ Ux y t) (Uxx x t) x)
    (a b x : ℝ) :
    iteratedDeriv 2 (test_squareEnergy U a b) x =
      ∫ t in a..b, 2 * (Ux x t ^ 2 + U x t * Uxx x t) := by
  rw [show iteratedDeriv 2 (test_squareEnergy U a b) x =
      deriv (deriv (test_squareEnergy U a b)) x by
    rw [show (2 : ℕ) = 1 + 1 by norm_num, iteratedDeriv_succ, iteratedDeriv_one]]
  rw [show deriv (test_squareEnergy U a b) =
      (fun y ↦ ∫ t in a..b, 2 * (U y t * Ux y t)) from
    funext fun y ↦ (test_hasDerivAt_squareEnergy hU hUx hdiff a b y).deriv]
  apply HasDerivAt.deriv
  apply test_hasDerivAt_intervalIntegral_of_continuous_partial
      (F := fun y t ↦ 2 * (U y t * Ux y t))
      (F' := fun y t ↦ 2 * (Ux y t ^ 2 + U y t * Uxx y t))
  · exact continuous_const.mul (hU.mul hUx)
  · exact continuous_const.mul ((hUx.pow 2).add (hU.mul hUxx))
  · intro y t
    simpa [pow_two] using ((hdiff y t).mul (hdiffx y t)).const_mul (2 : ℝ)

theorem test_intervalIntegral_mul_second_eq_neg_sq
    {u u' u'' : ℝ → ℝ} {a b : ℝ}
    (hu : ∀ t, HasDerivAt u (u' t) t)
    (hu' : ∀ t, HasDerivAt u' (u'' t) t)
    (hu'cont : Continuous u') (hu''cont : Continuous u'')
    (hboundary : u b * u' b = u a * u' a) :
    (∫ t in a..b, u t * u'' t) = -(∫ t in a..b, u' t ^ 2) := by
  have h := intervalIntegral.integral_mul_deriv_eq_deriv_mul
    (a := a) (b := b) (u := u) (v := u') (u' := u') (v' := u'')
    (fun t _ ↦ hu t) (fun t _ ↦ hu' t)
    (hu'cont.intervalIntegrable _ _) (hu''cont.intervalIntegrable _ _)
  rw [hboundary, sub_self, zero_sub] at h
  simpa only [pow_two] using h

theorem test_squareEnergy_second_deriv_ge_dirichlet
    {U Ux Uxx Ut Utt : ℝ → ℝ → ℝ}
    (hU : Continuous (Function.uncurry U))
    (hUx : Continuous (Function.uncurry Ux))
    (hUxx : Continuous (Function.uncurry Uxx))
    (hUt : Continuous (Function.uncurry Ut))
    (hUtt : Continuous (Function.uncurry Utt))
    (hdiff : ∀ x t, HasDerivAt (fun y ↦ U y t) (Ux x t) x)
    (hdiffx : ∀ x t, HasDerivAt (fun y ↦ Ux y t) (Uxx x t) x)
    (hdifft : ∀ x t, HasDerivAt (U x) (Ut x t) t)
    (hdifftt : ∀ x t, HasDerivAt (Ut x) (Utt x t) t)
    (hU_nonneg : ∀ x t, 0 ≤ U x t)
    (hsubharmonic : ∀ x t, 0 ≤ Uxx x t + Utt x t)
    {a b x : ℝ} (hab : a ≤ b)
    (hboundary : U x b * Ut x b = U x a * Ut x a) :
    2 * ((∫ t in a..b, Ux x t ^ 2) + ∫ t in a..b, Ut x t ^ 2) ≤
      iteratedDeriv 2 (test_squareEnergy U a b) x := by
  have hU_x : Continuous (U x) :=
    hU.comp (continuous_const.prodMk continuous_id)
  have hUx_x : Continuous (Ux x) :=
    hUx.comp (continuous_const.prodMk continuous_id)
  have hUxx_x : Continuous (Uxx x) :=
    hUxx.comp (continuous_const.prodMk continuous_id)
  have hUt_x : Continuous (Ut x) :=
    hUt.comp (continuous_const.prodMk continuous_id)
  have hUtt_x : Continuous (Utt x) :=
    hUtt.comp (continuous_const.prodMk continuous_id)
  have hibp : (∫ t in a..b, U x t * Utt x t) =
      -(∫ t in a..b, Ut x t ^ 2) :=
    test_intervalIntegral_mul_second_eq_neg_sq (hdifft x) (hdifftt x)
      hUt_x hUtt_x hboundary
  have hneg_int : IntervalIntegrable (fun t ↦ -(U x t * Utt x t)) volume a b :=
    (hU_x.mul hUtt_x).neg.intervalIntegrable _ _
  have hxx_int : IntervalIntegrable (fun t ↦ U x t * Uxx x t) volume a b :=
    (hU_x.mul hUxx_x).intervalIntegrable _ _
  have hmono : (∫ t in a..b, -(U x t * Utt x t)) ≤
      ∫ t in a..b, U x t * Uxx x t := by
    apply intervalIntegral.integral_mono_on hab hneg_int hxx_int
    intro t _
    have hmul := mul_nonneg (hU_nonneg x t) (hsubharmonic x t)
    nlinarith
  have ht_le_hxx : (∫ t in a..b, Ut x t ^ 2) ≤
      ∫ t in a..b, U x t * Uxx x t := by
    rw [intervalIntegral.integral_neg, hibp] at hmono
    simpa only [neg_neg] using hmono
  rw [test_iteratedDeriv_two_squareEnergy hU hUx hUxx hdiff hdiffx]
  have hUx2 : IntervalIntegrable (fun t ↦ Ux x t ^ 2) volume a b :=
    (hUx_x.pow 2).intervalIntegrable _ _
  have hUUxx : IntervalIntegrable (fun t ↦ U x t * Uxx x t) volume a b :=
    (hU_x.mul hUxx_x).intervalIntegrable _ _
  rw [intervalIntegral.integral_const_mul]
  rw [intervalIntegral.integral_add hUx2 hUUxx]
  exact mul_le_mul_of_nonneg_left (add_le_add le_rfl ht_le_hxx) (by norm_num)

noncomputable def test_logPolarX (f : ℂ → ℂ) (x θ : ℝ) : ℝ :=
  fderiv ℝ (logPolarLevel f) (logPolarPoint x θ) 1

noncomputable def test_logPolarT (f : ℂ → ℂ) (x θ : ℝ) : ℝ :=
  fderiv ℝ (logPolarLevel f) (logPolarPoint x θ) Complex.I

noncomputable def test_logPolarXX (f : ℂ → ℂ) (x θ : ℝ) : ℝ :=
  iteratedFDeriv ℝ 2 (logPolarLevel f) (logPolarPoint x θ) ![(1 : ℂ), 1]

noncomputable def test_logPolarTT (f : ℂ → ℂ) (x θ : ℝ) : ℝ :=
  iteratedFDeriv ℝ 2 (logPolarLevel f) (logPolarPoint x θ) ![Complex.I, Complex.I]

theorem test_continuous_logPolarPoint_uncurry :
    Continuous (Function.uncurry logPolarPoint) := by
  have h : Continuous (fun p : ℝ × ℝ ↦
      p.1 • (1 : ℂ) + p.2 • Complex.I) :=
    (continuous_fst.smul continuous_const).add (continuous_snd.smul continuous_const)
  convert h using 1
  funext p
  dsimp only [Function.uncurry]
  simp [logPolarPoint]

theorem test_continuous_logPolarX {f : ℂ → ℂ} (hf : IsEntire f) :
    Continuous (Function.uncurry (test_logPolarX f)) := by
  unfold test_logPolarX Function.uncurry
  exact ((contDiff_logPolarLevel hf).continuous_fderiv (by norm_num) |>.comp
    test_continuous_logPolarPoint_uncurry).clm_apply continuous_const

theorem test_continuous_logPolarT {f : ℂ → ℂ} (hf : IsEntire f) :
    Continuous (Function.uncurry (test_logPolarT f)) := by
  unfold test_logPolarT Function.uncurry
  exact ((contDiff_logPolarLevel hf).continuous_fderiv (by norm_num) |>.comp
    test_continuous_logPolarPoint_uncurry).clm_apply continuous_const

theorem test_continuous_logPolarXX {f : ℂ → ℂ} (hf : IsEntire f) :
    Continuous (Function.uncurry (test_logPolarXX f)) := by
  unfold test_logPolarXX Function.uncurry
  have hi : Continuous (fun p : ℝ × ℝ ↦
      iteratedFDeriv ℝ 2 (logPolarLevel f) (logPolarPoint p.1 p.2)) :=
    ((contDiff_logPolarLevel hf).continuous_iteratedFDeriv (by norm_num)).comp
      test_continuous_logPolarPoint_uncurry
  fun_prop

theorem test_continuous_logPolarTT {f : ℂ → ℂ} (hf : IsEntire f) :
    Continuous (Function.uncurry (test_logPolarTT f)) := by
  unfold test_logPolarTT Function.uncurry
  have hi : Continuous (fun p : ℝ × ℝ ↦
      iteratedFDeriv ℝ 2 (logPolarLevel f) (logPolarPoint p.1 p.2)) :=
    ((contDiff_logPolarLevel hf).continuous_iteratedFDeriv (by norm_num)).comp
      test_continuous_logPolarPoint_uncurry
  fun_prop

theorem test_deriv_logPolarSlice_fst {f : ℂ → ℂ} (hf : IsEntire f) (x θ : ℝ) :
    deriv (fun y : ℝ ↦ logPolarSlice f y θ) x = test_logPolarX f x θ := by
  rw [show (fun y : ℝ ↦ logPolarSlice f y θ) =
      (fun y : ℝ ↦ logPolarLevel f ((θ : ℂ) * Complex.I + y • (1 : ℂ))) by
    funext y
    simp [logPolarSlice, logPolarPoint, add_comm]]
  have hd := (contDiff_logPolarLevel hf).differentiable (by norm_num)
    ((θ : ℂ) * Complex.I + x • (1 : ℂ)) |>.deriv_comp_add_smul
  simpa [test_logPolarX, logPolarPoint, add_comm] using hd

theorem test_deriv_logPolarSlice_snd {f : ℂ → ℂ} (hf : IsEntire f) (x θ : ℝ) :
    deriv (logPolarSlice f x) θ = test_logPolarT f x θ := by
  rw [show logPolarSlice f x =
      (fun t : ℝ ↦ logPolarLevel f ((x : ℂ) + t • Complex.I)) by
    funext t
    simp [logPolarSlice, logPolarPoint]]
  have hd := (contDiff_logPolarLevel hf).differentiable (by norm_num)
    ((x : ℂ) + θ • Complex.I) |>.deriv_comp_add_smul
  simpa [test_logPolarT, logPolarPoint] using hd

theorem test_hasDerivAt_logPolarSlice_fst {f : ℂ → ℂ} (hf : IsEntire f) (x θ : ℝ) :
    HasDerivAt (fun y : ℝ ↦ logPolarSlice f y θ) (test_logPolarX f x θ) x := by
  rw [← test_deriv_logPolarSlice_fst hf x θ]
  exact hasDerivAt_deriv_iff.mpr
    ((contDiff_logPolarSlice_fst hf θ).differentiable (by norm_num) x)

theorem test_hasDerivAt_logPolarSlice_snd {f : ℂ → ℂ} (hf : IsEntire f) (x θ : ℝ) :
    HasDerivAt (logPolarSlice f x) (test_logPolarT f x θ) θ := by
  rw [← test_deriv_logPolarSlice_snd hf x θ]
  exact hasDerivAt_deriv_iff.mpr
    ((contDiff_logPolarSlice_snd hf x).differentiable (by norm_num) θ)

theorem test_iteratedDeriv_two_logPolarSlice_fst {f : ℂ → ℂ}
    (hf : IsEntire f) (x θ : ℝ) :
    iteratedDeriv 2 (fun y : ℝ ↦ logPolarSlice f y θ) x = test_logPolarXX f x θ := by
  rw [show (fun y : ℝ ↦ logPolarSlice f y θ) =
      (fun y : ℝ ↦ logPolarLevel f ((θ : ℂ) * Complex.I + y • (1 : ℂ))) by
    funext y
    simp [logPolarSlice, logPolarPoint, add_comm]]
  simpa [test_logPolarXX, logPolarPoint, add_comm] using
    (iteratedDeriv_two_affine_line_at
      (F := logPolarLevel f) (x := (θ : ℂ) * Complex.I) (v := (1 : ℂ)) (t := x)
      (contDiff_logPolarLevel hf).contDiffAt)

theorem test_iteratedDeriv_two_logPolarSlice_snd {f : ℂ → ℂ}
    (hf : IsEntire f) (x θ : ℝ) :
    iteratedDeriv 2 (logPolarSlice f x) θ = test_logPolarTT f x θ := by
  rw [show logPolarSlice f x =
      (fun t : ℝ ↦ logPolarLevel f ((x : ℂ) + t • Complex.I)) by
    funext t
    simp [logPolarSlice, logPolarPoint]]
  simpa [test_logPolarTT, logPolarPoint] using
    (iteratedDeriv_two_affine_line_at
      (F := logPolarLevel f) (x := (x : ℂ)) (v := Complex.I) (t := θ)
      (contDiff_logPolarLevel hf).contDiffAt)

theorem test_hasDerivAt_logPolarX_fst {f : ℂ → ℂ} (hf : IsEntire f) (x θ : ℝ) :
    HasDerivAt (fun y : ℝ ↦ test_logPolarX f y θ) (test_logPolarXX f x θ) x := by
  rw [show (fun y : ℝ ↦ test_logPolarX f y θ) =
      deriv (fun y : ℝ ↦ logPolarSlice f y θ) from
    funext fun y ↦ (test_deriv_logPolarSlice_fst hf y θ).symm]
  rw [← test_iteratedDeriv_two_logPolarSlice_fst hf x θ]
  rw [show iteratedDeriv 2 (fun y : ℝ ↦ logPolarSlice f y θ) x =
      deriv (deriv (fun y : ℝ ↦ logPolarSlice f y θ)) x by
    rw [show (2 : ℕ) = 1 + 1 by norm_num, iteratedDeriv_succ, iteratedDeriv_one]]
  have hslice : ContDiff ℝ (1 + 1) (fun y : ℝ ↦ logPolarSlice f y θ) := by
    convert contDiff_logPolarSlice_fst hf θ using 1 <;> norm_num
  exact hasDerivAt_deriv_iff.mpr
    ((contDiff_succ_iff_deriv.mp hslice).2.2.differentiable one_ne_zero x)

theorem test_hasDerivAt_logPolarT_snd {f : ℂ → ℂ} (hf : IsEntire f) (x θ : ℝ) :
    HasDerivAt (test_logPolarT f x) (test_logPolarTT f x θ) θ := by
  rw [show test_logPolarT f x = deriv (logPolarSlice f x) from
    funext fun t ↦ (test_deriv_logPolarSlice_snd hf x t).symm]
  rw [← test_iteratedDeriv_two_logPolarSlice_snd hf x θ]
  rw [show iteratedDeriv 2 (logPolarSlice f x) θ =
      deriv (deriv (logPolarSlice f x)) θ by
    rw [show (2 : ℕ) = 1 + 1 by norm_num, iteratedDeriv_succ, iteratedDeriv_one]]
  have hslice : ContDiff ℝ (1 + 1) (logPolarSlice f x) := by
    convert contDiff_logPolarSlice_snd hf x using 1 <;> norm_num
  exact hasDerivAt_deriv_iff.mpr
    ((contDiff_succ_iff_deriv.mp hslice).2.2.differentiable one_ne_zero θ)

theorem test_deriv_periodic {u : ℝ → ℝ} {T t : ℝ}
    (hu : Differentiable ℝ u) (hp : Function.Periodic u T) :
    deriv u (t + T) = deriv u t := by
  have hinner : HasDerivAt (fun s : ℝ ↦ s + T) 1 t :=
    (hasDerivAt_id t).add_const T
  have hcomp := (hasDerivAt_deriv_iff.mpr (hu (t + T))).comp t hinner
  have hfun : u ∘ (fun s : ℝ ↦ s + T) = u := by
    funext s
    exact hp s
  rw [hfun] at hcomp
  have hcomp' : HasDerivAt u (deriv u (t + T)) t := by simpa using hcomp
  exact hcomp'.unique (hasDerivAt_deriv_iff.mpr (hu t))

theorem test_continuous_uncurry_logPolarSlice {f : ℂ → ℂ} (hf : IsEntire f) :
    Continuous (Function.uncurry (logPolarSlice f)) := by
  exact (contDiff_logPolarLevel hf).continuous.comp test_continuous_logPolarPoint_uncurry

theorem test_logPolarSlice_nonneg (f : ℂ → ℂ) (x θ : ℝ) :
    0 ≤ logPolarSlice f x θ := by
  exact smoothPositivePart_nonneg _

theorem test_logPolar_second_fields_nonneg {f : ℂ → ℂ}
    (hf : IsEntire f) (x θ : ℝ) :
    0 ≤ test_logPolarXX f x θ + test_logPolarTT f x θ := by
  rw [← test_iteratedDeriv_two_logPolarSlice_fst hf x θ,
    ← test_iteratedDeriv_two_logPolarSlice_snd hf x θ]
  exact logPolarSlice_second_derivatives_add_nonneg hf x θ

theorem test_logPolarSlice_endpoint_eq (f : ℂ → ℂ) (x : ℝ) :
    logPolarSlice f x Real.pi = logPolarSlice f x (-Real.pi) := by
  have hp := logPolarSlice_periodic f x (-Real.pi)
  convert hp using 1 <;> ring

theorem test_logPolarT_endpoint_eq {f : ℂ → ℂ} (hf : IsEntire f) (x : ℝ) :
    test_logPolarT f x Real.pi = test_logPolarT f x (-Real.pi) := by
  have hp : Function.Periodic (logPolarSlice f x) (2 * Real.pi) :=
    logPolarSlice_periodic f x
  have hd := test_deriv_periodic
    ((contDiff_logPolarSlice_snd hf x).differentiable (by norm_num)) hp (t := -Real.pi)
  rw [test_deriv_logPolarSlice_snd hf x, test_deriv_logPolarSlice_snd hf x] at hd
  convert hd using 1 <;> ring

theorem test_logPolar_energy_second_deriv_ge {f : ℂ → ℂ}
    (hf : IsEntire f) (x : ℝ) :
    2 * ((∫ θ in -Real.pi..Real.pi, test_logPolarX f x θ ^ 2) +
        ∫ θ in -Real.pi..Real.pi, test_logPolarT f x θ ^ 2) ≤
      iteratedDeriv 2
        (cylindricalSquareEnergy (logPolarSlice f) (-Real.pi) Real.pi) x := by
  apply cylindricalSquareEnergy_second_deriv_ge_dirichlet
      (hU := test_continuous_uncurry_logPolarSlice hf)
      (hUx := test_continuous_logPolarX hf)
      (hUxx := test_continuous_logPolarXX hf)
      (hUt := test_continuous_logPolarT hf)
      (hUtt := test_continuous_logPolarTT hf)
      (hdiff := test_hasDerivAt_logPolarSlice_fst hf)
      (hdiffx := test_hasDerivAt_logPolarX_fst hf)
      (hdifft := test_hasDerivAt_logPolarSlice_snd hf)
      (hdifftt := test_hasDerivAt_logPolarT_snd hf)
      (hU_nonneg := test_logPolarSlice_nonneg f)
      (hsubharmonic := test_logPolar_second_fields_nonneg hf)
  · linarith [Real.pi_pos]
  · rw [test_logPolarSlice_endpoint_eq f x, test_logPolarT_endpoint_eq hf x]

theorem test_setIntegral_sq_le_measure_mul_setIntegral_sq
    {α : Type*} [MeasurableSpace α] {μ : Measure α} {s : Set α} {g : α → ℝ}
    (hs : μ s ≠ ∞)
    (hg_meas : AEStronglyMeasurable g (μ.restrict s))
    (hg_sq : Integrable (fun x ↦ g x ^ 2) (μ.restrict s))
    (hg_nonneg : ∀ᵐ x ∂μ.restrict s, 0 ≤ g x) :
    (∫ x in s, g x ∂μ) ^ 2 ≤
      μ.real s * ∫ x in s, g x ^ 2 ∂μ := by
  let ν : Measure α := μ.restrict s
  have hν : ν Set.univ ≠ ∞ := by
    simpa [ν] using hs
  let _ : IsFiniteMeasure ν := ⟨lt_top_iff_ne_top.mpr hν⟩
  have hone : MemLp (fun _ : α ↦ (1 : ℝ)) 2 ν := memLp_const 1
  have hg : MemLp g 2 ν :=
    (memLp_two_iff_integrable_sq hg_meas).mpr hg_sq
  have hholder := integral_mul_le_Lp_mul_Lq_of_nonneg
    (μ := ν) (f := fun _ : α ↦ (1 : ℝ)) (g := g)
    Real.HolderConjugate.two_two (ae_of_all ν fun _ ↦ zero_le_one) hg_nonneg
    (by simpa using hone) (by simpa using hg)
  change (∫ x, (1 : ℝ) * g x ∂ν) ≤
      (∫ _ : α, (1 : ℝ) ^ (2 : ℝ) ∂ν) ^ (1 / (2 : ℝ)) *
        (∫ x, g x ^ (2 : ℝ) ∂ν) ^ (1 / (2 : ℝ)) at hholder
  simp only [one_mul, Real.one_rpow, integral_const, smul_eq_mul, mul_one] at hholder
  rw [← Real.sqrt_eq_rpow, ← Real.sqrt_eq_rpow] at hholder
  have hholder' : (∫ x, g x ∂ν) ≤
      √(ν.real Set.univ) * √(∫ x, g x ^ 2 ∂ν) := by
    simpa only [Real.rpow_two] using hholder
  have hmeasure_nonneg : 0 ≤ ν.real Set.univ := measureReal_nonneg
  have hgint_nonneg : 0 ≤ ∫ x, g x ^ 2 ∂ν := by
    apply integral_nonneg_of_ae
    exact ae_of_all ν fun x ↦ sq_nonneg (g x)
  have hsquare : (∫ x, g x ∂ν) ^ 2 ≤
      (√(ν.real Set.univ) * √(∫ x, g x ^ 2 ∂ν)) ^ 2 :=
    (sq_le_sq₀ (integral_nonneg_of_ae hg_nonneg)
      (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))).mpr hholder'
  rw [mul_pow, Real.sq_sqrt hmeasure_nonneg, Real.sq_sqrt hgint_nonneg] at hsquare
  simpa only [ν, measureReal_restrict_apply_univ] using hsquare

theorem test_abs_le_intervalIntegral_abs_deriv
    {u u' : ℝ → ℝ} {a b z t : ℝ}
    (hu : ∀ x, HasDerivAt u (u' x) x) (hu' : Continuous u')
    (hz : z ∈ Set.Icc a b) (hz0 : u z = 0) (ht : t ∈ Set.Icc a b) :
    |u t| ≤ ∫ x in a..b, |u' x| := by
  have hdu : deriv u = u' := funext fun x ↦ (hu x).deriv
  have habsint : IntervalIntegrable (fun x ↦ |u' x|) volume a b :=
    hu'.abs.intervalIntegrable _ _
  rcases le_total z t with hzt | htz
  · have heq := intervalIntegral.integral_deriv_eq_sub' u hdu
      (fun x _ ↦ (hu x).differentiableAt) hu'.continuousOn (a := z) (b := t)
    rw [hz0, sub_zero] at heq
    rw [← heq, ← Real.norm_eq_abs]
    calc
      ‖∫ x in z..t, u' x‖ ≤ ∫ x in z..t, ‖u' x‖ :=
        intervalIntegral.norm_integral_le_integral_norm hzt
      _ ≤ ∫ x in a..b, ‖u' x‖ := intervalIntegral.integral_mono_interval
        hz.1 hzt ht.2 (ae_of_all _ fun x ↦ norm_nonneg _) habsint
  · have heq := intervalIntegral.integral_deriv_eq_sub' u hdu
      (fun x _ ↦ (hu x).differentiableAt) hu'.continuousOn (a := t) (b := z)
    rw [hz0, zero_sub] at heq
    rw [← Real.norm_eq_abs, ← norm_neg (u t), ← heq]
    calc
      ‖∫ x in t..z, u' x‖ ≤ ∫ x in t..z, ‖u' x‖ :=
        intervalIntegral.norm_integral_le_integral_norm htz
      _ ≤ ∫ x in a..b, ‖u' x‖ := intervalIntegral.integral_mono_interval
        ht.1 htz hz.2 (ae_of_all _ fun x ↦ norm_nonneg _) habsint

theorem test_intervalIntegral_sq_le_supportMeasure_sq_mul_deriv_sq
    {u u' : ℝ → ℝ} {a b : ℝ}
    (hab : a ≤ b) (hucont : Continuous u) (hu'cont : Continuous u')
    (hderiv : ∀ x, HasDerivAt u (u' x) x)
    (hunonneg : ∀ x, 0 ≤ u x)
    (hproper : volume.real (Set.Ioc a b ∩ {x | 0 < u x}) < volume.real (Set.Ioc a b)) :
    (∫ x in a..b, u x ^ 2) ≤
      (volume.real (Set.Ioc a b ∩ {x | 0 < u x})) ^ 2 *
        ∫ x in a..b, u' x ^ 2 := by
  let s : Set ℝ := Set.Ioc a b ∩ {x | 0 < u x}
  have hs_sub : s ⊆ Set.Ioc a b := inter_subset_left
  have hI_top : volume (Set.Ioc a b) ≠ ∞ := by
    simp [Real.volume_Ioc]
  have hs_top : volume s ≠ ∞ :=
    ne_top_of_le_ne_top hI_top (measure_mono hs_sub)
  have hnsub : ¬ Set.Ioc a b ⊆ s := by
    intro hsub
    exact (not_le_of_gt hproper) (measureReal_mono hsub hs_top)
  obtain ⟨z, hzI, hzs⟩ := Set.not_subset.mp hnsub
  have hz0 : u z = 0 := by
    have hnpos : ¬ 0 < u z := by
      intro hp
      exact hzs ⟨hzI, hp⟩
    exact le_antisymm (le_of_not_gt hnpos) (hunonneg z)
  have hzIcc : z ∈ Set.Icc a b := ⟨hzI.1.le, hzI.2⟩
  have hzero : ∀ y ∈ Set.Ioc a b \ s, u y = 0 := by
    intro y hy
    have hnpos : ¬ 0 < u y := by
      intro hp
      exact hy.2 ⟨hy.1, hp⟩
    exact le_antisymm (le_of_not_gt hnpos) (hunonneg y)
  have hderivzero : ∀ y ∈ Set.Ioc a b \ s, u' y = 0 := by
    intro y hy
    have hlocal : IsLocalMin u y := by
      filter_upwards with q
      rw [hzero y hy]
      exact hunonneg q
    have hd0 := hlocal.deriv_eq_zero
    rw [(hderiv y).deriv] at hd0
    exact hd0
  have hs_meas : MeasurableSet s := by
    exact measurableSet_Ioc.inter (isOpen_lt continuous_const hucont).measurableSet
  have habseq : (∫ x in a..b, |u' x|) = ∫ x in s, |u' x| := by
    rw [intervalIntegral.integral_of_le hab]
    apply setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Ioc hs_sub
    intro y hy
    rw [hderivzero y hy, abs_zero]
  have hderivsqeq : (∫ x in a..b, u' x ^ 2) = ∫ x in s, |u' x| ^ 2 := by
    rw [intervalIntegral.integral_of_le hab]
    calc
      (∫ x in Set.Ioc a b, u' x ^ 2) = ∫ x in Set.Ioc a b, |u' x| ^ 2 := by
        apply integral_congr_ae
        filter_upwards with y
        rw [sq_abs]
      _ = ∫ x in s, |u' x| ^ 2 := by
        apply setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Ioc hs_sub
        intro y hy
        rw [hderivzero y hy, abs_zero, zero_pow two_ne_zero]
  have hUsqeq : (∫ x in a..b, u x ^ 2) = ∫ x in s, u x ^ 2 := by
    rw [intervalIntegral.integral_of_le hab]
    apply setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Ioc hs_sub
    intro y hy
    rw [hzero y hy, zero_pow two_ne_zero]
  let J : ℝ := ∫ x in s, |u' x|
  have hpoint : ∀ y ∈ s, u y ^ 2 ≤ J ^ 2 := by
    intro y hy
    have hyIcc : y ∈ Set.Icc a b := ⟨hy.1.1.le, hy.1.2⟩
    have habs := test_abs_le_intervalIntegral_abs_deriv hderiv hu'cont hzIcc hz0 hyIcc
    rw [habseq] at habs
    exact (sq_le_sq₀ (hunonneg y) (by
      dsimp only [J]
      apply integral_nonneg_of_ae
      exact ae_of_all _ fun q ↦ abs_nonneg _)).mpr (by
        simpa [abs_of_nonneg (hunonneg y), J] using habs)
  have hUsq_int : IntegrableOn (fun y ↦ u y ^ 2) s :=
    (hucont.pow 2).integrableOn_Icc.mono_set (hs_sub.trans Set.Ioc_subset_Icc_self)
  have hconst_int : IntegrableOn (fun _ : ℝ ↦ J ^ 2) s := by
    exact integrableOn_const hs_top (by simp)
  have hU_le : (∫ y in s, u y ^ 2) ≤ volume.real s * J ^ 2 := by
    calc
      (∫ y in s, u y ^ 2) ≤ ∫ _ in s, J ^ 2 := by
        apply setIntegral_mono_on hUsq_int hconst_int hs_meas
        exact hpoint
      _ = volume.real s * J ^ 2 := by rw [setIntegral_const, smul_eq_mul]
  have hJ : J ^ 2 ≤ volume.real s * ∫ x in s, |u' x| ^ 2 := by
    apply test_setIntegral_sq_le_measure_mul_setIntegral_sq hs_top
    · exact hu'cont.abs.aestronglyMeasurable.restrict
    · exact (hu'cont.abs.pow 2).integrableOn_Icc.mono_set
        (hs_sub.trans Set.Ioc_subset_Icc_self)
    · exact ae_of_all _ fun y ↦ abs_nonneg _
  rw [hUsqeq, hderivsqeq]
  calc
    (∫ x in s, u x ^ 2) ≤ volume.real s * J ^ 2 := hU_le
    _ ≤ volume.real s * (volume.real s * ∫ x in s, |u' x| ^ 2) :=
      mul_le_mul_of_nonneg_left hJ measureReal_nonneg
    _ = (volume.real s) ^ 2 * ∫ x in s, |u' x| ^ 2 := by ring

theorem test_logPolar_support_measure_eq_angularWidth (f : ℂ → ℂ) (x : ℝ) :
    volume.real (Set.Ioc (-Real.pi) Real.pi ∩ ({θ | 0 < logPolarSlice f x θ} : Set ℝ)) =
      angularWidth (exceptionalSet f 1) (Real.exp x) := by
  have hbase : Set.Ioo (-Real.pi) Real.pi =ᵐ[volume] Set.Ioc (-Real.pi) Real.pi :=
    Ioo_ae_eq_Ioc
  have hae : ∀ᵐ θ ∂volume,
      θ ∈ Set.Ioc (-Real.pi) Real.pi ∩ ({θ | 0 < logPolarSlice f x θ} : Set ℝ) ↔
      θ ∈ Set.Ioo (-Real.pi) Real.pi ∩ ({θ | 0 < logPolarSlice f x θ} : Set ℝ) := by
    filter_upwards [hbase.symm] with θ hθ
    constructor
    · rintro ⟨hI, hp⟩
      have hI' : Set.Ioc (-Real.pi) Real.pi θ := hI
      have hI'' : Set.Ioo (-Real.pi) Real.pi θ := hθ ▸ hI'
      exact ⟨hI'', hp⟩
    · rintro ⟨hI, hp⟩
      have hI' : Set.Ioo (-Real.pi) Real.pi θ := hI
      have hI'' : Set.Ioc (-Real.pi) Real.pi θ := hθ.symm ▸ hI'
      exact ⟨hI'', hp⟩
  have hm : volume (Set.Ioc (-Real.pi) Real.pi ∩
      ({θ | 0 < logPolarSlice f x θ} : Set ℝ)) =
      volume (Set.Ioo (-Real.pi) Real.pi ∩
        ({θ | 0 < logPolarSlice f x θ} : Set ℝ)) :=
    measure_congr (hae.mono fun _ h ↦ propext h)
  rw [measureReal_def, hm]
  have hs : Set.Ioo (-Real.pi) Real.pi ∩ ({θ | 0 < logPolarSlice f x θ} : Set ℝ) =
      angularSection (exceptionalSet f 1) (Real.exp x) := by
    ext θ
    simpa only [Set.mem_inter_iff, Set.mem_ofPred_eq] using
      Set.ext_iff.mp (positive_logPolarSlice_set f x) θ
  rw [hs]
  rfl

theorem test_volumeReal_Ioc_neg_pi_pi :
    volume.real (Set.Ioc (-Real.pi) Real.pi) = 2 * Real.pi := by
  rw [measureReal_def, Real.volume_Ioc]
  simp only [sub_neg_eq_add, ENNReal.toReal_ofReal (by positivity : 0 ≤ Real.pi + Real.pi)]
  ring

theorem test_logPolar_poincare {f : ℂ → ℂ} (hf : IsEntire f) (x : ℝ)
    (hwidth : angularWidth (exceptionalSet f 1) (Real.exp x) < 2 * Real.pi) :
    cylindricalSquareEnergy (logPolarSlice f) (-Real.pi) Real.pi x ≤
      (angularWidth (exceptionalSet f 1) (Real.exp x)) ^ 2 *
        ∫ θ in -Real.pi..Real.pi, logPolarTheta f x θ ^ 2 := by
  unfold cylindricalSquareEnergy
  have htcont : Continuous (logPolarTheta f x) :=
    (continuous_logPolarTheta hf).comp (continuous_const.prodMk continuous_id)
  have hproper : volume.real
      (Set.Ioc (-Real.pi) Real.pi ∩ ({θ | 0 < logPolarSlice f x θ} : Set ℝ)) <
      volume.real (Set.Ioc (-Real.pi) Real.pi) := by
    rw [test_logPolar_support_measure_eq_angularWidth,
      test_volumeReal_Ioc_neg_pi_pi]
    exact hwidth
  have h := intervalIntegral_sq_le_supportMeasure_sq_mul_deriv_sq
      (u := logPolarSlice f x) (u' := logPolarTheta f x)
      (a := -Real.pi) (b := Real.pi) (by linarith [Real.pi_pos])
      (contDiff_logPolarSlice_snd hf x).continuous htcont
      (hasDerivAt_logPolarSlice_snd hf x) (logPolarSlice_nonneg f x) hproper
  rw [test_logPolar_support_measure_eq_angularWidth] at h
  exact h

theorem test_logPolar_energy_width_differential {f : ℂ → ℂ}
    (hf : IsEntire f) (x : ℝ)
    (hwidth : angularWidth (exceptionalSet f 1) (Real.exp x) < 2 * Real.pi) :
    2 * cylindricalSquareEnergy (logPolarSlice f) (-Real.pi) Real.pi x ≤
      (angularWidth (exceptionalSet f 1) (Real.exp x)) ^ 2 *
        iteratedDeriv 2
          (cylindricalSquareEnergy (logPolarSlice f) (-Real.pi) Real.pi) x := by
  let Ex : ℝ := ∫ θ in -Real.pi..Real.pi, logPolarX f x θ ^ 2
  let Et : ℝ := ∫ θ in -Real.pi..Real.pi, logPolarTheta f x θ ^ 2
  let H : ℝ → ℝ := cylindricalSquareEnergy
    (logPolarSlice f) (-Real.pi) Real.pi
  let Θ : ℝ := angularWidth (exceptionalSet f 1) (Real.exp x)
  have hEx : 0 ≤ Ex := by
    apply intervalIntegral.integral_nonneg (by linarith [Real.pi_pos])
    intro θ _
    exact sq_nonneg _
  have hp : H x ≤ Θ ^ 2 * Et := by
    simpa only [H, Θ, Et] using test_logPolar_poincare hf x hwidth
  have he : 2 * (Ex + Et) ≤ iteratedDeriv 2 H x := by
    simpa only [H, Ex, Et] using logPolar_energy_second_deriv_ge hf x
  have het : 2 * Et ≤ iteratedDeriv 2 H x := by
    calc
      2 * Et ≤ 2 * (Ex + Et) := by nlinarith
      _ ≤ iteratedDeriv 2 H x := he
  calc
    2 * H x ≤ 2 * (Θ ^ 2 * Et) := mul_le_mul_of_nonneg_left hp (by norm_num)
    _ = Θ ^ 2 * (2 * Et) := by ring
    _ ≤ Θ ^ 2 * iteratedDeriv 2 H x :=
      mul_le_mul_of_nonneg_left het (sq_nonneg Θ)

theorem test_intervalIntegral_mul_sq_le_mul_sq
    {u v : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hu : Continuous u) (hv : Continuous v) :
    (∫ t in a..b, u t * v t) ^ 2 ≤
      (∫ t in a..b, u t ^ 2) * (∫ t in a..b, v t ^ 2) := by
  rw [intervalIntegral.integral_of_le hab, intervalIntegral.integral_of_le hab,
    intervalIntegral.integral_of_le hab]
  let ν : Measure ℝ := volume.restrict (Set.Ioc a b)
  have hu_meas : AEStronglyMeasurable u ν :=
    hu.aestronglyMeasurable.restrict
  have hv_meas : AEStronglyMeasurable v ν :=
    hv.aestronglyMeasurable.restrict
  have hu_sq : Integrable (fun t ↦ u t ^ 2) ν := by
    exact (hu.pow 2).integrableOn_Icc.mono_set Set.Ioc_subset_Icc_self
  have hv_sq : Integrable (fun t ↦ v t ^ 2) ν := by
    exact (hv.pow 2).integrableOn_Icc.mono_set Set.Ioc_subset_Icc_self
  have hνu : MemLp u 2 ν :=
    (memLp_two_iff_integrable_sq hu_meas).mpr hu_sq
  have hνv : MemLp v 2 ν :=
    (memLp_two_iff_integrable_sq hv_meas).mpr hv_sq
  have hholder := integral_mul_norm_le_Lp_mul_Lq
    (f := u) (g := v) (p := (2 : ℝ)) (q := (2 : ℝ)) (μ := ν)
    Real.HolderConjugate.two_two (by simpa using hνu) (by simpa using hνv)
  change (∫ t, |u t| * |v t| ∂ν) ≤
      (∫ t, |u t| ^ (2 : ℝ) ∂ν) ^ (1 / (2 : ℝ)) *
        (∫ t, |v t| ^ (2 : ℝ) ∂ν) ^ (1 / (2 : ℝ)) at hholder
  have hu_abs_sq : (∫ t, |u t| ^ (2 : ℝ) ∂ν) = ∫ t, u t ^ 2 ∂ν := by
    apply integral_congr_ae
    filter_upwards with t
    rw [Real.rpow_two, sq_abs]
  have hv_abs_sq : (∫ t, |v t| ^ (2 : ℝ) ∂ν) = ∫ t, v t ^ 2 ∂ν := by
    apply integral_congr_ae
    filter_upwards with t
    rw [Real.rpow_two, sq_abs]
  rw [hu_abs_sq, hv_abs_sq, ← Real.sqrt_eq_rpow, ← Real.sqrt_eq_rpow] at hholder
  have hnorm : |∫ t, u t * v t ∂ν| ≤ ∫ t, |u t| * |v t| ∂ν := by
    calc
      |∫ t, u t * v t ∂ν| = ‖∫ t, u t * v t ∂ν‖ := by rw [Real.norm_eq_abs]
      _ ≤ ∫ t, ‖u t * v t‖ ∂ν := norm_integral_le_integral_norm _
      _ = ∫ t, |u t| * |v t| ∂ν := by
        apply integral_congr_ae
        filter_upwards with t
        rw [Real.norm_eq_abs, abs_mul]
  have hroot : |∫ t, u t * v t ∂ν| ≤
      √(∫ t, u t ^ 2 ∂ν) * √(∫ t, v t ^ 2 ∂ν) := hnorm.trans hholder
  have hu_nonneg : 0 ≤ ∫ t, u t ^ 2 ∂ν :=
    integral_nonneg_of_ae (ae_of_all _ fun t ↦ sq_nonneg _)
  have hv_nonneg : 0 ≤ ∫ t, v t ^ 2 ∂ν :=
    integral_nonneg_of_ae (ae_of_all _ fun t ↦ sq_nonneg _)
  have hsquare := (sq_le_sq₀ (abs_nonneg (∫ t, u t * v t ∂ν))
    (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))).mpr hroot
  rw [sq_abs, mul_pow, Real.sq_sqrt hu_nonneg, Real.sq_sqrt hv_nonneg] at hsquare
  simpa only [ν] using hsquare

theorem test_logPolar_energy_deriv_sq_le {f : ℂ → ℂ}
    (hf : IsEntire f) (x : ℝ) :
    (deriv (cylindricalSquareEnergy
      (logPolarSlice f) (-Real.pi) Real.pi) x) ^ 2 ≤
      4 * cylindricalSquareEnergy
          (logPolarSlice f) (-Real.pi) Real.pi x *
        ∫ θ in -Real.pi..Real.pi, logPolarX f x θ ^ 2 := by
  let H : ℝ → ℝ := cylindricalSquareEnergy
    (logPolarSlice f) (-Real.pi) Real.pi
  let J : ℝ := ∫ θ in -Real.pi..Real.pi,
    logPolarSlice f x θ * logPolarX f x θ
  have hderiv : deriv H x = 2 * J := by
    have h := (hasDerivAt_cylindricalSquareEnergy
      (continuous_uncurry_logPolarSlice hf) (continuous_logPolarX hf)
      (hasDerivAt_logPolarSlice_fst hf) (-Real.pi) Real.pi x).deriv
    dsimp only [H]
    rw [h, intervalIntegral.integral_const_mul]
  have hcs : J ^ 2 ≤
      H x * ∫ θ in -Real.pi..Real.pi, logPolarX f x θ ^ 2 := by
    dsimp only [J, H, cylindricalSquareEnergy]
    apply test_intervalIntegral_mul_sq_le_mul_sq (by linarith [Real.pi_pos])
    · exact (contDiff_logPolarSlice_snd hf x).continuous
    · exact (continuous_logPolarX hf).comp (continuous_const.prodMk continuous_id)
  rw [hderiv]
  nlinarith

theorem test_logPolar_energy_pos_of_log_max_pos {f : ℂ → ℂ}
    (hf : IsEntire f) (x : ℝ)
    (hlog : 0 < Real.log (logarithmicMaximum f 1 (Real.exp x))) :
    0 < cylindricalSquareEnergy
      (logPolarSlice f) (-Real.pi) Real.pi x := by
  have hr : 0 < Real.exp x := Real.exp_pos x
  have hB : 1 < logarithmicMaximum f 1 (Real.exp x) :=
    (Real.log_pos_iff Real.posLog_nonneg).mp hlog
  obtain ⟨θ, hθI, hθE⟩ :=
    angularSection_exceptional_nonempty_of_one_lt_logarithmicMaximum
      hf.continuous hr hB
  have hθpos : 0 < logPolarSlice f x θ := by
    have hs := Set.ext_iff.mp (positive_logPolarSlice_set f x) θ
    exact (hs.mpr ⟨hθI, hθE⟩).2
  let P : Set ℝ := Set.Ioo (-Real.pi) Real.pi ∩
    {t | 0 < logPolarSlice f x t}
  have hPopen : IsOpen P := by
    exact isOpen_Ioo.inter
      (isOpen_lt continuous_const (contDiff_logPolarSlice_snd hf x).continuous)
  have hPne : P.Nonempty := ⟨θ, hθI, hθpos⟩
  have hPpos : 0 < volume P := hPopen.measure_pos volume hPne
  have hPsub : P ⊆ Function.support (fun t ↦ logPolarSlice f x t ^ 2) ∩
      Set.Ioc (-Real.pi) Real.pi := by
    intro t ht
    refine ⟨?_, Set.Ioo_subset_Ioc_self ht.1⟩
    exact Function.mem_support.mpr (sq_pos_of_pos ht.2).ne'
  unfold cylindricalSquareEnergy
  rw [intervalIntegral.integral_of_le (by linarith [Real.pi_pos])]
  apply (setIntegral_pos_iff_support_of_nonneg_ae
    (ae_of_all _ fun t ↦ sq_nonneg _)
    ((contDiff_logPolarSlice_snd hf x).continuous.pow 2
      |>.integrableOn_Icc.mono_set Set.Ioc_subset_Icc_self)).mpr
  exact hPpos.trans_le (measure_mono hPsub)

theorem test_iteratedDeriv_two_sqrt
    {H H₁ H₂ : ℝ → ℝ}
    (hH : ∀ y, HasDerivAt H (H₁ y) y)
    (hH₁ : ∀ y, HasDerivAt H₁ (H₂ y) y)
    {x : ℝ} (hx : 0 < H x) :
    iteratedDeriv 2 (fun y ↦ √(H y)) x =
      H₂ x / (2 * √(H x)) - H₁ x ^ 2 / (4 * (√(H x)) ^ 3) := by
  let F : ℝ → ℝ := fun y ↦ √(H y)
  let G : ℝ → ℝ := fun y ↦ H₁ y / (2 * F y)
  let D : ℝ := H₂ x / (2 * F x) - H₁ x ^ 2 / (4 * (F x) ^ 3)
  have hFne : F x ≠ 0 := by
    dsimp only [F]
    exact (Real.sqrt_ne_zero').mpr hx
  have hF : HasDerivAt F (H₁ x / (2 * F x)) x := by
    dsimp only [F]
    simpa only using (hH x).sqrt hx.ne'
  have hG : HasDerivAt G D x := by
    have hraw := (hH₁ x).div (hF.const_mul 2) (mul_ne_zero two_ne_zero hFne)
    have hval :
        (H₂ x * (2 * F x) - H₁ x * (2 * (H₁ x / (2 * F x)))) /
            (2 * F x) ^ 2 = D := by
      dsimp only [D]
      field_simp [hFne]
      ring
    rw [hval] at hraw
    change HasDerivAt (fun y ↦ H₁ y / (2 * F y)) D x at hraw
    exact hraw
  have hHcont : Continuous H := continuous_iff_continuousAt.mpr fun y ↦ (hH y).continuousAt
  have hne : ∀ᶠ y in nhds x, H y ≠ 0 := by
    exact (isOpen_compl_singleton.preimage hHcont).mem_nhds hx.ne'
  have hderiv_eq : deriv F =ᶠ[nhds x] G := by
    filter_upwards [hne] with y hy
    dsimp only [F, G]
    rw [deriv_sqrt (hH y).differentiableAt hy, (hH y).deriv]
  have hd : HasDerivAt (deriv F) D x := hG.congr_of_eventuallyEq hderiv_eq
  rw [show iteratedDeriv 2 F x = deriv (deriv F) x by
    rw [show (2 : ℕ) = 1 + 1 by norm_num, iteratedDeriv_succ, iteratedDeriv_one]]
  simpa only [F, D] using hd.deriv

theorem test_logPolar_sqrt_energy_second_deriv_ge {f : ℂ → ℂ}
    (hf : IsEntire f) (x : ℝ)
    (hlog : 0 < Real.log (logarithmicMaximum f 1 (Real.exp x)))
    (hwidth : angularWidth (exceptionalSet f 1) (Real.exp x) < 2 * Real.pi) :
    √(cylindricalSquareEnergy
          (logPolarSlice f) (-Real.pi) Real.pi x) /
        (angularWidth (exceptionalSet f 1) (Real.exp x)) ^ 2 ≤
      iteratedDeriv 2
        (fun y ↦ √(cylindricalSquareEnergy
          (logPolarSlice f) (-Real.pi) Real.pi y)) x := by
  let H : ℝ → ℝ := cylindricalSquareEnergy
    (logPolarSlice f) (-Real.pi) Real.pi
  let H₁ : ℝ → ℝ := fun y ↦ ∫ θ in -Real.pi..Real.pi,
    2 * (logPolarSlice f y θ * logPolarX f y θ)
  let H₂ : ℝ → ℝ := fun y ↦ ∫ θ in -Real.pi..Real.pi,
    2 * (logPolarX f y θ ^ 2 + logPolarSlice f y θ * logPolarXX f y θ)
  let Ex : ℝ := ∫ θ in -Real.pi..Real.pi, logPolarX f x θ ^ 2
  let Et : ℝ := ∫ θ in -Real.pi..Real.pi, logPolarTheta f x θ ^ 2
  let Θ : ℝ := angularWidth (exceptionalSet f 1) (Real.exp x)
  let F : ℝ := √(H x)
  have hH : ∀ y, HasDerivAt H (H₁ y) y := by
    intro y
    simpa only [H, H₁] using hasDerivAt_cylindricalSquareEnergy
      (continuous_uncurry_logPolarSlice hf) (continuous_logPolarX hf)
      (hasDerivAt_logPolarSlice_fst hf) (-Real.pi) Real.pi y
  have hH₁ : ∀ y, HasDerivAt H₁ (H₂ y) y := by
    intro y
    apply hasDerivAt_intervalIntegral_of_continuous_partial
        (F := fun s t ↦ 2 * (logPolarSlice f s t * logPolarX f s t))
        (F' := fun s t ↦
          2 * (logPolarX f s t ^ 2 + logPolarSlice f s t * logPolarXX f s t))
    · exact continuous_const.mul
        ((continuous_uncurry_logPolarSlice hf).mul (continuous_logPolarX hf))
    · exact continuous_const.mul
        ((continuous_logPolarX hf).pow 2 |>.add
          ((continuous_uncurry_logPolarSlice hf).mul (continuous_logPolarXX hf)))
    · intro s t
      simpa [pow_two] using
        ((hasDerivAt_logPolarSlice_fst hf s t).mul
          (hasDerivAt_logPolarX_fst hf s t)).const_mul (2 : ℝ)
  have hHpos : 0 < H x := by
    simpa only [H] using test_logPolar_energy_pos_of_log_max_pos hf x hlog
  have hFpos : 0 < F := by
    dsimp only [F]
    exact Real.sqrt_pos.2 hHpos
  have hΘpos : 0 < Θ := by
    apply angularWidth_exceptional_pos_of_one_lt_logarithmicMaximum hf.continuous
      (Real.exp_pos x)
    exact (Real.log_pos_iff Real.posLog_nonneg).mp hlog
  have hF2 : F ^ 2 = H x := by
    dsimp only [F]
    exact Real.sq_sqrt hHpos.le
  have hsecond : iteratedDeriv 2 (fun y ↦ √(H y)) x =
      H₂ x / (2 * F) - H₁ x ^ 2 / (4 * F ^ 3) := by
    simpa only [F] using test_iteratedDeriv_two_sqrt hH hH₁ hHpos
  have hH2 : H₂ x = iteratedDeriv 2 H x := by
    symm
    simpa only [H, H₂] using iteratedDeriv_two_cylindricalSquareEnergy
      (continuous_uncurry_logPolarSlice hf) (continuous_logPolarX hf)
      (continuous_logPolarXX hf) (hasDerivAt_logPolarSlice_fst hf)
      (hasDerivAt_logPolarX_fst hf) (-Real.pi) Real.pi x
  have henergy : 2 * (Ex + Et) ≤ H₂ x := by
    rw [hH2]
    simpa only [H, Ex, Et] using logPolar_energy_second_deriv_ge hf x
  have hcs : H₁ x ^ 2 ≤ 4 * H x * Ex := by
    have h := test_logPolar_energy_deriv_sq_le hf x
    rw [(hH x).deriv] at h
    simpa only [H, H₁, Ex] using h
  have hp : H x ≤ Θ ^ 2 * Et := by
    simpa only [H, Θ, Et] using test_logPolar_poincare hf x hwidth
  have henergy' : 2 * (Ex + Et) * (2 * F ^ 2 * Θ ^ 2) ≤
      H₂ x * (2 * F ^ 2 * Θ ^ 2) :=
    mul_le_mul_of_nonneg_right henergy
      (mul_nonneg (mul_nonneg (by norm_num) (sq_nonneg F)) (sq_nonneg Θ))
  have hcs' : H₁ x ^ 2 * Θ ^ 2 ≤ (4 * H x * Ex) * Θ ^ 2 :=
    mul_le_mul_of_nonneg_right hcs (sq_nonneg Θ)
  have hp' : 4 * H x * H x ≤ 4 * H x * (Θ ^ 2 * Et) :=
    mul_le_mul_of_nonneg_left hp (mul_nonneg (by norm_num) hHpos.le)
  have hF4 : F ^ 4 = (H x) ^ 2 := by
    calc
      F ^ 4 = (F ^ 2) ^ 2 := by ring
      _ = (H x) ^ 2 := by rw [hF2]
  have hleft : 4 * F ^ 4 + H₁ x ^ 2 * Θ ^ 2 ≤
      4 * F ^ 2 * Θ ^ 2 * (Ex + Et) := by
    calc
      4 * F ^ 4 + H₁ x ^ 2 * Θ ^ 2 =
          4 * H x * H x + H₁ x ^ 2 * Θ ^ 2 := by rw [hF4]; ring
      _ ≤ 4 * H x * (Θ ^ 2 * Et) + (4 * H x * Ex) * Θ ^ 2 :=
        add_le_add hp' hcs'
      _ = 4 * F ^ 2 * Θ ^ 2 * (Ex + Et) := by rw [hF2]; ring
  have hright : 4 * F ^ 2 * Θ ^ 2 * (Ex + Et) ≤
      2 * H₂ x * F ^ 2 * Θ ^ 2 := by
    calc
      4 * F ^ 2 * Θ ^ 2 * (Ex + Et) =
          2 * (Ex + Et) * (2 * F ^ 2 * Θ ^ 2) := by ring
      _ ≤ H₂ x * (2 * F ^ 2 * Θ ^ 2) := henergy'
      _ = 2 * H₂ x * F ^ 2 * Θ ^ 2 := by ring
  have hpoly : 0 ≤
      2 * H₂ x * F ^ 2 * Θ ^ 2 - H₁ x ^ 2 * Θ ^ 2 - 4 * F ^ 4 := by
    nlinarith [hleft.trans hright]
  have hid : H₂ x / (2 * F) - H₁ x ^ 2 / (4 * F ^ 3) - F / Θ ^ 2 =
      (2 * H₂ x * F ^ 2 * Θ ^ 2 - H₁ x ^ 2 * Θ ^ 2 -
        4 * F ^ 4) / (4 * F ^ 3 * Θ ^ 2) := by
    field_simp [hFpos.ne', hΘpos.ne']
    ring
  change F / Θ ^ 2 ≤ iteratedDeriv 2 (fun y ↦ √(H y)) x
  rw [hsecond]
  apply le_of_sub_nonneg
  rw [hid]
  apply div_nonneg
  · exact hpoly
  · positivity

#check Integrable.mono'
#check Integrable.mono
#check Integrable.mono_measure
#check IntervalIntegrable.mono
#check intervalIntegral.integral_mono_on
#check intervalIntegral.integral_deriv_eq_sub'

theorem test_intervalIntegral_carleman_log_bound
    {F F₁ F₂ q : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hF : ∀ x, HasDerivAt F (F₁ x) x)
    (hF₁ : ∀ x, HasDerivAt F₁ (F₂ x) x)
    (hF₂cont : Continuous F₂)
    (hFpos : ∀ x ∈ Set.Icc a b, 0 < F x)
    (hF₁pos : ∀ x ∈ Set.Icc a b, 0 < F₁ x)
    (hqmeas : AEStronglyMeasurable q volume)
    (hqnonneg : ∀ x ∈ Set.Icc a b, 0 ≤ q x)
    (hcurv : ∀ x ∈ Set.Icc a b, q x ^ 2 * F x ≤ F₂ x) :
    IntervalIntegrable q volume a b ∧
      2 * ∫ x in a..b, q x ≤
        (Real.log (F b) - Real.log (F a)) +
          (Real.log (F₁ b) - Real.log (F₁ a)) := by
  have hFcont : Continuous F := continuous_iff_continuousAt.mpr fun x ↦ (hF x).continuousAt
  have hF₁cont : Continuous F₁ := continuous_iff_continuousAt.mpr fun x ↦ (hF₁ x).continuousAt
  let g : ℝ → ℝ := fun x ↦ F₁ x / F x + F₂ x / F₁ x
  have hpoint : ∀ x ∈ Set.Icc a b, 2 * q x ≤ g x := by
    intro x hx
    have hFp := hFpos x hx
    have hF₁p := hF₁pos x hx
    have hid : F₁ x / F x + q x ^ 2 * F x / F₁ x - 2 * q x =
        (F₁ x - q x * F x) ^ 2 / (F x * F₁ x) := by
      field_simp [hFp.ne', hF₁p.ne']
      ring
    have ham : 2 * q x ≤ F₁ x / F x + q x ^ 2 * F x / F₁ x := by
      rw [← sub_nonneg]
      rw [hid]
      positivity
    have hc : q x ^ 2 * F x / F₁ x ≤ F₂ x / F₁ x :=
      div_le_div_of_nonneg_right (hcurv x hx) hF₁p.le
    dsimp only [g]
    linarith
  have hgcont : ContinuousOn g (Set.Icc a b) := by
    have hg₁ : ContinuousOn (fun x ↦ F₁ x / F x) (Set.Icc a b) := by
      exact hF₁cont.continuousOn.div hFcont.continuousOn fun x hx ↦
        (hFpos x hx).ne'
    have hg₂ : ContinuousOn (fun x ↦ F₂ x / F₁ x) (Set.Icc a b) := by
      exact hF₂cont.continuousOn.div hF₁cont.continuousOn fun x hx ↦
        (hF₁pos x hx).ne'
    exact hg₁.add hg₂
  have hgint : IntegrableOn g (Set.Icc a b) := hgcont.integrableOn_Icc
  have hqintOn : IntegrableOn q (Set.Icc a b) := by
    apply hgint.mono' hqmeas.restrict
    filter_upwards [ae_restrict_mem measurableSet_Icc] with x hx
    rw [Real.norm_eq_abs, abs_of_nonneg (hqnonneg x hx)]
    exact (le_mul_of_one_le_left (hqnonneg x hx) (by norm_num : (1 : ℝ) ≤ 2)).trans
      (hpoint x hx)
  have hqint : IntervalIntegrable q volume a b := by
    rw [intervalIntegrable_iff, uIoc_of_le hab]
    exact hqintOn.mono_set Set.Ioc_subset_Icc_self
  have hgintI : IntervalIntegrable g volume a b := by
    rw [intervalIntegrable_iff, uIoc_of_le hab]
    exact hgint.mono_set Set.Ioc_subset_Icc_self
  have hmono : 2 * ∫ x in a..b, q x ≤ ∫ x in a..b, g x := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_mono_on hab (hqint.const_mul 2) hgintI
    exact hpoint
  have hlogF : (∫ x in a..b, F₁ x / F x) =
      Real.log (F b) - Real.log (F a) := by
    calc
      (∫ x in a..b, F₁ x / F x) =
          ∫ x in a..b, deriv (fun y ↦ Real.log (F y)) x := by
        apply intervalIntegral.integral_congr
        intro x hx
        exact ((hF x).log
          (hFpos x (by simpa [uIcc_of_le hab] using hx)).ne').deriv.symm
      _ = Real.log (F b) - Real.log (F a) := by
        apply intervalIntegral.integral_deriv_eq_sub' _ rfl
        · intro x hx
          exact ((hF x).log
            (hFpos x (by simpa [uIcc_of_le hab] using hx)).ne').differentiableAt
        · have hc : ContinuousOn (fun x ↦ F₁ x / F x) (uIcc a b) := by
            apply ContinuousOn.div hF₁cont.continuousOn hFcont.continuousOn
            intro x hx
            exact (hFpos x (by simpa [uIcc_of_le hab] using hx)).ne'
          apply hc.congr
          intro x hx
          exact ((hF x).log
            (hFpos x (by simpa [uIcc_of_le hab] using hx)).ne').deriv
  have hlogF₁ : (∫ x in a..b, F₂ x / F₁ x) =
      Real.log (F₁ b) - Real.log (F₁ a) := by
    calc
      (∫ x in a..b, F₂ x / F₁ x) =
          ∫ x in a..b, deriv (fun y ↦ Real.log (F₁ y)) x := by
        apply intervalIntegral.integral_congr
        intro x hx
        exact ((hF₁ x).log
          (hF₁pos x (by simpa [uIcc_of_le hab] using hx)).ne').deriv.symm
      _ = Real.log (F₁ b) - Real.log (F₁ a) := by
        apply intervalIntegral.integral_deriv_eq_sub' _ rfl
        · intro x hx
          exact ((hF₁ x).log
            (hF₁pos x (by simpa [uIcc_of_le hab] using hx)).ne').differentiableAt
        · have hc : ContinuousOn (fun x ↦ F₂ x / F₁ x) (uIcc a b) := by
            apply ContinuousOn.div hF₂cont.continuousOn hF₁cont.continuousOn
            intro x hx
            exact (hF₁pos x (by simpa [uIcc_of_le hab] using hx)).ne'
          apply hc.congr
          intro x hx
          exact ((hF₁ x).log
            (hF₁pos x (by simpa [uIcc_of_le hab] using hx)).ne').deriv
  refine ⟨hqint, hmono.trans_eq ?_⟩
  change (∫ x in a..b, F₁ x / F x + F₂ x / F₁ x) = _
  have hr₁ : IntervalIntegrable (fun x ↦ F₁ x / F x) volume a b := by
    rw [intervalIntegrable_iff, uIoc_of_le hab]
    apply (hF₁cont.continuousOn.div hFcont.continuousOn (fun x hx ↦
      (hFpos x hx).ne')).integrableOn_Icc.mono_set
    exact Set.Ioc_subset_Icc_self
  have hr₂ : IntervalIntegrable (fun x ↦ F₂ x / F₁ x) volume a b := by
    rw [intervalIntegrable_iff, uIoc_of_le hab]
    apply (hF₂cont.continuousOn.div hF₁cont.continuousOn (fun x hx ↦
      (hF₁pos x hx).ne')).integrableOn_Icc.mono_set
    exact Set.Ioc_subset_Icc_self
  rw [intervalIntegral.integral_add hr₁ hr₂, hlogF, hlogF₁]

theorem test_logPolar_sqrt_energy_second_deriv_nonneg {f : ℂ → ℂ}
    (hf : IsEntire f) (x : ℝ)
    (hlog : 0 < Real.log (logarithmicMaximum f 1 (Real.exp x))) :
    0 ≤ iteratedDeriv 2
      (fun y ↦ √(cylindricalSquareEnergy
        (logPolarSlice f) (-Real.pi) Real.pi y)) x := by
  let H : ℝ → ℝ := cylindricalSquareEnergy
    (logPolarSlice f) (-Real.pi) Real.pi
  let H₁ : ℝ → ℝ := fun y ↦ ∫ θ in -Real.pi..Real.pi,
    2 * (logPolarSlice f y θ * logPolarX f y θ)
  let H₂ : ℝ → ℝ := fun y ↦ ∫ θ in -Real.pi..Real.pi,
    2 * (logPolarX f y θ ^ 2 + logPolarSlice f y θ * logPolarXX f y θ)
  let Ex : ℝ := ∫ θ in -Real.pi..Real.pi, logPolarX f x θ ^ 2
  let Et : ℝ := ∫ θ in -Real.pi..Real.pi, logPolarTheta f x θ ^ 2
  let F : ℝ := √(H x)
  have hH : ∀ y, HasDerivAt H (H₁ y) y := by
    intro y
    simpa only [H, H₁] using hasDerivAt_cylindricalSquareEnergy
      (continuous_uncurry_logPolarSlice hf) (continuous_logPolarX hf)
      (hasDerivAt_logPolarSlice_fst hf) (-Real.pi) Real.pi y
  have hH₁ : ∀ y, HasDerivAt H₁ (H₂ y) y := by
    intro y
    apply hasDerivAt_intervalIntegral_of_continuous_partial
        (F := fun s t ↦ 2 * (logPolarSlice f s t * logPolarX f s t))
        (F' := fun s t ↦
          2 * (logPolarX f s t ^ 2 + logPolarSlice f s t * logPolarXX f s t))
    · exact continuous_const.mul
        ((continuous_uncurry_logPolarSlice hf).mul (continuous_logPolarX hf))
    · exact continuous_const.mul
        ((continuous_logPolarX hf).pow 2 |>.add
          ((continuous_uncurry_logPolarSlice hf).mul (continuous_logPolarXX hf)))
    · intro s t
      simpa [pow_two] using
        ((hasDerivAt_logPolarSlice_fst hf s t).mul
          (hasDerivAt_logPolarX_fst hf s t)).const_mul (2 : ℝ)
  have hHpos : 0 < H x := by
    simpa only [H] using test_logPolar_energy_pos_of_log_max_pos hf x hlog
  have hFpos : 0 < F := Real.sqrt_pos.2 hHpos
  have hF2 : F ^ 2 = H x := Real.sq_sqrt hHpos.le
  have hsecond : iteratedDeriv 2 (fun y ↦ √(H y)) x =
      H₂ x / (2 * F) - H₁ x ^ 2 / (4 * F ^ 3) := by
    simpa only [F] using test_iteratedDeriv_two_sqrt hH hH₁ hHpos
  have hH2 : H₂ x = iteratedDeriv 2 H x := by
    symm
    simpa only [H, H₂] using iteratedDeriv_two_cylindricalSquareEnergy
      (continuous_uncurry_logPolarSlice hf) (continuous_logPolarX hf)
      (continuous_logPolarXX hf) (hasDerivAt_logPolarSlice_fst hf)
      (hasDerivAt_logPolarX_fst hf) (-Real.pi) Real.pi x
  have henergy : 2 * (Ex + Et) ≤ H₂ x := by
    rw [hH2]
    simpa only [H, Ex, Et] using logPolar_energy_second_deriv_ge hf x
  have hEt : 0 ≤ Et := by
    apply intervalIntegral.integral_nonneg (by linarith [Real.pi_pos])
    intro θ _
    exact sq_nonneg _
  have hcs : H₁ x ^ 2 ≤ 4 * H x * Ex := by
    have h := test_logPolar_energy_deriv_sq_le hf x
    rw [(hH x).deriv] at h
    simpa only [H, H₁, Ex] using h
  have hExH2 : 2 * Ex ≤ H₂ x := by linarith
  have hmul : 4 * H x * Ex ≤ 2 * H x * H₂ x := by
    have hfactor : 0 ≤ 2 * H x := mul_nonneg (by norm_num) hHpos.le
    have h := mul_le_mul_of_nonneg_left hExH2 hfactor
    nlinarith
  have hnum : 0 ≤ 2 * H₂ x * F ^ 2 - H₁ x ^ 2 := by
    rw [hF2]
    nlinarith [hcs.trans hmul]
  have hid : H₂ x / (2 * F) - H₁ x ^ 2 / (4 * F ^ 3) =
      (2 * H₂ x * F ^ 2 - H₁ x ^ 2) / (4 * F ^ 3) := by
    field_simp [hFpos.ne']
    ring
  change 0 ≤ iteratedDeriv 2 (fun y ↦ √(H y)) x
  rw [hsecond, hid]
  exact div_nonneg hnum (by positivity)

theorem test_hasDerivAt_sqrt_first_field
    {H H₁ H₂ : ℝ → ℝ}
    (hH : ∀ y, HasDerivAt H (H₁ y) y)
    (hH₁ : ∀ y, HasDerivAt H₁ (H₂ y) y)
    {x : ℝ} (hx : 0 < H x) :
    HasDerivAt (fun y ↦ H₁ y / (2 * √(H y)))
      (H₂ x / (2 * √(H x)) - H₁ x ^ 2 / (4 * (√(H x)) ^ 3)) x := by
  have hroot : 0 < √(H x) := Real.sqrt_pos.2 hx
  have hF : HasDerivAt (fun y ↦ √(H y))
      (H₁ x / (2 * √(H x))) x := (hH x).sqrt hx.ne'
  have hraw := (hH₁ x).div (hF.const_mul 2)
    (mul_ne_zero two_ne_zero hroot.ne')
  have hval :
      (H₂ x * (2 * √(H x)) -
          H₁ x * (2 * (H₁ x / (2 * √(H x))))) /
          (2 * √(H x)) ^ 2 =
        H₂ x / (2 * √(H x)) - H₁ x ^ 2 / (4 * (√(H x)) ^ 3) := by
    field_simp [hroot.ne']
    ring
  rw [hval] at hraw
  change HasDerivAt (fun y ↦ H₁ y / (2 * √(H y))) _ x at hraw
  exact hraw

theorem test_angularWidth_le_two_pi (s : Set ℂ) (r : ℝ) :
    angularWidth s r ≤ 2 * Real.pi := by
  have hsub : angularSection s r ⊆ Set.Ioo (-Real.pi) Real.pi := fun _ h ↦ h.1
  have htop : volume (Set.Ioo (-Real.pi) Real.pi) ≠ ∞ :=
    ne_of_lt measure_Ioo_lt_top
  calc
    angularWidth s r = volume.real (angularSection s r) := rfl
    _ ≤ volume.real (Set.Ioo (-Real.pi) Real.pi) := measureReal_mono hsub htop
    _ = 2 * Real.pi := by
      rw [measureReal_def, Real.volume_Ioo]
      simp only [sub_neg_eq_add,
        ENNReal.toReal_ofReal (by positivity : 0 ≤ Real.pi + Real.pi)]
      ring

noncomputable def test_logPolarEnergy (f : ℂ → ℂ) (x : ℝ) : ℝ :=
  cylindricalSquareEnergy (logPolarSlice f) (-Real.pi) Real.pi x

noncomputable def test_logPolarEnergyFirst (f : ℂ → ℂ) (x : ℝ) : ℝ :=
  ∫ θ in -Real.pi..Real.pi, 2 * (logPolarSlice f x θ * logPolarX f x θ)

noncomputable def test_logPolarEnergySecond (f : ℂ → ℂ) (x : ℝ) : ℝ :=
  ∫ θ in -Real.pi..Real.pi,
    2 * (logPolarX f x θ ^ 2 + logPolarSlice f x θ * logPolarXX f x θ)

noncomputable def test_logPolarSqrtEnergy (f : ℂ → ℂ) (x : ℝ) : ℝ :=
  √(test_logPolarEnergy f x)

noncomputable def test_logPolarSqrtEnergyFirst (f : ℂ → ℂ) (x : ℝ) : ℝ :=
  test_logPolarEnergyFirst f x / (2 * test_logPolarSqrtEnergy f x)

noncomputable def test_logPolarSqrtEnergySecond (f : ℂ → ℂ) (x : ℝ) : ℝ :=
  test_logPolarEnergySecond f x / (2 * test_logPolarSqrtEnergy f x) -
    test_logPolarEnergyFirst f x ^ 2 / (4 * test_logPolarSqrtEnergy f x ^ 3)

theorem test_hasDerivAt_logPolarEnergy {f : ℂ → ℂ} (hf : IsEntire f) (x : ℝ) :
    HasDerivAt (test_logPolarEnergy f) (test_logPolarEnergyFirst f x) x := by
  exact hasDerivAt_cylindricalSquareEnergy
    (continuous_uncurry_logPolarSlice hf) (continuous_logPolarX hf)
    (hasDerivAt_logPolarSlice_fst hf) (-Real.pi) Real.pi x

theorem test_hasDerivAt_logPolarEnergyFirst {f : ℂ → ℂ}
    (hf : IsEntire f) (x : ℝ) :
    HasDerivAt (test_logPolarEnergyFirst f) (test_logPolarEnergySecond f x) x := by
  apply hasDerivAt_intervalIntegral_of_continuous_partial
      (F := fun s t ↦ 2 * (logPolarSlice f s t * logPolarX f s t))
      (F' := fun s t ↦
        2 * (logPolarX f s t ^ 2 + logPolarSlice f s t * logPolarXX f s t))
  · exact continuous_const.mul
      ((continuous_uncurry_logPolarSlice hf).mul (continuous_logPolarX hf))
  · exact continuous_const.mul
      ((continuous_logPolarX hf).pow 2 |>.add
        ((continuous_uncurry_logPolarSlice hf).mul (continuous_logPolarXX hf)))
  · intro s t
    simpa [pow_two] using
      ((hasDerivAt_logPolarSlice_fst hf s t).mul
        (hasDerivAt_logPolarX_fst hf s t)).const_mul (2 : ℝ)

theorem test_continuous_logPolarEnergy {f : ℂ → ℂ} (hf : IsEntire f) :
    Continuous (test_logPolarEnergy f) :=
  continuous_iff_continuousAt.mpr fun x ↦ (test_hasDerivAt_logPolarEnergy hf x).continuousAt

theorem test_continuous_logPolarEnergyFirst {f : ℂ → ℂ} (hf : IsEntire f) :
    Continuous (test_logPolarEnergyFirst f) :=
  continuous_iff_continuousAt.mpr fun x ↦
    (test_hasDerivAt_logPolarEnergyFirst hf x).continuousAt

theorem test_continuous_logPolarEnergySecond {f : ℂ → ℂ} (hf : IsEntire f) :
    Continuous (test_logPolarEnergySecond f) := by
  let K : ℝ → ℝ → ℝ := fun x θ ↦
    2 * (logPolarX f x θ ^ 2 + logPolarSlice f x θ * logPolarXX f x θ)
  have hK : Continuous (Function.uncurry K) := by
    exact continuous_const.mul
      ((continuous_logPolarX hf).pow 2 |>.add
        ((continuous_uncurry_logPolarSlice hf).mul (continuous_logPolarXX hf)))
  have hc := continuous_parametric_integral_of_continuous
    (f := K) (μ := volume) hK
      (isCompact_Icc : IsCompact (Set.Icc (-Real.pi) Real.pi))
  have heq : test_logPolarEnergySecond f =
      fun x ↦ ∫ θ in Set.Icc (-Real.pi) Real.pi, K x θ := by
    funext x
    unfold test_logPolarEnergySecond
    rw [intervalIntegral.integral_of_le (by linarith [Real.pi_pos])]
    rw [setIntegral_congr_set Ioc_ae_eq_Icc]
  rw [heq]
  exact hc

theorem test_continuous_logPolarSqrtEnergy {f : ℂ → ℂ} (hf : IsEntire f) :
    Continuous (test_logPolarSqrtEnergy f) := by
  exact Real.continuous_sqrt.comp (test_continuous_logPolarEnergy hf)

theorem test_hasDerivAt_logPolarSqrtEnergy {f : ℂ → ℂ}
    (hf : IsEntire f) {x : ℝ}
    (hlog : 0 < Real.log (logarithmicMaximum f 1 (Real.exp x))) :
    HasDerivAt (test_logPolarSqrtEnergy f) (test_logPolarSqrtEnergyFirst f x) x := by
  have hpos : 0 < test_logPolarEnergy f x := by
    simpa only [test_logPolarEnergy] using
      test_logPolar_energy_pos_of_log_max_pos hf x hlog
  unfold test_logPolarSqrtEnergyFirst test_logPolarSqrtEnergy
  exact (test_hasDerivAt_logPolarEnergy hf x).sqrt hpos.ne'

theorem test_hasDerivAt_logPolarSqrtEnergyFirst {f : ℂ → ℂ}
    (hf : IsEntire f) {x : ℝ}
    (hlog : 0 < Real.log (logarithmicMaximum f 1 (Real.exp x))) :
    HasDerivAt (test_logPolarSqrtEnergyFirst f)
      (test_logPolarSqrtEnergySecond f x) x := by
  have hpos : 0 < test_logPolarEnergy f x := by
    simpa only [test_logPolarEnergy] using
      test_logPolar_energy_pos_of_log_max_pos hf x hlog
  unfold test_logPolarSqrtEnergyFirst test_logPolarSqrtEnergySecond
    test_logPolarSqrtEnergy
  exact test_hasDerivAt_sqrt_first_field
    (test_hasDerivAt_logPolarEnergy hf) (test_hasDerivAt_logPolarEnergyFirst hf) hpos

theorem test_logPolarSqrtEnergySecond_eq_iteratedDeriv {f : ℂ → ℂ}
    (hf : IsEntire f) {x : ℝ}
    (hlog : 0 < Real.log (logarithmicMaximum f 1 (Real.exp x))) :
    test_logPolarSqrtEnergySecond f x =
      iteratedDeriv 2 (test_logPolarSqrtEnergy f) x := by
  have hpos : 0 < test_logPolarEnergy f x := by
    simpa only [test_logPolarEnergy] using
      test_logPolar_energy_pos_of_log_max_pos hf x hlog
  symm
  unfold test_logPolarSqrtEnergy test_logPolarSqrtEnergySecond
  exact test_iteratedDeriv_two_sqrt
    (test_hasDerivAt_logPolarEnergy hf) (test_hasDerivAt_logPolarEnergyFirst hf) hpos

theorem test_logPolarSqrtEnergySecond_nonneg {f : ℂ → ℂ}
    (hf : IsEntire f) {x : ℝ}
    (hlog : 0 < Real.log (logarithmicMaximum f 1 (Real.exp x))) :
    0 ≤ test_logPolarSqrtEnergySecond f x := by
  rw [test_logPolarSqrtEnergySecond_eq_iteratedDeriv hf hlog]
  unfold test_logPolarSqrtEnergy test_logPolarEnergy
  exact test_logPolar_sqrt_energy_second_deriv_nonneg hf x hlog

noncomputable def test_reducedReciprocalLogWidth (f : ℂ → ℂ) (x : ℝ) : ℝ :=
  if angularWidth (exceptionalSet f 1) (Real.exp x) < 2 * Real.pi then
    (angularWidth (exceptionalSet f 1) (Real.exp x))⁻¹ else 0

theorem test_measurable_reducedReciprocalLogWidth {f : ℂ → ℂ}
    (hf : Continuous f) : Measurable (test_reducedReciprocalLogWidth f) := by
  unfold test_reducedReciprocalLogWidth
  apply Measurable.ite
  · exact measurableSet_lt
      ((measurable_angularWidth (measurableSet_exceptionalSet hf 1)).comp
        Real.measurable_exp) measurable_const
  · exact (show Measurable (fun x ↦
      angularWidth (exceptionalSet f 1) (Real.exp x)) from
        (measurable_angularWidth (measurableSet_exceptionalSet hf 1)).comp
          Real.measurable_exp).inv
  · exact measurable_const

theorem test_reducedReciprocalLogWidth_nonneg {f : ℂ → ℂ} {x : ℝ}
    (hΘ : 0 < angularWidth (exceptionalSet f 1) (Real.exp x)) :
    0 ≤ test_reducedReciprocalLogWidth f x := by
  unfold test_reducedReciprocalLogWidth
  split_ifs
  · exact inv_nonneg.mpr hΘ.le
  · exact le_rfl

theorem test_reducedReciprocalLogWidth_curvature {f : ℂ → ℂ}
    (hf : IsEntire f) {x : ℝ}
    (hlog : 0 < Real.log (logarithmicMaximum f 1 (Real.exp x))) :
    test_reducedReciprocalLogWidth f x ^ 2 * test_logPolarSqrtEnergy f x ≤
      test_logPolarSqrtEnergySecond f x := by
  by_cases hw : angularWidth (exceptionalSet f 1) (Real.exp x) < 2 * Real.pi
  · have h := test_logPolar_sqrt_energy_second_deriv_ge hf x hlog hw
    unfold test_reducedReciprocalLogWidth
    rw [if_pos hw]
    rw [test_logPolarSqrtEnergySecond_eq_iteratedDeriv hf hlog]
    unfold test_logPolarSqrtEnergy test_logPolarEnergy
    simpa only [inv_pow, div_eq_mul_inv, mul_comm] using h
  · unfold test_reducedReciprocalLogWidth
    rw [if_neg hw, zero_pow two_ne_zero, zero_mul]
    exact test_logPolarSqrtEnergySecond_nonneg hf hlog
#check ConvexOn.map_set_average_le

theorem test_jensen_fifth {u : ℝ → ℝ} (hu : Continuous u)
    (hun : ∀ x, 0 ≤ u x) :
    (((volume.real (Set.Ioc (-Real.pi) Real.pi))⁻¹ *
      ∫ x in Set.Ioc (-Real.pi) Real.pi, u x) ^ 5) ≤
      (volume.real (Set.Ioc (-Real.pi) Real.pi))⁻¹ *
        ∫ x in Set.Ioc (-Real.pi) Real.pi, u x ^ 5 := by
  let I : Set ℝ := Set.Ioc (-Real.pi) Real.pi
  have h0 : volume I ≠ 0 := by
    change volume (Set.Ioc (-Real.pi) Real.pi) ≠ 0
    rw [Real.volume_Ioc]
    rw [ne_eq, ENNReal.ofReal_eq_zero]
    linarith [Real.pi_pos]
  have ht : volume I ≠ ∞ := ne_of_lt measure_Ioc_lt_top
  have hJ := (convexOn_pow 5 : ConvexOn ℝ (Set.Ici 0) (fun x : ℝ ↦ x ^ 5)).map_set_average_le
    (continuousOn_pow 5) isClosed_Ici h0 ht
    (ae_of_all _ fun x ↦ hun x)
    (hu.integrableOn_Icc.mono_set (by
      intro x hx
      exact ⟨hx.1.le, hx.2⟩))
    ((hu.pow 5).integrableOn_Icc.mono_set (by
      intro x hx
      exact ⟨hx.1.le, hx.2⟩))
  simpa only [I, MeasureTheory.average_eq, MeasureTheory.measureReal_restrict_apply_univ,
    smul_eq_mul, Function.comp_apply] using hJ
#check MeasureTheory.MeasurePreserving.measure_preimage
#check MeasureTheory.MeasurePreserving.measure_preimage_emb
#check MeasureTheory.MeasurePreserving.map_eq
#check MeasureTheory.Measure.prod_prod
#check Real.volume_Icc
#check ENNReal.summable_coe
#check ENNReal.tsum_coe
#check one_add_mul_le_pow
#check pow_le_pow_right_of_le_one'
#check div_pow
#check Finset.sum_range_add_sum_Ico
#check Finset.sum_range_add_sum_Ico_comm
#check Finset.sum_Ico_add
#check add_pow

example (A : ℕ) (hA : 0 < A) :
    (((A : ℝ) / (A + 1 : ℕ)) ^ (4 * A)) ≤ 1 / 16 := by
  have hAreal : (0 : ℝ) < A := by exact_mod_cast hA
  have hbern : (2 : ℝ) ≤ (1 + 1 / (A : ℝ)) ^ A := by
    have h := one_add_mul_le_pow (a := 1 / (A : ℝ))
      (by
        have hnonneg : (0 : ℝ) ≤ 1 / A := by positivity
        linarith) A
    calc
      (2 : ℝ) = 1 + (A : ℝ) * (1 / (A : ℝ)) := by field_simp; norm_num
      _ ≤ (1 + 1 / (A : ℝ)) ^ A := h
  have hratio : ((A : ℝ) / (A + 1 : ℕ)) ^ A ≤ 1 / 2 := by
    rw [div_pow]
    have hden : (0 : ℝ) < ((A + 1 : ℕ) : ℝ) ^ A := by positivity
    rw [div_le_iff₀ hden]
    have hA_pow : (0 : ℝ) < ((A : ℝ) ^ A) := by positivity
    have hone : 1 + 1 / (A : ℝ) = ((A + 1 : ℕ) : ℝ) / (A : ℝ) := by
      push_cast
      field_simp
    rw [hone, div_pow] at hbern
    have hbern' : 2 * ((A : ℝ) ^ A) ≤ (((A + 1 : ℕ) : ℝ) ^ A) := by
      exact (le_div_iff₀ hA_pow).mp hbern
    nlinarith
  calc
    ((A : ℝ) / (A + 1 : ℕ)) ^ (4 * A) =
        (((A : ℝ) / (A + 1 : ℕ)) ^ A) ^ 4 := by rw [← pow_mul]; congr 1; omega
    _ ≤ (1 / 2 : ℝ) ^ 4 := by gcongr
    _ = 1 / 16 := by norm_num
