import ErdosProblems.Erdos321.AdaptiveRecurrence

namespace Erdos321

open Filter
open scoped Topology

/-- The elementary logarithmic ratio used to budget kernel errors along an
adaptive orbit. -/
noncomputable def orbitLogRatio (n : ℕ) : ℝ :=
  Real.log n / n

private theorem log_ratio_sixteen_le
    {y z : ℝ} (hy : 16 ≤ y) (hzy : 16 * y ≤ z) :
    Real.log z / z ≤ (Real.log y / y) / 8 := by
  have hypos : 0 < y := by linarith
  have h16ypos : 0 < 16 * y := by positivity
  have hzpos : 0 < z := lt_of_lt_of_le h16ypos hzy
  have hexp16y : Real.exp 1 ≤ 16 * y := by
    have he : Real.exp 1 < 3 := Real.exp_one_lt_three
    linarith
  have hexpz : Real.exp 1 ≤ z := hexp16y.trans hzy
  have hanti : Real.log z / z ≤ Real.log (16 * y) / (16 * y) :=
    Real.log_div_self_antitoneOn hexp16y hexpz hzy
  have hlog16 : Real.log (16 : ℝ) ≤ Real.log y := by
    exact Real.strictMonoOn_log.monotoneOn (by norm_num) hypos hy
  have hlogmul : Real.log (16 * y) = Real.log 16 + Real.log y :=
    Real.log_mul (by norm_num) (ne_of_gt hypos)
  have hmiddle : Real.log (16 * y) / (16 * y) ≤
      (Real.log y / y) / 8 := by
    rw [hlogmul]
    have hlogy0 : 0 ≤ Real.log y := Real.log_nonneg (by linarith)
    apply (div_le_iff₀ h16ypos).2
    field_simp [ne_of_gt hypos]
    nlinarith
  exact hanti.trans hmiddle

private theorem adaptive_internal_error_bound
    {C : ℝ} (hC : 0 ≤ C) {x y : ℕ}
    (hdata : AdaptiveCutoffData x) (hy : 64 ≤ y)
    (hstep : y ≤ adaptiveEndpoint x) :
    uniformKernelError C x ≤ (C + 2) * orbitLogRatio y := by
  let z := Real.log x
  have hxposNat : 0 < x := by
    have := hdata.logScale_sq_le
    have hL := hdata.logScale_ge_four
    nlinarith
  have hxpos : (0 : ℝ) < x := by exact_mod_cast hxposNat
  have hzpos : 0 < z := by
    dsimp [z]
    exact lt_of_lt_of_le zero_lt_one hdata.log_ge_one
  have hyposNat : 0 < y := by omega
  have hypos : (0 : ℝ) < y := by exact_mod_cast hyposNat
  have hyReal : (16 : ℝ) ≤ y := by exact_mod_cast (show 16 ≤ y by omega)
  have hylog1 : 1 ≤ Real.log (y : ℝ) := by
    apply (Real.le_log_iff_exp_le hypos).2
    have he : Real.exp 1 < 3 := Real.exp_one_lt_three
    exact he.le.trans (by exact_mod_cast (show 3 ≤ y by omega))
  have hq0 : 0 ≤ orbitLogRatio y := by
    dsimp [orbitLogRatio]
    positivity
  have hyL : y < adaptiveLogScale x :=
    lt_of_le_of_lt hstep hdata.endpoint_lt_scale
  have hLfloor : ((adaptiveLogScale x : ℕ) : ℝ) ≤ z / 16 := by
    dsimp [adaptiveLogScale, z]
    exact Nat.floor_le (by positivity)
  have hzy : (16 : ℝ) * y ≤ z := by
    have hyLreal : (y : ℝ) ≤ adaptiveLogScale x := by
      exact_mod_cast (Nat.le_of_lt hyL)
    nlinarith
  have hone : 1 / z ≤ orbitLogRatio y / 16 := by
    have hrecip : 1 / z ≤ 1 / (16 * (y : ℝ)) :=
      one_div_le_one_div_of_le (by positivity) hzy
    have hlogrecip : 1 / (16 * (y : ℝ)) ≤
        Real.log y / (16 * y) := by
      apply (div_le_div_iff_of_pos_right (by positivity : 0 < (16 : ℝ) * y)).2
      exact hylog1
    calc
      1 / z ≤ 1 / (16 * (y : ℝ)) := hrecip
      _ ≤ Real.log y / (16 * y) := hlogrecip
      _ = orbitLogRatio y / 16 := by
        dsimp [orbitLogRatio]
        ring
  have hqz : Real.log z / z ≤ orbitLogRatio y / 8 := by
    apply log_ratio_sixteen_le hyReal hzy
  have hexp : z ^ 3 / 6 ≤ (x : ℝ) := by
    have h := Real.pow_div_factorial_le_exp z (le_of_lt hzpos) 3
    norm_num at h
    rw [Real.exp_log hxpos] at h
    exact h
  have hcubic : z ^ 3 ≤ 6 * (x : ℝ) := by
    simpa [mul_comm] using
      (div_le_iff₀ (by norm_num : (0 : ℝ) < 6)).mp hexp
  have hzplus : z + 1 ≤ 2 * z := by linarith
  have hfirst12 : z * (z + 1) / (x : ℝ) ≤ 12 / z := by
    apply (div_le_div_iff₀ hxpos hzpos).2
    calc
      z * (z + 1) * z = z ^ 2 * (z + 1) := by ring
      _ ≤ z ^ 2 * (2 * z) :=
        mul_le_mul_of_nonneg_left hzplus (sq_nonneg z)
      _ = 2 * z ^ 3 := by ring
      _ ≤ 12 * (x : ℝ) := by nlinarith
  have hfirst : z * (z + 1) / (x : ℝ) ≤
      (3 / 4 : ℝ) * orbitLogRatio y := by
    calc
      z * (z + 1) / (x : ℝ) ≤ 12 / z := hfirst12
      _ = 12 * (1 / z) := by ring
      _ ≤ 12 * (orbitLogRatio y / 16) := by gcongr
      _ = (3 / 4 : ℝ) * orbitLogRatio y := by ring
  have hsecond : 16 * C / z ≤ C * orbitLogRatio y := by
    calc
      16 * C / z = (16 * C) * (1 / z) := by ring
      _ ≤ (16 * C) * (orbitLogRatio y / 16) := by
        exact mul_le_mul_of_nonneg_left hone (by positivity)
      _ = C * orbitLogRatio y := by ring
  have hlog4 : Real.log (4 : ℝ) ≤ 3 := by
    have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 4 by norm_num)
    norm_num at this ⊢
    exact this
  have hlog4nonneg : 0 ≤ Real.log (4 : ℝ) := Real.log_nonneg (by norm_num)
  have hthirdConst : Real.log 4 / z ≤
      (3 / 16 : ℝ) * orbitLogRatio y := by
    calc
      Real.log 4 / z = Real.log 4 * (1 / z) := by ring
      _ ≤ Real.log 4 * (orbitLogRatio y / 16) :=
        mul_le_mul_of_nonneg_left hone hlog4nonneg
      _ ≤ 3 * (orbitLogRatio y / 16) :=
        mul_le_mul_of_nonneg_right hlog4 (by positivity)
      _ = (3 / 16 : ℝ) * orbitLogRatio y := by ring
  have hthird : Real.log (4 * z) / z ≤
      (5 / 16 : ℝ) * orbitLogRatio y := by
    rw [Real.log_mul (by norm_num : (4 : ℝ) ≠ 0) (ne_of_gt hzpos)]
    calc
      (Real.log 4 + Real.log z) / z =
          Real.log 4 / z + Real.log z / z := by ring
      _ ≤ (3 / 16 : ℝ) * orbitLogRatio y + orbitLogRatio y / 8 :=
        add_le_add hthirdConst hqz
      _ = (5 / 16 : ℝ) * orbitLogRatio y := by ring
  change z * (z + 1) / (x : ℝ) + 16 * C / z +
      Real.log (4 * z) / z ≤ (C + 2) * orbitLogRatio y
  nlinarith [hfirst, hsecond, hthird, hq0]

private theorem adaptive_step_ratio_contract
    {x y : ℕ} (hdata : AdaptiveCutoffData x) (hy : 64 ≤ y)
    (hstep : y ≤ adaptiveEndpoint x) :
    orbitLogRatio x ≤ orbitLogRatio y / 8 := by
  have hxposNat : 0 < x := by
    have := hdata.logScale_sq_le
    have hL := hdata.logScale_ge_four
    nlinarith
  have hxpos : (0 : ℝ) < x := by exact_mod_cast hxposNat
  have hyL : y < adaptiveLogScale x :=
    lt_of_le_of_lt hstep hdata.endpoint_lt_scale
  have hLfloor : ((adaptiveLogScale x : ℕ) : ℝ) ≤ Real.log x / 16 := by
    dsimp [adaptiveLogScale]
    exact Nat.floor_le (by positivity)
  have h16log : (16 : ℝ) * y ≤ Real.log x := by
    have hyLreal : (y : ℝ) ≤ adaptiveLogScale x := by
      exact_mod_cast (Nat.le_of_lt hyL)
    nlinarith
  have hlogx : Real.log (x : ℝ) ≤ x := by
    have h := Real.log_le_sub_one_of_pos hxpos
    linarith
  have h16x : (16 : ℝ) * y ≤ x := h16log.trans hlogx
  exact log_ratio_sixteen_le (by exact_mod_cast (show 16 ≤ y by omega)) h16x

private theorem orbitLogRatio_nonneg {n : ℕ} (hn : 1 ≤ n) :
    0 ≤ orbitLogRatio n := by
  dsimp [orbitLogRatio]
  positivity

/-- On the eventual cutoff range the explicit kernel error is nonnegative. -/
theorem uniformKernelError_nonneg_of_cutoffData
    {C : ℝ} (hC : 0 ≤ C) {N : ℕ} (hdata : AdaptiveCutoffData N) :
    0 ≤ uniformKernelError C N := by
  have hLpos : 0 < Real.log N :=
    lt_of_lt_of_le zero_lt_one hdata.log_ge_one
  have hNpos : (0 : ℝ) < N := by
    have := hdata.logScale_sq_le
    have hL := hdata.logScale_ge_four
    exact_mod_cast (show 0 < N by nlinarith)
  have hlogArg : 0 ≤ Real.log (4 * Real.log N) :=
    Real.log_nonneg (by nlinarith [hdata.log_ge_one])
  dsimp [uniformKernelError]
  positivity

/-- For a reverse-listed adaptive orbit (terminal node first, root last), the
sum of all kernel errors is controlled by the terminal error and logarithmic
ratio. -/
theorem adaptive_reverseOrbit_error_sum_bound
    {C : ℝ} (hC : 0 ≤ C) {x : ℕ} {xs : List ℕ}
    (hlarge : ∀ n ∈ x :: xs, 64 ≤ n)
    (hdata : ∀ n ∈ x :: xs, AdaptiveCutoffData n)
    (hchain : List.IsChain
      (fun child parent => child ≤ adaptiveEndpoint parent) (x :: xs)) :
    (List.map (uniformKernelError C) (x :: xs)).sum ≤
      uniformKernelError C x + 2 * (C + 2) * orbitLogRatio x := by
  induction xs generalizing x with
  | nil =>
      simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
      have hq : 0 ≤ orbitLogRatio x :=
        orbitLogRatio_nonneg (by have := hlarge x (by simp); omega)
      have hK : 0 ≤ C + 2 := by linarith
      have : 0 ≤ 2 * (C + 2) * orbitLogRatio x := by positivity
      linarith
  | cons y ys ih =>
      have hstep : x ≤ adaptiveEndpoint y := (List.chain_cons.mp hchain).1
      have hchainTail : List.IsChain
          (fun child parent => child ≤ adaptiveEndpoint parent) (y :: ys) :=
        (List.chain_cons.mp hchain).2
      have hlargeTail : ∀ n ∈ y :: ys, 64 ≤ n := by
        intro n hn
        exact hlarge n (by simp [hn])
      have hdataTail : ∀ n ∈ y :: ys, AdaptiveCutoffData n := by
        intro n hn
        exact hdata n (by simp [hn])
      have htail := ih hlargeTail hdataTail hchainTail
      have hyData : AdaptiveCutoffData y := hdata y (by simp)
      have hxLarge : 64 ≤ x := hlarge x (by simp)
      have hedge := adaptive_internal_error_bound hC hyData hxLarge hstep
      have hratio := adaptive_step_ratio_contract hyData hxLarge hstep
      have hK : 0 ≤ C + 2 := by linarith
      have hqx : 0 ≤ orbitLogRatio x :=
        orbitLogRatio_nonneg (by omega)
      have hscaled :
          2 * (C + 2) * orbitLogRatio y ≤
            2 * (C + 2) * (orbitLogRatio x / 8) :=
        mul_le_mul_of_nonneg_left hratio (by positivity)
      simp only [List.map_cons, List.sum_cons] at htail ⊢
      nlinarith

/-- The logarithmic ratio itself tends to zero. -/
theorem tendsto_orbitLogRatio :
    Tendsto orbitLogRatio atTop (𝓝 0) := by
  have hreal : Tendsto (fun x : ℝ => Real.log x / x) atTop (𝓝 0) :=
    Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero
  change Tendsto (fun n : ℕ => Real.log (n : ℝ) / (n : ℝ)) atTop (𝓝 0)
  convert hreal.comp tendsto_natCast_atTop_atTop using 1 <;> rfl

/-- For every positive budget there is one terminal threshold which bounds the
sum of `uniformKernelError` along every adaptive recursion chain, independent
of the chain length.  The list is ordered from terminal node to root. -/
theorem exists_uniform_kernelError_orbit_budget
    {C δ : ℝ} (hC : 0 ≤ C) (hδ : 0 < δ) :
    ∃ A : ℕ, 64 ≤ A ∧
      (∀ n, A ≤ n → AdaptiveCutoffData n) ∧
      ∀ {x : ℕ} {xs : List ℕ},
        (∀ n ∈ x :: xs, A ≤ n) →
        List.IsChain (fun child parent => child ≤ adaptiveEndpoint parent)
          (x :: xs) →
        (List.map (uniformKernelError C) (x :: xs)).sum ≤ δ := by
  have hε : ∀ᶠ n : ℕ in atTop, uniformKernelError C n ≤ δ / 2 :=
    (tendsto_uniformKernelError C).eventually
      (Iic_mem_nhds (by linarith : (0 : ℝ) < δ / 2))
  have hratioLim : Tendsto
      (fun n : ℕ => 2 * (C + 2) * orbitLogRatio n) atTop (𝓝 0) := by
    have h := tendsto_orbitLogRatio.const_mul (2 * (C + 2))
    simpa using h
  have hratio : ∀ᶠ n : ℕ in atTop,
      2 * (C + 2) * orbitLogRatio n ≤ δ / 2 :=
    hratioLim.eventually
      (Iic_mem_nhds (by linarith : (0 : ℝ) < δ / 2))
  have hall : ∀ᶠ n : ℕ in atTop,
      AdaptiveCutoffData n ∧
      uniformKernelError C n ≤ δ / 2 ∧
      2 * (C + 2) * orbitLogRatio n ≤ δ / 2 :=
    eventually_adaptiveCutoffData.and (hε.and hratio)
  obtain ⟨A₀, hA₀⟩ := eventually_atTop.mp hall
  let A := max 64 A₀
  refine ⟨A, le_max_left _ _, ?_, ?_⟩
  · intro n hn
    exact (hA₀ n ((le_max_right 64 A₀).trans hn)).1
  · intro x xs hlarge hchain
    have h64 : ∀ n ∈ x :: xs, 64 ≤ n := by
      intro n hn
      exact (le_max_left 64 A₀).trans (hlarge n hn)
    have hdata : ∀ n ∈ x :: xs, AdaptiveCutoffData n := by
      intro n hn
      exact (hA₀ n ((le_max_right 64 A₀).trans (hlarge n hn))).1
    have hbound := adaptive_reverseOrbit_error_sum_bound hC h64 hdata hchain
    have hxA := hlarge x (by simp)
    have hxSmall := (hA₀ x ((le_max_right 64 A₀).trans hxA)).2
    linarith [hxSmall.1, hxSmall.2]

end Erdos321
