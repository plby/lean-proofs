import ErdosProblems.Erdos841.LinearForms

namespace Erdos841.LinearForms

open scoped BigOperators

noncomputable def structuredBoxThresholdControl
    {F : Type*} [Field F] [NumberField F] {r : ℕ}
    (B : ℕ) (M : ℝ) (alpha : Fin (r + 1) → F)
    (ell : Fin (r + 1) → ℂ) : ℝ :=
  (1000000000000000000000000000000 : ℝ) + Real.log M +
    Real.log ((2 * B + 1 : ℕ) : ℝ) +
    ∑ i, Height.logHeight₁ (alpha i) + ∑ i, ‖ell i‖

lemma log_boxAnalyticSlope_le_control
    {F : Type*} [Field F] [NumberField F] {r : ℕ}
    (B : ℕ) (M : ℝ) (alpha : Fin (r + 1) → F)
    (ell : Fin (r + 1) → ℂ) (hM : 1 ≤ M) :
    Real.log (boxAnalyticSlope B ell : ℝ) + 32 ≤
      structuredBoxThresholdControl B M alpha ell := by
  let S : ℝ := ∑ i, ‖ell i‖
  let E : ℝ := ∑ i : Fin r, ‖ell i.succ‖
  let A : ℝ := ((2 * B + 1 : ℕ) : ℝ)
  have hS : 0 ≤ S := by dsimp [S]; positivity
  have hE : 0 ≤ E := by dsimp [E]; positivity
  have hES : E ≤ S := by
    dsimp [E, S]
    rw [Fin.sum_univ_succ]
    exact le_add_of_nonneg_left (norm_nonneg _)
  have hA : 1 ≤ A := by
    dsimp [A]
    exact_mod_cast (show 1 ≤ 2 * B + 1 by omega)
  have hlogM : 0 ≤ Real.log M := Real.log_nonneg hM
  have hlogA : 0 ≤ Real.log A := Real.log_nonneg hA
  have hH : 0 ≤ ∑ i, Height.logHeight₁ (alpha i) := by positivity
  have hslopePos : (0 : ℝ) < boxAnalyticSlope B ell := by
    exact_mod_cast boxAnalyticSlope_pos B ell
  have hceil : ((Nat.ceil (3 + 2 * (B : ℝ) +
      2 * (B : ℝ) * E) : ℕ) : ℝ) <
      (3 + 2 * (B : ℝ) + 2 * (B : ℝ) * E) + 1 := by
    exact_mod_cast Nat.ceil_lt_add_one (by positivity :
      0 ≤ 3 + 2 * (B : ℝ) + 2 * (B : ℝ) * E)
  have hslope : (boxAnalyticSlope B ell : ℝ) ≤ A * (S + 5) := by
    rw [boxAnalyticSlope]
    push_cast
    have hraw : (Nat.ceil (3 + 2 * (B : ℝ) +
        2 * (B : ℝ) * E) : ℝ) + 1 ≤
        5 + 2 * (B : ℝ) + 2 * (B : ℝ) * E := by
      linarith
    calc
      (Nat.ceil (3 + 2 * (B : ℝ) +
          2 * (B : ℝ) * E) : ℝ) + 1 ≤
          5 + 2 * (B : ℝ) + 2 * (B : ℝ) * E := hraw
      _ ≤ A * (S + 5) := by
        dsimp [A]
        push_cast
        nlinarith [mul_nonneg (show (0 : ℝ) ≤ 2 * B by positivity)
          (sub_nonneg.mpr hES)]
  have hASpos : 0 < A * (S + 5) := mul_pos (lt_of_lt_of_le zero_lt_one hA) (by linarith)
  have hlogSlope : Real.log (boxAnalyticSlope B ell : ℝ) ≤
      Real.log A + Real.log (S + 5) := by
    calc
      Real.log (boxAnalyticSlope B ell : ℝ) ≤
          Real.log (A * (S + 5)) :=
        Real.log_le_log hslopePos hslope
      _ = Real.log A + Real.log (S + 5) := by
        rw [Real.log_mul (by positivity) (by positivity)]
  have hlogS : Real.log (S + 5) ≤ S + 4 := by
    exact (Real.log_le_sub_one_of_pos (by linarith : 0 < S + 5)).trans_eq (by ring)
  unfold structuredBoxThresholdControl
  dsimp [A, S] at hlogA ⊢
  linarith [hlogSlope, hlogS]


noncomputable def structuredBoxThresholdTotal
    {F : Type*} [Field F] [NumberField F] {r : ℕ}
    (B : ℕ) (M : ℝ) (alpha : Fin (r + 1) → F)
    (ell : Fin (r + 1) → ℂ) : ℝ :=
  let Halpha : ℝ := ∑ i, Height.logHeight₁ (alpha i)
  let cH : ℝ := 8 * (314 * (314 + 34) + 26) + Halpha +
    (314 * 9) * 8 * (Real.log ((2 * B + 1 : ℕ) : ℝ) + 32)
  let cC : ℝ := 2 + 312 + 8 + Real.log M + 81 * Halpha + cH
  let cV : ℝ := Real.log (boxAnalyticSlope B ell : ℝ) + 32
  let cFac : ℝ := 314 * (314 + 34)
  let cE : ℝ := 314 * 9
  let cLog : ℝ := 312 + cC + cE * cV + cFac + 321
  let cInner : ℝ := 24 + cC + cFac + 319 + cE * cV
  cLog + 2320 + 8 * cInner + 2 * Halpha + 2 * ∑ i, ‖ell i‖

noncomputable def structuredBoxThresholdPerturb
    {F : Type*} [Field F] [NumberField F] {r : ℕ}
    (B : ℕ) (M : ℝ) (alpha : Fin (r + 1) → F)
    (ell : Fin (r + 1) → ℂ) : ℝ :=
  let Halpha : ℝ := ∑ i, Height.logHeight₁ (alpha i)
  let cH : ℝ := 8 * (314 * (314 + 34) + 26) + Halpha +
    (314 * 9) * 8 * (Real.log ((2 * B + 1 : ℕ) : ℝ) + 32)
  let cC : ℝ := 2 + 312 + 8 + Real.log M + 81 * Halpha + cH
  let cV : ℝ := Real.log (boxAnalyticSlope B ell : ℝ) + 32
  let cE : ℝ := 314 * 9
  3956 + (312 + cC + cE * cV + 315 * (315 + 34) + 318 +
    2 * ∑ i, ‖ell i‖ + cV + 4)


theorem structuredBoxBoundaryBase_control_bound
    {F : Type*} [Field F] [NumberField F] {r : ℕ}
    (B : ℕ) (M : ℝ) (alpha : Fin (r + 1) → F)
    (ell : Fin (r + 1) → ℂ) (hM : 1 ≤ M) :
    let T := structuredBoxThresholdControl B M alpha ell
    0 ≤ structuredBoxBoundaryBase B M alpha ell ∧
      structuredBoxBoundaryBase B M alpha ell ≤ T ^ 5 := by
  dsimp only
  let Halpha : ℝ := ∑ i, Height.logHeight₁ (alpha i)
  let S : ℝ := ∑ i, ‖ell i‖
  let logB : ℝ := Real.log ((2 * B + 1 : ℕ) : ℝ)
  let logM : ℝ := Real.log M
  let cH : ℝ := 8 * (314 * (314 + 34) + 26) + Halpha +
    (314 * 9) * 8 * (logB + 32)
  let cC : ℝ := 2 + 312 + 8 + logM + 81 * Halpha + cH
  let cV : ℝ := Real.log (boxAnalyticSlope B ell : ℝ) + 32
  let cFac : ℝ := 314 * (314 + 34)
  let cE : ℝ := 314 * 9
  let cLog : ℝ := 312 + cC + cE * cV + cFac + 321
  let cInner : ℝ := 24 + cC + cFac + 319 + cE * cV
  let cBoundary : ℝ := cLog + 2320 + 8 * cInner + 2 * Halpha
  let T := structuredBoxThresholdControl B M alpha ell
  have hH : 0 ≤ Halpha := by dsimp [Halpha]; positivity
  have hS : 0 ≤ S := by dsimp [S]; positivity
  have hlogM : 0 ≤ logM := by dsimp [logM]; exact Real.log_nonneg hM
  have hlogB : 0 ≤ logB := by
    dsimp [logB]
    apply Real.log_nonneg
    exact_mod_cast (show 1 ≤ 2 * B + 1 by omega)
  have hTdef : T = 1000000000000000000000000000000 + logM + logB + Halpha + S := by
    simp [T, structuredBoxThresholdControl, logM, logB, Halpha, S]
  have hTlarge : (1000000000000000000000000000000 : ℝ) ≤ T := by rw [hTdef]; linarith
  have hTone : (1 : ℝ) ≤ T := by linarith
  have hTpos : 0 < T := lt_of_lt_of_le zero_lt_one hTone
  have hHT : Halpha ≤ T := by rw [hTdef]; linarith
  have hlogMT : logM ≤ T := by rw [hTdef]; linarith
  have hlogBT : logB ≤ T := by rw [hTdef]; linarith
  have hcV0 : 0 ≤ cV := by
    dsimp [cV]
    have hslope : (1 : ℝ) ≤ boxAnalyticSlope B ell := by
      exact_mod_cast (show 1 ≤ boxAnalyticSlope B ell by
        exact boxAnalyticSlope_pos B ell)
    positivity
  have hcVT : cV ≤ T := by
    dsimp [cV]
    exact log_boxAnalyticSlope_le_control B M alpha ell hM
  have hcH0 : 0 ≤ cH := by dsimp [cH]; positivity
  have hcH : cH ≤ T ^ 2 := by
    have hlin : cH ≤ 30000 * T := by dsimp [cH]; nlinarith
    have hquad : 30000 * T ≤ T ^ 2 := by
      nlinarith [mul_nonneg (sub_nonneg.mpr hTlarge) hTpos.le]
    exact hlin.trans hquad
  have hcC0 : 0 ≤ cC := by dsimp [cC]; positivity
  have hcC : cC ≤ T ^ 3 := by
    have hraw : cC ≤ T ^ 2 + 100 * T := by dsimp [cC]; nlinarith
    have hdom : T ^ 2 + 100 * T ≤ T ^ 3 := by
      nlinarith [mul_nonneg (sq_nonneg T) (sub_nonneg.mpr hTone),
        mul_nonneg (sub_nonneg.mpr hTlarge) hTpos.le]
    exact hraw.trans hdom
  have hcLog0 : 0 ≤ cLog := by dsimp [cLog, cE, cFac]; positivity
  have hcInner0 : 0 ≤ cInner := by dsimp [cInner, cE, cFac]; positivity
  have hcLog : cLog ≤ T ^ 4 := by
    have hraw : cLog ≤ T ^ 3 + 3000 * T + 200000 := by
      dsimp [cLog, cE, cFac]; nlinarith
    have hdom : T ^ 3 + 3000 * T + 200000 ≤ T ^ 4 := by
      nlinarith [mul_nonneg (pow_nonneg hTpos.le 3) (sub_nonneg.mpr hTone),
        mul_nonneg (sub_nonneg.mpr hTlarge) hTpos.le]
    exact hraw.trans hdom
  have hcInner : cInner ≤ T ^ 4 := by
    have hraw : cInner ≤ T ^ 3 + 3000 * T + 200000 := by
      dsimp [cInner, cE, cFac]; nlinarith
    have hdom : T ^ 3 + 3000 * T + 200000 ≤ T ^ 4 := by
      nlinarith [mul_nonneg (pow_nonneg hTpos.le 3) (sub_nonneg.mpr hTone),
        mul_nonneg (sub_nonneg.mpr hTlarge) hTpos.le]
    exact hraw.trans hdom
  have hcBoundary0 : 0 ≤ cBoundary := by dsimp [cBoundary]; positivity
  have hcBoundary : cBoundary ≤ T ^ 5 := by
    have hraw : cBoundary ≤ 9 * T ^ 4 + 3 * T + 2320 := by
      dsimp [cBoundary]; nlinarith
    have hdom : 9 * T ^ 4 + 3 * T + 2320 ≤ T ^ 5 := by
      nlinarith [mul_nonneg (pow_nonneg hTpos.le 4)
          (sub_nonneg.mpr (hTlarge.trans' (by norm_num : (9 : ℝ) ≤ 1000000000000000000000000000000))),
        mul_nonneg (sub_nonneg.mpr hTlarge) hTpos.le]
    exact hraw.trans hdom
  change 0 ≤ cBoundary ∧ cBoundary ≤ T ^ 5
  exact ⟨hcBoundary0, hcBoundary⟩

theorem structuredBoxThreshold_extra_control_bounds
    {F : Type*} [Field F] [NumberField F] {r : ℕ}
    (B : ℕ) (M : ℝ) (alpha : Fin (r + 1) → F)
    (ell : Fin (r + 1) → ℂ) (hM : 1 ≤ M) :
    let T := structuredBoxThresholdControl B M alpha ell
    0 ≤ structuredBoxThresholdTotal B M alpha ell ∧
      structuredBoxThresholdTotal B M alpha ell ≤ T ^ 6 ∧
      0 ≤ structuredBoxThresholdPerturb B M alpha ell ∧
      structuredBoxThresholdPerturb B M alpha ell ≤ T ^ 7 := by
  dsimp only
  let Halpha : ℝ := ∑ i, Height.logHeight₁ (alpha i)
  let S : ℝ := ∑ i, ‖ell i‖
  let logB : ℝ := Real.log ((2 * B + 1 : ℕ) : ℝ)
  let logM : ℝ := Real.log M
  let cH : ℝ := 8 * (314 * (314 + 34) + 26) + Halpha +
    (314 * 9) * 8 * (logB + 32)
  let cC : ℝ := 2 + 312 + 8 + logM + 81 * Halpha + cH
  let cV : ℝ := Real.log (boxAnalyticSlope B ell : ℝ) + 32
  let cE : ℝ := 314 * 9
  let cCore : ℝ := 312 + cC + cE * cV + 315 * (315 + 34) +
    318 + 2 * S + cV + 4
  let cPerturb : ℝ := 3956 + cCore
  let T := structuredBoxThresholdControl B M alpha ell
  have hH : 0 ≤ Halpha := by dsimp [Halpha]; positivity
  have hS : 0 ≤ S := by dsimp [S]; positivity
  have hlogM : 0 ≤ logM := by dsimp [logM]; exact Real.log_nonneg hM
  have hlogB : 0 ≤ logB := by
    dsimp [logB]
    apply Real.log_nonneg
    exact_mod_cast (show 1 ≤ 2 * B + 1 by omega)
  have hTdef : T = 1000000000000000000000000000000 + logM + logB + Halpha + S := by
    simp [T, structuredBoxThresholdControl, logM, logB, Halpha, S]
  have hTlarge : (1000000000000000000000000000000 : ℝ) ≤ T := by rw [hTdef]; linarith
  have hTone : (1 : ℝ) ≤ T := by linarith
  have hTpos : 0 < T := lt_of_lt_of_le zero_lt_one hTone
  have hHT : Halpha ≤ T := by rw [hTdef]; linarith
  have hST : S ≤ T := by rw [hTdef]; linarith
  have hlogMT : logM ≤ T := by rw [hTdef]; linarith
  have hlogBT : logB ≤ T := by rw [hTdef]; linarith
  have hcV0 : 0 ≤ cV := by
    dsimp [cV]
    have hslope : (1 : ℝ) ≤ boxAnalyticSlope B ell := by
      exact_mod_cast (show 1 ≤ boxAnalyticSlope B ell by
        exact boxAnalyticSlope_pos B ell)
    positivity
  have hcVT : cV ≤ T := by
    dsimp [cV]
    exact log_boxAnalyticSlope_le_control B M alpha ell hM
  have hcH0 : 0 ≤ cH := by dsimp [cH]; positivity
  have hcH : cH ≤ T ^ 2 := by
    have hlin : cH ≤ 30000 * T := by dsimp [cH]; nlinarith
    have hquad : 30000 * T ≤ T ^ 2 := by
      nlinarith [mul_nonneg (sub_nonneg.mpr hTlarge) hTpos.le]
    exact hlin.trans hquad
  have hcC0 : 0 ≤ cC := by dsimp [cC]; positivity
  have hcC : cC ≤ T ^ 3 := by
    have hraw : cC ≤ T ^ 2 + 100 * T := by dsimp [cC]; nlinarith
    have hdom : T ^ 2 + 100 * T ≤ T ^ 3 := by
      nlinarith [mul_nonneg (sq_nonneg T) (sub_nonneg.mpr hTone),
        mul_nonneg (sub_nonneg.mpr hTlarge) hTpos.le]
    exact hraw.trans hdom
  have hcCore0 : 0 ≤ cCore := by dsimp [cCore, cE]; positivity
  have hcCore : cCore ≤ T ^ 6 := by
    have hraw : cCore ≤ T ^ 3 + 3000 * T + 200000 := by
      dsimp [cCore, cE]; nlinarith
    have hT3 : T ^ 3 ≤ T ^ 5 := pow_le_pow_right₀ hTone (by omega)
    have h3000 : 3000 * T ≤ T ^ 5 := by
      calc
        3000 * T ≤ T ^ 4 * T := by
          gcongr
          exact (by norm_num : (3000 : ℝ) ≤ 1000000000000000000000000000000).trans
            (hTlarge.trans (by simpa using
              (pow_le_pow_right₀ hTone (show (1 : ℕ) ≤ 4 by omega))))
        _ = T ^ 5 := by ring
    have hconst : (200000 : ℝ) ≤ T ^ 5 :=
      (by norm_num : (200000 : ℝ) ≤ 1000000000000000000000000000000).trans
        (hTlarge.trans (by simpa using
          (pow_le_pow_right₀ hTone (show (1 : ℕ) ≤ 5 by omega))))
    have hdom : T ^ 3 + 3000 * T + 200000 ≤ T ^ 6 := by
      calc
        T ^ 3 + 3000 * T + 200000 ≤ 3 * T ^ 5 := by linarith
        _ ≤ T * T ^ 5 := by gcongr <;> linarith
        _ = T ^ 6 := by ring
    exact hraw.trans hdom
  have hcPerturb0 : 0 ≤ cPerturb := by dsimp [cPerturb]; positivity
  have hcPerturb : cPerturb ≤ T ^ 7 := by
    have hraw : cPerturb ≤ T ^ 6 + 3956 := by dsimp [cPerturb]; linarith
    have hconst : (3956 : ℝ) ≤ T ^ 6 :=
      (by norm_num : (3956 : ℝ) ≤ 1000000000000000000000000000000).trans
        (hTlarge.trans (by simpa using
          (pow_le_pow_right₀ hTone (show (1 : ℕ) ≤ 6 by omega))))
    have hdom : T ^ 6 + 3956 ≤ T ^ 7 := by
      calc
        T ^ 6 + 3956 ≤ 2 * T ^ 6 := by linarith
        _ ≤ T * T ^ 6 := by gcongr <;> linarith
        _ = T ^ 7 := by ring
    exact hraw.trans hdom
  obtain ⟨hboundary0, hboundary⟩ :=
    structuredBoxBoundaryBase_control_bound B M alpha ell hM
  have hcTotal0 : 0 ≤ structuredBoxThresholdTotal B M alpha ell := by
    unfold structuredBoxThresholdTotal
    positivity
  have hcTotal : structuredBoxThresholdTotal B M alpha ell ≤ T ^ 6 := by
    have hraw : structuredBoxThresholdTotal B M alpha ell ≤ T ^ 5 + 2 * T := by
      rw [show structuredBoxThresholdTotal B M alpha ell =
          structuredBoxBoundaryBase B M alpha ell + 2 * S by
        simp [structuredBoxThresholdTotal, structuredBoxBoundaryBase,
          Halpha, S, logM, logB]]
      nlinarith
    have hdom : T ^ 5 + 2 * T ≤ T ^ 6 := by
      nlinarith [mul_nonneg (pow_nonneg hTpos.le 5) (sub_nonneg.mpr hTone),
        mul_nonneg (sub_nonneg.mpr hTlarge) hTpos.le]
    exact hraw.trans hdom
  change 0 ≤ structuredBoxThresholdTotal B M alpha ell ∧
    structuredBoxThresholdTotal B M alpha ell ≤ T ^ 6 ∧
    0 ≤ cPerturb ∧ cPerturb ≤ T ^ 7
  exact ⟨hcTotal0, hcTotal, hcPerturb0, hcPerturb⟩

theorem structuredBoxMasterL_control_bound
    {F : Type*} [Field F] [NumberField F] {r : ℕ}
    (B : ℕ) (M : ℝ) (alpha : Fin (r + 1) → F)
    (ell : Fin (r + 1) → ℂ) (hM : 1 ≤ M) :
    let T := structuredBoxThresholdControl B M alpha ell
    let L := structuredBoxMasterL B M alpha ell
    1 ≤ T ∧ 4 ≤ L ∧ 1 ≤ Real.log (L : ℝ) ∧
      (L : ℝ) ≤ T ^ 14 ∧ Real.log (L : ℝ) ≤ T ^ 14 := by
  dsimp only
  let S : ℝ := ∑ i, ‖ell i‖
  let X := structuredBoxMasterScale B M alpha ell
  let N := structuredBoxMasterN B M alpha ell
  let L := structuredBoxMasterL B M alpha ell
  let T := structuredBoxThresholdControl B M alpha ell
  have hS : 0 ≤ S := by dsimp [S]; positivity
  have hlogM : 0 ≤ Real.log M := Real.log_nonneg hM
  have hlogB : 0 ≤ Real.log ((2 * B + 1 : ℕ) : ℝ) := by
    apply Real.log_nonneg
    exact_mod_cast (show 1 ≤ 2 * B + 1 by omega)
  have hH : 0 ≤ ∑ i, Height.logHeight₁ (alpha i) := by positivity
  have hTlarge : (1000000000000000000000000000000 : ℝ) ≤ T := by
    dsimp [T, structuredBoxThresholdControl]
    linarith
  have hTone : (1 : ℝ) ≤ T := by linarith
  have hTpos : 0 < T := lt_of_lt_of_le zero_lt_one hTone
  have hST : S ≤ T := by
    dsimp [T, structuredBoxThresholdControl, S]
    linarith
  obtain ⟨hboundary0, hboundary⟩ :=
    structuredBoxBoundaryBase_control_bound B M alpha ell hM
  obtain ⟨hLfour, hlogLone, _hbig, _hdom, hNupperMaster⟩ :=
    structured_box_master_parameter B M alpha ell hM
  have hTle6 : T ≤ T ^ 6 := by
    simpa using (pow_le_pow_right₀ hTone (show (1 : ℕ) ≤ 6 by omega))
  have hX : X ≤ T ^ 6 := by
    dsimp [X, structuredBoxMasterScale]
    apply max_le
    · exact (show (2 : ℝ) ≤ T by linarith).trans hTle6
    apply max_le
    · have hc : (((314 ^ 9 * 314 * 16 : ℕ) + 1 : ℕ) : ℝ) ≤
          (1000000000000000000000000000000 : ℝ) := by norm_num
      exact hc.trans (hTlarge.trans hTle6)
    apply max_le
    · have h16 : 16 * structuredBoxBoundaryBase B M alpha ell ≤
          16 * T ^ 5 := mul_le_mul_of_nonneg_left hboundary (by norm_num)
      have h16T : 16 * T ^ 5 ≤ T ^ 6 := by
        calc
          16 * T ^ 5 ≤ T * T ^ 5 := by
            gcongr
            exact (by norm_num : (16 : ℝ) ≤ 1000000000000000000000000000000).trans hTlarge
          _ = T ^ 6 := by ring
      exact h16.trans h16T
    · have h64 : 64 * S ≤ 64 * T :=
        mul_le_mul_of_nonneg_left hST (by norm_num)
      have h64T5 : (64 : ℝ) ≤ T ^ 5 :=
        (by norm_num : (64 : ℝ) ≤ 1000000000000000000000000000000).trans
          (hTlarge.trans (by simpa using
            (pow_le_pow_right₀ hTone (show (1 : ℕ) ≤ 5 by omega))))
      have h64T : 64 * T ≤ T ^ 6 := by
        calc
          64 * T ≤ T ^ 5 * T := mul_le_mul_of_nonneg_right h64T5 hTpos.le
          _ = T ^ 6 := by ring
      simpa only [S] using h64.trans h64T
  have hNupper : (N : ℝ) < X + 1 := by simpa only [N, X] using hNupperMaster
  have hN0 : (0 : ℝ) ≤ N := by positivity
  have hN : (N : ℝ) ≤ T ^ 7 := by
    have hraw : (N : ℝ) ≤ T ^ 6 + 1 := by linarith
    have hone : (1 : ℝ) ≤ T ^ 6 :=
      pow_le_pow_right₀ hTone (show (0 : ℕ) ≤ 6 by omega)
    calc
      (N : ℝ) ≤ T ^ 6 + 1 := hraw
      _ ≤ 2 * T ^ 6 := by linarith
      _ ≤ T * T ^ 6 := by gcongr <;> linarith
      _ = T ^ 7 := by ring
  have hLdef : L = N ^ 2 := by rfl
  have hL : (L : ℝ) ≤ T ^ 14 := by
    rw [hLdef, Nat.cast_pow]
    have hpow := pow_le_pow_left₀ hN0 hN 2
    calc
      (N : ℝ) ^ 2 ≤ (T ^ 7) ^ 2 := hpow
      _ = T ^ 14 := by ring
  have hLpos : (0 : ℝ) < (L : ℝ) := by exact_mod_cast (by omega : 0 < L)
  have hlogL : Real.log (L : ℝ) ≤ T ^ 14 := by
    exact (Real.log_le_sub_one_of_pos hLpos).trans (by nlinarith [hL])
  exact ⟨hTone, hLfour, hlogLone, hL, hlogL⟩

theorem structuredBoxLogarithmicFormThreshold_at_master_lower
    {F : Type*} [Field F] [NumberField F] {r : ℕ}
    (B : ℕ) (M : ℝ) (alpha : Fin (r + 1) → F)
    (ell : Fin (r + 1) → ℂ) (hM : 1 ≤ M) :
    let T := structuredBoxThresholdControl B M alpha ell
    Real.exp (-(3 * T ^ 9900)) ≤
      structuredBoxLogarithmicFormThreshold B
        (structuredBoxMasterL B M alpha ell) M alpha ell := by
  dsimp only
  let L := structuredBoxMasterL B M alpha ell
  let T := structuredBoxThresholdControl B M alpha ell
  let cTotal := structuredBoxThresholdTotal B M alpha ell
  let cPerturb := structuredBoxThresholdPerturb B M alpha ell
  let Xmax : ℝ := 2 * cTotal *
    ((L : ℝ) ^ 346 * Real.log (L : ℝ) + (L : ℝ) ^ 347)
  let Qperturb : ℝ := cPerturb * (L : ℝ) ^ 694 * Real.log (L : ℝ)
  obtain ⟨hcTotal0, hcTotal, hcPerturb0, hcPerturb⟩ :=
    structuredBoxThreshold_extra_control_bounds B M alpha ell hM
  obtain ⟨hTone, _hLfour, hlogLone, hL, hlogL⟩ :=
    structuredBoxMasterL_control_bound B M alpha ell hM
  have hTpos : 0 < T := lt_of_lt_of_le zero_lt_one hTone
  have hL0 : (0 : ℝ) ≤ (L : ℝ) := by positivity
  have hlogL0 : 0 ≤ Real.log (L : ℝ) := zero_le_one.trans hlogLone
  have hL346 : (L : ℝ) ^ 346 ≤ T ^ (14 * 346) := by
    have hpow := pow_le_pow_left₀ hL0 hL 346
    calc
      (L : ℝ) ^ 346 ≤ (T ^ 14) ^ 346 := hpow
      _ = T ^ (14 * 346) := by ring
  have hL347 : (L : ℝ) ^ 347 ≤ T ^ (14 * 347) := by
    have hpow := pow_le_pow_left₀ hL0 hL 347
    calc
      (L : ℝ) ^ 347 ≤ (T ^ 14) ^ 347 := hpow
      _ = T ^ (14 * 347) := by ring
  have hL694 : (L : ℝ) ^ 694 ≤ T ^ (14 * 694) := by
    have hpow := pow_le_pow_left₀ hL0 hL 694
    calc
      (L : ℝ) ^ 694 ≤ (T ^ 14) ^ 694 := hpow
      _ = T ^ (14 * 694) := by ring
  have hXmax0 : 0 ≤ Xmax := by dsimp [Xmax]; positivity
  have hXmax : Xmax ≤ T ^ 5000 := by
    have hinner : (L : ℝ) ^ 346 * Real.log (L : ℝ) +
        (L : ℝ) ^ 347 ≤ 2 * T ^ 4858 := by
      calc
        (L : ℝ) ^ 346 * Real.log (L : ℝ) + (L : ℝ) ^ 347 ≤
            T ^ (14 * 346) * T ^ 14 + T ^ (14 * 347) := by gcongr
        _ = 2 * T ^ 4858 := by ring
    have hraw : Xmax ≤ 4 * T ^ 4864 := by
      dsimp [Xmax]
      calc
        2 * cTotal * ((L : ℝ) ^ 346 * Real.log (L : ℝ) +
            (L : ℝ) ^ 347) ≤ 2 * T ^ 6 * (2 * T ^ 4858) := by gcongr
        _ = 4 * T ^ 4864 := by ring
    have hpow4 : (4 : ℝ) ≤ T ^ 136 := by
      exact (by norm_num : (4 : ℝ) ≤ 1000000000000000000000000000000).trans
        ((show (1000000000000000000000000000000 : ℝ) ≤ T by
            dsimp [T, structuredBoxThresholdControl]
            have hlogM : 0 ≤ Real.log M := Real.log_nonneg hM
            have hlogB : 0 ≤ Real.log ((2 * B + 1 : ℕ) : ℝ) := by
              apply Real.log_nonneg
              exact_mod_cast (show 1 ≤ 2 * B + 1 by omega)
            have hH : 0 ≤ ∑ i, Height.logHeight₁ (alpha i) := by positivity
            have hS : 0 ≤ ∑ i, ‖ell i‖ := by positivity
            linarith).trans (by simpa using
              (pow_le_pow_right₀ hTone (show (1 : ℕ) ≤ 136 by omega))))
    exact hraw.trans (by
      calc
        4 * T ^ 4864 ≤ T ^ 136 * T ^ 4864 :=
          mul_le_mul_of_nonneg_right hpow4 (pow_nonneg hTpos.le _)
        _ = T ^ 5000 := by ring)
  have hQperturb0 : 0 ≤ Qperturb := by dsimp [Qperturb]; positivity
  have hQperturb : Qperturb ≤ T ^ 9800 := by
    have hraw : Qperturb ≤ T ^ 9737 := by
      dsimp [Qperturb]
      calc
        cPerturb * (L : ℝ) ^ 694 * Real.log (L : ℝ) ≤
            T ^ 7 * T ^ (14 * 694) * T ^ 14 := by gcongr
        _ = T ^ 9737 := by ring
    exact hraw.trans (pow_le_pow_right₀ hTone (by omega))
  have hlogTwo0 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hlogTwoUpper : Real.log 2 ≤ T ^ 9900 := by
    exact (Real.log_two_lt_d9.trans
      (by norm_num : (0.6931471808 : ℝ) < 1)).le.trans
      (by simpa using (pow_le_pow_right₀ hTone (show (0 : ℕ) ≤ 9900 by omega)))
  have hcost0 : 0 ≤ Xmax + Qperturb + Real.log 2 := by positivity
  have hcost : Xmax + Qperturb + Real.log 2 ≤ 3 * T ^ 9900 := by
    have hx' : Xmax ≤ T ^ 9900 :=
      hXmax.trans (pow_le_pow_right₀ hTone (by omega))
    have hq' : Qperturb ≤ T ^ 9900 :=
      hQperturb.trans (pow_le_pow_right₀ hTone (by omega))
    linarith
  have hthreshold :
      structuredBoxLogarithmicFormThreshold B L M alpha ell =
        Real.exp (-(Xmax + Qperturb + Real.log 2)) := by
    rw [structuredBoxLogarithmicFormThreshold]
    rw [min_eq_right]
    · rfl
    · apply Real.exp_le_one_iff.mpr
      change -(Xmax + Qperturb + Real.log 2) ≤ 0
      linarith
  change Real.exp (-(3 * T ^ 9900)) ≤
    structuredBoxLogarithmicFormThreshold B L M alpha ell
  rw [hthreshold]
  exact Real.exp_le_exp.mpr (by linarith)

end Erdos841.LinearForms
