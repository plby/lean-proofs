/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
import ErdosProblems.Erdos515.NestedDomains

/-!
# Boundary access in the Lewis--Rossi--Weitsman construction

This file proves the bounded-domain Phragmen--Lindelöf step used to control the distance to the
boundary of the nested sublevel domains.  Everything is stated for the finite continuous notion
of subharmonicity developed in `Subharmonic.lean`.
-/

open Filter MeasureTheory Metric Real Set Topology

namespace Erdos515

/-- The average of squared complex norm on a circle.  This elementary identity supplies the
strict quadratic perturbation in the weak maximum principle below. -/
lemma circleAverage_normSq (c : ℂ) (R : ℝ) :
    circleAverage Complex.normSq c R = Complex.normSq c + R ^ 2 := by
  rw [circleAverage_def]
  simp only [smul_eq_mul, Complex.normSq_apply, circleMap, Complex.add_re,
    Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.exp_re, Complex.exp_im, Complex.I_re, Complex.I_im, zero_mul, sub_zero, add_zero,
    mul_zero, mul_one, Real.exp_zero, one_mul]
  have hcos : IntervalIntegrable (fun x : ℝ ↦ Real.cos x) volume 0 (2 * π) :=
    Real.continuous_cos.intervalIntegrable _ _
  have hsin : IntervalIntegrable (fun x : ℝ ↦ Real.sin x) volume 0 (2 * π) :=
    Real.continuous_sin.intervalIntegrable _ _
  rw [show (fun x : ℝ ↦
      (c.re + R * Real.cos x) * (c.re + R * Real.cos x) +
        (c.im + R * Real.sin x) * (c.im + R * Real.sin x)) =
      (fun x ↦ (c.re ^ 2 + c.im ^ 2) +
        (2 * c.re * R) * Real.cos x + (2 * c.im * R) * Real.sin x +
        R ^ 2 * (Real.cos x ^ 2 + Real.sin x ^ 2)) by
      funext x
      ring]
  simp_rw [Real.cos_sq_add_sin_sq]
  have hA : IntervalIntegrable (fun _ : ℝ ↦ c.re ^ 2 + c.im ^ 2) volume 0 (2 * π) :=
    intervalIntegrable_const
  have hB : IntervalIntegrable (fun x : ℝ ↦ (2 * c.re * R) * Real.cos x)
      volume 0 (2 * π) := hcos.const_mul _
  have hC : IntervalIntegrable (fun x : ℝ ↦ (2 * c.im * R) * Real.sin x)
      volume 0 (2 * π) := hsin.const_mul _
  have hD : IntervalIntegrable (fun _ : ℝ ↦ R ^ 2 * 1) volume 0 (2 * π) :=
    intervalIntegrable_const
  rw [intervalIntegral.integral_add (hA.add hB |>.add hC) hD,
    intervalIntegral.integral_add (hA.add hB) hC,
    intervalIntegral.integral_add hA hB]
  simp
  field_simp [Real.pi_ne_zero]

/-- Weak maximum principle on a bounded open set whose closure remains in the ambient domain.

The proof uses the strict perturbation `u z + ε * normSq z`.  At an interior maximum its circle
average is smaller by the positive amount `ε * R²`, contradicting the submean inequality. -/
lemma SubharmonicOn.le_on_bounded_open_of_frontier_le {u : ℂ → ℝ} {Omega V : Set ℂ}
    (hu : SubharmonicOn u Omega) (hVopen : IsOpen V) (hVbounded : Bornology.IsBounded V)
    (hVclosure : closure V ⊆ Omega) {M : ℝ}
    (hfront : ∀ z ∈ frontier V, u z ≤ M) :
    ∀ z ∈ V, u z ≤ M := by
  intro z hz
  by_contra hnle
  have hzgt : M < u z := lt_of_not_ge hnle
  have hcompact : IsCompact (closure V) :=
    Metric.isCompact_iff_isClosed_bounded.mpr ⟨isClosed_closure, hVbounded.closure⟩
  have hzclosure : z ∈ closure V := subset_closure hz
  obtain ⟨Bpoint, hBpoint, hBmax⟩ := hcompact.exists_isMaxOn
    ⟨z, hzclosure⟩ Complex.continuous_normSq.continuousOn
  let B : ℝ := Complex.normSq Bpoint
  have hBz : Complex.normSq z ≤ B := hBmax hzclosure
  have hBnonneg : 0 ≤ B := Complex.normSq_nonneg _
  let epsilon : ℝ := (u z - M) / (2 * (B + 1))
  have hepsilon : 0 < epsilon := by
    dsimp [epsilon]
    positivity
  let w : ℂ → ℝ := fun x ↦ u x + epsilon * Complex.normSq x
  have hwcont : ContinuousOn w (closure V) :=
    (hu.continuousOn.mono hVclosure).add
      (continuousOn_const.mul Complex.continuous_normSq.continuousOn)
  obtain ⟨x, hxclosure, hxmax⟩ := hcompact.exists_isMaxOn
    ⟨z, hzclosure⟩ hwcont
  have hwz_le : w z ≤ w x := hxmax hzclosure
  have hboundary_lt (y : ℂ) (hy : y ∈ frontier V) : w y < w z := by
    have hyclosure : y ∈ closure V := frontier_subset_closure hy
    have hBy : Complex.normSq y ≤ B := hBmax hyclosure
    have heB : epsilon * Complex.normSq y ≤ epsilon * B :=
      mul_le_mul_of_nonneg_left hBy hepsilon.le
    have hyu : u y ≤ M := hfront y hy
    have hgap : M + epsilon * B < u z := by
      dsimp [epsilon]
      have hden : 0 < 2 * (B + 1) := by positivity
      have hsmall : (u z - M) * B / (2 * (B + 1)) < u z - M := by
        rw [div_lt_iff₀ hden]
        nlinarith
      have hsmall' : (u z - M) / (2 * (B + 1)) * B < u z - M := by
        simpa [div_mul_eq_mul_div] using hsmall
      linarith
    dsimp [w]
    exact (add_le_add hyu heB).trans_lt
      (hgap.trans_le (le_add_of_nonneg_right (mul_nonneg hepsilon.le
        (Complex.normSq_nonneg z))))
  have hxV : x ∈ V := by
    rw [closure_eq_self_union_frontier] at hxclosure
    rcases hxclosure with hxV | hxfront
    · exact hxV
    · exact False.elim ((not_le_of_gt (hboundary_lt x hxfront)) hwz_le)
  obtain ⟨rho, hrho, hballOpen⟩ := Metric.isOpen_iff.mp hVopen x hxV
  let R : ℝ := rho / 2
  have hR : 0 < R := by dsimp [R]; linarith
  have hRrho : R < rho := by dsimp [R]; linarith
  have hballV : closedBall x R ⊆ V :=
    (closedBall_subset_ball hRrho).trans hballOpen
  have hballOmega : closedBall x R ⊆ Omega :=
    hballV.trans (subset_closure.trans hVclosure)
  have huI : CircleIntegrable u x R :=
    (hu.continuousOn.mono (sphere_subset_closedBall.trans hballOmega)).circleIntegrable hR.le
  have hnormI : CircleIntegrable Complex.normSq x R :=
    Complex.continuous_normSq.continuousOn.circleIntegrable hR.le
  have hrhsI : CircleIntegrable (fun y ↦ w x - epsilon • Complex.normSq y) x R :=
    by
      have hc : Continuous (fun y : ℂ ↦ w x - epsilon * Complex.normSq y) :=
        continuous_const.sub (continuous_const.mul Complex.continuous_normSq)
      simpa only [smul_eq_mul] using hc.continuousOn.circleIntegrable hR.le
  have hcircle : circleAverage u x R ≤
      circleAverage (fun y ↦ w x - epsilon • Complex.normSq y) x R := by
    apply circleAverage_mono huI hrhsI
    intro y hy
    have hySphere : y ∈ sphere x R := by simpa [abs_of_pos hR] using hy
    have hyV : y ∈ V := hballV (sphere_subset_closedBall hySphere)
    have hyclosure : y ∈ closure V := subset_closure hyV
    have hymax : w y ≤ w x := hxmax hyclosure
    dsimp [w] at hymax ⊢
    linarith
  have hsubmean : u x ≤ circleAverage u x R :=
    hu.submean (hVclosure (subset_closure hxV)) hR hballOmega
  have hstrict : w x ≤ w x - epsilon * R ^ 2 := by
    calc
      w x = u x + epsilon * Complex.normSq x := rfl
      _ ≤ circleAverage u x R + epsilon * Complex.normSq x :=
        add_le_add hsubmean le_rfl
      _ ≤ circleAverage (fun y ↦ w x - epsilon • Complex.normSq y) x R +
          epsilon * Complex.normSq x := add_le_add hcircle le_rfl
      _ = w x - epsilon * R ^ 2 := by
        have heNormI : CircleIntegrable (fun y ↦ epsilon • Complex.normSq y) x R :=
          by
            have hc : Continuous (fun y : ℂ ↦ epsilon * Complex.normSq y) :=
              continuous_const.mul Complex.continuous_normSq
            simpa only [smul_eq_mul] using hc.continuousOn.circleIntegrable hR.le
        rw [circleAverage_fun_sub (circleIntegrable_const (w x) x R) heNormI,
          circleAverage_const, circleAverage_fun_smul,
          circleAverage_normSq]
        simp only [smul_eq_mul]
        ring
  have : 0 < epsilon * R ^ 2 := mul_pos hepsilon (sq_pos_of_pos hR)
  linarith

/-- The logarithmic excess whose positive component is followed to the boundary. -/
noncomputable def radialExcess (u : ℂ → ℝ) (M n : ℝ) (z : ℂ) : ℝ :=
  u z - M - n * Real.log ‖z‖

lemma continuousOn_radialExcess {u : ℂ → ℝ} (hu : Continuous u) (M n : ℝ) :
    ContinuousOn (radialExcess u M n) ({0}ᶜ : Set ℂ) := by
  intro z hz
  have hznorm : ‖z‖ ≠ 0 := norm_ne_zero_iff.mpr (by simpa using hz)
  have hlog : ContinuousAt (fun x : ℂ ↦ Real.log ‖x‖) z := by
    change ContinuousAt (Real.log ∘ fun x : ℂ ↦ ‖x‖) z
    exact Real.continuousAt_log hznorm |>.comp continuous_norm.continuousAt
  have hcont : ContinuousAt (fun x : ℂ ↦ u x - M - n * Real.log ‖x‖) z :=
    (hu.continuousAt.sub continuousAt_const).sub (continuousAt_const.mul hlog)
  change ContinuousWithinAt (fun x : ℂ ↦ u x - M - n * Real.log ‖x‖) ({0}ᶜ : Set ℂ) z
  exact hcont.continuousWithinAt

/-- Subtracting a positive multiple of `log |z|` preserves subharmonicity away from the origin,
because that logarithm has the exact mean-value property on every disk avoiding the origin. -/
lemma subharmonicOn_radialExcess {u : ℂ → ℝ} (hu : Subharmonic u) (M : ℝ)
    {n : ℝ} (_hn : 0 ≤ n) :
    SubharmonicOn (radialExcess u M n) ({0}ᶜ : Set ℂ) := by
  refine ⟨isOpen_compl_singleton, continuousOn_radialExcess hu.continuous M n, ?_⟩
  intro c hc R hR hball
  have hballAbs : closedBall c |R| ⊆ ({0}ᶜ : Set ℂ) := by
    simpa [abs_of_pos hR] using hball
  have hlogavg : circleAverage (fun z : ℂ ↦ Real.log ‖z‖) c R = Real.log ‖c‖ := by
    exact analyticOnNhd_id.circleAverage_log_norm_of_ne_zero
      (fun z hz ↦ by simpa using hballAbs hz)
  have huI : CircleIntegrable u c R :=
    (hu.continuous.continuousOn.mono sphere_subset_closedBall).circleIntegrable hR.le
  have hconstI : CircleIntegrable (fun _ : ℂ ↦ M) c R := circleIntegrable_const M c R
  have hlogI : CircleIntegrable (fun z : ℂ ↦ Real.log ‖z‖) c R := by
    have hcont : ContinuousOn (fun z : ℂ ↦ Real.log ‖z‖) (sphere c R) := by
      intro z hz
      have hzball : z ∈ closedBall c R := sphere_subset_closedBall hz
      have hz0 : z ≠ 0 := by simpa using hball hzball
      exact_mod_cast ((Real.continuousAt_log (norm_ne_zero_iff.mpr hz0)).comp
        continuous_norm.continuousAt).continuousWithinAt
    exact hcont.circleIntegrable hR.le
  have hnlogI : CircleIntegrable (fun z : ℂ ↦ n • Real.log ‖z‖) c R := by
    have hcont : ContinuousOn (fun z : ℂ ↦ n * Real.log ‖z‖) (sphere c R) :=
      continuousOn_const.mul (by
        intro z hz
        have hzball : z ∈ closedBall c R := sphere_subset_closedBall hz
        have hz0 : z ≠ 0 := by simpa using hball hzball
        exact_mod_cast ((Real.continuousAt_log (norm_ne_zero_iff.mpr hz0)).comp
          continuous_norm.continuousAt).continuousWithinAt)
    simpa only [smul_eq_mul] using hcont.circleIntegrable hR.le
  have hqavg : circleAverage (radialExcess u M n) c R =
      circleAverage u c R - M - n * Real.log ‖c‖ := by
    change circleAverage (fun z ↦ (u z - M) - n * Real.log ‖z‖) c R = _
    have huMinusI : CircleIntegrable (fun z : ℂ ↦ u z - M) c R :=
      (hu.continuous.sub continuous_const).continuousOn.circleIntegrable hR.le
    rw [show (fun z : ℂ ↦ (u z - M) - n * Real.log ‖z‖) =
        (fun z ↦ (u z - M) - n • Real.log ‖z‖) by
          funext z; simp only [smul_eq_mul],
      circleAverage_fun_sub huMinusI hnlogI,
      circleAverage_fun_sub huI hconstI, circleAverage_const, circleAverage_fun_smul,
      hlogavg]
    simp only [smul_eq_mul]
  rw [hqavg]
  exact sub_le_sub_right (sub_le_sub_right (hu.submean c hR) M) _

/-- The open superlevel region used in the boundary-access argument. -/
def excessRegion (u : ℂ → ℝ) (M n epsilon : ℝ) (U : Set ℂ) : Set ℂ :=
  {z | z ∈ U ∧ 1 < ‖z‖ ∧ epsilon < radialExcess u M n z}

/-- Its connected component through the chosen exterior witness. -/
noncomputable def excessComponent (u : ℂ → ℝ) (M n epsilon : ℝ)
    (U : Set ℂ) (z0 : ℂ) : Set ℂ :=
  connectedComponentIn (excessRegion u M n epsilon U) z0

lemma isOpen_excessRegion {u : ℂ → ℝ} (hu : Continuous u) {U : Set ℂ}
    (hU : IsOpen U) (M n epsilon : ℝ) :
    IsOpen (excessRegion u M n epsilon U) := by
  have hqOpen : IsOpen (({0}ᶜ : Set ℂ) ∩
      radialExcess u M n ⁻¹' Ioi epsilon) :=
    (continuousOn_radialExcess hu M n).isOpen_inter_preimage
      isOpen_compl_singleton isOpen_Ioi
  have hbaseOpen : IsOpen (U ∩ {z : ℂ | 1 < ‖z‖}) :=
    hU.inter (isOpen_lt continuous_const continuous_norm)
  rw [show excessRegion u M n epsilon U =
      (U ∩ {z : ℂ | 1 < ‖z‖}) ∩
        (({0}ᶜ : Set ℂ) ∩ radialExcess u M n ⁻¹' Ioi epsilon) by
      ext z
      simp only [excessRegion, mem_ofPred_eq, mem_inter_iff, mem_compl_iff, mem_singleton_iff,
        mem_preimage, mem_Ioi]
      constructor
      · rintro ⟨hzU, hznorm, hq⟩
        exact ⟨⟨hzU, hznorm⟩,
          ⟨norm_ne_zero_iff.mp (ne_of_gt (zero_lt_one.trans hznorm)), hq⟩⟩
      · rintro ⟨⟨hzU, hznorm⟩, _hz0, hq⟩
        exact ⟨hzU, hznorm, hq⟩]
  exact hbaseOpen.inter hqOpen

/-- A point of an open set which lies in the closure of one of its connected components already
belongs to that component. -/
lemma mem_connectedComponentIn_of_mem_closure {S : Set ℂ} (hS : IsOpen S)
    {a z : ℂ} (hzClosure : z ∈ closure (connectedComponentIn S a)) (hzS : z ∈ S) :
    z ∈ connectedComponentIn S a := by
  let A := connectedComponentIn S a
  let C := connectedComponentIn S z
  have hCopen : IsOpen C := hS.connectedComponentIn
  have hzC : z ∈ C := mem_connectedComponentIn hzS
  obtain ⟨y, hyC, hyA⟩ :=
    mem_closure_iff_nhds.mp hzClosure C (hCopen.mem_nhds hzC)
  have hAC : A = C :=
    (connectedComponentIn_eq hyA).trans (connectedComponentIn_eq hyC).symm
  change z ∈ A
  rw [hAC]
  exact hzC

/-- The positive component of the logarithmic excess reaches the finite frontier of `U`.

This is the continuous Phragmen--Lindelöf boundary-access lemma in the exact form used by LRW.
The returned sequence stays outside the closed unit disk and satisfies the *strict* excess
inequality. -/
theorem positiveComponent_hits_frontier {u : ℂ → ℝ} (hu : Subharmonic u)
    {U : Set ℂ} (hUopen : IsOpen U) {A M n : ℝ} (hn : 0 < n)
    (hUbound : ∀ z ∈ U, u z < A)
    (hsphere : ∀ z : ℂ, ‖z‖ = 1 → u z ≤ M)
    {z0 : ℂ} (hz0U : z0 ∈ U) (hz0norm : 1 < ‖z0‖)
    (hz0excess : 0 < radialExcess u M n z0) :
    ∃ zeta ∈ frontier U, ∃ z : ℕ → ℂ,
      (∀ j, z j ∈ U ∧ 1 < ‖z j‖ ∧ 0 < radialExcess u M n (z j)) ∧
      Tendsto z atTop (nhds zeta) := by
  let epsilon : ℝ := radialExcess u M n z0 / 2
  have hepsilon : 0 < epsilon := half_pos hz0excess
  let W := excessRegion u M n epsilon U
  let V := excessComponent u M n epsilon U z0
  have hWopen : IsOpen W := isOpen_excessRegion hu.continuous hUopen M n epsilon
  have hz0W : z0 ∈ W := by
    refine ⟨hz0U, hz0norm, ?_⟩
    dsimp [epsilon]
    linarith
  have hz0V : z0 ∈ V := mem_connectedComponentIn hz0W
  have hVopen : IsOpen V := hWopen.connectedComponentIn
  have hVW : V ⊆ W := connectedComponentIn_subset W z0
  have hVbounded : Bornology.IsBounded V := by
    apply (isBounded_iff_forall_norm_le (s := V)).2
    refine ⟨Real.exp ((A - M - epsilon) / n), fun z hz ↦ ?_⟩
    have hzW := hVW hz
    have huz : u z < A := hUbound z hzW.1
    have hqz : epsilon < u z - M - n * Real.log ‖z‖ := hzW.2.2
    have hlog : Real.log ‖z‖ < (A - M - epsilon) / n := by
      rw [lt_div_iff₀ hn]
      linarith
    have hnormpos : 0 < ‖z‖ := zero_lt_one.trans hzW.2.1
    calc
      ‖z‖ = Real.exp (Real.log ‖z‖) := (Real.exp_log hnormpos).symm
      _ ≤ Real.exp ((A - M - epsilon) / n) :=
        (Real.exp_lt_exp.mpr hlog).le
  have hclosureNorm : ∀ z ∈ closure V, 1 ≤ ‖z‖ := by
    have hsubset : V ⊆ {z : ℂ | 1 ≤ ‖z‖} := fun z hz ↦ (hVW hz).2.1.le
    exact closure_minimal hsubset (isClosed_le continuous_const continuous_norm)
  have hclosurePunctured : closure V ⊆ ({0}ᶜ : Set ℂ) := by
    intro z hz
    have hzNorm := hclosureNorm z hz
    simpa [norm_ne_zero_iff] using (ne_of_gt (zero_lt_one.trans_le hzNorm))
  have hqsub : SubharmonicOn (radialExcess u M n) ({0}ᶜ : Set ℂ) :=
    subharmonicOn_radialExcess hu M hn.le
  have hhit : (closure V ∩ frontier U).Nonempty := by
    by_contra hempty
    have hno : ∀ z ∈ closure V, z ∉ frontier U := by
      intro z hzV hzU
      exact hempty ⟨z, hzV, hzU⟩
    have hfrontBound : ∀ z ∈ frontier V, radialExcess u M n z ≤ epsilon := by
      intro z hzfront
      have hzClosureV : z ∈ closure V := frontier_subset_closure hzfront
      have hzClosureW : z ∈ closure W := closure_mono hVW hzClosureV
      have hzClosureU : z ∈ closure U :=
        closure_mono (fun y hy ↦ (show y ∈ W from hy).1) hzClosureW
      have hzU : z ∈ U := by
        rw [closure_eq_self_union_frontier] at hzClosureU
        exact hzClosureU.resolve_right (hno z hzClosureV)
      have hznorm : 1 ≤ ‖z‖ := hclosureNorm z hzClosureV
      rcases hznorm.eq_or_lt with hnormeq | hnormgt
      · have hzu : u z ≤ M := hsphere z hnormeq.symm
        simp only [radialExcess, hnormeq.symm, Real.log_one, mul_zero, sub_zero]
        linarith
      · by_contra hqle
        have hqgt : epsilon < radialExcess u M n z := lt_of_not_ge hqle
        have hzW : z ∈ W := ⟨hzU, hnormgt, hqgt⟩
        have hzV : z ∈ V :=
          mem_connectedComponentIn_of_mem_closure hWopen hzClosureV hzW
        have hzBoth : z ∈ V ∩ frontier V := ⟨hzV, hzfront⟩
        rw [hVopen.inter_frontier_eq] at hzBoth
        exact hzBoth
    have hz0le : radialExcess u M n z0 ≤ epsilon :=
      hqsub.le_on_bounded_open_of_frontier_le hVopen hVbounded
        hclosurePunctured hfrontBound z0 hz0V
    dsimp [epsilon] at hz0le
    linarith
  obtain ⟨zeta, hzetaClosure, hzetaFrontier⟩ := hhit
  obtain ⟨z, hzV, hzlim⟩ := mem_closure_iff_seq_limit.mp hzetaClosure
  refine ⟨zeta, hzetaFrontier, z, ?_, hzlim⟩
  intro j
  have hzW := hVW (hzV j)
  exact ⟨hzW.1, hzW.2.1, hepsilon.trans hzW.2.2⟩

/-- Explicit distance consequence of `positiveComponent_hits_frontier`.

The term `norm base` is the cost of comparing distance from `base` with modulus about the
origin.  This is precisely estimate (28) in the mathematical proof. -/
theorem distance_to_frontier_le_exp {u : ℂ → ℝ} (hu : Subharmonic u)
    {U : Set ℂ} (hUopen : IsOpen U) {A M n : ℝ} (hn : 0 < n)
    (hUbound : ∀ z ∈ U, u z < A)
    (hsphere : ∀ z : ℂ, ‖z‖ = 1 → u z ≤ M)
    {z0 : ℂ} (hz0U : z0 ∈ U) (hz0norm : 1 < ‖z0‖)
    (hz0excess : 0 < radialExcess u M n z0) (base : ℂ) :
    infDist base (frontier U) ≤ ‖base‖ + Real.exp ((A - M) / n) := by
  obtain ⟨zeta, hzetaFrontier, z, hz, hzlim⟩ :=
    positiveComponent_hits_frontier hu hUopen hn hUbound hsphere
      hz0U hz0norm hz0excess
  have hzNormBound (j : ℕ) : ‖z j‖ ≤ Real.exp ((A - M) / n) := by
    have huz : u (z j) < A := hUbound (z j) (hz j).1
    have hqz : 0 < u (z j) - M - n * Real.log ‖z j‖ := (hz j).2.2
    have hlog : Real.log ‖z j‖ < (A - M) / n := by
      rw [lt_div_iff₀ hn]
      linarith
    have hnormpos : 0 < ‖z j‖ := zero_lt_one.trans (hz j).2.1
    calc
      ‖z j‖ = Real.exp (Real.log ‖z j‖) := (Real.exp_log hnormpos).symm
      _ ≤ Real.exp ((A - M) / n) := (Real.exp_lt_exp.mpr hlog).le
  have hnormLim : Tendsto (fun j ↦ ‖z j‖) atTop (nhds ‖zeta‖) :=
    continuous_norm.continuousAt.tendsto.comp hzlim
  have hzetaNorm : ‖zeta‖ ≤ Real.exp ((A - M) / n) :=
    le_of_tendsto hnormLim (Eventually.of_forall hzNormBound)
  calc
    infDist base (frontier U) ≤ dist base zeta := infDist_le_dist_of_mem hzetaFrontier
    _ ≤ dist base 0 + dist 0 zeta := dist_triangle _ _ _
    _ = ‖base‖ + ‖zeta‖ := by simp only [dist_zero_right, dist_zero_left]
    _ ≤ ‖base‖ + Real.exp ((A - M) / n) := add_le_add le_rfl hzetaNorm

/-! ## Sequential boundary-scale adapters -/

/-- A bound by `K_delta * exp (delta * height)` for every positive `delta` implies the usual
subexponential estimate.  This form is convenient immediately after
`distance_to_frontier_le_exp`, where the fixed additive terms are absorbed into `K_delta`. -/
lemma boundaryScale_subexponential_of_const_mul_exp
    {height boundaryScale : ℕ → ℝ}
    (hheight : Tendsto height atTop atTop)
    (hbound : ∀ delta : ℝ, 0 < delta → ∃ K : ℝ, 0 ≤ K ∧
      ∀ᶠ k in atTop,
        boundaryScale k ≤ K * Real.exp (delta * height k)) :
    ∀ epsilon : ℝ, 0 < epsilon → ∀ᶠ k in atTop,
      boundaryScale k ≤ Real.exp (epsilon * height k) := by
  intro epsilon hepsilon
  let delta := epsilon / 2
  have hdelta : 0 < delta := half_pos hepsilon
  obtain ⟨K, hK, hKbound⟩ := hbound delta hdelta
  let L := Real.log (max 1 K)
  have hmaxPos : 0 < max 1 K := lt_max_of_lt_left zero_lt_one
  have hLnonneg : 0 ≤ L := Real.log_nonneg (le_max_left 1 K)
  have hheightLarge : ∀ᶠ k in atTop, 2 * L / epsilon ≤ height k :=
    hheight.eventually (eventually_ge_atTop (2 * L / epsilon))
  filter_upwards [hKbound, hheightLarge] with k hk hlarge
  have hLle : L ≤ delta * height k := by
    dsimp [delta]
    have := mul_le_mul_of_nonneg_left hlarge hepsilon.le
    field_simp [hepsilon.ne'] at this ⊢
    linarith
  have hKexp : K ≤ Real.exp (delta * height k) := by
    calc
      K ≤ max 1 K := le_max_right 1 K
      _ = Real.exp L := (Real.exp_log hmaxPos).symm
      _ ≤ Real.exp (delta * height k) := Real.exp_le_exp.mpr hLle
  calc
    boundaryScale k ≤ K * Real.exp (delta * height k) := hk
    _ ≤ Real.exp (delta * height k) * Real.exp (delta * height k) :=
      mul_le_mul_of_nonneg_right hKexp (Real.exp_nonneg _)
    _ = Real.exp (epsilon * height k) := by
      rw [← Real.exp_add]
      congr 1
      dsimp [delta]
      ring

/-- The subexponential estimate is equivalent, under the natural positivity normalization of
the scale, to the LRW quotient tending to infinity.  This is the exact field required by the
finite-block construction package. -/
lemma height_div_log_boundaryScale_tendsto_atTop
    {height boundaryScale : ℕ → ℝ}
    (hscale : ∀ k, 1 < boundaryScale k)
    (hsubexponential : ∀ epsilon : ℝ, 0 < epsilon → ∀ᶠ k in atTop,
      boundaryScale k ≤ Real.exp (epsilon * height k)) :
    Tendsto (fun k ↦ height k / Real.log (boundaryScale k)) atTop atTop := by
  refine tendsto_atTop.2 fun b ↦ ?_
  let T : ℝ := max b 0 + 1
  let epsilon : ℝ := T⁻¹
  have hT : 0 < T := by dsimp [T]; linarith [le_max_right b 0]
  have hepsilon : 0 < epsilon := inv_pos.mpr hT
  filter_upwards [hsubexponential epsilon hepsilon] with k hk
  have hscalePos : 0 < boundaryScale k := zero_lt_one.trans (hscale k)
  have hlogPos : 0 < Real.log (boundaryScale k) := Real.log_pos (hscale k)
  have hlogLe : Real.log (boundaryScale k) ≤ epsilon * height k :=
    (Real.log_le_iff_le_exp hscalePos).2 hk
  have hTlog : T * Real.log (boundaryScale k) ≤ height k := by
    have hmul := mul_le_mul_of_nonneg_left hlogLe hT.le
    calc
      T * Real.log (boundaryScale k) ≤ T * (epsilon * height k) := hmul
      _ = height k := by
        dsimp [epsilon]
        rw [← mul_assoc, mul_inv_cancel₀ hT.ne', one_mul]
  apply (le_div_iff₀ hlogPos).2
  exact (mul_le_mul_of_nonneg_right
    (show b ≤ T by dsimp [T]; linarith [le_max_left b 0]) hlogPos.le).trans hTlog

/-- Combined sequential adapter: soft constant-times-exponential bounds at every slope produce
the precise LRW quotient limit. -/
lemma height_div_log_boundaryScale_tendsto_of_const_mul_exp
    {height boundaryScale : ℕ → ℝ}
    (hheight : Tendsto height atTop atTop)
    (hscale : ∀ k, 1 < boundaryScale k)
    (hbound : ∀ delta : ℝ, 0 < delta → ∃ K : ℝ, 0 ≤ K ∧
      ∀ᶠ k in atTop,
        boundaryScale k ≤ K * Real.exp (delta * height k)) :
    Tendsto (fun k ↦ height k / Real.log (boundaryScale k)) atTop atTop := by
  apply height_div_log_boundaryScale_tendsto_atTop hscale
  exact boundaryScale_subexponential_of_const_mul_exp hheight hbound

/-- The form produced directly by the boundary-access estimate.  A fixed additive term and the
factor `exp (-D / n)` are absorbed into a slope-dependent constant, while the arbitrary positive
divisor `n` makes the exponential slope as small as desired. -/
lemma boundaryScale_const_mul_exp_of_divisor_bounds
    {height boundaryScale : ℕ → ℝ} {B C D : ℝ}
    (hheight : Tendsto height atTop atTop) (hB : 0 ≤ B)
    (hbound : ∀ n : ℝ, 0 < n → ∀ᶠ k in atTop,
      boundaryScale k ≤ B + Real.exp ((C * height k - D) / n)) :
    ∀ delta : ℝ, 0 < delta → ∃ K : ℝ, 0 ≤ K ∧
      ∀ᶠ k in atTop,
        boundaryScale k ≤ K * Real.exp (delta * height k) := by
  intro delta hdelta
  let n : ℝ := max 1 (C / delta)
  have hn : 0 < n := lt_of_lt_of_le zero_lt_one (le_max_left 1 (C / delta))
  have hgamma : C / n ≤ delta := by
    apply (div_le_iff₀ hn).2
    have hCn : C / delta ≤ n := le_max_right 1 (C / delta)
    simpa [mul_comm] using (div_le_iff₀ hdelta).1 hCn
  let K : ℝ := B + Real.exp (-D / n)
  have hK : 0 ≤ K := add_nonneg hB (Real.exp_nonneg _)
  refine ⟨K, hK, ?_⟩
  have hheightNonneg : ∀ᶠ k in atTop, 0 ≤ height k :=
    hheight.eventually (eventually_ge_atTop 0)
  filter_upwards [hbound n hn, hheightNonneg] with k hk hkHeight
  have hexpOne : 1 ≤ Real.exp (delta * height k) :=
    Real.one_le_exp (mul_nonneg hdelta.le hkHeight)
  have hgammaHeight : (C / n) * height k ≤ delta * height k :=
    mul_le_mul_of_nonneg_right hgamma hkHeight
  have hexpSlope : Real.exp ((C / n) * height k) ≤
      Real.exp (delta * height k) := Real.exp_le_exp.mpr hgammaHeight
  have hfirst : B ≤ B * Real.exp (delta * height k) := by
    nlinarith [mul_le_mul_of_nonneg_left hexpOne hB]
  have hsecond : Real.exp ((C * height k - D) / n) ≤
      Real.exp (-D / n) * Real.exp (delta * height k) := by
    calc
      Real.exp ((C * height k - D) / n) =
          Real.exp (-D / n) * Real.exp ((C / n) * height k) := by
        rw [← Real.exp_add]
        congr 1
        field_simp [hn.ne']
        ring
      _ ≤ Real.exp (-D / n) * Real.exp (delta * height k) :=
        mul_le_mul_of_nonneg_left hexpSlope (Real.exp_nonneg _)
  calc
    boundaryScale k ≤ B + Real.exp ((C * height k - D) / n) := hk
    _ ≤ B * Real.exp (delta * height k) +
        Real.exp (-D / n) * Real.exp (delta * height k) := add_le_add hfirst hsecond
    _ = K * Real.exp (delta * height k) := by
      dsimp [K]
      ring

/-- Turn the explicit family of LRW frontier bounds directly into the quotient limit required
by `LRWLogPosBlockConstruction`. -/
lemma height_div_log_boundaryScale_tendsto_of_divisor_bounds
    {height boundaryScale : ℕ → ℝ} {B C D : ℝ}
    (hheight : Tendsto height atTop atTop)
    (hscale : ∀ k, 1 < boundaryScale k) (hB : 0 ≤ B)
    (hbound : ∀ n : ℝ, 0 < n → ∀ᶠ k in atTop,
      boundaryScale k ≤ B + Real.exp ((C * height k - D) / n)) :
    Tendsto (fun k ↦ height k / Real.log (boundaryScale k)) atTop atTop := by
  apply height_div_log_boundaryScale_tendsto_of_const_mul_exp hheight hscale
  exact boundaryScale_const_mul_exp_of_divisor_bounds hheight hB hbound

end Erdos515
