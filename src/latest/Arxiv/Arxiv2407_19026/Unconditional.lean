import Arxiv.Arxiv2407_19026.NumericalProfiles

/-!
# Unconditional optimization rounds

This file packages the certified numerical profiles as inputs to the
pointwise-to-uniform optimization theorem.
-/

noncomputable section

namespace Arxiv2407_19026

lemma optimizedRamseyExponent_nonneg_of_nonneg
    {β z : ℝ} (hβ : 0 ≤ β) (hz : z ∈ Set.Icc (0 : ℝ) 1) :
    0 ≤ optimizedRamseyExponent β z := by
  have hzp : 0 < 1 + z := by linarith [hz.1]
  have hlogOne :
      z ≤ (1 + z) * Real.log (1 + z) := by
    have h :=
      Real.one_sub_inv_le_log_of_pos hzp
    have heq : 1 - (1 + z)⁻¹ = z / (1 + z) := by
      field_simp [hzp.ne']
      ring
    rw [heq] at h
    have := mul_le_mul_of_nonneg_left h hzp.le
    field_simp [hzp.ne'] at this
    linarith
  have hlogz : Real.log z ≤ 0 :=
    Real.log_nonpos hz.1 hz.2
  have hentropy : z ≤ ramseyEntropy z := by
    unfold ramseyEntropy
    rw [add_comm z 1]
    linarith [mul_nonpos_of_nonneg_of_nonpos hz.1 hlogz]
  have hcorrection :
      -(1 / 4 : ℝ) * z ≤ ramseyCorrection β z :=
    neg_quarter_mul_le_ramseyCorrection hβ hz.1
  unfold optimizedRamseyExponent
  norm_num at hcorrection ⊢
  linarith [hz.1]

/-- Perturb a boundary point of the Ramsey region and the limiting red
density simultaneously.  This is the general-region analogue of
`exists_elementary_admissibleBookCellData`. -/
lemma exists_admissibleBookCellData_of_region
    {F S z μ p₀ X Y : ℝ}
    (hμ : 0 < μ) (hμ1 : μ < 1)
    (hp₀ : 0 < p₀) (hp₀1 : p₀ < 1)
    (hX :
      X = p₀ ^ ((1 : ℝ) / (1 - μ)) * (1 - μ))
    (hX0 : 0 < X) (hX1 : X < 1)
    (hY0 : 0 < Y) (hY1 : Y < 1)
    (hregion : (X, Y) ∈ ramseyRegion)
    (hbook :
      -(Real.log X + z * Real.log μ +
          z * Real.log Y) / 2 < F)
    (hblue : Real.exp (-S) = 1 - p₀) :
    ∃ (D : AdmissibleBookCellData) (q : ℝ),
      0 ≤ q ∧ q < 1 ∧
      bookCellLogCost D z < F ∧
      Real.exp (-S) < q * (1 - D.p) := by
  let r : ℝ := 1 / (1 - μ)
  let pp : ℝ → ℝ := fun η ↦ p₀ - η
  let lim : ℝ → ℝ := fun η ↦ pp η ^ r * (1 - μ)
  let xx : ℝ → ℝ := fun η ↦ min (lim η) X - η
  let yy : ℝ → ℝ := fun η ↦ Y - η
  have hppCont : ContinuousAt pp 0 := by
    dsimp [pp]
    fun_prop
  have hlimCont : ContinuousAt lim 0 := by
    have hrpow :
        ContinuousAt (fun η : ℝ ↦ pp η ^ r) 0 := by
      have houter :=
        Real.continuousAt_rpow_const p₀ r (Or.inl hp₀.ne')
      have hcomp := houter.comp_of_eq hppCont (by simp [pp])
      change ContinuousAt ((fun x : ℝ ↦ x ^ r) ∘ pp) 0
      exact hcomp
    exact hrpow.mul continuousAt_const
  have hxxCont : ContinuousAt xx 0 := by
    dsimp [xx]
    fun_prop
  have hyyCont : ContinuousAt yy 0 := by
    dsimp [yy]
    fun_prop
  have hpp0 : pp 0 = p₀ := by simp [pp]
  have hlim0 : lim 0 = X := by
    simp [lim, pp, r, hX]
  have hxx0 : xx 0 = X := by simp [xx, hlim0]
  have hyy0 : yy 0 = Y := by simp [yy]
  have hcostCont :
      ContinuousAt
        (fun η : ℝ ↦
          -(Real.log (xx η) + z * Real.log μ +
            z * Real.log (yy η)) / 2) 0 := by
    have hxlog := hxxCont.log (by simpa [hxx0] using hX0.ne')
    have hylog := hyyCont.log (by simpa [hyy0] using hY0.ne')
    fun_prop
  have hppPos :
      ∀ᶠ η : ℝ in nhds 0, 0 < pp η :=
    continuousAt_const.eventually_lt hppCont (by simpa [hpp0] using hp₀)
  have hppOne :
      ∀ᶠ η : ℝ in nhds 0, pp η < 1 :=
    hppCont.eventually_lt continuousAt_const (by simpa [hpp0] using hp₀1)
  have hxxPos :
      ∀ᶠ η : ℝ in nhds 0, 0 < xx η :=
    continuousAt_const.eventually_lt hxxCont (by simpa [hxx0] using hX0)
  have hyyPos :
      ∀ᶠ η : ℝ in nhds 0, 0 < yy η :=
    continuousAt_const.eventually_lt hyyCont (by simpa [hyy0] using hY0)
  have hcost :
      ∀ᶠ η : ℝ in nhds 0,
        -(Real.log (xx η) + z * Real.log μ +
            z * Real.log (yy η)) / 2 < F :=
    hcostCont.eventually_lt continuousAt_const (by
      simpa [hxx0, hyy0] using hbook)
  have hall :
      {η : ℝ |
        0 < pp η ∧ pp η < 1 ∧
        0 < xx η ∧ 0 < yy η ∧
        -(Real.log (xx η) + z * Real.log μ +
            z * Real.log (yy η)) / 2 < F} ∈ nhds 0 := by
    filter_upwards [hppPos, hppOne, hxxPos, hyyPos, hcost] with
      η hp hp1 hx hy hc
    exact ⟨hp, hp1, hx, hy, hc⟩
  obtain ⟨d, hd, hball⟩ := Metric.mem_nhds_iff.1 hall
  let η : ℝ := d / 2
  have hη : 0 < η := half_pos hd
  have hηd : η < d := by dsimp [η]; linarith
  have hηball : η ∈ Metric.ball (0 : ℝ) d := by
    rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_pos hη]
    exact hηd
  have hgood := hball hηball
  rcases hgood with
    ⟨hppη, hppη1, hxxη, hyyη, hcostη⟩
  have hlimit : xx η < lim η := by
    dsimp [xx]
    have := min_le_left (lim η) X
    linarith
  have hxxX : xx η < X := by
    dsimp [xx]
    have := min_le_right (lim η) X
    linarith
  have hyyY : yy η < Y := by
    dsimp [yy]
    linarith
  have hxx1 : xx η < 1 := hxxX.trans hX1
  have hyy1 : yy η < 1 := hyyY.trans hY1
  have hregion' :
      (xx η, yy η) ∈ ramseyRegionInterior :=
    strict_mono_mem_ramseyRegionInterior
      hregion hxxη hxxX hyyη hyyY
  let D : AdmissibleBookCellData :=
    { x := xx η
      y := yy η
      μ := μ
      p := pp η
      x_pos := hxxη
      x_lt_one := hxx1
      y_pos := hyyη
      y_lt_one := hyy1
      μ_pos := hμ
      μ_lt_one := hμ1
      p_pos := hppη
      p_lt_one := hppη1
      limit := by simpa [lim, r] using hlimit
      region := hregion' }
  have hpLt : pp η < p₀ := by
    dsimp [pp]
    linarith
  have hblueGap : Real.exp (-S) < 1 - pp η := by
    rw [hblue]
    linarith
  let q : ℝ :=
    (Real.exp (-S) / (1 - pp η) + 1) / 2
  have hden : 0 < 1 - pp η := sub_pos.mpr hppη1
  have hratio0 : 0 < Real.exp (-S) / (1 - pp η) :=
    div_pos (Real.exp_pos _) hden
  have hratio1 : Real.exp (-S) / (1 - pp η) < 1 :=
    (div_lt_one hden).2 hblueGap
  have hq0 : 0 ≤ q := by
    dsimp [q]
    linarith
  have hq1 : q < 1 := by
    dsimp [q]
    linarith
  have hqblue : Real.exp (-S) < q * (1 - pp η) := by
    dsimp [q]
    field_simp [hden.ne']
    nlinarith [hblueGap]
  refine ⟨D, q, hq0, hq1, ?_, ?_⟩
  · simpa [D, bookCellLogCost] using hcostη
  · simpa [D] using hqblue

/-- A two-sided logarithmic certificate for a point of the Ramsey region,
using an arbitrary already-proved exponent profile. -/
structure ExponentRegionCertificate
    (F : ℝ → ℝ) (x y : ℝ) : Prop where
  forward :
    ∀ r ∈ Set.Ioc (0 : ℝ) 1,
      F r ≤ -Real.log x - r * Real.log y
  backward :
    ∀ r ∈ Set.Ioc (0 : ℝ) 1,
      F r ≤ -r * Real.log x - Real.log y

lemma ExponentRegionCertificate.swap
    {F : ℝ → ℝ} {x y : ℝ}
    (C : ExponentRegionCertificate F x y) :
    ExponentRegionCertificate F y x := by
  constructor
  · intro r hr
    have h := C.backward r hr
    linarith
  · intro r hr
    have h := C.forward r hr
    linarith

lemma eventuallyRamseyBound_of_exponentRegionCertificate
    {F : ℝ → ℝ} {x y : ℝ}
    (hx : 0 < x) (hy : 0 < y)
    (C : ExponentRegionCertificate F x y)
    (hExp : HasRamseyExponent F) :
    ∀ x₀ y₀ : ℝ, 0 < x₀ → x₀ < x → 0 < y₀ → y₀ < y →
      EventuallyRamseyBound x₀ y₀ := by
  intro x₀ y₀ hx₀ hxx hy₀ hyy
  have hlogx : Real.log x₀ < Real.log x :=
    Real.strictMonoOn_log (Set.mem_Ioi.mpr hx₀)
      (Set.mem_Ioi.mpr hx) hxx
  have hlogy : Real.log y₀ < Real.log y :=
    Real.strictMonoOn_log (Set.mem_Ioi.mpr hy₀)
      (Set.mem_Ioi.mpr hy) hyy
  let ε : ℝ :=
    min (Real.log x - Real.log x₀)
      (Real.log y - Real.log y₀) / 2
  have hε : 0 < ε := by
    dsimp [ε]
    positivity
  obtain ⟨K, hK⟩ := hExp ε hε
  refine ⟨2 * K, ?_⟩
  intro k l hk hl hsum
  have hkR : (0 : ℝ) < k := by
    exact_mod_cast (show 0 < k by omega)
  have hlR : (0 : ℝ) < l := by
    exact_mod_cast (show 0 < l by omega)
  have hεx : ε ≤ Real.log x - Real.log x₀ := by
    dsimp [ε]
    exact (div_le_self
      (le_min (sub_nonneg.mpr hlogx.le)
        (sub_nonneg.mpr hlogy.le)) (by norm_num)).trans
      (min_le_left _ _)
  have hεy : ε ≤ Real.log y - Real.log y₀ := by
    dsimp [ε]
    exact (div_le_self
      (le_min (sub_nonneg.mpr hlogx.le)
        (sub_nonneg.mpr hlogy.le)) (by norm_num)).trans
      (min_le_right _ _)
  have finish
      (hbound : (ramseyNumber k l : ℝ) ≤
        Real.exp (-(k : ℝ) * Real.log x₀ -
          (l : ℝ) * Real.log y₀)) :
      (ramseyNumber k l : ℝ) * x₀ ^ k * y₀ ^ l ≤ 1 := by
    calc
      (ramseyNumber k l : ℝ) * x₀ ^ k * y₀ ^ l ≤
          Real.exp (-(k : ℝ) * Real.log x₀ -
            (l : ℝ) * Real.log y₀) * x₀ ^ k * y₀ ^ l := by
        gcongr
      _ = 1 := by
        rw [show -(k : ℝ) * Real.log x₀ -
              (l : ℝ) * Real.log y₀ =
            (-(k : ℝ) * Real.log x₀) +
              (-(l : ℝ) * Real.log y₀) by ring,
          Real.exp_add, exp_neg_nat_mul_log hx₀,
          exp_neg_nat_mul_log hy₀]
        calc
          x₀⁻¹ ^ k * y₀⁻¹ ^ l * x₀ ^ k * y₀ ^ l =
              (x₀⁻¹ * x₀) ^ k * (y₀⁻¹ * y₀) ^ l := by
            rw [mul_pow, mul_pow]
            ring
          _ = 1 := by simp [hx₀.ne', hy₀.ne']
  by_cases hlk : l ≤ k
  · have hkK : K ≤ k := by omega
    have hraw := hK k l hkK hl hlk
    apply finish
    refine hraw.trans (Real.exp_le_exp_of_le ?_)
    have hratio :
        (l : ℝ) / k ∈ Set.Ioc (0 : ℝ) 1 := by
      exact ⟨div_pos hlR hkR, (div_le_one hkR).2 (by exact_mod_cast hlk)⟩
    have hcross := C.forward ((l : ℝ) / k) hratio
    have hxmul := mul_le_mul_of_nonneg_left hεx hkR.le
    have hexpand :
        (F ((l : ℝ) / k) + ε) * k =
          F ((l : ℝ) / k) * k + ε * k := by ring
    rw [hexpand]
    have hcross' :
        F ((l : ℝ) / k) * k ≤
          -(k : ℝ) * Real.log x - (l : ℝ) * Real.log y := by
      have := mul_le_mul_of_nonneg_right hcross hkR.le
      field_simp [hkR.ne'] at this
      nlinarith
    nlinarith
  · have hkl : k ≤ l := by omega
    have hlK : K ≤ l := by omega
    have hraw := hK l k hlK hk hkl
    rw [← ramseyNumber_swap] at hraw
    apply finish
    refine hraw.trans (Real.exp_le_exp_of_le ?_)
    have hratio :
        (k : ℝ) / l ∈ Set.Ioc (0 : ℝ) 1 := by
      exact ⟨div_pos hkR hlR, (div_le_one hlR).2 (by exact_mod_cast hkl)⟩
    have hcross := C.backward ((k : ℝ) / l) hratio
    have hymul := mul_le_mul_of_nonneg_left hεy hlR.le
    have hexpand :
        (F ((k : ℝ) / l) + ε) * l =
          F ((k : ℝ) / l) * l + ε * l := by ring
    rw [hexpand]
    have hcross' :
        F ((k : ℝ) / l) * l ≤
          -(k : ℝ) * Real.log x - (l : ℝ) * Real.log y := by
      have := mul_le_mul_of_nonneg_right hcross hlR.le
      field_simp [hlR.ne'] at this
      nlinarith
    nlinarith

theorem exponentRegionCertificate_mem_ramseyRegion
    {F : ℝ → ℝ} {x y : ℝ}
    (hx : 0 < x) (hx1 : x < 1)
    (hy : 0 < y) (hy1 : y < 1)
    (C : ExponentRegionCertificate F x y)
    (hExp : HasRamseyExponent F) :
    (x, y) ∈ ramseyRegion := by
  apply mem_ramseyRegion_of_strict_eventuallyRamseyBound
    hx hx1 hy hy1
  exact eventuallyRamseyBound_of_exponentRegionCertificate
    hx hy C hExp

/-- The exponential coordinates of a supporting tangent to an exponent
profile. -/
def tangentRegionX (F S : ℝ → ℝ) (t : ℝ) : ℝ :=
  Real.exp (t * S t - F t)

def tangentRegionY (S : ℝ → ℝ) (t : ℝ) : ℝ :=
  Real.exp (-S t)

lemma tangent_exponentRegionCertificate
    {F S : ℝ → ℝ} {t : ℝ}
    (htangent :
      ∀ r ∈ Set.Ioc (0 : ℝ) 1,
        F r ≤ F t + S t * (r - t))
    (horder : tangentRegionY S t ≤ tangentRegionX F S t) :
    ExponentRegionCertificate F
      (tangentRegionX F S t) (tangentRegionY S t) := by
  have hlogX :
      Real.log (tangentRegionX F S t) = t * S t - F t := by
    exact Real.log_exp _
  have hlogY :
      Real.log (tangentRegionY S t) = -S t := by
    exact Real.log_exp _
  constructor
  · intro r hr
    rw [hlogX, hlogY]
    have h := htangent r hr
    linarith
  · intro r hr
    have hr1 : 0 ≤ 1 - r := by linarith [hr.2]
    have hlogs :
        Real.log (tangentRegionY S t) ≤
          Real.log (tangentRegionX F S t) :=
      Real.log_le_log (Real.exp_pos _) horder
    rw [hlogX, hlogY] at hlogs ⊢
    have h := htangent r hr
    nlinarith

/-- The derivative of `optimizedRamseySlope`. -/
def optimizedRamseyCurvature (β z : ℝ) : ℝ :=
  1 / (z + 1) - 1 / z +
    (1 / 2 + 2 * β + (23 / 100 - 4 * β) * z +
      (β - 12 / 25) * z ^ 2 + (2 / 25) * z ^ 3) *
      Real.exp (-z)

lemma hasDerivAt_optimizedRamseySlope
    (β : ℝ) {z : ℝ} (hz : 0 < z) :
    HasDerivAt (optimizedRamseySlope β)
      (optimizedRamseyCurvature β z) z := by
  unfold optimizedRamseySlope optimizedRamseyCurvature
  convert
    ((((hasDerivAt_id z).add_const 1).log
      (by simpa [Function.id_def] using
        (show z + 1 ≠ 0 by linarith))).sub
      ((hasDerivAt_id z).log hz.ne')).add
      (((((hasDerivAt_const z (-(1 / 4 : ℝ))).add
        ((hasDerivAt_const z (2 * β)).mul
          (hasDerivAt_id z))).add
        ((hasDerivAt_const z (6 / 25 : ℝ)).mul
          ((hasDerivAt_id z).pow 2))).sub
        ((((hasDerivAt_const z (-(1 / 4 : ℝ))).mul
          (hasDerivAt_id z)).add
          ((hasDerivAt_const z β).mul
            ((hasDerivAt_id z).pow 2))).add
          ((hasDerivAt_const z (2 / 25 : ℝ)).mul
            ((hasDerivAt_id z).pow 3)))).mul
        (hasDerivAt_id z).neg.exp) using 1
  all_goals try rfl
  all_goals simp only [Function.id_def, Pi.add_apply, Pi.sub_apply,
    Pi.mul_apply, Pi.pow_apply, Pi.neg_apply, mul_one, zero_add]
  all_goals field_simp [hz.ne', (by linarith : z + 1 ≠ 0)]
  all_goals ring

lemma optimizedRamseyCurvature_neg
    {β z : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β ≤ 2 / 25)
    (hz0 : 0 < z) (hz1 : z ≤ 1) :
    optimizedRamseyCurvature β z < 0 := by
  let Q : ℝ :=
    1 / 2 + 2 * β + (23 / 100 - 4 * β) * z +
      (β - 12 / 25) * z ^ 2 + (2 / 25) * z ^ 3
  have hzsq0 : 0 ≤ z ^ 2 := sq_nonneg z
  have hzcube0 : 0 ≤ z ^ 3 := by positivity
  have hzsq1 : z ^ 2 ≤ 1 := by nlinarith
  have hzcube1 : z ^ 3 ≤ 1 := by
    nlinarith [mul_le_mul_of_nonneg_left hzsq1 hz0.le]
  have hcoef : 2 - 4 * z + z ^ 2 ≤ 2 := by
    nlinarith [mul_nonpos_of_nonneg_of_nonpos hz0.le (by linarith : z - 4 ≤ 0)]
  have hβcoef :
      β * (2 - 4 * z + z ^ 2) ≤ (4 / 25 : ℝ) := by
    calc
      β * (2 - 4 * z + z ^ 2) ≤ β * 2 :=
        mul_le_mul_of_nonneg_left hcoef hβ0
      _ ≤ (2 / 25 : ℝ) * 2 :=
        mul_le_mul_of_nonneg_right hβ1 (by norm_num)
      _ = 4 / 25 := by ring
  have hQ : Q ≤ (97 / 100 : ℝ) := by
    dsimp [Q]
    have hzlin : (23 / 100 : ℝ) * z ≤ 23 / 100 := by
      nlinarith
    have hzcube :
        (2 / 25 : ℝ) * z ^ 3 ≤ 2 / 25 := by
      nlinarith
    nlinarith
  have honeExp :
      (1 + z) * Real.exp (-z) ≤ 1 := by
    have h := Real.add_one_le_exp z
    have he := mul_le_mul_of_nonneg_right h (Real.exp_nonneg (-z))
    rw [← Real.exp_add] at he
    norm_num at he
    simpa [add_comm] using he
  have hQprod :
      Q * z * (1 + z) * Real.exp (-z) < 1 := by
    by_cases hQ0 : 0 ≤ Q
    · calc
        Q * z * (1 + z) * Real.exp (-z) =
            (Q * z) * ((1 + z) * Real.exp (-z)) := by ring
        _ ≤ ((97 / 100 : ℝ) * 1) * 1 := by
          gcongr
        _ < 1 := by norm_num
    · have hneg :
          Q * z * (1 + z) * Real.exp (-z) < 0 := by
        have : Q < 0 := lt_of_not_ge hQ0
        rw [show
          Q * z * (1 + z) * Real.exp (-z) =
            Q * (z * (1 + z) * Real.exp (-z)) by ring]
        exact mul_neg_of_neg_of_pos this (by positivity)
      linarith
  have hden : 0 < z * (z + 1) := mul_pos hz0 (by linarith)
  have hcorr :
      Q * Real.exp (-z) < 1 / (z * (z + 1)) := by
    rw [lt_div_iff₀ hden]
    nlinarith [hQprod]
  have hfrac :
      1 / (z + 1) - 1 / z = -1 / (z * (z + 1)) := by
    field_simp [hz0.ne', (by linarith : z + 1 ≠ 0)]
    ring
  unfold optimizedRamseyCurvature
  change
    1 / (z + 1) - 1 / z + Q * Real.exp (-z) < 0
  rw [hfrac]
  rw [show -1 / (z * (z + 1)) =
    -(1 / (z * (z + 1))) by ring]
  linarith

lemma optimizedRamseySlope_strictAntiOn
    {β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β ≤ 2 / 25) :
    StrictAntiOn (optimizedRamseySlope β) (Set.Ioc (0 : ℝ) 1) := by
  apply strictAntiOn_of_deriv_neg
    (convex_Ioc (0 : ℝ) 1)
  · intro z hz
    exact (hasDerivAt_optimizedRamseySlope β hz.1).continuousAt.continuousWithinAt
  · intro z hz
    have hz' : z ∈ Set.Ioo (0 : ℝ) 1 := by
      simpa only [interior_Ioc] using hz
    rw [(hasDerivAt_optimizedRamseySlope β hz'.1).deriv]
    exact optimizedRamseyCurvature_neg hβ0 hβ1 hz'.1 hz'.2.le

lemma optimizedRamseyExponent_tangent_upper
    {β t r : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β ≤ 2 / 25)
    (ht : t ∈ Set.Ioc (0 : ℝ) 1)
    (hr : r ∈ Set.Ioc (0 : ℝ) 1) :
    optimizedRamseyExponent β r ≤
      optimizedRamseyExponent β t +
        optimizedRamseySlope β t * (r - t) := by
  by_cases hrt : r = t
  · subst r
    simp
  have hanti :=
    (optimizedRamseySlope_strictAntiOn hβ0 hβ1).antitoneOn
  rcases lt_or_gt_of_ne hrt with hrt | htr
  · have hcont :
        ContinuousOn (optimizedRamseyExponent β) (Set.Icc r t) := by
      intro w hw
      exact (hasDerivAt_optimizedRamseyExponent β
        (hr.1.trans_le hw.1)).continuousAt.continuousWithinAt
    have hderiv :
        ∀ w ∈ Set.Ioo r t,
          HasDerivAt (optimizedRamseyExponent β)
            (optimizedRamseySlope β w) w := by
      intro w hw
      exact hasDerivAt_optimizedRamseyExponent β
        (hr.1.trans hw.1)
    obtain ⟨c, hc, hmean⟩ :=
      exists_hasDerivAt_eq_slope
        (optimizedRamseyExponent β) (optimizedRamseySlope β)
        hrt hcont hderiv
    have hcI : c ∈ Set.Ioc (0 : ℝ) 1 :=
      ⟨hr.1.trans hc.1, (hc.2.trans_le ht.2).le⟩
    have hSc : optimizedRamseySlope β t ≤ optimizedRamseySlope β c :=
      hanti hcI ht hc.2.le
    have hdiff :
        optimizedRamseyExponent β t -
            optimizedRamseyExponent β r =
          optimizedRamseySlope β c * (t - r) :=
      ((eq_div_iff (sub_ne_zero.mpr hrt.ne')).mp hmean).symm
    have hmul :=
      mul_le_mul_of_nonneg_right hSc (sub_nonneg.mpr hrt.le)
    nlinarith
  · have hcont :
        ContinuousOn (optimizedRamseyExponent β) (Set.Icc t r) := by
      intro w hw
      exact (hasDerivAt_optimizedRamseyExponent β
        (ht.1.trans_le hw.1)).continuousAt.continuousWithinAt
    have hderiv :
        ∀ w ∈ Set.Ioo t r,
          HasDerivAt (optimizedRamseyExponent β)
            (optimizedRamseySlope β w) w := by
      intro w hw
      exact hasDerivAt_optimizedRamseyExponent β
        (ht.1.trans hw.1)
    obtain ⟨c, hc, hmean⟩ :=
      exists_hasDerivAt_eq_slope
        (optimizedRamseyExponent β) (optimizedRamseySlope β)
        htr hcont hderiv
    have hcI : c ∈ Set.Ioc (0 : ℝ) 1 :=
      ⟨ht.1.trans hc.1, (hc.2.trans_le hr.2).le⟩
    have hSc : optimizedRamseySlope β c ≤ optimizedRamseySlope β t :=
      hanti ht hcI hc.1.le
    have hdiff :
        optimizedRamseyExponent β r -
            optimizedRamseyExponent β t =
          optimizedRamseySlope β c * (r - t) :=
      ((eq_div_iff (sub_ne_zero.mpr htr.ne')).mp hmean).symm
    have hmul :=
      mul_le_mul_of_nonneg_right hSc (sub_nonneg.mpr htr.le)
    nlinarith

/-- Cancellation-free form of the logarithmic separation between the two
tangent-region coordinates. -/
def tangentOrderAlgebraic (β t : ℝ) : ℝ :=
  -Real.log t +
    (-(1 / 4 : ℝ) + (1 / 4 : ℝ) * t +
      (49 / 100 : ℝ) * t ^ 2 + (2 / 25 : ℝ) * t ^ 3 -
      (2 / 25 : ℝ) * t ^ 4 +
      β * (2 * t - t ^ 3)) * Real.exp (-t)

lemma tangentOrderAlgebraic_eq
    {β t : ℝ} :
    tangentOrderAlgebraic β t =
      (t + 1) * optimizedRamseySlope β t -
        optimizedRamseyExponent β t := by
  unfold tangentOrderAlgebraic optimizedRamseySlope
    optimizedRamseyExponent ramseyEntropy ramseyCorrection
  ring

lemma tangentOrderCorrectionCoeff_nonneg_large :
    ∀ t ∈ Set.Icc (1 / 2 : ℝ) 1,
      0 ≤
        -(1 / 4 : ℝ) + (1 / 4 : ℝ) * t +
          (49 / 100 : ℝ) * t ^ 2 + (2 / 25 : ℝ) * t ^ 3 -
          (2 / 25 : ℝ) * t ^ 4 := by
  rintro t ⟨ht0, ht1⟩
  have ht3 : t ^ 3 ≤ t := by
    have ht_sq : t ^ 2 ≤ 1 :=
      by simpa [pow_two] using
        (mul_self_le_mul_self (by linarith : 0 ≤ t) ht1)
    nlinarith [mul_le_mul_of_nonneg_left ht_sq (by linarith : 0 ≤ t)]
  have hneg :=
    mul_le_mul_of_nonpos_left ht3
      (by norm_num : (-(2 / 25 : ℝ)) ≤ 0)
  have hQ :
      0 ≤
        -(2 / 25 : ℝ) * t ^ 3 + (1 / 25 : ℝ) * t ^ 2 +
          (51 / 100 : ℝ) * t + 101 / 200 := by
    nlinarith [sq_nonneg t]
  have hfactor :
      -(1 / 4 : ℝ) + (1 / 4 : ℝ) * t +
          (49 / 100 : ℝ) * t ^ 2 + (2 / 25 : ℝ) * t ^ 3 -
          (2 / 25 : ℝ) * t ^ 4 =
        1 / 400 +
          (t - 1 / 2) *
            (-(2 / 25 : ℝ) * t ^ 3 + (1 / 25 : ℝ) * t ^ 2 +
              (51 / 100 : ℝ) * t + 101 / 200) := by
    ring
  rw [hfactor]
  exact add_nonneg (by norm_num)
    (mul_nonneg (sub_nonneg.mpr ht0) hQ)

lemma tangentOrderAlgebraic_nonneg
    {β t : ℝ} (hβ : 0 ≤ β) (ht0 : 0 < t) (ht1 : t ≤ 1) :
    0 ≤ tangentOrderAlgebraic β t := by
  have hβterm :
      0 ≤ β * (2 * t - t ^ 3) * Real.exp (-t) := by
    have : 0 ≤ 2 * t - t ^ 3 := by
      nlinarith [mul_le_mul_of_nonneg_left
        (mul_self_le_mul_self (by linarith) ht1) ht0.le]
    positivity
  let R : ℝ :=
    -(1 / 4 : ℝ) + (1 / 4 : ℝ) * t +
      (49 / 100 : ℝ) * t ^ 2 + (2 / 25 : ℝ) * t ^ 3 -
      (2 / 25 : ℝ) * t ^ 4
  have ht4 : t ^ 4 ≤ 1 := by
    nlinarith [sq_nonneg (t ^ 2 - 1),
      mul_self_le_mul_self ht0.le ht1]
  have hRlower : (-33 / 100 : ℝ) ≤ R := by
    dsimp [R]
    nlinarith [sq_nonneg t, show 0 ≤ t ^ 3 by positivity]
  have hRprod : (-33 / 100 : ℝ) ≤ R * Real.exp (-t) := by
    have he0 : 0 < Real.exp (-t) := Real.exp_pos _
    have he1 : Real.exp (-t) ≤ 1 :=
      Real.exp_le_one_iff.mpr (by linarith)
    by_cases hR0 : 0 ≤ R
    · exact (by norm_num : (-33 / 100 : ℝ) ≤ 0).trans
        (mul_nonneg hR0 (Real.exp_nonneg _))
    · have hmul :=
        mul_le_mul_of_nonpos_left he1 (le_of_not_ge hR0)
      nlinarith
  by_cases ht : t ≤ 1 / 2
  · have hlog := Real.log_le_sub_one_of_pos ht0
    unfold tangentOrderAlgebraic
    dsimp [R] at hRprod
    nlinarith
  · have hR0 :=
      tangentOrderCorrectionCoeff_nonneg_large t
        ⟨by linarith, ht1⟩
    have hlog : Real.log t ≤ 0 :=
      Real.log_nonpos ht0.le ht1
    unfold tangentOrderAlgebraic
    have hRexp :=
      mul_nonneg hR0 (Real.exp_nonneg (-t))
    nlinarith

lemma tangentRegionY_le_tangentRegionX
    {β t : ℝ} (hβ : 0 ≤ β) (ht : t ∈ Set.Ioc (0 : ℝ) 1) :
    tangentRegionY (optimizedRamseySlope β) t ≤
      tangentRegionX (optimizedRamseyExponent β)
        (optimizedRamseySlope β) t := by
  apply Real.exp_le_exp_of_le
  have horder := tangentOrderAlgebraic_nonneg
    hβ ht.1 ht.2
  rw [tangentOrderAlgebraic_eq] at horder
  linarith

lemma optimizedRamseySlope_pos
    {β t : ℝ} (hβ : 0 ≤ β) (ht0 : 0 < t) (ht1 : t ≤ 1) :
    0 < optimizedRamseySlope β t := by
  let A : ℝ :=
    -(1 / 4 : ℝ) + 2 * β * t + (6 / 25 : ℝ) * t ^ 2 -
      (-(1 / 4 : ℝ) * t + β * t ^ 2 + (2 / 25 : ℝ) * t ^ 3)
  have hA : -(1 / 4 : ℝ) ≤ A := by
    have hβterm : 0 ≤ β * (2 * t - t ^ 2) := by
      have : 0 ≤ 2 * t - t ^ 2 := by nlinarith
      positivity
    have hcubic :
        0 ≤ (6 / 25 : ℝ) * t ^ 2 - (2 / 25 : ℝ) * t ^ 3 := by
      have : 0 ≤ t ^ 2 * (3 - t) :=
        mul_nonneg (sq_nonneg t) (by linarith)
      nlinarith
    dsimp [A]
    nlinarith
  have hAexp : -(1 / 4 : ℝ) ≤ A * Real.exp (-t) := by
    have he0 : 0 < Real.exp (-t) := Real.exp_pos _
    have he1 : Real.exp (-t) ≤ 1 :=
      Real.exp_le_one_iff.mpr (by linarith)
    by_cases hA0 : 0 ≤ A
    · exact (by norm_num : -(1 / 4 : ℝ) ≤ 0).trans
        (mul_nonneg hA0 (Real.exp_nonneg _))
    · have hmul :=
        mul_le_mul_of_nonpos_left he1 (le_of_not_ge hA0)
      nlinarith
  have hratio : (2 : ℝ) ≤ (t + 1) / t := by
    rw [le_div_iff₀ ht0]
    linarith
  have hlogRatio :
      Real.log 2 ≤ Real.log ((t + 1) / t) :=
    Real.log_le_log (by norm_num) hratio
  have hlog :
      Real.log (t + 1) - Real.log t =
        Real.log ((t + 1) / t) := by
    rw [Real.log_div (by linarith : t + 1 ≠ 0) ht0.ne']
  unfold optimizedRamseySlope
  change
    Real.log (t + 1) - Real.log t + A * Real.exp (-t) > 0
  rw [hlog]
  nlinarith [Real.log_two_gt_d9]

lemma tangentRegionX_lt_one
    {β t : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β ≤ 2 / 25)
    (ht0 : 0 < t) (ht1 : t ≤ 1) :
    tangentRegionX (optimizedRamseyExponent β)
        (optimizedRamseySlope β) t < 1 := by
  rw [tangentRegionX, Real.exp_lt_one_iff]
  let B : ℝ :=
    1 / 4 + β + (4 / 25 - β) * t - (2 / 25 : ℝ) * t ^ 2
  have hB : B ≤ (49 / 100 : ℝ) := by
    have hβterm : β * (1 - t) ≤ 2 / 25 := by
      have h1t : 0 ≤ 1 - t := by linarith
      calc
        β * (1 - t) ≤ β * 1 :=
          mul_le_mul_of_nonneg_left (by linarith) hβ0
        _ ≤ 2 / 25 := by simpa using hβ1
    dsimp [B]
    nlinarith [sq_nonneg t]
  have ht2 : t ^ 2 ≤ t := by nlinarith [sq_nonneg t]
  have he0 : 0 < Real.exp (-t) := Real.exp_pos _
  have he1 : Real.exp (-t) ≤ 1 :=
    Real.exp_le_one_iff.mpr (by linarith)
  have hcorr :
      t ^ 2 * B * Real.exp (-t) ≤ (49 / 100 : ℝ) * t := by
    by_cases hB0 : 0 ≤ B
    · calc
        t ^ 2 * B * Real.exp (-t) ≤
            t ^ 2 * (49 / 100 : ℝ) * 1 := by
          gcongr
        _ ≤ (49 / 100 : ℝ) * t := by nlinarith
    · have hneg : t ^ 2 * B * Real.exp (-t) < 0 := by
        have : B < 0 := lt_of_not_ge hB0
        rw [show t ^ 2 * B * Real.exp (-t) =
          B * (t ^ 2 * Real.exp (-t)) by ring]
        exact mul_neg_of_neg_of_pos this
          (mul_pos (sq_pos_of_pos ht0) (Real.exp_pos _))
      nlinarith
  have hlogRaw :=
    Real.one_sub_inv_le_log_of_pos (by linarith : 0 < 1 + t)
  have hfrac :
      1 - (1 + t)⁻¹ = t / (1 + t) := by
    field_simp [(by linarith : 1 + t ≠ 0)]
    ring
  rw [hfrac] at hlogRaw
  have hhalf : t / 2 ≤ t / (1 + t) := by
    rw [div_le_div_iff₀ (by norm_num : (0 : ℝ) < 2)
      (by linarith : 0 < 1 + t)]
    nlinarith
  have hlog : t / 2 ≤ Real.log (1 + t) :=
    hhalf.trans hlogRaw
  have heq :
      t * optimizedRamseySlope β t -
          optimizedRamseyExponent β t =
        -Real.log (1 + t) +
          t ^ 2 * B * Real.exp (-t) := by
    dsimp [B]
    unfold optimizedRamseySlope optimizedRamseyExponent
      ramseyEntropy ramseyCorrection
    ring_nf
  rw [heq]
  nlinarith

theorem optimizedTangentPoint_mem_ramseyRegion
    {β t : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β ≤ 2 / 25)
    (ht : t ∈ Set.Ioc (0 : ℝ) 1)
    (hExp : HasRamseyExponent (optimizedRamseyExponent β)) :
    (tangentRegionX (optimizedRamseyExponent β)
        (optimizedRamseySlope β) t,
      tangentRegionY (optimizedRamseySlope β) t) ∈ ramseyRegion := by
  have hX0 :
      0 < tangentRegionX (optimizedRamseyExponent β)
        (optimizedRamseySlope β) t := Real.exp_pos _
  have hY0 :
      0 < tangentRegionY (optimizedRamseySlope β) t :=
    Real.exp_pos _
  have hX1 :
      tangentRegionX (optimizedRamseyExponent β)
          (optimizedRamseySlope β) t < 1 :=
    tangentRegionX_lt_one hβ0 hβ1 ht.1 ht.2
  have hY1 :
      tangentRegionY (optimizedRamseySlope β) t < 1 := by
    rw [tangentRegionY, Real.exp_lt_one_iff]
    linarith [optimizedRamseySlope_pos hβ0 ht.1 ht.2]
  apply exponentRegionCertificate_mem_ramseyRegion
    hX0 hX1 hY0 hY1
  · apply tangent_exponentRegionCertificate
    · intro r hr
      exact optimizedRamseyExponent_tangent_upper
        hβ0 hβ1 ht hr
    · exact tangentRegionY_le_tangentRegionX hβ0 ht
  · exact hExp

lemma beta0_pointwiseBookProfile :
    PointwiseBookProfile
      (optimizedRamseyExponent (2 / 25))
      (optimizedRamseySlope (2 / 25)) := by
  constructor
  · intro z hz
    exact optimizedRamseyExponent_nonneg_of_nonneg (by norm_num) hz
  · intro z hz
    exact hasDerivAt_optimizedRamseyExponent (2 / 25) hz
  · intro z hz
    unfold optimizedRamseySlope
    have hz0 : z ≠ 0 := ne_of_gt hz
    have hzp : z + 1 ≠ 0 := by linarith
    fun_prop
  · intro z hz
    let μ : ℝ := optimizationM z
    let p : ℝ := beta0PolynomialP z
    let x : ℝ := beta0PolynomialX z
    let y : ℝ := beta0PolynomialY z
    let q : ℝ := 9999 / 10000
    have hzIcc : z ∈ Set.Icc (0 : ℝ) 1 := ⟨hz.1.le, hz.2⟩
    have hU : (2 / 5 : ℝ) ≤ beta0U z :=
      beta0U_lower z hzIcc
    have hV : (3 / 4 : ℝ) ≤ beta0V z :=
      beta0V_lower z hzIcc
    have hpLower : (1 / 2 : ℝ) ≤ p := by
      simpa [p] using beta0PolynomialP_lower z hzIcc
    have hxLower : (1 / 5 : ℝ) ≤ x := by
      simpa [x] using beta0PolynomialX_lower z hzIcc
    have hμ : 0 < μ := by
      dsimp [μ, optimizationM]
      exact mul_pos hz.1 (Real.exp_pos _)
    have hμ1 : μ < 1 := by
      have he0 : 0 < Real.exp (-z) := Real.exp_pos _
      have he1 : Real.exp (-z) < 1 :=
        Real.exp_lt_one_iff.mpr (by linarith [hz.1])
      dsimp [μ, optimizationM]
      exact mul_lt_one_of_nonneg_of_lt_one_right hz.2 he0.le he1
    have hp : 0 < p := lt_of_lt_of_le (by norm_num) hpLower
    have hp1 : p < 1 := by
      have hzU : 0 < z * beta0U z :=
        mul_pos hz.1 (lt_of_lt_of_le (by norm_num) hU)
      dsimp [p, beta0PolynomialP]
      linarith
    have hx : 0 < x := lt_of_lt_of_le (by norm_num) hxLower
    have hx1 : x < 1 := by
      have hzV : 0 < z * beta0V z :=
        mul_pos hz.1 (lt_of_lt_of_le (by norm_num) hV)
      dsimp [x, beta0PolynomialX]
      linarith
    have hy : 0 < y := by
      dsimp [y, beta0PolynomialY]
      exact mul_pos hz.1 (by linarith)
    have hxy :
        x + y = 1 - z / 100000 := by
      dsimp [x, y, beta0PolynomialX, beta0PolynomialY]
      ring
    have hy1 : y < 1 := by
      nlinarith [hx, hz.1]
    have hA : 0 < 1 - μ := sub_pos.mpr hμ1
    have hlimit : x < p ^ ((1 : ℝ) / (1 - μ)) * (1 - μ) := by
      have hmarg := beta0PolynomialLimitLogMargin_pos z hz
      have hlog :
          Real.log x <
            Real.log p / (1 - μ) + Real.log (1 - μ) := by
        unfold beta0PolynomialLimitLogMargin at hmarg
        dsimp [p, x, μ] at *
        have hdiv :
            Real.log (beta0PolynomialX z) -
                Real.log (1 - optimizationM z) <
              Real.log (beta0PolynomialP z) /
                (1 - optimizationM z) := by
          rw [lt_div_iff₀ hA]
          linarith
        linarith
      calc
        x = Real.exp (Real.log x) := (Real.exp_log hx).symm
        _ < Real.exp
            (Real.log p / (1 - μ) + Real.log (1 - μ)) :=
          Real.exp_lt_exp.mpr hlog
        _ = Real.exp (Real.log p * (1 / (1 - μ))) *
              (1 - μ) := by
          rw [Real.exp_add, Real.exp_log hA]
          congr 2
          field_simp
        _ = p ^ ((1 : ℝ) / (1 - μ)) * (1 - μ) := by
          rw [Real.rpow_def_of_pos hp]
    let s : ℝ := x + z / 200000
    have hs0 : 0 < s := by
      dsimp [s]
      exact add_pos hx (div_pos hz.1 (by norm_num))
    have hs1 : s < 1 := by
      have hzV :
          z / 200000 < z * beta0V z := by
        have hdiff :
            0 < z * (beta0V z - 1 / 200000) :=
          mul_pos hz.1 (by linarith)
        linarith
      dsimp [s, x, beta0PolynomialX]
      linarith
    have hxs : x < s := by
      dsimp [s]
      exact lt_add_of_pos_right x (div_pos hz.1 (by norm_num))
    have hys : y < 1 - s := by
      dsimp [s]
      linarith [hxy, hz.1]
    have hregionBase : (s, 1 - s) ∈ ramseyRegion :=
      elementary_mem_ramseyRegion s hs0 hs1
    have hregion : (x, y) ∈ ramseyRegionInterior :=
      strict_mono_mem_ramseyRegionInterior
        hregionBase hx hxs hy hys
    let D : AdmissibleBookCellData :=
      { x := x
        y := y
        μ := μ
        p := p
        x_pos := hx
        x_lt_one := hx1
        y_pos := hy
        y_lt_one := hy1
        μ_pos := hμ
        μ_lt_one := hμ1
        p_pos := hp
        p_lt_one := hp1
        limit := hlimit
        region := hregion }
    refine ⟨D, q, ?_, ?_, ?_, ?_⟩
    · norm_num [q]
    · norm_num [q]
    · have hw : 0 < beta0V z - 1 / 100000 := by
        linarith
      have hlogμ :
          Real.log μ = Real.log z - z := by
        rw [show μ = z * Real.exp (-z) by rfl,
          Real.log_mul hz.1.ne' (Real.exp_ne_zero _),
          Real.log_exp]
        ring
      have hlogy :
          Real.log y =
            Real.log z +
              Real.log (beta0V z - 1 / 100000) := by
        rw [show y = z * (beta0V z - 1 / 100000) by rfl,
          Real.log_mul hz.1.ne' hw.ne']
      have hmarg := beta0PolynomialBookMargin_pos z hz
      have heq :
          beta0PolynomialBookMargin z =
            optimizedRamseyExponent (2 / 25) z +
              (Real.log x + z * Real.log μ +
                z * Real.log y) / 2 := by
        rw [beta0PolynomialBookMargin,
          show x = beta0PolynomialX z by rfl, hlogμ, hlogy]
        unfold optimizedRamseyExponent ramseyEntropy
        ring_nf
      rw [heq] at hmarg
      simpa [D, bookCellLogCost] using
        (show
          -(Real.log x + z * Real.log μ + z * Real.log y) / 2 <
            optimizedRamseyExponent (2 / 25) z by linarith)
    · have hblue :=
        beta0PolynomialBlueLogMargin_lower z hzIcc
      have hq : 0 < q := by norm_num [q]
      have hzu : 0 < z * beta0U z :=
        mul_pos hz.1 (lt_of_lt_of_le (by norm_num) hU)
      have hlogProduct :
          Real.log (q * (1 - p)) =
            Real.log q + Real.log z + Real.log (beta0U z) := by
        rw [show 1 - p = z * beta0U z by
          dsimp [p, beta0PolynomialP]; ring,
          Real.log_mul hq.ne' hzu.ne',
          Real.log_mul hz.1.ne'
            (lt_of_lt_of_le (by norm_num) hU).ne']
        ring
      have hlog :
          -optimizedRamseySlope (2 / 25) z <
            Real.log (q * (1 - p)) := by
        rw [hlogProduct]
        unfold beta0PolynomialBlueLogMargin at hblue
        unfold optimizedRamseySlope
        unfold beta0CorrectionSlope at hblue
        dsimp [q]
        rw [add_comm 1 z] at hblue
        linarith
      rw [← Real.exp_log (mul_pos hq (sub_pos.mpr hp1))]
      simpa [D] using Real.exp_lt_exp.mpr hlog

theorem hasRamseyExponent_beta0 :
    HasRamseyExponent (optimizedRamseyExponent (2 / 25)) :=
  hasRamseyExponent_of_pointwiseBookProfile
    beta0_pointwiseBookProfile
    (hasSmallRatioBase_optimizedRamseyExponent (by norm_num))

end Arxiv2407_19026
