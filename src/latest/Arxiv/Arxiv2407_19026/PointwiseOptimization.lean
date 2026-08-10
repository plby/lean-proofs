import Arxiv.Arxiv2407_19026.RegionBoost

/-!
# Pointwise-to-uniform optimization

This file formalizes the compactness step in Theorem `t:general`.  Its input
is pointwise strict numerical data.  Compactness turns those data into
finitely many applications of the book theorem for each error tolerance.
-/

noncomputable section

open Finset

namespace Arxiv2407_19026

/-- The logarithmic cost of one book cell at ratio `z`. -/
def bookCellLogCost (D : AdmissibleBookCellData) (z : ℝ) : ℝ :=
  -(Real.log D.x + z * Real.log D.μ + z * Real.log D.y) / 2

/-- Pointwise hypotheses for the optimization theorem.  Strictness is
essential: it supplies both the finite-cover neighborhoods and the
arbitrarily small loss used when natural-number floors are introduced. -/
structure PointwiseBookProfile (F S : ℝ → ℝ) : Prop where
  exponent_nonneg :
    ∀ z ∈ Set.Icc (0 : ℝ) 1, 0 ≤ F z
  deriv :
    ∀ z : ℝ, 0 < z → HasDerivAt F (S z) z
  slope_continuous :
    ∀ z : ℝ, 0 < z → ContinuousAt S z
  pointwise :
    ∀ z ∈ Set.Ioc (0 : ℝ) 1,
      ∃ (D : AdmissibleBookCellData) (q : ℝ),
        0 ≤ q ∧ q < 1 ∧
        bookCellLogCost D z < F z ∧
        Real.exp (-S z) < q * (1 - D.p)

/-- The separate small-ratio base case used in `t:general`. -/
def HasSmallRatioBase (F : ℝ → ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε →
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1 ∧
      ∃ K : ℕ, ∀ k l : ℕ,
        K ≤ k → 1 ≤ l → l ≤ k →
        (l : ℝ) / k < δ →
        RamseyProperty k l (exponentThreshold F ε k l)

/-- Exact entropy form of the elementary Ramsey bound. -/
lemma ramseyNumber_le_exp_ramseyEntropy
    {k l : ℕ} (hk : 1 ≤ k) (hl : 1 ≤ l) :
    (ramseyNumber k l : ℝ) ≤
      Real.exp (ramseyEntropy ((l : ℝ) / k) * k) := by
  let x : ℝ := (k : ℝ) / (k + l : ℕ)
  let y : ℝ := (l : ℝ) / (k + l : ℕ)
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  have hlR : (0 : ℝ) < l := by exact_mod_cast hl
  have hsumR : (0 : ℝ) < ((k + l : ℕ) : ℝ) := by positivity
  have hsumR' : (0 : ℝ) < (k : ℝ) + l := add_pos hkR hlR
  have hx : 0 < x := div_pos hkR hsumR
  have hy : 0 < y := div_pos hlR hsumR
  have hxy : y = 1 - x := by
    dsimp [x, y]
    push_cast
    field_simp
    ring
  have hx1 : x < 1 := by
    rw [← sub_pos, ← hxy]
    exact hy
  have helem :=
    ramseyNumber_le_elementary x hx hx1 k l hk hl
  have hxpow :
      x ^ k ≤ x ^ (k - 1) := by
    rw [show k = (k - 1) + 1 by omega, pow_succ]
    exact mul_le_of_le_one_right (pow_nonneg hx.le _) hx1.le
  have hypow :
      y ^ l ≤ y ^ (l - 1) := by
    have hy1 : y ≤ 1 := by
      rw [hxy]
      linarith
    rw [show l = (l - 1) + 1 by omega, pow_succ]
    exact mul_le_of_le_one_right (pow_nonneg hy.le _) hy1
  have hden :
      x ^ k * y ^ l ≤ x ^ (k - 1) * y ^ (l - 1) :=
    mul_le_mul hxpow hypow (pow_nonneg hy.le _) (pow_nonneg hx.le _)
  have hfull :
      1 / (x ^ (k - 1) * y ^ (l - 1)) ≤
        1 / (x ^ k * y ^ l) :=
    one_div_le_one_div_of_le (mul_pos (pow_pos hx _) (pow_pos hy _)) hden
  have hexp :
      Real.exp (ramseyEntropy ((l : ℝ) / k) * k) =
        1 / (x ^ k * y ^ l) := by
    rw [one_div, mul_inv, ← inv_pow, ← inv_pow,
      ← exp_neg_nat_mul_log hx k,
      ← exp_neg_nat_mul_log hy l,
      ← Real.exp_add]
    congr 1
    rw [ramseyEntropy_mul_eq_two_mass_entropy hkR hlR]
    dsimp [x, y]
    push_cast
    rw [Real.log_div hkR.ne' hsumR'.ne',
      Real.log_div hlR.ne' hsumR'.ne']
    ring
  calc
    (ramseyNumber k l : ℝ) ≤
        1 / (x ^ (k - 1) * (1 - x) ^ (l - 1)) := helem
    _ ≤ 1 / (x ^ k * y ^ l) := by simpa [hxy] using hfull
    _ = Real.exp (ramseyEntropy ((l : ℝ) / k) * k) :=
      hexp.symm

/-- The correction term never loses more than `z/4` on `[0,1]` when
`β ≥ 0`. -/
lemma neg_quarter_mul_le_ramseyCorrection
    {β z : ℝ} (hβ : 0 ≤ β) (hz : 0 ≤ z) :
    -(1 / 4 : ℝ) * z ≤ ramseyCorrection β z := by
  have he0 : 0 ≤ Real.exp (-z) := Real.exp_nonneg _
  have he1 : Real.exp (-z) ≤ 1 :=
    Real.exp_le_one_iff.mpr (by linarith)
  unfold ramseyCorrection
  nlinarith [mul_nonneg hβ (sq_nonneg z),
    mul_nonneg (by positivity : (0 : ℝ) ≤ 2 / 25) (by positivity : 0 ≤ z ^ 3),
    mul_nonneg (mul_nonneg hβ (sq_nonneg z)) he0,
    mul_nonneg
      (mul_nonneg (by positivity : (0 : ℝ) ≤ 2 / 25)
        (by positivity : 0 ≤ z ^ 3)) he0,
    mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 4) hz)
      (sub_nonneg.mpr he1)]

/-- Every optimized profile with nonnegative `β` has the small-ratio
entropy base required by the compact optimization theorem. -/
lemma hasSmallRatioBase_optimizedRamseyExponent
    {β : ℝ} (hβ : 0 ≤ β) :
    HasSmallRatioBase (optimizedRamseyExponent β) := by
  intro ε hε
  let δ : ℝ := min 1 (4 * ε)
  have hδ : 0 < δ := lt_min zero_lt_one (mul_pos (by norm_num) hε)
  have hδ1 : δ ≤ 1 := min_le_left _ _
  refine ⟨δ, hδ, hδ1, 1, ?_⟩
  intro k l hk hl hlk hratio
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  have hz0 : (0 : ℝ) ≤ (l : ℝ) / k := by positivity
  have hzε : (1 / 4 : ℝ) * ((l : ℝ) / k) < ε := by
    have hz4ε :
        (l : ℝ) / k < 4 * ε :=
      hratio.trans_le (min_le_right _ _)
    linarith
  have hcorrection :
      -(1 / 4 : ℝ) * ((l : ℝ) / k) ≤
        ramseyCorrection β ((l : ℝ) / k) :=
    neg_quarter_mul_le_ramseyCorrection hβ hz0
  have hcoeff :
      ramseyEntropy ((l : ℝ) / k) ≤
        optimizedRamseyExponent β ((l : ℝ) / k) + ε := by
    unfold optimizedRamseyExponent
    linarith
  have hR := ramseyNumber_le_exp_ramseyEntropy hk hl
  have hRtarget :
      (ramseyNumber k l : ℝ) ≤
        Real.exp
          ((optimizedRamseyExponent β ((l : ℝ) / k) + ε) * k) := by
    exact hR.trans (Real.exp_le_exp_of_le
      (mul_le_mul_of_nonneg_right hcoeff hkR.le))
  have hRfloor :
      ramseyNumber k l ≤
        exponentThreshold (optimizedRamseyExponent β) ε k l :=
    Nat.le_floor hRtarget
  exact Ramsey.ramseyProperty_mono_vertices hRfloor
    (Ramsey.ramseyNumber_spec k l)

/-- A strict elementary-region optimization point can be perturbed into
the strict hypotheses of `graph_good_bookCor`.  This removes all arbitrary
decimal slack from the numerical layer. -/
lemma exists_elementary_admissibleBookCellData
    {F S z μ p₀ X : ℝ}
    (hμ : 0 < μ) (hμ1 : μ < 1)
    (hp₀ : 0 < p₀) (hp₀1 : p₀ < 1)
    (hX :
      X = p₀ ^ ((1 : ℝ) / (1 - μ)) * (1 - μ))
    (hX0 : 0 < X) (hX1 : X < 1)
    (hbook :
      -(Real.log X + z * Real.log μ +
          z * Real.log (1 - X)) / 2 < F)
    (hblue : Real.exp (-S) = 1 - p₀) :
    ∃ (D : AdmissibleBookCellData) (q : ℝ),
      0 ≤ q ∧ q < 1 ∧
      bookCellLogCost D z < F ∧
      Real.exp (-S) < q * (1 - D.p) := by
  let r : ℝ := 1 / (1 - μ)
  let pp : ℝ → ℝ := fun η ↦ p₀ - η
  let lim : ℝ → ℝ := fun η ↦ pp η ^ r * (1 - μ)
  let xx : ℝ → ℝ := fun η ↦ lim η - η
  let yy : ℝ → ℝ := fun η ↦ 1 - lim η - η
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
  have hyy0 : yy 0 = 1 - X := by simp [yy, hlim0]
  have hcostCont :
      ContinuousAt
        (fun η : ℝ ↦
          -(Real.log (xx η) + z * Real.log μ +
            z * Real.log (yy η)) / 2) 0 := by
    have hxlog := hxxCont.log (by simpa [hxx0] using hX0.ne')
    have hylog := hyyCont.log (by
      rw [hyy0]
      exact (sub_pos.mpr hX1).ne')
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
    continuousAt_const.eventually_lt hyyCont (by
      rw [hyy0]
      exact sub_pos.mpr hX1)
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
  have hlimη :
      lim η = pp η ^ ((1 : ℝ) / (1 - μ)) * (1 - μ) := by
    rfl
  have hsum : xx η + yy η = 1 - 2 * η := by
    dsimp [xx, yy]
    ring
  have hxx1 : xx η < 1 := by
    nlinarith [hyyη]
  have hyy1 : yy η < 1 := by
    nlinarith [hxxη]
  have hlimit : xx η < lim η := by
    dsimp [xx]
    linarith
  have hregionBase :
      (lim η, 1 - lim η) ∈ ramseyRegion := by
    apply elementary_mem_ramseyRegion
    · dsimp [lim]
      exact mul_pos
        (Real.rpow_pos_of_pos hppη _)
        (sub_pos.mpr hμ1)
    · have hylink : yy η = 1 - lim η - η := rfl
      linarith [hyyη]
  have hregion :
      (xx η, yy η) ∈ ramseyRegionInterior := by
    apply strict_mono_mem_ramseyRegionInterior hregionBase
    · exact hxxη
    · exact hlimit
    · exact hyyη
    · dsimp [yy]
      linarith
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
      limit := by simpa [hlimη] using hlimit
      region := hregion }
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

/-- Mean-value-theorem form of one blue-neighborhood step. -/
lemma exponential_blue_step_of_hasDerivAt
    {F S : ℝ → ℝ} {q p : ℝ} {k l : ℕ}
    (hk : 1 ≤ k) (hl : 2 ≤ l)
    (hderiv : ∀ z : ℝ, 0 < z → HasDerivAt F (S z) z)
    (hfactor :
      ∀ z ∈ Set.Icc
          (((l - 1 : ℕ) : ℝ) / k) ((l : ℝ) / k),
        Real.exp (-S z) ≤ q * (1 - p)) :
    Real.exp (F (((l - 1 : ℕ) : ℝ) / k) * k) ≤
      q * (1 - p) * Real.exp (F ((l : ℝ) / k) * k) := by
  let a : ℝ := ((l - 1 : ℕ) : ℝ) / k
  let b : ℝ := (l : ℝ) / k
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  have ha : 0 < a := by
    dsimp [a]
    exact div_pos (by exact_mod_cast (show 0 < l - 1 by omega)) hkR
  have hab : a < b := by
    dsimp [a, b]
    rw [div_lt_div_iff_of_pos_right hkR]
    exact_mod_cast (by omega : l - 1 < l)
  have hcont : ContinuousOn F (Set.Icc a b) := by
    intro z hz
    exact (hderiv z (ha.trans_le hz.1)).continuousAt.continuousWithinAt
  have hderiv' :
      ∀ z ∈ Set.Ioo a b, HasDerivAt F (S z) z := by
    intro z hz
    exact hderiv z (ha.trans hz.1)
  obtain ⟨c, hc, hmean⟩ :=
    exists_hasDerivAt_eq_slope F S hab hcont hderiv'
  have hba : b - a = 1 / (k : ℝ) := by
    dsimp [a, b]
    rw [div_sub_div_same]
    congr 1
    norm_num [Nat.cast_sub (by omega : 1 ≤ l)]
  have hdiff :
      (F a - F b) * k = -S c := by
    rw [hmean, hba]
    field_simp [hkR.ne']
    ring
  have hcFactor :
      Real.exp (-S c) ≤ q * (1 - p) :=
    hfactor c ⟨hc.1.le, hc.2.le⟩
  calc
    Real.exp (F a * k) =
        Real.exp ((F a - F b) * k) *
          Real.exp (F b * k) := by
      rw [← Real.exp_add]
      congr 1
      ring
    _ = Real.exp (-S c) * Real.exp (F b * k) := by
      rw [hdiff]
    _ ≤ (q * (1 - p)) * Real.exp (F b * k) := by
      gcongr
    _ = q * (1 - p) *
        Real.exp (F ((l : ℝ) / k) * k) := by
      rfl

/-- The compactness-and-induction theorem underlying `t:general`.

For each `ε`, the small-ratio hypothesis supplies `δ`.  The pointwise strict
book data give an open cover of `[δ,1]`; a finite subcover makes the integer
level in `graph_good_bookCor` uniform, and a Lebesgue number makes one blue
step remain inside the selected cell's neighborhood. -/
theorem hasRamseyExponent_of_pointwiseBookProfile
    {F S : ℝ → ℝ}
    (P : PointwiseBookProfile F S)
    (hsmall : HasSmallRatioBase F) :
    HasRamseyExponent F := by
  apply hasRamseyExponent_of_certificates
  intro ε hε
  obtain ⟨δ, hδ, hδ1, Ksmall, hKsmall⟩ :=
    hsmall ε hε
  let Kset : Set ℝ := Set.Icc δ 1
  let Center := {z : ℝ // z ∈ Kset}
  have hcenterIoc (z : Center) :
      (z : ℝ) ∈ Set.Ioc (0 : ℝ) 1 := by
    exact ⟨hδ.trans_le z.property.1, z.property.2⟩
  have hpoint :
      ∀ z : Center, ∃ (D : AdmissibleBookCellData) (q : ℝ),
        0 ≤ q ∧ q < 1 ∧
        bookCellLogCost D z < F z ∧
        Real.exp (-S z) < q * (1 - D.p) := by
    intro z
    exact P.pointwise z (hcenterIoc z)
  choose D qCell hqCell0 hqCell1 hDbook hDblue using hpoint
  have hgood_nhds (z : Center) :
      {w : ℝ |
          bookCellLogCost (D z) w < F w ∧
          Real.exp (-S w) < qCell z * (1 - (D z).p)} ∈
        nhds (z : ℝ) := by
    have hzpos : (0 : ℝ) < z := (hcenterIoc z).1
    have hFcont : ContinuousAt F z :=
      (P.deriv z hzpos).continuousAt
    have hcostCont :
        ContinuousAt (bookCellLogCost (D z)) z := by
      unfold bookCellLogCost
      fun_prop
    have hbookEvent :
        ∀ᶠ w : ℝ in nhds (z : ℝ),
          bookCellLogCost (D z) w < F w :=
      hcostCont.eventually_lt hFcont (hDbook z)
    have hnegS :
        ContinuousAt (fun w : ℝ ↦ -S w) z :=
      (P.slope_continuous z hzpos).neg
    have hexpS :
        ContinuousAt (fun w : ℝ ↦ Real.exp (-S w)) z := by
      change ContinuousAt (Real.exp ∘ fun w : ℝ ↦ -S w) z
      exact Real.continuous_exp.continuousAt.comp hnegS
    have hblueEvent :
        ∀ᶠ w : ℝ in nhds (z : ℝ),
          Real.exp (-S w) < qCell z * (1 - (D z).p) :=
      hexpS.eventually_lt continuousAt_const (hDblue z)
    filter_upwards [hbookEvent, hblueEvent] with w hwbook hwblue
    exact ⟨hwbook, hwblue⟩
  have hopenChoice :
      ∀ z : Center, ∃ U : Set ℝ,
        U ⊆ {w : ℝ |
          bookCellLogCost (D z) w < F w ∧
          Real.exp (-S w) < qCell z * (1 - (D z).p)} ∧
        IsOpen U ∧ (z : ℝ) ∈ U := by
    intro z
    exact mem_nhds_iff.1 (hgood_nhds z)
  choose U hUsub hUopen hUz using hopenChoice
  have hKcompact : IsCompact Kset := by
    simpa [Kset] using (isCompact_Icc : IsCompact (Set.Icc δ 1))
  have hcover : Kset ⊆ ⋃ z : Center, U z := by
    intro w hw
    rw [Set.mem_iUnion]
    exact ⟨⟨w, hw⟩, hUz ⟨w, hw⟩⟩
  obtain ⟨t, ht⟩ :=
    hKcompact.elim_finite_subcover U hUopen hcover
  have hδmem : δ ∈ Kset := by
    exact ⟨le_rfl, hδ1⟩
  have htNonempty : t.Nonempty := by
    obtain ⟨z, hzt, _hzU⟩ := Set.mem_iUnion₂.1 (ht hδmem)
    exact ⟨z, hzt⟩
  let q : ℝ := t.sup' htNonempty qCell
  have hq1 : q < 1 := by
    obtain ⟨z, hz, hqz⟩ :=
      Finset.exists_mem_eq_sup' htNonempty qCell
    change t.sup' htNonempty qCell < 1
    rw [hqz]
    exact hqCell1 z
  have hqCell_le (i : ↥t) : qCell i.1 ≤ q := by
    exact Finset.le_sup' qCell i.2
  have hcoverT :
      Kset ⊆ ⋃ i : ↥t, U i.1 := by
    intro w hw
    obtain ⟨z, hzt, hwU⟩ := Set.mem_iUnion₂.1 (ht hw)
    rw [Set.mem_iUnion]
    exact ⟨⟨z, hzt⟩, hwU⟩
  obtain ⟨ρ, hρ, hLeb⟩ :=
    lebesgue_number_lemma_of_metric hKcompact
      (fun i : ↥t ↦ hUopen i.1) hcoverT
  obtain ⟨i₀, hi₀⟩ := hLeb δ hδmem
  letI : Nonempty ↥t := ⟨i₀⟩
  have hpickExists :
      ∀ w : ℝ, ∃ i : ↥t,
        w ∈ Kset → Metric.ball w ρ ⊆ U i.1 := by
    intro w
    by_cases hw : w ∈ Kset
    · obtain ⟨i, hi⟩ := hLeb w hw
      exact ⟨i, fun _ ↦ hi⟩
    · exact ⟨i₀, fun h ↦ (hw h).elim⟩
  choose pick hpick using hpickExists
  let cells : ↥t → BookDescentCell.{0} :=
    fun i ↦ (D i.1).toCell
  let select : ℕ → ℕ → ↥t :=
    fun k l ↦ pick ((l : ℝ) / k)
  let active : ℕ → ℕ → Prop :=
    fun k l ↦
      δ ≤ (l : ℝ) / k ∧ bookDescentLevel cells ≤ l
  obtain ⟨Kstep, hKstep⟩ := Filter.eventually_atTop.1
    (tendsto_natCast_atTop_atTop.eventually
      (Filter.eventually_gt_atTop (1 / ρ : ℝ)))
  obtain ⟨Kfixed, hKfixed⟩ :=
    exists_small_l_base_cutoff
      P.exponent_nonneg hε (bookDescentLevel cells)
  let K₀ := max Ksmall (max Kfixed (max Kstep 1))
  have hK₀small : Ksmall ≤ K₀ :=
    le_max_left _ _
  have hK₀fixed : Kfixed ≤ K₀ :=
    (le_max_left Kfixed (max Kstep 1)).trans
      (le_max_right Ksmall _)
  have hK₀step : Kstep ≤ K₀ :=
    (le_trans (le_max_left Kstep 1)
      (le_max_right Kfixed (max Kstep 1))).trans
      (le_max_right Ksmall _)
  have hK₀one : 1 ≤ K₀ :=
    (le_trans (le_max_right Kstep 1)
      (le_max_right Kfixed (max Kstep 1))).trans
      (le_max_right Ksmall _)
  apply nonempty_descentCertificate_of_bookCellsOn
    hε cells select active hq1
      P.exponent_nonneg K₀
  · intro k l _hk _hl _hlk hactive
    exact hactive.2
  · intro k l hk hl hlk hinactive
    by_cases hratio : (l : ℝ) / k < δ
    · exact hKsmall k l (hK₀small.trans hk) hl hlk hratio
    · have hδratio : δ ≤ (l : ℝ) / k := le_of_not_gt hratio
      have hnotlevel : ¬bookDescentLevel cells ≤ l :=
        fun hlevel ↦ hinactive ⟨hδratio, hlevel⟩
      exact hKfixed k l (hK₀fixed.trans hk) hl hlk (by omega)
  · intro k l hk hl hlk hactive
    have hk1 : 1 ≤ k := hK₀one.trans hk
    have hkR : (0 : ℝ) < k := by exact_mod_cast hk1
    let b : ℝ := (l : ℝ) / k
    have hbK : b ∈ Kset := by
      constructor
      · exact hactive.1
      · dsimp [b]
        rw [div_le_one hkR]
        exact_mod_cast hlk
    let i : ↥t := pick b
    have hballSubset : Metric.ball b ρ ⊆ U i.1 := by
      exact hpick b hbK
    have hbU : b ∈ U i.1 := by
      apply hballSubset
      exact Metric.mem_ball.2 (by simpa using hρ)
    have hgood := hUsub i.1 hbU
    have hlog :
        bookCellLogCost (D i.1) b ≤ F b :=
      hgood.1.le
    have hraw :=
      bookGraphThreshold_le_exp_of_log
        (D i.1).x_pos (D i.1).y_pos (D i.1).μ_pos
        hk1 (by simpa [bookCellLogCost, b] using hlog)
    simpa [cells, select, i, b] using hraw
  · intro k l hk hl hlk hactive
    have hk1 : 1 ≤ k := hK₀one.trans hk
    have hkR : (0 : ℝ) < k := by exact_mod_cast hk1
    have hl2 : 2 ≤ l :=
      (two_le_bookDescentLevel cells).trans hactive.2
    let a : ℝ := ((l - 1 : ℕ) : ℝ) / k
    let b : ℝ := (l : ℝ) / k
    have hbK : b ∈ Kset := by
      constructor
      · exact hactive.1
      · dsimp [b]
        rw [div_le_one hkR]
        exact_mod_cast hlk
    let i : ↥t := pick b
    have hballSubset : Metric.ball b ρ ⊆ U i.1 := by
      exact hpick b hbK
    have hkρcast : 1 / ρ < (k : ℝ) :=
      hKstep k (hK₀step.trans hk)
    have hstep : 1 / (k : ℝ) < ρ := by
      have hmul : 1 < (k : ℝ) * ρ :=
        (div_lt_iff₀ hρ).1 hkρcast
      exact (div_lt_iff₀ hkR).2 (by nlinarith)
    have hfactor :
        ∀ z ∈ Set.Icc a b,
          Real.exp (-S z) ≤ q * (1 - (D i.1).p) := by
      intro z hz
      have hab : a ≤ b := by
        dsimp [a, b]
        rw [div_le_div_iff_of_pos_right hkR]
        exact_mod_cast (show l - 1 ≤ l by omega)
      have habdist : dist a b = 1 / (k : ℝ) := by
        rw [Real.dist_eq, abs_of_nonpos (sub_nonpos.mpr hab)]
        dsimp [a, b]
        rw [Nat.cast_sub (by omega : 1 ≤ l)]
        field_simp [hkR.ne']
        ring
      have hzdist : dist z b ≤ dist a b := by
        calc
          dist z b = b - z := by
            rw [Real.dist_eq,
              abs_of_nonpos (sub_nonpos.mpr hz.2)]
            ring
          _ ≤ b - a := sub_le_sub_left hz.1 b
          _ = dist a b := by
            rw [Real.dist_eq,
              abs_of_nonpos (sub_nonpos.mpr hab)]
            ring
      have hzball : z ∈ Metric.ball b ρ := by
        rw [Metric.mem_ball]
        exact hzdist.trans_lt (habdist.trans_lt hstep)
      have hzgood := hUsub i.1 (hballSubset hzball)
      exact hzgood.2.le.trans
        (mul_le_mul_of_nonneg_right (hqCell_le i)
          (sub_nonneg.mpr (D i.1).p_lt_one.le))
    have hraw :=
      exponential_blue_step_of_hasDerivAt
        hk1 hl2 P.deriv (q := q) (p := (D i.1).p)
        (by simpa [a, b] using hfactor)
    simpa [cells, select, i, b] using hraw

end Arxiv2407_19026
