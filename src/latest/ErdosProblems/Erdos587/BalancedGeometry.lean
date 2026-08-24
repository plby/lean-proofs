import ErdosProblems.Erdos587.NguyenVuCompletion

open scoped BigOperators Pointwise

namespace Erdos587
open NVGeneration

/-- The configured size hypothesis already puts the ambient parameter beyond
the fixed threshold in the balanced rectangle construction. -/
lemma configured_balanced_scale_threshold
    {A : Finset ℕ} {N N₀ p : ℕ}
    (hp : 0 < p) (hpN : p * N ≤ N₀)
    (hAN : A ⊆ Finset.Icc 1 N)
    (hlarge : nvOneStepLoss N₀ * nvBinaryLogScale N < A.card) :
    nvBalancedScaleThreshold ≤ nvCubicScale N₀ := by
  have hcard := card_le_ambient_of_subset_Icc hAN
  have hNN₀ := ambient_le_of_mul_le hp hpN
  have hS := nvCubicScale_pos N₀
  have hC := nvMasterConstant_pos
  have hlog := nvBinaryLogScale_pos N₀
  have hloss : nvOneStepLoss N₀ < A.card :=
    (Nat.le_mul_of_pos_right _ (nvBinaryLogScale_pos N)).trans_lt hlarge
  have hbase : nvMasterConstant ^ 10 * nvCubicScale N₀ ≤ nvOneStepLoss N₀ := by
    exact Nat.le_mul_of_pos_right _ (pow_pos hlog _)
  have hN₀ : 0 < N₀ := (nvOneStepLoss_pos N₀).trans (hloss.trans_le (hcard.trans hNN₀))
  have hcube := ambient_le_sixty_four_mul_scale_cube hN₀
  change N₀ ≤ 64 * nvCubicScale N₀ ^ 3 at hcube
  have hcancel : nvMasterConstant ^ 10 < 64 * nvCubicScale N₀ ^ 2 := by
    apply (Nat.mul_lt_mul_right hS).mp
    calc
      nvMasterConstant ^ 10 * nvCubicScale N₀ ≤ nvOneStepLoss N₀ := hbase
      _ < A.card := hloss
      _ ≤ N₀ := hcard.trans hNN₀
      _ ≤ 64 * nvCubicScale N₀ ^ 3 := hcube
      _ = 64 * nvCubicScale N₀ ^ 2 * nvCubicScale N₀ := by ring
  have hCbig : 4096 ≤ nvMasterConstant := by
    unfold nvMasterConstant
    omega
  have hCpow := Nat.pow_le_pow_left hCbig 10
  by_contra hnot
  have hsmall : nvCubicScale N₀ < 2 ^ 40 := by
    simpa only [nvBalancedScaleThreshold] using Nat.lt_of_not_ge hnot
  have hsq := Nat.pow_le_pow_left hsmall.le 2
  norm_num at hCpow hsq
  omega

/-- The cardinality comparison needed in the balanced rectangle lemma also
follows from the configured size hypothesis. -/
lemma configured_balanced_master_card
    {A : Finset ℕ} {N N₀ : ℕ}
    (hlarge : nvOneStepLoss N₀ * nvBinaryLogScale N < A.card) :
    12 * nvMasterConstant ^ 2 ≤ A.card := by
  have hC : 12 ≤ nvMasterConstant := by unfold nvMasterConstant; omega
  have hCpos := nvMasterConstant_pos
  have hpow : 12 * nvMasterConstant ^ 2 ≤ nvMasterConstant ^ 10 := by
    calc
      12 * nvMasterConstant ^ 2 ≤ nvMasterConstant * nvMasterConstant ^ 2 := by gcongr
      _ = nvMasterConstant ^ 3 := by ring
      _ ≤ nvMasterConstant ^ 10 := Nat.pow_le_pow_right hCpos (by omega)
  calc
    12 * nvMasterConstant ^ 2 ≤ nvMasterConstant ^ 10 := hpow
    _ ≤ nvMasterConstant ^ 10 * nvCubicScale N₀ :=
      Nat.le_mul_of_pos_right _ (nvCubicScale_pos N₀)
    _ ≤ nvOneStepLoss N₀ :=
      Nat.le_mul_of_pos_right _ (pow_pos (nvBinaryLogScale_pos N₀) _)
    _ ≤ nvOneStepLoss N₀ * nvBinaryLogScale N :=
      Nat.le_mul_of_pos_right _ (nvBinaryLogScale_pos N)
    _ ≤ A.card := hlarge.le

/-- A useful logarithmic reserve: once the binary logarithm is nonzero, the
initial polylogarithm absorbs two powers of the master constant. -/
lemma configured_initial_polylog_large {N₀ : ℕ} (hN₀ : 2 ≤ N₀) :
    2 ^ 32 * nvMasterConstant ^ 2 ≤ nvInitialPolylog N₀ := by
  have hell : 2 ≤ nvBinaryLogScale N₀ := by
    have := Nat.log_mono_right (b := 2) hN₀
    norm_num [nvBinaryLogScale] at *
    omega
  have hCpow : nvMasterConstant ≤ 2 ^ nvMasterConstant := nvMasterConstant.lt_two_pow_self.le
  have hexp : nvMasterConstant + 32 ≤ nvInitialLogExponent := by
    unfold nvInitialLogExponent
    omega
  calc
    2 ^ 32 * nvMasterConstant ^ 2 =
        nvMasterConstant * (nvMasterConstant * 2 ^ 32) := by ring
    _ ≤ nvMasterConstant * (2 ^ nvMasterConstant * 2 ^ 32) := by gcongr
    _ = nvMasterConstant * 2 ^ (nvMasterConstant + 32) := by rw [pow_add]
    _ ≤ nvMasterConstant * 2 ^ nvInitialLogExponent := by gcongr; norm_num
    _ ≤ nvMasterConstant * nvBinaryLogScale N₀ ^ nvInitialLogExponent := by gcongr
    _ = nvInitialPolylog N₀ := rfl

/-- The stopped product and ambient bounds imply the square-root width
condition underlying the congruence locator in the balanced case. -/
lemma balanced_step_width_budget
    {m S J K c b L₁ L₂ H : ℕ}
    (hm : 0 < m) (hS : 0 < S) (_hJ : 0 < J) (hL₂ : 0 < L₂)
    (hproduct : m * (S * J) ^ 2 ≤ K * (L₁ * L₂))
    (hspan : c * b * L₂ ≤ m * H)
    (hambient : H ≤ 64 * S ^ 3) (hside : S * J ≤ L₁) :
    c * b * J ^ 3 ≤ 64 * K * L₁ ^ 2 := by
  have hfirst : c * b * (S * J) ^ 2 ≤ K * L₁ * H := by
    apply Nat.le_of_mul_le_mul_right (c := m * L₂) _ (Nat.mul_pos hm hL₂)
    calc
      c * b * (S * J) ^ 2 * (m * L₂) =
          (c * b * L₂) * (m * (S * J) ^ 2) := by ring
      _ ≤ (m * H) * (K * (L₁ * L₂)) := Nat.mul_le_mul hspan hproduct
      _ = K * L₁ * H * (m * L₂) := by ring
  have hsecond : c * b * J ^ 2 ≤ 64 * K * L₁ * S := by
    apply Nat.le_of_mul_le_mul_right (c := S ^ 2) _ (pow_pos hS 2)
    calc
      c * b * J ^ 2 * S ^ 2 = c * b * (S * J) ^ 2 := by ring
      _ ≤ K * L₁ * H := hfirst
      _ ≤ K * L₁ * (64 * S ^ 3) := by gcongr
      _ = 64 * K * L₁ * S * S ^ 2 := by ring
  calc
    c * b * J ^ 3 = (c * b * J ^ 2) * J := by ring
    _ ≤ (64 * K * L₁ * S) * J := Nat.mul_le_mul_right J hsecond
    _ = 64 * K * L₁ * (S * J) := by ring
    _ ≤ 64 * K * L₁ * L₁ := by gcongr
    _ = 64 * K * L₁ ^ 2 := by ring

/-- A square-root width budget is enough for the primitive quadratic-value
threshold, including the common coefficient factor. -/
lemma reduced_period_threshold_of_square_width
    {c b ρ C L₁ : ℕ} (_hc : 0 < c) (hb : 0 < b) (_hρ : 0 < ρ)
    (hρc : ρ ≤ c) (hρb : ρ ∣ b)
    (hwidth : (64 * (C + 2)) ^ 2 * (c * b) ≤ L₁ ^ 2) :
    ρ + ρ * (7 + 8 * (C + Nat.sqrt (ordCompl[2] (b / ρ)))) ≤ L₁ / 8 := by
  let T := Nat.sqrt (c * b)
  let U := Nat.sqrt (ordCompl[2] (b / ρ))
  have hρle : ρ ≤ b := Nat.le_of_dvd hb hρb
  have hρT : ρ ≤ T := by
    apply Nat.le_sqrt.mpr
    simpa only [pow_two] using Nat.mul_le_mul hρc hρle
  have hUT : ρ * U ≤ T := by
    apply Nat.le_sqrt.mpr
    rw [← pow_two]
    have hUsq : U ^ 2 ≤ b / ρ :=
      (Nat.sqrt_le' _).trans (Nat.ordCompl_le _ 2)
    calc
      (ρ * U) ^ 2 = ρ * (ρ * U ^ 2) := by ring
      _ ≤ ρ * (ρ * (b / ρ)) := by gcongr
      _ = ρ * b := by rw [Nat.mul_div_cancel' hρb]
      _ ≤ c * b := by gcongr
  have hTwidth : 64 * (C + 2) * T ≤ L₁ := by
    apply (Nat.pow_le_pow_iff_left (by omega : 2 ≠ 0)).mp
    calc
      (64 * (C + 2) * T) ^ 2 = (64 * (C + 2)) ^ 2 * T ^ 2 := by ring
      _ ≤ (64 * (C + 2)) ^ 2 * (c * b) := by
        gcongr
        exact Nat.sqrt_le' _
      _ ≤ L₁ ^ 2 := hwidth
  apply (Nat.le_div_iff_mul_le (by omega : 0 < 8)).mpr
  calc
    (ρ + ρ * (7 + 8 * (C + U))) * 8 =
        64 * (C + 1) * ρ + 64 * (ρ * U) := by ring
    _ ≤ 64 * (C + 1) * T + 64 * T := by gcongr
    _ = 64 * (C + 2) * T := by ring
    _ ≤ L₁ := hTwidth

private lemma period_constant_pow_bound {C J : ℕ}
    (hC : 0 < C) (hJ : 512 * C ^ 2 ≤ J) :
    768 * C ^ 2 * (64 * (C + 2)) ^ 2 ≤ J ^ 3 := by
  calc
    768 * C ^ 2 * (64 * (C + 2)) ^ 2 ≤
        768 * C ^ 2 * (64 * (3 * C)) ^ 2 := by
      gcongr
      omega
    _ = 28311552 * C ^ 4 := by ring
    _ ≤ 134217728 * C ^ 6 := by
      exact Nat.mul_le_mul (by norm_num)
        (Nat.pow_le_pow_right hC (by omega))
    _ = (512 * C ^ 2) ^ 3 := by ring
    _ ≤ J ^ 3 := Nat.pow_le_pow_left hJ 3

lemma initial_polylog_dominates_period_constant {N₀ : ℕ} (hN₀ : 2 ≤ N₀) :
    768 * nvMasterConstant ^ 2 * (64 * (nvMasterConstant + 2)) ^ 2 ≤
      nvInitialPolylog N₀ ^ 3 := by
  apply period_constant_pow_bound nvMasterConstant_pos
  exact (Nat.mul_le_mul_right _ (by norm_num : 512 ≤ 2 ^ 32)).trans
    (configured_initial_polylog_large hN₀)

/-- The rank-two product lower bound and the ambient bound discharge the
width threshold in the full reduced-period branch, without any Weyl-sum
estimate. -/
lemma configured_balanced_reduced_period_threshold
    {A : Finset ℕ} {N N₀ p q₁ q₂ L₁ L₂ z₀ : ℕ}
    (hp : 0 < p) (hpN : p * N ≤ N₀) (hN₀ : 2 ≤ N₀)
    (hA : 0 < A.card) (hq₁ : 0 < q₁) (hq₂ : 0 < q₂)
    (hL₂ : 0 < L₂)
    (hproduct : A.card * (nvCubicScale N₀ * nvInitialPolylog N₀) ^ 2 ≤
      12 * nvMasterConstant ^ 2 * (L₁ * L₂))
    (hspan : q₂ * L₂ ≤ A.card * N)
    (hside : nvCubicScale N₀ * nvInitialPolylog N₀ ≤ L₁) :
    let g := q₁.gcd q₂
    let b := q₂ / g
    let ρ := ((p * g).gcd (2 * p * z₀)).gcd b
    ρ + ρ * (7 + 8 * (nvReducedPeriodConstant +
      Nat.sqrt (ordCompl[2] (b / ρ)))) ≤ L₁ / 8 := by
  let g := q₁.gcd q₂
  let b := q₂ / g
  let c := p * g
  let ρ := (c.gcd (2 * p * z₀)).gcd b
  have hg : 0 < g := Nat.gcd_pos_of_pos_left q₂ hq₁
  have hb : 0 < b := Nat.div_pos (Nat.gcd_le_right q₁ hq₂) hg
  have hc : 0 < c := Nat.mul_pos hp hg
  have hρ : 0 < ρ := Nat.gcd_pos_of_pos_right _ hb
  have hgb : g * b = q₂ := Nat.mul_div_cancel' (Nat.gcd_dvd_right q₁ q₂)
  have hspan' : c * b * L₂ ≤ A.card * N₀ := by
    calc
      c * b * L₂ = p * (q₂ * L₂) := by dsimp only [c]; rw [← hgb]; ring
      _ ≤ p * (A.card * N) := Nat.mul_le_mul_left p hspan
      _ = A.card * (p * N) := by ring
      _ ≤ A.card * N₀ := Nat.mul_le_mul_left _ hpN
  have hbudget := balanced_step_width_budget hA (nvCubicScale_pos N₀)
    (nvInitialPolylog_pos N₀) hL₂ hproduct hspan'
    (ambient_le_sixty_four_mul_scale_cube (by omega : 0 < N₀)) hside
  have hwidth : (64 * (nvMasterConstant + 2)) ^ 2 * (c * b) ≤ L₁ ^ 2 := by
    have hC := nvMasterConstant_pos
    apply Nat.le_of_mul_le_mul_left (c := 768 * nvMasterConstant ^ 2) _ (by positivity)
    calc
      768 * nvMasterConstant ^ 2 *
          ((64 * (nvMasterConstant + 2)) ^ 2 * (c * b)) =
          (c * b) * (768 * nvMasterConstant ^ 2 * (64 * (nvMasterConstant + 2)) ^ 2) := by ring
      _ ≤ (c * b) * nvInitialPolylog N₀ ^ 3 :=
        Nat.mul_le_mul_left _ (initial_polylog_dominates_period_constant hN₀)
      _ ≤ 768 * nvMasterConstant ^ 2 * L₁ ^ 2 := by
        convert hbudget using 1
        ring
  have hρc : ρ ≤ c :=
    (Nat.gcd_le_left _ (Nat.gcd_pos_of_pos_left _ hc)).trans (Nat.gcd_le_left _ hc)
  have hthreshold := reduced_period_threshold_of_square_width
    hc hb hρ hρc (Nat.gcd_dvd_right (c.gcd (2 * p * z₀)) b) hwidth
  change ρ + ρ * (7 + 8 * (nvReducedPeriodConstant +
    Nat.sqrt (ordCompl[2] (b / ρ)))) ≤ L₁ / 8
  calc
    _ ≤ ρ + ρ * (7 + 8 * (nvMasterConstant +
      Nat.sqrt (ordCompl[2] (b / ρ)))) := by
      gcongr
      exact nvReducedPeriodConstant_le_master
    _ ≤ L₁ / 8 := hthreshold

/-- With a full reduced period in the canonical quadratic interval, all the
remaining conditions of the balanced locator follow from the configured
stopped-sumset bounds. -/
theorem configured_balanced_locator_of_full_reduced_period
    {A B : Finset ℕ} {N N₀ p s b₀ r q₁ q₂ L₁ L₂ z₀ u : ℕ} {t : ℤ}
    (hp : 0 < p) (hpN : p * N ≤ N₀)
    (hAN : A ⊆ Finset.Icc 1 N)
    (hlarge : nvOneStepLoss N₀ * nvBinaryLogScale N < A.card)
    (hq₁ : 0 < q₁) (hq₂ : 0 < q₂)
    (hfamily : ∀ u ∈ B.subsetSum, ∀ x ≤ L₁, ∀ y ≤ L₂,
      r + u + q₁ * x + q₂ * y ∈ A.subsetSum)
    (hinj : ∀ x₁ ≤ L₁, ∀ y₁ ≤ L₂, ∀ x₂ ≤ L₁, ∀ y₂ ≤ L₂,
      r + q₁ * x₁ + q₂ * y₁ = r + q₁ * x₂ + q₂ * y₂ →
        x₁ = x₂ ∧ y₁ = y₂)
    (hspan : q₁ * L₁ + q₂ * L₂ ≤ A.card * N)
    (hW : (A.card / 2) * (nvCubicScale N₀ * nvInitialPolylog N₀) ^ 3 ≤
      nvRobustCubicLoss 64 * b₀ * (2 ^ s) ^ 3)
    (hscaled : b₀ * (2 ^ s) ^ 2 ≤
      nvStoppedBudgetScaledCardFactor 64 * ((L₁ + 1) * (L₂ + 1)))
    (hDU : 2 ^ s ≤ nvCubicScale N₀ * nvInitialPolylog N₀)
    (hL₁ : nvCubicScale N₀ * nvInitialPolylog N₀ ≤ L₁)
    (hL₂ : nvCubicScale N₀ * nvInitialPolylog N₀ ≤ L₂)
    (horient : q₁ * L₁ ≤ q₂ * L₂)
    (hu : u ∈ B.subsetSum) (hz₀ : z₀ < q₁.gcd q₂)
    (hbase : ((r + u : ℕ) : ℤ) =
      (p : ℤ) * (z₀ : ℤ) ^ 2 + t * (q₁.gcd q₂ : ℕ))
    (hperiod :
      let g := q₁.gcd q₂
      let b := q₂ / g
      let ρ := ((p * g).gcd (2 * p * z₀)).gcd b
      let S := Nat.sqrt ((A.card * N) / (p * g ^ 2)) + 1
      b / ρ ≤ (b * L₂) / (256 * (p * g) * S) + 1) :
    ∃ x ≤ L₁, ∃ y ≤ L₂, ∃ w : ℕ,
      0 < p * w ^ 2 ∧ r + u + q₁ * x + q₂ * y = p * w ^ 2 := by
  let g := q₁.gcd q₂
  let a := q₁ / g
  let b := q₂ / g
  let c := p * g
  let H := A.card * N
  let S := Nat.sqrt (H / (p * g ^ 2)) + 1
  let X := L₁ / 8
  let L := (b * L₂) / (256 * c * S)
  let T := a * (X + X) + t.toNat
  let Z := Nat.sqrt (T / c) + 1
  have hg : 0 < g := Nat.gcd_pos_of_pos_left q₂ hq₁
  have hc : 0 < c := Nat.mul_pos hp hg
  have hS : 0 < S := by dsimp only [S]; omega
  have hga : g * a = q₁ := Nat.mul_div_cancel' (Nat.gcd_dvd_left q₁ q₂)
  have hgb : g * b = q₂ := Nat.mul_div_cancel' (Nat.gcd_dvd_right q₁ q₂)
  have hscale := configured_balanced_scale_threshold hp hpN hAN hlarge
  have hN₀ : 2 ≤ N₀ := by
    by_contra hnot
    have hcases : N₀ = 0 ∨ N₀ = 1 := by omega
    rcases hcases with rfl | rfl <;>
      norm_num [nvBalancedScaleThreshold, nvCubicScale] at hscale
  have hmasterCard := configured_balanced_master_card hlarge
  have hC := nvMasterConstant_pos
  have hA2 : 2 ≤ A.card := by
    have : 1 ≤ nvMasterConstant ^ 2 := pow_pos hC 2
    omega
  have hXpos := Nat.mul_pos (nvCubicScale_pos N₀) (nvInitialPolylog_pos N₀)
  have hL₁pos : 0 < L₁ := hXpos.trans_le hL₁
  have hL₂pos : 0 < L₂ := hXpos.trans_le hL₂
  have hproduct := configured_rank_two_side_product_lower_bound
    hA2 hW hscaled hDU hL₁pos hL₂pos
  have hgspan : g * L₁ * L₂ ≤ H :=
    (gcd_mul_side_product_le_span_of_injective hq₁ hq₂ hinj).trans hspan
  have hgW := rank_two_common_step_budget_upper hW hscaled hDU hL₁pos hL₂pos hgspan
  have hcommon := configured_rank_two_common_step_bound hp hpN hAN hA2 hgW
  have hproper : L₁ < b := normalized_second_step_gt_first_side hq₁ hq₂ hinj horient
  have hPQ : L₁ * L₂ ≤ b * L₂ := Nat.mul_le_mul_right _ hproper.le
  have hspan' : g * (b * L₂) ≤ H := by
    rw [← mul_assoc, hgb]
    exact (Nat.le_add_left _ _).trans hspan
  have hbig := configured_balanced_rectangle_is_large hp hg (by omega : 0 < A.card)
    hpN hscale hproduct hPQ hspan' hcommon hmasterCard
  have horient' : a * L₁ ≤ b * L₂ := by
    apply Nat.le_of_mul_le_mul_left (c := g) _ hg
    simpa only [← mul_assoc, hga, hgb] using horient
  obtain ⟨hLpos, hxside, hLbound, hcapacity⟩ :=
    nguyen_vu_balanced_rectangle_capacity hp hg horient' hspan' hbig
  change 0 < L at hLpos
  change X + X ≤ L₁ at hxside
  change L ≤ 2 * S at hLbound
  change a * X + 32 * c * S * (L + 1) ≤ b * L₂ at hcapacity
  have hambient : r + u + q₁ * L₁ + q₂ * L₂ ≤ H := by
    exact (Finset.mem_Icc.mp (subsetSum_subset_Icc_of_subset
      (U := A) (A := A) Finset.Subset.rfl hAN le_rfl
        (hfamily u hu L₁ le_rfl L₂ le_rfl))).2
  have hZbound : Z ≤ S :=
    canonical_rank_two_Z_le_ambient_sqrt hp hq₁ hq₂ hz₀ hbase hambient hxside
  have hd : 2 * p * z₀ ≤ 2 * c := by
    dsimp only [c]
    simpa only [mul_assoc] using Nat.mul_le_mul_left (2 * p) hz₀.le
  have hcap : c * (Z + L) ^ 2 + (2 * p * z₀) * (Z + L) + c ≤
      b * L₂ + a * X + t.toNat := by
    have hraw := quadratic_rectangle_capacity_of_increment_budget
      hc hS (by simp [T] : a * (X + X) ≤ T)
      (rfl : Z = Nat.sqrt (T / c) + 1) hd
      (hZbound.trans (by omega : S ≤ 2 * S)) hLbound hcapacity
    simpa only [T, Nat.add_sub_cancel_left] using hraw
  obtain ⟨Z', hZ', hleft, hright⟩ :=
    rankTwoBalancedEndpointGeometry_of_relative_capacity
      (X := X) (Hx := X) (L := L) hp hq₁ hq₂ hz₀ hbase hcap
  have hthreshold := configured_balanced_reduced_period_threshold
    (z₀ := z₀) hp hpN hN₀ (by omega : 0 < A.card) hq₁ hq₂ hL₂pos hproduct
    ((Nat.le_add_left _ _).trans hspan) hL₁
  exact nvReducedPeriodConstant_spec hp hq₁ hq₂ hbase hZ'
    hperiod hthreshold hxside
    (rank_two_quadratic_strip_of_endpoint_bounds hxside hleft hright)

end Erdos587
