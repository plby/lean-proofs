import ErdosProblems.Erdos783.PrimeHigh

open MeasureTheory Set Finset Filter
open scoped Topology

namespace Erdos783

noncomputable section

/-! The last scale separation needed to pass from the power-cutoff theorem
to arbitrary finite prime sets. -/

theorem eventually_powerCutoff_pow_mul_le
    {a c d : ℝ} (ha : 0 < a) (hc : 0 < c) (hd : 0 < d)
    (r : ℕ) (hgap : (r : ℝ) * a + c < d) :
    ∀ᶠ N : ℕ in atTop,
      powerCutoff a N ^ r * powerCutoff c N ≤ powerCutoff d N := by
  let m : ℝ := (((r : ℝ) * a + c) + d) / 2
  have hlm : (r : ℝ) * a + c < m := by
    dsimp only [m]
    linarith
  have hmd : m < d := by
    dsimp only [m]
    linarith
  have hleft : Tendsto
      (fun N : ℕ ↦
        (r : ℝ) *
            (Real.log (powerCutoff a N : ℝ) / Real.log (N : ℝ)) +
          Real.log (powerCutoff c N : ℝ) / Real.log (N : ℝ))
      atTop (nhds ((r : ℝ) * a + c) ) :=
    (tendsto_const_nhds.mul (tendsto_log_powerCutoff_div_log ha)).add
      (tendsto_log_powerCutoff_div_log hc)
  have hright := tendsto_log_powerCutoff_div_log hd
  have hleftEvent := hleft.eventually (Iio_mem_nhds hlm)
  have hrightEvent := hright.eventually (Ioi_mem_nhds hmd)
  have haTop := tendsto_powerCutoff_atTop ha
  have hcTop := tendsto_powerCutoff_atTop hc
  have hdTop := tendsto_powerCutoff_atTop hd
  filter_upwards [hleftEvent, hrightEvent, eventually_ge_atTop 2,
      haTop.eventually (Ici_mem_atTop 2),
      hcTop.eventually (Ici_mem_atTop 2),
      hdTop.eventually (Ici_mem_atTop 2)]
      with N hleftN hrightN hN ha2 hc2 hd2
  have hlogN : 0 < Real.log (N : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < N by omega))
  have hratio :
      (r : ℝ) * Real.log (powerCutoff a N : ℝ) +
          Real.log (powerCutoff c N : ℝ) <
        Real.log (powerCutoff d N : ℝ) := by
    have hmid :
        (r : ℝ) *
              (Real.log (powerCutoff a N : ℝ) / Real.log (N : ℝ)) +
            Real.log (powerCutoff c N : ℝ) / Real.log (N : ℝ) <
          Real.log (powerCutoff d N : ℝ) / Real.log (N : ℝ) :=
      hleftN.trans hrightN
    have hscaled := mul_lt_mul_of_pos_right hmid hlogN
    have hleftEq :
        ((r : ℝ) *
              (Real.log (powerCutoff a N : ℝ) / Real.log (N : ℝ)) +
            Real.log (powerCutoff c N : ℝ) / Real.log (N : ℝ)) *
            Real.log (N : ℝ) =
          (r : ℝ) * Real.log (powerCutoff a N : ℝ) +
            Real.log (powerCutoff c N : ℝ) := by
      field_simp [hlogN.ne']
      <;> ring
    have hrightEq :
        (Real.log (powerCutoff d N : ℝ) / Real.log (N : ℝ)) *
            Real.log (N : ℝ) =
          Real.log (powerCutoff d N : ℝ) := by
      field_simp [hlogN.ne']
    rw [hleftEq, hrightEq] at hscaled
    exact hscaled
  have hlogProd :
      Real.log ((powerCutoff a N ^ r * powerCutoff c N : ℕ) : ℝ) <
        Real.log (powerCutoff d N : ℝ) := by
    rw [Nat.cast_mul, Nat.cast_pow, Real.log_mul (by positivity) (by positivity),
      Real.log_pow]
    exact hratio
  have hlt :
      (powerCutoff a N : ℝ) ^ r * (powerCutoff c N : ℝ) <
        (powerCutoff d N : ℝ) :=
    (Real.log_lt_log_iff (by positivity) (by positivity)).mp (by
      simpa only [Nat.cast_mul, Nat.cast_pow] using hlogProd)
  exact_mod_cast hlt.le

lemma primeExponentCell_one_windowExponent
    {y K : ℕ} (hy : 2 ≤ y) (hK : 0 < K) :
    primeExponentCell y 1 (logarithmicEndpoint (K * (y + 1)) y) =
      splitPrimeWindow y K := by
  have hT : 0 < K * (y + 1) := Nat.mul_pos hK (by omega)
  unfold primeExponentCell splitPrimeWindow
  rw [show ⌊(y : ℝ) ^ (1 : ℝ)⌋₊ = y by simp,
    floor_rpow_logarithmicEndpoint hy hT]

lemma windowExponent_le
    {Y y K : ℕ} (hY : 2 ≤ Y) (hYy : Y ≤ y) (hK : 0 < K) :
    logarithmicEndpoint (K * (y + 1)) y ≤
      1 + (Real.log (K : ℝ) + Real.log 2) / Real.log (Y : ℝ) := by
  have hy : 2 ≤ y := hY.trans hYy
  have hlogY : 0 < Real.log (Y : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < Y by omega))
  have hlogy : 0 < Real.log (y : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < y by omega))
  have hlogYy : Real.log (Y : ℝ) ≤ Real.log (y : ℝ) :=
    Real.log_le_log (by positivity) (by exact_mod_cast hYy)
  have hK1 : 1 ≤ K := by omega
  have hlogK : 0 ≤ Real.log (K : ℝ) :=
    Real.log_nonneg (by exact_mod_cast hK1)
  have hlog2 : 0 ≤ Real.log (2 : ℝ) := (Real.log_pos one_lt_two).le
  have hy1 : y + 1 ≤ 2 * y := by omega
  have hlogSucc : Real.log ((y + 1 : ℕ) : ℝ) ≤
      Real.log (2 : ℝ) + Real.log (y : ℝ) := by
    calc
      Real.log ((y + 1 : ℕ) : ℝ) ≤
          Real.log ((2 * y : ℕ) : ℝ) :=
        Real.log_le_log (by positivity) (by exact_mod_cast hy1)
      _ = Real.log (2 : ℝ) + Real.log (y : ℝ) := by
        rw [Nat.cast_mul, Real.log_mul (by norm_num) (by positivity)]
        norm_num
  have hnum :
      Real.log ((K * (y + 1) : ℕ) : ℝ) ≤
        Real.log (y : ℝ) +
          (Real.log (K : ℝ) + Real.log 2) := by
    rw [Nat.cast_mul, Real.log_mul (by positivity) (by positivity)]
    linarith
  have hfirst : logarithmicEndpoint (K * (y + 1)) y ≤
      1 + (Real.log (K : ℝ) + Real.log 2) / Real.log (y : ℝ) := by
    unfold logarithmicEndpoint
    rw [show 1 + (Real.log (K : ℝ) + Real.log 2) /
          Real.log (y : ℝ) =
        (Real.log (y : ℝ) +
          (Real.log (K : ℝ) + Real.log 2)) /
            Real.log (y : ℝ) by
      field_simp [hlogy.ne'] <;> ring]
    exact div_le_div_of_nonneg_right hnum hlogy.le
  have hdiv := div_le_div_of_nonneg_left (add_nonneg hlogK hlog2)
    hlogY hlogYy
  linarith

theorem tendsto_powerWindowLogRatio
    {a c : ℝ} (ha : 0 < a) (hc : 0 < c) (r : ℕ) :
    Tendsto
      (fun N : ℕ ↦
        (Real.log ((powerCutoff a N) ^ r : ℕ) + Real.log 2) /
          Real.log (powerCutoff c N : ℕ))
      atTop (nhds (((r : ℝ) * a) / c)) := by
  have hlogN : Tendsto (fun N : ℕ ↦ Real.log (N : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hsmall : Tendsto
      (fun N : ℕ ↦ Real.log (2 : ℝ) / Real.log (N : ℝ))
      atTop (nhds 0) := tendsto_const_nhds.div_atTop hlogN
  have hnum : Tendsto
      (fun N : ℕ ↦
        (r : ℝ) *
            (Real.log (powerCutoff a N : ℝ) / Real.log (N : ℝ)) +
          Real.log (2 : ℝ) / Real.log (N : ℝ))
      atTop (nhds ((r : ℝ) * a)) := by
    simpa using
      (tendsto_const_nhds.mul (tendsto_log_powerCutoff_div_log ha)).add hsmall
  have hden := tendsto_log_powerCutoff_div_log hc
  have hquot := hnum.div hden hc.ne'
  apply hquot.congr'
  have haTop := tendsto_powerCutoff_atTop ha
  have hcTop := tendsto_powerCutoff_atTop hc
  filter_upwards [eventually_ge_atTop 2,
      haTop.eventually (Ici_mem_atTop 2),
      hcTop.eventually (Ici_mem_atTop 2)]
      with N hN ha2 hc2
  have hlogN0 : Real.log (N : ℝ) ≠ 0 :=
    (Real.log_pos (by exact_mod_cast (show 1 < N by omega))).ne'
  have hlogC0 : Real.log (powerCutoff c N : ℕ) ≠ 0 :=
    (Real.log_pos (by
      exact_mod_cast (show 1 < powerCutoff c N by omega))).ne'
  change
    (((r : ℝ) *
          (Real.log (powerCutoff a N : ℝ) / Real.log (N : ℝ)) +
        Real.log (2 : ℝ) / Real.log (N : ℝ)) /
      (Real.log (powerCutoff c N : ℝ) / Real.log (N : ℝ))) =
    (Real.log ((powerCutoff a N) ^ r : ℕ) + Real.log (2 : ℝ)) /
      Real.log (powerCutoff c N : ℕ)
  rw [Nat.cast_pow, Real.log_pow]
  field_simp [hlogN0, hlogC0]

theorem eventually_splitPrimeWindowMass_powerCutoff
    {a c delta : ℝ} (ha : 0 < a) (hc : 0 < c) (hdelta : 0 < delta)
    (r : ℕ) (hratio : ((r : ℝ) * a) / c < delta / 4) :
    ∀ᶠ N : ℕ in atTop, ∀ y : ℕ, powerCutoff c N ≤ y →
      reciprocalMass
        (splitPrimeWindow y ((powerCutoff a N) ^ r)) < delta := by
  have hratioHalf : ((r : ℝ) * a) / c < delta / 2 := by linarith
  have hratioEvent := (tendsto_powerWindowLogRatio ha hc r).eventually
    (Iio_mem_nhds hratioHalf)
  have hcloseBase := eventually_primeExponentCellMass_close
    (delta / 4) (by positivity)
  have hYTop := tendsto_powerCutoff_atTop hc
  have hATop := tendsto_powerCutoff_atTop ha
  have hcloseEvent : ∀ᶠ N : ℕ in atTop, ∀ y : ℕ,
      powerCutoff c N ≤ y → ∀ u v : ℝ, 1 ≤ u → u ≤ v →
        |primeExponentCellMass y u v - (Real.log v - Real.log u)| <
          delta / 4 := by
    rw [eventually_atTop] at hcloseBase ⊢
    obtain ⟨Y₀, hY₀⟩ := hcloseBase
    have hYEvent := hYTop.eventually (Ici_mem_atTop Y₀)
    rw [eventually_atTop] at hYEvent
    obtain ⟨N₀, hN₀⟩ := hYEvent
    exact ⟨N₀, fun N hN y hYy ↦ hY₀ y ((hN₀ N hN).trans hYy)⟩
  filter_upwards [hratioEvent, hcloseEvent,
      hYTop.eventually (Ici_mem_atTop 2),
      hATop.eventually (Ici_mem_atTop 1)]
      with N hratioN hcloseN hY2 hA1
  intro y hYy
  let Y := powerCutoff c N
  let K := powerCutoff a N ^ r
  let d := logarithmicEndpoint (K * (y + 1)) y
  have hy2 : 2 ≤ y := hY2.trans hYy
  have hK : 0 < K := by
    dsimp only [K]
    positivity
  have hT : y < K * (y + 1) := by
    have hK1 : 1 ≤ K := by omega
    nlinarith
  have hd1 : 1 < d := by
    dsimp only [d]
    exact logarithmicEndpoint_gt_one hy2 hT
  have hdUpper : d < 1 + delta / 2 := by
    have hwindow := windowExponent_le hY2 hYy hK
    dsimp only [Y, K] at hwindow
    dsimp only [d]
    exact hwindow.trans_lt (by linarith)
  have hlogd : Real.log d < delta / 2 := by
    have hlog := Real.log_lt_sub_one_of_pos (by linarith) (by linarith)
    linarith
  have hclose := hcloseN y hYy 1 d (by norm_num) hd1.le
  have hmassEq :
      reciprocalMass (splitPrimeWindow y K) =
        primeExponentCellMass y 1 d := by
    dsimp only [d]
    unfold reciprocalMass primeExponentCellMass
    rw [primeExponentCell_one_windowExponent hy2 hK]
  rw [hmassEq]
  rw [Real.log_one, sub_zero] at hclose
  linarith [lt_of_abs_lt hclose]

theorem eventually_splittingApproximation_powerCutoff
    {C delta a c d : ℝ}
    (hC : 0 ≤ C) (hdelta : 0 < delta)
    (ha : 0 < a) (hc : 0 < c) (hd : 0 < d)
    (r : ℕ)
    (hratio : ((r : ℝ) * a) / c < delta / 4)
    (hgap : (r : ℝ) * a + c < d) :
    ∀ᶠ N : ℕ in atTop, ∀ A₁ A₂ : Finset ℕ,
      Disjoint A₁ A₂ →
      (∀ q ∈ A₁ ∪ A₂, 0 < q) →
      reciprocalMass (A₁ ∪ A₂) ≤ C →
      (∀ q ∈ A₁, q ≤ powerCutoff a N) →
      (∀ q ∈ A₂, q.Prime) →
      (∀ q ∈ A₂, powerCutoff d N < q) →
      (∀ q ∈ A₂, q ≤ N) →
      |truncatedSieveApprox N (A₁ ∪ A₂) r -
          truncatedSieveApprox N A₁ r *
            truncatedSieveApprox N A₂ r| ≤
        factorialTail C r + delta * Real.exp C := by
  have hscale := eventually_powerCutoff_pow_mul_le ha hc hd r hgap
  have hwindow := eventually_splitPrimeWindowMass_powerCutoff
    ha hc hdelta r hratio
  have haTop := tendsto_powerCutoff_atTop ha
  filter_upwards [hscale, hwindow,
      haTop.eventually (Ici_mem_atTop 1)]
      with N hscaleN hwindowN ha1
  intro A₁ A₂ hdisj hpos hmass hsmall hprime hlarge hendpoint
  exact splittingApproximation hC hdelta.le (by omega) hdisj hpos hmass
    hsmall hprime hlarge hendpoint hscaleN
    (fun y hy ↦ (hwindowN y hy).le)

def powerGapExponent (Q k j : ℕ) : ℝ :=
  (Q : ℝ) ^ j / (Q : ℝ) ^ (k + 1)

lemma powerGapExponent_pos {Q k : ℕ} (hQ : 0 < Q) (j : ℕ) :
    0 < powerGapExponent Q k j := by
  unfold powerGapExponent
  positivity

lemma powerGapExponent_succ {Q k j : ℕ} :
    powerGapExponent Q k (j + 1) = Q * powerGapExponent Q k j := by
  unfold powerGapExponent
  rw [pow_succ]
  ring

lemma monotone_powerGapExponent {Q k : ℕ} (hQ : 1 ≤ Q) :
    Monotone (powerGapExponent Q k) := by
  intro i j hij
  unfold powerGapExponent
  apply div_le_div_of_nonneg_right _ (by positivity)
  exact pow_le_pow_right₀ (by exact_mod_cast hQ) hij

lemma powerGapExponent_last {Q k : ℕ} (hQ : 0 < Q) :
    powerGapExponent Q k k = (Q : ℝ)⁻¹ := by
  unfold powerGapExponent
  rw [pow_succ]
  field_simp [show (Q : ℝ) ≠ 0 by positivity]

lemma disjoint_scaleGap_of_lt_monotone
    {A : Finset ℕ} {z : ℕ → ℕ} (hz : Monotone z)
    {i j : ℕ} (hij : i < j) :
    Disjoint (scaleGap A z i) (scaleGap A z j) := by
  rw [Finset.disjoint_left]
  intro q hqi hqj
  have hi := (mem_scaleGap.mp hqi).2
  have hj := (mem_scaleGap.mp hqj).2
  have hzle : z (i + 1) ≤ z j := hz (by omega)
  omega

lemma exists_scaleGap_mass_le_monotone
    {C : ℝ} {A : Finset ℕ} (hmass : reciprocalMass A ≤ C)
    (z : ℕ → ℕ) (hz : Monotone z) {k : ℕ} (hk : 0 < k) :
    ∃ j < k, reciprocalMass (scaleGap A z j) ≤ C / k := by
  have hdisj : Set.PairwiseDisjoint (↑(Finset.range k)) (scaleGap A z) := by
    intro i hi j hj hij
    rcases lt_or_gt_of_ne hij with hlt | hgt
    · exact disjoint_scaleGap_of_lt_monotone hz hlt
    · exact (disjoint_scaleGap_of_lt_monotone hz hgt).symm
  have hsum := Finset.sum_biUnion
    (f := fun q : ℕ ↦ (q : ℝ)⁻¹) hdisj
  have hsub : (Finset.range k).biUnion (scaleGap A z) ⊆ A := by
    rw [Finset.biUnion_subset_iff_forall_subset]
    intro j hj
    exact scaleGap_subset A z j
  have hle :
      (∑ q ∈ (Finset.range k).biUnion (scaleGap A z), (q : ℝ)⁻¹) ≤
        reciprocalMass A := by
    unfold reciprocalMass
    exact Finset.sum_le_sum_of_subset_of_nonneg hsub
      (fun _q _hq _hnot ↦ by positivity)
  rw [hsum] at hle
  by_contra hnot
  push_neg at hnot
  have hrange : (Finset.range k).Nonempty := by
    simp [Nat.ne_of_gt hk]
  have hlt :
      (∑ _j ∈ Finset.range k, C / (k : ℝ)) <
        ∑ j ∈ Finset.range k, reciprocalMass (scaleGap A z j) := by
    apply Finset.sum_lt_sum_of_nonempty hrange
    intro j hj
    exact hnot j (Finset.mem_range.mp hj)
  have hconst : (∑ _j ∈ Finset.range k, C / (k : ℝ)) = C := by
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    field_simp [show (k : ℝ) ≠ 0 by exact_mod_cast Nat.ne_of_gt hk]
  rw [hconst] at hlt
  have hle' :
      (∑ j ∈ Finset.range k, reciprocalMass (scaleGap A z j)) ≤ C := by
    simpa only [reciprocalMass] using hle.trans hmass
  linarith

lemma powerCutoff_pow_le_self
    {a : ℝ} (ha : 0 ≤ a) (r : ℕ)
    (har : a * (r : ℝ) ≤ 1) {N : ℕ} (hN : 1 ≤ N) :
    powerCutoff a N ^ r ≤ N := by
  have hfloor : (powerCutoff a N : ℝ) ≤ (N : ℝ) ^ a :=
    Nat.floor_le (Real.rpow_nonneg (by positivity) a)
  have hpow : (powerCutoff a N : ℝ) ^ r ≤ ((N : ℝ) ^ a) ^ r :=
    pow_le_pow_left₀ (by positivity) hfloor r
  have hbase : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hexp : (N : ℝ) ^ (a * (r : ℝ)) ≤ (N : ℝ) := by
    simpa using Real.rpow_le_rpow_of_exponent_le hbase har
  have hcast : ((powerCutoff a N ^ r : ℕ) : ℝ) ≤ (N : ℝ) := by
    rw [Nat.cast_pow]
    calc
      (powerCutoff a N : ℝ) ^ r ≤ ((N : ℝ) ^ a) ^ r := hpow
      _ = (N : ℝ) ^ (a * (r : ℝ)) := by
        rw [Real.rpow_mul_natCast (by positivity)]
      _ ≤ (N : ℝ) := hexp
  exact_mod_cast hcast

def powerGapMiddleExponent (Q k r j : ℕ) : ℝ :=
  (powerGapExponent Q k (j + 1) -
      (r : ℝ) * powerGapExponent Q k j) / 2

lemma powerGapMiddleExponent_pos
    {Q k r j : ℕ} (hQ : 0 < Q) (hrQ : (r : ℝ) < Q) :
    0 < powerGapMiddleExponent Q k r j := by
  rw [powerGapMiddleExponent, powerGapExponent_succ]
  have he := powerGapExponent_pos (k := k) hQ j
  have hQR : (Q : ℝ) - r > 0 := by linarith
  nlinarith

lemma powerGapMiddle_ratio
    {Q k r j : ℕ} (hQ : 0 < Q) (hrQ : (r : ℝ) < Q) :
    ((r : ℝ) * powerGapExponent Q k j) /
        powerGapMiddleExponent Q k r j =
      (2 * (r : ℝ)) / ((Q : ℝ) - r) := by
  rw [powerGapMiddleExponent, powerGapExponent_succ]
  have he := powerGapExponent_pos (k := k) hQ j
  have hden : (Q : ℝ) - r ≠ 0 := by positivity
  field_simp [he.ne', hden]

lemma powerGapMiddle_gap
    {Q k r j : ℕ} (hQ : 0 < Q) (hrQ : (r : ℝ) < Q) :
    (r : ℝ) * powerGapExponent Q k j +
        powerGapMiddleExponent Q k r j <
      powerGapExponent Q k (j + 1) := by
  rw [powerGapMiddleExponent, powerGapExponent_succ]
  have he := powerGapExponent_pos (k := k) hQ j
  have hQR : (0 : ℝ) < Q - r := by linarith
  nlinarith

lemma exists_powerGapBase (r : ℕ) {delta : ℝ} (hdelta : 0 < delta) :
    ∃ Q : ℕ, 1 < Q ∧ (r : ℝ) < Q ∧
      (2 * (r : ℝ)) / ((Q : ℝ) - r) < delta / 4 := by
  obtain ⟨Q, hQ⟩ := exists_nat_gt
    ((r : ℝ) + 8 * (r : ℝ) / delta + 2)
  have hfrac : 0 ≤ 8 * (r : ℝ) / delta := by positivity
  have hQ1R : (1 : ℝ) < Q := by linarith
  have hrQ : (r : ℝ) < Q := by linarith
  have hden : 0 < (Q : ℝ) - r := by linarith
  have hdiv : 8 * (r : ℝ) / delta < (Q : ℝ) - r := by
    linarith
  have hmul : 8 * (r : ℝ) < ((Q : ℝ) - r) * delta :=
    (div_lt_iff₀ hdelta).mp (by simpa [mul_div_assoc] using hdiv)
  refine ⟨Q, by exact_mod_cast hQ1R, hrQ, ?_⟩
  rw [div_lt_iff₀ hden]
  nlinarith

theorem primeOnlyLowerBound_dickmanRho :
    PrimeOnlyLowerBound dickmanRho := by
  intro C hC epsilon hepsilon
  let eta : ℝ := min (epsilon / 100) (1 / 100)
  have heta : 0 < eta := by
    dsimp only [eta]
    exact lt_min (div_pos hepsilon (by norm_num)) (by norm_num)
  have hetaEps : eta ≤ epsilon / 100 := min_le_left _ _
  have hetaOne : eta ≤ 1 / 100 := min_le_right _ _
  let delta : ℝ := eta / Real.exp C
  have hdelta : 0 < delta := div_pos heta (Real.exp_pos C)
  have hdeltaExp : delta * Real.exp C = eta := by
    dsimp only [delta]
    field_simp [(Real.exp_pos C).ne']
  obtain ⟨r, hr⟩ := exists_factorialTail_lt heta
  have hlayer : C ^ (r + 1) / (r + 1).factorial < eta :=
    (factorialLayer_le_factorialTail hC.le r).trans_lt hr
  obtain ⟨k, hklarge⟩ := exists_nat_gt (C / eta)
  have hkR : 0 < (k : ℝ) := (div_pos hC heta).trans hklarge
  have hk : 0 < k := by exact_mod_cast hkR
  have hCdivk : C / (k : ℝ) < eta := by
    rw [div_lt_iff₀ hkR]
    have := (div_lt_iff₀ heta).mp hklarge
    nlinarith
  obtain ⟨Q, hQ1, hrQ, hQratio⟩ := exists_powerGapBase r hdelta
  have hQ : 0 < Q := by omega
  have hQle : 1 ≤ Q := by omega
  let e : ℕ → ℝ := powerGapExponent Q k
  let middle : ℕ → ℝ := powerGapMiddleExponent Q k r
  have hePos (j : ℕ) : 0 < e j := powerGapExponent_pos hQ j
  have heMono : Monotone e := monotone_powerGapExponent hQle
  have hmiddlePos (j : ℕ) : 0 < middle j :=
    powerGapMiddleExponent_pos hQ hrQ
  have hmiddleRatio (j : ℕ) :
      ((r : ℝ) * e j) / middle j < delta / 4 := by
    dsimp only [e, middle]
    rw [powerGapMiddle_ratio hQ hrQ]
    exact hQratio
  have hmiddleGap (j : ℕ) :
      (r : ℝ) * e j + middle j < e (j + 1) := by
    dsimp only [e, middle]
    exact powerGapMiddle_gap hQ hrQ
  have hk1 : 1 ≤ k := by omega
  have heLast : e k = (Q : ℝ)⁻¹ := powerGapExponent_last hQ
  have heOnePos : 0 < e 1 := hePos 1
  have heOneLt : e 1 < 1 := by
    have hle : e 1 ≤ e k := heMono hk1
    rw [heLast] at hle
    exact hle.trans_lt (inv_lt_one_of_one_lt₀ (by exact_mod_cast hQ1))
  let SplitGood : ℕ → ℕ → Prop := fun N j ↦
    ∀ A₁ A₂ : Finset ℕ,
      Disjoint A₁ A₂ →
      (∀ q ∈ A₁ ∪ A₂, 0 < q) →
      reciprocalMass (A₁ ∪ A₂) ≤ C →
      (∀ q ∈ A₁, q ≤ powerCutoff (e j) N) →
      (∀ q ∈ A₂, q.Prime) →
      (∀ q ∈ A₂, powerCutoff (e (j + 1)) N < q) →
      (∀ q ∈ A₂, q ≤ N) →
      |truncatedSieveApprox N (A₁ ∪ A₂) r -
          truncatedSieveApprox N A₁ r * truncatedSieveApprox N A₂ r| ≤
        factorialTail C r + eta
  have hsplitEach : ∀ j ∈ Finset.range k, ∀ᶠ N : ℕ in atTop,
      SplitGood N j := by
    intro j hj
    have hraw := eventually_splittingApproximation_powerCutoff
      hC.le hdelta (hePos j) (hmiddlePos j) (hePos (j + 1)) r
      (hmiddleRatio j) (hmiddleGap j)
    filter_upwards [hraw] with N hN
    dsimp only [SplitGood]
    intro A₁ A₂ hdisj hpos hmass hsmall hprime hlarge hendpoint
    have := hN A₁ A₂ hdisj hpos hmass hsmall hprime hlarge hendpoint
    rwa [hdeltaExp] at this
  have hsplitAll : ∀ᶠ N : ℕ in atTop, ∀ j ∈ Finset.range k,
      SplitGood N j :=
    (Finset.eventually_all (Finset.range k)).2 hsplitEach
  have hhigh := eventually_powerCutoff_prime_lower hC.le heOnePos heOneLt
    heta
  have hbonf := eventually_sieveDensity_truncated_abs_lt
    hC.le heta 1 r
  have hz0 := (tendsto_powerCutoff_atTop (hePos 0)).eventually
    (Ici_mem_atTop 1)
  filter_upwards [hsplitAll, hhigh, hbonf, hz0, eventually_ge_atTop 1]
      with N hsplitN hhighN hbonfN hz0N hN
  intro P hP hPprime
  let z : ℕ → ℕ := fun j ↦ powerCutoff (e j) N
  have hzMono : Monotone z := by
    intro i j hij
    dsimp only [z]
    exact powerCutoff_mono_exponent (heMono hij) hN
  obtain ⟨j, hjk, hgap⟩ :=
    exists_scaleGap_mass_le_monotone hP.mass_le z hzMono hk
  have hgapEta : reciprocalMass (scaleGap P z j) < eta :=
    hgap.trans_lt hCdivk
  let A₁ := lowScalePart P (z j)
  let A₂ := highScalePart P (z (j + 1))
  let B := A₁ ∪ A₂
  have hzjj : z j ≤ z (j + 1) := hzMono (Nat.le_succ j)
  have hdisj : Disjoint A₁ A₂ := by
    rw [Finset.disjoint_left]
    intro q hq1 hq2
    have hq1' := (mem_lowScalePart.mp hq1).2
    have hq2' := (mem_highScalePart.mp hq2).2
    omega
  have hA₁sub : A₁ ⊆ P := lowScalePart_subset P (z j)
  have hA₂sub : A₂ ⊆ P := highScalePart_subset P (z (j + 1))
  have hBsub : B ⊆ P :=
    union_lowScalePart_highScalePart_subset P (z j) (z (j + 1))
  have hA₁ : Admissible C N A₁ := hP.mono hA₁sub
  have hA₂ : Admissible C N A₂ := hP.mono hA₂sub
  have hB : Admissible C N B := hP.mono hBsub
  have hA₁small : ∀ q ∈ A₁, q ≤ z j := by
    intro q hq
    exact (mem_lowScalePart.mp hq).2
  have hA₂large : ∀ q ∈ A₂, z (j + 1) < q := by
    intro q hq
    exact (mem_highScalePart.mp hq).2
  have hA₂prime : ∀ q ∈ A₂, q.Prime := by
    intro q hq
    exact hPprime q (hA₂sub hq)
  have hA₂endpoint : ∀ q ∈ A₂, q ≤ N := by
    intro q hq
    exact hP.le_endpoint (hA₂sub hq)
  have hposB : ∀ q ∈ B, 0 < q := by
    intro q hq
    have := hP.two_le (hBsub hq)
    omega
  have hsplit :
      |truncatedSieveApprox N B r -
          truncatedSieveApprox N A₁ r * truncatedSieveApprox N A₂ r| ≤
        factorialTail C r + eta := by
    have hs := hsplitN j (Finset.mem_range.mpr hjk)
    dsimp only [SplitGood] at hs
    dsimp only [B, A₁, A₂]
    apply hs
    · exact hdisj
    · exact hposB
    · exact hB.mass_le
    · simpa only [z] using hA₁small
    · exact hA₂prime
    · simpa only [z] using hA₂large
    · exact hA₂endpoint
  have hejLast : e j ≤ e k := heMono hjk.le
  have har : e j * (r : ℝ) ≤ 1 := by
    have hmul := mul_le_mul_of_nonneg_right hejLast (by positivity : (0 : ℝ) ≤ r)
    rw [heLast] at hmul
    have hrdiv : (r : ℝ) * (Q : ℝ)⁻¹ < 1 := by
      rw [← div_eq_mul_inv]
      exact (div_lt_one (by positivity)).2 hrQ
    nlinarith
  have hzjPos : 0 < z j := by
    have hz0le : z 0 ≤ z j := hzMono (Nat.zero_le j)
    exact (show 0 < z 0 by
      exact zero_lt_one.trans_le (by simpa only [z] using hz0N)).trans_le hz0le
  have hpowj : (z j) ^ r ≤ N := by
    dsimp only [z]
    exact powerCutoff_pow_le_self (hePos j).le r har hN
  have hbrun :
      |truncatedSieveApprox N A₁ r - periodicDensity A₁| ≤
        factorialTail C r := by
    exact pureBrunApproximation hC.le hA₁.mass_le hzjPos
      hA₁small hpowj
  have hBcomp : ∀ q ∈ B, ¬q.Prime → q < 1 := by
    intro q hq hnot
    exact (hnot (hPprime q (hBsub hq))).elim
  have hA₂comp : ∀ q ∈ A₂, ¬q.Prime → q < 1 := by
    intro q hq hnot
    exact (hnot (hA₂prime q hq)).elim
  have hbonfB :
      |sieveDensity N B - truncatedSieveApprox N B r| <
        C ^ (r + 1) / (r + 1).factorial + eta :=
    hbonfN B hB hBcomp
  have hbonfA₂ :
      |sieveDensity N A₂ - truncatedSieveApprox N A₂ r| <
        C ^ (r + 1) / (r + 1).factorial + eta :=
    hbonfN A₂ hA₂ hA₂comp
  have heOneLe : e 1 ≤ e (j + 1) := heMono (by omega)
  have hcutoffLe : powerCutoff (e 1) N ≤ z (j + 1) := by
    dsimp only [z]
    exact powerCutoff_mono_exponent heOneLe hN
  have hpA₂ :
      dickmanRho (Real.exp (reciprocalMass A₂)) - eta <
        sieveDensity N A₂ := by
    exact hhighN A₂ hA₂ hA₂prime
      (fun q hq ↦ hcutoffLe.trans_lt (hA₂large q hq))
  have hNpos : 0 < N := by omega
  have hsdiff : P \ B = scaleGap P z j := by
    dsimp only [B, A₁, A₂]
    exact sdiff_union_low_high_eq_scaleGap P z j
  have hlipschitz :
      sieveDensity N B - reciprocalMass (scaleGap P z j) ≤
        sieveDensity N P := by
    rw [← hsdiff]
    exact sieveDensity_sub_mass_sdiff_le hNpos B P
  have hA₁two : ∀ q ∈ A₁, 2 ≤ q := by
    intro q hq
    exact hP.two_le (hA₁sub hq)
  have hp1nonneg : 0 ≤ periodicDensity A₁ := periodicDensity_nonneg hA₁two
  have hp1le : periodicDensity A₁ ≤ 1 := periodicDensity_le_one hA₁two
  have hd2nonneg : 0 ≤ sieveDensity N A₂ := sieveDensity_nonneg N A₂
  have hd2le : sieveDensity N A₂ ≤ 1 := sieveDensity_le_one hNpos A₂
  have ht2diff :
      |truncatedSieveApprox N A₂ r - sieveDensity N A₂| < 2 * eta := by
    rw [abs_sub_comm]
    linarith
  have ht2abs : |truncatedSieveApprox N A₂ r| < 2 := by
    calc
      |truncatedSieveApprox N A₂ r| ≤
          |truncatedSieveApprox N A₂ r - sieveDensity N A₂| +
            |sieveDensity N A₂| := by
        simpa using abs_add_le
          (truncatedSieveApprox N A₂ r - sieveDensity N A₂)
          (sieveDensity N A₂)
      _ < 2 * eta + 1 := by
        rw [abs_of_nonneg hd2nonneg]
        linarith
      _ ≤ 2 := by linarith
  have hprodApprox :
      |truncatedSieveApprox N A₁ r * truncatedSieveApprox N A₂ r -
          periodicDensity A₁ * sieveDensity N A₂| < 4 * eta := by
    rw [show truncatedSieveApprox N A₁ r * truncatedSieveApprox N A₂ r -
          periodicDensity A₁ * sieveDensity N A₂ =
        (truncatedSieveApprox N A₁ r - periodicDensity A₁) *
            truncatedSieveApprox N A₂ r +
          periodicDensity A₁ *
            (truncatedSieveApprox N A₂ r - sieveDensity N A₂) by ring]
    calc
      |(truncatedSieveApprox N A₁ r - periodicDensity A₁) *
            truncatedSieveApprox N A₂ r +
          periodicDensity A₁ *
            (truncatedSieveApprox N A₂ r - sieveDensity N A₂)| ≤
          |truncatedSieveApprox N A₁ r - periodicDensity A₁| *
              |truncatedSieveApprox N A₂ r| +
            |periodicDensity A₁| *
              |truncatedSieveApprox N A₂ r - sieveDensity N A₂| := by
        simpa only [abs_mul] using abs_add_le
          ((truncatedSieveApprox N A₁ r - periodicDensity A₁) *
            truncatedSieveApprox N A₂ r)
          (periodicDensity A₁ *
            (truncatedSieveApprox N A₂ r - sieveDensity N A₂))
      _ ≤ eta * |truncatedSieveApprox N A₂ r| +
            |periodicDensity A₁| *
              |truncatedSieveApprox N A₂ r - sieveDensity N A₂| := by
        exact add_le_add
          (mul_le_mul_of_nonneg_right (hbrun.trans hr.le) (abs_nonneg _)) le_rfl
      _ < eta * 2 +
            |periodicDensity A₁| *
              |truncatedSieveApprox N A₂ r - sieveDensity N A₂| := by
        exact add_lt_add_of_lt_of_le
          (mul_lt_mul_of_pos_left ht2abs heta) le_rfl
      _ ≤ eta * 2 + 1 *
              |truncatedSieveApprox N A₂ r - sieveDensity N A₂| := by
        rw [abs_of_nonneg hp1nonneg]
        exact add_le_add le_rfl
          (mul_le_mul_of_nonneg_right hp1le (abs_nonneg _))
      _ < eta * 2 + 1 * (2 * eta) := by
        exact add_lt_add_of_le_of_lt le_rfl
          (mul_lt_mul_of_pos_left ht2diff zero_lt_one)
      _ = 4 * eta := by ring
  have hBproduct :
      periodicDensity A₁ * sieveDensity N A₂ - 8 * eta <
        sieveDensity N B := by
    have hsplit' :
        |truncatedSieveApprox N B r -
            truncatedSieveApprox N A₁ r * truncatedSieveApprox N A₂ r| <
          2 * eta := hsplit.trans_lt (by linarith)
    have hbonfB' :
        |sieveDensity N B - truncatedSieveApprox N B r| < 2 * eta := by
      linarith
    rw [abs_lt] at hsplit' hbonfB' hprodApprox
    rcases hsplit' with ⟨hsplitLower, hsplitUpper⟩
    rcases hbonfB' with ⟨hbonfLower, hbonfUpper⟩
    rcases hprodApprox with ⟨hprodLower, hprodUpper⟩
    linarith
  have hprimeProduct :
      periodicDensity A₁ *
          dickmanRho (Real.exp (reciprocalMass A₂)) - eta <
        periodicDensity A₁ * sieveDensity N A₂ := by
    by_cases hp1zero : periodicDensity A₁ = 0
    · rw [hp1zero]
      simp only [zero_mul]
      linarith
    · have hp1pos : 0 < periodicDensity A₁ :=
        lt_of_le_of_ne hp1nonneg (Ne.symm hp1zero)
      have hm := mul_lt_mul_of_pos_left hpA₂ hp1pos
      have hetaScale : periodicDensity A₁ * eta ≤ eta := by
        nlinarith
      calc
        periodicDensity A₁ * dickmanRho (Real.exp (reciprocalMass A₂)) - eta ≤
            periodicDensity A₁ * dickmanRho (Real.exp (reciprocalMass A₂)) -
              periodicDensity A₁ * eta := by linarith
        _ = periodicDensity A₁ *
              (dickmanRho (Real.exp (reciprocalMass A₂)) - eta) := by ring
        _ < periodicDensity A₁ * sieveDensity N A₂ := hm
  have hbridge :
      dickmanRho (Real.exp (reciprocalMass A₁ + reciprocalMass A₂)) ≤
        periodicDensity A₁ *
          dickmanRho (Real.exp (reciprocalMass A₂)) :=
    periodicDensity_mul_dickmanRho_ge dickmanProductInequality hA₁two
      (reciprocalMass_nonneg A₂)
  have hmassB : reciprocalMass B = reciprocalMass A₁ + reciprocalMass A₂ := by
    dsimp only [B, reciprocalMass]
    exact Finset.sum_union hdisj
  have hBmassP : reciprocalMass B ≤ reciprocalMass P :=
    reciprocalMass_mono hBsub (fun q hq ↦ by
      have := hP.two_le (hBsub hq)
      omega)
  have hmassBridge :
      dickmanRho (Real.exp (reciprocalMass P)) ≤
        dickmanRho (Real.exp (reciprocalMass A₁ + reciprocalMass A₂)) := by
    rw [← hmassB]
    exact antitoneOn_dickmanRho_Ici_zero
      (Real.exp_pos _).le (Real.exp_pos _).le
      (Real.exp_le_exp.mpr hBmassP)
  calc
    dickmanRho (Real.exp (reciprocalMass P)) - epsilon <
        dickmanRho (Real.exp (reciprocalMass P)) - 10 * eta := by
      have : 10 * eta < epsilon := by linarith
      linarith
    _ ≤ periodicDensity A₁ *
          dickmanRho (Real.exp (reciprocalMass A₂)) - 10 * eta := by
      linarith
    _ < periodicDensity A₁ * sieveDensity N A₂ - 9 * eta := by
      linarith
    _ < sieveDensity N B - eta := by
      linarith
    _ < sieveDensity N B - reciprocalMass (scaleGap P z j) := by
      linarith
    _ ≤ sieveDensity N P := hlipschitz

end

end Erdos783
