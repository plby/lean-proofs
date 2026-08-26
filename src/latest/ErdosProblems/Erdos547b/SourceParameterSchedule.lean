/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import Mathlib.Tactic

/-!
# Source-faithful rational parameters for Zhao's Section 6

These are the parameters (PAR) in `tex/547.tex`. The degree-error scale,
its actual fourth root, the regularity density cutoff, and the high-degree
reservoir fraction are separate quantities. In particular the cutoff is
smaller than the reservoir fraction; whole-pair pruning supplies the
large-endpoint property instead of a contradictory cutoff requirement.
-/

namespace Erdos547b.ZhaoSourceParameterSchedule

def rhoOne (α : ℚ) : ℚ := α / 1000
def rho (α : ℚ) : ℚ := rhoOne α ^ 3
def eta (α : ℚ) : ℚ := rho α ^ 12 / 1000000
def fourthRoot (α : ℚ) : ℚ := eta α ^ 4 / 1000000
def degreeError (α : ℚ) : ℚ := fourthRoot α ^ 4
def densityCutoff (α : ℚ) : ℚ := degreeError α / 100
def gamma (α : ℚ) : ℚ := degreeError α ^ 12 / 1000000
def epsilon (α : ℚ) : ℚ := gamma α ^ 12 / 1000000

/-- The rational square root of the regularity error, used in the
almost-all-target incidence estimate. -/
def rootTypicality (α : ℚ) : ℚ := gamma α ^ 6 / 1000

/-- A positive power of a number in `[0,1]` is no larger than that number. -/
theorem pow_succ_le_self {x : ℚ} (hx : 0 ≤ x) (hx1 : x ≤ 1) (k : ℕ) :
    x ^ (k + 1) ≤ x := by
  have hp : x ^ k ≤ 1 := by
    simpa only [one_pow] using pow_le_pow_left₀ hx hx1 k
  rw [pow_succ]
  simpa only [one_mul] using mul_le_mul_of_nonneg_right hp hx

theorem parameter_pos {α : ℚ} (hα : 0 < α) :
    0 < rhoOne α ∧ 0 < rho α ∧ 0 < eta α ∧ 0 < fourthRoot α ∧
      0 < degreeError α ∧ 0 < densityCutoff α ∧ 0 < gamma α ∧ 0 < epsilon α := by
  have hr1 : 0 < rhoOne α := by unfold rhoOne; positivity
  have hr : 0 < rho α := by unfold rho; positivity
  have he : 0 < eta α := by unfold eta; positivity
  have ht : 0 < fourthRoot α := by unfold fourthRoot; positivity
  have hd : 0 < degreeError α := by unfold degreeError; positivity
  have hcut : 0 < densityCutoff α := by unfold densityCutoff; positivity
  have hg : 0 < gamma α := by unfold gamma; positivity
  have hep : 0 < epsilon α := by unfold epsilon; positivity
  exact ⟨hr1, hr, he, ht, hd, hcut, hg, hep⟩

/-- The full chain is bounded above by one, with explicit multiplicative
separation where the proof needs it. -/
theorem parameter_upper_bounds {α : ℚ} (hα : 0 < α) (hα1 : α ≤ 1 / 4) :
    rhoOne α ≤ 1 ∧ rho α ≤ rhoOne α ∧ eta α ≤ rho α / 1000000 ∧
      fourthRoot α ≤ eta α ^ 3 / 1000000 ∧ degreeError α ≤ fourthRoot α ∧
      gamma α ≤ degreeError α / 1000000 ∧ epsilon α ≤ gamma α / 1000000 := by
  obtain ⟨hr10, hr0, he0, ht0, hd0, _hcut0, hg0, _hep0⟩ := parameter_pos hα
  have hr11 : rhoOne α ≤ 1 := by unfold rhoOne; linarith only [hα1]
  have hrr1 : rho α ≤ rhoOne α := pow_succ_le_self hr10.le hr11 2
  have hr1 : rho α ≤ 1 := hrr1.trans hr11
  have her : eta α ≤ rho α / 1000000 := by
    exact div_le_div_of_nonneg_right (pow_succ_le_self hr0.le hr1 11) (by norm_num)
  have he1 : eta α ≤ 1 := by linarith only [her, hr1]
  have hte3 : fourthRoot α ≤ eta α ^ 3 / 1000000 := by
    have hp : eta α ^ 4 ≤ eta α ^ 3 := by
      calc
        eta α ^ 4 = eta α ^ 3 * eta α := by ring
        _ ≤ eta α ^ 3 * 1 := mul_le_mul_of_nonneg_left he1 (by positivity)
        _ = eta α ^ 3 := mul_one _
    exact div_le_div_of_nonneg_right hp (by norm_num)
  have ht1 : fourthRoot α ≤ 1 := by
    have hp : eta α ^ 3 ≤ 1 := by
      simpa only [one_pow] using pow_le_pow_left₀ he0.le he1 3
    linarith only [hte3, hp]
  have hdt : degreeError α ≤ fourthRoot α := pow_succ_le_self ht0.le ht1 3
  have hd1 : degreeError α ≤ 1 := hdt.trans ht1
  have hgd : gamma α ≤ degreeError α / 1000000 := by
    exact div_le_div_of_nonneg_right (pow_succ_le_self hd0.le hd1 11) (by norm_num)
  have hg1 : gamma α ≤ 1 := by linarith only [hgd, hd1]
  have hepg : epsilon α ≤ gamma α / 1000000 := by
    exact div_le_div_of_nonneg_right (pow_succ_le_self hg0.le hg1 11) (by norm_num)
  exact ⟨hr11, hrr1, her, hte3, hdt, hgd, hepg⟩

/-- The source's fourth-root scale is much smaller than the corrected
`eta^3` exceptional saving. -/
theorem exceptional_saving_margin {α : ℚ} (hα : 0 < α) (hα1 : α ≤ 1 / 4) :
    15 * fourthRoot α + 10 * fourthRoot α ^ 2 + 6 * gamma α < eta α ^ 3 / 1000 := by
  obtain ⟨hr10, hr0, he0, ht0, hd0, _hcut0, hg0, _hep0⟩ := parameter_pos hα
  obtain ⟨hr11, hrr1, her, hte3, hdt, hgd, _hepg⟩ := parameter_upper_bounds hα hα1
  have hr1 : rho α ≤ 1 := hrr1.trans hr11
  have he1 : eta α ≤ 1 := by linarith only [her, hr1]
  have he3 : eta α ^ 3 ≤ 1 := by
    simpa only [one_pow] using pow_le_pow_left₀ he0.le he1 3
  have ht1 : fourthRoot α ≤ 1 := by linarith only [hte3, he3]
  have ht2 : fourthRoot α ^ 2 ≤ fourthRoot α := pow_succ_le_self ht0.le ht1 1
  have hgt : gamma α ≤ fourthRoot α := by linarith only [hgd, hdt, ht0]
  have he3pos : 0 < eta α ^ 3 := by positivity
  linarith only [ht2, hgt, hte3, he3pos]

/-- The name `fourthRoot` agrees with the actual square-root degree scale. -/
theorem sqrt_degreeError (α : ℚ) :
    Real.sqrt (degreeError α : ℝ) = (fourthRoot α : ℝ) ^ 2 := by
  simp only [degreeError, Rat.cast_pow]
  rw [show (fourthRoot α : ℝ) ^ 4 = ((fourthRoot α : ℝ) ^ 2) ^ 2 by ring,
    Real.sqrt_sq_eq_abs, abs_of_nonneg (sq_nonneg _)]

/-- The high-degree reservoir has enough volume to pay for the final
near-large degree defect in Claim 6.17. This is the separation missing from
the old cutoff-based constructor. -/
theorem high_reservoir_margin {α : ℚ} (hα : 0 < α) (hα1 : α ≤ 1 / 4) :
    5 * degreeError α < rho α * fourthRoot α ^ 2 := by
  obtain ⟨_hr10, hr0, he0, ht0, _hd0, _hcut0, _hg0, _hep0⟩ := parameter_pos hα
  obtain ⟨hr11, hrr1, her, hte3, _hdt, _hgd, _hepg⟩ := parameter_upper_bounds hα hα1
  have hr1 : rho α ≤ 1 := hrr1.trans hr11
  have he1 : eta α ≤ 1 := by linarith only [her, hr1]
  have he3 : eta α ^ 3 ≤ eta α := pow_succ_le_self he0.le he1 2
  have ht1 : fourthRoot α ≤ 1 := by linarith only [hte3, he3, he1]
  have ht2 : fourthRoot α ^ 2 ≤ fourthRoot α := pow_succ_le_self ht0.le ht1 1
  have hsmall : 5 * fourthRoot α ^ 2 < rho α := by
    linarith only [ht2, hte3, he3, her, hr0]
  calc
    5 * degreeError α = (5 * fourthRoot α ^ 2) * fourthRoot α ^ 2 := by
      unfold degreeError
      ring
    _ < rho α * fourthRoot α ^ 2 :=
      mul_lt_mul_of_pos_right hsmall (by positivity)

/-- The ordinary regularity error is small enough for the greedy small-tree
embedding at the actual (smaller) density cutoff. -/
theorem regularity_product_margin {α : ℚ} (hα : 0 < α) (hα1 : α ≤ 1 / 4) :
    10 * epsilon α < densityCutoff α * gamma α := by
  obtain ⟨_hr10, _hr0, he0, _ht0, hd0, _hcut0, hg0, _hep0⟩ := parameter_pos hα
  obtain ⟨hr11, hrr1, her, hte3, hdt, hgd, _hepg⟩ := parameter_upper_bounds hα hα1
  have hr1 : rho α ≤ 1 := hrr1.trans hr11
  have he1 : eta α ≤ 1 := by linarith only [her, hr1]
  have he3 : eta α ^ 3 ≤ 1 := by
    simpa only [one_pow] using pow_le_pow_left₀ he0.le he1 3
  have ht1 : fourthRoot α ≤ 1 := by linarith only [hte3, he3]
  have hd1 : degreeError α ≤ 1 := hdt.trans ht1
  have hg1 : gamma α ≤ 1 := by linarith only [hgd, hd1]
  have hg10 : gamma α ^ 10 ≤ 1 := by
    simpa only [one_pow] using pow_le_pow_left₀ hg0.le hg1 10
  have hg12 : gamma α ^ 12 ≤ gamma α ^ 2 := by
    calc
      gamma α ^ 12 = gamma α ^ 2 * gamma α ^ 10 := by ring
      _ ≤ gamma α ^ 2 * 1 := mul_le_mul_of_nonneg_left hg10 (sq_nonneg _)
      _ = gamma α ^ 2 := mul_one _
  have hprod := mul_le_mul_of_nonneg_right hgd hg0.le
  have hpositive := mul_pos hd0 hg0
  change 10 * (gamma α ^ 12 / 1000000) < (degreeError α / 100) * gamma α
  nlinarith only [hg12, hprod, hpositive]

/-- Concrete comparisons used in the large-cluster counting gates. The
reservoir fraction is the actual square root of the degree-error scale. -/
theorem reservoir_cleanup_bounds {α : ℚ} (hα : 0 < α) (hα1 : α ≤ 1 / 4) :
    0 < fourthRoot α ^ 2 ∧ fourthRoot α ^ 2 ≤ 1 / 16 ∧
      11 * fourthRoot α ^ 2 ≤ α ∧
      degreeError α ≤ fourthRoot α ^ 2 / 100 ∧
      epsilon α ≤ degreeError α / 1000000 ∧ degreeError α ≤ 1 := by
  obtain ⟨hr10, hr0, he0, ht0, hd0, _hcut0, hg0, _hep0⟩ := parameter_pos hα
  obtain ⟨hr11, hrr1, her, hte3, hdt, hgd, hepg⟩ := parameter_upper_bounds hα hα1
  have hr1 : rho α ≤ 1 := hrr1.trans hr11
  have he1 : eta α ≤ 1 := by linarith only [her, hr1]
  have he3 : eta α ^ 3 ≤ eta α := pow_succ_le_self he0.le he1 2
  have ht1 : fourthRoot α ≤ 1 := by linarith only [hte3, he3, he1]
  have ht2 : fourthRoot α ^ 2 ≤ fourthRoot α := pow_succ_le_self ht0.le ht1 1
  have htα : fourthRoot α ≤ α / 1000000000000000 := by
    dsimp only [rhoOne] at hrr1
    linarith only [hte3, he3, her, hrr1]
  have ht2small : fourthRoot α ^ 2 ≤ 1 / 100 := by linarith only [ht2, htα, hα1]
  have hdsmall : degreeError α ≤ fourthRoot α ^ 2 / 100 := by
    have h := mul_le_mul_of_nonneg_right ht2small (sq_nonneg (fourthRoot α))
    unfold degreeError
    nlinarith only [h]
  refine ⟨by positivity, ?_, ?_, hdsmall, ?_, hdt.trans ht1⟩
  · linarith only [ht2small]
  · linarith only [ht2, htα, hα]
  · linarith only [hepg, hgd, hd0]

theorem rootTypicality_sq (α : ℚ) : rootTypicality α ^ 2 = epsilon α := by
  unfold rootTypicality epsilon
  ring

/-- The almost-all-target loss uses less than half of the final reserved
square-root degree-error budget. -/
theorem rootTypicality_margin {α : ℚ} (hα : 0 < α) (hα1 : α ≤ 1 / 4) :
    0 < rootTypicality α ∧ 4 * rootTypicality α < fourthRoot α ^ 2 / 2 := by
  obtain ⟨_, _, _, _, hd, _, hg, _⟩ := parameter_pos hα
  obtain ⟨_, _, _, _, _, hgd, _⟩ := parameter_upper_bounds hα hα1
  obtain ⟨hsigma, _, _, hdSmall, _, hd1⟩ := reservoir_cleanup_bounds hα hα1
  have hg1 : gamma α ≤ 1 := by linarith only [hgd, hd1]
  have hg6 : gamma α ^ 6 ≤ gamma α := pow_succ_le_self hg.le hg1 5
  constructor
  · unfold rootTypicality
    positivity
  · unfold rootTypicality
    linarith only [hg6, hgd, hdSmall, hsigma]

theorem sqrt_epsilon {α : ℚ} (hα : 0 < α) :
    Real.sqrt (epsilon α : ℝ) = (rootTypicality α : ℝ) := by
  have hsq : (rootTypicality α : ℝ) ^ 2 = (epsilon α : ℝ) := by
    exact_mod_cast rootTypicality_sq α
  have hnonneg : (0 : ℝ) ≤ rootTypicality α := by
    unfold rootTypicality
    push_cast
    positivity
  rw [← hsq, Real.sqrt_sq_eq_abs, abs_of_nonneg hnonneg]

end Erdos547b.ZhaoSourceParameterSchedule

#print axioms Erdos547b.ZhaoSourceParameterSchedule.parameter_pos
#print axioms Erdos547b.ZhaoSourceParameterSchedule.parameter_upper_bounds
#print axioms Erdos547b.ZhaoSourceParameterSchedule.exceptional_saving_margin
#print axioms Erdos547b.ZhaoSourceParameterSchedule.sqrt_degreeError
#print axioms Erdos547b.ZhaoSourceParameterSchedule.high_reservoir_margin
#print axioms Erdos547b.ZhaoSourceParameterSchedule.regularity_product_margin
#print axioms Erdos547b.ZhaoSourceParameterSchedule.reservoir_cleanup_bounds
#print axioms Erdos547b.ZhaoSourceParameterSchedule.rootTypicality_sq
#print axioms Erdos547b.ZhaoSourceParameterSchedule.rootTypicality_margin
#print axioms Erdos547b.ZhaoSourceParameterSchedule.sqrt_epsilon
