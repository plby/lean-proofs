import ErdosProblems.Erdos1002.NearResonantPoleDerivatives

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# A smooth finite-cell representative of the primitive pole

For `p ≥ 2` the literal nearest-resonance pole agrees on `(0,1)` with a
finite sum of ordinary smooth affine cells.  No coprimality indicator is
differentiated: it selects whole disjoint cells, while every omitted
nearest-cell indicator is redundant because the profile is already zero
outside that cell.
-/

open Filter MeasureTheory Set
open scoped BigOperators

namespace Erdos1002

noncomputable section

/-- The indicator-free finite reduced-cell representative. -/
def smoothNearPrimitivePoleSum
    (a ε : ℝ) (p : ℕ) (alpha : ℝ) : ℂ :=
  ∑ q ∈ reducedResidues p, nearPoleCell a ε p q alpha

/-- Outside the half-open nearest cell the smooth affine pole is already
zero.  Thus removing a whole non-primitive cell creates no jump. -/
theorem nearPoleCell_eq_zero_of_not_mem_nearest
    (a ε : ℝ) (p q : ℕ) (alpha : ℝ)
    (hp : 0 < p) (ha : 0 < a) (hε : 0 < ε)
    (haε : a ≤ ε / 4) (hεhalf : ε ≤ 1 / 2)
    (hnot : ¬ ((p : ℝ) * alpha - (q : ℝ) ∈
      Ioc (-(1 : ℝ) / 2) ((1 : ℝ) / 2))) :
    nearPoleCell a ε p q alpha = 0 := by
  let z : ℝ := (p : ℝ) * alpha - (q : ℝ)
  have hz : z ≤ -(1 : ℝ) / 2 ∨ (1 : ℝ) / 2 < z := by
    by_cases hleft : z ≤ -(1 : ℝ) / 2
    · exact Or.inl hleft
    · right
      have hleft' : -(1 : ℝ) / 2 < z := lt_of_not_ge hleft
      exact lt_of_not_ge fun hright ↦ hnot ⟨hleft', hright⟩
  have hzabs : (1 : ℝ) / 2 ≤ |z| := by
    rcases hz with hz | hz
    · have hzneg : z < 0 := by linarith
      rw [abs_of_neg hzneg]
      linarith
    · have hzpos : 0 < z := by linarith
      rw [abs_of_pos hzpos]
      exact hz.le
  have hpR : (1 : ℝ) ≤ p := by exact_mod_cast hp
  have hscaled : ε ≤ |(p : ℝ) * z| := by
    rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ p)]
    nlinarith
  unfold nearPoleCell
  change nearW a ε ((p : ℝ) * z) = 0
  exact nearW_eq_zero_of_epsilon_le_abs a ε ((p : ℝ) * z)
    ha hε haε hscaled

/-- On the open unit interval the literal pole is exactly the
indicator-free smooth finite-cell sum. -/
theorem nearPrimitivePole_eq_smoothNearPrimitivePoleSum
    (a ε : ℝ) (p : ℕ) (hp : 2 ≤ p)
    (ha : 0 < a) (hε : 0 < ε) (haε : a ≤ ε / 4)
    (hεhalf : ε ≤ 1 / 2) {alpha : ℝ}
    (halpha : alpha ∈ Ioo (0 : ℝ) 1) :
    nearPrimitivePole a ε p alpha =
      smoothNearPrimitivePoleSum a ε p alpha := by
  rw [nearPrimitivePole_eq_nearestNearPoleCellExpansion hp halpha]
  unfold nearestNearPoleCellExpansion smoothNearPrimitivePoleSum
  apply Finset.sum_congr rfl
  intro q hq
  by_cases hcell : (p : ℝ) * alpha - (q : ℝ) ∈
      Ioc (-(1 : ℝ) / 2) ((1 : ℝ) / 2)
  · rw [if_pos hcell]
  · rw [if_neg hcell,
      nearPoleCell_eq_zero_of_not_mem_nearest
        a ε p q alpha (by omega) ha hε haε hεhalf hcell]

theorem nearPoleCell_contDiff
    (a ε : ℝ) (p q : ℕ) (ha : 0 < a) (haε : a ≤ ε / 4) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (nearPoleCell a ε p q) := by
  unfold nearPoleCell
  exact (nearW_contDiff a ε ha haε).comp
    (contDiff_const.mul ((contDiff_const.mul contDiff_id).sub contDiff_const))

/-- The representative is globally `C∞`, including every cutoff boundary. -/
theorem smoothNearPrimitivePoleSum_contDiff
    (a ε : ℝ) (p : ℕ) (ha : 0 < a) (haε : a ≤ ε / 4) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (smoothNearPrimitivePoleSum a ε p) := by
  unfold smoothNearPrimitivePoleSum
  apply ContDiff.sum
  intro q hq
  exact nearPoleCell_contDiff a ε p q ha haε

private theorem iteratedDeriv_finset_sum
    {ι : Type*} [DecidableEq ι] (s : Finset ι)
    (f : ι → ℝ → ℂ) (j : ℕ)
    (hf : ∀ i ∈ s, ContDiff ℝ j (f i)) (x : ℝ) :
    iteratedDeriv j (fun y ↦ ∑ i ∈ s, f i y) x =
      ∑ i ∈ s, iteratedDeriv j (f i) x := by
  induction s using Finset.induction_on with
  | empty => simp [iteratedDeriv_const]
  | @insert i s hi ih =>
      have hfi : ContDiff ℝ j (f i) := hf i (Finset.mem_insert_self i s)
      have hfs : ∀ k ∈ s, ContDiff ℝ j (f k) := by
        intro k hk
        exact hf k (Finset.mem_insert_of_mem hk)
      have hsum : ContDiff ℝ j (fun y ↦ ∑ k ∈ s, f k y) := by
        apply ContDiff.sum
        exact hfs
      have hfun : (fun y ↦ ∑ k ∈ insert i s, f k y) =
          (fun y ↦ f i y + ∑ k ∈ s, f k y) := by
        funext y
        rw [Finset.sum_insert hi]
      rw [hfun,
        iteratedDeriv_fun_add hfi.contDiffAt hsum.contDiffAt,
        ih hfs, Finset.sum_insert hi]

theorem iteratedDeriv_smoothNearPrimitivePoleSum
    (a ε : ℝ) (p j : ℕ) (ha : 0 < a) (haε : a ≤ ε / 4)
    (alpha : ℝ) :
    iteratedDeriv j (smoothNearPrimitivePoleSum a ε p) alpha =
      ∑ q ∈ reducedResidues p,
        iteratedDeriv j (nearPoleCell a ε p q) alpha := by
  unfold smoothNearPrimitivePoleSum
  apply iteratedDeriv_finset_sum
  intro q hq
  exact (nearPoleCell_contDiff a ε p q ha haε).of_le (by
    exact_mod_cast (show (j : ℕ∞) ≤ ⊤ from le_top))

theorem iteratedDeriv_nearPoleCell_mem_scaled_cutoff
    (a ε : ℝ) (p q j : ℕ) (hp : 0 < p)
    (ha : 0 < a) (hε : 0 < ε) (haε : a ≤ ε / 4)
    (alpha : ℝ)
    (hne : iteratedDeriv j (nearPoleCell a ε p q) alpha ≠ 0) :
    (p : ℝ) * ((p : ℝ) * alpha - (q : ℝ)) ∈ Icc (-ε) ε := by
  have hformula := iteratedDeriv_nearPoleCell
    a ε p q j hp ha haε alpha
  have hW : iteratedDeriv j (nearW a ε)
      ((p : ℝ) * ((p : ℝ) * alpha - (q : ℝ))) ≠ 0 := by
    intro hzero
    apply hne
    rw [hformula, hzero, smul_zero]
  exact support_iteratedDeriv_nearW_subset_Icc
    a ε ha hε haε j hW

/-- Derivative cells attached to two different numerators cannot both be
active at the same point. -/
theorem iteratedDeriv_nearPoleCell_pairwise_zero
    (a ε : ℝ) (p q r j : ℕ) (hp : 0 < p) (hqr : q ≠ r)
    (ha : 0 < a) (hε : 0 < ε) (haε : a ≤ ε / 4)
    (hεhalf : ε < 1 / 2) (alpha : ℝ) :
    iteratedDeriv j (nearPoleCell a ε p q) alpha = 0 ∨
      iteratedDeriv j (nearPoleCell a ε p r) alpha = 0 := by
  by_contra hnot
  rw [not_or] at hnot
  have hqcut := iteratedDeriv_nearPoleCell_mem_scaled_cutoff
    a ε p q j hp ha hε haε alpha hnot.1
  have hrcut := iteratedDeriv_nearPoleCell_mem_scaled_cutoff
    a ε p r j hp ha hε haε alpha hnot.2
  have hpone : (1 : ℝ) ≤ p := by exact_mod_cast hp
  rcases lt_or_gt_of_ne hqr with hqrlt | hrqlt
  · have hsep : (q : ℝ) + 1 ≤ r := by exact_mod_cast hqrlt
    nlinarith [hqcut.1, hqcut.2, hrcut.1, hrcut.2]
  · have hsep : (r : ℝ) + 1 ≤ q := by exact_mod_cast hrqlt
    nlinarith [hqcut.1, hqcut.2, hrcut.1, hrcut.2]

private theorem norm_sq_finset_sum_eq_sum_norm_sq
    {ι : Type*} [DecidableEq ι] (s : Finset ι) (f : ι → ℂ)
    (hdisj : ∀ i ∈ s, ∀ k ∈ s, i ≠ k → f i = 0 ∨ f k = 0) :
    ‖∑ i ∈ s, f i‖ ^ 2 = ∑ i ∈ s, ‖f i‖ ^ 2 := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
      have hdisjS : ∀ k ∈ s, ∀ l ∈ s, k ≠ l → f k = 0 ∨ f l = 0 := by
        intro k hk l hl hkl
        exact hdisj k (Finset.mem_insert_of_mem hk)
          l (Finset.mem_insert_of_mem hl) hkl
      by_cases hfi : f i = 0
      · simp [Finset.sum_insert hi, hfi, ih hdisjS]
      · have hzero : ∀ k ∈ s, f k = 0 := by
          intro k hk
          exact (hdisj i (Finset.mem_insert_self i s)
            k (Finset.mem_insert_of_mem hk) (by
              intro hik
              exact hi (hik ▸ hk))).resolve_left hfi
        have hsumzero : ∑ k ∈ s, f k = 0 :=
          Finset.sum_eq_zero fun k hk ↦ hzero k hk
        have hnormzero : ∑ k ∈ s, ‖f k‖ ^ 2 = 0 := by
          apply Finset.sum_eq_zero
          intro k hk
          rw [hzero k hk, norm_zero,
            zero_pow (by omega : (2 : ℕ) ≠ 0)]
        rw [Finset.sum_insert hi, hsumzero]
        calc
          ‖f i + 0‖ ^ 2 = ‖f i‖ ^ 2 := by simp
          _ = ‖f i‖ ^ 2 + ∑ k ∈ s, ‖f k‖ ^ 2 := by
            rw [hnormzero, add_zero]
          _ = ∑ k ∈ insert i s, ‖f k‖ ^ 2 := by
            rw [Finset.sum_insert hi]

/-- Pointwise Pythagoras identity for all derivative cells. -/
theorem norm_sq_iteratedDeriv_smoothNearPrimitivePoleSum_eq
    (a ε : ℝ) (p j : ℕ) (hp : 0 < p)
    (ha : 0 < a) (hε : 0 < ε) (haε : a ≤ ε / 4)
    (hεhalf : ε < 1 / 2) (alpha : ℝ) :
    ‖iteratedDeriv j (smoothNearPrimitivePoleSum a ε p) alpha‖ ^ 2 =
      ∑ q ∈ reducedResidues p,
        ‖iteratedDeriv j (nearPoleCell a ε p q) alpha‖ ^ 2 := by
  rw [iteratedDeriv_smoothNearPrimitivePoleSum a ε p j ha haε alpha]
  apply norm_sq_finset_sum_eq_sum_norm_sq
  intro q hq r hr hqr
  exact iteratedDeriv_nearPoleCell_pairwise_zero
    a ε p q r j hp hqr ha hε haε hεhalf alpha

theorem support_norm_iteratedDeriv_nearPoleCell_sq_subset
    (a ε : ℝ) (p q j : ℕ) (hp : 0 < p)
    (ha : 0 < a) (hε : 0 < ε) (haε : a ≤ ε / 4)
    (hεhalf : ε < 1 / 2) :
    Function.support (fun alpha : ℝ ↦
      ‖iteratedDeriv j (nearPoleCell a ε p q) alpha‖ ^ 2) ⊆
      Ioc (nearestCellLeft p q) (nearestCellRight p q) := by
  intro alpha halpha
  have hderiv : iteratedDeriv j (nearPoleCell a ε p q) alpha ≠ 0 := by
    intro hzero
    apply halpha
    change ‖iteratedDeriv j (nearPoleCell a ε p q) alpha‖ ^ 2 = 0
    simp [hzero]
  have hcut := iteratedDeriv_nearPoleCell_mem_scaled_cutoff
    a ε p q j hp ha hε haε alpha hderiv
  have hpR : 0 < (p : ℝ) := by exact_mod_cast hp
  have hpone : (1 : ℝ) ≤ p := by exact_mod_cast hp
  have hcell : (p : ℝ) * alpha - (q : ℝ) ∈
      Ioc (-(1 : ℝ) / 2) ((1 : ℝ) / 2) := by
    constructor <;> nlinarith [hcut.1, hcut.2]
  exact (mem_nearestCell_iff (q := q) hp alpha).1 hcell

theorem integrable_norm_iteratedDeriv_nearPoleCell_sq
    (a ε : ℝ) (p q j : ℕ) (hp : 0 < p)
    (ha : 0 < a) (hε : 0 < ε) (haε : a ≤ ε / 4)
    (hεhalf : ε < 1 / 2) :
    Integrable (fun alpha : ℝ ↦
      ‖iteratedDeriv j (nearPoleCell a ε p q) alpha‖ ^ 2) := by
  have hcontDeriv : Continuous
      (iteratedDeriv j (nearPoleCell a ε p q)) := by
    rw [iteratedDeriv_eq_iterate]
    exact (nearPoleCell_contDiff a ε p q ha haε).iterate_deriv j |>.continuous
  have hsupportIcc : Function.support (fun alpha : ℝ ↦
      ‖iteratedDeriv j (nearPoleCell a ε p q) alpha‖ ^ 2) ⊆
      Icc (nearestCellLeft p q) (nearestCellRight p q) :=
    (support_norm_iteratedDeriv_nearPoleCell_sq_subset
      a ε p q j hp ha hε haε hεhalf).trans Ioc_subset_Icc_self
  exact (hcontDeriv.norm.pow 2).integrable_of_hasCompactSupport
    (HasCompactSupport.of_support_subset_isCompact isCompact_Icc hsupportIcc)

theorem integral_unit_norm_iteratedDeriv_nearPoleCell_sq_eq
    (a ε : ℝ) (p q j : ℕ) (hp : 2 ≤ p)
    (hq : q ∈ reducedResidues p)
    (ha : 0 < a) (hε : 0 < ε) (haε : a ≤ ε / 4)
    (hεhalf : ε < 1 / 2) :
    (∫ alpha in (0 : ℝ)..1,
      ‖iteratedDeriv j (nearPoleCell a ε p q) alpha‖ ^ 2) =
      nearPoleCellDerivNormSqIntegral a ε p q j := by
  let f : ℝ → ℝ := fun alpha ↦
    ‖iteratedDeriv j (nearPoleCell a ε p q) alpha‖ ^ 2
  have hsupportCell : Function.support f ⊆
      Ioc (nearestCellLeft p q) (nearestCellRight p q) :=
    support_norm_iteratedDeriv_nearPoleCell_sq_subset
      a ε p q j (by omega) ha hε haε hεhalf
  have hsupportUnit : Function.support f ⊆ Ioc (0 : ℝ) 1 :=
    hsupportCell.trans (nearestCell_interval_subset_unit hp hq)
  calc
    (∫ alpha in (0 : ℝ)..1,
        ‖iteratedDeriv j (nearPoleCell a ε p q) alpha‖ ^ 2) =
        ∫ alpha : ℝ, f alpha :=
      intervalIntegral.integral_eq_integral_of_support_subset hsupportUnit
    _ = ∫ alpha in nearestCellLeft p q..nearestCellRight p q,
        f alpha := by
      symm
      exact intervalIntegral.integral_eq_integral_of_support_subset hsupportCell
    _ = nearPoleCellDerivNormSqIntegral a ε p q j := rfl

/-- Exact derivative mass of the complete smooth reduced-cell
representative.  This is the rigorous form of
`‖b_p^(j)‖₂² = φ(p) p^(4j-2) ‖W^(j)‖₂²`. -/
theorem integral_unit_norm_iteratedDeriv_smoothNearPrimitivePoleSum_sq_eq
    (a ε : ℝ) (p j : ℕ) (hp : 2 ≤ p)
    (ha : 0 < a) (hε : 0 < ε) (haε : a ≤ ε / 4)
    (hεhalf : ε < 1 / 2) :
    (∫ alpha in (0 : ℝ)..1,
      ‖iteratedDeriv j (smoothNearPrimitivePoleSum a ε p) alpha‖ ^ 2) =
      (Nat.totient p : ℝ) * (1 / (p : ℝ) ^ 2) *
        (((p : ℝ) ^ 2) ^ j) ^ 2 * nearWDerivNormSqMass a ε j := by
  have heq : ∀ᵐ alpha : ℝ ∂volume,
      ‖iteratedDeriv j (smoothNearPrimitivePoleSum a ε p) alpha‖ ^ 2 =
        ∑ q ∈ reducedResidues p,
          ‖iteratedDeriv j (nearPoleCell a ε p q) alpha‖ ^ 2 :=
    Eventually.of_forall fun alpha ↦
      norm_sq_iteratedDeriv_smoothNearPrimitivePoleSum_eq
        a ε p j (by omega) ha hε haε hεhalf alpha
  have heqInterval : ∀ᵐ alpha : ℝ ∂volume,
      alpha ∈ uIoc (0 : ℝ) 1 →
        ‖iteratedDeriv j (smoothNearPrimitivePoleSum a ε p) alpha‖ ^ 2 =
          ∑ q ∈ reducedResidues p,
            ‖iteratedDeriv j (nearPoleCell a ε p q) alpha‖ ^ 2 := by
    filter_upwards [heq] with alpha halpha
    intro _hmem
    exact halpha
  rw [intervalIntegral.integral_congr_ae heqInterval,
    intervalIntegral.integral_finset_sum]
  · calc
      (∑ q ∈ reducedResidues p,
          ∫ alpha in (0 : ℝ)..1,
            ‖iteratedDeriv j (nearPoleCell a ε p q) alpha‖ ^ 2) =
          ∑ q ∈ reducedResidues p,
            nearPoleCellDerivNormSqIntegral a ε p q j := by
        apply Finset.sum_congr rfl
        intro q hq
        exact integral_unit_norm_iteratedDeriv_nearPoleCell_sq_eq
          a ε p q j hp hq ha hε haε hεhalf
      _ = ∑ _q ∈ reducedResidues p,
          (1 / (p : ℝ) ^ 2) * (((p : ℝ) ^ 2) ^ j) ^ 2 *
            nearWDerivNormSqMass a ε j := by
        apply Finset.sum_congr rfl
        intro q hq
        exact nearPoleCellDerivNormSqIntegral_eq
          a ε p q j (by omega) ha hε haε hεhalf
      _ = (Nat.totient p : ℝ) * (1 / (p : ℝ) ^ 2) *
          (((p : ℝ) ^ 2) ^ j) ^ 2 * nearWDerivNormSqMass a ε j := by
        rw [Finset.sum_const, nsmul_eq_mul, card_reducedResidues]
        ring
  · intro q hq
    exact (integrable_norm_iteratedDeriv_nearPoleCell_sq
      a ε p q j (by omega) ha hε haε hεhalf).intervalIntegrable

end

end Erdos1002
