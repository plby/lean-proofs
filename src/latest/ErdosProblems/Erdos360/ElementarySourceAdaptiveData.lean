/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos360.ElementarySourceAdaptiveIntegration

/-!
# Packaging the elementary source-adaptive phase machine

The saturation threshold is the ceiling of the requested residue target
divided by the current closure modulus.  Saturated phases therefore reach
the target, while unsaturated phases gain a fixed amount `D` by the
elementary normalized-fibre selector.
-/

namespace Erdos360

attribute [local instance] Classical.propDecidable

/-- Ceiling saturation at a target cardinality. -/
def sourceAdaptiveCeilSaturation (target q : ℕ) : ℕ :=
  target ⌈/⌉ q

lemma sourceAdaptiveCeilSaturation_bound
    {target q : ℕ} (hq : 0 < q) :
    target ≤ q * sourceAdaptiveCeilSaturation target q := by
  exact le_smul_ceilDiv hq

/-- With a factor-four ambient margin, every ceiling saturation which is at
least two occupies at most half of the corresponding quotient group. -/
lemma two_mul_ceilDiv_le_div_of_four_mul_le
    {target q t : ℕ} (hq : 0 < q) (hqt : q ∣ t)
    (hceil : 2 ≤ target ⌈/⌉ q) (hroom : 4 * target ≤ t) :
    2 * (target ⌈/⌉ q) ≤ t / q := by
  have hqtarget : q < target := by
    by_contra hnot
    have hceilOne : target ⌈/⌉ q ≤ 1 :=
      (ceilDiv_le_iff_le_mul hq).2 (by simpa using Nat.le_of_not_gt hnot)
    omega
  have hmul : q * (target ⌈/⌉ q) ≤ target + q - 1 := by
    rw [Nat.ceilDiv_eq_add_pred_div]
    simpa [mul_comm] using Nat.div_mul_le_self (target + q - 1) q
  apply (Nat.le_div_iff_mul_le hq).2
  calc
    2 * (target ⌈/⌉ q) * q =
        2 * (q * (target ⌈/⌉ q)) := by ring
    _ ≤ 2 * (target + q - 1) := Nat.mul_le_mul_left 2 hmul
    _ ≤ 4 * target := by omega
    _ ≤ t := hroom

/-- A reusable constructor for `CFPSourceAdaptiveSelectorData` based only
on the elementary generated-subgroup selector.  All remaining hypotheses
are finite cardinal inequalities exposed for the eventual parameter
ledger. -/
theorem exists_CFPSourceAdaptiveSelectorData_elementary
    {t : ℕ} [NeZero t] (ht : 0 < t)
    (R₀ : Finset (ZMod t)) (hdiverse : PhaseDiverse ht R₀)
    (residueTarget phaseQ D L k : ℕ)
    (hD : 1 < D) (hL : 0 < L)
    (hhalf : 2 * k ≤ R₀.card)
    (hQroom : ∀ i < k,
      4 * phaseQ ≤
        (sourceAdaptiveRemainder ht R₀ {0} (by simp) hdiverse phaseQ i).card)
    (hLroom : ∀ i < k,
      4 * L ≤
        (sourceAdaptiveRemainder ht R₀ {0} (by simp) hdiverse phaseQ i).card)
    (hQlarge : 8 * (D - 1) ≤ phaseQ)
    (hsatHalf : ∀ i < k,
      IsSourceAdaptiveUnsaturatedStep ht R₀ {0} (by simp) hdiverse
        phaseQ (sourceAdaptiveCeilSaturation residueTarget) i →
      let R := sourceAdaptiveRemainder ht R₀ {0} (by simp) hdiverse phaseQ i
      let H := AddSubgroup.closure (R : Set (ZMod t))
      2 * sourceAdaptiveCeilSaturation residueTarget
          (sourceAdaptiveModulus ht R₀ {0} (by simp) hdiverse phaseQ i) ≤
        Nat.card H)
    (hgrowthBudget :
      (Nat.log 2 t + 1) *
          (2 * (Nat.log 2 t + 1) + (phaseQ / L + 1)) ≤ k)
    (hunsaturated : residueTarget ≤ D *
      (k - (Nat.log 2 t + 1) *
        (2 * (Nat.log 2 t + 1) + (phaseQ / L + 1)))) :
    Nonempty (CFPSourceAdaptiveSelectorData ht R₀ hdiverse residueTarget) := by
  let sat := sourceAdaptiveCeilSaturation residueTarget
  have hRlarge : ∀ i < k,
      8 * (D - 1) <
        (sourceAdaptiveRemainder ht R₀ {0} (by simp) hdiverse phaseQ i).card := by
    intro i hi
    have hroom := hQroom i hi
    have hQpos : 0 < phaseQ := by
      have : 0 < 8 * (D - 1) := Nat.mul_pos (by omega) (by omega)
      omega
    omega
  have hinc := sourceAdaptive_unsaturated_increment_elementary
    ht R₀ {0} (by simp) hdiverse phaseQ D sat k hD hQlarge hhalf
    (by simpa [sat] using hsatHalf) hRlarge
  refine ⟨
    { phaseQ := phaseQ
      largeGain := L
      unsaturatedGain := D
      phaseCount := k
      saturatedTarget := residueTarget
      unsaturatedTarget := residueTarget
      saturation := sat
      largeGain_pos := hL
      half := hhalf
      phaseQ_room := hQroom
      largeGain_room := hLroom
      unsaturatedIncrement := hinc
      saturated_bound := ?_
      growth_budget := by simpa using hgrowthBudget
      unsaturated_bound := by simpa using hunsaturated
      target_bound := by simp }⟩
  intro i hi
  exact sourceAdaptiveCeilSaturation_bound
    (closureModulus_pos ht
      (sourceAdaptiveRemainder ht R₀ {0} (by simp) hdiverse phaseQ i))

/-- Ambient-margin specialization of the elementary constructor.  The
factor-four target room automatically supplies the half-density condition
in every genuinely unsaturated phase. -/
theorem exists_CFPSourceAdaptiveSelectorData_elementary_of_target_room
    {t : ℕ} [NeZero t] (ht : 0 < t)
    (R₀ : Finset (ZMod t)) (hdiverse : PhaseDiverse ht R₀)
    (residueTarget phaseQ D L k : ℕ)
    (hD : 1 < D) (hL : 0 < L)
    (hhalf : 2 * k ≤ R₀.card)
    (hQroom : ∀ i < k,
      4 * phaseQ ≤
        (sourceAdaptiveRemainder ht R₀ {0} (by simp) hdiverse phaseQ i).card)
    (hLroom : ∀ i < k,
      4 * L ≤
        (sourceAdaptiveRemainder ht R₀ {0} (by simp) hdiverse phaseQ i).card)
    (hQlarge : 8 * (D - 1) ≤ phaseQ)
    (htargetRoom : 4 * residueTarget ≤ t)
    (hgrowthBudget :
      (Nat.log 2 t + 1) *
          (2 * (Nat.log 2 t + 1) + (phaseQ / L + 1)) ≤ k)
    (hunsaturated : residueTarget ≤ D *
      (k - (Nat.log 2 t + 1) *
        (2 * (Nat.log 2 t + 1) + (phaseQ / L + 1)))) :
    Nonempty (CFPSourceAdaptiveSelectorData ht R₀ hdiverse residueTarget) := by
  apply exists_CFPSourceAdaptiveSelectorData_elementary
    ht R₀ hdiverse residueTarget phaseQ D L k hD hL hhalf
    hQroom hLroom hQlarge
  · intro i hi hu
    let R := sourceAdaptiveRemainder ht R₀ {0} (by simp) hdiverse phaseQ i
    let H := AddSubgroup.closure (R : Set (ZMod t))
    let q := sourceAdaptiveModulus ht R₀ {0} (by simp) hdiverse phaseQ i
    have hbounds := sourceAdaptiveMinFiber_bounds_of_unsaturated
      ht R₀ {0} (by simp) hdiverse phaseQ
        (sourceAdaptiveCeilSaturation residueTarget)
        (i := i) (by omega) hu
    have hceil : 2 ≤ sourceAdaptiveCeilSaturation residueTarget q := by
      have hne : 0 <
          (sourceAdaptiveFiber R₀ {0} R
            (sourceAdaptiveMinFiberCenter R₀ {0} R)).card :=
        Finset.card_pos.mpr (by simpa [R] using hbounds.1)
      have hlt :
          (sourceAdaptiveFiber R₀ {0} R
            (sourceAdaptiveMinFiberCenter R₀ {0} R)).card <
              sourceAdaptiveCeilSaturation residueTarget q := by
        simpa [R, q, sourceAdaptiveModulus] using hbounds.2.2
      omega
    have hqpos : 0 < q := by
      exact closureModulus_pos ht R
    have hqdiv : q ∣ t := by
      exact closureModulus_dvd ht R
    have hquot := two_mul_ceilDiv_le_div_of_four_mul_le
      hqpos hqdiv hceil htargetRoom
    have hHcard : Nat.card H = t / q := by
      rw [Nat.card_eq_fintype_card]
      rw [show Fintype.card H = (H : Set (ZMod t)).ncard by
        exact Set.fintypeCard_eq_ncard (H : Set (ZMod t))]
      exact ncard_closure_eq_div_modulus ht R
    dsimp only [H]
    rw [hHcard]
    simpa [sourceAdaptiveCeilSaturation] using hquot
  · exact hgrowthBudget
  · exact hunsaturated

end Erdos360

#print axioms Erdos360.exists_CFPSourceAdaptiveSelectorData_elementary
#print axioms Erdos360.exists_CFPSourceAdaptiveSelectorData_elementary_of_target_room
