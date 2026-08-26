import ErdosProblems.Erdos520.ConcreteThinBlock

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open Finset MeasureTheory Set
open scoped BigOperators

namespace Erdos
namespace Problem520

/-!
# Comparison of Caich's localized main term with the block energy

In the smoothing argument the main term on a block `(a,b]` is integrated
only over `x / b < z ≤ x / a`, and its smoothness cutoff is `x / z`.
Throughout that interval the cutoff lies between `a` and `b`.  The concrete
block energy from `Equation16` takes the maximum over *every* cutoff in that
range and integrates over the whole positive half-line.  This file records
the resulting deterministic domination, including the floor and endpoint
bookkeeping.
-/

/-- Every intermediate smooth cutoff is one of the entries in the clamped
running maximum. -/
theorem abs_ΨReal_sq_le_realSmoothBlockMaxSq
    {a b c : ℕ} (hac : a ≤ c) (hcb : c ≤ b)
    (omega : Omega) (z : ℝ) :
    |ΨReal omega z c| ^ 2 ≤ realSmoothBlockMaxSq a b omega z := by
  unfold realSmoothBlockMaxSq finiteRunningMax
  have hcMem : c ∈ Finset.range (b + 1) := by
    exact Finset.mem_range.mpr (by omega)
  have hcutoff : freshCutoff a b c = c :=
    freshCutoff_eq_self hac hcb
  simpa only [hcutoff] using!
    (Finset.le_sup'
      (fun k ↦ |ΨReal omega z (freshCutoff a b k)| ^ 2) hcMem)

/-- The global block-max kernel is integrable.  This follows from the
already-proved frozen-fiber estimate by choosing the fresh signs from the
given global configuration. -/
theorem integrableOn_realSmoothBlockMaxSq_div_sq
    {a b : ℕ} (hab : a ≤ b) (omega : Omega) :
    IntegrableOn
      (fun z : ℝ ↦ realSmoothBlockMaxSq a b omega z / z ^ 2)
      (Ioi (0 : ℝ)) := by
  let v : FreshCube a b := fun p ↦ omega p
  have hsplice : spliceFresh omega v = omega := by
    funext p
    by_cases hp : p ∈ freshPrimes a b
    · simpa [v] using! spliceFresh_of_mem omega v hp
    · simpa [v] using! spliceFresh_of_not_mem omega v hp
  have h := integrableOn_realFrozenSmoothPathMaxSq_div_sq omega v hab
  simpa only [← realSmoothBlockMaxSq_spliceFresh, hsplice] using! h

/-- The cutoff occurring in Caich's localized main term. -/
noncomputable def caichLocalizedSmoothCutoff (x : ℕ) (z : ℝ) : ℕ :=
  ⌊(x : ℝ) / z⌋₊

/-- Caich's localized main energy on the block `(a,b]`.  `Ioc` is the exact
orientation obtained after the change of variables `z = x/t`; changing the
choice of endpoints would not affect the integral, but this convention makes
the floor inequalities literal. -/
noncomputable def caichLocalizedMainEnergy
    (x a b : ℕ) (omega : Omega) : ℝ :=
  (Real.log (b : ℝ))⁻¹ *
    ∫ z in Ioc ((x : ℝ) / (b : ℝ)) ((x : ℝ) / (a : ℝ)),
      |ΨReal omega z (caichLocalizedSmoothCutoff x z)| ^ 2 / z ^ 2

/-- On the localization interval, the moving cutoff lies in `[a,b]`. -/
theorem caichLocalizedSmoothCutoff_mem
    {x a b : ℕ} (ha : 1 ≤ a) (hab : a ≤ b) {z : ℝ}
    (hz : z ∈ Ioc ((x : ℝ) / (b : ℝ)) ((x : ℝ) / (a : ℝ))) :
    a ≤ caichLocalizedSmoothCutoff x z ∧
      caichLocalizedSmoothCutoff x z ≤ b := by
  have hb : 0 < b := lt_of_lt_of_le Nat.zero_lt_one (ha.trans hab)
  have hax : (0 : ℝ) ≤ (x : ℝ) / z := by
    have hzpos : 0 < z := by
      have hxnonneg : (0 : ℝ) ≤ (x : ℝ) := by positivity
      have hxbnonneg : (0 : ℝ) ≤ (x : ℝ) / (b : ℝ) := by positivity
      exact hxbnonneg.trans_lt hz.1
    positivity
  have hzpos : 0 < z := by
    have hxbnonneg : (0 : ℝ) ≤ (x : ℝ) / (b : ℝ) := by positivity
    exact hxbnonneg.trans_lt hz.1
  have haR : (0 : ℝ) < (a : ℝ) := by positivity
  have hbR : (0 : ℝ) < (b : ℝ) := by positivity
  have hlower : (a : ℝ) ≤ (x : ℝ) / z := by
    have hxdiv : z * (a : ℝ) ≤ (x : ℝ) := by
      have := (le_div_iff₀ haR).mp hz.2
      nlinarith
    exact (le_div_iff₀ hzpos).2 (by simpa [mul_comm] using! hxdiv)
  have hupper : (x : ℝ) / z ≤ (b : ℝ) := by
    have hxlt : (x : ℝ) < z * (b : ℝ) :=
      (div_lt_iff₀ hbR).mp hz.1
    exact (div_le_iff₀ hzpos).2 (by
      nlinarith)
  constructor
  · unfold caichLocalizedSmoothCutoff
    exact Nat.le_floor hlower
  · unfold caichLocalizedSmoothCutoff
    exact_mod_cast (Nat.floor_le hax).trans hupper

set_option maxHeartbeats 800000 in
-- The countable-product measurability elaboration unfolds the full smooth-sum definition.
/-- The smooth sum with the moving cutoff `floor (x / z)` is measurable in
the integration variable. -/
theorem measurable_ΨReal_caichLocalizedSmoothCutoff
    (omega : Omega) (x : ℕ) :
    Measurable fun z : ℝ ↦
      ΨReal omega z (caichLocalizedSmoothCutoff x z) := by
  let F : ℝ × ℕ → ℝ := fun zy ↦ ΨReal omega zy.1 zy.2
  have hF : Measurable F := by
    apply measurable_from_prod_countable_left
    intro y
    exact measurable_ΨReal_cutoff omega y
  have hcutoff : Measurable fun z : ℝ ↦
      caichLocalizedSmoothCutoff x z := by
    unfold caichLocalizedSmoothCutoff
    exact Nat.measurable_floor.comp (measurable_const.div measurable_id)
  exact hF.comp (measurable_id.prodMk hcutoff)

/-- The localized moving-cutoff kernel is integrable on its finite interval.
It is dominated by the global block-max kernel, whose integrability was
proved above. -/
theorem integrableOn_caichLocalizedMainKernel
    {x a b : ℕ} (ha : 1 ≤ a) (hab : a ≤ b) (omega : Omega) :
    IntegrableOn
      (fun z : ℝ ↦
        |ΨReal omega z (caichLocalizedSmoothCutoff x z)| ^ 2 / z ^ 2)
      (Ioc ((x : ℝ) / (b : ℝ)) ((x : ℝ) / (a : ℝ))) := by
  let s : Set ℝ := Ioc ((x : ℝ) / (b : ℝ)) ((x : ℝ) / (a : ℝ))
  let f : ℝ → ℝ := fun z ↦
    |ΨReal omega z (caichLocalizedSmoothCutoff x z)| ^ 2 / z ^ 2
  let g : ℝ → ℝ := fun z ↦ realSmoothBlockMaxSq a b omega z / z ^ 2
  have hs : s ⊆ Ioi (0 : ℝ) := by
    intro z hz
    have hb : 0 < b := lt_of_lt_of_le Nat.zero_lt_one (ha.trans hab)
    have hxb : (0 : ℝ) ≤ (x : ℝ) / (b : ℝ) := by positivity
    exact hxb.trans_lt hz.1
  have hg : IntegrableOn g s :=
    (integrableOn_realSmoothBlockMaxSq_div_sq hab omega).mono_set hs
  have hfMeas : AEStronglyMeasurable f (volume.restrict s) := by
    apply Measurable.aestronglyMeasurable
    exact ((measurable_ΨReal_caichLocalizedSmoothCutoff omega x).abs.pow_const 2).div
      (measurable_id.pow_const 2)
  refine hg.mono' hfMeas ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with z hz
  have hcutoff := caichLocalizedSmoothCutoff_mem ha hab hz
  have hpoint := abs_ΨReal_sq_le_realSmoothBlockMaxSq
    hcutoff.1 hcutoff.2 omega z
  have hz0 : 0 ≤ z ^ 2 := sq_nonneg z
  have hf0 : 0 ≤
      |ΨReal omega z (caichLocalizedSmoothCutoff x z)| ^ 2 / z ^ 2 := by
    positivity
  dsimp only [f, g]
  rw [Real.norm_eq_abs, abs_of_nonneg hf0]
  exact div_le_div_of_nonneg_right hpoint hz0

/-- The localized main term in Caich's smoothing inequality is bounded by
the concrete block energy controlled by equation (16).  No probability or
number theory enters this comparison. -/
theorem caichLocalizedMainEnergy_le_realSmoothBlockEnergy
    {x a b : ℕ} (ha : 1 ≤ a) (hab : a ≤ b) (hb : 2 ≤ b)
    (omega : Omega) :
    caichLocalizedMainEnergy x a b omega ≤
      realSmoothBlockEnergy a b omega := by
  let s : Set ℝ := Ioc ((x : ℝ) / (b : ℝ)) ((x : ℝ) / (a : ℝ))
  let f : ℝ → ℝ := fun z ↦
    |ΨReal omega z (caichLocalizedSmoothCutoff x z)| ^ 2 / z ^ 2
  let g : ℝ → ℝ := fun z ↦ realSmoothBlockMaxSq a b omega z / z ^ 2
  have hs : s ⊆ Ioi (0 : ℝ) := by
    intro z hz
    have hxb : (0 : ℝ) ≤ (x : ℝ) / (b : ℝ) := by positivity
    exact hxb.trans_lt hz.1
  have hf : IntegrableOn f s := by
    simpa only [s, f] using!
      integrableOn_caichLocalizedMainKernel ha hab omega
  have hgIoi : IntegrableOn g (Ioi (0 : ℝ)) := by
    simpa only [g] using! integrableOn_realSmoothBlockMaxSq_div_sq hab omega
  have hg : IntegrableOn g s := hgIoi.mono_set hs
  have hpoint : ∀ z ∈ s, f z ≤ g z := by
    intro z hz
    have hcutoff := caichLocalizedSmoothCutoff_mem ha hab hz
    exact div_le_div_of_nonneg_right
      (abs_ΨReal_sq_le_realSmoothBlockMaxSq
        hcutoff.1 hcutoff.2 omega z) (sq_nonneg z)
  have hsame : (∫ z in s, f z) ≤ ∫ z in s, g z :=
    setIntegral_mono_on hf hg measurableSet_Ioc hpoint
  have hg0 : 0 ≤ᵐ[volume.restrict (Ioi (0 : ℝ))] g := by
    filter_upwards with z
    exact div_nonneg
      (ConcreteThinBlockSchedule.realSmoothBlockMaxSq_nonneg a b omega z)
      (sq_nonneg z)
  have henlarge : (∫ z in s, g z) ≤ ∫ z in Ioi (0 : ℝ), g z :=
    setIntegral_mono_set hgIoi hg0 (ae_of_all volume hs)
  have hlog : 0 ≤ Real.log (b : ℝ) :=
    Real.log_nonneg (by exact_mod_cast (show 1 ≤ b by omega))
  unfold caichLocalizedMainEnergy realSmoothBlockEnergy
  dsimp only [s, f, g] at hsame henlarge ⊢
  exact mul_le_mul_of_nonneg_left (hsame.trans henlarge) (inv_nonneg.mpr hlog)

end Problem520
end Erdos
