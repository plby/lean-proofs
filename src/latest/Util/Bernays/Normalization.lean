import Util.BinQuadForm
import Mathlib.Analysis.Asymptotics.SpecificAsymptotics
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# Endpoint and normalization lemmas for Bernays' theorem

These lemmas retain the original real endpoint count. They permit the arithmetic
argument to be carried out at natural endpoints and then transfer its exact
asymptotic, with the same constant, to the statement over `ℝ`.
-/

open Filter Asymptotics
open scoped Topology

namespace BinQuadForm

theorem B_natFloor (f : BinQuadForm) {x : ℝ} (hx : 0 ≤ x) :
    f.B (⌊x⌋₊ : ℝ) = f.B x := by
  rw [f.B_eq_card_filter (Nat.cast_nonneg _), f.B_eq_card_filter hx]
  simp only [Nat.floor_natCast]

end BinQuadForm

namespace Bernays

/-- The normalization appearing in the original theorem. -/
noncomputable def scale (x : ℝ) : ℝ := x / Real.sqrt (Real.log x)

theorem scale_pos {x : ℝ} (hx : 1 < x) : 0 < scale x :=
  div_pos (zero_lt_one.trans hx) (Real.sqrt_pos.mpr (Real.log_pos hx))

theorem scale_tendsto_atTop : Tendsto scale atTop atTop := by
  have h := (tendsto_exp_div_rpow_atTop (1 / 2)).comp Real.tendsto_log_atTop
  apply h.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
  simp only [Function.comp_apply, scale, Real.exp_log hx, Real.sqrt_eq_rpow]

theorem sqrt_isEquivalent {α : Type*} {l : Filter α} {f g : α → ℝ}
    (h : f ~[l] g) (hg : ∀ᶠ x in l, 0 < g x) :
    (fun x => Real.sqrt (f x)) ~[l] (fun x => Real.sqrt (g x)) := by
  have ht := (isEquivalent_iff_tendsto_one (hg.mono fun _ hx => hx.ne')).mp h
  apply isEquivalent_of_tendsto_one
  have hs := ht.sqrt
  simp only [Real.sqrt_one] at hs
  apply hs.congr'
  filter_upwards [hg] with x hx
  exact Real.sqrt_div' _ hx.le

theorem scale_natFloor_isEquivalent :
    (fun x : ℝ => scale (⌊x⌋₊ : ℝ)) ~[atTop] scale := by
  have hfloor : (fun x : ℝ => (⌊x⌋₊ : ℝ)) ~[atTop] (fun x => x) :=
    isEquivalent_nat_floor
  have hlog := hfloor.log tendsto_id
  have hsqrt := sqrt_isEquivalent hlog
    (Real.tendsto_log_atTop.eventually (eventually_gt_atTop 0))
  exact hfloor.div hsqrt

theorem constant_scale_natFloor_isEquivalent (C : ℝ) :
    (fun x : ℝ => C * (⌊x⌋₊ : ℝ) / Real.sqrt (Real.log (⌊x⌋₊ : ℝ))) ~[atTop]
      (fun x : ℝ => C * x / Real.sqrt (Real.log x)) := by
  have h := (IsEquivalent.refl : (fun _ : ℝ => C) ~[atTop] (fun _ => C)).mul
    scale_natFloor_isEquivalent
  change (fun x : ℝ => C * ((⌊x⌋₊ : ℝ) / Real.sqrt (Real.log (⌊x⌋₊ : ℝ)))) ~[atTop]
    (fun x : ℝ => C * (x / Real.sqrt (Real.log x))) at h
  simpa only [mul_div_assoc] using h

/-- Natural and real endpoint versions have exactly the same asymptotic constant. -/
theorem real_asymptotic_iff_nat (f : BinQuadForm) (C : ℝ) :
    ((fun x : ℝ => (f.B x : ℝ)) ~[atTop]
      (fun x : ℝ => C * x / Real.sqrt (Real.log x))) ↔
    ((fun N : ℕ => (f.B (N : ℝ) : ℝ)) ~[atTop]
      (fun N : ℕ => C * (N : ℝ) / Real.sqrt (Real.log (N : ℝ)))) := by
  constructor
  · intro h
    exact h.comp_tendsto tendsto_natCast_atTop_atTop
  · intro h
    have hfloor := h.comp_tendsto (tendsto_nat_floor_atTop (α := ℝ))
    have hreal := hfloor.trans (constant_scale_natFloor_isEquivalent C)
    apply hreal.congr_left
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with x hx
    exact congrArg (fun n : ℕ => (n : ℝ)) (f.B_natFloor hx)

end Bernays
