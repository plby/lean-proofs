import Mathlib

/- Ported from Lean 4.31.0 to 4.33.0; imports and elaboration options adapted. -/
set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

namespace Erdos489

open Filter
open scoped Topology

/-- Square-root thinness makes the squared forbidden count at `2x+1`
negligible compared with `x`. -/
theorem tendsto_count_two_mul_add_one_sq_div
    (p : ℕ → Prop) [DecidablePred p]
    (hcount : (fun n : ℕ => (Nat.count p n : ℝ)) =o[atTop]
      (fun n : ℕ => Real.sqrt (n : ℝ))) :
    Tendsto (fun x : ℕ =>
      (Nat.count p (2 * x + 1) : ℝ) ^ 2 / (x : ℝ))
      atTop (𝓝 0) := by
  let g : ℕ → ℕ := fun x => 2 * x + 1
  have hgmono : StrictMono g := by
    intro x y hxy
    dsimp [g]
    omega
  have hg : Tendsto g atTop atTop := hgmono.tendsto_atTop
  have hr := (hcount.comp_tendsto hg).tendsto_div_nhds_zero
  have hinv : Tendsto (fun x : ℕ => ((x : ℝ))⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop
  have hratio : Tendsto (fun x : ℕ => ((g x : ℕ) : ℝ) / (x : ℝ))
      atTop (𝓝 2) := by
    have hbase : Tendsto (fun x : ℕ => (2 : ℝ) + ((x : ℝ))⁻¹)
        atTop (𝓝 ((2 : ℝ) + 0)) := tendsto_const_nhds.add hinv
    have hbase' : Tendsto (fun x : ℕ => (2 : ℝ) + ((x : ℝ))⁻¹)
        atTop (𝓝 2) := by simpa using hbase
    refine hbase'.congr' ?_
    filter_upwards [eventually_ge_atTop 1] with x hx
    dsimp [g]
    norm_num only [Nat.cast_add, Nat.cast_mul, Nat.cast_one, Nat.cast_ofNat]
    field_simp
  have hprod := (hr.pow 2).mul hratio
  have hzero : (0 : ℝ) ^ 2 * 2 = 0 := by norm_num
  rw [hzero] at hprod
  apply hprod.congr'
  filter_upwards [eventually_ge_atTop 1] with x hx
  dsimp [g]
  have hgpos : (0 : ℝ) < (2 * x + 1 : ℕ) := by positivity
  have hsqrt : (Real.sqrt ((2 * x + 1 : ℕ) : ℝ)) ^ 2 =
      ((2 * x + 1 : ℕ) : ℝ) := Real.sq_sqrt hgpos.le
  have hxpos : (0 : ℝ) < x := by exact_mod_cast hx
  field_simp [Real.sqrt_ne_zero'.mpr hgpos, hxpos.ne']
  nlinarith

end Erdos489
