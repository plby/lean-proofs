import ErdosProblems.Erdos380.SaddleScale

/-! # Elementary ratio limits used to choose integer exponents -/

open Filter
open scoped Topology

namespace Erdos380

lemma nat_floor_scaled_ratio_tendsto {α : Type*} {l : Filter α} {f : α → ℝ}
    (hf : Tendsto f l atTop) {c : ℝ} (hc : 0 < c) :
    Tendsto (fun x => (⌊c * f x⌋₊ : ℝ) / f x) l (𝓝 c) := by
  have h := ((tendsto_nat_floor_div_atTop (R := ℝ)).comp (hf.const_mul_atTop hc)).mul_const c
  rw [one_mul] at h
  apply h.congr'
  filter_upwards [hf.eventually (eventually_gt_atTop (0 : ℝ))] with x hx
  simp only [Function.comp_apply]
  field_simp

lemma log_sub_log_tendsto_of_ratio {α : Type*} {l : Filter α} {f g : α → ℝ}
    {c : ℝ} (hc : 0 < c) (h : Tendsto (fun x => f x / g x) l (𝓝 c))
    (hg : Tendsto g l atTop) :
    Tendsto (fun x => Real.log (f x) - Real.log (g x)) l (𝓝 (Real.log c)) := by
  have hl := (Real.continuousAt_log hc.ne').tendsto.comp h
  apply hl.congr'
  filter_upwards [h.eventually (lt_mem_nhds hc), hg.eventually (eventually_gt_atTop (0 : ℝ))]
    with x hx hgx
  have hfx : 0 < f x := by
    have := (lt_div_iff₀ hgx).mp hx
    simpa using this
  simp only [Function.comp_apply]
  exact Real.log_div hfx.ne' hgx.ne'

lemma log_ratio_tendsto_one_of_ratio {α : Type*} {l : Filter α} {f g : α → ℝ}
    {c : ℝ} (hc : 0 < c) (h : Tendsto (fun x => f x / g x) l (𝓝 c))
    (hg : Tendsto g l atTop) :
    Tendsto (fun x => Real.log (f x) / Real.log (g x)) l (𝓝 1) := by
  have hlogg := Real.tendsto_log_atTop.comp hg
  have hh := ((log_sub_log_tendsto_of_ratio hc h hg).div_atTop hlogg).add_const 1
  rw [zero_add] at hh
  apply hh.congr'
  filter_upwards [hg.eventually (eventually_gt_atTop (1 : ℝ))] with x hx
  have hp := Real.log_pos hx
  simp only [Function.comp_apply]
  field_simp
  ring

lemma tendsto_atTop_of_pos_ratio {α : Type*} {l : Filter α} {f g : α → ℝ}
    {c : ℝ} (hc : 0 < c) (h : Tendsto (fun x => f x / g x) l (𝓝 c))
    (hg : Tendsto g l atTop) : Tendsto f l atTop := by
  have hh := h.pos_mul_atTop hc hg
  apply hh.congr'
  filter_upwards [hg.eventually (eventually_gt_atTop (0 : ℝ))] with x hx
  exact div_mul_cancel₀ _ hx.ne'

end Erdos380
