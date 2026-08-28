import Wikipedia.HopfProblem.ToricHolomorphicSheafCohomologyProjectiveCocycleSplitting

/-!
# The projective compatibility forced by the actual Laurent splittings

Uniqueness on each punctured coordinate line separates the two entire
parts. Liouville's theorem then makes the remaining positive part
constant. The negative parts satisfy the literal incidence-blowup
overlap identity, which will permit actual holomorphic blowdown descent.
-/

noncomputable section

open Complex Set Filter
open scoped Topology

namespace Wikipedia.HopfProblem.HolomorphicSheafCohomology.ProjectiveCocycle.LaurentData

variable {h : ChartCocycle} (L : LaurentData h)

theorem separated_identity (x : ℂ) (hx : x ≠ 0) :
    (∀ y : ℂ, L.E (x, y) = L.B (x⁻¹, y) + L.C (x⁻¹, y / x)) ∧
      (∀ t : ℂ, L.F (x, t) = L.D (x⁻¹, x * t)) := by
  have hpos : AnalyticOnNhd ℂ
      (fun y : ℂ => L.B (x⁻¹, y) + L.C (x⁻¹, y / x)) univ := by
    intro y _
    apply (secondSlice_entire L.B_analytic x⁻¹ y (mem_univ _)).add
    exact AnalyticAt.comp (f := fun y : ℂ => (x⁻¹, y / x))
      (L.C_analytic (x⁻¹, y / x) (mem_univ _))
      (analyticAt_const.prod analyticAt_id.div_const)
  have hneg : AnalyticOnNhd ℂ (fun t : ℂ => L.D (x⁻¹, x * t)) univ := by
    intro t _
    exact AnalyticAt.comp (f := fun t : ℂ => (x⁻¹, x * t))
      (L.D_analytic (x⁻¹, x * t) (mem_univ _))
      (analyticAt_const.prod (analyticAt_const.mul analyticAt_id))
  obtain ⟨hp, hm⟩ := entire_splitting_unique
    (secondSlice_entire L.E_analytic x) hpos
    (secondSlice_entire L.F_analytic x 0 (mem_univ _)).continuousAt
    (hneg 0 (mem_univ _)).continuousAt
    (L.F_zero x) (by simpa only [mul_zero] using L.D_zero x⁻¹)
    (fun y hy => L.triple_identity x y hx hy)
  exact ⟨fun y => congrFun hp y, fun t => congrFun hm t⟩

theorem positive_identity (x : ℂ) (hx : x ≠ 0) (y : ℂ) :
    L.E (x, y) = L.B (x⁻¹, y) + L.C (x⁻¹, y / x) :=
  (L.separated_identity x hx).1 y

theorem blowup_identity (x t : ℂ) (hx : x ≠ 0) :
    L.F (x, t) = L.D (x⁻¹, x * t) :=
  (L.separated_identity x hx).2 t

theorem positive_tendsto (y : ℂ) :
    Tendsto (fun x : ℂ => L.E (x, y)) (cocompact ℂ) (𝓝 (L.C (0, 0))) := by
  have hB : Tendsto (fun x : ℂ => L.B (x⁻¹, y)) (cocompact ℂ) (𝓝 0) := by
    simpa only [Function.comp_def, L.B_zero] using
      (L.B_analytic (0, y) (mem_univ _)).continuousAt.tendsto.comp
        (tendsto_inv_cocompact.prodMk_nhds (tendsto_const_nhds (x := y)))
  have hC : Tendsto (fun x : ℂ => L.C (x⁻¹, y / x))
      (cocompact ℂ) (𝓝 (L.C (0, 0))) := by
    have hp : Tendsto (fun x : ℂ => (x⁻¹, y * x⁻¹))
        (cocompact ℂ) (𝓝 (0, 0)) := by
      simpa only [mul_zero] using tendsto_inv_cocompact.prodMk_nhds
        ((tendsto_const_nhds (x := y)).mul tendsto_inv_cocompact)
    simpa only [Function.comp_def, div_eq_mul_inv] using
      (L.C_analytic (0, 0) (mem_univ _)).continuousAt.tendsto.comp hp
  have hlim := hB.add hC
  simp only [zero_add] at hlim
  apply hlim.congr'
  filter_upwards [eventually_ne_zero_cocompact] with x hx
  exact (L.positive_identity x hx y).symm

theorem positive_eq_const (x y : ℂ) : L.E (x, y) = L.C (0, 0) := by
  have hd : Differentiable ℂ (fun x : ℂ => L.E (x, y)) :=
    fun x => (firstSlice_entire L.E_analytic y x (mem_univ _)).differentiableAt
  exact hd.apply_eq_of_tendsto_cocompact x (L.positive_tendsto y)

theorem zeroOne_corrected (x y : ℂ) (hx : x ≠ 0) :
    h.zeroOne (x, y) = (L.A (x, y) + L.C (0, 0)) - L.C (x⁻¹, y / x) := by
  have hp := L.positive_identity x hx y
  rw [L.positive_eq_const] at hp
  have he := L.zeroOne_eq x y hx
  linear_combination he - hp

theorem zeroTwo_corrected (x y : ℂ) (hy : y ≠ 0) :
    h.zeroTwo (x, y) = (L.A (x, y) + L.C (0, 0)) + L.F (x, y⁻¹) := by
  have he := L.zeroTwo_eq x y hy
  rw [L.positive_eq_const] at he
  linear_combination he

end Wikipedia.HopfProblem.HolomorphicSheafCohomology.ProjectiveCocycle.LaurentData
