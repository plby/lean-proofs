/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Copyright 2026 The Formal Conjectures Authors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/

import ErdosProblems.Erdos735.ProjectiveArrangement

/-!
# Injectivity of a projective chart coordinate on one line

Two distinct charted points on a projective line certify that the chart
coordinate is nonconstant on that line.  Consequently it is injective on
the entire part of the line in the affine chart, not merely on a prescribed
finite vertex set.  This is the algebraic chart-invariance input used to
compare concrete restriction-sector endpoints with cyclic successors.
-/

open scoped LinearAlgebra.Projectivization Matrix
open Matrix

namespace Erdos735.ProjectiveArrangement

open ChartOrder SignVector

noncomputable section

def projectiveDotLinear (h : Vec3) : Module.Dual ℝ Vec3 where
  toFun z := h ⬝ᵥ z
  map_add' u v := by simp [dotProduct_add]
  map_smul' c z := by simp [dotProduct_smul]

def projectivePairLinear (h : Vec3) (f : Module.Dual ℝ Vec3) :
    Vec3 →ₗ[ℝ] (Fin 2 → ℝ) :=
  LinearMap.pi fun i ↦ Fin.cases (projectiveDotLinear h) (fun _ ↦ f) i

theorem projectivePairLinear_surjective {h : Vec3} (hh : h ≠ 0)
    {f : Module.Dual ℝ Vec3} {u : Vec3}
    (hhu : h ⬝ᵥ u = 0) (hfu : f u = 1) :
    Function.Surjective (projectivePairLinear h f) := by
  intro y
  let q : Vec3 := (h ⬝ᵥ h)⁻¹ • h
  let q0 : Vec3 := q - (f q) • u
  refine ⟨(y 0) • q0 + (y 1) • u, ?_⟩
  funext i
  refine Fin.cases ?_ (fun j ↦ ?_) i
  · have hself : h ⬝ᵥ h ≠ 0 := (dotProduct_self_pos hh).ne'
    change h ⬝ᵥ ((y 0) • q0 + (y 1) • u) = y 0
    simp [q0, q, dotProduct_add, dotProduct_smul, hhu, hself]
  · have hj : j = 0 := Fin.eq_zero j
    subst j
    change f ((y 0) • q0 + (y 1) • u) = y 1
    simp [q0, q, hfu]

theorem eq_zero_of_dot_apply_apply_eq_zero
    {h : Vec3} (hh : h ≠ 0) {f g : Module.Dual ℝ Vec3}
    {u d r : Vec3}
    (hhu : h ⬝ᵥ u = 0) (hfu : f u = 1)
    (hhd : h ⬝ᵥ d = 0) (hfd : f d = 0) (hgd : g d ≠ 0)
    (hhr : h ⬝ᵥ r = 0) (hfr : f r = 0) (hgr : g r = 0) : r = 0 := by
  let F := projectivePairLinear h f
  have hsurj : Function.Surjective F := projectivePairLinear_surjective hh hhu hfu
  have hrange : LinearMap.range F = ⊤ := LinearMap.range_eq_top.mpr hsurj
  have hdimker : Module.finrank ℝ (LinearMap.ker F) = 1 := by
    have hdim := LinearMap.finrank_range_add_finrank_ker F
    have hrank : Module.finrank ℝ (LinearMap.range F) = 2 := by
      rw [hrange, finrank_top]
      simp
    rw [hrank] at hdim
    have hvec : Module.finrank ℝ Vec3 = 3 := by simp [Vec3]
    rw [hvec] at hdim
    omega
  have hdker : d ∈ LinearMap.ker F := by
    rw [LinearMap.mem_ker]
    funext i
    fin_cases i
    · exact hhd
    · exact hfd
  have hrker : r ∈ LinearMap.ker F := by
    rw [LinearMap.mem_ker]
    funext i
    fin_cases i
    · exact hhr
    · exact hfr
  let dd : LinearMap.ker F := ⟨d, hdker⟩
  have hdd : dd ≠ 0 := by
    intro hd0
    apply hgd
    have : d = 0 := congrArg Subtype.val hd0
    simp [this]
  obtain ⟨c, hc⟩ :=
    (finrank_eq_one_iff_of_nonzero' dd hdd).mp hdimker ⟨r, hrker⟩
  have hcr : c • d = r := congrArg Subtype.val hc
  have hcg := congrArg g hcr
  simp only [map_smul, hgr] at hcg
  have hc0 : c = 0 := (mul_eq_zero.mp hcg).resolve_right hgd
  rw [← hcr, hc0, zero_smul]

theorem chartCoord_injective_on_projective_line
    {h : Vec3} (hh : h ≠ 0)
    (f g : Module.Dual ℝ Vec3)
    {p q : ℙ ℝ Vec3}
    (hfp : f p.rep ≠ 0) (hfq : f q.rep ≠ 0)
    (hpp : OnProjectiveLine h p) (hqq : OnProjectiveLine h q)
    (hpq : chartCoord f g p ≠ chartCoord f g q) :
    Set.InjOn (chartCoord f g)
      {x : ℙ ℝ Vec3 | f x.rep ≠ 0 ∧ OnProjectiveLine h x} := by
  intro x hx y hy hxy
  let P := chartRep f p
  let Q := chartRep f q
  let X := chartRep f x
  let Y := chartRep f y
  let d := Q - P
  let r := X - Y
  have hhu : h ⬝ᵥ P = 0 :=
    (apply_chartRep_eq_zero_iff f (projectiveDotLinear h) p hfp).2 hpp
  have hfu : f P = 1 := apply_chartRep f p hfp
  have hhd : h ⬝ᵥ d = 0 := by
    rw [dotProduct_sub]
    exact sub_eq_zero.mpr <|
      (apply_chartRep_eq_zero_iff f (projectiveDotLinear h) q hfq).2 hqq |>.trans hhu.symm
  have hfd : f d = 0 := by
    simp [d, P, Q, apply_chartRep f p hfp, apply_chartRep f q hfq]
  have hgd : g d ≠ 0 := by
    simpa [d, P, Q, chartCoord, map_sub, sub_ne_zero] using hpq.symm
  have hhr : h ⬝ᵥ r = 0 := by
    rw [dotProduct_sub]
    apply sub_eq_zero.mpr
    exact ((apply_chartRep_eq_zero_iff f (projectiveDotLinear h) x hx.1).2 hx.2).trans
      ((apply_chartRep_eq_zero_iff f (projectiveDotLinear h) y hy.1).2 hy.2).symm
  have hfr : f r = 0 := by
    simp [r, X, Y, apply_chartRep f x hx.1, apply_chartRep f y hy.1]
  have hgr : g r = 0 := by
    simpa [r, X, Y, chartCoord, map_sub] using sub_eq_zero.mpr hxy
  have hr0 := eq_zero_of_dot_apply_apply_eq_zero hh hhu hfu hhd hfd hgd hhr hfr hgr
  have hXY : X = Y := sub_eq_zero.mp hr0
  rw [← mk_chartRep f x hx.1, ← mk_chartRep f y hy.1]
  congr

/-- A vector already normalized to chart height one is exactly the canonical
chart representative of its projective class. -/
theorem chartRep_mk_of_apply_eq_one (f : Module.Dual ℝ Vec3)
    {x : Vec3} (hx : x ≠ 0) (hfx : f x = 1) :
    chartRep f (Projectivization.mk ℝ x hx) = x := by
  let p := Projectivization.mk ℝ x hx
  have hfp : f p.rep ≠ 0 := by
    intro hzero
    have : f x = 0 :=
      (apply_rep_mk_eq_zero_iff f x hx).mp hzero
    linarith
  have hmk : Projectivization.mk ℝ (chartRep f p)
      (chartRep_nonzero f p hfp) = Projectivization.mk ℝ x hx := by
    simpa [p] using mk_chartRep f p hfp
  obtain ⟨a, ha⟩ :=
    (Projectivization.mk_eq_mk_iff' ℝ (chartRep f p) x
      (chartRep_nonzero f p hfp) hx).mp hmk
  have haf := congrArg f ha
  have haone : (a : ℝ) = 1 := by
    simpa [apply_chartRep f p hfp, hfx] using haf
  simpa [haone] using ha.symm

theorem chartCoord_mk_of_apply_eq_one (f g : Module.Dual ℝ Vec3)
    {x : Vec3} (hx : x ≠ 0) (hfx : f x = 1) :
    chartCoord f g (Projectivization.mk ℝ x hx) = g x := by
  simp [chartCoord, chartRep_mk_of_apply_eq_one f hx hfx]

theorem chartRep_mk_eq_inv_smul (f : Module.Dual ℝ Vec3)
    {x : Vec3} (hx : x ≠ 0) (hfx : f x ≠ 0) :
    chartRep f (Projectivization.mk ℝ x hx) = (f x)⁻¹ • x := by
  let z := (f x)⁻¹ • x
  have hz : z ≠ 0 := smul_ne_zero (inv_ne_zero hfx) hx
  have hfz : f z = 1 := by simp [z, hfx]
  have heq : Projectivization.mk ℝ z hz = Projectivization.mk ℝ x hx := by
    apply (Projectivization.mk_eq_mk_iff' ℝ z x hz hx).2
    exact ⟨(f x)⁻¹, rfl⟩
  rw [← heq]
  exact chartRep_mk_of_apply_eq_one f hz hfz

/-- On a charted projective line, affine interpolation of normalized
representatives is characterized by affine interpolation of the scalar
chart coordinate. -/
theorem eq_mk_chartRep_interpolation
    {h : Vec3} (hh : h ≠ 0) (f g : Module.Dual ℝ Vec3)
    {p q y : ℙ ℝ Vec3}
    (hfp : f p.rep ≠ 0) (hfq : f q.rep ≠ 0) (hfy : f y.rep ≠ 0)
    (hpp : OnProjectiveLine h p) (hqq : OnProjectiveLine h q)
    (hyy : OnProjectiveLine h y)
    (hpq : chartCoord f g p ≠ chartCoord f g q)
    (r : ℝ)
    (hycoord : chartCoord f g y =
      (1 - r) * chartCoord f g p + r * chartCoord f g q) :
    let z := (1 - r) • chartRep f p + r • chartRep f q
    ∃ hz : z ≠ 0, y = Projectivization.mk ℝ z hz := by
  let z := (1 - r) • chartRep f p + r • chartRep f q
  have hfz : f z = 1 := by
    simp [z, apply_chartRep f p hfp, apply_chartRep f q hfq]
  have hz : z ≠ 0 := by
    intro hz0
    rw [hz0, map_zero] at hfz
    norm_num at hfz
  refine ⟨hz, ?_⟩
  apply (chartCoord_injective_on_projective_line hh f g hfp hfq hpp hqq hpq)
  · exact ⟨hfy, hyy⟩
  · constructor
    · intro hzero
      have : f z = 0 :=
        (apply_rep_mk_eq_zero_iff f z hz).mp hzero
      linarith
    · apply (onProjectiveLine_mk_iff h z hz).2
      simp only [z, dotProduct_add, dotProduct_smul, smul_eq_mul]
      have hp0 : h ⬝ᵥ chartRep f p = 0 :=
        (apply_chartRep_eq_zero_iff f (projectiveDotLinear h) p hfp).2 hpp
      have hq0 : h ⬝ᵥ chartRep f q = 0 :=
        (apply_chartRep_eq_zero_iff f (projectiveDotLinear h) q hfq).2 hqq
      rw [hp0, hq0]
      ring
  · rw [chartCoord_mk_of_apply_eq_one f g hz hfz]
    simp only [z, map_add, map_smul, chartCoord]
    change chartCoord f g y =
      (1 - r) * chartCoord f g p + r * chartCoord f g q
    exact hycoord

/-- Two nonzero coefficients of the same sign give an interior affine
parameter after projectivizing their linear combination. -/
theorem sameSign_weightedParameter_between
    {l u A C : ℝ} (hlu : l < u) (hAC : 0 < A * C) :
    let t := (A * l + C * u) / (A + C)
    l < t ∧ t < u := by
  have hA : A ≠ 0 := by
    intro h
    rw [h, zero_mul] at hAC
    linarith
  have hC : C ≠ 0 := by
    intro h
    rw [h, mul_zero] at hAC
    linarith
  rcases lt_or_gt_of_ne hA with hAneg | hApos
  · have hCneg : C < 0 := by
      by_contra h
      have : 0 < C := lt_of_le_of_ne (le_of_not_gt h) (Ne.symm hC)
      nlinarith
    have hsum : A + C < 0 := by linarith
    dsimp
    constructor
    · apply (lt_div_iff_of_neg hsum).2
      nlinarith
    · apply (div_lt_iff_of_neg hsum).2
      nlinarith
  · have hCpos : 0 < C := by
      by_contra h
      have : C < 0 := lt_of_le_of_ne (le_of_not_gt h) hC
      nlinarith
    have hsum : 0 < A + C := by linarith
    dsimp
    constructor
    · apply (lt_div_iff₀ hsum).2
      nlinarith
    · apply (div_lt_iff₀ hsum).2
      nlinarith

theorem weighted_chartPoint_identity
    (x d : Vec3) (l u A C : ℝ) (hAC : A + C ≠ 0) :
    A • (x + l • d) + C • (x + u • d) =
      (A + C) •
        (x + ((A * l + C * u) / (A + C)) • d) := by
  have ht : (A + C) * ((A * l + C * u) / (A + C)) = A * l + C * u := by
    field_simp [hAC]
  simp only [smul_add, smul_smul]
  rw [ht]
  module

end

end Erdos735.ProjectiveArrangement
