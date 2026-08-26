import ErdosProblems.Erdos421.PerronKernel

/-! # Mellin inversion for the triangular cutoff -/

namespace Erdos421

open Complex Filter MeasureTheory Set Topology

noncomputable def triangularMellinWeight : ℝ → ℂ :=
  (Ioc (0 : ℝ) 1).indicator (fun x ↦ 1 - (x : ℂ))

theorem triangularMellinWeight_eq_of_pos {x : ℝ} (hx : 0 < x) :
    triangularMellinWeight x = ((max 0 (1 - x) : ℝ) : ℂ) := by
  by_cases hx1 : x ≤ 1
  · have hmem : x ∈ Ioc (0 : ℝ) 1 := ⟨hx, hx1⟩
    simp only [triangularMellinWeight, indicator_of_mem hmem,
      max_eq_right (sub_nonneg.mpr hx1), ofReal_sub, ofReal_one]
  · have hmem : x ∉ Ioc (0 : ℝ) 1 := fun h ↦ hx1 h.2
    simp only [triangularMellinWeight, indicator_of_notMem hmem,
      max_eq_left (by linarith : 1 - x ≤ 0), ofReal_zero]

theorem triangularMellinWeight_continuousAt {x : ℝ} (hx : 0 < x) :
    ContinuousAt triangularMellinWeight x := by
  have h : ContinuousAt (fun y : ℝ ↦ ((max 0 (1 - y) : ℝ) : ℂ)) x := by fun_prop
  apply h.congr_of_eventuallyEq
  filter_upwards [Ioi_mem_nhds hx] with y hy
  exact triangularMellinWeight_eq_of_pos hy

theorem hasMellin_triangularMellinWeight {s : ℂ} (hs : 0 < s.re) :
    HasMellin triangularMellinWeight s (perronKernel s) := by
  have hf := hasMellin_one_Ioc hs
  have hg := hasMellin_cpow_Ioc (1 : ℂ) (by simpa only [one_re] using
    (by linarith : 0 < s.re + 1))
  have hw : triangularMellinWeight = fun x ↦
      (Ioc (0 : ℝ) 1).indicator (fun _ ↦ (1 : ℂ)) x -
        (Ioc (0 : ℝ) 1).indicator (fun y ↦ (y : ℂ) ^ (1 : ℂ)) x := by
    funext x
    by_cases hx : x ∈ Ioc (0 : ℝ) 1
    · simp only [triangularMellinWeight, indicator_of_mem hx, cpow_one]
    · simp only [triangularMellinWeight, indicator_of_notMem hx, sub_zero]
  have h := hasMellin_sub hf.1 hg.1
  rw [hf.2, hg.2] at h
  have hs0 : s ≠ 0 := by intro he; simp only [he, zero_re, lt_self_iff_false] at hs
  have hs1 : s + 1 ≠ 0 := by
    intro he
    have hr := congrArg Complex.re he
    simp only [add_re, one_re, zero_re] at hr
    linarith
  have he : 1 / s - 1 / (s + 1) = perronKernel s := by
    unfold perronKernel
    field_simp
    ring
  rwa [he, ← hw] at h

theorem triangularMellin_inversion {σ x : ℝ} (hσ : 1 / 2 ≤ σ) (hx : 0 < x) :
    mellinInv σ perronKernel x = triangularMellinWeight x := by
  have hσp : 0 < σ := by linarith
  have hM := hasMellin_triangularMellinWeight (s := (σ : ℂ))
    (by simpa only [ofReal_re] using hσp)
  have hvertical : ∀ y : ℝ,
      mellin triangularMellinWeight ((σ : ℂ) + y * I) = perronKernel ((σ : ℂ) + y * I) := by
    intro y
    exact (hasMellin_triangularMellinWeight (by simpa using hσp)).2
  have hF : VerticalIntegrable (mellin triangularMellinWeight) σ := by
    unfold VerticalIntegrable
    simp_rw [hvertical]
    exact perronKernel_vertical_integrable hσ
  have h := mellinInv_mellin_eq σ triangularMellinWeight hx hM.1 hF
    (triangularMellinWeight_continuousAt hx)
  have he : mellinInv σ (mellin triangularMellinWeight) x = mellinInv σ perronKernel x := by
    unfold mellinInv
    simp_rw [hvertical]
  rwa [he] at h

end Erdos421
