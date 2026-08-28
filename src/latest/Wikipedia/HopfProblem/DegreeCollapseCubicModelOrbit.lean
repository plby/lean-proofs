import Wikipedia.HopfProblem.DegreeCollapseCubicDescent
import Mathlib.Analysis.SpecialFunctions.Artanh
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Topology.Order.MonotoneConvergence

/-!
# The complete connecting orbit of the cubic model

The actual scalar trajectory is `a * tanh (a * t)`. Its derivative, full
range, and limits are proved. In particular, the cubic chart's whole open
axis is one orbit, not merely a collection of local flow germs.
-/

noncomputable section

open Set Filter Function
open scoped Topology ContDiff

namespace Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation

theorem hasDerivAt_tanh (t : ℝ) :
    HasDerivAt Real.tanh (1 - Real.tanh t ^ 2) t := by
  have h := (Real.hasDerivAt_sinh t).div (Real.hasDerivAt_cosh t) (Real.cosh_pos t).ne'
  have hf : (fun x => Real.sinh x / Real.cosh x) = Real.tanh :=
    funext (fun x => (Real.tanh_eq_sinh_div_cosh x).symm)
  change HasDerivAt (fun x => Real.sinh x / Real.cosh x) _ t at h
  rw [hf] at h
  convert h using 1
  rw [Real.tanh_eq_sinh_div_cosh]
  field_simp

theorem strictMono_tanh : StrictMono Real.tanh :=
  strictMono_of_hasDerivAt_pos hasDerivAt_tanh (fun t => sub_pos.mpr (Real.tanh_sq_lt_one t))

theorem range_tanh : range Real.tanh = Ioo (-1 : ℝ) 1 := by
  ext s
  constructor
  · rintro ⟨t, rfl⟩
    exact ⟨Real.neg_one_lt_tanh t, Real.tanh_lt_one t⟩
  · intro hs
    obtain ⟨t, -, ht⟩ := Real.tanh_surjOn hs
    exact ⟨t, ht⟩

theorem tendsto_tanh_atTop : Tendsto Real.tanh atTop (𝓝 (1 : ℝ)) := by
  apply tendsto_atTop_isLUB strictMono_tanh.monotone
  rw [range_tanh]
  exact isLUB_Ioo (by norm_num)

theorem tendsto_tanh_atBot : Tendsto Real.tanh atBot (𝓝 (-1 : ℝ)) := by
  apply tendsto_atBot_isGLB strictMono_tanh.monotone
  rw [range_tanh]
  exact isGLB_Ioo (by norm_num)

def cubicAxisParameter (a t : ℝ) : ℝ := a * Real.tanh (a * t)

theorem hasDerivAt_cubicAxisParameter (a t : ℝ) :
    HasDerivAt (cubicAxisParameter a) (a ^ 2 - cubicAxisParameter a t ^ 2) t := by
  have h := ((hasDerivAt_tanh (a * t)).comp t ((hasDerivAt_id t).const_mul a)).const_mul a
  change HasDerivAt (cubicAxisParameter a)
    (a * ((1 - Real.tanh (a * t) ^ 2) * (a * 1))) t at h
  convert h using 1
  dsimp [cubicAxisParameter]
  ring

theorem cubicAxisParameter_mem {a : ℝ} (ha : 0 < a) (t : ℝ) :
    cubicAxisParameter a t ∈ Ioo (-a) a := by
  have hlo := mul_lt_mul_of_pos_left (Real.neg_one_lt_tanh (a * t)) ha
  have hhi := mul_lt_mul_of_pos_left (Real.tanh_lt_one (a * t)) ha
  constructor
  · simpa only [cubicAxisParameter, mul_neg, mul_one] using hlo
  · simpa only [cubicAxisParameter, mul_one] using hhi

theorem range_cubicAxisParameter {a : ℝ} (ha : 0 < a) :
    range (cubicAxisParameter a) = Ioo (-a) a := by
  ext s
  constructor
  · rintro ⟨t, rfl⟩
    exact cubicAxisParameter_mem ha t
  · intro hs
    have hs' : s / a ∈ Ioo (-1 : ℝ) 1 := by
      constructor
      · apply (lt_div_iff₀ ha).mpr
        simpa only [neg_one_mul] using hs.1
      · apply (div_lt_iff₀ ha).mpr
        simpa only [one_mul] using hs.2
    refine ⟨Real.artanh (s / a) / a, ?_⟩
    simp only [cubicAxisParameter, mul_div_cancel₀ _ ha.ne', Real.tanh_artanh hs']

theorem tendsto_cubicAxisParameter_atTop {a : ℝ} (ha : 0 < a) :
    Tendsto (cubicAxisParameter a) atTop (𝓝 a) := by
  have h := (tendsto_tanh_atTop.comp (tendsto_id.const_mul_atTop ha)).const_mul a
  change Tendsto (cubicAxisParameter a) atTop (𝓝 (a * 1)) at h
  simpa only [mul_one] using h

theorem tendsto_cubicAxisParameter_atBot {a : ℝ} (ha : 0 < a) :
    Tendsto (cubicAxisParameter a) atBot (𝓝 (-a)) := by
  have h := (tendsto_tanh_atBot.comp (tendsto_id.const_mul_atBot ha)).const_mul a
  change Tendsto (cubicAxisParameter a) atBot (𝓝 (a * -1)) at h
  simpa only [mul_neg, mul_one] using h

variable {m : ℕ}

def cubicModelOrbit (a t : ℝ) : Model m := (cubicAxisParameter a t, 0)

theorem cubicModelOrbit_zero (a : ℝ) : cubicModelOrbit (m := m) a 0 = 0 := by
  simp [cubicModelOrbit, cubicAxisParameter, Real.tanh_zero]

theorem hasDerivAt_cubicModelOrbit (σ : Fin m → ℝ) (a t : ℝ) :
    HasDerivAt (cubicModelOrbit a)
      (cubicDescent σ (-(a ^ 2)) (cubicModelOrbit a t)) t := by
  have h := (hasDerivAt_cubicAxisParameter a t).prodMk (hasDerivAt_const t (0 : Fin m → ℝ))
  change HasDerivAt (cubicModelOrbit a) (a ^ 2 - cubicAxisParameter a t ^ 2, 0) t at h
  convert h using 1
  apply Prod.ext
  · change -(cubicAxisParameter a t ^ 2 + -(a ^ 2)) = a ^ 2 - cubicAxisParameter a t ^ 2
    ring
  · funext i
    simp only [cubicDescent, cubicModelOrbit, Pi.zero_apply, mul_zero]

theorem range_cubicModelOrbit {a : ℝ} (ha : 0 < a) :
    range (cubicModelOrbit (m := m) a) = Ioo (-a) a ×ˢ {(0 : Fin m → ℝ)} := by
  ext p
  constructor
  · rintro ⟨t, rfl⟩
    exact ⟨cubicAxisParameter_mem ha t, rfl⟩
  · rintro ⟨hs, hz⟩
    obtain ⟨t, ht⟩ := (range_cubicAxisParameter ha).symm ▸ hs
    refine ⟨t, ?_⟩
    exact Prod.ext ht (show (0 : Fin m → ℝ) = p.2 from hz.symm)

theorem tendsto_cubicModelOrbit_atTop {a : ℝ} (ha : 0 < a) :
    Tendsto (cubicModelOrbit (m := m) a) atTop (𝓝 (a, 0)) :=
  (tendsto_cubicAxisParameter_atTop ha).prodMk_nhds tendsto_const_nhds

theorem tendsto_cubicModelOrbit_atBot {a : ℝ} (ha : 0 < a) :
    Tendsto (cubicModelOrbit (m := m) a) atBot (𝓝 (-a, 0)) :=
  (tendsto_cubicAxisParameter_atBot ha).prodMk_nhds tendsto_const_nhds

end Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation
