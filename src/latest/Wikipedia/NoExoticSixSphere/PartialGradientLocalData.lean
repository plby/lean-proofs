import Wikipedia.NoExoticSixSphere.PartialGradientCoordinates

/-!
# Smooth negative-family coordinate data

This structure records an actual partial diffeomorphism and its checked
properties, including a uniform negative Hessian bound on its source. The
construction below proves existence from a negative bound on an open domain.
-/

open Set
open scoped ContDiff Manifold

namespace NoExoticSixSphere.PartialGradientCoordinates

variable {D E : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D]
  [NormedAddCommGroup E] [NormedSpace ℝ E]

structure LocalData (f : E → ℝ) (L : D →L[ℝ] E) (U : Set E) where
  chart : PartialDiffeomorph 𝓘(ℝ, E) 𝓘(ℝ, (D →L[ℝ] ℝ) × (derivative f L).ker)
    E ((D →L[ℝ] ℝ) × (derivative f L).ker) ∞
  zero_mem_source : (0 : E) ∈ chart.source
  source_subset : chart.source ⊆ U
  map_zero : chart 0 = 0
  map_fst : ∀ z, (chart z).1 = gradient f L z
  same_snd_iff : ∀ z z', (chart z).2 = (chart z').2 ↔ ∃ w : D, z' = z + L w
  uniform_bound : ∃ c > 0, ∀ z ∈ chart.source, ∀ w : D,
    fderiv ℝ (fderiv ℝ f) z (L w) (L w) ≤ -c * ‖w‖ ^ 2

def LocalData.mono {f : E → ℝ} {L : D →L[ℝ] E} {U V : Set E}
    (C : LocalData f L U) (hUV : U ⊆ V) : LocalData f L V :=
  { C with source_subset := C.source_subset.trans hUV }

theorem LocalData.map_snd_add {f : E → ℝ} {L : D →L[ℝ] E} {U : Set E}
    (C : LocalData f L U) (z : E) (w : D) : (C.chart (z + L w)).2 = (C.chart z).2 :=
  ((C.same_snd_iff z (z + L w)).mpr ⟨w, rfl⟩).symm

theorem LocalData.gradient_zero_iff {f : E → ℝ} {L : D →L[ℝ] E} {U : Set E}
    (C : LocalData f L U) (z : E) (hz : z ∈ C.chart.source) :
    gradient f L z = 0 ↔ ∃ y : (derivative f L).ker,
      (0, y) ∈ C.chart.target ∧ C.chart.symm (0, y) = z :=
  gradient_zero_iff_inverse_zero_slice f L C.chart C.map_fst z hz

variable [CompleteSpace E] [FiniteDimensional ℝ D]

theorem nonempty_localData_of_bound (f : E → ℝ) (L : D →L[ℝ] E) (U : Set E)
    (hU : IsOpen U) (hzero : (0 : E) ∈ U) (hf : ContDiffOn ℝ ∞ f U)
    (hcrit : fderiv ℝ f 0 = 0) (c : ℝ) (hc : 0 < c)
    (hbound : ∀ z ∈ U, ∀ w : D, fderiv ℝ (fderiv ℝ f) z (L w) (L w) ≤ -c * ‖w‖ ^ 2) :
    Nonempty (LocalData f L U) := by
  have hn : ∀ w : D, w ≠ 0 → fderiv ℝ (fderiv ℝ f) 0 (L w) (L w) < 0 := by
    intro w hw
    exact (hbound 0 hzero w).trans_lt
      (mul_neg_of_neg_of_pos (neg_neg_of_pos hc) (sq_pos_of_pos (norm_pos_iff.mpr hw)))
  obtain ⟨Φ, hΦ0, hΦU, hΦ⟩ := exists_localCoordinates f L hn U hU hzero hf
  refine ⟨{
    chart := Φ
    zero_mem_source := hΦ0
    source_subset := hΦU
    map_zero := ?_
    map_fst := ?_
    same_snd_iff := ?_
    uniform_bound := ⟨c, hc, fun z hz w ↦ hbound z (hΦU hz) w⟩ }⟩
  · rw [hΦ]
    exact coordinates_zero f L hn hcrit
  · intro z
    rw [hΦ]
    rfl
  · intro z z'
    rw [hΦ]
    exact projection_eq_iff f L hn z z'

end NoExoticSixSphere.PartialGradientCoordinates
