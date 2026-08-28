import Wikipedia.NoExoticSixSphere.SardFlatEstimate
import Wikipedia.NoExoticSixSphere.RegularLevelNormalForm
import Mathlib.Analysis.Normed.Module.HahnBanach

/-!
# Local hypersurfaces containing a finite vanishing stratum

At a point where derivatives through order `k` vanish but the next one does
not, a scalar component of the `k`-th derivative has nonzero differential.
The proved inverse-function normal form straightens its zero set, which
contains the whole order-`k` vanishing locus locally.
-/

open scoped ContDiff Manifold
open Set Module

namespace NoExoticSixSphere.Sard

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem fderiv_eq_zero_of_mem_flatPoints {f : E → F} {k : ℕ} (hk : 1 ≤ k) {x : E}
    (hx : x ∈ flatPoints f k) : fderiv ℝ f x = 0 := by
  apply norm_eq_zero.mp
  rw [← norm_iteratedFDeriv_one, hx 1 le_rfl hk, norm_zero]

theorem flatPoints_one (f : E → F) : flatPoints f 1 = {x | fderiv ℝ f x = 0} := by
  ext x
  constructor
  · exact fderiv_eq_zero_of_mem_flatPoints le_rfl
  · intro hx j hj hj1
    have he : j = 1 := by omega
    subst j
    apply norm_eq_zero.mp
    rw [norm_iteratedFDeriv_one, hx, norm_zero]

theorem next_derivative_ne_zero {f : E → F} {k : ℕ} {x : E}
    (hx : x ∈ flatPoints f k) (hx' : x ∉ flatPoints f (k + 1)) :
    iteratedFDeriv ℝ (k + 1) f x ≠ 0 := by
  intro h
  apply hx'
  intro j hj hjk
  by_cases hj' : j ≤ k
  · exact hx j hj hj'
  · have he : j = k + 1 := by omega
    subst j
    exact h

theorem exists_flatStratumFunction {f : E → F} {U : Set E}
    (hU : IsOpen U) (hf : ContDiffOn ℝ ∞ f U) {k : ℕ} (hk : 1 ≤ k) {x : E}
    (hxU : x ∈ U) (hx : x ∈ flatPoints f k) (hx' : x ∉ flatPoints f (k + 1)) :
    ∃ g : E → ℝ, ContDiffOn ℝ ∞ g U ∧
      (∀ y ∈ flatPoints f k, g y = 0) ∧ Function.Surjective (fderiv ℝ g x) := by
  let J := iteratedFDeriv ℝ k f
  let D := fderiv ℝ J x
  have hD : D ≠ 0 := by
    intro h
    apply next_derivative_ne_zero hx hx'
    apply norm_eq_zero.mp
    rw [← norm_fderiv_iteratedFDeriv]
    change ‖D‖ = 0
    rw [h, norm_zero]
  have hv : ∃ v : E, D v ≠ 0 := by
    by_contra! h
    apply hD
    apply ContinuousLinearMap.ext
    intro v
    exact h v
  obtain ⟨v, hv⟩ := hv
  obtain ⟨ℓ, _, hℓ⟩ := exists_dual_vector ℝ (D v) (norm_ne_zero_iff.mpr hv)
  have hJ : ContDiffOn ℝ ∞ J U := by
    intro y hy
    exact ((hf.contDiffAt (hU.mem_nhds hy)).iteratedFDeriv_right (i := k) (m := ∞) (by
      exact_mod_cast (le_top : (⊤ : ℕ∞) + k ≤ ⊤))).contDiffWithinAt
  refine ⟨ℓ ∘ J, ℓ.contDiff.comp_contDiffOn hJ, ?_, ?_⟩
  · intro y hy
    change ℓ (iteratedFDeriv ℝ k f y) = 0
    rw [hy k hk le_rfl, map_zero]
  · rw [fderiv_comp x ℓ.differentiableAt
      ((hJ.contDiffAt (hU.mem_nhds hxU)).differentiableAt (by simp)), ℓ.fderiv]
    apply LinearMap.surjective (f := (ℓ.comp D).toLinearMap)
    intro h
    have hv0 : ℓ (D v) = 0 := congrArg (fun L : E →ₗ[ℝ] ℝ ↦ L v) h
    rw [hℓ] at hv0
    exact hv (norm_eq_zero.mp hv0)

variable [FiniteDimensional ℝ E]

theorem exists_flatStratumChart {f : E → F} {U : Set E}
    (hU : IsOpen U) (hf : ContDiffOn ℝ ∞ f U) {k : ℕ} (hk : 1 ≤ k) {x : E}
    (hxU : x ∈ U) (hx : x ∈ flatPoints f k) (hx' : x ∉ flatPoints f (k + 1)) :
    ∃ Φ : PartialDiffeomorph 𝓘(ℝ, E)
        𝓘(ℝ, ℝ × EuclideanSpace ℝ (Fin (finrank ℝ E - 1)))
        E (ℝ × EuclideanSpace ℝ (Fin (finrank ℝ E - 1))) ∞,
      x ∈ Φ.source ∧ Φ.source ⊆ U ∧
      (∀ y ∈ Φ.source ∩ flatPoints f k, (Φ y).1 = 0) ∧
      ∀ y ∈ Φ.source ∩ flatPoints f k, fderiv ℝ f y = 0 := by
  obtain ⟨g, hg, hzero, hreg⟩ := exists_flatStratumFunction hU hf hk hxU hx hx'
  have hd : 1 ≤ finrank ℝ E := by
    simpa using LinearMap.finrank_le_finrank_of_surjective
      (f := (fderiv ℝ g x).toLinearMap) hreg
  obtain ⟨Φ, hxΦ, hΦU, hfirst, _⟩ := exists_euclideanLevelNormalForm hU hxU hg hreg
    (finrank ℝ E - 1) (by simp only [finrank_self]; omega)
  exact ⟨Φ, hxΦ, hΦU, fun y hy ↦ (hfirst y).trans (hzero y hy.2),
    fun _ hy ↦ fderiv_eq_zero_of_mem_flatPoints hk hy.2⟩

end NoExoticSixSphere.Sard
