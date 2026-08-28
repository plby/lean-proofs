import Wikipedia.HopfProblem.DegreeCollapseSignedQuadraticNativeChart
import Wikipedia.SmoothSixDPoincare.PartialDiffeomorphRestriction

/-!
# Explicit signed Morse charts for a scaled native cubic endpoint germ

Restrict to the actual equality neighborhood, use the explicit scalar cubic
endpoint coordinate, and multiply every resulting quadratic coordinate by
the positive square root of the scale. The constructed signed chart keeps
the scalar and every transverse sign, in the original manifold atlas.
-/

noncomputable section

open Set Function Filter Manifold
open scoped ContDiff Topology
open Wikipedia.SmoothSixDPoincare ManifoldMorse

namespace Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ} {m : ℕ}

theorem exists_signed_chart_of_scaled_cubic_germ
    (Φ : PartialDiffeomorph 𝓘(ℝ, Model m) 𝓘(ℝ, E) (Model m) M ∞)
    (ρ : Option (Fin m) ≃ Fin (Module.finrank ℝ E))
    (σ : Fin m → ℝ) (hσ : ∀ i, σ i = -1 ∨ σ i = 1)
    {a δ b : ℝ} (ha : 0 < a) (hδ : 0 < δ)
    (e : ℝ) (he : e = -1 ∨ e = 1)
    (hp : (e * a, (0 : Fin m → ℝ)) ∈ Φ.source)
    (hgerm : f ∘ Φ =ᶠ[𝓝 (e * a, 0)] fun z => b + δ * cubic σ (-(a ^ 2)) z) :
    ∃ c : SignedMorseChart (E := E) f (Φ (e * a, 0)),
      c.weights (ρ none) = e ∧ ∀ i, c.weights (ρ (some i)) = σ i := by
  obtain ⟨W, hWsub, hW, hpW⟩ := mem_nhds_iff.mp hgerm
  let T := PartialChart.restrictSource Φ hW
  have hpT : (e * a, (0 : Fin m → ℝ)) ∈ T.source := ⟨hp, hpW⟩
  have he2 : e ^ 2 = 1 := by rcases he with rfl | rfl <;> norm_num
  obtain ⟨P, hpP, hP0, -, hP⟩ := exists_endpoint_product_chart σ ha e he2
  let B : Model m ≃L[ℝ] Model m :=
    (LinearEquiv.smulOfNeZero ℝ (Model m) (Real.sqrt δ) (Real.sqrt_pos.mpr hδ).ne').toContinuousLinearEquiv
  let C := (T.symm.trans P).trans B.toDiffeomorph.toPartialDiffeomorph
  have hTinv : T.symm (Φ (e * a, 0)) = (e * a, 0) := T.left_inv' hpT
  have hpC : Φ (e * a, 0) ∈ C.source := by
    change (Φ (e * a, 0) ∈ T.target ∧ T.symm (Φ (e * a, 0)) ∈ P.source) ∧ _
    exact ⟨⟨T.map_source' hpT, hTinv.symm ▸ hpP⟩, mem_univ _⟩
  have hC0 : C (Φ (e * a, 0)) = 0 := by
    change B (P (T.symm (Φ (e * a, 0)))) = 0
    rw [hTinv, hP0, map_zero]
  have hvalue : f (Φ (e * a, 0)) = b + δ * cubic σ (-(a ^ 2)) (e * a, 0) :=
    hgerm.self_of_nhds
  have hscale (z : Model m) :
      e * (B z).1 ^ 2 + ∑ i, σ i * (B z).2 i ^ 2 =
        δ * (e * z.1 ^ 2 + ∑ i, σ i * z.2 i ^ 2) := by
    change e * (Real.sqrt δ * z.1) ^ 2 +
      (∑ i, σ i * (Real.sqrt δ * z.2 i) ^ 2) = _
    simp only [mul_pow, Real.sq_sqrt hδ.le]
    rw [mul_add, Finset.mul_sum]
    congr 1
    · ring
    · apply Finset.sum_congr rfl
      intro i _
      ring
  apply exists_signed_chart_of_split_quadratic C hpC hC0 ρ e σ he hσ
  intro y hy
  have hyT : y ∈ T.target := hy.1.1
  have hzT := T.map_target' hyT
  have hzP : T.symm y ∈ P.source := hy.1.2
  have hfy : f y = b + δ * cubic σ (-(a ^ 2)) (T.symm y) := by
    have hh := hWsub hzT.2
    change f (T (T.symm y)) = b + δ * cubic σ (-(a ^ 2)) (T.symm y) at hh
    have hr : T (T.symm y) = y := T.right_inv' hyT
    rw [hr] at hh
    exact hh
  change f y = f (Φ (e * a, 0)) + e * (B (P (T.symm y))).1 ^ 2 +
    ∑ i, σ i * (B (P (T.symm y))).2 i ^ 2
  rw [hfy, hvalue, hP (T.symm y) hzP]
  have hs := hscale (P (T.symm y))
  linarith

end Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation
