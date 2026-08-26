import ErdosProblems.Erdos547.ImprovedBalancing
import ErdosProblems.Erdos547.CompletionInterpolation
import ErdosProblems.Erdos547.BipartiteDirected
import ErdosProblems.Erdos547.BipartiteSaturation

/-!
# Completion of a prescribed allocation

The residual endpoint equations are solved once. Capped coefficients at
vertices of the first side interpolate between full residual coverage and
an allocation oriented from the accessible second side. This directly
proves all conclusions of the completion lemma, including full coverage of
the second side when the second skew is at most one.
-/

noncomputable section

namespace Erdos547.DPRS

open Finset SimpleGraph
open scoped BigOperators

theorem normalized_endpoint (γ a b M : ℝ) (hγ : 0 ≤ γ) (hM : 0 < M) :
    ((1 + γ) * a / M + γ * ((1 + γ) * b / M)) / (1 + γ) = (a + γ * b) / M := by
  have hden : 1 + γ ≠ 0 := by linarith
  field_simp [hden, ne_of_gt hM]

variable {V : Type*} [Fintype V] {G : SimpleGraph V}

theorem exists_matching_completion (μ : FractionalMatching G) (U W : Finset V)
    (hdis : Disjoint U W) (hruns : μ.RunsBetween U W) (w : EdgeWeights G) (c : V)
    (hW : ∀ u ∈ W, μ.load u ≤ w.weight c u) (a₁ a₂ b₁ b₂ : ℝ)
    (ha₁ : 0 < a₁) (ha₂ : 0 ≤ a₂) (hb₁ : 0 < b₁) (hb₂ : 0 ≤ b₂)
    (hlo : max a₁ a₂ + min b₁ b₂ ≤ μ.total)
    (hhi : μ.total ≤ min a₁ a₂ + max b₁ b₂) :
    ∃ σ : SkewMatching G (a₂ / a₁), ∃ τ : SkewMatching G (b₂ / b₁),
      PairDominated σ τ μ ∧ σ.total = a₁ + a₂ ∧
      max 0 (w.saturation μ.load c - σ.total) ≤ τ.total ∧
      (∀ u ∉ U, σ.outLoad u = 0) ∧ τ.Fits w c ∧
      (b₂ / b₁ ≤ 1 → ∀ u ∈ W, σ.load u + τ.load u = μ.load u) := by
  classical
  have hmin : 0 ≤ min b₁ b₂ := le_min hb₁.le hb₂
  have hM : 0 < μ.total := by linarith [le_max_left a₁ a₂]
  have hcross := hruns.crosses hdis
  let γ := b₂ / b₁
  have hγ : 0 ≤ γ := div_nonneg hb₂ hb₁.le
  have hden : 1 + γ ≠ 0 := by linarith
  obtain ⟨x, y, z, hx, hy, hz, he₁, he₂, hz₁, hz₂, hzsum, hzfull⟩ :=
    exists_completion_coefficients a₁ a₂ b₁ b₂ μ.total ha₁.le ha₂ hb₁ hb₂ hlo hhi
  let t := fun u ↦ min (w.weight c u) (μ.load u) / μ.load u
  have ht0 (u : V) : 0 ≤ t u := capped_ratio_nonneg (w.nonnegative c u) (μ.load_nonneg u)
  have ht1 (u : V) : t u ≤ 1 := capped_ratio_le_one (μ.load_nonneg u)
  have htmul (u : V) : t u * μ.load u = min (w.weight c u) (μ.load u) :=
    capped_ratio_mul (w.nonnegative c u) (μ.load_nonneg u)
  let p := (a₁ + a₂) / μ.total
  let f := fun u ↦ (1 + γ) * (t u * x) / μ.total
  let g := fun u ↦ (1 + γ) * (t u * y + (1 - t u) * z) / μ.total
  have hp : 0 ≤ p := div_nonneg (by linarith) hM.le
  have hf (u : V) : 0 ≤ f u := div_nonneg
    (mul_nonneg (by linarith) (mul_nonneg (ht0 u) hx)) hM.le
  have hg (u : V) : 0 ≤ g u := div_nonneg
    (mul_nonneg (by linarith) (add_nonneg (mul_nonneg (ht0 u) hy)
      (mul_nonneg (sub_nonneg.mpr (ht1 u)) hz))) hM.le
  have heA₁ : (p + (a₂ / a₁) * 0) / (1 + a₂ / a₁) = a₁ / μ.total := by
    simpa only [one_mul, sub_self, zero_mul, zero_div, mul_zero, add_zero] using
      proportional_endpoint a₁ a₂ μ.total 1 ha₁ ha₂ hM
  have heA₂ : (0 + (a₂ / a₁) * p) / (1 + a₂ / a₁) = a₂ / μ.total := by
    simpa only [zero_mul, zero_div, sub_zero, one_mul, zero_add] using
      proportional_endpoint a₁ a₂ μ.total 0 ha₁ ha₂ hM
  have heB₁ (u : V) : (f u + γ * g u) / (1 + γ) =
      (t u * x + γ * (t u * y + (1 - t u) * z)) / μ.total :=
    normalized_endpoint γ _ _ μ.total hγ hM
  have heB₂ (u : V) : (g u + γ * f u) / (1 + γ) =
      (t u * y + (1 - t u) * z + γ * (t u * x)) / μ.total :=
    normalized_endpoint γ _ _ μ.total hγ hM
  have hcL (u : V) : (p + (a₂ / a₁) * 0) / (1 + a₂ / a₁) +
      (f u + γ * g u) / (1 + γ) ≤ 1 := by
    rw [heA₁, heB₁]
    exact interpolated_endpoint_le a₁ μ.total γ x y z (t u) hM (ht1 u) he₁ hz₁
  have hcR (u : V) : (0 + (a₂ / a₁) * p) / (1 + a₂ / a₁) +
      (g u + γ * f u) / (1 + γ) ≤ 1 := by
    rw [heA₂, heB₂]
    exact interpolated_reverse_endpoint_le a₂ μ.total γ x y z (t u) hM (ht1 u) he₂ hz₂
  have hc (u v : V) :
      (μ.directedWeight U (fun _ ↦ p) (fun _ ↦ 0) u v +
        (a₂ / a₁) * μ.directedWeight U (fun _ ↦ p) (fun _ ↦ 0) v u) / (1 + a₂ / a₁) +
      (μ.directedWeight U f g u v + γ * μ.directedWeight U f g v u) / (1 + γ) ≤
        μ.weight u v := by
    rw [hcross.directedWeight_endpoint, hcross.directedWeight_endpoint, ← add_mul]
    apply (mul_le_mul_of_nonneg_right _ (μ.nonnegative u v)).trans_eq (one_mul _)
    by_cases hu : u ∈ U
    · simpa only [if_pos hu] using hcL u
    · simpa only [if_neg hu] using hcR v
  obtain ⟨σ, τ, hdom, hσ, hτ⟩ := exists_pair_of_endpoint_bounds μ (a₂ / a₁) γ
    (div_nonneg ha₂ ha₁.le) hγ
    (μ.directedWeight U (fun _ ↦ p) (fun _ ↦ 0)) (μ.directedWeight U f g)
    (μ.directedWeight_nonneg U _ _ (fun _ ↦ hp) (fun _ ↦ le_rfl))
    (μ.directedWeight_nonneg U f g hf hg) hc
  have hσtotal : σ.total = a₁ + a₂ := by
    change (∑ u, ∑ v, σ.weight u v) = _
    simp_rw [hσ]
    rw [μ.directedWeight_total]
    simp only [add_zero, ← Finset.mul_sum, hcross.sum_load_side]
    exact div_mul_cancel₀ _ (ne_of_gt hM)
  have hτtotal : τ.total = ∑ u ∈ U, (f u + g u) * μ.load u := by
    change (∑ u, ∑ v, τ.weight u v) = _
    simp_rw [hτ]
    exact μ.directedWeight_total U f g
  have htotal_lower : w.saturation μ.load c - σ.total ≤ τ.total := by
    rw [hruns.saturation_eq hdis w c hW, hσtotal, hτtotal]
    have hpwise (u : V) : (t u + 1 - (a₁ + a₂) / μ.total) * μ.load u ≤
        (f u + g u) * μ.load u := by
      apply mul_le_mul_of_nonneg_right _ (μ.load_nonneg u)
      change _ ≤ (1 + γ) * (t u * x) / μ.total +
        (1 + γ) * (t u * y + (1 - t u) * z) / μ.total
      rw [← add_div]
      exact interpolated_total_lower a₁ a₂ μ.total γ x y z (t u) hM (ht1 u) he₁ he₂ hzsum
    have hsum := Finset.sum_le_sum (fun u (_ : u ∈ U) ↦ hpwise u)
    have heq : (∑ u ∈ U, (t u + 1 - (a₁ + a₂) / μ.total) * μ.load u) =
        (∑ u ∈ U, min (w.weight c u) (μ.load u)) + μ.total - (a₁ + a₂) := by
      simp only [sub_mul, add_mul, one_mul, Finset.sum_sub_distrib, Finset.sum_add_distrib,
        htmul, ← Finset.mul_sum, hcross.sum_load_side, div_mul_cancel₀ _ (ne_of_gt hM)]
    rwa [heq] at hsum
  have hfit : τ.Fits w c := by
    intro u
    by_cases hu : u ∈ U
    · have hout : τ.outLoad u = (x / μ.total) * min (w.weight c u) (μ.load u) := by
        change (∑ v, τ.weight u v) / (1 + γ) = _
        simp_rw [hτ, hcross.directedWeight_of_mem f g hu]
        rw [← Finset.mul_sum]
        change f u * μ.load u / (1 + γ) = _
        calc
          _ = (x / μ.total) * (t u * μ.load u) := by
            dsimp [f]
            field_simp [hden, ne_of_gt hM]
          _ = _ := by rw [htmul]
      rw [hout]
      have hxM : x ≤ μ.total := by linarith [mul_nonneg hγ hy]
      have hx1 : x / μ.total ≤ 1 := (div_le_one hM).mpr hxM
      exact ((mul_le_mul_of_nonneg_right hx1
        (le_min (w.nonnegative c u) (μ.load_nonneg u))).trans_eq (one_mul _)).trans
        (min_le_left _ _)
    · exact ((τ.outLoad_le_load u).trans (hdom.right.load_le u)).trans
        (hruns.outside_load_le w c hW hu)
  refine ⟨σ, τ, hdom, hσtotal, max_le ?_ htotal_lower, ?_, hfit, ?_⟩
  · exact Finset.sum_nonneg fun u _ ↦ Finset.sum_nonneg fun v _ ↦ τ.nonnegative u v
  · intro u hu
    change (∑ v, σ.weight u v) / (1 + a₂ / a₁) = 0
    simp only [hσ, FractionalMatching.directedWeight, if_neg hu, zero_mul, ite_self,
      zero_add, Finset.sum_const_zero, zero_div]
  · intro hsmall u huW
    have hu : u ∉ U := fun hu ↦ Finset.disjoint_left.mp hdis hu huW
    have hendpoint (v : V) : σ.endpointWeight u v + τ.endpointWeight u v = μ.weight u v := by
      change (σ.weight u v + (a₂ / a₁) * σ.weight v u) / (1 + a₂ / a₁) +
        (τ.weight u v + γ * τ.weight v u) / (1 + γ) = _
      rw [hσ, hσ, hτ, hτ, hcross.directedWeight_endpoint, hcross.directedWeight_endpoint,
        if_neg hu, if_neg hu, ← add_mul]
      have he : (0 + (a₂ / a₁) * p) / (1 + a₂ / a₁) +
          (g v + γ * f v) / (1 + γ) = 1 := by
        rw [heA₂, heB₂]
        exact interpolated_reverse_endpoint_eq a₂ μ.total γ x y z (t v) hM he₂ (hzfull hsmall)
      rw [he, one_mul]
    rw [← σ.sum_endpointWeight, ← τ.sum_endpointWeight, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun v _ ↦ hendpoint v

end Erdos547.DPRS

#print axioms Erdos547.DPRS.exists_matching_completion
