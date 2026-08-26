/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos4b.SourceDyadicPinnedConditions
import ErdosProblems.Erdos4b.GeneralFourierPinnedPrimeAsymptotic

/-!
# Uniform dyadic pinned prime-weight normalization

The residual prime, cofactor, allocated interval, and common divisor
cutoff all vary in the quantified limit. Only numeric range conditions
are imposed; the analytic prime-distribution estimates are proved.
-/

namespace Erdos4b.SmoothParameters

noncomputable section

open Filter
open scoped BigOperators Topology ContDiff

structure DyadicPinnedSourceRange (a D J : ℕ) (δ : ℝ) (r m p₀ A B : ℕ) : Prop where
  cofactor_pos : 0 < m
  cofactor_le : m ≤ D * fullResidualCofactorCutoff r
  pinned_prime : p₀.Prime
  pinned_lower : residualPrimeFrontier a r ≤ p₀
  pinned_upper : p₀ ≤ D * intervalLength a r / m
  residual_coprime : (m * p₀ - 1).Coprime (primorial (smoothFrontier r))
  interval_half : primaryFrontier a r ≤ 2 * A
  interval_order : A ≤ B
  interval_upper : B ≤ primaryFrontier a r
  interval_length : δ * (primaryFrontier a r : ℝ) / dyadicAmbientScale a r ^ J ≤ (B : ℝ) - A

theorem tendsto_dyadicPrimaryFrontier_atTop (a : ℕ) :
    Tendsto (primaryFrontier a) atTop atTop := by
  apply tendsto_atTop_mono _ tendsto_id
  intro r
  exact (self_le_primaryExponent a r).trans (primaryExponent a r).lt_two_pow_self.le

def dyadicPinnedSourceNormalizedWeight {K : ℕ} {I : Type*}
    (S : Finset I) (F : I → Fin K → ℝ → ℝ) (G : ℝ → ℝ) (h : Fin K)
    (a r m p₀ A B N : ℕ) : ℂ :=
  sourcePinnedPrimeNormalizedWeightSum S F G h (sourcePreSieveCutoff r) m p₀
    (smoothFrontier r) N A B (dyadicAmbientScale a r) (dyadicCompanionScale r)

theorem tendsto_dyadicPinnedSourceNormalizedWeight
    {α I : Type*} {l : Filter α} [l.IsCountablyGenerated] {K : ℕ}
    (S : Finset I) (F : I → Fin K → ℝ → ℝ) (G : ℝ → ℝ)
    (hFcompact : ∀ j i, HasCompactSupport (F j i)) (hFsmooth : ∀ j i, ContDiff ℝ ∞ (F j i))
    (hGcompact : HasCompactSupport G) (hGsmooth : ContDiff ℝ ∞ G)
    (hFsimplex : ∀ j ∈ S, ∀ u : Fin K → ℝ,
      (∀ i, 0 ≤ u i) → (∀ i, F j i (u i) ≠ 0) → (∑ i, u i) ≤ (1 : ℝ) / 10)
    (hFceiling : ∀ j ∈ S, ∀ i t, 0 ≤ t → F j i t ≠ 0 → t ≤ (1 : ℝ) / 10)
    (hGsupport : ∀ t, 0 ≤ t → G t ≠ 0 → t ≤ 1)
    (h : Fin K) (a D J : ℕ) {δ : ℝ} (hδ : 0 < δ)
    (r m p₀ A B N : α → ℕ) (hr : Tendsto r l atTop)
    (hdata : ∀ᶠ x in l, DyadicPinnedSourceRange a D J δ (r x) (m x) (p₀ x) (A x) (B x))
    (hN : ∀ᶠ x in l, jointSourceCommonPrimeBound S F G
      (dyadicAmbientScale a (r x)) (dyadicCompanionScale (r x)) ≤ N x) :
    Tendsto (fun x ↦ dyadicPinnedSourceNormalizedWeight S F G h a
      (r x) (m x) (p₀ x) (A x) (B x) (N x)) l
      (𝓝 ((sourcePinnedFirstVariationalIntegral S F h *
        sourcePinnedCompanionVariationalIntegral K G : ℝ) : ℂ)) := by
  have hcond : ∀ᶠ x in l, SourcePinnedNormalizationConditions K (sourcePreSieveCutoff (r x))
      (m x) (p₀ x) (smoothFrontier (r x)) (primaryFrontier a (r x)) (A x) (B x) J δ := by
    filter_upwards [hdata,
      hr.eventually (eventually_sourcePinnedNormalizationConditions_dyadic K a D J δ)] with x hx hc
    exact hc (m x) (p₀ x) (A x) (B x) hx.cofactor_pos hx.cofactor_le hx.pinned_prime
      hx.pinned_lower hx.pinned_upper hx.residual_coprime hx.interval_half hx.interval_order
      hx.interval_upper hx.interval_length
  exact tendsto_sourcePinnedPrimeNormalizedWeightSum S F G hFcompact hFsmooth hGcompact hGsmooth
    hFsimplex hFceiling hGsupport h J hδ (fun x ↦ sourcePreSieveCutoff (r x)) m p₀
    (fun x ↦ smoothFrontier (r x)) (fun x ↦ primaryFrontier a (r x)) A B N
    (tendsto_sourcePreSieveCutoff_atTop.comp hr) ((tendsto_dyadicPrimaryFrontier_atTop a).comp hr)
    hcond hN

theorem uniform_dyadicPinnedSourceNormalizedWeight_limit
    {I : Type*} {K : ℕ} (S : Finset I)
    (F : I → Fin K → ℝ → ℝ) (G : ℝ → ℝ)
    (hFcompact : ∀ j i, HasCompactSupport (F j i)) (hFsmooth : ∀ j i, ContDiff ℝ ∞ (F j i))
    (hGcompact : HasCompactSupport G) (hGsmooth : ContDiff ℝ ∞ G)
    (hFsimplex : ∀ j ∈ S, ∀ u : Fin K → ℝ,
      (∀ i, 0 ≤ u i) → (∀ i, F j i (u i) ≠ 0) → (∑ i, u i) ≤ (1 : ℝ) / 10)
    (hFceiling : ∀ j ∈ S, ∀ i t, 0 ≤ t → F j i t ≠ 0 → t ≤ (1 : ℝ) / 10)
    (hGsupport : ∀ t, 0 ≤ t → G t ≠ 0 → t ≤ 1)
    (h : Fin K) (a D J : ℕ) {δ ε : ℝ} (hδ : 0 < δ) (hε : 0 < ε) :
    ∀ᶠ r in atTop, ∀ m p₀ A B N : ℕ, DyadicPinnedSourceRange a D J δ r m p₀ A B →
      jointSourceCommonPrimeBound S F G (dyadicAmbientScale a r) (dyadicCompanionScale r) ≤ N →
      ‖dyadicPinnedSourceNormalizedWeight S F G h a r m p₀ A B N -
        ((sourcePinnedFirstVariationalIntegral S F h *
          sourcePinnedCompanionVariationalIntegral K G : ℝ) : ℂ)‖ < ε := by
  let T := {x : ℕ × ℕ × ℕ × ℕ × ℕ × ℕ //
    DyadicPinnedSourceRange a D J δ x.1 x.2.1 x.2.2.1 x.2.2.2.1 x.2.2.2.2.1 ∧
      jointSourceCommonPrimeBound S F G
        (dyadicAmbientScale a x.1) (dyadicCompanionScale x.1) ≤ x.2.2.2.2.2}
  let ρ : T → ℕ := fun x ↦ x.val.1
  let l : Filter T := Filter.comap ρ atTop
  have hr : Tendsto ρ l atTop := tendsto_comap
  have hlim := tendsto_dyadicPinnedSourceNormalizedWeight S F G hFcompact hFsmooth
    hGcompact hGsmooth hFsimplex hFceiling hGsupport h a D J hδ ρ
    (fun x ↦ x.val.2.1) (fun x ↦ x.val.2.2.1) (fun x ↦ x.val.2.2.2.1)
    (fun x ↦ x.val.2.2.2.2.1) (fun x ↦ x.val.2.2.2.2.2) hr
    (Eventually.of_forall fun x ↦ x.property.1) (Eventually.of_forall fun x ↦ x.property.2)
  have heps := (Metric.tendsto_nhds.mp hlim) ε hε
  obtain ⟨s, hs, hsub⟩ := Filter.mem_comap.mp heps
  obtain ⟨R, hR⟩ := Filter.mem_atTop_sets.mp hs
  apply eventually_atTop.mpr
  refine ⟨R, ?_⟩
  intro r hRr m p₀ A B N hdata hN
  let hx : T := ⟨(r, m, p₀, A, B, N), hdata, hN⟩
  have hp : ρ hx ∈ s := hR r hRr
  simpa only [Set.mem_ofPred_eq, dist_eq_norm, ρ, hx] using hsub hp

end

end Erdos4b.SmoothParameters
