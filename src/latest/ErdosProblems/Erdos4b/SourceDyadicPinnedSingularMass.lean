/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos4b.GeneralFourierPinnedSingularMassLimit
import ErdosProblems.Erdos4b.SourceDyadicPinnedNormalization

/-!
# Uniform singular-weighted pinned mass on the concrete dyadic source ray

The cofactor, residual prime, allocated interval and common divisor
cutoff all vary uniformly. The interval multiplier is an arbitrary
fixed natural number, as required for arbitrary prime-gap constants.
-/

namespace Erdos4b.SmoothParameters

noncomputable section

open Filter
open scoped BigOperators Topology ContDiff

def dyadicPinnedSingularWeightedMass {K : ℕ} {I : Type*}
    (S : Finset I) (F : I → Fin K → ℝ → ℝ) (G : ℝ → ℝ) (h : Fin K)
    (a r m p₀ A B N : ℕ) : ℝ :=
  ∑ q ∈ auxiliaryPrimeInterval A B,
    pinnedSourceRealIntegerWeight S F G h
      (selectedFourierPrimeCutoff (fun p ↦ decide (sourcePreSieveCutoff r < p))
        (boundedFourierPrimes N)) (sourcePreSieveCutoff r) m p₀ q
      (dyadicAmbientScale a r) (dyadicCompanionScale r) /
        largeGapSingularSeries (preSievedShifts K (sourcePreSieveCutoff r)) m q (smoothFrontier r)

theorem uniform_dyadicPinnedSingularWeightedMass_lower
    {I : Type*} {K : ℕ} (S : Finset I)
    (F : I → Fin K → ℝ → ℝ) (G : ℝ → ℝ)
    (hFcompact : ∀ j i, HasCompactSupport (F j i)) (hFsmooth : ∀ j i, ContDiff ℝ ∞ (F j i))
    (hGcompact : HasCompactSupport G) (hGsmooth : ContDiff ℝ ∞ G)
    (hFsimplex : ∀ j ∈ S, ∀ u : Fin K → ℝ,
      (∀ i, 0 ≤ u i) → (∀ i, F j i (u i) ≠ 0) → (∑ i, u i) ≤ (1 : ℝ) / 10)
    (hFceiling : ∀ j ∈ S, ∀ i t, 0 ≤ t → F j i t ≠ 0 → t ≤ (1 : ℝ) / 10)
    (hGsupport : ∀ t, 0 ≤ t → G t ≠ 0 → t ≤ 1)
    (h : Fin K) (a D J : ℕ) {δ : ℝ} (hδ : 0 < δ)
    (hmain : 0 < sourcePinnedFirstVariationalIntegral S F h *
      sourcePinnedCompanionVariationalIntegral K G) :
    ∀ᶠ r in atTop, ∀ m p₀ A B N : ℕ, DyadicPinnedSourceRange a D J δ r m p₀ A B →
      jointSourceCommonPrimeBound S F G (dyadicAmbientScale a r) (dyadicCompanionScale r) ≤ N →
      smoothFrontier r ≤ N →
      (sourcePinnedFirstVariationalIntegral S F h * sourcePinnedCompanionVariationalIntegral K G) *
        residualCofactorLocalProduct (smoothFrontier r) m * (auxiliaryPrimeInterval A B).card /
          (4 * (dyadicAmbientScale a r ^ (K - 1) * dyadicCompanionScale r ^ (K - 1))) ≤
        dyadicPinnedSingularWeightedMass S F G h a r m p₀ A B N := by
  let T := {x : ℕ × ℕ × ℕ × ℕ × ℕ × ℕ //
    DyadicPinnedSourceRange a D J δ x.1 x.2.1 x.2.2.1 x.2.2.2.1 x.2.2.2.2.1 ∧
      jointSourceCommonPrimeBound S F G
        (dyadicAmbientScale a x.1) (dyadicCompanionScale x.1) ≤ x.2.2.2.2.2 ∧
      smoothFrontier x.1 ≤ x.2.2.2.2.2}
  let ρ : T → ℕ := fun x ↦ x.val.1
  let l : Filter T := Filter.comap ρ atTop
  have hr : Tendsto ρ l atTop := tendsto_comap
  have hcond : ∀ᶠ x : T in l, SourcePinnedNormalizationConditions K (sourcePreSieveCutoff (ρ x))
      x.val.2.1 x.val.2.2.1 (smoothFrontier (ρ x)) (primaryFrontier a (ρ x))
      x.val.2.2.2.1 x.val.2.2.2.2.1 J δ := by
    filter_upwards [hr.eventually (eventually_sourcePinnedNormalizationConditions_dyadic K a D J δ)]
      with x hc
    have hx := x.property.1
    exact hc _ _ _ _ hx.cofactor_pos hx.cofactor_le hx.pinned_prime hx.pinned_lower
      hx.pinned_upper hx.residual_coprime hx.interval_half hx.interval_order
      hx.interval_upper hx.interval_length
  have hbound := eventually_pinnedSingularWeightedPrimeMass_lower S F G
    hFcompact hFsmooth hGcompact hGsmooth hFsimplex hFceiling hGsupport h hmain J hδ
    (fun x : T ↦ sourcePreSieveCutoff (ρ x)) (fun x ↦ x.val.2.1) (fun x ↦ x.val.2.2.1)
    (fun x ↦ smoothFrontier (ρ x)) (fun x ↦ primaryFrontier a (ρ x))
    (fun x ↦ x.val.2.2.2.1) (fun x ↦ x.val.2.2.2.2.1) (fun x ↦ x.val.2.2.2.2.2)
    (tendsto_sourcePreSieveCutoff_atTop.comp hr) ((tendsto_dyadicPrimaryFrontier_atTop a).comp hr)
    hcond (Eventually.of_forall fun x ↦ x.property.2.1)
    (Eventually.of_forall fun x ↦ x.property.2.2)
  obtain ⟨s, hs, hsub⟩ := Filter.mem_comap.mp hbound
  obtain ⟨R, hR⟩ := Filter.mem_atTop_sets.mp hs
  apply eventually_atTop.mpr
  refine ⟨R, ?_⟩
  intro r hRr m p₀ A B N hdata hN hYN
  let hx : T := ⟨(r, m, p₀, A, B, N), hdata, hN, hYN⟩
  have hp : ρ hx ∈ s := hR r hRr
  have hresult := hsub (a := hx) hp
  change (_ : ℝ) ≤ _ at hresult
  dsimp only [ρ, hx] at hresult
  simpa only [dyadicPinnedSingularWeightedMass, dyadicAmbientScale, dyadicCompanionScale]
    using hresult

end

end Erdos4b.SmoothParameters
