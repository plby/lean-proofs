/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos4b.SourceDyadicConditions
import ErdosProblems.Erdos4b.GeneralFourierSourceAsymptotic

/-!
# Uniform physical normalization on the concrete dyadic ray

The limit is uniform over every even positive cofactor in the displayed
range and every auxiliary prime in the upper half of the primary range.
The interval multiplier is fixed but arbitrary.
-/

namespace Erdos4b.SmoothParameters

noncomputable section

open Filter
open scoped BigOperators Topology ContDiff

def dyadicSourceRange (a D r m q : ℕ) : Prop :=
  0 < m ∧ Even m ∧ m ≤ D * fullResidualCofactorCutoff r ∧ q.Prime ∧
    primaryFrontier a r ≤ 2 * q ∧ q ≤ primaryFrontier a r

def dyadicSourceNormalizedWeight {K : ℕ} {J : Type*}
    (S : Finset J) (F : J → Fin K → ℝ → ℝ) (G : ℝ → ℝ) (a D r m q : ℕ) : ℝ :=
  dyadicAmbientScale a r ^ K * dyadicCompanionScale r ^ K *
    sourceAnalyticPreSievedWeightSum (preSievedShifts K (sourcePreSieveCutoff r))
      (sourceAnalyticPrimeCutoff S F G (sourcePreSieveCutoff r)
        (dyadicAmbientScale a r) (dyadicCompanionScale r)) S
      (fun j h ↦ F j ((preSievedShiftEquiv K (sourcePreSieveCutoff r)).symm h)) G
      (dyadicAmbientScale a r) (dyadicCompanionScale r) (sourcePreSieveCutoff r) m q
      (D * intervalLength a r / m) /
    (((D * intervalLength a r / m : ℕ) : ℝ) *
      largeGapSingularSeries (preSievedShifts K (sourcePreSieveCutoff r)) m q (smoothFrontier r))

theorem tendsto_dyadicSourceNormalizedWeight
    {α J : Type*} {l : Filter α} [l.IsCountablyGenerated] {K : ℕ}
    (hK : 0 < K) (S : Finset J) (F : J → Fin K → ℝ → ℝ) (G : ℝ → ℝ)
    (hFcompact : ∀ j i, HasCompactSupport (F j i)) (hFsmooth : ∀ j i, ContDiff ℝ ∞ (F j i))
    (hGcompact : HasCompactSupport G) (hGsmooth : ContDiff ℝ ∞ G)
    (hFsimplex : ∀ j ∈ S, ∀ u : Fin K → ℝ,
      (∀ i, 0 ≤ u i) → (∀ i, F j i (u i) ≠ 0) → (∑ i, u i) ≤ (1 : ℝ) / 10)
    (hFceiling : ∀ j ∈ S, ∀ i t, 0 ≤ t → F j i t ≠ 0 → t ≤ (1 : ℝ) / 10)
    (hGsupport : ∀ t, 0 ≤ t → G t ≠ 0 → t ≤ 1)
    (a D : ℕ) (r m q : α → ℕ) (hr : Tendsto r l atTop)
    (hdata : ∀ᶠ x in l, dyadicSourceRange a D (r x) (m x) (q x)) :
    Tendsto (fun x ↦ dyadicSourceNormalizedWeight S F G a D (r x) (m x) (q x)) l
      (𝓝 (sourceFirstVariationalIntegral S F * sourceCompanionVariationalIntegral K G)) := by
  have hcond : ∀ᶠ x in l,
      SourceNormalizationConditions K (sourcePreSieveCutoff (r x)) (m x) (q x)
        (D * intervalLength a (r x) / m x)
        (dyadicAmbientScale a (r x)) (dyadicCompanionScale (r x)) := by
    filter_upwards [hdata, hr.eventually (eventually_sourceNormalizationConditions_dyadic K a D)]
      with x hx hcx
    exact hcx (m x) (q x) hx.1 hx.2.1 hx.2.2.1 hx.2.2.2.1 hx.2.2.2.2.1 hx.2.2.2.2.2
  exact tendsto_sourceAnalyticPreSievedWeightSum_real_normalized K hK S F G
    hFcompact hFsmooth hGcompact hGsmooth hFsimplex hFceiling hGsupport
    (fun x ↦ sourcePreSieveCutoff (r x)) m q (fun x ↦ D * intervalLength a (r x) / m x)
    (fun x ↦ smoothFrontier (r x)) (fun x ↦ dyadicAmbientScale a (r x))
    (tendsto_sourcePreSieveCutoff_atTop.comp hr)
    ((tendsto_dyadicAmbientScale_atTop a).comp hr) hcond

theorem uniform_dyadicSourceNormalizedWeight_limit
    {J : Type*} {K : ℕ} (hK : 0 < K) (S : Finset J)
    (F : J → Fin K → ℝ → ℝ) (G : ℝ → ℝ)
    (hFcompact : ∀ j i, HasCompactSupport (F j i)) (hFsmooth : ∀ j i, ContDiff ℝ ∞ (F j i))
    (hGcompact : HasCompactSupport G) (hGsmooth : ContDiff ℝ ∞ G)
    (hFsimplex : ∀ j ∈ S, ∀ u : Fin K → ℝ,
      (∀ i, 0 ≤ u i) → (∀ i, F j i (u i) ≠ 0) → (∑ i, u i) ≤ (1 : ℝ) / 10)
    (hFceiling : ∀ j ∈ S, ∀ i t, 0 ≤ t → F j i t ≠ 0 → t ≤ (1 : ℝ) / 10)
    (hGsupport : ∀ t, 0 ≤ t → G t ≠ 0 → t ≤ 1)
    (a D : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ r in atTop, ∀ m q : ℕ, dyadicSourceRange a D r m q →
      |dyadicSourceNormalizedWeight S F G a D r m q -
        sourceFirstVariationalIntegral S F * sourceCompanionVariationalIntegral K G| < ε := by
  let A := {x : ℕ × ℕ × ℕ // dyadicSourceRange a D x.1 x.2.1 x.2.2}
  let ρ : A → ℕ := fun x ↦ x.val.1
  let l : Filter A := Filter.comap ρ atTop
  have hr : Tendsto ρ l atTop := tendsto_comap
  have hdata : ∀ᶠ x in l, dyadicSourceRange a D (ρ x) x.val.2.1 x.val.2.2 :=
    Eventually.of_forall fun x ↦ x.property
  have hlim := tendsto_dyadicSourceNormalizedWeight hK S F G hFcompact hFsmooth
    hGcompact hGsmooth hFsimplex hFceiling hGsupport a D ρ
    (fun x ↦ x.val.2.1) (fun x ↦ x.val.2.2) hr hdata
  have heps := (Metric.tendsto_nhds.mp hlim) ε hε
  obtain ⟨s, hs, hsub⟩ := Filter.mem_comap.mp heps
  obtain ⟨R, hR⟩ := Filter.mem_atTop_sets.mp hs
  apply eventually_atTop.mpr
  refine ⟨R, ?_⟩
  intro r hRr m q hmq
  let hx : A := ⟨(r, m, q), hmq⟩
  have hp : ρ hx ∈ s := hR r hRr
  have h := hsub hp
  simpa only [Set.mem_ofPred_eq, Real.dist_eq, ρ, hx] using h

end

end Erdos4b.SmoothParameters
