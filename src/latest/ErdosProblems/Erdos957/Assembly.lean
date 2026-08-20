/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos957.Asymptotic
import ErdosProblems.Erdos957.CoreBound
import ErdosProblems.Erdos957.GeometryStatement
import ErdosProblems.Erdos957.LowHull
import ErdosProblems.Erdos957.Packing
import ErdosProblems.Erdos957.Scale

/-!
# Final assembly for Erdős problem 957

This module contains every step after the genuine geometric transfer
theorem.  Its sole unproved input is passed explicitly as a term of
`Erdos957GeometryCore.GeometryProducesTransfer`; no declaration in this file
asserts that proposition.

Once the geometric module supplies an unconditional theorem

```
geometryProducesTransfer : Erdos957GeometryCore.GeometryProducesTransfer
```

the final public declarations are the three one-line specializations
`erdos957`, `erdos957_asymptotic`, and `erdos957_filter` described at the end
of this file.
-/

open Metric
open scoped EuclideanGeometry RealInnerProductSpace SimpleGraph

namespace Erdos957

noncomputable section

open Erdos957GeometryCore

/-- The geometry layer's unit-distance graph is exactly the public
distance-`1` graph.  The explicit inequality in `distanceGraph` is redundant
because a pair at distance one cannot be equal. -/
theorem unitDistanceGraph_eq_distanceGraph_one (A : Finset Point) :
    unitDistanceGraph A = distanceGraph A 1 := by
  ext x y
  constructor
  · intro hxy
    refine ⟨?_, hxy⟩
    intro h
    subst y
    simpa using hxy
  · exact fun hxy ↦ hxy.2

/-- Configurations whose maximum/minimum ratio is at most `101` form a
bounded-cardinality branch. -/
theorem small_ratio_product_bound {A : Finset Point} {d₁ dₖ : ℝ}
    (hmin : IsMinimumDistance A d₁) (hmax : IsMaximumDistance A dₖ)
    (hratio : dₖ / d₁ ≤ 101) :
    (multiplicity A d₁ : ℝ) * multiplicity A dₖ ≤
      (41209 : ℝ) ^ 3 * A.card := by
  let N := normalizedSet A d₁ hmin.pos
  have hsep : ∀ x ∈ N, ∀ y ∈ N, x ≠ y → 1 ≤ dist x y := by
    intro x hx y hy hxy
    exact normalizedSet_one_separated hmin hx hy hxy
  have hdiam : ∀ x ∈ N, ∀ y ∈ N, dist x y ≤ 101 := by
    intro x hx y hy
    exact (dist_normalized_le_ratio_of_isMaximum hmin.pos hmax hx hy).trans
      hratio
  have hNcard : N.card ≤ 41209 :=
    Erdos957Packing.card_le_41209_of_pairwise_one_le_dist_of_dist_le
      N hsep hdiam
  have hAcard : A.card ≤ 41209 := by
    simpa [N] using hNcard
  have hminNat : multiplicity A d₁ ≤ A.card ^ 2 :=
    (multiplicity_le_choose A d₁).trans (Nat.choose_le_pow A.card 2)
  have hmaxNat : multiplicity A dₖ ≤ A.card ^ 2 :=
    (multiplicity_le_choose A dₖ).trans (Nat.choose_le_pow A.card 2)
  have hminReal : (multiplicity A d₁ : ℝ) ≤ (A.card : ℝ) ^ 2 := by
    exact_mod_cast hminNat
  have hmaxReal : (multiplicity A dₖ : ℝ) ≤ (A.card : ℝ) ^ 2 := by
    exact_mod_cast hmaxNat
  have hn0 : (0 : ℝ) ≤ A.card := by positivity
  have hnle : (A.card : ℝ) ≤ 41209 := by exact_mod_cast hAcard
  calc
    (multiplicity A d₁ : ℝ) * multiplicity A dₖ
        ≤ (A.card : ℝ) ^ 2 * (A.card : ℝ) ^ 2 :=
      mul_le_mul hminReal hmaxReal (by positivity) (by positivity)
    _ = (A.card : ℝ) * (A.card : ℝ) ^ 3 := by ring
    _ ≤ (A.card : ℝ) * (41209 : ℝ) ^ 3 := by
      exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hn0 hnle 3) hn0
    _ = (41209 : ℝ) ^ 3 * A.card := by ring

/-- The branch with at most two normalized hull vertices is already linear,
so cyclic hull geometry is needed only from three vertices onward. -/
theorem normalized_low_hull_product_bound {A : Finset Point} {d₁ dₖ : ℝ}
    (hmin : IsMinimumDistance A d₁) (hmax : IsMaximumDistance A dₖ)
    (hhull :
      (hullVertices (normalizedSet A d₁ hmin.pos)).card ≤ 2) :
    (multiplicity A d₁ : ℝ) * multiplicity A dₖ ≤ 6 * A.card := by
  let N := normalizedSet A d₁ hmin.pos
  have hsep : ∀ x ∈ N, ∀ y ∈ N, x ≠ y → 1 ≤ dist x y := by
    intro x hx y hy hxy
    exact normalizedSet_one_separated hmin hx hy hxy
  have hmaxN : IsMaximumDistance N (dₖ / d₁) :=
    (isMaximumDistance_normalizedSet_iff A d₁ hmin.pos dₖ).2 hmax
  have hbound :=
    Erdos957LowHull.multiplicity_product_real_le_six_mul_card_of_hull_card_le_two
      hsep hmaxN hhull
  have hminMult : multiplicity N 1 = multiplicity A d₁ := by
    simpa [N, hmin.pos.ne'] using multiplicity_normalizedSet A d₁ hmin.pos d₁
  have hmaxMult : multiplicity N (dₖ / d₁) = multiplicity A dₖ := by
    simpa [N] using multiplicity_normalizedSet A d₁ hmin.pos dₖ
  have hcard : N.card = A.card := by
    simpa [N] using normalizedSet_card A d₁ hmin.pos
  simpa [hminMult, hmaxMult, hcard] using hbound

/-- Hopf--Pannwitz bounds the maximum-distance multiplicity by the canonical
diameter-witness endpoint count. -/
private theorem maximumMultiplicity_le_witnessEndpoints
    {A : Finset Point} {r : ℝ} (hmax : IsMaximumDistance A r)
    {P : CyclicHullData A} (W : DiameterWitnessData P)
    (hWr : W.radius = r) :
    multiplicity A r ≤ W.D.card := by
  have hpair := Erdos957Diameter.maximumDistancePairCount_le_endpoints
    (Erdos957LowHull.maximumDistance_to_diameter hmax)
  calc
    multiplicity A r =
        Erdos957Diameter.maximumDistancePairCount A r :=
      Erdos957LowHull.multiplicity_eq_maximumDistancePairCount A r
    _ ≤ (Erdos957Diameter.maximumDistanceEndpoints A r).card := hpair
    _ = (distanceEndpoints A r).card := by
      rw [Erdos957LowHull.maximumDistanceEndpoints_eq_distanceEndpoints]
    _ = W.D.card := by
      simpa [hWr] using W.card_D_eq_distanceEndpoints.symm

/-- The sharp large-ratio product estimate follows from the single genuine
geometric theorem `GeometryProducesTransfer`. -/
theorem large_ratio_product_bound_of_geometry
    (hgeometry : GeometryProducesTransfer)
    {A : Finset Point} {d₁ dₖ : ℝ}
    (hmin : IsMinimumDistance A d₁) (hmax : IsMaximumDistance A dₖ)
    (hratio : 101 < dₖ / d₁)
    (hhull : 3 ≤
      (hullVertices (normalizedSet A d₁ hmin.pos)).card) :
    (multiplicity A d₁ : ℝ) * multiplicity A dₖ ≤
      (9 / 8 : ℝ) * (A.card : ℝ) ^ 2 + 1260 * (A.card : ℝ) := by
  let N := normalizedSet A d₁ hmin.pos
  let ρ := dₖ / d₁
  have hsep : IsOneSeparated N := by
    intro x hx y hy hxy
    exact normalizedSet_one_separated hmin hx hy hxy
  have hmaxN : IsMaximumDistance N ρ := by
    exact (isMaximumDistance_normalizedSet_iff A d₁ hmin.pos dₖ).2 hmax
  obtain ⟨R, ⟨L⟩⟩ :=
    Erdos957HullAngleLift.exists_radiallySorted_liftedCyclicHullOrder N hhull
  let P : CyclicHullData N :=
    Erdos957HullGeometryBridge.cyclicHullDataOfOrder R.order L
  let W : DiameterWitnessData P :=
    diameterWitnessDataOfMaximumDistance P (le_of_lt hratio) hmaxN
  obtain ⟨C⟩ := hgeometry N hsep R L W
  have C' : TransferCert (distanceGraph N 1) P.H
      (distinguishedVertices P W) (sourceVertices P W) := by
    simpa only [unitDistanceGraph_eq_distanceGraph_one] using C
  have hDH : W.D.card ≤ P.H.card := Finset.card_le_card W.endpoint_mem_hull
  have hDQ : W.D.card ≤ (distinguishedVertices P W).card + 2520 :=
    card_diameterEndpoints_le_card_distinguished_add_2520 P W
  have hmaxCount : multiplicity N ρ ≤ W.D.card := by
    apply maximumMultiplicity_le_witnessEndpoints hmaxN W
    rfl
  exact product_bound_of_normalized_transfer
    (H := P.H) (Q := distinguishedVertices P W) (B := sourceVertices P W)
    (D := W.D) hmin C' hDH hDQ hmaxCount

/-- The complete finite resolution, conditional only on the one explicitly
named geometric theorem. -/
theorem erdos957_linearErrorBound_of_geometry
    (hgeometry : GeometryProducesTransfer) : HasLinearErrorBound := by
  let C : ℝ := (41209 : ℝ) ^ 3 + 1260
  refine ⟨C, by positivity, ?_⟩
  intro A d₁ dₖ hmin hmax
  have hn : (0 : ℝ) ≤ A.card := by positivity
  by_cases hratio : dₖ / d₁ ≤ 101
  · have hsmall := small_ratio_product_bound hmin hmax hratio
    have hbase : (0 : ℝ) ≤ (9 / 8 : ℝ) * (A.card : ℝ) ^ 2 := by
      positivity
    calc
      (multiplicity A d₁ : ℝ) * multiplicity A dₖ
          ≤ (41209 : ℝ) ^ 3 * A.card := hsmall
      _ ≤ (9 / 8 : ℝ) * (A.card : ℝ) ^ 2 + C * A.card := by
        dsimp [C]
        nlinarith
  · have hlarge : 101 < dₖ / d₁ := lt_of_not_ge hratio
    by_cases hhull :
        (hullVertices (normalizedSet A d₁ hmin.pos)).card ≤ 2
    · have hlow := normalized_low_hull_product_bound hmin hmax hhull
      calc
        (multiplicity A d₁ : ℝ) * multiplicity A dₖ
            ≤ 6 * (A.card : ℝ) := hlow
        _ ≤ (9 / 8 : ℝ) * (A.card : ℝ) ^ 2 + C * A.card := by
          dsimp [C]
          nlinarith
    · have hhullThree :
          3 ≤ (hullVertices (normalizedSet A d₁ hmin.pos)).card := by
        omega
      have hsharp := large_ratio_product_bound_of_geometry
        hgeometry hmin hmax hlarge hhullThree
      calc
        (multiplicity A d₁ : ℝ) * multiplicity A dₖ
            ≤ (9 / 8 : ℝ) * (A.card : ℝ) ^ 2 +
                1260 * (A.card : ℝ) := hsharp
        _ ≤ (9 / 8 : ℝ) * (A.card : ℝ) ^ 2 + C * A.card := by
          dsimp [C]
          nlinarith

/-- Literal uniform epsilon formulation of Problem 957, conditional on the
geometric transfer theorem. -/
theorem erdos957_asymptotic_of_geometry
    (hgeometry : GeometryProducesTransfer) : HasNineEighthsAsymptoticBound :=
  linearErrorBound_implies_nineEighthsAsymptoticBound
    (erdos957_linearErrorBound_of_geometry hgeometry)

/-- Literal filter formulation of Problem 957, conditional on the geometric
transfer theorem. -/
theorem erdos957_filter_of_geometry
    (hgeometry : GeometryProducesTransfer) : HasNineEighthsFilterBound :=
  linearErrorBound_implies_nineEighthsFilterBound
    (erdos957_linearErrorBound_of_geometry hgeometry)

/-!
After `GeometryTransfer.lean` proves an unconditional theorem named
`geometryProducesTransfer`, the main module should expose exactly:

```
theorem erdos957 : HasLinearErrorBound :=
  erdos957_linearErrorBound_of_geometry geometryProducesTransfer

theorem erdos957_asymptotic : HasNineEighthsAsymptoticBound :=
  erdos957_asymptotic_of_geometry geometryProducesTransfer

theorem erdos957_filter : HasNineEighthsFilterBound :=
  erdos957_filter_of_geometry geometryProducesTransfer
```
-/

end

end Erdos957
