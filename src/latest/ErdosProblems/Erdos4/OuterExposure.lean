import ErdosProblems.Erdos4.ExposureParameters

/-!
# Prime exposure on the concrete integer ray

The checked parameter theorem is applied to the actual source primes.
Small prime targets, whose anchors may leave the sampling interval, are
charged explicitly to the exceptional set. Outside that set, exposure
is the total actual tuple-hitting probability.
-/

open Filter
open scoped BigOperators Topology

namespace Erdos4.OuterExposure

open SmoothParameters ChebyshevIntervals OuterRay OuterAccuracy OuterPrimeSupply
open ExposureParameters

theorem exists_parameters {M η : ℝ} (hM : 0 < M) (hη : 0 < η) :
    ∃ (m : ℝ) (k K : ℕ), 1 ≤ m ∧ 0 < k ∧ k + 2 ≤ K ∧
      ∀ a D : ℕ, 1 ≤ D → ∀ᶠ r : ℕ in atTop,
        1 ≤ r ∧ K ≤ primaryFrontier a r ^ 5 ∧
        (∀ p ∈ sourcePrimes a r,
          (∑ n ∈ Finset.Icc 1 (length a D r),
            probability m k K (primaryFrontier a r) (length a D r) p n) = 1 ∧
          ∀ n, probability m k K (primaryFrontier a r) (length a D r) p n ≤
            (2 * Real.exp 1 ^ 2 / BoundedGaps.Maynard.coprimeHarmonicDensity (primorial K)) /
              (primaryFrontier a r : ℝ) ^ 30) ∧
        ∃ bad : Finset ℕ, bad ⊆ primeInterval (base a r) (length a D r) ∧
          (bad.card : ℝ) ≤ η * length a D r / Real.log (primaryFrontier a r : ℝ) +
            Nat.primeCounting (k * primorial K * frontier a r) ∧
          ∀ q ∈ primeInterval (base a r) (length a D r), q ∉ bad →
            M * frontier a r / length a D r ≤
              ∑ p : sourcePrimes a r,
                TupleCollisionMass.hitMass (AffineWeights.shift K : Fin k → ℕ) p
                  (length a D r) (probability m k K (primaryFrontier a r) (length a D r) p) q := by
  classical
  obtain ⟨c, hc, hsupply⟩ := exists_prime_supply
  obtain ⟨m, k, K, hm, hk, hK, hparams⟩ := ExposureParameters.exists_parameters hc hM hη
  refine ⟨m, k, K, hm, hk, hK, ?_⟩
  intro a D hD
  filter_upwards [eventually_ge_atTop 1, hsupply a,
    (tendsto_primary a).eventually hparams] with r hr hsrc hpar
  let X := frontier a r
  let Y := length a D r
  let H := k * primorial K
  let targets := primeInterval (base a r) Y
  let large := primeInterval (H * X) Y
  have hH : 1 ≤ H := Nat.mul_pos hk (primorial_pos K)
  have hXHX : X ≤ H * X := by simpa only [one_mul] using Nat.mul_le_mul_right X hH
  have hbHX : base a r ≤ H * X := (base_le_frontier a r).trans hXHX
  have hlarge : large ⊆ targets := by
    intro q hq
    have hh := mem_primeInterval.mp hq
    exact mem_primeInterval.mpr ⟨hh.1, hbHX.trans_lt hh.2.1, hh.2.2⟩
  have hX : primaryFrontier a r ^ 50 ≤ X := base_le_frontier a r
  have hY : primaryFrontier a r ^ 50 ≤ Y := hX.trans (frontier_le_length a hD hr)
  have hs : ∀ p ∈ sourcePrimes a r,
      p.Prime ∧ primaryFrontier a r ^ 5 < p ∧ p ≤ X := by
    intro p hp
    exact ⟨(source_range a r hp).1, source_gt_radius a r hp, (source_range a r hp).2.2⟩
  obtain ⟨hprob, badLarge, hbsub, hbcard, hgood⟩ :=
    hpar.2.2 X Y hX hY (sourcePrimes a r) large hsrc.2.1 hs
      (fun q hq => mem_primeInterval.mp hq)
  let small := targets.filter (fun q => q ≤ H * X)
  let bad := badLarge ∪ small
  have hsmall : small ⊆ (H * X).primesLE := by
    intro q hq
    have hh := Finset.mem_filter.mp hq
    exact Nat.mem_primesLE.mpr ⟨hh.2, (mem_primeInterval.mp hh.1).1⟩
  have hsmallcard : small.card ≤ Nat.primeCounting (H * X) := by
    simpa only [Nat.primesLE_card_eq_primeCounting] using Finset.card_le_card hsmall
  refine ⟨hr, hpar.2.1, hprob, bad, ?_, ?_, ?_⟩
  · exact Finset.union_subset (hbsub.trans hlarge) (Finset.filter_subset _ _)
  · have hh : (bad.card : ℝ) ≤ (badLarge.card : ℝ) + small.card := by
      exact_mod_cast Finset.card_union_le badLarge small
    exact hh.trans (add_le_add hbcard (by exact_mod_cast hsmallcard))
  · intro q hq hqbad
    have hnot : q ∉ badLarge ∧ q ∉ small := by
      simpa only [bad, Finset.mem_union, not_or] using hqbad
    have hqHX : H * X < q := by
      by_contra hn
      exact hnot.2 (Finset.mem_filter.mpr ⟨hq, by omega⟩)
    have hqY : q ≤ Y := (mem_primeInterval.mp hq).2.2
    have hqlarge : q ∈ large :=
      mem_primeInterval.mpr ⟨(mem_primeInterval.mp hq).1, hqHX, hqY⟩
    have hh := hgood q hqlarge hnot.1
    rw [ExposureParameters.exposure_eq_hitMass m k K (primaryFrontier a r) X Y
      (sourcePrimes a r) q (fun p hp => ⟨(hs p hp).1.pos, (hs p hp).2.2⟩) hqHX hqY] at hh
    exact hh

end Erdos4.OuterExposure
