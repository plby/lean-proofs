import ErdosProblems.Erdos4.OuterExposure
import ErdosProblems.Erdos4.OuterAtomDecay
import ErdosProblems.Erdos4.CoveringScalars

/-!
# Arbitrarily small conditional noncoverage on the outer ray

Choose a fixed profile with sufficiently large exposure. The preliminary
survival approximation is made uniformly accurate, and the actual atom
bound absorbs the collision term. The conclusion applies to all prime
targets outside the explicitly bounded exceptional set.
-/

open Filter
open scoped BigOperators Topology

namespace Erdos4.OuterNoncoverage

open SmoothParameters ChebyshevIntervals OuterRay OuterAccuracy OuterPrimeSupply
open ConditionalTupleMoments ConditionalCovering TupleCollisionMass

theorem exists_parameters (D : ℕ) (hD : 1 ≤ D) {β η : ℝ} (hβ : 0 < β) (hη : 0 < η) :
    ∃ k K : ℕ, 0 < k ∧ k + 2 ≤ K ∧ ∀ a : ℕ, ∀ᶠ r : ℕ in atTop,
      ∃ μ : ℕ → ℕ → ℝ,
        (∀ p ∈ sourcePrimes a r, ∀ n ∈ Finset.Icc 1 (length a D r), 0 ≤ μ p n) ∧
        ∃ bad : Finset ℕ, bad ⊆ primeInterval (base a r) (length a D r) ∧
          (bad.card : ℝ) ≤ η * length a D r / Real.log (primaryFrontier a r : ℝ) +
            Nat.primeCounting (k * primorial K * frontier a r) ∧
          ∀ q ∈ primeInterval (base a r) (length a D r), q ∉ bad →
            mean (fun l : randomPrimes a r => (l : ℕ)) q
              (miss (fun l : randomPrimes a r => (l : ℕ)) (AffineWeights.shift K : Fin k → ℕ)
                (sourcePrimes a r) (length a D r) μ q) ≤ β := by
  classical
  obtain ⟨c, C, hc, hC, hdensity⟩ := OuterDensity.exists_survival_density_bounds
  have hDR : (0 : ℝ) < D := by exact_mod_cast (show 0 < D by omega)
  let M := 8 * C * D / β
  have hM : 0 < M := by dsimp [M]; positivity
  let ε := min (1 / 4 : ℝ) (β / 12)
  have hε : 0 < ε := lt_min (by norm_num) (by positivity)
  have hε1 : ε < 1 := (min_le_left _ _).trans_lt (by norm_num)
  have hεβ : 3 * ε ≤ β / 4 := by
    have hh : ε ≤ β / 12 := min_le_right _ _
    linarith
  have hMβ : 2 * (C * D / M) = β / 4 := by dsimp [M]; field_simp; norm_num
  obtain ⟨m, k, K, _hm, hk, hK, hexposure⟩ := OuterExposure.exists_parameters hM hη
  let A := 2 * Real.exp 1 ^ 2 / BoundedGaps.Maynard.coprimeHarmonicDensity (primorial K)
  have hA : 0 < A := by
    have hh := FiberAsymptotic.density_pos (primorial_pos K)
    dsimp [A]
    positivity
  let B : ℝ := (k : ℝ) + (k : ℝ) ^ 2
  have hB : 0 < B := by
    have hh : (0 : ℝ) < k := by exact_mod_cast hk
    dsimp [B]
    positivity
  let L := B * D * A / (c ^ (2 * k - 2) * M)
  have hL : 0 < L := by dsimp [L]; positivity
  refine ⟨k, K, hk, hK, ?_⟩
  intro a
  filter_upwards [hexposure a D hD, hdensity a,
    eventually_random_accuracy a (k * primorial K) k hD hε,
    OuterAtomDecay.eventually_power_atom_small a (2 * k - 2 + 1) hL
      (by positivity : 0 < β / 2)] with r hexp hden hacc hatom
  let μ := ExposureParameters.probability m k K (primaryFrontier a r) (length a D r)
  have hμ0 : ∀ p ∈ sourcePrimes a r, ∀ n ∈ Finset.Icc 1 (length a D r), 0 ≤ μ p n := by
    intro p _hp n _hn
    exact ExposureParameters.probability_nonneg _ _ _ _ _ _ _
  obtain ⟨bad, hbsub, hbcard, hgood⟩ := hexp.2.2.2
  refine ⟨μ, hμ0, bad, hbsub, hbcard, ?_⟩
  intro q hq hqbad
  let ell : randomPrimes a r → ℕ := fun l => l
  let s : ℝ := (r : ℝ) * core r
  let τ := ∑ p : sourcePrimes a r,
    hitMass (AffineWeights.shift K : Fin k → ℕ) p (length a D r) (μ p) q
  let α := A / (primaryFrontier a r : ℝ) ^ 30
  have hrR : (0 : ℝ) < r := by exact_mod_cast hexp.1
  have hV : (0 : ℝ) < core r := by exact_mod_cast core_pos r
  have hs : 0 < s := mul_pos hrR hV
  have ht : (0 : ℝ) < primaryFrontier a r := by exact_mod_cast primaryFrontier_pos a r
  have hX : (0 : ℝ) < frontier a r := by exact_mod_cast frontier_pos a r
  have hτlow : M / (D * s) ≤ τ := by
    have heq : M * frontier a r / length a D r = M / (D * s) := by
      rw [OuterRay.length]
      push_cast
      dsimp [s]
      field_simp
    rw [← heq]
    exact hgood q hq hqbad
  have hτ : 0 < τ := (div_pos hM (mul_pos hDR hs)).trans_le hτlow
  have hsources : ∀ p ∈ sourcePrimes a r, p.Prime ∧ K < p ∧ k ≤ p := by
    intro p hp
    have hKp := hexp.2.1.trans_lt (source_gt_radius a r hp)
    exact ⟨(source_range a r hp).1, hKp, by omega⟩
  have hpoints : ∀ p ∈ sourcePrimes a r, ∀ n ∈ Finset.Icc 1 (length a D r),
      ∀ y ∈ AffineTuples.tuple (AffineWeights.shift K : Fin k → ℕ) p n,
        y ≤ extent a D (k * primorial K) r := by
    intro p hp n hn y hy
    obtain ⟨i, rfl⟩ := (AffineTuples.mem_tuple _ _ _ _).mp hy
    exact Nat.add_le_add (Finset.mem_Icc.mp hn).2
      (Nat.mul_le_mul (AffineWeights.shift_le_bound K i) (source_range a r hp).2.2)
  have hμ : ∀ p ∈ sourcePrimes a r, ∀ n ∈ Finset.Icc 1 (length a D r), μ p n ≤ α := by
    intro p hp n _hn
    exact (hexp.2.2.1 p hp).2 n
  have hsum : ∀ p ∈ sourcePrimes a r, ∑ n ∈ Finset.Icc 1 (length a D r), μ p n = 1 :=
    fun p hp => (hexp.2.2.1 p hp).1
  have hratio : UnitFourier.unitDensity ell / τ ≤ C * D / M :=
    CoveringScalars.exposure_ratio_le hC.le hDR hM hs hden.2 hτlow
  have hcollision : B * α / (UnitFourier.unitDensity ell ^ (2 * k - 2) * τ) ≤ β / 2 := by
    have hh := CoveringScalars.collision_ratio_le (2 * k - 2) hc hDR hM hs hden.1 hτlow
      hB.le (show 0 ≤ α by dsimp [α]; positivity)
    apply hh.trans
    have heq : (B * D / (c ^ (2 * k - 2) * M)) * (α * s ^ (2 * k - 2 + 1)) =
        L * ((r : ℝ) * core r) ^ (2 * k - 2 + 1) / (primaryFrontier a r : ℝ) ^ 30 := by
      dsimp [L, α, s]
      ring
    rw [heq]
    exact hatom
  have hraw := CoveringError.mean_miss_le_explicit ell (by omega : 1 ≤ k) K
    (sourcePrimes a r) (length a D r) (extent a D (k * primorial K) r) μ q hε.le hε1
    (show 0 ≤ α by dsimp [α]; positivity) hacc hsources hpoints hμ0 hμ hsum hτ
  change _ ≤ 3 * ε + 2 * UnitFourier.unitDensity ell / τ + B * α /
    (UnitFourier.unitDensity ell ^ (2 * k - 2) * τ) at hraw
  have htworatio : 2 * UnitFourier.unitDensity ell / τ ≤ β / 4 := by
    have hh := mul_le_mul_of_nonneg_left hratio (by norm_num : (0 : ℝ) ≤ 2)
    rw [hMβ] at hh
    simpa only [mul_div_assoc] using hh
  linarith

end Erdos4.OuterNoncoverage
