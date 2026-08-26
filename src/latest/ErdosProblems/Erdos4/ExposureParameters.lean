import ErdosProblems.Erdos4.WindowPrimeExposure
import ErdosProblems.Erdos4.ExposureConstants

/-!
# Fixed parameters giving arbitrarily large exposure

For any positive source-density constant, desired exposure and exceptional
density, choose the profile dimension and one fixed small-prime cutoff.
The conclusion is then uniform in both interval endpoints and both prime
sets. All constants are chosen before the outer variable tends to infinity.
-/

open Filter
open scoped BigOperators Topology

namespace Erdos4.ExposureParameters

open ArithmeticFibers

noncomputable def probability (m : ℝ) (k K t Y p n : ℕ) : ℝ :=
  WindowNormalization.probability (fun l : primeWindow K (t ^ 5) => (l : ℕ)) m (t ^ 5) Y
    (primorial K) (AffineWeights.shift K : Fin k → ℕ) p n

noncomputable def exposure (m : ℝ) (k K t Y : ℕ) (sources : Finset ℕ) (q : ℕ) : ℝ :=
  ExposureBounds.exposure (fun l : primeWindow K (t ^ 5) => (l : ℕ)) m (t ^ 5) Y
    (primorial K) (AffineWeights.shift K : Fin k → ℕ) sources q

theorem probability_nonneg (m : ℝ) (k K t Y p n : ℕ) : 0 ≤ probability m k K t Y p n :=
  WindowNormalization.probability_nonneg _ _ _ _ _ _ _ _

theorem exposure_eq_hitMass (m : ℝ) (k K t X Y : ℕ) (sources : Finset ℕ) (q : ℕ)
    (hs : ∀ p ∈ sources, 0 < p ∧ p ≤ X)
    (hq : k * primorial K * X < q) (hqY : q ≤ Y) :
    exposure m k K t Y sources q =
      ∑ p : sources, TupleCollisionMass.hitMass (AffineWeights.shift K : Fin k → ℕ)
        p Y (probability m k K t Y p) q := by
  classical
  change (∑ p : sources, ∑ j : Fin k, probability m k K t Y p
    (q - AffineWeights.shift K j * p)) = _
  apply Finset.sum_congr rfl
  intro p _hp
  apply TupleCollisionMass.anchor_sum_eq_hitMass _ (AffineTuples.shift_injective K)
    (hs p p.property).1 Y _ q
  · intro i
    exact (Nat.mul_le_mul (AffineWeights.shift_le_bound K i) (hs p p.property).2).trans hq.le
  · intro i
    exact AffineWeights.center_mem_Icc K X Y p q i (hs p p.property).2 hq hqY

theorem exists_parameters {c M η : ℝ} (hc : 0 < c) (hM : 0 < M) (hη : 0 < η) :
    ∃ (m : ℝ) (k K : ℕ), 1 ≤ m ∧ 0 < k ∧ k + 2 ≤ K ∧
      ∀ᶠ t : ℕ in atTop, 2 ≤ t ∧ K ≤ t ^ 5 ∧
        ∀ X Y : ℕ, t ^ 50 ≤ X → t ^ 50 ≤ Y → ∀ sources targets : Finset ℕ,
          c * X / Real.log t ≤ sources.card →
          (∀ p ∈ sources, p.Prime ∧ t ^ 5 < p ∧ p ≤ X) →
          (∀ q ∈ targets, q.Prime ∧ k * primorial K * X < q ∧ q ≤ Y) →
          (∀ p ∈ sources,
            (∑ n ∈ Finset.Icc 1 Y, probability m k K t Y p n) = 1 ∧
            ∀ n, probability m k K t Y p n ≤
              (2 * Real.exp 1 ^ 2 / BoundedGaps.Maynard.coprimeHarmonicDensity (primorial K)) /
                (t : ℝ) ^ 30) ∧
          ∃ bad : Finset ℕ, bad ⊆ targets ∧ (bad.card : ℝ) ≤ η * Y / Real.log t ∧
            ∀ q ∈ targets, q ∉ bad → M * X / Y ≤ exposure m k K t Y sources q := by
  classical
  obtain ⟨C, hC, hdensity⟩ := EulerDensityBounds.exists_uniform_density_upper
  let A := 2 * C * M / (5 * c)
  have hA : 0 < A := by dsimp [A]; positivity
  have hMA : M ≤ 5 * A * c / (2 * C) := by
    have heq : 5 * A * c / (2 * C) = M := by dsimp [A]; field_simp
    exact heq.ge
  obtain ⟨m, k, Kg, hm, hk, hKg, hgain⟩ :=
    EulerDensity.exists_arbitrary_principal_gain (A + 1)
  obtain ⟨Kn, hKn, hnorm⟩ := NormalizationAsymptotic.exists_eventual_probability_bounds hm k
  obtain ⟨δ, hδ, hδ1, hδsmall⟩ := ExposureConstants.exists_decay hc hη k
  obtain ⟨Kd, hKd⟩ := exists_nat_ge (20 * (k : ℝ) ^ 3 / δ)
  let K := max Kg (max Kn Kd)
  have hgK : Kg ≤ K := le_max_left _ _
  have hnK : Kn ≤ K := (le_max_left Kn Kd).trans (le_max_right Kg _)
  have hdK : Kd ≤ K := (le_max_right Kn Kd).trans (le_max_right Kg _)
  have hkK : k + 2 ≤ K := hKg.trans hgK
  have hlocal : 20 * (k : ℝ) ^ 3 ≤ δ * K := by
    have hh : 20 * (k : ℝ) ^ 3 / δ ≤ K := hKd.trans (by exact_mod_cast hdK)
    simpa only [mul_comm] using (div_le_iff₀ hδ).mp hh
  refine ⟨m, k, K, hm, hk, hkK, ?_⟩
  have hpow : Tendsto (fun t : ℕ => t ^ 5) atTop atTop :=
    tendsto_atTop_mono (fun t => Nat.le_pow (by norm_num : 0 < (5 : ℕ))) tendsto_id
  filter_upwards [eventually_ge_atTop K, hpow.eventually (hgain K hgK),
    hnorm K hnK, PrimeMeanSquare.eventually_good_cutoff] with t htK hpr hprob ht
  have hKR : K ≤ t ^ 5 := htK.trans (Nat.le_pow (by norm_num))
  refine ⟨ht.1, hKR, ?_⟩
  intro X Y hX hY sources targets hsource hsources htargets
  have hXpos : 0 < X := (pow_pos (by omega : 0 < t) 50).trans_le hX
  have hYpos : 0 < Y := (pow_pos (by omega : 0 < t) 50).trans_le hY
  have hXR : (0 : ℝ) < X := by exact_mod_cast hXpos
  have hYR : (0 : ℝ) < Y := by exact_mod_cast hYpos
  have hlog : 0 < Real.log (t : ℝ) := Real.log_pos (by exact_mod_cast ht.1)
  have hsourcepos : 0 < sources.card := by
    have hh : (0 : ℝ) < sources.card := (div_pos (mul_pos hc hXR) hlog).trans_le hsource
    exact_mod_cast hh
  have hnormSource (p : ℕ) (hp : p ∈ sources) :=
    hprob.2 Y hY p (hsources p hp).1 (hsources p hp).2.1
  refine ⟨fun p hp => ⟨(hnormSource p hp).2.2.1, (hnormSource p hp).2.2.2⟩, ?_⟩
  obtain ⟨bad, hbsub, hbcard, hbgood⟩ := WindowPrimeExposure.exists_exceptional_targets
    hm hk hkK ht.1 hKR hX hY ht.2 hδ.le hδ1 hlocal sources targets hsourcepos
    hsources htargets (fun p hp => ⟨(hnormSource p hp).1, (hnormSource p hp).2.1⟩) A hpr.2
  refine ⟨bad, hbsub, ?_, ?_⟩
  · exact hbcard.trans (ExposureConstants.exceptional_bound hc hlog hXR hYR.le
      (by positivity) hδsmall hsource)
  · intro q hq hgood
    apply le_trans _ (hbgood q hq hgood)
    have hd := hdensity K (t ^ 5) hKR hpr.1
    rw [Nat.cast_pow, Real.log_pow] at hd
    norm_num only [Nat.cast_ofNat] at hd
    exact ExposureConstants.exposure_bound hc hC hlog hXR hYR
      (FiberAsymptotic.density_pos (primorial_pos K)) (UnitFourier.unitDensity_pos _)
      hA.le hsource hd hMA

end Erdos4.ExposureParameters
