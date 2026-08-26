import ErdosProblems.Erdos4.PrincipalLowerBound
import ErdosProblems.Erdos4.ReciprocalTail

/-!
# Choosing the fixed parameters for principal gain

The profile dimension, reciprocal-mass threshold, and lower prime cutoff
are chosen before the outer cutoff tends to infinity. The actual
principal forms inherit arbitrary gain times their Euler density and
logarithm, with at most one unit of coefficient energy lost in the
projection comparison.
-/

open Filter
open scoped BigOperators Topology

namespace Erdos4.PrincipalGain

open PrimitiveProfile ArithmeticFibers DivisorCoefficients RestrictedProductNorm
open PrincipalLowerBound CoefficientMass

theorem exists_profile_parameters (M : ℝ) :
    ∃ (m : ℝ) (k : ℕ) (η : ℝ), 1 ≤ m ∧ 0 < k ∧ 0 < η ∧
      ∀ t : Fin k → ℝ, (∀ i, 0 ≤ t i) → (∑ i, t i) ≤ 1 →
        2 * M + (3 * η) * k / profile m k 1 ≤
          ∑ j, primitive m k (1 - (∑ i, t i) + t j) / profile m k (t j) := by
  obtain ⟨m, k, hm, hk, hgain⟩ := exists_arbitrary_gain (2 * M + 1)
  have hkp : (0 : ℝ) < k := by exact_mod_cast hk
  have hg : 0 < profile m k 1 := profile_pos (by linarith) hkp.le (by norm_num)
  let η : ℝ := profile m k 1 / (6 * k)
  have hη : 0 < η := div_pos hg (by positivity)
  refine ⟨m, k, η, hm, hk, hη, ?_⟩
  intro t ht hS
  have herr : (3 * η) * k / profile m k 1 = 1 / 2 := by
    dsimp [η]
    field_simp
    ring
  rw [herr]
  have hh := hgain t ht hS
  linarith

theorem exists_prime_cutoff {k : ℕ} (hk : 0 < k) {η : ℝ} (hη : 0 < η) :
    ∃ K : ℕ, k + 2 ≤ K ∧ ∀ S : Finset ℕ, (∀ p ∈ S, K < p) →
      (k : ℝ) * (∑ p ∈ S, (((p : ℝ) - 1)⁻¹) ^ 2) ≤ η / 2 ∧
      10 * (k : ℝ) ^ 3 * (∑ p ∈ S, 1 / (p : ℝ) ^ 2) ≤ 1 := by
  have hkp : (0 : ℝ) < k := by exact_mod_cast hk
  have hsmall : 0 < min (η / (2 * k)) (1 / (10 * (k : ℝ) ^ 3)) :=
    lt_min (by positivity) (by positivity)
  obtain ⟨K₀, _hK₀, htail⟩ := ReciprocalTail.exists_reciprocal_square_cutoff hsmall
  refine ⟨max K₀ (k + 2), le_max_right _ _, ?_⟩
  intro S hS
  have hh := htail S (fun p hp => lt_of_le_of_lt (le_max_left _ _) (hS p hp))
  have hfirst := (le_div_iff₀ (by positivity : (0 : ℝ) < 2 * k)).mp
    (hh.1.le.trans (min_le_left _ _))
  have hsecond := (le_div_iff₀ (by positivity : (0 : ℝ) < 10 * (k : ℝ) ^ 3)).mp
    (hh.2.le.trans (min_le_right _ _))
  constructor <;> nlinarith

/-- This conclusion concerns the actual principal deletion forms, with
all its profile and cutoff parameters chosen unconditionally. -/
theorem exists_eventual_principal_lower {M : ℝ} (hM : 0 ≤ M) :
    ∃ (m : ℝ) (k K₀ : ℕ), 1 ≤ m ∧ 0 < k ∧ k + 2 ≤ K₀ ∧
      ∀ K : ℕ, K₀ ≤ K → ∀ᶠ R : ℕ in atTop, 2 ≤ R ∧
        M * UnitFourier.unitDensity (fun p : primeWindow K R => (p : ℕ)) *
          BoundedGaps.Maynard.coprimeHarmonicDensity (primorial K) * Real.log R *
          energy (coefficient (k := k) m R (fun p : primeWindow K R => (p : ℕ))) -
          energy (coefficient (k := k) m R (fun p : primeWindow K R => (p : ℕ))) ≤
        ∑ j : Fin k, restrictedForm (fun p : primeWindow K R => (p : ℝ))
          (fun s => ∏ p, LocalCharacterMatrix.deletionMask j (s p))
          (coefficient m R (fun p : primeWindow K R => (p : ℕ)))
          (coefficient m R (fun p : primeWindow K R => (p : ℕ))) := by
  obtain ⟨m, k, η, hm, hk, hη, hgain⟩ := exists_profile_parameters M
  obtain ⟨K₀, hK₀, htail₀⟩ := exists_prime_cutoff hk hη
  refine ⟨m, k, K₀, hm, hk, hK₀, ?_⟩
  intro K hK₀K
  have hK : k + 2 ≤ K := hK₀.trans hK₀K
  have htail : ∀ S : Finset ℕ, (∀ p ∈ S, K < p) →
      (k : ℝ) * (∑ p ∈ S, (((p : ℝ) - 1)⁻¹) ^ 2) ≤ η / 2 ∧
      10 * (k : ℝ) ^ 3 * (∑ p ∈ S, 1 / (p : ℝ) ^ 2) ≤ 1 := by
    intro S hS
    exact htail₀ S (fun p hp => lt_of_le_of_lt hK₀K (hS p hp))
  filter_upwards [FiberAsymptotic.eventually_fiber_lower hm k K hη hη.le] with R hR
  refine ⟨hR.1, ?_⟩
  let ell : primeWindow K R → ℕ := fun p => p
  let N := energy (coefficient (k := k) m R ell)
  let L := BoundedGaps.Maynard.coprimeHarmonicDensity (primorial K) * Real.log R
  have hN : 0 ≤ N := energy_nonneg _
  have hL : 0 ≤ L := mul_nonneg (FiberAsymptotic.density_pos (primorial_pos K)).le
    (Real.log_natCast_nonneg R)
  have hell : ∀ p, k + 2 ≤ ell p := by
    intro p
    exact hK.trans (mem_primeWindow.mp p.property).2.1.le
  have hell2 : ∀ p, 2 ≤ ell p := fun p => by have := hell p; omega
  have hV := unitDensity_nonneg ell (fun p => by have := hell p; omega)
  have htailR := htail (primeWindow K R) (fun p hp => (mem_primeWindow.mp hp).2.1)
  have hshift : (k : ℝ) * (∑ p : primeWindow K R, (((ell p : ℝ) - 1)⁻¹) ^ 2) ≤ η / 2 := by
    simpa only [ell, Finset.sum_coe_sort (primeWindow K R)
      (fun p : ℕ => (((p : ℝ) - 1)⁻¹) ^ 2)] using htailR.1
  have herr : 10 * (k : ℝ) ^ 3 * (∑ p : primeWindow K R, 1 / (ell p : ℝ) ^ 2) ≤ 1 := by
    simpa only [ell, Finset.sum_coe_sort (primeWindow K R)
      (fun p : ℕ => 1 / (p : ℝ) ^ 2)] using htailR.2
  have hbad : (N * k * ∑ p, (((ell p : ℝ) - 1)⁻¹) ^ 2) / η ≤ N / 2 := by
    apply (div_le_iff₀ hη).mpr
    have hh := mul_le_mul_of_nonneg_left hshift hN
    nlinarith
  have hfiber : ∀ a : primeWindow K R → Option (Fin k), totalDivisor ell a ≤ R →
      reciprocalMass ell a ≤ η → ∀ j : Fin k,
      L * (primitive m k (1 - (∑ i, CutoffSimplex.coordinate R ell a i) +
        CutoffSimplex.coordinate R ell a j) - 3 * η) ≤ IdealAction.fiberSum m R ell j a := by
    intro a ha hmass j
    have hh := hR.2 j a ha hmass
    convert hh using 1 <;> dsimp [L, ell] <;> ring
  have hideal := sum_forms_lower hm hR.1 ell hell2 hL (by positivity : 0 ≤ 3 * η)
    (by positivity : 0 ≤ 2 * M) hη hgain hfiber
  have hideal' : UnitFourier.unitDensity ell * L * M * N ≤
      ∑ j : Fin k, ProjectionSliceBound.form (fun p => IdealProjection.normal (ell p : ℝ) j)
        (coefficient m R ell) (coefficient m R ell) := by
    apply le_trans _ hideal
    have hh := mul_le_mul_of_nonneg_left hbad (mul_nonneg (mul_nonneg hV hL) hM)
    change _ ≤ UnitFourier.unitDensity ell * L * (2 * M) * (N - _)
    nlinarith
  have hcompare := Finset.sum_le_sum (s := (Finset.univ : Finset (Fin k)))
    (fun j _hj => ProductProjectionComparison.ideal_form_sub_error_le_true hm hR.1 ell hell j)
  rw [Finset.sum_sub_distrib] at hcompare
  have herror : (∑ j : Fin k, N * ∑ p, 10 * (k : ℝ) ^ 2 / (ell p : ℝ) ^ 2) ≤ N := by
    have hh := mul_le_mul_of_nonneg_left herr hN
    calc
      _ = N * (10 * (k : ℝ) ^ 3 * ∑ p, 1 / (ell p : ℝ) ^ 2) := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        have heq : (∑ p, 10 * (k : ℝ) ^ 2 / (ell p : ℝ) ^ 2) =
            10 * (k : ℝ) ^ 2 * ∑ p, 1 / (ell p : ℝ) ^ 2 := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro p _hp
          ring
        rw [heq]
        ring
      _ ≤ N := by simpa only [mul_one] using hh
  change M * UnitFourier.unitDensity ell *
    BoundedGaps.Maynard.coprimeHarmonicDensity (primorial K) * Real.log R * N - N ≤ _
  dsimp [L] at hideal'
  linarith

end Erdos4.PrincipalGain
