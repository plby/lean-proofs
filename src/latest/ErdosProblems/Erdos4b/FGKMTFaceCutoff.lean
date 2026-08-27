/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos4b.FGKMTDimensionEnergy

/-!
# The actual inner face integral as a bounded smooth cutoff

The plateau identity uses the proved support width. It is the input
to the face-energy lower bound and the face version of the uniform
summation estimate.
-/

namespace Erdos4b.FGKMT

noncomputable section

theorem BoundedCutoff.sq {Φ : ℝ → ℝ} {K : ℝ} (hΦ : BoundedCutoff Φ K) :
    BoundedCutoff (fun t => Φ t ^ 2) (2 * K ^ 2) := by
  have hK := hΦ.constant_nonneg
  refine ⟨hΦ.smooth.pow 2, ?_, ?_⟩
  · intro t
    calc
      |Φ t ^ 2| = |Φ t| ^ 2 := abs_pow _ _
      _ ≤ K ^ 2 := pow_le_pow_left₀ (abs_nonneg _) (hΦ.value_bound t) 2
      _ ≤ _ := by nlinarith [sq_nonneg K]
  · intro t
    have hd : deriv (fun t => Φ t ^ 2) t = 2 * Φ t * deriv Φ t := by
      simpa only [Pi.pow_apply, Nat.cast_ofNat, Nat.reduceSub, pow_one] using!
        ((hΦ.smooth.differentiable_one t).hasDerivAt.pow 2).deriv
    rw [hd, abs_mul, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
    calc
      _ ≤ (2 * K) * K := mul_le_mul
        (mul_le_mul_of_nonneg_left (hΦ.value_bound t) (by norm_num))
        (hΦ.deriv_bound t) (abs_nonneg _) (by positivity)
      _ = _ := by ring

theorem dimensionProfileFactor_contDiff (k : ℕ) {n : ℕ∞} :
    ContDiff ℝ n (dimensionProfileFactor k) :=
  sieveFactor_contDiff _ _

theorem dimensionProfileFactor_nonneg (k : ℕ) (t : ℝ) : 0 ≤ dimensionProfileFactor k t :=
  sieveFactor_nonneg _ _ _

def dimensionProfileFirstMass (k : ℕ) : ℝ :=
  ∫ t in (0 : ℝ)..1, dimensionProfileFactor k t

def dimensionFaceCutoff (k : ℕ) : ℝ → ℝ :=
  cutoffAverage (dimensionProfileFactor k) sieveCutoff

theorem dimensionProfileFirstMass_nonneg (k : ℕ) : 0 ≤ dimensionProfileFirstMass k :=
  intervalIntegral.integral_nonneg_of_forall zero_le_one (dimensionProfileFactor_nonneg k)

theorem dimensionFaceCutoff_nonneg (k : ℕ) (u : ℝ) : 0 ≤ dimensionFaceCutoff k u := by
  rw [dimensionFaceCutoff, cutoffAverage_eq_interval]
  exact intervalIntegral.integral_nonneg_of_forall zero_le_one
    (fun t => mul_nonneg (dimensionProfileFactor_nonneg k t) (sieveCutoff_nonneg _))

theorem dimensionFaceCutoff_le_mass (k : ℕ) (u : ℝ) :
    dimensionFaceCutoff k u ≤ dimensionProfileFirstMass k := by
  have h := cutoffAverage_abs_le (dimensionProfileFactor_contDiff k (n := 1)).continuous
    (sieveCutoff_contDiff (n := 1)).continuous (fun t _ht => dimensionProfileFactor_nonneg k t)
    (fun s => by rw [abs_of_nonneg (sieveCutoff_nonneg s)]; exact sieveCutoff_le_one s) u
  exact (le_abs_self _).trans (by
    simpa only [one_mul, dimensionFaceCutoff, dimensionProfileFirstMass] using! h)

theorem dimensionFaceCutoff_eq_mass {k : ℕ} (hk : 0 < k) (hlog : 10000 ≤ Real.log k)
    {u : ℝ} (hu : u ≤ 4 / 5) : dimensionFaceCutoff k u = dimensionProfileFirstMass k := by
  have hb := profile_scales_bounds hk hlog
  rw [dimensionFaceCutoff, cutoffAverage_eq_interval, dimensionProfileFirstMass]
  apply intervalIntegral.integral_congr
  intro t _ht
  change dimensionProfileFactor k t * sieveCutoff (u + t) = dimensionProfileFactor k t
  by_cases htU : sieveProfileWidth k ≤ t
  · have hz : dimensionProfileFactor k t = 0 :=
      sieveFactor_zero_of_ge hb.2.1 htU (sieveProfileScale k)
    rw [hz, zero_mul]
  · rw [sieveCutoff_one_of_le (by linarith [hb.2.2.1]), mul_one]

theorem dimensionFaceCutoff_sq_bounds {k : ℕ} (hk : 0 < k) (hlog : 10000 ≤ Real.log k)
    {u : ℝ} (hu : 0 ≤ u) :
    dimensionProfileFirstMass k ^ 2 * (1 - (5 / 4) * u) ≤ dimensionFaceCutoff k u ^ 2 ∧
      dimensionFaceCutoff k u ^ 2 ≤ dimensionProfileFirstMass k ^ 2 := by
  constructor
  · by_cases hu' : u ≤ 4 / 5
    · rw [dimensionFaceCutoff_eq_mass hk hlog hu']
      nlinarith [mul_nonneg (sq_nonneg (dimensionProfileFirstMass k)) hu]
    · exact (mul_nonpos_of_nonneg_of_nonpos (sq_nonneg _) (by linarith)).trans (sq_nonneg _)
  · exact pow_le_pow_left₀ (dimensionFaceCutoff_nonneg k u) (dimensionFaceCutoff_le_mass k u) 2

theorem exists_dimensionFaceCutoff_sq_bounded :
    ∃ C : ℝ, 0 < C ∧ ∀ k : ℕ,
      BoundedCutoff (fun u => dimensionFaceCutoff k u ^ 2)
        (C * dimensionProfileFirstMass k ^ 2) := by
  obtain ⟨K, hK, hψ⟩ := exists_sieveCutoff_bounded
  have hK0 : 0 < K := zero_lt_one.trans_le hK
  refine ⟨2 * K ^ 2, by positivity, ?_⟩
  intro k
  have h := (hψ.average_mass (dimensionProfileFactor_contDiff k (n := 1)).continuous
    (fun t _ht => dimensionProfileFactor_nonneg k t)).sq
  convert h using 1 <;> dsimp only [dimensionFaceCutoff, dimensionProfileFirstMass]
  ring

end

end Erdos4b.FGKMT

#print axioms Erdos4b.FGKMT.dimensionFaceCutoff_eq_mass
#print axioms Erdos4b.FGKMT.exists_dimensionFaceCutoff_sq_bounded
