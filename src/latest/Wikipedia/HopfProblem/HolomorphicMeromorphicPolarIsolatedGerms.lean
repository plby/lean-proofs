import Wikipedia.HopfProblem.HolomorphicMeromorphicPolarIsolated
import Wikipedia.HopfProblem.AnalyticGermsFactorialCoordinateDivisionAlgebra

/-!
# Isolated common zeros of representatives of actual analytic germs

A linear combination equal to a coordinate power times a unit confines
common zeros to the coordinate axis. Nondivisibility of the second germ
by that coordinate rules out an identically vanishing axis restriction.
The resulting isolation statement holds for any analytic representatives
of the two given actual germs.
-/

open Set Filter Topology

namespace Wikipedia.HopfProblem.HolomorphicMeromorphic.PolarIsolated

open CuspNormalization.Germs CuspNormalization.Germs.CoordinateDivision

/-- An actual germ relation and coordinate nondivisibility isolate the
common zeros of any given analytic representatives. -/
theorem eventually_common_zero_eq_zero_of_germ_relation
    {P Q A C U : O₂} {n : ℕ} (hU : IsUnit U)
    (hrel : A * P + C * Q = firstCoordinateGerm ^ n * U)
    (hQ : ¬ firstCoordinateGerm ∣ Q)
    {p q : ℂ × ℂ → ℂ} (hp : AnalyticAt ℂ p 0) (hq : AnalyticAt ℂ q 0)
    (hP : ofAnalytic p hp = P) (hQrep : ofAnalytic q hq = Q) :
    ∀ᶠ z in 𝓝 (0 : ℂ × ℂ), p z = 0 → q z = 0 → z = 0 := by
  obtain ⟨a, ha, hA⟩ := exists_representative A
  obtain ⟨c, hc, hC⟩ := exists_representative C
  obtain ⟨u, hu, hUrep⟩ := exists_representative U
  have hu₀ : u 0 ≠ 0 := by
    have h := (isUnit_iff_eval_ne_zero U).mp hU
    rwa [← hUrep, eval_ofAnalytic] at h
  have hpow : ofAnalytic (fun z : ℂ × ℂ => z.1 ^ n) (analyticAt_fst.pow n) =
      firstCoordinateGerm ^ n := by
    apply CuspNormalization.Germs.ext
    change ((fun z : ℂ × ℂ => z.1 ^ n) : Filter.Germ (𝓝 (0 : ℂ × ℂ)) ℂ) =
      ((Prod.fst : ℂ × ℂ → ℂ) : Filter.Germ (𝓝 (0 : ℂ × ℂ)) ℂ) ^ n
    exact Filter.Germ.coe_pow _ n
  have hrep : (fun z => a z * p z + c z * q z) =ᶠ[𝓝 (0 : ℂ × ℂ)]
      (fun z => z.1 ^ n * u z) := by
    apply (ofAnalytic_eq_iff _ _ ((ha.mul hp).add (hc.mul hq))
      ((analyticAt_fst.pow n).mul hu)).mp
    calc
      _ = ofAnalytic a ha * ofAnalytic p hp + ofAnalytic c hc * ofAnalytic q hq := rfl
      _ = firstCoordinateGerm ^ n * ofAnalytic u hu := by
        rw [hA, hP, hC, hQrep, hUrep]
        exact hrel
      _ = _ := by rw [← hpow]; rfl
  have haxis : ¬ ((fun w : ℂ => q (0, w)) =ᶠ[𝓝 (0 : ℂ)] 0) := by
    intro hz
    apply hQ
    apply (axisRestriction_eq_zero_iff_dvd Q).mp
    rw [← hQrep, axisRestriction_ofAnalytic]
    exact (ofAnalytic_eq_zero_iff _ _).mpr hz
  exact eventually_common_zero_eq_zero hq hu hu₀ hrep haxis

/-- Actual analytic representatives can be chosen with the same named
germs and with no common zero near the origin except possibly the origin. -/
theorem exists_representatives_eventually_common_zero_eq_zero
    {P Q A C U : O₂} {n : ℕ} (hU : IsUnit U)
    (hrel : A * P + C * Q = firstCoordinateGerm ^ n * U)
    (hQ : ¬ firstCoordinateGerm ∣ Q) :
    ∃ (p q : ℂ × ℂ → ℂ) (hp : AnalyticAt ℂ p 0) (hq : AnalyticAt ℂ q 0),
      ofAnalytic p hp = P ∧ ofAnalytic q hq = Q ∧
        ∀ᶠ z in 𝓝 (0 : ℂ × ℂ), p z = 0 → q z = 0 → z = 0 := by
  obtain ⟨p, hp, hP⟩ := exists_representative P
  obtain ⟨q, hq, hQrep⟩ := exists_representative Q
  exact ⟨p, q, hp, hq, hP, hQrep,
    eventually_common_zero_eq_zero_of_germ_relation hU hrel hQ hp hq hP hQrep⟩

end Wikipedia.HopfProblem.HolomorphicMeromorphic.PolarIsolated
