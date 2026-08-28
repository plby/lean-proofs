import Wikipedia.HomotopyGroupsOfSpheres.QuaternionicCriticalEnergySpectrum

/-!
# A verified noncritical interval below an antipodal critical energy

Distinct values in the containing critical-energy lattice differ by at least
`8 * π²`. Thus the open interval of that length immediately below any actual
critical energy contains no critical polygon.
-/

open Set
open scoped Manifold ContDiff

namespace Wikipedia.HomotopyGroupsOfSpheres.QuaternionicColumns.Polygon

open NoExoticSixSphere.GLOrthonormalization VertexSpace

variable {n m : ℕ}

theorem noncritical_below_critical_energy (a b : symplecticSubgroup n)
    (τ : Fin (m + 2) → ℝ) (hτ : StrictMono τ)
    (hzero : τ 0 = 0) (hone : τ (Fin.last (m + 1)) = 1)
    (hanti : (a⁻¹ * b).val.val.val = -(1 : Vector (4 * n + 4) →L[ℝ] Vector (4 * n + 4)))
    (v : Space n m) (hv : v ∈ admissible a b m)
    (hcrit : mfderiv 𝓘(ℝ, Model n m) 𝓘(ℝ, ℝ) (energy a b τ) v = 0)
    (z : Space n m) (hz : z ∈ admissible a b m)
    (hlow : energy a b τ v - 8 * Real.pi ^ 2 < energy a b τ z)
    (hhigh : energy a b τ z < energy a b τ v) :
    mfderiv 𝓘(ℝ, Model n m) 𝓘(ℝ, ℝ) (energy a b τ) z ≠ 0 := by
  obtain ⟨r, hr⟩ := critical_energy_eq_pi_lattice a b τ hτ hzero hone hanti v hv hcrit
  intro hzcrit
  obtain ⟨q, hq⟩ := critical_energy_eq_pi_lattice a b τ hτ hzero hone hanti z hz hzcrit
  by_cases hqr : q < r
  · have hcast : (q : ℝ) + 1 ≤ r := by exact_mod_cast Nat.succ_le_of_lt hqr
    have hb : (((4 * n + 4 : ℕ) : ℝ) + 8 * ((q : ℝ) + 1)) * Real.pi ^ 2 ≤
        (((4 * n + 4 : ℕ) : ℝ) + 8 * (r : ℝ)) * Real.pi ^ 2 :=
      mul_le_mul_of_nonneg_right (by linarith) (sq_nonneg _)
    rw [hr, hq] at hlow
    nlinarith only [hb, hlow]
  · have hcast : (r : ℝ) ≤ q := by exact_mod_cast Nat.le_of_not_gt hqr
    have hb : (((4 * n + 4 : ℕ) : ℝ) + 8 * (r : ℝ)) * Real.pi ^ 2 ≤
        (((4 * n + 4 : ℕ) : ℝ) + 8 * (q : ℝ)) * Real.pi ^ 2 :=
      mul_le_mul_of_nonneg_right (by linarith) (sq_nonneg _)
    rw [hr, hq] at hhigh
    exact (not_lt_of_ge hb) hhigh

end Wikipedia.HomotopyGroupsOfSpheres.QuaternionicColumns.Polygon
