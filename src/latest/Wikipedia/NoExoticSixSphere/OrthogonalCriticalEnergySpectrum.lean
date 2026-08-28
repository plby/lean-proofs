import Wikipedia.NoExoticSixSphere.OrthogonalStationaryPolygon
import Wikipedia.NoExoticSixSphere.SkewAntipodalEnergySpectrum

/-!
# Discrete critical energies of actual antipodal polygons

Every critical polygon on a normalized partition realizes a single exponential,
so its actual energy belongs to the lattice `(n + 8q)π²`. Consequently the open
intervals between consecutive lattice values contain no critical points.
The lattice is only a containing set; no assertion of realizability is made.
-/

open Set
open scoped Manifold ContDiff

namespace NoExoticSixSphere.OrthogonalPolygon

open GLOrthonormalization CayleyTransform OrthogonalExponential OrthogonalVertexSpace

variable {n m : ℕ}

theorem critical_energy_eq_squareNorm (a b : OrthogonalOperators n)
    (τ : Fin (m + 2) → ℝ) (hτ : StrictMono τ)
    (hzero : τ 0 = 0) (hone : τ (Fin.last (m + 1)) = 1)
    (v : Space n m) (hv : v ∈ admissible a b m)
    (hcrit : mfderiv 𝓘(ℝ, Model n m) 𝓘(ℝ, ℝ) (energy a b τ) v = 0) :
    ∃ K : SkewOperators n, a * exp K = b ∧
      energy a b τ v = HilbertSchmidt.squareNorm (K : Vector n →L[ℝ] Vector n) := by
  obtain ⟨K, hend, hpath⟩ := critical_is_exponential a b τ hτ v hv hcrit
  simp only [hzero, hone, sub_zero, one_smul] at hend hpath
  refine ⟨K, hend, ?_⟩
  have he := path_energy_eq a b τ hτ hv
  rw [hzero, hone] at he
  have hcompare : OrthogonalPathEnergy.energy (fun t ↦ (path a b τ v t).1.1) 0 1 =
      OrthogonalPathEnergy.energy (fun t ↦ (a * exp (t • K)).1.1) 0 1 :=
    OrthogonalPathEnergy.energy_congr_Icc zero_le_one
      (fun t ht ↦ congrArg (fun q : OrthogonalOperators n ↦ q.1.1) (hpath t ht))
  rw [OrthogonalPathEnergy.energy_left_exp] at hcompare
  simpa only [sub_zero, one_mul] using he.symm.trans hcompare

theorem critical_energy_eq_pi_lattice (a b : OrthogonalOperators n)
    (τ : Fin (m + 2) → ℝ) (hτ : StrictMono τ)
    (hzero : τ 0 = 0) (hone : τ (Fin.last (m + 1)) = 1)
    (hanti : (a⁻¹ * b).1.1 = -(1 : Vector n →L[ℝ] Vector n))
    (v : Space n m) (hv : v ∈ admissible a b m)
    (hcrit : mfderiv 𝓘(ℝ, Model n m) 𝓘(ℝ, ℝ) (energy a b τ) v = 0) :
    ∃ q : ℕ, energy a b τ v = ((n : ℝ) + 8 * (q : ℝ)) * Real.pi ^ 2 := by
  obtain ⟨K, hend, he⟩ := critical_energy_eq_squareNorm a b τ hτ hzero hone v hv hcrit
  have hexpeq : exp K = a⁻¹ * b := by rw [← hend, inv_mul_cancel_left]
  have hexp : (exp K).1.1 = -(1 : Vector n →L[ℝ] Vector n) := by rwa [hexpeq]
  rw [he]
  exact SkewAntipodalSpectrum.squareNorm_eq_pi_lattice K hexp

theorem noncritical_of_energy_mem_gap (a b : OrthogonalOperators n)
    (τ : Fin (m + 2) → ℝ) (hτ : StrictMono τ)
    (hzero : τ 0 = 0) (hone : τ (Fin.last (m + 1)) = 1)
    (hanti : (a⁻¹ * b).1.1 = -(1 : Vector n →L[ℝ] Vector n))
    (v : Space n m) (hv : v ∈ admissible a b m) (q : ℕ)
    (hlow : ((n : ℝ) + 8 * (q : ℝ)) * Real.pi ^ 2 < energy a b τ v)
    (hhigh : energy a b τ v < ((n : ℝ) + 8 * ((q : ℝ) + 1)) * Real.pi ^ 2) :
    mfderiv 𝓘(ℝ, Model n m) 𝓘(ℝ, ℝ) (energy a b τ) v ≠ 0 := by
  intro hcrit
  obtain ⟨r, hr⟩ := critical_energy_eq_pi_lattice a b τ hτ hzero hone hanti v hv hcrit
  rcases le_or_gt r q with h | h
  · have hc : (r : ℝ) ≤ q := by exact_mod_cast h
    have he : ((n : ℝ) + 8 * (r : ℝ)) * Real.pi ^ 2 ≤
        ((n : ℝ) + 8 * (q : ℝ)) * Real.pi ^ 2 :=
      mul_le_mul_of_nonneg_right (by linarith) (sq_nonneg _)
    rw [hr] at hlow
    exact (not_lt_of_ge he) hlow
  · have hc : (q : ℝ) + 1 ≤ r := by exact_mod_cast h
    have he : ((n : ℝ) + 8 * ((q : ℝ) + 1)) * Real.pi ^ 2 ≤
        ((n : ℝ) + 8 * (r : ℝ)) * Real.pi ^ 2 :=
      mul_le_mul_of_nonneg_right (by linarith) (sq_nonneg _)
    rw [hr] at hhigh
    exact (not_lt_of_ge he) hhigh

end NoExoticSixSphere.OrthogonalPolygon
