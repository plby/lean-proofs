import Wikipedia.NoExoticSixSphere.SkewAntipodalMinimum
import Mathlib.Algebra.Ring.Parity

/-!
# A discrete lattice containing the antipodal exponential energies

Each Gram eigenvalue is an odd square times `π²`. Summing shows that every
antipodal generator has energy `(n + 8q)π²` for a natural number `q`. This is a
containing lattice: the theorem does not assert that every such value occurs.
-/

namespace NoExoticSixSphere.SkewAntipodalSpectrum

open GLOrthonormalization CayleyTransform HilbertSchmidt SkewSpectralPlane
  OrthogonalExponential

variable {n : ℕ}

theorem gram_eigenvalue_eq_pi_lattice (K : SkewOperators n)
    (hexp : (exp K).1.1 = -(1 : Vector n →L[ℝ] Vector n))
    {μ : ℝ} {x : Vector n} (hn : ‖x‖ = 1) (hx : gram K x = μ • x) :
    ∃ q : ℕ, μ = (1 + 8 * (q : ℝ)) * Real.pi ^ 2 := by
  obtain ⟨r, hr⟩ := gram_eigenvalue_odd_pi K hexp hn hx
  obtain ⟨q, hq⟩ := Nat.two_dvd_mul_add_one r
  have hqr : (r : ℝ) * ((r : ℝ) + 1) = 2 * (q : ℝ) := by exact_mod_cast hq
  refine ⟨q, ?_⟩
  calc
    μ = ((2 * (r : ℝ) + 1) * Real.pi) ^ 2 := hr
    _ = (1 + 4 * ((r : ℝ) * ((r : ℝ) + 1))) * Real.pi ^ 2 := by ring
    _ = (1 + 8 * (q : ℝ)) * Real.pi ^ 2 := by rw [hqr]; ring

theorem squareNorm_eq_pi_lattice (K : SkewOperators n)
    (hexp : (exp K).1.1 = -(1 : Vector n →L[ℝ] Vector n)) :
    ∃ q : ℕ, squareNorm (K : Vector n →L[ℝ] Vector n) =
      ((n : ℝ) + 8 * (q : ℝ)) * Real.pi ^ 2 := by
  let hS := gram_isSymmetric K
  let b := hS.eigenvectorBasis finrank_euclideanSpace_fin
  let μ := hS.eigenvalues finrank_euclideanSpace_fin
  have hex (i : Fin n) : ∃ q : ℕ, μ i = (1 + 8 * (q : ℝ)) * Real.pi ^ 2 :=
    gram_eigenvalue_eq_pi_lattice K hexp (b.orthonormal.norm_eq_one i)
      (hS.apply_eigenvectorBasis _ i)
  choose q hq using hex
  refine ⟨∑ i, q i, ?_⟩
  rw [squareNorm_eq_eigenvalue_sum]
  change (∑ i : Fin n, μ i) = _
  simp_rw [hq]
  rw [← Finset.sum_mul, Finset.sum_add_distrib, ← Finset.mul_sum]
  simp

theorem squareNorm_eq_min_or_ge_gap (K : SkewOperators n)
    (hexp : (exp K).1.1 = -(1 : Vector n →L[ℝ] Vector n)) :
    squareNorm (K : Vector n →L[ℝ] Vector n) = (n : ℝ) * Real.pi ^ 2 ∨
      ((n : ℝ) + 8) * Real.pi ^ 2 ≤ squareNorm (K : Vector n →L[ℝ] Vector n) := by
  obtain ⟨q, hq⟩ := squareNorm_eq_pi_lattice K hexp
  by_cases hz : q = 0
  · left
    simpa [hz] using hq
  · right
    rw [hq]
    have hqone : (1 : ℝ) ≤ q := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hz
    apply mul_le_mul_of_nonneg_right _ (sq_nonneg Real.pi)
    linarith

end NoExoticSixSphere.SkewAntipodalSpectrum
