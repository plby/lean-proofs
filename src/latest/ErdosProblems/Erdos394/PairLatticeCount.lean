import ErdosProblems.Erdos394.ForcedPairResidueKernel
import ErdosProblems.Erdos394.IntegralLatticeCount
import ErdosProblems.Erdos394.TrackedIntegralLatticeCount

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Explicit count for actual pair/Möbius lattices
-/

open Nat Finset Module Submodule

namespace Erdos394

/-- Every finite set of points of the forced pair lattice in `[0,Y]²` obeys
the sharp-leading reduced-basis count with determinant `(∏P)(∏F)`. -/
theorem forced_pair_lattice_square_count
    (P F : Finset ℕ) (a b : ℕ → ℕ) {K Y : ℕ}
    (hFP : F ⊆ P)
    (hzeroF : bothZeroLabelPrimes P a b ⊆ F)
    (hprime : ∀ p ∈ P, p.Prime)
    (ha : ∀ p ∈ P, a p < K) (hb : ∀ p ∈ P, b p < K)
    (hKp : ∀ p ∈ P, K < p)
    (S : Finset (globalForcedPairLattice P F a b hFP))
    (hpoint : ∀ x ∈ S, ∀ i,
      0 ≤ (x : Fin 2 → ℤ) i ∧ (x : Fin 2 → ℤ) i ≤ (Y : ℤ)) :
    ∃ L : ℕ, 0 < L ∧
      (S.card : ℝ) ≤ (Y : ℝ) ^ 2 /
          ((primeProduct P * primeProduct F : ℕ) : ℝ) +
        40 * ((Y : ℝ) / (L : ℝ)) + 4 := by
  have hprodP : 0 < primeProduct P := by
    unfold primeProduct
    apply Finset.prod_pos
    intro p hp
    exact (hprime p hp).pos
  have hprodF : 0 < primeProduct F := by
    unfold primeProduct
    apply Finset.prod_pos
    intro p hp
    exact (hprime p (hFP hp)).pos
  apply integral_lattice_square_count
    (globalForcedPairLattice P F a b hFP)
    (globalForcedPairLatticeBasis P F a b hFP hzeroF hprime ha hb hKp)
    S (by positivity)
    (globalForcedPairLattice_index P F a b hFP hzeroF hprime ha hb hKp)
    hpoint

/-- Tracked version retaining the selected reduced pair-lattice basis vector. -/
theorem forced_pair_lattice_square_count_tracked
    (P F : Finset ℕ) (a b : ℕ → ℕ) {K Y : ℕ}
    (hFP : F ⊆ P)
    (hzeroF : bothZeroLabelPrimes P a b ⊆ F)
    (hprime : ∀ p ∈ P, p.Prime)
    (ha : ∀ p ∈ P, a p < K) (hb : ∀ p ∈ P, b p < K)
    (hKp : ∀ p ∈ P, K < p)
    (S : Finset (globalForcedPairLattice P F a b hFP))
    (hpoint : ∀ x ∈ S, ∀ i,
      0 ≤ (x : Fin 2 → ℤ) i ∧ (x : Fin 2 → ℤ) i ≤ (Y : ℤ)) :
    ∃ c : Basis (Fin 2) ℤ (globalForcedPairLattice P F a b hFP), ∃ L : ℕ,
      L = intSupHeight2 (c 0 : Fin 2 → ℤ) ∧ 0 < L ∧
      L ≤ intSupHeight2 (c 1 : Fin 2 → ℤ) ∧
      (((((c 0 : Fin 2 → ℤ) 1).natAbs ≤ ((c 0 : Fin 2 → ℤ) 0).natAbs ∧
          2 * ((c 1 : Fin 2 → ℤ) 0).natAbs ≤ L) ∨
       (((c 0 : Fin 2 → ℤ) 0).natAbs ≤ ((c 0 : Fin 2 → ℤ) 1).natAbs ∧
          2 * ((c 1 : Fin 2 → ℤ) 1).natAbs ≤ L)) ∧
      (S.card : ℝ) ≤ (Y : ℝ) ^ 2 /
          ((primeProduct P * primeProduct F : ℕ) : ℝ) +
        40 * ((Y : ℝ) / (L : ℝ)) + 4) := by
  have hprodP : 0 < primeProduct P := by
    unfold primeProduct
    exact Finset.prod_pos fun p hp ↦ (hprime p hp).pos
  have hprodF : 0 < primeProduct F := by
    unfold primeProduct
    exact Finset.prod_pos fun p hp ↦ (hprime p (hFP hp)).pos
  exact integral_lattice_square_count_tracked
    (globalForcedPairLattice P F a b hFP)
    (globalForcedPairLatticeBasis P F a b hFP hzeroF hprime ha hb hKp)
    S (by positivity)
    (globalForcedPairLattice_index P F a b hFP hzeroF hprime ha hb hKp)
    hpoint

end Erdos394
