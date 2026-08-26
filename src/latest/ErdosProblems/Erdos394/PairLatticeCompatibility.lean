import ErdosProblems.Erdos394.PairLatticeCount
import ErdosProblems.Erdos394.ProductRootHeight

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Local slope compatibility of vectors in forced pair lattices

A vector in an actual pair/Möbius congruence lattice satisfies, at every
prime, one of the finitely many signed ratio congruences used by the
product-root obstruction.
-/

open Nat Finset Module Submodule

namespace Erdos394

/-- Every vector of a forced pair lattice is locally compatible with a
nonzero pair of labels below `K` at each prime.  At an unforced prime we use
the actual root labels; at a forced prime both coordinates vanish, so the
fixed label pair `(1,0)` works. -/
theorem forced_pair_lattice_local_ratio
    (P F : Finset ℕ) (a b : ℕ → ℕ) {K : ℕ}
    (hFP : F ⊆ P)
    (hzeroF : bothZeroLabelPrimes P a b ⊆ F)
    (hK : 1 < K)
    (ha : ∀ p ∈ P, a p < K) (hb : ∀ p ∈ P, b p < K)
    (x : globalForcedPairLattice P F a b hFP) :
    ∀ p ∈ P,
      ∃ A < K, ∃ B < K, (A ≠ 0 ∨ B ≠ 0) ∧
        p ∣ Int.natAbs ((A : ℤ) * (x : Fin 2 → ℤ) 1 -
          (B : ℤ) * (x : Fin 2 → ℤ) 0) := by
  intro p hpP
  have hxker : globalForcedPairEquationLinear P F a b hFP
      (x : Fin 2 → ℤ) = 0 := LinearMap.mem_ker.mp x.property
  let pp : {p // p ∈ P} := ⟨p, hpP⟩
  by_cases hpF : p ∈ F
  · let pf : {p // p ∈ F} := ⟨p, hpF⟩
    have hlz := congrArg (fun y : ForcedPairEquationSpace P F ↦ y.2 pf) hxker
    change ((x : Fin 2 → ℤ) 1 : ZMod p) = 0 at hlz
    have hlz' : ((x : Fin 2 → ℤ) 1 : ZMod p) = 0 := hlz
    have hldivInt : (p : ℤ) ∣ (x : Fin 2 → ℤ) 1 :=
      (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp hlz'
    have hldiv : p ∣ Int.natAbs ((x : Fin 2 → ℤ) 1) := by
      simpa using (Int.natAbs_dvd_natAbs.mpr hldivInt)
    refine ⟨1, hK, 0, by omega, Or.inl (by omega), ?_⟩
    simpa using hldiv
  · have hnotboth : ¬(a p = 0 ∧ b p = 0) := by
      intro hz
      exact hpF (hzeroF (Finset.mem_filter.mpr ⟨hpP, hz⟩))
    have heq := congrArg (fun y : ForcedPairEquationSpace P F ↦ y.1 pp) hxker
    change (if p ∈ F then ((x : Fin 2 → ℤ) 0 : ZMod p)
      else if a p = 0 then ((x : Fin 2 → ℤ) 0 : ZMod p)
      else if b p = 0 then ((x : Fin 2 → ℤ) 1 : ZMod p)
      else (a p : ZMod p) * ((x : Fin 2 → ℤ) 1 : ZMod p) -
        (b p : ZMod p) * ((x : Fin 2 → ℤ) 0 : ZMod p)) = 0 at heq
    rw [if_neg hpF] at heq
    have hcast :
        (((a p : ℕ) : ℤ) * (x : Fin 2 → ℤ) 1 -
          ((b p : ℕ) : ℤ) * (x : Fin 2 → ℤ) 0 : ZMod p) = 0 := by
      by_cases ha0 : a p = 0
      · have hb0 : b p ≠ 0 := fun hb0 ↦ hnotboth ⟨ha0, hb0⟩
        have hjz : ((x : Fin 2 → ℤ) 0 : ZMod p) = 0 := by
          simpa [ha0] using heq
        simp [ha0, hjz]
      · by_cases hb0 : b p = 0
        · have hlz : ((x : Fin 2 → ℤ) 1 : ZMod p) = 0 := by
            simpa [ha0, hb0] using heq
          simp [hb0, hlz]
        · simpa [ha0, hb0] using heq
    have hcast' :
        ((((a p : ℤ) * (x : Fin 2 → ℤ) 1 -
          (b p : ℤ) * (x : Fin 2 → ℤ) 0 : ℤ)) : ZMod p) = 0 := by
      simpa only [Int.cast_sub, Int.cast_mul, Int.cast_natCast] using hcast
    have hdivInt : (p : ℤ) ∣
        ((a p : ℤ) * (x : Fin 2 → ℤ) 1 -
          (b p : ℤ) * (x : Fin 2 → ℤ) 0) :=
      (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp hcast'
    have hdiv : p ∣ Int.natAbs
        ((a p : ℤ) * (x : Fin 2 → ℤ) 1 -
          (b p : ℤ) * (x : Fin 2 → ℤ) 0) := by
      simpa using (Int.natAbs_dvd_natAbs.mpr hdivInt)
    refine ⟨a p, ha p hpP, b p, hb p hpP, ?_, hdiv⟩
    exact not_and_or.mp hnotboth

/-- Consequently, a forced-lattice vector which lies on none of the small
rational lines has one factor of the chosen root scale in its height for every
prime in `P`. -/
theorem forced_pair_lattice_nonrational_height
    (P F : Finset ℕ) (a b : ℕ → ℕ) {K Z : ℕ}
    (hFP : F ⊆ P)
    (hzeroF : bothZeroLabelPrimes P a b ⊆ F)
    (hprime : ∀ p ∈ P, p.Prime) (hK : 1 < K)
    (ha : ∀ p ∈ P, a p < K) (hb : ∀ p ∈ P, b p < K)
    (hlarge : ∀ p ∈ P, Z ^ (K * K) ≤ p)
    (x : globalForcedPairLattice P F a b hFP)
    (hnorat : ∀ A < K, ∀ B < K, (A ≠ 0 ∨ B ≠ 0) →
      (A : ℤ) * (x : Fin 2 → ℤ) 1 ≠
        (B : ℤ) * (x : Fin 2 → ℤ) 0) :
    Z ^ P.card ≤ 2 * K * intSupHeight2 (x : Fin 2 → ℤ) := by
  simpa only [intSupHeight2] using
    (primeProduct_root_le_two_mul_height P hprime hK hlarge
      (forced_pair_lattice_local_ratio P F a b hFP hzeroF hK ha hb x)
      hnorat)

/-- Real reciprocal form of the preceding height bound, tailored to the
`40Y/L` boundary term in the lattice count. -/
theorem forty_boundary_le_of_nonrational_height
    {K Z r Y L : ℕ} (hK : 1 < K) (hZ : 1 ≤ Z) (hL : 0 < L)
    (hheight : Z ^ r ≤ 2 * K * L) :
    (40 : ℝ) * ((Y : ℝ) / (L : ℝ)) ≤
      80 * (K : ℝ) * (Y : ℝ) / ((Z ^ r : ℕ) : ℝ) := by
  have hLr : (0 : ℝ) < L := by exact_mod_cast hL
  have hpow : 0 < Z ^ r := pow_pos (Nat.zero_lt_of_lt hZ) _
  have hpowr : (0 : ℝ) < (Z ^ r : ℕ) := by exact_mod_cast hpow
  have hheightR : ((Z ^ r : ℕ) : ℝ) ≤ 2 * (K : ℝ) * (L : ℝ) := by
    exact_mod_cast hheight
  have hY : (0 : ℝ) ≤ Y := by positivity
  rw [show (40 : ℝ) * ((Y : ℝ) / (L : ℝ)) =
      (40 * (Y : ℝ)) / (L : ℝ) by ring,
    show (80 : ℝ) * (K : ℝ) * (Y : ℝ) / ((Z ^ r : ℕ) : ℝ) =
      (80 * (K : ℝ) * (Y : ℝ)) / ((Z ^ r : ℕ) : ℝ) by ring]
  apply (div_le_div_iff₀ hLr hpowr).mpr
  nlinarith

end Erdos394
