import ErdosProblems.Erdos394.PairLatticeCompatibility

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Factoring forced prime coordinates before the product-root argument
-/

open Nat Finset Module Submodule

namespace Erdos394

/-- A prime of `P` outside `F` does not divide the product of the primes in
`F`. -/
theorem prime_not_dvd_primeProduct_of_not_mem
    {P F : Finset ℕ} {p : ℕ} (hFP : F ⊆ P)
    (hprime : ∀ r ∈ P, r.Prime) (hpP : p ∈ P) (hpF : p ∉ F) :
    ¬p ∣ primeProduct F := by
  intro hdiv
  unfold primeProduct at hdiv
  obtain ⟨r, hrF, hpr⟩ :=
    (_root_.Prime.dvd_finsetProd_iff (hprime p hpP).prime
      (fun r : ℕ ↦ r)).mp hdiv
  have heq : p = r :=
    (Nat.prime_dvd_prime_iff_eq (hprime p hpP) (hprime r (hFP hrF))).mp hpr
  exact hpF (heq ▸ hrF)

/-- Every forced prime divides both coordinates, so their squarefree product
can be factored simultaneously from a forced-lattice vector. -/
theorem forced_pair_lattice_coordinates_factor
    (P F : Finset ℕ) (a b : ℕ → ℕ)
    (hFP : F ⊆ P) (hprime : ∀ p ∈ P, p.Prime)
    (x : globalForcedPairLattice P F a b hFP) :
    ∃ j l : ℤ,
      (x : Fin 2 → ℤ) 0 = (primeProduct F : ℤ) * j ∧
      (x : Fin 2 → ℤ) 1 = (primeProduct F : ℤ) * l := by
  have hxker : globalForcedPairEquationLinear P F a b hFP
      (x : Fin 2 → ℤ) = 0 := LinearMap.mem_ker.mp x.property
  have hcoord : ∀ i : Fin 2, primeProduct F ∣
      Int.natAbs ((x : Fin 2 → ℤ) i) := by
    intro i
    apply (primeProduct_dvd_iff_all_dvd F
      (fun p hpF ↦ hprime p (hFP hpF)) _).mpr
    intro p hpF
    let pp : {p // p ∈ P} := ⟨p, hFP hpF⟩
    let pf : {p // p ∈ F} := ⟨p, hpF⟩
    have hz : ((x : Fin 2 → ℤ) i : ZMod p) = 0 := by
      fin_cases i
      · have hfirst :=
          congrArg (fun y : ForcedPairEquationSpace P F ↦ y.1 pp) hxker
        change (if p ∈ F then ((x : Fin 2 → ℤ) 0 : ZMod p)
          else if a p = 0 then ((x : Fin 2 → ℤ) 0 : ZMod p)
          else if b p = 0 then ((x : Fin 2 → ℤ) 1 : ZMod p)
          else (a p : ZMod p) * ((x : Fin 2 → ℤ) 1 : ZMod p) -
            (b p : ZMod p) * ((x : Fin 2 → ℤ) 0 : ZMod p)) = 0 at hfirst
        simpa [hpF] using hfirst
      · have hsecond :=
          congrArg (fun y : ForcedPairEquationSpace P F ↦ y.2 pf) hxker
        change ((x : Fin 2 → ℤ) 1 : ZMod p) = 0 at hsecond
        exact hsecond
    have hdivInt : (p : ℤ) ∣ (x : Fin 2 → ℤ) i :=
      (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp hz
    simpa using (Int.natAbs_dvd_natAbs.mpr hdivInt)
  have hprod0Int : (primeProduct F : ℤ) ∣ (x : Fin 2 → ℤ) 0 := by
    rw [← Int.natAbs_dvd_natAbs]
    simpa using hcoord 0
  have hprod1Int : (primeProduct F : ℤ) ∣ (x : Fin 2 → ℤ) 1 := by
    rw [← Int.natAbs_dvd_natAbs]
    simpa using hcoord 1
  obtain ⟨j, hj⟩ := hprod0Int
  obtain ⟨l, hl⟩ := hprod1Int
  exact ⟨j, l, hj, hl⟩

/-- After dividing the forced product from both coordinates, all unforced
primes still satisfy one of the small-label ratio congruences. -/
theorem forced_pair_quotient_local_ratio
    (P F : Finset ℕ) (a b : ℕ → ℕ) {K : ℕ}
    (hFP : F ⊆ P)
    (hzeroF : bothZeroLabelPrimes P a b ⊆ F)
    (hprime : ∀ p ∈ P, p.Prime) (hK : 1 < K)
    (ha : ∀ p ∈ P, a p < K) (hb : ∀ p ∈ P, b p < K)
    (x : globalForcedPairLattice P F a b hFP)
    (j l : ℤ)
    (hj : (x : Fin 2 → ℤ) 0 = (primeProduct F : ℤ) * j)
    (hl : (x : Fin 2 → ℤ) 1 = (primeProduct F : ℤ) * l) :
    ∀ p ∈ P \ F,
      ∃ A < K, ∃ B < K, (A ≠ 0 ∨ B ≠ 0) ∧
        p ∣ Int.natAbs ((A : ℤ) * l - (B : ℤ) * j) := by
  intro p hpComp
  have hpP := (Finset.mem_sdiff.mp hpComp).1
  have hpF := (Finset.mem_sdiff.mp hpComp).2
  obtain ⟨A, hAK, B, hBK, hAB, hdiv⟩ :=
    forced_pair_lattice_local_ratio P F a b hFP hzeroF hK ha hb x p hpP
  refine ⟨A, hAK, B, hBK, hAB, ?_⟩
  have hfactor :
      Int.natAbs ((A : ℤ) * (x : Fin 2 → ℤ) 1 -
        (B : ℤ) * (x : Fin 2 → ℤ) 0) =
      primeProduct F * Int.natAbs ((A : ℤ) * l - (B : ℤ) * j) := by
    rw [hj, hl]
    rw [show (A : ℤ) * ((primeProduct F : ℤ) * l) -
        (B : ℤ) * ((primeProduct F : ℤ) * j) =
        (primeProduct F : ℤ) * ((A : ℤ) * l - (B : ℤ) * j) by ring,
      Int.natAbs_mul, Int.natAbs_natCast]
  rw [hfactor] at hdiv
  rcases (hprime p hpP).dvd_mul.mp hdiv with hpE | hpRatio
  · exact False.elim
      (prime_not_dvd_primeProduct_of_not_mem hFP hprime hpP hpF hpE)
  · exact hpRatio

/-- Strong product-root bound after extracting all forced coordinate factors.
This is the form whose reciprocal has the three-state Euler weights. -/
theorem forced_pair_lattice_quotient_nonrational_height
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
    primeProduct F * Z ^ (P \ F).card ≤
      2 * K * intSupHeight2 (x : Fin 2 → ℤ) := by
  obtain ⟨j, l, hj, hl⟩ :=
    forced_pair_lattice_coordinates_factor P F a b hFP hprime x
  have hprodF : 0 < primeProduct F := by
    unfold primeProduct
    exact Finset.prod_pos fun p hp ↦ (hprime p (hFP hp)).pos
  have hnorat' : ∀ A < K, ∀ B < K, (A ≠ 0 ∨ B ≠ 0) →
      (A : ℤ) * l ≠ (B : ℤ) * j := by
    intro A hAK B hBK hAB heq
    apply hnorat A hAK B hBK hAB
    rw [hj, hl]
    calc
      (A : ℤ) * ((primeProduct F : ℤ) * l) =
          (primeProduct F : ℤ) * ((A : ℤ) * l) := by ring
      _ = (primeProduct F : ℤ) * ((B : ℤ) * j) := by rw [heq]
      _ = (B : ℤ) * ((primeProduct F : ℤ) * j) := by ring
  have hroot : Z ^ (P \ F).card ≤
      2 * K * max j.natAbs l.natAbs := by
    apply primeProduct_root_le_two_mul_height (P \ F)
      (fun p hp ↦ hprime p (Finset.mem_sdiff.mp hp).1) hK
      (fun p hp ↦ hlarge p (Finset.mem_sdiff.mp hp).1)
      (forced_pair_quotient_local_ratio P F a b hFP hzeroF hprime hK
        ha hb x j l hj hl)
      hnorat'
  have hjabs : ((x : Fin 2 → ℤ) 0).natAbs =
      primeProduct F * j.natAbs := by
    rw [hj, Int.natAbs_mul, Int.natAbs_natCast]
  have hlabs : ((x : Fin 2 → ℤ) 1).natAbs =
      primeProduct F * l.natAbs := by
    rw [hl, Int.natAbs_mul, Int.natAbs_natCast]
  have hheight : intSupHeight2 (x : Fin 2 → ℤ) =
      primeProduct F * max j.natAbs l.natAbs := by
    simp only [intSupHeight2, hjabs, hlabs]
    rw [mul_max]
  rw [hheight]
  nlinarith

end Erdos394
