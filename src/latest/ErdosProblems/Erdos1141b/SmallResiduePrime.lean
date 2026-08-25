import ErdosProblems.Erdos1141b.ResidueCharacter
import ErdosProblems.Erdos1141b.UniformBurgess
import ErdosProblems.Erdos1141b.SmallSplitPrime

/-!
# Small primes at which a squarefree integer is a square
-/

open scoped BigOperators

namespace Erdos1141b

open CharacterSums

theorem exists_small_quadratic_residue_prime_cutoff :
    ∃ M0 : ℕ, ∀ {M d : ℕ}, M0 ≤ M → Squarefree d → 1 < d → 8 * d ∣ M →
      ∃ p : ℕ, p.Prime ∧ p ≠ 2 ∧ ¬p ∣ M ∧
        (p : ℝ) ≤ (M : ℝ) ^ (31 / 64 : ℝ) ∧ jacobiSym (d : ℤ) p = 1 := by
  classical
  obtain ⟨M1, hprefix⟩ := exists_twisted_prefix_bound_relative_cutoff
  obtain ⟨M2, hprime⟩ := exists_small_split_prime_cutoff
  refine ⟨max (max M1 M2) 2, ?_⟩
  intro M d hM hd hdgt hdM
  have hM1 : M1 ≤ M := (le_max_left M1 M2).trans ((le_max_left _ _).trans hM)
  have hM2 : M2 ≤ M := (le_max_right M1 M2).trans ((le_max_left _ _).trans hM)
  have hMpos : 0 < M := lt_of_lt_of_le (by decide : 0 < 2) ((le_max_right _ _).trans hM)
  obtain ⟨e, r, he, hdEq, hrOdd, hrSq⟩ := squarefree_two_odd_decomposition hd
  let p : r.primeFactors → ℕ := fun i ↦ i.val
  have : ∀ i, Fact (p i).Prime := fun i ↦ ⟨Nat.prime_of_mem_primeFactors i.property⟩
  have hc : Pairwise fun i j ↦ (p i).Coprime (p j) := by
    intro i j hij
    apply (Nat.prime_of_mem_primeFactors i.property).coprime_iff_not_dvd.mpr
    intro hdiv
    have heq : p i = p j := (Nat.prime_dvd_prime_iff_eq
      (Nat.prime_of_mem_primeFactors i.property) (Nat.prime_of_mem_primeFactors j.property)).mp hdiv
    exact hij (Subtype.ext heq)
  have hprod : (∏ i, p i) = r := by
    exact (Finset.prod_coe_sort r.primeFactors (fun x : ℕ ↦ x)).trans
      (Nat.prod_primeFactors_of_squarefree hrSq)
  have hodd : ∀ i, p i ≠ 2 := by
    intro i hi
    apply hrOdd.not_two_dvd_nat
    rw [← hi]
    exact Nat.dvd_of_mem_primeFactors i.property
  have ht : (8 : ℕ).Coprime (∏ i, p i) := by
    rw [hprod, show 8 = 2 ^ 3 by norm_num]
    exact (Nat.coprime_two_left.mpr hrOdd).pow_left 3
  let ψ := auxiliaryResidueCharacter e r
  let χ := crtMulChar ht ψ (primeProductMulChar p hc)
  let q := 8 * ∏ i, p i
  have hq : 1 < q := by
    dsimp only [q]
    rw [hprod]
    have hrpos := Nat.pos_of_ne_zero hrSq.ne_zero
    omega
  have : NeZero q := ⟨by omega⟩
  have hqdiv : q ∣ M := by
    apply dvd_trans _ hdM
    dsimp only [q]
    rw [hprod, hdEq]
    exact Nat.mul_dvd_mul_left 8 (dvd_mul_left r (2 ^ e))
  have hqM : q ≤ M := Nat.le_of_dvd hMpos hqdiv
  have hχquad : χ.IsQuadratic := crtMulChar_isQuadratic ht ψ (primeProductMulChar p hc)
    (auxiliaryResidueCharacter_isQuadratic e r) (primeProductMulChar_isQuadratic p hc)
  have hχne : χ ≠ 1 := by
    by_cases hr1 : r = 1
    · have he1 : e = 1 := by
        have : e = 0 ∨ e = 1 := by omega
        rcases this with he0 | he1
        · simp [he0, hr1] at hdEq
          omega
        · exact he1
      apply crtMulChar_ne_one_of_left ht ψ _
      simpa only [ψ, he1, hr1] using auxiliaryResidueCharacter_two_ne_one
    · obtain ⟨v, hv, hvdvd⟩ := Nat.exists_prime_and_dvd hr1
      let i : r.primeFactors := ⟨v, Nat.mem_primeFactors.mpr ⟨hv, hvdvd, hrSq.ne_zero⟩⟩
      exact crtMulChar_ne_one_of_right ht ψ _ (primeProductMulChar_ne_one p hc i (hodd i))
  have hcomplex : χ.ringHomComp (Int.castRingHom ℂ) ≠ 1 :=
    (MulChar.ringHomComp_ne_one_iff Int.cast_injective).mpr hχne
  have hshort : ∀ N : ℕ, (M : ℝ) ^ (15 / 32 : ℝ) ≤ (N : ℝ) →
      ‖∑ n ∈ Finset.Icc 1 N, χ.ringHomComp (Int.castRingHom ℂ) (n : ZMod q)‖ ≤
        (N : ℝ) * (M : ℝ) ^ (-1 / 512 : ℝ) :=
    hprefix M hM1 8 (by decide) p hc ht ψ (auxiliaryResidueCharacter_isQuadratic e r)
      hodd hq hqM hcomplex
  obtain ⟨v, hv, hvbound, hvM, hvχ⟩ := hprime M hM2 q hq hqdiv
    (χ.ringHomComp (Int.castRingHom ℂ)) hcomplex
    (hχquad.comp (Int.castRingHom ℂ)).sq_eq_one hshort
  have hv2 : v ≠ 2 := by
    intro hv2
    apply hvM
    rw [hv2]
    exact dvd_trans (by use 4 * d; ring : 2 ∣ 8 * d) hdM
  have hvOdd : Odd v := hv.odd_of_ne_two hv2
  have hvχint : χ (v : ZMod q) = 1 := by
    change (χ (v : ZMod q) : ℂ) = 1 at hvχ
    exact_mod_cast hvχ
  have hχeval : χ (v : ZMod q) = jacobiSym (d : ℤ) v := by
    change ψ (ZMod.chineseRemainder ht (v : ZMod q)).1 *
      primeProductCharacter p hc (ZMod.chineseRemainder ht (v : ZMod q)).2 = _
    simp only [map_natCast, Prod.fst_natCast, Prod.snd_natCast]
    have hj : primeProductCharacter p hc (v : ZMod (∏ i, p i)) = jacobiSym (v : ℤ) r := by
      simpa only [Int.cast_natCast, hprod] using primeProductCharacter_intCast p hc (v : ℤ)
    rw [hj, hdEq]
    exact auxiliaryResidueCharacter_reciprocity e r v hrOdd hvOdd
  exact ⟨v, hv, hv2, hvM, hvbound, hχeval ▸ hvχint⟩

end Erdos1141b
