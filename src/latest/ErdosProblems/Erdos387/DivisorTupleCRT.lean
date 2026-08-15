/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos387.Section6Counting

/-!
# CRT residue of a residual-divisor tuple

This formalizes the congruence `n ≡ γ_d (mod d)` used throughout BNPZ
Sections 6--10 when `d = ∏ i, d_i` and `d_i ∣ n-i` are pairwise coprime.
-/

namespace Erdos387

open scoped BigOperators

/-- A residual-divisor tuple together with the positivity and pairwise
coprimality facts needed by the Chinese remainder theorem. -/
structure CoprimeCoverDivisorTuple {n k : ℕ}
    (D : CoverFactorization n k) extends CoverDivisorTuple D where
  positive : ∀ i, 0 < factor i
  pairwise : ∀ i j, i ≠ j → Nat.Coprime (factor i) (factor j)

namespace CoprimeCoverDivisorTuple

/-- The represented divisor. -/
def value {D : CoverFactorization n k}
    (E : CoprimeCoverDivisorTuple D) : ℕ :=
  ∏ i, E.factor i

theorem value_dvd_choose {D : CoverFactorization n k}
    (E : CoprimeCoverDivisorTuple D) :
    E.value ∣ n.choose k := by
  rw [value, choose_eq_prod_coverQuotients D,
    ← Fin.prod_univ_eq_prod_range]
  exact Finset.prod_dvd_prod_of_dvd E.factor
    (fun i : Fin k => (n - i.val) / D.g i.val)
    (by intro i _; exact E.divides i)

/-- Product divisibility for a finite pairwise-coprime natural family. -/
theorem finset_prod_dvd_of_pairwise_coprime_nat
    {I : Type*} [DecidableEq I] (s : Finset I) (f : I → ℕ) (N : ℕ)
    (hpair : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → Nat.Coprime (f i) (f j))
    (hdvd : ∀ i ∈ s, f i ∣ N) :
    ∏ i ∈ s, f i ∣ N := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
      rw [Finset.prod_insert ha]
      have hcop : Nat.Coprime (f a) (∏ i ∈ s, f i) := by
        apply Nat.Coprime.prod_right
        intro i hi
        exact hpair a (Finset.mem_insert_self a s) i
          (Finset.mem_insert_of_mem hi) (fun hai => ha (hai ▸ hi))
      apply hcop.mul_dvd_of_dvd_of_dvd
      · exact hdvd a (Finset.mem_insert_self a s)
      · apply ih
        · intro i hi j hj hij
          exact hpair i (Finset.mem_insert_of_mem hi) j
            (Finset.mem_insert_of_mem hj) hij
        · intro i hi
          exact hdvd i (Finset.mem_insert_of_mem hi)

/-- The canonical representative of the simultaneous classes
`γ ≡ i (mod d_i)`. -/
noncomputable def crtResidue {D : CoverFactorization n k}
    (E : CoprimeCoverDivisorTuple D) : ℕ :=
  Nat.chineseRemainderOfFinset
    (fun i : Fin k => i.val) E.factor Finset.univ
    (by intro i _; exact (E.positive i).ne')
    (by
      intro i _ j _ hij
      exact E.pairwise i j hij)

theorem crtResidue_mod_factor {D : CoverFactorization n k}
    (E : CoprimeCoverDivisorTuple D) (i : Fin k) :
    E.crtResidue ≡ i.val [MOD E.factor i] := by
  exact (Nat.chineseRemainderOfFinset
    (fun i : Fin k => i.val) E.factor Finset.univ
    (by intro j _; exact (E.positive j).ne')
    (by
      intro a _ b _ hab
      exact E.pairwise a b hab)).prop i (Finset.mem_univ i)

theorem crtResidue_lt_value {D : CoverFactorization n k}
    (E : CoprimeCoverDivisorTuple D) :
    E.crtResidue < E.value := by
  unfold crtResidue value
  exact Nat.chineseRemainderOfFinset_lt_prod
    (a := fun i : Fin k => i.val) (s := E.factor) (t := Finset.univ)
    (by intro i _; exact (E.positive i).ne')
    (by
      intro i _ j _ hij
      exact E.pairwise i j hij)

/-- Every component modulus divides the difference between the ambient
integer and the tuple's CRT representative. -/
theorem factor_dvd_ambient_sub_crtResidue
    {D : CoverFactorization n k} (E : CoprimeCoverDivisorTuple D)
    (hkn : k ≤ n) (hvalue : E.value ≤ n) (i : Fin k) :
    E.factor i ∣ n - E.crtResidue := by
  have hresLe : E.crtResidue ≤ n :=
    (E.crtResidue_lt_value.le.trans hvalue)
  have hiLe : i.val ≤ n := (Nat.le_of_lt i.isLt).trans hkn
  have hiModN : i.val ≡ n [MOD E.factor i] :=
    (Nat.modEq_iff_dvd' hiLe).mpr
      (E.divides i |>.trans (coverQuotient_dvd_term D i.isLt))
  have hresModN : E.crtResidue ≡ n [MOD E.factor i] :=
    (E.crtResidue_mod_factor i).trans hiModN
  exact (Nat.modEq_iff_dvd' hresLe).mp hresModN

/-- The product `d = ∏ d_i` divides `n-γ_d`. -/
theorem value_dvd_ambient_sub_crtResidue
    {D : CoverFactorization n k} (E : CoprimeCoverDivisorTuple D)
    (hkn : k ≤ n) (hvalue : E.value ≤ n) :
    E.value ∣ n - E.crtResidue := by
  change (∏ i : Fin k, E.factor i) ∣ n - E.crtResidue
  exact finset_prod_dvd_of_pairwise_coprime_nat
    Finset.univ E.factor (n - E.crtResidue)
    (by intro i _ j _ hij; exact E.pairwise i j hij)
    (by intro i _; exact E.factor_dvd_ambient_sub_crtResidue hkn hvalue i)

/-- Source-facing form of the tuple CRT congruence. -/
theorem ambient_modEq_crtResidue
    {D : CoverFactorization n k} (E : CoprimeCoverDivisorTuple D)
    (hkn : k ≤ n) (hvalue : E.value ≤ n) :
    n ≡ E.crtResidue [MOD E.value] := by
  have hresLe : E.crtResidue ≤ n :=
    E.crtResidue_lt_value.le.trans hvalue
  exact ((Nat.modEq_iff_dvd' hresLe).mpr
    (E.value_dvd_ambient_sub_crtResidue hkn hvalue)).symm

/-- A near-top divisor on the public progression carries the exact CRT
tuple and congruence used in the analytic counting arguments. -/
theorem exists_of_nearDivisor
    {B K n : ℕ} (S : CoverBPZ.BPZSection6Input B K) (hB : 0 < B)
    (hn : S.k < n)
    (hprog : (CoverBPZ.Nk_formula S.k : ℤ) ∣ (n : ℤ) - S.α)
    (hnear : HasFixedBNearDivisor B n S.k) :
    let D := S.toCoverFactorization hn hprog
    ∃ d : ℕ, ∃ E : CoprimeCoverDivisorTuple D,
      n < B * d ∧ d ≤ n ∧ E.value = d ∧
        n ≡ E.crtResidue [MOD d] := by
  dsimp
  obtain ⟨d, E₀, hnd, hdn, hvalue, _hcomponentDvd,
      hpair, _htwo⟩ :=
    nearDivisor_has_residualTuple S hB hn hprog hnear
  have hpos : ∀ i : Fin S.k, 0 < E₀.factor i := by
    intro i
    have hfactorDvd : E₀.factor i ∣ n.choose S.k :=
      (E₀.divides i).trans
        (coverQuotient_dvd_choose (S.toCoverFactorization hn hprog) i.isLt)
    exact Nat.pos_of_dvd_of_pos hfactorDvd (Nat.choose_pos hn.le)
  let E : CoprimeCoverDivisorTuple (S.toCoverFactorization hn hprog) :=
    { toCoverDivisorTuple := E₀
      positive := hpos
      pairwise := hpair }
  have hEvalue : E.value = d := by
    change E₀.value = d
    exact hvalue
  refine ⟨d, E, hnd, hdn, hEvalue, ?_⟩
  rw [← hEvalue]
  exact E.ambient_modEq_crtResidue hn.le (hEvalue.trans_le hdn)

end CoprimeCoverDivisorTuple

end Erdos387
