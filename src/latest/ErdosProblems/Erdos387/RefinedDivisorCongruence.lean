/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos387.CongruenceCounting
import ErdosProblems.Erdos387.DivisorTupleCRT
import ErdosProblems.Erdos387.RefinedErrorCounting

/-!
# Simultaneous progression and divisor congruences

For a refined rough candidate, every represented near-top divisor `d` is
coprime to the fixed progression modulus `M`.  Hence the conditions
`n ≡ γ (mod M)` and `n ≡ γ_d (mod d)` combine into one class modulo
`M d`, exactly as in BNPZ Sections 6--10.
-/

namespace Erdos387

/-- Roughness beyond `2k` separates every divisor of the binomial
coefficient from the fixed refined modulus. -/
theorem coprime_refinementModulus_of_dvd_choose_of_rough
    {B K n z d : ℕ} (S : CoverBPZ.BPZSection6Input B K)
    (hz : 2 * S.k ≤ z) (hrough : IsZRough z (n.choose S.k))
    (hd : d ∣ n.choose S.k) :
    Nat.Coprime (CoverBPZ.refinementModulus S) d := by
  by_contra hcop
  obtain ⟨p, hp, hpM, hpd⟩ := Nat.Prime.not_coprime_iff_dvd.mp hcop
  have hp2k :=
    CoverBPZ.prime_lt_two_mul_k_of_dvd_refinementModulus S hp hpM
  exact hrough p hp (hp2k.trans_le hz) (hpd.trans hd)

/-- A bad refined candidate supplies a single simultaneous congruence class
modulo `M*d`, with the represented divisor and its full coprime tuple. -/
theorem refinedNearDivisor_has_simultaneousClass
    {B K X z n : ℕ} (S : CoverBPZ.BPZSection6Input B K)
    (hB : 0 < B) (hz : 2 * S.k ≤ z)
    (hnIoc : n ∈ Finset.Ioc (X / 2) X) (hn : S.k < n)
    (hnRefined : (CoverBPZ.refinementModulus S : ℤ) ∣
      (n : ℤ) - CoverBPZ.refinementResidue S)
    (hrough : IsZRough z (n.choose S.k))
    (hnear : HasFixedBNearDivisor B n S.k) :
    let D := S.toCoverFactorization hn
      (refinement_progression_implies_public S hnRefined)
    ∃ d : ℕ, ∃ E : CoprimeCoverDivisorTuple D,
      ∃ hcop : Nat.Coprime (CoverBPZ.refinementModulus S) d,
        n < B * d ∧ d ≤ n ∧ E.value = d ∧
          n ∈ simultaneousClassIoc (X / 2) X
            (CoverBPZ.refinementModulus S) d
            (CoverBPZ.refinementResidue S) E.crtResidue hcop := by
  dsimp
  let hprog := refinement_progression_implies_public S hnRefined
  obtain ⟨d, E, hnd, hdn, hvalue, hnD⟩ :=
    CoprimeCoverDivisorTuple.exists_of_nearDivisor S hB hn hprog hnear
  have hdChoose : d ∣ n.choose S.k := by
    rw [← hvalue]
    exact E.value_dvd_choose
  have hdPos : 0 < d :=
    Nat.pos_of_dvd_of_pos hdChoose (Nat.choose_pos hn.le)
  have hcop : Nat.Coprime (CoverBPZ.refinementModulus S) d :=
    coprime_refinementModulus_of_dvd_choose_of_rough S hz hrough hdChoose
  refine ⟨d, E, hcop, hnd, hdn, hvalue, ?_⟩
  apply (mem_simultaneousClassIoc_iff hcop
    (CoverBPZ.refinementModulus_pos S) hdPos).mpr
  refine ⟨hnIoc, ?_, hnD⟩
  exact (CoverBPZ.refinement_progression_dvd_iff_modEq S).mp hnRefined

/-- Source-facing specialization of the generic single-class cardinality
bound to the refined modulus. -/
theorem card_refinedSimultaneousClassIoc_le
    {B K L U d a : ℕ} (S : CoverBPZ.BPZSection6Input B K)
    (hLU : L ≤ U) (hd : 0 < d)
    (hcop : Nat.Coprime (CoverBPZ.refinementModulus S) d) :
    ((simultaneousClassIoc L U (CoverBPZ.refinementModulus S) d
      (CoverBPZ.refinementResidue S) a hcop).card : ℝ) ≤
      ((U - L : ℕ) : ℝ) /
        (CoverBPZ.refinementModulus S * d : ℕ) + 2 := by
  exact card_simultaneousClassIoc_le hLU hcop
    (CoverBPZ.refinementModulus_pos S) hd

end Erdos387
