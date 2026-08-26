/- Adapted from Erdos1148/IntegerLocalCount.lean; only a local base pair is required. -/
import ErdosProblems.Erdos941.PairLocal.LocalPairCount

/-!
# Expressing the local bound in integer factorizations

The p-adic content exponent is the valuation of the integer gcd. The
resultant valuation is bounded by the binary discriminant valuation.
-/

namespace Erdos941.PairLocal

lemma padicInt_valuation_intCast (p : ℕ) [Fact p.Prime] (n : ℤ) :
    (n : PadicInt p).valuation = n.natAbs.factorization p := by
  simp [PadicInt.valuation, padicValInt, Nat.factorization_def _ (Fact.out : p.Prime)]

lemma pairContentValuation_intCast (p : ℕ) [Fact p.Prime] (d ℓ : ℤ) (hd : d ≠ 0) :
    pairContentValuation p (d : PadicInt p) (ℓ : PadicInt p) =
      (d.natAbs.gcd ℓ.natAbs).factorization p := by
  classical
  by_cases hℓ : ℓ = 0
  · simp [pairContentValuation, hℓ, padicInt_valuation_intCast]
  have hℓK : (ℓ : PadicInt p) ≠ 0 := by exact_mod_cast hℓ
  rw [pairContentValuation, if_neg hℓK, padicInt_valuation_intCast,
    padicInt_valuation_intCast, Nat.factorization_gcd (Int.natAbs_ne_zero.mpr hd)
      (Int.natAbs_ne_zero.mpr hℓ), Finsupp.inf_apply]

lemma resultant_valuation_le_binary_discriminant (p : ℕ) [Fact p.Prime]
    {d ℓ : PadicInt p} (base : FormPair (PadicInt p) d ℓ) (hnd : ℓ ^ 2 ≠ 4 * d ^ 2) :
    (pairResultant base.1.1 base.1.2).valuation ≤ (ℓ ^ 2 - 4 * d ^ 2).valuation := by
  have hres := pairResultant_ne_zero base hnd
  have h16 : (16 : PadicInt p) ≠ 0 := by norm_num
  have heq : 16 * pairResultant base.1.1 base.1.2 = ℓ ^ 2 - 4 * d ^ 2 := by
    rw [pairResultant_discr, base.2.1, base.2.2.1, base.2.2.2]
    ring
  rw [← heq, PadicInt.valuation_mul h16 hres]
  omega

theorem card_padicPairOrbits_le_factorization (p : ℕ) [Fact p.Prime]
    {d ℓ : ℤ} (base : FormPair (PadicInt p) (d : PadicInt p) (ℓ : PadicInt p)) (hd : d ≠ 0) (hnd : ℓ ^ 2 ≠ 4 * d ^ 2) :
    Nat.card (SpecialPairOrbits (PadicInt p) d ℓ) ≤
      16 * ((ℓ ^ 2 - 4 * d ^ 2).natAbs.factorization p + 1) *
        p ^ ((d.natAbs.gcd ℓ.natAbs).factorization p / 2) := by
  let pair := base
  have hdK : (d : PadicInt p) ≠ 0 := by exact_mod_cast hd
  have hndK := map_nondegenerate (Int.castRingHom (PadicInt p)) Int.cast_injective hnd
  have h := card_padicPairOrbits_le_content p pair hdK hndK
  have hval := resultant_valuation_le_binary_discriminant p pair hndK
  have hbinary : ((ℓ : PadicInt p) ^ 2 - 4 * (d : PadicInt p) ^ 2).valuation =
      (ℓ ^ 2 - 4 * d ^ 2).natAbs.factorization p := by
    rw [← padicInt_valuation_intCast p (ℓ ^ 2 - 4 * d ^ 2)]
    congr 1
    push_cast
    rfl
  rw [hbinary] at hval
  rw [pairContentValuation_intCast p d ℓ hd] at h
  exact h.trans (Nat.mul_le_mul_right _ (Nat.mul_le_mul_left 16 (Nat.add_le_add_right hval 1)))

end Erdos941.PairLocal
