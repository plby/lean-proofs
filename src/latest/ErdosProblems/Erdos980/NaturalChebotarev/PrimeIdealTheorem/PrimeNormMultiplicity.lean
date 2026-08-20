/-
Copyright (c) 2026 The Formal Conjectures Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Formal Conjectures Authors
-/

import ErdosProblems.Erdos980.NaturalChebotarev.IdealMangoldt.Basic
import ErdosProblems.Erdos980.NaturalChebotarev.SplitTransfer.Counting
import ErdosProblems.Erdos980.NaturalChebotarev.WeightedToCounting

/-!
# Prime ideals grouped by their absolute norm

The prime-ideal counting function is the partial sum of a natural-valued norm
multiplicity.  In a finite Galois extension of `ℚ`, every norm fiber has
cardinality at most the field degree.
-/

namespace Erdos980.NaturalChebotarev.PrimeIdealTheorem

open BigOperators NumberField

noncomputable section

abbrev PrimeIdeal (K : Type*) [Field K] [NumberField K] :=
  IdealMangoldt.PrimeIdeal K

/-- Prime ideals having a prescribed absolute norm. -/
def primeNormFiber (K : Type*) [Field K] [NumberField K] (n : ℕ) :=
  {P : PrimeIdeal K // Ideal.absNorm P.1 = n}

instance primeNormFiber_finite
    (K : Type*) [Field K] [NumberField K] (n : ℕ) :
    Finite (primeNormFiber K n) := by
  let f : primeNormFiber K n → {I : Ideal (𝓞 K) // Ideal.absNorm I = n} :=
    fun P ↦ ⟨P.1.1, P.2⟩
  letI : Finite {I : Ideal (𝓞 K) // Ideal.absNorm I = n} :=
    (Ideal.finite_setOfPred_absNorm_eq (S := 𝓞 K) n).to_subtype
  exact Finite.of_injective f fun P Q h ↦ by
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg
      (fun z : {I : Ideal (𝓞 K) // Ideal.absNorm I = n} ↦ z.1) h

/-- The number of prime ideals whose absolute norm is exactly `n`. -/
def primeNormMultiplicity (K : Type*) [Field K] [NumberField K] (n : ℕ) : ℕ :=
  Nat.card (primeNormFiber K n)

namespace PrimeNormMultiplicity

variable (L : Type*) [Field L] [NumberField L] [Algebra ℚ L] [IsGalois ℚ L]

private theorem residueDegree_pos (P : PrimeIdeal L) :
    0 < SplitTransfer.residueDegree L P.1 := by
  letI : P.1.IsPrime := P.2.1
  letI : P.1.LiesOver (P.1.under (𝓞 ℚ)) :=
    Ideal.over_under (A := 𝓞 ℚ) (P := P.1)
  exact Ideal.inertiaDeg_pos' _ _

/-- A fixed norm can occur for at most `[L : ℚ]` prime ideals. -/
theorem primeNormMultiplicity_le_degree (n : ℕ) :
    primeNormMultiplicity L n ≤ Module.finrank ℚ L := by
  classical
  by_cases hne : Nonempty (primeNormFiber L n)
  · let P₀ := Classical.choice hne
    let p := SplitTransfer.primeBelow L P₀.1.1
    have hp : p.Prime :=
      (SplitTransfer.under_eq_rationalIdeal_primeBelow L P₀.1.2.1 P₀.1.2.2).2
    have hp0 : SplitTransfer.rationalIdeal p ≠ ⊥ := by
      intro h
      have hnorm := congrArg Ideal.absNorm h
      rw [SplitTransfer.absNorm_rationalIdeal, Ideal.absNorm_bot] at hnorm
      exact hp.ne_zero hnorm
    letI : (SplitTransfer.rationalIdeal p).IsPrime :=
      SplitTransfer.rationalIdeal_isPrime hp
    letI : (SplitTransfer.rationalIdeal p).IsMaximal :=
      (SplitTransfer.rationalIdeal_isPrime hp).isMaximal hp0
    haveI : Finite {P : Ideal (𝓞 L) // P.IsPrime ∧
        P.LiesOver (SplitTransfer.rationalIdeal p)} :=
      (IsDedekindDomain.primesOver_finite
        (SplitTransfer.rationalIdeal p) (𝓞 L)).to_subtype
    let f : primeNormFiber L n →
        {P : Ideal (𝓞 L) // P.IsPrime ∧
          P.LiesOver (SplitTransfer.rationalIdeal p)} := fun P ↦ by
      have hpP :=
        (SplitTransfer.under_eq_rationalIdeal_primeBelow L P.1.2.1 P.1.2.2).2
      have hnormP :=
        SplitTransfer.absNorm_eq_primeBelow_pow_residueDegree L P.1.2.1 P.1.2.2
      have hnorm0 :=
        SplitTransfer.absNorm_eq_primeBelow_pow_residueDegree L P₀.1.2.1 P₀.1.2.2
      have hfP : SplitTransfer.residueDegree L P.1.1 ≠ 0 :=
        Nat.ne_of_gt (residueDegree_pos L P.1)
      have hf0 : SplitTransfer.residueDegree L P₀.1.1 ≠ 0 :=
        Nat.ne_of_gt (residueDegree_pos L P₀.1)
      have hpow :
          SplitTransfer.primeBelow L P.1.1 ^ SplitTransfer.residueDegree L P.1.1 =
            p ^ SplitTransfer.residueDegree L P₀.1.1 := by
        rw [← hnormP, ← hnorm0, P.2, P₀.2]
      have hbelow : SplitTransfer.primeBelow L P.1.1 = p := by
        have hfac := congrArg Nat.primeFactors hpow
        simpa [Nat.primeFactors_prime_pow hfP hpP,
          Nat.primeFactors_prime_pow hf0 hp] using hfac
      refine ⟨P.1.1, P.1.2.1, ?_⟩
      have hunder :=
        (SplitTransfer.under_eq_rationalIdeal_primeBelow L P.1.2.1 P.1.2.2).1
      exact ⟨by rw [hunder, hbelow]⟩
    exact (Nat.card_le_card_of_injective f fun P Q h ↦ by
      apply Subtype.ext
      apply Subtype.ext
      exact congrArg (fun z : {P : Ideal (𝓞 L) // P.IsPrime ∧
        P.LiesOver (SplitTransfer.rationalIdeal p)} ↦ z.1) h).trans
          (SplitTransfer.card_primesAbove_le_degree L hp)
  · haveI : IsEmpty (primeNormFiber L n) := not_nonempty_iff.mp hne
    simp [primeNormMultiplicity, Nat.card_eq_zero]

end PrimeNormMultiplicity

/-- The strict partial sum of norm multiplicities is the inclusive
prime-ideal counting function at the preceding endpoint. -/
theorem coefficientCount_primeNormMultiplicity
    (K : Type*) [Field K] [NumberField K] (N : ℕ) :
    coefficientCount (primeNormMultiplicity K) (N + 1) =
      SplitTransfer.primeIdealCount K N := by
  classical
  have hfinite : ∀ n : ℕ,
      {P : PrimeIdeal K | Ideal.absNorm P.1 = n}.Finite := fun n ↦
    Set.Finite.preimage (f := fun P : PrimeIdeal K ↦ P.1)
      (fun _ _ _ _ ↦ Subtype.ext)
      (Ideal.finite_setOfPred_absNorm_eq (S := 𝓞 K) n)
  have key := Finset.card_preimage_eq_sum_card_image_eq
    (f := fun P : PrimeIdeal K ↦ Ideal.absNorm P.1)
    (s := Finset.range (N + 1)) (fun n _ ↦ hfinite n)
  have hpreimage :
      ((fun P : PrimeIdeal K ↦ Ideal.absNorm P.1) ⁻¹'
          (Finset.range (N + 1) : Set ℕ)) =
        {P : PrimeIdeal K | Ideal.absNorm P.1 ≤ N} := by
    ext P
    simp only [Set.mem_preimage, Finset.coe_range, Set.mem_Iio, Set.mem_ofPred_eq]
    omega
  rw [hpreimage] at key
  rw [coefficientCount, SplitTransfer.primeIdealCount]
  calc
    ∑ n ∈ Finset.range (N + 1), primeNormMultiplicity K n =
        Nat.card {P : PrimeIdeal K // Ideal.absNorm P.1 ≤ N} := by
      change
        (∑ n ∈ Finset.range (N + 1),
          Nat.card {P : PrimeIdeal K // Ideal.absNorm P.1 = n}) =
            Nat.card ↑({P : PrimeIdeal K | Ideal.absNorm P.1 ≤ N} : Set (PrimeIdeal K))
      rw [Nat.card_coe_set_eq]
      exact key.symm
    _ = Nat.card (SplitTransfer.PrimeIdealsUpTo K N) := by
      apply Nat.card_congr
      exact
        { toFun := fun P ↦ ⟨P.1.1, P.1.2.1, P.1.2.2, P.2⟩
          invFun := fun P ↦ ⟨⟨P.1, P.2.1, P.2.2.1⟩, P.2.2.2⟩
          left_inv := fun _ ↦ rfl
          right_inv := fun _ ↦ rfl }

end

end Erdos980.NaturalChebotarev.PrimeIdealTheorem
