/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos387.DivisorSwitching
import ErdosProblems.Erdos387.SimultaneousFourier

/-!
# Removing one coordinate from a tuple CRT residue

The medium and separated-prime arguments write a divisor tuple as
`d = D * dᵢ`, where `D` is the product of every coordinate except `i`.
This file constructs the corresponding residue `γ_D` and proves that the
full tuple residue is exactly the canonical simultaneous residue determined
by `γ_D (mod D)` and `i (mod dᵢ)`.
-/

namespace Erdos387

open scoped BigOperators

namespace TupleCertificate

/-- The residue of the full tuple reduced modulo the product of all
coordinates other than `i`.  Defining it by reduction makes its compatibility
with the already-established full CRT residue definitionally transparent. -/
noncomputable def otherResidue (C : TupleCertificate k X) (i : Fin k) : ℕ :=
  C.crtResidue % C.otherValue i

theorem otherValue_pos (C : TupleCertificate k X) (i : Fin k) :
    0 < C.otherValue i := by
  unfold otherValue
  exact Finset.prod_pos fun j _ => C.positive j

theorem factor_dvd_otherValue (C : TupleCertificate k X)
    {i j : Fin k} (hji : j ≠ i) :
    C.factor j ∣ C.otherValue i := by
  unfold otherValue
  exact Finset.dvd_prod_of_mem C.factor
    (Finset.mem_erase.mpr ⟨hji, Finset.mem_univ j⟩)

theorem factor_coprime_otherValue (C : TupleCertificate k X)
    (i : Fin k) :
    Nat.Coprime (C.factor i) (C.otherValue i) := by
  unfold otherValue
  apply Nat.Coprime.prod_right
  intro j hj
  exact C.pairwise i j (by
    intro hij
    subst j
    exact (Finset.mem_erase.mp hj).1 rfl)

theorem otherValue_coprime_factor (C : TupleCertificate k X)
    (i : Fin k) :
    Nat.Coprime (C.otherValue i) (C.factor i) :=
  (C.factor_coprime_otherValue i).symm

theorem otherResidue_lt_otherValue (C : TupleCertificate k X)
    (i : Fin k) :
    C.otherResidue i < C.otherValue i := by
  exact Nat.mod_lt _ (C.otherValue_pos i)

theorem crtResidue_modEq_otherResidue (C : TupleCertificate k X)
    (i : Fin k) :
    C.crtResidue ≡ C.otherResidue i [MOD C.otherValue i] := by
  exact (Nat.mod_modEq C.crtResidue (C.otherValue i)).symm

/-- The reduced residue still has every prescribed congruence away from the
removed coordinate. -/
theorem otherResidue_mod_factor (C : TupleCertificate k X)
    {i j : Fin k} (hji : j ≠ i) :
    C.otherResidue i ≡ j.val [MOD C.factor j] := by
  exact ((Nat.mod_modEq C.crtResidue (C.otherValue i)).of_dvd
    (C.factor_dvd_otherValue hji)).trans (C.crtResidue_mod_factor j)

theorem otherValue_mul_factor (C : TupleCertificate k X) (i : Fin k) :
    C.otherValue i * C.factor i = C.value := by
  rw [Nat.mul_comm]
  exact C.factor_mul_otherValue i

/-- The complementary CRT residue cannot collide with the removed index
modulo a prime factor of the complementary product.  This is the exact
coprimality assertion used before applying the incomplete Kloosterman bound
in Proposition 6.3. -/
theorem gcd_otherResidue_sub_index_otherValue_eq_one
    (C : TupleCertificate k X) (i : Fin k) (z : ℕ)
    (hkz : k ≤ z) (hrough : ∀ j : Fin k, IsZRough z (C.factor j)) :
    Int.gcd ((C.otherResidue i : ℤ) - i.val) (C.otherValue i : ℤ) = 1 := by
  apply CoverBPZ.int_gcd_eq_one_of_no_prime_common
  intro p hp hpDiff hpOther
  have hpOtherNat : p ∣ C.otherValue i := by
    exact_mod_cast hpOther
  unfold otherValue at hpOtherNat
  obtain ⟨j, hj, hpFactor⟩ :=
    (hp.prime.dvd_finsetProd_iff C.factor).mp hpOtherNat
  have hji : j ≠ i := (Finset.mem_erase.mp hj).1
  have hzp : z ≤ p := by
    by_contra hpz
    exact hrough j p hp (Nat.lt_of_not_ge hpz) hpFactor
  have hotherJ : C.otherResidue i ≡ j.val [MOD p] :=
    (C.otherResidue_mod_factor hji).of_dvd hpFactor
  have hotherI : C.otherResidue i ≡ i.val [MOD p] := by
    rw [Nat.modEq_iff_dvd]
    have hneg : (p : ℤ) ∣ -((C.otherResidue i : ℤ) - i.val) :=
      dvd_neg.mpr hpDiff
    simpa only [neg_sub] using hneg
  have hijMod : i.val ≡ j.val [MOD p] := hotherI.symm.trans hotherJ
  have hip : i.val < p := i.isLt.trans_le (hkz.trans hzp)
  have hjp : j.val < p := j.isLt.trans_le (hkz.trans hzp)
  exact hji (Fin.ext (hijMod.eq_of_lt_of_lt hip hjp).symm)

/-- Exact coordinate split of the canonical tuple residue. -/
theorem crtResidue_eq_simultaneousResidue_other
    (C : TupleCertificate k X) (i : Fin k) :
    C.crtResidue = simultaneousResidue
      (C.otherValue_coprime_factor i) (C.otherResidue i) i.val := by
  let hcop := C.otherValue_coprime_factor i
  have hcombined : C.crtResidue ≡
      simultaneousResidue hcop (C.otherResidue i) i.val
        [MOD C.otherValue i * C.factor i] :=
    Nat.chineseRemainder_modEq_unique hcop
      (C.crtResidue_modEq_otherResidue i)
      (C.crtResidue_mod_factor i)
  apply hcombined.eq_of_lt_of_lt
  · rw [C.otherValue_mul_factor i]
    exact C.crtResidue_lt_value
  · exact simultaneousResidue_lt hcop (C.otherValue_pos i)
      (C.positive i) (C.otherResidue i) i.val

/-- Fourier-ready version of the coordinate split: the full tuple phase is
the product of the inverse-twisted `dᵢ` phase and the complementary `D`
phase. -/
theorem stdAddChar_neg_mul_crtResidue_coordinate_split
    (C : TupleCertificate k X) (i : Fin k)
    [NeZero (C.otherValue i)] [NeZero (C.factor i)]
    (h : ZMod (C.otherValue i * C.factor i)) :
    ZMod.stdAddChar
        (-h * (C.crtResidue : ZMod (C.otherValue i * C.factor i))) =
      ZMod.stdAddChar
          (-(ZMod.chineseRemainder (C.otherValue_coprime_factor i) h).2 *
            (i.val : ZMod (C.factor i)) *
            (Nat.gcdA (C.otherValue i) (C.factor i) :
              ZMod (C.factor i))) *
        ZMod.stdAddChar
          (-(ZMod.chineseRemainder (C.otherValue_coprime_factor i) h).1 *
            (C.otherResidue i : ZMod (C.otherValue i)) *
            (Nat.gcdB (C.otherValue i) (C.factor i) :
              ZMod (C.otherValue i))) := by
  rw [C.crtResidue_eq_simultaneousResidue_other i]
  exact SimultaneousFourier.stdAddChar_neg_mul_simultaneousResidue
    (C.otherValue_coprime_factor i) (C.otherResidue i) i.val h

/-- Source-shaped reciprocity formula.  Apart from the harmless full-modulus
phase at the fixed residue `i`, the varying coordinate enters as the inverse
`gcdB D dᵢ` modulo the complementary product `D`. -/
theorem stdAddChar_mul_crtResidue_reciprocity
    (C : TupleCertificate k X) (i : Fin k)
    [NeZero (C.otherValue i)] [NeZero (C.factor i)]
    (h : ZMod (C.otherValue i * C.factor i)) :
    ZMod.stdAddChar
        (h * (C.crtResidue : ZMod (C.otherValue i * C.factor i))) =
      ZMod.stdAddChar
          ((ZMod.chineseRemainder (C.otherValue_coprime_factor i) h).1 *
            ((C.otherResidue i : ZMod (C.otherValue i)) -
              (i.val : ZMod (C.otherValue i))) *
            (Nat.gcdB (C.otherValue i) (C.factor i) :
              ZMod (C.otherValue i))) *
        ZMod.stdAddChar
          (h * (i.val : ZMod (C.otherValue i * C.factor i))) := by
  rw [C.crtResidue_eq_simultaneousResidue_other i]
  exact SimultaneousFourier.stdAddChar_mul_simultaneousResidue_reciprocity
    (C.otherValue_coprime_factor i) (C.otherResidue i) i.val h

end TupleCertificate

end Erdos387
