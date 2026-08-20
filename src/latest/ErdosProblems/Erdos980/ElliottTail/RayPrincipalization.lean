import Mathlib.NumberTheory.NumberField.ClassNumber
import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
import Mathlib.RingTheory.Ideal.Quotient.HasFiniteQuotients
import BernoulliRegular.Reflection.ResidueSymbol.Furtwaengler.EisensteinReciprocityBasic

/-!
# Finite ray-class principalization

This file supplies the elementary ray-class input needed in the odd-prime
part of Elliott's argument.  No ray class group is required.  We first choose
one ordinary ideal-class correction.  The unique power of the distinguished
prime `L` is removed from that correction by unique factorization of ideals.
The remaining congruence obstruction is a residue modulo `L ^ n`, hence has
only finitely many possibilities.
-/

open scoped NumberField nonZeroDivisors

namespace Erdos980.ElliottTail.RayPrincipalization

noncomputable section

section ClassCorrections

variable {R : Type*} [CommRing R] [IsDedekindDomain R]
  [Fintype (ClassGroup R)]

/-- A fixed nonzero integral ideal in the inverse of a prescribed ideal
class. -/
noncomputable def rawClassCorrection (c : ClassGroup R) : (Ideal R)⁰ :=
  Classical.choose (ClassGroup.mk0_surjective c⁻¹)

@[simp]
lemma mk0_rawClassCorrection (c : ClassGroup R) :
    ClassGroup.mk0 (rawClassCorrection c) = c⁻¹ :=
  Classical.choose_spec (ClassGroup.mk0_surjective c⁻¹)

variable (L : Ideal R) [L.IsMaximal]

/-- Remove the complete `L`-part from the ordinary class correction. -/
noncomputable def classCorrection (c : ClassGroup R) : Ideal R :=
  Classical.choose
    (Ideal.eq_prime_pow_mul_coprime
      (nonZeroDivisors.coe_ne_zero (rawClassCorrection c)) L)

lemma classCorrection_coprime (c : ClassGroup R) :
    L ⊔ classCorrection L c = ⊤ :=
  (Classical.choose_spec
    (Ideal.eq_prime_pow_mul_coprime
      (nonZeroDivisors.coe_ne_zero (rawClassCorrection c)) L)).1

lemma rawClassCorrection_eq_pow_mul_classCorrection (c : ClassGroup R) :
    (rawClassCorrection c : Ideal R) =
      L ^ Multiset.count L
        (UniqueFactorizationMonoid.normalizedFactors
          (rawClassCorrection c : Ideal R)) * classCorrection L c :=
  (Classical.choose_spec
    (Ideal.eq_prime_pow_mul_coprime
      (nonZeroDivisors.coe_ne_zero (rawClassCorrection c)) L)).2

lemma classCorrection_ne_bot (c : ClassGroup R) :
    classCorrection L c ≠ ⊥ := by
  intro h
  have hraw := rawClassCorrection_eq_pow_mul_classCorrection L c
  rw [h] at hraw
  rw [Ideal.mul_bot] at hraw
  exact nonZeroDivisors.coe_ne_zero (rawClassCorrection c) hraw

/-- Removing a power of a principal prime does not change the ideal class. -/
lemma mk0_classCorrection (hL0 : L ≠ ⊥) (hL : L.IsPrincipal)
    (c : ClassGroup R) :
    ClassGroup.mk0
        (⟨classCorrection L c,
          mem_nonZeroDivisors_iff_ne_zero.mpr
            (classCorrection_ne_bot L c)⟩ : (Ideal R)⁰) = c⁻¹ := by
  let e : ℕ := Multiset.count L
    (UniqueFactorizationMonoid.normalizedFactors
      (rawClassCorrection c : Ideal R))
  let L0 : (Ideal R)⁰ :=
    ⟨L, mem_nonZeroDivisors_iff_ne_zero.mpr
      hL0⟩
  let Q0 : (Ideal R)⁰ :=
    ⟨classCorrection L c,
      mem_nonZeroDivisors_iff_ne_zero.mpr
        (classCorrection_ne_bot L c)⟩
  have hLclass : ClassGroup.mk0 L0 = 1 := by
    exact (ClassGroup.mk0_eq_one_iff L0.2).2 hL
  have hpowclass : ClassGroup.mk0 (L0 ^ e) = 1 := by
    rw [map_pow, hLclass, one_pow]
  have hrawIdeal : (rawClassCorrection c : Ideal R) =
      ((L0 ^ e : (Ideal R)⁰) : Ideal R) * (Q0 : Ideal R) := by
    simpa [e, L0, Q0] using
      rawClassCorrection_eq_pow_mul_classCorrection L c
  have hrawSubtype : rawClassCorrection c = L0 ^ e * Q0 := by
    exact Subtype.ext hrawIdeal
  calc
    ClassGroup.mk0 Q0 = 1 * ClassGroup.mk0 Q0 := by simp
    _ = ClassGroup.mk0 (L0 ^ e) * ClassGroup.mk0 Q0 := by rw [hpowclass]
    _ = ClassGroup.mk0 (L0 ^ e * Q0) := by rw [map_mul]
    _ = ClassGroup.mk0 (rawClassCorrection c) := by rw [hrawSubtype]
    _ = c⁻¹ := mk0_rawClassCorrection c

/-- The fixed correction principalizes every ideal in the corresponding
ordinary ideal class. -/
lemma exists_generator_mul_classCorrection
    (hL0 : L ≠ ⊥) (hL : L.IsPrincipal) (P : (Ideal R)⁰) :
    ∃ a : R, a ≠ 0 ∧
      (P : Ideal R) * classCorrection L (ClassGroup.mk0 P) =
        Ideal.span {a} := by
  let Q0 : (Ideal R)⁰ :=
    ⟨classCorrection L (ClassGroup.mk0 P),
      mem_nonZeroDivisors_iff_ne_zero.mpr
        (classCorrection_ne_bot L (ClassGroup.mk0 P))⟩
  have hclass : ClassGroup.mk0 P = (ClassGroup.mk0 Q0)⁻¹ := by
    rw [mk0_classCorrection L hL0 hL (ClassGroup.mk0 P), inv_inv]
  obtain ⟨a, ha0, ha⟩ := ClassGroup.mk0_eq_mk0_inv_iff.mp hclass
  exact ⟨a, ha0, by simpa [Q0] using ha⟩

end ClassCorrections

section ResidueCorrections

variable {R : Type*} [CommRing R] [IsDedekindDomain R]
  [Fintype (ClassGroup R)]
variable (L : Ideal R) [L.IsMaximal] (n : ℕ)

/-- A fixed lift of a residue class. -/
noncomputable def residueLift (x : R ⧸ L ^ n) : R :=
  Classical.choose (Ideal.Quotient.mk_surjective x)

@[simp]
lemma mk_residueLift (x : R ⧸ L ^ n) :
    Ideal.Quotient.mk (L ^ n) (residueLift L n x) = x :=
  Classical.choose_spec (Ideal.Quotient.mk_surjective x)

/-- The finite indexing type for correction ideals.  The subtype condition
removes residue lifts divisible by the distinguished prime. -/
def RayCorrectionIndex :=
  {i : ClassGroup R × (R ⧸ L ^ n) //
    L ⊔ Ideal.span {residueLift L n i.2} = ⊤}

instance [Finite (R ⧸ L ^ n)] : Finite (RayCorrectionIndex L n) :=
  Finite.of_injective (fun i : RayCorrectionIndex L n ↦ i.1) Subtype.val_injective

noncomputable instance [Fintype (R ⧸ L ^ n)] :
    Fintype (RayCorrectionIndex L n) :=
  Fintype.ofFinite _

/-- The correction attached to an ordinary ideal class and a ray residue. -/
noncomputable def rayCorrection (i : RayCorrectionIndex L n) : Ideal R :=
  classCorrection L i.1.1 * Ideal.span {residueLift L n i.1.2}

lemma residueLift_ne_zero (i : RayCorrectionIndex L n) :
    residueLift L n i.1.2 ≠ 0 := by
  intro h
  have hi := i.2
  rw [h] at hi
  rw [Ideal.span_singleton_eq_bot.mpr rfl, sup_bot_eq] at hi
  exact (Ideal.IsMaximal.ne_top (I := L) inferInstance) hi

lemma rayCorrection_ne_bot (i : RayCorrectionIndex L n) :
    rayCorrection L n i ≠ ⊥ := by
  rw [rayCorrection]
  exact mul_ne_zero (classCorrection_ne_bot L i.1.1)
    ((Ideal.span_singleton_eq_bot.not).2 (residueLift_ne_zero L n i))

lemma rayCorrection_coprime (i : RayCorrectionIndex L n) :
    L ⊔ rayCorrection L n i = ⊤ := by
  rw [← Ideal.isCoprime_iff_sup_eq]
  exact (Ideal.isCoprime_iff_sup_eq.mpr
      (classCorrection_coprime L i.1.1)).mul_right
    (Ideal.isCoprime_iff_sup_eq.mpr i.2)

/-- Congruence-one ray principalization by one of a finite family of
corrections. -/
theorem exists_rayCorrection_generator
    (hn : n ≠ 0) (hL0 : L ≠ ⊥) (hL : L.IsPrincipal)
    (P : (Ideal R)⁰)
    (hPL : L ⊔ (P : Ideal R) = ⊤) :
    ∃ (i : RayCorrectionIndex L n) (a : R),
      a ≠ 0 ∧
      Ideal.span {a} = (P : Ideal R) * rayCorrection L n i ∧
      a - 1 ∈ L ^ n := by
  obtain ⟨a, ha0, ha⟩ :=
    exists_generator_mul_classCorrection L hL0 hL P
  have hLa : L ⊔ Ideal.span {a} = ⊤ := by
    rw [← ha, ← Ideal.isCoprime_iff_sup_eq]
    exact (Ideal.isCoprime_iff_sup_eq.mpr hPL).mul_right
      (Ideal.isCoprime_iff_sup_eq.mpr
        (classCorrection_coprime L (ClassGroup.mk0 P)))
  have hM : IsCoprime (L ^ n) (Ideal.span {a}) :=
    (Ideal.isCoprime_iff_sup_eq.mpr hLa).pow_left
  obtain ⟨m, hm, j, hj, hmj⟩ := Ideal.isCoprime_iff_exists.mp hM
  obtain ⟨u, rfl⟩ := Ideal.mem_span_singleton.mp hj
  let r : R ⧸ L ^ n := Ideal.Quotient.mk (L ^ n) u
  let v : R := residueLift L n r
  have hvu : v - u ∈ L ^ n := by
    rw [← Ideal.Quotient.eq]
    simpa [v, r] using mk_residueLift L n r
  have hau : a * u - 1 ∈ L ^ n := by
    have : a * u - 1 = -m := by rw [← hmj]; ring
    rw [this, Ideal.neg_mem_iff]
    exact hm
  have hav : a * v - 1 ∈ L ^ n := by
    have heq : a * v - 1 = a * (v - u) + (a * u - 1) := by ring
    rw [heq]
    exact (L ^ n).add_mem ((L ^ n).mul_mem_left a hvu) hau
  have hML : L ^ n ≤ L := Ideal.pow_le_self hn
  have hLv : L ⊔ Ideal.span {v} = ⊤ := by
    rw [← Ideal.isCoprime_iff_sup_eq, Ideal.isCoprime_iff_exists]
    refine ⟨-(a * v - 1), ?_, a * v, ?_, by ring⟩
    · exact L.neg_mem (hML hav)
    · exact Ideal.mem_span_singleton.mpr ⟨a, by ring⟩
  let i : RayCorrectionIndex L n :=
    ⟨(ClassGroup.mk0 P, r), by simpa [v] using hLv⟩
  have hilift : residueLift L n i.1.2 = v := rfl
  refine ⟨i, a * v, mul_ne_zero ha0 ?_, ?_, hav⟩
  · rw [← hilift]
    exact residueLift_ne_zero L n i
  · change Ideal.span {a * v} =
    (P : Ideal R) *
      (classCorrection L (ClassGroup.mk0 P) * Ideal.span {v})
    rw [← Ideal.span_singleton_mul_span_singleton, ← ha]
    ac_rfl

end ResidueCorrections

section Cyclotomic

open NumberField IsCyclotomicExtension
open BernoulliRegular

variable (p : ℕ) [Fact p.Prime]
  (K : Type*) [Field K] [NumberField K]
  [IsCyclotomicExtension {p} ℚ K]

local notation "lam" => FLT37.zetaSubOne p K
local notation "L" => Ideal.span ({lam} : Set (𝓞 K))

private lemma cyclotomic_lambdaIdeal_ne_bot : L ≠ ⊥ := by
  intro h
  exact FLT37.zetaSubOne_ne_zero p K
    (Ideal.span_singleton_eq_bot.mp h)

noncomputable local instance :
    (Ideal.span ({FLT37.zetaSubOne p K} : Set (𝓞 K))).IsMaximal :=
  (Ideal.isPrime_of_prime
    (Ideal.prime_span_singleton_iff.mpr
      (FLT37.zetaSubOne_prime p K))).isMaximal
        (cyclotomic_lambdaIdeal_ne_bot p K)

private lemma cyclotomic_modulus_ne_bot : L ^ (2 * p) ≠ ⊥ :=
  pow_ne_zero _ (cyclotomic_lambdaIdeal_ne_bot p K)

noncomputable local instance : Finite (𝓞 K ⧸ L ^ (2 * p)) :=
  Ring.HasFiniteQuotients.finiteQuotient (cyclotomic_modulus_ne_bot p K)

noncomputable local instance : Fintype (𝓞 K ⧸ L ^ (2 * p)) :=
  Fintype.ofFinite _

/-- The actual finite correction index used for the `p`-cyclotomic field. -/
abbrev CyclotomicRayCorrectionIndex := RayCorrectionIndex L (2 * p)

/-- The actual correction ideal used for the `p`-cyclotomic field. -/
noncomputable abbrev cyclotomicRayCorrection
    (i : CyclotomicRayCorrectionIndex p K) : Ideal (𝓞 K) :=
  rayCorrection L (2 * p) i

theorem cyclotomicRayCorrection_ne_bot
    (i : CyclotomicRayCorrectionIndex p K) :
    cyclotomicRayCorrection p K i ≠ ⊥ :=
  rayCorrection_ne_bot L (2 * p) i

theorem cyclotomicRayCorrection_coprime_lambda
    (i : CyclotomicRayCorrectionIndex p K) :
    L ⊔ cyclotomicRayCorrection p K i = ⊤ :=
  rayCorrection_coprime L (2 * p) i

/-- Every nonzero ideal away from `λ` is principalized by one member of a
fixed finite family, with a primary generator prime to the rational prime
`p`. -/
theorem exists_primary_generator_mul_cyclotomicRayCorrection
    (P : (Ideal (𝓞 K))⁰) (hPL : L ⊔ (P : Ideal (𝓞 K)) = ⊤) :
    ∃ (i : CyclotomicRayCorrectionIndex p K) (a : 𝓞 K),
      BernoulliRegular.FLT37.IsPrimary p (K := K) a ∧
      BernoulliRegular.Furtwaengler.IsPrimeToP (p := p) (K := K) a ∧
      Ideal.span {a} = (P : Ideal (𝓞 K)) *
        cyclotomicRayCorrection p K i := by
  have hn : 2 * p ≠ 0 := by
    exact mul_ne_zero (by decide) ((Fact.out : Nat.Prime p).ne_zero)
  have hLprincipal : Submodule.IsPrincipal
      (Ideal.span ({FLT37.zetaSubOne p K} : Set (𝓞 K))) :=
    ⟨lam, rfl⟩
  obtain ⟨i, a, ha0, ha, ha1⟩ :=
    exists_rayCorrection_generator L (2 * p) hn
      (cyclotomic_lambdaIdeal_ne_bot p K)
      hLprincipal P hPL
  refine ⟨i, a, ?_, ?_, ha⟩
  · refine ⟨1, ?_⟩
    rw [← Ideal.mem_span_singleton, ← Ideal.span_singleton_pow]
    simpa using ha1
  · refine ⟨ha0, ?_⟩
    have hLa : L ⊔ Ideal.span {a} = ⊤ := by
      rw [ha, ← Ideal.isCoprime_iff_sup_eq]
      exact (Ideal.isCoprime_iff_sup_eq.mpr hPL).mul_right
        (Ideal.isCoprime_iff_sup_eq.mpr
          (cyclotomicRayCorrection_coprime_lambda p K i))
    have hcop_lambda_a : IsCoprime lam a := by
      rw [← Ideal.isCoprime_span_singleton_iff]
      exact Ideal.isCoprime_iff_sup_eq.mpr hLa
    have hnot : ¬ lam ∣ a := by
      intro hdiv
      exact (FLT37.zetaSubOne_prime p K).not_isUnit
        (hcop_lambda_a.isUnit_of_dvd hdiv)
    have hcopa : IsCoprime (p : 𝓞 K) a :=
      IsCyclotomicExtension.Rat.isCoprime_of_not_zeta_sub_one_dvd
        p (zeta_spec p ℚ K) hnot
    change Ideal.span (Set.insert a ({(p : 𝓞 K)} : Set (𝓞 K))) = ⊤
    calc
      Ideal.span (Set.insert a ({(p : 𝓞 K)} : Set (𝓞 K))) =
          Ideal.span {a} ⊔ Ideal.span {(p : 𝓞 K)} :=
        Ideal.span_insert _ _
      _ = ⊤ := Ideal.isCoprime_iff_sup_eq.mp
        ((Ideal.isCoprime_span_singleton_iff (p : 𝓞 K) a).mpr hcopa).symm

end Cyclotomic

end

end Erdos980.ElliottTail.RayPrincipalization
