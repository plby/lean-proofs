/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

import Mathlib
import ErdosProblems.Erdos980.NaturalChebotarev.PrimeIdealTheorem.PrimeIdealCounting
import ErdosProblems.Erdos980.ElliottTail.IdealGeneratorCongruenceCount

/-!
# Finite power-class tensors for Elliott's medium sieve

This file contains the algebraic, finite part of the number-field larger
sieve used for Erdős problem 980.  An `ell`-th-power condition in a finite
residue field is encoded by the quotient of its unit group by the image of
the `ell`-th-power map.  When `ell` divides the order of the unit group and
is prime, that quotient has exactly `ell` elements.  Consequently `j`
independent residue coordinates form a tensor with exactly `ell ^ j`
classes, and a uniform fibre estimate has the exact geometric factor
`ell⁻ʲ` required in Elliott's argument.

The results are deliberately separated from the analytic ray-class large
sieve.  That input only has to bound all fibres of a map into the tensor;
the theorems below select the identity (all-power-residue) fibre and put its
main term into the form `ell⁻ʲ`.
-/

open scoped BigOperators nonZeroDivisors Pointwise

noncomputable section

namespace Erdos980.ElliottTail.NumberFieldLargerSieve

open NumberField

/-! ## Power classes of a finite cyclic group -/

/-- The quotient of a commutative group by its subgroup of `ell`-th powers. -/
abbrev PowerClass (G : Type*) [CommGroup G] (ell : ℕ) :=
  G ⧸ (powMonoidHom ell : G →* G).range

noncomputable instance powerClassFintype
    (G : Type*) [CommGroup G] [Finite G] (ell : ℕ) :
    Fintype (PowerClass G ell) :=
  Fintype.ofFinite _

/-- The class of an element modulo `ell`-th powers. -/
def powerClass {G : Type*} [CommGroup G] (ell : ℕ) (g : G) :
    PowerClass G ell :=
  QuotientGroup.mk' (powMonoidHom ell : G →* G).range g

/-- An element represents the identity power class exactly when it is an
`ell`-th power. -/
theorem powerClass_eq_one_iff {G : Type*} [CommGroup G] (ell : ℕ) (g : G) :
    powerClass ell g = 1 ↔ ∃ a : G, a ^ ell = g := by
  simp [powerClass, QuotientGroup.eq_one_iff, MonoidHom.mem_range]

/-- The number of power classes in a finite cyclic group is the gcd of the
group order with the exponent. -/
theorem natCard_powerClass (G : Type*) [CommGroup G] [Finite G] [IsCyclic G]
    (ell : ℕ) :
    Nat.card (PowerClass G ell) = (Nat.card G).gcd ell := by
  rw [← Subgroup.index_eq_card]
  exact IsCyclic.index_powMonoidHom_range G ell

/-- If `ell` divides the order of a finite cyclic group, there are exactly
`ell` power classes. -/
theorem natCard_powerClass_eq (G : Type*) [CommGroup G] [Finite G] [IsCyclic G]
    {ell : ℕ} (hell : ell ∣ Nat.card G) :
    Nat.card (PowerClass G ell) = ell := by
  rw [natCard_powerClass, Nat.gcd_eq_right_iff_dvd]
  exact hell

/-! ## Tensor products of local power classes -/

/-- A finite tuple of local power classes. -/
abbrev PowerClassTensor (I : Type*) (G : I → Type*)
    [∀ i, CommGroup (G i)] (ell : ℕ) :=
  ∀ i, PowerClass (G i) ell

/-- The class of a tuple, coordinate by coordinate. -/
def powerClassTensorOf {I : Type*} {G : I → Type*}
    [∀ i, CommGroup (G i)] (ell : ℕ) (g : ∀ i, G i) :
    PowerClassTensor I G ell :=
  fun i ↦ powerClass ell (g i)

/-- A tuple has trivial power class exactly when every coordinate is an
`ell`-th power. -/
theorem powerClassTensorOf_eq_one_iff
    {I : Type*} {G : I → Type*} [∀ i, CommGroup (G i)]
    (ell : ℕ) (g : ∀ i, G i) :
    powerClassTensorOf ell g = 1 ↔ ∀ i, ∃ a : G i, a ^ ell = g i := by
  constructor
  · intro h i
    exact (powerClass_eq_one_iff ell (g i)).mp (congrFun h i)
  · intro h
    funext i
    exact (powerClass_eq_one_iff ell (g i)).mpr (h i)

/-- Cardinality of a tensor of finite power-class quotients. -/
theorem natCard_powerClassTensor
    (I : Type*) [Fintype I] (G : I → Type*)
    [∀ i, CommGroup (G i)] [∀ i, Finite (G i)] [∀ i, IsCyclic (G i)]
    (ell : ℕ) :
    Nat.card (PowerClassTensor I G ell) =
      ∏ i, (Nat.card (G i)).gcd ell := by
  rw [Nat.card_pi]
  apply Finset.prod_congr rfl
  intro i _hi
  exact natCard_powerClass (G i) ell

/-- If every local unit-group order is divisible by `ell`, a tensor indexed
by `I` has exactly `ell ^ |I|` classes. -/
theorem natCard_powerClassTensor_eq_pow
    (I : Type*) [Fintype I] (G : I → Type*)
    [∀ i, CommGroup (G i)] [∀ i, Finite (G i)] [∀ i, IsCyclic (G i)]
    {ell : ℕ} (hell : ∀ i, ell ∣ Nat.card (G i)) :
    Nat.card (PowerClassTensor I G ell) = ell ^ Fintype.card I := by
  rw [natCard_powerClassTensor]
  simp_rw [Nat.gcd_eq_right_iff_dvd.mpr (hell _)]
  simp

/-! ## Residue quotients of ideals -/

/-- The `ell`-power class group of the units of an ideal quotient.  For a
nonzero prime ideal in a number ring the quotient is a finite field, so its
unit group is cyclic. -/
abbrev IdealPowerClass {R : Type*} [CommRing R] (P : Ideal R) (ell : ℕ) :=
  PowerClass (R ⧸ P)ˣ ell

/-- The tensor of local power classes attached to a finite family of ideals. -/
abbrev IdealPowerClassTensor {R : Type*} [CommRing R]
    (I : Type*) (P : I → Ideal R) (ell : ℕ) :=
  ∀ i, IdealPowerClass (P i) ell

/-- An ideal-residue unit represents the identity class precisely when it
is an `ell`-th power in that residue-field unit group. -/
theorem idealPowerClass_eq_one_iff {R : Type*} [CommRing R]
    (P : Ideal R) (ell : ℕ) (u : (R ⧸ P)ˣ) :
    powerClass ell u = (1 : IdealPowerClass P ell) ↔
      ∃ v : (R ⧸ P)ˣ, v ^ ell = u :=
  powerClass_eq_one_iff ell u

/-- Exact tensor cardinality for a family of finite cyclic ideal-residue
unit groups.  The hypotheses are automatic for finite-field quotients. -/
theorem natCard_idealPowerClassTensor_eq_pow
    {R : Type*} [CommRing R] (I : Type*) [Fintype I]
    (P : I → Ideal R) [∀ i, Finite (R ⧸ P i)]
    [∀ i, IsCyclic ((R ⧸ P i)ˣ)] {ell : ℕ}
    (hell : ∀ i, ell ∣ Nat.card ((R ⧸ P i)ˣ)) :
    Nat.card (IdealPowerClassTensor I P ell) = ell ^ Fintype.card I := by
  exact natCard_powerClassTensor_eq_pow I (fun i ↦ (R ⧸ P i)ˣ) hell

/-! ### Specialization to ideals in a number field -/

/-- For maximal ideals of a number ring, divisibility of `N(P) - 1` by
`ell` gives exactly `ell ^ |I|` local power-class patterns.  Finiteness,
the field structure on each quotient, and cyclicity of its unit group are
all supplied by Mathlib; they are not hypotheses of the statement. -/
theorem natCard_numberFieldIdealPowerClassTensor_eq_pow
    (K : Type*) [Field K] [NumberField K]
    (I : Type*) [Fintype I] (P : I → Ideal (𝓞 K))
    (hmax : ∀ i, (P i).IsMaximal) {ell : ℕ}
    (hell : ∀ i, ell ∣ Ideal.absNorm (P i) - 1) :
    Nat.card (IdealPowerClassTensor I P ell) = ell ^ Fintype.card I := by
  letI (i : I) : (P i).IsMaximal := hmax i
  letI (i : I) : Field ((𝓞 K) ⧸ P i) := Ideal.Quotient.field (P i)
  apply natCard_idealPowerClassTensor_eq_pow I P
  intro i
  rw [Nat.card_units, ← Submodule.cardQuot_apply,
    ← Ideal.absNorm_apply]
  exact hell i

/-! ## Fibres and the geometric `ell⁻ʲ` factor -/

/-- Elements of `S` having one prescribed tensor pattern. -/
noncomputable def tensorPatternFiber {A T : Type*} [DecidableEq A]
    (S : Finset A) (code : A → T) (pattern : T) : Finset A := by
  classical
  exact S.filter fun a ↦ code a = pattern

@[simp] theorem mem_tensorPatternFiber
    {A T : Type*} [DecidableEq A]
    {S : Finset A} {code : A → T} {pattern : T} {a : A} :
    a ∈ tensorPatternFiber S code pattern ↔ a ∈ S ∧ code a = pattern := by
  simp [tensorPatternFiber]

/-- The all-power-residue fibre of a tensor-valued code. -/
def allPowerResidueFiber {A I : Type*} [DecidableEq A] [Fintype I]
    {G : I → Type*} [∀ i, CommGroup (G i)]
    {ell : ℕ} (S : Finset A)
    (code : A → PowerClassTensor I G ell) : Finset A :=
  tensorPatternFiber S code 1

@[simp] theorem mem_allPowerResidueFiber
    {A I : Type*} [DecidableEq A] [Fintype I]
    {G : I → Type*} [∀ i, CommGroup (G i)]
    {ell : ℕ} {S : Finset A}
    {code : A → PowerClassTensor I G ell} {a : A} :
    a ∈ allPowerResidueFiber S code ↔ a ∈ S ∧ code a = 1 := by
  simp [allPowerResidueFiber]

/-- The all-power-residue subset when the local residue data are units in
ideal quotient rings.  In the Elliott application `A` is a finite set of
degree-one prime ideals (or the corresponding rational primes). -/
def numberFieldAllPowerResidueFiber
    {K : Type*} [Field K] [NumberField K]
    {A I : Type*} [DecidableEq A] [Fintype I]
    (P : I → Ideal (𝓞 K)) (ell : ℕ) (S : Finset A)
    (residueUnit : A → ∀ i, ((𝓞 K) ⧸ P i)ˣ) : Finset A :=
  allPowerResidueFiber S fun a ↦ powerClassTensorOf ell (residueUnit a)

/-- Membership in the number-field all-power-residue fibre is exactly the
simultaneous local `ell`-th-power condition. -/
theorem mem_numberFieldAllPowerResidueFiber_iff
    {K : Type*} [Field K] [NumberField K]
    {A I : Type*} [DecidableEq A] [Fintype I]
    {P : I → Ideal (𝓞 K)} {ell : ℕ} {S : Finset A}
    {residueUnit : A → ∀ i, ((𝓞 K) ⧸ P i)ˣ} {a : A} :
    a ∈ numberFieldAllPowerResidueFiber P ell S residueUnit ↔
      a ∈ S ∧ ∀ i, ∃ v : ((𝓞 K) ⧸ P i)ˣ,
        v ^ ell = residueUnit a i := by
  rw [numberFieldAllPowerResidueFiber, mem_allPowerResidueFiber]
  exact and_congr_right fun _ ↦
    powerClassTensorOf_eq_one_iff ell (residueUnit a)

/-- A uniform fibre estimate for a finite tensor.  This is the exact
interface supplied by the analytic ray-class larger sieve. -/
def UniformTensorFiberBound {A T : Type*} [DecidableEq A]
    (S : Finset A) (code : A → T) (main error : ℝ) : Prop :=
  ∀ pattern : T,
    ((tensorPatternFiber S code pattern).card : ℝ) ≤
      main / Nat.card T + error

/-! ## The finite Fourier certificate for tensor fibres -/

/-- The complex additive characters of the additive group underlying a
commutative multiplicative group. -/
abbrev TensorCharacter (T : Type*) [CommGroup T] := AddChar (Additive T) ℂ

/-- The character sum detecting one prescribed tensor pattern. -/
def tensorCharacterSum {A T : Type*} [DecidableEq A] [CommGroup T]
    (S : Finset A) (code : A → T) (pattern : T)
    (χ : TensorCharacter T) : ℂ :=
  ∑ a ∈ S, χ (Additive.ofMul (code a * pattern⁻¹))

/-- Character orthogonality gives an exact formula for every fibre.  This is
the finite Fourier certificate behind the ray-class tensor larger sieve. -/
theorem natCard_mul_tensorPatternFiber_card_eq_sum_characters
    {A T : Type*} [DecidableEq A] [CommGroup T] [Fintype T]
    (S : Finset A) (code : A → T) (pattern : T) :
    (Fintype.card T : ℂ) * (tensorPatternFiber S code pattern).card =
      ∑ χ : TensorCharacter T, tensorCharacterSum S code pattern χ := by
  classical
  simp_rw [tensorCharacterSum]
  rw [Finset.sum_comm]
  calc
    (Fintype.card T : ℂ) * (tensorPatternFiber S code pattern).card =
        ∑ a ∈ S, if code a = pattern then (Fintype.card T : ℂ) else 0 := by
      change (Fintype.card T : ℂ) *
          (S.filter fun a ↦ code a = pattern).card = _
      rw [← Finset.sum_filter]
      simp [mul_comm]
    _ = ∑ a ∈ S,
        if Additive.ofMul (code a * pattern⁻¹) = 0 then
          (Fintype.card (Additive T) : ℂ) else 0 := by
      apply Finset.sum_congr rfl
      intro a _ha
      have heq :
          Additive.ofMul (code a * pattern⁻¹) = 0 ↔ code a = pattern := by
        change code a * pattern⁻¹ = 1 ↔ code a = pattern
        exact mul_inv_eq_one
      by_cases h : code a = pattern
      · have hz : Additive.ofMul (code a * pattern⁻¹) = 0 := heq.mpr h
        rw [if_pos h, if_pos hz]
        norm_num
      · have hz : Additive.ofMul (code a * pattern⁻¹) ≠ 0 :=
          fun hz ↦ h (heq.mp hz)
        rw [if_neg h, if_neg hz]
    _ = ∑ a ∈ S, ∑ χ : TensorCharacter T,
        χ (Additive.ofMul (code a * pattern⁻¹)) := by
      apply Finset.sum_congr rfl
      intro a _ha
      rw [AddChar.sum_apply_eq_ite]
    _ = ∑ a ∈ S, ∑ χ : TensorCharacter T,
        χ (Additive.ofMul (code a * pattern⁻¹)) := rfl

/-- The trivial tensor character contributes exactly the cardinality of the
source set. -/
@[simp] theorem tensorCharacterSum_zero
    {A T : Type*} [DecidableEq A] [CommGroup T]
    (S : Finset A) (code : A → T) (pattern : T) :
    tensorCharacterSum S code pattern (0 : TensorCharacter T) = S.card := by
  simp [tensorCharacterSum]

/-- A denominator-free L¹ larger-sieve estimate for one tensor pattern.
All nontrivial ray-class character sums occur explicitly on the right. -/
theorem natCard_mul_tensorPatternFiber_card_le_card_add_characterError
    {A T : Type*} [DecidableEq A] [CommGroup T] [Fintype T]
    (S : Finset A) (code : A → T) (pattern : T) :
    (Fintype.card T : ℝ) * (tensorPatternFiber S code pattern).card ≤
      S.card + ∑ χ ∈ (Finset.univ : Finset (TensorCharacter T)).erase 0,
        ‖tensorCharacterSum S code pattern χ‖ := by
  classical
  have hexact := natCard_mul_tensorPatternFiber_card_eq_sum_characters
    S code pattern
  have hsplit :
      (∑ χ : TensorCharacter T, tensorCharacterSum S code pattern χ) =
        S.card + ∑ χ ∈ (Finset.univ : Finset (TensorCharacter T)).erase 0,
          tensorCharacterSum S code pattern χ := by
    calc
      (∑ χ : TensorCharacter T, tensorCharacterSum S code pattern χ) =
          (∑ χ ∈ (Finset.univ : Finset (TensorCharacter T)).erase 0,
            tensorCharacterSum S code pattern χ) +
            tensorCharacterSum S code pattern 0 :=
        (Finset.sum_erase_add (Finset.univ : Finset (TensorCharacter T))
          (fun χ ↦ tensorCharacterSum S code pattern χ)
          (Finset.mem_univ (0 : TensorCharacter T))).symm
      _ = S.card + ∑ χ ∈
          (Finset.univ : Finset (TensorCharacter T)).erase 0,
            tensorCharacterSum S code pattern χ := by
        rw [tensorCharacterSum_zero]
        ring
  rw [hsplit] at hexact
  have hnorm := norm_add_le
    (S.card : ℂ)
    (∑ χ ∈ (Finset.univ : Finset (TensorCharacter T)).erase 0,
      tensorCharacterSum S code pattern χ)
  have hsumNorm :
      ‖∑ χ ∈ (Finset.univ : Finset (TensorCharacter T)).erase 0,
          tensorCharacterSum S code pattern χ‖ ≤
        ∑ χ ∈ (Finset.univ : Finset (TensorCharacter T)).erase 0,
          ‖tensorCharacterSum S code pattern χ‖ :=
    norm_sum_le _ _
  have hleft :
      ‖((Fintype.card T : ℂ) *
          (tensorPatternFiber S code pattern).card)‖ =
        (Fintype.card T : ℝ) *
          (tensorPatternFiber S code pattern).card := by
    norm_num
  rw [← hexact, hleft, Complex.norm_natCast] at hnorm
  exact hnorm.trans (add_le_add le_rfl hsumNorm)

/-- An L¹ bound for all nontrivial tensor characters. -/
def TensorCharacterErrorBound
    {A T : Type*} [DecidableEq A] [CommGroup T] [Fintype T]
    (S : Finset A) (code : A → T) (error : ℝ) : Prop :=
  ∀ pattern : T,
    (∑ χ ∈ (Finset.univ : Finset (TensorCharacter T)).erase 0,
      ‖tensorCharacterSum S code pattern χ‖) ≤
        Fintype.card T * error

/-- The finite Fourier certificate converts an L¹ nontrivial-character
bound into the uniform tensor-fibre estimate consumed by the geometric
power-class theorems. -/
theorem uniformTensorFiberBound_of_characterError
    {A T : Type*} [DecidableEq A] [CommGroup T] [Fintype T]
    (S : Finset A) (code : A → T) {error : ℝ}
    (herror : TensorCharacterErrorBound S code error) :
    UniformTensorFiberBound S code S.card error := by
  intro pattern
  have hraw :=
    natCard_mul_tensorPatternFiber_card_le_card_add_characterError
      S code pattern
  have hcard : (0 : ℝ) < Fintype.card T := by positivity
  rw [Nat.card_eq_fintype_card]
  have hnormalize :
      (S.card : ℝ) / Fintype.card T + error =
        ((S.card : ℝ) + Fintype.card T * error) / Fintype.card T := by
    field_simp
  rw [hnormalize, le_div_iff₀ hcard]
  calc
    ((tensorPatternFiber S code pattern).card : ℝ) * Fintype.card T =
        Fintype.card T * (tensorPatternFiber S code pattern).card := by ring
    _ ≤ S.card + ∑ χ ∈
        (Finset.univ : Finset (TensorCharacter T)).erase 0,
          ‖tensorCharacterSum S code pattern χ‖ := hraw
    _ ≤ S.card + Fintype.card T * error :=
      add_le_add le_rfl (herror pattern)

/-! ## Explicit errors and finite correction fibres -/

/-- The normalized nontrivial-character contribution for one prescribed
tensor pattern.  Unlike `TensorCharacterErrorBound`, this is a concrete
finite sum, not a hypothesis. -/
noncomputable def tensorPatternCharacterError
    {A T : Type*} [DecidableEq A] [CommGroup T] [Fintype T]
    (S : Finset A) (code : A → T) (pattern : T) : ℝ :=
  (∑ χ ∈ (Finset.univ : Finset (TensorCharacter T)).erase 0,
      ‖tensorCharacterSum S code pattern χ‖) / Fintype.card T

theorem tensorPatternCharacterError_nonneg
    {A T : Type*} [DecidableEq A] [CommGroup T] [Fintype T]
    (S : Finset A) (code : A → T) (pattern : T) :
    0 ≤ tensorPatternCharacterError S code pattern := by
  unfold tensorPatternCharacterError
  positivity

/-- Character orthogonality gives an unconditional fibre estimate whose
error is the explicit normalized sum over nontrivial characters. -/
theorem tensorPatternFiber_card_le_card_div_add_characterError
    {A T : Type*} [DecidableEq A] [CommGroup T] [Fintype T]
    (S : Finset A) (code : A → T) (pattern : T) :
    ((tensorPatternFiber S code pattern).card : ℝ) ≤
      S.card / Fintype.card T +
        tensorPatternCharacterError S code pattern := by
  have hraw :=
    natCard_mul_tensorPatternFiber_card_le_card_add_characterError
      S code pattern
  have hcard : (0 : ℝ) < Fintype.card T := by positivity
  unfold tensorPatternCharacterError
  rw [← add_div]
  rw [le_div_iff₀ hcard]
  simpa [mul_comm] using hraw

/-- The part of `S` belonging to one finite correction index. -/
noncomputable def finiteCorrectionFiber
    {A C : Type*} [DecidableEq A] [Fintype C]
    (S : Finset A) (correction : A → C) (c : C) : Finset A := by
  classical
  exact S.filter fun a ↦ correction a = c

/-- A prescribed tensor pattern, after the tensor code is allowed to depend
on the finite correction attached to the source element. -/
noncomputable def correctedTensorPatternFiber
    {A C T : Type*} [DecidableEq A] [Fintype C]
    (S : Finset A) (correction : A → C) (code : C → A → T)
    (pattern : T) : Finset A := by
  classical
  exact S.filter fun a ↦ code (correction a) a = pattern

@[simp] theorem mem_finiteCorrectionFiber
    {A C : Type*} [DecidableEq A] [Fintype C]
    {S : Finset A} {correction : A → C} {c : C} {a : A} :
    a ∈ finiteCorrectionFiber S correction c ↔
      a ∈ S ∧ correction a = c := by
  simp [finiteCorrectionFiber]

@[simp] theorem mem_correctedTensorPatternFiber
    {A C T : Type*} [DecidableEq A] [Fintype C]
    {S : Finset A} {correction : A → C} {code : C → A → T}
    {pattern : T} {a : A} :
    a ∈ correctedTensorPatternFiber S correction code pattern ↔
      a ∈ S ∧ code (correction a) a = pattern := by
  simp [correctedTensorPatternFiber]

/-- The corrected pattern fibre is the disjoint union of its correction
fibres. -/
theorem correctedTensorPatternFiber_card_eq_sum
    {A C T : Type*} [DecidableEq A] [Fintype C]
    (S : Finset A) (correction : A → C) (code : C → A → T)
    (pattern : T) :
    (correctedTensorPatternFiber S correction code pattern).card =
      ∑ c : C,
        (tensorPatternFiber (finiteCorrectionFiber S correction c)
          (code c) pattern).card := by
  classical
  let F : C → Finset A := fun c ↦
    tensorPatternFiber (finiteCorrectionFiber S correction c)
      (code c) pattern
  have hpair : (↑(Finset.univ : Finset C) : Set C).PairwiseDisjoint F := by
    intro c _ d _ hcd
    change Disjoint (F c) (F d)
    rw [Finset.disjoint_left]
    intro a hac had
    change a ∈ tensorPatternFiber
      (finiteCorrectionFiber S correction c) (code c) pattern at hac
    change a ∈ tensorPatternFiber
      (finiteCorrectionFiber S correction d) (code d) pattern at had
    have hc : correction a = c :=
      (mem_finiteCorrectionFiber.mp
        (mem_tensorPatternFiber.mp hac).1).2
    have hd : correction a = d :=
      (mem_finiteCorrectionFiber.mp
        (mem_tensorPatternFiber.mp had).1).2
    exact hcd (hc.symm.trans hd)
  have hunion : (Finset.univ : Finset C).biUnion F =
      correctedTensorPatternFiber S correction code pattern := by
    ext a
    rw [Finset.mem_biUnion, mem_correctedTensorPatternFiber]
    constructor
    · rintro ⟨c, _hc, hac⟩
      change a ∈ tensorPatternFiber
        (finiteCorrectionFiber S correction c) (code c) pattern at hac
      obtain ⟨haf, hcode⟩ := mem_tensorPatternFiber.mp hac
      obtain ⟨haS, hac⟩ := mem_finiteCorrectionFiber.mp haf
      subst c
      exact ⟨haS, hcode⟩
    · rintro ⟨haS, hcode⟩
      refine ⟨correction a, Finset.mem_univ _, ?_⟩
      change a ∈ tensorPatternFiber
        (finiteCorrectionFiber S correction (correction a))
          (code (correction a)) pattern
      exact mem_tensorPatternFiber.mpr
        ⟨mem_finiteCorrectionFiber.mpr ⟨haS, rfl⟩, hcode⟩
  rw [← hunion]
  simpa [F] using Finset.card_biUnion hpair

/-- The correction fibres themselves partition the source. -/
theorem sum_finiteCorrectionFiber_card
    {A C : Type*} [DecidableEq A] [Fintype C]
    (S : Finset A) (correction : A → C) :
    ∑ c : C, (finiteCorrectionFiber S correction c).card = S.card := by
  classical
  simpa [finiteCorrectionFiber] using
    (Finset.sum_fiberwise S correction (fun _a ↦ (1 : ℕ))).trans
      (by simp)

/-- Finite ray-class correction costs no factor in the main term.  The
individual correction-fibre masses add back to `|S|`; only their explicit
nontrivial-character errors add. -/
theorem correctedTensorPatternFiber_card_le_explicitCharacterError
    {A C T : Type*} [DecidableEq A] [Fintype C]
    [CommGroup T] [Fintype T]
    (S : Finset A) (correction : A → C) (code : C → A → T)
    (pattern : T) :
    ((correctedTensorPatternFiber S correction code pattern).card : ℝ) ≤
      S.card / Fintype.card T +
        ∑ c : C, tensorPatternCharacterError
          (finiteCorrectionFiber S correction c) (code c) pattern := by
  rw [correctedTensorPatternFiber_card_eq_sum]
  push_cast
  calc
    (∑ c : C, ((tensorPatternFiber
        (finiteCorrectionFiber S correction c) (code c) pattern).card : ℝ)) ≤
        ∑ c : C, (((finiteCorrectionFiber S correction c).card : ℝ) /
          Fintype.card T + tensorPatternCharacterError
            (finiteCorrectionFiber S correction c) (code c) pattern) := by
      exact Finset.sum_le_sum fun c _ ↦
        tensorPatternFiber_card_le_card_div_add_characterError
          (finiteCorrectionFiber S correction c) (code c) pattern
    _ = S.card / Fintype.card T +
        ∑ c : C, tensorPatternCharacterError
          (finiteCorrectionFiber S correction c) (code c) pattern := by
      rw [Finset.sum_add_distrib, ← Finset.sum_div]
      rw [← Nat.cast_sum, sum_finiteCorrectionFiber_card]

/-! ## Exact finite residue-cell density -/

/-- The coordinatewise quotient map from full local unit residues to their
`ell`-power classes. -/
def powerClassTensorHom
    {I : Type*} {G : I → Type*} [∀ i, CommGroup (G i)] (ell : ℕ) :
    (∀ i, G i) →* PowerClassTensor I G ell where
  toFun := powerClassTensorOf ell
  map_one' := by
    funext i
    exact map_one (QuotientGroup.mk' (powMonoidHom ell : G i →* G i).range)
  map_mul' := by
    intro x y
    funext i
    exact map_mul (QuotientGroup.mk' (powMonoidHom ell : G i →* G i).range) (x i) (y i)

theorem powerClassTensorHom_surjective
    {I : Type*} {G : I → Type*} [∀ i, CommGroup (G i)] (ell : ℕ) :
    Function.Surjective (powerClassTensorHom (I := I) (G := G) ell) := by
  classical
  intro pattern
  choose g hg using fun i =>
    QuotientGroup.mk'_surjective
      (N := (powMonoidHom ell : G i →* G i).range) (pattern i)
  exact ⟨g, funext hg⟩

/-- The full unit-residue tuples realizing one prescribed tensor of local
`ell`-power classes.  Analytic congruence-cell estimates are summed over
exactly this finite set. -/
noncomputable def powerClassTensorResidueCell
    {I : Type*} [Fintype I] {G : I → Type*}
    [∀ i, CommGroup (G i)] [∀ i, Fintype (G i)]
    [Fintype (∀ i, G i)]
    (ell : ℕ) (pattern : PowerClassTensor I G ell) :
    Finset (∀ i, G i) := by
  classical
  exact tensorPatternFiber Finset.univ (powerClassTensorOf ell) pattern

/-- Every power-class pattern contains the same number of full unit-residue
tuples. -/
theorem powerClassTensorResidueCell_card_eq
    {I : Type*} [Fintype I] {G : I → Type*}
    [∀ i, CommGroup (G i)] [∀ i, Fintype (G i)]
    [Fintype (∀ i, G i)]
    (ell : ℕ) (p₁ p₂ : PowerClassTensor I G ell) :
    (powerClassTensorResidueCell (G := G) ell p₁).card =
      (powerClassTensorResidueCell (G := G) ell p₂).card := by
  classical
  let f := powerClassTensorHom (I := I) (G := G) ell
  obtain ⟨x, hx⟩ := powerClassTensorHom_surjective ell p₁
  obtain ⟨y, hy⟩ := powerClassTensorHom_surjective ell p₂
  let e : (∀ i, G i) ≃ (∀ i, G i) := Equiv.mulRight (x⁻¹ * y)
  apply Finset.card_bijective e e.bijective
  intro g
  simp only [powerClassTensorResidueCell, tensorPatternFiber,
    Finset.mem_filter, Finset.mem_univ, true_and]
  change f g = p₁ ↔ f (g * (x⁻¹ * y)) = p₂
  rw [map_mul, map_mul, map_inv, hx, hy]
  constructor
  · intro hg
    rw [hg]
    simp
  · intro h
    have h' : f g * p₁⁻¹ = 1 := by
      apply mul_right_cancel (b := p₂)
      simpa only [mul_assoc, one_mul] using h
    exact mul_inv_eq_one.mp h'

/-- Exact finite-cell main-term summation: the number of tensor patterns
times the number of full residue cells in any one pattern is the total
number of full unit-residue tuples. -/
theorem powerClassTensorResidueCell_card_mul
    {I : Type*} [Fintype I] {G : I → Type*}
    [∀ i, CommGroup (G i)] [∀ i, Fintype (G i)]
    [Fintype (∀ i, G i)]
    (ell : ℕ) [Fintype (PowerClassTensor I G ell)]
    (pattern : PowerClassTensor I G ell) :
    Fintype.card (PowerClassTensor I G ell) *
        (powerClassTensorResidueCell (G := G) ell pattern).card =
      Fintype.card (∀ i, G i) := by
  classical
  calc
    Fintype.card (PowerClassTensor I G ell) *
        (powerClassTensorResidueCell (G := G) ell pattern).card =
        ∑ p : PowerClassTensor I G ell,
          (powerClassTensorResidueCell (G := G) ell p).card := by
      have heq : ∀ p : PowerClassTensor I G ell,
          (powerClassTensorResidueCell (G := G) ell p).card =
            (powerClassTensorResidueCell (G := G) ell pattern).card :=
        fun p => powerClassTensorResidueCell_card_eq ell p pattern
      simp_rw [heq]
      simp
    _ = (Finset.univ : Finset (∀ i, G i)).card := by
      exact sum_finiteCorrectionFiber_card Finset.univ (powerClassTensorOf ell)
    _ = Fintype.card (∀ i, G i) := Finset.card_univ

/-- If every local cyclic unit group has order divisible by `ell`, then each
prescribed correction pattern contains exactly an `ell ^ (-|I|)` fraction of
all full residue tuples, stated integrally without division. -/
theorem ell_pow_mul_powerClassTensorResidueCell_card
    {I : Type*} [Fintype I] {G : I → Type*} {ell : ℕ}
    [∀ i, CommGroup (G i)] [∀ i, Fintype (G i)]
    [Fintype (∀ i, G i)]
    [Fintype (PowerClassTensor I G ell)]
    [∀ i, IsCyclic (G i)]
    (hell : ∀ i, ell ∣ Fintype.card (G i))
    (pattern : PowerClassTensor I G ell) :
    ell ^ Fintype.card I *
        (powerClassTensorResidueCell (G := G) ell pattern).card =
      Fintype.card (∀ i, G i) := by
  calc
    ell ^ Fintype.card I *
        (powerClassTensorResidueCell (G := G) ell pattern).card =
        Fintype.card (PowerClassTensor I G ell) *
          (powerClassTensorResidueCell (G := G) ell pattern).card := by
      congr 1
      symm
      rw [← Nat.card_eq_fintype_card]
      apply natCard_powerClassTensor_eq_pow
      intro i
      simpa only [Nat.card_eq_fintype_card] using hell i
    _ = Fintype.card (∀ i, G i) :=
      powerClassTensorResidueCell_card_mul ell pattern

/-- Transport an allowed tuple of local unit residues into the coordinate
residue vectors used by a generator-congruence count.  An embedding is used
because unit residue vectors generally form only a subset of all coordinate
vectors modulo the scalar modulus. -/
noncomputable def mappedPowerClassTensorResidueCell
    {I A : Type*} [Fintype I] {G : I → Type*}
    [∀ i, CommGroup (G i)] [∀ i, Fintype (G i)]
    [Fintype (∀ i, G i)]
    (e : (∀ i, G i) ↪ A) (ell : ℕ)
    (pattern : PowerClassTensor I G ell) : Finset A :=
  (powerClassTensorResidueCell (G := G) ell pattern).map e

@[simp] theorem card_mappedPowerClassTensorResidueCell
    {I A : Type*} [Fintype I] {G : I → Type*}
    [∀ i, CommGroup (G i)] [∀ i, Fintype (G i)]
    [Fintype (∀ i, G i)]
    (e : (∀ i, G i) ↪ A) (ell : ℕ)
    (pattern : PowerClassTensor I G ell) :
    (mappedPowerClassTensorResidueCell e ell pattern).card =
      (powerClassTensorResidueCell (G := G) ell pattern).card := by
  simp [mappedPowerClassTensorResidueCell]

theorem ell_pow_mul_mappedPowerClassTensorResidueCell_card
    {I A : Type*} [Fintype I] {G : I → Type*} {ell : ℕ}
    [∀ i, CommGroup (G i)] [∀ i, Fintype (G i)]
    [Fintype (∀ i, G i)]
    [Fintype (PowerClassTensor I G ell)]
    [∀ i, IsCyclic (G i)]
    (hell : ∀ i, ell ∣ Fintype.card (G i))
    (e : (∀ i, G i) ↪ A) (pattern : PowerClassTensor I G ell) :
    ell ^ Fintype.card I *
        (mappedPowerClassTensorResidueCell e ell pattern).card =
      Fintype.card (∀ i, G i) := by
  rw [card_mappedPowerClassTensorResidueCell]
  exact ell_pow_mul_powerClassTensorResidueCell_card hell pattern

open IdealGeneratorCongruenceCount

open Classical in
/-- Uniform growing-modulus generator count summed over any finite set of
full coordinate residue cells.  The main and boundary terms are multiplied
by the exact number of allowed cells; the theorem above supplies that number
as an `ell ^ (-j)` fraction for a power-class pattern. -/
theorem exists_uniform_sum_generatorCongruenceCell_count_growing_modulus
    (K : Type*) [Field K] [NumberField K]
    (J : (Ideal (𝓞 K))⁰) :
    ∃ C : ℝ, ∀ (m : ℕ) [NeZero m]
      (allowed : Finset (NumberField.mixedEmbedding.index K → ZMod m))
      (t : ℝ), (m : ℝ) ≤ t →
      |(∑ k ∈ allowed,
          (Nat.card ↑(generatorCongruenceCell J m k ∩
            t • generatorNormRegion K) : ℝ)) -
        (allowed.card : ℝ) *
          (MeasureTheory.volume.real (generatorNormRegion K) /
              |LinearMap.det (idealLatticeChart J :
                (NumberField.mixedEmbedding.index K → ℝ) →ₗ[ℝ]
                  (NumberField.mixedEmbedding.index K → ℝ))| *
            (t / m) ^ Fintype.card (NumberField.mixedEmbedding.index K))|
        ≤ (allowed.card : ℝ) * C *
          (t / m) ^ (Fintype.card (NumberField.mixedEmbedding.index K) - 1) := by
  obtain ⟨C, hC⟩ :=
    exists_uniform_generatorCongruenceCell_count_growing_modulus K J
  refine ⟨C, fun m _ allowed t hmt ↦ ?_⟩
  let main : ℝ :=
    MeasureTheory.volume.real (generatorNormRegion K) /
        |LinearMap.det (idealLatticeChart J :
          (NumberField.mixedEmbedding.index K → ℝ) →ₗ[ℝ]
            (NumberField.mixedEmbedding.index K → ℝ))| *
      (t / m) ^ Fintype.card (NumberField.mixedEmbedding.index K)
  let err : ℝ := C *
    (t / m) ^ (Fintype.card (NumberField.mixedEmbedding.index K) - 1)
  have hcell : ∀ k, k ∈ allowed →
      |(Nat.card ↑(generatorCongruenceCell J m k ∩
          t • generatorNormRegion K) : ℝ) - main| ≤ err := by
    intro k _hk
    simpa only [main, err] using hC m k t hmt
  have hrewrite :
      (∑ k ∈ allowed,
          (Nat.card ↑(generatorCongruenceCell J m k ∩
            t • generatorNormRegion K) : ℝ)) -
          (allowed.card : ℝ) * main =
        ∑ k ∈ allowed,
          ((Nat.card ↑(generatorCongruenceCell J m k ∩
            t • generatorNormRegion K) : ℝ) - main) := by
    rw [Finset.sum_sub_distrib]
    simp
  rw [hrewrite]
  calc
    |∑ k ∈ allowed,
        ((Nat.card ↑(generatorCongruenceCell J m k ∩
          t • generatorNormRegion K) : ℝ) - main)| ≤
        ∑ k ∈ allowed,
          |(Nat.card ↑(generatorCongruenceCell J m k ∩
            t • generatorNormRegion K) : ℝ) - main| := by
      exact Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _k ∈ allowed, err := by
      exact Finset.sum_le_sum fun k hk => hcell k hk
    _ = (allowed.card : ℝ) * err := by simp
    _ = (allowed.card : ℝ) * C *
          (t / m) ^ (Fintype.card (NumberField.mixedEmbedding.index K) - 1) := by
      dsimp [err]
      ring

/-! ## Prime-ideal scale with explicit character error -/

/-- Put the finite-correction Fourier estimate into prime-counting scale once
the tensor cardinality is known to be `ell ^ j`.  This generic form applies
directly to the correction-normalized symbol tensor `Q → ZMod ell`. -/
theorem correctedTensorPattern_card_le_primeScale_explicit
    {A C T : Type*} [DecidableEq A] [Fintype C]
    [CommGroup T] [Fintype T]
    {ell j x : ℕ} (S : Finset A) (correction : A → C)
    (code : C → A → T) {pattern : T} {B : ℝ}
    (hcard : Fintype.card T = ell ^ j)
    (hsource : (S.card : ℝ) ≤
      B * ((x : ℝ) / Real.log (x : ℝ))) :
    ((correctedTensorPatternFiber S correction code pattern).card : ℝ) ≤
      B * ((ell : ℝ)⁻¹) ^ j *
          ((x : ℝ) / Real.log (x : ℝ)) +
        ∑ c : C, tensorPatternCharacterError
          (finiteCorrectionFiber S correction c) (code c) pattern := by
  have hcore := correctedTensorPatternFiber_card_le_explicitCharacterError
    S correction code pattern
  rw [hcard] at hcore
  norm_num only [Nat.cast_pow] at hcore
  have hden : (0 : ℝ) ≤ (ell : ℝ) ^ j := by positivity
  calc
    ((correctedTensorPatternFiber S correction code pattern).card : ℝ) ≤
        (S.card : ℝ) / (ell : ℝ) ^ j +
          ∑ c : C, tensorPatternCharacterError
            (finiteCorrectionFiber S correction c) (code c) pattern := hcore
    _ ≤ (B * ((x : ℝ) / Real.log (x : ℝ))) /
          (ell : ℝ) ^ j +
          ∑ c : C, tensorPatternCharacterError
            (finiteCorrectionFiber S correction c) (code c) pattern := by
      exact add_le_add
        (div_le_div_of_nonneg_right hsource hden) le_rfl
    _ = B * ((ell : ℝ)⁻¹) ^ j *
          ((x : ℝ) / Real.log (x : ℝ)) +
        ∑ c : C, tensorPatternCharacterError
          (finiteCorrectionFiber S correction c) (code c) pattern := by
      rw [div_eq_mul_inv, inv_pow]
      ring

/-- A direct number-field specialization of the finite-correction theorem.
The only remainder is the displayed, concrete sum of nontrivial character
sums.  In particular this endpoint does not assume `UniformTensorFiberBound`.
-/
theorem numberFieldCorrectedPowerPattern_card_le_primeScale_explicit
    {K : Type*} [Field K] [NumberField K]
    {A C I : Type*} [DecidableEq A] [Fintype C] [Fintype I]
    (P : I → Ideal (𝓞 K)) (hmax : ∀ i, (P i).IsMaximal)
    {ell x : ℕ} (S : Finset A) (correction : A → C)
    (code : C → A → IdealPowerClassTensor I P ell)
    [Fintype (IdealPowerClassTensor I P ell)]
    {B : ℝ}
    (hell : ∀ i, ell ∣ Ideal.absNorm (P i) - 1)
    (hsource : (S.card : ℝ) ≤
      B * ((x : ℝ) / Real.log (x : ℝ))) :
    ((correctedTensorPatternFiber S correction code 1).card : ℝ) ≤
      B * ((ell : ℝ)⁻¹) ^ Fintype.card I *
          ((x : ℝ) / Real.log (x : ℝ)) +
        ∑ c : C, tensorPatternCharacterError
          (finiteCorrectionFiber S correction c) (code c) 1 := by
  letI (i : I) : (P i).IsMaximal := hmax i
  letI (i : I) : Field ((𝓞 K) ⧸ P i) := Ideal.Quotient.field (P i)
  have hcore := correctedTensorPatternFiber_card_le_explicitCharacterError
    S correction code (1 : IdealPowerClassTensor I P ell)
  have hcardNat :
      Fintype.card (IdealPowerClassTensor I P ell) =
        ell ^ Fintype.card I := by
    rw [← Nat.card_eq_fintype_card]
    exact natCard_numberFieldIdealPowerClassTensor_eq_pow K I P hmax hell
  rw [hcardNat] at hcore
  norm_num only [Nat.cast_pow] at hcore
  have hden : (0 : ℝ) ≤ (ell : ℝ) ^ Fintype.card I := by positivity
  calc
    ((correctedTensorPatternFiber S correction code 1).card : ℝ) ≤
        (S.card : ℝ) / (ell : ℝ) ^ Fintype.card I +
          ∑ c : C, tensorPatternCharacterError
            (finiteCorrectionFiber S correction c) (code c) 1 := hcore
    _ ≤ (B * ((x : ℝ) / Real.log (x : ℝ))) /
          (ell : ℝ) ^ Fintype.card I +
          ∑ c : C, tensorPatternCharacterError
            (finiteCorrectionFiber S correction c) (code c) 1 := by
      exact add_le_add
        (div_le_div_of_nonneg_right hsource hden) le_rfl
    _ = B * ((ell : ℝ)⁻¹) ^ Fintype.card I *
          ((x : ℝ) / Real.log (x : ℝ)) +
        ∑ c : C, tensorPatternCharacterError
          (finiteCorrectionFiber S correction c) (code c) 1 := by
      rw [div_eq_mul_inv, inv_pow]
      ring

open Filter
open scoped Topology

/-- The bounded prime-ideal subtype is finite; fix its canonical classical
`Fintype` structure for use as an actual finite sieve source. -/
noncomputable instance primeIdealsUpToFintype
    (K : Type*) [Field K] [NumberField K] (x : ℕ) :
    Fintype (NaturalChebotarev.SplitTransfer.PrimeIdealsUpTo K x) :=
  Fintype.ofFinite _

noncomputable instance primeIdealsUpToDecidableEq
    (K : Type*) [Field K] [NumberField K] (x : ℕ) :
    DecidableEq (NaturalChebotarev.SplitTransfer.PrimeIdealsUpTo K x) :=
  Classical.decEq _

/-- The finite source of all nonzero prime ideals with norm at most `x`,
packaged using the exact subtype counted by the prime ideal theorem. -/
noncomputable def primeIdealTensorSource
    (K : Type*) [Field K] [NumberField K] (x : ℕ) :
    Finset (NaturalChebotarev.SplitTransfer.PrimeIdealsUpTo K x) := by
  exact Finset.univ

@[simp] theorem card_primeIdealTensorSource
    (K : Type*) [Field K] [NumberField K] (x : ℕ) :
    (primeIdealTensorSource K x).card =
      NaturalChebotarev.SplitTransfer.primeIdealCount K x := by
  unfold primeIdealTensorSource
  rw [Finset.card_univ,
    NaturalChebotarev.SplitTransfer.primeIdealCount,
    Nat.card_eq_fintype_card]

/-- A uniform constant-two upper bound on the prime-ideal source, obtained
unconditionally from the prime ideal theorem already proved in this
repository. -/
theorem eventually_primeIdealTensorSource_card_le_two_mul_pntScale
    (K : Type*) [Field K] [NumberField K] :
    ∀ᶠ x : ℕ in atTop,
      ((primeIdealTensorSource K x).card : ℝ) ≤
        2 * ((x : ℝ) / Real.log (x : ℝ)) := by
  have hpnt :=
    Erdos980.NaturalChebotarev.PrimeIdealTheorem.primeIdealCount_isEquivalent_natCast_div_log K
  have herr := hpnt.isLittleO.def (show (0 : ℝ) < 1 by norm_num)
  filter_upwards [herr, eventually_ge_atTop 2] with x hxerr hx
  let scale : ℝ := (x : ℝ) / Real.log (x : ℝ)
  have hscale : 0 ≤ scale := by
    dsimp [scale]
    positivity
  have habs :
      |(NaturalChebotarev.SplitTransfer.primeIdealCount K x : ℝ) - scale| ≤
        scale := by
    simpa only [Pi.sub_apply, Real.norm_eq_abs, abs_of_nonneg hscale,
      one_mul, scale] using hxerr
  rw [card_primeIdealTensorSource]
  linarith [le_abs_self
    ((NaturalChebotarev.SplitTransfer.primeIdealCount K x : ℝ) - scale)]

/-- The unconditional PNT-scale endpoint for any correction-indexed tensor
whose cardinality is `ell ^ j`.  In the odd-prime bridge one takes
`T = Q → ZMod ell` and `j = |Q|`. -/
theorem eventually_primeIdealCorrectedTensorPattern_card_le
    {K : Type*} [Field K] [NumberField K]
    {C T : Type*} [Fintype C] [CommGroup T] [Fintype T]
    {ell j : ℕ} (hcard : Fintype.card T = ell ^ j)
    (correction : ∀ x,
      NaturalChebotarev.SplitTransfer.PrimeIdealsUpTo K x → C)
    (code : ∀ x, C →
      NaturalChebotarev.SplitTransfer.PrimeIdealsUpTo K x → T)
    (pattern : T) :
    ∀ᶠ x : ℕ in atTop,
      ((correctedTensorPatternFiber (primeIdealTensorSource K x)
          (correction x) (code x) pattern).card : ℝ) ≤
        2 * ((ell : ℝ)⁻¹) ^ j *
            ((x : ℝ) / Real.log (x : ℝ)) +
          ∑ c : C, tensorPatternCharacterError
            (finiteCorrectionFiber (primeIdealTensorSource K x)
              (correction x) c) (code x c) pattern := by
  filter_upwards [eventually_primeIdealTensorSource_card_le_two_mul_pntScale K]
    with x hx
  exact correctedTensorPattern_card_le_primeScale_explicit
    (primeIdealTensorSource K x) (correction x) (code x) hcard hx

/-- The unconditional prime-ideal endpoint for a family of finite-correction
tensor codes.  The prime ideal theorem supplies the factor `x / log x`, and
finite Fourier inversion supplies the exact factor `ell ^ (-|I|)`.  Thus the
only term left for an arithmetic larger-sieve argument is the displayed sum
of nontrivial tensor-character sums. -/
theorem eventually_primeIdealCorrectedPowerPattern_card_le
    {K : Type*} [Field K] [NumberField K]
    {C I : Type*} [Fintype C] [Fintype I]
    (P : I → Ideal (𝓞 K)) (hmax : ∀ i, (P i).IsMaximal)
    {ell : ℕ} [Fintype (IdealPowerClassTensor I P ell)]
    (hell : ∀ i, ell ∣ Ideal.absNorm (P i) - 1)
    (correction : ∀ x,
      NaturalChebotarev.SplitTransfer.PrimeIdealsUpTo K x → C)
    (code : ∀ x, C →
      NaturalChebotarev.SplitTransfer.PrimeIdealsUpTo K x →
        IdealPowerClassTensor I P ell) :
    ∀ᶠ x : ℕ in atTop,
      ((correctedTensorPatternFiber (primeIdealTensorSource K x)
          (correction x) (code x) 1).card : ℝ) ≤
        2 * ((ell : ℝ)⁻¹) ^ Fintype.card I *
            ((x : ℝ) / Real.log (x : ℝ)) +
          ∑ c : C, tensorPatternCharacterError
            (finiteCorrectionFiber (primeIdealTensorSource K x)
              (correction x) c) (code x c) 1 := by
  filter_upwards [eventually_primeIdealTensorSource_card_le_two_mul_pntScale K]
    with x hx
  exact numberFieldCorrectedPowerPattern_card_le_primeScale_explicit
    P hmax (primeIdealTensorSource K x) (correction x) (code x) hell hx

/-- Select the identity fibre from a uniform tensor-fibre estimate. -/
theorem allPowerResidueFiber_card_le_of_uniform
    {A I : Type*} [DecidableEq A] [Fintype I]
    {G : I → Type*} [∀ i, CommGroup (G i)]
    [∀ i, Finite (G i)] [∀ i, IsCyclic (G i)]
    {ell : ℕ}
    {S : Finset A} {code : A → PowerClassTensor I G ell}
    {main error : ℝ}
    (hbound : UniformTensorFiberBound S code main error)
    (hell : ∀ i, ell ∣ Nat.card (G i)) :
    ((allPowerResidueFiber S code).card : ℝ) ≤
      main / (ell : ℝ) ^ Fintype.card I + error := by
  have h := hbound (1 : PowerClassTensor I G ell)
  rw [natCard_powerClassTensor_eq_pow I G hell] at h
  exact_mod_cast h

/-- The same bound written with the geometric factor `(ell⁻¹)^|I|`. -/
theorem allPowerResidueFiber_card_le_geometric
    {A I : Type*} [DecidableEq A] [Fintype I]
    {G : I → Type*} [∀ i, CommGroup (G i)]
    [∀ i, Finite (G i)] [∀ i, IsCyclic (G i)]
    {ell : ℕ}
    {S : Finset A} {code : A → PowerClassTensor I G ell}
    {main error : ℝ}
    (hbound : UniformTensorFiberBound S code main error)
    (hell : ∀ i, ell ∣ Nat.card (G i)) :
    ((allPowerResidueFiber S code).card : ℝ) ≤
      main * ((ell : ℝ)⁻¹) ^ Fintype.card I + error := by
  have h := allPowerResidueFiber_card_le_of_uniform hbound hell
  simpa [div_pow, div_eq_mul_inv] using h

/-! ## A prime-counting-scale adapter -/

/-- A uniform ray-class fibre bound with main scale `x / log x` immediately
gives the exact `ell⁻ʲ x / log x` estimate for the all-power-residue class.
No positivity is needed for this purely algebraic normalization. -/
theorem allPowerResidueFiber_card_le_primeScale
    {A I : Type*} [DecidableEq A] [Fintype I]
    {G : I → Type*} [∀ i, CommGroup (G i)]
    [∀ i, Finite (G i)] [∀ i, IsCyclic (G i)]
    {ell : ℕ}
    {S : Finset A} {code : A → PowerClassTensor I G ell}
    {x : ℕ} {C error : ℝ}
    (hbound : UniformTensorFiberBound S code
      (C * ((x : ℝ) / Real.log (x : ℝ))) error)
    (hell : ∀ i, ell ∣ Nat.card (G i)) :
    ((allPowerResidueFiber S code).card : ℝ) ≤
      C * ((ell : ℝ)⁻¹) ^ Fintype.card I *
          ((x : ℝ) / Real.log (x : ℝ)) + error := by
  have h := allPowerResidueFiber_card_le_geometric hbound hell
  calc
    ((allPowerResidueFiber S code).card : ℝ) ≤
        (C * ((x : ℝ) / Real.log (x : ℝ))) *
          ((ell : ℝ)⁻¹) ^ Fintype.card I + error := h
    _ = C * ((ell : ℝ)⁻¹) ^ Fintype.card I *
          ((x : ℝ) / Real.log (x : ℝ)) + error := by ring

/-- Number-field ideal specialization of the prime-scale tensor estimate.
It turns a uniform ray-class fibre estimate into the desired simultaneous
power-residue count with the exact factor `ell⁻|I|`. -/
theorem numberFieldAllPowerResidueFiber_card_le_primeScale
    {K : Type*} [Field K] [NumberField K]
    {A I : Type*} [DecidableEq A] [Fintype I]
    (P : I → Ideal (𝓞 K)) (hmax : ∀ i, (P i).IsMaximal)
    {ell x : ℕ} (S : Finset A)
    (residueUnit : A → ∀ i, ((𝓞 K) ⧸ P i)ˣ)
    {C error : ℝ}
    (hell : ∀ i, ell ∣ Ideal.absNorm (P i) - 1)
    (hbound : UniformTensorFiberBound S
      (fun a ↦ powerClassTensorOf ell (residueUnit a))
      (C * ((x : ℝ) / Real.log (x : ℝ))) error) :
    ((numberFieldAllPowerResidueFiber P ell S residueUnit).card : ℝ) ≤
      C * ((ell : ℝ)⁻¹) ^ Fintype.card I *
          ((x : ℝ) / Real.log (x : ℝ)) + error := by
  letI (i : I) : (P i).IsMaximal := hmax i
  letI (i : I) : Field ((𝓞 K) ⧸ P i) := Ideal.Quotient.field (P i)
  have hell' : ∀ i, ell ∣ Nat.card (((𝓞 K) ⧸ P i)ˣ) := by
    intro i
    rw [Nat.card_units, ← Submodule.cardQuot_apply,
      ← Ideal.absNorm_apply]
    exact hell i
  simpa only [numberFieldAllPowerResidueFiber] using
    (allPowerResidueFiber_card_le_primeScale
      (G := fun i ↦ ((𝓞 K) ⧸ P i)ˣ) hbound hell')

end Erdos980.ElliottTail.NumberFieldLargerSieve
