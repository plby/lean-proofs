import ErdosProblems.Erdos240.External.Towers.NumberTheory.Locals.NewtonRootLifting
import Mathlib.Algebra.QuadraticAlgebra.Basic
import Mathlib.Algebra.Group.Subgroup.Even
import Mathlib.FieldTheory.KummerExtension
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.NumberTheory.Padics.RingHoms

/-!
# Milne, Chapter 7, Exercise 7-5

This file develops the square-class calculation underlying the classification
of the seven quadratic extensions of `ℚ_[2]`.
-/

namespace Towers.NumberTheory.Milne

open Polynomial

noncomputable section

local instance twoPrimeFact_5 : Fact (Nat.Prime 2) := ⟨by decide⟩

/-- A `2`-adic integer congruent to `1` modulo `8` is a square.  This is the
Newton-lifting step in Milne's solution of Exercise 7-5. -/
theorem padic_square_z
    (u : ℤ_[2]) (hu : PadicInt.toZModPow 3 u = 1) :
    IsSquare u := by
  let F : ℤ_[2][X] := X ^ 2 - C u
  have hF : F.aeval (1 : ℤ_[2]) = 1 - u := by
    simp [F]
  have hFd : F.derivative.aeval (1 : ℤ_[2]) = 2 := by
    norm_num [F, aeval_def]
  have hmem : 1 - u ∈ (Ideal.span {(2 : ℤ_[2]) ^ 3} : Ideal ℤ_[2]) := by
    change 1 - u ∈ (Ideal.span {((2 : ℕ) : ℤ_[2]) ^ 3} : Ideal ℤ_[2])
    rw [← PadicInt.ker_toZModPow 3, RingHom.mem_ker]
    rw [map_sub, map_one, hu, sub_self]
  have hvalue : ‖F.aeval (1 : ℤ_[2])‖ ≤ (2 : ℝ) ^ (-3 : ℤ) := by
    rw [hF]
    exact (PadicInt.norm_le_pow_iff_mem_span_pow (p := 2) (1 - u) 3).2 hmem
  have hderiv : ‖F.derivative.aeval (1 : ℤ_[2])‖ ^ 2 = (2 : ℝ) ^ (-2 : ℤ) := by
    rw [hFd]
    calc
      ‖(2 : ℤ_[2])‖ ^ 2 = ((2 : ℝ)⁻¹) ^ 2 :=
        congrArg (fun x : ℝ ↦ x ^ 2) (@PadicInt.norm_p 2 inferInstance)
      _ = (2 : ℝ) ^ (-2 : ℤ) := by norm_num [zpow_neg]
  have hnewton :
      ‖F.aeval (1 : ℤ_[2])‖ < ‖F.derivative.aeval (1 : ℤ_[2])‖ ^ 2 := by
    rw [hderiv]
    exact lt_of_le_of_lt hvalue (by norm_num [zpow_neg])
  obtain ⟨y, hy, -, -, -⟩ := padic_newton_root F 1 hnewton
  refine ⟨y, ?_⟩
  have : y ^ 2 - u = 0 := by simpa [F] using hy
  simpa [pow_two] using (sub_eq_zero.mp this).symm

private theorem padic_square_aux
    (u : ℤ_[2]ˣ) (a : ℤ) (ha : a ≠ 0)
    (hmod : PadicInt.toZModPow 3 ((u : ℤ_[2]) * (a : ℤ_[2])) = 1) :
    ∃ y : ℚ_[2], (u : ℚ_[2]) = a * y ^ 2 := by
  obtain ⟨y, hy⟩ :=
    padic_square_z
      ((u : ℤ_[2]) * (a : ℤ_[2])) hmod
  refine ⟨(y : ℚ_[2]) / (a : ℚ_[2]), ?_⟩
  have haq : (a : ℚ_[2]) ≠ 0 := by exact_mod_cast ha
  have hyq : (u : ℚ_[2]) * (a : ℚ_[2]) = (y : ℚ_[2]) * y := by
    exact congrArg (fun z : ℤ_[2] ↦ (z : ℚ_[2])) hy
  calc
    (u : ℚ_[2]) = ((u : ℚ_[2]) * a) / a := by field_simp
    _ = ((y : ℚ_[2]) * y) / a := by rw [hyq]
    _ = a * ((y : ℚ_[2]) / a) ^ 2 := by field_simp

/-- Every `2`-adic unit has square class represented by one of
`1, -1, 5, -5`. -/
theorem padic_square_class (u : ℤ_[2]ˣ) :
    ∃ a : ℤ, a ∈ ({1, -1, 5, -5} : Finset ℤ) ∧
      ∃ y : ℚ_[2], (u : ℚ_[2]) = a * y ^ 2 := by
  let r : (ZMod (2 ^ 3))ˣ := Units.map (PadicInt.toZModPow (p := 2) 3) u
  have hcast (a : ℤ) :
      PadicInt.toZModPow 3 (a : ℤ_[2]) = (a : ZMod 8) := by
    simp
  have hr :
      (r : ZMod 8) = 1 ∨ (r : ZMod 8) = 3 ∨
        (r : ZMod 8) = 5 ∨ (r : ZMod 8) = 7 := by
    have hall : ∀ s : (ZMod 8)ˣ,
        (s : ZMod 8) = 1 ∨ (s : ZMod 8) = 3 ∨
          (s : ZMod 8) = 5 ∨ (s : ZMod 8) = 7 := by decide
    exact hall r
  rcases hr with hr | hr | hr | hr
  · refine ⟨1, by simp, padic_square_aux u 1 (by norm_num) ?_⟩
    have hru : PadicInt.toZModPow 3 (u : ℤ_[2]) = 1 := by simpa [r] using hr
    rw [map_mul, hru, hcast]
    decide
  · refine ⟨-5, by simp, padic_square_aux u (-5) (by norm_num) ?_⟩
    have hru : PadicInt.toZModPow 3 (u : ℤ_[2]) = 3 := by simpa [r] using hr
    rw [map_mul, hru, hcast]
    decide
  · refine ⟨5, by simp, padic_square_aux u 5 (by norm_num) ?_⟩
    have hru : PadicInt.toZModPow 3 (u : ℤ_[2]) = 5 := by simpa [r] using hr
    rw [map_mul, hru, hcast]
    decide
  · refine ⟨-1, by simp, padic_square_aux u (-1) (by norm_num) ?_⟩
    have hru : PadicInt.toZModPow 3 (u : ℤ_[2]) = 7 := by simpa [r] using hr
    rw [map_mul, hru, hcast]
    decide

/-- The eight representatives in Milne's computation of
`ℚ_[2]ˣ / ℚ_[2]ˣ²`. -/
def padicSquareRepresentatives : Finset ℤ :=
  {1, -1, 5, -5, 2, -2, 10, -10}

/-- Every nonzero `2`-adic number is one of the eight standard representatives
times a square. -/
theorem padic_two_square (x : ℚ_[2]) (hx : x ≠ 0) :
    ∃ a : ℤ, a ∈ padicSquareRepresentatives ∧
      ∃ y : ℚ_[2], x = a * y ^ 2 := by
  let v : ℤ := x.valuation
  let uq : ℚ_[2] := x * (2 : ℚ_[2]) ^ (-v)
  have htwo : (2 : ℚ_[2]) ≠ 0 := by norm_num
  have huq0 : uq ≠ 0 := by
    exact mul_ne_zero hx (zpow_ne_zero _ htwo)
  have huqVal : uq.valuation = 0 := by
    have hvalTwo : Padic.valuation (2 : ℚ_[2]) = 1 := by
      change Padic.valuation (((2 : ℕ) : ℚ_[2])) = 1
      exact Padic.valuation_p
    rw [Padic.valuation_mul hx (zpow_ne_zero _ htwo), Padic.valuation_zpow,
      hvalTwo]
    dsimp [v]
    ring
  have huqNorm : ‖uq‖ = 1 := by
    rw [Padic.norm_eq_zpow_neg_valuation huq0, huqVal]
    simp
  let u : ℤ_[2]ˣ := PadicInt.mkUnits huqNorm
  obtain ⟨a, ha, y, hy⟩ := padic_square_class u
  have huq : (u : ℚ_[2]) = uq := PadicInt.mkUnits_eq huqNorm
  have hxDecomp : x = uq * (2 : ℚ_[2]) ^ v := by
    dsimp [uq]
    rw [mul_assoc, ← zpow_add₀ htwo, neg_add_cancel, zpow_zero, mul_one]
  obtain ⟨k, hk | hk⟩ := Int.even_or_odd' v
  · refine ⟨a, ?_, y * (2 : ℚ_[2]) ^ k, ?_⟩
    · simp only [padicSquareRepresentatives, Finset.mem_insert,
        Finset.mem_singleton] at ha ⊢
      omega
    · have hpow :
          (2 : ℚ_[2]) ^ (2 * k) = ((2 : ℚ_[2]) ^ k) ^ 2 := by
        rw [show 2 * k = k * 2 by ring, zpow_mul, zpow_ofNat]
      rw [hxDecomp, ← huq, hy, hk, hpow]
      ring
  · refine ⟨2 * a, ?_, y * (2 : ℚ_[2]) ^ k, ?_⟩
    · simp only [padicSquareRepresentatives, Finset.mem_insert,
        Finset.mem_singleton] at ha ⊢
      omega
    · have hpow :
          (2 : ℚ_[2]) ^ (2 * k) = ((2 : ℚ_[2]) ^ k) ^ 2 := by
        rw [show 2 * k = k * 2 by ring, zpow_mul, zpow_ofNat]
      rw [hxDecomp, ← huq, hy, hk, zpow_add₀ htwo, hpow, zpow_one]
      push_cast
      ring

private theorem padic_square_eight
    (a : ℤ) (ha0 : a ≠ 0) (hval : padicValInt 2 a = 0)
    (hmod : (a : ZMod 8) ≠ 1) :
    ¬IsSquare (a : ℚ_[2]) := by
  rintro ⟨y, hy⟩
  have hy0 : y ≠ 0 := by
    intro hy0
    subst y
    apply ha0
    have hazero : (a : ℚ_[2]) = 0 := by simpa using hy
    exact_mod_cast hazero
  have hv := congrArg Padic.valuation hy
  rw [Padic.valuation_intCast, hval, Padic.valuation_mul hy0 hy0] at hv
  have hyVal : y.valuation = 0 := by omega
  have hyNorm : ‖y‖ = 1 := by
    rw [Padic.norm_eq_zpow_neg_valuation hy0, hyVal]
    simp
  let u : ℤ_[2]ˣ := PadicInt.mkUnits hyNorm
  have hyInt : (a : ℤ_[2]) = (u : ℤ_[2]) * (u : ℤ_[2]) := by
    apply Subtype.ext
    change (a : ℚ_[2]) = (u : ℚ_[2]) * (u : ℚ_[2])
    simpa [u, PadicInt.mkUnits_eq] using hy
  have hmapped := congrArg (PadicInt.toZModPow (p := 2) 3) hyInt
  let r : (ZMod 8)ˣ := Units.map (PadicInt.toZModPow (p := 2) 3) u
  have hrsq : (r : ZMod 8) * r = 1 := by
    have hall : ∀ s : (ZMod 8)ˣ, (s : ZMod 8) * s = 1 := by decide
    exact hall r
  apply hmod
  have hcast : PadicInt.toZModPow 3 (a : ℤ_[2]) = (a : ZMod 8) := by simp
  rw [hcast] at hmapped
  calc
    (a : ZMod 8) = (r : ZMod 8) * r := by simpa [r] using hmapped
    _ = 1 := hrsq

private theorem square_odd_valuation
    (x : ℚ_[2]) (hx : x ≠ 0) (hodd : Odd x.valuation) :
    ¬IsSquare x := by
  rintro ⟨y, hy⟩
  have hy0 : y ≠ 0 := by
    intro hy0
    subst y
    apply hx
    simpa using hy
  have heven : Even x.valuation := by
    refine ⟨y.valuation, ?_⟩
    have hv := congrArg Padic.valuation hy
    rw [Padic.valuation_mul hy0 hy0] at hv
    omega
  rcases hodd with ⟨m, hm⟩
  rcases heven with ⟨n, hn⟩
  omega

/-- The seven nontrivial standard representatives are not squares in `ℚ_[2]`.
Together with `padic_two_square`, this gives the eight square classes
used in Milne's classification of the seven quadratic extensions. -/
theorem standa_repre_nonsq
    (a : ℤ) (ha : a ∈ ({-1, 5, -5, 2, -2, 10, -10} : Finset ℤ)) :
    ¬IsSquare (a : ℚ_[2]) := by
  simp only [Finset.mem_insert, Finset.mem_singleton] at ha
  rcases ha with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · apply padic_square_eight (-1) (by norm_num)
      (by norm_num [padicValInt])
    decide
  · apply padic_square_eight 5 (by norm_num)
      (by norm_num [padicValInt])
    decide
  · apply padic_square_eight (-5) (by norm_num)
      (by norm_num [padicValInt])
    decide
  · apply square_odd_valuation ((2 : ℤ) : ℚ_[2]) (by norm_num)
    rw [Padic.valuation_intCast]
    norm_num [padicValInt]
  · apply square_odd_valuation ((-2 : ℤ) : ℚ_[2]) (by norm_num)
    rw [Padic.valuation_intCast]
    norm_num [padicValInt]
  · apply square_odd_valuation ((10 : ℤ) : ℚ_[2]) (by norm_num)
    rw [Padic.valuation_intCast]
    have hv : padicValNat 2 10 = 1 := by
      change padicValNat 2 (2 * 5) = 1
      rw [padicValNat.mul (by norm_num) (by norm_num), padicValNat_self,
        padicValNat.eq_zero_of_not_dvd (by norm_num)]
    have hvInt : padicValInt 2 (10 : ℤ) = 1 := by
      simpa [padicValInt] using hv
    rw [hvInt]
    exact odd_one
  · apply square_odd_valuation ((-10 : ℤ) : ℚ_[2]) (by norm_num)
    rw [Padic.valuation_intCast]
    have hv : padicValNat 2 10 = 1 := by
      change padicValNat 2 (2 * 5) = 1
      rw [padicValNat.mul (by norm_num) (by norm_num), padicValNat_self,
        padicValNat.eq_zero_of_not_dvd (by norm_num)]
    have hvInt : padicValInt 2 (-10 : ℤ) = 1 := by
      simpa [padicValInt] using hv
    rw [hvInt]
    exact odd_one

private def adicBitXor : Bool → Bool → Bool
  | false, b => b
  | true, false => true
  | true, true => false

private theorem bit_xor_true (i j : Bool) :
    adicBitXor i j = true ↔ i ≠ j := by
  fin_cases i <;> fin_cases j <;> decide

private def adicBitRepresentative (i j k : Bool) : ℤ :=
  (-1) ^ i.toNat * 5 ^ j.toNat * 2 ^ k.toNat

private def adicBitCancel (g : ℚ_[2]) (i j : Bool) : ℚ_[2] :=
  if !i && j then g⁻¹ else 1

private theorem bit_representative_normalize
    (i j k i' j' k' : Bool) :
    IsSquare
      (((adicBitRepresentative i j k : ℤ) : ℚ_[2]) /
          (adicBitRepresentative i' j' k' : ℤ) /
        (adicBitRepresentative (adicBitXor i i')
          (adicBitXor j j') (adicBitXor k k') : ℤ)) := by
  refine ⟨adicBitCancel (-1) i i' * adicBitCancel 5 j j' *
    adicBitCancel 2 k k', ?_⟩
  fin_cases i <;> fin_cases j <;> fin_cases k <;>
    fin_cases i' <;> fin_cases j' <;> fin_cases k' <;>
      norm_num [adicBitRepresentative, adicBitXor, adicBitCancel]

private theorem adic_bit_representative (i j k : Bool) :
    ((adicBitRepresentative i j k : ℤ) : ℚ_[2]) ≠ 0 := by
  fin_cases i <;> fin_cases j <;> fin_cases k <;>
    norm_num [adicBitRepresentative]

set_option linter.flexible false in
private theorem bit_representative_nonsquare
    (i j k : Bool) (h : i = true ∨ j = true ∨ k = true) :
    ¬IsSquare ((adicBitRepresentative i j k : ℤ) : ℚ_[2]) := by
  fin_cases i <;> fin_cases j <;> fin_cases k <;>
    simp_all [adicBitRepresentative]
  all_goals
    apply standa_repre_nonsq
    simp

private theorem square_div
    {q c : ℚ_[2]} (hq0 : q ≠ 0) (hc0 : c ≠ 0)
    (hq : IsSquare q) (hqc : IsSquare (q / c)) :
    IsSquare c := by
  have h := hq.div hqc
  have heq : q / (q / c) = c := by field_simp
  rwa [heq] at h

/-- The three-bit representatives give distinct square classes. -/
theorem bit_representative_square
    (i j k i' j' k' : Bool)
    (h : IsSquare
      (((adicBitRepresentative i j k : ℤ) : ℚ_[2]) /
        (adicBitRepresentative i' j' k' : ℤ))) :
    i = i' ∧ j = j' ∧ k = k' := by
  by_contra hne
  let q : ℚ_[2] :=
    ((adicBitRepresentative i j k : ℤ) : ℚ_[2]) /
      (adicBitRepresentative i' j' k' : ℤ)
  let c : ℚ_[2] :=
    (adicBitRepresentative (adicBitXor i i')
      (adicBitXor j j') (adicBitXor k k') : ℤ)
  have hq0 : q ≠ 0 := by
    dsimp [q]
    exact div_ne_zero (adic_bit_representative i j k)
      (adic_bit_representative i' j' k')
  have hc0 : c ≠ 0 := by
    dsimp [c]
    exact adic_bit_representative _ _ _
  have hqSquare : IsSquare q := by simpa [q] using h
  have hquotSquare : IsSquare (q / c) := by
    simpa [q, c] using
      bit_representative_normalize i j k i' j' k'
  have hcSquare : IsSquare c := by
    exact square_div hq0 hc0 hqSquare hquotSquare
  have hxor :
      adicBitXor i i' = true ∨ adicBitXor j j' = true ∨
        adicBitXor k k' = true := by
    rw [bit_xor_true, bit_xor_true,
      bit_xor_true]
    tauto
  exact bit_representative_nonsquare _ _ _ hxor (by simpa [c] using hcSquare)

private theorem padic_square_representatives (a : ℤ) :
    a ∈ padicSquareRepresentatives ↔
      ∃ i j k : Bool, a = adicBitRepresentative i j k := by
  constructor
  · intro ha
    simp only [padicSquareRepresentatives, Finset.mem_insert,
      Finset.mem_singleton] at ha
    rcases ha with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact ⟨false, false, false, by decide⟩
    · exact ⟨true, false, false, by decide⟩
    · exact ⟨false, true, false, by decide⟩
    · exact ⟨true, true, false, by decide⟩
    · exact ⟨false, false, true, by decide⟩
    · exact ⟨true, false, true, by decide⟩
    · exact ⟨false, true, true, by decide⟩
    · exact ⟨true, true, true, by decide⟩
  · rintro ⟨i, j, k, rfl⟩
    fin_cases i <;> fin_cases j <;> fin_cases k <;>
      simp [padicSquareRepresentatives, adicBitRepresentative]

/-- The eight standard representatives are pairwise distinct modulo squares. -/
theorem square_representatives_injective
    {a b : ℤ} (ha : a ∈ padicSquareRepresentatives)
    (hb : b ∈ padicSquareRepresentatives)
    (h : IsSquare ((a : ℚ_[2]) / (b : ℚ_[2]))) :
    a = b := by
  obtain ⟨i, j, k, rfl⟩ :=
    (padic_square_representatives a).1 ha
  obtain ⟨i', j', k', rfl⟩ :=
    (padic_square_representatives b).1 hb
  obtain ⟨rfl, rfl, rfl⟩ :=
    bit_representative_square i j k i' j' k' h
  rfl

private theorem padic_square_representative
    {a : ℤ} (ha : a ∈ padicSquareRepresentatives) :
    (a : ℚ_[2]) ≠ 0 := by
  simp only [padicSquareRepresentatives, Finset.mem_insert,
    Finset.mem_singleton] at ha
  rcases ha with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    norm_num

/-- Milne's eight representatives surject onto the square-class group of
`ℚ_[2]`. -/
theorem square_representatives_surjective :
    Function.Surjective
      (fun a : ↑padicSquareRepresentatives =>
        QuotientGroup.mk
          (s := Subgroup.square ℚ_[2]ˣ)
          (Units.mk0 (a.1 : ℚ_[2])
            (padic_square_representative a.2))) := by
  intro q
  refine QuotientGroup.induction_on q ?_
  intro x
  obtain ⟨a, ha, y, hy⟩ := padic_two_square (x : ℚ_[2]) x.ne_zero
  have ha0 : (a : ℚ_[2]) ≠ 0 :=
    padic_square_representative ha
  have hy0 : y ≠ 0 := by
    intro hy0
    rw [hy0, zero_pow (by norm_num), mul_zero] at hy
    exact x.ne_zero hy
  refine ⟨⟨a, ha⟩, ?_⟩
  apply QuotientGroup.eq.mpr
  change IsSquare ((Units.mk0 (a : ℚ_[2]) ha0)⁻¹ * x)
  let yu : ℚ_[2]ˣ := Units.mk0 y hy0
  refine ⟨yu, Units.ext ?_⟩
  change (a : ℚ_[2])⁻¹ * (x : ℚ_[2]) = y * y
  rw [hy]
  field_simp

/-- The square-class group `ℚ_[2]ˣ / ℚ_[2]ˣ²` has at most eight elements. -/
theorem padic_square_card :
    Nat.card (ℚ_[2]ˣ ⧸ Subgroup.square ℚ_[2]ˣ) ≤ 8 := by
  calc
    Nat.card (ℚ_[2]ˣ ⧸ Subgroup.square ℚ_[2]ˣ) ≤
        Nat.card ↑padicSquareRepresentatives :=
      Nat.card_le_card_of_surjective _
        square_representatives_surjective
    _ = padicSquareRepresentatives.card := by
      rw [Nat.card_eq_fintype_card, Fintype.card_coe]
    _ = 8 := by norm_num [padicSquareRepresentatives]

/-- The seven radicands representing the quadratic extensions of `ℚ_[2]`. -/
def padicQuadraticRadicands : Finset ℤ :=
  {-1, 5, -5, 2, -2, 10, -10}

private theorem radicands_subset_representatives
    {a : ℤ} (ha : a ∈ padicQuadraticRadicands) :
    a ∈ padicSquareRepresentatives := by
  simp only [padicQuadraticRadicands, padicSquareRepresentatives,
    Finset.mem_insert, Finset.mem_singleton] at ha ⊢
  omega

/-- There are exactly seven standard nonsquare radicands. -/
theorem quadratic_radicands_card :
    padicQuadraticRadicands.card = 7 := by
  norm_num [padicQuadraticRadicands]

/-- Each standard quadratic radicand is a nonsquare in `ℚ_[2]`. -/
theorem quadratic_radicands_nonsquare
    {a : ℤ} (ha : a ∈ padicQuadraticRadicands) :
    ¬IsSquare (a : ℚ_[2]) := by
  exact standa_repre_nonsq a (by
    simpa [padicQuadraticRadicands] using ha)

/-- For each of the seven standard radicands, `X² - a` is irreducible over
`ℚ_[2]`, and hence adjoining one of its roots gives a quadratic field
extension. -/
theorem quadratic_radicand_irreducible
    {a : ℤ} (ha : a ∈ padicQuadraticRadicands) :
    Irreducible ((X : ℚ_[2][X]) ^ 2 - C (a : ℚ_[2])) := by
  apply X_pow_sub_C_irreducible_of_prime Nat.prime_two
  intro y hy
  apply quadratic_radicands_nonsquare ha
  refine ⟨y, ?_⟩
  change (a : ℚ_[2]) = y * y
  simpa [pow_two] using hy.symm

/-- Milne, Exercise 7-5, in square-class form: every nonsquare in `ℚ_[2]`
belongs to exactly one of the seven standard nonsquare classes.  Together
with `quadratic_radicand_irreducible`, these are precisely the seven
quadratic radical extensions listed in the exercise. -/
theorem padic_nonsquare_classification
    (x : ℚ_[2]) (hx : x ≠ 0) (hnsq : ¬IsSquare x) :
    ∃! a : ℤ, a ∈ padicQuadraticRadicands ∧
      IsSquare (x / (a : ℚ_[2])) := by
  obtain ⟨a, ha, y, hy⟩ := padic_two_square x hx
  have ha1 : a ≠ 1 := by
    intro ha1
    subst a
    apply hnsq
    exact ⟨y, by simpa [pow_two] using hy⟩
  have harad : a ∈ padicQuadraticRadicands := by
    simp only [padicSquareRepresentatives, Finset.mem_insert,
      Finset.mem_singleton] at ha
    simp only [padicQuadraticRadicands, Finset.mem_insert,
      Finset.mem_singleton]
    omega
  have ha0 : (a : ℚ_[2]) ≠ 0 := by
    simp only [padicQuadraticRadicands, Finset.mem_insert,
      Finset.mem_singleton] at harad
    rcases harad with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> norm_num
  refine ⟨a, ⟨harad, ?_⟩, ?_⟩
  · refine ⟨y, ?_⟩
    rw [hy]
    field_simp
  · intro b hb
    have hratio : IsSquare ((b : ℚ_[2]) / (a : ℚ_[2])) := by
      have h := (show IsSquare (x / (a : ℚ_[2])) from ⟨y, by
        rw [hy]
        field_simp⟩).div hb.2
      simpa only [div_div_div_cancel_left' _ _ hx] using h
    have hbRep : b ∈ padicSquareRepresentatives := by
      simp only [padicSquareRepresentatives,
        padicQuadraticRadicands, Finset.mem_insert,
        Finset.mem_singleton] at hb ⊢
      tauto
    have haRep : a ∈ padicSquareRepresentatives := by
      simp only [padicSquareRepresentatives,
        padicQuadraticRadicands, Finset.mem_insert,
        Finset.mem_singleton] at harad ⊢
      tauto
    exact square_representatives_injective
      (a := b) (b := a) hbRep haRep hratio

/-- The quadratic field obtained by adjoining a square root of one of the
seven standard radicands. -/
abbrev AdicQuadraticExtension (a : ↑padicQuadraticRadicands) :=
  QuadraticAlgebra ℚ_[2] (a.1 : ℚ_[2]) 0

noncomputable instance adicQuadraticNonsquare
    (a : ↑padicQuadraticRadicands) :
    Fact (∀ r : ℚ_[2], r ^ 2 ≠ (a.1 : ℚ_[2]) + 0 * r) := by
  refine ⟨fun r hr ↦ ?_⟩
  apply quadratic_radicands_nonsquare a.2
  exact ⟨r, by simpa [pow_two] using hr.symm⟩

noncomputable instance adicQuadraticExtension
    (a : ↑padicQuadraticRadicands) :
    Algebra.IsQuadraticExtension ℚ_[2] (AdicQuadraticExtension a) where
  finrank_eq_two' := QuadraticAlgebra.finrank_eq_two (a.1 : ℚ_[2]) 0

private theorem quadratic_alg_sq
    {K : Type*} [Field K] {a b u : K}
    (ha : ∀ r : K, r ^ 2 ≠ a) (hb : ∀ r : K, r ^ 2 ≠ b)
    (hab : a = b * u ^ 2) :
    Nonempty (QuadraticAlgebra K a 0 ≃ₐ[K] QuadraticAlgebra K b 0) := by
  letI : Fact (∀ r : K, r ^ 2 ≠ a + 0 * r) := ⟨by simpa using ha⟩
  letI : Fact (∀ r : K, r ^ 2 ≠ b + 0 * r) := ⟨by simpa using hb⟩
  let φ : QuadraticAlgebra K a 0 →ₐ[K] QuadraticAlgebra K b 0 :=
    QuadraticAlgebra.lift ⟨u • QuadraticAlgebra.omega, by
      rw [smul_mul_smul, QuadraticAlgebra.omega_mul_omega_eq_add]
      rw [hab, pow_two]
      simp [smul_smul]
      ring⟩
  have hφinj : Function.Injective φ := φ.injective
  have hdim :
      Module.finrank K (QuadraticAlgebra K a 0) =
        Module.finrank K (QuadraticAlgebra K b 0) := by
    rw [QuadraticAlgebra.finrank_eq_two a 0,
      QuadraticAlgebra.finrank_eq_two b 0]
  have hφsurj : Function.Surjective φ :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
      hdim (f := φ.toLinearMap)).mp hφinj
  exact ⟨AlgEquiv.ofBijective φ ⟨hφinj, hφsurj⟩⟩

/-- Every quadratic square-root extension of `ℚ_[2]` is isomorphic to one
of the seven standard models. -/
theorem padic_quadratic_exhaustive
    (d : ℚ_[2]) (hd : ¬IsSquare d) :
    ∃ a : ↑padicQuadraticRadicands,
      Nonempty
        (QuadraticAlgebra ℚ_[2] d 0 ≃ₐ[ℚ_[2]] AdicQuadraticExtension a) := by
  have hd0 : d ≠ 0 := by
    intro hd0
    apply hd
    exact ⟨0, by simp [hd0]⟩
  obtain ⟨a, ha, y, hy⟩ := padic_two_square d hd0
  have ha1 : a ≠ 1 := by
    intro ha1
    subst a
    apply hd
    exact ⟨y, by simpa [pow_two] using hy⟩
  have haSeven : a ∈ padicQuadraticRadicands := by
    simp only [padicSquareRepresentatives, Finset.mem_insert,
      Finset.mem_singleton] at ha
    simp only [padicQuadraticRadicands, Finset.mem_insert,
      Finset.mem_singleton]
    omega
  let a' : ↑padicQuadraticRadicands := ⟨a, haSeven⟩
  refine ⟨a', quadratic_alg_sq (u := y) ?_ ?_ ?_⟩
  · intro r hr
    apply hd
    exact ⟨r, by simpa [pow_two] using hr.symm⟩
  · intro r hr
    exact (adicQuadraticNonsquare a').out r (by simpa using hr)
  · simpa [a', pow_two] using hy

private theorem padic_square_div
    {a b : ℚ_[2]} (ha : ¬IsSquare a) (hb : ¬IsSquare b)
    (e : QuadraticAlgebra ℚ_[2] a 0 ≃ₐ[ℚ_[2]]
      QuadraticAlgebra ℚ_[2] b 0) :
    IsSquare (a / b) := by
  let z : QuadraticAlgebra ℚ_[2] b 0 := e QuadraticAlgebra.omega
  have hzsq : z * z = algebraMap ℚ_[2] (QuadraticAlgebra ℚ_[2] b 0) a := by
    dsimp [z]
    rw [← map_mul, QuadraticAlgebra.omega_mul_omega_eq_add]
    simp [Algebra.smul_def]
  have hcoord := congrArg QuadraticAlgebra.im hzsq
  have hcoord' : z.re * z.im + z.im * z.re = 0 := by
    simpa using hcoord
  have hzim : z.im ≠ 0 := by
    intro hzim
    apply ha
    refine ⟨z.re, ?_⟩
    have hre := congrArg QuadraticAlgebra.re hzsq
    simp only [QuadraticAlgebra.re_mul, QuadraticAlgebra.algebraMap_re] at hre
    simpa [hzim, pow_two] using hre.symm
  have hzre : z.re = 0 := by
    have htwo : (2 : ℚ_[2]) ≠ 0 := by norm_num
    have hriTwo : (2 : ℚ_[2]) * (z.re * z.im) = 0 := by
      calc
        (2 : ℚ_[2]) * (z.re * z.im) =
            z.re * z.im + z.im * z.re := by ring
        _ = 0 := hcoord'
    have hri : z.re * z.im = 0 :=
      (mul_eq_zero.mp hriTwo).resolve_left htwo
    exact (mul_eq_zero.mp hri).resolve_right hzim
  have hb0 : b ≠ 0 := by
    intro hb0
    apply hb
    exact ⟨0, by simp [hb0]⟩
  have hab : a = b * z.im ^ 2 := by
    have hre := congrArg QuadraticAlgebra.re hzsq
    simp only [QuadraticAlgebra.re_mul, QuadraticAlgebra.algebraMap_re] at hre
    simpa [hzre, pow_two, mul_assoc] using hre.symm
  refine ⟨z.im, ?_⟩
  rw [hab]
  field_simp

/-- The seven standard quadratic extensions are pairwise nonisomorphic as
`ℚ_[2]`-algebras. -/
theorem adic_quadratic_injective
    (a b : ↑padicQuadraticRadicands)
    (e : AdicQuadraticExtension a ≃ₐ[ℚ_[2]]
      AdicQuadraticExtension b) :
    a = b := by
  apply Subtype.ext
  apply square_representatives_injective
  · exact radicands_subset_representatives a.2
  · exact radicands_subset_representatives b.2
  · exact padic_square_div
      (quadratic_radicands_nonsquare a.2)
      (quadratic_radicands_nonsquare b.2) e

/-- Milne, Exercise 7-5: every quadratic extension of `ℚ_[2]` is
isomorphic to one of the seven standard extensions. -/
theorem padic_quadratic_classification
    (L : Type*) [Field L] [Algebra ℚ_[2] L]
    [Algebra.IsQuadraticExtension ℚ_[2] L] :
    ∃ a : ↑padicQuadraticRadicands,
      Nonempty (L ≃ₐ[ℚ_[2]] AdicQuadraticExtension a) := by
  have hroots : (primitiveRoots 2 ℚ_[2]).Nonempty := by
    refine ⟨-1, ?_⟩
    rw [mem_primitiveRoots (by norm_num)]
    exact IsPrimitiveRoot.neg_one 0 (by norm_num)
  have hfin : Module.finrank ℚ_[2] L = 2 :=
    Algebra.IsQuadraticExtension.finrank_eq_two ℚ_[2] L
  have hcyclic : IsGalois ℚ_[2] L ∧ IsCyclic Gal(L/ℚ_[2]) :=
    ⟨inferInstance, inferInstance⟩
  obtain ⟨α, hαpow, hαadjoin⟩ :=
    ((isCyclic_tfae ℚ_[2] L (by simpa [hfin] using hroots)).out 0 2).mp hcyclic
  obtain ⟨d, hd⟩ := hαpow
  have hpow : α ^ 2 = algebraMap ℚ_[2] L d := by
    simpa [hfin] using hd.symm
  have hirr : Irreducible ((X : ℚ_[2][X]) ^ 2 - C d) := by
    simpa [hfin] using
      (irreducible_X_pow_sub_C_of_root_adjoin_eq_top
        (by simpa [hfin] using hpow) hαadjoin)
  have hdnsq : ¬IsSquare d := by
    rintro ⟨r, hr⟩
    have h := (X_pow_sub_C_irreducible_iff_of_prime Nat.prime_two).1 hirr r
    exact h (by simpa [pow_two] using hr.symm)
  letI : Fact (∀ r : ℚ_[2], r ^ 2 ≠ d + 0 * r) := ⟨by
    intro r hr
    apply hdnsq
    exact ⟨r, by simpa [pow_two] using hr.symm⟩⟩
  let φ : QuadraticAlgebra ℚ_[2] d 0 →ₐ[ℚ_[2]] L :=
    QuadraticAlgebra.lift ⟨α, by
      simpa [Algebra.smul_def, pow_two] using hpow⟩
  have hφinj : Function.Injective φ := φ.injective
  have hφrange : φ.range = ⊤ := by
    apply top_unique
    have hadjoin : Algebra.adjoin ℚ_[2] {α} = ⊤ := by
      rw [← IntermediateField.top_toSubalgebra, ← hαadjoin,
        IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic
          (IsAlgebraic.of_finite ℚ_[2] α)]
    rw [← hadjoin]
    apply Algebra.adjoin_le
    rw [Set.singleton_subset_iff]
    refine ⟨QuadraticAlgebra.omega, ?_⟩
    simp [φ]
  have hφsurj : Function.Surjective φ :=
    (AlgHom.range_eq_top φ).mp hφrange
  let e : QuadraticAlgebra ℚ_[2] d 0 ≃ₐ[ℚ_[2]] L :=
    AlgEquiv.ofBijective φ ⟨hφinj, hφsurj⟩
  obtain ⟨a, ⟨ea⟩⟩ := padic_quadratic_exhaustive d hdnsq
  exact ⟨a, ⟨e.symm.trans ea⟩⟩

/-- There are exactly seven quadratic extensions of `ℚ_[2]` up to
`ℚ_[2]`-algebra equivalence. -/
theorem padic_unique_model
    (L : Type*) [Field L] [Algebra ℚ_[2] L]
    [Algebra.IsQuadraticExtension ℚ_[2] L] :
    ∃! a : ↑padicQuadraticRadicands,
      Nonempty (L ≃ₐ[ℚ_[2]] AdicQuadraticExtension a) := by
  obtain ⟨a, ⟨ea⟩⟩ := padic_quadratic_classification L
  refine ⟨a, ⟨ea⟩, ?_⟩
  intro b hb
  obtain ⟨eb⟩ := hb
  exact (adic_quadratic_injective a b
    (ea.symm.trans eb)).symm

end

end Towers.NumberTheory.Milne
