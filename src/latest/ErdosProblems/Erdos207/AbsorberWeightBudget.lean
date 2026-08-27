/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.AbsorberIndexedWeightedBound
import Mathlib.Data.Nat.Choose.Bounds

/-!
# Simplifying the absorber extension-weight budgets

The exact iterated sums from the A2 split admit transparent coarse bounds:
there are quadratically many triples through a fixed support vertex, only
polynomially many fixed-size bank parts, and boundedly many configuration
orders.  This file records those reductions without suppressing any of the
exact classes used upstream.
-/

namespace Erdos207

open Finset
open scoped BigOperators NNReal

/-- Two-element subsets, used to encode a triple after deleting one fixed
vertex. -/
abbrev PairOn (V : Type*) := {s : Finset V // s.card = 2}

def eraseThroughVertex
    {V : Type*} [Fintype V] [DecidableEq V] (v : V)
    (T : universeTriplesThrough v) : PairOn V :=
  ⟨T.1.1.erase v, by
    rw [card_erase_of_mem (mem_universeTriplesThrough_iff.mp T.2), T.1.2]⟩

lemma eraseThroughVertex_injective
    {V : Type*} [Fintype V] [DecidableEq V] (v : V) :
    Function.Injective (eraseThroughVertex v) := by
  intro T U hTU
  apply Subtype.ext
  apply Subtype.ext
  have hErase : T.1.1.erase v = U.1.1.erase v :=
    congrArg Subtype.val hTU
  have hvT : v ∈ T.1.1 := mem_universeTriplesThrough_iff.mp T.2
  have hvU : v ∈ U.1.1 := mem_universeTriplesThrough_iff.mp U.2
  calc
    T.1.1 = insert v (T.1.1.erase v) := (insert_erase hvT).symm
    _ = insert v (U.1.1.erase v) := by rw [hErase]
    _ = U.1.1 := insert_erase hvU

/-- At most `|V|²` ambient triples pass through one prescribed vertex. -/
theorem card_universeTriplesThrough_le_sq
    (V : Type*) [Fintype V] [DecidableEq V] (v : V) :
    (universeTriplesThrough v).card ≤ Fintype.card V ^ 2 := by
  calc
    (universeTriplesThrough v).card =
        Fintype.card (universeTriplesThrough v) :=
      (Fintype.card_coe _).symm
    _ ≤ Fintype.card (PairOn V) :=
      Fintype.card_le_of_injective (eraseThroughVertex v)
        (eraseThroughVertex_injective v)
    _ = Nat.choose (Fintype.card V) 2 := by
      simpa only [PairOn] using (Fintype.card_finset_len (α := V) 2)
    _ ≤ Fintype.card V ^ 2 := Nat.choose_le_pow _ _

/-- Fixed-size subsets of a bank have a uniform polynomial bound. -/
theorem card_powersetCard_le_add_one_pow
    {α : Type*} [DecidableEq α] (B : Finset α) {k q : ℕ} (hkq : k ≤ q) :
    (B.powersetCard k).card ≤ (B.card + 1) ^ q := by
  rw [card_powersetCard]
  calc
    Nat.choose B.card k ≤ B.card ^ k := Nat.choose_le_pow _ _
    _ ≤ (B.card + 1) ^ k := pow_le_pow_left₀ zero_le (by omega) _
    _ ≤ (B.card + 1) ^ q := pow_le_pow_right₀ (by omega) hkq

/-- The exact-class constant is monotone in the cutoff. -/
theorem exactBankWeightConstant_mono {r q : ℕ} (hrq : r ≤ q) :
    2 ^ (r ^ 3) * (r + 1) ≤ 2 ^ (q ^ 3) * (q + 1) := by
  apply Nat.mul_le_mul
  · exact pow_le_pow_right₀ (by omega)
      (pow_le_pow_left₀ zero_le hrq 3)
  · omega

/-- The factor `n²/(n+1)` is at most `n+1`. -/
lemma card_sq_mul_inv_add_one_le
    (n : ℕ) :
    (n : ℝ≥0) ^ 2 * ((n + 1 : ℕ) : ℝ≥0)⁻¹ ≤ (n + 1 : ℕ) := by
  have hpos : (0 : ℝ≥0) < (n + 1 : ℕ) := by positivity
  apply (mul_inv_le_iff₀ hpos).2
  rw [Nat.cast_add, Nat.cast_one]
  simpa only [pow_two] using
    (pow_le_pow_left₀ zero_le
      (by exact_mod_cast (show n ≤ n + 1 by omega) : (n : ℝ≥0) ≤ n + 1) 2)

/-- The exact local-branch sum is bounded using only the localization size
`M` and the cutoff `q`. -/
theorem localAbsorberWeightBudget_le
    {V : Type*} [Fintype V] [DecidableEq V]
    {q M : ℕ} {L : TripleSystemOn V} (hLM : L.card ≤ M) :
    (∑ r ∈ Icc 5 q, ∑ _K ∈ L.powerset,
      (2 ^ (r ^ 3) * (r + 1) : ℕ) *
        (Fintype.card V + 1 : ℝ≥0) ^ 2) ≤
      ((q + 1) * 2 ^ M * (2 ^ (q ^ 3) * (q + 1)) : ℕ) *
        (Fintype.card V + 1 : ℝ≥0) ^ 2 := by
  let C : ℝ≥0 := (2 ^ (q ^ 3) * (q + 1) : ℕ)
  let N2 : ℝ≥0 := (Fintype.card V + 1 : ℝ≥0) ^ 2
  have hpoint : ∀ r ∈ Icc 5 q,
      ((2 ^ (r ^ 3) * (r + 1) : ℕ) : ℝ≥0) * N2 ≤ C * N2 := by
    intro r hr
    have hrq := (mem_Icc.mp hr).2
    have hc :
        ((2 ^ (r ^ 3) * (r + 1) : ℕ) : ℝ≥0) ≤ C := by
      dsimp only [C]
      exact_mod_cast exactBankWeightConstant_mono hrq
    simpa only [mul_comm] using mul_le_mul_right hc N2
  have hIcc : (Icc 5 q).card ≤ q + 1 := by
    rw [Nat.card_Icc]
    omega
  have hpowerset : L.powerset.card ≤ 2 ^ M := by
    rw [card_powerset]
    exact pow_le_pow_right₀ (by omega) hLM
  calc
    (∑ r ∈ Icc 5 q, ∑ _K ∈ L.powerset,
        (2 ^ (r ^ 3) * (r + 1) : ℕ) *
          (Fintype.card V + 1 : ℝ≥0) ^ 2) ≤
      ∑ _r ∈ Icc 5 q, ∑ _K ∈ L.powerset, C * N2 := by
        apply sum_le_sum
        intro r hr
        apply sum_le_sum
        intro K _hK
        exact hpoint r hr
    _ = ((Icc 5 q).card * L.powerset.card : ℕ) * (C * N2) := by
      simp only [sum_const, nsmul_eq_mul, Nat.cast_mul]
      ring
    _ ≤ (((q + 1) * 2 ^ M : ℕ) : ℝ≥0) * (C * N2) := by
      gcongr
    _ = ((q + 1) * 2 ^ M * (2 ^ (q ^ 3) * (q + 1)) : ℕ) *
        (Fintype.card V + 1 : ℝ≥0) ^ 2 := by
      simp only [C, N2, Nat.cast_mul]
      ring

/-- Closed constant bound for the local branch when an outside triangle has
already been prescribed. -/
theorem localAbsorberWeightBudget_nonempty_le
    {V : Type*} [Fintype V] [DecidableEq V]
    {q M : ℕ} {L : TripleSystemOn V} (hLM : L.card ≤ M) :
    (∑ r ∈ Icc 5 q, ∑ _K ∈ L.powerset,
      ((2 ^ (r ^ 3) * (r + 1) : ℕ) : ℝ≥0)) ≤
      (((q + 1) * 2 ^ M * (2 ^ (q ^ 3) * (q + 1)) : ℕ) : ℝ≥0) := by
  let C : ℝ≥0 := (2 ^ (q ^ 3) * (q + 1) : ℕ)
  have hpoint : ∀ r ∈ Icc 5 q,
      ((2 ^ (r ^ 3) * (r + 1) : ℕ) : ℝ≥0) ≤ C := by
    intro r hr
    dsimp only [C]
    exact_mod_cast exactBankWeightConstant_mono (mem_Icc.mp hr).2
  have hIcc : (Icc 5 q).card ≤ q + 1 := by
    rw [Nat.card_Icc]
    omega
  have hpowerset : L.powerset.card ≤ 2 ^ M := by
    rw [card_powerset]
    exact pow_le_pow_right₀ (by omega) hLM
  calc
    (∑ r ∈ Icc 5 q, ∑ _K ∈ L.powerset,
        ((2 ^ (r ^ 3) * (r + 1) : ℕ) : ℝ≥0)) ≤
      ∑ _r ∈ Icc 5 q, ∑ _K ∈ L.powerset, C := by
        apply sum_le_sum
        intro r hr
        apply sum_le_sum
        intro K _hK
        exact hpoint r hr
    _ = ((Icc 5 q).card * L.powerset.card : ℕ) * C := by
      simp only [sum_const, nsmul_eq_mul, Nat.cast_mul]
      ring
    _ ≤ (((q + 1) * 2 ^ M : ℕ) : ℝ≥0) * C := by
      gcongr
    _ = ((q + 1) * 2 ^ M * (2 ^ (q ^ 3) * (q + 1)) : ℕ) := by
      simp only [C, Nat.cast_mul]

/-- The support-branch sum loses one ambient vertex choice.  After summing
the distinguished triangle through that vertex, it grows only linearly in
the ambient order (apart from the fixed bank-polynomial factor). -/
theorem supportAbsorberWeightBudget_le
    {V : Type*} [Fintype V] [DecidableEq V]
    {q j : ℕ} (H : SimpleGraph V) (X : Finset V)
    (B : TripleSystemOn V) :
    (∑ v ∈ graphSupportFinset H \ X,
      ∑ _T ∈ universeTriplesThrough v,
        ∑ r ∈ Icc 5 q, ∑ _K ∈ B.powersetCard (r - j),
          (2 ^ (r ^ 3) * (r + 1) : ℕ) *
            (Fintype.card V + 1 : ℝ≥0)⁻¹) ≤
      ((graphSupportFinset H \ X).card * (q + 1) *
        (B.card + 1) ^ q * (2 ^ (q ^ 3) * (q + 1)) : ℕ) *
          (Fintype.card V + 1 : ℝ≥0) := by
  let C : ℝ≥0 := (2 ^ (q ^ 3) * (q + 1) : ℕ)
  let Kmax : ℝ≥0 := ((B.card + 1) ^ q : ℕ)
  let D : ℝ≥0 := C * (Fintype.card V + 1 : ℝ≥0)⁻¹
  have hIcc : (Icc 5 q).card ≤ q + 1 := by
    rw [Nat.card_Icc]
    omega
  have hpoint : ∀ r ∈ Icc 5 q,
      ((2 ^ (r ^ 3) * (r + 1) : ℕ) : ℝ≥0) *
          (Fintype.card V + 1 : ℝ≥0)⁻¹ ≤ D := by
    intro r hr
    have hc :
        ((2 ^ (r ^ 3) * (r + 1) : ℕ) : ℝ≥0) ≤ C := by
      dsimp only [C]
      exact_mod_cast exactBankWeightConstant_mono (mem_Icc.mp hr).2
    dsimp only [D]
    simpa only [mul_comm] using mul_le_mul_right hc
      ((Fintype.card V + 1 : ℝ≥0)⁻¹)
  have hRK :
      (∑ r ∈ Icc 5 q, ∑ _K ∈ B.powersetCard (r - j), D) ≤
        (q + 1 : ℕ) * (Kmax * D) := by
    calc
      (∑ r ∈ Icc 5 q, ∑ _K ∈ B.powersetCard (r - j), D) =
          ∑ r ∈ Icc 5 q,
            ((B.powersetCard (r - j)).card : ℝ≥0) * D := by
        apply sum_congr rfl
        intro r _hr
        simp
      _ ≤ ∑ _r ∈ Icc 5 q, Kmax * D := by
        apply sum_le_sum
        intro r hr
        have hk : (B.powersetCard (r - j)).card ≤
            (B.card + 1) ^ q :=
          card_powersetCard_le_add_one_pow B (by
            have := (mem_Icc.mp hr).2
            omega)
        have hk' : ((B.powersetCard (r - j)).card : ℝ≥0) ≤ Kmax := by
          dsimp only [Kmax]
          exact_mod_cast hk
        simpa only [mul_comm] using mul_le_mul_right hk' D
      _ = ((Icc 5 q).card : ℝ≥0) * (Kmax * D) := by simp
      _ ≤ (q + 1 : ℕ) * (Kmax * D) := by
        have hi : ((Icc 5 q).card : ℝ≥0) ≤ (q + 1 : ℕ) := by
          exact_mod_cast hIcc
        simpa only [mul_comm] using mul_le_mul_right hi (Kmax * D)
  have hTv : ∀ v : V,
      (∑ _T ∈ universeTriplesThrough v,
        ∑ r ∈ Icc 5 q, ∑ _K ∈ B.powersetCard (r - j),
          (2 ^ (r ^ 3) * (r + 1) : ℕ) *
            (Fintype.card V + 1 : ℝ≥0)⁻¹) ≤
        (Fintype.card V : ℝ≥0) ^ 2 *
          ((q + 1 : ℕ) * (Kmax * D)) := by
    intro v
    calc
      (∑ _T ∈ universeTriplesThrough v,
          ∑ r ∈ Icc 5 q, ∑ _K ∈ B.powersetCard (r - j),
            (2 ^ (r ^ 3) * (r + 1) : ℕ) *
              (Fintype.card V + 1 : ℝ≥0)⁻¹) ≤
          ∑ _T ∈ universeTriplesThrough v,
            ∑ r ∈ Icc 5 q, ∑ _K ∈ B.powersetCard (r - j), D := by
        apply sum_le_sum
        intro T _hT
        apply sum_le_sum
        intro r hr
        apply sum_le_sum
        intro K _hK
        exact hpoint r hr
      _ ≤ ∑ _T ∈ universeTriplesThrough v,
          ((q + 1 : ℕ) * (Kmax * D)) := by
        apply sum_le_sum
        intro T _hT
        exact hRK
      _ = ((universeTriplesThrough v).card : ℝ≥0) *
          ((q + 1 : ℕ) * (Kmax * D)) := by simp
      _ ≤ (Fintype.card V : ℝ≥0) ^ 2 *
          ((q + 1 : ℕ) * (Kmax * D)) := by
        have ht : ((universeTriplesThrough v).card : ℝ≥0) ≤
            (Fintype.card V : ℝ≥0) ^ 2 := by
          exact_mod_cast card_universeTriplesThrough_le_sq V v
        simpa only [mul_comm] using mul_le_mul_right ht
          ((q + 1 : ℕ) * (Kmax * D))
  calc
    (∑ v ∈ graphSupportFinset H \ X,
        ∑ _T ∈ universeTriplesThrough v,
          ∑ r ∈ Icc 5 q, ∑ _K ∈ B.powersetCard (r - j),
            (2 ^ (r ^ 3) * (r + 1) : ℕ) *
              (Fintype.card V + 1 : ℝ≥0)⁻¹) ≤
      ∑ _v ∈ graphSupportFinset H \ X,
        (Fintype.card V : ℝ≥0) ^ 2 *
          ((q + 1 : ℕ) * (Kmax * D)) := by
      apply sum_le_sum
      intro v _hv
      exact hTv v
    _ = (((graphSupportFinset H \ X).card : ℝ≥0) *
        ((q + 1 : ℕ) * Kmax * C)) *
          ((Fintype.card V : ℝ≥0) ^ 2 *
            (Fintype.card V + 1 : ℝ≥0)⁻¹) := by
      simp only [sum_const, nsmul_eq_mul, D]
      ring
    _ ≤ (((graphSupportFinset H \ X).card : ℝ≥0) *
        ((q + 1 : ℕ) * Kmax * C)) *
          (Fintype.card V + 1 : ℝ≥0) := by
      simpa only [Nat.cast_add, Nat.cast_one, mul_comm] using mul_le_mul_right
        (card_sq_mul_inv_add_one_le (Fintype.card V))
        (((graphSupportFinset H \ X).card : ℝ≥0) *
          ((q + 1 : ℕ) * Kmax * C))
    _ = ((graphSupportFinset H \ X).card * (q + 1) *
        (B.card + 1) ^ q * (2 ^ (q ^ 3) * (q + 1)) : ℕ) *
          (Fintype.card V + 1 : ℝ≥0) := by
      simp only [Kmax, C, Nat.cast_mul, Nat.cast_pow, Nat.cast_add,
        Nat.cast_one]
      ring

/-- The common exact-class sum over configuration orders and fixed-size bank
parts is bounded independently of the ambient vertex order. -/
theorem bankClassWeightBudget_le
    {V : Type*} [Fintype V] [DecidableEq V]
    {q j : ℕ} (B : TripleSystemOn V) :
    (∑ r ∈ Icc 5 q, ∑ _K ∈ B.powersetCard (r - j),
      ((2 ^ (r ^ 3) * (r + 1) : ℕ) : ℝ≥0)) ≤
      (((q + 1) * (B.card + 1) ^ q *
        (2 ^ (q ^ 3) * (q + 1)) : ℕ) : ℝ≥0) := by
  let C : ℝ≥0 := (2 ^ (q ^ 3) * (q + 1) : ℕ)
  let Kmax : ℝ≥0 := ((B.card + 1) ^ q : ℕ)
  have hIcc : (Icc 5 q).card ≤ q + 1 := by
    rw [Nat.card_Icc]
    omega
  have hpoint : ∀ r ∈ Icc 5 q,
      ((2 ^ (r ^ 3) * (r + 1) : ℕ) : ℝ≥0) ≤ C := by
    intro r hr
    dsimp only [C]
    exact_mod_cast exactBankWeightConstant_mono (mem_Icc.mp hr).2
  calc
    (∑ r ∈ Icc 5 q, ∑ _K ∈ B.powersetCard (r - j),
        ((2 ^ (r ^ 3) * (r + 1) : ℕ) : ℝ≥0)) ≤
      ∑ _r ∈ Icc 5 q, ∑ _K ∈ B.powersetCard (_r - j), C := by
        apply sum_le_sum
        intro r hr
        apply sum_le_sum
        intro K _hK
        exact hpoint r hr
    _ ≤ ∑ _r ∈ Icc 5 q, Kmax * C := by
      apply sum_le_sum
      intro r hr
      calc
        (∑ _K ∈ B.powersetCard (r - j), C) =
            ((B.powersetCard (r - j)).card : ℝ≥0) * C := by simp
        _ ≤ Kmax * C := by
          have hk := card_powersetCard_le_add_one_pow B (by
            have := (mem_Icc.mp hr).2
            omega : r - j ≤ q)
          have hk' : ((B.powersetCard (r - j)).card : ℝ≥0) ≤ Kmax := by
            dsimp only [Kmax]
            exact_mod_cast hk
          exact mul_le_mul_left hk' C
    _ = ((Icc 5 q).card : ℝ≥0) * (Kmax * C) := by simp
    _ ≤ (q + 1 : ℕ) * (Kmax * C) := by
      have hi : ((Icc 5 q).card : ℝ≥0) ≤ (q + 1 : ℕ) := by
        exact_mod_cast hIcc
      exact mul_le_mul_left hi (Kmax * C)
    _ = (((q + 1) * (B.card + 1) ^ q *
        (2 ^ (q ^ 3) * (q + 1)) : ℕ) : ℝ≥0) := by
      simp only [Kmax, C, Nat.cast_mul, Nat.cast_pow, Nat.cast_add,
        Nat.cast_one]
      ring

lemma card_sq_mul_inv_sq_add_one_le_one (n : ℕ) :
    (n : ℝ≥0) ^ 2 * (((n + 1 : ℕ) : ℝ≥0)⁻¹) ^ 2 ≤ 1 := by
  calc
    (n : ℝ≥0) ^ 2 * (((n + 1 : ℕ) : ℝ≥0)⁻¹) ^ 2 ≤
        ((n + 1 : ℕ) : ℝ≥0) ^ 2 *
          (((n + 1 : ℕ) : ℝ≥0)⁻¹) ^ 2 := by
      gcongr
      exact_mod_cast (show n ≤ n + 1 by omega)
    _ ≤ 1 := pow_mul_inv_pow_le_one (n + 1) 2 2 (by omega) (by omega)

/-- Closed bound for the refined support split.  Both the two-inverse
interior term and the regrouped endpoint term are independent of the ambient
order. -/
theorem supportAbsorberWeightBudget_refined_le
    {V : Type*} [Fintype V] [DecidableEq V]
    {q j : ℕ} (H : SimpleGraph V) (X : Finset V)
    (B : TripleSystemOn V) :
    ((∑ v ∈ graphSupportFinset H \ X,
      ∑ _T ∈ universeTriplesThrough v,
        ∑ r ∈ Icc 5 q, ∑ _K ∈ B.powersetCard (r - j),
          (2 ^ (r ^ 3) * (r + 1) : ℕ) *
            ((Fintype.card V + 1 : ℝ≥0)⁻¹) ^ 2) +
      (∑ r ∈ Icc 5 q, ∑ _K ∈ B.powersetCard (r - j),
        (2 ^ (r ^ 3) * (r + 1) : ℕ) *
          (Fintype.card V + 1 : ℝ≥0)⁻¹)) ≤
      (((graphSupportFinset H \ X).card + 1) * (q + 1) *
        (B.card + 1) ^ q * (2 ^ (q ^ 3) * (q + 1)) : ℕ) := by
  let D : ℝ≥0 := (((q + 1) * (B.card + 1) ^ q *
    (2 ^ (q ^ 3) * (q + 1)) : ℕ) : ℝ≥0)
  let p : ℝ≥0 := (Fintype.card V + 1 : ℝ≥0)⁻¹
  have hRK :
      (∑ r ∈ Icc 5 q, ∑ _K ∈ B.powersetCard (r - j),
        ((2 ^ (r ^ 3) * (r + 1) : ℕ) : ℝ≥0)) ≤ D := by
    exact bankClassWeightBudget_le B
  have hp : p ≤ 1 := by
    dsimp only [p]
    exact inv_le_one₀ (by positivity) |>.2 (by
      exact_mod_cast (show 1 ≤ Fintype.card V + 1 by omega))
  have hRKp :
      (∑ r ∈ Icc 5 q, ∑ _K ∈ B.powersetCard (r - j),
        ((2 ^ (r ^ 3) * (r + 1) : ℕ) : ℝ≥0) * p) ≤ D := by
    calc
      (∑ r ∈ Icc 5 q, ∑ _K ∈ B.powersetCard (r - j),
          ((2 ^ (r ^ 3) * (r + 1) : ℕ) : ℝ≥0) * p) =
        (∑ r ∈ Icc 5 q, ∑ _K ∈ B.powersetCard (r - j),
          ((2 ^ (r ^ 3) * (r + 1) : ℕ) : ℝ≥0)) * p := by
          simp only [sum_mul]
      _ ≤ D * p := mul_le_mul_left hRK p
      _ ≤ D * 1 := mul_le_mul_right hp D
      _ = D := by simp
  have hRKp2 :
      (∑ r ∈ Icc 5 q, ∑ _K ∈ B.powersetCard (r - j),
        ((2 ^ (r ^ 3) * (r + 1) : ℕ) : ℝ≥0) * p ^ 2) ≤
        D * p ^ 2 := by
    calc
      (∑ r ∈ Icc 5 q, ∑ _K ∈ B.powersetCard (r - j),
          ((2 ^ (r ^ 3) * (r + 1) : ℕ) : ℝ≥0) * p ^ 2) =
        (∑ r ∈ Icc 5 q, ∑ _K ∈ B.powersetCard (r - j),
          ((2 ^ (r ^ 3) * (r + 1) : ℕ) : ℝ≥0)) * p ^ 2 := by
            simp only [sum_mul]
      _ ≤ D * p ^ 2 := mul_le_mul_left hRK (p ^ 2)
  have hvertex : ∀ v : V,
      (∑ _T ∈ universeTriplesThrough v,
        ∑ r ∈ Icc 5 q, ∑ _K ∈ B.powersetCard (r - j),
          ((2 ^ (r ^ 3) * (r + 1) : ℕ) : ℝ≥0) * p ^ 2) ≤ D := by
    intro v
    calc
      (∑ _T ∈ universeTriplesThrough v,
          ∑ r ∈ Icc 5 q, ∑ _K ∈ B.powersetCard (r - j),
            ((2 ^ (r ^ 3) * (r + 1) : ℕ) : ℝ≥0) * p ^ 2) ≤
        ∑ _T ∈ universeTriplesThrough v, D * p ^ 2 := by
          apply sum_le_sum
          intro T _hT
          exact hRKp2
      _ = ((universeTriplesThrough v).card : ℝ≥0) * (D * p ^ 2) := by
        simp
      _ ≤ (Fintype.card V : ℝ≥0) ^ 2 * (D * p ^ 2) := by
        have ht : ((universeTriplesThrough v).card : ℝ≥0) ≤
            (Fintype.card V : ℝ≥0) ^ 2 := by
          exact_mod_cast card_universeTriplesThrough_le_sq V v
        exact mul_le_mul_left ht (D * p ^ 2)
      _ = D * ((Fintype.card V : ℝ≥0) ^ 2 * p ^ 2) := by ring
      _ ≤ D * 1 := by
        apply mul_le_mul_right _ D
        dsimp only [p]
        simpa only [Nat.cast_add, Nat.cast_one] using
          card_sq_mul_inv_sq_add_one_le_one (Fintype.card V)
      _ = D := by simp
  calc
    ((∑ v ∈ graphSupportFinset H \ X,
        ∑ _T ∈ universeTriplesThrough v,
          ∑ r ∈ Icc 5 q, ∑ _K ∈ B.powersetCard (r - j),
            (2 ^ (r ^ 3) * (r + 1) : ℕ) *
              ((Fintype.card V + 1 : ℝ≥0)⁻¹) ^ 2) +
        (∑ r ∈ Icc 5 q, ∑ _K ∈ B.powersetCard (r - j),
          (2 ^ (r ^ 3) * (r + 1) : ℕ) *
            (Fintype.card V + 1 : ℝ≥0)⁻¹)) ≤
      (∑ _v ∈ graphSupportFinset H \ X, D) + D := by
        apply add_le_add
        · apply sum_le_sum
          intro v _hv
          simpa only [p] using hvertex v
        · simpa only [p] using hRKp
    _ = (((graphSupportFinset H \ X).card + 1 : ℕ) : ℝ≥0) * D := by
      simp only [sum_const, nsmul_eq_mul, Nat.cast_add, Nat.cast_one]
      ring
    _ = (((graphSupportFinset H \ X).card + 1) * (q + 1) *
        (B.card + 1) ^ q * (2 ^ (q ^ 3) * (q + 1)) : ℕ) := by
      simp only [D, Nat.cast_mul, Nat.cast_add, Nat.cast_one, Nat.cast_pow]
      ring
/-- Coarse closed-form consequence of the exact weighted A2 split. -/
theorem exists_local_bank_extensionWeight_absorberInduced_le_budget
    {V : Type*} [Fintype V] [DecidableEq V]
    {q M j : ℕ} {H : SimpleGraph V} {X : Finset V}
    {B R : TripleSystemOn V}
    (hA2 : HasAbsorberLocalization q M H X B)
    (hRq : R.card ≤ q) (hj : 2 ≤ j) :
    ∃ L : TripleSystemOn V, L ⊆ B ∧ L.card ≤ M ∧
      extensionWeight
          (fun S : absorberInducedConfigurationsOn q j B ↦ S.1)
          (constantTripleWeight ((Fintype.card V + 1 : ℝ≥0)⁻¹)) R ≤
        ((q + 1) * 2 ^ M * (2 ^ (q ^ 3) * (q + 1)) : ℕ) *
            (Fintype.card V + 1 : ℝ≥0) ^ 2 +
          ((graphSupportFinset H \ X).card * (q + 1) *
            (B.card + 1) ^ q * (2 ^ (q ^ 3) * (q + 1)) : ℕ) *
              (Fintype.card V + 1 : ℝ≥0) := by
  obtain ⟨L, hLB, hLM, hweight⟩ :=
    exists_local_bank_extensionWeight_absorberInduced_le
      hA2 hRq hj
  refine ⟨L, hLB, hLM, hweight.trans ?_⟩
  apply add_le_add
  · exact localAbsorberWeightBudget_le hLM
  · exact supportAbsorberWeightBudget_le H X B

/-- Closed-form rooted consequence of the weighted A2 split.  The local
term is independent of the ambient order; only the exposed-support term is
linear. -/
theorem exists_local_bank_extensionWeight_absorberInduced_le_budget_of_nonempty
    {V : Type*} [Fintype V] [DecidableEq V]
    {q M j : ℕ} {H : SimpleGraph V} {X : Finset V}
    {B R : TripleSystemOn V}
    (hA2 : HasAbsorberLocalization q M H X B)
    (hRq : R.card ≤ q) (hj : 2 ≤ j) (hR : 1 ≤ R.card) :
    ∃ L : TripleSystemOn V, L ⊆ B ∧ L.card ≤ M ∧
      extensionWeight
          (fun S : absorberInducedConfigurationsOn q j B ↦ S.1)
          (constantTripleWeight ((Fintype.card V + 1 : ℝ≥0)⁻¹)) R ≤
        ((q + 1) * 2 ^ M * (2 ^ (q ^ 3) * (q + 1)) : ℕ) +
          ((graphSupportFinset H \ X).card * (q + 1) *
            (B.card + 1) ^ q * (2 ^ (q ^ 3) * (q + 1)) : ℕ) *
              (Fintype.card V + 1 : ℝ≥0) := by
  obtain ⟨L, hLB, hLM, hweight⟩ :=
    exists_local_bank_extensionWeight_absorberInduced_le_of_nonempty
      hA2 hRq hj hR
  refine ⟨L, hLB, hLM, hweight.trans ?_⟩
  apply add_le_add
  · simpa only [Nat.cast_sum] using
      localAbsorberWeightBudget_nonempty_le hLM
  · exact supportAbsorberWeightBudget_le H X B

/-- Fully refined rooted budget: neither A2 branch carries a positive power
of the ambient order. -/
theorem exists_local_bank_extensionWeight_absorberInduced_le_refined_budget
    {V : Type*} [Fintype V] [DecidableEq V]
    {q M j : ℕ} {H : SimpleGraph V} {X : Finset V}
    {B R : TripleSystemOn V}
    (hA2 : HasAbsorberLocalization q M H X B)
    (hRq : R.card ≤ q) (hj : 2 ≤ j) (hR : 1 ≤ R.card) :
    ∃ L : TripleSystemOn V, L ⊆ B ∧ L.card ≤ M ∧
      extensionWeight
          (fun S : absorberInducedConfigurationsOn q j B ↦ S.1)
          (constantTripleWeight ((Fintype.card V + 1 : ℝ≥0)⁻¹)) R ≤
        ((q + 1) * 2 ^ M * (2 ^ (q ^ 3) * (q + 1)) : ℕ) +
          (((graphSupportFinset H \ X).card + 1) * (q + 1) *
            (B.card + 1) ^ q * (2 ^ (q ^ 3) * (q + 1)) : ℕ) := by
  obtain ⟨L, hLB, hLM, hweight⟩ :=
    exists_local_bank_extensionWeight_absorberInduced_le_refined
      hA2 hRq hj hR
  refine ⟨L, hLB, hLM, hweight.trans ?_⟩
  apply add_le_add
  · simpa only [Nat.cast_sum] using
      localAbsorberWeightBudget_nonempty_le hLM
  · exact supportAbsorberWeightBudget_refined_le H X B

end Erdos207
