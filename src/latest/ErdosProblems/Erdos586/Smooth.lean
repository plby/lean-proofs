/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
import Mathlib

/-!
# Smooth antichain estimates for Erdős Problem 586

This file proves the three finite estimates from Lemmas 9.2--9.4 of
Balister--Bollobás--Morris--Sahasrabudhe--Tiba.  Smooth integers are encoded
by their vectors of prime exponents.  The coordinate order is divisibility.
-/

open scoped BigOperators

namespace Erdos586

noncomputable section

attribute [local instance] Classical.propDecidable

abbrev Exp2 := ℕ × ℕ
abbrev Exp3 := ℕ × ℕ × ℕ

/-- Coordinatewise order on exponent pairs. -/
def PairLe (x y : Exp2) : Prop := x.1 ≤ y.1 ∧ x.2 ≤ y.2

/-- Coordinatewise order on exponent triples. -/
def TripleLe (x y : Exp3) : Prop :=
  x.1 ≤ y.1 ∧ x.2.1 ≤ y.2.1 ∧ x.2.2 ≤ y.2.2

def PairAntichain (A : Finset Exp2) : Prop := IsAntichain PairLe (A : Set Exp2)
def TripleAntichain (A : Finset Exp3) : Prop := IsAntichain TripleLe (A : Set Exp3)

/-- Decode a pair of exponents as a 3-smooth natural number. -/
def decode3 (x : Exp2) : ℕ := 2 ^ x.1 * 3 ^ x.2

/-- Decode a triple of exponents as a 5-smooth natural number. -/
def decode5 (x : Exp3) : ℕ := 2 ^ x.1 * 3 ^ x.2.1 * 5 ^ x.2.2

/-- The reciprocal weight of a 3-smooth exponent pair. -/
def pairWeight (x : Exp2) : ℝ := (1 / 2 : ℝ) ^ x.1 * (1 / 3 : ℝ) ^ x.2

/-- The reciprocal weight of a 5-smooth exponent triple. -/
def tripleWeight (x : Exp3) : ℝ :=
  (1 / 2 : ℝ) ^ x.1 * (1 / 3 : ℝ) ^ x.2.1 * (1 / 5 : ℝ) ^ x.2.2

/-- The LCM-energy kernel in two exponent coordinates. -/
def pairKernel (x y : Exp2) : ℝ :=
  (1 / 2 : ℝ) ^ max x.1 y.1 * (1 / 3 : ℝ) ^ max x.2 y.2

/-- The LCM-energy kernel in three exponent coordinates. -/
def tripleKernel (x y : Exp3) : ℝ :=
  (1 / 2 : ℝ) ^ max x.1 y.1 *
    (1 / 3 : ℝ) ^ max x.2.1 y.2.1 *
    (1 / 5 : ℝ) ^ max x.2.2 y.2.2

def pairEnergy (A B : Finset Exp2) : ℝ := ∑ x ∈ A, ∑ y ∈ B, pairKernel x y
def tripleEnergy (A B : Finset Exp3) : ℝ := ∑ x ∈ A, ∑ y ∈ B, tripleKernel x y

lemma geometric_finset_le (s : Finset ℕ) {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) :
    ∑ n ∈ s, r ^ n ≤ (1 - r)⁻¹ := by
  have hs : Summable (fun n : ℕ ↦ r ^ n) :=
    summable_geometric_of_norm_lt_one (by simpa [abs_of_nonneg hr0] using hr1)
  calc
    ∑ n ∈ s, r ^ n ≤ ∑' n : ℕ, r ^ n :=
      hs.sum_le_tsum s (fun n _ ↦ pow_nonneg hr0 n)
    _ = (1 - r)⁻¹ := tsum_geometric_of_norm_lt_one
      (by simpa [abs_of_nonneg hr0] using hr1)

lemma pair_fst_injOn {A : Finset Exp2} (hA : PairAntichain A) :
    Set.InjOn Prod.fst (A : Set Exp2) := by
  intro x hx y hy hxy
  rcases le_total x.2 y.2 with h | h
  · exact hA.eq hx hy ⟨hxy.le, h⟩
  · exact hA.eq' hx hy ⟨hxy.ge, h⟩

lemma pair_snd_injOn {A : Finset Exp2} (hA : PairAntichain A) :
    Set.InjOn Prod.snd (A : Set Exp2) := by
  intro x hx y hy hxy
  rcases le_total x.1 y.1 with h | h
  · exact hA.eq hx hy ⟨h, hxy.le⟩
  · exact hA.eq' hx hy ⟨h, hxy.ge⟩

lemma sum_pair_fst_pow_le {A : Finset Exp2} (hA : PairAntichain A)
    {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) :
    ∑ x ∈ A, r ^ x.1 ≤ (1 - r)⁻¹ := by
  rw [← Finset.sum_image (pair_fst_injOn hA)]
  exact geometric_finset_le _ hr0 hr1

lemma sum_pair_snd_pow_le {A : Finset Exp2} (hA : PairAntichain A)
    {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) :
    ∑ x ∈ A, r ^ x.2 ≤ (1 - r)⁻¹ := by
  rw [← Finset.sum_image (pair_snd_injOn hA)]
  exact geometric_finset_le _ hr0 hr1

lemma fin_strictMono_nat_id_le {k : ℕ} {f : Fin k → ℕ} (hf : StrictMono f) (i : Fin k) :
    (i : ℕ) ≤ f i := by
  induction hn : (i : ℕ) using Nat.strong_induction_on generalizing i with
  | h n ih =>
      by_cases hn0 : n = 0
      · omega
      · let j : Fin k := ⟨n - 1, by omega⟩
        have hjval : (j : ℕ) = n - 1 := rfl
        have hji : j < i := by
          apply Fin.mk_lt_mk.mpr
          show n - 1 < (i : ℕ)
          rw [hn]
          omega
        have hj := ih (n - 1) (by omega) j hjval
        have hfij := hf hji
        omega

lemma fin_strictAnti_nat_rev_le {k : ℕ} {f : Fin k → ℕ} (hf : StrictAnti f) (i : Fin k) :
    k - 1 - (i : ℕ) ≤ f i := by
  have hg : StrictMono (f ∘ Fin.rev) := hf.comp Fin.rev_strictAnti
  have h := fin_strictMono_nat_id_le hg i.rev
  simp only [Function.comp_apply, Fin.rev_rev] at h
  rw [Fin.val_rev] at h
  omega


def pairLexFinset (A : Finset Exp2) : Finset (ℕ ×ₗ ℕ) := A.map toLex.toEmbedding

@[simp] lemma card_pairLexFinset (A : Finset Exp2) : (pairLexFinset A).card = A.card := by
  simp [pairLexFinset]

def pairEnumLex (A : Finset Exp2) : Fin A.card → (ℕ ×ₗ ℕ) :=
  (pairLexFinset A).orderEmbOfFin (card_pairLexFinset A)

/-- Increasing lexicographic enumeration of a finite exponent-pair antichain. -/
def pairEnum (A : Finset Exp2) (i : Fin A.card) : Exp2 := ofLex (pairEnumLex A i)

@[simp] lemma pairEnum_mem (A : Finset Exp2) (i : Fin A.card) : pairEnum A i ∈ A := by
  have h := (pairLexFinset A).orderEmbOfFin_mem (card_pairLexFinset A) i
  simpa [pairLexFinset, pairEnum, pairEnumLex] using h

lemma pairEnum_injective (A : Finset Exp2) : Function.Injective (pairEnum A) := by
  intro i j hij
  apply ((pairLexFinset A).orderEmbOfFin (card_pairLexFinset A)).injective
  apply ofLex.injective
  exact hij

lemma pairEnum_fst_strictMono {A : Finset Exp2} (hA : PairAntichain A) :
    StrictMono (fun i ↦ (pairEnum A i).1) := by
  intro i j hij
  have hlex : pairEnumLex A i < pairEnumLex A j :=
    ((pairLexFinset A).orderEmbOfFin (card_pairLexFinset A)).strictMono hij
  rcases Prod.Lex.lt_iff.mp hlex with h | h
  · exact h
  · exfalso
    have hpair := (pair_fst_injOn hA) (pairEnum_mem A i) (pairEnum_mem A j) h.1
    exact hij.ne (pairEnum_injective A hpair)

lemma pairEnum_snd_strictAnti {A : Finset Exp2} (hA : PairAntichain A) :
    StrictAnti (fun i ↦ (pairEnum A i).2) := by
  intro i j hij
  have hfst := pairEnum_fst_strictMono hA hij
  rcases lt_or_ge (pairEnum A j).2 (pairEnum A i).2 with h | h
  · exact h
  · exfalso
    exact hij.ne (pairEnum_injective A <|
      hA.eq (pairEnum_mem A i) (pairEnum_mem A j) ⟨hfst.le, h⟩)

lemma pairEnum_canonical_le {A : Finset Exp2} (hA : PairAntichain A) (i : Fin A.card) :
    (i : ℕ) ≤ (pairEnum A i).1 ∧ A.card - 1 - (i : ℕ) ≤ (pairEnum A i).2 :=
  ⟨fin_strictMono_nat_id_le (pairEnum_fst_strictMono hA) i,
    fin_strictAnti_nat_rev_le (pairEnum_snd_strictAnti hA) i⟩

lemma pairEnum_image (A : Finset Exp2) :
    Finset.image (pairEnum A) Finset.univ = A := by
  ext x
  constructor
  · simp only [Finset.mem_image, Finset.mem_univ, true_and]
    rintro ⟨i, rfl⟩
    exact pairEnum_mem A i
  · intro hx
    have hxlex : toLex x ∈ pairLexFinset A := by simpa [pairLexFinset] using hx
    let e := (pairLexFinset A).orderIsoOfFin (card_pairLexFinset A)
    let i : Fin A.card := e.symm ⟨toLex x, hxlex⟩
    refine Finset.mem_image.mpr ⟨i, Finset.mem_univ _, ?_⟩
    change ofLex (e i : ℕ ×ₗ ℕ) = x
    simp [i, e]

lemma sum_pairEnum (A : Finset Exp2) (f : Exp2 → ℝ) :
    ∑ x ∈ A, f x = ∑ i : Fin A.card, f (pairEnum A i) := by
  calc
    ∑ x ∈ A, f x = ∑ x ∈ Finset.image (pairEnum A) Finset.univ, f x := by
      rw [pairEnum_image]
    _ = ∑ i : Fin A.card, f (pairEnum A i) := by
      rw [Finset.sum_image (Set.injOn_of_injective (pairEnum_injective A))]

/-- The minimal `k`-point path in the two-coordinate divisibility order. -/
def canonicalPair (k : ℕ) (i : Fin k) : Exp2 := (i, k - 1 - i)

def canonicalPairEnergy (m k : ℕ) : ℝ :=
  ∑ i : Fin m, ∑ j : Fin k, pairKernel (canonicalPair m i) (canonicalPair k j)

def canonicalPairWeightSum (k : ℕ) : ℝ := ∑ i : Fin k, pairWeight (canonicalPair k i)

lemma canonicalPairWeightSum_eq (k : ℕ) :
    canonicalPairWeightSum k =
      6 * ((1 / 2 : ℝ) ^ k - (1 / 3 : ℝ) ^ k) := by
  unfold canonicalPairWeightSum pairWeight canonicalPair
  simp only
  rw [Fin.sum_univ_eq_sum_range
    (fun i ↦ (1 / 2 : ℝ) ^ i * (1 / 3 : ℝ) ^ (k - 1 - i))]
  have h := geom_sum₂_mul (1 / 2 : ℝ) (1 / 3 : ℝ) k
  norm_num at h ⊢
  linarith

lemma pairKernel_anti {x x' y y' : Exp2} (hx : PairLe x x') (hy : PairLe y y') :
    pairKernel x' y' ≤ pairKernel x y := by
  unfold pairKernel
  apply mul_le_mul
  · exact pow_le_pow_of_le_one (by norm_num) (by norm_num)
      (max_le_max hx.1 hy.1)
  · exact pow_le_pow_of_le_one (by norm_num) (by norm_num)
      (max_le_max hx.2 hy.2)
  · positivity
  · positivity

lemma canonicalPair_le_pairEnum {A : Finset Exp2} (hA : PairAntichain A)
    (i : Fin A.card) : PairLe (canonicalPair A.card i) (pairEnum A i) :=
  pairEnum_canonical_le hA i

lemma pairEnergy_le_canonical {A B : Finset Exp2}
    (hA : PairAntichain A) (hB : PairAntichain B) :
    pairEnergy A B ≤ canonicalPairEnergy A.card B.card := by
  rw [pairEnergy, sum_pairEnum A]
  simp_rw [sum_pairEnum B]
  unfold canonicalPairEnergy
  exact Finset.sum_le_sum fun i _ ↦ Finset.sum_le_sum fun j _ ↦
    pairKernel_anti (canonicalPair_le_pairEnum hA i) (canonicalPair_le_pairEnum hB j)

lemma pairKernel_comm (x y : Exp2) : pairKernel x y = pairKernel y x := by
  simp [pairKernel, max_comm]

lemma pairEnergy_comm (A B : Finset Exp2) : pairEnergy A B = pairEnergy B A := by
  unfold pairEnergy
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x hx
  apply Finset.sum_congr rfl
  intro y hy
  exact pairKernel_comm _ _

lemma pairKernel_le_right_weight (x y : Exp2) : pairKernel x y ≤ pairWeight y := by
  unfold pairKernel pairWeight
  apply mul_le_mul
  · exact pow_le_pow_of_le_one (by norm_num) (by norm_num) (le_max_right _ _)
  · exact pow_le_pow_of_le_one (by norm_num) (by norm_num) (le_max_right _ _)
  · positivity
  · positivity

lemma canonicalPairEnergy_comm (m k : ℕ) :
    canonicalPairEnergy m k = canonicalPairEnergy k m := by
  unfold canonicalPairEnergy
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  exact pairKernel_comm _ _

lemma canonicalPairEnergy_le_card_mul (m k : ℕ) :
    canonicalPairEnergy m k ≤ (m : ℝ) * canonicalPairWeightSum k := by
  unfold canonicalPairEnergy canonicalPairWeightSum
  calc
    ∑ i : Fin m, ∑ j : Fin k, pairKernel (canonicalPair m i) (canonicalPair k j) ≤
        ∑ i : Fin m, ∑ j : Fin k, pairWeight (canonicalPair k j) := by
          exact Finset.sum_le_sum fun i _ ↦ Finset.sum_le_sum fun j _ ↦
            pairKernel_le_right_weight _ _
    _ = (m : ℝ) * ∑ j : Fin k, pairWeight (canonicalPair k j) := by simp

lemma six_mul_nat_mul_half_pow_le {k : ℕ} (hk : 6 ≤ k) :
    6 * (k : ℝ) * (1 / 2 : ℝ) ^ k ≤ 9 / 16 := by
  induction k, hk using Nat.le_induction with
  | base => norm_num
  | succ k hk ih =>
      calc
        6 * ((k + 1 : ℕ) : ℝ) * (1 / 2 : ℝ) ^ (k + 1) ≤
            6 * (k : ℝ) * (1 / 2 : ℝ) ^ k := by
              rw [pow_succ]
              have hp : 0 ≤ (1 / 2 : ℝ) ^ k := by positivity
              have hk' : (k : ℝ) + 1 ≤ 2 * k := by
                norm_num
                exact_mod_cast (show k + 1 ≤ 2 * k by omega)
              have hm := mul_le_mul_of_nonneg_right hk' hp
              norm_num [Nat.cast_add, Nat.cast_one]
              nlinarith
        _ ≤ 9 / 16 := ih

lemma canonicalPairEnergy_le_of_five {m k : ℕ} (hmk : m ≤ k) (hk : 5 ≤ k) :
    canonicalPairEnergy m k ≤ 31 / 36 := by
  have hcard := canonicalPairEnergy_le_card_mul m k
  rw [canonicalPairWeightSum_eq] at hcard
  by_cases hk5 : k = 5
  · subst k
    norm_num at hmk ⊢
    have hm : (m : ℝ) ≤ 5 := by exact_mod_cast hmk
    have hp : 0 ≤ (1 / 2 : ℝ) ^ 5 - (1 / 3 : ℝ) ^ 5 := by norm_num
    calc
      canonicalPairEnergy m 5 ≤ (m : ℝ) * (6 * ((1 / 2 : ℝ) ^ 5 - (1 / 3 : ℝ) ^ 5)) := hcard
      _ ≤ 5 * (6 * ((1 / 2 : ℝ) ^ 5 - (1 / 3 : ℝ) ^ 5)) := by gcongr
      _ ≤ 31 / 36 := by norm_num
  · have hk6 : 6 ≤ k := by omega
    have hm : (m : ℝ) ≤ k := by exact_mod_cast hmk
    have hpow : 0 ≤ (1 / 2 : ℝ) ^ k := by positivity
    have hthird : 0 ≤ (1 / 3 : ℝ) ^ k := by positivity
    calc
      canonicalPairEnergy m k ≤ (m : ℝ) *
          (6 * ((1 / 2 : ℝ) ^ k - (1 / 3 : ℝ) ^ k)) := hcard
      _ ≤ (k : ℝ) * (6 * (1 / 2 : ℝ) ^ k) := by nlinarith
      _ = 6 * (k : ℝ) * (1 / 2 : ℝ) ^ k := by ring
      _ ≤ 9 / 16 := six_mul_nat_mul_half_pow_le hk6
      _ ≤ 31 / 36 := by norm_num

lemma canonicalPairEnergy_le (m k : ℕ)
    (h11 : ¬(m = 1 ∧ k = 1)) (h22 : ¬(m = 2 ∧ k = 2)) :
    canonicalPairEnergy m k ≤ 31 / 36 := by
  wlog hmk : m ≤ k generalizing m k
  · rw [canonicalPairEnergy_comm]
    exact this k m (by simpa [and_comm] using h11) (by simpa [and_comm] using h22) (by omega)
  by_cases hk : 5 ≤ k
  · exact canonicalPairEnergy_le_of_five hmk hk
  · have hm : m ≤ 4 := by omega
    have hk' : k ≤ 4 := by omega
    interval_cases m <;> interval_cases k <;>
      first | contradiction |
        norm_num [canonicalPairEnergy, pairKernel, canonicalPair, Fin.sum_univ_succ]

def onePair : Finset Exp2 := {(0, 0)}
def twoPair : Finset Exp2 := {(0, 1), (1, 0)}

lemma pairWeight_le_one (x : Exp2) : pairWeight x ≤ 1 := by
  unfold pairWeight
  have h2 : (1 / 2 : ℝ) ^ x.1 ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
  have h3 : (1 / 3 : ℝ) ^ x.2 ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
  calc
    (1 / 2 : ℝ) ^ x.1 * (1 / 3 : ℝ) ^ x.2 ≤ 1 * (1 / 3 : ℝ) ^ x.2 :=
      mul_le_mul_of_nonneg_right h2 (by positivity)
    _ ≤ 1 := by simpa using h3

lemma pairKernel_le_half_of_ne_zero {x y : Exp2} (h : x ≠ (0, 0) ∨ y ≠ (0, 0)) :
    pairKernel x y ≤ 1 / 2 := by
  rcases x with ⟨a, b⟩
  rcases y with ⟨c, d⟩
  unfold pairKernel
  have h2 : (1 / 2 : ℝ) ^ max a c ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
  have h3 : (1 / 3 : ℝ) ^ max b d ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
  rcases h with h | h
  all_goals
    by_cases hac : max a c = 0
    · have hbd : 1 ≤ max b d := by
        by_contra hbd
        apply h
        apply Prod.ext <;> omega
      have hp := pow_le_pow_of_le_one (a := (1 / 3 : ℝ)) (by norm_num) (by norm_num) hbd
      norm_num [hac]
      nlinarith
    · have hac' : 1 ≤ max a c := by omega
      have hp := pow_le_pow_of_le_one (a := (1 / 2 : ℝ)) (by norm_num) (by norm_num) hac'
      change (1 / 2 : ℝ) ^ max a c * (1 / 3 : ℝ) ^ max b d ≤ 1 / 2
      calc
        (1 / 2 : ℝ) ^ max a c * (1 / 3 : ℝ) ^ max b d ≤
            (1 / 2 : ℝ) ^ max a c * 1 :=
          mul_le_mul_of_nonneg_left h3 (by positivity)
        _ ≤ 1 / 2 := by simpa using hp

lemma pairEnergy_singletons_le {a b : Exp2} (h : ¬(a = (0, 0) ∧ b = (0, 0))) :
    pairEnergy {a} {b} ≤ 31 / 36 := by
  simp only [not_and_or] at h
  simp [pairEnergy]
  exact (pairKernel_le_half_of_ne_zero h).trans (by norm_num)

lemma two_card_boundary {A : Finset Exp2} (hA : PairAntichain A) (hc : A.card = 2)
    (hne : A ≠ twoPair) :
    (PairLe (0, 2) (pairEnum A ⟨0, by omega⟩) ∧
      PairLe (1, 0) (pairEnum A ⟨1, by omega⟩)) ∨
      (PairLe (0, 1) (pairEnum A ⟨0, by omega⟩) ∧
        PairLe (2, 0) (pairEnum A ⟨1, by omega⟩)) := by
  let i0 : Fin A.card := ⟨0, by omega⟩
  let i1 : Fin A.card := ⟨1, by omega⟩
  have h01 : i0 < i1 := by simp [i0, i1]
  have h0 := pairEnum_canonical_le hA i0
  have h1 := pairEnum_canonical_le hA i1
  simp only [hc, i0, i1] at h0 h1
  by_cases hs : 2 ≤ (pairEnum A i0).2
  · left
    exact ⟨⟨Nat.zero_le _, hs⟩, ⟨h1.1, Nat.zero_le _⟩⟩
  · by_cases hf : 2 ≤ (pairEnum A i1).1
    · right
      exact ⟨⟨Nat.zero_le _, h0.2⟩, ⟨hf, Nat.zero_le _⟩⟩
    · exfalso
      have hltfst := pairEnum_fst_strictMono hA h01
      have hltsnd := pairEnum_snd_strictAnti hA h01
      change (pairEnum A i0).1 < (pairEnum A i1).1 at hltfst
      change (pairEnum A i1).2 < (pairEnum A i0).2 at hltsnd
      have he0fst : (pairEnum A i0).1 = 0 := by omega
      have he0snd : (pairEnum A i0).2 = 1 := by omega
      have he1fst : (pairEnum A i1).1 = 1 := by omega
      have he1snd : (pairEnum A i1).2 = 0 := by omega
      have he0 : pairEnum A i0 = (0, 1) := Prod.ext he0fst he0snd
      have he1 : pairEnum A i1 = (1, 0) := Prod.ext he1fst he1snd
      apply hne
      rw [← pairEnum_image A]
      ext x
      simp only [Finset.mem_image, Finset.mem_univ, true_and, twoPair, Finset.mem_insert,
        Finset.mem_singleton]
      constructor
      · rintro ⟨i, rfl⟩
        have hi : (i : ℕ) = 0 ∨ (i : ℕ) = 1 := by omega
        rcases hi with hi | hi
        · left
          have hii : i = i0 := Fin.ext (by simpa [i0] using hi)
          simpa [hii] using he0
        · right
          have hii : i = i1 := Fin.ext (by simpa [i1] using hi)
          simpa [hii] using he1
      · intro hx
        rcases hx with rfl | rfl
        · exact ⟨i0, he0⟩
        · exact ⟨i1, he1⟩

lemma pairEnergy_two_card_left_le {A B : Finset Exp2} (hA : PairAntichain A)
    (hB : PairAntichain B) (hAc : A.card = 2) (hBc : B.card = 2)
    (hAne : A ≠ twoPair) : pairEnergy A B ≤ 31 / 36 := by
  rw [pairEnergy, sum_pairEnum A]
  simp_rw [sum_pairEnum B]
  rcases two_card_boundary hA hAc hAne with h | h
  · let T : Fin A.card → Exp2 := fun i ↦ if (i : ℕ) = 0 then (0, 2) else (1, 0)
    calc
        ∑ i : Fin A.card, ∑ j : Fin B.card, pairKernel (pairEnum A i) (pairEnum B j) ≤
            ∑ i : Fin A.card, ∑ j : Fin B.card,
              pairKernel (T i) (canonicalPair B.card j) := by
                apply Finset.sum_le_sum
                intro i hi
                apply Finset.sum_le_sum
                intro j hj
                by_cases hi0 : (i : ℕ) = 0
                · have hii : i = ⟨0, by omega⟩ := Fin.ext hi0
                  simpa [T, hi0, hii] using
                    pairKernel_anti h.1 (canonicalPair_le_pairEnum hB j)
                · have hi1 : (i : ℕ) = 1 := by omega
                  have hii : i = ⟨1, by omega⟩ := Fin.ext hi1
                  simpa [T, hi0, hii] using
                    pairKernel_anti h.2 (canonicalPair_le_pairEnum hB j)
      _ ≤ 31 / 36 := by
        dsimp [T]
        rw [hAc, hBc]
        norm_num [pairKernel, canonicalPair, Fin.sum_univ_succ]
  · let T : Fin A.card → Exp2 := fun i ↦ if (i : ℕ) = 0 then (0, 1) else (2, 0)
    calc
        ∑ i : Fin A.card, ∑ j : Fin B.card, pairKernel (pairEnum A i) (pairEnum B j) ≤
            ∑ i : Fin A.card, ∑ j : Fin B.card,
              pairKernel (T i) (canonicalPair B.card j) := by
                apply Finset.sum_le_sum
                intro i hi
                apply Finset.sum_le_sum
                intro j hj
                by_cases hi0 : (i : ℕ) = 0
                · have hii : i = ⟨0, by omega⟩ := Fin.ext hi0
                  simpa [T, hi0, hii] using
                    pairKernel_anti h.1 (canonicalPair_le_pairEnum hB j)
                · have hi1 : (i : ℕ) = 1 := by omega
                  have hii : i = ⟨1, by omega⟩ := Fin.ext hi1
                  simpa [T, hi0, hii] using
                    pairKernel_anti h.2 (canonicalPair_le_pairEnum hB j)
      _ ≤ 31 / 36 := by
        dsimp [T]
        rw [hAc, hBc]
        norm_num [pairKernel, canonicalPair, Fin.sum_univ_succ]

lemma pairEnergy_two_card_le {A B : Finset Exp2} (hA : PairAntichain A)
    (hB : PairAntichain B) (hAc : A.card = 2) (hBc : B.card = 2)
    (hne : ¬(A = twoPair ∧ B = twoPair)) : pairEnergy A B ≤ 31 / 36 := by
  rcases not_and_or.mp hne with hAne | hBne
  · exact pairEnergy_two_card_left_le hA hB hAc hBc hAne
  · rw [pairEnergy_comm]
    exact pairEnergy_two_card_left_le hB hA hBc hAc hBne

/-- BBMST Lemma 9.3 in exponent coordinates. -/
theorem three_smooth_energy_le (A B : Finset Exp2) (hA : PairAntichain A)
    (hB : PairAntichain B) (h1 : ¬(A = onePair ∧ B = onePair))
    (h23 : ¬(A = twoPair ∧ B = twoPair)) : pairEnergy A B ≤ 31 / 36 := by
  by_cases hc1 : A.card = 1 ∧ B.card = 1
  · obtain ⟨a, hAe⟩ := Finset.card_eq_one.mp hc1.1
    obtain ⟨b, hBe⟩ := Finset.card_eq_one.mp hc1.2
    subst A
    subst B
    apply pairEnergy_singletons_le
    simpa [onePair] using h1
  · by_cases hc2 : A.card = 2 ∧ B.card = 2
    · exact pairEnergy_two_card_le hA hB hc2.1 hc2.2 h23
    · exact (pairEnergy_le_canonical hA hB).trans
        (canonicalPairEnergy_le A.card B.card hc1 hc2)

def pairWeightSum (A : Finset Exp2) : ℝ := ∑ x ∈ A, pairWeight x

lemma pairWeight_anti {x y : Exp2} (h : PairLe x y) : pairWeight y ≤ pairWeight x := by
  unfold pairWeight
  exact mul_le_mul
    (pow_le_pow_of_le_one (by norm_num) (by norm_num) h.1)
    (pow_le_pow_of_le_one (by norm_num) (by norm_num) h.2) (by positivity) (by positivity)

lemma pairWeightSum_le_canonical {A : Finset Exp2} (hA : PairAntichain A) :
    pairWeightSum A ≤ canonicalPairWeightSum A.card := by
  rw [pairWeightSum, sum_pairEnum A]
  unfold canonicalPairWeightSum
  exact Finset.sum_le_sum fun i _ ↦ pairWeight_anti (canonicalPair_le_pairEnum hA i)

lemma canonicalPairWeightSum_le_one (k : ℕ) : canonicalPairWeightSum k ≤ 1 := by
  rw [canonicalPairWeightSum_eq]
  by_cases hk : k ≤ 2
  · interval_cases k <;> norm_num
  · have hk3 : 3 ≤ k := by omega
    have hh := pow_le_pow_of_le_one (a := (1 / 2 : ℝ)) (by norm_num) (by norm_num) hk3
    have ht : 0 ≤ (1 / 3 : ℝ) ^ k := by positivity
    norm_num at hh ⊢
    nlinarith

lemma pairWeightSum_le_one {A : Finset Exp2} (hA : PairAntichain A) :
    pairWeightSum A ≤ 1 :=
  (pairWeightSum_le_canonical hA).trans (canonicalPairWeightSum_le_one _)

lemma pairWeight_le_half_of_ne_zero {x : Exp2} (hx : x ≠ (0, 0)) :
    pairWeight x ≤ 1 / 2 := by
  rcases x with ⟨a, b⟩
  unfold pairWeight
  by_cases ha : a = 0
  · have hb : 1 ≤ b := by
      by_contra hb
      apply hx
      apply Prod.ext <;> omega
    have hp := pow_le_pow_of_le_one (a := (1 / 3 : ℝ)) (by norm_num) (by norm_num) hb
    simpa [ha] using hp.trans (by norm_num : (1 / 3 : ℝ) ^ 1 ≤ 1 / 2)
  · have ha' : 1 ≤ a := by omega
    have hp := pow_le_pow_of_le_one (a := (1 / 2 : ℝ)) (by norm_num) (by norm_num) ha'
    have h3 : (1 / 3 : ℝ) ^ b ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
    have hp0 : 0 ≤ (1 / 2 : ℝ) ^ a := by positivity
    calc
      (1 / 2 : ℝ) ^ a * (1 / 3 : ℝ) ^ b ≤ (1 / 2 : ℝ) ^ a * 1 :=
        mul_le_mul_of_nonneg_left h3 hp0
      _ ≤ 1 / 2 := by simpa using hp

lemma pairWeightSum_two_boundary_le {A : Finset Exp2} (hA : PairAntichain A)
    (hc : A.card = 2) (hne : A ≠ twoPair) : pairWeightSum A ≤ 11 / 18 := by
  rw [pairWeightSum, sum_pairEnum A]
  rcases two_card_boundary hA hc hne with h | h
  · let T : Fin A.card → Exp2 := fun i ↦ if (i : ℕ) = 0 then (0, 2) else (1, 0)
    calc
      ∑ i : Fin A.card, pairWeight (pairEnum A i) ≤ ∑ i : Fin A.card, pairWeight (T i) := by
        apply Finset.sum_le_sum
        intro i hi
        by_cases hi0 : (i : ℕ) = 0
        · have hii : i = ⟨0, by omega⟩ := Fin.ext hi0
          simpa [T, hi0, hii] using pairWeight_anti h.1
        · have hi1 : (i : ℕ) = 1 := by omega
          have hii : i = ⟨1, by omega⟩ := Fin.ext hi1
          simpa [T, hi0, hii] using pairWeight_anti h.2
      _ ≤ 11 / 18 := by
        dsimp [T]
        rw [hc]
        norm_num [pairWeight, Fin.sum_univ_succ]
  · let T : Fin A.card → Exp2 := fun i ↦ if (i : ℕ) = 0 then (0, 1) else (2, 0)
    calc
      ∑ i : Fin A.card, pairWeight (pairEnum A i) ≤ ∑ i : Fin A.card, pairWeight (T i) := by
        apply Finset.sum_le_sum
        intro i hi
        by_cases hi0 : (i : ℕ) = 0
        · have hii : i = ⟨0, by omega⟩ := Fin.ext hi0
          simpa [T, hi0, hii] using pairWeight_anti h.1
        · have hi1 : (i : ℕ) = 1 := by omega
          have hii : i = ⟨1, by omega⟩ := Fin.ext hi1
          simpa [T, hi0, hii] using pairWeight_anti h.2
      _ ≤ 11 / 18 := by
        dsimp [T]
        rw [hc]
        norm_num [pairWeight, Fin.sum_univ_succ]

lemma pairWeightSum_ne_origin_le {A : Finset Exp2} (hA : PairAntichain A)
    (h0 : (0, 0) ∉ A) : pairWeightSum A ≤ 5 / 6 := by
  by_cases hcard : A.card = 0
  · rw [Finset.card_eq_zero.mp hcard]
    norm_num [pairWeightSum]
  by_cases hcard1 : A.card = 1
  · obtain ⟨x, rfl⟩ := Finset.card_eq_one.mp hcard1
    simp only [Finset.mem_singleton] at h0
    simpa [pairWeightSum] using (pairWeight_le_half_of_ne_zero (fun e ↦ h0 e.symm)).trans
      (by norm_num : (1 / 2 : ℝ) ≤ 5 / 6)
  · exact (pairWeightSum_le_canonical hA).trans <| by
      rw [canonicalPairWeightSum_eq]
      have hk : 2 ≤ A.card := by omega
      by_cases heq : A.card = 2
      · rw [heq]
        norm_num
      · have hk3 : 3 ≤ A.card := by omega
        have hh := pow_le_pow_of_le_one (a := (1 / 2 : ℝ)) (by norm_num) (by norm_num) hk3
        have ht : 0 ≤ (1 / 3 : ℝ) ^ A.card := by positivity
        norm_num at hh ⊢
        nlinarith

lemma pairWeightSum_ne_origin_ne_two_le {A : Finset Exp2} (hA : PairAntichain A)
    (h0 : (0, 0) ∉ A) (h2 : A ≠ twoPair) : pairWeightSum A ≤ 11 / 18 := by
  by_cases hc0 : A.card = 0
  · rw [Finset.card_eq_zero.mp hc0]
    norm_num [pairWeightSum]
  by_cases hc1 : A.card = 1
  · obtain ⟨x, rfl⟩ := Finset.card_eq_one.mp hc1
    simp only [Finset.mem_singleton] at h0
    simpa [pairWeightSum] using (pairWeight_le_half_of_ne_zero (fun e ↦ h0 e.symm)).trans
      (by norm_num : (1 / 2 : ℝ) ≤ 11 / 18)
  by_cases hc2 : A.card = 2
  · exact pairWeightSum_two_boundary_le hA hc2 h2
  · have hc3 : 3 ≤ A.card := by omega
    calc
      pairWeightSum A ≤ canonicalPairWeightSum A.card := pairWeightSum_le_canonical hA
      _ = 6 * ((1 / 2 : ℝ) ^ A.card - (1 / 3 : ℝ) ^ A.card) :=
        canonicalPairWeightSum_eq A.card
      _ ≤ 11 / 18 := by
        by_cases hc : A.card = 3
        · rw [hc]
          norm_num
        · have hc4 : 4 ≤ A.card := by omega
          have hh := pow_le_pow_of_le_one (a := (1 / 2 : ℝ)) (by norm_num) (by norm_num) hc4
          have ht : 0 ≤ (1 / 3 : ℝ) ^ A.card := by positivity
          norm_num at hh ⊢
          nlinarith

lemma fin_strictMono_nat_add_le {k c : ℕ} {f : Fin k → ℕ} (hf : StrictMono f)
    (hmin : ∀ i, c ≤ f i) (i : Fin k) : c + (i : ℕ) ≤ f i := by
  induction hn : (i : ℕ) using Nat.strong_induction_on generalizing i with
  | h n ih =>
      by_cases hn0 : n = 0
      · simpa [hn0, hn] using hmin i
      · let j : Fin k := ⟨n - 1, by omega⟩
        have hjval : (j : ℕ) = n - 1 := rfl
        have hji : j < i := by apply Fin.mk_lt_mk.mpr; rw [hn]; omega
        have hj := ih (n - 1) (by omega) j hjval
        have hfij := hf hji
        omega

lemma fin_strictAnti_nat_add_rev_le {k c : ℕ} {f : Fin k → ℕ} (hf : StrictAnti f)
    (hmin : ∀ i, c ≤ f i) (i : Fin k) : c + (k - 1 - (i : ℕ)) ≤ f i := by
  have hg : StrictMono (f ∘ Fin.rev) := hf.comp Fin.rev_strictAnti
  have hgmin : ∀ j, c ≤ (f ∘ Fin.rev) j := fun j ↦ hmin _
  have h := fin_strictMono_nat_add_le hg hgmin i.rev
  simp only [Function.comp_apply, Fin.rev_rev] at h
  rw [Fin.val_rev] at h
  omega

lemma pairWeightSum_le_scaled {A : Finset Exp2} (hA : PairAntichain A) {a b : ℕ}
    (ha : ∀ x ∈ A, a ≤ x.1) (hb : ∀ x ∈ A, b ≤ x.2) :
    pairWeightSum A ≤ (1 / 2 : ℝ) ^ a * (1 / 3 : ℝ) ^ b := by
  rw [pairWeightSum, sum_pairEnum A]
  have hfst : ∀ i : Fin A.card, a + (i : ℕ) ≤ (pairEnum A i).1 :=
    fin_strictMono_nat_add_le (pairEnum_fst_strictMono hA) (fun i ↦ ha _ (pairEnum_mem A i))
  have hsnd : ∀ i : Fin A.card, b + (A.card - 1 - (i : ℕ)) ≤ (pairEnum A i).2 :=
    fin_strictAnti_nat_add_rev_le (pairEnum_snd_strictAnti hA)
      (fun i ↦ hb _ (pairEnum_mem A i))
  calc
    ∑ i : Fin A.card, pairWeight (pairEnum A i) ≤
        ∑ i : Fin A.card, (1 / 2 : ℝ) ^ (a + (i : ℕ)) *
          (1 / 3 : ℝ) ^ (b + (A.card - 1 - (i : ℕ))) := by
            exact Finset.sum_le_sum fun i _ ↦
              pairWeight_anti (x := (a + (i : ℕ), b + (A.card - 1 - (i : ℕ))))
                (y := pairEnum A i) ⟨hfst i, hsnd i⟩
    _ = (1 / 2 : ℝ) ^ a * (1 / 3 : ℝ) ^ b * canonicalPairWeightSum A.card := by
      unfold canonicalPairWeightSum pairWeight canonicalPair
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      simp only [Prod.fst, Prod.snd, pow_add]
      ring
    _ ≤ (1 / 2 : ℝ) ^ a * (1 / 3 : ℝ) ^ b := by
      have hc := canonicalPairWeightSum_le_one A.card
      have hp : 0 ≤ (1 / 2 : ℝ) ^ a * (1 / 3 : ℝ) ^ b := by positivity
      nlinarith

def triplePair (x : Exp3) : Exp2 := (x.1, x.2.1)
def tripleThird (x : Exp3) : ℕ := x.2.2
def mkTriple (x : Exp2) (c : ℕ) : Exp3 := (x.1, x.2, c)

def tripleLevel (A : Finset Exp3) (c : ℕ) : Finset Exp2 :=
  (A.filter fun x ↦ tripleThird x = c).image triplePair

def tripleLevelSupport (A : Finset Exp3) : Finset ℕ := A.image tripleThird

lemma mem_tripleLevel {A : Finset Exp3} {c : ℕ} {x : Exp2} :
    x ∈ tripleLevel A c ↔ mkTriple x c ∈ A := by
  constructor
  · simp only [tripleLevel, Finset.mem_image, Finset.mem_filter]
    rintro ⟨y, ⟨hyA, hyc⟩, hy⟩
    rcases y with ⟨u, v, w⟩
    simp only [tripleThird, triplePair, mkTriple, Prod.mk.injEq] at hyc hy ⊢
    aesop
  · intro hx
    refine Finset.mem_image.mpr ⟨mkTriple x c, ?_, ?_⟩
    · exact Finset.mem_filter.mpr ⟨hx, rfl⟩
    · rfl

lemma tripleLevel_antichain {A : Finset Exp3} (hA : TripleAntichain A) (c : ℕ) :
    PairAntichain (tripleLevel A c) := by
  intro x hx y hy hxy hle
  have heq := hA.eq (mem_tripleLevel.mp hx) (mem_tripleLevel.mp hy) ⟨hle.1, hle.2, le_rfl⟩
  have hp := congr_arg (fun z : Exp3 ↦ (z.1, z.2.1)) heq
  change x = y at hp
  exact hxy hp

lemma pairWeightSum_tripleLevel (A : Finset Exp3) (c : ℕ) :
    pairWeightSum (tripleLevel A c) =
      ∑ x ∈ A.filter (fun x ↦ tripleThird x = c), pairWeight (triplePair x) := by
  unfold pairWeightSum tripleLevel
  rw [Finset.sum_image]
  intro x hx y hy hxy
  rcases x with ⟨a, b, d⟩
  rcases y with ⟨a', b', d'⟩
  have hd : d = c := by simpa [tripleThird] using (Finset.mem_filter.mp hx).2
  have hd' : d' = c := by simpa [tripleThird] using (Finset.mem_filter.mp hy).2
  simp only [triplePair] at hxy
  obtain ⟨rfl, rfl⟩ := hxy
  exact Prod.ext rfl (Prod.ext rfl (hd.trans hd'.symm))

lemma sum_over_triple_levels (A : Finset Exp3) (f : Exp3 → ℝ) :
    ∑ c ∈ tripleLevelSupport A, ∑ x ∈ A.filter (fun x ↦ tripleThird x = c), f x =
      ∑ x ∈ A, f x := by
  simp_rw [Finset.sum_filter]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x hx
  have hmem : tripleThird x ∈ tripleLevelSupport A := by
    exact Finset.mem_image.mpr ⟨x, hx, rfl⟩
  simp [hmem]

lemma tripleWeight_sum_eq_levels (A : Finset Exp3) :
    ∑ x ∈ A, tripleWeight x =
      ∑ c ∈ tripleLevelSupport A, (1 / 5 : ℝ) ^ c * pairWeightSum (tripleLevel A c) := by
  rw [← sum_over_triple_levels A tripleWeight]
  apply Finset.sum_congr rfl
  intro c hc
  rw [pairWeightSum_tripleLevel]
  simp_rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x hx
  have hxc := (Finset.mem_filter.mp hx).2
  rcases x with ⟨a, b, d⟩
  simp only [tripleThird] at hxc
  subst d
  unfold tripleWeight pairWeight triplePair
  ring

def PrimePowerExp (x : Exp3) : Prop :=
  (0 < x.1 ∧ x.2.1 = 0 ∧ x.2.2 = 0) ∨
    (x.1 = 0 ∧ 0 < x.2.1 ∧ x.2.2 = 0) ∨
    (x.1 = 0 ∧ x.2.1 = 0 ∧ 0 < x.2.2)

lemma geometric_finset_le_tail (s : Finset ℕ) (N : ℕ) {r : ℝ}
    (hr0 : 0 ≤ r) (hr1 : r < 1) (hs : ∀ n ∈ s, N ≤ n) :
    ∑ n ∈ s, r ^ n ≤ r ^ N * (1 - r)⁻¹ := by
  let t := s.image (fun n ↦ n - N)
  have hinj : Set.InjOn (fun n ↦ n - N) (s : Set ℕ) := by
    intro a ha b hb hab
    have haN := hs a ha
    have hbN := hs b hb
    change a - N = b - N at hab
    have hae := Nat.sub_add_cancel haN
    have hbe := Nat.sub_add_cancel hbN
    omega
  have heq : ∑ n ∈ s, r ^ n = r ^ N * ∑ n ∈ t, r ^ n := by
    rw [Finset.mul_sum, Finset.sum_image hinj]
    apply Finset.sum_congr rfl
    intro n hn
    rw [← pow_add]
    congr 1
    exact (Nat.add_sub_of_le (hs n hn)).symm
  rw [heq]
  exact mul_le_mul_of_nonneg_left (geometric_finset_le t hr0 hr1) (pow_nonneg hr0 N)

lemma tripleLevel_zero_positive {A : Finset Exp3}
    (hne : ∀ x ∈ A, x ≠ (0, 0, 0)) (hnpp : ∀ x ∈ A, ¬PrimePowerExp x) :
    ∀ x ∈ tripleLevel A 0, 1 ≤ x.1 ∧ 1 ≤ x.2 := by
  intro x hx
  have hxA := mem_tripleLevel.mp hx
  have hne' := hne _ hxA
  have hnpp' := hnpp _ hxA
  rcases x with ⟨a, b⟩
  constructor
  · by_contra ha
    have ha0 : a = 0 := by omega
    have hbpos : 0 < b := by
      by_contra hb
      apply hne'
      simp [mkTriple, ha0, show b = 0 by omega]
    apply hnpp'
    simp [PrimePowerExp, mkTriple, ha0, hbpos]
  · by_contra hb
    have hb0 : b = 0 := by omega
    have hapos : 0 < a := by
      by_contra ha
      apply hne'
      simp [mkTriple, hb0, show a = 0 by omega]
    apply hnpp'
    simp [PrimePowerExp, mkTriple, hb0, hapos]

lemma tripleLevel_origin_not_mem {A : Finset Exp3}
    (hnpp : ∀ x ∈ A, ¬PrimePowerExp x) {c : ℕ} (hc : 0 < c) :
    (0, 0) ∉ tripleLevel A c := by
  intro hmem
  have hxA := mem_tripleLevel.mp hmem
  have := hnpp _ hxA
  simp [PrimePowerExp, mkTriple, hc] at this

lemma later_level_empty_of_level_one_eq_two {A : Finset Exp3} (hA : TripleAntichain A)
    (hnpp : ∀ x ∈ A, ¬PrimePowerExp x) (h1 : tripleLevel A 1 = twoPair)
    {c : ℕ} (hc : 1 < c) : tripleLevel A c = ∅ := by
  have h10 : (1, 0) ∈ tripleLevel A 1 := by simp [h1, twoPair]
  have h01 : (0, 1) ∈ tripleLevel A 1 := by simp [h1, twoPair]
  apply Finset.ext
  intro x
  constructor
  · intro hx
    have horigin : (0, 0) ∉ tripleLevel A c :=
      tripleLevel_origin_not_mem hnpp (c := c) (by omega)
    have hx0 : x ≠ (0, 0) := by
      intro h
      subst x
      exact horigin hx
    have hxA := mem_tripleLevel.mp hx
    rcases x with ⟨a, b⟩
    rcases lt_or_ge 0 a with ha | ha
    · have heq := hA.eq (mem_tripleLevel.mp h10) hxA
          (show TripleLe (mkTriple (1, 0) 1) (mkTriple (a, b) c) by
            change 1 ≤ a ∧ 0 ≤ b ∧ 1 ≤ c
            omega)
      simp [mkTriple] at heq
      omega
    · have ha0 : a = 0 := by omega
      have hb : 0 < b := by
        by_contra hb
        have hb0 : b = 0 := by omega
        exact hx0 (Prod.ext ha0 hb0)
      have heq := hA.eq (mem_tripleLevel.mp h01) hxA
          (show TripleLe (mkTriple (0, 1) 1) (mkTriple (a, b) c) by
            change 0 ≤ a ∧ 1 ≤ b ∧ 1 ≤ c
            omega)
      simp [mkTriple] at heq
      omega
  · intro hx
    exact (Finset.notMem_empty x hx).elim

lemma weighted_level_zero_le {A : Finset Exp3} (hA : TripleAntichain A)
    (hne : ∀ x ∈ A, x ≠ (0, 0, 0)) (hnpp : ∀ x ∈ A, ¬PrimePowerExp x) :
    pairWeightSum (tripleLevel A 0) ≤ 1 / 6 := by
  have h := pairWeightSum_le_scaled (tripleLevel_antichain hA 0)
    (fun x hx ↦ (tripleLevel_zero_positive hne hnpp x hx).1)
    (fun x hx ↦ (tripleLevel_zero_positive hne hnpp x hx).2)
  norm_num at h ⊢
  exact h

lemma sum_piecewise_reciprocal_bound (S : Finset ℕ) :
    ∑ c ∈ S, (if c = 0 then (1 / 6 : ℝ)
      else if c = 1 then 11 / 90 else (5 / 6 : ℝ) * (1 / 5 : ℝ) ^ c) ≤ 119 / 360 := by
  have htail : ∑ c ∈ S.filter (fun c ↦ 2 ≤ c), (1 / 5 : ℝ) ^ c ≤ 1 / 20 := by
    calc
      ∑ c ∈ S.filter (fun c ↦ 2 ≤ c), (1 / 5 : ℝ) ^ c ≤
          (1 / 5 : ℝ) ^ 2 * (1 - (1 / 5 : ℝ))⁻¹ :=
        geometric_finset_le_tail _ 2 (by norm_num) (by norm_num) (by simp_all)
      _ = 1 / 20 := by norm_num
  have hrewrite :
      ∑ c ∈ S, (if c = 0 then (1 / 6 : ℝ)
        else if c = 1 then 11 / 90 else (5 / 6 : ℝ) * (1 / 5 : ℝ) ^ c) =
      (∑ c ∈ S, if c = 0 then (1 / 6 : ℝ) else 0) +
      (∑ c ∈ S, if c = 1 then (11 / 90 : ℝ) else 0) +
      (5 / 6 : ℝ) * ∑ c ∈ S.filter (fun c ↦ 2 ≤ c), (1 / 5 : ℝ) ^ c := by
    rw [Finset.mul_sum]
    simp_rw [Finset.sum_filter]
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro c hc
    by_cases h0 : c = 0 <;> by_cases h1 : c = 1 <;> simp [h0, h1]
    omega
  rw [hrewrite]
  have hzero : (∑ c ∈ S, if c = 0 then (1 / 6 : ℝ) else 0) ≤ 1 / 6 := by
    simp only [Finset.sum_ite_eq', Finset.mem_filter]
    split <;> norm_num
  have hone : (∑ c ∈ S, if c = 1 then (11 / 90 : ℝ) else 0) ≤ 11 / 90 := by
    simp only [Finset.sum_ite_eq', Finset.mem_filter]
    split <;> norm_num
  nlinarith

/-- BBMST Lemma 9.2 in exponent coordinates. -/
theorem five_smooth_reciprocal_le (A : Finset Exp3) (hA : TripleAntichain A)
    (hne : ∀ x ∈ A, x ≠ (0, 0, 0)) (hnpp : ∀ x ∈ A, ¬PrimePowerExp x) :
    ∑ x ∈ A, tripleWeight x ≤ 1 / 3 := by
  rw [tripleWeight_sum_eq_levels]
  by_cases htwo : tripleLevel A 1 = twoPair
  · calc
      ∑ c ∈ tripleLevelSupport A, (1 / 5 : ℝ) ^ c * pairWeightSum (tripleLevel A c) ≤
          ∑ c ∈ tripleLevelSupport A,
            (if c = 0 then (1 / 6 : ℝ) else if c = 1 then 1 / 6 else 0) := by
              apply Finset.sum_le_sum
              intro c hc
              by_cases hc0 : c = 0
              · subst c
                norm_num
                exact weighted_level_zero_le hA hne hnpp
              · by_cases hc1 : c = 1
                · subst c
                  rw [htwo]
                  norm_num [pairWeightSum, twoPair, pairWeight]
                · have hcgt : 1 < c := by omega
                  rw [later_level_empty_of_level_one_eq_two hA hnpp htwo hcgt]
                  simp [pairWeightSum, hc0, hc1]
      _ ≤ 1 / 3 := by
        have h0 : (∑ c ∈ tripleLevelSupport A, if c = 0 then (1 / 6 : ℝ) else 0) ≤ 1 / 6 := by
          simp only [Finset.sum_ite_eq']; split <;> norm_num
        have h1 : (∑ c ∈ tripleLevelSupport A, if c = 1 then (1 / 6 : ℝ) else 0) ≤ 1 / 6 := by
          simp only [Finset.sum_ite_eq']; split <;> norm_num
        rw [show (∑ c ∈ tripleLevelSupport A,
          (if c = 0 then (1 / 6 : ℝ) else if c = 1 then 1 / 6 else 0)) =
          (∑ c ∈ tripleLevelSupport A, if c = 0 then (1 / 6 : ℝ) else 0) +
          (∑ c ∈ tripleLevelSupport A, if c = 1 then (1 / 6 : ℝ) else 0) by
            rw [← Finset.sum_add_distrib]
            apply Finset.sum_congr rfl
            intro c hc
            by_cases h0c : c = 0 <;> by_cases h1c : c = 1 <;> simp [h0c, h1c]]
        linarith
  · calc
      ∑ c ∈ tripleLevelSupport A, (1 / 5 : ℝ) ^ c * pairWeightSum (tripleLevel A c) ≤
          ∑ c ∈ tripleLevelSupport A,
            (if c = 0 then (1 / 6 : ℝ)
              else if c = 1 then 11 / 90 else (5 / 6 : ℝ) * (1 / 5 : ℝ) ^ c) := by
                apply Finset.sum_le_sum
                intro c hc
                by_cases hc0 : c = 0
                · subst c
                  norm_num
                  exact weighted_level_zero_le hA hne hnpp
                · have horigin := tripleLevel_origin_not_mem hnpp (show 0 < c by omega)
                  by_cases hc1 : c = 1
                  · subst c
                    norm_num
                    have hlev := pairWeightSum_ne_origin_ne_two_le
                      (tripleLevel_antichain hA 1) horigin htwo
                    nlinarith
                  · have hlev := pairWeightSum_ne_origin_le (tripleLevel_antichain hA c) horigin
                    simp only [hc0, hc1, if_false]
                    have hp : 0 ≤ (1 / 5 : ℝ) ^ c := pow_nonneg (by norm_num) c
                    nlinarith
      _ ≤ 119 / 360 := sum_piecewise_reciprocal_bound _
      _ ≤ 1 / 3 := by norm_num

lemma pairEnergy_tripleLevels (A B : Finset Exp3) (c d : ℕ) :
    pairEnergy (tripleLevel A c) (tripleLevel B d) =
      ∑ x ∈ A.filter (fun x ↦ tripleThird x = c),
        ∑ y ∈ B.filter (fun y ↦ tripleThird y = d), pairKernel (triplePair x) (triplePair y) := by
  have hinjA : Set.InjOn triplePair (A.filter (fun x ↦ tripleThird x = c) : Set Exp3) := by
    intro x hx y hy hxy
    rcases x with ⟨a, b, e⟩
    rcases y with ⟨a', b', e'⟩
    have he : e = c := by simpa [tripleThird] using (Finset.mem_filter.mp hx).2
    have he' : e' = c := by simpa [tripleThird] using (Finset.mem_filter.mp hy).2
    simp only [triplePair] at hxy
    obtain ⟨rfl, rfl⟩ := hxy
    exact Prod.ext rfl (Prod.ext rfl (he.trans he'.symm))
  have hinjB : Set.InjOn triplePair (B.filter (fun y ↦ tripleThird y = d) : Set Exp3) := by
    intro x hx y hy hxy
    rcases x with ⟨a, b, e⟩
    rcases y with ⟨a', b', e'⟩
    have he : e = d := by simpa [tripleThird] using (Finset.mem_filter.mp hx).2
    have he' : e' = d := by simpa [tripleThird] using (Finset.mem_filter.mp hy).2
    simp only [triplePair] at hxy
    obtain ⟨rfl, rfl⟩ := hxy
    exact Prod.ext rfl (Prod.ext rfl (he.trans he'.symm))
  unfold pairEnergy tripleLevel
  rw [Finset.sum_image hinjA]
  apply Finset.sum_congr rfl
  intro x hx
  rw [Finset.sum_image hinjB]

lemma tripleEnergy_eq_levels (A B : Finset Exp3) :
    tripleEnergy A B =
      ∑ c ∈ tripleLevelSupport A, ∑ d ∈ tripleLevelSupport B,
        (1 / 5 : ℝ) ^ max c d * pairEnergy (tripleLevel A c) (tripleLevel B d) := by
  unfold tripleEnergy
  rw [← sum_over_triple_levels A (fun x ↦ ∑ y ∈ B, tripleKernel x y)]
  apply Finset.sum_congr rfl
  intro c hc
  rw [Finset.sum_comm]
  rw [← sum_over_triple_levels B
    (fun y ↦ ∑ x ∈ A.filter (fun x ↦ tripleThird x = c), tripleKernel x y)]
  apply Finset.sum_congr rfl
  intro d hd
  rw [pairEnergy_tripleLevels, Finset.sum_comm, Finset.mul_sum]
  simp_rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro y hy
  apply Finset.sum_congr rfl
  intro x hx
  have hxc := (Finset.mem_filter.mp hx).2
  have hyd := (Finset.mem_filter.mp hy).2
  change x.2.2 = d at hxc
  change y.2.2 = c at hyd
  unfold tripleKernel pairKernel triplePair
  rw [hxc, hyd]
  ring

lemma max_geometric_row_le (S : Finset ℕ) (i : ℕ) :
    ∑ j ∈ S, (1 / 5 : ℝ) ^ max i j ≤
      ((i : ℝ) + 1) * (1 / 5 : ℝ) ^ i + (1 / 4 : ℝ) * (1 / 5 : ℝ) ^ i := by
  let L := S.filter (fun j ↦ j ≤ i)
  let R := S.filter (fun j ↦ i < j)
  have hsplit : ∑ j ∈ S, (1 / 5 : ℝ) ^ max i j =
      ∑ j ∈ L, (1 / 5 : ℝ) ^ max i j + ∑ j ∈ R, (1 / 5 : ℝ) ^ max i j := by
    rw [← Finset.sum_union]
    · apply Finset.sum_congr
      · ext j
        simp only [L, R, Finset.mem_union, Finset.mem_filter]
        constructor
        · intro hj
          by_cases hji : j ≤ i
          · exact Or.inl ⟨hj, hji⟩
          · exact Or.inr ⟨hj, by omega⟩
        · rintro (⟨hj, -⟩ | ⟨hj, -⟩) <;> exact hj
      · simp
    · rw [Finset.disjoint_left]
      intro j hjL hjR
      simp only [L, R, Finset.mem_filter] at hjL hjR
      omega
  rw [hsplit]
  have hLcard : L.card ≤ i + 1 := by
    have hsub : L ⊆ Finset.range (i + 1) := by
      intro j hj
      simp only [L, Finset.mem_filter] at hj
      simpa [Finset.mem_range] using hj.2
    simpa using Finset.card_le_card hsub
  have hL : ∑ j ∈ L, (1 / 5 : ℝ) ^ max i j ≤ ((i : ℝ) + 1) * (1 / 5 : ℝ) ^ i := by
    have heq : ∑ j ∈ L, (1 / 5 : ℝ) ^ max i j =
        (L.card : ℝ) * (1 / 5 : ℝ) ^ i := by
      calc
        ∑ j ∈ L, (1 / 5 : ℝ) ^ max i j = ∑ _j ∈ L, (1 / 5 : ℝ) ^ i := by
          apply Finset.sum_congr rfl
          intro j hj
          rw [max_eq_left]
          exact (Finset.mem_filter.mp hj).2
        _ = (L.card : ℝ) * (1 / 5 : ℝ) ^ i := by simp
    rw [heq]
    have hc : (L.card : ℝ) ≤ (i : ℝ) + 1 := by exact_mod_cast hLcard
    exact mul_le_mul_of_nonneg_right hc (by positivity)
  have hR : ∑ j ∈ R, (1 / 5 : ℝ) ^ max i j ≤ (1 / 4 : ℝ) * (1 / 5 : ℝ) ^ i := by
    have ht := geometric_finset_le_tail R (i + 1) (r := (1 / 5 : ℝ))
      (by norm_num) (by norm_num) (by intro j hj; simp [R] at hj; omega)
    have heq : ∑ j ∈ R, (1 / 5 : ℝ) ^ max i j = ∑ j ∈ R, (1 / 5 : ℝ) ^ j := by
      apply Finset.sum_congr rfl
      intro j hj
      rw [max_eq_right]
      exact (Finset.mem_filter.mp hj).2.le
    rw [heq]
    calc
      ∑ j ∈ R, (1 / 5 : ℝ) ^ j ≤ (1 / 5 : ℝ) ^ (i + 1) *
          (1 - (1 / 5 : ℝ))⁻¹ := ht
      _ = (1 / 4 : ℝ) * (1 / 5 : ℝ) ^ i := by rw [pow_succ]; norm_num; ring
  linarith

lemma max_geometric_finsets_le (S T : Finset ℕ) :
    ∑ i ∈ S, ∑ j ∈ T, (1 / 5 : ℝ) ^ max i j ≤ 15 / 8 := by
  have hpoint : ∀ i ∈ S, (∑ j ∈ T, (1 / 5 : ℝ) ^ max i j) ≤
      ((i : ℝ) + 1) * (1 / 5 : ℝ) ^ i + (1 / 4 : ℝ) * (1 / 5 : ℝ) ^ i :=
    fun i _ ↦ max_geometric_row_le T i
  have hn := hasSum_coe_mul_geometric_of_norm_lt_one (𝕜 := ℝ)
    (r := (1 / 5 : ℝ)) (by norm_num)
  have hg := hasSum_geometric_of_norm_lt_one (ξ := (1 / 5 : ℝ)) (by norm_num)
  have hsum := hn.add ((hg.mul_left (5 / 4 : ℝ)))
  have hsummable : Summable (fun i : ℕ ↦
      ((i : ℝ) + 1) * (1 / 5 : ℝ) ^ i + (1 / 4 : ℝ) * (1 / 5 : ℝ) ^ i) := by
    have hs := hsum.summable
    apply hs.congr
    intro i
    ring
  calc
    ∑ i ∈ S, ∑ j ∈ T, (1 / 5 : ℝ) ^ max i j ≤
        ∑ i ∈ S, (((i : ℝ) + 1) * (1 / 5 : ℝ) ^ i +
          (1 / 4 : ℝ) * (1 / 5 : ℝ) ^ i) := Finset.sum_le_sum hpoint
    _ ≤ ∑' i : ℕ, (((i : ℝ) + 1) * (1 / 5 : ℝ) ^ i +
          (1 / 4 : ℝ) * (1 / 5 : ℝ) ^ i) := hsummable.sum_le_tsum S
            (fun i hi ↦ by positivity)
    _ = 15 / 8 := by
      calc
        ∑' i : ℕ, (((i : ℝ) + 1) * (1 / 5 : ℝ) ^ i +
            (1 / 4 : ℝ) * (1 / 5 : ℝ) ^ i) =
            ∑' i : ℕ, ((i : ℝ) * (1 / 5 : ℝ) ^ i +
              (5 / 4 : ℝ) * (1 / 5 : ℝ) ^ i) := by
                apply tsum_congr
                intro i
                ring
        _ = (1 / 5 : ℝ) / (1 - 1 / 5) ^ 2 +
            (5 / 4 : ℝ) * (1 - 1 / 5)⁻¹ := hsum.tsum_eq
        _ = 15 / 8 := by norm_num

def SingleAt (A : Finset Exp3) (c : ℕ) : Prop := tripleLevel A c = onePair
def DoubleAt (A : Finset Exp3) (c : ℕ) : Prop := tripleLevel A c = twoPair

lemma singleAt_mem_support {A : Finset Exp3} {c : ℕ} (h : SingleAt A c) :
    c ∈ tripleLevelSupport A := by
  change tripleLevel A c = onePair at h
  have hm : (0, 0) ∈ tripleLevel A c := by rw [h]; simp [onePair]
  have hA := mem_tripleLevel.mp hm
  exact Finset.mem_image.mpr ⟨mkTriple (0, 0) c, hA, rfl⟩

lemma doubleAt_mem_support {A : Finset Exp3} {c : ℕ} (h : DoubleAt A c) :
    c ∈ tripleLevelSupport A := by
  change tripleLevel A c = twoPair at h
  have hm : (1, 0) ∈ tripleLevel A c := by rw [h]; simp [twoPair]
  have hA := mem_tripleLevel.mp hm
  exact Finset.mem_image.mpr ⟨mkTriple (1, 0) c, hA, rfl⟩

lemma singleAt_unique {A : Finset Exp3} (hA : TripleAntichain A)
    {r s : ℕ} (hr : SingleAt A r) (hs : SingleAt A s) : r = s := by
  change tripleLevel A r = onePair at hr
  change tripleLevel A s = onePair at hs
  have hrm : (0, 0) ∈ tripleLevel A r := by rw [hr]; simp [onePair]
  have hsm : (0, 0) ∈ tripleLevel A s := by rw [hs]; simp [onePair]
  rcases le_total r s with hrs | hsr
  · have heq := hA.eq (mem_tripleLevel.mp hrm) (mem_tripleLevel.mp hsm)
      (show TripleLe (mkTriple (0, 0) r) (mkTriple (0, 0) s) by exact ⟨le_rfl, le_rfl, hrs⟩)
    have ht := congr_arg (fun x : Exp3 ↦ x.2.2) heq
    simpa [mkTriple] using ht
  · have heq := hA.eq (mem_tripleLevel.mp hsm) (mem_tripleLevel.mp hrm)
      (show TripleLe (mkTriple (0, 0) s) (mkTriple (0, 0) r) by exact ⟨le_rfl, le_rfl, hsr⟩)
    have ht := congr_arg (fun x : Exp3 ↦ x.2.2) heq
    simpa [mkTriple] using ht.symm

lemma doubleAt_unique {A : Finset Exp3} (hA : TripleAntichain A)
    {r s : ℕ} (hr : DoubleAt A r) (hs : DoubleAt A s) : r = s := by
  change tripleLevel A r = twoPair at hr
  change tripleLevel A s = twoPair at hs
  have hrm : (1, 0) ∈ tripleLevel A r := by rw [hr]; simp [twoPair]
  have hsm : (1, 0) ∈ tripleLevel A s := by rw [hs]; simp [twoPair]
  rcases le_total r s with hrs | hsr
  · have heq := hA.eq (mem_tripleLevel.mp hrm) (mem_tripleLevel.mp hsm)
      (show TripleLe (mkTriple (1, 0) r) (mkTriple (1, 0) s) by exact ⟨le_rfl, le_rfl, hrs⟩)
    have ht := congr_arg (fun x : Exp3 ↦ x.2.2) heq
    simpa [mkTriple] using ht
  · have heq := hA.eq (mem_tripleLevel.mp hsm) (mem_tripleLevel.mp hrm)
      (show TripleLe (mkTriple (1, 0) s) (mkTriple (1, 0) r) by exact ⟨le_rfl, le_rfl, hsr⟩)
    have ht := congr_arg (fun x : Exp3 ↦ x.2.2) heq
    simpa [mkTriple] using ht.symm

lemma doubleAt_lt_singleAt {A : Finset Exp3} (hA : TripleAntichain A)
    {i r : ℕ} (hi : DoubleAt A i) (hr : SingleAt A r) : i < r := by
  change tripleLevel A i = twoPair at hi
  change tripleLevel A r = onePair at hr
  have him : (1, 0) ∈ tripleLevel A i := by rw [hi]; simp [twoPair]
  have hrm : (0, 0) ∈ tripleLevel A r := by rw [hr]; simp [onePair]
  by_contra hir
  have hri : r ≤ i := by omega
  have heq := hA.eq (mem_tripleLevel.mp hrm) (mem_tripleLevel.mp him)
    (show TripleLe (mkTriple (0, 0) r) (mkTriple (1, 0) i) by
      exact ⟨by simp [mkTriple], by simp [mkTriple], hri⟩)
  have hf := congr_arg (fun x : Exp3 ↦ x.1) heq
  norm_num [mkTriple] at hf

def singleCorrection (A B : Finset Exp3) : ℝ :=
  ∑ c ∈ tripleLevelSupport A, ∑ d ∈ tripleLevelSupport B,
    (1 / 5 : ℝ) ^ max c d *
      (if SingleAt A c ∧ SingleAt B d then (1 : ℝ) else 0)

def doubleCorrection (A B : Finset Exp3) : ℝ :=
  ∑ c ∈ tripleLevelSupport A, ∑ d ∈ tripleLevelSupport B,
    (1 / 5 : ℝ) ^ max c d *
      (if DoubleAt A c ∧ DoubleAt B d then (1 : ℝ) else 0)

lemma onePair_ne_twoPair : onePair ≠ twoPair := by
  intro h
  have hm : (0, 0) ∈ twoPair := by rw [← h]; simp [onePair]
  simpa [twoPair] using hm

lemma twoPair_ne_onePair : twoPair ≠ onePair := onePair_ne_twoPair.symm

lemma pairEnergy_exception_bound (X Y : Finset Exp2) (hX : PairAntichain X)
    (hY : PairAntichain Y) :
    pairEnergy X Y ≤ 31 / 36 +
      (11 / 36) * (if X = twoPair ∧ Y = twoPair then 1 else 0) +
      (5 / 36) * (if X = onePair ∧ Y = onePair then 1 else 0) := by
  by_cases h2 : X = twoPair ∧ Y = twoPair
  · rcases h2 with ⟨rfl, rfl⟩
    have hnot : ¬(twoPair = onePair ∧ twoPair = onePair) :=
      fun h ↦ twoPair_ne_onePair h.1
    have hraw : ({(0, 1), (1, 0)} : Finset Exp2) ≠ {(0, 0)} := by
      simpa [twoPair, onePair] using twoPair_ne_onePair
    norm_num [hnot, hraw, pairEnergy, pairKernel, twoPair, onePair]
  · by_cases h1 : X = onePair ∧ Y = onePair
    · rcases h1 with ⟨rfl, rfl⟩
      have hnot : ¬(onePair = twoPair ∧ onePair = twoPair) :=
        fun h ↦ onePair_ne_twoPair h.1
      have hraw : ({(0, 0)} : Finset Exp2) ≠ {(0, 1), (1, 0)} := by
        simpa [twoPair, onePair] using onePair_ne_twoPair
      norm_num [hnot, hraw, pairEnergy, pairKernel, twoPair, onePair]
    · simpa [h1, h2] using three_smooth_energy_le X Y hX hY h1 h2

lemma tripleEnergy_le_baseline (A B : Finset Exp3) (hA : TripleAntichain A)
    (hB : TripleAntichain B) :
    tripleEnergy A B ≤ 155 / 96 + (11 / 36) * doubleCorrection A B +
      (5 / 36) * singleCorrection A B := by
  rw [tripleEnergy_eq_levels]
  have hbase := max_geometric_finsets_le (tripleLevelSupport A) (tripleLevelSupport B)
  calc
    ∑ c ∈ tripleLevelSupport A, ∑ d ∈ tripleLevelSupport B,
        (1 / 5 : ℝ) ^ max c d * pairEnergy (tripleLevel A c) (tripleLevel B d) ≤
      ∑ c ∈ tripleLevelSupport A, ∑ d ∈ tripleLevelSupport B,
        (1 / 5 : ℝ) ^ max c d *
          (31 / 36 + (11 / 36) * (if DoubleAt A c ∧ DoubleAt B d then 1 else 0) +
            (5 / 36) * (if SingleAt A c ∧ SingleAt B d then 1 else 0)) := by
              apply Finset.sum_le_sum
              intro c hc
              apply Finset.sum_le_sum
              intro d hd
              apply mul_le_mul_of_nonneg_left _ (by positivity)
              have hb := pairEnergy_exception_bound _ _ (tripleLevel_antichain hA c)
                (tripleLevel_antichain hB d)
              by_cases hD : DoubleAt A c ∧ DoubleAt B d <;>
                by_cases hS : SingleAt A c ∧ SingleAt B d
              all_goals
                simp only [DoubleAt] at hD
                simp only [SingleAt] at hS
                simp only [DoubleAt, SingleAt] at ⊢
                simp [hD, hS, twoPair_ne_onePair, onePair_ne_twoPair] at hb ⊢
                exact hb
    _ = (31 / 36) * (∑ c ∈ tripleLevelSupport A, ∑ d ∈ tripleLevelSupport B,
          (1 / 5 : ℝ) ^ max c d) +
        (11 / 36) * doubleCorrection A B + (5 / 36) * singleCorrection A B := by
          simp only [singleCorrection, doubleCorrection]
          simp_rw [mul_add, Finset.sum_add_distrib]
          simp_rw [Finset.mul_sum]
          ring
    _ ≤ 155 / 96 + (11 / 36) * doubleCorrection A B +
        (5 / 36) * singleCorrection A B := by
          have : 0 ≤ (31 / 36 : ℝ) := by norm_num
          nlinarith

lemma singleCorrection_eq {A B : Finset Exp3} (hA : TripleAntichain A)
    (hB : TripleAntichain B) {r s : ℕ} (hr : SingleAt A r) (hs : SingleAt B s) :
    singleCorrection A B = (1 / 5 : ℝ) ^ max r s := by
  unfold singleCorrection
  have hra := singleAt_mem_support hr
  have hsb := singleAt_mem_support hs
  calc
    ∑ c ∈ tripleLevelSupport A, ∑ d ∈ tripleLevelSupport B,
        (1 / 5 : ℝ) ^ max c d *
          (if SingleAt A c ∧ SingleAt B d then (1 : ℝ) else 0) =
      ∑ d ∈ tripleLevelSupport B,
        (1 / 5 : ℝ) ^ max r d *
          (if SingleAt A r ∧ SingleAt B d then (1 : ℝ) else 0) := by
          apply Finset.sum_eq_single r
          · intro c hc hcr
            have hnot : ¬SingleAt A c := fun h ↦ hcr (singleAt_unique hA h hr)
            simp [hnot]
          · simp [hra]
    _ = (1 / 5 : ℝ) ^ max r s *
        (if SingleAt A r ∧ SingleAt B s then (1 : ℝ) else 0) := by
      apply Finset.sum_eq_single s
      · intro d hd hds
        have hnot : ¬SingleAt B d := fun h ↦ hds (singleAt_unique hB h hs)
        simp [hr, hnot]
      · simp [hsb]
    _ = (1 / 5 : ℝ) ^ max r s := by simp [hr, hs]

lemma doubleCorrection_eq {A B : Finset Exp3} (hA : TripleAntichain A)
    (hB : TripleAntichain B) {r s : ℕ} (hr : DoubleAt A r) (hs : DoubleAt B s) :
    doubleCorrection A B = (1 / 5 : ℝ) ^ max r s := by
  unfold doubleCorrection
  have hra := doubleAt_mem_support hr
  have hsb := doubleAt_mem_support hs
  calc
    ∑ c ∈ tripleLevelSupport A, ∑ d ∈ tripleLevelSupport B,
        (1 / 5 : ℝ) ^ max c d *
          (if DoubleAt A c ∧ DoubleAt B d then (1 : ℝ) else 0) =
      ∑ d ∈ tripleLevelSupport B,
        (1 / 5 : ℝ) ^ max r d *
          (if DoubleAt A r ∧ DoubleAt B d then (1 : ℝ) else 0) := by
          apply Finset.sum_eq_single r
          · intro c hc hcr
            have hnot : ¬DoubleAt A c := fun h ↦ hcr (doubleAt_unique hA h hr)
            simp [hnot]
          · simp [hra]
    _ = (1 / 5 : ℝ) ^ max r s *
        (if DoubleAt A r ∧ DoubleAt B s then (1 : ℝ) else 0) := by
      apply Finset.sum_eq_single s
      · intro d hd hds
        have hnot : ¬DoubleAt B d := fun h ↦ hds (doubleAt_unique hB h hs)
        simp [hr, hnot]
      · simp [hsb]
    _ = (1 / 5 : ℝ) ^ max r s := by simp [hr, hs]

lemma singleCorrection_eq_zero_of_not_exists_left (A B : Finset Exp3)
    (h : ¬∃ r, SingleAt A r) : singleCorrection A B = 0 := by
  unfold singleCorrection
  apply Finset.sum_eq_zero
  intro c hc
  have hc0 : ¬SingleAt A c := fun hc' ↦ h ⟨c, hc'⟩
  simp [hc0]

lemma doubleCorrection_eq_zero_of_not_exists_left (A B : Finset Exp3)
    (h : ¬∃ r, DoubleAt A r) : doubleCorrection A B = 0 := by
  unfold doubleCorrection
  apply Finset.sum_eq_zero
  intro c hc
  have hc0 : ¬DoubleAt A c := fun hc' ↦ h ⟨c, hc'⟩
  simp [hc0]

lemma singleCorrection_eq_zero_of_not_exists_right (A B : Finset Exp3)
    (h : ¬∃ r, SingleAt B r) : singleCorrection A B = 0 := by
  unfold singleCorrection
  apply Finset.sum_eq_zero
  intro c hc
  apply Finset.sum_eq_zero
  intro d hd
  have hd0 : ¬SingleAt B d := fun hd' ↦ h ⟨d, hd'⟩
  simp [hd0]

lemma doubleCorrection_eq_zero_of_not_exists_right (A B : Finset Exp3)
    (h : ¬∃ r, DoubleAt B r) : doubleCorrection A B = 0 := by
  unfold doubleCorrection
  apply Finset.sum_eq_zero
  intro c hc
  apply Finset.sum_eq_zero
  intro d hd
  have hd0 : ¬DoubleAt B d := fun hd' ↦ h ⟨d, hd'⟩
  simp [hd0]

lemma eq_singleton_of_singleAt_zero {A : Finset Exp3} (hA : TripleAntichain A)
    (h0 : SingleAt A 0) : A = {mkTriple (0, 0) 0} := by
  change tripleLevel A 0 = onePair at h0
  have hzlev : (0, 0) ∈ tripleLevel A 0 := by rw [h0]; simp [onePair]
  have hz : mkTriple (0, 0) 0 ∈ A := mem_tripleLevel.mp hzlev
  apply Finset.eq_singleton_iff_unique_mem.mpr
  refine ⟨hz, ?_⟩
  intro x hx
  have heq := hA.eq hz hx (show TripleLe (mkTriple (0, 0) 0) x by
    rcases x with ⟨a, b, c⟩
    exact ⟨by simp [mkTriple], by simp [mkTriple], by simp [mkTriple]⟩)
  exact heq.symm

lemma singleAt_of_doubleAt_zero_of_mem_support {A : Finset Exp3} (hA : TripleAntichain A)
    (h0 : DoubleAt A 0) {c : ℕ} (hcS : c ∈ tripleLevelSupport A) (hc0 : c ≠ 0) :
    SingleAt A c := by
  change tripleLevel A 0 = twoPair at h0
  have h10 : (1, 0) ∈ tripleLevel A 0 := by rw [h0]; simp [twoPair]
  have h01 : (0, 1) ∈ tripleLevel A 0 := by rw [h0]; simp [twoPair]
  have hcpos : 0 < c := by omega
  unfold SingleAt
  apply Finset.ext
  intro x
  simp only [onePair, Finset.mem_singleton]
  constructor
  · intro hx
    rcases x with ⟨a, b⟩
    by_cases ha : 0 < a
    · have hle : TripleLe (mkTriple (1, 0) 0) (mkTriple (a, b) c) := by
        change 1 ≤ a ∧ 0 ≤ b ∧ 0 ≤ c
        omega
      have heq := hA.eq (mem_tripleLevel.mp h10) (mem_tripleLevel.mp hx) hle
      have ht := congr_arg (fun z : Exp3 ↦ z.2.2) heq
      simp [mkTriple] at ht
      omega
    · by_cases hb : 0 < b
      · have hle : TripleLe (mkTriple (0, 1) 0) (mkTriple (a, b) c) := by
          change 0 ≤ a ∧ 1 ≤ b ∧ 0 ≤ c
          omega
        have heq := hA.eq (mem_tripleLevel.mp h01) (mem_tripleLevel.mp hx) hle
        have ht := congr_arg (fun z : Exp3 ↦ z.2.2) heq
        simp [mkTriple] at ht
        omega
      · exact Prod.ext (by omega) (by omega)
  · rintro rfl
    rcases Finset.mem_image.mp hcS with ⟨y, hyA, hyc⟩
    have hyL : triplePair y ∈ tripleLevel A c := by
      apply Finset.mem_image.mpr
      exact ⟨y, Finset.mem_filter.mpr ⟨hyA, hyc⟩, rfl⟩
    have hy0 : triplePair y = (0, 0) := by
      rcases hpair : triplePair y with ⟨a, b⟩
      by_cases ha : 0 < a
      · have hle : TripleLe (mkTriple (1, 0) 0) (mkTriple (triplePair y) c) := by
          rw [hpair]
          change 1 ≤ a ∧ 0 ≤ b ∧ 0 ≤ c
          omega
        have heq := hA.eq (mem_tripleLevel.mp h10) (mem_tripleLevel.mp hyL) hle
        have ht := congr_arg (fun z : Exp3 ↦ z.2.2) heq
        simp [mkTriple] at ht
        omega
      · by_cases hb : 0 < b
        · have hle : TripleLe (mkTriple (0, 1) 0) (mkTriple (triplePair y) c) := by
            rw [hpair]
            change 0 ≤ a ∧ 1 ≤ b ∧ 0 ≤ c
            omega
          have heq := hA.eq (mem_tripleLevel.mp h01) (mem_tripleLevel.mp hyL) hle
          have ht := congr_arg (fun z : Exp3 ↦ z.2.2) heq
          simp [mkTriple] at ht
          omega
        · exact Prod.ext (by omega) (by omega)
    rw [← hy0]
    exact hyL

lemma erase_zero_card_le_one_of_doubleAt_zero {A : Finset Exp3} (hA : TripleAntichain A)
    (h0 : DoubleAt A 0) : ((tripleLevelSupport A).erase 0).card ≤ 1 := by
  apply Finset.card_le_one.mpr
  intro c hc d hd
  have hcS := (Finset.mem_erase.mp hc).2
  have hdS := (Finset.mem_erase.mp hd).2
  exact singleAt_unique hA
    (singleAt_of_doubleAt_zero_of_mem_support hA h0 hcS (Finset.mem_erase.mp hc).1)
    (singleAt_of_doubleAt_zero_of_mem_support hA h0 hdS (Finset.mem_erase.mp hd).1)

lemma double_zero_numeric_bound (S T : Finset ℕ) (h0S : 0 ∈ S) (h0T : 0 ∈ T)
    (hSc : (S.erase 0).card ≤ 1) (hTc : (T.erase 0).card ≤ 1) :
    ∑ c ∈ S, ∑ d ∈ T, (1 / 5 : ℝ) ^ max c d *
      (if c = 0 ∧ d = 0 then 7 / 6 else if c = 0 ∨ d = 0 then 5 / 6 else 1) ≤
      17 / 10 := by
  let S' := S.erase 0
  let T' := T.erase 0
  have hS : S = insert 0 S' := (Finset.insert_erase h0S).symm
  have hT : T = insert 0 T' := (Finset.insert_erase h0T).symm
  have h0S' : 0 ∉ S' := by simp [S']
  have h0T' : 0 ∉ T' := by simp [T']
  have hST : ∑ d ∈ T', (1 / 5 : ℝ) ^ d * (5 / 6) ≤ 1 / 6 := by
    calc
      ∑ d ∈ T', (1 / 5 : ℝ) ^ d * (5 / 6) ≤ ∑ _d ∈ T', (1 / 6 : ℝ) := by
        apply Finset.sum_le_sum
        intro d hd
        have hdpos : 1 ≤ d := by
          have hd0 : d ≠ 0 := fun h ↦ h0T' (h ▸ hd)
          omega
        have hp := pow_le_pow_of_le_one (a := (1 / 5 : ℝ)) (by norm_num) (by norm_num) hdpos
        norm_num at hp ⊢
        nlinarith
      _ ≤ 1 / 6 := by
        simp only [Finset.sum_const, nsmul_eq_mul]
        have : ((T'.card : ℕ) : ℝ) ≤ 1 := by exact_mod_cast hTc
        norm_num at this ⊢
        nlinarith
  have hTS : ∑ c ∈ S', (1 / 5 : ℝ) ^ c * (5 / 6) ≤ 1 / 6 := by
    calc
      ∑ c ∈ S', (1 / 5 : ℝ) ^ c * (5 / 6) ≤ ∑ _c ∈ S', (1 / 6 : ℝ) := by
        apply Finset.sum_le_sum
        intro c hc
        have hcpos : 1 ≤ c := by
          have hc0 : c ≠ 0 := fun h ↦ h0S' (h ▸ hc)
          omega
        have hp := pow_le_pow_of_le_one (a := (1 / 5 : ℝ)) (by norm_num) (by norm_num) hcpos
        norm_num at hp ⊢
        nlinarith
      _ ≤ 1 / 6 := by
        simp only [Finset.sum_const, nsmul_eq_mul]
        have : ((S'.card : ℕ) : ℝ) ≤ 1 := by exact_mod_cast hSc
        norm_num at this ⊢
        nlinarith
  have hSS : ∑ c ∈ S', ∑ d ∈ T', (1 / 5 : ℝ) ^ max c d ≤ 1 / 5 := by
    calc
      ∑ c ∈ S', ∑ d ∈ T', (1 / 5 : ℝ) ^ max c d ≤
          ∑ _c ∈ S', ∑ _d ∈ T', (1 / 5 : ℝ) := by
            apply Finset.sum_le_sum
            intro c hc
            apply Finset.sum_le_sum
            intro d hd
            have hcpos : 1 ≤ c := by
              have hc0 : c ≠ 0 := fun h ↦ h0S' (h ▸ hc)
              omega
            have hp := pow_le_pow_of_le_one (a := (1 / 5 : ℝ)) (by norm_num) (by norm_num)
              (show 1 ≤ max c d from le_max_of_le_left hcpos)
            simpa using hp
      _ ≤ 1 / 5 := by
        simp only [Finset.sum_const, nsmul_eq_mul]
        have hprod : ((S'.card * T'.card : ℕ) : ℝ) ≤ 1 := by
          exact_mod_cast Nat.mul_le_mul hSc hTc
        norm_num at hprod ⊢
        nlinarith
  have hdecomp :
      (∑ c ∈ S, ∑ d ∈ T, (1 / 5 : ℝ) ^ max c d *
        (if c = 0 ∧ d = 0 then 7 / 6 else if c = 0 ∨ d = 0 then 5 / 6 else 1)) =
      7 / 6 + (∑ d ∈ T', (1 / 5 : ℝ) ^ d * (5 / 6)) +
        (∑ c ∈ S', (1 / 5 : ℝ) ^ c * (5 / 6)) +
        (∑ c ∈ S', ∑ d ∈ T', (1 / 5 : ℝ) ^ max c d) := by
    rw [hS, hT]
    simp only [Finset.sum_insert h0S', Finset.sum_insert h0T']
    have hTrow : (∑ d ∈ T', (1 / 5 : ℝ) ^ max 0 d *
        (if True ∧ d = 0 then 7 / 6 else if True ∨ d = 0 then 5 / 6 else 1)) =
        ∑ d ∈ T', (1 / 5 : ℝ) ^ d * (5 / 6) := by
      apply Finset.sum_congr rfl
      intro d hd
      have hd0 : d ≠ 0 := by
        intro h
        subst d
        exact h0T' hd
      simp [hd0]
    have hSrows :
        (∑ c ∈ S',
          ((1 / 5 : ℝ) ^ max c 0 *
              (if c = 0 ∧ True then 7 / 6 else if c = 0 ∨ True then 5 / 6 else 1) +
            ∑ d ∈ T', (1 / 5 : ℝ) ^ max c d *
              (if c = 0 ∧ d = 0 then 7 / 6 else if c = 0 ∨ d = 0 then 5 / 6 else 1))) =
          (∑ c ∈ S', (1 / 5 : ℝ) ^ c * (5 / 6)) +
            ∑ c ∈ S', ∑ d ∈ T', (1 / 5 : ℝ) ^ max c d := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro c hc
      have hc0 : c ≠ 0 := by
        intro h
        subst c
        exact h0S' hc
      have hinner :
          (∑ d ∈ T', (1 / 5 : ℝ) ^ max c d *
            (if c = 0 ∧ d = 0 then 7 / 6 else if c = 0 ∨ d = 0 then 5 / 6 else 1)) =
            ∑ d ∈ T', (1 / 5 : ℝ) ^ max c d := by
        apply Finset.sum_congr rfl
        intro d hd
        have hd0 : d ≠ 0 := by
          intro h
          subst d
          exact h0T' hd
        simp [hc0, hd0]
      rw [hinner]
      simp [hc0]
    rw [hTrow, hSrows]
    norm_num
    ring
  rw [hdecomp]
  nlinarith

lemma tripleEnergy_le_of_doubleAt_zero (A B : Finset Exp3) (hA : TripleAntichain A)
    (hB : TripleAntichain B) (hA0 : DoubleAt A 0) (hB0 : DoubleAt B 0) :
    tripleEnergy A B ≤ 17 / 10 := by
  rw [tripleEnergy_eq_levels]
  have h0A := doubleAt_mem_support hA0
  have h0B := doubleAt_mem_support hB0
  apply le_trans ?_ (double_zero_numeric_bound _ _ h0A h0B
    (erase_zero_card_le_one_of_doubleAt_zero hA hA0)
    (erase_zero_card_le_one_of_doubleAt_zero hB hB0))
  apply Finset.sum_le_sum
  intro c hc
  apply Finset.sum_le_sum
  intro d hd
  by_cases hc0 : c = 0
  · subst c
    rw [show tripleLevel A 0 = twoPair from hA0]
    by_cases hd0 : d = 0
    · subst d
      rw [show tripleLevel B 0 = twoPair from hB0]
      norm_num [pairEnergy, pairKernel, twoPair]
    · rw [show tripleLevel B d = onePair from
        singleAt_of_doubleAt_zero_of_mem_support hB hB0 hd hd0]
      norm_num [hd0, pairEnergy, pairKernel, twoPair, onePair]
  · rw [show tripleLevel A c = onePair from
      singleAt_of_doubleAt_zero_of_mem_support hA hA0 hc hc0]
    by_cases hd0 : d = 0
    · subst d
      rw [show tripleLevel B 0 = twoPair from hB0]
      norm_num [hc0, pairEnergy, pairKernel, twoPair, onePair]
    · rw [show tripleLevel B d = onePair from
        singleAt_of_doubleAt_zero_of_mem_support hB hB0 hd hd0]
      simp [hc0, hd0, pairEnergy, pairKernel, onePair]

lemma one_fifth_pow_le_of_pos {n : ℕ} (hn : 0 < n) :
    (1 / 5 : ℝ) ^ n ≤ 1 / 5 := by
  have h := pow_le_pow_of_le_one (a := (1 / 5 : ℝ)) (by norm_num) (by norm_num)
    (show 1 ≤ n by omega)
  simpa using h

/-- BBMST Lemma 9.4 in exponent coordinates. -/
theorem five_smooth_energy_le (A B : Finset Exp3) (hA : TripleAntichain A)
    (hB : TripleAntichain B) : tripleEnergy A B ≤ 17 / 10 := by
  have hbase := tripleEnergy_le_baseline A B hA hB
  by_cases hdA : ∃ i, DoubleAt A i
  · obtain ⟨i, hi⟩ := hdA
    by_cases hdB : ∃ j, DoubleAt B j
    · obtain ⟨j, hj⟩ := hdB
      rw [doubleCorrection_eq hA hB hi hj] at hbase
      by_cases hm0 : max i j = 0
      · have hi0 : i = 0 := by omega
        have hj0 : j = 0 := by omega
        subst i
        subst j
        exact tripleEnergy_le_of_doubleAt_zero A B hA hB hi hj
      · have hmpos : 0 < max i j := by omega
        have hmpow := one_fifth_pow_le_of_pos hmpos
        by_cases hsA : ∃ r, SingleAt A r
        · obtain ⟨r, hr⟩ := hsA
          by_cases hsB : ∃ s, SingleAt B s
          · obtain ⟨s, hs⟩ := hsB
            rw [singleCorrection_eq hA hB hr hs] at hbase
            have hir := doubleAt_lt_singleAt hA hi hr
            have hjs := doubleAt_lt_singleAt hB hj hs
            have hgap : max i j + 1 ≤ max r s := by omega
            have hspow := pow_le_pow_of_le_one (a := (1 / 5 : ℝ))
              (by norm_num) (by norm_num) hgap
            rw [pow_succ] at hspow
            norm_num at hspow
            nlinarith
          · rw [singleCorrection_eq_zero_of_not_exists_right A B hsB] at hbase
            nlinarith
        · rw [singleCorrection_eq_zero_of_not_exists_left A B hsA] at hbase
          nlinarith
    · rw [doubleCorrection_eq_zero_of_not_exists_right A B hdB] at hbase
      by_cases hsA : ∃ r, SingleAt A r
      · obtain ⟨r, hr⟩ := hsA
        by_cases hsB : ∃ s, SingleAt B s
        · obtain ⟨s, hs⟩ := hsB
          rw [singleCorrection_eq hA hB hr hs] at hbase
          by_cases hm0 : max r s = 0
          · have hr0 : r = 0 := by omega
            have hs0 : s = 0 := by omega
            subst r
            subst s
            rw [eq_singleton_of_singleAt_zero hA hr,
              eq_singleton_of_singleAt_zero hB hs]
            norm_num [tripleEnergy, tripleKernel, mkTriple]
          · have hp := one_fifth_pow_le_of_pos (show 0 < max r s by omega)
            nlinarith
        · rw [singleCorrection_eq_zero_of_not_exists_right A B hsB] at hbase
          norm_num at hbase ⊢
          linarith
      · rw [singleCorrection_eq_zero_of_not_exists_left A B hsA] at hbase
        norm_num at hbase ⊢
        linarith
  · rw [doubleCorrection_eq_zero_of_not_exists_left A B hdA] at hbase
    by_cases hsA : ∃ r, SingleAt A r
    · obtain ⟨r, hr⟩ := hsA
      by_cases hsB : ∃ s, SingleAt B s
      · obtain ⟨s, hs⟩ := hsB
        rw [singleCorrection_eq hA hB hr hs] at hbase
        by_cases hm0 : max r s = 0
        · have hr0 : r = 0 := by omega
          have hs0 : s = 0 := by omega
          subst r
          subst s
          rw [eq_singleton_of_singleAt_zero hA hr,
            eq_singleton_of_singleAt_zero hB hs]
          norm_num [tripleEnergy, tripleKernel, mkTriple]
        · have hp := one_fifth_pow_le_of_pos (show 0 < max r s by omega)
          nlinarith
      · rw [singleCorrection_eq_zero_of_not_exists_right A B hsB] at hbase
        norm_num at hbase ⊢
        linarith
    · rw [singleCorrection_eq_zero_of_not_exists_left A B hsA] at hbase
      norm_num at hbase ⊢
      linarith

/-! ## Bridges to natural-number divisibility and LCM weights -/

def pairMax (x y : Exp2) : Exp2 := (max x.1 y.1, max x.2 y.2)
def tripleMax (x y : Exp3) : Exp3 :=
  (max x.1 y.1, max x.2.1 y.2.1, max x.2.2 y.2.2)

lemma pairLe_decode3_dvd {x y : Exp2} (h : PairLe x y) : decode3 x ∣ decode3 y := by
  exact Nat.mul_dvd_mul (pow_dvd_pow 2 h.1) (pow_dvd_pow 3 h.2)

lemma tripleLe_decode5_dvd {x y : Exp3} (h : TripleLe x y) : decode5 x ∣ decode5 y := by
  exact Nat.mul_dvd_mul
    (Nat.mul_dvd_mul (pow_dvd_pow 2 h.1) (pow_dvd_pow 3 h.2.1))
    (pow_dvd_pow 5 h.2.2)

lemma pairAntichain_of_decode3 {A : Finset Exp2}
    (h : ∀ x ∈ A, ∀ y ∈ A, x ≠ y → ¬decode3 x ∣ decode3 y) : PairAntichain A := by
  intro x hx y hy hxy hle
  exact h x hx y hy hxy (pairLe_decode3_dvd hle)

lemma tripleAntichain_of_decode5 {A : Finset Exp3}
    (h : ∀ x ∈ A, ∀ y ∈ A, x ≠ y → ¬decode5 x ∣ decode5 y) : TripleAntichain A := by
  intro x hx y hy hxy hle
  exact h x hx y hy hxy (tripleLe_decode5_dvd hle)

lemma pairWeight_eq_inv_decode3 (x : Exp2) :
    pairWeight x = ((decode3 x : ℕ) : ℝ)⁻¹ := by
  rcases x with ⟨a, b⟩
  norm_num [pairWeight, decode3, Nat.cast_mul, Nat.cast_pow, one_div, mul_inv_rev]
  rw [one_div, one_div]
  rw [← inv_pow, ← inv_pow]
  ring

lemma tripleWeight_eq_inv_decode5 (x : Exp3) :
    tripleWeight x = ((decode5 x : ℕ) : ℝ)⁻¹ := by
  rcases x with ⟨a, b, c⟩
  norm_num [tripleWeight, decode5, Nat.cast_mul, Nat.cast_pow, one_div, mul_inv_rev]
  rw [one_div, one_div, one_div]
  rw [← inv_pow, ← inv_pow, ← inv_pow]
  ring

lemma pairKernel_eq_inv_decode3_max (x y : Exp2) :
    pairKernel x y = ((decode3 (pairMax x y) : ℕ) : ℝ)⁻¹ := by
  rcases x with ⟨a, b⟩
  rcases y with ⟨c, d⟩
  norm_num [pairKernel, pairMax, decode3, Nat.cast_mul, Nat.cast_pow, one_div, mul_inv_rev]
  rw [one_div, one_div]
  rw [← inv_pow, ← inv_pow]
  ring

lemma tripleKernel_eq_inv_decode5_max (x y : Exp3) :
    tripleKernel x y = ((decode5 (tripleMax x y) : ℕ) : ℝ)⁻¹ := by
  rcases x with ⟨a, b, c⟩
  rcases y with ⟨d, e, f⟩
  norm_num [tripleKernel, tripleMax, decode5, Nat.cast_mul, Nat.cast_pow, one_div, mul_inv_rev]
  rw [one_div, one_div, one_div]
  rw [← inv_pow, ← inv_pow, ← inv_pow]
  ring

end

end Erdos586
