/-
Copyright 2026 The Lean-Proofs Authors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    http://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/
import Wikipedia.VinogradovsTheorem.CircleMethod

/-!
# Prime-power removal for Erdős Problem 471

The circle method is most naturally applied to von Mangoldt weights.  This
file proves, without analytic number theory, that triples containing a proper
prime power have total weight `o(n²)`.  The sparse-counting argument follows
the standard observation that a proper prime power `p^k ≤ n` has
`p ≤ sqrt n` and `k ≤ log₂ n`.
-/

noncomputable section

namespace VinogradovsTheorem.PrimePowerTail

open Finset Filter Asymptotics

/-- A prime power which is not itself prime. -/
def ProperPrimePower (n : ℕ) : Prop :=
  IsPrimePow n ∧ ¬ n.Prime

instance (n : ℕ) : Decidable (ProperPrimePower n) := by
  unfold ProperPrimePower
  infer_instance

/-- A triple with at least one proper-prime-power coordinate. -/
def HasProperPrimePowerComponent (x : ℕ × ℕ × ℕ) : Prop :=
  ProperPrimePower x.1 ∨ ProperPrimePower x.2.1 ∨ ProperPrimePower x.2.2

instance (x : ℕ × ℕ × ℕ) : Decidable (HasProperPrimePowerComponent x) := by
  unfold HasProperPrimePowerComponent
  infer_instance

theorem not_hasProperPrimePowerComponent_iff {x : ℕ × ℕ × ℕ} :
    ¬ HasProperPrimePowerComponent x ↔
      ¬ ProperPrimePower x.1 ∧ ¬ ProperPrimePower x.2.1 ∧
        ¬ ProperPrimePower x.2.2 := by
  unfold HasProperPrimePowerComponent
  tauto

/-- All ordered triples of naturals summing to `n`. -/
def weightedTriples (n : ℕ) : Finset (ℕ × ℕ × ℕ) :=
  ((Finset.range (n + 1)) ×ˢ (Finset.range (n + 1)) ×ˢ
      (Finset.range (n + 1))).filter
    (fun x ↦ x.1 + x.2.1 + x.2.2 = n)

/-- The von Mangoldt-weighted ternary coefficient. -/
def vonMangoldtTripleWeight (n : ℕ) : ℝ :=
  ∑ x ∈ weightedTriples n,
    ArithmeticFunction.vonMangoldt x.1 *
      ArithmeticFunction.vonMangoldt x.2.1 *
        ArithmeticFunction.vonMangoldt x.2.2

/-- Proper prime powers not exceeding `n`. -/
def properPrimePowersUpTo (n : ℕ) : Finset ℕ :=
  (Finset.range (n + 1)).filter ProperPrimePower

/-- Bounded base/exponent witnesses for proper prime powers up to `n`. -/
def properPrimePowerSqrtLogWitnessPairsUpTo (n : ℕ) : Finset (ℕ × ℕ) :=
  (Finset.range (Nat.sqrt n + 1) ×ˢ Finset.range (Nat.log 2 n + 1)).filter
    (fun pk ↦ pk.1.Prime ∧ 2 ≤ pk.2 ∧ pk.1 ^ pk.2 ≤ n)

def properTailFstSparseBox (n : ℕ) : Finset (ℕ × ℕ × ℕ) :=
  (properPrimePowersUpTo n ×ˢ Finset.range (n + 1)).image
    (fun mb ↦ (mb.1, mb.2, n - mb.1 - mb.2))

def properTailSndFstSparseBox (n : ℕ) : Finset (ℕ × ℕ × ℕ) :=
  (Finset.range (n + 1) ×ˢ properPrimePowersUpTo n).image
    (fun am ↦ (am.1, am.2, n - am.1 - am.2))

def properTailSndSndSparseBox (n : ℕ) : Finset (ℕ × ℕ × ℕ) :=
  (Finset.range (n + 1) ×ˢ properPrimePowersUpTo n).image
    (fun am ↦ (am.1, n - am.1 - am.2, am.2))

/-- Contaminated triples. -/
def primePowerTailTriples (n : ℕ) : Finset (ℕ × ℕ × ℕ) :=
  (weightedTriples n).filter HasProperPrimePowerComponent

/-- Their total von Mangoldt weight. -/
def primePowerTail (n : ℕ) : ℝ :=
  ∑ x ∈ primePowerTailTriples n,
    ArithmeticFunction.vonMangoldt x.1 *
      ArithmeticFunction.vonMangoldt x.2.1 *
        ArithmeticFunction.vonMangoldt x.2.2

/-- The complementary, prime-only part of the ternary coefficient. -/
def primeOnlyWeightedTriples (n : ℕ) : Finset (ℕ × ℕ × ℕ) :=
  (weightedTriples n).filter (fun x ↦ ¬ HasProperPrimePowerComponent x)

def primeOnlyWeightedContribution (n : ℕ) : ℝ :=
  ∑ x ∈ primeOnlyWeightedTriples n,
    ArithmeticFunction.vonMangoldt x.1 *
      ArithmeticFunction.vonMangoldt x.2.1 *
        ArithmeticFunction.vonMangoldt x.2.2

/-- Explicit upper bound for the proper-prime-power tail. -/
def sqrtLogPrimePowerTailBound (n : ℕ) : ℝ :=
  (3 * ((Nat.sqrt n + 1) * (Nat.log 2 n + 1)) * (n + 1) : ℕ) *
    Real.log (n : ℝ) ^ 3

theorem weightedTriples_mem {n : ℕ} {x : ℕ × ℕ × ℕ} :
    x ∈ weightedTriples n ↔
      x.1 ≤ n ∧ x.2.1 ≤ n ∧ x.2.2 ≤ n ∧
        x.1 + x.2.1 + x.2.2 = n := by
  simp [weightedTriples]
  constructor
  · intro h
    exact ⟨h.1.1, h.1.2.1, h.1.2.2, h.2⟩
  · intro h
    exact ⟨⟨h.1, h.2.1, h.2.2.1⟩, h.2.2.2⟩

theorem vonMangoldtTripleWeight_eq_raw (n : ℕ) :
    vonMangoldtTripleWeight n =
      CircleMethod.rawVonMangoldtTripleWeight n n := by
  unfold vonMangoldtTripleWeight weightedTriples
    CircleMethod.rawVonMangoldtTripleWeight
  simp_rw [Finset.sum_filter]
  simp_rw [Finset.sum_product]

/-- Fourier inversion for the von Mangoldt-weighted coefficient. -/
theorem vonMangoldtTripleWeight_eq_circleIntegral (n : ℕ) :
    (vonMangoldtTripleWeight n : ℂ) =
      ∫ α in Set.Icc (0 : ℝ) 1,
        CircleMethod.vonMangoldtExpSum α n ^ 3 *
          Complex.exp (-2 * Real.pi * Complex.I * (α : ℂ) * (n : ℂ)) := by
  rw [CircleMethod.integral_vonMangoldtExpSum_cube_kernel,
    vonMangoldtTripleWeight_eq_raw]

theorem mem_properPrimePowersUpTo {n m : ℕ} :
    m ∈ properPrimePowersUpTo n ↔ m ≤ n ∧ ProperPrimePower m := by
  simp [properPrimePowersUpTo]

theorem mem_properPrimePowerSqrtLogWitnessPairsUpTo {n : ℕ} {pk : ℕ × ℕ} :
    pk ∈ properPrimePowerSqrtLogWitnessPairsUpTo n ↔
      pk.1 ≤ Nat.sqrt n ∧ pk.2 ≤ Nat.log 2 n ∧ pk.1.Prime ∧
        2 ≤ pk.2 ∧ pk.1 ^ pk.2 ≤ n := by
  simp [properPrimePowerSqrtLogWitnessPairsUpTo]
  constructor
  · intro h
    exact ⟨h.1.1, h.1.2, h.2.1, h.2.2.1, h.2.2.2⟩
  · intro h
    exact ⟨⟨h.1, h.2.1⟩, h.2.2.1, h.2.2.2.1, h.2.2.2.2⟩

theorem properPrimePower_exists_bounded_log_witness {n m : ℕ}
    (hm : m ∈ properPrimePowersUpTo n) :
    ∃ p k : ℕ, p ≤ n ∧ k ≤ Nat.log 2 n ∧ p.Prime ∧ 2 ≤ k ∧ p ^ k = m := by
  have hm' := mem_properPrimePowersUpTo.mp hm
  rcases (isPrimePow_nat_iff_bounded_log m).mp hm'.2.1 with
    ⟨k, hklog_m, hkpos, p, hpm, hpow, hp⟩
  have hlog_mn : Nat.log 2 m ≤ Nat.log 2 n :=
    Nat.log_mono Nat.one_lt_two Nat.AtLeastTwo.prop hm'.1
  have hk_ne_one : k ≠ 1 := by
    intro hk
    apply hm'.2.2
    simpa [hpow, hk] using hp
  have hk_two : 2 ≤ k := by omega
  exact ⟨p, k, le_trans hpm hm'.1, le_trans hklog_m hlog_mn,
    hp, hk_two, hpow.symm⟩

theorem properPrimePower_exists_bounded_sqrt_log_witness {n m : ℕ}
    (hm : m ∈ properPrimePowersUpTo n) :
    ∃ p k : ℕ, p ≤ Nat.sqrt n ∧ k ≤ Nat.log 2 n ∧ p.Prime ∧
      2 ≤ k ∧ p ^ k = m := by
  rcases properPrimePower_exists_bounded_log_witness hm with
    ⟨p, k, _hpn, hklog, hp, hk, hpow⟩
  have hp2_le_pow : p ^ 2 ≤ p ^ k := Nat.pow_le_pow_right hp.one_lt.le hk
  have hp2_le_n : p ^ 2 ≤ n := by
    rw [hpow] at hp2_le_pow
    exact le_trans hp2_le_pow (mem_properPrimePowersUpTo.mp hm).1
  exact ⟨p, k, Nat.le_sqrt'.mpr hp2_le_n, hklog, hp, hk, hpow⟩

theorem properPrimePowersUpTo_subset_witness_image (n : ℕ) :
    properPrimePowersUpTo n ⊆
      (properPrimePowerSqrtLogWitnessPairsUpTo n).image
        (fun pk : ℕ × ℕ ↦ pk.1 ^ pk.2) := by
  intro m hm
  rcases properPrimePower_exists_bounded_sqrt_log_witness hm with
    ⟨p, k, hpsqrt, hklog, hp, hk, hpow⟩
  refine Finset.mem_image.mpr ⟨(p, k), ?_, hpow⟩
  exact mem_properPrimePowerSqrtLogWitnessPairsUpTo.mpr
    ⟨hpsqrt, hklog, hp, hk, by rw [hpow]; exact (mem_properPrimePowersUpTo.mp hm).1⟩

theorem properPrimePowersUpTo_card_le_sqrt_log (n : ℕ) :
    (properPrimePowersUpTo n).card ≤
      (Nat.sqrt n + 1) * (Nat.log 2 n + 1) := by
  calc
    (properPrimePowersUpTo n).card ≤
        ((properPrimePowerSqrtLogWitnessPairsUpTo n).image
          (fun pk : ℕ × ℕ ↦ pk.1 ^ pk.2)).card :=
      Finset.card_le_card (properPrimePowersUpTo_subset_witness_image n)
    _ ≤ (properPrimePowerSqrtLogWitnessPairsUpTo n).card := Finset.card_image_le
    _ ≤ (Finset.range (Nat.sqrt n + 1) ×ˢ
          Finset.range (Nat.log 2 n + 1)).card := by
      apply Finset.card_le_card
      intro pk hpk
      exact (Finset.mem_filter.mp hpk).1
    _ = (Nat.sqrt n + 1) * (Nat.log 2 n + 1) := by simp

theorem properTailFstSparseBox_card (n : ℕ) :
    (properTailFstSparseBox n).card =
      (properPrimePowersUpTo n).card * (n + 1) := by
  unfold properTailFstSparseBox
  rw [Finset.card_image_of_injective]
  · simp
  · intro a b h
    ext
    · exact congrArg (fun x : ℕ × ℕ × ℕ ↦ x.1) h
    · exact congrArg (fun x : ℕ × ℕ × ℕ ↦ x.2.1) h

theorem properTailSndFstSparseBox_card (n : ℕ) :
    (properTailSndFstSparseBox n).card =
      (n + 1) * (properPrimePowersUpTo n).card := by
  unfold properTailSndFstSparseBox
  rw [Finset.card_image_of_injective]
  · simp
  · intro a b h
    ext
    · exact congrArg (fun x : ℕ × ℕ × ℕ ↦ x.1) h
    · exact congrArg (fun x : ℕ × ℕ × ℕ ↦ x.2.1) h

theorem properTailSndSndSparseBox_card (n : ℕ) :
    (properTailSndSndSparseBox n).card =
      (n + 1) * (properPrimePowersUpTo n).card := by
  unfold properTailSndSndSparseBox
  rw [Finset.card_image_of_injective]
  · simp
  · intro a b h
    ext
    · exact congrArg (fun x : ℕ × ℕ × ℕ ↦ x.1) h
    · exact congrArg (fun x : ℕ × ℕ × ℕ ↦ x.2.2) h

theorem mem_primePowerTailTriples {n : ℕ} {x : ℕ × ℕ × ℕ} :
    x ∈ primePowerTailTriples n ↔
      x ∈ weightedTriples n ∧ HasProperPrimePowerComponent x := by
  simp [primePowerTailTriples]

theorem primePowerTailTriples_component {n : ℕ} {x : ℕ × ℕ × ℕ}
    (hx : x ∈ primePowerTailTriples n) :
    x.1 ∈ properPrimePowersUpTo n ∨
      x.2.1 ∈ properPrimePowersUpTo n ∨ x.2.2 ∈ properPrimePowersUpTo n := by
  have hx' := mem_primePowerTailTriples.mp hx
  have hw := weightedTriples_mem.mp hx'.1
  rcases hx'.2 with h | h | h
  · exact Or.inl (mem_properPrimePowersUpTo.mpr ⟨hw.1, h⟩)
  · exact Or.inr (Or.inl (mem_properPrimePowersUpTo.mpr ⟨hw.2.1, h⟩))
  · exact Or.inr (Or.inr (mem_properPrimePowersUpTo.mpr ⟨hw.2.2.1, h⟩))

theorem mem_properTailFstSparseBox_of_weighted {n : ℕ} {x : ℕ × ℕ × ℕ}
    (hx : x ∈ weightedTriples n) (hfst : x.1 ∈ properPrimePowersUpTo n) :
    x ∈ properTailFstSparseBox n := by
  refine Finset.mem_image.mpr ⟨(x.1, x.2.1), ?_, ?_⟩
  · exact Finset.mem_product.mpr
      ⟨hfst, Finset.mem_range.mpr (Nat.lt_succ_iff.mpr (weightedTriples_mem.mp hx).2.1)⟩
  · ext <;> simp
    have hsum := (weightedTriples_mem.mp hx).2.2.2
    omega

theorem mem_properTailSndFstSparseBox_of_weighted {n : ℕ} {x : ℕ × ℕ × ℕ}
    (hx : x ∈ weightedTriples n) (hsnd : x.2.1 ∈ properPrimePowersUpTo n) :
    x ∈ properTailSndFstSparseBox n := by
  refine Finset.mem_image.mpr ⟨(x.1, x.2.1), ?_, ?_⟩
  · exact Finset.mem_product.mpr
      ⟨Finset.mem_range.mpr (Nat.lt_succ_iff.mpr (weightedTriples_mem.mp hx).1), hsnd⟩
  · ext <;> simp
    have hsum := (weightedTriples_mem.mp hx).2.2.2
    omega

theorem mem_properTailSndSndSparseBox_of_weighted {n : ℕ} {x : ℕ × ℕ × ℕ}
    (hx : x ∈ weightedTriples n) (hthird : x.2.2 ∈ properPrimePowersUpTo n) :
    x ∈ properTailSndSndSparseBox n := by
  refine Finset.mem_image.mpr ⟨(x.1, x.2.2), ?_, ?_⟩
  · exact Finset.mem_product.mpr
      ⟨Finset.mem_range.mpr (Nat.lt_succ_iff.mpr (weightedTriples_mem.mp hx).1), hthird⟩
  · ext <;> simp
    have hsum := (weightedTriples_mem.mp hx).2.2.2
    omega

theorem primePowerTailTriples_subset_sparse_boxes (n : ℕ) :
    primePowerTailTriples n ⊆
      properTailFstSparseBox n ∪ properTailSndFstSparseBox n ∪
        properTailSndSndSparseBox n := by
  intro x hx
  have hxw := (mem_primePowerTailTriples.mp hx).1
  rcases primePowerTailTriples_component hx with h | h | h
  · exact Finset.mem_union.mpr <| Or.inl <| Finset.mem_union.mpr <| Or.inl <|
      mem_properTailFstSparseBox_of_weighted hxw h
  · exact Finset.mem_union.mpr <| Or.inl <| Finset.mem_union.mpr <| Or.inr <|
      mem_properTailSndFstSparseBox_of_weighted hxw h
  · exact Finset.mem_union.mpr <| Or.inr <|
      mem_properTailSndSndSparseBox_of_weighted hxw h

theorem primePowerTailTriples_card_le (n : ℕ) :
    (primePowerTailTriples n).card ≤
      3 * ((Nat.sqrt n + 1) * (Nat.log 2 n + 1)) * (n + 1) := by
  have hsubset := Finset.card_le_card (primePowerTailTriples_subset_sparse_boxes n)
  have hu1 := Finset.card_union_le
    (properTailFstSparseBox n ∪ properTailSndFstSparseBox n)
    (properTailSndSndSparseBox n)
  have hu2 := Finset.card_union_le (properTailFstSparseBox n)
    (properTailSndFstSparseBox n)
  have hpp := properPrimePowersUpTo_card_le_sqrt_log n
  calc
    (primePowerTailTriples n).card ≤
        (properTailFstSparseBox n ∪ properTailSndFstSparseBox n ∪
          properTailSndSndSparseBox n).card := hsubset
    _ ≤ (properTailFstSparseBox n ∪ properTailSndFstSparseBox n).card +
        (properTailSndSndSparseBox n).card := hu1
    _ ≤ ((properTailFstSparseBox n).card + (properTailSndFstSparseBox n).card) +
        (properTailSndSndSparseBox n).card := Nat.add_le_add_right hu2 _
    _ = 3 * (properPrimePowersUpTo n).card * (n + 1) := by
      rw [properTailFstSparseBox_card, properTailSndFstSparseBox_card,
        properTailSndSndSparseBox_card]
      ring
    _ ≤ 3 * ((Nat.sqrt n + 1) * (Nat.log 2 n + 1)) * (n + 1) := by
      nlinarith

theorem vonMangoldt_le_log_of_le {n m : ℕ} (hn : 1 ≤ n) (hm : m ≤ n) :
    ArithmeticFunction.vonMangoldt m ≤ Real.log (n : ℝ) := by
  have hΛ : ArithmeticFunction.vonMangoldt m ≤ Real.log (m : ℝ) :=
    ArithmeticFunction.vonMangoldt_le_log
  by_cases hm0 : m = 0
  · subst m
    simp
    exact Real.log_nonneg (by exact_mod_cast hn)
  · exact hΛ.trans <| Real.log_le_log
      (by exact_mod_cast Nat.pos_of_ne_zero hm0) (by exact_mod_cast hm)

theorem primePowerTail_le_bound {n : ℕ} (hn : 1 ≤ n) :
    primePowerTail n ≤ sqrtLogPrimePowerTailBound n := by
  have hlog0 : 0 ≤ Real.log (n : ℝ) :=
    Real.log_nonneg (by exact_mod_cast hn)
  unfold primePowerTail sqrtLogPrimePowerTailBound
  calc
    (∑ x ∈ primePowerTailTriples n,
        ArithmeticFunction.vonMangoldt x.1 *
          ArithmeticFunction.vonMangoldt x.2.1 *
            ArithmeticFunction.vonMangoldt x.2.2) ≤
        ∑ _x ∈ primePowerTailTriples n, Real.log (n : ℝ) ^ 3 := by
      refine Finset.sum_le_sum fun x hx ↦ ?_
      have hw := weightedTriples_mem.mp (mem_primePowerTailTriples.mp hx).1
      have h1 := vonMangoldt_le_log_of_le hn hw.1
      have h2 := vonMangoldt_le_log_of_le hn hw.2.1
      have h3 := vonMangoldt_le_log_of_le hn hw.2.2.1
      have hn1 := ArithmeticFunction.vonMangoldt_nonneg (n := x.1)
      have hn2 := ArithmeticFunction.vonMangoldt_nonneg (n := x.2.1)
      have hn3 := ArithmeticFunction.vonMangoldt_nonneg (n := x.2.2)
      calc
        ArithmeticFunction.vonMangoldt x.1 *
            ArithmeticFunction.vonMangoldt x.2.1 *
              ArithmeticFunction.vonMangoldt x.2.2 ≤
            Real.log (n : ℝ) * Real.log (n : ℝ) * Real.log (n : ℝ) := by
          gcongr
        _ = Real.log (n : ℝ) ^ 3 := by ring
    _ = (primePowerTailTriples n).card * Real.log (n : ℝ) ^ 3 := by
      simp [nsmul_eq_mul]
    _ ≤ (3 * ((Nat.sqrt n + 1) * (Nat.log 2 n + 1)) * (n + 1) : ℕ) *
          Real.log (n : ℝ) ^ 3 := by
      exact mul_le_mul_of_nonneg_right
        (by exact_mod_cast primePowerTailTriples_card_le n) (by positivity)

theorem vonMangoldtTripleWeight_split (n : ℕ) :
    vonMangoldtTripleWeight n =
      primePowerTail n + primeOnlyWeightedContribution n := by
  unfold vonMangoldtTripleWeight primePowerTail primeOnlyWeightedContribution
    primePowerTailTriples primeOnlyWeightedTriples
  exact (Finset.sum_filter_add_sum_filter_not (weightedTriples n)
    HasProperPrimePowerComponent
    (fun x : ℕ × ℕ × ℕ ↦
      ArithmeticFunction.vonMangoldt x.1 *
        ArithmeticFunction.vonMangoldt x.2.1 *
          ArithmeticFunction.vonMangoldt x.2.2)).symm

/-- Smooth real envelope for the elementary tail bound. -/
def tailEnvelope (n : ℕ) : ℝ :=
  3 * (Real.sqrt (n : ℝ) + 1) *
    (Real.logb 2 (n : ℝ) + 1) * ((n : ℝ) + 1) *
      Real.log (n : ℝ) ^ 3

theorem sqrtLogPrimePowerTailBound_le_envelope {n : ℕ} (hn : 1 ≤ n) :
    sqrtLogPrimePowerTailBound n ≤ tailEnvelope n := by
  have hsqrt : ((Nat.sqrt n : ℕ) : ℝ) ≤ Real.sqrt (n : ℝ) :=
    Real.nat_sqrt_le_real_sqrt
  have hlog : ((Nat.log 2 n : ℕ) : ℝ) ≤ Real.logb 2 (n : ℝ) :=
    Real.natLog_le_logb n 2
  have hlog0 : 0 ≤ Real.log (n : ℝ) :=
    Real.log_nonneg (by exact_mod_cast hn)
  have hlogb0 : 0 ≤ Real.logb 2 (n : ℝ) := by
    exact le_trans (by positivity : (0 : ℝ) ≤ (Nat.log 2 n : ℕ)) hlog
  unfold sqrtLogPrimePowerTailBound tailEnvelope
  push_cast
  have hsqrt' : (n.sqrt : ℝ) + 1 ≤ Real.sqrt (n : ℝ) + 1 := by linarith
  have hlog' : (Nat.log 2 n : ℝ) + 1 ≤ Real.logb 2 (n : ℝ) + 1 := by linarith
  have hprod : ((n.sqrt : ℝ) + 1) * ((Nat.log 2 n : ℝ) + 1) ≤
      (Real.sqrt (n : ℝ) + 1) * (Real.logb 2 (n : ℝ) + 1) := by
    exact mul_le_mul hsqrt' hlog' (by positivity) (by positivity)
  calc
    3 * (((n.sqrt : ℝ) + 1) * ((Nat.log 2 n : ℝ) + 1)) *
        ((n : ℝ) + 1) * Real.log (n : ℝ) ^ 3 ≤
      3 * ((Real.sqrt (n : ℝ) + 1) * (Real.logb 2 (n : ℝ) + 1)) *
        ((n : ℝ) + 1) * Real.log (n : ℝ) ^ 3 := by
      gcongr
    _ = 3 * (Real.sqrt (n : ℝ) + 1) *
        (Real.logb 2 (n : ℝ) + 1) * ((n : ℝ) + 1) *
          Real.log (n : ℝ) ^ 3 := by ring

private theorem log_pow_four_isLittleO_sqrt :
    (fun n : ℕ ↦ Real.log (n : ℝ) ^ 4) =o[atTop]
      (fun n : ℕ ↦ Real.sqrt (n : ℝ)) := by
  have h := (isLittleO_log_rpow_rpow_atTop (4 : ℝ)
    (by norm_num : (0 : ℝ) < 1 / 2)).comp_tendsto
      tendsto_natCast_atTop_atTop
  have heq1 : ∀ᶠ n : ℕ in atTop,
      Real.log (n : ℝ) ^ (4 : ℝ) = Real.log (n : ℝ) ^ (4 : ℕ) := by
    filter_upwards [eventually_ge_atTop 1] with n hn
    rw [show (4 : ℝ) = ((4 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  have heq2 : ∀ᶠ n : ℕ in atTop,
      (n : ℝ) ^ (1 / 2 : ℝ) = Real.sqrt (n : ℝ) := by
    filter_upwards with n
    rw [← Real.sqrt_eq_rpow]
  exact h.congr' heq1 heq2

private theorem modelTail_isLittleO_sq :
    (fun n : ℕ ↦ (n : ℝ) * Real.sqrt (n : ℝ) *
      Real.log (n : ℝ) ^ 4) =o[atTop]
        (fun n : ℕ ↦ (n : ℝ) ^ 2) := by
  have hmul := (isBigO_refl
    (fun n : ℕ ↦ (n : ℝ) * Real.sqrt (n : ℝ)) atTop).mul_isLittleO
      log_pow_four_isLittleO_sqrt
  have heq : ∀ᶠ n : ℕ in atTop,
      ((n : ℝ) * Real.sqrt (n : ℝ)) * Real.sqrt (n : ℝ) =
        (n : ℝ) ^ 2 := by
    filter_upwards with n
    rw [mul_assoc, Real.mul_self_sqrt (by positivity)]
    ring
  exact hmul.congr' (Eventually.of_forall fun _ ↦ by ring) heq

theorem tailEnvelope_isLittleO_sq :
    tailEnvelope =o[atTop] (fun n : ℕ ↦ (n : ℝ) ^ 2) := by
  let f : ℕ → ℝ := fun n ↦
    (n : ℝ) * Real.sqrt (n : ℝ) * Real.log (n : ℝ) ^ 4
  have hbig : tailEnvelope =O[atTop] f := by
    refine Asymptotics.IsBigO.of_bound (24 / Real.log 2) ?_
    filter_upwards [eventually_ge_atTop 4] with n hn
    have hnR : (4 : ℝ) ≤ n := by exact_mod_cast hn
    have hnpos : (0 : ℝ) < n := by positivity
    have hsqrt1 : (1 : ℝ) ≤ Real.sqrt (n : ℝ) := by
      have : (1 : ℝ) ≤ n := by linarith
      simpa using (Real.sqrt_le_sqrt this : Real.sqrt 1 ≤ Real.sqrt (n : ℝ))
    have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
    have hlog_ge : Real.log 2 ≤ Real.log (n : ℝ) :=
      Real.log_le_log (by norm_num) (by linarith)
    have hlog0 : 0 ≤ Real.log (n : ℝ) := le_trans (by positivity) hlog_ge
    have hlogb1 : (1 : ℝ) ≤ Real.logb 2 (n : ℝ) := by
      rw [Real.logb, le_div_iff₀ hlog2, one_mul]
      exact hlog_ge
    have hsqrt : Real.sqrt (n : ℝ) + 1 ≤ 2 * Real.sqrt (n : ℝ) := by linarith
    have hlogb : Real.logb 2 (n : ℝ) + 1 ≤
        2 * (Real.log (n : ℝ) / Real.log 2) := by
      rw [Real.logb] at hlogb1 ⊢
      linarith
    have hn1 : (n : ℝ) + 1 ≤ 2 * (n : ℝ) := by linarith
    have henv0 : 0 ≤ tailEnvelope n := by
      unfold tailEnvelope
      positivity
    have hf0 : 0 ≤ f n := by
      dsimp [f]
      positivity
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg henv0, abs_of_nonneg hf0]
    unfold tailEnvelope
    dsimp [f]
    calc
      3 * (Real.sqrt (n : ℝ) + 1) * (Real.logb 2 (n : ℝ) + 1) *
          ((n : ℝ) + 1) * Real.log (n : ℝ) ^ 3 ≤
        3 * (2 * Real.sqrt (n : ℝ)) *
          (2 * (Real.log (n : ℝ) / Real.log 2)) *
            (2 * (n : ℝ)) * Real.log (n : ℝ) ^ 3 := by
          gcongr
      _ = (24 / Real.log 2) * f n := by
        field_simp
        ring
  exact hbig.trans_isLittleO modelTail_isLittleO_sq

theorem sqrtLogPrimePowerTailBound_isLittleO_sq :
    sqrtLogPrimePowerTailBound =o[atTop] (fun n : ℕ ↦ (n : ℝ) ^ 2) := by
  have hO : sqrtLogPrimePowerTailBound =O[atTop] tailEnvelope := by
    refine Asymptotics.IsBigO.of_bound 1 ?_
    filter_upwards [eventually_ge_atTop 1] with n hn
    have hle := sqrtLogPrimePowerTailBound_le_envelope hn
    have h1 : 0 ≤ sqrtLogPrimePowerTailBound n := by
      unfold sqrtLogPrimePowerTailBound
      positivity
    have h2 : 0 ≤ tailEnvelope n := h1.trans hle
    simpa [Real.norm_eq_abs, abs_of_nonneg h1, abs_of_nonneg h2] using hle
  exact hO.trans_isLittleO tailEnvelope_isLittleO_sq

theorem eventually_tail_le_eps_sq {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop,
      primePowerTail n ≤ ε * (n : ℝ) ^ 2 := by
  have hb := sqrtLogPrimePowerTailBound_isLittleO_sq.bound hε
  filter_upwards [hb, eventually_ge_atTop 1] with n hbn hn
  have ht := primePowerTail_le_bound hn
  have htail0 : 0 ≤ sqrtLogPrimePowerTailBound n := by
    unfold sqrtLogPrimePowerTailBound
    positivity
  have hbn' : sqrtLogPrimePowerTailBound n ≤ ε * (n : ℝ) ^ 2 := by
    simpa [Real.norm_eq_abs, abs_of_nonneg htail0,
      abs_of_nonneg (sq_nonneg (n : ℝ))] using hbn
  exact ht.trans hbn'

#print axioms vonMangoldtTripleWeight_eq_circleIntegral
#print axioms eventually_tail_le_eps_sq

end VinogradovsTheorem.PrimePowerTail
