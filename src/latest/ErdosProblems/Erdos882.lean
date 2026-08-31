/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
This is a Lean formalization of a solution to Erdős Problem 882.
https://www.erdosproblems.com/forum/thread/882

Informal authors:
- Paul Erdős
- Vsevolod F. Lev
- Gérard Rauzy
- Csaba Sándor
- András Sárközy

Formal authors:
- Codex
- GPT-5.6 Sol

URLs:
- https://github.com/plby/lean-proofs/blob/main/ErdosProblems/Erdos882.md
-/
import Mathlib

/-!
# Erdős Problem 882

The construction of Erdős, Lev, Rauzy, Sándor and Sárközy is
`{2 ^ m - 2 ^ i | i < m}`.  Its nonempty subset sums form a primitive set.
-/

open scoped BigOperators

namespace Erdos882

/-- The number of nonzero binary digits of a natural number. -/
def binaryWeight (n : ℕ) : ℕ := n.bitIndices.length

@[simp] lemma binaryWeight_zero : binaryWeight 0 = 0 := by
  simp [binaryWeight]

@[simp] lemma binaryWeight_one : binaryWeight 1 = 1 := by
  simp [binaryWeight]

@[simp] lemma binaryWeight_two_mul (n : ℕ) :
    binaryWeight (2 * n) = binaryWeight n := by
  simp [binaryWeight]

@[simp] lemma binaryWeight_two_mul_add_one (n : ℕ) :
    binaryWeight (2 * n + 1) = binaryWeight n + 1 := by
  simp [binaryWeight]

@[simp] lemma binaryWeight_two_pow_mul (k n : ℕ) :
    binaryWeight (2 ^ k * n) = binaryWeight n := by
  simp [binaryWeight]

@[simp] lemma binaryWeight_two_pow (k : ℕ) : binaryWeight (2 ^ k) = 1 := by
  simp [binaryWeight]

lemma binaryWeight_le (n : ℕ) : binaryWeight n ≤ n := by
  have h := List.length_le_sum_of_one_le
    (n.bitIndices.map fun i => 2 ^ i)
    (by
      intro a ha
      obtain ⟨i, _, rfl⟩ := List.mem_map.mp ha
      have hp : 0 < 2 ^ i := Nat.pow_pos (by omega)
      omega)
  simpa [binaryWeight] using h

lemma binaryWeight_succ_le (n : ℕ) :
    binaryWeight (n + 1) ≤ binaryWeight n + 1 := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
      obtain ⟨q, rfl | rfl⟩ := Nat.even_or_odd' n
      · simp
      · have hq : q < 2 * q + 1 := by omega
        have hi := ih q hq
        rw [show 2 * q + 1 + 1 = 2 * (q + 1) by omega,
          binaryWeight_two_mul, binaryWeight_two_mul_add_one]
        omega

lemma binaryWeight_add_pow_le (n k : ℕ) :
    binaryWeight (n + 2 ^ k) ≤ binaryWeight n + 1 := by
  induction k generalizing n with
  | zero => simpa using binaryWeight_succ_le n
  | succ k ih =>
      obtain ⟨q, rfl | rfl⟩ := Nat.even_or_odd' n
      · rw [pow_succ,
          show 2 * q + 2 ^ k * 2 = 2 * (q + 2 ^ k) by omega,
          binaryWeight_two_mul]
        simpa using ih q
      · have hi := ih q
        rw [pow_succ,
          show 2 * q + 1 + 2 ^ k * 2 = 2 * (q + 2 ^ k) + 1 by omega,
          binaryWeight_two_mul_add_one, binaryWeight_two_mul_add_one]
        omega

lemma binaryWeight_add_geomSum_le (n : ℕ) (s : Finset ℕ) :
    binaryWeight (n + ∑ i ∈ s, 2 ^ i) ≤ binaryWeight n + s.card := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
      rw [Finset.sum_insert hi]
      calc
        binaryWeight (n + (2 ^ i + ∑ j ∈ s, 2 ^ j)) =
            binaryWeight ((n + ∑ j ∈ s, 2 ^ j) + 2 ^ i) := by
              congr 1
              omega
        _ ≤ binaryWeight (n + ∑ j ∈ s, 2 ^ j) + 1 :=
          binaryWeight_add_pow_le _ _
        _ ≤ binaryWeight n + (insert i s).card := by
          rw [Finset.card_insert_of_notMem hi]
          omega

lemma binaryWeight_add_le (n r : ℕ) :
    binaryWeight (n + r) ≤ binaryWeight n + binaryWeight r := by
  have h := binaryWeight_add_geomSum_le n r.bitIndices.toFinset
  rw [Finset.sum_toFinset_bitIndices_two_pow] at h
  simpa [binaryWeight, List.toFinset_card_of_nodup Nat.bitIndices_nodup] using h

lemma binaryWeight_finset_sum_le {α : Type*} (s : Finset α) (f : α → ℕ) :
    binaryWeight (∑ i ∈ s, f i) ≤ ∑ i ∈ s, binaryWeight (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
      rw [Finset.sum_insert hi, Finset.sum_insert hi]
      exact (binaryWeight_add_le _ _).trans (Nat.add_le_add_left ih _)

lemma binaryWeight_mul_le (n r : ℕ) :
    binaryWeight (n * r) ≤ binaryWeight n * binaryWeight r := by
  let s := r.bitIndices.toFinset
  have hr : ∑ i ∈ s, 2 ^ i = r := Finset.sum_toFinset_bitIndices_two_pow r
  calc
    binaryWeight (n * r) = binaryWeight (∑ i ∈ s, 2 ^ i * n) := by
      rw [← Finset.sum_mul, hr, Nat.mul_comm]
    _ ≤ ∑ i ∈ s, binaryWeight (2 ^ i * n) := binaryWeight_finset_sum_le s _
    _ = s.card * binaryWeight n := by simp
    _ = binaryWeight n * binaryWeight r := by
      simp [s, binaryWeight, List.toFinset_card_of_nodup Nat.bitIndices_nodup,
        Nat.mul_comm]

lemma binaryWeight_eq_digits_sum (n : ℕ) :
    binaryWeight n = (Nat.digits 2 n).sum := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
      obtain ⟨q, hq | hq⟩ := Nat.even_or_odd' n
      · subst n
        by_cases hq0 : q = 0
        · subst q
          simp
        · have hqpos : 0 < q := Nat.pos_of_ne_zero hq0
          rw [Nat.digits_base_mul (b := 2) (m := q) (by omega) hqpos]
          simp only [List.sum_cons, zero_add, binaryWeight_two_mul]
          exact ih q (by omega)
      · subst n
        rw [Nat.digits_def' (b := 2) (by omega) (by omega)]
        have hmod : (2 * q + 1) % 2 = 1 := by omega
        have hdiv : (2 * q + 1) / 2 = q := by omega
        rw [hmod, hdiv, List.sum_cons, binaryWeight_two_mul_add_one,
          ih q (by omega)]
        omega

/-- Binary digits below `2 ^ m` and above that place occupy disjoint blocks. -/
lemma binaryWeight_block (r c m : ℕ) (hr : r < 2 ^ m) :
    binaryWeight (c * 2 ^ m + r) = binaryWeight c + binaryWeight r := by
  by_cases hc : c = 0
  · subst c
    simp
  have hcpos : 0 < c := Nat.pos_of_ne_zero hc
  have hlen : (Nat.digits 2 r).length ≤ m :=
    (Nat.digits_length_le_iff (by omega) r).2 hr
  have hd := Nat.digits_append_zeroes_append_digits
    (b := 2) (k := m - (Nat.digits 2 r).length) (m := c) (n := r)
    (by omega) hcpos
  rw [Nat.add_sub_of_le hlen] at hd
  have hsum := congrArg List.sum hd
  simp only [List.sum_append_nat, List.sum_replicate, nsmul_zero, add_zero] at hsum
  rw [binaryWeight_eq_digits_sum, binaryWeight_eq_digits_sum,
    binaryWeight_eq_digits_sum]
  rw [show c * 2 ^ m + r = r + 2 ^ m * c by ac_rfl]
  exact hsum.symm.trans (Nat.add_comm _ _)

/-- The number of binary carries accumulated below a natural number. -/
def binaryDefect (n : ℕ) : ℕ := n - binaryWeight n

lemma binaryDefect_succ_mono (n : ℕ) :
    binaryDefect n ≤ binaryDefect (n + 1) := by
  have hn := binaryWeight_le n
  have hn1 := binaryWeight_le (n + 1)
  have hs := binaryWeight_succ_le n
  simp only [binaryDefect]
  omega

lemma binaryDefect_mono : Monotone binaryDefect :=
  monotone_nat_of_le_succ binaryDefect_succ_mono

lemma binaryDefect_lt_add_two (n : ℕ) :
    binaryDefect n < binaryDefect (n + 2) := by
  have hn := binaryWeight_le n
  have hn2 := binaryWeight_le (n + 2)
  have hs := binaryWeight_add_pow_le n 1
  norm_num at hs
  simp only [binaryDefect]
  omega

lemma eq_add_one_of_binaryDefect_eq {c d : ℕ} (hcd : c < d)
    (hdef : binaryDefect c = binaryDefect d) : d = c + 1 := by
  by_contra h
  have hc2 : c + 2 ≤ d := by omega
  have hle := binaryDefect_mono hc2
  have hlt := binaryDefect_lt_add_two c
  omega

lemma binaryDefect_pos {d : ℕ} (hd : 2 ≤ d) : 0 < binaryDefect d := by
  have hle := binaryDefect_mono hd
  have htwo : binaryDefect 2 = 1 := by rfl
  rw [htwo] at hle
  omega

/-- Sum of the binary place values indexed by `S`. -/
def bitSum (S : Finset ℕ) : ℕ := ∑ i ∈ S, 2 ^ i

/-- A subset sum of the indexed Erdős--Sárközy construction. -/
def indexedSum (m : ℕ) (S : Finset ℕ) : ℕ :=
  ∑ i ∈ S, (2 ^ m - 2 ^ i)

lemma binaryWeight_bitSum (S : Finset ℕ) : binaryWeight (bitSum S) = S.card := by
  unfold bitSum binaryWeight
  rw [← List.toFinset_card_of_nodup Nat.bitIndices_nodup,
    Finset.toFinset_bitIndices_sum_two_pow]

lemma bitSum_lt_pow {m : ℕ} {S : Finset ℕ} (hS : S ⊆ Finset.range m) :
    bitSum S < 2 ^ m := by
  apply Nat.geomSum_lt (m := 2) (by omega)
  intro i hi
  exact Finset.mem_range.mp (hS hi)

lemma bitSum_pos {S : Finset ℕ} (hS : S.Nonempty) : 0 < bitSum S := by
  obtain ⟨i, hi⟩ := hS
  have hpow : 0 < 2 ^ i := Nat.pow_pos (by omega)
  exact hpow.trans_le (Finset.single_le_sum (fun _ _ ↦ Nat.zero_le _) hi)

lemma indexedSum_eq (m : ℕ) (S : Finset ℕ) (hS : S ⊆ Finset.range m) :
    indexedSum m S = S.card * 2 ^ m - bitSum S := by
  induction S using Finset.induction_on with
  | empty => simp [indexedSum, bitSum]
  | @insert i S hi ih =>
      have him : i < m := Finset.mem_range.mp (hS (by simp))
      have hSi : S ⊆ Finset.range m := fun j hj ↦ hS (by simp [hj])
      have hiM : 2 ^ i ≤ 2 ^ m := pow_le_pow_right₀ (by omega) him.le
      have hqle : bitSum S ≤ S.card * 2 ^ m := by
        calc
          bitSum S = ∑ j ∈ S, 2 ^ j := rfl
          _ ≤ ∑ _j ∈ S, 2 ^ m := Finset.sum_le_sum fun j hj ↦
            pow_le_pow_right₀ (by omega) (Finset.mem_range.mp (hSi hj)).le
          _ = S.card * 2 ^ m := by simp
      unfold bitSum at hqle
      simp only [indexedSum, bitSum, Finset.sum_insert hi,
        Finset.card_insert_of_notMem hi]
      rw [show ∑ j ∈ S, (2 ^ m - 2 ^ j) =
          S.card * 2 ^ m - ∑ j ∈ S, 2 ^ j by simpa [indexedSum, bitSum] using ih hSi]
      have hcard : (S.card + 1) * 2 ^ m = S.card * 2 ^ m + 2 ^ m := by ring
      rw [hcard]
      omega

private lemma no_proper_divisor
    (m k l q r x y d : ℕ)
    (hk : 0 < k) (hl : 0 < l)
    (hq : 0 < q) (hr : 0 < r)
    (hqM : q < 2 ^ m) (hrM : r < 2 ^ m)
    (hx : x + q = k * 2 ^ m) (hy : y + r = l * 2 ^ m)
    (hxy : y = x * d) (hd : 2 ≤ d)
    (hwq : binaryWeight q = k) (hwr : binaryWeight r = l)
    (hhalf : k = 1 → 2 * q ≤ 2 ^ m) : False := by
  have hM : 0 < 2 ^ m := Nat.pow_pos (by omega)
  have hkpred : k - 1 + 1 = k := Nat.sub_add_cancel (by omega)
  have hlpred : l - 1 + 1 = l := Nat.sub_add_cancel (by omega)
  have hxlt : x < k * 2 ^ m := by omega
  have hylt : y < l * 2 ^ m := by omega
  have hxlow : (k - 1) * 2 ^ m < x := by nlinarith
  have hylow : (l - 1) * 2 ^ m < y := by nlinarith
  have hyupper : y < (d * k) * 2 ^ m := by
    have hh := Nat.mul_lt_mul_of_pos_right hxlt (by omega : 0 < d)
    rw [hxy]
    convert hh using 1
    all_goals ring
  have hlcoef : l - 1 < d * k :=
    (Nat.mul_lt_mul_right hM).mp (hylow.trans hyupper)
  have hldk : l ≤ d * k := by omega
  let c := d * k - l
  have hcl : c + l = d * k := Nat.sub_add_cancel hldk
  have hdxlow : (d * (k - 1)) * 2 ^ m < y := by
    have hh := Nat.mul_lt_mul_of_pos_right hxlow (by omega : 0 < d)
    rw [hxy]
    convert hh using 1
    all_goals ring
  have hcoef : d * (k - 1) < l :=
    (Nat.mul_lt_mul_right hM).mp (hdxlow.trans hylt)
  have hdk : d * (k - 1) + d = d * k := by
    calc
      d * (k - 1) + d = d * ((k - 1) + 1) := by rw [Nat.mul_add, Nat.mul_one]
      _ = d * k := by rw [hkpred]
  have hcd : c < d := by omega
  have hmul := congrArg (fun z : ℕ => d * z) hx
  simp only [Nat.mul_add] at hmul
  have heq : d * q = c * 2 ^ m + r := by nlinarith
  have hblock : binaryWeight (d * q) = binaryWeight c + l := by
    rw [heq, binaryWeight_block r c m hrM, hwr]
  have hmulweight : binaryWeight (d * q) ≤ binaryWeight d * k := by
    simpa [hwq] using binaryWeight_mul_le d q
  have hweight : binaryWeight c + l ≤ binaryWeight d * k := by
    rw [← hblock]
    exact hmulweight
  have hwd : binaryWeight d ≤ d := binaryWeight_le d
  have hwc : binaryWeight c ≤ c := binaryWeight_le c
  have hdadd : binaryWeight d + binaryDefect d = d := by
    simp [binaryDefect, Nat.add_sub_of_le hwd]
  have hcadd : binaryWeight c + binaryDefect c = c := by
    simp [binaryDefect, Nat.add_sub_of_le hwc]
  have hkd := congrArg (fun z : ℕ => z * k) hdadd
  simp only [Nat.add_mul] at hkd
  have hdefect : k * binaryDefect d ≤ binaryDefect c := by
    rw [Nat.mul_comm]
    omega
  have hmono : binaryDefect c ≤ binaryDefect d := binaryDefect_mono hcd.le
  have hdpos : 0 < binaryDefect d := binaryDefect_pos hd
  have hkone : k = 1 := by
    by_contra hne
    have hk2 : 2 ≤ k := by omega
    have htwod := Nat.mul_le_mul_right (binaryDefect d) hk2
    omega
  have hdefeq : binaryDefect c = binaryDefect d := by
    have hdefone : binaryDefect d ≤ binaryDefect c := by
      rw [hkone] at hdefect
      simpa using hdefect
    exact le_antisymm hmono hdefone
  have hdc : d = c + 1 := eq_add_one_of_binaryDefect_eq hcd hdefeq
  have hqhalf := hhalf hkone
  have hqbig : (d - 1) * 2 ^ m < d * q := by
    rw [heq]
    have hcform : c = d - 1 := by omega
    rw [hcform]
    omega
  have hqsmall : d * q ≤ (d - 1) * 2 ^ m := by
    have hh := Nat.mul_le_mul_left d hqhalf
    have hdineq : d ≤ 2 * (d - 1) := by omega
    have hh' := Nat.mul_le_mul_right (2 ^ m) hdineq
    have htwo : 2 * (d * q) ≤ 2 * ((d - 1) * 2 ^ m) := by
      calc
        2 * (d * q) = d * (2 * q) := by ring
        _ ≤ d * 2 ^ m := hh
        _ ≤ 2 * ((d - 1) * 2 ^ m) := by
          convert hh' using 1
          all_goals ring
    omega
  omega

theorem indexedSum_dvd_indexedSum
    {m : ℕ} {S T : Finset ℕ}
    (hS : S ⊆ Finset.range m) (hT : T ⊆ Finset.range m)
    (hneS : S.Nonempty) (hneT : T.Nonempty)
    (hdiv : indexedSum m S ∣ indexedSum m T) :
    indexedSum m S = indexedSum m T := by
  let q := bitSum S
  let r := bitSum T
  let k := S.card
  let l := T.card
  let x := indexedSum m S
  let y := indexedSum m T
  have hk : 0 < k := Finset.card_pos.mpr hneS
  have hl : 0 < l := Finset.card_pos.mpr hneT
  have hq : 0 < q := bitSum_pos hneS
  have hr : 0 < r := bitSum_pos hneT
  have hqM : q < 2 ^ m := bitSum_lt_pow hS
  have hrM : r < 2 ^ m := bitSum_lt_pow hT
  have hx : x + q = k * 2 ^ m := by
    rw [show x = k * 2 ^ m - q by simpa [x, k, q] using indexedSum_eq m S hS]
    exact Nat.sub_add_cancel (hqM.le.trans (Nat.le_mul_of_pos_left _ hk))
  have hy : y + r = l * 2 ^ m := by
    rw [show y = l * 2 ^ m - r by simpa [y, l, r] using indexedSum_eq m T hT]
    exact Nat.sub_add_cancel (hrM.le.trans (Nat.le_mul_of_pos_left _ hl))
  have hMpos : 0 < 2 ^ m := Nat.pow_pos (by omega)
  have hxpos : 0 < x := by nlinarith
  have hypos : 0 < y := by nlinarith
  obtain ⟨d, hd⟩ := hdiv
  have hdpos : 0 < d := by
    by_contra hd0
    have : d = 0 := by omega
    subst d
    simp at hd
    omega
  by_cases hd1 : d = 1
  · subst d
    simpa [x, y] using hd.symm
  have hd2 : 2 ≤ d := by omega
  exfalso
  apply no_proper_divisor m k l q r x y d hk hl hq hr hqM hrM hx hy
    (by simpa [x, y] using hd) hd2
    (by simpa [q, k] using binaryWeight_bitSum S)
    (by simpa [r, l] using binaryWeight_bitSum T)
  intro hk1
  have hkcard : S.card = 1 := by simpa [k] using hk1
  obtain ⟨i, rfl⟩ := Finset.card_eq_one.mp hkcard
  have him : i < m := Finset.mem_range.mp (hS (by simp))
  simp only [bitSum, Finset.sum_singleton, q]
  calc
    2 * 2 ^ i = 2 ^ (i + 1) := by rw [pow_succ']
    _ ≤ 2 ^ m := pow_le_pow_right₀ (by omega) (by omega)

/-- The set of all sums of nonempty subsets of `A`. -/
def nonemptySubsetSums (A : Finset ℕ) : Finset ℕ :=
  ((A.powerset.filter fun S ↦ S.Nonempty).image fun S ↦ ∑ a ∈ S, a)

/-- A finite set is primitive if divisibility between two of its elements forces equality. -/
def IsPrimitive (B : Finset ℕ) : Prop :=
  ∀ x ∈ B, ∀ y ∈ B, x ∣ y → x = y

/-- The injection which enumerates the published construction. -/
def constructionEmbedding (m : ℕ) : Fin m ↪ ℕ where
  toFun i := 2 ^ m - 2 ^ i.val
  inj' := by
    intro i j hij
    have hi : 2 ^ i.val ≤ 2 ^ m := pow_le_pow_right₀ (by omega) i.isLt.le
    have hj : 2 ^ j.val ≤ 2 ^ m := pow_le_pow_right₀ (by omega) j.isLt.le
    have hp : 2 ^ i.val = 2 ^ j.val := (tsub_right_inj hi hj).mp hij
    exact Fin.ext (Nat.pow_right_injective (by omega) hp)

/-- The finite set `{2^m - 2^i | 0 ≤ i < m}`. -/
def construction (m : ℕ) : Finset ℕ :=
  Finset.univ.map (constructionEmbedding m)

@[simp] lemma construction_card (m : ℕ) : (construction m).card = m := by
  simp [construction]

lemma construction_pos {m a : ℕ} (ha : a ∈ construction m) : 0 < a := by
  rw [construction, Finset.mem_map] at ha
  obtain ⟨i, _, rfl⟩ := ha
  have hi : 2 ^ i.val < 2 ^ m := pow_lt_pow_right₀ (by omega) i.isLt
  change 0 < 2 ^ m - 2 ^ i.val
  omega

lemma construction_le_pow {m a : ℕ} (ha : a ∈ construction m) : a ≤ 2 ^ m := by
  rw [construction, Finset.mem_map] at ha
  obtain ⟨i, _, rfl⟩ := ha
  change 2 ^ m - 2 ^ i.val ≤ 2 ^ m
  exact Nat.sub_le _ _

private def valEmbedding (m : ℕ) : Fin m ↪ ℕ where
  toFun i := i.val
  inj' := Fin.val_injective

private lemma recover_indices {m : ℕ} {U : Finset ℕ} (hU : U ⊆ construction m) :
    ∃ S : Finset ℕ, S ⊆ Finset.range m ∧
      U.card = S.card ∧ (∑ a ∈ U, a) = indexedSum m S := by
  let e := constructionEmbedding m
  let P := U.preimage e e.injective.injOn
  let S := P.map (valEmbedding m)
  have hmap : P.map e = U := by
    ext a
    constructor
    · intro ha
      rw [Finset.mem_map] at ha
      obtain ⟨i, hi, rfl⟩ := ha
      exact Finset.mem_preimage.mp hi
    · intro ha
      have hac := hU ha
      rw [construction, Finset.mem_map] at hac
      obtain ⟨i, _, rfl⟩ := hac
      rw [Finset.mem_map]
      exact ⟨i, Finset.mem_preimage.mpr ha, rfl⟩
  refine ⟨S, ?_, ?_, ?_⟩
  · intro i hi
    simp only [S, Finset.mem_map] at hi
    obtain ⟨j, _, rfl⟩ := hi
    exact Finset.mem_range.mpr j.isLt
  · rw [← hmap]
    simp [S]
  · rw [← hmap]
    simp only [Finset.sum_map]
    change (∑ i ∈ P, (2 ^ m - 2 ^ i.val)) = indexedSum m S
    unfold indexedSum
    simp [S, valEmbedding]

/-- Every pair of nonempty subset sums of the construction is incomparable by divisibility. -/
theorem construction_subset_sums_primitive (m : ℕ) :
    IsPrimitive (nonemptySubsetSums (construction m)) := by
  intro x hx y hy hdiv
  rw [nonemptySubsetSums, Finset.mem_image] at hx hy
  obtain ⟨U, hUf, rfl⟩ := hx
  obtain ⟨V, hVf, rfl⟩ := hy
  have hUf' := Finset.mem_filter.mp hUf
  have hVf' := Finset.mem_filter.mp hVf
  have hUsub : U ⊆ construction m := Finset.mem_powerset.mp hUf'.1
  have hVsub : V ⊆ construction m := Finset.mem_powerset.mp hVf'.1
  obtain ⟨S, hS, hcardS, hsumS⟩ := recover_indices hUsub
  obtain ⟨T, hT, hcardT, hsumT⟩ := recover_indices hVsub
  have hneS : S.Nonempty := Finset.card_pos.mp (by
    rw [← hcardS]
    exact hUf'.2.card_pos)
  have hneT : T.Nonempty := Finset.card_pos.mp (by
    rw [← hcardT]
    exact hVf'.2.card_pos)
  have hdiv' : indexedSum m S ∣ indexedSum m T := by
    rwa [← hsumS, ← hsumT]
  have heq := indexedSum_dvd_indexedSum hS hT hneS hneT hdiv'
  exact hsumS.trans (heq.trans hsumT.symm)

/-- `A` is an admissible set for Problem 882 at `n`. -/
def Admissible (n : ℕ) (A : Finset ℕ) : Prop :=
  A ⊆ Finset.Icc 1 n ∧ IsPrimitive (nonemptySubsetSums A)

lemma construction_admissible {m n : ℕ} (hmn : 2 ^ m ≤ n) :
    Admissible n (construction m) := by
  constructor
  · intro a ha
    exact Finset.mem_Icc.mpr
      ⟨construction_pos ha, (construction_le_pow ha).trans hmn⟩
  · exact construction_subset_sums_primitive m

/-- The actual largest cardinality in the finite extremal problem. -/
noncomputable def maximumSize (n : ℕ) : ℕ := by
  classical
  exact ((Finset.Icc 1 n).powerset.filter fun A ↦
    IsPrimitive (nonemptySubsetSums A)).sup Finset.card

lemma card_le_maximumSize {n : ℕ} {A : Finset ℕ} (hA : Admissible n A) :
    A.card ≤ maximumSize n := by
  classical
  apply Finset.le_sup
  exact Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr hA.1, hA.2⟩

lemma maximumSize_attained (n : ℕ) :
    ∃ A : Finset ℕ, Admissible n A ∧ A.card = maximumSize n := by
  classical
  let candidates := (Finset.Icc 1 n).powerset.filter fun A ↦
    IsPrimitive (nonemptySubsetSums A)
  have hempty : ∅ ∈ candidates := by
    simp [candidates, IsPrimitive, nonemptySubsetSums]
  obtain ⟨A, hA, hmax⟩ := Finset.exists_mem_eq_sup candidates ⟨∅, hempty⟩ Finset.card
  refine ⟨A, ?_, hmax.symm⟩
  exact ⟨Finset.mem_powerset.mp (Finset.mem_filter.mp hA).1,
    (Finset.mem_filter.mp hA).2⟩

lemma log_bound (n : ℕ) :
    Real.logb 2 (n : ℝ) - 1 < (Nat.log 2 n : ℝ) := by
  have h := Nat.lt_floor_add_one (Real.logb 2 (n : ℝ))
  have hf : ⌊Real.logb 2 (n : ℝ)⌋₊ = Nat.log 2 n := by
    simpa using Real.natFloor_logb_natCast 2 n
  rw [hf] at h
  linarith

/-- The explicit set of size `⌊log₂ n⌋` resolving the published lower bound. -/
theorem erdos_882_witness (n : ℕ) (hn : 0 < n) :
    ∃ A : Finset ℕ,
      A.card = Nat.log 2 n ∧ Admissible n A ∧
        Real.logb 2 (n : ℝ) - 1 < (A.card : ℝ) := by
  let m := Nat.log 2 n
  refine ⟨construction m, by simp [m], ?_, ?_⟩
  · exact construction_admissible (Nat.pow_log_le_self 2 (by omega))
  · simpa [m] using log_bound n

/-- Erdős Problem 882: the largest possible size is greater than `log₂ n - 1`. -/
theorem erdos_882 (n : ℕ) (hn : 0 < n) :
    Real.logb 2 (n : ℝ) - 1 < (maximumSize n : ℝ) := by
  obtain ⟨A, hcard, hA, hlog⟩ := erdos_882_witness n hn
  have hle : A.card ≤ maximumSize n := card_le_maximumSize hA
  exact hlog.trans_le (by exact_mod_cast hle)

end Erdos882
