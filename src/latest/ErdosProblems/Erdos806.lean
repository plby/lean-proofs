/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/- Original license: Apache 2.0. Note: This file has been modified. -/
/-
This is a Lean formalization of a solution to Erdős Problem 806.
https://www.erdosproblems.com/forum/thread/806

Informal authors:
- Noga Alon
- Boris Bukh
- Benny Sudakov

Formal authors:
- Codex
- GPT-5.6 Sol

URLs:
- https://github.com/plby/lean-proofs/blob/main/ErdosProblems/Erdos806.md
-/
/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import Mathlib.Algebra.Group.Pointwise.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Ring.CharZero
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Data.Finset.Interval
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Data.Nat.ModEq
import Lean.Elab.Tactic.Omega
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Erdős Problem 806

Alon, Bukh, and Sudakov proved that every finite set
\(A \subseteq \{1,\ldots,n\}\) with \(|A|\leq\sqrt n\) is contained in
\(B+B\) for an integer set \(B\) of size \(o(\sqrt n)\), uniformly in \(A\).

The proof below formalizes their explicit base-\(q\) universal-set construction.
A finite set is partitioned into quotient fibers and then into chunks of at
most \(k\) elements.  A digit-by-digit correcting shift covers every chunk
using a universal residue set of size at most \(kq^{k-1}\).  Choosing
\(q=\lfloor n^{1/(2k-1)}\rfloor\), then taking fixed \(k\) and a sufficiently
large threshold, gives the exact uniform little-o statement.
-/

open Finset
open scoped Pointwise

namespace Erdos806

noncomputable section

def digit (q i x : ℕ) : ℕ := x / q ^ i % q

def zeroLayer (q k i : ℕ) : Finset ℕ :=
  ((Finset.range (q ^ (k - i - 1))) ×ˢ (Finset.range (q ^ i))).image
    (fun p : ℕ × ℕ => p.1 * q ^ (i + 1) + p.2)

def universalSet (q k : ℕ) : Finset ℕ :=
  (Finset.range k).biUnion (zeroLayer q k)

lemma zeroLayer_card_le (q k i : ℕ) (hi : i < k) :
    (zeroLayer q k i).card ≤ q ^ (k - 1) := by
  rw [zeroLayer]
  calc
    ((Finset.range (q ^ (k - i - 1)) ×ˢ Finset.range (q ^ i)).image
        (fun p : ℕ × ℕ => p.1 * q ^ (i + 1) + p.2)).card
        ≤ (Finset.range (q ^ (k - i - 1)) ×ˢ Finset.range (q ^ i)).card :=
          Finset.card_image_le
    _ = q ^ (k - i - 1) * q ^ i := by simp
    _ = q ^ (k - 1) := by
      rw [← pow_add]
      congr 1
      omega

lemma universalSet_card_le (q k : ℕ) :
    (universalSet q k).card ≤ k * q ^ (k - 1) := by
  rw [universalSet]
  calc
    ((Finset.range k).biUnion (zeroLayer q k)).card
        ≤ ∑ i ∈ Finset.range k, (zeroLayer q k i).card := Finset.card_biUnion_le
    _ ≤ ∑ _i ∈ Finset.range k, q ^ (k - 1) := by
      gcongr with i hi
      exact zeroLayer_card_le q k i (Finset.mem_range.mp hi)
    _ = k * q ^ (k - 1) := by simp

lemma mem_zeroLayer_of_digit_eq_zero (q k i u : ℕ) (hq : 0 < q)
    (hi : i < k) (hu : u < q ^ k) (hdigit : digit q i u = 0) :
    u ∈ zeroLayer q k i := by
  have hpowi : 0 < q ^ i := Nat.pow_pos hq
  have hpows : 0 < q ^ (i + 1) := Nat.pow_pos hq
  have hquot : u / q ^ i = q * (u / q ^ (i + 1)) := by
    have hmod : u / q ^ i % q = 0 := hdigit
    have hdecomp := Nat.mod_add_div (u / q ^ i) q
    rw [hmod, zero_add] at hdecomp
    rw [Nat.div_div_eq_div_mul, ← pow_succ] at hdecomp
    exact hdecomp.symm
  have hu_decomp :
      u = (u / q ^ (i + 1)) * q ^ (i + 1) + u % q ^ i := by
    calc
      u = u % q ^ i + q ^ i * (u / q ^ i) := (Nat.mod_add_div _ _).symm
      _ = u % q ^ i + q ^ i * (q * (u / q ^ (i + 1))) := by rw [hquot]
      _ = (u / q ^ (i + 1)) * q ^ (i + 1) + u % q ^ i := by
        rw [pow_succ]
        ring
  have hhigh : u / q ^ (i + 1) < q ^ (k - i - 1) := by
    rw [Nat.div_lt_iff_lt_mul hpows]
    rw [← pow_add]
    convert hu using 1
    congr 1
    omega
  have hlow : u % q ^ i < q ^ i := Nat.mod_lt u hpowi
  rw [zeroLayer]
  apply Finset.mem_image.mpr
  refine ⟨(u / q ^ (i + 1), u % q ^ i), ?_, ?_⟩
  · simp [hhigh, hlow]
  · exact hu_decomp.symm

lemma mem_universalSet_of_digit_eq_zero (q k i u : ℕ) (hq : 0 < q)
    (hi : i < k) (hu : u < q ^ k) (hdigit : digit q i u = 0) :
    u ∈ universalSet q k := by
  rw [universalSet, Finset.mem_biUnion]
  exact ⟨i, Finset.mem_range.mpr hi,
    mem_zeroLayer_of_digit_eq_zero q k i u hq hi hu hdigit⟩

def correctingShift (q : ℕ) (x : ℕ → ℕ) : ℕ → ℕ
  | 0 => 0
  | i + 1 =>
      let g := correctingShift q x i
      let d := (q - digit q i (g + x i)) % q
      g + d * q ^ i

lemma correctingShift_lt (q : ℕ) (x : ℕ → ℕ) (hq : 1 < q) :
    ∀ i, correctingShift q x i < q ^ i := by
  intro i
  induction i with
  | zero => simp [correctingShift]
  | succ i ih =>
      have hqpos : 0 < q := by omega
      have hd : (q - digit q i (correctingShift q x i + x i)) % q < q :=
        Nat.mod_lt _ hqpos
      simp only [correctingShift]
      rw [pow_succ]
      have hp : 0 < q ^ i := Nat.pow_pos hqpos
      nlinarith

lemma digit_eq_of_modEq (q i x y : ℕ) (h : x ≡ y [MOD q ^ (i + 1)]) :
    digit q i x = digit q i y := by
  have hmod : x % q ^ (i + 1) = y % q ^ (i + 1) := h
  simp only [digit]
  rw [← Nat.mod_mul_right_div_self x (q ^ i) q,
    ← Nat.mod_mul_right_div_self y (q ^ i) q, ← pow_succ, hmod]

lemma correctingShift_modEq (q : ℕ) (x : ℕ → ℕ) (i j : ℕ) (hj : j ≤ i) :
    correctingShift q x i ≡ correctingShift q x j [MOD q ^ j] := by
  induction i with
  | zero =>
      have : j = 0 := by omega
      subst j
      exact Nat.ModEq.refl _
  | succ i ih =>
      by_cases hji : j ≤ i
      · have hrec := ih hji
        apply Nat.ModEq.trans ?_ hrec
        have hdvd : q ^ j ∣
            (q - digit q i (correctingShift q x i + x i)) % q * q ^ i :=
          dvd_mul_of_dvd_right (Nat.pow_dvd_pow q hji) _
        simpa only [correctingShift, add_zero] using
          (Nat.ModEq.refl (correctingShift q x i)).add hdvd.modEq_zero_nat
      · have : j = i + 1 := by omega
        subst j
        exact Nat.ModEq.refl _

lemma correctingShift_digit_zero (q : ℕ) (x : ℕ → ℕ) (hq : 1 < q) :
    ∀ i, digit q i (correctingShift q x (i + 1) + x i) = 0 := by
  intro i
  let g := correctingShift q x i
  let a := g + x i
  let d := (q - digit q i a) % q
  have hqpos : 0 < q := by omega
  have hp : 0 < q ^ i := Nat.pow_pos hqpos
  have hadd : digit q i (a + d * q ^ i) = (digit q i a + d) % q := by
    simp only [digit]
    rw [mul_comm d, Nat.add_mul_div_left a d hp]
    simp [Nat.add_mod]
  have hcancel : (digit q i a + d) % q = 0 := by
    have hlt : digit q i a < q := Nat.mod_lt _ hqpos
    by_cases hz : digit q i a = 0
    · simp [d, hz]
    · have hsub : q - digit q i a < q := by omega
      rw [show d = q - digit q i a by simp [d, Nat.mod_eq_of_lt hsub]]
      rw [Nat.add_sub_of_le (Nat.le_of_lt hlt), Nat.mod_self]
  change digit q i (g + d * q ^ i + x i) = 0
  simpa only [a, add_assoc, add_left_comm, add_comm] using hadd.trans hcancel

lemma correctingShift_preserves_digit (q : ℕ) (x : ℕ → ℕ) (i j : ℕ)
    (hj : j < i) :
    digit q j (correctingShift q x i + x j) =
      digit q j (correctingShift q x (j + 1) + x j) := by
  apply digit_eq_of_modEq
  exact (correctingShift_modEq q x i (j + 1) (by omega)).add (Nat.ModEq.refl _)

lemma correctingShift_all_digits_zero (q : ℕ) (x : ℕ → ℕ) (hq : 1 < q)
    (i j : ℕ) (hj : j < i) :
    digit q j (correctingShift q x i + x j) = 0 := by
  rw [correctingShift_preserves_digit q x i j hj]
  exact correctingShift_digit_zero q x hq j

def enumerate (T : Finset ℕ) (i : ℕ) : ℕ :=
  if hi : i < T.card then (T.equivFin.symm ⟨i, hi⟩ : T).1 else 0

lemma enumerate_mem (T : Finset ℕ) (i : ℕ) (hi : i < T.card) :
    enumerate T i ∈ T := by
  simp only [enumerate, dif_pos hi]
  exact (T.equivFin.symm ⟨i, hi⟩).2

lemma exists_enumerate_eq (T : Finset ℕ) (t : ℕ) (ht : t ∈ T) :
    ∃ i < T.card, enumerate T i = t := by
  let z : T := ⟨t, ht⟩
  let i := (T.equivFin z).1
  have hi : i < T.card := (T.equivFin z).2
  refine ⟨i, hi, ?_⟩
  simp only [enumerate, dif_pos hi]
  exact congrArg Subtype.val (T.equivFin.symm_apply_apply z)

lemma mod_lt_pow (q k x : ℕ) (hq : 0 < q) : x % q ^ k < q ^ k :=
  Nat.mod_lt _ (Nat.pow_pos hq)

lemma universal_chunk_residues (q k : ℕ) (hq : 1 < q)
    (T : Finset ℕ) (hTcard : T.card ≤ k) :
    let g := correctingShift q (enumerate T) k
    g < q ^ k ∧ ∀ t ∈ T, (g + t) % q ^ k ∈ universalSet q k := by
  let g := correctingShift q (enumerate T) k
  have hg : g < q ^ k := correctingShift_lt q (enumerate T) hq k
  refine ⟨hg, ?_⟩
  intro t ht
  obtain ⟨i, hiT, hit⟩ := exists_enumerate_eq T t ht
  have hik : i < k := lt_of_lt_of_le hiT hTcard
  have hzero : digit q i (g + t) = 0 := by
    rw [← hit]
    exact correctingShift_all_digits_zero q (enumerate T) hq k i hik
  have hmodEqM : (g + t) % q ^ k ≡ g + t [MOD q ^ k] := Nat.mod_modEq _ _
  have hdiv : q ^ (i + 1) ∣ q ^ k := Nat.pow_dvd_pow q (by omega)
  have hzero' : digit q i ((g + t) % q ^ k) = 0 := by
    rw [digit_eq_of_modEq q i ((g + t) % q ^ k) (g + t) (hmodEqM.of_dvd hdiv)]
    exact hzero
  exact mem_universalSet_of_digit_eq_zero q k i ((g + t) % q ^ k)
    (by omega) hik (mod_lt_pow q k _ (by omega)) hzero'

lemma universal_chunk_cover (q k : ℕ) (hq : 1 < q)
    (T : Finset ℕ) (hTcard : T.card ≤ k) (hTlt : ∀ t ∈ T, t < q ^ k) :
    ∃ g < q ^ k, ∀ t ∈ T, ∃ u ∈ universalSet q k,
      (t : ℤ) = (u : ℤ) + -(g : ℤ) ∨
      (t : ℤ) = (u : ℤ) + ((q ^ k : ℕ) : ℤ) - (g : ℤ) := by
  let g := correctingShift q (enumerate T) k
  have hres := universal_chunk_residues q k hq T hTcard
  change g < q ^ k ∧ ∀ t ∈ T, (g + t) % q ^ k ∈ universalSet q k at hres
  refine ⟨g, hres.1, ?_⟩
  intro t ht
  let u := (g + t) % q ^ k
  refine ⟨u, hres.2 t ht, ?_⟩
  have hMpos : 0 < q ^ k := Nat.pow_pos (by omega)
  have hsum_lt : g + t < 2 * q ^ k := by
    have hg := hres.1
    have ht' := hTlt t ht
    omega
  have hquot : (g + t) / q ^ k ≤ 1 := by
    apply (Nat.div_le_iff_le_mul hMpos).mpr
    omega
  have hdecomp := Nat.mod_add_div (g + t) (q ^ k)
  change u + q ^ k * ((g + t) / q ^ k) = g + t at hdecomp
  interval_cases hcase : (g + t) / q ^ k
  · left
    norm_num [hcase] at hdecomp
    have hc : (u : ℤ) = (g : ℤ) + (t : ℤ) := by exact_mod_cast hdecomp
    omega
  · right
    norm_num [hcase] at hdecomp
    have hc : (u : ℤ) + (q ^ k : ℕ) = (g : ℤ) + (t : ℤ) := by
      exact_mod_cast hdecomp
    omega

lemma exists_chunking {α : Type*} (S : Finset α) (k : ℕ)
    (hk : 0 < k) :
    ∃ C : Finset (Finset α),
      (∀ T ∈ C, T ⊆ S ∧ T.card ≤ k) ∧
      (∀ x ∈ S, ∃ T ∈ C, x ∈ T) ∧
      C.card ≤ S.card / k + 1 := by
  classical
  induction hn : S.card using Nat.strong_induction_on generalizing S with
  | h n ih =>
      by_cases hsmall : S.card ≤ k
      · refine ⟨{S}, ?_, ?_, ?_⟩
        · intro T hT
          simp only [Finset.mem_singleton] at hT
          subst T
          exact ⟨Finset.Subset.rfl, hsmall⟩
        · intro x hx
          exact ⟨S, Finset.mem_singleton_self S, hx⟩
        · simp
      · have hkS : k ≤ S.card := by omega
        obtain ⟨T, hTS, hTcard⟩ := Finset.exists_subset_card_eq hkS
        let R := S \ T
        have hRsub : R ⊆ S := Finset.sdiff_subset
        have hinter : T ∩ S = T := Finset.inter_eq_left.mpr hTS
        have hRcard : R.card = S.card - k := by
          change (S \ T).card = S.card - k
          rw [Finset.card_sdiff, hinter, hTcard]
        have hRlt : R.card < n := by
          rw [hRcard, ← hn]
          omega
        obtain ⟨C, hCsub, hCcover, hCcard⟩ := ih R.card hRlt R rfl
        refine ⟨insert T C, ?_, ?_, ?_⟩
        · intro U hU
          rw [Finset.mem_insert] at hU
          rcases hU with rfl | hU
          · exact ⟨hTS, by omega⟩
          · exact ⟨fun x hx => hRsub ((hCsub U hU).1 hx), (hCsub U hU).2⟩
        · intro x hx
          by_cases hxT : x ∈ T
          · exact ⟨T, Finset.mem_insert_self T C, hxT⟩
          · have hxR : x ∈ R := by simp [R, hx, hxT]
            obtain ⟨U, hUC, hxU⟩ := hCcover x hxR
            exact ⟨U, Finset.mem_insert_of_mem hUC, hxU⟩
        · calc
            (insert T C).card ≤ C.card + 1 := Finset.card_insert_le _ _
            _ ≤ (R.card / k + 1) + 1 := Nat.add_le_add_right hCcard 1
            _ = n / k + 1 := by
              rw [hRcard, ← Nat.div_eq_sub_div hk hkS, hn]

noncomputable def chunks {α : Type*}
    (S : Finset α) (k : ℕ) (hk : 0 < k) : Finset (Finset α) :=
  Classical.choose (exists_chunking S k hk)

lemma chunks_spec {α : Type*}
    (S : Finset α) (k : ℕ) (hk : 0 < k) :
    (∀ T ∈ chunks S k hk, T ⊆ S ∧ T.card ≤ k) ∧
    (∀ x ∈ S, ∃ T ∈ chunks S k hk, x ∈ T) ∧
    (chunks S k hk).card ≤ S.card / k + 1 :=
  Classical.choose_spec (exists_chunking S k hk)

def fiber (A : Finset ℕ) (M t : ℕ) : Finset ℕ :=
  A.filter (fun a => a / M = t)

def residueSet (M : ℕ) (T : Finset ℕ) : Finset ℕ :=
  T.image (fun a => a % M)

def chunkShift (q k : ℕ) (T : Finset ℕ) : ℕ :=
  correctingShift q (enumerate (residueSet (q ^ k) T)) k

def shiftPair (M t g : ℕ) : Finset ℤ :=
  {((t * M : ℕ) : ℤ) - (g : ℤ), (((t + 1) * M : ℕ) : ℤ) - (g : ℤ)}

def coveringBasis (n q k : ℕ) (A : Finset ℕ) (hk : 0 < k) : Finset ℤ :=
  (universalSet q k).map (Nat.castEmbedding : ℕ ↪ ℤ) ∪
    (Finset.range (n / q ^ k + 1)).biUnion fun t =>
      (chunks (fiber A (q ^ k) t) k hk).biUnion fun T =>
        shiftPair (q ^ k) t (chunkShift q k T)

lemma residueSet_card_le (M : ℕ) (T : Finset ℕ) :
    (residueSet M T).card ≤ T.card := by
  exact Finset.card_image_le

lemma mem_residueSet (M : ℕ) {T : Finset ℕ} {a : ℕ} (ha : a ∈ T) :
    a % M ∈ residueSet M T := by
  exact Finset.mem_image.mpr ⟨a, ha, rfl⟩

lemma sum_div_le_div_sum {ι : Type*}
    (s : Finset ι) (f : ι → ℕ) (k : ℕ) :
    ∑ i ∈ s, f i / k ≤ (∑ i ∈ s, f i) / k := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
      simp only [Finset.sum_insert ha]
      exact le_trans (Nat.add_le_add_left ih _) Nat.div_add_div_le_add_div

lemma fiber_card_sum (n M : ℕ) (A : Finset ℕ)
    (hA : ∀ a ∈ A, a ≤ n) :
    ∑ t ∈ Finset.range (n / M + 1), (fiber A M t).card = A.card := by
  have hmap : (A : Set ℕ).MapsTo (fun a => a / M) (Finset.range (n / M + 1)) := by
    intro a ha
    exact Finset.mem_range.mpr
      (Nat.lt_succ_of_le (Nat.div_le_div_right (c := M) (hA a ha)))
  rw [Finset.card_eq_sum_card_fiberwise hmap]
  rfl

lemma chunks_card_sum_le (n M k : ℕ) (hk : 0 < k)
    (A : Finset ℕ) (hA : ∀ a ∈ A, a ≤ n) :
    ∑ t ∈ Finset.range (n / M + 1),
        (chunks (fiber A M t) k hk).card ≤ A.card / k + (n / M + 1) := by
  calc
    ∑ t ∈ Finset.range (n / M + 1), (chunks (fiber A M t) k hk).card
        ≤ ∑ t ∈ Finset.range (n / M + 1), ((fiber A M t).card / k + 1) := by
          gcongr with t ht
          exact (chunks_spec (fiber A M t) k hk).2.2
    _ = (∑ t ∈ Finset.range (n / M + 1), (fiber A M t).card / k) +
          (n / M + 1) := by simp [Finset.sum_add_distrib]
    _ ≤ (∑ t ∈ Finset.range (n / M + 1), (fiber A M t).card) / k +
          (n / M + 1) := by
            gcongr
            exact sum_div_le_div_sum _ _ _
    _ = A.card / k + (n / M + 1) := by rw [fiber_card_sum n M A hA]

lemma coveringBasis_card_le (n q k : ℕ) (hk : 0 < k)
    (A : Finset ℕ) (hA : ∀ a ∈ A, a ≤ n) :
    (coveringBasis n q k A hk).card ≤
      k * q ^ (k - 1) + 2 * (A.card / k + (n / q ^ k + 1)) := by
  let M := q ^ k
  let shifts : Finset ℤ :=
    (Finset.range (n / M + 1)).biUnion fun t =>
      (chunks (fiber A M t) k hk).biUnion fun T =>
        shiftPair M t (chunkShift q k T)
  have hshiftPair (t : ℕ) (T : Finset ℕ) :
      (shiftPair M t (chunkShift q k T)).card ≤ 2 := by
    rw [shiftPair]
    calc
      ({((t * M : ℕ) : ℤ) - (chunkShift q k T : ℤ),
          (((t + 1) * M : ℕ) : ℤ) - (chunkShift q k T : ℤ)} : Finset ℤ).card
          ≤ ({(((t + 1) * M : ℕ) : ℤ) - (chunkShift q k T : ℤ)} : Finset ℤ).card + 1 :=
            Finset.card_insert_le _ _
      _ = 2 := by simp
  have hshifts : shifts.card ≤
      2 * ∑ t ∈ Finset.range (n / M + 1), (chunks (fiber A M t) k hk).card := by
    calc
      shifts.card ≤ ∑ t ∈ Finset.range (n / M + 1),
          ((chunks (fiber A M t) k hk).biUnion fun T =>
            shiftPair M t (chunkShift q k T)).card := Finset.card_biUnion_le
      _ ≤ ∑ t ∈ Finset.range (n / M + 1),
          ∑ T ∈ chunks (fiber A M t) k hk,
            (shiftPair M t (chunkShift q k T)).card := by
              gcongr with t ht
              exact Finset.card_biUnion_le
      _ ≤ ∑ t ∈ Finset.range (n / M + 1),
          ∑ _T ∈ chunks (fiber A M t) k hk, 2 := by
            gcongr with t ht T hT
            exact hshiftPair t T
      _ = 2 * ∑ t ∈ Finset.range (n / M + 1),
          (chunks (fiber A M t) k hk).card := by
            simp only [Finset.sum_const, Nat.nsmul_eq_mul]
            rw [← Finset.sum_mul]
            omega
  have hchunkSum := chunks_card_sum_le n M k hk A hA
  change ∑ t ∈ Finset.range (n / q ^ k + 1),
      (chunks (fiber A (q ^ k) t) k hk).card ≤
        A.card / k + (n / q ^ k + 1) at hchunkSum
  change ((universalSet q k).map (Nat.castEmbedding : ℕ ↪ ℤ) ∪ shifts).card ≤ _
  calc
    ((universalSet q k).map (Nat.castEmbedding : ℕ ↪ ℤ) ∪ shifts).card
        ≤ ((universalSet q k).map (Nat.castEmbedding : ℕ ↪ ℤ)).card + shifts.card :=
          Finset.card_union_le _ _
    _ ≤ k * q ^ (k - 1) +
        2 * ∑ t ∈ Finset.range (n / M + 1),
          (chunks (fiber A M t) k hk).card := by
            apply Nat.add_le_add
            · simpa using universalSet_card_le q k
            · exact hshifts
    _ ≤ k * q ^ (k - 1) + 2 * (A.card / k + (n / q ^ k + 1)) := by
      change k * q ^ (k - 1) +
          2 * ∑ t ∈ Finset.range (n / q ^ k + 1),
            (chunks (fiber A (q ^ k) t) k hk).card ≤ _
      gcongr

lemma residue_cover_with_chunkShift (q k : ℕ) (hq : 1 < q)
    (T : Finset ℕ) (hTcard : T.card ≤ k) {a : ℕ} (ha : a ∈ T) :
    ∃ u ∈ universalSet q k,
      ((a % q ^ k : ℕ) : ℤ) = (u : ℤ) + -(chunkShift q k T : ℤ) ∨
      ((a % q ^ k : ℕ) : ℤ) = (u : ℤ) + ((q ^ k : ℕ) : ℤ) -
        (chunkShift q k T : ℤ) := by
  let R := residueSet (q ^ k) T
  let g := chunkShift q k T
  have hRcard : R.card ≤ k := le_trans (residueSet_card_le _ _) hTcard
  have hres := universal_chunk_residues q k hq R hRcard
  change g < q ^ k ∧ ∀ r ∈ R, (g + r) % q ^ k ∈ universalSet q k at hres
  let r := a % q ^ k
  let u := (g + r) % q ^ k
  have hrR : r ∈ R := mem_residueSet _ ha
  refine ⟨u, hres.2 r hrR, ?_⟩
  change (r : ℤ) = (u : ℤ) + -(g : ℤ) ∨
    (r : ℤ) = (u : ℤ) + (q ^ k : ℕ) - (g : ℤ)
  have hMpos : 0 < q ^ k := Nat.pow_pos (by omega)
  have hrlt : r < q ^ k := Nat.mod_lt _ hMpos
  have hquot : (g + r) / q ^ k ≤ 1 := by
    apply (Nat.div_le_iff_le_mul hMpos).mpr
    omega
  have hdecomp := Nat.mod_add_div (g + r) (q ^ k)
  change u + q ^ k * ((g + r) / q ^ k) = g + r at hdecomp
  interval_cases hcase : (g + r) / q ^ k
  · left
    norm_num [hcase] at hdecomp
    have hc : (u : ℤ) = (g : ℤ) + (r : ℤ) := by exact_mod_cast hdecomp
    omega
  · right
    norm_num [hcase] at hdecomp
    have hc : (u : ℤ) + (q ^ k : ℕ) = (g : ℤ) + (r : ℤ) := by
      exact_mod_cast hdecomp
    omega

lemma coveringBasis_covers (n q k : ℕ) (hq : 1 < q) (hk : 0 < k)
    (A : Finset ℕ) (hA : ∀ a ∈ A, a ≤ n) :
    A.map (Nat.castEmbedding : ℕ ↪ ℤ) ⊆
      coveringBasis n q k A hk + coveringBasis n q k A hk := by
  intro z hz
  obtain ⟨a, ha, rfl⟩ := Finset.mem_map.mp hz
  change (a : ℤ) ∈ coveringBasis n q k A hk + coveringBasis n q k A hk
  let M := q ^ k
  let t := a / M
  have hM : 0 < M := Nat.pow_pos (by omega)
  have htRange : t ∈ Finset.range (n / M + 1) := by
    rw [Finset.mem_range]
    have hdiv := Nat.div_le_div_right (c := M) (hA a ha)
    omega
  have haFiber : a ∈ fiber A M t := by simp [fiber, ha, t]
  obtain ⟨T, hTchunks, haT⟩ :=
    (chunks_spec (fiber A M t) k hk).2.1 a haFiber
  have hTcard : T.card ≤ k := ((chunks_spec (fiber A M t) k hk).1 T hTchunks).2
  obtain ⟨u, huU, hcover⟩ := residue_cover_with_chunkShift q k hq T hTcard haT
  change ((a % M : ℕ) : ℤ) = (u : ℤ) + -(chunkShift q k T : ℤ) ∨
      ((a % M : ℕ) : ℤ) = (u : ℤ) + (M : ℤ) - (chunkShift q k T : ℤ) at hcover
  have huB : (u : ℤ) ∈ coveringBasis n q k A hk := by
    apply Finset.mem_union_left
    exact Finset.mem_map.mpr ⟨u, huU, rfl⟩
  have hdecompNat := Nat.mod_add_div a M
  have hdecomp : (a : ℤ) = ((a % M : ℕ) : ℤ) + (M : ℤ) * (t : ℤ) := by
    have hc := congrArg (fun x : ℕ => (x : ℤ)) hdecompNat
    simp only [Nat.cast_add, Nat.cast_mul] at hc
    simpa only [t] using hc.symm
  rcases hcover with hcover | hcover
  · let s : ℤ := ((t * M : ℕ) : ℤ) - (chunkShift q k T : ℤ)
    have hsPair : s ∈ shiftPair M t (chunkShift q k T) := by
      simp [s, shiftPair]
    have hsB : s ∈ coveringBasis n q k A hk := by
      apply Finset.mem_union_right
      rw [Finset.mem_biUnion]
      refine ⟨t, ?_, ?_⟩
      · simpa only [M] using htRange
      · rw [Finset.mem_biUnion]
        refine ⟨T, ?_, ?_⟩
        · simpa only [M, t] using hTchunks
        · simpa only [M, t] using hsPair
    have heq : (a : ℤ) = (u : ℤ) + s := by
      calc
        (a : ℤ) = ((a % M : ℕ) : ℤ) + (M : ℤ) * (t : ℤ) := hdecomp
        _ = (u : ℤ) + s := by
          rw [hcover]
          simp only [s, Nat.cast_mul]
          ring
    rw [heq]
    exact Finset.add_mem_add huB hsB
  · let s : ℤ := (((t + 1) * M : ℕ) : ℤ) - (chunkShift q k T : ℤ)
    have hsPair : s ∈ shiftPair M t (chunkShift q k T) := by
      simp [s, shiftPair]
    have hsB : s ∈ coveringBasis n q k A hk := by
      apply Finset.mem_union_right
      rw [Finset.mem_biUnion]
      refine ⟨t, ?_, ?_⟩
      · simpa only [M] using htRange
      · rw [Finset.mem_biUnion]
        refine ⟨T, ?_, ?_⟩
        · simpa only [M, t] using hTchunks
        · simpa only [M, t] using hsPair
    have heq : (a : ℤ) = (u : ℤ) + s := by
      calc
        (a : ℤ) = ((a % M : ℕ) : ℤ) + (M : ℤ) * (t : ℤ) := hdecomp
        _ = (u : ℤ) + s := by
          rw [hcover]
          simp only [s, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
          ring
    rw [heq]
    exact Finset.add_mem_add huB hsB

theorem finite_cover (n q k : ℕ) (hq : 1 < q) (hk : 0 < k)
    (A : Finset ℕ) (hA : A ⊆ Finset.Icc 1 n) :
    ∃ B : Finset ℤ,
      A.map (Nat.castEmbedding : ℕ ↪ ℤ) ⊆ B + B ∧
      B.card ≤ k * q ^ (k - 1) + 2 * (A.card / k + (n / q ^ k + 1)) := by
  have hAupper : ∀ a ∈ A, a ≤ n := fun a ha => (Finset.mem_Icc.mp (hA ha)).2
  exact ⟨coveringBasis n q k A hk,
    coveringBasis_covers n q k hq hk A hAupper,
    coveringBasis_card_le n q k hk A hAupper⟩

def rootFloor (e n : ℕ) : ℕ :=
  Nat.findGreatest (fun q => q ^ e ≤ n) n

lemma rootFloor_pow_le (e n : ℕ) (hn : 0 < n) :
    rootFloor e n ^ e ≤ n := by
  rw [rootFloor]
  have hn1 : 1 ≤ n := by omega
  exact Nat.findGreatest_spec (P := fun q => q ^ e ≤ n) (n := n) (m := 1)
    hn1 (by simpa using hn1)

lemma le_rootFloor (e n Q : ℕ) (he : 0 < e) (hQ : 0 < Q)
    (hn : Q ^ e ≤ n) : Q ≤ rootFloor e n := by
  apply Nat.le_findGreatest
  · have hQpow : Q ≤ Q ^ e := by
      have := Nat.pow_le_pow_right hQ (show 1 ≤ e by omega)
      simpa using this
    exact hQpow.trans hn
  · exact hn

lemma lt_succ_rootFloor_pow (e n : ℕ) (he : 0 < e) :
    n < (rootFloor e n + 1) ^ e := by
  let q := rootFloor e n
  by_cases hqn : q + 1 ≤ n
  · exact lt_of_not_ge (Nat.findGreatest_is_greatest (P := fun x => x ^ e ≤ n)
      (show q < q + 1 by omega) hqn)
  · have hnq : n < q + 1 := by omega
    have hbase : q + 1 ≤ (q + 1) ^ e := by
      have := Nat.pow_le_pow_right (show 0 < q + 1 by omega) (show 1 ≤ e by omega)
      simpa using this
    exact hnq.trans_le hbase

lemma rootFloor_scaled_upper (e n : ℕ) (he : 0 < e)
    (hq : 1 ≤ rootFloor e n) :
    n < 2 ^ e * rootFloor e n ^ e := by
  let q := rootFloor e n
  have hbase : q + 1 ≤ 2 * q := by omega
  have hp := Nat.pow_le_pow_left hbase e
  calc
    n < (q + 1) ^ e := lt_succ_rootFloor_pow e n he
    _ ≤ (2 * q) ^ e := hp
    _ = 2 ^ e * q ^ e := by rw [mul_pow]

lemma rootFloor_sqrt_lower (n q k r : ℕ) (hk : 0 < k)
    (hqpow : q ^ (2 * k - 1) ≤ n) (hr : r ^ 2 ≤ q) :
    (r : ℝ) * q ^ (k - 1) ≤ Real.sqrt n := by
  have hsqNat : (r * q ^ (k - 1)) ^ 2 ≤ n := by
    calc
      (r * q ^ (k - 1)) ^ 2 = r ^ 2 * q ^ (2 * (k - 1)) := by ring
      _ ≤ q * q ^ (2 * (k - 1)) := Nat.mul_le_mul_right _ hr
      _ = q ^ (2 * k - 1) := by
        rw [← pow_succ']
        congr 1
        omega
      _ ≤ n := hqpow
  rw [Real.le_sqrt (by positivity) (by positivity)]
  exact_mod_cast hsqNat

lemma quotient_bound_of_scaled_upper (n q k : ℕ) (hk : 0 < k) (hq : 0 < q)
    (hn : n < 2 ^ (2 * k - 1) * q ^ (2 * k - 1)) :
    n / q ^ k ≤ 2 ^ (2 * k - 1) * q ^ (k - 1) := by
  have hden : 0 < q ^ k := Nat.pow_pos hq
  have hlt : n / q ^ k < 2 ^ (2 * k - 1) * q ^ (k - 1) + 1 := by
    rw [Nat.div_lt_iff_lt_mul hden]
    calc
      n < 2 ^ (2 * k - 1) * q ^ (2 * k - 1) := hn
      _ ≤ (2 ^ (2 * k - 1) * q ^ (k - 1) + 1) * q ^ k := by
        have hp : q ^ (2 * k - 1) = q ^ (k - 1) * q ^ k := by
          rw [← pow_add]
          congr 1
          omega
        rw [hp]
        nlinarith [Nat.pow_pos (n := k) hq]
  omega

theorem finite_cover_coarse (n q k : ℕ) (hq : 1 < q) (hk : 0 < k)
    (A : Finset ℕ) (hA : A ⊆ Finset.Icc 1 n)
    (hn : n < 2 ^ (2 * k - 1) * q ^ (2 * k - 1)) :
    ∃ B : Finset ℤ,
      A.map (Nat.castEmbedding : ℕ ↪ ℤ) ⊆ B + B ∧
      B.card ≤ 2 * (A.card / k) +
        (k + 2 ^ (2 * k)) * q ^ (k - 1) + 2 := by
  obtain ⟨B, hcover, hB⟩ := finite_cover n q k hq hk A hA
  have hdiv := quotient_bound_of_scaled_upper n q k hk (by omega) hn
  have hcoeff :
      2 * (2 ^ (2 * k - 1) * q ^ (k - 1)) =
        2 ^ (2 * k) * q ^ (k - 1) := by
    calc
      2 * (2 ^ (2 * k - 1) * q ^ (k - 1)) =
          (2 ^ (2 * k - 1) * 2) * q ^ (k - 1) := by ring
      _ = 2 ^ ((2 * k - 1) + 1) * q ^ (k - 1) := by rw [pow_succ]
      _ = 2 ^ (2 * k) * q ^ (k - 1) := by congr 2; omega
  refine ⟨B, hcover, hB.trans ?_⟩
  rw [Nat.mul_add, Nat.mul_add]
  nlinarith [hdiv]

lemma coarse_bound_to_real (ε : ℝ) (hε : 0 < ε)
    (k r C p a b : ℕ) (hk : 0 < k) (hr : 0 < r) (hp : 0 < p)
    (hklarge : (8 : ℝ) < ε * k)
    (hrlarge : (4 : ℝ) * (C + 2) < ε * r)
    (s : ℝ) (hs : 0 ≤ s) (ha : (a : ℝ) ≤ s)
    (hroot : (r : ℝ) * p ≤ s)
    (hb : b ≤ 2 * (a / k) + C * p + 2) :
    (b : ℝ) ≤ ε * s := by
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  have hrR : (0 : ℝ) < r := by exact_mod_cast hr
  have hcoefK : (2 : ℝ) / k ≤ ε / 4 := by
    rw [div_le_iff₀ hkR]
    nlinarith
  have hcoefR : ((C + 2 : ℕ) : ℝ) / r ≤ ε / 4 := by
    rw [div_le_iff₀ hrR]
    norm_num only [Nat.cast_add, Nat.cast_ofNat] at hrlarge ⊢
    nlinarith
  have hcastDiv : ((a / k : ℕ) : ℝ) ≤ (a : ℝ) / (k : ℝ) := by
    rw [le_div_iff₀ hkR]
    norm_cast
    exact Nat.div_mul_le_self a k
  have hAterm : (2 : ℝ) * (a / k : ℕ) ≤ (ε / 4) * s := by
    calc
      (2 : ℝ) * (a / k : ℕ) ≤ 2 * ((a : ℝ) / (k : ℝ)) := by
        gcongr
      _ ≤ 2 * (s / (k : ℝ)) := by gcongr
      _ = ((2 : ℝ) / k) * s := by ring
      _ ≤ (ε / 4) * s := mul_le_mul_of_nonneg_right hcoefK hs
  have hp1 : 1 ≤ p := by omega
  have hRterm : ((C * p + 2 : ℕ) : ℝ) ≤ (ε / 4) * s := by
    calc
      ((C * p + 2 : ℕ) : ℝ) ≤ (((C + 2) * p : ℕ) : ℝ) := by
        norm_cast
        nlinarith
      _ = (((C + 2 : ℕ) : ℝ) / r) * ((r : ℝ) * p) := by
        norm_num only [Nat.cast_mul, Nat.cast_add, Nat.cast_ofNat]
        field_simp
      _ ≤ (ε / 4) * ((r : ℝ) * p) := by
        gcongr
      _ ≤ (ε / 4) * s := by
        gcongr
  norm_num only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat] at hRterm
  have hbR : (b : ℝ) ≤
      (2 * (a / k) + C * p + 2 : ℕ) := by exact_mod_cast hb
  norm_num only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat] at hbR
  nlinarith [mul_nonneg hε.le hs]

/-- The uniform little-o formulation of Erdős Problem 806. -/
def Erdos806Statement : Prop :=
  ∀ ε : ℝ, 0 < ε →
    ∀ᶠ n : ℕ in Filter.atTop,
      ∀ A : Finset ℕ, A ⊆ Finset.Icc 1 n →
        (A.card : ℝ) ≤ Real.sqrt n →
        ∃ B : Finset ℤ,
          A.map (Nat.castEmbedding : ℕ ↪ ℤ) ⊆ B + B ∧
          (B.card : ℝ) ≤ ε * Real.sqrt n

/-- The affirmative resolution of Erdős Problem 806. -/
theorem erdos_806 : (∀ ε : ℝ, 0 < ε →
  ∀ᶠ n : ℕ in Filter.atTop,
    ∀ A : Finset ℕ, A ⊆ Finset.Icc 1 n →
      (A.card : ℝ) ≤ Real.sqrt n →
      ∃ B : Finset ℤ,
        A.map (Nat.castEmbedding : ℕ ↪ ℤ) ⊆ B + B ∧
        (B.card : ℝ) ≤ ε * Real.sqrt n) := by
  intro ε hε
  obtain ⟨k, hkchoice⟩ := exists_nat_gt ((8 : ℝ) / ε + 1)
  have hkR : (0 : ℝ) < k := by
    have hx : (0 : ℝ) < 8 / ε + 1 := by positivity
    exact hx.trans hkchoice
  have hk : 0 < k := by exact_mod_cast hkR
  have hklarge : (8 : ℝ) < ε * k := by
    have hdiv : (8 : ℝ) / ε < k := by linarith
    have h := (div_lt_iff₀ hε).mp hdiv
    nlinarith
  let C := k + 2 ^ (2 * k)
  obtain ⟨r, hrchoice⟩ := exists_nat_gt
    ((4 : ℝ) * ((C + 2 : ℕ) : ℝ) / ε + 1)
  have hrR : (0 : ℝ) < r := by
    have hx : (0 : ℝ) < (4 : ℝ) * ((C + 2 : ℕ) : ℝ) / ε + 1 := by positivity
    exact hx.trans hrchoice
  have hr : 0 < r := by exact_mod_cast hrR
  have hrlarge : (4 : ℝ) * ((C + 2 : ℕ) : ℝ) < ε * r := by
    have hdiv : (4 : ℝ) * ((C + 2 : ℕ) : ℝ) / ε < r := by linarith
    have h := (div_lt_iff₀ hε).mp hdiv
    nlinarith
  let Q := max 2 (r ^ 2)
  let e := 2 * k - 1
  have hQ : 0 < Q := lt_of_lt_of_le (by omega) (le_max_left 2 (r ^ 2))
  have he : 0 < e := by simp only [e]; omega
  rw [Filter.eventually_atTop]
  refine ⟨Q ^ e, ?_⟩
  intro n hn A hAsub hAcard
  let q := rootFloor e n
  have hqQ : Q ≤ q := le_rootFloor e n Q he hQ hn
  have hq : 1 < q := lt_of_lt_of_le (by
    exact lt_of_lt_of_le (by omega : 1 < 2) (le_max_left 2 (r ^ 2))) hqQ
  have hnpos : 0 < n := by
    have hpowpos : 0 < Q ^ e := Nat.pow_pos hQ
    omega
  have hqpow : q ^ e ≤ n := rootFloor_pow_le e n hnpos
  have hnupper : n < 2 ^ (2 * k - 1) * q ^ (2 * k - 1) := by
    have hu := rootFloor_scaled_upper e n he (by omega : 1 ≤ q)
    simpa only [e, q] using hu
  obtain ⟨B, hcover, hBcard⟩ := finite_cover_coarse n q k hq hk A hAsub hnupper
  have hrq : r ^ 2 ≤ q := (le_max_right 2 (r ^ 2)).trans hqQ
  have hsqrt : (r : ℝ) * q ^ (k - 1) ≤ Real.sqrt n :=
    rootFloor_sqrt_lower n q k r hk (by simpa only [e] using hqpow) hrq
  refine ⟨B, hcover, ?_⟩
  apply coarse_bound_to_real ε hε k r C (q ^ (k - 1)) A.card B.card
  · exact hk
  · exact hr
  · exact Nat.pow_pos (by omega)
  · exact hklarge
  · simpa only [Nat.cast_add, Nat.cast_ofNat] using hrlarge
  · exact Real.sqrt_nonneg _
  · exact hAcard
  · simpa only [Nat.cast_pow] using hsqrt
  · simpa only [C] using hBcard

end
end Erdos806

#print axioms Erdos806.erdos_806
