/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Copyright (c) 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Multiset.Filter
import Mathlib.Data.Multiset.MapFold
import Mathlib.Data.Multiset.Replicate
import Mathlib.Data.Sym.NatCard
import Mathlib.Tactic

/-!
# Erdős Problem 733: the finite dyadic encoding

This file contains the purely combinatorial part of the proof.  A multiset
whose entries belong to the first `b` dyadic intervals and whose `i`th
interval contains at most `cap i` entries is encoded injectively in

`(i : Fin b) → Sym (Fin (dyadicScale i + 1)) (cap i)`.

In the `i`th coordinate an entry `x` is relabelled by `x - dyadicScale i`.
Unused positions are padded by the extra label `dyadicScale i`.  Filtering
out that extra label recovers each dyadic bucket, so the encoding is
injective.  Stars and bars then gives the product of binomial coefficients.
-/

namespace Erdos733

open Function

noncomputable section

/-- The left endpoint of the `i`th dyadic bucket: `2^(i+1)`. -/
def dyadicScale (i : ℕ) : ℕ :=
  2 ^ (i + 1)

lemma dyadicScale_pos (i : ℕ) : 0 < dyadicScale i := by
  simp [dyadicScale]

/-- Membership in the half-open dyadic interval `[2^(i+1), 2^(i+2))`. -/
def InDyadicBucket (i x : ℕ) : Prop :=
  dyadicScale i ≤ x ∧ x < 2 * dyadicScale i

instance (i x : ℕ) : Decidable (InDyadicBucket i x) :=
  by
    unfold InDyadicBucket
    infer_instance

/-- The part of a multiset lying in the `i`th dyadic bucket. -/
def dyadicBucket (i : ℕ) (M : Multiset ℕ) : Multiset ℕ :=
  M.filter (InDyadicBucket i)

@[simp]
lemma mem_dyadicBucket {i x : ℕ} {M : Multiset ℕ} :
    x ∈ dyadicBucket i M ↔ x ∈ M ∧ InDyadicBucket i x := by
  simp [dyadicBucket]

lemma dyadicBucket_le (i : ℕ) (M : Multiset ℕ) :
    dyadicBucket i M ≤ M := by
  exact Multiset.filter_le _ _

lemma dyadicBucket_card_le (i : ℕ) (M : Multiset ℕ) :
    (dyadicBucket i M).card ≤ M.card := by
  exact Multiset.card_le_card (dyadicBucket_le i M)

/-- Every entry of `M` lies in one of the first `b` dyadic buckets. -/
def SupportedInDyadicBuckets (b : ℕ) (M : Multiset ℕ) : Prop :=
  ∀ x ∈ M, ∃ i : Fin b, InDyadicBucket i x

/-- Multisets supported in the first `b` dyadic buckets and obeying the
prescribed bucket-cardinality caps. -/
def CappedDyadicMultisets (b : ℕ) (cap : Fin b → ℕ) :=
  {M : Multiset ℕ //
    SupportedInDyadicBuckets b M ∧
      ∀ i : Fin b, (dyadicBucket i M).card ≤ cap i}

/-- Relabel a member of the `i`th bucket by its offset from the bucket's
left endpoint.  Its value is strictly below `dyadicScale i`; the final
point of `Fin (dyadicScale i + 1)` is reserved for padding. -/
def dyadicLabel (i x : ℕ) (hx : InDyadicBucket i x) :
    Fin (dyadicScale i + 1) :=
  ⟨x - dyadicScale i, by
    have hlt : x - dyadicScale i < 2 * dyadicScale i - dyadicScale i :=
      Nat.sub_lt_sub_right hx.1 hx.2
    have htwo : 2 * dyadicScale i - dyadicScale i = dyadicScale i := by
      omega
    rw [htwo] at hlt
    exact hlt.trans (Nat.lt_succ_self _)⟩

@[simp]
lemma dyadicLabel_val (i x : ℕ) (hx : InDyadicBucket i x) :
    (dyadicLabel i x hx : ℕ) = x - dyadicScale i :=
  rfl

lemma dyadicLabel_lt (i x : ℕ) (hx : InDyadicBucket i x) :
    (dyadicLabel i x hx : ℕ) < dyadicScale i := by
  have hlt : x - dyadicScale i < 2 * dyadicScale i - dyadicScale i :=
    Nat.sub_lt_sub_right hx.1 hx.2
  have htwo : 2 * dyadicScale i - dyadicScale i = dyadicScale i := by
    omega
  simpa only [dyadicLabel_val, htwo] using hlt

/-- The extra label used to pad a bucket code to its cap. -/
def dyadicDummy (i : ℕ) : Fin (dyadicScale i + 1) :=
  ⟨dyadicScale i, Nat.lt_succ_self _⟩

@[simp]
lemma dyadicDummy_val (i : ℕ) : (dyadicDummy i : ℕ) = dyadicScale i :=
  rfl

/-- Relabel all entries in one dyadic bucket. -/
def relabelDyadicBucket (i : ℕ) (M : Multiset ℕ) :
    Multiset (Fin (dyadicScale i + 1)) :=
  Multiset.pmap (dyadicLabel i) (dyadicBucket i M)
    (fun _x hx ↦ (mem_dyadicBucket.mp hx).2)

@[simp]
lemma card_relabelDyadicBucket (i : ℕ) (M : Multiset ℕ) :
    (relabelDyadicBucket i M).card = (dyadicBucket i M).card := by
  simp [relabelDyadicBucket, Multiset.card_pmap]

lemma relabelDyadicBucket_mem_lt {i : ℕ} {M : Multiset ℕ}
    {y : Fin (dyadicScale i + 1)} (hy : y ∈ relabelDyadicBucket i M) :
    (y : ℕ) < dyadicScale i := by
  rw [relabelDyadicBucket, Multiset.mem_pmap] at hy
  obtain ⟨x, hx, rfl⟩ := hy
  exact dyadicLabel_lt i x _

/-- Inverse arithmetic map for genuine (non-padding) bucket labels. -/
def decodeDyadicLabel (i : ℕ) (y : Fin (dyadicScale i + 1)) : ℕ :=
  dyadicScale i + y

lemma map_decode_relabelDyadicBucket (i : ℕ) (M : Multiset ℕ) :
    (relabelDyadicBucket i M).map (decodeDyadicLabel i) = dyadicBucket i M := by
  rw [relabelDyadicBucket, Multiset.map_pmap]
  let hB : ∀ x ∈ dyadicBucket i M, InDyadicBucket i x :=
    fun _x hx ↦ (mem_dyadicBucket.mp hx).2
  change Multiset.pmap
      (fun x hx ↦ decodeDyadicLabel i (dyadicLabel i x hx))
      (dyadicBucket i M) hB = dyadicBucket i M
  calc
    Multiset.pmap
          (fun x hx ↦ decodeDyadicLabel i (dyadicLabel i x hx))
          (dyadicBucket i M) hB =
        Multiset.pmap (fun x (_ : InDyadicBucket i x) ↦ x)
          (dyadicBucket i M) hB := by
      apply Multiset.pmap_congr
      intro x hx h₁ h₂
      simp only [decodeDyadicLabel, dyadicLabel_val]
      exact Nat.add_sub_of_le h₁.1
    _ = (dyadicBucket i M).map id := by
      exact Multiset.pmap_eq_map _ _ _ hB
    _ = dyadicBucket i M := by
      simpa only using (Multiset.map_id (dyadicBucket i M))

/-- The padded multiset underlying the code of one bucket. -/
def paddedDyadicBucket (i : ℕ) (M : Multiset ℕ) (c : ℕ) :
    Multiset (Fin (dyadicScale i + 1)) :=
  relabelDyadicBucket i M +
    Multiset.replicate (c - (dyadicBucket i M).card) (dyadicDummy i)

lemma card_paddedDyadicBucket {i c : ℕ} {M : Multiset ℕ}
    (hcap : (dyadicBucket i M).card ≤ c) :
    (paddedDyadicBucket i M c).card = c := by
  simp [paddedDyadicBucket, Nat.add_sub_of_le hcap]

/-- The fixed-length symmetric-power code for one capped bucket. -/
def encodeDyadicBucket (i : ℕ) (M : Multiset ℕ) (c : ℕ)
    (hcap : (dyadicBucket i M).card ≤ c) :
    Sym (Fin (dyadicScale i + 1)) c :=
  Sym.mk (paddedDyadicBucket i M c) (card_paddedDyadicBucket hcap)

lemma filter_paddedDyadicBucket (i : ℕ) (M : Multiset ℕ) (c : ℕ) :
    (paddedDyadicBucket i M c).filter
        (fun y : Fin (dyadicScale i + 1) ↦ (y : ℕ) < dyadicScale i) =
      relabelDyadicBucket i M := by
  rw [paddedDyadicBucket, Multiset.filter_add]
  rw [Multiset.filter_eq_self.mpr]
  · rw [Multiset.filter_eq_nil.mpr, add_zero]
    intro y hy
    simp only [Multiset.mem_replicate] at hy
    rcases hy with ⟨-, rfl⟩
    simp
  · intro y hy
    exact relabelDyadicBucket_mem_lt hy

/-- Simultaneously encode all capped dyadic buckets. -/
def encodeCappedDyadicMultiset {b : ℕ} {cap : Fin b → ℕ}
    (M : CappedDyadicMultisets b cap) :
    (i : Fin b) → Sym (Fin (dyadicScale i + 1)) (cap i) :=
  fun i ↦ encodeDyadicBucket i M.1 (cap i) (M.2.2 i)

lemma encodeCappedDyadicMultiset_injective {b : ℕ} {cap : Fin b → ℕ} :
    Function.Injective (encodeCappedDyadicMultiset (b := b) (cap := cap)) := by
  intro M N hcode
  apply Subtype.ext
  have hbuckets : ∀ i : Fin b, dyadicBucket i M.1 = dyadicBucket i N.1 := by
    intro i
    have hi := congrFun hcode i
    have hval : paddedDyadicBucket i M.1 (cap i) =
        paddedDyadicBucket i N.1 (cap i) := by
      exact congrArg Sym.toMultiset hi
    have hrelabel : relabelDyadicBucket i M.1 = relabelDyadicBucket i N.1 := by
      rw [← filter_paddedDyadicBucket i M.1 (cap i),
        ← filter_paddedDyadicBucket i N.1 (cap i), hval]
    have hdecoded := congrArg (Multiset.map (decodeDyadicLabel i)) hrelabel
    simpa only [map_decode_relabelDyadicBucket] using hdecoded
  ext x
  by_cases hx : ∃ i : Fin b, InDyadicBucket i x
  · obtain ⟨i, hi⟩ := hx
    have hcount := congrArg (Multiset.count x) (hbuckets i)
    simpa only [dyadicBucket, Multiset.count_filter_of_pos hi] using hcount
  · have hxM : x ∉ M.1 := by
      intro hxM
      exact hx (M.2.1 x hxM)
    have hxN : x ∉ N.1 := by
      intro hxN
      exact hx (N.2.1 x hxN)
    simp [Multiset.count_eq_zero_of_notMem, hxM, hxN]

/-- Stars and bars for one dyadic coordinate. -/
lemma natCard_dyadicCodeCoordinate (i c : ℕ) :
    Nat.card (Sym (Fin (dyadicScale i + 1)) c) =
      (dyadicScale i + c).choose c := by
  rw [Sym.natCard_sym_eq_choose]
  simp only [Nat.card_fin]
  congr 1
  omega

/-- The central finite counting bound: capped dyadic multisets inject into a
product of symmetric powers, hence their number is bounded by a product of
binomial coefficients. -/
theorem natCard_cappedDyadicMultisets_le (b : ℕ) (cap : Fin b → ℕ) :
    Nat.card (CappedDyadicMultisets b cap) ≤
      ∏ i : Fin b, (dyadicScale i + cap i).choose (cap i) := by
  calc
    Nat.card (CappedDyadicMultisets b cap) ≤
        Nat.card ((i : Fin b) → Sym (Fin (dyadicScale i + 1)) (cap i)) :=
      Nat.card_le_card_of_injective
        (encodeCappedDyadicMultiset (b := b) (cap := cap))
        encodeCappedDyadicMultiset_injective
    _ = ∏ i : Fin b, Nat.card (Sym (Fin (dyadicScale i + 1)) (cap i)) := by
      rw [Nat.card_pi]
    _ = ∏ i : Fin b, (dyadicScale i + cap i).choose (cap i) := by
      apply Finset.prod_congr rfl
      intro i _
      exact natCard_dyadicCodeCoordinate i (cap i)

end

end Erdos733
