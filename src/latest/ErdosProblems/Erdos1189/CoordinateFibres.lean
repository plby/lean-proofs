/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Counting prime-adic coordinate fibres, including arbitrary non-arithmetic orders.
Informal source: BBMST Section 7.1.
Formal author: OpenAI Codex.
-/

import ErdosProblems.Erdos1189.ProfileEntropy
import ErdosProblems.Erdos1189.PrimeGrid

namespace Erdos1189

open Finset

def fibreExponent {N : ℕ} (S : Finset (PrimeCoordinate N)) (p : ℕ) : ℕ :=
  (S.filter (fun c => c.1.val = p)).card

lemma fibreExponent_eq {N : ℕ} (S : Finset (PrimeCoordinate N)) (p : N.primeFactors) :
    fibreExponent S p = (univ.filter (fun e : Fin (N.factorization p) =>
      (⟨p, e⟩ : PrimeCoordinate N) ∈ S)).card := by
  classical
  have hset : S.filter (fun c => c.1.val = p.val) =
      (univ.filter (fun e : Fin (N.factorization p) =>
        (⟨p, e⟩ : PrimeCoordinate N) ∈ S)).image (fun e => (⟨p, e⟩ : PrimeCoordinate N)) := by
    ext c
    constructor
    · intro hc
      obtain ⟨hcS, hcp⟩ := mem_filter.mp hc
      obtain ⟨p', e⟩ := c
      have hpp : p' = p := Subtype.ext hcp
      subst p'
      exact mem_image.mpr ⟨e, mem_filter.mpr ⟨mem_univ _, hcS⟩, rfl⟩
    · intro hc
      obtain ⟨e, he, rfl⟩ := mem_image.mp hc
      exact mem_filter.mpr ⟨(mem_filter.mp he).2, rfl⟩
  rw [fibreExponent, hset, card_image_of_injective]
  intro e f hef
  exact eq_of_heq (Sigma.mk.inj hef).2

lemma card_fin_lt_of_le {n r : ℕ} (hr : r ≤ n) :
    (univ.filter (fun e : Fin n => e.val < r)).card = r := by
  have hset : (univ.filter (fun e : Fin n => e.val < r)).image Fin.val = range r := by
    ext e
    constructor
    · intro he
      obtain ⟨f, hf, rfl⟩ := mem_image.mp he
      exact mem_range.mpr (mem_filter.mp hf).2
    · intro he
      have her := mem_range.mp he
      exact mem_image.mpr ⟨⟨e, her.trans_le hr⟩, mem_filter.mpr ⟨mem_univ _, her⟩, rfl⟩
  have hcard := congrArg Finset.card hset
  simpa only [card_image_of_injective _ Fin.val_injective, card_range] using hcard

lemma fibreExponent_congruenceBox {N d a : ℕ} (hN : N ≠ 0) (hd : d ∣ N)
    (p : N.primeFactors) :
    fibreExponent (Grid.fixed (congruenceBox N d a)) p = d.factorization p := by
  rw [fibreExponent_eq]
  simp only [mem_fixed_congruenceBox]
  exact card_fin_lt_of_le ((Nat.factorization_le_iff_dvd
    (ne_zero_of_dvd_ne_zero hN hd) hN).mpr hd p)

lemma fibreExponent_le_factorization {N : ℕ} (S : Finset (PrimeCoordinate N))
    (p : N.primeFactors) : fibreExponent S p ≤ N.factorization p := by
  rw [fibreExponent_eq]
  exact (card_filter_le _ _).trans (by simp)

lemma fibreExponent_mono {N : ℕ} {S T : Finset (PrimeCoordinate N)} (hST : S ⊆ T) (p : ℕ) :
    fibreExponent S p ≤ fibreExponent T p := card_le_card (filter_subset_filter _ hST)

lemma fibreExponent_union_le {N : ℕ} (S T : Finset (PrimeCoordinate N)) (p : ℕ) :
    fibreExponent (S ∪ T) p ≤ fibreExponent S p + fibreExponent T p := by
  unfold fibreExponent
  rw [filter_union]
  exact card_union_le _ _

lemma fibreExponent_le_card {N : ℕ} (S : Finset (PrimeCoordinate N)) (p : ℕ) :
    fibreExponent S p ≤ S.card := card_filter_le _ _

lemma profileWeight_fibreExponent_on {N : ℕ} (S : Finset (PrimeCoordinate N)) (P : Finset ℕ) :
    profileWeight P (fibreExponent S) =
      ∑ c ∈ S with c.1.val ∈ P, (coordinateSize c - 1) := by
  have h := sum_fiberwise_eq_sum_filter S P (fun c => c.1.val)
    (fun c => coordinateSize c - 1)
  rw [← h]
  apply sum_congr rfl
  intro p _
  unfold fibreExponent
  calc
    _ = ∑ _c ∈ S.filter (fun c => c.1.val = p), (p - 1) := by simp
    _ = _ := sum_congr rfl fun c hc =>
      congrArg (fun p : ℕ => p - 1) (mem_filter.mp hc).2.symm

lemma profileWeight_fibreExponent {N : ℕ} (S : Finset (PrimeCoordinate N)) :
    profileWeight N.primeFactors (fibreExponent S) = ∑ c ∈ S, (coordinateSize c - 1) := by
  rw [profileWeight_fibreExponent_on]
  have hf : S.filter (fun c => c.1.val ∈ N.primeFactors) = S :=
    filter_eq_self.mpr fun c _ => c.1.property
  rw [hf]

lemma fibreExponent_univ {N : ℕ} (p : N.primeFactors) :
    fibreExponent (univ : Finset (PrimeCoordinate N)) p = N.factorization p := by
  rw [fibreExponent_eq]
  simp

end Erdos1189
