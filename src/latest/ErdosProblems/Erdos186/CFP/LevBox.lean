/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
import ErdosProblems.Erdos186.CFP.Elementary

/-!
# A dense two-sumset interval lemma

This is the elementary one-dimensional ``box lemma'' used in the proof of
Lev's iterated-sumset theorem.  If two subsets of integer intervals have
combined density greater than one, their sum contains the indicated central
interval.
-/

namespace Erdos186.CFP.LevBox

open scoped Pointwise

/-- Truncating a set contained in `[0,L]` at an integer `n ≤ L` loses at
most `L-n` elements.  The cardinality inequality is stated in `ℤ` so that
it composes directly with the endpoint estimates in `dense_two_sumset_Icc`.-/
private theorem card_le_card_filter_le_add_sub {L : ℕ} {S : Finset ℤ}
    (hS : S ⊆ Finset.Icc 0 (L : ℤ)) {n : ℤ} (hnL : n ≤ (L : ℤ)) :
    (S.card : ℤ) ≤ ((S.filter fun x ↦ x ≤ n).card : ℤ) + (L : ℤ) - n := by
  classical
  let T := S.filter fun x ↦ ¬x ≤ n
  have hT : T ⊆ Finset.Ioc n (L : ℤ) := by
    intro x hx
    have hx' := Finset.mem_filter.mp hx
    have hxS := Finset.mem_Icc.mp (hS hx'.1)
    exact Finset.mem_Ioc.mpr ⟨lt_of_not_ge hx'.2, hxS.2⟩
  have hTcard : (T.card : ℤ) ≤ (L : ℤ) - n := by
    calc
      (T.card : ℤ) ≤ ((Finset.Ioc n (L : ℤ)).card : ℤ) := by
        exact_mod_cast Finset.card_le_card hT
      _ = (L : ℤ) - n := Int.card_Ioc_of_le n (L : ℤ) hnL
  have hpartition :=
    Finset.card_filter_add_card_filter_not (s := S) (fun x : ℤ ↦ x ≤ n)
  change
    (S.filter fun x ↦ x ≤ n).card + T.card = S.card at hpartition
  omega

/-- If the truncation point is beyond the containing interval, truncation
does not remove any point. -/
private theorem filter_le_eq_self_of_lt {L : ℕ} {S : Finset ℤ}
    (hS : S ⊆ Finset.Icc 0 (L : ℤ)) {n : ℤ} (hLn : (L : ℤ) < n) :
    S.filter (fun x ↦ x ≤ n) = S := by
  apply Finset.filter_eq_self.mpr
  intro x hx
  have hxL := (Finset.mem_Icc.mp (hS hx)).2
  omega

/-- **Dense two-sumset interval lemma.**

Let `S₁ ⊆ [0,L₁]` and `S₂ ⊆ [0,L₂]`, with both lengths positive.  Put
`c = |S₁| + |S₂| - 2`.  If `c ≥ max L₁ L₂`, then every integer from
`L₁+L₂-c` through `c` is in the pointwise sum `S₁ + S₂`.

The proof truncates both sets at a proposed sum `n` and reflects the second
truncation by `b ↦ n-b`.  The two resulting subsets of `[0,n]` have more
than `n+1` elements in total, so the pigeonhole principle gives an
intersection point and hence a representation of `n` as a sum.-/
theorem dense_two_sumset_Icc {L₁ L₂ : ℕ} (hL₁ : 0 < L₁) (hL₂ : 0 < L₂)
    {S₁ S₂ : Finset ℤ}
    (hS₁ : S₁ ⊆ Finset.Icc 0 (L₁ : ℤ))
    (hS₂ : S₂ ⊆ Finset.Icc 0 (L₂ : ℤ))
    (hdense : max L₁ L₂ ≤ S₁.card + S₂.card - 2) :
    Finset.Icc
        ((L₁ : ℤ) + (L₂ : ℤ) -
          ((S₁.card + S₂.card - 2 : ℕ) : ℤ))
        ((S₁.card + S₂.card - 2 : ℕ) : ℤ) ⊆
      S₁ + S₂ := by
  classical
  let c := S₁.card + S₂.card - 2
  have hcL₁ : L₁ ≤ c := (le_max_left L₁ L₂).trans hdense
  have hcL₂ : L₂ ≤ c := (le_max_right L₁ L₂).trans hdense
  have htwo : 2 ≤ S₁.card + S₂.card := by omega
  have hc_cast : (c : ℤ) = (S₁.card : ℤ) + (S₂.card : ℤ) - 2 := by
    simp [c, Nat.cast_sub htwo]
  have hcard₁ : S₁.card ≤ L₁ + 1 := by
    have hmono := Finset.card_le_card hS₁
    have hinterval : ((Finset.Icc (0 : ℤ) (L₁ : ℤ)).card : ℤ) = L₁ + 1 := by
      rw [Int.card_Icc_of_le]
      · norm_num
      · omega
    exact_mod_cast (show (S₁.card : ℤ) ≤ (L₁ : ℤ) + 1 by
      calc
        (S₁.card : ℤ) ≤ ((Finset.Icc (0 : ℤ) (L₁ : ℤ)).card : ℤ) := by
          exact_mod_cast hmono
        _ = (L₁ : ℤ) + 1 := hinterval)
  have hcard₂ : S₂.card ≤ L₂ + 1 := by
    have hmono := Finset.card_le_card hS₂
    have hinterval : ((Finset.Icc (0 : ℤ) (L₂ : ℤ)).card : ℤ) = L₂ + 1 := by
      rw [Int.card_Icc_of_le]
      · norm_num
      · omega
    exact_mod_cast (show (S₂.card : ℤ) ≤ (L₂ : ℤ) + 1 by
      calc
        (S₂.card : ℤ) ≤ ((Finset.Icc (0 : ℤ) (L₂ : ℤ)).card : ℤ) := by
          exact_mod_cast hmono
        _ = (L₂ : ℤ) + 1 := hinterval)
  have hc_upper : c ≤ L₁ + L₂ := by omega
  intro n hn
  have hn' := Finset.mem_Icc.mp hn
  have hn_lower : (L₁ : ℤ) + (L₂ : ℤ) - (c : ℤ) ≤ n := by
    simpa [c] using hn'.1
  have hn_upper : n ≤ (c : ℤ) := by
    simpa [c] using hn'.2
  have hc_upper' : (c : ℤ) ≤ (L₁ : ℤ) + (L₂ : ℤ) := by
    exact_mod_cast hc_upper
  have hn_nonneg : 0 ≤ n := by omega
  let A := S₁.filter fun x ↦ x ≤ n
  let B := S₂.filter fun x ↦ x ≤ n
  let R := B.image fun b ↦ n - b
  let U := Finset.Icc 0 n
  have hAU : A ⊆ U := by
    intro a ha
    have ha' := Finset.mem_filter.mp ha
    have haS := Finset.mem_Icc.mp (hS₁ ha'.1)
    exact Finset.mem_Icc.mpr ⟨haS.1, ha'.2⟩
  have hRU : R ⊆ U := by
    intro x hx
    obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hx
    have hb' := Finset.mem_filter.mp hb
    have hbS := Finset.mem_Icc.mp (hS₂ hb'.1)
    exact Finset.mem_Icc.mpr ⟨by omega, by omega⟩
  have hRcard : R.card = B.card := by
    exact Finset.card_image_of_injective B (fun x y hxy ↦ by omega)
  have hUcard : (U.card : ℤ) = n + 1 := by
    simpa [U] using Int.card_Icc_of_le 0 n (by omega)
  have hlarge : (U.card : ℤ) < (A.card : ℤ) + (B.card : ℤ) := by
    by_cases hnL₁ : n ≤ (L₁ : ℤ)
    · have hA := card_le_card_filter_le_add_sub hS₁ hnL₁
      change (S₁.card : ℤ) ≤ (A.card : ℤ) + (L₁ : ℤ) - n at hA
      by_cases hnL₂ : n ≤ (L₂ : ℤ)
      · have hB := card_le_card_filter_le_add_sub hS₂ hnL₂
        change (S₂.card : ℤ) ≤ (B.card : ℤ) + (L₂ : ℤ) - n at hB
        omega
      · have hB := filter_le_eq_self_of_lt hS₂ (lt_of_not_ge hnL₂)
        change B = S₂ at hB
        have hBcard : (B.card : ℤ) = S₂.card := by rw [hB]
        have hcL₁' : (L₁ : ℤ) ≤ (c : ℤ) := by exact_mod_cast hcL₁
        omega
    · have hA := filter_le_eq_self_of_lt hS₁ (lt_of_not_ge hnL₁)
      change A = S₁ at hA
      have hAcard : (A.card : ℤ) = S₁.card := by rw [hA]
      by_cases hnL₂ : n ≤ (L₂ : ℤ)
      · have hB := card_le_card_filter_le_add_sub hS₂ hnL₂
        change (S₂.card : ℤ) ≤ (B.card : ℤ) + (L₂ : ℤ) - n at hB
        have hcL₂' : (L₂ : ℤ) ≤ (c : ℤ) := by exact_mod_cast hcL₂
        omega
      · have hB := filter_le_eq_self_of_lt hS₂ (lt_of_not_ge hnL₂)
        change B = S₂ at hB
        have hBcard : (B.card : ℤ) = S₂.card := by rw [hB]
        omega
  have hinter : (A ∩ R).Nonempty := by
    apply Finset.inter_nonempty_of_card_lt_card_add_card hAU hRU
    rw [hRcard]
    exact_mod_cast hlarge
  obtain ⟨a, ha⟩ := hinter
  have ha' := Finset.mem_inter.mp ha
  have haA := Finset.mem_filter.mp ha'.1
  obtain ⟨b, hbB, hab⟩ := Finset.mem_image.mp ha'.2
  have hb := Finset.mem_filter.mp hbB
  simp only [Finset.mem_add]
  refine ⟨a, haA.1, b, hb.1, ?_⟩
  omega

end Erdos186.CFP.LevBox
