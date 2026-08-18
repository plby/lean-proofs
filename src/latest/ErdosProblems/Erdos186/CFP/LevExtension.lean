/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
import ErdosProblems.Erdos186.CFP.Elementary

/-!
# Extending an integer interval by a bounded sumset summand

This file isolates the elementary interval-extension step used after an
interval has already appeared in a partial sumset.  If a nonempty finite set
`S` has diameter no larger than the width of an interval contained in `T`,
then `T + S` contains the interval obtained by translating the left endpoint
by `min S` and the right endpoint by `max S`.

In particular, if `S` has at least `n` elements in an interval of `q + 1`
integers and `T` contains an interval of at least `q + 1` integers, then
adding `S` increases the number of guaranteed points by at least `n - 1`.
-/

namespace Erdos186.CFP.LevExtension

open scoped Pointwise

/-- A finite set of integers has at most one more element than its diameter.
This formulation avoids introducing a separate diameter definition. -/
theorem card_le_max'_sub_min'_toNat_add_one (S : Finset ℤ) (hS : S.Nonempty) :
    S.card ≤ (S.max' hS - S.min' hS).toNat + 1 := by
  have hsub : S ⊆ Finset.Icc (S.min' hS) (S.max' hS) := by
    intro x hx
    exact Finset.mem_Icc.mpr
      ⟨Finset.min'_le S x hx, Finset.le_max' S x hx⟩
  calc
    S.card ≤ (Finset.Icc (S.min' hS) (S.max' hS)).card :=
      Finset.card_le_card hsub
    _ = (S.max' hS - S.min' hS).toNat + 1 := by
      rw [Int.card_Icc]
      have hminmax : S.min' hS ≤ S.max' hS :=
        Finset.min'_le S _ (Finset.max'_mem S hS)
      omega

/-- If an integer set has at least `n` elements, its diameter is at least
`n - 1`. -/
theorem card_sub_one_le_max'_sub_min'_toNat (S : Finset ℤ) (hS : S.Nonempty)
    (n : ℕ) (hcard : n ≤ S.card) :
    n - 1 ≤ (S.max' hS - S.min' hS).toNat := by
  have h := card_le_max'_sub_min'_toNat_add_one S hS
  omega

/-- A set contained in `q + 1` consecutive integers has diameter at most
`q`. -/
theorem max'_sub_min'_le_of_subset_Icc {S : Finset ℤ} (hS : S.Nonempty)
    {c : ℤ} {q : ℕ} (hsub : S ⊆ Finset.Icc c (c + (q : ℤ))) :
    S.max' hS - S.min' hS ≤ (q : ℤ) := by
  have hmin := Finset.mem_Icc.mp (hsub (Finset.min'_mem S hS))
  have hmax := Finset.mem_Icc.mp (hsub (Finset.max'_mem S hS))
  omega

/-- Diameter form of interval extension.  The two extreme translates of the
old interval already cover the entire interval between the new extremes. -/
theorem Icc_add_min'_max'_subset_add {S T : Finset ℤ} (hS : S.Nonempty)
    {a b : ℤ} (hdiam : S.max' hS - S.min' hS ≤ b - a)
    (hT : Finset.Icc a b ⊆ T) :
    Finset.Icc (a + S.min' hS) (b + S.max' hS) ⊆ T + S := by
  intro x hx
  have hx' := Finset.mem_Icc.mp hx
  by_cases hleft : x ≤ b + S.min' hS
  · have hxm : x - S.min' hS ∈ Finset.Icc a b := by
      exact Finset.mem_Icc.mpr ⟨by omega, by omega⟩
    exact Finset.mem_add.mpr
      ⟨x - S.min' hS, hT hxm, S.min' hS, Finset.min'_mem S hS, by omega⟩
  · have hxm : x - S.max' hS ∈ Finset.Icc a b := by
      exact Finset.mem_Icc.mpr ⟨by omega, by omega⟩
    exact Finset.mem_add.mpr
      ⟨x - S.max' hS, hT hxm, S.max' hS, Finset.max'_mem S hS, by omega⟩

/-- **Interval extension by a bounded summand.**

Here `m` and `q` count steps, so the interval known to lie in `T` has
`m + 1` points.  If it is at least as wide as the `q + 1`-point interval
containing `S`, and `S` has at least `n` elements, then `T + S` contains an
interval with `m + (n - 1) + 1` points.  Thus the guaranteed point-length
increases by `n - 1`.
-/
theorem interval_extension {S T : Finset ℤ} {a c : ℤ} {m q n : ℕ}
    (hn : 1 ≤ n) (hcard : n ≤ S.card)
    (hSbound : S ⊆ Finset.Icc c (c + (q : ℤ)))
    (hqm : q ≤ m) (hT : Finset.Icc a (a + (m : ℤ)) ⊆ T) :
    ∃ d : ℤ,
      Finset.Icc d (d + ((m + (n - 1) : ℕ) : ℤ)) ⊆ T + S := by
  have hS : S.Nonempty := Finset.card_pos.mp (lt_of_lt_of_le hn hcard)
  let s₀ := S.min' hS
  refine ⟨a + s₀, ?_⟩
  have hdiam : S.max' hS - S.min' hS ≤ (m : ℤ) := by
    have hqdiam := max'_sub_min'_le_of_subset_Icc hS hSbound
    exact hqdiam.trans (by exact_mod_cast hqm)
  have hfull :
      Finset.Icc (a + S.min' hS) (a + (m : ℤ) + S.max' hS) ⊆ T + S := by
    apply Icc_add_min'_max'_subset_add hS
    · omega
    · exact hT
  intro x hx
  apply hfull
  have hx' := Finset.mem_Icc.mp hx
  apply Finset.mem_Icc.mpr
  constructor
  · simpa [s₀] using hx'.1
  · have hspreadNat :
        n - 1 ≤ (S.max' hS - S.min' hS).toNat :=
      card_sub_one_le_max'_sub_min'_toNat S hS n hcard
    have hminmax : S.min' hS ≤ S.max' hS :=
      Finset.min'_le S _ (Finset.max'_mem S hS)
    have hspread : (n - 1 : ℕ) ≤ S.max' hS - S.min' hS := by
      have hspreadCast :
          ((n - 1 : ℕ) : ℤ) ≤
            (((S.max' hS - S.min' hS).toNat : ℕ) : ℤ) := by
        exact_mod_cast hspreadNat
      rw [Int.toNat_of_nonneg (sub_nonneg.mpr hminmax)] at hspreadCast
      exact hspreadCast
    dsimp [s₀] at hx' ⊢
    omega

end Erdos186.CFP.LevExtension
