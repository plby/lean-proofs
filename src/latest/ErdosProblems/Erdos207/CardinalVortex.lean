/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.InitialVortexTypicality
import Mathlib.Order.Interval.Finset.Fin

/-!
# Explicit gradual vortices on `Fin n`

The outer part of level `i` is an initial interval of prescribed size, and
the fixed absorber root `X` is adjoined at every level.  This gives a nested
vortex without requiring the embedded absorber root itself to be an initial
interval.  Exact lower and upper cardinal bounds are recorded for later
scalar estimates.
-/

namespace Erdos207

open Finset

noncomputable section

/-- A prefix-sized vortex containing a fixed terminal set.  The zeroth level
is the ambient set.  At every positive level we adjoin `X` to the initial
interval of length `sizes i`. -/
def cardinalVortex {n ell : ℕ} (X : Finset (Fin n))
    (sizes : Fin (ell + 1) → ℕ)
    (hsmall : ∀ i, i ≠ 0 → sizes i < n)
    (hanti : Antitone sizes) : Vortex (Fin n) ell where
  U i := if hi : i = 0 then univ
    else X ∪ Iio (⟨sizes i, hsmall i hi⟩ : Fin n)
  root := by simp
  antitone := by
    intro i j hij
    by_cases hi : i = 0
    · subst i
      simp
    have hj : j ≠ 0 := by
      intro hj
      subst j
      apply hi
      apply Fin.ext
      exact Nat.eq_zero_of_le_zero hij
    simp only [hi, hj, ↓reduceDIte]
    apply union_subset_union_right
    apply Finset.Iio_subset_Iio
    exact hanti hij

@[simp]
theorem cardinalVortex_U_zero {n ell : ℕ} (X : Finset (Fin n))
    (sizes : Fin (ell + 1) → ℕ)
    (hsmall : ∀ i, i ≠ 0 → sizes i < n)
    (hanti : Antitone sizes) :
    (cardinalVortex X sizes hsmall hanti).U 0 = univ := by
  simp [cardinalVortex]

theorem cardinalVortex_U_of_ne_zero {n ell : ℕ} (X : Finset (Fin n))
    (sizes : Fin (ell + 1) → ℕ)
    (hsmall : ∀ i, i ≠ 0 → sizes i < n)
    (hanti : Antitone sizes) {i : Fin (ell + 1)} (hi : i ≠ 0) :
    (cardinalVortex X sizes hsmall hanti).U i =
      X ∪ Iio (⟨sizes i, hsmall i hi⟩ : Fin n) := by
  simp [cardinalVortex, hi]

theorem subset_cardinalVortex_U {n ell : ℕ} (X : Finset (Fin n))
    (sizes : Fin (ell + 1) → ℕ)
    (hsmall : ∀ i, i ≠ 0 → sizes i < n)
    (hanti : Antitone sizes) (i : Fin (ell + 1)) :
    X ⊆ (cardinalVortex X sizes hsmall hanti).U i := by
  by_cases hi : i = 0
  · subst i
    simp
  · rw [cardinalVortex_U_of_ne_zero X sizes hsmall hanti hi]
    exact subset_union_left

theorem sizes_le_card_cardinalVortex_U {n ell : ℕ}
    (X : Finset (Fin n)) (sizes : Fin (ell + 1) → ℕ)
    (hsmall : ∀ i, i ≠ 0 → sizes i < n)
    (hanti : Antitone sizes) {i : Fin (ell + 1)} (hi : i ≠ 0) :
    sizes i ≤ ((cardinalVortex X sizes hsmall hanti).U i).card := by
  rw [cardinalVortex_U_of_ne_zero X sizes hsmall hanti hi]
  have hsub : Iio (⟨sizes i, hsmall i hi⟩ : Fin n) ⊆
      X ∪ Iio (⟨sizes i, hsmall i hi⟩ : Fin n) := subset_union_right
  simpa only [Fin.card_Iio] using card_le_card hsub

theorem card_cardinalVortex_U_le {n ell : ℕ}
    (X : Finset (Fin n)) (sizes : Fin (ell + 1) → ℕ)
    (hsmall : ∀ i, i ≠ 0 → sizes i < n)
    (hanti : Antitone sizes) {i : Fin (ell + 1)} (hi : i ≠ 0) :
    ((cardinalVortex X sizes hsmall hanti).U i).card ≤ X.card + sizes i := by
  rw [cardinalVortex_U_of_ne_zero X sizes hsmall hanti hi]
  simpa only [Fin.card_Iio] using
    card_union_le X (Iio (⟨sizes i, hsmall i hi⟩ : Fin n))

/-- If the final prescribed prefix size is zero, the terminal vortex level
is exactly the absorber root. -/
theorem cardinalVortex_U_last {n ell : ℕ} (hell : 0 < ell)
    (X : Finset (Fin n)) (sizes : Fin (ell + 1) → ℕ)
    (hsmall : ∀ i, i ≠ 0 → sizes i < n)
    (hanti : Antitone sizes) (hlast : sizes (Fin.last ell) = 0) :
    (cardinalVortex X sizes hsmall hanti).U (Fin.last ell) = X := by
  have hne : (Fin.last ell : Fin (ell + 1)) ≠ 0 := by
    intro hzero
    have := congrArg Fin.val hzero
    simp only [Fin.val_last, Fin.val_zero] at this
    omega
  rw [cardinalVortex_U_of_ne_zero X sizes hsmall hanti hne]
  have hIio : Iio
      (⟨sizes (Fin.last ell), hsmall (Fin.last ell) hne⟩ : Fin n) = ∅ := by
    ext x
    constructor
    · intro hx
      have hxval : x.val < sizes (Fin.last ell) := by
        have hxfin : x <
            (⟨sizes (Fin.last ell), hsmall (Fin.last ell) hne⟩ : Fin n) := by
          simpa only [Finset.mem_Iio] using hx
        exact hxfin
      rw [hlast] at hxval
      omega
    · intro hx
      have : False := by simpa using hx
      exact this.elim
  simp only [hIio, union_empty]

theorem cardinalVortex_nonempty {n ell : ℕ} (X : Finset (Fin n))
    (sizes : Fin (ell + 1) → ℕ)
    (hsmall : ∀ i, i ≠ 0 → sizes i < n)
    (hanti : Antitone sizes) (hX : X.Nonempty) :
    ∀ i, ((cardinalVortex X sizes hsmall hanti).U i).Nonempty := by
  intro i
  exact hX.mono (subset_cardinalVortex_U X sizes hsmall hanti i)

end

end Erdos207
