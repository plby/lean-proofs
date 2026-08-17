/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/
import ErdosProblems.Erdos54.RobustBlock
import ErdosProblems.Erdos55.Core

/-!
# Robust blocks for an arbitrary number of colors

The two-color development for Erdős Problem 54 proves the full finite CFP
modular-growth estimate, but packages its last sampling step at twice the
robustness threshold.  Here the same sample is enlarged by a factor `r`.
Every `640*q`-element subblock still contains the required interval, while a
pigeonhole argument guarantees that an `r`-coloring supplies such a subblock.
-/

namespace Erdos55

open scoped BigOperators
open Filter

/-- The arbitrary-color version of the integer-rounded CFP robust block. -/
def IsRRobustBlock (r x q : ℕ) (S : Finset ℕ) : Prop :=
  S ⊆ Finset.Ico x (2 * x) ∧
  S.card = 1280 * r * q ∧
  ∀ T : Finset ℕ, T ⊆ S → 640 * q ≤ T.card →
    Erdos54.CoversInterval T (160 * q * x) (560 * q * x)

theorem universallyModularGood_mono_carrier
    {q h : ℕ} {S₀ S : Finset ℕ}
    (hsub : S₀ ⊆ S) (hgood : Erdos54.UniversallyModularGood q h S) :
    Erdos54.UniversallyModularGood q h S₀ := by
  intro P hPS₀ hPcard m hm
  apply hgood P (hPS₀.trans hsub) hPcard m
  exact Finset.mem_sdiff.mpr
    ⟨hsub (Finset.mem_sdiff.mp hm).1, Finset.mem_sdiff.mp hm |>.2⟩

/-- The deterministic forty-piece argument works inside a chosen
`1280*q`-element subblock of the larger sample. -/
theorem isRRobustBlock_of_modularGood
    (hlev : Erdos54.FortySetIntervalPrinciple)
    {r x w q : ℕ} {S : Finset ℕ}
    (hr : 1 ≤ r) (hx : 200 ≤ x) (hq : 1 ≤ q) (hw : 17 ≤ w)
    (hSrough : S ⊆ Erdos54.roughNumbersAt x w)
    (hScard : S.card = 1280 * r * q)
    (hgood : Erdos54.UniversallyModularGood q (x / 4) S) :
    IsRRobustBlock r x q S := by
  classical
  have hSIco : S ⊆ Finset.Ico x (2 * x) := by
    intro a ha
    have hrough := Erdos54.mem_roughNumbersAt.mp (hSrough ha)
    exact Finset.mem_Ico.mpr ⟨hrough.1, hrough.2.1⟩
  refine ⟨hSIco, hScard, ?_⟩
  intro T hTS hTcard
  obtain ⟨T₀, hT₀T, hT₀card⟩ := Finset.exists_subset_card_eq hTcard
  have hsmall : T₀.card ≤ 1280 * q := by rw [hT₀card]; omega
  have hlarge : 1280 * q ≤ S.card := by rw [hScard]; nlinarith
  obtain ⟨S₀, hT₀S₀, hS₀S, hS₀card⟩ :=
    Finset.exists_subsuperset_card_eq (hT₀T.trans hTS) hsmall hlarge
  have hS₀rough : S₀ ⊆ Erdos54.roughNumbersAt x w := hS₀S.trans hSrough
  have hS₀good : Erdos54.UniversallyModularGood q (x / 4) S₀ :=
    universallyModularGood_mono_carrier hS₀S hgood
  have hrobust := Erdos54.isRobustBlock_of_modularGood hlev hx hq hw
    hS₀rough hS₀card hS₀good
  exact (hrobust.2.2 T₀ hT₀S₀ (by rw [hT₀card])).mono hT₀T

/-- A crude coordinate/modulus bound for a sample enlarged by the fixed
factor `r`.  The threshold may depend on `r`, exactly as allowed in the CFP
construction for each fixed number of colors. -/
theorem r_coordinate_modulus_factor_le_logScale_power
    {r x q u : ℕ} (hr : 1 ≤ r) (hq : q ≤ 6 * u) (hxpow : x ≤ 3 ^ u)
    (hlarge : 2 ^ (4 * (7680 * r + 3)) ≤ u) :
    2 * Fintype.card
        (Erdos54.CoordinateSubset (1280 * r * q) q × ↑(Erdos54.roughNumbers x)) ≤
      u ^ (u / 2) := by
  have hu : 2 ≤ u := by
    have hexp : 1 ≤ 4 * (7680 * r + 3) := by omega
    have : 2 ≤ 2 ^ (4 * (7680 * r + 3)) := by
      simpa using Nat.pow_le_pow_right (by omega : 1 ≤ 2) hexp
    omega
  have hrough : (Erdos54.roughNumbers x).card ≤ x := by
    calc
      (Erdos54.roughNumbers x).card ≤ (Finset.Ico x (2 * x)).card :=
        Finset.card_le_card fun n hn ↦ Finset.mem_Ico.mpr
          ⟨(Erdos54.mem_roughNumbers.mp hn).1,
            (Erdos54.mem_roughNumbers.mp hn).2.1⟩
      _ = x := by simp; omega
  have hxTwo : x ≤ 2 ^ (2 * u) := by
    calc
      x ≤ 3 ^ u := hxpow
      _ ≤ 4 ^ u := Nat.pow_le_pow_left (by omega) _
      _ = 2 ^ (2 * u) := by rw [pow_mul]; norm_num
  have hcoord := Erdos54.card_coordinateSubset_le (1280 * r * q) q
  have hN : 1280 * r * q ≤ 7680 * r * u := by nlinarith
  have hindex :
      Fintype.card
          (Erdos54.CoordinateSubset (1280 * r * q) q ×
            ↑(Erdos54.roughNumbers x)) ≤
        2 ^ ((7680 * r + 2) * u) := by
    rw [Fintype.card_prod, Fintype.card_coe]
    calc
      Fintype.card (Erdos54.CoordinateSubset (1280 * r * q) q) *
          (Erdos54.roughNumbers x).card ≤ 2 ^ (1280 * r * q) * x :=
        Nat.mul_le_mul hcoord hrough
      _ ≤ 2 ^ (7680 * r * u) * 2 ^ (2 * u) :=
        Nat.mul_le_mul (Nat.pow_le_pow_right (by omega) hN) hxTwo
      _ = 2 ^ ((7680 * r + 2) * u) := by
        rw [← pow_add]
        congr 1
        ring
  have htwoIndex :
      2 * Fintype.card
          (Erdos54.CoordinateSubset (1280 * r * q) q ×
            ↑(Erdos54.roughNumbers x)) ≤
        2 ^ ((7680 * r + 3) * u) := by
    calc
      2 * Fintype.card
          (Erdos54.CoordinateSubset (1280 * r * q) q ×
            ↑(Erdos54.roughNumbers x)) ≤
          2 * 2 ^ ((7680 * r + 2) * u) := Nat.mul_le_mul_left 2 hindex
      _ = 2 ^ ((7680 * r + 2) * u + 1) := by rw [pow_add]; simp [Nat.mul_comm]
      _ ≤ 2 ^ ((7680 * r + 3) * u) :=
        Nat.pow_le_pow_right (by omega) (by nlinarith)
  have hexponent :
      (7680 * r + 3) * u ≤ 4 * (7680 * r + 3) * (u / 2) := by
    have : u ≤ 4 * (u / 2) := by omega
    nlinarith
  calc
    2 * Fintype.card
        (Erdos54.CoordinateSubset (1280 * r * q) q ×
          ↑(Erdos54.roughNumbers x)) ≤
        2 ^ ((7680 * r + 3) * u) := htwoIndex
    _ ≤ 2 ^ (4 * (7680 * r + 3) * (u / 2)) :=
      Nat.pow_le_pow_right (by omega) hexponent
    _ = (2 ^ (4 * (7680 * r + 3))) ^ (u / 2) := by rw [pow_mul]
    _ ≤ u ^ (u / 2) := Nat.pow_le_pow_left hlarge _

end Erdos55
