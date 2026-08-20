/-
Copyright (c) 2026 The Formal Conjectures Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Formal Conjectures Authors
-/

import ErdosProblems.Erdos446.RaneyOccupancy
import Mathlib.Data.Nat.Find

/-!
# Erdős Problem 446: the last failed Smirnov prefix

The complement of the finite Smirnov region is partitioned by its last
failed prefix.  At that prefix the lower barrier is met exactly, and the
remaining suffix satisfies the zero-offset barriers.  This is the finite
first-crossing decomposition behind Pyke's formula.
-/

namespace Erdos446

open Finset
open scoped BigOperators

/-- General offset barrier, separated from the total-mass condition. -/
def SatisfiesSmirnovBarrier {v : ℕ} (u : ℕ) (c : Fin v → ℕ) : Prop :=
  ∀ h : ℕ, 1 ≤ h → h ≤ v → occupancyPrefix c h < u + h

theorem satisfiesSmirnovBarrier_zero {v : ℕ} (c : Fin v → ℕ) :
    SatisfiesSmirnovBarrier 0 c ↔ SatisfiesZeroBarrier c := by
  simp [SatisfiesSmirnovBarrier, SatisfiesZeroBarrier]

theorem mem_smirnovOccupancies_iff_barrier
    {k u v : ℕ} {c : Fin v → ℕ} :
    c ∈ smirnovOccupancies k u v ↔
      c ∈ compositionsOf v k ∧ SatisfiesSmirnovBarrier u c := by
  simp [mem_smirnovOccupancies, mem_compositionsOf,
    SatisfiesSmirnovBarrier]

/-- Largest positive prefix at which the strict Smirnov barrier fails. -/
def lastFailedPrefix {v : ℕ} (u : ℕ) (c : Fin v → ℕ) : ℕ :=
  Nat.findGreatest (fun h ↦ 1 ≤ h ∧ u + h ≤ occupancyPrefix c h) v

theorem lastFailedPrefix_le {v u : ℕ} (c : Fin v → ℕ) :
    lastFailedPrefix u c ≤ v := by
  exact Nat.findGreatest_le v

theorem exists_failedPrefix_of_not_barrier
    {v u : ℕ} {c : Fin v → ℕ}
    (hbad : ¬ SatisfiesSmirnovBarrier u c) :
    ∃ h, 1 ≤ h ∧ h ≤ v ∧ u + h ≤ occupancyPrefix c h := by
  simp only [SatisfiesSmirnovBarrier] at hbad
  push_neg at hbad
  obtain ⟨h, hh, hvh, hfail⟩ := hbad
  exact ⟨h, hh, hvh, hfail⟩

theorem lastFailedPrefix_pos_of_not_barrier
    {v u : ℕ} {c : Fin v → ℕ}
    (hbad : ¬ SatisfiesSmirnovBarrier u c) :
    0 < lastFailedPrefix u c := by
  obtain ⟨h, hh, hvh, hfail⟩ :=
    exists_failedPrefix_of_not_barrier hbad
  have hle : h ≤ lastFailedPrefix u c :=
    Nat.le_findGreatest hvh ⟨hh, hfail⟩
  omega

theorem lastFailedPrefix_spec_of_not_barrier
    {v u : ℕ} {c : Fin v → ℕ}
    (hbad : ¬ SatisfiesSmirnovBarrier u c) :
    1 ≤ lastFailedPrefix u c ∧
      u + lastFailedPrefix u c ≤
        occupancyPrefix c (lastFailedPrefix u c) := by
  obtain ⟨h, hh, hvh, hfail⟩ :=
    exists_failedPrefix_of_not_barrier hbad
  unfold lastFailedPrefix
  exact Nat.findGreatest_spec (P := fun t ↦
    1 ≤ t ∧ u + t ≤ occupancyPrefix c t) hvh ⟨hh, hfail⟩

theorem lastFailedPrefix_lt_length
    {k u v w : ℕ} (hw : 0 < w) (hrel : u + v = k + w)
    {c : Fin v → ℕ} (hc : ∑ i, c i = k)
    (hbad : ¬ SatisfiesSmirnovBarrier u c) :
    lastFailedPrefix u c < v := by
  have hle := lastFailedPrefix_le (u := u) c
  have hterminal : ¬ (u + v ≤ occupancyPrefix c v) := by
    rw [occupancyPrefix_at_length, hc]
    omega
  by_contra hnot
  have heq : lastFailedPrefix u c = v := by omega
  have hspec := lastFailedPrefix_spec_of_not_barrier hbad
  rw [heq] at hspec
  exact hterminal hspec.2

theorem no_failedPrefix_after_last
    {v u : ℕ} {c : Fin v → ℕ} {t : ℕ}
    (hlt : lastFailedPrefix u c < t) (htv : t ≤ v) :
    ¬ (1 ≤ t ∧ u + t ≤ occupancyPrefix c t) := by
  exact Nat.findGreatest_is_greatest hlt htv

/-- The last failed prefix meets the affine barrier exactly. -/
theorem occupancyPrefix_lastFailedPrefix_eq
    {k u v w : ℕ} (hw : 0 < w) (hrel : u + v = k + w)
    {c : Fin v → ℕ} (hc : ∑ i, c i = k)
    (hbad : ¬ SatisfiesSmirnovBarrier u c) :
    occupancyPrefix c (lastFailedPrefix u c) =
      u + lastFailedPrefix u c := by
  let H := lastFailedPrefix u c
  change occupancyPrefix c H = u + H
  have hspec : 1 ≤ H ∧ u + H ≤ occupancyPrefix c H := by
    simpa [H] using lastFailedPrefix_spec_of_not_barrier hbad
  have hHlt : H < v := lastFailedPrefix_lt_length hw hrel hc hbad
  have hnextNot := no_failedPrefix_after_last (c := c)
    (u := u) (t := H + 1) (by omega) (by omega)
  have hnext : occupancyPrefix c (H + 1) < u + (H + 1) := by
    have hpos : 1 ≤ H + 1 := by omega
    omega
  have hmono : occupancyPrefix c H ≤ occupancyPrefix c (H + 1) :=
    occupancyPrefix_mono c (by omega)
  omega

/-- Every nonempty suffix prefix after the last failure has mass smaller
than its length. -/
theorem suffixPrefix_lt_of_lastFailedPrefix
    {k u v w : ℕ} (hw : 0 < w) (hrel : u + v = k + w)
    {c : Fin v → ℕ} (hc : ∑ i, c i = k)
    (hbad : ¬ SatisfiesSmirnovBarrier u c)
    {t : ℕ} (ht : 1 ≤ t)
    (htv : t ≤ v - lastFailedPrefix u c) :
    occupancyPrefix c (lastFailedPrefix u c + t) -
        occupancyPrefix c (lastFailedPrefix u c) < t := by
  let H := lastFailedPrefix u c
  change occupancyPrefix c (H + t) - occupancyPrefix c H < t
  have hHlt : H < v := lastFailedPrefix_lt_length hw hrel hc hbad
  have hsumLe : H + t ≤ v := by dsimp [H] at htv ⊢; omega
  have hnot := no_failedPrefix_after_last (c := c) (u := u)
    (t := H + t) (by omega) hsumLe
  have hupper : occupancyPrefix c (H + t) < u + (H + t) := by
    omega
  have hexact : occupancyPrefix c H = u + H := by
    simpa [H] using occupancyPrefix_lastFailedPrefix_eq hw hrel hc hbad
  have hmono : occupancyPrefix c H ≤ occupancyPrefix c (H + t) :=
    occupancyPrefix_mono c (by omega)
  omega

/-- Converse characterization: an exact failed prefix followed by a
zero-barrier suffix is the last failed prefix. -/
theorem lastFailedPrefix_eq_of_exact_suffix
    {u v h : ℕ} {c : Fin v → ℕ}
    (hh : 1 ≤ h) (hhv : h ≤ v)
    (hexact : occupancyPrefix c h = u + h)
    (hsuffix : ∀ t : ℕ, 1 ≤ t → t ≤ v - h →
      occupancyPrefix c (h + t) - occupancyPrefix c h < t) :
    lastFailedPrefix u c = h := by
  rw [lastFailedPrefix, Nat.findGreatest_eq_iff]
  refine ⟨hhv, fun _hne ↦ ⟨hh, by omega⟩, ?_⟩
  intro n hhn hnv hnfail
  let t := n - h
  have ht : 1 ≤ t := by dsimp [t]; omega
  have htv : t ≤ v - h := by dsimp [t]; omega
  have hsum : h + t = n := by dsimp [t]; omega
  have hsuf := hsuffix t ht htv
  rw [hsum] at hsuf
  have hmono : occupancyPrefix c h ≤ occupancyPrefix c n :=
    occupancyPrefix_mono c (by omega)
  omega

end Erdos446
