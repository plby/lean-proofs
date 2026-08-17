/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/
import ErdosProblems.Erdos55.WindowClassification

/-!
# Omitted integers at every selected weak scale

The final coloring makes precisely the union of the sparse selected windows
blue and everything else red, retaining the rank hue as the other color
coordinate.  A red monochromatic sum cannot enter the target interval because
the scale is not red-strong.  The blue sums form a finset smaller than that
interval, so at least one target integer is not monochromatically represented.
-/

namespace Erdos55

open scoped BigOperators

noncomputable def subtypeValues {A : Set ℕ} (T : Finset A) : Finset ℕ :=
  T.map (Function.Embedding.subtype (fun a ↦ a ∈ A))

@[simp] theorem mem_subtypeValues {A : Set ℕ} {T : Finset A} {a : ℕ} :
    a ∈ subtypeValues T ↔ ∃ x ∈ T, (x : ℕ) = a := by
  simp [subtypeValues]

theorem sum_subtypeValues {A : Set ℕ} (T : Finset A) :
    (∑ a ∈ subtypeValues T, a) = ∑ a ∈ T, (a : ℕ) := by
  rw [subtypeValues, Finset.sum_map]
  rfl

theorem red_sum_not_mem_target {A : Set ℕ} (hA : A.Infinite)
    {h s : ℕ} (hs : s < h) {J : ℕ → ℕ} {n : ℕ} {T : Finset ℕ}
    (hweak : ¬RedStrong A h (J n))
    (hTA : ∀ a ∈ T, a ∈ A)
    (hThue : ∀ a ∈ T, hueIn A h a = s)
    (hTred : ∀ a ∈ T, ¬selectedBlue A J a) :
    (∑ a ∈ T, a) ∉ targetInterval (J n) := by
  intro htarget
  have hbds := Finset.mem_Ioc.mp htarget
  have ha_le_sum : ∀ a ∈ T, a ≤ ∑ x ∈ T, x := by
    intro a ha
    exact Finset.single_le_sum (s := T) (f := fun x : ℕ ↦ x)
      (fun x _ ↦ Nat.zero_le x) ha
  have hTprefix : T ⊆ rankHuePrefix A h s (2 ^ J n) := by
    intro a ha
    apply (mem_rankHuePrefix_iff hA).mpr
    refine ⟨hTA a ha, ?_, hThue a ha⟩
    by_contra halow
    apply hTred a ha
    refine ⟨n, (mem_blueWindow_iff hA).mpr ⟨hTA a ha, ?_, ?_⟩⟩
    · exact Nat.lt_of_not_ge halow
    · exact (ha_le_sum a ha).trans hbds.2
  have hsumPrefix : (∑ a ∈ T, a) ≤
      ∑ a ∈ rankHuePrefix A h s (2 ^ J n), a := by
    apply Finset.sum_le_sum_of_subset_of_nonneg hTprefix
    intro a _ _
    exact Nat.zero_le a
  have hpref : (∑ a ∈ rankHuePrefix A h s (2 ^ J n), a) ≤
      redThreshold (J n) := by
    by_contra hnot
    apply hweak
    exact ⟨s, hs, Nat.lt_of_not_ge hnot⟩
  omega

noncomputable def sparseObstructionColor (A : Set ℕ) (h r : ℕ)
    (hh : 0 < h) (hhr : 2 * h ≤ r)
    (hunbounded : ∀ b, ∃ j, b < j ∧ WeakScale A h j) : A → Fin r :=
  let J := sparseWeakSequence hunbounded A h
  hueBitColorCast A h r hh hhr (selectedBlueBit A J)

theorem sparseWeakSequence_gt_sixteen {A : Set ℕ} {h : ℕ} (hh : 0 < h)
    (hunbounded : ∀ b, ∃ j, b < j ∧ WeakScale A h j) (n : ℕ) :
    16 < sparseWeakSequence hunbounded A h n := by
  have hzero := sparseWeakSequence_zero_gt hunbounded A h
  have hmono := (sparseWeakSequence_strictMono hunbounded A h).monotone
    (Nat.zero_le n)
  omega

theorem exists_omitted_at_sparseWeakSequence {A : Set ℕ} (hA : A.Infinite)
    {h r : ℕ} (hh : 0 < h) (hhr : 2 * h ≤ r)
    (hunbounded : ∀ b, ∃ j, b < j ∧ WeakScale A h j) (n : ℕ) :
    ∃ m ∈ targetInterval (sparseWeakSequence hunbounded A h n),
      ¬IsMonochromaticSum A
        (sparseObstructionColor A h r hh hhr hunbounded) m := by
  classical
  let J := sparseWeakSequence hunbounded A h
  let j := J n
  have hJ : StrictMono J := sparseWeakSequence_strictMono hunbounded A h
  have hjbig : 16 < j := sparseWeakSequence_gt_sixteen hh hunbounded n
  have hweak : WeakScale A h j := sparseWeakSequence_mem hunbounded A h n
  have hblueSmall : 16 * (bluePossible A h J n).card < j * 2 ^ j := by
    exact card_bluePossible_mul_sixteen_lt hA hunbounded hweak.2
  have htargetLarge : j * 2 ^ j < 16 * (targetInterval j).card :=
    scale_lt_sixteen_mul_target_card hjbig
  have hcard : (bluePossible A h J n).card < (targetInterval j).card := by
    omega
  obtain ⟨m, hmTarget, hmBlue⟩ :
      ∃ m, m ∈ targetInterval j ∧ m ∉ bluePossible A h J n := by
    by_contra hnone
    have hsub : targetInterval j ⊆ bluePossible A h J n := by
      intro m hm
      by_contra hmnot
      exact hnone ⟨m, hm, hmnot⟩
    exact (not_le_of_gt hcard) (Finset.card_le_card hsub)
  refine ⟨m, hmTarget, ?_⟩
  intro hmonoSum
  obtain ⟨i, T, hcolor, hsum⟩ := hmonoSum
  have hmpos : 0 < m := by
    have := (Finset.mem_Ioc.mp hmTarget).1
    omega
  have hTnonempty : T.Nonempty := by
    by_contra hempty
    rw [Finset.not_nonempty_iff_eq_empty.mp hempty] at hsum
    simp at hsum
    omega
  obtain ⟨a₀, ha₀T⟩ := hTnonempty
  let V := subtypeValues T
  let s := hueIn A h a₀
  let bit := selectedBlueBit A J a₀
  have hs : s < h := hueIn_lt hh
  have hdecode : ∀ a ∈ T,
      hueIn A h a = s ∧ selectedBlueBit A J a = bit := by
    intro a haT
    apply (hueBitColorCast_eq_iff hh hhr (selectedBlueBit A J) a a₀).mp
    exact (hcolor a haT).trans (hcolor a₀ ha₀T).symm
  have hVA : ∀ a ∈ V, a ∈ A := by
    intro a ha
    obtain ⟨x, hxT, rfl⟩ := mem_subtypeValues.mp ha
    exact x.property
  have hVhue : ∀ a ∈ V, hueIn A h a = s := by
    intro a ha
    obtain ⟨x, hxT, rfl⟩ := mem_subtypeValues.mp ha
    exact (hdecode x hxT).1
  have hVbit : ∀ a ∈ V, selectedBlueBit A J a = bit := by
    intro a ha
    obtain ⟨x, hxT, rfl⟩ := mem_subtypeValues.mp ha
    exact (hdecode x hxT).2
  have hsumV : (∑ a ∈ V, a) = m := by
    rw [show (∑ a ∈ V, a) = ∑ a ∈ T, (a : ℕ) by
      exact sum_subtypeValues T]
    exact hsum
  cases hbit : bit with
  | false =>
      have hVred : ∀ a ∈ V, ¬selectedBlue A J a := by
        intro a ha
        rw [← selectedBlueBit_eq_false]
        exact (hVbit a ha).trans hbit
      apply red_sum_not_mem_target hA hs hweak.1 hVA hVhue hVred
      rwa [hsumV]
  | true =>
      apply hmBlue
      rw [← hsumV]
      apply sum_mem_bluePossible hA hh hJ
        (sparseWeakSequence_window_gap hunbounded A h n) hVA
      · exact ⟨s, hs, hVhue⟩
      · intro a ha
        rw [← selectedBlueBit_eq_true]
        exact (hVbit a ha).trans hbit
      · rw [hsumV]
        exact (Finset.mem_Ioc.mp hmTarget).2

theorem not_ramseyComplete_of_weakScale_unbounded {A : Set ℕ} (hA : A.Infinite)
    {h r : ℕ} (hh : 0 < h) (hhr : 2 * h ≤ r)
    (hunbounded : ∀ b, ∃ j, b < j ∧ WeakScale A h j) :
    ¬RamseyComplete r A := by
  intro hramsey
  obtain ⟨N₀, hN₀⟩ := hramsey
    (sparseObstructionColor A h r hh hhr hunbounded)
  obtain ⟨m, hmTarget, hmnot⟩ :=
    exists_omitted_at_sparseWeakSequence hA hh hhr hunbounded N₀
  have hJid : N₀ ≤ sparseWeakSequence hunbounded A h N₀ :=
    (sparseWeakSequence_strictMono hunbounded A h).id_le N₀
  have hjbig := sparseWeakSequence_gt_sixteen hh hunbounded N₀
  have hthreshold : sparseWeakSequence hunbounded A h N₀ ≤
      redThreshold (sparseWeakSequence hunbounded A h N₀) := by
    unfold redThreshold
    have hp : 1 ≤ 2 ^ (sparseWeakSequence hunbounded A h N₀ - 1) :=
      Nat.one_le_two_pow
    nlinarith
  have hN₀m : N₀ ≤ m := by
    have hmLower := (Finset.mem_Ioc.mp hmTarget).1
    omega
  exact hmnot (hN₀ m hN₀m)

end Erdos55
