/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos4b.GeneralFourierPinnedNaturalWeight
import ErdosProblems.Erdos4b.GeneralFourierSourceTransport

/-!
# The original primorial-shift square at a pinned prime

The companion coprimality filter is redundant on supported natural
divisibility summands. Reindexing the actual primorial shifts then
identifies the original nonnegative square with the reduced pinned square.
-/

namespace Erdos4b

noncomputable section

open scoped BigOperators

theorem sum_cutoffDivisorTupleSupport_equiv
    {ι κ M : Type*} [Fintype ι] [Fintype κ] [AddCommMonoid M]
    (e : ι ≃ κ) (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) (f : (κ → ℕ) → M) :
    (∑ d ∈ cutoffDivisorTupleSupport κ P, f d) =
      ∑ d ∈ cutoffDivisorTupleSupport ι P, f (fun j ↦ d (e.symm j)) := by
  classical
  apply Finset.sum_bij (fun d _ ↦ fun i ↦ d (e i))
  · intro d hd
    rw [mem_cutoffDivisorTupleSupport P hP] at hd ⊢
    exact fun i ↦ hd (e i)
  · intro d hd d' hd' heq
    funext j
    simpa only [Equiv.apply_symm_apply] using congrFun heq (e.symm j)
  · intro d hd
    refine ⟨fun j ↦ d (e.symm j), ?_, ?_⟩
    · rw [mem_cutoffDivisorTupleSupport P hP] at hd ⊢
      exact fun j ↦ hd (e.symm j)
    · funext i
      exact congrArg d (e.symm_apply_apply i)
  · intro d hd
    simp only [Equiv.apply_symm_apply]

theorem largeGapDivisorCondition_companion_coprime
    {H : Finset ℕ} {m q n : ℕ} (hm : 0 < m) (hn : 0 < n)
    {d e : H → ℕ} (hc : largeGapDivisorCondition H m q n d e) :
    ∀ i, m.Coprime (e i) := by
  intro i
  have hpos : 1 ≤ m * (n + i.val * q) :=
    Nat.succ_le_iff.mpr (Nat.mul_pos hm (by omega))
  have hcop : (m * (n + i.val * q)).Coprime (m * (n + i.val * q) - 1) :=
    (Nat.coprime_self_sub_right hpos).mpr (Nat.coprime_one_right _)
  exact (hcop.of_dvd_left (dvd_mul_right m (n + i.val * q))).of_dvd_right (hc i).2

open Classical in
theorem doubledSelbergInner_cutoff_eq_full
    (H P : Finset ℕ) {m q n : ℕ} (hm : 0 < m) (hn : 0 < n)
    (lambda : (H → ℕ) → (H → ℕ) → ℝ) :
    doubledSelbergInner H (cutoffDivisorTupleSupport H P)
        (cutoffCompanionDivisorTupleSupport H P m) lambda m q n =
      ∑ d ∈ cutoffDivisorTupleSupport H P, ∑ e ∈ cutoffDivisorTupleSupport H P,
        if largeGapDivisorCondition H m q n d e then lambda d e else 0 := by
  unfold doubledSelbergInner cutoffCompanionDivisorTupleSupport
  simp only [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro d hd
  apply Finset.sum_congr rfl
  intro e he
  by_cases hc : largeGapDivisorCondition H m q n d e
  · simp only [if_pos hc, if_pos (largeGapDivisorCondition_companion_coprime hm hn hc)]
  · simp only [if_neg hc, ite_self]

theorem largeGapDivisorCondition_preSieved_iff_indexed
    {K w m q n : ℕ} (d e : Fin K → ℕ) :
    largeGapDivisorCondition (preSievedShifts K w) m q n
        (fun j ↦ d ((preSievedShiftEquiv K w).symm j))
        (fun j ↦ e ((preSievedShiftEquiv K w).symm j)) ↔
      IndexedSourceDivisorCondition w m q n d e := by
  constructor
  · intro hc i
    simpa only [Equiv.symm_apply_apply, preSievedShiftEquiv_apply_val] using
      hc (preSievedShiftEquiv K w i)
  · intro hc j
    have hj : primorial w * ((preSievedShiftEquiv K w).symm j).val = j.val := by
      rw [← preSievedShiftEquiv_apply_val, Equiv.apply_symm_apply]
    simpa only [hj] using hc ((preSievedShiftEquiv K w).symm j)

theorem doubledSelbergWeight_source_eq_indexed
    {K w m q n : ℕ} {J : Type*}
    (S : Finset J) (F : J → Fin K → ℝ → ℝ) (G : ℝ → ℝ)
    (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) (LD LE : ℝ) (hm : 0 < m) (hn : 0 < n) :
    doubledSelbergWeight (preSievedShifts K w)
        (cutoffDivisorTupleSupport (preSievedShifts K w) P)
        (cutoffCompanionDivisorTupleSupport (preSievedShifts K w) P m)
        (sourceAnalyticSelbergCoefficient S
          (fun j i ↦ F j ((preSievedShiftEquiv K w).symm i)) G LD LE) m q n =
      indexedSourceWeight S F G P w m q n LD LE := by
  classical
  unfold doubledSelbergWeight indexedSourceWeight
  congr 1
  rw [doubledSelbergInner_cutoff_eq_full _ _ hm hn,
    sum_cutoffDivisorTupleSupport_equiv (preSievedShiftEquiv K w) P hP]
  apply Finset.sum_congr rfl
  intro d hd
  rw [sum_cutoffDivisorTupleSupport_equiv (preSievedShiftEquiv K w) P hP]
  apply Finset.sum_congr rfl
  intro e he
  simp only [largeGapDivisorCondition_preSieved_iff_indexed,
    sourceAnalyticSelbergCoefficient_equiv (preSievedShiftEquiv K w), Equiv.symm_apply_apply]

theorem doubledSelbergWeight_source_eq_pinned
    {K w m p₀ q n Y : ℕ} {J : Type*}
    (S : Finset J) (F : J → Fin K → ℝ → ℝ) (G : ℝ → ℝ)
    (h : Fin K) (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    {LD : ℝ} (hLD : 0 < LD) (hY : 1 < Y) (hm : 0 < m) (hn : 0 < n)
    (hp₀ : p₀.Prime) (hpin : n + primorial w * h.val * q = p₀)
    (hFsupport : ∀ j ∈ S, ∀ i t, 0 ≤ t → F j i t ≠ 0 → t ≤ (1 : ℝ) / 10)
    (hGsupport : ∀ t, 0 ≤ t → G t ≠ 0 → t ≤ 1)
    (hD : LD / 10 < Real.log p₀) (hcop : (m * p₀ - 1).Coprime (primorial Y)) :
    (doubledSelbergWeight (preSievedShifts K w)
        (cutoffDivisorTupleSupport (preSievedShifts K w) P)
        (cutoffCompanionDivisorTupleSupport (preSievedShifts K w) P m)
        (sourceAnalyticSelbergCoefficient S
          (fun j i ↦ F j ((preSievedShiftEquiv K w).symm i)) G LD (Real.log Y)) m q n : ℂ) =
      pinnedSourceIntegerWeight S F G h P w m p₀ q LD (Real.log Y) := by
  rw [doubledSelbergWeight_source_eq_indexed S F G P hP LD (Real.log Y) hm hn]
  exact indexedSourceWeight_eq_pinnedSourceIntegerWeight S F G h P hP hLD hY hm hn
    hp₀ hpin hFsupport hGsupport hD hcop

end

end Erdos4b
