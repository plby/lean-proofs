/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.GainDefectExponentBudget
import ErdosProblems.Erdos207.EqualRemainderOmissionWeight

/-! # The fourth-moment exception retains its omission multiplicity -/

namespace Erdos207

open Finset
open scoped NNReal

noncomputable section

def gainDefectExceptionalClass
    {W : Type*} [Fintype W] [DecidableEq W]
    (F G : Finset (Finset W)) (T : W) (z : ℕ) (H : Finset W) :
    Finset (GainDefectWitness F G T z) := by
  classical
  exact univ.filter fun w ↦ H ⊆ w.remainder ∧ w.ForwardExceptional H ∧
    H.card = 1 ∧ T ∉ w.second ∧ w.second \ H = w.first.erase T

def gainDefectExceptionalEmbedding
    {W : Type*} [Fintype W] [DecidableEq W]
    (F : Finset (Finset W)) (T T' : W) (z : ℕ) :
    gainDefectExceptionalClass F F T z {T'} ↪ equalRemainderOmissionCodes F T T' z := by
  classical
  refine ⟨fun w ↦ ⟨((w.1.first, w.1.second), w.1.omitted), ?_⟩, ?_⟩
  · have hw := (mem_filter.mp w.2).2
    have hroot : T' ∈ w.1.second :=
      w.1.extension_subset_second_of_forwardExceptional {T'} hw.1 hw.2.1 (mem_singleton_self _)
    have hne : w.1.first ≠ w.1.second := by
      intro h
      exact w.1.not_subset (h ▸ Subset.refl w.1.first)
    have hrem : w.1.first.erase T = w.1.second.erase T' := by
      simpa only [sdiff_singleton_eq_erase] using hw.2.2.2.2.symm
    exact mem_equalRemainderOmissionCodes_iff.mpr
      ⟨mem_distinctEqualRemainderPairs_iff.mpr
        ⟨w.1.first_mem, w.1.second_mem, hne, w.1.root_mem, hroot, hrem⟩,
        w.1.omitted_subset, w.1.omitted_card⟩
  · intro w u h
    have hf : w.1.first = u.1.first := congrArg (fun p ↦ p.1.1.1) h
    have hs : w.1.second = u.1.second := congrArg (fun p ↦ p.1.1.2) h
    have ho : w.1.omitted = u.1.omitted := congrArg (fun p ↦ p.1.2) h
    apply Subtype.ext
    rcases w with ⟨w, hw⟩
    rcases u with ⟨u, hu⟩
    cases w
    cases u
    simp_all

def gainDefectExceptionalWeight
    {W : Type*} [Fintype W] [DecidableEq W]
    (F G : Finset (Finset W)) (T : W) (z : ℕ) (H : Finset W) (p : ℝ≥0) : ℝ≥0 :=
  ∑ w ∈ gainDefectExceptionalClass F G T z H, p ^ (w.remainder \ H).card

theorem gainDefectExceptionalWeight_le_omissionWeight
    {W : Type*} [Fintype W] [DecidableEq W]
    (F : Finset (Finset W)) (T T' : W) (z m : ℕ) (p : ℝ≥0)
    (hF : ∀ E ∈ F, E.card = m) :
    gainDefectExceptionalWeight F F T z {T'} p ≤ equalRemainderOmissionWeight F T T' z p := by
  classical
  have hcard : (gainDefectExceptionalClass F F T z {T'}).card ≤
      (equalRemainderOmissionCodes F T T' z).card := by
    rw [← Fintype.card_coe, ← Fintype.card_coe]
    exact Fintype.card_le_of_embedding (gainDefectExceptionalEmbedding F T T' z)
  have hweight : gainDefectExceptionalWeight F F T z {T'} p =
      (gainDefectExceptionalClass F F T z {T'}).card * p ^ (m - 1 - z) := by
    unfold gainDefectExceptionalWeight
    calc
      _ = ∑ _w ∈ gainDefectExceptionalClass F F T z {T'}, p ^ (m - 1 - z) := by
        apply sum_congr rfl
        intro w hw
        have h := (mem_filter.mp hw).2
        rw [w.remainder_sdiff_eq_left_of_forwardExceptional {T'} h.2.1,
          w.leftRemainder_card, hF w.first w.first_mem]
        congr 1
        omega
      _ = _ := by simp
  rw [hweight, equalRemainderOmissionWeight_eq F T T' z m p hF]
  apply mul_le_mul_of_nonneg_right _ zero_le
  exact_mod_cast hcard

theorem gainDefectExceptionalWeight_eq_zero_of_orders_ne
    {W : Type*} [Fintype W] [DecidableEq W]
    (F G : Finset (Finset W)) (T : W) (z r s : ℕ) (H : Finset W) (p : ℝ≥0)
    (hF : ∀ E ∈ F, E.card = r - 2) (hG : ∀ E ∈ G, E.card = s - 2) (hrs : r ≠ s) :
    gainDefectExceptionalWeight F G T z H p = 0 := by
  classical
  have hempty : gainDefectExceptionalClass F G T z H = ∅ := by
    apply eq_empty_iff_forall_notMem.mpr
    intro w hw
    have h := (mem_filter.mp hw).2
    exact hrs (w.equal_remainders_orders_eq H h.1 h.2.1 h.2.2.1 h.2.2.2.2
      r s (hF w.first w.first_mem) (hG w.second w.second_mem))
  simp only [gainDefectExceptionalWeight, hempty, sum_empty]

theorem gainDefectExceptionalWeight_absorberInduced_le
    {V : Type*} [Fintype V] [DecidableEq V]
    (q r z : ℕ) (B : TripleSystemOn V) (T : TripleOn V) (H : TripleSystemOn V)
    (hr : 4 ≤ r) (hz : 1 ≤ z) :
    gainDefectExceptionalWeight (absorberInducedConfigurationsOn q r B)
      (absorberInducedConfigurationsOn q r B) T z H (Fintype.card V + 1 : ℝ≥0)⁻¹ ≤
      (2 : ℝ≥0) ^ (r - 3) *
        (2 * pairExactBankExtensionCoefficient q B + 2 ^ (r ^ 3) * (r + 1) : ℕ) *
        (Fintype.card V + 1 : ℝ≥0) ^ (z - 1) := by
  classical
  by_cases hcard : H.card = 1
  · obtain ⟨T', rfl⟩ := card_eq_one.mp hcard
    exact (gainDefectExceptionalWeight_le_omissionWeight
      (absorberInducedConfigurationsOn q r B) T T' z (r - 2) _
      absorberInducedConfigurationsOn_fixed_card).trans
      (equalRemainderOmissionWeight_absorberInduced_le q r z B T T' hr hz)
  · have he : gainDefectExceptionalClass (absorberInducedConfigurationsOn q r B)
        (absorberInducedConfigurationsOn q r B) T z H = ∅ := by
      apply eq_empty_iff_forall_notMem.mpr
      intro w hw
      exact hcard (mem_filter.mp hw).2.2.2.1
    rw [gainDefectExceptionalWeight, he, sum_empty]
    exact zero_le

end

end Erdos207
