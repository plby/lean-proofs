/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.GainDefectExposureClass

/-! # A bounded code support for forward gain-defect exposures -/

namespace Erdos207

open Finset

noncomputable section

abbrev GainDefectExposureCode (W : Type*) := (Finset W × Finset W) × (ℕ × ℕ)

def GainDefectWitness.exposureCode
    {W : Type*} [DecidableEq W] {F G : Finset (Finset W)} {T : W} {z : ℕ}
    (w : GainDefectWitness F G T z) (H : Finset W) : GainDefectExposureCode W :=
  ((w.firstExposureRoot H, w.second ∩ H),
    ((w.secondExposureRoot H).card, (w.leftRemainder ∩ w.rightRemainder).card))

def gainDefectExposureCodeSupport
    {W : Type*} [DecidableEq W] (T : W) (H : Finset W) (q : ℕ) : Finset (GainDefectExposureCode W) :=
  ((H.powerset.image (insert T)) ×ˢ H.powerset) ×ˢ (range (q + 1) ×ˢ range (q + 1))

theorem card_gainDefectExposureCodeSupport_le
    {W : Type*} [DecidableEq W] (T : W) (H : Finset W) (q : ℕ) :
    (gainDefectExposureCodeSupport T H q).card ≤ 2 ^ (2 * H.card) * (q + 1) ^ 2 := by
  unfold gainDefectExposureCodeSupport
  simp only [card_product, card_range]
  calc
    _ ≤ (H.powerset.card * H.powerset.card) * ((q + 1) * (q + 1)) :=
      Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ card_image_le)
    _ = _ := by rw [card_powerset, ← pow_add]; congr 1 <;> ring

theorem GainDefectWitness.exposureCode_mem_support
    {W : Type*} [DecidableEq W] {F G : Finset (Finset W)} {T : W} {z : ℕ}
    (w : GainDefectWitness F G T z) (H : Finset W) (q : ℕ)
    (hfirst : w.first.card ≤ q) (hsecond : w.second.card ≤ q) :
    w.exposureCode H ∈ gainDefectExposureCodeSupport T H q := by
  have hb : (w.secondExposureRoot H).card ≤ q := (card_le_card inter_subset_left).trans hsecond
  have hk : (w.leftRemainder ∩ w.rightRemainder).card ≤ q := by
    refine (card_le_card inter_subset_left).trans ?_
    rw [w.leftRemainder_card]
    omega
  apply mem_product.mpr
  refine ⟨mem_product.mpr ⟨?_, ?_⟩, mem_product.mpr ⟨?_, ?_⟩⟩
  · exact mem_image.mpr ⟨w.first ∩ H, mem_powerset.mpr inter_subset_right, rfl⟩
  · exact mem_powerset.mpr inter_subset_right
  · apply mem_range.mpr
    change (w.secondExposureRoot H).card < q + 1
    omega
  · apply mem_range.mpr
    change (w.leftRemainder ∩ w.rightRemainder).card < q + 1
    omega

theorem gainDefectExposureClass_eq_code_fibre
    {W : Type*} [Fintype W] [DecidableEq W]
    (F G : Finset (Finset W)) (T : W) (z : ℕ) (H : Finset W) (c : GainDefectExposureCode W) :
    gainDefectExposureClass F G T z H c.1.1 c.1.2 c.2.1 c.2.2 =
      univ.filter (fun w : GainDefectWitness F G T z ↦ H ⊆ w.remainder ∧ w.exposureCode H = c) := by
  classical
  rcases c with ⟨⟨Q, Q'⟩, ⟨b, k⟩⟩
  ext w
  simp only [gainDefectExposureClass, GainDefectWitness.exposureCode,
    mem_filter, mem_univ, true_and, Prod.mk.injEq]
  tauto

theorem card_second_root_of_mem_gainDefectExposureCodeSupport
    {W : Type*} [DecidableEq W] {T : W} {H : Finset W} {q : ℕ}
    {c : GainDefectExposureCode W} (hc : c ∈ gainDefectExposureCodeSupport T H q) :
    c.1.2.card ≤ H.card :=
  card_le_card (mem_powerset.mp (mem_product.mp (mem_product.mp hc).1).2)

end

end Erdos207
