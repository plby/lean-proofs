/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.CommonThreatExposureClass

/-! # A bounded finite code set for the third-moment exposure partition -/

namespace Erdos207

open Finset

noncomputable section

abbrev CommonThreatExposureCode (W : Type*) := (Finset W × Finset W) × (ℕ × ℕ)

def CommonThreatWitness.exposureCode
    {W : Type*} [DecidableEq W] {F G : Finset (Finset W)} {T T' : W}
    (w : CommonThreatWitness F G T T') (H : Finset W) : CommonThreatExposureCode W :=
  ((w.firstExposureRoot H, insert T' (w.second ∩ H)),
    ((w.secondExposureRoot H).card, (w.leftRemainder ∩ w.rightRemainder).card))

def commonThreatExposureCodeSupport
    {W : Type*} [DecidableEq W] (T T' : W) (H : Finset W) (q : ℕ) :
    Finset (CommonThreatExposureCode W) :=
  ((H.powerset.image (insert T)) ×ˢ (H.powerset.image (insert T'))) ×ˢ
    (range (q + 1) ×ˢ range (q + 1))

theorem card_commonThreatExposureCodeSupport_le
    {W : Type*} [DecidableEq W] (T T' : W) (H : Finset W) (q : ℕ) :
    (commonThreatExposureCodeSupport T T' H q).card ≤ 2 ^ (2 * H.card) * (q + 1) ^ 2 := by
  unfold commonThreatExposureCodeSupport
  simp only [card_product, card_range]
  calc
    _ ≤ (H.powerset.card * H.powerset.card) * ((q + 1) * (q + 1)) := by
      exact Nat.mul_le_mul_right _ (Nat.mul_le_mul card_image_le card_image_le)
    _ = _ := by rw [card_powerset, ← pow_add]; congr 1 <;> ring

theorem CommonThreatWitness.exposureCode_mem_support
    {W : Type*} [DecidableEq W] {F G : Finset (Finset W)} {T T' : W}
    (w : CommonThreatWitness F G T T') (H : Finset W) (q : ℕ)
    (hfirst : w.first.card ≤ q) (hsecond : w.second.card ≤ q) :
    w.exposureCode H ∈ commonThreatExposureCodeSupport T T' H q := by
  have hb : (w.secondExposureRoot H).card ≤ q := by
    rw [w.secondExposureRoot_eq_inter]
    exact (card_le_card inter_subset_left).trans hsecond
  have hk : (w.leftRemainder ∩ w.rightRemainder).card ≤ q := by
    refine (card_le_card inter_subset_left).trans ?_
    rw [w.leftRemainder_card]
    omega
  apply mem_product.mpr
  refine ⟨mem_product.mpr ⟨?_, ?_⟩, mem_product.mpr ⟨?_, ?_⟩⟩
  · exact mem_image.mpr ⟨w.leftRemainder ∩ H, mem_powerset.mpr inter_subset_right, rfl⟩
  · exact mem_image.mpr ⟨w.second ∩ H, mem_powerset.mpr inter_subset_right, rfl⟩
  · apply mem_range.mpr
    change (w.secondExposureRoot H).card < q + 1
    omega
  · apply mem_range.mpr
    change (w.leftRemainder ∩ w.rightRemainder).card < q + 1
    omega

theorem commonThreatExposureClass_eq_code_fibre
    {W : Type*} [Fintype W] [DecidableEq W]
    (F G : Finset (Finset W)) (T T' : W) (H : Finset W) (c : CommonThreatExposureCode W) :
    commonThreatExposureClass F G T T' H c.1.1 c.1.2 c.2.1 c.2.2 =
      univ.filter (fun w : CommonThreatWitness F G T T' ↦ H ⊆ w.remainder ∧ w.exposureCode H = c) := by
  classical
  rcases c with ⟨⟨Q, Q'⟩, ⟨b, k⟩⟩
  ext w
  simp only [commonThreatExposureClass, CommonThreatWitness.exposureCode,
    mem_filter, mem_univ, true_and, Prod.mk.injEq]
  tauto

theorem card_second_root_of_mem_commonThreatExposureCodeSupport
    {W : Type*} [DecidableEq W] {T T' : W} {H : Finset W} {q : ℕ}
    {c : CommonThreatExposureCode W} (hc : c ∈ commonThreatExposureCodeSupport T T' H q) :
    c.1.2.card ≤ H.card + 1 := by
  obtain ⟨R, hR, hEq⟩ := mem_image.mp (mem_product.mp (mem_product.mp hc).1).2
  rw [← hEq]
  exact (card_insert_le _ _).trans (Nat.add_le_add_right (card_le_card (mem_powerset.mp hR)) 1)

end

end Erdos207
