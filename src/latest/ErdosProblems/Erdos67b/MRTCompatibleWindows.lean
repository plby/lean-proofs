import ErdosProblems.Erdos67b.MRTProductWindows

/-! # Counting compatible quadruples of discrete short-interval starts -/

open scoped BigOperators
open Finset

namespace Erdos67b

noncomputable section

def mrtCompanionStarts (H n p r : ℕ) : Finset ℕ :=
  Finset.Icc ((n / p + 1) * r - H) ((n / p + 1) * r + 2 * H)

theorem mrtProductWindow_companion_mem {Z H n s p r m : ℕ} (hp : 0 < p)
    (hr : r ≤ 2 * p) (hn : mrtProductWindow Z H n p m)
    (hs : mrtProductWindow Z H s r m) : s ∈ mrtCompanionStarts H n p r := by
  let a := n / p + 1
  have ham : a ≤ m := Nat.succ_le_of_lt ((Nat.div_lt_iff_lt_mul hp).2 hn.1)
  have hfirst : n < a * p := (Nat.div_lt_iff_lt_mul hp).1 (Nat.lt_succ_self (n / p))
  have hdecomp : m * p = a * p + (m - a) * p := by
    rw [← Nat.add_mul, Nat.add_sub_of_le ham]
  have hgap : (m - a) * p ≤ H := by
    have hupper := hn.2.1
    omega
  have hgapr : (m - a) * r ≤ 2 * H := by
    calc
      _ ≤ (m - a) * (2 * p) := Nat.mul_le_mul_left (m - a) hr
      _ = 2 * ((m - a) * p) := by ring
      _ ≤ _ := Nat.mul_le_mul_left 2 hgap
  have hdecompr : m * r = a * r + (m - a) * r := by
    rw [← Nat.add_mul, Nat.add_sub_of_le ham]
  have hlow : a * r ≤ s + H := (Nat.mul_le_mul_right r ham).trans hs.2.1
  have hupp : s < a * r + (m - a) * r := by rw [← hdecompr]; exact hs.1
  change s ∈ Finset.Icc (a * r - H) (a * r + 2 * H)
  rw [Finset.mem_Icc]
  omega

theorem mrtCard_startInterval_le (a H : ℕ) :
    (Finset.Icc (a - H) (a + 2 * H)).card ≤ 3 * H + 1 := by
  rw [Nat.card_Icc]
  omega

theorem card_mrtCompanionStarts_le (H n p r : ℕ) :
    (mrtCompanionStarts H n p r).card ≤ 3 * H + 1 :=
  mrtCard_startInterval_le _ _

def mrtStartBox (H : ℕ) (p : (ℕ × ℕ) × (ℕ × ℕ)) (a : ℕ) :
    Finset ((ℕ × ℕ) × (ℕ × ℕ)) :=
  ({a} ×ˢ mrtCompanionStarts H a p.1.1 p.1.2) ×ˢ
    (mrtCompanionStarts H a p.1.1 p.2.1 ×ˢ mrtCompanionStarts H a p.1.1 p.2.2)

def mrtCompatibleStarts (Z H M Y : ℕ) (p : (ℕ × ℕ) × (ℕ × ℕ)) :
    Finset ((ℕ × ℕ) × (ℕ × ℕ)) := by
  classical
  exact (primeQuadrupleSet (Finset.Ioc Y (2 * Y))).filter fun n ↦
    (mrtQuadCofactors Z H M p n).Nonempty

theorem mrtCompatibleStarts_subset_boxes (Z H M Y : ℕ) (p : (ℕ × ℕ) × (ℕ × ℕ))
    (h₁₁ : 0 < p.1.1) (h₁₂ : p.1.2 ≤ 2 * p.1.1)
    (h₂₁ : p.2.1 ≤ 2 * p.1.1) (h₂₂ : p.2.2 ≤ 2 * p.1.1) :
    mrtCompatibleStarts Z H M Y p ⊆
      (Finset.Ioc Y (2 * Y)).biUnion (mrtStartBox H p) := by
  classical
  intro n hn
  obtain ⟨hstarts, m, hm⟩ := Finset.mem_filter.1 hn
  have hfirst : n.1.1 ∈ Finset.Ioc Y (2 * Y) :=
    (Finset.mem_product.1 (Finset.mem_product.1 hstarts).1).1
  obtain ⟨_, _, hm₁₁, hm₁₂, hm₂₁, hm₂₂⟩ := mem_mrtQuadCofactors.1 hm
  apply Finset.mem_biUnion.2
  refine ⟨n.1.1, hfirst, ?_⟩
  simp only [mrtStartBox, Finset.mem_product, Finset.mem_singleton]
  exact ⟨⟨True.intro, mrtProductWindow_companion_mem h₁₁ h₁₂ hm₁₁ hm₁₂⟩,
    mrtProductWindow_companion_mem h₁₁ h₂₁ hm₁₁ hm₂₁,
    mrtProductWindow_companion_mem h₁₁ h₂₂ hm₁₁ hm₂₂⟩

theorem card_mrtStartBox_le (H : ℕ) (p : (ℕ × ℕ) × (ℕ × ℕ)) (a : ℕ) :
    (mrtStartBox H p a).card ≤ (3 * H + 1) ^ 3 := by
  simp only [mrtStartBox, Finset.card_product, Finset.card_singleton, one_mul]
  calc
    _ ≤ (3 * H + 1) * ((3 * H + 1) * (3 * H + 1)) :=
      Nat.mul_le_mul (card_mrtCompanionStarts_le _ _ _ _)
        (Nat.mul_le_mul (card_mrtCompanionStarts_le _ _ _ _) (card_mrtCompanionStarts_le _ _ _ _))
    _ = _ := by ring

theorem card_mrtCompatibleStarts_le (Z H M Y : ℕ) (p : (ℕ × ℕ) × (ℕ × ℕ))
    (h₁₁ : 0 < p.1.1) (h₁₂ : p.1.2 ≤ 2 * p.1.1)
    (h₂₁ : p.2.1 ≤ 2 * p.1.1) (h₂₂ : p.2.2 ≤ 2 * p.1.1) :
    (mrtCompatibleStarts Z H M Y p).card ≤ Y * (3 * H + 1) ^ 3 := by
  have hcard : (Finset.Ioc Y (2 * Y)).card = Y := by
    rw [Nat.card_Ioc]
    omega
  calc
    _ ≤ ((Finset.Ioc Y (2 * Y)).biUnion (mrtStartBox H p)).card :=
      Finset.card_le_card (mrtCompatibleStarts_subset_boxes Z H M Y p h₁₁ h₁₂ h₂₁ h₂₂)
    _ ≤ ∑ a ∈ Finset.Ioc Y (2 * Y), (mrtStartBox H p a).card := Finset.card_biUnion_le
    _ ≤ ∑ _a ∈ Finset.Ioc Y (2 * Y), (3 * H + 1) ^ 3 :=
      Finset.sum_le_sum fun a _ ↦ card_mrtStartBox_le H p a
    _ = _ := by simp [hcard]

theorem card_mrtCompatibleStarts_le_cube (Z H M Y : ℕ) (p : (ℕ × ℕ) × (ℕ × ℕ))
    (hH : 1 ≤ H) (h₁₁ : 0 < p.1.1) (h₁₂ : p.1.2 ≤ 2 * p.1.1)
    (h₂₁ : p.2.1 ≤ 2 * p.1.1) (h₂₂ : p.2.2 ≤ 2 * p.1.1) :
    (mrtCompatibleStarts Z H M Y p).card ≤ 64 * Y * H ^ 3 := by
  apply (card_mrtCompatibleStarts_le Z H M Y p h₁₁ h₁₂ h₂₁ h₂₂).trans
  calc
    _ ≤ Y * (4 * H) ^ 3 := Nat.mul_le_mul_left Y (Nat.pow_le_pow_left (by omega) 3)
    _ = _ := by ring

end

end Erdos67b
