import Mathlib
import ErdosProblems.Erdos336.LShapeArithmetic
import ErdosProblems.Erdos336.TwoGeneratorDiagram

/- Ported from Lean 4.31.0 to 4.33.0; imports, helper namespaces, and elaboration adapted. -/
set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Degree--diameter bound for an L-shaped canonical diagram
-/

namespace Erdos336

/-- The lattice cells in an outer `l × h` rectangle after deleting the
upper-right `w × y` rectangle. -/
def lShapeFinset (l h w y : ℕ) : Finset (ℕ × ℕ) :=
  (Finset.range l ×ˢ Finset.range h) \
    (Finset.Ico (l - w) l ×ˢ Finset.Ico (h - y) h)

@[simp] theorem mem_lShapeFinset {l h w y : ℕ} {p : ℕ × ℕ} :
    p ∈ lShapeFinset l h w y ↔
      p.1 < l ∧ p.2 < h ∧ ¬(l - w ≤ p.1 ∧ h - y ≤ p.2) := by
  simp only [lShapeFinset, Finset.mem_sdiff, Finset.mem_product,
    Finset.mem_range, Finset.mem_Ico]
  tauto

/-- Its cardinality is the expected rectangle difference. -/
theorem card_lShapeFinset {l h w y : ℕ} (hw : w ≤ l) (hy : y ≤ h) :
    (lShapeFinset l h w y).card = l * h - w * y := by
  have hsub :
      (Finset.Ico (l - w) l ×ˢ Finset.Ico (h - y) h) ⊆
        (Finset.range l ×ˢ Finset.range h) := by
    intro p hp
    simp only [Finset.mem_product, Finset.mem_Ico, Finset.mem_range] at hp ⊢
    exact ⟨hp.1.2, hp.2.2⟩
  rw [lShapeFinset, Finset.card_sdiff_of_subset hsub]
  simp [Nat.sub_sub_self hw, Nat.sub_sub_self hy]

/-- The lower end of the vertical arm belongs to a nondegenerate L-shape. -/
theorem leftArm_tip_mem_lShape
    {l h w y : ℕ} (hw : w < l) (hy : y < h) :
    (l - w - 1, h - 1) ∈ lShapeFinset l h w y := by
  rw [mem_lShapeFinset]
  constructor
  · omega
  constructor
  · omega
  · omega

/-- The right end of the horizontal arm belongs to a nondegenerate L-shape. -/
theorem bottomArm_tip_mem_lShape
    {l h w y : ℕ} (hw : w < l) (hy : y < h) :
    (l - 1, h - y - 1) ∈ lShapeFinset l h w y := by
  rw [mem_lShapeFinset]
  constructor
  · omega
  constructor
  · omega
  · omega

/-- Any L-shaped diagram lying in the total-degree `H` triangle has cardinality
at most `(H+2)²/3`. -/
theorem card_lShape_le_third
    {l h w y H : ℕ} (hw : w < l) (hy : y < h)
    (hdegree : ∀ p ∈ lShapeFinset l h w y, p.1 + p.2 ≤ H) :
    3 * (lShapeFinset l h w y).card ≤ (H + 2) ^ 2 := by
  have hleft := hdegree _ (leftArm_tip_mem_lShape hw hy)
  have hbottom := hdegree _ (bottomArm_tip_mem_lShape hw hy)
  have hd₁ : l + h - w ≤ H + 2 := by omega
  have hd₂ : l + h - y ≤ H + 2 := by omega
  have hcard := card_lShapeFinset (Nat.le_of_lt hw) (Nat.le_of_lt hy)
  apply lShape_area_le_third (Nat.le_of_lt hw) (Nat.le_of_lt hy)
  · rw [hcard]
    apply Nat.sub_add_cancel
    exact Nat.mul_le_mul (Nat.le_of_lt hw) (Nat.le_of_lt hy)
  · exact hd₁
  · exact hd₂

/-- Consequently, once the canonical two-generator minimum-distance diagram
is identified as a nondegenerate L-shape, the sharp degree--diameter bound is
automatic. -/
theorem twoGenerator_card_le_third_of_lShape
    {G : Type*} [AddCommMonoid G] [DecidableEq G] [Fintype G]
    (a b : G)
    (hgen : ∀ g : G, ∃ p : ℕ × ℕ, twoGenLabel a b p = g)
    {H l h w y : ℕ}
    (hcover : ∀ g : G, ∃ p : ℕ × ℕ,
      p.1 + p.2 ≤ H ∧ twoGenLabel a b p = g)
    (hw : w < l) (hy : y < h)
    (hshape : canonicalTwoDiagram a b hgen = lShapeFinset l h w y) :
    3 * Fintype.card G ≤ (H + 2) ^ 2 := by
  rw [← card_canonicalTwoDiagram a b hgen, hshape]
  apply card_lShape_le_third hw hy
  intro p hp
  apply canonicalTwoDiagram_degree_le a b hgen hcover
  simpa [hshape] using hp

end Erdos336
