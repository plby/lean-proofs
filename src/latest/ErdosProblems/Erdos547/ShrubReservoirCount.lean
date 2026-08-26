import ErdosProblems.Erdos547.PlacedShrub
import Mathlib.Data.Finset.Option

/-!
# Only the distinguished roots consume reservoir vertices
-/

namespace Erdos547

open Finset

theorem card_reservoir_image_le {U V : Type*} [Fintype U] [DecidableEq V]
    (f : U → V) (r : U) (s : Option U) (Q : Finset V) (p : Prop) [Decidable p]
    (hroots : ∀ u, f u ∈ Q → u = r ∨ s = some u) (hprimary : f r ∈ Q → p) :
    (Q ∩ Finset.univ.image f).card ≤ (if p then 1 else 0) + (if s.isSome then 1 else 0) := by
  classical
  let R : Finset V := if p then {f r} else ∅
  have hsub : Q ∩ Finset.univ.image f ⊆ R ∪ s.toFinset.image f := by
    intro v hv
    obtain ⟨hvQ, hv⟩ := Finset.mem_inter.mp hv
    obtain ⟨u, _, rfl⟩ := Finset.mem_image.mp hv
    rcases hroots u hvQ with rfl | hs
    · have hp := hprimary hvQ
      exact Finset.mem_union_left _ (by simp only [R, if_pos hp, Finset.mem_singleton])
    · apply Finset.mem_union_right
      apply Finset.mem_image.mpr
      refine ⟨u, ?_, rfl⟩
      rw [hs]
      simp
  have hh := (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)
  have hcardR : R.card = if p then 1 else 0 := by
    simp only [R, apply_ite Finset.card, Finset.card_singleton, Finset.card_empty]
  have hcards : (s.toFinset.image f).card ≤ if s.isSome then 1 else 0 := by
    apply Finset.card_image_le.trans
    cases s <;> simp
  rw [hcardR] at hh
  omega

theorem reservoir_count_after_union {V : Type*} [DecidableEq V]
    (Q used fresh : Finset V) (a b : ℕ)
    (hused : (Q ∩ used).card ≤ a) (hfresh : (Q ∩ fresh).card ≤ b) :
    (Q ∩ (used ∪ fresh)).card ≤ a + b := by
  rw [Finset.inter_union_distrib_left]
  exact (Finset.card_union_le _ _).trans (Nat.add_le_add hused hfresh)

theorem card_postponed_le_near_mass {F : Type*} [DecidableEq F]
    (B : Finset F) (w : F → ℕ) (hw : ∀ x ∈ B, 1 ≤ w x) : B.card ≤ ∑ x ∈ B, w x := by
  calc
    B.card = ∑ _x ∈ B, 1 := by simp
    _ ≤ ∑ x ∈ B, w x := Finset.sum_le_sum hw

end Erdos547

#print axioms Erdos547.card_reservoir_image_le
