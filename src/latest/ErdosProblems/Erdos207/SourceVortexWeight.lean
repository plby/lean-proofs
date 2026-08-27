/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.SourceVortexWellSpread
import ErdosProblems.Erdos207.VortexWeight

/-! # Exact signed-profile cancellation and multiplicity-preserving weights -/

namespace Erdos207

open Finset
open scoped NNReal

noncomputable section

theorem Vortex.level_card_pos_of_terminal
    {V : Type*} [Fintype V] [DecidableEq V] {ell : ℕ}
    (W : Vortex V ell) (hn : 0 < W.terminalSize) (i : Fin (ell + 1)) :
    0 < (W.U i).card :=
  hn.trans_le (card_le_card (W.antitone i (Fin.last ell) (Fin.le_last i)))

theorem Vortex.sourceProfileScale_mul_weight
    {V : Type*} [Fintype V] [DecidableEq V] {ell d f : ℕ}
    (W : Vortex V ell) (w : ℝ≥0) (t : VortexProfile ell)
    (hn : 0 < W.terminalSize) (ht : t.mass ≤ f) :
    W.sourceProfileScale d t * vortexProfileWeight W w f t =
      w ^ f * (W.terminalSize : ℝ≥0) ^ d / (W.terminalSize : ℝ≥0) ^ f := by
  have hn0 : (W.terminalSize : ℝ≥0) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
  calc
    _ = ((W.profileScale t : ℝ≥0) *
        (∏ i : Fin ell, (w / (W.U i.castSucc).card) ^ t i)) *
        w ^ (f - t.mass) * (W.terminalSize : ℝ≥0) ^ d /
        ((W.terminalSize : ℝ≥0) ^ t.mass *
          (W.terminalSize : ℝ≥0) ^ (f - t.mass)) := by
      unfold sourceProfileScale vortexProfileWeight
      rw [div_pow]
      field_simp
    _ = _ := by
      rw [W.profileScale_mul_outerWeight w t
        (fun i ↦ W.level_card_pos_of_terminal hn i.castSucc)]
      rw [← pow_add, ← pow_add, Nat.add_sub_of_le ht]

theorem Vortex.weight_sum_le_of_profile_count
    {V α : Type*} [Fintype V] [DecidableEq V] [DecidableEq α]
    {ell d f : ℕ} (W : Vortex V ell) (I : Finset α)
    (A : α → TripleSystemOn V) (w b : ℝ≥0)
    (hn : 0 < W.terminalSize) (hcard : ∀ x ∈ I, (A x).card = f)
    (hcount : ∀ t : VortexProfile ell,
      ((I.filter fun x ↦ W.outerProfile (A x) = t).card : ℝ≥0) ≤
        b * W.sourceProfileScale d t) :
    ∑ x ∈ I, setWeight (vortexTripleWeight W w) (A x) ≤
      ((f + 1) ^ ell : ℕ) * b * w ^ f *
        (W.terminalSize : ℝ≥0) ^ d / (W.terminalSize : ℝ≥0) ^ f := by
  let code := fun x ↦ W.outerProfile (A x)
  let target := b * w ^ f * (W.terminalSize : ℝ≥0) ^ d /
    (W.terminalSize : ℝ≥0) ^ f
  have hprofile : ∀ t ∈ I.image code,
      ∑ x ∈ I.filter (fun x ↦ code x = t),
        setWeight (vortexTripleWeight W w) (A x) ≤ target := by
    intro t ht
    obtain ⟨x, hx, hxt⟩ := mem_image.mp ht
    have hmass : t.mass ≤ f := by
      rw [← hxt]
      exact (W.outerProfile_mass_le_card (A x)).trans_eq (hcard x hx)
    calc
      _ = ((I.filter fun x ↦ code x = t).card : ℝ≥0) *
          vortexProfileWeight W w f t := by
        calc
          _ = ∑ _x ∈ I.filter (fun x ↦ code x = t),
              vortexProfileWeight W w f t := by
            apply sum_congr rfl
            intro x hx
            have hm := mem_filter.mp hx
            rw [setWeight_vortexTripleWeight_eq_profileWeight W w (A x) t hm.2,
              hcard x hm.1]
          _ = _ := by simp
      _ ≤ (b * W.sourceProfileScale d t) * vortexProfileWeight W w f t :=
        mul_le_mul_of_nonneg_right (hcount t) zero_le
      _ = target := by
        rw [mul_assoc, W.sourceProfileScale_mul_weight w t hn hmass]
        dsimp only [target]
        ring
  have hbox : I.image code ⊆ vortexProfileBox ell f := by
    intro t ht
    obtain ⟨x, hx, rfl⟩ := mem_image.mp ht
    rw [mem_vortexProfileBox_iff]
    intro i
    exact (W.outerProfile_apply_le_card (A x) i).trans_eq (hcard x hx)
  calc
    _ = ∑ t ∈ I.image code, ∑ x ∈ I.filter (fun x ↦ code x = t),
        setWeight (vortexTripleWeight W w) (A x) := by
      symm
      apply sum_fiberwise_of_maps_to
      intro x hx
      exact mem_image_of_mem code hx
    _ ≤ ∑ _t ∈ I.image code, target := sum_le_sum hprofile
    _ = ((I.image code).card : ℝ≥0) * target := by simp
    _ ≤ (((f + 1) ^ ell : ℕ) : ℝ≥0) * target := by
      apply mul_le_mul_of_nonneg_right _ zero_le
      exact_mod_cast (card_le_card hbox).trans_eq (card_vortexProfileBox ell f)
    _ = _ := by dsimp only [target]; ring

end

end Erdos207
