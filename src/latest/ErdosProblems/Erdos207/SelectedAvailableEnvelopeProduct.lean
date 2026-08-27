/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.InhomogeneousSelectedUncoveredProduct
import ErdosProblems.Erdos207.SelectedAvailableUncoveredTransfer

/-!
# Product bound for the selected/available transfer envelope

If the raw insertion hazard is bounded by a full one-step survival factor
times `rho`, then the transfer recurrence has the correct retrospective
scale.  A triangle selected at time `i` has survived as an available
triangle during all earlier transitions, producing the factor
`cumulativeSurvival theta i ^ 3`.  The residual graph edges retain the full
survival product through the terminal time.
-/

namespace Erdos207

open Finset
open scoped BigOperators NNReal

noncomputable section

lemma sdiff_erase_eq_insert_sdiff
    {W : Type*} [DecidableEq W]
    {Q S : Finset W} {x : W} (hx : x ∈ S) (hSQ : S ⊆ Q) :
    Q \ S.erase x = insert x (Q \ S) := by
  ext y
  simp only [mem_sdiff, mem_erase, mem_insert]
  constructor
  · rintro ⟨hyQ, hnot⟩
    by_cases hyx : y = x
    · exact Or.inl hyx
    · exact Or.inr ⟨hyQ, fun hyS ↦ hnot ⟨hyx, hyS⟩⟩
  · rintro (rfl | ⟨hyQ, hyS⟩)
    · exact ⟨hSQ hx, by simp⟩
    · exact ⟨hyQ, fun h ↦ hyS h.2⟩

lemma card_sdiff_erase_of_mem_subset
    {W : Type*} [DecidableEq W]
    {Q S : Finset W} {x : W} (hx : x ∈ S) (hSQ : S ⊆ Q) :
    (Q \ S.erase x).card = (Q \ S).card + 1 := by
  rw [sdiff_erase_eq_insert_sdiff hx hSQ, card_insert_of_notMem]
  simp [hx]

/-- The cumulative retrospective point weight for a selected triangle. -/
def transferPointWeight (theta rho : ℕ → ℝ≥0) (t : ℕ) : ℝ≥0 :=
  ∑ i ∈ range t, rho i * cumulativeSurvival theta i ^ 3

@[simp]
lemma transferPointWeight_zero (theta rho : ℕ → ℝ≥0) :
    transferPointWeight theta rho 0 = 0 := by
  simp [transferPointWeight]

lemma transferPointWeight_succ (theta rho : ℕ → ℝ≥0) (t : ℕ) :
    transferPointWeight theta rho (t + 1) =
      transferPointWeight theta rho t +
        rho t * cumulativeSurvival theta t ^ 3 := by
  simp [transferPointWeight, sum_range_succ]

/-- Closed product upper bound for the exact transfer recurrence. -/
theorem selectedAvailableUncoveredEnvelope_le_product
    {W : Type*} [DecidableEq W]
    (delta theta rho : ℕ → ℝ≥0) (Q : Finset W) (b : ℕ)
    (htheta : ∀ i, theta i ≤ 1)
    (hadjust : ∀ i,
      delta i ≤ theta i ^ (3 * Q.card + b) * rho i) :
    ∀ (t : ℕ) (S : Finset W), S ⊆ Q →
      selectedAvailableUncoveredEnvelope delta theta Q b t S ≤
        cumulativeSurvival theta t ^ (3 * (Q \ S).card + b) *
          setWeight (fun _ ↦ transferPointWeight theta rho t) S := by
  classical
  intro t
  induction t with
  | zero =>
      intro S hSQ
      by_cases hS : S = ∅
      · subst S
        simp [setWeight]
      · have hcard : S.card ≠ 0 := card_ne_zero.mpr
          (nonempty_iff_ne_empty.mpr hS)
        simp [selectedAvailableUncoveredEnvelope, hS, setWeight, hcard]
  | succ t ih =>
      intro S hSQ
      let w : ℕ := 3 * (Q \ S).card + b
      let c : ℝ≥0 := cumulativeSurvival theta t
      let pi : W → ℝ≥0 := fun _ ↦ transferPointWeight theta rho t
      let r : ℝ≥0 := rho t * c ^ 3
      have hw : w ≤ 3 * Q.card + b := by
        dsimp only [w]
        have hcard : (Q \ S).card ≤ Q.card := card_le_card sdiff_subset
        omega
      have hthetaPow : theta t ^ (3 * Q.card + b) ≤ theta t ^ w :=
        pow_le_pow_right_of_le_one' (htheta t) hw
      have hdelta : delta t ≤ theta t ^ w * rho t := by
        apply (hadjust t).trans
        gcongr
      have hmain :
          selectedAvailableUncoveredEnvelope delta theta Q b t S ≤
            c ^ w * setWeight pi S := by
        simpa only [c, w, pi] using ih S hSQ
      have herase : ∀ x ∈ S,
          selectedAvailableUncoveredEnvelope delta theta Q b t (S.erase x) ≤
            c ^ (w + 3) * setWeight pi (S.erase x) := by
        intro x hx
        have hsub : S.erase x ⊆ Q := (erase_subset x S).trans hSQ
        have hi := ih (S.erase x) hsub
        rw [card_sdiff_erase_of_mem_subset hx hSQ] at hi
        have hexp : 3 * ((Q \ S).card + 1) + b = w + 3 := by
          dsimp only [w]
          omega
        rw [hexp] at hi
        simpa only [c, pi] using hi
      have hfirst :
          theta t ^ w *
              selectedAvailableUncoveredEnvelope delta theta Q b t S ≤
            (c * theta t) ^ w * setWeight pi S := by
        calc
          theta t ^ w *
                selectedAvailableUncoveredEnvelope delta theta Q b t S ≤
              theta t ^ w * (c ^ w * setWeight pi S) := by gcongr
          _ = (c * theta t) ^ w * setWeight pi S := by
            rw [mul_pow]
            ring
      have htransfer : ∀ x ∈ S,
          delta t *
              selectedAvailableUncoveredEnvelope delta theta Q b t
                (S.erase x) ≤
            (c * theta t) ^ w *
              (r * setWeight pi (S.erase x)) := by
        intro x hx
        calc
          delta t *
                selectedAvailableUncoveredEnvelope delta theta Q b t
                  (S.erase x) ≤
              (theta t ^ w * rho t) *
                (c ^ (w + 3) * setWeight pi (S.erase x)) := by
            gcongr
            exact herase x hx
          _ = (c * theta t) ^ w *
                (r * setWeight pi (S.erase x)) := by
            simp only [r, pow_add, mul_pow]
            ring
      rw [selectedAvailableUncoveredEnvelope_succ]
      calc
        theta t ^ w *
              selectedAvailableUncoveredEnvelope delta theta Q b t S +
            ∑ x ∈ S, delta t *
              selectedAvailableUncoveredEnvelope delta theta Q b t
                (S.erase x) ≤
            (c * theta t) ^ w * setWeight pi S +
              ∑ x ∈ S, (c * theta t) ^ w *
                (r * setWeight pi (S.erase x)) := by
          exact add_le_add hfirst (sum_le_sum fun x hx ↦ htransfer x hx)
        _ = (c * theta t) ^ w *
              (setWeight pi S +
                ∑ x ∈ S, r * setWeight pi (S.erase x)) := by
          rw [mul_add, mul_sum]
        _ ≤ (c * theta t) ^ w *
              setWeight (fun x ↦ pi x + r) S := by
          gcongr
          exact setWeight_add_singletons_le pi (fun _ ↦ r) S
        _ = cumulativeSurvival theta (t + 1) ^
                (3 * (Q \ S).card + b) *
              setWeight
                (fun _ ↦ transferPointWeight theta rho (t + 1)) S := by
          simp only [c, w, pi, r, cumulativeSurvival_succ,
            transferPointWeight_succ]

end

end Erdos207
