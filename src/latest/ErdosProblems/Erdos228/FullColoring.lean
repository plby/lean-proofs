/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex, Boris Alexeev
-/
import ErdosProblems.Erdos228.Discrepancy

/-!
# From partial colourings to full colourings

This file formalizes the deterministic iteration in Corollary 4.2 of
Balister--Bollobás--Morris--Sahasrabudhe--Tiba.  The probabilistic
partial-colouring theorem is an explicit argument of the final theorem.
-/

open scoped BigOperators

noncomputable section

namespace Erdos228.Discrepancy

universe uI uJ

variable {I : Type uI} {J : Type uJ} [Fintype I] [Fintype J]

/-- The parameter used for the recursively coloured half of the coordinates. -/
def nextParameter (d : ℕ) (c : J → ℝ) : J → ℝ :=
  fun j ↦ Real.sqrt (c j ^ 2 + 196 * Real.log ((d : ℝ) / (d / 2 : ℕ)))

omit [Fintype J] in
theorem nextParameter_nonneg (d : ℕ) (c : J → ℝ) :
    ∀ j, 0 ≤ nextParameter d c j := fun _ ↦ Real.sqrt_nonneg _

theorem half_pos {d : ℕ} (hd : 900 < d) : 0 < d / 2 := by omega

theorem half_lt {d : ℕ} (hd : 900 < d) : d / 2 < d := by omega

theorem half_ratio_one_le {d : ℕ} (hd : 900 < d) :
    (1 : ℝ) ≤ (d : ℝ) / (d / 2 : ℕ) := by
  have hq : 0 < ((d / 2 : ℕ) : ℝ) := by exact_mod_cast half_pos hd
  rw [le_div_iff₀ hq]
  norm_num
  exact_mod_cast (show d / 2 ≤ d by omega)

omit [Fintype J] in
theorem nextParameter_sq {d : ℕ} (hd : 900 < d) (c : J → ℝ) (j : J) :
    nextParameter d c j ^ 2 =
      c j ^ 2 + 196 * Real.log ((d : ℝ) / (d / 2 : ℕ)) := by
  rw [nextParameter, Real.sq_sqrt]
  have hlog : 0 ≤ Real.log ((d : ℝ) / (d / 2 : ℕ)) :=
    Real.log_nonneg (half_ratio_one_le hd)
  positivity

omit [Fintype J] in
theorem nextParameter_exp_identity {d : ℕ} (hd : 900 < d)
    (c : J → ℝ) (j : J) :
    Real.exp (-(nextParameter d c j) ^ 2 / 196) =
      Real.exp (-(c j) ^ 2 / 196) * ((d / 2 : ℕ) : ℝ) / d := by
  have hdR : (0 : ℝ) < d := by exact_mod_cast (show 0 < d by omega)
  have hqR : (0 : ℝ) < (d / 2 : ℕ) := by exact_mod_cast half_pos hd
  rw [nextParameter_sq hd]
  rw [show -(c j ^ 2 + 196 * Real.log ((d : ℝ) / (d / 2 : ℕ))) / 196 =
      -(c j) ^ 2 / 196 - Real.log ((d : ℝ) / (d / 2 : ℕ)) by ring]
  rw [Real.exp_sub, Real.exp_log (div_pos hdR hqR)]
  field_simp

theorem nextParameter_budget {d : ℕ} (hd : 900 < d) (c : J → ℝ)
    (hbudget : (∑ j, Real.exp (-(c j) ^ 2 / 196)) ≤ (d : ℝ) / 16) :
    (∑ j, Real.exp (-(nextParameter d c j) ^ 2 / 196)) ≤
      ((d / 2 : ℕ) : ℝ) / 16 := by
  simp_rw [nextParameter_exp_identity hd]
  simp_rw [mul_div_assoc]
  rw [← Finset.sum_mul]
  have hfactor : 0 ≤ (((d / 2 : ℕ) : ℝ) / d) := by positivity
  calc
    (∑ j, Real.exp (-(c j) ^ 2 / 196)) * (((d / 2 : ℕ) : ℝ) / d)
        ≤ ((d : ℝ) / 16) * (((d / 2 : ℕ) : ℝ) / d) := by
          exact mul_le_mul_of_nonneg_right hbudget hfactor
    _ = ((d / 2 : ℕ) : ℝ) / 16 := by
      have hd0 : (d : ℝ) ≠ 0 := by positivity
      field_simp

/-- Extend a vector on the as-yet-unfixed coordinates by zero dummy
coordinates, up to exactly `q` coordinates. -/
def padVector [DecidableEq I] (F : Finset I) (q : ℕ) (v : I → ℝ) :
    Sum ↥(Fᶜ : Finset I) (Fin (q - Fᶜ.card)) → ℝ
  | Sum.inl i => v i
  | Sum.inr _ => 0

/-- Extend a cube point on the as-yet-unfixed coordinates by zero dummy
coordinates. -/
def padPoint [DecidableEq I] (F : Finset I) (q : ℕ) (x : I → ℝ) :
    Sum ↥(Fᶜ : Finset I) (Fin (q - Fᶜ.card)) → ℝ
  | Sum.inl i => x i
  | Sum.inr _ => 0

theorem inCube_padPoint [DecidableEq I] (F : Finset I) (q : ℕ)
    {x : I → ℝ} (hx : InCube x) : InCube (padPoint F q x) := by
  intro i
  cases i with
  | inl i => simpa [padPoint] using hx i
  | inr i => simp [padPoint]

theorem norm_padVector_le [DecidableEq I] (F : Finset I) (q : ℕ)
    (v : I → ℝ) : ‖padVector F q v‖ ≤ ‖v‖ := by
  rw [pi_norm_le_iff_of_nonneg (norm_nonneg _)]
  intro i
  cases i with
  | inl i => simpa [padVector] using norm_le_pi_norm v i
  | inr i => simp [padVector]

theorem card_pad [DecidableEq I] (F : Finset I) (q : ℕ)
    (hcard : Fᶜ.card ≤ q) :
    Fintype.card (Sum ↥(Fᶜ : Finset I) (Fin (q - Fᶜ.card))) = q := by
  rw [Fintype.card_sum, Fintype.card_coe, Fintype.card_fin,
    Nat.add_sub_of_le hcard]

theorem dot_pad_sub [DecidableEq I] (F : Finset I) (q : ℕ)
    (y : Sum ↥(Fᶜ : Finset I) (Fin (q - Fᶜ.card)) → ℝ)
    (x v : I → ℝ) :
    dot (y - padPoint F q x) (padVector F q v) =
      dot (fun i : ↥(Fᶜ : Finset I) ↦ y (Sum.inl i) - x i)
        (restrictOutside F v) := by
  simp [dot, padPoint, padVector, restrictOutside]

theorem fixed_restrict_isSign [DecidableEq I] (x : I → ℝ) :
    IsSign (restrict (fixedCoordinates x) x) := by
  intro i
  have hi : |x i| = 1 := by
    simpa [fixedCoordinates] using i.property
  simpa [restrict] using (abs_eq (by norm_num : (0 : ℝ) ≤ 1)).mp hi

theorem card_compl_fixed_le_half [DecidableEq I] {x : I → ℝ}
    (hfixed : Fintype.card I ≤ 2 * (fixedCoordinates x).card) :
    (fixedCoordinates x)ᶜ.card ≤ Fintype.card I / 2 := by
  rw [Finset.card_compl]
  omega

theorem dot_glue_sub_same_fixed [DecidableEq I] (F : Finset I)
    (xF : F → ℝ) (xOutside yOutside : ↥(Fᶜ : Finset I) → ℝ)
    (v : I → ℝ) :
    dot (glue F xF yOutside - glue F xF xOutside) v =
      dot (yOutside - xOutside) (restrictOutside F v) := by
  rw [dot_sub_left, dot_glue, dot_glue, dot_sub_left]
  ring

/-- BBMST Corollary 4.2.  This is the complete deterministic iteration; its
only non-elementary input is the supplied Lovett--Meka partial-colouring
principle, explicitly quantified over every finite coordinate type used by
the recursion. -/
theorem hasFullColoring_of_partialColoringPrinciple
    (hLM : ∀ (K : Type uI) [Fintype K] [DecidableEq K],
      PartialColoringPrinciple K J)
    (v : J → I → ℝ) (x₀ : I → ℝ) (c : J → ℝ)
    (hx₀ : InCube x₀) (hc : ∀ j, 0 ≤ c j)
    (hbudget : (∑ j, Real.exp (-(c j) ^ 2 / 196)) ≤
      (Fintype.card I : ℝ) / 16) :
    HasFullColoring v x₀ c := by
  classical
  generalize hdcard : Fintype.card I = d at hbudget ⊢
  induction d using Nat.strong_induction_on generalizing I c with
  | h d ih =>
      by_cases hdsmall : d ≤ 900
      · exact hasFullColoring_of_card_le_900 v x₀ c hx₀ hc
          (hdcard.trans_le hdsmall)
      · have hdlarge : 900 < d := by omega
        have hbudgetI :
            (∑ j, Real.exp (-(c j) ^ 2 / 196)) ≤
              (Fintype.card I : ℝ) / 16 := by simpa [hdcard] using hbudget
        obtain ⟨x, hxCube, hxFixed, hxError⟩ :=
          partialColoring_step (hLM I) v x₀ c hx₀ hc hbudgetI
        let F : Finset I := fixedCoordinates x
        let q : ℕ := d / 2
        have hFcard : Fᶜ.card ≤ q := by
          dsimp only [F, q]
          have hhalf := card_compl_fixed_le_half hxFixed
          simpa [hdcard] using hhalf
        let K := Sum ↥(Fᶜ : Finset I) (Fin (q - Fᶜ.card))
        let vK : J → K → ℝ := fun j ↦ padVector F q (v j)
        let xK : K → ℝ := padPoint F q x
        have hcardK : Fintype.card K = q := by
          exact card_pad F q hFcard
        have hq_lt : q < d := by
          dsimp only [q]
          exact half_lt hdlarge
        have hxK : InCube xK := inCube_padPoint F q hxCube
        have hbudgetK :
            (∑ j, Real.exp (-(nextParameter d c j) ^ 2 / 196)) ≤
              (Fintype.card K : ℝ) / 16 := by
          rw [hcardK]
          exact nextParameter_budget hdlarge c hbudget
        have hrecursive : HasFullColoring vK xK (nextParameter d c) := by
          apply ih q hq_lt (I := K) vK xK (nextParameter d c) hxK
            (nextParameter_nonneg d c) hcardK
          simpa [hcardK] using hbudgetK
        obtain ⟨yK, hyKSign, hyKError⟩ := hrecursive
        let yOutside : ↥(Fᶜ : Finset I) → ℝ := fun i ↦ yK (Sum.inl i)
        let y : I → ℝ := glue F (restrict F x) yOutside
        have hyOutsideSign : IsSign yOutside := fun i ↦ hyKSign (Sum.inl i)
        have hySign : IsSign y := by
          exact isSign_glue F (fixed_restrict_isSign x) hyOutsideSign
        refine ⟨y, hySign, ?_⟩
        intro j
        have hpartial :
            |dot (x - x₀) (v j)| ≤
              (2 * c j / 7 * Real.sqrt d) * ‖v j‖ := by
          calc
            |dot (x - x₀) (v j)|
                ≤ partialParameter c j * l2Norm (v j) := hxError j
            _ ≤ partialParameter c j *
                (Real.sqrt (Fintype.card I) * ‖v j‖) := by
                  exact mul_le_mul_of_nonneg_left
                    (l2Norm_le_sqrt_card_mul_norm (v j))
                    (partialParameter_nonneg hc j)
            _ = (2 * c j / 7 * Real.sqrt d) * ‖v j‖ := by
                  simp [partialParameter, hdcard]
                  ring
        have hvKnorm : ‖vK j‖ ≤ ‖v j‖ := norm_padVector_le F q (v j)
        have hrecursiveError :
            |dot (yK - xK) (vK j)| ≤
              ((nextParameter d c j + 30) * Real.sqrt q) * ‖v j‖ := by
          calc
            |dot (yK - xK) (vK j)|
                ≤ (nextParameter d c j + 30) *
                    Real.sqrt (Fintype.card K) * ‖vK j‖ := hyKError j
            _ = ((nextParameter d c j + 30) * Real.sqrt q) * ‖vK j‖ := by
                  rw [hcardK]
            _ ≤ ((nextParameter d c j + 30) * Real.sqrt q) * ‖v j‖ := by
                  exact mul_le_mul_of_nonneg_left hvKnorm
                    (mul_nonneg (by linarith [nextParameter_nonneg d c j])
                      (Real.sqrt_nonneg _))
        have hyxDot :
            dot (y - x) (v j) = dot (yK - xK) (vK j) := by
          calc
            dot (y - x) (v j) =
                dot (yOutside - restrictOutside F x) (restrictOutside F (v j)) := by
              change dot (glue F (restrict F x) yOutside - x) (v j) = _
              rw [dot_sub_left, dot_glue, dot_restrict_add_outside F x,
                dot_sub_left]
              ring
            _ = dot (yK - xK) (vK j) := by
              symm
              exact dot_pad_sub F q yK x (v j)
        have hyx :
            |dot (y - x) (v j)| ≤
              ((nextParameter d c j + 30) * Real.sqrt q) * ‖v j‖ := by
          rw [hyxDot]
          exact hrecursiveError
        have hsplit :
            dot (y - x₀) (v j) = dot (x - x₀) (v j) + dot (y - x) (v j) := by
          rw [dot_sub_left, dot_sub_left, dot_sub_left]
          ring
        rw [hsplit]
        calc
          |dot (x - x₀) (v j) + dot (y - x) (v j)|
              ≤ |dot (x - x₀) (v j)| + |dot (y - x) (v j)| := abs_add_le _ _
          _ ≤ (2 * c j / 7 * Real.sqrt d) * ‖v j‖ +
                ((nextParameter d c j + 30) * Real.sqrt q) * ‖v j‖ :=
              add_le_add hpartial hyx
          _ = (2 * c j / 7 * Real.sqrt d +
                (nextParameter d c j + 30) * Real.sqrt q) * ‖v j‖ := by ring
          _ ≤ ((c j + 30) * Real.sqrt d) * ‖v j‖ := by
              exact mul_le_mul_of_nonneg_right
                (by simpa [nextParameter, q] using
                  induction_constant_inequality d (c j) hdlarge (hc j))
                (norm_nonneg _)
          _ = (c j + 30) * Real.sqrt (Fintype.card I) * ‖v j‖ := by
              rw [hdcard]

end Erdos228.Discrepancy
