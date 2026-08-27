import Arxiv.Arxiv2411_18291.ShiftedChooseBounds
import Arxiv.Arxiv2411_18291.Incidence
import Mathlib.Probability.Distributions.Uniform

/-! # Uniformly enlarging an entire clique

A shared decoder region is sampled from all supersets of a given clique.
The probability of containing a fixed face depends on its vertices outside
the original clique, with one common factorial constant.
-/

open Finset MeasureTheory

noncomputable section

namespace Arxiv2411_18291

variable {V : Type*} [Fintype V] [DecidableEq V] {q d : ℕ}

def cliqueEnlargements (Q : Block V q) (d : ℕ) : Finset (Block V (q + d)) :=
  univ.filter fun Z => Q.val ⊆ Z.val

theorem cliqueEnlargements_card (Q : Block V q) (d : ℕ) :
    (cliqueEnlargements Q d).card = (Fintype.card V - q).choose d := by
  have h := card_blocks_between (r := q + d) Q.val univ (subset_univ _)
    (by rw [Q.property]; omega)
  simpa only [cliqueEnlargements, subset_univ, and_true, card_univ, Q.property,
    Nat.add_sub_cancel_left] using h

theorem cliqueEnlargements_nonempty (Q : Block V q) (hn : q + d ≤ Fintype.card V) :
    (cliqueEnlargements Q d).Nonempty := by
  rw [← card_pos, cliqueEnlargements_card]
  exact Nat.choose_pos (by omega)

theorem cliqueEnlargements_face_card_le (Q : Block V q) (S : Finset V)
    (hj : (S \ Q.val).card ≤ d) :
    ((cliqueEnlargements Q d).filter fun Z => S ⊆ Z.val).card ≤
      Fintype.card V ^ (d - (S \ Q.val).card) := by
  have hu : (Q.val ∪ S).card = q + (S \ Q.val).card := by
    have h := card_sdiff_add_card S Q.val
    rw [union_comm] at h
    omega
  have heq : (cliqueEnlargements Q d).filter (fun Z => S ⊆ Z.val) =
      univ.filter (fun Z : Block V (q + d) =>
        Q.val ∪ S ⊆ Z.val ∧ Z.val ⊆ univ) := by
    ext Z
    simp only [cliqueEnlargements, mem_filter, mem_univ, true_and, subset_univ,
      and_true, union_subset_iff]
  rw [heq, card_blocks_between _ _ (subset_univ _) (by rw [hu]; omega), card_univ, hu,
    show q + d - (q + (S \ Q.val).card) = d - (S \ Q.val).card by omega]
  exact (Nat.choose_le_pow _ _).trans (Nat.pow_le_pow_left (Nat.sub_le _ _) _)

theorem uniformCliqueEnlargement_face_probability_le (Q : Block V q) (S : Finset V)
    [MeasurableSpace (Block V (q + d))] [MeasurableSingletonClass (Block V (q + d))]
    (hS : S.card ≤ d) (hn : q + d ≤ Fintype.card V) (hnpos : 0 < Fintype.card V)
    (hsize : (d : ℝ) * (q + d) ≤ (Fintype.card V : ℝ) / 2) :
    (PMF.uniformOfFinset (cliqueEnlargements Q d)
      (cliqueEnlargements_nonempty Q hn)).toMeasure.real {Z | S ⊆ Z.val} ≤
        2 * d.factorial / (Fintype.card V : ℝ) ^ (S \ Q.val).card := by
  have hN : (0 : ℝ) < Fintype.card V := by exact_mod_cast hnpos
  have hfac : (0 : ℝ) < d.factorial := by exact_mod_cast Nat.factorial_pos d
  have hj : (S \ Q.val).card ≤ d := (card_le_card sdiff_subset).trans hS
  have hcount : (1 / 2 : ℝ) * (Fintype.card V : ℝ) ^ d / d.factorial ≤
      (cliqueEnlargements Q d).card := by
    rw [cliqueEnlargements_card]
    convert shifted_choose_relative_lower (Fintype.card V) q d
      (by norm_num : (0 : ℝ) ≤ 1 / 2) hn (by linarith only [hsize]) using 1
    norm_num
  rw [measureReal_def, PMF.toMeasure_uniformOfFinset_apply _ _
    (Set.toFinite _).measurableSet, ENNReal.toReal_div, ENNReal.toReal_natCast,
    ENNReal.toReal_natCast]
  simp only [Set.mem_ofPred_eq]
  have hnum : (((cliqueEnlargements Q d).filter fun Z => S ⊆ Z.val).card : ℝ) ≤
      (Fintype.card V : ℝ) ^ (d - (S \ Q.val).card) := by
    exact_mod_cast cliqueEnlargements_face_card_le Q S hj
  calc
    _ ≤ (Fintype.card V : ℝ) ^ (d - (S \ Q.val).card) /
        ((1 / 2 : ℝ) * (Fintype.card V : ℝ) ^ d / d.factorial) :=
      div_le_div₀ (by positivity) hnum (by positivity) hcount
    _ = _ := by
      rw [pow_sub₀ _ hN.ne' hj]
      field_simp

end Arxiv2411_18291
