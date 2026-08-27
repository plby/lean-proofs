import Arxiv.Arxiv2411_18291.UniformCliqueEnlargement
import Arxiv.Arxiv2411_18291.CliqueEnlargementBudget
import Arxiv.Arxiv2411_18291.FiniteChoiceConcentration
import Arxiv.Arxiv2411_18291.CliquePairRootDegrees

/-! # Constructed shared decoder regions with bounded face counts -/

open Finset MeasureTheory
open scoped BigOperators

noncomputable section

namespace Arxiv2411_18291

variable {V : Type*} [Fintype V] [DecidableEq V] {q r d t : ℕ}

theorem exists_indexed_clique_enlargements (E : ℕ → Block V q)
    (hrq : r ≤ q) (hrd : r ≤ d) {b : ℝ} (hb : 0 ≤ b)
    (hn : q + d ≤ Fintype.card V) (hnpos : 0 < Fintype.card V)
    (hsize : (d : ℝ) * (q + d) ≤ (Fintype.card V : ℝ) / 2)
    (hE : ∀ T : Block V r,
      (familyDegree (fun i : Fin t => E i) T.val : ℝ) ≤ b * Fintype.card V)
    (hfailure : Fintype.card (Block V r) *
      Real.exp (-(2 ^ (r + 1) * d.factorial * b * Fintype.card V / 3)) < 1) :
    ∃ Z : Fin t → Block V (q + d), (∀ i : Fin t, (E (i : ℕ)).val ⊆ (Z i).val) ∧
      ∀ S : Block V r, (familyDegree Z S.val : ℝ) <
        (2 ^ (r + 2) * d.factorial * b) * Fintype.card V := by
  classical
  let : MeasurableSpace (Block V (q + d)) := ⊤
  let p : ℕ → PMF (Block V (q + d)) := fun i =>
    PMF.uniformOfFinset (cliqueEnlargements (E i) d)
      (cliqueEnlargements_nonempty (E i) hn)
  let f : Block V r → Block V (q + d) → ℝ := fun S Z => if S.val ⊆ Z.val then 1 else 0
  have hf : ∀ S Z, 0 ≤ f S Z ∧ f S Z ≤ 1 := by
    intro S Z
    dsimp only [f]
    split_ifs <;> norm_num
  have hmean (i : ℕ) (S : Block V r) :
      (∫ Z, f S Z ∂(p i).toMeasure) ≤
        2 * d.factorial / (Fintype.card V : ℝ) ^ (S.val \ (E i).val).card := by
    have heq : f S = {Z : Block V (q + d) | S.val ⊆ Z.val}.indicator (fun _ => (1 : ℝ)) := by
      funext Z
      simp only [f, Set.indicator, Set.mem_ofPred_eq]
    have hi : (∫ Z, f S Z ∂(p i).toMeasure) =
        (p i).toMeasure.real {Z | S.val ⊆ Z.val} := by
      rw [heq]
      exact integral_indicator_one (μ := (p i).toMeasure)
        (s := {Z : Block V (q + d) | S.val ⊆ Z.val}) (Set.toFinite _).measurableSet
    rw [hi]
    exact uniformCliqueEnlargement_face_probability_le (E i) S.val
      (by rw [S.property]; exact hrd) hn hnpos hsize
  have hbudget (S : Block V r) :
      (∑ i ∈ range t, ∫ Z, f S Z ∂(p i).toMeasure) ≤
        2 ^ (r + 1) * d.factorial * b * Fintype.card V := by
    rw [← Fin.sum_univ_eq_sum_range (fun i => ∫ Z, f S Z ∂(p i).toMeasure) t]
    exact (sum_le_sum fun (i : Fin t) _ => hmean i S).trans
      (sum_enlargement_face_budget (d := d) (fun i : Fin t => E i) hrq hb hnpos hE S)
  obtain ⟨start, _⟩ := cliqueEnlargements_nonempty (E 0) hn
  obtain ⟨Z, hs, hZ⟩ := exists_finite_choices_below_double_budget start p f t hf hbudget hfailure
  refine ⟨Z, ?_, ?_⟩
  · intro i
    have h := hs i
    change Z i ∈ (PMF.uniformOfFinset (cliqueEnlargements (E i) d)
      (cliqueEnlargements_nonempty (E i) hn)).support at h
    rw [PMF.support_uniformOfFinset] at h
    exact (mem_filter.mp h).2
  · intro S
    have hc : (familyDegree Z S.val : ℝ) = ∑ i, f S (Z i) := by
      simp only [familyDegree, f, ← sum_filter, sum_const, nsmul_eq_mul, mul_one]
    rw [hc]
    convert hZ S using 1
    rw [show r + 2 = (r + 1) + 1 by omega, pow_succ]
    ring

theorem exists_clique_enlargements_of_boundary_bound
    (D : Finset (Block V q)) (hrq : r < q) (hrd : r ≤ d) {θ : ℝ} (hθ : 0 ≤ θ)
    (hD : IsCliqueFamilyBounded r D θ)
    (hn : q + d ≤ Fintype.card V) (hnpos : 0 < Fintype.card V)
    (hsize : (d : ℝ) * (q + d) ≤ (Fintype.card V : ℝ) / 2)
    (hfailure : Fintype.card (Block V r) *
      Real.exp (-(2 ^ (r + 1) * d.factorial * (θ / (q - r : ℕ)) * Fintype.card V / 3)) <
        1) :
    ∃ Z : D → Block V (q + d), (∀ Q, Q.val.val ⊆ (Z Q).val) ∧
      ∀ S : Block V r, (familyDegree Z S.val : ℝ) <
        (2 ^ (r + 2) * d.factorial * (θ / (q - r : ℕ))) * Fintype.card V := by
  classical
  obtain ⟨a, _, ha⟩ := exists_subset_card_eq (s := (univ : Finset V))
    (by simpa only [card_univ] using (show q ≤ Fintype.card V by omega))
  let Q₀ : Block V q := ⟨a, ha⟩
  let enum : Fin D.card ≃ D := D.equivFin.symm
  let E : ℕ → Block V q := fun i => if hi : i < D.card then (enum ⟨i, hi⟩).val else Q₀
  have hE (i : Fin D.card) : E i = (enum i).val := by
    dsimp only [E]
    rw [dif_pos i.isLt]
  have hroots (T : Block V r) :
      (familyDegree (fun i : Fin D.card => E i) T.val : ℝ) ≤
        (θ / (q - r : ℕ)) * Fintype.card V := by
    simp only [hE, familyDegree_reindex, familyDegree_subtype_eq]
    simpa only [T.property, Nat.add_sub_cancel_left, pow_one] using
      hD.clique_degree_le hrq hθ T.val T.property.le
  obtain ⟨Z, hs, hZ⟩ := exists_indexed_clique_enlargements E hrq.le hrd
    (div_nonneg hθ (Nat.cast_nonneg _)) hn hnpos hsize hroots hfailure
  refine ⟨fun Q => Z (enum.symm Q), ?_, ?_⟩
  · intro Q
    have h := hs (enum.symm Q)
    simpa only [hE, Equiv.apply_symm_apply] using h
  · intro S
    simpa only [familyDegree_reindex] using hZ S

end Arxiv2411_18291
