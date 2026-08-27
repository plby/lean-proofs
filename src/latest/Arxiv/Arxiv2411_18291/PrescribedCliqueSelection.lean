import Arxiv.Arxiv2411_18291.PrescribedCliqueEnlargement
import Arxiv.Arxiv2411_18291.CliqueEnlargementBudget
import Arxiv.Arxiv2411_18291.FiniteChoiceConcentration

/-! # Bounded choices of prescribed cliques without disjointness assumptions -/

open Finset MeasureTheory
open scoped BigOperators

noncomputable section

namespace Arxiv2411_18291

theorem face_power_le_twice_factorial (r : ℕ) : 2 ^ (r + 1) ≤ 2 * (r + 1).factorial := by
  have h : 2 ^ r ≤ (r + 1).factorial := by
    simpa only [Nat.factorial_one, one_mul, show 1 + r = r + 1 by omega] using
      (Nat.factorial_mul_pow_le_factorial (m := 1) (n := r))
  rw [pow_succ]
  nlinarith only [h]

theorem exists_prescribed_clique_selection {V : Type*} [Fintype V] [DecidableEq V]
    {r d t : ℕ} (E : ℕ → Block V (r + 1))
    (C : ℕ → Finset (Block V (r + 1 + d))) {b η : ℝ}
    (hb : 0 ≤ b) (hη : 0 < η) (hn : 0 < Fintype.card V)
    (hC : ∀ i, C i ⊆ cliqueEnlargements (E i) d)
    (hcount : ∀ i, η * (Fintype.card V : ℝ) ^ d ≤ (C i).card)
    (hE : ∀ S : Block V r,
      (familyDegree (fun i : Fin t => E i) S.val : ℝ) ≤ b * Fintype.card V)
    (hfailure : Fintype.card (Block V r) *
      Real.exp (-(2 * (r + 1).factorial * b * Fintype.card V / η / 3)) < 1) :
    ∃ Z : Fin t → Block V (r + 1 + d), (∀ i : Fin t, Z i ∈ C (i : ℕ)) ∧
      ∀ S : Block V r, (familyDegree Z S.val : ℝ) <
        (4 * (r + 1).factorial * b / η) * Fintype.card V := by
  classical
  let : MeasurableSpace (Block V (r + 1 + d)) := ⊤
  have hN : (0 : ℝ) < Fintype.card V := by exact_mod_cast hn
  have hnonempty (i : ℕ) : (C i).Nonempty := by
    rw [← card_pos]
    have hp : (0 : ℝ) < (C i).card := (by positivity : 0 < η *
      (Fintype.card V : ℝ) ^ d).trans_le (hcount i)
    exact_mod_cast hp
  let p : ℕ → PMF (Block V (r + 1 + d)) := fun i => PMF.uniformOfFinset (C i) (hnonempty i)
  let f : Block V r → Block V (r + 1 + d) → ℝ :=
    fun S Z => if S.val ⊆ Z.val then 1 else 0
  have hf : ∀ S Z, 0 ≤ f S Z ∧ f S Z ≤ 1 := by
    intro S Z
    dsimp only [f]
    split_ifs <;> norm_num
  have hmean (i : ℕ) (S : Block V r) : (∫ Z, f S Z ∂(p i).toMeasure) ≤
      (2 / (Fintype.card V : ℝ) ^ (S.val \ (E i).val).card) / η := by
    have heq : f S = {Z : Block V (r + 1 + d) | S.val ⊆ Z.val}.indicator
        (fun _ => (1 : ℝ)) := by
      funext Z
      simp only [f, Set.indicator, Set.mem_ofPred_eq]
    have hi : (∫ Z, f S Z ∂(p i).toMeasure) =
        (p i).toMeasure.real {Z | S.val ⊆ Z.val} := by
      rw [heq]
      exact integral_indicator_one (μ := (p i).toMeasure)
        (s := {Z : Block V (r + 1 + d) | S.val ⊆ Z.val}) (Set.toFinite _).measurableSet
    rw [hi]
    exact (uniform_prescribed_clique_face_probability_le (E i) (C i) (hnonempty i)
      (hC i) hη (hcount i) hn S.val).trans (by gcongr; norm_num)
  have hbudget (S : Block V r) :
      (∑ i ∈ range t, ∫ Z, f S Z ∂(p i).toMeasure) ≤
        2 * (r + 1).factorial * b * Fintype.card V / η := by
    rw [← Fin.sum_univ_eq_sum_range (fun i => ∫ Z, f S Z ∂(p i).toMeasure) t]
    have hsum := sum_enlargement_face_budget (d := 0) (fun i : Fin t => E i)
      (by omega : r ≤ r + 1) hb hn hE S
    simp only [Nat.factorial_zero, Nat.cast_one, mul_one] at hsum
    have hcoef : (2 : ℝ) ^ (r + 1) ≤ 2 * (r + 1).factorial := by
      exact_mod_cast face_power_le_twice_factorial r
    calc
      _ ≤ ∑ i : Fin t, (2 / (Fintype.card V : ℝ) ^ (S.val \ (E i).val).card) / η :=
        sum_le_sum fun i _ => hmean i S
      _ = (∑ i : Fin t, 2 / (Fintype.card V : ℝ) ^ (S.val \ (E i).val).card) / η :=
        (sum_div _ _ _).symm
      _ ≤ (2 ^ (r + 1) * b * Fintype.card V) / η :=
        div_le_div_of_nonneg_right hsum hη.le
      _ ≤ _ := by gcongr
  obtain ⟨start, _⟩ := hnonempty 0
  obtain ⟨Z, hs, hZ⟩ := exists_finite_choices_below_double_budget start p f t hf hbudget hfailure
  refine ⟨Z, ?_, ?_⟩
  · intro i
    have h := hs i
    change Z i ∈ (PMF.uniformOfFinset (C i) (hnonempty i)).support at h
    simpa only [PMF.support_uniformOfFinset, mem_coe] using h
  · intro S
    have hc : (familyDegree Z S.val : ℝ) = ∑ i, f S (Z i) := by
      simp only [familyDegree, f, ← sum_filter, sum_const, nsmul_eq_mul, mul_one]
    rw [hc]
    convert hZ S using 1
    ring

end Arxiv2411_18291
