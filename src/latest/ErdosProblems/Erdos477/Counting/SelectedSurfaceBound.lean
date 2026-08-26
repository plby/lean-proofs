/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Combining the determinant cover and the cylinder bounds for the selected sextic points.
Formal author: Codex.
-/

import ErdosProblems.Erdos477.Counting.LowCylinderBound
import ErdosProblems.Erdos477.Geometry.LowCylinderCover

namespace Erdos477.Counting

open Erdos477.Geometry
open scoped BigOperators

theorem exists_positive_surface_log_bound (c : ℤ) (hc : c ∉ PowerValues 6) :
    ∃ M : ℝ, 0 < M ∧ ∀ B : ℝ, 1 ≤ B → ∀ S : Finset (Fin 3 → ℤ),
      (∀ z ∈ S, IntegerDiagonalPoint c z ∧ 1 ≤ z 1) →
      (∀ z ∈ S, ∀ i, |(z i : ℝ)| ≤ B) →
      (S.card : ℝ) ≤ M * B ^ ((82 : ℝ) / 100) * (Real.log B + 1) := by
  classical
  have hc0 : c ≠ 0 := by intro h; exact hc ⟨0, by simp [h]⟩
  obtain ⟨A, hA, hcover⟩ := exists_low_degree_cylinder_cover (K := ℂ) c hc0
  obtain ⟨L, hL, hcurve⟩ := exists_low_cylinder_bound (K := ℂ) ((1 : ℝ) / 100) (by norm_num)
  refine ⟨A * (1 + L), by positivity, ?_⟩
  intro B hB S hS hheight
  have hB0 : 0 < B := by linarith
  have hlog : 0 ≤ Real.log B := Real.log_nonneg hB
  obtain ⟨C, E, hC, hCcard, _, hCE, hEcard⟩ := hcover B hB S (by
    intro z hz
    exact (mem_sexticBox c B z).mpr ⟨(hS z hz).1.2.2.2, hheight z hz⟩)
    (fun z hz => (hS z hz).1.nonnegative 0)
  let U := fun P : MvPolynomial (Fin 2) ℂ =>
    S.filter (fun z => MvPolynomial.eval ![(z 1 : ℂ), (z 2 : ℂ)] P = 0)
  have heach (P) (hPC : P ∈ C) :
      ((U P).card : ℝ) ≤ L * B ^ ((1 : ℝ) / 3 + 1 / 100) :=
    hcurve c hc P (hC P hPC).1 (hC P hPC).2 B hB (U P)
      (fun z hz => hS z (Finset.mem_filter.mp hz).1)
      (fun _ hz => (Finset.mem_filter.mp hz).2)
      (fun z hz => hheight z (Finset.mem_filter.mp hz).1)
  have hsub : S ⊆ E ∪ C.biUnion U := by
    intro z hz
    rcases hCE z hz with hE | ⟨P, hPC, hzero⟩
    · exact Finset.mem_union_left _ hE
    · exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr
        ⟨P, hPC, Finset.mem_filter.mpr ⟨hz, hzero⟩⟩)
  have hnat : S.card ≤ E.card + ∑ P ∈ C, (U P).card :=
    (Finset.card_le_card hsub).trans ((Finset.card_union_le _ _).trans
      (Nat.add_le_add_left Finset.card_biUnion_le _))
  have hreal : (S.card : ℝ) ≤ E.card + ∑ P ∈ C, ((U P).card : ℝ) := by exact_mod_cast hnat
  have hpower : B ^ ((41 : ℝ) / 100) * B ^ ((1 : ℝ) / 3 + 1 / 100) ≤
      B ^ ((82 : ℝ) / 100) := by
    rw [← Real.rpow_add hB0]
    exact Real.rpow_le_rpow_of_exponent_le hB (by norm_num)
  calc
    _ ≤ E.card + ∑ P ∈ C, ((U P).card : ℝ) := hreal
    _ ≤ E.card + (C.card : ℝ) * (L * B ^ ((1 : ℝ) / 3 + 1 / 100)) := by
      rw [← nsmul_eq_mul, ← Finset.sum_const]
      exact add_le_add le_rfl (Finset.sum_le_sum heach)
    _ ≤ A * B ^ ((82 : ℝ) / 100) * (Real.log B + 1) +
        (A * B ^ ((41 : ℝ) / 100)) * (L * B ^ ((1 : ℝ) / 3 + 1 / 100)) :=
      add_le_add hEcard (mul_le_mul_of_nonneg_right hCcard (by positivity))
    _ = A * B ^ ((82 : ℝ) / 100) * (Real.log B + 1) +
        A * L * (B ^ ((41 : ℝ) / 100) * B ^ ((1 : ℝ) / 3 + 1 / 100)) := by ring
    _ ≤ A * B ^ ((82 : ℝ) / 100) * (Real.log B + 1) + A * L * B ^ ((82 : ℝ) / 100) :=
      add_le_add le_rfl (mul_le_mul_of_nonneg_left hpower (mul_nonneg hA.le hL.le))
    _ ≤ _ := by
      have hp := mul_nonneg (mul_nonneg (mul_nonneg hA.le hL.le)
        (Real.rpow_nonneg hB0.le ((82 : ℝ) / 100))) hlog
      nlinarith

lemma log_add_one_le_small_power (B : ℝ) (hB : 1 ≤ B) :
    Real.log B + 1 ≤ 100 * B ^ ((1 : ℝ) / 100) := by
  have hB0 : 0 < B := by linarith
  have h := Real.log_le_sub_one_of_pos (Real.rpow_pos_of_pos hB0 ((1 : ℝ) / 100))
  rw [Real.log_rpow hB0] at h
  linarith

theorem exists_selected_surface_bound (c : ℤ) (hc : c ∉ PowerValues 6) :
    ∃ M : ℝ, 0 < M ∧ ∀ B : ℝ, 1 ≤ B → ∀ S : Finset (Fin 3 → ℤ),
      (∀ z ∈ S, IntegerDiagonalPoint c z) →
      (∀ z ∈ S, ∀ i, |(z i : ℝ)| ≤ B) →
      (S.card : ℝ) ≤ M * B ^ ((83 : ℝ) / 100) := by
  classical
  obtain ⟨L, hL, hpositive⟩ := exists_positive_surface_log_bound c hc
  let Z := (sexticBox c (c.natAbs : ℝ)).card
  refine ⟨(Z : ℝ) + 100 * L, by positivity, ?_⟩
  intro B hB S hS hheight
  let T := S.filter (fun z => z 1 = 0)
  let U := S.filter (fun z => z 1 ≠ 0)
  have hT : (T.card : ℝ) ≤ Z := by
    exact_mod_cast card_zero_middle_points_le c (by intro h; exact hc ⟨0, by simp [h]⟩) T
      (fun z hz => ⟨hS z (Finset.mem_filter.mp hz).1, (Finset.mem_filter.mp hz).2⟩)
  have hU := hpositive B hB U (by
    intro z hz
    have h := hS z (Finset.mem_filter.mp hz).1
    refine ⟨h, ?_⟩
    have hne := (Finset.mem_filter.mp hz).2
    have hnonneg := h.2.1
    omega) (fun z hz => hheight z (Finset.mem_filter.mp hz).1)
  have hU' : (U.card : ℝ) ≤ (100 * L) * B ^ ((83 : ℝ) / 100) := by
    calc
      _ ≤ L * B ^ ((82 : ℝ) / 100) * (Real.log B + 1) := hU
      _ ≤ L * B ^ ((82 : ℝ) / 100) * (100 * B ^ ((1 : ℝ) / 100)) :=
        mul_le_mul_of_nonneg_left (log_add_one_le_small_power B hB) (by positivity)
      _ = (100 * L) * B ^ ((83 : ℝ) / 100) := by
        rw [show L * B ^ ((82 : ℝ) / 100) * (100 * B ^ ((1 : ℝ) / 100)) =
          (100 * L) * (B ^ ((82 : ℝ) / 100) * B ^ ((1 : ℝ) / 100)) by ring,
          ← Real.rpow_add (by linarith : 0 < B)]
        norm_num
  have hcard : (T.card : ℝ) + U.card = S.card := by
    exact_mod_cast Finset.card_filter_add_card_filter_not (s := S) (fun z => z 1 = 0)
  have hp : 1 ≤ B ^ ((83 : ℝ) / 100) := Real.one_le_rpow hB (by norm_num)
  have hZ : (Z : ℝ) ≤ Z * B ^ ((83 : ℝ) / 100) :=
    le_mul_of_one_le_right (Nat.cast_nonneg _) hp
  nlinarith

#print axioms exists_selected_surface_bound
-- 'Erdos477.Counting.exists_selected_surface_bound' depends on axioms:
-- [propext, Classical.choice, Quot.sound]

end Erdos477.Counting
