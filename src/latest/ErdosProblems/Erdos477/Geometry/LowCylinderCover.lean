/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Reducing the remaining sextic count to line and conic cylinders.
Formal author: Codex.
-/

import ErdosProblems.Erdos477.Geometry.SexticCylinderCover
import ErdosProblems.Erdos477.Counting.BoundedDegreeCurves

namespace Erdos477.Geometry

open Counting
open scoped BigOperators

variable {K : Type*} [Field K] [CharZero K] [IsAlgClosed K]

/-- All cylinders of plane degree at least three can be absorbed in the
exceptional set using the unconditional uniform plane-curve estimate. -/
theorem exists_low_degree_cylinder_cover (c : ℤ) (hc : c ≠ 0) :
    ∃ A : ℝ, 0 < A ∧ ∀ B : ℝ, 1 ≤ B →
      ∀ S : Finset (Fin 3 → ℤ), S ⊆ sexticBox c B → (∀ z ∈ S, 0 ≤ z 0) →
      ∃ C : Finset (MvPolynomial (Fin 2) K), ∃ E : Finset (Fin 3 → ℤ),
        (∀ F ∈ C, Irreducible F ∧ F.totalDegree ≤ 2) ∧
        (C.card : ℝ) ≤ A * B ^ ((41 : ℝ) / 100) ∧ E ⊆ S ∧
        (∀ z ∈ S, z ∈ E ∨ ∃ F ∈ C, MvPolynomial.eval ![(z 1 : K), (z 2 : K)] F = 0) ∧
        (E.card : ℝ) ≤ A * B ^ ((82 : ℝ) / 100) * (Real.log B + 1) := by
  classical
  obtain ⟨M, hM, N, hcover⟩ := exists_sextic_cylinder_cover (K := K) c hc
  obtain ⟨L, hL, hcurve⟩ := exists_high_degree_cylinder_bound (K := K) N
    ((1 : ℝ) / 100) (by norm_num)
  let A := M * (1 + L)
  have hA : 0 < A := by dsimp only [A]; positivity
  have hMA : M ≤ A := by dsimp only [A]; nlinarith
  refine ⟨A, hA, ?_⟩
  intro B hB S hS hnonneg
  have hB0 : 0 < B := by linarith
  have hlogB : 0 ≤ Real.log B := Real.log_nonneg hB
  obtain ⟨C, E, hC, hCcard, hES, hCE, hEcard⟩ := hcover B hB S hS hnonneg
  let small := C.filter (fun F => F.totalDegree ≤ 2)
  let large := C.filter (fun F => 3 ≤ F.totalDegree)
  let U := fun F : MvPolynomial (Fin 2) K =>
    S.filter (fun z => MvPolynomial.eval ![(z 1 : K), (z 2 : K)] F = 0)
  let E' := E ∪ large.biUnion U
  have hU (F) (hF : F ∈ large) :
      ((U F).card : ℝ) ≤ L * B ^ ((1 : ℝ) / 3 + 1 / 100) := by
    have hFC := (Finset.mem_filter.mp hF).1
    exact hcurve c B hB F (hC F hFC).1 (Finset.mem_filter.mp hF).2 (hC F hFC).2
      (U F) (fun z hz =>
        ⟨hnonneg z (Finset.mem_filter.mp hz).1,
          ((mem_sexticBox c B z).mp (hS (Finset.mem_filter.mp hz).1)).1⟩)
      (fun _ hz => (Finset.mem_filter.mp hz).2)
      (fun z hz => ((mem_sexticBox c B z).mp (hS (Finset.mem_filter.mp hz).1)).2)
  have hlargecard : (large.card : ℝ) ≤ M * B ^ ((41 : ℝ) / 100) :=
    (Nat.cast_le.mpr (Finset.card_filter_le _ _)).trans hCcard
  have hE' : (E'.card : ℝ) ≤ (E.card : ℝ) +
      (large.card : ℝ) * (L * B ^ ((1 : ℝ) / 3 + 1 / 100)) := by
    have hnat : E'.card ≤ E.card + ∑ F ∈ large, (U F).card :=
      (Finset.card_union_le _ _).trans (Nat.add_le_add_left Finset.card_biUnion_le _)
    have hreal : (E'.card : ℝ) ≤ (E.card : ℝ) + ∑ F ∈ large, ((U F).card : ℝ) := by
      exact_mod_cast hnat
    apply hreal.trans
    rw [← nsmul_eq_mul, ← Finset.sum_const]
    exact add_le_add le_rfl (Finset.sum_le_sum hU)
  refine ⟨small, E', ?_, ?_, ?_, ?_, ?_⟩
  · intro F hF
    exact ⟨(hC F (Finset.mem_filter.mp hF).1).1, (Finset.mem_filter.mp hF).2⟩
  · exact ((Nat.cast_le.mpr (Finset.card_filter_le _ _)).trans hCcard).trans
      (mul_le_mul_of_nonneg_right hMA (Real.rpow_nonneg hB0.le _))
  · intro z hz
    rcases Finset.mem_union.mp hz with hz | hz
    · exact hES hz
    · obtain ⟨F, _, hz⟩ := Finset.mem_biUnion.mp hz
      exact (Finset.mem_filter.mp hz).1
  · intro z hz
    rcases hCE z hz with hzE | ⟨F, hF, hzero⟩
    · exact Or.inl (Finset.mem_union_left _ hzE)
    · by_cases hsmall : F.totalDegree ≤ 2
      · exact Or.inr ⟨F, Finset.mem_filter.mpr ⟨hF, hsmall⟩, hzero⟩
      · exact Or.inl (Finset.mem_union_right _ (Finset.mem_biUnion.mpr
          ⟨F, Finset.mem_filter.mpr ⟨hF, by omega⟩, Finset.mem_filter.mpr ⟨hz, hzero⟩⟩))
  · have hpower : B ^ ((41 : ℝ) / 100) * B ^ ((1 : ℝ) / 3 + 1 / 100) ≤
        B ^ ((82 : ℝ) / 100) := by
      rw [← Real.rpow_add hB0]
      exact Real.rpow_le_rpow_of_exponent_le hB (by norm_num)
    calc
      _ ≤ (E.card : ℝ) + (large.card : ℝ) *
          (L * B ^ ((1 : ℝ) / 3 + 1 / 100)) := hE'
      _ ≤ M * B ^ ((82 : ℝ) / 100) * Real.log B +
          (M * B ^ ((41 : ℝ) / 100)) * (L * B ^ ((1 : ℝ) / 3 + 1 / 100)) :=
        add_le_add hEcard (mul_le_mul_of_nonneg_right hlargecard (by positivity))
      _ = M * B ^ ((82 : ℝ) / 100) * Real.log B +
          M * L * (B ^ ((41 : ℝ) / 100) * B ^ ((1 : ℝ) / 3 + 1 / 100)) := by ring
      _ ≤ M * B ^ ((82 : ℝ) / 100) * Real.log B + M * L * B ^ ((82 : ℝ) / 100) :=
        add_le_add le_rfl (mul_le_mul_of_nonneg_left hpower (mul_nonneg hM.le hL.le))
      _ ≤ A * B ^ ((82 : ℝ) / 100) * (Real.log B + 1) := by
        have h1 := mul_nonneg (mul_nonneg hM.le hL.le)
          (mul_nonneg (Real.rpow_nonneg hB0.le ((82 : ℝ) / 100)) hlogB)
        have h2 := mul_nonneg hM.le (Real.rpow_nonneg hB0.le ((82 : ℝ) / 100))
        dsimp only [A]
        nlinarith

#print axioms exists_low_degree_cylinder_cover
-- 'Erdos477.Geometry.exists_low_degree_cylinder_cover' depends on axioms:
-- [propext, Classical.choice, Quot.sound]

end Erdos477.Geometry
