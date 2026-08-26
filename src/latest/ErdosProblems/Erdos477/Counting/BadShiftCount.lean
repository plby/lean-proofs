/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
The unconditional sublinear count of positive bad shifts.
Formal author: Codex.
-/

import ErdosProblems.Erdos477.Counting.SelectedSurfaceBound
import ErdosProblems.Erdos477.Counting.BadShiftHeight

namespace Erdos477.Counting

theorem exists_bad_shift_bound (c : ℤ) (hc : c ∉ PowerValues 6) :
    ∃ M : ℝ, 0 < M ∧ ∀ N : ℕ, 1 ≤ N → ∀ T : Finset ℕ,
      (∀ t ∈ T, 1 ≤ t ∧ t ≤ N ∧ IsBadShift c t) →
      (T.card : ℝ) ≤ M * (N : ℝ) ^ ((249 : ℝ) / 250) := by
  classical
  obtain ⟨L, hL, hbound⟩ := exists_selected_surface_bound c hc
  refine ⟨L * (1 + (c.natAbs : ℝ)) ^ ((83 : ℝ) / 100), by positivity, ?_⟩
  intro N hN T hT
  have hex (t : T) : ∃ z : Fin 3 → ℤ, IntegerDiagonalPoint c z ∧ z 0 = (t.val : ℤ) ∧
      ∀ i, |(z i : ℝ)| ≤ badShiftHeight c N :=
    badShift_bounded_point c hc N t.val (hT t.val t.property).1
      (hT t.val t.property).2.1 (hT t.val t.property).2.2
  choose z hz using hex
  have hinj : Function.Injective z := by
    intro s t h
    apply Subtype.ext
    have hcast : (s.val : ℤ) = (t.val : ℤ) :=
      (hz s).2.1.symm.trans ((congrFun h 0).trans (hz t).2.1)
    exact_mod_cast hcast
  let S := Finset.univ.image z
  have hcard : S.card = T.card := by
    simp only [S, Finset.card_image_of_injective _ hinj, Finset.card_univ, Fintype.card_coe]
  have hcount := hbound (badShiftHeight c N) (badShiftHeight_ge_one c N hN) S (by
    intro w hw
    obtain ⟨t, _, rfl⟩ := Finset.mem_image.mp hw
    exact (hz t).1) (by
    intro w hw
    obtain ⟨t, _, rfl⟩ := Finset.mem_image.mp hw
    exact (hz t).2.2)
  rw [hcard] at hcount
  have hpower : (badShiftHeight c N) ^ ((83 : ℝ) / 100) =
      (1 + (c.natAbs : ℝ)) ^ ((83 : ℝ) / 100) * (N : ℝ) ^ ((249 : ℝ) / 250) := by
    rw [badShiftHeight, Real.mul_rpow (by positivity) (Real.rpow_nonneg (Nat.cast_nonneg N) _),
      ← Real.rpow_mul (Nat.cast_nonneg N)]
    norm_num
  rw [hpower, ← mul_assoc] at hcount
  exact hcount

lemma exists_nat_sublinear_gap (M : ℝ) :
    ∃ N : ℕ, 1 ≤ N ∧ M * (N : ℝ) ^ ((249 : ℝ) / 250) < N := by
  have htend : Filter.Tendsto (fun N : ℕ => (N : ℝ) ^ ((1 : ℝ) / 250))
      Filter.atTop Filter.atTop :=
    (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 250)).comp tendsto_natCast_atTop_atTop
  have hevent := (Filter.tendsto_atTop.1 htend) (M + 1)
  obtain ⟨N, hM, hN⟩ := (hevent.and (Filter.eventually_ge_atTop 1)).exists
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  refine ⟨N, hN, ?_⟩
  calc
    _ < (N : ℝ) ^ ((1 : ℝ) / 250) * (N : ℝ) ^ ((249 : ℝ) / 250) :=
      mul_lt_mul_of_pos_right (by linarith) (Real.rpow_pos_of_pos hNr _)
    _ = N := by rw [← Real.rpow_add hNr]; norm_num

#print axioms exists_bad_shift_bound
-- 'Erdos477.Counting.exists_bad_shift_bound' depends on axioms:
-- [propext, Classical.choice, Quot.sound]

end Erdos477.Counting
