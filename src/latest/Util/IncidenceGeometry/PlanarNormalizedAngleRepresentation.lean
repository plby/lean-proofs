import Mathlib.Tactic
import Mathlib.Analysis.SpecialFunctions.Complex.Arg
import Util.IncidenceGeometry.Basic

open Classical
noncomputable section

lemma PlanarNormalizedAngleRepresentation (v : EuclideanSpace ℝ (Fin 2)) (hv : v ≠ 0) :
    let z : ℂ := (v 0 : ℂ) + (v 1 : ℂ) * Complex.I
    let α : ℝ := let a := Complex.arg z
      if 0 ≤ a then a else a + 2 * Real.pi
    0 ≤ α ∧ α < 2 * Real.pi ∧
      ∃ r : ℝ, 0 < r ∧
        v = r • WithLp.toLp 2
          (fun k : Fin 2 => if k = 0 then Real.cos α else Real.sin α) := by
  dsimp only
  let z : ℂ := (v 0 : ℂ) + (v 1 : ℂ) * Complex.I
  let a : ℝ := Complex.arg z
  let α : ℝ := if 0 ≤ a then a else a + 2 * Real.pi
  have hz : z ≠ 0 := by
    intro hz0
    apply hv
    apply PiLp.ext
    intro k
    fin_cases k
    · have hr := congrArg Complex.re hz0
      simpa [z] using hr
    · have hi := congrArg Complex.im hz0
      simpa [z] using hi
  have hrpos : 0 < ‖z‖ := norm_pos_iff.mpr hz
  have hα_nonneg : 0 ≤ α := by
    dsimp [α, a]
    split_ifs with h
    · exact h
    · have harg_gt : -Real.pi < Complex.arg z := Complex.neg_pi_lt_arg z
      linarith [Real.pi_pos]
  have hα_lt : α < 2 * Real.pi := by
    dsimp [α, a]
    split_ifs with h
    · have hle := Complex.arg_le_pi z
      linarith [Real.pi_pos]
    · have hneg : Complex.arg z < 0 := lt_of_not_ge h
      linarith
  have hcosα : Real.cos α = Real.cos a := by
    dsimp [α]
    split_ifs with h
    · rfl
    · rw [Real.cos_add_two_pi]
  have hsinα : Real.sin α = Real.sin a := by
    dsimp [α]
    split_ifs with h
    · rfl
    · rw [Real.sin_add_two_pi]
  refine ⟨hα_nonneg, hα_lt, ‖z‖, hrpos, ?_⟩
  apply PiLp.ext
  intro k
  fin_cases k
  · change v 0 = ‖z‖ * Real.cos α
    rw [hcosα]
    dsimp [a]
    simpa [z] using (Complex.norm_mul_cos_arg z).symm
  · change v 1 = ‖z‖ * Real.sin α
    rw [hsinα]
    dsimp [a]
    simpa [z] using (Complex.norm_mul_sin_arg z).symm
