import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.Tactic.NormNum

/-!

# The actual unit sphere in a real line is finite

Every vector is a scalar multiple of a chosen unit vector. The unit norm
forces that scalar to be one or minus one. This identifies the original
unit sphere with a two-point set, without replacing its norm or topology.
-/

noncomputable section

open Set Metric

namespace Wikipedia.HopfProblem.DegreeCollapse.AttachmentFiniteness

variable {N : Type*} [NormedAddCommGroup N] [NormedSpace ℝ N]

theorem unit_sphere_eq_pair_of_finrank_one (h : Module.finrank ℝ N = 1)
    (u : sphere (0 : N) 1) : sphere (0 : N) 1 = {u.val, -u.val} := by
  have hu : ‖u.val‖ = 1 := mem_sphere_zero_iff_norm.mp u.property
  have hne : u.val ≠ 0 := by
    intro hz
    simp [hz] at hu
  apply Set.ext
  intro x
  constructor
  · intro hx
    obtain ⟨c, rfl⟩ := (finrank_eq_one_iff_of_nonzero' u.val hne).mp h x
    have hc : |c| = 1 := by simpa [norm_smul, hu] using hx
    rcases (abs_eq (by norm_num : (0 : ℝ) ≤ 1)).mp hc with hc | hc
    · simp [hc]
    · simp [hc]
  · intro hx
    rcases hx with rfl | hx
    · exact u.property
    · have hx' : x = -u.val := hx
      simp [hx', hu]

theorem finite_unit_sphere_of_finrank_one (h : Module.finrank ℝ N = 1) :
    Finite (sphere (0 : N) 1) := by
  classical
  cases isEmpty_or_nonempty (sphere (0 : N) 1) with
  | inl hEmpty => exact inferInstance
  | inr hNonempty =>
    let u : sphere (0 : N) 1 := Classical.arbitrary _
    have hs : (sphere (0 : N) 1).Finite := by
      rw [unit_sphere_eq_pair_of_finrank_one h u]
      exact (Set.finite_singleton _).insert _
    exact hs.to_subtype

end Wikipedia.HopfProblem.DegreeCollapse.AttachmentFiniteness
