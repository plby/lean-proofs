/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional

/-!
# Transversality under one hyperplane cut

This file records the direction calculation used at every successor stage of
the Anderson--Keisler cutting hierarchy.  If a parent direction `D` is
transverse to a pattern direction `B`, then cutting `D` by the hyperplane
orthogonal to a normal `v` preserves transversality precisely when `v` is not
orthogonal to the old intersection `D ⊓ B`.

The child has codimension one in its parent whenever the normal belongs to the
parent and is nonzero.
-/

open Module

namespace Erdos909

noncomputable section

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

/-- The direction obtained by cutting `D` with the linear hyperplane normal
to `v`. -/
def hyperplaneChildDirection (D : Submodule ℝ V) (v : V) : Submodule ℝ V :=
  D ⊓ (ℝ ∙ v)ᗮ

@[simp]
theorem mem_hyperplaneChildDirection {D : Submodule ℝ V} {v x : V} :
    x ∈ hyperplaneChildDirection D v ↔
      x ∈ D ∧ inner ℝ v x = 0 := by
  simp [hyperplaneChildDirection,
    Submodule.mem_orthogonal_singleton_iff_inner_right]

/-- Cutting a parent direction by a normal which is nonorthogonal to its old
intersection with `B` preserves transversality to `B`. -/
theorem hyperplaneChildDirection_sup_eq_top
    (D B : Submodule ℝ V) (hDB : D ⊔ B = ⊤) {v : V} (_hvD : v ∈ D)
    (hv : v ∉ (D ⊓ B)ᗮ) :
    hyperplaneChildDirection D v ⊔ B = ⊤ := by
  rw [Submodule.eq_top_iff']
  intro x
  have hx : x ∈ D ⊔ B := by rw [hDB]; exact Submodule.mem_top
  rcases Submodule.mem_sup.mp hx with ⟨d, hd, b, hb, rfl⟩
  rw [Submodule.mem_orthogonal] at hv
  push Not at hv
  obtain ⟨z, ⟨hzD, hzB⟩, hzv⟩ := hv
  let a : ℝ := (inner ℝ z v)⁻¹ * inner ℝ d v
  have hzv' : inner ℝ z v ≠ 0 := hzv
  have hcut : d - a • z ∈ hyperplaneChildDirection D v := by
    refine ⟨D.sub_mem hd (D.smul_mem a hzD), ?_⟩
    apply Submodule.mem_orthogonal_singleton_iff_inner_left.mpr
    simp only [inner_sub_left, inner_smul_left, starRingEnd_apply,
      star_trivial, a]
    field_simp
    simp
  have hB : b + a • z ∈ B := B.add_mem hb (B.smul_mem a hzB)
  convert Submodule.add_mem_sup hcut hB using 1 <;> module

/-- A normal satisfying the transversality condition is automatically
nonzero. -/
theorem ne_zero_of_not_mem_inf_orthogonal
    {D B : Submodule ℝ V} {v : V} (hv : v ∉ (D ⊓ B)ᗮ) :
    v ≠ 0 := by
  intro hv0
  subst v
  exact hv (Submodule.zero_mem _)

section FiniteDimensional

variable [FiniteDimensional ℝ V]

/-- The child direction has codimension one in its parent.  The additive
form avoids truncated subtraction and is normally the most convenient form
for subsequent finrank calculations. -/
theorem finrank_hyperplaneChildDirection_add_one
    (D : Submodule ℝ V) {v : V} (hvD : v ∈ D) (hv0 : v ≠ 0) :
    finrank ℝ (hyperplaneChildDirection D v) + 1 = finrank ℝ D := by
  have hspan : ℝ ∙ v ≤ D :=
    (Submodule.span_singleton_le_iff_mem v D).2 hvD
  have hdim := Submodule.finrank_add_inf_finrank_orthogonal hspan
  rw [finrank_span_singleton hv0] at hdim
  change finrank ℝ (D ⊓ (ℝ ∙ v)ᗮ : Submodule ℝ V) + 1 = finrank ℝ D
  rw [inf_comm, Nat.add_comm]
  exact hdim

/-- Subtraction form of `finrank_hyperplaneChildDirection_add_one`. -/
theorem finrank_hyperplaneChildDirection
    (D : Submodule ℝ V) {v : V} (hvD : v ∈ D) (hv0 : v ≠ 0) :
    finrank ℝ (hyperplaneChildDirection D v) = finrank ℝ D - 1 := by
  have hdim := finrank_hyperplaneChildDirection_add_one D hvD hv0
  omega

/-- Under the transversality hypothesis the nonzero assumption required by
the codimension calculation need not be supplied separately. -/
theorem finrank_hyperplaneChildDirection_of_transverse
    (D B : Submodule ℝ V) {v : V} (hvD : v ∈ D)
    (hv : v ∉ (D ⊓ B)ᗮ) :
    finrank ℝ (hyperplaneChildDirection D v) = finrank ℝ D - 1 :=
  finrank_hyperplaneChildDirection D hvD
    (ne_zero_of_not_mem_inf_orthogonal hv)

end FiniteDimensional

end

end Erdos909
