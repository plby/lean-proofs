import Wikipedia.HopfProblem.HigherHurewiczSimplexNullhomotopyBasic
import Mathlib.Analysis.Convex.GaugeRescale
import Mathlib.Topology.Homotopy.HomotopyGroup

/-!
# Geometry of the actual native cube in every dimension

The ambient coordinatewise interval is compact, convex, and has nonempty
interior. Its frontier is exactly the native cube boundary after the
coordinatewise subtype homeomorphism, including in dimension zero.
-/

noncomputable section

open Set
open scoped Topology unitInterval

namespace Wikipedia.HopfProblem.HigherHurewicz

theorem convex_realCubeSet (n : ℕ) : Convex ℝ (realCubeSet n) := convex_Icc 0 1

theorem isClosed_realCubeSet (n : ℕ) : IsClosed (realCubeSet n) := isClosed_Icc

theorem isCompact_realCubeSet (n : ℕ) : IsCompact (realCubeSet n) := isCompact_Icc

theorem mem_interior_realCubeSet (n : ℕ) (v : Fin n → ℝ) :
    v ∈ interior (realCubeSet n) ↔ ∀ i, 0 < v i ∧ v i < 1 := by
  rw [realCubeSet, ← pi_univ_Icc, interior_pi_set (finite_univ)]
  simp only [mem_pi, mem_univ, forall_const, interior_Icc, Pi.zero_apply, Pi.one_apply,
    mem_Ioo]

theorem interior_realCubeSet_nonempty (n : ℕ) : (interior (realCubeSet n)).Nonempty := by
  refine ⟨fun _ => 1 / 2, (mem_interior_realCubeSet n _).mpr ?_⟩
  intro i
  norm_num

/-- Frontier membership for an actual point of the ambient unit cube. -/
theorem realCubeSet_mem_frontier_iff (n : ℕ) (v : ↥(realCubeSet n)) :
    v.val ∈ frontier (realCubeSet n) ↔ ∃ i, v.val i = 0 ∨ v.val i = 1 := by
  classical
  rw [frontier, (isClosed_realCubeSet n).closure_eq]
  simp only [mem_sdiff, v.property, true_and, mem_interior_realCubeSet]
  constructor
  · intro h
    simp only [not_forall, not_and_or, not_lt] at h
    obtain ⟨i, h | h⟩ := h
    · exact ⟨i, Or.inl (le_antisymm h (v.property.1 i))⟩
    · exact ⟨i, Or.inr (le_antisymm (v.property.2 i) h)⟩
  · rintro ⟨i, h | h⟩ hi
    · have h0 := (hi i).1
      rw [h] at h0
      exact lt_irrefl _ h0
    · have h1 := (hi i).2
      rw [h] at h1
      exact lt_irrefl _ h1

/-- Coordinatewise bundling gives the homeomorphism to Mathlib's native cube. -/
def realCubeHomeomorph (n : ℕ) : ↥(realCubeSet n) ≃ₜ (Fin n → I) where
  toFun v i := ⟨v.val i, v.property.1 i, v.property.2 i⟩
  invFun u := ⟨fun i => (u i : ℝ), fun i => (u i).property.1, fun i => (u i).property.2⟩
  left_inv v := Subtype.ext rfl
  right_inv u := by
    funext i
    apply Subtype.ext
    rfl
  continuous_toFun := by
    apply continuous_pi
    intro i
    exact ((continuous_apply i).comp continuous_subtype_val).subtype_mk _
  continuous_invFun := by
    apply Continuous.subtype_mk
    exact continuous_pi fun i => continuous_subtype_val.comp (continuous_apply i)

@[simp] theorem realCubeHomeomorph_apply (n : ℕ) (v : ↥(realCubeSet n)) (i : Fin n) :
    (realCubeHomeomorph n v i : ℝ) = v.val i := rfl

@[simp] theorem realCubeHomeomorph_symm_apply (n : ℕ) (u : Fin n → I) (i : Fin n) :
    ((realCubeHomeomorph n).symm u).val i = (u i : ℝ) := rfl

/-- The native boundary condition agrees with the actual ambient frontier. -/
theorem realCubeHomeomorph_mem_boundary_iff (n : ℕ) (v : ↥(realCubeSet n)) :
    realCubeHomeomorph n v ∈ Cube.boundary (Fin n) ↔ v.val ∈ frontier (realCubeSet n) := by
  rw [realCubeSet_mem_frontier_iff]
  constructor
  · rintro ⟨i, hi | hi⟩
    · exact ⟨i, Or.inl (congrArg (fun t : I => (t : ℝ)) hi)⟩
    · exact ⟨i, Or.inr (congrArg (fun t : I => (t : ℝ)) hi)⟩
  · rintro ⟨i, hi | hi⟩
    · exact ⟨i, Or.inl (Subtype.ext hi)⟩
    · exact ⟨i, Or.inr (Subtype.ext hi)⟩

theorem realCubeHomeomorph_symm_mem_frontier_iff (n : ℕ) (u : Fin n → I) :
    ((realCubeHomeomorph n).symm u).val ∈ frontier (realCubeSet n) ↔
      u ∈ Cube.boundary (Fin n) := by
  rw [← realCubeHomeomorph_mem_boundary_iff, Homeomorph.apply_symm_apply]

end Wikipedia.HopfProblem.HigherHurewicz
