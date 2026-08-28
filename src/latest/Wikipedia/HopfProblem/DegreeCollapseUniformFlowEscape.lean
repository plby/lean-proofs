import Mathlib.Dynamics.Flow
import Mathlib.Topology.Compactness.Compact
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Tactic.Linarith
import Mathlib.Topology.Instances.Real.Lemmas

/-!
# Uniform finite-time escape from a compact set

If every trajectory through a compact set leaves a closed height band,
compactness constructs one time bound and one positive height margin for
all starting points. This is the first compactness step toward a no-return
neighborhood of the unique connecting trajectory.
-/

noncomputable section

open Set
open scoped Topology

namespace Wikipedia.HopfProblem.DegreeCollapse.FlowCancellation

variable {X : Type*} [TopologicalSpace X]

/-- Pointwise escape supplies uniform time and height margins on an actual compact set. -/
theorem exists_uniform_flow_escape (F : Flow ℝ X) {f : X → ℝ} (hf : Continuous f)
    {C : Set X} (hC : IsCompact C) {c d : ℝ}
    (hescape : ∀ x ∈ C, ∃ t : ℝ, f (F t x) ∉ Icc c d) :
    ∃ T : ℝ, 0 < T ∧ ∃ δ : ℝ, 0 < δ ∧
      ∀ x ∈ C, ∃ t ∈ Icc (-T) T, f (F t x) < c - δ ∨ d + δ < f (F t x) := by
  classical
  by_cases hne : C.Nonempty
  swap
  · exact ⟨1, by norm_num, 1, by norm_num, fun x hx => False.elim (hne ⟨x, hx⟩)⟩
  let J := {p : ℝ × ℝ // 0 < p.2}
  let O : J → Set X := fun p =>
    {x | f (F p.val.1 x) < c - p.val.2 ∨ d + p.val.2 < f (F p.val.1 x)}
  have hO (p : J) : IsOpen (O p) :=
    (isOpen_lt (hf.comp (F.continuous_toFun p.val.1)) continuous_const).union
      (isOpen_lt continuous_const (hf.comp (F.continuous_toFun p.val.1)))
  have hcover : C ⊆ ⋃ p, O p := by
    intro x hx
    obtain ⟨t, ht⟩ := hescape x hx
    by_cases hl : c ≤ f (F t x)
    · have hr : d < f (F t x) := lt_of_not_ge (fun h => ht ⟨hl, h⟩)
      have hδ : 0 < (f (F t x) - d) / 2 := by linarith
      apply mem_iUnion.mpr
      refine ⟨⟨(t, (f (F t x) - d) / 2), hδ⟩, Or.inr ?_⟩
      change d + (f (F t x) - d) / 2 < f (F t x)
      linarith
    · have hl' : f (F t x) < c := lt_of_not_ge hl
      have hδ : 0 < (c - f (F t x)) / 2 := by linarith
      apply mem_iUnion.mpr
      refine ⟨⟨(t, (c - f (F t x)) / 2), hδ⟩, Or.inl ?_⟩
      change f (F t x) < c - (c - f (F t x)) / 2
      linarith
  obtain ⟨S, hScover⟩ := hC.elim_finite_subcover O hO hcover
  have hS : S.Nonempty := by
    obtain ⟨x, hx⟩ := hne
    obtain ⟨p, hp, -⟩ := mem_iUnion₂.mp (hScover hx)
    exact ⟨p, hp⟩
  let T := S.sup' hS (fun p => |p.val.1|) + 1
  let δ := S.inf' hS (fun p => p.val.2) / 2
  have hmin : 0 < S.inf' hS (fun p => p.val.2) :=
    (Finset.lt_inf'_iff hS).mpr (fun p _ => p.property)
  have hT : 0 < T := by
    obtain ⟨p, hp⟩ := hS
    have hh := Finset.le_sup' (fun p : J => |p.val.1|) hp
    have habs := abs_nonneg p.val.1
    dsimp [T]
    linarith
  have hδ : 0 < δ := div_pos hmin (by norm_num)
  refine ⟨T, hT, δ, hδ, ?_⟩
  intro x hx
  obtain ⟨p, hp, hpx⟩ := mem_iUnion₂.mp (hScover hx)
  have ht : |p.val.1| ≤ T := by
    have hh := Finset.le_sup' (fun p : J => |p.val.1|) hp
    dsimp [T]
    linarith
  have hd : δ ≤ p.val.2 := by
    have hh := Finset.inf'_le (fun p : J => p.val.2) hp
    dsimp [δ]
    linarith
  refine ⟨p.val.1, abs_le.mp ht, ?_⟩
  rcases hpx with h | h
  · exact Or.inl (by linarith)
  · exact Or.inr (by linarith)

end Wikipedia.HopfProblem.DegreeCollapse.FlowCancellation
