import Wikipedia.HomotopyGroupsOfSpheres.QuaternionicVertexSpace

/-! # Smooth families in the original symplectic vertex manifold -/

open scoped Manifold ContDiff

namespace Wikipedia.HomotopyGroupsOfSpheres.QuaternionicColumns.VertexSpace

open NoExoticSixSphere.GLOrthonormalization

variable {n m : ℕ}
variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] [TopologicalSpace M] [ChartedSpace H M]
  {I : ModelWithCorners ℝ E H} {f : M → Space n m} {x : M}

theorem contMDiffAt_iff_coordinatewise :
    ContMDiffAt I 𝓘(ℝ, Model n m) ∞ f x ↔
      ∀ i : Fin m, ContMDiffAt I 𝓘(ℝ, SkewSpace n) ∞ (fun y => f y i) x := by
  constructor
  · intro hf i
    exact (contMDiff_eval (n := n) i).contMDiffAt.comp x hf
  · intro hf
    apply (contMDiffAt_iff_target_of_mem_source
      (I := I) (I' := 𝓘(ℝ, Model n m)) (f := f)
      (mem_atVertices_source (n := n) (m := m) (f x))).mpr
    refine ⟨continuousAt_pi.mpr (fun i => (hf i).continuousAt), ?_⟩
    change ContMDiffAt I 𝓘(ℝ, Model n m) ∞ (fun y => atVertices (f x) (f y)) x
    apply contMDiffAt_pi_space.mpr
    intro i
    exact (Smoothness.contMDiffAt_iff_chart.mp (hf i)).2

theorem contMDiff_iff_coordinatewise :
    ContMDiff I 𝓘(ℝ, Model n m) ∞ f ↔
      ∀ i : Fin m, ContMDiff I 𝓘(ℝ, SkewSpace n) ∞ (fun y => f y i) := by
  constructor
  · intro hf i x
    exact contMDiffAt_iff_coordinatewise.mp (hf x) i
  · intro hf x
    exact contMDiffAt_iff_coordinatewise.mpr (fun i => hf i x)

theorem contMDiff_iff_operator_family :
    ContMDiff I 𝓘(ℝ, Model n m) ∞ f ↔
      ∀ i : Fin m, ContMDiff I 𝓘(ℝ, Vector (4 * n + 4) →L[ℝ] Vector (4 * n + 4)) ∞
        (fun y => (f y i).val.val.val) := by
  rw [contMDiff_iff_coordinatewise]
  exact forall_congr' (fun _ => Smoothness.contMDiff_iff_operator)

end Wikipedia.HomotopyGroupsOfSpheres.QuaternionicColumns.VertexSpace
