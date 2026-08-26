import ErdosProblems.Erdos633b.RegularTriangle
import ErdosProblems.Erdos633b.VertexReindex

/-! A scalene outer triangle has no pair of reference angle counts equal
at all actual tiling vertices. -/

namespace Erdos633b.Tiling

theorem equilateral_of_equal_vertex_counts {T : Triangle} {n : ℕ} (d : Tiling T n)
    (i j : Fin 3) (hij : i ≠ j)
    (h : ∀ v : d.Vertex, d.vertexAngleCount v i = d.vertexAngleCount v j) :
    ∀ k, T.angle k = Real.pi / 3 := by
  have hf : Function.Injective (![i, j] : Fin 2 → Fin 3) := by
    intro x y he
    fin_cases x <;> fin_cases y <;> simp_all
  have hg : Function.Injective (![0, 1] : Fin 2 → Fin 3) := by
    intro x y he
    fin_cases x <;> fin_cases y <;> simp_all
  obtain ⟨e, he⟩ := Equiv.Perm.exists_extending_pair ![i, j] ![0, 1] hf hg
  have hei : e i = 0 := he 0
  have hej : e j = 1 := he 1
  apply (d.reindexTile e).equilateral_of_equal_first_two_vertex_counts
  intro v
  simpa only [d.vertexAngleCount_reindexTile, ← hei, ← hej, Equiv.symm_apply_apply] using
    h (d.vertexReindexEquiv e v)

theorem exists_unequal_vertex_counts_of_scalene {T : Triangle} {n : ℕ} (d : Tiling T n)
    (hscalene : Function.Injective T.angle) (i j : Fin 3) (hij : i ≠ j) :
    ∃ v : d.Vertex, d.vertexAngleCount v i ≠ d.vertexAngleCount v j := by
  by_contra hn
  push Not at hn
  exact T.not_equilateral_of_injective_angles hscalene
    (d.equilateral_of_equal_vertex_counts i j hij hn)

theorem equal_count_pair_necessary {T : Triangle} {n : ℕ} (d : Tiling T n)
    (i j : Fin 3) (hij : i ≠ j)
    (h : ∀ v : d.Vertex, d.vertexAngleCount v i = d.vertexAngleCount v j) : EightCases T := by
  have he := d.equilateral_of_equal_vertex_counts i j hij h
  refine ⟨Equiv.refl _, Or.inl ?_⟩
  exact (he 0).trans (he 1).symm

end Erdos633b.Tiling
