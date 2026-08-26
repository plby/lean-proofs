import ErdosProblems.Erdos633b.IsoscelesTileRefinement

/-! Every actual tiling by an isosceles reference triangle has an outer
triangle in case (1) or case (3). No tile-count hypothesis is required. -/

namespace Erdos633b.Tiling

theorem isosceles_tile_ordered_necessary {T : Triangle} {n : ℕ} (d : Tiling T n)
    (heq : d.tile.angle 0 = d.tile.angle 1) : EightCases T := by
  by_cases hscalene : Function.Injective T.angle
  · have hα := d.isosceles_base_angle_eq_pi_six heq hscalene
    obtain ⟨e, he⟩ := d.isosceles_half_permutation heq hscalene
    let f : Equiv.Perm (Fin 3) := (Equiv.swap 0 1).trans (Equiv.swap 0 2)
    refine ⟨f.trans e, ?_⟩
    right; right; left
    change T.angle (e 1) = Real.pi / 6 ∧ T.angle (e 2) = Real.pi / 2 ∧
      T.angle (e 0) = Real.pi / 3
    rw [he, he, he, d.tile.firstHalf_angle_one,
      d.tile.firstHalf_angle_two_of_isosceles heq,
      d.tile.firstHalf_angle_zero_of_isosceles heq, hα]
    constructor
    · rfl
    · constructor
      · rfl
      · ring
  · exact eightCases_of_not_injective_angles T hscalene

theorem isosceles_tile_necessary {T : Triangle} {n : ℕ} (d : Tiling T n)
    (i j : Fin 3) (hij : i ≠ j) (heq : d.tile.angle i = d.tile.angle j) : EightCases T := by
  have hf : Function.Injective (![i, j] : Fin 2 → Fin 3) := by
    intro x y h
    fin_cases x <;> fin_cases y <;> simp_all
  have hg : Function.Injective (![0, 1] : Fin 2 → Fin 3) := by
    intro x y h
    fin_cases x <;> fin_cases y <;> simp_all
  obtain ⟨e, he⟩ := Equiv.Perm.exists_extending_pair ![i, j] ![0, 1] hf hg
  have hei : e i = 0 := he 0
  have hej : e j = 1 := he 1
  have hbase : (d.reindexTile e).tile.angle 0 = (d.reindexTile e).tile.angle 1 := by
    change Triangle.angle (d.tile.reindex e) 0 = Triangle.angle (d.tile.reindex e) 1
    simpa only [Triangle.angle_reindex, ← hei, ← hej, Equiv.symm_apply_apply] using heq
  exact (d.reindexTile e).isosceles_tile_ordered_necessary hbase

theorem tile_angles_injective_of_counterexample {T : Triangle} {n : ℕ} (d : Tiling T n)
    (hnot : ¬ EightCases T) : Function.Injective d.tile.angle := by
  intro i j heq
  by_contra hij
  exact hnot (d.isosceles_tile_necessary i j hij heq)

end Erdos633b.Tiling
