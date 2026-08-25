import StackExchange.Puzzling139335.JordanRegion
import StackExchange.Puzzling139335.Basic

/-!
# Local ownership and the final boundary formulation

Closedness of the finitely many other pieces gives a neighborhood owned by
the only piece incident at a point. At square corners this is a relative
neighborhood in the square, not an ambient interior neighborhood.
-/

open Set Metric

namespace Puzzling139335

theorem squareCenter_mem_interior_unitSquare : squareCenter ∈ interior unitSquare := by
  let U : Set Plane := {p | p 0 ∈ Ioo (0 : ℝ) 1 ∧ p 1 ∈ Ioo (0 : ℝ) 1}
  have hU : IsOpen U :=
    (isOpen_Ioo.preimage (EuclideanSpace.proj (0 : Fin 2)).continuous).inter
      (isOpen_Ioo.preimage (EuclideanSpace.proj (1 : Fin 2)).continuous)
  have hsub : U ⊆ unitSquare := by
    intro p hp
    exact ⟨⟨hp.1.1.le, hp.1.2.le⟩, ⟨hp.2.1.le, hp.2.2.le⟩⟩
  apply interior_mono hsub
  rw [hU.interior_eq]
  norm_num [U, squareCenter]

/-- If all other closed pieces omit a point, one piece owns its relative
square neighborhood. This does not assume the point is interior to the square. -/
theorem SquareDissection.unique_piece_relative_neighborhood (d : SquareDissection)
    (i : Fin 4) {p : Plane} (hunique : ∀ j, j ≠ i → p ∉ d.piece j) :
    ∃ ε : ℝ, 0 < ε ∧ ball p ε ∩ unitSquare ⊆ d.piece i := by
  classical
  let U : Set Plane := ⋂ j : Fin 4, if j = i then Set.univ else (d.piece j)ᶜ
  have hU : IsOpen U := by
    apply isOpen_iInter_of_finite
    intro j
    split_ifs
    · exact isOpen_univ
    · exact (d.jordan j).isClosed.isOpen_compl
  have hpU : p ∈ U := by
    apply mem_iInter.mpr
    intro j
    split_ifs with hji
    · trivial
    · exact hunique j hji
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp (hU.mem_nhds hpU)
  refine ⟨ε, hε, ?_⟩
  intro x hx
  obtain ⟨j, hj⟩ := d.exists_piece_mem hx.2
  by_cases hji : j = i
  · simpa only [hji] using hj
  · have hxU : x ∈ U := hball hx.1
    have hxnot : x ∉ d.piece j := by
      change x ∈ (d.piece j)ᶜ
      simpa only [if_neg hji] using mem_iInter.mp hxU j
    exact False.elim (hxnot hj)

theorem SquareDissection.mem_interior_of_unique_piece (d : SquareDissection)
    (i : Fin 4) {p : Plane} (hp : p ∈ interior unitSquare)
    (hunique : ∀ j, j ≠ i → p ∉ d.piece j) : p ∈ interior (d.piece i) := by
  obtain ⟨ε, hε, hsub⟩ := d.unique_piece_relative_neighborhood i hunique
  have hV : IsOpen (ball p ε ∩ interior unitSquare) := isOpen_ball.inter isOpen_interior
  have hsub' : ball p ε ∩ interior unitSquare ⊆ d.piece i :=
    fun x hx => hsub ⟨hx.1, interior_subset hx.2⟩
  apply interior_mono hsub'
  rw [hV.interior_eq]
  exact ⟨mem_ball_self hε, hp⟩

/-- Once the geometric impossibility is proved, the center belongs to at
least two boundaries. This lemma does not assert the missing impossibility. -/
theorem SquareDissection.center_mem_two_frontiers_of_not_protected (d : SquareDissection)
    (h : ¬ d.HasProtectedCenter) :
    ∃ i j : Fin 4, i ≠ j ∧ squareCenter ∈ frontier (d.piece i) ∧
      squareCenter ∈ frontier (d.piece j) := by
  classical
  have hnot : ∀ i, squareCenter ∉ interior (d.piece i) := fun i hi => h ⟨i, hi⟩
  obtain ⟨i, hi⟩ := d.exists_piece_mem squareCenter_mem_unitSquare
  have hex : ∃ j, j ≠ i ∧ squareCenter ∈ d.piece j := by
    by_contra hnone
    apply hnot i
    apply d.mem_interior_of_unique_piece i squareCenter_mem_interior_unitSquare
    intro j hji hj
    exact hnone ⟨j, hji, hj⟩
  obtain ⟨j, hji, hj⟩ := hex
  refine ⟨i, j, hji.symm, ?_, ?_⟩
  · rw [(d.jordan i).isClosed.frontier_eq]
    exact ⟨hi, hnot i⟩
  · rw [(d.jordan j).isClosed.frontier_eq]
    exact ⟨hj, hnot j⟩

end Puzzling139335
