import Wikipedia.HopfProblem.CuspHoneycombCompatibleArcs
import Wikipedia.HopfProblem.CuspCollapseStabilizersGroups

/-!
# The actual open honeycomb edges have their prescribed circle stabilizers

In every oriented chart, a boundary point away from its two toric origins
has exactly two zero ambient coordinates. The stabilizer calculation for
the genuine fibre-torus action therefore gives the circle of the boundary
ray. This geometric statement applies to every compatible boundary arc,
including those transported by the actual opposite-side gluing.
-/

noncomputable section

open Set Topology

namespace Wikipedia.HopfProblem.CuspCentralHomology

open ToricCharts ToricFan ToricSpace ToricComponent CuspHoneycombHexagon

theorem chartPoint_stabilizer_fst_zero (i : Fin 6) (z : CoordinateSpace 2)
    (hz0 : z 0 = 0) (hz1 : z 1 ≠ 0) :
    MulAction.stabilizer CompactFibreTorus (chartPoint i z : Space) =
      edgeCircle (hexagonRay i) := by
  have hne : zeroCoordinate i ≠ firstCoordinate i := by
    intro h
    have hv := congrArg (zeroTriangle i).vertex h
    rw [zeroTriangle_vertex, firstCoordinate_vertex] at hv
    exact hexagonRay_ne_zero i hv.symm
  have hrest (j : Fin 3) (hj0 : j ≠ zeroCoordinate i) (hj1 : j ≠ firstCoordinate i) :
      liftCoordinates i z j ≠ 0 := by
    rcases coordinates_exhaustive i j with h | h | h
    · exact (hj0 h).elim
    · exact (hj1 h).elim
    · subst j
      simpa only [liftCoordinates_second] using hz1
  rw [chartPoint_coe]
  have h := compactFibre_stabilizer_eq_edgeCircle_of_two_zero (zeroTriangle i)
    (liftCoordinates i z) (zeroCoordinate i) (firstCoordinate i) hne
    (liftCoordinates_zero i z) (by simpa only [liftCoordinates_first] using hz0) hrest
  simpa only [firstCoordinate_vertex, zeroTriangle_vertex, sub_zero] using h

theorem chartPoint_stabilizer_snd_zero (i : Fin 6) (z : CoordinateSpace 2)
    (hz0 : z 0 ≠ 0) (hz1 : z 1 = 0) :
    MulAction.stabilizer CompactFibreTorus (chartPoint i z : Space) =
      edgeCircle (hexagonRay (i + 1)) := by
  have hne : zeroCoordinate i ≠ secondCoordinate i := by
    intro h
    have hv := congrArg (zeroTriangle i).vertex h
    rw [zeroTriangle_vertex, secondCoordinate_vertex] at hv
    exact hexagonRay_ne_zero (i + 1) hv.symm
  have hrest (j : Fin 3) (hj0 : j ≠ zeroCoordinate i) (hj1 : j ≠ secondCoordinate i) :
      liftCoordinates i z j ≠ 0 := by
    rcases coordinates_exhaustive i j with h | h | h
    · exact (hj0 h).elim
    · subst j
      simpa only [liftCoordinates_first] using hz0
    · exact (hj1 h).elim
  rw [chartPoint_coe]
  have h := compactFibre_stabilizer_eq_edgeCircle_of_two_zero (zeroTriangle i)
    (liftCoordinates i z) (zeroCoordinate i) (secondCoordinate i) hne
    (liftCoordinates_zero i z) (by simpa only [liftCoordinates_second] using hz1) hrest
  simpa only [secondCoordinate_vertex, zeroTriangle_vertex, sub_zero] using h

/-- Every actual positive boundary point other than its two triple points
has precisely the circle stabilizer of the boundary ray. -/
theorem positiveBoundary_stabilizer_eq_edgeCircle (k : Fin 6) (q : positiveBoundary k)
    (hprev : q.1 ≠ squarePoint (k - 1) cornerZero)
    (hcurr : q.1 ≠ squarePoint k cornerZero) :
    MulAction.stabilizer CompactFibreTorus (q.1.1 : Space) = edgeCircle (hexagonRay k) := by
  obtain ⟨i, z, he⟩ := chartPoint_jointly_surjective q.1.1
  have hqzero (hz0 : z 0 = 0) (hz1 : z 1 = 0) : q.1 = squarePoint i cornerZero := by
    apply Subtype.ext
    change q.1.1 = chartPoint i (fun j => (cornerZero.1 j : ℂ))
    rw [← he]
    apply congrArg (chartPoint i)
    funext j
    fin_cases j
    · change z 0 = 0
      exact hz0
    · change z 1 = 0
      exact hz1
  have hb : (chartPoint i z : Space) ∈ rayDivisor (hexagonRay k) := by
    rw [he]
    exact q.property
  rcases (chartPoint_mem_rayDivisor_iff i k z).mp hb with ⟨rfl, hz0⟩ | ⟨rfl, hz1⟩
  · have hz1 : z 1 ≠ 0 := fun hz1 => hcurr (hqzero hz0 hz1)
    rw [← he]
    exact chartPoint_stabilizer_fst_zero k z hz0 hz1
  · have hz0 : z 0 ≠ 0 := by
      intro hz0
      apply hprev
      simpa only [add_sub_cancel_right] using hqzero hz0 hz1
    rw [← he]
    exact chartPoint_stabilizer_snd_zero i z hz0 hz1

/-- Open points of every compatible arc have the prescribed actual fibre-torus stabilizer. -/
theorem compatibleBoundaryArc_stabilizer (C₀ : Matrix (Fin 2) (Fin 2) ℂ)
    (k : Fin 6) (t : unitInterval) (ht0 : t ≠ 0) (ht1 : t ≠ 1) :
    MulAction.stabilizer CompactFibreTorus ((compatibleBoundaryArc C₀ k t).1.1 : Space) =
      edgeCircle (hexagonRay k) := by
  apply positiveBoundary_stabilizer_eq_edgeCircle k (compatibleBoundaryArc C₀ k t)
  · intro h
    apply ht0
    apply (compatibleBoundaryArc C₀ k).injective
    apply Subtype.ext
    exact h.trans (compatibleBoundaryArc_zero_point C₀ k).symm
  · intro h
    apply ht1
    apply (compatibleBoundaryArc C₀ k).injective
    apply Subtype.ext
    exact h.trans (compatibleBoundaryArc_one_point C₀ k).symm

theorem compatibleBoundaryArc_stabilizer_of_pos_lt_one
    (C₀ : Matrix (Fin 2) (Fin 2) ℂ) (k : Fin 6) (t : unitInterval)
    (ht0 : 0 < (t : ℝ)) (ht1 : (t : ℝ) < 1) :
    MulAction.stabilizer CompactFibreTorus ((compatibleBoundaryArc C₀ k t).1.1 : Space) =
      edgeCircle (hexagonRay k) :=
  compatibleBoundaryArc_stabilizer C₀ k t
    (fun h => (ne_of_gt ht0) (congrArg Subtype.val h))
    (fun h => (ne_of_lt ht1) (congrArg Subtype.val h))

@[simp] theorem compatibleBoundaryArc_stabilizer_zero
    (C₀ : Matrix (Fin 2) (Fin 2) ℂ) (k : Fin 6) :
    MulAction.stabilizer CompactFibreTorus ((compatibleBoundaryArc C₀ k 0).1.1 : Space) = ⊤ := by
  rw [compatibleBoundaryArc_zero_point, squarePoint_cornerZero_coe]
  exact compactFibre_stabilizer_inclusion_zero _

@[simp] theorem compatibleBoundaryArc_stabilizer_one
    (C₀ : Matrix (Fin 2) (Fin 2) ℂ) (k : Fin 6) :
    MulAction.stabilizer CompactFibreTorus ((compatibleBoundaryArc C₀ k 1).1.1 : Space) = ⊤ := by
  rw [compatibleBoundaryArc_one_point, squarePoint_cornerZero_coe]
  exact compactFibre_stabilizer_inclusion_zero _

end Wikipedia.HopfProblem.CuspCentralHomology
