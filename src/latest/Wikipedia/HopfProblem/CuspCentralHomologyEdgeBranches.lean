import Wikipedia.HopfProblem.CuspCentralHomologyEdgeOrbits
import Wikipedia.HopfProblem.ToricBranchSeparation

/-!
# Branch labels along the actual honeycomb edge cylinders

An interior point of the compatible positive boundary arc has precisely
the two ambient branches labelled by zero and the corresponding hexagon
ray. Applying any of its circle phases preserves those labels. The two
ends are the original toric triple points.
-/

noncomputable section

open Set Topology

namespace Wikipedia.HopfProblem.CuspCentralHomology

open ToricCharts ToricFan ToricSpace ToricComponent CuspHoneycombHexagon
open CuspRetraction CuspPositiveRetraction CuspCollapse

theorem chartPoint_branchVertices_fst_zero (i : Fin 6) (z : CoordinateSpace 2)
    (hz0 : z 0 = 0) (hz1 : z 1 ≠ 0) :
    branchVertices (chartPoint i z : Space) = {0, hexagonRay i} := by
  rw [chartPoint_coe, branchVertices_inclusion]
  ext v
  change (∃ j, liftCoordinates i z j = 0 ∧ (zeroTriangle i).vertex j = v) ↔
    v = 0 ∨ v = hexagonRay i
  constructor
  · rintro ⟨j, hj, rfl⟩
    rcases coordinates_exhaustive i j with rfl | rfl | rfl
    · exact Or.inl (zeroTriangle_vertex i)
    · exact Or.inr (firstCoordinate_vertex i)
    · exact (hz1 (by simpa only [liftCoordinates_second] using hj)).elim
  · rintro (rfl | rfl)
    · exact ⟨zeroCoordinate i, liftCoordinates_zero i z, zeroTriangle_vertex i⟩
    · exact ⟨firstCoordinate i, (liftCoordinates_first i z).trans hz0,
        firstCoordinate_vertex i⟩

theorem chartPoint_branchVertices_snd_zero (i : Fin 6) (z : CoordinateSpace 2)
    (hz0 : z 0 ≠ 0) (hz1 : z 1 = 0) :
    branchVertices (chartPoint i z : Space) = {0, hexagonRay (i + 1)} := by
  rw [chartPoint_coe, branchVertices_inclusion]
  ext v
  change (∃ j, liftCoordinates i z j = 0 ∧ (zeroTriangle i).vertex j = v) ↔
    v = 0 ∨ v = hexagonRay (i + 1)
  constructor
  · rintro ⟨j, hj, rfl⟩
    rcases coordinates_exhaustive i j with rfl | rfl | rfl
    · exact Or.inl (zeroTriangle_vertex i)
    · exact (hz0 (by simpa only [liftCoordinates_first] using hj)).elim
    · exact Or.inr (secondCoordinate_vertex i)
  · rintro (rfl | rfl)
    · exact ⟨zeroCoordinate i, liftCoordinates_zero i z, zeroTriangle_vertex i⟩
    · exact ⟨secondCoordinate i, (liftCoordinates_second i z).trans hz1,
        secondCoordinate_vertex i⟩

/-- The literal open boundary has exactly its two ambient component labels. -/
theorem positiveBoundary_branchVertices (k : Fin 6) (q : positiveBoundary k)
    (hprev : q.1 ≠ squarePoint (k - 1) cornerZero)
    (hcurr : q.1 ≠ squarePoint k cornerZero) :
    branchVertices (q.1.1 : Space) = {0, hexagonRay k} := by
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
    exact chartPoint_branchVertices_fst_zero k z hz0 hz1
  · have hz0 : z 0 ≠ 0 := by
      intro hz0
      apply hprev
      simpa only [add_sub_cancel_right] using hqzero hz0 hz1
    rw [← he]
    exact chartPoint_branchVertices_snd_zero i z hz0 hz1

theorem compatibleBoundaryArc_branchVertices (C₀ : Matrix (Fin 2) (Fin 2) ℂ)
    (k : Fin 6) (t : unitInterval) (ht0 : t ≠ 0) (ht1 : t ≠ 1) :
    branchVertices ((compatibleBoundaryArc C₀ k t).1.1 : Space) = {0, hexagonRay k} := by
  apply positiveBoundary_branchVertices k (compatibleBoundaryArc C₀ k t)
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

/-- The prescribed positive arc lies in exactly the two indicated branches
at every parameter other than its endpoints. -/
theorem edgeArcPositive_branchVertices (C₀ : Matrix (Fin 2) (Fin 2) ℂ)
    (k : Fin 6) (t : unitInterval) (ht0 : t ≠ 0) (ht1 : t ≠ 1) :
    branchVertices ((edgeArcPositive C₀ k t).1 : Space) = {0, hexagonRay k} :=
  compatibleBoundaryArc_branchVertices C₀ k t ht0 ht1

/-- The original phase action does not change ambient branch labels. -/
theorem branchVertices_compactFibreAction (u : CompactFibreTorus) (x : Space) :
    branchVertices (compactFibreAction u x) = branchVertices x :=
  branchVertices_torusAction _ x

/-- Every point of the open cylinder has the same two actual branch labels. -/
theorem edgeCylinder_branchVertices (C₀ : Matrix (Fin 2) (Fin 2) ℂ)
    (k : Fin 6) (p : unitInterval × Circle) (ht0 : p.1 ≠ 0) (ht1 : p.1 ≠ 1) :
    branchVertices (edgeCylinder C₀ k p : Space) = {0, hexagonRay k} := by
  rw [edgeCylinder_coe, branchVertices_compactFibreAction]
  exact compatibleBoundaryArc_branchVertices C₀ k p.1 ht0 ht1

theorem edgeArcPositive_branchCount (C₀ : Matrix (Fin 2) (Fin 2) ℂ)
    (k : Fin 6) (t : unitInterval) (ht0 : t ≠ 0) (ht1 : t ≠ 1) :
    branchCount ((edgeArcPositive C₀ k t).1 : Space) = 2 := by
  rw [← branchVertices_ncard, edgeArcPositive_branchVertices C₀ k t ht0 ht1]
  exact Set.ncard_pair (hexagonRay_ne_zero k).symm

theorem edgeCylinder_branchCount (C₀ : Matrix (Fin 2) (Fin 2) ℂ)
    (k : Fin 6) (p : unitInterval × Circle) (ht0 : p.1 ≠ 0) (ht1 : p.1 ≠ 1) :
    branchCount (edgeCylinder C₀ k p : Space) = 2 := by
  rw [← branchVertices_ncard, edgeCylinder_branchVertices C₀ k p ht0 ht1]
  exact Set.ncard_pair (hexagonRay_ne_zero k).symm

@[simp] theorem edgeArcPositive_zero_branchCount (C₀ : Matrix (Fin 2) (Fin 2) ℂ)
    (k : Fin 6) : branchCount ((edgeArcPositive C₀ k 0).1 : Space) = 3 := by
  rw [edgeArcPositive_coe, compatibleBoundaryArc_zero_point, squarePoint_cornerZero_coe,
    branchCount_inclusion, zeroCount_zero]

@[simp] theorem edgeArcPositive_one_branchCount (C₀ : Matrix (Fin 2) (Fin 2) ℂ)
    (k : Fin 6) : branchCount ((edgeArcPositive C₀ k 1).1 : Space) = 3 := by
  rw [edgeArcPositive_coe, compatibleBoundaryArc_one_point, squarePoint_cornerZero_coe,
    branchCount_inclusion, zeroCount_zero]

@[simp] theorem edgeCylinder_zero_branchCount (C₀ : Matrix (Fin 2) (Fin 2) ℂ)
    (k : Fin 6) (a : Circle) : branchCount (edgeCylinder C₀ k (0, a) : Space) = 3 := by
  rw [edgeCylinder_zero_coe, branchCount_inclusion, zeroCount_zero]

@[simp] theorem edgeCylinder_one_branchCount (C₀ : Matrix (Fin 2) (Fin 2) ℂ)
    (k : Fin 6) (a : Circle) : branchCount (edgeCylinder C₀ k (1, a) : Space) = 3 := by
  rw [edgeCylinder_one_coe, branchCount_inclusion, zeroCount_zero]

/-- The cylinder meets the triple locus exactly at its two collapsed ends. -/
theorem edgeCylinder_branchCount_eq_three_iff (C₀ : Matrix (Fin 2) (Fin 2) ℂ)
    (k : Fin 6) (p : unitInterval × Circle) :
    branchCount (edgeCylinder C₀ k p : Space) = 3 ↔ p.1 = 0 ∨ p.1 = 1 := by
  rcases p with ⟨t, a⟩
  by_cases ht0 : t = 0
  · subst t
    rw [edgeCylinder_zero_branchCount]
    simp
  by_cases ht1 : t = 1
  · subst t
    rw [edgeCylinder_one_branchCount]
    simp
  rw [edgeCylinder_branchCount C₀ k (t, a) ht0 ht1]
  simp [ht0, ht1]

theorem edgeCylinder_branchCount_eq_two_iff (C₀ : Matrix (Fin 2) (Fin 2) ℂ)
    (k : Fin 6) (p : unitInterval × Circle) :
    branchCount (edgeCylinder C₀ k p : Space) = 2 ↔ p.1 ≠ 0 ∧ p.1 ≠ 1 := by
  rcases p with ⟨t, a⟩
  by_cases ht0 : t = 0
  · subst t
    rw [edgeCylinder_zero_branchCount]
    simp
  by_cases ht1 : t = 1
  · subst t
    rw [edgeCylinder_one_branchCount]
    simp
  rw [edgeCylinder_branchCount C₀ k (t, a) ht0 ht1]
  simp [ht0, ht1]

end Wikipedia.HopfProblem.CuspCentralHomology
