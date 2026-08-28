import Wikipedia.HopfProblem.ThirdHurewiczThreeSimplexCycles
import Wikipedia.HopfProblem.ThirdHurewiczCubeSubdivisionGeometry
import Mathlib.Order.Preorder.Finite

/-!
# The simplex quotient on the six actual cube tetrahedra

On the positively ordered tetrahedron the quotient is exactly the identity
simplex. Every other ordering maps into the simplex boundary. The proof uses
the actual affine coordinates and finite-order monotonicity, not a degree
or Hurewicz theorem.
-/

noncomputable section

open scoped Topology unitInterval

namespace Wikipedia.HopfProblem.ThirdHurewicz

open FirstHurewicz Geometry

theorem threeSimplex_coordinate_sum (s : Simplex 3) :
    s 0 + (s 1 + s 2 + s 3) = 1 := by
  have hs := stdSimplex.sum_eq_one s
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hs
  change s 0 + (s 1 + (s 2 + s 3)) = 1 at hs
  linarith

/-- The principal affine tetrahedron is a genuine section of the PL quotient. -/
theorem threeSimplexQuotient_cubeTetrahedron_refl :
    threeSimplexQuotient.comp (cubeTetrahedron (Equiv.refl (Fin 3))) =
      ContinuousMap.id (Simplex 3) := by
  apply ContinuousMap.ext
  intro s
  apply Subtype.ext
  funext i
  have h₁ : s 2 + s 3 ≤ s 1 + s 2 + s 3 := by
    linarith [stdSimplex.zero_le s 1]
  have h₂ : s 3 ≤ s 2 + s 3 := le_add_of_nonneg_left (stdSimplex.zero_le s 2)
  have h₃ : s 3 ≤ s 1 + s 2 + s 3 := h₂.trans h₁
  have hu₀ := cubeTetrahedron_coordinate_zero (Equiv.refl (Fin 3)) s
  have hu₁ := cubeTetrahedron_coordinate_one (Equiv.refl (Fin 3)) s
  have hu₂ := cubeTetrahedron_coordinate_two (Equiv.refl (Fin 3)) s
  change (cubeTetrahedron (Equiv.refl (Fin 3)) s 0 : ℝ) = _ at hu₀
  change (cubeTetrahedron (Equiv.refl (Fin 3)) s 1 : ℝ) = _ at hu₁
  change (cubeTetrahedron (Equiv.refl (Fin 3)) s 2 : ℝ) = _ at hu₂
  fin_cases i
  · change 1 - (cubeTetrahedron (Equiv.refl (Fin 3)) s 0 : ℝ) = s 0
    rw [hu₀]
    linarith [threeSimplex_coordinate_sum s]
  · change (cubeTetrahedron (Equiv.refl (Fin 3)) s 0 : ℝ) -
      min (cubeTetrahedron (Equiv.refl (Fin 3)) s 0 : ℝ)
        (cubeTetrahedron (Equiv.refl (Fin 3)) s 1 : ℝ) = s 1
    rw [hu₀, hu₁, min_eq_right h₁]
    ring
  · change min (cubeTetrahedron (Equiv.refl (Fin 3)) s 0 : ℝ)
        (cubeTetrahedron (Equiv.refl (Fin 3)) s 1 : ℝ) -
      min (cubeTetrahedron (Equiv.refl (Fin 3)) s 0 : ℝ)
        (min (cubeTetrahedron (Equiv.refl (Fin 3)) s 1 : ℝ)
          (cubeTetrahedron (Equiv.refl (Fin 3)) s 2 : ℝ)) = s 2
    rw [hu₀, hu₁, hu₂, min_eq_right h₁, min_eq_right h₂, min_eq_right h₃]
    ring
  · change min (cubeTetrahedron (Equiv.refl (Fin 3)) s 0 : ℝ)
        (min (cubeTetrahedron (Equiv.refl (Fin 3)) s 1 : ℝ)
          (cubeTetrahedron (Equiv.refl (Fin 3)) s 2 : ℝ)) = s 3
    rw [hu₀, hu₁, hu₂, min_eq_right h₂, min_eq_right h₃]

theorem cubeTetrahedron_coordinates_antitone (e : Equiv.Perm (Fin 3)) (s : Simplex 3) :
    Antitone (fun i => (cubeTetrahedron e s (e i) : ℝ)) := by
  apply Fin.antitone_iff_succ_le.mpr
  intro i
  fin_cases i
  · exact cubeTetrahedron_order_first e s
  · exact cubeTetrahedron_order_second e s

/-- A nonidentity order has a coordinate inversion in the fixed native order. -/
theorem cubeTetrahedron_coordinate_inversion (e : Equiv.Perm (Fin 3))
    (he : e ≠ Equiv.refl (Fin 3)) (s : Simplex 3) :
    (cubeTetrahedron e s 0 : ℝ) ≤ cubeTetrahedron e s 1 ∨
      (cubeTetrahedron e s 1 : ℝ) ≤ cubeTetrahedron e s 2 := by
  by_contra h
  obtain ⟨h₁, h₂⟩ := not_or.mp h
  have hu : StrictAnti (fun i => (cubeTetrahedron e s i : ℝ)) := by
    apply Fin.strictAnti_iff_succ_lt.mpr
    intro i
    fin_cases i
    · exact lt_of_not_ge h₁
    · exact lt_of_not_ge h₂
  have hm : Monotone e := by
    intro i j hij
    exact hu.le_iff_ge.mp (cubeTetrahedron_coordinates_antitone e s hij)
  apply he
  apply Equiv.ext
  intro i
  exact (hm.strictMono_of_injective e.injective).apply_eq

/-- Every other actual affine cube tetrahedron lands in the simplex boundary. -/
theorem threeSimplexQuotient_cubeTetrahedron_boundary (e : Equiv.Perm (Fin 3))
    (he : e ≠ Equiv.refl (Fin 3)) (s : Simplex 3) :
    threeSimplexQuotient (cubeTetrahedron e s) ∈ threeSimplexBoundary := by
  rcases cubeTetrahedron_coordinate_inversion e he s with h | h
  · exact threeSimplexQuotient_boundary_of_first_le _ h
  · exact threeSimplexQuotient_boundary_of_second_le _ h

variable {X : Type} [TopologicalSpace X] {x : X}

theorem basedThreeSimplexLoop_cubeTetrahedron_refl (τ : BasedThreeSimplex x) :
    (basedThreeSimplexLoop τ).val.comp (cubeTetrahedron (Equiv.refl (Fin 3))) = τ.val := by
  change (τ.val.comp threeSimplexQuotient).comp _ = _
  rw [ContinuousMap.comp_assoc, threeSimplexQuotient_cubeTetrahedron_refl,
    ContinuousMap.comp_id]

theorem basedThreeSimplexLoop_cubeTetrahedron_other (τ : BasedThreeSimplex x)
    (e : Equiv.Perm (Fin 3)) (he : e ≠ Equiv.refl (Fin 3)) :
    (basedThreeSimplexLoop τ).val.comp (cubeTetrahedron e) =
      ContinuousMap.const (Simplex 3) x := by
  apply ContinuousMap.ext
  intro s
  exact τ.property _ (threeSimplexQuotient_cubeTetrahedron_boundary e he s)

/-- The actual three-simplex quotient is onto the entire simplex. -/
theorem threeSimplexQuotient_surjective : Function.Surjective threeSimplexQuotient := by
  intro s
  exact ⟨cubeTetrahedron (Equiv.refl (Fin 3)) s,
    ContinuousMap.congr_fun threeSimplexQuotient_cubeTetrahedron_refl s⟩

end Wikipedia.HopfProblem.ThirdHurewicz
