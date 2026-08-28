import Wikipedia.HopfProblem.DegreeCollapseSpecialLinearPaths
import Mathlib.Analysis.Convex.Basic
import Mathlib.Topology.Sets.Opens

/-!
# Actual paths in either real determinant component

Normalize a matrix by one diagonal entry to get determinant one. Elementary
special-linear paths connect it to that diagonal matrix. Two same-sign
diagonal entries are connected by a literal straight segment.
-/

noncomputable section

open Matrix Set
open scoped Topology

namespace Wikipedia.HopfProblem.DegreeCollapse.LinearFramePaths

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def scalarDiagonal (i : ι) (a : ℝ) : Matrix ι ι ℝ := diagonal (fun k => if k = i then a else 1)

theorem det_scalarDiagonal (i : ι) (a : ℝ) : det (scalarDiagonal i a) = a := by
  simp [scalarDiagonal, det_diagonal]

theorem scalarDiagonal_mul (i : ι) (a b : ℝ) :
    scalarDiagonal i a * scalarDiagonal i b = scalarDiagonal i (a * b) := by
  rw [scalarDiagonal, scalarDiagonal, diagonal_mul_diagonal]
  congr 1
  funext k
  by_cases h : k = i <;> simp [h]

omit [Fintype ι] in
theorem scalarDiagonal_one (i : ι) : scalarDiagonal i 1 = 1 := by
  simp [scalarDiagonal]

omit [Fintype ι] in
theorem continuous_scalarDiagonal (i : ι) : Continuous (scalarDiagonal i) := by
  apply continuous_pi
  intro k
  apply continuous_pi
  intro l
  simp only [scalarDiagonal, diagonal_apply]
  by_cases hkl : k = l
  · simp only [hkl, ite_true]
    by_cases hli : l = i
    · simp only [hli, ite_true]
      fun_prop
    · simp only [hli, ite_false]
      fun_prop
  · simp only [hkl, ite_false]
    fun_prop

def determinantComponent (σ : ℝ) : TopologicalSpace.Opens (Matrix ι ι ℝ) :=
  ⟨{A | 0 < σ * det A},
    isOpen_lt continuous_const (continuous_const.mul continuous_id.matrix_det)⟩

def diagonalPoint (i : ι) {σ : ℝ} (A : determinantComponent (ι := ι) σ) :
    determinantComponent (ι := ι) σ :=
  ⟨scalarDiagonal i (det (A : Matrix ι ι ℝ)), by
    change 0 < σ * det (scalarDiagonal i (det (A : Matrix ι ι ℝ)))
    rw [det_scalarDiagonal]
    exact A.property⟩

variable [Nontrivial ι]

/-- A matrix is joined, within its determinant component, to one diagonal entry. -/
theorem joined_diagonal_to_matrix (i : ι) {σ : ℝ}
    (A : determinantComponent (ι := ι) σ) : Joined (diagonalPoint i A) A := by
  have ha : det (A : Matrix ι ι ℝ) ≠ 0 := by
    intro hz
    have hh : 0 < σ * det (A : Matrix ι ι ℝ) := A.property
    rw [hz, mul_zero] at hh
    exact lt_irrefl _ hh
  let N : SpecialLinearGroup ι ℝ :=
    ⟨scalarDiagonal i (det (A : Matrix ι ι ℝ))⁻¹ * (A : Matrix ι ι ℝ), by
      rw [det_mul, det_scalarDiagonal, inv_mul_cancel₀ ha]⟩
  let ψ : SpecialLinearGroup ι ℝ → determinantComponent (ι := ι) σ := fun L =>
    ⟨scalarDiagonal i (det (A : Matrix ι ι ℝ)) * (L : Matrix ι ι ℝ), by
      change 0 < σ * det (scalarDiagonal i (det (A : Matrix ι ι ℝ)) * L.val)
      rw [det_mul, det_scalarDiagonal, L.property, mul_one]
      exact A.property⟩
  have hψ : Continuous ψ :=
    (continuous_const.mul continuous_subtype_val).subtype_mk _
  have h0 : ψ 1 = diagonalPoint i A := by
    apply Subtype.ext
    change scalarDiagonal i (det (A : Matrix ι ι ℝ)) * 1 = _
    rw [mul_one]
    rfl
  have h1 : ψ N = A := by
    apply Subtype.ext
    change scalarDiagonal i (det (A : Matrix ι ι ℝ)) *
      (scalarDiagonal i (det (A : Matrix ι ι ℝ))⁻¹ * (A : Matrix ι ι ℝ)) = _
    rw [← mul_assoc, scalarDiagonal_mul, mul_inv_cancel₀ ha, scalarDiagonal_one, one_mul]
  have h := (joined_one_specialLinear N).map hψ
  rwa [h0, h1] at h

omit [Nontrivial ι] in
/-- The scalar diagonal entries stay in the selected open half-line throughout the path. -/
theorem joined_diagonal_points (i : ι) {σ : ℝ}
    (A B : determinantComponent (ι := ι) σ) : Joined (diagonalPoint i A) (diagonalPoint i B) := by
  let g := fun t : unitInterval =>
    (1 - (t : ℝ)) * det (A : Matrix ι ι ℝ) + (t : ℝ) * det (B : Matrix ι ι ℝ)
  have hg : Continuous g := by fun_prop
  have hpos (t : unitInterval) : 0 < σ * g t := by
    have hh := (convex_Ioi (0 : ℝ)) A.property B.property
      (sub_nonneg.mpr t.property.2) t.property.1 (show 1 - (t : ℝ) + (t : ℝ) = 1 by ring)
    change 0 < (1 - (t : ℝ)) * (σ * det (A : Matrix ι ι ℝ)) +
      (t : ℝ) * (σ * det (B : Matrix ι ι ℝ)) at hh
    convert hh using 1
    dsimp only [g]
    ring
  refine ⟨{
    toFun := fun t => ⟨scalarDiagonal i (g t), by
      change 0 < σ * det (scalarDiagonal i (g t))
      rw [det_scalarDiagonal]
      exact hpos t⟩
    continuous_toFun := ((continuous_scalarDiagonal i).comp hg).subtype_mk (fun t => by
      change 0 < σ * det (scalarDiagonal i (g t))
      rw [det_scalarDiagonal]
      exact hpos t)
    source' := ?_
    target' := ?_ }⟩
  · apply Subtype.ext
    simp [g, diagonalPoint]
  · apply Subtype.ext
    simp [g, diagonalPoint]

/-- Any two real matrices in the same determinant component have an actual continuous path. -/
theorem joined_determinantComponent {σ : ℝ} (A B : determinantComponent (ι := ι) σ) :
    Joined A B := by
  let i := Classical.choice (inferInstance : Nonempty ι)
  exact (joined_diagonal_to_matrix i A).symm.trans
    ((joined_diagonal_points i A B).trans (joined_diagonal_to_matrix i B))

end Wikipedia.HopfProblem.DegreeCollapse.LinearFramePaths
