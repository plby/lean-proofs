import Wikipedia.HopfProblem.SecondHurewiczSimplyConnectedTriangleBasic
import Mathlib.Analysis.Convex.StdSimplex

/-!
# Based faces of an actual tetrahedron

The one-skeleton consists of the points having at least two zero barycentric
coordinates. In particular every face of a tetrahedron which sends this
one-skeleton to the base point is an actual based singular triangle.
-/

noncomputable section

open scoped Topology unitInterval

namespace Wikipedia.HopfProblem.SecondHurewicz.SimplyConnected

open FirstHurewicz

/-- The entire geometric one-skeleton of the standard tetrahedron. -/
def tetrahedronOneSkeleton : Set (Simplex 3) :=
  {s | ∃ i j : Fin 4, i ≠ j ∧ s i = 0 ∧ s j = 0}

/-- A singular tetrahedron with its actual whole one-skeleton based. -/
def BasedTetrahedron {X : Type} [TopologicalSpace X] (x : X) :=
  {τ : C(Simplex 3, X) // ∀ s ∈ tetrahedronOneSkeleton, τ s = x}

variable {X : Type} [TopologicalSpace X] {x : X}

theorem simplexFace_triangleBoundary (i : Fin 4) (s : Simplex 2)
    (hs : s ∈ triangleBoundary) : simplexFace 2 i s ∈ tetrahedronOneSkeleton := by
  obtain ⟨j, hj⟩ := hs
  exact ⟨i, i.succAbove j, (Fin.succAbove_ne i j).symm,
    simplexFace_apply_self 2 i s, (simplexFace_apply_succAbove 2 i s j).trans hj⟩

/-- The literal singular face, with its induced based-boundary condition. -/
def basedTetrahedronFace (τ : BasedTetrahedron x) (i : Fin 4) : BasedTriangle x :=
  ⟨τ.val.comp (simplexFace 2 i),
    fun s hs => τ.property _ (simplexFace_triangleBoundary i s hs)⟩

@[simp] theorem basedTetrahedronFace_apply (τ : BasedTetrahedron x)
    (i : Fin 4) (s : Simplex 2) :
    (basedTetrahedronFace τ i).val s = τ.val (simplexFace 2 i s) := rfl

/-- Affine interpolation inside a genuine standard simplex. -/
def tetrahedronSimplexBlend {n : ℕ} (t : I) (a b : Simplex n) : Simplex n :=
  ⟨(1 - (t : ℝ)) • (a : Fin (n + 1) → ℝ) + (t : ℝ) • (b : Fin (n + 1) → ℝ),
    convex_stdSimplex ℝ _ a.property b.property
      (sub_nonneg.mpr t.property.2) t.property.1 (by ring)⟩

@[simp] theorem tetrahedronSimplexBlend_apply {n : ℕ} (t : I)
    (a b : Simplex n) (i : Fin (n + 1)) :
    tetrahedronSimplexBlend t a b i = (1 - (t : ℝ)) * a i + (t : ℝ) * b i := rfl

@[simp] theorem tetrahedronSimplexBlend_zero {n : ℕ} (a b : Simplex n) :
    tetrahedronSimplexBlend 0 a b = a := by
  apply Subtype.ext
  funext i
  change tetrahedronSimplexBlend 0 a b i = a i
  simp

@[simp] theorem tetrahedronSimplexBlend_one {n : ℕ} (a b : Simplex n) :
    tetrahedronSimplexBlend 1 a b = b := by
  apply Subtype.ext
  funext i
  change tetrahedronSimplexBlend 1 a b i = b i
  simp

@[simp] theorem tetrahedronSimplexBlend_self {n : ℕ} (t : I) (a : Simplex n) :
    tetrahedronSimplexBlend t a a = a := by
  apply Subtype.ext
  funext i
  change (1 - (t : ℝ)) * a i + (t : ℝ) * a i = a i
  ring

def tetrahedronSimplexBlendMap {n : ℕ} {Y : Type} [TopologicalSpace Y]
    (f g : C(Y, Simplex n)) : C(I × Y, Simplex n) where
  toFun p := tetrahedronSimplexBlend p.1 (f p.2) (g p.2)
  continuous_toFun := by
    apply Continuous.subtype_mk
    apply continuous_pi
    intro i
    change Continuous fun p : I × Y =>
      (1 - (p.1 : ℝ)) * f p.2 i + (p.1 : ℝ) * g p.2 i
    have hf : Continuous fun p : I × Y => f p.2 i :=
      (continuous_apply i).comp
        (continuous_subtype_val.comp (f.continuous.comp continuous_snd))
    have hg : Continuous fun p : I × Y => g p.2 i :=
      (continuous_apply i).comp
        (continuous_subtype_val.comp (g.continuous.comp continuous_snd))
    exact ((continuous_const.sub (continuous_subtype_val.comp continuous_fst)).mul hf).add
      ((continuous_subtype_val.comp continuous_fst).mul hg)

/-- A common zero coordinate remains zero throughout affine interpolation. -/
theorem tetrahedronSimplexBlend_zero_coordinate {n : ℕ} (t : I)
    (a b : Simplex n) (i : Fin (n + 1)) (ha : a i = 0) (hb : b i = 0) :
    tetrahedronSimplexBlend t a b i = 0 := by
  simp [ha, hb]

theorem simplexFace_two_zero (s : Simplex 2) :
    (simplexFace 2 0 s : Fin 4 → ℝ) = ![0, s 0, s 1, s 2] := by
  funext i
  fin_cases i
  · exact simplexFace_apply_self 2 0 s
  · exact simplexFace_apply_succAbove 2 0 s 0
  · exact simplexFace_apply_succAbove 2 0 s 1
  · exact simplexFace_apply_succAbove 2 0 s 2

theorem simplexFace_two_one (s : Simplex 2) :
    (simplexFace 2 1 s : Fin 4 → ℝ) = ![s 0, 0, s 1, s 2] := by
  funext i
  fin_cases i
  · exact simplexFace_apply_succAbove 2 1 s 0
  · exact simplexFace_apply_self 2 1 s
  · exact simplexFace_apply_succAbove 2 1 s 1
  · exact simplexFace_apply_succAbove 2 1 s 2

theorem simplexFace_two_two (s : Simplex 2) :
    (simplexFace 2 2 s : Fin 4 → ℝ) = ![s 0, s 1, 0, s 2] := by
  funext i
  fin_cases i
  · exact simplexFace_apply_succAbove 2 2 s 0
  · exact simplexFace_apply_succAbove 2 2 s 1
  · exact simplexFace_apply_self 2 2 s
  · exact simplexFace_apply_succAbove 2 2 s 2

theorem simplexFace_two_three (s : Simplex 2) :
    (simplexFace 2 3 s : Fin 4 → ℝ) = ![s 0, s 1, s 2, 0] := by
  funext i
  fin_cases i
  · exact simplexFace_apply_succAbove 2 3 s 0
  · exact simplexFace_apply_succAbove 2 3 s 1
  · exact simplexFace_apply_succAbove 2 3 s 2
  · exact simplexFace_apply_self 2 3 s

end Wikipedia.HopfProblem.SecondHurewicz.SimplyConnected
