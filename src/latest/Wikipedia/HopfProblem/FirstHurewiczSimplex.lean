import Mathlib.AlgebraicTopology.TopologicalSimplex
import Mathlib.Topology.Homotopy.Path
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Path simplices and the concatenation triangle

The simplices here are Mathlib's actual standard topological simplices,
with the actual cosimplicial face maps. A path is a singular one-simplex
via the standard homeomorphism `Δ¹ ≃ [0,1]`.
-/

noncomputable section

open Set
open scoped Simplicial

namespace Wikipedia.HopfProblem.FirstHurewicz

/-- The actual standard topological `n`-simplex. -/
abbrev Simplex (n : ℕ) := stdSimplex ℝ (Fin (n + 1))

/-- The actual face map, deleting vertex `i`. -/
def simplexFace (n : ℕ) (i : Fin (n + 2)) : C(Simplex n, Simplex (n + 1)) :=
  ⟨stdSimplex.map (SimplexCategory.δ i).toOrderHom,
    stdSimplex.continuous_map (SimplexCategory.δ i).toOrderHom⟩

theorem simplexFace_apply (n : ℕ) (i : Fin (n + 2)) (s : Simplex n) :
    simplexFace n i s = stdSimplex.map i.succAbove s := rfl

/-- These are exactly the face maps used in Mathlib's topological simplex
functor, not replacement maps with an assumed compatibility. -/
theorem simplexFace_toTop (n : ℕ) (i : Fin (n + 2)) :
    simplexFace n i = (SimplexCategory.toTop₀.map (SimplexCategory.δ i)).hom := rfl

/-- Each barycentric coordinate takes values in the unit interval. -/
def simplexCoordinate (n : ℕ) (i : Fin (n + 1)) : C(Simplex n, unitInterval) where
  toFun s := ⟨s i, stdSimplex.zero_le s i, stdSimplex.le_one s i⟩
  continuous_toFun := ((continuous_apply i).comp continuous_subtype_val).subtype_mk _

@[simp] theorem simplexCoordinate_coe (n : ℕ) (i : Fin (n + 1)) (s : Simplex n) :
    (simplexCoordinate n i s : ℝ) = s i := rfl

@[simp] theorem simplexFace_apply_self (n : ℕ) (i : Fin (n + 2)) (s : Simplex n) :
    simplexFace n i s i = 0 := by
  change FunOnFinite.linearMap ℝ ℝ i.succAbove (s : Fin (n + 1) → ℝ) i = 0
  rw [FunOnFinite.linearMap_apply_apply]
  apply Finset.sum_eq_zero
  intro k hk
  exact False.elim (Fin.succAbove_ne i k (Finset.mem_filter.mp hk).2)

@[simp] theorem simplexFace_apply_succAbove (n : ℕ) (i : Fin (n + 2))
    (s : Simplex n) (k : Fin (n + 1)) :
    simplexFace n i s (i.succAbove k) = s k := by
  change FunOnFinite.linearMap ℝ ℝ i.succAbove (s : Fin (n + 1) → ℝ)
    (i.succAbove k) = s k
  simp [FunOnFinite.linearMap_apply_apply, Fin.succAbove_right_injective.eq_iff,
    Finset.sum_filter]

/-- The three triangle faces insert a zero into the two edge coordinates. -/
theorem simplexFace_one_zero (s : Simplex 1) :
    (simplexFace 1 0 s : Fin 3 → ℝ) = ![0, s 0, s 1] := by
  funext k
  fin_cases k
  · exact simplexFace_apply_self 1 0 s
  · exact simplexFace_apply_succAbove 1 0 s 0
  · exact simplexFace_apply_succAbove 1 0 s 1

theorem simplexFace_one_one (s : Simplex 1) :
    (simplexFace 1 1 s : Fin 3 → ℝ) = ![s 0, 0, s 1] := by
  funext k
  fin_cases k
  · exact simplexFace_apply_succAbove 1 1 s 0
  · exact simplexFace_apply_self 1 1 s
  · exact simplexFace_apply_succAbove 1 1 s 1

theorem simplexFace_one_two (s : Simplex 1) :
    (simplexFace 1 2 s : Fin 3 → ℝ) = ![s 0, s 1, 0] := by
  funext k
  fin_cases k
  · exact simplexFace_apply_succAbove 1 2 s 0
  · exact simplexFace_apply_succAbove 1 2 s 1
  · exact simplexFace_apply_self 1 2 s

theorem simplexZero_eq_vertex (s : Simplex 0) :
    s = stdSimplex.vertex (S := ℝ) (0 : Fin 1) := by
  let : Unique (Fin (0 + 1)) := inferInstanceAs (Unique (Fin 1))
  apply Subtype.ext
  funext k
  fin_cases k
  change s 0 = 1
  exact stdSimplex.eq_one_of_unique (s : stdSimplex ℝ (Fin 1)) (0 : Fin 1)

@[simp] theorem simplexFace_zero_zero (s : Simplex 0) :
    simplexFace 0 0 s = stdSimplex.vertex (S := ℝ) (1 : Fin 2) := by
  rw [simplexZero_eq_vertex s, simplexFace_apply, stdSimplex.map_vertex]
  rfl

@[simp] theorem simplexFace_zero_one (s : Simplex 0) :
    simplexFace 0 1 s = stdSimplex.vertex (S := ℝ) (0 : Fin 2) := by
  rw [simplexZero_eq_vertex s, simplexFace_apply, stdSimplex.map_vertex]
  rfl

variable {X : Type*} [TopologicalSpace X] {x y z : X}

/-- A path as a singular one-simplex in the standard barycentric model. -/
def pathSimplex (p : Path x y) : C(Simplex 1, X) :=
  p.toContinuousMap.comp
    ⟨stdSimplexHomeomorphUnitInterval, stdSimplexHomeomorphUnitInterval.continuous⟩

theorem pathSimplex_apply (p : Path x y) (s : Simplex 1) :
    pathSimplex p s = p (simplexCoordinate 1 1 s) := rfl

@[simp] theorem pathSimplex_vertex_zero (p : Path x y) :
    pathSimplex p (stdSimplex.vertex (S := ℝ) (0 : Fin 2)) = x := by
  change p (stdSimplexHomeomorphUnitInterval _) = x
  rw [stdSimplexHomeomorphUnitInterval_zero, p.source]

@[simp] theorem pathSimplex_vertex_one (p : Path x y) :
    pathSimplex p (stdSimplex.vertex (S := ℝ) (1 : Fin 2)) = y := by
  change p (stdSimplexHomeomorphUnitInterval _) = y
  rw [stdSimplexHomeomorphUnitInterval_one, p.target]

/-- With the standard face numbering, `δ₀` gives the target. -/
@[simp] theorem pathSimplex_face_zero (p : Path x y) :
    (pathSimplex p).comp (simplexFace 0 0) = ContinuousMap.const (Simplex 0) y := by
  apply ContinuousMap.ext
  intro s
  change pathSimplex p (simplexFace 0 0 s) = y
  rw [simplexFace_zero_zero, pathSimplex_vertex_one]

/-- With the standard face numbering, `δ₁` gives the source. -/
@[simp] theorem pathSimplex_face_one (p : Path x y) :
    (pathSimplex p).comp (simplexFace 0 1) = ContinuousMap.const (Simplex 0) x := by
  apply ContinuousMap.ext
  intro s
  change pathSimplex p (simplexFace 0 1 s) = x
  rw [simplexFace_zero_one, pathSimplex_vertex_zero]

/-- Conversely, an actual singular one-simplex is a path between its two
actual vertices. -/
def simplexPath (σ : C(Simplex 1, X)) :
    Path (σ (stdSimplex.vertex (S := ℝ) (0 : Fin 2)))
      (σ (stdSimplex.vertex (S := ℝ) (1 : Fin 2))) where
  toFun t := σ (stdSimplexHomeomorphUnitInterval.symm t)
  continuous_toFun := σ.continuous.comp stdSimplexHomeomorphUnitInterval.symm.continuous
  source' := congrArg σ (stdSimplexHomeomorphUnitInterval.symm_apply_eq.mpr
    stdSimplexHomeomorphUnitInterval_zero.symm)
  target' := congrArg σ (stdSimplexHomeomorphUnitInterval.symm_apply_eq.mpr
    stdSimplexHomeomorphUnitInterval_one.symm)

@[simp] theorem pathSimplex_simplexPath (σ : C(Simplex 1, X)) :
    pathSimplex (simplexPath σ) = σ := by
  apply ContinuousMap.ext
  intro s
  change σ (stdSimplexHomeomorphUnitInterval.symm (stdSimplexHomeomorphUnitInterval s)) = σ s
  rw [Homeomorph.symm_apply_apply]

/-- Affine time on the triangle, with vertex values `0`, `1/2`, and `1`. -/
def concatTime : C(Simplex 2, unitInterval) where
  toFun s := ⟨s 1 / 2 + s 2, by
    have h0 := stdSimplex.zero_le s 0
    have h1 := stdSimplex.zero_le s 1
    have h2 := stdSimplex.zero_le s 2
    have hs := stdSimplex.sum_eq_one s
    simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hs
    change s 0 + (s 1 + s 2) = 1 at hs
    constructor <;> linarith⟩
  continuous_toFun := by
    apply Continuous.subtype_mk
    exact ((continuous_apply (1 : Fin 3)).comp continuous_subtype_val).div_const 2 |>.add
      ((continuous_apply (2 : Fin 3)).comp continuous_subtype_val)

@[simp] theorem concatTime_coe (s : Simplex 2) :
    (concatTime s : ℝ) = s 1 / 2 + s 2 := rfl

/-- The actual singular triangle recording concatenation of two paths. -/
def concatSimplex (p : Path x y) (q : Path y z) : C(Simplex 2, X) :=
  (p.trans q).toContinuousMap.comp concatTime

theorem concatSimplex_apply (p : Path x y) (q : Path y z) (s : Simplex 2) :
    concatSimplex p q s = (p.trans q).extend (s 1 / 2 + s 2) :=
  (Path.extend_apply (p.trans q) (concatTime s).property).symm

/-- The face opposite vertex zero is exactly the second path. -/
@[simp] theorem concatSimplex_face_zero (p : Path x y) (q : Path y z) :
    (concatSimplex p q).comp (simplexFace 1 0) = pathSimplex q := by
  apply ContinuousMap.ext
  intro s
  change concatSimplex p q (simplexFace 1 0 s) = pathSimplex q s
  rw [concatSimplex_apply]
  have h1 : simplexFace 1 0 s 1 = s 0 := simplexFace_apply_succAbove 1 0 s 0
  have h2 : simplexFace 1 0 s 2 = s 1 := simplexFace_apply_succAbove 1 0 s 1
  rw [h1, h2]
  have hs := stdSimplex.add_eq_one s
  have hnonneg := stdSimplex.zero_le s 1
  rw [Path.extend_trans_of_half_le p q (show 1 / 2 ≤ s 0 / 2 + s 1 by linarith)]
  have he : 2 * (s 0 / 2 + s 1) - 1 = s 1 := by linarith
  rw [he]
  exact Path.extend_apply q (simplexCoordinate 1 1 s).property

/-- The face opposite vertex one is exactly the concatenated path. -/
@[simp] theorem concatSimplex_face_one (p : Path x y) (q : Path y z) :
    (concatSimplex p q).comp (simplexFace 1 1) = pathSimplex (p.trans q) := by
  apply ContinuousMap.ext
  intro s
  change concatSimplex p q (simplexFace 1 1 s) = pathSimplex (p.trans q) s
  rw [concatSimplex_apply, simplexFace_apply_self]
  have h2 : simplexFace 1 1 s 2 = s 1 := simplexFace_apply_succAbove 1 1 s 1
  rw [h2, zero_div, zero_add]
  exact Path.extend_apply (p.trans q) (simplexCoordinate 1 1 s).property

/-- The face opposite vertex two is exactly the first path. Thus the
alternating boundary is `q - (p.trans q) + p`. -/
@[simp] theorem concatSimplex_face_two (p : Path x y) (q : Path y z) :
    (concatSimplex p q).comp (simplexFace 1 2) = pathSimplex p := by
  apply ContinuousMap.ext
  intro s
  change concatSimplex p q (simplexFace 1 2 s) = pathSimplex p s
  rw [concatSimplex_apply, simplexFace_apply_self]
  have h1 : simplexFace 1 2 s 1 = s 1 := simplexFace_apply_succAbove 1 2 s 1
  rw [h1, add_zero]
  have hle := stdSimplex.le_one s 1
  rw [Path.extend_trans_of_le_half p q (show s 1 / 2 ≤ 1 / 2 by linarith)]
  rw [show 2 * (s 1 / 2) = s 1 by ring]
  exact Path.extend_apply p (simplexCoordinate 1 1 s).property

end Wikipedia.HopfProblem.FirstHurewicz
