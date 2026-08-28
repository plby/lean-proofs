import Wikipedia.HopfProblem.ToricCharts
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Algebra.Order.Archimedean.Real.Basic

/-!
# The integral triangles used at the cusp

The two triangles over each integral square give the fan in §4.2 of
`tex/s6.tex`. Their height-one rays and dual integral bases are explicit.
The resulting monomial coordinate changes are genuine holomorphic partial
homeomorphisms and preserve the local normal-crossings function `z₀z₁z₂`.
-/

noncomputable section

open Set Topology
open scoped ContDiff Matrix

namespace Wikipedia.HopfProblem.ToricFan

open ToricCharts

/-- The lower or upper triangle in the square with lower-left corner `(a,b)`. -/
@[ext] structure Triangle where
  a : ℤ
  b : ℤ
  upper : Bool
  deriving DecidableEq

instance : Countable Triangle := by
  apply Function.Injective.countable (f := fun s : Triangle => (s.a, s.b, s.upper))
  intro s t h
  simpa only [Prod.mk.injEq, Triangle.ext_iff, and_assoc] using h

namespace Triangle

/-- Columns are the three primitive height-one rays. -/
def rays (s : Triangle) : Matrix (Fin 3) (Fin 3) ℤ :=
  if s.upper then
    !![s.a + 1, s.a, s.a + 1; s.b, s.b + 1, s.b + 1; 1, 1, 1]
  else
    !![s.a, s.a + 1, s.a; s.b, s.b, s.b + 1; 1, 1, 1]

/-- Rows are the integral characters dual to the primitive rays. -/
def dual (s : Triangle) : Matrix (Fin 3) (Fin 3) ℤ :=
  if s.upper then
    !![0, -1, s.b + 1; -1, 0, s.a + 1; 1, 1, -1 - s.a - s.b]
  else
    !![-1, -1, 1 + s.a + s.b; 1, 0, -s.a; 0, 1, -s.b]

theorem dual_rays (s : Triangle) : s.dual * s.rays = 1 := by
  ext i j
  cases h : s.upper <;> fin_cases i <;> fin_cases j <;>
    simp [dual, rays, h, Matrix.mul_apply, Fin.sum_univ_succ] <;> ring

theorem rays_dual (s : Triangle) : s.rays * s.dual = 1 := by
  ext i j
  cases h : s.upper <;> fin_cases i <;> fin_cases j <;>
    simp [dual, rays, h, Matrix.mul_apply, Fin.sum_univ_succ] <;> ring

theorem rays_det (s : Triangle) : s.rays.det = if s.upper then -1 else 1 := by
  cases h : s.upper <;> simp [rays, h, Matrix.det_fin_three] <;> ring

theorem rays_unimodular (s : Triangle) : IsUnit s.rays.det := by
  rw [rays_det]
  cases s.upper <;> norm_num

@[simp] theorem rays_height (s : Triangle) (j : Fin 3) : s.rays 2 j = 1 := by
  cases h : s.upper <;> fin_cases j <;> simp [rays, h]

/-- Exponent matrix for changing from the `s`-chart to the `t`-chart. -/
def transition (s t : Triangle) : Matrix (Fin 3) (Fin 3) ℤ := t.dual * s.rays

@[simp] theorem transition_self (s : Triangle) : transition s s = 1 := s.dual_rays

theorem transition_mul (r s t : Triangle) :
    transition s t * transition r s = transition r t := by
  unfold transition
  rw [Matrix.mul_assoc, ← Matrix.mul_assoc s.rays, rays_dual, Matrix.one_mul]

theorem transition_covariance (s t : Triangle) :
    t.rays * transition s t = s.rays := by
  rw [transition, ← Matrix.mul_assoc, rays_dual, Matrix.one_mul]

theorem transition_heightOne (s t : Triangle) : HeightOne (transition s t) := by
  intro j
  have h := congrFun (congrFun (transition_covariance s t) 2) j
  simpa [Matrix.mul_apply] using h

/-- The analytic chart change, with its exact open source and target. -/
def chartChange (s t : Triangle) : OpenPartialHomeomorph (CoordinateSpace 3)
    (CoordinateSpace 3) :=
  changeOfCoordinates (transition s t) (transition t s)
    (by rw [transition_mul, transition_self])
    (by rw [transition_mul, transition_self])

@[simp] theorem chartChange_source (s t : Triangle) :
    (chartChange s t).source = domain (transition s t) :=
  overlap_eq_domain (transition_heightOne s t)
    (by rw [transition_mul, transition_self])

@[simp] theorem chartChange_target (s t : Triangle) :
    (chartChange s t).target = domain (transition t s) :=
  overlap_eq_domain (transition_heightOne t s)
    (by rw [transition_mul, transition_self])

@[simp] theorem chartChange_self_source (s : Triangle) :
    (chartChange s s).source = univ := by
  rw [chartChange_source, transition_self]
  ext z
  simp only [domain, mem_ofPred_eq, mem_univ, iff_true]
  intro i j h
  simp only [Matrix.one_apply] at h
  split_ifs at h <;> omega

@[simp] theorem chartChange_self_apply (s : Triangle) (z : CoordinateSpace 3) :
    chartChange s s z = z := by
  change monomial (transition s s) z = z
  rw [transition_self, monomial_one]

theorem chartChange_cocycle (r s t : Triangle) {z : CoordinateSpace 3}
    (hz : z ∈ (chartChange r s).source)
    (hsz : chartChange r s z ∈ (chartChange s t).source) :
    z ∈ (chartChange r t).source ∧
      chartChange s t (chartChange r s z) = chartChange r t z := by
  rw [chartChange_source] at hz hsz ⊢
  have hm : z ∈ overlap (transition r s) (transition s t) := ⟨hz, hsz⟩
  constructor
  · simpa only [transition_mul] using domain_composition (transition_heightOne r s) hm
  · change monomial (transition s t) (monomial (transition r s) z) =
      monomial (transition r t) z
    simpa only [Function.comp_apply, transition_mul] using
      monomial_mul_on_overlap (transition_heightOne r s) hm

theorem chartChange_inter (r s t : Triangle) {z : CoordinateSpace 3}
    (hs : z ∈ (chartChange r s).source) (ht : z ∈ (chartChange r t).source) :
    chartChange r s z ∈ (chartChange s t).source := by
  have hi : chartChange r s z ∈ (chartChange s r).source :=
    (chartChange r s).map_source hs
  have hinv : chartChange s r (chartChange r s z) = z :=
    (chartChange r s).left_inv hs
  exact (chartChange_cocycle s r t hi (by rwa [hinv])).1

theorem chartChange_holomorphic (s t : Triangle) :
    ContDiffOn ℂ ω (chartChange s t) (chartChange s t).source :=
  changeOfCoordinates_holomorphic _ _ _ _

theorem chartChange_symm_holomorphic (s t : Triangle) :
    ContDiffOn ℂ ω (chartChange s t).symm (chartChange s t).target :=
  changeOfCoordinates_symm_holomorphic _ _ _ _

/-- Local defining function of the reduced central normal-crossings fibre. -/
def time (z : CoordinateSpace 3) : ℂ := z 0 * z 1 * z 2

theorem time_holomorphic : ContDiff ℂ ω time := by
  exact ((contDiff_apply ℂ ℂ 0).mul (contDiff_apply ℂ ℂ 1)).mul
    (contDiff_apply ℂ ℂ 2)

theorem monomial_rays_height (s : Triangle) (z : CoordinateSpace 3) :
    monomial s.rays z 2 = time z := by
  simp [monomial, rays_height, Fin.prod_univ_succ, time, mul_assoc]

theorem chartChange_preserves_time (s t : Triangle) :
    EqOn (time ∘ chartChange s t) time (chartChange s t).source := by
  have h : EqOn (time ∘ chartChange s t) time ((chartChange s t).source ∩ torus) := by
    intro z hz
    change time (monomial (transition s t) z) = time z
    have he := congrFun (monomial_mul_on_torus t.rays (transition s t) hz.2) 2
    simpa only [transition_covariance, monomial_rays_height] using he
  refine h.of_subset_closure ?_ time_holomorphic.continuous.continuousOn
    inter_subset_left (torus_dense.open_subset_closure_inter (chartChange s t).open_source)
  exact time_holomorphic.continuous.comp_continuousOn (chartChange s t).continuousOn

theorem central_fibre (z : CoordinateSpace 3) :
    time z = 0 ↔ z 0 = 0 ∨ z 1 = 0 ∨ z 2 = 0 := by
  simp [time, mul_eq_zero, or_assoc]

end Triangle

end Wikipedia.HopfProblem.ToricFan
