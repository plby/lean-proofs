import Wikipedia.HopfProblem.SphereHomologyBasic
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Literal latitude coordinates for the next Euclidean sphere

The suspension height is sent to the first real coordinate. Its remaining
coordinates are the original unit vector multiplied by the nonnegative
latitude radius. The two end slices, and only those slices, collapse.
-/

noncomputable section

open Set
open scoped unitInterval

namespace Wikipedia.HopfProblem.SphereHomology.Latitude

def height (t : unitInterval) : ℝ := 2 * (t : ℝ) - 1

def radius (t : unitInterval) : ℝ := Real.sqrt (1 - height t ^ 2)

theorem height_sq_le_one (t : unitInterval) : height t ^ 2 ≤ 1 := by
  have h0 := t.property.1
  have h1 := t.property.2
  dsimp [height]
  nlinarith

theorem radius_sq (t : unitInterval) : radius t ^ 2 = 1 - height t ^ 2 :=
  Real.sq_sqrt (sub_nonneg.mpr (height_sq_le_one t))

theorem radius_nonneg (t : unitInterval) : 0 ≤ radius t := Real.sqrt_nonneg _

@[simp] theorem height_zero : height 0 = -1 := by norm_num [height]
@[simp] theorem height_one : height 1 = 1 := by norm_num [height]
@[simp] theorem radius_zero : radius 0 = 0 := by simp [radius]
@[simp] theorem radius_one : radius 1 = 0 := by simp [radius]

theorem height_injective : Function.Injective height := by
  intro t s h
  apply Subtype.ext
  dsimp [height] at h
  linarith

theorem radius_pos_of_interior (t : unitInterval) (h0 : t ≠ 0) (h1 : t ≠ 1) :
    0 < radius t := by
  have ht0 : 0 < (t : ℝ) := lt_of_le_of_ne t.property.1 (by
    intro h
    exact h0 (Subtype.ext h.symm))
  have ht1 : (t : ℝ) < 1 := lt_of_le_of_ne t.property.2 (by
    intro h
    exact h1 (Subtype.ext h))
  apply Real.sqrt_pos.mpr
  dsimp [height]
  nlinarith

@[continuity, fun_prop] theorem height_continuous : Continuous height := by
  unfold height
  fun_prop

@[continuity, fun_prop] theorem radius_continuous : Continuous radius := by
  unfold radius
  exact Real.continuous_sqrt.comp (continuous_const.sub (height_continuous.pow 2))

/-- The actual vector on the next sphere, before bundling its norm proof. -/
def vector (n : ℕ) (t : unitInterval) (x : UnitSphere n) :
    EuclideanSpace ℝ (Fin (n + 2)) :=
  WithLp.toLp 2 (Fin.cons (height t) (fun i => radius t * x.val i))

@[simp] theorem vector_zero (n : ℕ) (t : unitInterval) (x : UnitSphere n) :
    vector n t x 0 = height t := rfl

@[simp] theorem vector_succ (n : ℕ) (t : unitInterval) (x : UnitSphere n)
    (i : Fin (n + 1)) : vector n t x i.succ = radius t * x.val i := rfl

theorem vector_norm_sq (n : ℕ) (t : unitInterval) (x : UnitSphere n) :
    ‖vector n t x‖ ^ 2 = 1 := by
  rw [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_succ]
  simp only [vector_zero, vector_succ, mul_pow]
  rw [← Finset.mul_sum, ← EuclideanSpace.real_norm_sq_eq, unitSphere_norm]
  rw [one_pow, mul_one, radius_sq]
  ring

theorem vector_mem_sphere (n : ℕ) (t : unitInterval) (x : UnitSphere n) :
    vector n t x ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 2))) 1 := by
  have hn := vector_norm_sq n t x
  have hnorm : ‖vector n t x‖ = 1 := by nlinarith [norm_nonneg (vector n t x)]
  simpa only [Metric.mem_sphere, dist_zero_right] using hnorm

def point (n : ℕ) (t : unitInterval) (x : UnitSphere n) : UnitSphere (n + 1) :=
  ⟨vector n t x, vector_mem_sphere n t x⟩

@[continuity, fun_prop] theorem vector_continuous (n : ℕ) :
    Continuous (fun p : unitInterval × UnitSphere n => vector n p.1 p.2) := by
  apply (PiLp.continuous_toLp 2 (fun _ : Fin (n + 2) => ℝ)).comp
  apply continuous_pi
  intro i
  refine Fin.cases ?_ (fun j => ?_) i
  · exact height_continuous.comp continuous_fst
  · exact (radius_continuous.comp continuous_fst).mul
      ((PiLp.continuous_apply 2 (fun _ : Fin (n + 1) => ℝ) j).comp
        (continuous_subtype_val.comp continuous_snd))

@[continuity, fun_prop] theorem point_continuous (n : ℕ) :
    Continuous (fun p : unitInterval × UnitSphere n => point n p.1 p.2) :=
  (vector_continuous n).subtype_mk _

end Wikipedia.HopfProblem.SphereHomology.Latitude
