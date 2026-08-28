import Wikipedia.SmoothSixDPoincare.DiskDouble
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Explicit hemispherical parametrizations by closed disks

The maps use the usual square-root graph over the Euclidean closed disk.
They agree exactly on the common unit-sphere boundary. These are maps into
the original Euclidean sphere, not a sphere-like replacement space.
-/

noncomputable section

open Set Metric

namespace Wikipedia.SmoothSixDPoincare.Hemisphere

abbrev Ambient (n : ℕ) := EuclideanSpace ℝ (Fin n)
abbrev Ball (n : ℕ) := DiskDouble.Disk (Ambient n)
abbrev Sphere (n : ℕ) := Metric.sphere (0 : Ambient (n + 1)) 1

variable {n : ℕ}

def radius (x : Ball n) : ℝ := Real.sqrt (1 - ‖(x : Ambient n)‖ ^ 2)

theorem radius_sq (x : Ball n) : radius x ^ 2 = 1 - ‖(x : Ambient n)‖ ^ 2 := by
  apply Real.sq_sqrt
  have hx : ‖(x : Ambient n)‖ ≤ 1 := mem_closedBall_zero_iff.mp x.property
  nlinarith [norm_nonneg (x : Ambient n)]

theorem radius_nonneg (x : Ball n) : 0 ≤ radius x := Real.sqrt_nonneg _

def vector (b : Bool) (x : Ball n) : Ambient (n + 1) :=
  WithLp.toLp 2 (Fin.cons (if b then radius x else -radius x) (x : Ambient n))

@[simp] theorem vector_zero (b : Bool) (x : Ball n) :
    vector b x 0 = if b then radius x else -radius x := rfl

@[simp] theorem vector_succ (b : Bool) (x : Ball n) (i : Fin n) :
    vector b x i.succ = (x : Ambient n) i := rfl

theorem vector_norm_sq (b : Bool) (x : Ball n) : ‖vector b x‖ ^ 2 = 1 := by
  rw [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_succ]
  simp only [vector_zero, vector_succ]
  rw [← EuclideanSpace.real_norm_sq_eq]
  cases b <;> simp only [Bool.false_eq_true, ↓reduceIte, neg_sq]
    <;> rw [radius_sq] <;> ring

def point (b : Bool) (x : Ball n) : Sphere n :=
  ⟨vector b x, by
    rw [mem_sphere_zero_iff_norm]
    have h := vector_norm_sq b x
    nlinarith [norm_nonneg (vector b x)]⟩

@[simp] theorem point_zero (b : Bool) (x : Ball n) :
    (point b x : Ambient (n + 1)) 0 = if b then radius x else -radius x := rfl

@[simp] theorem point_succ (b : Bool) (x : Ball n) (i : Fin n) :
    (point b x : Ambient (n + 1)) i.succ = (x : Ambient n) i := rfl

theorem continuous_radius : Continuous (radius (n := n)) := by
  unfold radius
  fun_prop

theorem continuous_vector (b : Bool) : Continuous (vector (n := n) b) := by
  apply (PiLp.continuous_toLp 2 (fun _ : Fin (n + 1) => ℝ)).comp
  apply continuous_pi
  intro i
  refine Fin.cases ?_ (fun j => ?_) i
  · cases b
    · exact continuous_radius.neg
    · exact continuous_radius
  · exact (PiLp.continuous_apply 2 (fun _ : Fin n => ℝ) j).comp continuous_subtype_val

theorem continuous_point (b : Bool) : Continuous (point (n := n) b) :=
  (continuous_vector b).subtype_mk _

theorem point_injective (b : Bool) : Function.Injective (point (n := n) b) := by
  intro x y h
  apply Subtype.ext
  ext i
  exact congrArg (fun z : Sphere n => (z : Ambient (n + 1)) i.succ) h

@[simp] theorem radius_boundary (x : DiskDouble.Boundary (Ambient n)) :
    radius (DiskDouble.boundary (Ambient n) x) = 0 := by
  have hx : ‖(x : Ambient n)‖ = 1 := mem_sphere_zero_iff_norm.mp x.property
  simp [radius, DiskDouble.boundary, hx]

theorem point_boundary (x : DiskDouble.Boundary (Ambient n)) :
    point false (DiskDouble.boundary (Ambient n) x) =
      point true (DiskDouble.boundary (Ambient n) x) := by
  apply Subtype.ext
  ext i
  refine Fin.cases ?_ (fun j => ?_) i
  · simp
  · rfl

/-- Points from opposite hemispheres coincide only at corresponding boundary points. -/
theorem point_false_eq_true_iff (x y : Ball n) :
    point false x = point true y ↔
      ∃ z : DiskDouble.Boundary (Ambient n),
        x = DiskDouble.boundary (Ambient n) z ∧ y = DiskDouble.boundary (Ambient n) z := by
  constructor
  · intro h
    have hxy : x = y := by
      apply Subtype.ext
      ext i
      exact congrArg (fun z : Sphere n => (z : Ambient (n + 1)) i.succ) h
    subst y
    have hr : radius x = 0 := by
      have hh := congrArg (fun z : Sphere n => (z : Ambient (n + 1)) 0) h
      simp only [point_zero, Bool.false_eq_true, ↓reduceIte] at hh
      linarith
    have hn : ‖(x : Ambient n)‖ = 1 := by
      have hs := radius_sq x
      rw [hr] at hs
      nlinarith [norm_nonneg (x : Ambient n)]
    exact ⟨⟨x, mem_sphere_zero_iff_norm.mpr hn⟩, rfl, rfl⟩
  · rintro ⟨z, rfl, rfl⟩
    exact point_boundary z

end Wikipedia.SmoothSixDPoincare.Hemisphere
