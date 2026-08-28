import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# The fixed Euclidean coordinates of the standard six-sphere

These are the first three and last four coordinates of the original
Euclidean seven-space.  Its sphere keeps its subspace topology; no topology
or atlas is transported from another manifold.
-/

noncomputable section

namespace Wikipedia.HopfProblem.StandardSixSphereCircleModel

abbrev Base := EuclideanSpace ℝ (Fin 3)
abbrev Normal := EuclideanSpace ℝ (Fin 4)
abbrev Ambient := EuclideanSpace ℝ (Fin 7)

abbrev Sphere := Metric.sphere (0 : Ambient) 1
abbrev BaseSphere := Metric.sphere (0 : Base) 1
abbrev NormalSphere := Metric.sphere (0 : Normal) 1

/-- The standard ordered splitting, not a change of smooth structure. -/
abbrev split : Ambient ≃L[ℝ] Base × Normal :=
  EuclideanSpace.finAddEquivProd (n := 3) (m := 4)

def base (z : Ambient) : Base := (split z).1
def normal (z : Ambient) : Normal := (split z).2
def join (x : Base) (y : Normal) : Ambient := split.symm (x, y)

@[simp] theorem base_apply (z : Ambient) (i : Fin 3) :
    base z i = z (Fin.castAdd 4 i) := rfl

@[simp] theorem normal_apply (z : Ambient) (i : Fin 4) :
    normal z i = z (Fin.natAdd 3 i) := rfl

@[simp] theorem base_join (x : Base) (y : Normal) : base (join x y) = x := by
  exact congrArg Prod.fst (split.apply_symm_apply (x, y))

@[simp] theorem normal_join (x : Base) (y : Normal) : normal (join x y) = y := by
  exact congrArg Prod.snd (split.apply_symm_apply (x, y))

@[simp] theorem join_base_normal (z : Ambient) : join (base z) (normal z) = z :=
  split.symm_apply_apply z

theorem continuous_base : Continuous base := split.continuous.fst
theorem continuous_normal : Continuous normal := split.continuous.snd

theorem continuous_join : Continuous (fun p : Base × Normal => join p.1 p.2) :=
  split.symm.continuous

@[simp] theorem base_smul (r : ℝ) (z : Ambient) : base (r • z) = r • base z := by
  exact congrArg Prod.fst (split.map_smul r z)

@[simp] theorem normal_smul (r : ℝ) (z : Ambient) : normal (r • z) = r • normal z := by
  exact congrArg Prod.snd (split.map_smul r z)

/-- The norm is the Euclidean norm, not the maximum norm on a product. -/
theorem norm_sq_eq (z : Ambient) :
    ‖z‖ ^ 2 = ‖base z‖ ^ 2 + ‖normal z‖ ^ 2 := by
  simp only [EuclideanSpace.real_norm_sq_eq, base_apply, normal_apply]
  exact Fin.sum_univ_add (fun i : Fin (3 + 4) => (z i) ^ 2)

theorem join_norm_sq (x : Base) (y : Normal) :
    ‖join x y‖ ^ 2 = ‖x‖ ^ 2 + ‖y‖ ^ 2 := by
  rw [norm_sq_eq, base_join, normal_join]

@[simp] theorem sphere_norm (p : Sphere) : ‖p.val‖ = 1 := by
  simpa only [Metric.mem_sphere, dist_zero_right] using p.property

@[simp] theorem baseSphere_norm (p : BaseSphere) : ‖p.val‖ = 1 := by
  simpa only [Metric.mem_sphere, dist_zero_right] using p.property

@[simp] theorem normalSphere_norm (p : NormalSphere) : ‖p.val‖ = 1 := by
  simpa only [Metric.mem_sphere, dist_zero_right] using p.property

theorem sphere_norm_sq (p : Sphere) :
    ‖base p.val‖ ^ 2 + ‖normal p.val‖ ^ 2 = 1 := by
  rw [← norm_sq_eq, sphere_norm, one_pow]

theorem mem_sphere_of_norm_sq (z : Ambient) (hz : ‖z‖ ^ 2 = 1) : z ∈ Sphere := by
  have hn : ‖z‖ = 1 := by nlinarith [norm_nonneg z]
  simpa only [Metric.mem_sphere, dist_zero_right] using hn

end Wikipedia.HopfProblem.StandardSixSphereCircleModel
