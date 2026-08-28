import Wikipedia.NoExoticSixSphere.PartialFrameTailVectors
import Wikipedia.NoExoticSixSphere.PartialFrameTransition
import Wikipedia.NoExoticSixSphere.PartialFrameOneColumn
import Wikipedia.NoExoticSixSphere.EquatorOrthogonalSphere
import Wikipedia.NoExoticSixSphere.SphereReflectionHomology

/-!
# The original equatorial factor is the actual reflection family

Evaluate the remaining one-column frame and reconstruct its actual complement
vector. The proved chart-transition identity is then literally reflection
on the orthogonal-complement sphere. Neither the source nor target is replaced
by a sphere with an assigned degree.
-/

noncomputable section

namespace NoExoticSixSphere.Stiefel.ColumnBundle

open GLOrthonormalization ColumnCoordinates Set
open NoExoticSixSphere.Stiefel.ColumnFiber

variable {n : ℕ}

local instance complementDimension :
    Fact (Module.finrank ℝ (Vector (n + 1)) = n + 1) := ⟨finrank_euclideanSpace_fin⟩

variable (c : UnitSphere (Vector (n + 1)))

theorem equator_mem_baseSets (x : Equator c) : x.val ∈ baseSet c ∩ baseSet (antipode c) := by
  have hcc : inner ℝ c.val c.val = 1 := by
    rw [real_inner_self_eq_norm_sq, ClosedHemisphere.unit_norm, one_pow]
  have hx : inner ℝ c.val x.val.val = 0 := x.property
  constructor
  · intro h
    have he : x.val.val = -c.val := congrArg Subtype.val h
    rw [he, inner_neg_right, hcc] at hx
    norm_num at hx
  · intro h
    have he : x.val.val = c.val := (congrArg Subtype.val h).trans (neg_neg _)
    rw [he, hcc] at hx
    norm_num at hx

def frameSphereHomeomorph (u : UnitSphere (Vector 1)) :
    Space n 1 ≃ₜ UnitSphere ((ℝ ∙ c.val)ᗮ) :=
  (OneColumn.homeomorph u).trans (unitSphereCongr (complement c).symm)

theorem frameSphereHomeomorph_val (u : UnitSphere (Vector 1)) (q : Space n 1) :
    ((frameSphereHomeomorph c u q).val : Vector (n + 1)) = tailVector c (q.val u.val) := rfl

def fixedVector (q : Space n 1) (u : UnitSphere (Vector 1)) : UnitSphere ((ℝ ∙ c.val)ᗮ) :=
  ⟨⟨tailVector (antipode c) (q.val u.val), by
    apply Submodule.mem_orthogonal_singleton_iff_inner_right.mpr
    have h := tailVector_inner (antipode c) (q.val u.val)
    change inner ℝ (-c.val) (tailVector (antipode c) (q.val u.val)) = 0 at h
    rw [inner_neg_left] at h
    exact neg_eq_zero.mp h⟩, by
    rw [Metric.mem_sphere, dist_zero_right]
    change ‖tailVector (antipode c) (q.val u.val)‖ = 1
    rw [tailVector_norm, q.property, ClosedHemisphere.unit_norm]⟩

def equatorialFactor (v : UnitSphere (Vector 2)) (q : Space n 1) : C(Equator c, Space n 1) :=
  ⟨fun x ↦ transition v c (antipode c) x.val q,
    continuous_transition v c (antipode c) (fun x : Equator c ↦ (x.val, q))
      (continuous_subtype_val.prodMk continuous_const) (equator_mem_baseSets c)⟩

theorem equatorialFactor_reflection (v : UnitSphere (Vector 2)) (q : Space n 1)
    (u : UnitSphere (Vector 1)) (x : Equator c) :
    frameSphereHomeomorph c u (equatorialFactor c v q x) =
      SphereReflection.positive (fixedVector c q u) (equatorOrthogonalHomeomorph c x) := by
  apply Subtype.ext
  apply Subtype.ext
  rw [SphereReflection.positive_apply]
  change tailVector c ((transition v c (antipode c) x.val q).val u.val) =
    tailVector (antipode c) (q.val u.val) -
      (2 * inner ℝ x.val.val (tailVector (antipode c) (q.val u.val))) • x.val.val
  have h := equatorial_reconstruct_transition v c x.val x.property q (tailVector v u.val)
    (tailVector_inner v u.val)
  rw [reconstruct_tailVector, reconstruct_tailVector] at h
  exact h

theorem equatorialFactor_conjugacy (v : UnitSphere (Vector 2)) (q : Space n 1)
    (u : UnitSphere (Vector 1)) :
    equatorialFactor c v q = ((frameSphereHomeomorph c u).symm :
      C(UnitSphere ((ℝ ∙ c.val)ᗮ), Space n 1)).comp
        ((SphereReflection.positive (fixedVector c q u)).comp
          (equatorOrthogonalHomeomorph c : C(Equator c, UnitSphere ((ℝ ∙ c.val)ᗮ)))) := by
  apply ContinuousMap.ext
  intro x
  apply (frameSphereHomeomorph c u).injective
  change frameSphereHomeomorph c u (equatorialFactor c v q x) =
    frameSphereHomeomorph c u ((frameSphereHomeomorph c u).symm
      (SphereReflection.positive (fixedVector c q u) (equatorOrthogonalHomeomorph c x)))
  rw [Homeomorph.apply_symm_apply]
  exact equatorialFactor_reflection c v q u x

end NoExoticSixSphere.Stiefel.ColumnBundle
