import Wikipedia.NoExoticSixSphere.SphereNormalization
import Mathlib.Analysis.InnerProductSpace.Projection.Submodule

/-!
# The unit normal of an immersed cooriented hypersurface

The hypersurface tangent image is the image of the kernel of an actual
defining differential. Project an actual transverse tangent vector onto its
orthogonal complement. The projection is nonzero for an injective immersion,
remains tangent to the ambient manifold, and its normalized direction depends
only on the sign of the defining differential.
-/

noncomputable section

open Function Set
open scoped Manifold ContDiff

namespace NoExoticSixSphere.CoorientedHypersurfaceNormal

variable {V E : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  (D : V →L[ℝ] E) (l : V →L[ℝ] ℝ)

def tangent : Submodule ℝ E := l.ker.map D.toLinearMap

def projected (u : V) : E := (tangent D l)ᗮ.starProjection (D u)

def unitNormal (u : V) : E := NormedSpace.normalize (projected D l u)

theorem projected_eq_zero_iff (hD : Injective D) (u : V) :
    projected D l u = 0 ↔ l u = 0 := by
  change D u ∈ (tangent D l)ᗮ.starProjection.ker ↔ _
  rw [Submodule.ker_starProjection, Submodule.orthogonal_orthogonal]
  constructor
  · rintro ⟨v, hv, he⟩
    have hvu : v = u := hD he
    exact hvu ▸ hv
  · intro hu
    exact ⟨u, hu, rfl⟩

theorem projected_mem_range (u : V) : projected D l u ∈ D.range := by
  rw [projected, Submodule.starProjection_orthogonal_val]
  obtain ⟨v, _, hv⟩ := (tangent D l).starProjection_apply_mem (D u)
  refine ⟨u - v, ?_⟩
  rw [map_sub, hv]
  rfl

theorem projected_mem_orthogonal (u : V) : projected D l u ∈ (tangent D l)ᗮ :=
  (tangent D l)ᗮ.starProjection_apply_mem (D u)

theorem projected_eq_smul (u v : V) (hv : l v ≠ 0) :
    projected D l u = (l u / l v) • projected D l v := by
  have hk : D (u - (l u / l v) • v) ∈ tangent D l := by
    refine ⟨u - (l u / l v) • v, ?_, rfl⟩
    change l (u - (l u / l v) • v) = 0
    rw [map_sub, map_smul]
    change l u - (l u / l v) * l v = 0
    field_simp
    ring
  have hp := Submodule.starProjection_orthogonal_apply_eq_zero hk
  rw [map_sub, map_smul, map_sub, map_smul] at hp
  exact sub_eq_zero.mp hp

theorem unitNormal_eq_of_negative (u v : V) (hu : l u < 0) (hv : l v < 0) :
    unitNormal D l u = unitNormal D l v := by
  rw [unitNormal, projected_eq_smul D l u v hv.ne,
    NormedSpace.normalize_smul_of_pos (div_pos_of_neg_of_neg hu hv)]
  rfl

theorem unitNormal_eq_of_positive (u v : V) (hu : 0 < l u) (hv : 0 < l v) :
    unitNormal D l u = unitNormal D l v := by
  rw [unitNormal, projected_eq_smul D l u v hv.ne',
    NormedSpace.normalize_smul_of_pos (div_pos hu hv)]
  rfl

theorem norm_unitNormal (hD : Injective D) (u : V) (hu : l u ≠ 0) :
    ‖unitNormal D l u‖ = 1 :=
  NormedSpace.norm_normalize (fun hz ↦ hu ((projected_eq_zero_iff D l hD u).mp hz))

theorem unitNormal_mem_range (u : V) : unitNormal D l u ∈ D.range :=
  D.range.smul_mem _ (projected_mem_range D l u)

theorem unitNormal_mem_orthogonal (u : V) : unitNormal D l u ∈ (tangent D l)ᗮ :=
  (tangent D l)ᗮ.smul_mem _ (projected_mem_orthogonal D l u)

theorem unitNormal_neg (u : V) : unitNormal D l (-u) = -unitNormal D l u := by
  simp only [unitNormal, projected, map_neg, NormedSpace.normalize_neg]

end NoExoticSixSphere.CoorientedHypersurfaceNormal
