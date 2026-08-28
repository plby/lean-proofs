import Wikipedia.NoExoticSixSphere.Definitions
import Mathlib.Topology.TietzeExtension

/-!
# The finite unit cube is a retract of the sphere of the same dimension

Embed the cube into a stereographic chart. Its image is closed by compactness.
Tietze extension of the coordinate functions, followed by interval projection,
gives a continuous left inverse. This lets cube-parameter families be extended
to a compact boundaryless parameter manifold without changing their restriction.
-/

open Set

namespace NoExoticSixSphere.CubeSphereRetract

noncomputable def coordinates (d : ℕ) : C((Fin d → unitInterval), EuclideanSpace ℝ (Fin d)) where
  toFun x := WithLp.toLp 2 (fun i ↦ (x i : ℝ))
  continuous_toFun := (PiLp.continuous_toLp 2 (fun _ : Fin d ↦ ℝ)).comp
    (continuous_pi (fun i ↦ continuous_subtype_val.comp (continuous_apply i)))

theorem coordinates_injective (d : ℕ) : Function.Injective (coordinates d) := by
  intro x y h
  funext i
  apply Subtype.ext
  exact congrArg (fun z : EuclideanSpace ℝ (Fin d) ↦ z i) h

theorem exists_closed_embedding (d : ℕ) :
    ∃ e : C((Fin d → unitInterval), Sphere d), Topology.IsClosedEmbedding e := by
  let : Nonempty (Sphere d) := NormedSpace.sphere_nonempty_rclike ℝ zero_le_one
  let : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin (d + 1))) = d + 1) :=
    ⟨finrank_euclideanSpace_fin⟩
  let v : Sphere d := Classical.choice inferInstance
  let c := stereographic' d v
  have hc : Topology.IsOpenEmbedding c.symm := c.symm.isOpenEmbedding (stereographic'_target v)
  let e : C((Fin d → unitInterval), Sphere d) :=
    ⟨fun x ↦ c.symm (coordinates d x), hc.continuous.comp (coordinates d).continuous⟩
  exact ⟨e, e.continuous.isClosedEmbedding (hc.injective.comp (coordinates_injective d))⟩

theorem exists_retract (d : ℕ) :
    ∃ e : C((Fin d → unitInterval), Sphere d),
      ∃ r : C(Sphere d, (Fin d → unitInterval)), r.comp e = ContinuousMap.id _ := by
  obtain ⟨e, he⟩ := exists_closed_embedding d
  let f : C((Fin d → unitInterval), (Fin d → ℝ)) :=
    ⟨fun x i ↦ (x i : ℝ),
      continuous_pi (fun i ↦ continuous_subtype_val.comp (continuous_apply i))⟩
  obtain ⟨R, hR⟩ := f.exists_extension' he
  let r : C(Sphere d, (Fin d → unitInterval)) := {
    toFun z i := projIcc 0 1 zero_le_one (R z i)
    continuous_toFun := continuous_pi (fun i ↦
      continuous_projIcc.comp ((continuous_apply i).comp R.continuous)) }
  refine ⟨e, r, ?_⟩
  apply ContinuousMap.ext
  intro x
  funext i
  change projIcc 0 1 zero_le_one (R (e x) i) = x i
  have h := congrFun (congrFun hR x) i
  change R (e x) i = (x i : ℝ) at h
  rw [h, projIcc_val]

end NoExoticSixSphere.CubeSphereRetract
