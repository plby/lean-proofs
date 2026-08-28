import Wikipedia.NoExoticSixSphere.SphereNormalization
import Wikipedia.NoExoticSixSphere.OpenSubsetSmoothMaps

/-!
# Smooth radial retraction near the unit sphere

The total function uses a specified fallback at zero, but every smoothness
statement is restricted to nonzero vectors. It fixes the actual unit sphere
pointwise and allows smooth sphere maps to be extended to an ambient open
neighborhood.
-/

open scoped Manifold ContDiff
open Set TopologicalSpace

namespace NoExoticSixSphere.SphereRadialRetraction

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

noncomputable def retract (a : UnitSphere E) (x : E) : UnitSphere E := by
  classical
  exact if h : x = 0 then a else
    ⟨NormedSpace.normalize x, by
      simpa only [Metric.mem_sphere, dist_zero_right] using NormedSpace.norm_normalize h⟩

theorem retract_coe (a x : UnitSphere E) : retract a (x : E) = x := by
  have hx : (x : E) ≠ 0 := ne_zero_of_mem_unit_sphere x
  apply Subtype.ext
  simp only [retract, dif_neg hx]
  exact NormedSpace.normalize_eq_self_of_norm_eq_one (ClosedHemisphere.unit_norm x)

variable {n : ℕ} [Fact (Module.finrank ℝ E = n + 1)]

theorem contMDiffOn_retract (a : UnitSphere E) :
    ContMDiffOn 𝓘(ℝ, E) (𝓡 n) ∞ (retract a) {x | x ≠ 0} := by
  let U : Opens E := ⟨{x | x ≠ 0}, isOpen_ne⟩
  apply (contMDiffOn_iff_openSubset (I := 𝓘(ℝ, E)) (J := 𝓡 n) U (retract a)).mpr
  have hN := contMDiff_normalize (I := 𝓘(ℝ, E))
    (g := fun x : U ↦ x.val) contMDiff_subtype_val (fun x ↦ x.property)
  have hmem : ∀ x : U, NormedSpace.normalize x.val ∈ UnitSphere E := by
    intro x
    simpa only [Metric.mem_sphere, dist_zero_right] using NormedSpace.norm_normalize x.property
  have hs := hN.codRestrict_sphere (n := n) hmem
  have he : (fun x : U ↦ retract a x.val) = Set.codRestrict
      (fun x : U ↦ NormedSpace.normalize x.val) (UnitSphere E) hmem := by
    funext x
    apply Subtype.ext
    change (retract a x.val).val = NormedSpace.normalize x.val
    simp only [retract, dif_neg x.property]
  rw [he]
  exact hs

theorem contMDiffAt_retract (a : UnitSphere E) {x : E} (hx : x ≠ 0) :
    ContMDiffAt 𝓘(ℝ, E) (𝓡 n) ∞ (retract a) x :=
  (contMDiffOn_retract (n := n) a).contMDiffAt
    (isOpen_ne.mem_nhds hx)

end NoExoticSixSphere.SphereRadialRetraction
