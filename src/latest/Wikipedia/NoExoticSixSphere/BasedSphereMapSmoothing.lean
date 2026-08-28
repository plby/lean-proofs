import Wikipedia.NoExoticSixSphere.SphereLocalFlattening
import Wikipedia.NoExoticSixSphere.GLOrthonormalization
import Wikipedia.SmoothSixDPoincare.GlobalMapSmoothing

/-!
# Smooth representatives preserving the value at a sphere basepoint

First compose with the constructed local sphere collapse. The composite
is constant near the basepoint even when the original map was only
continuous. Relative manifold smoothing then fixes that point exactly.
Both actual homotopies are retained and composed.
-/

noncomputable section

open Set Function
open scoped Manifold ContDiff

namespace NoExoticSixSphere

open GLOrthonormalization

variable {M : Type*} [TopologicalSpace M] [ChartedSpace (Vector 6) M]
  [IsManifold (𝓡 6) ∞ M]

theorem exists_smooth_based_sphereMap (b : Sphere 3) (f : C(Sphere 3, M)) :
    ∃ F : C(Sphere 3, M), ContMDiff (𝓡 3) (𝓡 6) ∞ F ∧ f.HomotopicRel F {b} := by
  let : Fact (Module.finrank ℝ (Vector 4) = 3 + 1) := ⟨by simp [GLOrthonormalization.Vector]⟩
  obtain ⟨R, _, ⟨H⟩, _, _, W, hW, hbW, hRW⟩ :=
    SphereCap.exists_smooth_localFlattening (n := 3) b isOpen_univ (mem_univ b)
  have HR : (ContinuousMap.id (Sphere 3)).HomotopicRel R {b} :=
    ⟨{ toHomotopy := H.toHomotopy
       prop' := fun t x hx ↦ H.eq_fst t (Or.inr hx) }⟩
  have Hf : f.HomotopicRel (f.comp R) {b} := HR.comp_continuousMap f
  have hfW : EqOn (f.comp R) (fun _ ↦ f b) W := fun x hx ↦ congrArg f (hRW hx)
  have hsW : ContMDiffOn (𝓡 3) (𝓡 6) ∞ (f.comp R) W :=
    contMDiffOn_const.congr hfW
  have hsub : ({b} : Set (Sphere 3)) ⊆ W := by
    rintro x rfl
    exact hbW
  obtain ⟨F, hF, HF⟩ :=
    Wikipedia.SmoothSixDPoincare.ManifoldSmoothing.exists_smooth_map_homotopicRel
      (I := 𝓡 3) (J := 𝓡 6) (f.comp R) isClosed_singleton hW hsub hsW
  exact ⟨F, hF, Hf.trans HF⟩

theorem exists_smooth_flat_based_sphereMap (b : Sphere 3) (f : C(Sphere 3, M)) :
    ∃ F : C(Sphere 3, M), ContMDiff (𝓡 3) (𝓡 6) ∞ F ∧ f.HomotopicRel F {b} ∧
      ∃ U : Set (Sphere 3), IsOpen U ∧ b ∈ U ∧ EqOn F (fun _ ↦ f b) U := by
  obtain ⟨G, hG, HG⟩ := exists_smooth_based_sphereMap b f
  let : Fact (Module.finrank ℝ (Vector 4) = 3 + 1) := ⟨by simp [GLOrthonormalization.Vector]⟩
  obtain ⟨R, hR, ⟨H⟩, _, _, W, hW, hbW, hRW⟩ :=
    SphereCap.exists_smooth_localFlattening (n := 3) b isOpen_univ (mem_univ b)
  have HR : (ContinuousMap.id (Sphere 3)).HomotopicRel R {b} :=
    ⟨{ toHomotopy := H.toHomotopy
       prop' := fun t x hx ↦ H.eq_fst t (Or.inr hx) }⟩
  have HGR : G.HomotopicRel (G.comp R) {b} := HR.comp_continuousMap G
  refine ⟨G.comp R, hG.comp hR, HG.trans HGR, W, hW, hbW, ?_⟩
  intro x hx
  exact (congrArg G (hRW hx)).trans (HG.fst_eq_snd (mem_singleton b)).symm

end NoExoticSixSphere
