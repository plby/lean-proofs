import Wikipedia.NoExoticSixSphere.SphereFamilyPairCoordinates
import Wikipedia.NoExoticSixSphere.ManifoldChartDerivative

/-!
# Smooth coordinates for an actual sphere family at arbitrary times

These domains do not discard the endpoint times. They record exactly source
chart validity and target chart validity for the given smooth family.
-/

noncomputable section

open Set Function TopologicalSpace
open scoped Manifold ContDiff

namespace NoExoticSixSphere.SphereFamily

open GLOrthonormalization ManifoldAffineSphereFamily

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (Vector n) M]
  (g : ℝ → Sphere 3 → M)
  (hg : ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 3)) (𝓡 n) ∞ (uncurry g))
  (s : SourceChart) (c : TargetChart n M)

def coordinateSource : Opens (ℝ × Vector 3) :=
  ⟨{q | q.2 ∈ s.target}, s.open_target.preimage continuous_snd⟩

include hg

theorem contMDiffOn_inChart :
    ContMDiffOn 𝓘(ℝ, ℝ × Vector 3) (𝓡 n) ∞
      (fun q : ℝ × Vector 3 ↦ g q.1 (s.symm q.2)) (coordinateSource s) := by
  have ht : ContMDiffOn 𝓘(ℝ, ℝ × Vector 3) 𝓘(ℝ, ℝ) ∞
      (fun q : ℝ × Vector 3 ↦ q.1) (coordinateSource s) :=
    contDiff_fst.contMDiff.contMDiffOn
  have hs : ContMDiffOn 𝓘(ℝ, ℝ × Vector 3) (𝓡 3) ∞
      (fun q : ℝ × Vector 3 ↦ s.symm q.2) (coordinateSource s) :=
    s.contMDiffOn_invFun.comp contDiff_snd.contMDiff.contMDiffOn (fun _ hq ↦ hq)
  exact hg.comp_contMDiffOn (ht.prodMk hs)

def coordinateRegion : Opens (ℝ × Vector 3) :=
  ⟨(coordinateSource s : Set (ℝ × Vector 3)) ∩
      (fun q : ℝ × Vector 3 ↦ g q.1 (s.symm q.2)) ⁻¹' c.source,
    (contMDiffOn_inChart g hg s).continuousOn.isOpen_inter_preimage
      (coordinateSource s).isOpen c.open_source⟩

theorem contDiffOn_coordinateFamily :
    ContDiffOn ℝ ∞ (uncurry (coordinateFamily g s c)) (coordinateRegion g hg s c) :=
  (c.contMDiffOn_toFun.comp ((contMDiffOn_inChart g hg s).mono inter_subset_left)
    (fun _ hq ↦ hq.2)).contDiffOn

theorem mem_coordinateRegion_at_source (q : ℝ × Sphere 3)
    (hs : q.2 ∈ s.source) (hc : g q.1 q.2 ∈ c.source) :
    (q.1, s q.2) ∈ coordinateRegion g hg s c := by
  have hleft : s.symm (s q.2) = q.2 := s.left_inv hs
  change s q.2 ∈ s.target ∧ g q.1 (s.symm (s q.2)) ∈ c.source
  rw [hleft]
  exact ⟨s.map_source hs, hc⟩

theorem injective_coordinate_spatial_iff (q : ℝ × Sphere 3)
    (hs : q.2 ∈ s.source) (hc : g q.1 q.2 ∈ c.source) :
    Injective (fderiv ℝ (coordinateFamily g s c q.1) (s q.2)) ↔
      Injective (mfderiv (𝓡 3) (𝓡 n) (g q.1) q.2) := by
  have hslice : ContMDiff (𝓡 3) (𝓡 n) ∞ (g q.1) :=
    hg.comp (contMDiff_const.prodMk contMDiff_id)
  have hleft : s.symm (s q.2) = q.2 := s.left_inv hs
  have hc' : g q.1 (s.symm (s q.2)) ∈ c.source := by
    rw [hleft]
    exact hc
  have h := ManifoldCoordinates.injective_fderiv_in_charts_iff
    (g q.1) s c (s q.2) (s.map_source hs) hc' (hslice.mdifferentiableAt (by simp))
  rw [hleft] at h
  exact h

end NoExoticSixSphere.SphereFamily
