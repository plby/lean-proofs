import Wikipedia.NoExoticSixSphere.SphereIntersectionTrace
import Wikipedia.NoExoticSixSphere.RegularLevelNormalForm
import Wikipedia.NoExoticSixSphere.RegularLevelChart
import Wikipedia.NoExoticSixSphere.PartialHomeomorphSubsets
import Wikipedia.NoExoticSixSphere.EuclideanTailSplitting

/-!
# Native chart equations for intersections of two sphere families

Each sphere has its own source chart. The target chart is shared only near
an actual coincidence. The open domain retains both source-chart conditions
and both target-chart conditions. Its zero equation is exactly equality of
the original images, and smoothness is proved only on that valid domain.
-/

noncomputable section

open Set Function Topology
open scoped Manifold ContDiff

namespace NoExoticSixSphere.IntersectionTrace

open GLOrthonormalization

abbrev SphereChart := PartialDiffeomorph (𝓡 3) (𝓡 3) (Sphere 3) (Vector 3) ∞

abbrev ManifoldChart (M : Type*) [TopologicalSpace M] [ChartedSpace (Vector 6) M] :=
  PartialDiffeomorph (𝓡 6) (𝓡 6) M (Vector 6) ∞

abbrev PairModel := ℝ × (Vector 3 × Vector 3)

variable {M : Type*} [TopologicalSpace M] [ChartedSpace (Vector 6) M]
  (f g : ℝ → Sphere 3 → M)
  (hf : ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 3)) (𝓡 6) ∞ (uncurry f))
  (hg : ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 3)) (𝓡 6) ∞ (uncurry g))
  (s z : SphereChart) (c : ManifoldChart M)

def coordinateSource : Set PairModel :=
  {q | q.1 ∈ Ioo 0 1 ∧ q.2.1 ∈ s.target ∧ q.2.2 ∈ z.target}

theorem isOpen_coordinateSource : IsOpen (coordinateSource s z) :=
  (isOpen_Ioo.preimage continuous_fst).inter
    ((s.open_target.preimage continuous_snd.fst).inter
      (z.open_target.preimage continuous_snd.snd))

def coordinateLeft (q : PairModel) : M := f q.1 (s.symm q.2.1)

def coordinateRight (q : PairModel) : M := g q.1 (z.symm q.2.2)

include hf in
theorem contMDiffOn_coordinateLeft :
    ContMDiffOn 𝓘(ℝ, PairModel) (𝓡 6) ∞ (coordinateLeft f s) (coordinateSource s z) := by
  have ht : ContMDiffOn 𝓘(ℝ, PairModel) 𝓘(ℝ, ℝ) ∞
      (fun q : PairModel ↦ q.1) (coordinateSource s z) := contDiff_fst.contMDiff.contMDiffOn
  have hx : ContMDiffOn 𝓘(ℝ, PairModel) (𝓡 3) ∞
      (fun q : PairModel ↦ s.symm q.2.1) (coordinateSource s z) :=
    s.contMDiffOn_invFun.comp
      (contDiff_fst.comp contDiff_snd).contMDiff.contMDiffOn (fun _ hq ↦ hq.2.1)
  exact hf.comp_contMDiffOn (ht.prodMk hx)

include hg in
theorem contMDiffOn_coordinateRight :
    ContMDiffOn 𝓘(ℝ, PairModel) (𝓡 6) ∞ (coordinateRight g z) (coordinateSource s z) := by
  have ht : ContMDiffOn 𝓘(ℝ, PairModel) 𝓘(ℝ, ℝ) ∞
      (fun q : PairModel ↦ q.1) (coordinateSource s z) := contDiff_fst.contMDiff.contMDiffOn
  have hx : ContMDiffOn 𝓘(ℝ, PairModel) (𝓡 3) ∞
      (fun q : PairModel ↦ z.symm q.2.2) (coordinateSource s z) :=
    z.contMDiffOn_invFun.comp
      (contDiff_snd.comp contDiff_snd).contMDiff.contMDiffOn (fun _ hq ↦ hq.2.2)
  exact hg.comp_contMDiffOn (ht.prodMk hx)

def coordinateDomain : Set PairModel := coordinateSource s z ∩
  (fun q ↦ (coordinateLeft f s q, coordinateRight g z q)) ⁻¹' (c.source ×ˢ c.source)

include hf hg in
theorem isOpen_coordinateDomain : IsOpen (coordinateDomain f g s z c) :=
  ((contMDiffOn_coordinateLeft f hf s z).continuousOn.prodMk
    (contMDiffOn_coordinateRight g hg s z).continuousOn).isOpen_inter_preimage
    (isOpen_coordinateSource s z) (c.open_source.prod c.open_source)

def coordinateDifference (q : PairModel) : Vector 6 :=
  c (coordinateLeft f s q) - c (coordinateRight g z q)

include hf hg in
theorem contDiffOn_coordinateDifference :
    ContDiffOn ℝ ∞ (coordinateDifference f g s z c) (coordinateDomain f g s z c) := by
  have hL : ContDiffOn ℝ ∞ (fun q ↦ c (coordinateLeft f s q))
      (coordinateDomain f g s z c) := (c.contMDiffOn_toFun.comp
    ((contMDiffOn_coordinateLeft f hf s z).mono
      (show coordinateDomain f g s z c ⊆ coordinateSource s z from inter_subset_left))
    (fun _ hq ↦ hq.2.1)).contDiffOn
  have hR : ContDiffOn ℝ ∞ (fun q ↦ c (coordinateRight g z q))
      (coordinateDomain f g s z c) := (c.contMDiffOn_toFun.comp
    ((contMDiffOn_coordinateRight g hg s z).mono
      (show coordinateDomain f g s z c ⊆ coordinateSource s z from inter_subset_left))
    (fun _ hq ↦ hq.2.2)).contDiffOn
  exact hL.sub hR

theorem coordinateDifference_zero_iff (q : PairModel) (hq : q ∈ coordinateDomain f g s z c) :
    coordinateDifference f g s z c q = 0 ↔
      f q.1 (s.symm q.2.1) = g q.1 (z.symm q.2.2) := by
  change c (coordinateLeft f s q) - c (coordinateRight g z q) = 0 ↔ _
  rw [sub_eq_zero]
  exact ⟨fun h ↦ c.injOn hq.2.1 hq.2.2 h, fun h ↦ congrArg c h⟩

end NoExoticSixSphere.IntersectionTrace
