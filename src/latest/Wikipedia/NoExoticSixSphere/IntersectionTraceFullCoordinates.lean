import Wikipedia.NoExoticSixSphere.IntersectionTraceCoordinates

/-!
# Coincidence coordinates on an open neighborhood of an endpoint time

The source and target chart conditions impose no time cutoff. In particular,
the actual native coincidence equation is smooth on an open neighborhood
of a valid endpoint configuration, not just on the open time interval.
-/

noncomputable section

open Set Function Topology
open scoped Manifold ContDiff

namespace NoExoticSixSphere.IntersectionTrace

open GLOrthonormalization

variable {M : Type*} [TopologicalSpace M] [ChartedSpace (Vector 6) M]
  (f g : ℝ → Sphere 3 → M)
  (hf : ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 3)) (𝓡 6) ∞ (uncurry f))
  (hg : ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 3)) (𝓡 6) ∞ (uncurry g))
  (s z : SphereChart) (c : ManifoldChart M)

def fullCoordinateSource : Set PairModel := {q | q.2.1 ∈ s.target ∧ q.2.2 ∈ z.target}

theorem isOpen_fullCoordinateSource : IsOpen (fullCoordinateSource s z) :=
  (s.open_target.preimage continuous_snd.fst).inter
    (z.open_target.preimage continuous_snd.snd)

include hf in
theorem contMDiffOn_coordinateLeft_full :
    ContMDiffOn 𝓘(ℝ, PairModel) (𝓡 6) ∞ (coordinateLeft f s) (fullCoordinateSource s z) := by
  have ht : ContMDiffOn 𝓘(ℝ, PairModel) 𝓘(ℝ, ℝ) ∞
      (fun q : PairModel ↦ q.1) (fullCoordinateSource s z) :=
    contDiff_fst.contMDiff.contMDiffOn
  have hx : ContMDiffOn 𝓘(ℝ, PairModel) (𝓡 3) ∞
      (fun q : PairModel ↦ s.symm q.2.1) (fullCoordinateSource s z) :=
    s.contMDiffOn_invFun.comp
      (contDiff_fst.comp contDiff_snd).contMDiff.contMDiffOn (fun _ hq ↦ hq.1)
  exact hf.comp_contMDiffOn (ht.prodMk hx)

include hg in
theorem contMDiffOn_coordinateRight_full :
    ContMDiffOn 𝓘(ℝ, PairModel) (𝓡 6) ∞ (coordinateRight g z) (fullCoordinateSource s z) := by
  have ht : ContMDiffOn 𝓘(ℝ, PairModel) 𝓘(ℝ, ℝ) ∞
      (fun q : PairModel ↦ q.1) (fullCoordinateSource s z) :=
    contDiff_fst.contMDiff.contMDiffOn
  have hx : ContMDiffOn 𝓘(ℝ, PairModel) (𝓡 3) ∞
      (fun q : PairModel ↦ z.symm q.2.2) (fullCoordinateSource s z) :=
    z.contMDiffOn_invFun.comp
      (contDiff_snd.comp contDiff_snd).contMDiff.contMDiffOn (fun _ hq ↦ hq.2)
  exact hg.comp_contMDiffOn (ht.prodMk hx)

def fullCoordinateDomain : Set PairModel := fullCoordinateSource s z ∩
  (fun q ↦ (coordinateLeft f s q, coordinateRight g z q)) ⁻¹' (c.source ×ˢ c.source)

include hf hg in
theorem isOpen_fullCoordinateDomain : IsOpen (fullCoordinateDomain f g s z c) :=
  ((contMDiffOn_coordinateLeft_full f hf s z).continuousOn.prodMk
    (contMDiffOn_coordinateRight_full g hg s z).continuousOn).isOpen_inter_preimage
    (isOpen_fullCoordinateSource s z) (c.open_source.prod c.open_source)

include hf hg in
theorem contDiffOn_coordinateDifference_full :
    ContDiffOn ℝ ∞ (coordinateDifference f g s z c) (fullCoordinateDomain f g s z c) := by
  have hL : ContDiffOn ℝ ∞ (fun q ↦ c (coordinateLeft f s q))
      (fullCoordinateDomain f g s z c) := (c.contMDiffOn_toFun.comp
    ((contMDiffOn_coordinateLeft_full f hf s z).mono
      (show fullCoordinateDomain f g s z c ⊆ fullCoordinateSource s z from inter_subset_left))
    (fun _ hq ↦ hq.2.1)).contDiffOn
  have hR : ContDiffOn ℝ ∞ (fun q ↦ c (coordinateRight g z q))
      (fullCoordinateDomain f g s z c) := (c.contMDiffOn_toFun.comp
    ((contMDiffOn_coordinateRight_full g hg s z).mono
      (show fullCoordinateDomain f g s z c ⊆ fullCoordinateSource s z from inter_subset_left))
    (fun _ hq ↦ hq.2.2)).contDiffOn
  exact hL.sub hR

theorem coordinateDifference_zero_iff_full (q : PairModel)
    (hq : q ∈ fullCoordinateDomain f g s z c) :
    coordinateDifference f g s z c q = 0 ↔
      f q.1 (s.symm q.2.1) = g q.1 (z.symm q.2.2) := by
  change c (coordinateLeft f s q) - c (coordinateRight g z q) = 0 ↔ _
  rw [sub_eq_zero]
  exact ⟨fun h ↦ c.injOn hq.2.1 hq.2.2 h, fun h ↦ congrArg c h⟩

end NoExoticSixSphere.IntersectionTrace
