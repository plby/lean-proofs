import Wikipedia.NoExoticSixSphere.CompactFiberNeighborhood
import Wikipedia.NoExoticSixSphere.TransverseSphereResolution
import Wikipedia.SmoothSixDPoincare.PartialDiffeomorphRestriction

/-!
# A transverse chart clean with respect to both entire sphere maps

At a common value with one preimage on each sphere, compactness excludes
all branches outside small reference-chart disks. The native transverse
chart then identifies the complete fibers, not just the local patch images.
The unique-fiber hypotheses remain explicit and are not inferred from
transversality of one selected pair.
-/

noncomputable section

open Set Function Metric Topology
open scoped Manifold ContDiff

namespace NoExoticSixSphere.SphereSumNeck

open GLOrthonormalization

theorem sourceChart_isOpenMap : IsOpenMap sourceChart :=
  (sourceChart.toOpenPartialHomeomorph.isOpenEmbedding sourceChart_source).isOpenMap

variable {M : Type*} [TopologicalSpace M] [ChartedSpace (Vector 6) M]
  [IsManifold (𝓡 6) ∞ M] [T2Space M] [CompactSpace M]
  (F G : C(Sphere 3, M))

theorem exists_globally_clean_sphere_sheetChart
    (hF : ContMDiff (𝓡 3) (𝓡 6) ∞ F) (hG : ContMDiff (𝓡 3) (𝓡 6) ∞ G)
    (hzero : F (sourceChart 0) = G (sourceChart 0))
    (hFu : ∀ x, F x = F (sourceChart 0) → x = sourceChart 0)
    (hGu : ∀ x, G x = G (sourceChart 0) → x = sourceChart 0)
    (ht : Surjective ((mfderiv (𝓡 3) (𝓡 6) F (sourceChart 0)).coprod
      (mfderiv (𝓡 3) (𝓡 6) G (sourceChart 0))))
    {O : Set M} (hO : IsOpen O) (h0O : F (sourceChart 0) ∈ O) :
    ∃ b : ℝ, 0 < b ∧ ∃ Φ : PartialDiffeomorph 𝓘(ℝ, Vector 3 × Vector 3) (𝓡 6)
      (Vector 3 × Vector 3) M ∞,
      closedBall (0 : Vector 3) b ×ˢ closedBall (0 : Vector 3) b ⊆ Φ.source ∧
      Φ.target ⊆ O ∧
      (∀ v, (v, 0) ∈ Φ.source → Φ (v, 0) = F (sourceChart v)) ∧
      (∀ v, (0, v) ∈ Φ.source → Φ (0, v) = G (sourceChart v)) ∧
      (∀ q ∈ Φ.source,
        (∀ x, F x = Φ q ↔ q.2 = 0 ∧ x = sourceChart q.1) ∧
        (∀ x, G x = Φ q ↔ q.1 = 0 ∧ x = sourceChart q.2)) := by
  have hf := hF.comp contMDiff_sourceChart
  have hg := hG.comp contMDiff_sourceChart
  have hdim : Module.finrank ℝ (Vector 3) + Module.finrank ℝ (Vector 3) =
      Module.finrank ℝ (Vector 6) := by simp
  obtain ⟨a, ha, Φ, hprod, _, htarget, hleft, hright⟩ :=
    Wikipedia.SmoothSixDPoincare.exists_simultaneous_sheetChart isOpen_univ isOpen_univ
      (mem_univ (0 : Vector 3)) (mem_univ (0 : Vector 3)) hf.contMDiffOn hg.contMDiffOn
      hzero.symm hdim (sourceChart_transversality F G hF hG ht) hO h0O
  let U := sourceChart '' ball (0 : Vector 3) a
  have hU : IsOpen U := sourceChart_isOpenMap _ isOpen_ball
  have h0U : sourceChart 0 ∈ U := ⟨0, mem_ball_self ha, rfl⟩
  obtain ⟨A, hA, h0A, hpreA⟩ := exists_open_full_preimage_subset F.continuous hU
    (fun x hx ↦ (hFu x hx).symm ▸ h0U)
  obtain ⟨B, hB, h0B, hpreB⟩ := exists_open_full_preimage_subset G.continuous hU
    (fun x hx ↦ (hGu x hx).symm ▸ h0U)
  let Ψ := Wikipedia.SmoothSixDPoincare.PartialChart.restrictTarget Φ (hA.inter hB)
  have h0Φ : (0, 0) ∈ Φ.source := hprod
    ⟨mem_closedBall_self ha.le, mem_closedBall_self ha.le⟩
  have h0Ψ : (0, 0) ∈ Ψ.source := by
    refine ⟨h0Φ, ?_⟩
    change Φ (0, 0) ∈ A ∩ B
    rw [hleft 0 h0Φ]
    change F (sourceChart 0) ∈ A ∩ B
    exact ⟨h0A, hzero.symm ▸ h0B⟩
  obtain ⟨b, hb, hball⟩ := nhds_basis_closedBall.mem_iff.mp (Ψ.open_source.mem_nhds h0Ψ)
  refine ⟨b, hb, Ψ, ?_, fun _ hy ↦ htarget hy.1,
    (fun v hv ↦ hleft v hv.1), (fun v hv ↦ hright v hv.1), ?_⟩
  · rw [closedBall_prod_same]
    exact hball
  · rintro ⟨u, v⟩ hq
    constructor
    · intro x
      constructor
      · intro he
        obtain ⟨w, hw, hxw⟩ := hpreA x (he ▸ hq.2.1)
        have hs : (w, 0) ∈ Φ.source := hprod
          ⟨ball_subset_closedBall hw, mem_closedBall_self ha.le⟩
        have haxis : Φ (w, 0) = F x := (hleft w hs).trans (congrArg F hxw)
        have hp : (u, v) = (w, 0) := Φ.injOn hq.1 hs (he.symm.trans haxis.symm)
        exact ⟨congrArg Prod.snd hp,
          hxw.symm.trans (congrArg sourceChart (congrArg Prod.fst hp).symm)⟩
      · rintro ⟨rfl, rfl⟩
        exact (hleft u hq.1).symm
    · intro x
      constructor
      · intro he
        obtain ⟨w, hw, hxw⟩ := hpreB x (he ▸ hq.2.2)
        have hs : (0, w) ∈ Φ.source := hprod
          ⟨mem_closedBall_self ha.le, ball_subset_closedBall hw⟩
        have haxis : Φ (0, w) = G x := (hright w hs).trans (congrArg G hxw)
        have hp : (u, v) = (0, w) := Φ.injOn hq.1 hs (he.symm.trans haxis.symm)
        exact ⟨congrArg Prod.fst hp,
          hxw.symm.trans (congrArg sourceChart (congrArg Prod.snd hp).symm)⟩
      · rintro ⟨rfl, rfl⟩
        exact (hright v hq.1).symm

end NoExoticSixSphere.SphereSumNeck
