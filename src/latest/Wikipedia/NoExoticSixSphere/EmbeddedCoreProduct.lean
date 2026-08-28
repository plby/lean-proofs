import Wikipedia.NoExoticSixSphere.CompactCoreImmersion
import Wikipedia.NoExoticSixSphere.UniformProductTube
import Wikipedia.NoExoticSixSphere.PartialFrames

/-!
# An embedded thin product from an embedded immersive compact disk core

For a general smooth product map, not necessarily an affine thickening,
compact-core injectivity and the tube lemma give one embedded immersive
closed product. The output radius is bounded by the supplied smooth domain.
-/

noncomputable section

open Function Set Metric Topology
open scoped ContDiff

namespace NoExoticSixSphere

open GLOrthonormalization

theorem exists_embedded_core_product {N q : ℕ} (H : Vector 4 × Vector q → Vector N)
    (r : ℝ) (hr : 0 < r)
    (hHs : ∀ x ∈ closedBall (0 : Vector 4) 1, ∀ v ∈ closedBall (0 : Vector q) r,
      ContDiffAt ℝ ∞ H (x, v))
    (hcore : InjOn (fun x ↦ H (x, 0)) (closedBall (0 : Vector 4) 1))
    (hi : ∀ x ∈ closedBall (0 : Vector 4) 1, Injective (fderiv ℝ H (x, 0))) :
    ∃ ε : ℝ, 0 < ε ∧ ε ≤ r ∧
      IsClosedEmbedding (fun p : closedBall (0 : Vector 4) 1 × closedBall (0 : Vector q) ε ↦
        H (p.1.val, p.2.val)) ∧
      ∀ x ∈ closedBall (0 : Vector 4) 1, ∀ v ∈ closedBall (0 : Vector q) ε,
        ContDiffAt ℝ ∞ H (x, v) ∧ Injective (fderiv ℝ H (x, v)) := by
  let K := closedBall (0 : Vector 4) 1 ×ˢ ({0} : Set (Vector q))
  have hK : IsCompact K := (isCompact_closedBall (0 : Vector 4) 1).prod isCompact_singleton
  have hKs : ∀ p ∈ K, ContDiffAt ℝ ∞ H p := by
    rintro ⟨x, v⟩ ⟨hx, hv⟩
    rcases mem_singleton_iff.mp hv with rfl
    exact hHs x hx 0 (mem_closedBall_self hr.le)
  have hKi : InjOn H K := by
    rintro ⟨x, v⟩ ⟨hx, hv⟩ ⟨y, w⟩ ⟨hy, hw⟩ he
    rcases mem_singleton_iff.mp hv with rfl
    rcases mem_singleton_iff.mp hw with rfl
    exact Prod.ext (hcore hx hy he) rfl
  have hKd : ∀ p ∈ K, Injective (fderiv ℝ H p) := by
    rintro ⟨x, v⟩ ⟨hx, hv⟩
    rcases mem_singleton_iff.mp hv with rfl
    exact hi x hx
  obtain ⟨V, hV, hKV, hVi, hVd⟩ :=
    CompactCoreImmersion.exists_open_injOn_near_compact hK hKs hKi hKd
  let coreInclusion : closedBall (0 : Vector 4) 1 × Vector q → Vector 4 × Vector q :=
    fun p ↦ (p.1.val, p.2)
  have hq : Continuous coreInclusion :=
    (continuous_subtype_val.comp continuous_fst).prodMk continuous_snd
  obtain ⟨δ, hδ, hδV⟩ := exists_uniform_closedProductTube (hV.preimage hq)
    (fun x ↦ hKV ⟨x.property, rfl⟩)
  let ε := min δ r
  have hεδ : ε ≤ δ := min_le_left _ _
  have hεr : ε ≤ r := min_le_right _ _
  have hm (x : Vector 4) (hx : x ∈ closedBall (0 : Vector 4) 1)
      (v : Vector q) (hv : v ∈ closedBall (0 : Vector q) ε) : (x, v) ∈ V := by
    apply hδV ⟨x, hx⟩ v
    have hvδ := (closedBall_subset_closedBall hεδ) hv
    simpa only [mem_closedBall, dist_zero_right] using hvδ
  let j : closedBall (0 : Vector 4) 1 × closedBall (0 : Vector q) ε → Vector 4 × Vector q :=
    fun p ↦ (p.1.val, p.2.val)
  have hj : Continuous j := (continuous_subtype_val.comp continuous_fst).prodMk
    (continuous_subtype_val.comp continuous_snd)
  have hc : Continuous (fun p : closedBall (0 : Vector 4) 1 × closedBall (0 : Vector q) ε ↦
      H (p.1.val, p.2.val)) := by
    apply continuous_iff_continuousAt.mpr
    intro p
    exact ContinuousAt.comp (f := j)
      (hHs p.1.val p.1.property p.2.val
        ((closedBall_subset_closedBall hεr) p.2.property)).continuousAt hj.continuousAt
  refine ⟨ε, lt_min hδ hr, hεr, hc.isClosedEmbedding ?_, ?_⟩
  · intro p z hpz
    have hp := hVi (hm p.1.val p.1.property p.2.val p.2.property)
      (hm z.1.val z.1.property z.2.val z.2.property) hpz
    exact Prod.ext (Subtype.ext (congrArg (Prod.fst : Vector 4 × Vector q → _) hp))
      (Subtype.ext (congrArg (Prod.snd : Vector 4 × Vector q → _) hp))
  · intro x hx v hv
    exact ⟨hHs x hx v ((closedBall_subset_closedBall hεr) hv), hVd (x, v) (hm x hx v hv)⟩

end NoExoticSixSphere
