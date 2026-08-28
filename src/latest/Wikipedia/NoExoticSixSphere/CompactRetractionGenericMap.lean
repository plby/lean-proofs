import Wikipedia.NoExoticSixSphere.GenericFourSevenManifoldJets
import Wikipedia.NoExoticSixSphere.CompactRetractionGenericDoublePoints
import Wikipedia.NoExoticSixSphere.LocalInverse

/-!
# One small protected map with generic jets on the original source region

Compactness is used only for the specified source region and its actual
image. A countable cover of the original target charts controls the same
parameter everywhere. Small parameters remain in the constructed tubular
domain on the whole compact source, including protected boundary points.
The resulting map is smooth there and fixes the cutoff zero set exactly.
The same parameter has regular actual double-point equations whenever
at least one source point is outside the protected zero set.
-/

noncomputable section

open Set Function Filter Metric
open MeasureTheory MeasureTheory.Measure
open scoped Manifold ContDiff Topology

namespace NoExoticSixSphere.CompactRetractionAffineFamily

open GLOrthonormalization EuclideanEmbedding

variable {d n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (Vector n) M]
  (e : EuclideanEmbedding n M) {K : Set M} (r : e.RetractionNear K)
  (f : Vector d → M) (χ : Vector d → ℝ)

theorem eventually_mem_tubular_on_compact {L : Set (Vector d)} (hL : IsCompact L)
    (hf : ∀ x ∈ L, ContMDiffAt (𝓡 d) (𝓡 n) ∞ f x) (hχ : ContDiff ℝ ∞ χ)
    (hb : ∀ x ∈ L, f x ∈ r.base) :
    ∀ᶠ p in 𝓝 (0 : Parameters d e), ∀ x ∈ L, ambient e f χ p x ∈ r.domain := by
  apply hL.eventually_forall_of_forall_eventually
  intro x hx
  have he : ambient e f χ (0 : Parameters d e) x = e.toFun (f x) := by
    simp only [ambient, WeightedAffineComposite.ambient, AffinePerturbation.value,
      Prod.fst_zero, Prod.snd_zero, zero_apply, add_zero, smul_zero, comp_apply]
  have hmem : ambient e f χ (0 : Parameters d e) x ∈ r.domain :=
    he.symm ▸ r.contains ⟨f x, hb x hx, rfl⟩
  exact (contDiffAt_ambient e f χ 0 x (hf x hx) hχ.contDiffAt).continuousAt
    (r.domain.isOpen.mem_nhds hmem)

include e in
theorem exists_countable_target_chart_cover [IsManifold (𝓡 n) ∞ M] :
    ∃ C : Set (PartialDiffeomorph (𝓡 n) (𝓡 n) M (Vector n) ∞),
      C.Countable ∧ ∀ x : M, ∃ c ∈ C, x ∈ c.source := by
  let : SecondCountableTopology M := e.closedEmbedding.isEmbedding.secondCountableTopology
  let c := fun x : M ↦ modelChartPartialDiffeomorph (I := 𝓡 n) x
  have hcover : (univ : Set M) ⊆ ⋃ x, (c x).source := by
    intro x _
    exact mem_iUnion.mpr ⟨x, mem_extChartAt_source x⟩
  obtain ⟨T, hT, hcov⟩ := isLindelof_univ.elim_countable_subcover
    (fun x ↦ (c x).source) (fun x ↦ (c x).open_source) hcover
  refine ⟨c '' T, hT.image c, ?_⟩
  intro x
  obtain ⟨y, hy, hxy⟩ := mem_iUnion₂.mp (hcov (mem_univ x))
  exact ⟨c y, mem_image_of_mem c hy, hxy⟩

theorem exists_small_regular_on_compact_mem [IsManifold (𝓡 n) ∞ M]
    {L : Set (Vector d)} (hL : IsCompact L)
    (hf : ∀ x ∈ L, ContMDiffAt (𝓡 d) (𝓡 n) ∞ f x) (hχ : ContDiff ℝ ∞ χ)
    (hb : ∀ x ∈ L, f x ∈ r.base) (U : TopologicalSpace.Opens (Vector d))
    (hUL : (U : Set _) ⊆ L) (hd : d = 4) (hn : n = 7)
    (A : Set (Parameters d e)) (hA : A ∈ 𝓝 (0 : Parameters d e))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ C : Set (PartialDiffeomorph (𝓡 n) (𝓡 n) M (Vector n) ∞),
      ∃ p : Parameters d e,
        C.Countable ∧ (∀ y : M, ∃ c ∈ C, y ∈ c.source) ∧ ‖p‖ < ε ∧ p ∈ A ∧
        (∀ x ∈ L, ambient e f χ p x ∈ r.domain) ∧
        (∀ x ∈ L, ContMDiffAt (𝓡 d) (𝓡 n) ∞ (map e r f χ p) x) ∧
        (∀ x ∈ L, χ x = 0 → map e r f χ p x = f x) ∧
        (∀ c ∈ C, OperatorRank.RegularFourSevenOn
          (fun x ↦ chartJet e r f χ c (p, x))
          {x | (p, x) ∈ activeChartDomain e r f χ U
            (fun x hx ↦ (hf x (hUL hx)).contMDiffWithinAt) hχ c}) ∧
        RegularDoublePointsOn (map e r f χ p) U {x | χ x ≠ 0} C := by
  let : MeasurableSpace (Parameters d e) := borel (Parameters d e)
  let : BorelSpace (Parameters d e) := ⟨rfl⟩
  obtain ⟨C, hC, hcov⟩ := exists_countable_target_chart_cover e
  have hfU : ContMDiffOn (𝓡 d) (𝓡 n) ∞ f U :=
    fun x hx ↦ (hf x (hUL hx)).contMDiffWithinAt
  have hgen := ae_regular_in_charts e r f χ U hfU hχ addHaar hd hn C hC
  have hpair := ae_regular_double_points_in_charts e r f χ U hfU hχ addHaar C hC
  have hdense := Measure.dense_of_ae (hgen.and hpair)
  have hnear := eventually_mem_tubular_on_compact e r f χ hL hf hχ hb
  obtain ⟨δ, hδ, hδmem⟩ := Metric.mem_nhds_iff.mp (hnear.and hA)
  obtain ⟨p, hp, hsmall⟩ := hdense.exists_dist_lt 0 (lt_min hε hδ)
  have hp' : ‖p‖ < min ε δ := by simpa only [dist_zero_left] using hsmall
  have hpnear : (∀ x ∈ L, ambient e f χ p x ∈ r.domain) ∧ p ∈ A :=
    hδmem (mem_ball_zero_iff.mpr (hp'.trans_le (min_le_right _ _)))
  have hmem := hpnear.1
  have hdouble := regularDoublePointsOn_of_chartwise e r f χ U hfU hχ C p
    (fun x hx ↦ hmem x (hUL hx)) hp.2
  refine ⟨C, p, hC, hcov, hp'.trans_le (min_le_left _ _), hpnear.2, hmem,
    ?_, ?_, hp.1, hdouble⟩
  · intro x hx
    exact (contMDiffAt_map e r f χ p x (hf x hx) hχ.contDiffAt (hmem x hx)).comp x
      (contDiff_const.prodMk contDiff_id).contMDiff.contMDiffAt
  · intro x hx hzero
    exact map_eq_of_cutoff_zero e r f χ p x (hb x hx) hzero

theorem exists_small_regular_on_compact [IsManifold (𝓡 n) ∞ M]
    {L : Set (Vector d)} (hL : IsCompact L)
    (hf : ∀ x ∈ L, ContMDiffAt (𝓡 d) (𝓡 n) ∞ f x) (hχ : ContDiff ℝ ∞ χ)
    (hb : ∀ x ∈ L, f x ∈ r.base) (U : TopologicalSpace.Opens (Vector d))
    (hUL : (U : Set _) ⊆ L) (hd : d = 4) (hn : n = 7) {ε : ℝ} (hε : 0 < ε) :
    ∃ C : Set (PartialDiffeomorph (𝓡 n) (𝓡 n) M (Vector n) ∞),
      ∃ p : Parameters d e,
        C.Countable ∧ (∀ y : M, ∃ c ∈ C, y ∈ c.source) ∧ ‖p‖ < ε ∧
        (∀ x ∈ L, ambient e f χ p x ∈ r.domain) ∧
        (∀ x ∈ L, ContMDiffAt (𝓡 d) (𝓡 n) ∞ (map e r f χ p) x) ∧
        (∀ x ∈ L, χ x = 0 → map e r f χ p x = f x) ∧
        ∀ c ∈ C, OperatorRank.RegularFourSevenOn
          (fun x ↦ chartJet e r f χ c (p, x))
          {x | (p, x) ∈ activeChartDomain e r f χ U
            (fun x hx ↦ (hf x (hUL hx)).contMDiffWithinAt) hχ c} := by
  obtain ⟨C, p, hC, hcov, hp, -, hmem, hs, heq, hg⟩ :=
    exists_small_regular_on_compact_mem e r f χ hL hf hχ hb U hUL hd hn
      univ univ_mem hε
  exact ⟨C, p, hC, hcov, hp, hmem, hs, heq, hg.1⟩

end NoExoticSixSphere.CompactRetractionAffineFamily
