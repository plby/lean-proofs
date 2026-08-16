import Wikipedia.SzemeredisTheorem.Hypergraph.RankwiseBundleEnvelopeSelection
import Wikipedia.SzemeredisTheorem.Hypergraph.SourceFullRankwiseBundleCounting
import Wikipedia.SzemeredisTheorem.Hypergraph.SourceFullOrderedRemoval
import Wikipedia.SzemeredisTheorem.Hypergraph.SourceFullCoarseTargetRegularity
import Wikipedia.SzemeredisTheorem.Hypergraph.SourceFullBundleRemovalParameters
import Wikipedia.SzemeredisTheorem.Hypergraph.OrderedRemovalAssembly

/-!
# Source-full bundle-counting removal assembly

This file joins the ambient-independent source-full regularity plan to the
rankwise bundle-counting theorem and the source-full bad-base deletion family.
The selected regularity scale is clipped to the finite rank horizon.  Since
the selected scales decrease with rank while `sourceBundleDensity` decreases
with its scale, the resulting density schedule increases with rank; hence its
bundle prefix floor is exactly its rank-zero value.
-/

namespace Wikipedia.SzemeredisTheorem

open scoped BigOperators

/-! ## Ambient-independent scalar budgets -/

/-- The largest edge horizon queried by the reverse-doubling recurrence. -/
noncomputable def sourceBundleRemovalHorizon (k r : ℕ) : ℕ :=
  bundleReverseDoublingHorizon r
    (orderedConfigurationInitialBundle k r).edges.card 0

/-- Each positive subface spends two copies of this allowance: one for
low density and one for its source-full defect. -/
noncomputable def sourceBundleRemovalDensityBudget
    (ε : ℝ) (r : ℕ) : ℝ :=
  min ε 1 /
    (4 * (Fintype.card (OrderedPositiveSubface r) + 1 : ℕ) : ℕ)

/-- The per-step reserve in the explicit reverse-doubling envelope. -/
noncomputable def sourceBundleRemovalStep (k r : ℕ) : ℝ :=
  1 /
    (4 * (r * sourceBundleRemovalHorizon k r + 1 : ℕ) : ℕ)

/-- The square-root defect coefficient; the factor eight leaves room for
both halves of every one-edge counting increment. -/
noncomputable def sourceBundleRemovalKappa (k r : ℕ) : ℝ :=
  sourceBundleRemovalStep k r / 8

theorem sourceBundleRemovalDensityBudget_pos
    {ε : ℝ} (hε : 0 < ε) (r : ℕ) :
    0 < sourceBundleRemovalDensityBudget ε r := by
  unfold sourceBundleRemovalDensityBudget
  positivity

theorem sourceBundleRemovalDensityBudget_le_one
    {ε : ℝ} (hε : 0 < ε) (r : ℕ) :
    sourceBundleRemovalDensityBudget ε r ≤ 1 := by
  unfold sourceBundleRemovalDensityBudget
  have hmin : min ε 1 ≤ 1 := min_le_right _ _
  have hden : (1 : ℝ) ≤
      (4 * (Fintype.card (OrderedPositiveSubface r) + 1 : ℕ) : ℕ) := by
    push_cast
    have hcard :
        (0 : ℝ) ≤ Fintype.card (OrderedPositiveSubface r) := by
      positivity
    nlinarith
  exact (div_le_self (le_of_lt (lt_min hε zero_lt_one)) hden).trans hmin

/-- The total deletion cost of all positive subfaces fits below the input
allowance. -/
theorem card_mul_two_sourceBundleRemovalDensityBudget_le
    {ε : ℝ} (hε : 0 < ε) (r : ℕ) :
    (Fintype.card (OrderedPositiveSubface r) : ℝ) *
        (sourceBundleRemovalDensityBudget ε r +
          sourceBundleRemovalDensityBudget ε r) ≤ ε := by
  let s := Fintype.card (OrderedPositiveSubface r)
  let x : ℝ := min ε 1
  have hx : 0 < x := lt_min hε zero_lt_one
  have hden : (0 : ℝ) < (4 * (s + 1 : ℕ) : ℕ) := by
    positivity
  have hs : (0 : ℝ) ≤ s := by positivity
  calc
    (Fintype.card (OrderedPositiveSubface r) : ℝ) *
          (sourceBundleRemovalDensityBudget ε r +
            sourceBundleRemovalDensityBudget ε r) =
        ((2 * (s : ℝ)) * x) / (4 * (s + 1 : ℕ) : ℕ) := by
      simp only [sourceBundleRemovalDensityBudget, s, x]
      ring
    _ ≤ x := by
      apply (div_le_iff₀ hden).2
      push_cast
      nlinarith
    _ ≤ ε := min_le_left _ _

theorem sourceBundleRemovalStep_pos (k r : ℕ) :
    0 < sourceBundleRemovalStep k r := by
  unfold sourceBundleRemovalStep
  positivity

theorem sourceBundleRemovalStep_le_one (k r : ℕ) :
    sourceBundleRemovalStep k r ≤ 1 := by
  unfold sourceBundleRemovalStep
  apply (div_le_one (by positivity)).2
  push_cast
  have hr : (0 : ℝ) ≤ r := by positivity
  have hH : (0 : ℝ) ≤ sourceBundleRemovalHorizon k r := by
    positivity
  nlinarith [mul_nonneg hr hH]

theorem sourceBundleRemovalKappa_pos (k r : ℕ) :
    0 < sourceBundleRemovalKappa k r := by
  unfold sourceBundleRemovalKappa
  exact div_pos (sourceBundleRemovalStep_pos k r) (by norm_num)

theorem sourceBundleRemovalKappa_le_one (k r : ℕ) :
    sourceBundleRemovalKappa k r ≤ 1 := by
  unfold sourceBundleRemovalKappa
  have hstep := sourceBundleRemovalStep_le_one k r
  nlinarith [sourceBundleRemovalStep_pos k r]

theorem four_mul_sourceBundleRemovalKappa_le_step (k r : ℕ) :
    4 * sourceBundleRemovalKappa k r ≤
      sourceBundleRemovalStep k r := by
  unfold sourceBundleRemovalKappa
  nlinarith [sourceBundleRemovalStep_pos k r]

theorem sourceBundleRemovalKappa_sq_le_half_step (k r : ℕ) :
    sourceBundleRemovalKappa k r ^ 2 ≤
      sourceBundleRemovalStep k r / 2 := by
  unfold sourceBundleRemovalKappa
  have hpos := sourceBundleRemovalStep_pos k r
  have hone := sourceBundleRemovalStep_le_one k r
  nlinarith [sq_nonneg (sourceBundleRemovalStep k r)]

/-- The chosen step reserve makes the entire finite envelope smaller than
one quarter, and therefore supplies both the cap and strict half-error
hypotheses. -/
theorem sourceBundleRemovalStep_total_le_quarter (k r : ℕ) :
    (r : ℝ) * (sourceBundleRemovalHorizon k r : ℝ) *
        sourceBundleRemovalStep k r ≤ 1 / 4 := by
  let p := r * sourceBundleRemovalHorizon k r
  have hden : (0 : ℝ) < (4 * (p + 1 : ℕ) : ℕ) := by
    positivity
  rw [show
    (r : ℝ) * (sourceBundleRemovalHorizon k r : ℝ) *
          sourceBundleRemovalStep k r =
        (p : ℝ) / (4 * (p + 1 : ℕ) : ℕ) by
      simp only [sourceBundleRemovalStep, p]
      push_cast
      ring]
  apply (div_le_iff₀ hden).2
  push_cast
  have hp : (0 : ℝ) ≤ p := by positivity
  nlinarith

theorem sourceBundleRemovalStep_total_le_one (k r : ℕ) :
    (r : ℝ) * (sourceBundleRemovalHorizon k r : ℝ) *
        sourceBundleRemovalStep k r ≤ 1 :=
  (sourceBundleRemovalStep_total_le_quarter k r).trans (by norm_num)

theorem sourceBundleRemovalStep_total_lt_half (k r : ℕ) :
    (r : ℝ) * (sourceBundleRemovalHorizon k r : ℝ) *
        sourceBundleRemovalStep k r < 1 / 2 :=
  (sourceBundleRemovalStep_total_le_quarter k r).trans_lt (by norm_num)

/-! ## A uniform count threshold from the bounded scale ceiling -/

noncomputable def sourceBundleRemovalCountThreshold
    (k r ceiling : ℕ) (δ : ℝ) : ℝ :=
  (1 / 2 : ℝ) *
    sourceBundleDensity δ ceiling ^
      Fintype.card (PositiveOrderedFace k r)

theorem sourceBundleRemovalCountThreshold_pos
    {δ : ℝ} (hδ : 0 < δ) (k r ceiling : ℕ) :
    0 < sourceBundleRemovalCountThreshold k r ceiling δ := by
  unfold sourceBundleRemovalCountThreshold
  exact mul_pos (by norm_num)
    (pow_pos (sourceBundleDensity_pos hδ ceiling) _)

/-! ## End-to-end source-full ordered removal -/

/-- Tao's source-full hierarchy, the rankwise bundle-counting envelope, and
source-full bad-base cleaning prove uniform ordered removal at every positive
rank. -/
theorem hasUniformOrderedPatternRemoval_sourceFull
    (k n : ℕ) (hrank : n + 1 ≤ k) :
    HasUniformOrderedPatternRemoval k (n + 1) := by
  intro ε hε
  let r : ℕ := n + 1
  let edgeBound : ℕ :=
    (orderedConfigurationInitialBundle k r).edges.card
  let N : ℕ := sourceBundleRemovalHorizon k r
  let δ : ℝ := sourceBundleRemovalDensityBudget ε r
  let step : ℝ := sourceBundleRemovalStep k r
  let κ : ℝ := sourceBundleRemovalKappa k r
  have hδ : 0 < δ := by
    exact sourceBundleRemovalDensityBudget_pos hε r
  have hδ_one : δ ≤ 1 := by
    exact sourceBundleRemovalDensityBudget_le_one hε r
  have hstep : 0 < step := by
    exact sourceBundleRemovalStep_pos k r
  have hκ : 0 < κ := by
    exact sourceBundleRemovalKappa_pos k r
  have hκ_one : κ ≤ 1 := by
    exact sourceBundleRemovalKappa_le_one k r
  have hκ_step : 4 * κ ≤ step := by
    exact four_mul_sourceBundleRemovalKappa_le_step k r
  have hκ_sq : κ ^ 2 ≤ step / 2 := by
    exact sourceBundleRemovalKappa_sq_le_half_step k r
  obtain ⟨Q, hQ⟩ :=
    exists_sourceBundleRemovalGrowthCoefficient
      hδ hδ_one hκ hκ_one N
  let F : NatGrowthFunction := sourceBundleRemovalGrowth Q N
  let initialBound : Fin (r + 1) → ℕ := fun _ => 2
  let S : SourceFullCoarseTargetSchedule.Bounded
      k r initialBound F 0 :=
    Classical.choice
      (SourceFullCoarseTargetSchedule.bounded_nonempty
        k r initialBound F 0)
  let c : ℝ :=
    sourceBundleRemovalCountThreshold k r S.ceiling δ
  have hc : 0 < c := by
    exact sourceBundleRemovalCountThreshold_pos hδ k r S.ceiling
  refine ⟨c, hc, ?_⟩
  intro G _instFintype _instDecidableEq _instNonempty H hcount
  let initial : OrderedPartitionComplex G k r :=
    orderedPatternInitialComplex H
  obtain ⟨Cbounded⟩ :=
    S.certificate_nonempty initial (by
      intro q e
      exact complexity_orderedPatternInitialComplex_le_two H q e)
  let C := Cbounded.toSourceFull
  let P : OrderedCoarseFineComplex G k r :=
    C.regularity.toCoarseFine
  let α : ℕ → ℝ := sourceBundleRankwiseDensity δ C.scale
  let β : ℕ → ℝ := sourceBundleRankwiseDefect δ κ N C.scale
  let μ : ℕ → ℝ := bundleRankwiseDensityFloor α
  let τ : ℝ := sourceFullCommonTolerance F C.scale
  let E : ℕ → ℕ → ℝ :=
    bundleRankwiseEnvelopeError α β μ τ
  let D : OrderedPattern.DeletionFamily (G := G) k r :=
    P.sourceFullBadBaseDeletionFamily α β
  have hα : ∀ d, 0 < α d := by
    intro d
    exact sourceBundleRankwiseDensity_pos hδ C.scale d
  have hα_one : ∀ d, α d ≤ 1 := by
    intro d
    exact sourceBundleRankwiseDensity_le_one hδ.le hδ_one C.scale d
  have hβ : ∀ d, 0 ≤ β d := by
    intro d
    exact sourceBundleRankwiseDefect_nonneg δ κ N C.scale d
  have hβ_pos : ∀ d, 0 < β d := by
    intro d
    unfold β sourceBundleRankwiseDefect
    exact sq_pos_of_pos
      (sourceBundleDefectScale_pos hδ hκ N _)
  have hτ : 0 ≤ τ := by
    exact (sourceFullCommonTolerance_pos F C.scale).le
  have hscale : Antitone C.scale := C.scale_antitone
  have henvelopeRaw :=
    sourceBundleRankwiseEnvelope_and_error_lt_half
      (r := r) (edgeBound := edgeBound) (Q := Q)
      hδ hδ_one hκ hstep.le hκ_step hκ_sq
      (by
        simpa [step, N, edgeBound, sourceBundleRemovalHorizon] using
          sourceBundleRemovalStep_total_le_one k r)
      (by
        simpa [step, N, edgeBound, sourceBundleRemovalHorizon] using
          sourceBundleRemovalStep_total_lt_half k r)
      (by simpa [N, edgeBound, sourceBundleRemovalHorizon] using hQ)
      C.scale hscale
  have henvelope : IsBundleCountingEnvelope α β μ τ E := by
    simpa [α, β, μ, τ, E, F, N, edgeBound,
      sourceBundleRemovalHorizon] using henvelopeRaw.1
  have herror : E r edgeBound < 1 / 2 := by
    simpa [α, β, μ, τ, E, F, N, edgeBound,
      sourceBundleRemovalHorizon] using henvelopeRaw.2
  have hregular :
      IsFullyMixedPreliminaryOrderedRegular P (fun _ => τ) := by
    simpa [P, τ] using
      C.isFullyMixedPreliminaryOrderedRegular_common
  have hthreshold :
      c ≤ (1 / 2 : ℝ) *
        (∏ e : PositiveOrderedFace k r, α e.rank) := by
    have hfloor : 0 ≤ sourceBundleDensity δ S.ceiling :=
      (sourceBundleDensity_pos hδ S.ceiling).le
    have hpoint : ∀ e : PositiveOrderedFace k r,
        sourceBundleDensity δ S.ceiling ≤ α e.rank := by
      intro e
      unfold α sourceBundleRankwiseDensity
      apply sourceBundleDensity_antitone hδ.le
      exact
        (hscale (Fin.zero_le _)).trans
          Cbounded.scale_zero_le_ceiling
    have hprod :
        sourceBundleDensity δ S.ceiling ^
            Fintype.card (PositiveOrderedFace k r) ≤
          ∏ e : PositiveOrderedFace k r, α e.rank := by
      calc
        sourceBundleDensity δ S.ceiling ^
              Fintype.card (PositiveOrderedFace k r) =
            ∏ _e : PositiveOrderedFace k r,
              sourceBundleDensity δ S.ceiling := by simp
        _ ≤ ∏ e : PositiveOrderedFace k r, α e.rank := by
          apply Finset.prod_le_prod
          · intro e _he
            exact hfloor
          · intro e _he
            exact hpoint e
    simpa [c, sourceBundleRemovalCountThreshold] using
      (mul_le_mul_of_nonneg_left hprod (by norm_num : (0 : ℝ) ≤ 1 / 2))
  have hgoodCount :
      ∀ A : ClosedOrderedAtomConfiguration G k r P.coarse,
        A.IsSourceFullMixedGood P α β →
          c ≤ fullConfigurationCount A := by
    intro A hgood
    exact hthreshold.trans
      (half_rankwiseDensityProduct_le_fullConfigurationCount_of_rankBound
        P A α β μ τ E hα hα_one hβ hτ hgood hregular
        henvelope (by simpa [edgeBound] using herror))
  have hinitial :
      P.coarse.Refines (orderedPatternInitialComplex H) := by
    simpa [P, initial,
      CoarseTargetOrderedComplexRegularityCertificate.toCoarseFine] using
        C.regularity.coarse_refines_initial
  have hcover : H.IsCover D := by
    exact
      sourceFullBadBaseDeletionFamily_isCover_of_sourceFullMixedGood_count
        (by simpa [r] using hrank) H P hinitial α β c hcount hgoodCount
  refine ⟨D, hcover, ?_⟩
  intro e
  have hbase :=
    P.faceDeletionDensity_sourceFullBadBaseDeletionFamily_le
      α β (fun j => (hα (j + 1)).le) (fun j => hβ_pos (j + 1)) e
  calc
    OrderedPattern.faceDeletionDensity D e ≤
        ∑ q : OrderedPositiveSubface r,
          ((FacePartition.complexity
              (P.coarse.partition q.1.succ (q.2.trans e)) : ℝ) *
                α (q.1.1 + 1) +
            P.coarseUpperFaceAtomEnergyGap q.1 (q.2.trans e) /
                β (q.1.1 + 1)) := by
      simpa [D] using hbase
    _ ≤ ∑ _q : OrderedPositiveSubface r, (δ + δ) := by
      apply Finset.sum_le_sum
      intro q _hq
      have hd : q.1.1 + 1 ≤ r := by omega
      have hselected :
          sourceBundleSelectedScale C.scale (q.1.1 + 1) =
            C.scale q.1.succ := by
        calc
          sourceBundleSelectedScale C.scale (q.1.1 + 1) =
              C.scale
                ⟨q.1.1 + 1, Nat.lt_succ_iff.mpr hd⟩ :=
            sourceBundleSelectedScale_of_le C.scale hd
          _ = C.scale q.1.succ := by
            apply congrArg C.scale
            exact Fin.ext rfl
      have hcomplexity :
          FacePartition.complexity
              (P.coarse.partition q.1.succ (q.2.trans e)) ≤
            C.scale q.1.succ := by
        simpa [P,
          CoarseTargetOrderedComplexRegularityCertificate.toCoarseFine] using
          C.coarse_complexity q.1.succ (q.2.trans e)
      have hlow :
          (FacePartition.complexity
              (P.coarse.partition q.1.succ (q.2.trans e)) : ℝ) *
                α (q.1.1 + 1) ≤ δ := by
        calc
          (FacePartition.complexity
                (P.coarse.partition q.1.succ (q.2.trans e)) : ℝ) *
                  α (q.1.1 + 1) ≤
              (C.scale q.1.succ : ℝ) * α (q.1.1 + 1) :=
            mul_le_mul_of_nonneg_right
              (Nat.cast_le.mpr hcomplexity) (hα _).le
          _ = (C.scale q.1.succ : ℝ) *
                sourceBundleDensity δ (C.scale q.1.succ) := by
            simp [α, sourceBundleRankwiseDensity, hselected]
          _ ≤ δ := mul_sourceBundleDensity_le hδ.le _
      have hfaceLayer :
          P.coarseUpperFaceAtomEnergyGap q.1 (q.2.trans e) ≤
            P.coarseUpperLayerAtomEnergyGap q.1 := by
        rw [P.coarseUpperLayerAtomEnergyGap_eq_sum_face q.1]
        exact Finset.single_le_sum
          (fun f _ => P.coarseUpperFaceAtomEnergyGap_nonneg q.1 f)
          (Finset.mem_univ (q.2.trans e))
      have hlayer :
          P.coarseUpperLayerAtomEnergyGap q.1 ≤
            sourceFullRankGap F C.scale q.1 := by
        simpa [P] using C.rank_gap_le q.1
      have hdefect :
          P.coarseUpperFaceAtomEnergyGap q.1 (q.2.trans e) /
                β (q.1.1 + 1) ≤ δ := by
        calc
          P.coarseUpperFaceAtomEnergyGap q.1 (q.2.trans e) /
                β (q.1.1 + 1) ≤
              sourceFullRankGap F C.scale q.1 /
                β (q.1.1 + 1) :=
            div_le_div_of_nonneg_right
              (hfaceLayer.trans hlayer) (hβ _)
          _ =
              (1 /
                  (sourceBundleRemovalGrowth Q N
                    (C.scale q.1.succ) : ℝ) ^ 2) /
                sourceBundleDefectScale δ κ N
                    (C.scale q.1.succ) ^ 2 := by
            simp [F, sourceFullRankGap, β,
              sourceBundleRankwiseDefect, hselected]
          _ ≤ δ :=
            sourceFullRankGap_div_sourceBundleDefectScale_sq_le
              hδ hκ hQ (C.scale q.1.succ)
      exact add_le_add hlow hdefect
    _ = (Fintype.card (OrderedPositiveSubface r) : ℝ) *
          (δ + δ) := by
      simp [mul_add]
    _ ≤ ε := by
      simpa [δ, r] using
        card_mul_two_sourceBundleRemovalDensityBudget_le hε (n + 1)

end Wikipedia.SzemeredisTheorem
