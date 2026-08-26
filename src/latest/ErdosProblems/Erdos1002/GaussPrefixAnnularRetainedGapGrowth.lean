import ErdosProblems.Erdos1002.GaussPrefixAnnularLateRealization

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Growth of the retained midpoint gap

The late prefix--future argument uses a natural half-band gap
`⌈rho * H_N⌉₊ / 2`, where `H_N` is the annular depth horizon.  This file
makes two facts explicit:

* for every fixed `rho > 0`, that gap tends to infinity;
* the whole depth horizon is bounded by a fixed natural multiple of one
  plus the gap.

The second assertion is proved pointwise, with the explicit multiplier
`⌈2 / rho⌉₊`; no asymptotic rounding convention is needed.
-/

open Filter Finset
open scoped Topology

namespace Erdos1002

noncomputable section

/-- A positive relative midpoint-band width diverges with the annular
depth horizon. -/
theorem tendsto_annularMidpointBandWidth_atTop
    {rho : ℝ} (hrho : 0 < rho) :
    Tendsto (annularMidpointBandWidth rho) atTop atTop := by
  have hHreal :
      Tendsto
        (fun N : ℕ ↦ (annularDepthAmbientSize N : ℝ))
        atTop atTop :=
    tendsto_natCast_atTop_atTop.comp
      tendsto_annularDepthAmbientSize_atTop
  have hrhoH :
      Tendsto
        (fun N : ℕ ↦ rho * (annularDepthAmbientSize N : ℝ))
        atTop atTop :=
    hHreal.const_mul_atTop hrho
  simpa only [annularMidpointBandWidth] using!
    tendsto_nat_ceil_atTop.comp hrhoH

/-- For fixed positive `rho`, the half-band gap used in every upper
retained realization tends to infinity. -/
theorem tendsto_annularUpperRetainedGap_atTop
    {rho : ℝ} (hrho : 0 < rho) :
    Tendsto (annularUpperRetainedGap rho) atTop atTop := by
  unfold annularUpperRetainedGap midpointPrefixFutureGap
  exact
    (Nat.tendsto_div_const_atTop (by norm_num : (2 : ℕ) ≠ 0)).comp
      (tendsto_annularMidpointBandWidth_atTop hrho)

/-- Exact all-`N` comparison between the complete annular horizon and the
retained gap.  The extra `1` absorbs integer division by two. -/
theorem annularDepthAmbientSize_le_natCeil_two_div_rho_mul_gap_add_one
    {rho : ℝ} (hrho : 0 < rho) (N : ℕ) :
    annularDepthAmbientSize N ≤
      ⌈2 / rho⌉₊ * (annularUpperRetainedGap rho N + 1) := by
  let H : ℕ := annularDepthAmbientSize N
  let W : ℕ := annularMidpointBandWidth rho N
  let G : ℕ := annularUpperRetainedGap rho N
  let D : ℕ := ⌈2 / rho⌉₊
  have hceilW :
      rho * (H : ℝ) ≤ (W : ℝ) := by
    simpa only [W, H, annularMidpointBandWidth] using!
      (Nat.le_ceil
        (rho * (annularDepthAmbientSize N : ℝ)))
  have hHdiv :
      (H : ℝ) ≤ (W : ℝ) / rho := by
    apply (le_div_iff₀ hrho).2
    simpa only [mul_comm] using! hceilW
  have hroundNat : W ≤ 2 * (G + 1) := by
    dsimp only [W, G, annularUpperRetainedGap,
      midpointPrefixFutureGap]
    omega
  have hroundReal : (W : ℝ) ≤ 2 * (G + 1 : ℕ) := by
    exact_mod_cast hroundNat
  have hdivRound :
      (W : ℝ) / rho ≤ (2 / rho) * (G + 1 : ℕ) := by
    apply (div_le_iff₀ hrho).2
    calc
      (W : ℝ) ≤ 2 * (G + 1 : ℕ) := hroundReal
      _ = ((2 / rho) * (G + 1 : ℕ)) * rho := by
        field_simp [ne_of_gt hrho]
  have hceilD : 2 / rho ≤ (D : ℝ) := by
    simpa only [D] using! (Nat.le_ceil (2 / rho))
  have hcoef :
      (2 / rho) * (G + 1 : ℕ) ≤
        (D : ℝ) * (G + 1 : ℕ) :=
    mul_le_mul_of_nonneg_right hceilD (by positivity)
  have hreal :
      (H : ℝ) ≤ (D : ℝ) * (G + 1 : ℕ) :=
    hHdiv.trans (hdivRound.trans hcoef)
  exact_mod_cast hreal

/-- Existential/eventual form used by aggregate mixing estimates.  The
witness can be chosen explicitly as `⌈2 / rho⌉₊`. -/
theorem exists_eventually_annularDepthAmbientSize_le_mul_gap_add_one
    {rho : ℝ} (hrho : 0 < rho) :
    ∃ D : ℕ, ∀ᶠ N : ℕ in atTop,
      annularDepthAmbientSize N ≤
        D * (annularUpperRetainedGap rho N + 1) := by
  refine ⟨⌈2 / rho⌉₊, ?_⟩
  exact Filter.Eventually.of_forall
    (annularDepthAmbientSize_le_natCeil_two_div_rho_mul_gap_add_one hrho)

/-! ## The lower/upper split is genuinely disjoint at positive width -/

/-- At positive band width, a later depth cannot lie simultaneously on
the lower and upper retained half-lines. -/
theorem disjoint_laterLowerMidpointNatTupleFamily_laterUpper
    {r : ℕ} (centerIndex : Fin r) (H W : ℕ) (hW : 0 < W)
    (tuples : Finset (Fin r → ℕ)) :
    Disjoint
      (laterLowerMidpointNatTupleFamily centerIndex H W tuples)
      (laterUpperMidpointNatTupleFamily centerIndex H W tuples) := by
  rw [Finset.disjoint_left]
  intro t htLower htUpper
  have hlower :=
    (mem_laterLowerMidpointNatTupleFamily_iff.mp htLower).2.2
  obtain ⟨j, hj, hupper⟩ :=
    (mem_laterUpperMidpointNatTupleFamily_iff.mp htUpper).2.2
  have hjLower := hlower j hj
  omega

/-- Hence the annular early/late split is disjoint whenever its natural
band width is positive. -/
theorem disjoint_annularCanonicalLaterLower_upper
    {rho : ℝ} {N grid : ℕ}
    (k : AnnularGridIndex grid → ℕ)
    (hr : 0 < MixedOccurrenceCount k)
    (e : Fin (MixedOccurrenceCount k) ≃
      GaussPrefixMixedOccurrence k)
    (mode : Fin (MixedOccurrenceCount k) → ℤ)
    (hmode : mode ≠ 0)
    (hW : 0 < annularMidpointBandWidth rho N) :
    Disjoint
      (annularCanonicalLaterLowerMidpointTupleFamily
        rho N k hr e mode hmode)
      (annularCanonicalLaterUpperMidpointTupleFamily
        rho N k hr e mode hmode) := by
  exact
    disjoint_laterLowerMidpointNatTupleFamily_laterUpper
      (annularLastNonzeroIndex mode hmode)
      (annularDepthAmbientSize N)
      (annularMidpointBandWidth rho N) hW
      (interiorSeparatedCanonicalAnnularGridTupleFamily N k hr e)

/-- Positive relative width makes the annular lower/upper union a
disjoint union for all sufficiently large `N`. -/
theorem eventually_disjoint_annularCanonicalLaterLower_upper
    {rho : ℝ} (hrho : 0 < rho) {grid : ℕ}
    (k : AnnularGridIndex grid → ℕ)
    (hr : 0 < MixedOccurrenceCount k)
    (e : Fin (MixedOccurrenceCount k) ≃
      GaussPrefixMixedOccurrence k)
    (mode : Fin (MixedOccurrenceCount k) → ℤ)
    (hmode : mode ≠ 0) :
    ∀ᶠ N : ℕ in atTop,
      Disjoint
        (annularCanonicalLaterLowerMidpointTupleFamily
          rho N k hr e mode hmode)
        (annularCanonicalLaterUpperMidpointTupleFamily
          rho N k hr e mode hmode) := by
  filter_upwards
    [(tendsto_annularMidpointBandWidth_atTop hrho).eventually_gt_atTop 0]
      with N hW
  exact disjoint_annularCanonicalLaterLower_upper
    k hr e mode hmode hW

end

end Erdos1002
