import Wikipedia.SzemeredisTheorem.Hypergraph.SourceFullCoarseTargetRegularity
import Wikipedia.SzemeredisTheorem.Hypergraph.HypergraphBundleEnvelopeSelection
import Wikipedia.SzemeredisTheorem.Hypergraph.RankwiseBundleEnvelopeSelection

/-!
# Ambient-independent source-full bundle-removal parameters

This file packages two pieces of the final numerical diagonal.

* `sourceBundleDensity δ m = δ / (m + 1)` pays for a coarse upper
  partition of complexity at most `m` without choosing a global complexity
  window.
* `sourceBundleDefectScale δ η N m = η * sourceBundleDensity δ m ^ N`
  is small relative to every density power up to the fixed finite bundle
  horizon `N`.

The polynomial growth function

```
F(m) = Q * (m + 1)^N + (m + 1)
```

then makes both the common preliminary-regularity tolerance and the
rankwise source energy gaps small at the *same selected scale*.  This is the
pointwise choice which removes the apparent global complexity fixed point.

The last section retains the uniform ceiling supplied by
`SourceFullCoarseTargetSchedule.Bounded` when realizing the numerical plan
over an ambient finite type.  The older `certificate_nonempty` theorem
forgets the landing and hence cannot expose this ceiling to the uniform
count threshold.
-/

namespace Wikipedia.SzemeredisTheorem

open scoped BigOperators

/-! ## Scale-dependent density and defect parameters -/

/-- Density threshold attached to a coarse complexity scale. -/
noncomputable def sourceBundleDensity (δ : ℝ) (m : ℕ) : ℝ :=
  δ / (m + 1 : ℕ)

/-- Square-root defect threshold attached to the same scale. -/
noncomputable def sourceBundleDefectScale
    (δ η : ℝ) (N m : ℕ) : ℝ :=
  η * sourceBundleDensity δ m ^ N

theorem sourceBundleDensity_pos
    {δ : ℝ} (hδ : 0 < δ) (m : ℕ) :
    0 < sourceBundleDensity δ m := by
  unfold sourceBundleDensity
  positivity

theorem sourceBundleDensity_nonneg
    {δ : ℝ} (hδ : 0 ≤ δ) (m : ℕ) :
    0 ≤ sourceBundleDensity δ m := by
  unfold sourceBundleDensity
  positivity

theorem sourceBundleDensity_le_one
    {δ : ℝ} (hδ : δ ≤ 1) (hδ0 : 0 ≤ δ) (m : ℕ) :
    sourceBundleDensity δ m ≤ 1 := by
  unfold sourceBundleDensity
  have hden : (1 : ℝ) ≤ (m + 1 : ℕ) := by
    exact_mod_cast Nat.succ_le_succ (Nat.zero_le m)
  exact (div_le_self hδ0 hden).trans hδ

theorem sourceBundleDensity_antitone
    {δ : ℝ} (hδ : 0 ≤ δ) :
    Antitone (sourceBundleDensity δ) := by
  intro a b hab
  unfold sourceBundleDensity
  apply div_le_div_of_nonneg_left hδ
  · positivity
  · exact_mod_cast Nat.add_le_add_right hab 1

/-- The low-density cleaning term at scale `m` costs at most `δ`. -/
theorem mul_sourceBundleDensity_le
    {δ : ℝ} (hδ : 0 ≤ δ) (m : ℕ) :
    (m : ℝ) * sourceBundleDensity δ m ≤ δ := by
  unfold sourceBundleDensity
  have hden : (0 : ℝ) < (m + 1 : ℕ) := by positivity
  calc
    (m : ℝ) * (δ / (m + 1 : ℕ)) =
        δ * ((m : ℝ) / (m + 1 : ℕ)) := by ring
    _ ≤ δ * 1 := by
      apply mul_le_mul_of_nonneg_left _ hδ
      exact (div_le_one hden).2 (by norm_num)
    _ = δ := mul_one δ

theorem sourceBundleDefectScale_pos
    {δ η : ℝ} (hδ : 0 < δ) (hη : 0 < η)
    (N m : ℕ) :
    0 < sourceBundleDefectScale δ η N m := by
  unfold sourceBundleDefectScale
  exact mul_pos hη (pow_pos (sourceBundleDensity_pos hδ m) N)

theorem sourceBundleDefectScale_nonneg
    {δ η : ℝ} (hδ : 0 ≤ δ) (hη : 0 ≤ η)
    (N m : ℕ) :
    0 ≤ sourceBundleDefectScale δ η N m := by
  unfold sourceBundleDefectScale
  exact mul_nonneg hη
    (pow_nonneg (sourceBundleDensity_nonneg hδ m) N)

/-! ## Rankwise schedules attached to a selected scale hierarchy -/

/-- Extend a finite selected scale hierarchy to all natural ranks by
clamping at its deepest rank.  Bundle-counting envelopes are indexed by
all naturals even though source-full configurations only query ranks at
most `r`. -/
def sourceBundleSelectedScale
    {r : ℕ} (scale : Fin (r + 1) → ℕ) (d : ℕ) : ℕ :=
  scale ⟨min d r, Nat.lt_succ_iff.mpr (Nat.min_le_right d r)⟩

@[simp]
theorem sourceBundleSelectedScale_zero
    {r : ℕ} (scale : Fin (r + 1) → ℕ) :
    sourceBundleSelectedScale scale 0 = scale 0 := by
  simp [sourceBundleSelectedScale]

theorem sourceBundleSelectedScale_of_le
    {r d : ℕ} (scale : Fin (r + 1) → ℕ) (hd : d ≤ r) :
    sourceBundleSelectedScale scale d =
      scale ⟨d, Nat.lt_succ_iff.mpr hd⟩ := by
  simp [sourceBundleSelectedScale, Nat.min_eq_left hd]

/-- The density schedule obtained by evaluating `sourceBundleDensity` at
the selected scale of each rank. -/
noncomputable def sourceBundleRankwiseDensity
    {r : ℕ} (δ : ℝ) (scale : Fin (r + 1) → ℕ) (d : ℕ) : ℝ :=
  sourceBundleDensity δ (sourceBundleSelectedScale scale d)

/-- The squared localized-defect schedule paired with the selected
rankwise density schedule. -/
noncomputable def sourceBundleRankwiseDefect
    {r : ℕ} (δ κ : ℝ) (N : ℕ)
    (scale : Fin (r + 1) → ℕ) (d : ℕ) : ℝ :=
  sourceBundleDefectScale δ κ N
      (sourceBundleSelectedScale scale d) ^ 2

theorem sourceBundleRankwiseDensity_pos
    {r : ℕ} {δ : ℝ} (hδ : 0 < δ)
    (scale : Fin (r + 1) → ℕ) (d : ℕ) :
    0 < sourceBundleRankwiseDensity δ scale d :=
  sourceBundleDensity_pos hδ _

theorem sourceBundleRankwiseDensity_le_one
    {r : ℕ} {δ : ℝ} (hδ : 0 ≤ δ) (hδ_one : δ ≤ 1)
    (scale : Fin (r + 1) → ℕ) (d : ℕ) :
    sourceBundleRankwiseDensity δ scale d ≤ 1 :=
  sourceBundleDensity_le_one hδ_one hδ _

theorem sourceBundleRankwiseDefect_nonneg
    {r : ℕ} (δ κ : ℝ) (N : ℕ)
    (scale : Fin (r + 1) → ℕ) (d : ℕ) :
    0 ≤ sourceBundleRankwiseDefect δ κ N scale d :=
  sq_nonneg _

/-- Antitonicity of the selected scales makes rank zero the least density
in the extended rankwise density schedule. -/
theorem sourceBundleRankwiseDensity_zero_le
    {r : ℕ} {δ : ℝ} (hδ : 0 ≤ δ)
    {scale : Fin (r + 1) → ℕ} (hscale : Antitone scale)
    (d : ℕ) :
    sourceBundleRankwiseDensity δ scale 0 ≤
      sourceBundleRankwiseDensity δ scale d := by
  apply sourceBundleDensity_antitone hδ
  exact hscale (Fin.zero_le _)

/-- If the zeroth entry is a lower bound for a schedule, it is also a
lower bound for every finite prefix minimum. -/
theorem le_bundleRankwiseDensityFloor_of_zero_le
    {α : ℕ → ℝ} (hα : ∀ d, α 0 ≤ α d) :
    ∀ d, α 0 ≤ bundleRankwiseDensityFloor α d := by
  intro d
  induction d with
  | zero => exact le_rfl
  | succ d ih =>
      rw [bundleRankwiseDensityFloor_succ]
      exact le_min ih (hα (d + 1))

/-! ## Polynomial pointwise growth -/

/-- A monotone growth function which dominates `Q * (m + 1)^N` at every
scale. -/
def sourceBundleRemovalGrowth (Q N : ℕ) : NatGrowthFunction where
  toFun m := Q * (m + 1) ^ N + (m + 1)
  monotone' := by
    intro a b hab
    apply Nat.add_le_add
    · exact Nat.mul_le_mul_left Q
        (Nat.pow_le_pow_left (Nat.add_le_add_right hab 1) N)
    · exact Nat.add_le_add_right hab 1
  above_diagonal := by
    intro m
    exact (Nat.le_add_left (m + 1) (Q * (m + 1) ^ N))

@[simp]
theorem sourceBundleRemovalGrowth_apply
    (Q N m : ℕ) :
    sourceBundleRemovalGrowth Q N m =
      Q * (m + 1) ^ N + (m + 1) :=
  rfl

theorem sourceBundleRemovalGrowth_polynomial_le
    (Q N m : ℕ) :
    Q * (m + 1) ^ N ≤ sourceBundleRemovalGrowth Q N m := by
  rw [sourceBundleRemovalGrowth_apply]
  exact Nat.le_add_right _ _

/-- The two scalar inequalities required of the polynomial coefficient.
The first pays for the normalized frozen-uniformity term and the second for
the source energy-gap cleaning term. -/
structure SourceBundleRemovalGrowthConditions
    (δ η : ℝ) (N Q : ℕ) : Prop where
  uniform :
    1 ≤ (Q : ℝ) * η ^ 2 * δ ^ N
  gap :
    1 ≤ δ * (Q : ℝ) ^ 2 * η ^ 2 * δ ^ (2 * N)

/-- A natural polynomial coefficient satisfying both source-bundle
inequalities exists for every pair of positive real parameters. -/
theorem exists_sourceBundleRemovalGrowthCoefficient
    {δ η : ℝ} (hδ : 0 < δ) (hδ_one : δ ≤ 1)
    (hη : 0 < η) (_hη_one : η ≤ 1) (N : ℕ) :
    ∃ Q : ℕ,
      SourceBundleRemovalGrowthConditions δ η N Q := by
  let x : ℝ := η ^ 2 * δ ^ (2 * N + 1)
  have hx : 0 < x := by
    dsimp [x]
    positivity
  obtain ⟨Q, hQ⟩ := exists_nat_gt (1 / x)
  have hQpos : 0 < (Q : ℝ) := (div_pos one_pos hx).trans hQ
  have hQone : (1 : ℝ) ≤ Q := by
    exact_mod_cast (Nat.one_le_iff_ne_zero.mpr
      (by exact_mod_cast ne_of_gt hQpos))
  have hQx : 1 < (Q : ℝ) * x := by
    calc
      1 = (1 / x) * x := by field_simp
      _ < (Q : ℝ) * x := mul_lt_mul_of_pos_right hQ hx
  refine ⟨Q, ?_, ?_⟩
  · have hpow : δ ^ (2 * N + 1) ≤ δ ^ N := by
      exact pow_le_pow_of_le_one hδ.le hδ_one (by omega)
    calc
      1 ≤ (Q : ℝ) * x := hQx.le
      _ ≤ (Q : ℝ) * η ^ 2 * δ ^ N := by
        dsimp [x]
        simpa [mul_assoc] using
          (mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left hpow (sq_nonneg η))
            hQpos.le)
  · calc
      1 ≤ (Q : ℝ) * x := hQx.le
      _ ≤ (Q : ℝ) * ((Q : ℝ) * x) := by
        simpa only [one_mul] using
          (mul_le_mul_of_nonneg_right hQone
            (mul_nonneg hQpos.le hx.le))
      _ = δ * (Q : ℝ) ^ 2 * η ^ 2 * δ ^ (2 * N) := by
        dsimp [x]
        ring

/-- The polynomial growth value makes the common reciprocal tolerance at
scale `m` no larger than the normalized finite-horizon target. -/
theorem one_div_sourceBundleRemovalGrowth_le
    {δ η : ℝ} {N Q : ℕ}
    (hδ : 0 < δ) (hη : 0 < η)
    (hQ : SourceBundleRemovalGrowthConditions δ η N Q)
    (m : ℕ) :
    1 / (sourceBundleRemovalGrowth Q N m : ℝ) ≤
      η ^ 2 * sourceBundleDensity δ m ^ N := by
  have hx : (0 : ℝ) < (m + 1 : ℕ) := by positivity
  have hF : (0 : ℝ) < sourceBundleRemovalGrowth Q N m := by
    exact_mod_cast (sourceBundleRemovalGrowth Q N).positive m
  apply (div_le_iff₀ hF).2
  have hpoly :
      (Q : ℝ) * ((m + 1 : ℕ) : ℝ) ^ N ≤
        (sourceBundleRemovalGrowth Q N m : ℕ) := by
    exact_mod_cast sourceBundleRemovalGrowth_polynomial_le Q N m
  calc
    1 ≤ (Q : ℝ) * η ^ 2 * δ ^ N := hQ.uniform
    _ =
        (η ^ 2 * sourceBundleDensity δ m ^ N) *
          ((Q : ℝ) * ((m + 1 : ℕ) : ℝ) ^ N) := by
      unfold sourceBundleDensity
      rw [div_pow]
      field_simp
    _ ≤
        (η ^ 2 * sourceBundleDensity δ m ^ N) *
          (sourceBundleRemovalGrowth Q N m : ℕ) := by
      apply mul_le_mul_of_nonneg_left hpoly
      exact mul_nonneg (sq_nonneg η)
        (pow_nonneg (sourceBundleDensity_nonneg hδ.le m) N)

/-- After division by the scale-dependent squared defect threshold, the
source rank-gap target costs at most `δ`. -/
theorem sourceFullRankGap_div_sourceBundleDefectScale_sq_le
    {δ η : ℝ} {N Q : ℕ}
    (hδ : 0 < δ) (hη : 0 < η)
    (hQ : SourceBundleRemovalGrowthConditions δ η N Q)
    (m : ℕ) :
    (1 / (sourceBundleRemovalGrowth Q N m : ℝ) ^ 2) /
          sourceBundleDefectScale δ η N m ^ 2 ≤
      δ := by
  have hx : (0 : ℝ) < (m + 1 : ℕ) := by positivity
  have hF : (0 : ℝ) < sourceBundleRemovalGrowth Q N m := by
    exact_mod_cast (sourceBundleRemovalGrowth Q N).positive m
  have ht : 0 < sourceBundleDefectScale δ η N m :=
    sourceBundleDefectScale_pos hδ hη N m
  rw [div_le_iff₀ (sq_pos_of_pos ht)]
  rw [div_le_iff₀ (sq_pos_of_pos hF)]
  have hpoly :
      (Q : ℝ) * ((m + 1 : ℕ) : ℝ) ^ N ≤
        (sourceBundleRemovalGrowth Q N m : ℕ) := by
    exact_mod_cast sourceBundleRemovalGrowth_polynomial_le Q N m
  have hpolySq :
      ((Q : ℝ) * ((m + 1 : ℕ) : ℝ) ^ N) ^ 2 ≤
        (sourceBundleRemovalGrowth Q N m : ℝ) ^ 2 := by
    exact
      (sq_le_sq₀
        (mul_nonneg (Nat.cast_nonneg Q) (pow_nonneg hx.le N))
        hF.le).2 hpoly
  calc
    1 ≤ δ * (Q : ℝ) ^ 2 * η ^ 2 * δ ^ (2 * N) := hQ.gap
    _ =
        δ * (((Q : ℝ) * ((m + 1 : ℕ) : ℝ) ^ N) ^ 2 *
          sourceBundleDefectScale δ η N m ^ 2) := by
      unfold sourceBundleDefectScale sourceBundleDensity
      rw [div_pow]
      field_simp
      ring
    _ ≤
        δ * ((sourceBundleRemovalGrowth Q N m : ℝ) ^ 2 *
          sourceBundleDefectScale δ η N m ^ 2) := by
      apply mul_le_mul_of_nonneg_left _ hδ.le
      exact mul_le_mul_of_nonneg_right hpolySq (sq_nonneg _)
    _ =
        δ * sourceBundleDefectScale δ η N m ^ 2 *
          (sourceBundleRemovalGrowth Q N m : ℝ) ^ 2 := by
      ring

/-! ## Finite-horizon normalized counting bounds -/

/-- The density-scaled defect is small after normalization by every density
power up to its chosen horizon.  The factor four is the lower-error cap
appearing in the reverse-doubling bundle envelope. -/
theorem sqrt_sourceBundleDefectScale_sq_four_div_pow_le
    {δ κ step : ℝ} {N p m : ℕ}
    (hδ : 0 < δ) (hδ_one : δ ≤ 1)
    (hκ : 0 ≤ κ) (hκ_step : 4 * κ ≤ step)
    (hp : p ≤ N) :
    Real.sqrt
          (sourceBundleDefectScale δ κ N m ^ 2 *
            (1 + (1 : ℝ)) * (1 + (1 : ℝ))) /
        sourceBundleDensity δ m ^ p ≤
      step / 2 := by
  let a := sourceBundleDensity δ m
  let t := sourceBundleDefectScale δ κ N m
  have ha : 0 < a := sourceBundleDensity_pos hδ m
  have ha_one : a ≤ 1 :=
    sourceBundleDensity_le_one hδ_one hδ.le m
  have ht : 0 ≤ t :=
    sourceBundleDefectScale_nonneg hδ.le hκ N m
  have hpow : a ^ N ≤ a ^ p :=
    pow_le_pow_of_le_one ha.le ha_one hp
  have hsqrt :
      Real.sqrt (t ^ 2 * (1 + (1 : ℝ)) * (1 + (1 : ℝ))) =
        2 * t := by
    rw [show
      t ^ 2 * (1 + (1 : ℝ)) * (1 + (1 : ℝ)) =
        (2 * t) ^ 2 by ring]
    exact Real.sqrt_sq (mul_nonneg (by norm_num) ht)
  rw [show sourceBundleDefectScale δ κ N m = t by rfl,
    show sourceBundleDensity δ m = a by rfl, hsqrt]
  have hnormalized : 2 * t / a ^ p ≤ 2 * κ := by
    apply (div_le_iff₀ (pow_pos ha p)).2
    calc
      2 * t = (2 * κ) * a ^ N := by
        dsimp [t, a, sourceBundleDefectScale]
        ring
      _ ≤ (2 * κ) * a ^ p :=
        mul_le_mul_of_nonneg_left hpow (by positivity)
  exact hnormalized.trans (by linarith)

/-- A tolerance bounded by `κ² a^N` remains at most `κ²` after
normalization by any larger density floor to a power at most `N`. -/
theorem div_pow_le_sq_of_le_scaled_pow
    {τ κ a μ : ℝ} {p N : ℕ}
    (ha : 0 < a) (ha_one : a ≤ 1) (haμ : a ≤ μ)
    (hτ : τ ≤ κ ^ 2 * a ^ N) (hp : p ≤ N) :
    τ / μ ^ p ≤ κ ^ 2 := by
  have hμ : 0 < μ := ha.trans_le haμ
  have hpow₁ : a ^ N ≤ a ^ p :=
    pow_le_pow_of_le_one ha.le ha_one hp
  have hpow₂ : a ^ p ≤ μ ^ p :=
    pow_le_pow_left₀ ha.le haμ p
  apply (div_le_iff₀ (pow_pos hμ p)).2
  exact hτ.trans
    (mul_le_mul_of_nonneg_left (hpow₁.trans hpow₂) (sq_nonneg κ))

/-- The explicit source-full hierarchy, viewed just as a selected scale
array, feeds the reverse-doubling bundle envelope.  All hypotheses are
scalar and ambient-independent. -/
theorem sourceBundleRankwiseEnvelope_and_error_lt_half
    {r edgeBound Q : ℕ} {δ κ step : ℝ}
    (hδ : 0 < δ) (hδ_one : δ ≤ 1)
    (hκ : 0 < κ) (hstep : 0 ≤ step)
    (hκ_step : 4 * κ ≤ step)
    (hκ_sq : κ ^ 2 ≤ step / 2)
    (hcap :
      (r : ℝ) *
          (bundleReverseDoublingHorizon r edgeBound 0 : ℝ) * step ≤ 1)
    (hfinal :
      (r : ℝ) *
          (bundleReverseDoublingHorizon r edgeBound 0 : ℝ) * step < 1 / 2)
    (hQ : SourceBundleRemovalGrowthConditions δ κ
      (bundleReverseDoublingHorizon r edgeBound 0) Q)
    (scale : Fin (r + 1) → ℕ) (hscale : Antitone scale) :
    IsBundleCountingEnvelope
        (sourceBundleRankwiseDensity δ scale)
        (sourceBundleRankwiseDefect δ κ
          (bundleReverseDoublingHorizon r edgeBound 0) scale)
        (bundleRankwiseDensityFloor
          (sourceBundleRankwiseDensity δ scale))
        (sourceFullCommonTolerance
          (sourceBundleRemovalGrowth Q
            (bundleReverseDoublingHorizon r edgeBound 0)) scale)
        (bundleRankwiseEnvelopeError
          (sourceBundleRankwiseDensity δ scale)
          (sourceBundleRankwiseDefect δ κ
            (bundleReverseDoublingHorizon r edgeBound 0) scale)
          (bundleRankwiseDensityFloor
            (sourceBundleRankwiseDensity δ scale))
          (sourceFullCommonTolerance
            (sourceBundleRemovalGrowth Q
              (bundleReverseDoublingHorizon r edgeBound 0)) scale)) ∧
      bundleRankwiseEnvelopeError
          (sourceBundleRankwiseDensity δ scale)
          (sourceBundleRankwiseDefect δ κ
            (bundleReverseDoublingHorizon r edgeBound 0) scale)
          (bundleRankwiseDensityFloor
            (sourceBundleRankwiseDensity δ scale))
          (sourceFullCommonTolerance
            (sourceBundleRemovalGrowth Q
              (bundleReverseDoublingHorizon r edgeBound 0)) scale)
          r edgeBound < 1 / 2 := by
  let N := bundleReverseDoublingHorizon r edgeBound 0
  let α := sourceBundleRankwiseDensity δ scale
  let β := sourceBundleRankwiseDefect δ κ N scale
  let μ := bundleRankwiseDensityFloor α
  let τ := sourceFullCommonTolerance
    (sourceBundleRemovalGrowth Q N) scale
  have hα : ∀ d, 0 < α d := by
    intro d
    exact sourceBundleRankwiseDensity_pos hδ scale d
  have hα_one : ∀ d, α d ≤ 1 := by
    intro d
    exact sourceBundleRankwiseDensity_le_one hδ.le hδ_one scale d
  have hβ : ∀ d, 0 ≤ β d := by
    intro d
    exact sourceBundleRankwiseDefect_nonneg δ κ N scale d
  have hτ : 0 ≤ τ := by
    exact (sourceFullCommonTolerance_pos
      (sourceBundleRemovalGrowth Q N) scale).le
  have hαzero : ∀ d, α 0 ≤ α d := by
    intro d
    exact sourceBundleRankwiseDensity_zero_le hδ.le hscale d
  have hfinitePower :
      ∀ d, d < r → ∀ n,
        n < bundleReverseDoublingHorizon r edgeBound (d + 1) →
          n + 1 ≤ N := by
    intro d _hd n hn
    have hhorizon :=
      bundleReverseDoublingHorizon_le_zero r edgeBound (d + 1)
    dsimp only [N]
    omega
  apply
    (bundleRankwiseEnvelope_and_error_lt_half_of_reverseDoublingBudget
      hα hα_one hβ hτ hstep r edgeBound hcap hfinal)
  · intro d hd n hn
    have hp := hfinitePower d hd n hn
    simpa only [α, β, N, sourceBundleRankwiseDefect,
      sourceBundleRankwiseDensity] using
      (sqrt_sourceBundleDefectScale_sq_four_div_pow_le
        hδ hδ_one hκ.le hκ_step hp)
  · intro d hd n hn
    have hp := hfinitePower d hd n hn
    have ha0 : 0 < α 0 := hα 0
    have ha0_one : α 0 ≤ 1 := hα_one 0
    have ha0μ : α 0 ≤ μ (d + 1) :=
      le_bundleRankwiseDensityFloor_of_zero_le hαzero (d + 1)
    have hτscaled : τ ≤ κ ^ 2 * (α 0) ^ N := by
      simpa only [τ, α, N, sourceFullCommonTolerance,
        sourceBundleRankwiseDensity, sourceBundleSelectedScale_zero] using
        (one_div_sourceBundleRemovalGrowth_le hδ hκ hQ (scale 0))
    exact
      (div_pow_le_sq_of_le_scaled_pow
        ha0 ha0_one ha0μ hτscaled hp).trans hκ_sq

namespace SourceFullCoarseTargetSchedule.Certificate

/-- The scale hierarchy stored in a realized source-full certificate is
antitone. -/
theorem scale_antitone
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    {initial : OrderedPartitionComplex G k r}
    {initialBound : Fin (r + 1) → ℕ}
    {F : NatGrowthFunction}
    {scaleFloor : ℕ}
    (C : SourceFullCoarseTargetSchedule.Certificate
      k r initial initialBound F scaleFloor) :
    Antitone C.scale := by
  rw [Fin.antitone_iff_succ_le]
  intro j
  exact
    (Nat.le_succ _).trans
      ((F.above_diagonal (C.scale j.succ)).trans
        (C.scale_hierarchy j))

end SourceFullCoarseTargetSchedule.Certificate

/-! ## A bounded realized certificate -/

namespace SourceFullCoarseTargetSchedule.Bounded

/-- A realized source-full certificate which remembers the numerical
ceiling of the ambient-independent bounded plan. -/
structure Certificate
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    {initialBound : Fin (r + 1) → ℕ}
    {F : NatGrowthFunction}
    {scaleFloor : ℕ}
    (S : SourceFullCoarseTargetSchedule.Bounded
      k r initialBound F scaleFloor)
    (initial : OrderedPartitionComplex G k r) where
  toSourceFull :
    SourceFullCoarseTargetSchedule.Certificate
      k r initial initialBound F scaleFloor
  scale_zero_le_ceiling : toSourceFull.scale 0 ≤ S.ceiling

/-- Realize a bounded numerical plan while retaining its landing-independent
ceiling. -/
theorem certificate_nonempty
    {G : Type*} [Fintype G] [DecidableEq G] [Nonempty G]
    {k r : ℕ}
    {initialBound : Fin (r + 1) → ℕ}
    {F : NatGrowthFunction}
    {scaleFloor : ℕ}
    (S : SourceFullCoarseTargetSchedule.Bounded
      k r initialBound F scaleFloor)
    (initial : OrderedPartitionComplex G k r)
    (hinitial :
      ∀ (q : Fin (r + 1)) (e : OrderedFace k q.1),
        FacePartition.complexity
            (initial.partition q e) ≤
          initialBound q) :
    Nonempty (Certificate S initial) := by
  obtain ⟨P, R, hindex⟩ :=
    S.plan.schedule.exists_landing_certificate
      initial S.plan.schedule_admissible
  let C : SourceFullCoarseTargetSchedule.Certificate
      k r initial initialBound F scaleFloor :=
    { tolerance := P.tolerance
      budget := P.budget
      length := P.length
      regularity := R
      scale := S.plan.scale P
      scaleFloor_le := S.plan.scaleFloor_le P
      scale_hierarchy := S.plan.scale_hierarchy P
      selected_tolerance_nonneg := by
        intro j
        simp only [selectedOrderedComplexTolerance]
        rw [congrFun hindex j]
        exact
          P.tolerance_nonneg S.plan.schedule_admissible
            j (P.index j)
      selected_tolerance_le_common := by
        intro j
        simpa [selectedOrderedComplexTolerance, hindex] using
          S.plan.selected_tolerance_le_common P j
      rank_gap_le := by
        intro j
        have hgap := R.gap_le j
        have hreciprocal := S.plan.reciprocal_gap_le P j
        change
          orderedLayerAtomEnergy
                (R.fine.partition j.castSucc)
                (R.coarse.partition j.succ) -
              orderedLayerAtomEnergy
                (R.coarse.partition j.castSucc)
                (R.coarse.partition j.succ) ≤
            sourceFullRankGap F (S.plan.scale P) j
        exact hgap.trans hreciprocal
      coarse_complexity := by
        intro q
        cases q using Fin.lastCases with
        | last =>
            intro e
            have htop := congrFun R.coarse_topLayer_eq e
            simp only [OrderedPartitionComplex.topLayer] at htop
            rw [htop]
            calc
              FacePartition.complexity
                    (initial.partition (Fin.last r) e) ≤
                  initialBound (Fin.last r) :=
                hinitial (Fin.last r) e
              _ = adaptiveSelectedCoarseLayerBound
                    initialBound P (Fin.last r) := by
                simp [adaptiveSelectedCoarseLayerBound]
              _ ≤ S.plan.scale P (Fin.last r) :=
                S.plan.selected_coarse_bound P (Fin.last r)
        | cast j =>
            intro e
            calc
              FacePartition.complexity
                    (R.coarse.partition j.castSucc e) ≤
                  fixedUpperLayerComplexityFactor
                        j.1 (P.budget j) (P.index j) *
                    FacePartition.complexity
                        (initial.partition j.castSucc e) := by
                rw [← congrFun hindex j]
                exact R.coarse_complexity j e
              _ ≤ fixedUpperLayerComplexityFactor
                        j.1 (P.budget j) (P.index j) *
                    initialBound j.castSucc :=
                Nat.mul_le_mul_left _ (hinitial j.castSucc e)
              _ = adaptiveSelectedCoarseLayerBound
                    initialBound P j.castSucc := by
                simp [adaptiveSelectedCoarseLayerBound]
              _ ≤ S.plan.scale P j.castSucc :=
                S.plan.selected_coarse_bound P j.castSucc }
  exact ⟨⟨C, S.scale_zero_le P⟩⟩

end SourceFullCoarseTargetSchedule.Bounded

end Wikipedia.SzemeredisTheorem
