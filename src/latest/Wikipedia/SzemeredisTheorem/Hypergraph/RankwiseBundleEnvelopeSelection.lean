import Wikipedia.SzemeredisTheorem.Hypergraph.HypergraphBundleEnvelopeSelection

/-!
# Rankwise numerical envelopes for bundle counting

The generalized bundle-counting recurrence permits the density and
localized-defect parameters to depend on the rank.  This file supplies a
direct numerical envelope for those rankwise parameters.  Its density floor
is the prefix minimum of the rankwise densities, so no global density lower
bound is needed.

The row constructor takes a maximum with the preceding-order row.  This
makes monotonicity in bundle order automatic even when consecutive ranks use
unrelated parameters; its other branch is equality in the one-edge counting
recurrence.
-/

namespace Wikipedia.SzemeredisTheorem

open Filter Topology

/-! ## Prefix density floors -/

/-- The least density encountered through rank `d`, written recursively so
that no finite-set choice is involved. -/
def bundleRankwiseDensityFloor (α : ℕ → ℝ) : ℕ → ℝ
  | 0 => α 0
  | d + 1 => min (bundleRankwiseDensityFloor α d) (α (d + 1))

@[simp]
theorem bundleRankwiseDensityFloor_zero (α : ℕ → ℝ) :
    bundleRankwiseDensityFloor α 0 = α 0 :=
  rfl

@[simp]
theorem bundleRankwiseDensityFloor_succ (α : ℕ → ℝ) (d : ℕ) :
    bundleRankwiseDensityFloor α (d + 1) =
      min (bundleRankwiseDensityFloor α d) (α (d + 1)) :=
  rfl

/-- A positive rankwise density schedule has positive prefix floors. -/
theorem bundleRankwiseDensityFloor_pos
    {α : ℕ → ℝ} (hα : ∀ d, 0 < α d) :
    ∀ d, 0 < bundleRankwiseDensityFloor α d := by
  intro d
  induction d with
  | zero => simpa using hα 0
  | succ d ih =>
      simpa using lt_min ih (hα (d + 1))

/-- The prefix floor at `d` lies below every density of rank at most `d`. -/
theorem bundleRankwiseDensityFloor_le
    (α : ℕ → ℝ) {i d : ℕ} (hid : i ≤ d) :
    bundleRankwiseDensityFloor α d ≤ α i := by
  induction d with
  | zero =>
      have hi : i = 0 := Nat.eq_zero_of_le_zero hid
      subst i
      exact le_rfl
  | succ d ih =>
      rw [bundleRankwiseDensityFloor_succ]
      by_cases hi : i = d + 1
      · subst i
        exact min_le_right _ _
      · exact (min_le_left _ _).trans (ih (Nat.le_of_lt_succ (lt_of_le_of_ne hid hi)))

/-- Prefix floors decrease as the permitted rank increases. -/
theorem bundleRankwiseDensityFloor_antitone (α : ℕ → ℝ) :
    Antitone (bundleRankwiseDensityFloor α) := by
  apply antitone_nat_of_succ_le
  intro d
  rw [bundleRankwiseDensityFloor_succ]
  exact min_le_left _ _

/-! ## The rankwise recurrence -/

/-- The rank-`d + 1` contribution from adjoining the `(n + 1)`st edge. -/
noncomputable def bundleRankwiseStepIncrement
    (α β μ : ℕ → ℝ) (τ : ℝ)
    (lower : ℕ → ℝ) (d n : ℕ) : ℝ :=
  Real.sqrt
        (β (d + 1) *
          (1 + lower (n + 1)) *
          (1 + lower (2 * (n + 1)))) /
      (α (d + 1)) ^ (n + 1) +
    τ / (μ (d + 1)) ^ (n + 1)

/-- Construct the next error row.  The first branch of the maximum preserves
the preceding-order estimate, while the second absorbs the new counting
increment exactly. -/
noncomputable def bundleRankwiseNextRow
    (α β μ : ℕ → ℝ) (τ : ℝ)
    (d : ℕ) (lower : ℕ → ℝ) : ℕ → ℝ
  | 0 => 0
  | n + 1 =>
      max (lower (n + 1))
        (bundleRankwiseNextRow α β μ τ d lower n +
          bundleRankwiseStepIncrement α β μ τ lower d n)

/-- The rankwise bundle-counting envelope. -/
noncomputable def bundleRankwiseEnvelopeError
    (α β μ : ℕ → ℝ) (τ : ℝ) : ℕ → ℕ → ℝ
  | 0 => fun _ => 0
  | d + 1 =>
      bundleRankwiseNextRow α β μ τ d
        (bundleRankwiseEnvelopeError α β μ τ d)

@[simp]
theorem bundleRankwiseNextRow_zero
    (α β μ : ℕ → ℝ) (τ : ℝ) (d : ℕ) (lower : ℕ → ℝ) :
    bundleRankwiseNextRow α β μ τ d lower 0 = 0 :=
  rfl

@[simp]
theorem bundleRankwiseNextRow_succ
    (α β μ : ℕ → ℝ) (τ : ℝ) (d n : ℕ) (lower : ℕ → ℝ) :
    bundleRankwiseNextRow α β μ τ d lower (n + 1) =
      max (lower (n + 1))
        (bundleRankwiseNextRow α β μ τ d lower n +
          bundleRankwiseStepIncrement α β μ τ lower d n) :=
  rfl

@[simp]
theorem bundleRankwiseEnvelopeError_zero_order
    (α β μ : ℕ → ℝ) (τ : ℝ) (n : ℕ) :
    bundleRankwiseEnvelopeError α β μ τ 0 n = 0 :=
  rfl

@[simp]
theorem bundleRankwiseEnvelopeError_succ_order
    (α β μ : ℕ → ℝ) (τ : ℝ) (d n : ℕ) :
    bundleRankwiseEnvelopeError α β μ τ (d + 1) n =
      bundleRankwiseNextRow α β μ τ d
        (bundleRankwiseEnvelopeError α β μ τ d) n :=
  rfl

/-! ## Positivity and monotonicity -/

theorem bundleRankwiseStepIncrement_nonneg
    {α β μ : ℕ → ℝ} {τ : ℝ}
    (hα : ∀ d, 0 ≤ α d) (hμ : ∀ d, 0 ≤ μ d)
    (hτ : 0 ≤ τ) (lower : ℕ → ℝ) (d n : ℕ) :
    0 ≤ bundleRankwiseStepIncrement α β μ τ lower d n := by
  unfold bundleRankwiseStepIncrement
  exact add_nonneg
    (div_nonneg (Real.sqrt_nonneg _) (pow_nonneg (hα _) _))
    (div_nonneg hτ (pow_nonneg (hμ _) _))

theorem bundleRankwiseNextRow_nonneg
    {α β μ : ℕ → ℝ} {τ : ℝ}
    (hα : ∀ d, 0 ≤ α d) (hμ : ∀ d, 0 ≤ μ d)
    (hτ : 0 ≤ τ) (d : ℕ) (lower : ℕ → ℝ) :
    ∀ n, 0 ≤ bundleRankwiseNextRow α β μ τ d lower n := by
  intro n
  induction n with
  | zero => simp
  | succ n ih =>
      rw [bundleRankwiseNextRow_succ]
      exact le_max_of_le_right
        (add_nonneg ih
          (bundleRankwiseStepIncrement_nonneg hα hμ hτ lower d n))

theorem bundleRankwiseEnvelopeError_nonneg
    {α β μ : ℕ → ℝ} {τ : ℝ}
    (hα : ∀ d, 0 ≤ α d) (hμ : ∀ d, 0 ≤ μ d)
    (hτ : 0 ≤ τ) :
    ∀ d n, 0 ≤ bundleRankwiseEnvelopeError α β μ τ d n := by
  intro d
  induction d with
  | zero =>
      intro n
      simp
  | succ d _ih =>
      intro n
      rw [bundleRankwiseEnvelopeError_succ_order]
      exact bundleRankwiseNextRow_nonneg hα hμ hτ d _ n

@[simp]
theorem bundleRankwiseEnvelopeError_zero_card
    (α β μ : ℕ → ℝ) (τ : ℝ) :
    ∀ d, bundleRankwiseEnvelopeError α β μ τ d 0 = 0 := by
  intro d
  cases d <;> simp

/-- Every rankwise row increases with the number of occurrence edges. -/
theorem bundleRankwiseEnvelopeError_monotone_card
    {α β μ : ℕ → ℝ} {τ : ℝ}
    (hα : ∀ d, 0 ≤ α d) (hμ : ∀ d, 0 ≤ μ d)
    (hτ : 0 ≤ τ) (d : ℕ) :
    Monotone (bundleRankwiseEnvelopeError α β μ τ d) := by
  apply monotone_nat_of_le_succ
  intro n
  cases d with
  | zero => simp
  | succ d =>
      rw [bundleRankwiseEnvelopeError_succ_order,
        bundleRankwiseEnvelopeError_succ_order,
        bundleRankwiseNextRow_succ]
      exact le_max_of_le_right
        (le_add_of_nonneg_right
          (bundleRankwiseStepIncrement_nonneg hα hμ hτ _ d n))

/-- The maximum in the row constructor makes the error monotone in rank. -/
theorem bundleRankwiseEnvelopeError_le_succ_order
    (α β μ : ℕ → ℝ) (τ : ℝ) (d n : ℕ) :
    bundleRankwiseEnvelopeError α β μ τ d n ≤
      bundleRankwiseEnvelopeError α β μ τ (d + 1) n := by
  cases n with
  | zero => simp
  | succ n =>
      rw [bundleRankwiseEnvelopeError_succ_order,
        bundleRankwiseNextRow_succ]
      exact le_max_left _ _

theorem bundleRankwiseEnvelopeError_monotone_order
    (α β μ : ℕ → ℝ) (τ : ℝ) (n : ℕ) :
    Monotone (fun d => bundleRankwiseEnvelopeError α β μ τ d n) := by
  apply monotone_nat_of_le_succ
  exact fun d => bundleRankwiseEnvelopeError_le_succ_order α β μ τ d n

/-! ## The generalized-counting interface -/

/-- The rankwise equality/max schedule is a counting envelope with the
prefix-minimum density floor. -/
theorem bundleRankwiseEnvelopeError_isEnvelope
    {α β : ℕ → ℝ} {τ : ℝ}
    (hα : ∀ d, 0 < α d) (hα_one : ∀ d, α d ≤ 1)
    (hβ : ∀ d, 0 ≤ β d) (hτ : 0 ≤ τ) :
    IsBundleCountingEnvelope α β
      (bundleRankwiseDensityFloor α) τ
      (bundleRankwiseEnvelopeError α β
        (bundleRankwiseDensityFloor α) τ) := by
  let μ := bundleRankwiseDensityFloor α
  have hμ : ∀ d, 0 < μ d := bundleRankwiseDensityFloor_pos hα
  refine
    { density_pos := hα
      density_le_one := hα_one
      defect_nonneg := hβ
      uniform_nonneg := hτ
      floor_pos := hμ
      rankFloor := ?_
      error_nonneg := bundleRankwiseEnvelopeError_nonneg
        (fun d => (hα d).le) (fun d => (hμ d).le) hτ
      error_mono_order := ?_
      error_mono_card := ?_
      step := ?_ }
  · intro i d hid
    exact bundleRankwiseDensityFloor_le α hid
  · intro d d' n hdd'
    exact (bundleRankwiseEnvelopeError_monotone_order α β μ τ n) hdd'
  · intro d n n' hnn'
    exact (bundleRankwiseEnvelopeError_monotone_card
      (fun q => (hα q).le) (fun q => (hμ q).le) hτ d) hnn'
  · intro d n
    have hstep :
        bundleRankwiseNextRow α β μ τ d
              (bundleRankwiseEnvelopeError α β μ τ d) n +
            bundleRankwiseStepIncrement α β μ τ
              (bundleRankwiseEnvelopeError α β μ τ d) d n ≤
          max (bundleRankwiseEnvelopeError α β μ τ d (n + 1))
            (bundleRankwiseNextRow α β μ τ d
                (bundleRankwiseEnvelopeError α β μ τ d) n +
              bundleRankwiseStepIncrement α β μ τ
                (bundleRankwiseEnvelopeError α β μ τ d) d n) :=
      le_max_right _ _
    simp [μ, bundleRankwiseStepIncrement, add_assoc] at hstep ⊢

/-! ## Vanishing and continuous rankwise parameter paths -/

/-- If every rank defect and the frozen-uniformity error vanish, the next
row is zero over a zero lower row. -/
@[simp]
theorem bundleRankwiseNextRow_zero_parameters
    (α μ : ℕ → ℝ) (d : ℕ) (lower : ℕ → ℝ)
    (hlower : ∀ n, lower n = 0) :
    ∀ n,
      bundleRankwiseNextRow α (fun _ => 0) μ 0 d lower n = 0 := by
  intro n
  induction n with
  | zero => simp
  | succ n ih =>
      rw [bundleRankwiseNextRow_succ, ih]
      simp [bundleRankwiseStepIncrement, hlower]

/-- The complete rankwise schedule vanishes when all analytic errors do. -/
@[simp]
theorem bundleRankwiseEnvelopeError_zero_parameters
    (α μ : ℕ → ℝ) :
    ∀ d n,
      bundleRankwiseEnvelopeError α (fun _ => 0) μ 0 d n = 0 := by
  intro d
  induction d with
  | zero =>
      intro n
      simp
  | succ d ih =>
      intro n
      rw [bundleRankwiseEnvelopeError_succ_order]
      exact bundleRankwiseNextRow_zero_parameters α μ d _ ih n

/-- The row constructor varies continuously along any continuous defect,
uniformity, and lower-row path. -/
theorem continuous_bundleRankwiseNextRow
    (α μ : ℕ → ℝ) (β : ℝ → ℕ → ℝ) (τ : ℝ → ℝ)
    (d : ℕ) (lower : ℝ → ℕ → ℝ)
    (hβ : ∀ q, Continuous (fun t => β t q))
    (hτ : Continuous τ)
    (hlower : ∀ n, Continuous (fun t => lower t n)) :
    ∀ n,
      Continuous (fun t =>
        bundleRankwiseNextRow α (β t) μ (τ t) d (lower t) n) := by
  intro n
  induction n with
  | zero =>
      simp only [bundleRankwiseNextRow_zero]
      fun_prop
  | succ n ih =>
      simp only [bundleRankwiseNextRow_succ,
        bundleRankwiseStepIncrement]
      have hβd := hβ (d + 1)
      have hlower₁ := hlower (n + 1)
      have hlower₂ := hlower (2 * (n + 1))
      fun_prop

/-- Every fixed entry of the rankwise envelope is continuous along a
continuous parameter path. -/
theorem continuous_bundleRankwiseEnvelopeError
    (α μ : ℕ → ℝ) (β : ℝ → ℕ → ℝ) (τ : ℝ → ℝ)
    (hβ : ∀ q, Continuous (fun t => β t q))
    (hτ : Continuous τ) :
    ∀ d n,
      Continuous (fun t =>
        bundleRankwiseEnvelopeError α (β t) μ (τ t) d n) := by
  intro d
  induction d with
  | zero =>
      intro n
      simp only [bundleRankwiseEnvelopeError_zero_order]
      fun_prop
  | succ d ih =>
      intro n
      change Continuous (fun t =>
        bundleRankwiseNextRow α (β t) μ (τ t) d
          (bundleRankwiseEnvelopeError α (β t) μ (τ t) d) n)
      exact continuous_bundleRankwiseNextRow α μ β τ d _ hβ hτ ih n

/-! ## Density-scaled finite-horizon selection -/

/-- A defect schedule whose rank-`d` reserve uses only `α d` (besides the
common scalar and the caller-chosen exponent). -/
noncomputable def bundleRankwiseScaledDefect
    (α : ℕ → ℝ) (power : ℕ → ℕ) (t : ℝ) (d : ℕ) : ℝ :=
  (t * (α d) ^ (power d)) ^ 2

/-- A frozen-uniformity reserve scaled by the prefix density floor at the
finite rank horizon. -/
noncomputable def bundleRankwiseScaledUniformity
    (α : ℕ → ℝ) (rankBound uniformPower : ℕ) (t : ℝ) : ℝ :=
  (t *
      (bundleRankwiseDensityFloor α rankBound) ^ uniformPower) ^ 2

theorem continuous_bundleRankwiseScaledDefect
    (α : ℕ → ℝ) (power : ℕ → ℕ) (d : ℕ) :
    Continuous (fun t => bundleRankwiseScaledDefect α power t d) := by
  unfold bundleRankwiseScaledDefect
  fun_prop

theorem continuous_bundleRankwiseScaledUniformity
    (α : ℕ → ℝ) (rankBound uniformPower : ℕ) :
    Continuous (bundleRankwiseScaledUniformity α rankBound uniformPower) := by
  unfold bundleRankwiseScaledUniformity
  fun_prop

@[simp]
theorem bundleRankwiseScaledDefect_zero
    (α : ℕ → ℝ) (power : ℕ → ℕ) (d : ℕ) :
    bundleRankwiseScaledDefect α power 0 d = 0 := by
  simp [bundleRankwiseScaledDefect]

@[simp]
theorem bundleRankwiseScaledUniformity_zero
    (α : ℕ → ℝ) (rankBound uniformPower : ℕ) :
    bundleRankwiseScaledUniformity α rankBound uniformPower 0 = 0 := by
  simp [bundleRankwiseScaledUniformity]

/-- Along the density-scaled one-parameter family, every fixed finite entry
of the rankwise envelope tends to zero. -/
theorem tendsto_bundleRankwiseScaledEnvelopeError_zero
    (α : ℕ → ℝ) (power : ℕ → ℕ)
    (rankBound uniformPower d n : ℕ) :
    Tendsto
      (fun t =>
        bundleRankwiseEnvelopeError α
          (bundleRankwiseScaledDefect α power t)
          (bundleRankwiseDensityFloor α)
          (bundleRankwiseScaledUniformity α rankBound uniformPower t)
          d n)
      (𝓝 0) (𝓝 0) := by
  have hcontinuous :=
    continuous_bundleRankwiseEnvelopeError
      α (bundleRankwiseDensityFloor α)
      (fun t => bundleRankwiseScaledDefect α power t)
      (bundleRankwiseScaledUniformity α rankBound uniformPower)
      (continuous_bundleRankwiseScaledDefect α power)
      (continuous_bundleRankwiseScaledUniformity α rankBound uniformPower)
      d n
  have hβzero :
      bundleRankwiseScaledDefect α power 0 = fun _ => 0 := by
    funext q
    exact bundleRankwiseScaledDefect_zero α power q
  simpa [hβzero] using hcontinuous.tendsto 0

/-- Finite-horizon rankwise small-parameter selection.

The selected defect at rank `d` is
`(t * α d ^ power d)²`, so its density dependence is pointwise rather than
through a common floor.  The single frozen-uniformity reserve is
`(t * μ rankBound ^ uniformPower)²`, where `μ` is the prefix floor.  Both
formulas are strictly positive for positive densities and `t > 0`, and their
explicit envelope error can be made smaller than any prescribed reserve. -/
theorem exists_bundleRankwiseScaledEnvelopeError_lt
    {α : ℕ → ℝ}
    (hα : ∀ d, 0 < α d) (hα_one : ∀ d, α d ≤ 1)
    (power : ℕ → ℕ) (rankBound edgeBound uniformPower : ℕ)
    {parameterReserve errorReserve : ℝ}
    (hparameter : 0 < parameterReserve)
    (herror : 0 < errorReserve) :
    ∃ t : ℝ,
      0 < t ∧ t < parameterReserve ∧ t < 1 ∧
      IsBundleCountingEnvelope α
        (bundleRankwiseScaledDefect α power t)
        (bundleRankwiseDensityFloor α)
        (bundleRankwiseScaledUniformity α rankBound uniformPower t)
        (bundleRankwiseEnvelopeError α
          (bundleRankwiseScaledDefect α power t)
          (bundleRankwiseDensityFloor α)
          (bundleRankwiseScaledUniformity α rankBound uniformPower t)) ∧
      bundleRankwiseEnvelopeError α
          (bundleRankwiseScaledDefect α power t)
          (bundleRankwiseDensityFloor α)
          (bundleRankwiseScaledUniformity α rankBound uniformPower t)
          rankBound edgeBound < errorReserve := by
  have heventually :
      ∀ᶠ t : ℝ in 𝓝 0,
        bundleRankwiseEnvelopeError α
            (bundleRankwiseScaledDefect α power t)
            (bundleRankwiseDensityFloor α)
            (bundleRankwiseScaledUniformity α rankBound uniformPower t)
            rankBound edgeBound < errorReserve :=
    (tendsto_bundleRankwiseScaledEnvelopeError_zero
      α power rankBound uniformPower rankBound edgeBound).eventually_lt_const herror
  obtain ⟨δ, hδ, hball⟩ := Metric.eventually_nhds_iff_ball.mp heventually
  let t : ℝ := min δ (min parameterReserve 1) / 2
  have hmin : 0 < min δ (min parameterReserve 1) :=
    lt_min hδ (lt_min hparameter zero_lt_one)
  have ht : 0 < t := by
    dsimp [t]
    linarith
  have htδ : t < δ := by
    dsimp [t]
    have hle : min δ (min parameterReserve 1) ≤ δ := min_le_left _ _
    linarith
  have htparameter : t < parameterReserve := by
    dsimp [t]
    have hle₁ : min δ (min parameterReserve 1) ≤ min parameterReserve 1 :=
      min_le_right _ _
    have hle₂ : min parameterReserve 1 ≤ parameterReserve := min_le_left _ _
    linarith
  have htone : t < 1 := by
    dsimp [t]
    have hle₁ : min δ (min parameterReserve 1) ≤ min parameterReserve 1 :=
      min_le_right _ _
    have hle₂ : min parameterReserve 1 ≤ 1 := min_le_right _ _
    linarith
  have henvelope :
      IsBundleCountingEnvelope α
        (bundleRankwiseScaledDefect α power t)
        (bundleRankwiseDensityFloor α)
        (bundleRankwiseScaledUniformity α rankBound uniformPower t)
        (bundleRankwiseEnvelopeError α
          (bundleRankwiseScaledDefect α power t)
          (bundleRankwiseDensityFloor α)
          (bundleRankwiseScaledUniformity α rankBound uniformPower t)) :=
    bundleRankwiseEnvelopeError_isEnvelope hα hα_one
      (fun d => sq_nonneg (t * (α d) ^ (power d)))
      (sq_nonneg
        (t * (bundleRankwiseDensityFloor α rankBound) ^ uniformPower))
  refine ⟨t, ht, htparameter, htone, henvelope, ?_⟩
  apply hball
  simpa [Real.dist_eq, abs_of_pos ht] using htδ

/-- The concrete half-error selector used to turn the relative counting
estimate into a positive configuration count. -/
theorem exists_bundleRankwiseScaledEnvelopeError_lt_half
    {α : ℕ → ℝ}
    (hα : ∀ d, 0 < α d) (hα_one : ∀ d, α d ≤ 1)
    (power : ℕ → ℕ) (rankBound edgeBound uniformPower : ℕ) :
    ∃ t : ℝ,
      0 < t ∧ t < 1 ∧
      IsBundleCountingEnvelope α
        (bundleRankwiseScaledDefect α power t)
        (bundleRankwiseDensityFloor α)
        (bundleRankwiseScaledUniformity α rankBound uniformPower t)
        (bundleRankwiseEnvelopeError α
          (bundleRankwiseScaledDefect α power t)
          (bundleRankwiseDensityFloor α)
          (bundleRankwiseScaledUniformity α rankBound uniformPower t)) ∧
      bundleRankwiseEnvelopeError α
          (bundleRankwiseScaledDefect α power t)
          (bundleRankwiseDensityFloor α)
          (bundleRankwiseScaledUniformity α rankBound uniformPower t)
          rankBound edgeBound < 1 / 2 := by
  obtain ⟨t, ht, htone, _htone', hE, hfinal⟩ :=
    exists_bundleRankwiseScaledEnvelopeError_lt hα hα_one power
      rankBound edgeBound uniformPower zero_lt_one
      (by norm_num : (0 : ℝ) < 1 / 2)
  exact ⟨t, ht, htone, hE, hfinal⟩

/-! ## Explicit finite-horizon sufficient bounds -/

/-- Reverse-doubling edge horizon: lower-order calls made while controlling
rank `d + 1` through its horizon fit into the rank-`d` horizon. -/
def bundleReverseDoublingHorizon
    (rankBound edgeBound d : ℕ) : ℕ :=
  (edgeBound + 1) * 2 ^ (rankBound - d)

theorem bundleReverseDoublingHorizon_two_mul_succ
    {rankBound edgeBound d : ℕ} (hd : d < rankBound) :
    2 * bundleReverseDoublingHorizon rankBound edgeBound (d + 1) =
      bundleReverseDoublingHorizon rankBound edgeBound d := by
  have hsub : rankBound - d = rankBound - (d + 1) + 1 := by
    omega
  simp only [bundleReverseDoublingHorizon, hsub, pow_succ]
  ring

theorem bundleReverseDoublingHorizon_le_zero
    (rankBound edgeBound d : ℕ) :
    bundleReverseDoublingHorizon rankBound edgeBound d ≤
      bundleReverseDoublingHorizon rankBound edgeBound 0 := by
  unfold bundleReverseDoublingHorizon
  apply Nat.mul_le_mul_left
  exact (pow_right_monotone (by norm_num : (1 : ℕ) ≤ 2))
    (Nat.sub_le rankBound d)

/-- If the two lower-row entries are bounded by `B`, the actual one-edge
increment is bounded by the sum of a defect-only and a uniformity-only
majorant.  This is the separation used by the finite-horizon theorem below. -/
theorem bundleRankwiseStepIncrement_le_of_lower_le
    {α β μ : ℕ → ℝ} {τ B η : ℝ}
    (hα : ∀ d, 0 ≤ α d) (hβ : ∀ d, 0 ≤ β d)
    (lower : ℕ → ℝ) (d n : ℕ)
    (hlower_nonneg : ∀ m, 0 ≤ lower m)
    (hlower₁ : lower (n + 1) ≤ B)
    (hlower₂ : lower (2 * (n + 1)) ≤ B)
    (hdefect :
      Real.sqrt
            (β (d + 1) * (1 + B) * (1 + B)) /
          (α (d + 1)) ^ (n + 1) ≤ η / 2)
    (huniform :
      τ / (μ (d + 1)) ^ (n + 1) ≤ η / 2) :
    bundleRankwiseStepIncrement α β μ τ lower d n ≤ η := by
  have hlower₁nonneg : 0 ≤ 1 + lower (n + 1) := by
    linarith [hlower_nonneg (n + 1)]
  have hlower₂nonneg : 0 ≤ 1 + lower (2 * (n + 1)) := by
    linarith [hlower_nonneg (2 * (n + 1))]
  have hB₁nonneg : 0 ≤ 1 + B := by
    linarith [hlower_nonneg (n + 1), hlower₁]
  have hproduct :
      (1 + lower (n + 1)) * (1 + lower (2 * (n + 1))) ≤
        (1 + B) * (1 + B) := by
    exact mul_le_mul
      (by linarith)
      (by linarith)
      hlower₂nonneg hB₁nonneg
  have hradicand :
      β (d + 1) *
          (1 + lower (n + 1)) *
          (1 + lower (2 * (n + 1))) ≤
        β (d + 1) * (1 + B) * (1 + B) := by
    simpa [mul_assoc] using
      mul_le_mul_of_nonneg_left hproduct (hβ (d + 1))
  have hsqrt :
      Real.sqrt
          (β (d + 1) *
            (1 + lower (n + 1)) *
            (1 + lower (2 * (n + 1)))) ≤
        Real.sqrt (β (d + 1) * (1 + B) * (1 + B)) :=
    Real.sqrt_le_sqrt hradicand
  have hnormalized :
      Real.sqrt
            (β (d + 1) *
              (1 + lower (n + 1)) *
              (1 + lower (2 * (n + 1)))) /
          (α (d + 1)) ^ (n + 1) ≤ η / 2 :=
    (div_le_div_of_nonneg_right hsqrt
      (pow_nonneg (hα (d + 1)) (n + 1))).trans hdefect
  unfold bundleRankwiseStepIncrement
  linarith

/-- A finite-rank/cardinality estimate from separated numerical hypotheses.

`horizon` must reverse-double, because one counting step at rank `d + 1`
consults lower-order bundles of sizes `n + 1` and `2(n + 1)`.  The defect
hypothesis at rank `d + 1` mentions only `β (d + 1)` and `α (d + 1)`;
the uniformity hypothesis mentions only `τ` and `μ (d + 1)`.  Thus the two
analytic parameters can be scheduled independently once a common per-step
budget `η` and a harmless lower-error cap `B` have been fixed. -/
theorem bundleRankwiseEnvelopeError_le_finiteBudget
    {α β μ : ℕ → ℝ} {τ η B : ℝ}
    (hα : ∀ d, 0 ≤ α d) (hβ : ∀ d, 0 ≤ β d)
    (hμ : ∀ d, 0 ≤ μ d) (hτ : 0 ≤ τ) (hη : 0 ≤ η)
    (rankBound : ℕ) (horizon : ℕ → ℕ)
    (hreverse : ∀ d, d < rankBound →
      2 * horizon (d + 1) ≤ horizon d)
    (hzero : ∀ d, d ≤ rankBound → horizon d ≤ horizon 0)
    (hcap :
      (rankBound : ℝ) * (horizon 0 : ℝ) * η ≤ B)
    (hdefect : ∀ d, d < rankBound → ∀ n, n < horizon (d + 1) →
      Real.sqrt
            (β (d + 1) * (1 + B) * (1 + B)) /
          (α (d + 1)) ^ (n + 1) ≤ η / 2)
    (huniform : ∀ d, d < rankBound → ∀ n, n < horizon (d + 1) →
      τ / (μ (d + 1)) ^ (n + 1) ≤ η / 2) :
    ∀ d, d ≤ rankBound → ∀ n, n ≤ horizon d →
      bundleRankwiseEnvelopeError α β μ τ d n ≤
        (d : ℝ) * (horizon 0 : ℝ) * η := by
  intro d hd
  induction d with
  | zero =>
      intro n hn
      simp
  | succ d ih =>
      have hdlt : d < rankBound := Nat.lt_of_succ_le hd
      let lower := bundleRankwiseEnvelopeError α β μ τ d
      have hlower_nonneg : ∀ m, 0 ≤ lower m :=
        bundleRankwiseEnvelopeError_nonneg hα hμ hτ d
      have hdle : d ≤ rankBound := Nat.le_of_lt hdlt
      have hdbound :
          (d : ℝ) * (horizon 0 : ℝ) * η ≤ B := by
        have hdcast : (d : ℝ) ≤ rankBound := by exact_mod_cast hdle
        have hq0 : 0 ≤ (horizon 0 : ℝ) := by positivity
        have hscale : 0 ≤ (horizon 0 : ℝ) * η := mul_nonneg hq0 hη
        calc
          (d : ℝ) * (horizon 0 : ℝ) * η =
              (d : ℝ) * ((horizon 0 : ℝ) * η) := by ring
          _ ≤ (rankBound : ℝ) * ((horizon 0 : ℝ) * η) :=
            mul_le_mul_of_nonneg_right hdcast hscale
          _ = (rankBound : ℝ) * (horizon 0 : ℝ) * η := by ring
          _ ≤ B := hcap
      have hrow : ∀ m, m ≤ horizon (d + 1) →
          bundleRankwiseNextRow α β μ τ d lower m ≤
            (d : ℝ) * (horizon 0 : ℝ) * η + (m : ℝ) * η := by
        intro m hm
        induction m with
        | zero =>
            simp only [bundleRankwiseNextRow_zero, Nat.cast_zero, zero_mul,
              add_zero]
            exact mul_nonneg (mul_nonneg (by positivity) (by positivity)) hη
        | succ m ihm =>
            have hmle : m ≤ horizon (d + 1) := Nat.le_trans (Nat.le_succ m) hm
            have hm_lt : m < horizon (d + 1) := Nat.lt_of_succ_le hm
            have hsmall₁ : m + 1 ≤ horizon d := by
              have hrev := hreverse d hdlt
              omega
            have hsmall₂ : 2 * (m + 1) ≤ horizon d := by
              have hrev := hreverse d hdlt
              omega
            have hlower₁raw := ih hdle (m + 1) hsmall₁
            have hlower₂raw := ih hdle (2 * (m + 1)) hsmall₂
            have hlower₁ : lower (m + 1) ≤ B := hlower₁raw.trans hdbound
            have hlower₂ : lower (2 * (m + 1)) ≤ B := hlower₂raw.trans hdbound
            have hincrement :
                bundleRankwiseStepIncrement α β μ τ lower d m ≤ η :=
              bundleRankwiseStepIncrement_le_of_lower_le hα hβ lower d m
                hlower_nonneg hlower₁ hlower₂
                (hdefect d hdlt m hm_lt) (huniform d hdlt m hm_lt)
            rw [bundleRankwiseNextRow_succ]
            apply max_le
            · calc
                lower (m + 1) ≤
                    (d : ℝ) * (horizon 0 : ℝ) * η := hlower₁raw
                _ ≤ (d : ℝ) * (horizon 0 : ℝ) * η +
                    ((m + 1 : ℕ) : ℝ) * η :=
                  le_add_of_nonneg_right (mul_nonneg (by positivity) hη)
            · calc
                bundleRankwiseNextRow α β μ τ d lower m +
                      bundleRankwiseStepIncrement α β μ τ lower d m ≤
                    ((d : ℝ) * (horizon 0 : ℝ) * η + (m : ℝ) * η) + η :=
                  add_le_add (ihm hmle) hincrement
                _ = (d : ℝ) * (horizon 0 : ℝ) * η +
                    ((m + 1 : ℕ) : ℝ) * η := by
                  push_cast
                  ring
      intro n hn
      rw [bundleRankwiseEnvelopeError_succ_order]
      have hmain := hrow n hn
      have hnzero : n ≤ horizon 0 := hn.trans (hzero (d + 1) hd)
      have hncast : (n : ℝ) ≤ horizon 0 := by exact_mod_cast hnzero
      have hηscale : (n : ℝ) * η ≤ (horizon 0 : ℝ) * η :=
        mul_le_mul_of_nonneg_right hncast hη
      calc
        bundleRankwiseNextRow α β μ τ d lower n ≤
            (d : ℝ) * (horizon 0 : ℝ) * η + (n : ℝ) * η := hmain
        _ ≤ (d : ℝ) * (horizon 0 : ℝ) * η +
            (horizon 0 : ℝ) * η := add_le_add_right hηscale _
        _ = ((d + 1 : ℕ) : ℝ) * (horizon 0 : ℝ) * η := by
          push_cast
          ring

/-- Specialization of the finite-budget theorem to the canonical
reverse-doubling horizons. -/
theorem bundleRankwiseEnvelopeError_le_reverseDoublingBudget
    {α β μ : ℕ → ℝ} {τ η B : ℝ}
    (hα : ∀ d, 0 ≤ α d) (hβ : ∀ d, 0 ≤ β d)
    (hμ : ∀ d, 0 ≤ μ d) (hτ : 0 ≤ τ) (hη : 0 ≤ η)
    (rankBound edgeBound : ℕ)
    (hcap :
      (rankBound : ℝ) *
          (bundleReverseDoublingHorizon rankBound edgeBound 0 : ℝ) * η ≤ B)
    (hdefect : ∀ d, d < rankBound → ∀ n,
      n < bundleReverseDoublingHorizon rankBound edgeBound (d + 1) →
      Real.sqrt
            (β (d + 1) * (1 + B) * (1 + B)) /
          (α (d + 1)) ^ (n + 1) ≤ η / 2)
    (huniform : ∀ d, d < rankBound → ∀ n,
      n < bundleReverseDoublingHorizon rankBound edgeBound (d + 1) →
      τ / (μ (d + 1)) ^ (n + 1) ≤ η / 2) :
    bundleRankwiseEnvelopeError α β μ τ rankBound (edgeBound + 1) ≤
      (rankBound : ℝ) *
        (bundleReverseDoublingHorizon rankBound edgeBound 0 : ℝ) * η := by
  apply bundleRankwiseEnvelopeError_le_finiteBudget hα hβ hμ hτ hη
    rankBound (bundleReverseDoublingHorizon rankBound edgeBound)
    (fun d hd => (bundleReverseDoublingHorizon_two_mul_succ hd).le)
    (fun d _hd => bundleReverseDoublingHorizon_le_zero rankBound edgeBound d)
    hcap hdefect huniform rankBound le_rfl (edgeBound + 1)
  simp [bundleReverseDoublingHorizon]

/-- A ready-to-use half-error criterion with prefix density floors.

The cap `1` makes every lower correction factor at most `2`.  The defect
conditions remain rank-local, while the uniform conditions use only the
prefix floor.  The conclusion packages both the global counting-envelope
interface and the finite error estimate needed for positivity. -/
theorem bundleRankwiseEnvelope_and_error_lt_half_of_reverseDoublingBudget
    {α β : ℕ → ℝ} {τ η : ℝ}
    (hα : ∀ d, 0 < α d) (hα_one : ∀ d, α d ≤ 1)
    (hβ : ∀ d, 0 ≤ β d) (hτ : 0 ≤ τ) (hη : 0 ≤ η)
    (rankBound edgeBound : ℕ)
    (hcap :
      (rankBound : ℝ) *
          (bundleReverseDoublingHorizon rankBound edgeBound 0 : ℝ) * η ≤ 1)
    (hfinal :
      (rankBound : ℝ) *
          (bundleReverseDoublingHorizon rankBound edgeBound 0 : ℝ) * η < 1 / 2)
    (hdefect : ∀ d, d < rankBound → ∀ n,
      n < bundleReverseDoublingHorizon rankBound edgeBound (d + 1) →
      Real.sqrt
            (β (d + 1) * (1 + (1 : ℝ)) * (1 + (1 : ℝ))) /
          (α (d + 1)) ^ (n + 1) ≤ η / 2)
    (huniform : ∀ d, d < rankBound → ∀ n,
      n < bundleReverseDoublingHorizon rankBound edgeBound (d + 1) →
      τ /
          (bundleRankwiseDensityFloor α (d + 1)) ^ (n + 1) ≤
        η / 2) :
    IsBundleCountingEnvelope α β
        (bundleRankwiseDensityFloor α) τ
        (bundleRankwiseEnvelopeError α β
          (bundleRankwiseDensityFloor α) τ) ∧
      bundleRankwiseEnvelopeError α β
          (bundleRankwiseDensityFloor α) τ rankBound edgeBound < 1 / 2 := by
  have hμ : ∀ d, 0 ≤ bundleRankwiseDensityFloor α d :=
    fun d => (bundleRankwiseDensityFloor_pos hα d).le
  have hbound :=
    bundleRankwiseEnvelopeError_le_reverseDoublingBudget
      (fun d => (hα d).le) hβ hμ hτ hη rankBound edgeBound
      hcap hdefect huniform
  have hcard :
      bundleRankwiseEnvelopeError α β
          (bundleRankwiseDensityFloor α) τ rankBound edgeBound ≤
        bundleRankwiseEnvelopeError α β
          (bundleRankwiseDensityFloor α) τ rankBound (edgeBound + 1) :=
    (bundleRankwiseEnvelopeError_monotone_card
      (fun d => (hα d).le) hμ hτ rankBound) (Nat.le_succ edgeBound)
  exact ⟨bundleRankwiseEnvelopeError_isEnvelope hα hα_one hβ hτ,
    (hcard.trans hbound).trans_lt hfinal⟩

end Wikipedia.SzemeredisTheorem
