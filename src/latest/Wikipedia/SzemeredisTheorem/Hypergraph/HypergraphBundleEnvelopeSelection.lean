import Wikipedia.SzemeredisTheorem.Hypergraph.HypergraphBundleGeneralizedCounting

/-!
# Small parameters for the bundle-counting envelope

The generalized bundle-counting induction asks for an error array indexed
both by bundle order and by the number of occurrence edges.  At one step,
the array must absorb

```text
sqrt (β * (1 + lower error) * (1 + doubled lower error)) / α^n
  + τ / μ^n.
```

This file gives a self-contained numerical solution when all density
floors are bounded below by one common number `a`.  We put both the defect
and frozen-uniformity errors equal to `t²` and define the array by equality
in the required recurrence.  For each fixed finite pair `(r, L)`, this
array is continuous in `t` and is zero at `t = 0`.  Consequently one can
choose a strictly positive `t`, as small as desired, for which the final
error is below any prescribed positive reserve.

Using a square as the common small parameter has two conveniences:
nonnegativity is automatic for every real `t`, and the square root in the
recurrence remains a globally continuous function of `t`.
-/

namespace Wikipedia.SzemeredisTheorem

open Filter Topology

/-! ## The equality schedule -/

/-- The contribution added while adjoining the `(n + 1)`st occurrence
edge at the next order. -/
noncomputable def bundleCommonStepIncrement
    (a t : ℝ) (lower : ℕ → ℝ) (n : ℕ) : ℝ :=
  Real.sqrt
        (t ^ 2 *
          (1 + lower (n + 1)) *
          (1 + lower (2 * (n + 1)))) /
      a ^ (n + 1) +
    t ^ 2 / a ^ (n + 1)

/-- Given the complete error row at lower order, form the next row by
summing the one-edge increments. -/
noncomputable def bundleCommonNextRow
    (a t : ℝ) (lower : ℕ → ℝ) : ℕ → ℝ
  | 0 => 0
  | n + 1 =>
      bundleCommonNextRow a t lower n +
        bundleCommonStepIncrement a t lower n

/-- The common-floor bundle-counting error schedule.

Order zero is exact.  Each positive-order row is obtained from the
preceding row by `bundleCommonNextRow`. -/
noncomputable def bundleCommonEnvelopeError
    (a t : ℝ) : ℕ → ℕ → ℝ
  | 0 => fun _ => 0
  | d + 1 =>
      bundleCommonNextRow a t
        (bundleCommonEnvelopeError a t d)

@[simp]
theorem bundleCommonNextRow_zero
    (a t : ℝ) (lower : ℕ → ℝ) :
    bundleCommonNextRow a t lower 0 = 0 :=
  rfl

@[simp]
theorem bundleCommonNextRow_succ
    (a t : ℝ) (lower : ℕ → ℝ) (n : ℕ) :
    bundleCommonNextRow a t lower (n + 1) =
      bundleCommonNextRow a t lower n +
        bundleCommonStepIncrement a t lower n :=
  rfl

@[simp]
theorem bundleCommonEnvelopeError_zero_order
    (a t : ℝ) (n : ℕ) :
    bundleCommonEnvelopeError a t 0 n = 0 :=
  rfl

@[simp]
theorem bundleCommonEnvelopeError_succ_order
    (a t : ℝ) (d n : ℕ) :
    bundleCommonEnvelopeError a t (d + 1) n =
      bundleCommonNextRow a t
        (bundleCommonEnvelopeError a t d) n :=
  rfl

/-! ## Positivity and monotonicity -/

/-- Every row produced by the equality schedule is nonnegative when the
common density floor is nonnegative. -/
theorem bundleCommonNextRow_nonneg
    {a t : ℝ} (ha : 0 ≤ a)
    (lower : ℕ → ℝ) :
    ∀ n, 0 ≤ bundleCommonNextRow a t lower n := by
  intro n
  induction n with
  | zero =>
      simp
  | succ n ihn =>
      rw [bundleCommonNextRow_succ]
      apply add_nonneg ihn
      unfold bundleCommonStepIncrement
      exact add_nonneg
        (div_nonneg (Real.sqrt_nonneg _)
          (pow_nonneg ha _))
        (div_nonneg (sq_nonneg t)
          (pow_nonneg ha _))

/-- Every entry in the two-dimensional schedule is nonnegative. -/
theorem bundleCommonEnvelopeError_nonneg
    {a t : ℝ} (ha : 0 ≤ a) :
    ∀ d n, 0 ≤ bundleCommonEnvelopeError a t d n := by
  intro d
  induction d with
  | zero =>
      intro n
      simp
  | succ d _ih =>
      intro n
      rw [bundleCommonEnvelopeError_succ_order]
      exact bundleCommonNextRow_nonneg ha _ n

/-- Increasing a nonnegative lower row pointwise can only increase the
one-edge increment. -/
theorem bundleCommonStepIncrement_mono
    {a t : ℝ} (ha : 0 ≤ a)
    {lower₁ lower₂ : ℕ → ℝ}
    (hlower₁ : ∀ n, 0 ≤ lower₁ n)
    (hlower : ∀ n, lower₁ n ≤ lower₂ n)
    (n : ℕ) :
    bundleCommonStepIncrement a t lower₁ n ≤
      bundleCommonStepIncrement a t lower₂ n := by
  have h₁nonneg :
      0 ≤ 1 + lower₁ (n + 1) := by
    linarith [hlower₁ (n + 1)]
  have h₂nonneg :
      0 ≤ 1 + lower₁ (2 * (n + 1)) := by
    linarith [hlower₁ (2 * (n + 1))]
  have hright₁nonneg :
      0 ≤ 1 + lower₂ (n + 1) := by
    linarith [hlower₁ (n + 1), hlower (n + 1)]
  have hproduct :
      (1 + lower₁ (n + 1)) *
          (1 + lower₁ (2 * (n + 1))) ≤
        (1 + lower₂ (n + 1)) *
          (1 + lower₂ (2 * (n + 1))) := by
    exact mul_le_mul
      (by linarith [hlower (n + 1)])
      (by linarith [hlower (2 * (n + 1))])
      h₂nonneg hright₁nonneg
  have hradicand :
      t ^ 2 *
          (1 + lower₁ (n + 1)) *
          (1 + lower₁ (2 * (n + 1))) ≤
        t ^ 2 *
          (1 + lower₂ (n + 1)) *
          (1 + lower₂ (2 * (n + 1))) := by
    simpa [mul_assoc] using
      mul_le_mul_of_nonneg_left hproduct (sq_nonneg t)
  unfold bundleCommonStepIncrement
  apply add_le_add
  · exact div_le_div_of_nonneg_right
      (Real.sqrt_le_sqrt hradicand)
      (pow_nonneg ha _)
  · exact le_rfl

/-- The row constructor is monotone in a nonnegative lower row. -/
theorem bundleCommonNextRow_mono
    {a t : ℝ} (ha : 0 ≤ a)
    {lower₁ lower₂ : ℕ → ℝ}
    (hlower₁ : ∀ n, 0 ≤ lower₁ n)
    (hlower : ∀ n, lower₁ n ≤ lower₂ n) :
    ∀ n,
      bundleCommonNextRow a t lower₁ n ≤
        bundleCommonNextRow a t lower₂ n := by
  intro n
  induction n with
  | zero =>
      simp
  | succ n ihn =>
      rw [bundleCommonNextRow_succ,
        bundleCommonNextRow_succ]
      exact add_le_add ihn
        (bundleCommonStepIncrement_mono
          ha hlower₁ hlower n)

/-- At fixed order, the schedule is monotone in the occurrence-edge
cardinality. -/
theorem bundleCommonEnvelopeError_monotone_card
    {a t : ℝ} (ha : 0 ≤ a) (d : ℕ) :
    Monotone (bundleCommonEnvelopeError a t d) := by
  apply monotone_nat_of_le_succ
  intro n
  cases d with
  | zero =>
      simp
  | succ d =>
      rw [bundleCommonEnvelopeError_succ_order,
        bundleCommonEnvelopeError_succ_order,
        bundleCommonNextRow_succ]
      exact le_add_of_nonneg_right
        (by
          unfold bundleCommonStepIncrement
          exact add_nonneg
            (div_nonneg (Real.sqrt_nonneg _)
              (pow_nonneg ha _))
            (div_nonneg (sq_nonneg t)
              (pow_nonneg ha _)))

/-- At fixed cardinality, the schedule is monotone in bundle order. -/
theorem bundleCommonEnvelopeError_monotone_order
    {a t : ℝ} (ha : 0 ≤ a) :
    ∀ n, Monotone (fun d =>
      bundleCommonEnvelopeError a t d n) := by
  intro n
  apply monotone_nat_of_le_succ
  intro d
  induction d generalizing n with
  | zero =>
      simp only [bundleCommonEnvelopeError_zero_order]
      exact bundleCommonEnvelopeError_nonneg ha 1 n
  | succ d ihd =>
      rw [bundleCommonEnvelopeError_succ_order,
        bundleCommonEnvelopeError_succ_order]
      apply bundleCommonNextRow_mono ha
      · exact bundleCommonEnvelopeError_nonneg ha d
      · intro m
        exact ihd m

/-! ## The envelope interface -/

/-- With a common density floor `a` and common squared error `t²`, the
equality schedule is a valid `IsBundleCountingEnvelope`. -/
theorem bundleCommonEnvelopeError_isEnvelope
    {a t : ℝ} (ha : 0 < a) (ha_one : a ≤ 1) :
    IsBundleCountingEnvelope
      (fun _ => a) (fun _ => t ^ 2) (fun _ => a) (t ^ 2)
      (bundleCommonEnvelopeError a t) := by
  refine
    { density_pos := fun _ => ha
      density_le_one := fun _ => ha_one
      defect_nonneg := fun _ => sq_nonneg t
      uniform_nonneg := sq_nonneg t
      floor_pos := fun _ => ha
      rankFloor := ?_
      error_nonneg :=
        bundleCommonEnvelopeError_nonneg ha.le
      error_mono_order := ?_
      error_mono_card := ?_
      step := ?_ }
  · intro i d hid
    exact le_rfl
  · intro d d' n hdd'
    exact
      (bundleCommonEnvelopeError_monotone_order
        ha.le n) hdd'
  · intro d n n' hnn'
    exact
      (bundleCommonEnvelopeError_monotone_card
        ha.le d) hnn'
  · intro d n
    rw [bundleCommonEnvelopeError_succ_order,
      bundleCommonEnvelopeError_succ_order,
      bundleCommonNextRow_succ]
    unfold bundleCommonStepIncrement
    ring_nf
    exact le_rfl

/-! ## Vanishing at the origin and finite-horizon selection -/

/-- At zero defect and zero frozen-uniformity error, the schedule is
identically zero. -/
@[simp]
theorem bundleCommonNextRow_zero_parameter
    (a : ℝ) (lower : ℕ → ℝ)
    (hlower : ∀ n, lower n = 0) :
    ∀ n, bundleCommonNextRow a 0 lower n = 0 := by
  intro n
  induction n with
  | zero =>
      simp
  | succ n ihn =>
      rw [bundleCommonNextRow_succ, ihn]
      simp [bundleCommonStepIncrement, hlower]

/-- Every fixed entry of the schedule is zero at the origin. -/
@[simp]
theorem bundleCommonEnvelopeError_zero_parameter
    (a : ℝ) :
    ∀ d n, bundleCommonEnvelopeError a 0 d n = 0 := by
  intro d
  induction d with
  | zero =>
      intro n
      simp
  | succ d ihd =>
      intro n
      rw [bundleCommonEnvelopeError_succ_order]
      exact bundleCommonNextRow_zero_parameter a
        (bundleCommonEnvelopeError a 0 d) ihd n

/-- For a continuously varying lower row, every fixed entry of the next
row varies continuously. -/
theorem continuous_bundleCommonNextRow
    (a : ℝ) (lower : ℝ → ℕ → ℝ)
    (hlower : ∀ n, Continuous (fun t => lower t n)) :
    ∀ n,
      Continuous
        (fun t =>
          bundleCommonNextRow a t (lower t) n) := by
  intro n
  induction n with
  | zero =>
      simp only [bundleCommonNextRow_zero]
      fun_prop
  | succ n ihn =>
      simp only [bundleCommonNextRow_succ,
        bundleCommonStepIncrement]
      have h₁ := hlower (n + 1)
      have h₂ := hlower (2 * (n + 1))
      fun_prop

/-- Every fixed finite-order, finite-cardinality envelope entry is a
continuous function of the common small parameter. -/
theorem continuous_bundleCommonEnvelopeError_real
    (a : ℝ) :
    ∀ d n,
      Continuous
        (fun t : ℝ =>
          bundleCommonEnvelopeError a t d n) := by
  intro d
  induction d with
  | zero =>
      intro n
      simp only [bundleCommonEnvelopeError_zero_order]
      fun_prop
  | succ d ihd =>
      intro n
      change
        Continuous (fun t : ℝ =>
          bundleCommonNextRow a t
            (bundleCommonEnvelopeError a t d) n)
      exact continuous_bundleCommonNextRow
        a
        (fun t m =>
          bundleCommonEnvelopeError a t d m)
        ihd n

/-- Every fixed finite-horizon envelope entry tends to zero with the
common small parameter. -/
theorem tendsto_bundleCommonEnvelopeError_zero
    (a : ℝ) (d n : ℕ) :
    Tendsto
      (fun t : ℝ =>
        bundleCommonEnvelopeError a t d n)
      (𝓝 0) (𝓝 0) := by
  simpa using
    (continuous_bundleCommonEnvelopeError_real a d n).tendsto 0

/-- For fixed rank and bundle-size bounds, a strictly positive common
parameter can be chosen below an arbitrary reserve so that the final
relative counting error is below any prescribed positive reserve. -/
theorem exists_bundleCommonEnvelopeError_lt
    (a : ℝ) (rankBound edgeBound : ℕ)
    {parameterReserve errorReserve : ℝ}
    (hparameter : 0 < parameterReserve)
    (herror : 0 < errorReserve) :
    ∃ t : ℝ,
      0 < t ∧ t < parameterReserve ∧ t < 1 ∧
        bundleCommonEnvelopeError
            a t rankBound edgeBound <
          errorReserve := by
  have heventually :
      ∀ᶠ t : ℝ in 𝓝 0,
        bundleCommonEnvelopeError
            a t rankBound edgeBound <
          errorReserve :=
    (tendsto_bundleCommonEnvelopeError_zero
      a rankBound edgeBound).eventually_lt_const herror
  obtain ⟨δ, hδ, hball⟩ :=
    Metric.eventually_nhds_iff_ball.mp heventually
  let t : ℝ := min δ (min parameterReserve 1) / 2
  have hmin :
      0 < min δ (min parameterReserve 1) := by
    exact lt_min hδ (lt_min hparameter zero_lt_one)
  have ht : 0 < t := by
    dsimp [t]
    linarith
  have htδ : t < δ := by
    dsimp [t]
    have hle :
        min δ (min parameterReserve 1) ≤ δ :=
      min_le_left _ _
    linarith
  have htparameter : t < parameterReserve := by
    dsimp [t]
    have hle :
        min δ (min parameterReserve 1) ≤
          min parameterReserve 1 :=
      min_le_right _ _
    have hle' : min parameterReserve 1 ≤ parameterReserve :=
      min_le_left _ _
    linarith
  have htone : t < 1 := by
    dsimp [t]
    have hle :
        min δ (min parameterReserve 1) ≤
          min parameterReserve 1 :=
      min_le_right _ _
    have hle' : min parameterReserve 1 ≤ 1 :=
      min_le_right _ _
    linarith
  refine ⟨t, ht, htparameter, htone, ?_⟩
  apply hball
  simpa [Real.dist_eq, abs_of_pos ht] using htδ

/-- The concrete half-error form used in generalized counting. -/
theorem exists_bundleCommonEnvelopeError_lt_half
    {a : ℝ} (ha : 0 < a) (ha_one : a ≤ 1)
    (rankBound edgeBound : ℕ) :
    ∃ t : ℝ,
      0 < t ∧ t < 1 ∧
      IsBundleCountingEnvelope
        (fun _ => a) (fun _ => t ^ 2) (fun _ => a) (t ^ 2)
        (bundleCommonEnvelopeError a t) ∧
      bundleCommonEnvelopeError
          a t rankBound edgeBound < 1 / 2 := by
  obtain ⟨t, ht, htone, _htone', hfinal⟩ :=
    exists_bundleCommonEnvelopeError_lt
      a rankBound edgeBound zero_lt_one
        (by norm_num : (0 : ℝ) < 1 / 2)
  exact ⟨t, ht, htone,
    bundleCommonEnvelopeError_isEnvelope ha ha_one,
    hfinal⟩

end Wikipedia.SzemeredisTheorem
