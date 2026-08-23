/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos1166.Erdos1166Core
import ErdosProblems.Erdos446.Moment

/-!
# The Appendix-A second-moment assembly

This file formalizes the finite combinatorial and probability-theoretic
assembly in the proof of HLOZ (A.3).  The source-specific one-point estimate
(Proposition A.3(1)), the Harnack/two-point estimate (Proposition A.3(2)), and
the final deterministic absorption of the close-pair polynomial are explicit
premises.  Everything after those estimates -- the successful-site sum,
first moment, separation-level decomposition, lattice shell count, close-pair
bound, and Paley--Zygmund step -- is proved here.
-/

namespace Erdos1166.HLOZAppendixASecondMoment

open MeasureTheory Set
open scoped BigOperators ENNReal NNReal

variable {Ω ι : Type*} [MeasurableSpace Ω]

/-- The finite sum of indicators of successful sites. -/
noncomputable def successfulSiteSum (U : Finset ι) (A : ι → Set Ω) (ω : Ω) : ℝ :=
  ∑ x ∈ U, (A x).indicator (fun _ ↦ (1 : ℝ)) ω

/-- The event that at least one site in `U` is successful. -/
def someSuccessful (U : Finset ι) (A : ι → Set Ω) : Set Ω :=
  ⋃ x ∈ U, A x

/-- The sum of the one-point probabilities, i.e. the first moment. -/
noncomputable def firstMoment (μ : Measure Ω) (U : Finset ι)
    (A : ι → Set Ω) : ℝ :=
  ∑ x ∈ U, μ.real (A x)

/-- The sum of all ordered two-point probabilities, i.e. the second moment. -/
noncomputable def pairMoment (μ : Measure Ω) (U : Finset ι)
    (A : ι → Set Ω) : ℝ :=
  ∑ x ∈ U, ∑ y ∈ U, μ.real (A x ∩ A y)

/-- Ordered pairs whose separation level is at most the cutoff. -/
noncomputable def separatedPairMoment (μ : Measure Ω) (U : Finset ι)
    (A : ι → Set Ω) (level : ι → ι → ℕ) (L : ℕ) : ℝ :=
  ∑ x ∈ U, ∑ y ∈ U.filter (fun y ↦ level x y ≤ L), μ.real (A x ∩ A y)

/-- Ordered pairs closer than the last scale used in the two-point estimate. -/
noncomputable def closePairMoment (μ : Measure Ω) (U : Finset ι)
    (A : ι → Set Ω) (level : ι → ι → ℕ) (L : ℕ) : ℝ :=
  ∑ x ∈ U, ∑ y ∈ U.filter (fun y ↦ L < level x y), μ.real (A x ∩ A y)

/-- The `l`-th separation shell about `x`. -/
noncomputable def separationShell (U : Finset ι)
    (level : ι → ι → ℕ) (x : ι) (l : ℕ) : Finset ι :=
  U.filter fun y ↦ level x y = l

theorem successfulSiteSum_nonneg (U : Finset ι) (A : ι → Set Ω) (ω : Ω) :
    0 ≤ successfulSiteSum U A ω := by
  classical
  apply Finset.sum_nonneg
  intro x hx
  by_cases hω : ω ∈ A x <;> simp [successfulSiteSum, hω]

theorem successfulSiteSum_pos_iff (U : Finset ι) (A : ι → Set Ω) (ω : Ω) :
    0 < successfulSiteSum U A ω ↔ ω ∈ someSuccessful U A := by
  classical
  simp only [successfulSiteSum, someSuccessful, Set.mem_iUnion]
  constructor
  · intro h
    by_contra hn
    push_neg at hn
    have hz : ∑ x ∈ U, (A x).indicator (fun _ ↦ (1 : ℝ)) ω = 0 := by
      apply Finset.sum_eq_zero
      intro x hx
      simp [hn x hx]
    linarith
  · rintro ⟨x, hxU, hωx⟩
    have hone : (A x).indicator (fun _ ↦ (1 : ℝ)) ω = 1 := by simp [hωx]
    have hle : (A x).indicator (fun _ ↦ (1 : ℝ)) ω ≤
        ∑ y ∈ U, (A y).indicator (fun _ ↦ (1 : ℝ)) ω := by
      exact Finset.single_le_sum
        (f := fun y ↦ (A y).indicator (fun _ ↦ (1 : ℝ)) ω) (s := U)
        (fun y hy ↦ by
          by_cases hω : ω ∈ A y
          · simp only [Set.indicator_of_mem hω]
            norm_num
          · simp only [Set.indicator_of_notMem hω]
            norm_num) hxU
    linarith

theorem integral_successfulSiteSum
    (μ : Measure Ω) [IsFiniteMeasure μ] (U : Finset ι) (A : ι → Set Ω)
    (hA : ∀ x ∈ U, MeasurableSet (A x)) :
    ∫ ω, successfulSiteSum U A ω ∂μ = firstMoment μ U A := by
  classical
  unfold successfulSiteSum firstMoment
  rw [integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro x hx
    exact integral_indicator_one (hA x hx)
  · intro x hx
    exact (integrableOn_const (measure_ne_top μ (A x))).integrable_indicator (hA x hx)

theorem integral_successfulSiteSum_sq
    (μ : Measure Ω) [IsFiniteMeasure μ] (U : Finset ι) (A : ι → Set Ω)
    (hA : ∀ x ∈ U, MeasurableSet (A x)) :
    ∫ ω, successfulSiteSum U A ω ^ 2 ∂μ = pairMoment μ U A := by
  classical
  let ind : ι → Ω → ℝ := fun x ω ↦ (A x).indicator (fun _ ↦ (1 : ℝ)) ω
  have hmul (x y : ι) (ω : Ω) :
      ind x ω * ind y ω = (A x ∩ A y).indicator (fun _ ↦ (1 : ℝ)) ω := by
    by_cases hx : ω ∈ A x <;> by_cases hy : ω ∈ A y <;> simp [ind, hx, hy]
  have hint (x y : ι) (hx : x ∈ U) (hy : y ∈ U) :
      Integrable (fun ω ↦ ind x ω * ind y ω) μ := by
    rw [show (fun ω ↦ ind x ω * ind y ω) =
        (A x ∩ A y).indicator (fun _ ↦ (1 : ℝ)) by
      funext ω; exact hmul x y ω]
    exact (integrableOn_const (measure_ne_top μ (A x ∩ A y))).integrable_indicator
      ((hA x hx).inter (hA y hy))
  calc
    ∫ ω, successfulSiteSum U A ω ^ 2 ∂μ =
        ∫ ω, ∑ x ∈ U, ∑ y ∈ U, ind x ω * ind y ω ∂μ := by
      apply integral_congr_ae
      filter_upwards [] with ω
      rw [successfulSiteSum, pow_two, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro x hx
      rw [Finset.mul_sum]
    _ = ∑ x ∈ U, ∑ y ∈ U, ∫ ω, ind x ω * ind y ω ∂μ := by
      rw [integral_finsetSum]
      · apply Finset.sum_congr rfl
        intro x hx
        rw [integral_finsetSum]
        exact fun y hy ↦ hint x y hx hy
      · intro x hx
        exact integrable_finsetSum U fun y hy ↦ hint x y hx hy
    _ = pairMoment μ U A := by
      rw [pairMoment]
      apply Finset.sum_congr rfl
      intro x hx
      apply Finset.sum_congr rfl
      intro y hy
      rw [show (fun ω ↦ ind x ω * ind y ω) =
          (A x ∩ A y).indicator (fun _ ↦ (1 : ℝ)) by
        funext ω; exact hmul x y ω]
      exact integral_indicator_one ((hA x hx).inter (hA y hy))

/-- Uniform one-point bounds turn directly into the source's
`I'_n ≍ K_n² Q_n` first-moment comparison. -/
theorem firstMoment_cardinality_scaling
    (μ : Measure Ω) (U : Finset ι) (A : ι → Set Ω)
    {q c : ℝ} (hq : 0 ≤ q) (hc : 0 ≤ c)
    (hone : ∀ x ∈ U, q ≤ μ.real (A x) ∧ μ.real (A x) ≤ c * q) :
    (U.card : ℝ) * q ≤ firstMoment μ U A ∧
      firstMoment μ U A ≤ (U.card : ℝ) * (c * q) := by
  classical
  constructor
  · calc
      (U.card : ℝ) * q = ∑ _x ∈ U, q := by simp
      _ ≤ firstMoment μ U A := by
        rw [firstMoment]
        exact Finset.sum_le_sum fun x hx ↦ (hone x hx).1
  · calc
      firstMoment μ U A ≤ ∑ _x ∈ U, c * q := by
        rw [firstMoment]
        exact Finset.sum_le_sum fun x hx ↦ (hone x hx).2
      _ = (U.card : ℝ) * (c * q) := by simp

/-! ### The finite source box `U_n` -/

/-- Integer-radius version of the source box
`U_n = [2 r_{n,0},3 r_{n,0}]²`.  Rounding the real radius is kept outside
this definition, so its cardinality is exact. -/
noncomputable def appendixSiteBox (R : ℕ) : Finset Site :=
  (Finset.Icc (2 * (R : ℤ)) (3 * (R : ℤ))).product
    (Finset.Icc (2 * (R : ℤ)) (3 * (R : ℤ)))

theorem card_appendixSiteBox (R : ℕ) :
    (appendixSiteBox R).card = (R + 1) ^ 2 := by
  have hinterval :
      (Finset.Icc (2 * (R : ℤ)) (3 * (R : ℤ))).card = R + 1 := by
    rw [Int.card_Icc]
    omega
  rw [appendixSiteBox]
  calc
    ((Finset.Icc (2 * (R : ℤ)) (3 * (R : ℤ))).product
        (Finset.Icc (2 * (R : ℤ)) (3 * (R : ℤ)))).card =
        (Finset.Icc (2 * (R : ℤ)) (3 * (R : ℤ))).card *
          (Finset.Icc (2 * (R : ℤ)) (3 * (R : ℤ))).card :=
      Finset.card_product _ _
    _ = (R + 1) ^ 2 := by rw [hinterval, pow_two]

/-- The random successful-site count over the source box. -/
noncomputable def appendixSuccessfulSiteSum
    (R : ℕ) (A : Site → Set Ω) (ω : Ω) : ℝ :=
  successfulSiteSum (appendixSiteBox R) A ω

/-- Exact source-box specialization of the first-moment scaling. -/
theorem firstMoment_appendixSiteBox_scaling
    (μ : Measure Ω) (R : ℕ) (A : Site → Set Ω)
    {q c : ℝ} (hq : 0 ≤ q) (hc : 0 ≤ c)
    (hone : ∀ x ∈ appendixSiteBox R,
      q ≤ μ.real (A x) ∧ μ.real (A x) ≤ c * q) :
    (((R + 1) ^ 2 : ℕ) : ℝ) * q ≤ firstMoment μ (appendixSiteBox R) A ∧
      firstMoment μ (appendixSiteBox R) A ≤
        (((R + 1) ^ 2 : ℕ) : ℝ) * (c * q) := by
  simpa [card_appendixSiteBox] using
    firstMoment_cardinality_scaling μ (appendixSiteBox R) A hq hc hone

/-- Exact split of the ordered second moment into separated and close pairs. -/
theorem pairMoment_eq_separated_add_close
    (μ : Measure Ω) (U : Finset ι) (A : ι → Set Ω)
    (level : ι → ι → ℕ) (L : ℕ) :
    pairMoment μ U A = separatedPairMoment μ U A level L +
      closePairMoment μ U A level L := by
  classical
  rw [pairMoment, separatedPairMoment, closePairMoment, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro x hx
  rw [← Finset.sum_filter_add_sum_filter_not
    (s := U) (p := fun y ↦ level x y ≤ L)
    (f := fun y ↦ μ.real (A x ∩ A y))]
  congr 1
  apply Finset.sum_congr
  · ext y
    simp
  · intro y hy
    rfl

/-- Exact regrouping of the separated inner sum by separation level. -/
theorem separated_inner_eq_sum_shells
    (μ : Measure Ω) (U : Finset ι) (A : ι → Set Ω)
    (level : ι → ι → ℕ) (L : ℕ) (x : ι) :
    (∑ y ∈ U.filter (fun y ↦ level x y ≤ L), μ.real (A x ∩ A y)) =
      ∑ l ∈ Finset.range (L + 1),
        ∑ y ∈ separationShell U level x l, μ.real (A x ∩ A y) := by
  classical
  have hmaps : ∀ y ∈ U.filter (fun y ↦ level x y ≤ L),
      level x y ∈ Finset.range (L + 1) := by
    intro y hy
    simp only [Finset.mem_filter] at hy
    simpa [Finset.mem_range] using Nat.lt_succ_of_le hy.2
  calc
    (∑ y ∈ U.filter (fun y ↦ level x y ≤ L), μ.real (A x ∩ A y)) =
        ∑ l ∈ Finset.range (L + 1),
          ∑ y ∈ (U.filter (fun y ↦ level x y ≤ L)).filter
            (fun y ↦ level x y = l), μ.real (A x ∩ A y) :=
      (Finset.sum_fiberwise_of_maps_to
        (s := U.filter (fun y ↦ level x y ≤ L))
        (t := Finset.range (L + 1)) hmaps
        (fun y ↦ μ.real (A x ∩ A y))).symm
    _ = ∑ l ∈ Finset.range (L + 1),
        ∑ y ∈ separationShell U level x l, μ.real (A x ∩ A y) := by
      apply Finset.sum_congr rfl
      intro l hl
      apply Finset.sum_congr
      · ext y
        have hlL : l ≤ L := Nat.le_of_lt_succ (by simpa using hl)
        simp [separationShell, hlL]
        omega
      · intro y hy
        rfl

/-! ## The elementary lattice shell count -/

/-- A square lattice neighborhood in the sup norm. -/
noncomputable def latticeSupBall (x : Site) (R : ℕ) : Finset Site :=
  (Finset.Icc (x.1 - R) (x.1 + R)).product
    (Finset.Icc (x.2 - R) (x.2 + R))

theorem card_latticeSupBall (x : Site) (R : ℕ) :
    (latticeSupBall x R).card = (2 * R + 1) ^ 2 := by
  have hcoord (z : ℤ) :
      (Finset.Icc (z - R) (z + R)).card = 2 * R + 1 := by
    rw [Int.card_Icc]
    have heq : z + (R : ℤ) + 1 - (z - (R : ℤ)) =
        ((2 * R + 1 : ℕ) : ℤ) := by
      push_cast
      ring
    rw [heq]
    omega
  rw [latticeSupBall]
  calc
    ((Finset.Icc (x.1 - R) (x.1 + R)).product
        (Finset.Icc (x.2 - R) (x.2 + R))).card =
        (Finset.Icc (x.1 - R) (x.1 + R)).card *
          (Finset.Icc (x.2 - R) (x.2 + R)).card :=
      Finset.card_product _ _
    _ = (2 * R + 1) ^ 2 := by rw [hcoord, hcoord]; ring

/-- If a separation shell is contained in the appropriate lattice
neighborhood, its cardinality has the expected quadratic bound. -/
theorem card_separationShell_le_square
    (U : Finset Site) (level : Site → Site → ℕ)
    (radius : ℕ → ℕ) (x : Site) (l : ℕ)
    (hcontained : ∀ y ∈ separationShell U level x l,
      y ∈ latticeSupBall x (radius l)) :
    (separationShell U level x l).card ≤ (2 * radius l + 1) ^ 2 := by
  rw [← card_latticeSupBall x (radius l)]
  exact Finset.card_le_card hcontained

/-- The source's `O(K_n² e^{-2l})` shell count, reduced to the explicit
radius comparison after the exact lattice cardinality calculation. -/
theorem card_separationShell_real_le_exp
    (U : Finset Site) (level : Site → Site → ℕ)
    (radius : ℕ → ℕ) (x : Site) (l : ℕ) {C Ksq : ℝ}
    (hcontained : ∀ y ∈ separationShell U level x l,
      y ∈ latticeSupBall x (radius l))
    (hradius : (((2 * radius l + 1) ^ 2 : ℕ) : ℝ) ≤
      C * Ksq * Real.exp (-2 * (l : ℝ))) :
    ((separationShell U level x l).card : ℝ) ≤
      C * Ksq * Real.exp (-2 * (l : ℝ)) := by
  have hnat := card_separationShell_le_square U level radius x l hcontained
  have hreal : ((separationShell U level x l).card : ℝ) ≤
      (((2 * radius l + 1) ^ 2 : ℕ) : ℝ) := by exact_mod_cast hnat
  exact hreal.trans hradius

/-- The two real source scales used in the shell count:
`K_n = 16 e^n n^9` and `r_{n,l-1} = e^{n-l+1} n^9`. -/
noncomputable def appendixKScale (n : ℕ) : ℝ :=
  16 * Real.exp (n : ℝ) * (n : ℝ) ^ 9

noncomputable def appendixShellScale (n l : ℕ) : ℝ :=
  Real.exp ((n : ℝ) - (l : ℝ) + 1) * (n : ℝ) ^ 9

/-- Integer radius enclosing the source disk of radius `2 r_{n,l-1}`. -/
noncomputable def roundedAppendixShellRadius (n l : ℕ) : ℕ :=
  ⌈2 * appendixShellScale n l⌉₊

theorem one_le_appendixShellScale {n l : ℕ} (hn : 1 ≤ n) (hl : l ≤ n + 1) :
    1 ≤ appendixShellScale n l := by
  have hlR : (l : ℝ) ≤ (n : ℝ) + 1 := by exact_mod_cast hl
  have hexponent : 0 ≤ (n : ℝ) - (l : ℝ) + 1 := by linarith
  have hexp : 1 ≤ Real.exp ((n : ℝ) - (l : ℝ) + 1) :=
    Real.one_le_exp hexponent
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hpow : 1 ≤ (n : ℝ) ^ 9 := one_le_pow₀ hnR
  unfold appendixShellScale
  nlinarith [mul_le_mul hexp hpow (by norm_num : (0 : ℝ) ≤ 1)
    (Real.exp_pos _).le]

/-- The fully explicit deterministic estimate behind
`#\{y:l(x,y)=l\}=O(K_n²e^{-2l})`.  The constant is intentionally coarse;
the point is that rounding the radius changes only the universal constant. -/
theorem roundedAppendixShellRadius_sq_le_exp
    {n l : ℕ} (hn : 1 ≤ n) (hl : l ≤ n + 1) :
    (((2 * roundedAppendixShellRadius n l + 1) ^ 2 : ℕ) : ℝ) ≤
      49 * Real.exp 2 * appendixKScale n ^ 2 *
        Real.exp (-2 * (l : ℝ)) := by
  let r := appendixShellScale n l
  have hr1 : 1 ≤ r := one_le_appendixShellScale hn hl
  have hr0 : 0 ≤ r := zero_le_one.trans hr1
  have hceil : ((roundedAppendixShellRadius n l : ℕ) : ℝ) < 2 * r + 1 := by
    simpa [roundedAppendixShellRadius, r] using
      (Nat.ceil_lt_add_one (show 0 ≤ 2 * r by positivity))
  have hlinear : (((2 * roundedAppendixShellRadius n l + 1 : ℕ) : ℝ)) ≤ 7 * r := by
    norm_num [Nat.cast_add, Nat.cast_mul]
    nlinarith
  have hsquare :
      (((2 * roundedAppendixShellRadius n l + 1) ^ 2 : ℕ) : ℝ) ≤
        49 * r ^ 2 := by
    have hbase0 : 0 ≤ (((2 * roundedAppendixShellRadius n l + 1 : ℕ) : ℝ)) := by
      positivity
    have := pow_le_pow_left₀ hbase0 hlinear 2
    norm_num [Nat.cast_pow] at this ⊢
    nlinarith
  have hexp :
      Real.exp 2 * Real.exp (n : ℝ) ^ 2 * Real.exp (-2 * (l : ℝ)) =
        Real.exp ((n : ℝ) - (l : ℝ) + 1) ^ 2 := by
    rw [← Real.exp_nat_mul, ← Real.exp_nat_mul]
    rw [← Real.exp_add, ← Real.exp_add]
    congr 1
    ring
  have hscaleEq :
      Real.exp 2 * appendixKScale n ^ 2 * Real.exp (-2 * (l : ℝ)) =
        256 * r ^ 2 := by
    unfold appendixKScale r appendixShellScale
    calc
      Real.exp 2 * (16 * Real.exp (n : ℝ) * (n : ℝ) ^ 9) ^ 2 *
          Real.exp (-2 * (l : ℝ)) =
          256 *
            (Real.exp 2 * Real.exp (n : ℝ) ^ 2 *
              Real.exp (-2 * (l : ℝ))) * ((n : ℝ) ^ 9) ^ 2 := by ring
      _ = 256 * (Real.exp ((n : ℝ) - (l : ℝ) + 1) * (n : ℝ) ^ 9) ^ 2 := by
        rw [hexp]
        ring
  calc
    (((2 * roundedAppendixShellRadius n l + 1) ^ 2 : ℕ) : ℝ) ≤
        49 * r ^ 2 := hsquare
    _ ≤ 49 * (Real.exp 2 * appendixKScale n ^ 2 *
        Real.exp (-2 * (l : ℝ))) := by
      rw [hscaleEq]
      nlinarith [sq_nonneg r]
    _ = 49 * Real.exp 2 * appendixKScale n ^ 2 *
        Real.exp (-2 * (l : ℝ)) := by ring

/-! ## Separated and close pair bounds -/

/-- A finite shell sum is bounded by its cardinality times a pointwise
majorant. -/
theorem sum_shell_le_card_mul
    (U : Finset ι) (level : ι → ι → ℕ)
    (x : ι) (l : ℕ) (f : ι → ℝ) {B : ℝ}
    (hB : ∀ y ∈ separationShell U level x l, f y ≤ B) :
    ∑ y ∈ separationShell U level x l, f y ≤
      ((separationShell U level x l).card : ℝ) * B := by
  calc
    ∑ y ∈ separationShell U level x l, f y ≤
        ∑ _y ∈ separationShell U level x l, B := Finset.sum_le_sum hB
    _ = ((separationShell U level x l).card : ℝ) * B := by simp

theorem exp_shell_cancellation (C Ksq E c q : ℝ) (l : ℕ) :
    (C * Ksq * Real.exp (-2 * (l : ℝ))) *
        (Real.exp (2 * (l : ℝ) + E) * (c * q) ^ 2) =
      C * Ksq * Real.exp E * (c * q) ^ 2 := by
  calc
    (C * Ksq * Real.exp (-2 * (l : ℝ))) *
        (Real.exp (2 * (l : ℝ) + E) * (c * q) ^ 2) =
        C * Ksq *
          (Real.exp (-2 * (l : ℝ)) * Real.exp (2 * (l : ℝ) + E)) *
            (c * q) ^ 2 := by ring
    _ = C * Ksq * Real.exp E * (c * q) ^ 2 := by
      rw [← Real.exp_add]
      congr 3
      ring

/-- Proposition A.3(2), uniform one-point comparability, and the geometric
shell count give the separated-pair contribution. -/
theorem separatedPairMoment_le_of_exp_shells
    (μ : Measure Ω) (U : Finset ι) (A : ι → Set Ω)
    (level : ι → ι → ℕ) (L : ℕ) {q c C Ksq E : ℝ}
    (hq : 0 ≤ q) (hc : 0 ≤ c) (hC : 0 ≤ C) (hK : 0 ≤ Ksq)
    (honeUpper : ∀ x ∈ U, μ.real (A x) ≤ c * q)
    (hshell : ∀ x ∈ U, ∀ l ≤ L,
      ((separationShell U level x l).card : ℝ) ≤
        C * Ksq * Real.exp (-2 * (l : ℝ)))
    (htwoPoint : ∀ x ∈ U, ∀ y ∈ U, level x y ≤ L →
      μ.real (A x ∩ A y) ≤
        Real.exp (2 * (level x y : ℝ) + E) *
          μ.real (A x) * μ.real (A y)) :
    separatedPairMoment μ U A level L ≤
      (U.card : ℝ) * (L + 1 : ℝ) *
        (C * Ksq * Real.exp E * (c * q) ^ 2) := by
  classical
  rw [separatedPairMoment]
  calc
    (∑ x ∈ U, ∑ y ∈ U.filter (fun y ↦ level x y ≤ L),
        μ.real (A x ∩ A y)) =
        ∑ x ∈ U, ∑ l ∈ Finset.range (L + 1),
          ∑ y ∈ separationShell U level x l, μ.real (A x ∩ A y) := by
      apply Finset.sum_congr rfl
      intro x hx
      exact separated_inner_eq_sum_shells μ U A level L x
    _ ≤ ∑ x ∈ U, ∑ l ∈ Finset.range (L + 1),
        C * Ksq * Real.exp E * (c * q) ^ 2 := by
      apply Finset.sum_le_sum
      intro x hx
      apply Finset.sum_le_sum
      intro l hl
      have hlL : l ≤ L := Nat.le_of_lt_succ (by simpa using hl)
      calc
        (∑ y ∈ separationShell U level x l, μ.real (A x ∩ A y)) ≤
            ((separationShell U level x l).card : ℝ) *
              (Real.exp (2 * (l : ℝ) + E) * (c * q) ^ 2) := by
          apply sum_shell_le_card_mul
          intro y hy
          have hyU : y ∈ U := (Finset.mem_filter.mp hy).1
          have hlev : level x y = l := (Finset.mem_filter.mp hy).2
          calc
            μ.real (A x ∩ A y) ≤
                Real.exp (2 * (level x y : ℝ) + E) *
                  μ.real (A x) * μ.real (A y) :=
              htwoPoint x hx y hyU (hlev.trans_le hlL)
            _ ≤ Real.exp (2 * (l : ℝ) + E) * (c * q) * (c * q) := by
              rw [hlev]
              exact mul_le_mul (mul_le_mul_of_nonneg_left
                (honeUpper x hx) (Real.exp_pos _).le)
                (honeUpper y hyU) (measureReal_nonneg) (by positivity)
            _ = Real.exp (2 * (l : ℝ) + E) * (c * q) ^ 2 := by ring
        _ ≤ (C * Ksq * Real.exp (-2 * (l : ℝ))) *
              (Real.exp (2 * (l : ℝ) + E) * (c * q) ^ 2) := by
          exact mul_le_mul_of_nonneg_right (hshell x hx l hlL) (by positivity)
        _ = C * Ksq * Real.exp E * (c * q) ^ 2 :=
          exp_shell_cancellation C Ksq E c q l
    _ = (U.card : ℝ) * (L + 1 : ℝ) *
        (C * Ksq * Real.exp E * (c * q) ^ 2) := by
      simp [mul_assoc]

/-- Close pairs need no two-point estimate: `A_x ∩ A_y ⊆ A_x` and a
uniform bound on the number of close neighbors suffice. -/
theorem closePairMoment_le
    (μ : Measure Ω) [IsFiniteMeasure μ] (U : Finset ι) (A : ι → Set Ω)
    (level : ι → ι → ℕ) (L : ℕ) {q c D : ℝ}
    (hq : 0 ≤ q) (hc : 0 ≤ c) (hD : 0 ≤ D)
    (honeUpper : ∀ x ∈ U, μ.real (A x) ≤ c * q)
    (hcloseCard : ∀ x ∈ U,
      ((U.filter (fun y ↦ L < level x y)).card : ℝ) ≤ D) :
    closePairMoment μ U A level L ≤ (U.card : ℝ) * D * (c * q) := by
  classical
  rw [closePairMoment]
  calc
    (∑ x ∈ U, ∑ y ∈ U.filter (fun y ↦ L < level x y),
        μ.real (A x ∩ A y)) ≤
        ∑ x ∈ U, D * (c * q) := by
      apply Finset.sum_le_sum
      intro x hx
      calc
        (∑ y ∈ U.filter (fun y ↦ L < level x y), μ.real (A x ∩ A y)) ≤
            ((U.filter (fun y ↦ L < level x y)).card : ℝ) * (c * q) := by
          calc
            (∑ y ∈ U.filter (fun y ↦ L < level x y), μ.real (A x ∩ A y)) ≤
                ∑ _y ∈ U.filter (fun y ↦ L < level x y), c * q := by
              apply Finset.sum_le_sum
              intro y hy
              exact (measureReal_mono inter_subset_left (measure_ne_top μ (A x))).trans
                (honeUpper x hx)
            _ = ((U.filter (fun y ↦ L < level x y)).card : ℝ) * (c * q) := by simp
        _ ≤ D * (c * q) :=
          mul_le_mul_of_nonneg_right (hcloseCard x hx) (mul_nonneg hc hq)
    _ = (U.card : ℝ) * D * (c * q) := by simp [mul_assoc]

/-! ## Paley--Zygmund and the complete Appendix-A assembly -/

/-- The support form of Paley--Zygmund for the successful-site sum. -/
theorem one_div_pair_coefficient_le_probability
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (U : Finset ι) (A : ι → Set Ω)
    (hA : ∀ x ∈ U, MeasurableSet (A x))
    {B : ℝ} (hB : 0 < B) (hfirst : 0 < firstMoment μ U A)
    (hpair : pairMoment μ U A ≤ B * firstMoment μ U A ^ 2) :
    1 / B ≤ μ.real (someSuccessful U A) := by
  have hsecond := Erdos446.finite_union_second_moment U A hA
    (fun x hx ↦ measure_ne_top μ (A x))
  rw [show (∑ x ∈ U, μ.real (A x)) = firstMoment μ U A by rfl,
    show (∑ x ∈ U, ∑ y ∈ U, μ.real (A x ∩ A y)) = pairMoment μ U A by rfl,
    show (⋃ x ∈ U, A x) = someSuccessful U A by rfl] at hsecond
  have hμ : 0 ≤ μ.real (someSuccessful U A) := measureReal_nonneg
  have hsq : 0 < firstMoment μ U A ^ 2 := sq_pos_of_pos hfirst
  have hscaled : firstMoment μ U A ^ 2 ≤
      (μ.real (someSuccessful U A) * B) * firstMoment μ U A ^ 2 := by
    calc
      firstMoment μ U A ^ 2 ≤
          μ.real (someSuccessful U A) * pairMoment μ U A := hsecond
      _ ≤ μ.real (someSuccessful U A) *
          (B * firstMoment μ U A ^ 2) :=
        mul_le_mul_of_nonneg_left hpair hμ
      _ = (μ.real (someSuccessful U A) * B) *
          firstMoment μ U A ^ 2 := by ring
  have hone : 1 ≤ μ.real (someSuccessful U A) * B := by
    nlinarith
  rw [div_le_iff₀ hB]
  simpa [mul_comm] using hone

/-- Complete checked form of the second-moment calculation proving (A.3).

`Ksq` represents `K_n²`; `q` is the infimum one-point mass; `Ccard`
compares `#U_n` with `K_n²`; `Cshell` is the geometric shell constant;
`Dclose` is the polynomial close-neighbor count.  `hcloseAbsorb` is exactly
the final deterministic use of Proposition A.3(1), namely that this
polynomial is swallowed by the first-moment exponential scale. -/
theorem appendixA_success_lower_bound
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (U : Finset ι) (A : ι → Set Ω)
    (level : ι → ι → ℕ) (L : ℕ)
    {q c Ksq Ccard Cshell Dclose E : ℝ}
    (hA : ∀ x ∈ U, MeasurableSet (A x))
    (hq : 0 < q) (hc : 0 ≤ c) (hK : 0 < Ksq)
    (hCcard : 0 ≤ Ccard) (hCshell : 0 ≤ Cshell) (hDclose : 0 ≤ Dclose)
    (hcardLower : Ksq ≤ (U.card : ℝ))
    (hcardUpper : (U.card : ℝ) ≤ Ccard * Ksq)
    (honePoint : ∀ x ∈ U,
      q ≤ μ.real (A x) ∧ μ.real (A x) ≤ c * q)
    (hshell : ∀ x ∈ U, ∀ l ≤ L,
      ((separationShell U level x l).card : ℝ) ≤
        Cshell * Ksq * Real.exp (-2 * (l : ℝ)))
    (htwoPoint : ∀ x ∈ U, ∀ y ∈ U, level x y ≤ L →
      μ.real (A x ∩ A y) ≤
        Real.exp (2 * (level x y : ℝ) + E) *
          μ.real (A x) * μ.real (A y))
    (hcloseCard : ∀ x ∈ U,
      ((U.filter (fun y ↦ L < level x y)).card : ℝ) ≤ Dclose)
    (hcloseAbsorb : Ccard * Dclose * c ≤ Real.exp E * (Ksq * q)) :
    1 / (Ccard * (L + 1 : ℝ) * Cshell * Real.exp E * c ^ 2 + Real.exp E) ≤
      μ.real (someSuccessful U A) := by
  classical
  let I := firstMoment μ U A
  let Bfar := Ccard * (L + 1 : ℝ) * Cshell * Real.exp E * c ^ 2
  let B := Bfar + Real.exp E
  have hq0 : 0 ≤ q := hq.le
  have hK0 : 0 ≤ Ksq := hK.le
  have hfirstBounds := firstMoment_cardinality_scaling μ U A hq0 hc honePoint
  have hKqpos : 0 < Ksq * q := mul_pos hK hq
  have hfirstLower : Ksq * q ≤ I := by
    exact (mul_le_mul_of_nonneg_right hcardLower hq0).trans hfirstBounds.1
  have hIpos : 0 < I := hKqpos.trans_le hfirstLower
  have hsep := separatedPairMoment_le_of_exp_shells μ U A level L
    hq0 hc hCshell hK0 (fun x hx ↦ (honePoint x hx).2) hshell htwoPoint
  have hsepB : separatedPairMoment μ U A level L ≤ Bfar * I ^ 2 := by
    calc
      separatedPairMoment μ U A level L ≤
          (U.card : ℝ) * (L + 1 : ℝ) *
            (Cshell * Ksq * Real.exp E * (c * q) ^ 2) := hsep
      _ ≤ (Ccard * Ksq) * (L + 1 : ℝ) *
            (Cshell * Ksq * Real.exp E * (c * q) ^ 2) := by
        have hnonneg : 0 ≤ (L + 1 : ℝ) *
            (Cshell * Ksq * Real.exp E * (c * q) ^ 2) := by positivity
        nlinarith
      _ = Bfar * (Ksq * q) ^ 2 := by
        dsimp [Bfar]
        ring
      _ ≤ Bfar * I ^ 2 := by
        have hBfar0 : 0 ≤ Bfar := by dsimp [Bfar]; positivity
        exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hKqpos.le hfirstLower 2) hBfar0
  have hclose := closePairMoment_le μ U A level L hq0 hc hDclose
    (fun x hx ↦ (honePoint x hx).2) hcloseCard
  have hcloseB : closePairMoment μ U A level L ≤ Real.exp E * I ^ 2 := by
    calc
      closePairMoment μ U A level L ≤
          (U.card : ℝ) * Dclose * (c * q) := hclose
      _ ≤ (Ccard * Ksq) * Dclose * (c * q) := by
        have hnonneg : 0 ≤ Dclose * (c * q) := by positivity
        nlinarith
      _ = (Ccard * Dclose * c) * (Ksq * q) := by ring
      _ ≤ (Real.exp E * (Ksq * q)) * (Ksq * q) :=
        mul_le_mul_of_nonneg_right hcloseAbsorb hKqpos.le
      _ = Real.exp E * (Ksq * q) ^ 2 := by ring
      _ ≤ Real.exp E * I ^ 2 :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hKqpos.le hfirstLower 2)
          (Real.exp_pos E).le
  have hpair : pairMoment μ U A ≤ B * I ^ 2 := by
    rw [pairMoment_eq_separated_add_close μ U A level L]
    calc
      separatedPairMoment μ U A level L + closePairMoment μ U A level L ≤
          Bfar * I ^ 2 + Real.exp E * I ^ 2 := add_le_add hsepB hcloseB
      _ = B * I ^ 2 := by dsimp [B]; ring
  have hBpos : 0 < B := by
    dsimp [B, Bfar]
    positivity
  simpa [I, B, Bfar] using
    one_div_pair_coefficient_le_probability μ U A hA hBpos hIpos hpair

/-- Complete second-moment bound before artificially absorbing the close
pairs into a scale-independent constant.  This is the quantitatively natural
form for the Appendix source: when the one-point mass is
`exp (-2n - o(n))`, the quotient `Dclose / (Ksq * q)` contributes exactly
the stretched-exponential term which Paley--Zygmund is meant to retain. -/
theorem appendixA_success_lower_bound_unabsorbed
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (U : Finset ι) (A : ι → Set Ω)
    (level : ι → ι → ℕ) (L : ℕ)
    {q c Ksq Ccard Cshell Dclose E : ℝ}
    (hA : ∀ x ∈ U, MeasurableSet (A x))
    (hq : 0 < q) (hc : 0 ≤ c) (hK : 0 < Ksq)
    (hCcard : 0 ≤ Ccard) (hCshell : 0 ≤ Cshell) (hDclose : 0 ≤ Dclose)
    (hcardLower : Ksq ≤ (U.card : ℝ))
    (hcardUpper : (U.card : ℝ) ≤ Ccard * Ksq)
    (honePoint : ∀ x ∈ U,
      q ≤ μ.real (A x) ∧ μ.real (A x) ≤ c * q)
    (hshell : ∀ x ∈ U, ∀ l ≤ L,
      ((separationShell U level x l).card : ℝ) ≤
        Cshell * Ksq * Real.exp (-2 * (l : ℝ)))
    (htwoPoint : ∀ x ∈ U, ∀ y ∈ U, level x y ≤ L →
      μ.real (A x ∩ A y) ≤
        Real.exp (2 * (level x y : ℝ) + E) *
          μ.real (A x) * μ.real (A y))
    (hcloseCard : ∀ x ∈ U,
      ((U.filter (fun y ↦ L < level x y)).card : ℝ) ≤ Dclose) :
    1 / (Ccard * (L + 1 : ℝ) * Cshell * Real.exp E * c ^ 2 +
          Real.exp E + Ccard * Dclose * c / (Ksq * q)) ≤
      μ.real (someSuccessful U A) := by
  classical
  let I := firstMoment μ U A
  let Bfar := Ccard * (L + 1 : ℝ) * Cshell * Real.exp E * c ^ 2
  let Bclose := Ccard * Dclose * c / (Ksq * q)
  let B := Bfar + Real.exp E + Bclose
  have hq0 : 0 ≤ q := hq.le
  have hK0 : 0 ≤ Ksq := hK.le
  have hfirstBounds := firstMoment_cardinality_scaling μ U A hq0 hc honePoint
  have hKqpos : 0 < Ksq * q := mul_pos hK hq
  have hfirstLower : Ksq * q ≤ I := by
    exact (mul_le_mul_of_nonneg_right hcardLower hq0).trans hfirstBounds.1
  have hIpos : 0 < I := hKqpos.trans_le hfirstLower
  have hsep := separatedPairMoment_le_of_exp_shells μ U A level L
    hq0 hc hCshell hK0 (fun x hx ↦ (honePoint x hx).2) hshell htwoPoint
  have hsepB : separatedPairMoment μ U A level L ≤ Bfar * I ^ 2 := by
    calc
      separatedPairMoment μ U A level L ≤
          (U.card : ℝ) * (L + 1 : ℝ) *
            (Cshell * Ksq * Real.exp E * (c * q) ^ 2) := hsep
      _ ≤ (Ccard * Ksq) * (L + 1 : ℝ) *
            (Cshell * Ksq * Real.exp E * (c * q) ^ 2) := by
        have hnonneg : 0 ≤ (L + 1 : ℝ) *
            (Cshell * Ksq * Real.exp E * (c * q) ^ 2) := by positivity
        nlinarith
      _ = Bfar * (Ksq * q) ^ 2 := by
        dsimp [Bfar]
        ring
      _ ≤ Bfar * I ^ 2 := by
        have hBfar0 : 0 ≤ Bfar := by dsimp [Bfar]; positivity
        exact mul_le_mul_of_nonneg_left
          (pow_le_pow_left₀ hKqpos.le hfirstLower 2) hBfar0
  have hclose := closePairMoment_le μ U A level L hq0 hc hDclose
    (fun x hx ↦ (honePoint x hx).2) hcloseCard
  have hBclose0 : 0 ≤ Bclose := by
    dsimp [Bclose]
    positivity
  have hcloseB : closePairMoment μ U A level L ≤ Bclose * I ^ 2 := by
    calc
      closePairMoment μ U A level L ≤
          (U.card : ℝ) * Dclose * (c * q) := hclose
      _ ≤ (Ccard * Ksq) * Dclose * (c * q) := by
        have hnonneg : 0 ≤ Dclose * (c * q) := by positivity
        nlinarith
      _ = (Ccard * Dclose * c) * (Ksq * q) := by ring
      _ = Bclose * (Ksq * q) ^ 2 := by
        dsimp [Bclose]
        field_simp [hKqpos.ne']
        <;> ring
      _ ≤ Bclose * I ^ 2 :=
        mul_le_mul_of_nonneg_left
          (pow_le_pow_left₀ hKqpos.le hfirstLower 2) hBclose0
  have hpair : pairMoment μ U A ≤ B * I ^ 2 := by
    rw [pairMoment_eq_separated_add_close μ U A level L]
    calc
      separatedPairMoment μ U A level L + closePairMoment μ U A level L ≤
          Bfar * I ^ 2 + Bclose * I ^ 2 := add_le_add hsepB hcloseB
      _ ≤ B * I ^ 2 := by
        dsimp [B]
        nlinarith [Real.exp_pos E, sq_nonneg I]
  have hBpos : 0 < B := by
    dsimp [B, Bfar]
    have : 0 ≤ Bclose := hBclose0
    positivity
  simpa [I, B, Bfar, Bclose] using
    one_div_pair_coefficient_le_probability μ U A hA hBpos hIpos hpair

/-- Exponential form of the A.1/A.3 conclusion. -/
theorem appendixA_success_lower_bound_exp
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (U : Finset ι) (A : ι → Set Ω) {B R : ℝ}
    (hA : ∀ x ∈ U, MeasurableSet (A x))
    (hB : 0 < B) (hfirst : 0 < firstMoment μ U A)
    (hpair : pairMoment μ U A ≤ B * firstMoment μ U A ^ 2)
    (hBR : B ≤ Real.exp R) :
    Real.exp (-R) ≤ μ.real (someSuccessful U A) := by
  have hpaley := one_div_pair_coefficient_le_probability μ U A hA hB hfirst hpair
  calc
    Real.exp (-R) = 1 / Real.exp R := by rw [Real.exp_neg]; ring
    _ ≤ 1 / B := by
      exact one_div_le_one_div_of_le hB hBR
    _ ≤ μ.real (someSuccessful U A) := hpaley

end Erdos1166.HLOZAppendixASecondMoment
