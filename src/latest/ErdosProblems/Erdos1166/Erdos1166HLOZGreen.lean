import ErdosProblems.Erdos1166.Erdos1166Core

namespace Erdos1166

open Filter MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal

/-- Partial sum of a finite iid increment block. -/
def blockPartialSum {m : ℕ} (η : Fin m → Direction) (r : Fin (m + 1)) : Site :=
  ∑ i : Fin r, directionStep (η ⟨i, by omega⟩)

/-- A finite increment block has no positive-time return to its starting site. -/
def blockNoReturn (m : ℕ) : Set (Fin m → Direction) :=
  {η | ∀ r : Fin (m + 1), 0 < r → blockPartialSum η r ≠ 0}

theorem measurableSet_blockNoReturn (m : ℕ) : MeasurableSet (blockNoReturn m) := by
  exact MeasurableSet.of_discrete

/-- No positive return to the origin through deterministic time `n`.  This is
the finite-time version of HLOZ's event `{H₀ > n}` (up to endpoint convention). -/
def noReturnThrough (n : ℕ) : Set (ℕ → Direction) :=
  {ω | ∀ r, 1 ≤ r → r ≤ n → simpleRandomWalk ω r ≠ 0}

theorem measurableSet_noReturnThrough (n : ℕ) : MeasurableSet (noReturnThrough n) := by
  have heq : noReturnThrough n =
      ⋂ r : ℕ, ⋂ (_ : 1 ≤ r), ⋂ (_ : r ≤ n),
        { ω : ℕ → Direction | simpleRandomWalk ω r ≠ 0 } := by
    ext ω
    simp [noReturnThrough]
  rw [heq]
  exact MeasurableSet.iInter fun r ↦ MeasurableSet.iInter fun _ ↦
    MeasurableSet.iInter fun _ ↦
      (measurableSet_eq_fun
        ((measurable_pi_apply r).comp measurable_simpleRandomWalk) measurable_const).compl

noncomputable def noReturnReal (n : ℕ) : ℝ :=
  incrementLaw.real (noReturnThrough n)

theorem noReturnReal_nonneg (n : ℕ) : 0 ≤ noReturnReal n :=
  measureReal_nonneg

theorem blockPartialSum_iidBlock_zero (m : ℕ) (ω : ℕ → Direction)
    (r : Fin (m + 1)) :
    blockPartialSum (iidBlock (X := Direction) 0 m ω) r = simpleRandomWalk ω r := by
  simp only [blockPartialSum, iidBlock, Nat.zero_add, simpleRandomWalk]
  exact Fin.sum_univ_eq_sum_range (fun i ↦ directionStep (ω i)) r

theorem iidBlock_zero_preimage_blockNoReturn (m : ℕ) :
    iidBlock (X := Direction) 0 m ⁻¹' blockNoReturn m = noReturnThrough m := by
  ext ω
  simp only [Set.mem_preimage, blockNoReturn, Set.mem_setOf_eq,
    noReturnThrough]
  constructor
  · intro h r hr1 hrm
    let r' : Fin (m + 1) := ⟨r, by omega⟩
    rw [← blockPartialSum_iidBlock_zero m ω r']
    apply h r'
    change 0 < r
    exact hr1
  · intro h r hr
    rw [blockPartialSum_iidBlock_zero m ω r]
    exact h r hr (Nat.le_of_lt_succ r.isLt)

theorem finitePi_blockNoReturn_eq_noReturn (m : ℕ) :
    (Measure.infinitePi fun _ : Fin m ↦ directionLaw) (blockNoReturn m) =
      incrementLaw (noReturnThrough m) := by
  rw [← iidBlock_map directionLaw 0 m]
  rw [Measure.map_apply (measurable_iidBlock 0 m) (measurableSet_blockNoReturn m)]
  exact congrArg incrementLaw (iidBlock_zero_preimage_blockNoReturn m)

theorem blockPartialSum_iidBlock_eq_walk_sub {n i j : ℕ}
    (hi : i ≤ j) (hj : j ≤ n) (ω : ℕ → Direction) :
    blockPartialSum (iidBlock (X := Direction) i (n - i) ω)
        ⟨j - i, by omega⟩ =
      simpleRandomWalk ω j - simpleRandomWalk ω i := by
  unfold blockPartialSum
  change (∑ k : Fin (j - i), directionStep (ω (i + (k : ℕ)))) = _
  rw [Fin.sum_univ_eq_sum_range (fun k ↦ directionStep (ω (i + k))) (j - i)]
  rw [← Finset.sum_Ico_eq_sum_range (fun k ↦ directionStep (ω k)) i j]
  exact Finset.sum_Ico_eq_sub (fun k ↦ directionStep (ω k)) hi

/-- The event that `j` is the last visit to the origin through time `n`,
written in a product-block form suitable for iid restart. -/
def lastZeroBlockEvent (n j : ℕ) : Set (ℕ → Direction) :=
  {ω | simpleRandomWalk ω j = 0} ∩
    iidBlock (X := Direction) j (n - j) ⁻¹' blockNoReturn (n - j)

theorem measurableSet_lastZeroBlockEvent (n j : ℕ) :
    MeasurableSet (lastZeroBlockEvent n j) := by
  exact (measurableSet_returnAt j).inter
    ((measurable_iidBlock j (n - j)) (measurableSet_blockNoReturn (n - j)))

theorem lastZeroBlockEvent_disjoint_of_lt {n i j : ℕ}
    (hj : j ≤ n) (hij : i < j) :
    Disjoint (lastZeroBlockEvent n i) (lastZeroBlockEvent n j) := by
  rw [Set.disjoint_left]
  intro ω hi hjEvent
  rcases hi with ⟨hi0, hiNo⟩
  rcases hjEvent with ⟨hj0, _⟩
  let r : Fin (n - i + 1) := ⟨j - i, by omega⟩
  have hsum : blockPartialSum (iidBlock (X := Direction) i (n - i) ω)
      r = 0 := by
    change blockPartialSum (iidBlock (X := Direction) i (n - i) ω)
      ⟨j - i, by omega⟩ = 0
    rw [blockPartialSum_iidBlock_eq_walk_sub (Nat.le_of_lt hij) hj ω, hi0, hj0]
    simp
  exact (hiNo r (by
    change 0 < j - i
    omega)) hsum

theorem pairwiseDisjoint_lastZeroBlockEvent (n : ℕ) :
    Set.PairwiseDisjoint (↑(Finset.range (n + 1))) (lastZeroBlockEvent n) := by
  intro i hi j hj hij
  have hin : i ≤ n := by
    exact Nat.le_of_lt_succ (Finset.mem_range.mp hi)
  have hjn : j ≤ n := by
    exact Nat.le_of_lt_succ (Finset.mem_range.mp hj)
  rcases lt_or_gt_of_ne hij with hij' | hji'
  · exact lastZeroBlockEvent_disjoint_of_lt hjn hij'
  · exact (lastZeroBlockEvent_disjoint_of_lt hin hji').symm

theorem iUnion_lastZeroBlockEvent (n : ℕ) :
    (⋃ j ∈ Finset.range (n + 1), lastZeroBlockEvent n j) = Set.univ := by
  apply Set.eq_univ_of_forall
  intro ω
  let Z := (Finset.range (n + 1)).filter fun j ↦ simpleRandomWalk ω j = 0
  have hZ : Z.Nonempty := by
    refine ⟨0, ?_⟩
    rw [Finset.mem_filter]
    constructor
    · simp
    · simp [simpleRandomWalk]
  let j := Z.max' hZ
  have hjZ : j ∈ Z := Z.max'_mem hZ
  have hjn : j ≤ n := by
    have := (Finset.mem_filter.mp hjZ).1
    simp only [Finset.mem_range] at this
    omega
  apply Set.mem_iUnion.mpr
  refine ⟨j, Set.mem_iUnion.mpr ⟨?_, ?_⟩⟩
  · simp only [Finset.mem_range]
    omega
  · refine ⟨(Finset.mem_filter.mp hjZ).2, ?_⟩
    intro r hr
    have hrpos : 0 < (r : ℕ) := hr
    intro hsum
    have hwalk : simpleRandomWalk ω (j + r) = 0 := by
      have hdiff := blockPartialSum_iidBlock_eq_walk_sub
        (n := n) (i := j) (j := j + r) (by omega) (by omega) ω
      have hrFin : (⟨j + (r : ℕ) - j, by omega⟩ : Fin (n - j + 1)) = r := by
        apply Fin.ext
        simp
      rw [hrFin, hsum, (Finset.mem_filter.mp hjZ).2] at hdiff
      simpa using hdiff.symm
    have hjrZ : j + r ∈ Z := by
      rw [Finset.mem_filter]
      exact ⟨by simp only [Finset.mem_range]; omega, hwalk⟩
    have := Z.le_max' (j + r) hjrZ
    omega

/-- Exact iid factorization of a last-exit summand. -/
theorem measureReal_lastZeroBlockEvent (n j : ℕ) :
    incrementLaw.real (lastZeroBlockEvent n j) =
      returnProb j * noReturnReal (n - j) := by
  have hpast : MeasurableSet[iidHistory (X := Direction) j]
      {ω : ℕ → Direction | simpleRandomWalk ω j = 0} := by
    exact measurableSet_eq_fun
      (HLOZFoundation.measurable_simpleRandomWalk_time_iidHistory (j := j) (k := j) le_rfl)
      measurable_const
  have hprod := measure_inter_iidBlock_eq_mul directionLaw j (n - j)
    hpast (measurableSet_blockNoReturn (n - j))
  have hprod' : incrementLaw (lastZeroBlockEvent n j) =
      incrementLaw {ω : ℕ → Direction | simpleRandomWalk ω j = 0} *
        (Measure.infinitePi fun _ : Fin (n - j) ↦ directionLaw)
          (blockNoReturn (n - j)) := by
    simpa only [incrementLaw, lastZeroBlockEvent] using hprod
  rw [measureReal_def, hprod', ENNReal.toReal_mul,
    ← measureReal_def, finitePi_blockNoReturn_eq_noReturn,
    ← measureReal_def]
  rfl

/-- Finite last-exit renewal identity.  This is the exact discrete identity
underlying the first-return estimate (2.1) of HLOZ Lemma 2.1. -/
theorem finite_lastExit_renewal (n : ℕ) :
    ∑ j ∈ Finset.range (n + 1), returnProb j * noReturnReal (n - j) = 1 := by
  calc
    ∑ j ∈ Finset.range (n + 1), returnProb j * noReturnReal (n - j) =
        ∑ j ∈ Finset.range (n + 1),
          incrementLaw.real (lastZeroBlockEvent n j) := by
      apply Finset.sum_congr rfl
      intro j _
      exact (measureReal_lastZeroBlockEvent n j).symm
    _ = incrementLaw.real
        (⋃ j ∈ Finset.range (n + 1), lastZeroBlockEvent n j) := by
      symm
      exact measureReal_biUnion_finset (pairwiseDisjoint_lastZeroBlockEvent n)
        (fun j _ ↦ measurableSet_lastZeroBlockEvent n j)
    _ = incrementLaw.real Set.univ := by rw [iUnion_lastZeroBlockEvent]
    _ = 1 := by simp

theorem noReturnThrough_antitone : Antitone noReturnThrough := by
  intro m n hmn ω hω r hr1 hrm
  exact hω r hr1 (hrm.trans hmn)

theorem noReturnReal_antitone : Antitone noReturnReal := by
  intro m n hmn
  exact measureReal_mono (noReturnThrough_antitone hmn)
    (measure_ne_top incrementLaw (noReturnThrough m))

/-- Exact finite Green/survival inequality
`P(H₀ > n) * G_n(0,0) ≤ 1`. -/
theorem noReturnReal_mul_finiteGreen_le_one (n : ℕ) :
    noReturnReal n * (∑ j ∈ Finset.range (n + 1), returnProb j) ≤ 1 := by
  rw [Finset.mul_sum]
  calc
    ∑ j ∈ Finset.range (n + 1), noReturnReal n * returnProb j ≤
        ∑ j ∈ Finset.range (n + 1),
          returnProb j * noReturnReal (n - j) := by
      apply Finset.sum_le_sum
      intro j hj
      rw [mul_comm (noReturnReal n) (returnProb j)]
      apply mul_le_mul_of_nonneg_left
      · apply noReturnReal_antitone
        exact Nat.sub_le n j
      · exact returnProb_nonneg j
    _ = 1 := finite_lastExit_renewal n

/-- Explicit finite-time version of the upper half of the order estimate in
HLOZ Lemma 2.1(2.1).  Our endpoint convention is `{H₀ > n}`. -/
theorem noReturnReal_even_le_four_div_harmonic (k : ℕ) :
    noReturnReal (2 * (k + 1)) ≤ 4 / (harmonic (k + 1) : ℝ) := by
  let n := 2 * (k + 1)
  let G := ∑ j ∈ Finset.range (n + 1), returnProb j
  have hgreen : (1 / 4 : ℝ) * (harmonic (k + 1) : ℝ) ≤ G := by
    have h := quarter_harmonic_le_returnMean k
    rw [integral_returnCount] at h
    exact h
  have hsurv := noReturnReal_mul_finiteGreen_le_one n
  have hmul : noReturnReal n * ((1 / 4 : ℝ) * (harmonic (k + 1) : ℝ)) ≤ 1 :=
    (mul_le_mul_of_nonneg_left hgreen (noReturnReal_nonneg n)).trans hsurv
  have hHrat : (0 : ℚ) < harmonic (k + 1) := harmonic_pos (by omega)
  have hH : (0 : ℝ) < (harmonic (k + 1) : ℝ) := by exact_mod_cast hHrat
  dsimp only [n] at hmul ⊢
  apply (le_div_iff₀ hH).2
  nlinarith

theorem noReturnReal_even_le_four_div_log (k : ℕ) :
    noReturnReal (2 * (k + 1)) ≤ 4 / Real.log (k + 2 : ℝ) := by
  have hHrat : (0 : ℚ) < harmonic (k + 1) := harmonic_pos (by omega)
  have hH : (0 : ℝ) < (harmonic (k + 1) : ℝ) := by exact_mod_cast hHrat
  have hlog : Real.log (k + 2 : ℝ) ≤ (harmonic (k + 1) : ℝ) := by
    have harg : (((k + 1 : ℕ) : ℝ) + 1) = (k + 2 : ℝ) := by
      push_cast
      ring
    rw [← harg]
    simpa only [Nat.cast_add, Nat.cast_one] using
      log_add_one_le_harmonic (k + 1)
  have hlogpos : 0 < Real.log (k + 2 : ℝ) := by
    apply Real.log_pos
    exact_mod_cast (show 1 < k + 2 by omega)
  exact (noReturnReal_even_le_four_div_harmonic k).trans
    ((div_le_div_iff₀ hH hlogpos).2 (by nlinarith))

/-- All-time finite-horizon form: for `n ≥ 2`, compare with the largest even
horizon below `n`. -/
theorem noReturnReal_le_four_div_log_half {n : ℕ} (hn : 2 ≤ n) :
    noReturnReal n ≤ 4 / Real.log ((n / 2 + 1 : ℕ) : ℝ) := by
  let k := n / 2 - 1
  have hhalf : 1 ≤ n / 2 := by omega
  have hk : k + 1 = n / 2 := by
    dsimp only [k]
    omega
  have heven : 2 * (k + 1) ≤ n := by
    rw [hk]
    omega
  calc
    noReturnReal n ≤ noReturnReal (2 * (k + 1)) :=
      noReturnReal_antitone heven
    _ ≤ 4 / Real.log (k + 2 : ℝ) := noReturnReal_even_le_four_div_log k
    _ = 4 / Real.log ((n / 2 + 1 : ℕ) : ℝ) := by
      have hknat : k + 2 = n / 2 + 1 := by omega
      have hreal : (k : ℝ) + 2 = ((n / 2 + 1 : ℕ) : ℝ) := by
        exact_mod_cast hknat
      rw [hreal]

/-- Free (unkilled) finite-time Green function at the origin. -/
noncomputable def freeFiniteGreen (n : ℕ) : ℝ :=
  ∑ j ∈ Finset.range (n + 1), returnProb j

/-- Explicit two-sided finite Green bounds available from the exact planar
return formula.  This is the time-horizon analogue of the Green estimates
recorded immediately before HLOZ Lemma 2.1. -/
theorem freeFiniteGreen_even_two_sided (k : ℕ) :
    (1 / 4 : ℝ) * (harmonic (k + 1) : ℝ) ≤
        freeFiniteGreen (2 * (k + 1)) ∧
      freeFiniteGreen (2 * (k + 1)) ≤
        2 * (1 + Real.log ((2 * (k + 1) + 1 : ℕ) : ℝ)) := by
  constructor
  · have h := quarter_harmonic_le_returnMean k
    rw [integral_returnCount] at h
    exact h
  · have h := CollisionKernel.sum_returnKernel_le (2 * (k + 1))
    change (∑ d : Fin (2 * (k + 1) + 1), returnProb d) ≤ _ at h
    rw [Fin.sum_univ_eq_sum_range] at h
    simpa only [freeFiniteGreen, Nat.cast_add, Nat.cast_one] using h

/-! ### Quantitative planar return estimate

The exact planar return probability can be expressed through the finite
Wallis product.  Mathlib's two-sided Wallis inequalities then give a local
central-limit estimate with an explicit summable remainder. -/

theorem centralBinom_sq_div_sixteen_mul_wallis (j : ℕ) :
    ((((2 * j).choose j : ℝ) ^ 2) / (16 : ℝ) ^ j) *
        (((2 * j + 1 : ℕ) : ℝ) * Real.Wallis.W j) = 1 := by
  have hfacNat : (2 * j).choose j * j.factorial * j.factorial = (2 * j).factorial := by
    have hsub : 2 * j - j = j := by omega
    simpa only [hsub] using
      (Nat.choose_mul_factorial_mul_factorial (show j ≤ 2 * j by omega))
  have hfac :
      (((2 * j).choose j : ℝ) * (j.factorial : ℝ) * (j.factorial : ℝ)) =
        ((2 * j).factorial : ℝ) := by
    exact_mod_cast hfacNat
  rw [Real.Wallis.W_eq_factorial_ratio]
  push_cast
  field_simp
  have hpow : (2 : ℝ) ^ (4 * j) = 16 ^ j := by
    rw [pow_mul]
    norm_num
  rw [hpow]
  calc
    (((2 * j).choose j : ℝ) ^ 2 * 16 ^ j * (j.factorial : ℝ) ^ 4) =
        16 ^ j *
          (((2 * j).choose j : ℝ) * (j.factorial : ℝ) * (j.factorial : ℝ)) ^ 2 := by
      ring
    _ = 16 ^ j * ((2 * j).factorial : ℝ) ^ 2 := by rw [hfac]

theorem centralBinom_sq_div_sixteen_eq_wallis_inv (j : ℕ) :
    (((2 * j).choose j : ℝ) ^ 2) / (16 : ℝ) ^ j =
      ((((2 * j + 1 : ℕ) : ℝ) * Real.Wallis.W j))⁻¹ := by
  exact eq_inv_of_mul_eq_one_left (centralBinom_sq_div_sixteen_mul_wallis j)

/-- Exact expression of the even-time planar return probability through the
finite Wallis product. -/
theorem returnProb_even_eq_wallis_inv (j : ℕ) :
    returnProb (2 * j) =
      ((((2 * j + 1 : ℕ) : ℝ) * Real.Wallis.W j))⁻¹ := by
  rw [returnProb, return_real_even]
  have hpow : (4 : ℝ) ^ (2 * j) = 16 ^ j := by
    rw [pow_mul]
    norm_num
  rw [hpow, centralBinom_sq_div_sixteen_eq_wallis_inv]

theorem two_div_pi_mul_succ_le_returnProb_even (j : ℕ) :
    2 / (Real.pi * ((2 * j + 1 : ℕ) : ℝ)) ≤ returnProb (2 * j) := by
  rw [returnProb_even_eq_wallis_inv]
  calc
    2 / (Real.pi * ((2 * j + 1 : ℕ) : ℝ)) =
        1 / (((2 * j + 1 : ℕ) : ℝ) * (Real.pi / 2)) := by
      field_simp
    _ ≤ 1 / (((2 * j + 1 : ℕ) : ℝ) * Real.Wallis.W j) := by
      apply one_div_le_one_div_of_le
        (mul_pos (by positivity) (Real.Wallis.W_pos j))
      exact mul_le_mul_of_nonneg_left (Real.Wallis.W_le j) (by positivity)
    _ = ((((2 * j + 1 : ℕ) : ℝ) * Real.Wallis.W j))⁻¹ := by
      rw [one_div]

theorem returnProb_even_le_one_div_pi_mul (j : ℕ) (hj : 1 ≤ j) :
    returnProb (2 * j) ≤ 1 / (Real.pi * (j : ℝ)) := by
  rw [returnProb_even_eq_wallis_inv]
  let a : ℝ := ((2 * j + 1 : ℕ) : ℝ)
  let b : ℝ := ((2 * j + 2 : ℕ) : ℝ)
  have ha : 0 < a := by dsimp [a]; positivity
  have hb : 0 < b := by dsimp [b]; positivity
  have hwallis : a / b * (Real.pi / 2) ≤ Real.Wallis.W j := by
    simpa [a, b, Nat.cast_add, Nat.cast_mul] using Real.Wallis.le_W j
  have hdenLower : a * (a / b * (Real.pi / 2)) ≤ a * Real.Wallis.W j :=
    mul_le_mul_of_nonneg_left hwallis ha.le
  have hjreal : (1 : ℝ) ≤ j := by exact_mod_cast hj
  have hcompare : Real.pi * (j : ℝ) ≤ a * (a / b * (Real.pi / 2)) := by
    dsimp [a, b]
    push_cast
    field_simp
    nlinarith [Real.pi_pos]
  calc
    (a * Real.Wallis.W j)⁻¹ ≤
        (a * (a / b * (Real.pi / 2)))⁻¹ := by
      simpa only [one_div] using one_div_le_one_div_of_le (by positivity) hdenLower
    _ ≤ (Real.pi * (j : ℝ))⁻¹ := by
      simpa only [one_div] using
        one_div_le_one_div_of_le (mul_pos Real.pi_pos (by positivity)) hcompare
    _ = 1 / (Real.pi * (j : ℝ)) := by rw [one_div]

/-- Quantitative local central-limit estimate for planar returns, with an
explicit remainder sharper than `1 / j²`. -/
theorem returnProb_even_localCLT_abs_le (j : ℕ) (hj : 1 ≤ j) :
    |returnProb (2 * j) - 1 / (Real.pi * (j : ℝ))| ≤
      1 / (Real.pi * (j : ℝ) * ((2 * j + 1 : ℕ) : ℝ)) := by
  have hu := returnProb_even_le_one_div_pi_mul j hj
  have hl := two_div_pi_mul_succ_le_returnProb_even j
  rw [abs_of_nonpos (sub_nonpos.mpr hu)]
  calc
    -(returnProb (2 * j) - 1 / (Real.pi * (j : ℝ))) =
        1 / (Real.pi * (j : ℝ)) - returnProb (2 * j) := by ring
    _ ≤ 1 / (Real.pi * (j : ℝ)) -
        2 / (Real.pi * ((2 * j + 1 : ℕ) : ℝ)) := by
      exact sub_le_sub_left hl _
    _ = 1 / (Real.pi * (j : ℝ) * ((2 * j + 1 : ℕ) : ℝ)) := by
      push_cast
      field_simp
      all_goals norm_num

/-- Convenient `C / j²` form of `returnProb_even_localCLT_abs_le`, with
the explicit constant `C = 1`. -/
theorem returnProb_even_localCLT_abs_le_inv_sq (j : ℕ) (hj : 1 ≤ j) :
    |returnProb (2 * j) - 1 / (Real.pi * (j : ℝ))| ≤ 1 / (j : ℝ) ^ 2 := by
  refine (returnProb_even_localCLT_abs_le j hj).trans ?_
  have hjpos : (0 : ℝ) < j := by exact_mod_cast (show 0 < j by omega)
  have hcast : (j : ℝ) ≤ ((2 * j + 1 : ℕ) : ℝ) := by
    exact_mod_cast (show j ≤ 2 * j + 1 by omega)
  have hpi : (1 : ℝ) ≤ Real.pi :=
    (by norm_num : (1 : ℝ) ≤ 3).trans Real.pi_gt_three.le
  have hden : (j : ℝ) ^ 2 ≤
      Real.pi * (j : ℝ) * ((2 * j + 1 : ℕ) : ℝ) := by
    calc
      (j : ℝ) ^ 2 = (j : ℝ) * (j : ℝ) := by ring
      _ ≤ (j : ℝ) * ((2 * j + 1 : ℕ) : ℝ) :=
        mul_le_mul_of_nonneg_left hcast hjpos.le
      _ ≤ (Real.pi * (j : ℝ)) * ((2 * j + 1 : ℕ) : ℝ) := by
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        simpa only [one_mul] using mul_le_mul_of_nonneg_right hpi hjpos.le
  exact one_div_le_one_div_of_le (sq_pos_of_pos hjpos) hden

/-- The local central-limit remainders along the positive even times are
absolutely summable. -/
theorem summable_returnProb_even_localCLTRemainder :
    Summable (fun j : ℕ ↦
      |returnProb (2 * (j + 1)) -
        1 / (Real.pi * ((j + 1 : ℕ) : ℝ))|) := by
  have hs0 : Summable (fun j : ℕ ↦ 1 / (j : ℝ) ^ 2) :=
    Real.summable_one_div_nat_pow.mpr (by norm_num)
  have hs : Summable (fun j : ℕ ↦ 1 / ((j + 1 : ℕ) : ℝ) ^ 2) := by
    simpa only [Nat.cast_add, Nat.cast_one] using (summable_nat_add_iff 1).mpr hs0
  exact Summable.of_nonneg_of_le
    (fun _ ↦ abs_nonneg _)
    (fun j ↦ returnProb_even_localCLT_abs_le_inv_sq (j + 1) (by omega)) hs

end Erdos1166
