/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos1166.Erdos1166HLOZProp45Theta

/-!
The top-level (`a=m`), unprimed `Theta^-` source-clock component used in
HLOZ Proposition 4.5, equations (4.21)--(4.24).  Unlike
`Erdos1166HLOZProp45Theta`, this file uses the capped external profile
`dotΞ_m` at the deterministic external horizon.  The stopped-event inclusion
and its concrete holding-prefix realization are recorded below the
probability estimate; the exact Proposition 4.2 conditional law remains an
explicit, accurately typed premise.  The arbitrary-`a` lower branch is in
`Erdos1166HLOZProp45SourceInterval`; neither file claims the `Theta^+` or
primed estimate.
-/

open MeasureTheory Set ProbabilityTheory Filter
open scoped ENNReal BigOperators

namespace Erdos1166.HLOZProp45SourceClock

open HLOZFoundation HLOZUrn

noncomputable def sourceKappa : ℝ := 17 / 50
noncomputable def sourceRateExponent : ℝ := 1 - 2 * sourceKappa
noncomputable def sourceRate (m : ℕ) : ℝ := (m : ℝ) ^ sourceRateExponent
noncomputable def sourceNearWidth (m : ℕ) : ℝ := 10 * (m : ℝ) ^ (1 - sourceKappa)
noncomputable def sourceFarWidth (m : ℕ) : ℝ := 10 * (m : ℝ) ^ (3 / 4 : ℝ)
noncomputable def sourceNearDeviation (m : ℕ) : ℝ := (16 / 15 : ℝ) * sourceNearWidth m
noncomputable def sourceFarDeviation (m : ℕ) : ℝ := (16 / 15 : ℝ) * sourceFarWidth m
noncomputable def sourceLowCutReal (m : ℕ) : ℝ :=
  (15 / 16 : ℝ) * m - sourceNearWidth m
noncomputable def sourceSplitCutReal (m : ℕ) : ℝ :=
  (15 / 16 : ℝ) * m - sourceFarWidth m
noncomputable def sourceLowCut (m : ℕ) : ℕ :=
  Nat.floor (max (sourceLowCutReal m) 0)
noncomputable def sourceSplitCut (m : ℕ) : ℕ :=
  Nat.floor (max (sourceSplitCutReal m) 0)

noncomputable def sourceProp44Threshold (m : ℕ) : ℝ :=
  (15 / 16 : ℝ) * m - (m : ℝ) ^ (4 / 5 : ℝ)

@[simp] lemma sourceRateExponent_eq : sourceRateExponent = (8 : ℝ) / 25 := by
  norm_num [sourceRateExponent, sourceKappa]

/-- A local power-comparison lemma, kept here so the source-clock helper does
not depend on the later screening-parameter assembly. -/
lemma eventually_const_mul_nat_rpow_le_const_mul_nat_rpow
    {C d p q : ℝ} (_hC : 0 ≤ C) (hd : 0 < d) (hpq : p < q) :
    ∀ᶠ m : ℕ in atTop, C * (m : ℝ) ^ p ≤ d * (m : ℝ) ^ q := by
  have hpow : Tendsto (fun m : ℕ ↦ (m : ℝ) ^ (q - p)) atTop atTop :=
    (tendsto_rpow_atTop (sub_pos.mpr hpq)).comp
      (tendsto_natCast_atTop_atTop (R := ℝ))
  have hlarge := hpow.eventually (eventually_ge_atTop (C / d))
  filter_upwards [hlarge, eventually_ge_atTop 1] with m hm hm1
  have hmpos : 0 < (m : ℝ) := by exact_mod_cast (show 0 < m by omega)
  have hratio : C ≤ d * (m : ℝ) ^ (q - p) := by
    simpa only [mul_comm] using (div_le_iff₀ hd).mp hm
  calc
    C * (m : ℝ) ^ p ≤ (d * (m : ℝ) ^ (q - p)) * (m : ℝ) ^ p := by
      gcongr
    _ = d * ((m : ℝ) ^ (q - p) * (m : ℝ) ^ p) := by ring
    _ = d * (m : ℝ) ^ q := by
      rw [← Real.rpow_add hmpos]
      congr 2
      ring

lemma sourceNearExponentBase (m : ℕ) (hm : 1 ≤ m) :
    17 * sourceRate m ≤ sourceNearDeviation m ^ 2 / (4 * (m : ℝ)) := by
  have hmR : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
  have hp : ((m : ℝ) ^ (1 - sourceKappa)) ^ (2 : ℝ) =
      (m : ℝ) ^ (2 * (1 - sourceKappa)) := by
    rw [← Real.rpow_mul (le_of_lt hmR)]
    ring_nf
  have hmul : (m : ℝ) ^ sourceRateExponent * (m : ℝ) =
      (m : ℝ) ^ (2 * (1 - sourceKappa)) := by
    calc
      (m : ℝ) ^ sourceRateExponent * (m : ℝ) =
          (m : ℝ) ^ (sourceRateExponent + 1) := by
            rw [Real.rpow_add hmR, Real.rpow_one]
      _ = (m : ℝ) ^ (2 * (1 - sourceKappa)) := by
        norm_num [sourceRateExponent_eq, sourceKappa]
  rw [sourceNearDeviation, sourceNearWidth, sourceRate]
  rw [show (16 / 15 * (10 * (m : ℝ) ^ (1 - sourceKappa))) ^ 2 =
      (16 / 15 : ℝ) ^ 2 * 100 *
        (((m : ℝ) ^ (1 - sourceKappa)) ^ (2 : ℝ)) by
          rw [Real.rpow_two]
          ring]
  rw [hp]
  rw [← hmul]
  apply (le_div_iff₀ (by positivity : (0 : ℝ) < 4 * m)).2
  have hpow : 0 ≤ (m : ℝ) ^ sourceRateExponent := by positivity
  have hprod : 0 < (m : ℝ) ^ sourceRateExponent * (m : ℝ) := by positivity
  norm_num
  have hprod' : 0 < (m : ℝ) ^ (8 / 25 : ℝ) * (m : ℝ) := by positivity
  nlinarith

lemma sourceFarQuadraticBase (m : ℕ) (hm : 1 ≤ m) :
    17 * Real.sqrt (m : ℝ) ≤ sourceFarDeviation m ^ 2 / (4 * (m : ℝ)) := by
  have hmR : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
  have hp : ((m : ℝ) ^ (3 / 4 : ℝ)) ^ (2 : ℝ) =
      (m : ℝ) ^ (3 / 2 : ℝ) := by
    rw [← Real.rpow_mul (le_of_lt hmR)]
    norm_num
  have hsqrt : Real.sqrt (m : ℝ) = (m : ℝ) ^ (1 / 2 : ℝ) := by
    rw [Real.sqrt_eq_rpow]
  have hmul : (m : ℝ) ^ (1 / 2 : ℝ) * (m : ℝ) =
      (m : ℝ) ^ (3 / 2 : ℝ) := by
    calc
      (m : ℝ) ^ (1 / 2 : ℝ) * (m : ℝ) =
          (m : ℝ) ^ ((1 / 2 : ℝ) + 1) := by
            rw [Real.rpow_add hmR, Real.rpow_one]
      _ = (m : ℝ) ^ (3 / 2 : ℝ) := by norm_num
  rw [sourceFarDeviation, sourceFarWidth, hsqrt]
  rw [show (16 / 15 * (10 * (m : ℝ) ^ (3 / 4 : ℝ))) ^ 2 =
      (16 / 15 : ℝ) ^ 2 * 100 *
        (((m : ℝ) ^ (3 / 4 : ℝ)) ^ (2 : ℝ)) by
          rw [Real.rpow_two]
          ring]
  rw [hp]
  rw [← hmul]
  apply (le_div_iff₀ (by positivity : (0 : ℝ) < 4 * m)).2
  have hpow : 0 ≤ (m : ℝ) ^ (1 / 2 : ℝ) := by positivity
  have hprod : 0 < (m : ℝ) ^ (1 / 2 : ℝ) * (m : ℝ) := by positivity
  norm_num
  nlinarith

/-- A fixed-tilt Chernoff bound for deviations larger than the number of
geometric summands.  This is the missing complement to the moderate bound
in `HLOZUrn.negBinUpperTail_le_exp`. -/
theorem negBinUpperTail_le_exp_linear (i : ℕ) (hi : 1 ≤ i) (a : ℝ)
    (hia : (i : ℝ) ≤ a) :
    negBinUpperTail i ((i : ℝ) / 15 + a) ≤ Real.exp (-a / 4) := by
  let t : ℝ := 1 / 2
  let b : ℝ := (i : ℝ) / 15 + a
  have ht0 : 0 ≤ t := by norm_num [t]
  have htHalf : t ≤ 1 / 2 := by norm_num [t]
  have hexp16 : Real.exp t < 16 := by
    have he := exp_le_one_add_add_sq ht0 (by norm_num [t] : t ≤ 1)
    norm_num [t] at he ⊢
    linarith
  have hm := hasSum_negBinMass_mul_exp i hi hexp16
  have hbase := negBin_base_le_exp ht0 htHalf
  have hbase0 : 0 ≤ 15 / (16 - Real.exp t) := by positivity
  have hpow : (15 / (16 - Real.exp t)) ^ i ≤
      (Real.exp (t / 15 + t ^ 2)) ^ i :=
    pow_le_pow_left₀ hbase0 hbase i
  have hweighted : Summable (fun j : ℕ ↦
      Real.exp (-t * b) * (negBinMass i j * Real.exp (t * j))) :=
    hm.summable.mul_left _
  have htailSummable : Summable (fun j : ℕ ↦
      if b ≤ (j : ℝ) then negBinMass i j else 0) := by
    apply Summable.of_nonneg_of_le
      (fun j ↦ by
        split_ifs
        · exact negBinMass_nonneg i j
        · exact le_rfl)
      (fun j ↦ ?_) hweighted
    split_ifs with hj
    · have hweight : 1 ≤ Real.exp (-t * b) * Real.exp (t * j) := by
        rw [← Real.exp_add]
        apply Real.one_le_exp
        nlinarith
      calc
        negBinMass i j = negBinMass i j * 1 := by ring
        _ ≤ negBinMass i j *
            (Real.exp (-t * b) * Real.exp (t * j)) :=
          mul_le_mul_of_nonneg_left hweight (negBinMass_nonneg i j)
        _ = Real.exp (-t * b) * (negBinMass i j * Real.exp (t * j)) := by ring
    · exact mul_nonneg (Real.exp_nonneg _)
        (mul_nonneg (negBinMass_nonneg i j) (Real.exp_nonneg _))
  calc
    negBinUpperTail i ((i : ℝ) / 15 + a) =
        ∑' j : ℕ, if b ≤ (j : ℝ) then negBinMass i j else 0 := by rfl
    _ ≤ ∑' j : ℕ,
        Real.exp (-t * b) * (negBinMass i j * Real.exp (t * j)) := by
      apply Summable.tsum_le_tsum
        (fun j ↦ ?_) htailSummable hweighted
      split_ifs with hj
      · have hweight : 1 ≤ Real.exp (-t * b) * Real.exp (t * j) := by
          rw [← Real.exp_add]
          apply Real.one_le_exp
          nlinarith
        calc
          negBinMass i j = negBinMass i j * 1 := by ring
          _ ≤ negBinMass i j *
              (Real.exp (-t * b) * Real.exp (t * j)) :=
            mul_le_mul_of_nonneg_left hweight (negBinMass_nonneg i j)
          _ = Real.exp (-t * b) * (negBinMass i j * Real.exp (t * j)) := by ring
      · exact mul_nonneg (Real.exp_nonneg _)
          (mul_nonneg (negBinMass_nonneg i j) (Real.exp_nonneg _))
    _ = Real.exp (-t * b) * (15 / (16 - Real.exp t)) ^ i :=
      (hm.mul_left _).tsum_eq
    _ ≤ Real.exp (-t * b) * (Real.exp (t / 15 + t ^ 2)) ^ i :=
      mul_le_mul_of_nonneg_left hpow (Real.exp_nonneg _)
    _ = Real.exp (-t * b + (i : ℝ) * (t / 15 + t ^ 2)) := by
      rw [← Real.exp_nat_mul, ← Real.exp_add]
    _ ≤ Real.exp (-a / 4) := by
      apply Real.exp_le_exp.mpr
      dsimp [t, b]
      nlinarith

lemma hasLaw_negBin_upperDeviation_le_exp_linear
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    (X : Ω → ℕ) {i : ℕ} (hi : 1 ≤ i) (d : ℝ)
    (hid : (i : ℝ) ≤ d) (hLaw : HasLaw X (negBinMeasure i) μ) :
    μ {ω | (i : ℝ) / 15 + d ≤ X ω} ≤
      ENNReal.ofReal (Real.exp (-d / 4)) := by
  have hEq := hLaw.measure_eq
    (p := fun j : ℕ ↦ (i : ℝ) / 15 + d ≤ (j : ℝ))
    (show MeasurableSet {j : ℕ | (i : ℝ) / 15 + d ≤ (j : ℝ)} from
      (Set.countable_univ.mono (Set.subset_univ _)).measurableSet)
  rw [hEq]
  rw [HLOZProp45Theta.negBinMeasure_upperTail i hi]
  exact ENNReal.ofReal_le_ofReal (negBinUpperTail_le_exp_linear i hi d hid)

structure SourceScale (m : ℕ) : Prop where
  one_le : 1 ≤ m
  split_le_low : sourceSplitCut m ≤ sourceLowCut m
  split_lower : (15 / 31 : ℝ) * m ≤ sourceSplitCut m
  prop44_le_split : sourceProp44Threshold m ≤ sourceSplitCut m
  far_linear : 17 * Real.sqrt (m : ℝ) ≤ sourceFarDeviation m / 4

lemma eventually_sourceScale : ∀ᶠ m : ℕ in atTop, SourceScale m := by
  have hfarNear :=
    eventually_const_mul_nat_rpow_le_const_mul_nat_rpow
      (C := 10) (d := 10) (p := 1 - sourceKappa) (q := 3 / 4)
      (by norm_num) (by norm_num) (by norm_num [sourceKappa])
  have hfarSub : ∀ᶠ m : ℕ in atTop,
      10 * (m : ℝ) ^ (3 / 4 : ℝ) + 1 ≤ (m : ℝ) ^ (4 / 5 : ℝ) := by
    have h1 := eventually_const_mul_nat_rpow_le_const_mul_nat_rpow
      (C := 10) (d := 1 / 2) (p := 3 / 4) (q := 4 / 5)
      (by norm_num) (by norm_num) (by norm_num)
    have h2 := eventually_const_mul_nat_rpow_le_const_mul_nat_rpow
      (C := 1) (d := 1 / 2) (p := 0) (q := 4 / 5)
      (by norm_num) (by norm_num) (by norm_num)
    filter_upwards [h1, h2, eventually_ge_atTop 1] with m hm1 hm2 hm
    simp only [Real.rpow_zero, mul_one] at hm2
    nlinarith
  have hsplitLower : ∀ᶠ m : ℕ in atTop,
      10 * (m : ℝ) ^ (3 / 4 : ℝ) + 1 ≤
        ((15 / 16 : ℝ) - 15 / 31) * m := by
    have h1 := eventually_const_mul_nat_rpow_le_const_mul_nat_rpow
      (C := 10) (d := ((15 / 16 : ℝ) - 15 / 31) / 2)
      (p := 3 / 4) (q := 1) (by norm_num) (by norm_num) (by norm_num)
    have h2 := eventually_const_mul_nat_rpow_le_const_mul_nat_rpow
      (C := 1) (d := ((15 / 16 : ℝ) - 15 / 31) / 2)
      (p := 0) (q := 1) (by norm_num) (by norm_num) (by norm_num)
    filter_upwards [h1, h2] with m hm1 hm2
    simp only [Real.rpow_zero, Real.rpow_one, mul_one] at hm1 hm2 ⊢
    nlinarith
  have hlinear : ∀ᶠ m : ℕ in atTop,
      17 * (m : ℝ) ^ (1 / 2 : ℝ) ≤
        (8 / 3 : ℝ) * (m : ℝ) ^ (3 / 4 : ℝ) :=
    eventually_const_mul_nat_rpow_le_const_mul_nat_rpow
      (C := 17) (d := 8 / 3) (p := 1 / 2) (q := 3 / 4)
      (by norm_num) (by norm_num) (by norm_num)
  filter_upwards [hfarNear, hfarSub, hsplitLower, hlinear,
    eventually_ge_atTop 1] with m hfarNear hfarSub hsplitLower hlinear hm
  have hmR : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
  have hsplitPos : 0 ≤ sourceSplitCutReal m := by
    rw [sourceSplitCutReal, sourceFarWidth]
    nlinarith
  have hlowPos : 0 ≤ sourceLowCutReal m := by
    rw [sourceLowCutReal, sourceNearWidth]
    nlinarith
  have hsplitFloorLower : sourceSplitCutReal m < sourceSplitCut m + 1 := by
    rw [sourceSplitCut, max_eq_left hsplitPos]
    exact Nat.lt_floor_add_one _
  refine ⟨hm, ?_, ?_, ?_, ?_⟩
  · apply Nat.floor_mono
    rw [max_eq_left hsplitPos, max_eq_left hlowPos]
    rw [sourceSplitCutReal, sourceLowCutReal, sourceFarWidth, sourceNearWidth]
    nlinarith
  · rw [sourceSplitCutReal, sourceFarWidth] at hsplitFloorLower
    exact le_of_lt (by nlinarith)
  · rw [sourceProp44Threshold]
    rw [sourceSplitCutReal, sourceFarWidth] at hsplitFloorLower
    nlinarith
  · rw [Real.sqrt_eq_rpow, sourceFarDeviation, sourceFarWidth]
    norm_num at hlinear ⊢
    nlinarith

/-! ### The source capped profile and its two-scale split -/

/-- `dotΞ_m(x)` from (4.21)--(4.23), after the external path through
`ψ_m` has been fixed. -/
noncomputable def sourceDotIndex (m : ℕ) (profile : Site → ℕ) (x : Site) : ℕ :=
  min (profile x) (sourceLowCut m)

/-- Deviation above the negative-binomial mean needed for the capped profile
to reach level `m`. -/
noncomputable def sourceDotDeviation (m : ℕ) (profile : Site → ℕ) (x : Site) : ℝ :=
  (m : ℝ) - (16 / 15 : ℝ) * sourceDotIndex m profile x

/-- One coordinate of `dotΘ_{ψ_m}(m,m)`.  The supplied random variable is
the sum of the first `dotΞ_m(x)` holding times. -/
def sourceDotThetaAt {Ω : Type*} (m : ℕ) (profile : Site → ℕ)
    (lazyPrefixSum : Ω → Site → ℕ) (x : Site) : Set Ω :=
  {ω | m ≤ sourceDotIndex m profile x + lazyPrefixSum ω x}

def sourceDotThetaEvent {Ω : Type*} (sites : Finset Site) (m : ℕ)
    (profile : Site → ℕ) (lazyPrefixSum : Ω → Site → ℕ) : Set Ω :=
  ⋃ x ∈ sites, sourceDotThetaAt m profile lazyPrefixSum x

noncomputable def sourceNearCandidates (sites : Finset Site) (m : ℕ)
    (profile : Site → ℕ) : Finset Site :=
  sites.filter fun x ↦ sourceSplitCut m ≤ profile x

noncomputable def sourceFarCandidates (sites : Finset Site) (m : ℕ)
    (profile : Site → ℕ) : Finset Site :=
  sites.filter fun x ↦ profile x < sourceSplitCut m

noncomputable def sourceProp44Candidates (sites : Finset Site) (m : ℕ)
    (profile : Site → ℕ) : Finset Site :=
  sites.filter fun x ↦ sourceProp44Threshold m ≤ profile x

lemma sourceDotThetaEvent_eq_near_union_far {Ω : Type*}
    (sites : Finset Site) (m : ℕ) (profile : Site → ℕ)
    (lazyPrefixSum : Ω → Site → ℕ) :
    sourceDotThetaEvent sites m profile lazyPrefixSum =
      (⋃ x ∈ sourceNearCandidates sites m profile,
        sourceDotThetaAt m profile lazyPrefixSum x) ∪
      (⋃ x ∈ sourceFarCandidates sites m profile,
        sourceDotThetaAt m profile lazyPrefixSum x) := by
  ext ω
  simp only [sourceDotThetaEvent, Set.mem_iUnion, Set.mem_union,
    sourceNearCandidates, sourceFarCandidates, Finset.mem_filter]
  constructor
  · rintro ⟨x, hx, hω⟩
    by_cases hnear : sourceSplitCut m ≤ profile x
    · exact Or.inl ⟨x, ⟨hx, hnear⟩, hω⟩
    · exact Or.inr ⟨x, ⟨hx, by omega⟩, hω⟩
  · rintro (⟨x, ⟨hx, _⟩, hω⟩ | ⟨x, ⟨hx, _⟩, hω⟩) <;>
      exact ⟨x, hx, hω⟩

lemma sourceNearCandidates_subset_prop44 (m : ℕ) (hs : SourceScale m)
    (sites : Finset Site) (profile : Site → ℕ) :
    sourceNearCandidates sites m profile ⊆
      sourceProp44Candidates sites m profile := by
  intro x hx
  rw [sourceNearCandidates, Finset.mem_filter] at hx
  rw [sourceProp44Candidates, Finset.mem_filter]
  exact ⟨hx.1, hs.prop44_le_split.trans (by exact_mod_cast hx.2)⟩

lemma sourceLowCut_le (m : ℕ) (hm : 1 ≤ m) : sourceLowCut m ≤ m := by
  have hm0 : (0 : ℝ) ≤ m := by positivity
  have hreal : max (sourceLowCutReal m) 0 ≤ (m : ℝ) := by
    apply max_le
    · rw [sourceLowCutReal, sourceNearWidth]
      have hp : 0 ≤ (m : ℝ) ^ (1 - sourceKappa) := by positivity
      nlinarith
    · exact hm0
  have hf : (sourceLowCut m : ℝ) ≤ (m : ℝ) := by
    rw [sourceLowCut]
    exact (Nat.floor_le (by positivity)).trans hreal
  exact_mod_cast hf

lemma sourceLowCut_cast_le_real (m : ℕ) (hreal : 0 ≤ sourceLowCutReal m) :
    (sourceLowCut m : ℝ) ≤ sourceLowCutReal m := by
  rw [sourceLowCut, max_eq_left hreal]
  exact Nat.floor_le hreal

lemma sourceSplitCut_cast_le_real (m : ℕ) (hreal : 0 ≤ sourceSplitCutReal m) :
    (sourceSplitCut m : ℝ) ≤ sourceSplitCutReal m := by
  rw [sourceSplitCut, max_eq_left hreal]
  exact Nat.floor_le hreal

lemma sourceScale_split_pos (m : ℕ) (hs : SourceScale m) :
    1 ≤ sourceSplitCut m := by
  have hm : 0 < m := lt_of_lt_of_le Nat.zero_lt_one hs.one_le
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have : (0 : ℝ) < sourceSplitCut m :=
    lt_of_lt_of_le (mul_pos (by norm_num) hmR) hs.split_lower
  exact_mod_cast this

lemma sourceScale_lowCutReal_nonneg (m : ℕ) (hs : SourceScale m) :
    0 ≤ sourceLowCutReal m := by
  have hcut : 0 < sourceLowCut m :=
    lt_of_lt_of_le Nat.zero_lt_one
      ((sourceScale_split_pos m hs).trans hs.split_le_low)
  by_contra h
  have : sourceLowCut m = 0 := by
    rw [sourceLowCut, max_eq_right (le_of_not_ge h)]
    simp
  omega

lemma sourceScale_splitCutReal_nonneg (m : ℕ) (hs : SourceScale m) :
    0 ≤ sourceSplitCutReal m := by
  have hcut : 0 < sourceSplitCut m :=
    lt_of_lt_of_le Nat.zero_lt_one (sourceScale_split_pos m hs)
  by_contra h
  have : sourceSplitCut m = 0 := by
    rw [sourceSplitCut, max_eq_right (le_of_not_ge h)]
    simp
  omega

lemma sourceDotIndex_pos (m : ℕ) (hs : SourceScale m)
    (profile : Site → ℕ) {x : Site} (hx : 1 ≤ profile x) :
    1 ≤ sourceDotIndex m profile x := by
  rw [sourceDotIndex]
  exact le_min hx ((sourceScale_split_pos m hs).trans hs.split_le_low)

lemma sourceDotIndex_le_m (m : ℕ) (hs : SourceScale m)
    (profile : Site → ℕ) (x : Site) :
    sourceDotIndex m profile x ≤ m :=
  (min_le_right _ _).trans (sourceLowCut_le m hs.one_le)

lemma sourceDotDeviation_nonneg (m : ℕ) (hs : SourceScale m)
    (profile : Site → ℕ) (x : Site) :
    0 ≤ sourceDotDeviation m profile x := by
  have hreal := sourceScale_lowCutReal_nonneg m hs
  have hiR : (sourceDotIndex m profile x : ℝ) ≤ sourceLowCutReal m :=
    (by exact_mod_cast min_le_right (profile x) (sourceLowCut m) :
      (sourceDotIndex m profile x : ℝ) ≤ sourceLowCut m) |>.trans
        (sourceLowCut_cast_le_real m hreal)
  rw [sourceDotDeviation]
  rw [sourceLowCutReal, sourceNearWidth] at hiR
  have hp : 0 ≤ (m : ℝ) ^ (1 - sourceKappa) := by positivity
  nlinarith

lemma sourceDotThetaAt_eq_upperDeviation {Ω : Type*}
    (m : ℕ) (profile : Site → ℕ) (lazyPrefixSum : Ω → Site → ℕ) (x : Site) :
    sourceDotThetaAt m profile lazyPrefixSum x =
      {ω | (sourceDotIndex m profile x : ℝ) / 15 +
        sourceDotDeviation m profile x ≤ lazyPrefixSum ω x} := by
  ext ω
  simp only [sourceDotThetaAt, Set.mem_setOf_eq, sourceDotDeviation]
  constructor
  · intro h
    have hR : (m : ℝ) ≤ sourceDotIndex m profile x + lazyPrefixSum ω x := by
      exact_mod_cast h
    norm_num at hR ⊢
    nlinarith
  · intro h
    have hR : (m : ℝ) ≤ sourceDotIndex m profile x + lazyPrefixSum ω x := by
      norm_num at h ⊢
      nlinarith
    exact_mod_cast hR

lemma sourceNear_deviation_le_index (m : ℕ) (hs : SourceScale m)
    (sites : Finset Site) (profile : Site → ℕ) {x : Site}
    (hx : x ∈ sourceNearCandidates sites m profile) :
    sourceDotDeviation m profile x ≤ sourceDotIndex m profile x := by
  have hxprof : sourceSplitCut m ≤ profile x :=
    (Finset.mem_filter.mp hx).2
  have hilow : sourceSplitCut m ≤ sourceDotIndex m profile x := by
    rw [sourceDotIndex]
    exact le_min hxprof hs.split_le_low
  have hiR : (15 / 31 : ℝ) * m ≤ sourceDotIndex m profile x :=
    hs.split_lower.trans (by exact_mod_cast hilow)
  rw [sourceDotDeviation]
  nlinarith

lemma sourceNear_deviation_ge (m : ℕ) (hs : SourceScale m)
    (sites : Finset Site) (profile : Site → ℕ) {x : Site}
    (_hx : x ∈ sourceNearCandidates sites m profile) :
    sourceNearDeviation m ≤ sourceDotDeviation m profile x := by
  have hlowReal := sourceScale_lowCutReal_nonneg m hs
  have hi : (sourceDotIndex m profile x : ℝ) ≤ sourceLowCutReal m :=
    (by exact_mod_cast min_le_right (profile x) (sourceLowCut m) :
      (sourceDotIndex m profile x : ℝ) ≤ sourceLowCut m) |>.trans
        (sourceLowCut_cast_le_real m hlowReal)
  rw [sourceLowCutReal, sourceNearWidth] at hi
  rw [sourceNearDeviation, sourceDotDeviation, sourceNearWidth]
  nlinarith

lemma sourceNear_exponent (m : ℕ) (hs : SourceScale m)
    (sites : Finset Site) (profile : Site → ℕ) {x : Site}
    (hx : x ∈ sourceNearCandidates sites m profile) :
    17 * sourceRate m ≤
      sourceDotDeviation m profile x ^ 2 /
        (4 * (sourceDotIndex m profile x : ℝ)) := by
  have hmR : (0 : ℝ) < m := by
    exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hs.one_le)
  have hiPos : (0 : ℝ) < sourceDotIndex m profile x := by
    have hxprof : 1 ≤ profile x := by
      have := sourceScale_split_pos m hs
      have hp := (Finset.mem_filter.mp hx).2
      omega
    exact_mod_cast sourceDotIndex_pos m hs profile hxprof
  have hiM : (sourceDotIndex m profile x : ℝ) ≤ m := by
    exact_mod_cast sourceDotIndex_le_m m hs profile x
  have hd0 := sourceDotDeviation_nonneg m hs profile x
  have hdev := sourceNear_deviation_ge m hs sites profile hx
  have hnear0 : 0 ≤ sourceNearDeviation m := by
    rw [sourceNearDeviation, sourceNearWidth]
    positivity
  have hsq : sourceNearDeviation m ^ 2 ≤ sourceDotDeviation m profile x ^ 2 := by
    nlinarith [sq_nonneg (sourceDotDeviation m profile x - sourceNearDeviation m)]
  calc
    17 * sourceRate m ≤ sourceNearDeviation m ^ 2 / (4 * (m : ℝ)) :=
      sourceNearExponentBase m hs.one_le
    _ ≤ sourceDotDeviation m profile x ^ 2 / (4 * (m : ℝ)) := by
      gcongr
    _ ≤ sourceDotDeviation m profile x ^ 2 /
        (4 * (sourceDotIndex m profile x : ℝ)) := by
      exact div_le_div_of_nonneg_left (sq_nonneg _) (by positivity) (by gcongr)

lemma sourceFar_index_eq_profile (m : ℕ) (hs : SourceScale m)
    (sites : Finset Site) (profile : Site → ℕ) {x : Site}
    (hx : x ∈ sourceFarCandidates sites m profile) :
    sourceDotIndex m profile x = profile x := by
  rw [sourceDotIndex, min_eq_left]
  exact (le_of_lt (Finset.mem_filter.mp hx).2).trans hs.split_le_low

lemma sourceFar_deviation_ge (m : ℕ) (hs : SourceScale m)
    (sites : Finset Site) (profile : Site → ℕ) {x : Site}
    (hx : x ∈ sourceFarCandidates sites m profile) :
    sourceFarDeviation m ≤ sourceDotDeviation m profile x := by
  have hsplitPos := sourceScale_splitCutReal_nonneg m hs
  have hprof : (profile x : ℝ) < sourceSplitCutReal m :=
    (by exact_mod_cast (Finset.mem_filter.mp hx).2 :
      (profile x : ℝ) < sourceSplitCut m) |>.trans_le
        (sourceSplitCut_cast_le_real m hsplitPos)
  rw [sourceDotDeviation, sourceFar_index_eq_profile m hs sites profile hx]
  rw [sourceSplitCutReal, sourceFarWidth] at hprof
  rw [sourceFarDeviation, sourceFarWidth]
  nlinarith

lemma sourceFar_exponent_quadratic (m : ℕ) (hs : SourceScale m)
    (sites : Finset Site) (profile : Site → ℕ) {x : Site}
    (hx : x ∈ sourceFarCandidates sites m profile)
    (hxpos : 1 ≤ profile x) :
    17 * Real.sqrt (m : ℝ) ≤
      sourceDotDeviation m profile x ^ 2 /
        (4 * (sourceDotIndex m profile x : ℝ)) := by
  have hiPos : (0 : ℝ) < sourceDotIndex m profile x := by
    exact_mod_cast sourceDotIndex_pos m hs profile hxpos
  have hiM : (sourceDotIndex m profile x : ℝ) ≤ m := by
    exact_mod_cast sourceDotIndex_le_m m hs profile x
  have hd0 := sourceDotDeviation_nonneg m hs profile x
  have hdev := sourceFar_deviation_ge m hs sites profile hx
  have hfar0 : 0 ≤ sourceFarDeviation m := by
    rw [sourceFarDeviation, sourceFarWidth]
    positivity
  have hsq : sourceFarDeviation m ^ 2 ≤ sourceDotDeviation m profile x ^ 2 := by
    nlinarith [sq_nonneg (sourceDotDeviation m profile x - sourceFarDeviation m)]
  calc
    17 * Real.sqrt (m : ℝ) ≤
        sourceFarDeviation m ^ 2 / (4 * (m : ℝ)) :=
      sourceFarQuadraticBase m hs.one_le
    _ ≤ sourceDotDeviation m profile x ^ 2 / (4 * (m : ℝ)) := by
      gcongr
    _ ≤ sourceDotDeviation m profile x ^ 2 /
        (4 * (sourceDotIndex m profile x : ℝ)) := by
      exact div_le_div_of_nonneg_left (sq_nonneg _) (by positivity) (by gcongr)

theorem cond_sourceNearAt_le_exp_seventeen
    {Ω : Type*} [MeasurableSpace Ω]
    (m : ℕ) (hs : SourceScale m) (μ : Measure Ω) (C : Set Ω)
    (sites : Finset Site) (profile : Site → ℕ)
    (lazyPrefixSum : Ω → Site → ℕ) {x : Site}
    (hx : x ∈ sourceNearCandidates sites m profile)
    (hpositive : 1 ≤ profile x)
    (hLaw : HasLaw (fun ω ↦ lazyPrefixSum ω x)
      (negBinMeasure (sourceDotIndex m profile x)) μ[|C]) :
    μ[|C] (sourceDotThetaAt m profile lazyPrefixSum x) ≤
      ENNReal.ofReal (Real.exp (-17 * sourceRate m)) := by
  rw [sourceDotThetaAt_eq_upperDeviation]
  calc
    μ[|C] {ω | (sourceDotIndex m profile x : ℝ) / 15 +
        sourceDotDeviation m profile x ≤ lazyPrefixSum ω x} ≤
        ENNReal.ofReal (Real.exp
          (-(sourceDotDeviation m profile x ^ 2 /
            (4 * (sourceDotIndex m profile x : ℝ))))) :=
      HLOZProp45Theta.hasLaw_negBin_upperDeviation_le_exp
        (fun ω ↦ lazyPrefixSum ω x)
        (sourceDotIndex_pos m hs profile hpositive)
        (sourceDotDeviation m profile x)
        (sourceDotDeviation_nonneg m hs profile x)
        (sourceNear_deviation_le_index m hs sites profile hx) hLaw
    _ ≤ ENNReal.ofReal (Real.exp (-17 * sourceRate m)) := by
      apply ENNReal.ofReal_le_ofReal
      apply Real.exp_le_exp.mpr
      have h := neg_le_neg (sourceNear_exponent m hs sites profile hx)
      nlinarith

theorem cond_sourceFarAt_le_exp_seventeen
    {Ω : Type*} [MeasurableSpace Ω]
    (m : ℕ) (hs : SourceScale m) (μ : Measure Ω) (C : Set Ω)
    (sites : Finset Site) (profile : Site → ℕ)
    (lazyPrefixSum : Ω → Site → ℕ) {x : Site}
    (hx : x ∈ sourceFarCandidates sites m profile)
    (hpositive : 1 ≤ profile x)
    (hLaw : HasLaw (fun ω ↦ lazyPrefixSum ω x)
      (negBinMeasure (sourceDotIndex m profile x)) μ[|C]) :
    μ[|C] (sourceDotThetaAt m profile lazyPrefixSum x) ≤
      ENNReal.ofReal (Real.exp (-17 * Real.sqrt (m : ℝ))) := by
  rw [sourceDotThetaAt_eq_upperDeviation]
  let d := sourceDotDeviation m profile x
  let i := sourceDotIndex m profile x
  have hi : 1 ≤ i := sourceDotIndex_pos m hs profile hpositive
  have hd0 : 0 ≤ d := sourceDotDeviation_nonneg m hs profile x
  rcases le_total d (i : ℝ) with hdi | hid
  · calc
      μ[|C] {ω | (i : ℝ) / 15 + d ≤ lazyPrefixSum ω x} ≤
          ENNReal.ofReal (Real.exp (-(d ^ 2 / (4 * (i : ℝ))))) :=
        HLOZProp45Theta.hasLaw_negBin_upperDeviation_le_exp
          (fun ω ↦ lazyPrefixSum ω x) hi d hd0 hdi hLaw
      _ ≤ ENNReal.ofReal (Real.exp (-17 * Real.sqrt (m : ℝ))) := by
        apply ENNReal.ofReal_le_ofReal
        apply Real.exp_le_exp.mpr
        have h := neg_le_neg
          (sourceFar_exponent_quadratic m hs sites profile hx hpositive)
        dsimp only [d, i]
        nlinarith
  · calc
      μ[|C] {ω | (i : ℝ) / 15 + d ≤ lazyPrefixSum ω x} ≤
          ENNReal.ofReal (Real.exp (-d / 4)) :=
        hasLaw_negBin_upperDeviation_le_exp_linear
          (fun ω ↦ lazyPrefixSum ω x) hi d hid hLaw
      _ ≤ ENNReal.ofReal (Real.exp (-17 * Real.sqrt (m : ℝ))) := by
        apply ENNReal.ofReal_le_ofReal
        apply Real.exp_le_exp.mpr
        have hmain : 17 * Real.sqrt (m : ℝ) ≤ d / 4 := calc
          17 * Real.sqrt (m : ℝ) ≤ sourceFarDeviation m / 4 := hs.far_linear
          _ ≤ d / 4 := by
            exact div_le_div_of_nonneg_right
              (sourceFar_deviation_ge m hs sites profile hx) (by norm_num)
        nlinarith

/-- Source-specialized conditional form of (4.22)--(4.24) at the top level
`a=m`.  The only probabilistic inputs are the exact Proposition 4.2 capped
negative-binomial law, the Proposition 4.4 high-profile count, and the
external-horizon site count. -/
theorem cond_sourceDotTheta_le_two_scale
    {Ω : Type*} [MeasurableSpace Ω]
    (m : ℕ) (hs : SourceScale m) (μ : Measure Ω) (C : Set Ω)
    (sites : Finset Site) (profile : Site → ℕ)
    (lazyPrefixSum : Ω → Site → ℕ)
    (hpositive : ∀ x ∈ sites, 1 ≤ profile x)
    (hProp44Card : ((sourceProp44Candidates sites m profile).card : ℝ) ≤
      Real.exp (16 * sourceRate m))
    (hHorizonCard : (sites.card : ℝ) ≤
      Real.exp (16 * Real.sqrt (m : ℝ)))
    (hLaw : ∀ x ∈ sites,
      HasLaw (fun ω ↦ lazyPrefixSum ω x)
        (negBinMeasure (sourceDotIndex m profile x)) μ[|C]) :
    μ[|C] (sourceDotThetaEvent sites m profile lazyPrefixSum) ≤
      ENNReal.ofReal (Real.exp (-sourceRate m)) +
        ENNReal.ofReal (Real.exp (-Real.sqrt (m : ℝ))) := by
  let near := sourceNearCandidates sites m profile
  let far := sourceFarCandidates sites m profile
  let E := sourceDotThetaAt m profile lazyPrefixSum
  have hnearCard : (near.card : ℝ) ≤ Real.exp (16 * sourceRate m) := by
    calc
      (near.card : ℝ) ≤ ((sourceProp44Candidates sites m profile).card : ℝ) := by
        exact_mod_cast Finset.card_le_card
          (sourceNearCandidates_subset_prop44 m hs sites profile)
      _ ≤ Real.exp (16 * sourceRate m) := hProp44Card
  have hnear : μ[|C] (⋃ x ∈ near, E x) ≤
      ENNReal.ofReal (Real.exp (-sourceRate m)) := by
    apply HLOZProp45Union.finite_union_exp_sixteen_seventeen
      μ[|C] near E _ (sourceRate m) Set.Subset.rfl hnearCard
    intro x hx
    have hx' : x ∈ sourceNearCandidates sites m profile := by simpa [near] using hx
    have hxsite : x ∈ sites := (Finset.mem_filter.mp hx').1
    exact cond_sourceNearAt_le_exp_seventeen m hs μ C sites profile
      lazyPrefixSum hx' (hpositive x hxsite) (hLaw x hxsite)
  have hfarCard : (far.card : ℝ) ≤
      Real.exp (16 * Real.sqrt (m : ℝ)) := by
    calc
      (far.card : ℝ) ≤ (sites.card : ℝ) := by
        exact_mod_cast Finset.card_le_card (Finset.filter_subset _ _)
      _ ≤ Real.exp (16 * Real.sqrt (m : ℝ)) := hHorizonCard
  have hfar : μ[|C] (⋃ x ∈ far, E x) ≤
      ENNReal.ofReal (Real.exp (-Real.sqrt (m : ℝ))) := by
    apply HLOZProp45Union.finite_union_exp_sixteen_seventeen
      μ[|C] far E _ (Real.sqrt (m : ℝ)) Set.Subset.rfl hfarCard
    intro x hx
    have hx' : x ∈ sourceFarCandidates sites m profile := by simpa [far] using hx
    have hxsite : x ∈ sites := (Finset.mem_filter.mp hx').1
    exact cond_sourceFarAt_le_exp_seventeen m hs μ C sites profile
      lazyPrefixSum hx' (hpositive x hxsite) (hLaw x hxsite)
  rw [sourceDotThetaEvent_eq_near_union_far]
  calc
    μ[|C] ((⋃ x ∈ near, E x) ∪ (⋃ x ∈ far, E x)) ≤
        μ[|C] (⋃ x ∈ near, E x) + μ[|C] (⋃ x ∈ far, E x) :=
      measure_union_le _ _
    _ ≤ ENNReal.ofReal (Real.exp (-sourceRate m)) +
        ENNReal.ofReal (Real.exp (-Real.sqrt (m : ℝ))) :=
      add_le_add hnear hfar

/-- Eventual source form: all analytic threshold and exponent inequalities
have been discharged. -/
theorem eventually_cond_sourceDotTheta_le_two_scale
    {Ω : Type*} [MeasurableSpace Ω] :
    ∀ᶠ m : ℕ in atTop, ∀ (μ : Measure Ω) (C : Set Ω)
      (sites : Finset Site) (profile : Site → ℕ)
      (lazyPrefixSum : Ω → Site → ℕ),
      (∀ x ∈ sites, 1 ≤ profile x) →
      ((sourceProp44Candidates sites m profile).card : ℝ) ≤
        Real.exp (16 * sourceRate m) →
      (sites.card : ℝ) ≤ Real.exp (16 * Real.sqrt (m : ℝ)) →
      (∀ x ∈ sites, HasLaw (fun ω ↦ lazyPrefixSum ω x)
        (negBinMeasure (sourceDotIndex m profile x)) μ[|C]) →
      μ[|C] (sourceDotThetaEvent sites m profile lazyPrefixSum) ≤
        ENNReal.ofReal (Real.exp (-sourceRate m)) +
          ENNReal.ofReal (Real.exp (-Real.sqrt (m : ℝ))) := by
  filter_upwards [eventually_sourceScale] with m hs
  intro μ C sites profile lazyPrefixSum hpositive hProp44 hHorizon hLaw
  exact cond_sourceDotTheta_le_two_scale m hs μ C sites profile lazyPrefixSum
    hpositive hProp44 hHorizon hLaw

/-! ### Canonical inverse-clock realization and the stopped-event bridge -/

open HLOZDecomposition

/-- The first original time at which the deletion clock equals the external
time `q`.  It is set to zero only on paths on which that clock value is never
attained.  HLOZ denote this inverse by `N⁻¹₋(q)`. -/
noncomputable def externalInverseMinus (s : ℕ → Site) (q : ℕ) : ℕ := by
  classical
  exact if h : ∃ n, paperExternalClock s n = q then Nat.find h else 0

lemma externalInverseMinus_spec {s : ℕ → Site} {q : ℕ}
    (h : ∃ n, paperExternalClock s n = q) :
    paperExternalClock s (externalInverseMinus s q) = q := by
  rw [externalInverseMinus, dif_pos h]
  exact Nat.find_spec h

lemma externalInverseMinus_minimal {s : ℕ → Site} {q n : ℕ}
    (hn : paperExternalClock s n = q) : externalInverseMinus s q ≤ n := by
  have h : ∃ j, paperExternalClock s j = q := ⟨n, hn⟩
  rw [externalInverseMinus, dif_pos h]
  exact Nat.find_min' h hn

/-- The retained external-chain state at clock value `q`. -/
noncomputable def externalStateAt (s : ℕ → Site) (q : ℕ) : Site :=
  s (externalInverseMinus s q)

/-- External clock indices through `q` at which the retained chain is at
`x`, in their chronological order. -/
noncomputable def externalVisitIndexList
    (s : ℕ → Site) (q : ℕ) (x : Site) : List ℕ :=
  (List.range (q + 1)).filter fun r ↦ externalStateAt s r = x

/-- The external local-time profile read directly from the inverse clock. -/
noncomputable def inverseClockProfile
    (s : ℕ → Site) (q : ℕ) (x : Site) : ℕ :=
  (externalVisitIndexList s q x).length

/-- A finite natural version of the holding time `h_q`.  Exceptional paths
with infinitely many excursions at one external state are assigned zero by
`WithTop.toNat`; the Proposition 4.2 law excludes those paths. -/
noncomputable def paperHoldingNat (s : ℕ → Site) (q : ℕ) : ℕ :=
  (paperHoldingTime s q).toNat

/-- Sum of the holding times attached to the first `cut` visits to `x` before
external time `q`.  This is the concrete sum in `dotΘ_{ψ_m}`. -/
noncomputable def inverseClockHoldingPrefix
    (s : ℕ → Site) (q cut : ℕ) (x : Site) : ℕ :=
  (((externalVisitIndexList s q x).take cut).map
    (paperHoldingNat s)).sum

/-- Atom fixing the inverse-clock external profile through `q`. -/
def inverseClockProfileAtom (q : ℕ) (sites : Finset Site)
    (profile : Site → ℕ) : Set (ℕ → Site) :=
  {s | ∀ x ∈ sites, inverseClockProfile s q x = profile x}

/-- The exact concrete `dotΘ` event on a fixed external-profile atom. -/
def canonicalDotThetaEvent (q : ℕ) (sites : Finset Site) (m : ℕ)
    (profile : Site → ℕ) : Set (ℕ → Site) :=
  sourceDotThetaEvent sites m profile fun s x ↦
    inverseClockHoldingPrefix s q (sourceDotIndex m profile x) x

/-- `T_m^k`, converted from `WithTop ℕ` using the same default convention
as Mathlib's `stoppedValue`. -/
noncomputable def favoriteCreationHorizon (m k : ℕ) (s : ℕ → Site) : ℕ :=
  (favoriteCreationTime m k s).untopA

/-- The lower stopped imbalance clause at the exact source stopping time,
specialized to the top interval endpoint `a=m`. -/
def stoppedThetaMinusAt (m k : ℕ) (x : Site) : Set (ℕ → Site) :=
  {s | paperExternalLocalTime s (favoriteCreationHorizon m k s) x ≤
      sourceLowCut m ∧
    m ≤ localTime s (favoriteCreationHorizon m k s) x}

def stoppedThetaMinusEvent (sites : Finset Site) (m k : ℕ) : Set (ℕ → Site) :=
  ⋃ x ∈ sites, stoppedThetaMinusAt m k x

/-- The two deterministic inverse-clock facts needed in (4.21): by external
time `q` the profile contains the stopped external visits, and the capped
holding prefix contains the stopped lazy contribution.  The reconstruction
layer is responsible for proving this predicate from `N_{T_m^k} ≤ q`. -/
def SourceClockPrefixCompatibleAt
    (s : ℕ → Site) (T q cut : ℕ) (x : Site) : Prop :=
  paperExternalLocalTime s T x ≤ inverseClockProfile s q x ∧
    paperLazyLocalTime s T x ≤ inverseClockHoldingPrefix s q cut x

def sourceClockPrefixCompatibleEvent
    (q : ℕ) (sites : Finset Site) (m k : ℕ)
    (profile : Site → ℕ) : Set (ℕ → Site) :=
  {s | ∀ x ∈ sites, SourceClockPrefixCompatibleAt s
    (favoriteCreationHorizon m k s) q (sourceDotIndex m profile x) x}

/-- The exact deterministic content of HLOZ (4.21), after the inverse-clock
prefix compatibility supplied by reconstruction is exposed explicitly. -/
theorem stoppedThetaMinus_subset_canonicalDotTheta
    (q : ℕ) (sites : Finset Site) (m k : ℕ) (profile : Site → ℕ) :
    stoppedThetaMinusEvent sites m k ∩ inverseClockProfileAtom q sites profile ∩
        sourceClockPrefixCompatibleEvent q sites m k profile ⊆
      canonicalDotThetaEvent q sites m profile := by
  intro s hs
  rcases hs with ⟨⟨hsTheta, hsProfile⟩, hsCompat⟩
  simp only [stoppedThetaMinusEvent, Set.mem_iUnion] at hsTheta
  rcases hsTheta with ⟨x, hxsite, hxTheta⟩
  rw [canonicalDotThetaEvent, sourceDotThetaEvent]
  simp only [Set.mem_iUnion]
  refine ⟨x, hxsite, ?_⟩
  change m ≤ sourceDotIndex m profile x +
    inverseClockHoldingPrefix s q (sourceDotIndex m profile x) x
  have hprofile : inverseClockProfile s q x = profile x :=
    hsProfile x hxsite
  have hcompat := hsCompat x hxsite
  have hext : paperExternalLocalTime s (favoriteCreationHorizon m k s) x ≤
      sourceDotIndex m profile x := by
    rw [sourceDotIndex]
    apply le_min
    · simpa only [hprofile] using hcompat.1
    · exact hxTheta.1
  have hlazy := hcompat.2
  have hdecomp := localTime_eq_paperExternal_add_paperLazy
    s (favoriteCreationHorizon m k s) x
  calc
    m ≤ localTime s (favoriteCreationHorizon m k s) x := hxTheta.2
    _ = paperExternalLocalTime s (favoriteCreationHorizon m k s) x +
        paperLazyLocalTime s (favoriteCreationHorizon m k s) x := hdecomp
    _ ≤ sourceDotIndex m profile x +
        inverseClockHoldingPrefix s q (sourceDotIndex m profile x) x :=
      Nat.add_le_add hext hlazy

/-- The source two-scale estimate instantiated with the concrete inverse-clock
holding prefix.  `hLaw` is precisely the capped Proposition 4.2 input; it is
not mislabeled as the truncated Proposition 4.3 law. -/
theorem cond_canonicalDotTheta_le_two_scale
    (q m : ℕ) (hs : SourceScale m) (μ : Measure (ℕ → Site))
    (C : Set (ℕ → Site)) (sites : Finset Site) (profile : Site → ℕ)
    (hpositive : ∀ x ∈ sites, 1 ≤ profile x)
    (hProp44Card : ((sourceProp44Candidates sites m profile).card : ℝ) ≤
      Real.exp (16 * sourceRate m))
    (hHorizonCard : (sites.card : ℝ) ≤
      Real.exp (16 * Real.sqrt (m : ℝ)))
    (hLaw : ∀ x ∈ sites,
      HasLaw (fun s ↦ inverseClockHoldingPrefix s q
        (sourceDotIndex m profile x) x)
        (negBinMeasure (sourceDotIndex m profile x)) μ[|C]) :
    μ[|C] (canonicalDotThetaEvent q sites m profile) ≤
      ENNReal.ofReal (Real.exp (-sourceRate m)) +
        ENNReal.ofReal (Real.exp (-Real.sqrt (m : ℝ))) := by
  exact cond_sourceDotTheta_le_two_scale m hs μ C sites profile
    (fun s x ↦ inverseClockHoldingPrefix s q
      (sourceDotIndex m profile x) x)
    hpositive hProp44Card hHorizonCard hLaw

/-- Source-facing stopped-time conclusion.  The two support assumptions are
the exact deterministic clock/reconstruction inputs of (4.21); all Chernoff,
threshold, and union-bound work is discharged in this file. -/
theorem cond_inter_stoppedThetaMinus_le_two_scale
    (q m k : ℕ) (hs : SourceScale m) (μ : Measure (ℕ → Site))
    (C : Set (ℕ → Site)) (sites : Finset Site) (profile : Site → ℕ)
    (hProfile : C ⊆ inverseClockProfileAtom q sites profile)
    (hPrefix : C ⊆ sourceClockPrefixCompatibleEvent q sites m k profile)
    (hpositive : ∀ x ∈ sites, 1 ≤ profile x)
    (hProp44Card : ((sourceProp44Candidates sites m profile).card : ℝ) ≤
      Real.exp (16 * sourceRate m))
    (hHorizonCard : (sites.card : ℝ) ≤
      Real.exp (16 * Real.sqrt (m : ℝ)))
    (hLaw : ∀ x ∈ sites,
      HasLaw (fun s ↦ inverseClockHoldingPrefix s q
        (sourceDotIndex m profile x) x)
        (negBinMeasure (sourceDotIndex m profile x)) μ[|C]) :
    μ[|C] (C ∩ stoppedThetaMinusEvent sites m k) ≤
      ENNReal.ofReal (Real.exp (-sourceRate m)) +
        ENNReal.ofReal (Real.exp (-Real.sqrt (m : ℝ))) := by
  calc
    μ[|C] (C ∩ stoppedThetaMinusEvent sites m k) ≤
        μ[|C] (canonicalDotThetaEvent q sites m profile) := by
      apply measure_mono
      intro s hsC
      apply stoppedThetaMinus_subset_canonicalDotTheta q sites m k profile
      exact ⟨⟨hsC.2, hProfile hsC.1⟩, hPrefix hsC.1⟩
    _ ≤ ENNReal.ofReal (Real.exp (-sourceRate m)) +
        ENNReal.ofReal (Real.exp (-Real.sqrt (m : ℝ))) :=
      cond_canonicalDotTheta_le_two_scale q m hs μ C sites profile
        hpositive hProp44Card hHorizonCard hLaw

end Erdos1166.HLOZProp45SourceClock
