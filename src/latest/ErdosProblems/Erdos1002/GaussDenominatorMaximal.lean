import ErdosProblems.Erdos1002.MonotoneMeshWindow
import ErdosProblems.Erdos1002.GaussDenominatorWeakLaw
import ErdosProblems.Erdos1002.GaussLebesgueTransfer
import ErdosProblems.Erdos1002.GaussPrefixMarkedMixedFourier
import Mathlib.MeasureTheory.Measure.Typeclasses.NoAtoms

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# A single maximal denominator-time good event

This file upgrades the one-time weak law to the process-level statement
used in the marked Poisson argument: with probability tending to one, the
logarithmic continued-fraction denominator is uniformly linear at every
depth in a fixed linearly growing window.  The upgrade uses positivity of
the logarithmic roof and a finite deterministic mesh, not an invalid union
bound over `O(L)` individual times.
-/

open Filter MeasureTheory Set ProbabilityTheory
open scoped BigOperators ENNReal NNReal Topology

namespace Erdos1002

noncomputable section

theorem gaussRoofMean_pos : 0 < gaussRoofMean := by
  rw [gaussRoofMean_eq_pi_sq_div_log_two]
  positivity

/-- The roof partial sums are monotone on one common full-measure set. -/
theorem ae_monotone_gaussRoofSum :
    ∀ᵐ x ∂gaussMeasure, Monotone (fun n => gaussRoofSum n x) := by
  have horbit : ∀ᵐ x ∂gaussMeasure, ∀ n : ℕ,
      gaussOrbit n x ∈ Ioc (0 : ℝ) 1 :=
    ae_all_iff.mpr gaussOrbit_unit_ae
  filter_upwards [horbit] with x hx
  apply monotone_nat_of_le_succ
  intro n
  simp only [gaussRoofSum, Finset.sum_range_succ]
  exact le_add_of_nonneg_right
    (neg_nonneg.mpr (Real.log_nonpos (hx n).1.le (hx n).2))

/-- Every fixed positive mesh ray `j * (L / M)` inherits the roof weak law.
-/
theorem tendstoInMeasure_gaussRoofAverage_mesh
    {M j : ℕ} (hM : 0 < M) (hj : 0 < j) :
    TendstoInMeasure gaussMeasure
      (fun L => gaussRoofAverage (j * (L / M))) atTop
      (fun _ => gaussRoofMean) := by
  have hidx : Tendsto (fun L : ℕ => j * (L / M)) atTop atTop := by
    apply tendsto_atTop.2
    intro b
    have hdiv := (Nat.tendsto_div_const_atTop hM.ne').eventually
      (eventually_ge_atTop b)
    filter_upwards [hdiv] with L hL
    exact hL.trans (Nat.le_mul_of_pos_left _ hj)
  exact tendstoInMeasure_gaussRoofAverage.comp hidx

/-- At every fixed mesh ray, deviations of the unnormalized roof sum by a
positive multiple of the ambient scale have probability tending to zero. -/
theorem tendsto_gaussRoofSum_meshDeviation_measureReal_zero
    {M j : ℕ} (hM : 0 < M) (hj : 0 < j)
    {a : ℝ} (ha : 0 < a) :
    Tendsto
      (fun L : ℕ => gaussMeasure.real
        {x | a * (L : ℝ) ≤
          |gaussRoofSum (j * (L / M)) x -
            ((j * (L / M) : ℕ) : ℝ) * gaussRoofMean|})
      atTop (𝓝 0) := by
  let delta : ℝ := a / ((j : ℝ) + 1)
  have hdelta : 0 < delta := by
    dsimp only [delta]
    positivity
  have havg : Tendsto
      (fun L => gaussMeasure.real
        {x | delta ≤
          dist (gaussRoofAverage (j * (L / M)) x) gaussRoofMean})
      atTop (𝓝 0) :=
    (tendstoInMeasure_iff_measureReal_dist.mp
      (tendstoInMeasure_gaussRoofAverage_mesh hM hj)) delta hdelta
  have hupper : ∀ᶠ L : ℕ in atTop,
      gaussMeasure.real
          {x | a * (L : ℝ) ≤
            |gaussRoofSum (j * (L / M)) x -
              ((j * (L / M) : ℕ) : ℝ) * gaussRoofMean|} ≤
        gaussMeasure.real
          {x | delta ≤
            dist (gaussRoofAverage (j * (L / M)) x) gaussRoofMean} := by
    filter_upwards [eventually_ge_atTop M] with L hLM
    have hKpos : 0 < L / M := Nat.div_pos hLM hM
    have hidxpos : 0 < j * (L / M) := Nat.mul_pos hj hKpos
    have hidxBound : (j * (L / M) : ℕ) ≤ j * L := by
      exact Nat.mul_le_mul_left j (Nat.div_le_self L M)
    apply measureReal_mono (h₂ := by finiteness)
    intro x hx
    by_contra hratio
    have hratioSmall :
        dist (gaussRoofAverage (j * (L / M)) x) gaussRoofMean <
          delta := by
      exact lt_of_not_ge hratio
    have hidxR : (0 : ℝ) < (j * (L / M) : ℕ) := by
      exact_mod_cast hidxpos
    have hfactor :
        |gaussRoofSum (j * (L / M)) x -
            ((j * (L / M) : ℕ) : ℝ) * gaussRoofMean| =
          ((j * (L / M) : ℕ) : ℝ) *
            dist (gaussRoofAverage (j * (L / M)) x)
              gaussRoofMean := by
      rw [Real.dist_eq, gaussRoofAverage_eq_gaussRoofSum_div]
      rw [show gaussRoofSum (j * (L / M)) x -
          ((j * (L / M) : ℕ) : ℝ) * gaussRoofMean =
          ((j * (L / M) : ℕ) : ℝ) *
            (gaussRoofSum (j * (L / M)) x /
              (j * (L / M) : ℕ) - gaussRoofMean) by
        field_simp [ne_of_gt hidxR]]
      rw [abs_mul, abs_of_pos hidxR]
    have hidxBoundR :
        ((j * (L / M) : ℕ) : ℝ) ≤ (j : ℝ) * (L : ℝ) := by
      exact_mod_cast hidxBound
    have hsmall :
        |gaussRoofSum (j * (L / M)) x -
            ((j * (L / M) : ℕ) : ℝ) * gaussRoofMean| <
          a * (L : ℝ) := by
      rw [hfactor]
      calc
        ((j * (L / M) : ℕ) : ℝ) *
              dist (gaussRoofAverage (j * (L / M)) x) gaussRoofMean <
            ((j * (L / M) : ℕ) : ℝ) * delta :=
          mul_lt_mul_of_pos_left hratioSmall hidxR
        _ ≤ ((j : ℝ) * (L : ℝ)) * delta :=
          mul_le_mul_of_nonneg_right hidxBoundR hdelta.le
        _ < ((j : ℝ) + 1) * (L : ℝ) * delta := by
          dsimp only [delta]
          have : (j : ℝ) * (L : ℝ) <
              ((j : ℝ) + 1) * (L : ℝ) := by
            nlinarith [show (0 : ℝ) < L by
              exact_mod_cast hM.trans_le hLM]
          exact mul_lt_mul_of_pos_right this hdelta
        _ = a * (L : ℝ) := by
          dsimp only [delta]
          field_simp
    exact (not_lt_of_ge hx) hsmall
  exact squeeze_zero'
    (Eventually.of_forall fun _ => measureReal_nonneg)
    hupper havg

/-! ## From the finite mesh to one global roof event -/

/-- Simultaneous linear-window good event for the roof partial sums. -/
def gaussRoofLinearWindowGoodEvent
    (C L : ℕ) (Delta : ℝ) : Set ℝ :=
  {x | ∀ n : ℕ, n ≤ C * L →
    |gaussRoofSum n x - (n : ℝ) * gaussRoofMean| ≤
      Delta * (L : ℝ)}

/-- Its literal strict complement, written existentially. -/
def gaussRoofLinearWindowBadEvent
    (C L : ℕ) (Delta : ℝ) : Set ℝ :=
  {x | ∃ n : ℕ, n ≤ C * L ∧
    Delta * (L : ℝ) <
      |gaussRoofSum n x - (n : ℝ) * gaussRoofMean|}

theorem gaussRoofLinearWindowBadEvent_eq_compl
    (C L : ℕ) (Delta : ℝ) :
    gaussRoofLinearWindowBadEvent C L Delta =
      (gaussRoofLinearWindowGoodEvent C L Delta)ᶜ := by
  ext x
  change (∃ n : ℕ, n ≤ C * L ∧
      Delta * (L : ℝ) <
        |gaussRoofSum n x - (n : ℝ) * gaussRoofMean|) ↔
    ¬(∀ n : ℕ, n ≤ C * L →
      |gaussRoofSum n x - (n : ℝ) * gaussRoofMean| ≤
        Delta * (L : ℝ))
  constructor
  · rintro ⟨n, hn, hbad⟩ hall
    exact (not_lt_of_ge (hall n hn)) hbad
  · intro hnot
    rcases not_forall.mp hnot with ⟨n, hn⟩
    rcases Classical.not_imp.mp hn with ⟨hnBound, hnBad⟩
    exact ⟨n, hnBound, lt_of_not_ge hnBad⟩

/-- Finite-mesh upgrade: the roof is uniformly linear, in probability, at
all depths in every fixed positive linear window. -/
theorem tendsto_gaussRoofLinearWindowBadEvent_measureReal_zero
    {C : ℕ} (hC : 0 < C) {Delta : ℝ} (hDelta : 0 < Delta) :
    Tendsto
      (fun L : ℕ =>
        gaussMeasure.real (gaussRoofLinearWindowBadEvent C L Delta))
      atTop (𝓝 0) := by
  obtain ⟨M, hMlarge⟩ :=
    exists_nat_gt (2 * gaussRoofMean / Delta)
  have hMpos : 0 < M := by
    have : (0 : ℝ) < M :=
      lt_of_le_of_lt
        (div_nonneg
          (mul_nonneg (by norm_num) gaussRoofMean_pos.le) hDelta.le)
        hMlarge
    exact_mod_cast this
  let D : ℕ := C * M
  let meshBad : ℕ → ℕ → Set ℝ := fun j L =>
    {x | Delta * (L : ℝ) / 2 <
      |gaussRoofSum (j * (L / M)) x -
        ((j * (L / M) : ℕ) : ℝ) * gaussRoofMean|}
  have hmeshTerm (j : ℕ) :
      Tendsto (fun L : ℕ => gaussMeasure.real (meshBad j L))
        atTop (𝓝 0) := by
    by_cases hj : j = 0
    · subst j
      have hzero : (fun L : ℕ => gaussMeasure.real (meshBad 0 L)) =
          fun _ : ℕ => 0 := by
        funext L
        have hempty : meshBad 0 L = ∅ := by
          ext x
          simp only [meshBad, zero_mul, gaussRoofSum, Finset.range_zero,
            Finset.sum_empty, Nat.cast_zero, sub_zero, abs_zero,
            mem_setOf_eq, mem_empty_iff_false, iff_false]
          exact not_lt_of_ge
            (div_nonneg (mul_nonneg hDelta.le (Nat.cast_nonneg L))
              (by norm_num))
        rw [hempty]
        simp
      rw [hzero]
      exact tendsto_const_nhds
    · have hjpos : 0 < j := Nat.pos_of_ne_zero hj
      have hlarge :=
        tendsto_gaussRoofSum_meshDeviation_measureReal_zero
          hMpos hjpos (show 0 < Delta / 2 by positivity)
      apply squeeze_zero'
      · exact Eventually.of_forall fun _ => measureReal_nonneg
      · filter_upwards with L
        show gaussMeasure.real (meshBad j L) ≤
          gaussMeasure.real
            {x | Delta / 2 * (L : ℝ) ≤
              |gaussRoofSum (j * (L / M)) x -
                ((j * (L / M) : ℕ) : ℝ) * gaussRoofMean|}
        apply measureReal_mono (h₂ := measure_ne_top gaussMeasure _)
        intro x hx
        change Delta * (L : ℝ) / 2 <
          |gaussRoofSum (j * (L / M)) x -
            ((j * (L / M) : ℕ) : ℝ) * gaussRoofMean| at hx
        change Delta / 2 * (L : ℝ) ≤
          |gaussRoofSum (j * (L / M)) x -
            ((j * (L / M) : ℕ) : ℝ) * gaussRoofMean|
        nlinarith
      · simpa only [meshBad] using! hlarge
  have hsum : Tendsto
      (fun L : ℕ => ∑ j ∈ Finset.range (D + 2),
        gaussMeasure.real (meshBad j L)) atTop (𝓝 0) := by
    have h := tendsto_finset_sum (Finset.range (D + 2))
      (fun j _hj => hmeshTerm j)
    simpa using! h
  have hlong : ∀ᶠ L : ℕ in atTop, D ≤ L / M :=
    (Nat.tendsto_div_const_atTop hMpos.ne').eventually
      (eventually_ge_atTop D)
  have hmeanDiv : gaussRoofMean / (M : ℝ) < Delta / 2 := by
    apply (div_lt_iff₀ (show (0 : ℝ) < M by exact_mod_cast hMpos)).2
    have hmul : 2 * gaussRoofMean < Delta * (M : ℝ) := by
      simpa only [mul_comm] using! (div_lt_iff₀ hDelta).1 hMlarge
    nlinarith
  have hstepEventually : ∀ᶠ L : ℕ in atTop,
      ((L / M : ℕ) : ℝ) * gaussRoofMean ≤
        Delta * (L : ℝ) / 2 := by
    filter_upwards with L
    have hcast : ((L / M : ℕ) : ℝ) ≤ (L : ℝ) / (M : ℝ) :=
      Nat.cast_div_le
    have hL0 : (0 : ℝ) ≤ L := Nat.cast_nonneg L
    calc
      ((L / M : ℕ) : ℝ) * gaussRoofMean ≤
          ((L : ℝ) / (M : ℝ)) * gaussRoofMean :=
        mul_le_mul_of_nonneg_right hcast gaussRoofMean_pos.le
      _ = (L : ℝ) * (gaussRoofMean / (M : ℝ)) := by ring
      _ ≤ (L : ℝ) * (Delta / 2) :=
        mul_le_mul_of_nonneg_left hmeanDiv.le hL0
      _ = Delta * (L : ℝ) / 2 := by ring
  have hupper : ∀ᶠ L : ℕ in atTop,
      gaussMeasure.real (gaussRoofLinearWindowBadEvent C L Delta) ≤
        ∑ j ∈ Finset.range (D + 2),
          gaussMeasure.real (meshBad j L) := by
    filter_upwards [hlong, hstepEventually] with L hLlong hLstep
    have hsubsetAE :
        gaussRoofLinearWindowBadEvent C L Delta ≤ᵐ[gaussMeasure]
          (⋃ j ∈ Finset.range (D + 2), meshBad j L : Set ℝ) := by
      filter_upwards [ae_monotone_gaussRoofSum] with x hxmono
      intro hxbad
      by_contra hxmesh
      have hmeshGood : ∀ j : ℕ, j ≤ C * M + 1 →
          |gaussRoofSum (j * (L / M)) x -
              ((j * (L / M) : ℕ) : ℝ) * gaussRoofMean| ≤
            Delta * (L : ℝ) / 2 := by
        intro j hj
        have hjrange : j ∈ Finset.range (D + 2) := by
          simp only [Finset.mem_range, D]
          omega
        have hnot : x ∉ meshBad j L := by
          intro hxj
          apply hxmesh
          exact mem_iUnion.mpr ⟨j,
            mem_iUnion.mpr ⟨hjrange, hxj⟩⟩
        change ¬Delta * (L : ℝ) / 2 <
          |gaussRoofSum (j * (L / M)) x -
            ((j * (L / M) : ℕ) : ℝ) * gaussRoofMean| at hnot
        exact le_of_not_gt hnot
      have hall := monotone_mesh_linear_window
        (fun n => gaussRoofSum n x) hxmono gaussRoofMean_pos.le
        hC hMpos hLlong hmeshGood hLstep
      rcases hxbad with ⟨n, hn, hbad⟩
      exact (not_lt_of_ge (hall n hn)) hbad
    have hmonoENN := measure_mono_ae hsubsetAE
    have hmonoReal :
        gaussMeasure.real (gaussRoofLinearWindowBadEvent C L Delta) ≤
          gaussMeasure.real
            (⋃ j ∈ Finset.range (D + 2), meshBad j L) :=
      ENNReal.toReal_mono (measure_ne_top gaussMeasure _) hmonoENN
    exact hmonoReal.trans
      (measureReal_biUnion_finset_le (Finset.range (D + 2))
        (fun j => meshBad j L))
  exact squeeze_zero'
    (Eventually.of_forall fun _ => measureReal_nonneg)
    hupper hsum

/-! ## The literal selected-prefix denominator event -/

/-- The selected terminal denominator is a measurable natural-valued
function. -/
theorem measurable_gaussPrefixDenominator (n : ℕ) :
    Measurable (gaussPrefixDenominator n) := by
  let : MeasurableSpace (PositiveDigitWord n) := ⊤
  have hselected : Measurable (selectedGaussPrefixWord n) :=
    measurable_selectedGaussPrefixWord n
  have hterminal : Measurable
      (fun w : PositiveDigitWord n => cfTerminalDenominator w.1) :=
    measurable_of_countable _
  simpa only [gaussPrefixDenominator] using! hterminal.comp hselected

/-- The single global event requested by the chronological marked-tuple
argument.  It directly uses the terminal denominator of the selected prefix.
-/
def gaussDenominatorLinearGoodEvent
    (C L : ℕ) (Delta : ℝ) : Set ℝ :=
  {x | ∀ n : ℕ, n ≤ C * L →
    |Real.log
        (cfTerminalDenominator (selectedGaussPrefixWord n x).1 : ℝ) -
      (n : ℝ) * gaussRoofMean| ≤ Delta * (L : ℝ)}

def gaussDenominatorLinearBadEvent
    (C L : ℕ) (Delta : ℝ) : Set ℝ :=
  {x | ∃ n : ℕ, n ≤ C * L ∧
    Delta * (L : ℝ) <
      |Real.log
          (cfTerminalDenominator (selectedGaussPrefixWord n x).1 : ℝ) -
        (n : ℝ) * gaussRoofMean|}

theorem gaussDenominatorLinearBadEvent_eq_compl
    (C L : ℕ) (Delta : ℝ) :
    gaussDenominatorLinearBadEvent C L Delta =
      (gaussDenominatorLinearGoodEvent C L Delta)ᶜ := by
  ext x
  change (∃ n : ℕ, n ≤ C * L ∧
      Delta * (L : ℝ) <
        |Real.log
            (cfTerminalDenominator (selectedGaussPrefixWord n x).1 : ℝ) -
          (n : ℝ) * gaussRoofMean|) ↔
    ¬(∀ n : ℕ, n ≤ C * L →
      |Real.log
          (cfTerminalDenominator (selectedGaussPrefixWord n x).1 : ℝ) -
        (n : ℝ) * gaussRoofMean| ≤ Delta * (L : ℝ))
  constructor
  · rintro ⟨n, hn, hbad⟩ hall
    exact (not_lt_of_ge (hall n hn)) hbad
  · intro hnot
    rcases not_forall.mp hnot with ⟨n, hn⟩
    rcases Classical.not_imp.mp hn with ⟨hnBound, hnBad⟩
    exact ⟨n, hnBound, lt_of_not_ge hnBad⟩

theorem measurableSet_gaussDenominatorLinearGoodEvent
    (C L : ℕ) (Delta : ℝ) :
    MeasurableSet (gaussDenominatorLinearGoodEvent C L Delta) := by
  let f : ℕ → ℝ → ℝ := fun n x =>
    |Real.log (gaussPrefixDenominator n x : ℝ) -
      (n : ℝ) * gaussRoofMean|
  have hf (n : ℕ) : Measurable (f n) := by
    dsimp only [f]
    have hcast : Measurable (fun k : ℕ => (k : ℝ)) :=
      measurable_of_countable _
    exact ((Real.measurable_log.comp
      (hcast.comp (measurable_gaussPrefixDenominator n))).sub_const _).abs
  have heq : gaussDenominatorLinearGoodEvent C L Delta =
      ⋂ n ∈ Finset.range (C * L + 1),
        {x | f n x ≤ Delta * (L : ℝ)} := by
    ext x
    simp only [gaussDenominatorLinearGoodEvent,
      mem_iInter, Finset.mem_range,
      mem_setOf_eq, Nat.lt_add_one_iff]
    rfl
  rw [heq]
  exact (Finset.range (C * L + 1)).measurableSet_biInter
    (fun n _hn => measurableSet_Iic.preimage (hf n))

theorem measurableSet_gaussDenominatorLinearBadEvent
    (C L : ℕ) (Delta : ℝ) :
    MeasurableSet (gaussDenominatorLinearBadEvent C L Delta) := by
  rw [gaussDenominatorLinearBadEvent_eq_compl]
  exact (measurableSet_gaussDenominatorLinearGoodEvent C L Delta).compl

/-- Maximal denominator-time weak law under invariant Gauss measure. -/
theorem tendsto_gaussDenominatorLinearBadEvent_gaussMeasureReal_zero
    {C : ℕ} (hC : 0 < C) {Delta : ℝ} (hDelta : 0 < Delta) :
    Tendsto
      (fun L : ℕ =>
        gaussMeasure.real
          (gaussDenominatorLinearBadEvent C L Delta))
      atTop (𝓝 0) := by
  have hroof := tendsto_gaussRoofLinearWindowBadEvent_measureReal_zero
    hC (show 0 < Delta / 2 by positivity)
  have hlogError : ∀ᶠ L : ℕ in atTop,
      Real.log 2 ≤ Delta * (L : ℝ) / 2 := by
    have hratio : Tendsto
        (fun L : ℕ => Real.log 2 / (L : ℝ)) atTop (𝓝 0) :=
      tendsto_const_div_atTop_nhds_zero_nat (Real.log 2)
    have hsmall : ∀ᶠ L : ℕ in atTop,
        Real.log 2 / (L : ℝ) < Delta / 2 :=
      (tendsto_order.1 hratio).2 (Delta / 2) (by positivity)
    filter_upwards [eventually_ge_atTop 1, hsmall] with L hL hs
    have hLR : (0 : ℝ) < L := by exact_mod_cast (show 0 < L by omega)
    have h := ((div_lt_iff₀ hLR).1 hs).le
    nlinarith
  have hupper : ∀ᶠ L : ℕ in atTop,
      gaussMeasure.real
          (gaussDenominatorLinearBadEvent C L Delta) ≤
        gaussMeasure.real
          (gaussRoofLinearWindowBadEvent C L (Delta / 2)) := by
    filter_upwards [hlogError] with L herror
    have hsubsetAE :
        gaussDenominatorLinearBadEvent C L Delta ≤ᵐ[gaussMeasure]
          (gaussRoofLinearWindowBadEvent C L (Delta / 2) : Set ℝ) := by
      filter_upwards [ae_nonterminating_gaussMeasure] with x hx
      rintro ⟨n, hn, hbad⟩
      refine ⟨n, hn, ?_⟩
      by_contra hroofSmall
      have hroofBound :
          |gaussRoofSum n x - (n : ℝ) * gaussRoofMean| ≤
            Delta / 2 * (L : ℝ) := le_of_not_gt hroofSmall
      have hdenRoof :=
        abs_gaussRoofSum_sub_log_gaussPrefixDenominator_le_log_two
          (n := n) hx.1 hx.2
      have htri := abs_sub_le
        (Real.log (gaussPrefixDenominator n x : ℝ))
        (gaussRoofSum n x) ((n : ℝ) * gaussRoofMean)
      have htotal :
          |Real.log (gaussPrefixDenominator n x : ℝ) -
              (n : ℝ) * gaussRoofMean| ≤ Delta * (L : ℝ) := by
        calc
          |Real.log (gaussPrefixDenominator n x : ℝ) -
              (n : ℝ) * gaussRoofMean| ≤
              |Real.log (gaussPrefixDenominator n x : ℝ) -
                gaussRoofSum n x| +
              |gaussRoofSum n x - (n : ℝ) * gaussRoofMean| := htri
          _ ≤ Real.log 2 + Delta / 2 * (L : ℝ) := by
            gcongr
            simpa only [abs_sub_comm] using! hdenRoof
          _ ≤ Delta * (L : ℝ) := by nlinarith [herror]
      exact (not_lt_of_ge htotal) hbad
    have hmono := measure_mono_ae hsubsetAE
    exact ENNReal.toReal_mono (measure_ne_top gaussMeasure _) hmono
  exact squeeze_zero'
    (Eventually.of_forall fun _ => measureReal_nonneg)
    hupper hroof

/-! ## Transfer of the single event to uniform Lebesgue measure -/

theorem uniform01Measure_eq_gaussMeasure_withDensity :
    uniform01Measure =
      gaussMeasure.withDensity lebesgueOverGaussDensity := by
  calc
    uniform01Measure = volume.restrict (Ioo (0 : ℝ) 1) := rfl
    _ = volume.restrict (Ioc (0 : ℝ) 1) :=
      restrict_Ioo_eq_restrict_Ioc
    _ = gaussMeasure.withDensity lebesgueOverGaussDensity :=
      gaussMeasure_withDensity_lebesgueOverGaussDensity.symm

/-- Quantitative absolute-continuity bound used to transfer vanishing
probabilities. -/
theorem uniform01Measure_le_gaussMeasure
    {s : Set ℝ} (hs : MeasurableSet s) :
    uniform01Measure s ≤
      ENNReal.ofReal (2 * Real.log 2) * gaussMeasure s := by
  rw [uniform01Measure_eq_gaussMeasure_withDensity,
    withDensity_apply _ hs]
  calc
    (∫⁻ x in s, lebesgueOverGaussDensity x ∂gaussMeasure) ≤
        ∫⁻ _x in s, ENNReal.ofReal (2 * Real.log 2)
          ∂gaussMeasure := by
      apply lintegral_mono_ae
      filter_upwards [ae_restrict_of_ae gaussMeasure_unit_ae] with x hx
      unfold lebesgueOverGaussDensity
      exact ENNReal.ofReal_le_ofReal
        (lebesgueOverGaussDensityReal_bounds
          (show x ∈ Icc (0 : ℝ) 1 from ⟨hx.1.le, hx.2⟩)).2
    _ = ENNReal.ofReal (2 * Real.log 2) * gaussMeasure s :=
      setLIntegral_const s _

theorem uniform01MeasureReal_le_gaussMeasureReal
    {s : Set ℝ} (hs : MeasurableSet s) :
    uniform01Measure.real s ≤
      (2 * Real.log 2) * gaussMeasure.real s := by
  have h := uniform01Measure_le_gaussMeasure hs
  have hreal := ENNReal.toReal_mono
    (ENNReal.mul_ne_top ENNReal.ofReal_ne_top
      (measure_ne_top gaussMeasure s)) h
  have hc0 : 0 ≤ 2 * Real.log 2 := by positivity
  simpa only [measureReal_def, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal hc0] using! hreal

/-- Final process-level time change in the exact form used by the marked
tuple proof: one selected-prefix event controls every depth `n ≤ C L`, and
its complement has vanishing uniform-Lebesgue probability. -/
theorem tendsto_gaussDenominatorLinearBadEvent_uniform01MeasureReal_zero
    {C : ℕ} (hC : 0 < C) {Delta : ℝ} (hDelta : 0 < Delta) :
    Tendsto
      (fun L : ℕ => uniform01Measure.real
        (gaussDenominatorLinearBadEvent C L Delta))
      atTop (𝓝 0) := by
  have hgauss :=
    tendsto_gaussDenominatorLinearBadEvent_gaussMeasureReal_zero
      hC hDelta
  have hupper : ∀ L : ℕ,
      uniform01Measure.real
          (gaussDenominatorLinearBadEvent C L Delta) ≤
        (2 * Real.log 2) * gaussMeasure.real
          (gaussDenominatorLinearBadEvent C L Delta) := by
    intro L
    exact uniform01MeasureReal_le_gaussMeasureReal
      (measurableSet_gaussDenominatorLinearBadEvent C L Delta)
  have hscaled : Tendsto
      (fun L : ℕ => (2 * Real.log 2) * gaussMeasure.real
        (gaussDenominatorLinearBadEvent C L Delta))
      atTop (𝓝 0) := by
    simpa only [mul_zero] using!
      (tendsto_const_nhds.mul hgauss)
  exact squeeze_zero'
    (Eventually.of_forall fun _ => measureReal_nonneg)
    (Eventually.of_forall hupper) hscaled

/-- Equivalent good-event formulation: the probability of the complement
of the simultaneous selected-denominator estimate tends to zero. -/
theorem tendsto_gaussDenominatorLinearGoodEvent_compl_uniform_zero
    {C : ℕ} (hC : 0 < C) {Delta : ℝ} (hDelta : 0 < Delta) :
    Tendsto
      (fun L : ℕ => uniform01Measure.real
        (gaussDenominatorLinearGoodEvent C L Delta)ᶜ)
      atTop (𝓝 0) := by
  simpa only [← gaussDenominatorLinearBadEvent_eq_compl] using!
    tendsto_gaussDenominatorLinearBadEvent_uniform01MeasureReal_zero
      hC hDelta

/-- Eventual epsilon form, convenient when the good event is inserted into
a finite factorial-moment sum. -/
theorem eventually_gaussDenominatorLinearGoodEvent_compl_measure_lt
    {C : ℕ} (hC : 0 < C) {Delta eta : ℝ}
    (hDelta : 0 < Delta) (heta : 0 < eta) :
    ∀ᶠ L : ℕ in atTop,
      uniform01Measure.real
        (gaussDenominatorLinearGoodEvent C L Delta)ᶜ < eta :=
  (tendsto_order.1
    (tendsto_gaussDenominatorLinearGoodEvent_compl_uniform_zero
      hC hDelta)).2 eta heta

end

end Erdos1002
