import ErdosProblems.Erdos1002.ActualGridFinalReduction
import ErdosProblems.Erdos1002.FactorialMomentBounds
import ErdosProblems.Erdos1002.GaussPrefixAnnularBoundaryCells
import Mathlib.Topology.MetricSpace.Bounded

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Assembly of nonterminal and terminal annular grid cells

The marked Fourier argument naturally proves mixed factorial limits when
every positively used cell is nonterminal.  This file proves that this is
enough for the full literal grid statement.

The only nontrivial boundary case is a terminal time cell used to first
factorial order.  Its count is rare but it may be multiplied by other
counts.  We therefore first obtain uniform ordinary moments of every
coordinate from higher single-coordinate factorial limits, and only then
apply the proved rare-coordinate deletion lemma.
-/

open Filter MeasureTheory Set Finset
open scoped BigOperators Topology

namespace Erdos1002

noncomputable section

open MultivariateFactorialMomentMethod

local instance gaussPrefixAnnularBoundaryAssemblyPropDecidable (P : Prop) :
    Decidable P := Classical.propDecidable P

/-- The exact interior input produced by the marked Fourier argument:
only cells occurring with positive factorial order are required to be
nonterminal. -/
def GaussPrefixNonterminalAnnularGridFactorialLimits : Prop :=
  ∀ {ε A : ℝ}, 0 < ε → ε < A →
    ∀ m (k : AnnularGridIndex (m + 1) → ℕ),
      (∀ i, 0 < k i →
        i.time.1 < m + 1 ∧ i.signed.1 < m + 1 ∧ i.torus.1 < m + 1) →
      Tendsto
        (fun N ↦ mixedFactorialMoment
          (gaussPrefixMarkedCountVectorLaw N
            (annularGridCell ε A (m + 1))
            (fun i ↦ measurableSet_annularGridCell ε A (m + 1) i)) k)
        atTop
        (nhds (∏ i,
          (annularGridCellPoissonRate ε A (m + 1) i : ℝ) ^ (k i)))

/-- A factorial order supported at one coordinate, with arbitrary order
`s` at that coordinate. -/
def coordinateFactorialOrder {ι : Type*} [DecidableEq ι]
    (i : ι) (s : ℕ) : ι → ℕ :=
  fun j ↦ if j = i then s else 0

@[simp]
theorem mixedDescFactorial_coordinateFactorialOrder
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (i : ι) (s : ℕ) (x : ι → ℕ) :
    mixedDescFactorial (coordinateFactorialOrder i s) x =
      (x i).descFactorial s := by
  classical
  unfold mixedDescFactorial coordinateFactorialOrder
  rw [Fintype.prod_eq_single i]
  · simp
  · intro j hji
    simp [hji]

@[simp]
theorem sum_coordinateFactorialOrder
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (i : ι) (s : ℕ) :
    ∑ j, coordinateFactorialOrder i s j = s := by
  classical
  unfold coordinateFactorialOrder
  rw [Fintype.sum_eq_single i]
  · simp
  · intro j hji
    simp [hji]

/-- The single-coordinate mixed factorial moment is literally the
integral of the corresponding falling factorial of that count. -/
theorem mixedFactorialMoment_coordinateFactorialOrder_gaussPrefix
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (N : ℕ) (B : ι → Set (ℝ × ℝ × ℝ))
    (hB : ∀ i, MeasurableSet (B i))
    (i : ι) (s : ℕ) :
    mixedFactorialMoment
        (gaussPrefixMarkedCountVectorLaw N B hB)
        (coordinateFactorialOrder i s) =
      ∫ α, ((gaussPrefixMarkedCount N (B i) α).descFactorial s : ℝ)
        ∂uniform01Measure := by
  rw [mixedFactorialMoment_gaussPrefixMarkedCountVectorLaw]
  apply integral_congr_ae
  filter_upwards with α
  simp only [mixedDescFactorial_coordinateFactorialOrder,
    gaussPrefixMarkedCountVector]

/-- Falling factorials of one finite Gauss-prefix count are integrable. -/
theorem integrable_gaussPrefixMarkedCount_descFactorial
    (N s : ℕ) {B : Set (ℝ × ℝ × ℝ)} (hB : MeasurableSet B) :
    Integrable
      (fun α ↦ ((gaussPrefixMarkedCount N B α).descFactorial s : ℝ))
      uniform01Measure := by
  have hmeas :
      Measurable
        (fun α ↦
          ((gaussPrefixMarkedCount N B α).descFactorial s : ℝ)) :=
    (measurable_of_countable
      (fun q : ℕ ↦ (q.descFactorial s : ℝ))).comp
        (measurable_gaussPrefixMarkedCount N hB)
  apply Integrable.of_bound hmeas.aestronglyMeasurable
    (((N + 1 : ℕ) : ℝ) ^ s)
  filter_upwards with α
  rw [Real.norm_of_nonneg (by positivity)]
  calc
    ((gaussPrefixMarkedCount N B α).descFactorial s : ℝ) ≤
        (gaussPrefixMarkedCount N B α : ℝ) ^ s := by
      exact_mod_cast
        Nat.descFactorial_le_pow (gaussPrefixMarkedCount N B α) s
    _ ≤ (((N + 1 : ℕ) : ℝ) ^ s) := by
      gcongr
      exact_mod_cast gaussPrefixMarkedCount_le_succ N B α

/-- Every coordinate's single-coordinate factorial moment of order at
least two is a convergent sequence.  For a nonterminal coordinate this is
the assumed interior theorem.  Terminal signed and torus coordinates
vanish, while a terminal time count is eventually at most one. -/
theorem tendsto_singleCoordinateFactorialMoment_of_nonterminal
    (hInterior : GaussPrefixNonterminalAnnularGridFactorialLimits)
    {ε A : ℝ} (hε : 0 < ε) (hεA : ε < A)
    (m : ℕ) (j : AnnularGridIndex (m + 1))
    {s : ℕ} (hs : 2 ≤ s) :
    ∃ c : ℝ,
      Tendsto
        (fun N ↦
          mixedFactorialMoment
            (gaussPrefixMarkedCountVectorLaw N
              (annularGridCell ε A (m + 1))
              (fun i ↦
                measurableSet_annularGridCell ε A (m + 1) i))
            (coordinateFactorialOrder j s))
        atTop (nhds c) := by
  let q : AnnularGridIndex (m + 1) → ℕ :=
    coordinateFactorialOrder j s
  have hqj : 0 < q j := by
    simp only [q, coordinateFactorialOrder, if_pos]
    omega
  have hqTwo : 2 ≤ q j := by
    simp only [q, coordinateFactorialOrder, if_pos]
    exact hs
  have htimeCases : j.time.1 < m + 1 ∨ j.time.1 = m + 1 := by
    omega
  have hsignedCases : j.signed.1 < m + 1 ∨ j.signed.1 = m + 1 := by
    omega
  have htorusCases : j.torus.1 < m + 1 ∨ j.torus.1 = m + 1 := by
    omega
  rcases htorusCases with htorus | htorus
  · rcases hsignedCases with hsigned | hsigned
    · rcases htimeCases with htime | htime
      · refine ⟨_, hInterior hε hεA m q ?_⟩
        intro i hi
        have hij : i = j := by
          by_contra hij
          simp [q, coordinateFactorialOrder, hij] at hi
        subst i
        exact ⟨htime, hsigned, htorus⟩
      · refine ⟨0, ?_⟩
        apply tendsto_const_nhds.congr'
        filter_upwards [eventually_ge_atTop 2,
          tendsto_log_natCast_atTop.eventually_gt_atTop (2 * A)]
            with N hN hlog
        symm
        exact
          mixedFactorialMoment_gaussPrefixAnnular_eq_zero_of_time_terminal_order_two
            hN hε.le hεA (by omega) hlog q
              hqTwo htime
    · refine ⟨0, ?_⟩
      apply tendsto_const_nhds.congr'
      filter_upwards [eventually_ge_atTop 2,
        tendsto_log_natCast_atTop.eventually_gt_atTop (2 * A)]
          with N hN hlog
      symm
      exact
        mixedFactorialMoment_gaussPrefixAnnular_eq_zero_of_active_signed_terminal
          hN hε.le hεA (by omega) hlog q hqj hsigned
  · refine ⟨0, ?_⟩
    apply tendsto_const_nhds.congr'
    filter_upwards with N
    symm
    exact
      mixedFactorialMoment_gaussPrefixAnnular_eq_zero_of_active_torus_terminal
        N ε A q hqj htorus

/-- Higher single-coordinate limits furnish one numerical ordinary-moment
bound which is uniform in both the horizon and the finite grid coordinate. -/
theorem exists_uniform_coordinateMoment_bound_of_nonterminal
    (hInterior : GaussPrefixNonterminalAnnularGridFactorialLimits)
    {ε A : ℝ} (hε : 0 < ε) (hεA : ε < A)
    (m s : ℕ) (hs : 2 ≤ s) :
    ∃ C : ℝ, ∀ N (j : AnnularGridIndex (m + 1)),
      ∫ α,
        (gaussPrefixMarkedCount N
          (annularGridCell ε A (m + 1) j) α : ℝ) ^ s
          ∂uniform01Measure ≤ C := by
  let moment : AnnularGridIndex (m + 1) → ℕ → ℝ :=
    fun j N ↦
      ∫ α,
        ((gaussPrefixMarkedCount N
          (annularGridCell ε A (m + 1) j) α).descFactorial s : ℝ)
        ∂uniform01Measure
  have htend : ∀ j : AnnularGridIndex (m + 1),
      ∃ c : ℝ, Tendsto (moment j) atTop (nhds c) := by
    intro j
    obtain ⟨c, hc⟩ :=
      tendsto_singleCoordinateFactorialMoment_of_nonterminal
        hInterior hε hεA m j hs
    refine ⟨c, ?_⟩
    apply hc.congr'
    filter_upwards with N
    exact
      mixedFactorialMoment_coordinateFactorialOrder_gaussPrefix
        N (annularGridCell ε A (m + 1))
          (fun i ↦ measurableSet_annularGridCell ε A (m + 1) i)
          j s
  have hbdd : ∀ j : AnnularGridIndex (m + 1),
      BddAbove (Set.range (moment j)) := by
    intro j
    obtain ⟨c, hc⟩ := htend j
    exact (Metric.isBounded_range_of_tendsto (moment j) hc).bddAbove
  let upper : AnnularGridIndex (m + 1) → ℝ :=
    fun j ↦ Classical.choose (hbdd j)
  have hupper : ∀ j N, moment j N ≤ upper j := by
    intro j N
    exact Classical.choose_spec (hbdd j) ⟨N, rfl⟩
  let facBound : ℝ :=
    ∑ j : AnnularGridIndex (m + 1), max 0 (upper j)
  have hfacBound : ∀ j N, moment j N ≤ facBound := by
    intro j N
    calc
      moment j N ≤ upper j := hupper j N
      _ ≤ max 0 (upper j) := le_max_right _ _
      _ ≤ ∑ q : AnnularGridIndex (m + 1), max 0 (upper q) := by
        exact Finset.single_le_sum
          (fun q _hq ↦ le_max_left 0 (upper q))
          (Finset.mem_univ j)
      _ = facBound := rfl
  refine ⟨
    (2 : ℝ) ^ s * facBound + ((2 * s : ℕ) : ℝ) ^ s, ?_⟩
  intro N j
  apply
    integral_natCast_pow_le_of_descFactorial_integral_le
      uniform01Measure
      (fun α ↦ gaussPrefixMarkedCount N
        (annularGridCell ε A (m + 1) j) α)
      (measurable_gaussPrefixMarkedCount N
        (measurableSet_annularGridCell ε A (m + 1) j))
      s
      (integrable_gaussPrefixMarkedCount_descFactorial N s
        (measurableSet_annularGridCell ε A (m + 1) j))
      (hfacBound j N)

/-- Interior mixed factorial limits imply the complete grid statement,
including all three kinds of terminal singleton cells. -/
theorem gaussPrefixAnnularGridFactorialLimits_of_nonterminal
    (hInterior : GaussPrefixNonterminalAnnularGridFactorialLimits) :
    GaussPrefixAnnularGridFactorialLimits := by
  intro ε A hε hεA m k
  by_cases hzero : ∀ i, k i = 0
  · have hk : k = fun _i ↦ 0 := funext hzero
    subst k
    exact gaussPrefixAnnularGridFactorialLimit_zero m
  by_cases hinterior :
      ∀ i, 0 < k i →
        i.time.1 < m + 1 ∧ i.signed.1 < m + 1 ∧ i.torus.1 < m + 1
  · exact hInterior hε hεA m k hinterior
  · rw [not_forall] at hinterior
    obtain ⟨i, hi⟩ := hinterior
    rw [_root_.not_imp] at hi
    obtain ⟨hki, hterminal⟩ := hi
    have hterminal' :
        i.time.1 = m + 1 ∨
          i.signed.1 = m + 1 ∨ i.torus.1 = m + 1 := by
      by_cases htime : i.time.1 < m + 1
      · by_cases hsigned : i.signed.1 < m + 1
        · right
          right
          omega
        · right
          left
          omega
      · left
        omega
    have htarget :
        (∏ j,
          (annularGridCellPoissonRate ε A (m + 1) j : ℝ) ^
            k j) = 0 :=
      prod_annularGridCellPoissonRate_pow_eq_zero_of_active_terminal
        ε A k hki hterminal'
    rw [htarget]
    rcases hterminal' with htime | hsigned | htorus
    · by_cases hkitwo : 2 ≤ k i
      · apply tendsto_const_nhds.congr'
        filter_upwards [eventually_ge_atTop 2,
          tendsto_log_natCast_atTop.eventually_gt_atTop (2 * A)]
            with N hN hlog
        symm
        exact
          mixedFactorialMoment_gaussPrefixAnnular_eq_zero_of_time_terminal_order_two
            hN hε.le hεA (by omega) hlog k hkitwo htime
      · have hkiOne : k i = 1 := by omega
        obtain ⟨C, hC⟩ :=
          exists_uniform_coordinateMoment_bound_of_nonterminal
            hInterior hε hεA m (2 * (∑ q, k q)) (by
              have hsum : 0 < ∑ q, k q :=
                (Finset.single_le_sum
                  (fun q _hq ↦ Nat.zero_le (k q))
                  (Finset.mem_univ i)).trans_lt' hki
              omega)
        exact
          tendsto_mixedFactorialMoment_gaussPrefixAnnular_of_active_time_terminal_of_uniform_coordinate_moments
            hε.le hεA (by omega) k hki htime hC
    · apply tendsto_const_nhds.congr'
      filter_upwards [eventually_ge_atTop 2,
        tendsto_log_natCast_atTop.eventually_gt_atTop (2 * A)]
          with N hN hlog
      symm
      exact
        mixedFactorialMoment_gaussPrefixAnnular_eq_zero_of_active_signed_terminal
          hN hε.le hεA (by omega) hlog k hki hsigned
    · apply tendsto_const_nhds.congr'
      filter_upwards with N
      symm
      exact
        mixedFactorialMoment_gaussPrefixAnnular_eq_zero_of_active_torus_terminal
          N ε A k hki htorus

end

end Erdos1002
