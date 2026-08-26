import ErdosProblems.Erdos1002.ResonanceGaussCoordinateBridge
import ErdosProblems.Erdos1002.FiniteShotConvergence

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Equality of literal marked-resonance counts and Gauss-prefix counts

On a fixed compact annulus and once `log N > 2A`, Legendre's inequality is
automatic.  This file upgrades the pointwise coordinate identities to a
finite bijection: the original denominator index `p` and the
continued-fraction depth `n` count exactly the same marked points away from
the explicit terminating null set.
-/

open Filter MeasureTheory Set
open scoped BigOperators

namespace Erdos1002

noncomputable section

local instance markedResonanceGaussCountBridgePropDecidable (P : Prop) :
    Decidable P := Classical.propDecidable P

/-- A positive word has depth at most its terminal denominator.  This
elementary bound makes the depth-indexed count finite with cutoff `N`. -/
theorem length_le_cfTerminalDenominator
    {w : List ℕ} (hpos : IsPositiveCFWord w) :
    w.length ≤ cfTerminalDenominator w := by
  induction w with
  | nil => simp
  | cons a w ih =>
      have ha : 0 < a := hpos a (by simp)
      have htail : IsPositiveCFWord w := by
        intro q hq
        exact hpos q (by simp [hq])
      have ih' := ih htail
      cases w with
      | nil =>
          simpa using! ha
      | cons b v =>
          have hvpos : IsPositiveCFWord v := by
            intro q hq
            exact htail q (by simp [hq])
          have hDv : 0 < cfTerminalDenominator v :=
            cfTerminalDenominator_pos hvpos
          calc
            (a :: b :: v).length = (b :: v).length + 1 := by simp
            _ ≤ cfTerminalDenominator (b :: v) + 1 :=
              Nat.add_le_add_right ih' 1
            _ ≤ a * cfTerminalDenominator (b :: v) +
                cfTerminalDenominator v :=
              Nat.add_le_add (Nat.le_mul_of_pos_left _ ha)
                (Nat.succ_le_iff.mpr hDv)
            _ = cfTerminalDenominator (a :: b :: v) := by
              simp only [cfTerminalDenominator_cons,
                cfTerminalNumerator_cons]

/-- The marked event indexed by one continued-fraction depth.  The union is
over all positive words of that depth, but the half-open cylinders are
disjoint, so at most one word can contribute at a given point. -/
def gaussPrefixMarkedEvent (N : ℕ) (B : Set (ℝ × ℝ × ℝ))
    (n : ℕ) : Set ℝ :=
  ⋃ w : PositiveDigitWord n,
    if cfTerminalDenominator w.1 ≤ N then
      positivePrefixCylinder n w ∩
        {x | gaussApproximationCoordinate n x < (1 : ℝ) / 2} ∩
        gaussPrefixMarkedPoint N n w ⁻¹' B
    else ∅

theorem mem_gaussPrefixMarkedEvent_iff
    {N n : ℕ} {B : Set (ℝ × ℝ × ℝ)} {x : ℝ} :
    x ∈ gaussPrefixMarkedEvent N B n ↔
      ∃ w : PositiveDigitWord n,
        x ∈ positivePrefixCylinder n w ∧
        cfTerminalDenominator w.1 ≤ N ∧
        gaussApproximationCoordinate n x < (1 : ℝ) / 2 ∧
        gaussPrefixMarkedPoint N n w x ∈ B := by
  constructor
  · intro hx
    rcases mem_iUnion.mp hx with ⟨w, hw⟩
    by_cases hden : cfTerminalDenominator w.1 ≤ N
    · rw [if_pos hden] at hw
      exact ⟨w, hw.1.1, hden, hw.1.2, hw.2⟩
    · rw [if_neg hden] at hw
      exact hw.elim
  · rintro ⟨w, hw, hden, htheta, hpoint⟩
    apply mem_iUnion.mpr
    refine ⟨w, ?_⟩
    rw [if_pos hden]
    exact ⟨⟨hw, htheta⟩, hpoint⟩

theorem measurableSet_gaussPrefixMarkedEvent
    (N n : ℕ) {B : Set (ℝ × ℝ × ℝ)}
    (hB : MeasurableSet B) :
    MeasurableSet (gaussPrefixMarkedEvent N B n) := by
  unfold gaussPrefixMarkedEvent
  apply MeasurableSet.iUnion
  intro w
  split
  · exact ((measurableSet_positivePrefixCylinder n w).inter
      (measurableSet_lt (measurable_gaussApproximationCoordinate n)
        measurable_const)).inter
      (hB.preimage (measurable_gaussPrefixMarkedPoint N n w))
  · exact MeasurableSet.empty

/-- Finite depth-indexed marked count. -/
def gaussPrefixMarkedCount (N : ℕ) (B : Set (ℝ × ℝ × ℝ))
    (x : ℝ) : ℕ :=
  ∑ n ∈ Finset.Icc 0 N,
    if x ∈ gaussPrefixMarkedEvent N B n then 1 else 0

/-- Relation implementing the denominator/depth correspondence. -/
def ResonanceGaussDepthRelation (N : ℕ)
    (B : Set (ℝ × ℝ × ℝ)) (x : ℝ) (p n : ℕ) : Prop :=
  ∃ w : PositiveDigitWord n,
    x ∈ positivePrefixCylinder n w ∧
    p = cfTerminalDenominator w.1 ∧
    gaussApproximationCoordinate n x < (1 : ℝ) / 2 ∧
    gaussPrefixMarkedPoint N n w x ∈ B

theorem measurable_gaussPrefixMarkedCount
    (N : ℕ) {B : Set (ℝ × ℝ × ℝ)}
    (hB : MeasurableSet B) :
    Measurable (gaussPrefixMarkedCount N B) := by
  unfold gaussPrefixMarkedCount
  apply Finset.measurable_fun_sum
  intro n _hn
  exact Measurable.ite (measurableSet_gaussPrefixMarkedEvent N n hB)
    measurable_const measurable_const

/-- Membership in a fixed marked annulus forces Legendre's inequality once
`log N > 2A`. -/
theorem resonanceDelta_abs_lt_legendre_of_mem_compactAnnular
    {N p : ℕ} {x ε A : ℝ} (hN : 2 ≤ N)
    (hp : p ∈ Finset.Icc 1 N) (hε : 0 ≤ ε)
    (hlog : 2 * A < Real.log (N : ℝ))
    (hpoint : markedResonancePoint N p x ∈
      compactAnnularMarkedRegion ε A) :
    |resonanceDelta p x| < 1 / (2 * (p : ℝ)) := by
  have hlogPos : 0 < Real.log (N : ℝ) :=
    Real.log_pos (by exact_mod_cast hN)
  have hpBounds := Finset.mem_Icc.mp hp
  have hpNat : 0 < p := lt_of_lt_of_le Nat.zero_lt_one hpBounds.1
  have hpR : (0 : ℝ) < p := by exact_mod_cast hpNat
  have hupper :=
    ((markedResonancePoint_mem_compactAnnularMarkedRegion_iff
      hN hp hε x).1 hpoint).2
  have habsScaled :
      |scaledResonanceCoordinate N p x| =
        Real.log (N : ℝ) * (p : ℝ) * |resonanceDelta p x| := by
    unfold scaledResonanceCoordinate
    rw [abs_mul, abs_mul, abs_of_pos hlogPos, abs_of_pos hpR]
  rw [habsScaled] at hupper
  have hyLe : (p : ℝ) * |resonanceDelta p x| ≤
      A / Real.log (N : ℝ) := by
    apply (le_div_iff₀ hlogPos).2
    calc
      (p : ℝ) * |resonanceDelta p x| * Real.log (N : ℝ) =
          Real.log (N : ℝ) * (p : ℝ) *
            |resonanceDelta p x| := by ring
      _ ≤ A := hupper
  have hratio : A / Real.log (N : ℝ) < (1 : ℝ) / 2 := by
    apply (div_lt_iff₀ hlogPos).2
    linarith
  have hy : (p : ℝ) * |resonanceDelta p x| < (1 : ℝ) / 2 :=
    hyLe.trans_lt hratio
  calc
    |resonanceDelta p x| < ((1 : ℝ) / 2) / p := by
      apply (lt_div_iff₀ hpR).2
      simpa only [mul_comm] using! hy
    _ = 1 / (2 * (p : ℝ)) := by ring

/-- Forward half of the finite bijection: one literal marked denominator in
the annulus supplies a retained Gauss-prefix depth no larger than `N`. -/
theorem exists_depth_relation_of_marked
    {N p : ℕ} {x ε A : ℝ} {B : Set (ℝ × ℝ × ℝ)}
    (hN : 2 ≤ N) (hε : 0 ≤ ε)
    (hlog : 2 * A < Real.log (N : ℝ))
    (hB : B ⊆ compactAnnularMarkedRegion ε A)
    (hx : x ∈ Ioo (0 : ℝ) 1)
    (hnonterm : ∀ k : ℕ, (gaussMap^[k]) x ≠ 0)
    (hp : p ∈ Finset.Icc 1 N)
    (hprim : IsPrimitiveResonance p x)
    (hpoint : markedResonancePoint N p x ∈ B) :
    ∃ n ∈ Finset.Icc 0 N,
      ResonanceGaussDepthRelation N B x p n := by
  have hpBounds := Finset.mem_Icc.mp hp
  have hpPos : 0 < p := lt_of_lt_of_le Nat.zero_lt_one hpBounds.1
  have hsmall := resonanceDelta_abs_lt_legendre_of_mem_compactAnnular
    hN hp hε hlog (hB hpoint)
  obtain ⟨n, w, hw, hpDen, _hnum, hdelta, hscaled, htorus⟩ :=
    exists_gaussPrefix_coordinates_of_small_primitive_resonance
      (N := N) hx hpPos hprim hsmall hnonterm
  have hex : x ∉ gaussPrefixExceptional (n + 1) :=
    not_mem_gaussPrefixExceptional_of_nonterminating hx hnonterm _
  have hthetaPos :=
    gaussApproximationCoordinate_pos_of_mem_positivePrefix w hx hex hw
  have hpR : (0 : ℝ) < p := by exact_mod_cast hpPos
  have habsDelta : |resonanceDelta p x| =
      gaussApproximationCoordinate n x / p := by
    rw [hdelta, abs_div, abs_mul, abs_pow, abs_neg, abs_one,
      one_pow, one_mul, abs_of_pos hthetaPos, abs_of_pos hpR]
  have hthetaSmall :
      gaussApproximationCoordinate n x < (1 : ℝ) / 2 := by
    have hdiv : gaussApproximationCoordinate n x / p <
        ((1 : ℝ) / 2) / p := by
      calc
        gaussApproximationCoordinate n x / p =
            |resonanceDelta p x| := habsDelta.symm
        _ < 1 / (2 * (p : ℝ)) := hsmall
        _ = ((1 : ℝ) / 2) / p := by ring
    exact (div_lt_div_iff_of_pos_right hpR).1 hdiv
  have hpointEq : markedResonancePoint N p x =
      gaussPrefixMarkedPoint N n w x := by
    rw [hpDen] at hscaled htorus
    unfold markedResonancePoint gaussPrefixMarkedPoint resonanceTimeCoordinate
    rw [hpDen, hscaled, htorus]
  have hnLe : n ≤ N := by
    calc
      n = w.1.length := w.2.1.symm
      _ ≤ cfTerminalDenominator w.1 :=
        length_le_cfTerminalDenominator w.2.2
      _ = p := hpDen.symm
      _ ≤ N := hpBounds.2
  refine ⟨n, Finset.mem_Icc.mpr ⟨Nat.zero_le n, hnLe⟩, ?_⟩
  exact ⟨w, hw, hpDen, hthetaSmall, hpointEq ▸ hpoint⟩

/-- Event-valued corollary of the forward relation. -/
theorem exists_depth_mem_gaussPrefixMarkedEvent_of_marked
    {N p : ℕ} {x ε A : ℝ} {B : Set (ℝ × ℝ × ℝ)}
    (hN : 2 ≤ N) (hε : 0 ≤ ε)
    (hlog : 2 * A < Real.log (N : ℝ))
    (hB : B ⊆ compactAnnularMarkedRegion ε A)
    (hx : x ∈ Ioo (0 : ℝ) 1)
    (hnonterm : ∀ k : ℕ, (gaussMap^[k]) x ≠ 0)
    (hp : p ∈ Finset.Icc 1 N)
    (hprim : IsPrimitiveResonance p x)
    (hpoint : markedResonancePoint N p x ∈ B) :
    ∃ n ∈ Finset.Icc 0 N, x ∈ gaussPrefixMarkedEvent N B n := by
  obtain ⟨n, hn, w, hw, hpDen, htheta, hpointGauss⟩ :=
    exists_depth_relation_of_marked hN hε hlog hB hx hnonterm hp hprim hpoint
  have hpBounds := Finset.mem_Icc.mp hp
  refine ⟨n, hn, mem_gaussPrefixMarkedEvent_iff.mpr ?_⟩
  exact ⟨w, hw, hpDen ▸ hpBounds.2, htheta, hpointGauss⟩

/-- Reverse half of the finite bijection: a retained Gauss-prefix depth
supplies its literal primitive denominator and marked point. -/
theorem exists_denominator_of_mem_gaussPrefixMarkedEvent
    {N n : ℕ} {x : ℝ} {B : Set (ℝ × ℝ × ℝ)}
    (hx : x ∈ Ioo (0 : ℝ) 1)
    (hnonterm : ∀ k : ℕ, (gaussMap^[k]) x ≠ 0)
    (hevent : x ∈ gaussPrefixMarkedEvent N B n) :
    ∃ p ∈ Finset.Icc 1 N,
      IsPrimitiveResonance p x ∧ markedResonancePoint N p x ∈ B := by
  obtain ⟨w, hw, hden, htheta, hpoint⟩ :=
    mem_gaussPrefixMarkedEvent_iff.mp hevent
  have hex : x ∉ gaussPrefixExceptional (n + 1) :=
    not_mem_gaussPrefixExceptional_of_nonterminating hx hnonterm _
  obtain ⟨_hnum, hprim, _hdelta, _hsmall⟩ :=
    terminalPrefix_is_small_primitive_resonance w hx hex hw htheta
  have hpointEq :=
    markedResonancePoint_terminalDenominator_eq_gaussPrefixMarkedPoint
      (N := N) w hx hex hw htheta
  have hpPos : 0 < cfTerminalDenominator w.1 :=
    cfTerminalDenominator_pos w.2.2
  refine ⟨cfTerminalDenominator w.1,
    Finset.mem_Icc.mpr ⟨Nat.succ_le_iff.mpr hpPos, hden⟩,
    hprim, ?_⟩
  rwa [hpointEq]

theorem ResonanceGaussDepthRelation.mem_event_of_denominator_le
    {N p n : ℕ} {x : ℝ} {B : Set (ℝ × ℝ × ℝ)}
    (hrel : ResonanceGaussDepthRelation N B x p n) (hpN : p ≤ N) :
    x ∈ gaussPrefixMarkedEvent N B n := by
  obtain ⟨w, hw, hpDen, htheta, hpoint⟩ := hrel
  apply mem_gaussPrefixMarkedEvent_iff.mpr
  exact ⟨w, hw, hpDen ▸ hpN, htheta, hpoint⟩

/-- At one fixed depth, the half-open cylinder convention makes the
denominator side of the relation unique. -/
theorem ResonanceGaussDepthRelation.left_unique
    {N n p q : ℕ} {x : ℝ} {B : Set (ℝ × ℝ × ℝ)}
    (hp : ResonanceGaussDepthRelation N B x p n)
    (hq : ResonanceGaussDepthRelation N B x q n) :
    p = q := by
  obtain ⟨w, hw, hpDen, _hthetaW, _hpointW⟩ := hp
  obtain ⟨v, hv, hqDen, _hthetaV, _hpointV⟩ := hq
  have hwv : w = v := by
    by_contra hne
    exact (Set.disjoint_left.mp
      (pairwise_disjoint_positivePrefixCylinder n hne) hw hv).elim
  subst v
  exact hpDen.trans hqDen.symm

/-- For a nonterminating point, one literal denominator occurs at only one
retained depth. -/
theorem ResonanceGaussDepthRelation.right_unique
    {N p n m : ℕ} {x : ℝ} {B : Set (ℝ × ℝ × ℝ)}
    (hx : x ∈ Ioo (0 : ℝ) 1)
    (hnonterm : ∀ k : ℕ, (gaussMap^[k]) x ≠ 0)
    (hn : ResonanceGaussDepthRelation N B x p n)
    (hm : ResonanceGaussDepthRelation N B x p m) :
    n = m := by
  obtain ⟨w, hw, hpDenW, hthetaW, _hpointW⟩ := hn
  obtain ⟨v, hv, hpDenV, hthetaV, _hpointV⟩ := hm
  have hexW : x ∉ gaussPrefixExceptional (n + 1) :=
    not_mem_gaussPrefixExceptional_of_nonterminating hx hnonterm _
  have hexV : x ∉ gaussPrefixExceptional (m + 1) :=
    not_mem_gaussPrefixExceptional_of_nonterminating hx hnonterm _
  obtain ⟨hnumW, _hprimW, _hdeltaW, _hsmallW⟩ :=
    terminalPrefix_is_small_primitive_resonance w hx hexW hw hthetaW
  obtain ⟨hnumV, _hprimV, _hdeltaV, _hsmallV⟩ :=
    terminalPrefix_is_small_primitive_resonance v hx hexV hv hthetaV
  rw [← hpDenW] at hnumW
  rw [← hpDenV] at hnumV
  have hpair : cfTerminalPair w.1 = cfTerminalPair v.1 := by
    apply Prod.ext
    · simpa [cfTerminalNumerator] using! hnumW.symm.trans hnumV
    · simpa [cfTerminalDenominator] using! hpDenW.symm.trans hpDenV
  exact positivePrefix_depth_eq_of_terminalPair_eq
    w v hx hexW hexV hw hv hpair

/-- An event depth supplies a denominator together with both sides of the
correspondence. -/
theorem exists_denominator_relation_of_mem_gaussPrefixMarkedEvent
    {N n : ℕ} {x : ℝ} {B : Set (ℝ × ℝ × ℝ)}
    (hx : x ∈ Ioo (0 : ℝ) 1)
    (hnonterm : ∀ k : ℕ, (gaussMap^[k]) x ≠ 0)
    (hevent : x ∈ gaussPrefixMarkedEvent N B n) :
    ∃ p ∈ Finset.Icc 1 N,
      ResonanceGaussDepthRelation N B x p n ∧
      IsPrimitiveResonance p x ∧ markedResonancePoint N p x ∈ B := by
  obtain ⟨w, hw, hden, htheta, hpoint⟩ :=
    mem_gaussPrefixMarkedEvent_iff.mp hevent
  have hex : x ∉ gaussPrefixExceptional (n + 1) :=
    not_mem_gaussPrefixExceptional_of_nonterminating hx hnonterm _
  obtain ⟨_hnum, hprim, _hdelta, _hsmall⟩ :=
    terminalPrefix_is_small_primitive_resonance w hx hex hw htheta
  have hpointEq :=
    markedResonancePoint_terminalDenominator_eq_gaussPrefixMarkedPoint
      (N := N) w hx hex hw htheta
  have hpPos : 0 < cfTerminalDenominator w.1 :=
    cfTerminalDenominator_pos w.2.2
  refine ⟨cfTerminalDenominator w.1,
    Finset.mem_Icc.mpr ⟨Nat.succ_le_iff.mpr hpPos, hden⟩,
    ⟨w, hw, rfl, htheta, hpoint⟩, hprim, ?_⟩
  rwa [hpointEq]

/-- Exact finite count identity on every nonterminating point.  This is the
literal denominator-to-depth bijection needed before any factorial-moment
or oscillatory argument is applied. -/
theorem markedResonanceCount_eq_gaussPrefixMarkedCount
    {N : ℕ} {x ε A : ℝ} {B : Set (ℝ × ℝ × ℝ)}
    (hN : 2 ≤ N) (hε : 0 ≤ ε)
    (hlog : 2 * A < Real.log (N : ℝ))
    (hB : B ⊆ compactAnnularMarkedRegion ε A)
    (hx : x ∈ Ioo (0 : ℝ) 1)
    (hnonterm : ∀ k : ℕ, (gaussMap^[k]) x ≠ 0) :
    markedResonanceCount N N B x = gaussPrefixMarkedCount N B x := by
  classical
  let S : Finset ℕ := (Finset.Icc 1 N).filter fun p ↦
    IsPrimitiveResonance p x ∧ markedResonancePoint N p x ∈ B
  let T : Finset ℕ := (Finset.Icc 0 N).filter fun n ↦
    x ∈ gaussPrefixMarkedEvent N B n
  have hmarked : markedResonanceCount N N B x = S.card := by
    unfold markedResonanceCount S
    exact Finset.sum_boole _ _
  have hgauss : gaussPrefixMarkedCount N B x = T.card := by
    unfold gaussPrefixMarkedCount T
    exact Finset.sum_boole _ _
  have hforward : ∀ p ∈ S, ∃ n ∈ T,
      ResonanceGaussDepthRelation N B x p n := by
    intro p hpS
    have hpData := Finset.mem_filter.mp hpS
    obtain ⟨n, hn, hrel⟩ := exists_depth_relation_of_marked
      hN hε hlog hB hx hnonterm hpData.1 hpData.2.1 hpData.2.2
    have hpBounds := Finset.mem_Icc.mp hpData.1
    refine ⟨n, Finset.mem_filter.mpr ⟨hn, ?_⟩, hrel⟩
    exact hrel.mem_event_of_denominator_le hpBounds.2
  let depth : ∀ p ∈ S, ℕ := fun p hpS ↦
    Classical.choose (hforward p hpS)
  have depth_mem (p : ℕ) (hpS : p ∈ S) : depth p hpS ∈ T :=
    (Classical.choose_spec (hforward p hpS)).1
  have depth_rel (p : ℕ) (hpS : p ∈ S) :
      ResonanceGaussDepthRelation N B x p (depth p hpS) :=
    (Classical.choose_spec (hforward p hpS)).2
  rw [hmarked, hgauss]
  apply Finset.card_bij depth depth_mem
  · intro p hpS q hqS heq
    have hqRel : ResonanceGaussDepthRelation N B x q (depth p hpS) := by
      rw [heq]
      exact depth_rel q hqS
    exact ResonanceGaussDepthRelation.left_unique (depth_rel p hpS) hqRel
  · intro n hnT
    have hevent := (Finset.mem_filter.mp hnT).2
    obtain ⟨p, hp, hrel, hprim, hpoint⟩ :=
      exists_denominator_relation_of_mem_gaussPrefixMarkedEvent
        hx hnonterm hevent
    have hpS : p ∈ S :=
      Finset.mem_filter.mpr ⟨hp, hprim, hpoint⟩
    refine ⟨p, hpS, ?_⟩
    exact ResonanceGaussDepthRelation.right_unique
      hx hnonterm (depth_rel p hpS) hrel

/-- Uniform Lebesgue-almost every point in `(0,1)` has a nonterminating
Gauss orbit.  The exceptional set is written as the explicit countable
union of the finite-prefix exceptional sets. -/
theorem ae_nonterminating_uniform01 :
    ∀ᵐ x ∂uniform01Measure,
      x ∈ Ioo (0 : ℝ) 1 ∧ ∀ k : ℕ, (gaussMap^[k]) x ≠ 0 := by
  let E : Set ℝ := ⋃ b : ℕ, gaussPrefixExceptional b
  have hEmeas : MeasurableSet E := by
    exact MeasurableSet.iUnion measurableSet_gaussPrefixExceptional
  have hEzero : volume E = 0 := by
    exact MeasureTheory.measure_iUnion_null
      (fun b ↦ volume_gaussPrefixExceptional b)
  have hEzeroUniform : uniform01Measure E = 0 := by
    rw [uniform01Measure, Measure.restrict_apply hEmeas]
    exact MeasureTheory.measure_mono_null inter_subset_left hEzero
  have hnotE : ∀ᵐ x ∂uniform01Measure, x ∉ E :=
    measure_eq_zero_iff_ae_notMem.mp hEzeroUniform
  have hunit : ∀ᵐ x ∂uniform01Measure, x ∈ Ioo (0 : ℝ) 1 := by
    rw [uniform01Measure]
    exact ae_restrict_mem measurableSet_Ioo
  filter_upwards [hunit, hnotE] with x hx hxE
  refine ⟨hx, ?_⟩
  intro k hk
  apply hxE
  apply mem_iUnion.mpr
  refine ⟨k + 1, Or.inl ⟨⟨hx.1, hx.2.le⟩, ?_⟩⟩
  apply mem_iUnion.mpr
  refine ⟨⟨k, by omega⟩, ?_⟩
  simpa only [mem_preimage, mem_singleton_iff] using! hk

/-- Almost-everywhere form consumed by laws and factorial moments. -/
theorem ae_markedResonanceCount_eq_gaussPrefixMarkedCount
    {N : ℕ} {ε A : ℝ} {B : Set (ℝ × ℝ × ℝ)}
    (hN : 2 ≤ N) (hε : 0 ≤ ε)
    (hlog : 2 * A < Real.log (N : ℝ))
    (hB : B ⊆ compactAnnularMarkedRegion ε A) :
    markedResonanceCount N N B =ᵐ[uniform01Measure]
      gaussPrefixMarkedCount N B := by
  filter_upwards [ae_nonterminating_uniform01] with x hx
  exact markedResonanceCount_eq_gaussPrefixMarkedCount
    hN hε hlog hB hx.1 hx.2

/-! ## Count-vector laws after the exact bijection -/

variable {ι : Type*} [Fintype ι]

open MultivariateFactorialMomentMethod

def gaussPrefixMarkedCountVector (N : ℕ)
    (B : ι → Set (ℝ × ℝ × ℝ)) (x : ℝ) : ι → ℕ :=
  fun i ↦ gaussPrefixMarkedCount N (B i) x

omit [Fintype ι] in
theorem measurable_gaussPrefixMarkedCountVector
    (N : ℕ) {B : ι → Set (ℝ × ℝ × ℝ)}
    (hB : ∀ i, MeasurableSet (B i)) :
    Measurable (gaussPrefixMarkedCountVector N B) := by
  apply measurable_pi_lambda
  intro i
  exact measurable_gaussPrefixMarkedCount N (hB i)

def gaussPrefixMarkedCountVectorLaw (N : ℕ)
    (B : ι → Set (ℝ × ℝ × ℝ))
    (hB : ∀ i, MeasurableSet (B i)) : ProbabilityMeasure (ι → ℕ) :=
  uniform01.map (measurable_gaussPrefixMarkedCountVector N hB).aemeasurable

/-- Equality of the actual count-vector law with its finite Gauss-prefix
model for every sufficiently large fixed `N`. -/
theorem markedResonanceCountVectorLaw_eq_gaussPrefix
    {N : ℕ} {ε A : ℝ} (B : ι → Set (ℝ × ℝ × ℝ))
    (hBmeas : ∀ i, MeasurableSet (B i))
    (hBsub : ∀ i, B i ⊆ compactAnnularMarkedRegion ε A)
    (hN : 2 ≤ N) (hε : 0 ≤ ε)
    (hlog : 2 * A < Real.log (N : ℝ)) :
    markedResonanceCountVectorLaw N N B hBmeas =
      gaussPrefixMarkedCountVectorLaw N B hBmeas := by
  apply ProbabilityMeasure.toMeasure_injective
  change Measure.map (markedResonanceCountVector N N B) uniform01Measure =
    Measure.map (gaussPrefixMarkedCountVector N B) uniform01Measure
  apply Measure.map_congr
  have hall : ∀ᵐ x ∂uniform01Measure, ∀ i,
      markedResonanceCount N N (B i) x =
        gaussPrefixMarkedCount N (B i) x :=
    ae_all_iff.mpr fun i ↦
      ae_markedResonanceCount_eq_gaussPrefixMarkedCount
        hN hε hlog (hBsub i)
  filter_upwards [hall] with x hx
  funext i
  exact hx i

/-- Consequently every mixed factorial moment of the actual grid count is
literally the corresponding Gauss-prefix moment. -/
theorem mixedFactorialMoment_markedResonance_eq_gaussPrefix
    {N : ℕ} {ε A : ℝ} (B : ι → Set (ℝ × ℝ × ℝ))
    (hBmeas : ∀ i, MeasurableSet (B i))
    (hBsub : ∀ i, B i ⊆ compactAnnularMarkedRegion ε A)
    (hN : 2 ≤ N) (hε : 0 ≤ ε)
    (hlog : 2 * A < Real.log (N : ℝ)) (k : ι → ℕ) :
    mixedFactorialMoment (markedResonanceCountVectorLaw N N B hBmeas) k =
      mixedFactorialMoment (gaussPrefixMarkedCountVectorLaw N B hBmeas) k := by
  rw [markedResonanceCountVectorLaw_eq_gaussPrefix
    B hBmeas hBsub hN hε hlog]

/-- For fixed annular windows the law identity holds eventually as the
natural denominator cutoff tends to infinity. -/
theorem eventually_markedResonanceCountVectorLaw_eq_gaussPrefix
    {ε A : ℝ} (B : ι → Set (ℝ × ℝ × ℝ))
    (hBmeas : ∀ i, MeasurableSet (B i))
    (hBsub : ∀ i, B i ⊆ compactAnnularMarkedRegion ε A)
    (hε : 0 ≤ ε) :
    ∀ᶠ N : ℕ in atTop,
      markedResonanceCountVectorLaw N N B hBmeas =
        gaussPrefixMarkedCountVectorLaw N B hBmeas := by
  have hlogTop : Tendsto (fun N : ℕ ↦ Real.log (N : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hlogLarge : ∀ᶠ N : ℕ in atTop,
      2 * A + 1 ≤ Real.log (N : ℝ) :=
    (tendsto_atTop.1 hlogTop (2 * A + 1))
  filter_upwards [eventually_ge_atTop 2, hlogLarge] with N hN hlog
  exact markedResonanceCountVectorLaw_eq_gaussPrefix
    B hBmeas hBsub hN hε (by linarith)

/-- A Gauss-prefix mixed-factorial limit therefore transfers verbatim to
the actual marked grid counts. -/
theorem tendsto_mixedFactorialMoment_markedResonance_of_gaussPrefix
    {ε A limit : ℝ} (B : ι → Set (ℝ × ℝ × ℝ))
    (hBmeas : ∀ i, MeasurableSet (B i))
    (hBsub : ∀ i, B i ⊆ compactAnnularMarkedRegion ε A)
    (hε : 0 ≤ ε) (k : ι → ℕ)
    (hGauss : Tendsto
      (fun N ↦ mixedFactorialMoment
        (gaussPrefixMarkedCountVectorLaw N B hBmeas) k)
      atTop (nhds limit)) :
    Tendsto
      (fun N ↦ mixedFactorialMoment
        (markedResonanceCountVectorLaw N N B hBmeas) k)
      atTop (nhds limit) := by
  apply hGauss.congr'
  filter_upwards
    [eventually_markedResonanceCountVectorLaw_eq_gaussPrefix
      B hBmeas hBsub hε] with N hN
  rw [hN]

end

end Erdos1002
