/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos285.Approximation
import ErdosProblems.Erdos285.Lemma12
import ErdosProblems.Erdos285.Lemma12Numerics
import ErdosProblems.Erdos285.PrimePowers
import ErdosProblems.Erdos285.SmoothReservoir

/-!
# Erdős 285: the construction in Martin's Proposition 6

This file begins the source-faithful construction, rather than treating the
large set in Proposition 6 as an unspecified input.

The initial block is

`{n : exp (-r) x < n ≤ x and every prime-power divisor of n is at most z}`.

The strict lower endpoint is arithmetically immaterial and has the useful formal
consequence that the lower smooth reservoir, whose elements are at most
`exp (-r) x`, is automatically disjoint from the main block.

The second part couples the finite-set recursion in `Approximation.lean` to the
running rational residual.  It proves the exact residual identity at every
stage and implements well-founded descent on the largest exact prime-power part
of the reduced residual denominator.  Martin's Lemma 12 supplies the one-step
existence theorem used to instantiate this recursion.
-/

namespace Erdos285

open Filter Finset Real
open scoped BigOperators Topology

noncomputable section

attribute [local instance] Classical.propDecidable

/-! ## The source's initial prime-power-smooth block -/

/--
The initial block in Proposition 6, with lower ratio `alpha`, scale `x`, and
prime-power cutoff `z`.
-/
def initialSmoothBlock (alpha : ℝ) (x : ℕ) (z : ℝ) : Finset ℕ :=
  (Finset.Ioc ⌊alpha * (x : ℝ)⌋₊ x).filter (UnitFractions.is_smooth z)

/--
The large prime-power cutoff used in this formalization.  Martin uses exponent
`22`; exponent `30` leaves enough room for the elementary five-prime reservoir:
the elimination loss becomes `O(x / log(x)^7)`, while that reservoir has size
`≫ x / log(x)^5`.
-/
def proposition6MainCutoff (x : ℕ) : ℝ :=
  (x : ℝ) / Real.log (x : ℝ) ^ 30

/-- The fifth-root scale whose five-prime products lie below `alpha*x`. -/
def proposition6ReservoirScale (alpha : ℝ) (x : ℕ) : ℝ :=
  (alpha * (x : ℝ)) ^ ((5 : ℝ)⁻¹)

lemma proposition6ReservoirScale_pow_five {alpha : ℝ} {x : ℕ}
    (halpha : 0 ≤ alpha) :
    proposition6ReservoirScale alpha x ^ 5 = alpha * (x : ℝ) := by
  exact Real.rpow_inv_natCast_pow
    (mul_nonneg halpha (Nat.cast_nonneg x)) (by norm_num : (5 : ℕ) ≠ 0)

@[simp] lemma mem_initialSmoothBlock {alpha z : ℝ} {x n : ℕ} :
    n ∈ initialSmoothBlock alpha x z ↔
      ⌊alpha * (x : ℝ)⌋₊ < n ∧ n ≤ x ∧ UnitFractions.is_smooth z n := by
  simp [initialSmoothBlock, and_assoc]

lemma initialSmoothBlock_zero_not_mem (alpha z : ℝ) (x : ℕ) :
    0 ∉ initialSmoothBlock alpha x z := by
  intro h
  have := (mem_initialSmoothBlock.mp h).1
  omega

lemma initialSmoothBlock_upper {alpha z : ℝ} {x n : ℕ}
    (hn : n ∈ initialSmoothBlock alpha x z) : n ≤ x :=
  (mem_initialSmoothBlock.mp hn).2.1

lemma initialSmoothBlock_smooth {alpha z : ℝ} {x n : ℕ}
    (hn : n ∈ initialSmoothBlock alpha x z) : UnitFractions.is_smooth z n :=
  (mem_initialSmoothBlock.mp hn).2.2

lemma initialSmoothBlock_lower {alpha z : ℝ} {x n : ℕ}
    (_halpha : 0 ≤ alpha) (hn : n ∈ initialSmoothBlock alpha x z) :
    alpha * (x : ℝ) < n := by
  exact Nat.lt_of_floor_lt (mem_initialSmoothBlock.mp hn).1

/-- The initial recursion state: every initially selected term is marked used. -/
def initialApproximationState (alpha : ℝ) (x : ℕ) (z : ℝ) :
    ApproximationState where
  selected := initialSmoothBlock alpha x z
  used := initialSmoothBlock alpha x z

lemma initialApproximationState_validRun_nil (alpha : ℝ) (x : ℕ) (z : ℝ) :
    ValidApproximationRun (initialApproximationState alpha x z) [] := by
  exact Finset.Subset.rfl

/-! ## A concrete lower reservoir and its separation from the main block -/

/--
The five-prime reservoir API becomes the interval `[alpha*x/2,alpha*x]` when
`y^5 = alpha*x`.
-/
lemma smoothReservoir_in_lower_interval {alpha y : ℝ} {x n : ℕ}
    (hy : 0 < y) (hy5 : y ^ 5 = alpha * (x : ℝ))
    (hn : n ∈ smoothReservoir y) :
    alpha * (x : ℝ) / 2 < (n : ℝ) ∧ (n : ℝ) ≤ alpha * x := by
  constructor
  · rw [← hy5]
    exact smoothReservoir_lower hy hn
  · rw [← hy5]
    exact smoothReservoir_upper hy.le hn

lemma initialSmoothBlock_disjoint_smoothReservoir
    {alpha y z : ℝ} {x : ℕ}
    (halpha : 0 ≤ alpha) (hy : 0 < y)
    (hy5 : y ^ 5 = alpha * (x : ℝ)) :
    Disjoint (initialSmoothBlock alpha x z) (smoothReservoir y) := by
  rw [Finset.disjoint_left]
  intro n hnMain hnReservoir
  have hlower := initialSmoothBlock_lower halpha hnMain
  have hupper := (smoothReservoir_in_lower_interval hy hy5 hnReservoir).2
  linarith

lemma smoothReservoir_smooth_at_cutoff {y z : ℝ} (hyz : y ≤ z) {n : ℕ}
    (hn : n ∈ smoothReservoir y) : UnitFractions.is_smooth z n := by
  intro q hq hqdiv
  exact (smoothReservoir_primePower_bound hn q hq hqdiv).trans hyz

lemma proposition6Reservoir_disjoint_initial
    {alpha z : ℝ} {x : ℕ} (halpha : 0 < alpha) :
    Disjoint (initialSmoothBlock alpha x z)
      (smoothReservoir (proposition6ReservoirScale alpha x)) := by
  by_cases hx : x = 0
  · subst x
    simp [initialSmoothBlock]
  · apply initialSmoothBlock_disjoint_smoothReservoir halpha.le
      (Real.rpow_pos_of_pos (mul_pos halpha (by exact_mod_cast Nat.pos_of_ne_zero hx)) _)
    exact proposition6ReservoirScale_pow_five halpha.le

/-- A reservoir built at any lower ratio `beta ≤ alpha` is disjoint from
the main block beginning above `alpha * x`. -/
lemma proposition6Reservoir_disjoint_initial_of_le
    {alpha beta z : ℝ} {x : ℕ} (hbeta : 0 < beta) (hba : beta ≤ alpha) :
    Disjoint (initialSmoothBlock alpha x z)
      (smoothReservoir (proposition6ReservoirScale beta x)) := by
  by_cases hx : x = 0
  · subst x
    simp [initialSmoothBlock]
  · rw [Finset.disjoint_left]
    intro n hnMain hnReservoir
    have hmainLower := initialSmoothBlock_lower
      (hbeta.le.trans hba) hnMain
    have hypos : 0 < proposition6ReservoirScale beta x :=
      Real.rpow_pos_of_pos
        (mul_pos hbeta (by exact_mod_cast Nat.pos_of_ne_zero hx)) _
    have hreservoirUpper := (smoothReservoir_in_lower_interval hypos
      (proposition6ReservoirScale_pow_five (x := x) hbeta.le) hnReservoir).2
    have hbetaAlpha : beta * (x : ℝ) ≤ alpha * x :=
      mul_le_mul_of_nonneg_right hba (Nat.cast_nonneg x)
    linarith

/-! ## Residual-preserving recursion -/

/--
A recursion state together with the residual rational.  The balance equation is
Martin's invariant `sum(selected) + residual = r`.
-/
structure ResidualApproximationState (r : ℚ) where
  terms : ApproximationState
  residual : ℚ
  balance : UnitFractions.rec_sum terms.selected + residual = r

/-- A residual state whose selected terms have all been marked as used. -/
def ResidualApproximationState.Coherent {r : ℚ}
    (s : ResidualApproximationState r) : Prop :=
  s.terms.selected ⊆ s.terms.used

/-- The residual change opposite to the reciprocal-sum change of a stage. -/
def ApproximationStep.residualDelta (d : ApproximationStep) : ℚ :=
  UnitFractions.rec_sum d.remove - UnitFractions.rec_sum d.add

/-- Apply one valid stage while maintaining the exact rational balance. -/
def ResidualApproximationState.applyStep {r : ℚ}
    (s : ResidualApproximationState r) (d : ApproximationStep)
    (hd : d.Valid s.terms) : ResidualApproximationState r where
  terms := s.terms.applyStep d
  residual := s.residual + d.residualDelta
  balance := by
    change UnitFractions.rec_sum (s.terms.applyStep d).selected +
      (s.residual + (UnitFractions.rec_sum d.remove - UnitFractions.rec_sum d.add)) = r
    linarith [s.balance, hd.rec_sum_balance]

lemma ResidualApproximationState.Coherent.applyStep {r : ℚ}
    {s : ResidualApproximationState r} {d : ApproximationStep}
    (hd : d.Valid s.terms) :
    (s.applyStep d hd).Coherent := by
  exact hd.selected_subset_used_after

@[simp] lemma ResidualApproximationState.applyStep_residual {r : ℚ}
    (s : ResidualApproximationState r) (d : ApproximationStep)
    (hd : d.Valid s.terms) :
    (s.applyStep d hd).residual = s.residual + d.residualDelta := rfl

lemma ResidualApproximationState.applyStep_balance {r : ℚ}
    (s : ResidualApproximationState r) (d : ApproximationStep)
    (hd : d.Valid s.terms) :
    UnitFractions.rec_sum (s.applyStep d hd).terms.selected +
      (s.applyStep d hd).residual = r :=
  (s.applyStep d hd).balance

/-- Package any completed residual state directly as the finite Proposition 6
certificate, using the rational's canonical reduced numerator and denominator.
-/
noncomputable def approximationCertificate_of_residualState
    {r : ℚ} {x R : ℕ} (s : ResidualApproximationState r)
    (hcard : s.terms.selected.card = R)
    (hzero : 0 ∉ s.terms.selected)
    (hinterval : ∀ n ∈ s.terms.selected,
      Real.exp (-(r : ℝ)) * (x : ℝ) / 2 ≤ (n : ℝ) ∧ (n : ℝ) ≤ x)
    (hpos : 0 < s.residual)
    (hlower : (Real.log (x : ℝ))⁻¹ < (s.residual : ℝ))
    (hupper : (s.residual : ℝ) < 1)
    (hsmooth : ∀ q : ℕ, IsPrimePow q → q ∣ s.residual.den → q ^ 5 ≤ x) :
    ApproximationCertificate r x R := by
  have hnumPos : 0 < s.residual.num := Rat.num_pos.mpr hpos
  have hnumAbs : (s.residual.num.natAbs : ℤ) = s.residual.num :=
    Int.natAbs_of_nonneg hnumPos.le
  have hresidualQ :
      (s.residual.num.natAbs : ℚ) / s.residual.den = s.residual := by
    rw [← Int.cast_natCast, hnumAbs, Rat.num_div_den]
  have hresidualR :
      (s.residual.num.natAbs : ℝ) / s.residual.den = (s.residual : ℝ) := by
    have hcast := congrArg (fun u : ℚ ↦ (u : ℝ)) hresidualQ
    norm_num at hcast ⊢
    exact hcast
  refine
    { denominators := s.terms.selected
      numerator := s.residual.num.natAbs
      denominator := s.residual.den
      denominator_pos := s.residual.den_pos
      numerator_pos := Int.natAbs_pos.mpr hnumPos.ne'
      reduced := s.residual.reduced
      card_eq := hcard
      zero_not_mem := hzero
      interval := hinterval
      sum_add_residual := ?_
      residual_lower := ?_
      residual_upper := ?_
      denominator_primePower_bound := hsmooth }
  · rw [hresidualQ]
    exact s.balance
  · rw [hresidualR]
    exact hlower
  · rw [hresidualR]
    exact hupper

/-- Adding a fresh reservoir set, without removing any current term. -/
def reservoirPaddingStep (padding : Finset ℕ) : ApproximationStep where
  remove := ∅
  add := padding

lemma reservoirPaddingStep_valid {r : ℚ} {s : ResidualApproximationState r}
    (hs : s.Coherent) {padding : Finset ℕ} (hfresh : Disjoint padding s.terms.used) :
    (reservoirPaddingStep padding).Valid s.terms := by
  refine ⟨hs, ?_, hfresh⟩
  exact Finset.empty_subset _

lemma reservoirPaddingStep_selected {r : ℚ} {s : ResidualApproximationState r}
    {padding : Finset ℕ} (hfresh : Disjoint padding s.terms.used)
    (hs : s.Coherent) :
    (s.applyStep (reservoirPaddingStep padding)
      (reservoirPaddingStep_valid hs hfresh)).terms.selected =
      s.terms.selected ∪ padding := by
  simp [ResidualApproximationState.applyStep, ApproximationState.applyStep,
    reservoirPaddingStep]

lemma reservoirPaddingStep_residual {r : ℚ} {s : ResidualApproximationState r}
    {padding : Finset ℕ} (hfresh : Disjoint padding s.terms.used)
    (hs : s.Coherent) :
    (s.applyStep (reservoirPaddingStep padding)
      (reservoirPaddingStep_valid hs hfresh)).residual =
      s.residual - UnitFractions.rec_sum padding := by
  simp [ResidualApproximationState.applyStep, ApproximationStep.residualDelta,
    reservoirPaddingStep]
  ring

/--
Concrete smooth-reservoir padding.  This is the exact-cardinality step at the
end of Proposition 6; the residual is updated by subtracting the newly inserted
unit fractions, and the defining reciprocal-sum balance remains exact.
-/
theorem exists_fivePrimeReservoir_padding
    {r : ℚ} {alpha : ℝ} {x R : ℕ} {s : ResidualApproximationState r}
    (halpha : 0 < alpha) (hs : s.Coherent)
    (hcard : s.terms.selected.card ≤ R)
    (hcapacity : R - s.terms.selected.card ≤
      (smoothReservoir (proposition6ReservoirScale alpha x)).card)
    (hfresh : Disjoint s.terms.used
      (smoothReservoir (proposition6ReservoirScale alpha x))) :
    ∃ padding : Finset ℕ,
      padding ⊆ smoothReservoir (proposition6ReservoirScale alpha x) ∧
      Disjoint padding s.terms.used ∧
      ∃ hp : (reservoirPaddingStep padding).Valid s.terms,
        (s.applyStep (reservoirPaddingStep padding) hp).terms.selected.card = R ∧
        (s.applyStep (reservoirPaddingStep padding) hp).Coherent ∧
        (s.applyStep (reservoirPaddingStep padding) hp).residual =
          s.residual - UnitFractions.rec_sum padding ∧
        UnitFractions.rec_sum
            (s.applyStep (reservoirPaddingStep padding) hp).terms.selected +
          (s.applyStep (reservoirPaddingStep padding) hp).residual = r ∧
        (∀ n ∈ padding,
          alpha * (x : ℝ) / 2 < (n : ℝ) ∧
          (n : ℝ) ≤ alpha * x ∧
          UnitFractions.is_smooth (proposition6ReservoirScale alpha x) n) := by
  obtain ⟨padding, hpadding, hpaddingCard⟩ :=
    exists_smoothReservoir_subset_card_eq hcapacity
  have hpadUsed : Disjoint padding s.terms.used :=
    (hfresh.mono_right hpadding).symm
  let hp : (reservoirPaddingStep padding).Valid s.terms :=
    reservoirPaddingStep_valid hs hpadUsed
  refine ⟨padding, hpadding, hpadUsed, hp, ?_, ?_, ?_, ?_, ?_⟩
  · rw [reservoirPaddingStep_selected hpadUsed hs,
      Finset.card_union_of_disjoint
        (hpadUsed.mono_right hs).symm,
      hpaddingCard]
    omega
  · exact ResidualApproximationState.Coherent.applyStep hp
  · exact reservoirPaddingStep_residual hpadUsed hs
  · exact (s.applyStep (reservoirPaddingStep padding) hp).balance
  · intro n hn
    have hnReservoir := hpadding hn
    have hypos : 0 < proposition6ReservoirScale alpha x := by
      have hxpos : 0 < x := by
        by_contra hx
        have hx0 : x = 0 := Nat.eq_zero_of_not_pos hx
        subst x
        have hscale : proposition6ReservoirScale alpha 0 = 0 := by
          simp [proposition6ReservoirScale, Real.zero_rpow (by norm_num : (5 : ℝ)⁻¹ ≠ 0)]
        rw [hscale] at hnReservoir
        obtain ⟨S, hS, hScard, -⟩ := mem_smoothReservoir_source hnReservoir
        have hSne : S.Nonempty := Finset.card_pos.mp (by omega)
        obtain ⟨p, hp⟩ := hSne
        have hpdata := mem_reservoirPrimes (hS hp)
        have hple : p ≤ 0 := by exact_mod_cast hpdata.2.2
        have hppos : 0 < p := hpdata.1.pos
        omega
      exact Real.rpow_pos_of_pos (mul_pos halpha (by exact_mod_cast hxpos)) _
    have hy5 := proposition6ReservoirScale_pow_five (x := x) halpha.le
    refine ⟨(smoothReservoir_in_lower_interval hypos hy5 hnReservoir).1,
      (smoothReservoir_in_lower_interval hypos hy5 hnReservoir).2, ?_⟩
    exact smoothReservoir_primePower_bound hnReservoir

/-! ## Removal steps and availability of lower-tagged terms -/

/-- The descent measure in Martin's recursive extraction. -/
def ResidualApproximationState.primePowerMeasure {r : ℚ}
    (s : ResidualApproximationState r) : ℕ :=
  PrimePowers.largestPrimePowerPart s.residual.den

/-- A source-faithful Lemma 12 step removes a block and adds nothing. -/
def eliminationRemovalStep (U : Finset ℕ) : ApproximationStep where
  remove := U
  add := ∅

lemma eliminationRemovalStep_valid {r : ℚ} {s : ResidualApproximationState r}
    (hs : s.Coherent) {U : Finset ℕ} (hU : U ⊆ s.terms.selected) :
    (eliminationRemovalStep U).Valid s.terms := by
  refine ⟨hs, hU, ?_⟩
  simp [eliminationRemovalStep]

lemma eliminationRemovalStep_selected {r : ℚ} {s : ResidualApproximationState r}
    {U : Finset ℕ} (hs : s.Coherent) (hU : U ⊆ s.terms.selected) :
    (s.applyStep (eliminationRemovalStep U)
      (eliminationRemovalStep_valid hs hU)).terms.selected = s.terms.selected \ U := by
  simp [ResidualApproximationState.applyStep, ApproximationState.applyStep,
    eliminationRemovalStep]

lemma eliminationRemovalStep_residual {r : ℚ} {s : ResidualApproximationState r}
    {U : Finset ℕ} (hs : s.Coherent) (hU : U ⊆ s.terms.selected) :
    (s.applyStep (eliminationRemovalStep U)
      (eliminationRemovalStep_valid hs hU)).residual =
      s.residual + UnitFractions.rec_sum U := by
  simp [ResidualApproximationState.applyStep, ApproximationStep.residualDelta,
    eliminationRemovalStep]

/--
Availability invariant for descending tag elimination.  Every member of the
original block whose exact prime-power tag is no larger than the current
residual measure is still selected.
-/
def AvailableBelow (base : Finset ℕ) {r : ℚ}
    (s : ResidualApproximationState r) : Prop :=
  ∀ n ∈ base,
    PrimePowers.largestPrimePowerPart n ≤ s.primePowerMeasure →
      n ∈ s.terms.selected

/--
Removing a block tagged by the current measure preserves all terms whose tags
are at most the strictly smaller new measure.
-/
lemma AvailableBelow.eliminationRemovalStep
    {base : Finset ℕ} {r : ℚ} {s : ResidualApproximationState r}
    (havail : AvailableBelow base s) (hs : s.Coherent)
    {U : Finset ℕ} (hU : U ⊆ s.terms.selected)
    (htag : ∀ n ∈ U,
      PrimePowers.largestPrimePowerPart n = s.primePowerMeasure)
    (hdesc :
      (s.applyStep (eliminationRemovalStep U)
        (eliminationRemovalStep_valid hs hU)).primePowerMeasure <
          s.primePowerMeasure) :
    AvailableBelow base
      (s.applyStep (eliminationRemovalStep U)
        (eliminationRemovalStep_valid hs hU)) := by
  intro n hnbase hntag
  have hnold : n ∈ s.terms.selected :=
    havail n hnbase (hntag.trans hdesc.le)
  rw [eliminationRemovalStep_selected hs hU, Finset.mem_sdiff]
  refine ⟨hnold, ?_⟩
  intro hnU
  have := htag n hnU
  omega

/-- A largest-exact-prime-power bound implies `UnitFractions.is_smooth`. -/
lemma isSmooth_of_largestPrimePowerPart_le
    {z : ℝ} {n : ℕ} (hn : n ≠ 0)
    (hmax : (PrimePowers.largestPrimePowerPart n : ℝ) ≤ z) :
    UnitFractions.is_smooth z n := by
  intro q hqpp hqdiv
  have hqexact : ∃ exactPart : ℕ,
      exactPart ∈ PrimePowers.primePowerParts n ∧ q ∣ exactPart := by
    rcases (isPrimePow_nat_iff q).1 hqpp with ⟨p, k, hp, hk, rfl⟩
    let exactPart := p ^ n.factorization p
    have hkle : k ≤ n.factorization p :=
      (hp.pow_dvd_iff_le_factorization hn).1 hqdiv
    have hfac : n.factorization p ≠ 0 :=
      Nat.ne_zero_of_lt (hk.trans_le hkle)
    refine ⟨exactPart, (PrimePowers.mem_primePowerParts hn).2 ?_, ?_⟩
    · refine ⟨hp.isPrimePow.pow hfac, ?_, ?_⟩
      · dsimp [exactPart]
        simpa using Nat.ordProj_dvd n p
      · dsimp [exactPart]
        exact ((UnitFractions.factorization_eq_iff (n := n) hp hfac).2 rfl).2
    · dsimp [exactPart]
      exact pow_dvd_pow p hkle
  obtain ⟨exactPart, hpart, hqpart⟩ := hqexact
  have hpartpos : 0 < exactPart :=
    ((PrimePowers.mem_primePowerParts hn).1 hpart).1.pos
  have hqle : (q : ℝ) ≤ exactPart := by
    exact_mod_cast Nat.le_of_dvd hpartpos hqpart
  have hpartmax : (exactPart : ℝ) ≤
      PrimePowers.largestPrimePowerPart n := by
    exact_mod_cast PrimePowers.le_largestPrimePowerPart hpart
  exact hqle.trans (hpartmax.trans hmax)

/-- Smooth displayed denominators give a smooth reduced denominator for their
finite reciprocal sum. -/
lemma recSum_den_isSmooth {y : ℝ} {A : Finset ℕ}
    (hzero : ∀ n ∈ A, n ≠ 0)
    (hsmooth : ∀ n ∈ A, UnitFractions.is_smooth y n) :
    UnitFractions.is_smooth y (UnitFractions.rec_sum A).den := by
  intro q hq hqden
  have hqlcm : q ∣ A.lcm id :=
    hqden.trans (PrimePowers.recSum_den_dvd_lcm A)
  obtain ⟨n, hn, hqn⟩ :=
    Lemma12.isPrimePow_dvd_finsetLcm hq hzero hqlcm
  exact hsmooth n hn q hq hqn

/-- Smoothness bounds the largest exact prime-power part by the natural floor
of the smoothness parameter. -/
lemma largestPrimePowerPart_le_floor_of_isSmooth
    {y : ℝ} {n : ℕ} (hsmooth : UnitFractions.is_smooth y n) :
    PrimePowers.largestPrimePowerPart n ≤ ⌊y⌋₊ := by
  by_cases hn : 2 ≤ n
  · have hmem := PrimePowers.largestPrimePowerPart_mem hn
    have hspec := (PrimePowers.mem_primePowerParts (by omega : n ≠ 0)).mp hmem
    exact Nat.le_floor (hsmooth _ hspec.1 hspec.2.1)
  · have hempty : PrimePowers.primePowerParts n = ∅ :=
      PrimePowers.primePowerParts_empty_iff.mpr (Nat.lt_of_not_ge hn)
    simp [PrimePowers.largestPrimePowerPart, hempty]

/-- Subtracting a reciprocal sum whose displayed denominators are smooth
preserves smoothness of a smooth rational denominator. -/
lemma sub_recSum_den_isSmooth {y : ℝ} (rho : ℚ) {A : Finset ℕ}
    (hrho : UnitFractions.is_smooth y rho.den)
    (hzero : ∀ n ∈ A, n ≠ 0)
    (hA : ∀ n ∈ A, UnitFractions.is_smooth y n) :
    UnitFractions.is_smooth y (rho - UnitFractions.rec_sum A).den := by
  have hsum := recSum_den_isSmooth hzero hA
  intro q hq hqden
  have hqLcm : q ∣ Nat.lcm rho.den (UnitFractions.rec_sum A).den :=
    hqden.trans (Rat.sub_den_dvd_lcm rho (UnitFractions.rec_sum A))
  rcases Lemma12.isPrimePow_dvd_lcm hq rho.den_ne_zero
      (UnitFractions.rec_sum A).den_ne_zero hqLcm with hqrho | hqsum
  · exact hrho q hq hqrho
  · exact hsum q hq hqsum

/-- Adding a reciprocal sum whose displayed denominators are smooth preserves
smoothness of a smooth rational denominator. -/
lemma add_recSum_den_isSmooth {y : ℝ} (rho : ℚ) {A : Finset ℕ}
    (hrho : UnitFractions.is_smooth y rho.den)
    (hzero : ∀ n ∈ A, n ≠ 0)
    (hA : ∀ n ∈ A, UnitFractions.is_smooth y n) :
    UnitFractions.is_smooth y (rho + UnitFractions.rec_sum A).den := by
  have hsum := recSum_den_isSmooth hzero hA
  intro q hq hqden
  have hqLcm : q ∣ Nat.lcm rho.den (UnitFractions.rec_sum A).den :=
    hqden.trans (Rat.add_den_dvd_lcm rho (UnitFractions.rec_sum A))
  rcases Lemma12.isPrimePow_dvd_lcm hq rho.den_ne_zero
      (UnitFractions.rec_sum A).den_ne_zero hqLcm with hqrho | hqsum
  · exact hrho q hq hqrho
  · exact hsum q hq hqsum

/-- Smoothness at the real fifth-root scale is exactly the integral
prime-power bound stored in an approximation certificate. -/
lemma primePower_pow_five_le_of_den_isSmooth
    {x d : ℕ}
    (hsmooth : UnitFractions.is_smooth
      ((x : ℝ) ^ ((5 : ℝ)⁻¹)) d) :
    ∀ q : ℕ, IsPrimePow q → q ∣ d → q ^ 5 ≤ x := by
  intro q hq hqd
  have hqle : (q : ℝ) ≤ (x : ℝ) ^ ((5 : ℝ)⁻¹) :=
    hsmooth q hq hqd
  have hpow : (q : ℝ) ^ 5 ≤
      ((x : ℝ) ^ ((5 : ℝ)⁻¹)) ^ 5 :=
    pow_le_pow_left₀ (Nat.cast_nonneg q) hqle 5
  have hroot : ((x : ℝ) ^ ((5 : ℝ)⁻¹)) ^ 5 = x := by
    convert Real.rpow_inv_natCast_pow (Nat.cast_nonneg x)
      (by norm_num : (5 : ℕ) ≠ 0) using 1
    all_goals norm_num
  rw [hroot] at hpow
  exact_mod_cast hpow

/-!
## Instantiating one recursion stage with the concrete Lemma 12

The sign change is the correction to the printed Proposition 6 recursion:
Lemma 12 is applied to the negative residual.  Removing `U` from the selected
set changes the residual from `ρ` to `ρ + rec_sum U`, the negative of
`-ρ - rec_sum U` appearing in Lemma 12.
-/

theorem lemma12_eliminationRemovalStep
    {r : ℚ} {alpha xi z : ℝ} {x : ℕ}
    {s : ResidualApproximationState r} {M : Finset ℕ}
    (hs : s.Coherent)
    (havail : AvailableBelow (initialSmoothBlock alpha x z) s)
    (hdata : Lemma12.CandidateData xi x s.primePowerMeasure (-s.residual) M)
    (hsurj : Lemma12.BoundedInverseSubsetSurjective s.primePowerMeasure
      (Lemma12.martinBlockBound x s.primePowerMeasure) M)
    (hxi : (⌊alpha * (x : ℝ)⌋₊ : ℝ) < xi * x)
    (hqz : (s.primePowerMeasure : ℝ) ≤ z) :
    ∃ U : Finset ℕ,
      U.card ≤ Lemma12.martinBlockBound x s.primePowerMeasure ∧
      U ⊆ initialSmoothBlock alpha x z ∧
      ∃ hp : (eliminationRemovalStep U).Valid s.terms,
        (s.applyStep (eliminationRemovalStep U) hp).primePowerMeasure <
          s.primePowerMeasure ∧
        AvailableBelow (initialSmoothBlock alpha x z)
          (s.applyStep (eliminationRemovalStep U) hp) := by
  obtain ⟨U, hUcard, hUint, hUtag, -, hdescNeg⟩ :=
    Lemma12.largePrimePowerElimination hdata hsurj
  have hqspec :=
    (PrimePowers.mem_primePowerParts (-s.residual).den_ne_zero).mp hdata.q_part
  have hqpos : 0 < s.primePowerMeasure := hqspec.1.pos
  have hUbase : U ⊆ initialSmoothBlock alpha x z := by
    intro u hu
    apply mem_initialSmoothBlock.mpr
    have huLowerR : (⌊alpha * (x : ℝ)⌋₊ : ℝ) < u :=
      hxi.trans_le (hUint u hu).1
    have huLower : ⌊alpha * (x : ℝ)⌋₊ < u := by exact_mod_cast huLowerR
    have huUpper : u ≤ x := by exact_mod_cast (hUint u hu).2
    have hu0 : u ≠ 0 := by omega
    have huSmooth : UnitFractions.is_smooth z u := by
      apply isSmooth_of_largestPrimePowerPart_le hu0
      rw [hUtag u hu]
      exact hqz
    exact ⟨huLower, huUpper, huSmooth⟩
  have hUselected : U ⊆ s.terms.selected := by
    intro u hu
    exact havail u (hUbase hu) (by rw [hUtag u hu])
  let hp : (eliminationRemovalStep U).Valid s.terms :=
    eliminationRemovalStep_valid hs hUselected
  have hresidual :
      (s.applyStep (eliminationRemovalStep U) hp).residual =
        s.residual + UnitFractions.rec_sum U := by
    exact eliminationRemovalStep_residual hs hUselected
  have hdenEq :
      ((-s.residual) - UnitFractions.rec_sum U).den =
        (s.residual + UnitFractions.rec_sum U).den := by
    have heq : (-s.residual) - UnitFractions.rec_sum U =
        -(s.residual + UnitFractions.rec_sum U) := by ring
    rw [heq, Rat.den_neg_eq_den]
  have hdesc :
      (s.applyStep (eliminationRemovalStep U) hp).primePowerMeasure <
        s.primePowerMeasure := by
    rw [ResidualApproximationState.primePowerMeasure, hresidual, ← hdenEq]
    exact hdescNeg
  refine ⟨U, hUcard, hUbase, hp, hdesc, ?_⟩
  exact havail.eliminationRemovalStep hs hUselected hUtag hdesc

/-- Sum of the worst-case Lemma 12 block bounds for all tags up to `Q`. -/
def totalEliminationBudget (x Q : ℕ) : ℕ :=
  ∑ q ∈ Finset.range (Q + 1), Lemma12.martinBlockBound x q

lemma totalEliminationBudget_mono (x : ℕ) : Monotone (totalEliminationBudget x) := by
  intro a b hab
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · exact Finset.range_mono (Nat.succ_le_succ hab)
  · simp

lemma largestPrimePowerPart_mem_of_pos {n : ℕ}
    (hpos : 0 < PrimePowers.largestPrimePowerPart n) :
    PrimePowers.largestPrimePowerPart n ∈ PrimePowers.primePowerParts n := by
  apply PrimePowers.largestPrimePowerPart_mem
  by_contra hn
  have hempty : PrimePowers.primePowerParts n = ∅ :=
    PrimePowers.primePowerParts_empty_iff.mpr (Nat.lt_of_not_ge hn)
  rw [PrimePowers.largestPrimePowerPart, hempty] at hpos
  simp at hpos

/-- Every prime power in the cofactor left after removing the largest exact
prime-power part is strictly smaller than that part. -/
lemma primePower_dvd_cofactor_lt_largest
    {t : ℚ} {q ℓ : ℕ}
    (hqpart : q ∈ PrimePowers.primePowerParts t.den)
    (hmax : PrimePowers.largestPrimePowerPart t.den = q)
    (hℓpp : IsPrimePow ℓ) (hℓdiv : ℓ ∣ t.den / q) : ℓ < q := by
  have hqspec := (PrimePowers.mem_primePowerParts t.den_ne_zero).mp hqpart
  have hℓden : ℓ ∣ t.den :=
    hℓdiv.trans (Nat.div_dvd_of_dvd hqspec.2.1)
  have hsmooth : UnitFractions.is_smooth (q : ℝ) t.den := by
    apply isSmooth_of_largestPrimePowerPart_le t.den_ne_zero
    rw [hmax]
  have hℓle : ℓ ≤ q := by
    exact_mod_cast hsmooth ℓ hℓpp hℓden
  have hℓne : ℓ ≠ q := by
    intro heq
    subst ℓ
    have hqone := Nat.eq_one_of_dvd_coprimes hqspec.2.2 dvd_rfl hℓdiv
    exact hqspec.1.ne_one hqone
  exact lt_of_le_of_ne hℓle hℓne

/-- The precise finite input which the four-prime construction and the
modular subset-sum theorem supply at one residual state. -/
def Lemma12StepData {r : ℚ} (xi : ℝ) (x : ℕ)
    (s : ResidualApproximationState r) : Prop :=
  ∃ M : Finset ℕ,
    Lemma12.CandidateData xi x s.primePowerMeasure (-s.residual) M ∧
      Lemma12.BoundedInverseSubsetSurjective s.primePowerMeasure
        (Lemma12.martinBlockBound x s.primePowerMeasure) M

/-- Assemble the exact Lemma 12 input from an explicit subfamily of the
four-prime candidates.  All structural, interval, largest-part, and auxiliary
LCM fields are discharged here; only the separately proved subset-sum
surjectivity remains as an argument. -/
theorem lemma12StepData_of_rawCandidateFamily
    {r : ℚ} {xi : ℝ} {x p ν : ℕ}
    {s : ResidualApproximationState r} {M : Finset ℕ}
    (hxi : 0 < xi) (hxi1 : xi < 1) (hx : 0 < x)
    (hp : p.Prime) (hν : 0 < ν)
    (hqeq : s.primePowerMeasure = p ^ ν)
    (hrange : Lemma12.InEliminationRange x s.primePowerMeasure)
    (hM : M ⊆ Lemma12Candidates.rawCandidates p
      (Lemma12Candidates.fourthRoot xi)
      (Lemma12Candidates.fourthRoot ((x : ℝ) / (p ^ ν : ℕ))))
    (hsurj : Lemma12.BoundedInverseSubsetSurjective s.primePowerMeasure
      (Lemma12.martinBlockBound x s.primePowerMeasure) M) :
    Lemma12StepData xi x s := by
  have hqpos : 0 < s.primePowerMeasure := by
    rw [hqeq]
    exact pow_pos hp.pos ν
  have hqpartResidual : s.primePowerMeasure ∈
      PrimePowers.primePowerParts s.residual.den :=
    largestPrimePowerPart_mem_of_pos hqpos
  have hqpart : p ^ ν ∈ PrimePowers.primePowerParts (-s.residual).den := by
    rw [Rat.den_neg_eq_den, ← hqeq]
    exact hqpartResidual
  have hcofactor : ∀ ℓ : ℕ, IsPrimePow ℓ →
      ℓ ∣ (-s.residual).den / (p ^ ν) → ℓ < p ^ ν := by
    intro ℓ hℓpp hℓdiv
    apply primePower_dvd_cofactor_lt_largest hqpart
    · simpa [ResidualApproximationState.primePowerMeasure,
        Rat.den_neg_eq_den] using hqeq
    · exact hℓpp
    · exact hℓdiv
  unfold Lemma12StepData
  rw [hqeq]
  refine ⟨M, ?_, ?_⟩
  · apply Lemma12.candidateData_of_rawCandidateFamily
      hxi hxi1 hx hp hν
    · simpa [hqeq] using hrange
    · exact hqpart
    · exact hM
    · exact hcofactor
  · simpa [hqeq] using hsurj

/-- The strong `log⁻³⁰` range used by the uniform candidate construction is
contained in Martin's `log⁻²²` elimination range once `log x ≥ 1`. -/
lemma inEliminationRange_of_strongRange
    {x q : ℕ} (hlog : 1 ≤ Real.log (x : ℝ))
    (hrange : Lemma12Numerics.InStrongEliminationRange x q) :
    Lemma12.InEliminationRange x q := by
  refine ⟨hrange.1, hrange.2.trans ?_⟩
  apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg x)
  exact Real.rpow_le_rpow_of_exponent_le hlog (by norm_num)

/-- Uniform, unconditional Lemma 12 input at every residual state in the
strong elimination range.  The four-prime family, its exact cardinality, and
the bounded inverse-subset surjectivity are all supplied by
`Lemma12Numerics`; no state-local number-theoretic theorem remains as a
parameter. -/
theorem eventually_lemma12StepData_threeFourths :
    ∀ᶠ x : ℕ in atTop, ∀ {r : ℚ} (s : ResidualApproximationState r),
      Lemma12Numerics.InStrongEliminationRange x s.primePowerMeasure →
      Lemma12StepData ((3 : ℝ) / 4) x s := by
  have hfamilies :=
    Lemma12Numerics.eventually_exists_martin_candidate_family
      (show (0 : ℝ) < 3 / 4 by norm_num)
      (show (3 : ℝ) / 4 < 1 by norm_num)
  have hlogTop : Tendsto (fun x : ℕ ↦ Real.log (x : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards [hfamilies, hlogTop.eventually_ge_atTop 1]
      with x hfamily hlog
  intro r s hrange
  have hx : 0 < x := by
    have hlogpos : 0 < Real.log (x : ℝ) := zero_lt_one.trans_le hlog
    have hxone : 1 < (x : ℝ) :=
      (Real.log_pos_iff (Nat.cast_nonneg x)).mp hlogpos
    exact_mod_cast (zero_lt_one.trans hxone)
  have hqpos : 0 < s.primePowerMeasure := by
    have hrootpos : 0 < (x : ℝ) ^ ((1 : ℝ) / 5) :=
      Real.rpow_pos_of_pos (by exact_mod_cast hx) _
    have hqreal : (0 : ℝ) < s.primePowerMeasure :=
      hrootpos.trans_le hrange.1
    exact_mod_cast hqreal
  have hqpart : s.primePowerMeasure ∈
      PrimePowers.primePowerParts s.residual.den :=
    largestPrimePowerPart_mem_of_pos hqpos
  have hqpp : IsPrimePow s.primePowerMeasure :=
    ((PrimePowers.mem_primePowerParts s.residual.den_ne_zero).mp hqpart).1
  rcases (isPrimePow_nat_iff s.primePowerMeasure).1 hqpp with
    ⟨p, ν, hp, hν, hqeq⟩
  obtain ⟨M, -, hM, -, -, -, -, -, hsurj⟩ :=
    hfamily p ν hp hν (by simpa [hqeq] using hrange)
  have hsurj' : Lemma12.BoundedInverseSubsetSurjective s.primePowerMeasure
      (Lemma12.martinBlockBound x s.primePowerMeasure) M := by
    rw [← hqeq]
    exact hsurj
  apply lemma12StepData_of_rawCandidateFamily
      (s := s) (M := M) (p := p) (ν := ν)
  · norm_num
  · norm_num
  · exact hx
  · exact hp
  · exact hν
  · exact hqeq.symm
  · exact inEliminationRange_of_strongRange hlog hrange
  · simpa [hqeq] using hM
  · exact hsurj'

/-- Moving-endpoint version of the preceding theorem.  The numerical module is
uniform for every `0 < xi ≤ 9/10`, which is the form needed by the final
last-crossing construction. -/
theorem eventually_lemma12StepData_uniform :
    ∀ᶠ x : ℕ in atTop, ∀ (xi : ℝ), 0 < xi → xi ≤ (9 : ℝ) / 10 →
      ∀ {r : ℚ} (s : ResidualApproximationState r),
        Lemma12Numerics.InStrongEliminationRange x s.primePowerMeasure →
        Lemma12StepData xi x s := by
  filter_upwards
      [Lemma12Numerics.eventually_exists_candidateData_and_surjective_uniform,
        eventually_ge_atTop 1]
      with x hfamily hx
  intro xi hxi hxiUpper r s hrange
  have hqpos : 0 < s.primePowerMeasure := by
    have hxpos : (0 : ℝ) < x := by exact_mod_cast (Nat.zero_lt_of_lt hx)
    have hrootpos : 0 < (x : ℝ) ^ ((1 : ℝ) / 5) :=
      Real.rpow_pos_of_pos hxpos _
    have hqreal : (0 : ℝ) < s.primePowerMeasure :=
      hrootpos.trans_le hrange.1
    exact_mod_cast hqreal
  have hqpartResidual : s.primePowerMeasure ∈
      PrimePowers.primePowerParts s.residual.den :=
    largestPrimePowerPart_mem_of_pos hqpos
  have hqpart : s.primePowerMeasure ∈
      PrimePowers.primePowerParts (-s.residual).den := by
    simpa using hqpartResidual
  have hqspec :=
    (PrimePowers.mem_primePowerParts (-s.residual).den_ne_zero).mp hqpart
  have hcofactor : ∀ ℓ : ℕ, IsPrimePow ℓ →
      ℓ ∣ (-s.residual).den / s.primePowerMeasure →
      ℓ < s.primePowerMeasure := by
    intro ℓ hℓpp hℓdiv
    apply primePower_dvd_cofactor_lt_largest hqpart
    · simp [ResidualApproximationState.primePowerMeasure]
    · exact hℓpp
    · exact hℓdiv
  obtain ⟨M, hdata, hsurj⟩ := hfamily xi hxi hxiUpper
    s.primePowerMeasure (-s.residual) hqspec.1 hrange hqpart hcofactor
  exact ⟨M, hdata, hsurj⟩

/--
The complete output of the descending removal recursion, including the union of
all removed blocks and the explicit sum of their individual Lemma 12 bounds.
-/
structure RemovalDescentOutcome
    (base : Finset ℕ) (x y : ℕ) {r : ℚ}
    (start : ResidualApproximationState r) where
  final : ResidualApproximationState r
  removed : Finset ℕ
  coherent : final.Coherent
  available : AvailableBelow base final
  measure_le : final.primePowerMeasure ≤ y
  removed_subset_base : removed ⊆ base
  removed_subset_selected : removed ⊆ start.terms.selected
  selected_eq : final.terms.selected = start.terms.selected \ removed
  used_eq : final.terms.used = start.terms.used
  residual_eq : final.residual = start.residual + UnitFractions.rec_sum removed
  card_le : removed.card ≤ totalEliminationBudget x start.primePowerMeasure

lemma RemovalDescentOutcome.final_card_eq
    {base : Finset ℕ} {x y : ℕ} {r : ℚ}
    {start : ResidualApproximationState r}
    (out : RemovalDescentOutcome base x y start) :
    out.final.terms.selected.card =
      start.terms.selected.card - out.removed.card := by
  rw [out.selected_eq, Finset.card_sdiff_of_subset out.removed_subset_selected]

/-- A removal-only step leaves the ever-used set unchanged. -/
lemma eliminationRemovalStep_used {r : ℚ} {s : ResidualApproximationState r}
    {U : Finset ℕ} (hs : s.Coherent) (hU : U ⊆ s.terms.selected) :
    (s.applyStep (eliminationRemovalStep U)
      (eliminationRemovalStep_valid hs hU)).terms.used = s.terms.used := by
  simp [ResidualApproximationState.applyStep, ApproximationState.applyStep,
    eliminationRemovalStep]

/--
Well-founded descending recursion with exact removal-set bookkeeping.  The
one-step premise is precisely what `lemma12_eliminationRemovalStep` proves from
concrete candidate data and bounded inverse-subset surjectivity.
-/
noncomputable def exists_removalDescentOutcome
    (base : Finset ℕ) (x y measureBound : ℕ) {r : ℚ}
    (start : ResidualApproximationState r) (hcoh : start.Coherent)
    (havail : AvailableBelow base start)
    (hbound : start.primePowerMeasure ≤ measureBound)
    (hstep : ∀ s : ResidualApproximationState r, s.Coherent →
      AvailableBelow base s → s.primePowerMeasure ≤ measureBound →
      y < s.primePowerMeasure →
      ∃ U : Finset ℕ,
        U.card ≤ Lemma12.martinBlockBound x s.primePowerMeasure ∧
        U ⊆ base ∧
        ∃ hp : (eliminationRemovalStep U).Valid s.terms,
          (s.applyStep (eliminationRemovalStep U) hp).primePowerMeasure <
            s.primePowerMeasure ∧
          AvailableBelow base (s.applyStep (eliminationRemovalStep U) hp)) :
    RemovalDescentOutcome base x y start := by
  induction hmeasure : start.primePowerMeasure using Nat.strongRecOn generalizing start with
  | ind q ih =>
      by_cases hdone : start.primePowerMeasure ≤ y
      · exact
          { final := start
            removed := ∅
            coherent := hcoh
            available := havail
            measure_le := hdone
            removed_subset_base := by simp
            removed_subset_selected := by simp
            selected_eq := by simp
            used_eq := rfl
            residual_eq := by simp
            card_le := by simp }
      · have habove : y < start.primePowerMeasure := Nat.lt_of_not_ge hdone
        let hstage := hstep start hcoh havail hbound habove
        let U : Finset ℕ := Classical.choose hstage
        have hUfacts := Classical.choose_spec hstage
        have hUcard : U.card ≤
            Lemma12.martinBlockBound x start.primePowerMeasure := hUfacts.1
        have hUbase : U ⊆ base := hUfacts.2.1
        let hp : (eliminationRemovalStep U).Valid start.terms :=
          Classical.choose hUfacts.2.2
        have hpFacts := Classical.choose_spec hUfacts.2.2
        have hdesc :
            (start.applyStep (eliminationRemovalStep U) hp).primePowerMeasure <
              start.primePowerMeasure := hpFacts.1
        have hnextAvail : AvailableBelow base
            (start.applyStep (eliminationRemovalStep U) hp) := hpFacts.2
        have hUselected : U ⊆ start.terms.selected := hp.2.1
        let next := start.applyStep (eliminationRemovalStep U) hp
        have hnextCoh : next.Coherent :=
          ResidualApproximationState.Coherent.applyStep hp
        have hnextSelected : next.terms.selected = start.terms.selected \ U := by
          simp [next, ResidualApproximationState.applyStep,
            ApproximationState.applyStep, eliminationRemovalStep]
        have hnextMeasure : next.primePowerMeasure < q := by
          rw [← hmeasure]
          exact hdesc
        have hnextBound : next.primePowerMeasure ≤ measureBound :=
          hdesc.le.trans hbound
        have tail :=
          ih next.primePowerMeasure hnextMeasure next hnextCoh hnextAvail hnextBound rfl
        let removed := U ∪ tail.removed
        have hdisjoint : Disjoint U tail.removed := by
          rw [Finset.disjoint_left]
          intro n hnU hnTail
          have hnNext : n ∈ next.terms.selected := tail.removed_subset_selected hnTail
          have hnDiff : n ∈ start.terms.selected \ U := by
            rwa [hnextSelected] at hnNext
          exact (Finset.mem_sdiff.mp hnDiff).2 hnU
        refine
          { final := tail.final
            removed := removed
            coherent := tail.coherent
            available := tail.available
            measure_le := tail.measure_le
            removed_subset_base := ?_
            removed_subset_selected := ?_
            selected_eq := ?_
            used_eq := ?_
            residual_eq := ?_
            card_le := ?_ }
        · intro n hn
          rcases Finset.mem_union.mp hn with hnU | hnTail
          · exact hUbase hnU
          · exact tail.removed_subset_base hnTail
        · intro n hn
          rcases Finset.mem_union.mp hn with hnU | hnTail
          · exact hUselected hnU
          · have hnNext := tail.removed_subset_selected hnTail
            have hnDiff : n ∈ start.terms.selected \ U := by
              rwa [hnextSelected] at hnNext
            exact (Finset.mem_sdiff.mp hnDiff).1
        · rw [tail.selected_eq]
          ext n
          simp only [hnextSelected, Finset.mem_sdiff]
          simp [removed]
          tauto
        · rw [tail.used_eq]
          exact eliminationRemovalStep_used hcoh hUselected
        · rw [tail.residual_eq]
          have hnextResidual : next.residual =
              start.residual + UnitFractions.rec_sum U := by
            simpa [next] using eliminationRemovalStep_residual hcoh hUselected
          rw [hnextResidual, UnitFractions.rec_sum_disjoint hdisjoint]
          ring
        · rw [Finset.card_union_of_disjoint hdisjoint]
          have htailBudget :
              totalEliminationBudget x next.primePowerMeasure ≤
                ∑ i ∈ Finset.range start.primePowerMeasure,
                  Lemma12.martinBlockBound x i := by
            apply Finset.sum_le_sum_of_subset_of_nonneg
            · exact Finset.range_mono hdesc
            · simp
          calc
            U.card + tail.removed.card ≤
                Lemma12.martinBlockBound x start.primePowerMeasure +
                  totalEliminationBudget x next.primePowerMeasure :=
              Nat.add_le_add hUcard tail.card_le
            _ ≤ Lemma12.martinBlockBound x start.primePowerMeasure +
                ∑ i ∈ Finset.range start.primePowerMeasure,
                  Lemma12.martinBlockBound x i := Nat.add_le_add_left htailBudget _
            _ = totalEliminationBudget x start.primePowerMeasure := by
              rw [totalEliminationBudget, Finset.sum_range_succ]
              omega

/--
Run the removal recursion using the actual finite conclusion of Martin's
Lemma 12, rather than an abstract one-step eliminator.  The only input left in
this theorem is `Lemma12StepData`, the exact interface proved by the explicit
four-prime candidate and subset-sum construction.
-/
noncomputable def lemma12RemovalDescent
    (alpha xi z : ℝ) (base : Finset ℕ) (x y measureBound : ℕ)
    {r : ℚ} (start : ResidualApproximationState r)
    (hbase : base = initialSmoothBlock alpha x z)
    (hcoh : start.Coherent) (havail : AvailableBelow base start)
    (hbound : start.primePowerMeasure ≤ measureBound)
    (hboundZ : (measureBound : ℝ) ≤ z)
    (hxi : (⌊alpha * (x : ℝ)⌋₊ : ℝ) < xi * x)
    (hdata : ∀ s : ResidualApproximationState r, s.Coherent →
      AvailableBelow base s → s.primePowerMeasure ≤ measureBound →
      y < s.primePowerMeasure → Lemma12StepData xi x s) :
    RemovalDescentOutcome base x y start :=
  exists_removalDescentOutcome base x y measureBound start hcoh havail hbound
    (fun s hs ha hsBound hy ↦ by
      have hqz : (s.primePowerMeasure : ℝ) ≤ z := by
        have hcast : (s.primePowerMeasure : ℝ) ≤ measureBound := by
          exact_mod_cast hsBound
        exact hcast.trans hboundZ
      obtain ⟨M, hMdata, hMsurj⟩ := hdata s hs ha hsBound hy
      subst base
      exact lemma12_eliminationRemovalStep hs ha hMdata hMsurj hxi hqz)

/-! ## Exact padding and certificate assembly -/

/-- The rational residual left by the explicit initial smooth block. -/
def initialResidual (r : ℚ) (alpha : ℝ) (x : ℕ) (z : ℝ) : ℚ :=
  r - UnitFractions.rec_sum (initialSmoothBlock alpha x z)

/-- Initial block and initial residual bundled with their exact balance. -/
def initialResidualApproximationState
    (r : ℚ) (alpha : ℝ) (x : ℕ) (z : ℝ) :
    ResidualApproximationState r where
  terms := initialApproximationState alpha x z
  residual := initialResidual r alpha x z
  balance := by
    simp [initialResidual, initialApproximationState]

/-- The initial residual inherits the smoothness bound of both the target
rational and every denominator in the initial block. -/
lemma initialResidual_den_isSmooth
    {r : ℚ} {alpha z : ℝ} {x : ℕ}
    (hr : UnitFractions.is_smooth z r.den) :
    UnitFractions.is_smooth z (initialResidual r alpha x z).den := by
  rw [initialResidual]
  apply sub_recSum_den_isSmooth r hr
  · intro n hn hn0
    subst n
    exact initialSmoothBlock_zero_not_mem alpha z x hn
  · intro n hn
    exact initialSmoothBlock_smooth hn

/-- Consequently the starting descent measure is at most the natural smooth
cutoff. -/
lemma initialResidualApproximationState_measure_le_floor
    {r : ℚ} {alpha z : ℝ} {x : ℕ} (hr : UnitFractions.is_smooth z r.den) :
    (initialResidualApproximationState r alpha x z).primePowerMeasure ≤ ⌊z⌋₊ := by
  apply largestPrimePowerPart_le_floor_of_isSmooth
  exact initialResidual_den_isSmooth hr

/-- Specialization of the starting-measure bound to the target rational `1`. -/
lemma initialResidualApproximationState_one_measure_le_floor
    {alpha z : ℝ} {x : ℕ} :
    (initialResidualApproximationState (1 : ℚ) alpha x z).primePowerMeasure ≤
      ⌊z⌋₊ := by
  apply initialResidualApproximationState_measure_le_floor
  intro q hq hqdiv
  have hqone : q = 1 := Nat.dvd_one.mp (by simpa using hqdiv)
  exact (hq.ne_one hqone).elim

/-- The complete Lemma 12 recursion for the target rational `1`, uniform in
every moving lower endpoint below `3/4`.  All candidate and subset-sum inputs
come from the proved eventual theorem above. -/
theorem eventually_concreteRemovalDescent_one :
    ∀ᶠ x : ℕ in atTop, ∀ (alpha : ℝ), 0 ≤ alpha → alpha < (3 : ℝ) / 4 →
      Nonempty (RemovalDescentOutcome
        (initialSmoothBlock alpha x (proposition6MainCutoff x)) x
        (approximationCorrectionScale x)
        (initialResidualApproximationState (1 : ℚ) alpha x
          (proposition6MainCutoff x))) := by
  have hlogTop : Tendsto (fun x : ℕ ↦ Real.log (x : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards [eventually_lemma12StepData_threeFourths,
    eventually_ge_atTop 1, hlogTop.eventually_ge_atTop 1]
      with x hstepData hx hlog
  intro alpha halpha halphaXi
  let z := proposition6MainCutoff x
  let y := approximationCorrectionScale x
  let Q := ⌊z⌋₊
  let start := initialResidualApproximationState (1 : ℚ) alpha x z
  have hz : 0 ≤ z := by
    dsimp [z, proposition6MainCutoff]
    positivity
  have hbound : start.primePowerMeasure ≤ Q := by
    exact initialResidualApproximationState_one_measure_le_floor
  have hQz : (Q : ℝ) ≤ z := by
    exact Nat.floor_le hz
  have hxi : (⌊alpha * (x : ℝ)⌋₊ : ℝ) < ((3 : ℝ) / 4) * x := by
    have hfloor : (⌊alpha * (x : ℝ)⌋₊ : ℝ) ≤ alpha * x :=
      Nat.floor_le (mul_nonneg halpha (Nat.cast_nonneg x))
    have hxR : (0 : ℝ) < x := by exact_mod_cast (Nat.zero_lt_of_lt hx)
    exact hfloor.trans_lt (mul_lt_mul_of_pos_right halphaXi hxR)
  have hdata : ∀ s : ResidualApproximationState (1 : ℚ), s.Coherent →
      AvailableBelow (initialSmoothBlock alpha x z) s →
      s.primePowerMeasure ≤ Q → y < s.primePowerMeasure →
      Lemma12StepData ((3 : ℝ) / 4) x s := by
    intro s _ _ hsQ hys
    apply hstepData s
    constructor
    · have hrootLt : (x : ℝ) ^ ((5 : ℝ)⁻¹) <
          ((⌊(x : ℝ) ^ ((5 : ℝ)⁻¹)⌋₊ + 1 : ℕ) : ℝ) := by
        simpa using Nat.lt_floor_add_one ((x : ℝ) ^ ((5 : ℝ)⁻¹))
      have hsucc : ⌊(x : ℝ) ^ ((5 : ℝ)⁻¹)⌋₊ + 1 ≤
          s.primePowerMeasure := by
        change y + 1 ≤ s.primePowerMeasure
        omega
      have hsuccR : ((⌊(x : ℝ) ^ ((5 : ℝ)⁻¹)⌋₊ + 1 : ℕ) : ℝ) ≤
          (s.primePowerMeasure : ℝ) := by exact_mod_cast hsucc
      simpa only [show ((5 : ℝ)⁻¹) = (1 : ℝ) / 5 by norm_num] using
        hrootLt.le.trans hsuccR
    · have hqQ : (s.primePowerMeasure : ℝ) ≤ Q := by
        exact_mod_cast hsQ
      have hupper := hqQ.trans hQz
      calc
        (s.primePowerMeasure : ℝ) ≤ z := hupper
        _ = (x : ℝ) * Real.log x ^ (-30 : ℝ) := by
          dsimp [z, proposition6MainCutoff]
          rw [show (-30 : ℝ) = -(30 : ℝ) by norm_num,
            Real.rpow_neg (zero_lt_one.trans_le hlog).le,
            show (30 : ℝ) = ((30 : ℕ) : ℝ) by norm_num,
            Real.rpow_natCast]
          ring
  exact ⟨lemma12RemovalDescent alpha ((3 : ℝ) / 4) z
    (initialSmoothBlock alpha x z) x y Q start rfl
    (by exact Finset.Subset.rfl)
    (by intro n hn _; exact hn) hbound hQz hxi hdata⟩

/--
Turn a completed Lemma 12 removal descent into a Proposition 6 certificate.
All loss estimates are explicit in the hypotheses: the removal union is
bounded by `totalEliminationBudget`, and the same quantity controls both the
reservoir capacity and the reciprocal-sum margins.  No analytic or
number-theoretic conclusion is assumed inside the bookkeeping proof.
-/
theorem exists_approximationCertificate_of_removalDescent
    {r : ℚ} {alpha beta z : ℝ} {x y R : ℕ}
    (halpha : 0 < alpha) (halphaOne : alpha ≤ 1)
    (hbeta : 0 < beta) (hbetaAlpha : beta ≤ alpha)
    (hExpLe : Real.exp (-(r : ℝ)) ≤ beta) (hx : 0 < x)
    (out : RemovalDescentOutcome (initialSmoothBlock alpha x z) x y
      (initialResidualApproximationState r alpha x z))
    (hmainCard : (initialSmoothBlock alpha x z).card ≤ R)
    (hcapacity :
      R - (initialSmoothBlock alpha x z).card +
          totalEliminationBudget x
            (initialResidualApproximationState r alpha x z).primePowerMeasure ≤
        (smoothReservoir (proposition6ReservoirScale beta x)).card)
    (hyRoot : (y : ℝ) ≤ (x : ℝ) ^ ((5 : ℝ)⁻¹))
    (hlowerPositive :
      0 < (Real.log (x : ℝ))⁻¹)
    (hlowerXMargin :
      (Real.log (x : ℝ))⁻¹ +
          ((R - (initialSmoothBlock alpha x z).card +
              totalEliminationBudget x
                (initialResidualApproximationState r alpha x z).primePowerMeasure : ℕ) : ℝ) /
            (beta * x / 2) <
        (initialResidual r alpha x z : ℝ))
    (hupperMargin :
      (initialResidual r alpha x z : ℝ) +
          (totalEliminationBudget x
              (initialResidualApproximationState r alpha x z).primePowerMeasure : ℝ) /
            (alpha * x) < 1) :
    Nonempty (ApproximationCertificate r x R) := by
  let start := initialResidualApproximationState r alpha x z
  let reservoir := smoothReservoir (proposition6ReservoirScale beta x)
  have hfinalCardEq : out.final.terms.selected.card =
      (initialSmoothBlock alpha x z).card - out.removed.card := by
    simpa [start, initialResidualApproximationState, initialApproximationState] using
      out.final_card_eq
  have hfinalCard : out.final.terms.selected.card ≤ R := by
    rw [hfinalCardEq]
    omega
  have hneed : R - out.final.terms.selected.card ≤ reservoir.card := by
    have houtBudget := out.card_le
    have hneedBound : R - out.final.terms.selected.card ≤
        R - (initialSmoothBlock alpha x z).card +
          totalEliminationBudget x
            (initialResidualApproximationState r alpha x z).primePowerMeasure := by
      rw [hfinalCardEq]
      omega
    exact hneedBound.trans (by simpa [reservoir] using hcapacity)
  have hfresh : Disjoint out.final.terms.used reservoir := by
    rw [out.used_eq]
    change Disjoint (initialSmoothBlock alpha x z) reservoir
    simpa [reservoir] using proposition6Reservoir_disjoint_initial_of_le
      (x := x) (z := z) hbeta hbetaAlpha
  obtain ⟨padding, hpadding, hpaddingUsed, hp, hcard, hcoherent,
      hresidual, hbalance, hpaddingProps⟩ :=
    exists_fivePrimeReservoir_padding hbeta out.coherent hfinalCard hneed hfresh
  let completed := out.final.applyStep (reservoirPaddingStep padding) hp
  have hpaddingCard : padding.card = R - out.final.terms.selected.card := by
    have hselected := reservoirPaddingStep_selected hpaddingUsed out.coherent
    have hdis : Disjoint out.final.terms.selected padding :=
      hpaddingUsed.mono_right out.coherent |>.symm
    have hcardUnion : (out.final.terms.selected ∪ padding).card =
        out.final.terms.selected.card + padding.card :=
      Finset.card_union_of_disjoint hdis
    have hcompletedCard : completed.terms.selected.card = R := by
      simpa [completed] using hcard
    rw [hselected, hcardUnion] at hcompletedCard
    omega
  have hpaddingCardBound : padding.card ≤
      R - (initialSmoothBlock alpha x z).card +
        totalEliminationBudget x
          (initialResidualApproximationState r alpha x z).primePowerMeasure := by
    rw [hpaddingCard, hfinalCardEq]
    have houtBudget := out.card_le
    omega
  have halphaX : 0 < alpha * (x : ℝ) :=
    mul_pos halpha (by exact_mod_cast hx)
  have hbetaX : 0 < beta * (x : ℝ) :=
    mul_pos hbeta (by exact_mod_cast hx)
  have hremovedSum : ((UnitFractions.rec_sum out.removed : ℚ) : ℝ) ≤
      (out.removed.card : ℝ) / (alpha * x) := by
    apply UnitFractions.rec_sum_le_card_div halphaX
    intro n hn
    exact (initialSmoothBlock_lower halpha.le (out.removed_subset_base hn)).le
  have hpaddingSum : ((UnitFractions.rec_sum padding : ℚ) : ℝ) ≤
      (padding.card : ℝ) / (beta * x / 2) := by
    apply UnitFractions.rec_sum_le_card_div (div_pos hbetaX (by norm_num))
    intro n hn
    exact (hpaddingProps n hn).1.le
  have hremovedNonneg :
      0 ≤ ((UnitFractions.rec_sum out.removed : ℚ) : ℝ) := by
    exact_mod_cast UnitFractions.rec_sum_nonneg
  have hpaddingNonneg :
      0 ≤ ((UnitFractions.rec_sum padding : ℚ) : ℝ) := by
    exact_mod_cast UnitFractions.rec_sum_nonneg
  have hremovedBudget : ((UnitFractions.rec_sum out.removed : ℚ) : ℝ) ≤
      (totalEliminationBudget x
          (initialResidualApproximationState r alpha x z).primePowerMeasure : ℝ) /
        (alpha * x) := by
    refine hremovedSum.trans ?_
    apply div_le_div_of_nonneg_right _ halphaX.le
    exact_mod_cast out.card_le
  have hpaddingBudget : ((UnitFractions.rec_sum padding : ℚ) : ℝ) ≤
      ((R - (initialSmoothBlock alpha x z).card +
          totalEliminationBudget x
            (initialResidualApproximationState r alpha x z).primePowerMeasure : ℕ) : ℝ) /
        (beta * x / 2) := by
    refine hpaddingSum.trans ?_
    apply div_le_div_of_nonneg_right _ (div_nonneg hbetaX.le (by norm_num))
    exact_mod_cast hpaddingCardBound
  have hcompletedResidualQ : completed.residual =
      initialResidual r alpha x z + UnitFractions.rec_sum out.removed -
        UnitFractions.rec_sum padding := by
    rw [show completed.residual = out.final.residual -
        UnitFractions.rec_sum padding by simpa [completed] using hresidual,
      out.residual_eq]
    rfl
  have hcompletedResidualR : (completed.residual : ℝ) =
      (initialResidual r alpha x z : ℝ) +
        (UnitFractions.rec_sum out.removed : ℝ) -
        (UnitFractions.rec_sum padding : ℝ) := by
    have hcast := congrArg (fun u : ℚ ↦ (u : ℝ)) hcompletedResidualQ
    norm_num at hcast ⊢
    exact hcast
  have hlowerX : (Real.log (x : ℝ))⁻¹ < (completed.residual : ℝ) := by
    rw [hcompletedResidualR]
    nlinarith
  have hupper : (completed.residual : ℝ) < 1 := by
    rw [hcompletedResidualR]
    nlinarith
  have hpositiveR : (0 : ℝ) < (completed.residual : ℝ) :=
    hlowerPositive.trans hlowerX
  have hpositiveQ : (0 : ℚ) < completed.residual := by
    exact_mod_cast hpositiveR
  have hfinalSmooth : UnitFractions.is_smooth
      ((x : ℝ) ^ ((5 : ℝ)⁻¹)) out.final.residual.den := by
    apply isSmooth_of_largestPrimePowerPart_le out.final.residual.den_ne_zero
    exact (by exact_mod_cast out.measure_le :
      (out.final.primePowerMeasure : ℝ) ≤ y) |>.trans hyRoot
  have hreservoirScaleLeRoot : proposition6ReservoirScale beta x ≤
      (x : ℝ) ^ ((5 : ℝ)⁻¹) := by
    apply Real.rpow_le_rpow
    · exact mul_nonneg hbeta.le (Nat.cast_nonneg x)
    · exact mul_le_of_le_one_left (Nat.cast_nonneg x)
        (hbetaAlpha.trans halphaOne)
    · norm_num
  have hpaddingSmooth : ∀ n ∈ padding,
      UnitFractions.is_smooth ((x : ℝ) ^ ((5 : ℝ)⁻¹)) n := by
    intro n hn q hq hqn
    exact (smoothReservoir_primePower_bound (hpadding hn) q hq hqn).trans
      hreservoirScaleLeRoot
  have hpaddingZero : ∀ n ∈ padding, n ≠ 0 := by
    intro n hn hn0
    subst n
    have hzeroLower := (hpaddingProps 0 hn).1
    norm_num at hzeroLower
    nlinarith
  have hcompletedSmooth : UnitFractions.is_smooth
      ((x : ℝ) ^ ((5 : ℝ)⁻¹)) completed.residual.den := by
    rw [show completed.residual = out.final.residual -
        UnitFractions.rec_sum padding by simpa [completed] using hresidual]
    exact sub_recSum_den_isSmooth out.final.residual hfinalSmooth
      hpaddingZero hpaddingSmooth
  have hprimePowerBound :=
    primePower_pow_five_le_of_den_isSmooth hcompletedSmooth
  have hcompletedZero : 0 ∉ completed.terms.selected := by
    intro hzero
    have hselected := reservoirPaddingStep_selected hpaddingUsed out.coherent
    rw [show completed.terms.selected = out.final.terms.selected ∪ padding by
      simpa [completed] using hselected, Finset.mem_union] at hzero
    rcases hzero with hzero | hzero
    · have hfinalSubset : out.final.terms.selected ⊆ initialSmoothBlock alpha x z := by
        rw [out.selected_eq]
        exact Finset.sdiff_subset.trans (by
          change (initialSmoothBlock alpha x z) ⊆ initialSmoothBlock alpha x z
          exact Finset.Subset.rfl)
      exact initialSmoothBlock_zero_not_mem alpha z x (hfinalSubset hzero)
    · exact hpaddingZero 0 hzero rfl
  have hcompletedInterval : ∀ n ∈ completed.terms.selected,
      Real.exp (-(r : ℝ)) * (x : ℝ) / 2 ≤ (n : ℝ) ∧
        (n : ℝ) ≤ x := by
    intro n hn
    have hselected := reservoirPaddingStep_selected hpaddingUsed out.coherent
    rw [show completed.terms.selected = out.final.terms.selected ∪ padding by
      simpa [completed] using hselected, Finset.mem_union] at hn
    rcases hn with hn | hn
    · have hnBase : n ∈ initialSmoothBlock alpha x z := by
        rw [out.selected_eq] at hn
        exact Finset.sdiff_subset hn
      constructor
      · calc
          Real.exp (-(r : ℝ)) * (x : ℝ) / 2 ≤ alpha * (x : ℝ) / 2 :=
            div_le_div_of_nonneg_right
              (mul_le_mul_of_nonneg_right (hExpLe.trans hbetaAlpha)
                (Nat.cast_nonneg x)) (by norm_num)
          _ ≤ alpha * (x : ℝ) :=
            div_le_self (mul_nonneg halpha.le (Nat.cast_nonneg x)) (by norm_num)
          _ ≤ (n : ℝ) := (initialSmoothBlock_lower halpha.le hnBase).le
      · exact_mod_cast initialSmoothBlock_upper hnBase
    · have hpdata := hpaddingProps n hn
      constructor
      · exact (div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_right hExpLe (Nat.cast_nonneg x)) (by norm_num)).trans
            hpdata.1.le
      · have hleBetaAlpha : beta * (x : ℝ) ≤ alpha * x :=
          mul_le_mul_of_nonneg_right hbetaAlpha (Nat.cast_nonneg x)
        have hleAlpha : alpha * (x : ℝ) ≤ x :=
          mul_le_of_le_one_left (Nat.cast_nonneg x) halphaOne
        exact hpdata.2.1.trans (hleBetaAlpha.trans hleAlpha)
  exact ⟨approximationCertificate_of_residualState completed
    (by simpa [completed] using hcard) hcompletedZero hcompletedInterval
    hpositiveQ hlowerX hupper hprimePowerBound⟩

/--
Finite last-crossing wrapper for the preceding certificate constructor.  If
the score `initial.card + correction` lies below `t`, its deficit and the full
Lemma 12 loss are each at most `D`, and the reservoir contains `2D` terms,
then all exact-cardinality and reciprocal-mass hypotheses follow.  This is the
arithmetic interface consumed by the final eventual construction.
-/
theorem exists_approximationCertificate_one_of_budget
    {alpha beta z : ℝ} {x y t correction D : ℕ}
    (halpha : 0 < alpha) (halphaOne : alpha ≤ 1)
    (hbeta : 0 < beta) (hbetaAlpha : beta ≤ alpha)
    (hExpLe : Real.exp (-1) ≤ beta) (hx : 0 < x)
    (out : RemovalDescentOutcome (initialSmoothBlock alpha x z) x y
      (initialResidualApproximationState (1 : ℚ) alpha x z))
    (hscore : (initialSmoothBlock alpha x z).card + correction ≤ t)
    (hdeficit : t - ((initialSmoothBlock alpha x z).card + correction) ≤ D)
    (hbudget : totalEliminationBudget x
      (initialResidualApproximationState (1 : ℚ) alpha x z).primePowerMeasure ≤ D)
    (hreservoir : 2 * D ≤
      (smoothReservoir (proposition6ReservoirScale beta x)).card)
    (hyRoot : (y : ℝ) ≤ (x : ℝ) ^ ((5 : ℝ)⁻¹))
    (hlowerPositive : 0 < (Real.log (x : ℝ))⁻¹)
    (hlowerMargin :
      (Real.log (x : ℝ))⁻¹ +
          4 * (D : ℝ) / (beta * x) <
        (initialResidual (1 : ℚ) alpha x z : ℝ))
    (hupperMargin :
      (initialResidual (1 : ℚ) alpha x z : ℝ) +
          (D : ℝ) / (alpha * x) < 1) :
    Nonempty (ApproximationCertificate (1 : ℚ) x (t - correction)) := by
  have hmainCard : (initialSmoothBlock alpha x z).card ≤ t - correction := by
    omega
  have hrequestedDeficit :
      (t - correction) - (initialSmoothBlock alpha x z).card =
        t - ((initialSmoothBlock alpha x z).card + correction) := by
    omega
  have hcount :
      (t - correction) - (initialSmoothBlock alpha x z).card +
          totalEliminationBudget x
            (initialResidualApproximationState (1 : ℚ) alpha x z).primePowerMeasure ≤
        2 * D := by
    rw [hrequestedDeficit]
    omega
  have hcapacity :
      (t - correction) - (initialSmoothBlock alpha x z).card +
          totalEliminationBudget x
            (initialResidualApproximationState (1 : ℚ) alpha x z).primePowerMeasure ≤
        (smoothReservoir (proposition6ReservoirScale beta x)).card :=
    hcount.trans hreservoir
  have halphaX : 0 < alpha * (x : ℝ) :=
    mul_pos halpha (by exact_mod_cast hx)
  have hbetaX : 0 < beta * (x : ℝ) :=
    mul_pos hbeta (by exact_mod_cast hx)
  have hcountR :
      (((t - correction) - (initialSmoothBlock alpha x z).card +
          totalEliminationBudget x
            (initialResidualApproximationState (1 : ℚ) alpha x z).primePowerMeasure : ℕ) : ℝ) ≤
        2 * D := by
    exact_mod_cast hcount
  have hquotient :
      (((t - correction) - (initialSmoothBlock alpha x z).card +
          totalEliminationBudget x
            (initialResidualApproximationState (1 : ℚ) alpha x z).primePowerMeasure : ℕ) : ℝ) /
          (beta * x / 2) ≤
        4 * (D : ℝ) / (beta * x) := by
    calc
      _ ≤ (2 * (D : ℝ)) / (beta * x / 2) := by
        exact div_le_div_of_nonneg_right hcountR
          (div_nonneg hbetaX.le (by norm_num))
      _ = 4 * (D : ℝ) / (beta * x) := by field_simp; ring
  have hlowerNeeded :
      (Real.log (x : ℝ))⁻¹ +
          (((t - correction) - (initialSmoothBlock alpha x z).card +
              totalEliminationBudget x
                (initialResidualApproximationState (1 : ℚ) alpha x z).primePowerMeasure : ℕ) : ℝ) /
            (beta * x / 2) <
        (initialResidual (1 : ℚ) alpha x z : ℝ) := by
    calc
      _ ≤ (Real.log (x : ℝ))⁻¹ + 4 * (D : ℝ) / (beta * x) := by
        exact add_le_add_right hquotient _
      _ < (initialResidual (1 : ℚ) alpha x z : ℝ) := hlowerMargin
  have hbudgetR :
      (totalEliminationBudget x
        (initialResidualApproximationState (1 : ℚ) alpha x z).primePowerMeasure : ℝ) ≤ D := by
    exact_mod_cast hbudget
  have hupperNeeded :
      (initialResidual (1 : ℚ) alpha x z : ℝ) +
          (totalEliminationBudget x
              (initialResidualApproximationState (1 : ℚ) alpha x z).primePowerMeasure : ℝ) /
            (alpha * x) < 1 := by
    calc
      _ ≤ (initialResidual (1 : ℚ) alpha x z : ℝ) +
          (D : ℝ) / (alpha * x) := by
        exact add_le_add_right
          (div_le_div_of_nonneg_right hbudgetR halphaX.le) _
      _ < 1 := hupperMargin
  exact exists_approximationCertificate_of_removalDescent
    halpha halphaOne hbeta hbetaAlpha (by simpa using hExpLe) hx out
    hmainCard hcapacity hyRoot
    hlowerPositive hlowerNeeded hupperNeeded

/--
An alternative exact-cardinality assembly which first runs Lemma 12 on the
whole initial block and then discards surplus survivors.  This keeps every
candidate denominator available during the descent.  The total discarded set
has exactly `initial.card - R` members, so its reciprocal mass is controlled by
one transparent hypothesis and no positive-density reservoir is needed.
-/
theorem exists_approximationCertificate_of_removalDescent_trim
    {r : ℚ} {alpha z : ℝ} {x y R : ℕ}
    (halpha : 0 < alpha)
    (hExpLe : Real.exp (-(r : ℝ)) ≤ alpha) (hx : 0 < x)
    (out : RemovalDescentOutcome (initialSmoothBlock alpha x z) x y
      (initialResidualApproximationState r alpha x z))
    (hR : R ≤ out.final.terms.selected.card)
    (hyRoot : (y : ℝ) ≤ (x : ℝ) ^ ((5 : ℝ)⁻¹))
    (hzRoot : z ≤ (x : ℝ) ^ ((5 : ℝ)⁻¹))
    (hlowerPositive : 0 < (Real.log (x : ℝ))⁻¹)
    (hlowerMargin :
      (Real.log (x : ℝ))⁻¹ < (initialResidual r alpha x z : ℝ))
    (hupperMargin :
      (initialResidual r alpha x z : ℝ) +
          (((initialSmoothBlock alpha x z).card - R : ℕ) : ℝ) /
            (alpha * x) < 1) :
    Nonempty (ApproximationCertificate r x R) := by
  obtain ⟨chosen, hchosen, hchosenCard⟩ :=
    Finset.exists_subset_card_eq hR
  let discard := out.final.terms.selected \ chosen
  have hdiscard : discard ⊆ out.final.terms.selected := Finset.sdiff_subset
  let hp : (eliminationRemovalStep discard).Valid out.final.terms :=
    eliminationRemovalStep_valid out.coherent hdiscard
  let completed := out.final.applyStep (eliminationRemovalStep discard) hp
  have hcompletedSelected : completed.terms.selected = chosen := by
    rw [show completed.terms.selected = out.final.terms.selected \ discard by
      simpa [completed, hp] using
        eliminationRemovalStep_selected out.coherent hdiscard]
    ext n
    simp only [discard, Finset.mem_sdiff]
    constructor
    · rintro ⟨hnFinal, hnnot⟩
      by_contra hnChosen
      exact hnnot ⟨hnFinal, hnChosen⟩
    · intro hnChosen
      exact ⟨hchosen hnChosen, fun hn ↦ hn.2 hnChosen⟩
  have hdiscardCard : discard.card = out.final.terms.selected.card - R := by
    dsimp [discard]
    rw [Finset.card_sdiff_of_subset hchosen, hchosenCard]
  have hremovedDiscard : Disjoint out.removed discard := by
    rw [Finset.disjoint_left]
    intro n hnRemoved hnDiscard
    have hnFinal : n ∈ out.final.terms.selected := hdiscard hnDiscard
    rw [out.selected_eq, Finset.mem_sdiff] at hnFinal
    exact hnFinal.2 hnRemoved
  let totalDiscard := out.removed ∪ discard
  have htotalSubset : totalDiscard ⊆ initialSmoothBlock alpha x z := by
    intro n hn
    rcases Finset.mem_union.mp hn with hnRemoved | hnDiscard
    · exact out.removed_subset_base hnRemoved
    · have hnFinal : n ∈ out.final.terms.selected := hdiscard hnDiscard
      rw [out.selected_eq] at hnFinal
      exact Finset.sdiff_subset hnFinal
  have htotalCard : totalDiscard.card =
      (initialSmoothBlock alpha x z).card - R := by
    dsimp [totalDiscard]
    have hfinalCardEq : out.final.terms.selected.card =
        (initialSmoothBlock alpha x z).card - out.removed.card := by
      simpa [initialResidualApproximationState, initialApproximationState] using
        out.final_card_eq
    rw [Finset.card_union_of_disjoint hremovedDiscard,
      hdiscardCard, hfinalCardEq]
    have houtCard : out.removed.card ≤ (initialSmoothBlock alpha x z).card :=
      Finset.card_le_card out.removed_subset_base
    have hRbase : R ≤ (initialSmoothBlock alpha x z).card - out.removed.card := by
      simpa [hfinalCardEq] using hR
    omega
  have hcompletedResidual : completed.residual =
      initialResidual r alpha x z + UnitFractions.rec_sum totalDiscard := by
    have hsumUnion : UnitFractions.rec_sum totalDiscard =
        UnitFractions.rec_sum out.removed + UnitFractions.rec_sum discard := by
      dsimp [totalDiscard]
      exact UnitFractions.rec_sum_disjoint hremovedDiscard
    rw [show completed.residual = out.final.residual +
        UnitFractions.rec_sum discard by
      simpa [completed, hp] using
        eliminationRemovalStep_residual out.coherent hdiscard,
      out.residual_eq, hsumUnion]
    change initialResidual r alpha x z + UnitFractions.rec_sum out.removed +
        UnitFractions.rec_sum discard = _
    ring
  have halphaX : 0 < alpha * (x : ℝ) :=
    mul_pos halpha (by exact_mod_cast hx)
  have htotalSum : ((UnitFractions.rec_sum totalDiscard : ℚ) : ℝ) ≤
      (totalDiscard.card : ℝ) / (alpha * x) := by
    apply UnitFractions.rec_sum_le_card_div halphaX
    intro n hn
    exact (initialSmoothBlock_lower halpha.le (htotalSubset hn)).le
  have htotalNonneg :
      0 ≤ ((UnitFractions.rec_sum totalDiscard : ℚ) : ℝ) := by
    exact_mod_cast UnitFractions.rec_sum_nonneg
  have hcompletedResidualR : (completed.residual : ℝ) =
      (initialResidual r alpha x z : ℝ) +
        (UnitFractions.rec_sum totalDiscard : ℝ) := by
    have hcast := congrArg (fun u : ℚ ↦ (u : ℝ)) hcompletedResidual
    norm_num at hcast ⊢
    exact hcast
  have hlower : (Real.log (x : ℝ))⁻¹ < (completed.residual : ℝ) := by
    rw [hcompletedResidualR]
    linarith
  have hupper : (completed.residual : ℝ) < 1 := by
    rw [hcompletedResidualR]
    rw [htotalCard] at htotalSum
    nlinarith
  have hpositiveR : (0 : ℝ) < (completed.residual : ℝ) :=
    hlowerPositive.trans hlower
  have hpositiveQ : (0 : ℚ) < completed.residual := by
    exact_mod_cast hpositiveR
  have hfinalSmooth : UnitFractions.is_smooth
      ((x : ℝ) ^ ((5 : ℝ)⁻¹)) out.final.residual.den := by
    apply isSmooth_of_largestPrimePowerPart_le out.final.residual.den_ne_zero
    exact (by exact_mod_cast out.measure_le :
      (out.final.primePowerMeasure : ℝ) ≤ y) |>.trans hyRoot
  have hdiscardZero : ∀ n ∈ discard, n ≠ 0 := by
    intro n hn
    exact fun hn0 ↦ initialSmoothBlock_zero_not_mem alpha z x
      (hn0 ▸ htotalSubset (Finset.mem_union_right _ hn))
  have hdiscardSmooth : ∀ n ∈ discard,
      UnitFractions.is_smooth ((x : ℝ) ^ ((5 : ℝ)⁻¹)) n := by
    intro n hn q hq hqn
    exact (initialSmoothBlock_smooth (htotalSubset
      (Finset.mem_union_right _ hn)) q hq hqn).trans hzRoot
  have hcompletedSmooth : UnitFractions.is_smooth
      ((x : ℝ) ^ ((5 : ℝ)⁻¹)) completed.residual.den := by
    rw [show completed.residual = out.final.residual +
        UnitFractions.rec_sum discard by
      simpa [completed, hp] using
        eliminationRemovalStep_residual out.coherent hdiscard]
    exact add_recSum_den_isSmooth out.final.residual hfinalSmooth
      hdiscardZero hdiscardSmooth
  have hprimePowerBound :=
    primePower_pow_five_le_of_den_isSmooth hcompletedSmooth
  have hcompletedZero : 0 ∉ completed.terms.selected := by
    rw [hcompletedSelected]
    intro hzero
    have hzeroFinal : 0 ∈ out.final.terms.selected := hchosen hzero
    rw [out.selected_eq] at hzeroFinal
    exact initialSmoothBlock_zero_not_mem alpha z x
      (Finset.sdiff_subset hzeroFinal)
  have hcompletedInterval : ∀ n ∈ completed.terms.selected,
      Real.exp (-(r : ℝ)) * (x : ℝ) / 2 ≤ (n : ℝ) ∧
        (n : ℝ) ≤ x := by
    intro n hn
    have hnBase : n ∈ initialSmoothBlock alpha x z := by
      rw [hcompletedSelected] at hn
      have hnFinal := hchosen hn
      rw [out.selected_eq] at hnFinal
      exact Finset.sdiff_subset hnFinal
    constructor
    · calc
        Real.exp (-(r : ℝ)) * (x : ℝ) / 2 ≤ alpha * (x : ℝ) / 2 :=
          div_le_div_of_nonneg_right
            (mul_le_mul_of_nonneg_right hExpLe (Nat.cast_nonneg x)) (by norm_num)
        _ ≤ alpha * (x : ℝ) :=
          div_le_self (mul_nonneg halpha.le (Nat.cast_nonneg x)) (by norm_num)
        _ ≤ (n : ℝ) := (initialSmoothBlock_lower halpha.le hnBase).le
    · exact_mod_cast initialSmoothBlock_upper hnBase
  exact ⟨approximationCertificate_of_residualState completed
    (by simpa [hcompletedSelected] using hchosenCard) hcompletedZero
    hcompletedInterval hpositiveQ hlower hupper hprimePowerBound⟩

/--
A concrete elimination stage: the finite-set step is valid and strictly lowers
the largest exact prime-power part of the reduced residual denominator.
-/
def ApproximationStep.EliminatesLargestPrimePower {r : ℚ}
    (s : ResidualApproximationState r) (d : ApproximationStep) : Prop :=
  ∃ hd : d.Valid s.terms,
    (s.applyStep d hd).primePowerMeasure < s.primePowerMeasure

lemma ApproximationStep.EliminatesLargestPrimePower.valid {r : ℚ}
    {s : ResidualApproximationState r} {d : ApproximationStep}
    (h : d.EliminatesLargestPrimePower s) : d.Valid s.terms := by
  exact h.choose

lemma ApproximationStep.EliminatesLargestPrimePower.measure_lt {r : ℚ}
    {s : ResidualApproximationState r} {d : ApproximationStep}
    (h : d.EliminatesLargestPrimePower s) :
    (s.applyStep d h.valid).primePowerMeasure < s.primePowerMeasure := by
  exact h.choose_spec

/-- A dependently valid run, since each residual state depends on prior proofs. -/
inductive ResidualApproximationRun {r : ℚ} :
    ResidualApproximationState r → ResidualApproximationState r → Prop
  | refl (s : ResidualApproximationState r) : ResidualApproximationRun s s
  | step {s t : ResidualApproximationState r} (d : ApproximationStep)
      (hd : d.Valid s.terms)
      (tail : ResidualApproximationRun (s.applyStep d hd) t) :
      ResidualApproximationRun s t

/--
Well-founded implementation of Martin's descent.  To use it, Lemma 12 supplies
a strictly measure-decreasing stage whenever the current measure exceeds `y`.
The recursion itself, including termination, is proved here.
-/
theorem exists_residual_descent_to
    {r : ℚ} (y : ℕ) (s : ResidualApproximationState r) (hs : s.Coherent)
    (hstep : ∀ u : ResidualApproximationState r, u.Coherent →
      y < u.primePowerMeasure →
      ∃ d : ApproximationStep, d.EliminatesLargestPrimePower u) :
    ∃ t : ResidualApproximationState r,
      ResidualApproximationRun s t ∧ t.Coherent ∧ t.primePowerMeasure ≤ y := by
  induction hmeasure : s.primePowerMeasure using Nat.strong_induction_on generalizing s with
  | h m ih =>
      by_cases hdone : s.primePowerMeasure ≤ y
      · exact ⟨s, .refl s, hs, hdone⟩
      · have habove : y < s.primePowerMeasure := Nat.lt_of_not_ge hdone
        obtain ⟨d, hd⟩ := hstep s hs habove
        let hv := hd.valid
        let next := s.applyStep d hv
        have hlt : next.primePowerMeasure < m := by
          rw [← hmeasure]
          exact hd.measure_lt
        have hnext : next.Coherent := ResidualApproximationState.Coherent.applyStep hv
        obtain ⟨t, hrun, htcoh, htmeasure⟩ := ih next.primePowerMeasure hlt next hnext rfl
        exact ⟨t, .step d hv hrun, htcoh, htmeasure⟩

/-! ## Concrete initialization -/

lemma availableBelow_initial
    (r : ℚ) (alpha : ℝ) (x : ℕ) (z : ℝ) :
    AvailableBelow (initialSmoothBlock alpha x z)
      (initialResidualApproximationState r alpha x z) := by
  intro n hn _
  exact hn

lemma initialResidualApproximationState_coherent
    (r : ℚ) (alpha : ℝ) (x : ℕ) (z : ℝ) :
    (initialResidualApproximationState r alpha x z).Coherent := by
  exact Finset.Subset.rfl

/--
The actual recursive descent starting from Martin's explicit initial block.
This theorem performs the construction once the concrete one-step Lemma 12 is
provided; its conclusion retains the exact reciprocal-sum invariant.
-/
theorem exists_descent_from_initialSmoothBlock
    (r : ℚ) (alpha : ℝ) (x y : ℕ) (z : ℝ)
    (hstep : ∀ u : ResidualApproximationState r, u.Coherent →
      y < u.primePowerMeasure →
      ∃ d : ApproximationStep, d.EliminatesLargestPrimePower u) :
    ∃ t : ResidualApproximationState r,
      ResidualApproximationRun (initialResidualApproximationState r alpha x z) t ∧
      t.Coherent ∧
      t.primePowerMeasure ≤ y ∧
      UnitFractions.rec_sum t.terms.selected + t.residual = r := by
  obtain ⟨t, hrun, hcoh, hmeasure⟩ :=
    exists_residual_descent_to y (initialResidualApproximationState r alpha x z)
      (initialResidualApproximationState_coherent r alpha x z) hstep
  exact ⟨t, hrun, hcoh, hmeasure, t.balance⟩

end

end Erdos285

#print axioms Erdos285.initialSmoothBlock_disjoint_smoothReservoir
#print axioms Erdos285.exists_residual_descent_to
#print axioms Erdos285.exists_descent_from_initialSmoothBlock
