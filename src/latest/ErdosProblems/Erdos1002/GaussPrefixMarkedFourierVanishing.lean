import ErdosProblems.Erdos1002.MarkedResonanceGaussCountBridge
import ErdosProblems.Erdos1002.OscillatoryCylinderTupleSum
import ErdosProblems.Erdos1002.PrefixFreezingPointwise
import ErdosProblems.Erdos1002.MixedFactorialEventExpansion
import ErdosProblems.Erdos1002.GaussUnmarkedFactorialLimit
import ErdosProblems.Erdos1002.PrimitiveShotCellFourier

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# A literal nonzero Fourier coefficient of the marked Gauss-prefix process

This file proves the order-one instance of the nonzero torus-Fourier
vanishing argument in Section 4.  It is stated for the *literal primitive
resonance event* and is therefore, by the exact resonance--Gauss-prefix
bridge, an actual coefficient of the Gauss-prefix marked process rather
than an abstract oscillatory surrogate.

For a denominator `p` and reduced numerator `q`, a compact signed-coordinate
window is one affine interval.  On that interval the torus character is the
single phase `exp (2π i h N p α)`: the numerator contributes an integral
phase and disappears.  Summing the exact interval estimate over the reduced
residues and over `p ≤ P` gives `O(P/N)`.  Thus every nonzero character
vanishes whenever `P = o(N)`, which is precisely the compact interior-time
regime of the marked point process.

The arbitrary-order mixed coefficient still needs the early/late cylinder
decomposition; this module deliberately closes the genuine order-one base
case without postulating any equidistribution hypothesis.
-/

open Filter MeasureTheory Set
open scoped BigOperators Topology Real

namespace Erdos1002

noncomputable section

local instance gaussPrefixMarkedFourierVanishingPropDecidable (P : Prop) :
    Decidable P := Classical.propDecidable P

/-- Left endpoint of the affine cell cut out by
`scaledResonanceCoordinate N p α ∈ [a,b]` and numerator `q`. -/
def scaledMarkedCellLeft (N p q : ℕ) (a : ℝ) : ℝ :=
  ((q : ℝ) + a / (Real.log (N : ℝ) * (p : ℝ))) / (p : ℝ)

/-- Right endpoint of the same affine cell. -/
def scaledMarkedCellRight (N p q : ℕ) (b : ℝ) : ℝ :=
  ((q : ℝ) + b / (Real.log (N : ℝ) * (p : ℝ))) / (p : ℝ)

/-- The literal first-factorial torus Fourier integrand for one denominator.
The value window is closed; endpoint choices are immaterial to its integral,
but using `Icc` makes the affine-cell identity pointwise. -/
def primitiveMarkedFourierIntegrand
    (N p : ℕ) (h : ℤ) (a b : ℝ) (α : ℝ) : ℂ :=
  if IsPrimitiveResonance p α ∧
      scaledResonanceCoordinate N p α ∈ Icc a b then
    paperExp ((h : ℝ) * resonanceTorusCoordinate N p α)
  else 0

/-- The finite denominator sum of the literal marked first-factorial
Fourier coefficient, integrated against uniform Lebesgue measure. -/
def primitiveMarkedFourierCoefficient
    (N P : ℕ) (h : ℤ) (a b : ℝ) : ℂ :=
  ∫ α, (∑ p ∈ Finset.Icc 2 P,
    primitiveMarkedFourierIntegrand N p h a b α) ∂uniform01Measure

theorem measurable_primitiveMarkedFourierIntegrand
    (N p : ℕ) (h : ℤ) (a b : ℝ) :
    Measurable (primitiveMarkedFourierIntegrand N p h a b) := by
  unfold primitiveMarkedFourierIntegrand
  apply Measurable.ite
  · exact (measurableSet_isPrimitiveResonance p).inter
      (measurableSet_Icc.preimage (measurable_scaledResonanceCoordinate N p))
  · have ht : Measurable
        (fun x ↦ (h : ℝ) * resonanceTorusCoordinate N p x) :=
      measurable_const.mul (measurable_resonanceTorusCoordinate N p)
    unfold paperExp
    fun_prop
  · exact measurable_const

private theorem paperExp_int_markedFourier (z : ℤ) :
    paperExp (z : ℝ) = 1 := by
  unfold paperExp
  convert! Complex.exp_int_mul_two_pi_mul_I z using 2
  push_cast
  ring

private theorem paperExp_add_markedFourier (u v : ℝ) :
    paperExp (u + v) = paperExp u * paperExp v := by
  unfold paperExp
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

theorem paperExp_mul_resonanceTorusCoordinate
    (N p : ℕ) (h : ℤ) (α : ℝ) :
    paperExp ((h : ℝ) * resonanceTorusCoordinate N p α) =
      paperExp ((h : ℝ) * (N : ℝ) * (p : ℝ) * α) := by
  let x : ℝ := (N : ℝ) * resonanceDelta p α
  have hfract : Int.fract x + (⌊x⌋ : ℤ) = x := Int.fract_add_floor x
  have hnum : (N : ℝ) * resonanceDelta p α =
      (N : ℝ) * (p : ℝ) * α -
        (((N : ℤ) * resonanceNumerator p α : ℤ) : ℝ) := by
    unfold resonanceDelta
    push_cast
    ring
  have htorus : resonanceTorusCoordinate N p α =
      x - (⌊x⌋ : ℤ) := by
    unfold resonanceTorusCoordinate
    linarith
  rw [htorus]
  change paperExp ((h : ℝ) *
      ((N : ℝ) * resonanceDelta p α - (⌊x⌋ : ℤ))) = _
  rw [hnum]
  let z : ℤ := -h * ((N : ℤ) * resonanceNumerator p α + ⌊x⌋)
  have harg :
      (h : ℝ) *
          (((N : ℝ) * (p : ℝ) * α -
              (((N : ℤ) * resonanceNumerator p α : ℤ) : ℝ)) -
            (⌊x⌋ : ℤ)) =
        (h : ℝ) * (N : ℝ) * (p : ℝ) * α + (z : ℝ) := by
    dsimp [z]
    push_cast
    ring
  rw [harg, paperExp_add_markedFourier, paperExp_int_markedFourier, mul_one]

theorem paperExp_scaledMarkedCell_eq_oscillatoryPhase
    (N p : ℕ) (h : ℤ) (α : ℝ) :
    paperExp ((h : ℝ) * (N : ℝ) * (p : ℝ) * α) =
      oscillatoryPhase ((h : ℝ) * (N : ℝ) * (p : ℝ)) α := by
  unfold paperExp oscillatoryPhase
  congr 1
  push_cast
  ring

/-- Solving the signed-coordinate inequalities gives exactly the two
affine endpoints above. -/
theorem mem_Icc_scaledMarkedCell_iff
    {N p q : ℕ} {a b α : ℝ} (hN : 2 ≤ N) (hp : 0 < p) :
    α ∈ Icc (scaledMarkedCellLeft N p q a)
        (scaledMarkedCellRight N p q b) ↔
      Real.log (N : ℝ) * (p : ℝ) *
          ((p : ℝ) * α - (q : ℝ)) ∈ Icc a b := by
  have hlog : 0 < Real.log (N : ℝ) :=
    Real.log_pos (by exact_mod_cast hN)
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp
  have hc : 0 < Real.log (N : ℝ) * (p : ℝ) := mul_pos hlog hpR
  constructor
  · rintro ⟨hl, hr⟩
    rw [scaledMarkedCellLeft, div_le_iff₀ hpR] at hl
    rw [scaledMarkedCellRight, le_div_iff₀ hpR] at hr
    have hl' : a ≤
        (Real.log (N : ℝ) * (p : ℝ)) *
          ((p : ℝ) * α - (q : ℝ)) := by
      have hpre : a / (Real.log (N : ℝ) * (p : ℝ)) ≤
          (p : ℝ) * α - (q : ℝ) := by linarith
      have hmul := (div_le_iff₀ hc).1 hpre
      nlinarith
    have hr' :
        (Real.log (N : ℝ) * (p : ℝ)) *
          ((p : ℝ) * α - (q : ℝ)) ≤ b := by
      have hpre : (p : ℝ) * α - (q : ℝ) ≤
          b / (Real.log (N : ℝ) * (p : ℝ)) := by linarith
      have hmul := (le_div_iff₀ hc).1 hpre
      nlinarith
    constructor <;> nlinarith
  · rintro ⟨hl, hr⟩
    constructor
    · rw [scaledMarkedCellLeft, div_le_iff₀ hpR]
      have hl' : a / (Real.log (N : ℝ) * (p : ℝ)) ≤
          (p : ℝ) * α - (q : ℝ) := by
        apply (div_le_iff₀ hc).2
        nlinarith
      linarith
    · rw [scaledMarkedCellRight, le_div_iff₀ hpR]
      have hr' : (p : ℝ) * α - (q : ℝ) ≤
          b / (Real.log (N : ℝ) * (p : ℝ)) := by
        apply (le_div_iff₀ hc).2
        nlinarith
      linarith

/-- A point in a compact signed-coordinate cell is strictly inside the
nearest-integer cell when `A / log N < 1/2`. -/
theorem abs_affine_sub_lt_half_of_mem_scaledMarkedCell
    {N p q : ℕ} {a b A α : ℝ}
    (hN : 2 ≤ N) (hp : 0 < p) (hA : 0 ≤ A)
    (ha : |a| ≤ A) (hb : |b| ≤ A)
    (hsmall : A / Real.log (N : ℝ) < (1 : ℝ) / 2)
    (hα : α ∈ Icc (scaledMarkedCellLeft N p q a)
      (scaledMarkedCellRight N p q b)) :
    |(p : ℝ) * α - (q : ℝ)| < (1 : ℝ) / 2 := by
  have hlog : 0 < Real.log (N : ℝ) :=
    Real.log_pos (by exact_mod_cast hN)
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp
  have hc : 0 < Real.log (N : ℝ) * (p : ℝ) := mul_pos hlog hpR
  have hy := (mem_Icc_scaledMarkedCell_iff hN hp).1 hα
  have habounds : -A ≤
      Real.log (N : ℝ) * (p : ℝ) *
          ((p : ℝ) * α - (q : ℝ)) ∧
      Real.log (N : ℝ) * (p : ℝ) *
          ((p : ℝ) * α - (q : ℝ)) ≤ A := by
    have haa := (abs_le.mp ha)
    have hbb := (abs_le.mp hb)
    exact ⟨haa.1.trans hy.1, hy.2.trans hbb.2⟩
  have habsScaled :
      |Real.log (N : ℝ) * (p : ℝ) *
          ((p : ℝ) * α - (q : ℝ))| ≤ A :=
    abs_le.mpr habounds
  have habs : |(p : ℝ) * α - (q : ℝ)| ≤
      A / (Real.log (N : ℝ) * (p : ℝ)) := by
    rw [abs_mul, abs_mul, abs_of_pos hlog, abs_of_pos hpR] at habsScaled
    apply (le_div_iff₀ hc).2
    calc
      |(p : ℝ) * α - (q : ℝ)| *
          (Real.log (N : ℝ) * (p : ℝ)) =
          Real.log (N : ℝ) * (p : ℝ) *
            |(p : ℝ) * α - (q : ℝ)| := by ring
      _ ≤ A := habsScaled
  have hdiv : A / (Real.log (N : ℝ) * (p : ℝ)) ≤
      A / Real.log (N : ℝ) := by
    have hpOne : (1 : ℝ) ≤ p := by exact_mod_cast hp
    apply div_le_div_of_nonneg_left hA hlog
    nlinarith
  exact (habs.trans hdiv).trans_lt hsmall

/-- Every reduced scaled cell lies in the open unit interval. -/
theorem scaledMarkedCell_subset_Ioo
    {N p q : ℕ} {a b A : ℝ}
    (hN : 2 ≤ N) (hp : 2 ≤ p) (hq : q ∈ reducedResidues p)
    (hA : 0 ≤ A) (ha : |a| ≤ A) (hb : |b| ≤ A)
    (hsmall : A / Real.log (N : ℝ) < (1 : ℝ) / 2) :
    Icc (scaledMarkedCellLeft N p q a)
        (scaledMarkedCellRight N p q b) ⊆ Ioo (0 : ℝ) 1 := by
  intro α hα
  have hnear := abs_affine_sub_lt_half_of_mem_scaledMarkedCell
    hN (by omega) hA ha hb hsmall hα
  have hcell : α ∈ Ioc (nearestCellLeft p q) (nearestCellRight p q) :=
    (mem_nearestCell_iff (by omega) α).1 <| by
      rw [mem_Ioc]
      constructor
      · linarith [(abs_lt.mp hnear).1]
      · exact (abs_lt.mp hnear).2.le
  have hunit := nearestCell_interval_subset_unit hp hq hcell
  have hqlt : q < p := by
    exact Finset.mem_range.mp (Finset.mem_filter.mp (by
      simpa only [reducedResidues] using! hq)).1
  have hpR : (0 : ℝ) < p := by positivity
  have hqR : (q : ℝ) + 1 ≤ (p : ℝ) := by
    exact_mod_cast (show q + 1 ≤ p by omega)
  have hupper := (abs_lt.mp hnear).2
  refine ⟨hunit.1, ?_⟩
  nlinarith

/-- The nearest numerator and primitive condition on one reduced scaled
cell are literal, not merely almost-everywhere assertions. -/
theorem numerator_eq_and_primitive_of_mem_scaledMarkedCell
    {N p q : ℕ} {a b A α : ℝ}
    (hN : 2 ≤ N) (hp : 2 ≤ p) (hq : q ∈ reducedResidues p)
    (hA : 0 ≤ A) (ha : |a| ≤ A) (hb : |b| ≤ A)
    (hsmall : A / Real.log (N : ℝ) < (1 : ℝ) / 2)
    (hα : α ∈ Icc (scaledMarkedCellLeft N p q a)
      (scaledMarkedCellRight N p q b)) :
    resonanceNumerator p α = (q : ℤ) ∧ IsPrimitiveResonance p α := by
  have hnear := abs_affine_sub_lt_half_of_mem_scaledMarkedCell
    hN (by omega) hA ha hb hsmall hα
  have hnum := resonanceNumerator_eq_of_abs_sub_lt_half hnear
  refine ⟨hnum, ?_⟩
  unfold IsPrimitiveResonance
  rw [hnum]
  have hcop := (Finset.mem_filter.mp (by
    simpa only [reducedResidues] using! hq)).2
  simpa using! hcop

/-- Closed-cell version used for the exact pointwise residue expansion. -/
def scaledMarkedCellFourierTerm
    (N p q : ℕ) (h : ℤ) (a b : ℝ) (α : ℝ) : ℂ :=
  if α ∈ Icc (scaledMarkedCellLeft N p q a)
      (scaledMarkedCellRight N p q b) then
    oscillatoryPhase ((h : ℝ) * (N : ℝ) * (p : ℝ)) α
  else 0

/-- Half-open version with support in the precise interval-integral domain.
It differs from the closed version only at one endpoint. -/
def scaledMarkedCellFourierTermIoc
    (N p q : ℕ) (h : ℤ) (a b : ℝ) (α : ℝ) : ℂ :=
  if α ∈ Ioc (scaledMarkedCellLeft N p q a)
      (scaledMarkedCellRight N p q b) then
    oscillatoryPhase ((h : ℝ) * (N : ℝ) * (p : ℝ)) α
  else 0

theorem measurable_scaledMarkedCellFourierTerm
    (N p q : ℕ) (h : ℤ) (a b : ℝ) :
    Measurable (scaledMarkedCellFourierTerm N p q h a b) := by
  unfold scaledMarkedCellFourierTerm
  apply Measurable.ite measurableSet_Icc
  · unfold oscillatoryPhase
    fun_prop
  · exact measurable_const

theorem measurable_scaledMarkedCellFourierTermIoc
    (N p q : ℕ) (h : ℤ) (a b : ℝ) :
    Measurable (scaledMarkedCellFourierTermIoc N p q h a b) := by
  unfold scaledMarkedCellFourierTermIoc
  apply Measurable.ite measurableSet_Ioc
  · unfold oscillatoryPhase
    fun_prop
  · exact measurable_const

/-- Exact finite reduced-residue expansion of the literal marked Fourier
integrand on the open unit interval. -/
theorem primitiveMarkedFourierIntegrand_eq_sum_scaledMarkedCells
    {N p : ℕ} (h : ℤ) {a b A α : ℝ}
    (hN : 2 ≤ N) (hp : 2 ≤ p) (hA : 0 ≤ A)
    (ha : |a| ≤ A) (hb : |b| ≤ A)
    (hsmall : A / Real.log (N : ℝ) < (1 : ℝ) / 2)
    (hα : α ∈ Ioo (0 : ℝ) 1) :
    primitiveMarkedFourierIntegrand N p h a b α =
      ∑ q ∈ reducedResidues p,
        scaledMarkedCellFourierTerm N p q h a b α := by
  classical
  by_cases hevent : IsPrimitiveResonance p α ∧
      scaledResonanceCoordinate N p α ∈ Icc a b
  · let q : ℕ := (resonanceNumerator p α).natAbs
    have hqmem : q ∈ reducedResidues p :=
      resonanceNumerator_nat_mem_reducedResidues hp hα hevent.1
    have hqnonneg : 0 ≤ resonanceNumerator p α :=
      (resonanceNumerator_bounds_of_mem_unitInterval p hα).1
    have hqcast : (q : ℤ) = resonanceNumerator p α := by
      dsimp [q]
      rw [Int.natCast_natAbs, abs_of_nonneg hqnonneg]
    have hcell : α ∈ Icc (scaledMarkedCellLeft N p q a)
        (scaledMarkedCellRight N p q b) := by
      apply (mem_Icc_scaledMarkedCell_iff hN (by omega)).2
      simpa only [scaledResonanceCoordinate, resonanceDelta, ← hqcast]
        using! hevent.2
    rw [primitiveMarkedFourierIntegrand, if_pos hevent]
    rw [Finset.sum_eq_single q]
    · rw [scaledMarkedCellFourierTerm, if_pos hcell,
        paperExp_mul_resonanceTorusCoordinate,
        paperExp_scaledMarkedCell_eq_oscillatoryPhase]
    · intro q' hq'mem hq'ne
      have hnot : α ∉ Icc (scaledMarkedCellLeft N p q' a)
          (scaledMarkedCellRight N p q' b) := by
        intro hcell'
        have hnum' :=
          (numerator_eq_and_primitive_of_mem_scaledMarkedCell
            hN hp hq'mem hA ha hb hsmall hcell').1
        apply hq'ne
        have hz : (q' : ℤ) = (q : ℤ) := hnum'.symm.trans hqcast.symm
        exact_mod_cast hz
      rw [scaledMarkedCellFourierTerm, if_neg hnot]
    · exact fun hnot ↦ (hnot hqmem).elim
  · rw [primitiveMarkedFourierIntegrand, if_neg hevent]
    symm
    apply Finset.sum_eq_zero
    intro q hqmem
    have hnot : α ∉ Icc (scaledMarkedCellLeft N p q a)
        (scaledMarkedCellRight N p q b) := by
      intro hcell
      have hdata := numerator_eq_and_primitive_of_mem_scaledMarkedCell
        hN hp hqmem hA ha hb hsmall hcell
      apply hevent
      refine ⟨hdata.2, ?_⟩
      have hcoord := (mem_Icc_scaledMarkedCell_iff hN (by omega)).1 hcell
      simpa only [scaledResonanceCoordinate, resonanceDelta, hdata.1]
        using! hcoord
    rw [scaledMarkedCellFourierTerm, if_neg hnot]

theorem scaledMarkedCellLeft_le_right
    {N p q : ℕ} {a b : ℝ} (hN : 2 ≤ N) (hp : 0 < p)
    (hab : a ≤ b) :
    scaledMarkedCellLeft N p q a ≤ scaledMarkedCellRight N p q b := by
  have hlog : 0 < Real.log (N : ℝ) :=
    Real.log_pos (by exact_mod_cast hN)
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp
  unfold scaledMarkedCellLeft scaledMarkedCellRight
  apply div_le_div_of_nonneg_right _ hpR.le
  gcongr

theorem scaledMarkedCellFourierTerm_ae_eq_Ioc
    (N p q : ℕ) (h : ℤ) (a b : ℝ) :
    scaledMarkedCellFourierTerm N p q h a b =ᵐ[volume]
      scaledMarkedCellFourierTermIoc N p q h a b := by
  have hleft : ∀ᵐ α : ℝ ∂volume,
      α ≠ scaledMarkedCellLeft N p q a := by
    simp [ae_iff, measure_singleton]
  filter_upwards [hleft] with α hα
  unfold scaledMarkedCellFourierTerm scaledMarkedCellFourierTermIoc
  by_cases hclosed : α ∈ Icc (scaledMarkedCellLeft N p q a)
      (scaledMarkedCellRight N p q b)
  · have hopen : α ∈ Ioc (scaledMarkedCellLeft N p q a)
        (scaledMarkedCellRight N p q b) :=
      ⟨lt_of_le_of_ne hclosed.1 (Ne.symm hα), hclosed.2⟩
    rw [if_pos hclosed, if_pos hopen]
  · have hopen : α ∉ Ioc (scaledMarkedCellLeft N p q a)
        (scaledMarkedCellRight N p q b) := fun h ↦
      hclosed ⟨h.1.le, h.2⟩
    rw [if_neg hclosed, if_neg hopen]

theorem support_scaledMarkedCellFourierTermIoc_subset
    (N p q : ℕ) (h : ℤ) (a b : ℝ) :
    Function.support (scaledMarkedCellFourierTermIoc N p q h a b) ⊆
      Ioc (scaledMarkedCellLeft N p q a)
        (scaledMarkedCellRight N p q b) := by
  intro α hα
  by_contra hnot
  change scaledMarkedCellFourierTermIoc N p q h a b α ≠ 0 at hα
  rw [scaledMarkedCellFourierTermIoc, if_neg hnot] at hα
  exact hα rfl

/-- One reduced residue contributes exactly one ordinary oscillatory
interval integral. -/
theorem integral_scaledMarkedCellFourierTerm
    {N p q : ℕ} (h : ℤ) {a b A : ℝ}
    (hN : 2 ≤ N) (hp : 2 ≤ p) (hq : q ∈ reducedResidues p)
    (hab : a ≤ b) (hA : 0 ≤ A) (ha : |a| ≤ A) (hb : |b| ≤ A)
    (hsmall : A / Real.log (N : ℝ) < (1 : ℝ) / 2) :
    (∫ α, scaledMarkedCellFourierTerm N p q h a b α
        ∂uniform01Measure) =
      ∫ α : ℝ in scaledMarkedCellLeft N p q a..
          scaledMarkedCellRight N p q b,
        oscillatoryPhase ((h : ℝ) * (N : ℝ) * (p : ℝ)) α := by
  let f : ℝ → ℂ := scaledMarkedCellFourierTerm N p q h a b
  let g : ℝ → ℂ := scaledMarkedCellFourierTermIoc N p q h a b
  have hcellUnit := scaledMarkedCell_subset_Ioo
    hN hp hq hA ha hb hsmall
  have hsupportUnit : Function.support g ⊆ Ioc (0 : ℝ) 1 := by
    intro α hα
    have hcell := support_scaledMarkedCellFourierTermIoc_subset
      N p q h a b hα
    have hclosed : α ∈ Icc (scaledMarkedCellLeft N p q a)
        (scaledMarkedCellRight N p q b) := ⟨hcell.1.le, hcell.2⟩
    have hunit := hcellUnit hclosed
    exact ⟨hunit.1, hunit.2.le⟩
  have hsupportCell : Function.support g ⊆
      Ioc (scaledMarkedCellLeft N p q a)
        (scaledMarkedCellRight N p q b) :=
    support_scaledMarkedCellFourierTermIoc_subset N p q h a b
  have hunitIntegral (u : ℝ → ℂ) :
      (∫ α, u α ∂uniform01Measure) = ∫ α : ℝ in (0 : ℝ)..1, u α := by
    rw [uniform01Measure, restrict_Ioo_eq_restrict_Ioc]
    exact (intervalIntegral.integral_of_le (by norm_num)).symm
  calc
    (∫ α, scaledMarkedCellFourierTerm N p q h a b α
        ∂uniform01Measure) = ∫ α : ℝ in (0 : ℝ)..1, f α :=
      hunitIntegral f
    _ = ∫ α : ℝ in (0 : ℝ)..1, g α := by
      apply intervalIntegral.integral_congr_ae
      filter_upwards [scaledMarkedCellFourierTerm_ae_eq_Ioc
        N p q h a b] with α hfg
      intro _hα
      exact hfg
    _ = ∫ α : ℝ, g α :=
      intervalIntegral.integral_eq_integral_of_support_subset hsupportUnit
    _ = ∫ α : ℝ in scaledMarkedCellLeft N p q a..
          scaledMarkedCellRight N p q b, g α :=
      (intervalIntegral.integral_eq_integral_of_support_subset
        hsupportCell).symm
    _ = ∫ α : ℝ in scaledMarkedCellLeft N p q a..
          scaledMarkedCellRight N p q b,
        oscillatoryPhase ((h : ℝ) * (N : ℝ) * (p : ℝ)) α := by
      apply intervalIntegral.integral_congr_ae
      filter_upwards with α
      intro hα
      have hlr : scaledMarkedCellLeft N p q a ≤
          scaledMarkedCellRight N p q b :=
        scaledMarkedCellLeft_le_right (N := N) (p := p) (q := q)
          hN (by omega) hab
      have hIoc : α ∈ Ioc (scaledMarkedCellLeft N p q a)
          (scaledMarkedCellRight N p q b) := by
        rw [uIoc_of_le hlr] at hα
        exact hα
      change scaledMarkedCellFourierTermIoc N p q h a b α = _
      rw [scaledMarkedCellFourierTermIoc, if_pos hIoc]

/-- Explicit `1/(π |h| N p)` cancellation for one reduced cell. -/
theorem norm_integral_scaledMarkedCellFourierTerm_le
    {N p q : ℕ} {h : ℤ} {a b A : ℝ}
    (hN : 2 ≤ N) (hp : 2 ≤ p) (hq : q ∈ reducedResidues p)
    (hh : h ≠ 0) (hab : a ≤ b) (hA : 0 ≤ A)
    (ha : |a| ≤ A) (hb : |b| ≤ A)
    (hsmall : A / Real.log (N : ℝ) < (1 : ℝ) / 2) :
    ‖∫ α, scaledMarkedCellFourierTerm N p q h a b α
        ∂uniform01Measure‖ ≤
      1 / (Real.pi * |(h : ℝ)| * (N : ℝ) * (p : ℝ)) := by
  rw [integral_scaledMarkedCellFourierTerm h hN hp hq hab hA ha hb hsmall]
  have hK : (h : ℝ) * (N : ℝ) * (p : ℝ) ≠ 0 := by
    exact mul_ne_zero (mul_ne_zero (by exact_mod_cast hh)
      (by positivity)) (by positivity)
  simpa only [abs_mul, abs_of_pos (show (0 : ℝ) < (N : ℝ) by positivity),
    abs_of_pos (show (0 : ℝ) < (p : ℝ) by positivity), mul_assoc] using
    norm_intervalIntegral_oscillatoryPhase_le
      (scaledMarkedCellLeft N p q a)
      (scaledMarkedCellRight N p q b)
      ((h : ℝ) * (N : ℝ) * (p : ℝ)) hK

theorem integrable_scaledMarkedCellFourierTerm_uniform01
    (N p q : ℕ) (h : ℤ) (a b : ℝ) :
    Integrable (scaledMarkedCellFourierTerm N p q h a b)
      uniform01Measure := by
  apply Integrable.of_bound
    (measurable_scaledMarkedCellFourierTerm N p q h a b).aestronglyMeasurable 1
  filter_upwards with α
  unfold scaledMarkedCellFourierTerm
  split_ifs
  · rw [norm_oscillatoryPhase]
  · simp

theorem integrable_primitiveMarkedFourierIntegrand_uniform01
    (N p : ℕ) (h : ℤ) (a b : ℝ) :
    Integrable (primitiveMarkedFourierIntegrand N p h a b)
      uniform01Measure := by
  apply Integrable.of_bound
    (measurable_primitiveMarkedFourierIntegrand N p h a b).aestronglyMeasurable 1
  filter_upwards with α
  unfold primitiveMarkedFourierIntegrand
  split_ifs
  · unfold paperExp
    rw [Complex.norm_exp]
    simp
  · simp

/-- Integrated finite reduced-residue expansion for one literal marked
denominator event. -/
theorem integral_primitiveMarkedFourierIntegrand_eq_sum_cells
    {N p : ℕ} (h : ℤ) {a b A : ℝ}
    (hN : 2 ≤ N) (hp : 2 ≤ p) (hA : 0 ≤ A)
    (ha : |a| ≤ A) (hb : |b| ≤ A)
    (hsmall : A / Real.log (N : ℝ) < (1 : ℝ) / 2) :
    (∫ α, primitiveMarkedFourierIntegrand N p h a b α
        ∂uniform01Measure) =
      ∑ q ∈ reducedResidues p,
        ∫ α, scaledMarkedCellFourierTerm N p q h a b α
          ∂uniform01Measure := by
  have hunit : ∀ᵐ α ∂uniform01Measure, α ∈ Ioo (0 : ℝ) 1 := by
    rw [uniform01Measure]
    exact ae_restrict_mem measurableSet_Ioo
  calc
    (∫ α, primitiveMarkedFourierIntegrand N p h a b α
        ∂uniform01Measure) =
        ∫ α, (∑ q ∈ reducedResidues p,
          scaledMarkedCellFourierTerm N p q h a b α)
            ∂uniform01Measure := by
      apply integral_congr_ae
      filter_upwards [hunit] with α hα
      exact primitiveMarkedFourierIntegrand_eq_sum_scaledMarkedCells
        h hN hp hA ha hb hsmall hα
    _ = ∑ q ∈ reducedResidues p,
        ∫ α, scaledMarkedCellFourierTerm N p q h a b α
          ∂uniform01Measure := by
      rw [MeasureTheory.integral_finset_sum]
      intro q _hq
      exact integrable_scaledMarkedCellFourierTerm_uniform01 N p q h a b

/-- One literal denominator contributes at most its number of reduced
residues times the one-cell oscillatory bound. -/
theorem norm_integral_primitiveMarkedFourierIntegrand_le
    {N p : ℕ} {h : ℤ} {a b A : ℝ}
    (hN : 2 ≤ N) (hp : 2 ≤ p) (hh : h ≠ 0)
    (hab : a ≤ b) (hA : 0 ≤ A) (ha : |a| ≤ A) (hb : |b| ≤ A)
    (hsmall : A / Real.log (N : ℝ) < (1 : ℝ) / 2) :
    ‖∫ α, primitiveMarkedFourierIntegrand N p h a b α
        ∂uniform01Measure‖ ≤
      (Nat.totient p : ℝ) /
        (Real.pi * |(h : ℝ)| * (N : ℝ) * (p : ℝ)) := by
  rw [integral_primitiveMarkedFourierIntegrand_eq_sum_cells
    h hN hp hA ha hb hsmall]
  calc
    ‖∑ q ∈ reducedResidues p,
        ∫ α, scaledMarkedCellFourierTerm N p q h a b α
          ∂uniform01Measure‖ ≤
        ∑ q ∈ reducedResidues p,
          ‖∫ α, scaledMarkedCellFourierTerm N p q h a b α
            ∂uniform01Measure‖ := norm_sum_le _ _
    _ ≤ ∑ _q ∈ reducedResidues p,
        (1 / (Real.pi * |(h : ℝ)| * (N : ℝ) * (p : ℝ))) := by
      gcongr with q hq
      exact norm_integral_scaledMarkedCellFourierTerm_le
        hN hp hq hh hab hA ha hb hsmall
    _ = (Nat.totient p : ℝ) /
        (Real.pi * |(h : ℝ)| * (N : ℝ) * (p : ℝ)) := by
      rw [Finset.sum_const, nsmul_eq_mul, card_reducedResidues]
      ring

/-- The exact `O(P/N)` bound for the literal first-factorial nonzero marked
Fourier coefficient.  No mixing or equidistribution hypothesis occurs. -/
theorem norm_primitiveMarkedFourierCoefficient_le
    {N P : ℕ} {h : ℤ} {a b A : ℝ}
    (hN : 2 ≤ N) (hh : h ≠ 0) (hab : a ≤ b)
    (hA : 0 ≤ A) (ha : |a| ≤ A) (hb : |b| ≤ A)
    (hsmall : A / Real.log (N : ℝ) < (1 : ℝ) / 2) :
    ‖primitiveMarkedFourierCoefficient N P h a b‖ ≤
      (P : ℝ) / (Real.pi * |(h : ℝ)| * (N : ℝ)) := by
  unfold primitiveMarkedFourierCoefficient
  rw [MeasureTheory.integral_finset_sum]
  · calc
      ‖∑ p ∈ Finset.Icc 2 P,
          ∫ α, primitiveMarkedFourierIntegrand N p h a b α
            ∂uniform01Measure‖ ≤
          ∑ p ∈ Finset.Icc 2 P,
            ‖∫ α, primitiveMarkedFourierIntegrand N p h a b α
              ∂uniform01Measure‖ := norm_sum_le _ _
      _ ≤ ∑ _p ∈ Finset.Icc 2 P,
          (1 / (Real.pi * |(h : ℝ)| * (N : ℝ))) := by
        apply Finset.sum_le_sum
        intro p hpMem
        have hp : 2 ≤ p := (Finset.mem_Icc.mp hpMem).1
        have hden : 0 < Real.pi * |(h : ℝ)| * (N : ℝ) := by
          have hhR : (h : ℝ) ≠ 0 := by exact_mod_cast hh
          positivity
        calc
          ‖∫ α, primitiveMarkedFourierIntegrand N p h a b α
              ∂uniform01Measure‖ ≤
              (Nat.totient p : ℝ) /
                (Real.pi * |(h : ℝ)| * (N : ℝ) * (p : ℝ)) :=
            norm_integral_primitiveMarkedFourierIntegrand_le
              hN hp hh hab hA ha hb hsmall
          _ ≤ 1 / (Real.pi * |(h : ℝ)| * (N : ℝ)) := by
            have hpR : (0 : ℝ) < p := by positivity
            have htot : (Nat.totient p : ℝ) ≤ (p : ℝ) := by
              exact_mod_cast totient_le_self p
            apply (div_le_iff₀ (mul_pos hden hpR)).2
            calc
              (Nat.totient p : ℝ) ≤ (p : ℝ) := htot
              _ = 1 / (Real.pi * |(h : ℝ)| * (N : ℝ)) *
                    (Real.pi * |(h : ℝ)| * (N : ℝ) * (p : ℝ)) := by
                field_simp
      _ = ((Finset.Icc 2 P).card : ℝ) *
          (1 / (Real.pi * |(h : ℝ)| * (N : ℝ))) := by
        rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ (P : ℝ) *
          (1 / (Real.pi * |(h : ℝ)| * (N : ℝ))) := by
        gcongr
        have hcard : (Finset.Icc 2 P).card ≤ P := by
          rw [Nat.card_Icc]
          omega
        exact_mod_cast hcard
      _ = (P : ℝ) / (Real.pi * |(h : ℝ)| * (N : ℝ)) := by ring
  · intro p _hp
    exact integrable_primitiveMarkedFourierIntegrand_uniform01 N p h a b

/-- Genuine nonzero torus-Fourier vanishing in every sublinear denominator
range.  This is the complete order-one marked factorial statement on an
interior time layer. -/
theorem tendsto_primitiveMarkedFourierCoefficient_zero
    (Ns Ps : ℕ → ℕ) {h : ℤ} {a b A : ℝ}
    (hh : h ≠ 0) (hab : a ≤ b) (hA : 0 ≤ A)
    (ha : |a| ≤ A) (hb : |b| ≤ A)
    (hNs : ∀ᶠ n : ℕ in atTop, 2 ≤ Ns n)
    (hsmall : ∀ᶠ n : ℕ in atTop,
      A / Real.log (Ns n : ℝ) < (1 : ℝ) / 2)
    (hsublinear : Tendsto
      (fun n : ℕ ↦ (Ps n : ℝ) / (Ns n : ℝ)) atTop (𝓝 0)) :
    Tendsto
      (fun n : ℕ ↦ primitiveMarkedFourierCoefficient
        (Ns n) (Ps n) h a b) atTop (𝓝 0) := by
  have hhR : (h : ℝ) ≠ 0 := by exact_mod_cast hh
  let C : ℝ := 1 / (Real.pi * |(h : ℝ)|)
  have hC : Tendsto (fun _ : ℕ ↦ C) atTop (𝓝 C) := tendsto_const_nhds
  have hupperRaw := hC.mul hsublinear
  have hupper : Tendsto
      (fun n : ℕ ↦ (Ps n : ℝ) /
        (Real.pi * |(h : ℝ)| * (Ns n : ℝ))) atTop (𝓝 0) := by
    have heq :
        (fun n : ℕ ↦ C * ((Ps n : ℝ) / (Ns n : ℝ))) =ᶠ[atTop]
          (fun n : ℕ ↦ (Ps n : ℝ) /
            (Real.pi * |(h : ℝ)| * (Ns n : ℝ))) := by
      filter_upwards [hNs] with n hn
      have hNne : (Ns n : ℝ) ≠ 0 := by positivity
      dsimp [C]
      field_simp
    have htarget := hupperRaw.congr' heq
    simpa only [mul_zero] using! htarget
  rw [tendsto_zero_iff_norm_tendsto_zero]
  apply squeeze_zero'
  · filter_upwards with n
    exact norm_nonneg _
  · filter_upwards [hNs, hsmall] with n hn hs
    exact norm_primitiveMarkedFourierCoefficient_le
      hn hh hab hA ha hb hs
  · exact hupper

/-! ## Exact weighted transfer to the actual Gauss-prefix process -/

/-- The unique positive word of depth `n` when it exists, and a harmless
default on the terminating exceptional set. -/
def selectedGaussPrefixWord (n : ℕ) (x : ℝ) : PositiveDigitWord n :=
  if hx : x ∈ positivePrefixDomain n then
    Classical.choose (existsUnique_mem_positivePrefixCylinder hx)
  else defaultPositiveDigitWord n

theorem selectedGaussPrefixWord_mem
    {n : ℕ} {x : ℝ} (hx : x ∈ positivePrefixDomain n) :
    x ∈ positivePrefixCylinder n (selectedGaussPrefixWord n x) := by
  rw [selectedGaussPrefixWord, dif_pos hx]
  exact (Classical.choose_spec (existsUnique_mem_positivePrefixCylinder hx)).1

theorem selectedGaussPrefixWord_eq_of_mem
    {n : ℕ} {x : ℝ} (w : PositiveDigitWord n)
    (hw : x ∈ positivePrefixCylinder n w) :
    selectedGaussPrefixWord n x = w := by
  have hdomain : x ∈ positivePrefixDomain n := mem_iUnion.mpr ⟨w, hw⟩
  rw [selectedGaussPrefixWord, dif_pos hdomain]
  exact ((Classical.choose_spec
    (existsUnique_mem_positivePrefixCylinder hdomain)).2 w hw).symm

/-- Literal nonzero Fourier sum over primitive denominators `2 ≤ p ≤ P`. -/
def markedResonanceFourierSum
    (N P : ℕ) (B : Set (ℝ × ℝ × ℝ)) (h : ℤ) (x : ℝ) : ℂ :=
  ∑ p ∈ Finset.Icc 2 P,
    if IsPrimitiveResonance p x ∧ markedResonancePoint N p x ∈ B then
      paperExp ((h : ℝ) * resonanceTorusCoordinate N p x)
    else 0

/-- The same weighted sum indexed by actual continued-fraction depths.  The
event is `gaussPrefixMarkedEvent`; the selected word is equal to its unique
witness on that event. -/
def gaussPrefixMarkedFourierSum
    (N P : ℕ) (B : Set (ℝ × ℝ × ℝ)) (h : ℤ) (x : ℝ) : ℂ :=
  ∑ n ∈ Finset.Icc 0 N,
    if x ∈ gaussPrefixMarkedEvent N B n ∧
        cfTerminalDenominator (selectedGaussPrefixWord n x).1 ∈
          Finset.Icc 2 P then
      paperExp ((h : ℝ) *
        (gaussPrefixMarkedPoint N n (selectedGaussPrefixWord n x) x).2.2)
    else 0

/-- Weighted version of the finite denominator/depth bijection.  This is
the formal statement that the Fourier coefficient above belongs to the
actual Gauss-prefix marked process. -/
theorem markedResonanceFourierSum_eq_gaussPrefix
    {N P : ℕ} {x ε A : ℝ} {B : Set (ℝ × ℝ × ℝ)} (h : ℤ)
    (hN : 2 ≤ N) (hP : P ≤ N) (hε : 0 ≤ ε)
    (hlog : 2 * A < Real.log (N : ℝ))
    (hB : B ⊆ compactAnnularMarkedRegion ε A)
    (hx : x ∈ Ioo (0 : ℝ) 1)
    (hnonterm : ∀ k : ℕ, (gaussMap^[k]) x ≠ 0) :
    markedResonanceFourierSum N P B h x =
      gaussPrefixMarkedFourierSum N P B h x := by
  classical
  let S : Finset ℕ := (Finset.Icc 2 P).filter fun p ↦
    IsPrimitiveResonance p x ∧ markedResonancePoint N p x ∈ B
  let T : Finset ℕ := (Finset.Icc 0 N).filter fun n ↦
    x ∈ gaussPrefixMarkedEvent N B n ∧
      cfTerminalDenominator (selectedGaussPrefixWord n x).1 ∈ Finset.Icc 2 P
  have hmarked : markedResonanceFourierSum N P B h x =
      ∑ p ∈ S, paperExp ((h : ℝ) * resonanceTorusCoordinate N p x) := by
    unfold markedResonanceFourierSum S
    rw [Finset.sum_filter]
  have hprefix : gaussPrefixMarkedFourierSum N P B h x =
      ∑ n ∈ T, paperExp ((h : ℝ) *
        (gaussPrefixMarkedPoint N n (selectedGaussPrefixWord n x) x).2.2) := by
    unfold gaussPrefixMarkedFourierSum T
    rw [Finset.sum_filter]
  have hforward : ∀ p ∈ S, ∃ n ∈ T,
      ResonanceGaussDepthRelation N B x p n := by
    intro p hpS
    have hpData := Finset.mem_filter.mp hpS
    have hpBounds := Finset.mem_Icc.mp hpData.1
    have hpN : p ∈ Finset.Icc 1 N :=
      Finset.mem_Icc.mpr ⟨by omega, hpBounds.2.trans hP⟩
    obtain ⟨n, hn, hrel⟩ := exists_depth_relation_of_marked
      hN hε hlog hB hx hnonterm hpN hpData.2.1 hpData.2.2
    obtain ⟨w, hw, hpDen, htheta, hpoint⟩ := hrel
    have hword : selectedGaussPrefixWord n x = w :=
      selectedGaussPrefixWord_eq_of_mem w hw
    have hevent : x ∈ gaussPrefixMarkedEvent N B n := by
      apply mem_gaussPrefixMarkedEvent_iff.mpr
      refine ⟨w, hw, ?_, htheta, hpoint⟩
      rw [← hpDen]
      exact hpBounds.2.trans hP
    have hdenSelected :
        cfTerminalDenominator (selectedGaussPrefixWord n x).1 ∈
          Finset.Icc 2 P := by
      rw [hword, ← hpDen]
      exact hpData.1
    exact ⟨n, Finset.mem_filter.mpr ⟨hn, hevent, hdenSelected⟩,
      ⟨w, hw, hpDen, htheta, hpoint⟩⟩
  let depth : ∀ p ∈ S, ℕ := fun p hpS ↦
    Classical.choose (hforward p hpS)
  have depth_mem (p : ℕ) (hpS : p ∈ S) : depth p hpS ∈ T :=
    (Classical.choose_spec (hforward p hpS)).1
  have depth_rel (p : ℕ) (hpS : p ∈ S) :
      ResonanceGaussDepthRelation N B x p (depth p hpS) :=
    (Classical.choose_spec (hforward p hpS)).2
  rw [hmarked, hprefix]
  apply Finset.sum_bij (s := S) (t := T) depth
  · exact depth_mem
  · intro p hpS q hqS heq
    have hqRel : ResonanceGaussDepthRelation N B x q (depth p hpS) := by
      rw [heq]
      exact depth_rel q hqS
    exact ResonanceGaussDepthRelation.left_unique (depth_rel p hpS) hqRel
  · intro n hnT
    have hndata := Finset.mem_filter.mp hnT
    obtain ⟨p, hpN, hrel, hprim, hpoint⟩ :=
      exists_denominator_relation_of_mem_gaussPrefixMarkedEvent
        hx hnonterm hndata.2.1
    have hrelSaved := hrel
    obtain ⟨w, hw, hpDen, _htheta, _hpointGauss⟩ := hrel
    have hword : selectedGaussPrefixWord n x = w :=
      selectedGaussPrefixWord_eq_of_mem w hw
    have hpRange : p ∈ Finset.Icc 2 P := by
      rw [hword, ← hpDen] at hndata
      exact hndata.2.2
    have hpS : p ∈ S :=
      Finset.mem_filter.mpr ⟨hpRange, hprim, hpoint⟩
    refine ⟨p, hpS, ?_⟩
    exact ResonanceGaussDepthRelation.right_unique
      hx hnonterm (depth_rel p hpS) hrelSaved
  · intro p hpS
    obtain ⟨w, hw, hpDen, htheta, _hpoint⟩ := depth_rel p hpS
    have hword : selectedGaussPrefixWord (depth p hpS) x = w :=
      selectedGaussPrefixWord_eq_of_mem w hw
    have hex : x ∉ gaussPrefixExceptional (depth p hpS + 1) :=
      not_mem_gaussPrefixExceptional_of_nonterminating hx hnonterm _
    have hpointEq :=
      markedResonancePoint_terminalDenominator_eq_gaussPrefixMarkedPoint
        (N := N) w hx hex hw htheta
    have hpPointEq : markedResonancePoint N p x =
        gaussPrefixMarkedPoint N (depth p hpS) w x := by
      calc
        markedResonancePoint N p x =
            markedResonancePoint N (cfTerminalDenominator w.1) x := by
          exact congrArg (fun r : ℕ ↦ markedResonancePoint N r x) hpDen
        _ = gaussPrefixMarkedPoint N (depth p hpS) w x := hpointEq
    have htorusEq : resonanceTorusCoordinate N p x =
        (gaussPrefixMarkedPoint N (depth p hpS)
          (selectedGaussPrefixWord (depth p hpS) x) x).2.2 := by
      calc
        resonanceTorusCoordinate N p x =
            (markedResonancePoint N p x).2.2 := rfl
        _ = (gaussPrefixMarkedPoint N (depth p hpS) w x).2.2 :=
          congrArg (fun z : ℝ × ℝ × ℝ ↦ z.2.2) hpPointEq
        _ = (gaussPrefixMarkedPoint N (depth p hpS)
              (selectedGaussPrefixWord (depth p hpS) x) x).2.2 := by
          rw [hword]
    rw [htorusEq]

/-- The compact marked region retaining all time and torus coordinates and
one signed-coordinate interval. -/
def compactValueMarkedRegion (a b : ℝ) : Set (ℝ × ℝ × ℝ) :=
  Icc (0 : ℝ) 1 ×ˢ (Icc a b ×ˢ Icc (0 : ℝ) 1)

theorem measurableSet_compactValueMarkedRegion (a b : ℝ) :
    MeasurableSet (compactValueMarkedRegion a b) :=
  measurableSet_Icc.prod (measurableSet_Icc.prod measurableSet_Icc)

theorem compactValueMarkedRegion_subset_compactAnnular
    {a b A : ℝ} (ha : |a| ≤ A) (hb : |b| ≤ A) :
    compactValueMarkedRegion a b ⊆ compactAnnularMarkedRegion 0 A := by
  rintro z ⟨htime, hvalue, htorus⟩
  refine ⟨htime, ?_, htorus⟩
  rw [mem_signedAnnulus_iff_abs (show (0 : ℝ) ≤ 0 by rfl)]
  refine ⟨abs_nonneg _, ?_⟩
  apply abs_le.mpr
  have halower := (abs_le.mp ha).1
  have hbupper := (abs_le.mp hb).2
  exact ⟨halower.trans hvalue.1, hvalue.2.trans hbupper⟩

theorem markedResonancePoint_mem_compactValueMarkedRegion_iff
    {N P p : ℕ} (hN : 2 ≤ N) (hP : P ≤ N)
    (hp : p ∈ Finset.Icc 2 P) {a b α : ℝ} :
    markedResonancePoint N p α ∈ compactValueMarkedRegion a b ↔
      scaledResonanceCoordinate N p α ∈ Icc a b := by
  have hpBounds := Finset.mem_Icc.mp hp
  have hpN : p ∈ Finset.Icc 1 N :=
    Finset.mem_Icc.mpr ⟨by omega, hpBounds.2.trans hP⟩
  have htime := resonanceTimeCoordinate_mem_Icc hN hpN
  have htorus := resonanceTorusCoordinate_mem_Ico N p α
  unfold compactValueMarkedRegion markedResonancePoint
  simp only [mem_prod]
  constructor
  · exact fun hz ↦ hz.2.1
  · intro hx
    exact ⟨htime, hx, htorus.1, htorus.2.le⟩

/-- The literal denominator Fourier sum for the compact value region is
exactly the sum of the one-denominator integrands used above. -/
theorem markedResonanceFourierSum_compactValue_eq
    {N P : ℕ} (h : ℤ) (a b x : ℝ)
    (hN : 2 ≤ N) (hP : P ≤ N) :
    markedResonanceFourierSum N P (compactValueMarkedRegion a b) h x =
      ∑ p ∈ Finset.Icc 2 P,
        primitiveMarkedFourierIntegrand N p h a b x := by
  unfold markedResonanceFourierSum primitiveMarkedFourierIntegrand
  apply Finset.sum_congr rfl
  intro p hp
  rw [markedResonancePoint_mem_compactValueMarkedRegion_iff hN hP hp]
  by_cases hevent : IsPrimitiveResonance p x ∧
      scaledResonanceCoordinate N p x ∈ Icc a b <;> simp [hevent]

/-- The actual Gauss-prefix first-factorial Fourier coefficient. -/
def gaussPrefixMarkedFourierCoefficient
    (N P : ℕ) (h : ℤ) (a b : ℝ) : ℂ :=
  ∫ x, gaussPrefixMarkedFourierSum N P
    (compactValueMarkedRegion a b) h x ∂uniform01Measure

/-- Exact equality of the literal primitive-resonance coefficient and the
actual Gauss-prefix coefficient, away from the terminating null set. -/
theorem primitiveMarkedFourierCoefficient_eq_gaussPrefix
    {N P : ℕ} {h : ℤ} {a b A : ℝ}
    (hN : 2 ≤ N) (hP : P ≤ N)
    (ha : |a| ≤ A) (hb : |b| ≤ A)
    (hlog : 2 * A < Real.log (N : ℝ)) :
    primitiveMarkedFourierCoefficient N P h a b =
      gaussPrefixMarkedFourierCoefficient N P h a b := by
  unfold primitiveMarkedFourierCoefficient gaussPrefixMarkedFourierCoefficient
  apply integral_congr_ae
  filter_upwards [ae_nonterminating_uniform01] with x hx
  rw [← markedResonanceFourierSum_compactValue_eq h a b x hN hP]
  exact markedResonanceFourierSum_eq_gaussPrefix
    h hN hP (show (0 : ℝ) ≤ 0 by rfl) hlog
    (compactValueMarkedRegion_subset_compactAnnular ha hb) hx.1 hx.2

/-- Final order-one theorem in Gauss-prefix notation: every nonzero torus
character vanishes on a compact signed-coordinate window and a sublinear
denominator range. -/
theorem tendsto_gaussPrefixMarkedFourierCoefficient_zero
    (Ns Ps : ℕ → ℕ) {h : ℤ} {a b A : ℝ}
    (hh : h ≠ 0) (hab : a ≤ b) (hA : 0 ≤ A)
    (ha : |a| ≤ A) (hb : |b| ≤ A)
    (hNs : ∀ᶠ n : ℕ in atTop, 2 ≤ Ns n)
    (hPs : ∀ᶠ n : ℕ in atTop, Ps n ≤ Ns n)
    (hlog : ∀ᶠ n : ℕ in atTop,
      2 * A < Real.log (Ns n : ℝ))
    (hsmall : ∀ᶠ n : ℕ in atTop,
      A / Real.log (Ns n : ℝ) < (1 : ℝ) / 2)
    (hsublinear : Tendsto
      (fun n : ℕ ↦ (Ps n : ℝ) / (Ns n : ℝ)) atTop (𝓝 0)) :
    Tendsto
      (fun n : ℕ ↦ gaussPrefixMarkedFourierCoefficient
        (Ns n) (Ps n) h a b) atTop (𝓝 0) := by
  have hprimitive := tendsto_primitiveMarkedFourierCoefficient_zero
    Ns Ps hh hab hA ha hb hNs hsmall hsublinear
  apply hprimitive.congr'
  filter_upwards [hNs, hPs, hlog] with n hn hpn hln
  exact primitiveMarkedFourierCoefficient_eq_gaussPrefix
    hn hpn ha hb hln

end

end Erdos1002
