import ErdosProblems.Erdos1002.ProbabilityFoundations
import ErdosProblems.Erdos1002.RamanujanSums
import ErdosProblems.Erdos1002.Resonances
import Mathlib.NumberTheory.Harmonic.Bounds

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Measure bounds for primitive resonance cells

The finite-shot argument repeatedly uses a union bound over reduced rational
cells.  This file proves the bound directly from interval length, including
the endpoint and nearest-integer conventions.
-/

open MeasureTheory Set
open scoped BigOperators ENNReal

namespace Erdos1002

noncomputable section

/-- A real affine band has its expected length. -/
theorem volumeReal_affine_band_le (p : ℕ) (q : ℤ) (ε : ℝ)
    (hp : 0 < p) (hε : 0 ≤ ε) :
    volume.real {α : ℝ | |(p : ℝ) * α - (q : ℝ)| ≤ ε} ≤
      2 * ε / (p : ℝ) := by
  have hpR : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hp
  let a : ℝ := ((q : ℝ) - ε) / (p : ℝ)
  let b : ℝ := ((q : ℝ) + ε) / (p : ℝ)
  have hsub : {α : ℝ | |(p : ℝ) * α - (q : ℝ)| ≤ ε} ⊆ Icc a b := by
    intro α hα
    rw [mem_setOf_eq, abs_le] at hα
    constructor
    · dsimp [a]
      rw [div_le_iff₀ hpR]
      linarith
    · dsimp [b]
      rw [le_div_iff₀ hpR]
      linarith
  calc
    volume.real {α : ℝ | |(p : ℝ) * α - (q : ℝ)| ≤ ε} ≤
        volume.real (Icc a b) := measureReal_mono hsub (by
          rw [Real.volume_Icc]
          exact ENNReal.ofReal_ne_top)
    _ = b - a := by
      have hba : 0 ≤ b - a := by
        dsimp [a, b]
        rw [show ((q : ℝ) + ε) / (p : ℝ) -
            ((q : ℝ) - ε) / (p : ℝ) = 2 * ε / (p : ℝ) by
          field_simp
          ring]
        exact div_nonneg (mul_nonneg (by norm_num) hε) hpR.le
      rw [measureReal_def, Real.volume_Icc, ENNReal.toReal_ofReal hba]
    _ = 2 * ε / (p : ℝ) := by
      dsimp [a, b]
      field_simp
      ring

/-- The primitive resonance event with a fixed denominator and displacement
window. -/
def primitiveResonanceBand (p : ℕ) (ε : ℝ) : Set ℝ :=
  {α | α ∈ Ioo (0 : ℝ) 1 ∧ IsPrimitiveResonance p α ∧
    |resonanceDelta p α| ≤ ε}

theorem primitiveResonanceBand_measurable (p : ℕ) (ε : ℝ) :
    MeasurableSet (primitiveResonanceBand p ε) := by
  exact measurableSet_Ioo.inter <|
    (measurableSet_isPrimitiveResonance p).inter <|
      measurableSet_le (measurable_resonanceDelta p).abs measurable_const

theorem resonanceNumerator_nat_lt {p : ℕ} (hp : 2 ≤ p) {α : ℝ}
    (hα : α ∈ Ioo (0 : ℝ) 1) (hprim : IsPrimitiveResonance p α) :
    (resonanceNumerator p α).natAbs < p := by
  obtain ⟨hq0, hqp⟩ := resonanceNumerator_bounds_of_mem_unitInterval p hα
  have hqnat : ((resonanceNumerator p α).natAbs : ℤ) =
      resonanceNumerator p α := by
    rw [Int.natCast_natAbs, abs_of_nonneg hq0]
  have hle : (resonanceNumerator p α).natAbs ≤ p := by
    have hz : ((resonanceNumerator p α).natAbs : ℤ) ≤ (p : ℤ) :=
      hqnat.le.trans hqp
    exact_mod_cast hz
  apply lt_of_le_of_ne hle
  intro heq
  change Nat.Coprime (resonanceNumerator p α).natAbs p at hprim
  have hcop : Nat.Coprime p p := by
    rw [heq] at hprim
    exact hprim
  have hp1 : p = 1 := by simpa using! hcop
  omega

theorem resonanceNumerator_nat_mem_reducedResidues {p : ℕ} (hp : 2 ≤ p)
    {α : ℝ} (hα : α ∈ Ioo (0 : ℝ) 1)
    (hprim : IsPrimitiveResonance p α) :
    (resonanceNumerator p α).natAbs ∈ reducedResidues p := by
  rw [reducedResidues, Finset.mem_filter, Finset.mem_range]
  exact ⟨resonanceNumerator_nat_lt hp hα hprim, hprim⟩

/-- A primitive nearest cell is contained in the union of the reduced affine
bands. -/
theorem primitiveResonanceBand_subset_reduced_union {p : ℕ} (hp : 2 ≤ p)
    (ε : ℝ) :
    primitiveResonanceBand p ε ⊆
      ⋃ q ∈ reducedResidues p,
        {α : ℝ | |(p : ℝ) * α - (q : ℝ)| ≤ ε} := by
  intro α hα
  rcases hα with ⟨hunit, hprim, hδ⟩
  let q : ℕ := (resonanceNumerator p α).natAbs
  have hqmem : q ∈ reducedResidues p :=
    resonanceNumerator_nat_mem_reducedResidues hp hunit hprim
  rw [mem_iUnion]
  refine ⟨q, ?_⟩
  rw [mem_iUnion]
  refine ⟨hqmem, ?_⟩
  have hq0 := (resonanceNumerator_bounds_of_mem_unitInterval p hunit).1
  have hcast : (q : ℤ) = resonanceNumerator p α := by
    dsimp [q]
    rw [Int.natCast_natAbs, abs_of_nonneg hq0]
  change |(p : ℝ) * α - (q : ℝ)| ≤ ε
  rw [show (q : ℝ) = (resonanceNumerator p α : ℝ) by exact_mod_cast hcast]
  exact hδ

/-- Exact reduced-cell union bound. -/
theorem volumeReal_primitiveResonanceBand_le {p : ℕ} (hp : 2 ≤ p)
    {ε : ℝ} (hε : 0 ≤ ε) :
    volume.real (primitiveResonanceBand p ε) ≤
      (Nat.totient p : ℝ) * (2 * ε / (p : ℝ)) := by
  let cell : ℕ → Set ℝ := fun q ↦
    {α : ℝ | |(p : ℝ) * α - (q : ℝ)| ≤ ε}
  have hcell_ne_top (q : ℕ) : volume (cell q) ≠ ∞ := by
    have hpR : (0 : ℝ) < (p : ℝ) := by exact_mod_cast (by omega : 0 < p)
    let a : ℝ := ((q : ℝ) - ε) / (p : ℝ)
    let b : ℝ := ((q : ℝ) + ε) / (p : ℝ)
    have hsub : cell q ⊆ Icc a b := by
      intro α hα
      dsimp [cell] at hα
      rw [abs_le] at hα
      constructor
      · dsimp [a]
        rw [div_le_iff₀ hpR]
        linarith
      · dsimp [b]
        rw [le_div_iff₀ hpR]
        linarith
    exact measure_ne_top_of_subset hsub (by
      rw [Real.volume_Icc]
      exact ENNReal.ofReal_ne_top)
  have hunion_ne_top : volume (⋃ q ∈ reducedResidues p, cell q) ≠ ∞ := by
    have hle := measure_biUnion_finset_le (μ := volume) (reducedResidues p) cell
    have hsum : (∑ q ∈ reducedResidues p, volume (cell q)) ≠ ∞ := by
      rw [ENNReal.sum_ne_top]
      exact fun q _hq ↦ hcell_ne_top q
    exact ne_of_lt (lt_of_le_of_lt hle hsum.lt_top)
  calc
    volume.real (primitiveResonanceBand p ε) ≤
        volume.real (⋃ q ∈ reducedResidues p, cell q) :=
      measureReal_mono (primitiveResonanceBand_subset_reduced_union hp ε) hunion_ne_top
    _ ≤ ∑ q ∈ reducedResidues p, volume.real (cell q) :=
      measureReal_biUnion_finset_le (reducedResidues p) cell
    _ ≤ ∑ _q ∈ reducedResidues p, (2 * ε / (p : ℝ)) := by
      gcongr with q hq
      exact volumeReal_affine_band_le p (q : ℤ) ε (by omega) hε
    _ = (Nat.totient p : ℝ) * (2 * ε / (p : ℝ)) := by
      rw [Finset.sum_const, nsmul_eq_mul, card_reducedResidues]

/-- The window expressed in the scaled coordinate `(log N) p δ_p`. -/
def scaledPrimitiveResonanceBand (N p : ℕ) (A : ℝ) : Set ℝ :=
  {α | α ∈ Ioo (0 : ℝ) 1 ∧ IsPrimitiveResonance p α ∧
    |Real.log (N : ℝ) * (p : ℝ) * resonanceDelta p α| ≤ A}

theorem scaledPrimitiveResonanceBand_eq (N p : ℕ) (A : ℝ)
    (hN : 2 ≤ N) (hp : 0 < p) :
    scaledPrimitiveResonanceBand N p A =
      primitiveResonanceBand p (A / (Real.log (N : ℝ) * (p : ℝ))) := by
  have hlog : 0 < Real.log (N : ℝ) := Real.log_pos (by exact_mod_cast hN)
  have hpR : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hp
  have hc : 0 < Real.log (N : ℝ) * (p : ℝ) := mul_pos hlog hpR
  ext α
  simp only [scaledPrimitiveResonanceBand, primitiveResonanceBand, mem_setOf_eq,
    and_congr_right_iff]
  intro _hunit _hprim
  rw [show Real.log (N : ℝ) * (p : ℝ) * resonanceDelta p α =
      (Real.log (N : ℝ) * (p : ℝ)) * resonanceDelta p α by ring,
    abs_mul, abs_of_pos hc, le_div_iff₀ hc]
  simp [mul_comm]

theorem volumeReal_scaledPrimitiveResonanceBand_le
    {N p : ℕ} (hN : 2 ≤ N) (hp : 2 ≤ p) {A : ℝ} (hA : 0 ≤ A) :
    volume.real (scaledPrimitiveResonanceBand N p A) ≤
      (2 * A / Real.log (N : ℝ)) *
        ((Nat.totient p : ℝ) / (p : ℝ) ^ 2) := by
  have hlog : 0 < Real.log (N : ℝ) := Real.log_pos (by exact_mod_cast hN)
  have hpR : (0 : ℝ) < (p : ℝ) := by positivity
  rw [scaledPrimitiveResonanceBand_eq N p A hN (by omega)]
  refine (volumeReal_primitiveResonanceBand_le hp
    (div_nonneg hA (mul_pos hlog hpR).le)).trans_eq ?_
  field_simp

/-- Union bound over any finite set of denominators at least two. -/
theorem volumeReal_iUnion_scaledPrimitiveResonanceBand_le
    {N : ℕ} (hN : 2 ≤ N) (P : Finset ℕ)
    (hP : ∀ p ∈ P, 2 ≤ p) {A : ℝ} (hA : 0 ≤ A) :
    volume.real (⋃ p ∈ P, scaledPrimitiveResonanceBand N p A) ≤
      (2 * A / Real.log (N : ℝ)) *
        ∑ p ∈ P, ((Nat.totient p : ℝ) / (p : ℝ) ^ 2) := by
  calc
    volume.real (⋃ p ∈ P, scaledPrimitiveResonanceBand N p A) ≤
        ∑ p ∈ P, volume.real (scaledPrimitiveResonanceBand N p A) :=
      measureReal_biUnion_finset_le P (fun p ↦ scaledPrimitiveResonanceBand N p A)
    _ ≤ ∑ p ∈ P, (2 * A / Real.log (N : ℝ)) *
          ((Nat.totient p : ℝ) / (p : ℝ) ^ 2) := by
      gcongr with p hp
      exact volumeReal_scaledPrimitiveResonanceBand_le hN (hP p hp) hA
    _ = (2 * A / Real.log (N : ℝ)) *
        ∑ p ∈ P, ((Nat.totient p : ℝ) / (p : ℝ) ^ 2) := by
      rw [Finset.mul_sum]

theorem totient_le_self (p : ℕ) : Nat.totient p ≤ p := by
  calc
    Nat.totient p = (reducedResidues p).card := (card_reducedResidues p).symm
    _ ≤ (Finset.range p).card := Finset.card_le_card (by
      exact Finset.filter_subset (fun a ↦ Nat.Coprime a p) (Finset.range p))
    _ = p := Finset.card_range p

/-- The elementary harmonic majorant needed for the small-window union
bound; no average-order theorem for the totient is required here. -/
theorem sum_totient_div_sq_Icc_le_harmonic (N : ℕ) :
    (∑ p ∈ Finset.Icc 2 N,
      ((Nat.totient p : ℝ) / (p : ℝ) ^ 2)) ≤ (harmonic N : ℝ) := by
  calc
    (∑ p ∈ Finset.Icc 2 N,
        ((Nat.totient p : ℝ) / (p : ℝ) ^ 2)) ≤
        ∑ p ∈ Finset.Icc 2 N, (1 / (p : ℝ)) := by
      apply Finset.sum_le_sum
      intro p hp
      have hp0 : (p : ℝ) ≠ 0 := by
        have : 2 ≤ p := (Finset.mem_Icc.mp hp).1
        positivity
      have hφ : (Nat.totient p : ℝ) ≤ (p : ℝ) := by
        exact_mod_cast totient_le_self p
      calc
        (Nat.totient p : ℝ) / (p : ℝ) ^ 2 ≤
            (p : ℝ) / (p : ℝ) ^ 2 :=
          div_le_div_of_nonneg_right hφ (sq_nonneg (p : ℝ))
        _ = 1 / (p : ℝ) := by field_simp
    _ ≤ ∑ p ∈ Finset.Icc 1 N, (1 / (p : ℝ)) := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro p hp
        rw [Finset.mem_Icc] at hp ⊢
        omega
      · intro p _hp _hnot
        positivity
    _ = (harmonic N : ℝ) := by
      simp only [harmonic_eq_sum_Icc, Rat.cast_sum, Rat.cast_inv,
        Rat.cast_natCast, one_div]

theorem volumeReal_scaledResonanceUnion_Icc_le
    {N : ℕ} (hN : 2 ≤ N) {A : ℝ} (hA : 0 ≤ A) :
    volume.real
        (⋃ p ∈ Finset.Icc 2 N, scaledPrimitiveResonanceBand N p A) ≤
      (2 * A / Real.log (N : ℝ)) * (1 + Real.log (N : ℝ)) := by
  have hfactor : 0 ≤ 2 * A / Real.log (N : ℝ) := by
    have : 0 < Real.log (N : ℝ) := Real.log_pos (by exact_mod_cast hN)
    positivity
  calc
    volume.real
        (⋃ p ∈ Finset.Icc 2 N, scaledPrimitiveResonanceBand N p A) ≤
      (2 * A / Real.log (N : ℝ)) *
        ∑ p ∈ Finset.Icc 2 N,
          ((Nat.totient p : ℝ) / (p : ℝ) ^ 2) := by
      apply volumeReal_iUnion_scaledPrimitiveResonanceBand_le hN
      · intro p hp
        exact (Finset.mem_Icc.mp hp).1
      · exact hA
    _ ≤ (2 * A / Real.log (N : ℝ)) * (harmonic N : ℝ) := by
      gcongr
      exact sum_totient_div_sq_Icc_le_harmonic N
    _ ≤ (2 * A / Real.log (N : ℝ)) * (1 + Real.log (N : ℝ)) := by
      gcongr
      exact harmonic_le_one_add_log N

/-- The exceptional denominator `p = 1` lies in one of the two endpoint
nearest-integer cells.  The deliberately coarse factor four is enough for
endpoint restoration and keeps both half-cell conventions explicit. -/
theorem volumeReal_primitiveResonanceBand_one_le {A : ℝ} (hA : 0 ≤ A) :
    volume.real (primitiveResonanceBand 1 A) ≤ 4 * A := by
  let C₀ : Set ℝ := {α | |(1 : ℝ) * α - (0 : ℝ)| ≤ A}
  let C₁ : Set ℝ := {α | |(1 : ℝ) * α - (1 : ℝ)| ≤ A}
  have hsub : primitiveResonanceBand 1 A ⊆ C₀ ∪ C₁ := by
    intro α hα
    rcases hα with ⟨hunit, _hprim, hδ⟩
    obtain ⟨hq0, hq1⟩ :=
      resonanceNumerator_bounds_of_mem_unitInterval 1 hunit
    have hq : resonanceNumerator 1 α = 0 ∨ resonanceNumerator 1 α = 1 := by
      omega
    rcases hq with hq | hq
    · left
      change |(1 : ℝ) * α - (0 : ℝ)| ≤ A
      simpa [resonanceDelta, hq] using! hδ
    · right
      change |(1 : ℝ) * α - (1 : ℝ)| ≤ A
      simpa [resonanceDelta, hq] using! hδ
  have hfinite : volume (C₀ ∪ C₁) ≠ ∞ := by
    have h₀ : volume C₀ ≠ ∞ := by
      have hsub₀ : C₀ ⊆ Icc (-A) A := by
        intro α hα
        change |(1 : ℝ) * α - (0 : ℝ)| ≤ A at hα
        simpa [abs_le] using! hα
      exact measure_ne_top_of_subset hsub₀ (by
        rw [Real.volume_Icc]
        exact ENNReal.ofReal_ne_top)
    have h₁ : volume C₁ ≠ ∞ := by
      have hsub₁ : C₁ ⊆ Icc (1 - A) (1 + A) := by
        intro α hα
        change |(1 : ℝ) * α - (1 : ℝ)| ≤ A at hα
        rw [abs_le] at hα
        constructor <;> linarith
      exact measure_ne_top_of_subset hsub₁ (by
        rw [Real.volume_Icc]
        exact ENNReal.ofReal_ne_top)
    exact measure_union_lt_top h₀.lt_top h₁.lt_top |>.ne
  calc
    volume.real (primitiveResonanceBand 1 A) ≤ volume.real (C₀ ∪ C₁) :=
      measureReal_mono hsub hfinite
    _ ≤ volume.real C₀ + volume.real C₁ := measureReal_union_le C₀ C₁
    _ ≤ (2 * A / (1 : ℝ)) + (2 * A / (1 : ℝ)) := by
      gcongr
      · simpa [C₀] using! volumeReal_affine_band_le 1 0 A (by omega) hA
      · simpa [C₁] using! volumeReal_affine_band_le 1 1 A (by omega) hA
    _ = 4 * A := by ring

theorem volumeReal_scaledPrimitiveResonanceBand_one_le
    {N : ℕ} (hN : 2 ≤ N) {A : ℝ} (hA : 0 ≤ A) :
    volume.real (scaledPrimitiveResonanceBand N 1 A) ≤
      4 * A / Real.log (N : ℝ) := by
  have hlog : 0 < Real.log (N : ℝ) :=
    Real.log_pos (by exact_mod_cast hN)
  rw [scaledPrimitiveResonanceBand_eq N 1 A hN (by omega)]
  refine (volumeReal_primitiveResonanceBand_one_le
    (div_nonneg hA (by positivity))).trans_eq ?_
  norm_num
  ring

/-- Complete coarse small-window union bound, now including `p = 1`. -/
theorem volumeReal_scaledResonanceUnion_Icc_one_le
    {N : ℕ} (hN : 2 ≤ N) {A : ℝ} (hA : 0 ≤ A) :
    volume.real
        (⋃ p ∈ Finset.Icc 1 N, scaledPrimitiveResonanceBand N p A) ≤
      4 * A / Real.log (N : ℝ) +
        (2 * A / Real.log (N : ℝ)) * (1 + Real.log (N : ℝ)) := by
  have hIcc : Finset.Icc 1 N = insert 1 (Finset.Icc 2 N) := by
    ext p
    simp only [Finset.mem_Icc, Finset.mem_insert]
    omega
  rw [hIcc, Finset.set_biUnion_insert]
  calc
    volume.real
        (scaledPrimitiveResonanceBand N 1 A ∪
          ⋃ p ∈ Finset.Icc 2 N, scaledPrimitiveResonanceBand N p A) ≤
        volume.real (scaledPrimitiveResonanceBand N 1 A) +
          volume.real
            (⋃ p ∈ Finset.Icc 2 N, scaledPrimitiveResonanceBand N p A) :=
      measureReal_union_le _ _
    _ ≤ 4 * A / Real.log (N : ℝ) +
        (2 * A / Real.log (N : ℝ)) * (1 + Real.log (N : ℝ)) := by
      gcongr
      · exact volumeReal_scaledPrimitiveResonanceBand_one_le hN hA
      · exact volumeReal_scaledResonanceUnion_Icc_le hN hA

end

end Erdos1002
