/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos1027.DGKPriorities
import ErdosProblems.Erdos1027.DGKAnalytic

/-!
# Global finite-probability bookkeeping for the DGK argument

The fixed-edge part of the Duraj--Gutowski--Kozik proof is local.  This file
contains the remaining global bookkeeping:

* a union bound for initially monochromatic edges whose priorities are all
  below their edge-dependent high window;
* the Markov estimate for the almost-monochromatic mass;
* the union over the two final colours and all edges;
* the elementary numerical comparison which makes the sum of the three bad
  probabilities strictly smaller than one; and
* extraction of an outcome whose final Boolean colouring is proper.

Everything is phrased on finite uniform sample spaces.  The Markov and
fixed-edge interfaces are deliberately abstract, so this module does not
depend on the implementation of `almostMass` or of the greedy algorithm.
-/

open scoped BigOperators

namespace Erdos1027.DGKUnion

open Finset
open Erdos1027.FiniteExpect

attribute [local instance] Classical.propDecidable

abbrev Hypergraph (V : Type*) := Finset (Finset V)

/-- The usual Boolean weight, kept local so the bookkeeping module is
independent of the decision-tree development. -/
def booleanWeightQ {V : Type*} [DecidableEq V] (H : Hypergraph V) : ℚ :=
  ∑ e ∈ H, (2 : ℚ) ^ (-(e.card : ℤ))

noncomputable def booleanWeightR {V : Type*} [DecidableEq V] (H : Hypergraph V) : ℝ :=
  ∑ e ∈ H, (2 : ℝ) ^ (-(e.card : ℤ))

/-- DGK's doubled Boolean weight. -/
def qWeightQ {V : Type*} [DecidableEq V] (H : Hypergraph V) : ℚ :=
  2 * booleanWeightQ H

noncomputable def qWeightR {V : Type*} [DecidableEq V] (H : Hypergraph V) : ℝ :=
  2 * booleanWeightR H

/-- The fixed-edge coefficient `2^(-|e|)`.  This is definitionally the same
quantity used in `DGKFixedEdge`, but is kept local to avoid an import cycle. -/
noncomputable def invTwoPow (n : ℕ) : ℝ := ((2 : ℝ)⁻¹) ^ n

lemma qWeightR_nonneg {V : Type*} [DecidableEq V] (H : Hypergraph V) :
    0 ≤ qWeightR H := by
  unfold qWeightR booleanWeightR
  positivity

/-! ## Real indicators and finite union/Markov bounds -/

/-- The real-valued indicator of a proposition. -/
noncomputable def realIndicator (P : Prop) : ℝ := if P then 1 else 0

@[simp] lemma realIndicator_of_true {P : Prop} (hP : P) :
    realIndicator P = 1 := by
  simp [realIndicator, hP]

@[simp] lemma realIndicator_of_false {P : Prop} (hP : ¬P) :
    realIndicator P = 0 := by
  simp [realIndicator, hP]

lemma realIndicator_nonneg (P : Prop) : 0 ≤ realIndicator P := by
  unfold realIndicator
  split <;> norm_num

lemma realIndicator_eq_ratCast_indicator (P : Prop) :
    realIndicator P = (indicator P : ℝ) := by
  by_cases hP : P <;> simp [realIndicator, indicator, hP]

lemma expect_realIndicator_eq_ratCast_expect_indicator
    {Ω : Type*} [Fintype Ω] (P : Ω → Prop) :
    (𝔼 ω : Ω, realIndicator (P ω)) =
      (((𝔼 ω : Ω, indicator (P ω)) : ℚ) : ℝ) := by
  classical
  simp_rw [realIndicator_eq_ratCast_indicator]
  exact (algebraMap.coe_expect (N := ℝ) Finset.univ
    (fun ω : Ω ↦ indicator (P ω))).symm

/-- Pointwise union bound for a finite family of real indicators. -/
lemma realIndicator_biExists_le_sum {ι : Type*} (I : Finset ι) (P : ι → Prop) :
    realIndicator (∃ i ∈ I, P i) ≤ ∑ i ∈ I, realIndicator (P i) := by
  classical
  by_cases h : ∃ i ∈ I, P i
  · obtain ⟨i, hi, hPi⟩ := h
    have hExists : ∃ i ∈ I, P i := ⟨i, hi, hPi⟩
    have hone : (1 : ℝ) ≤ ∑ j ∈ I, realIndicator (P j) := by
      calc
        (1 : ℝ) = realIndicator (P i) := (realIndicator_of_true hPi).symm
        _ ≤ ∑ j ∈ I, realIndicator (P j) := by
          exact Finset.single_le_sum
            (fun j _ ↦ realIndicator_nonneg (P j)) hi
    rw [realIndicator_of_true hExists]
    exact hone
  · rw [realIndicator_of_false h]
    exact Finset.sum_nonneg fun i _ ↦ realIndicator_nonneg (P i)

/-- The finite union bound on a uniform finite sample space. -/
lemma expect_realIndicator_biExists_le_sum {Ω ι : Type*} [Fintype Ω]
    (I : Finset ι) (P : ι → Ω → Prop) :
    (𝔼 ω : Ω, realIndicator (∃ i ∈ I, P i ω)) ≤
      ∑ i ∈ I, 𝔼 ω : Ω, realIndicator (P i ω) := by
  classical
  calc
    (𝔼 ω : Ω, realIndicator (∃ i ∈ I, P i ω)) ≤
        𝔼 ω : Ω, ∑ i ∈ I, realIndicator (P i ω) :=
      Finset.expect_le_expect fun ω _ ↦
        realIndicator_biExists_le_sum I (fun i ↦ P i ω)
    _ = ∑ i ∈ I, 𝔼 ω : Ω, realIndicator (P i ω) :=
      Finset.expect_sum_comm _ _ _

/-- Markov's inequality for a nonnegative real statistic on a finite uniform
sample space. -/
lemma expect_realIndicator_threshold_le {Ω : Type*} [Fintype Ω]
    (Z : Ω → ℝ) {t : ℝ} (ht : 0 < t) (hZ : ∀ ω, 0 ≤ Z ω) :
    (𝔼 ω : Ω, realIndicator (t ≤ Z ω)) ≤ (𝔼 ω : Ω, Z ω) / t := by
  classical
  calc
    (𝔼 ω : Ω, realIndicator (t ≤ Z ω)) ≤
        𝔼 ω : Ω, Z ω / t := by
      apply Finset.expect_le_expect
      intro ω _
      by_cases h : t ≤ Z ω
      · rw [realIndicator_of_true h]
        exact (le_div_iff₀ ht).2 (by simpa using h)
      · rw [realIndicator_of_false h]
        exact div_nonneg (hZ ω) ht.le
    _ = (𝔼 ω : Ω, Z ω) / t := (Finset.expect_div _ _ _).symm

/-! ## Light edges -/

/-- A light edge is initially monochromatic and all its priorities lie below
the high interval of density `d / |e|`. -/
def LightEdge {V : Type*} {N : ℕ} (d : ℕ)
    (w : DGKPriorities.Outcome V N) (e : Finset V) : Prop :=
  DGKPriorities.InitiallyMonochromatic w e ∧
    DGKPriorities.AllLow d e.card w e

/-- Some edge of `H` is light. -/
def HasLightEdge {V : Type*} {N : ℕ} (H : Hypergraph V) (d : ℕ)
    (w : DGKPriorities.Outcome V N) : Prop :=
  ∃ e ∈ H, LightEdge d w e

/-- The probability of a fixed light edge is its doubled Boolean-weight
summand divided by at least `d+1`. -/
lemma expect_indicator_lightEdge_le
    {V : Type*} [Fintype V] [DecidableEq V]
    {N d : ℕ} (hN : 0 < N) (e : Finset V)
    (hdiv : e.card ∣ N) (hdcard : d ≤ e.card) :
    (𝔼 w : DGKPriorities.Outcome V N, indicator (LightEdge d w e)) ≤
      (2 : ℚ) ^ (1 - (e.card : ℤ)) / ((d : ℚ) + 1) := by
  classical
  have : Nonempty (Fin N) := Fin.pos_iff_nonempty.mp hN
  have hecard : 0 < e.card := Nat.pos_of_dvd_of_pos hdiv hN
  have he : e.Nonempty := Finset.card_pos.mp hecard
  rw [show (𝔼 w : DGKPriorities.Outcome V N, indicator (LightEdge d w e)) =
      (2 : ℚ) ^ (1 - (e.card : ℤ)) *
        (1 - (d : ℚ) / e.card) ^ e.card by
    simpa [LightEdge] using
      DGKPriorities.expect_indicator_initiallyMonochromatic_and_allLow
        hN hdcard hdiv e rfl he]
  have hanalyticR :
      (((1 - (d : ℚ) / e.card) ^ e.card : ℚ) : ℝ) ≤
        ((1 / ((d : ℚ) + 1) : ℚ) : ℝ) := by
    exact_mod_cast
      DGKAnalytic.one_sub_div_pow_le_inv_add_one_rat d e.card hdcard
  have htargetR :
      (((2 : ℚ) ^ (1 - (e.card : ℤ)) *
          (1 - (d : ℚ) / e.card) ^ e.card : ℚ) : ℝ) ≤
        (((2 : ℚ) ^ (1 - (e.card : ℤ)) /
          ((d : ℚ) + 1) : ℚ) : ℝ) := by
    push_cast at hanalyticR
    rw [one_div] at hanalyticR
    push_cast
    exact mul_le_mul_of_nonneg_left hanalyticR
      (zpow_nonneg (by norm_num : (0 : ℝ) ≤ 2) _)
  exact_mod_cast htargetR

private lemma two_zpow_neg_eq_zpow_one_sub (k : ℕ) :
    2 * (2 : ℚ) ^ (-(k : ℤ)) = (2 : ℚ) ^ (1 - (k : ℤ)) := by
  rw [zpow_sub₀ (by norm_num : (2 : ℚ) ≠ 0), zpow_one]
  rw [zpow_neg]
  ring

/-- Global light-edge union bound.  Notice that no common edge size is used:
only divisibility of each edge size into the finite priority denominator and
the lower bound `d ≤ |e|` are needed. -/
theorem expect_indicator_hasLightEdge_le
    {V : Type*} [Fintype V] [DecidableEq V]
    {N d : ℕ} (H : Hypergraph V) (hN : 0 < N)
    (hdiv : ∀ e ∈ H, e.card ∣ N) (hmin : ∀ e ∈ H, d ≤ e.card) :
    (𝔼 w : DGKPriorities.Outcome V N, indicator (HasLightEdge H d w)) ≤
      qWeightQ H / ((d : ℚ) + 1) := by
  classical
  have : Nonempty (Fin N) := Fin.pos_iff_nonempty.mp hN
  calc
    (𝔼 w : DGKPriorities.Outcome V N, indicator (HasLightEdge H d w)) ≤
        ∑ e ∈ H,
          𝔼 w : DGKPriorities.Outcome V N, indicator (LightEdge d w e) := by
      simpa [HasLightEdge] using
        expect_indicator_biExists_le_sum H
          (fun e w ↦ LightEdge d w e)
    _ ≤ ∑ e ∈ H,
        (2 : ℚ) ^ (1 - (e.card : ℤ)) / ((d : ℚ) + 1) := by
      exact Finset.sum_le_sum fun e he ↦
        expect_indicator_lightEdge_le hN e (hdiv e he) (hmin e he)
    _ = qWeightQ H / ((d : ℚ) + 1) := by
      unfold qWeightQ booleanWeightQ
      rw [Finset.mul_sum, Finset.sum_div]
      apply Finset.sum_congr rfl
      intro e he
      rw [two_zpow_neg_eq_zpow_one_sub]

lemma qWeightR_eq_ratCast_qWeightQ {V : Type*} [DecidableEq V]
    (H : Hypergraph V) : qWeightR H = (qWeightQ H : ℝ) := by
  unfold qWeightR qWeightQ booleanWeightR booleanWeightQ
  push_cast
  rfl

/-- Real-valued version of the global light-edge bound, ready to combine
with the real-valued fixed-edge and Markov estimates. -/
theorem expect_realIndicator_hasLightEdge_le
    {V : Type*} [Fintype V] [DecidableEq V]
    {N d : ℕ} (H : Hypergraph V) (hN : 0 < N)
    (hdiv : ∀ e ∈ H, e.card ∣ N) (hmin : ∀ e ∈ H, d ≤ e.card) :
    (𝔼 w : DGKPriorities.Outcome V N, realIndicator (HasLightEdge H d w)) ≤
      qWeightR H / ((d : ℝ) + 1) := by
  calc
    (𝔼 w : DGKPriorities.Outcome V N,
        realIndicator (HasLightEdge H d w)) =
        (((𝔼 w : DGKPriorities.Outcome V N,
          indicator (HasLightEdge H d w)) : ℚ) : ℝ) :=
      expect_realIndicator_eq_ratCast_expect_indicator
        (fun w => HasLightEdge H d w)
    _ ≤ ((qWeightQ H / ((d : ℚ) + 1) : ℚ) : ℝ) := by
      exact_mod_cast expect_indicator_hasLightEdge_le H hN hdiv hmin
    _ = qWeightR H / ((d : ℝ) + 1) := by
      rw [qWeightR_eq_ratCast_qWeightQ]
      push_cast
      rfl

lemma rat_Q_div_128Q_add_one_lt_one_over_128 (Q : ℕ) (hQ : 0 < Q) :
    (Q : ℚ) / ((128 * Q : ℕ) + 1) < (1 : ℚ) / 128 := by
  have hden : (0 : ℚ) < ((128 * Q : ℕ) + 1) := by positivity
  rw [div_lt_div_iff₀ hden (by norm_num : (0 : ℚ) < 128)]
  norm_num
  linarith

/-- With the DGK choice `d=128Q`, the total light-edge probability is
strictly less than `1/128` whenever `q(H) ≤ Q`. -/
theorem expect_indicator_hasLightEdge_lt_one_over_128
    {V : Type*} [Fintype V] [DecidableEq V]
    {N Q : ℕ} (H : Hypergraph V) (hN : 0 < N) (hQ : 0 < Q)
    (hdiv : ∀ e ∈ H, e.card ∣ N)
    (hmin : ∀ e ∈ H, 128 * Q ≤ e.card)
    (hq : qWeightQ H ≤ Q) :
    (𝔼 w : DGKPriorities.Outcome V N,
        indicator (HasLightEdge H (128 * Q) w)) < (1 : ℚ) / 128 := by
  calc
    (𝔼 w : DGKPriorities.Outcome V N,
        indicator (HasLightEdge H (128 * Q) w)) ≤
        qWeightQ H / (((128 * Q : ℕ) : ℚ) + 1) :=
      expect_indicator_hasLightEdge_le H hN hdiv hmin
    _ ≤ (Q : ℚ) / (((128 * Q : ℕ) : ℚ) + 1) := by
      exact div_le_div_of_nonneg_right (by exact_mod_cast hq) (by positivity)
    _ < (1 : ℚ) / 128 := by
      simpa only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat] using
        rat_Q_div_128Q_add_one_lt_one_over_128 Q hQ

/-- Real form of the `1/128` light-edge estimate. -/
theorem expect_realIndicator_hasLightEdge_lt_one_over_128
    {V : Type*} [Fintype V] [DecidableEq V]
    {N Q : ℕ} (H : Hypergraph V) (hN : 0 < N) (hQ : 0 < Q)
    (hdiv : ∀ e ∈ H, e.card ∣ N)
    (hmin : ∀ e ∈ H, 128 * Q ≤ e.card)
    (hq : qWeightR H ≤ Q) :
    (𝔼 w : DGKPriorities.Outcome V N,
        realIndicator (HasLightEdge H (128 * Q) w)) < (1 : ℝ) / 128 := by
  calc
    (𝔼 w : DGKPriorities.Outcome V N,
        realIndicator (HasLightEdge H (128 * Q) w)) ≤
        qWeightR H / (((128 * Q : ℕ) : ℝ) + 1) :=
      expect_realIndicator_hasLightEdge_le H hN hdiv hmin
    _ ≤ (Q : ℝ) / (((128 * Q : ℕ) : ℝ) + 1) := by
      exact div_le_div_of_nonneg_right hq (by positivity)
    _ < (1 : ℝ) / 128 := by
      have hden : (0 : ℝ) < ((128 * Q : ℕ) + 1) := by positivity
      rw [div_lt_div_iff₀ hden (by norm_num : (0 : ℝ) < 128)]
      norm_num
      linarith

/-! ## The almost-monochromatic-mass Markov estimate -/

/-- Abstract Markov interface used for `almostMass`.  In the application its
expectation is at most `2Q`; at threshold `16Q` its bad probability is at
most `1/8`. -/
theorem almostMass_markov_le_one_eighth
    {Ω : Type*} [Fintype Ω] (mass : Ω → ℝ) {Q : ℕ} (hQ : 0 < Q)
    (hmass : ∀ ω, 0 ≤ mass ω)
    (hexpect : (𝔼 ω : Ω, mass ω) ≤ 2 * (Q : ℝ)) :
    (𝔼 ω : Ω, realIndicator ((16 * Q : ℕ) ≤ mass ω)) ≤
      (1 : ℝ) / 8 := by
  have ht : (0 : ℝ) < (16 * Q : ℕ) := by positivity
  calc
    (𝔼 ω : Ω, realIndicator ((16 * Q : ℕ) ≤ mass ω)) ≤
        (𝔼 ω : Ω, mass ω) / (16 * Q : ℕ) :=
      expect_realIndicator_threshold_le mass ht hmass
    _ ≤ (2 * (Q : ℝ)) / (16 * Q : ℕ) :=
      div_le_div_of_nonneg_right hexpect ht.le
    _ = (1 : ℝ) / 8 := by
      have hQr : (Q : ℝ) ≠ 0 := by positivity
      norm_num
      field_simp [hQr] <;> norm_num

/-! ## Union over final colours and edges -/

/-- The final colouring is monochromatic on `e` in the prescribed colour. -/
def FinalMonoInColour {V Ω : Type*} (finalColour : Ω → V → Bool)
    (b : Bool) (e : Finset V) (ω : Ω) : Prop :=
  ∀ v ∈ e, finalColour ω v = b

/-- Some edge finishes monochromatic, in one of the two colours. -/
def HasFinalMonochromaticEdge {V Ω : Type*} (H : Hypergraph V)
    (finalColour : Ω → V → Bool) (ω : Ω) : Prop :=
  ∃ b : Bool, ∃ e ∈ H, FinalMonoInColour finalColour b e ω

private lemma invTwoPow_eq_zpow_neg (k : ℕ) :
    invTwoPow k = (2 : ℝ) ^ (-(k : ℤ)) := by
  simpa [invTwoPow, zpow_neg, zpow_natCast] using
    (inv_pow (2 : ℝ) k)

/-- If the fixed-edge estimate has the common error factor `K`, summing it
over both colours and every edge multiplies `K` by exactly the doubled
Boolean weight `q(H)`. -/
theorem expect_hasFinalMonochromaticEdge_le
    {V Ω : Type*} [DecidableEq V] [Fintype Ω]
    (H : Hypergraph V) (finalColour : Ω → V → Bool) (K : ℝ)
    (hfixed : ∀ b e, e ∈ H →
      (𝔼 ω : Ω, realIndicator (FinalMonoInColour finalColour b e ω)) ≤
        invTwoPow e.card * K) :
    (𝔼 ω : Ω, realIndicator (HasFinalMonochromaticEdge H finalColour ω)) ≤
      qWeightR H * K := by
  classical
  calc
    (𝔼 ω : Ω, realIndicator (HasFinalMonochromaticEdge H finalColour ω)) =
        𝔼 ω : Ω, realIndicator
          (∃ b ∈ (Finset.univ : Finset Bool),
            ∃ e ∈ H, FinalMonoInColour finalColour b e ω) := by
      apply Finset.expect_congr rfl
      intro ω _
      congr 1
      simp [HasFinalMonochromaticEdge]
    _ ≤ ∑ b ∈ (Finset.univ : Finset Bool),
        𝔼 ω : Ω, realIndicator
          (∃ e ∈ H, FinalMonoInColour finalColour b e ω) :=
      expect_realIndicator_biExists_le_sum (Finset.univ : Finset Bool)
        (fun b ω ↦ ∃ e ∈ H, FinalMonoInColour finalColour b e ω)
    _ ≤ ∑ b ∈ (Finset.univ : Finset Bool), ∑ e ∈ H,
        𝔼 ω : Ω, realIndicator (FinalMonoInColour finalColour b e ω) := by
      apply Finset.sum_le_sum
      intro b hb
      exact expect_realIndicator_biExists_le_sum H
        (fun e ω ↦ FinalMonoInColour finalColour b e ω)
    _ ≤ ∑ b ∈ (Finset.univ : Finset Bool), ∑ e ∈ H,
        invTwoPow e.card * K := by
      exact Finset.sum_le_sum fun b hb ↦
        Finset.sum_le_sum fun e he ↦ hfixed b e he
    _ = qWeightR H * K := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_bool,
        nsmul_eq_mul, Nat.cast_ofNat]
      rw [qWeightR, booleanWeightR]
      simp_rw [invTwoPow_eq_zpow_neg]
      rw [← Finset.sum_mul]
      ring

/-- The common fixed-edge factor in the DGK proof is globally below
`Q^2 d 3^M / r` when the doubled Boolean weight is at most `Q`. -/
lemma qWeight_mul_fixedFactor_le_threePow
    {q : ℝ} {Q d M r : ℕ} (hq0 : 0 ≤ q) (hq : q ≤ Q) (hr : 0 < r) :
    q * (q * d / r * Real.exp M) ≤
      ((Q : ℝ) ^ 2 * d * 3 ^ M) / r := by
  have hQ0 : (0 : ℝ) ≤ Q := by positivity
  have hd0 : (0 : ℝ) ≤ d := by positivity
  have hr0 : (0 : ℝ) ≤ r := by positivity
  have hexp0 : 0 ≤ Real.exp (M : ℝ) := (Real.exp_pos _).le
  have hsq : q ^ 2 ≤ (Q : ℝ) ^ 2 := by
    nlinarith
  have hexp : Real.exp (M : ℝ) ≤ (3 : ℝ) ^ M :=
    DGKAnalytic.exp_le_three_pow_of_le_natCast (le_rfl : (M : ℝ) ≤ M)
  rw [div_eq_mul_inv, div_eq_mul_inv]
  calc
    q * (q * (d : ℝ) * (r : ℝ)⁻¹ * Real.exp (M : ℝ)) =
        q ^ 2 * (d : ℝ) * (r : ℝ)⁻¹ * Real.exp (M : ℝ) := by ring
    _ ≤ (Q : ℝ) ^ 2 * (d : ℝ) * (r : ℝ)⁻¹ * Real.exp (M : ℝ) := by
      gcongr
    _ ≤ (Q : ℝ) ^ 2 * (d : ℝ) * (r : ℝ)⁻¹ * (3 : ℝ) ^ M := by
      gcongr
    _ = ((Q : ℝ) ^ 2 * d * 3 ^ M) * (r : ℝ)⁻¹ := by ring

/-- Ready-to-use final-event estimate: combine a fixed-edge DGK estimate with
the two-colour/edge union bound and the numerical cutoff. -/
theorem expect_hasFinalMonochromaticEdge_lt_one_sixteenth
    {V Ω : Type*} [DecidableEq V] [Fintype Ω]
    (H : Hypergraph V) (finalColour : Ω → V → Bool)
    {Q d M r : ℕ} (hq : qWeightR H ≤ Q) (hrpos : 0 < r)
    (hcutoff : Q ^ 2 * d * 3 ^ M * 16 < r)
    (hfixed : ∀ b e, e ∈ H →
      (𝔼 ω : Ω, realIndicator (FinalMonoInColour finalColour b e ω)) ≤
        invTwoPow e.card *
          (qWeightR H * d / r * Real.exp M)) :
    (𝔼 ω : Ω,
      realIndicator (HasFinalMonochromaticEdge H finalColour ω)) <
        (1 : ℝ) / 16 := by
  calc
    (𝔼 ω : Ω,
      realIndicator (HasFinalMonochromaticEdge H finalColour ω)) ≤
        qWeightR H * (qWeightR H * d / r * Real.exp M) :=
      expect_hasFinalMonochromaticEdge_le H finalColour
        (qWeightR H * d / r * Real.exp M) hfixed
    _ ≤ ((Q : ℝ) ^ 2 * d * 3 ^ M) / r :=
      qWeight_mul_fixedFactor_le_threePow (qWeightR_nonneg H) hq hrpos
    _ < (1 : ℝ) / 16 := by
      have hrpos' : (0 : ℝ) < r := by exact_mod_cast hrpos
      rw [div_lt_div_iff₀ hrpos' (by norm_num : (0 : ℝ) < 16)]
      norm_num
      exact_mod_cast hcutoff

/-! ## The numerical endgame -/

lemma real_Q_div_128Q_add_one_lt_one_over_128 (Q : ℕ) (hQ : 0 < Q) :
    (Q : ℝ) / ((128 * Q : ℕ) + 1) < (1 : ℝ) / 128 := by
  have hden : (0 : ℝ) < ((128 * Q : ℕ) + 1) := by positivity
  rw [div_lt_div_iff₀ hden (by norm_num : (0 : ℝ) < 128)]
  norm_num
  linarith

lemma twoQ_div_sixteenQ_eq_one_eighth (Q : ℕ) (hQ : 0 < Q) :
    (2 * (Q : ℝ)) / (16 * Q : ℕ) = (1 : ℝ) / 8 := by
  have hQr : (Q : ℝ) ≠ 0 := by positivity
  norm_num
  field_simp [hQr] <;> norm_num

/-- The natural-number cutoff inequality used by DGK implies that the final
monochromatic-edge error is below `1/16`. -/
lemma final_error_lt_one_sixteenth
    {Q d M r : ℕ} (hr : Q ^ 2 * d * 3 ^ M * 16 < r) :
    ((Q : ℝ) ^ 2 * d * 3 ^ M) / r < (1 : ℝ) / 16 := by
  have hrpos : (0 : ℝ) < r := by
    exact_mod_cast (lt_of_le_of_lt (Nat.zero_le _) hr)
  rw [div_lt_div_iff₀ hrpos (by norm_num : (0 : ℝ) < 16)]
  norm_num
  exact_mod_cast hr

/-- The three DGK bad-event estimates add to strictly less than one.  The
three summands are, respectively, the light-edge union bound, the Markov
bound, and the final-monochromatic-edge union bound after replacing `exp M`
by `3^M`. -/
theorem dgk_three_errors_lt_one
    {Q d M r : ℕ} (hQ : 0 < Q) (hr : Q ^ 2 * d * 3 ^ M * 16 < r) :
    (Q : ℝ) / ((128 * Q : ℕ) + 1) +
        (2 * (Q : ℝ)) / (16 * Q : ℕ) +
        ((Q : ℝ) ^ 2 * d * 3 ^ M) / r < 1 := by
  have hlight := real_Q_div_128Q_add_one_lt_one_over_128 Q hQ
  have halmost := twoQ_div_sixteenQ_eq_one_eighth Q hQ
  have hfinal := final_error_lt_one_sixteenth hr
  rw [halmost]
  linarith

/-! ## Extraction of a good outcome -/

/-- If a bad event has probability strictly below one on a nonempty finite
uniform sample space, some outcome avoids it. -/
theorem exists_not_bad_of_expect_lt_one
    {Ω : Type*} [Fintype Ω] [Nonempty Ω] (Bad : Ω → Prop)
    (hbad : (𝔼 ω : Ω, realIndicator (Bad ω)) < 1) :
    ∃ ω : Ω, ¬ Bad ω := by
  classical
  by_contra h
  push_neg at h
  have hone : (𝔼 ω : Ω, realIndicator (Bad ω)) = 1 := by
    simp [realIndicator, h]
  linarith

/-- A three-event union bound, in the exact shape used in the DGK
application (light edge, excessive almost-mass, final monochromatic edge). -/
lemma expect_realIndicator_or_three_le
    {Ω : Type*} [Fintype Ω] (A B C : Ω → Prop) :
    (𝔼 ω : Ω, realIndicator (A ω ∨ B ω ∨ C ω)) ≤
      (𝔼 ω : Ω, realIndicator (A ω)) +
        (𝔼 ω : Ω, realIndicator (B ω)) +
          (𝔼 ω : Ω, realIndicator (C ω)) := by
  classical
  calc
    (𝔼 ω : Ω, realIndicator (A ω ∨ B ω ∨ C ω)) ≤
        𝔼 ω : Ω,
          (realIndicator (A ω) + realIndicator (B ω) + realIndicator (C ω)) := by
      apply Finset.expect_le_expect
      intro ω _
      by_cases hA : A ω <;> by_cases hB : B ω <;> by_cases hC : C ω <;>
        simp [realIndicator, hA, hB, hC]
    _ = (𝔼 ω : Ω, realIndicator (A ω)) +
        (𝔼 ω : Ω, realIndicator (B ω)) +
          (𝔼 ω : Ω, realIndicator (C ω)) := by
      rw [Finset.expect_add_distrib, Finset.expect_add_distrib]

/-- A Boolean colouring is proper when every edge contains two vertices of
different colours. -/
def ProperBooleanColouring {V : Type*} (H : Hypergraph V) (χ : V → Bool) : Prop :=
  ∀ e ∈ H, ∃ x ∈ e, ∃ y ∈ e, χ x ≠ χ y

lemma properBooleanColouring_of_not_hasFinalMonochromaticEdge
    {V Ω : Type*} [DecidableEq V]
    (H : Hypergraph V) (finalColour : Ω → V → Bool) (ω : Ω)
    (hω : ¬HasFinalMonochromaticEdge H finalColour ω) :
    ProperBooleanColouring H (finalColour ω) := by
  classical
  intro e he
  have hene : e.Nonempty := by
    by_contra hempty
    apply hω
    refine ⟨false, e, he, ?_⟩
    simpa [FinalMonoInColour, Finset.not_nonempty_iff_eq_empty.mp hempty]
  obtain ⟨x, hxe⟩ := hene
  by_contra hdiff
  push_neg at hdiff
  apply hω
  refine ⟨finalColour ω x, e, he, ?_⟩
  intro y hye
  exact hdiff y hye x hxe

/-- The final extraction step: a probability below one for the event that
some edge finishes monochromatic produces a proper Boolean colouring. -/
theorem exists_properColouring_of_finalMono_expect_lt_one
    {V Ω : Type*} [DecidableEq V] [Fintype Ω] [Nonempty Ω]
    (H : Hypergraph V) (finalColour : Ω → V → Bool)
    (hbad :
      (𝔼 ω : Ω, realIndicator (HasFinalMonochromaticEdge H finalColour ω)) < 1) :
    ∃ ω : Ω, ProperBooleanColouring H (finalColour ω) := by
  classical
  obtain ⟨ω, hω⟩ :=
    exists_not_bad_of_expect_lt_one
      (HasFinalMonochromaticEdge H finalColour) hbad
  exact ⟨ω, properBooleanColouring_of_not_hasFinalMonochromaticEdge
    H finalColour ω hω⟩

/-- Complete abstract union/extraction interface.  Concrete light-edge,
Markov, and fixed-edge estimates can be supplied independently; if their
three bounds add to less than one, one outcome has a proper final colouring. -/
theorem exists_properColouring_of_three_bad_estimates
    {V Ω : Type*} [DecidableEq V] [Fintype Ω] [Nonempty Ω]
    (H : Hypergraph V) (finalColour : Ω → V → Bool)
    (light excessive : Ω → Prop) (a b c : ℝ)
    (hlight : (𝔼 ω : Ω, realIndicator (light ω)) ≤ a)
    (hexcessive : (𝔼 ω : Ω, realIndicator (excessive ω)) ≤ b)
    (hfinal :
      (𝔼 ω : Ω, realIndicator (HasFinalMonochromaticEdge H finalColour ω)) ≤ c)
    (htotal : a + b + c < 1) :
    ∃ ω : Ω, ProperBooleanColouring H (finalColour ω) := by
  classical
  let Bad : Ω → Prop := fun ω ↦
    light ω ∨ excessive ω ∨ HasFinalMonochromaticEdge H finalColour ω
  have hBadExpect : (𝔼 ω : Ω, realIndicator (Bad ω)) < 1 := by
    calc
      (𝔼 ω : Ω, realIndicator (Bad ω)) ≤
          (𝔼 ω : Ω, realIndicator (light ω)) +
            (𝔼 ω : Ω, realIndicator (excessive ω)) +
              (𝔼 ω : Ω,
                realIndicator (HasFinalMonochromaticEdge H finalColour ω)) :=
        expect_realIndicator_or_three_le light excessive
          (HasFinalMonochromaticEdge H finalColour)
      _ ≤ a + b + c := add_le_add (add_le_add hlight hexcessive) hfinal
      _ < 1 := htotal
  obtain ⟨ω, hω⟩ := exists_not_bad_of_expect_lt_one Bad hBadExpect
  refine ⟨ω, properBooleanColouring_of_not_hasFinalMonochromaticEdge
    H finalColour ω ?_⟩
  intro hfinalω
  exact hω (Or.inr (Or.inr hfinalω))

end Erdos1027.DGKUnion
