/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
This is a Lean formalization of a solution to Erdős Problem 308.
https://www.erdosproblems.com/forum/thread/308

Informal authors:
- Ernest S. Croot III
- Hisashi Yokota

Formal authors:
- Codex
- GPT-5.6 Sol

URLs:
- https://github.com/plby/lean-proofs/blob/main/ErdosProblems/Erdos308.md
-/
/-
Erdős Problem 308: integers represented by bounded unit fractions.

Informal authors:
- Ernest S. Croot III
- Hisashi Yokota

Formal author:
- OpenAI Codex

The detailed mathematical proof and Leanization plan are in tex/308.tex.
-/

import UnitFractions.Definitions
import ErdosProblems.Erdos308.CrootCompletion
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.NumberTheory.Harmonic.Bounds
import Mathlib.NumberTheory.Harmonic.Int
import Mathlib.Tactic

open Filter Real
open scoped BigOperators Topology

namespace Erdos308

noncomputable section

attribute [local instance] Classical.propDecidable

/-- Representation by distinct unit fractions with denominators at most N. -/
def IsRepresentable (N k : ℕ) : Prop :=
  ∃ A : Finset ℕ,
    A ⊆ Finset.Icc 1 N ∧ UnitFractions.rec_sum A = (k : ℚ)

/-- The represented positive integers. -/
def representedPositiveIntegers (N : ℕ) : Set ℕ :=
  {k | 0 < k ∧ IsRepresentable N k}

/-- A finite encoding of every represented integer, including zero. -/
def representedIntegers (N : ℕ) : Finset ℕ :=
  (Finset.range (N + 1)).filter (IsRepresentable N)

/-- The cardinality convention used by Croot and Yokota, which includes zero. -/
def representedCount (N : ℕ) : ℕ :=
  (representedIntegers N).card

/-- The harmonic sum, coerced to the reals. -/
def harmonicReal (N : ℕ) : ℝ :=
  ((harmonic N : ℚ) : ℝ)

/-- The greatest natural number not exceeding the harmonic sum. -/
def harmonicFloor (N : ℕ) : ℕ :=
  ⌊harmonicReal N⌋₊

/-- Croot's lower-order scale. -/
def crootScale (N : ℕ) : ℝ :=
  Real.log (Real.log (N : ℝ)) ^ 2 / Real.log (N : ℝ)

/-- The least positive integer which is not represented. -/
noncomputable def firstMissing (N : ℕ) : ℕ :=
  sInf {k : ℕ | 0 < k ∧ ¬ IsRepresentable N k}

/-- A quantified interpretation of Croot's interval theorem, relative to the
exact harmonic sum. -/
def CrootIntervalStatement : Prop :=
  ∃ e : ℕ → ℝ,
    Tendsto e atTop (𝓝 0) ∧
      ∀ᶠ N : ℕ in atTop, ∀ k : ℕ,
        0 < k →
        (k : ℝ) <
          harmonicReal N - ((9 / 2 : ℝ) + e N) * crootScale N →
        IsRepresentable N k

/-- Croot's two-sided cardinality estimates, in the convention which counts
the representation of zero by the empty set. -/
def CrootCardinalityBounds : Prop :=
  ∃ lowerError upperError : ℕ → ℝ,
    Tendsto lowerError atTop (𝓝 0) ∧
    Tendsto upperError atTop (𝓝 0) ∧
      ∀ᶠ N : ℕ in atTop,
        harmonicReal N -
            ((9 / 2 : ℝ) + lowerError N) * crootScale N ≤
          (representedCount N : ℝ) ∧
        (representedCount N : ℝ) ≤
          harmonicReal N -
            ((1 / 2 : ℝ) + upperError N) * crootScale N

@[simp] lemma mem_representedIntegers {N k : ℕ} :
    k ∈ representedIntegers N ↔ k ≤ N ∧ IsRepresentable N k := by
  simp [representedIntegers]

lemma rec_sum_Icc_one (N : ℕ) :
    UnitFractions.rec_sum (Finset.Icc 1 N) = harmonic N := by
  rw [UnitFractions.rec_sum, harmonic_eq_sum_Icc]
  simp [one_div]

lemma represented_le_harmonic {N k : ℕ} (hk : IsRepresentable N k) :
    (k : ℚ) ≤ harmonic N := by
  obtain ⟨A, hAN, hsum⟩ := hk
  rw [← rec_sum_Icc_one N, ← hsum]
  exact UnitFractions.rec_sum_mono hAN

lemma harmonicReal_nonneg (N : ℕ) : 0 ≤ harmonicReal N := by
  rw [harmonicReal, harmonic_eq_sum_Icc, Rat.cast_sum]
  positivity

lemma represented_le_harmonicFloor {N k : ℕ} (hk : IsRepresentable N k) :
    k ≤ harmonicFloor N := by
  apply Nat.le_floor
  change (k : ℝ) ≤ ((harmonic N : ℚ) : ℝ)
  exact Rat.cast_le.mpr (represented_le_harmonic hk)

lemma represented_le_N {N k : ℕ} (hk : IsRepresentable N k) : k ≤ N := by
  obtain ⟨A, hAN, hsum⟩ := hk
  have hsumCard : UnitFractions.rec_sum A ≤ (A.card : ℚ) := by
    rw [UnitFractions.rec_sum]
    calc
      ∑ n ∈ A, (1 : ℚ) / n ≤ ∑ _n ∈ A, (1 : ℚ) := by
        apply Finset.sum_le_sum
        intro n hn
        have hnOne : (1 : ℚ) ≤ n := by
          exact_mod_cast (Finset.mem_Icc.mp (hAN hn)).1
        exact (div_le_one (by positivity : (0 : ℚ) < n)).2 hnOne
      _ = (A.card : ℚ) := by simp
  have hkCardQ : (k : ℚ) ≤ (A.card : ℚ) := by simpa [hsum] using hsumCard
  have hkCard : k ≤ A.card := by exact_mod_cast hkCardQ
  exact hkCard.trans (by simpa using Finset.card_le_card hAN)

lemma representedIntegers_eq_filter_floor (N : ℕ) :
    representedIntegers N =
      (Finset.range (harmonicFloor N + 1)).filter (IsRepresentable N) := by
  ext k
  simp only [mem_representedIntegers, Finset.mem_filter, Finset.mem_range,
    Nat.lt_add_one_iff]
  constructor
  · rintro ⟨_, hk⟩
    exact ⟨represented_le_harmonicFloor hk, hk⟩
  · rintro ⟨_, hk⟩
    exact ⟨represented_le_N hk, hk⟩

@[simp] lemma zero_isRepresentable (N : ℕ) : IsRepresentable N 0 := by
  exact ⟨∅, by simp, by simp [UnitFractions.rec_sum]⟩

lemma firstMissing_set_nonempty (N : ℕ) :
    {k : ℕ | 0 < k ∧ ¬ IsRepresentable N k}.Nonempty := by
  refine ⟨harmonicFloor N + 1, by omega, ?_⟩
  intro hrep
  exact (Nat.not_succ_le_self (harmonicFloor N))
    (represented_le_harmonicFloor hrep)

lemma firstMissing_mem (N : ℕ) :
    firstMissing N ∈ {k : ℕ | 0 < k ∧ ¬ IsRepresentable N k} := by
  exact Nat.sInf_mem (firstMissing_set_nonempty N)

lemma firstMissing_pos (N : ℕ) : 0 < firstMissing N :=
  (firstMissing_mem N).1

lemma firstMissing_not_representable (N : ℕ) :
    ¬ IsRepresentable N (firstMissing N) :=
  (firstMissing_mem N).2

lemma firstMissing_le_of_not_representable {N k : ℕ}
    (hkPos : 0 < k) (hk : ¬ IsRepresentable N k) :
    firstMissing N ≤ k := by
  exact Nat.sInf_le ⟨hkPos, hk⟩

lemma representable_of_lt_firstMissing {N k : ℕ}
    (hkPos : 0 < k) (hk : k < firstMissing N) :
    IsRepresentable N k := by
  by_contra hrep
  exact (not_le_of_gt hk) (firstMissing_le_of_not_representable hkPos hrep)

lemma firstMissing_le_floor_add_one (N : ℕ) :
    firstMissing N ≤ harmonicFloor N + 1 := by
  apply firstMissing_le_of_not_representable (by omega)
  intro hrep
  exact (Nat.not_succ_le_self (harmonicFloor N))
    (represented_le_harmonicFloor hrep)

lemma crootScale_tendsto_zero :
    Tendsto crootScale atTop (𝓝 0) := by
  have hreal :
      Tendsto (fun y : ℝ ↦ (Real.log y) ^ (2 : ℝ) / y)
        atTop (𝓝 0) := by
    simpa only [Real.rpow_one] using
      (isLittleO_log_rpow_rpow_atTop (s := 1) 2 one_pos).tendsto_div_nhds_zero
  have hlogNat :
      Tendsto (fun N : ℕ ↦ Real.log (N : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hcomp :=
    (hreal.comp Real.tendsto_log_atTop).comp tendsto_natCast_atTop_atTop
  apply hcomp.congr'
  filter_upwards [
    (Real.tendsto_log_atTop.comp hlogNat).eventually
      (eventually_ge_atTop (0 : ℝ))] with N hloglog
  simp only [Function.comp_apply, crootScale]
  rw [show Real.log (Real.log (N : ℝ)) ^ (2 : ℝ) =
      Real.log (Real.log (N : ℝ)) ^ (2 : ℕ) by
        exact Real.rpow_natCast _ 2]

lemma crootScale_eventually_pos :
    ∀ᶠ N : ℕ in atTop, 0 < crootScale N := by
  have hlogNat :
      Tendsto (fun N : ℕ ↦ Real.log (N : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards [
    hlogNat.eventually (eventually_gt_atTop (1 : ℝ)),
    (Real.tendsto_log_atTop.comp hlogNat).eventually
      (eventually_gt_atTop (0 : ℝ))] with N hlogOne hloglog
  exact div_pos (sq_pos_of_pos hloglog) (by linarith)

lemma representedIntegers_eq_range_of_large_shape {N : ℕ}
    (hshape :
      representedPositiveIntegers N = Set.Icc 1 (harmonicFloor N)) :
    representedIntegers N = Finset.range (harmonicFloor N + 1) := by
  ext k
  rw [mem_representedIntegers, Finset.mem_range, Nat.lt_add_one_iff]
  constructor
  · rintro ⟨_, hkRep⟩
    exact represented_le_harmonicFloor hkRep
  · intro hkFloor
    have hkRep : IsRepresentable N k := by
      by_cases hkZero : k = 0
      · simp [hkZero]
      · have hkPos : 0 < k := Nat.pos_of_ne_zero hkZero
        have hkMem : k ∈ representedPositiveIntegers N := by
          rw [hshape]
          exact ⟨hkPos, hkFloor⟩
        exact hkMem.2
    exact ⟨represented_le_N hkRep, hkRep⟩

lemma representedCount_eq_floor_add_one_of_large_shape {N : ℕ}
    (hshape :
      representedPositiveIntegers N = Set.Icc 1 (harmonicFloor N)) :
    representedCount N = harmonicFloor N + 1 := by
  rw [representedCount, representedIntegers_eq_range_of_large_shape hshape]
  simp

/-- Croot's interval theorem alone gives the two alternatives printed on the
maintained problem page. -/
lemma interval_shape_of_croot
    (hCroot : CrootIntervalStatement) :
    ∀ᶠ N : ℕ in atTop,
      representedPositiveIntegers N = Set.Icc 1 (harmonicFloor N - 1) ∨
      representedPositiveIntegers N = Set.Icc 1 (harmonicFloor N) := by
  obtain ⟨e, he, hinterval⟩ := hCroot
  have hcoeff :
      Tendsto (fun N : ℕ ↦ (9 / 2 : ℝ) + e N) atTop (𝓝 (9 / 2 : ℝ)) :=
    by
      simpa only [add_zero] using
        (tendsto_const_nhds.add he :
          Tendsto (fun N : ℕ ↦ (9 / 2 : ℝ) + e N) atTop
            (𝓝 ((9 / 2 : ℝ) + 0)))
  have hcorrection :
      Tendsto (fun N : ℕ ↦ ((9 / 2 : ℝ) + e N) * crootScale N)
        atTop (𝓝 0) := by
    simpa using hcoeff.mul crootScale_tendsto_zero
  have hlessOne :
      ∀ᶠ N : ℕ in atTop,
        ((9 / 2 : ℝ) + e N) * crootScale N < 1 :=
    hcorrection.eventually (eventually_lt_nhds (by norm_num))
  filter_upwards [hinterval, hlessOne] with N hN hcorr
  have hbelow : ∀ k : ℕ, 0 < k → k ≤ harmonicFloor N - 1 →
      IsRepresentable N k := by
    intro k hkPos hkFloor
    apply hN k hkPos
    have hkSucc : k + 1 ≤ harmonicFloor N := by omega
    have hkSuccReal : (k : ℝ) + 1 ≤ harmonicFloor N := by
      exact_mod_cast hkSucc
    have hfloorLe : (harmonicFloor N : ℝ) ≤ harmonicReal N :=
      Nat.floor_le (harmonicReal_nonneg N)
    linarith
  by_cases htop : IsRepresentable N (harmonicFloor N)
  · right
    ext k
    constructor
    · rintro ⟨hkPos, hkRep⟩
      exact ⟨hkPos, represented_le_harmonicFloor hkRep⟩
    · rintro ⟨hkPos, hkLe⟩
      refine ⟨hkPos, ?_⟩
      rcases lt_or_eq_of_le hkLe with hkLt | rfl
      · exact hbelow k hkPos (by omega)
      · exact htop
  · left
    ext k
    constructor
    · rintro ⟨hkPos, hkRep⟩
      refine ⟨hkPos, ?_⟩
      have hkLe := represented_le_harmonicFloor hkRep
      have hkNe : k ≠ harmonicFloor N := by
        intro hkEq
        exact htop (hkEq ▸ hkRep)
      omega
    · rintro ⟨hkPos, hkLe⟩
      exact ⟨hkPos, hbelow k hkPos hkLe⟩

/-- Adding Croot's cardinality upper bound rules out the larger alternative. -/
lemma exact_shape_of_croot
    (hInterval : CrootIntervalStatement)
    (hBounds : CrootCardinalityBounds) :
    ∀ᶠ N : ℕ in atTop,
      representedPositiveIntegers N = Set.Icc 1 (harmonicFloor N - 1) := by
  obtain ⟨lowerError, upperError, hlower, hupper, hcard⟩ := hBounds
  have hupperCoeff :
      ∀ᶠ N : ℕ in atTop, 0 < (1 / 2 : ℝ) + upperError N := by
    have hcoeff :
        Tendsto (fun N : ℕ ↦ (1 / 2 : ℝ) + upperError N)
          atTop (𝓝 (1 / 2 : ℝ)) := by
      simpa only [add_zero] using
        (tendsto_const_nhds.add hupper :
          Tendsto (fun N : ℕ ↦ (1 / 2 : ℝ) + upperError N) atTop
            (𝓝 ((1 / 2 : ℝ) + 0)))
    exact hcoeff.eventually (eventually_gt_nhds (by norm_num))
  filter_upwards [interval_shape_of_croot hInterval, hcard, hupperCoeff,
      crootScale_eventually_pos] with N hshape hcardN hcoeff hscale
  rcases hshape with hsmall | hlarge
  · exact hsmall
  · exfalso
    have hcount :
        representedCount N = harmonicFloor N + 1 :=
      representedCount_eq_floor_add_one_of_large_shape hlarge
    have hcountLt : (representedCount N : ℝ) < harmonicReal N := by
      calc
        (representedCount N : ℝ) ≤
            harmonicReal N -
              ((1 / 2 : ℝ) + upperError N) * crootScale N := hcardN.2
        _ < harmonicReal N := sub_lt_self _ (mul_pos hcoeff hscale)
    rw [hcount] at hcountLt
    norm_num at hcountLt
    have hfloorLt :
        harmonicReal N < (harmonicFloor N : ℝ) + 1 :=
      Nat.lt_floor_add_one (harmonicReal N)
    linarith

lemma one_isRepresentable {N : ℕ} (hN : 1 ≤ N) :
    IsRepresentable N 1 := by
  refine ⟨{1}, ?_, ?_⟩
  · simp [hN]
  · simp [UnitFractions.rec_sum]

lemma harmonicFloor_pos {N : ℕ} (hN : 1 ≤ N) :
    0 < harmonicFloor N := by
  have := represented_le_harmonicFloor (one_isRepresentable hN)
  omega

lemma firstMissing_eq_floor_of_exact_shape
    {N : ℕ}
    (hshape :
      representedPositiveIntegers N = Set.Icc 1 (harmonicFloor N - 1))
    (hfloorPos : 0 < harmonicFloor N) :
    firstMissing N = harmonicFloor N := by
  have hfloorNot : ¬ IsRepresentable N (harmonicFloor N) := by
    intro hrep
    have hmem : harmonicFloor N ∈ representedPositiveIntegers N :=
      ⟨hfloorPos, hrep⟩
    rw [hshape] at hmem
    change 1 ≤ harmonicFloor N ∧
      harmonicFloor N ≤ harmonicFloor N - 1 at hmem
    omega
  apply Nat.le_antisymm
  · exact firstMissing_le_of_not_representable hfloorPos hfloorNot
  · by_contra hnot
    have hlt : firstMissing N < harmonicFloor N := Nat.lt_of_not_ge hnot
    have hmem : firstMissing N ∈ Set.Icc 1 (harmonicFloor N - 1) :=
      ⟨firstMissing_pos N, by omega⟩
    rw [← hshape] at hmem
    exact firstMissing_not_representable N hmem.2

lemma firstMissing_eq_floor_of_croot
    (hInterval : CrootIntervalStatement)
    (hBounds : CrootCardinalityBounds) :
    ∀ᶠ N : ℕ in atTop, firstMissing N = harmonicFloor N := by
  filter_upwards [exact_shape_of_croot hInterval hBounds,
      eventually_ge_atTop (1 : ℕ)] with N hshape hN
  exact firstMissing_eq_floor_of_exact_shape hshape (harmonicFloor_pos hN)

/-! ## Unconditional resolution -/

/-- The Croot construction formalized in the companion modules covers every
positive integer at least one below the harmonic floor. -/
theorem eventually_interval_coverage :
    ∀ᶠ N : ℕ in atTop, ∀ k : ℕ,
      0 < k → k ≤ harmonicFloor N - 1 → IsRepresentable N k := by
  filter_upwards [CrootCompletion.eventually_initial_interval] with N hN
  intro k hkpos hkle
  apply hN k hkpos
  simpa [harmonicFloor, harmonicReal, CrootInterval.harmonicMass] using
    (show k + 1 ≤ harmonicFloor N by omega)

/-- Unconditionally, the represented positive integers have one of the two
eventual initial-interval shapes stated on the Erdős Problems page. -/
theorem eventually_represented_shape :
    ∀ᶠ N : ℕ in atTop,
      representedPositiveIntegers N = Set.Icc 1 (harmonicFloor N - 1) ∨
      representedPositiveIntegers N = Set.Icc 1 (harmonicFloor N) := by
  filter_upwards [eventually_interval_coverage] with N hcoverage
  by_cases htop : IsRepresentable N (harmonicFloor N)
  · right
    ext k
    constructor
    · rintro ⟨hkpos, hkrep⟩
      exact ⟨hkpos, represented_le_harmonicFloor hkrep⟩
    · rintro ⟨hkpos, hkle⟩
      refine ⟨hkpos, ?_⟩
      rcases lt_or_eq_of_le hkle with hklt | rfl
      · exact hcoverage k hkpos (by omega)
      · exact htop
  · left
    ext k
    constructor
    · rintro ⟨hkpos, hkrep⟩
      refine ⟨hkpos, ?_⟩
      have hkle := represented_le_harmonicFloor hkrep
      have hkne : k ≠ harmonicFloor N := by
        intro heq
        exact htop (heq ▸ hkrep)
      omega
    · rintro ⟨hkpos, hkle⟩
      exact ⟨hkpos, hcoverage k hkpos hkle⟩

lemma firstMissing_eq_floor_add_one_of_large_shape
    {N : ℕ}
    (hshape :
      representedPositiveIntegers N = Set.Icc 1 (harmonicFloor N)) :
    firstMissing N = harmonicFloor N + 1 := by
  apply le_antisymm (firstMissing_le_floor_add_one N)
  by_contra hnot
  have hle : firstMissing N ≤ harmonicFloor N := by omega
  have hmem : firstMissing N ∈ representedPositiveIntegers N := by
    rw [hshape]
    exact ⟨firstMissing_pos N, hle⟩
  exact firstMissing_not_representable N hmem.2

/-- **Resolution of Erdős Problem 308.**  For every sufficiently large
`N`, the positive represented integers are either precisely
`{1,…,⌊H_N⌋-1}` or precisely `{1,…,⌊H_N⌋}`.  Accordingly, the least
positive missing integer is either `⌊H_N⌋` or `⌊H_N⌋+1`.

The disjunction is intentionally synchronized: each least-missing value is
proved from the corresponding set equality rather than stated independently.
-/
theorem erdos_308 :
    ∀ᶠ N : ℕ in atTop,
      (representedPositiveIntegers N = Set.Icc 1 (harmonicFloor N - 1) ∧
        firstMissing N = harmonicFloor N) ∨
      (representedPositiveIntegers N = Set.Icc 1 (harmonicFloor N) ∧
        firstMissing N = harmonicFloor N + 1) := by
  filter_upwards [eventually_represented_shape, eventually_ge_atTop 1]
      with N hshape hN
  rcases hshape with hsmall | hlarge
  · exact Or.inl ⟨hsmall,
      firstMissing_eq_floor_of_exact_shape hsmall (harmonicFloor_pos hN)⟩
  · exact Or.inr ⟨hlarge, firstMissing_eq_floor_add_one_of_large_shape hlarge⟩

end

end Erdos308

#print axioms Erdos308.erdos_308
