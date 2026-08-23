/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
This is a Lean formalization of a solution to Erdős Problem 305.
https://www.erdosproblems.com/forum/thread/305

Informal authors:
- Michael N. Bleicher
- Paul Erdős
- Hisashi Yokota
- Yang P. Liu
- Mehtaab Sawhney

Formal authors:
- Codex
- GPT-5.6 Sol

URLs:
- https://github.com/plby/lean-proofs/blob/main/ErdosProblems/Erdos305.md
-/
/-
This file formalizes the affirmative resolution of Erdős Problem 305.

Informal authors:
- Michael N. Bleicher and Paul Erdős
- Hisashi Yokota
- Yang P. Liu and Mehtaab Sawhney

Formalization:
- OpenAI Codex

Primary references:
- https://combinatorica.hu/~p_erdos/1976-10.pdf
- https://doi.org/10.1016/0022-314X(88)90017-0
- https://arxiv.org/abs/2404.07113
-/
import Util.PolynomialEgyptianSums
import ErdosProblems.Erdos285.PrimePowers
import ErdosProblems.Erdos285.Proposition7
import ErdosProblems.Erdos305.Assembly
import UnitFractions.Definitions

open Filter Real
open scoped BigOperators Topology

namespace Erdos305

noncomputable section

attribute [local instance] Classical.propDecidable

/-- `a / b` has an Egyptian-fraction expansion by distinct positive
denominators, every one of which is at most `B`.  A `Finset` is equivalent
to the increasing-sequence formulation after sorting. -/
def HasBoundedExpansion (a b B : ℕ) : Prop :=
  ∃ E : Finset ℕ,
    0 ∉ E ∧
    (∀ n ∈ E, n ≤ B) ∧
    UnitFractions.rec_sum E = (a : ℚ) / b

/-- The least possible largest denominator in an Egyptian-fraction
expansion of `a / b`. -/
def D (a b : ℕ) : ℕ :=
  sInf {B : ℕ | HasBoundedExpansion a b B}

/-- The worst least denominator bound among the proper fractions with
denominator `b`. -/
def Dmax (b : ℕ) : ℕ :=
  (Finset.Ico 1 b).sup fun a ↦ D a b

/-- The exact eventual meaning of
`D(b) ≪ b (log b) ^ (1 + o(1))`. -/
def Erdos305Answer : Prop :=
  ∃ δ : ℕ → ℝ, Tendsto δ atTop (𝓝 0) ∧
    ∃ C : ℝ, 0 < C ∧
      ∀ᶠ b : ℕ in atTop,
        (Dmax b : ℝ) ≤ C * b * (log b) ^ (1 + δ b)

/-- Bounded expansions are monotone in their denominator cap. -/
lemma HasBoundedExpansion.mono {a b B B' : ℕ}
    (h : HasBoundedExpansion a b B) (hBB' : B ≤ B') :
    HasBoundedExpansion a b B' := by
  obtain ⟨E, hE0, hEB, hsum⟩ := h
  exact ⟨E, hE0, fun n hn ↦ (hEB n hn).trans hBB', hsum⟩

/-- Every positive rational `a / b` has a bounded expansion. -/
lemma exists_hasBoundedExpansion {a b : ℕ} (ha : 0 < a) (hb : 0 < b) :
    ∃ B : ℕ, HasBoundedExpansion a b B := by
  have hrat : (0 : ℚ) < (a : ℚ) / b := by
    exact div_pos (by exact_mod_cast ha) (by exact_mod_cast hb)
  obtain ⟨E, hEpos, hsum⟩ :=
    PolynomialEgyptianSums.egyptian_expansion_exists ((a : ℚ) / b) hrat 0
  refine ⟨E.sup id, E, ?_, ?_, ?_⟩
  · intro h0
    have := hEpos 0 h0
    omega
  · intro n hn
    exact Finset.le_sup (s := E) (f := id) hn
  · simpa [UnitFractions.rec_sum] using hsum.symm

/-- The infimum in `D` is attained for every positive fraction. -/
lemma hasBoundedExpansion_D {a b : ℕ} (ha : 0 < a) (hb : 0 < b) :
    HasBoundedExpansion a b (D a b) := by
  change sInf {B : ℕ | HasBoundedExpansion a b B} ∈
    {B : ℕ | HasBoundedExpansion a b B}
  apply Nat.sInf_mem
  exact exists_hasBoundedExpansion ha hb

/-- A displayed bounded expansion bounds the least possible largest
denominator. -/
lemma D_le_of_hasBoundedExpansion {a b B : ℕ}
    (h : HasBoundedExpansion a b B) : D a b ≤ B := by
  exact Nat.sInf_le h

/-- For positive `a,b`, the least bound is at most `B` exactly when an
expansion bounded by `B` exists. -/
lemma D_le_iff {a b B : ℕ} (ha : 0 < a) (hb : 0 < b) :
    D a b ≤ B ↔ HasBoundedExpansion a b B := by
  constructor
  · intro hDB
    exact (hasBoundedExpansion_D ha hb).mono hDB
  · exact D_le_of_hasBoundedExpansion

/-- A uniform pointwise bound for all proper numerators bounds `Dmax`. -/
lemma Dmax_le {b B : ℕ}
    (h : ∀ a, 1 ≤ a → a < b → D a b ≤ B) : Dmax b ≤ B := by
  rw [Dmax]
  apply Finset.sup_le
  intro a ha
  simp only [Finset.mem_Ico] at ha
  exact h a ha.1 ha.2

/-- `Dmax` dominates each proper numerator. -/
lemma D_le_Dmax {a b : ℕ} (ha : 1 ≤ a) (hab : a < b) :
    D a b ≤ Dmax b := by
  rw [Dmax]
  exact Finset.le_sup (s := Finset.Ico 1 b) (f := fun x ↦ D x b)
    (Finset.mem_Ico.mpr ⟨ha, hab⟩)

/-! ## The already-formalized square-bound baseline

The unpadded form of the prime-power elimination developed for Erdős
Problem 285 gives the exact `S ^ 2` denominator bound for an `S`-smooth
rational.  This is the classical square loss that the Yokota and
Liu--Sawhney interval lemmas sharpen. -/

open Erdos285.PrimePowers

/-- Unpadded Proposition 7: under its explicit cutoff estimates, an
`y`-smooth rational in the indicated range has an exact expansion with
all denominators at most `y ^ 2`. -/
theorem smooth_expansion_square_of_cutoff
    {c : ℝ} (_hc : 0 < c) {lo y : ℕ} {r : ℚ}
    (_hy : 40 ≤ y) (hlo : 3 ≤ lo) (hloy : lo ≤ y)
    (hL : initialLcm lo ≤ y ^ 2)
    (hry : largestPrimePowerPart r.den ≤ y)
    (hrLower : c / log (y : ℝ) < (r : ℝ))
    (hrUpper : (r : ℝ) < 1)
    (htail : Erdos285.Proposition7.largeSquareCost lo y < c / log (y : ℝ)) :
    ∃ E : Finset ℕ,
      UnitFractions.rec_sum E = r ∧
      0 ∉ E ∧
      ∀ n ∈ E, n ≤ y ^ 2 := by
  obtain ⟨E, hE⟩ :=
    Erdos285.Proposition7.exists_budgetedPreliminaryResult_of_lemmas
      lo y hlo hloy hL r hry
  have hsumlt : (UnitFractions.rec_sum E : ℝ) < 1 + (r : ℝ) := by
    linarith [hE.rec_sum_lt]
  have hsum_nonnegQ : 0 ≤ UnitFractions.rec_sum E :=
    UnitFractions.rec_sum_nonneg
  have hsum_nonneg : (0 : ℝ) ≤ UnitFractions.rec_sum E := by
    exact_mod_cast hsum_nonnegQ
  have hresLower : (-1 : ℝ) < (r : ℝ) - UnitFractions.rec_sum E := by
    linarith
  have hresUpper : (r : ℝ) - UnitFractions.rec_sum E < 1 := by
    linarith
  have hsmallR : |(r : ℝ) - UnitFractions.rec_sum E| < 1 :=
    (abs_lt).2 ⟨hresLower, hresUpper⟩
  have hsmall : |r - UnitFractions.rec_sum E| < (1 : ℚ) := by
    exact_mod_cast hsmallR
  have hzero := hE.toPreliminaryResult.residual_eq_zero hsmall
  refine ⟨E, ?_, hE.zero_not_mem, hE.le_bound⟩
  linarith

/-- Eventual unpadded Proposition 7. -/
theorem eventually_smooth_expansion_square {c : ℝ} (hc : 0 < c) :
    ∀ᶠ y : ℕ in atTop, ∀ r : ℚ,
      largestPrimePowerPart r.den ≤ y →
      c / log (y : ℝ) < (r : ℝ) →
      (r : ℝ) < 1 →
      ∃ E : Finset ℕ,
        UnitFractions.rec_sum E = r ∧
        0 ∉ E ∧
        ∀ n ∈ E, n ≤ y ^ 2 := by
  have htail :=
    Erdos285.RoughCounts.eventually_sum_ten_div_primePower_sq_lt_div_log hc
  have hcut3 :=
    Erdos285.RoughCounts.naturalLogCutoff_tendsto_atTop.eventually
      (eventually_ge_atTop (3 : ℕ))
  filter_upwards [eventually_ge_atTop (40 : ℕ), htail, hcut3,
    Erdos285.Proposition7.eventually_initialLcm_naturalLogCutoff_le_sq]
      with y hy htailY hcut3Y hLY
  intro r hry hrLower hrUpper
  apply smooth_expansion_square_of_cutoff hc hy hcut3Y
  · exact (Erdos285.Proposition7.naturalLogCutoff_lt_half y hy).le.trans
      (Nat.div_le_self y 2)
  · exact hLY
  · exact hry
  · exact hrLower
  · exact hrUpper
  · simpa [Erdos285.Proposition7.largeSquareCost] using htailY

/-! ## Resolution of Problem 305 -/

/-- Erdős Problem 305 has an affirmative answer: uniformly over every
proper numerator `a`, the least possible largest denominator is at most
`b * (log b) ^ (1 + o(1))`, up to an absolute constant. -/
theorem erdos305 : Erdos305Answer := by
  refine ⟨Scale.delta, Scale.delta_tendsto_zero, 8, by norm_num, ?_⟩
  filter_upwards [Assembly.eventually_uniform_expansion,
    Scale.eventually_cutoff_le_two_realScale,
    Scale.eventually_realScale_eq_rpow]
      with b hExpansion hcutoff hscale
  have hDmax : Dmax b ≤ 4 * b * Scale.cutoff b := by
    apply Dmax_le
    intro a ha hab
    obtain ⟨E, hsum, hE0, hEbound⟩ := hExpansion a ha hab
    exact D_le_of_hasBoundedExpansion ⟨E, hE0, hEbound, hsum⟩
  have hDmaxR : (Dmax b : ℝ) ≤ 4 * b * Scale.cutoff b := by
    exact_mod_cast hDmax
  calc
    (Dmax b : ℝ) ≤ 4 * b * Scale.cutoff b := hDmaxR
    _ ≤ 4 * b * (2 * Scale.realScale b) :=
      mul_le_mul_of_nonneg_left hcutoff (by positivity)
    _ = 8 * b * Scale.realScale b := by ring
    _ = 8 * b * Real.log (b : ℝ) ^ (1 + Scale.delta b) := by rw [hscale]

end

end Erdos305

#print axioms Erdos305.erdos305
