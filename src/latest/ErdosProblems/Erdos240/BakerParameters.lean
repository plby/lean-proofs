/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Finset.Pi
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Parameters for the rational-prime van der Poorten--Loxton construction

This file fixes the elementary notation and parameter choices used by the
specialization of van der Poorten--Loxton's proof to rational primes.  The
data in `VDPLParameters` are a finite family of distinct old primes, a fresh
prime, the source coefficient bound `Bsrc ≥ exp 2`, and a finite list of
explicit lower bounds on `k`.  The latter is data, not an unproved
hypothesis: each later source inequality contributes its displayed real
right-hand side to this list.  All heights and auxiliary-function parameters
below are definitions derived from those data.

The explicit choices

* `mu = 1`, `kappa = 1/2`;
* `epsilon = 1 / (6 * (rank + 1))`;
* `sigma = 2 / (3 * (rank + 1))`;
* `q = 13` and a seed
  `k₀ = (64 * (rank + 1)) ^ (6 * (rank + 1))`

make the elementary radical-prime inequalities transparent.  In particular
the source's equation-(1) requirement
`(32 * (rank+1))^(1/epsilon) < k` holds strictly, hence
`q ≤ k ^ epsilon`, while `sigma + epsilon < 1`.  The definitions
`vdplRequirementBound` and `k` give the checked finite-maximum mechanism for
imposing all additional displayed requirements without changing the
dependency set.
The old logarithmic
height product is independent of the varying prime, as required for the
uniform Baker bound.
-/

namespace Erdos240

open scoped BigOperators NNReal
open Finset

noncomputable section

/-- Multi-indices for the normalized partial derivatives in the auxiliary
function. -/
abbrev VDPLMultiIndex (n : ℕ) := Fin n → ℕ

namespace VDPLMultiIndex

/-- Total order of a multi-index. -/
def weight {n : ℕ} (m : VDPLMultiIndex n) : ℕ :=
  ∑ i, m i

@[simp] theorem weight_zero (n : ℕ) :
    weight (0 : VDPLMultiIndex n) = 0 := by
  simp [weight]

theorem component_le_weight {n : ℕ} (m : VDPLMultiIndex n) (i : Fin n) :
    m i ≤ weight m := by
  classical
  exact Finset.single_le_sum (fun _ _ ↦ Nat.zero_le _) (Finset.mem_univ i)

end VDPLMultiIndex

/-- Vanishing at the rational grid `l / den`, with a radius and a total
multi-index budget.  This is the common conclusion of the two extrapolation
steps in the source. -/
def VanishesOn {n : ℕ}
    (F : ℂ → VDPLMultiIndex n → ℂ) (den R S : ℕ) : Prop :=
  ∀ l : ℕ, 1 ≤ l → l ≤ R →
    ∀ m, VDPLMultiIndex.weight m ≤ S →
      F ((l : ℂ) / (den : ℂ)) m = 0

namespace VanishesOn

/-- Restricting either the evaluation radius or the derivative budget
preserves vanishing. -/
theorem mono {n den R S R' S' : ℕ}
    {F : ℂ → VDPLMultiIndex n → ℂ}
    (h : VanishesOn F den R S) (hR : R' ≤ R) (hS : S' ≤ S) :
    VanishesOn F den R' S' := by
  intro l hl hle m hm
  exact h l hl (hle.trans hR) m (hm.trans hS)

theorem zero {n den R S : ℕ} :
    VanishesOn
      (fun (_ : ℂ) (_ : VDPLMultiIndex n) ↦ (0 : ℂ)) den R S := by
  simp [VanishesOn]

end VanishesOn

/-- Integral source bound used when the external real coefficient bound is
only assumed to be at least `exp 1`. -/
def vdplSourceBound (B : ℝ) : ℕ :=
  ⌈Real.exp 1 * B⌉₊

/-- A nonnegative number dominating every member of a finite family of
explicit real lower bounds.  A sum of positive parts is used instead of a
finite maximum so no exceptional empty-family case is needed. -/
def vdplRequirementBound (requirements : Finset ℝ) : ℝ :=
  ∑ x ∈ requirements, max 0 x

theorem mem_le_vdplRequirementBound {requirements : Finset ℝ} {x : ℝ}
    (hx : x ∈ requirements) : x ≤ vdplRequirementBound requirements := by
  have hxmax : x ≤ max 0 x := le_max_right _ _
  have hterm : max 0 x ≤ ∑ y ∈ requirements, max 0 y := by
    exact Finset.single_le_sum
      (fun y hy ↦ le_max_left 0 y) hx
  exact hxmax.trans hterm

theorem vdplRequirementBound_nonneg (requirements : Finset ℝ) :
    0 ≤ vdplRequirementBound requirements := by
  exact Finset.sum_nonneg fun x _ ↦ le_max_left 0 x

/-- Rescaling an external bound `B ≥ e` by a single factor of `e` makes
the source bound at least `e²`. -/
theorem exp_two_le_vdplSourceBound_cast {B : ℝ}
    (hB : Real.exp 1 ≤ B) :
    Real.exp 2 ≤ (vdplSourceBound B : ℝ) := by
  calc
    Real.exp 2 = Real.exp 1 * Real.exp 1 := by
      rw [← Real.exp_add]
      norm_num
    _ ≤ Real.exp 1 * B := mul_le_mul_of_nonneg_left hB (Real.exp_pos 1).le
    _ ≤ (vdplSourceBound B : ℕ) := Nat.le_ceil _

/-- Every coefficient bounded by the external `B` is still bounded by the
rescaled integral source bound. -/
theorem le_vdplSourceBound_cast {B : ℝ} (hB : Real.exp 1 ≤ B) :
    B ≤ (vdplSourceBound B : ℝ) := by
  calc
    B ≤ Real.exp 1 * B := by
      have hBpos : 0 ≤ B := (Real.exp_pos 1).le.trans hB
      exact le_mul_of_one_le_left hBpos (by
        rw [← Real.exp_zero]
        exact Real.exp_le_exp.mpr (by norm_num))
    _ ≤ (vdplSourceBound B : ℕ) := Nat.le_ceil _

theorem vdplSourceBound_cast_lt_add_one (B : ℝ) (hB : 0 ≤ B) :
    (vdplSourceBound B : ℝ) < Real.exp 1 * B + 1 := by
  exact Nat.ceil_lt_add_one (mul_nonneg (Real.exp_pos 1).le hB)

/-- The ceiling costs only an absolute factor. -/
theorem vdplSourceBound_cast_le_two_mul_exp_mul {B : ℝ}
    (hB : Real.exp 1 ≤ B) :
    (vdplSourceBound B : ℝ) ≤ 2 * Real.exp 1 * B := by
  have hBpos : 0 < B := (Real.exp_pos 1).trans_le hB
  have hone : (1 : ℝ) ≤ Real.exp 1 * B := by
    nlinarith [Real.exp_one_gt_two, Real.exp_pos (1 : ℝ)]
  have hceil := vdplSourceBound_cast_lt_add_one B hBpos.le
  linarith

/-- The logarithm of the integral source bound is at most three times the
external logarithm.  This is the normalization used to pass the source's
`Bsrc ≥ e²` theorem to the cleaner external hypothesis `B ≥ e`. -/
theorem log_vdplSourceBound_cast_le_three_mul_log {B : ℝ}
    (hB : Real.exp 1 ≤ B) :
    Real.log (vdplSourceBound B : ℝ) ≤ 3 * Real.log B := by
  have hBpos : 0 < B := (Real.exp_pos 1).trans_le hB
  have hsourcePos : 0 < (vdplSourceBound B : ℝ) :=
    (Real.exp_pos 2).trans_le (exp_two_le_vdplSourceBound_cast hB)
  have hmajorPos : 0 < 2 * Real.exp 1 * B := by positivity
  have hlogMajor : Real.log (vdplSourceBound B : ℝ) ≤
      Real.log (2 * Real.exp 1 * B) :=
    Real.log_le_log hsourcePos (vdplSourceBound_cast_le_two_mul_exp_mul hB)
  have hlogFormula : Real.log (2 * Real.exp 1 * B) =
      Real.log 2 + 1 + Real.log B := by
    rw [Real.log_mul (by positivity : (2 * Real.exp 1 : ℝ) ≠ 0) hBpos.ne',
      Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) (Real.exp_ne_zero 1),
      Real.log_exp]
  have hlogTwo : Real.log (2 : ℝ) ≤ 1 := by
    have := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    norm_num at this ⊢
    exact this
  have honeLog : 1 ≤ Real.log B := by
    rw [← Real.log_exp (1 : ℝ)]
    exact Real.strictMonoOn_log.monotoneOn
      (Real.exp_pos 1) hBpos hB
  rw [hlogFormula] at hlogMajor
  linarith

/-- Input data for the specialized rational-prime construction.  No
analytic or number-theoretic conclusion is included as a field. -/
structure VDPLParameters (ι : Type*) [Fintype ι] where
  old : ι → ℕ
  old_prime : ∀ i, (old i).Prime
  old_injective : Function.Injective old
  newPrime : ℕ
  new_prime : newPrime.Prime
  new_fresh : ∀ i, old i ≠ newPrime
  /-- Integer coefficient bound used by the source. -/
  Bsrc : ℕ
  Bsrc_lower : Real.exp 2 ≤ (Bsrc : ℝ)
  /-- Explicit additional lower bounds required by later source estimates.
  The rational-prime specialization constructs this finite list from the
  rank and the fixed old heights. -/
  kRequirements : Finset ℝ

namespace VDPLParameters

variable {ι : Type*} [Fintype ι] (P : VDPLParameters ι)

/-- Number of logarithms after adjoining the varying prime. -/
def rank (_P : VDPLParameters ι) : ℕ := Fintype.card ι + 1

/-- The source's auxiliary prime. -/
def q (_P : VDPLParameters ι) : ℕ := 13

/-- A source-normalized height for each fixed old prime.  The floor
`exp (exp 1)` is exactly what ensures `log log A_i ≥ 1`. -/
def oldHeight (P : VDPLParameters ι) (i : ι) : ℝ :=
  max (Real.exp (Real.exp 1)) ((P.old i : ℝ) + 1)

/-- Height of the varying prime before making it the largest height. -/
def varyingHeight (P : VDPLParameters ι) : ℝ :=
  max (Real.exp (Real.exp 1)) ((P.newPrime : ℝ) + 1)

/-- Product of the fixed old heights. -/
def fixedHeightProduct (P : VDPLParameters ι) : ℝ :=
  ∏ i, P.oldHeight i

/-- A largest-height substitute.  Multiplying by all fixed heights rather
than taking a finite maximum makes its dependence particularly explicit and
still gives a valid (larger) height bound. -/
def newHeight (P : VDPLParameters ι) : ℝ :=
  P.fixedHeightProduct * P.varyingHeight

/-- Product of the logarithmic heights of the fixed old primes. -/
def OmegaOld (P : VDPLParameters ι) : ℝ :=
  ∏ i, Real.log (P.oldHeight i)

/-- Full height product, with the varying height kept as the last factor. -/
def Omega (P : VDPLParameters ι) : ℝ :=
  P.OmegaOld * Real.log P.newHeight

/-- Constant, depending only on the old primes, which absorbs the fixed
height product while leaving one visible factor `log newPrime`. -/
def heightConstant (P : VDPLParameters ι) : ℝ :=
  4 + Real.log P.fixedHeightProduct / Real.log 2

/-- `μ` in the source. -/
def mu (_P : VDPLParameters ι) : ℝ := 1

/-- `κ` in the source. -/
def kappa (_P : VDPLParameters ι) : ℝ := 1 / 2

/-- `ε = (μ-κ)/((1+μ)(1+κ)(rank+1))`. -/
def epsilon (P : VDPLParameters ι) : ℝ :=
  (P.mu - P.kappa) /
    ((1 + P.mu) * (1 + P.kappa) * (P.rank + 1 : ℝ))

/-- `σ = 1/((1+κ)(rank+1))`. -/
def sigma (P : VDPLParameters ι) : ℝ :=
  1 / ((1 + P.kappa) * (P.rank + 1 : ℝ))

/-- The natural exponent used in the explicit choice of `k`. -/
def kExponent (P : VDPLParameters ι) : ℕ := 6 * (P.rank + 1)

/-- Base of the seed power. -/
def kSeedBase (P : VDPLParameters ι) : ℝ :=
  64 * (P.rank + 1 : ℝ)

/-- Seed parameter already large enough for the corrected equation (1). -/
def kSeed (P : VDPLParameters ι) : ℝ :=
  P.kSeedBase ^ P.kExponent

/-- The right side of source equation (1) after substituting
`epsilon = 1 / kExponent` and `D = 1`. -/
def equationOneThreshold (P : VDPLParameters ι) : ℝ :=
  (32 * (P.rank + 1 : ℝ)) ^ P.kExponent

/-- Actual source parameter.  Every source quantity `C`, `Slevel`, `Sstep`,
`levelBound`, and the side lengths below depends on this enlarged value. -/
def k (P : VDPLParameters ι) : ℝ :=
  P.kSeed + vdplRequirementBound P.kRequirements + 1

/-- Enlarge the baseline `k` so that it strictly dominates every member of
a finite list of explicit source requirements.  If the requirement list is
defined from `rank` and the old heights, this operation preserves exactly
the uniformity needed in the final varying-prime bound. -/
def enlargedK (P : VDPLParameters ι) (requirements : Finset ℝ) : ℝ :=
  P.k + vdplRequirementBound requirements + 1

/-- The constant denoted `C = k^(1+μ)` in the source. -/
def C (P : VDPLParameters ι) : ℝ := P.k ^ (1 + P.mu)

/-- The source's integral coefficient-height parameter. -/
def h (P : VDPLParameters ι) : ℕ := ⌊Real.log P.Bsrc⌋₊

/-- `q^{-J}`, written without a negative real power. -/
def qInvPow (P : VDPLParameters ι) (J : ℕ) : ℝ :=
  (((P.q ^ J : ℕ) : ℝ))⁻¹

/-- The common real expression inside the two derivative-budget floors. -/
def levelScale (P : VDPLParameters ι) (J : ℕ) : ℝ :=
  P.qInvPow J * P.k * P.Omega * Real.log P.OmegaOld

/-- Derivative budget at level `J`. -/
def Slevel (P : VDPLParameters ι) (J : ℕ) : ℕ :=
  ⌊P.levelScale J⌋₊

/-- The loss parameter `ε_J = max(ε, 3/k^(ε J))` in source Lemma 4.
It is used only for positive interpolation indices; the exceptional first
step is recorded separately in `lemmaFourBudget`. -/
def lemmaFourEpsilon (P : VDPLParameters ι) (J : ℕ) : ℝ :=
  max P.epsilon (3 / P.k ^ (P.epsilon * (J : ℝ)))

/-- Exact derivative-budget recursion in source Lemma 4.  At a fixed outer
level `N`, the source starts with `S₀ = Slevel N`, sets
`S₁ = floor(S₀/2)`, and, for `J ≥ 1`, sets
`S_(J+1) = floor((1-ε_J) S_J)`. -/
def lemmaFourBudget (P : VDPLParameters ι) (N : ℕ) : ℕ → ℕ
  | 0 => P.Slevel N
  | 1 => ⌊(P.Slevel N : ℝ) / 2⌋₊
  | J + 2 =>
      ⌊(1 - P.lemmaFourEpsilon (J + 1)) *
        (P.lemmaFourBudget N (J + 1) : ℝ)⌋₊

/-- Real interpolation radius in source Lemma 4, specialized to `D = 1`:
`16 q^N h k^(ε J)`. -/
def lemmaFourRadiusScale (P : VDPLParameters ι) (N J : ℕ) : ℝ :=
  16 * ((P.q ^ N : ℕ) : ℝ) * P.h *
    P.k ^ (P.epsilon * (J : ℝ))

/-- Integral radius obtained by flooring the source's real Lemma 4 radius. -/
def lemmaFourRadius (P : VDPLParameters ι) (N J : ℕ) : ℕ :=
  ⌊P.lemmaFourRadiusScale N J⌋₊

/-- A deliberately conservative budget used by the subsequent rational-grid
step.  It is weaker than the exact first Lemma 4 budget `floor(S₀/2)`;
keeping it explicit is useful because `Slevel (J+1) ≤ Sstep J` follows from
the fixed auxiliary prime `q = 13`. -/
def Sstep (P : VDPLParameters ι) (J : ℕ) : ℕ :=
  ⌊P.levelScale J / 9⌋₊

/-- Radius of the integral/rational interpolation grid.  The displayed
floor in the source is redundant because every factor is integral. -/
def R (P : VDPLParameters ι) (J : ℕ) : ℕ :=
  16 * P.q ^ J * P.h

/-- Right side of the source's admissible-level inequality. -/
def levelBound (P : VDPLParameters ι) : ℝ :=
  (8 * P.rank : ℝ)⁻¹ *
    P.k ^ (1 - (P.sigma - P.epsilon)) *
      P.OmegaOld * Real.log P.OmegaOld

/-- The source's strict inequality allowing an induction level `J`. -/
def LevelOK (P : VDPLParameters ι) (J : ℕ) : Prop :=
  ((P.q ^ J : ℕ) : ℝ) < P.levelBound

/-- Nonstrict terminal upper bound.  The final source index may lie exactly
on `levelBound`, while every earlier induction level satisfies `LevelOK`. -/
def LevelWithin (P : VDPLParameters ι) (J : ℕ) : Prop :=
  ((P.q ^ J : ℕ) : ℝ) ≤ P.levelBound

/-- `L_{-1}+1` in the source. -/
def LminusOnePlusOne (P : VDPLParameters ι) : ℕ := P.h

/-- Maximum exponent `L_{-1}`; the source specifies its successor. -/
def LminusOne (P : VDPLParameters ι) : ℕ :=
  P.LminusOnePlusOne - 1

/-- Real side length whose floor is `L_0+1`. -/
def LzeroScale (P : VDPLParameters ι) : ℝ :=
  (1 / 8 : ℝ) * P.k ^ (1 - P.sigma) * P.Omega

/-- `L_0+1 = floor((1/8) k^(1-σ) Ω)` in the source. -/
def LzeroPlusOne (P : VDPLParameters ι) : ℕ :=
  ⌊P.LzeroScale⌋₊

/-- Maximum exponent `L_0`; keeping the subtraction here prevents the
off-by-one error of using the number of choices as the maximum exponent. -/
def Lzero (P : VDPLParameters ι) : ℕ :=
  P.LzeroPlusOne - 1

/-- Real initial side length corresponding to an old logarithm. -/
def LiZeroScale (P : VDPLParameters ι) (i : ι) : ℝ :=
  (8 * P.rank : ℝ)⁻¹ * P.k ^ (1 - P.sigma) *
    P.Omega * Real.log P.OmegaOld / Real.log (P.oldHeight i)

/-- Initial side length corresponding to an old logarithm. -/
def LiZero (P : VDPLParameters ι) (i : ι) : ℕ :=
  ⌊P.LiZeroScale i⌋₊

/-- Initial side length for the varying last logarithm, the source's
`L_n`.  Keeping this side explicit is essential for the final degree count. -/
def LlastZeroScale (P : VDPLParameters ι) : ℝ :=
  (8 * P.rank : ℝ)⁻¹ * P.k ^ (1 - P.sigma) *
    P.Omega * Real.log P.OmegaOld / Real.log P.newHeight

/-- Floor of the last-logarithm side length. -/
def LlastZero (P : VDPLParameters ι) : ℕ :=
  ⌊P.LlastZeroScale⌋₊

/-- Uniform auxiliary coefficient height in Lemmas 2--6. -/
def coeffHeight (P : VDPLParameters ι) : ℝ :=
  Real.exp ((1 / 3 : ℝ) * P.h * P.k * P.Omega * Real.log P.OmegaOld)

@[simp] theorem rank_eq : P.rank = Fintype.card ι + 1 := rfl

theorem rank_pos : 0 < P.rank := by
  simp [rank]

theorem one_le_rank : 1 ≤ P.rank := P.rank_pos

theorem two_le_rank [Nonempty ι] : 2 ≤ P.rank := by
  have hcard : 0 < Fintype.card ι := Fintype.card_pos
  simp only [rank]
  omega

@[simp] theorem q_eq : P.q = 13 := rfl

theorem q_prime : P.q.Prime := by
  simpa [q] using (by decide : Nat.Prime 13)

theorem thirteen_le_q : 13 ≤ P.q := by
  simp [q]

theorem one_lt_q : 1 < P.q := by
  simp [q]

theorem sourceHeight_le_oldHeight (i : ι) :
    Real.exp (Real.exp 1) ≤ P.oldHeight i := by
  exact le_max_left _ _

theorem oldHeight_lower (i : ι) : Real.exp 2 ≤ P.oldHeight i := by
  exact (Real.exp_le_exp.mpr Real.exp_one_gt_two.le).trans
    (P.sourceHeight_le_oldHeight i)

theorem oldHeight_pos (i : ι) : 0 < P.oldHeight i :=
  (Real.exp_pos 2).trans_le (P.oldHeight_lower i)

/-- The height majorant is strict, as required by the corrigendum. -/
theorem old_cast_lt_oldHeight (i : ι) :
    (P.old i : ℝ) < P.oldHeight i := by
  exact (lt_add_one (P.old i : ℝ)).trans_le (le_max_right _ _)

theorem two_le_log_oldHeight (i : ι) :
    2 ≤ Real.log (P.oldHeight i) := by
  rw [← Real.log_exp (2 : ℝ)]
  exact Real.strictMonoOn_log.monotoneOn
    (Real.exp_pos 2) (P.oldHeight_pos i) (P.oldHeight_lower i)

theorem exp_one_le_log_oldHeight (i : ι) :
    Real.exp 1 ≤ Real.log (P.oldHeight i) := by
  rw [← Real.log_exp (Real.exp 1)]
  exact Real.strictMonoOn_log.monotoneOn
    (Real.exp_pos (Real.exp 1)) (P.oldHeight_pos i)
      (P.sourceHeight_le_oldHeight i)

theorem log_oldHeight_pos (i : ι) :
    0 < Real.log (P.oldHeight i) :=
  lt_of_lt_of_le (by norm_num) (P.two_le_log_oldHeight i)

theorem one_le_log_log_oldHeight (i : ι) :
    1 ≤ Real.log (Real.log (P.oldHeight i)) := by
  rw [← Real.log_exp (1 : ℝ)]
  exact Real.strictMonoOn_log.monotoneOn
    (Real.exp_pos 1) (P.log_oldHeight_pos i) (P.exp_one_le_log_oldHeight i)

theorem sourceHeight_le_varyingHeight :
    Real.exp (Real.exp 1) ≤ P.varyingHeight :=
  le_max_left _ _

theorem varyingHeight_lower : Real.exp 2 ≤ P.varyingHeight :=
  (Real.exp_le_exp.mpr Real.exp_one_gt_two.le).trans
    P.sourceHeight_le_varyingHeight

theorem varyingHeight_pos : 0 < P.varyingHeight :=
  (Real.exp_pos 2).trans_le P.varyingHeight_lower

/-- Strict majorization of the varying prime by its source height. -/
theorem newPrime_cast_lt_varyingHeight :
    (P.newPrime : ℝ) < P.varyingHeight := by
  exact (lt_add_one (P.newPrime : ℝ)).trans_le (le_max_right _ _)

theorem one_lt_varyingHeight : 1 < P.varyingHeight := by
  have : (1 : ℝ) < Real.exp 2 := by
    rw [← Real.exp_zero]
    exact Real.exp_lt_exp.mpr (by norm_num)
  exact this.trans_le P.varyingHeight_lower

theorem exp_one_le_log_varyingHeight :
    Real.exp 1 ≤ Real.log P.varyingHeight := by
  rw [← Real.log_exp (Real.exp 1)]
  exact Real.strictMonoOn_log.monotoneOn
    (Real.exp_pos (Real.exp 1)) P.varyingHeight_pos
      P.sourceHeight_le_varyingHeight

theorem one_le_log_log_varyingHeight :
    1 ≤ Real.log (Real.log P.varyingHeight) := by
  rw [← Real.log_exp (1 : ℝ)]
  exact Real.strictMonoOn_log.monotoneOn
    (Real.exp_pos 1) (lt_of_lt_of_le (Real.exp_pos 1)
      P.exp_one_le_log_varyingHeight) P.exp_one_le_log_varyingHeight

theorem fixedHeightProduct_pos : 0 < P.fixedHeightProduct := by
  unfold fixedHeightProduct
  exact Finset.prod_pos fun i _ ↦ P.oldHeight_pos i

theorem one_le_fixedHeightProduct : 1 ≤ P.fixedHeightProduct := by
  unfold fixedHeightProduct
  exact Finset.one_le_prod fun i _ ↦ (by
    have : (1 : ℝ) < Real.exp 2 := by
      rw [← Real.exp_zero]
      exact Real.exp_lt_exp.mpr (by norm_num)
    exact (this.trans_le (P.oldHeight_lower i)).le)

theorem log_fixedHeightProduct_nonneg :
    0 ≤ Real.log P.fixedHeightProduct :=
  Real.log_nonneg P.one_le_fixedHeightProduct

theorem two_le_newPrime : 2 ≤ P.newPrime := P.new_prime.two_le

theorem newPrime_pos : 0 < P.newPrime :=
  lt_of_lt_of_le (by norm_num) P.two_le_newPrime

/-- The varying height is bounded by a fixed power of the varying prime.
The exponent four is deliberately generous and covers the small primes. -/
theorem varyingHeight_le_newPrime_pow_four :
    P.varyingHeight ≤ (P.newPrime : ℝ) ^ 4 := by
  have hpR : (2 : ℝ) ≤ P.newPrime := by exact_mod_cast P.two_le_newPrime
  have hinner : Real.exp 1 < 4 * Real.log 2 := by
    nlinarith [Real.exp_one_lt_d9, Real.log_two_gt_d9]
  have hsource : Real.exp (Real.exp 1) < (16 : ℝ) := by
    calc
      Real.exp (Real.exp 1) < Real.exp (4 * Real.log 2) :=
        Real.exp_lt_exp.mpr hinner
      _ = 16 := by
        calc
          Real.exp (4 * Real.log 2) =
              Real.exp (Real.log ((2 : ℝ) ^ 4)) := by
            congr 1
            rw [Real.log_pow]
            norm_num
          _ = (2 : ℝ) ^ 4 := Real.exp_log (by positivity)
          _ = 16 := by norm_num
  apply max_le
  · calc
      Real.exp (Real.exp 1) ≤ 16 := hsource.le
      _ = (2 : ℝ) ^ 4 := by norm_num
      _ ≤ (P.newPrime : ℝ) ^ 4 :=
        pow_le_pow_left₀ (by norm_num) hpR 4
  · calc
      (P.newPrime : ℝ) + 1 ≤ (P.newPrime : ℝ) ^ 2 := by
        have hpOne : (1 : ℝ) ≤ P.newPrime := by
          exact_mod_cast P.two_le_newPrime.trans' (by norm_num)
        calc
          (P.newPrime : ℝ) + 1 ≤
              (P.newPrime : ℝ) + P.newPrime :=
            by linarith
          _ = 2 * (P.newPrime : ℝ) := by ring
          _ ≤ (P.newPrime : ℝ) * P.newPrime := by
            exact mul_le_mul_of_nonneg_right hpR (by positivity)
          _ = (P.newPrime : ℝ) ^ 2 := by ring
      _ ≤ (P.newPrime : ℝ) ^ 4 := by
        exact pow_le_pow_right₀
          (by exact_mod_cast P.two_le_newPrime.trans' (by norm_num)) (by norm_num)

theorem log_varyingHeight_le_four_mul_log_newPrime :
    Real.log P.varyingHeight ≤ 4 * Real.log (P.newPrime : ℝ) := by
  calc
    Real.log P.varyingHeight ≤ Real.log ((P.newPrime : ℝ) ^ 4) :=
      Real.log_le_log P.varyingHeight_pos P.varyingHeight_le_newPrime_pow_four
    _ = 4 * Real.log (P.newPrime : ℝ) := by rw [Real.log_pow]; norm_num

theorem log_two_pos : 0 < Real.log (2 : ℝ) :=
  Real.log_pos (by norm_num)

theorem log_two_le_log_newPrime :
    Real.log (2 : ℝ) ≤ Real.log (P.newPrime : ℝ) := by
  exact Real.log_le_log (by norm_num) (by exact_mod_cast P.two_le_newPrime)

theorem heightConstant_pos : 0 < P.heightConstant := by
  unfold heightConstant
  have := div_nonneg P.log_fixedHeightProduct_nonneg log_two_pos.le
  linarith

/-- Height normalization with the varying logarithm left visible.  The
constant on the right depends only on the fixed old family. -/
theorem log_newHeight_le_heightConstant_mul_log_newPrime :
    Real.log P.newHeight ≤
      P.heightConstant * Real.log (P.newPrime : ℝ) := by
  have hpLog : 0 < Real.log (P.newPrime : ℝ) :=
    Real.log_pos (by exact_mod_cast P.new_prime.one_lt)
  have hratio : 1 ≤
      Real.log (P.newPrime : ℝ) / Real.log 2 := by
    apply (le_div_iff₀ log_two_pos).2
    simpa using P.log_two_le_log_newPrime
  have hfixed : Real.log P.fixedHeightProduct ≤
      Real.log P.fixedHeightProduct *
        (Real.log (P.newPrime : ℝ) / Real.log 2) :=
    le_mul_of_one_le_right P.log_fixedHeightProduct_nonneg hratio
  rw [newHeight,
    Real.log_mul P.fixedHeightProduct_pos.ne' P.varyingHeight_pos.ne',
    heightConstant]
  calc
    Real.log P.fixedHeightProduct + Real.log P.varyingHeight ≤
        Real.log P.fixedHeightProduct +
          4 * Real.log (P.newPrime : ℝ) :=
      add_le_add le_rfl P.log_varyingHeight_le_four_mul_log_newPrime
    _ ≤ Real.log P.fixedHeightProduct *
          (Real.log (P.newPrime : ℝ) / Real.log 2) +
            4 * Real.log (P.newPrime : ℝ) :=
      add_le_add hfixed le_rfl
    _ = (4 + Real.log P.fixedHeightProduct / Real.log 2) *
          Real.log (P.newPrime : ℝ) := by field_simp; ring

theorem newHeight_pos : 0 < P.newHeight := by
  unfold newHeight
  exact mul_pos (Finset.prod_pos fun i _ ↦ P.oldHeight_pos i) P.varyingHeight_pos

theorem varyingHeight_le_newHeight : P.varyingHeight ≤ P.newHeight := by
  unfold newHeight
  simpa using mul_le_mul_of_nonneg_right P.one_le_fixedHeightProduct
    P.varyingHeight_pos.le

theorem oldHeight_le_fixedHeightProduct (i : ι) :
    P.oldHeight i ≤ P.fixedHeightProduct := by
  classical
  unfold fixedHeightProduct
  have herase : 1 ≤ ∏ j ∈ (Finset.univ.erase i), P.oldHeight j := by
    exact Finset.one_le_prod fun j _ ↦ (by
      have hone : (1 : ℝ) ≤ Real.exp 2 := by
        rw [← Real.exp_zero]
        exact Real.exp_le_exp.mpr (by norm_num)
      exact hone.trans (P.oldHeight_lower j))
  calc
    P.oldHeight i = P.oldHeight i * 1 := by ring
    _ ≤ P.oldHeight i * ∏ j ∈ (Finset.univ.erase i), P.oldHeight j :=
      mul_le_mul_of_nonneg_left herase (P.oldHeight_pos i).le
    _ = ∏ j, P.oldHeight j :=
      Finset.mul_prod_erase Finset.univ P.oldHeight (Finset.mem_univ i)

theorem oldHeight_le_newHeight (i : ι) : P.oldHeight i ≤ P.newHeight := by
  exact (P.oldHeight_le_fixedHeightProduct i).trans (by
    unfold newHeight
    calc
      P.fixedHeightProduct = P.fixedHeightProduct * 1 := by ring
      _ ≤ P.fixedHeightProduct * P.varyingHeight :=
        mul_le_mul_of_nonneg_left P.one_lt_varyingHeight.le
          P.fixedHeightProduct_pos.le)

theorem one_lt_newHeight : 1 < P.newHeight := by
  unfold newHeight fixedHeightProduct
  have hprod : 1 ≤ ∏ i, P.oldHeight i := by
    exact Finset.one_le_prod fun i _ ↦ (by
      exact (le_of_lt (by
        have : (1 : ℝ) < Real.exp 2 := by
          rw [← Real.exp_zero]
          exact Real.exp_lt_exp.mpr (by norm_num)
        exact this.trans_le (P.oldHeight_lower i))))
  exact P.one_lt_varyingHeight.trans_le (by
    simpa using
      mul_le_mul_of_nonneg_right hprod (le_of_lt P.varyingHeight_pos))

theorem log_newHeight_pos : 0 < Real.log P.newHeight :=
  Real.log_pos P.one_lt_newHeight

theorem exp_one_le_log_newHeight :
    Real.exp 1 ≤ Real.log P.newHeight := by
  exact P.exp_one_le_log_varyingHeight.trans
    (Real.log_le_log P.varyingHeight_pos P.varyingHeight_le_newHeight)

theorem one_le_log_log_newHeight :
    1 ≤ Real.log (Real.log P.newHeight) := by
  rw [← Real.log_exp (1 : ℝ)]
  exact Real.strictMonoOn_log.monotoneOn
    (Real.exp_pos 1) P.log_newHeight_pos P.exp_one_le_log_newHeight

theorem OmegaOld_pos : 0 < P.OmegaOld := by
  unfold OmegaOld
  exact Finset.prod_pos fun i _ ↦ P.log_oldHeight_pos i

theorem one_le_OmegaOld : 1 ≤ P.OmegaOld := by
  unfold OmegaOld
  exact Finset.one_le_prod fun i _ ↦ (by
    exact (by norm_num : (1 : ℝ) ≤ 2).trans (P.two_le_log_oldHeight i))

theorem one_le_log_newHeight : 1 ≤ Real.log P.newHeight := by
  have he : (1 : ℝ) ≤ Real.exp 1 := by
    nlinarith [Real.exp_one_gt_two]
  exact he.trans P.exp_one_le_log_newHeight

theorem one_le_Omega : 1 ≤ P.Omega := by
  unfold Omega
  calc
    (1 : ℝ) = 1 * 1 := by ring
    _ ≤ P.OmegaOld * Real.log P.newHeight :=
      mul_le_mul P.one_le_OmegaOld P.one_le_log_newHeight (by norm_num)
        P.OmegaOld_pos.le

theorem two_pow_card_le_OmegaOld :
    (2 : ℝ) ^ Fintype.card ι ≤ P.OmegaOld := by
  classical
  unfold OmegaOld
  calc
    (2 : ℝ) ^ Fintype.card ι = ∏ _ : ι, (2 : ℝ) := by simp
    _ ≤ ∏ i, Real.log (P.oldHeight i) :=
      Finset.prod_le_prod (fun _ _ ↦ by norm_num) fun i _ ↦
        P.two_le_log_oldHeight i

private theorem card_succ_le_two_pow {c : ℕ} (hc : 1 ≤ c) :
    c + 1 ≤ 2 ^ c := by
  induction c with
  | zero => omega
  | succ c ih =>
      by_cases hc0 : c = 0
      · simp [hc0]
      · have hcpos : 1 ≤ c := Nat.one_le_iff_ne_zero.2 hc0
        have hrec := ih hcpos
        rw [pow_succ]
        omega

theorem rank_le_OmegaOld [Nonempty ι] : (P.rank : ℝ) ≤ P.OmegaOld := by
  have hcard : 1 ≤ Fintype.card ι := by
    have hpos : 0 < Fintype.card ι := Fintype.card_pos
    omega
  have hnat : P.rank ≤ 2 ^ Fintype.card ι := by
    simpa [rank] using card_succ_le_two_pow hcard
  exact (by exact_mod_cast hnat : (P.rank : ℝ) ≤
    (2 : ℝ) ^ Fintype.card ι).trans P.two_pow_card_le_OmegaOld

theorem one_lt_OmegaOld [Nonempty ι] : 1 < P.OmegaOld := by
  have hcard : 0 < Fintype.card ι := Fintype.card_pos
  have hpow : (1 : ℝ) < 2 ^ Fintype.card ι := by
    exact one_lt_pow₀ (by norm_num) hcard.ne'
  exact hpow.trans_le P.two_pow_card_le_OmegaOld

theorem log_OmegaOld_pos [Nonempty ι] : 0 < Real.log P.OmegaOld :=
  Real.log_pos P.one_lt_OmegaOld

theorem log_two_le_log_OmegaOld [Nonempty ι] :
    Real.log (2 : ℝ) ≤ Real.log P.OmegaOld := by
  have : (2 : ℝ) ≤ P.OmegaOld := by
    exact (show (2 : ℝ) ≤ P.rank by
      exact_mod_cast (show 2 ≤ P.rank by
        have hc : 0 < Fintype.card ι := Fintype.card_pos
        simp only [rank]
        omega)).trans P.rank_le_OmegaOld
  exact Real.log_le_log (by norm_num) this

theorem Omega_pos : 0 < P.Omega := by
  exact mul_pos P.OmegaOld_pos P.log_newHeight_pos

@[simp] theorem mu_eq : P.mu = 1 := rfl

@[simp] theorem kappa_eq : P.kappa = 1 / 2 := rfl

theorem mu_lt_two : P.mu < 2 := by norm_num [mu]

theorem kappa_pos : 0 < P.kappa := by norm_num [kappa]

theorem kappa_le_mu_div_two : P.kappa ≤ P.mu / 2 := by norm_num [kappa, mu]

theorem two_div_rank_add_one_le_mu :
    2 / (P.rank + 1 : ℝ) ≤ P.mu := by
  rw [mu]
  have hrank : (2 : ℝ) ≤ (P.rank : ℝ) + 1 := by
    exact_mod_cast Nat.succ_le_succ P.one_le_rank
  exact (div_le_one (by positivity)).2 hrank

theorem epsilon_eq :
    P.epsilon = 1 / (6 * (P.rank + 1 : ℝ)) := by
  unfold epsilon mu kappa
  field_simp
  ring

theorem sigma_eq :
    P.sigma = 2 / (3 * (P.rank + 1 : ℝ)) := by
  unfold sigma kappa
  field_simp
  ring

theorem epsilon_pos : 0 < P.epsilon := by
  rw [P.epsilon_eq]
  positivity

theorem sigma_pos : 0 < P.sigma := by
  rw [P.sigma_eq]
  positivity

theorem sigma_add_epsilon_eq :
    P.sigma + P.epsilon = 5 / (6 * (P.rank + 1 : ℝ)) := by
  rw [P.sigma_eq, P.epsilon_eq]
  field_simp
  ring

theorem sigma_add_epsilon_lt_one : P.sigma + P.epsilon < 1 := by
  rw [P.sigma_add_epsilon_eq]
  have hrank : (2 : ℝ) ≤ (P.rank + 1 : ℕ) := by
    exact_mod_cast Nat.succ_le_succ P.one_le_rank
  have : (5 : ℝ) < 6 * (P.rank + 1 : ℝ) := by nlinarith
  exact (div_lt_one (by positivity)).2 this

theorem one_sub_sigma_epsilon_pos :
    0 < 1 - (P.sigma + P.epsilon) := by
  linarith [P.sigma_add_epsilon_lt_one]

theorem epsilon_le_one_sub_sigma_add_epsilon :
    P.epsilon ≤ 1 - (P.sigma + P.epsilon) := by
  rw [P.sigma_eq, P.epsilon_eq]
  have hrank : (1 : ℝ) ≤ P.rank + 1 := by
    exact_mod_cast Nat.le_add_left 1 P.rank
  field_simp
  nlinarith

@[simp] theorem kExponent_eq : P.kExponent = 6 * (P.rank + 1) := rfl

theorem kExponent_pos : 0 < P.kExponent := by
  simp [kExponent]

theorem kSeedBase_pos : 0 < P.kSeedBase := by
  unfold kSeedBase
  positivity

theorem one_le_kSeedBase : 1 ≤ P.kSeedBase := by
  unfold kSeedBase
  have hrank0 : (0 : ℝ) ≤ P.rank := by positivity
  nlinarith

theorem kSeed_pos : 0 < P.kSeed := by
  unfold kSeed
  exact pow_pos P.kSeedBase_pos _

theorem one_le_kSeed : 1 ≤ P.kSeed := by
  unfold kSeed
  exact one_le_pow₀ P.one_le_kSeedBase

theorem kSeed_lt_k : P.kSeed < P.k := by
  unfold k
  have := vdplRequirementBound_nonneg P.kRequirements
  linarith

theorem k_pos : 0 < P.k := by
  exact P.kSeed_pos.trans P.kSeed_lt_k

theorem one_le_k : 1 ≤ P.k := by
  exact P.one_le_kSeed.trans P.kSeed_lt_k.le

theorem requirement_lt_k {x : ℝ} (hx : x ∈ P.kRequirements) : x < P.k := by
  unfold k
  have hxbound := mem_le_vdplRequirementBound hx
  have hkseed := P.kSeed_pos
  linarith

theorem k_lt_enlargedK (requirements : Finset ℝ) :
    P.k < P.enlargedK requirements := by
  unfold enlargedK
  have := vdplRequirementBound_nonneg requirements
  linarith

theorem requirement_lt_enlargedK {requirements : Finset ℝ} {x : ℝ}
    (hx : x ∈ requirements) : x < P.enlargedK requirements := by
  unfold enlargedK
  have hxbound := mem_le_vdplRequirementBound hx
  have hk := P.k_pos
  linarith

theorem enlargedK_pos (requirements : Finset ℝ) :
    0 < P.enlargedK requirements :=
  P.k_pos.trans (P.k_lt_enlargedK requirements)

theorem kExponent_mul_epsilon : (P.kExponent : ℝ) * P.epsilon = 1 := by
  rw [P.epsilon_eq]
  unfold kExponent
  push_cast
  field_simp

theorem epsilon_inv_eq_kExponent : P.epsilon⁻¹ = (P.kExponent : ℝ) := by
  calc
    P.epsilon⁻¹ = P.epsilon⁻¹ *
        ((P.kExponent : ℝ) * P.epsilon) := by
      rw [P.kExponent_mul_epsilon, mul_one]
    _ = (P.kExponent : ℝ) := by
      field_simp [P.epsilon_pos.ne']

theorem kSeed_rpow_epsilon_eq_kSeedBase :
    P.kSeed ^ P.epsilon = P.kSeedBase := by
  calc
    P.kSeed ^ P.epsilon =
        (P.kSeedBase ^ (P.kExponent : ℝ)) ^ P.epsilon := by
      rw [Real.rpow_natCast]
      rfl
    _ = P.kSeedBase ^ ((P.kExponent : ℝ) * P.epsilon) := by
      rw [Real.rpow_mul P.kSeedBase_pos.le]
    _ = P.kSeedBase := by rw [P.kExponent_mul_epsilon, Real.rpow_one]

theorem equationOneThreshold_eq_rpow :
    P.equationOneThreshold =
      (32 * (P.rank + 1 : ℝ)) ^ P.epsilon⁻¹ := by
  rw [P.epsilon_inv_eq_kExponent, Real.rpow_natCast]
  rfl

theorem equationOneThreshold_lt_k : P.equationOneThreshold < P.k := by
  have hbase : (32 : ℝ) * ((P.rank : ℝ) + 1) < P.kSeedBase := by
    unfold kSeedBase
    have hrank : (0 : ℝ) < (P.rank : ℝ) + 1 := by positivity
    nlinarith
  have hpow : P.equationOneThreshold < P.kSeed := by
    unfold equationOneThreshold kSeed
    exact pow_lt_pow_left₀ hbase (by positivity) P.kExponent_pos.ne'
  exact hpow.trans P.kSeed_lt_k

theorem q_le_k_rpow_epsilon : (P.q : ℝ) ≤ P.k ^ P.epsilon := by
  have hseed : P.kSeed ^ P.epsilon ≤ P.k ^ P.epsilon :=
    Real.rpow_le_rpow P.kSeed_pos.le P.kSeed_lt_k.le P.epsilon_pos.le
  rw [P.kSeed_rpow_epsilon_eq_kSeedBase] at hseed
  calc
    (P.q : ℝ) ≤ P.kSeedBase := by
      rw [show (P.q : ℝ) = 13 by norm_num [q]]
      unfold kSeedBase
      have hrank : (1 : ℝ) ≤ P.rank := by exact_mod_cast P.one_le_rank
      nlinarith
    _ ≤ P.k ^ P.epsilon := hseed

theorem q_lt_k_rpow_epsilon : (P.q : ℝ) < P.k ^ P.epsilon := by
  have hseed : P.kSeedBase ≤ P.k ^ P.epsilon := by
    have h := Real.rpow_le_rpow P.kSeed_pos.le P.kSeed_lt_k.le
      P.epsilon_pos.le
    rwa [P.kSeed_rpow_epsilon_eq_kSeedBase] at h
  calc
    (P.q : ℝ) = 13 := by norm_num [q]
    _ < 64 * (P.rank + 1 : ℝ) := by
      have hrank : (1 : ℝ) ≤ P.rank := by exact_mod_cast P.one_le_rank
      nlinarith
    _ = P.kSeedBase := rfl
    _ ≤ P.k ^ P.epsilon := hseed

theorem thirteen_le_k_rpow_one_sub_sigma_epsilon :
    (13 : ℝ) ≤ P.k ^ (1 - (P.sigma + P.epsilon)) := by
  calc
    (13 : ℝ) = P.q := by simp [q]
    _ ≤ P.k ^ P.epsilon := P.q_le_k_rpow_epsilon
    _ ≤ P.k ^ (1 - (P.sigma + P.epsilon)) :=
      Real.rpow_le_rpow_of_exponent_le P.one_le_k
        P.epsilon_le_one_sub_sigma_add_epsilon

theorem epsilon_le_one_sub_sigma_sub_epsilon :
    P.epsilon ≤ 1 - (P.sigma - P.epsilon) := by
  linarith [P.sigma_add_epsilon_lt_one, P.epsilon_pos]

theorem thirteen_le_k_rpow_one_sub_sigma_sub_epsilon :
    (13 : ℝ) ≤ P.k ^ (1 - (P.sigma - P.epsilon)) := by
  calc
    (13 : ℝ) = P.q := by simp [q]
    _ ≤ P.k ^ P.epsilon := P.q_le_k_rpow_epsilon
    _ ≤ P.k ^ (1 - (P.sigma - P.epsilon)) :=
      Real.rpow_le_rpow_of_exponent_le P.one_le_k
        P.epsilon_le_one_sub_sigma_sub_epsilon

theorem thirteen_le_k_rpow_one_sub_sigma :
    (13 : ℝ) ≤ P.k ^ (1 - P.sigma) := by
  calc
    (13 : ℝ) = P.q := by simp [q]
    _ ≤ P.k ^ P.epsilon := P.q_le_k_rpow_epsilon
    _ ≤ P.k ^ (1 - P.sigma) :=
      Real.rpow_le_rpow_of_exponent_le P.one_le_k (by
        linarith [P.epsilon_le_one_sub_sigma_add_epsilon, P.epsilon_pos])

theorem q_le_enlargedK_rpow_epsilon (requirements : Finset ℝ) :
    (P.q : ℝ) ≤ P.enlargedK requirements ^ P.epsilon := by
  exact P.q_le_k_rpow_epsilon.trans
    (Real.rpow_le_rpow P.k_pos.le (P.k_lt_enlargedK requirements).le P.epsilon_pos.le)

theorem C_pos : 0 < P.C := by
  unfold C
  exact Real.rpow_pos_of_pos P.k_pos _

theorem two_le_log_Bsrc : 2 ≤ Real.log P.Bsrc := by
  rw [← Real.log_exp (2 : ℝ)]
  exact Real.strictMonoOn_log.monotoneOn
    (Real.exp_pos 2) ((Real.exp_pos 2).trans_le P.Bsrc_lower) P.Bsrc_lower

theorem two_le_h : 2 ≤ P.h := by
  unfold h
  apply Nat.le_floor
  exact P.two_le_log_Bsrc

theorem h_pos : 0 < P.h := lt_of_lt_of_le (by norm_num) P.two_le_h

theorem one_le_h : 1 ≤ P.h := P.h_pos

theorem h_cast_le_log_Bsrc : (P.h : ℝ) ≤ Real.log P.Bsrc := by
  exact Nat.floor_le (le_trans (by norm_num) P.two_le_log_Bsrc)

theorem log_Bsrc_lt_h_add_one : Real.log P.Bsrc < P.h + 1 := by
  exact Nat.lt_floor_add_one _

theorem qInvPow_pos (J : ℕ) : 0 < P.qInvPow J := by
  simp only [qInvPow, inv_pos]
  exact_mod_cast pow_pos (Nat.zero_lt_of_lt P.one_lt_q) J

theorem qInvPow_succ (J : ℕ) :
    P.qInvPow (J + 1) = P.qInvPow J / P.q := by
  unfold qInvPow
  rw [pow_succ]
  push_cast
  field_simp

theorem qInvPow_antitone : Antitone P.qInvPow := by
  intro a b hab
  unfold qInvPow
  apply inv_anti₀
  · exact_mod_cast pow_pos (Nat.zero_lt_of_lt P.one_lt_q) a
  · exact_mod_cast Nat.pow_le_pow_right (Nat.zero_lt_of_lt P.one_lt_q) hab

theorem levelScale_pos [Nonempty ι] (J : ℕ) :
    0 < P.levelScale J := by
  unfold levelScale
  exact mul_pos (mul_pos (mul_pos (P.qInvPow_pos J) P.k_pos) P.Omega_pos)
    P.log_OmegaOld_pos

/-- The admissible-level inequality gives a strong lower bound for the
derivative scale.  This is the form used to absorb every floor in the
Lemma 4 budget recursion. -/
theorem eight_mul_rank_mul_rpow_sub_mul_log_lt_levelScale [Nonempty ι]
    {N : ℕ} (hN : P.LevelOK N) :
    8 * (P.rank : ℝ) * P.k ^ (P.sigma - P.epsilon) *
        Real.log P.newHeight < P.levelScale N := by
  have hRank : (0 : ℝ) < 8 * P.rank := by
    exact mul_pos (by norm_num) (by exact_mod_cast P.rank_pos)
  have hQ : (0 : ℝ) < ((P.q ^ N : ℕ) : ℝ) := by
    exact_mod_cast pow_pos (Nat.zero_lt_of_lt P.one_lt_q) N
  have hKpart : 0 < P.k ^ (P.sigma - P.epsilon) :=
    Real.rpow_pos_of_pos P.k_pos _
  have hLevelMul := mul_lt_mul_of_pos_right hN hRank
  have hCore :
      ((P.q ^ N : ℕ) : ℝ) * (8 * P.rank) <
        P.k ^ (1 - (P.sigma - P.epsilon)) *
          P.OmegaOld * Real.log P.OmegaOld := by
    calc
      ((P.q ^ N : ℕ) : ℝ) * (8 * P.rank) <
          P.levelBound * (8 * P.rank) := hLevelMul
      _ = P.k ^ (1 - (P.sigma - P.epsilon)) *
          P.OmegaOld * Real.log P.OmegaOld := by
            unfold levelBound
            field_simp [hRank.ne']
  have hCoreMul := mul_lt_mul_of_pos_right hCore hKpart
  have hPow :
      P.k ^ (1 - (P.sigma - P.epsilon)) *
          P.k ^ (P.sigma - P.epsilon) = P.k := by
    rw [← Real.rpow_add P.k_pos]
    ring_nf
    exact Real.rpow_one P.k
  unfold levelScale qInvPow Omega
  rw [show ((P.q ^ N : ℕ) : ℝ)⁻¹ * P.k *
      (P.OmegaOld * Real.log P.newHeight) * Real.log P.OmegaOld =
      ((P.q ^ N : ℕ) : ℝ)⁻¹ *
        (P.k * (P.OmegaOld * Real.log P.newHeight) *
          Real.log P.OmegaOld) by ring]
  rw [lt_inv_mul_iff₀ hQ]
  have hAll := mul_lt_mul_of_pos_right hCoreMul P.log_newHeight_pos
  calc
    ((P.q ^ N : ℕ) : ℝ) *
        (8 * (P.rank : ℝ) * P.k ^ (P.sigma - P.epsilon) *
          Real.log P.newHeight) =
      (((P.q ^ N : ℕ) : ℝ) * (8 * P.rank) *
        P.k ^ (P.sigma - P.epsilon)) * Real.log P.newHeight := by ring
    _ < (P.k ^ (1 - (P.sigma - P.epsilon)) *
          P.OmegaOld * Real.log P.OmegaOld *
        P.k ^ (P.sigma - P.epsilon)) * Real.log P.newHeight := hAll
    _ = P.k * (P.OmegaOld * Real.log P.newHeight) *
          Real.log P.OmegaOld := by
      calc
        (P.k ^ (1 - (P.sigma - P.epsilon)) *
              P.OmegaOld * Real.log P.OmegaOld *
            P.k ^ (P.sigma - P.epsilon)) * Real.log P.newHeight =
            (P.k ^ (1 - (P.sigma - P.epsilon)) *
              P.k ^ (P.sigma - P.epsilon)) * P.OmegaOld *
                Real.log P.newHeight * Real.log P.OmegaOld := by ring
        _ = P.k * (P.OmegaOld * Real.log P.newHeight) *
              Real.log P.OmegaOld := by rw [hPow]; ring

/-- A coarse numerical consequence of the preceding source inequality.
The factor `512` leaves ample room for all floors in the terminal Lemma 4
budget estimate. -/
theorem fiveHundredTwelve_mul_rank_add_one_lt_levelScale [Nonempty ι]
    {N : ℕ} (hN : P.LevelOK N) :
    512 * (P.rank + 1 : ℝ) < P.levelScale N := by
  have hSeed : P.kSeedBase ≤ P.k ^ P.epsilon := by
    have h := Real.rpow_le_rpow P.kSeed_pos.le P.kSeed_lt_k.le
      P.epsilon_pos.le
    rwa [P.kSeed_rpow_epsilon_eq_kSeedBase] at h
  have hExponent : P.epsilon ≤ P.sigma - P.epsilon := by
    rw [P.sigma_eq, P.epsilon_eq]
    have hm : (0 : ℝ) < P.rank + 1 := by positivity
    field_simp
    nlinarith
  have hRpow : 64 * (P.rank + 1 : ℝ) ≤
      P.k ^ (P.sigma - P.epsilon) := by
    exact hSeed.trans
      (Real.rpow_le_rpow_of_exponent_le P.one_le_k hExponent)
  have hRankOne : (1 : ℝ) ≤ P.rank := by
    exact_mod_cast P.one_le_rank
  calc
    512 * (P.rank + 1 : ℝ) =
        8 * 1 * (64 * (P.rank + 1 : ℝ)) * 1 := by ring
    _ ≤ 8 * (P.rank : ℝ) * (64 * (P.rank + 1 : ℝ)) * 1 := by
      gcongr
    _ ≤ 8 * (P.rank : ℝ) * P.k ^ (P.sigma - P.epsilon) * 1 := by
      gcongr
    _ ≤ 8 * (P.rank : ℝ) * P.k ^ (P.sigma - P.epsilon) *
          Real.log P.newHeight := by
      exact mul_le_mul_of_nonneg_left P.one_le_log_newHeight
        (mul_nonneg
          (mul_nonneg (by norm_num) (by positivity))
          (Real.rpow_pos_of_pos P.k_pos _).le)
    _ < P.levelScale N :=
      P.eight_mul_rank_mul_rpow_sub_mul_log_lt_levelScale hN

theorem levelScale_antitone [Nonempty ι] : Antitone P.levelScale := by
  intro a b hab
  unfold levelScale
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (P.qInvPow_antitone hab) P.k_pos.le)
      P.Omega_pos.le) P.log_OmegaOld_pos.le

theorem Slevel_cast_le [Nonempty ι] (J : ℕ) :
    (P.Slevel J : ℝ) ≤ P.levelScale J := by
  exact Nat.floor_le (le_of_lt (P.levelScale_pos J))

theorem levelScale_lt_Slevel_add_one (J : ℕ) :
    P.levelScale J < P.Slevel J + 1 := by
  exact Nat.lt_floor_add_one _

@[simp] theorem lemmaFourBudget_zero (N : ℕ) :
    P.lemmaFourBudget N 0 = P.Slevel N := rfl

@[simp] theorem lemmaFourBudget_one (N : ℕ) :
    P.lemmaFourBudget N 1 = ⌊(P.Slevel N : ℝ) / 2⌋₊ := rfl

@[simp] theorem lemmaFourBudget_succ_succ (N J : ℕ) :
    P.lemmaFourBudget N (J + 2) =
      ⌊(1 - P.lemmaFourEpsilon (J + 1)) *
        (P.lemmaFourBudget N (J + 1) : ℝ)⌋₊ := rfl

theorem epsilon_le_lemmaFourEpsilon (J : ℕ) :
    P.epsilon ≤ P.lemmaFourEpsilon J := by
  exact le_max_left _ _

theorem three_div_k_rpow_le_lemmaFourEpsilon (J : ℕ) :
    3 / P.k ^ (P.epsilon * (J : ℝ)) ≤ P.lemmaFourEpsilon J := by
  exact le_max_right _ _

/-- For every positive interpolation index, the maximum in the source's
definition of `ε_J` is attained by `ε`.  The deliberately large seed for
`k` makes this uniform in the outer level. -/
theorem lemmaFourEpsilon_eq_epsilon {J : ℕ} (hJ : 1 ≤ J) :
    P.lemmaFourEpsilon J = P.epsilon := by
  unfold lemmaFourEpsilon
  apply max_eq_left
  have hExp : P.epsilon ≤ P.epsilon * (J : ℝ) := by
    nlinarith [P.epsilon_pos, (by exact_mod_cast hJ : (1 : ℝ) ≤ J)]
  have hkMono : P.k ^ P.epsilon ≤
      P.k ^ (P.epsilon * (J : ℝ)) :=
    Real.rpow_le_rpow_of_exponent_le P.one_le_k hExp
  have hSeed : P.kSeedBase ≤ P.k ^ P.epsilon := by
    have h := Real.rpow_le_rpow P.kSeed_pos.le P.kSeed_lt_k.le
      P.epsilon_pos.le
    rwa [P.kSeed_rpow_epsilon_eq_kSeedBase] at h
  have hDen : 64 * (P.rank + 1 : ℝ) ≤
      P.k ^ (P.epsilon * (J : ℝ)) := by
    exact hSeed.trans hkMono
  have hDenPos : 0 < P.k ^ (P.epsilon * (J : ℝ)) :=
    Real.rpow_pos_of_pos P.k_pos _
  have hm : (0 : ℝ) < P.rank + 1 := by positivity
  have hfrac : 3 / P.k ^ (P.epsilon * (J : ℝ)) ≤
      1 / (6 * (P.rank + 1 : ℝ)) := by
    apply (div_le_div_iff₀ hDenPos
      (by positivity : (0 : ℝ) < 6 * (P.rank + 1))).2
    nlinarith
  exact hfrac.trans_eq P.epsilon_eq.symm

/-- A floor-robust lower estimate for the exact Lemma 4 budget recursion.
The estimate is deliberately linear (Bernoulli's inequality plus one unit
for each floor), so it can later be specialized at the source endpoint. -/
theorem lemmaFourBudget_lower_linear (N J : ℕ)
    (hS : 2 ≤ P.Slevel N) (hJ : 1 ≤ J)
    (hJepsilon : (J : ℝ) * P.epsilon ≤ 1 / 2) :
    (1 - ((J : ℝ) - 1) * P.epsilon) *
          ((P.Slevel N : ℝ) / 2 - 1) - ((J : ℝ) - 1) <
      P.lemmaFourBudget N J := by
  induction J with
  | zero => omega
  | succ J ih =>
      by_cases hJ0 : J = 0
      · subst J
        norm_num [lemmaFourBudget]
        have hFloor := Nat.lt_floor_add_one ((P.Slevel N : ℝ) / 2)
        linarith
      · obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hJ0
        have hjOne : 1 ≤ j + 1 := by omega
        have hjCast : (0 : ℝ) ≤ j := by positivity
        have hepsNonneg : 0 ≤ P.epsilon := P.epsilon_pos.le
        have hepsLtOne : P.epsilon < 1 := by
          rw [P.epsilon_eq]
          have hm : (1 : ℝ) ≤ P.rank + 1 := by
            exact_mod_cast Nat.succ_le_succ (Nat.zero_le P.rank)
          apply (div_lt_one (by positivity : (0 : ℝ) < 6 * (P.rank + 1))).2
          nlinarith
        have hjEpsilon : ((j + 1 : ℕ) : ℝ) * P.epsilon ≤ 1 / 2 := by
          exact hJepsilon.trans' (by
            push_cast
            nlinarith [P.epsilon_pos])
        have hprev := ih hjOne hjEpsilon
        have heq := P.lemmaFourEpsilon_eq_epsilon hjOne
        have hFloor := Nat.lt_floor_add_one
          ((1 - P.epsilon) * (P.lemmaFourBudget N (j + 1) : ℝ))
        have hMul :
            (1 - P.epsilon) *
                ((1 - ((((j + 1 : ℕ) : ℝ)) - 1) * P.epsilon) *
                    ((P.Slevel N : ℝ) / 2 - 1) -
                  ((((j + 1 : ℕ) : ℝ)) - 1)) <
              (1 - P.epsilon) * (P.lemmaFourBudget N (j + 1) : ℝ) := by
          exact mul_lt_mul_of_pos_left hprev (sub_pos.mpr hepsLtOne)
        have hA : 0 ≤ (P.Slevel N : ℝ) / 2 - 1 := by
          have hSreal : (2 : ℝ) ≤ P.Slevel N := by exact_mod_cast hS
          linarith
        have herror : 0 ≤ (j : ℝ) * P.epsilon * P.epsilon *
            ((P.Slevel N : ℝ) / 2 - 1) := by positivity
        rw [P.lemmaFourBudget_succ_succ, heq]
        push_cast at hMul ⊢
        nlinarith

/-- Exact terminal derivative budget in the rational-prime specialization of
source Lemma 4.  Here `3 * (rank+1) = μ/(2ε)` for `μ = 1`; the source then
uses `floor(levelScale/6)` as the input budget for Lemma 5. -/
theorem levelScale_div_six_floor_le_terminalBudget [Nonempty ι]
    {N : ℕ} (hN : P.LevelOK N) :
    ⌊P.levelScale N / 6⌋₊ ≤
      P.lemmaFourBudget N (3 * (P.rank + 1)) := by
  have hmPos : (0 : ℝ) < P.rank + 1 := by positivity
  have hmOne : (1 : ℝ) ≤ P.rank + 1 := by
    exact_mod_cast Nat.succ_le_succ (Nat.zero_le P.rank)
  have hScaleHuge :=
    P.fiveHundredTwelve_mul_rank_add_one_lt_levelScale hN
  have hScale36 : 36 * (P.rank + 1 : ℝ) < P.levelScale N := by
    nlinarith
  have hS : 2 ≤ P.Slevel N := by
    unfold Slevel
    apply Nat.le_floor
    have hTwo : (2 : ℝ) ≤ 36 * (P.rank + 1 : ℝ) := by nlinarith
    exact hTwo.trans hScale36.le
  have hTPos : 1 ≤ 3 * (P.rank + 1) := by omega
  have hTEpsilon :
      ((3 * (P.rank + 1) : ℕ) : ℝ) * P.epsilon ≤ 1 / 2 := by
    rw [P.epsilon_eq]
    push_cast
    field_simp
    norm_num
  have hTerminal := P.lemmaFourBudget_lower_linear N
    (3 * (P.rank + 1)) hS hTPos hTEpsilon
  have hCoeff :
      1 - ((((3 * (P.rank + 1) : ℕ) : ℝ)) - 1) * P.epsilon =
        1 / 2 + P.epsilon := by
    rw [P.epsilon_eq]
    push_cast
    field_simp
    ring_nf
  rw [hCoeff] at hTerminal
  have hA : 0 ≤ (P.Slevel N : ℝ) / 2 - 1 := by
    have hSreal : (2 : ℝ) ≤ P.Slevel N := by exact_mod_cast hS
    linarith
  have hCoeffMul :
      (1 / 2 : ℝ) * ((P.Slevel N : ℝ) / 2 - 1) ≤
        (1 / 2 + P.epsilon) * ((P.Slevel N : ℝ) / 2 - 1) := by
    exact mul_le_mul_of_nonneg_right (by linarith [P.epsilon_pos]) hA
  have hCoarse :
      (1 / 2 : ℝ) * ((P.Slevel N : ℝ) / 2 - 1) -
          ((((3 * (P.rank + 1) : ℕ) : ℝ)) - 1) <
        P.lemmaFourBudget N (3 * (P.rank + 1)) :=
    (sub_le_sub_right hCoeffMul _).trans_lt hTerminal
  have hScaleFloor := P.levelScale_lt_Slevel_add_one N
  have hSix :
      P.levelScale N / 6 <
        (P.lemmaFourBudget N (3 * (P.rank + 1)) : ℝ) := by
    push_cast at hCoarse
    nlinarith
  have hFloorSix :
      (⌊P.levelScale N / 6⌋₊ : ℝ) ≤ P.levelScale N / 6 := by
    exact Nat.floor_le (div_nonneg (P.levelScale_pos N).le (by norm_num))
  have hCast :
      (⌊P.levelScale N / 6⌋₊ : ℝ) <
        P.lemmaFourBudget N (3 * (P.rank + 1)) :=
    hFloorSix.trans_lt hSix
  exact_mod_cast hCast.le

/-- The weaker `/9` budget consumed after Lemma 5 is in particular available
at the terminal Lemma 4 stage. -/
theorem Sstep_le_terminalBudget [Nonempty ι]
    {N : ℕ} (hN : P.LevelOK N) :
    P.Sstep N ≤ P.lemmaFourBudget N (3 * (P.rank + 1)) := by
  calc
    P.Sstep N ≤ ⌊P.levelScale N / 6⌋₊ := by
      unfold Sstep
      apply Nat.floor_mono
      have hScale := P.levelScale_pos N
      nlinarith
    _ ≤ P.lemmaFourBudget N (3 * (P.rank + 1)) :=
      P.levelScale_div_six_floor_le_terminalBudget hN

/-- At the exact source endpoint `J = 3(rank+1)`, the Lemma 4 radius has
grown by `k^(1/2)`. -/
theorem lemmaFourRadiusScale_terminal (N : ℕ) :
    P.lemmaFourRadiusScale N (3 * (P.rank + 1)) =
      16 * ((P.q ^ N : ℕ) : ℝ) * P.h * P.k ^ (1 / 2 : ℝ) := by
  unfold lemmaFourRadiusScale
  congr 1
  rw [P.epsilon_eq]
  push_cast
  field_simp
  ring_nf

theorem lemmaFourRadius_terminal (N : ℕ) :
    P.lemmaFourRadius N (3 * (P.rank + 1)) =
      ⌊16 * ((P.q ^ N : ℕ) : ℝ) * P.h * P.k ^ (1 / 2 : ℝ)⌋₊ := by
  unfold lemmaFourRadius
  rw [P.lemmaFourRadiusScale_terminal]

theorem lemmaFourRadiusScale_pos [Nonempty ι] (N J : ℕ) :
    0 < P.lemmaFourRadiusScale N J := by
  unfold lemmaFourRadiusScale
  exact mul_pos
    (mul_pos
      (mul_pos (by norm_num)
        (by exact_mod_cast pow_pos (Nat.zero_lt_of_lt P.one_lt_q) N))
      (by exact_mod_cast P.h_pos))
    (Real.rpow_pos_of_pos P.k_pos _)

@[simp] theorem lemmaFourRadiusScale_zero (N : ℕ) :
    P.lemmaFourRadiusScale N 0 = (P.R N : ℝ) := by
  simp [lemmaFourRadiusScale, R]

@[simp] theorem lemmaFourRadius_zero (N : ℕ) :
    P.lemmaFourRadius N 0 = P.R N := by
  unfold lemmaFourRadius
  rw [P.lemmaFourRadiusScale_zero]
  exact Nat.floor_natCast _

theorem R_succ_le_lemmaFourRadius_one [Nonempty ι] (N : ℕ) :
    P.R (N + 1) ≤ P.lemmaFourRadius N 1 := by
  unfold lemmaFourRadius
  apply Nat.le_floor
  have hq := P.q_le_k_rpow_epsilon
  have hfac : (0 : ℝ) ≤
      16 * ((P.q ^ N : ℕ) : ℝ) * P.h := by positivity
  calc
    (P.R (N + 1) : ℝ) =
        (16 * ((P.q ^ N : ℕ) : ℝ) * P.h) * P.q := by
          unfold R
          rw [pow_succ]
          push_cast
          ring
    _ ≤ (16 * ((P.q ^ N : ℕ) : ℝ) * P.h) *
          P.k ^ P.epsilon := mul_le_mul_of_nonneg_left hq hfac
    _ = P.lemmaFourRadiusScale N 1 := by
          unfold lemmaFourRadiusScale
          norm_num

theorem Sstep_cast_le [Nonempty ι] (J : ℕ) :
    (P.Sstep J : ℝ) ≤ P.levelScale J / 9 := by
  exact Nat.floor_le (div_nonneg (P.levelScale_pos J).le (by norm_num))

theorem levelScale_div_nine_lt_Sstep_add_one (J : ℕ) :
    P.levelScale J / 9 < P.Sstep J + 1 := by
  exact Nat.lt_floor_add_one _

theorem Slevel_antitone [Nonempty ι] : Antitone P.Slevel := by
  intro a b hab
  unfold Slevel
  exact Nat.floor_mono (P.levelScale_antitone hab)

theorem Sstep_le_Slevel [Nonempty ι] (J : ℕ) :
    P.Sstep J ≤ P.Slevel J := by
  unfold Sstep Slevel
  apply Nat.floor_mono
  have h := P.levelScale_pos J
  nlinarith

theorem levelScale_succ (J : ℕ) :
    P.levelScale (J + 1) = P.levelScale J / P.q := by
  unfold levelScale
  rw [P.qInvPow_succ]
  field_simp

theorem Slevel_succ_le_Sstep [Nonempty ι] (J : ℕ) :
    P.Slevel (J + 1) ≤ P.Sstep J := by
  unfold Slevel Sstep
  apply Nat.floor_mono
  rw [P.levelScale_succ]
  have h := P.levelScale_pos J
  rw [q]
  nlinarith

theorem R_pos (J : ℕ) : 0 < P.R J := by
  unfold R
  exact Nat.mul_pos
    (Nat.mul_pos (by norm_num) (pow_pos (Nat.zero_lt_of_lt P.one_lt_q) J)) P.h_pos

theorem R_mono : Monotone P.R := by
  intro a b hab
  unfold R
  exact Nat.mul_le_mul_right P.h
    (Nat.mul_le_mul_left 16
      (Nat.pow_le_pow_right (Nat.zero_lt_of_lt P.one_lt_q) hab))

theorem R_succ (J : ℕ) : P.R (J + 1) = P.q * P.R J := by
  simp only [R, pow_succ]
  ac_rfl

theorem floor_source_radius_eq_R (J : ℕ) :
    ⌊16 * ((P.q ^ J : ℕ) : ℝ) * P.h⌋₊ = P.R J := by
  unfold R
  apply (Nat.floor_eq_iff (by positivity)).2
  constructor
  · norm_cast
  · push_cast
    linarith

theorem levelBound_pos [Nonempty ι] : 0 < P.levelBound := by
  unfold levelBound
  have hrank : (0 : ℝ) < 8 * (P.rank : ℝ) := by
    exact mul_pos (by norm_num) (by exact_mod_cast P.rank_pos)
  exact mul_pos
    (mul_pos
      (mul_pos (inv_pos.mpr hrank)
        (Real.rpow_pos_of_pos P.k_pos _))
      P.OmegaOld_pos)
    P.log_OmegaOld_pos

/-- The baseline choice of `k` already makes the admissible-level interval
nonempty.  Extra source requirements can only enlarge `k`. -/
theorem one_lt_levelBound [Nonempty ι] : 1 < P.levelBound := by
  have hrankPos : (0 : ℝ) < P.rank := by exact_mod_cast P.rank_pos
  have hdenPos : (0 : ℝ) < 8 * P.rank := mul_pos (by norm_num) hrankPos
  have hlogNumerical : (8 : ℝ) < 13 * Real.log 2 := by
    nlinarith [Real.log_two_gt_d9]
  have hsmall : 8 * (P.rank : ℝ) <
      13 * (P.rank : ℝ) * Real.log 2 := by
    have := mul_lt_mul_of_pos_right hlogNumerical hrankPos
    nlinarith
  have hk : (13 : ℝ) ≤
      P.k ^ (1 - (P.sigma - P.epsilon)) :=
    P.thirteen_le_k_rpow_one_sub_sigma_sub_epsilon
  have hkpos : 0 ≤ P.k ^ (1 - (P.sigma - P.epsilon)) :=
    (Real.rpow_pos_of_pos P.k_pos _).le
  have hprod : 13 * (P.rank : ℝ) * Real.log 2 ≤
      P.k ^ (1 - (P.sigma - P.epsilon)) *
        P.OmegaOld * Real.log P.OmegaOld := by
    calc
      13 * (P.rank : ℝ) * Real.log 2 ≤
          P.k ^ (1 - (P.sigma - P.epsilon)) *
            (P.rank : ℝ) * Real.log 2 := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right hk hrankPos.le) log_two_pos.le
      _ ≤ P.k ^ (1 - (P.sigma - P.epsilon)) *
            P.OmegaOld * Real.log 2 := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left P.rank_le_OmegaOld hkpos) log_two_pos.le
      _ ≤ P.k ^ (1 - (P.sigma - P.epsilon)) *
            P.OmegaOld * Real.log P.OmegaOld := by
        exact mul_le_mul_of_nonneg_left P.log_two_le_log_OmegaOld
          (mul_nonneg hkpos P.OmegaOld_pos.le)
  unfold levelBound
  rw [show (8 * (P.rank : ℝ))⁻¹ *
      P.k ^ (1 - (P.sigma - P.epsilon)) *
        P.OmegaOld * Real.log P.OmegaOld =
      (8 * (P.rank : ℝ))⁻¹ *
        (P.k ^ (1 - (P.sigma - P.epsilon)) *
          P.OmegaOld * Real.log P.OmegaOld) by ring]
  apply (one_lt_inv_mul₀ hdenPos).2
  exact hsmall.trans_le hprod

theorem LevelOK.mono {J J' : ℕ} (h : P.LevelOK J) (hle : J' ≤ J) :
    P.LevelOK J' := by
  unfold LevelOK at h ⊢
  exact lt_of_le_of_lt (by
    exact_mod_cast Nat.pow_le_pow_right (by simp [q]) hle) h

theorem LevelOK.levelWithin {J : ℕ} (h : P.LevelOK J) :
    P.LevelWithin J := h.le

theorem LevelWithin.mono {J J' : ℕ} (h : P.LevelWithin J) (hle : J' ≤ J) :
    P.LevelWithin J' := by
  unfold LevelWithin at h ⊢
  have hp : ((P.q ^ J' : ℕ) : ℝ) ≤ ((P.q ^ J : ℕ) : ℝ) := by
    exact_mod_cast Nat.pow_le_pow_right (by simp [q]) hle
  exact hp.trans h

/-- Every level strictly below a terminal nonstrict level is an admissible
strict induction level. -/
theorem LevelWithin.strict_of_lt {J J' : ℕ} (h : P.LevelWithin J)
    (hlt : J' < J) : P.LevelOK J' := by
  unfold LevelWithin at h
  unfold LevelOK
  have hp : ((P.q ^ J' : ℕ) : ℝ) < ((P.q ^ J : ℕ) : ℝ) := by
    exact_mod_cast Nat.pow_lt_pow_right P.one_lt_q hlt
  exact hp.trans_le h

/-- Whenever the level interval is nonempty, it has a largest admissible
natural level.  This is the exact floor/maximality fact used when the source
chooses `N`; it does not assume an unproved Archimedean endpoint. -/
theorem exists_maximal_level (hlarge : 1 < P.levelBound) :
    ∃ N : ℕ, P.LevelOK N ∧ ¬ P.LevelOK (N + 1) := by
  classical
  have hex : ∃ J : ℕ, ¬ P.LevelOK J := by
    obtain ⟨m, hm⟩ := exists_nat_gt P.levelBound
    refine ⟨m, ?_⟩
    intro hlevel
    have hpow : (m : ℝ) < (P.q ^ m : ℕ) := by
      exact_mod_cast Nat.lt_pow_self P.one_lt_q
    unfold LevelOK at hlevel
    linarith
  let firstBad : ℕ := Nat.find hex
  have hfirstBad : ¬ P.LevelOK firstBad := by
    exact Nat.find_spec hex
  have hfirstBadPos : 0 < firstBad := by
    by_contra hzero
    have hzero' : firstBad = 0 := Nat.eq_zero_of_not_pos hzero
    apply hfirstBad
    unfold LevelOK
    simpa [hzero'] using hlarge
  have hpred_lt : firstBad - 1 < firstBad := Nat.sub_lt hfirstBadPos (by norm_num)
  have hpred : P.LevelOK (firstBad - 1) := by
    by_contra hnot
    exact (Nat.find_min hex hpred_lt) hnot
  refine ⟨firstBad - 1, hpred, ?_⟩
  rwa [Nat.sub_add_cancel hfirstBadPos]

theorem levelBound_div_q_le_pow_of_not_LevelOK_succ {N : ℕ}
    (hnot : ¬ P.LevelOK (N + 1)) :
    P.levelBound / P.q ≤ ((P.q ^ N : ℕ) : ℝ) := by
  have hqR : (0 : ℝ) < P.q := by
    exact_mod_cast Nat.zero_lt_of_lt P.one_lt_q
  apply (div_le_iff₀ hqR).2
  have hupper : P.levelBound ≤ ((P.q ^ (N + 1) : ℕ) : ℝ) := by
    exact not_lt.mp hnot
  rw [pow_succ] at hupper
  push_cast at hupper ⊢
  simpa [mul_comm] using hupper

/-- Auxiliary maximal strict induction level.  The final source index is the
separate minimal-above-side-length choice `exists_terminal_level` below. -/
theorem exists_level_with_two_sided_bounds [Nonempty ι] :
    ∃ N : ℕ,
      P.levelBound / P.q ≤ ((P.q ^ N : ℕ) : ℝ) ∧
      ((P.q ^ N : ℕ) : ℝ) < P.levelBound := by
  obtain ⟨N, hN, hNmax⟩ := P.exists_maximal_level P.one_lt_levelBound
  exact ⟨N, P.levelBound_div_q_le_pow_of_not_LevelOK_succ hNmax, hN⟩

theorem coeffHeight_pos : 0 < P.coeffHeight := by
  unfold coeffHeight
  positivity

theorem LminusOnePlusOne_eq_h : P.LminusOnePlusOne = P.h := rfl

theorem LminusOne_pos : 0 < P.LminusOne := by
  unfold LminusOne LminusOnePlusOne
  have h := P.two_le_h
  omega

theorem LminusOne_add_one_eq_h : P.LminusOne + 1 = P.h := by
  unfold LminusOne LminusOnePlusOne
  have h := P.two_le_h
  omega

theorem eight_le_k_rpow_one_sub_sigma :
    (8 : ℝ) ≤ P.k ^ (1 - P.sigma) := by
  have hexponent : P.epsilon ≤ 1 - P.sigma := by
    linarith [P.sigma_add_epsilon_lt_one]
  calc
    (8 : ℝ) ≤ P.q := by norm_num [q]
    _ ≤ P.k ^ P.epsilon := P.q_le_k_rpow_epsilon
    _ ≤ P.k ^ (1 - P.sigma) :=
      Real.rpow_le_rpow_of_exponent_le P.one_le_k hexponent

theorem LzeroPlusOne_pos : 0 < P.LzeroPlusOne := by
  unfold LzeroPlusOne LzeroScale
  rw [Nat.floor_pos]
  have hkpos : 0 ≤ P.k ^ (1 - P.sigma) :=
    (Real.rpow_pos_of_pos P.k_pos _).le
  have hmul : P.k ^ (1 - P.sigma) ≤
      P.k ^ (1 - P.sigma) * P.Omega :=
    le_mul_of_one_le_right hkpos P.one_le_Omega
  have height := P.eight_le_k_rpow_one_sub_sigma.trans hmul
  nlinarith

theorem LzeroPlusOne_cast_le : (P.LzeroPlusOne : ℝ) ≤ P.LzeroScale := by
  apply Nat.floor_le
  unfold LzeroScale
  exact mul_nonneg
    (mul_nonneg (by norm_num) (Real.rpow_pos_of_pos P.k_pos _).le)
    P.Omega_pos.le

theorem LzeroScale_lt_add_one :
    P.LzeroScale < (P.LzeroPlusOne : ℝ) + 1 := by
  exact Nat.lt_floor_add_one _

theorem LiZeroScale_pos [Nonempty ι] (i : ι) : 0 < P.LiZeroScale i := by
  unfold LiZeroScale
  exact div_pos
    (mul_pos
      (mul_pos
        (mul_pos (inv_pos.mpr (by
          have hr : (0 : ℝ) < P.rank := by exact_mod_cast P.rank_pos
          positivity)) (Real.rpow_pos_of_pos P.k_pos _))
        P.Omega_pos)
      P.log_OmegaOld_pos)
    (P.log_oldHeight_pos i)

theorem LiZero_cast_le [Nonempty ι] (i : ι) :
    (P.LiZero i : ℝ) ≤ P.LiZeroScale i := by
  exact Nat.floor_le (P.LiZeroScale_pos i).le

theorem LiZeroScale_lt_add_one (i : ι) :
    P.LiZeroScale i < (P.LiZero i : ℝ) + 1 := by
  exact Nat.lt_floor_add_one _

theorem LlastZeroScale_pos [Nonempty ι] : 0 < P.LlastZeroScale := by
  unfold LlastZeroScale
  exact div_pos
    (mul_pos
      (mul_pos
        (mul_pos (inv_pos.mpr (by
          have hr : (0 : ℝ) < P.rank := by exact_mod_cast P.rank_pos
          positivity)) (Real.rpow_pos_of_pos P.k_pos _))
        P.Omega_pos)
      P.log_OmegaOld_pos)
    P.log_newHeight_pos

theorem LlastZeroScale_eq [Nonempty ι] :
    P.LlastZeroScale =
      (8 * P.rank : ℝ)⁻¹ * P.k ^ (1 - P.sigma) *
        P.OmegaOld * Real.log P.OmegaOld := by
  unfold LlastZeroScale Omega
  field_simp [P.log_newHeight_pos.ne']

/-- In particular the terminal level cannot be zero. -/
theorem one_lt_LlastZeroScale [Nonempty ι] : 1 < P.LlastZeroScale := by
  have hrankPos : (0 : ℝ) < P.rank := by exact_mod_cast P.rank_pos
  have hdenPos : (0 : ℝ) < 8 * P.rank := mul_pos (by norm_num) hrankPos
  have hlogNumerical : (8 : ℝ) < 13 * Real.log 2 := by
    nlinarith [Real.log_two_gt_d9]
  have hsmall : 8 * (P.rank : ℝ) <
      13 * (P.rank : ℝ) * Real.log 2 := by
    have := mul_lt_mul_of_pos_right hlogNumerical hrankPos
    nlinarith
  have hk : (13 : ℝ) ≤ P.k ^ (1 - P.sigma) :=
    P.thirteen_le_k_rpow_one_sub_sigma
  have hkpos : 0 ≤ P.k ^ (1 - P.sigma) :=
    (Real.rpow_pos_of_pos P.k_pos _).le
  have hprod : 13 * (P.rank : ℝ) * Real.log 2 ≤
      P.k ^ (1 - P.sigma) * P.OmegaOld * Real.log P.OmegaOld := by
    calc
      13 * (P.rank : ℝ) * Real.log 2 ≤
          P.k ^ (1 - P.sigma) * (P.rank : ℝ) * Real.log 2 := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right hk hrankPos.le) log_two_pos.le
      _ ≤ P.k ^ (1 - P.sigma) * P.OmegaOld * Real.log 2 := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left P.rank_le_OmegaOld hkpos) log_two_pos.le
      _ ≤ P.k ^ (1 - P.sigma) * P.OmegaOld * Real.log P.OmegaOld := by
        exact mul_le_mul_of_nonneg_left P.log_two_le_log_OmegaOld
          (mul_nonneg hkpos P.OmegaOld_pos.le)
  rw [P.LlastZeroScale_eq]
  rw [show (8 * (P.rank : ℝ))⁻¹ * P.k ^ (1 - P.sigma) *
      P.OmegaOld * Real.log P.OmegaOld =
      (8 * (P.rank : ℝ))⁻¹ *
        (P.k ^ (1 - P.sigma) * P.OmegaOld * Real.log P.OmegaOld) by ring]
  apply (one_lt_inv_mul₀ hdenPos).2
  exact hsmall.trans_le hprod

theorem one_le_LlastZeroScale [Nonempty ι] : 1 ≤ P.LlastZeroScale :=
  P.one_lt_LlastZeroScale.le

/-- The corrected upper-level exponent is exactly one factor `k^epsilon`
above the last-coordinate side length. -/
theorem k_rpow_epsilon_mul_LlastZeroScale_eq_levelBound [Nonempty ι] :
    P.k ^ P.epsilon * P.LlastZeroScale = P.levelBound := by
  unfold LlastZeroScale levelBound Omega
  have hlog : Real.log P.newHeight ≠ 0 := P.log_newHeight_pos.ne'
  field_simp [hlog]
  rw [show P.k ^ P.epsilon * P.k ^ (1 - P.sigma) =
      P.k ^ (1 - (P.sigma - P.epsilon)) by
    rw [← Real.rpow_add P.k_pos]
    congr 1
    ring]
  ring

/-- Final source level: the last-coordinate side is strictly below a
`q`-power, while that power satisfies the corrected strict upper bound.
The minimal `q`-power above `LlastZeroScale` works because
`q < k^epsilon`. -/
theorem exists_terminal_level [Nonempty ι] :
    ∃ N : ℕ,
      P.LlastZeroScale < ((P.q ^ N : ℕ) : ℝ) ∧ P.LevelOK N := by
  classical
  have hex : ∃ J : ℕ, P.LlastZeroScale < ((P.q ^ J : ℕ) : ℝ) := by
    obtain ⟨m, hm⟩ := exists_nat_gt P.LlastZeroScale
    refine ⟨m, hm.trans ?_⟩
    exact_mod_cast Nat.lt_pow_self P.one_lt_q
  let firstGood : ℕ := Nat.find hex
  have hGood : P.LlastZeroScale < ((P.q ^ firstGood : ℕ) : ℝ) :=
    Nat.find_spec hex
  refine ⟨firstGood, hGood, ?_⟩
  unfold LevelOK
  by_cases hzero : firstGood = 0
  · simpa [hzero] using P.one_lt_levelBound
  · have hpos : 0 < firstGood := Nat.pos_of_ne_zero hzero
    have hpredlt : firstGood - 1 < firstGood :=
      Nat.sub_lt hpos (by norm_num)
    have hminimal :
        ¬ P.LlastZeroScale <
          ((P.q ^ (firstGood - 1) : ℕ) : ℝ) :=
      Nat.find_min hex hpredlt
    have hpred : ((P.q ^ (firstGood - 1) : ℕ) : ℝ) ≤
        P.LlastZeroScale := not_lt.mp hminimal
    have hqNonneg : (0 : ℝ) ≤ P.q := by positivity
    have hfirst : ((P.q ^ firstGood : ℕ) : ℝ) ≤
        (P.q : ℝ) * P.LlastZeroScale := by
      have hmul := mul_le_mul_of_nonneg_left hpred hqNonneg
      rw [← Nat.sub_add_cancel hpos, pow_succ]
      push_cast
      simpa [mul_comm] using hmul
    calc
      ((P.q ^ firstGood : ℕ) : ℝ) ≤
          (P.q : ℝ) * P.LlastZeroScale := hfirst
      _ < P.k ^ P.epsilon * P.LlastZeroScale :=
        mul_lt_mul_of_pos_right P.q_lt_k_rpow_epsilon
          P.LlastZeroScale_pos
      _ = P.levelBound := P.k_rpow_epsilon_mul_LlastZeroScale_eq_levelBound

theorem exists_terminal_level_pos [Nonempty ι] :
    ∃ N : ℕ, 0 < N ∧
      P.LlastZeroScale < ((P.q ^ N : ℕ) : ℝ) ∧ P.LevelOK N := by
  obtain ⟨N, hlower, hupper⟩ := P.exists_terminal_level
  refine ⟨N, ?_, hlower, hupper⟩
  by_contra hN
  have hzero : N = 0 := Nat.eq_zero_of_not_pos hN
  simp [hzero] at hlower
  linarith [P.one_lt_LlastZeroScale]

theorem LlastZero_cast_le [Nonempty ι] :
    (P.LlastZero : ℝ) ≤ P.LlastZeroScale := by
  exact Nat.floor_le P.LlastZeroScale_pos.le

theorem LlastZeroScale_lt_add_one :
    P.LlastZeroScale < (P.LlastZero : ℝ) + 1 := by
  exact Nat.lt_floor_add_one _

theorem Lzero_add_one_eq_LzeroPlusOne :
    P.Lzero + 1 = P.LzeroPlusOne := by
  unfold Lzero
  have h := P.LzeroPlusOne_pos
  omega

end VDPLParameters

end

end Erdos240

#print axioms Erdos240.VDPLParameters.Slevel_succ_le_Sstep
#print axioms Erdos240.VDPLParameters.LevelOK.mono
#print axioms Erdos240.log_vdplSourceBound_cast_le_three_mul_log
#print axioms Erdos240.VDPLParameters.one_le_log_log_oldHeight
#print axioms Erdos240.VDPLParameters.one_le_log_log_newHeight
#print axioms Erdos240.VDPLParameters.equationOneThreshold_lt_k
#print axioms Erdos240.VDPLParameters.log_newHeight_le_heightConstant_mul_log_newPrime
#print axioms Erdos240.VDPLParameters.exists_level_with_two_sided_bounds
#print axioms Erdos240.VDPLParameters.levelScale_div_six_floor_le_terminalBudget
#print axioms Erdos240.VDPLParameters.lemmaFourRadiusScale_terminal
#print axioms Erdos240.VDPLParameters.exists_terminal_level_pos
