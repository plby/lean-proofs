/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos547b.Section6RichHierarchy

/-!
# One explicit eventual hierarchy for Zhao's Section 6

This file fixes all real/rational scales used by the quantitative-large-cluster
entry and by Claims 6.16--6.18.  The only input is the final structural error
`β`.  Integral scales are obtained by the floor/ceiling constructors from
`RoundedScales`; consequently none of the downstream statements needs an
exact equality between a real product and a natural number.

The definitions here are numerical.  They do not package an embedding or an
extremal conclusion.  Structural hypotheses which depend on the actual
regularity witness or matching decomposition remain with their respective
theorems.
-/

noncomputable section

namespace Erdos547b.ZhaoSection6EventualParameters

open Erdos547b.ZhaoDegreeForm
open Erdos547b.ZhaoDegreeFormQuantitative
open Erdos547b.ZhaoRoundedScales
open Erdos547b.ZhaoSection6RichHierarchy
open Erdos547b.ZhaoStability
open Erdos547b.ZhaoStabilityPropertyRichEntry

/-- Master small parameter.  The denominator leaves room for the final
`16 * (rho + rho₁)` reduced-crossing loss. -/
def tiny (β : ℚ) : ℚ := β / 4096

/-- Claim-6.17 scale.  Taking a literal cube makes the Claim-6.18 cube root
rational. -/
def rho (β : ℚ) : ℚ := tiny β ^ 3

/-- Lemma-6.11 exceptional-family threshold `eta`, far below `rho`. -/
def eta (β : ℚ) : ℚ := rho β ^ 2 / 1000

/-- The literal fourth root `d^(1/4)`, far below `eta`. -/
def fourthRootD (β : ℚ) : ℚ := eta β ^ 2 / 1000

/-- The rich-cluster scale `d = (d^(1/4))^2`.  This is also the scale used
for the quantitative high-degree reservoirs in Claim 6.1. -/
def sigma (β : ℚ) : ℚ := fourthRootD β ^ 2

/-- Degree-form reduced-density cutoff.  It is strictly above four times the
rich-reservoir scale, exactly as required by `richQuota_density_separation`. -/
def reducedDensity (β : ℚ) : ℚ := 5 * sigma β

/-- The forest-embedding reserve `gamma`, below `d = sigma^2`. -/
def embeddingGamma (β : ℚ) : ℚ := sigma β ^ 2 / 1000

/-- Regularity error at the product scale required by the dynamic
regular-pair embedding: `epsilon ≪ reducedDensity * gamma`. -/
def regularityEpsilon (β : ℚ) : ℚ :=
  reducedDensity β * embeddingGamma β / 1000

/-- The real parameter denoted `rho₁` in Claim 6.18. -/
def rhoOne (β : ℚ) : ℝ := (tiny β : ℝ)

/-- An explicit lower bound on the padded reduced half.  The factor `200`
absorbs all unit errors introduced by floors and ceilings. -/
def section6K₀ (β : ℚ) : ℕ :=
  upperScale (200 / (sigma β : ℝ)) + 1

/-- Degree form is asked for twice the downstream reduced-half threshold,
so every cleaned partition has padded half at least `section6K₀`. -/
def section6M₀ (β : ℚ) : ℕ := 2 * section6K₀ β

/-- An explicit host threshold.  Its first term invokes degree-form
regularity.  The second makes every bounded reduced-graph error negligible
compared with `β n`; later endpoint lemmas may freely enlarge this maximum. -/
def section6N₀ (β : ℚ) : ℕ :=
  let m₀ := section6M₀ β
  let M := degreeFormBound (regularityEpsilon β) m₀
  max (degreeFormThreshold (regularityEpsilon β) m₀ + 2)
    (upperScale
      ((1000000 : ℝ) * (M + 1) / (sigma β : ℝ)) + 2)

/-- Downward-rounded `rho * k`, used as the Claim-6.17 value `r`. -/
def mainScale (β : ℚ) (k : ℕ) : ℕ :=
  lowerScale ((rho β : ℝ) * k)

/-- Claim 6.16 uses `rho0 = rho/10`, not the larger Claim-6.17 scale. -/
def claim616Scale (β : ℚ) (k : ℕ) : ℕ :=
  lowerScale (((rho β : ℝ) / 10) * k)

/-- Zhao's cap on the number of edges of `M_in`.  In the padded convention
the reduced graph has `2 * k` vertices, so `M_in` is capped at `⌊k/2⌋`
edges.  This scale is deliberately distinct from `mainScale = ⌊ρk⌋`,
which is the much smaller cluster-set size used only in Claim 6.16. -/
def minEdgeCap (k : ℕ) : ℕ := k / 2

/-- Upward-rounded `eta * k`, used for exceptional families and `h`. -/
def auxiliaryScale (β : ℚ) (k : ℕ) : ℕ :=
  upperScale ((eta β : ℝ) * k)

/-- Claim 6.1's integral slack. -/
def claim61C (β : ℚ) (k : ℕ) : ℕ :=
  upperScale (50 * (sigma β : ℝ) * k)

/-- The literal miss parameter returned by quantitative Claim 6.1. -/
def claim61Miss (β : ℚ) (k : ℕ) : ℕ :=
  2 * claim61C β k + 1

/-- Claim 6.17's optional-matching scale `q`. -/
def claim617Q (β : ℚ) (k : ℕ) : ℕ :=
  upperScale ((fourthRootD β : ℝ) * k)

/-- Claim 6.17's exceptional-size scale `h`. -/
def claim617H (β : ℚ) (k : ℕ) : ℕ := auxiliaryScale β k

/-- Claim 6.18's high-degree pruning scale `a`. -/
def claim618A (β : ℚ) (k : ℕ) : ℕ :=
  lowerScale (8 * rhoOne β * k)

/-- Claim 6.18's bad-vertex budget `b`. -/
def claim618B (β : ℚ) (k : ℕ) : ℕ :=
  lowerScale ((7 / 2 : ℝ) * rhoOne β * k)

/-- The lower-degree threshold `z` in Claim 6.18's double count. -/
def claim618Z (β : ℚ) (k : ℕ) : ℕ :=
  lowerScale ((7 / 4 : ℝ) * rhoOne β * k)

/-- The common-neighbor threshold `u` in Claim 6.18. -/
def claim618U (β : ℚ) (k : ℕ) : ℕ :=
  lowerScale (10 * rhoOne β ^ 2 * k)

/-- The partner threshold is chosen literally as `u+q`, so the partner
arithmetic premise of Claim 6.18 is definitional. -/
def claim618T (β : ℚ) (k : ℕ) : ℕ :=
  claim618U β k + claim617Q β k

/-! ### The Lemma-6.11/Claim-6.16 source margins

These constants are kept separate from the reduced-density cutoff.  The
quantity called `d` in Lemmas 6.13--6.15 is the rich-cluster scale `sigma`,
so its square root is the preceding fourth-root scale.  The cleaned reduced
graph uses the slightly larger cutoff `reducedDensity = 5 * sigma`. -/

/-- The explicit value of `sqrt d` in Lemmas 6.13--6.15. -/
def lemma611DSqrt (β : ℚ) : ℝ := (fourthRootD β : ℝ)

/-- The corresponding literal nonnegative `d`. -/
def lemma611D (β : ℚ) : ℝ := lemma611DSqrt β ^ 2

/-- The quantitative loss in `deg(A,M_in)`, exactly `8*eta`. -/
def lemma611EpsilonOne (β : ℚ) : ℝ := 8 * (eta β : ℝ)

/-- The real degree target used when constructing `M_in`. -/
def lemma611TargetA (β : ℚ) (n : ℝ) : ℝ :=
  (1 - lemma611EpsilonOne β) * n

/-- Claim 6.16 applies Lemma 6.14(2) with
`epsilon2 = rho0/2 = rho/20`. -/
def claim616EpsilonTwo (β : ℚ) : ℝ := (rho β : ℝ) / 20

/-- The online-embedding reserve is `gamma`, above regularity epsilon and
below `d`. -/
def claim616Gamma (β : ℚ) : ℝ := (embeddingGamma β : ℝ)

/-- The integral lower target in display (6.23): select `F₀` just past
`deg(A,M₀) + (rho0/2)n = deg(A,M₀) + (rho/20)n`. -/
def claim616SelectedTarget (β : ℚ) (degreeMzero n : ℝ) : ℕ :=
  upperScale (degreeMzero + claim616EpsilonTwo β * n)

theorem tiny_pos {β : ℚ} (hβ : 0 < β) : 0 < tiny β := by
  simp only [tiny]
  positivity

theorem tiny_le_one {β : ℚ} (hβ : β ≤ 1 / 4) : tiny β ≤ 1 := by
  simp only [tiny]
  norm_num at hβ ⊢
  linarith

theorem rho_pos {β : ℚ} (hβ : 0 < β) : 0 < rho β := by
  simp only [rho]
  positivity [tiny_pos hβ]

theorem rho_le_one {β : ℚ} (hβ0 : 0 < β) (hβ1 : β ≤ 1 / 4) :
    rho β ≤ 1 := by
  have ht0 : (0 : ℚ) ≤ tiny β := (tiny_pos hβ0).le
  have ht1 : tiny β ≤ 1 := tiny_le_one hβ1
  simpa only [rho, one_pow] using pow_le_pow_left₀ ht0 ht1 3

theorem eta_pos {β : ℚ} (hβ : 0 < β) : 0 < eta β := by
  simp only [eta]
  positivity [rho_pos hβ]

theorem fourthRootD_pos {β : ℚ} (hβ : 0 < β) :
    0 < fourthRootD β := by
  simp only [fourthRootD]
  positivity [eta_pos hβ]

theorem sigma_pos {β : ℚ} (hβ : 0 < β) : 0 < sigma β := by
  simp only [sigma]
  positivity [fourthRootD_pos hβ]

theorem reducedDensity_pos {β : ℚ} (hβ : 0 < β) :
    0 < reducedDensity β := by
  simp only [reducedDensity]
  positivity [sigma_pos hβ]

theorem embeddingGamma_pos {β : ℚ} (hβ : 0 < β) :
    0 < embeddingGamma β := by
  simp only [embeddingGamma]
  positivity [sigma_pos hβ]

theorem rhoOne_pos {β : ℚ} (hβ : 0 < β) : 0 < rhoOne β := by
  change (0 : ℝ) < (tiny β : ℝ)
  exact_mod_cast tiny_pos hβ

theorem rhoOne_le_one {β : ℚ} (hβ : β ≤ 1 / 4) : rhoOne β ≤ 1 := by
  change (tiny β : ℝ) ≤ 1
  exact_mod_cast tiny_le_one hβ

theorem rho_cast_eq_rhoOne_cube (β : ℚ) :
    (rho β : ℝ) = rhoOne β ^ 3 := by
  simp only [rho, rhoOne, Rat.cast_pow]

theorem sigma_le_rhoOne_sq_div {β : ℚ}
    (hβ0 : 0 < β) (hβ1 : β ≤ 1 / 4) :
    (sigma β : ℝ) ≤ rhoOne β ^ 2 / 1000 := by
  have hx0 : (0 : ℝ) < rhoOne β := rhoOne_pos hβ0
  have hx1 : rhoOne β ≤ 1 := rhoOne_le_one hβ1
  have hr1 : (rho β : ℝ) ≤ 1 := by
    exact_mod_cast rho_le_one hβ0 hβ1
  have heta0 : (0 : ℝ) < (eta β : ℝ) := by
    exact_mod_cast eta_pos hβ0
  have heta1 : (eta β : ℝ) ≤ 1 := by
    have hr0 : (0 : ℝ) ≤ (rho β : ℝ) := by
      exact_mod_cast (rho_pos hβ0).le
    have hrSq : (rho β : ℝ) ^ 2 ≤ 1 := by
      simpa using pow_le_pow_left₀ hr0 hr1 2
    rw [eta]
    push_cast
    nlinarith
  have hfEta : (fourthRootD β : ℝ) ≤ (eta β : ℝ) := by
    have hetaSqLe : (eta β : ℝ) ^ 2 ≤ (eta β : ℝ) := by
      nlinarith [mul_nonneg heta0.le (sub_nonneg.mpr heta1)]
    rw [fourthRootD]
    push_cast
    nlinarith
  have hf1 : (fourthRootD β : ℝ) ≤ 1 := hfEta.trans heta1
  have hsF : (sigma β : ℝ) ≤ (fourthRootD β : ℝ) := by
    have hf0 : (0 : ℝ) ≤ (fourthRootD β : ℝ) := by
      exact_mod_cast (fourthRootD_pos hβ0).le
    have hfSqLe : (fourthRootD β : ℝ) ^ 2 ≤
        (fourthRootD β : ℝ) := by
      nlinarith [mul_nonneg hf0 (sub_nonneg.mpr hf1)]
    rw [sigma]
    push_cast
    exact hfSqLe
  have heta_rho : (eta β : ℝ) ≤ (rho β : ℝ) / 1000 := by
    have hr0 : (0 : ℝ) ≤ (rho β : ℝ) := by
      exact_mod_cast (rho_pos hβ0).le
    have hrSqLe : (rho β : ℝ) ^ 2 ≤ (rho β : ℝ) := by
      nlinarith [mul_nonneg hr0 (sub_nonneg.mpr hr1)]
    rw [eta]
    push_cast
    nlinarith
  rw [rho_cast_eq_rhoOne_cube] at heta_rho
  nlinarith [sq_nonneg (rhoOne β),
    mul_nonneg (sq_nonneg (rhoOne β)) (sub_nonneg.mpr hx1)]

theorem sigma_le_one_div {β : ℚ}
    (hβ0 : 0 < β) (hβ1 : β ≤ 1 / 4) :
    (sigma β : ℝ) ≤ 1 / 1000 := by
  have hs := sigma_le_rhoOne_sq_div hβ0 hβ1
  have hx0 : (0 : ℝ) ≤ rhoOne β := (rhoOne_pos hβ0).le
  have hx1 : rhoOne β ≤ 1 := rhoOne_le_one hβ1
  nlinarith [sq_nonneg (rhoOne β)]

theorem eta_le_rho_div_1000 {β : ℚ}
    (hβ0 : 0 < β) (hβ1 : β ≤ 1 / 4) :
    (eta β : ℝ) ≤ (rho β : ℝ) / 1000 := by
  have hr0 : (0 : ℝ) ≤ (rho β : ℝ) := by
    exact_mod_cast (rho_pos hβ0).le
  have hr1 : (rho β : ℝ) ≤ 1 := by
    exact_mod_cast rho_le_one hβ0 hβ1
  have hrSqLe : (rho β : ℝ) ^ 2 ≤ (rho β : ℝ) := by
    nlinarith [mul_nonneg hr0 (sub_nonneg.mpr hr1)]
  rw [eta]
  push_cast
  nlinarith

theorem fourthRootD_le_eta_div_1000 {β : ℚ}
    (hβ0 : 0 < β) (hβ1 : β ≤ 1 / 4) :
    (fourthRootD β : ℝ) ≤ (eta β : ℝ) / 1000 := by
  have heta0 : (0 : ℝ) ≤ (eta β : ℝ) := by
    exact_mod_cast (eta_pos hβ0).le
  have heta1 : (eta β : ℝ) ≤ 1 :=
    (eta_le_rho_div_1000 hβ0 hβ1).trans (by
      have hr : (rho β : ℝ) ≤ 1 := by
        exact_mod_cast rho_le_one hβ0 hβ1
      nlinarith)
  have hetaSqLe : (eta β : ℝ) ^ 2 ≤ (eta β : ℝ) := by
    nlinarith [mul_nonneg heta0 (sub_nonneg.mpr heta1)]
  rw [fourthRootD]
  push_cast
  nlinarith

theorem sigma_le_fourthRootD {β : ℚ}
    (hβ0 : 0 < β) (hβ1 : β ≤ 1 / 4) :
    (sigma β : ℝ) ≤ (fourthRootD β : ℝ) := by
  have hf0 : (0 : ℝ) ≤ (fourthRootD β : ℝ) := by
    exact_mod_cast (fourthRootD_pos hβ0).le
  have hf1 : (fourthRootD β : ℝ) ≤ 1 :=
    (fourthRootD_le_eta_div_1000 hβ0 hβ1).trans (by
      have heta : (eta β : ℝ) ≤ 1 :=
        (eta_le_rho_div_1000 hβ0 hβ1).trans (by
          have hr : (rho β : ℝ) ≤ 1 := by
            exact_mod_cast rho_le_one hβ0 hβ1
          nlinarith)
      nlinarith)
  have hfSqLe : (fourthRootD β : ℝ) ^ 2 ≤
      (fourthRootD β : ℝ) := by
    nlinarith [mul_nonneg hf0 (sub_nonneg.mpr hf1)]
  rw [sigma]
  push_cast
  exact hfSqLe

theorem embeddingGamma_le_eta {β : ℚ}
    (hβ0 : 0 < β) (hβ1 : β ≤ 1 / 4) :
    (embeddingGamma β : ℝ) ≤ (eta β : ℝ) := by
  have hs0 : (0 : ℝ) ≤ (sigma β : ℝ) := by
    exact_mod_cast (sigma_pos hβ0).le
  have hs1 := sigma_le_one_div hβ0 hβ1
  have heta0 : (0 : ℝ) ≤ (eta β : ℝ) := by
    exact_mod_cast (eta_pos hβ0).le
  have hfEta : (fourthRootD β : ℝ) ≤ (eta β : ℝ) := by
    have hf := fourthRootD_le_eta_div_1000 hβ0 hβ1
    nlinarith
  have hsEta := (sigma_le_fourthRootD hβ0 hβ1).trans hfEta
  rw [embeddingGamma]
  push_cast
  nlinarith [sq_nonneg (sigma β : ℝ)]

theorem regularityEpsilon_pos {β : ℚ} (hβ : 0 < β) :
    0 < regularityEpsilon β := by
  simp only [regularityEpsilon]
  positivity [reducedDensity_pos hβ, embeddingGamma_pos hβ]

/-- The product-scale regularity choice leaves the literal coefficient
needed by the dynamic small-component embedding.  Three epsilon-sized
charges (the component, the regularity reserve, and one rounding unit) fit
inside the reduced-density gap over an `embeddingGamma` fraction of a
cluster. -/
theorem three_regularityEpsilon_le_density_gap_mul_embeddingGamma
    {β : ℚ} (hβ0 : 0 < β) (hβ1 : β ≤ 1 / 4) :
    3 * (regularityEpsilon β : ℝ) ≤
      ((reducedDensity β : ℝ) - (regularityEpsilon β : ℝ)) *
        (embeddingGamma β : ℝ) := by
  have hd0 : (0 : ℝ) ≤ (reducedDensity β : ℝ) := by
    exact_mod_cast (reducedDensity_pos hβ0).le
  have hg0 : (0 : ℝ) ≤ (embeddingGamma β : ℝ) := by
    exact_mod_cast (embeddingGamma_pos hβ0).le
  have hg1 : (embeddingGamma β : ℝ) ≤ 1 := by
    have hgEta := embeddingGamma_le_eta hβ0 hβ1
    have hetaRho := eta_le_rho_div_1000 hβ0 hβ1
    have hrho : (rho β : ℝ) ≤ 1 := by
      exact_mod_cast rho_le_one hβ0 hβ1
    linarith
  have hε : (regularityEpsilon β : ℝ) =
      (reducedDensity β : ℝ) * (embeddingGamma β : ℝ) / 1000 := by
    rw [regularityEpsilon]
    push_cast
    ring
  have hfactor : (0 : ℝ) ≤ 997 - (embeddingGamma β : ℝ) := by
    linarith
  have hproduct : 0 ≤
      (reducedDensity β : ℝ) * (embeddingGamma β : ℝ) *
        (997 - (embeddingGamma β : ℝ)) := by
    exact mul_nonneg (mul_nonneg hd0 hg0) hfactor
  rw [hε]
  nlinarith

/-- In particular the regularity error is strictly below the reduced-pair
density cutoff, so every dynamic regular-pair density gap is nonnegative. -/
theorem regularityEpsilon_lt_reducedDensity
    {β : ℚ} (hβ0 : 0 < β) (hβ1 : β ≤ 1 / 4) :
    (regularityEpsilon β : ℝ) < (reducedDensity β : ℝ) := by
  have hε := three_regularityEpsilon_le_density_gap_mul_embeddingGamma
    hβ0 hβ1
  have hεpos : (0 : ℝ) < (regularityEpsilon β : ℝ) := by
    exact_mod_cast regularityEpsilon_pos hβ0
  have hg0 : (0 : ℝ) ≤ (embeddingGamma β : ℝ) := by
    exact_mod_cast (embeddingGamma_pos hβ0).le
  by_contra hnot
  have hgap : (reducedDensity β : ℝ) -
      (regularityEpsilon β : ℝ) ≤ 0 := sub_nonpos.mpr (le_of_not_gt hnot)
  have hright : ((reducedDensity β : ℝ) -
        (regularityEpsilon β : ℝ)) * (embeddingGamma β : ℝ) ≤ 0 :=
    mul_nonpos_of_nonpos_of_nonneg hgap hg0
  linarith

theorem regularityEpsilon_cast_eq (β : ℚ) :
    (regularityEpsilon β : ℝ) =
      (reducedDensity β : ℝ) * (embeddingGamma β : ℝ) / 1000 := by
  rw [regularityEpsilon]
  push_cast
  ring

/-- The product-scale choice leaves the precise one-component margin needed
by the dynamic regular-pair embedding. -/
theorem regularityEpsilon_le_density_margin {β : ℚ}
    (hβ0 : 0 < β) (hβ1 : β ≤ 1 / 4) :
    (regularityEpsilon β : ℝ) ≤
      ((reducedDensity β : ℝ) - (regularityEpsilon β : ℝ)) *
        (embeddingGamma β : ℝ) := by
  have hd0 : (0 : ℝ) ≤ (reducedDensity β : ℝ) := by
    exact_mod_cast (reducedDensity_pos hβ0).le
  have hg0 : (0 : ℝ) ≤ (embeddingGamma β : ℝ) := by
    exact_mod_cast (embeddingGamma_pos hβ0).le
  have hg1 : (embeddingGamma β : ℝ) ≤ 1 := by
    exact (embeddingGamma_le_eta hβ0 hβ1).trans <| by
      have heta := eta_le_rho_div_1000 hβ0 hβ1
      have hrho : (rho β : ℝ) ≤ 1 := by
        exact_mod_cast rho_le_one hβ0 hβ1
      linarith
  rw [regularityEpsilon_cast_eq]
  nlinarith [mul_nonneg (mul_nonneg hd0 hg0)
    (show 0 ≤ 1 - ((embeddingGamma β : ℝ) + 1) / 1000 by linarith)]

theorem lemma611DSqrt_pos {β : ℚ} (hβ : 0 < β) :
    0 < lemma611DSqrt β := by
  simp only [lemma611DSqrt]
  exact_mod_cast fourthRootD_pos hβ

@[simp] theorem sqrt_lemma611D {β : ℚ} (hβ : 0 < β) :
    Real.sqrt (lemma611D β) = lemma611DSqrt β := by
  rw [lemma611D, Real.sqrt_sq (lemma611DSqrt_pos hβ).le]

theorem lemma611EpsilonOne_nonneg {β : ℚ} (hβ : 0 < β) :
    0 ≤ lemma611EpsilonOne β := by
  simp only [lemma611EpsilonOne]
  have hs : (0 : ℝ) ≤ (eta β : ℝ) := by
    exact_mod_cast (eta_pos hβ).le
  positivity

theorem lemma611EpsilonOne_le_two_fifths {β : ℚ}
    (hβ0 : 0 < β) (hβ1 : β ≤ 1 / 4) :
    lemma611EpsilonOne β ≤ 2 / 5 := by
  have heta := eta_le_rho_div_1000 hβ0 hβ1
  have hrho : (rho β : ℝ) ≤ 1 := by
    exact_mod_cast rho_le_one hβ0 hβ1
  simp only [lemma611EpsilonOne]
  nlinarith

theorem lemma611TargetA_nonneg {β : ℚ}
    (hβ0 : 0 < β) (hβ1 : β ≤ 1 / 4)
    {n : ℝ} (hn : 0 ≤ n) :
    0 ≤ lemma611TargetA β n := by
  have he := lemma611EpsilonOne_le_two_fifths hβ0 hβ1
  have hfactor : 0 ≤ 1 - lemma611EpsilonOne β := by nlinarith
  simp only [lemma611TargetA]
  exact mul_nonneg hfactor hn

/-- The exact Lemma-6.14(2) hierarchy inequality with
`epsilon1 = 8*eta`, `epsilon2 = rho/20`, and the separate online reserve
`gamma = embeddingGamma`. -/
theorem claim616_margin_hierarchy {β : ℚ}
    (hβ0 : 0 < β) (hβ1 : β ≤ 1 / 4) :
    3 * claim616Gamma β ≤
      claim616EpsilonTwo β - lemma611EpsilonOne β := by
  have heta := eta_le_rho_div_1000 hβ0 hβ1
  have hgamma := embeddingGamma_le_eta hβ0 hβ1
  change 3 * (embeddingGamma β : ℝ) ≤
    (rho β : ℝ) / 20 - 8 * (eta β : ℝ)
  calc
    3 * (embeddingGamma β : ℝ) ≤ 3 * (eta β : ℝ) := by linarith
    _ ≤ (rho β : ℝ) / 20 - 8 * (eta β : ℝ) := by
      have hrho : (0 : ℝ) < (rho β : ℝ) := by
        exact_mod_cast rho_pos hβ0
      have hscaled := mul_le_mul_of_nonneg_left heta
        (show (0 : ℝ) ≤ 11 by norm_num)
      linarith

theorem claim616_selectedTarget_real_le
    (β : ℚ) (degreeMzero n : ℝ) :
    degreeMzero + claim616EpsilonTwo β * n ≤
      (claim616SelectedTarget β degreeMzero n : ℝ) := by
  exact le_upperScale_cast _

theorem claim616_degreeMzero_le_target_sub_margin
    (β : ℚ) (degreeMzero n : ℝ) :
    degreeMzero ≤ (claim616SelectedTarget β degreeMzero n : ℝ) -
      claim616EpsilonTwo β * n := by
  have := claim616_selectedTarget_real_le β degreeMzero n
  linarith

theorem claim616_selectedTarget_cast_lt
    {β : ℚ} (hβ : 0 < β)
    {degreeMzero n : ℝ} (hdegree : 0 ≤ degreeMzero) (hn : 0 ≤ n) :
    (claim616SelectedTarget β degreeMzero n : ℝ) <
      degreeMzero + claim616EpsilonTwo β * n + 1 := by
  apply upperScale_cast_lt_add_one
  have hrho : (0 : ℝ) ≤ (rho β : ℝ) := by
    exact_mod_cast (rho_pos hβ).le
  simp only [claim616EpsilonTwo]
  positivity

/-- The density separation consumed by the quantitative rich-cluster entry. -/
theorem rich_cutoff_separation {β : ℚ} (hβ : 0 < β) :
    (4 : ℝ) * (sigma β : ℝ) < (reducedDensity β : ℝ) := by
  have hs : (0 : ℝ) < (sigma β : ℝ) := by exact_mod_cast sigma_pos hβ
  norm_num [reducedDensity]
  linarith

/-- Because `rho` is a literal cube, Claim 6.18's real cube root is the
rational master scale `tiny`. -/
theorem rhoOne_eq_rpow {β : ℚ} (hβ : 0 < β) :
    rhoOne β = Real.rpow (rho β : ℝ) (1 / 3 : ℝ) := by
  have hx : (0 : ℝ) ≤ rhoOne β := (rhoOne_pos hβ).le
  rw [rho_cast_eq_rhoOne_cube]
  simpa [one_div] using
    (Real.pow_rpow_inv_natCast hx (by norm_num : (3 : ℕ) ≠ 0)).symm

/-- The complete reduced-crossing coefficient is already far below `β`.
This is the scale inequality used at the final EC2 lift. -/
theorem final_reduced_coefficient_lt {β : ℚ}
    (hβ0 : 0 < β) (hβ1 : β ≤ 1 / 4) :
    16 * ((rho β : ℝ) + rhoOne β) < (β : ℝ) / 64 := by
  have ht0 : (0 : ℝ) < (tiny β : ℝ) := by exact_mod_cast tiny_pos hβ0
  have ht1 : (tiny β : ℝ) ≤ 1 := by exact_mod_cast tiny_le_one hβ1
  have hr_le_t : (rho β : ℝ) ≤ tiny β := by
    have ht_sq : (tiny β : ℝ) ^ 2 ≤ 1 := by
      have := pow_le_pow_left₀ ht0.le ht1 2
      simpa using this
    rw [rho]
    push_cast
    nlinarith
  have htβ : (tiny β : ℝ) = (β : ℝ) / 4096 := by
    rw [tiny]
    push_cast
    ring
  change 16 * ((rho β : ℝ) + (tiny β : ℝ)) < (β : ℝ) / 64
  rw [htβ]
  linarith

theorem sigma_le_beta_div {β : ℚ}
    (hβ0 : 0 < β) (hβ1 : β ≤ 1 / 4) :
    (sigma β : ℝ) ≤ (β : ℝ) / 4096000 := by
  have hs := sigma_le_rhoOne_sq_div hβ0 hβ1
  have hx0 : (0 : ℝ) ≤ rhoOne β := (rhoOne_pos hβ0).le
  have hx1 : rhoOne β ≤ 1 := rhoOne_le_one hβ1
  have hsx : (sigma β : ℝ) ≤ rhoOne β / 1000 := by
    nlinarith [sq_nonneg (rhoOne β)]
  have htβ : rhoOne β = (β : ℝ) / 4096 := by
    rw [rhoOne, tiny]
    push_cast
    ring
  rw [htβ] at hsx
  norm_num at hsx ⊢
  linarith

/-- Continuous margin underlying the rounded Claim-6.17 inequality. -/
theorem claim617_continuous_margin {β : ℚ}
    (hβ0 : 0 < β) (hβ1 : β ≤ 1 / 4) :
    80 * (rho β : ℝ) * (eta β : ℝ) +
        4 * (fourthRootD β : ℝ) <
      (rho β : ℝ) / 10 := by
  have hr0 : (0 : ℝ) < (rho β : ℝ) := by exact_mod_cast rho_pos hβ0
  have hr1 : (rho β : ℝ) ≤ 1 := by exact_mod_cast rho_le_one hβ0 hβ1
  have heta := eta_le_rho_div_1000 hβ0 hβ1
  have hfourth := fourthRootD_le_eta_div_1000 hβ0 hβ1
  have heta0 : (0 : ℝ) < (eta β : ℝ) := by
    exact_mod_cast eta_pos hβ0
  have hrEta := mul_le_mul_of_nonneg_right hr1 heta0.le
  nlinarith

theorem section6K₀_pos (β : ℚ) : 0 < section6K₀ β := by
  simp only [section6K₀]
  omega

theorem section6M₀_pos (β : ℚ) : 0 < section6M₀ β := by
  simp only [section6M₀]
  exact Nat.mul_pos (by norm_num) (section6K₀_pos β)

theorem section6K₀_le_paddedHalf_of_m₀_le_card
    (β : ℚ) (ι : Type*) [Fintype ι]
    (hcard : section6M₀ β ≤ Fintype.card ι) :
    section6K₀ β ≤ Erdos547b.ZhaoEvenReducedPadding.paddedHalf ι := by
  simp only [section6M₀,
    Erdos547b.ZhaoEvenReducedPadding.paddedHalf] at hcard ⊢
  omega

theorem section6K₀_le_witnessPaddedHalf
    {β : ℚ} {N M : ℕ} {G : SimpleGraph (Fin N)}
    [DecidableRel G.Adj]
    (W : DegreeFormWitness G (regularityEpsilon β) (reducedDensity β)
      (section6M₀ β) M) :
    section6K₀ β ≤
      Erdos547b.ZhaoEvenReducedPadding.paddedHalf
        {Q // Q ∈ W.partition.parts} := by
  apply section6K₀_le_paddedHalf_of_m₀_le_card
  simpa using W.lower_parts

/-- The eventual reduced-order threshold is chosen at the smallest scale. -/
theorem sigma_target_large {β : ℚ} (hβ : 0 < β) {k : ℕ}
    (hk : section6K₀ β ≤ k) :
    (200 : ℝ) ≤ (sigma β : ℝ) * k := by
  have hs : (0 : ℝ) < (sigma β : ℝ) := by exact_mod_cast sigma_pos hβ
  have hceil : 200 / (sigma β : ℝ) ≤
      (upperScale (200 / (sigma β : ℝ)) : ℝ) :=
    le_upperScale_cast _
  have hkR : ((section6K₀ β : ℕ) : ℝ) ≤ k := by exact_mod_cast hk
  have hkTarget : 200 / (sigma β : ℝ) ≤ (k : ℝ) := by
    simp only [section6K₀, Nat.cast_add, Nat.cast_one] at hkR
    linarith
  simpa only [mul_comm] using (div_le_iff₀ hs).mp hkTarget

/-- Each larger Section-6 scale is therefore large as well. -/
theorem fourthRootD_target_large {β : ℚ}
    (hβ0 : 0 < β) (hβ1 : β ≤ 1 / 4) {k : ℕ}
    (hk : section6K₀ β ≤ k) :
    (200 : ℝ) ≤ (fourthRootD β : ℝ) * k := by
  exact (sigma_target_large hβ0 hk).trans
    (mul_le_mul_of_nonneg_right (sigma_le_fourthRootD hβ0 hβ1)
      (by positivity))

theorem eta_target_large {β : ℚ}
    (hβ0 : 0 < β) (hβ1 : β ≤ 1 / 4) {k : ℕ}
    (hk : section6K₀ β ≤ k) :
    (200 : ℝ) ≤ (eta β : ℝ) * k := by
  have hfEta : (fourthRootD β : ℝ) ≤ (eta β : ℝ) := by
    have hf := fourthRootD_le_eta_div_1000 hβ0 hβ1
    have heta0 : (0 : ℝ) ≤ (eta β : ℝ) := by
      exact_mod_cast (eta_pos hβ0).le
    nlinarith
  exact (fourthRootD_target_large hβ0 hβ1 hk).trans
    (mul_le_mul_of_nonneg_right hfEta (by positivity))

theorem main_target_large {β : ℚ}
    (hβ0 : 0 < β) (hβ1 : β ≤ 1 / 4) {k : ℕ}
    (hk : section6K₀ β ≤ k) :
    (200 : ℝ) ≤ (rho β : ℝ) * k := by
  have hetaRho : (eta β : ℝ) ≤ (rho β : ℝ) := by
    have heta := eta_le_rho_div_1000 hβ0 hβ1
    have hr0 : (0 : ℝ) ≤ (rho β : ℝ) := by
      exact_mod_cast (rho_pos hβ0).le
    nlinarith
  exact (eta_target_large hβ0 hβ1 hk).trans
    (mul_le_mul_of_nonneg_right hetaRho (by positivity))

theorem mainScale_pos {β : ℚ}
    (hβ0 : 0 < β) (hβ1 : β ≤ 1 / 4) {k : ℕ}
    (hk : section6K₀ β ≤ k) :
    0 < mainScale β k := by
  apply lowerScale_pos
  exact (show (1 : ℝ) ≤ (rho β : ℝ) * k by
    exact (by norm_num : (1 : ℝ) ≤ 200).trans
      (main_target_large hβ0 hβ1 hk))

theorem claim616Scale_pos {β : ℚ}
    (hβ0 : 0 < β) (hβ1 : β ≤ 1 / 4) {k : ℕ}
    (hk : section6K₀ β ≤ k) :
    0 < claim616Scale β k := by
  apply lowerScale_pos
  have hlarge := main_target_large hβ0 hβ1 hk
  nlinarith

theorem minEdgeCap_pos {β : ℚ}
    (hβ0 : 0 < β) (hβ1 : β ≤ 1 / 4) {k : ℕ}
    (hk : section6K₀ β ≤ k) :
    0 < minEdgeCap k := by
  have hrho : (rho β : ℝ) ≤ 1 := by
    exact_mod_cast rho_le_one hβ0 hβ1
  have hk0 : (0 : ℝ) ≤ k := by positivity
  have hrhok := mul_le_mul_of_nonneg_right hrho hk0
  norm_num at hrhok
  have hkLarge : (200 : ℝ) ≤ k :=
    (main_target_large hβ0 hβ1 hk).trans hrhok
  have hkTwo : 2 ≤ k := by exact_mod_cast (show (2 : ℝ) ≤ k by linarith)
  simp only [minEdgeCap]
  omega

theorem twice_minEdgeCap_le (k : ℕ) :
    2 * minEdgeCap k ≤ k := by
  simp only [minEdgeCap]
  omega

theorem le_twice_minEdgeCap_add_one (k : ℕ) :
    k ≤ 2 * minEdgeCap k + 1 := by
  simp only [minEdgeCap]
  omega

/-- The near-half matching cap has enough total pair capacity for the
explicit Lemma-6.11 target.  `error` is the exceptional-vertex contribution
in the identity relating the host half-order to the ordinary clusters. -/
theorem lemma611_minEdgeCap_capacity
    {β : ℚ} (hβ0 : 0 < β) (hβ1 : β ≤ 1 / 4)
    {k : ℕ} {N n error : ℝ}
    (hN : 0 < N) (hn : 0 < n) (herror : 0 ≤ error)
    (hnCovered : n ≤ (k : ℝ) * N + error)
    (hcover : (k : ℝ) * N ≤ n + N)
    (herrorSmall : error ≤ (sigma β : ℝ) * n)
    (hcluster : N ≤ 3 * (sigma β : ℝ) * n) :
    lemma611TargetA β n <
      (minEdgeCap k : ℝ) *
        (N * (2 - 3 * (eta β : ℝ))) := by
  let c := minEdgeCap k
  have hs0 : (0 : ℝ) < (sigma β : ℝ) := by
    exact_mod_cast sigma_pos hβ0
  have hs1 : (sigma β : ℝ) ≤ 1 / 1000 :=
    sigma_le_one_div hβ0 hβ1
  have heta0 : (0 : ℝ) < (eta β : ℝ) := by
    exact_mod_cast eta_pos hβ0
  have heta1 : (eta β : ℝ) ≤ 1 / 1000 := by
    have heta := eta_le_rho_div_1000 hβ0 hβ1
    have hr : (rho β : ℝ) ≤ 1 := by
      exact_mod_cast rho_le_one hβ0 hβ1
    nlinarith
  have hsEta : (sigma β : ℝ) ≤ (eta β : ℝ) := by
    have hsFourth := sigma_le_fourthRootD hβ0 hβ1
    have hfEta := fourthRootD_le_eta_div_1000 hβ0 hβ1
    nlinarith
  have hcLowerNat := le_twice_minEdgeCap_add_one k
  have hcLower : (k : ℝ) ≤ 2 * c + 1 := by
    exact_mod_cast hcLowerNat
  have hcUpperNat := twice_minEdgeCap_le k
  have hcUpper : (2 : ℝ) * c ≤ k := by
    exact_mod_cast hcUpperNat
  have hcLowerN := mul_le_mul_of_nonneg_right hcLower hN.le
  have hcUpperN := mul_le_mul_of_nonneg_right hcUpper hN.le
  have hpenalty :
      3 * (eta β : ℝ) * c * N ≤
        (3 / 2 : ℝ) * (eta β : ℝ) * ((k : ℝ) * N) := by
    have := mul_le_mul_of_nonneg_left hcUpperN
      (show (0 : ℝ) ≤ (3 / 2 : ℝ) * (eta β : ℝ) by positivity)
    nlinarith
  simp only [lemma611TargetA, lemma611EpsilonOne]
  dsimp only [c] at hcLowerN hcUpperN hpenalty ⊢
  nlinarith

theorem auxiliaryScale_pos {β : ℚ} (hβ : 0 < β) {k : ℕ}
    (hk : section6K₀ β ≤ k) :
    0 < auxiliaryScale β k := by
  have hs : (0 : ℝ) < (eta β : ℝ) := by exact_mod_cast eta_pos hβ
  have hkpos : 0 < k := (section6K₀_pos β).trans_le hk
  have htarget : (0 : ℝ) < (eta β : ℝ) * k := by positivity
  have hle : (eta β : ℝ) * k ≤ (auxiliaryScale β k : ℝ) := by
    exact le_upperScale_cast _
  have : (0 : ℝ) < (auxiliaryScale β k : ℝ) := htarget.trans_le hle
  exact_mod_cast this

theorem claim617Q_pos {β : ℚ} (hβ : 0 < β) {k : ℕ}
    (hk : section6K₀ β ≤ k) :
    0 < claim617Q β k := by
  have hf : (0 : ℝ) < (fourthRootD β : ℝ) := by
    exact_mod_cast fourthRootD_pos hβ
  have hkpos : 0 < k := (section6K₀_pos β).trans_le hk
  have htarget : (0 : ℝ) < (fourthRootD β : ℝ) * k := by positivity
  have hle : (fourthRootD β : ℝ) * k ≤ (claim617Q β k : ℝ) :=
    le_upperScale_cast _
  exact_mod_cast htarget.trans_le hle

/-- The optional matching reserved before Claim 6.15 occupies at most half
of the exceptional-family threshold.  This is the rounded form of Zhao's
`2 d^(1/4) ≤ eta / 2`; the Section-6 lower bound on `k` absorbs the one
ceiling unit in `claim617Q`. -/
theorem claim617Q_cast_le_eta_half {β : ℚ}
    (hβ0 : 0 < β) (hβ1 : β ≤ 1 / 4) {k : ℕ}
    (hk : section6K₀ β ≤ k) :
    (claim617Q β k : ℝ) ≤ (eta β : ℝ) * k / 2 := by
  have hkpos : 0 < k := (section6K₀_pos β).trans_le hk
  have hkRpos : (0 : ℝ) < k := by exact_mod_cast hkpos
  have hqUpper : (claim617Q β k : ℝ) <
      (fourthRootD β : ℝ) * k + 1 := by
    exact upperScale_cast_lt_add_one (by
      have : (0 : ℝ) < (fourthRootD β : ℝ) := by
        exact_mod_cast fourthRootD_pos hβ0
      positivity)
  have hfourth := fourthRootD_le_eta_div_1000 hβ0 hβ1
  have hfourthK := mul_le_mul_of_nonneg_right hfourth hkRpos.le
  have hetaK := eta_target_large hβ0 hβ1 hk
  linarith

theorem claim61C_le_reducedHalf {β : ℚ}
    (hβ0 : 0 < β) (hβ1 : β ≤ 1 / 4) {k : ℕ}
    (hk : section6K₀ β ≤ k) : claim61C β k ≤ k := by
  have hkpos : 0 < k := (section6K₀_pos β).trans_le hk
  have hkRpos : (0 : ℝ) < k := by exact_mod_cast hkpos
  have hs := sigma_le_one_div hβ0 hβ1
  have hcUpper : (claim61C β k : ℝ) <
      50 * (sigma β : ℝ) * k + 1 :=
    upperScale_cast_lt_add_one (by
      have : (0 : ℝ) < (sigma β : ℝ) := by exact_mod_cast sigma_pos hβ0
      positivity)
  have hkLarge : (200 : ℝ) ≤ k := by
    have hsK := mul_le_mul_of_nonneg_right
      (sigma_le_one_div hβ0 hβ1) hkRpos.le
    exact (sigma_target_large hβ0 hk).trans (hsK.trans (by nlinarith))
  have hreal : (claim61C β k : ℝ) < (k : ℝ) + 1 := by
    nlinarith
  have hnat : claim61C β k < k + 1 := by exact_mod_cast hreal
  omega

/-- The weaker master target `rho₁*k` is also large whenever the cubic
target `rho*k` is large. -/
theorem rhoOne_target_large {β : ℚ}
    (hβ0 : 0 < β) (hβ1 : β ≤ 1 / 4) {k : ℕ}
    (hk : section6K₀ β ≤ k) :
    (200 : ℝ) ≤ rhoOne β * k := by
  have hx0 : (0 : ℝ) < rhoOne β := rhoOne_pos hβ0
  have hx1 : rhoOne β ≤ 1 := rhoOne_le_one hβ1
  have hcube_le : (rho β : ℝ) ≤ rhoOne β := by
    rw [rho_cast_eq_rhoOne_cube]
    nlinarith [sq_nonneg (rhoOne β),
      mul_nonneg (sq_nonneg (rhoOne β)) (sub_nonneg.mpr hx1)]
  exact (main_target_large hβ0 hβ1 hk).trans
    (mul_le_mul_of_nonneg_right hcube_le (by positivity))

theorem rhoOne_sq_target_large {β : ℚ}
    (hβ0 : 0 < β) (hβ1 : β ≤ 1 / 4) {k : ℕ}
    (hk : section6K₀ β ≤ k) :
    (200 : ℝ) ≤ rhoOne β ^ 2 * k := by
  have hx0 : (0 : ℝ) < rhoOne β := rhoOne_pos hβ0
  have hx1 : rhoOne β ≤ 1 := rhoOne_le_one hβ1
  have hcube_le_sq : (rho β : ℝ) ≤ rhoOne β ^ 2 := by
    rw [rho_cast_eq_rhoOne_cube]
    nlinarith [sq_nonneg (rhoOne β),
      mul_nonneg (sq_nonneg (rhoOne β)) (sub_nonneg.mpr hx1)]
  exact (main_target_large hβ0 hβ1 hk).trans
    (mul_le_mul_of_nonneg_right hcube_le_sq (by positivity))

theorem claim618A_pos {β : ℚ}
    (hβ0 : 0 < β) (hβ1 : β ≤ 1 / 4) {k : ℕ}
    (hk : section6K₀ β ≤ k) : 0 < claim618A β k := by
  apply lowerScale_pos
  have := rhoOne_target_large hβ0 hβ1 hk
  nlinarith

theorem claim618B_pos {β : ℚ}
    (hβ0 : 0 < β) (hβ1 : β ≤ 1 / 4) {k : ℕ}
    (hk : section6K₀ β ≤ k) : 0 < claim618B β k := by
  apply lowerScale_pos
  have := rhoOne_target_large hβ0 hβ1 hk
  nlinarith

theorem claim618Z_pos {β : ℚ}
    (hβ0 : 0 < β) (hβ1 : β ≤ 1 / 4) {k : ℕ}
    (hk : section6K₀ β ≤ k) : 0 < claim618Z β k := by
  apply lowerScale_pos
  have := rhoOne_target_large hβ0 hβ1 hk
  nlinarith

theorem claim618U_pos {β : ℚ}
    (hβ0 : 0 < β) (hβ1 : β ≤ 1 / 4) {k : ℕ}
    (hk : section6K₀ β ≤ k) : 0 < claim618U β k := by
  apply lowerScale_pos
  have := rhoOne_sq_target_large hβ0 hβ1 hk
  nlinarith

/-- The floor choice for `a` is exactly the monotone scale hypothesis in
Claim 6.18. -/
theorem claim618A_cast_le {β : ℚ} (hβ : 0 < β) (k : ℕ) :
    (claim618A β k : ℝ) ≤ 8 * rhoOne β * k := by
  apply lowerScale_cast_le
  positivity [rhoOne_pos hβ]

/-- Claim 6.18's partner-count arithmetic is true by construction. -/
theorem claim618_partner_inequality (β : ℚ) (k : ℕ) :
    claim618U β k + claim617Q β k ≤ claim618T β k := by
  rfl

/-- Unit rounding errors are absorbed uniformly above `section6M₀`.  This is
the literal natural-number inequality required by Claim 6.17. -/
theorem claim617_rounding_inequality {β : ℚ}
    (hβ0 : 0 < β) (hβ1 : β ≤ 1 / 4) {k : ℕ}
    (hk : section6K₀ β ≤ k) :
    80 * mainScale β k * claim617H β k +
        4 * claim617Q β k * k < mainScale β k * k := by
  let r := mainScale β k
  let h := claim617H β k
  let q := claim617Q β k
  have hkpos : 0 < k := (section6K₀_pos β).trans_le hk
  have hkRpos : (0 : ℝ) < k := by exact_mod_cast hkpos
  have hrho0 : (0 : ℝ) < (rho β : ℝ) := by
    exact_mod_cast rho_pos hβ0
  have hrho1 : (rho β : ℝ) ≤ 1 := by exact_mod_cast rho_le_one hβ0 hβ1
  have hrUpper : (r : ℝ) ≤ (rho β : ℝ) * k := by
    exact lowerScale_cast_le (by positivity)
  have hrLower : (rho β : ℝ) * k - 1 < (r : ℝ) := by
    have := lt_lowerScale_cast_add_one ((rho β : ℝ) * k)
    dsimp only [r, mainScale] at this ⊢
    linarith
  have hhUpper : (h : ℝ) < (eta β : ℝ) * k + 1 := by
    exact upperScale_cast_lt_add_one
      (mul_nonneg (by exact_mod_cast (eta_pos hβ0).le) (by positivity))
  have hqUpper : (q : ℝ) < (fourthRootD β : ℝ) * k + 1 := by
    exact upperScale_cast_lt_add_one
      (mul_nonneg (by exact_mod_cast (fourthRootD_pos hβ0).le) (by positivity))
  have hrpos : (0 : ℝ) < r := by
    exact_mod_cast mainScale_pos hβ0 hβ1 hk
  have hlarge := main_target_large hβ0 hβ1 hk
  have hcoefficient := claim617_continuous_margin hβ0 hβ1
  have haddFactor : 80 * (rho β : ℝ) + 4 ≤ 84 := by nlinarith
  have hleft :
      (80 : ℝ) * r * h + 4 * q * k <
        80 * ((rho β : ℝ) * k) * ((eta β : ℝ) * k + 1) +
          4 * ((fourthRootD β : ℝ) * k + 1) * k := by
    have h1 : (80 : ℝ) * r * h <
        80 * ((rho β : ℝ) * k) * ((eta β : ℝ) * k + 1) := by
      have hrs : (r : ℝ) * h <
          ((rho β : ℝ) * k) * ((eta β : ℝ) * k + 1) := by
        calc
          (r : ℝ) * h < r * ((eta β : ℝ) * k + 1) :=
            mul_lt_mul_of_pos_left hhUpper hrpos
          _ ≤ ((rho β : ℝ) * k) * ((eta β : ℝ) * k + 1) :=
            mul_le_mul_of_nonneg_right hrUpper (by
              have heta0 : (0 : ℝ) ≤ (eta β : ℝ) := by
                exact_mod_cast (eta_pos hβ0).le
              positivity)
      nlinarith
    have h2 : (4 : ℝ) * q * k <
        4 * ((fourthRootD β : ℝ) * k + 1) * k := by
      exact mul_lt_mul_of_pos_right
        (mul_lt_mul_of_pos_left hqUpper (by norm_num)) hkRpos
    linarith
  have hcontinuous :
      80 * ((rho β : ℝ) * k) * ((eta β : ℝ) * k + 1) +
          4 * ((fourthRootD β : ℝ) * k + 1) * k <
        (rho β : ℝ) * (k : ℝ) ^ 2 - k := by
    have hmain :
        (80 * (rho β : ℝ) * (eta β : ℝ) +
            4 * (fourthRootD β : ℝ)) *
            (k : ℝ) ^ 2 <
          ((rho β : ℝ) / 10) * (k : ℝ) ^ 2 :=
      mul_lt_mul_of_pos_right hcoefficient (sq_pos_of_pos hkRpos)
    have habsorb : 85 * (k : ℝ) ≤
        (9 / 10 : ℝ) * (rho β : ℝ) * (k : ℝ) ^ 2 := by
      have hm := mul_le_mul_of_nonneg_right hlarge hkRpos.le
      nlinarith
    nlinarith
  have hright : (rho β : ℝ) * (k : ℝ) ^ 2 - k < (r : ℝ) * k := by
    have := mul_lt_mul_of_pos_right hrLower hkRpos
    nlinarith
  have hreal :
      (80 : ℝ) * r * h + 4 * q * k < (r : ℝ) * k :=
    hleft.trans (hcontinuous.trans hright)
  dsimp only [r, h, q] at hreal
  exact_mod_cast hreal

/-- The Claim-6.1 matching miss `2*c+1` and the Claim-6.17 optional
matching support `4*q` fit inside the Claim-6.16 reserve `rhoK`. -/
theorem claim616_reserve_inequality {β : ℚ}
    (hβ0 : 0 < β) (hβ1 : β ≤ 1 / 4)
    {k : ℕ} (hk : section6K₀ β ≤ k) :
    2 * claim61C β k + 1 + 4 * claim617Q β k ≤
      claim616Scale β k := by
  let r₀ := claim616Scale β k
  let q := claim617Q β k
  let c := claim61C β k
  have hkpos : 0 < k := (section6K₀_pos β).trans_le hk
  have hkRpos : (0 : ℝ) < k := by exact_mod_cast hkpos
  have hrLower : (rho β : ℝ) / 10 * k - 1 < (r₀ : ℝ) := by
    have := lt_lowerScale_cast_add_one (((rho β : ℝ) / 10) * k)
    dsimp only [r₀, claim616Scale] at this ⊢
    linarith
  have hqUpper : (q : ℝ) < (fourthRootD β : ℝ) * k + 1 := by
    exact upperScale_cast_lt_add_one (by
      have : (0 : ℝ) < (fourthRootD β : ℝ) := by
        exact_mod_cast fourthRootD_pos hβ0
      positivity)
  have hcUpper : (c : ℝ) < 50 * (sigma β : ℝ) * k + 1 := by
    exact upperScale_cast_lt_add_one (by
      have : (0 : ℝ) < (sigma β : ℝ) := by
        exact_mod_cast sigma_pos hβ0
      positivity)
  have hlarge := main_target_large hβ0 hβ1 hk
  have hfourth := fourthRootD_le_eta_div_1000 hβ0 hβ1
  have heta := eta_le_rho_div_1000 hβ0 hβ1
  have hsFourth := sigma_le_fourthRootD hβ0 hβ1
  have hfourthK := mul_le_mul_of_nonneg_right hfourth hkRpos.le
  have hetaK := mul_le_mul_of_nonneg_right heta hkRpos.le
  have hsFourthK := mul_le_mul_of_nonneg_right hsFourth hkRpos.le
  have hgap :
      100 * (sigma β : ℝ) * k +
          4 * (fourthRootD β : ℝ) * k + 7 <
        (rho β : ℝ) / 10 * k - 1 := by
    have hm := mul_le_mul_of_nonneg_right hlarge
      (show (0 : ℝ) ≤ (1 / 20 : ℝ) by norm_num)
    nlinarith
  have hreal : (2 : ℝ) * c + 1 + 4 * q < (r₀ : ℝ) := by
    nlinarith
  have hnat : 2 * c + 1 + 4 * q < r₀ := by exact_mod_cast hreal
  dsimp only [r₀, q, c] at hnat ⊢
  omega

/-- The literal source-filter deletion inequality for the explicit
Lemma-6.11 target.  The two scale hypotheses are the exact consequences
needed from an equal-cluster degree-form witness: one cluster has size at
most `3*sigma*n`, and the padded half accounts for at most `n+N` ordinary
vertices.  All exceptional-family, optional-matching, and rounding charges
are already present in the displayed left-hand side. -/
theorem lemma611_deletion_numeric
    {β : ℚ} (hβ0 : 0 < β) (hβ1 : β ≤ 1 / 4)
    {k : ℕ} {N n : ℝ}
    (hN : 0 < N) (hn : 0 ≤ n)
    (hcluster : N ≤ 3 * (sigma β : ℝ) * n)
    (hcover : (k : ℝ) * N ≤ n + N) :
    lemma611TargetA β n +
        2 * N * (2 * (auxiliaryScale β k + 2) +
          claim617Q β k + 1) +
        3 * (eta β : ℝ) * N * k <
      (1 - 10 * Real.sqrt (lemma611D β)) * n + 4 * N := by
  let h := auxiliaryScale β k
  let q := claim617Q β k
  have hs0 : (0 : ℝ) < (sigma β : ℝ) := by
    exact_mod_cast sigma_pos hβ0
  have heta0 : (0 : ℝ) < (eta β : ℝ) := by
    exact_mod_cast eta_pos hβ0
  have hf0 : (0 : ℝ) < (fourthRootD β : ℝ) := by
    exact_mod_cast fourthRootD_pos hβ0
  have heta1 : (eta β : ℝ) ≤ 1 := by
    have heta := eta_le_rho_div_1000 hβ0 hβ1
    have hr : (rho β : ℝ) ≤ 1 := by
      exact_mod_cast rho_le_one hβ0 hβ1
    nlinarith
  have hf1 : (fourthRootD β : ℝ) ≤ 1 := by
    have hf := fourthRootD_le_eta_div_1000 hβ0 hβ1
    nlinarith
  have hfEta := fourthRootD_le_eta_div_1000 hβ0 hβ1
  have hsFourth := sigma_le_fourthRootD hβ0 hβ1
  have hnpos : 0 < n := by
    by_contra hn0
    have : n = 0 := le_antisymm (not_lt.mp hn0) hn
    subst n
    norm_num at hcluster
    linarith
  have hhUpper : (h : ℝ) < (eta β : ℝ) * k + 1 := by
    exact upperScale_cast_lt_add_one (by positivity)
  have hqUpper : (q : ℝ) < (fourthRootD β : ℝ) * k + 1 := by
    exact upperScale_cast_lt_add_one (by positivity)
  have hbracket :
      ((2 * (h + 2) + q + 1 : ℕ) : ℝ) <
        2 * (eta β : ℝ) * k + (fourthRootD β : ℝ) * k + 8 := by
    push_cast
    nlinarith
  have hfirst := mul_lt_mul_of_pos_left hbracket
    (show (0 : ℝ) < 2 * N by positivity)
  have hdelete :
      2 * N * ((2 * (h + 2) + q + 1 : ℕ) : ℝ) +
          3 * (eta β : ℝ) * N * k <
        (7 * (eta β : ℝ) + 2 * (fourthRootD β : ℝ)) *
            ((k : ℝ) * N) + 16 * N := by
    nlinarith
  have hcoverScaled := mul_le_mul_of_nonneg_left hcover
    (show (0 : ℝ) ≤ 7 * (eta β : ℝ) +
      2 * (fourthRootD β : ℝ) by positivity)
  have hcoefBound :
      7 * (eta β : ℝ) + 2 * (fourthRootD β : ℝ) + 12 ≤ 21 := by
    nlinarith
  have hNabsorb :
      (7 * (eta β : ℝ) + 2 * (fourthRootD β : ℝ) + 12) * N ≤
        63 * (sigma β : ℝ) * n := by
    have hleft := mul_le_mul_of_nonneg_right hcoefBound hN.le
    have hright := mul_le_mul_of_nonneg_left hcluster
      (show (0 : ℝ) ≤ 21 by norm_num)
    nlinarith
  have hsmallCoefficient :
      73 * (sigma β : ℝ) + 2 * (fourthRootD β : ℝ) <
        (eta β : ℝ) := by
    nlinarith
  have hdeleteFinal :
      2 * N * ((2 * (h + 2) + q + 1 : ℕ) : ℝ) +
          3 * (eta β : ℝ) * N * k <
        (8 * (eta β : ℝ) - 10 * (sigma β : ℝ)) * n + 4 * N := by
    nlinarith
  dsimp only [h, q] at hdeleteFinal
  rw [sqrt_lemma611D hβ0]
  simp only [lemma611TargetA, lemma611EpsilonOne, lemma611DSqrt]
  nlinarith

/-- The rounded choices `a,b,q,c` satisfy Claim 6.18's local budget.  Here
`miss = 2*c+1` is the literal output of quantitative Claim 6.1. -/
theorem claim618_local_inequality {β : ℚ}
    (hβ0 : 0 < β) (hβ1 : β ≤ 1 / 4) {k : ℕ}
    (hk : section6K₀ β ≤ k) :
    2 * (claim618B β k + claim617Q β k + 1) +
        (2 * claim61C β k + 1) ≤ claim618A β k := by
  let x := rhoOne β
  let a := claim618A β k
  let b := claim618B β k
  let q := claim617Q β k
  let c := claim61C β k
  have hx0 : (0 : ℝ) < x := rhoOne_pos hβ0
  have hkpos : 0 < k := (section6K₀_pos β).trans_le hk
  have hkRpos : (0 : ℝ) < k := by exact_mod_cast hkpos
  have hxk : (200 : ℝ) ≤ x * k := rhoOne_target_large hβ0 hβ1 hk
  have haLower : 8 * x * k - 1 < (a : ℝ) := by
    have := lt_lowerScale_cast_add_one (8 * x * k)
    dsimp only [a, claim618A, x] at this ⊢
    linarith
  have hbUpper : (b : ℝ) ≤ (7 / 2 : ℝ) * x * k := by
    exact lowerScale_cast_le (by positivity)
  have hqUpper : (q : ℝ) < (fourthRootD β : ℝ) * k + 1 := by
    exact upperScale_cast_lt_add_one (by
      have : (0 : ℝ) < (fourthRootD β : ℝ) := by
        exact_mod_cast fourthRootD_pos hβ0
      positivity)
  have hcUpper : (c : ℝ) < 50 * (sigma β : ℝ) * k + 1 := by
    exact upperScale_cast_lt_add_one (by
      have : (0 : ℝ) < (sigma β : ℝ) := by exact_mod_cast sigma_pos hβ0
      positivity)
  have hsx : (sigma β : ℝ) ≤ x / 1000 := by
    have hs2 := sigma_le_rhoOne_sq_div hβ0 hβ1
    have hx1 : x ≤ 1 := rhoOne_le_one hβ1
    have hx2le : x ^ 2 ≤ x := by nlinarith [sq_nonneg x]
    linarith
  have hfx : (fourthRootD β : ℝ) ≤ x / 1000 := by
    have hfEta := fourthRootD_le_eta_div_1000 hβ0 hβ1
    have hetaRho := eta_le_rho_div_1000 hβ0 hβ1
    have hrx : (rho β : ℝ) ≤ x := by
      rw [rho_cast_eq_rhoOne_cube]
      have hx1 : x ≤ 1 := rhoOne_le_one hβ1
      nlinarith [sq_nonneg x,
        mul_nonneg (sq_nonneg x) (sub_nonneg.mpr hx1)]
    nlinarith
  have hgap :
      7 * x * k + 2 * ((fourthRootD β : ℝ) * k + 1) +
          2 * (50 * (sigma β : ℝ) * k + 1) + 3 <
        8 * x * k - 1 := by
    have hsigmul : (sigma β : ℝ) * k ≤ x * k / 1000 :=
      (mul_le_mul_of_nonneg_right hsx hkRpos.le).trans_eq (by ring)
    have hfourthmul : (fourthRootD β : ℝ) * k ≤ x * k / 1000 :=
      (mul_le_mul_of_nonneg_right hfx hkRpos.le).trans_eq (by ring)
    nlinarith
  have hreal : (2 : ℝ) * (b + q + 1) + (2 * c + 1) < a := by
    push_cast
    nlinarith
  have hnat : 2 * (b + q + 1) + (2 * c + 1) < a := by
    exact_mod_cast hreal
  dsimp only [a, b, q, c] at hnat ⊢
  omega

/-- The chosen `z,u` have product at least `16*rho*k^2`, including both
flooring losses.  This discharges Claim 6.18's last arithmetic premise. -/
theorem claim618_final_product {β : ℚ}
    (hβ0 : 0 < β) (hβ1 : β ≤ 1 / 4) {k : ℕ}
    (hk : section6K₀ β ≤ k) :
    16 * (rho β : ℝ) * (k : ℝ) ^ 2 ≤
      ((claim618Z β k * claim618U β k : ℕ) : ℝ) := by
  let x := rhoOne β
  let z := claim618Z β k
  let u := claim618U β k
  have hx0 : (0 : ℝ) < x := rhoOne_pos hβ0
  have hkpos : 0 < k := (section6K₀_pos β).trans_le hk
  have hkRpos : (0 : ℝ) < k := by exact_mod_cast hkpos
  have hxk : (200 : ℝ) ≤ x * k := rhoOne_target_large hβ0 hβ1 hk
  have hx2k : (200 : ℝ) ≤ x ^ 2 * k :=
    rhoOne_sq_target_large hβ0 hβ1 hk
  have hzLower : (7 / 4 : ℝ) * x * k - 1 < (z : ℝ) := by
    have := lt_lowerScale_cast_add_one ((7 / 4 : ℝ) * x * k)
    dsimp only [z, claim618Z, x] at this ⊢
    linarith
  have huLower : 10 * x ^ 2 * k - 1 < (u : ℝ) := by
    have := lt_lowerScale_cast_add_one (10 * x ^ 2 * k)
    dsimp only [u, claim618U, x] at this ⊢
    linarith
  have hz0 : (0 : ℝ) < z := by exact_mod_cast claim618Z_pos hβ0 hβ1 hk
  have hu0 : (0 : ℝ) < u := by exact_mod_cast claim618U_pos hβ0 hβ1 hk
  have hlowerZ : (0 : ℝ) < (7 / 4 : ℝ) * x * k - 1 := by nlinarith
  have hproductLower :
      ((7 / 4 : ℝ) * x * k - 1) * (10 * x ^ 2 * k - 1) <
        (z : ℝ) * u := by
    calc
      ((7 / 4 : ℝ) * x * k - 1) * (10 * x ^ 2 * k - 1) <
          ((7 / 4 : ℝ) * x * k - 1) * u :=
        mul_lt_mul_of_pos_left huLower hlowerZ
      _ < (z : ℝ) * u := mul_lt_mul_of_pos_right hzLower hu0
  have hmainProduct : 200 * (x * k) ≤ x ^ 3 * (k : ℝ) ^ 2 := by
    have hmul := mul_le_mul_of_nonneg_right hx2k
      (show 0 ≤ x * k by positivity)
    nlinarith
  have hcontinuous :
      16 * x ^ 3 * (k : ℝ) ^ 2 <
        ((7 / 4 : ℝ) * x * k - 1) * (10 * x ^ 2 * k - 1) := by
    have hx2kle : x ^ 2 * k ≤ x * k := by
      have hx1 : x ≤ 1 := rhoOne_le_one hβ1
      have hx2 : x ^ 2 ≤ x := by nlinarith [sq_nonneg x]
      exact mul_le_mul_of_nonneg_right hx2 hkRpos.le
    nlinarith
  have hrho : (rho β : ℝ) = x ^ 3 := by
    dsimp only [x]
    exact rho_cast_eq_rhoOne_cube β
  rw [hrho]
  push_cast
  exact (hcontinuous.trans hproductLower).le

/-- The remaining double-count premise of Claim 6.18 follows from the actual
Lemma-6.11 estimate `|V2| ≤ k+8h`; no equality of rounded scales is used. -/
theorem claim618_double_count_inequality {β : ℚ}
    (hβ0 : 0 < β) (hβ1 : β ≤ 1 / 4) {k v : ℕ}
    (hk : section6K₀ β ≤ k)
    (hv : v ≤ k + 8 * claim617H β k) :
    claim618Z β k * claim618A β k + v * claim618T β k ≤
      claim618A β k * claim618B β k := by
  let x := rhoOne β
  let a := claim618A β k
  let b := claim618B β k
  let z := claim618Z β k
  let u := claim618U β k
  let h := claim617H β k
  let q := claim617Q β k
  let t := u + q
  have hx0 : (0 : ℝ) < x := rhoOne_pos hβ0
  have hx1 : x ≤ 1 := rhoOne_le_one hβ1
  have hkpos : 0 < k := (section6K₀_pos β).trans_le hk
  have hkRpos : (0 : ℝ) < k := by exact_mod_cast hkpos
  have hxk : (200 : ℝ) ≤ x * k := rhoOne_target_large hβ0 hβ1 hk
  have hhUpper : (h : ℝ) < (eta β : ℝ) * k + 1 := by
    exact upperScale_cast_lt_add_one (by
      have : (0 : ℝ) < (eta β : ℝ) := by exact_mod_cast eta_pos hβ0
      positivity)
  have hqUpper : (q : ℝ) < (fourthRootD β : ℝ) * k + 1 := by
    exact upperScale_cast_lt_add_one (by
      have : (0 : ℝ) < (fourthRootD β : ℝ) := by
        exact_mod_cast fourthRootD_pos hβ0
      positivity)
  have hetaK := eta_target_large hβ0 hβ1 hk
  have hfourthK := fourthRootD_target_large hβ0 hβ1 hk
  have hetaOne : (eta β : ℝ) ≤ 1 / 1000 := by
    have heta := eta_le_rho_div_1000 hβ0 hβ1
    have hr : (rho β : ℝ) ≤ 1 := by
      exact_mod_cast rho_le_one hβ0 hβ1
    nlinarith
  have hhScaled : (h : ℝ) < (201 / 200 : ℝ) * (eta β : ℝ) * k := by
    nlinarith
  have hqScaled : (q : ℝ) <
      (201 / 200 : ℝ) * (fourthRootD β : ℝ) * k := by
    nlinarith
  have hfourthXsq : (fourthRootD β : ℝ) ≤ x ^ 2 / 1000 := by
    have hfEta := fourthRootD_le_eta_div_1000 hβ0 hβ1
    have hetaRho := eta_le_rho_div_1000 hβ0 hβ1
    have hrx3 : (rho β : ℝ) = x ^ 3 := by
      dsimp only [x]
      exact rho_cast_eq_rhoOne_cube β
    rw [hrx3] at hetaRho
    nlinarith [sq_nonneg x,
      mul_nonneg (sq_nonneg x) (sub_nonneg.mpr hx1)]
  have haUpper : (a : ℝ) ≤ 8 * x * k := lowerScale_cast_le (by positivity)
  have hbLower : (7 / 2 : ℝ) * x * k - 1 < (b : ℝ) := by
    have := lt_lowerScale_cast_add_one ((7 / 2 : ℝ) * x * k)
    dsimp only [b, claim618B, x] at this ⊢
    linarith
  have haLower : 8 * x * k - 1 < (a : ℝ) := by
    have := lt_lowerScale_cast_add_one (8 * x * k)
    dsimp only [a, claim618A, x] at this ⊢
    linarith
  have hzUpper : (z : ℝ) ≤ (7 / 4 : ℝ) * x * k :=
    lowerScale_cast_le (by positivity)
  have huUpper : (u : ℝ) ≤ 10 * x ^ 2 * k :=
    lowerScale_cast_le (by positivity)
  have hvRealNat : (v : ℝ) ≤ k + 8 * h := by exact_mod_cast hv
  have hvUpper : (v : ℝ) < (21 / 20 : ℝ) * k := by
    have hetaKle : (eta β : ℝ) * k ≤ (1 / 1000 : ℝ) * k :=
      mul_le_mul_of_nonneg_right hetaOne hkRpos.le
    nlinarith
  have htUpper : (t : ℝ) < (101 / 10 : ℝ) * x ^ 2 * k := by
    have hqK : (fourthRootD β : ℝ) * k ≤ (x ^ 2 / 1000) * k :=
      mul_le_mul_of_nonneg_right hfourthXsq hkRpos.le
    dsimp only [t]
    push_cast
    nlinarith
  have ht0 : (0 : ℝ) < t := by
    have : 0 < u := claim618U_pos hβ0 hβ1 hk
    positivity
  have hza : (z : ℝ) * a ≤ 14 * x ^ 2 * (k : ℝ) ^ 2 := by
    have hm := mul_le_mul hzUpper haUpper (by positivity) (by positivity)
    nlinarith
  have hvt : (v : ℝ) * t <
      (2121 / 200 : ℝ) * x ^ 2 * (k : ℝ) ^ 2 := by
    calc
      (v : ℝ) * t < ((21 / 20 : ℝ) * k) * t :=
        mul_lt_mul_of_pos_right hvUpper ht0
      _ < ((21 / 20 : ℝ) * k) * ((101 / 10 : ℝ) * x ^ 2 * k) :=
        mul_lt_mul_of_pos_left htUpper (by positivity)
      _ = (2121 / 200 : ℝ) * x ^ 2 * (k : ℝ) ^ 2 := by ring
  have habLower :
      (8 * x * k - 1) * ((7 / 2 : ℝ) * x * k - 1) <
        (a : ℝ) * b := by
    have hleft0 : (0 : ℝ) < 8 * x * k - 1 := by nlinarith
    have hb0 : (0 : ℝ) < b := by exact_mod_cast claim618B_pos hβ0 hβ1 hk
    calc
      (8 * x * k - 1) * ((7 / 2 : ℝ) * x * k - 1) <
          (8 * x * k - 1) * b := mul_lt_mul_of_pos_left hbLower hleft0
      _ < (a : ℝ) * b := mul_lt_mul_of_pos_right haLower hb0
  have hlinearAbsorb :
      (23 / 2 : ℝ) * (x * k) ≤
        (23 / 400 : ℝ) * (x ^ 2 * (k : ℝ) ^ 2) := by
    have hmul := mul_le_mul_of_nonneg_left hxk
      (show (0 : ℝ) ≤ (23 / 400) * (x * k) by positivity)
    nlinarith
  have hcontinuous :
      14 * x ^ 2 * (k : ℝ) ^ 2 +
          (2121 / 200 : ℝ) * x ^ 2 * (k : ℝ) ^ 2 <
        (8 * x * k - 1) * ((7 / 2 : ℝ) * x * k - 1) := by
    nlinarith
  have hreal : (z : ℝ) * a + v * t < (a : ℝ) * b := by
    exact (add_lt_add_of_le_of_lt hza hvt).trans
      (hcontinuous.trans habLower)
  have hnat : z * a + v * t < a * b := by exact_mod_cast hreal
  dsimp only [a, b, z, u, h, q, t, claim617H, claim618T] at hv hnat ⊢
  omega

/-- `section6N₀` really dominates the degree-form threshold. -/
theorem degreeFormThreshold_le_section6N₀ (β : ℚ) :
    degreeFormThreshold (regularityEpsilon β) (section6M₀ β) + 2 ≤
      section6N₀ β := by
  simp only [section6N₀]
  exact le_max_left _ _

theorem degreeFormThreshold_le_ramseyHost
    {β : ℚ} {n : ℕ} (hn : section6N₀ β ≤ n) :
    degreeFormThreshold (regularityEpsilon β) (section6M₀ β) ≤
      2 * n - 2 := by
  have hbase := (degreeFormThreshold_le_section6N₀ β).trans hn
  omega

theorem exists_explicit_degreeFormWitness
    {β : ℚ} (hβ : 0 < β) {n : ℕ}
    (G : SimpleGraph (Fin (2 * n - 2))) [DecidableRel G.Adj]
    (hN : section6N₀ β ≤ 2 * n - 2) :
    Nonempty (DegreeFormWitness G (regularityEpsilon β) (reducedDensity β)
      (section6M₀ β)
      (degreeFormBound (regularityEpsilon β) (section6M₀ β))) := by
  apply exists_degreeFormWitness (regularityEpsilon_pos hβ)
    (reducedDensity_pos hβ)
  have hthreshold := degreeFormThreshold_le_section6N₀ β
  exact (show degreeFormThreshold (regularityEpsilon β) (section6M₀ β) ≤
      degreeFormThreshold (regularityEpsilon β) (section6M₀ β) + 2 by omega).trans
    (hthreshold.trans hN)

/-- The second component of the host threshold absorbs every error bounded
by the fixed regularity bound. -/
theorem bounded_reduced_error_absorbed
    {β : ℚ} (hβ : 0 < β) {n : ℕ} (hn : section6N₀ β ≤ n) :
    (1000000 : ℝ) *
        (degreeFormBound (regularityEpsilon β) (section6M₀ β) + 1) ≤
      (sigma β : ℝ) * n := by
  let M := degreeFormBound (regularityEpsilon β) (section6M₀ β)
  let target := (1000000 : ℝ) * (M + 1) / (sigma β : ℝ)
  have hright : upperScale target + 2 ≤ section6N₀ β := by
    simp only [section6N₀, M, target]
    exact le_max_right _ _
  have hceilNat : upperScale target ≤ n := by
    exact (show upperScale target ≤ upperScale target + 2 by omega).trans
      (hright.trans hn)
  have hceilReal : (upperScale target : ℝ) ≤ n := by exact_mod_cast hceilNat
  have htarget : target ≤ (n : ℝ) := (le_upperScale_cast target).trans hceilReal
  have hσR : (0 : ℝ) < sigma β := by exact_mod_cast sigma_pos hβ
  have := (div_le_iff₀ hσR).mp htarget
  dsimp only [target, M] at this ⊢
  simpa only [mul_comm, mul_left_comm, mul_assoc] using this

private theorem degreeForm_common_bounds
    {β : ℚ} (hβ0 : 0 < β) (hβ1 : β ≤ 1 / 4)
    {N : ℕ} {G : SimpleGraph (Fin N)} [DecidableRel G.Adj]
    (W : DegreeFormWitness G (regularityEpsilon β) (reducedDensity β)
      (section6M₀ β)
      (degreeFormBound (regularityEpsilon β) (section6M₀ β)))
    (hN : section6N₀ β ≤ N) :
    let K := W.ordinaryParts
    let A := ((N / K + 1 : ℕ) : ℝ)
    let cf := cleanupFraction (regularityEpsilon β)
    let f := 2 * cf + (reducedDensity β : ℝ) +
      2 * ordinaryError (regularityEpsilon β)
    (K : ℝ) ≤ (N : ℝ) / 5 ∧
      (K : ℝ) * A ≤ (6 / 5 : ℝ) * N ∧
      (1000000 : ℝ) * K ≤ (sigma β : ℝ) * N ∧
      (1000000 : ℝ) ≤ (sigma β : ℝ) * N ∧
      cf ≤ (sigma β : ℝ) / 64000 ∧
      0 ≤ cf ∧ 0 ≤ f ∧ f ≤ 6 * (sigma β : ℝ) := by
  let K := W.ordinaryParts
  let A := ((N / K + 1 : ℕ) : ℝ)
  let cf := cleanupFraction (regularityEpsilon β)
  let f := 2 * cf + (reducedDensity β : ℝ) +
    2 * ordinaryError (regularityEpsilon β)
  have hσ0 : (0 : ℝ) < (sigma β : ℝ) := by exact_mod_cast sigma_pos hβ0
  have hε0 : 0 < regularityEpsilon β := regularityEpsilon_pos hβ0
  have hd0 : 0 < reducedDensity β := reducedDensity_pos hβ0
  have hKposNat : 0 < K := W.ordinaryParts_pos
  have hfiveNat : 5 * K ≤ N := W.five_ordinaryParts_le_host
  have hfive : (5 : ℝ) * K ≤ N := by exact_mod_cast hfiveNat
  have hKN : (K : ℝ) ≤ (N : ℝ) / 5 := by nlinarith
  have hKA : (K : ℝ) * A ≤ (N : ℝ) + K := by
    have hdiv : (N / K) * K ≤ N := Nat.div_mul_le_self N K
    have hdivR : ((N / K : ℕ) : ℝ) * K ≤ N := by exact_mod_cast hdiv
    dsimp only [A]
    push_cast
    nlinarith
  have hKAsix : (K : ℝ) * A ≤ (6 / 5 : ℝ) * N := by
    nlinarith
  have hfixed := bounded_reduced_error_absorbed hβ0 hN
  have hKupper : K ≤
      degreeFormBound (regularityEpsilon β) (section6M₀ β) := W.upper_parts
  have hKfixed : (1000000 : ℝ) * K ≤ (sigma β : ℝ) * N := by
    have hKupperR : (K : ℝ) ≤
        degreeFormBound (regularityEpsilon β) (section6M₀ β) + 1 := by
      exact_mod_cast (hKupper.trans (Nat.le_succ _))
    have := mul_le_mul_of_nonneg_left hKupperR
      (by norm_num : (0 : ℝ) ≤ 1000000)
    exact this.trans hfixed
  have honeFixed : (1000000 : ℝ) ≤ (sigma β : ℝ) * N := by
    have hOne : (1 : ℝ) ≤
        degreeFormBound (regularityEpsilon β) (section6M₀ β) + 1 := by
      exact_mod_cast (show 1 ≤
        degreeFormBound (regularityEpsilon β) (section6M₀ β) + 1 by omega)
    have hscaled := mul_le_mul_of_nonneg_left hOne
      (show (0 : ℝ) ≤ 1000000 by norm_num)
    simpa only [mul_one] using hscaled.trans hfixed
  have hgammaSigma : (embeddingGamma β : ℝ) ≤ (sigma β : ℝ) := by
    have hs1 := sigma_le_one_div hβ0 hβ1
    rw [embeddingGamma]
    push_cast
    nlinarith [sq_nonneg (sigma β : ℝ)]
  have hεeq := regularityEpsilon_cast_eq β
  have hdensityOne : (reducedDensity β : ℝ) ≤ 1 := by
    have hs1 := sigma_le_one_div hβ0 hβ1
    rw [reducedDensity]
    push_cast
    nlinarith
  have hgamma0 : (0 : ℝ) ≤ (embeddingGamma β : ℝ) := by
    exact_mod_cast (embeddingGamma_pos hβ0).le
  have hproduct :
      (reducedDensity β : ℝ) * (embeddingGamma β : ℝ) ≤
        (embeddingGamma β : ℝ) := by
    nlinarith [mul_nonneg hgamma0 (sub_nonneg.mpr hdensityOne)]
  have hεσ : (regularityEpsilon β : ℝ) ≤
      (sigma β : ℝ) / 1000 := by
    rw [hεeq]
    nlinarith
  have hcf : cf ≤ (sigma β : ℝ) / 64000 := by
    have hraw := cleanupFraction_le_eps_div
      (ε := regularityEpsilon β)
    have hεdiv := mul_le_mul_of_nonneg_right hεσ
      (show (0 : ℝ) ≤ 1 / 64 by norm_num)
    dsimp only [cf] at hraw ⊢
    calc
      cleanupFraction (regularityEpsilon β) ≤
          (regularityEpsilon β : ℝ) / 64 := hraw
      _ ≤ (sigma β : ℝ) / 64000 := by
        calc
          (regularityEpsilon β : ℝ) / 64 =
              (regularityEpsilon β : ℝ) * (1 / 64 : ℝ) := by ring
          _ ≤ ((sigma β : ℝ) / 1000) * (1 / 64 : ℝ) := hεdiv
          _ = (sigma β : ℝ) / 64000 := by ring
  have hcf0 : (0 : ℝ) ≤ cf := (cleanupFraction_pos hε0).le
  have hord : 2 * ordinaryError (regularityEpsilon β) ≤
      (sigma β : ℝ) / 1000 := by
    have hraw := twice_ordinaryError_le_eps hε0
    exact hraw.trans hεσ
  have hf0 : (0 : ℝ) ≤ f := by
    dsimp only [f]
    have hdR : (0 : ℝ) ≤ (reducedDensity β : ℝ) := by
      exact_mod_cast hd0.le
    have hcfNonneg : (0 : ℝ) ≤ cf := hcf0
    have hordNonneg : (0 : ℝ) ≤ ordinaryError (regularityEpsilon β) :=
      (ordinaryError_pos hε0).le
    linarith
  have hf : f ≤ 6 * (sigma β : ℝ) := by
    dsimp only [f, reducedDensity]
    push_cast
    nlinarith
  exact ⟨hKN, hKAsix, hKfixed, honeFixed, hcf, hcf0, hf0, hf⟩

private theorem degreeForm_exceptional_small
    {β : ℚ} (hβ0 : 0 < β) (hβ1 : β ≤ 1 / 4)
    {N : ℕ} {G : SimpleGraph (Fin N)} [DecidableRel G.Adj]
    (W : DegreeFormWitness G (regularityEpsilon β) (reducedDensity β)
      (section6M₀ β)
      (degreeFormBound (regularityEpsilon β) (section6M₀ β)))
    (hN : section6N₀ β ≤ N) :
    (W.exceptional.card : ℝ) < (sigma β : ℝ) * N := by
  let K := W.ordinaryParts
  let A := ((N / K + 1 : ℕ) : ℝ)
  let cf := cleanupFraction (regularityEpsilon β)
  let f := 2 * cf + (reducedDensity β : ℝ) +
    2 * ordinaryError (regularityEpsilon β)
  have H := degreeForm_common_bounds hβ0 hβ1 W hN
  dsimp only at H
  obtain ⟨hKN, hKAsix, hKfixed, honeFixed, hcf, hcf0, hf0, hf⟩ := H
  have hcleanupKA : 2 * cf * ((K : ℝ) * A) ≤
      (12 / 320000 : ℝ) * (sigma β : ℝ) * N := by
    have hsDiv0 : (0 : ℝ) ≤ (sigma β : ℝ) / 64000 := by
      positivity [sigma_pos hβ0]
    have hKA0 : (0 : ℝ) ≤ (K : ℝ) * A := by positivity
    have h1 := mul_le_mul hcf hKAsix hKA0 hsDiv0
    nlinarith
  have hEraw := exceptional_card_lt_cleanup_bound W
  have hEform : (W.exceptional.card : ℝ) <
      2 * cf * ((K : ℝ) * A) + 2 * K := by
    change (W.exceptional.card : ℝ) <
      (K : ℝ) * (cf * A + 2) + cf * K * A at hEraw
    convert hEraw using 1 <;> ring
  have hKsmall : (2 : ℝ) * K ≤
      (2 / 1000000 : ℝ) * ((sigma β : ℝ) * N) := by
    have h := mul_le_mul_of_nonneg_left hKfixed
      (show (0 : ℝ) ≤ 2 / 1000000 by norm_num)
    nlinarith
  calc
    (W.exceptional.card : ℝ) <
        2 * cf * ((K : ℝ) * A) + 2 * K := hEform
    _ ≤ (12 / 320000 : ℝ) * (sigma β : ℝ) * N +
        (2 / 1000000 : ℝ) * ((sigma β : ℝ) * N) :=
      add_le_add hcleanupKA hKsmall
    _ < (sigma β : ℝ) * N := by
      have hpositive : (0 : ℝ) < (sigma β : ℝ) * N := by
        linarith [honeFixed]
      nlinarith

private theorem degreeForm_loss_small
    {β : ℚ} (hβ0 : 0 < β) (hβ1 : β ≤ 1 / 4)
    {N : ℕ} {G : SimpleGraph (Fin N)} [DecidableRel G.Adj]
    (W : DegreeFormWitness G (regularityEpsilon β) (reducedDensity β)
      (section6M₀ β)
      (degreeFormBound (regularityEpsilon β) (section6M₀ β)))
    (hN : section6N₀ β ≤ N) :
    (W.loss : ℝ) < 9 * (sigma β : ℝ) * N := by
  let K := W.ordinaryParts
  let A := ((N / K + 1 : ℕ) : ℝ)
  let cf := cleanupFraction (regularityEpsilon β)
  let f := 2 * cf + (reducedDensity β : ℝ) +
    2 * ordinaryError (regularityEpsilon β)
  have H := degreeForm_common_bounds hβ0 hβ1 W hN
  dsimp only at H
  obtain ⟨hKN, hKAsix, hKfixed, honeFixed, hcf, hcf0, hf0, hf⟩ := H
  have hε0 : 0 < regularityEpsilon β := regularityEpsilon_pos hβ0
  have hd0 : 0 < reducedDensity β := reducedDensity_pos hβ0
  have hKscaleNat : 4 * section6K₀ β ≤ K := by
    have h := W.twice_requested_le_ordinary
    simp only [section6M₀] at h
    omega
  have hKscale : (4 : ℝ) * section6K₀ β ≤ K := by
    exact_mod_cast hKscaleNat
  have hσK0 := sigma_target_large hβ0
    (k := section6K₀ β) le_rfl
  have hσK : (800 : ℝ) ≤ (sigma β : ℝ) * K := by
    have hm := mul_le_mul_of_nonneg_left hKscale
      (show (0 : ℝ) ≤ (sigma β : ℝ) by
        exact_mod_cast (sigma_pos hβ0).le)
    nlinarith
  have hdivMulNat : (N / K) * K ≤ N := Nat.div_mul_le_self N K
  have hdivMul : ((N / K : ℕ) : ℝ) * K ≤ N := by
    exact_mod_cast hdivMulNat
  have haverage : ((N / K : ℕ) : ℝ) ≤
      (sigma β : ℝ) * N / 800 := by
    have hleft := mul_le_mul_of_nonneg_right hσK
      (show (0 : ℝ) ≤ ((N / K : ℕ) : ℝ) by positivity)
    have hright := mul_le_mul_of_nonneg_left hdivMul
      (show (0 : ℝ) ≤ (sigma β : ℝ) by
        exact_mod_cast (sigma_pos hβ0).le)
    apply (le_div_iff₀ (by norm_num : (0 : ℝ) < 800)).2
    calc
      ((N / K : ℕ) : ℝ) * 800 =
          800 * ((N / K : ℕ) : ℝ) := by ring
      _ ≤ ((sigma β : ℝ) * K) * ((N / K : ℕ) : ℝ) := hleft
      _ = (sigma β : ℝ) * (((N / K : ℕ) : ℝ) * K) := by ring
      _ ≤ (sigma β : ℝ) * N := hright
  have haverageSigma : ((N / K : ℕ) : ℝ) ≤
      (5 / 4 : ℝ) * (sigma β : ℝ) * N := by
    exact haverage.trans (by nlinarith)
  have hfNK : f * ((N : ℝ) + K) ≤
      (36 / 5 : ℝ) * (sigma β : ℝ) * N := by
    have hNK : (N : ℝ) + K ≤ (6 / 5 : ℝ) * N := by nlinarith
    have hSixSigma : (0 : ℝ) ≤ 6 * (sigma β : ℝ) := by
      positivity [sigma_pos hβ0]
    have hNK0 : (0 : ℝ) ≤ (N : ℝ) + K := by positivity
    calc
      f * ((N : ℝ) + K) ≤
          (6 * (sigma β : ℝ)) * ((6 / 5 : ℝ) * N) :=
        mul_le_mul hf hNK hNK0 hSixSigma
      _ = (36 / 5 : ℝ) * (sigma β : ℝ) * N := by ring
  have hLossRaw := loss_lt_average_add_cleanup W hε0 hd0
  change (W.loss : ℝ) <
    ((N / K : ℕ) : ℝ) + f * ((N : ℝ) + K) + 1 at hLossRaw
  have hone : (1 : ℝ) ≤ (sigma β : ℝ) * N / 1000000 := by
    apply (le_div_iff₀ (by norm_num : (0 : ℝ) < 1000000)).2
    simpa only [one_mul] using honeFixed
  calc
    (W.loss : ℝ) <
        ((N / K : ℕ) : ℝ) + f * ((N : ℝ) + K) + 1 := hLossRaw
    _ ≤ (5 / 4 : ℝ) * (sigma β : ℝ) * N +
        (36 / 5 : ℝ) * (sigma β : ℝ) * N +
        (sigma β : ℝ) * N / 1000000 :=
      add_le_add (add_le_add haverageSigma hfNK) hone
    _ < 9 * (sigma β : ℝ) * N := by
      have hpositive : (0 : ℝ) < (sigma β : ℝ) * N := by
        linarith [honeFixed]
      nlinarith

/-- Actual degree-form exceptional and pointwise-loss estimates at the
explicit host threshold.  These are the two cleanup terms used by both the
rich Claim-6.1 entry and the final EC2 lift. -/
theorem degreeForm_exceptional_and_loss_small
    {β : ℚ} (hβ0 : 0 < β) (hβ1 : β ≤ 1 / 4)
    {N : ℕ} {G : SimpleGraph (Fin N)} [DecidableRel G.Adj]
    (W : DegreeFormWitness G (regularityEpsilon β) (reducedDensity β)
      (section6M₀ β)
      (degreeFormBound (regularityEpsilon β) (section6M₀ β)))
    (hN : section6N₀ β ≤ N) :
    (W.exceptional.card : ℝ) < (sigma β : ℝ) * N ∧
      (W.loss : ℝ) < 9 * (sigma β : ℝ) * N :=
  ⟨degreeForm_exceptional_small hβ0 hβ1 W hN,
    degreeForm_loss_small hβ0 hβ1 W hN⟩

/-- The exact padded-cluster estimates needed at the Lemma-6.11 entry.
The last inequality is the complete cleanup charge: degree-form loss,
exceptional vertices, Claim-6.1 missed clusters, and the four-cluster
distinguished-source reserve. -/
theorem degreeForm_preExceptional_bounds
    {β : ℚ} (hβ0 : 0 < β) (hβ1 : β ≤ 1 / 4)
    {N q : ℕ} {G : SimpleGraph (Fin N)} [DecidableRel G.Adj]
    (W : DegreeFormWitness G (regularityEpsilon β) (reducedDensity β)
      (section6M₀ β)
      (degreeFormBound (regularityEpsilon β) (section6M₀ β)))
    (hNq : N = 2 * q) (hN : section6N₀ β ≤ N) :
    let ι := {Q // Q ∈ W.partition.parts}
    let k := Erdos547b.ZhaoEvenReducedPadding.paddedHalf ι
    (k : ℝ) * W.clusterSize ≤ q + W.clusterSize ∧
      (q : ℝ) ≤ (k : ℝ) * W.clusterSize + W.exceptional.card / 2 ∧
      (W.exceptional.card : ℝ) / 2 ≤ (sigma β : ℝ) * q ∧
      (W.clusterSize : ℝ) ≤ (sigma β : ℝ) * q / 400 ∧
      ((W.loss + W.exceptional.card +
          claim61Miss β k * W.clusterSize + 4 * W.clusterSize : ℕ) : ℝ) <
        10 * (fourthRootD β : ℝ) * q := by
  subst N
  classical
  dsimp only
  let ι := {Q // Q ∈ W.partition.parts}
  let k := Erdos547b.ZhaoEvenReducedPadding.paddedHalf ι
  let K := W.ordinaryParts
  have hk : section6K₀ β ≤ k := by
    dsimp only [k, ι]
    exact section6K₀_le_witnessPaddedHalf W
  have hq : 0 < q := by
    have hpositive : 0 < 5 * W.ordinaryParts :=
      Nat.mul_pos (by norm_num) W.ordinaryParts_pos
    have hhostPositive : 0 < 2 * q :=
      lt_of_lt_of_le hpositive W.five_ordinaryParts_le_host
    omega
  have hhost : W.exceptional.card + Fintype.card ι * W.clusterSize =
      2 * q := by
    simpa [ι] using exceptional_add_clusters_eq_host W
  have hpadded : 2 * k ≤ Fintype.card ι + 1 := by
    have h := Erdos547b.ZhaoEvenReducedPadding.paddedCard_le_card_add_one ι
    simpa only [Erdos547b.ZhaoEvenReducedPadding.paddedCard_eq_two_mul, k]
      using h
  have hcoverNat : k * W.clusterSize ≤ q + W.clusterSize := by
    have hmul := Nat.mul_le_mul_right W.clusterSize hpadded
    have hordinary : Fintype.card ι * W.clusterSize ≤ 2 * q := by omega
    have htwice : 2 * (k * W.clusterSize) ≤
        2 * (q + W.clusterSize) := by
      calc
        2 * (k * W.clusterSize) = (2 * k) * W.clusterSize := by ring
        _ ≤ (Fintype.card ι + 1) * W.clusterSize := hmul
        _ = Fintype.card ι * W.clusterSize + W.clusterSize := by ring
        _ ≤ 2 * q + W.clusterSize := Nat.add_le_add_right hordinary _
        _ ≤ 2 * (q + W.clusterSize) := by omega
    exact (Nat.mul_le_mul_left_iff (by norm_num : 0 < 2)).mp
      (by simpa [mul_assoc] using htwice)
  have hcoveredNat : 2 * q ≤
      2 * (k * W.clusterSize) + W.exceptional.card := by
    have hcard := Erdos547b.ZhaoEvenReducedPadding.card_le_paddedCard ι
    have hmul := Nat.mul_le_mul_right W.clusterSize hcard
    rw [Erdos547b.ZhaoEvenReducedPadding.paddedCard_eq_two_mul] at hmul
    calc
      2 * q = W.exceptional.card +
          Fintype.card ι * W.clusterSize := hhost.symm
      _ ≤ W.exceptional.card + (2 * k) * W.clusterSize :=
        Nat.add_le_add_left hmul _
      _ = 2 * (k * W.clusterSize) + W.exceptional.card := by ring
  have hcover : (k : ℝ) * W.clusterSize ≤ q + W.clusterSize := by
    exact_mod_cast hcoverNat
  have hcovered : (q : ℝ) ≤
      (k : ℝ) * W.clusterSize + W.exceptional.card / 2 := by
    have hcoveredR : (2 : ℝ) * q ≤
        2 * ((k : ℝ) * W.clusterSize) + W.exceptional.card := by
      exact_mod_cast hcoveredNat
    nlinarith
  obtain ⟨hE, hLoss⟩ :=
    degreeForm_exceptional_and_loss_small hβ0 hβ1 W hN
  push_cast at hE hLoss
  have herror : (W.exceptional.card : ℝ) / 2 ≤
      (sigma β : ℝ) * q := by
    linarith
  have hKscaleNat : 4 * section6K₀ β ≤ K := by
    have h := W.twice_requested_le_ordinary
    simp only [section6M₀] at h
    omega
  have hKscale : (4 : ℝ) * section6K₀ β ≤ K := by
    exact_mod_cast hKscaleNat
  have hsigmaK0 := sigma_target_large hβ0
    (k := section6K₀ β) le_rfl
  have hsigmaK : (800 : ℝ) ≤ (sigma β : ℝ) * K := by
    have hm := mul_le_mul_of_nonneg_left hKscale
      (show (0 : ℝ) ≤ (sigma β : ℝ) by
        exact_mod_cast (sigma_pos hβ0).le)
    nlinarith
  have hdivNat := Nat.div_mul_le_self (2 * q) K
  have hdiv : (((2 * q) / K : ℕ) : ℝ) * K ≤ 2 * q := by
    exact_mod_cast hdivNat
  have hleft := mul_le_mul_of_nonneg_right hsigmaK
    (show (0 : ℝ) ≤ (((2 * q) / K : ℕ) : ℝ) by positivity)
  have hright := mul_le_mul_of_nonneg_left hdiv
    (show (0 : ℝ) ≤ (sigma β : ℝ) by
      exact_mod_cast (sigma_pos hβ0).le)
  have haverage : (((2 * q) / K : ℕ) : ℝ) ≤
      (sigma β : ℝ) * q / 400 := by
    nlinarith
  have hcluster : (W.clusterSize : ℝ) ≤
      (sigma β : ℝ) * q / 400 := by
    have hmNat : W.clusterSize ≤ (2 * q) / K := by
      simpa only [K] using W.clusterSize_le_average
    have hmR : (W.clusterSize : ℝ) ≤ (((2 * q) / K : ℕ) : ℝ) := by
      exact_mod_cast hmNat
    exact hmR.trans haverage
  have hcUpper : (claim61C β k : ℝ) <
      50 * (sigma β : ℝ) * k + 1 := by
    exact upperScale_cast_lt_add_one (by positivity [sigma_pos hβ0])
  have hmissUpper : (claim61Miss β k : ℝ) <
      100 * (sigma β : ℝ) * k + 3 := by
    simp only [claim61Miss]
    push_cast
    linarith
  have hm0 : (0 : ℝ) ≤ W.clusterSize := by positivity
  have hmissm : (claim61Miss β k : ℝ) * W.clusterSize <
      (100 * (sigma β : ℝ) * k + 3) * W.clusterSize :=
    mul_lt_mul_of_pos_right hmissUpper (by exact_mod_cast W.clusterSize_pos)
  have hsigmaOne := sigma_le_one_div hβ0 hβ1
  have hfourthSmall : (fourthRootD β : ℝ) ≤ 1 / 1000 := by
    have h := fourthRootD_le_eta_div_1000 hβ0 hβ1
    have heta : (eta β : ℝ) ≤ 1 :=
      (eta_le_rho_div_1000 hβ0 hβ1).trans (by
        have hr : (rho β : ℝ) ≤ 1 := by
          exact_mod_cast rho_le_one hβ0 hβ1
        linarith)
    linarith
  have hsigmaFourth : (sigma β : ℝ) ≤
      (fourthRootD β : ℝ) / 1000 := by
    rw [sigma]
    push_cast
    have hf0 : (0 : ℝ) ≤ (fourthRootD β : ℝ) := by
      exact_mod_cast (fourthRootD_pos hβ0).le
    nlinarith
  have hcleanupSigma :
      (W.loss : ℝ) + W.exceptional.card +
          (claim61Miss β k : ℝ) * W.clusterSize + 4 * W.clusterSize <
        123 * (sigma β : ℝ) * q := by
    have hcoverScaled := mul_le_mul_of_nonneg_left hcover
      (show (0 : ℝ) ≤ 100 * (sigma β : ℝ) by
        have hs : (0 : ℝ) ≤ (sigma β : ℝ) := by
          exact_mod_cast (sigma_pos hβ0).le
        positivity)
    have hclusterScaled := mul_le_mul_of_nonneg_left hcluster
      (show (0 : ℝ) ≤ 103 by norm_num)
    nlinarith
  have hcleanup :
      (W.loss : ℝ) + W.exceptional.card +
          (claim61Miss β k : ℝ) * W.clusterSize + 4 * W.clusterSize <
        10 * (fourthRootD β : ℝ) * q := by
    have hscale := mul_le_mul_of_nonneg_right hsigmaFourth
      (show (0 : ℝ) ≤ q by positivity)
    have hpositive : (0 : ℝ) < (fourthRootD β : ℝ) * q := by
      have hf : (0 : ℝ) < (fourthRootD β : ℝ) := by
        exact_mod_cast fourthRootD_pos hβ0
      have hqR : (0 : ℝ) < q := by exact_mod_cast hq
      positivity
    nlinarith
  refine ⟨hcover, hcovered, herror, hcluster, ?_⟩
  push_cast
  simpa only [Nat.cast_add, Nat.cast_mul] using hcleanup

theorem degreeForm_endpoint_error_small
    {β : ℚ} (hβ0 : 0 < β) (hβ1 : β ≤ 1 / 4)
    {N q : ℕ} {G : SimpleGraph (Fin N)} [DecidableRel G.Adj]
    (W : DegreeFormWitness G (regularityEpsilon β) (reducedDensity β)
      (section6M₀ β)
      (degreeFormBound (regularityEpsilon β) (section6M₀ β)))
    (hNq : N = 2 * q) (hN : section6N₀ β ≤ N) :
    ((W.exceptional.card + W.loss : ℕ) : ℝ) ≤ (β : ℝ) * q / 16 := by
  obtain ⟨hE, hLoss⟩ :=
    degreeForm_exceptional_and_loss_small hβ0 hβ1 W hN
  have hσβ := sigma_le_beta_div hβ0 hβ1
  have hq0 : (0 : ℝ) ≤ q := by positivity
  subst N
  push_cast at hE hLoss ⊢
  have hsum : (W.exceptional.card : ℝ) + W.loss <
      20 * (sigma β : ℝ) * q := by
    calc
      (W.exceptional.card : ℝ) + W.loss <
          (sigma β : ℝ) * (2 * q) +
            9 * (sigma β : ℝ) * (2 * q) := add_lt_add hE hLoss
      _ = 20 * (sigma β : ℝ) * q := by ring
  have hσq := mul_le_mul_of_nonneg_right hσβ hq0
  have hscaled : 20 * (sigma β : ℝ) * q ≤ (β : ℝ) * q / 16 := by
    have h20 := mul_le_mul_of_nonneg_left hσq
      (show (0 : ℝ) ≤ 20 by norm_num)
    have hβ0R : (0 : ℝ) ≤ β := by exact_mod_cast hβ0.le
    nlinarith
  exact hsum.le.trans hscaled

private theorem richQuota_density_separation_for_entry
    {β : ℚ} (hβ : 0 < β) {m : ℕ} (hm : 0 < m) :
    (((2 *
        (Erdos547b.ZhaoSection6RichHierarchy.richQuota (sigma β : ℝ) m - 1) *
        m : ℕ) : ℚ)) <
      reducedDensity β * (m : ℚ) * (m : ℚ) := by
  apply Erdos547b.ZhaoSection6RichHierarchy.richQuota_density_separation
  · exact_mod_cast sigma_pos hβ
  · exact hm
  · exact rich_cutoff_separation hβ

private theorem richQuota_total_error_for_entry
    {β : ℚ} (hβ : 0 < β) {K m q : ℕ}
    (hm : 0 < m) (hq : 0 < q) (hKm : K * m ≤ 2 * q) :
    ((K *
      (Erdos547b.ZhaoSection6RichHierarchy.richQuota (sigma β : ℝ) m - 1) : ℕ) :
        ℝ) < 4 * (sigma β : ℝ) * q := by
  exact Erdos547b.ZhaoSection6RichHierarchy.richQuota_total_error_lt
    (by exact_mod_cast sigma_pos hβ) hm hq hKm

private theorem claim61_capacity_for_entry
    {β : ℚ} {k m e exceptional : ℕ}
    (hbound :
      ((m + 2 * e + exceptional : ℕ) : ℝ) ≤
        100 * (sigma β : ℝ) * k * m) :
    m + 2 * e + exceptional ≤ 2 * claim61C β k * m := by
  have hc : 50 * (sigma β : ℝ) * k ≤ (claim61C β k : ℝ) :=
    le_upperScale_cast _
  have hright :
      100 * (sigma β : ℝ) * k * m ≤
        (2 * claim61C β k * m : ℕ) := by
    push_cast
    have htwice := mul_le_mul_of_nonneg_left hc
      (show (0 : ℝ) ≤ 2 by norm_num)
    have hm := mul_le_mul_of_nonneg_right htwice
      (show (0 : ℝ) ≤ m by positivity)
    ring_nf at hm ⊢
    exact hm
  exact_mod_cast hbound.trans hright

private theorem richEntry_three_and_error_for_entry
    {β : ℚ} (hβ0 : 0 < β) (hβ1 : β ≤ 1 / 4) {q E : ℕ}
    (hE : (E : ℝ) ≤ (β : ℝ) * q / 4) :
    3 * E ≤ q ∧
      (((3 * q * E : ℕ) : ℕ) : ℚ) ≤
        β * (q : ℚ) * (q : ℚ) := by
  have hβR1 : (β : ℝ) ≤ (1 / 4 : ℝ) := by
    simpa using (Rat.cast_le (K := ℝ)).mpr hβ1
  have hthreeR : (3 : ℝ) * E ≤ q := by
    have hβR0 : (0 : ℝ) < β := by exact_mod_cast hβ0
    have hq0 : (0 : ℝ) ≤ q := by positivity
    have hE0 : (0 : ℝ) ≤ E := by positivity
    nlinarith
  have herrorR : (3 : ℝ) * q * E ≤ (β : ℝ) * q * q := by
    have hmul := mul_le_mul_of_nonneg_left hE
      (show (0 : ℝ) ≤ 3 * q by positivity)
    nlinarith
  exact ⟨by exact_mod_cast hthreeR, by exact_mod_cast herrorR⟩

/-- All numeric premises of `pruned_degreeForm_ec1_or_richClaim61...` for an
actual degree-form witness on the Ramsey host.  No graph-theoretic conclusion
is included in this package. -/
theorem degreeForm_richEntry_numerics
    {β : ℚ} (hβ0 : 0 < β) (hβ1 : β ≤ 1 / 4)
    {N q : ℕ} {G : SimpleGraph (Fin N)} [DecidableRel G.Adj]
    (W : DegreeFormWitness G (regularityEpsilon β) (reducedDensity β)
      (section6M₀ β)
      (degreeFormBound (regularityEpsilon β) (section6M₀ β)))
    (hNq : N = 2 * q) (hN : section6N₀ β ≤ N) :
    let ι := {Q // Q ∈ W.partition.parts}
    let k := Erdos547b.ZhaoEvenReducedPadding.paddedHalf ι
    let quota := Erdos547b.ZhaoSection6RichHierarchy.richQuota
      (sigma β : ℝ) W.clusterSize
    let richCap := Fintype.card ι * (quota - 1)
    0 < quota ∧
      claim61C β k ≤ k ∧
      (((2 * (quota - 1) * W.clusterSize : ℕ) : ℚ)) <
        reducedDensity β * (W.clusterSize : ℚ) * (W.clusterSize : ℚ) ∧
      W.clusterSize + 2 * W.loss + W.exceptional.card ≤
        2 * claim61C β k * W.clusterSize ∧
      W.clusterSize + 2 * richCap + W.exceptional.card ≤
        2 * claim61C β k * W.clusterSize ∧
      3 * (W.exceptional.card + W.loss + richCap) ≤ q ∧
      (((3 * q * (W.exceptional.card + W.loss + richCap) : ℕ) : ℕ) : ℚ) ≤
        β * (q : ℚ) * (q : ℚ) := by
  subst N
  classical
  dsimp only
  let ι := {Q // Q ∈ W.partition.parts}
  let k := Erdos547b.ZhaoEvenReducedPadding.paddedHalf ι
  let quota := Erdos547b.ZhaoSection6RichHierarchy.richQuota
    (sigma β : ℝ) W.clusterSize
  let richCap := Fintype.card ι * (quota - 1)
  have hk : section6K₀ β ≤ k := by
    dsimp only [k, ι]
    exact section6K₀_le_witnessPaddedHalf W
  have hm : 0 < W.clusterSize := W.clusterSize_pos
  have hq : 0 < q := by
    have hfive : 0 < 5 * W.ordinaryParts :=
      Nat.mul_pos (by norm_num) W.ordinaryParts_pos
    have hhost : 0 < 2 * q :=
      lt_of_lt_of_le hfive W.five_ordinaryParts_le_host
    omega
  have hquota : 0 < quota := by
    dsimp only [quota]
    exact Erdos547b.ZhaoSection6RichHierarchy.richQuota_pos
      (by exact_mod_cast sigma_pos hβ0) hm
  have herrors := degreeForm_exceptional_and_loss_small hβ0 hβ1 W hN
  have hE := herrors.1
  have hLoss := herrors.2
  push_cast at hE hLoss
  have hσ0 : (0 : ℝ) < (sigma β : ℝ) := by exact_mod_cast sigma_pos hβ0
  have hσ1 := sigma_le_one_div hβ0 hβ1
  have hhost := exceptional_add_clusters_eq_host W
  have hhostR : (W.exceptional.card : ℝ) +
      (Fintype.card ι : ℝ) * W.clusterSize = 2 * q := by
    exact_mod_cast (by simpa [ι] using hhost)
  have hQpad : Fintype.card ι ≤ 2 * k := by
    have h := Erdos547b.ZhaoEvenReducedPadding.card_le_paddedCard ι
    simpa only [Erdos547b.ZhaoEvenReducedPadding.paddedCard_eq_two_mul,
      k] using h
  have hQpadR : (Fintype.card ι : ℝ) ≤ 2 * k := by exact_mod_cast hQpad
  have hEhalf : (W.exceptional.card : ℝ) < q := by
    have hqR : (0 : ℝ) < q := by exact_mod_cast hq
    have hσq := mul_le_mul_of_nonneg_right hσ1
      (show (0 : ℝ) ≤ 2 * q by positivity)
    have hmiddle : (sigma β : ℝ) * (2 * q) ≤
        (1 / 1000 : ℝ) * (2 * q) := hσq
    have hlast : (1 / 1000 : ℝ) * (2 * q) < q := by
      nlinarith
    exact hE.trans (hmiddle.trans_lt hlast)
  have hkmLower : (2 : ℝ) * q < 4 * (k : ℝ) * W.clusterSize := by
    have hQm : (q : ℝ) < (Fintype.card ι : ℝ) * W.clusterSize := by
      nlinarith
    have hQmPad := mul_le_mul_of_nonneg_right hQpadR
      (show (0 : ℝ) ≤ W.clusterSize by positivity)
    nlinarith
  have hQmNat : Fintype.card ι * W.clusterSize ≤ 2 * q := by
    have hEq : W.exceptional.card +
        Fintype.card ι * W.clusterSize = 2 * q := by
      simpa [ι] using hhost
    omega
  have hRich := richQuota_total_error_for_entry hβ0 hm hq hQmNat
  have hRichN : (richCap : ℝ) < 4 * (sigma β : ℝ) * q := by
    simpa only [richCap, quota, ι] using hRich
  have hKaverage : ((2 * q / W.ordinaryParts : ℕ) : ℝ) ≤
      (5 / 4 : ℝ) * (sigma β : ℝ) * (2 * q) := by
    have hKscaleNat : 4 * section6K₀ β ≤ W.ordinaryParts := by
      have h := W.twice_requested_le_ordinary
      simp only [section6M₀] at h
      omega
    have hKscale : (4 : ℝ) * section6K₀ β ≤ W.ordinaryParts := by
      exact_mod_cast hKscaleNat
    have hσK0 := sigma_target_large hβ0
      (k := section6K₀ β) le_rfl
    have hσK : (800 : ℝ) ≤
        (sigma β : ℝ) * W.ordinaryParts := by
      have hm := mul_le_mul_of_nonneg_left hKscale
        (show (0 : ℝ) ≤ (sigma β : ℝ) by
          exact_mod_cast (sigma_pos hβ0).le)
      nlinarith
    have hdivNat := Nat.div_mul_le_self (2 * q) W.ordinaryParts
    have hdiv : (((2 * q) / W.ordinaryParts : ℕ) : ℝ) *
        W.ordinaryParts ≤ 2 * q := by exact_mod_cast hdivNat
    have hleft := mul_le_mul_of_nonneg_right hσK
      (show (0 : ℝ) ≤ (((2 * q) / W.ordinaryParts : ℕ) : ℝ) by positivity)
    have hright := mul_le_mul_of_nonneg_left hdiv
      (show (0 : ℝ) ≤ (sigma β : ℝ) by
        exact_mod_cast (sigma_pos hβ0).le)
    have hbase : (((2 * q) / W.ordinaryParts : ℕ) : ℝ) ≤
        (sigma β : ℝ) * (2 * q) / 800 := by
      apply (le_div_iff₀ (by norm_num : (0 : ℝ) < 800)).2
      calc
        (((2 * q) / W.ordinaryParts : ℕ) : ℝ) * 800 =
            800 * (((2 * q) / W.ordinaryParts : ℕ) : ℝ) := by ring
        _ ≤ ((sigma β : ℝ) * W.ordinaryParts) *
            (((2 * q) / W.ordinaryParts : ℕ) : ℝ) := hleft
        _ = (sigma β : ℝ) *
            ((((2 * q) / W.ordinaryParts : ℕ) : ℝ) *
              W.ordinaryParts) := by ring
        _ ≤ (sigma β : ℝ) * (2 * q) := hright
    linarith
  have hmUpper : (W.clusterSize : ℝ) ≤
      (5 / 4 : ℝ) * (sigma β : ℝ) * (2 * q) := by
    have hmNat := W.clusterSize_le_average
    have hmR : (W.clusterSize : ℝ) ≤
        ((2 * q / W.ordinaryParts : ℕ) : ℝ) := by exact_mod_cast hmNat
    exact hmR.trans hKaverage
  have hdegreeReal :
      ((W.clusterSize + 2 * W.loss + W.exceptional.card : ℕ) : ℝ) <
        25 * (sigma β : ℝ) * (2 * q) := by
    push_cast
    have htwiceLoss := mul_lt_mul_of_pos_left hLoss
      (show (0 : ℝ) < 2 by norm_num)
    have hsum := add_lt_add_of_le_of_lt hmUpper
      (add_lt_add htwiceLoss hE)
    have hsqp : (0 : ℝ) < (sigma β : ℝ) * q := by positivity
    ring_nf at hsum ⊢
    linarith
  have hcardReal :
      ((W.clusterSize + 2 * richCap + W.exceptional.card : ℕ) : ℝ) <
        25 * (sigma β : ℝ) * (2 * q) := by
    push_cast
    have htwiceRich := mul_lt_mul_of_pos_left hRichN
      (show (0 : ℝ) < 2 by norm_num)
    have hsum := add_lt_add_of_le_of_lt hmUpper
      (add_lt_add htwiceRich hE)
    have hsqp : (0 : ℝ) < (sigma β : ℝ) * q := by positivity
    ring_nf at hsum ⊢
    linarith
  have hcapacityLower :
      25 * (sigma β : ℝ) * (2 * q) <
        100 * (sigma β : ℝ) * k * W.clusterSize := by
    have := mul_lt_mul_of_pos_left hkmLower
      (show (0 : ℝ) < 25 * (sigma β : ℝ) by positivity)
    nlinarith
  have hdegreeCapacity := claim61_capacity_for_entry
    (hdegreeReal.trans hcapacityLower).le
  have hcardCapacity := claim61_capacity_for_entry
    (hcardReal.trans hcapacityLower).le
  have htotal :
      ((W.exceptional.card + W.loss + richCap : ℕ) : ℝ) <
        12 * (sigma β : ℝ) * (2 * q) := by
    push_cast
    have hsum := add_lt_add hE (add_lt_add hLoss hRichN)
    calc
      (W.exceptional.card : ℝ) + W.loss + richCap =
          (W.exceptional.card : ℝ) + (W.loss + richCap) := by ring
      _ <
          (sigma β : ℝ) * (2 * q) +
            (9 * (sigma β : ℝ) * (2 * q) +
              4 * (sigma β : ℝ) * q) := hsum
      _ = 12 * (sigma β : ℝ) * (2 * q) := by ring
  have hσβ := sigma_le_beta_div hβ0 hβ1
  have htotalQuarter :
      ((W.exceptional.card + W.loss + richCap : ℕ) : ℝ) ≤
        (β : ℝ) * q / 4 := by
    have hqR : (0 : ℝ) < q := by exact_mod_cast hq
    have hσq := mul_le_mul_of_nonneg_right hσβ hqR.le
    nlinarith
  have hthreeError := richEntry_three_and_error_for_entry
    hβ0 hβ1 htotalQuarter
  refine ⟨hquota, claim61C_le_reducedHalf hβ0 hβ1 hk, ?_,
    hdegreeCapacity, hcardCapacity, hthreeError.1, hthreeError.2⟩
  simpa only [quota] using richQuota_density_separation_for_entry hβ0 hm

/-- The corrected rich Claim-6.1 entry with every hierarchy premise filled by
the explicit scales above.  The only remaining assumptions are the original
Ramsey high-degree count and the concrete degree-form witness. -/
theorem pruned_degreeForm_ec1_or_richClaim61_explicit
    {β : ℚ} (hβ0 : 0 < β) (hβ1 : β ≤ 1 / 4)
    {n : ℕ}
    (G : SimpleGraph (Fin (2 * n - 2))) [DecidableRel G.Adj]
    (W : DegreeFormWitness
      (pruneSmallEdges G {v | n - 1 ≤ G.degree v})
      (regularityEpsilon β) (reducedDensity β) (section6M₀ β)
      (degreeFormBound (regularityEpsilon β) (section6M₀ β)))
    (hn : 2 ≤ n)
    (hlarge : n - 1 ≤
      (Finset.univ.filter fun v => n - 1 ≤ G.degree v).card)
    (hN : section6N₀ β ≤ 2 * n - 2) :
    let ι := {Q // Q ∈ W.partition.parts}
    let P : ClusterAssignment (Fin (2 * n - 2)) ι :=
      partitionAssignment W.exceptional W.partition
    let H := pruneSmallEdges G {v | n - 1 ≤ G.degree v}
    let R : SimpleGraph ι :=
      regularityReducedGraph H (fun i : ι => i.1)
        (regularityEpsilon β) (reducedDensity β)
    let quota := richQuota (sigma β : ℝ) W.clusterSize
    let L := Erdos547b.ZhaoQuantitativeLargeClusters.largeClustersAtLeast
      P G (n - 1) quota
    ZhaoExtremalCaseOne β G ∨
      Nonempty (Erdos547b.ZhaoClaim61RichFull.RichClaim61Certificate
        P G (n - 1) quota R L
          (2 * claim61C β
            (Erdos547b.ZhaoEvenReducedPadding.paddedHalf ι) + 1)) := by
  classical
  let ι := {Q // Q ∈ W.partition.parts}
  let k := Erdos547b.ZhaoEvenReducedPadding.paddedHalf ι
  let quota := richQuota (sigma β : ℝ) W.clusterSize
  have hhosteq : 2 * n - 2 = 2 * (n - 1) := by omega
  have hnum := degreeForm_richEntry_numerics hβ0 hβ1 W hhosteq hN
  dsimp only at hnum
  obtain ⟨hquota, hc, hdensity, hdegree, hcard, hthree, herror⟩ := hnum
  simpa only [ι, k, quota] using
    (pruned_degreeForm_ec1_or_richClaim61_of_error_capacities
      G W hn hlarge quota (claim61C β k) hquota hdensity hc
      hdegree hcard hthree herror)

/-- Direct specialization of the quantitative-rich density premise. -/
theorem richQuota_density_separation_explicit
    {β : ℚ} (hβ : 0 < β) {m : ℕ} (hm : 0 < m) :
    (((2 *
        (Erdos547b.ZhaoSection6RichHierarchy.richQuota (sigma β : ℝ) m - 1) *
        m : ℕ) : ℚ)) <
      reducedDensity β * (m : ℚ) * (m : ℚ) := by
  apply Erdos547b.ZhaoSection6RichHierarchy.richQuota_density_separation
  · exact_mod_cast sigma_pos hβ
  · exact hm
  · exact rich_cutoff_separation hβ

/-- The deterministic discarded-high-vertex error from non-rich clusters is
strictly below `4*sigma*q` whenever the regular clusters cover at most the
two Ramsey sides. -/
theorem richQuota_total_error_explicit
    {β : ℚ} (hβ : 0 < β) {K m q : ℕ}
    (hm : 0 < m) (hq : 0 < q) (hKm : K * m ≤ 2 * q) :
    ((K *
      (Erdos547b.ZhaoSection6RichHierarchy.richQuota (sigma β : ℝ) m - 1) : ℕ) :
        ℝ) < 4 * (sigma β : ℝ) * q := by
  exact Erdos547b.ZhaoSection6RichHierarchy.richQuota_total_error_lt
    (by exact_mod_cast sigma_pos hβ) hm hq hKm

/-- Upward rounding of `c` turns the scale-level capacity `100*sigma*k*m`
into the exact natural capacity consumed by quantitative Claim 6.1. -/
theorem claim61_capacity_of_real_bound
    {β : ℚ} (hβ : 0 < β) {k m e exceptional : ℕ}
    (hbound :
      ((m + 2 * e + exceptional : ℕ) : ℝ) ≤
        100 * (sigma β : ℝ) * k * m) :
    m + 2 * e + exceptional ≤ 2 * claim61C β k * m := by
  have hc : 50 * (sigma β : ℝ) * k ≤ (claim61C β k : ℝ) := by
    exact le_upperScale_cast _
  have hright :
      100 * (sigma β : ℝ) * k * m ≤
        (2 * claim61C β k * m : ℕ) := by
    push_cast
    have htwice := mul_le_mul_of_nonneg_left hc
      (show (0 : ℝ) ≤ 2 by norm_num)
    have hm := mul_le_mul_of_nonneg_right htwice
      (show (0 : ℝ) ≤ m by positivity)
    ring_nf at hm ⊢
    exact hm
  exact_mod_cast hbound.trans hright

/-- A single quarter-error bound discharges both `hthree` and `herror` in
the rich Claim-6.1 entry. -/
theorem richEntry_three_and_error_of_total_bound
    {β : ℚ} (hβ0 : 0 < β) (hβ1 : β ≤ 1 / 4) {q E : ℕ}
    (hE : (E : ℝ) ≤ (β : ℝ) * q / 4) :
    3 * E ≤ q ∧
      (((3 * q * E : ℕ) : ℕ) : ℚ) ≤
        β * (q : ℚ) * (q : ℚ) := by
  have hβR0 : (0 : ℝ) < β := by exact_mod_cast hβ0
  have hβR1 : (β : ℝ) ≤ (1 / 4 : ℝ) := by
    simpa using (Rat.cast_le (K := ℝ)).mpr hβ1
  have hq0 : (0 : ℝ) ≤ q := by positivity
  have hER0 : (0 : ℝ) ≤ E := by positivity
  have hthreeR : (3 : ℝ) * E ≤ q := by nlinarith
  have herrorR : (3 : ℝ) * q * E ≤
      (β : ℝ) * q * q := by
    have hmul := mul_le_mul_of_nonneg_left hE
      (show (0 : ℝ) ≤ 3 * q by positivity)
    nlinarith
  constructor
  · exact_mod_cast hthreeR
  · exact_mod_cast herrorR

/-- Final EC2 host arithmetic after Claims 6.17--6.18.  The hypotheses are
the elementary component bounds supplied respectively by the equal-cluster
partition, degree-form cleanup, and the source-side imbalance estimate. -/
theorem final_host_numeric_of_component_bounds
    {β : ℚ} (hβ0 : 0 < β) (hβ1 : β ≤ 1 / 4)
    {k m q x error b : ℕ}
    (hkm : (k : ℝ) * m ≤ 2 * q)
    (hx : (x : ℝ) ≤ 2 * q)
    (herror : (error : ℝ) ≤ (β : ℝ) * q / 16)
    (hb : (b : ℝ) ≤ (β : ℝ) * q / 16) :
    16 * ((rho β : ℝ) + rhoOne β) * (k : ℝ) ^ 2 * (m : ℝ) ^ 2 +
        (x : ℝ) * error + 2 * q * b ≤
      (β : ℝ) * (q : ℝ) ^ 2 := by
  have hβR : (0 : ℝ) < β := by exact_mod_cast hβ0
  have hcoef := final_reduced_coefficient_lt hβ0 hβ1
  have hkmSq : ((k : ℝ) * m) ^ 2 ≤ (2 * (q : ℝ)) ^ 2 := by
    exact pow_le_pow_left₀ (by positivity) hkm 2
  have hred :
      16 * ((rho β : ℝ) + rhoOne β) * (k : ℝ) ^ 2 * (m : ℝ) ^ 2 ≤
        ((β : ℝ) / 16) * (q : ℝ) ^ 2 := by
    have hcoefMul := mul_le_mul_of_nonneg_right hcoef.le
      (sq_nonneg ((k : ℝ) * m))
    have hscale := mul_le_mul_of_nonneg_left hkmSq
      (show (0 : ℝ) ≤ (β : ℝ) / 64 by positivity)
    nlinarith
  have hx0 : (0 : ℝ) ≤ x := by positivity
  have he0 : (0 : ℝ) ≤ error := by positivity
  have hb0 : (0 : ℝ) ≤ b := by positivity
  have hxerr : (x : ℝ) * error ≤
      ((β : ℝ) / 8) * (q : ℝ) ^ 2 := by
    calc
      (x : ℝ) * error ≤ (2 * (q : ℝ)) * error :=
        mul_le_mul_of_nonneg_right hx he0
      _ ≤ (2 * (q : ℝ)) * ((β : ℝ) * q / 16) :=
        mul_le_mul_of_nonneg_left herror (by positivity)
      _ = ((β : ℝ) / 8) * (q : ℝ) ^ 2 := by ring
  have hqb : (2 : ℝ) * q * b ≤
      ((β : ℝ) / 8) * (q : ℝ) ^ 2 := by
    calc
      (2 : ℝ) * q * b ≤ (2 * (q : ℝ)) * ((β : ℝ) * q / 16) :=
        mul_le_mul_of_nonneg_left hb (by positivity)
      _ = ((β : ℝ) / 8) * (q : ℝ) ^ 2 := by ring
  nlinarith [sq_nonneg (q : ℝ)]

/-- All purely numerical Claim-6.18 premises under the one actual
decomposition-dependent estimate `v ≤ k+8h`. -/
theorem explicit_eventual_claim618_hierarchy
    {β : ℚ} (hβ0 : 0 < β) (hβ1 : β ≤ 1 / 4) :
    ∀ k, section6K₀ β ≤ k →
      0 < claim618A β k ∧
      0 < claim618B β k ∧
      0 < claim618Z β k ∧
      0 < claim618U β k ∧
      (claim618A β k : ℝ) ≤ 8 * rhoOne β * k ∧
      2 * (claim618B β k + claim617Q β k + 1) +
          (2 * claim61C β k + 1) ≤ claim618A β k ∧
      claim618U β k + claim617Q β k ≤ claim618T β k ∧
      16 * (rho β : ℝ) * (k : ℝ) ^ 2 ≤
        ((claim618Z β k * claim618U β k : ℕ) : ℝ) ∧
      ∀ v, v ≤ k + 8 * claim617H β k →
        claim618Z β k * claim618A β k + v * claim618T β k ≤
          claim618A β k * claim618B β k := by
  intro k hk
  exact ⟨claim618A_pos hβ0 hβ1 hk, claim618B_pos hβ0 hβ1 hk,
    claim618Z_pos hβ0 hβ1 hk, claim618U_pos hβ0 hβ1 hk,
    claim618A_cast_le hβ0 k, claim618_local_inequality hβ0 hβ1 hk,
    claim618_partner_inequality β k, claim618_final_product hβ0 hβ1 hk,
    fun v hv ↦ claim618_double_count_inequality hβ0 hβ1 hk hv⟩

/-- Single numerical hierarchy theorem.  Its output matches the pure numeric
premises presently exposed by the rich Claim-6.1 entry, Claim 6.16, Claim
6.17, Claim 6.18's cube-root scale, and the final reduced EC2 bound. -/
theorem explicit_eventual_section6_hierarchy
    {β : ℚ} (hβ0 : 0 < β) (hβ1 : β ≤ 1 / 4) :
    0 < rho β ∧
    0 < eta β ∧
    0 < fourthRootD β ∧
    0 < sigma β ∧
    0 < embeddingGamma β ∧
    0 < reducedDensity β ∧
    0 < regularityEpsilon β ∧
    (sigma β : ℝ) ≤ (fourthRootD β : ℝ) ∧
    (fourthRootD β : ℝ) ≤ (eta β : ℝ) / 1000 ∧
    (eta β : ℝ) ≤ (rho β : ℝ) / 1000 ∧
    (embeddingGamma β : ℝ) ≤ (eta β : ℝ) ∧
    Real.sqrt (lemma611D β) = lemma611DSqrt β ∧
    3 * claim616Gamma β ≤
      claim616EpsilonTwo β - lemma611EpsilonOne β ∧
    (4 : ℝ) * (sigma β : ℝ) < (reducedDensity β : ℝ) ∧
    rhoOne β = Real.rpow (rho β : ℝ) (1 / 3 : ℝ) ∧
    16 * ((rho β : ℝ) + rhoOne β) < (β : ℝ) / 64 ∧
    degreeFormThreshold (regularityEpsilon β) (section6M₀ β) + 2 ≤
      section6N₀ β ∧
    ∀ k, section6K₀ β ≤ k →
      0 < mainScale β k ∧
      0 < claim616Scale β k ∧
      0 < minEdgeCap k ∧
      0 < auxiliaryScale β k ∧
      0 < claim617Q β k ∧
      claim61C β k ≤ k ∧
      80 * mainScale β k * claim617H β k +
          4 * claim617Q β k * k < mainScale β k * k ∧
      2 * claim61C β k + 1 + 4 * claim617Q β k ≤
        claim616Scale β k ∧
      0 < claim618A β k ∧
      0 < claim618B β k ∧
      0 < claim618Z β k ∧
      0 < claim618U β k ∧
      (claim618A β k : ℝ) ≤ 8 * rhoOne β * k ∧
      2 * (claim618B β k + claim617Q β k + 1) +
          (2 * claim61C β k + 1) ≤ claim618A β k ∧
      claim618U β k + claim617Q β k ≤ claim618T β k ∧
      16 * (rho β : ℝ) * (k : ℝ) ^ 2 ≤
        ((claim618Z β k * claim618U β k : ℕ) : ℝ) ∧
      ∀ v, v ≤ k + 8 * claim617H β k →
        claim618Z β k * claim618A β k + v * claim618T β k ≤
          claim618A β k * claim618B β k := by
  refine ⟨rho_pos hβ0, eta_pos hβ0, fourthRootD_pos hβ0,
    sigma_pos hβ0, embeddingGamma_pos hβ0, reducedDensity_pos hβ0,
    regularityEpsilon_pos hβ0, sigma_le_fourthRootD hβ0 hβ1,
    fourthRootD_le_eta_div_1000 hβ0 hβ1,
    eta_le_rho_div_1000 hβ0 hβ1, embeddingGamma_le_eta hβ0 hβ1,
    sqrt_lemma611D hβ0,
    claim616_margin_hierarchy hβ0 hβ1, rich_cutoff_separation hβ0,
    rhoOne_eq_rpow hβ0, final_reduced_coefficient_lt hβ0 hβ1,
    degreeFormThreshold_le_section6N₀ β, ?_⟩
  intro k hk
  obtain ⟨ha, hb, hz, hu, haScale, hlocal, hpartner, hfinal, hdouble⟩ :=
    explicit_eventual_claim618_hierarchy hβ0 hβ1 k hk
  exact ⟨mainScale_pos hβ0 hβ1 hk,
    claim616Scale_pos hβ0 hβ1 hk,
    minEdgeCap_pos hβ0 hβ1 hk, auxiliaryScale_pos hβ0 hk,
    claim617Q_pos hβ0 hk,
    claim61C_le_reducedHalf hβ0 hβ1 hk,
    claim617_rounding_inequality hβ0 hβ1 hk,
    claim616_reserve_inequality hβ0 hβ1 hk, ha, hb, hz, hu, haScale,
    hlocal, hpartner, hfinal, hdouble⟩

#print axioms three_regularityEpsilon_le_density_gap_mul_embeddingGamma
#print axioms regularityEpsilon_lt_reducedDensity
#print axioms claim617Q_cast_le_eta_half

end Erdos547b.ZhaoSection6EventualParameters
