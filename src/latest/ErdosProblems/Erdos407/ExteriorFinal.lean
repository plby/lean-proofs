/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
import ErdosProblems.Erdos407.ExteriorFiniteGlue
import ErdosProblems.Erdos407.ExteriorWedgeBounds
import ErdosProblems.Erdos407.AdelicSuccessiveMinima
import ErdosProblems.Erdos407.AdelicMinimaProduct
import ErdosProblems.Erdos407.AdelicMinimaUpper
import ErdosProblems.Erdos407.AdelicMinimaLogBounds
import ErdosProblems.Erdos407.WeightedEvertseBasis
import ErdosProblems.Erdos407.RankDropTerminalFinal

/-!
# The exterior-power endpoint for the rational three-place Subspace Theorem

This is the acyclic final assembly module.  Its imported layers provide:

* finite exponent boxing and the final finite-cover glue;
* rank-adapted adelic successive minima;
* the row-weighted Evertse triangular basis and the omitted-wedge estimates;
* dimension-generic rank stabilization for the resulting exterior domains.

The small lemmas below convert positive multiplicative factors into exact
base-`Q` exponents.  This keeps the constants from the weighted Evertse basis
and the successive-minimum saving visible in the exponent sum used by the
rank-stabilization theorem.
-/

namespace Erdos407.PadicSubspace

open scoped BigOperators ExteriorAlgebra

namespace ExteriorFinal

open Erdos407 HeightBoxes

theorem two_le_choose_of_pos_of_lt {n q : ℕ} (hn : 2 ≤ n)
    (hq : 0 < q) (hqn : q < n) : 2 ≤ n.choose q := by
  have hpos : 0 < n.choose q := Nat.choose_pos hqn.le
  have hone : n.choose q ≠ 1 := by
    intro hone
    rcases Nat.choose_eq_one_iff.mp hone with hq0 | hnq
    · omega
    · omega
  omega

theorem choose_le_ten_of_le_five {n : ℕ} (hn : n ≤ 5) (q : ℕ) :
    n.choose q ≤ 10 := by
  by_cases hq : q ≤ n
  · interval_cases n <;> interval_cases q <;> norm_num [Nat.choose]
  · rw [Nat.choose_eq_zero_of_lt (Nat.lt_of_not_ge hq)]
    omega

/-! ## Integral points and the `S`-integral approximation span -/

/-- Every integral vector is, tautologically, integral away from `2` and
`3`.  Stating this explicitly avoids any denominator-normalization step when
the original strong solution is inserted into the `S`-integral domain. -/
theorem intCastVec_inZOneSix {n : ℕ} (x : IntVector n) :
    AdelicMinkowski.InZOneSix (intCastVec x) := by
  refine ⟨0, x, ?_⟩
  intro i
  simp [intCastVec]

/-- An integral point in a real approximation box belongs to the genuine
`Z[1/6]` domain used by rank stabilization. -/
theorem intCastVec_mem_realSIntegralApproximationDomain {n Q : ℕ}
    {L : Place23 → Fin n → RatLinearForm n}
    {c : HeightBoxes.LocalConstants n} {x : IntVector n}
    (hx : InApproximationBox L (Q : ℝ) c (intCastVec x)) :
    intCastVec x ∈
      Erdos407.RankDrop.realSIntegralApproximationDomain L Q c := by
  exact ⟨intCastVec_inZOneSix x, hx⟩

/-- A nonzero point in an `S`-integral approximation domain forces that
domain's rational span to have positive rank. -/
theorem realSApproximationRank_pos_of_mem {n Q : ℕ}
    {L : Place23 → Fin n → RatLinearForm n}
    {c : HeightBoxes.LocalConstants n} {x : Fin n → ℚ}
    (hx0 : x ≠ 0)
    (hx : x ∈ Erdos407.RankDrop.realSIntegralApproximationDomain L Q c) :
    0 < Erdos407.RankDrop.realSApproximationRank L Q c := by
  rw [Erdos407.RankDrop.realSApproximationRank]
  rw [Nat.lt_iff_add_one_le, zero_add,
    Submodule.one_le_finrank_iff]
  intro hbot
  have hxspan := Erdos407.RankDrop.mem_realSApproximationSpan hx
  rw [hbot] at hxspan
  exact hx0 ((Submodule.mem_bot ℚ).mp hxspan)

/-! ## The unconditional upper successive-minima certificate -/

/-- A canonical choice of the genuine adelic Minkowski certificate.  This
is a definition, not an extra endpoint premise: its inhabitant is supplied
by `AdelicMinimaUpper.exists_upperAdaptedBasisCertificate`. -/
noncomputable def upperAdaptedCertificate {n Q : ℕ}
    (hn : 0 < n) (L : Place23 → Fin n → RatLinearForm n)
    (hL : IsNonsingularFamily L) (hQ : 1 ≤ Q)
    (c : HeightBoxes.LocalConstants n) :
    AdelicMinimaUpper.UpperAdaptedBasisCertificate L Q c
      (AdelicMinimaUpper.upperConstant L) :=
  Classical.choice
    (AdelicMinimaUpper.exists_upperAdaptedBasisCertificate hn L hL hQ c)

theorem upperAdaptedCertificate_product_le {n Q : ℕ}
    (hn : 0 < n) (L : Place23 → Fin n → RatLinearForm n)
    (hL : IsNonsingularFamily L) (hQ : 1 ≤ Q)
    (c : HeightBoxes.LocalConstants n) :
    ∏ i, (upperAdaptedCertificate hn L hL hQ c).lambda i ≤
      AdelicMinimaUpper.upperConstant L *
        (Q : ℝ) ^ (-(∑ place, ∑ i, c place i)) := by
  exact (upperAdaptedCertificate hn L hL hQ c).product_le_rpow_neg_sum hQ

/-- If an original integral point enters the labelled box, the adapted
certificate selected above has positive scale-one rank and its prefix span
contains that point. -/
theorem upperAdaptedCertificate_rank_pos_and_mem {n Q : ℕ}
    (hn : 0 < n) (L : Place23 → Fin n → RatLinearForm n)
    (hL : IsNonsingularFamily L) (hQ : 1 ≤ Q)
    (c : HeightBoxes.LocalConstants n) {x : IntVector n} (hx0 : x ≠ 0)
    (hx : InApproximationBox L (Q : ℝ) c (intCastVec x)) :
    0 < (upperAdaptedCertificate hn L hL hQ c).rank ∧
      intCastVec x ∈
        Erdos407.RankDrop.realSApproximationSpan L Q c := by
  have hxD := intCastVec_mem_realSIntegralApproximationDomain hx
  exact ⟨by
    simpa [(upperAdaptedCertificate hn L hL hQ c).rank_eq] using
      realSApproximationRank_pos_of_mem
        (Primitive.intCastVec_ne_zero hx0) hxD,
    Erdos407.RankDrop.mem_realSApproximationSpan hxD⟩

/-- Every original finite-box upper endpoint lies in the fixed compact
interval needed by the individual minima bounds. -/
theorem upperLocalConstants_mem_Icc {n : ℕ}
    (b : ExteriorFiniteGlue.LocalBoxLabel n
      ExteriorFiniteGlue.originalBoxingMesh)
    (place : Place23) (i : Fin n) :
    ExteriorFiniteGlue.upperLocalConstants b place i ∈
      Set.Icc (-5 : ℝ) 3 := by
  have hb := (b place i).2
  unfold ExteriorFiniteGlue.upperLocalConstants
  norm_num [ExteriorFiniteGlue.originalBoxingMesh,
    HeightBoxes.BoundedLogBox] at hb ⊢
  have hbR : (-300 : ℝ) ≤ ((b place i).1 : ℝ) ∧
      ((b place i).1 : ℝ) ≤ 120 := by
    exact_mod_cast hb
  constructor <;> nlinarith [hbR.1, hbR.2]

/-- The canonical upper certificate has all base-`Q` minima exponents in
one symmetric interval depending only on the fixed original forms. -/
theorem upperAdaptedCertificate_logarithmicExponent_mem_Icc
    {n Q : ℕ} (hn : 0 < n)
    (L : Place23 → Fin n → RatLinearForm n)
    (hL : IsNonsingularFamily L) (hQ : 2 ≤ Q)
    (b : ExteriorFiniteGlue.LocalBoxLabel n
      ExteriorFiniteGlue.originalBoxingMesh) (j : Fin n) :
    AdelicMinimaLogBounds.logarithmicExponent Q
        ((upperAdaptedCertificate hn L hL (Nat.le_trans (by decide) hQ)
          (ExteriorFiniteGlue.upperLocalConstants b)).lambda j) ∈
      Set.Icc (-AdelicMinimaLogBounds.logarithmicBound L)
        (AdelicMinimaLogBounds.logarithmicBound L) := by
  exact AdelicMinimaLogBounds.logarithmicExponent_mem_Icc hL hQ
    (upperLocalConstants_mem_Icc b)
    (upperAdaptedCertificate hn L hL (Nat.le_trans (by decide) hQ)
      (ExteriorFiniteGlue.upperLocalConstants b)) j

/-- The exact exponent of a positive real factor in base `Q`. -/
noncomputable def logarithmicExponent (Q : ℕ) (a : ℝ) : ℝ :=
  Real.log a / Real.log (Q : ℝ)

theorem rpow_logarithmicExponent {Q : ℕ} (hQ : 1 < Q)
    {a : ℝ} (ha : 0 < a) :
    (Q : ℝ) ^ logarithmicExponent Q a = a := by
  have hQr : 0 < (Q : ℝ) := by positivity
  have hlogQ : Real.log (Q : ℝ) ≠ 0 :=
    (Real.log_pos (by exact_mod_cast hQ)).ne'
  rw [logarithmicExponent, Real.rpow_def_of_pos hQr]
  congr 1
  field_simp
  exact Real.exp_log ha

theorem logarithmicExponent_mono {Q : ℕ} (hQ : 1 < Q)
    {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    logarithmicExponent Q a ≤ logarithmicExponent Q b := by
  unfold logarithmicExponent
  apply (div_le_div_iff_of_pos_right
    (Real.log_pos (by exact_mod_cast hQ))).2
  exact Real.log_le_log ha hab

theorem logarithmicExponent_mul {Q : ℕ} {a b : ℝ}
    (ha : 0 < a) (hb : 0 < b) :
    logarithmicExponent Q (a * b) =
      logarithmicExponent Q a + logarithmicExponent Q b := by
  unfold logarithmicExponent
  rw [Real.log_mul ha.ne' hb.ne']
  ring

theorem logarithmicExponent_div {Q : ℕ} {a b : ℝ}
    (ha : 0 < a) (hb : 0 < b) :
    logarithmicExponent Q (a / b) =
      logarithmicExponent Q a - logarithmicExponent Q b := by
  unfold logarithmicExponent
  rw [Real.log_div ha.ne' hb.ne']
  ring

theorem logarithmicExponent_pow {Q m : ℕ} {a : ℝ} :
    logarithmicExponent Q (a ^ m) =
      m * logarithmicExponent Q a := by
  unfold logarithmicExponent
  rw [Real.log_pow]
  ring

theorem logarithmicExponent_rpow {Q : ℕ} (hQ : 1 < Q) (a : ℝ) :
    logarithmicExponent Q ((Q : ℝ) ^ a) = a := by
  have hQr : 0 < (Q : ℝ) := by positivity
  have hlogQ : Real.log (Q : ℝ) ≠ 0 :=
    (Real.log_pos (by exact_mod_cast hQ)).ne'
  unfold logarithmicExponent
  rw [Real.log_rpow hQr]
  exact mul_div_cancel_right₀ a hlogQ

/-- A fixed positive multiplicative loss has a uniformly bounded base-`Q`
exponent for every integral base `Q ≥ 2`. -/
theorem abs_logarithmicExponent_le_of_two_le {Q : ℕ} (hQ : 2 ≤ Q)
    {a : ℝ} (_ha : 0 < a) :
    |logarithmicExponent Q a| ≤
      |Real.log a| / Real.log 2 := by
  have hQone : 1 < Q := by omega
  have hlogQ : 0 < Real.log (Q : ℝ) :=
    Real.log_pos (by exact_mod_cast hQone)
  have hlogTwo : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  have hlogTwoQ : Real.log (2 : ℝ) ≤ Real.log (Q : ℝ) := by
    apply Real.log_le_log (by norm_num)
    exact_mod_cast hQ
  rw [logarithmicExponent, abs_div, abs_of_pos hlogQ]
  exact div_le_div_of_nonneg_left (abs_nonneg _) hlogTwo hlogTwoQ

/-- The base-`Q` exponent of a fixed positive multiplicative constant is
eventually arbitrarily small. -/
theorem exists_abs_logarithmicExponent_cutoff {a ε : ℝ}
    (ha : 0 < a) (hε : 0 < ε) :
    ∃ Q₀ : ℕ, ∀ Q, Q₀ ≤ Q → 2 ≤ Q →
      |logarithmicExponent Q a| ≤ ε := by
  have htendsto : Filter.Tendsto
      (fun Q : ℕ ↦ Real.log (Q : ℝ)) Filter.atTop Filter.atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hlarge : ∀ᶠ Q : ℕ in Filter.atTop,
      |Real.log a| / ε ≤ Real.log (Q : ℝ) :=
    htendsto.eventually (Filter.eventually_ge_atTop (|Real.log a| / ε))
  rw [Filter.eventually_atTop] at hlarge
  obtain ⟨Q₀, hQ₀⟩ := hlarge
  refine ⟨Q₀, ?_⟩
  intro Q hQ hQtwo
  have hlogQ : 0 < Real.log (Q : ℝ) :=
    Real.log_pos (by exact_mod_cast (lt_of_lt_of_le (by omega : 1 < 2) hQtwo))
  rw [logarithmicExponent, abs_div, abs_of_pos hlogQ]
  apply (div_le_iff₀ hlogQ).2
  calc
    |Real.log a| = ε * (|Real.log a| / ε) := by
      field_simp
    _ ≤ ε * Real.log (Q : ℝ) :=
      mul_le_mul_of_nonneg_left (hQ₀ Q hQ) hε.le

/-- At the real place, the logarithmic minimum contributes its base-`Q`
exponent; at the two finite places adelic dilation contributes no exponent. -/
noncomputable def minimaLocalConstants {n : ℕ} (Q : ℕ)
    (lambda : Fin n → ℝ) : HeightBoxes.LocalConstants n :=
  fun place i ↦
    if place = Place23.infinite then logarithmicExponent Q (lambda i) else 0

theorem exponentRadius_minimaLocalConstants {n Q : ℕ} (hQ : 1 < Q)
    {lambda : Fin n → ℝ} (hlambda : ∀ i, 0 < lambda i)
    (place : Place23) (i : Fin n) :
    exponentRadius (Q : ℝ) (minimaLocalConstants Q lambda) place i =
      AdelicMinima.placeScale place (lambda i) := by
  by_cases hv : place = Place23.infinite
  · subst place
    simp only [minimaLocalConstants, if_pos, exponentRadius,
      AdelicMinima.placeScale_infinite]
    exact rpow_logarithmicExponent hQ (hlambda i)
  · simp [minimaLocalConstants, hv, exponentRadius,
      AdelicMinima.placeScale]

theorem sum_minimaLocalConstants {n Q : ℕ} (lambda : Fin n → ℝ) :
    (∑ place, ∑ i, minimaLocalConstants Q lambda place i) =
      ∑ i, logarithmicExponent Q (lambda i) := by
  simp [minimaLocalConstants, Fin.sum_univ_succ, Place23.infinite]

theorem sum_logarithmicExponent_eq_product {n Q : ℕ}
    (lambda : Fin n → ℝ) (hlambda : ∀ i, 0 < lambda i) :
    (∑ i, logarithmicExponent Q (lambda i)) =
      logarithmicExponent Q (∏ i, lambda i) := by
  simp only [logarithmicExponent]
  rw [Real.log_prod (fun i _ ↦ (hlambda i).ne')]
  exact (Finset.sum_div _ _ _).symm

theorem sum_minimaLocalConstants_eq_product {n Q : ℕ}
    (lambda : Fin n → ℝ) (hlambda : ∀ i, 0 < lambda i) :
    (∑ place, ∑ i, minimaLocalConstants Q lambda place i) =
      logarithmicExponent Q (∏ i, lambda i) := by
  rw [sum_minimaLocalConstants, sum_logarithmicExponent_eq_product lambda hlambda]

/-- The upper half of the adelic minima product estimate cancels the
original total exponent, leaving only the base-`Q` logarithm of its fixed
constant.  This is the exact cancellation used in the exterior exponent
sum. -/
theorem sum_original_add_minimaLocalConstants_le_fixedLog
    {n Q : ℕ} (hQ : 1 < Q)
    (c : HeightBoxes.LocalConstants n) (lambda : Fin n → ℝ)
    (hlambda : ∀ i, 0 < lambda i) {C : ℝ} (hC : 0 < C)
    (hprod : ∏ i, lambda i ≤
      C * (Q : ℝ) ^ (-(∑ place, ∑ i, c place i))) :
    (∑ place, ∑ i, c place i) +
        ∑ place, ∑ i, minimaLocalConstants Q lambda place i ≤
      logarithmicExponent Q C := by
  let s : ℝ := ∑ place, ∑ i, c place i
  have hprodPos : 0 < ∏ i, lambda i :=
    Finset.prod_pos fun i _ ↦ hlambda i
  have hpowPos : 0 < (Q : ℝ) ^ (-s) := by positivity
  have hlog : logarithmicExponent Q (∏ i, lambda i) ≤
      logarithmicExponent Q (C * (Q : ℝ) ^ (-s)) :=
    logarithmicExponent_mono hQ hprodPos (by simpa only [s] using hprod)
  rw [logarithmicExponent_mul hC hpowPos,
    logarithmicExponent_rpow hQ] at hlog
  rw [sum_minimaLocalConstants_eq_product lambda hlambda]
  change s + logarithmicExponent Q (∏ i, lambda i) ≤ _
  linarith

/-- The saving exponent attached to the distinguished exterior coordinate.
It occurs only at the real place. -/
noncomputable def gapSavingLocalConstant (Q : ℕ) (saving : ℝ) :
    Place23 → ℝ :=
  fun place ↦
    if place = Place23.infinite then logarithmicExponent Q saving else 0

theorem rpow_gapSavingLocalConstant {Q : ℕ} (hQ : 1 < Q)
    {saving : ℝ} (hsaving : 0 < saving) (place : Place23) :
    (Q : ℝ) ^ gapSavingLocalConstant Q saving place =
      if place = Place23.infinite then saving else 1 := by
  by_cases hv : place = Place23.infinite
  · subst place
    simp only [gapSavingLocalConstant, if_pos]
    exact rpow_logarithmicExponent hQ hsaving
  · simp [gapSavingLocalConstant, hv]

theorem sum_gapSavingLocalConstant (Q : ℕ) (saving : ℝ) :
    ∑ place, gapSavingLocalConstant Q saving place =
      logarithmicExponent Q saving := by
  simp [gapSavingLocalConstant, Fin.sum_univ_succ, Place23.infinite]

theorem sum_gapSavingLocalConstant_le_of_ratio_le_rpow
    {Q : ℕ} (hQ : 1 < Q) {saving a : ℝ} (hsaving : 0 < saving)
    (hratio : saving ≤ (Q : ℝ) ^ (-a)) :
    ∑ place, gapSavingLocalConstant Q saving place ≤ -a := by
  rw [sum_gapSavingLocalConstant]
  calc
    logarithmicExponent Q saving ≤
        logarithmicExponent Q ((Q : ℝ) ^ (-a)) :=
      logarithmicExponent_mono hQ hsaving hratio
    _ = -a := logarithmicExponent_rpow hQ (-a)

/-- In original dimension at most five, the rank-tail pigeonhole exponent
is uniformly at least `3/200`.  This is the numerical margin used after the
last-minimum lower bound with original exponent sum at most `-3/4`. -/
theorem three_over_two_hundred_le_rank_tailExponent
    {n R : ℕ} (hn2 : 2 ≤ n) (hn5 : n ≤ 5)
    (hRpos : 0 < R) (hRlt : R < n) :
    (3 / 200 : ℝ) ≤ (3 / 4 : ℝ) / (2 * n) / (n - R : ℕ) := by
  interval_cases n <;> interval_cases R <;> norm_num at *

/-- A fixed positive local loss is recorded once in every exterior row. -/
noncomputable def lossLocalConstant (Q : ℕ) (loss : Place23 → ℝ) :
    Place23 → ℝ :=
  fun place ↦ logarithmicExponent Q (loss place)

theorem rpow_lossLocalConstant {Q : ℕ} (hQ : 1 < Q)
    {loss : Place23 → ℝ} (hloss : ∀ place, 0 < loss place)
    (place : Place23) :
    (Q : ℝ) ^ lossLocalConstant Q loss place = loss place := by
  exact rpow_logarithmicExponent hQ (hloss place)

theorem sum_lossLocalConstant_eq_product (Q : ℕ)
    (loss : Place23 → ℝ) (hloss : ∀ place, 0 < loss place) :
    ∑ place, lossLocalConstant Q loss place =
      logarithmicExponent Q (∏ place, loss place) := by
  exact sum_logarithmicExponent_eq_product loss hloss

/-- The two fixed contributions in the exterior exponent sum—the upper
minima-product constant and the determinant/Evertse losses—are together the
base-`Q` exponent of one fixed positive factor. -/
theorem fixedExteriorExponent_eq_logarithmicExponent
    (Q m d : ℕ) {C : ℝ} (hC : 0 < C)
    (loss : Place23 → ℝ) (hloss : ∀ place, 0 < loss place) :
    m * logarithmicExponent Q C +
        d * ∑ place, lossLocalConstant Q loss place =
      logarithmicExponent Q
        (C ^ m * (∏ place, loss place) ^ d) := by
  rw [sum_lossLocalConstant_eq_product Q loss hloss,
    logarithmicExponent_mul (pow_pos hC m)
      (pow_pos (Finset.prod_pos fun place _ ↦ hloss place) d),
    logarithmicExponent_pow, logarithmicExponent_pow]

theorem exists_fixedExteriorExponent_cutoff
    (m d : ℕ) {C : ℝ} (hC : 0 < C)
    (loss : Place23 → ℝ) (hloss : ∀ place, 0 < loss place)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ Q₀ : ℕ, ∀ Q, Q₀ ≤ Q → 2 ≤ Q →
      |m * logarithmicExponent Q C +
        d * ∑ place, lossLocalConstant Q loss place| ≤ ε := by
  have hfactor : 0 < C ^ m * (∏ place, loss place) ^ d :=
    mul_pos (pow_pos hC m)
      (pow_pos (Finset.prod_pos fun place _ ↦ hloss place) d)
  obtain ⟨Q₀, hQ₀⟩ := exists_abs_logarithmicExponent_cutoff hfactor hε
  refine ⟨Q₀, ?_⟩
  intro Q hQ hQtwo
  rw [fixedExteriorExponent_eq_logarithmicExponent Q m d hC loss hloss]
  exact hQ₀ Q hQ hQtwo

/-- The complete forms-dependent multiplicative loss in exterior degree
`q`.  It is independent of the height `Q` and of the chosen point. -/
noncomputable def fixedRankTailFactor {n : ℕ}
    (q : ℕ) (L : Place23 → Fin n → RatLinearForm n)
    (hL : IsNonsingularFamily L) : ℝ :=
  (AdelicMinimaUpper.upperConstant L) ^ ((n - 1).choose (q - 1)) *
    (∏ place,
      (Nat.factorial q : ℝ) *
        (ExteriorWedgeBounds.fixedWeightedEvertseCoefficient L hL place) ^ q) ^
      (n.choose q)

theorem fixedRankTailFactor_pos {n : ℕ}
    (q : ℕ) (L : Place23 → Fin n → RatLinearForm n)
    (hL : IsNonsingularFamily L) : 0 < fixedRankTailFactor q L hL := by
  unfold fixedRankTailFactor
  apply mul_pos
  · exact pow_pos (AdelicMinimaUpper.upperConstant_pos L hL) _
  · apply pow_pos
    apply Finset.prod_pos
    intro place _
    apply mul_pos
    · positivity
    · apply pow_pos
      unfold ExteriorWedgeBounds.fixedWeightedEvertseCoefficient
      apply mul_pos
      · exact zero_lt_one.trans_le
          (WeightedEvertseBasis.one_le_rowApproxFactor place)
      · split_ifs
        · exact zero_lt_one.trans_le
            (ExteriorWedgeBounds.one_le_weightedEvertseConstant L hL)
        · positivity

/-- The fixed term in the rank-tail exponent sum is the base-`Q`
logarithm of `fixedRankTailFactor`. -/
theorem fixedRankTailBudget_eq_logarithmicExponent
    {n Q : ℕ} (q : ℕ)
    (L : Place23 → Fin n → RatLinearForm n)
    (hL : IsNonsingularFamily L) :
    (n - 1).choose (q - 1) *
          ExteriorWedgeBounds.logBase (Q : ℝ)
            (AdelicMinimaUpper.upperConstant L) +
        n.choose q * ∑ place,
          ExteriorWedgeBounds.fixedWeightedDeterminantConstant
            (q := q) (Q : ℝ) L hL place =
      logarithmicExponent Q (fixedRankTailFactor q L hL) := by
  let loss : Place23 → ℝ := fun place ↦
    (Nat.factorial q : ℝ) *
      (ExteriorWedgeBounds.fixedWeightedEvertseCoefficient L hL place) ^ q
  have hloss : ∀ place, 0 < loss place := by
    intro place
    dsimp only [loss]
    apply mul_pos
    · positivity
    · apply pow_pos
      unfold ExteriorWedgeBounds.fixedWeightedEvertseCoefficient
      apply mul_pos
      · exact zero_lt_one.trans_le
          (WeightedEvertseBasis.one_le_rowApproxFactor place)
      · split_ifs
        · exact zero_lt_one.trans_le
            (ExteriorWedgeBounds.one_le_weightedEvertseConstant L hL)
        · positivity
  have h := fixedExteriorExponent_eq_logarithmicExponent Q
    ((n - 1).choose (q - 1)) (n.choose q)
    (AdelicMinimaUpper.upperConstant_pos L hL) loss hloss
  simpa only [ExteriorWedgeBounds.logBase, logarithmicExponent,
    lossLocalConstant, ExteriorWedgeBounds.fixedWeightedDeterminantConstant,
    loss, fixedRankTailFactor] using h

/-- For fixed exterior degree, all determinant and triangular-basis losses
consume at most `1/200` of exponent once `Q` is large. -/
theorem exists_fixedRankTailBudget_cutoff {n : ℕ}
    (q : ℕ) (L : Place23 → Fin n → RatLinearForm n)
    (hL : IsNonsingularFamily L) :
    ∃ Q₀ : ℕ, ∀ Q, Q₀ ≤ Q → 2 ≤ Q →
      |(n - 1).choose (q - 1) *
            ExteriorWedgeBounds.logBase (Q : ℝ)
              (AdelicMinimaUpper.upperConstant L) +
          n.choose q * ∑ place,
            ExteriorWedgeBounds.fixedWeightedDeterminantConstant
              (q := q) (Q : ℝ) L hL place| ≤ (1 / 200 : ℝ) := by
  obtain ⟨Q₀, hQ₀⟩ := exists_abs_logarithmicExponent_cutoff
    (fixedRankTailFactor_pos q L hL) (by norm_num : (0 : ℝ) < 1 / 200)
  refine ⟨Q₀, ?_⟩
  intro Q hQ hQtwo
  rw [fixedRankTailBudget_eq_logarithmicExponent q L hL]
  exact hQ₀ Q hQ hQtwo

/-- A single forms-dependent bound for the absolute logarithms of all
determinant constants in degrees `q ≤ n`. -/
noncomputable def fixedDeterminantLogBound {n : ℕ}
    (L : Place23 → Fin n → RatLinearForm n)
    (hL : IsNonsingularFamily L) : ℝ :=
  ∑ q : Fin (n + 1), ∑ place,
    |Real.log ((Nat.factorial q.val : ℝ) *
      (ExteriorWedgeBounds.fixedWeightedEvertseCoefficient L hL place) ^
        q.val)| / Real.log 2

theorem fixedDeterminantLogBound_nonneg {n : ℕ}
    (L : Place23 → Fin n → RatLinearForm n)
    (hL : IsNonsingularFamily L) : 0 ≤ fixedDeterminantLogBound L hL := by
  unfold fixedDeterminantLogBound
  apply Finset.sum_nonneg
  intro q _
  apply Finset.sum_nonneg
  intro place _
  positivity

theorem abs_fixedWeightedDeterminantConstant_le {n q Q : ℕ}
    (hq : q ≤ n) (hQ : 2 ≤ Q)
    (L : Place23 → Fin n → RatLinearForm n)
    (hL : IsNonsingularFamily L) (place : Place23) :
    |ExteriorWedgeBounds.fixedWeightedDeterminantConstant
        (q := q) (Q : ℝ) L hL place| ≤
      fixedDeterminantLogBound L hL := by
  let qi : Fin (n + 1) := ⟨q, by omega⟩
  let factor : ℝ := (Nat.factorial q : ℝ) *
    (ExteriorWedgeBounds.fixedWeightedEvertseCoefficient L hL place) ^ q
  have hfactor : 0 < factor := by
    dsimp only [factor]
    apply mul_pos
    · positivity
    · apply pow_pos
      unfold ExteriorWedgeBounds.fixedWeightedEvertseCoefficient
      apply mul_pos
      · exact zero_lt_one.trans_le
          (WeightedEvertseBasis.one_le_rowApproxFactor place)
      · split_ifs
        · exact zero_lt_one.trans_le
            (ExteriorWedgeBounds.one_le_weightedEvertseConstant L hL)
        · positivity
  have hbase : |logarithmicExponent Q factor| ≤
      |Real.log factor| / Real.log 2 :=
    abs_logarithmicExponent_le_of_two_le hQ hfactor
  have hplace : |Real.log factor| / Real.log 2 ≤
      ∑ p : Place23,
        |Real.log ((Nat.factorial qi.val : ℝ) *
          (ExteriorWedgeBounds.fixedWeightedEvertseCoefficient L hL p) ^
            qi.val)| / Real.log 2 := by
    simpa [qi, factor] using
      (Finset.single_le_sum
        (s := Finset.univ)
        (f := fun p : Place23 ↦
          |Real.log ((Nat.factorial qi.val : ℝ) *
            (ExteriorWedgeBounds.fixedWeightedEvertseCoefficient L hL p) ^
              qi.val)| / Real.log 2)
        (fun p _ ↦ by positivity) (Finset.mem_univ place))
  have hqsum :
      (∑ p : Place23,
        |Real.log ((Nat.factorial qi.val : ℝ) *
          (ExteriorWedgeBounds.fixedWeightedEvertseCoefficient L hL p) ^
            qi.val)| / Real.log 2) ≤ fixedDeterminantLogBound L hL := by
    unfold fixedDeterminantLogBound
    exact Finset.single_le_sum
      (s := Finset.univ)
      (f := fun q' : Fin (n + 1) ↦
        ∑ p : Place23,
          |Real.log ((Nat.factorial q'.val : ℝ) *
            (ExteriorWedgeBounds.fixedWeightedEvertseCoefficient L hL p) ^
              q'.val)| / Real.log 2)
      (fun q' _ ↦ Finset.sum_nonneg fun p _ ↦ by positivity)
      (Finset.mem_univ qi)
  change |logarithmicExponent Q factor| ≤ _
  exact hbase.trans (hplace.trans hqsum)

theorem abs_certificateMinimaLog_le_logarithmicBound
    {n Q : ℕ}
    (L : AdelicMinima.LocalForms n) (hL : IsNonsingularFamily L)
    (hQ : 2 ≤ Q) (c : HeightBoxes.LocalConstants n)
    (hc : ∀ place i, c place i ∈ Set.Icc (-5 : ℝ) 3)
    (A : AdelicMinimaUpper.UpperAdaptedBasisCertificate L Q c
      (AdelicMinimaUpper.upperConstant L)) (place : Place23) (i : Fin n) :
    |ExteriorWedgeBounds.certificateMinimaLog (Q : ℝ)
      (ExteriorWedgeBounds.OrderedMinimaData.ofAdaptedBasisCertificate
        A.toAdaptedBasisCertificate) place i| ≤
      AdelicMinimaLogBounds.logarithmicBound L := by
  by_cases hv : place = Place23.infinite
  · subst place
    have hi := AdelicMinimaLogBounds.logarithmicExponent_mem_Icc
      hL hQ hc A i
    rw [abs_le]
    simpa [ExteriorWedgeBounds.certificateMinimaLog,
      ExteriorWedgeBounds.logBase,
      ExteriorWedgeBounds.OrderedMinimaData.ofAdaptedBasisCertificate,
      AdelicMinimaLogBounds.logarithmicExponent] using hi
  · simp [ExteriorWedgeBounds.certificateMinimaLog, hv,
      AdelicMinimaLogBounds.logarithmicBound_nonneg L]

theorem abs_splitGapSaving_le_two_logarithmicBound
    {n Q : ℕ}
    (L : AdelicMinima.LocalForms n) (hQ : 2 ≤ Q)
    (B : ExteriorWedgeBounds.OrderedMinimaData n)
    (kappa : Fin n) (hkappa : 0 < kappa.val)
    (hlog : ∀ i,
      |ExteriorWedgeBounds.logBase (Q : ℝ) (B.lambda i)| ≤
        AdelicMinimaLogBounds.logarithmicBound L)
    (place : Place23) :
    |ExteriorWedgeBounds.splitGapSaving (Q : ℝ)
      B kappa hkappa place| ≤
      2 * AdelicMinimaLogBounds.logarithmicBound L := by
  by_cases hv : place = Place23.infinite
  · subst place
    rw [ExteriorWedgeBounds.splitGapSaving, if_pos rfl,
      ExteriorWedgeBounds.distinguishedRatio, ExteriorWedgeBounds.logBase,
      Real.log_div (B.lambda_pos _).ne' (B.lambda_pos _).ne']
    have heq :
        (Real.log (B.lambda (ExteriorWedgeBounds.splitPredecessor kappa hkappa)) -
          Real.log (B.lambda kappa)) / Real.log (Q : ℝ) =
        ExteriorWedgeBounds.logBase (Q : ℝ)
            (B.lambda (ExteriorWedgeBounds.splitPredecessor kappa hkappa)) -
          ExteriorWedgeBounds.logBase (Q : ℝ) (B.lambda kappa) := by
      unfold ExteriorWedgeBounds.logBase
      ring
    rw [heq]
    calc
      _ ≤ |ExteriorWedgeBounds.logBase (Q : ℝ)
              (B.lambda (ExteriorWedgeBounds.splitPredecessor kappa hkappa))| +
            |ExteriorWedgeBounds.logBase (Q : ℝ) (B.lambda kappa)| :=
        abs_sub _ _
      _ ≤ AdelicMinimaLogBounds.logarithmicBound L +
          AdelicMinimaLogBounds.logarithmicBound L :=
        add_le_add (hlog _) (hlog _)
      _ = 2 * AdelicMinimaLogBounds.logarithmicBound L := by ring
  · simp [ExteriorWedgeBounds.splitGapSaving, hv,
      AdelicMinimaLogBounds.logarithmicBound_nonneg L]

/-- The product upper bound, the rank-tail gap, and the fixed coefficient
budget leave a uniform negative raw exterior exponent in all original
dimensions at most five. -/
theorem sum_rankTailRaw_le_neg_one_hundred
    {n Q : ℕ} (hn2 : 2 ≤ n) (hn5 : n ≤ 5)
    (L : AdelicMinima.LocalForms n) (hL : IsNonsingularFamily L)
    (hQ : 2 ≤ Q) (c : HeightBoxes.LocalConstants n)
    (B₀ : AdelicMinima.AdaptedBasisCertificate L Q c)
    (hRpos : 0 < B₀.rank) (hRlt : B₀.rank < n)
    {ρ : Place23 → Fin n → ℝ}
    (E : ExteriorWedgeBounds.WeightedEvertseData L
      (ExteriorWedgeBounds.OrderedMinimaData.ofAdaptedBasisCertificate B₀) ρ)
    (hcoeff : E.coefficient =
      ExteriorWedgeBounds.fixedWeightedEvertseCoefficient L hL)
    (hprod : (∏ i, B₀.lambda i) ≤
      AdelicMinimaUpper.upperConstant L *
        (Q : ℝ) ^ (-∑ place, ∑ i, c place i))
    (hlast : (Q : ℝ) ^ ((3 / 4 : ℝ) / (2 * n)) ≤
      B₀.lambda ⟨n - 1, by omega⟩)
    (hfixed : |(n - 1).choose
          ((n - (ExteriorWedgeBounds.rankTailSelectedSplit
            hRpos hRlt B₀.lambda).val) - 1) *
          ExteriorWedgeBounds.logBase (Q : ℝ)
            (AdelicMinimaUpper.upperConstant L) +
        n.choose (n - (ExteriorWedgeBounds.rankTailSelectedSplit
            hRpos hRlt B₀.lambda).val) *
          ∑ place, ExteriorWedgeBounds.fixedWeightedDeterminantConstant
            (q := n - (ExteriorWedgeBounds.rankTailSelectedSplit
              hRpos hRlt B₀.lambda).val) (Q : ℝ) L hL place| ≤
        (1 / 200 : ℝ)) :
    (∑ place, ∑ i,
      ExteriorWedgeBounds.splitWeightedRawExteriorLocalConstants (Q : ℝ) c
        (ExteriorWedgeBounds.OrderedMinimaData.ofAdaptedBasisCertificate B₀) E
        (ExteriorWedgeBounds.rankTailSelectedSplit hRpos hRlt B₀.lambda)
        (ExteriorWedgeBounds.rankTailSelectedSplit_pos
          hRpos hRlt B₀.lambda) place i) ≤ -(1 / 100 : ℝ) := by
  have hraw :=
    ExteriorWedgeBounds.sum_adaptedRankTailRaw_le_of_product_and_last
      L hQ c B₀ hRpos hRlt E
      (AdelicMinimaUpper.upperConstant_pos L hL) hprod hlast
  have hdet := ExteriorWedgeBounds.weightedDeterminantConstant_eq_fixed
    (q := n - (ExteriorWedgeBounds.rankTailSelectedSplit
      hRpos hRlt B₀.lambda).val) hL (Q : ℝ) E hcoeff
  rw [hdet] at hraw
  have hfixedUpper :
      (n - 1).choose
          ((n - (ExteriorWedgeBounds.rankTailSelectedSplit
            hRpos hRlt B₀.lambda).val) - 1) *
          ExteriorWedgeBounds.logBase (Q : ℝ)
            (AdelicMinimaUpper.upperConstant L) +
        n.choose (n - (ExteriorWedgeBounds.rankTailSelectedSplit
            hRpos hRlt B₀.lambda).val) *
          ∑ place, ExteriorWedgeBounds.fixedWeightedDeterminantConstant
            (q := n - (ExteriorWedgeBounds.rankTailSelectedSplit
              hRpos hRlt B₀.lambda).val) (Q : ℝ) L hL place ≤
        (1 / 200 : ℝ) :=
    (le_abs_self _).trans hfixed
  have hgap := three_over_two_hundred_le_rank_tailExponent
    hn2 hn5 hRpos hRlt
  have hneg :
      (-(3 / 4 / (2 * (n : ℝ))) / ((n - B₀.rank : ℕ) : ℝ)) =
        -((3 / 4 : ℝ) / (2 * n) / (n - B₀.rank : ℕ)) := by
    ring
  rw [hneg] at hraw
  linarith

/-- The determinant expansion contributes `q!` and one copy of the local
weighted-Evertse loss in each of its `q` rows. -/
noncomputable def exteriorLoss (q : ℕ) (A : Place23 → ℝ) :
    Place23 → ℝ :=
  fun place ↦ (Nat.factorial q : ℝ) * (A place) ^ q

theorem exteriorLoss_pos {q : ℕ} {A : Place23 → ℝ}
    (hA : ∀ place, 0 < A place) (place : Place23) :
    0 < exteriorLoss q A place := by
  exact mul_pos (by positivity) (pow_pos (hA place) q)

open ExteriorEndpoint ExteriorWedgeBounds

/-- The complete weighted omitted-wedge radius is exactly the radius encoded
by the raw exterior exponent array.  Thus the later grid rounding really is
an enlargement of the concrete determinant domain, including the fixed
Evertse and factorial losses. -/
theorem weightedOmittedWedgeRowRadius_eq_exponentRadius
    {n Q : ℕ} (hQ : 1 < Q) (kappa : Fin n) (hkappa : 0 < kappa.val)
    (c : HeightBoxes.LocalConstants n)
    (pi : Place23 → Equiv.Perm (Fin n))
    (lambda : Fin n → ℝ) (hlambda : ∀ i, 0 < lambda i)
    (A : Place23 → ℝ) (hA : ∀ place, 0 < A place)
    (place : Place23)
    (I : Set.powersetCard (Fin n) (n - kappa.val)) :
    weightedOmittedWedgeRowRadius kappa hkappa
        (fun i ↦ AdelicMinima.placeScale place (lambda i))
        (fun i ↦ exponentRadius (Q : ℝ) c place (pi place i))
        (A place) I =
      exponentRadius (Q : ℝ)
        (weightedRawExteriorLocalConstants c
          (minimaLocalConstants Q lambda) pi
          (fun _ ↦ tailExteriorIndex kappa)
          (gapSavingLocalConstant Q
            (distinguishedRatio kappa hkappa lambda))
          (lossLocalConstant Q (exteriorLoss (n - kappa.val) A)))
        place (exteriorIndexEquivFin n (n - kappa.val) I) := by
  have hQr : 0 < (Q : ℝ) := by exact_mod_cast (Nat.zero_lt_of_lt hQ)
  simp only [exponentRadius]
  rw [weightedRawExteriorLocalConstants_eq]
  simp only [Equiv.symm_apply_apply]
  rw [Real.rpow_add hQr, Real.rpow_add hQr]
  rw [Real.rpow_sum_of_pos hQr]
  simp_rw [Real.rpow_add hQr]
  have hmu (i : Fin n) :
      (Q : ℝ) ^ minimaLocalConstants Q lambda place i =
        AdelicMinima.placeScale place (lambda i) := by
    exact exponentRadius_minimaLocalConstants hQ hlambda place i
  have hgap : 0 < distinguishedRatio kappa hkappa lambda := by
    exact div_pos (hlambda _) (hlambda _)
  have hratioPlace :
      distinguishedRatio kappa hkappa
          (fun i ↦ AdelicMinima.placeScale place (lambda i)) =
        if place = Place23.infinite then
          distinguishedRatio kappa hkappa lambda else 1 := by
    by_cases hv : place = Place23.infinite
    · subst place
      simp [AdelicMinima.placeScale]
    · simp [AdelicMinima.placeScale, hv, distinguishedRatio]
  have hsave :
      (Q : ℝ) ^
          (if I = tailExteriorIndex kappa then
            gapSavingLocalConstant Q
              (distinguishedRatio kappa hkappa lambda) place else 0) =
        if I = tailExteriorIndex kappa then
          distinguishedRatio kappa hkappa
            (fun i ↦ AdelicMinima.placeScale place (lambda i)) else 1 := by
    by_cases hI : I = tailExteriorIndex kappa
    · simp only [hI, if_pos]
      rw [hratioPlace]
      exact rpow_gapSavingLocalConstant hQ hgap place
    · simp [hI]
  have hloss :
      (Q : ℝ) ^ lossLocalConstant Q
          (exteriorLoss (n - kappa.val) A) place =
        exteriorLoss (n - kappa.val) A place :=
    rpow_lossLocalConstant hQ (exteriorLoss_pos hA) place
  simp_rw [hmu]
  rw [hsave, hloss]
  simp only [weightedOmittedWedgeRowRadius, exteriorLoss,
    Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ,
    Fintype.card_fin]
  ring

/-- Upward discretization enlarges the exact weighted omitted-wedge domain. -/
theorem weightedOmittedWedgeRowRadius_le_discretizedExponentRadius
    {n Q : ℕ} (hQ : 1 < Q) (kappa : Fin n) (hkappa : 0 < kappa.val)
    (c : HeightBoxes.LocalConstants n)
    (pi : Place23 → Equiv.Perm (Fin n))
    (lambda : Fin n → ℝ) (hlambda : ∀ i, 0 < lambda i)
    (A : Place23 → ℝ) (hA : ∀ place, 0 < A place)
    {gamma : ℝ} (hgamma : 0 < gamma)
    (place : Place23)
    (I : Set.powersetCard (Fin n) (n - kappa.val)) :
    weightedOmittedWedgeRowRadius kappa hkappa
        (fun i ↦ AdelicMinima.placeScale place (lambda i))
        (fun i ↦ exponentRadius (Q : ℝ) c place (pi place i))
        (A place) I ≤
      exponentRadius (Q : ℝ)
        (discretizedLocalConstants gamma
          (weightedRawExteriorLocalConstants c
            (minimaLocalConstants Q lambda) pi
            (fun _ ↦ tailExteriorIndex kappa)
            (gapSavingLocalConstant Q
              (distinguishedRatio kappa hkappa lambda))
            (lossLocalConstant Q (exteriorLoss (n - kappa.val) A))))
        place (exteriorIndexEquivFin n (n - kappa.val) I) := by
  rw [weightedOmittedWedgeRowRadius_eq_exponentRadius hQ kappa hkappa
    c pi lambda hlambda A hA place I]
  simp only [exponentRadius, discretizedLocalConstants]
  apply Real.rpow_le_rpow_of_exponent_le
  · exact_mod_cast (Nat.le_of_lt hQ)
  · exact le_discretizedExponent hgamma

/-- Exact exterior rank `D-1` is precisely membership of the resulting span
in the codimension-one family consumed by the dimension-generic
rank-stabilization theorem. -/
theorem realSApproximationSpan_mem_sCodimOne_of_rank_eq_pred
    {d Q : ℕ} (hd : 0 < d) (hQ : 2 ≤ Q)
    (L : Erdos407.RankDrop.LocalForms d)
    (c : HeightBoxes.LocalConstants d)
    (hrank : Erdos407.RankDrop.realSApproximationRank L Q c = d - 1) :
    Erdos407.RankDrop.realSApproximationSpan L Q c ∈
      Erdos407.RankDrop.sCodimOneApproximationSpaces L c := by
  refine ⟨Q, hQ, rfl, ?_⟩
  change Erdos407.RankDrop.realSApproximationRank L Q c + 1 = d
  rw [hrank]
  omega

/-- The omitted wedges give the lower rank bound, while the `S`-integral
determinant gap gives strict upper rank.  Together they put the exterior
span directly in the codimension-one stabilization family. -/
theorem realSApproximationSpan_mem_sCodimOne_of_pred_le_rank_lt
    {d Q : ℕ} (hd : 0 < d) (hQ : 2 ≤ Q)
    (L : Erdos407.RankDrop.LocalForms d)
    (c : HeightBoxes.LocalConstants d)
    (hlower : d - 1 ≤ Erdos407.RankDrop.realSApproximationRank L Q c)
    (hupper : Erdos407.RankDrop.realSApproximationRank L Q c < d) :
    Erdos407.RankDrop.realSApproximationSpan L Q c ∈
      Erdos407.RankDrop.sCodimOneApproximationSpaces L c := by
  apply realSApproximationSpan_mem_sCodimOne_of_rank_eq_pred hd hQ L c
  omega

/-! ## Packaging the weighted triangular basis with its exterior domain -/

/-- The placewise loss in the row-weighted Evertse basis lemma. -/
def weightedEvertseLoss (C : ℝ) (place : Place23) : ℝ :=
  WeightedEvertseBasis.rowApproxFactor place *
    if place = Place23.infinite then C else 1

theorem weightedEvertseLoss_pos {C : ℝ} (hC : 1 ≤ C) (place : Place23) :
    0 < weightedEvertseLoss C place := by
  unfold weightedEvertseLoss
  apply mul_pos
  · exact lt_of_lt_of_le zero_lt_one
      (WeightedEvertseBasis.one_le_rowApproxFactor place)
  · split_ifs
    · exact zero_lt_one.trans_le hC
    · exact zero_lt_one

/-- The raw exterior exponent array attached to one split of an ordered
minima basis. -/
noncomputable def weightedExteriorRawLocalConstants {n : ℕ}
    (Q : ℕ) (kappa : Fin n) (hkappa : 0 < kappa.val)
    (c : HeightBoxes.LocalConstants n) (lambda : Fin n → ℝ)
    (pi : Place23 → Equiv.Perm (Fin n)) (C : ℝ) :
    HeightBoxes.LocalConstants (n.choose (n - kappa.val)) :=
  weightedRawExteriorLocalConstants c
    (minimaLocalConstants Q lambda) pi
    (fun _ ↦ tailExteriorIndex kappa)
    (gapSavingLocalConstant Q (distinguishedRatio kappa hkappa lambda))
    (lossLocalConstant Q
      (exteriorLoss (n - kappa.val) (weightedEvertseLoss C)))

/-- Coordinatewise bounds for the four contributions to a weighted exterior
exponent give a uniform bound for the complete raw exponent.  This is the
finite-label bridge once the individual logarithmic minima have been placed
in a fixed interval. -/
theorem abs_weightedRawExteriorLocalConstants_le
    {n q : ℕ} (c ell : HeightBoxes.LocalConstants n)
    (pi : Place23 → Equiv.Perm (Fin n))
    (J₀ : Place23 → Set.powersetCard (Fin n) q)
    (saving constant : Place23 → ℝ) {C M S K : ℝ}
    (_hC : 0 ≤ C) (_hM : 0 ≤ M) (hS : 0 ≤ S) (_hK : 0 ≤ K)
    (hc : ∀ place i, |c place i| ≤ C)
    (hell : ∀ place i, |ell place i| ≤ M)
    (hsaving : ∀ place, |saving place| ≤ S)
    (hconstant : ∀ place, |constant place| ≤ K)
    (place : Place23) (i : Fin (n.choose q)) :
    |weightedRawExteriorLocalConstants c ell pi J₀ saving constant place i| ≤
      q * (C + M) + S + K := by
  rw [weightedRawExteriorLocalConstants_eq]
  let J := (exteriorIndexEquivFin n q).symm i
  let f : Fin q → ℝ := fun a ↦
    c place (pi place (Set.powersetCard.ofFinEmbEquiv.symm J a)) +
      ell place (Set.powersetCard.ofFinEmbEquiv.symm J a)
  have hf (a : Fin q) : |f a| ≤ C + M := by
    apply (abs_add_le _ _).trans
    exact add_le_add (hc _ _) (hell _ _)
  have hsum : |∑ a, f a| ≤ q * (C + M) := by
    calc
      |∑ a, f a| ≤ ∑ a, |f a| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _a : Fin q, (C + M) :=
        Finset.sum_le_sum fun a _ ↦ hf a
      _ = q * (C + M) := by simp; ring
  have hif : |if J = J₀ place then saving place else 0| ≤ S := by
    split_ifs
    · exact hsaving place
    · simpa using hS
  change |(∑ a, f a) + (if J = J₀ place then saving place else 0) +
      constant place| ≤ _
  calc
    _ ≤ |(∑ a, f a) + (if J = J₀ place then saving place else 0)| +
        |constant place| := abs_add_le _ _
    _ ≤ (|∑ a, f a| +
        |if J = J₀ place then saving place else 0|) +
          |constant place| := by
      gcongr
      exact abs_add_le _ _
    _ ≤ q * (C + M) + S + K := by
      gcongr
      exact hconstant place

/-- One symmetric interval, depending only on the original local forms,
contains every raw rank-tail exterior exponent in dimensions at most five. -/
noncomputable def rawExteriorLogBound {n : ℕ}
    (L : Place23 → Fin n → RatLinearForm n)
    (hL : IsNonsingularFamily L) : ℝ :=
  5 * (5 + AdelicMinimaLogBounds.logarithmicBound L) +
    2 * AdelicMinimaLogBounds.logarithmicBound L +
      fixedDeterminantLogBound L hL

theorem rawExteriorLogBound_nonneg {n : ℕ}
    (L : Place23 → Fin n → RatLinearForm n)
    (hL : IsNonsingularFamily L) : 0 ≤ rawExteriorLogBound L hL := by
  unfold rawExteriorLogBound
  have hM := AdelicMinimaLogBounds.logarithmicBound_nonneg L
  have hK := fixedDeterminantLogBound_nonneg L hL
  positivity

theorem abs_splitWeightedRawExteriorLocalConstants_le_rawBound
    {n Q : ℕ} (hn5 : n ≤ 5)
    (L : AdelicMinima.LocalForms n) (hL : IsNonsingularFamily L)
    (hQ : 2 ≤ Q) (c : HeightBoxes.LocalConstants n)
    (hc : ∀ place i, c place i ∈ Set.Icc (-5 : ℝ) 3)
    (A : AdelicMinimaUpper.UpperAdaptedBasisCertificate L Q c
      (AdelicMinimaUpper.upperConstant L))
    (E : ExteriorWedgeBounds.WeightedEvertseData L
      (ExteriorWedgeBounds.OrderedMinimaData.ofAdaptedBasisCertificate
        A.toAdaptedBasisCertificate)
      (fun place i ↦ HeightBoxes.exponentRadius (Q : ℝ) c place i))
    (hcoeff : E.coefficient =
      ExteriorWedgeBounds.fixedWeightedEvertseCoefficient L hL)
    (kappa : Fin n) (hkappa : 0 < kappa.val)
    (place : Place23) (i : Fin (n.choose (n - kappa.val))) :
    |ExteriorWedgeBounds.splitWeightedRawExteriorLocalConstants (Q : ℝ) c
      (ExteriorWedgeBounds.OrderedMinimaData.ofAdaptedBasisCertificate
        A.toAdaptedBasisCertificate) E kappa hkappa place i| ≤
      rawExteriorLogBound L hL := by
  let B := ExteriorWedgeBounds.OrderedMinimaData.ofAdaptedBasisCertificate
    A.toAdaptedBasisCertificate
  let M := AdelicMinimaLogBounds.logarithmicBound L
  let K := fixedDeterminantLogBound L hL
  have hM : 0 ≤ M := AdelicMinimaLogBounds.logarithmicBound_nonneg L
  have hK : 0 ≤ K := fixedDeterminantLogBound_nonneg L hL
  have hcabs : ∀ place i, |c place i| ≤ (5 : ℝ) := by
    intro place i
    rw [abs_le]
    have hi := hc place i
    constructor <;> linarith [hi.1, hi.2]
  have hell : ∀ place i,
      |ExteriorWedgeBounds.certificateMinimaLog (Q : ℝ) B place i| ≤ M := by
    intro place i
    exact abs_certificateMinimaLog_le_logarithmicBound
      L hL hQ c hc A place i
  have hlog : ∀ i,
      |ExteriorWedgeBounds.logBase (Q : ℝ) (B.lambda i)| ≤ M := by
    intro i
    have hi := AdelicMinimaLogBounds.logarithmicExponent_mem_Icc
      hL hQ hc A i
    rw [abs_le]
    simpa [B, ExteriorWedgeBounds.logBase,
      ExteriorWedgeBounds.OrderedMinimaData.ofAdaptedBasisCertificate,
      AdelicMinimaLogBounds.logarithmicExponent] using hi
  have hsave : ∀ place,
      |ExteriorWedgeBounds.splitGapSaving (Q : ℝ) B kappa hkappa place| ≤
        2 * M := by
    intro place
    exact abs_splitGapSaving_le_two_logarithmicBound
      L hQ B kappa hkappa hlog place
  have hdet : ExteriorWedgeBounds.weightedDeterminantConstant
      (q := n - kappa.val) (Q : ℝ) E =
      ExteriorWedgeBounds.fixedWeightedDeterminantConstant
        (q := n - kappa.val) (Q : ℝ) L hL :=
    ExteriorWedgeBounds.weightedDeterminantConstant_eq_fixed
      hL (Q : ℝ) E hcoeff
  have hconstant : ∀ place,
      |ExteriorWedgeBounds.weightedDeterminantConstant
        (q := n - kappa.val) (Q : ℝ) E place| ≤ K := by
    intro place
    rw [hdet]
    exact abs_fixedWeightedDeterminantConstant_le
      (Nat.sub_le n kappa.val) hQ L hL place
  have hraw := abs_weightedRawExteriorLocalConstants_le
    c (ExteriorWedgeBounds.certificateMinimaLog (Q : ℝ) B)
    E.permutation (fun _ ↦ tailExteriorIndex kappa)
    (ExteriorWedgeBounds.splitGapSaving (Q : ℝ) B kappa hkappa)
    (ExteriorWedgeBounds.weightedDeterminantConstant
      (q := n - kappa.val) (Q : ℝ) E)
    (C := 5) (M := M) (S := 2 * M) (K := K)
    (by norm_num) hM (by positivity) hK hcabs hell hsave hconstant place i
  change _ ≤ rawExteriorLogBound L hL
  refine hraw.trans ?_
  unfold rawExteriorLogBound
  have hq : ((n - kappa.val : ℕ) : ℝ) ≤ 5 := by
    exact_mod_cast (Nat.sub_le n kappa.val |>.trans hn5)
  dsimp only [M, K] at hq ⊢
  nlinarith

/-- A `3/200` adjacent-minimum saving, after absorbing all fixed factors in
`1/200`, leaves the uniform raw margin `-1/100`. -/
theorem sum_weightedRawExteriorLocalConstants_le_neg_one_hundred
    {n q Q : ℕ} (hq : 0 < q)
    (c ell : HeightBoxes.LocalConstants n)
    (pi : Place23 → Equiv.Perm (Fin n))
    (J₀ : Place23 → Set.powersetCard (Fin n) q)
    (saving constant : Place23 → ℝ) {C : ℝ}
    (hcancel : (∑ place, ∑ i, c place i) +
        (∑ place, ∑ i, ell place i) ≤ logarithmicExponent Q C)
    (hsaving : ∑ place, saving place ≤ -(3 / 200 : ℝ))
    (hfixed : |(n - 1).choose (q - 1) * logarithmicExponent Q C +
        n.choose q * ∑ place, constant place| ≤ (1 / 200 : ℝ)) :
    (∑ place, ∑ i,
      weightedRawExteriorLocalConstants c ell pi J₀ saving constant place i) ≤
      -(1 / 100 : ℝ) := by
  rw [sum_weightedRawExteriorLocalConstants hq]
  have hmult := mul_le_mul_of_nonneg_left hcancel
    (Nat.cast_nonneg ((n - 1).choose (q - 1)) :
      0 ≤ ((n - 1).choose (q - 1) : ℝ))
  have hfixedUpper :
      (n - 1).choose (q - 1) * logarithmicExponent Q C +
          n.choose q * ∑ place, constant place ≤ (1 / 200 : ℝ) :=
    (le_abs_self _).trans hfixed
  linarith

/-- The coordinatewise upward discretization of the raw exterior exponent
array. -/
noncomputable def weightedExteriorLocalConstants {n : ℕ}
    (Q : ℕ) (kappa : Fin n) (hkappa : 0 < kappa.val)
    (c : HeightBoxes.LocalConstants n) (lambda : Fin n → ℝ)
    (pi : Place23 → Equiv.Perm (Fin n)) (C gamma : ℝ) :
    HeightBoxes.LocalConstants (n.choose (n - kappa.val)) :=
  discretizedLocalConstants gamma
    (weightedExteriorRawLocalConstants Q kappa hkappa c lambda pi C)

/-- All algebraic and local-domain data produced by applying the weighted
Evertse basis lemma to a rank-adapted minima basis.  The prefix flag is
retained explicitly for the final Plücker recovery. -/
structure WeightedExteriorCertificate {n Q : ℕ}
    (L : Place23 → Fin n → RatLinearForm n)
    (hL : IsNonsingularFamily L)
    (c : HeightBoxes.LocalConstants n)
    (B : AdelicMinima.AdaptedBasisCertificate L Q c)
    (kappa : Fin n) (hkappa : 0 < kappa.val) where
  C : ℝ
  C_ge_one : 1 ≤ C
  change : Matrix (Fin n) (Fin n) ℚ
  change_triangular : EvertseBasis.IsUnitLowerTriangular change
  change_sIntegral : ∀ i j,
    AdelicMinkowski.InZOneSix (fun _ : Fin 1 ↦ change i j)
  pi : Place23 → Equiv.Perm (Fin n)
  transformedIndependent :
    LinearIndependent ℚ (EvertseBasis.transformBasis change B.point)
  transformedSIntegral : ∀ i,
    AdelicMinkowski.InZOneSix (EvertseBasis.transformBasis change B.point i)
  prefix_span :
    initialBasisSpan (EvertseBasis.transformBasis change B.point)
        B.rank B.rank_le =
      Erdos407.RankDrop.realSApproximationSpan L Q c
  local_bound : ∀ place i j,
    realPlaceNorm place
        (L place (pi place i)
          (EvertseBasis.transformBasis change B.point j)) ≤
      weightedEvertseLoss C place *
        exponentRadius (Q : ℝ) c place (pi place i) *
          min (AdelicMinima.placeScale place (B.lambda i))
            (AdelicMinima.placeScale place (B.lambda j))
  omitted_mem : ∀ {gamma : ℝ}, 0 < gamma →
    ∀ J : OmittedExteriorIndex (tailExteriorIndex kappa),
      finExteriorBasisWedge
          (EvertseBasis.transformBasis change B.point) J.1 ∈
        Erdos407.RankDrop.realSIntegralApproximationDomain
          (exteriorLocalForms (permutedLocalForms L pi)
            (permutedLocalForms_nonsingular hL pi)
            (n - kappa.val)) Q
          (weightedExteriorLocalConstants Q kappa hkappa c B.lambda pi C gamma)

theorem exists_weightedExteriorCertificate {n Q : ℕ} (hQ : 1 < Q)
    (L : Place23 → Fin n → RatLinearForm n)
    (hL : IsNonsingularFamily L) (c : HeightBoxes.LocalConstants n)
    (B : AdelicMinima.AdaptedBasisCertificate L Q c)
    (kappa : Fin n) (hkappa : 0 < kappa.val) :
    Nonempty (WeightedExteriorCertificate L hL c B kappa hkappa) := by
  let rho : Place23 → Fin n → ℝ :=
    fun place i ↦ exponentRadius (Q : ℝ) c place i
  let mu : Place23 → Fin n → ℝ :=
    fun place i ↦ AdelicMinima.placeScale place (B.lambda i)
  have hQr : 0 < (Q : ℝ) := by exact_mod_cast (Nat.zero_lt_of_lt hQ)
  have hrho : ∀ place i, 0 < rho place i := by
    intro place i
    exact Real.rpow_pos_of_pos hQr _
  have hmu : ∀ place i, 0 < mu place i := by
    intro place i
    by_cases hv : place = Place23.infinite
    · subst place
      simpa [mu] using B.lambda_pos i
    · simp [mu, AdelicMinima.placeScale, hv]
  have hmuMono : ∀ place, Monotone (mu place) := by
    intro place
    by_cases hv : place = Place23.infinite
    · subst place
      simpa [mu] using B.lambda_mono
    · simp only [mu, AdelicMinima.placeScale, if_neg hv]
      exact fun _ _ _ ↦ le_rfl
  have hbound : ∀ place i j,
      realPlaceNorm place (L place i (B.point j)) ≤
        rho place i * mu place j := by
    intro place i j
    simpa only [rho, mu, mul_comm] using B.local_bound j place i
  obtain ⟨C, hC, hweighted⟩ :=
    WeightedEvertseBasis.exists_weightedEvertseBasis L hL
  obtain ⟨T, hTtri, hTS, hvLI, hvS, pi, hentry⟩ :=
    hweighted B.point rho mu B.independent B.sIntegral hrho hmu hmuMono hbound
  refine ⟨{
    C := C
    C_ge_one := hC
    change := T
    change_triangular := hTtri
    change_sIntegral := hTS
    pi := pi
    transformedIndependent := hvLI
    transformedSIntegral := hvS
    prefix_span := ?_
    local_bound := ?_
    omitted_mem := ?_ }⟩
  · rw [initialBasisSpan_evertseTransform_eq hTtri B.independent]
    simpa [initialBasisSpan, Function.comp_def] using B.prefix_span
  · intro place i j
    simpa only [weightedEvertseLoss, rho, mu] using hentry place i j
  · intro gamma hgamma
    let rho' : Place23 → Fin n → ℝ :=
      fun place i ↦ exponentRadius (Q : ℝ) c place (pi place i)
    let Aloss : Place23 → ℝ := weightedEvertseLoss C
    have hAloss : ∀ place, 0 < Aloss place :=
      fun place ↦ weightedEvertseLoss_pos hC place
    have hrho' : ∀ place i, 0 < rho' place i := by
      intro place i
      exact Real.rpow_pos_of_pos hQr _
    refine omittedWedges_mem_realSIntegralApproximationDomain_weighted
      kappa hkappa L hL pi (EvertseBasis.transformBasis T B.point) hvS
      mu rho' Aloss (fun place ↦ (hAloss place).le)
      (fun place i ↦ (hrho' place i).le) hmu hmuMono ?_
      Q (weightedExteriorLocalConstants Q kappa hkappa c B.lambda pi C gamma) ?_
    · intro place i j
      simpa only [Aloss, rho', rho, mu, weightedEvertseLoss,
        permutedLocalForms] using hentry place i j
    · intro place I
      simpa only [weightedExteriorLocalConstants,
        weightedExteriorRawLocalConstants, Aloss, rho', mu] using
        weightedOmittedWedgeRowRadius_le_discretizedExponentRadius
          hQ kappa hkappa c pi B.lambda B.lambda_pos
            (weightedEvertseLoss C) (weightedEvertseLoss_pos hC)
            hgamma place I

/-! ## Finite labels for the varying exterior exponents -/

/-- A finite simultaneous label for exterior exponents known to lie in a
fixed interval. -/
abbrev ExteriorExponentLabel (d : ℕ) (gamma lo hi : ℝ) :=
  Place23 → Fin d → HeightBoxes.BoundedLogBox gamma lo hi

/-- A single mesh works for every exterior dimension arising from an
original dimension at most five (`d ≤ 10`). -/
noncomputable def exteriorBoxingMesh : ℝ := 1 / 10000

theorem exteriorBoxingMesh_pos : 0 < exteriorBoxingMesh := by
  norm_num [exteriorBoxingMesh]

noncomputable def exteriorExponentLabelOf {d : ℕ} {gamma lo hi : ℝ}
    (hgamma : 0 < gamma) (a : HeightBoxes.LocalConstants d)
    (ha : ∀ place i, a place i ∈ Set.Icc lo hi) :
    ExteriorExponentLabel d gamma lo hi :=
  fun place i ↦ HeightBoxes.boundedLogBoxOf hgamma (ha place i)

/-- The fixed upper endpoint attached to a finite exterior exponent label. -/
noncomputable def exteriorLabelUpperConstants {d : ℕ} {gamma lo hi : ℝ}
    (b : ExteriorExponentLabel d gamma lo hi) :
    HeightBoxes.LocalConstants d :=
  fun place i ↦ (((b place i).1 : ℝ) + 1) * gamma

theorem exteriorExponent_lt_labelUpper {d : ℕ} {gamma lo hi : ℝ}
    (hgamma : 0 < gamma) (a : HeightBoxes.LocalConstants d)
    (ha : ∀ place i, a place i ∈ Set.Icc lo hi)
    (place : Place23) (i : Fin d) :
    a place i < exteriorLabelUpperConstants
      (exteriorExponentLabelOf hgamma a ha) place i := by
  change a place i <
    (((HeightBoxes.logBoxIndex gamma (a place i) : ℝ) + 1) * gamma)
  exact HeightBoxes.logBoxIndex_upper hgamma

theorem exteriorLabelUpper_le_exponent_add {d : ℕ}
    {gamma lo hi : ℝ} (hgamma : 0 < gamma)
    (a : HeightBoxes.LocalConstants d)
    (ha : ∀ place i, a place i ∈ Set.Icc lo hi)
    (place : Place23) (i : Fin d) :
    exteriorLabelUpperConstants (exteriorExponentLabelOf hgamma a ha) place i
      ≤ a place i + gamma := by
  have hlo := HeightBoxes.logBoxIndex_lower
    (t := a place i) hgamma
  change ((((HeightBoxes.logBoxIndex gamma (a place i) : ℝ) + 1) * gamma) ≤
    a place i + gamma)
  rw [add_mul, one_mul]
  simpa [add_comm] using add_le_add_right hlo gamma

/-- The finite-label upper endpoint also dominates the integer-ceiling
discretization used by the wedge layer.  Thus its witnesses can be moved
into a genuinely finite family of exterior domains without changing them. -/
theorem discretizedExponent_le_exteriorLabelUpper
    {gamma lo hi a : ℝ} (hgamma : 0 < gamma)
    (ha : a ∈ Set.Icc lo hi) :
    discretizedExponent gamma a ≤
      (((exteriorExponentLabelOf (d := 1) hgamma
          (fun _ _ ↦ a) (fun _ _ ↦ ha) Place23.infinite 0).1 : ℝ) + 1) *
        gamma := by
  change gamma * (⌈a / gamma⌉ : ℤ) ≤
    (((⌊a / gamma⌋ : ℤ) : ℝ) + 1) * gamma
  have hceil : ⌈a / gamma⌉ ≤ ⌊a / gamma⌋ + 1 := by
    rw [Int.ceil_le]
    simpa using (Int.lt_floor_add_one (a / gamma)).le
  have hcast : ((⌈a / gamma⌉ : ℤ) : ℝ) ≤
      (((⌊a / gamma⌋ : ℤ) + 1 : ℤ) : ℝ) := by
    exact_mod_cast hceil
  rw [Int.cast_add, Int.cast_one] at hcast
  nlinarith

theorem discretizedLocalConstants_le_exteriorLabelUpper
    {d : ℕ} {gamma lo hi : ℝ} (hgamma : 0 < gamma)
    (a : HeightBoxes.LocalConstants d)
    (ha : ∀ place i, a place i ∈ Set.Icc lo hi) :
    ∀ place i, discretizedLocalConstants gamma a place i ≤
      exteriorLabelUpperConstants
        (exteriorExponentLabelOf hgamma a ha) place i := by
  intro place i
  change gamma * (⌈a place i / gamma⌉ : ℤ) ≤
    (((⌊a place i / gamma⌋ : ℤ) : ℝ) + 1) * gamma
  have hceil : ⌈a place i / gamma⌉ ≤
      ⌊a place i / gamma⌋ + 1 := by
    rw [Int.ceil_le]
    simpa using (Int.lt_floor_add_one (a place i / gamma)).le
  have hcast : ((⌈a place i / gamma⌉ : ℤ) : ℝ) ≤
      (((⌊a place i / gamma⌋ : ℤ) + 1 : ℤ) : ℝ) := by
    exact_mod_cast hceil
  rw [Int.cast_add, Int.cast_one] at hcast
  nlinarith

theorem mem_labelUpper_of_mem_discretized
    {d Q : ℕ} (hQ : 1 < Q)
    {L : Place23 → Fin d → RatLinearForm d}
    {gamma lo hi : ℝ} (hgamma : 0 < gamma)
    (a : HeightBoxes.LocalConstants d)
    (ha : ∀ place i, a place i ∈ Set.Icc lo hi)
    {x : Fin d → ℚ}
    (hx : x ∈ Erdos407.RankDrop.realSIntegralApproximationDomain L Q
      (discretizedLocalConstants gamma a)) :
    x ∈ Erdos407.RankDrop.realSIntegralApproximationDomain L Q
      (exteriorLabelUpperConstants
        (exteriorExponentLabelOf hgamma a ha)) := by
  refine ⟨hx.1, ?_⟩
  exact hx.2.mono (by exact_mod_cast hQ.le)
    (discretizedLocalConstants_le_exteriorLabelUpper hgamma a ha)

/-! ## The finite stabilization labels -/

abbrev GoodOriginalBoxLabel (n : ℕ) :=
  {b : ExteriorFiniteGlue.LocalBoxLabel n
      ExteriorFiniteGlue.originalBoxingMesh //
    (∑ place, ∑ i,
      ExteriorFiniteGlue.upperLocalConstants b place i) ≤ -(3 / 4 : ℝ)}

abbrev PositiveSplit (n : ℕ) := {kappa : Fin n // 0 < kappa.val}

abbrev GoodExteriorExponentLabel {n : ℕ}
    (L : Place23 → Fin n → RatLinearForm n)
    (hL : IsNonsingularFamily L) (kappa : PositiveSplit n) :=
  {b : ExteriorExponentLabel (n.choose (n - kappa.1.val))
      exteriorBoxingMesh (-rawExteriorLogBound L hL) (rawExteriorLogBound L hL) //
    (∑ place, ∑ i, exteriorLabelUpperConstants b place i) ≤
      -(1 / 1000 : ℝ)}

/-- A label fixes the exterior degree, Evertse row permutation, and the
rounded negative exponent array. -/
abbrev ExteriorStabilizationLabel {n : ℕ}
    (L : Place23 → Fin n → RatLinearForm n)
    (hL : IsNonsingularFamily L) :=
  Σ kappa : PositiveSplit n,
    (Place23 → Equiv.Perm (Fin n)) × GoodExteriorExponentLabel L hL kappa

def exteriorLabelDegree {n : ℕ}
    {L : Place23 → Fin n → RatLinearForm n}
    {hL : IsNonsingularFamily L}
    (a : ExteriorStabilizationLabel L hL) : ℕ := n - a.1.1.val

def exteriorLabelDimension {n : ℕ}
    {L : Place23 → Fin n → RatLinearForm n}
    {hL : IsNonsingularFamily L}
    (a : ExteriorStabilizationLabel L hL) : ℕ :=
  n.choose (exteriorLabelDegree a)

theorem exteriorLabelDegree_pos {n : ℕ}
    {L : Place23 → Fin n → RatLinearForm n}
    {hL : IsNonsingularFamily L}
    (a : ExteriorStabilizationLabel L hL) : 0 < exteriorLabelDegree a := by
  unfold exteriorLabelDegree
  exact Nat.sub_pos_of_lt a.1.1.isLt

theorem exteriorLabelDegree_lt {n : ℕ}
    {L : Place23 → Fin n → RatLinearForm n}
    {hL : IsNonsingularFamily L}
    (a : ExteriorStabilizationLabel L hL) : exteriorLabelDegree a < n := by
  unfold exteriorLabelDegree
  exact Nat.sub_lt (Nat.zero_lt_of_lt a.1.1.isLt) a.1.2

theorem exteriorLabelDimension_two_le {n : ℕ} (hn2 : 2 ≤ n)
    {L : Place23 → Fin n → RatLinearForm n}
    {hL : IsNonsingularFamily L}
    (a : ExteriorStabilizationLabel L hL) :
    2 ≤ exteriorLabelDimension a := by
  exact two_le_choose_of_pos_of_lt hn2
    (exteriorLabelDegree_pos a) (exteriorLabelDegree_lt a)

theorem exteriorLabelDimension_le_ten {n : ℕ} (hn5 : n ≤ 5)
    {L : Place23 → Fin n → RatLinearForm n}
    {hL : IsNonsingularFamily L}
    (a : ExteriorStabilizationLabel L hL) :
    exteriorLabelDimension a ≤ 10 := by
  exact choose_le_ten_of_le_five hn5 (exteriorLabelDegree a)

/-! ## Uniform cutoffs attached to finite labels -/

/-- The exterior form family belonging to a stabilization label. -/
noncomputable def labeledExteriorForms {n : ℕ}
    {L : Place23 → Fin n → RatLinearForm n}
    {hL : IsNonsingularFamily L}
    (a : ExteriorStabilizationLabel L hL) :
    Place23 → Fin (exteriorLabelDimension a) →
      RatLinearForm (exteriorLabelDimension a) :=
  exteriorLocalForms
    (permutedLocalForms L a.2.1)
    (permutedLocalForms_nonsingular hL a.2.1)
    (exteriorLabelDegree a)

theorem labeledExteriorForms_eq {n : ℕ}
    {L : Place23 → Fin n → RatLinearForm n}
    {hL : IsNonsingularFamily L}
    (a : ExteriorStabilizationLabel L hL) :
    labeledExteriorForms a =
      exteriorLocalForms
        (permutedLocalForms L a.2.1)
        (permutedLocalForms_nonsingular hL a.2.1)
        (exteriorLabelDegree a) := by
  unfold labeledExteriorForms
  congr 1

theorem labeledExteriorForms_nonsingular {n : ℕ}
    {L : Place23 → Fin n → RatLinearForm n}
    {hL : IsNonsingularFamily L}
    (a : ExteriorStabilizationLabel L hL) :
    IsNonsingularFamily (labeledExteriorForms a) := by
  exact exteriorLocalForms_nonsingular
    (permutedLocalForms L a.2.1)
    (permutedLocalForms_nonsingular hL a.2.1)
    (exteriorLabelDegree a)

/-- The labelled (rounded-up) exponent array in exterior coordinates. -/
noncomputable def labeledExteriorConstants {n : ℕ}
    {L : Place23 → Fin n → RatLinearForm n}
    {hL : IsNonsingularFamily L}
    (a : ExteriorStabilizationLabel L hL) :
    HeightBoxes.LocalConstants (exteriorLabelDimension a) :=
  exteriorLabelUpperConstants a.2.2.1

theorem sum_labeledExteriorConstants_le {n : ℕ}
    {L : Place23 → Fin n → RatLinearForm n}
    {hL : IsNonsingularFamily L}
    (a : ExteriorStabilizationLabel L hL) :
    (∑ place, ∑ i, labeledExteriorConstants a place i) ≤
      -(1 / 1000 : ℝ) := by
  exact a.2.2.2

/-- A concrete full-rank-exclusion cutoff for an original exponent label. -/
noncomputable def originalRankCutoff {n : ℕ}
    (L : Place23 → Fin n → RatLinearForm n)
    (hL : IsNonsingularFamily L) (b : GoodOriginalBoxLabel n) : ℕ :=
  Classical.choose (Erdos407.RankDrop.exists_sRankDeficient_cutoff
    L hL (ExteriorFiniteGlue.upperLocalConstants b.1)
    (by norm_num : (0 : ℝ) < 3 / 4) b.2)

theorem originalRankCutoff_spec {n : ℕ}
    (L : Place23 → Fin n → RatLinearForm n)
    (hL : IsNonsingularFamily L) (b : GoodOriginalBoxLabel n)
    {Q : ℕ} (hQ : originalRankCutoff L hL b ≤ Q) :
    Erdos407.RankDrop.realSApproximationRank L Q
      (ExteriorFiniteGlue.upperLocalConstants b.1) < n := by
  exact (Classical.choose_spec
    (Erdos407.RankDrop.exists_sRankDeficient_cutoff
      L hL (ExteriorFiniteGlue.upperLocalConstants b.1)
      (by norm_num : (0 : ℝ) < 3 / 4) b.2)) Q hQ

/-- A concrete cutoff for the lower bound on the last successive minimum. -/
noncomputable def lastMinimumCutoff {n : ℕ} (hn2 : 2 ≤ n)
    (L : Place23 → Fin n → RatLinearForm n)
    (hL : IsNonsingularFamily L) (b : GoodOriginalBoxLabel n) : ℕ := by
  letI : NeZero n := ⟨by omega⟩
  exact Classical.choose (AdelicMinima.exists_half_power_last_cutoff
    L hL (ExteriorFiniteGlue.upperLocalConstants b.1)
    (by norm_num : (0 : ℝ) < 3 / 4) b.2)

theorem lastMinimumCutoff_spec {n : ℕ} (hn2 : 2 ≤ n)
    (L : Place23 → Fin n → RatLinearForm n)
    (hL : IsNonsingularFamily L) (b : GoodOriginalBoxLabel n)
    {Q : ℕ} (hQ : lastMinimumCutoff hn2 L hL b ≤ Q)
    (x : Fin n → AdelicMinima.RatVector n) (lambda : Fin n → ℝ)
    (hx : LinearIndependent ℚ x)
    (hxS : ∀ j, AdelicMinkowski.InZOneSix (x j))
    (hlambda : ∀ j, 0 ≤ lambda j) (hmono : Monotone lambda)
    (hlocal : ∀ j v i,
      realPlaceNorm v (L v i (x j)) ≤
        AdelicMinima.placeScale v (lambda j) *
          exponentRadius (Q : ℝ)
            (ExteriorFiniteGlue.upperLocalConstants b.1) v i) :
    (Q : ℝ) ^ ((3 / 4 : ℝ) / (2 * n)) ≤
      lambda ⟨n - 1, by omega⟩ := by
  let : NeZero n := ⟨by omega⟩
  simpa [AdelicMinima.lastIndex] using (Classical.choose_spec
    (AdelicMinima.exists_half_power_last_cutoff
      L hL (ExteriorFiniteGlue.upperLocalConstants b.1)
      (by norm_num : (0 : ℝ) < 3 / 4) b.2))
    Q hQ x lambda hx hxS hlambda hmono hlocal

/-- The fixed determinant/Evertse-loss cutoff for one split label. -/
noncomputable def rankTailBudgetCutoff {n : ℕ}
    (L : Place23 → Fin n → RatLinearForm n)
    (hL : IsNonsingularFamily L) (kappa : PositiveSplit n) : ℕ :=
  Classical.choose
    (exists_fixedRankTailBudget_cutoff (n - kappa.1.val) L hL)

theorem rankTailBudgetCutoff_spec {n : ℕ}
    (L : Place23 → Fin n → RatLinearForm n)
    (hL : IsNonsingularFamily L) (kappa : PositiveSplit n)
    {Q : ℕ} (hQ : rankTailBudgetCutoff L hL kappa ≤ Q)
    (hQ2 : 2 ≤ Q) :
    |(n - 1).choose ((n - kappa.1.val) - 1) *
          ExteriorWedgeBounds.logBase (Q : ℝ)
            (AdelicMinimaUpper.upperConstant L) +
        n.choose (n - kappa.1.val) * ∑ place,
          ExteriorWedgeBounds.fixedWeightedDeterminantConstant
            (q := n - kappa.1.val) (Q : ℝ) L hL place| ≤
      (1 / 200 : ℝ) := by
  exact (Classical.choose_spec
    (exists_fixedRankTailBudget_cutoff (n - kappa.1.val) L hL))
    Q hQ hQ2

/-- A concrete rank-deficiency cutoff for the labelled exterior domain. -/
noncomputable def exteriorRankCutoff {n : ℕ}
    {L : Place23 → Fin n → RatLinearForm n}
    {hL : IsNonsingularFamily L}
    (a : ExteriorStabilizationLabel L hL) : ℕ :=
  Classical.choose (Erdos407.RankDrop.exists_sRankDeficient_cutoff
    (labeledExteriorForms a) (labeledExteriorForms_nonsingular a)
    (labeledExteriorConstants a)
    (by norm_num : (0 : ℝ) < 1 / 1000)
    (sum_labeledExteriorConstants_le a))

theorem exteriorRankCutoff_spec {n : ℕ}
    {L : Place23 → Fin n → RatLinearForm n}
    {hL : IsNonsingularFamily L}
    (a : ExteriorStabilizationLabel L hL) {Q : ℕ}
    (hQ : exteriorRankCutoff a ≤ Q) :
    Erdos407.RankDrop.realSApproximationRank
      (labeledExteriorForms a) Q (labeledExteriorConstants a) <
        exteriorLabelDimension a := by
  exact (Classical.choose_spec
    (Erdos407.RankDrop.exists_sRankDeficient_cutoff
      (labeledExteriorForms a) (labeledExteriorForms_nonsingular a)
      (labeledExteriorConstants a)
      (by norm_num : (0 : ℝ) < 1 / 1000)
      (sum_labeledExteriorConstants_le a))) Q hQ

/-- The maximum of a natural-number cutoff over an arbitrary finite type. -/
noncomputable def finiteNatSup {α : Type*} [Finite α] (f : α → ℕ) : ℕ := by
  letI := Fintype.ofFinite α
  exact Finset.univ.sup f

theorem le_finiteNatSup {α : Type*} [Finite α] (f : α → ℕ) (a : α) :
    f a ≤ finiteNatSup f := by
  classical
  let := Fintype.ofFinite α
  exact Finset.le_sup (s := Finset.univ) (f := f) (Finset.mem_univ a)

/-- Replacing every bounded raw exponent by its labelled upper endpoint
loses at most one mesh in each of the `3d` coordinates. -/
theorem sum_exteriorLabelUpper_le {d : ℕ}
    {gamma lo hi : ℝ} (hgamma : 0 < gamma)
    (a : HeightBoxes.LocalConstants d)
    (ha : ∀ place i, a place i ∈ Set.Icc lo hi) :
    (∑ place, ∑ i,
      exteriorLabelUpperConstants
        (exteriorExponentLabelOf hgamma a ha) place i) ≤
      (∑ place, ∑ i, a place i) + 3 * d * gamma := by
  calc
    _ ≤ ∑ place, ∑ i, (a place i + gamma) := by
      apply Finset.sum_le_sum
      intro place _
      apply Finset.sum_le_sum
      intro i _
      exact exteriorLabelUpper_le_exponent_add hgamma a ha place i
    _ = _ := by
      simp only [Finset.sum_add_distrib, Finset.sum_const,
        Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      ring

/-- In every exterior dimension `d ≤ 10`, the fixed mesh retains a
uniform negative sum from the raw margin `-1/100`. -/
theorem sum_exteriorLabelUpper_le_neg_one_thousand {d : ℕ}
    (hd : d ≤ 10) {lo hi : ℝ}
    (a : HeightBoxes.LocalConstants d)
    (ha : ∀ place i, a place i ∈ Set.Icc lo hi)
    (hsum : (∑ place, ∑ i, a place i) ≤ -(1 / 100 : ℝ)) :
    (∑ place, ∑ i,
      exteriorLabelUpperConstants
        (exteriorExponentLabelOf exteriorBoxingMesh_pos a ha) place i) ≤
      -(1 / 1000 : ℝ) := by
  have hround := sum_exteriorLabelUpper_le exteriorBoxingMesh_pos a ha
  calc
    _ ≤ (∑ place, ∑ i, a place i) +
        3 * d * exteriorBoxingMesh := hround
    _ ≤ -(1 / 100 : ℝ) + 3 * 10 * exteriorBoxingMesh := by
      apply add_le_add hsum
      apply mul_le_mul_of_nonneg_right
      · have hdR : (d : ℝ) ≤ 10 := by exact_mod_cast hd
        nlinarith
      · exact exteriorBoxingMesh_pos.le
    _ ≤ -(1 / 1000 : ℝ) := by
      norm_num [exteriorBoxingMesh]

theorem exponentRadius_le_exteriorLabelUpper {d Q : ℕ} (hQ : 1 < Q)
    {gamma lo hi : ℝ} (hgamma : 0 < gamma)
    (a : HeightBoxes.LocalConstants d)
    (ha : ∀ place i, a place i ∈ Set.Icc lo hi)
    (place : Place23) (i : Fin d) :
    exponentRadius (Q : ℝ) a place i ≤
      exponentRadius (Q : ℝ)
        (exteriorLabelUpperConstants
          (exteriorExponentLabelOf hgamma a ha)) place i := by
  unfold exponentRadius
  apply Real.rpow_le_rpow_of_exponent_le
  · exact_mod_cast (Nat.le_of_lt hQ)
  · exact (exteriorExponent_lt_labelUpper hgamma a ha place i).le

/-- Once the raw exterior exponents lie in a fixed interval, the omitted
wedges furnished by a weighted certificate all enter the single domain
indexed by their finite label. -/
theorem WeightedExteriorCertificate.omitted_mem_labelUpper
    {n Q : ℕ} (hQ : 1 < Q)
    {L : Place23 → Fin n → RatLinearForm n}
    {hL : IsNonsingularFamily L} {c : HeightBoxes.LocalConstants n}
    {B : AdelicMinima.AdaptedBasisCertificate L Q c}
    {kappa : Fin n} {hkappa : 0 < kappa.val}
    (E : WeightedExteriorCertificate L hL c B kappa hkappa)
    {gamma lo hi : ℝ} (hgamma : 0 < gamma)
    (hrange : ∀ place i,
      weightedExteriorRawLocalConstants Q kappa hkappa c B.lambda E.pi E.C
          place i ∈ Set.Icc lo hi) :
    ∀ J : OmittedExteriorIndex (tailExteriorIndex kappa),
      finExteriorBasisWedge
          (EvertseBasis.transformBasis E.change B.point) J.1 ∈
        Erdos407.RankDrop.realSIntegralApproximationDomain
          (exteriorLocalForms (permutedLocalForms L E.pi)
            (permutedLocalForms_nonsingular hL E.pi)
            (n - kappa.val)) Q
          (exteriorLabelUpperConstants
            (exteriorExponentLabelOf hgamma
              (weightedExteriorRawLocalConstants Q kappa hkappa c
                B.lambda E.pi E.C) hrange)) := by
  let mu : Place23 → Fin n → ℝ :=
    fun place i ↦ AdelicMinima.placeScale place (B.lambda i)
  let rho : Place23 → Fin n → ℝ :=
    fun place i ↦ exponentRadius (Q : ℝ) c place (E.pi place i)
  let Aloss : Place23 → ℝ := weightedEvertseLoss E.C
  let raw := weightedExteriorRawLocalConstants Q kappa hkappa c
    B.lambda E.pi E.C
  have hQr : 0 < (Q : ℝ) := by exact_mod_cast (Nat.zero_lt_of_lt hQ)
  have hmu : ∀ place i, 0 < mu place i := by
    intro place i
    by_cases hv : place = Place23.infinite
    · subst place
      simpa [mu] using B.lambda_pos i
    · simp [mu, AdelicMinima.placeScale, hv]
  have hmuMono : ∀ place, Monotone (mu place) := by
    intro place
    by_cases hv : place = Place23.infinite
    · subst place
      simpa [mu] using B.lambda_mono
    · simp only [mu, AdelicMinima.placeScale, if_neg hv]
      exact fun _ _ _ ↦ le_rfl
  have hrho : ∀ place i, 0 < rho place i := by
    intro place i
    exact Real.rpow_pos_of_pos hQr _
  have hAloss : ∀ place, 0 < Aloss place :=
    fun place ↦ weightedEvertseLoss_pos E.C_ge_one place
  refine omittedWedges_mem_realSIntegralApproximationDomain_weighted
    kappa hkappa L hL E.pi
      (EvertseBasis.transformBasis E.change B.point) E.transformedSIntegral
      mu rho Aloss (fun place ↦ (hAloss place).le)
      (fun place i ↦ (hrho place i).le) hmu hmuMono ?_ Q
      (exteriorLabelUpperConstants
        (exteriorExponentLabelOf hgamma raw (by simpa only [raw] using hrange))) ?_
  · intro place i j
    simpa only [mu, rho, Aloss, permutedLocalForms] using E.local_bound place i j
  · intro place I
    rw [weightedOmittedWedgeRowRadius_eq_exponentRadius hQ kappa hkappa
      c E.pi B.lambda B.lambda_pos (weightedEvertseLoss E.C)
        (weightedEvertseLoss_pos E.C_ge_one) place I]
    apply exponentRadius_le_exteriorLabelUpper hQ hgamma raw
      (by simpa only [raw] using hrange)

/-! ## Finite recovery across finitely many exterior labels -/

/-- A finite family of finite exterior-span sets, even with varying exterior
degree, recovers only finitely many original subspaces.  This is the
dependent finite-union form needed when the stabilized rank and gap index
are included in the label. -/
theorem finite_recoveredSpaces_of_finite_exteriorFamilies
    {n : ℕ} {label : Type*} [Finite label]
    (q : label → ℕ) (hq : ∀ a, 0 < q a)
    (C : ∀ a, Set (Submodule ℚ (⋀[ℚ]^(q a) (Fin n → ℚ))))
    (hC : ∀ a, (C a).Finite) :
    {W : Submodule ℚ (Fin n → ℚ) |
      ∃ a, ∃ v : Fin n → Fin n → ℚ, LinearIndependent ℚ v ∧
        ∃ J : Set.powersetCard (Fin n) (q a),
          W = basisComplementSubspace v J ∧
            omittedExteriorSpan v J ∈ C a}.Finite := by
  let R : label → Set (Submodule ℚ (Fin n → ℚ)) := fun a ↦
    {W | ∃ v : Fin n → Fin n → ℚ, LinearIndependent ℚ v ∧
      ∃ J : Set.powersetCard (Fin n) (q a),
        W = basisComplementSubspace v J ∧ omittedExteriorSpan v J ∈ C a}
  have hR : ∀ a, (R a).Finite := by
    intro a
    exact finite_basisComplementSubspaces_of_finite_exteriorSpans
      (E := Fin n → ℚ) (n := n) (q := q a) (by simp) (hq a) (hC a)
  have hUnion :
      {W : Submodule ℚ (Fin n → ℚ) |
        ∃ a, ∃ v : Fin n → Fin n → ℚ, LinearIndependent ℚ v ∧
          ∃ J : Set.powersetCard (Fin n) (q a),
            W = basisComplementSubspace v J ∧ omittedExteriorSpan v J ∈ C a} =
        ⋃ a, R a := by
    ext W
    simp only [Set.mem_setOf_eq, Set.mem_iUnion]
    rfl
  rw [hUnion]
  exact Set.finite_iUnion hR

/-! ## Transporting stabilized exterior spans back through coordinates -/

noncomputable def exteriorCoordinateSubmodule {n q : ℕ}
    (U : Submodule ℚ (⋀[ℚ]^q (Fin n → ℚ))) :
    Submodule ℚ (Fin (n.choose q) → ℚ) :=
  U.map (exteriorFinCoordinateEquiv n q).toLinearMap

theorem exteriorCoordinateSubmodule_injective {n q : ℕ} :
    Function.Injective (exteriorCoordinateSubmodule (n := n) (q := q)) := by
  exact Submodule.map_injective_of_injective
    (exteriorFinCoordinateEquiv n q).injective

theorem finite_exteriorSubmodules_of_finite_coordinateSubmodules
    {n q : ℕ} {C : Set (Submodule ℚ (Fin (n.choose q) → ℚ))}
    (hC : C.Finite) :
    {U : Submodule ℚ (⋀[ℚ]^q (Fin n → ℚ)) |
      exteriorCoordinateSubmodule U ∈ C}.Finite := by
  exact hC.preimage
    (Set.injOn_of_injective exteriorCoordinateSubmodule_injective)

/-- If all omitted finite-coordinate wedges lie in a codimension-one
exterior span, that span is exactly the coordinate image of the omitted
wedge hyperplane. -/
theorem exteriorCoordinateSubmodule_omitted_eq_of_finrank
    {n q : ℕ} {v : Fin n → Fin n → ℚ}
    (hv : LinearIndependent ℚ v)
    (J₀ : Set.powersetCard (Fin n) q)
    (W : Submodule ℚ (Fin (n.choose q) → ℚ))
    (hmem : ∀ J : OmittedExteriorIndex J₀,
      finExteriorBasisWedge v J.1 ∈ W)
    (hrank : Module.finrank ℚ W = n.choose q - 1) :
    exteriorCoordinateSubmodule (omittedExteriorSpan v J₀) = W := by
  apply Submodule.eq_of_le_of_finrank_le
  · rintro _ ⟨x, hx, rfl⟩
    refine Submodule.span_induction
      (p := fun x _ ↦ (exteriorFinCoordinateEquiv n q) x ∈ W)
      ?_ (by simpa using W.zero_mem) ?_ ?_ hx
    · rintro _ ⟨J, rfl⟩
      exact hmem J
    · intro x y _ _ hx hy
      simpa using W.add_mem hx hy
    · intro a x _ hx
      simpa using W.smul_mem a hx
  · rw [hrank, exteriorCoordinateSubmodule,
      LinearEquiv.finrank_map_eq,
      finrank_omittedExteriorSpan hv J₀]

/-! ## The finite stabilized families -/

/-- The codimension-one original approximation spans, over the finite
family of admissible original exponent labels. -/
noncomputable def originalStabilizedSpaces {n : ℕ}
    (L : Place23 → Fin n → RatLinearForm n) :
    Set (Submodule ℚ (Fin n → ℚ)) :=
  ⋃ b : GoodOriginalBoxLabel n,
    Erdos407.RankDrop.sCodimOneApproximationSpaces L
      (ExteriorFiniteGlue.upperLocalConstants b.1)

theorem originalStabilizedSpaces_finite {n : ℕ} (hn2 : 2 ≤ n)
    (L : Place23 → Fin n → RatLinearForm n)
    (hL : IsNonsingularFamily L) :
    (originalStabilizedSpaces L).Finite := by
  unfold originalStabilizedSpaces
  apply Set.finite_iUnion
  intro b
  exact Erdos407.RankDrop.sCodimOneApproximationSpaces_finite
    hn2 L hL (ExteriorFiniteGlue.upperLocalConstants b.1)
    (by norm_num : (0 : ℝ) < 3 / 4) b.2

/-- Codimension-one coordinate spans in the exterior system belonging to
one stabilization label. -/
noncomputable def labeledExteriorCoordinateSpaces {n : ℕ}
    {L : Place23 → Fin n → RatLinearForm n}
    {hL : IsNonsingularFamily L}
    (a : ExteriorStabilizationLabel L hL) :
    Set (Submodule ℚ (Fin (exteriorLabelDimension a) → ℚ)) :=
  Erdos407.RankDrop.sCodimOneApproximationSpaces
    (labeledExteriorForms a) (labeledExteriorConstants a)

theorem labeledExteriorCoordinateSpaces_finite {n : ℕ} (hn2 : 2 ≤ n)
    {L : Place23 → Fin n → RatLinearForm n}
    {hL : IsNonsingularFamily L}
    (a : ExteriorStabilizationLabel L hL) :
    (labeledExteriorCoordinateSpaces a).Finite := by
  exact Erdos407.RankDrop.sCodimOneApproximationSpaces_finite
    (exteriorLabelDimension_two_le hn2 a)
    (labeledExteriorForms a) (labeledExteriorForms_nonsingular a)
    (labeledExteriorConstants a)
    (by norm_num : (0 : ℝ) < 1 / 1000)
    (sum_labeledExteriorConstants_le a)

/-- Pull the finite stabilized coordinate spans back through the canonical
exterior-coordinate equivalence. -/
noncomputable def labeledExteriorAlgebraSpaces {n : ℕ}
    {L : Place23 → Fin n → RatLinearForm n}
    {hL : IsNonsingularFamily L}
    (a : ExteriorStabilizationLabel L hL) :
    Set (Submodule ℚ (⋀[ℚ]^(exteriorLabelDegree a) (Fin n → ℚ))) :=
  {U | exteriorCoordinateSubmodule U ∈ labeledExteriorCoordinateSpaces a}

theorem labeledExteriorAlgebraSpaces_finite {n : ℕ} (hn2 : 2 ≤ n)
    {L : Place23 → Fin n → RatLinearForm n}
    {hL : IsNonsingularFamily L}
    (a : ExteriorStabilizationLabel L hL) :
    (labeledExteriorAlgebraSpaces a).Finite := by
  exact finite_exteriorSubmodules_of_finite_coordinateSubmodules
    (labeledExteriorCoordinateSpaces_finite hn2 a)

/-- Original subspaces recovered, by the omitted Pluecker coordinate, from
all finitely many stabilized exterior hyperplanes. -/
noncomputable def exteriorRecoveredSpaces {n : ℕ}
    (L : Place23 → Fin n → RatLinearForm n)
    (hL : IsNonsingularFamily L) :
    Set (Submodule ℚ (Fin n → ℚ)) :=
  {W | ∃ a : ExteriorStabilizationLabel L hL,
    ∃ v : Fin n → Fin n → ℚ, LinearIndependent ℚ v ∧
      ∃ J : Set.powersetCard (Fin n) (exteriorLabelDegree a),
        W = basisComplementSubspace v J ∧
          omittedExteriorSpan v J ∈ labeledExteriorAlgebraSpaces a}

theorem exteriorRecoveredSpaces_finite {n : ℕ} (hn2 : 2 ≤ n)
    (L : Place23 → Fin n → RatLinearForm n)
    (hL : IsNonsingularFamily L) :
    (exteriorRecoveredSpaces L hL).Finite := by
  exact finite_recoveredSpaces_of_finite_exteriorFamilies
    exteriorLabelDegree exteriorLabelDegree_pos
    labeledExteriorAlgebraSpaces
    (labeledExteriorAlgebraSpaces_finite hn2)

/-- Both the original codimension-one branch and the exterior rank-tail
branch range over one finite family of proper original subspaces. -/
noncomputable def stabilizedRecoveredSpaces {n : ℕ}
    (L : Place23 → Fin n → RatLinearForm n)
    (hL : IsNonsingularFamily L) :
    Set (Submodule ℚ (Fin n → ℚ)) :=
  originalStabilizedSpaces L ∪ exteriorRecoveredSpaces L hL

theorem stabilizedRecoveredSpaces_finite {n : ℕ} (hn2 : 2 ≤ n)
    (L : Place23 → Fin n → RatLinearForm n)
    (hL : IsNonsingularFamily L) :
    (stabilizedRecoveredSpaces L hL).Finite :=
  (originalStabilizedSpaces_finite hn2 L hL).union
    (exteriorRecoveredSpaces_finite hn2 L hL)

theorem stabilizedRecoveredSpaces_proper {n : ℕ} (hn2 : 2 ≤ n)
    (L : Place23 → Fin n → RatLinearForm n)
    (hL : IsNonsingularFamily L)
    (W : stabilizedRecoveredSpaces L hL) :
    (W.1 : Submodule ℚ (Fin n → ℚ)) < ⊤ := by
  rcases W.2 with hW | hW
  · change W.1 ∈ originalStabilizedSpaces L at hW
    simp only [originalStabilizedSpaces, Set.mem_iUnion] at hW
    obtain ⟨b, hb⟩ := hW
    exact Erdos407.RankDrop.sCodimOne_isProper (by omega)
      ⟨W.1, hb⟩
  · change W.1 ∈ exteriorRecoveredSpaces L hL at hW
    obtain ⟨a, v, hv, J, hW, _⟩ := hW
    rw [hW]
    exact ExteriorFiniteGlue.basisComplementSubspace_lt_top hv
      (exteriorLabelDegree_pos a) J

/-! ## One uniform height cutoff -/

noncomputable def originalLabelCutoffSup {n : ℕ} (hn2 : 2 ≤ n)
    (L : Place23 → Fin n → RatLinearForm n)
    (hL : IsNonsingularFamily L) : ℕ :=
  finiteNatSup fun b : GoodOriginalBoxLabel n ↦
    max (originalRankCutoff L hL b) (lastMinimumCutoff hn2 L hL b)

noncomputable def rankTailBudgetCutoffSup {n : ℕ}
    (L : Place23 → Fin n → RatLinearForm n)
    (hL : IsNonsingularFamily L) : ℕ :=
  finiteNatSup fun kappa : PositiveSplit n ↦
    rankTailBudgetCutoff L hL kappa

noncomputable def exteriorRankCutoffSup {n : ℕ}
    (L : Place23 → Fin n → RatLinearForm n)
    (hL : IsNonsingularFamily L) : ℕ :=
  finiteNatSup fun a : ExteriorStabilizationLabel L hL ↦
    exteriorRankCutoff a

noncomputable def endpointHeightCutoff {n : ℕ} (hn2 : 2 ≤ n)
    (L : Place23 → Fin n → RatLinearForm n)
    (hL : IsNonsingularFamily L) : ℕ :=
  max 2 (max (ExteriorFiniteGlue.localFormsHeightCutoff L)
    (max (originalLabelCutoffSup hn2 L hL)
      (max (rankTailBudgetCutoffSup L hL)
        (exteriorRankCutoffSup L hL))))

theorem two_le_endpointHeightCutoff {n : ℕ} (hn2 : 2 ≤ n)
    (L : Place23 → Fin n → RatLinearForm n)
    (hL : IsNonsingularFamily L) :
    2 ≤ endpointHeightCutoff hn2 L hL := by
  exact le_max_left _ _

theorem localFormsHeightCutoff_le_endpoint {n : ℕ} (hn2 : 2 ≤ n)
    (L : Place23 → Fin n → RatLinearForm n)
    (hL : IsNonsingularFamily L) :
    ExteriorFiniteGlue.localFormsHeightCutoff L ≤
      endpointHeightCutoff hn2 L hL := by
  exact (le_max_left _ _).trans (le_max_right _ _)

theorem originalRankCutoff_le_endpoint {n : ℕ} (hn2 : 2 ≤ n)
    (L : Place23 → Fin n → RatLinearForm n)
    (hL : IsNonsingularFamily L) (b : GoodOriginalBoxLabel n) :
    originalRankCutoff L hL b ≤ endpointHeightCutoff hn2 L hL := by
  have hs := le_finiteNatSup
    (fun b : GoodOriginalBoxLabel n ↦
      max (originalRankCutoff L hL b) (lastMinimumCutoff hn2 L hL b)) b
  unfold endpointHeightCutoff originalLabelCutoffSup
  omega

theorem lastMinimumCutoff_le_endpoint {n : ℕ} (hn2 : 2 ≤ n)
    (L : Place23 → Fin n → RatLinearForm n)
    (hL : IsNonsingularFamily L) (b : GoodOriginalBoxLabel n) :
    lastMinimumCutoff hn2 L hL b ≤ endpointHeightCutoff hn2 L hL := by
  have hs := le_finiteNatSup
    (fun b : GoodOriginalBoxLabel n ↦
      max (originalRankCutoff L hL b) (lastMinimumCutoff hn2 L hL b)) b
  unfold endpointHeightCutoff originalLabelCutoffSup
  omega

theorem rankTailBudgetCutoff_le_endpoint {n : ℕ} (hn2 : 2 ≤ n)
    (L : Place23 → Fin n → RatLinearForm n)
    (hL : IsNonsingularFamily L) (kappa : PositiveSplit n) :
    rankTailBudgetCutoff L hL kappa ≤ endpointHeightCutoff hn2 L hL := by
  have hs := le_finiteNatSup
    (fun kappa : PositiveSplit n ↦ rankTailBudgetCutoff L hL kappa) kappa
  unfold endpointHeightCutoff rankTailBudgetCutoffSup
  omega

theorem exteriorRankCutoff_le_endpoint {n : ℕ} (hn2 : 2 ≤ n)
    (L : Place23 → Fin n → RatLinearForm n)
    (hL : IsNonsingularFamily L) (a : ExteriorStabilizationLabel L hL) :
    exteriorRankCutoff a ≤ endpointHeightCutoff hn2 L hL := by
  have hs := le_finiteNatSup
    (fun a : ExteriorStabilizationLabel L hL ↦ exteriorRankCutoff a) a
  unfold endpointHeightCutoff exteriorRankCutoffSup
  omega

/-! ## Pointwise exterior rank-tail recovery -/

theorem zeroLocalForm_or_mem_stabilizedRecoveredSpaces
    {n : ℕ} (hn2 : 2 ≤ n) (hn5 : n ≤ 5)
    (L : Place23 → Fin n → RatLinearForm n)
    (hL : IsNonsingularFamily L) (x : IntVector n)
    (hx0 : x ≠ 0) (hx : SatisfiesStrongInequality L x)
    (hlarge : endpointHeightCutoff hn2 L hL < boxHeight x) :
    (∃ v i, L v i (intCastVec x) = 0) ∨
      ∃ W : stabilizedRecoveredSpaces L hL, intCastVec x ∈ W.1 := by
  have hlocal : ExteriorFiniteGlue.localFormsHeightCutoff L ≤ boxHeight x :=
    (localFormsHeightCutoff_le_endpoint hn2 L hL).trans hlarge.le
  rcases ExteriorFiniteGlue.zeroLocalForm_or_exists_originalLocalBox
      hn5 L x hx0 hlocal hx with hzero | ⟨b₀, hbox, hsum⟩
  · exact Or.inl hzero
  · right
    let b : GoodOriginalBoxLabel n := ⟨b₀, hsum⟩
    let Q : ℕ := boxHeight x
    let c : HeightBoxes.LocalConstants n :=
      ExteriorFiniteGlue.upperLocalConstants b.1
    have hQ2 : 2 ≤ Q :=
      (two_le_endpointHeightCutoff hn2 L hL).trans hlarge.le
    have hQ1 : 1 ≤ Q := by omega
    let A := upperAdaptedCertificate (by omega) L hL hQ1 c
    let B := A.toAdaptedBasisCertificate
    have hbox' : InApproximationBox L (Q : ℝ) c (intCastVec x) := by
      simpa only [Q, c, b] using hbox
    have hRpos_mem := upperAdaptedCertificate_rank_pos_and_mem
      (by omega) L hL hQ1 c hx0 hbox'
    have hRpos : 0 < B.rank := by
      simpa only [B, A] using hRpos_mem.1
    have hxspan : intCastVec x ∈
        Erdos407.RankDrop.realSApproximationSpan L Q c := hRpos_mem.2
    have hQoriginal : originalRankCutoff L hL b ≤ Q :=
      (originalRankCutoff_le_endpoint hn2 L hL b).trans hlarge.le
    have hRlt : B.rank < n := by
      change A.rank < n
      rw [A.rank_eq]
      exact originalRankCutoff_spec L hL b hQoriginal
    by_cases hcodim : B.rank + 1 = n
    · let W := Erdos407.RankDrop.realSApproximationSpan L Q c
      have hWcodim : W ∈ Erdos407.RankDrop.sCodimOneApproximationSpaces L c := by
        apply realSApproximationSpan_mem_sCodimOne_of_rank_eq_pred
          (by omega) hQ2 L c
        rw [← B.rank_eq]
        omega
      refine ⟨⟨W, Or.inl ?_⟩, ?_⟩
      · change W ∈ originalStabilizedSpaces L
        simp only [originalStabilizedSpaces, Set.mem_iUnion]
        exact ⟨b, hWcodim⟩
      · exact hxspan
    · have hlast : (Q : ℝ) ^ ((3 / 4 : ℝ) / (2 * n)) ≤
          B.lambda ⟨n - 1, by omega⟩ := by
        apply lastMinimumCutoff_spec hn2 L hL b
        · exact (lastMinimumCutoff_le_endpoint hn2 L hL b).trans hlarge.le
        · exact B.independent
        · exact B.sIntegral
        · exact fun j ↦ (B.lambda_pos j).le
        · exact B.lambda_mono
        · exact B.local_bound
      have hkappa : 0 < (ExteriorWedgeBounds.rankTailSelectedSplit
          hRpos hRlt B.lambda).val :=
        ExteriorWedgeBounds.rankTailSelectedSplit_pos hRpos hRlt B.lambda
      let kappaLabel : PositiveSplit n :=
        ⟨ExteriorWedgeBounds.rankTailSelectedSplit hRpos hRlt B.lambda,
          hkappa⟩
      have hfixed :
          |(n - 1).choose ((n - (ExteriorWedgeBounds.rankTailSelectedSplit
                hRpos hRlt B.lambda).val) - 1) *
                ExteriorWedgeBounds.logBase (Q : ℝ)
                  (AdelicMinimaUpper.upperConstant L) +
              n.choose (n - (ExteriorWedgeBounds.rankTailSelectedSplit
                hRpos hRlt B.lambda).val) * ∑ place,
                ExteriorWedgeBounds.fixedWeightedDeterminantConstant
                  (q := n - (ExteriorWedgeBounds.rankTailSelectedSplit
                    hRpos hRlt B.lambda).val) (Q : ℝ) L hL place| ≤
            (1 / 200 : ℝ) := by
        apply rankTailBudgetCutoff_spec L hL kappaLabel
        · exact (rankTailBudgetCutoff_le_endpoint hn2 L hL kappaLabel).trans
            hlarge.le
        · exact hQ2
      obtain ⟨E, hcoeff, homitted⟩ :=
        ExteriorWedgeBounds.exists_adaptedRankTail_fixedCoefficient_omittedWedges
          L hL hQ2 c B hRpos hRlt exteriorBoxingMesh_pos
      let raw := ExteriorWedgeBounds.splitWeightedRawExteriorLocalConstants
        (Q : ℝ) c
        (ExteriorWedgeBounds.OrderedMinimaData.ofAdaptedBasisCertificate B)
        E (ExteriorWedgeBounds.rankTailSelectedSplit hRpos hRlt B.lambda)
          hkappa
      have hcIcc : ∀ place i, c place i ∈ Set.Icc (-5 : ℝ) 3 := by
        intro place i
        exact upperLocalConstants_mem_Icc b.1 place i
      have hrawRange : ∀ place i,
          raw place i ∈ Set.Icc (-rawExteriorLogBound L hL)
            (rawExteriorLogBound L hL) := by
        intro place i
        have hi := abs_splitWeightedRawExteriorLocalConstants_le_rawBound
          hn5 L hL hQ2 c hcIcc A E hcoeff
            (ExteriorWedgeBounds.rankTailSelectedSplit hRpos hRlt B.lambda)
            hkappa place i
        exact abs_le.mp hi
      have hprod : (∏ i, B.lambda i) ≤
          AdelicMinimaUpper.upperConstant L *
            (Q : ℝ) ^ (-∑ place, ∑ i, c place i) := by
        exact A.product_le_rpow_neg_sum hQ1
      have hrawSum : (∑ place, ∑ i, raw place i) ≤ -(1 / 100 : ℝ) := by
        exact sum_rankTailRaw_le_neg_one_hundred hn2 hn5 L hL hQ2 c B
          hRpos hRlt E hcoeff hprod hlast hfixed
      let e := exteriorExponentLabelOf exteriorBoxingMesh_pos raw hrawRange
      have heSum : (∑ place, ∑ i,
          exteriorLabelUpperConstants e place i) ≤ -(1 / 1000 : ℝ) := by
        exact sum_exteriorLabelUpper_le_neg_one_thousand
          (choose_le_ten_of_le_five hn5
            (n - (ExteriorWedgeBounds.rankTailSelectedSplit
              hRpos hRlt B.lambda).val)) raw hrawRange hrawSum
      let a : ExteriorStabilizationLabel L hL :=
        ⟨kappaLabel, E.permutation, ⟨e, heSum⟩⟩
      have haPermutation : a.2.1 = E.permutation := rfl
      have homittedLabel : ∀ J : OmittedExteriorIndex
          (ExteriorWedgeBounds.tailExteriorIndex
            (ExteriorWedgeBounds.rankTailSelectedSplit hRpos hRlt B.lambda)),
          finExteriorBasisWedge E.vector J.1 ∈
            Erdos407.RankDrop.realSIntegralApproximationDomain
              (labeledExteriorForms a) Q (labeledExteriorConstants a) := by
        intro J
        have hJ := mem_labelUpper_of_mem_discretized
          (by omega : 1 < Q) exteriorBoxingMesh_pos raw hrawRange
          (homitted J)
        have hforms : labeledExteriorForms a =
            exteriorLocalForms
              (permutedLocalForms L E.permutation)
              (permutedLocalForms_nonsingular hL E.permutation)
              (n - (ExteriorWedgeBounds.rankTailSelectedSplit
                hRpos hRlt B.lambda).val) := by
          rw [labeledExteriorForms_eq a, haPermutation]
          rfl
        have hconstants : labeledExteriorConstants a =
            exteriorLabelUpperConstants e := by
          unfold labeledExteriorConstants
          congr 1
        rw [hforms, hconstants]
        have he : e = exteriorExponentLabelOf
            exteriorBoxingMesh_pos raw hrawRange := rfl
        rw [he]
        exact hJ
      let W := Erdos407.RankDrop.realSApproximationSpan
        (labeledExteriorForms a) Q (labeledExteriorConstants a)
      have hWlower : exteriorLabelDimension a - 1 ≤ Module.finrank ℚ W := by
        apply exteriorSpan_finrank_ge_pred E.independent
          (ExteriorWedgeBounds.tailExteriorIndex
            (ExteriorWedgeBounds.rankTailSelectedSplit hRpos hRlt B.lambda)) W
        intro J
        exact Erdos407.RankDrop.mem_realSApproximationSpan (homittedLabel J)
      have hQexterior : exteriorRankCutoff a ≤ Q :=
        (exteriorRankCutoff_le_endpoint hn2 L hL a).trans hlarge.le
      have hWupper : Module.finrank ℚ W < exteriorLabelDimension a := by
        exact exteriorRankCutoff_spec a hQexterior
      have hWrank : Module.finrank ℚ W = exteriorLabelDimension a - 1 := by
        omega
      have hWcodim : W ∈ labeledExteriorCoordinateSpaces a := by
        exact realSApproximationSpan_mem_sCodimOne_of_pred_le_rank_lt
          (by have := exteriorLabelDimension_two_le hn2 a; omega)
          hQ2 (labeledExteriorForms a) (labeledExteriorConstants a)
          hWlower hWupper
      have hcoordinate :
          exteriorCoordinateSubmodule
              (omittedExteriorSpan E.vector
                (ExteriorWedgeBounds.tailExteriorIndex
                  (ExteriorWedgeBounds.rankTailSelectedSplit
                    hRpos hRlt B.lambda))) = W := by
        apply exteriorCoordinateSubmodule_omitted_eq_of_finrank E.independent
          (ExteriorWedgeBounds.tailExteriorIndex
            (ExteriorWedgeBounds.rankTailSelectedSplit hRpos hRlt B.lambda)) W
        · intro J
          exact Erdos407.RankDrop.mem_realSApproximationSpan (homittedLabel J)
        · exact hWrank
      have homittedAlgebra :
          omittedExteriorSpan E.vector
              (ExteriorWedgeBounds.tailExteriorIndex
                (ExteriorWedgeBounds.rankTailSelectedSplit hRpos hRlt B.lambda)) ∈
            labeledExteriorAlgebraSpaces a := by
        change exteriorCoordinateSubmodule
            (omittedExteriorSpan E.vector
              (ExteriorWedgeBounds.tailExteriorIndex
                (ExteriorWedgeBounds.rankTailSelectedSplit hRpos hRlt B.lambda))) ∈
          labeledExteriorCoordinateSpaces a
        rw [hcoordinate]
        exact hWcodim
      let recovered := basisComplementSubspace E.vector
        (ExteriorWedgeBounds.tailExteriorIndex
          (ExteriorWedgeBounds.rankTailSelectedSplit hRpos hRlt B.lambda))
      have hrecovered : recovered ∈ exteriorRecoveredSpaces L hL := by
        refine ⟨a, E.vector, E.independent,
          ExteriorWedgeBounds.tailExteriorIndex
            (ExteriorWedgeBounds.rankTailSelectedSplit hRpos hRlt B.lambda),
          rfl, ?_⟩
        exact homittedAlgebra
      refine ⟨⟨recovered, Or.inr hrecovered⟩, ?_⟩
      exact (ExteriorWedgeBounds.adaptedRankTailApproximationSpan_le_recoveredComplement
        L c B hRpos hRlt E) hxspan


end ExteriorFinal

/-- The rational three-place Subspace-Theorem endpoint in original
dimensions at most five.  All analytic rank stabilization is applied in
the (possibly larger) exterior-coordinate dimension before the resulting
hyperplanes are dualized back to proper original subspaces. -/
theorem finiteCover_primitiveStrongSolutions
    {n : ℕ} (hn2 : 2 ≤ n) (hn5 : n ≤ 5)
    (L : Place23 → Fin n → RatLinearForm n)
    (hL : IsNonsingularFamily L) :
    HasFiniteHyperplaneCover (primitiveStrongSolutions L) := by
  open ExteriorFinal in
    apply finiteCover_of_largeHeightConclusion hn2
    refine ⟨endpointHeightCutoff hn2 L hL, ?_⟩
    let Xzero : Set (HeightBoxes.IntVector n) :=
      {x | ∃ v i, L v i (intCastVec x) = 0}
    let Xrecovered : Set (HeightBoxes.IntVector n) :=
      {x | ∃ W : stabilizedRecoveredSpaces L hL, intCastVec x ∈ W.1}
    have hzero : HasFiniteHyperplaneCover Xzero := by
      apply zeroLocalForm_hasFiniteHyperplaneCover L
      intro v i
      exact (hL v).ne_zero i
    have hrecovered : HasFiniteHyperplaneCover Xrecovered := by
      apply Erdos407.RankDrop.finiteHyperplaneCover_of_finite_properSubspaces
        (stabilizedRecoveredSpaces_finite hn2 L hL)
      · intro W hW
        exact stabilizedRecoveredSpaces_proper hn2 L hL ⟨W, hW⟩
      · intro x hx
        change ∃ W : stabilizedRecoveredSpaces L hL,
          intCastVec x ∈ W.1 at hx
        obtain ⟨W, hxW⟩ := hx
        exact ⟨W.1, W.2, hxW⟩
    apply (hzero.union hrecovered).mono
    intro x hx
    exact zeroLocalForm_or_mem_stabilizedRecoveredSpaces
      hn2 hn5 L hL x hx.1.2.1 hx.1.2.2 hx.2

end Erdos407.PadicSubspace
