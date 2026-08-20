/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
import Mathlib
import ErdosProblems.Erdos407.PadicProduct

/-!
# The elementary adelic geometry used for Erdős 407

This file fixes the three rational places `∞`, `2`, and `3` and records the
geometry-of-numbers facts which are needed before the determinant argument in
the rational Subspace Theorem.  In particular, it contains no abstract
"Minkowski hypothesis": the existence theorem below is an application of
Mathlib's Minkowski convex-body theorem to the standard integer lattice.

The ring `ℤ[1/6]` is represented by its increasing family of denominator
lattices `6⁻ᵏ ℤⁿ`.  This is more useful in the application than choosing a
localization presentation: every finite collection of `ℤ[1/6]` points occurs
in one of these lattices, while their Archimedean covolume is explicit.
-/

namespace Erdos407.AdelicMinkowski

open scoped BigOperators Matrix NNReal ENNReal Pointwise
open MeasureTheory Module Submodule Set

/-- The places used in the `{2,3}`-unit argument: `0 = ∞`, `1 = 2`, `2 = 3`. -/
abbrev RationalPlace := Fin 3

/-- A rational vector of dimension `n`. -/
abbrev RatVector (n : ℕ) := Fin n → ℚ

/-- A rational linear form, represented by its coefficients. -/
abbrev ratLinearForm (n : ℕ) := Fin n → ℚ

/-- Evaluation of a rational linear form. -/
def eval {n : ℕ} (L : ratLinearForm n) (x : RatVector n) : ℚ :=
  ∑ i, L i * x i

/-- The normalized absolute value at `∞`, `2`, or `3`. -/
def placeNorm (v : RationalPlace) (q : ℚ) : ℚ :=
  ![|q|, padicNorm 2 q, padicNorm 3 q] v

@[simp] theorem placeNorm_infty (q : ℚ) : placeNorm 0 q = |q| := rfl
@[simp] theorem placeNorm_two (q : ℚ) : placeNorm 1 q = padicNorm 2 q := rfl
@[simp] theorem placeNorm_three (q : ℚ) : placeNorm 2 q = padicNorm 3 q := rfl

@[simp] theorem placeNorm_zero (v : RationalPlace) : placeNorm v 0 = 0 := by
  fin_cases v <;> simp [placeNorm]

@[simp] theorem placeNorm_one (v : RationalPlace) : placeNorm v 1 = 1 := by
  fin_cases v <;> simp [placeNorm]

theorem placeNorm_nonneg (v : RationalPlace) (q : ℚ) : 0 ≤ placeNorm v q := by
  fin_cases v
  · exact abs_nonneg q
  · exact padicNorm.nonneg _
  · exact padicNorm.nonneg _

theorem placeNorm_mul (v : RationalPlace) (q r : ℚ) :
    placeNorm v (q * r) = placeNorm v q * placeNorm v r := by
  fin_cases v
  · simp [placeNorm, abs_mul]
  · exact padicNorm.mul q r
  · exact padicNorm.mul q r

theorem placeNorm_neg (v : RationalPlace) (q : ℚ) :
    placeNorm v (-q) = placeNorm v q := by
  fin_cases v <;> simp [placeNorm]

/-- The product of the three selected local norms. -/
def placeProduct (q : ℚ) : ℚ := ∏ v : RationalPlace, placeNorm v q

theorem placeProduct_eq_normProduct23 (q : ℚ) :
    placeProduct q = PadicProduct.normProduct23 q := by
  simp [placeProduct, PadicProduct.normProduct23, PadicProduct.archNorm,
    Fin.prod_univ_succ]
  ring

theorem placeProduct_mul (q r : ℚ) :
    placeProduct (q * r) = placeProduct q * placeProduct r := by
  simp only [placeProduct, placeNorm_mul, Finset.prod_mul_distrib]

/-! ## `ℤ[1/6]` and its denominator lattices -/

/-- The common denominator at level `k`. -/
def denominator (k : ℕ) : ℕ := 6 ^ k

@[simp] theorem denominator_zero : denominator 0 = 1 := by simp [denominator]

theorem denominator_pos (k : ℕ) : 0 < denominator k := by
  exact pow_pos (by omega) k

theorem denominator_ne_zero (k : ℕ) : denominator k ≠ 0 :=
  (denominator_pos k).ne'

/-- Membership in `6⁻ᵏ ℤⁿ`, the level-`k` denominator lattice. -/
def InDenominatorLattice {n : ℕ} (k : ℕ) (x : RatVector n) : Prop :=
  ∃ z : Fin n → ℤ, ∀ i, x i = (z i : ℚ) / denominator k

/-- Coordinatewise membership in `ℤ[1/6]`. -/
def InZOneSix {n : ℕ} (x : RatVector n) : Prop :=
  ∃ k, InDenominatorLattice k x

theorem inDenominatorLattice_zero {n k : ℕ} :
    InDenominatorLattice (n := n) k 0 := by
  refine ⟨0, fun i ↦ ?_⟩
  simp

theorem InDenominatorLattice.neg {n k : ℕ} {x : RatVector n}
    (hx : InDenominatorLattice k x) : InDenominatorLattice k (-x) := by
  obtain ⟨z, hz⟩ := hx
  refine ⟨-z, fun i ↦ ?_⟩
  change -(x i) = ((-z i : ℤ) : ℚ) / denominator k
  rw [hz i, Int.cast_neg]
  ring

theorem InDenominatorLattice.add {n k : ℕ} {x y : RatVector n}
    (hx : InDenominatorLattice k x) (hy : InDenominatorLattice k y) :
    InDenominatorLattice k (x + y) := by
  obtain ⟨z, hz⟩ := hx
  obtain ⟨w, hw⟩ := hy
  refine ⟨z + w, fun i ↦ ?_⟩
  simp only [Pi.add_apply, Int.cast_add, hz i, hw i]
  ring

theorem InDenominatorLattice.smul_int {n k : ℕ} {x : RatVector n}
    (hx : InDenominatorLattice k x) (a : ℤ) :
    InDenominatorLattice k ((a : ℚ) • x) := by
  obtain ⟨z, hz⟩ := hx
  refine ⟨a • z, fun i ↦ ?_⟩
  simp only [Pi.smul_apply, smul_eq_mul, Int.cast_mul, hz i]
  ring

theorem InDenominatorLattice.mono {n k l : ℕ} {x : RatVector n}
    (hx : InDenominatorLattice k x) (hkl : k ≤ l) :
    InDenominatorLattice l x := by
  obtain ⟨z, hz⟩ := hx
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hkl
  refine ⟨fun i ↦ z i * (6 : ℤ) ^ d, fun i ↦ ?_⟩
  rw [hz i]
  simp only [denominator, pow_add, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat,
    Int.cast_mul, Int.cast_pow, Int.cast_ofNat]
  field_simp

theorem InDenominatorLattice.inZOneSix {n k : ℕ} {x : RatVector n}
    (hx : InDenominatorLattice k x) : InZOneSix x :=
  ⟨k, hx⟩

theorem InZOneSix.add {n : ℕ} {x y : RatVector n}
    (hx : InZOneSix x) (hy : InZOneSix y) : InZOneSix (x + y) := by
  obtain ⟨k, hk⟩ := hx
  obtain ⟨l, hl⟩ := hy
  exact ⟨max k l, (hk.mono (le_max_left _ _)).add (hl.mono (le_max_right _ _))⟩

theorem InZOneSix.neg {n : ℕ} {x : RatVector n} (hx : InZOneSix x) :
    InZOneSix (-x) := by
  obtain ⟨k, hk⟩ := hx
  exact ⟨k, hk.neg⟩

/-! ## Adelic approximation boxes -/

/-- Local radii for `n` forms at the three selected places. -/
abbrev LocalRadii (n : ℕ) := RationalPlace → Fin n → ℚ

/-- The rational points satisfying all local linear-form inequalities. -/
def approximationBox {n : ℕ}
    (L : RationalPlace → Fin n → ratLinearForm n) (c : LocalRadii n) :
    Set (RatVector n) :=
  {x | ∀ v i, placeNorm v (eval (L v i) x) ≤ c v i}

/-- The level-`k` `ℤ[1/6]` points in an approximation box. -/
def approximationDomain {n : ℕ} (k : ℕ)
    (L : RationalPlace → Fin n → ratLinearForm n) (c : LocalRadii n) :
    Set (RatVector n) :=
  {x | InDenominatorLattice k x ∧ x ∈ approximationBox L c}

theorem approximationDomain_subset_ZOneSix {n k : ℕ}
    {L : RationalPlace → Fin n → ratLinearForm n} {c : LocalRadii n} :
    approximationDomain k L c ⊆ {x | InZOneSix x} := by
  intro x hx
  exact hx.1.inZOneSix

theorem eval_smul {n : ℕ} (L : ratLinearForm n) (a : ℚ) (x : RatVector n) :
    eval L (a • x) = a * eval L x := by
  simp only [eval, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  ring

/-- Radii obtained by multiplying a box by a rational scalar. -/
def scaleRadii {n : ℕ} (a : ℚ) (c : LocalRadii n) : LocalRadii n :=
  fun v i ↦ placeNorm v a * c v i

theorem smul_mem_approximationBox {n : ℕ}
    (L : RationalPlace → Fin n → ratLinearForm n) (c : LocalRadii n)
    {x : RatVector n} (hx : x ∈ approximationBox L c) (a : ℚ) :
    a • x ∈ approximationBox L (scaleRadii a c) := by
  intro v i
  rw [eval_smul, placeNorm_mul]
  exact mul_le_mul_of_nonneg_left (hx v i) (placeNorm_nonneg v a)

/-- Product of every local radius. -/
def radiiProduct {n : ℕ} (c : LocalRadii n) : ℚ :=
  ∏ v : RationalPlace, ∏ i : Fin n, c v i

/-- Scaling a local box has the expected adelic product factor. -/
theorem radiiProduct_scale {n : ℕ} (a : ℚ) (c : LocalRadii n) :
    radiiProduct (scaleRadii a c) = placeProduct a ^ n * radiiProduct c := by
  simp only [radiiProduct, scaleRadii, Finset.prod_mul_distrib,
    Finset.prod_const]
  rw [Finset.card_univ, Fintype.card_fin]
  change (∏ v : RationalPlace, placeNorm v a ^ n) * _ =
    (∏ v : RationalPlace, placeNorm v a) ^ n * _
  rw [Finset.prod_pow]

/-! ## Rank thresholds (successive-minimum language without choosing infima) -/

/-- `D` contains `r` linearly independent rational points.  This is the
order-theoretic content of saying that the `r`-th successive minimum is at
most the current scale. -/
def HasRankAtLeast {n : ℕ} (D : Set (RatVector n)) (r : ℕ) : Prop :=
  ∃ v : Fin r → RatVector n, LinearIndependent ℚ v ∧ ∀ i, v i ∈ D

theorem hasRankAtLeast_zero {n : ℕ} (D : Set (RatVector n)) :
    HasRankAtLeast D 0 := by
  refine ⟨fun i ↦ Fin.elim0 i, linearIndependent_empty_type, ?_⟩
  intro i
  exact Fin.elim0 i

theorem HasRankAtLeast.mono_set {n r : ℕ} {D E : Set (RatVector n)}
    (hD : HasRankAtLeast D r) (hDE : D ⊆ E) : HasRankAtLeast E r := by
  obtain ⟨v, hv, hvD⟩ := hD
  exact ⟨v, hv, fun i ↦ hDE (hvD i)⟩

theorem HasRankAtLeast.le_dimension {n r : ℕ} {D : Set (RatVector n)}
    (hD : HasRankAtLeast D r) : r ≤ n := by
  obtain ⟨v, hv, _⟩ := hD
  simpa only [Fintype.card_fin, Module.finrank_fin_fun] using hv.fintype_card_le_finrank

/-! ## Archimedean boxes, covolumes, and Minkowski -/

/-- A closed coordinate box centered at the origin. -/
def realBox {n : ℕ} (r : Fin n → ℝ) : Set (Fin n → ℝ) :=
  Set.Icc (-r) r

theorem realBox_volume {n : ℕ} (r : Fin n → ℝ) :
    volume (realBox r) = ∏ i, ENNReal.ofReal (2 * r i) := by
  rw [realBox, Real.volume_Icc_pi]
  congr 1
  funext i
  congr 1
  simp only [Pi.neg_apply]
  ring

theorem realBox_symmetric {n : ℕ} (r : Fin n → ℝ) :
    ∀ x ∈ realBox r, -x ∈ realBox r := by
  intro x hx
  constructor
  · intro i
    change -r i ≤ -x i
    exact _root_.neg_le_neg (hx.2 i)
  · intro i
    change -x i ≤ r i
    have hi := _root_.neg_le_neg (hx.1 i)
    change -x i ≤ -(-r i) at hi
    simpa only [neg_neg] using hi

theorem realBox_convex {n : ℕ} (r : Fin n → ℝ) : Convex ℝ (realBox r) :=
  convex_Icc _ _

theorem realBox_compact {n : ℕ} (r : Fin n → ℝ) : IsCompact (realBox r) :=
  isCompact_Icc

/-- The standard integer lattice in `ℝⁿ`. -/
def standardLattice (n : ℕ) : AddSubgroup (Fin n → ℝ) :=
  (Submodule.span ℤ (Set.range (Pi.basisFun ℝ (Fin n)))).toAddSubgroup

noncomputable instance standardLattice_countable (n : ℕ) :
    Countable (standardLattice n) := by
  change Countable (Submodule.span ℤ (Set.range (Pi.basisFun ℝ (Fin n))))
  infer_instance

noncomputable instance standardLattice_discrete (n : ℕ) :
    DiscreteTopology (standardLattice n) := by
  change DiscreteTopology (Submodule.span ℤ (Set.range (Pi.basisFun ℝ (Fin n))))
  infer_instance

/-- The half-open unit cube is a fundamental domain for `ℤⁿ`. -/
theorem standardLattice_fundamentalDomain (n : ℕ) :
    IsAddFundamentalDomain (standardLattice n)
      (ZSpan.fundamentalDomain (Pi.basisFun ℝ (Fin n))) volume := by
  exact ZSpan.isAddFundamentalDomain' (Pi.basisFun ℝ (Fin n)) volume

/-- The standard integer lattice has covolume one. -/
theorem standardLattice_covolume (n : ℕ) :
    volume (ZSpan.fundamentalDomain (Pi.basisFun ℝ (Fin n))) = 1 := by
  rw [ZSpan.volume_fundamentalDomain]
  have hmatrix : Matrix.of (Pi.basisFun ℝ (Fin n) : Fin n → Fin n → ℝ) = 1 := by
    classical
    ext i j
    rw [Matrix.of_apply, Pi.basisFun_apply, Pi.single_apply, Matrix.one_apply]
    by_cases hij : i = j
    · subst j
      rfl
    · rw [if_neg hij, if_neg (Ne.symm hij)]
  rw [hmatrix, Matrix.det_one, abs_one, ENNReal.ofReal_one]

/-- Minkowski's theorem for a symmetric coordinate box and the standard
integer lattice.  The witness is bundled with its lattice membership. -/
theorem exists_nonzero_standardLattice_mem_realBox {n : ℕ} (r : Fin n → ℝ)
    (hvol : (2 : ℝ≥0∞) ^ n < volume (realBox r)) :
    ∃ x : standardLattice n, x ≠ 0 ∧ (x : Fin n → ℝ) ∈ realBox r := by
  have hfinrank : Module.finrank ℝ (Fin n → ℝ) = n := by
    simp
  have hM :
      volume (ZSpan.fundamentalDomain (Pi.basisFun ℝ (Fin n))) *
          2 ^ Module.finrank ℝ (Fin n → ℝ) < volume (realBox r) := by
    rw [standardLattice_covolume, one_mul, hfinrank]
    exact hvol
  obtain ⟨x, hx0, hxr⟩ :=
    MeasureTheory.exists_ne_zero_mem_lattice_of_measure_mul_two_pow_lt_measure
      (standardLattice_fundamentalDomain n) (realBox_symmetric r)
      (realBox_convex r) hM
  exact ⟨x, hx0, hxr⟩

/-- The compact, weak-inequality version of the same theorem. -/
theorem exists_nonzero_standardLattice_mem_realBox_of_le {n : ℕ} [NeZero n]
    (r : Fin n → ℝ)
    (hvol : (2 : ℝ≥0∞) ^ n ≤ volume (realBox r)) :
    ∃ x : standardLattice n, x ≠ 0 ∧ (x : Fin n → ℝ) ∈ realBox r := by
  have hfinrank : Module.finrank ℝ (Fin n → ℝ) = n := by
    simp
  have hM :
      volume (ZSpan.fundamentalDomain (Pi.basisFun ℝ (Fin n))) *
          2 ^ Module.finrank ℝ (Fin n → ℝ) ≤ volume (realBox r) := by
    rw [standardLattice_covolume, one_mul, hfinrank]
    exact hvol
  obtain ⟨x, hx0, hxr⟩ :=
    MeasureTheory.exists_ne_zero_mem_lattice_of_measure_mul_two_pow_le_measure
      (standardLattice_fundamentalDomain n) (realBox_symmetric r)
      (realBox_convex r) (realBox_compact r) hM
  exact ⟨x, hx0, hxr⟩

/-! ### The denominator lattice `6⁻ᵏ ℤⁿ` -/

/-- The Archimedean scaling factor at denominator level `k`. -/
noncomputable def denominatorScale (k : ℕ) : ℝ := (denominator k : ℝ)⁻¹

theorem denominatorScale_pos (k : ℕ) : 0 < denominatorScale k := by
  apply inv_pos.mpr
  exact_mod_cast denominator_pos k

theorem denominatorScale_ne_zero (k : ℕ) : denominatorScale k ≠ 0 :=
  (denominatorScale_pos k).ne'

/-- The basis `(6⁻ᵏ e_i)_i` of `ℝⁿ`. -/
noncomputable def denominatorBasis (n k : ℕ) : Basis (Fin n) ℝ (Fin n → ℝ) :=
  (Pi.basisFun ℝ (Fin n)).isUnitSMul fun _ ↦
    isUnit_iff_ne_zero.mpr (denominatorScale_ne_zero k)

@[simp] theorem denominatorBasis_apply (n k : ℕ) (i : Fin n) :
    denominatorBasis n k i = denominatorScale k • Pi.basisFun ℝ (Fin n) i := by
  exact Basis.isUnitSMul_apply _ i

/-- The real lattice generated by the level-`k` `ℤ[1/6]` points. -/
def denominatorRealLattice (n k : ℕ) : AddSubgroup (Fin n → ℝ) :=
  (Submodule.span ℤ (Set.range (denominatorBasis n k))).toAddSubgroup

noncomputable instance denominatorRealLattice_countable (n k : ℕ) :
    Countable (denominatorRealLattice n k) := by
  change Countable (Submodule.span ℤ (Set.range (denominatorBasis n k)))
  infer_instance

noncomputable instance denominatorRealLattice_discrete (n k : ℕ) :
    DiscreteTopology (denominatorRealLattice n k) := by
  change DiscreteTopology (Submodule.span ℤ (Set.range (denominatorBasis n k)))
  infer_instance

theorem denominatorRealLattice_fundamentalDomain (n k : ℕ) :
    IsAddFundamentalDomain (denominatorRealLattice n k)
      (ZSpan.fundamentalDomain (denominatorBasis n k)) volume := by
  exact ZSpan.isAddFundamentalDomain' (denominatorBasis n k) volume

/-- The exact covolume of `6⁻ᵏ ℤⁿ` is `(6⁻ᵏ)ⁿ`.  This is the
Archimedean index factor which cancels the two finite-place denominator
factors in the adelic argument. -/
theorem denominatorRealLattice_covolume (n k : ℕ) :
    volume (ZSpan.fundamentalDomain (denominatorBasis n k)) =
      ENNReal.ofReal (denominatorScale k ^ n) := by
  rw [ZSpan.measure_fundamentalDomain (denominatorBasis n k) volume
    (Pi.basisFun ℝ (Fin n)), standardLattice_covolume, mul_one]
  have hdet :
      (Pi.basisFun ℝ (Fin n)).det (denominatorBasis n k) =
        denominatorScale k ^ n := by
    rw [denominatorBasis, Basis.det_isUnitSMul]
    simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  rw [hdet, abs_of_pos (pow_pos (denominatorScale_pos k) n)]

/-- Minkowski for `6⁻ᵏ ℤⁿ`, with the exact covolume rather than an
unspecified lattice constant. -/
theorem exists_nonzero_denominatorLattice_mem_realBox {n : ℕ} (k : ℕ)
    (r : Fin n → ℝ)
    (hvol : ENNReal.ofReal (denominatorScale k ^ n) * (2 : ℝ≥0∞) ^ n <
      volume (realBox r)) :
    ∃ x : denominatorRealLattice n k,
      x ≠ 0 ∧ (x : Fin n → ℝ) ∈ realBox r := by
  have hfinrank : Module.finrank ℝ (Fin n → ℝ) = n := by simp
  have hM :
      volume (ZSpan.fundamentalDomain (denominatorBasis n k)) *
          2 ^ Module.finrank ℝ (Fin n → ℝ) < volume (realBox r) := by
    rw [denominatorRealLattice_covolume, hfinrank]
    exact hvol
  obtain ⟨x, hx0, hxr⟩ :=
    MeasureTheory.exists_ne_zero_mem_lattice_of_measure_mul_two_pow_lt_measure
      (denominatorRealLattice_fundamentalDomain n k) (realBox_symmetric r)
      (realBox_convex r) hM
  exact ⟨x, hx0, hxr⟩

/-- Rational form of the denominator-lattice Minkowski theorem.  Its witness
is an actual point of `6⁻ᵏ ℤⁿ`, not merely an element of an abstract real
lattice. -/
theorem exists_nonzero_denominatorPoint_mem_realBox {n : ℕ} (k : ℕ)
    (r : Fin n → ℝ)
    (hvol : ENNReal.ofReal (denominatorScale k ^ n) * (2 : ℝ≥0∞) ^ n <
      volume (realBox r)) :
    ∃ q : RatVector n, q ≠ 0 ∧ InDenominatorLattice k q ∧
      (fun i ↦ (q i : ℝ)) ∈ realBox r := by
  obtain ⟨x, hx0, hxr⟩ := exists_nonzero_denominatorLattice_mem_realBox k r hvol
  have hxmem : (x : Fin n → ℝ) ∈
      Submodule.span ℤ (Set.range (denominatorBasis n k)) := x.property
  have hcoord := ((denominatorBasis n k).mem_span_iff_repr_mem ℤ _).mp hxmem
  choose z hz using hcoord
  let q : RatVector n := fun i ↦ (z i : ℚ) / denominator k
  have hcast : (fun i ↦ (q i : ℝ)) = (x : Fin n → ℝ) := by
    funext j
    calc
      (q j : ℝ) = (z j : ℝ) * denominatorScale k := by
        simp [q, denominatorScale, div_eq_mul_inv]
      _ = ∑ i, ((denominatorBasis n k).repr (x : Fin n → ℝ) i) *
          denominatorBasis n k i j := by
        classical
        simp_rw [← hz]
        simp [denominatorBasis_apply, denominatorScale, Pi.basisFun_apply,
          Pi.single_apply]
      _ = (x : Fin n → ℝ) j := by
        simpa only [Pi.smul_apply, smul_eq_mul, Finset.sum_apply] using
          congrFun ((denominatorBasis n k).sum_repr (x : Fin n → ℝ)) j
  refine ⟨q, ?_, ⟨z, fun i ↦ rfl⟩, ?_⟩
  · intro hq
    apply hx0
    apply Subtype.ext
    rw [← hcast, hq]
    funext i
    simp
  · rw [hcast]
    exact hxr

/-! ### Successive-minimum product certificates -/

/-- A concrete upper certificate for the product of the successive minima of
a symmetric coordinate box with respect to a specified lattice: it gives `n`
independent lattice points, the scale at which each enters the box, and a
bound for the product of those scales. -/
structure SuccessiveProductCertificate {n : ℕ} (Λ : AddSubgroup (Fin n → ℝ))
    (r : Fin n → ℝ) (B : ℝ) where
  scale : Fin n → ℝ
  point : Fin n → Fin n → ℝ
  scale_nonneg : ∀ i, 0 ≤ scale i
  point_mem : ∀ i, point i ∈ Λ
  independent : LinearIndependent ℝ point
  mem_scaledBox : ∀ i, point i ∈ realBox (scale i • r)
  product_le : ∏ i, scale i ≤ B

/-- The standard coordinate points supply the sharp product certificate
`∏ r_i⁻¹` for a positive coordinate box. -/
noncomputable def realBoxSuccessiveProductCertificate {n : ℕ} (r : Fin n → ℝ)
    (hr : ∀ i, 0 < r i) :
    SuccessiveProductCertificate (standardLattice n) r ((∏ i, r i)⁻¹) := by
  let s : Fin n → ℝ := fun i ↦ (r i)⁻¹
  let e : Fin n → Fin n → ℝ := fun i ↦ Pi.single i 1
  refine
    { scale := s
      point := e
      scale_nonneg := fun i ↦ (inv_pos.mpr (hr i)).le
      point_mem := ?_
      independent := ?_
      mem_scaledBox := ?_
      product_le := ?_ }
  · intro i
    change e i ∈ Submodule.span ℤ (Set.range (Pi.basisFun ℝ (Fin n)))
    have hi : Pi.basisFun ℝ (Fin n) i ∈
        Submodule.span ℤ (Set.range (Pi.basisFun ℝ (Fin n))) :=
      Submodule.subset_span (Set.mem_range_self i)
    simpa [e, Pi.basisFun_apply] using hi
  · have he : e = Pi.basisFun ℝ (Fin n) := by
      funext i j
      simp [e, Pi.basisFun_apply]
    rw [he]
    exact (Pi.basisFun ℝ (Fin n)).linearIndependent
  · intro i
    constructor <;> intro j
    · by_cases hji : j = i
      · subst j
        simp [e, s, (hr i).ne']
      · have hnonneg : 0 ≤ s i * r j :=
          mul_nonneg (inv_nonneg.mpr (hr i).le) (hr j).le
        simp [e, s, hji, hnonneg]
    · by_cases hji : j = i
      · subst j
        simp [e, s, (hr i).ne']
      · have hnonneg : 0 ≤ s i * r j :=
          mul_nonneg (inv_nonneg.mpr (hr i).le) (hr j).le
        simp [e, s, hji, hnonneg]
  · change (∏ i, (r i)⁻¹) ≤ (∏ i, r i)⁻¹
    rw [← Finset.prod_inv_distrib]

/-- A positive coordinate box admits a sharp upper certificate for the
product of its successive minima. -/
theorem realBox_has_successiveProductCertificate {n : ℕ} (r : Fin n → ℝ)
    (hr : ∀ i, 0 < r i) :
    Nonempty (SuccessiveProductCertificate (standardLattice n) r ((∏ i, r i)⁻¹)) :=
  ⟨realBoxSuccessiveProductCertificate r hr⟩

/-- In the dimensions occurring after dehomogenizing an equation with at
most six terms, the preceding certificate is immediately available. -/
theorem realBox_has_successiveProductCertificate_dim_le_five {n : ℕ} (_hn : n ≤ 5)
    (r : Fin n → ℝ) (hr : ∀ i, 0 < r i) :
    Nonempty (SuccessiveProductCertificate (standardLattice n) r ((∏ i, r i)⁻¹)) :=
  realBox_has_successiveProductCertificate r hr

/-- The sharp coordinate certificate for the denominator lattice.  Its
product is the covolume factor `(6⁻ᵏ)ⁿ` divided by the product of the box
radii. -/
noncomputable def denominatorRealBoxSuccessiveProductCertificate {n : ℕ}
    (k : ℕ) (r : Fin n → ℝ) (hr : ∀ i, 0 < r i) :
    SuccessiveProductCertificate (denominatorRealLattice n k) r
      (denominatorScale k ^ n * (∏ i, r i)⁻¹) := by
  let s : Fin n → ℝ := fun i ↦ denominatorScale k * (r i)⁻¹
  let e : Fin n → Fin n → ℝ := denominatorBasis n k
  refine
    { scale := s
      point := e
      scale_nonneg := fun i ↦ mul_nonneg (denominatorScale_pos k).le
        (inv_nonneg.mpr (hr i).le)
      point_mem := ?_
      independent := (denominatorBasis n k).linearIndependent
      mem_scaledBox := ?_
      product_le := ?_ }
  · intro i
    exact Submodule.subset_span (R := ℤ) (Set.mem_range_self i)
  · intro i
    constructor <;> intro j
    · by_cases hji : j = i
      · subst j
        simp [e, s, denominatorBasis_apply, (hr i).ne',
          (denominatorScale_pos k).le]
      · have hnonneg : 0 ≤ s i * r j :=
          mul_nonneg (mul_nonneg (denominatorScale_pos k).le
            (inv_nonneg.mpr (hr i).le)) (hr j).le
        simp [e, s, denominatorBasis_apply, Pi.basisFun_apply, hji, hnonneg]
    · by_cases hji : j = i
      · subst j
        simp [e, s, denominatorBasis_apply, (hr i).ne']
      · have hnonneg : 0 ≤ s i * r j :=
          mul_nonneg (mul_nonneg (denominatorScale_pos k).le
            (inv_nonneg.mpr (hr i).le)) (hr j).le
        simp [e, s, denominatorBasis_apply, Pi.basisFun_apply, hji, hnonneg]
  · change (∏ i, denominatorScale k * (r i)⁻¹) ≤
      denominatorScale k ^ n * (∏ i, r i)⁻¹
    rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ,
      Fintype.card_fin, ← Finset.prod_inv_distrib]

theorem denominatorRealBox_has_successiveProductCertificate {n : ℕ}
    (k : ℕ) (r : Fin n → ℝ) (hr : ∀ i, 0 < r i) :
    Nonempty (SuccessiveProductCertificate (denominatorRealLattice n k) r
      (denominatorScale k ^ n * (∏ i, r i)⁻¹)) :=
  ⟨denominatorRealBoxSuccessiveProductCertificate k r hr⟩

/-! ## Explicit full-rank witnesses in dimensions used by the application -/

/-- The rational standard coordinate vector. -/
def ratBasisVector {n : ℕ} (i : Fin n) : RatVector n :=
  Pi.single i 1

theorem ratBasisVector_linearIndependent (n : ℕ) :
    LinearIndependent ℚ (ratBasisVector : Fin n → RatVector n) := by
  have hfun : (ratBasisVector : Fin n → RatVector n) = Pi.basisFun ℚ (Fin n) := by
    funext i j
    simp [ratBasisVector, Pi.basisFun_apply]
  rw [hfun]
  exact (Pi.basisFun ℚ (Fin n)).linearIndependent

theorem ratBasisVector_in_denominatorLattice {n k : ℕ} (i : Fin n) :
    InDenominatorLattice k (ratBasisVector i) := by
  refine ⟨fun j ↦ if j = i then denominator k else 0, fun j ↦ ?_⟩
  classical
  by_cases hji : j = i
  · subst j
    simp [ratBasisVector, denominator_ne_zero]
  · simp [ratBasisVector, hji]

/-- A direct full-rank criterion for an approximation domain.  It is often
used after determinant estimates have shown that all coordinate vectors lie
in the enlarged local box. -/
theorem approximationDomain_hasFullRank_of_basis {n k : ℕ}
    (L : RationalPlace → Fin n → ratLinearForm n) (c : LocalRadii n)
    (hbasis : ∀ j v i, placeNorm v (L v i j) ≤ c v i) :
    HasRankAtLeast (approximationDomain k L c) n := by
  refine ⟨ratBasisVector, ratBasisVector_linearIndependent n, fun j ↦ ?_⟩
  refine ⟨ratBasisVector_in_denominatorLattice j, fun v i ↦ ?_⟩
  have heval : eval (L v i) (ratBasisVector j) = L v i j := by
    classical
    simp [eval, ratBasisVector, Pi.single_apply]
  rw [heval]
  exact hbasis j v i

/-- Dimension-specialized wrappers used by the at-most-six-term unit
equations (after dehomogenizing, `n ≤ 5`). -/
theorem approximationDomain_hasFullRank_dim_le_five {n k : ℕ} (_hn : n ≤ 5)
    (L : RationalPlace → Fin n → ratLinearForm n) (c : LocalRadii n)
    (hbasis : ∀ j v i, placeNorm v (L v i j) ≤ c v i) :
    HasRankAtLeast (approximationDomain k L c) n := by
  exact approximationDomain_hasFullRank_of_basis L c hbasis

theorem approximationDomain_hasFullRank_dim_one (k : ℕ)
    (L : RationalPlace → Fin 1 → ratLinearForm 1) (c : LocalRadii 1)
    (hbasis : ∀ j v i, placeNorm v (L v i j) ≤ c v i) :
    HasRankAtLeast (approximationDomain k L c) 1 :=
  approximationDomain_hasFullRank_dim_le_five (by omega) L c hbasis

theorem approximationDomain_hasFullRank_dim_two (k : ℕ)
    (L : RationalPlace → Fin 2 → ratLinearForm 2) (c : LocalRadii 2)
    (hbasis : ∀ j v i, placeNorm v (L v i j) ≤ c v i) :
    HasRankAtLeast (approximationDomain k L c) 2 :=
  approximationDomain_hasFullRank_dim_le_five (by omega) L c hbasis

theorem approximationDomain_hasFullRank_dim_three (k : ℕ)
    (L : RationalPlace → Fin 3 → ratLinearForm 3) (c : LocalRadii 3)
    (hbasis : ∀ j v i, placeNorm v (L v i j) ≤ c v i) :
    HasRankAtLeast (approximationDomain k L c) 3 :=
  approximationDomain_hasFullRank_dim_le_five (by omega) L c hbasis

theorem approximationDomain_hasFullRank_dim_four (k : ℕ)
    (L : RationalPlace → Fin 4 → ratLinearForm 4) (c : LocalRadii 4)
    (hbasis : ∀ j v i, placeNorm v (L v i j) ≤ c v i) :
    HasRankAtLeast (approximationDomain k L c) 4 :=
  approximationDomain_hasFullRank_dim_le_five (by omega) L c hbasis

theorem approximationDomain_hasFullRank_dim_five (k : ℕ)
    (L : RationalPlace → Fin 5 → ratLinearForm 5) (c : LocalRadii 5)
    (hbasis : ∀ j v i, placeNorm v (L v i j) ≤ c v i) :
    HasRankAtLeast (approximationDomain k L c) 5 :=
  approximationDomain_hasFullRank_dim_le_five (by omega) L c hbasis

end Erdos407.AdelicMinkowski

#print axioms Erdos407.AdelicMinkowski.exists_nonzero_standardLattice_mem_realBox
#print axioms Erdos407.AdelicMinkowski.denominatorRealLattice_covolume
#print axioms Erdos407.AdelicMinkowski.exists_nonzero_denominatorPoint_mem_realBox
#print axioms Erdos407.AdelicMinkowski.realBox_has_successiveProductCertificate
#print axioms Erdos407.AdelicMinkowski.denominatorRealBox_has_successiveProductCertificate
#print axioms Erdos407.AdelicMinkowski.radiiProduct_scale
#print axioms Erdos407.AdelicMinkowski.approximationDomain_hasFullRank_dim_le_five
