import Mathlib.FieldTheory.IntermediateField.Adjoin.Algebra
import Mathlib.LinearAlgebra.Basis.Defs
import Mathlib.LinearAlgebra.Dimension.OrzechProperty
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-!
# The monomial basis of the thirteenth-root extension

For a finite family `beta i` with `beta i ^ 13` rational, the monomials with
exponents in `Fin 13` span the generated field.  For distinct rational-prime
radicands, the exact degree theorem in `Kummer.lean` then makes them a basis.
-/

open scoped BigOperators

noncomputable section

namespace Erdos240.Kummer

open Finset

/-- A bounded-exponent monomial in the chosen thirteenth roots. -/
def thirteenthRootMonomial {ι Ω : Type*} [Fintype ι]
    [CommMonoid Ω] (beta : ι → Ω) (e : ι → Fin 13) : Ω :=
  ∏ i, beta i ^ (e i : ℕ)

/-- Coordinatewise addition of exponent vectors, reduced modulo `13`. -/
def exponentAddMod13 {ι : Type*} (e f : ι → Fin 13) : ι → Fin 13 :=
  fun i ↦ ⟨((e i : ℕ) + (f i : ℕ)) % 13, Nat.mod_lt _ (by norm_num)⟩

/-- The rational coefficient produced by the carries in coordinatewise
addition of two exponent vectors. -/
def exponentCarry13 {ι : Type*} [Fintype ι]
    (p : ι → ℕ) (e f : ι → Fin 13) : ℚ :=
  ∏ i, (p i : ℚ) ^ (((e i : ℕ) + (f i : ℕ)) / 13)

theorem pow_eq_map_pow_div_mul_pow_mod13
    {Ω : Type*} [Field Ω] [Algebra ℚ Ω]
    {x : Ω} {c : ℚ} (hx : x ^ 13 = algebraMap ℚ Ω c) (n : ℕ) :
    x ^ n = algebraMap ℚ Ω (c ^ (n / 13)) * x ^ (n % 13) := by
  nth_rw 1 [← Nat.mod_add_div n 13]
  rw [pow_add, pow_mul, hx, map_pow, mul_comm]

theorem thirteenthRootMonomial_mul
    {ι Ω : Type*} [Fintype ι]
    [Field Ω] [Algebra ℚ Ω]
    (p : ι → ℕ) (beta : ι → Ω)
    (hbeta : ∀ i, beta i ^ 13 = algebraMap ℚ Ω (p i : ℚ))
    (e f : ι → Fin 13) :
    thirteenthRootMonomial beta e * thirteenthRootMonomial beta f =
      algebraMap ℚ Ω (exponentCarry13 p e f) *
        thirteenthRootMonomial beta (exponentAddMod13 e f) := by
  rw [thirteenthRootMonomial, thirteenthRootMonomial, ← Finset.prod_mul_distrib]
  simp_rw [← pow_add]
  rw [Finset.prod_congr rfl fun i _ ↦
    pow_eq_map_pow_div_mul_pow_mod13 (hbeta i) _]
  rw [Finset.prod_mul_distrib, ← map_prod]
  rfl

/-- The rational span of the bounded-exponent monomials. -/
def thirteenthRootMonomialSpan {ι Ω : Type*} [Fintype ι]
    [Field Ω] [Algebra ℚ Ω] (beta : ι → Ω) : Submodule ℚ Ω :=
  Submodule.span ℚ (Set.range (thirteenthRootMonomial beta))

theorem thirteenthRootMonomial_mem_span
    {ι Ω : Type*} [Fintype ι]
    [Field Ω] [Algebra ℚ Ω] (beta : ι → Ω) (e : ι → Fin 13) :
    thirteenthRootMonomial beta e ∈ thirteenthRootMonomialSpan beta :=
  Submodule.subset_span (Set.mem_range_self e)

theorem one_mem_thirteenthRootMonomialSpan
    {ι Ω : Type*} [Fintype ι]
    [Field Ω] [Algebra ℚ Ω] (beta : ι → Ω) :
    (1 : Ω) ∈ thirteenthRootMonomialSpan beta := by
  simpa [thirteenthRootMonomial] using
    (thirteenthRootMonomial_mem_span beta (fun _ ↦ (0 : Fin 13)))

theorem mul_mem_thirteenthRootMonomialSpan
    {ι Ω : Type*} [Fintype ι]
    [Field Ω] [Algebra ℚ Ω]
    (p : ι → ℕ) (beta : ι → Ω)
    (hbeta : ∀ i, beta i ^ 13 = algebraMap ℚ Ω (p i : ℚ))
    {x y : Ω} (hx : x ∈ thirteenthRootMonomialSpan beta)
    (hy : y ∈ thirteenthRootMonomialSpan beta) :
    x * y ∈ thirteenthRootMonomialSpan beta := by
  apply (show thirteenthRootMonomialSpan beta *
      thirteenthRootMonomialSpan beta ≤ thirteenthRootMonomialSpan beta from ?_)
    (Submodule.mul_mem_mul hx hy)
  rw [thirteenthRootMonomialSpan, Submodule.span_mul_span]
  apply Submodule.span_le.mpr
  intro z hz
  obtain ⟨u, ⟨e, rfl⟩, v, ⟨f, rfl⟩, rfl⟩ := Set.mem_mul.mp hz
  rw [thirteenthRootMonomial_mul p beta hbeta e f, ← Algebra.smul_def]
  exact Submodule.smul_mem _ _
    (thirteenthRootMonomial_mem_span beta (exponentAddMod13 e f))

/-- The monomial span, regarded as a subalgebra using the radical equations. -/
def thirteenthRootMonomialSubalgebra
    {ι Ω : Type*} [Fintype ι]
    [Field Ω] [Algebra ℚ Ω]
    (p : ι → ℕ) (beta : ι → Ω)
    (hbeta : ∀ i, beta i ^ 13 = algebraMap ℚ Ω (p i : ℚ)) :
    Subalgebra ℚ Ω where
  carrier := thirteenthRootMonomialSpan beta
  add_mem' := Submodule.add_mem _
  zero_mem' := Submodule.zero_mem _
  mul_mem' := mul_mem_thirteenthRootMonomialSpan p beta hbeta
  algebraMap_mem' r := by
    simpa [Algebra.smul_def] using
      (Submodule.smul_mem (thirteenthRootMonomialSpan beta) r
        (one_mem_thirteenthRootMonomialSpan beta))

/-- The exponent vector which is `1` in coordinate `i` and `0` elsewhere. -/
def singleExponent13 {ι : Type*} [DecidableEq ι] (i : ι) : ι → Fin 13 :=
  fun j ↦ if j = i then 1 else 0

@[simp]
theorem thirteenthRootMonomial_singleExponent13
    {ι Ω : Type*} [Fintype ι] [DecidableEq ι]
    [CommMonoid Ω] (beta : ι → Ω) (i : ι) :
    thirteenthRootMonomial beta (singleExponent13 i) = beta i := by
  rw [thirteenthRootMonomial]
  rw [Finset.prod_eq_single i]
  · simp [singleExponent13]
  · intro j hj hji
    simp [singleExponent13, hji]
  · simp

theorem thirteenthRootMonomial_mem_adjoin
    {ι Ω : Type*} [Fintype ι]
    [Field Ω] [Algebra ℚ Ω]
    (beta : ι → Ω) (e : ι → Fin 13) :
    thirteenthRootMonomial beta e ∈ Algebra.adjoin ℚ (Set.range beta) := by
  apply Subalgebra.prod_mem
  intro i hi
  exact Subalgebra.pow_mem _ (Algebra.subset_adjoin (Set.mem_range_self i)) _

theorem thirteenthRootMonomialSubalgebra_eq_adjoin
    {ι Ω : Type*} [Fintype ι] [DecidableEq ι]
    [Field Ω] [Algebra ℚ Ω]
    (p : ι → ℕ) (beta : ι → Ω)
    (hbeta : ∀ i, beta i ^ 13 = algebraMap ℚ Ω (p i : ℚ)) :
    thirteenthRootMonomialSubalgebra p beta hbeta =
      Algebra.adjoin ℚ (Set.range beta) := by
  apply le_antisymm
  · intro x hx
    change x ∈ thirteenthRootMonomialSpan beta at hx
    apply (show thirteenthRootMonomialSpan beta ≤
      (Algebra.adjoin ℚ (Set.range beta)).toSubmodule from ?_) hx
    apply Submodule.span_le.mpr
    rintro _ ⟨e, rfl⟩
    exact thirteenthRootMonomial_mem_adjoin beta e
  · apply Algebra.adjoin_le
    rintro _ ⟨i, rfl⟩
    change beta i ∈ thirteenthRootMonomialSpan beta
    rw [← thirteenthRootMonomial_singleExponent13 beta i]
    exact thirteenthRootMonomial_mem_span beta (singleExponent13 i)

theorem thirteenthRootMonomialSpan_eq_adjoin_toSubmodule
    {ι Ω : Type*} [Fintype ι] [DecidableEq ι]
    [Field Ω] [Algebra ℚ Ω] [Algebra.IsAlgebraic ℚ Ω]
    (p : ι → ℕ) (beta : ι → Ω)
    (hbeta : ∀ i, beta i ^ 13 = algebraMap ℚ Ω (p i : ℚ)) :
    thirteenthRootMonomialSpan beta =
      (IntermediateField.adjoin ℚ (Set.range beta)).toSubmodule := by
  have hsubalg : thirteenthRootMonomialSubalgebra p beta hbeta =
      (IntermediateField.adjoin ℚ (Set.range beta)).toSubalgebra :=
    (thirteenthRootMonomialSubalgebra_eq_adjoin p beta hbeta).trans
      (IntermediateField.adjoin_toSubalgebra (Set.range beta)).symm
  exact congrArg Subalgebra.toSubmodule hsubalg

theorem linearIndependent_thirteenthRootMonomials_of_finrank
    {ι Ω : Type*} [Fintype ι] [DecidableEq ι]
    [Field Ω] [Algebra ℚ Ω] [Algebra.IsAlgebraic ℚ Ω]
    (p : ι → ℕ) (beta : ι → Ω)
    (hbeta : ∀ i, beta i ^ 13 = algebraMap ℚ Ω (p i : ℚ))
    (hfinrank : Module.finrank ℚ
        (IntermediateField.adjoin ℚ (Set.range beta)) =
      13 ^ Fintype.card ι) :
    LinearIndependent ℚ (thirteenthRootMonomial beta) := by
  rw [linearIndependent_iff_card_eq_finrank_span]
  change Fintype.card (ι → Fin 13) =
    Module.finrank ℚ (thirteenthRootMonomialSpan beta)
  rw [thirteenthRootMonomialSpan_eq_adjoin_toSubmodule p beta hbeta]
  change Fintype.card (ι → Fin 13) = Module.finrank ℚ
    (IntermediateField.adjoin ℚ (Set.range beta))
  rw [hfinrank]
  simp

/-- A bounded-exponent monomial, regarded as an element of the field generated
by the chosen radicals. -/
def thirteenthRootMonomialInAdjoin
    {ι Ω : Type*} [Fintype ι]
    [Field Ω] [Algebra ℚ Ω]
    (beta : ι → Ω) (e : ι → Fin 13) :
    IntermediateField.adjoin ℚ (Set.range beta) :=
  ⟨thirteenthRootMonomial beta e, by
    apply (IntermediateField.adjoin ℚ (Set.range beta)).prod_mem
    intro i hi
    exact (IntermediateField.adjoin ℚ (Set.range beta)).toSubfield.pow_mem
      (IntermediateField.subset_adjoin ℚ _ (Set.mem_range_self i)) (e i : ℕ)⟩

@[simp]
theorem coe_thirteenthRootMonomialInAdjoin
    {ι Ω : Type*} [Fintype ι]
    [Field Ω] [Algebra ℚ Ω]
    (beta : ι → Ω) (e : ι → Fin 13) :
    (thirteenthRootMonomialInAdjoin beta e : Ω) =
      thirteenthRootMonomial beta e :=
  rfl

theorem linearIndependent_thirteenthRootMonomialsInAdjoin_of_finrank
    {ι Ω : Type*} [Fintype ι] [DecidableEq ι]
    [Field Ω] [Algebra ℚ Ω] [Algebra.IsAlgebraic ℚ Ω]
    (p : ι → ℕ) (beta : ι → Ω)
    (hbeta : ∀ i, beta i ^ 13 = algebraMap ℚ Ω (p i : ℚ))
    (hfinrank : Module.finrank ℚ
        (IntermediateField.adjoin ℚ (Set.range beta)) =
      13 ^ Fintype.card ι) :
    LinearIndependent ℚ (thirteenthRootMonomialInAdjoin beta) := by
  rw [Fintype.linearIndependent_iff]
  intro g hg i
  have hsum := linearIndependent_thirteenthRootMonomials_of_finrank
    p beta hbeta hfinrank
  rw [Fintype.linearIndependent_iff] at hsum
  apply hsum g
  simpa using congrArg Subtype.val hg

/-- The exact monomial basis of the field generated by a family of radicals,
assuming the expected degree formula. -/
noncomputable def thirteenthRootMonomialBasisOfFinrank
    {ι Ω : Type*} [Fintype ι] [DecidableEq ι]
    [Field Ω] [Algebra ℚ Ω] [Algebra.IsAlgebraic ℚ Ω]
    (p : ι → ℕ) (beta : ι → Ω)
    (hbeta : ∀ i, beta i ^ 13 = algebraMap ℚ Ω (p i : ℚ))
    (hfinrank : Module.finrank ℚ
        (IntermediateField.adjoin ℚ (Set.range beta)) =
      13 ^ Fintype.card ι) :
    Module.Basis (ι → Fin 13) ℚ
      (IntermediateField.adjoin ℚ (Set.range beta)) := by
  letI : FiniteDimensional ℚ
      (IntermediateField.adjoin ℚ (Set.range beta)) :=
    FiniteDimensional.of_finrank_pos (by
      rw [hfinrank]
      positivity)
  exact basisOfLinearIndependentOfCardEqFinrank'
    (thirteenthRootMonomialInAdjoin beta)
    (linearIndependent_thirteenthRootMonomialsInAdjoin_of_finrank
      p beta hbeta hfinrank)
    (by rw [hfinrank]; simp)

@[simp]
theorem coe_thirteenthRootMonomialBasisOfFinrank
    {ι Ω : Type*} [Fintype ι] [DecidableEq ι]
    [Field Ω] [Algebra ℚ Ω] [Algebra.IsAlgebraic ℚ Ω]
    (p : ι → ℕ) (beta : ι → Ω)
    (hbeta : ∀ i, beta i ^ 13 = algebraMap ℚ Ω (p i : ℚ))
    (hfinrank : Module.finrank ℚ
        (IntermediateField.adjoin ℚ (Set.range beta)) =
      13 ^ Fintype.card ι) :
    ⇑(thirteenthRootMonomialBasisOfFinrank p beta hbeta hfinrank) =
      thirteenthRootMonomialInAdjoin beta := by
  simp [thirteenthRootMonomialBasisOfFinrank]

end Erdos240.Kummer
