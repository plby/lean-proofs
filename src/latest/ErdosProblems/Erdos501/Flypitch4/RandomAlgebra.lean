/-
Copyright (c) 2026 The Flypitch Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

The ℵ₂-random algebra.
-/
import Mathlib.Probability.ProductMeasure
import Mathlib.MeasureTheory.Measure.Dirac
import ErdosProblems.Erdos501.Flypitch4.MeasureAlgebra
import ErdosProblems.Erdos501.Flypitch4.Forcing

set_option relaxedAutoImplicit true

/-!
# The `ℵ₂`-random algebra

The *`ℵ₂`-random algebra* is the measure algebra of the product measure on `2^(ℵ₂ × ω)`, i.e.
of the product of `ℵ₂` copies of the fair-coin measure on Cantor space `2^ω`.  Forcing with it
adds `ℵ₂` random reals.

We build, for an arbitrary index type `ι`, the probability space `Ω ι := ι → (ℕ → Bool)` with
the infinite product `μ_random ι` of copies of the fair-coin product measure `cantorMeasure` on
`ℕ → Bool` (`MeasureTheory.Measure.infinitePi`), and set
`randomAlgebra ι := MeasureAlgebra (μ_random ι)` (the `κ`-random algebra for `#ι = κ`).  By
`MeasureAlgebra.lean` this is a nontrivial complete Boolean algebra satisfying the countable
chain condition.  The `ℵ₂`-random algebra is `𝔹_random := randomAlgebra PSet.pSet_aleph2.Type`.

The `ν`-th random real is (the name of) the subset of `ω` whose characteristic function is
`n ↦ χ ν n`, where `χ ν n` is the class of the event `{x | x ν n = true}` (the `n`-th bit of the
`ν`-th coordinate).  The key measure-theoretic fact proved here (`iInf_biimp_χ_eq_bot`) is that
for `ν₁ ≠ ν₂` the event "the `ν₁`-th and `ν₂`-th coordinates agree on all bits" has measure `0`
(it is contained in cylinders of measure `2^{-N}` for every `N`), so that in the Boolean-valued
model the random reals are pairwise distinct.
-/

universe u

open MeasureTheory Set
open scoped ENNReal Flypitch

namespace Flypitch

namespace RandomAlgebra

/-! ### The fair coin -/

/-- The fair-coin measure on `Bool`. -/
noncomputable def fairCoin : Measure Bool := (2 : ℝ≥0∞)⁻¹ • (Measure.dirac true + Measure.dirac false)

lemma fairCoin_apply (s : Set Bool) :
    fairCoin s = 2⁻¹ * (s.indicator 1 true + s.indicator 1 false) := by
  simp only [fairCoin, Measure.smul_apply, Measure.add_apply, Measure.dirac_apply, smul_eq_mul]

@[simp] lemma fairCoin_singleton (b : Bool) : fairCoin {b} = 2⁻¹ := by
  cases b <;> simp [fairCoin_apply]

instance : IsProbabilityMeasure fairCoin := ⟨by
  rw [fairCoin_apply]
  simp only [indicator_univ, Pi.one_apply, one_add_one_eq_two]
  exact ENNReal.inv_mul_cancel two_ne_zero ENNReal.ofNat_ne_top⟩

/-! ### Cantor space with the fair-coin product measure -/

/-- Cantor space `ℕ → Bool` with the product of fair-coin measures. -/
noncomputable def cantorMeasure : Measure (ℕ → Bool) := Measure.infinitePi (fun _ : ℕ => fairCoin)

instance : IsProbabilityMeasure cantorMeasure := by
  unfold cantorMeasure; infer_instance

/-- The cylinder of sequences agreeing with `σ` on the first `N` bits. -/
def cyl (σ : ℕ → Bool) (N : ℕ) : Set (ℕ → Bool) :=
  Set.pi (↑(Finset.range N) : Set ℕ) (fun n => {σ n})

lemma mem_cyl {σ : ℕ → Bool} {N : ℕ} {y : ℕ → Bool} : y ∈ cyl σ N ↔ ∀ n < N, y n = σ n := by
  simp [cyl, Set.mem_pi]

lemma measurableSet_cyl (σ : ℕ → Bool) (N : ℕ) : MeasurableSet (cyl σ N) :=
  MeasurableSet.pi (Finset.range N).countable_toSet (fun _ _ => measurableSet_singleton _)

lemma cantorMeasure_cyl (σ : ℕ → Bool) (N : ℕ) : cantorMeasure (cyl σ N) = 2⁻¹ ^ N := by
  unfold cantorMeasure cyl
  rw [Measure.infinitePi_pi (fun _ : ℕ => fairCoin) (fun _ _ => measurableSet_singleton _)]
  simp [Finset.prod_const]

/-! ### The random algebra of an arbitrary index set

`randomAlgebra ι` is the measure algebra of the product measure on `2^(ι × ω)`; for `#ι = κ` this
is the `κ`-random algebra (the measure algebra of Maharam type `κ`).  The `ℵ₂`-random algebra
`𝔹_random` used to force `¬CH` is the case `ι = PSet.pSet_aleph2.Type`. -/

section general

variable (ι : Type)

/-- The underlying space: `ι` many points of Cantor space, i.e. `2^(ι × ω)`. -/
abbrev Ω : Type := ι → (ℕ → Bool)

/-- The product of `ι` copies of the fair-coin measure on Cantor space, i.e. the fair-coin
product measure on `2^(ι × ω)`. -/
noncomputable def μ_random : Measure (Ω ι) := Measure.infinitePi (fun _ : ι => cantorMeasure)

instance : IsProbabilityMeasure (μ_random ι) := by
  unfold μ_random; infer_instance

end general

end RandomAlgebra

open RandomAlgebra in
/-- The random algebra of the index set `ι`: the measure algebra of the product measure on
`2^(ι × ω)`.  For `#ι = κ` this is the `κ`-random algebra. -/
abbrev randomAlgebra (ι : Type) : Type := MeasureAlgebra (μ_random ι)

noncomputable instance randomAlgebra.instNontrivialCBA (ι : Type) :
    NontrivialCompleteBooleanAlgebra (randomAlgebra ι) :=
  MeasureAlgebra.instNontrivialCompleteBooleanAlgebra

theorem randomAlgebra_CCC (ι : Type) : CCC (randomAlgebra ι) := MeasureAlgebra.CCC_measureAlgebra

/-- The `ℵ₂`-random algebra: the measure algebra of the product measure on `2^(ℵ₂ × ω)`. -/
abbrev 𝔹_random : Type := randomAlgebra PSet.pSet_aleph2.Type

noncomputable instance 𝔹_random.instNontrivialCBA : NontrivialCompleteBooleanAlgebra 𝔹_random :=
  randomAlgebra.instNontrivialCBA _

theorem 𝔹_random_CCC : CCC 𝔹_random := randomAlgebra_CCC _

namespace RandomAlgebra

/-! ### The random bits -/

variable {ι : Type}

/-- The event that the `n`-th bit of the `ν`-th coordinate is `true`. -/
def bit (ν : ι) (n : ℕ) : Set (Ω ι) := {x | x ν n = true}

lemma measurableSet_bit (ν : ι) (n : ℕ) : MeasurableSet (bit ν n) := by
  have h : Measurable (fun x : Ω ι => x ν n) := (measurable_pi_apply n).comp (measurable_pi_apply ν)
  exact h (measurableSet_singleton true)

/-- The `n`-th bit of the `ν`-th random real, as an element of the random algebra. -/
noncomputable def χ (ν : ι) (n : ℕ) : randomAlgebra ι :=
  MeasureAlgebra.mk (μ_random ι) (bit ν n) (measurableSet_bit ν n)

/-- The event that the `ν₁`-th and `ν₂`-th coordinates agree on the first `N` bits. -/
def agree (ν₁ ν₂ : ι) (N : ℕ) : Set (Ω ι) := {x | ∀ n < N, x ν₁ n = x ν₂ n}

/-- Extend `σ : Fin N → Bool` by `false`. -/
def extBool {N : ℕ} (σ : Fin N → Bool) : ℕ → Bool :=
  fun n => if h : n < N then σ ⟨n, h⟩ else false

lemma agree_subset_iUnion (ν₁ ν₂ : ι) (N : ℕ) [DecidableEq ι] :
    agree ν₁ ν₂ N ⊆
      ⋃ σ : Fin N → Bool, Set.pi (↑({ν₁, ν₂} : Finset ι)) (fun _ => cyl (extBool σ) N) := by
  intro x hx
  refine mem_iUnion.mpr ⟨fun i => x ν₁ i, ?_⟩
  simp only [Set.mem_pi, Finset.coe_insert, Finset.coe_singleton, mem_insert_iff, mem_singleton_iff,
    forall_eq_or_imp, forall_eq]
  constructor
  · rw [mem_cyl]; intro n hn; simp [extBool, hn]
  · rw [mem_cyl]; intro n hn; simp only [extBool, hn, dite_true]; exact (hx n hn).symm

lemma μ_random_pi_pair {ν₁ ν₂ : ι} (hne : ν₁ ≠ ν₂)
    [DecidableEq ι] (C : Set (ℕ → Bool)) (hC : MeasurableSet C) :
    μ_random ι (Set.pi (↑({ν₁, ν₂} : Finset ι)) (fun _ => C)) =
      cantorMeasure C * cantorMeasure C := by
  unfold μ_random
  rw [Measure.infinitePi_pi (fun _ : ι => cantorMeasure) (fun _ _ => hC),
    Finset.prod_pair hne]

lemma μ_random_agree_le {ν₁ ν₂ : ι} (hne : ν₁ ≠ ν₂) (N : ℕ) :
    μ_random ι (agree ν₁ ν₂ N) ≤ 2⁻¹ ^ N := by
  classical
  calc μ_random ι (agree ν₁ ν₂ N)
      ≤ μ_random ι (⋃ σ : Fin N → Bool,
          Set.pi (↑({ν₁, ν₂} : Finset ι)) (fun _ => cyl (extBool σ) N)) :=
        measure_mono (agree_subset_iUnion ν₁ ν₂ N)
    _ ≤ ∑ σ : Fin N → Bool,
          μ_random ι (Set.pi (↑({ν₁, ν₂} : Finset ι)) (fun _ => cyl (extBool σ) N)) :=
        measure_iUnion_fintype_le _ _
    _ = ∑ _σ : Fin N → Bool, (2⁻¹ ^ N * 2⁻¹ ^ N : ℝ≥0∞) := by
        apply Finset.sum_congr rfl
        intro σ _
        rw [μ_random_pi_pair hne _ (measurableSet_cyl _ _), cantorMeasure_cyl]
    _ = 2⁻¹ ^ N := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_bool,
          Fintype.card_fin, nsmul_eq_mul, Nat.cast_pow, Nat.cast_ofNat, ← mul_assoc, ← mul_pow,
          ENNReal.mul_inv_cancel two_ne_zero ENNReal.ofNat_ne_top, one_pow, one_mul]

/-- The event that two distinct coordinates agree on all bits is null. -/
lemma μ_random_iInter_agree {ν₁ ν₂ : ι} (hne : ν₁ ≠ ν₂) :
    μ_random ι (⋂ N, agree ν₁ ν₂ N) = 0 := by
  by_contra h
  obtain ⟨N, hN⟩ := ENNReal.exists_inv_two_pow_lt h
  exact absurd ((measure_mono (iInter_subset _ N)).trans (μ_random_agree_le hne N)) (not_le.mpr hN)

/-- The Boolean value "the `ν₁`-th and `ν₂`-th random reals have the same bits" is `⊥`. -/
theorem iInf_biimp_χ_eq_bot {ν₁ ν₂ : ι} (hne : ν₁ ≠ ν₂) :
    (⨅ n : ℕ, biimp (χ ν₁ n) (χ ν₂ n)) = (⊥ : randomAlgebra ι) := by
  simp only [χ, biimp, imp, MeasureAlgebra.mk_compl, MeasureAlgebra.mk_sup, MeasureAlgebra.mk_inf]
  rw [MeasureAlgebra.iInf_mk, ← MeasureAlgebra.meas_eq_zero_iff, MeasureAlgebra.meas_mk]
  apply measure_mono_null _ (μ_random_iInter_agree hne)
  intro x hx
  simp only [mem_iInter, mem_inter_iff, mem_union, mem_compl_iff, bit, mem_setOf_eq] at hx
  simp only [mem_iInter, agree, mem_setOf_eq]
  intro N n _
  have := hx n
  cases h₁ : x ν₁ n <;> cases h₂ : x ν₂ n <;> simp_all

end RandomAlgebra

end Flypitch
