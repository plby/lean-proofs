/- leanprover/lean4:v4.30.0  mathlib v4.30.0 -/
/-
This is a Lean formalization of a solution to Erdős Problem 42.
https://www.erdosproblems.com/forum/thread/42

Informal authors:
- GPT-5.5 Pro
- Harjas Sandhu

Formal authors:
- Codex 5.5
- GPT-5.5 Pro
- Pawan Sasanka Ammanamanchi

URLs:
- https://www.erdosproblems.com/forum/thread/42#post-6370
- https://github.com/Shashi456/erdos-formalizations/blob/main/Erdos/P42/CompactCayley/Proof.lean
- https://github.com/google-deepmind/formal-conjectures/blob/main/FormalConjectures/ErdosProblems/42.lean
- https://raw.githubusercontent.com/Shashi456/erdos-formalizations/refs/heads/main/Erdos/P42/CompactCayley/Proof.lean
-/
/-
**STANDALONE FLAT BUNDLE** of Erdős Problem #42 — compact-Cayley route.

This file is generated from the modular Route B files under `Erdos/P42` and
contains the axiom-free proof of `Erdos42.CompactCayley.compact_cayley_clique`.
Project-local imports are deliberately flattened; only Mathlib imports remain.
-/

import Mathlib
import Mathlib.Algebra.Group.Torsion
import Mathlib.Algebra.Module.CharacterModule
import Mathlib.Algebra.Module.Torsion.Free
import Mathlib.Algebra.Order.Archimedean.Basic
import Mathlib.Algebra.Order.Ring.Pow
import Mathlib.Analysis.Fourier.ZMod
import Mathlib.Analysis.Normed.Group.FunctionSeries
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Int.Interval
import Mathlib.Data.PNat.Basic
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.Real.Sqrt
import Mathlib.GroupTheory.Finiteness
import Mathlib.LinearAlgebra.Finsupp.Defs
import Mathlib.LinearAlgebra.FreeModule.PID
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Group.Arithmetic
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Measure.Haar.Basic
import Mathlib.RingTheory.Finiteness.Defs
import Mathlib.SetTheory.Cardinal.Free
import Mathlib.Tactic
import Mathlib.Topology.Algebra.PontryaginDual
import Mathlib.Topology.ContinuousMap.SecondCountableSpace

attribute [local instance] Classical.propDecidable

/-!
Trust boundary (verified at the bottom with `#print axioms`):
  Mathlib/Lean core only (`propext`, `Classical.choice`, `Quot.sound`).
-/


/-! =============================================================
    Section from: Erdos/P42/Common.lean
    ============================================================= -/

/-
Erdős Problem 42 — shared finite-combinatorial primitives.

`DiffFinset`, `SymmetricFinset`, `CliqueInCayley`, `AvoidsNonzeroDiff`, plus
tiny lemmas that both the Fourier-positive and compact-Cayley routes use. We
work with `Finset` rather than `Set` because Lean's `Set ℕ` subtraction is
truncated.
-/


namespace Erdos42

open Finset

/-- Difference set of two `Finset`s: image of `(a, b) ↦ a - b` over `A ×ˢ B`. -/
def DiffFinset {α : Type*} [DecidableEq α] [Sub α] (A B : Finset α) : Finset α :=
  (A ×ˢ B).image (fun ab => ab.1 - ab.2)

@[simp] lemma mem_diffFinset {α : Type*} [DecidableEq α] [Sub α]
    {A B : Finset α} {x : α} :
    x ∈ DiffFinset A B ↔ ∃ a ∈ A, ∃ b ∈ B, a - b = x := by
  simp [DiffFinset, Finset.mem_image, Finset.mem_product, and_assoc]

/-- A `Finset` is symmetric under negation. -/
def SymmetricFinset {α : Type*} [Neg α] (S : Finset α) : Prop :=
  ∀ x, x ∈ S ↔ -x ∈ S

/-- A `Finset C` is a clique in the Cayley graph on `ZMod p` with allowed
difference set `T`: every pair of distinct vertices in `C` has its difference
in `T`. -/
def CliqueInCayley {p : ℕ} (T C : Finset (ZMod p)) : Prop :=
  ∀ x ∈ C, ∀ y ∈ C, x ≠ y → x - y ∈ T

/-- `A` and `B` share no nonzero difference. -/
def AvoidsNonzeroDiff {α : Type*} [DecidableEq α] [Zero α] [Sub α]
    (A B : Finset α) : Prop :=
  ∀ d ∈ DiffFinset A A, d ∈ DiffFinset B B → d = 0

end Erdos42


/-! =============================================================
    Section from: Erdos/P42/Sidon.lean
    ============================================================= -/

/-
Erdős Problem 42 — Sidon predicates and the elementary cardinality / difference
lemmas every route depends on.

We define `IsSidonInt` over `Finset ℤ` (the natural setting for the analytic
proof) and `IsSidonNat` over `Finset ℕ` / `Set ℕ` (the FC-aligned setting).
Bridge lemmas live in `FC/Local.lean`.
-/


namespace Erdos42

open Finset

/-- A `Finset ℤ` is Sidon iff all unordered pair-sums are distinct, i.e. no
nontrivial additive collision `a₁ + a₂ = a₃ + a₄` with `{a₁, a₂} ≠ {a₃, a₄}`. -/
def IsSidonInt (A : Finset ℤ) : Prop :=
  ∀ ⦃a₁⦄, a₁ ∈ A → ∀ ⦃a₂⦄, a₂ ∈ A → ∀ ⦃a₃⦄, a₃ ∈ A → ∀ ⦃a₄⦄, a₄ ∈ A →
    a₁ + a₂ = a₃ + a₄ → (a₁ = a₃ ∧ a₂ = a₄) ∨ (a₁ = a₄ ∧ a₂ = a₃)

/-- A `Finset ℕ` is Sidon under the same rule. -/
def IsSidonNat (A : Finset ℕ) : Prop :=
  ∀ ⦃a₁⦄, a₁ ∈ A → ∀ ⦃a₂⦄, a₂ ∈ A → ∀ ⦃a₃⦄, a₃ ∈ A → ∀ ⦃a₄⦄, a₄ ∈ A →
    a₁ + a₂ = a₃ + a₄ → (a₁ = a₃ ∧ a₂ = a₄) ∨ (a₁ = a₄ ∧ a₂ = a₃)

/-- A `Finset (ZMod p)` is Sidon under the same rule. -/
def IsSidonZMod {p : ℕ} (A : Finset (ZMod p)) : Prop :=
  ∀ ⦃a₁⦄, a₁ ∈ A → ∀ ⦃a₂⦄, a₂ ∈ A → ∀ ⦃a₃⦄, a₃ ∈ A → ∀ ⦃a₄⦄, a₄ ∈ A →
    a₁ + a₂ = a₃ + a₄ → (a₁ = a₃ ∧ a₂ = a₄) ∨ (a₁ = a₄ ∧ a₂ = a₃)

lemma isSidonInt_empty : IsSidonInt ∅ := by
  intro a₁ ha₁
  simp at ha₁

lemma IsSidonInt.mono {A B : Finset ℤ} (hB : IsSidonInt B) (hAB : A ⊆ B) :
    IsSidonInt A := by
  intro a₁ ha₁ a₂ ha₂ a₃ ha₃ a₄ ha₄ hsum
  exact hB (hAB ha₁) (hAB ha₂) (hAB ha₃) (hAB ha₄) hsum

/-! ## Elementary cardinality bounds (TODO) -/

/-- For `A ⊆ {1, …, N}` Sidon, the nonzero differences `(A - A) \ {0}` have
cardinality at most `2N - 2` (equals `|A|(|A|-1)`). -/
theorem sidon_nonzero_diff_card_le
    (A : Finset ℤ) (N : ℕ)
    (hAint : ∀ a ∈ A, 1 ≤ a ∧ a ≤ (N : ℤ))
    (_hSidon : IsSidonInt A) :
    ((DiffFinset A A).erase 0).card ≤ 2 * N - 2 := by
  classical
  let box : Finset ℤ := (Finset.Icc (1 - (N : ℤ)) ((N : ℤ) - 1)).erase 0
  have hsub : (DiffFinset A A).erase 0 ⊆ box := by
    intro d hd
    rw [Finset.mem_erase] at hd
    rcases hd with ⟨hd0, hdDiff⟩
    rw [mem_diffFinset] at hdDiff
    rcases hdDiff with ⟨a, ha, b, hb, rfl⟩
    obtain ⟨ha1, haN⟩ := hAint a ha
    obtain ⟨hb1, hbN⟩ := hAint b hb
    change a - b ∈ (Finset.Icc (1 - (N : ℤ)) ((N : ℤ) - 1)).erase 0
    rw [Finset.mem_erase, Finset.mem_Icc]
    refine ⟨hd0, ?_, ?_⟩ <;> linarith
  refine (Finset.card_le_card hsub).trans ?_
  by_cases hN : N = 0
  · subst N
    simp [box]
  · have hNpos : 0 < N := Nat.pos_of_ne_zero hN
    have h0 : (0 : ℤ) ∈ Finset.Icc (1 - (N : ℤ)) ((N : ℤ) - 1) := by
      rw [Finset.mem_Icc]
      constructor <;> omega
    have hcard_int :
        ((box.card : ℤ) = (2 * N - 2 : ℕ)) := by
      change
        ((((Finset.Icc (1 - (N : ℤ)) ((N : ℤ) - 1)).erase 0).card : ℤ) =
          (2 * N - 2 : ℕ))
      rw [Finset.card_erase_of_mem h0]
      have hIcc :
          (((Finset.Icc (1 - (N : ℤ)) ((N : ℤ) - 1)).card : ℤ) =
            2 * (N : ℤ) - 1) := by
        rw [Int.card_Icc_of_le]
        · ring
        · omega
      omega
    exact le_of_eq (Int.ofNat_inj.mp hcard_int)

/-- For `A ⊆ {1, …, N}` Sidon, `binomial(|A|, 2) ≤ N - 1`. Standard counting:
the `binomial(|A|, 2)` positive differences are distinct elements of
`{1, …, N-1}`. -/
theorem sidon_choose_two_le_interval
    (A : Finset ℤ) (N : ℕ)
    (hAint : ∀ a ∈ A, 1 ≤ a ∧ a ≤ (N : ℤ))
    (hSidon : IsSidonInt A) :
    Nat.choose A.card 2 ≤ N - 1 := by
  classical
  let f : ℤ × ℤ → ℤ := fun ab => ab.1 - ab.2
  have hmaps : Set.MapsTo f (A.offDiag : Set (ℤ × ℤ)) ((DiffFinset A A).erase 0 : Set ℤ) := by
    intro ab hab
    have habFin : ab ∈ A.offDiag := by simpa using hab
    rw [Finset.mem_offDiag] at habFin
    rcases habFin with ⟨ha, hb, hne⟩
    change ab.1 - ab.2 ∈ (DiffFinset A A).erase 0
    rw [Finset.mem_erase, mem_diffFinset]
    exact ⟨sub_ne_zero.mpr hne, ⟨ab.1, ha, ab.2, hb, rfl⟩⟩
  have hinj : (A.offDiag : Set (ℤ × ℤ)).InjOn f := by
    intro ab hab cd hcd hdiff
    have habFin : ab ∈ A.offDiag := by simpa using hab
    have hcdFin : cd ∈ A.offDiag := by simpa using hcd
    rw [Finset.mem_offDiag] at habFin hcdFin
    rcases habFin with ⟨hab1, hab2, hab_ne⟩
    rcases hcdFin with ⟨hcd1, hcd2, _hcd_ne⟩
    have hsum : ab.1 + cd.2 = cd.1 + ab.2 := by
      dsimp [f] at hdiff
      linarith
    rcases hSidon hab1 hcd2 hcd1 hab2 hsum with h | h
    · exact Prod.ext h.1 h.2.symm
    · exact False.elim (hab_ne h.1)
  have hoff_le :
      A.offDiag.card ≤ ((DiffFinset A A).erase 0).card :=
    Finset.card_le_card_of_injOn f hmaps hinj
  have hordered_le : A.card * A.card - A.card ≤ 2 * N - 2 := by
    rw [← Finset.offDiag_card]
    exact hoff_le.trans (sidon_nonzero_diff_card_le A N hAint hSidon)
  have hdiv :
      (A.card * A.card - A.card) / 2 ≤ (2 * N - 2) / 2 :=
    Nat.div_le_div_right (a := A.card * A.card - A.card) (b := 2 * N - 2) (c := 2)
      hordered_le
  rw [Nat.choose_two_right]
  have hleft : A.card * (A.card - 1) = A.card * A.card - A.card := by
    rw [Nat.mul_sub_one]
  have hright : (2 * N - 2) / 2 = N - 1 := by omega
  simpa [hleft, hright] using hdiv

/-! ## Difference-set helpers -/

lemma diffFinset_erase_zero_card_le_offDiag_card (A : Finset ℤ) :
    ((DiffFinset A A).erase 0).card ≤ A.card * A.card - A.card := by
  classical
  let f : ℤ × ℤ → ℤ := fun ab => ab.1 - ab.2
  have hsub : (DiffFinset A A).erase 0 ⊆ A.offDiag.image f := by
    intro d hd
    rw [Finset.mem_erase, mem_diffFinset] at hd
    rcases hd with ⟨hd0, a, ha, b, hb, rfl⟩
    have hab : a ≠ b := sub_ne_zero.mp hd0
    exact Finset.mem_image.mpr ⟨(a, b), by
      rw [Finset.mem_offDiag]
      exact ⟨ha, hb, hab⟩, rfl⟩
  calc
    ((DiffFinset A A).erase 0).card ≤ (A.offDiag.image f).card := Finset.card_le_card hsub
    _ ≤ A.offDiag.card := Finset.card_image_le
    _ = A.card * A.card - A.card := by rw [Finset.offDiag_card]

lemma diffFinset_self_symmetric (A : Finset ℤ) :
    SymmetricFinset (DiffFinset A A) := by
  intro x
  simp only [mem_diffFinset]
  constructor
  · rintro ⟨a, ha, b, hb, rfl⟩; exact ⟨b, hb, a, ha, by ring⟩
  · rintro ⟨a, ha, b, hb, h⟩; exact ⟨b, hb, a, ha, by linarith⟩

lemma zero_mem_diffFinset_self {A : Finset ℤ} (hA : A.Nonempty) :
    (0 : ℤ) ∈ DiffFinset A A := by
  obtain ⟨a, ha⟩ := hA
  exact mem_diffFinset.mpr ⟨a, ha, a, ha, by ring⟩

end Erdos42


/-! =============================================================
    Section from: Erdos/P42/FiniteFourier.lean
    ============================================================= -/

/-
Erdős Problem 42 — finite-Fourier predicates used by the route-axioms.

These predicates use Mathlib's discrete Fourier transform on `ZMod p`. The
transform `ZMod.dft` is unnormalized, so `normalizedDftCoeff` multiplies by
`p⁻¹`, matching the averaged Fourier coefficients in the compact-Cayley and
Fourier-positive notes.

`FourierLowerIndicator` is used by Route A: lower bound `Re ≥ -ε`.
`FourierUpperIndicator` is used by Route B: upper bound `Re ≤ ε` at
nontrivial characters.
-/


namespace Erdos42

open scoped BigOperators ZMod

/-- Complex-valued indicator of a finite set in `ZMod p`. -/
noncomputable def indicatorC {p : ℕ} (T : Finset (ZMod p)) : ZMod p → ℂ :=
  fun x => if x ∈ T then 1 else 0

/-- Normalized DFT coefficient of an arbitrary complex-valued function on
`ZMod p`. This is the common finite-Fourier primitive needed for both axiom
removal projects; `normalizedDftCoeff` is the indicator-specialized version. -/
noncomputable def normalizedDftFunction {p : ℕ} [NeZero p]
    (f : ZMod p → ℂ) (r : ZMod p) : ℂ :=
  ((p : ℂ)⁻¹) * (ZMod.dft f r)

/-- Normalized DFT coefficient of the indicator of `T`.

Mathlib's `ZMod.dft` is the counting-measure transform
`∑ x, stdAddChar (-(x * r)) • f x`; the compact-Cayley statements use the
averaged coefficient, hence the factor `(p : ℂ)⁻¹`. -/
noncomputable def normalizedDftCoeff {p : ℕ} [NeZero p]
    (T : Finset (ZMod p)) (r : ZMod p) : ℂ :=
  normalizedDftFunction (indicatorC T) r

/-- Normalized Fourier *lower* bound: every character of `ZMod p` evaluated on
`1_F` has real part `≥ -ε`. Used by Route A (Fourier-positive). -/
def FourierLowerIndicator {p : ℕ} [NeZero p] (F : Finset (ZMod p)) (ε : ℝ) : Prop :=
  ∀ r : ZMod p, -(ε : ℝ) ≤ (normalizedDftCoeff F r).re

/-- Normalized Fourier *upper* bound: every nontrivial character of `ZMod p`
evaluated on `1_T` has real part `≤ ε`. Used by Route B (compact Cayley). -/
def FourierUpperIndicator {p : ℕ} [NeZero p] (T : Finset (ZMod p)) (ε : ℝ) : Prop :=
  ∀ r : ZMod p, r ≠ 0 → (normalizedDftCoeff T r).re ≤ ε

lemma normalizedDftFunction_eq_sum {p : ℕ} [NeZero p]
    (f : ZMod p → ℂ) (r : ZMod p) :
    normalizedDftFunction f r =
      ((p : ℂ)⁻¹) * ∑ x : ZMod p, ZMod.stdAddChar (-(x * r)) * f x := by
  rw [normalizedDftFunction, ZMod.dft_apply]
  simp [smul_eq_mul]

lemma normalizedDftFunction_zero_eq_average {p : ℕ} [NeZero p]
    (f : ZMod p → ℂ) :
    normalizedDftFunction f 0 =
      ((p : ℂ)⁻¹) * ∑ x : ZMod p, f x := by
  rw [normalizedDftFunction_eq_sum]
  simp

@[simp] lemma normalizedDftFunction_zero_fun {p : ℕ} [NeZero p]
    (r : ZMod p) :
    normalizedDftFunction (fun _ : ZMod p => 0) r = 0 := by
  rw [normalizedDftFunction_eq_sum]
  simp

lemma normalizedDftFunction_add {p : ℕ} [NeZero p]
    (f g : ZMod p → ℂ) (r : ZMod p) :
    normalizedDftFunction (fun x => f x + g x) r =
      normalizedDftFunction f r + normalizedDftFunction g r := by
  rw [normalizedDftFunction_eq_sum, normalizedDftFunction_eq_sum,
    normalizedDftFunction_eq_sum]
  simp [mul_add, Finset.sum_add_distrib]

lemma normalizedDftFunction_neg {p : ℕ} [NeZero p]
    (f : ZMod p → ℂ) (r : ZMod p) :
    normalizedDftFunction (fun x => -f x) r =
      - normalizedDftFunction f r := by
  rw [normalizedDftFunction_eq_sum, normalizedDftFunction_eq_sum]
  simp [Finset.mul_sum]

lemma normalizedDftFunction_sub {p : ℕ} [NeZero p]
    (f g : ZMod p → ℂ) (r : ZMod p) :
    normalizedDftFunction (fun x => f x - g x) r =
      normalizedDftFunction f r - normalizedDftFunction g r := by
  simp [sub_eq_add_neg, normalizedDftFunction_add, normalizedDftFunction_neg]

lemma normalizedDftFunction_const_mul {p : ℕ} [NeZero p]
    (c : ℂ) (f : ZMod p → ℂ) (r : ZMod p) :
    normalizedDftFunction (fun x => c * f x) r =
      c * normalizedDftFunction f r := by
  rw [normalizedDftFunction_eq_sum, normalizedDftFunction_eq_sum]
  simp [Finset.mul_sum, mul_comm, mul_left_comm, mul_assoc]

lemma normalizedDftCoeff_eq_sum {p : ℕ} [NeZero p]
    (T : Finset (ZMod p)) (r : ZMod p) :
    normalizedDftCoeff T r =
      ((p : ℂ)⁻¹) * ∑ x ∈ T, ZMod.stdAddChar (-(x * r)) := by
  classical
  rw [normalizedDftCoeff, normalizedDftFunction_eq_sum]
  simp [indicatorC]

lemma normalizedDftCoeff_zero_eq_card_div {p : ℕ} [NeZero p]
    (T : Finset (ZMod p)) :
    normalizedDftCoeff T 0 = (T.card : ℂ) / (p : ℂ) := by
  rw [normalizedDftCoeff_eq_sum]
  simp [div_eq_inv_mul]

/-- Fourier inversion in the normalized convention, for arbitrary functions. -/
lemma function_eq_sum_normalizedDftFunction {p : ℕ} [NeZero p]
    (f : ZMod p → ℂ) (x : ZMod p) :
    f x =
      ∑ r : ZMod p, ZMod.stdAddChar (r * x) * normalizedDftFunction f r := by
  classical
  have h :=
    congrFun (LinearEquiv.symm_apply_apply (ZMod.dft : (ZMod p → ℂ) ≃ₗ[ℂ] (ZMod p → ℂ))
      f) x
  calc
    f x =
        ((p : ℂ)⁻¹) * ∑ r : ZMod p,
          ZMod.stdAddChar (r * x) * ZMod.dft f r := by
          simpa [ZMod.invDFT_apply, smul_eq_mul] using h.symm
    _ = ∑ r : ZMod p, ZMod.stdAddChar (r * x) * normalizedDftFunction f r := by
          simp [normalizedDftFunction, Finset.mul_sum, mul_comm, mul_left_comm]

/-- Fourier inversion in the normalization used by the compact-Cayley route. -/
lemma indicatorC_eq_sum_normalizedDftCoeff {p : ℕ} [NeZero p]
    (T : Finset (ZMod p)) (x : ZMod p) :
    indicatorC T x =
      ∑ r : ZMod p, ZMod.stdAddChar (r * x) * normalizedDftCoeff T r := by
  simpa [normalizedDftCoeff] using
    function_eq_sum_normalizedDftFunction (p := p) (indicatorC T) x

lemma sum_stdAddChar_neg_mul_eq_zero_of_ne_zero
    {p : ℕ} [Fact p.Prime] [NeZero p] {r : ZMod p} (hr : r ≠ 0) :
    ∑ x : ZMod p, ZMod.stdAddChar (-(x * r)) = 0 := by
  classical
  have hnontrivial :
      AddChar.mulShift (ZMod.stdAddChar (N := p)) (-r) ≠ 1 :=
    (ZMod.isPrimitive_stdAddChar p) (by simpa using neg_ne_zero.mpr hr)
  have hsum :
      ∑ x : ZMod p, AddChar.mulShift (ZMod.stdAddChar (N := p)) (-r) x = 0 :=
    AddChar.sum_eq_zero_of_ne_one hnontrivial
  simpa [AddChar.mulShift_apply, mul_comm, mul_left_comm, mul_assoc] using hsum

lemma sum_stdAddChar_neg_mul_eq_sum_pos_mul_of_symmetric
    {p : ℕ} [NeZero p] {T : Finset (ZMod p)}
    (hT : SymmetricFinset T) (r : ZMod p) :
    ∑ x ∈ T, ZMod.stdAddChar (-(x * r)) =
      ∑ x ∈ T, ZMod.stdAddChar (x * r) := by
  classical
  refine Finset.sum_bij (fun x hx => -x) ?_ ?_ ?_ ?_
  · intro x hx
    exact (hT x).mp hx
  · intro x₁ hx₁ x₂ hx₂ h
    exact neg_injective h
  · intro y hy
    refine ⟨-y, ?_, ?_⟩
    · have hy' : - -y ∈ T := by simpa using hy
      exact (hT (-y)).mpr hy'
    · simp
  · intro x hx
    simp

lemma star_sum_stdAddChar_neg_mul_eq_self_of_symmetric
    {p : ℕ} [NeZero p] {T : Finset (ZMod p)}
    (hT : SymmetricFinset T) (r : ZMod p) :
    (starRingEnd ℂ) (∑ x ∈ T, ZMod.stdAddChar (-(x * r))) =
      ∑ x ∈ T, ZMod.stdAddChar (-(x * r)) := by
  classical
  calc
    (starRingEnd ℂ) (∑ x ∈ T, ZMod.stdAddChar (-(x * r)))
        = ∑ x ∈ T, (starRingEnd ℂ) (ZMod.stdAddChar (-(x * r))) := by
          rw [map_sum]
    _ = ∑ x ∈ T, ZMod.stdAddChar (x * r) := by
          refine Finset.sum_congr rfl ?_
          intro x hx
          have hchar := AddChar.map_neg_eq_conj (ZMod.stdAddChar (N := p)) (x * r)
          simp [hchar] at *
    _ = ∑ x ∈ T, ZMod.stdAddChar (-(x * r)) :=
          (sum_stdAddChar_neg_mul_eq_sum_pos_mul_of_symmetric hT r).symm

lemma star_normalizedDftCoeff_eq_self_of_symmetric
    {p : ℕ} [NeZero p] {T : Finset (ZMod p)}
    (hT : SymmetricFinset T) (r : ZMod p) :
    (starRingEnd ℂ) (normalizedDftCoeff T r) = normalizedDftCoeff T r := by
  rw [normalizedDftCoeff_eq_sum]
  simp [star_sum_stdAddChar_neg_mul_eq_self_of_symmetric hT r]

lemma normalizedDftCoeff_im_eq_zero_of_symmetric
    {p : ℕ} [NeZero p] {T : Finset (ZMod p)}
    (hT : SymmetricFinset T) (r : ZMod p) :
    (normalizedDftCoeff T r).im = 0 := by
  have h := congrArg Complex.im (star_normalizedDftCoeff_eq_self_of_symmetric hT r)
  simp at h
  linarith

lemma normalizedDftCoeff_neg_eq_of_symmetric
    {p : ℕ} [NeZero p] {T : Finset (ZMod p)}
    (hT : SymmetricFinset T) (r : ZMod p) :
    normalizedDftCoeff T (-r) = normalizedDftCoeff T r := by
  rw [normalizedDftCoeff_eq_sum, normalizedDftCoeff_eq_sum]
  congr 1
  calc
    (∑ x ∈ T, ZMod.stdAddChar (-(x * -r))) =
        ∑ x ∈ T, ZMod.stdAddChar (x * r) := by
          refine Finset.sum_congr rfl ?_
          intro x _hx
          congr 1
          ring
    _ = ∑ x ∈ T, ZMod.stdAddChar (-(x * r)) :=
          (sum_stdAddChar_neg_mul_eq_sum_pos_mul_of_symmetric hT r).symm

end Erdos42


/-! =============================================================
    Section from: Erdos/P42/FiniteReduction.lean
    ============================================================= -/

/-
Erdős Problem 42 — shared finite-reduction machinery.

This file contains the route-neutral finite pieces used by both the Fourier-positive Route A and
the compact-Cayley Route B:

  1. Greedy Sidon subset lemma: any sufficiently large finite integer set
     contains a Sidon subset of any prescribed size.
  2. Allowed-difference set: for `A ⊆ [N]` Sidon and prime `p > 2N`, define
     `T_A := (ZMod p) \ ((A − A) ∪ {0})`. Then `T_A` is symmetric, `0 ∉ T_A`,
     `|T_A| ≥ p/2`, and the normalized Fourier transform satisfies an upper
     bound `≤ (|A|−1)/p ≤ ε` for `p` large.
  3. Cyclic-interval averaging: some cyclic interval of length `N` in `ZMod p`
     contains `≥ greedySidonThreshold M` clique elements (uses `p < 8N`).
  4. Lift the clique-in-interval to an integer set `X ⊆ [1, N]` avoiding
     `A − A`; greedily extract a Sidon subset `B ⊆ X` of size `M`.

The Route-specific theorem files import this module; this file imports no analytic
trust-boundary axiom.
-/


namespace Erdos42

open Finset Erdos42

/-! ## Step 1 — greedy Sidon subset bound (compact PDF Lemma 3.2) -/

/-- The compact PDF's greedy Sidon threshold:
`R_M = 1 + (M − 1) + binomial(M−1, 2) + 2 (M − 1) · binomial(M−1, 2)`.

Any finite integer set of size `≥ R_M` contains a Sidon subset of size `M`,
proved by a greedy argument that excludes (a) already-chosen elements, (b)
elements producing an old difference, and (c) midpoints of two chosen
elements. -/
def greedySidonThreshold (M : ℕ) : ℕ :=
  1 + (M - 1) + Nat.choose (M - 1) 2
    + 2 * (M - 1) * Nat.choose (M - 1) 2

/-- The midpoint map on unordered pairs from a finite integer set. -/
noncomputable def midpointMap (B : Finset ℤ) : Sym2 (B : Type) → ℤ :=
  Sym2.lift ⟨fun a b : (B : Type) => (a.1 + b.1) / 2, by
    intro a b
    change (a.1 + b.1) / 2 = (b.1 + a.1) / 2
    rw [add_comm]⟩

/-- Midpoints of distinct unordered pairs from `B`. These are the new values
that would create a collision `x + x = b₁ + b₂`. -/
noncomputable def midpointSet (B : Finset ℤ) : Finset ℤ :=
  ((⊤ : SimpleGraph (B : Type)).edgeFinset).image (midpointMap B)

/-- Values obtained by translating an old nonzero difference by an old point:
these are the new values that can create a one-new-point collision. -/
def shiftedDiffSet (B : Finset ℤ) : Finset ℤ :=
  (B ×ˢ ((DiffFinset B B).erase 0)).image (fun bd => bd.1 + bd.2)

/-- The finite set avoided in the greedy Sidon construction. -/
noncomputable def greedyBadSet (B : Finset ℤ) : Finset ℤ :=
  B ∪ midpointSet B ∪ shiftedDiffSet B

lemma midpointSet_card_le (B : Finset ℤ) :
    (midpointSet B).card ≤ Nat.choose B.card 2 := by
  classical
  calc
    (midpointSet B).card ≤ ((⊤ : SimpleGraph (B : Type)).edgeFinset).card :=
      Finset.card_image_le
    _ = Nat.choose (Fintype.card (B : Type)) 2 :=
      SimpleGraph.card_edgeFinset_top_eq_card_choose_two
    _ = Nat.choose B.card 2 := by rw [Fintype.card_coe]

lemma mem_midpointSet_of_two_mul_eq {B : Finset ℤ} {x a b : ℤ}
    (ha : a ∈ B) (hb : b ∈ B) (hne : a ≠ b) (hmid : 2 * x = a + b) :
    x ∈ midpointSet B := by
  classical
  let aa : (B : Type) := ⟨a, ha⟩
  let bb : (B : Type) := ⟨b, hb⟩
  have hne' : aa ≠ bb := by
    intro h
    exact hne (Subtype.ext_iff.mp h)
  have hedge : Sym2.mk aa bb ∈ (⊤ : SimpleGraph (B : Type)).edgeFinset := by
    rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet]
    simpa [SimpleGraph.top_adj] using hne'
  refine Finset.mem_image.mpr ⟨Sym2.mk aa bb, hedge, ?_⟩
  change (aa.1 + bb.1) / 2 = x
  have hdvd : (2 : ℤ) ∣ aa.1 + bb.1 := Dvd.intro x (by simpa [aa, bb] using hmid)
  exact (EuclideanDomain.div_eq_iff_eq_mul_of_dvd
      (aa.1 + bb.1) (2 : ℤ) x (by norm_num) hdvd).mpr
    (by simpa [aa, bb] using hmid.symm)

lemma shiftedDiffSet_card_le (B : Finset ℤ) :
    (shiftedDiffSet B).card ≤ B.card * (Nat.choose B.card 2 * 2) := by
  classical
  calc
    (shiftedDiffSet B).card ≤ (B ×ˢ ((DiffFinset B B).erase 0)).card :=
      Finset.card_image_le
    _ = B.card * ((DiffFinset B B).erase 0).card := by rw [Finset.card_product]
    _ ≤ B.card * (B.card * B.card - B.card) := by
      exact Nat.mul_le_mul_left _ (diffFinset_erase_zero_card_le_offDiag_card B)
    _ = B.card * (Nat.choose B.card 2 * 2) := by
      rw [Nat.choose_two_right, Nat.div_mul_cancel (Nat.two_dvd_mul_sub_one B.card)]
      rw [Nat.mul_sub_one]

lemma greedyBadSet_card_le (B : Finset ℤ) :
    (greedyBadSet B).card ≤
      B.card + Nat.choose B.card 2 + 2 * B.card * Nat.choose B.card 2 := by
  classical
  calc
    (greedyBadSet B).card ≤ B.card + (midpointSet B).card + (shiftedDiffSet B).card := by
      unfold greedyBadSet
      have h₁ :
          (B ∪ midpointSet B ∪ shiftedDiffSet B).card ≤
            (B ∪ midpointSet B).card + (shiftedDiffSet B).card :=
        Finset.card_union_le (B ∪ midpointSet B) (shiftedDiffSet B)
      have h₂ : (B ∪ midpointSet B).card ≤ B.card + (midpointSet B).card :=
        Finset.card_union_le B (midpointSet B)
      omega
    _ ≤ B.card + Nat.choose B.card 2 + B.card * (Nat.choose B.card 2 * 2) := by
      have hmid := midpointSet_card_le B
      have hshift := shiftedDiffSet_card_le B
      omega
    _ = B.card + Nat.choose B.card 2 + 2 * B.card * Nat.choose B.card 2 := by
      ring

lemma greedySidonThreshold_le_succ (M : ℕ) :
    greedySidonThreshold M ≤ greedySidonThreshold (M + 1) := by
  unfold greedySidonThreshold
  have hM : M - 1 ≤ M := Nat.sub_le M 1
  have hchoose : Nat.choose (M - 1) 2 ≤ Nat.choose M 2 :=
    Nat.choose_le_choose 2 hM
  have hprod : (M - 1) * Nat.choose (M - 1) 2 ≤ M * Nat.choose M 2 :=
    Nat.mul_le_mul hM hchoose
  have hlast :
      2 * (M - 1) * Nat.choose (M - 1) 2 ≤ 2 * M * Nat.choose M 2 :=
    Nat.mul_le_mul (Nat.mul_le_mul_left 2 hM) hchoose
  rw [Nat.add_sub_cancel]
  omega

lemma isSidonInt_insert_of_notMem_greedyBad {B : Finset ℤ} {x : ℤ}
    (hB : IsSidonInt B) (hx : x ∉ greedyBadSet B) :
    IsSidonInt (insert x B) := by
  classical
  rw [greedyBadSet, Finset.mem_union, Finset.mem_union, not_or] at hx
  rcases hx with ⟨hxOldOrMid, hxShift⟩
  rw [not_or] at hxOldOrMid
  rcases hxOldOrMid with ⟨hxB, hxMid⟩
  have no_mid : ∀ {a b : ℤ}, a ∈ B → b ∈ B → a ≠ b → 2 * x ≠ a + b := by
    intro a b ha hb hne h
    exact hxMid (mem_midpointSet_of_two_mul_eq ha hb hne h)
  have no_shift :
      ∀ {c d : ℤ}, c ∈ B → d ∈ (DiffFinset B B).erase 0 → c + d ≠ x := by
    intro c d hc hd h
    apply hxShift
    exact Finset.mem_image.mpr ⟨(c, d), by
      rw [Finset.mem_product]
      exact ⟨hc, hd⟩, h⟩
  intro a₁ ha₁ a₂ ha₂ a₃ ha₃ a₄ ha₄ hsum
  rw [Finset.mem_insert] at ha₁ ha₂ ha₃ ha₄
  rcases ha₁ with h₁ | ha₁
  · subst a₁
    rcases ha₂ with h₂ | ha₂
    · subst a₂
      rcases ha₃ with h₃ | ha₃
      · subst a₃
        rcases ha₄ with h₄ | ha₄
        · subst a₄
          exact Or.inl ⟨rfl, rfl⟩
        · exfalso
          have hx4 : x = a₄ := by linarith
          exact hxB (by simpa [hx4] using ha₄)
      · rcases ha₄ with h₄ | ha₄
        · subst a₄
          exfalso
          have hx3 : x = a₃ := by linarith
          exact hxB (by simpa [hx3] using ha₃)
        · exfalso
          by_cases h34 : a₃ = a₄
          · subst a₄
            have hx3 : x = a₃ := by linarith
            exact hxB (by simpa [hx3] using ha₃)
          · exact no_mid ha₃ ha₄ h34 (by linarith)
    · rcases ha₃ with h₃ | ha₃
      · subst a₃
        rcases ha₄ with h₄ | ha₄
        · subst a₄
          exfalso
          have hx2 : x = a₂ := by linarith
          exact hxB (by simpa [hx2] using ha₂)
        · have h24 : a₂ = a₄ := by linarith
          exact Or.inl ⟨rfl, h24⟩
      · rcases ha₄ with h₄ | ha₄
        · subst a₄
          have h23 : a₂ = a₃ := by linarith
          exact Or.inr ⟨rfl, h23⟩
        · exfalso
          by_cases h42 : a₄ = a₂
          · subst a₄
            have hx3 : x = a₃ := by linarith
            exact hxB (by simpa [hx3] using ha₃)
          · have hd : a₄ - a₂ ∈ (DiffFinset B B).erase 0 := by
              rw [Finset.mem_erase, mem_diffFinset]
              exact ⟨sub_ne_zero.mpr h42, ⟨a₄, ha₄, a₂, ha₂, rfl⟩⟩
            exact no_shift ha₃ hd (by linarith)
  · rcases ha₂ with h₂ | ha₂
    · subst a₂
      rcases ha₃ with h₃ | ha₃
      · subst a₃
        rcases ha₄ with h₄ | ha₄
        · subst a₄
          exfalso
          have hx1 : x = a₁ := by linarith
          exact hxB (by simpa [hx1] using ha₁)
        · have h14 : a₁ = a₄ := by linarith
          exact Or.inr ⟨h14, rfl⟩
      · rcases ha₄ with h₄ | ha₄
        · subst a₄
          have h13 : a₁ = a₃ := by linarith
          exact Or.inl ⟨h13, rfl⟩
        · exfalso
          by_cases h41 : a₄ = a₁
          · subst a₄
            have hx3 : x = a₃ := by linarith
            exact hxB (by simpa [hx3] using ha₃)
          · have hd : a₄ - a₁ ∈ (DiffFinset B B).erase 0 := by
              rw [Finset.mem_erase, mem_diffFinset]
              exact ⟨sub_ne_zero.mpr h41, ⟨a₄, ha₄, a₁, ha₁, rfl⟩⟩
            exact no_shift ha₃ hd (by linarith)
    · rcases ha₃ with h₃ | ha₃
      · subst a₃
        rcases ha₄ with h₄ | ha₄
        · subst a₄
          exfalso
          by_cases h12 : a₁ = a₂
          · subst a₂
            have hx1 : x = a₁ := by linarith
            exact hxB (by simpa [hx1] using ha₁)
          · exact no_mid ha₁ ha₂ h12 (by linarith)
        · exfalso
          by_cases h24 : a₂ = a₄
          · subst a₂
            have hx1 : x = a₁ := by linarith
            exact hxB (by simpa [hx1] using ha₁)
          · have hd : a₂ - a₄ ∈ (DiffFinset B B).erase 0 := by
              rw [Finset.mem_erase, mem_diffFinset]
              exact ⟨sub_ne_zero.mpr h24, ⟨a₂, ha₂, a₄, ha₄, rfl⟩⟩
            exact no_shift ha₁ hd (by linarith)
      · rcases ha₄ with h₄ | ha₄
        · subst a₄
          exfalso
          by_cases h23 : a₂ = a₃
          · subst a₂
            have hx1 : x = a₁ := by linarith
            exact hxB (by simpa [hx1] using ha₁)
          · have hd : a₂ - a₃ ∈ (DiffFinset B B).erase 0 := by
              rw [Finset.mem_erase, mem_diffFinset]
              exact ⟨sub_ne_zero.mpr h23, ⟨a₂, ha₂, a₃, ha₃, rfl⟩⟩
            exact no_shift ha₁ hd (by linarith)
        · exact hB ha₁ ha₂ ha₃ ha₄ hsum

/-- Greedy Sidon subset bound: every large integer `Finset` contains a Sidon
subset of any prescribed size. -/
theorem exists_sidon_subset_of_card_ge
    (M : ℕ) (X : Finset ℤ)
    (hX : greedySidonThreshold M ≤ X.card) :
    ∃ B : Finset ℤ, B ⊆ X ∧ B.card = M ∧ IsSidonInt B := by
  classical
  induction M with
  | zero =>
      exact ⟨∅, by simp, by simp, isSidonInt_empty⟩
  | succ M ih =>
      have hXM : greedySidonThreshold M ≤ X.card :=
        (greedySidonThreshold_le_succ M).trans hX
      obtain ⟨B, hBX, hBcard, hBsidon⟩ := ih hXM
      have hbad_lt : (greedyBadSet B).card < X.card := by
        have hbad_le := greedyBadSet_card_le B
        have hbad_leM :
            (greedyBadSet B).card ≤
              M + Nat.choose M 2 + 2 * M * Nat.choose M 2 := by
          simpa [hBcard] using hbad_le
        have hthresh :
            greedySidonThreshold (M + 1) =
              1 + M + Nat.choose M 2 + 2 * M * Nat.choose M 2 := by
          unfold greedySidonThreshold
          rw [Nat.add_sub_cancel]
        have hbad_lt_threshold : (greedyBadSet B).card < greedySidonThreshold (M + 1) := by
          rw [hthresh]
          omega
        exact hbad_lt_threshold.trans_le hX
      obtain ⟨x, hxX, hxBad⟩ := Finset.exists_mem_notMem_of_card_lt_card hbad_lt
      have hxB : x ∉ B := by
        intro hxB
        apply hxBad
        unfold greedyBadSet
        simp [hxB]
      refine ⟨insert x B, ?_, ?_, ?_⟩
      · intro y hy
        rw [Finset.mem_insert] at hy
        rcases hy with rfl | hy
        · exact hxX
        · exact hBX hy
      · rw [Finset.card_insert_of_notMem hxB, hBcard]
      · exact isSidonInt_insert_of_notMem_greedyBad hBsidon hxBad

/-! ## Step 2 — allowed-difference set & Fourier upper bound -/

/-- The allowed-difference set: `T_A := (ZMod p) \ ((A − A) ∪ {0})` viewed
through the natural cast `ℤ → ZMod p`. -/
noncomputable def allowedDiffSetMod (p : ℕ) [NeZero p] (A : Finset ℤ) :
    Finset (ZMod p) :=
  (Finset.univ : Finset (ZMod p)).filter
    (fun t => t ≠ 0 ∧ ∀ a ∈ A, ∀ b ∈ A, ((a - b : ℤ) : ZMod p) ≠ t)

/-- The allowed-difference set is symmetric. -/
lemma allowedDiffSetMod_symmetric (p : ℕ) [NeZero p] (A : Finset ℤ) :
    SymmetricFinset (allowedDiffSetMod p A) := by
  intro t
  simp only [allowedDiffSetMod, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨ht0, ht⟩
    refine ⟨?_, ?_⟩
    · intro hzero
      exact ht0 (by simpa using congrArg Neg.neg hzero)
    · intro a ha b hb hdiff
      have hswap : ((b - a : ℤ) : ZMod p) = t := by
        calc
          ((b - a : ℤ) : ZMod p) = -(((a - b : ℤ) : ZMod p)) := by norm_num
          _ = t := by simp [hdiff]
      exact ht b hb a ha hswap
  · rintro ⟨ht0, ht⟩
    refine ⟨?_, ?_⟩
    · intro hzero
      exact ht0 (by simpa using congrArg Neg.neg hzero)
    · intro a ha b hb hdiff
      have hswap : ((b - a : ℤ) : ZMod p) = -t := by
        calc
          ((b - a : ℤ) : ZMod p) = -(((a - b : ℤ) : ZMod p)) := by norm_num
          _ = -t := by simp [hdiff]
      exact ht b hb a ha hswap

/-- `0` is not in the allowed-difference set (by construction). -/
lemma zero_notMem_allowedDiffSetMod (p : ℕ) [NeZero p] (A : Finset ℤ) :
    (0 : ZMod p) ∉ allowedDiffSetMod p A := by
  simp [allowedDiffSetMod]

/-- Density bound: for `A ⊆ [N]` Sidon and `p > 4N`, the allowed-difference
set covers more than half of `ZMod p`. -/
lemma allowedDiffSetMod_density
    {p N : ℕ} [Fact p.Prime] (hbig : 4 * N < p)
    (A : Finset ℤ)
    (hAint : ∀ a ∈ A, 1 ≤ a ∧ a ≤ (N : ℤ))
    (hSidon : IsSidonInt A) :
    (1 / 2 : ℝ) * p ≤ ((allowedDiffSetMod p A).card : ℝ) := by
  classical
  by_cases hN0 : N = 0
  · subst N
    have hAempty : A = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro a ha
      have ha' := hAint a ha
      omega
    have hcard : (allowedDiffSetMod p A).card = p - 1 := by
      have hallowed_eq :
          allowedDiffSetMod p A = (Finset.univ : Finset (ZMod p)).erase 0 := by
        ext t
        simp [allowedDiffSetMod, hAempty]
      rw [hallowed_eq, Finset.card_erase_of_mem (Finset.mem_univ (0 : ZMod p)),
        Finset.card_univ, ZMod.card]
    have hp2 : 2 ≤ p := (Fact.out : p.Prime).two_le
    rw [hcard]
    rw [Nat.cast_sub (by omega : 1 ≤ p)]
    have hp2R : (2 : ℝ) ≤ (p : ℝ) := Nat.cast_le.mpr hp2
    nlinarith
  · have hNpos : 0 < N := Nat.pos_of_ne_zero hN0
    let P : ZMod p → Prop :=
      fun t => t ≠ 0 ∧ ∀ a ∈ A, ∀ b ∈ A, ((a - b : ℤ) : ZMod p) ≠ t
    let bad : Finset (ZMod p) := (Finset.univ : Finset (ZMod p)).filter (fun t => ¬ P t)
    let forbidden : Finset (ZMod p) :=
      insert 0 (((DiffFinset A A).erase 0).image (fun x : ℤ => (x : ZMod p)))
    have hbad_subset : bad ⊆ forbidden := by
      intro t ht
      change t ∈ (Finset.univ : Finset (ZMod p)).filter (fun t => ¬ P t) at ht
      rw [Finset.mem_filter] at ht
      rcases ht with ⟨_htuniv, htbad⟩
      by_cases ht0 : t = 0
      · change t ∈ insert 0 (((DiffFinset A A).erase 0).image (fun x : ℤ => (x : ZMod p)))
        simp [ht0]
      · have hnot :
            ¬ ∀ a ∈ A, ∀ b ∈ A, ((a - b : ℤ) : ZMod p) ≠ t := by
          intro hall
          exact htbad ⟨ht0, hall⟩
        push Not at hnot
        rcases hnot with ⟨a, ha, b, hb, hcast⟩
        have hdiff_ne : a - b ≠ 0 := by
          intro hzero
          apply ht0
          simpa [hzero] using hcast.symm
        have hdiff_mem : a - b ∈ (DiffFinset A A).erase 0 := by
          rw [Finset.mem_erase, mem_diffFinset]
          exact ⟨hdiff_ne, ⟨a, ha, b, hb, rfl⟩⟩
        change t ∈ insert 0 (((DiffFinset A A).erase 0).image (fun x : ℤ => (x : ZMod p)))
        exact Finset.mem_insert.mpr
          (Or.inr (Finset.mem_image.mpr ⟨a - b, hdiff_mem, hcast⟩))
    have hbad_card : bad.card ≤ 2 * N - 1 := by
      calc
        bad.card ≤ forbidden.card := Finset.card_le_card hbad_subset
        _ ≤ (((DiffFinset A A).erase 0).image (fun x : ℤ => (x : ZMod p))).card + 1 :=
          Finset.card_insert_le _ _
        _ ≤ ((DiffFinset A A).erase 0).card + 1 :=
          Nat.add_le_add_right Finset.card_image_le 1
        _ ≤ (2 * N - 2) + 1 :=
          Nat.add_le_add_right (sidon_nonzero_diff_card_le A N hAint hSidon) 1
        _ ≤ 2 * N - 1 := by omega
    have hsum : (allowedDiffSetMod p A).card + bad.card = p := by
      change
        ((Finset.univ : Finset (ZMod p)).filter P).card +
            ((Finset.univ : Finset (ZMod p)).filter (fun t => ¬ P t)).card = p
      rw [Finset.card_filter_add_card_filter_not]
      simp [ZMod.card]
    have hbad_half : 2 * bad.card ≤ p := by omega
    have hallowed_nat : p ≤ 2 * (allowedDiffSetMod p A).card := by omega
    have hallowed_real :
        (p : ℝ) ≤ 2 * ((allowedDiffSetMod p A).card : ℝ) := by
      exact_mod_cast hallowed_nat
    nlinarith

lemma int_difference_eq_of_zmod_eq_of_interval
    {p N : ℕ} [NeZero p] (hbig : 4 * N < p)
    {a b c d : ℤ}
    (ha : 1 ≤ a ∧ a ≤ (N : ℤ))
    (hb : 1 ≤ b ∧ b ≤ (N : ℤ))
    (hc : 1 ≤ c ∧ c ≤ (N : ℤ))
    (hd : 1 ≤ d ∧ d ≤ (N : ℤ))
    (hcong : ((a - b : ℤ) : ZMod p) = ((c - d : ℤ) : ZMod p)) :
    a - b = c - d := by
  have hdiv : (p : ℤ) ∣ (c - d) - (a - b) :=
    (ZMod.intCast_eq_intCast_iff_dvd_sub (a - b) (c - d) p).mp hcong
  have hp_bound : (2 * (N : ℤ) : ℤ) < (p : ℤ) := by exact_mod_cast (by omega)
  have habs : |(c - d) - (a - b)| < (p : ℤ) := by
    rw [abs_lt]
    constructor <;> omega
  have hzero : (c - d) - (a - b) = 0 := Int.eq_zero_of_abs_lt_dvd hdiv habs
  linarith

lemma offDiag_diff_cast_injOn
    {p N : ℕ} [NeZero p] (hbig : 4 * N < p)
    (A : Finset ℤ)
    (hAint : ∀ a ∈ A, 1 ≤ a ∧ a ≤ (N : ℤ))
    (hSidon : IsSidonInt A) :
    Set.InjOn (fun ab : ℤ × ℤ => ((ab.1 - ab.2 : ℤ) : ZMod p))
      (A.offDiag : Set (ℤ × ℤ)) := by
  intro ab hab cd hcd hcast
  have habFin : ab ∈ A.offDiag := by simpa using hab
  have hcdFin : cd ∈ A.offDiag := by simpa using hcd
  rw [Finset.mem_offDiag] at habFin hcdFin
  rcases habFin with ⟨hab1, hab2, hab_ne⟩
  rcases hcdFin with ⟨hcd1, hcd2, _hcd_ne⟩
  have hdiff : ab.1 - ab.2 = cd.1 - cd.2 :=
    int_difference_eq_of_zmod_eq_of_interval (p := p) (N := N) hbig
      (hAint ab.1 hab1) (hAint ab.2 hab2) (hAint cd.1 hcd1) (hAint cd.2 hcd2) hcast
  have hsum : ab.1 + cd.2 = cd.1 + ab.2 := by linarith
  rcases hSidon hab1 hcd2 hcd1 hab2 hsum with h | h
  · exact Prod.ext h.1 h.2.symm
  · exact False.elim (hab_ne h.1)

/-- Nonzero ordered difference residues from `A`. -/
noncomputable def offDiagDiffSetMod (p : ℕ) [NeZero p] (A : Finset ℤ) :
    Finset (ZMod p) :=
  A.offDiag.image (fun ab : ℤ × ℤ => ((ab.1 - ab.2 : ℤ) : ZMod p))

lemma zero_notMem_offDiagDiffSetMod
    {p N : ℕ} [NeZero p] (hbig : 4 * N < p)
    (A : Finset ℤ)
    (hAint : ∀ a ∈ A, 1 ≤ a ∧ a ≤ (N : ℤ)) :
    (0 : ZMod p) ∉ offDiagDiffSetMod p A := by
  classical
  rw [offDiagDiffSetMod, Finset.mem_image]
  rintro ⟨ab, hab, hcast⟩
  rw [Finset.mem_offDiag] at hab
  rcases hab with ⟨ha, hb, hne⟩
  have hcong :
      ((ab.1 - ab.2 : ℤ) : ZMod p) = ((ab.1 - ab.1 : ℤ) : ZMod p) := by
    simpa using hcast
  have hdiff :
      ab.1 - ab.2 = ab.1 - ab.1 :=
    int_difference_eq_of_zmod_eq_of_interval (p := p) (N := N) hbig
      (hAint ab.1 ha) (hAint ab.2 hb) (hAint ab.1 ha) (hAint ab.1 ha) hcong
  exact hne (by linarith)

lemma allowedDiffSetMod_union_forbidden (p : ℕ) [NeZero p] (A : Finset ℤ) :
    allowedDiffSetMod p A ∪ insert 0 (offDiagDiffSetMod p A) =
      (Finset.univ : Finset (ZMod p)) := by
  classical
  ext t
  simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_univ, iff_true]
  by_cases ht_allowed : t ∈ allowedDiffSetMod p A
  · exact Or.inl ht_allowed
  · right
    rw [allowedDiffSetMod, Finset.mem_filter] at ht_allowed
    simp only [Finset.mem_univ, true_and, not_and, not_forall] at ht_allowed
    by_cases ht0 : t = 0
    · exact Or.inl ht0
    · right
      have hnot_all := ht_allowed ht0
      push Not at hnot_all
      rcases hnot_all with ⟨a, ha, b, hb, hdiff⟩
      rw [offDiagDiffSetMod, Finset.mem_image]
      by_cases hab : a = b
      · subst b
        exfalso
        exact ht0 (by simpa using hdiff.symm)
      · refine ⟨(a, b), ?_, hdiff⟩
        rw [Finset.mem_offDiag]
        exact ⟨ha, hb, hab⟩

lemma disjoint_allowedDiffSetMod_forbidden (p : ℕ) [NeZero p] (A : Finset ℤ) :
    Disjoint (allowedDiffSetMod p A) (insert 0 (offDiagDiffSetMod p A)) := by
  classical
  rw [Finset.disjoint_left]
  intro t ht hforbidden
  rw [allowedDiffSetMod, Finset.mem_filter] at ht
  rcases ht with ⟨_htuniv, ht0, hno⟩
  rw [Finset.mem_insert] at hforbidden
  rcases hforbidden with rfl | hoff
  · exact ht0 rfl
  · rw [offDiagDiffSetMod, Finset.mem_image] at hoff
    rcases hoff with ⟨ab, hab, hdiff⟩
    rw [Finset.mem_offDiag] at hab
    rcases hab with ⟨ha, hb, _hne⟩
    exact hno ab.1 ha ab.2 hb hdiff

lemma sum_allowedDiffSetMod_eq_neg_forbidden
    {p : ℕ} [Fact p.Prime] [NeZero p]
    (A : Finset ℤ) {r : ZMod p} (hr : r ≠ 0) :
    ∑ x ∈ allowedDiffSetMod p A, ZMod.stdAddChar (-(x * r)) =
      - ∑ x ∈ insert 0 (offDiagDiffSetMod p A), ZMod.stdAddChar (-(x * r)) := by
  classical
  have htotal := sum_stdAddChar_neg_mul_eq_zero_of_ne_zero (p := p) hr
  have hsum_union :
      ∑ x ∈ allowedDiffSetMod p A ∪ insert 0 (offDiagDiffSetMod p A),
          ZMod.stdAddChar (-(x * r)) =
        ∑ x ∈ allowedDiffSetMod p A, ZMod.stdAddChar (-(x * r)) +
          ∑ x ∈ insert 0 (offDiagDiffSetMod p A), ZMod.stdAddChar (-(x * r)) := by
    rw [Finset.sum_union (disjoint_allowedDiffSetMod_forbidden p A)]
  rw [allowedDiffSetMod_union_forbidden p A] at hsum_union
  have hadd :
      ∑ x ∈ allowedDiffSetMod p A, ZMod.stdAddChar (-(x * r)) +
          ∑ x ∈ insert 0 (offDiagDiffSetMod p A), ZMod.stdAddChar (-(x * r)) = 0 := by
    rw [← hsum_union]
    exact htotal
  exact eq_neg_of_add_eq_zero_left hadd

lemma sum_forbidden_eq_one_add_offDiag
    {p N : ℕ} [NeZero p] (hbig : 4 * N < p)
    (A : Finset ℤ)
    (hAint : ∀ a ∈ A, 1 ≤ a ∧ a ≤ (N : ℤ))
    (r : ZMod p) :
    ∑ x ∈ insert 0 (offDiagDiffSetMod p A), ZMod.stdAddChar (-(x * r)) =
      1 + ∑ x ∈ offDiagDiffSetMod p A, ZMod.stdAddChar (-(x * r)) := by
  classical
  rw [Finset.sum_insert (zero_notMem_offDiagDiffSetMod (p := p) (N := N) hbig A hAint)]
  simp

lemma sum_offDiagDiffSetMod_eq_sum_offDiag
    {p N : ℕ} [NeZero p] (hbig : 4 * N < p)
    (A : Finset ℤ)
    (hAint : ∀ a ∈ A, 1 ≤ a ∧ a ≤ (N : ℤ))
    (hSidon : IsSidonInt A)
    (f : ZMod p → ℂ) :
    ∑ x ∈ offDiagDiffSetMod p A, f x =
      ∑ ab ∈ A.offDiag, f (((ab.1 - ab.2 : ℤ) : ZMod p)) := by
  classical
  rw [offDiagDiffSetMod]
  rw [Finset.sum_image]
  intro ab hab cd hcd h
  exact offDiag_diff_cast_injOn (p := p) (N := N) hbig A hAint hSidon
    (by simpa using hab) (by simpa using hcd) h

lemma sum_product_eq_sum_diag_add_sum_offDiag
    (A : Finset ℤ) (f : ℤ × ℤ → ℂ) :
    ∑ ab ∈ A ×ˢ A, f ab =
      (∑ a ∈ A, f (a, a)) + ∑ ab ∈ A.offDiag, f ab := by
  classical
  rw [← Finset.diag_union_offDiag (s := A)]
  rw [Finset.sum_union (Finset.disjoint_diag_offDiag A)]
  rw [Finset.sum_diag]

lemma sum_product_stdAddChar_neg_diff
    {p : ℕ} [NeZero p] (A : Finset ℤ) (r : ZMod p) :
    (∑ ab ∈ A ×ˢ A,
        ZMod.stdAddChar (-(((ab.1 - ab.2 : ℤ) : ZMod p) * r))) =
      (∑ a ∈ A, ZMod.stdAddChar (-(((a : ZMod p) * r)))) *
        (∑ b ∈ A, ZMod.stdAddChar (((b : ZMod p) * r))) := by
  classical
  rw [Finset.sum_product]
  rw [Finset.sum_mul]
  simp_rw [Finset.mul_sum]
  refine Finset.sum_congr rfl ?_
  intro a ha
  refine Finset.sum_congr rfl ?_
  intro b hb
  rw [← ZMod.stdAddChar.map_add_eq_mul]
  congr 1
  norm_num
  ring_nf

lemma sum_diag_stdAddChar_diff
    {p : ℕ} [NeZero p] (A : Finset ℤ) (r : ZMod p) :
    ∑ a ∈ A, ZMod.stdAddChar (-((((a - a : ℤ) : ZMod p) * r))) = (A.card : ℂ) := by
  simp

lemma sum_offDiagDiffSetMod_stdAddChar_eq
    {p N : ℕ} [NeZero p] (hbig : 4 * N < p)
    (A : Finset ℤ)
    (hAint : ∀ a ∈ A, 1 ≤ a ∧ a ≤ (N : ℤ))
    (hSidon : IsSidonInt A)
    (r : ZMod p) :
    ∑ x ∈ offDiagDiffSetMod p A, ZMod.stdAddChar (-(x * r)) =
      (∑ a ∈ A, ZMod.stdAddChar (-(((a : ZMod p) * r)))) *
        (∑ b ∈ A, ZMod.stdAddChar (((b : ZMod p) * r))) - (A.card : ℂ) := by
  classical
  let F : ℤ × ℤ → ℂ :=
    fun ab => ZMod.stdAddChar (-((((ab.1 - ab.2 : ℤ) : ZMod p) * r)))
  have hoff :=
    sum_offDiagDiffSetMod_eq_sum_offDiag (p := p) (N := N) hbig A hAint hSidon
      (fun x : ZMod p => ZMod.stdAddChar (-(x * r)))
  have hsplit := sum_product_eq_sum_diag_add_sum_offDiag A F
  have hprod := sum_product_stdAddChar_neg_diff A r
  have hdiag : ∑ a ∈ A, F (a, a) = (A.card : ℂ) := by
    simp [F]
  rw [hoff]
  have hsplit' :
      ∑ ab ∈ A.offDiag, F ab =
        (∑ ab ∈ A ×ˢ A, F ab) - ∑ a ∈ A, F (a, a) := by
    rw [eq_sub_iff_add_eq]
    rw [add_comm]
    exact hsplit.symm
  rw [hprod] at hsplit'
  simpa [F, hdiag] using hsplit'

lemma stdAddChar_neg_eq_conj {p : ℕ} [NeZero p] (x : ZMod p) :
    ZMod.stdAddChar (-x) = (starRingEnd ℂ) (ZMod.stdAddChar x) := by
  simpa using AddChar.map_neg_eq_conj (ZMod.stdAddChar (N := p)) x

lemma sum_stdAddChar_neg_eq_conj_sum
    {p : ℕ} [NeZero p] (A : Finset ℤ) (r : ZMod p) :
    ∑ b ∈ A, ZMod.stdAddChar (-(((b : ZMod p) * r))) =
      (starRingEnd ℂ) (∑ a ∈ A, ZMod.stdAddChar (((a : ZMod p) * r))) := by
  classical
  calc
    ∑ b ∈ A, ZMod.stdAddChar (-(((b : ZMod p) * r))) =
        ∑ a ∈ A, (starRingEnd ℂ) (ZMod.stdAddChar (((a : ZMod p) * r))) := by
      refine Finset.sum_congr rfl ?_
      intro a ha
      exact stdAddChar_neg_eq_conj (p := p) (((a : ZMod p) * r))
    _ = (starRingEnd ℂ) (∑ a ∈ A, ZMod.stdAddChar (((a : ZMod p) * r))) := by
      simp

lemma stdAddChar_neg_product_re_nonneg
    {p : ℕ} [NeZero p] (A : Finset ℤ) (r : ZMod p) :
    0 ≤
      ((∑ a ∈ A, ZMod.stdAddChar (-(((a : ZMod p) * r)))) *
        (∑ b ∈ A, ZMod.stdAddChar (((b : ZMod p) * r)))).re := by
  classical
  let S : ℂ := ∑ b ∈ A, ZMod.stdAddChar (((b : ZMod p) * r))
  have hneg :
      (∑ a ∈ A, ZMod.stdAddChar (-(((a : ZMod p) * r)))) =
        (starRingEnd ℂ) S := by
    simpa [S] using sum_stdAddChar_neg_eq_conj_sum A r
  rw [hneg]
  rw [← Complex.normSq_eq_conj_mul_self]
  simpa using Complex.normSq_nonneg S

lemma sum_allowedDiffSetMod_stdAddChar_re_le
    {p N : ℕ} [Fact p.Prime] (hbig : 4 * N < p)
    (A : Finset ℤ)
    (hAint : ∀ a ∈ A, 1 ≤ a ∧ a ≤ (N : ℤ))
    (hSidon : IsSidonInt A)
    {r : ZMod p} (hr : r ≠ 0) :
    (∑ x ∈ allowedDiffSetMod p A, ZMod.stdAddChar (-(x * r))).re ≤
      ((A.card - 1 : ℕ) : ℝ) := by
  classical
  let P : ℂ :=
    (∑ a ∈ A, ZMod.stdAddChar (-(((a : ZMod p) * r)))) *
      (∑ b ∈ A, ZMod.stdAddChar (((b : ZMod p) * r)))
  have hallowed :=
    sum_allowedDiffSetMod_eq_neg_forbidden (p := p) A hr
  have hforbidden :=
    sum_forbidden_eq_one_add_offDiag (p := p) (N := N) hbig A hAint r
  have hoff :=
    sum_offDiagDiffSetMod_stdAddChar_eq (p := p) (N := N) hbig A hAint hSidon r
  have hsum :
      ∑ x ∈ allowedDiffSetMod p A, ZMod.stdAddChar (-(x * r)) =
        (A.card : ℂ) - 1 - P := by
    rw [hallowed, hforbidden, hoff]
    simp [P]
    ring
  have hP_nonneg : 0 ≤ P.re := by
    simpa [P] using stdAddChar_neg_product_re_nonneg A r
  rw [hsum]
  by_cases hA0 : A.card = 0
  · simp [hA0]
    linarith
  · have hApos : 1 ≤ A.card := by omega
    have hcast : ((A.card - 1 : ℕ) : ℝ) = (A.card : ℝ) - 1 := by
      rw [Nat.cast_sub hApos]
      norm_num
    rw [hcast]
    simp only [Complex.sub_re, Complex.natCast_re, Complex.one_re, tsub_le_iff_right,
      le_add_iff_nonneg_right, ge_iff_le]
    exact hP_nonneg

/-- Sidon Fourier estimate (normalized): `Re 1̂_{T_A}(r) ≤ (|A|−1)/p` for every
nontrivial character `r`, for `T_A = (ZMod p) \ ((A−A) ∪ {0})` and `A` Sidon
(compact PDF §3 calculation).

This is a finite Fourier calculation, separate from the compact-Cayley clique
theorem. It expands `ZMod.dft`, uses the vanishing of nontrivial character sums,
and rewrites the nonzero-difference contribution as
`|∑ a ∈ A, χ a|^2 - |A|`. -/
theorem allowedDiffs_fourier_upper
    {p N : ℕ} [Fact p.Prime] (hbig : 4 * N < p)
    (A : Finset ℤ)
    (hAint : ∀ a ∈ A, 1 ≤ a ∧ a ≤ (N : ℤ))
    (hSidon : IsSidonInt A)
    (ε : ℝ)
    (hε : ((A.card - 1 : ℕ) : ℝ) / p ≤ ε) :
    FourierUpperIndicator (allowedDiffSetMod p A) ε := by
  classical
  intro r hr
  have hp_pos_nat : 0 < p := (Fact.out : p.Prime).pos
  have hp_pos : 0 < (p : ℝ) := by exact_mod_cast hp_pos_nat
  have hsum_le :=
    sum_allowedDiffSetMod_stdAddChar_re_le (p := p) (N := N) hbig A hAint hSidon hr
  rw [normalizedDftCoeff_eq_sum]
  have hinv : ((p : ℂ)⁻¹) = (((p : ℝ)⁻¹ : ℝ) : ℂ) := by
    rw [← Complex.ofReal_natCast, ← Complex.ofReal_inv]
  rw [hinv, Complex.re_ofReal_mul]
  have hmul_le :
      (p : ℝ)⁻¹ *
          (∑ x ∈ allowedDiffSetMod p A, ZMod.stdAddChar (-(x * r))).re ≤
        (p : ℝ)⁻¹ * ((A.card - 1 : ℕ) : ℝ) :=
    mul_le_mul_of_nonneg_left hsum_le (inv_nonneg.mpr hp_pos.le)
  refine hmul_le.trans ?_
  rw [div_eq_inv_mul] at hε
  simpa [mul_comm] using hε

/-- Eventual smallness of the normalized Sidon-size error term.

For `A ⊆ [1,N]` Sidon, `choose |A| 2 ≤ N - 1`, so `|A| = O(sqrt N)`.
Since the chosen prime satisfies `p > 4N`, `( |A| - 1 ) / p → 0`. This
elementary asymptotic bound is kept separate from the finite Fourier identity
above. -/
lemma sidon_card_minus_one_div_prime_eventually_small
    (ε : ℝ) (hε : 0 < ε) :
    ∃ Nε : ℕ, ∀ N p : ℕ,
      Nε ≤ N →
      4 * N < p →
      ∀ A : Finset ℤ,
        (∀ a ∈ A, 1 ≤ a ∧ a ≤ (N : ℤ)) →
        IsSidonInt A →
        ((A.card - 1 : ℕ) : ℝ) / p ≤ ε := by
  classical
  have hden_pos : 0 < 8 * ε ^ 2 := by positivity
  obtain ⟨Nε, hNε_gt⟩ := exists_nat_gt ((1 : ℝ) / (8 * ε ^ 2))
  refine ⟨Nε, ?_⟩
  intro N p hN hp A hAint hSidon
  let t : ℝ := ((A.card - 1 : ℕ) : ℝ)
  let k : ℝ := (A.card : ℝ)
  have hN_large_base : (1 : ℝ) / (8 * ε ^ 2) < (N : ℝ) :=
    hNε_gt.trans_le (by exact_mod_cast hN)
  have hN_large : 1 < 8 * ε ^ 2 * (N : ℝ) := by
    have := (div_lt_iff₀ hden_pos).mp hN_large_base
    nlinarith
  have hN_pos : 0 < (N : ℝ) := (one_div_pos.mpr hden_pos).trans hN_large_base
  have hp_pos : 0 < (p : ℝ) := by
    have : 0 < p := by omega
    exact_mod_cast this
  have hp_gt4N : 4 * (N : ℝ) < (p : ℝ) := by exact_mod_cast hp
  have hchoose := sidon_choose_two_le_interval A N hAint hSidon
  by_cases hAcard0 : A.card = 0
  · simp [hAcard0, le_of_lt hε]
  have hAcard_pos : 1 ≤ A.card := by omega
  have ht_eq : t = (A.card : ℝ) - 1 := by
    dsimp [t]
    rw [Nat.cast_sub hAcard_pos]
    norm_num
  have hchoose_real :
      (Nat.choose A.card 2 : ℝ) ≤ (N - 1 : ℕ) := by exact_mod_cast hchoose
  have hchoose_le_N :
      k * t / 2 ≤ (N : ℝ) := by
    have hformula :
        (Nat.choose A.card 2 : ℝ) = k * t / 2 := by
      simpa [k, ht_eq] using (Nat.cast_choose_two (K := ℝ) A.card)
    have hsub_le : ((N - 1 : ℕ) : ℝ) ≤ (N : ℝ) := by
      exact_mod_cast (Nat.sub_le N 1)
    nlinarith
  have ht_nonneg : 0 ≤ t := by positivity
  have hk_nonneg : 0 ≤ k := by positivity
  have ht_le_k : t ≤ k := by
    dsimp [t, k]
    exact_mod_cast (Nat.sub_le A.card 1)
  have ht_sq_le : t ^ 2 ≤ 2 * (N : ℝ) := by
    have hsq_le : t * t ≤ k * t := by nlinarith
    nlinarith
  have htarget_sq : t ^ 2 ≤ (ε * (p : ℝ)) ^ 2 := by
    have hεsq_pos : 0 < ε ^ 2 := by positivity
    have hp_sq_gt : (4 * (N : ℝ)) ^ 2 < (p : ℝ) ^ 2 := by
      nlinarith [hp_gt4N, hN_pos, hp_pos, sq_nonneg ((p : ℝ) - 4 * (N : ℝ))]
    nlinarith
  have ht_le_epsp : t ≤ ε * (p : ℝ) := by
    exact le_of_sq_le_sq htarget_sq (by positivity)
  rw [div_le_iff₀ hp_pos]
  simpa [t] using ht_le_epsp

/-! ## Step 3 — cyclic interval averaging -/

/-- Cyclic interval `{s, s+1, …, s+N-1}` in `ZMod p`. -/
noncomputable def cyclicInterval (p N : ℕ) [NeZero p] (s : ZMod p) :
    Finset (ZMod p) :=
  (Finset.range N).image (fun i : ℕ => s + (i : ZMod p))

lemma nat_eq_of_zmod_eq_of_lt {p i j : ℕ} [NeZero p]
    (hi : i < p) (hj : j < p) (hij : (i : ZMod p) = (j : ZMod p)) :
    i = j := by
  have hmod : i % p = j % p := (ZMod.natCast_eq_natCast_iff' i j p).mp hij
  rw [Nat.mod_eq_of_lt hi, Nat.mod_eq_of_lt hj] at hmod
  exact hmod

/-- Integer lift of clique points lying in the cyclic interval
`{s, …, s+N-1}`. The residue `s+i` is lifted to the integer `i+1`, so the
lift lies in `[1, N]`. -/
noncomputable def intervalLiftSet (p N : ℕ) [NeZero p] (s : ZMod p)
    (C : Finset (ZMod p)) : Finset ℤ :=
  ((Finset.range N).filter (fun i : ℕ => s + (i : ZMod p) ∈ C)).image
    (fun i : ℕ => (i + 1 : ℤ))

lemma intervalLiftSet_card_eq
    {p N : ℕ} [NeZero p] (hpN : N < p) (s : ZMod p) (C : Finset (ZMod p)) :
    (intervalLiftSet p N s C).card =
      (C.filter (fun x => x ∈ cyclicInterval p N s)).card := by
  classical
  let I : Finset ℕ := (Finset.range N).filter (fun i : ℕ => s + (i : ZMod p) ∈ C)
  let f : ℕ → ZMod p := fun i => s + (i : ZMod p)
  let target : Finset (ZMod p) := C.filter (fun x => x ∈ cyclicInterval p N s)
  have hinjI : Set.InjOn f (I : Set ℕ) := by
    intro i hi j hj hij
    have hiI : i ∈ I := by simpa using hi
    have hjI : j ∈ I := by simpa using hj
    rw [Finset.mem_filter] at hiI hjI
    apply nat_eq_of_zmod_eq_of_lt
      (Nat.lt_trans (by simpa using hiI.1) hpN)
      (Nat.lt_trans (by simpa using hjI.1) hpN)
    apply add_left_cancel (a := s)
    simpa [f] using hij
  have hI_image_card : (I.image f).card = I.card :=
    Finset.card_image_of_injOn hinjI
  have hI_image : I.image f = target := by
    ext x
    constructor
    · intro hx
      rw [Finset.mem_image] at hx
      rcases hx with ⟨i, hiI, rfl⟩
      rw [Finset.mem_filter] at hiI
      rw [Finset.mem_filter]
      refine ⟨hiI.2, ?_⟩
      rw [cyclicInterval]
      exact Finset.mem_image.mpr ⟨i, hiI.1, rfl⟩
    · intro hx
      change x ∈ target at hx
      rw [Finset.mem_filter] at hx
      rcases hx with ⟨hxC, hxInt⟩
      rw [cyclicInterval, Finset.mem_image] at hxInt
      rcases hxInt with ⟨i, hiN, rfl⟩
      rw [Finset.mem_image]
      exact ⟨i, by
        rw [Finset.mem_filter]
        exact ⟨hiN, hxC⟩, rfl⟩
  have hlift_card : (intervalLiftSet p N s C).card = I.card := by
    unfold intervalLiftSet
    change (I.image (fun i : ℕ => (i + 1 : ℤ))).card = I.card
    apply Finset.card_image_of_injOn
    intro i _hi j _hj hij
    have hnat : i + 1 = j + 1 := Int.ofNat_inj.mp hij
    omega
  calc
    (intervalLiftSet p N s C).card = I.card := hlift_card
    _ = (I.image f).card := hI_image_card.symm
    _ = target.card := by rw [hI_image]

lemma mem_intervalLiftSet.mp
    {p N : ℕ} [NeZero p] {s : ZMod p} {C : Finset (ZMod p)} {b : ℤ}
    (hb : b ∈ intervalLiftSet p N s C) :
    ∃ i : ℕ, i < N ∧ s + (i : ZMod p) ∈ C ∧ b = (i + 1 : ℤ) := by
  classical
  rw [intervalLiftSet, Finset.mem_image] at hb
  rcases hb with ⟨i, hi, rfl⟩
  rw [Finset.mem_filter] at hi
  exact ⟨i, by simpa using hi.1, hi.2, rfl⟩

/-- Pigeonhole: a clique of size `8R` in `ZMod p` (with `p < 8N`) intersects
some cyclic interval of length `N` in at least `R` points. -/
theorem exists_large_intersection_cyclicInterval
    {p N R : ℕ} [NeZero p] (hpN : N < p) (C : Finset (ZMod p))
    (hsize : C.card = 8 * R)
    (hpupper : p < 8 * N) :
    ∃ s : ZMod p,
      R ≤ (C.filter (fun x => x ∈ cyclicInterval p N s)).card := by
  classical
  by_cases hR0 : R = 0
  · subst R
    exact ⟨0, by simp⟩
  · have hRpos : 0 < R := Nat.pos_of_ne_zero hR0
    let D : Finset (ZMod p × ℕ) := C.product (Finset.range N)
    let start : ZMod p × ℕ → ZMod p := fun ci => ci.1 - (ci.2 : ZMod p)
    have hlarge :
        (Finset.univ : Finset (ZMod p)).card * R < D.card := by
      rw [Finset.card_univ, ZMod.card]
      change p * R < (C ×ˢ Finset.range N).card
      rw [Finset.card_product, Finset.card_range, hsize]
      calc
        p * R < (8 * N) * R := Nat.mul_lt_mul_of_pos_right hpupper hRpos
        _ = (8 * R) * N := by ring
    obtain ⟨s, _hsuniv, hs⟩ :=
      Finset.exists_lt_card_fiber_of_mul_lt_card_of_maps_to
        (s := D) (t := (Finset.univ : Finset (ZMod p))) (f := start) (n := R)
        (by intro x _hx; exact Finset.mem_univ _) hlarge
    refine ⟨s, ?_⟩
    let fiber : Finset (ZMod p × ℕ) := D.filter (fun ci => start ci = s)
    let target : Finset (ZMod p) := C.filter (fun x => x ∈ cyclicInterval p N s)
    have hmaps :
        Set.MapsTo (fun ci : ZMod p × ℕ => ci.1)
          (fiber : Set (ZMod p × ℕ)) (target : Set (ZMod p)) := by
      intro ci hci
      have hci' : ci ∈ D.filter (fun ci => start ci = s) := by
        simpa [fiber] using hci
      rw [Finset.mem_filter] at hci'
      rcases hci' with ⟨hciD, hstart⟩
      have hmem : ci.1 ∈ C ∧ ci.2 ∈ Finset.range N := by
        simpa [D] using hciD
      rcases hmem with ⟨hc, hi⟩
      have hpoint : ci.1 ∈ cyclicInterval p N s := by
        rw [cyclicInterval]
        refine Finset.mem_image.mpr ⟨ci.2, hi, ?_⟩
        have hadd : ci.1 = s + (ci.2 : ZMod p) := by
          simpa [start] using (sub_eq_iff_eq_add.mp hstart)
        exact hadd.symm
      change ci.1 ∈ C.filter (fun x => x ∈ cyclicInterval p N s)
      rw [Finset.mem_filter]
      exact ⟨hc, hpoint⟩
    have hinj :
        (fiber : Set (ZMod p × ℕ)).InjOn (fun ci : ZMod p × ℕ => ci.1) := by
      intro ci hci cj hcj hproj
      have hci' : ci ∈ D.filter (fun ci => start ci = s) := by
        simpa [fiber] using hci
      have hcj' : cj ∈ D.filter (fun ci => start ci = s) := by
        simpa [fiber] using hcj
      rw [Finset.mem_filter] at hci' hcj'
      rcases hci' with ⟨hciD, hstart_i⟩
      rcases hcj' with ⟨hcjD, hstart_j⟩
      have hi : ci.2 ∈ Finset.range N := by
        have hmem : ci.1 ∈ C ∧ ci.2 ∈ Finset.range N := by
          simpa [D] using hciD
        exact hmem.2
      have hj : cj.2 ∈ Finset.range N := by
        have hmem : cj.1 ∈ C ∧ cj.2 ∈ Finset.range N := by
          simpa [D] using hcjD
        exact hmem.2
      have hci_add : ci.1 = s + (ci.2 : ZMod p) := by
        simpa [start] using (sub_eq_iff_eq_add.mp hstart_i)
      have hcj_add : cj.1 = s + (cj.2 : ZMod p) := by
        simpa [start] using (sub_eq_iff_eq_add.mp hstart_j)
      have hcast : (ci.2 : ZMod p) = (cj.2 : ZMod p) := by
        apply add_left_cancel (a := s)
        calc
          s + (ci.2 : ZMod p) = ci.1 := hci_add.symm
          _ = cj.1 := hproj
          _ = s + (cj.2 : ZMod p) := hcj_add
      have hmod : ci.2 % p = cj.2 % p := by
        exact (ZMod.natCast_eq_natCast_iff' ci.2 cj.2 p).mp hcast
      have hilt : ci.2 < p := by
        exact Nat.lt_trans (by simpa using hi) hpN
      have hjlt : cj.2 < p := by
        exact Nat.lt_trans (by simpa using hj) hpN
      have hidx : ci.2 = cj.2 := by
        rw [Nat.mod_eq_of_lt hilt, Nat.mod_eq_of_lt hjlt] at hmod
        exact hmod
      exact Prod.ext hproj hidx
    have hfiber_le : fiber.card ≤ target.card :=
      Finset.card_le_card_of_injOn (fun ci : ZMod p × ℕ => ci.1) hmaps hinj
    have hs' : R < fiber.card := by
      simpa [fiber] using hs
    exact (Nat.le_of_lt hs').trans hfiber_le

end Erdos42


/-! =============================================================
    Section from: Erdos/P42/CompactCayley/Counterexample.lean
    ============================================================= -/

/-
Erdős Problem 42 — compact-Cayley counterexample sequence.

This is the Route B contradiction skeleton for opening
`compact_cayley_clique`.  It is independent of Route A: if the explicit-prime
compact Cayley statement fails, then one can choose primes `p_n → ∞` and
allowed sets `T_n ⊆ ZMod p_n` with density `η`, zero-free symmetry, Fourier
upper bias tending to zero, and no `K_ℓ` clique.
-/


namespace Erdos42.CompactCayley

open Filter Erdos42
open scoped Topology

/-- Explicit-prime version of the compact Cayley theorem statement.  This
avoids typeclass binders in the counterexample extraction; it is equivalent in
content to the Route B trust-boundary axiom's statement. -/
def CompactCayleyCliqueStatementExplicit (ℓ : ℕ) (η : ℝ) : Prop :=
  ∃ ε : ℝ, 0 < ε ∧
  ∃ p₀ : ℕ, ∀ (p : ℕ) (hp : p.Prime), p₀ < p →
    ∀ T : Finset (ZMod p),
      SymmetricFinset T →
      (0 : ZMod p) ∉ T →
      η * (p : ℝ) ≤ (T.card : ℝ) →
      (letI : NeZero p := ⟨hp.ne_zero⟩; FourierUpperIndicator T ε) →
      ∃ C : Finset (ZMod p), C.card = ℓ ∧ CliqueInCayley T C

/-- The explicit-prime compact-Cayley statement implies the original
typeclass-shaped statement used by the Route B trust-boundary axiom. -/
theorem compactCayleyCliqueStatement_from_explicit
    {ℓ : ℕ} {η : ℝ}
    (h : CompactCayleyCliqueStatementExplicit ℓ η) :
    ∃ ε : ℝ, 0 < ε ∧
    ∃ p₀ : ℕ, ∀ p : ℕ, [Fact p.Prime] → p₀ < p →
    ∀ T : Finset (ZMod p),
      SymmetricFinset T →
      (0 : ZMod p) ∉ T →
      η * (p : ℝ) ≤ (T.card : ℝ) →
      FourierUpperIndicator T ε →
      ∃ C : Finset (ZMod p), C.card = ℓ ∧ CliqueInCayley T C := by
  rcases h with ⟨ε, hε, p₀, hp₀⟩
  refine ⟨ε, hε, p₀, ?_⟩
  intro p hpFact hpgt T hsym hzero hdens hfourier
  have hp : p.Prime := Fact.out
  exact hp₀ p hp hpgt T hsym hzero hdens (by simpa using hfourier)

/-- Conversely, the original typeclass-shaped compact-Cayley statement implies
the explicit-prime formulation used for contradiction extraction. -/
theorem explicit_of_compactCayleyCliqueStatement
    {ℓ : ℕ} {η : ℝ}
    (h : ∃ ε : ℝ, 0 < ε ∧
      ∃ p₀ : ℕ, ∀ p : ℕ, [Fact p.Prime] → p₀ < p →
      ∀ T : Finset (ZMod p),
        SymmetricFinset T →
        (0 : ZMod p) ∉ T →
        η * (p : ℝ) ≤ (T.card : ℝ) →
        FourierUpperIndicator T ε →
        ∃ C : Finset (ZMod p), C.card = ℓ ∧ CliqueInCayley T C) :
    CompactCayleyCliqueStatementExplicit ℓ η := by
  rcases h with ⟨ε, hε, p₀, hp₀⟩
  refine ⟨ε, hε, p₀, ?_⟩
  intro p hp hpgt T hsym hzero hdens hfourier
  haveI : Fact p.Prime := ⟨hp⟩
  exact hp₀ p hpgt T hsym hzero hdens (by simpa using hfourier)

/-- A sequence of finite Cayley-graph counterexamples with Fourier upper bias
tending to zero. This is the exact starting point for Lemmas 2.2–2.7 in the
compact-Cayley PDF. -/
structure CayleyCounterSeq (ℓ : ℕ) (η : ℝ) where
  p : ℕ → ℕ
  prime : ∀ n, (p n).Prime
  p_gt : ∀ n, n < p n
  T : ∀ n, Finset (ZMod (p n))
  T_sym : ∀ n, SymmetricFinset (T n)
  T_zero : ∀ n, (0 : ZMod (p n)) ∉ T n
  T_density : ∀ n, η * (p n : ℝ) ≤ ((T n).card : ℝ)
  eps : ℕ → ℝ
  eps_pos : ∀ n, 0 < eps n
  eps_tendsto_zero : Tendsto eps atTop (𝓝 0)
  T_fourier_upper : ∀ n,
    letI : NeZero (p n) := ⟨(prime n).ne_zero⟩
    FourierUpperIndicator (T n) (eps n)
  no_clique : ∀ n,
    ¬ ∃ C : Finset (ZMod (p n)), C.card = ℓ ∧ CliqueInCayley (T n) C

lemma CayleyCounterSeq.tendsto_p_atTop {ℓ : ℕ} {η : ℝ}
    (S : CayleyCounterSeq ℓ η) :
    Tendsto S.p atTop atTop :=
  tendsto_atTop_mono (fun n => le_of_lt (S.p_gt n)) tendsto_id

lemma CayleyCounterSeq.tendsto_p_natCast_atTop {ℓ : ℕ} {η : ℝ}
    (S : CayleyCounterSeq ℓ η) :
    Tendsto (fun n => (S.p n : ℝ)) atTop atTop :=
  tendsto_natCast_atTop_atTop.comp S.tendsto_p_atTop

/-- Failure of the explicit compact-Cayley statement produces the standard
contradiction sequence with `ε_n = 1 / (n + 1)` and `p_n > n`. -/
theorem exists_cayleyCounterSeq_of_not_compactCayleyCliqueStatementExplicit
    {ℓ : ℕ} {η : ℝ}
    (hfail : ¬ CompactCayleyCliqueStatementExplicit ℓ η) :
    ∃ _S : CayleyCounterSeq ℓ η, True := by
  classical
  have hbad : ∀ n : ℕ,
      ∃ p : ℕ, ∃ hp : p.Prime, n < p ∧
      ∃ T : Finset (ZMod p),
        SymmetricFinset T ∧
        (0 : ZMod p) ∉ T ∧
        η * (p : ℝ) ≤ (T.card : ℝ) ∧
        (letI : NeZero p := ⟨hp.ne_zero⟩;
          FourierUpperIndicator T (((n + 1 : ℕ) : ℝ)⁻¹)) ∧
        ¬ ∃ C : Finset (ZMod p), C.card = ℓ ∧ CliqueInCayley T C := by
    intro n
    by_contra hnone
    apply hfail
    refine ⟨(((n + 1 : ℕ) : ℝ)⁻¹), by positivity, n, ?_⟩
    intro p hp hpgt T hsym hzero hdens hfourier
    by_contra hNo
    apply hnone
    exact ⟨p, hp, hpgt, T, hsym, hzero, hdens, hfourier, hNo⟩
  choose p hp hpgt T hsym hzero hdens hfourier hnoclique using hbad
  refine ⟨{
    p := p
    prime := hp
    p_gt := hpgt
    T := T
    T_sym := hsym
    T_zero := hzero
    T_density := hdens
    eps := fun n => (((n + 1 : ℕ) : ℝ)⁻¹)
    eps_pos := by
      intro n
      positivity
    eps_tendsto_zero := by
      simpa [one_div] using (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
    T_fourier_upper := by
      intro n
      simpa using hfourier n
    no_clique := hnoclique
  }, trivial⟩

end Erdos42.CompactCayley


/-! =============================================================
    Section from: Erdos/P42/CompactCayley/CliqueEndpoint.lean
    ============================================================= -/

/-
Erdős Problem 42 — internal finite lemmas for the compact-Cayley theorem.

This file starts opening the remaining Route B trust boundary
`compact_cayley_clique`.  The lemmas here are finite bookkeeping around the
endpoint of the compactness argument: once counting convergence gives an
ordered tuple whose pairwise differences lie in the allowed set, `0 ∉ T`
turns that tuple into an actual finite clique.
-/


namespace Erdos42.CompactCayley

open Finset Erdos42

/-- An ordered `ℓ`-tuple whose distinct pairwise differences all lie in the
allowed Cayley set `T`. -/
def CliqueTuple {p ℓ : ℕ} (T : Finset (ZMod p)) (x : Fin ℓ → ZMod p) : Prop :=
  ∀ i j : Fin ℓ, i ≠ j → x i - x j ∈ T

lemma cliqueTuple_injective_of_zero_notMem
    {p ℓ : ℕ} {T : Finset (ZMod p)} {x : Fin ℓ → ZMod p}
    (hT0 : (0 : ZMod p) ∉ T) (hx : CliqueTuple T x) :
    Function.Injective x := by
  intro i j hij
  by_contra hne
  have hdiff : x i - x j ∈ T := hx i j hne
  apply hT0
  simpa [hij] using hdiff

/-- A zero-free ordered clique tuple yields the `Finset` clique required by
`compact_cayley_clique`. This is the finite endpoint used after the compact
counting argument proves that at least one ordered clique tuple exists. -/
theorem exists_clique_of_cliqueTuple
    {p ℓ : ℕ} {T : Finset (ZMod p)} (hT0 : (0 : ZMod p) ∉ T)
    {x : Fin ℓ → ZMod p} (hx : CliqueTuple T x) :
    ∃ C : Finset (ZMod p), C.card = ℓ ∧ CliqueInCayley T C := by
  classical
  let C : Finset (ZMod p) := (Finset.univ : Finset (Fin ℓ)).image x
  have hinj : Function.Injective x :=
    cliqueTuple_injective_of_zero_notMem hT0 hx
  refine ⟨C, ?_, ?_⟩
  · dsimp [C]
    rw [Finset.card_image_of_injective _ hinj, Finset.card_univ, Fintype.card_fin]
  · intro y hy z hz hyz
    change y ∈ (Finset.univ : Finset (Fin ℓ)).image x at hy
    change z ∈ (Finset.univ : Finset (Fin ℓ)).image x at hz
    rw [Finset.mem_image] at hy hz
    rcases hy with ⟨i, _hi, rfl⟩
    rcases hz with ⟨j, _hj, rfl⟩
    have hij : i ≠ j := by
      intro hij
      exact hyz (by simp [hij])
    exact hx i j hij

/-- Contrapositive form: a zero-free Cayley graph with no `ℓ`-clique has no
ordered clique tuple of length `ℓ`. -/
lemma not_cliqueTuple_of_no_clique
    {p ℓ : ℕ} {T : Finset (ZMod p)} (hT0 : (0 : ZMod p) ∉ T)
    (hNoClique : ¬ ∃ C : Finset (ZMod p), C.card = ℓ ∧ CliqueInCayley T C)
    (x : Fin ℓ → ZMod p) :
    ¬ CliqueTuple T x := by
  intro hx
  exact hNoClique (exists_clique_of_cliqueTuple hT0 hx)

/-- Boolean-valued indicator for ordered clique tuples, useful when connecting
finite homomorphism densities to actual cliques. -/
noncomputable def cliqueTupleIndicator {p ℓ : ℕ}
    (T : Finset (ZMod p)) (x : Fin ℓ → ZMod p) : ℂ :=
  by
    classical
    exact if CliqueTuple T x then 1 else 0

lemma cliqueTupleIndicator_eq_zero_of_no_clique
    {p ℓ : ℕ} {T : Finset (ZMod p)} (hT0 : (0 : ZMod p) ∉ T)
    (hNoClique : ¬ ∃ C : Finset (ZMod p), C.card = ℓ ∧ CliqueInCayley T C)
    (x : Fin ℓ → ZMod p) :
    cliqueTupleIndicator T x = 0 := by
  classical
  unfold cliqueTupleIndicator
  simp [not_cliqueTuple_of_no_clique hT0 hNoClique x]

/-- The finite set of ordered `ℓ`-tuples forming a clique in the Cayley graph. -/
noncomputable def cliqueTupleFinset {p ℓ : ℕ} [NeZero p]
    (T : Finset (ZMod p)) : Finset (Fin ℓ → ZMod p) :=
  by
    classical
    exact (Finset.univ : Finset (Fin ℓ → ZMod p)).filter (fun x => CliqueTuple T x)

lemma mem_cliqueTupleFinset {p ℓ : ℕ} [NeZero p]
    {T : Finset (ZMod p)} {x : Fin ℓ → ZMod p} :
    x ∈ cliqueTupleFinset (ℓ := ℓ) T ↔ CliqueTuple T x := by
  classical
  simp [cliqueTupleFinset]

lemma cliqueTupleFinset_nonempty_of_cliqueTuple
    {p ℓ : ℕ} [NeZero p] {T : Finset (ZMod p)}
    {x : Fin ℓ → ZMod p} (hx : CliqueTuple T x) :
    (cliqueTupleFinset (ℓ := ℓ) T).Nonempty :=
  ⟨x, mem_cliqueTupleFinset.mpr hx⟩

lemma exists_clique_of_cliqueTupleFinset_nonempty
    {p ℓ : ℕ} [NeZero p] {T : Finset (ZMod p)}
    (hT0 : (0 : ZMod p) ∉ T)
    (h : (cliqueTupleFinset (ℓ := ℓ) T).Nonempty) :
    ∃ C : Finset (ZMod p), C.card = ℓ ∧ CliqueInCayley T C := by
  rcases h with ⟨x, hx⟩
  exact exists_clique_of_cliqueTuple hT0 (mem_cliqueTupleFinset.mp hx)

lemma cliqueTupleFinset_nonempty_of_clique
    {p ℓ : ℕ} [NeZero p] {T C : Finset (ZMod p)}
    (hCcard : C.card = ℓ) (hClique : CliqueInCayley T C) :
    (cliqueTupleFinset (ℓ := ℓ) T).Nonempty := by
  classical
  let e : C ≃ Fin ℓ := C.equivFinOfCardEq hCcard
  let x : Fin ℓ → ZMod p := fun i => (e.symm i).1
  refine cliqueTupleFinset_nonempty_of_cliqueTuple (T := T) (x := x) ?_
  intro i j hij
  have hxi : x i ∈ C := (e.symm i).2
  have hxj : x j ∈ C := (e.symm j).2
  have hne : x i ≠ x j := by
    intro h
    have hsub : e.symm i = e.symm j := Subtype.ext h
    exact hij (by simpa using congrArg e hsub)
  exact hClique (x i) hxi (x j) hxj hne

lemma cliqueTupleFinset_nonempty_iff_exists_clique
    {p ℓ : ℕ} [NeZero p] {T : Finset (ZMod p)}
    (hT0 : (0 : ZMod p) ∉ T) :
    (cliqueTupleFinset (ℓ := ℓ) T).Nonempty ↔
      ∃ C : Finset (ZMod p), C.card = ℓ ∧ CliqueInCayley T C := by
  refine ⟨exists_clique_of_cliqueTupleFinset_nonempty hT0, ?_⟩
  rintro ⟨C, hCcard, hClique⟩
  exact cliqueTupleFinset_nonempty_of_clique hCcard hClique

/-- The edge set of the complete graph on `Fin ℓ`, oriented by the natural
order to avoid double-counting. -/
def cliqueEdgePairs (ℓ : ℕ) : Finset (Fin ℓ × Fin ℓ) :=
  (Finset.univ : Finset (Fin ℓ × Fin ℓ)).filter (fun e => e.1 < e.2)

lemma cliqueEdgePairs_left_lt_right {ℓ : ℕ} {e : Fin ℓ × Fin ℓ}
    (he : e ∈ cliqueEdgePairs ℓ) : e.1 < e.2 := by
  exact (Finset.mem_filter.mp he).2

lemma cliqueEdgePairs_left_ne_right {ℓ : ℕ} {e : Fin ℓ × Fin ℓ}
    (he : e ∈ cliqueEdgePairs ℓ) : e.1 ≠ e.2 :=
  ne_of_lt (cliqueEdgePairs_left_lt_right he)

lemma cliqueEdgePairs_card_le_sq (ℓ : ℕ) :
    (cliqueEdgePairs ℓ).card ≤ ℓ * ℓ := by
  classical
  unfold cliqueEdgePairs
  have h := Finset.card_filter_le (s := (Finset.univ : Finset (Fin ℓ × Fin ℓ)))
    (p := fun e : Fin ℓ × Fin ℓ => e.1 < e.2)
  simpa [Fintype.card_prod, Fintype.card_fin] using h

/-- Product weight for the finite Cayley `K_ℓ` homomorphism density. For
indicator functions this is `1` exactly on ordered clique tuples and `0`
otherwise, once `T` is symmetric. -/
noncomputable def cliqueKernelWeight {p ℓ : ℕ}
    (T : Finset (ZMod p)) (x : Fin ℓ → ZMod p) : ℂ :=
  ∏ e ∈ cliqueEdgePairs ℓ, indicatorC T (x e.1 - x e.2)

lemma cliqueKernelWeight_eq_one_of_cliqueTuple
    {p ℓ : ℕ} {T : Finset (ZMod p)} {x : Fin ℓ → ZMod p}
    (hx : CliqueTuple T x) :
    cliqueKernelWeight T x = 1 := by
  classical
  unfold cliqueKernelWeight
  apply Finset.prod_eq_one
  intro e he
  have hlt : e.1 < e.2 := (Finset.mem_filter.mp he).2
  have hmem : x e.1 - x e.2 ∈ T := hx e.1 e.2 (ne_of_lt hlt)
  simp [indicatorC, hmem]

lemma cliqueKernelWeight_eq_zero_of_not_cliqueTuple
    {p ℓ : ℕ} {T : Finset (ZMod p)} {x : Fin ℓ → ZMod p}
    (hTsym : SymmetricFinset T) (hx : ¬ CliqueTuple T x) :
    cliqueKernelWeight T x = 0 := by
  classical
  rw [CliqueTuple, not_forall] at hx
  rcases hx with ⟨i, hx⟩
  rw [not_forall] at hx
  rcases hx with ⟨j, hx⟩
  rw [Classical.not_imp] at hx
  rcases hx with ⟨hij, hnot⟩
  rcases lt_or_gt_of_ne hij with hlt | hgt
  · unfold cliqueKernelWeight
    apply Finset.prod_eq_zero (i := (i, j))
    · simp [cliqueEdgePairs, hlt]
    · simp [indicatorC, hnot]
  · have hnot' : x j - x i ∉ T := by
      intro hji
      have hneg : -(x j - x i) ∈ T := (hTsym (x j - x i)).mp hji
      exact hnot (by simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using hneg)
    unfold cliqueKernelWeight
    apply Finset.prod_eq_zero (i := (j, i))
    · simp [cliqueEdgePairs, hgt]
    · simp [indicatorC, hnot']

lemma cliqueKernelWeight_eq_cliqueTupleIndicator_of_symmetric
    {p ℓ : ℕ} {T : Finset (ZMod p)} (hTsym : SymmetricFinset T)
    (x : Fin ℓ → ZMod p) :
    cliqueKernelWeight T x = cliqueTupleIndicator T x := by
  classical
  unfold cliqueTupleIndicator
  by_cases hx : CliqueTuple T x
  · simp [hx, cliqueKernelWeight_eq_one_of_cliqueTuple hx]
  · simp [hx, cliqueKernelWeight_eq_zero_of_not_cliqueTuple hTsym hx]

/-- Ordered clique-tuple count. This is the finite, unnormalized version of the
`K_ℓ` Cayley homomorphism density for indicator functions. -/
noncomputable def cliqueTupleCount {p ℓ : ℕ} [NeZero p]
    (T : Finset (ZMod p)) : ℂ :=
  ∑ x : Fin ℓ → ZMod p, cliqueTupleIndicator T x

lemma cliqueTupleCount_eq_zero_of_no_clique
    {p ℓ : ℕ} [NeZero p] {T : Finset (ZMod p)}
    (hT0 : (0 : ZMod p) ∉ T)
    (hNoClique : ¬ ∃ C : Finset (ZMod p), C.card = ℓ ∧ CliqueInCayley T C) :
    cliqueTupleCount (ℓ := ℓ) T = 0 := by
  classical
  unfold cliqueTupleCount
  simp [cliqueTupleIndicator_eq_zero_of_no_clique hT0 hNoClique]

lemma cliqueTupleCount_eq_card_cliqueTupleFinset
    {p ℓ : ℕ} [NeZero p] (T : Finset (ZMod p)) :
    cliqueTupleCount (ℓ := ℓ) T =
      ((cliqueTupleFinset (ℓ := ℓ) T).card : ℂ) := by
  classical
  rw [cliqueTupleCount]
  change
    (∑ x ∈ (Finset.univ : Finset (Fin ℓ → ZMod p)),
        if CliqueTuple T x then (1 : ℂ) else 0) =
      (((Finset.univ : Finset (Fin ℓ → ZMod p)).filter
        (fun x => CliqueTuple T x)).card : ℂ)
  rw [Finset.sum_boole]

/-- Normalized ordered clique-tuple density. -/
noncomputable def cliqueTupleDensity {p ℓ : ℕ} [NeZero p]
    (T : Finset (ZMod p)) : ℂ :=
  ((Fintype.card (Fin ℓ → ZMod p) : ℂ)⁻¹) * cliqueTupleCount (ℓ := ℓ) T

lemma cliqueTupleDensity_eq_card_cliqueTupleFinset
    {p ℓ : ℕ} [NeZero p] (T : Finset (ZMod p)) :
    cliqueTupleDensity (ℓ := ℓ) T =
      ((Fintype.card (Fin ℓ → ZMod p) : ℂ)⁻¹) *
        ((cliqueTupleFinset (ℓ := ℓ) T).card : ℂ) := by
  simp [cliqueTupleDensity, cliqueTupleCount_eq_card_cliqueTupleFinset]

lemma card_fun_fin_zmod (p ℓ : ℕ) [NeZero p] :
    Fintype.card (Fin ℓ → ZMod p) = p ^ ℓ := by
  simp [ZMod.card]

lemma cliqueTupleDensity_re_eq_card_div
    {p ℓ : ℕ} [NeZero p] (T : Finset (ZMod p)) :
    (cliqueTupleDensity (ℓ := ℓ) T).re =
      ((cliqueTupleFinset (ℓ := ℓ) T).card : ℝ) /
        (Fintype.card (Fin ℓ → ZMod p) : ℝ) := by
  rw [cliqueTupleDensity_eq_card_cliqueTupleFinset]
  have hden :
      ((Fintype.card (Fin ℓ → ZMod p) : ℂ)⁻¹) =
        (((Fintype.card (Fin ℓ → ZMod p) : ℝ)⁻¹ : ℝ) : ℂ) := by
    rw [← Complex.ofReal_natCast, ← Complex.ofReal_inv]
  rw [hden, Complex.re_ofReal_mul]
  simp [div_eq_inv_mul]

lemma cliqueTupleDensity_re_pos_iff_cliqueTupleFinset_nonempty
    {p ℓ : ℕ} [NeZero p] (T : Finset (ZMod p)) :
    0 < (cliqueTupleDensity (ℓ := ℓ) T).re ↔
      (cliqueTupleFinset (ℓ := ℓ) T).Nonempty := by
  rw [cliqueTupleDensity_re_eq_card_div]
  have hden_pos : 0 < (Fintype.card (Fin ℓ → ZMod p) : ℝ) := by
    exact_mod_cast (Fintype.card_pos : 0 < Fintype.card (Fin ℓ → ZMod p))
  rw [div_eq_inv_mul, mul_pos_iff_of_pos_left (inv_pos.mpr hden_pos)]
  constructor
  · intro hcard
    exact Finset.card_pos.mp (by exact_mod_cast hcard)
  · intro hnonempty
    exact_mod_cast (Finset.card_pos.mpr hnonempty)

lemma cliqueTupleDensity_re_pos_iff_exists_clique
    {p ℓ : ℕ} [NeZero p] {T : Finset (ZMod p)}
    (hT0 : (0 : ZMod p) ∉ T) :
    0 < (cliqueTupleDensity (ℓ := ℓ) T).re ↔
      ∃ C : Finset (ZMod p), C.card = ℓ ∧ CliqueInCayley T C := by
  rw [cliqueTupleDensity_re_pos_iff_cliqueTupleFinset_nonempty]
  exact cliqueTupleFinset_nonempty_iff_exists_clique hT0

/-- Product-form `K_ℓ` density, matching the notation in the compact-Cayley
PDF before it is specialized to indicators of Cayley sets. -/
noncomputable def cliqueKernelDensity {p ℓ : ℕ} [NeZero p]
    (T : Finset (ZMod p)) : ℂ :=
  ((Fintype.card (Fin ℓ → ZMod p) : ℂ)⁻¹) *
    ∑ x : Fin ℓ → ZMod p, cliqueKernelWeight T x

lemma cliqueKernelDensity_eq_cliqueTupleDensity_of_symmetric
    {p ℓ : ℕ} [NeZero p] {T : Finset (ZMod p)}
    (hTsym : SymmetricFinset T) :
    cliqueKernelDensity (ℓ := ℓ) T = cliqueTupleDensity (ℓ := ℓ) T := by
  classical
  simp [cliqueKernelDensity, cliqueTupleDensity, cliqueTupleCount,
    cliqueKernelWeight_eq_cliqueTupleIndicator_of_symmetric hTsym]

lemma cliqueTupleDensity_eq_zero_of_no_clique
    {p ℓ : ℕ} [NeZero p] {T : Finset (ZMod p)}
    (hT0 : (0 : ZMod p) ∉ T)
    (hNoClique : ¬ ∃ C : Finset (ZMod p), C.card = ℓ ∧ CliqueInCayley T C) :
    cliqueTupleDensity (ℓ := ℓ) T = 0 := by
  simp [cliqueTupleDensity, cliqueTupleCount_eq_zero_of_no_clique hT0 hNoClique]

/-- Nonzero ordered clique-tuple count yields an actual finite clique. -/
theorem exists_clique_of_cliqueTupleCount_ne_zero
    {p ℓ : ℕ} [NeZero p] {T : Finset (ZMod p)}
    (hT0 : (0 : ZMod p) ∉ T)
    (hcount : cliqueTupleCount (ℓ := ℓ) T ≠ 0) :
    ∃ C : Finset (ZMod p), C.card = ℓ ∧ CliqueInCayley T C := by
  by_contra hNoClique
  exact hcount (cliqueTupleCount_eq_zero_of_no_clique hT0 hNoClique)

/-- Nonzero normalized ordered `K_ℓ` density yields an actual finite clique. -/
theorem exists_clique_of_cliqueTupleDensity_ne_zero
    {p ℓ : ℕ} [NeZero p] {T : Finset (ZMod p)}
    (hT0 : (0 : ZMod p) ∉ T)
    (hdensity : cliqueTupleDensity (ℓ := ℓ) T ≠ 0) :
    ∃ C : Finset (ZMod p), C.card = ℓ ∧ CliqueInCayley T C := by
  by_contra hNoClique
  exact hdensity (cliqueTupleDensity_eq_zero_of_no_clique hT0 hNoClique)

/-- The form used at the end of the compactness proof: once counting
convergence gives a strictly positive real part for the finite `K_ℓ` density,
the finite Cayley graph contains an `ℓ`-clique. -/
theorem exists_clique_of_cliqueTupleDensity_re_pos
    {p ℓ : ℕ} [NeZero p] {T : Finset (ZMod p)}
    (hT0 : (0 : ZMod p) ∉ T)
    (hdensity : 0 < (cliqueTupleDensity (ℓ := ℓ) T).re) :
    ∃ C : Finset (ZMod p), C.card = ℓ ∧ CliqueInCayley T C := by
  refine exists_clique_of_cliqueTupleDensity_ne_zero hT0 ?_
  intro hzero
  exact (ne_of_gt hdensity) (by simp [hzero])

lemma cliqueKernelDensity_eq_zero_of_no_clique
    {p ℓ : ℕ} [NeZero p] {T : Finset (ZMod p)}
    (hTsym : SymmetricFinset T) (hT0 : (0 : ZMod p) ∉ T)
    (hNoClique : ¬ ∃ C : Finset (ZMod p), C.card = ℓ ∧ CliqueInCayley T C) :
    cliqueKernelDensity (ℓ := ℓ) T = 0 := by
  rw [cliqueKernelDensity_eq_cliqueTupleDensity_of_symmetric hTsym]
  exact cliqueTupleDensity_eq_zero_of_no_clique hT0 hNoClique

lemma cliqueKernelDensity_re_pos_iff_exists_clique
    {p ℓ : ℕ} [NeZero p] {T : Finset (ZMod p)}
    (hTsym : SymmetricFinset T) (hT0 : (0 : ZMod p) ∉ T) :
    0 < (cliqueKernelDensity (ℓ := ℓ) T).re ↔
      ∃ C : Finset (ZMod p), C.card = ℓ ∧ CliqueInCayley T C := by
  rw [cliqueKernelDensity_eq_cliqueTupleDensity_of_symmetric hTsym]
  exact cliqueTupleDensity_re_pos_iff_exists_clique hT0

end Erdos42.CompactCayley


/-! =============================================================
    Section from: Erdos/P42/CompactCayley/SpectralCutNorm.lean
    ============================================================= -/

/-
Erdős Problem 42 — compact-Cayley route, Lemma 2.5 finite spectral layer.

The compact-Cayley proof's Lemma 2.5 is the finite statement that the Cayley
cut norm of a kernel `a(x-y)` is controlled by the largest Fourier coefficient
of `a`.  This file starts that route with the concrete finite objects and the
Fourier expansion of the Cayley kernel. It deliberately introduces no new
assumptions; the operator-norm/Cauchy-Schwarz estimate builds on these
definitions.
-/


namespace Erdos42.CompactCayley

open scoped BigOperators ZMod

/-- Normalized average over `ZMod p`. -/
noncomputable def avgZMod {p : ℕ} [NeZero p] (f : ZMod p → ℂ) : ℂ :=
  ((p : ℂ)⁻¹) * ∑ x : ZMod p, f x

lemma avgZMod_sum {p : ℕ} [NeZero p] {ι : Type*} [Fintype ι]
    (F : ι → ZMod p → ℂ) :
    avgZMod (fun x => ∑ i : ι, F i x) = ∑ i : ι, avgZMod (F i) := by
  classical
  unfold avgZMod
  rw [Finset.sum_comm]
  rw [Finset.mul_sum]

lemma avgZMod_const_mul {p : ℕ} [NeZero p]
    (c : ℂ) (f : ZMod p → ℂ) :
    avgZMod (fun x => c * f x) = c * avgZMod f := by
  unfold avgZMod
  rw [← Finset.mul_sum]
  ring

lemma avgZMod_mul_const {p : ℕ} [NeZero p]
    (f : ZMod p → ℂ) (c : ℂ) :
    avgZMod (fun x => f x * c) = avgZMod f * c := by
  unfold avgZMod
  rw [← Finset.sum_mul]
  ring

/-- The finite Cayley cut functional attached to the kernel `a(x-y)` and two
test functions.  Lemma 2.5 takes a supremum of `‖cayleyCutFunctional a φ ψ‖`
over tests bounded by `1`. -/
noncomputable def cayleyCutFunctional {p : ℕ} [NeZero p]
    (a φ ψ : ZMod p → ℂ) : ℂ :=
  avgZMod fun x => avgZMod fun y => a (x - y) * φ x * ψ y

/-- The Cayley convolution operator `Aψ(x) = E_y a(x-y)ψ(y)` from the proof of
compact-Cayley Lemma 2.5. -/
noncomputable def cayleyConvolution {p : ℕ} [NeZero p]
    (a ψ : ZMod p → ℂ) (x : ZMod p) : ℂ :=
  avgZMod fun y => a (x - y) * ψ y

lemma cayleyCutFunctional_eq_avg_convolution {p : ℕ} [NeZero p]
    (a φ ψ : ZMod p → ℂ) :
    cayleyCutFunctional a φ ψ =
      avgZMod fun x => cayleyConvolution a ψ x * φ x := by
  unfold cayleyCutFunctional cayleyConvolution
  congr 1
  funext x
  rw [← avgZMod_mul_const]
  congr 1
  funext y
  ring

/-- The left test Fourier factor appearing after expanding the Cayley kernel. -/
noncomputable def leftFourierTest {p : ℕ} [NeZero p]
    (φ : ZMod p → ℂ) (r : ZMod p) : ℂ :=
  avgZMod fun x => ZMod.stdAddChar (r * x) * φ x

/-- The right test Fourier factor appearing after expanding the Cayley kernel. -/
noncomputable def rightFourierTest {p : ℕ} [NeZero p]
    (ψ : ZMod p → ℂ) (r : ZMod p) : ℂ :=
  avgZMod fun y => ZMod.stdAddChar (-(r * y)) * ψ y

lemma rightFourierTest_eq_normalizedDftFunction {p : ℕ} [NeZero p]
    (ψ : ZMod p → ℂ) (r : ZMod p) :
    rightFourierTest ψ r = normalizedDftFunction ψ r := by
  dsimp [rightFourierTest, avgZMod]
  rw [normalizedDftFunction_eq_sum (p := p) ψ r]
  apply congrArg (fun S : ℂ => ((p : ℂ)⁻¹) * S)
  refine Finset.sum_congr rfl ?_
  intro y _
  rw [mul_comm r y]

lemma leftFourierTest_eq_normalizedDftFunction_neg {p : ℕ} [NeZero p]
    (φ : ZMod p → ℂ) (r : ZMod p) :
    leftFourierTest φ r = normalizedDftFunction φ (-r) := by
  dsimp [leftFourierTest, avgZMod]
  rw [normalizedDftFunction_eq_sum (p := p) φ (-r)]
  apply congrArg (fun S : ℂ => ((p : ℂ)⁻¹) * S)
  refine Finset.sum_congr rfl ?_
  intro x _
  congr 1
  simp [mul_comm]

lemma sum_sq_norm_rightFourierTest_eq_normalizedDftFunction
    {p : ℕ} [NeZero p] (ψ : ZMod p → ℂ) :
    (∑ r : ZMod p, ‖rightFourierTest ψ r‖ ^ 2) =
      ∑ r : ZMod p, ‖normalizedDftFunction ψ r‖ ^ 2 := by
  refine Finset.sum_congr rfl ?_
  intro r _
  rw [rightFourierTest_eq_normalizedDftFunction]

lemma sum_sq_norm_leftFourierTest_eq_normalizedDftFunction
    {p : ℕ} [NeZero p] (φ : ZMod p → ℂ) :
    (∑ r : ZMod p, ‖leftFourierTest φ r‖ ^ 2) =
      ∑ r : ZMod p, ‖normalizedDftFunction φ r‖ ^ 2 := by
  classical
  calc
    (∑ r : ZMod p, ‖leftFourierTest φ r‖ ^ 2) =
        ∑ r : ZMod p, ‖normalizedDftFunction φ (-r)‖ ^ 2 := by
          refine Finset.sum_congr rfl ?_
          intro r _
          rw [leftFourierTest_eq_normalizedDftFunction_neg]
    _ = ∑ r : ZMod p, ‖normalizedDftFunction φ r‖ ^ 2 := by
          refine Fintype.sum_equiv (Equiv.neg (ZMod p)) _ _ ?_
          intro r
          simp

lemma star_stdAddChar_neg_mul {p : ℕ} [NeZero p] (x r : ZMod p) :
    (starRingEnd ℂ) (ZMod.stdAddChar (-(x * r))) =
      ZMod.stdAddChar (x * r) := by
  have h := AddChar.map_neg_eq_conj (ZMod.stdAddChar (N := p)) (x * r)
  simp [h]

lemma star_normalizedDftFunction {p : ℕ} [NeZero p]
    (f : ZMod p → ℂ) (r : ZMod p) :
    (starRingEnd ℂ) (normalizedDftFunction f r) =
      ((p : ℂ)⁻¹) *
        ∑ x : ZMod p, ZMod.stdAddChar (x * r) * (starRingEnd ℂ) (f x) := by
  rw [normalizedDftFunction_eq_sum]
  simp [map_sum, star_stdAddChar_neg_mul, mul_comm]

lemma avg_stdAddChar_mul_star_eq_star_normalizedDftFunction
    {p : ℕ} [NeZero p] (g : ZMod p → ℂ) (r : ZMod p) :
    avgZMod (fun x => ZMod.stdAddChar (r * x) * (starRingEnd ℂ) (g x)) =
      (starRingEnd ℂ) (normalizedDftFunction g r) := by
  rw [star_normalizedDftFunction, avgZMod]
  apply congrArg (fun S : ℂ => ((p : ℂ)⁻¹) * S)
  refine Finset.sum_congr rfl ?_
  intro x _
  rw [mul_comm r x]

/-- Parseval cross identity in normalized-average form. -/
lemma avg_mul_star_eq_sum_normalizedDftFunction {p : ℕ} [NeZero p]
    (f g : ZMod p → ℂ) :
    avgZMod (fun x => f x * (starRingEnd ℂ) (g x)) =
      ∑ r : ZMod p,
        normalizedDftFunction f r * (starRingEnd ℂ) (normalizedDftFunction g r) := by
  classical
  calc
    avgZMod (fun x => f x * (starRingEnd ℂ) (g x)) =
        avgZMod
          (fun x =>
            (∑ r : ZMod p, ZMod.stdAddChar (r * x) * normalizedDftFunction f r) *
              (starRingEnd ℂ) (g x)) := by
          congr 1
          funext x
          rw [← function_eq_sum_normalizedDftFunction (p := p) f x]
    _ = avgZMod
          (fun x =>
            ∑ r : ZMod p,
              normalizedDftFunction f r *
                (ZMod.stdAddChar (r * x) * (starRingEnd ℂ) (g x))) := by
          congr 1
          funext x
          rw [Finset.sum_mul]
          refine Finset.sum_congr rfl ?_
          intro r _
          ring
    _ = ∑ r : ZMod p,
        normalizedDftFunction f r * (starRingEnd ℂ) (normalizedDftFunction g r) := by
          rw [avgZMod_sum]
          refine Finset.sum_congr rfl ?_
          intro r _
          rw [avgZMod_const_mul, avg_stdAddChar_mul_star_eq_star_normalizedDftFunction]

/-- Parseval in the normalized convention used here. -/
lemma sum_sq_norm_normalizedDftFunction_eq_avg
    {p : ℕ} [NeZero p] (f : ZMod p → ℂ) :
    (∑ r : ZMod p, ‖normalizedDftFunction f r‖ ^ 2) =
      ((p : ℝ)⁻¹) * ∑ x : ZMod p, ‖f x‖ ^ 2 := by
  classical
  apply Complex.ofReal_injective
  have hcomplex :
      ((p : ℂ)⁻¹) * ∑ x : ZMod p, (‖f x‖ : ℂ) ^ 2 =
        ∑ r : ZMod p, (‖normalizedDftFunction f r‖ : ℂ) ^ 2 := by
    calc
      ((p : ℂ)⁻¹) * ∑ x : ZMod p, (‖f x‖ : ℂ) ^ 2 =
          avgZMod (fun x => f x * (starRingEnd ℂ) (f x)) := by
            unfold avgZMod
            apply congrArg (fun S : ℂ => ((p : ℂ)⁻¹) * S)
            refine Finset.sum_congr rfl ?_
            intro x _
            rw [← Complex.mul_conj']
      _ = ∑ r : ZMod p,
          normalizedDftFunction f r * (starRingEnd ℂ) (normalizedDftFunction f r) :=
            avg_mul_star_eq_sum_normalizedDftFunction f f
      _ = ∑ r : ZMod p, (‖normalizedDftFunction f r‖ : ℂ) ^ 2 := by
            refine Finset.sum_congr rfl ?_
            intro r _
            rw [Complex.mul_conj']
  simpa [Complex.ofReal_sum, Complex.ofReal_mul, Complex.ofReal_inv,
    Complex.ofReal_pow, Complex.ofReal_natCast] using hcomplex.symm

lemma sum_sq_norm_normalizedDftFunction_le_one_of_norm_le_one
    {p : ℕ} [NeZero p] {f : ZMod p → ℂ}
    (hf : ∀ x, ‖f x‖ ≤ 1) :
    (∑ r : ZMod p, ‖normalizedDftFunction f r‖ ^ 2) ≤ 1 := by
  classical
  rw [sum_sq_norm_normalizedDftFunction_eq_avg]
  have hsum : (∑ x : ZMod p, ‖f x‖ ^ 2) ≤ (p : ℝ) := by
    calc
      (∑ x : ZMod p, ‖f x‖ ^ 2) ≤ ∑ _x : ZMod p, (1 : ℝ) := by
        refine Finset.sum_le_sum ?_
        intro x _
        have hx_nonneg : 0 ≤ ‖f x‖ := norm_nonneg _
        have hx_le : ‖f x‖ ^ 2 ≤ (1 : ℝ) := by
          nlinarith [hf x]
        exact hx_le
      _ = (p : ℝ) := by simp [ZMod.card]
  have hp_nonneg : 0 ≤ ((p : ℝ)⁻¹) := inv_nonneg.mpr (Nat.cast_nonneg p)
  have hp_ne : (p : ℝ) ≠ 0 := by exact_mod_cast (NeZero.ne p)
  calc
    ((p : ℝ)⁻¹) * ∑ x : ZMod p, ‖f x‖ ^ 2
        ≤ ((p : ℝ)⁻¹) * (p : ℝ) := mul_le_mul_of_nonneg_left hsum hp_nonneg
    _ = 1 := inv_mul_cancel₀ hp_ne

lemma sum_sq_norm_rightFourierTest_le_one_of_norm_le_one
    {p : ℕ} [NeZero p] {ψ : ZMod p → ℂ}
    (hψ : ∀ y, ‖ψ y‖ ≤ 1) :
    (∑ r : ZMod p, ‖rightFourierTest ψ r‖ ^ 2) ≤ 1 := by
  rw [sum_sq_norm_rightFourierTest_eq_normalizedDftFunction]
  exact sum_sq_norm_normalizedDftFunction_le_one_of_norm_le_one hψ

lemma sum_sq_norm_leftFourierTest_le_one_of_norm_le_one
    {p : ℕ} [NeZero p] {φ : ZMod p → ℂ}
    (hφ : ∀ x, ‖φ x‖ ≤ 1) :
    (∑ r : ZMod p, ‖leftFourierTest φ r‖ ^ 2) ≤ 1 := by
  rw [sum_sq_norm_leftFourierTest_eq_normalizedDftFunction]
  exact sum_sq_norm_normalizedDftFunction_le_one_of_norm_le_one hφ

lemma stdAddChar_mul_sub {p : ℕ} [NeZero p] (r x y : ZMod p) :
    ZMod.stdAddChar (r * (x - y)) =
      ZMod.stdAddChar (r * x) * ZMod.stdAddChar (-(r * y)) := by
  rw [← ZMod.stdAddChar.map_add_eq_mul]
  congr 1
  ring

lemma sum_stdAddChar_mul_eq_zero_of_ne_zero
    {p : ℕ} [NeZero p] {t : ZMod p} (ht : t ≠ 0) :
    ∑ r : ZMod p, ZMod.stdAddChar (r * t) = 0 := by
  classical
  have hnontrivial :
      AddChar.mulShift (ZMod.stdAddChar (N := p)) t ≠ 1 :=
    (ZMod.isPrimitive_stdAddChar p) ht
  have hsum :
      ∑ r : ZMod p, AddChar.mulShift (ZMod.stdAddChar (N := p)) t r = 0 :=
    AddChar.sum_eq_zero_of_ne_one hnontrivial
  simpa [AddChar.mulShift_apply, mul_comm, mul_left_comm, mul_assoc] using hsum

/-- Orthogonality of the standard additive characters on `ZMod p`, in the
summation direction needed for Parseval. -/
lemma sum_stdAddChar_mul_sub_eq_card_if {p : ℕ} [NeZero p] (x y : ZMod p) :
    ∑ r : ZMod p, ZMod.stdAddChar (r * (x - y)) =
      if x = y then (p : ℂ) else 0 := by
  classical
  by_cases hxy : x = y
  · simp [hxy, ZMod.card]
  · have hsub : x - y ≠ 0 := sub_ne_zero.mpr hxy
    simp [hxy, sum_stdAddChar_mul_eq_zero_of_ne_zero (p := p) hsub]

/-- Characters diagonalize the finite Cayley convolution operator. -/
lemma cayleyConvolution_stdAddChar {p : ℕ} [NeZero p]
    (a : ZMod p → ℂ) (r x : ZMod p) :
    cayleyConvolution a (fun y => ZMod.stdAddChar (r * y)) x =
      normalizedDftFunction a r * ZMod.stdAddChar (r * x) := by
  classical
  unfold cayleyConvolution avgZMod
  rw [normalizedDftFunction_eq_sum]
  have hchange :
      (∑ y : ZMod p, a (x - y) * ZMod.stdAddChar (r * y)) =
        ∑ z : ZMod p, a z * ZMod.stdAddChar (r * (x - z)) := by
    refine Fintype.sum_equiv (Equiv.subLeft x) _ _ ?_
    intro y
    simp [Equiv.subLeft_apply]
  rw [hchange]
  calc
    ((p : ℂ)⁻¹) * (∑ z : ZMod p, a z * ZMod.stdAddChar (r * (x - z))) =
        ((p : ℂ)⁻¹) *
          (ZMod.stdAddChar (r * x) *
            ∑ z : ZMod p, ZMod.stdAddChar (-(z * r)) * a z) := by
          congr 1
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl ?_
          intro z _
          rw [stdAddChar_mul_sub]
          have hrz : -(r * z) = -(z * r) := by ring
          rw [hrz]
          ring
    _ = (((p : ℂ)⁻¹) * ∑ z : ZMod p, ZMod.stdAddChar (-(z * r)) * a z) *
          ZMod.stdAddChar (r * x) := by
          ring

/-- Fourier diagonalization of the Cayley convolution operator on an arbitrary
test function. -/
lemma cayleyConvolution_eq_fourier_sum {p : ℕ} [NeZero p]
    (a ψ : ZMod p → ℂ) (x : ZMod p) :
    cayleyConvolution a ψ x =
      ∑ r : ZMod p,
        normalizedDftFunction ψ r * normalizedDftFunction a r *
          ZMod.stdAddChar (r * x) := by
  classical
  unfold cayleyConvolution
  simp_rw [function_eq_sum_normalizedDftFunction (p := p) ψ]
  calc
    avgZMod
        (fun y : ZMod p =>
          a (x - y) *
            ∑ r : ZMod p, ZMod.stdAddChar (r * y) * normalizedDftFunction ψ r) =
        avgZMod
          (fun y : ZMod p =>
            ∑ r : ZMod p,
              normalizedDftFunction ψ r *
                (a (x - y) * ZMod.stdAddChar (r * y))) := by
          congr 1
          funext y
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl ?_
          intro r _
          ring
    _ = ∑ r : ZMod p,
        normalizedDftFunction ψ r * normalizedDftFunction a r *
          ZMod.stdAddChar (r * x) := by
          rw [avgZMod_sum]
          refine Finset.sum_congr rfl ?_
          intro r _
          rw [avgZMod_const_mul]
          change normalizedDftFunction ψ r *
              cayleyConvolution a (fun y => ZMod.stdAddChar (r * y)) x =
            normalizedDftFunction ψ r * normalizedDftFunction a r *
              ZMod.stdAddChar (r * x)
          rw [cayleyConvolution_stdAddChar]
          ring

/-- Fourier inversion applied to the Cayley kernel `a(x-y)`, in the exact
factorized form used by the spectral-cut argument. -/
lemma cayleyKernel_eq_fourier_sum {p : ℕ} [NeZero p]
    (a : ZMod p → ℂ) (x y : ZMod p) :
    a (x - y) =
      ∑ r : ZMod p,
        normalizedDftFunction a r *
          ZMod.stdAddChar (r * x) *
          ZMod.stdAddChar (-(r * y)) := by
  calc
    a (x - y) =
        ∑ r : ZMod p, ZMod.stdAddChar (r * (x - y)) *
          normalizedDftFunction a r := by
          exact function_eq_sum_normalizedDftFunction (p := p) a (x - y)
    _ = ∑ r : ZMod p,
        normalizedDftFunction a r *
          ZMod.stdAddChar (r * x) *
          ZMod.stdAddChar (-(r * y)) := by
          refine Finset.sum_congr rfl ?_
          intro r _
          rw [stdAddChar_mul_sub]
          ring

/-- The same kernel expansion with the two test functions multiplied in. -/
lemma cayleyKernel_mul_tests_eq_fourier_sum {p : ℕ} [NeZero p]
    (a φ ψ : ZMod p → ℂ) (x y : ZMod p) :
    a (x - y) * φ x * ψ y =
      ∑ r : ZMod p,
        normalizedDftFunction a r *
          (ZMod.stdAddChar (r * x) * φ x) *
          (ZMod.stdAddChar (-(r * y)) * ψ y) := by
  rw [cayleyKernel_eq_fourier_sum (p := p) a x y]
  simp only [Finset.sum_mul]
  refine Finset.sum_congr rfl ?_
  intro r _
  ring

/-- The double-average Cayley cut functional factors through the normalized
Fourier coefficients of the kernel and the two test Fourier factors.  This is
the algebraic core of the spectral cut-norm bound in compact-Cayley Lemma 2.5. -/
lemma cayleyCutFunctional_eq_fourier_sum {p : ℕ} [NeZero p]
    (a φ ψ : ZMod p → ℂ) :
    cayleyCutFunctional a φ ψ =
      ∑ r : ZMod p,
        normalizedDftFunction a r * leftFourierTest φ r * rightFourierTest ψ r := by
  classical
  unfold cayleyCutFunctional
  simp_rw [cayleyKernel_mul_tests_eq_fourier_sum (p := p) a φ ψ]
  calc
    avgZMod
        (fun x : ZMod p =>
          avgZMod
            (fun y : ZMod p =>
              ∑ r : ZMod p,
                normalizedDftFunction a r *
                  (ZMod.stdAddChar (r * x) * φ x) *
                  (ZMod.stdAddChar (-(r * y)) * ψ y))) =
        avgZMod
          (fun x : ZMod p =>
            ∑ r : ZMod p,
              normalizedDftFunction a r *
                (ZMod.stdAddChar (r * x) * φ x) *
                rightFourierTest ψ r) := by
          congr 1
          funext x
          rw [avgZMod_sum]
          refine Finset.sum_congr rfl ?_
          intro r _
          rw [avgZMod_const_mul]
          simp [rightFourierTest, mul_assoc]
    _ = ∑ r : ZMod p,
        normalizedDftFunction a r * leftFourierTest φ r * rightFourierTest ψ r := by
          rw [avgZMod_sum]
          refine Finset.sum_congr rfl ?_
          intro r _
          rw [avgZMod_mul_const, avgZMod_const_mul]
          simp [leftFourierTest, mul_assoc]

/-- Immediate `L¹` Fourier bound for the Cayley cut functional.  Lemma 2.5
will sharpen this to the spectral supremum under `‖φ‖∞, ‖ψ‖∞ ≤ 1`, using the
Hilbert-space/operator-norm argument from the compact-Cayley PDF. -/
lemma norm_cayleyCutFunctional_le_fourier_l1 {p : ℕ} [NeZero p]
    (a φ ψ : ZMod p → ℂ) :
    ‖cayleyCutFunctional a φ ψ‖ ≤
      ∑ r : ZMod p,
        ‖normalizedDftFunction a r‖ * ‖leftFourierTest φ r‖ *
          ‖rightFourierTest ψ r‖ := by
  rw [cayleyCutFunctional_eq_fourier_sum]
  refine (norm_sum_le _ _).trans ?_
  refine Finset.sum_le_sum ?_
  intro r _
  rw [norm_mul, norm_mul]

/-- Cauchy-Schwarz sharpening of the Fourier `L¹` bound, assuming the two
test-factor Fourier `L²` sums are at most `1`.  This is the finite analytic
core that remains after Parseval supplies those two `L²` hypotheses from
`‖φ‖∞, ‖ψ‖∞ ≤ 1`. -/
lemma norm_cayleyCutFunctional_le_spectral_of_fourier_l2
    {p : ℕ} [NeZero p] (a φ ψ : ZMod p → ℂ) {M : ℝ}
    (hM : ∀ r : ZMod p, ‖normalizedDftFunction a r‖ ≤ M)
    (hMnonneg : 0 ≤ M)
    (hφ2 : (∑ r : ZMod p, ‖leftFourierTest φ r‖ ^ 2) ≤ 1)
    (hψ2 : (∑ r : ZMod p, ‖rightFourierTest ψ r‖ ^ 2) ≤ 1) :
    ‖cayleyCutFunctional a φ ψ‖ ≤ M := by
  classical
  let L : ZMod p → ℝ := fun r => ‖leftFourierTest φ r‖
  let R : ZMod p → ℝ := fun r => ‖rightFourierTest ψ r‖
  have h_l1 :
      ‖cayleyCutFunctional a φ ψ‖ ≤ ∑ r : ZMod p,
        ‖normalizedDftFunction a r‖ * L r * R r := by
    simpa [L, R, mul_assoc] using norm_cayleyCutFunctional_le_fourier_l1 a φ ψ
  have h_by_M :
      ∑ r : ZMod p, ‖normalizedDftFunction a r‖ * L r * R r ≤
        ∑ r : ZMod p, M * (L r * R r) := by
    refine Finset.sum_le_sum ?_
    intro r _
    have hLR : 0 ≤ L r * R r := mul_nonneg (norm_nonneg _) (norm_nonneg _)
    calc
      ‖normalizedDftFunction a r‖ * L r * R r =
          ‖normalizedDftFunction a r‖ * (L r * R r) := by ring
      _ ≤ M * (L r * R r) := mul_le_mul_of_nonneg_right (hM r) hLR
  have hcs :
      ∑ r : ZMod p, L r * R r ≤
        Real.sqrt (∑ r : ZMod p, L r ^ 2) *
          Real.sqrt (∑ r : ZMod p, R r ^ 2) := by
    simpa [L, R] using
      (Real.sum_mul_le_sqrt_mul_sqrt (Finset.univ : Finset (ZMod p)) L R)
  have hsqrtL : Real.sqrt (∑ r : ZMod p, L r ^ 2) ≤ 1 := by
    rw [Real.sqrt_le_one]
    simpa [L] using hφ2
  have hsqrtR : Real.sqrt (∑ r : ZMod p, R r ^ 2) ≤ 1 := by
    rw [Real.sqrt_le_one]
    simpa [R] using hψ2
  have hsqrt_nonneg_L : 0 ≤ Real.sqrt (∑ r : ZMod p, L r ^ 2) := Real.sqrt_nonneg _
  have hsqrt_nonneg_R : 0 ≤ Real.sqrt (∑ r : ZMod p, R r ^ 2) := Real.sqrt_nonneg _
  have hprod :
      Real.sqrt (∑ r : ZMod p, L r ^ 2) *
          Real.sqrt (∑ r : ZMod p, R r ^ 2) ≤ 1 := by
    nlinarith
  have hsumLR : ∑ r : ZMod p, L r * R r ≤ 1 := hcs.trans hprod
  calc
    ‖cayleyCutFunctional a φ ψ‖
        ≤ ∑ r : ZMod p, ‖normalizedDftFunction a r‖ * L r * R r := h_l1
    _ ≤ ∑ r : ZMod p, M * (L r * R r) := h_by_M
    _ = M * ∑ r : ZMod p, L r * R r := by rw [Finset.mul_sum]
    _ ≤ M * 1 := mul_le_mul_of_nonneg_left hsumLR hMnonneg
    _ = M := by ring

/-- Finite spectral cut-norm control for one pair of bounded test functions.

This is the usable Lemma 2.5 core for the compact-Cayley route: if every
normalized Fourier coefficient of the Cayley kernel `a` has norm at most `M`,
then every double average against tests bounded by `1` has norm at most `M`. -/
lemma norm_cayleyCutFunctional_le_spectral
    {p : ℕ} [NeZero p] (a φ ψ : ZMod p → ℂ) {M : ℝ}
    (hM : ∀ r : ZMod p, ‖normalizedDftFunction a r‖ ≤ M)
    (hMnonneg : 0 ≤ M)
    (hφ : ∀ x, ‖φ x‖ ≤ 1)
    (hψ : ∀ y, ‖ψ y‖ ≤ 1) :
    ‖cayleyCutFunctional a φ ψ‖ ≤ M := by
  exact norm_cayleyCutFunctional_le_spectral_of_fourier_l2 a φ ψ hM hMnonneg
    (sum_sq_norm_leftFourierTest_le_one_of_norm_le_one hφ)
    (sum_sq_norm_rightFourierTest_le_one_of_norm_le_one hψ)

/-- Predicate form of the spectral coefficient bound. -/
def SpectralBound {p : ℕ} [NeZero p] (a : ZMod p → ℂ) (M : ℝ) : Prop :=
  ∀ r : ZMod p, ‖normalizedDftFunction a r‖ ≤ M

/-- Predicate form of the Cayley cut-norm bound: every double average against
tests bounded by `1` has norm at most `M`. -/
def CayleyCutBound {p : ℕ} [NeZero p] (a : ZMod p → ℂ) (M : ℝ) : Prop :=
  ∀ φ ψ : ZMod p → ℂ,
    (∀ x, ‖φ x‖ ≤ 1) → (∀ y, ‖ψ y‖ ≤ 1) →
      ‖cayleyCutFunctional a φ ψ‖ ≤ M

/-- Compact-Cayley Lemma 2.5 in predicate form. -/
theorem cayleyCutBound_of_spectralBound
    {p : ℕ} [NeZero p] (a : ZMod p → ℂ) {M : ℝ}
    (hMnonneg : 0 ≤ M) (hM : SpectralBound a M) :
    CayleyCutBound a M := by
  intro φ ψ hφ hψ
  exact norm_cayleyCutFunctional_le_spectral a φ ψ hM hMnonneg hφ hψ

end Erdos42.CompactCayley


/-! =============================================================
    Section from: Erdos/P42/CompactCayley/CountingConvergence.lean
    ============================================================= -/

/-
Erdős Problem 42 — finite density target for compact-Cayley counting convergence.

This file does not prove the compactness/counting-convergence lemma yet.  It
sets up the exact finite `K_ℓ` density that Lemma 2.6 should converge to, and
connects its indicator-specialized form to the existing finite clique endpoint.
-/


namespace Erdos42.CompactCayley

open Finset Erdos42 Filter
open scoped Topology

/-- Normalized average over a nonempty finite type.  This is used for the
remaining coordinates after a single clique edge has been isolated. -/
noncomputable def avgFinite (α : Type*) [Fintype α] (f : α → ℂ) : ℂ :=
  ((Fintype.card α : ℂ)⁻¹) * ∑ x : α, f x

lemma norm_avgFinite_le {α : Type*} [Fintype α] [Nonempty α]
    {f : α → ℂ} {M : ℝ} (hf : ∀ x, ‖f x‖ ≤ M) :
    ‖avgFinite α f‖ ≤ M := by
  classical
  have hcard_pos_nat : 0 < Fintype.card α := Fintype.card_pos
  have hcard_pos : 0 < (Fintype.card α : ℝ) := by exact_mod_cast hcard_pos_nat
  have hsum :
      ‖∑ x : α, f x‖ ≤ (Fintype.card α : ℝ) * M := by
    calc
      ‖∑ x : α, f x‖ ≤ ∑ x : α, ‖f x‖ := norm_sum_le _ _
      _ ≤ ∑ _x : α, M := by
        exact Finset.sum_le_sum (fun x _hx => hf x)
      _ = (Fintype.card α : ℝ) * M := by simp
  unfold avgFinite
  calc
    ‖((Fintype.card α : ℂ)⁻¹) * ∑ x : α, f x‖
        = ‖((Fintype.card α : ℂ)⁻¹)‖ * ‖∑ x : α, f x‖ := norm_mul _ _
    _ ≤ ‖((Fintype.card α : ℂ)⁻¹)‖ * ((Fintype.card α : ℝ) * M) :=
        mul_le_mul_of_nonneg_left hsum (norm_nonneg _)
    _ = M := by
      rw [norm_inv, Complex.norm_natCast]
      field_simp [ne_of_gt hcard_pos]

lemma norm_avgZMod_le {p : ℕ} [NeZero p] {f : ZMod p → ℂ} {M : ℝ}
    (hf : ∀ x, ‖f x‖ ≤ M) :
    ‖avgZMod f‖ ≤ M := by
  simpa [avgFinite, avgZMod, ZMod.card] using
    norm_avgFinite_le (α := ZMod p) (f := f) hf

/-- Averaging Cayley cut functionals over a nonempty finite parameter set does
not increase a uniform Cayley cut bound.  This is the reusable analytic estimate
for one-edge replacement after the remaining vertices are frozen. -/
lemma norm_avgFinite_cayleyCutFunctional_le
    {ι : Type*} [Fintype ι] [Nonempty ι]
    {p : ℕ} [NeZero p] {a : ZMod p → ℂ} {M : ℝ}
    (hcut : CayleyCutBound a M)
    (φ ψ : ι → ZMod p → ℂ)
    (hφ : ∀ t x, ‖φ t x‖ ≤ 1)
    (hψ : ∀ t y, ‖ψ t y‖ ≤ 1) :
    ‖avgFinite ι (fun t => cayleyCutFunctional a (φ t) (ψ t))‖ ≤ M := by
  exact norm_avgFinite_le (fun t => hcut (φ t) (ψ t) (hφ t) (hψ t))

/-- Indices other than the two endpoints of a chosen clique edge. -/
def EdgeRest {ℓ : ℕ} (e₀ : Fin ℓ × Fin ℓ) : Type :=
  {k : Fin ℓ // k ≠ e₀.1 ∧ k ≠ e₀.2}

instance instFintypeEdgeRest {ℓ : ℕ} (e₀ : Fin ℓ × Fin ℓ) :
    Fintype (EdgeRest e₀) := by
  classical
  unfold EdgeRest
  infer_instance

noncomputable instance instDecidableEqEdgeRest {ℓ : ℕ} (e₀ : Fin ℓ × Fin ℓ) :
    DecidableEq (EdgeRest e₀) := by
  classical
  infer_instance

/-- Assignments to all non-endpoint coordinates of a chosen clique edge. -/
abbrev EdgeRestAssignment (p ℓ : ℕ) (e₀ : Fin ℓ × Fin ℓ) : Type :=
  EdgeRest e₀ → ZMod p

noncomputable instance instFintypeEdgeRestAssignment {p ℓ : ℕ} [NeZero p]
    (e₀ : Fin ℓ × Fin ℓ) : Fintype (EdgeRestAssignment p ℓ e₀) := by
  unfold EdgeRestAssignment
  infer_instance

/-- Extend a frozen assignment on the remaining vertices by assigning `u` and
`v` to the two endpoints of the chosen edge. -/
noncomputable def extendEdgeTuple {p ℓ : ℕ} (e₀ : Fin ℓ × Fin ℓ)
    (r : EdgeRestAssignment p ℓ e₀) (u v : ZMod p) : Fin ℓ → ZMod p :=
  fun k =>
    if h1 : k = e₀.1 then u
    else if h2 : k = e₀.2 then v
    else r ⟨k, h1, h2⟩

@[simp] lemma extendEdgeTuple_left {p ℓ : ℕ} (e₀ : Fin ℓ × Fin ℓ)
    (r : EdgeRestAssignment p ℓ e₀) (u v : ZMod p) :
    extendEdgeTuple e₀ r u v e₀.1 = u := by
  simp [extendEdgeTuple]

@[simp] lemma extendEdgeTuple_right {p ℓ : ℕ} {e₀ : Fin ℓ × Fin ℓ}
    (hne : e₀.2 ≠ e₀.1) (r : EdgeRestAssignment p ℓ e₀) (u v : ZMod p) :
    extendEdgeTuple e₀ r u v e₀.2 = v := by
  simp [extendEdgeTuple, hne]

lemma extendEdgeTuple_rest {p ℓ : ℕ} (e₀ : Fin ℓ × Fin ℓ)
    (r : EdgeRestAssignment p ℓ e₀) (u v : ZMod p)
    {k : Fin ℓ} (h1 : k ≠ e₀.1) (h2 : k ≠ e₀.2) :
    extendEdgeTuple e₀ r u v k = r ⟨k, h1, h2⟩ := by
  simp [extendEdgeTuple, h1, h2]

lemma extendEdgeTuple_edge_diff {p ℓ : ℕ} {e₀ : Fin ℓ × Fin ℓ}
    (hne : e₀.1 ≠ e₀.2) (r : EdgeRestAssignment p ℓ e₀) (u v : ZMod p) :
    extendEdgeTuple e₀ r u v e₀.1 - extendEdgeTuple e₀ r u v e₀.2 = u - v := by
  simp [extendEdgeTuple_right (e₀ := e₀) (show e₀.2 ≠ e₀.1 from hne.symm)]

lemma extendEdgeTuple_edge_diff_of_mem_cliqueEdgePairs {p ℓ : ℕ}
    {e₀ : Fin ℓ × Fin ℓ} (he₀ : e₀ ∈ cliqueEdgePairs ℓ)
    (r : EdgeRestAssignment p ℓ e₀) (u v : ZMod p) :
    extendEdgeTuple e₀ r u v e₀.1 - extendEdgeTuple e₀ r u v e₀.2 = u - v :=
  extendEdgeTuple_edge_diff (cliqueEdgePairs_left_ne_right he₀) r u v

/-- An edge is incident to a vertex. -/
def edgeUsesVertex {ℓ : ℕ} (e : Fin ℓ × Fin ℓ) (i : Fin ℓ) : Prop :=
  e.1 = i ∨ e.2 = i

instance instDecidableEdgeUsesVertex {ℓ : ℕ} (e : Fin ℓ × Fin ℓ) (i : Fin ℓ) :
    Decidable (edgeUsesVertex e i) := by
  unfold edgeUsesVertex
  infer_instance

/-- All clique edges except the edge currently being replaced. -/
def remainingCliqueEdges {ℓ : ℕ} (e₀ : Fin ℓ × Fin ℓ) : Finset (Fin ℓ × Fin ℓ) :=
  cliqueEdgePairs ℓ \ {e₀}

/-- Remaining clique edges incident to the left endpoint of the replaced edge. -/
def leftCliqueEdges {ℓ : ℕ} (e₀ : Fin ℓ × Fin ℓ) : Finset (Fin ℓ × Fin ℓ) :=
  (remainingCliqueEdges e₀).filter (fun e => edgeUsesVertex e e₀.1)

/-- Remaining clique edges incident to the right endpoint but not the left
endpoint of the replaced edge. -/
def rightCliqueEdges {ℓ : ℕ} (e₀ : Fin ℓ × Fin ℓ) : Finset (Fin ℓ × Fin ℓ) :=
  (remainingCliqueEdges e₀).filter
    (fun e => ¬ edgeUsesVertex e e₀.1 ∧ edgeUsesVertex e e₀.2)

/-- Remaining clique edges incident to neither endpoint of the replaced edge. -/
def constantCliqueEdges {ℓ : ℕ} (e₀ : Fin ℓ × Fin ℓ) : Finset (Fin ℓ × Fin ℓ) :=
  (remainingCliqueEdges e₀).filter
    (fun e => ¬ edgeUsesVertex e e₀.1 ∧ ¬ edgeUsesVertex e e₀.2)

lemma edge_not_uses_both_endpoints_of_mem_remaining {ℓ : ℕ}
    {e₀ e : Fin ℓ × Fin ℓ} (he₀ : e₀ ∈ cliqueEdgePairs ℓ)
    (he : e ∈ remainingCliqueEdges e₀)
    (hleft : edgeUsesVertex e e₀.1) (hright : edgeUsesVertex e e₀.2) : False := by
  have he_pair : e ∈ cliqueEdgePairs ℓ := (Finset.mem_sdiff.mp he).1
  have hne_single : e ∉ ({e₀} : Finset (Fin ℓ × Fin ℓ)) := (Finset.mem_sdiff.mp he).2
  have hlt_e : e.1 < e.2 := cliqueEdgePairs_left_lt_right he_pair
  have hlt_e₀ : e₀.1 < e₀.2 := cliqueEdgePairs_left_lt_right he₀
  rcases hleft with hleft | hleft <;> rcases hright with hright | hright
  · have h_eq : e₀.1 = e₀.2 := hleft.symm.trans hright
    exact (ne_of_lt hlt_e₀) h_eq
  · have h_eq : e = e₀ := Prod.ext hleft hright
    exact hne_single (by simp [h_eq])
  · have hbad : e₀.2 < e₀.1 := by simpa [hleft, hright] using hlt_e
    exact (not_lt_of_ge (le_of_lt hlt_e₀)) hbad
  · have h_eq : e₀.1 = e₀.2 := hleft.symm.trans hright
    exact (ne_of_lt hlt_e₀) h_eq

lemma extendEdgeTuple_eq_of_same_left {p ℓ : ℕ} {e₀ : Fin ℓ × Fin ℓ}
    (r : EdgeRestAssignment p ℓ e₀) (u v v' : ZMod p) {k : Fin ℓ}
    (h2 : k ≠ e₀.2) :
    extendEdgeTuple e₀ r u v k = extendEdgeTuple e₀ r u v' k := by
  by_cases h1 : k = e₀.1
  · subst h1
    simp [extendEdgeTuple]
  · rw [extendEdgeTuple_rest e₀ r u v h1 h2,
      extendEdgeTuple_rest e₀ r u v' h1 h2]

lemma extendEdgeTuple_eq_of_same_right {p ℓ : ℕ} {e₀ : Fin ℓ × Fin ℓ}
    (r : EdgeRestAssignment p ℓ e₀) (u u' v : ZMod p) {k : Fin ℓ}
    (h1 : k ≠ e₀.1) :
    extendEdgeTuple e₀ r u v k = extendEdgeTuple e₀ r u' v k := by
  by_cases h2 : k = e₀.2
  · subst h2
    simp [extendEdgeTuple, h1]
  · rw [extendEdgeTuple_rest e₀ r u v h1 h2,
      extendEdgeTuple_rest e₀ r u' v h1 h2]

lemma extendEdgeTuple_eq_of_not_endpoints {p ℓ : ℕ} {e₀ : Fin ℓ × Fin ℓ}
    (r : EdgeRestAssignment p ℓ e₀) (u v u' v' : ZMod p) {k : Fin ℓ}
    (h1 : k ≠ e₀.1) (h2 : k ≠ e₀.2) :
    extendEdgeTuple e₀ r u v k = extendEdgeTuple e₀ r u' v' k := by
  rw [extendEdgeTuple_rest e₀ r u v h1 h2,
    extendEdgeTuple_rest e₀ r u' v' h1 h2]

/-- Product over remaining edges incident to the left endpoint.  It only
depends on the left endpoint variable. -/
noncomputable def remainingLeftTest {p ℓ : ℕ} [NeZero p]
    (F : (Fin ℓ × Fin ℓ) → ZMod p → ℂ) (e₀ : Fin ℓ × Fin ℓ)
    (r : EdgeRestAssignment p ℓ e₀) (u : ZMod p) : ℂ :=
  ∏ e ∈ leftCliqueEdges e₀,
    F e (extendEdgeTuple e₀ r u 0 e.1 - extendEdgeTuple e₀ r u 0 e.2)

/-- Product over remaining edges incident to the right endpoint but not the
left endpoint.  It only depends on the right endpoint variable. -/
noncomputable def remainingRightTest {p ℓ : ℕ} [NeZero p]
    (F : (Fin ℓ × Fin ℓ) → ZMod p → ℂ) (e₀ : Fin ℓ × Fin ℓ)
    (r : EdgeRestAssignment p ℓ e₀) (v : ZMod p) : ℂ :=
  ∏ e ∈ rightCliqueEdges e₀,
    F e (extendEdgeTuple e₀ r 0 v e.1 - extendEdgeTuple e₀ r 0 v e.2)

/-- Product over remaining edges incident to neither endpoint.  It is constant
in the two active endpoint variables once the rest assignment is fixed. -/
noncomputable def remainingConstFactor {p ℓ : ℕ} [NeZero p]
    (F : (Fin ℓ × Fin ℓ) → ZMod p → ℂ) (e₀ : Fin ℓ × Fin ℓ)
    (r : EdgeRestAssignment p ℓ e₀) : ℂ :=
  ∏ e ∈ constantCliqueEdges e₀,
    F e (extendEdgeTuple e₀ r 0 0 e.1 - extendEdgeTuple e₀ r 0 0 e.2)

lemma prod_remainingCliqueEdges_split {ℓ : ℕ} (e₀ : Fin ℓ × Fin ℓ)
    (H : Fin ℓ × Fin ℓ → ℂ) :
    (∏ e ∈ remainingCliqueEdges e₀, H e) =
      (∏ e ∈ leftCliqueEdges e₀, H e) *
        (∏ e ∈ rightCliqueEdges e₀, H e) *
          (∏ e ∈ constantCliqueEdges e₀, H e) := by
  classical
  unfold leftCliqueEdges rightCliqueEdges constantCliqueEdges
  let s := remainingCliqueEdges e₀
  let P : Fin ℓ × Fin ℓ → Prop := fun e => edgeUsesVertex e e₀.1
  let Q : Fin ℓ × Fin ℓ → Prop := fun e => edgeUsesVertex e e₀.2
  have h1 := Finset.prod_filter_mul_prod_filter_not (s := s) (p := P) (f := H)
  have h2 := Finset.prod_filter_mul_prod_filter_not
    (s := s.filter (fun e => ¬ P e)) (p := Q) (f := H)
  dsimp [P, Q, s] at h1 h2 ⊢
  rw [← h1]
  rw [← h2]
  simp [Finset.filter_filter, mul_assoc]

lemma prod_leftCliqueEdges_actual_eq {p ℓ : ℕ} [NeZero p]
    {F : (Fin ℓ × Fin ℓ) → ZMod p → ℂ} {e₀ : Fin ℓ × Fin ℓ}
    (he₀ : e₀ ∈ cliqueEdgePairs ℓ) (r : EdgeRestAssignment p ℓ e₀)
    (u v : ZMod p) :
    (∏ e ∈ leftCliqueEdges e₀,
      F e (extendEdgeTuple e₀ r u v e.1 - extendEdgeTuple e₀ r u v e.2)) =
    remainingLeftTest F e₀ r u := by
  classical
  unfold remainingLeftTest
  refine Finset.prod_congr rfl ?_
  intro e he
  have he_rem : e ∈ remainingCliqueEdges e₀ := (Finset.mem_filter.mp he).1
  have hleft : edgeUsesVertex e e₀.1 := (Finset.mem_filter.mp he).2
  have hnot_right : ¬ edgeUsesVertex e e₀.2 := by
    intro hright
    exact edge_not_uses_both_endpoints_of_mem_remaining he₀ he_rem hleft hright
  have hnr := not_or.mp hnot_right
  rw [extendEdgeTuple_eq_of_same_left r u v 0 hnr.1,
    extendEdgeTuple_eq_of_same_left r u v 0 hnr.2]

lemma prod_rightCliqueEdges_actual_eq {p ℓ : ℕ} [NeZero p]
    {F : (Fin ℓ × Fin ℓ) → ZMod p → ℂ} {e₀ : Fin ℓ × Fin ℓ}
    (r : EdgeRestAssignment p ℓ e₀) (u v : ZMod p) :
    (∏ e ∈ rightCliqueEdges e₀,
      F e (extendEdgeTuple e₀ r u v e.1 - extendEdgeTuple e₀ r u v e.2)) =
    remainingRightTest F e₀ r v := by
  classical
  unfold remainingRightTest
  refine Finset.prod_congr rfl ?_
  intro e he
  have hnot_left : ¬ edgeUsesVertex e e₀.1 := (Finset.mem_filter.mp he).2.1
  have hnl := not_or.mp hnot_left
  rw [extendEdgeTuple_eq_of_same_right r u 0 v hnl.1,
    extendEdgeTuple_eq_of_same_right r u 0 v hnl.2]

lemma prod_constantCliqueEdges_actual_eq {p ℓ : ℕ} [NeZero p]
    {F : (Fin ℓ × Fin ℓ) → ZMod p → ℂ} {e₀ : Fin ℓ × Fin ℓ}
    (r : EdgeRestAssignment p ℓ e₀) (u v : ZMod p) :
    (∏ e ∈ constantCliqueEdges e₀,
      F e (extendEdgeTuple e₀ r u v e.1 - extendEdgeTuple e₀ r u v e.2)) =
    remainingConstFactor F e₀ r := by
  classical
  unfold remainingConstFactor
  refine Finset.prod_congr rfl ?_
  intro e he
  have hnot_left : ¬ edgeUsesVertex e e₀.1 := (Finset.mem_filter.mp he).2.1
  have hnot_right : ¬ edgeUsesVertex e e₀.2 := (Finset.mem_filter.mp he).2.2
  have hnl := not_or.mp hnot_left
  have hnr := not_or.mp hnot_right
  rw [extendEdgeTuple_eq_of_not_endpoints r u v 0 0 hnl.1 hnr.1,
    extendEdgeTuple_eq_of_not_endpoints r u v 0 0 hnl.2 hnr.2]

lemma remainingCliqueEdgeProduct_factorization {p ℓ : ℕ} [NeZero p]
    {F : (Fin ℓ × Fin ℓ) → ZMod p → ℂ} {e₀ : Fin ℓ × Fin ℓ}
    (he₀ : e₀ ∈ cliqueEdgePairs ℓ) (r : EdgeRestAssignment p ℓ e₀)
    (u v : ZMod p) :
    (∏ e ∈ cliqueEdgePairs ℓ \ {e₀},
      F e (extendEdgeTuple e₀ r u v e.1 - extendEdgeTuple e₀ r u v e.2)) =
        (remainingConstFactor F e₀ r * remainingLeftTest F e₀ r u) *
          remainingRightTest F e₀ r v := by
  classical
  change (∏ e ∈ remainingCliqueEdges e₀,
      F e (extendEdgeTuple e₀ r u v e.1 - extendEdgeTuple e₀ r u v e.2)) = _
  rw [prod_remainingCliqueEdges_split]
  rw [prod_leftCliqueEdges_actual_eq he₀ r u v,
    prod_rightCliqueEdges_actual_eq r u v,
    prod_constantCliqueEdges_actual_eq r u v]
  ring

/-- Reindex all clique tuples by a chosen edge's two endpoint values and the
assignment on the remaining vertices. -/
noncomputable def edgeTupleEquiv {p ℓ : ℕ} (e₀ : Fin ℓ × Fin ℓ)
    (hne : e₀.1 ≠ e₀.2) :
    (Fin ℓ → ZMod p) ≃ (EdgeRestAssignment p ℓ e₀ × ZMod p × ZMod p) where
  toFun x := (fun k => x k.1, x e₀.1, x e₀.2)
  invFun q := extendEdgeTuple e₀ q.1 q.2.1 q.2.2
  left_inv x := by
    funext k
    by_cases h1 : k = e₀.1
    · subst h1
      simp [extendEdgeTuple]
    · by_cases h2 : k = e₀.2
      · subst h2
        simp [extendEdgeTuple, hne.symm]
      · simp [extendEdgeTuple, h1, h2]
  right_inv q := by
    rcases q with ⟨r, u, v⟩
    ext k
    · exact extendEdgeTuple_rest e₀ r u v k.property.1 k.property.2
    · simp [extendEdgeTuple]
    · simp [extendEdgeTuple, hne.symm]

lemma sum_edgeTupleEquiv {p ℓ : ℕ} [NeZero p] {e₀ : Fin ℓ × Fin ℓ}
    (hne : e₀.1 ≠ e₀.2) (f : (Fin ℓ → ZMod p) → ℂ) :
    (∑ x : Fin ℓ → ZMod p, f x) =
      ∑ q : EdgeRestAssignment p ℓ e₀ × ZMod p × ZMod p,
        f (extendEdgeTuple e₀ q.1 q.2.1 q.2.2) := by
  simpa [edgeTupleEquiv] using ((edgeTupleEquiv (p := p) e₀ hne).symm.sum_comp f).symm

/-- The normalized tuple average, after reindexing at one chosen edge, is the
average over frozen remaining coordinates of a two-variable normalized
average. -/
lemma edgeTuple_normalized_sum_eq_avgFinite_avgZMod
    {p ℓ : ℕ} [NeZero p] {e₀ : Fin ℓ × Fin ℓ} (hne : e₀.1 ≠ e₀.2)
    (H : EdgeRestAssignment p ℓ e₀ → ZMod p → ZMod p → ℂ) :
    ((Fintype.card (Fin ℓ → ZMod p) : ℂ)⁻¹) *
      ∑ q : EdgeRestAssignment p ℓ e₀ × ZMod p × ZMod p,
        H q.1 q.2.1 q.2.2 =
    avgFinite (EdgeRestAssignment p ℓ e₀)
      (fun r => avgZMod fun u => avgZMod fun v => H r u v) := by
  classical
  have hcard_nat :
      Fintype.card (Fin ℓ → ZMod p) =
        Fintype.card (EdgeRestAssignment p ℓ e₀) * p * p := by
    calc
      Fintype.card (Fin ℓ → ZMod p) =
          Fintype.card (EdgeRestAssignment p ℓ e₀ × ZMod p × ZMod p) :=
            Fintype.card_congr (edgeTupleEquiv (p := p) e₀ hne)
      _ = Fintype.card (EdgeRestAssignment p ℓ e₀) * p * p := by
            simp [Fintype.card_prod, ZMod.card, mul_assoc]
  have hcard_complex :
      (Fintype.card (Fin ℓ → ZMod p) : ℂ) =
        (Fintype.card (EdgeRestAssignment p ℓ e₀) : ℂ) * (p : ℂ) * (p : ℂ) := by
    exact_mod_cast hcard_nat
  unfold avgFinite avgZMod
  rw [hcard_complex]
  simp only [Fintype.sum_prod_type]
  simp_rw [← Finset.mul_sum]
  ring

/-- Product weight for the finite Cayley `K_ℓ` density with an arbitrary complex
kernel `f`.  The compact-Cayley counting convergence lemma should produce
positivity of the density built from this generic kernel, before specializing
`f` to an indicator. -/
noncomputable def finiteCliqueKernelWeight {p ℓ : ℕ}
    (f : ZMod p → ℂ) (x : Fin ℓ → ZMod p) : ℂ :=
  ∏ e ∈ cliqueEdgePairs ℓ, f (x e.1 - x e.2)

/-- Normalized finite `K_ℓ` Cayley density for an arbitrary kernel on `ZMod p`. -/
noncomputable def finiteCliqueKernelDensity {p ℓ : ℕ} [NeZero p]
    (f : ZMod p → ℂ) : ℂ :=
  ((Fintype.card (Fin ℓ → ZMod p) : ℂ)⁻¹) *
    ∑ x : Fin ℓ → ZMod p, finiteCliqueKernelWeight f x

/-- Edge-indexed version of the finite Cayley `K_ℓ` product weight.  This is
the natural bookkeeping object for the telescoping proof of counting
convergence, where one edge kernel is replaced at a time. -/
noncomputable def finiteCliqueKernelWeightEdge {p ℓ : ℕ}
    (F : (Fin ℓ × Fin ℓ) → ZMod p → ℂ) (x : Fin ℓ → ZMod p) : ℂ :=
  ∏ e ∈ cliqueEdgePairs ℓ, F e (x e.1 - x e.2)

/-- Edge-indexed normalized finite `K_ℓ` Cayley density. -/
noncomputable def finiteCliqueKernelDensityEdge {p ℓ : ℕ} [NeZero p]
    (F : (Fin ℓ × Fin ℓ) → ZMod p → ℂ) : ℂ :=
  ((Fintype.card (Fin ℓ → ZMod p) : ℂ)⁻¹) *
    ∑ x : Fin ℓ → ZMod p, finiteCliqueKernelWeightEdge F x

lemma finiteCliqueKernelWeightEdge_const
    {p ℓ : ℕ} (f : ZMod p → ℂ) (x : Fin ℓ → ZMod p) :
    finiteCliqueKernelWeightEdge (fun _ => f) x =
      finiteCliqueKernelWeight f x := by
  rfl

lemma finiteCliqueKernelDensityEdge_const
    {p ℓ : ℕ} [NeZero p] (f : ZMod p → ℂ) :
    finiteCliqueKernelDensityEdge (ℓ := ℓ) (fun _ => f) =
      finiteCliqueKernelDensity (ℓ := ℓ) f := by
  rfl

/-- Every edge kernel is uniformly bounded by `1`. -/
def EdgeKernelBoundedByOne {p ℓ : ℕ}
    (F : (Fin ℓ × Fin ℓ) → ZMod p → ℂ) : Prop :=
  ∀ e z, ‖F e z‖ ≤ 1

/-- Replace one edge kernel in an edge-indexed kernel family. -/
noncomputable def replaceEdgeKernel {p ℓ : ℕ}
    (F : (Fin ℓ × Fin ℓ) → ZMod p → ℂ) (e₀ : Fin ℓ × Fin ℓ)
    (g : ZMod p → ℂ) : (Fin ℓ × Fin ℓ) → ZMod p → ℂ :=
  fun e z => if e = e₀ then g z else F e z

lemma EdgeKernelBoundedByOne.const {p ℓ : ℕ} {f : ZMod p → ℂ}
    (hf : ∀ z, ‖f z‖ ≤ 1) :
    EdgeKernelBoundedByOne (ℓ := ℓ) (fun _ => f) := by
  intro _ z
  exact hf z

lemma EdgeKernelBoundedByOne.replace {p ℓ : ℕ}
    {F : (Fin ℓ × Fin ℓ) → ZMod p → ℂ} {e₀ : Fin ℓ × Fin ℓ}
    {g : ZMod p → ℂ} (hF : EdgeKernelBoundedByOne F)
    (hg : ∀ z, ‖g z‖ ≤ 1) :
    EdgeKernelBoundedByOne (replaceEdgeKernel F e₀ g) := by
  intro e z
  by_cases h : e = e₀
  · simp [replaceEdgeKernel, h, hg z]
  · simp [replaceEdgeKernel, h, hF e z]

lemma norm_remainingLeftTest_le_one {p ℓ : ℕ} [NeZero p]
    {F : (Fin ℓ × Fin ℓ) → ZMod p → ℂ} (hF : EdgeKernelBoundedByOne F)
    (e₀ : Fin ℓ × Fin ℓ) (r : EdgeRestAssignment p ℓ e₀) (u : ZMod p) :
    ‖remainingLeftTest F e₀ r u‖ ≤ 1 := by
  classical
  unfold remainingLeftTest
  rw [norm_prod]
  exact Finset.prod_le_one
    (fun e _he =>
      norm_nonneg
        (F e (extendEdgeTuple e₀ r u 0 e.1 - extendEdgeTuple e₀ r u 0 e.2)))
    (fun e _he =>
      hF e (extendEdgeTuple e₀ r u 0 e.1 - extendEdgeTuple e₀ r u 0 e.2))

lemma norm_remainingRightTest_le_one {p ℓ : ℕ} [NeZero p]
    {F : (Fin ℓ × Fin ℓ) → ZMod p → ℂ} (hF : EdgeKernelBoundedByOne F)
    (e₀ : Fin ℓ × Fin ℓ) (r : EdgeRestAssignment p ℓ e₀) (v : ZMod p) :
    ‖remainingRightTest F e₀ r v‖ ≤ 1 := by
  classical
  unfold remainingRightTest
  rw [norm_prod]
  exact Finset.prod_le_one
    (fun e _he =>
      norm_nonneg
        (F e (extendEdgeTuple e₀ r 0 v e.1 - extendEdgeTuple e₀ r 0 v e.2)))
    (fun e _he =>
      hF e (extendEdgeTuple e₀ r 0 v e.1 - extendEdgeTuple e₀ r 0 v e.2))

lemma norm_remainingConstFactor_le_one {p ℓ : ℕ} [NeZero p]
    {F : (Fin ℓ × Fin ℓ) → ZMod p → ℂ} (hF : EdgeKernelBoundedByOne F)
    (e₀ : Fin ℓ × Fin ℓ) (r : EdgeRestAssignment p ℓ e₀) :
    ‖remainingConstFactor F e₀ r‖ ≤ 1 := by
  classical
  unfold remainingConstFactor
  rw [norm_prod]
  exact Finset.prod_le_one
    (fun e _he =>
      norm_nonneg
        (F e (extendEdgeTuple e₀ r 0 0 e.1 - extendEdgeTuple e₀ r 0 0 e.2)))
    (fun e _he =>
      hF e (extendEdgeTuple e₀ r 0 0 e.1 - extendEdgeTuple e₀ r 0 0 e.2))

lemma norm_remainingConstFactor_mul_leftTest_le_one {p ℓ : ℕ} [NeZero p]
    {F : (Fin ℓ × Fin ℓ) → ZMod p → ℂ} (hF : EdgeKernelBoundedByOne F)
    (e₀ : Fin ℓ × Fin ℓ) (r : EdgeRestAssignment p ℓ e₀) (u : ZMod p) :
    ‖remainingConstFactor F e₀ r * remainingLeftTest F e₀ r u‖ ≤ 1 := by
  rw [norm_mul]
  have hc := norm_remainingConstFactor_le_one hF e₀ r
  have hl := norm_remainingLeftTest_le_one hF e₀ r u
  have hcn : 0 ≤ ‖remainingConstFactor F e₀ r‖ := norm_nonneg _
  have hln : 0 ≤ ‖remainingLeftTest F e₀ r u‖ := norm_nonneg _
  nlinarith

lemma norm_finiteCliqueKernelWeightEdge_le_one
    {p ℓ : ℕ} {F : (Fin ℓ × Fin ℓ) → ZMod p → ℂ}
    (hF : EdgeKernelBoundedByOne F) (x : Fin ℓ → ZMod p) :
    ‖finiteCliqueKernelWeightEdge F x‖ ≤ 1 := by
  classical
  rw [finiteCliqueKernelWeightEdge, norm_prod]
  exact Finset.prod_le_one
    (fun e _he => norm_nonneg (F e (x e.1 - x e.2)))
    (fun e _he => hF e (x e.1 - x e.2))

lemma norm_finiteCliqueKernelWeight_le_one
    {p ℓ : ℕ} {f : ZMod p → ℂ} (hf : ∀ z, ‖f z‖ ≤ 1)
    (x : Fin ℓ → ZMod p) :
    ‖finiteCliqueKernelWeight f x‖ ≤ 1 := by
  simpa [finiteCliqueKernelWeightEdge_const] using
    norm_finiteCliqueKernelWeightEdge_le_one
      (F := fun _ : Fin ℓ × Fin ℓ => f)
      (EdgeKernelBoundedByOne.const (ℓ := ℓ) hf) x

lemma finiteCliqueKernelWeightEdge_eq_single_mul
    {p ℓ : ℕ} {F : (Fin ℓ × Fin ℓ) → ZMod p → ℂ}
    {e₀ : Fin ℓ × Fin ℓ} (he₀ : e₀ ∈ cliqueEdgePairs ℓ)
    (x : Fin ℓ → ZMod p) :
    finiteCliqueKernelWeightEdge F x =
      F e₀ (x e₀.1 - x e₀.2) *
        ∏ e ∈ cliqueEdgePairs ℓ \ {e₀}, F e (x e.1 - x e.2) := by
  classical
  unfold finiteCliqueKernelWeightEdge
  exact Finset.prod_eq_mul_prod_sdiff_singleton_of_mem he₀
    (fun e => F e (x e.1 - x e.2))

lemma finiteCliqueKernelWeightEdge_replace_eq_single_mul
    {p ℓ : ℕ} {F : (Fin ℓ × Fin ℓ) → ZMod p → ℂ}
    {e₀ : Fin ℓ × Fin ℓ} (he₀ : e₀ ∈ cliqueEdgePairs ℓ)
    (g : ZMod p → ℂ) (x : Fin ℓ → ZMod p) :
    finiteCliqueKernelWeightEdge (replaceEdgeKernel F e₀ g) x =
      g (x e₀.1 - x e₀.2) *
        ∏ e ∈ cliqueEdgePairs ℓ \ {e₀}, F e (x e.1 - x e.2) := by
  classical
  rw [finiteCliqueKernelWeightEdge_eq_single_mul he₀]
  congr 1
  · simp [replaceEdgeKernel]
  · refine Finset.prod_congr rfl ?_
    intro e he
    have hne : e ≠ e₀ := by
      intro h
      exact (Finset.mem_sdiff.mp he).2 (by simp [h])
    simp [replaceEdgeKernel, hne]

lemma norm_remainingCliqueEdgeProduct_le_one
    {p ℓ : ℕ} {F : (Fin ℓ × Fin ℓ) → ZMod p → ℂ}
    (hF : EdgeKernelBoundedByOne F) (e₀ : Fin ℓ × Fin ℓ)
    (x : Fin ℓ → ZMod p) :
    ‖∏ e ∈ cliqueEdgePairs ℓ \ {e₀}, F e (x e.1 - x e.2)‖ ≤ 1 := by
  classical
  rw [norm_prod]
  exact Finset.prod_le_one
    (fun e _he => norm_nonneg (F e (x e.1 - x e.2)))
    (fun e _he => hF e (x e.1 - x e.2))

/-- Pointwise single-edge replacement identity, used by the telescoping proof of
finite counting convergence. -/
lemma finiteCliqueKernelWeightEdge_replace_sub
    {p ℓ : ℕ} {F : (Fin ℓ × Fin ℓ) → ZMod p → ℂ}
    {e₀ : Fin ℓ × Fin ℓ} (he₀ : e₀ ∈ cliqueEdgePairs ℓ)
    (g : ZMod p → ℂ) (x : Fin ℓ → ZMod p) :
    finiteCliqueKernelWeightEdge (replaceEdgeKernel F e₀ g) x -
        finiteCliqueKernelWeightEdge F x =
      (g (x e₀.1 - x e₀.2) - F e₀ (x e₀.1 - x e₀.2)) *
        ∏ e ∈ cliqueEdgePairs ℓ \ {e₀}, F e (x e.1 - x e.2) := by
  rw [finiteCliqueKernelWeightEdge_replace_eq_single_mul he₀,
    finiteCliqueKernelWeightEdge_eq_single_mul he₀]
  ring

/-- Density-level form of the single-edge replacement identity. -/
lemma finiteCliqueKernelDensityEdge_replace_sub
    {p ℓ : ℕ} [NeZero p] {F : (Fin ℓ × Fin ℓ) → ZMod p → ℂ}
    {e₀ : Fin ℓ × Fin ℓ} (he₀ : e₀ ∈ cliqueEdgePairs ℓ)
    (g : ZMod p → ℂ) :
    finiteCliqueKernelDensityEdge (replaceEdgeKernel F e₀ g) -
        finiteCliqueKernelDensityEdge F =
      ((Fintype.card (Fin ℓ → ZMod p) : ℂ)⁻¹) *
        ∑ x : Fin ℓ → ZMod p,
          (g (x e₀.1 - x e₀.2) - F e₀ (x e₀.1 - x e₀.2)) *
            ∏ e ∈ cliqueEdgePairs ℓ \ {e₀}, F e (x e.1 - x e.2) := by
  unfold finiteCliqueKernelDensityEdge
  rw [← mul_sub, ← Finset.sum_sub_distrib]
  congr 1
  refine Finset.sum_congr rfl ?_
  intro x _hx
  exact finiteCliqueKernelWeightEdge_replace_sub he₀ g x

/-- Reindexed density-level single-edge replacement identity.  The full tuple
sum is rewritten as a sum over frozen non-endpoint coordinates and the two
endpoint variables. -/
lemma finiteCliqueKernelDensityEdge_replace_sub_reindex
    {p ℓ : ℕ} [NeZero p] {F : (Fin ℓ × Fin ℓ) → ZMod p → ℂ}
    {e₀ : Fin ℓ × Fin ℓ} (he₀ : e₀ ∈ cliqueEdgePairs ℓ)
    (g : ZMod p → ℂ) :
    finiteCliqueKernelDensityEdge (replaceEdgeKernel F e₀ g) -
        finiteCliqueKernelDensityEdge F =
      ((Fintype.card (Fin ℓ → ZMod p) : ℂ)⁻¹) *
        ∑ q : EdgeRestAssignment p ℓ e₀ × ZMod p × ZMod p,
          (g (q.2.1 - q.2.2) - F e₀ (q.2.1 - q.2.2)) *
            ∏ e ∈ cliqueEdgePairs ℓ \ {e₀},
              F e (extendEdgeTuple e₀ q.1 q.2.1 q.2.2 e.1 -
                extendEdgeTuple e₀ q.1 q.2.1 q.2.2 e.2) := by
  rw [finiteCliqueKernelDensityEdge_replace_sub he₀]
  congr 1
  rw [sum_edgeTupleEquiv (cliqueEdgePairs_left_ne_right he₀)]
  refine Finset.sum_congr rfl ?_
  intro q _hq
  rw [extendEdgeTuple_edge_diff_of_mem_cliqueEdgePairs he₀]

/-- If the remaining-edge product factors into a left test and a right test
after the chosen edge has been isolated, then the single-edge replacement
difference is exactly an average of Cayley cut functionals. -/
lemma finiteCliqueKernelDensityEdge_replace_sub_eq_avgFinite_cayleyCutFunctional_of_factorization
    {p ℓ : ℕ} [NeZero p] {F : (Fin ℓ × Fin ℓ) → ZMod p → ℂ}
    {e₀ : Fin ℓ × Fin ℓ} (he₀ : e₀ ∈ cliqueEdgePairs ℓ)
    (g : ZMod p → ℂ)
    (φ ψ : EdgeRestAssignment p ℓ e₀ → ZMod p → ℂ)
    (hprod : ∀ r u v,
      (∏ e ∈ cliqueEdgePairs ℓ \ {e₀},
        F e (extendEdgeTuple e₀ r u v e.1 - extendEdgeTuple e₀ r u v e.2)) =
          φ r u * ψ r v) :
    finiteCliqueKernelDensityEdge (replaceEdgeKernel F e₀ g) -
        finiteCliqueKernelDensityEdge F =
      avgFinite (EdgeRestAssignment p ℓ e₀)
        (fun r => cayleyCutFunctional
          (fun z => g z - F e₀ z) (φ r) (ψ r)) := by
  rw [finiteCliqueKernelDensityEdge_replace_sub_reindex he₀]
  rw [edgeTuple_normalized_sum_eq_avgFinite_avgZMod
    (p := p) (ℓ := ℓ) (e₀ := e₀) (cliqueEdgePairs_left_ne_right he₀)
    (fun r u v =>
      (g (u - v) - F e₀ (u - v)) *
        ∏ e ∈ cliqueEdgePairs ℓ \ {e₀},
          F e (extendEdgeTuple e₀ r u v e.1 - extendEdgeTuple e₀ r u v e.2))]
  unfold cayleyCutFunctional
  congr 1
  funext r
  congr 1
  funext u
  congr 1
  funext v
  rw [hprod]
  ring

/-- One-edge replacement estimate, assuming the tuple-sum difference has already
been rewritten as an average of Cayley cut functionals over the frozen remaining
coordinates.  The remaining work for Lemma 2.6 is to supply this representation
for the concrete edge being replaced. -/
lemma norm_finiteCliqueKernelDensityEdge_replace_sub_le_of_cut_representation
    {ι : Type*} [Fintype ι] [Nonempty ι]
    {p ℓ : ℕ} [NeZero p]
    {F : (Fin ℓ × Fin ℓ) → ZMod p → ℂ} {e₀ : Fin ℓ × Fin ℓ}
    {g : ZMod p → ℂ} {M : ℝ}
    (φ ψ : ι → ZMod p → ℂ)
    (hrepr :
      finiteCliqueKernelDensityEdge (replaceEdgeKernel F e₀ g) -
          finiteCliqueKernelDensityEdge F =
        avgFinite ι
          (fun t => cayleyCutFunctional
            (fun z => g z - F e₀ z) (φ t) (ψ t)))
    (hcut : CayleyCutBound (fun z => g z - F e₀ z) M)
    (hφ : ∀ t x, ‖φ t x‖ ≤ 1)
    (hψ : ∀ t y, ‖ψ t y‖ ≤ 1) :
    ‖finiteCliqueKernelDensityEdge (replaceEdgeKernel F e₀ g) -
        finiteCliqueKernelDensityEdge F‖ ≤ M := by
  rw [hrepr]
  exact norm_avgFinite_cayleyCutFunctional_le hcut φ ψ hφ hψ

/-- One-edge replacement estimate from a concrete factorization of the
remaining-edge product into two bounded test functions. -/
lemma norm_finiteCliqueKernelDensityEdge_replace_sub_le_of_factorization
    {p ℓ : ℕ} [NeZero p]
    {F : (Fin ℓ × Fin ℓ) → ZMod p → ℂ} {e₀ : Fin ℓ × Fin ℓ}
    {g : ZMod p → ℂ} {M : ℝ}
    (he₀ : e₀ ∈ cliqueEdgePairs ℓ)
    (φ ψ : EdgeRestAssignment p ℓ e₀ → ZMod p → ℂ)
    (hprod : ∀ r u v,
      (∏ e ∈ cliqueEdgePairs ℓ \ {e₀},
        F e (extendEdgeTuple e₀ r u v e.1 - extendEdgeTuple e₀ r u v e.2)) =
          φ r u * ψ r v)
    (hcut : CayleyCutBound (fun z => g z - F e₀ z) M)
    (hφ : ∀ t x, ‖φ t x‖ ≤ 1)
    (hψ : ∀ t y, ‖ψ t y‖ ≤ 1) :
    ‖finiteCliqueKernelDensityEdge (replaceEdgeKernel F e₀ g) -
        finiteCliqueKernelDensityEdge F‖ ≤ M := by
  exact norm_finiteCliqueKernelDensityEdge_replace_sub_le_of_cut_representation φ ψ
    (finiteCliqueKernelDensityEdge_replace_sub_eq_avgFinite_cayleyCutFunctional_of_factorization
      he₀ g φ ψ hprod)
    hcut hφ hψ

/-- Concrete one-edge replacement estimate: if all unreplaced edge kernels are
bounded by `1`, then replacing one edge is controlled by the Cayley cut bound of
the replacement difference. -/
lemma norm_finiteCliqueKernelDensityEdge_replace_sub_le_of_cutBound
    {p ℓ : ℕ} [NeZero p]
    {F : (Fin ℓ × Fin ℓ) → ZMod p → ℂ} {e₀ : Fin ℓ × Fin ℓ}
    {g : ZMod p → ℂ} {M : ℝ}
    (he₀ : e₀ ∈ cliqueEdgePairs ℓ)
    (hF : EdgeKernelBoundedByOne F)
    (hcut : CayleyCutBound (fun z => g z - F e₀ z) M) :
    ‖finiteCliqueKernelDensityEdge (replaceEdgeKernel F e₀ g) -
        finiteCliqueKernelDensityEdge F‖ ≤ M := by
  exact norm_finiteCliqueKernelDensityEdge_replace_sub_le_of_factorization he₀
    (fun r u => remainingConstFactor F e₀ r * remainingLeftTest F e₀ r u)
    (fun r v => remainingRightTest F e₀ r v)
    (by intro r u v; exact remainingCliqueEdgeProduct_factorization he₀ r u v)
    hcut
    (by intro r u; exact norm_remainingConstFactor_mul_leftTest_le_one hF e₀ r u)
    (by intro r v; exact norm_remainingRightTest_le_one hF e₀ r v)

/-- Patch an edge-indexed kernel family by replacing the kernels on `S` with
those from another family. -/
noncomputable def patchEdgeKernel {p ℓ : ℕ}
    (F G : (Fin ℓ × Fin ℓ) → ZMod p → ℂ) (S : Finset (Fin ℓ × Fin ℓ)) :
    (Fin ℓ × Fin ℓ) → ZMod p → ℂ :=
  fun e z => if e ∈ S then G e z else F e z

lemma patchEdgeKernel_insert_eq_replace {p ℓ : ℕ}
    (F G : (Fin ℓ × Fin ℓ) → ZMod p → ℂ) (S : Finset (Fin ℓ × Fin ℓ))
    (e₀ : Fin ℓ × Fin ℓ) :
    patchEdgeKernel F G (insert e₀ S) =
      replaceEdgeKernel (patchEdgeKernel F G S) e₀ (G e₀) := by
  funext e z
  by_cases h : e = e₀
  · subst h
    simp [patchEdgeKernel, replaceEdgeKernel]
  · simp [patchEdgeKernel, replaceEdgeKernel, h]

lemma EdgeKernelBoundedByOne.patch {p ℓ : ℕ}
    {F G : (Fin ℓ × Fin ℓ) → ZMod p → ℂ} {S : Finset (Fin ℓ × Fin ℓ)}
    (hF : EdgeKernelBoundedByOne F) (hG : EdgeKernelBoundedByOne G) :
    EdgeKernelBoundedByOne (patchEdgeKernel F G S) := by
  intro e z
  by_cases h : e ∈ S
  · simp [patchEdgeKernel, h, hG e z]
  · simp [patchEdgeKernel, h, hF e z]

lemma finiteCliqueKernelDensityEdge_patch_empty {p ℓ : ℕ} [NeZero p]
    (F G : (Fin ℓ × Fin ℓ) → ZMod p → ℂ) :
    finiteCliqueKernelDensityEdge (patchEdgeKernel F G (∅ : Finset (Fin ℓ × Fin ℓ))) =
      finiteCliqueKernelDensityEdge F := by
  unfold finiteCliqueKernelDensityEdge finiteCliqueKernelWeightEdge
  simp [patchEdgeKernel]

lemma finiteCliqueKernelDensityEdge_patch_all {p ℓ : ℕ} [NeZero p]
    (F G : (Fin ℓ × Fin ℓ) → ZMod p → ℂ) :
    finiteCliqueKernelDensityEdge (patchEdgeKernel F G (cliqueEdgePairs ℓ)) =
      finiteCliqueKernelDensityEdge G := by
  classical
  unfold finiteCliqueKernelDensityEdge finiteCliqueKernelWeightEdge
  congr 1
  refine Finset.sum_congr rfl ?_
  intro x _hx
  refine Finset.prod_congr rfl ?_
  intro e he
  simp [patchEdgeKernel, he]

lemma norm_finiteCliqueKernelDensityEdge_patch_insert_sub_le {p ℓ : ℕ} [NeZero p]
    {F G : (Fin ℓ × Fin ℓ) → ZMod p → ℂ} {S : Finset (Fin ℓ × Fin ℓ)}
    {e₀ : Fin ℓ × Fin ℓ} {M : ℝ}
    (he₀ : e₀ ∈ cliqueEdgePairs ℓ) (heS : e₀ ∉ S)
    (hF : EdgeKernelBoundedByOne F) (hG : EdgeKernelBoundedByOne G)
    (hcut : CayleyCutBound (fun z => G e₀ z - F e₀ z) M) :
    ‖finiteCliqueKernelDensityEdge (patchEdgeKernel F G (insert e₀ S)) -
        finiteCliqueKernelDensityEdge (patchEdgeKernel F G S)‖ ≤ M := by
  rw [patchEdgeKernel_insert_eq_replace]
  exact norm_finiteCliqueKernelDensityEdge_replace_sub_le_of_cutBound he₀
    (EdgeKernelBoundedByOne.patch hF hG)
    (by simpa [patchEdgeKernel, heS] using hcut)

/-- Finite telescoping estimate for compact-Cayley Lemma 2.6.  Replacing all
edge kernels changes the finite `K_ℓ` density by at most the number of clique
edges times a uniform Cayley cut bound. -/
lemma norm_finiteCliqueKernelDensityEdge_patch_sub_le_card_mul {p ℓ : ℕ} [NeZero p]
    {F G : (Fin ℓ × Fin ℓ) → ZMod p → ℂ} {M : ℝ}
    (hF : EdgeKernelBoundedByOne F) (hG : EdgeKernelBoundedByOne G)
    (hcut : ∀ e ∈ cliqueEdgePairs ℓ, CayleyCutBound (fun z => G e z - F e z) M)
    (S : Finset (Fin ℓ × Fin ℓ)) (hS : S ⊆ cliqueEdgePairs ℓ) :
    ‖finiteCliqueKernelDensityEdge (patchEdgeKernel F G S) -
        finiteCliqueKernelDensityEdge F‖ ≤ (S.card : ℝ) * M := by
  classical
  refine Finset.induction_on S ?base ?step hS
  · intro _hS
    rw [finiteCliqueKernelDensityEdge_patch_empty]
    simp
  · intro e S heS ih hInsert
    have heClique : e ∈ cliqueEdgePairs ℓ := hInsert (by simp)
    have hSsub : S ⊆ cliqueEdgePairs ℓ := by
      intro x hx
      exact hInsert (by simp [hx])
    have hstep := norm_finiteCliqueKernelDensityEdge_patch_insert_sub_le
      (F := F) (G := G) (S := S) (e₀ := e) heClique heS hF hG (hcut e heClique)
    have hih := ih hSsub
    have hdecomp :
        finiteCliqueKernelDensityEdge (patchEdgeKernel F G (insert e S)) -
            finiteCliqueKernelDensityEdge F =
          (finiteCliqueKernelDensityEdge (patchEdgeKernel F G (insert e S)) -
            finiteCliqueKernelDensityEdge (patchEdgeKernel F G S)) +
          (finiteCliqueKernelDensityEdge (patchEdgeKernel F G S) -
            finiteCliqueKernelDensityEdge F) := by
      ring
    rw [hdecomp]
    calc
      ‖(finiteCliqueKernelDensityEdge (patchEdgeKernel F G (insert e S)) -
            finiteCliqueKernelDensityEdge (patchEdgeKernel F G S)) +
          (finiteCliqueKernelDensityEdge (patchEdgeKernel F G S) -
            finiteCliqueKernelDensityEdge F)‖
          ≤ ‖finiteCliqueKernelDensityEdge (patchEdgeKernel F G (insert e S)) -
            finiteCliqueKernelDensityEdge (patchEdgeKernel F G S)‖ +
            ‖finiteCliqueKernelDensityEdge (patchEdgeKernel F G S) -
              finiteCliqueKernelDensityEdge F‖ := norm_add_le _ _
      _ ≤ M + (S.card : ℝ) * M := add_le_add hstep hih
      _ = ((insert e S).card : ℝ) * M := by
        rw [Finset.card_insert_of_notMem heS]
        norm_num
        ring

lemma norm_finiteCliqueKernelDensityEdge_sub_le_card_mul_cutBound {p ℓ : ℕ} [NeZero p]
    {F G : (Fin ℓ × Fin ℓ) → ZMod p → ℂ} {M : ℝ}
    (hF : EdgeKernelBoundedByOne F) (hG : EdgeKernelBoundedByOne G)
    (hcut : ∀ e ∈ cliqueEdgePairs ℓ, CayleyCutBound (fun z => G e z - F e z) M) :
    ‖finiteCliqueKernelDensityEdge G - finiteCliqueKernelDensityEdge F‖ ≤
      ((cliqueEdgePairs ℓ).card : ℝ) * M := by
  have h := norm_finiteCliqueKernelDensityEdge_patch_sub_le_card_mul
    (F := F) (G := G) (M := M) hF hG hcut (cliqueEdgePairs ℓ) (by intro x hx; exact hx)
  rwa [finiteCliqueKernelDensityEdge_patch_all] at h

lemma norm_finiteCliqueKernelDensityEdge_sub_le_card_mul_spectralBound
    {p ℓ : ℕ} [NeZero p]
    {F G : (Fin ℓ × Fin ℓ) → ZMod p → ℂ} {M : ℝ}
    (hMnonneg : 0 ≤ M)
    (hF : EdgeKernelBoundedByOne F) (hG : EdgeKernelBoundedByOne G)
    (hspec : ∀ e ∈ cliqueEdgePairs ℓ,
      SpectralBound (fun z => G e z - F e z) M) :
    ‖finiteCliqueKernelDensityEdge G - finiteCliqueKernelDensityEdge F‖ ≤
      ((cliqueEdgePairs ℓ).card : ℝ) * M := by
  exact norm_finiteCliqueKernelDensityEdge_sub_le_card_mul_cutBound hF hG
    (fun e he => cayleyCutBound_of_spectralBound
      (a := fun z => G e z - F e z) hMnonneg (hspec e he))

lemma norm_finiteCliqueKernelDensity_sub_le_card_mul_cutBound
    {p ℓ : ℕ} [NeZero p] {f g : ZMod p → ℂ} {M : ℝ}
    (hf : ∀ z, ‖f z‖ ≤ 1) (hg : ∀ z, ‖g z‖ ≤ 1)
    (hcut : CayleyCutBound (fun z => g z - f z) M) :
    ‖finiteCliqueKernelDensity (ℓ := ℓ) g - finiteCliqueKernelDensity (ℓ := ℓ) f‖ ≤
      ((cliqueEdgePairs ℓ).card : ℝ) * M := by
  simpa [finiteCliqueKernelDensityEdge_const] using
    norm_finiteCliqueKernelDensityEdge_sub_le_card_mul_cutBound
      (F := fun _ : Fin ℓ × Fin ℓ => f) (G := fun _ : Fin ℓ × Fin ℓ => g)
      (M := M)
      (EdgeKernelBoundedByOne.const (ℓ := ℓ) hf)
      (EdgeKernelBoundedByOne.const (ℓ := ℓ) hg)
      (fun _e _he => hcut)

lemma norm_finiteCliqueKernelDensity_sub_le_card_mul_spectralBound
    {p ℓ : ℕ} [NeZero p] {f g : ZMod p → ℂ} {M : ℝ}
    (hMnonneg : 0 ≤ M)
    (hf : ∀ z, ‖f z‖ ≤ 1) (hg : ∀ z, ‖g z‖ ≤ 1)
    (hspec : SpectralBound (fun z => g z - f z) M) :
    ‖finiteCliqueKernelDensity (ℓ := ℓ) g - finiteCliqueKernelDensity (ℓ := ℓ) f‖ ≤
      ((cliqueEdgePairs ℓ).card : ℝ) * M := by
  exact norm_finiteCliqueKernelDensity_sub_le_card_mul_cutBound
    (ℓ := ℓ) hf hg
    (cayleyCutBound_of_spectralBound (a := fun z => g z - f z) hMnonneg hspec)

lemma indicatorC_norm_le_one {p : ℕ} (T : Finset (ZMod p)) (z : ZMod p) :
    ‖indicatorC T z‖ ≤ 1 := by
  classical
  by_cases h : z ∈ T
  · simp [indicatorC, h]
  · simp [indicatorC, h]

lemma finiteCliqueKernelWeight_indicatorC
    {p ℓ : ℕ} (T : Finset (ZMod p)) (x : Fin ℓ → ZMod p) :
    finiteCliqueKernelWeight (indicatorC T) x = cliqueKernelWeight T x := by
  rfl

lemma finiteCliqueKernelDensity_indicatorC
    {p ℓ : ℕ} [NeZero p] (T : Finset (ZMod p)) :
    finiteCliqueKernelDensity (ℓ := ℓ) (indicatorC T) =
      cliqueKernelDensity (ℓ := ℓ) T := by
  rfl

lemma finiteCliqueKernelDensity_indicatorC_eq_zero_of_no_clique
    {p ℓ : ℕ} [NeZero p] {T : Finset (ZMod p)}
    (hTsym : SymmetricFinset T) (hT0 : (0 : ZMod p) ∉ T)
    (hNoClique : ¬ ∃ C : Finset (ZMod p), C.card = ℓ ∧ CliqueInCayley T C) :
    finiteCliqueKernelDensity (ℓ := ℓ) (indicatorC T) = 0 := by
  rw [finiteCliqueKernelDensity_indicatorC]
  exact cliqueKernelDensity_eq_zero_of_no_clique hTsym hT0 hNoClique

lemma CayleyCounterSeq.finiteCliqueKernelDensity_indicatorC_eq_zero
    {ℓ : ℕ} {η : ℝ} (S : CayleyCounterSeq ℓ η) (n : ℕ) :
    (letI : NeZero (S.p n) := ⟨(S.prime n).ne_zero⟩;
      finiteCliqueKernelDensity (ℓ := ℓ) (indicatorC (S.T n))) = 0 := by
  letI : NeZero (S.p n) := ⟨(S.prime n).ne_zero⟩
  exact finiteCliqueKernelDensity_indicatorC_eq_zero_of_no_clique
    (S.T_sym n) (S.T_zero n) (S.no_clique n)

lemma CayleyCounterSeq.finiteCliqueKernelDensity_indicatorC_tendsto_zero
    {ℓ : ℕ} {η : ℝ} (S : CayleyCounterSeq ℓ η) :
    Tendsto
      (fun n =>
        letI : NeZero (S.p n) := ⟨(S.prime n).ne_zero⟩;
        finiteCliqueKernelDensity (ℓ := ℓ) (indicatorC (S.T n)))
      atTop (𝓝 0) := by
  have hzero : ∀ n,
      (letI : NeZero (S.p n) := ⟨(S.prime n).ne_zero⟩;
        finiteCliqueKernelDensity (ℓ := ℓ) (indicatorC (S.T n))) = 0 :=
    S.finiteCliqueKernelDensity_indicatorC_eq_zero
  have heq :
      (fun n =>
        letI : NeZero (S.p n) := ⟨(S.prime n).ne_zero⟩;
        finiteCliqueKernelDensity (ℓ := ℓ) (indicatorC (S.T n))) = fun _ => (0 : ℂ) := by
    funext n
    exact hzero n
  rw [heq]
  exact tendsto_const_nhds

/-- Indicator-specialized finite generic density is positive exactly when the
finite Cayley graph contains a clique. -/
lemma finiteCliqueKernelDensity_indicatorC_re_pos_iff_exists_clique
    {p ℓ : ℕ} [NeZero p] {T : Finset (ZMod p)}
    (hTsym : SymmetricFinset T) (hT0 : (0 : ZMod p) ∉ T) :
    0 < (finiteCliqueKernelDensity (ℓ := ℓ) (indicatorC T)).re ↔
      ∃ C : Finset (ZMod p), C.card = ℓ ∧ CliqueInCayley T C := by
  rw [finiteCliqueKernelDensity_indicatorC]
  exact cliqueKernelDensity_re_pos_iff_exists_clique hTsym hT0

/-- Positive finite generic density for the indicator kernel gives the finite
clique needed by the compact-Cayley theorem.  This is the endpoint that the
future counting-convergence proof should feed into. -/
theorem exists_clique_of_finiteCliqueKernelDensity_indicator_re_pos
    {p ℓ : ℕ} [NeZero p] {T : Finset (ZMod p)}
    (hTsym : SymmetricFinset T) (hT0 : (0 : ZMod p) ∉ T)
    (hdensity : 0 < (finiteCliqueKernelDensity (ℓ := ℓ) (indicatorC T)).re) :
    ∃ C : Finset (ZMod p), C.card = ℓ ∧ CliqueInCayley T C := by
  exact (finiteCliqueKernelDensity_indicatorC_re_pos_iff_exists_clique hTsym hT0).mp hdensity

/-- Finite endpoint for the compact counting transfer: if a bounded model
kernel has positive finite `K_ℓ` density by more than the spectral-transfer
error, and it is spectrally close to `1_T`, then `T` contains a clique. -/
theorem exists_clique_of_spectral_density_transfer
    {p ℓ : ℕ} [NeZero p] {T : Finset (ZMod p)}
    (hTsym : SymmetricFinset T) (hT0 : (0 : ZMod p) ∉ T)
    {g : ZMod p → ℂ} {M : ℝ}
    (hMnonneg : 0 ≤ M)
    (hg : ∀ z, ‖g z‖ ≤ 1)
    (hspec : SpectralBound (fun z => indicatorC T z - g z) M)
    (hdensity : ((cliqueEdgePairs ℓ).card : ℝ) * M <
      (finiteCliqueKernelDensity (ℓ := ℓ) g).re) :
    ∃ C : Finset (ZMod p), C.card = ℓ ∧ CliqueInCayley T C := by
  have hclose := norm_finiteCliqueKernelDensity_sub_le_card_mul_spectralBound
    (ℓ := ℓ) hMnonneg hg (indicatorC_norm_le_one T) hspec
  have hre_abs :
      |(finiteCliqueKernelDensity (ℓ := ℓ) (indicatorC T) -
          finiteCliqueKernelDensity (ℓ := ℓ) g).re| ≤
        ((cliqueEdgePairs ℓ).card : ℝ) * M := by
    exact le_trans (Complex.abs_re_le_norm _) hclose
  have hre_low :
      -(((cliqueEdgePairs ℓ).card : ℝ) * M) ≤
        (finiteCliqueKernelDensity (ℓ := ℓ) (indicatorC T) -
          finiteCliqueKernelDensity (ℓ := ℓ) g).re :=
    (abs_le.mp hre_abs).1
  have hpos : 0 < (finiteCliqueKernelDensity (ℓ := ℓ) (indicatorC T)).re := by
    have hcalc :
        (finiteCliqueKernelDensity (ℓ := ℓ) (indicatorC T)).re =
          (finiteCliqueKernelDensity (ℓ := ℓ) g).re +
            (finiteCliqueKernelDensity (ℓ := ℓ) (indicatorC T) -
              finiteCliqueKernelDensity (ℓ := ℓ) g).re := by
      simp
    rw [hcalc]
    linarith
  exact exists_clique_of_finiteCliqueKernelDensity_indicator_re_pos hTsym hT0 hpos

/-- Same finite endpoint with the rough bound `#E(K_ℓ) ≤ ℓ²`, avoiding exact
edge-count bookkeeping at higher compactness layers. -/
theorem exists_clique_of_spectral_density_transfer_sq
    {p ℓ : ℕ} [NeZero p] {T : Finset (ZMod p)}
    (hTsym : SymmetricFinset T) (hT0 : (0 : ZMod p) ∉ T)
    {g : ZMod p → ℂ} {M : ℝ}
    (hMnonneg : 0 ≤ M)
    (hg : ∀ z, ‖g z‖ ≤ 1)
    (hspec : SpectralBound (fun z => indicatorC T z - g z) M)
    (hdensity : ((ℓ * ℓ : ℕ) : ℝ) * M <
      (finiteCliqueKernelDensity (ℓ := ℓ) g).re) :
    ∃ C : Finset (ZMod p), C.card = ℓ ∧ CliqueInCayley T C := by
  have hcard : ((cliqueEdgePairs ℓ).card : ℝ) ≤ ((ℓ * ℓ : ℕ) : ℝ) := by
    exact_mod_cast cliqueEdgePairs_card_le_sq ℓ
  exact exists_clique_of_spectral_density_transfer hTsym hT0 hMnonneg hg hspec
    (lt_of_le_of_lt (mul_le_mul_of_nonneg_right hcard hMnonneg) hdensity)

end Erdos42.CompactCayley


/-! =============================================================
    Section from: Erdos/P42/CompactCayley/Subseq.lean
    ============================================================= -/

/-
Erdős Problem 42 — compact-Cayley counterexample subsequences.

Fourier extraction repeatedly passes to strictly monotone subsequences.  This
file keeps that bookkeeping out of the later compactness files.
-/


namespace Erdos42.CompactCayley

open Filter
open scoped Topology

/-- Pass a compact-Cayley counterexample sequence to a strictly monotone
subsequence. -/
def CayleyCounterSeq.subseq
    {ℓ : ℕ} {η : ℝ}
    (S : CayleyCounterSeq ℓ η)
    (φ : ℕ → ℕ) (hφ : StrictMono φ) :
    CayleyCounterSeq ℓ η where
  p n := S.p (φ n)
  prime n := S.prime (φ n)
  p_gt n := by
    have hn_le_φn : n ≤ φ n := by
      induction n with
      | zero =>
          exact Nat.zero_le _
      | succ n ih =>
          have hstep : φ n < φ (n + 1) := hφ (Nat.lt_succ_self n)
          omega
    exact lt_of_le_of_lt hn_le_φn (S.p_gt (φ n))
  T n := S.T (φ n)
  T_sym n := S.T_sym (φ n)
  T_zero n := S.T_zero (φ n)
  T_density n := S.T_density (φ n)
  eps n := S.eps (φ n)
  eps_pos n := S.eps_pos (φ n)
  eps_tendsto_zero := by
    exact S.eps_tendsto_zero.comp hφ.tendsto_atTop
  T_fourier_upper n := by
    simpa using S.T_fourier_upper (φ n)
  no_clique n := S.no_clique (φ n)

@[simp] lemma CayleyCounterSeq.subseq_p
    {ℓ : ℕ} {η : ℝ}
    (S : CayleyCounterSeq ℓ η)
    (φ : ℕ → ℕ) (hφ : StrictMono φ) (n : ℕ) :
    (S.subseq φ hφ).p n = S.p (φ n) := rfl

@[simp] lemma CayleyCounterSeq.subseq_T
    {ℓ : ℕ} {η : ℝ}
    (S : CayleyCounterSeq ℓ η)
    (φ : ℕ → ℕ) (hφ : StrictMono φ) (n : ℕ) :
    (S.subseq φ hφ).T n = S.T (φ n) := rfl

@[simp] lemma CayleyCounterSeq.subseq_eps
    {ℓ : ℕ} {η : ℝ}
    (S : CayleyCounterSeq ℓ η)
    (φ : ℕ → ℕ) (hφ : StrictMono φ) (n : ℕ) :
    (S.subseq φ hφ).eps n = S.eps (φ n) := rfl

/-- The epsilon bias still tends to zero after passing to a strictly monotone
subsequence. -/
lemma CayleyCounterSeq.subseq_tendsto_eps_zero
    {ℓ : ℕ} {η : ℝ}
    (S : CayleyCounterSeq ℓ η)
    (φ : ℕ → ℕ) (hφ : StrictMono φ) :
    Tendsto (fun n => S.eps (φ n)) atTop (𝓝 0) := by
  exact S.eps_tendsto_zero.comp hφ.tendsto_atTop

end Erdos42.CompactCayley


/-! =============================================================
    Section from: Erdos/P42/CompactCayley/FourierExtraction.lean
    ============================================================= -/

/-
Erdős Problem 42 — generic finite Fourier extraction primitives.

This is the first compact-Cayley axiom-removal layer.  It deliberately avoids
clique-specific definitions: a `FourierSeq` is only a bounded sequence of
complex-valued functions on prime cyclic groups.  Later compact-Cayley
extraction specializes it to the indicators of the counterexample sets.
-/


namespace Erdos42.CompactCayley

open Finset Erdos42
open scoped BigOperators Topology

/-- A bounded sequence of functions on prime cyclic groups. -/
structure FourierSeq where
  p : ℕ → ℕ
  prime : ∀ n, (p n).Prime
  p_gt : ∀ n, n < p n
  h : ∀ n, ZMod (p n) → ℂ
  h_bound : ∀ n x, ‖h n x‖ ≤ 1

/-- Pass a generic Fourier sequence to a strictly monotone subsequence. -/
def FourierSeq.subseq
    (F : FourierSeq) (φ : ℕ → ℕ) (hφ : StrictMono φ) :
    FourierSeq where
  p n := F.p (φ n)
  prime n := F.prime (φ n)
  p_gt n := by
    have hn_le_φn : n ≤ φ n := by
      induction n with
      | zero => exact Nat.zero_le _
      | succ n ih =>
          exact Nat.succ_le_of_lt (lt_of_le_of_lt ih (hφ (Nat.lt_succ_self n)))
    exact lt_of_le_of_lt hn_le_φn (F.p_gt (φ n))
  h n := F.h (φ n)
  h_bound n x := F.h_bound (φ n) x

/-- The Fourier sequence attached to a compact-Cayley counterexample sequence:
the functions are indicators of the allowed Cayley difference sets. -/
noncomputable def CayleyCounterSeq.toFourierSeq
    {ℓ : ℕ} {η : ℝ} (S : CayleyCounterSeq ℓ η) :
    FourierSeq where
  p := S.p
  prime := S.prime
  p_gt := S.p_gt
  h n := indicatorC (S.T n)
  h_bound n x := by
    classical
    by_cases hx : x ∈ S.T n <;> simp [indicatorC, hx]

/-- Normalized Fourier coefficient of the `n`-th function in a `FourierSeq`. -/
noncomputable def FourierSeq.coeff
    (F : FourierSeq) (n : ℕ) (r : ZMod (F.p n)) : ℂ :=
  letI : NeZero (F.p n) := ⟨(F.prime n).ne_zero⟩
  normalizedDftFunction (F.h n) r

lemma FourierSeq.coeff_eq_normalizedDftFunction
    (F : FourierSeq) (n : ℕ) :
    letI : NeZero (F.p n) := ⟨(F.prime n).ne_zero⟩
    F.coeff n = normalizedDftFunction (F.h n) := by
  funext r
  rfl

/-- Parseval bound for a bounded `FourierSeq` term. -/
lemma FourierSeq.sum_sq_norm_coeff_le_one
    (F : FourierSeq) (n : ℕ) :
    letI : NeZero (F.p n) := ⟨(F.prime n).ne_zero⟩
    (∑ r : ZMod (F.p n), ‖F.coeff n r‖ ^ 2) ≤ 1 := by
  letI : NeZero (F.p n) := ⟨(F.prime n).ne_zero⟩
  simpa [FourierSeq.coeff] using
    (sum_sq_norm_normalizedDftFunction_le_one_of_norm_le_one
      (p := F.p n) (f := F.h n) (F.h_bound n))

/-- Pointwise normalized Fourier coefficients of a bounded `FourierSeq` are
bounded by `1`. -/
lemma FourierSeq.norm_coeff_le_one
    (F : FourierSeq) (n : ℕ) (r : ZMod (F.p n)) :
    ‖F.coeff n r‖ ≤ 1 := by
  letI : NeZero (F.p n) := ⟨(F.prime n).ne_zero⟩
  have hsum := F.sum_sq_norm_coeff_le_one n
  have hterm :
      ‖F.coeff n r‖ ^ 2 ≤
        ∑ s : ZMod (F.p n), ‖F.coeff n s‖ ^ 2 :=
    Finset.single_le_sum
      (s := (Finset.univ : Finset (ZMod (F.p n))))
      (f := fun s : ZMod (F.p n) => ‖F.coeff n s‖ ^ 2)
      (fun _s _hs => sq_nonneg _) (Finset.mem_univ r)
  have hsquare : ‖F.coeff n r‖ ^ 2 ≤ 1 := hterm.trans hsum
  have habs : |‖F.coeff n r‖| ≤ 1 :=
    (sq_le_one_iff_abs_le_one _).mp hsquare
  simpa [abs_of_nonneg (norm_nonneg _)] using habs

/-- Large spectrum at threshold `q⁻¹`. -/
noncomputable def FourierSeq.largeSpectrum
    (F : FourierSeq) (q : ℕ+) (n : ℕ) :
    Finset (ZMod (F.p n)) :=
  letI : NeZero (F.p n) := ⟨(F.prime n).ne_zero⟩
  (Finset.univ : Finset (ZMod (F.p n))).filter
    (fun r => ((q : ℝ)⁻¹) < ‖F.coeff n r‖)

lemma FourierSeq.mem_largeSpectrum
    {F : FourierSeq} {q : ℕ+} {n : ℕ} {r : ZMod (F.p n)} :
    r ∈ F.largeSpectrum q n ↔ ((q : ℝ)⁻¹) < ‖F.coeff n r‖ := by
  letI : NeZero (F.p n) := ⟨(F.prime n).ne_zero⟩
  simp [FourierSeq.largeSpectrum]

lemma FourierSeq.largeSpectrum_subset_univ
    (F : FourierSeq) (q : ℕ+) (n : ℕ) :
    letI : NeZero (F.p n) := ⟨(F.prime n).ne_zero⟩
    F.largeSpectrum q n ⊆ (Finset.univ : Finset (ZMod (F.p n))) := by
  letI : NeZero (F.p n) := ⟨(F.prime n).ne_zero⟩
  intro r _hr
  simp

lemma FourierSeq.largeSpectrum_card_mul_sq_le_sum_sq
    (F : FourierSeq) (q : ℕ+) (n : ℕ) :
    letI : NeZero (F.p n) := ⟨(F.prime n).ne_zero⟩
    ((F.largeSpectrum q n).card : ℝ) * ((q : ℝ)⁻¹) ^ 2 ≤
      ∑ r : ZMod (F.p n), ‖F.coeff n r‖ ^ 2 := by
  letI : NeZero (F.p n) := ⟨(F.prime n).ne_zero⟩
  calc
    ((F.largeSpectrum q n).card : ℝ) * ((q : ℝ)⁻¹) ^ 2 =
        ∑ r ∈ F.largeSpectrum q n, ((q : ℝ)⁻¹) ^ 2 := by
          simp [mul_comm]
    _ ≤ ∑ r ∈ F.largeSpectrum q n, ‖F.coeff n r‖ ^ 2 := by
          refine Finset.sum_le_sum ?_
          intro r hr
          have hlt : ((q : ℝ)⁻¹) < ‖F.coeff n r‖ :=
            FourierSeq.mem_largeSpectrum.mp hr
          have hq_nonneg : 0 ≤ ((q : ℝ)⁻¹) := by positivity
          have hnorm_nonneg : 0 ≤ ‖F.coeff n r‖ := norm_nonneg _
          have hle_abs : |((q : ℝ)⁻¹)| ≤ |‖F.coeff n r‖| := by
            rw [abs_of_nonneg hq_nonneg, abs_of_nonneg hnorm_nonneg]
            exact le_of_lt hlt
          exact sq_le_sq.mpr hle_abs
    _ ≤ ∑ r : ZMod (F.p n), ‖F.coeff n r‖ ^ 2 := by
          exact Finset.sum_le_sum_of_subset_of_nonneg
            (F.largeSpectrum_subset_univ q n)
            (by intro r _hrUniv _hrNotLarge; exact sq_nonneg _)

/-- Parseval cardinality bound for the large spectrum at threshold `q⁻¹`. -/
lemma FourierSeq.largeSpectrum_card_le
    (F : FourierSeq) (q : ℕ+) (n : ℕ) :
    (F.largeSpectrum q n).card ≤ (q : ℕ) ^ 2 := by
  letI : NeZero (F.p n) := ⟨(F.prime n).ne_zero⟩
  have hmass :=
    (F.largeSpectrum_card_mul_sq_le_sum_sq q n).trans
      (F.sum_sq_norm_coeff_le_one n)
  have hq_pos : 0 < (q : ℝ) := by positivity
  have hτsq_pos : 0 < ((q : ℝ)⁻¹) ^ 2 := sq_pos_of_pos (inv_pos.mpr hq_pos)
  have hreal :
      ((F.largeSpectrum q n).card : ℝ) ≤ ((q : ℝ) ^ 2) := by
    calc
      ((F.largeSpectrum q n).card : ℝ) ≤
          1 / (((q : ℝ)⁻¹) ^ 2) := by
            exact (le_div_iff₀ hτsq_pos).mpr (by simpa [mul_comm] using hmass)
      _ = (q : ℝ) ^ 2 := by
            field_simp [hq_pos.ne']
  have hreal_nat :
      ((F.largeSpectrum q n).card : ℝ) ≤ (((q : ℕ) ^ 2 : ℕ) : ℝ) := by
    simpa using hreal
  exact_mod_cast hreal_nat

/-! ## Finite large-spectrum labelling -/

/-- A fixed countable label type large enough to label every threshold-large
frequency, for every `n`, without needing cardinalities to stabilize. -/
abbrev LargeLabel : Type :=
  Sigma fun q : ℕ+ => Fin ((q : ℕ) ^ 2 + 1)

/-- A finite set of cardinality at most `m` can be covered by a map from
`Fin m`.  Extra indices may repeat an arbitrary default value. -/
lemma exists_cover_map_of_card_le
    {α : Type*} [Inhabited α] (s : Finset α) (m : ℕ)
    (hcard : s.card ≤ m) :
    ∃ f : Fin m → α, ∀ x ∈ s, ∃ i : Fin m, f i = x := by
  classical
  let f : Fin m → α := fun i =>
    if h : (i : ℕ) < s.card then
      ((Finset.equivFin s).symm ⟨i, h⟩).1
    else default
  refine ⟨f, ?_⟩
  intro x hx
  let xs : s := ⟨x, hx⟩
  let j : Fin s.card := Finset.equivFin s xs
  let i : Fin m := ⟨j, lt_of_lt_of_le j.2 hcard⟩
  refine ⟨i, ?_⟩
  have hi : (i : ℕ) < s.card := j.2
  have hfin : (⟨(i : ℕ), hi⟩ : Fin s.card) = j := by
    ext
    rfl
  have hpre :
      (Finset.equivFin s).symm ⟨(i : ℕ), hi⟩ = xs := by
    rw [hfin]
    dsimp [j]
    simp
  simp [f, i, hi, hpre, xs]

/-- A canonical, choice-based frequency assignment for all large-spectrum
labels of a fixed `FourierSeq`. -/
noncomputable def FourierSeq.largeSpectrumLabelFreq
    (F : FourierSeq) (label : LargeLabel) (n : ℕ) :
    ZMod (F.p n) :=
  let q := label.1
  let m := (q : ℕ) ^ 2 + 1
  let cover :=
    Classical.choose
      (exists_cover_map_of_card_le (s := F.largeSpectrum q n) m (by
        have hcard := F.largeSpectrum_card_le q n
        omega))
  cover label.2

/-- Every threshold-large frequency is represented by one of the fixed labels
at that threshold. -/
lemma FourierSeq.exists_largeSpectrumLabelFreq_eq_of_mem
    (F : FourierSeq) (q : ℕ+) (n : ℕ) {r : ZMod (F.p n)}
    (hr : r ∈ F.largeSpectrum q n) :
    ∃ k : Fin ((q : ℕ) ^ 2 + 1),
      F.largeSpectrumLabelFreq ⟨q, k⟩ n = r := by
  classical
  unfold FourierSeq.largeSpectrumLabelFreq
  let m := (q : ℕ) ^ 2 + 1
  let cover :=
    Classical.choose
      (exists_cover_map_of_card_le (s := F.largeSpectrum q n) m (by
        have hcard := F.largeSpectrum_card_le q n
        omega))
  have hcover :
      ∀ x ∈ F.largeSpectrum q n, ∃ i : Fin m, cover i = x :=
    Classical.choose_spec
      (exists_cover_map_of_card_le (s := F.largeSpectrum q n) m (by
        have hcard := F.largeSpectrum_card_le q n
        omega))
  rcases hcover r hr with ⟨k, hk⟩
  exact ⟨k, hk⟩

/-- Existential packaging of the label-frequency assignment, useful for later
extraction structures that should not expose the chosen implementation. -/
theorem FourierSeq.exists_labelFreq_for_largeSpectrum
    (F : FourierSeq) :
    ∃ labelFreq : LargeLabel → ∀ n, ZMod (F.p n),
      ∀ q n r,
        r ∈ F.largeSpectrum q n →
        ∃ k : Fin ((q : ℕ) ^ 2 + 1),
          labelFreq ⟨q, k⟩ n = r := by
  refine ⟨fun label n => F.largeSpectrumLabelFreq label n, ?_⟩
  intro q n r hr
  exact F.exists_largeSpectrumLabelFreq_eq_of_mem q n hr

end Erdos42.CompactCayley


/-! =============================================================
    Section from: Erdos/P42/CompactCayley/ExtractionGroup.lean
    ============================================================= -/

/-
Erdős Problem 42 — compact-Cayley extraction quotient skeleton.

This file implements the formal free-abelian word lifts and the eventual-kernel
quotient used by the compact dual construction.  It intentionally stops before
the diagonal stability layer: without eventual zero/nonzero stabilization one
can define the quotient and its basic equality API, but not yet prove the
finite-lift injectivity-on-finite-sets facts needed later.
-/


namespace Erdos42.CompactCayley

open Filter Erdos42
open scoped Topology

/-- Formal integer combinations of compact-Cayley large-spectrum labels. -/
abbrev ExtractionFreeGroup : Type :=
  FreeAbelianGroup LargeLabel

instance extractionFreeGroupCountable : Countable ExtractionFreeGroup := by
  dsimp [ExtractionFreeGroup, LargeLabel]
  infer_instance

/-- Finite lift homomorphism of a formal label combination to the `n`-th
cyclic group. -/
noncomputable def FourierSeq.wordLiftHom
    (F : FourierSeq) (labelFreq : LargeLabel → ∀ n, ZMod (F.p n))
    (n : ℕ) :
    ExtractionFreeGroup →+ ZMod (F.p n) :=
  FreeAbelianGroup.lift fun label : LargeLabel => labelFreq label n

/-- Finite lift of a formal label combination. -/
noncomputable def FourierSeq.wordLift
    (F : FourierSeq) (labelFreq : LargeLabel → ∀ n, ZMod (F.p n))
    (w : ExtractionFreeGroup) (n : ℕ) :
    ZMod (F.p n) :=
  F.wordLiftHom labelFreq n w

lemma FourierSeq.wordLiftHom_apply_of
    (F : FourierSeq) (labelFreq : LargeLabel → ∀ n, ZMod (F.p n))
    (n : ℕ) (label : LargeLabel) :
    F.wordLiftHom labelFreq n (FreeAbelianGroup.of label) =
      labelFreq label n := by
  simp [FourierSeq.wordLiftHom]

lemma FourierSeq.wordLift_add
    (F : FourierSeq) (labelFreq : LargeLabel → ∀ n, ZMod (F.p n))
    (w v : ExtractionFreeGroup) (n : ℕ) :
    F.wordLift labelFreq (w + v) n =
      F.wordLift labelFreq w n + F.wordLift labelFreq v n := by
  simp [FourierSeq.wordLift]

lemma FourierSeq.wordLift_neg
    (F : FourierSeq) (labelFreq : LargeLabel → ∀ n, ZMod (F.p n))
    (w : ExtractionFreeGroup) (n : ℕ) :
    F.wordLift labelFreq (-w) n =
      -F.wordLift labelFreq w n := by
  simp [FourierSeq.wordLift]

/-- Formal combinations whose finite lifts vanish eventually. -/
def FourierSeq.eventualKernel
    (F : FourierSeq) (labelFreq : LargeLabel → ∀ n, ZMod (F.p n)) :
    AddSubgroup ExtractionFreeGroup where
  carrier := {w | ∀ᶠ n in atTop, F.wordLift labelFreq w n = 0}
  zero_mem' := by
    simp [FourierSeq.wordLift]
  add_mem' := by
    intro w v hw hv
    filter_upwards [hw, hv] with n hwn hvn
    simp [FourierSeq.wordLift_add, hwn, hvn]
  neg_mem' := by
    intro w hw
    filter_upwards [hw] with n hwn
    simp [FourierSeq.wordLift_neg, hwn]

lemma FourierSeq.mem_eventualKernel_iff
    {F : FourierSeq} {labelFreq : LargeLabel → ∀ n, ZMod (F.p n)}
    {w : ExtractionFreeGroup} :
    w ∈ F.eventualKernel labelFreq ↔
      ∀ᶠ n in atTop, F.wordLift labelFreq w n = 0 :=
  Iff.rfl

/-- Discrete quotient group produced by the compact-Cayley extraction
skeleton.  Its Pontryagin dual is the future compact limit group. -/
abbrev FourierSeq.ExtractionGroup
    (F : FourierSeq) (labelFreq : LargeLabel → ∀ n, ZMod (F.p n)) : Type :=
  ExtractionFreeGroup ⧸ F.eventualKernel labelFreq

instance FourierSeq.extractionGroupAddCommGroup
    (F : FourierSeq) (labelFreq : LargeLabel → ∀ n, ZMod (F.p n)) :
    AddCommGroup (F.ExtractionGroup labelFreq) :=
  inferInstance

instance FourierSeq.extractionGroupCountable
    (F : FourierSeq) (labelFreq : LargeLabel → ∀ n, ZMod (F.p n)) :
    Countable (F.ExtractionGroup labelFreq) :=
  (QuotientAddGroup.mk'_surjective (F.eventualKernel labelFreq)).countable

/-- Canonical quotient class of a large-spectrum label. -/
noncomputable def FourierSeq.extractionGenerator
    (F : FourierSeq) (labelFreq : LargeLabel → ∀ n, ZMod (F.p n)) :
    LargeLabel → F.ExtractionGroup labelFreq :=
  fun label => QuotientAddGroup.mk (FreeAbelianGroup.of label)

/-- Quotient equality is exactly eventual equality of finite lifts. -/
lemma FourierSeq.extractionQuotient_eq_iff_eventually_lift_eq
    {F : FourierSeq} {labelFreq : LargeLabel → ∀ n, ZMod (F.p n)}
    {w v : ExtractionFreeGroup} :
    (QuotientAddGroup.mk w : F.ExtractionGroup labelFreq) =
        QuotientAddGroup.mk v ↔
      ∀ᶠ n in atTop, F.wordLift labelFreq w n =
        F.wordLift labelFreq v n := by
  rw [QuotientAddGroup.eq_iff_sub_mem]
  simp only [FourierSeq.mem_eventualKernel_iff, AddMonoidHom.map_sub,
    FourierSeq.wordLift, sub_eq_zero]

/-- A quotient class is zero exactly when its finite lifts are eventually zero. -/
lemma FourierSeq.extractionQuotient_eq_zero_iff_eventually_lift_eq_zero
    {F : FourierSeq} {labelFreq : LargeLabel → ∀ n, ZMod (F.p n)}
    {w : ExtractionFreeGroup} :
    (QuotientAddGroup.mk w : F.ExtractionGroup labelFreq) = 0 ↔
      ∀ᶠ n in atTop, F.wordLift labelFreq w n = 0 := by
  rw [QuotientAddGroup.eq_zero_iff]
  rfl

/-- Equality of two quotient generators is eventual equality of their labelled
finite frequencies. -/
lemma FourierSeq.extractionGenerator_eq_iff_eventually_freq_eq
    (F : FourierSeq) (labelFreq : LargeLabel → ∀ n, ZMod (F.p n))
    (label label' : LargeLabel) :
    F.extractionGenerator labelFreq label =
        F.extractionGenerator labelFreq label' ↔
      ∀ᶠ n in atTop, labelFreq label n = labelFreq label' n := by
  rw [FourierSeq.extractionGenerator, FourierSeq.extractionGenerator,
    FourierSeq.extractionQuotient_eq_iff_eventually_lift_eq]
  simp [FourierSeq.wordLiftHom_apply_of, FourierSeq.wordLift]

end Erdos42.CompactCayley


/-! =============================================================
    Section from: Erdos/P42/CompactCayley/StableExtraction.lean
    ============================================================= -/

/-
Erdős Problem 42 — compact-Cayley diagonal extraction data.

The free-abelian extraction group from `ExtractionGroup` only becomes useful
after passing to a subsequence where every formal finite-lift zero relation is
eventually stable and every formal Fourier coefficient converges.  This file
packages that diagonal step for a generic `FourierSeq`.
-/


namespace Erdos42.CompactCayley

open Filter Erdos42
open scoped Topology

noncomputable section

/-- Closed unit disk, used as a compact target for countable diagonal
subsequence extraction. -/
abbrev ClosedUnitDisk : Type :=
  {z : ℂ // z ∈ Metric.closedBall (0 : ℂ) 1}

lemma compactSpace_closedUnitDisk : CompactSpace ClosedUnitDisk := by
  have hK : IsCompact (Metric.closedBall (0 : ℂ) 1) :=
    ProperSpace.isCompact_closedBall (0 : ℂ) 1
  exact isCompact_iff_compactSpace.mp hK

lemma exists_strictMono_subseq_tendsto_countable_family_of_norm_le_one
    {ι : Type*} [Countable ι] (a : ι → ℕ → ℂ)
    (ha : ∀ i n, ‖a i n‖ ≤ 1) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧
      ∀ i : ι, ∃ z : ℂ,
        Tendsto (fun n => a i (φ n)) atTop (𝓝 z) := by
  let x : ℕ → (ι → ClosedUnitDisk) := fun n i =>
    ⟨a i n, by
      rw [Metric.mem_closedBall, dist_zero_right]
      exact ha i n⟩
  letI : CompactSpace ClosedUnitDisk := compactSpace_closedUnitDisk
  rcases CompactSpace.tendsto_subseq x with ⟨y, φ, hφ, hlim⟩
  refine ⟨φ, hφ, ?_⟩
  intro i
  refine ⟨(y i : ℂ), ?_⟩
  have hcont :
      Continuous (fun y : ι → ClosedUnitDisk => ((y i : ClosedUnitDisk) : ℂ)) :=
    continuous_subtype_val.comp (continuous_apply i)
  have hi := (hcont.tendsto y).comp hlim
  simpa [x, Function.comp_def] using hi

/-- Countable diagonal stabilization for decidable relations.  This is the
relation-theoretic companion to coefficient convergence: after passing to one
subsequence, every countably indexed yes/no relation is eventually constantly
true or eventually constantly false. -/
lemma exists_strictMono_subseq_eventually_const_countable_family
    {ι : Type*} [Countable ι] (P : ι → ℕ → Prop)
    :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧
      ∀ i : ι, (∀ᶠ n in atTop, P i (φ n)) ∨
        (∀ᶠ n in atTop, ¬ P i (φ n)) := by
  classical
  let x : ℕ → (ι → Bool) := fun n i => decide (P i n)
  rcases CompactSpace.tendsto_subseq x with ⟨y, φ, hφ, hlim⟩
  refine ⟨φ, hφ, ?_⟩
  intro i
  have hcont : Continuous (fun y : ι → Bool => y i) := continuous_apply i
  have hi : Tendsto (fun n => x (φ n) i) atTop (𝓝 (y i)) :=
    (hcont.tendsto y).comp hlim
  have hmem : ({y i} : Set Bool) ∈ 𝓝 (y i) := by
    exact (isOpen_discrete ({y i} : Set Bool)).mem_nhds rfl
  have hmem' : ∀ᶠ n in atTop, x (φ n) i ∈ ({y i} : Set Bool) :=
    hi.eventually hmem
  have heq : ∀ᶠ n in atTop, x (φ n) i = y i := by
    filter_upwards [hmem'] with n hn
    simpa using hn
  cases hy : y i
  · right
    filter_upwards [heq] with n hn
    simpa [x, hy] using hn
  · left
    filter_upwards [heq] with n hn
    simpa [x, hy] using hn

/-- Relabel a label-frequency assignment after passing a `FourierSeq` to a
subsequence. -/
def FourierSeq.subseqLabelFreq
    (F : FourierSeq) (labelFreq : LargeLabel → ∀ n, ZMod (F.p n))
    (φ : ℕ → ℕ) (hφ : StrictMono φ) :
    LargeLabel → ∀ n, ZMod ((F.subseq φ hφ).p n) :=
  fun label n => labelFreq label (φ n)

lemma FourierSeq.wordLift_subseq
    (F : FourierSeq) (labelFreq : LargeLabel → ∀ n, ZMod (F.p n))
    (φ : ℕ → ℕ) (hφ : StrictMono φ)
    (w : ExtractionFreeGroup) (n : ℕ) :
    (F.subseq φ hφ).wordLift (F.subseqLabelFreq labelFreq φ hφ) w n =
      F.wordLift labelFreq w (φ n) := by
  rfl

/-- A fully diagonalized compact-Cayley Fourier extraction package for a fixed
label-frequency assignment.

The subsequence `φ` is still recorded explicitly because later Cayley
specialization will pass the whole counterexample sequence through the same
subsequence. -/
structure FourierSeq.StableSubseqData
    (F : FourierSeq) (labelFreq : LargeLabel → ∀ n, ZMod (F.p n)) where
  φ : ℕ → ℕ
  strictMono_φ : StrictMono φ
  finiteLift_eventually_stable : ∀ w : ExtractionFreeGroup,
    (∀ᶠ n in atTop, F.wordLift labelFreq w (φ n) = 0) ∨
      (∀ᶠ n in atTop, F.wordLift labelFreq w (φ n) ≠ 0)
  coeffLimit : ExtractionFreeGroup → ℂ
  coeffLimit_tendsto : ∀ w : ExtractionFreeGroup,
    Tendsto
      (fun n =>
        letI : NeZero (F.p (φ n)) := ⟨(F.prime (φ n)).ne_zero⟩;
        F.coeff (φ n) (F.wordLift labelFreq w (φ n)))
      atTop (𝓝 (coeffLimit w))

/-- Countable diagonal extraction for all formal finite-lift zero relations
and all formal Fourier coefficients. -/
theorem FourierSeq.exists_stableSubseqData
    (F : FourierSeq) (labelFreq : LargeLabel → ∀ n, ZMod (F.p n)) :
    ∃ _data : F.StableSubseqData labelFreq, True := by
  classical
  let P : ExtractionFreeGroup → ℕ → Prop :=
    fun w n => F.wordLift labelFreq w n = 0
  rcases
      exists_strictMono_subseq_eventually_const_countable_family
        P with
    ⟨φ, hφ, hstable⟩
  let a : ExtractionFreeGroup → ℕ → ℂ := fun w n =>
    letI : NeZero (F.p (φ n)) := ⟨(F.prime (φ n)).ne_zero⟩
    F.coeff (φ n) (F.wordLift labelFreq w (φ n))
  have ha : ∀ w n, ‖a w n‖ ≤ 1 := by
    intro w n
    dsimp [a]
    exact F.norm_coeff_le_one (φ n) (F.wordLift labelFreq w (φ n))
  rcases
      exists_strictMono_subseq_tendsto_countable_family_of_norm_le_one
        a ha with
    ⟨ψ, hψ, hconv⟩
  let χ : ℕ → ℕ := fun n => φ (ψ n)
  have hstrict : StrictMono χ := by
    simpa [χ, Function.comp_def] using hφ.comp hψ
  have hstable' : ∀ w : ExtractionFreeGroup,
      (∀ᶠ n in atTop, F.wordLift labelFreq w (χ n) = 0) ∨
        (∀ᶠ n in atTop, F.wordLift labelFreq w (χ n) ≠ 0) := by
    intro w
    rcases hstable w with hzero | hnonzero
    · exact Or.inl (by
        filter_upwards [hψ.tendsto_atTop.eventually hzero] with n hn
        change F.wordLift labelFreq w (φ (ψ n)) = 0
        simpa [P] using hn)
    · exact Or.inr (by
        filter_upwards [hψ.tendsto_atTop.eventually hnonzero] with n hn
        change F.wordLift labelFreq w (φ (ψ n)) ≠ 0
        simpa [P] using hn)
  have hcoeff : ∀ w : ExtractionFreeGroup, ∃ z : ℂ,
      Tendsto
        (fun n =>
          (letI : NeZero (F.p (χ n)) :=
              ⟨(F.prime (χ n)).ne_zero⟩;
            F.coeff (χ n)
              (F.wordLift labelFreq w (χ n))))
        atTop (𝓝 z) := by
    intro w
    rcases hconv w with ⟨z, hz⟩
    refine ⟨z, ?_⟩
    simpa [a, χ] using hz
  choose coeffLimit hcoeffLimit using hcoeff
  refine ⟨{
    φ := χ
    strictMono_φ := hstrict
    finiteLift_eventually_stable := hstable'
    coeffLimit := coeffLimit
    coeffLimit_tendsto := hcoeffLimit
  }, trivial⟩

end

end Erdos42.CompactCayley


/-! =============================================================
    Section from: Erdos/P42/CompactCayley/QuotientLift.lean
    ============================================================= -/

/-
Erdős Problem 42 — finite lifts from the compact-Cayley extraction quotient.

Stable extraction data selects a subsequence.  The quotient group used later is
the extraction quotient of that subsequenced `FourierSeq`; finite lifts of
quotient elements use arbitrary representatives, so all algebraic facts are
recorded as eventual statements.
-/


namespace Erdos42.CompactCayley

open Filter Erdos42
open scoped Topology

noncomputable section

namespace FourierSeq.StableSubseqData

variable {F : FourierSeq} {labelFreq : LargeLabel → ∀ n, ZMod (F.p n)}

/-- The Fourier sequence after applying the stable extraction subsequence. -/
def seq (data : F.StableSubseqData labelFreq) : FourierSeq :=
  F.subseq data.φ data.strictMono_φ

/-- The label frequencies transported to the stable extraction subsequence. -/
def subseqLabelFreq (data : F.StableSubseqData labelFreq) :
    LargeLabel → ∀ n, ZMod ((data.seq).p n) :=
  F.subseqLabelFreq labelFreq data.φ data.strictMono_φ

/-- The discrete extraction quotient attached to stable compact-Cayley data. -/
abbrev Group (data : F.StableSubseqData labelFreq) : Type :=
  (data.seq).ExtractionGroup data.subseqLabelFreq

instance (data : F.StableSubseqData labelFreq) :
    Countable data.Group :=
  FourierSeq.extractionGroupCountable data.seq data.subseqLabelFreq

/-- Finite lift homomorphism for formal words along the stable subsequence. -/
noncomputable def finiteLiftHom
    (data : F.StableSubseqData labelFreq) (n : ℕ) :
    ExtractionFreeGroup →+ ZMod (F.p (data.φ n)) :=
  (data.seq).wordLiftHom data.subseqLabelFreq n

lemma finiteLiftHom_apply
    (data : F.StableSubseqData labelFreq) (n : ℕ)
    (w : ExtractionFreeGroup) :
    data.finiteLiftHom n w = F.wordLift labelFreq w (data.φ n) := by
  rfl

/-- Chosen finite lift of a quotient frequency. -/
noncomputable def finiteLift
    (data : F.StableSubseqData labelFreq) (n : ℕ)
    (γ : data.Group) :
    ZMod (F.p (data.φ n)) :=
  data.finiteLiftHom n (Quotient.out γ)

/-- Quotient equality is eventual equality of chosen finite lifts of formal
representatives, along the stable subsequence. -/
lemma quotient_eq_iff_eventually_lift_eq
    (data : F.StableSubseqData labelFreq)
    {w v : ExtractionFreeGroup} :
    (QuotientAddGroup.mk w : data.Group) = QuotientAddGroup.mk v ↔
      ∀ᶠ n in atTop, data.finiteLiftHom n w = data.finiteLiftHom n v := by
  rw [FourierSeq.extractionQuotient_eq_iff_eventually_lift_eq
    (F := data.seq) (labelFreq := data.subseqLabelFreq)]
  rfl

/-- A quotient class is zero exactly when its representative lift vanishes
eventually. -/
lemma quotient_eq_zero_iff_eventually_lift_eq_zero
    (data : F.StableSubseqData labelFreq)
    {w : ExtractionFreeGroup} :
    (QuotientAddGroup.mk w : data.Group) = 0 ↔
      ∀ᶠ n in atTop, data.finiteLiftHom n w = 0 := by
  rw [FourierSeq.extractionQuotient_eq_zero_iff_eventually_lift_eq_zero
    (F := data.seq) (labelFreq := data.subseqLabelFreq)]
  rfl

/-- A chosen quotient representative has the same finite lift as any specified
representative of the same quotient class, eventually. -/
lemma finiteLift_mk_eventually_eq
    (data : F.StableSubseqData labelFreq) (w : ExtractionFreeGroup) :
    ∀ᶠ n in atTop,
      data.finiteLift n (QuotientAddGroup.mk w : data.Group) =
        data.finiteLiftHom n w := by
  exact (data.quotient_eq_iff_eventually_lift_eq
    (w := Quotient.out (QuotientAddGroup.mk w : data.Group)) (v := w)).mp
    (Quotient.out_eq _)

lemma finiteLift_zero_eventually_eq_zero
    (data : F.StableSubseqData labelFreq) :
    ∀ᶠ n in atTop, data.finiteLift n (0 : data.Group) = 0 := by
  simpa [finiteLift] using
    (data.quotient_eq_zero_iff_eventually_lift_eq_zero
      (w := Quotient.out (0 : data.Group))).mp
      (Quotient.out_eq (0 : data.Group))

lemma finiteLift_add_eventually_eq
    (data : F.StableSubseqData labelFreq) (γ δ : data.Group) :
    ∀ᶠ n in atTop,
      data.finiteLift n (γ + δ) =
        data.finiteLift n γ + data.finiteLift n δ := by
  have hquot :
      (QuotientAddGroup.mk (Quotient.out (γ + δ)) : data.Group) =
        QuotientAddGroup.mk (Quotient.out γ + Quotient.out δ) := by
    simp [Quotient.out_eq γ, Quotient.out_eq δ]
  filter_upwards
    [(data.quotient_eq_iff_eventually_lift_eq
      (w := Quotient.out (γ + δ))
      (v := Quotient.out γ + Quotient.out δ)).mp hquot] with n hn
  rw [finiteLift, hn]
  simp [finiteLift, finiteLiftHom]

lemma finiteLift_neg_eventually_eq
    (data : F.StableSubseqData labelFreq) (γ : data.Group) :
    ∀ᶠ n in atTop,
      data.finiteLift n (-γ) = -data.finiteLift n γ := by
  have hquot :
      (QuotientAddGroup.mk (Quotient.out (-γ)) : data.Group) =
        QuotientAddGroup.mk (-Quotient.out γ) := by
    simp [Quotient.out_eq γ]
  filter_upwards
    [(data.quotient_eq_iff_eventually_lift_eq
      (w := Quotient.out (-γ)) (v := -Quotient.out γ)).mp hquot] with n hn
  rw [finiteLift, hn]
  simp [finiteLift, finiteLiftHom]

lemma finiteLift_sub_eventually_eq
    (data : F.StableSubseqData labelFreq) (γ δ : data.Group) :
    ∀ᶠ n in atTop,
      data.finiteLift n (γ - δ) =
        data.finiteLift n γ - data.finiteLift n δ := by
  have hquot :
      (QuotientAddGroup.mk (Quotient.out (γ - δ)) : data.Group) =
        QuotientAddGroup.mk (Quotient.out γ - Quotient.out δ) := by
    simp [Quotient.out_eq γ, Quotient.out_eq δ]
  filter_upwards
    [(data.quotient_eq_iff_eventually_lift_eq
      (w := Quotient.out (γ - δ))
      (v := Quotient.out γ - Quotient.out δ)).mp hquot] with n hn
  rw [finiteLift, hn]
  simp [finiteLift, finiteLiftHom]

lemma finiteLift_sum_eventually_eq
    (data : F.StableSubseqData labelFreq)
    {ι : Type*} (s : Finset ι) (f : ι → data.Group) :
    ∀ᶠ n in atTop,
      data.finiteLift n (∑ i ∈ s, f i) =
        ∑ i ∈ s, data.finiteLift n (f i) := by
  classical
  refine Finset.induction_on s ?base ?step
  · filter_upwards [data.finiteLift_zero_eventually_eq_zero] with n hzero
    simpa using hzero
  · intro a s ha ih
    filter_upwards
      [ih, data.finiteLift_add_eventually_eq (f a) (∑ i ∈ s, f i)] with n hsum hadd
    rw [Finset.sum_insert ha, Finset.sum_insert ha, hadd, hsum]

lemma finiteLift_sum_univ_eventually_eq
    (data : F.StableSubseqData labelFreq)
    {ι : Type*} [Fintype ι] (f : ι → data.Group) :
    ∀ᶠ n in atTop,
      data.finiteLift n (∑ i, f i) =
        ∑ i, data.finiteLift n (f i) := by
  simpa using data.finiteLift_sum_eventually_eq (Finset.univ : Finset ι) f

lemma finiteLift_eq_of_eq_eventually
    (data : F.StableSubseqData labelFreq)
    {γ δ : data.Group} (h : γ = δ) :
    ∀ᶠ n in atTop, data.finiteLift n γ = data.finiteLift n δ := by
  subst h
  exact Eventually.of_forall fun _ => rfl

/-- Nonzero quotient elements have nonzero finite lifts eventually. -/
lemma finiteLift_eventually_ne_zero
    (data : F.StableSubseqData labelFreq)
    {γ : data.Group} (hγ : γ ≠ 0) :
    ∀ᶠ n in atTop, data.finiteLift n γ ≠ 0 := by
  rcases data.finiteLift_eventually_stable (Quotient.out γ) with hzero | hnonzero
  · have hγ0 : γ = 0 := by
      have hmk :
          (QuotientAddGroup.mk (Quotient.out γ) : data.Group) = 0 :=
        (data.quotient_eq_zero_iff_eventually_lift_eq_zero
          (w := Quotient.out γ)).mpr (by
            simpa [finiteLiftHom_apply] using hzero)
      simpa [Quotient.out_eq γ] using hmk
    exact (hγ hγ0).elim
  · simpa [finiteLift, finiteLiftHom_apply] using hnonzero

/-- Distinct quotient elements have distinct finite lifts eventually. -/
lemma finiteLift_eventually_ne_of_ne
    (data : F.StableSubseqData labelFreq)
    {γ δ : data.Group} (hγδ : γ ≠ δ) :
    ∀ᶠ n in atTop, data.finiteLift n γ ≠ data.finiteLift n δ := by
  have hsub : γ - δ ≠ 0 := sub_ne_zero.mpr hγδ
  filter_upwards
    [data.finiteLift_eventually_ne_zero hsub,
      data.finiteLift_sub_eventually_eq γ δ] with n hn hsubeq heq
  exact hn (by simpa [heq] using hsubeq)

/-- The finite lift is eventually injective on any fixed finite subset of the
extraction quotient. -/
lemma finiteLift_eventually_injOn_finset
    (data : F.StableSubseqData labelFreq) (Q : Finset data.Group) :
    ∀ᶠ n in atTop,
      Set.InjOn (fun γ => data.finiteLift n γ) (Q : Set data.Group) := by
  classical
  have hpairs :
      ∀ᶠ n in atTop, ∀ pair ∈ Q.product Q,
        pair.1 ≠ pair.2 →
          data.finiteLift n pair.1 ≠ data.finiteLift n pair.2 := by
    rw [(Q.product Q).eventually_all]
    intro pair _hmem
    by_cases hp : pair.1 = pair.2
    · exact Eventually.of_forall fun _ hne => (hne hp).elim
    · exact (data.finiteLift_eventually_ne_of_ne hp).mono
        (fun _ hn _hne => hn)
  filter_upwards [hpairs] with n hn γ hγ δ hδ heq
  by_contra hne
  have hpair : (γ, δ) ∈ Q.product Q := Finset.mem_product.mpr ⟨hγ, hδ⟩
  exact (hn (γ, δ) hpair hne) heq

end FourierSeq.StableSubseqData

end

end Erdos42.CompactCayley


/-! =============================================================
    Section from: Erdos/P42/CompactCayley/TorsionFree.lean
    ============================================================= -/

/-
Erdős Problem 42 — torsion-freeness of the compact-Cayley extraction quotient.

Finite lifts land in cyclic groups of prime order tending to infinity along the
stable subsequence.  A fixed nonzero scalar cannot create persistent torsion in
those cyclic groups, hence the eventual-kernel quotient is torsion-free.
-/


namespace Erdos42.CompactCayley

open Filter Erdos42
open scoped Topology

noncomputable section

namespace FourierSeq.StableSubseqData

variable {F : FourierSeq} {labelFreq : LargeLabel → ∀ n, ZMod (F.p n)}

lemma eventually_prime_gt
    (data : F.StableSubseqData labelFreq) (q : ℕ) :
    ∀ᶠ n in atTop, q < F.p (data.φ n) := by
  rw [Filter.eventually_atTop]
  refine ⟨q + 1, ?_⟩
  intro n hn
  have hq_lt_n : q < n :=
    Nat.lt_of_lt_of_le (Nat.lt_succ_self q) hn
  have hn_le_φn : n ≤ data.φ n := data.strictMono_φ.le_apply
  exact lt_trans (lt_of_lt_of_le hq_lt_n hn_le_φn)
    (F.p_gt (data.φ n))

lemma zmod_nsmul_eq_zero_iff_of_prime_not_dvd
    {p q : ℕ} [Fact p.Prime] (hnot : ¬ p ∣ q) (x : ZMod p) :
    q • x = 0 ↔ x = 0 := by
  have hunit : IsUnit (q : ZMod p) := by
    rw [ZMod.isUnit_iff_coprime]
    exact ((Nat.Prime.coprime_iff_not_dvd Fact.out).2 hnot).symm
  constructor
  · intro hx
    have hxmul : (q : ZMod p) * x = (q : ZMod p) * 0 := by
      simpa [nsmul_eq_mul] using hx
    exact hunit.mul_left_cancel hxmul
  · intro hx
    simp [hx]

lemma quotient_nsmul_eq_zero_iff_eventually_lift_nsmul_eq_zero
    (data : F.StableSubseqData labelFreq)
    (q : ℕ) {w : ExtractionFreeGroup} :
    q • (QuotientAddGroup.mk w : data.Group) = 0 ↔
      ∀ᶠ n in atTop, q • data.finiteLiftHom n w = 0 := by
  rw [← QuotientAddGroup.mk_nsmul
    ((data.seq).eventualKernel data.subseqLabelFreq) w q,
    data.quotient_eq_zero_iff_eventually_lift_eq_zero]
  simp [AddMonoidHom.map_nsmul]

lemma finiteLiftHom_eventually_eq_zero_of_eventually_nsmul_eq_zero
    (data : F.StableSubseqData labelFreq)
    {q : ℕ} (hq : q ≠ 0) {w : ExtractionFreeGroup}
    (h : ∀ᶠ n in atTop, q • data.finiteLiftHom n w = 0) :
    ∀ᶠ n in atTop, data.finiteLiftHom n w = 0 := by
  filter_upwards [h, data.eventually_prime_gt q] with n hn hgt
  haveI : Fact (F.p (data.φ n)).Prime := ⟨F.prime (data.φ n)⟩
  have hnot : ¬ F.p (data.φ n) ∣ q :=
    Nat.not_dvd_of_pos_of_lt (Nat.pos_of_ne_zero hq) hgt
  exact (zmod_nsmul_eq_zero_iff_of_prime_not_dvd hnot
    (data.finiteLiftHom n w)).mp hn

/-- The stable compact-Cayley extraction quotient is torsion-free. -/
theorem group_isAddTorsionFree
    (data : F.StableSubseqData labelFreq) :
    IsAddTorsionFree data.Group where
  nsmul_right_injective := by
    intro q hq x y hxy
    induction x using QuotientAddGroup.induction_on with
    | H w =>
      induction y using QuotientAddGroup.induction_on with
      | H v =>
        have hsub_q :
            q • (QuotientAddGroup.mk (w - v) : data.Group) = 0 := by
          rw [QuotientAddGroup.mk_sub]
          simp [nsmul_sub, hxy]
        have hlift_q :
            ∀ᶠ n in atTop, q • data.finiteLiftHom n (w - v) = 0 :=
          (data.quotient_nsmul_eq_zero_iff_eventually_lift_nsmul_eq_zero
            q).mp hsub_q
        have hlift :
            ∀ᶠ n in atTop, data.finiteLiftHom n (w - v) = 0 :=
          data.finiteLiftHom_eventually_eq_zero_of_eventually_nsmul_eq_zero
            hq hlift_q
        have hsub :
            (QuotientAddGroup.mk (w - v) : data.Group) = 0 :=
          (data.quotient_eq_zero_iff_eventually_lift_eq_zero).mpr hlift
        rw [QuotientAddGroup.mk_sub] at hsub
        exact sub_eq_zero.mp hsub

instance (data : F.StableSubseqData labelFreq) :
    IsAddTorsionFree data.Group :=
  data.group_isAddTorsionFree

end FourierSeq.StableSubseqData

end

end Erdos42.CompactCayley


/-! =============================================================
    Section from: Erdos/P42/CompactCayley/CoeffLimit.lean
    ============================================================= -/

/-
Erdős Problem 42 — quotient coefficient limits and large-spectrum cover.

This file pushes the formal-word coefficient limits from stable extraction data
to chosen representatives of quotient frequencies.  It also records the key
large-spectrum covering consequence of the non-nested labels.
-/


namespace Erdos42.CompactCayley

open Filter Erdos42
open scoped BigOperators Topology

noncomputable section

namespace FourierSeq.StableSubseqData

variable {F : FourierSeq} {labelFreq : LargeLabel → ∀ n, ZMod (F.p n)}

/-- Coefficient limit attached to a quotient frequency, using its chosen
representative. -/
noncomputable def coeff
    (data : F.StableSubseqData labelFreq) (γ : data.Group) : ℂ :=
  data.coeffLimit (Quotient.out γ)

lemma coeff_tendsto
    (data : F.StableSubseqData labelFreq) (γ : data.Group) :
    Tendsto
      (fun n =>
        letI : NeZero (F.p (data.φ n)) := ⟨(F.prime (data.φ n)).ne_zero⟩;
        F.coeff (data.φ n) (data.finiteLift n γ))
      atTop (𝓝 (data.coeff γ)) := by
  simpa [coeff, finiteLift, finiteLiftHom_apply] using
    data.coeffLimit_tendsto (Quotient.out γ)

/-- Quotient generator associated to a large-spectrum label. -/
noncomputable def generator
    (data : F.StableSubseqData labelFreq) (label : LargeLabel) :
    data.Group :=
  QuotientAddGroup.mk (FreeAbelianGroup.of label)

/-- The finite set of quotient frequencies representing the `q`-large
spectrum, plus zero. -/
noncomputable def largeSpectrumGenerators
    (data : F.StableSubseqData labelFreq) (q : ℕ+) :
    Finset data.Group :=
  ((Finset.univ : Finset (Fin ((q : ℕ) ^ 2 + 1))).image
      (fun k => data.generator (⟨q, k⟩ : LargeLabel))) ∪ {0}

lemma generator_mem_largeSpectrumGenerators
    (data : F.StableSubseqData labelFreq) (q : ℕ+)
    (k : Fin ((q : ℕ) ^ 2 + 1)) :
    data.generator (⟨q, k⟩ : LargeLabel) ∈
      data.largeSpectrumGenerators q := by
  classical
  unfold largeSpectrumGenerators
  exact Finset.mem_union.mpr <|
    Or.inl (Finset.mem_image.mpr ⟨k, Finset.mem_univ _, rfl⟩)

lemma zero_mem_largeSpectrumGenerators
    (data : F.StableSubseqData labelFreq) (q : ℕ+) :
    (0 : data.Group) ∈ data.largeSpectrumGenerators q := by
  classical
  simp [largeSpectrumGenerators]

lemma largeSpectrumGenerators_card_le
    (data : F.StableSubseqData labelFreq) (q : ℕ+) :
    (data.largeSpectrumGenerators q).card ≤ (q : ℕ) ^ 2 + 2 := by
  classical
  unfold largeSpectrumGenerators
  calc
    (((Finset.univ : Finset (Fin ((q : ℕ) ^ 2 + 1))).image
          (fun k => data.generator (⟨q, k⟩ : LargeLabel))) ∪ {0}).card
        ≤ ((((Finset.univ : Finset (Fin ((q : ℕ) ^ 2 + 1))).image
          (fun k => data.generator (⟨q, k⟩ : LargeLabel))).card) +
            (({(0 : data.Group)} : Finset data.Group).card)) := by
          exact Finset.card_union_le _ _
    _ = (((Finset.univ : Finset (Fin ((q : ℕ) ^ 2 + 1))).image
          (fun k => data.generator (⟨q, k⟩ : LargeLabel))).card) + 1 := by
          simp
    _ ≤ (Finset.univ : Finset (Fin ((q : ℕ) ^ 2 + 1))).card + 1 := by
          exact Nat.add_le_add_right Finset.card_image_le 1
    _ = (q : ℕ) ^ 2 + 2 := by simp

/-- Label generators have their labelled finite frequency as finite lift,
eventually. -/
lemma finiteLift_generator_eventually_eq
    (data : F.StableSubseqData labelFreq) (label : LargeLabel) :
    ∀ᶠ n in atTop,
      data.finiteLift n (data.generator label) =
        labelFreq label (data.φ n) := by
  filter_upwards
    [data.finiteLift_mk_eventually_eq (FreeAbelianGroup.of label)] with n hn
  simpa [generator, finiteLiftHom_apply, FourierSeq.wordLift,
    FourierSeq.wordLiftHom_apply_of] using hn

/-- If `labelFreq` covers every finite large spectrum before extraction, then
the quotient generators cover every finite large spectrum along the stable
subsequence. -/
lemma eventually_largeSpectrum_covered
    (data : F.StableSubseqData labelFreq)
    (hcover :
      ∀ q n r, r ∈ F.largeSpectrum q n →
        ∃ k : Fin ((q : ℕ) ^ 2 + 1),
          labelFreq ⟨q, k⟩ n = r)
    (q : ℕ+) :
    ∀ᶠ n in atTop,
      ∀ r : ZMod (F.p (data.φ n)),
        ((q : ℝ)⁻¹ : ℝ) < ‖F.coeff (data.φ n) r‖ →
          ∃ γ ∈ data.largeSpectrumGenerators q,
            data.finiteLift n γ = r := by
  classical
  have hlabels' :
      ∀ᶠ n in atTop,
        ∀ k ∈ (Finset.univ : Finset (Fin ((q : ℕ) ^ 2 + 1))),
          data.finiteLift n (data.generator (⟨q, k⟩ : LargeLabel)) =
            labelFreq ⟨q, k⟩ (data.φ n) := by
    rw [(Finset.univ : Finset (Fin ((q : ℕ) ^ 2 + 1))).eventually_all]
    intro k _hk
    exact data.finiteLift_generator_eventually_eq (⟨q, k⟩ : LargeLabel)
  have hlabels :
      ∀ᶠ n in atTop,
        ∀ k : Fin ((q : ℕ) ^ 2 + 1),
          data.finiteLift n (data.generator (⟨q, k⟩ : LargeLabel)) =
            labelFreq ⟨q, k⟩ (data.φ n) := by
    filter_upwards [hlabels'] with n hn k
    exact hn k (Finset.mem_univ k)
  filter_upwards [hlabels] with n hn r hr
  have hrmem : r ∈ F.largeSpectrum q (data.φ n) :=
    FourierSeq.mem_largeSpectrum.mpr hr
  rcases hcover q (data.φ n) r hrmem with ⟨k, hk⟩
  refine ⟨data.generator (⟨q, k⟩ : LargeLabel),
    data.generator_mem_largeSpectrumGenerators q k, ?_⟩
  exact (hn k).trans hk

/-- Coefficient limits outside the `q`-large-spectrum generator set have norm
at most `q⁻¹`. -/
lemma coeff_norm_le_inv_of_not_mem_largeSpectrumGenerators
    (data : F.StableSubseqData labelFreq)
    (hcover :
      ∀ q n r, r ∈ F.largeSpectrum q n →
        ∃ k : Fin ((q : ℕ) ^ 2 + 1),
          labelFreq ⟨q, k⟩ n = r)
    (q : ℕ+) {γ : data.Group}
    (hγ : γ ∉ data.largeSpectrumGenerators q) :
    ‖data.coeff γ‖ ≤ ((q : ℝ)⁻¹ : ℝ) := by
  classical
  by_contra hnot
  have hlt : ((q : ℝ)⁻¹ : ℝ) < ‖data.coeff γ‖ := lt_of_not_ge hnot
  have hnorm :
      Tendsto
        (fun n =>
          ‖(letI : NeZero (F.p (data.φ n)) :=
              ⟨(F.prime (data.φ n)).ne_zero⟩;
            F.coeff (data.φ n) (data.finiteLift n γ))‖)
        atTop (𝓝 ‖data.coeff γ‖) :=
    (continuous_norm.tendsto (data.coeff γ)).comp (data.coeff_tendsto γ)
  have hlarge :
      ∀ᶠ n in atTop,
        ((q : ℝ)⁻¹ : ℝ) <
          ‖(letI : NeZero (F.p (data.φ n)) :=
              ⟨(F.prime (data.φ n)).ne_zero⟩;
            F.coeff (data.φ n) (data.finiteLift n γ))‖ :=
    hnorm.eventually (eventually_gt_nhds hlt)
  have hcovered := data.eventually_largeSpectrum_covered hcover q
  have hinj :=
    data.finiteLift_eventually_injOn_finset
      (data.largeSpectrumGenerators q ∪ {γ})
  rcases (hlarge.and (hcovered.and hinj)).exists with
    ⟨n, hnlarge, hncovered, hninj⟩
  rcases hncovered (data.finiteLift n γ) (by simpa using hnlarge) with
    ⟨δ, hδmem, hδeq⟩
  have hδmem' : δ ∈ (data.largeSpectrumGenerators q ∪ {γ}) := by
    simp [hδmem]
  have hγmem' : γ ∈ (data.largeSpectrumGenerators q ∪ {γ}) := by
    simp
  have hδγ : δ = γ := hninj hδmem' hγmem' hδeq
  exact hγ (by simpa [hδγ] using hδmem)

end FourierSeq.StableSubseqData

end

end Erdos42.CompactCayley


/-! =============================================================
    Section from: Erdos/P42/CompactCayley/CayleyExtraction.lean
    ============================================================= -/

/-
Erdős Problem 42 — compact-Cayley extraction specialized to counterexamples.

This file connects the generic Fourier extraction sequence to the concrete
counterexample sets `T_n`.  The resulting coefficient facts are the finite
hypotheses that later define the compact limit kernel.
-/


namespace Erdos42.CompactCayley

open Filter Erdos42
open scoped Topology

noncomputable section

/-- Stable Fourier extraction package attached to a compact-Cayley
counterexample sequence. -/
structure CayleyExtraction {ℓ : ℕ} {η : ℝ}
    (S : CayleyCounterSeq ℓ η) where
  data :
    (S.toFourierSeq).StableSubseqData
      (S.toFourierSeq.largeSpectrumLabelFreq)

namespace CayleyExtraction

variable {ℓ : ℕ} {η : ℝ} {S : CayleyCounterSeq ℓ η}

/-- The discrete extraction quotient. -/
abbrev Group (E : CayleyExtraction S) : Type :=
  E.data.Group

instance (E : CayleyExtraction S) : Countable E.Group :=
  inferInstance

instance (E : CayleyExtraction S) : IsAddTorsionFree E.Group :=
  inferInstance

/-- The selected index in the original counterexample sequence. -/
def φ (E : CayleyExtraction S) : ℕ → ℕ :=
  E.data.φ

lemma strictMono_φ (E : CayleyExtraction S) :
    StrictMono E.φ :=
  E.data.strictMono_φ

/-- Finite lift of an extraction quotient frequency to the selected cyclic
group. -/
noncomputable def lift (E : CayleyExtraction S)
    (n : ℕ) (γ : E.Group) :
    ZMod (S.p (E.φ n)) :=
  E.data.finiteLift n γ

/-- Coefficient limit attached to a quotient frequency. -/
noncomputable def coeff (E : CayleyExtraction S) (γ : E.Group) : ℂ :=
  E.data.coeff γ

lemma coeff_tendsto (E : CayleyExtraction S) (γ : E.Group) :
    Tendsto
      (fun n =>
        letI : NeZero (S.p (E.φ n)) := ⟨(S.prime (E.φ n)).ne_zero⟩;
        normalizedDftCoeff (S.T (E.φ n)) (E.lift n γ))
      atTop (𝓝 (E.coeff γ)) := by
  simpa [coeff, lift, φ, CayleyCounterSeq.toFourierSeq, FourierSeq.coeff,
    normalizedDftCoeff] using E.data.coeff_tendsto γ

/-- Canonical labels cover all finite large spectra along the extracted
subsequence. -/
lemma eventually_largeSpectrum_covered
    (E : CayleyExtraction S) (q : ℕ+) :
    ∀ᶠ n in atTop,
      ∀ r : ZMod (S.p (E.φ n)),
        ((q : ℝ)⁻¹ : ℝ) <
            ‖(letI : NeZero (S.p (E.φ n)) :=
                ⟨(S.prime (E.φ n)).ne_zero⟩;
              normalizedDftCoeff (S.T (E.φ n)) r)‖ →
          ∃ γ ∈ E.data.largeSpectrumGenerators q,
            E.lift n γ = r := by
  have hcover :
      ∀ q n r,
        r ∈ (S.toFourierSeq).largeSpectrum q n →
          ∃ k : Fin ((q : ℕ) ^ 2 + 1),
            (S.toFourierSeq).largeSpectrumLabelFreq ⟨q, k⟩ n = r := by
    intro q n r hr
    exact (S.toFourierSeq).exists_largeSpectrumLabelFreq_eq_of_mem q n hr
  simpa [lift, φ, CayleyCounterSeq.toFourierSeq, FourierSeq.coeff,
    normalizedDftCoeff] using
      E.data.eventually_largeSpectrum_covered hcover q

lemma coeff_norm_le_inv_of_not_mem_largeSpectrumGenerators
    (E : CayleyExtraction S) (q : ℕ+) {γ : E.Group}
    (hγ : γ ∉ E.data.largeSpectrumGenerators q) :
    ‖E.coeff γ‖ ≤ ((q : ℝ)⁻¹ : ℝ) := by
  have hcover :
      ∀ q n r,
        r ∈ (S.toFourierSeq).largeSpectrum q n →
          ∃ k : Fin ((q : ℕ) ^ 2 + 1),
            (S.toFourierSeq).largeSpectrumLabelFreq ⟨q, k⟩ n = r := by
    intro q n r hr
    exact (S.toFourierSeq).exists_largeSpectrumLabelFreq_eq_of_mem q n hr
  simpa [coeff] using
    E.data.coeff_norm_le_inv_of_not_mem_largeSpectrumGenerators hcover q hγ

lemma coeff_im_eq_zero (E : CayleyExtraction S) (γ : E.Group) :
    (E.coeff γ).im = 0 := by
  have hlim :=
    Complex.continuous_im.tendsto (E.coeff γ) |>.comp (E.coeff_tendsto γ)
  have him :
      ∀ᶠ n in atTop,
        (letI : NeZero (S.p (E.φ n)) := ⟨(S.prime (E.φ n)).ne_zero⟩;
          (normalizedDftCoeff (S.T (E.φ n)) (E.lift n γ)).im) = 0 :=
    Filter.Eventually.of_forall (fun n => by
      letI : NeZero (S.p (E.φ n)) := ⟨(S.prime (E.φ n)).ne_zero⟩
      exact normalizedDftCoeff_im_eq_zero_of_symmetric
        (S.T_sym (E.φ n)) (E.lift n γ))
  have hzero :
      Tendsto (fun _n : ℕ => (0 : ℝ)) atTop (𝓝 (E.coeff γ).im) :=
    Filter.Tendsto.congr' him hlim
  exact tendsto_nhds_unique hzero tendsto_const_nhds

lemma coeff_neg_eq (E : CayleyExtraction S) (γ : E.Group) :
    E.coeff (-γ) = E.coeff γ := by
  have hneg_tendsto := E.coeff_tendsto (-γ)
  have hpos_tendsto := E.coeff_tendsto γ
  have heq :
      (fun n =>
        letI : NeZero (S.p (E.φ n)) := ⟨(S.prime (E.φ n)).ne_zero⟩;
        normalizedDftCoeff (S.T (E.φ n)) (E.lift n (-γ))) =ᶠ[atTop]
      (fun n =>
        letI : NeZero (S.p (E.φ n)) := ⟨(S.prime (E.φ n)).ne_zero⟩;
        normalizedDftCoeff (S.T (E.φ n)) (E.lift n γ)) := by
    filter_upwards [E.data.finiteLift_neg_eventually_eq γ] with n hneg
    haveI : NeZero (S.p (E.φ n)) := ⟨(S.prime (E.φ n)).ne_zero⟩
    rw [lift, lift, hneg]
    exact normalizedDftCoeff_neg_eq_of_symmetric (S.T_sym (E.φ n)) (E.lift n γ)
  exact tendsto_nhds_unique (hneg_tendsto.congr' heq) hpos_tendsto

lemma coeff_nonpos_of_ne_zero
    (E : CayleyExtraction S) {γ : E.Group} (hγ : γ ≠ 0) :
    (E.coeff γ).re ≤ 0 := by
  have hlim :=
    Complex.continuous_re.tendsto (E.coeff γ) |>.comp (E.coeff_tendsto γ)
  have heps :
      Tendsto (fun n => S.eps (E.φ n)) atTop (𝓝 0) :=
    S.eps_tendsto_zero.comp E.strictMono_φ.tendsto_atTop
  have hupper :
      ∀ᶠ n in atTop,
        (letI : NeZero (S.p (E.φ n)) := ⟨(S.prime (E.φ n)).ne_zero⟩;
          (normalizedDftCoeff (S.T (E.φ n)) (E.lift n γ)).re) ≤
          S.eps (E.φ n) := by
    filter_upwards [E.data.finiteLift_eventually_ne_zero hγ] with n hn
    letI : NeZero (S.p (E.φ n)) := ⟨(S.prime (E.φ n)).ne_zero⟩
    exact S.T_fourier_upper (E.φ n) (E.lift n γ) hn
  exact le_of_tendsto_of_tendsto hlim heps hupper

lemma coeff_zero_ge_eta (E : CayleyExtraction S) :
    η ≤ (E.coeff 0).re := by
  have hlim :=
    Complex.continuous_re.tendsto (E.coeff (0 : E.Group)) |>.comp
      (E.coeff_tendsto (0 : E.Group))
  have hdens :
      ∀ᶠ n in atTop,
        η ≤
          (letI : NeZero (S.p (E.φ n)) := ⟨(S.prime (E.φ n)).ne_zero⟩;
            (normalizedDftCoeff (S.T (E.φ n)) (E.lift n 0)).re) := by
    filter_upwards [E.data.finiteLift_zero_eventually_eq_zero] with n hn
    letI : NeZero (S.p (E.φ n)) := ⟨(S.prime (E.φ n)).ne_zero⟩
    have hp_pos : 0 < (S.p (E.φ n) : ℝ) := by
      exact_mod_cast Nat.pos_of_ne_zero (S.prime (E.φ n)).ne_zero
    have hη_div :
        η ≤ ((S.T (E.φ n)).card : ℝ) / (S.p (E.φ n) : ℝ) :=
      (le_div_iff₀ hp_pos).mpr (S.T_density (E.φ n))
    have hlift : E.lift n (0 : E.Group) = (0 : ZMod (S.p (E.φ n))) := by
      change E.data.finiteLift n (0 : E.data.Group) = 0
      exact hn
    have hcoeff_re :
        ((normalizedDftCoeff (S.T (E.φ n)) (E.lift n 0)).re) =
          ((S.T (E.φ n)).card : ℝ) / (S.p (E.φ n) : ℝ) := by
      rw [hlift]
      rw [normalizedDftCoeff_zero_eq_card_div]
      simp
    rw [hcoeff_re]
    exact hη_div
  exact le_of_tendsto_of_tendsto tendsto_const_nhds hlim hdens

end CayleyExtraction

/-- Existence of compact-Cayley stable extraction data for a counterexample
sequence. -/
theorem exists_cayleyExtraction
    {ℓ : ℕ} {η : ℝ} (S : CayleyCounterSeq ℓ η) :
    ∃ _E : CayleyExtraction S, True := by
  classical
  rcases (S.toFourierSeq).exists_stableSubseqData
      (S.toFourierSeq.largeSpectrumLabelFreq) with
    ⟨data, _⟩
  exact ⟨⟨data⟩, trivial⟩

end

end Erdos42.CompactCayley


/-! =============================================================
    Section from: Erdos/P42/CompactCayley/CompactDual.lean
    ============================================================= -/

/-
Erdős Problem 42 — compact dual attached to compact-Cayley extraction.

The extraction quotient is a countable discrete torsion-free abelian group.
This file builds its Pontryagin dual, then wraps it additively so the compact
endpoint can use additive notation and Haar probability measure.
-/


namespace Erdos42.CompactCayley


noncomputable section

namespace CayleyExtraction

variable {ℓ : ℕ} {η : ℝ} {S : CayleyCounterSeq ℓ η}

instance groupTopologicalSpace (E : CayleyExtraction S) :
    TopologicalSpace E.Group :=
  ⊥

instance groupDiscreteTopology (E : CayleyExtraction S) :
    DiscreteTopology E.Group :=
  ⟨rfl⟩

/-- Multiplicative version of the extraction quotient, for Mathlib's
`PontryaginDual` API. -/
abbrev DualDomain (E : CayleyExtraction S) : Type :=
  Multiplicative E.Group

/-- Compact Pontryagin dual of the extraction quotient. -/
abbrev CompactDual (E : CayleyExtraction S) : Type :=
  PontryaginDual E.DualDomain

/-- Additive wrapper around the compact extraction dual. -/
abbrev CompactAddDual (E : CayleyExtraction S) : Type :=
  Additive E.CompactDual

theorem compactDual_compactSpace (E : CayleyExtraction S) :
    CompactSpace E.CompactDual :=
  inferInstance

theorem compactDual_t2Space (E : CayleyExtraction S) :
    T2Space E.CompactDual :=
  inferInstance

theorem compactDual_isTopologicalGroup (E : CayleyExtraction S) :
    IsTopologicalGroup E.CompactDual :=
  inferInstance

instance dualDomainCountable (E : CayleyExtraction S) :
    Countable E.DualDomain :=
  Countable.of_equiv E.Group Multiplicative.ofAdd

instance dualDomainDiscreteTopology (E : CayleyExtraction S) :
    DiscreteTopology E.DualDomain :=
  inferInstance

instance dualDomainSecondCountableTopology (E : CayleyExtraction S) :
    SecondCountableTopology E.DualDomain := by
  letI : Countable E.DualDomain := dualDomainCountable E
  letI : DiscreteTopology E.DualDomain := dualDomainDiscreteTopology E
  infer_instance

instance compactDualSecondCountableTopology (E : CayleyExtraction S) :
    SecondCountableTopology E.CompactDual := by
  dsimp [CompactDual, PontryaginDual]
  exact (ContinuousMonoidHom.isInducing_toContinuousMap
    E.DualDomain Circle).secondCountableTopology

theorem dualDomain_isMulTorsionFree (E : CayleyExtraction S) :
    IsMulTorsionFree E.DualDomain :=
  inferInstance

/-- Identity homeomorphism from the multiplicative compact dual to its
additive wrapper. -/
def compactDualAdditiveHomeomorph (E : CayleyExtraction S) :
    E.CompactDual ≃ₜ E.CompactAddDual where
  toEquiv := Additive.ofMul
  continuous_toFun := continuous_id
  continuous_invFun := continuous_id

theorem compactAddDual_t2Space (E : CayleyExtraction S) :
    T2Space E.CompactAddDual :=
  (E.compactDualAdditiveHomeomorph).t2Space

theorem compactAddDual_compactSpace (E : CayleyExtraction S) :
    CompactSpace E.CompactAddDual :=
  inferInstance

theorem compactAddDual_isTopologicalAddGroup (E : CayleyExtraction S) :
    IsTopologicalAddGroup E.CompactAddDual :=
  inferInstance

instance compactAddDualSecondCountableTopology (E : CayleyExtraction S) :
    SecondCountableTopology E.CompactAddDual :=
  (E.compactDualAdditiveHomeomorph).symm.secondCountableTopology

instance compactAddDualMeasurableSpace (E : CayleyExtraction S) :
    MeasurableSpace E.CompactAddDual :=
  borel E.CompactAddDual

instance compactAddDualBorelSpace (E : CayleyExtraction S) :
    BorelSpace E.CompactAddDual :=
  ⟨rfl⟩

instance compactAddDualMeasurableAdd₂ (E : CayleyExtraction S) :
    MeasurableAdd₂ E.CompactAddDual where
  measurable_add := continuous_add.measurable

instance compactAddDualMeasurableNeg (E : CayleyExtraction S) :
    MeasurableNeg E.CompactAddDual where
  measurable_neg := continuous_neg.measurable

instance compactAddDualMeasurableSub₂ (E : CayleyExtraction S) :
    MeasurableSub₂ E.CompactAddDual where
  measurable_sub := continuous_sub.measurable

/-- Normalized additive Haar probability measure on the compact additive dual. -/
noncomputable def haar (E : CayleyExtraction S) :
    MeasureTheory.Measure E.CompactAddDual :=
  MeasureTheory.Measure.addHaarMeasure
    (⊤ : TopologicalSpace.PositiveCompacts E.CompactAddDual)

instance haar_isAddHaarMeasure (E : CayleyExtraction S) :
    (E.haar).IsAddHaarMeasure := by
  unfold haar
  infer_instance

instance haar_isOpenPosMeasure (E : CayleyExtraction S) :
    (E.haar).IsOpenPosMeasure :=
  inferInstance

instance haar_isProbabilityMeasure (E : CayleyExtraction S) :
    MeasureTheory.IsProbabilityMeasure E.haar where
  measure_univ := by
    unfold haar
    simpa using
      (MeasureTheory.Measure.addHaarMeasure_self
        (K₀ := (⊤ : TopologicalSpace.PositiveCompacts E.CompactAddDual)))

end CayleyExtraction

end

end Erdos42.CompactCayley


/-! =============================================================
    Section from: Erdos/P42/CompactCayley/Characters.lean
    ============================================================= -/

/-
Erdős Problem 42 — characters on the compact-Cayley compact dual.
-/


namespace Erdos42.CompactCayley

open MeasureTheory
open scoped ComplexConjugate Topology

noncomputable section

/-- The rational character module target `ℚ / ℤ`, embedded in the usual unit
circle. -/
noncomputable def ratAddCircleToCircleAdditive :
    AddCircle (1 : ℚ) →+ Additive Circle := by
  let f : ℚ →+ Additive Circle :=
    { toFun := fun q =>
        Additive.ofMul
          (AddCircle.toCircle (((q : ℝ) : AddCircle (1 : ℝ))))
      map_zero' := by
        simp
      map_add' := by
        intro a b
        ext
        simp [Rat.cast_add, AddCircle.toCircle_add] }
  refine QuotientAddGroup.lift (AddSubgroup.zmultiples (1 : ℚ)) f ?_
  intro x hx
  obtain ⟨k, rfl⟩ := AddSubgroup.mem_zmultiples_iff.mp hx
  change
    Additive.ofMul
        (AddCircle.toCircle
          ((((k • (1 : ℚ) : ℚ) : ℝ) : AddCircle (1 : ℝ)))) = 0
  rw [ofMul_eq_zero]
  have hzero :
      (((k : ℝ) : AddCircle (1 : ℝ))) = 0 := by
    rw [AddCircle.coe_eq_zero_iff]
    exact ⟨k, by simp⟩
  simpa using congrArg (fun y : AddCircle (1 : ℝ) => AddCircle.toCircle y) hzero

lemma ratAddCircleToCircleAdditive_eq_zero
    {x : AddCircle (1 : ℚ)}
    (hx : ratAddCircleToCircleAdditive x = 0) :
    x = 0 := by
  induction x using QuotientAddGroup.induction_on with
  | H q =>
      change ratAddCircleToCircleAdditive ((q : AddCircle (1 : ℚ))) = 0 at hx
      have hcircle :
          AddCircle.toCircle (((q : ℝ) : AddCircle (1 : ℝ))) = 1 := by
        have hx' :
            Additive.ofMul
              (AddCircle.toCircle (((q : ℝ) : AddCircle (1 : ℝ)))) = 0 := by
          simpa [ratAddCircleToCircleAdditive] using hx
        exact ofMul_eq_zero.mp hx'
      have hreal :
          (((q : ℝ) : AddCircle (1 : ℝ))) = 0 :=
        (AddCircle.injective_toCircle (T := (1 : ℝ)) one_ne_zero)
          (by simpa using hcircle)
      rw [AddCircle.coe_eq_zero_iff] at hreal ⊢
      rcases hreal with ⟨k, hk⟩
      refine ⟨k, ?_⟩
      apply Rat.cast_injective (α := ℝ)
      simpa using hk

namespace CayleyExtraction

variable {ℓ : ℕ} {η : ℝ} {S : CayleyCounterSeq ℓ η}

/-- Evaluation of a compact-dual character at an extraction quotient
frequency, viewed in `ℂ`. -/
noncomputable def characterValue
    (E : CayleyExtraction S) (z : E.CompactDual) (γ : E.Group) : ℂ :=
  (z (Multiplicative.ofAdd γ) : ℂ)

/-- Character evaluation on the additive compact-dual wrapper. -/
noncomputable def addCharacterValue
    (E : CayleyExtraction S) (z : E.CompactAddDual) (γ : E.Group) : ℂ :=
  E.characterValue z.toMul γ

@[simp]
lemma characterValue_zero
    (E : CayleyExtraction S) (z : E.CompactDual) :
    E.characterValue z (0 : E.Group) = 1 := by
  simp [characterValue]

@[simp]
lemma characterValue_add
    (E : CayleyExtraction S) (z : E.CompactDual)
    (γ δ : E.Group) :
    E.characterValue z (γ + δ) =
      E.characterValue z γ * E.characterValue z δ := by
  simp [characterValue]

@[simp]
lemma characterValue_neg
    (E : CayleyExtraction S) (z : E.CompactDual) (γ : E.Group) :
    E.characterValue z (-γ) = (E.characterValue z γ)⁻¹ := by
  simp [characterValue]

@[simp]
lemma star_characterValue
    (E : CayleyExtraction S) (z : E.CompactDual) (γ : E.Group) :
    star (E.characterValue z γ) = E.characterValue z (-γ) := by
  unfold characterValue
  rw [show star (↑(z (Multiplicative.ofAdd γ)) : ℂ) =
      conj (↑(z (Multiplicative.ofAdd γ)) : ℂ) by rfl]
  rw [← Circle.coe_inv_eq_conj]
  simp

lemma characterValue_sub
    (E : CayleyExtraction S) (z : E.CompactDual)
    (γ δ : E.Group) :
    E.characterValue z (γ - δ) =
      E.characterValue z γ * star (E.characterValue z δ) := by
  rw [sub_eq_add_neg, characterValue_add, star_characterValue]

@[simp]
lemma characterValue_one_point
    (E : CayleyExtraction S) (γ : E.Group) :
    E.characterValue (1 : E.CompactDual) γ = 1 := by
  rfl

@[simp]
lemma characterValue_mul_point
    (E : CayleyExtraction S) (z w : E.CompactDual) (γ : E.Group) :
    E.characterValue (z * w) γ =
      E.characterValue z γ * E.characterValue w γ := by
  rfl

@[simp]
lemma characterValue_inv_point
    (E : CayleyExtraction S) (z : E.CompactDual) (γ : E.Group) :
    E.characterValue z⁻¹ γ = (E.characterValue z γ)⁻¹ := by
  rfl

@[simp]
lemma addCharacterValue_zero
    (E : CayleyExtraction S) (z : E.CompactAddDual) :
    E.addCharacterValue z (0 : E.Group) = 1 := by
  simp [addCharacterValue]

@[simp]
lemma addCharacterValue_add
    (E : CayleyExtraction S) (z : E.CompactAddDual)
    (γ δ : E.Group) :
    E.addCharacterValue z (γ + δ) =
      E.addCharacterValue z γ * E.addCharacterValue z δ := by
  simp [addCharacterValue]

@[simp]
lemma addCharacterValue_neg
    (E : CayleyExtraction S) (z : E.CompactAddDual) (γ : E.Group) :
    E.addCharacterValue z (-γ) = (E.addCharacterValue z γ)⁻¹ := by
  simp [addCharacterValue]

@[simp]
lemma star_addCharacterValue
    (E : CayleyExtraction S) (z : E.CompactAddDual) (γ : E.Group) :
    star (E.addCharacterValue z γ) = E.addCharacterValue z (-γ) := by
  simp [addCharacterValue, star_characterValue]

lemma addCharacterValue_sub
    (E : CayleyExtraction S) (z : E.CompactAddDual)
    (γ δ : E.Group) :
    E.addCharacterValue z (γ - δ) =
      E.addCharacterValue z γ * star (E.addCharacterValue z δ) := by
  simpa [addCharacterValue] using E.characterValue_sub z.toMul γ δ

@[simp]
lemma addCharacterValue_zero_point
    (E : CayleyExtraction S) (γ : E.Group) :
    E.addCharacterValue (0 : E.CompactAddDual) γ = 1 := by
  simp [addCharacterValue]

@[simp]
lemma addCharacterValue_add_point
    (E : CayleyExtraction S) (z w : E.CompactAddDual) (γ : E.Group) :
    E.addCharacterValue (z + w) γ =
      E.addCharacterValue z γ * E.addCharacterValue w γ := by
  simp [addCharacterValue]

lemma addCharacterValue_nsmul_frequency
    (E : CayleyExtraction S) (z : E.CompactAddDual)
    (γ : E.Group) (n : ℕ) :
    E.addCharacterValue z (n • γ) =
      (E.addCharacterValue z γ) ^ n := by
  induction n with
  | zero =>
      simp
  | succ n ih =>
      rw [succ_nsmul, E.addCharacterValue_add, ih, pow_succ]

lemma addCharacterValue_nsmul_point
    (E : CayleyExtraction S) (z : E.CompactAddDual)
    (γ : E.Group) (n : ℕ) :
    E.addCharacterValue (n • z) γ =
      (E.addCharacterValue z γ) ^ n := by
  induction n with
  | zero =>
      simp
  | succ n ih =>
      rw [succ_nsmul, E.addCharacterValue_add_point, ih, pow_succ]

@[simp]
lemma addCharacterValue_neg_point
    (E : CayleyExtraction S) (z : E.CompactAddDual) (γ : E.Group) :
    E.addCharacterValue (-z) γ = (E.addCharacterValue z γ)⁻¹ := by
  simp [addCharacterValue]

@[simp]
lemma norm_characterValue
    (E : CayleyExtraction S) (z : E.CompactDual) (γ : E.Group) :
    ‖E.characterValue z γ‖ = 1 :=
  Circle.norm_coe _

@[simp]
lemma norm_addCharacterValue
    (E : CayleyExtraction S) (z : E.CompactAddDual) (γ : E.Group) :
    ‖E.addCharacterValue z γ‖ = 1 := by
  simp [addCharacterValue]

lemma characterValue_continuous
    (E : CayleyExtraction S) (γ : E.Group) :
    Continuous (fun z : E.CompactDual => E.characterValue z γ) := by
  change Continuous (fun z : E.DualDomain →ₜ* Circle =>
    ((z.toContinuousMap (Multiplicative.ofAdd γ) : Circle) : ℂ))
  exact
    (continuous_subtype_val.comp
      ((continuous_eval_const (F := C(E.DualDomain, Circle))
        (Multiplicative.ofAdd γ)).comp
          (ContinuousMonoidHom.isInducing_toContinuousMap
            E.DualDomain Circle).continuous))

lemma addCharacterValue_continuous
    (E : CayleyExtraction S) (γ : E.Group) :
    Continuous (fun z : E.CompactAddDual => E.addCharacterValue z γ) := by
  change Continuous (fun z : E.CompactAddDual => E.characterValue z.toMul γ)
  exact
    (E.characterValue_continuous γ).comp
      (E.compactDualAdditiveHomeomorph.symm.continuous)

@[simp]
lemma integral_addCharacterValue_zero
    (E : CayleyExtraction S) :
    ∫ z : E.CompactAddDual,
        E.addCharacterValue z (0 : E.Group) ∂E.haar = 1 := by
  simp

/-- Haar orthogonality for a character once a point where it is nontrivial has
been supplied.  The separate Pontryagin-dual separation theorem should provide
this witness for every nonzero extraction frequency. -/
lemma integral_addCharacterValue_eq_zero_of_exists_ne_one
    (E : CayleyExtraction S) (γ : E.Group)
    (hne : ∃ y : E.CompactAddDual, E.addCharacterValue y γ ≠ 1) :
    ∫ z : E.CompactAddDual, E.addCharacterValue z γ ∂E.haar = 0 := by
  classical
  rcases hne with ⟨y, hy⟩
  let I : ℂ :=
    ∫ z : E.CompactAddDual, E.addCharacterValue z γ ∂E.haar
  have htrans :
      (∫ z : E.CompactAddDual,
          E.addCharacterValue (y + z) γ ∂E.haar) = I := by
    simpa [I] using
      (integral_add_left_eq_self
        (μ := E.haar)
        (fun z : E.CompactAddDual => E.addCharacterValue z γ) y)
  have hleft :
      (∫ z : E.CompactAddDual,
          E.addCharacterValue (y + z) γ ∂E.haar) =
        E.addCharacterValue y γ * I := by
    simp_rw [E.addCharacterValue_add_point y]
    simpa [I] using
      (integral_const_mul (μ := E.haar) (E.addCharacterValue y γ)
        (fun z : E.CompactAddDual => E.addCharacterValue z γ))
  have hscalar : E.addCharacterValue y γ * I = I := by
    rw [← hleft, htrans]
  have hzero : (E.addCharacterValue y γ - 1) * I = 0 := by
    calc
      (E.addCharacterValue y γ - 1) * I =
          E.addCharacterValue y γ * I - I := by ring
      _ = I - I := by rw [hscalar]
      _ = 0 := by ring
  have hfactor : E.addCharacterValue y γ - 1 ≠ 0 := sub_ne_zero.mpr hy
  exact (mul_eq_zero.mp hzero).resolve_left hfactor

lemma integral_addCharacterValue_eq_if_of_separating
    (E : CayleyExtraction S)
    (hsep :
      ∀ γ : E.Group, γ ≠ 0 →
        ∃ y : E.CompactAddDual, E.addCharacterValue y γ ≠ 1)
    (γ : E.Group) :
    ∫ z : E.CompactAddDual, E.addCharacterValue z γ ∂E.haar =
      if γ = 0 then 1 else 0 := by
  by_cases hγ : γ = 0
  · subst γ
    simp
  · simp [hγ, E.integral_addCharacterValue_eq_zero_of_exists_ne_one γ (hsep γ hγ)]

lemma exists_dual_point_ne_one
    (E : CayleyExtraction S) {γ : E.Group} (hγ : γ ≠ 0) :
    ∃ y : E.CompactAddDual, E.addCharacterValue y γ ≠ 1 := by
  classical
  obtain ⟨c, hc⟩ :=
    CharacterModule.exists_character_apply_ne_zero_of_ne_zero
      (A := E.Group) (a := γ) hγ
  let ψ : E.Group →+ Additive Circle :=
    ratAddCircleToCircleAdditive.comp c
  have hψ : ψ γ ≠ 0 := by
    intro hzero
    exact hc (ratAddCircleToCircleAdditive_eq_zero hzero)
  let mψ : E.DualDomain →* Circle :=
    AddMonoidHom.toMultiplicativeLeft ψ
  let z : E.CompactDual :=
    { toMonoidHom := mψ
      continuous_toFun := continuous_of_discreteTopology }
  refine ⟨Additive.ofMul z, ?_⟩
  intro htriv
  have hcoe :
      ((mψ (Multiplicative.ofAdd γ) : Circle) : ℂ) = 1 := by
    change ((z (Multiplicative.ofAdd γ) : Circle) : ℂ) = 1
    simpa [addCharacterValue, characterValue] using htriv
  have hmψ : mψ (Multiplicative.ofAdd γ) = 1 := by
    exact Subtype.ext hcoe
  have hcircle : (ψ γ).toMul = 1 := by
    simpa [mψ, AddMonoidHom.coe_toMultiplicativeLeft] using hmψ
  exact hψ (toMul_eq_one.mp hcircle)

lemma integral_addCharacterValue
    (E : CayleyExtraction S) (γ : E.Group) :
    ∫ z : E.CompactAddDual, E.addCharacterValue z γ ∂E.haar =
      if γ = 0 then 1 else 0 :=
  E.integral_addCharacterValue_eq_if_of_separating
    (fun _ hγ => E.exists_dual_point_ne_one hγ) γ

end CayleyExtraction

end

end Erdos42.CompactCayley


/-! =============================================================
    Section from: Erdos/P42/CompactCayley/TrigPolynomial.lean
    ============================================================= -/

/-
Erdős Problem 42 — trigonometric polynomials for compact-Cayley extraction.

This is the finite-support Fourier-polynomial interface on the extraction
quotient, together with finite cyclic lifts and the zero-frequency finite
average convergence that follows from relation-stable quotient lifts.
-/


namespace Erdos42.CompactCayley

open Filter Complex MeasureTheory
open scoped BigOperators ComplexConjugate Topology

noncomputable section

namespace CayleyExtraction

variable {ℓ : ℕ} {η : ℝ} {S : CayleyCounterSeq ℓ η}

/-- Finitely supported Fourier polynomials on the extraction quotient. -/
abbrev TrigPoly (E : CayleyExtraction S) : Type :=
  E.Group →₀ ℂ

/-- Compact-dual evaluation of an extraction trigonometric polynomial. -/
noncomputable def TrigPoly.eval
    {E : CayleyExtraction S} (P : E.TrigPoly) (z : E.CompactDual) : ℂ :=
  P.sum fun γ c => c * E.characterValue z γ

/-- Additive-wrapper compact-dual evaluation. -/
noncomputable def TrigPoly.evalAdd
    {E : CayleyExtraction S} (P : E.TrigPoly) (z : E.CompactAddDual) : ℂ :=
  P.sum fun γ c => c * E.addCharacterValue z γ

/-- Finite cyclic lift of a trigonometric polynomial. -/
noncomputable def TrigPoly.evalFinite
    {E : CayleyExtraction S} (P : E.TrigPoly) (n : ℕ)
    (x : ZMod (S.p (E.φ n))) : ℂ :=
  letI : NeZero (S.p (E.φ n)) := ⟨(S.prime (E.φ n)).ne_zero⟩
  P.sum fun γ c => c * ZMod.stdAddChar (-(E.lift n γ * x))

/-- Normalized finite average of a lifted trigonometric polynomial. -/
noncomputable def TrigPoly.finiteAverage
    {E : CayleyExtraction S} (P : E.TrigPoly) (n : ℕ) : ℂ :=
  letI : NeZero (S.p (E.φ n)) := ⟨(S.prime (E.φ n)).ne_zero⟩
  avgZMod fun x : ZMod (S.p (E.φ n)) => P.evalFinite n x

/-- Finite average of a lifted trigonometric polynomial against the Cayley-set
indicator. -/
noncomputable def TrigPoly.indicatorWeightedFiniteAverage
    {E : CayleyExtraction S} (P : E.TrigPoly) (n : ℕ) : ℂ :=
  letI : NeZero (S.p (E.φ n)) := ⟨(S.prime (E.φ n)).ne_zero⟩
  avgZMod fun x : ZMod (S.p (E.φ n)) =>
    indicatorC (S.T (E.φ n)) x * P.evalFinite n x

/-- Abstract compact average, represented algebraically by the zero-frequency
coefficient. -/
noncomputable def TrigPoly.compactAverage
    {E : CayleyExtraction S} (P : E.TrigPoly) : ℂ :=
  P (0 : E.Group)

/-- Compact-limit coefficient functional obtained by pairing a trigonometric
polynomial with the extracted Cayley Fourier coefficient limits. -/
noncomputable def TrigPoly.indicatorCoeffFunctional
    {E : CayleyExtraction S} (P : E.TrigPoly) : ℂ :=
  P.sum fun γ c => c * E.coeff γ

lemma TrigPoly.evalAdd_eq_eval
    {E : CayleyExtraction S} (P : E.TrigPoly) (z : E.CompactAddDual) :
    TrigPoly.evalAdd P z = TrigPoly.eval P z.toMul := by
  rfl

lemma TrigPoly.eval_add
    {E : CayleyExtraction S} (P Q : E.TrigPoly) (z : E.CompactDual) :
    TrigPoly.eval (P + Q) z =
      TrigPoly.eval P z + TrigPoly.eval Q z := by
  unfold TrigPoly.eval
  let h : E.Group → ℂ →+ ℂ := fun γ =>
    { toFun := fun c => c * E.characterValue z γ
      map_zero' := by simp
      map_add' := by intro a b; ring }
  change Finsupp.sum (P + Q) (fun γ c => h γ c) =
    Finsupp.sum P (fun γ c => h γ c) +
      Finsupp.sum Q (fun γ c => h γ c)
  rw [Finsupp.sum_hom_add_index]

lemma TrigPoly.evalAdd_add
    {E : CayleyExtraction S} (P Q : E.TrigPoly) (z : E.CompactAddDual) :
    TrigPoly.evalAdd (P + Q) z =
      TrigPoly.evalAdd P z + TrigPoly.evalAdd Q z := by
  simpa [TrigPoly.evalAdd_eq_eval] using
    TrigPoly.eval_add P Q z.toMul

@[simp]
lemma TrigPoly.eval_zero
    {E : CayleyExtraction S} (z : E.CompactDual) :
    TrigPoly.eval (0 : E.TrigPoly) z = 0 := by
  simp [TrigPoly.eval]

@[simp]
lemma TrigPoly.evalAdd_zero
    {E : CayleyExtraction S} (z : E.CompactAddDual) :
    TrigPoly.evalAdd (0 : E.TrigPoly) z = 0 := by
  simp [TrigPoly.evalAdd_eq_eval]

@[simp]
lemma TrigPoly.eval_single
    {E : CayleyExtraction S} (γ : E.Group) (c : ℂ)
    (z : E.CompactDual) :
    TrigPoly.eval (Finsupp.single γ c : E.TrigPoly) z =
      c * E.characterValue z γ := by
  simp [TrigPoly.eval]

@[simp]
lemma TrigPoly.evalAdd_single
    {E : CayleyExtraction S} (γ : E.Group) (c : ℂ)
    (z : E.CompactAddDual) :
    TrigPoly.evalAdd (Finsupp.single γ c : E.TrigPoly) z =
      c * E.addCharacterValue z γ := by
  simp [TrigPoly.evalAdd]

@[simp]
lemma TrigPoly.eval_single_zero
    {E : CayleyExtraction S} (c : ℂ) (z : E.CompactDual) :
    TrigPoly.eval
        (Finsupp.single (0 : E.Group) c : E.TrigPoly) z = c := by
  simp

@[simp]
lemma TrigPoly.evalAdd_single_zero
    {E : CayleyExtraction S} (c : ℂ) (z : E.CompactAddDual) :
    TrigPoly.evalAdd
        (Finsupp.single (0 : E.Group) c : E.TrigPoly) z = c := by
  simp

lemma TrigPoly.continuous_eval
    (E : CayleyExtraction S) (P : E.TrigPoly) :
    Continuous (fun z : E.CompactDual => TrigPoly.eval P z) := by
  refine Finsupp.induction_linear P ?zero ?add ?single
  · simpa using (continuous_const :
      Continuous (fun _ : E.CompactDual => (0 : ℂ)))
  · intro P Q hP hQ
    rw [show
        (fun z : E.CompactDual => TrigPoly.eval (P + Q) z) =
          fun z => TrigPoly.eval P z + TrigPoly.eval Q z by
        funext z
        exact TrigPoly.eval_add P Q z]
    exact hP.add hQ
  · intro γ c
    rw [show
        (fun z : E.CompactDual =>
            TrigPoly.eval (Finsupp.single γ c : E.TrigPoly) z) =
          fun z => c * E.characterValue z γ by
        funext z
        exact TrigPoly.eval_single γ c z]
    exact continuous_const.mul (E.characterValue_continuous γ)

lemma TrigPoly.continuous_evalAdd
    (E : CayleyExtraction S) (P : E.TrigPoly) :
    Continuous (fun z : E.CompactAddDual => TrigPoly.evalAdd P z) := by
  refine Finsupp.induction_linear P ?zero ?add ?single
  · simpa using (continuous_const :
      Continuous (fun _ : E.CompactAddDual => (0 : ℂ)))
  · intro P Q hP hQ
    rw [show
        (fun z : E.CompactAddDual => TrigPoly.evalAdd (P + Q) z) =
          fun z => TrigPoly.evalAdd P z + TrigPoly.evalAdd Q z by
        funext z
        exact TrigPoly.evalAdd_add P Q z]
    exact hP.add hQ
  · intro γ c
    rw [show
        (fun z : E.CompactAddDual =>
            TrigPoly.evalAdd (Finsupp.single γ c : E.TrigPoly) z) =
          fun z => c * E.addCharacterValue z γ by
        funext z
        exact TrigPoly.evalAdd_single γ c z]
    exact continuous_const.mul (E.addCharacterValue_continuous γ)

lemma TrigPoly.integrable_evalAdd
    (E : CayleyExtraction S) (P : E.TrigPoly) :
    Integrable (fun z : E.CompactAddDual => TrigPoly.evalAdd P z) E.haar :=
  (TrigPoly.continuous_evalAdd E P).integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)

lemma TrigPoly.integral_evalAdd_eq_compactAverage
    (E : CayleyExtraction S) (P : E.TrigPoly) :
    ∫ z : E.CompactAddDual, TrigPoly.evalAdd P z ∂E.haar =
      TrigPoly.compactAverage P := by
  refine Finsupp.induction_linear P ?zero ?add ?single
  · simp [TrigPoly.compactAverage]
  · intro P Q hP hQ
    rw [show
        (fun z : E.CompactAddDual => TrigPoly.evalAdd (P + Q) z) =
          fun z => TrigPoly.evalAdd P z + TrigPoly.evalAdd Q z by
        funext z
        exact TrigPoly.evalAdd_add P Q z]
    rw [integral_add (TrigPoly.integrable_evalAdd E P)
      (TrigPoly.integrable_evalAdd E Q), hP, hQ]
    simp [TrigPoly.compactAverage]
  · intro γ c
    by_cases hγ : γ = 0
    · subst γ
      simp [TrigPoly.compactAverage]
    · rw [show
          (fun z : E.CompactAddDual =>
              TrigPoly.evalAdd (Finsupp.single γ c : E.TrigPoly) z) =
            fun z => c * E.addCharacterValue z γ by
          funext z
          simp]
      rw [show
          (∫ z : E.CompactAddDual, c * E.addCharacterValue z γ ∂E.haar) =
            c * ∫ z : E.CompactAddDual, E.addCharacterValue z γ ∂E.haar by
        simpa using
          (integral_const_mul (μ := E.haar) c
            (fun z : E.CompactAddDual => E.addCharacterValue z γ))]
      rw [E.integral_addCharacterValue]
      simp [hγ, TrigPoly.compactAverage, Finsupp.single_eq_of_ne (Ne.symm hγ)]

lemma TrigPoly.integrable_evalAdd_mul_char
    (E : CayleyExtraction S) (P : E.TrigPoly) (γ : E.Group) :
    Integrable
      (fun z : E.CompactAddDual =>
        TrigPoly.evalAdd P z * E.addCharacterValue z γ) E.haar :=
  ((TrigPoly.continuous_evalAdd E P).mul
      (E.addCharacterValue_continuous γ)).integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)

lemma TrigPoly.integral_evalAdd_mul_char
    (E : CayleyExtraction S) (P : E.TrigPoly) (γ : E.Group) :
    ∫ z : E.CompactAddDual,
        TrigPoly.evalAdd P z * E.addCharacterValue z γ ∂E.haar =
      P (-γ) := by
  refine Finsupp.induction_linear P ?zero ?add ?single
  · simp
  · intro P Q hP hQ
    rw [show
        (fun z : E.CompactAddDual =>
            TrigPoly.evalAdd (P + Q) z * E.addCharacterValue z γ) =
          fun z =>
            TrigPoly.evalAdd P z * E.addCharacterValue z γ +
              TrigPoly.evalAdd Q z * E.addCharacterValue z γ by
        funext z
        rw [TrigPoly.evalAdd_add]
        ring]
    rw [integral_add (TrigPoly.integrable_evalAdd_mul_char E P γ)
      (TrigPoly.integrable_evalAdd_mul_char E Q γ), hP, hQ]
    simp
  · intro δ c
    rw [show
        (fun z : E.CompactAddDual =>
            TrigPoly.evalAdd (Finsupp.single δ c : E.TrigPoly) z *
              E.addCharacterValue z γ) =
          fun z => c * E.addCharacterValue z (δ + γ) by
        funext z
        simp only [TrigPoly.evalAdd_single]
        rw [mul_assoc]
        rw [← E.addCharacterValue_add]]
    rw [show
        (∫ z : E.CompactAddDual, c * E.addCharacterValue z (δ + γ) ∂E.haar) =
          c * ∫ z : E.CompactAddDual, E.addCharacterValue z (δ + γ) ∂E.haar by
      simpa using
        (integral_const_mul (μ := E.haar) c
          (fun z : E.CompactAddDual => E.addCharacterValue z (δ + γ)))]
    rw [E.integral_addCharacterValue]
    by_cases hδγ : δ + γ = 0
    · have hδ : δ = -γ := by
        exact eq_neg_of_add_eq_zero_left hδγ
      subst δ
      simp
    · have hδ : δ ≠ -γ := by
        intro h
        subst h
        exact hδγ (by simp)
      rw [Finsupp.single_eq_of_ne (Ne.symm hδ)]
      simp [hδγ]

lemma TrigPoly.integral_evalAdd_eq_compactAverage_of_separating
    (E : CayleyExtraction S)
    (_hsep :
      ∀ γ : E.Group, γ ≠ 0 →
        ∃ y : E.CompactAddDual, E.addCharacterValue y γ ≠ 1)
    (P : E.TrigPoly) :
    ∫ z : E.CompactAddDual, TrigPoly.evalAdd P z ∂E.haar =
      TrigPoly.compactAverage P :=
  TrigPoly.integral_evalAdd_eq_compactAverage E P

@[simp]
lemma TrigPoly.evalFinite_zero
    {E : CayleyExtraction S} (n : ℕ) (x : ZMod (S.p (E.φ n))) :
    TrigPoly.evalFinite (0 : E.TrigPoly) n x = 0 := by
  haveI : NeZero (S.p (E.φ n)) := ⟨(S.prime (E.φ n)).ne_zero⟩
  simp [TrigPoly.evalFinite]

@[simp]
lemma TrigPoly.evalFinite_single
    {E : CayleyExtraction S} (γ : E.Group) (c : ℂ)
    (n : ℕ) (x : ZMod (S.p (E.φ n))) :
    TrigPoly.evalFinite (Finsupp.single γ c : E.TrigPoly) n x =
      (letI : NeZero (S.p (E.φ n)) := ⟨(S.prime (E.φ n)).ne_zero⟩;
        c * ZMod.stdAddChar (-(E.lift n γ * x))) := by
  simp [TrigPoly.evalFinite]

lemma TrigPoly.evalFinite_add
    {E : CayleyExtraction S} (P Q : E.TrigPoly)
    (n : ℕ) (x : ZMod (S.p (E.φ n))) :
    TrigPoly.evalFinite (P + Q) n x =
      TrigPoly.evalFinite P n x + TrigPoly.evalFinite Q n x := by
  haveI : NeZero (S.p (E.φ n)) := ⟨(S.prime (E.φ n)).ne_zero⟩
  classical
  unfold TrigPoly.evalFinite
  let h : E.Group → ℂ →+ ℂ := fun γ =>
    { toFun := fun c => c * ZMod.stdAddChar (-(E.lift n γ * x))
      map_zero' := by simp
      map_add' := by intro a b; ring }
  change Finsupp.sum (P + Q) (fun γ c => h γ c) =
    Finsupp.sum P (fun γ c => h γ c) +
      Finsupp.sum Q (fun γ c => h γ c)
  rw [Finsupp.sum_hom_add_index]

lemma TrigPoly.finiteAverage_add
    {E : CayleyExtraction S} (P Q : E.TrigPoly) (n : ℕ) :
    TrigPoly.finiteAverage (P + Q) n =
      TrigPoly.finiteAverage P n + TrigPoly.finiteAverage Q n := by
  haveI : NeZero (S.p (E.φ n)) := ⟨(S.prime (E.φ n)).ne_zero⟩
  unfold TrigPoly.finiteAverage
  rw [show
      (fun x : ZMod (S.p (E.φ n)) =>
        TrigPoly.evalFinite (P + Q) n x) =
      (fun x : ZMod (S.p (E.φ n)) =>
        TrigPoly.evalFinite P n x + TrigPoly.evalFinite Q n x) by
        funext x
        exact TrigPoly.evalFinite_add P Q n x]
  unfold avgZMod
  rw [Finset.sum_add_distrib, mul_add]

lemma TrigPoly.indicatorWeightedFiniteAverage_add
    {E : CayleyExtraction S} (P Q : E.TrigPoly) (n : ℕ) :
    TrigPoly.indicatorWeightedFiniteAverage (P + Q) n =
      TrigPoly.indicatorWeightedFiniteAverage P n +
        TrigPoly.indicatorWeightedFiniteAverage Q n := by
  haveI : NeZero (S.p (E.φ n)) := ⟨(S.prime (E.φ n)).ne_zero⟩
  unfold TrigPoly.indicatorWeightedFiniteAverage
  rw [show
      (fun x : ZMod (S.p (E.φ n)) =>
        indicatorC (S.T (E.φ n)) x *
          TrigPoly.evalFinite (P + Q) n x) =
      (fun x : ZMod (S.p (E.φ n)) =>
        indicatorC (S.T (E.φ n)) x *
          TrigPoly.evalFinite P n x +
        indicatorC (S.T (E.φ n)) x *
          TrigPoly.evalFinite Q n x) by
        funext x
        rw [TrigPoly.evalFinite_add]
        ring]
  unfold avgZMod
  rw [Finset.sum_add_distrib, mul_add]

lemma avgZMod_stdAddChar_neg_mul_eq_zero_of_ne_zero
    {p : ℕ} [Fact p.Prime] [NeZero p] {r : ZMod p} (hr : r ≠ 0) :
    avgZMod (fun x : ZMod p => ZMod.stdAddChar (-(r * x))) = 0 := by
  unfold avgZMod
  rw [show (∑ x : ZMod p, ZMod.stdAddChar (-(r * x))) = 0 by
    simpa [mul_comm] using
      sum_stdAddChar_neg_mul_eq_zero_of_ne_zero (p := p) (r := r) hr]
  simp

lemma avgZMod_stdAddChar_neg_mul_eq_ite
    {p : ℕ} [Fact p.Prime] [NeZero p] (r : ZMod p) :
    avgZMod (fun x : ZMod p => ZMod.stdAddChar (-(r * x))) =
      if r = 0 then 1 else 0 := by
  by_cases hr : r = 0
  · subst r
    unfold avgZMod
    have hp : (p : ℂ) ≠ 0 := by exact_mod_cast (NeZero.ne p)
    simp [hp]
  · simp [hr, avgZMod_stdAddChar_neg_mul_eq_zero_of_ne_zero hr]

lemma avgZMod_const {p : ℕ} [NeZero p] (c : ℂ) :
    avgZMod (fun _ : ZMod p => c) = c := by
  unfold avgZMod
  have hp : (p : ℂ) ≠ 0 := by exact_mod_cast (NeZero.ne p)
  simp [hp]

lemma normalizedDftFunction_eq_avgZMod {p : ℕ} [NeZero p]
    (f : ZMod p → ℂ) (r : ZMod p) :
    normalizedDftFunction f r =
      avgZMod fun x : ZMod p => ZMod.stdAddChar (-(x * r)) * f x := by
  rw [normalizedDftFunction_eq_sum]
  rfl

lemma TrigPoly.finiteAverage_single_eq_coeff_of_lift_eq_zero
    {E : CayleyExtraction S} (γ : E.Group) (c : ℂ) (n : ℕ)
    (hγ : E.lift n γ = 0) :
    TrigPoly.finiteAverage (Finsupp.single γ c : E.TrigPoly) n = c := by
  haveI : NeZero (S.p (E.φ n)) := ⟨(S.prime (E.φ n)).ne_zero⟩
  rw [TrigPoly.finiteAverage]
  simp [TrigPoly.evalFinite_single, hγ, avgZMod_const]

lemma TrigPoly.finiteAverage_single_eq_zero_of_lift_ne_zero
    {E : CayleyExtraction S} (γ : E.Group) (c : ℂ) (n : ℕ)
    (hγ : E.lift n γ ≠ 0) :
    TrigPoly.finiteAverage (Finsupp.single γ c : E.TrigPoly) n = 0 := by
  haveI : Fact (S.p (E.φ n)).Prime := ⟨S.prime (E.φ n)⟩
  haveI : NeZero (S.p (E.φ n)) := ⟨(S.prime (E.φ n)).ne_zero⟩
  rw [TrigPoly.finiteAverage]
  simp [TrigPoly.evalFinite_single, avgZMod_const_mul,
    avgZMod_stdAddChar_neg_mul_eq_zero_of_ne_zero hγ]

lemma TrigPoly.normalizedDftFunction_evalFinite_single
    {E : CayleyExtraction S} (γ : E.Group) (c : ℂ) (n : ℕ)
    [Fact (S.p (E.φ n)).Prime] [NeZero (S.p (E.φ n))]
    (r : ZMod (S.p (E.φ n))) :
    normalizedDftFunction
        (fun x : ZMod (S.p (E.φ n)) =>
          TrigPoly.evalFinite (Finsupp.single γ c : E.TrigPoly) n x) r =
      if r + E.lift n γ = 0 then c else 0 := by
  rw [normalizedDftFunction_eq_avgZMod]
  simp only [TrigPoly.evalFinite_single]
  calc
    avgZMod
        (fun x : ZMod (S.p (E.φ n)) =>
          ZMod.stdAddChar (-(x * r)) *
            (c * ZMod.stdAddChar (-(E.lift n γ * x))))
        =
      avgZMod
        (fun x : ZMod (S.p (E.φ n)) =>
          c * ZMod.stdAddChar (-((r + E.lift n γ) * x))) := by
          congr 1
          funext x
          calc
            ZMod.stdAddChar (-(x * r)) *
                (c * ZMod.stdAddChar (-(E.lift n γ * x)))
                =
              c * (ZMod.stdAddChar (-(x * r)) *
                ZMod.stdAddChar (-(E.lift n γ * x))) := by
                ring
            _ =
              c * ZMod.stdAddChar (-((r + E.lift n γ) * x)) := by
                congr 1
                rw [← ZMod.stdAddChar.map_add_eq_mul]
                congr 1
                ring
    _ =
      c * avgZMod
        (fun x : ZMod (S.p (E.φ n)) =>
          ZMod.stdAddChar (-((r + E.lift n γ) * x))) := by
          rw [avgZMod_const_mul]
    _ = if r + E.lift n γ = 0 then c else 0 := by
          rw [avgZMod_stdAddChar_neg_mul_eq_ite]
          by_cases h : r + E.lift n γ = 0 <;> simp [h]

lemma TrigPoly.indicatorWeightedFiniteAverage_single
    {E : CayleyExtraction S} (γ : E.Group) (c : ℂ) (n : ℕ) :
    TrigPoly.indicatorWeightedFiniteAverage
        (Finsupp.single γ c : E.TrigPoly) n =
      (letI : NeZero (S.p (E.φ n)) := ⟨(S.prime (E.φ n)).ne_zero⟩;
        c * normalizedDftCoeff (S.T (E.φ n)) (E.lift n γ)) := by
  haveI : NeZero (S.p (E.φ n)) := ⟨(S.prime (E.φ n)).ne_zero⟩
  unfold TrigPoly.indicatorWeightedFiniteAverage
  change avgZMod
      (fun x : ZMod (S.p (E.φ n)) =>
        indicatorC (S.T (E.φ n)) x *
          TrigPoly.evalFinite
            (Finsupp.single γ c : E.TrigPoly) n x) =
    c * normalizedDftCoeff (S.T (E.φ n)) (E.lift n γ)
  rw [show
      (fun x : ZMod (S.p (E.φ n)) =>
        indicatorC (S.T (E.φ n)) x *
          TrigPoly.evalFinite
            (Finsupp.single γ c : E.TrigPoly) n x) =
      (fun x : ZMod (S.p (E.φ n)) =>
        c * (ZMod.stdAddChar (-(x * E.lift n γ)) *
          indicatorC (S.T (E.φ n)) x)) by
        funext x
        simp [TrigPoly.evalFinite_single]
        ring_nf]
  rw [avgZMod_const_mul]
  congr 1

lemma TrigPoly.indicatorCoeffFunctional_add
    {E : CayleyExtraction S} (P Q : E.TrigPoly) :
    TrigPoly.indicatorCoeffFunctional (P + Q) =
      TrigPoly.indicatorCoeffFunctional P +
        TrigPoly.indicatorCoeffFunctional Q := by
  unfold TrigPoly.indicatorCoeffFunctional
  let h : E.Group → ℂ →+ ℂ := fun γ =>
    { toFun := fun c => c * E.coeff γ
      map_zero' := by simp
      map_add' := by intro a b; ring }
  change Finsupp.sum (P + Q) (fun γ c => h γ c) =
    Finsupp.sum P (fun γ c => h γ c) +
      Finsupp.sum Q (fun γ c => h γ c)
  rw [Finsupp.sum_hom_add_index]

@[simp]
lemma TrigPoly.indicatorCoeffFunctional_zero
    {E : CayleyExtraction S} :
    TrigPoly.indicatorCoeffFunctional (0 : E.TrigPoly) = 0 := by
  simp [TrigPoly.indicatorCoeffFunctional]

lemma TrigPoly.indicatorCoeffFunctional_single
    {E : CayleyExtraction S} (γ : E.Group) (c : ℂ) :
    TrigPoly.indicatorCoeffFunctional
        (Finsupp.single γ c : E.TrigPoly) =
      c * E.coeff γ := by
  simp [TrigPoly.indicatorCoeffFunctional]

lemma TrigPoly.normalizedDftFunction_evalFinite
    {E : CayleyExtraction S} (P : E.TrigPoly) (n : ℕ)
    [Fact (S.p (E.φ n)).Prime] [NeZero (S.p (E.φ n))]
    (r : ZMod (S.p (E.φ n))) :
    normalizedDftFunction
        (fun x : ZMod (S.p (E.φ n)) =>
          TrigPoly.evalFinite P n x) r =
      P.sum fun γ c => if r + E.lift n γ = 0 then c else 0 := by
  classical
  refine Finsupp.induction_linear P ?zero ?add ?single
  · simp [normalizedDftFunction_zero_fun]
  · intro P Q hP hQ
    have hfun :
      (fun x : ZMod (S.p (E.φ n)) =>
          TrigPoly.evalFinite (P + Q) n x) =
        fun x =>
          TrigPoly.evalFinite P n x + TrigPoly.evalFinite Q n x := by
      funext x
      exact TrigPoly.evalFinite_add P Q n x
    rw [hfun]
    rw [normalizedDftFunction_add, hP, hQ]
    let h : E.Group → ℂ →+ ℂ := fun γ =>
      { toFun := fun c => if r + E.lift n γ = 0 then c else 0
        map_zero' := by by_cases hγ : r + E.lift n γ = 0 <;> simp [hγ]
        map_add' := by
          intro a b
          by_cases hγ : r + E.lift n γ = 0 <;> simp [hγ] }
    change Finsupp.sum P (fun γ c => h γ c) +
        Finsupp.sum Q (fun γ c => h γ c) =
      Finsupp.sum (P + Q) (fun γ c => h γ c)
    rw [Finsupp.sum_hom_add_index]
  · intro γ c
    simpa using TrigPoly.normalizedDftFunction_evalFinite_single
      (E := E) γ c n r

lemma TrigPoly.sum_if_neg_lift_add_eq_zero_eq_apply_of_injOn
    {E : CayleyExtraction S} (P : E.TrigPoly) (n : ℕ)
    (γ : E.Group)
    (hinj :
      Set.InjOn
        (fun δ : E.Group => E.lift n δ)
        {δ : E.Group | δ ∈ insert γ P.support}) :
    P.sum (fun δ c =>
        if -E.lift n γ + E.lift n δ = 0 then c else 0) =
      P γ := by
  classical
  unfold Finsupp.sum
  rw [Finset.sum_eq_single γ]
  · simp
  · intro δ hδ hδγ
    have hnot : ¬ (-E.lift n γ + E.lift n δ = 0) := by
      intro hzero
      have heq : E.lift n δ = E.lift n γ := by
        have h := congrArg (fun z : ZMod (S.p (E.φ n)) => z + E.lift n γ) hzero
        simpa [add_comm, add_left_comm, add_assoc] using h
      exact hδγ (hinj
        (Finset.mem_insert.mpr (Or.inr hδ))
        (Finset.mem_insert_self γ P.support)
        heq)
    simp [hnot]
  · intro hγ
    have hpγ : P γ = 0 := Finsupp.notMem_support_iff.mp hγ
    simp [hpγ]

lemma TrigPoly.finiteAverage_single_zero_eventually_eq_coeff
    (E : CayleyExtraction S) (c : ℂ) :
    ∀ᶠ n in atTop,
      TrigPoly.finiteAverage
          (Finsupp.single (0 : E.Group) c : E.TrigPoly) n = c := by
  filter_upwards [E.data.finiteLift_zero_eventually_eq_zero] with n hn
  exact TrigPoly.finiteAverage_single_eq_coeff_of_lift_eq_zero
    (E := E) (0 : E.Group) c n hn

lemma finiteLift_eventually_ne_zero
    (E : CayleyExtraction S) {γ : E.Group} (hγ : γ ≠ 0) :
    ∀ᶠ n in atTop, E.lift n γ ≠ 0 :=
  E.data.finiteLift_eventually_ne_zero hγ

lemma TrigPoly.finiteAverage_single_eq_zero_eventually_of_ne_zero
    (E : CayleyExtraction S) {γ : E.Group}
    (hγ : γ ≠ 0) (c : ℂ) :
    ∀ᶠ n in atTop,
      TrigPoly.finiteAverage (Finsupp.single γ c : E.TrigPoly) n = 0 := by
  filter_upwards [E.finiteLift_eventually_ne_zero hγ] with n hn
  exact TrigPoly.finiteAverage_single_eq_zero_of_lift_ne_zero
    (E := E) γ c n hn

/-- Along relation-stable extraction data, finite averages of lifted
trigonometric polynomials are eventually their zero-frequency coefficient. -/
lemma TrigPoly.finiteAverage_eventually_eq_zeroCoeff
    (E : CayleyExtraction S) (P : E.TrigPoly) :
    ∀ᶠ n in atTop,
      TrigPoly.finiteAverage P n = P (0 : E.Group) := by
  refine Finsupp.induction_linear P ?zero ?add ?single
  · simp [TrigPoly.finiteAverage, avgZMod]
  · intro P Q hP hQ
    filter_upwards [hP, hQ] with n hp hq
    rw [TrigPoly.finiteAverage_add, hp, hq]
    rfl
  · intro γ c
    by_cases hγ : γ = 0
    · subst hγ
      simpa [Finsupp.single_eq_same] using
        TrigPoly.finiteAverage_single_zero_eventually_eq_coeff E c
    · filter_upwards
        [TrigPoly.finiteAverage_single_eq_zero_eventually_of_ne_zero E hγ c] with n hn
      rw [hn]
      exact (Finsupp.single_eq_of_ne (Ne.symm hγ) :
        (Finsupp.single γ c : E.TrigPoly) (0 : E.Group) = 0).symm

lemma TrigPoly.finiteAverage_tendsto_zeroCoeff
    (E : CayleyExtraction S) (P : E.TrigPoly) :
    Tendsto (fun n => TrigPoly.finiteAverage P n) atTop
      (𝓝 (P (0 : E.Group))) := by
  have h :
      (fun _ : ℕ => P (0 : E.Group)) =ᶠ[atTop]
        fun n => TrigPoly.finiteAverage P n := by
    filter_upwards [TrigPoly.finiteAverage_eventually_eq_zeroCoeff E P] with n hn
    exact hn.symm
  exact tendsto_const_nhds.congr' h

lemma TrigPoly.finiteAverage_tendsto_compactAverage
    (E : CayleyExtraction S) (P : E.TrigPoly) :
    Tendsto (fun n => TrigPoly.finiteAverage P n) atTop
      (𝓝 (TrigPoly.compactAverage P)) := by
  simpa [TrigPoly.compactAverage] using
    TrigPoly.finiteAverage_tendsto_zeroCoeff E P

lemma TrigPoly.indicatorWeightedFiniteAverage_tendsto_coeffFunctional
    (E : CayleyExtraction S) (P : E.TrigPoly) :
    Tendsto
      (fun n => TrigPoly.indicatorWeightedFiniteAverage P n)
      atTop (𝓝 (TrigPoly.indicatorCoeffFunctional P)) := by
  refine Finsupp.induction_linear P ?zero ?add ?single
  · simp [TrigPoly.indicatorWeightedFiniteAverage,
      TrigPoly.indicatorCoeffFunctional, avgZMod]
  · intro P Q hP hQ
    rw [TrigPoly.indicatorCoeffFunctional_add P Q]
    exact (hP.add hQ).congr' (Filter.Eventually.of_forall fun n => by
      exact (TrigPoly.indicatorWeightedFiniteAverage_add P Q n).symm)
  · intro γ c
    rw [TrigPoly.indicatorCoeffFunctional_single γ c]
    have hcoeff := E.coeff_tendsto γ
    have hc : Tendsto (fun _ : ℕ => c) atTop (𝓝 c) :=
      tendsto_const_nhds
    have hmul := hc.mul hcoeff
    exact hmul.congr' (Filter.Eventually.of_forall fun n => by
      exact (TrigPoly.indicatorWeightedFiniteAverage_single γ c n).symm)

end CayleyExtraction

end

end Erdos42.CompactCayley


/-! =============================================================
    Section from: Erdos/P42/CompactCayley/PairOverlap.lean
    ============================================================= -/

/-
Erdős Problem 42 — generic finite pair-overlap predicates.
-/


namespace Erdos42.CompactCayley


/-- The finite fiber of pairs in `Q × Q` with prescribed difference.  This
definition fixes the otherwise hidden decidability argument of `Finset.filter`,
so downstream bounds can share exactly the same finite set. -/
noncomputable def pairFiber {G : Type*} [Sub G] (Q : Finset G) (γ : G) :
    Finset (G × G) := by
  classical
  exact (Q.product Q).filter (fun pair => pair.1 - pair.2 = γ)

/-- Generic lower-overlap form of the Fejér coefficient bound. -/
def PairCoeffLowerBound {G : Type*} [AddGroup G]
    (Q B : Finset G) (M : ℝ) : Prop :=
  ∀ γ ∈ B,
    1 - M ≤ ((pairFiber Q γ).card : ℝ) / (Q.card : ℝ)

/-- Absolute-error real-ratio form of the finite pair-overlap bound. -/
def PairCoeffRealBound {G : Type*} [AddGroup G]
    (Q B : Finset G) (M : ℝ) : Prop :=
  ∀ γ ∈ B,
    |1 - ((pairFiber Q γ).card : ℝ) / (Q.card : ℝ)| ≤ M

namespace PairCoeffRealBound

variable {G : Type*} [AddGroup G]

lemma pairFilter_card_le (Q : Finset G) (γ : G) :
    (pairFiber Q γ).card ≤ Q.card := by
  classical
  let fiber := pairFiber Q γ
  have hmaps :
      Set.MapsTo (fun pair : G × G => pair.1) (↑fiber : Set (G × G)) (↑Q : Set G) := by
    intro pair hpair
    have hpair_fin : pair ∈ fiber := by
      simpa using hpair
    have hpair' :
        pair ∈ (Q.product Q).filter (fun pair : G × G => pair.1 - pair.2 = γ) := by
      simpa only [fiber, pairFiber] using hpair_fin
    exact (Finset.mem_product.mp (Finset.mem_filter.mp hpair').1).1
  have hinj :
      Set.InjOn (fun pair : G × G => pair.1) (↑fiber : Set (G × G)) := by
    intro pair hpair pair' hpair' hfirst
    have hpair_fin : pair ∈ fiber := by
      simpa using hpair
    have hpair'_fin : pair' ∈ fiber := by
      simpa using hpair'
    have hpair_mem :
        pair ∈ (Q.product Q).filter (fun pair : G × G => pair.1 - pair.2 = γ) := by
      simpa only [fiber, pairFiber] using hpair_fin
    have hpair'_mem :
        pair' ∈ (Q.product Q).filter (fun pair : G × G => pair.1 - pair.2 = γ) := by
      simpa only [fiber, pairFiber] using hpair'_fin
    have hdiff : pair.1 - pair.2 = γ :=
      (Finset.mem_filter.mp hpair_mem).2
    have hdiff' : pair'.1 - pair'.2 = γ :=
      (Finset.mem_filter.mp hpair'_mem).2
    have hsub : pair.1 - pair.2 = pair.1 - pair'.2 := by
      simpa [hfirst] using hdiff.trans hdiff'.symm
    have hsecond : pair.2 = pair'.2 := by
      simpa [sub_eq_sub_iff_add_eq_add] using hsub
    exact Prod.ext hfirst hsecond
  simpa [fiber] using
    Finset.card_le_card_of_injOn (fun pair : G × G => pair.1)
      hmaps hinj

lemma of_lowerBound {Q B : Finset G} {M : ℝ}
    (hQ : Q ≠ ∅) (hM : PairCoeffLowerBound Q B M) :
    PairCoeffRealBound Q B M := by
  classical
  intro γ hγ
  have hQpos_nat : 0 < Q.card := Finset.card_pos.mpr
    (Finset.nonempty_iff_ne_empty.mpr hQ)
  have hQpos : 0 < (Q.card : ℝ) := by exact_mod_cast hQpos_nat
  have hratio_le_one :
      ((pairFiber Q γ).card : ℝ) / (Q.card : ℝ) ≤ 1 := by
    rw [div_le_iff₀ hQpos]
    norm_num
    exact_mod_cast pairFilter_card_le Q γ
  have hratio_ge := hM γ hγ
  rw [abs_le]
  constructor <;> linarith

end PairCoeffRealBound

end Erdos42.CompactCayley


/-! =============================================================
    Section from: Erdos/P42/CompactCayley/Fejer.lean
    ============================================================= -/

/-
Erdős Problem 42 — Fejér kernels for compact-Cayley extraction.
-/


namespace Erdos42.CompactCayley

open Filter Complex
open scoped BigOperators ComplexConjugate Topology

noncomputable section

namespace CayleyExtraction

variable {ℓ : ℕ} {η : ℝ} {S : CayleyCounterSeq ℓ η}

/-- Compact-dual Fejér kernel associated to a finite frequency set. -/
noncomputable def compactFejerKernel
    (E : CayleyExtraction S) (Q : Finset E.Group)
    (z : E.CompactDual) : ℂ :=
  ((Q.card : ℂ)⁻¹) *
    ((∑ γ ∈ Q, E.characterValue z γ) *
      star (∑ γ ∈ Q, E.characterValue z γ))

/-- Compact-dual Fejér kernel on the additive wrapper. -/
noncomputable def compactAddFejerKernel
    (E : CayleyExtraction S) (Q : Finset E.Group)
    (z : E.CompactAddDual) : ℂ :=
  E.compactFejerKernel Q z.toMul

/-- Finite cyclic lift of the Fejér kernel. -/
noncomputable def finiteFejerKernel
    (E : CayleyExtraction S) (Q : Finset E.Group) (n : ℕ)
    (x : ZMod (S.p (E.φ n))) : ℂ :=
  letI : NeZero (S.p (E.φ n)) := ⟨(S.prime (E.φ n)).ne_zero⟩
  ((Q.card : ℂ)⁻¹) *
    ((∑ γ ∈ Q, ZMod.stdAddChar (-(E.lift n γ * x))) *
      star (∑ γ ∈ Q, ZMod.stdAddChar (-(E.lift n γ * x))))

/-- Finite cyclic lift of the compact-phase shifted Fejér kernel. -/
noncomputable def shiftedFiniteFejerKernel
    (E : CayleyExtraction S) (Q : Finset E.Group) (z : E.CompactAddDual)
    (n : ℕ) (x : ZMod (S.p (E.φ n))) : ℂ :=
  letI : NeZero (S.p (E.φ n)) := ⟨(S.prime (E.φ n)).ne_zero⟩
  ((Q.card : ℂ)⁻¹) *
    ((∑ γ ∈ Q,
        E.addCharacterValue z γ *
          ZMod.stdAddChar (-(E.lift n γ * x))) *
      star (∑ γ ∈ Q,
        E.addCharacterValue z γ *
          ZMod.stdAddChar (-(E.lift n γ * x))))

/-- Normalized finite average of the finite cyclic Fejér kernel. -/
noncomputable def finiteFejerKernelAverage
    (E : CayleyExtraction S) (Q : Finset E.Group) (n : ℕ) : ℂ :=
  letI : NeZero (S.p (E.φ n)) := ⟨(S.prime (E.φ n)).ne_zero⟩
  avgZMod fun x : ZMod (S.p (E.φ n)) => E.finiteFejerKernel Q n x

/-- One Fourier mode in the Fejér expansion. -/
noncomputable def fejerTerm
    (E : CayleyExtraction S) (Q : Finset E.Group)
    (pair : E.Group × E.Group) : E.TrigPoly :=
  Finsupp.single (pair.1 - pair.2) ((Q.card : ℂ)⁻¹)

/-- The Fejér kernel as a trigonometric polynomial. -/
noncomputable def fejerTrigPoly
    (E : CayleyExtraction S) (Q : Finset E.Group) : E.TrigPoly :=
  ∑ pair ∈ Q.product Q, E.fejerTerm Q pair

/-- One Fourier mode in the Fejér expansion, modulated by a compact-dual point.

For fixed `z`, the resulting polynomial is the Fejér kernel translated by `z`
on the compact side; on the finite side it remains a squared magnitude because
the factors `E.addCharacterValue z γ` are unit phases. -/
noncomputable def shiftedFejerTerm
    (E : CayleyExtraction S) (Q : Finset E.Group) (z : E.CompactAddDual)
    (pair : E.Group × E.Group) : E.TrigPoly :=
  Finsupp.single (pair.1 - pair.2)
    ((Q.card : ℂ)⁻¹ * E.addCharacterValue z (pair.1 - pair.2))

/-- The compact-phase shifted Fejér polynomial. -/
noncomputable def shiftedFejerTrigPoly
    (E : CayleyExtraction S) (Q : Finset E.Group) (z : E.CompactAddDual) :
    E.TrigPoly :=
  ∑ pair ∈ Q.product Q, E.shiftedFejerTerm Q z pair

lemma fejerTerm_evalFinite
    (E : CayleyExtraction S) (Q : Finset E.Group)
    (pair : E.Group × E.Group) (n : ℕ)
    [NeZero (S.p (E.φ n))]
    (x : ZMod (S.p (E.φ n))) :
    TrigPoly.evalFinite (E.fejerTerm Q pair) n x =
      (Q.card : ℂ)⁻¹ *
        ZMod.stdAddChar (-(E.lift n (pair.1 - pair.2) * x)) := by
  simp [fejerTerm, TrigPoly.evalFinite]

lemma fejerTerm_evalAdd
    (E : CayleyExtraction S) (Q : Finset E.Group)
    (pair : E.Group × E.Group) (z : E.CompactAddDual) :
    TrigPoly.evalAdd (E.fejerTerm Q pair) z =
      (Q.card : ℂ)⁻¹ * E.addCharacterValue z (pair.1 - pair.2) := by
  simp [fejerTerm]

lemma shiftedFejerTerm_evalFinite
    (E : CayleyExtraction S) (Q : Finset E.Group) (z : E.CompactAddDual)
    (pair : E.Group × E.Group) (n : ℕ)
    [NeZero (S.p (E.φ n))]
    (x : ZMod (S.p (E.φ n))) :
    TrigPoly.evalFinite (E.shiftedFejerTerm Q z pair) n x =
      ((Q.card : ℂ)⁻¹ * E.addCharacterValue z (pair.1 - pair.2)) *
        ZMod.stdAddChar (-(E.lift n (pair.1 - pair.2) * x)) := by
  rw [shiftedFejerTerm, TrigPoly.evalFinite_single]

lemma shiftedFejerTerm_apply
    (E : CayleyExtraction S) (Q : Finset E.Group) (z : E.CompactAddDual)
    (pair : E.Group × E.Group) (γ : E.Group) :
    (E.shiftedFejerTerm Q z pair) γ =
      (E.fejerTerm Q pair γ) * E.addCharacterValue z γ := by
  by_cases h : pair.1 - pair.2 = γ
  · subst h
    simp [shiftedFejerTerm, fejerTerm]
  · simp [shiftedFejerTerm, fejerTerm, h]

lemma shiftedFejerTrigPoly_apply
    (E : CayleyExtraction S) (Q : Finset E.Group) (z : E.CompactAddDual)
    (γ : E.Group) :
    E.shiftedFejerTrigPoly Q z γ =
      (E.fejerTrigPoly Q γ) * E.addCharacterValue z γ := by
  classical
  unfold shiftedFejerTrigPoly fejerTrigPoly
  rw [Finsupp.finsetSum_apply, Finsupp.finsetSum_apply]
  simp_rw [E.shiftedFejerTerm_apply Q z]
  rw [Finset.sum_mul]

lemma stdAddChar_sub_fejer
    {p : ℕ} [NeZero p] (r s x : ZMod p) :
    ZMod.stdAddChar (-((r - s) * x)) =
      ZMod.stdAddChar (-(r * x)) *
        star (ZMod.stdAddChar (-(s * x))) := by
  have hstar : star (ZMod.stdAddChar (-(s * x))) =
      ZMod.stdAddChar (s * x) := by
    have h := AddChar.map_neg_eq_conj (ZMod.stdAddChar (N := p)) (s * x)
    simp [h]
  rw [hstar]
  rw [← ZMod.stdAddChar.map_add_eq_mul]
  congr 1
  ring

lemma sum_product_const_mul_star
    {ι : Type*} (Q : Finset ι) (a : ι → ℂ) (c : ℂ) :
    (∑ x ∈ Q.product Q, c * (a x.1 * star (a x.2))) =
      c * ((∑ x ∈ Q, a x) * star (∑ y ∈ Q, a y)) := by
  have hstar : star (∑ y ∈ Q, a y) = ∑ y ∈ Q, star (a y) := by
    simp
  rw [hstar]
  change (∑ x ∈ Q ×ˢ Q, c * (a x.1 * star (a x.2))) =
    c * ((∑ x ∈ Q, a x) * ∑ y ∈ Q, star (a y))
  rw [Finset.sum_product]
  simp_rw [Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl ?_
  intro x _hx
  rw [← Finset.mul_sum]

lemma fejerTrigPoly_compactAverage_eq_one_of_nonempty
    (E : CayleyExtraction S) (Q : Finset E.Group) (hQ : Q ≠ ∅) :
    TrigPoly.compactAverage (E.fejerTrigPoly Q) = 1 := by
  classical
  have hcard_ne : (Q.card : ℂ) ≠ 0 := by
    exact_mod_cast (Finset.card_ne_zero.mpr
      (Finset.nonempty_iff_ne_empty.mpr hQ))
  unfold TrigPoly.compactAverage fejerTrigPoly fejerTerm
  rw [Finsupp.finsetSum_apply]
  change (∑ i ∈ Q ×ˢ Q,
    (Finsupp.single (i.1 - i.2) ((Q.card : ℂ)⁻¹) :
      E.TrigPoly) (0 : E.Group)) = 1
  rw [Finset.sum_product]
  simp [Finsupp.single_apply, sub_eq_zero, hcard_ne]

lemma shiftedFejerTrigPoly_compactAverage_eq_one_of_nonempty
    (E : CayleyExtraction S) (Q : Finset E.Group) (z : E.CompactAddDual)
    (hQ : Q ≠ ∅) :
    TrigPoly.compactAverage (E.shiftedFejerTrigPoly Q z) = 1 := by
  unfold TrigPoly.compactAverage
  rw [E.shiftedFejerTrigPoly_apply Q z 0]
  have hfejer0 : (E.fejerTrigPoly Q) (0 : E.Group) = 1 := by
    simpa [TrigPoly.compactAverage] using
      E.fejerTrigPoly_compactAverage_eq_one_of_nonempty Q hQ
  rw [hfejer0]
  simp

lemma fejerTrigPoly_evalAdd_eq_compactAddFejerKernel
    (E : CayleyExtraction S) (Q : Finset E.Group)
    (z : E.CompactAddDual) :
    TrigPoly.evalAdd (E.fejerTrigPoly Q) z =
      E.compactAddFejerKernel Q z := by
  classical
  unfold fejerTrigPoly
  let ev : E.TrigPoly →+ ℂ :=
    { toFun := fun P => TrigPoly.evalAdd P z
      map_zero' := by simp
      map_add' := by
        intro P R
        exact TrigPoly.evalAdd_add P R z }
  change ev (∑ pair ∈ Q.product Q, E.fejerTerm Q pair) =
    E.compactAddFejerKernel Q z
  rw [map_sum]
  change
      (∑ pair ∈ Q.product Q,
        TrigPoly.evalAdd (E.fejerTerm Q pair) z) =
      E.compactAddFejerKernel Q z
  simp_rw [E.fejerTerm_evalAdd]
  calc
    (∑ pair ∈ Q.product Q,
        (Q.card : ℂ)⁻¹ * E.addCharacterValue z (pair.1 - pair.2)) =
        ∑ pair ∈ Q.product Q,
          (Q.card : ℂ)⁻¹ *
            (E.addCharacterValue z pair.1 *
              star (E.addCharacterValue z pair.2)) := by
      refine Finset.sum_congr rfl ?_
      intro pair _hpair
      rw [E.addCharacterValue_sub]
    _ = E.compactAddFejerKernel Q z := by
      unfold compactAddFejerKernel compactFejerKernel addCharacterValue
      exact sum_product_const_mul_star Q
        (fun γ => E.characterValue z.toMul γ)
        ((Q.card : ℂ)⁻¹)

lemma integral_compactAddFejerKernel_eq_one
    (E : CayleyExtraction S) (Q : Finset E.Group) (hQ : Q ≠ ∅) :
    ∫ z : E.CompactAddDual, E.compactAddFejerKernel Q z ∂E.haar = 1 := by
  rw [show
      (fun z : E.CompactAddDual => E.compactAddFejerKernel Q z) =
        fun z => TrigPoly.evalAdd (E.fejerTrigPoly Q) z by
      funext z
      exact (E.fejerTrigPoly_evalAdd_eq_compactAddFejerKernel Q z).symm]
  rw [TrigPoly.integral_evalAdd_eq_compactAverage E]
  exact E.fejerTrigPoly_compactAverage_eq_one_of_nonempty Q hQ

lemma integral_compactAddFejerKernel_eq_one_of_separating
    (E : CayleyExtraction S)
    (_hsep :
      ∀ γ : E.Group, γ ≠ 0 →
        ∃ y : E.CompactAddDual, E.addCharacterValue y γ ≠ 1)
    (Q : Finset E.Group) (hQ : Q ≠ ∅) :
    ∫ z : E.CompactAddDual, E.compactAddFejerKernel Q z ∂E.haar = 1 :=
  E.integral_compactAddFejerKernel_eq_one Q hQ

lemma fejerTrigPoly_apply_sum
    (E : CayleyExtraction S) (Q : Finset E.Group) (γ : E.Group) :
    (E.fejerTrigPoly Q) γ =
      ∑ pair ∈ Q.product Q,
        if pair.1 - pair.2 = γ then (Q.card : ℂ)⁻¹ else 0 := by
  unfold fejerTrigPoly fejerTerm
  rw [Finsupp.finsetSum_apply]
  simp [Finsupp.single_apply]

lemma fejerTrigPoly_apply_filter_card
    (E : CayleyExtraction S) (Q : Finset E.Group) (γ : E.Group) :
    (E.fejerTrigPoly Q) γ =
      ((pairFiber Q γ).card : ℂ) *
        (Q.card : ℂ)⁻¹ := by
  rw [E.fejerTrigPoly_apply_sum Q γ]
  rw [← Finset.sum_filter]
  have hfilter :
      (Q.product Q).filter (fun pair : E.Group × E.Group =>
        pair.1 - pair.2 = γ) = pairFiber Q γ := by
    ext pair
    simp [pairFiber]
  rw [hfilter]
  simp [mul_comm]

lemma pairFiber_card_neg
    (E : CayleyExtraction S)
    (Q : Finset E.Group) (γ : E.Group) :
    (pairFiber Q (-γ)).card = (pairFiber Q γ).card := by
  classical
  refine Finset.card_bij (fun pair _hpair => (pair.2, pair.1)) ?mem ?inj ?surj
  · intro pair hpair
    have hmem :
        pair ∈ (Q.product Q).filter
          (fun pair : E.Group × E.Group => pair.1 - pair.2 = -γ) := by
      simpa [pairFiber] using hpair
    have hprod := (Finset.mem_filter.mp hmem).1
    have hprod' : (pair.2, pair.1) ∈ Q.product Q :=
      Finset.mem_product.mpr
        ⟨(Finset.mem_product.mp hprod).2, (Finset.mem_product.mp hprod).1⟩
    have hdiff := (Finset.mem_filter.mp hmem).2
    have hdiff' : pair.2 - pair.1 = γ := by
      calc
        pair.2 - pair.1 = -(pair.1 - pair.2) := by rw [neg_sub]
        _ = γ := by rw [hdiff]; simp
    have hfilter' :
        (pair.2, pair.1) ∈ (Q.product Q).filter
          (fun pair : E.Group × E.Group => pair.1 - pair.2 = γ) :=
      Finset.mem_filter.mpr ⟨hprod', hdiff'⟩
    simpa [pairFiber] using hfilter'
  · intro a ha b hb hswap
    exact Prod.ext (congrArg Prod.snd hswap) (congrArg Prod.fst hswap)
  · intro pair hpair
    refine ⟨(pair.2, pair.1), ?_, ?_⟩
    · have hmem :
          pair ∈ (Q.product Q).filter
            (fun pair : E.Group × E.Group => pair.1 - pair.2 = γ) := by
        simpa [pairFiber] using hpair
      have hprod := (Finset.mem_filter.mp hmem).1
      have hprod' : (pair.2, pair.1) ∈ Q.product Q :=
        Finset.mem_product.mpr
          ⟨(Finset.mem_product.mp hprod).2, (Finset.mem_product.mp hprod).1⟩
      have hdiff := (Finset.mem_filter.mp hmem).2
      have hdiff' : pair.2 - pair.1 = -γ := by
        calc
          pair.2 - pair.1 = -(pair.1 - pair.2) := by rw [neg_sub]
          _ = -γ := by rw [hdiff]
      have hfilter' :
          (pair.2, pair.1) ∈ (Q.product Q).filter
            (fun pair : E.Group × E.Group => pair.1 - pair.2 = -γ) :=
        Finset.mem_filter.mpr ⟨hprod', hdiff'⟩
      simpa [pairFiber] using hfilter'
    · rfl

lemma fejerTrigPoly_apply_neg
    (E : CayleyExtraction S) (Q : Finset E.Group) (γ : E.Group) :
    (E.fejerTrigPoly Q) (-γ) = (E.fejerTrigPoly Q) γ := by
  rw [E.fejerTrigPoly_apply_filter_card Q (-γ),
    E.fejerTrigPoly_apply_filter_card Q γ, E.pairFiber_card_neg Q γ]

lemma fejerTrigPoly_apply_re_eq_pairRatio
    (E : CayleyExtraction S) (Q : Finset E.Group) (γ : E.Group) :
    ((E.fejerTrigPoly Q) γ).re =
      ((pairFiber Q γ).card : ℝ) / (Q.card : ℝ) := by
  let fiber := pairFiber Q γ
  rw [E.fejerTrigPoly_apply_filter_card]
  change (((fiber.card : ℂ) * (Q.card : ℂ)⁻¹).re) =
    (fiber.card : ℝ) / (Q.card : ℝ)
  have hcast :
      ((fiber.card : ℂ) * (Q.card : ℂ)⁻¹) =
        (((fiber.card : ℝ) / (Q.card : ℝ) : ℝ) : ℂ) := by
    rw [div_eq_mul_inv]
    have hfiber : (fiber.card : ℂ) = ((fiber.card : ℝ) : ℂ) := by
      norm_num
    have hQ : (Q.card : ℂ) = ((Q.card : ℝ) : ℂ) := by
      norm_num
    rw [hfiber, hQ, ← Complex.ofReal_inv, ← Complex.ofReal_mul]
  rw [hcast]
  simp

lemma fejerTrigPoly_apply_im_eq_zero
    (E : CayleyExtraction S) (Q : Finset E.Group) (γ : E.Group) :
    ((E.fejerTrigPoly Q) γ).im = 0 := by
  let fiber := pairFiber Q γ
  rw [E.fejerTrigPoly_apply_filter_card]
  change (((fiber.card : ℂ) * (Q.card : ℂ)⁻¹).im) = 0
  have hcast :
      ((fiber.card : ℂ) * (Q.card : ℂ)⁻¹) =
        (((fiber.card : ℝ) / (Q.card : ℝ) : ℝ) : ℂ) := by
    rw [div_eq_mul_inv]
    have hfiber : (fiber.card : ℂ) = ((fiber.card : ℝ) : ℂ) := by
      norm_num
    have hQ : (Q.card : ℂ) = ((Q.card : ℝ) : ℂ) := by
      norm_num
    rw [hfiber, hQ, ← Complex.ofReal_inv, ← Complex.ofReal_mul]
  rw [hcast]
  simp

lemma fejerTrigPoly_apply_re_nonneg
    (E : CayleyExtraction S) (Q : Finset E.Group) (γ : E.Group) :
    0 ≤ ((E.fejerTrigPoly Q) γ).re := by
  rw [E.fejerTrigPoly_apply_re_eq_pairRatio]
  positivity

lemma fejerTrigPoly_apply_re_le_one
    (E : CayleyExtraction S) (Q : Finset E.Group) (γ : E.Group) :
    ((E.fejerTrigPoly Q) γ).re ≤ 1 := by
  rw [E.fejerTrigPoly_apply_re_eq_pairRatio]
  exact div_le_one_of_le₀
    (by exact_mod_cast PairCoeffRealBound.pairFilter_card_le Q γ)
    (Nat.cast_nonneg Q.card)

/-- Abstract finite-frequency Fejér coefficient bound. -/
def FejerCoeffBound
    (E : CayleyExtraction S) (Q B : Finset E.Group) (M : ℝ) : Prop :=
  ∀ γ ∈ B, ‖1 - (E.fejerTrigPoly Q) γ‖ ≤ M

/-- Pair-count form of the Fejér coefficient bound. -/
def FejerPairCoeffBound
    (E : CayleyExtraction S) (Q B : Finset E.Group) (M : ℝ) : Prop :=
  ∀ γ ∈ B,
    ‖1 -
      (((pairFiber Q γ).card : ℂ) *
        (Q.card : ℂ)⁻¹)‖ ≤ M

/-- Real-ratio form of the pair-count Fejér coefficient bound, as produced by
Følner overlap estimates. -/
def FejerPairCoeffRealBound
    (E : CayleyExtraction S) (Q B : Finset E.Group) (M : ℝ) : Prop :=
  PairCoeffRealBound Q B M

/-- Lower-overlap form of the Fejér coefficient bound.  This is the shape
normally produced by a Følner-set estimate. -/
def FejerPairCoeffLowerBound
    (E : CayleyExtraction S) (Q B : Finset E.Group) (M : ℝ) : Prop :=
  PairCoeffLowerBound Q B M

/-- Fejér coefficient bound on negative frequencies, the form used by the
finite DFT formula at positive extracted lifts. -/
def FejerNegCoeffBound
    (E : CayleyExtraction S) (Q B : Finset E.Group) (M : ℝ) : Prop :=
  ∀ γ ∈ B, ‖1 - (E.fejerTrigPoly Q) (-γ)‖ ≤ M

lemma fejerCoeffBound_of_pairCoeffBound
    (E : CayleyExtraction S) {Q B : Finset E.Group} {M : ℝ}
    (hM : E.FejerPairCoeffBound Q B M) :
    E.FejerCoeffBound Q B M := by
  intro γ hγ
  rw [E.fejerTrigPoly_apply_filter_card]
  exact hM γ hγ

lemma fejerPairCoeffBound_of_realBound
    (E : CayleyExtraction S) {Q B : Finset E.Group} {M : ℝ}
    (hM : E.FejerPairCoeffRealBound Q B M) :
    E.FejerPairCoeffBound Q B M := by
  intro γ hγ
  let fiber := pairFiber Q γ
  have hcast :
      ((fiber.card : ℂ) * (Q.card : ℂ)⁻¹) =
        (((fiber.card : ℝ) / (Q.card : ℝ) : ℝ) : ℂ) := by
    rw [div_eq_mul_inv]
    have hfiber : (fiber.card : ℂ) = ((fiber.card : ℝ) : ℂ) := by
      norm_num
    have hQ : (Q.card : ℂ) = ((Q.card : ℝ) : ℂ) := by
      norm_num
    rw [hfiber, hQ, ← Complex.ofReal_inv, ← Complex.ofReal_mul]
  change ‖1 - (fiber.card : ℂ) * (Q.card : ℂ)⁻¹‖ ≤ M
  rw [hcast]
  rw [← Complex.ofReal_one, ← Complex.ofReal_sub]
  rw [Complex.norm_real, Real.norm_eq_abs]
  simpa [fiber, FejerPairCoeffRealBound, PairCoeffRealBound] using hM γ hγ

lemma fejerCoeffBound_of_pairCoeffRealBound
    (E : CayleyExtraction S) {Q B : Finset E.Group} {M : ℝ}
    (hM : E.FejerPairCoeffRealBound Q B M) :
    E.FejerCoeffBound Q B M :=
  E.fejerCoeffBound_of_pairCoeffBound
    (E.fejerPairCoeffBound_of_realBound hM)

lemma fejerNegCoeffBound_of_coeffBound_neg
    (E : CayleyExtraction S) {Q B : Finset E.Group} {M : ℝ}
    (hM : E.FejerCoeffBound Q (B.image Neg.neg) M) :
    E.FejerNegCoeffBound Q B M := by
  intro γ hγ
  exact hM (-γ) (Finset.mem_image.mpr ⟨γ, hγ, rfl⟩)

lemma fejerNegCoeffBound_of_pairCoeffRealBound_neg
    (E : CayleyExtraction S) {Q B : Finset E.Group} {M : ℝ}
    (hM : E.FejerPairCoeffRealBound Q (B.image Neg.neg) M) :
    E.FejerNegCoeffBound Q B M :=
  E.fejerNegCoeffBound_of_coeffBound_neg
    (E.fejerCoeffBound_of_pairCoeffRealBound hM)

lemma fejerPairFilter_card_le
    (E : CayleyExtraction S) (Q : Finset E.Group) (γ : E.Group) :
    (pairFiber Q γ).card ≤ Q.card :=
  PairCoeffRealBound.pairFilter_card_le Q γ

lemma fejerPairCoeffRealBound_of_lowerBound
    (E : CayleyExtraction S) {Q B : Finset E.Group} {M : ℝ}
    (hQ : Q ≠ ∅) (hM : E.FejerPairCoeffLowerBound Q B M) :
    E.FejerPairCoeffRealBound Q B M :=
  PairCoeffRealBound.of_lowerBound hQ hM

lemma fejerCoeffBound_of_pairCoeffLowerBound
    (E : CayleyExtraction S) {Q B : Finset E.Group} {M : ℝ}
    (hQ : Q ≠ ∅) (hM : E.FejerPairCoeffLowerBound Q B M) :
    E.FejerCoeffBound Q B M :=
  E.fejerCoeffBound_of_pairCoeffRealBound
    (E.fejerPairCoeffRealBound_of_lowerBound hQ hM)

lemma fejerNegCoeffBound_of_pairCoeffLowerBound_neg
    (E : CayleyExtraction S) {Q B : Finset E.Group} {M : ℝ}
    (hQ : Q ≠ ∅) (hM : E.FejerPairCoeffLowerBound Q (B.image Neg.neg) M) :
    E.FejerNegCoeffBound Q B M :=
  E.fejerNegCoeffBound_of_coeffBound_neg
    (E.fejerCoeffBound_of_pairCoeffLowerBound hQ hM)

lemma fejerTrigPoly_evalFinite_eventually_eq
    (E : CayleyExtraction S) (Q : Finset E.Group) :
    ∀ᶠ n in atTop,
      ∀ x : ZMod (S.p (E.φ n)),
        TrigPoly.evalFinite (E.fejerTrigPoly Q) n x =
          E.finiteFejerKernel Q n x := by
  classical
  have hpairs :
      ∀ᶠ n in atTop,
        ∀ pair ∈ Q.product Q,
          E.lift n (pair.1 - pair.2) =
            E.lift n pair.1 - E.lift n pair.2 := by
    rw [(Q.product Q).eventually_all]
    intro pair _hpair
    exact E.data.finiteLift_sub_eventually_eq pair.1 pair.2
  filter_upwards [hpairs] with n hn x
  haveI : NeZero (S.p (E.φ n)) := ⟨(S.prime (E.φ n)).ne_zero⟩
  unfold fejerTrigPoly
  let ev : E.TrigPoly →+ ℂ :=
    { toFun := fun P => TrigPoly.evalFinite P n x
      map_zero' := by simp
      map_add' := by
        intro P R
        exact TrigPoly.evalFinite_add P R n x }
  change ev (∑ pair ∈ Q.product Q, E.fejerTerm Q pair) =
    E.finiteFejerKernel Q n x
  rw [map_sum]
  change
      (∑ pair ∈ Q.product Q,
        TrigPoly.evalFinite (E.fejerTerm Q pair) n x) =
      E.finiteFejerKernel Q n x
  simp_rw [E.fejerTerm_evalFinite]
  calc
    (∑ pair ∈ Q.product Q,
        (Q.card : ℂ)⁻¹ *
          ZMod.stdAddChar (-(E.lift n (pair.1 - pair.2) * x))) =
        ∑ pair ∈ Q.product Q,
          (Q.card : ℂ)⁻¹ *
            (ZMod.stdAddChar (-(E.lift n pair.1 * x)) *
              star (ZMod.stdAddChar (-(E.lift n pair.2 * x)))) := by
      refine Finset.sum_congr rfl ?_
      intro pair hpair
      rw [hn pair hpair]
      rw [stdAddChar_sub_fejer]
    _ = E.finiteFejerKernel Q n x := by
      unfold finiteFejerKernel
      exact sum_product_const_mul_star Q
        (fun γ => ZMod.stdAddChar (-(E.lift n γ * x)))
        ((Q.card : ℂ)⁻¹)

lemma shiftedFejerTrigPoly_evalFinite_eventually_eq
    (E : CayleyExtraction S) (Q : Finset E.Group) (z : E.CompactAddDual) :
    ∀ᶠ n in atTop,
      ∀ x : ZMod (S.p (E.φ n)),
        TrigPoly.evalFinite (E.shiftedFejerTrigPoly Q z) n x =
          E.shiftedFiniteFejerKernel Q z n x := by
  classical
  have hpairs :
      ∀ᶠ n in atTop,
        ∀ pair ∈ Q.product Q,
          E.lift n (pair.1 - pair.2) =
            E.lift n pair.1 - E.lift n pair.2 := by
    rw [(Q.product Q).eventually_all]
    intro pair _hpair
    exact E.data.finiteLift_sub_eventually_eq pair.1 pair.2
  filter_upwards [hpairs] with n hn x
  haveI : NeZero (S.p (E.φ n)) := ⟨(S.prime (E.φ n)).ne_zero⟩
  unfold shiftedFejerTrigPoly
  let ev : E.TrigPoly →+ ℂ :=
    { toFun := fun P => TrigPoly.evalFinite P n x
      map_zero' := by simp
      map_add' := by
        intro P R
        exact TrigPoly.evalFinite_add P R n x }
  change ev (∑ pair ∈ Q.product Q, E.shiftedFejerTerm Q z pair) =
    E.shiftedFiniteFejerKernel Q z n x
  rw [map_sum]
  change
      (∑ pair ∈ Q.product Q,
        TrigPoly.evalFinite (E.shiftedFejerTerm Q z pair) n x) =
      E.shiftedFiniteFejerKernel Q z n x
  simp_rw [E.shiftedFejerTerm_evalFinite]
  calc
    (∑ pair ∈ Q.product Q,
        ((Q.card : ℂ)⁻¹ * E.addCharacterValue z (pair.1 - pair.2)) *
          ZMod.stdAddChar (-(E.lift n (pair.1 - pair.2) * x))) =
        ∑ pair ∈ Q.product Q,
          (Q.card : ℂ)⁻¹ *
            ((E.addCharacterValue z pair.1 *
                ZMod.stdAddChar (-(E.lift n pair.1 * x))) *
              star (E.addCharacterValue z pair.2 *
                ZMod.stdAddChar (-(E.lift n pair.2 * x)))) := by
      refine Finset.sum_congr rfl ?_
      intro pair hpair
      rw [hn pair hpair]
      rw [E.addCharacterValue_sub, stdAddChar_sub_fejer]
      rw [star_mul]
      ring
    _ = E.shiftedFiniteFejerKernel Q z n x := by
      unfold shiftedFiniteFejerKernel
      exact sum_product_const_mul_star Q
        (fun γ =>
          E.addCharacterValue z γ *
            ZMod.stdAddChar (-(E.lift n γ * x)))
        ((Q.card : ℂ)⁻¹)

lemma finiteFejerKernelAverage_eventually_eq
    (E : CayleyExtraction S) (Q : Finset E.Group) :
    ∀ᶠ n in atTop,
      E.finiteFejerKernelAverage Q n =
        TrigPoly.finiteAverage (E.fejerTrigPoly Q) n := by
  filter_upwards [E.fejerTrigPoly_evalFinite_eventually_eq Q] with n hn
  haveI : NeZero (S.p (E.φ n)) := ⟨(S.prime (E.φ n)).ne_zero⟩
  unfold finiteFejerKernelAverage TrigPoly.finiteAverage
  apply congrArg (fun f : ZMod (S.p (E.φ n)) → ℂ => avgZMod f)
  funext x
  exact (hn x).symm

lemma finiteFejerKernelAverage_tendsto_compactAverage
    (E : CayleyExtraction S) (Q : Finset E.Group) :
    Tendsto (fun n => E.finiteFejerKernelAverage Q n) atTop
      (𝓝 (TrigPoly.compactAverage (E.fejerTrigPoly Q))) := by
  have h :
      (fun n => TrigPoly.finiteAverage (E.fejerTrigPoly Q) n) =ᶠ[atTop]
        fun n => E.finiteFejerKernelAverage Q n := by
    filter_upwards [E.finiteFejerKernelAverage_eventually_eq Q] with n hn
    exact hn.symm
  exact (TrigPoly.finiteAverage_tendsto_compactAverage E
    (E.fejerTrigPoly Q)).congr' h

lemma finiteFejerKernelAverage_tendsto_one
    (E : CayleyExtraction S) (Q : Finset E.Group) (hQ : Q ≠ ∅) :
    Tendsto (fun n => E.finiteFejerKernelAverage Q n) atTop (𝓝 (1 : ℂ)) := by
  simpa [E.fejerTrigPoly_compactAverage_eq_one_of_nonempty Q hQ] using
    E.finiteFejerKernelAverage_tendsto_compactAverage Q

lemma normalizedDftFunction_finiteFejerKernel_eventually_eq
    (E : CayleyExtraction S) (Q : Finset E.Group) :
    ∀ᶠ n in atTop,
      ∀ r : ZMod (S.p (E.φ n)),
        (letI : NeZero (S.p (E.φ n)) := ⟨(S.prime (E.φ n)).ne_zero⟩;
          normalizedDftFunction (E.finiteFejerKernel Q n) r) =
          (E.fejerTrigPoly Q).sum fun γ c =>
            if r + E.lift n γ = 0 then c else 0 := by
  filter_upwards [E.fejerTrigPoly_evalFinite_eventually_eq Q] with n hn r
  haveI : Fact (S.p (E.φ n)).Prime := ⟨S.prime (E.φ n)⟩
  haveI : NeZero (S.p (E.φ n)) := ⟨(S.prime (E.φ n)).ne_zero⟩
  have hfun :
      E.finiteFejerKernel Q n =
        fun x : ZMod (S.p (E.φ n)) =>
          TrigPoly.evalFinite (E.fejerTrigPoly Q) n x := by
    funext x
    exact (hn x).symm
  rw [hfun]
  exact TrigPoly.normalizedDftFunction_evalFinite
    (E := E) (E.fejerTrigPoly Q) n r

lemma normalizedDftFunction_finiteFejerKernel_at_neg_lift_eventually_eq_coeff
    (E : CayleyExtraction S) (Q : Finset E.Group) (γ : E.Group) :
    ∀ᶠ n in atTop,
      (letI : NeZero (S.p (E.φ n)) := ⟨(S.prime (E.φ n)).ne_zero⟩;
        normalizedDftFunction (E.finiteFejerKernel Q n) (-E.lift n γ)) =
        (E.fejerTrigPoly Q) γ := by
  let P : E.TrigPoly := E.fejerTrigPoly Q
  filter_upwards
    [E.normalizedDftFunction_finiteFejerKernel_eventually_eq Q,
      E.data.finiteLift_eventually_injOn_finset (insert γ P.support)] with n hfourier hinj
  haveI : NeZero (S.p (E.φ n)) := ⟨(S.prime (E.φ n)).ne_zero⟩
  rw [hfourier (-E.lift n γ)]
  exact TrigPoly.sum_if_neg_lift_add_eq_zero_eq_apply_of_injOn
    (E := E) P n γ hinj

lemma normalizedDftFunction_finiteFejerKernel_at_lift_eventually_eq_coeff
    (E : CayleyExtraction S) (Q : Finset E.Group) (γ : E.Group) :
    ∀ᶠ n in atTop,
      (letI : NeZero (S.p (E.φ n)) := ⟨(S.prime (E.φ n)).ne_zero⟩;
        normalizedDftFunction (E.finiteFejerKernel Q n) (E.lift n γ)) =
        (E.fejerTrigPoly Q) (-γ) := by
  filter_upwards
    [E.normalizedDftFunction_finiteFejerKernel_at_neg_lift_eventually_eq_coeff
        Q (-γ),
      E.data.finiteLift_neg_eventually_eq γ] with n hcoeff hneg
  haveI : NeZero (S.p (E.φ n)) := ⟨(S.prime (E.φ n)).ne_zero⟩
  have hfreq : -E.lift n (-γ) = E.lift n γ := by
    rw [lift, hneg]
    change - -E.data.finiteLift n γ = E.data.finiteLift n γ
    simp
  rw [← hfreq]
  exact hcoeff

lemma norm_one_sub_normalizedDftFunction_finiteFejerKernel_at_lift_eventually_le
    (E : CayleyExtraction S) (Q : Finset E.Group) (γ : E.Group)
    {M : ℝ} (hM : ‖1 - (E.fejerTrigPoly Q) (-γ)‖ ≤ M) :
    ∀ᶠ n in atTop,
      (letI : NeZero (S.p (E.φ n)) := ⟨(S.prime (E.φ n)).ne_zero⟩;
        ‖1 - normalizedDftFunction (E.finiteFejerKernel Q n) (E.lift n γ)‖) ≤ M := by
  filter_upwards
    [E.normalizedDftFunction_finiteFejerKernel_at_lift_eventually_eq_coeff
      Q γ] with n hn
  rw [hn]
  exact hM

lemma finiteFejerKernelAverage_eventually_eq_one
    (E : CayleyExtraction S) (Q : Finset E.Group) (hQ : Q ≠ ∅) :
    ∀ᶠ n in atTop, E.finiteFejerKernelAverage Q n = 1 := by
  let P : E.TrigPoly := E.fejerTrigPoly Q
  filter_upwards
    [E.finiteFejerKernelAverage_eventually_eq Q,
      TrigPoly.finiteAverage_eventually_eq_zeroCoeff E P] with n hkernel hpoly
  rw [hkernel, hpoly]
  exact E.fejerTrigPoly_compactAverage_eq_one_of_nonempty Q hQ

lemma compactFejerKernel_re_nonneg
    (E : CayleyExtraction S) (Q : Finset E.Group)
    (z : E.CompactDual) :
    0 ≤ (E.compactFejerKernel Q z).re := by
  unfold compactFejerKernel
  set w : ℂ := ∑ γ ∈ Q, E.characterValue z γ
  have hnonneg : 0 ≤ ((Q.card : ℝ)⁻¹) :=
    inv_nonneg.mpr (Nat.cast_nonneg Q.card)
  rw [← Complex.ofReal_natCast, ← Complex.ofReal_inv]
  rw [show star w = conj w by rfl, Complex.mul_conj]
  simp only [ofReal_inv, ofReal_natCast, mul_re, inv_re, natCast_re, normSq_natCast,
    div_self_mul_self', ofReal_re, inv_im, natCast_im, neg_zero, zero_div, ofReal_im,
    mul_zero, sub_zero, ge_iff_le]
  exact mul_nonneg hnonneg (Complex.normSq_nonneg w)

lemma compactFejerKernel_im_eq_zero
    (E : CayleyExtraction S) (Q : Finset E.Group)
    (z : E.CompactDual) :
    (E.compactFejerKernel Q z).im = 0 := by
  unfold compactFejerKernel
  set w : ℂ := ∑ γ ∈ Q, E.characterValue z γ
  rw [← Complex.ofReal_natCast, ← Complex.ofReal_inv]
  rw [show star w = conj w by rfl, Complex.mul_conj]
  simp [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im]

lemma compactAddFejerKernel_re_nonneg
    (E : CayleyExtraction S) (Q : Finset E.Group)
    (z : E.CompactAddDual) :
    0 ≤ (E.compactAddFejerKernel Q z).re := by
  simpa [compactAddFejerKernel] using E.compactFejerKernel_re_nonneg Q z.toMul

lemma compactAddFejerKernel_im_eq_zero
    (E : CayleyExtraction S) (Q : Finset E.Group)
    (z : E.CompactAddDual) :
    (E.compactAddFejerKernel Q z).im = 0 := by
  simpa [compactAddFejerKernel] using E.compactFejerKernel_im_eq_zero Q z.toMul

lemma finiteFejerKernel_re_nonneg
    (E : CayleyExtraction S) (Q : Finset E.Group) (n : ℕ)
    (x : ZMod (S.p (E.φ n))) :
    0 ≤ (E.finiteFejerKernel Q n x).re := by
  haveI : NeZero (S.p (E.φ n)) := ⟨(S.prime (E.φ n)).ne_zero⟩
  unfold finiteFejerKernel
  set w : ℂ := ∑ γ ∈ Q, ZMod.stdAddChar (-(E.lift n γ * x))
  change 0 ≤ (((Q.card : ℂ)⁻¹) * (w * star w)).re
  have hnonneg : 0 ≤ ((Q.card : ℝ)⁻¹) :=
    inv_nonneg.mpr (Nat.cast_nonneg Q.card)
  rw [← Complex.ofReal_natCast, ← Complex.ofReal_inv]
  rw [show star w = conj w by rfl, Complex.mul_conj]
  simp only [ofReal_inv, ofReal_natCast, mul_re, inv_re, natCast_re, normSq_natCast,
    div_self_mul_self', ofReal_re, inv_im, natCast_im, neg_zero, zero_div, ofReal_im,
    mul_zero, sub_zero, ge_iff_le]
  exact mul_nonneg hnonneg (Complex.normSq_nonneg w)

lemma finiteFejerKernel_im_eq_zero
    (E : CayleyExtraction S) (Q : Finset E.Group) (n : ℕ)
    (x : ZMod (S.p (E.φ n))) :
    (E.finiteFejerKernel Q n x).im = 0 := by
  haveI : NeZero (S.p (E.φ n)) := ⟨(S.prime (E.φ n)).ne_zero⟩
  unfold finiteFejerKernel
  set w : ℂ := ∑ γ ∈ Q, ZMod.stdAddChar (-(E.lift n γ * x))
  change (((Q.card : ℂ)⁻¹) * (w * star w)).im = 0
  rw [← Complex.ofReal_natCast, ← Complex.ofReal_inv]
  rw [show star w = conj w by rfl, Complex.mul_conj]
  simp [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im]

lemma shiftedFiniteFejerKernel_re_nonneg
    (E : CayleyExtraction S) (Q : Finset E.Group) (z : E.CompactAddDual)
    (n : ℕ) (x : ZMod (S.p (E.φ n))) :
    0 ≤ (E.shiftedFiniteFejerKernel Q z n x).re := by
  haveI : NeZero (S.p (E.φ n)) := ⟨(S.prime (E.φ n)).ne_zero⟩
  unfold shiftedFiniteFejerKernel
  set w : ℂ := ∑ γ ∈ Q,
    E.addCharacterValue z γ * ZMod.stdAddChar (-(E.lift n γ * x))
  change 0 ≤ (((Q.card : ℂ)⁻¹) * (w * star w)).re
  have hnonneg : 0 ≤ ((Q.card : ℝ)⁻¹) :=
    inv_nonneg.mpr (Nat.cast_nonneg Q.card)
  rw [← Complex.ofReal_natCast, ← Complex.ofReal_inv]
  rw [show star w = conj w by rfl, Complex.mul_conj]
  simp only [ofReal_inv, ofReal_natCast, mul_re, inv_re, natCast_re, normSq_natCast,
    div_self_mul_self', ofReal_re, inv_im, natCast_im, neg_zero, zero_div, ofReal_im,
    mul_zero, sub_zero, ge_iff_le]
  exact mul_nonneg hnonneg (Complex.normSq_nonneg w)

lemma shiftedFiniteFejerKernel_im_eq_zero
    (E : CayleyExtraction S) (Q : Finset E.Group) (z : E.CompactAddDual)
    (n : ℕ) (x : ZMod (S.p (E.φ n))) :
    (E.shiftedFiniteFejerKernel Q z n x).im = 0 := by
  haveI : NeZero (S.p (E.φ n)) := ⟨(S.prime (E.φ n)).ne_zero⟩
  unfold shiftedFiniteFejerKernel
  set w : ℂ := ∑ γ ∈ Q,
    E.addCharacterValue z γ * ZMod.stdAddChar (-(E.lift n γ * x))
  change (((Q.card : ℂ)⁻¹) * (w * star w)).im = 0
  rw [← Complex.ofReal_natCast, ← Complex.ofReal_inv]
  rw [show star w = conj w by rfl, Complex.mul_conj]
  simp [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im]

end CayleyExtraction

end

end Erdos42.CompactCayley


/-! =============================================================
    Section from: Erdos/P42/CompactCayley/Smoothing.lean
    ============================================================= -/

/-
Erdős Problem 42 — finite Fejér smoothing for compact-Cayley extraction.
-/


namespace Erdos42.CompactCayley

open Filter Complex MeasureTheory
open scoped BigOperators Topology

noncomputable section

/-- Normalized convolution on `ZMod p`. -/
noncomputable def avgConvolution {p : ℕ} [NeZero p]
    (f g : ZMod p → ℂ) : ZMod p → ℂ :=
  fun x => avgZMod fun y => f (x - y) * g y

lemma stdAddChar_neg_mul_split_sub
    {p : ℕ} [NeZero p] (x y r : ZMod p) :
    ZMod.stdAddChar (-(x * r)) =
      ZMod.stdAddChar (-((x - y) * r)) *
        ZMod.stdAddChar (-(y * r)) := by
  rw [← ZMod.stdAddChar.map_add_eq_mul]
  congr 1
  ring

lemma normalizedDftFunction_eq_avgZMod {p : ℕ} [NeZero p]
    (f : ZMod p → ℂ) (r : ZMod p) :
    normalizedDftFunction f r =
      avgZMod fun x : ZMod p => ZMod.stdAddChar (-(x * r)) * f x := by
  rw [normalizedDftFunction_eq_sum]
  rfl

lemma avgZMod_comm {p : ℕ} [NeZero p] (F : ZMod p → ZMod p → ℂ) :
    avgZMod (fun x => avgZMod fun y => F x y) =
      avgZMod (fun y => avgZMod fun x => F x y) := by
  unfold avgZMod
  calc
    ((p : ℂ)⁻¹) * ∑ x : ZMod p, ((p : ℂ)⁻¹) * ∑ y : ZMod p, F x y
        = ((p : ℂ)⁻¹) * ((p : ℂ)⁻¹) *
            ∑ x : ZMod p, ∑ y : ZMod p, F x y := by
          rw [← Finset.mul_sum]
          ring
    _ = ((p : ℂ)⁻¹) * ((p : ℂ)⁻¹) *
          ∑ y : ZMod p, ∑ x : ZMod p, F x y := by
          rw [Finset.sum_comm]
    _ = ((p : ℂ)⁻¹) * ∑ y : ZMod p, ((p : ℂ)⁻¹) *
          ∑ x : ZMod p, F x y := by
          rw [← Finset.mul_sum]
          ring

lemma avgZMod_sub_right {p : ℕ} [NeZero p]
    (f : ZMod p → ℂ) (y : ZMod p) :
    avgZMod (fun x => f (x - y)) = avgZMod f := by
  unfold avgZMod
  apply congrArg (fun S : ℂ => ((p : ℂ)⁻¹) * S)
  refine Fintype.sum_equiv (Equiv.addRight (-y)) _ _ ?_
  intro x
  simp [sub_eq_add_neg]

lemma avgZMod_re {p : ℕ} [NeZero p] (f : ZMod p → ℂ) :
    (avgZMod f).re = ((p : ℝ)⁻¹) * ∑ x : ZMod p, (f x).re := by
  unfold avgZMod
  rw [show ((p : ℂ)⁻¹) = (((p : ℝ)⁻¹ : ℝ) : ℂ) by
    rw [← Complex.ofReal_natCast, ← Complex.ofReal_inv]]
  simp [Complex.mul_re]

lemma avgZMod_re_le {p : ℕ} [NeZero p] {f g : ZMod p → ℂ}
    (h : ∀ x, (f x).re ≤ (g x).re) :
    (avgZMod f).re ≤ (avgZMod g).re := by
  rw [avgZMod_re f, avgZMod_re g]
  exact mul_le_mul_of_nonneg_left
    (Finset.sum_le_sum fun x _hx => h x)
    (inv_nonneg.mpr (Nat.cast_nonneg p))

/-- Normalized DFT sends normalized convolution to pointwise multiplication. -/
lemma normalizedDftFunction_avgConvolution {p : ℕ} [NeZero p]
    (f g : ZMod p → ℂ) (r : ZMod p) :
    normalizedDftFunction (avgConvolution f g) r =
      normalizedDftFunction f r * normalizedDftFunction g r := by
  classical
  rw [normalizedDftFunction_eq_avgZMod]
  unfold avgConvolution
  calc
    avgZMod
        (fun x : ZMod p =>
          ZMod.stdAddChar (-(x * r)) *
            avgZMod (fun y : ZMod p => f (x - y) * g y))
        =
      avgZMod
        (fun x : ZMod p =>
          avgZMod
            (fun y : ZMod p =>
              ZMod.stdAddChar (-(x * r)) * (f (x - y) * g y))) := by
          congr 1
          funext x
          rw [avgZMod_const_mul]
    _ =
      avgZMod
        (fun y : ZMod p =>
          avgZMod
            (fun x : ZMod p =>
              ZMod.stdAddChar (-(x * r)) * (f (x - y) * g y))) := by
          exact avgZMod_comm
            (fun x y : ZMod p =>
              ZMod.stdAddChar (-(x * r)) * (f (x - y) * g y))
    _ =
      avgZMod
        (fun y : ZMod p =>
          normalizedDftFunction f r *
            (ZMod.stdAddChar (-(y * r)) * g y)) := by
          congr 1
          funext y
          calc
            avgZMod
                (fun x : ZMod p =>
                  ZMod.stdAddChar (-(x * r)) * (f (x - y) * g y))
                =
              avgZMod
                (fun x : ZMod p =>
                  (ZMod.stdAddChar (-((x - y) * r)) * f (x - y)) *
                    (ZMod.stdAddChar (-(y * r)) * g y)) := by
                congr 1
                funext x
                rw [stdAddChar_neg_mul_split_sub x y r]
                ring
            _ =
              avgZMod
                (fun x : ZMod p =>
                  ZMod.stdAddChar (-((x - y) * r)) * f (x - y)) *
                (ZMod.stdAddChar (-(y * r)) * g y) := by
                rw [avgZMod_mul_const]
            _ =
              normalizedDftFunction f r *
                (ZMod.stdAddChar (-(y * r)) * g y) := by
                have hshift :
                    avgZMod
                        (fun x : ZMod p =>
                          ZMod.stdAddChar (-((x - y) * r)) * f (x - y)) =
                      normalizedDftFunction f r := by
                  rw [avgZMod_sub_right
                    (fun z : ZMod p => ZMod.stdAddChar (-(z * r)) * f z) y]
                  rw [← normalizedDftFunction_eq_avgZMod]
                rw [hshift]
    _ = normalizedDftFunction f r * normalizedDftFunction g r := by
          rw [avgZMod_const_mul]
          rw [← normalizedDftFunction_eq_avgZMod]

lemma norm_normalizedDftFunction_le_norm_average
    {p : ℕ} [NeZero p] (f : ZMod p → ℂ) (r : ZMod p) :
    ‖normalizedDftFunction f r‖ ≤
      ((p : ℝ)⁻¹) * ∑ x : ZMod p, ‖f x‖ := by
  rw [normalizedDftFunction_eq_avgZMod]
  unfold avgZMod
  calc
    ‖((p : ℂ)⁻¹) *
        ∑ x : ZMod p, ZMod.stdAddChar (-(x * r)) * f x‖
        = ‖((p : ℂ)⁻¹)‖ *
            ‖∑ x : ZMod p, ZMod.stdAddChar (-(x * r)) * f x‖ := by
          rw [norm_mul]
    _ ≤ ‖((p : ℂ)⁻¹)‖ *
        ∑ x : ZMod p, ‖ZMod.stdAddChar (-(x * r)) * f x‖ := by
          exact mul_le_mul_of_nonneg_left (norm_sum_le _ _) (norm_nonneg _)
    _ = ‖((p : ℂ)⁻¹)‖ * ∑ x : ZMod p, ‖f x‖ := by
          congr 1
          refine Finset.sum_congr rfl ?_
          intro x _hx
          rw [norm_mul, AddChar.norm_apply, one_mul]
    _ = ((p : ℝ)⁻¹) * ∑ x : ZMod p, ‖f x‖ := by
          rw [norm_inv, Complex.norm_natCast]

lemma norm_avgConvolution_indicator_le_of_kernel_norm_average_le_one
    {p : ℕ} [NeZero p] (T : Finset (ZMod p)) (K : ZMod p → ℂ)
    (hK_norm_avg : ((p : ℝ)⁻¹) * ∑ y : ZMod p, ‖K y‖ ≤ 1) :
    ∀ x : ZMod p, ‖avgConvolution (indicatorC T) K x‖ ≤ 1 := by
  intro x
  unfold avgConvolution avgZMod
  have hsum :
      ‖∑ y : ZMod p, indicatorC T (x - y) * K y‖ ≤
        ∑ y : ZMod p, ‖K y‖ := by
    calc
      ‖∑ y : ZMod p, indicatorC T (x - y) * K y‖
          ≤ ∑ y : ZMod p, ‖indicatorC T (x - y) * K y‖ := norm_sum_le _ _
      _ ≤ ∑ y : ZMod p, ‖K y‖ := by
          refine Finset.sum_le_sum ?_
          intro y _hy
          rw [norm_mul]
          have hind : ‖indicatorC T (x - y)‖ ≤ 1 := by
            classical
            by_cases h : x - y ∈ T
            · simp [indicatorC, h]
            · simp [indicatorC, h]
          exact mul_le_of_le_one_left (norm_nonneg _) hind
  calc
    ‖(↑p)⁻¹ * ∑ y : ZMod p, indicatorC T (x - y) * K y‖
        = ‖((p : ℂ)⁻¹)‖ *
            ‖∑ y : ZMod p, indicatorC T (x - y) * K y‖ := by
          rw [norm_mul]
    _ ≤ ‖((p : ℂ)⁻¹)‖ * ∑ y : ZMod p, ‖K y‖ :=
          mul_le_mul_of_nonneg_left hsum (norm_nonneg _)
    _ = ((p : ℝ)⁻¹) * ∑ y : ZMod p, ‖K y‖ := by
          rw [norm_inv, Complex.norm_natCast]
    _ ≤ 1 := hK_norm_avg

lemma kernel_norm_average_eq_one_of_real_nonneg_avg_one
    {p : ℕ} [NeZero p] (K : ZMod p → ℂ)
    (hK_nonneg : ∀ y, 0 ≤ (K y).re)
    (hK_im : ∀ y, (K y).im = 0)
    (hK_avg : avgZMod K = 1) :
    ((p : ℝ)⁻¹) * ∑ y : ZMod p, ‖K y‖ = 1 := by
  have hsum_eq :
      (∑ y : ZMod p, K y) =
        ((∑ y : ZMod p, (K y).re : ℝ) : ℂ) := by
    apply Complex.ext
    · simp [Complex.re_sum]
    · simp [Complex.im_sum, hK_im]
  have havg_re :
      ((p : ℝ)⁻¹) * ∑ y : ZMod p, (K y).re = 1 := by
    have h := congrArg Complex.re hK_avg
    unfold avgZMod at h
    rw [hsum_eq] at h
    rw [← Complex.ofReal_natCast, ← Complex.ofReal_inv] at h
    simpa [Complex.ofReal_mul] using h
  calc
    ((p : ℝ)⁻¹) * ∑ y : ZMod p, ‖K y‖
        = ((p : ℝ)⁻¹) * ∑ y : ZMod p, (K y).re := by
          congr 1
          refine Finset.sum_congr rfl ?_
          intro y _hy
          have hnorm := (Complex.abs_re_eq_norm).mpr (hK_im y)
          rw [← hnorm, abs_of_nonneg (hK_nonneg y)]
    _ = 1 := havg_re

lemma norm_avgConvolution_indicator_le_of_kernel_real_nonneg_avg_one
    {p : ℕ} [NeZero p] (T : Finset (ZMod p)) (K : ZMod p → ℂ)
    (hK_nonneg : ∀ y, 0 ≤ (K y).re)
    (hK_im : ∀ y, (K y).im = 0)
    (hK_avg : avgZMod K = 1) :
    ∀ x : ZMod p, ‖avgConvolution (indicatorC T) K x‖ ≤ 1 :=
  norm_avgConvolution_indicator_le_of_kernel_norm_average_le_one T K
    ((kernel_norm_average_eq_one_of_real_nonneg_avg_one
      K hK_nonneg hK_im hK_avg).le)

lemma norm_normalizedDftFunction_le_one_of_kernel_real_nonneg_avg_one
    {p : ℕ} [NeZero p] (K : ZMod p → ℂ)
    (hK_nonneg : ∀ y, 0 ≤ (K y).re)
    (hK_im : ∀ y, (K y).im = 0)
    (hK_avg : avgZMod K = 1)
    (r : ZMod p) :
    ‖normalizedDftFunction K r‖ ≤ 1 :=
  (norm_normalizedDftFunction_le_norm_average K r).trans_eq
    (kernel_norm_average_eq_one_of_real_nonneg_avg_one
      K hK_nonneg hK_im hK_avg)

namespace CayleyExtraction

variable {ℓ : ℕ} {η : ℝ} {S : CayleyCounterSeq ℓ η}

/-- Finite Fejér-smoothed Cayley allowed kernel `1_T * K_Q`. -/
noncomputable def finiteSmooth
    (E : CayleyExtraction S) (Q : Finset E.Group) (n : ℕ) :
    ZMod (S.p (E.φ n)) → ℂ :=
  letI : NeZero (S.p (E.φ n)) := ⟨(S.prime (E.φ n)).ne_zero⟩
  avgConvolution (indicatorC (S.T (E.φ n))) (E.finiteFejerKernel Q n)

/-- Finite average of the complement indicator `1 - 1_T` weighted by a Fejér
kernel.  This is the finite inequality input for summability of `gCoeff`. -/
noncomputable def finiteComplementFejerAverage
    (E : CayleyExtraction S) (Q : Finset E.Group) (n : ℕ) : ℂ :=
  letI : NeZero (S.p (E.φ n)) := ⟨(S.prime (E.φ n)).ne_zero⟩
  avgZMod fun x : ZMod (S.p (E.φ n)) =>
    (1 - indicatorC (S.T (E.φ n)) x) * E.finiteFejerKernel Q n x

/-- Finite average of the complement indicator `1 - 1_T` weighted by an
arbitrary lifted trigonometric polynomial. -/
noncomputable def finiteComplementWeightedAverage
    (E : CayleyExtraction S) (P : E.TrigPoly) (n : ℕ) : ℂ :=
  letI : NeZero (S.p (E.φ n)) := ⟨(S.prime (E.φ n)).ne_zero⟩
  avgZMod fun x : ZMod (S.p (E.φ n)) =>
    (1 - indicatorC (S.T (E.φ n)) x) * TrigPoly.evalFinite P n x

lemma finiteComplementWeightedAverage_eventually_eq
    (E : CayleyExtraction S) (P : E.TrigPoly) :
    ∀ᶠ n in atTop,
      E.finiteComplementWeightedAverage P n =
        TrigPoly.finiteAverage P n -
          TrigPoly.indicatorWeightedFiniteAverage P n := by
  filter_upwards with n
  haveI : NeZero (S.p (E.φ n)) := ⟨(S.prime (E.φ n)).ne_zero⟩
  unfold finiteComplementWeightedAverage TrigPoly.finiteAverage
    TrigPoly.indicatorWeightedFiniteAverage
  calc
    avgZMod (fun x : ZMod (S.p (E.φ n)) =>
        (1 - indicatorC (S.T (E.φ n)) x) * TrigPoly.evalFinite P n x)
        =
      avgZMod (fun x : ZMod (S.p (E.φ n)) =>
        TrigPoly.evalFinite P n x -
          indicatorC (S.T (E.φ n)) x * TrigPoly.evalFinite P n x) := by
        congr 1
        funext x
        ring
    _ =
      avgZMod (fun x : ZMod (S.p (E.φ n)) =>
        TrigPoly.evalFinite P n x) -
      avgZMod (fun x : ZMod (S.p (E.φ n)) =>
        indicatorC (S.T (E.φ n)) x * TrigPoly.evalFinite P n x) := by
        unfold avgZMod
        rw [Finset.sum_sub_distrib]
        ring

lemma finiteComplementWeightedAverage_tendsto
    (E : CayleyExtraction S) (P : E.TrigPoly) :
    Tendsto
      (fun n => E.finiteComplementWeightedAverage P n)
      atTop
      (𝓝 (TrigPoly.compactAverage P -
        TrigPoly.indicatorCoeffFunctional P)) := by
  have hdiff :=
    (TrigPoly.finiteAverage_tendsto_compactAverage E P).sub
      (TrigPoly.indicatorWeightedFiniteAverage_tendsto_coeffFunctional E P)
  exact hdiff.congr'
    (by
      filter_upwards [E.finiteComplementWeightedAverage_eventually_eq P] with n hn
      exact hn.symm)

lemma finiteComplementWeightedAverage_re_nonneg
    (E : CayleyExtraction S) (P : E.TrigPoly) (n : ℕ)
    (hP : ∀ x : ZMod (S.p (E.φ n)),
      0 ≤ (TrigPoly.evalFinite P n x).re) :
    0 ≤ (E.finiteComplementWeightedAverage P n).re := by
  haveI : NeZero (S.p (E.φ n)) := ⟨(S.prime (E.φ n)).ne_zero⟩
  rw [finiteComplementWeightedAverage, avgZMod_re]
  refine mul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg _)) ?_
  refine Finset.sum_nonneg ?_
  intro x _hx
  by_cases hx : x ∈ S.T (E.φ n)
  · simp [indicatorC, hx]
  · simpa [indicatorC, hx] using hP x

lemma shiftedFejer_complementFunctional_re_nonneg
    (E : CayleyExtraction S) (Q : Finset E.Group) (z : E.CompactAddDual) :
    0 ≤
      (TrigPoly.compactAverage (E.shiftedFejerTrigPoly Q z) -
        TrigPoly.indicatorCoeffFunctional (E.shiftedFejerTrigPoly Q z)).re := by
  let P : E.TrigPoly := E.shiftedFejerTrigPoly Q z
  have htendsto :=
    E.finiteComplementWeightedAverage_tendsto P
  have htendsto_re :=
    Complex.continuous_re.tendsto
      (TrigPoly.compactAverage P - TrigPoly.indicatorCoeffFunctional P) |>.comp
      htendsto
  have hnonneg :
      ∀ᶠ n in atTop, 0 ≤ (E.finiteComplementWeightedAverage P n).re := by
    filter_upwards [E.shiftedFejerTrigPoly_evalFinite_eventually_eq Q z] with n hn
    exact E.finiteComplementWeightedAverage_re_nonneg P n (by
      intro x
      simpa [P, hn x] using E.shiftedFiniteFejerKernel_re_nonneg Q z n x)
  exact le_of_tendsto_of_tendsto tendsto_const_nhds htendsto_re hnonneg

lemma finiteComplementFejerAverage_eventually_eq
    (E : CayleyExtraction S) (Q : Finset E.Group) :
    ∀ᶠ n in atTop,
      E.finiteComplementFejerAverage Q n =
        TrigPoly.finiteAverage (E.fejerTrigPoly Q) n -
          TrigPoly.indicatorWeightedFiniteAverage (E.fejerTrigPoly Q) n := by
  filter_upwards [E.fejerTrigPoly_evalFinite_eventually_eq Q] with n hn
  haveI : NeZero (S.p (E.φ n)) := ⟨(S.prime (E.φ n)).ne_zero⟩
  unfold finiteComplementFejerAverage TrigPoly.finiteAverage
    TrigPoly.indicatorWeightedFiniteAverage
  calc
    avgZMod (fun x : ZMod (S.p (E.φ n)) =>
        (1 - indicatorC (S.T (E.φ n)) x) *
          E.finiteFejerKernel Q n x)
        =
      avgZMod (fun x : ZMod (S.p (E.φ n)) =>
        TrigPoly.evalFinite (E.fejerTrigPoly Q) n x -
          indicatorC (S.T (E.φ n)) x *
            TrigPoly.evalFinite (E.fejerTrigPoly Q) n x) := by
        congr 1
        funext x
        rw [hn x]
        ring
    _ =
      avgZMod (fun x : ZMod (S.p (E.φ n)) =>
        TrigPoly.evalFinite (E.fejerTrigPoly Q) n x) -
      avgZMod (fun x : ZMod (S.p (E.φ n)) =>
        indicatorC (S.T (E.φ n)) x *
          TrigPoly.evalFinite (E.fejerTrigPoly Q) n x) := by
        unfold avgZMod
        rw [Finset.sum_sub_distrib]
        ring

lemma finiteComplementFejerAverage_tendsto
    (E : CayleyExtraction S) (Q : Finset E.Group) :
    Tendsto
      (fun n => E.finiteComplementFejerAverage Q n)
      atTop
      (𝓝 (TrigPoly.compactAverage (E.fejerTrigPoly Q) -
        TrigPoly.indicatorCoeffFunctional (E.fejerTrigPoly Q))) := by
  have hdiff :=
    (TrigPoly.finiteAverage_tendsto_compactAverage E
      (E.fejerTrigPoly Q)).sub
      (TrigPoly.indicatorWeightedFiniteAverage_tendsto_coeffFunctional E
        (E.fejerTrigPoly Q))
  exact hdiff.congr'
    (by
      filter_upwards [E.finiteComplementFejerAverage_eventually_eq Q] with n hn
      exact hn.symm)

lemma finiteComplementFejerAverage_tendsto_one_sub_indicatorCoeffFunctional
    (E : CayleyExtraction S) (Q : Finset E.Group) (hQ : Q ≠ ∅) :
    Tendsto
      (fun n => E.finiteComplementFejerAverage Q n)
      atTop
      (𝓝 (1 - TrigPoly.indicatorCoeffFunctional (E.fejerTrigPoly Q))) := by
  simpa [E.fejerTrigPoly_compactAverage_eq_one_of_nonempty Q hQ] using
    E.finiteComplementFejerAverage_tendsto Q

lemma finiteComplementFejerAverage_re_le_fejerAverage_re
    (E : CayleyExtraction S) (Q : Finset E.Group) (n : ℕ) :
    (E.finiteComplementFejerAverage Q n).re ≤
      (E.finiteFejerKernelAverage Q n).re := by
  haveI : NeZero (S.p (E.φ n)) := ⟨(S.prime (E.φ n)).ne_zero⟩
  unfold finiteComplementFejerAverage finiteFejerKernelAverage
  refine avgZMod_re_le ?_
  intro x
  by_cases hx : x ∈ S.T (E.φ n)
  · simp [indicatorC, hx, E.finiteFejerKernel_re_nonneg Q n x]
  · simp [indicatorC, hx]

lemma finiteComplementFejerAverage_re_le_one_eventually
    (E : CayleyExtraction S) (Q : Finset E.Group) (hQ : Q ≠ ∅) :
    ∀ᶠ n in atTop,
      (E.finiteComplementFejerAverage Q n).re ≤ 1 := by
  filter_upwards [E.finiteFejerKernelAverage_eventually_eq_one Q hQ] with n havg
  exact (E.finiteComplementFejerAverage_re_le_fejerAverage_re Q n).trans_eq
    (by simp [havg])

lemma finiteSmooth_norm_le_one_eventually
    (E : CayleyExtraction S) (Q : Finset E.Group) (hQ : Q ≠ ∅) :
    ∀ᶠ n in atTop,
      ∀ z : ZMod (S.p (E.φ n)), ‖E.finiteSmooth Q n z‖ ≤ 1 := by
  filter_upwards [E.finiteFejerKernelAverage_eventually_eq_one Q hQ] with n havg z
  haveI : NeZero (S.p (E.φ n)) := ⟨(S.prime (E.φ n)).ne_zero⟩
  refine norm_avgConvolution_indicator_le_of_kernel_real_nonneg_avg_one
    (S.T (E.φ n)) (E.finiteFejerKernel Q n)
    (E.finiteFejerKernel_re_nonneg Q n)
    (E.finiteFejerKernel_im_eq_zero Q n) ?_ z
  simpa [finiteFejerKernelAverage] using havg

lemma normalizedDftFunction_finiteSmooth
    (E : CayleyExtraction S) (Q : Finset E.Group) (n : ℕ)
    [NeZero (S.p (E.φ n))]
    (r : ZMod (S.p (E.φ n))) :
    normalizedDftFunction (E.finiteSmooth Q n) r =
      normalizedDftCoeff (S.T (E.φ n)) r *
        normalizedDftFunction (E.finiteFejerKernel Q n) r := by
  unfold finiteSmooth
  rw [normalizedDftFunction_avgConvolution]
  rfl

/-- For a fixed finite polynomial `P`, weight its lifted finite Fourier
coefficients by the finite indicator coefficients of the extracted cyclic
model. This is the finite polynomial model for Fejér smoothing. -/
noncomputable def finiteDftWeightedTrigPoly
    (E : CayleyExtraction S) (P : E.TrigPoly) (n : ℕ) : E.TrigPoly :=
  letI : NeZero (S.p (E.φ n)) := ⟨(S.prime (E.φ n)).ne_zero⟩
  P.sum fun γ c =>
    Finsupp.single γ
      (normalizedDftCoeff (S.T (E.φ n)) (-E.lift n γ) * c)

lemma finiteDftWeightedTrigPoly_add
    (E : CayleyExtraction S) (P R : E.TrigPoly) (n : ℕ) :
    E.finiteDftWeightedTrigPoly (P + R) n =
      E.finiteDftWeightedTrigPoly P n +
        E.finiteDftWeightedTrigPoly R n := by
  classical
  haveI : NeZero (S.p (E.φ n)) := ⟨(S.prime (E.φ n)).ne_zero⟩
  unfold finiteDftWeightedTrigPoly
  let h : E.Group → ℂ →+ E.TrigPoly := fun γ =>
    { toFun := fun c =>
        Finsupp.single γ
          (normalizedDftCoeff (S.T (E.φ n)) (-E.lift n γ) * c)
      map_zero' := by simp
      map_add' := by
        intro a b
        rw [mul_add, Finsupp.single_add] }
  change Finsupp.sum (P + R) (fun γ c => h γ c) =
    Finsupp.sum P (fun γ c => h γ c) +
      Finsupp.sum R (fun γ c => h γ c)
  rw [Finsupp.sum_hom_add_index]

lemma finiteDftWeightedTrigPoly_single
    (E : CayleyExtraction S) (γ : E.Group) (c : ℂ) (n : ℕ) :
    E.finiteDftWeightedTrigPoly (Finsupp.single γ c : E.TrigPoly) n =
      (letI : NeZero (S.p (E.φ n)) := ⟨(S.prime (E.φ n)).ne_zero⟩;
        Finsupp.single γ
          (normalizedDftCoeff (S.T (E.φ n)) (-E.lift n γ) * c)) := by
  classical
  haveI : NeZero (S.p (E.φ n)) := ⟨(S.prime (E.φ n)).ne_zero⟩
  unfold finiteDftWeightedTrigPoly
  rw [Finsupp.sum_single_index]
  simp

lemma finiteDftWeightedTrigPoly_apply
    (E : CayleyExtraction S) (P : E.TrigPoly) (n : ℕ) (γ : E.Group) :
    E.finiteDftWeightedTrigPoly P n γ =
      (letI : NeZero (S.p (E.φ n)) := ⟨(S.prime (E.φ n)).ne_zero⟩;
        normalizedDftCoeff (S.T (E.φ n)) (-E.lift n γ) * P γ) := by
  classical
  haveI : NeZero (S.p (E.φ n)) := ⟨(S.prime (E.φ n)).ne_zero⟩
  refine Finsupp.induction_linear P ?zero ?add ?single
  · simp [finiteDftWeightedTrigPoly]
  · intro P R hP hR
    rw [E.finiteDftWeightedTrigPoly_add P R n]
    simp [hP, hR, mul_add]
  · intro δ c
    rw [E.finiteDftWeightedTrigPoly_single δ c n]
    by_cases hδγ : δ = γ
    · subst hδγ
      simp
    · have hleft :
          (Finsupp.single δ
            (normalizedDftCoeff (S.T (E.φ n)) (-E.lift n δ) * c) :
              E.TrigPoly) γ = 0 :=
        Finsupp.single_eq_of_ne (Ne.symm hδγ)
      have hright : (Finsupp.single δ c : E.TrigPoly) γ = 0 :=
        Finsupp.single_eq_of_ne (Ne.symm hδγ)
      rw [hleft, hright]
      simp

lemma normalizedDftFunction_evalFinite_finiteDftWeightedTrigPoly
    (E : CayleyExtraction S) (P : E.TrigPoly) (n : ℕ)
    [Fact (S.p (E.φ n)).Prime] [NeZero (S.p (E.φ n))]
    (r : ZMod (S.p (E.φ n))) :
    normalizedDftFunction
        (fun x : ZMod (S.p (E.φ n)) =>
          TrigPoly.evalFinite (E.finiteDftWeightedTrigPoly P n) n x) r =
      normalizedDftCoeff (S.T (E.φ n)) r *
        (P.sum fun γ c => if r + E.lift n γ = 0 then c else 0) := by
  classical
  refine Finsupp.induction_linear P ?zero ?add ?single
  · simp [finiteDftWeightedTrigPoly, normalizedDftFunction_zero_fun]
  · intro P R hP hR
    rw [E.finiteDftWeightedTrigPoly_add P R n]
    have hfun :
        (fun x : ZMod (S.p (E.φ n)) =>
            TrigPoly.evalFinite (E.finiteDftWeightedTrigPoly P n +
              E.finiteDftWeightedTrigPoly R n) n x) =
          fun x =>
            TrigPoly.evalFinite (E.finiteDftWeightedTrigPoly P n) n x +
              TrigPoly.evalFinite (E.finiteDftWeightedTrigPoly R n) n x := by
      funext x
      exact TrigPoly.evalFinite_add
        (E.finiteDftWeightedTrigPoly P n)
        (E.finiteDftWeightedTrigPoly R n) n x
    rw [hfun, normalizedDftFunction_add, hP, hR]
    let h : E.Group → ℂ →+ ℂ := fun γ =>
      { toFun := fun c => if r + E.lift n γ = 0 then c else 0
        map_zero' := by by_cases hγ : r + E.lift n γ = 0 <;> simp [hγ]
        map_add' := by
          intro a b
          by_cases hγ : r + E.lift n γ = 0 <;> simp [hγ] }
    change normalizedDftCoeff (S.T (E.φ n)) r *
        Finsupp.sum P (fun γ c => h γ c) +
        normalizedDftCoeff (S.T (E.φ n)) r *
          Finsupp.sum R (fun γ c => h γ c) =
      normalizedDftCoeff (S.T (E.φ n)) r *
        Finsupp.sum (P + R) (fun γ c => h γ c)
    rw [Finsupp.sum_hom_add_index]
    ring
  · intro γ c
    rw [E.finiteDftWeightedTrigPoly_single γ c n]
    rw [TrigPoly.normalizedDftFunction_evalFinite_single]
    by_cases hγ : r + E.lift n γ = 0
    · have hr : r = -E.lift n γ := eq_neg_of_add_eq_zero_left hγ
      simp [hr]
    · simp [hγ]

/-- The finite trigonometric polynomial whose lifted evaluation is eventually
the fixed-`Q` finite Fejér-smoothed kernel. -/
noncomputable def finiteSmoothModelTrigPoly
    (E : CayleyExtraction S) (Q : Finset E.Group) (n : ℕ) : E.TrigPoly :=
  E.finiteDftWeightedTrigPoly (E.fejerTrigPoly Q) n

lemma finiteSmoothModelTrigPoly_apply
    (E : CayleyExtraction S) (Q : Finset E.Group) (n : ℕ) (γ : E.Group) :
    E.finiteSmoothModelTrigPoly Q n γ =
      (letI : NeZero (S.p (E.φ n)) := ⟨(S.prime (E.φ n)).ne_zero⟩;
        normalizedDftCoeff (S.T (E.φ n)) (-E.lift n γ) *
          (E.fejerTrigPoly Q) γ) := by
  simp [finiteSmoothModelTrigPoly, E.finiteDftWeightedTrigPoly_apply]

lemma finiteSmooth_eq_evalFinite_finiteSmoothModelTrigPoly_eventually
    (E : CayleyExtraction S) (Q : Finset E.Group) :
    ∀ᶠ n in atTop,
      ∀ x : ZMod (S.p (E.φ n)),
        E.finiteSmooth Q n x =
          TrigPoly.evalFinite (E.finiteSmoothModelTrigPoly Q n) n x := by
  filter_upwards
    [E.normalizedDftFunction_finiteFejerKernel_eventually_eq Q] with n hK x
  haveI : Fact (S.p (E.φ n)).Prime := ⟨S.prime (E.φ n)⟩
  haveI : NeZero (S.p (E.φ n)) := ⟨(S.prime (E.φ n)).ne_zero⟩
  rw [function_eq_sum_normalizedDftFunction (p := S.p (E.φ n))
      (E.finiteSmooth Q n) x]
  rw [function_eq_sum_normalizedDftFunction (p := S.p (E.φ n))
      (fun x : ZMod (S.p (E.φ n)) =>
        TrigPoly.evalFinite (E.finiteSmoothModelTrigPoly Q n) n x) x]
  refine Finset.sum_congr rfl ?_
  intro r _hr
  congr 1
  rw [E.normalizedDftFunction_finiteSmooth Q n r, hK r]
  rw [finiteSmoothModelTrigPoly,
    E.normalizedDftFunction_evalFinite_finiteDftWeightedTrigPoly
      (E.fejerTrigPoly Q) n r]

lemma normalizedDftFunction_indicator_sub_finiteSmooth
    (E : CayleyExtraction S) (Q : Finset E.Group) (n : ℕ)
    [NeZero (S.p (E.φ n))]
    (r : ZMod (S.p (E.φ n))) :
    normalizedDftFunction
        (fun z : ZMod (S.p (E.φ n)) =>
          indicatorC (S.T (E.φ n)) z - E.finiteSmooth Q n z) r =
      normalizedDftCoeff (S.T (E.φ n)) r *
        (1 - normalizedDftFunction (E.finiteFejerKernel Q n) r) := by
  rw [normalizedDftFunction_sub, E.normalizedDftFunction_finiteSmooth Q n r]
  simp [normalizedDftCoeff]
  ring

lemma normalizedDftFunction_finiteSmooth_at_lift_tendsto
    (E : CayleyExtraction S) (Q : Finset E.Group) (γ : E.Group) :
    Tendsto
      (fun n =>
        letI : NeZero (S.p (E.φ n)) := ⟨(S.prime (E.φ n)).ne_zero⟩;
        normalizedDftFunction (E.finiteSmooth Q n) (E.lift n γ))
      atTop
      (𝓝 (E.coeff γ * (E.fejerTrigPoly Q) (-γ))) := by
  have hT := E.coeff_tendsto γ
  have hK :
      Tendsto (fun _n : ℕ => (E.fejerTrigPoly Q) (-γ))
        atTop (𝓝 ((E.fejerTrigPoly Q) (-γ))) :=
    tendsto_const_nhds
  have hprod := hT.mul hK
  refine hprod.congr' ?_
  filter_upwards
    [E.normalizedDftFunction_finiteFejerKernel_at_lift_eventually_eq_coeff
      Q γ] with n hKcoeff
  haveI : NeZero (S.p (E.φ n)) := ⟨(S.prime (E.φ n)).ne_zero⟩
  rw [E.normalizedDftFunction_finiteSmooth Q n (E.lift n γ)]
  rw [hKcoeff]

/-- Compact-side trigonometric polynomial whose coefficients match the
fixed-`Q` Fejér-smoothed Cayley limit. -/
noncomputable def compactSmoothTrigPoly
    (E : CayleyExtraction S) (Q : Finset E.Group) : E.TrigPoly :=
  ∑ γ ∈ (E.fejerTrigPoly Q).support,
    Finsupp.single γ ((E.fejerTrigPoly Q) γ * E.coeff (-γ))

lemma compactSmoothTrigPoly_apply
    (E : CayleyExtraction S) (Q : Finset E.Group) (γ : E.Group) :
    E.compactSmoothTrigPoly Q γ =
      (E.fejerTrigPoly Q) γ * E.coeff (-γ) := by
  classical
  unfold compactSmoothTrigPoly
  rw [Finsupp.finsetSum_apply]
  by_cases hγ : γ ∈ (E.fejerTrigPoly Q).support
  · rw [Finset.sum_eq_single γ]
    · simp
    · intro δ hδ hδγ
      exact Finsupp.single_eq_of_ne (Ne.symm hδγ)
    · intro hnot
      exact (hnot hγ).elim
  · have hzero : (E.fejerTrigPoly Q) γ = 0 :=
      Finsupp.notMem_support_iff.mp hγ
    rw [Finset.sum_eq_zero]
    · rw [hzero]
      simp
    · intro δ hδ
      have hδγ : δ ≠ γ := by
        intro h
        subst h
        exact hγ hδ
      exact Finsupp.single_eq_of_ne (Ne.symm hδγ)

lemma finiteSmoothModelTrigPoly_apply_tendsto_compactSmoothTrigPoly
    (E : CayleyExtraction S) (Q : Finset E.Group) (γ : E.Group) :
    Tendsto
      (fun n => E.finiteSmoothModelTrigPoly Q n γ)
      atTop (𝓝 (E.compactSmoothTrigPoly Q γ)) := by
  have hcoeff := E.coeff_tendsto (-γ)
  have hcoeff' :
      Tendsto
        (fun n =>
          letI : NeZero (S.p (E.φ n)) := ⟨(S.prime (E.φ n)).ne_zero⟩;
          normalizedDftCoeff (S.T (E.φ n)) (-E.lift n γ))
        atTop (𝓝 (E.coeff (-γ))) := by
    refine hcoeff.congr' ?_
    filter_upwards [E.data.finiteLift_neg_eventually_eq γ] with n hneg
    haveI : NeZero (S.p (E.φ n)) := ⟨(S.prime (E.φ n)).ne_zero⟩
    simp [lift, hneg]
    rfl
  have hconst :
      Tendsto (fun _n : ℕ => (E.fejerTrigPoly Q) γ)
        atTop (𝓝 ((E.fejerTrigPoly Q) γ)) :=
    tendsto_const_nhds
  have hprod := hcoeff'.mul hconst
  have htarget :
      E.coeff (-γ) * (E.fejerTrigPoly Q γ) =
        E.compactSmoothTrigPoly Q γ := by
    rw [E.compactSmoothTrigPoly_apply Q γ]
    ring
  have hprod' := hprod.congr' (by
    filter_upwards with n
    exact (E.finiteSmoothModelTrigPoly_apply Q n γ).symm)
  simpa [htarget] using hprod'

/-- Compact finite-Fejér smoothing of the limiting allowed kernel, represented
by the fixed trigonometric polynomial whose coefficients are the limits of the
finite smoothed kernels. -/
noncomputable def compactSmooth
    (E : CayleyExtraction S) (Q : Finset E.Group) :
    E.CompactAddDual → ℂ :=
  fun z => TrigPoly.evalAdd (E.compactSmoothTrigPoly Q) z

noncomputable def compactSmoothReal
    (E : CayleyExtraction S) (Q : Finset E.Group) :
    E.CompactAddDual → ℝ :=
  fun z => (E.compactSmooth Q z).re

lemma TrigPoly.evalAdd_im_eq_zero_of_apply_neg_eq_self
    (E : CayleyExtraction S) (P : E.TrigPoly)
    (hneg : ∀ γ : E.Group, P (-γ) = P γ)
    (him : ∀ γ : E.Group, (P γ).im = 0)
    (z : E.CompactAddDual) :
    (TrigPoly.evalAdd P z).im = 0 := by
  classical
  have hsupport_neg : ∀ {γ : E.Group}, γ ∈ P.support → -γ ∈ P.support := by
    intro γ hγ
    rw [Finsupp.mem_support_iff] at hγ ⊢
    intro hzero
    have hPγ : P γ = 0 := by
      rw [← hneg γ, hzero]
    exact hγ hPγ
  have hsum :
      TrigPoly.evalAdd P z =
        ∑ γ ∈ P.support, P γ * E.addCharacterValue z γ := by
    unfold TrigPoly.evalAdd
    rw [Finsupp.sum_of_support_subset
      (f := P) (s := P.support) (by intro γ hγ; exact hγ)]
    intro γ _hγ
    simp
  have hstar : star (TrigPoly.evalAdd P z) = TrigPoly.evalAdd P z := by
    calc
      star (TrigPoly.evalAdd P z)
          = ∑ γ ∈ P.support, star (P γ * E.addCharacterValue z γ) := by
            rw [hsum]
            simp
      _ = ∑ γ ∈ P.support, P (-γ) * E.addCharacterValue z (-γ) := by
            refine Finset.sum_congr rfl ?_
            intro γ _hγ
            have hreal : star (P γ) = P γ := by
              simpa using (Complex.conj_eq_iff_im.mpr (him γ))
            rw [star_mul, E.star_addCharacterValue, hreal, ← hneg γ]
            ring
      _ = ∑ γ ∈ P.support, P γ * E.addCharacterValue z γ := by
            refine Finset.sum_bij (fun γ _hγ => -γ) ?mem ?inj ?surj ?eq
            · intro γ hγ
              exact hsupport_neg hγ
            · intro a _ha b _hb h
              exact neg_inj.mp h
            · intro b hb
              refine ⟨-b, hsupport_neg hb, ?_⟩
              simp
            · intro γ hγ
              simp
      _ = TrigPoly.evalAdd P z := hsum.symm
  exact Complex.conj_eq_iff_im.mp hstar

lemma compactSmoothTrigPoly_apply_neg
    (E : CayleyExtraction S) (Q : Finset E.Group) (γ : E.Group) :
    E.compactSmoothTrigPoly Q (-γ) = E.compactSmoothTrigPoly Q γ := by
  rw [E.compactSmoothTrigPoly_apply Q (-γ),
    E.compactSmoothTrigPoly_apply Q γ,
    E.fejerTrigPoly_apply_neg Q γ]
  simp [E.coeff_neg_eq γ]

lemma compactSmoothTrigPoly_apply_im_eq_zero
    (E : CayleyExtraction S) (Q : Finset E.Group) (γ : E.Group) :
    (E.compactSmoothTrigPoly Q γ).im = 0 := by
  rw [E.compactSmoothTrigPoly_apply Q γ]
  have hK : ((E.fejerTrigPoly Q) γ).im = 0 :=
    E.fejerTrigPoly_apply_im_eq_zero Q γ
  have hcoeff : (E.coeff (-γ)).im = 0 := E.coeff_im_eq_zero (-γ)
  simp [Complex.mul_im, hK, hcoeff]

lemma compactSmooth_im_eq_zero
    (E : CayleyExtraction S) (Q : Finset E.Group) (z : E.CompactAddDual) :
    (E.compactSmooth Q z).im = 0 := by
  exact TrigPoly.evalAdd_im_eq_zero_of_apply_neg_eq_self E
    (E.compactSmoothTrigPoly Q)
    (E.compactSmoothTrigPoly_apply_neg Q)
    (E.compactSmoothTrigPoly_apply_im_eq_zero Q) z

lemma compactSmooth_eq_ofReal_compactSmoothReal
    (E : CayleyExtraction S) (Q : Finset E.Group) (z : E.CompactAddDual) :
    E.compactSmooth Q z = (E.compactSmoothReal Q z : ℂ) := by
  apply Complex.ext
  · simp [compactSmoothReal]
  · simp [compactSmoothReal, E.compactSmooth_im_eq_zero Q z]

lemma compactSmooth_continuous
    (E : CayleyExtraction S) (Q : Finset E.Group) :
    Continuous (E.compactSmooth Q) :=
  TrigPoly.continuous_evalAdd E (E.compactSmoothTrigPoly Q)

lemma compactSmoothReal_continuous
    (E : CayleyExtraction S) (Q : Finset E.Group) :
    Continuous (E.compactSmoothReal Q) :=
  Complex.continuous_re.comp (E.compactSmooth_continuous Q)

lemma compactSmoothReal_eq_sum_support
    (E : CayleyExtraction S) (Q : Finset E.Group) (z : E.CompactAddDual) :
    E.compactSmoothReal Q z =
      ∑ γ ∈ (E.compactSmoothTrigPoly Q).support,
        ((E.fejerTrigPoly Q γ).re * (E.coeff γ).re *
          (E.addCharacterValue z γ).re) := by
  classical
  have hsum :
      TrigPoly.evalAdd (E.compactSmoothTrigPoly Q) z =
        ∑ γ ∈ (E.compactSmoothTrigPoly Q).support,
          E.compactSmoothTrigPoly Q γ * E.addCharacterValue z γ := by
    unfold TrigPoly.evalAdd
    rw [Finsupp.sum_of_support_subset
      (f := E.compactSmoothTrigPoly Q)
      (s := (E.compactSmoothTrigPoly Q).support) (by intro γ hγ; exact hγ)]
    intro γ _hγ
    simp
  unfold compactSmoothReal compactSmooth
  rw [hsum]
  change Complex.reAddGroupHom
      (∑ γ ∈ (E.compactSmoothTrigPoly Q).support,
        E.compactSmoothTrigPoly Q γ * E.addCharacterValue z γ) = _
  rw [map_sum]
  refine Finset.sum_congr rfl ?_
  intro γ hγ
  change (E.compactSmoothTrigPoly Q γ * E.addCharacterValue z γ).re =
    (E.fejerTrigPoly Q γ).re * (E.coeff γ).re *
      (E.addCharacterValue z γ).re
  rw [E.compactSmoothTrigPoly_apply Q γ, E.coeff_neg_eq γ]
  have hKim : ((E.fejerTrigPoly Q) γ).im = 0 :=
    E.fejerTrigPoly_apply_im_eq_zero Q γ
  have hAim : (E.coeff γ).im = 0 := E.coeff_im_eq_zero γ
  simp [Complex.mul_re, Complex.mul_im, hKim, hAim, mul_assoc]

lemma compactSmoothReal_eq_sum_of_support_subset
    (E : CayleyExtraction S) (Q : Finset E.Group) (z : E.CompactAddDual)
    (A : Finset E.Group) (hA : (E.compactSmoothTrigPoly Q).support ⊆ A) :
    E.compactSmoothReal Q z =
      ∑ γ ∈ A,
        ((E.fejerTrigPoly Q γ).re * (E.coeff γ).re *
          (E.addCharacterValue z γ).re) := by
  classical
  have hsum :
      TrigPoly.evalAdd (E.compactSmoothTrigPoly Q) z =
        ∑ γ ∈ A,
          E.compactSmoothTrigPoly Q γ * E.addCharacterValue z γ := by
    unfold TrigPoly.evalAdd
    rw [Finsupp.sum_of_support_subset
      (f := E.compactSmoothTrigPoly Q) (s := A) hA]
    intro γ _hγ
    simp
  unfold compactSmoothReal compactSmooth
  rw [hsum]
  change Complex.reAddGroupHom
      (∑ γ ∈ A,
        E.compactSmoothTrigPoly Q γ * E.addCharacterValue z γ) = _
  rw [map_sum]
  refine Finset.sum_congr rfl ?_
  intro γ hγ
  change (E.compactSmoothTrigPoly Q γ * E.addCharacterValue z γ).re =
    (E.fejerTrigPoly Q γ).re * (E.coeff γ).re *
      (E.addCharacterValue z γ).re
  rw [E.compactSmoothTrigPoly_apply Q γ, E.coeff_neg_eq γ]
  have hKim : ((E.fejerTrigPoly Q) γ).im = 0 :=
    E.fejerTrigPoly_apply_im_eq_zero Q γ
  have hAim : (E.coeff γ).im = 0 := E.coeff_im_eq_zero γ
  simp [Complex.mul_re, Complex.mul_im, hKim, hAim, mul_assoc]

lemma integral_compactSmooth
    (E : CayleyExtraction S) (Q : Finset E.Group) :
    ∫ z : E.CompactAddDual, E.compactSmooth Q z ∂E.haar =
      E.compactSmoothTrigPoly Q 0 := by
  simp [compactSmooth, TrigPoly.integral_evalAdd_eq_compactAverage,
    TrigPoly.compactAverage]

lemma integral_compactSmooth_eq_coeff_zero_of_nonempty
    (E : CayleyExtraction S) (Q : Finset E.Group) (hQ : Q ≠ ∅) :
    ∫ z : E.CompactAddDual, E.compactSmooth Q z ∂E.haar =
      E.coeff 0 := by
  rw [E.integral_compactSmooth Q]
  rw [E.compactSmoothTrigPoly_apply Q 0]
  have hfejer0 : (E.fejerTrigPoly Q) (0 : E.Group) = 1 :=
    E.fejerTrigPoly_compactAverage_eq_one_of_nonempty Q hQ
  simp [hfejer0]

lemma normalizedDftFunction_finiteSmooth_at_neg_lift_tendsto_compactCoeff
    (E : CayleyExtraction S) (Q : Finset E.Group) (γ : E.Group) :
    Tendsto
      (fun n =>
        letI : NeZero (S.p (E.φ n)) := ⟨(S.prime (E.φ n)).ne_zero⟩;
        normalizedDftFunction (E.finiteSmooth Q n) (-E.lift n γ))
      atTop (𝓝 (E.compactSmoothTrigPoly Q γ)) := by
  have ht := E.normalizedDftFunction_finiteSmooth_at_lift_tendsto Q (-γ)
  have htarget :
      E.coeff (-γ) * (E.fejerTrigPoly Q) γ =
        E.compactSmoothTrigPoly Q γ := by
    rw [E.compactSmoothTrigPoly_apply Q γ]
    ring
  have ht' :
      Tendsto
        (fun n =>
          letI : NeZero (S.p (E.φ n)) := ⟨(S.prime (E.φ n)).ne_zero⟩;
          normalizedDftFunction (E.finiteSmooth Q n) (-E.lift n γ))
        atTop (𝓝 (E.coeff (-γ) * (E.fejerTrigPoly Q) γ)) := by
    have heq :
        (fun n =>
          letI : NeZero (S.p (E.φ n)) := ⟨(S.prime (E.φ n)).ne_zero⟩;
          normalizedDftFunction (E.finiteSmooth Q n) (E.lift n (-γ))) =ᶠ[atTop]
        (fun n =>
          letI : NeZero (S.p (E.φ n)) := ⟨(S.prime (E.φ n)).ne_zero⟩;
          normalizedDftFunction (E.finiteSmooth Q n) (-E.lift n γ)) := by
      filter_upwards [E.data.finiteLift_neg_eventually_eq γ] with n hneg
      haveI : NeZero (S.p (E.φ n)) := ⟨(S.prime (E.φ n)).ne_zero⟩
      simp [lift, hneg]
      rfl
    have ht_simplified :
        Tendsto
          (fun n =>
            letI : NeZero (S.p (E.φ n)) := ⟨(S.prime (E.φ n)).ne_zero⟩;
            normalizedDftFunction (E.finiteSmooth Q n) (E.lift n (-γ)))
          atTop (𝓝 (E.coeff (-γ) * (E.fejerTrigPoly Q) γ)) := by
      simpa using ht
    exact ht_simplified.congr' heq
  simpa [htarget] using ht'

/-- Finite average pairing the smoothed Cayley kernel with a lifted fixed
trigonometric polynomial. -/
noncomputable def finiteSmoothWeightedAverage
    (E : CayleyExtraction S) (Q : Finset E.Group)
    (P : E.TrigPoly) (n : ℕ) : ℂ :=
  letI : NeZero (S.p (E.φ n)) := ⟨(S.prime (E.φ n)).ne_zero⟩
  avgZMod fun x : ZMod (S.p (E.φ n)) =>
    E.finiteSmooth Q n x * P.evalFinite n x

/-- Coefficient functional that is the fixed-`Q` limit of
`finiteSmoothWeightedAverage`. -/
noncomputable def smoothedCoeffFunctional
    (E : CayleyExtraction S) (Q : Finset E.Group)
    (P : E.TrigPoly) : ℂ :=
  P.sum fun γ c => c * (E.coeff γ * (E.fejerTrigPoly Q) (-γ))

lemma finiteSmoothWeightedAverage_add
    (E : CayleyExtraction S) (Q : Finset E.Group)
    (P R : E.TrigPoly) (n : ℕ) :
    E.finiteSmoothWeightedAverage Q (P + R) n =
      E.finiteSmoothWeightedAverage Q P n +
        E.finiteSmoothWeightedAverage Q R n := by
  haveI : NeZero (S.p (E.φ n)) := ⟨(S.prime (E.φ n)).ne_zero⟩
  unfold finiteSmoothWeightedAverage
  rw [show
      (fun x : ZMod (S.p (E.φ n)) =>
        E.finiteSmooth Q n x * TrigPoly.evalFinite (P + R) n x) =
      (fun x : ZMod (S.p (E.φ n)) =>
        E.finiteSmooth Q n x * TrigPoly.evalFinite P n x +
        E.finiteSmooth Q n x * TrigPoly.evalFinite R n x) by
        funext x
        rw [TrigPoly.evalFinite_add]
        ring]
  unfold avgZMod
  rw [Finset.sum_add_distrib, mul_add]

lemma finiteSmoothWeightedAverage_single
    (E : CayleyExtraction S) (Q : Finset E.Group)
    (γ : E.Group) (c : ℂ) (n : ℕ) :
    E.finiteSmoothWeightedAverage Q
        (Finsupp.single γ c : E.TrigPoly) n =
      (letI : NeZero (S.p (E.φ n)) := ⟨(S.prime (E.φ n)).ne_zero⟩;
        c * normalizedDftFunction (E.finiteSmooth Q n) (E.lift n γ)) := by
  haveI : NeZero (S.p (E.φ n)) := ⟨(S.prime (E.φ n)).ne_zero⟩
  unfold finiteSmoothWeightedAverage
  change avgZMod
      (fun x : ZMod (S.p (E.φ n)) =>
        E.finiteSmooth Q n x *
          TrigPoly.evalFinite
            (Finsupp.single γ c : E.TrigPoly) n x) =
    c * normalizedDftFunction (E.finiteSmooth Q n) (E.lift n γ)
  rw [show
      (fun x : ZMod (S.p (E.φ n)) =>
        E.finiteSmooth Q n x *
          TrigPoly.evalFinite
            (Finsupp.single γ c : E.TrigPoly) n x) =
      (fun x : ZMod (S.p (E.φ n)) =>
        c * (ZMod.stdAddChar (-(x * E.lift n γ)) *
          E.finiteSmooth Q n x)) by
        funext x
        simp [TrigPoly.evalFinite_single]
        ring_nf]
  rw [avgZMod_const_mul]
  rw [normalizedDftFunction_eq_avgZMod]

lemma smoothedCoeffFunctional_add
    (E : CayleyExtraction S) (Q : Finset E.Group)
    (P R : E.TrigPoly) :
    E.smoothedCoeffFunctional Q (P + R) =
      E.smoothedCoeffFunctional Q P +
        E.smoothedCoeffFunctional Q R := by
  unfold smoothedCoeffFunctional
  let h : E.Group → ℂ →+ ℂ := fun γ =>
    { toFun := fun c => c * (E.coeff γ * (E.fejerTrigPoly Q) (-γ))
      map_zero' := by simp
      map_add' := by intro a b; ring }
  change Finsupp.sum (P + R) (fun γ c => h γ c) =
    Finsupp.sum P (fun γ c => h γ c) +
      Finsupp.sum R (fun γ c => h γ c)
  rw [Finsupp.sum_hom_add_index]

@[simp]
lemma smoothedCoeffFunctional_zero
    (E : CayleyExtraction S) (Q : Finset E.Group) :
    E.smoothedCoeffFunctional Q (0 : E.TrigPoly) = 0 := by
  simp [smoothedCoeffFunctional]

lemma smoothedCoeffFunctional_single
    (E : CayleyExtraction S) (Q : Finset E.Group)
    (γ : E.Group) (c : ℂ) :
    E.smoothedCoeffFunctional Q (Finsupp.single γ c : E.TrigPoly) =
      c * (E.coeff γ * (E.fejerTrigPoly Q) (-γ)) := by
  simp [smoothedCoeffFunctional]

lemma compactSmooth_mul_evalAdd_integrable
    (E : CayleyExtraction S) (Q : Finset E.Group) (P : E.TrigPoly) :
    Integrable
      (fun z : E.CompactAddDual =>
        E.compactSmooth Q z * TrigPoly.evalAdd P z) E.haar :=
  ((E.compactSmooth_continuous Q).mul
      (TrigPoly.continuous_evalAdd E P)).integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)

lemma smoothedCoeffFunctional_eq_integral_compactSmooth_mul_evalAdd
    (E : CayleyExtraction S) (Q : Finset E.Group) (P : E.TrigPoly) :
    E.smoothedCoeffFunctional Q P =
      ∫ z : E.CompactAddDual,
        E.compactSmooth Q z * TrigPoly.evalAdd P z ∂E.haar := by
  refine Finsupp.induction_linear P ?zero ?add ?single
  · simp [smoothedCoeffFunctional]
  · intro P R hP hR
    rw [E.smoothedCoeffFunctional_add Q P R, hP, hR]
    rw [show
        (fun z : E.CompactAddDual =>
            E.compactSmooth Q z * TrigPoly.evalAdd (P + R) z) =
          fun z =>
            E.compactSmooth Q z * TrigPoly.evalAdd P z +
              E.compactSmooth Q z * TrigPoly.evalAdd R z by
        funext z
        rw [TrigPoly.evalAdd_add]
        ring]
    rw [integral_add (E.compactSmooth_mul_evalAdd_integrable Q P)
      (E.compactSmooth_mul_evalAdd_integrable Q R)]
  · intro γ c
    rw [E.smoothedCoeffFunctional_single Q γ c]
    rw [show
        (fun z : E.CompactAddDual =>
            E.compactSmooth Q z *
              TrigPoly.evalAdd (Finsupp.single γ c : E.TrigPoly) z) =
          fun z =>
            c * (TrigPoly.evalAdd (E.compactSmoothTrigPoly Q) z *
              E.addCharacterValue z γ) by
        funext z
        simp [compactSmooth]
        ring]
    rw [show
        (∫ z : E.CompactAddDual,
            c * (TrigPoly.evalAdd (E.compactSmoothTrigPoly Q) z *
              E.addCharacterValue z γ) ∂E.haar) =
          c * ∫ z : E.CompactAddDual,
            TrigPoly.evalAdd (E.compactSmoothTrigPoly Q) z *
              E.addCharacterValue z γ ∂E.haar by
      simpa using
        (integral_const_mul (μ := E.haar) c
          (fun z : E.CompactAddDual =>
            TrigPoly.evalAdd (E.compactSmoothTrigPoly Q) z *
              E.addCharacterValue z γ))]
    rw [TrigPoly.integral_evalAdd_mul_char E (E.compactSmoothTrigPoly Q) γ]
    rw [E.compactSmoothTrigPoly_apply Q (-γ)]
    have hnegneg : (-(-γ) : E.Group) = γ := by simp
    rw [hnegneg]
    ring

lemma finiteSmoothWeightedAverage_tendsto_coeffFunctional
    (E : CayleyExtraction S) (Q : Finset E.Group) (P : E.TrigPoly) :
    Tendsto
      (fun n => E.finiteSmoothWeightedAverage Q P n)
      atTop (𝓝 (E.smoothedCoeffFunctional Q P)) := by
  refine Finsupp.induction_linear P ?zero ?add ?single
  · rw [E.smoothedCoeffFunctional_zero Q]
    have hzero :
        (fun n => E.finiteSmoothWeightedAverage Q (0 : E.TrigPoly) n) =
          fun _n => (0 : ℂ) := by
      funext n
      haveI : NeZero (S.p (E.φ n)) := ⟨(S.prime (E.φ n)).ne_zero⟩
      simp [finiteSmoothWeightedAverage, avgZMod]
    rw [hzero]
    exact tendsto_const_nhds
  · intro P R hP hR
    rw [E.smoothedCoeffFunctional_add Q P R]
    exact (hP.add hR).congr' (Filter.Eventually.of_forall fun n => by
      exact (E.finiteSmoothWeightedAverage_add Q P R n).symm)
  · intro γ c
    rw [E.smoothedCoeffFunctional_single Q γ c]
    have hcoeff := E.normalizedDftFunction_finiteSmooth_at_lift_tendsto Q γ
    have hc : Tendsto (fun _ : ℕ => c) atTop (𝓝 c) :=
      tendsto_const_nhds
    have hmul := hc.mul hcoeff
    exact hmul.congr' (Filter.Eventually.of_forall fun n => by
      exact (E.finiteSmoothWeightedAverage_single Q γ c n).symm)

lemma finiteSmoothWeightedAverage_tendsto_integral_compactSmooth_mul_evalAdd
    (E : CayleyExtraction S) (Q : Finset E.Group) (P : E.TrigPoly) :
    Tendsto
      (fun n => E.finiteSmoothWeightedAverage Q P n)
      atTop
      (𝓝 (∫ z : E.CompactAddDual,
        E.compactSmooth Q z * TrigPoly.evalAdd P z ∂E.haar)) := by
  simpa [E.smoothedCoeffFunctional_eq_integral_compactSmooth_mul_evalAdd Q P]
    using E.finiteSmoothWeightedAverage_tendsto_coeffFunctional Q P

/-- Fejér smoothing is spectrally close to the original indicator once the
chosen Fejér polynomial is close to `1` on the extracted large-spectrum
generators.  The small-spectrum branch gives the explicit `2 / q` term. -/
lemma spectralBound_indicator_sub_finiteSmooth_eventually
    (E : CayleyExtraction S) (q : ℕ+) (Q : Finset E.Group) (hQ : Q ≠ ∅)
    {M : ℝ}
    (hM : ∀ γ ∈ E.data.largeSpectrumGenerators q,
      ‖1 - (E.fejerTrigPoly Q) (-γ)‖ ≤ M) :
    ∀ᶠ n in atTop,
      (letI : NeZero (S.p (E.φ n)) := ⟨(S.prime (E.φ n)).ne_zero⟩;
        SpectralBound
          (fun z : ZMod (S.p (E.φ n)) =>
            indicatorC (S.T (E.φ n)) z - E.finiteSmooth Q n z)
          (max (2 * ((q : ℝ)⁻¹ : ℝ)) M)) := by
  classical
  have hcovered := E.eventually_largeSpectrum_covered q
  have hfejerLarge :
      ∀ᶠ n in atTop,
        ∀ γ ∈ E.data.largeSpectrumGenerators q,
          (letI : NeZero (S.p (E.φ n)) := ⟨(S.prime (E.φ n)).ne_zero⟩;
            ‖1 - normalizedDftFunction (E.finiteFejerKernel Q n)
              (E.lift n γ)‖) ≤ M := by
    rw [(E.data.largeSpectrumGenerators q).eventually_all]
    intro γ hγ
    exact E.norm_one_sub_normalizedDftFunction_finiteFejerKernel_at_lift_eventually_le
      Q γ (hM γ hγ)
  have hfejerNorm :
      ∀ᶠ n in atTop,
        ∀ r : ZMod (S.p (E.φ n)),
          (letI : NeZero (S.p (E.φ n)) := ⟨(S.prime (E.φ n)).ne_zero⟩;
            ‖normalizedDftFunction (E.finiteFejerKernel Q n) r‖) ≤ 1 := by
    filter_upwards [E.finiteFejerKernelAverage_eventually_eq_one Q hQ] with n havg r
    haveI : NeZero (S.p (E.φ n)) := ⟨(S.prime (E.φ n)).ne_zero⟩
    refine norm_normalizedDftFunction_le_one_of_kernel_real_nonneg_avg_one
      (E.finiteFejerKernel Q n)
      (E.finiteFejerKernel_re_nonneg Q n)
      (E.finiteFejerKernel_im_eq_zero Q n) ?_ r
    simpa [finiteFejerKernelAverage] using havg
  filter_upwards [hcovered, hfejerLarge, hfejerNorm] with n hncover hnlarge hnnorm
  intro r
  haveI : NeZero (S.p (E.φ n)) := ⟨(S.prime (E.φ n)).ne_zero⟩
  rw [E.normalizedDftFunction_indicator_sub_finiteSmooth Q n r]
  by_cases hsmall :
      ‖normalizedDftCoeff (S.T (E.φ n)) r‖ ≤ ((q : ℝ)⁻¹ : ℝ)
  · have h1K :
        ‖1 - normalizedDftFunction (E.finiteFejerKernel Q n) r‖ ≤
          (2 : ℝ) := by
      calc
        ‖1 - normalizedDftFunction (E.finiteFejerKernel Q n) r‖
            ≤ ‖(1 : ℂ)‖ +
                ‖normalizedDftFunction (E.finiteFejerKernel Q n) r‖ :=
              norm_sub_le _ _
        _ ≤ 1 + 1 := by
              exact add_le_add (by norm_num) (hnnorm r)
        _ = (2 : ℝ) := by norm_num
    calc
      ‖normalizedDftCoeff (S.T (E.φ n)) r *
          (1 - normalizedDftFunction (E.finiteFejerKernel Q n) r)‖
          =
        ‖normalizedDftCoeff (S.T (E.φ n)) r‖ *
          ‖1 - normalizedDftFunction (E.finiteFejerKernel Q n) r‖ := by
          rw [norm_mul]
      _ ≤ ((q : ℝ)⁻¹ : ℝ) * 2 := by
          exact mul_le_mul hsmall h1K (norm_nonneg _) (by positivity)
      _ = 2 * ((q : ℝ)⁻¹ : ℝ) := by ring
      _ ≤ max (2 * ((q : ℝ)⁻¹ : ℝ)) M := le_max_left _ _
  · have hlarge :
        ((q : ℝ)⁻¹ : ℝ) <
          ‖normalizedDftCoeff (S.T (E.φ n)) r‖ := lt_of_not_ge hsmall
    rcases hncover r (by simpa using hlarge) with ⟨γ, hγ, hγr⟩
    have hK :
        ‖1 - normalizedDftFunction (E.finiteFejerKernel Q n) r‖ ≤ M := by
      simpa [hγr] using hnlarge γ hγ
    have hcoef_le :
        ‖normalizedDftCoeff (S.T (E.φ n)) r‖ ≤ 1 := by
      simpa [CayleyCounterSeq.toFourierSeq, FourierSeq.coeff,
        normalizedDftCoeff] using
        (S.toFourierSeq).norm_coeff_le_one (E.φ n) r
    calc
      ‖normalizedDftCoeff (S.T (E.φ n)) r *
          (1 - normalizedDftFunction (E.finiteFejerKernel Q n) r)‖
          =
        ‖normalizedDftCoeff (S.T (E.φ n)) r‖ *
          ‖1 - normalizedDftFunction (E.finiteFejerKernel Q n) r‖ := by
          rw [norm_mul]
      _ ≤ 1 * M := by
          exact mul_le_mul hcoef_le hK (norm_nonneg _) (by norm_num)
      _ = M := by ring
      _ ≤ max (2 * ((q : ℝ)⁻¹ : ℝ)) M := le_max_right _ _

lemma spectralBound_indicator_sub_finiteSmooth_eventually_of_negCoeffBound
    (E : CayleyExtraction S) (q : ℕ+) (Q : Finset E.Group) (hQ : Q ≠ ∅)
    {M : ℝ}
    (hM : E.FejerNegCoeffBound Q (E.data.largeSpectrumGenerators q) M) :
    ∀ᶠ n in atTop,
      (letI : NeZero (S.p (E.φ n)) := ⟨(S.prime (E.φ n)).ne_zero⟩;
        SpectralBound
          (fun z : ZMod (S.p (E.φ n)) =>
            indicatorC (S.T (E.φ n)) z - E.finiteSmooth Q n z)
          (max (2 * ((q : ℝ)⁻¹ : ℝ)) M)) :=
  E.spectralBound_indicator_sub_finiteSmooth_eventually q Q hQ hM

lemma spectralBound_indicator_sub_finiteSmooth_eventually_of_lowerBound_neg
    (E : CayleyExtraction S) (q : ℕ+) (Q : Finset E.Group) (hQ : Q ≠ ∅)
    {M : ℝ}
    (hM :
      E.FejerPairCoeffLowerBound Q
        ((E.data.largeSpectrumGenerators q).image Neg.neg) M) :
    ∀ᶠ n in atTop,
      (letI : NeZero (S.p (E.φ n)) := ⟨(S.prime (E.φ n)).ne_zero⟩;
        SpectralBound
          (fun z : ZMod (S.p (E.φ n)) =>
            indicatorC (S.T (E.φ n)) z - E.finiteSmooth Q n z)
          (max (2 * ((q : ℝ)⁻¹ : ℝ)) M)) :=
  E.spectralBound_indicator_sub_finiteSmooth_eventually_of_negCoeffBound q Q hQ
    (E.fejerNegCoeffBound_of_pairCoeffLowerBound_neg hQ hM)

end CayleyExtraction

end

end Erdos42.CompactCayley


/-! =============================================================
    Section from: Erdos/P42/CompactCayley/Folner.lean
    ============================================================= -/

/-
Erdős Problem 42 — finite Følner overlap infrastructure.

This file isolates the finite pair-count lower bound from the extraction
structure.  The later constructive box estimate can then be proved in a
standard free abelian model and transported back to finite generated
subgroups of the extraction group.
-/


namespace Erdos42.CompactCayley

open scoped BigOperators

noncomputable section

namespace PairCoeffLowerBound

variable {G H : Type*} [AddGroup G] [AddGroup H]

def addEquivEmbedding (e : G ≃+ H) : G ↪ H :=
  e.toEquiv.toEmbedding

def addMonoidHomEmbedding (f : G →+ H) (hf : Function.Injective f) : G ↪ H where
  toFun := f
  inj' := hf

private def addEquivPairEmbedding (e : G ≃+ H) : G × G ↪ H × H where
  toFun pair := (e pair.1, e pair.2)
  inj' := by
    intro pair pair' hpair
    exact Prod.ext
      (e.injective (congrArg Prod.fst hpair))
      (e.injective (congrArg Prod.snd hpair))

lemma pairFiber_card_map_addEquiv
    (e : G ≃+ H) (Q : Finset G) (γ : G) :
    (pairFiber (Q.map (addEquivEmbedding e))
        ((addEquivEmbedding e) γ)).card =
      (pairFiber Q γ).card := by
  classical
  have hleft :
      pairFiber (Q.map (addEquivEmbedding e)) ((addEquivEmbedding e) γ) =
        ((Q.map (addEquivEmbedding e)).product
          (Q.map (addEquivEmbedding e))).filter
          (fun pair : H × H => pair.1 - pair.2 =
            (addEquivEmbedding e) γ) := by
    ext pair
    simp [pairFiber]
  have hright :
      pairFiber Q γ =
        (Q.product Q).filter (fun pair : G × G => pair.1 - pair.2 = γ) := by
    ext pair
    simp [pairFiber]
  rw [hleft, hright]
  symm
  apply Finset.card_bij (fun pair _hpair => (e pair.1, e pair.2))
  · intro pair hpair
    rw [Finset.mem_filter] at hpair
    rw [Finset.mem_filter]
    constructor
    · apply Finset.mem_product.mpr
      have hprod := Finset.mem_product.mp hpair.1
      exact
        ⟨Finset.mem_map.mpr ⟨pair.1, hprod.1, rfl⟩,
          Finset.mem_map.mpr ⟨pair.2, hprod.2, rfl⟩⟩
    · have hdiff : e (pair.1 - pair.2) = e γ := congrArg e hpair.2
      simpa [addEquivEmbedding, e.map_sub] using hdiff
  · intro pair _hpair pair' _hpair' h
    exact Prod.ext
      (e.injective (congrArg Prod.fst h))
      (e.injective (congrArg Prod.snd h))
  · intro pair hpair
    rw [Finset.mem_filter] at hpair
    have hprod := Finset.mem_product.mp hpair.1
    rcases Finset.mem_map.mp hprod.1 with ⟨a, haQ, ha⟩
    rcases Finset.mem_map.mp hprod.2 with ⟨b, hbQ, hb⟩
    refine ⟨(a, b), ?_, ?_⟩
    · rw [Finset.mem_filter]
      constructor
      · exact Finset.mem_product.mpr ⟨haQ, hbQ⟩
      · have hdiff :
            (addEquivEmbedding e) (a - b) = (addEquivEmbedding e) γ := by
          have htarget :
              (addEquivEmbedding e) a - (addEquivEmbedding e) b =
                (addEquivEmbedding e) γ := by
            rw [ha, hb]
            exact hpair.2
          simpa [addEquivEmbedding, e.map_sub] using htarget
        exact e.injective (by simpa [addEquivEmbedding] using hdiff)
    · exact Prod.ext ha hb

lemma pairFiber_card_map_addMonoidHom_of_injective
    (f : G →+ H) (hf : Function.Injective f) (Q : Finset G) (γ : G) :
    (pairFiber (Q.map (addMonoidHomEmbedding f hf))
        ((addMonoidHomEmbedding f hf) γ)).card =
      (pairFiber Q γ).card := by
  classical
  have hleft :
      pairFiber (Q.map (addMonoidHomEmbedding f hf))
          ((addMonoidHomEmbedding f hf) γ) =
        ((Q.map (addMonoidHomEmbedding f hf)).product
          (Q.map (addMonoidHomEmbedding f hf))).filter
          (fun pair : H × H => pair.1 - pair.2 =
            (addMonoidHomEmbedding f hf) γ) := by
    ext pair
    simp [pairFiber]
  have hright :
      pairFiber Q γ =
        (Q.product Q).filter (fun pair : G × G => pair.1 - pair.2 = γ) := by
    ext pair
    simp [pairFiber]
  rw [hleft, hright]
  symm
  apply Finset.card_bij (fun pair _hpair => (f pair.1, f pair.2))
  · intro pair hpair
    rw [Finset.mem_filter] at hpair
    rw [Finset.mem_filter]
    constructor
    · apply Finset.mem_product.mpr
      have hprod := Finset.mem_product.mp hpair.1
      exact
        ⟨Finset.mem_map.mpr ⟨pair.1, hprod.1, rfl⟩,
          Finset.mem_map.mpr ⟨pair.2, hprod.2, rfl⟩⟩
    · have hdiff : f (pair.1 - pair.2) = f γ := congrArg f hpair.2
      simpa [addMonoidHomEmbedding] using hdiff
  · intro pair _hpair pair' _hpair' h
    exact Prod.ext
      (hf (congrArg Prod.fst h))
      (hf (congrArg Prod.snd h))
  · intro pair hpair
    rw [Finset.mem_filter] at hpair
    have hprod := Finset.mem_product.mp hpair.1
    rcases Finset.mem_map.mp hprod.1 with ⟨a, haQ, ha⟩
    rcases Finset.mem_map.mp hprod.2 with ⟨b, hbQ, hb⟩
    refine ⟨(a, b), ?_, ?_⟩
    · rw [Finset.mem_filter]
      constructor
      · exact Finset.mem_product.mpr ⟨haQ, hbQ⟩
      · have hdiff : f (a - b) = f γ := by
          have htarget :
              (addMonoidHomEmbedding f hf) a - (addMonoidHomEmbedding f hf) b =
                (addMonoidHomEmbedding f hf) γ := by
            rw [ha, hb]
            exact hpair.2
          simpa [addMonoidHomEmbedding] using htarget
        exact hf hdiff
    · exact Prod.ext ha hb

lemma map_addEquiv
    (e : G ≃+ H) {Q B : Finset G} {M : ℝ}
    (h : PairCoeffLowerBound Q B M) :
    PairCoeffLowerBound
      (Q.map (addEquivEmbedding e)) (B.map (addEquivEmbedding e)) M := by
  classical
  intro γ hγ
  rcases Finset.mem_map.mp hγ with ⟨δ, hδ, rfl⟩
  rw [pairFiber_card_map_addEquiv, Finset.card_map]
  exact h δ hδ

lemma map_addMonoidHom_of_injective
    (f : G →+ H) (hf : Function.Injective f) {Q B : Finset G} {M : ℝ}
    (h : PairCoeffLowerBound Q B M) :
    PairCoeffLowerBound
      (Q.map (addMonoidHomEmbedding f hf)) (B.map (addMonoidHomEmbedding f hf)) M := by
  classical
  intro γ hγ
  rcases Finset.mem_map.mp hγ with ⟨δ, hδ, rfl⟩
  rw [pairFiber_card_map_addMonoidHom_of_injective, Finset.card_map]
  exact h δ hδ

lemma of_map_addEquiv
    (e : G ≃+ H) {Q B : Finset G} {M : ℝ}
    (h :
      PairCoeffLowerBound
        (Q.map (addEquivEmbedding e)) (B.map (addEquivEmbedding e)) M) :
    PairCoeffLowerBound Q B M := by
  classical
  intro γ hγ
  have hγ' : (addEquivEmbedding e) γ ∈ B.map (addEquivEmbedding e) :=
    Finset.mem_map.mpr ⟨γ, hγ, rfl⟩
  have hbound := h ((addEquivEmbedding e) γ) hγ'
  rwa [pairFiber_card_map_addEquiv, Finset.card_map] at hbound

lemma exists_of_addEquiv
    (e : G ≃+ H) {B : Finset G} {M : ℝ}
    (h :
      ∃ Q : Finset H, Q.Nonempty ∧
        PairCoeffLowerBound Q (B.map (addEquivEmbedding e)) M) :
    ∃ Q : Finset G, Q.Nonempty ∧ PairCoeffLowerBound Q B M := by
  classical
  rcases h with ⟨Q, hQ, hbound⟩
  refine ⟨Q.map (addEquivEmbedding e.symm), ?_, ?_⟩
  · rcases hQ with ⟨q, hq⟩
    exact ⟨e.symm q, Finset.mem_map.mpr ⟨q, hq, rfl⟩⟩
  have hmap := map_addEquiv e.symm hbound
  simpa [addEquivEmbedding, Finset.map_map] using hmap

end PairCoeffLowerBound

section PairFiberCounting

variable {G : Type*} [AddCommGroup G]

/-- Any set whose `γ`-backward translate stays inside `Q` injects into the
pair fiber `{(x,y) ∈ Q × Q | x - y = γ}`. -/
lemma card_le_pairFiber_card_of_sub_right_subset
    (Q R : Finset G) (γ : G)
    (hR : ∀ x ∈ R, x ∈ Q ∧ x - γ ∈ Q) :
    R.card ≤
      ((Q.product Q).filter (fun pair : G × G => pair.1 - pair.2 = γ)).card := by
  classical
  refine Finset.card_le_card_of_injOn
    (fun x : G => (x, x - γ)) ?_ ?_
  · intro x hx
    change (x, x - γ) ∈
      ((Q.product Q).filter (fun pair : G × G => pair.1 - pair.2 = γ))
    rw [Finset.mem_filter]
    constructor
    · exact Finset.mem_product.mpr ⟨(hR x hx).1, (hR x hx).2⟩
    · simp [sub_eq_add_neg, add_left_comm]
  · intro x _hx y _hy hxy
    exact congrArg Prod.fst hxy

lemma pairCoeffLowerBound_of_inner_card
    {Q B : Finset G} {M : ℝ}
    (inner : G → Finset G)
    (hinner : ∀ γ ∈ B, ∀ x ∈ inner γ, x ∈ Q ∧ x - γ ∈ Q)
    (hcard :
      ∀ γ ∈ B,
        1 - M ≤ ((inner γ).card : ℝ) / (Q.card : ℝ)) :
    PairCoeffLowerBound Q B M := by
  classical
  intro γ hγ
  have hle :
      ((inner γ).card : ℝ) ≤
        (((Q.product Q).filter
          (fun pair : G × G => pair.1 - pair.2 = γ)).card : ℝ) := by
    exact_mod_cast
      card_le_pairFiber_card_of_sub_right_subset Q (inner γ) γ
        (hinner γ hγ)
  exact (hcard γ hγ).trans (div_le_div_of_nonneg_right hle (by positivity))

end PairFiberCounting

section IntIntervals

/-- Centered integer interval `[-N,N]`. -/
def intCenteredInterval (N : ℕ) : Finset ℤ :=
  Finset.Icc (-(N : ℤ)) (N : ℤ)

/-- Inner interval that stays inside `[-N,N]` after subtracting any integer of
absolute value at most `K`. -/
def intInnerInterval (N K : ℕ) : Finset ℤ :=
  Finset.Icc (-(N : ℤ) + (K : ℤ)) ((N : ℤ) - (K : ℤ))

lemma intCenteredInterval_nonempty (N : ℕ) :
    (intCenteredInterval N).Nonempty := by
  refine ⟨0, ?_⟩
  rw [intCenteredInterval, Finset.mem_Icc]
  constructor
  · exact neg_nonpos.mpr (by exact_mod_cast Nat.zero_le N)
  · exact_mod_cast Nat.zero_le N

lemma intCenteredInterval_card (N : ℕ) :
    (intCenteredInterval N).card = 2 * N + 1 := by
  rw [intCenteredInterval, Int.card_Icc]
  omega

lemma intInnerInterval_card {N K : ℕ} (hK : K ≤ N) :
    (intInnerInterval N K).card = 2 * (N - K) + 1 := by
  rw [intInnerInterval, Int.card_Icc]
  omega

lemma intInnerInterval_subset_centered
    {N K : ℕ} :
    intInnerInterval N K ⊆ intCenteredInterval N := by
  intro x hx
  rw [intInnerInterval, Finset.mem_Icc] at hx
  rw [intCenteredInterval, Finset.mem_Icc]
  constructor <;> nlinarith

lemma intInnerInterval_sub_mem_centered
    {N K : ℕ} {γ x : ℤ}
    (hγ : γ.natAbs ≤ K) (hx : x ∈ intInnerInterval N K) :
    x - γ ∈ intCenteredInterval N := by
  rw [intInnerInterval, Finset.mem_Icc] at hx
  rw [intCenteredInterval, Finset.mem_Icc]
  have hγ_le_K : γ ≤ (K : ℤ) := by
    exact le_trans Int.le_natAbs (by exact_mod_cast hγ)
  have hnegK_le_γ : -(K : ℤ) ≤ γ := by
    have hneg_abs : -((γ.natAbs : ℤ)) ≤ γ := by
      exact neg_le.mp (by simpa using (Int.le_natAbs (a := -γ)))
    have hγZ : (γ.natAbs : ℤ) ≤ (K : ℤ) := by exact_mod_cast hγ
    exact le_trans (neg_le_neg hγZ) hneg_abs
  constructor <;> nlinarith [hx.1, hx.2, hγ_le_K, hnegK_le_γ]

lemma int_pairCoeffLowerBound_of_inner_ratio
    {B : Finset ℤ} {N K : ℕ} {M : ℝ}
    (hB : ∀ γ ∈ B, γ.natAbs ≤ K)
    (hratio :
      1 - M ≤
        ((intInnerInterval N K).card : ℝ) /
          ((intCenteredInterval N).card : ℝ)) :
    PairCoeffLowerBound (intCenteredInterval N) B M := by
  classical
  refine pairCoeffLowerBound_of_inner_card
    (Q := intCenteredInterval N) (B := B) (M := M)
    (fun _γ => intInnerInterval N K) ?_ ?_
  · intro γ hγ x hx
    exact
      ⟨intInnerInterval_subset_centered hx,
        intInnerInterval_sub_mem_centered (hB γ hγ) hx⟩
  · intro γ _hγ
    exact hratio

lemma int_pairCoeffLowerBound_of_nat_ratio
    {B : Finset ℤ} {N K : ℕ} {M : ℝ}
    (hK : K ≤ N)
    (hB : ∀ γ ∈ B, γ.natAbs ≤ K)
    (hratio :
      1 - M ≤
        ((2 * (N - K) + 1 : ℕ) : ℝ) /
          ((2 * N + 1 : ℕ) : ℝ)) :
    PairCoeffLowerBound (intCenteredInterval N) B M :=
  int_pairCoeffLowerBound_of_inner_ratio hB (by
    simpa [intInnerInterval_card hK, intCenteredInterval_card] using hratio)

lemma int_interval_ratio_bound
    {N K : ℕ} {M : ℝ} (hK : K ≤ N)
    (hloss : (2 * K : ℝ) ≤ M * ((2 * N + 1 : ℕ) : ℝ)) :
    1 - M ≤
      ((2 * (N - K) + 1 : ℕ) : ℝ) /
        ((2 * N + 1 : ℕ) : ℝ) := by
  have hden : 0 < ((2 * N + 1 : ℕ) : ℝ) := by positivity
  rw [le_div_iff₀ hden]
  norm_num [Nat.cast_sub hK] at hloss hden ⊢
  nlinarith

lemma int_pairCoeffLowerBound_of_loss
    {B : Finset ℤ} {N K : ℕ} {M : ℝ}
    (hK : K ≤ N)
    (hB : ∀ γ ∈ B, γ.natAbs ≤ K)
    (hloss : (2 * K : ℝ) ≤ M * ((2 * N + 1 : ℕ) : ℝ)) :
    PairCoeffLowerBound (intCenteredInterval N) B M :=
  int_pairCoeffLowerBound_of_nat_ratio hK hB
    (int_interval_ratio_bound hK hloss)

lemma exists_int_pairCoeffLowerBound_of_bound
    (B : Finset ℤ) (K : ℕ) {M : ℝ} (hM : 0 < M)
    (hB : ∀ γ ∈ B, γ.natAbs ≤ K) :
    ∃ Q : Finset ℤ, Q.Nonempty ∧ PairCoeffLowerBound Q B M := by
  classical
  obtain ⟨N, hN⟩ := exists_nat_gt (((2 * K : ℝ) / M) + (K : ℝ))
  have hN_gt_K : (K : ℝ) < (N : ℝ) := by
    have hterm_nonneg : 0 ≤ (2 * K : ℝ) / M := by
      positivity
    nlinarith [hN]
  have hKle : K ≤ N := by exact_mod_cast le_of_lt hN_gt_K
  have hloss : (2 * K : ℝ) ≤ M * ((2 * N + 1 : ℕ) : ℝ) := by
    have hNbig : (2 * K : ℝ) / M < (N : ℝ) := by
      nlinarith [hN]
    have htwoK_lt : (2 * K : ℝ) < M * (N : ℝ) := by
      have hraw : (2 * K : ℝ) < (N : ℝ) * M := by
        rwa [div_lt_iff₀ hM] at hNbig
      nlinarith
    have hN_le : (N : ℝ) ≤ ((2 * N + 1 : ℕ) : ℝ) := by
      exact_mod_cast (by omega : N ≤ 2 * N + 1)
    exact (le_of_lt htwoK_lt).trans
      (mul_le_mul_of_nonneg_left hN_le (le_of_lt hM))
  exact
    ⟨intCenteredInterval N, intCenteredInterval_nonempty N,
      int_pairCoeffLowerBound_of_loss hKle hB hloss⟩

lemma exists_int_pairCoeffLowerBound
    (B : Finset ℤ) {M : ℝ} (hM : 0 < M) :
    ∃ Q : Finset ℤ, Q.Nonempty ∧ PairCoeffLowerBound Q B M := by
  classical
  by_cases hBne : B.Nonempty
  · let K : ℕ := (B.image Int.natAbs).max' (hBne.image Int.natAbs)
    exact exists_int_pairCoeffLowerBound_of_bound B K hM (by
      intro γ hγ
      exact (B.image Int.natAbs).le_max' γ.natAbs
        (Finset.mem_image.mpr ⟨γ, hγ, rfl⟩))
  · have hBempty : B = ∅ := Finset.not_nonempty_iff_eq_empty.mp hBne
    exact
      ⟨intCenteredInterval 0, intCenteredInterval_nonempty 0, by
        simp [PairCoeffLowerBound, hBempty]⟩

end IntIntervals

section IntPiBoxes

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Product box `[-N,N]^ι` in the finite-rank free abelian group `ι → Z`. -/
def intPiCenteredBox (ι : Type*) [Fintype ι] [DecidableEq ι]
    (N : ℕ) : Finset (ι → ℤ) :=
  Fintype.piFinset fun _ : ι => intCenteredInterval N

/-- Inner product box that stays inside `[-N,N]^ι` after subtracting any vector
whose coordinates have absolute value at most `K`. -/
def intPiInnerBox (ι : Type*) [Fintype ι] [DecidableEq ι]
    (N K : ℕ) : Finset (ι → ℤ) :=
  Fintype.piFinset fun _ : ι => intInnerInterval N K

lemma intPiCenteredBox_nonempty (N : ℕ) :
    (intPiCenteredBox ι N).Nonempty := by
  rw [intPiCenteredBox, Fintype.piFinset_nonempty]
  intro i
  exact intCenteredInterval_nonempty N

lemma intPiCenteredBox_card (N : ℕ) :
    (intPiCenteredBox ι N).card = ∏ _i : ι, (2 * N + 1 : ℕ) := by
  rw [intPiCenteredBox, Fintype.card_piFinset]
  simp [intCenteredInterval_card]

lemma intPiInnerBox_card {N K : ℕ} (hK : K ≤ N) :
    (intPiInnerBox ι N K).card =
      ∏ _i : ι, (2 * (N - K) + 1 : ℕ) := by
  rw [intPiInnerBox, Fintype.card_piFinset]
  simp [intInnerInterval_card hK]

lemma intPiInnerBox_subset_centered
    {N K : ℕ} {x : ι → ℤ}
    (hx : x ∈ intPiInnerBox ι N K) :
    x ∈ intPiCenteredBox ι N := by
  rw [intPiInnerBox, Fintype.mem_piFinset] at hx
  rw [intPiCenteredBox, Fintype.mem_piFinset]
  intro i
  exact intInnerInterval_subset_centered (hx i)

lemma intPiInnerBox_sub_mem_centered
    {N K : ℕ} {γ x : ι → ℤ}
    (hγ : ∀ i : ι, (γ i).natAbs ≤ K)
    (hx : x ∈ intPiInnerBox ι N K) :
    x - γ ∈ intPiCenteredBox ι N := by
  rw [intPiInnerBox, Fintype.mem_piFinset] at hx
  rw [intPiCenteredBox, Fintype.mem_piFinset]
  intro i
  simpa using intInnerInterval_sub_mem_centered (hγ i) (hx i)

lemma intPi_pairCoeffLowerBound_of_inner_ratio
    {B : Finset (ι → ℤ)} {N K : ℕ} {M : ℝ}
    (hB : ∀ γ ∈ B, ∀ i : ι, (γ i).natAbs ≤ K)
    (hratio :
      1 - M ≤
        ((intPiInnerBox ι N K).card : ℝ) /
          ((intPiCenteredBox ι N).card : ℝ)) :
    PairCoeffLowerBound (intPiCenteredBox ι N) B M := by
  classical
  refine pairCoeffLowerBound_of_inner_card
    (Q := intPiCenteredBox ι N) (B := B) (M := M)
    (fun _γ => intPiInnerBox ι N K) ?_ ?_
  · intro γ hγ x hx
    exact
      ⟨intPiInnerBox_subset_centered hx,
        intPiInnerBox_sub_mem_centered (hB γ hγ) hx⟩
  · intro γ _hγ
    exact hratio

lemma intPi_pairCoeffLowerBound_of_nat_ratio
    {B : Finset (ι → ℤ)} {N K : ℕ} {M : ℝ}
    (hK : K ≤ N)
    (hB : ∀ γ ∈ B, ∀ i : ι, (γ i).natAbs ≤ K)
    (hratio :
      1 - M ≤
        ((∏ _i : ι, (2 * (N - K) + 1 : ℕ)) : ℝ) /
          ((∏ _i : ι, (2 * N + 1 : ℕ)) : ℝ)) :
    PairCoeffLowerBound (intPiCenteredBox ι N) B M :=
  intPi_pairCoeffLowerBound_of_inner_ratio hB (by
    simpa [intPiInnerBox_card (ι := ι) hK, intPiCenteredBox_card (ι := ι)]
      using hratio)

omit [DecidableEq ι] in
lemma intPi_product_ratio_bound
    {N K : ℕ} {M : ℝ} (hK : K ≤ N)
    (hloss :
      ((Fintype.card ι : ℝ) * (2 * K : ℝ)) ≤
        M * ((2 * N + 1 : ℕ) : ℝ)) :
    1 - M ≤
      ((∏ _i : ι, (2 * (N - K) + 1 : ℕ)) : ℝ) /
        ((∏ _i : ι, (2 * N + 1 : ℕ)) : ℝ) := by
  classical
  let d : ℕ := Fintype.card ι
  let inner : ℝ := ((2 * (N - K) + 1 : ℕ) : ℝ)
  let outer : ℝ := ((2 * N + 1 : ℕ) : ℝ)
  have houter_pos : 0 < outer := by
    dsimp [outer]
    positivity
  have hinner_nonneg : 0 ≤ inner := by
    dsimp [inner]
    positivity
  have hratio_eq :
      ((∏ _i : ι, (2 * (N - K) + 1 : ℕ)) : ℝ) /
          ((∏ _i : ι, (2 * N + 1 : ℕ)) : ℝ) =
        (inner / outer) ^ d := by
    simp [d, inner, outer, Finset.prod_const, Finset.card_univ, div_pow]
  have hratio_nonneg : 0 ≤ inner / outer :=
    div_nonneg hinner_nonneg houter_pos.le
  have hbernoulli :
      1 + (d : ℝ) * (inner / outer - 1) ≤ (inner / outer) ^ d :=
    one_add_mul_sub_le_pow (a := inner / outer) (n := d) (by linarith)
  have hinner_eq : inner = outer - (2 * K : ℝ) := by
    dsimp [inner, outer]
    norm_num [Nat.cast_sub hK]
    ring
  have hsub :
      inner / outer - 1 = -((2 * K : ℝ) / outer) := by
    rw [hinner_eq]
    field_simp [houter_pos.ne']
    ring
  have hdiv_loss' :
      (((d : ℝ) * (2 * K : ℝ)) / outer) ≤ M := by
    rw [div_le_iff₀ houter_pos]
    simpa [d, outer] using hloss
  have hdiv_loss :
      (d : ℝ) * ((2 * K : ℝ) / outer) ≤ M := by
    simpa [mul_div_assoc] using hdiv_loss'
  have hlower :
      1 - M ≤ 1 + (d : ℝ) * (inner / outer - 1) := by
    rw [hsub]
    nlinarith
  calc
    1 - M ≤ 1 + (d : ℝ) * (inner / outer - 1) := hlower
    _ ≤ (inner / outer) ^ d := hbernoulli
    _ = ((∏ _i : ι, (2 * (N - K) + 1 : ℕ)) : ℝ) /
          ((∏ _i : ι, (2 * N + 1 : ℕ)) : ℝ) := hratio_eq.symm

lemma intPi_pairCoeffLowerBound_of_loss
    {B : Finset (ι → ℤ)} {N K : ℕ} {M : ℝ}
    (hK : K ≤ N)
    (hB : ∀ γ ∈ B, ∀ i : ι, (γ i).natAbs ≤ K)
    (hloss :
      ((Fintype.card ι : ℝ) * (2 * K : ℝ)) ≤
        M * ((2 * N + 1 : ℕ) : ℝ)) :
    PairCoeffLowerBound (intPiCenteredBox ι N) B M :=
  intPi_pairCoeffLowerBound_of_nat_ratio hK hB
    (intPi_product_ratio_bound (ι := ι) hK hloss)

omit [Fintype ι] [DecidableEq ι] in
lemma exists_intPi_pairCoeffLowerBound_of_bound
    [Finite ι]
    (B : Finset (ι → ℤ)) (K : ℕ) {M : ℝ} (hM : 0 < M)
    (hB : ∀ γ ∈ B, ∀ i : ι, (γ i).natAbs ≤ K) :
    ∃ Q : Finset (ι → ℤ), Q.Nonempty ∧ PairCoeffLowerBound Q B M := by
  classical
  letI := Fintype.ofFinite ι
  obtain ⟨N, hN⟩ :=
    exists_nat_gt ((((Fintype.card ι : ℝ) * (2 * K : ℝ)) / M) + (K : ℝ))
  have hN_gt_K : (K : ℝ) < (N : ℝ) := by
    have hterm_nonneg :
        0 ≤ (((Fintype.card ι : ℝ) * (2 * K : ℝ)) / M) := by
      positivity
    nlinarith [hN]
  have hKle : K ≤ N := by exact_mod_cast le_of_lt hN_gt_K
  have hloss :
      ((Fintype.card ι : ℝ) * (2 * K : ℝ)) ≤
        M * ((2 * N + 1 : ℕ) : ℝ) := by
    have hNbig :
        (((Fintype.card ι : ℝ) * (2 * K : ℝ)) / M) < (N : ℝ) := by
      nlinarith [hN]
    have hlt :
        ((Fintype.card ι : ℝ) * (2 * K : ℝ)) < M * (N : ℝ) := by
      have hraw :
          ((Fintype.card ι : ℝ) * (2 * K : ℝ)) < (N : ℝ) * M := by
        rwa [div_lt_iff₀ hM] at hNbig
      nlinarith
    have hN_le : (N : ℝ) ≤ ((2 * N + 1 : ℕ) : ℝ) := by
      exact_mod_cast (by omega : N ≤ 2 * N + 1)
    exact (le_of_lt hlt).trans
      (mul_le_mul_of_nonneg_left hN_le (le_of_lt hM))
  exact
    ⟨intPiCenteredBox ι N, intPiCenteredBox_nonempty N,
      intPi_pairCoeffLowerBound_of_loss hKle hB hloss⟩

omit [Fintype ι] [DecidableEq ι] in
lemma exists_intPi_pairCoeffLowerBound
    [Finite ι]
    (B : Finset (ι → ℤ)) {M : ℝ} (hM : 0 < M) :
    ∃ Q : Finset (ι → ℤ), Q.Nonempty ∧ PairCoeffLowerBound Q B M := by
  classical
  letI := Fintype.ofFinite ι
  let C : Finset ℕ :=
    B.biUnion fun γ => (Finset.univ : Finset ι).image fun i => (γ i).natAbs
  by_cases hC : C.Nonempty
  · let K : ℕ := C.max' hC
    exact exists_intPi_pairCoeffLowerBound_of_bound B K hM (by
      intro γ hγ i
      exact C.le_max' (γ i).natAbs (by
        change (γ i).natAbs ∈
          B.biUnion (fun γ => (Finset.univ : Finset ι).image fun i => (γ i).natAbs)
        rw [Finset.mem_biUnion]
        exact ⟨γ, hγ, Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩⟩))
  · exact exists_intPi_pairCoeffLowerBound_of_bound B 0 hM (by
      intro γ hγ i
      exfalso
      exact hC ⟨(γ i).natAbs, by
        change (γ i).natAbs ∈
          B.biUnion (fun γ => (Finset.univ : Finset ι).image fun i => (γ i).natAbs)
        rw [Finset.mem_biUnion]
        exact ⟨γ, hγ, Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩⟩⟩)

end IntPiBoxes

section FinsuppBoxes

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [Fintype ι] [DecidableEq ι] in
lemma exists_finsupp_pairCoeffLowerBound
    [Finite ι]
    (B : Finset (ι →₀ ℤ)) {M : ℝ} (hM : 0 < M) :
    ∃ Q : Finset (ι →₀ ℤ), Q.Nonempty ∧ PairCoeffLowerBound Q B M := by
  classical
  letI := Fintype.ofFinite ι
  let e : (ι →₀ ℤ) ≃+ (ι → ℤ) :=
    (Finsupp.linearEquivFunOnFinite ℤ ℤ ι).toAddEquiv
  exact PairCoeffLowerBound.exists_of_addEquiv e
    (exists_intPi_pairCoeffLowerBound
      (B.map (PairCoeffLowerBound.addEquivEmbedding e)) hM)

end FinsuppBoxes

section FreeFinite

variable {G : Type*} [AddCommGroup G]

lemma exists_free_finite_pairCoeffLowerBound
    [Module.Free ℤ G] [Module.Finite ℤ G]
    (B : Finset G) {M : ℝ} (hM : 0 < M) :
    ∃ Q : Finset G, Q.Nonempty ∧ PairCoeffLowerBound Q B M := by
  classical
  let ι := Module.Free.ChooseBasisIndex ℤ G
  let b := Module.Free.chooseBasis ℤ G
  haveI : Finite ι := Module.Finite.finite_basis b
  letI : Fintype ι := Fintype.ofFinite ι
  letI : DecidableEq ι := Classical.decEq ι
  let e : G ≃+ (ι →₀ ℤ) := b.repr.toAddEquiv
  exact PairCoeffLowerBound.exists_of_addEquiv e
    (exists_finsupp_pairCoeffLowerBound
      (B.map (PairCoeffLowerBound.addEquivEmbedding e)) hM)

lemma exists_fg_torsionFree_pairCoeffLowerBound
    [IsAddTorsionFree G] [AddGroup.FG G]
    (B : Finset G) {M : ℝ} (hM : 0 < M) :
    ∃ Q : Finset G, Q.Nonempty ∧ PairCoeffLowerBound Q B M := by
  classical
  haveI : Module.Finite ℤ G :=
    Module.Finite.iff_addGroup_fg.mpr (inferInstance : AddGroup.FG G)
  haveI : Module.Free ℤ G := Module.free_of_finite_type_torsion_free'
  exact exists_free_finite_pairCoeffLowerBound B hM

lemma exists_torsionFree_pairCoeffLowerBound
    [IsAddTorsionFree G]
    (B : Finset G) {M : ℝ} (hM : 0 < M) :
    ∃ Q : Finset G, Q.Nonempty ∧ PairCoeffLowerBound Q B M := by
  classical
  let H : AddSubgroup G := AddSubgroup.closure (B : Set G)
  let BH : Finset H := B.subtype fun x => x ∈ H
  haveI : IsAddTorsionFree H := by
    constructor
    intro n hn x y hxy
    ext
    exact IsAddTorsionFree.nsmul_right_injective hn (by
      simpa using congrArg Subtype.val hxy)
  haveI : Finite (B : Set G) := Set.finite_coe_iff.mpr B.finite_toSet
  haveI : AddGroup.FG H := AddGroup.closure_finite_fg (B : Set G)
  obtain ⟨QH, hQH, hboundH⟩ :=
    exists_fg_torsionFree_pairCoeffLowerBound (G := H) BH hM
  let emb := PairCoeffLowerBound.addMonoidHomEmbedding
    H.subtype (AddSubgroup.subtype_injective H)
  have hBmap : BH.map emb = B := by
    ext γ
    simp only [Finset.mem_map, Subtype.exists]
    constructor
    · rintro ⟨a, haH, haBH, hγ⟩
      rw [← hγ]
      simpa [BH, emb, PairCoeffLowerBound.addMonoidHomEmbedding] using haBH
    · intro hγ
      exact ⟨γ, AddSubgroup.subset_closure hγ, by simpa [BH], rfl⟩
  refine ⟨QH.map emb, ?_, ?_⟩
  · rcases hQH with ⟨q, hq⟩
    exact ⟨q, Finset.mem_map.mpr ⟨q, hq, rfl⟩⟩
  · have hmap :=
      PairCoeffLowerBound.map_addMonoidHom_of_injective
        H.subtype (AddSubgroup.subtype_injective H) hboundH
    simpa [emb, hBmap] using hmap

end FreeFinite

namespace CayleyExtraction

variable {ℓ : ℕ} {η : ℝ} {S : CayleyCounterSeq ℓ η}

lemma exists_pairCoeffLowerBound
    (E : CayleyExtraction S)
    (B : Finset E.Group) {M : ℝ} (hM : 0 < M) :
    ∃ Q : Finset E.Group, Q.Nonempty ∧ PairCoeffLowerBound Q B M :=
  exists_torsionFree_pairCoeffLowerBound (G := E.Group) B hM

lemma exists_pairCoeffLowerBound_nonempty_ne
    (E : CayleyExtraction S)
    (B : Finset E.Group) {M : ℝ} (hM : 0 < M) :
    ∃ Q : Finset E.Group, Q ≠ ∅ ∧ PairCoeffLowerBound Q B M := by
  classical
  obtain ⟨Q, hQ, hbound⟩ :=
    E.exists_pairCoeffLowerBound B hM
  exact ⟨Q, Finset.nonempty_iff_ne_empty.mp hQ, hbound⟩

lemma exists_fejerPairCoeffLowerBound
    (E : CayleyExtraction S)
    (B : Finset E.Group) {M : ℝ} (hM : 0 < M) :
    ∃ Q : Finset E.Group, Q ≠ ∅ ∧ E.FejerPairCoeffLowerBound Q B M := by
  simpa [FejerPairCoeffLowerBound] using
    E.exists_pairCoeffLowerBound_nonempty_ne B hM

end CayleyExtraction

end

end Erdos42.CompactCayley


/-! =============================================================
    Section from: Erdos/P42/CompactCayley/ContinuousEndpoint.lean
    ============================================================= -/

/-
Erdős Problem 42 — Layer 1 continuous-analogue lemma.

Following Tao's May 2026 forum comment + natso26's clean exposition
(`fourier_positive_ulam_note.pdf`). The geometric core
`closed_proper_subgroup_haar_null` is proved here axiom-free; the main
`tao_continuous_avoidance` lemma is also proved once the standard measurable
group assumptions needed by Mathlib's Haar shear lemmas are available.

This file is shared scaffolding: Route A (Fourier-positive) eventually uses it
as the continuous endpoint of the U²-regularity / counting argument. Route B
(compact Cayley) uses a closely related lemma in its clique-forcing proof
(Lemma 2.7 of the compact Cayley PDF), which is also a candidate destination
for `closed_proper_subgroup_haar_null` once we open that black box.
-/
namespace Erdos42

open Filter Set Finset MeasureTheory
open scoped Pointwise Topology

universe u

/-- A nonnegative integrable real-valued function that is positive almost
everywhere on a probability space has positive integral. -/
lemma integral_pos_of_ae_pos_of_nonneg
    {α : Type*} [MeasurableSpace α] (μ : Measure α) [IsProbabilityMeasure μ]
    {F : α → ℝ} (hFint : Integrable F μ)
    (hFnonneg : 0 ≤ᵐ[μ] F) (hFpos : ∀ᵐ x ∂μ, 0 < F x) :
    0 < ∫ x, F x ∂μ := by
  rw [integral_pos_iff_support_of_nonneg_ae hFnonneg hFint]
  have hsupp_ae : ∀ᵐ x ∂μ, x ∈ Function.support F := by
    filter_upwards [hFpos] with x hx
    exact ne_of_gt hx
  have hcompl_zero : μ (Function.support F)ᶜ = 0 := by
    rwa [ae_iff] at hsupp_ae
  by_contra hnot
  have hsupp_zero : μ (Function.support F) = 0 := by
    exact le_antisymm (not_lt.mp hnot) bot_le
  have h_univ_zero : μ (Set.univ : Set α) = 0 := by
    have hcover : (Set.univ : Set α) =
        Function.support F ∪ (Function.support F)ᶜ := by
      ext x
      simp
    refine le_antisymm ?_ bot_le
    calc
      μ (Set.univ : Set α) =
          μ (Function.support F ∪ (Function.support F)ᶜ) := by rw [hcover]
      _ ≤ μ (Function.support F) + μ (Function.support F)ᶜ :=
          measure_union_le _ _
      _ = 0 := by simp [hsupp_zero, hcompl_zero]
  have h_univ_one : μ (Set.univ : Set α) = 1 := measure_univ
  norm_num [h_univ_one] at h_univ_zero

/-- Edge set of `K_M`, oriented by the natural order. This is the continuous
analogue of the finite ordered-clique product in the compact-Cayley proof. -/
def continuousCliqueEdgePairs (M : ℕ) : Finset (Fin M × Fin M) :=
  (Finset.univ : Finset (Fin M × Fin M)).filter (fun e => e.1 < e.2)

/-- Product kernel for the continuous `K_M` Cayley density. -/
noncomputable def continuousCliqueKernel
    {G : Type u} [Sub G] (M : ℕ) (f : G → ℝ) (x : Fin M → G) : ℝ :=
  ∏ e ∈ continuousCliqueEdgePairs M, f (x e.1 - x e.2)

/-- Continuous Cayley `K_M` density associated to a kernel `f`. -/
noncomputable def continuousCliqueDensity
    {G : Type u} [MeasurableSpace G] [Sub G]
    (μ : Measure G) (M : ℕ) (f : G → ℝ) : ℝ :=
  ∫ x : Fin M → G, continuousCliqueKernel M f x ∂Measure.pi (fun _ : Fin M => μ)

lemma abs_prod_sub_prod_le_sum_abs
    {ι : Type*} (s : Finset ι) (f g : ι → ℝ)
    (hf_nonneg : ∀ i ∈ s, 0 ≤ f i)
    (hf_le : ∀ i ∈ s, f i ≤ 1)
    (hg_nonneg : ∀ i ∈ s, 0 ≤ g i)
    (hg_le : ∀ i ∈ s, g i ≤ 1) :
    |(∏ i ∈ s, f i) - ∏ i ∈ s, g i| ≤
      ∑ i ∈ s, |f i - g i| := by
  classical
  revert hf_nonneg hf_le hg_nonneg hg_le
  refine Finset.induction_on s ?base ?step
  · simp
  · intro a s ha ih hf_nonneg hf_le hg_nonneg hg_le
    have hf_nonneg_s : ∀ i ∈ s, 0 ≤ f i := by
      intro i hi
      exact hf_nonneg i (by simp [hi])
    have hf_le_s : ∀ i ∈ s, f i ≤ 1 := by
      intro i hi
      exact hf_le i (by simp [hi])
    have hg_nonneg_s : ∀ i ∈ s, 0 ≤ g i := by
      intro i hi
      exact hg_nonneg i (by simp [hi])
    have hg_le_s : ∀ i ∈ s, g i ≤ 1 := by
      intro i hi
      exact hg_le i (by simp [hi])
    have htail := ih hf_nonneg_s hf_le_s hg_nonneg_s hg_le_s
    let Pf : ℝ := ∏ i ∈ s, f i
    let Pg : ℝ := ∏ i ∈ s, g i
    have hfa_abs : |f a| ≤ 1 := by
      have hfa_nonneg : 0 ≤ f a := hf_nonneg a (by simp [ha])
      simpa [abs_of_nonneg hfa_nonneg] using hf_le a (by simp [ha])
    have hPg_nonneg : 0 ≤ Pg := by
      dsimp [Pg]
      exact Finset.prod_nonneg fun i hi => hg_nonneg_s i hi
    have hPg_le : Pg ≤ 1 := by
      dsimp [Pg]
      exact Finset.prod_le_one
        (fun i hi => hg_nonneg_s i hi) (fun i hi => hg_le_s i hi)
    have hPg_abs : |Pg| ≤ 1 := by
      simpa [abs_of_nonneg hPg_nonneg] using hPg_le
    rw [Finset.prod_insert ha, Finset.prod_insert ha, Finset.sum_insert ha]
    have hdecomp : f a * Pf - g a * Pg =
        f a * (Pf - Pg) + (f a - g a) * Pg := by ring
    calc
      |f a * Pf - g a * Pg|
          = |f a * (Pf - Pg) + (f a - g a) * Pg| := by rw [hdecomp]
      _ ≤ |f a * (Pf - Pg)| + |(f a - g a) * Pg| := abs_add_le _ _
      _ = |f a| * |Pf - Pg| + |f a - g a| * |Pg| := by
            rw [abs_mul, abs_mul]
      _ ≤ 1 * |Pf - Pg| + |f a - g a| * 1 := by
            exact add_le_add
              (mul_le_mul_of_nonneg_right hfa_abs (abs_nonneg _))
              (mul_le_mul_of_nonneg_left hPg_abs (abs_nonneg _))
      _ ≤ 1 * (∑ i ∈ s, |f i - g i|) + |f a - g a| * 1 := by
            have hfirst :
                1 * |Pf - Pg| ≤ 1 * (∑ i ∈ s, |f i - g i|) :=
              mul_le_mul_of_nonneg_left (by simpa [Pf, Pg] using htail)
                zero_le_one
            nlinarith
      _ = |f a - g a| + ∑ i ∈ s, |f i - g i| := by ring

lemma abs_prod_sub_prod_le_sum_abs_mul_two_pow
    {ι : Type*} (s : Finset ι) (f g : ι → ℝ)
    (hf_abs : ∀ i ∈ s, |f i| ≤ 2)
    (hg_abs : ∀ i ∈ s, |g i| ≤ 2) :
    |(∏ i ∈ s, f i) - ∏ i ∈ s, g i| ≤
      (∑ i ∈ s, |f i - g i|) * (2 : ℝ) ^ s.card := by
  classical
  revert hf_abs hg_abs
  refine Finset.induction_on s ?base ?step
  · simp
  · intro a s ha ih hf_abs hg_abs
    have hf_abs_s : ∀ i ∈ s, |f i| ≤ 2 := by
      intro i hi
      exact hf_abs i (by simp [hi])
    have hg_abs_s : ∀ i ∈ s, |g i| ≤ 2 := by
      intro i hi
      exact hg_abs i (by simp [hi])
    have htail := ih hf_abs_s hg_abs_s
    let Pf : ℝ := ∏ i ∈ s, f i
    let Pg : ℝ := ∏ i ∈ s, g i
    have hfa_abs : |f a| ≤ 2 := hf_abs a (by simp [ha])
    have hPg_abs : |Pg| ≤ (2 : ℝ) ^ s.card := by
      dsimp [Pg]
      rw [abs_prod]
      calc
        ∏ i ∈ s, |g i| ≤ ∏ _i ∈ s, (2 : ℝ) := by
          exact Finset.prod_le_prod
            (fun i _hi => abs_nonneg (g i))
            (fun i hi => hg_abs_s i hi)
        _ = (2 : ℝ) ^ s.card := by simp
    have hpow_nonneg : 0 ≤ (2 : ℝ) ^ s.card := by positivity
    have hpow_succ_ge : (2 : ℝ) ^ s.card ≤ (2 : ℝ) ^ (insert a s).card := by
      rw [Finset.card_insert_of_notMem ha]
      rw [pow_succ]
      nlinarith [show 0 ≤ (2 : ℝ) ^ s.card by positivity]
    rw [Finset.prod_insert ha, Finset.prod_insert ha, Finset.sum_insert ha]
    have hdecomp : f a * Pf - g a * Pg =
        f a * (Pf - Pg) + (f a - g a) * Pg := by ring
    calc
      |f a * Pf - g a * Pg|
          = |f a * (Pf - Pg) + (f a - g a) * Pg| := by rw [hdecomp]
      _ ≤ |f a * (Pf - Pg)| + |(f a - g a) * Pg| := abs_add_le _ _
      _ = |f a| * |Pf - Pg| + |f a - g a| * |Pg| := by
            rw [abs_mul, abs_mul]
      _ ≤ 2 * ((∑ i ∈ s, |f i - g i|) * (2 : ℝ) ^ s.card) +
            |f a - g a| * ((2 : ℝ) ^ s.card) := by
            exact add_le_add
              (mul_le_mul hfa_abs htail (abs_nonneg _) zero_le_two)
              (mul_le_mul_of_nonneg_left hPg_abs (abs_nonneg _))
      _ ≤ 2 * ((∑ i ∈ s, |f i - g i|) * (2 : ℝ) ^ s.card) +
            |f a - g a| * ((2 : ℝ) ^ (insert a s).card) := by
            simpa [add_comm, add_left_comm, add_assoc] using
              add_le_add_left
                (mul_le_mul_of_nonneg_left hpow_succ_ge (abs_nonneg _))
                (2 * ((∑ i ∈ s, |f i - g i|) * (2 : ℝ) ^ s.card))
      _ = (|f a - g a| + ∑ i ∈ s, |f i - g i|) *
            (2 : ℝ) ^ (insert a s).card := by
            rw [Finset.card_insert_of_notMem ha, pow_succ]
            ring

lemma abs_continuousCliqueKernel_sub_le_card_mul
    {G : Type u} [Sub G] (M : ℕ) {f g : G → ℝ} {δ : ℝ}
    (hf_nonneg : ∀ x, 0 ≤ f x)
    (hf_le : ∀ x, f x ≤ 1)
    (hg_nonneg : ∀ x, 0 ≤ g x)
    (hg_le : ∀ x, g x ≤ 1)
    (hclose : ∀ x, |f x - g x| ≤ δ)
    (x : Fin M → G) :
    |continuousCliqueKernel M f x - continuousCliqueKernel M g x| ≤
      ((continuousCliqueEdgePairs M).card : ℝ) * δ := by
  unfold continuousCliqueKernel
  calc
    |(∏ e ∈ continuousCliqueEdgePairs M, f (x e.1 - x e.2)) -
        ∏ e ∈ continuousCliqueEdgePairs M, g (x e.1 - x e.2)|
        ≤ ∑ e ∈ continuousCliqueEdgePairs M,
            |f (x e.1 - x e.2) - g (x e.1 - x e.2)| := by
          exact abs_prod_sub_prod_le_sum_abs (continuousCliqueEdgePairs M)
            (fun e => f (x e.1 - x e.2))
            (fun e => g (x e.1 - x e.2))
            (fun e _he => hf_nonneg _)
            (fun e _he => hf_le _)
            (fun e _he => hg_nonneg _)
            (fun e _he => hg_le _)
    _ ≤ ∑ _e ∈ continuousCliqueEdgePairs M, δ := by
          exact Finset.sum_le_sum fun e _he => hclose (x e.1 - x e.2)
    _ = ((continuousCliqueEdgePairs M).card : ℝ) * δ := by simp

lemma abs_continuousCliqueKernel_sub_le_card_mul_two_pow
    {G : Type u} [Sub G] (M : ℕ) {f g : G → ℝ} {δ : ℝ}
    (hf_abs : ∀ x, |f x| ≤ 2)
    (hg_abs : ∀ x, |g x| ≤ 2)
    (hclose : ∀ x, |f x - g x| ≤ δ)
    (x : Fin M → G) :
    |continuousCliqueKernel M f x - continuousCliqueKernel M g x| ≤
      (((continuousCliqueEdgePairs M).card : ℝ) * δ) *
        (2 : ℝ) ^ (continuousCliqueEdgePairs M).card := by
  unfold continuousCliqueKernel
  have hpow_nonneg : 0 ≤ (2 : ℝ) ^ (continuousCliqueEdgePairs M).card := by
    positivity
  calc
    |(∏ e ∈ continuousCliqueEdgePairs M, f (x e.1 - x e.2)) -
        ∏ e ∈ continuousCliqueEdgePairs M, g (x e.1 - x e.2)|
        ≤ (∑ e ∈ continuousCliqueEdgePairs M,
            |f (x e.1 - x e.2) - g (x e.1 - x e.2)|) *
            (2 : ℝ) ^ (continuousCliqueEdgePairs M).card := by
          exact abs_prod_sub_prod_le_sum_abs_mul_two_pow
            (continuousCliqueEdgePairs M)
            (fun e => f (x e.1 - x e.2))
            (fun e => g (x e.1 - x e.2))
            (fun e _he => hf_abs _)
            (fun e _he => hg_abs _)
    _ ≤ (∑ _e ∈ continuousCliqueEdgePairs M, δ) *
          (2 : ℝ) ^ (continuousCliqueEdgePairs M).card := by
          exact mul_le_mul_of_nonneg_right
            (Finset.sum_le_sum fun e _he => hclose (x e.1 - x e.2))
            hpow_nonneg
    _ = (((continuousCliqueEdgePairs M).card : ℝ) * δ) *
          (2 : ℝ) ^ (continuousCliqueEdgePairs M).card := by simp

lemma continuousCliqueDensity_lipschitz_sup
    {G : Type u} [MeasurableSpace G] [Sub G] [MeasurableSub₂ G]
    (μ : Measure G) [IsProbabilityMeasure μ] (M : ℕ)
    {f g : G → ℝ} {δ : ℝ}
    (hf_meas : Measurable f) (hg_meas : Measurable g)
    (hf_nonneg : ∀ x, 0 ≤ f x)
    (hf_le : ∀ x, f x ≤ 1)
    (hg_nonneg : ∀ x, 0 ≤ g x)
    (hg_le : ∀ x, g x ≤ 1)
    (hδ_nonneg : 0 ≤ δ)
    (hclose : ∀ x, |f x - g x| ≤ δ) :
    |continuousCliqueDensity μ M f - continuousCliqueDensity μ M g| ≤
      ((continuousCliqueEdgePairs M).card : ℝ) * δ := by
  let μM : Measure (Fin M → G) := Measure.pi (fun _ : Fin M => μ)
  let Kf : (Fin M → G) → ℝ := fun x => continuousCliqueKernel M f x
  let Kg : (Fin M → G) → ℝ := fun x => continuousCliqueKernel M g x
  have hKf_meas : Measurable Kf := by
    dsimp [Kf, continuousCliqueKernel]
    refine (continuousCliqueEdgePairs M).measurable_prod ?_
    intro e _he
    exact hf_meas.comp ((measurable_pi_apply e.1).sub (measurable_pi_apply e.2))
  have hKg_meas : Measurable Kg := by
    dsimp [Kg, continuousCliqueKernel]
    refine (continuousCliqueEdgePairs M).measurable_prod ?_
    intro e _he
    exact hg_meas.comp ((measurable_pi_apply e.1).sub (measurable_pi_apply e.2))
  have hKf_bound : ∀ᵐ x ∂μM, ‖Kf x‖ ≤ 1 := by
    exact Eventually.of_forall fun x => by
      have hnonneg : 0 ≤ Kf x := by
        dsimp [Kf, continuousCliqueKernel]
        exact Finset.prod_nonneg fun e _he => hf_nonneg _
      have hle : Kf x ≤ 1 := by
        dsimp [Kf, continuousCliqueKernel]
        exact Finset.prod_le_one (fun e _he => hf_nonneg _) (fun e _he => hf_le _)
      simpa [Real.norm_eq_abs, abs_of_nonneg hnonneg] using hle
  have hKg_bound : ∀ᵐ x ∂μM, ‖Kg x‖ ≤ 1 := by
    exact Eventually.of_forall fun x => by
      have hnonneg : 0 ≤ Kg x := by
        dsimp [Kg, continuousCliqueKernel]
        exact Finset.prod_nonneg fun e _he => hg_nonneg _
      have hle : Kg x ≤ 1 := by
        dsimp [Kg, continuousCliqueKernel]
        exact Finset.prod_le_one (fun e _he => hg_nonneg _) (fun e _he => hg_le _)
      simpa [Real.norm_eq_abs, abs_of_nonneg hnonneg] using hle
  have hKf_int : Integrable Kf μM :=
    Integrable.of_bound hKf_meas.aestronglyMeasurable 1 hKf_bound
  have hKg_int : Integrable Kg μM :=
    Integrable.of_bound hKg_meas.aestronglyMeasurable 1 hKg_bound
  let C : ℝ := ((continuousCliqueEdgePairs M).card : ℝ) * δ
  have hC_nonneg : 0 ≤ C := by
    dsimp [C]
    exact mul_nonneg (Nat.cast_nonneg _) hδ_nonneg
  have hdiff_bound : ∀ᵐ x ∂μM, ‖Kf x - Kg x‖ ≤ C := by
    exact Eventually.of_forall fun x => by
      simpa [Kf, Kg, C, Real.norm_eq_abs] using
        abs_continuousCliqueKernel_sub_le_card_mul M
          hf_nonneg hf_le hg_nonneg hg_le hclose x
  have hμM_real : μM.real Set.univ = 1 := by
    haveI : IsProbabilityMeasure μM := inferInstance
    simp [Measure.real, IsProbabilityMeasure.measure_univ]
  unfold continuousCliqueDensity
  change |∫ x, Kf x ∂μM - ∫ x, Kg x ∂μM| ≤ C
  rw [← integral_sub hKf_int hKg_int]
  calc
    |∫ x, Kf x - Kg x ∂μM|
        = ‖∫ x, Kf x - Kg x ∂μM‖ := by
            simp [Real.norm_eq_abs]
    _ ≤ C * μM.real Set.univ :=
        MeasureTheory.norm_integral_le_of_norm_le_const hdiff_bound
    _ = C := by rw [hμM_real, mul_one]

lemma continuousCliqueDensity_lipschitz_sup_two_pow
    {G : Type u} [MeasurableSpace G] [Sub G] [MeasurableSub₂ G]
    (μ : Measure G) [IsProbabilityMeasure μ] (M : ℕ)
    {f g : G → ℝ} {δ : ℝ}
    (hf_meas : Measurable f) (hg_meas : Measurable g)
    (hf_abs : ∀ x, |f x| ≤ 2)
    (hg_abs : ∀ x, |g x| ≤ 2)
    (hδ_nonneg : 0 ≤ δ)
    (hclose : ∀ x, |f x - g x| ≤ δ) :
    |continuousCliqueDensity μ M f - continuousCliqueDensity μ M g| ≤
      (((continuousCliqueEdgePairs M).card : ℝ) * δ) *
        (2 : ℝ) ^ (continuousCliqueEdgePairs M).card := by
  let μM : Measure (Fin M → G) := Measure.pi (fun _ : Fin M => μ)
  let Kf : (Fin M → G) → ℝ := fun x => continuousCliqueKernel M f x
  let Kg : (Fin M → G) → ℝ := fun x => continuousCliqueKernel M g x
  have hKf_meas : Measurable Kf := by
    dsimp [Kf, continuousCliqueKernel]
    refine (continuousCliqueEdgePairs M).measurable_prod ?_
    intro e _he
    exact hf_meas.comp ((measurable_pi_apply e.1).sub (measurable_pi_apply e.2))
  have hKg_meas : Measurable Kg := by
    dsimp [Kg, continuousCliqueKernel]
    refine (continuousCliqueEdgePairs M).measurable_prod ?_
    intro e _he
    exact hg_meas.comp ((measurable_pi_apply e.1).sub (measurable_pi_apply e.2))
  let B : ℝ := (2 : ℝ) ^ (continuousCliqueEdgePairs M).card
  have hB_nonneg : 0 ≤ B := by
    dsimp [B]
    positivity
  have hKf_bound : ∀ᵐ x ∂μM, ‖Kf x‖ ≤ B := by
    exact Eventually.of_forall fun x => by
      dsimp [Kf, continuousCliqueKernel, B]
      rw [abs_prod]
      calc
        ∏ e ∈ continuousCliqueEdgePairs M, |f (x e.1 - x e.2)|
            ≤ ∏ _e ∈ continuousCliqueEdgePairs M, (2 : ℝ) := by
              exact Finset.prod_le_prod
                (fun e _he => abs_nonneg (f (x e.1 - x e.2)))
                (fun e _he => hf_abs _)
        _ = (2 : ℝ) ^ (continuousCliqueEdgePairs M).card := by simp
  have hKg_bound : ∀ᵐ x ∂μM, ‖Kg x‖ ≤ B := by
    exact Eventually.of_forall fun x => by
      dsimp [Kg, continuousCliqueKernel, B]
      rw [abs_prod]
      calc
        ∏ e ∈ continuousCliqueEdgePairs M, |g (x e.1 - x e.2)|
            ≤ ∏ _e ∈ continuousCliqueEdgePairs M, (2 : ℝ) := by
              exact Finset.prod_le_prod
                (fun e _he => abs_nonneg (g (x e.1 - x e.2)))
                (fun e _he => hg_abs _)
        _ = (2 : ℝ) ^ (continuousCliqueEdgePairs M).card := by simp
  have hKf_int : Integrable Kf μM :=
    Integrable.of_bound hKf_meas.aestronglyMeasurable B hKf_bound
  have hKg_int : Integrable Kg μM :=
    Integrable.of_bound hKg_meas.aestronglyMeasurable B hKg_bound
  let C : ℝ := (((continuousCliqueEdgePairs M).card : ℝ) * δ) *
    (2 : ℝ) ^ (continuousCliqueEdgePairs M).card
  have hC_nonneg : 0 ≤ C := by
    dsimp [C]
    exact mul_nonneg (mul_nonneg (Nat.cast_nonneg _) hδ_nonneg) (by positivity)
  have hdiff_bound : ∀ᵐ x ∂μM, ‖Kf x - Kg x‖ ≤ C := by
    exact Eventually.of_forall fun x => by
      simpa [Kf, Kg, C, Real.norm_eq_abs] using
        abs_continuousCliqueKernel_sub_le_card_mul_two_pow M
          hf_abs hg_abs hclose x
  have hμM_real : μM.real Set.univ = 1 := by
    haveI : IsProbabilityMeasure μM := inferInstance
    simp [Measure.real, IsProbabilityMeasure.measure_univ]
  unfold continuousCliqueDensity
  change |∫ x, Kf x ∂μM - ∫ x, Kg x ∂μM| ≤ C
  rw [← integral_sub hKf_int hKg_int]
  calc
    |∫ x, Kf x - Kg x ∂μM|
        = ‖∫ x, Kf x - Kg x ∂μM‖ := by
            simp [Real.norm_eq_abs]
    _ ≤ C * μM.real Set.univ :=
        MeasureTheory.norm_integral_le_of_norm_le_const hdiff_bound
    _ = C := by rw [hμM_real, mul_one]

/-- Route A weighted continuous avoidance kernel:
`∏ᵢ u(xᵢ) * ∏_{i<j} (1 - f(xᵢ - xⱼ))`.

In the Fourier-positive route, `f` is the compact-limit forbidden kernel and
`u` is the compact-limit dense vertex weight. -/
noncomputable def continuousWeightedAvoidanceKernel
    {G : Type u} [Sub G] (M : ℕ) (f u : G → ℝ) (x : Fin M → G) : ℝ :=
  (∏ i : Fin M, u (x i)) *
    ∏ e ∈ continuousCliqueEdgePairs M, (1 - f (x e.1 - x e.2))

/-- Route A weighted continuous avoidance density. -/
noncomputable def continuousWeightedAvoidanceDensity
    {G : Type u} [MeasurableSpace G] [Sub G]
    (μ : Measure G) (M : ℕ) (f u : G → ℝ) : ℝ :=
  ∫ x : Fin M → G, continuousWeightedAvoidanceKernel M f u x
    ∂Measure.pi (fun _ : Fin M => μ)

/-- If the continuous clique kernel is strictly positive on a nonempty open box,
then its continuous Cayley density is strictly positive.

This is the topological-measure endpoint for the `g(0) < 1` case of the compact
Cayley clique-forcing lemma: continuity gives a small open neighbourhood on
which every clique edge receives positive weight, and Haar open-positivity turns
that box into positive measure. -/
theorem continuousCliqueDensity_pos_of_pos_on_open_pi
    {G : Type u} [TopologicalSpace G] [MeasurableSpace G] [BorelSpace G]
    [Sub G] [MeasurableSub₂ G]
    (μ : Measure G) [IsProbabilityMeasure μ] [μ.IsOpenPosMeasure]
    (M : ℕ)
    (f : G → ℝ) (hf_meas : Measurable f)
    (hf_nonneg : ∀ x, 0 ≤ f x)
    (hf_le : ∀ x, f x ≤ 1)
    (U : Set G) (hUopen : IsOpen U) (hUnonempty : U.Nonempty)
    (hposU : ∀ x : Fin M → G, x ∈ Set.univ.pi (fun _ : Fin M => U) →
      0 < continuousCliqueKernel M f x) :
    0 < continuousCliqueDensity μ M f := by
  let μM : Measure (Fin M → G) := Measure.pi (fun _ : Fin M => μ)
  have hkernel_meas : Measurable (fun x : Fin M → G => continuousCliqueKernel M f x) := by
    unfold continuousCliqueKernel
    refine (continuousCliqueEdgePairs M).measurable_prod ?_
    intro e _he
    exact hf_meas.comp ((measurable_pi_apply e.1).sub (measurable_pi_apply e.2))
  have hkernel_nonneg :
      0 ≤ᵐ[μM] (fun x : Fin M → G => continuousCliqueKernel M f x) := by
    exact Eventually.of_forall fun x => by
      unfold continuousCliqueKernel
      exact Finset.prod_nonneg fun e _he => hf_nonneg _
  have hkernel_bound :
      ∀ᵐ x ∂μM, ‖continuousCliqueKernel M f x‖ ≤ 1 := by
    exact Eventually.of_forall fun x => by
      have hnonneg : 0 ≤ continuousCliqueKernel M f x := by
        unfold continuousCliqueKernel
        exact Finset.prod_nonneg fun e _he => hf_nonneg _
      have hle : continuousCliqueKernel M f x ≤ 1 := by
        unfold continuousCliqueKernel
        exact Finset.prod_le_one (fun e _he => hf_nonneg _) (fun e _he => hf_le _)
      simpa [Real.norm_eq_abs, abs_of_nonneg hnonneg] using hle
  have hkernel_int : Integrable (fun x : Fin M → G => continuousCliqueKernel M f x) μM :=
    Integrable.of_bound hkernel_meas.aestronglyMeasurable 1 hkernel_bound
  have hpi_pos : 0 < μM (Set.univ.pi (fun _ : Fin M => U)) := by
    dsimp [μM]
    rw [Measure.pi_pi]
    rw [pos_iff_ne_zero]
    exact Finset.prod_ne_zero_iff.mpr
      (fun i _hi => ne_of_gt (hUopen.measure_pos μ hUnonempty))
  have hpi_subset_support :
      Set.univ.pi (fun _ : Fin M => U) ⊆
        Function.support (fun x : Fin M → G => continuousCliqueKernel M f x) := by
    intro x hx
    exact ne_of_gt (hposU x hx)
  have hsupport_pos :
      0 < μM (Function.support (fun x : Fin M → G => continuousCliqueKernel M f x)) :=
    lt_of_lt_of_le hpi_pos (measure_mono hpi_subset_support)
  rw [continuousCliqueDensity]
  exact (MeasureTheory.integral_pos_iff_support_of_nonneg_ae hkernel_nonneg hkernel_int).mpr
    hsupport_pos

/-- Compact-Cayley Lemma 2.7, open-neighbourhood case. If the continuous
allowed kernel is positive at zero, then it is positive on a small open
neighbourhood of zero. Shrinking the neighbourhood in the two coordinates makes
every clique edge difference land there, so the continuous `K_M` density is
positive.

This proves the `g(0) < 1` branch after setting `f = 1 - g`. -/
theorem continuousCliqueDensity_pos_of_pos_at_zero
    {G : Type u} [AddCommGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G]
    [MeasurableSpace G] [BorelSpace G] [MeasurableSub₂ G]
    (μ : Measure G) [IsProbabilityMeasure μ] [μ.IsOpenPosMeasure]
    (M : ℕ)
    (f : G → ℝ) (hf_cont : Continuous f)
    (hf_nonneg : ∀ x, 0 ≤ f x)
    (hf_le : ∀ x, f x ≤ 1)
    (hzero : 0 < f 0) :
    0 < continuousCliqueDensity μ M f := by
  let V : Set G := {x | 0 < f x}
  have hVopen : IsOpen V := by
    exact isOpen_lt continuous_const hf_cont
  have hVmem : V ∈ 𝓝 (0 : G) := hVopen.mem_nhds hzero
  have hVmem' : V ∈ 𝓝 (((0 : G), (0 : G)).1 - ((0 : G), (0 : G)).2) := by
    simpa using hVmem
  have hpre : (fun z : G × G => z.1 - z.2) ⁻¹' V ∈ 𝓝 ((0 : G), (0 : G)) := by
    convert (continuous_fst.sub continuous_snd).continuousAt hVmem' using 1
    rfl
  rcases mem_nhds_prod_iff'.mp hpre with
    ⟨U₁, U₂, hU₁open, hU₁zero, hU₂open, hU₂zero, hUsub⟩
  let U : Set G := U₁ ∩ U₂
  have hUopen : IsOpen U := hU₁open.inter hU₂open
  have hUnonempty : U.Nonempty := ⟨0, hU₁zero, hU₂zero⟩
  refine continuousCliqueDensity_pos_of_pos_on_open_pi μ M f hf_cont.measurable hf_nonneg
    hf_le U hUopen hUnonempty ?_
  intro x hx
  unfold continuousCliqueKernel
  refine Finset.prod_pos ?_
  intro e he
  have hx₁ : x e.1 ∈ U := hx e.1 (by simp)
  have hx₂ : x e.2 ∈ U := hx e.2 (by simp)
  have hpair : (x e.1, x e.2) ∈ U₁ ×ˢ U₂ := ⟨hx₁.1, hx₂.2⟩
  exact hUsub hpair

/-- A closed proper subgroup of a connected compact abelian Hausdorff group is
Haar-null. Geometric core of Layer 1; no Fourier content.

Argument: assume `μ H ≠ 0`. The cosets of `H` partition `G`, each with the same
measure `μ H` by translation invariance. With finite total measure and a
constant positive contribution, only finitely many cosets exist; hence
`H.FiniteIndex`. A closed finite-index subgroup is open
(`AddSubgroup.isOpen_of_isClosed_of_finiteIndex`). A non-empty clopen subset of
a connected space is the whole space, contradicting `H` proper. -/
theorem closed_proper_subgroup_haar_null
    {G : Type u} [AddCommGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G]
    [CompactSpace G] [T2Space G] [ConnectedSpace G]
    [MeasurableSpace G] [BorelSpace G]
    (μ : Measure G) [μ.IsAddHaarMeasure] [IsFiniteMeasure μ]
    (H : AddSubgroup G) (hH_closed : IsClosed (H : Set G))
    (hH_proper : (H : Set G) ≠ Set.univ) :
    μ (H : Set G) = 0 := by
  by_contra hμH_ne
  have hH_meas : MeasurableSet (H : Set G) := hH_closed.measurableSet
  obtain ⟨s, hs, _⟩ := H.exists_isComplement_left 0
  have hs_finite : Finite s := by
    rcases finite_or_infinite s with hfin | hinf
    · exact hfin
    · exfalso
      let e : ℕ ↪ s := Infinite.natEmbedding s
      let f : ℕ → Set G := fun n => (e n).val +ᵥ (H : Set G)
      have h_disjoint : Pairwise (fun m n : ℕ => Disjoint (f m) (f n)) := by
        intro m n hmn
        have : (e m).val ≠ (e n).val :=
          fun h => hmn (e.injective (Subtype.ext h))
        exact hs.pairwiseDisjoint_vadd (e m).2 (e n).2 this
      have h_meas : ∀ n : ℕ, MeasurableSet (f n) :=
        fun n => hH_meas.const_vadd _
      have h_const : ∀ n : ℕ, μ (f n) = μ (H : Set G) :=
        fun n => measure_vadd μ (e n).val _
      have h_subset : (⋃ n : ℕ, f n) ⊆ Set.univ := fun _ _ => trivial
      have hμ_iUnion : μ (⋃ n : ℕ, f n) = ∑' n : ℕ, μ (f n) :=
        measure_iUnion h_disjoint h_meas
      have h_top : (∑' _ : ℕ, μ (H : Set G)) = ⊤ :=
        ENNReal.tsum_const_eq_top_of_ne_zero hμH_ne
      have hμ_top : μ (⋃ n : ℕ, f n) = ⊤ := by
        rw [hμ_iUnion, tsum_congr h_const]; exact h_top
      have hμ_univ_top : μ (Set.univ : Set G) = ⊤ :=
        top_unique (hμ_top ▸ measure_mono h_subset)
      exact absurd hμ_univ_top (ne_of_lt IsFiniteMeasure.measure_univ_lt_top)
  have hH_findex : H.FiniteIndex := hs.finite_left_iff.mp hs_finite
  have hH_open : IsOpen (H : Set G) :=
    AddSubgroup.isOpen_of_isClosed_of_finiteIndex H hH_closed
  exact hH_proper (IsClopen.eq_univ ⟨hH_closed, hH_open⟩ ⟨0, H.zero_mem⟩)

/-- A closed subgroup of infinite index is Haar-null.

This is the finite-index half of `closed_proper_subgroup_haar_null`, isolated
for compact duals where proving connectedness is overkill. Positive Haar
measure for `H` forces only finitely many cosets by the same disjoint-coset
counting argument used above. -/
theorem closed_subgroup_haar_null_of_not_finiteIndex
    {G : Type u} [AddCommGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G]
    [MeasurableSpace G] [BorelSpace G]
    (μ : Measure G) [μ.IsAddHaarMeasure] [IsFiniteMeasure μ]
    (H : AddSubgroup G) (hH_closed : IsClosed (H : Set G))
    (hH_not_finiteIndex : ¬ H.FiniteIndex) :
    μ (H : Set G) = 0 := by
  by_contra hμH_ne
  have hH_meas : MeasurableSet (H : Set G) := hH_closed.measurableSet
  obtain ⟨s, hs, _⟩ := H.exists_isComplement_left 0
  have hs_finite : Finite s := by
    rcases finite_or_infinite s with hfin | hinf
    · exact hfin
    · exfalso
      let e : ℕ ↪ s := Infinite.natEmbedding s
      let f : ℕ → Set G := fun n => (e n).val +ᵥ (H : Set G)
      have h_disjoint : Pairwise (fun m n : ℕ => Disjoint (f m) (f n)) := by
        intro m n hmn
        have : (e m).val ≠ (e n).val :=
          fun h => hmn (e.injective (Subtype.ext h))
        exact hs.pairwiseDisjoint_vadd (e m).2 (e n).2 this
      have h_meas : ∀ n : ℕ, MeasurableSet (f n) :=
        fun n => hH_meas.const_vadd _
      have h_const : ∀ n : ℕ, μ (f n) = μ (H : Set G) :=
        fun n => measure_vadd μ (e n).val _
      have h_subset : (⋃ n : ℕ, f n) ⊆ Set.univ := fun _ _ => trivial
      have hμ_iUnion : μ (⋃ n : ℕ, f n) = ∑' n : ℕ, μ (f n) :=
        measure_iUnion h_disjoint h_meas
      have h_top : (∑' _ : ℕ, μ (H : Set G)) = ⊤ :=
        ENNReal.tsum_const_eq_top_of_ne_zero hμH_ne
      have hμ_top : μ (⋃ n : ℕ, f n) = ⊤ := by
        rw [hμ_iUnion, tsum_congr h_const]; exact h_top
      have hμ_univ_top : μ (Set.univ : Set G) = ⊤ :=
        top_unique (hμ_top ▸ measure_mono h_subset)
      exact absurd hμ_univ_top (ne_of_lt IsFiniteMeasure.measure_univ_lt_top)
  exact hH_not_finiteIndex (hs.finite_left_iff.mp hs_finite)

/-- If `H` is Haar-null, then the set of finite tuples whose `i,j` difference
lands in `H` is null. This is the Fubini/shear step used in Tao's continuous
avoidance lemma.

The proof splits off the `i`-th coordinate, evaluates the `j`-th coordinate in
the remaining product, and then uses the Haar-preserving shear
`(x, y) ↦ (x - y, y)` on `G × G`. -/
theorem pi_pair_sub_mem_null
    {G : Type u} [AddCommGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G]
    [MeasurableSpace G] [BorelSpace G] [MeasurableAdd₂ G] [MeasurableNeg G]
    (μ : Measure G) [μ.IsAddHaarMeasure] [IsProbabilityMeasure μ]
    {M : ℕ} (H : AddSubgroup G) (hH_closed : IsClosed (H : Set G))
    (hμH : μ (H : Set G) = 0)
    (i j : Fin M) (hij : i ≠ j) :
    Measure.pi (fun _ : Fin M => μ)
      {x : Fin M → G | x i - x j ∈ (H : Set G)} = 0 := by
  cases M with
  | zero =>
      exact Fin.elim0 i
  | succ n =>
      obtain ⟨k, hk⟩ :=
        Fin.exists_succAbove_eq (x := j) (y := i) (by simpa [ne_comm] using hij)
      have hsplit :
          MeasurePreserving (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => G) i)
            (Measure.pi (fun _ : Fin (n + 1) => μ))
            (μ.prod (Measure.pi (fun _ : Fin n => μ))) := by
        simpa using
          (measurePreserving_piFinSuccAbove (α := fun _ : Fin (n + 1) => G)
            (fun _ : Fin (n + 1) => μ) i)
      have hrest :
          MeasurePreserving (Function.eval k)
            (Measure.pi (fun _ : Fin n => μ)) μ :=
        measurePreserving_eval (fun _ : Fin n => μ) k
      have hpair_after :
          MeasurePreserving
            (Prod.map (fun x : G => x) (Function.eval k))
            (μ.prod (Measure.pi (fun _ : Fin n => μ))) (μ.prod μ) :=
        MeasurePreserving.prod
          (MeasurePreserving.id μ : MeasurePreserving (fun x : G => x) μ μ) hrest
      have hpair :
          MeasurePreserving (fun x : Fin (n + 1) → G => (x i, x j))
            (Measure.pi (fun _ : Fin (n + 1) => μ)) (μ.prod μ) := by
        convert hpair_after.comp hsplit using 1
        ext x
        · simp
        · rw [← hk]
          rfl
      have hdiff_prod :
          MeasurePreserving (fun z : G × G => (z.1 - z.2, z.2))
            (μ.prod μ) (μ.prod μ) := by
        simpa using (measurePreserving_sub_prod (μ := μ) (ν := μ))
      have hdiff :
          MeasurePreserving (fun z : G × G => z.1 - z.2)
            (μ.prod μ) μ := by
        simpa [Function.comp_def] using
          (measurePreserving_fst (μ := μ) (ν := μ)).comp hdiff_prod
      have hmap :
          MeasurePreserving (fun x : Fin (n + 1) → G => x i - x j)
            (Measure.pi (fun _ : Fin (n + 1) => μ)) μ := by
        simpa [Function.comp_def] using hdiff.comp hpair
      have hH_meas : MeasurableSet (H : Set G) := hH_closed.measurableSet
      calc
        Measure.pi (fun _ : Fin (n + 1) => μ)
            {x : Fin (n + 1) → G | x i - x j ∈ (H : Set G)}
            = (Measure.map (fun x : Fin (n + 1) → G => x i - x j)
                (Measure.pi (fun _ : Fin (n + 1) => μ))) (H : Set G) := by
              change Measure.pi (fun _ : Fin (n + 1) => μ)
                  ((fun x : Fin (n + 1) → G => x i - x j) ⁻¹' (H : Set G)) = _
              rw [Measure.map_apply hmap.measurable hH_meas]
        _ = μ (H : Set G) := by rw [hmap.map_eq]
        _ = 0 := hμH

/-- Compact-clique-forcing endpoint, case where the zero set is a proper
closed subgroup. If `f ≥ 0` and `f` vanishes exactly on such a subgroup, then
the continuous Cayley `K_M` density is strictly positive.

This is the measure-theoretic part of compact-Cayley Lemma 2.7 after the
Fourier/positive-definite argument has identified the level set
`{x | f x = 0}` as a proper closed subgroup. -/
theorem continuousCliqueDensity_pos_of_zeroLevel_null_subgroup
    {G : Type u} [AddCommGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G]
    [MeasurableSpace G] [BorelSpace G] [MeasurableSub₂ G]
    [MeasurableAdd₂ G] [MeasurableNeg G]
    (μ : Measure G) [μ.IsAddHaarMeasure] [IsProbabilityMeasure μ]
    (M : ℕ)
    (f : G → ℝ) (hf_meas : Measurable f)
    (hf_nonneg : ∀ x, 0 ≤ f x)
    (hf_le : ∀ x, f x ≤ 1)
    (H : AddSubgroup G) (hH_closed : IsClosed (H : Set G))
    (hH_eq : ∀ x : G, x ∈ H ↔ f x = 0)
    (hμH : μ (H : Set G) = 0) :
    0 < continuousCliqueDensity μ M f := by
  have h_pair_null :
      ∀ i j : Fin M, i ≠ j →
        Measure.pi (fun _ : Fin M => μ)
          {x : Fin M → G | x i - x j ∈ (H : Set G)} = 0 := by
    intro i j hij
    exact pi_pair_sub_mem_null μ H hH_closed hμH i j hij
  have h_bad_null :
      Measure.pi (fun _ : Fin M => μ)
        (⋃ (i : Fin M) (j : Fin M) (_ : i < j),
          {x : Fin M → G | x i - x j ∈ (H : Set G)}) = 0 := by
    refine measure_iUnion_null fun i => measure_iUnion_null fun j => ?_
    by_cases hij : i < j
    · simp only [hij, Set.iUnion_true]
      exact h_pair_null i j (ne_of_lt hij)
    · simp only [hij, Set.iUnion_of_empty, measure_empty]
  have h_ae_avoid : ∀ᵐ (x : Fin M → G) ∂(Measure.pi (fun _ : Fin M => μ)),
      ∀ i j : Fin M, i < j → x i - x j ∉ (H : Set G) := by
    rw [ae_iff]
    refine measure_mono_null ?_ h_bad_null
    intro x hx
    push Not at hx
    obtain ⟨i, j, hij, hmem⟩ := hx
    exact Set.mem_iUnion.mpr
      ⟨i, Set.mem_iUnion.mpr ⟨j, Set.mem_iUnion.mpr ⟨hij, hmem⟩⟩⟩
  have hkernel_meas :
      Measurable (fun x : Fin M → G => continuousCliqueKernel M f x) := by
    unfold continuousCliqueKernel
    refine (continuousCliqueEdgePairs M).measurable_prod ?_
    intro e _he
    exact hf_meas.comp ((measurable_pi_apply e.1).sub (measurable_pi_apply e.2))
  have hkernel_nonneg :
      0 ≤ᵐ[Measure.pi (fun _ : Fin M => μ)]
        (fun x : Fin M → G => continuousCliqueKernel M f x) := by
    exact Eventually.of_forall fun x => by
      unfold continuousCliqueKernel
      exact Finset.prod_nonneg fun e _he => hf_nonneg _
  have hkernel_bound :
      ∀ᵐ x ∂Measure.pi (fun _ : Fin M => μ),
        ‖continuousCliqueKernel M f x‖ ≤ 1 := by
    exact Eventually.of_forall fun x => by
      have hnonneg : 0 ≤ continuousCliqueKernel M f x := by
        unfold continuousCliqueKernel
        exact Finset.prod_nonneg fun e _he => hf_nonneg _
      have hle : continuousCliqueKernel M f x ≤ 1 := by
        unfold continuousCliqueKernel
        exact Finset.prod_le_one (fun e _he => hf_nonneg _) (fun e _he => hf_le _)
      simpa [Real.norm_eq_abs, abs_of_nonneg hnonneg] using hle
  have hkernel_int :
      Integrable (fun x : Fin M → G => continuousCliqueKernel M f x)
        (Measure.pi (fun _ : Fin M => μ)) :=
    Integrable.of_bound hkernel_meas.aestronglyMeasurable 1 hkernel_bound
  have hkernel_pos :
      ∀ᵐ x ∂Measure.pi (fun _ : Fin M => μ),
        0 < continuousCliqueKernel M f x := by
    filter_upwards [h_ae_avoid] with x hx
    unfold continuousCliqueKernel
    refine Finset.prod_pos ?_
    intro e he
    have hlt : e.1 < e.2 := (Finset.mem_filter.mp he).2
    have hnot : x e.1 - x e.2 ∉ (H : Set G) := hx e.1 e.2 hlt
    have hne : f (x e.1 - x e.2) ≠ 0 := by
      intro hzero
      exact hnot ((hH_eq (x e.1 - x e.2)).mpr hzero)
    exact lt_of_le_of_ne (hf_nonneg _) hne.symm
  exact integral_pos_of_ae_pos_of_nonneg
    (Measure.pi (fun _ : Fin M => μ)) hkernel_int hkernel_nonneg hkernel_pos

theorem continuousCliqueDensity_pos_of_zeroLevel_proper_subgroup
    {G : Type u} [AddCommGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G]
    [CompactSpace G] [T2Space G] [ConnectedSpace G]
    [MeasurableSpace G] [BorelSpace G] [MeasurableSub₂ G]
    [MeasurableAdd₂ G] [MeasurableNeg G]
    (μ : Measure G) [μ.IsAddHaarMeasure] [IsProbabilityMeasure μ]
    (M : ℕ)
    (f : G → ℝ) (hf_meas : Measurable f)
    (hf_nonneg : ∀ x, 0 ≤ f x)
    (hf_le : ∀ x, f x ≤ 1)
    (H : AddSubgroup G) (hH_closed : IsClosed (H : Set G))
    (hH_eq : ∀ x : G, x ∈ H ↔ f x = 0)
    (hH_proper : (H : Set G) ≠ Set.univ) :
    0 < continuousCliqueDensity μ M f := by
  have hμH : μ (H : Set G) = 0 :=
    closed_proper_subgroup_haar_null μ H hH_closed hH_proper
  exact continuousCliqueDensity_pos_of_zeroLevel_null_subgroup μ M f
    hf_meas hf_nonneg hf_le H hH_closed hH_eq hμH

/-- Compact-Cayley Lemma 2.7 endpoint after the positive-definite argument has
identified the level set `{x | g x = 1}` as a Haar-null closed subgroup.
Applying the zero-level null-subgroup theorem to `f = 1 - g` gives positive
continuous clique density for the allowed kernel. -/
theorem continuousCliqueDensity_pos_of_one_sub_level_one_null_subgroup
    {G : Type u} [AddCommGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G]
    [MeasurableSpace G] [BorelSpace G] [MeasurableSub₂ G]
    [MeasurableAdd₂ G] [MeasurableNeg G]
    (μ : Measure G) [μ.IsAddHaarMeasure] [IsProbabilityMeasure μ]
    (M : ℕ)
    (g : G → ℝ) (hg_meas : Measurable g)
    (hg_nonneg : ∀ x, 0 ≤ g x)
    (hg_le : ∀ x, g x ≤ 1)
    (H : AddSubgroup G) (hH_closed : IsClosed (H : Set G))
    (hH_eq : ∀ x : G, x ∈ H ↔ g x = 1)
    (hμH : μ (H : Set G) = 0) :
    0 < continuousCliqueDensity μ M (fun x => 1 - g x) := by
  refine continuousCliqueDensity_pos_of_zeroLevel_null_subgroup μ M
    (fun x => 1 - g x) ?_ ?_ ?_ H hH_closed ?_ hμH
  · exact measurable_const.sub hg_meas
  · intro x
    linarith [hg_le x]
  · intro x
    linarith [hg_nonneg x]
  · intro x
    constructor
    · intro hx
      have hg : g x = 1 := (hH_eq x).mp hx
      linarith
    · intro hzero
      exact (hH_eq x).mpr (by linarith)

/-- Version of the compact-Cayley level-one endpoint where the level-one
subgroup is known to have infinite index.  The general Haar theorem converts
that algebraic hypothesis into nullness. -/
theorem continuousCliqueDensity_pos_of_one_sub_level_one_not_finiteIndex_subgroup
    {G : Type u} [AddCommGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G]
    [MeasurableSpace G] [BorelSpace G] [MeasurableSub₂ G]
    [MeasurableAdd₂ G] [MeasurableNeg G]
    (μ : Measure G) [μ.IsAddHaarMeasure] [IsProbabilityMeasure μ]
    (M : ℕ)
    (g : G → ℝ) (hg_meas : Measurable g)
    (hg_nonneg : ∀ x, 0 ≤ g x)
    (hg_le : ∀ x, g x ≤ 1)
    (H : AddSubgroup G) (hH_closed : IsClosed (H : Set G))
    (hH_eq : ∀ x : G, x ∈ H ↔ g x = 1)
    (hH_not_finiteIndex : ¬ H.FiniteIndex) :
    0 < continuousCliqueDensity μ M (fun x => 1 - g x) :=
  continuousCliqueDensity_pos_of_one_sub_level_one_null_subgroup μ M g
    hg_meas hg_nonneg hg_le H hH_closed hH_eq
    (closed_subgroup_haar_null_of_not_finiteIndex μ H hH_closed hH_not_finiteIndex)

/-- Compact-Cayley Lemma 2.7 endpoint after the positive-definite argument has
identified the level set `{x | g x = 1}` as a proper closed subgroup.  Applying
the previous theorem to `f = 1 - g` gives positive continuous clique density
for the allowed kernel. -/
theorem continuousCliqueDensity_pos_of_one_sub_level_one_proper_subgroup
    {G : Type u} [AddCommGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G]
    [CompactSpace G] [T2Space G] [ConnectedSpace G]
    [MeasurableSpace G] [BorelSpace G] [MeasurableSub₂ G]
    [MeasurableAdd₂ G] [MeasurableNeg G]
    (μ : Measure G) [μ.IsAddHaarMeasure] [IsProbabilityMeasure μ]
    (M : ℕ)
    (g : G → ℝ) (hg_meas : Measurable g)
    (hg_nonneg : ∀ x, 0 ≤ g x)
    (hg_le : ∀ x, g x ≤ 1)
    (H : AddSubgroup G) (hH_closed : IsClosed (H : Set G))
    (hH_eq : ∀ x : G, x ∈ H ↔ g x = 1)
    (hH_proper : (H : Set G) ≠ Set.univ) :
    0 < continuousCliqueDensity μ M (fun x => 1 - g x) := by
  refine continuousCliqueDensity_pos_of_zeroLevel_proper_subgroup μ M
    (fun x => 1 - g x) ?_ ?_ ?_ H hH_closed ?_ hH_proper
  · exact measurable_const.sub hg_meas
  · intro x
    linarith [hg_le x]
  · intro x
    linarith [hg_nonneg x]
  · intro x
    constructor
    · intro hx
      have hg : g x = 1 := (hH_eq x).mp hx
      linarith
    · intro hzero
      exact (hH_eq x).mpr (by linarith)

/-- Route A weighted endpoint after the positive-definite argument identifies
the level set `{x | f x = 1}` as a proper closed subgroup.

If `u` is positive on a set of positive Haar measure, then almost every tuple in
that positive-measure vertex box avoids the subgroup in every pairwise
difference.  On that set all vertex factors `u(xᵢ)` and edge factors
`1 - f(xᵢ - xⱼ)` are strictly positive, so the weighted avoidance integral is
strictly positive. -/
theorem continuousWeightedAvoidanceDensity_pos_of_level_one_null_subgroup
    {G : Type u} [AddCommGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G]
    [MeasurableSpace G] [BorelSpace G] [MeasurableSub₂ G]
    [MeasurableAdd₂ G] [MeasurableNeg G]
    (μ : Measure G) [μ.IsAddHaarMeasure] [IsProbabilityMeasure μ]
    (M : ℕ)
    (f u : G → ℝ) (hf_meas : Measurable f) (hu_meas : Measurable u)
    (hf_nonneg : ∀ x, 0 ≤ f x)
    (hf_le : ∀ x, f x ≤ 1)
    (hu_nonneg : ∀ x, 0 ≤ u x)
    (hu_le : ∀ x, u x ≤ 1)
    (H : AddSubgroup G) (hH_closed : IsClosed (H : Set G))
    (hH_eq : ∀ x : G, x ∈ H ↔ f x = 1)
    (hμH : μ (H : Set G) = 0)
    (hu_pos_set : 0 < μ {x : G | 0 < u x}) :
    0 < continuousWeightedAvoidanceDensity μ M f u := by
  let μM : Measure (Fin M → G) := Measure.pi (fun _ : Fin M => μ)
  let S : Set G := {x : G | 0 < u x}
  let Bad : Set (Fin M → G) :=
    ⋃ (i : Fin M) (j : Fin M) (_ : i < j),
      {x : Fin M → G | x i - x j ∈ (H : Set G)}
  let K : (Fin M → G) → ℝ := fun x => continuousWeightedAvoidanceKernel M f u x
  have h_pair_null :
      ∀ i j : Fin M, i ≠ j →
        μM {x : Fin M → G | x i - x j ∈ (H : Set G)} = 0 := by
    intro i j hij
    dsimp [μM]
    exact pi_pair_sub_mem_null μ H hH_closed hμH i j hij
  have h_bad_null : μM Bad = 0 := by
    dsimp [Bad, μM]
    refine measure_iUnion_null fun i => measure_iUnion_null fun j => ?_
    by_cases hij : i < j
    · simp only [hij, Set.iUnion_true]
      exact h_pair_null i j (ne_of_lt hij)
    · simp only [hij, Set.iUnion_of_empty, measure_empty]
  have hkernel_meas : Measurable K := by
    dsimp [K, continuousWeightedAvoidanceKernel]
    refine
      ((Finset.univ : Finset (Fin M)).measurable_prod
        (fun i _hi => hu_meas.comp (measurable_pi_apply i))).mul ?_
    refine (continuousCliqueEdgePairs M).measurable_prod ?_
    intro e _he
    exact measurable_const.sub
      (hf_meas.comp ((measurable_pi_apply e.1).sub (measurable_pi_apply e.2)))
  have hkernel_nonneg : 0 ≤ᵐ[μM] K := by
    exact Eventually.of_forall fun x => by
      dsimp [K, continuousWeightedAvoidanceKernel]
      refine mul_nonneg ?_ ?_
      · exact Finset.prod_nonneg fun i _hi => hu_nonneg _
      · exact Finset.prod_nonneg fun e _he => by linarith [hf_le (x e.1 - x e.2)]
  have hkernel_bound : ∀ᵐ x ∂μM, ‖K x‖ ≤ 1 := by
    exact Eventually.of_forall fun x => by
      have hv_nonneg : 0 ≤ ∏ i : Fin M, u (x i) :=
        Finset.prod_nonneg fun i _hi => hu_nonneg _
      have hv_le : (∏ i : Fin M, u (x i)) ≤ 1 :=
        Finset.prod_le_one (fun i _hi => hu_nonneg _) (fun i _hi => hu_le _)
      have he_nonneg :
          0 ≤ ∏ e ∈ continuousCliqueEdgePairs M, (1 - f (x e.1 - x e.2)) :=
        Finset.prod_nonneg fun e _he => by linarith [hf_le (x e.1 - x e.2)]
      have he_le :
          (∏ e ∈ continuousCliqueEdgePairs M, (1 - f (x e.1 - x e.2))) ≤ 1 :=
        Finset.prod_le_one
          (fun e _he => by linarith [hf_le (x e.1 - x e.2)])
          (fun e _he => by linarith [hf_nonneg (x e.1 - x e.2)])
      have hnonneg : 0 ≤ K x := by
        dsimp [K, continuousWeightedAvoidanceKernel]
        exact mul_nonneg hv_nonneg he_nonneg
      have hle : K x ≤ 1 := by
        dsimp [K, continuousWeightedAvoidanceKernel]
        calc
          (∏ i : Fin M, u (x i)) *
              ∏ e ∈ continuousCliqueEdgePairs M, (1 - f (x e.1 - x e.2))
              ≤ 1 * 1 := mul_le_mul hv_le he_le he_nonneg (by norm_num)
          _ = 1 := by norm_num
      simpa [Real.norm_eq_abs, abs_of_nonneg hnonneg] using hle
  have hkernel_int : Integrable K μM :=
    Integrable.of_bound hkernel_meas.aestronglyMeasurable 1 hkernel_bound
  have hpiS_pos : 0 < μM (Set.univ.pi (fun _ : Fin M => S)) := by
    dsimp [μM, S]
    rw [Measure.pi_pi]
    rw [pos_iff_ne_zero]
    exact Finset.prod_ne_zero_iff.mpr
      (fun _i _hi => ne_of_gt hu_pos_set)
  have hpiS_subset : Set.univ.pi (fun _ : Fin M => S) ⊆ Function.support K ∪ Bad := by
    intro x hxS
    by_cases hxBad : x ∈ Bad
    · exact Or.inr hxBad
    · refine Or.inl ?_
      have havoid :
          ∀ i j : Fin M, i < j → x i - x j ∉ (H : Set G) := by
        intro i j hij hmem
        exact hxBad (Set.mem_iUnion.mpr
          ⟨i, Set.mem_iUnion.mpr
            ⟨j, Set.mem_iUnion.mpr ⟨hij, hmem⟩⟩⟩)
      have hv_pos : 0 < ∏ i : Fin M, u (x i) := by
        refine Finset.prod_pos ?_
        intro i _hi
        exact hxS i (by simp)
      have he_pos :
          0 < ∏ e ∈ continuousCliqueEdgePairs M, (1 - f (x e.1 - x e.2)) := by
        refine Finset.prod_pos ?_
        intro e he
        have hlt : e.1 < e.2 := (Finset.mem_filter.mp he).2
        have hnot : x e.1 - x e.2 ∉ (H : Set G) := havoid e.1 e.2 hlt
        have hne : f (x e.1 - x e.2) ≠ 1 := by
          intro hone
          exact hnot ((hH_eq (x e.1 - x e.2)).mpr hone)
        have hlt_one : f (x e.1 - x e.2) < 1 :=
          lt_of_le_of_ne (hf_le (x e.1 - x e.2)) hne
        linarith
      exact ne_of_gt (by
        dsimp [K, continuousWeightedAvoidanceKernel]
        exact mul_pos hv_pos he_pos)
  have hsupport_pos : 0 < μM (Function.support K) := by
    by_contra hnot
    have hsupport_zero : μM (Function.support K) = 0 :=
      le_antisymm (not_lt.mp hnot) bot_le
    have hpiS_zero : μM (Set.univ.pi (fun _ : Fin M => S)) = 0 := by
      refine le_antisymm ?_ bot_le
      calc
        μM (Set.univ.pi (fun _ : Fin M => S)) ≤ μM (Function.support K ∪ Bad) :=
          measure_mono hpiS_subset
        _ ≤ μM (Function.support K) + μM Bad := measure_union_le _ _
        _ = 0 := by simp [hsupport_zero, h_bad_null]
    exact (ne_of_gt hpiS_pos) hpiS_zero
  rw [continuousWeightedAvoidanceDensity]
  exact (MeasureTheory.integral_pos_iff_support_of_nonneg_ae hkernel_nonneg hkernel_int).mpr
    hsupport_pos

/-- Route A weighted endpoint after the positive-definite argument identifies
the level set `{x | f x = 1}` as a proper closed subgroup of a connected compact
group.  This wrapper proves Haar-nullness from connectedness and then applies
the sharper null-subgroup endpoint. -/
theorem continuousWeightedAvoidanceDensity_pos_of_level_one_proper_subgroup
    {G : Type u} [AddCommGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G]
    [CompactSpace G] [T2Space G] [ConnectedSpace G]
    [MeasurableSpace G] [BorelSpace G] [MeasurableSub₂ G]
    [MeasurableAdd₂ G] [MeasurableNeg G]
    (μ : Measure G) [μ.IsAddHaarMeasure] [IsProbabilityMeasure μ]
    (M : ℕ)
    (f u : G → ℝ) (hf_meas : Measurable f) (hu_meas : Measurable u)
    (hf_nonneg : ∀ x, 0 ≤ f x)
    (hf_le : ∀ x, f x ≤ 1)
    (hu_nonneg : ∀ x, 0 ≤ u x)
    (hu_le : ∀ x, u x ≤ 1)
    (H : AddSubgroup G) (hH_closed : IsClosed (H : Set G))
    (hH_eq : ∀ x : G, x ∈ H ↔ f x = 1)
    (hH_proper : (H : Set G) ≠ Set.univ)
    (hu_pos_set : 0 < μ {x : G | 0 < u x}) :
    0 < continuousWeightedAvoidanceDensity μ M f u :=
  continuousWeightedAvoidanceDensity_pos_of_level_one_null_subgroup μ M
    f u hf_meas hu_meas hf_nonneg hf_le hu_nonneg hu_le H hH_closed hH_eq
    (closed_proper_subgroup_haar_null μ H hH_closed hH_proper) hu_pos_set

/-- Integral-positive version of
`continuousWeightedAvoidanceDensity_pos_of_level_one_null_subgroup`.

This is the narrow Route A endpoint: the level-one subgroup is assumed
Haar-null directly, avoiding a separate connectedness hypothesis. -/
theorem continuousWeightedAvoidanceDensity_pos_of_level_one_null_subgroup_of_integral_pos
    {G : Type u} [AddCommGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G]
    [MeasurableSpace G] [BorelSpace G] [MeasurableSub₂ G]
    [MeasurableAdd₂ G] [MeasurableNeg G]
    (μ : Measure G) [μ.IsAddHaarMeasure] [IsProbabilityMeasure μ]
    (M : ℕ)
    (f u : G → ℝ) (hf_meas : Measurable f) (hu_meas : Measurable u)
    (hf_nonneg : ∀ x, 0 ≤ f x)
    (hf_le : ∀ x, f x ≤ 1)
    (hu_nonneg : ∀ x, 0 ≤ u x)
    (hu_le : ∀ x, u x ≤ 1)
    (H : AddSubgroup G) (hH_closed : IsClosed (H : Set G))
    (hH_eq : ∀ x : G, x ∈ H ↔ f x = 1)
    (hμH : μ (H : Set G) = 0)
    (hu_integral_pos : 0 < ∫ x, u x ∂μ) :
    0 < continuousWeightedAvoidanceDensity μ M f u := by
  have hu_bound : ∀ᵐ x ∂μ, ‖u x‖ ≤ 1 := by
    exact Eventually.of_forall fun x => by
      simpa [Real.norm_eq_abs, abs_of_nonneg (hu_nonneg x)] using hu_le x
  have hu_int : Integrable u μ :=
    Integrable.of_bound hu_meas.aestronglyMeasurable 1 hu_bound
  have hsupp_pos : 0 < μ (Function.support u) :=
    (MeasureTheory.integral_pos_iff_support_of_nonneg
      (fun x => hu_nonneg x) hu_int).mp hu_integral_pos
  have hsupp_subset : Function.support u ⊆ {x : G | 0 < u x} := by
    intro x hx
    exact lt_of_le_of_ne (hu_nonneg x) hx.symm
  have hu_pos_set : 0 < μ {x : G | 0 < u x} :=
    lt_of_lt_of_le hsupp_pos (measure_mono hsupp_subset)
  exact continuousWeightedAvoidanceDensity_pos_of_level_one_null_subgroup μ M
    f u hf_meas hu_meas hf_nonneg hf_le hu_nonneg hu_le H hH_closed
    hH_eq hμH hu_pos_set

/-- Route A null-subgroup endpoint with the usual compact-model lower bound
`α ≤ ∫ u`, `α > 0`. -/
theorem continuousWeightedAvoidanceDensity_pos_of_level_one_null_subgroup_of_integral_ge
    {G : Type u} [AddCommGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G]
    [MeasurableSpace G] [BorelSpace G] [MeasurableSub₂ G]
    [MeasurableAdd₂ G] [MeasurableNeg G]
    (μ : Measure G) [μ.IsAddHaarMeasure] [IsProbabilityMeasure μ]
    (M : ℕ)
    (f u : G → ℝ) (hf_meas : Measurable f) (hu_meas : Measurable u)
    (hf_nonneg : ∀ x, 0 ≤ f x)
    (hf_le : ∀ x, f x ≤ 1)
    (hu_nonneg : ∀ x, 0 ≤ u x)
    (hu_le : ∀ x, u x ≤ 1)
    (H : AddSubgroup G) (hH_closed : IsClosed (H : Set G))
    (hH_eq : ∀ x : G, x ∈ H ↔ f x = 1)
    (hμH : μ (H : Set G) = 0)
    {α : ℝ} (hα : 0 < α) (hmean_u : α ≤ ∫ x, u x ∂μ) :
    0 < continuousWeightedAvoidanceDensity μ M f u :=
  continuousWeightedAvoidanceDensity_pos_of_level_one_null_subgroup_of_integral_pos μ M
    f u hf_meas hu_meas hf_nonneg hf_le hu_nonneg hu_le H hH_closed hH_eq hμH
    (lt_of_lt_of_le hα hmean_u)

/-- Integral-positive version of
`continuousWeightedAvoidanceDensity_pos_of_level_one_proper_subgroup`.

This is closer to the Route A compact model: the dense vertex weight satisfies
`∫ u > 0`, hence `{x | 0 < u x}` has positive Haar measure. -/
theorem continuousWeightedAvoidanceDensity_pos_of_level_one_proper_subgroup_of_integral_pos
    {G : Type u} [AddCommGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G]
    [CompactSpace G] [T2Space G] [ConnectedSpace G]
    [MeasurableSpace G] [BorelSpace G] [MeasurableSub₂ G]
    [MeasurableAdd₂ G] [MeasurableNeg G]
    (μ : Measure G) [μ.IsAddHaarMeasure] [IsProbabilityMeasure μ]
    (M : ℕ)
    (f u : G → ℝ) (hf_meas : Measurable f) (hu_meas : Measurable u)
    (hf_nonneg : ∀ x, 0 ≤ f x)
    (hf_le : ∀ x, f x ≤ 1)
    (hu_nonneg : ∀ x, 0 ≤ u x)
    (hu_le : ∀ x, u x ≤ 1)
    (H : AddSubgroup G) (hH_closed : IsClosed (H : Set G))
    (hH_eq : ∀ x : G, x ∈ H ↔ f x = 1)
    (hH_proper : (H : Set G) ≠ Set.univ)
    (hu_integral_pos : 0 < ∫ x, u x ∂μ) :
    0 < continuousWeightedAvoidanceDensity μ M f u := by
  have hu_bound : ∀ᵐ x ∂μ, ‖u x‖ ≤ 1 := by
    exact Eventually.of_forall fun x => by
      simpa [Real.norm_eq_abs, abs_of_nonneg (hu_nonneg x)] using hu_le x
  have hu_int : Integrable u μ :=
    Integrable.of_bound hu_meas.aestronglyMeasurable 1 hu_bound
  have hsupp_pos : 0 < μ (Function.support u) :=
    (MeasureTheory.integral_pos_iff_support_of_nonneg
      (fun x => hu_nonneg x) hu_int).mp hu_integral_pos
  have hsupp_subset : Function.support u ⊆ {x : G | 0 < u x} := by
    intro x hx
    exact lt_of_le_of_ne (hu_nonneg x) hx.symm
  have hu_pos_set : 0 < μ {x : G | 0 < u x} :=
    lt_of_lt_of_le hsupp_pos (measure_mono hsupp_subset)
  exact continuousWeightedAvoidanceDensity_pos_of_level_one_proper_subgroup μ M
    f u hf_meas hu_meas hf_nonneg hf_le hu_nonneg hu_le H hH_closed
    hH_eq hH_proper hu_pos_set

/-- Route A endpoint with the usual compact-model lower bound
`α ≤ ∫ u`, `α > 0`. -/
theorem continuousWeightedAvoidanceDensity_pos_of_level_one_proper_subgroup_of_integral_ge
    {G : Type u} [AddCommGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G]
    [CompactSpace G] [T2Space G] [ConnectedSpace G]
    [MeasurableSpace G] [BorelSpace G] [MeasurableSub₂ G]
    [MeasurableAdd₂ G] [MeasurableNeg G]
    (μ : Measure G) [μ.IsAddHaarMeasure] [IsProbabilityMeasure μ]
    (M : ℕ)
    (f u : G → ℝ) (hf_meas : Measurable f) (hu_meas : Measurable u)
    (hf_nonneg : ∀ x, 0 ≤ f x)
    (hf_le : ∀ x, f x ≤ 1)
    (hu_nonneg : ∀ x, 0 ≤ u x)
    (hu_le : ∀ x, u x ≤ 1)
    (H : AddSubgroup G) (hH_closed : IsClosed (H : Set G))
    (hH_eq : ∀ x : G, x ∈ H ↔ f x = 1)
    (hH_proper : (H : Set G) ≠ Set.univ)
    {α : ℝ} (hα : 0 < α) (hmean_u : α ≤ ∫ x, u x ∂μ) :
    0 < continuousWeightedAvoidanceDensity μ M f u :=
  continuousWeightedAvoidanceDensity_pos_of_level_one_proper_subgroup_of_integral_pos μ M
    f u hf_meas hu_meas hf_nonneg hf_le hu_nonneg hu_le H hH_closed hH_eq hH_proper
    (lt_of_lt_of_le hα hmean_u)

/-- **Tao's continuous-analogue key lemma (May 2026 forum comment).** Let `G` be a
connected compact abelian Hausdorff group with Haar probability measure `μ`, and
let `f : G → ℝ` be measurable with `f ≤ 1` pointwise. Suppose the level set
`{x : f x = 1}` coincides with a closed subgroup `H ≤ G`, and `H` is proper.
Then for almost every `(x₁, …, x_M) ∈ G^M`, `f (x_i − x_j) < 1` for all
`1 ≤ i < j ≤ M`.

The hypothesis "level set is a closed subgroup" is what positive-definiteness of
`f` is used to establish in the original argument; we factor it out so the core
lemma is purely measure-theoretic. -/
theorem tao_continuous_avoidance
    {G : Type u} [AddCommGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G]
    [CompactSpace G] [T2Space G] [ConnectedSpace G]
    [MeasurableSpace G] [BorelSpace G] [MeasurableAdd₂ G] [MeasurableNeg G]
    (μ : Measure G) [μ.IsAddHaarMeasure] [IsProbabilityMeasure μ]
    (M : ℕ)
    (f : G → ℝ) (_hf_meas : Measurable f) (hf_le : ∀ x, f x ≤ 1)
    (H : AddSubgroup G) (hH_closed : IsClosed (H : Set G))
    (hH_eq : ∀ x : G, x ∈ H ↔ f x = 1)
    (hH_proper : (H : Set G) ≠ Set.univ) :
    ∀ᵐ (x : Fin M → G) ∂(Measure.pi (fun _ : Fin M => μ)),
      ∀ i j : Fin M, i < j → f (x i - x j) < 1 := by
  have hμH : μ (H : Set G) = 0 :=
    closed_proper_subgroup_haar_null μ H hH_closed hH_proper
  -- Fubini step (deferred): for each pair `(i, j)` with `i ≠ j`, the set of
  -- M-tuples with `x i - x j ∈ H` has product measure zero. Argument:
  -- translation invariance of `μ` plus `μ ↑H = 0` plus Fubini on the pi
  -- measure (or a measure-preserving "shear" change of variables).
  have h_pair_null :
      ∀ i j : Fin M, i ≠ j →
        Measure.pi (fun _ : Fin M => μ)
          {x : Fin M → G | x i - x j ∈ (H : Set G)} = 0 := by
    intro i j hij
    exact pi_pair_sub_mem_null μ H hH_closed hμH i j hij
  have h_bad_null :
      Measure.pi (fun _ : Fin M => μ)
        (⋃ (i : Fin M) (j : Fin M) (_ : i < j),
          {x : Fin M → G | x i - x j ∈ (H : Set G)}) = 0 := by
    refine measure_iUnion_null fun i => measure_iUnion_null fun j => ?_
    by_cases hij : i < j
    · simp only [hij, Set.iUnion_true]
      exact h_pair_null i j (ne_of_lt hij)
    · simp only [hij, Set.iUnion_of_empty, measure_empty]
  have h_ae_avoid : ∀ᵐ (x : Fin M → G) ∂(Measure.pi (fun _ : Fin M => μ)),
      ∀ i j : Fin M, i < j → x i - x j ∉ (H : Set G) := by
    rw [ae_iff]
    refine measure_mono_null ?_ h_bad_null
    intro x hx
    push Not at hx
    obtain ⟨i, j, hij, hmem⟩ := hx
    exact Set.mem_iUnion.mpr
      ⟨i, Set.mem_iUnion.mpr ⟨j, Set.mem_iUnion.mpr ⟨hij, hmem⟩⟩⟩
  filter_upwards [h_ae_avoid] with x hx i j hij
  have h_ne_one : f (x i - x j) ≠ 1 := by
    intro heq
    exact hx i j hij ((hH_eq (x i - x j)).mpr heq)
  exact lt_of_le_of_ne (hf_le _) h_ne_one

end Erdos42


/-! =============================================================
    Section from: Erdos/P42/CompactCayley/PositiveDefinite.lean
    ============================================================= -/

/-
Erdős Problem 42 — compact-Cayley route, positive-definite endpoint interface.

In compact-Cayley Lemma 2.7, the Fourier/positive-definite argument is used to
show that the level set `{x | g x = 1}` is a proper closed subgroup.  This file
formalizes the downstream subgroup construction and density conclusion from the
exact closure property that the positive-definite argument must supply.

No new axiom is introduced here: the remaining Route B work is to derive
`LevelOneSubgroupKernel g` from the compact limit's positive Fourier
coefficients.
-/


namespace Erdos42

open MeasureTheory

universe u

/-- Compact-Cayley Lemma 2.7, first branch. If `g 0 < 1`, then the allowed
kernel `1 - g` is positive at zero, hence has positive continuous clique
density by the open-neighbourhood endpoint. -/
theorem continuousCliqueDensity_pos_of_one_sub_of_lt_one_at_zero
    {G : Type u} [AddCommGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G]
    [MeasurableSpace G] [BorelSpace G] [MeasurableSub₂ G]
    (μ : Measure G) [IsProbabilityMeasure μ] [μ.IsOpenPosMeasure]
    (M : ℕ)
    (g : G → ℝ) (hg_cont : Continuous g)
    (hg_nonneg : ∀ x, 0 ≤ g x)
    (hg_le : ∀ x, g x ≤ 1)
    (hg0 : g 0 < 1) :
    0 < continuousCliqueDensity μ M (fun x => 1 - g x) := by
  refine continuousCliqueDensity_pos_of_pos_at_zero μ M (fun x => 1 - g x)
    (continuous_const.sub hg_cont) ?_ ?_ ?_
  · intro x
    linarith [hg_le x]
  · intro x
    linarith [hg_nonneg x]
  · linarith

/-- Abstract output of the positive-definite part of compact-Cayley Lemma 2.7:
the level-one set is nonempty and closed under subtraction.

For the eventual full proof, this structure should be produced from the
positive-definite kernel attached to `g`. -/
structure LevelOneSubgroupKernel {G : Type u} [Zero G] [Sub G]
    (g : G → ℝ) : Prop where
  map_zero : g 0 = 1
  sub_mem : ∀ x y : G, g x = 1 → g y = 1 → g (x - y) = 1

/-- A concrete Hilbert-space representation of a real positive-definite kernel:
`g (x - y)` is realized as an inner product of unit vectors.

This is not yet the compact extraction/GNS construction. It is the clean
finite-dimensional-style interface from which the level-one subgroup property
is elementary. -/
structure RealHilbertKernelRepresentation
    {G : Type u} (E : Type*) [AddCommGroup G]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (g : G → ℝ) where
  vec : G → E
  norm_vec : ∀ x : G, ‖vec x‖ = 1
  inner_sub : ∀ x y : G, inner ℝ (vec x) (vec y) = g (x - y)

lemma RealHilbertKernelRepresentation.vec_eq_zero_of_level_one
    {G : Type u} {E : Type*} [AddCommGroup G]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {g : G → ℝ} (hrep : RealHilbertKernelRepresentation E g)
    {x : G} (hx : g x = 1) :
    hrep.vec x = hrep.vec 0 := by
  let v : E := hrep.vec x
  let w : E := hrep.vec 0
  have hinner : inner ℝ v w = 1 := by
    calc
      inner ℝ v w = g (x - 0) := by simpa [v, w] using hrep.inner_sub x 0
      _ = g x := by simp
      _ = 1 := hx
  have hnormv : ‖v‖ = 1 := by simpa [v] using hrep.norm_vec x
  have hnormw : ‖w‖ = 1 := by simpa [w] using hrep.norm_vec 0
  have hsquare : ‖v - w‖ ^ 2 = 0 := by
    rw [norm_sub_sq_real, hinner, hnormv, hnormw]
    norm_num
  have hnorm : ‖v - w‖ = 0 := by
    have hnonneg : 0 ≤ ‖v - w‖ := norm_nonneg _
    nlinarith
  have hsub : v - w = 0 := norm_eq_zero.mp hnorm
  have hvw : v = w := sub_eq_zero.mp hsub
  simp [v, w, hvw]

theorem levelOneSubgroupKernel_of_realHilbertKernelRepresentation
    {G : Type u} {E : Type*} [AddCommGroup G]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {g : G → ℝ} (hrep : RealHilbertKernelRepresentation E g) :
    LevelOneSubgroupKernel g where
  map_zero := by
    calc
      g 0 = inner ℝ (hrep.vec 0) (hrep.vec 0) := by
        simpa using (hrep.inner_sub 0 0).symm
      _ = ‖hrep.vec 0‖ ^ 2 := real_inner_self_eq_norm_sq _
      _ = 1 := by rw [hrep.norm_vec 0]; norm_num
  sub_mem := by
    intro x y hx hy
    have hxvec : hrep.vec x = hrep.vec 0 :=
      hrep.vec_eq_zero_of_level_one hx
    have hyvec : hrep.vec y = hrep.vec 0 :=
      hrep.vec_eq_zero_of_level_one hy
    calc
      g (x - y) = inner ℝ (hrep.vec x) (hrep.vec y) :=
        (hrep.inner_sub x y).symm
      _ = inner ℝ (hrep.vec 0) (hrep.vec 0) := by rw [hxvec, hyvec]
      _ = ‖hrep.vec 0‖ ^ 2 := real_inner_self_eq_norm_sq _
      _ = 1 := by rw [hrep.norm_vec 0]; norm_num

/-- The subgroup `{x | g x = 1}` built from the level-one closure property. -/
def levelOneAddSubgroup {G : Type u} [AddCommGroup G]
    (g : G → ℝ) (hg : LevelOneSubgroupKernel g) : AddSubgroup G where
  carrier := {x | g x = 1}
  zero_mem' := hg.map_zero
  add_mem' := by
    intro x y hx hy
    have hneg_y : g (-y) = 1 := by
      simpa using hg.sub_mem 0 y hg.map_zero hy
    simpa [sub_eq_add_neg] using hg.sub_mem x (-y) hx hneg_y
  neg_mem' := by
    intro x hx
    simpa using hg.sub_mem 0 x hg.map_zero hx

lemma mem_levelOneAddSubgroup {G : Type u} [AddCommGroup G]
    {g : G → ℝ} {hg : LevelOneSubgroupKernel g} {x : G} :
    x ∈ levelOneAddSubgroup g hg ↔ g x = 1 := Iff.rfl

lemma levelOneAddSubgroup_isClosed {G : Type u}
    [AddCommGroup G] [TopologicalSpace G]
    {g : G → ℝ} (hg : LevelOneSubgroupKernel g)
    (hg_cont : Continuous g) :
    IsClosed (levelOneAddSubgroup g hg : Set G) := by
  change IsClosed (g ⁻¹' ({1} : Set ℝ))
  exact isClosed_singleton.preimage hg_cont

lemma levelOneAddSubgroup_proper_of_exists_ne_one {G : Type u}
    [AddCommGroup G] {g : G → ℝ} (hg : LevelOneSubgroupKernel g)
    (hne : ∃ x : G, g x ≠ 1) :
    (levelOneAddSubgroup g hg : Set G) ≠ Set.univ := by
  rcases hne with ⟨x, hx⟩
  intro htop
  have hxmem : x ∈ (levelOneAddSubgroup g hg : Set G) := by
    rw [htop]
    trivial
  exact hx (mem_levelOneAddSubgroup.mp hxmem)

lemma levelOneAddSubgroup_proper_of_integral_le_one_sub
    {G : Type u} [AddCommGroup G] [MeasurableSpace G]
    (μ : Measure G) [IsProbabilityMeasure μ]
    {g : G → ℝ} (hg : LevelOneSubgroupKernel g)
    {η : ℝ} (hη : 0 < η)
    (hmean : (∫ x, g x ∂μ) ≤ 1 - η) :
    (levelOneAddSubgroup g hg : Set G) ≠ Set.univ := by
  refine levelOneAddSubgroup_proper_of_exists_ne_one hg ?_
  by_contra hnone
  push Not at hnone
  have hint : (∫ x, g x ∂μ) = 1 := by
    simp [hnone]
  nlinarith

/-- Compact-Cayley Lemma 2.7 after isolating the positive-definite algebraic
input.  Once the positive-definite argument gives `LevelOneSubgroupKernel g`,
continuity gives closedness, the mean bound gives properness, and the
measure-theoretic endpoint yields positive `K_M` density for `1 - g`. -/
theorem continuousCliqueDensity_pos_of_levelOneSubgroupKernel
    {G : Type u} [AddCommGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G]
    [CompactSpace G] [T2Space G] [ConnectedSpace G]
    [MeasurableSpace G] [BorelSpace G] [MeasurableSub₂ G]
    [MeasurableAdd₂ G] [MeasurableNeg G]
    (μ : Measure G) [μ.IsAddHaarMeasure] [IsProbabilityMeasure μ]
    (M : ℕ)
    (g : G → ℝ) (hg_cont : Continuous g)
    (hg_nonneg : ∀ x, 0 ≤ g x)
    (hg_le : ∀ x, g x ≤ 1)
    (hg_level : LevelOneSubgroupKernel g)
    {η : ℝ} (hη : 0 < η)
    (hmean : (∫ x, g x ∂μ) ≤ 1 - η) :
    0 < continuousCliqueDensity μ M (fun x => 1 - g x) := by
  let H : AddSubgroup G := levelOneAddSubgroup g hg_level
  have hH_closed : IsClosed (H : Set G) :=
    levelOneAddSubgroup_isClosed hg_level hg_cont
  have hH_eq : ∀ x : G, x ∈ H ↔ g x = 1 := by
    intro x
    rfl
  have hH_proper : (H : Set G) ≠ Set.univ :=
    levelOneAddSubgroup_proper_of_integral_le_one_sub μ hg_level hη hmean
  exact continuousCliqueDensity_pos_of_one_sub_level_one_proper_subgroup
    μ M g hg_cont.measurable hg_nonneg hg_le H hH_closed hH_eq hH_proper

/-- Compact-Cayley endpoint with the exact null-subgroup hypothesis on the
level-one subgroup.  This avoids connectedness: once the positive-definite
argument gives subgroup closure and the compact-dual algebra gives nullness,
the measure-theoretic clique forcing is immediate. -/
theorem continuousCliqueDensity_pos_of_levelOneSubgroupKernel_null
    {G : Type u} [AddCommGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G]
    [MeasurableSpace G] [BorelSpace G] [MeasurableSub₂ G]
    [MeasurableAdd₂ G] [MeasurableNeg G]
    (μ : Measure G) [μ.IsAddHaarMeasure] [IsProbabilityMeasure μ]
    (M : ℕ)
    (g : G → ℝ) (hg_cont : Continuous g)
    (hg_nonneg : ∀ x, 0 ≤ g x)
    (hg_le : ∀ x, g x ≤ 1)
    (hg_level : LevelOneSubgroupKernel g)
    (hμH : μ ((levelOneAddSubgroup g hg_level : AddSubgroup G) : Set G) = 0) :
    0 < continuousCliqueDensity μ M (fun x => 1 - g x) := by
  let H : AddSubgroup G := levelOneAddSubgroup g hg_level
  have hH_closed : IsClosed (H : Set G) :=
    levelOneAddSubgroup_isClosed hg_level hg_cont
  have hH_eq : ∀ x : G, x ∈ H ↔ g x = 1 := by
    intro x
    rfl
  exact continuousCliqueDensity_pos_of_one_sub_level_one_null_subgroup
    μ M g hg_cont.measurable hg_nonneg hg_le H hH_closed hH_eq hμH

/-- Compact-Cayley endpoint where nullness of the level-one subgroup is proved
from infinite index.  This is often a smaller target for the extraction compact
dual than proving connectedness of the whole dual group. -/
theorem continuousCliqueDensity_pos_of_levelOneSubgroupKernel_not_finiteIndex
    {G : Type u} [AddCommGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G]
    [MeasurableSpace G] [BorelSpace G] [MeasurableSub₂ G]
    [MeasurableAdd₂ G] [MeasurableNeg G]
    (μ : Measure G) [μ.IsAddHaarMeasure] [IsProbabilityMeasure μ]
    (M : ℕ)
    (g : G → ℝ) (hg_cont : Continuous g)
    (hg_nonneg : ∀ x, 0 ≤ g x)
    (hg_le : ∀ x, g x ≤ 1)
    (hg_level : LevelOneSubgroupKernel g)
    (hH_not_finiteIndex :
      ¬ (levelOneAddSubgroup g hg_level : AddSubgroup G).FiniteIndex) :
    0 < continuousCliqueDensity μ M (fun x => 1 - g x) := by
  let H : AddSubgroup G := levelOneAddSubgroup g hg_level
  have hH_closed : IsClosed (H : Set G) :=
    levelOneAddSubgroup_isClosed hg_level hg_cont
  exact continuousCliqueDensity_pos_of_levelOneSubgroupKernel_null μ M g
    hg_cont hg_nonneg hg_le hg_level
    (closed_subgroup_haar_null_of_not_finiteIndex μ H hH_closed hH_not_finiteIndex)

/-- Route A weighted endpoint after isolating the positive-definite algebraic
input.  Once the limiting forbidden kernel `f` has level-one subgroup closure,
continuity gives closedness, the mean bound `∫ f ≤ 1 - ρ` gives properness, and
the weighted measure-theoretic endpoint gives a positive avoidance integral
against any vertex weight `u` with `α ≤ ∫ u`, `α > 0`. -/
theorem continuousWeightedAvoidanceDensity_pos_of_levelOneSubgroupKernel
    {G : Type u} [AddCommGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G]
    [CompactSpace G] [T2Space G] [ConnectedSpace G]
    [MeasurableSpace G] [BorelSpace G] [MeasurableSub₂ G]
    [MeasurableAdd₂ G] [MeasurableNeg G]
    (μ : Measure G) [μ.IsAddHaarMeasure] [IsProbabilityMeasure μ]
    (M : ℕ)
    (f u : G → ℝ) (hf_cont : Continuous f) (hu_meas : Measurable u)
    (hf_nonneg : ∀ x, 0 ≤ f x)
    (hf_le : ∀ x, f x ≤ 1)
    (hu_nonneg : ∀ x, 0 ≤ u x)
    (hu_le : ∀ x, u x ≤ 1)
    (hf_level : LevelOneSubgroupKernel f)
    {ρ : ℝ} (hρ : 0 < ρ)
    (hmean_f : (∫ x, f x ∂μ) ≤ 1 - ρ)
    {α : ℝ} (hα : 0 < α)
    (hmean_u : α ≤ ∫ x, u x ∂μ) :
    0 < continuousWeightedAvoidanceDensity μ M f u := by
  let H : AddSubgroup G := levelOneAddSubgroup f hf_level
  have hH_closed : IsClosed (H : Set G) :=
    levelOneAddSubgroup_isClosed hf_level hf_cont
  have hH_eq : ∀ x : G, x ∈ H ↔ f x = 1 := by
    intro x
    rfl
  have hH_proper : (H : Set G) ≠ Set.univ :=
    levelOneAddSubgroup_proper_of_integral_le_one_sub μ hf_level hρ hmean_f
  exact continuousWeightedAvoidanceDensity_pos_of_level_one_proper_subgroup_of_integral_ge
    μ M f u hf_cont.measurable hu_meas hf_nonneg hf_le hu_nonneg hu_le
    H hH_closed hH_eq hH_proper hα hmean_u

/-- Compact-Cayley Lemma 2.7 endpoint in the Hilbert-representation form:
once the positive-definite kernel is represented by unit vectors with
`g (x - y) = ⟪v x, v y⟫`, the level-one subgroup property and the continuous
clique-forcing conclusion are automatic. -/
theorem continuousCliqueDensity_pos_of_realHilbertKernelRepresentation
    {G : Type u} {E : Type*} [AddCommGroup G]
    [TopologicalSpace G] [IsTopologicalAddGroup G]
    [CompactSpace G] [T2Space G] [ConnectedSpace G]
    [MeasurableSpace G] [BorelSpace G] [MeasurableSub₂ G]
    [MeasurableAdd₂ G] [MeasurableNeg G]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (μ : Measure G) [μ.IsAddHaarMeasure] [IsProbabilityMeasure μ]
    (M : ℕ)
    (g : G → ℝ) (hg_cont : Continuous g)
    (hg_nonneg : ∀ x, 0 ≤ g x)
    (hg_le : ∀ x, g x ≤ 1)
    (hrep : RealHilbertKernelRepresentation E g)
    {η : ℝ} (hη : 0 < η)
    (hmean : (∫ x, g x ∂μ) ≤ 1 - η) :
    0 < continuousCliqueDensity μ M (fun x => 1 - g x) := by
  exact continuousCliqueDensity_pos_of_levelOneSubgroupKernel μ M g hg_cont hg_nonneg hg_le
    (levelOneSubgroupKernel_of_realHilbertKernelRepresentation hrep) hη hmean

/-- Compact-Cayley Lemma 2.7 endpoint with the two proof branches exposed:
either `g 0 < 1`, or the positive-definite argument supplies the level-one
subgroup closure property. -/
theorem continuousCliqueDensity_pos_of_lt_one_or_levelOneSubgroupKernel
    {G : Type u} [AddCommGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G]
    [CompactSpace G] [T2Space G] [ConnectedSpace G]
    [MeasurableSpace G] [BorelSpace G] [MeasurableSub₂ G]
    [MeasurableAdd₂ G] [MeasurableNeg G]
    (μ : Measure G) [μ.IsAddHaarMeasure] [IsProbabilityMeasure μ]
    (M : ℕ)
    (g : G → ℝ) (hg_cont : Continuous g)
    (hg_nonneg : ∀ x, 0 ≤ g x)
    (hg_le : ∀ x, g x ≤ 1)
    {η : ℝ} (hη : 0 < η)
    (hmean : (∫ x, g x ∂μ) ≤ 1 - η)
    (hbranch : g 0 < 1 ∨ LevelOneSubgroupKernel g) :
    0 < continuousCliqueDensity μ M (fun x => 1 - g x) := by
  rcases hbranch with hg0 | hg_level
  · exact continuousCliqueDensity_pos_of_one_sub_of_lt_one_at_zero μ M g hg_cont
      hg_nonneg hg_le hg0
  · exact continuousCliqueDensity_pos_of_levelOneSubgroupKernel μ M g hg_cont
      hg_nonneg hg_le hg_level hη hmean

/-- Two-branch compact-Cayley endpoint using the narrower infinite-index
certificate instead of connectedness. -/
theorem continuousCliqueDensity_pos_of_lt_one_or_levelOneSubgroupKernel_not_finiteIndex
    {G : Type u} [AddCommGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G]
    [MeasurableSpace G] [BorelSpace G] [MeasurableSub₂ G]
    [MeasurableAdd₂ G] [MeasurableNeg G]
    (μ : Measure G) [μ.IsAddHaarMeasure] [IsProbabilityMeasure μ]
    (M : ℕ)
    (g : G → ℝ) (hg_cont : Continuous g)
    (hg_nonneg : ∀ x, 0 ≤ g x)
    (hg_le : ∀ x, g x ≤ 1)
    (hbranch :
      g 0 < 1 ∨
        ∃ hg_level : LevelOneSubgroupKernel g,
          ¬ (levelOneAddSubgroup g hg_level : AddSubgroup G).FiniteIndex) :
    0 < continuousCliqueDensity μ M (fun x => 1 - g x) := by
  rcases hbranch with hg0 | hlevel
  · exact continuousCliqueDensity_pos_of_one_sub_of_lt_one_at_zero μ M g hg_cont
      hg_nonneg hg_le hg0
  · rcases hlevel with ⟨hg_level, hnot⟩
    exact continuousCliqueDensity_pos_of_levelOneSubgroupKernel_not_finiteIndex
      μ M g hg_cont hg_nonneg hg_le hg_level hnot

/-- Same two-branch endpoint, using a concrete Hilbert-space representation for
the second branch. The remaining Fourier/GNS work can target the `Nonempty`
representation hypothesis directly. -/
theorem continuousCliqueDensity_pos_of_lt_one_or_realHilbertKernelRepresentation
    {G : Type u} {E : Type*} [AddCommGroup G]
    [TopologicalSpace G] [IsTopologicalAddGroup G]
    [CompactSpace G] [T2Space G] [ConnectedSpace G]
    [MeasurableSpace G] [BorelSpace G] [MeasurableSub₂ G]
    [MeasurableAdd₂ G] [MeasurableNeg G]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (μ : Measure G) [μ.IsAddHaarMeasure] [IsProbabilityMeasure μ]
    (M : ℕ)
    (g : G → ℝ) (hg_cont : Continuous g)
    (hg_nonneg : ∀ x, 0 ≤ g x)
    (hg_le : ∀ x, g x ≤ 1)
    {η : ℝ} (hη : 0 < η)
    (hmean : (∫ x, g x ∂μ) ≤ 1 - η)
    (hbranch : g 0 < 1 ∨ Nonempty (RealHilbertKernelRepresentation E g)) :
    0 < continuousCliqueDensity μ M (fun x => 1 - g x) := by
  refine continuousCliqueDensity_pos_of_lt_one_or_levelOneSubgroupKernel μ M g hg_cont
    hg_nonneg hg_le hη hmean ?_
  exact hbranch.imp id fun hrep =>
    levelOneSubgroupKernel_of_realHilbertKernelRepresentation hrep.some

end Erdos42


/-! =============================================================
    Section from: Erdos/P42/CompactCayley/LimitKernel.lean
    ============================================================= -/

/-
Erdős Problem 42 — first compact-limit kernel coefficient layer.

This file defines the complement coefficients
`gCoeff 0 = 1 - a(0).re`, `gCoeff γ = -a(γ).re` for nonzero `γ`, where
`a` is the extracted Cayley Fourier coefficient limit.  The summability and
continuous Fourier-series construction are later steps.
-/


namespace Erdos42.CompactCayley

open Filter Erdos42 MeasureTheory
open scoped Topology

noncomputable section

namespace CayleyExtraction

variable {ℓ : ℕ} {η : ℝ} {S : CayleyCounterSeq ℓ η}

lemma coeff_norm_le_one (E : CayleyExtraction S) (γ : E.Group) :
    ‖E.coeff γ‖ ≤ 1 := by
  have hlim :=
    (continuous_norm.tendsto (E.coeff γ)).comp (E.coeff_tendsto γ)
  have hbound :
      ∀ᶠ n in atTop,
        ‖(letI : NeZero (S.p (E.φ n)) := ⟨(S.prime (E.φ n)).ne_zero⟩;
          normalizedDftCoeff (S.T (E.φ n)) (E.lift n γ))‖ ≤ 1 :=
    Filter.Eventually.of_forall (fun n => by
      letI : NeZero (S.p (E.φ n)) := ⟨(S.prime (E.φ n)).ne_zero⟩
      simpa [CayleyCounterSeq.toFourierSeq, FourierSeq.coeff,
        normalizedDftCoeff] using
        (S.toFourierSeq).norm_coeff_le_one (E.φ n) (E.lift n γ))
  exact le_of_tendsto_of_tendsto hlim tendsto_const_nhds hbound

lemma coeff_zero_re_le_one (E : CayleyExtraction S) :
    (E.coeff (0 : E.Group)).re ≤ 1 := by
  exact (Complex.re_le_norm (E.coeff (0 : E.Group))).trans
    (E.coeff_norm_le_one 0)

lemma coeff_zero_re_nonneg (E : CayleyExtraction S) :
    0 ≤ (E.coeff (0 : E.Group)).re := by
  have hlim :=
    Complex.continuous_re.tendsto (E.coeff (0 : E.Group)) |>.comp
      (E.coeff_tendsto (0 : E.Group))
  have hnonneg :
      ∀ᶠ n in atTop,
        0 ≤
          (letI : NeZero (S.p (E.φ n)) := ⟨(S.prime (E.φ n)).ne_zero⟩;
            (normalizedDftCoeff (S.T (E.φ n)) (E.lift n 0)).re) := by
    filter_upwards [E.data.finiteLift_zero_eventually_eq_zero] with n hn
    letI : NeZero (S.p (E.φ n)) := ⟨(S.prime (E.φ n)).ne_zero⟩
    have hp_pos : 0 < (S.p (E.φ n) : ℝ) := by
      exact_mod_cast Nat.pos_of_ne_zero (S.prime (E.φ n)).ne_zero
    have hcard_nonneg :
        0 ≤ ((S.T (E.φ n)).card : ℝ) / (S.p (E.φ n) : ℝ) := by
      positivity
    have hlift : E.lift n (0 : E.Group) = (0 : ZMod (S.p (E.φ n))) := by
      change E.data.finiteLift n (0 : E.data.Group) = 0
      exact hn
    have hcoeff_re :
        ((normalizedDftCoeff (S.T (E.φ n)) (E.lift n 0)).re) =
          ((S.T (E.φ n)).card : ℝ) / (S.p (E.φ n) : ℝ) := by
      rw [hlift]
      rw [normalizedDftCoeff_zero_eq_card_div]
      simp
    rw [hcoeff_re]
    exact hcard_nonneg
  exact le_of_tendsto_of_tendsto tendsto_const_nhds hlim hnonneg

/-- Complement Fourier coefficients for the compact limit kernel `g = 1 - f`. -/
noncomputable def gCoeff (E : CayleyExtraction S) (γ : E.Group) : ℝ :=
  if γ = 0 then 1 - (E.coeff (0 : E.Group)).re else -(E.coeff γ).re

lemma gCoeff_zero (E : CayleyExtraction S) :
    E.gCoeff 0 = 1 - (E.coeff (0 : E.Group)).re := by
  simp [gCoeff]

lemma gCoeff_of_ne_zero (E : CayleyExtraction S)
    {γ : E.Group} (hγ : γ ≠ 0) :
    E.gCoeff γ = -(E.coeff γ).re := by
  simp [gCoeff, hγ]

lemma gCoeff_nonneg (E : CayleyExtraction S) (γ : E.Group) :
    0 ≤ E.gCoeff γ := by
  by_cases hγ : γ = 0
  · subst hγ
    rw [E.gCoeff_zero]
    linarith [E.coeff_zero_re_le_one]
  · rw [E.gCoeff_of_ne_zero hγ]
    exact neg_nonneg.mpr (E.coeff_nonpos_of_ne_zero hγ)

lemma gCoeff_zero_le_one_sub_eta (E : CayleyExtraction S) :
    E.gCoeff 0 ≤ 1 - η := by
  rw [E.gCoeff_zero]
  linarith [E.coeff_zero_ge_eta]

lemma gCoeff_neg_eq (E : CayleyExtraction S) (γ : E.Group) :
    E.gCoeff (-γ) = E.gCoeff γ := by
  by_cases hγ : γ = 0
  · subst hγ
    simp
  · have hneg : -γ ≠ 0 := neg_ne_zero.mpr hγ
    rw [E.gCoeff_of_ne_zero hneg, E.gCoeff_of_ne_zero hγ, E.coeff_neg_eq γ]

lemma gCoeff_le_one (E : CayleyExtraction S) (γ : E.Group) :
    E.gCoeff γ ≤ 1 := by
  by_cases hγ : γ = 0
  · subst hγ
    rw [E.gCoeff_zero]
    linarith [E.coeff_zero_re_nonneg]
  · rw [E.gCoeff_of_ne_zero hγ]
    have hneg_re_le_norm : -(E.coeff γ).re ≤ ‖E.coeff γ‖ := by
      have h := (abs_le.mp (Complex.abs_re_le_norm (E.coeff γ))).1
      linarith
    exact hneg_re_le_norm.trans (E.coeff_norm_le_one γ)

lemma gCoeff_le_norm_coeff_of_ne_zero
    (E : CayleyExtraction S) {γ : E.Group} (hγ : γ ≠ 0) :
    E.gCoeff γ ≤ ‖E.coeff γ‖ := by
  rw [E.gCoeff_of_ne_zero hγ]
  have h := (abs_le.mp (Complex.abs_re_le_norm (E.coeff γ))).1
  linarith

lemma ne_zero_of_not_mem_largeSpectrumGenerators
    (E : CayleyExtraction S) (q : ℕ+) {γ : E.Group}
    (hγ : γ ∉ E.data.largeSpectrumGenerators q) :
    γ ≠ 0 := by
  intro hzero
  subst hzero
  exact hγ (E.data.zero_mem_largeSpectrumGenerators q)

lemma gCoeff_le_inv_of_not_mem_largeSpectrumGenerators
    (E : CayleyExtraction S) (q : ℕ+) {γ : E.Group}
    (hγ : γ ∉ E.data.largeSpectrumGenerators q) :
    E.gCoeff γ ≤ ((q : ℝ)⁻¹ : ℝ) := by
  exact (E.gCoeff_le_norm_coeff_of_ne_zero
      (E.ne_zero_of_not_mem_largeSpectrumGenerators q hγ)).trans
    (E.coeff_norm_le_inv_of_not_mem_largeSpectrumGenerators q hγ)

lemma sum_gCoeff_le_card_mul_inv_of_forall_not_mem_largeSpectrumGenerators
    (E : CayleyExtraction S) (q : ℕ+) (A : Finset E.Group)
    (hA : ∀ γ ∈ A, γ ∉ E.data.largeSpectrumGenerators q) :
    (∑ γ ∈ A, E.gCoeff γ) ≤
      (A.card : ℝ) * ((q : ℝ)⁻¹ : ℝ) := by
  calc
    (∑ γ ∈ A, E.gCoeff γ)
        ≤ ∑ γ ∈ A, ((q : ℝ)⁻¹ : ℝ) := by
          refine Finset.sum_le_sum ?_
          intro γ hγ
          exact E.gCoeff_le_inv_of_not_mem_largeSpectrumGenerators q (hA γ hγ)
    _ = (A.card : ℝ) * ((q : ℝ)⁻¹ : ℝ) := by
          simp [mul_comm]

lemma sum_gCoeff_sdiff_largeSpectrumGenerators_le_card_mul_inv
    (E : CayleyExtraction S) (q : ℕ+) (A : Finset E.Group) :
    (∑ γ ∈ A \ E.data.largeSpectrumGenerators q, E.gCoeff γ) ≤
      ((A \ E.data.largeSpectrumGenerators q).card : ℝ) *
        ((q : ℝ)⁻¹ : ℝ) :=
  E.sum_gCoeff_le_card_mul_inv_of_forall_not_mem_largeSpectrumGenerators q
    (A \ E.data.largeSpectrumGenerators q) (by
      intro γ hγ hmem
      exact (Finset.mem_sdiff.mp hγ).2 hmem)

lemma sum_gCoeff_largeSpectrumGenerators_le_card
    (E : CayleyExtraction S) (q : ℕ+) :
    (∑ γ ∈ E.data.largeSpectrumGenerators q, E.gCoeff γ) ≤
      (E.data.largeSpectrumGenerators q).card := by
  calc
    (∑ γ ∈ E.data.largeSpectrumGenerators q, E.gCoeff γ)
        ≤ ∑ γ ∈ E.data.largeSpectrumGenerators q, (1 : ℝ) := by
          refine Finset.sum_le_sum ?_
          intro γ _hγ
          exact E.gCoeff_le_one γ
    _ = (E.data.largeSpectrumGenerators q).card := by simp

lemma sum_gCoeff_largeSpectrumGenerators_le_quad
    (E : CayleyExtraction S) (q : ℕ+) :
    (∑ γ ∈ E.data.largeSpectrumGenerators q, E.gCoeff γ) ≤
      ((q : ℕ) ^ 2 + 2 : ℕ) := by
  exact (E.sum_gCoeff_largeSpectrumGenerators_le_card q).trans
    (by exact_mod_cast E.data.largeSpectrumGenerators_card_le q)

lemma one_sub_indicatorCoeffFunctional_fejer_re_le_one
    (E : CayleyExtraction S) (Q : Finset E.Group) (hQ : Q ≠ ∅) :
    (1 - TrigPoly.indicatorCoeffFunctional (E.fejerTrigPoly Q)).re ≤ 1 := by
  have htendsto :=
    E.finiteComplementFejerAverage_tendsto_one_sub_indicatorCoeffFunctional Q hQ
  have htendsto_re :=
    Complex.continuous_re.tendsto
      (1 - TrigPoly.indicatorCoeffFunctional (E.fejerTrigPoly Q)) |>.comp htendsto
  exact le_of_tendsto_of_tendsto htendsto_re tendsto_const_nhds
    (E.finiteComplementFejerAverage_re_le_one_eventually Q hQ)

lemma indicatorCoeffFunctional_fejer_re_nonneg
    (E : CayleyExtraction S) (Q : Finset E.Group) (hQ : Q ≠ ∅) :
    0 ≤ (TrigPoly.indicatorCoeffFunctional (E.fejerTrigPoly Q)).re := by
  have h := E.one_sub_indicatorCoeffFunctional_fejer_re_le_one Q hQ
  have h' :
      1 - (TrigPoly.indicatorCoeffFunctional (E.fejerTrigPoly Q)).re ≤ 1 := by
    simpa using h
  linarith

lemma one_sub_indicatorCoeffFunctional_fejer_re_eq_sum_gCoeff
    (E : CayleyExtraction S) (Q : Finset E.Group) (hQ : Q ≠ ∅) :
    (1 - TrigPoly.indicatorCoeffFunctional (E.fejerTrigPoly Q)).re =
      ∑ γ ∈ (E.fejerTrigPoly Q).support,
        ((E.fejerTrigPoly Q) γ).re * E.gCoeff γ := by
  classical
  let P : E.TrigPoly := E.fejerTrigPoly Q
  have hP0 : P (0 : E.Group) = 1 := by
    simpa [P, TrigPoly.compactAverage] using
      E.fejerTrigPoly_compactAverage_eq_one_of_nonempty Q hQ
  have h0mem : (0 : E.Group) ∈ P.support := by
    rw [Finsupp.mem_support_iff]
    rw [hP0]
    norm_num
  have hindicator_re :
      (TrigPoly.indicatorCoeffFunctional P).re =
        ∑ γ ∈ P.support, (P γ * E.coeff γ).re := by
    unfold TrigPoly.indicatorCoeffFunctional
    rw [Finsupp.sum]
    simp [Complex.re_sum]
  have hsum_if :
      (∑ γ ∈ P.support, if γ = (0 : E.Group) then (1 : ℝ) else 0) = 1 := by
    rw [Finset.sum_eq_single (0 : E.Group)]
    · simp
    · intro γ hγ hγ_ne
      simp [hγ_ne]
    · intro hnot
      exact False.elim (hnot h0mem)
  have hpoint :
      ∀ γ ∈ P.support,
        ((P γ).re * E.gCoeff γ) =
          (if γ = (0 : E.Group) then (1 : ℝ) else 0) -
            (P γ * E.coeff γ).re := by
    intro γ _hγ
    have hP_im : (P γ).im = 0 := by
      simpa [P] using E.fejerTrigPoly_apply_im_eq_zero Q γ
    have hcoeff_im : (E.coeff γ).im = 0 := E.coeff_im_eq_zero γ
    have hmul_re : (P γ * E.coeff γ).re = (P γ).re * (E.coeff γ).re := by
      rw [Complex.mul_re, hP_im, hcoeff_im]
      ring
    by_cases hγ0 : γ = 0
    · subst hγ0
      have hP0_re : (P (0 : E.Group)).re = 1 := by
        rw [hP0]
        simp
      rw [E.gCoeff_zero, hmul_re, hP0_re]
      simp
    · rw [E.gCoeff_of_ne_zero hγ0, hmul_re]
      simp [hγ0]
  calc
    (1 - TrigPoly.indicatorCoeffFunctional (E.fejerTrigPoly Q)).re
        = 1 - (TrigPoly.indicatorCoeffFunctional P).re := by
            simp [P]
    _ = (∑ γ ∈ P.support, if γ = (0 : E.Group) then (1 : ℝ) else 0) -
          ∑ γ ∈ P.support, (P γ * E.coeff γ).re := by
            rw [hsum_if, hindicator_re]
    _ = ∑ γ ∈ P.support,
          (((if γ = (0 : E.Group) then (1 : ℝ) else 0) -
            (P γ * E.coeff γ).re)) := by
            rw [Finset.sum_sub_distrib]
    _ = ∑ γ ∈ P.support, (P γ).re * E.gCoeff γ := by
            refine Finset.sum_congr rfl ?_
            intro γ hγ
            exact (hpoint γ hγ).symm
    _ = ∑ γ ∈ (E.fejerTrigPoly Q).support,
          ((E.fejerTrigPoly Q) γ).re * E.gCoeff γ := by
            simp [P]

lemma shiftedFejer_complementFunctional_re_eq_sum_gCoeff_mul_character_re
    (E : CayleyExtraction S) (Q : Finset E.Group) (z : E.CompactAddDual)
    (hQ : Q ≠ ∅) :
    (TrigPoly.compactAverage (E.shiftedFejerTrigPoly Q z) -
        TrigPoly.indicatorCoeffFunctional (E.shiftedFejerTrigPoly Q z)).re =
      ∑ γ ∈ (E.shiftedFejerTrigPoly Q z).support,
        ((E.fejerTrigPoly Q) γ).re * E.gCoeff γ *
          (E.addCharacterValue z γ).re := by
  classical
  let P : E.TrigPoly := E.shiftedFejerTrigPoly Q z
  let K : E.TrigPoly := E.fejerTrigPoly Q
  have hP0 : P (0 : E.Group) = 1 := by
    simpa [P, TrigPoly.compactAverage] using
      E.shiftedFejerTrigPoly_compactAverage_eq_one_of_nonempty Q z hQ
  have hK0 : K (0 : E.Group) = 1 := by
    simpa [K, TrigPoly.compactAverage] using
      E.fejerTrigPoly_compactAverage_eq_one_of_nonempty Q hQ
  have h0mem : (0 : E.Group) ∈ P.support := by
    rw [Finsupp.mem_support_iff]
    rw [hP0]
    norm_num
  have hindicator_re :
      (TrigPoly.indicatorCoeffFunctional P).re =
        ∑ γ ∈ P.support, (P γ * E.coeff γ).re := by
    unfold TrigPoly.indicatorCoeffFunctional
    rw [Finsupp.sum]
    simp [Complex.re_sum]
  have hsum_if :
      (∑ γ ∈ P.support, if γ = (0 : E.Group) then (1 : ℝ) else 0) = 1 := by
    rw [Finset.sum_eq_single (0 : E.Group)]
    · simp
    · intro γ hγ hγ_ne
      simp [hγ_ne]
    · intro hnot
      exact False.elim (hnot h0mem)
  have hpoint :
      ∀ γ ∈ P.support,
        ((K γ).re * E.gCoeff γ * (E.addCharacterValue z γ).re) =
          (if γ = (0 : E.Group) then (1 : ℝ) else 0) -
            (P γ * E.coeff γ).re := by
    intro γ _hγ
    have hP_apply :
        P γ = K γ * E.addCharacterValue z γ := by
      simpa [P, K] using E.shiftedFejerTrigPoly_apply Q z γ
    have hK_im : (K γ).im = 0 := by
      simpa [K] using E.fejerTrigPoly_apply_im_eq_zero Q γ
    have hcoeff_im : (E.coeff γ).im = 0 := E.coeff_im_eq_zero γ
    have hmul_re :
        (P γ * E.coeff γ).re =
          (K γ).re * (E.addCharacterValue z γ).re * (E.coeff γ).re := by
      rw [hP_apply]
      simp [Complex.mul_re, Complex.mul_im, hK_im, hcoeff_im,
        mul_left_comm, mul_comm]
    by_cases hγ0 : γ = 0
    · subst hγ0
      have hK0_re : (K (0 : E.Group)).re = 1 := by
        rw [hK0]
        simp
      rw [E.gCoeff_zero, hmul_re, hK0_re]
      simp
    · rw [E.gCoeff_of_ne_zero hγ0, hmul_re]
      simp [hγ0]
      ring
  calc
    (TrigPoly.compactAverage (E.shiftedFejerTrigPoly Q z) -
        TrigPoly.indicatorCoeffFunctional (E.shiftedFejerTrigPoly Q z)).re
        = 1 - (TrigPoly.indicatorCoeffFunctional P).re := by
            simp [P, E.shiftedFejerTrigPoly_compactAverage_eq_one_of_nonempty Q z hQ]
    _ = (∑ γ ∈ P.support, if γ = (0 : E.Group) then (1 : ℝ) else 0) -
          ∑ γ ∈ P.support, (P γ * E.coeff γ).re := by
            rw [hsum_if, hindicator_re]
    _ = ∑ γ ∈ P.support,
          (((if γ = (0 : E.Group) then (1 : ℝ) else 0) -
            (P γ * E.coeff γ).re)) := by
            rw [Finset.sum_sub_distrib]
    _ = ∑ γ ∈ P.support,
          (K γ).re * E.gCoeff γ * (E.addCharacterValue z γ).re := by
            refine Finset.sum_congr rfl ?_
            intro γ hγ
            exact (hpoint γ hγ).symm
    _ = ∑ γ ∈ (E.shiftedFejerTrigPoly Q z).support,
          ((E.fejerTrigPoly Q) γ).re * E.gCoeff γ *
            (E.addCharacterValue z γ).re := by
            simp [P, K]

lemma sum_gCoeff_le_of_fejerCoeffLowerBound
    (E : CayleyExtraction S) (Q B : Finset E.Group) (hQ : Q ≠ ∅)
    {M : ℝ} (hM_lt : M < 1)
    (hcoeff :
      ∀ γ ∈ B, 1 - M ≤ ((E.fejerTrigPoly Q) γ).re) :
    (1 - M) * (∑ γ ∈ B, E.gCoeff γ) ≤ 1 := by
  classical
  let P : E.TrigPoly := E.fejerTrigPoly Q
  have hpos : 0 < 1 - M := by linarith
  have hBsupport : B ⊆ P.support := by
    intro γ hγ
    have hre_pos : 0 < (P γ).re := by
      exact lt_of_lt_of_le hpos (by simpa [P] using hcoeff γ hγ)
    by_contra hnot
    have hzero : P γ = 0 := Finsupp.notMem_support_iff.mp hnot
    rw [hzero] at hre_pos
    norm_num at hre_pos
  calc
    (1 - M) * (∑ γ ∈ B, E.gCoeff γ)
        = ∑ γ ∈ B, (1 - M) * E.gCoeff γ := by
            rw [Finset.mul_sum]
    _ ≤ ∑ γ ∈ B, (P γ).re * E.gCoeff γ := by
            refine Finset.sum_le_sum ?_
            intro γ hγ
            exact mul_le_mul_of_nonneg_right
              (by simpa [P] using hcoeff γ hγ) (E.gCoeff_nonneg γ)
    _ ≤ ∑ γ ∈ P.support, (P γ).re * E.gCoeff γ := by
            exact Finset.sum_le_sum_of_subset_of_nonneg hBsupport (by
              intro γ _hγP _hγB
              exact mul_nonneg
                (by simpa [P] using E.fejerTrigPoly_apply_re_nonneg Q γ)
                (E.gCoeff_nonneg γ))
    _ = (1 - TrigPoly.indicatorCoeffFunctional (E.fejerTrigPoly Q)).re := by
            rw [E.one_sub_indicatorCoeffFunctional_fejer_re_eq_sum_gCoeff Q hQ]
    _ ≤ 1 := E.one_sub_indicatorCoeffFunctional_fejer_re_le_one Q hQ

lemma sum_gCoeff_le_of_fejerPairCoeffLowerBound
    (E : CayleyExtraction S) (Q B : Finset E.Group) (hQ : Q ≠ ∅)
    {M : ℝ} (hM_lt : M < 1)
    (hcoeff : E.FejerPairCoeffLowerBound Q B M) :
    (1 - M) * (∑ γ ∈ B, E.gCoeff γ) ≤ 1 :=
  E.sum_gCoeff_le_of_fejerCoeffLowerBound Q B hQ hM_lt (by
    intro γ hγ
    rw [E.fejerTrigPoly_apply_re_eq_pairRatio Q γ]
    exact hcoeff γ hγ)

lemma sum_gCoeff_le_one_of_forall_fejerPairCoeffLowerBound
    (E : CayleyExtraction S)
    (hfejer :
      ∀ (B : Finset E.Group) (M : ℝ), 0 < M →
        ∃ Q : Finset E.Group,
          Q ≠ ∅ ∧ E.FejerPairCoeffLowerBound Q B M)
    (B : Finset E.Group) :
    (∑ γ ∈ B, E.gCoeff γ) ≤ 1 := by
  classical
  by_contra hnot
  have hsum_gt : 1 < ∑ γ ∈ B, E.gCoeff γ := lt_of_not_ge hnot
  let A : ℝ := ∑ γ ∈ B, E.gCoeff γ
  let M : ℝ := (A - 1) / (2 * A)
  have hA_pos : 0 < A := by
    exact lt_trans zero_lt_one hsum_gt
  have hM_pos : 0 < M := by
    dsimp [M]
    have hnum : 0 < A - 1 := by
      simpa [A] using sub_pos.mpr hsum_gt
    have hden : 0 < 2 * A := by positivity
    exact div_pos hnum hden
  have hM_lt : M < 1 := by
    dsimp [M]
    have hA_ne : A ≠ 0 := ne_of_gt hA_pos
    field_simp [hA_ne]
    nlinarith [hA_pos]
  obtain ⟨Q, hQ, hlower⟩ := hfejer B M hM_pos
  have hbound :
      (1 - M) * (∑ γ ∈ B, E.gCoeff γ) ≤ 1 :=
    E.sum_gCoeff_le_of_fejerPairCoeffLowerBound Q B hQ hM_lt hlower
  have hprod_gt : 1 < (1 - M) * (∑ γ ∈ B, E.gCoeff γ) := by
    have hcalc : (1 - M) * A = (A + 1) / 2 := by
      dsimp [M]
      have hA_ne : A ≠ 0 := ne_of_gt hA_pos
      field_simp [hA_ne]
      ring
    have hA_gt : 1 < A := by simpa [A] using hsum_gt
    change 1 < (1 - M) * A
    rw [hcalc]
    nlinarith
  exact not_le_of_gt hprod_gt hbound

lemma summable_gCoeff_of_forall_fejerPairCoeffLowerBound
    (E : CayleyExtraction S)
    (hfejer :
      ∀ (B : Finset E.Group) (M : ℝ), 0 < M →
        ∃ Q : Finset E.Group,
          Q ≠ ∅ ∧ E.FejerPairCoeffLowerBound Q B M) :
    Summable E.gCoeff :=
  summable_of_sum_le (fun γ => E.gCoeff_nonneg γ)
    (fun B => E.sum_gCoeff_le_one_of_forall_fejerPairCoeffLowerBound hfejer B)

lemma tsum_gCoeff_le_one_of_forall_fejerPairCoeffLowerBound
    (E : CayleyExtraction S)
    (hfejer :
      ∀ (B : Finset E.Group) (M : ℝ), 0 < M →
        ∃ Q : Finset E.Group,
          Q ≠ ∅ ∧ E.FejerPairCoeffLowerBound Q B M) :
    (∑' γ : E.Group, E.gCoeff γ) ≤ 1 := by
  have hsum : Summable E.gCoeff :=
    E.summable_gCoeff_of_forall_fejerPairCoeffLowerBound hfejer
  exact le_of_tendsto_of_tendsto hsum.hasSum tendsto_const_nhds
    (Filter.Eventually.of_forall
      (fun B => E.sum_gCoeff_le_one_of_forall_fejerPairCoeffLowerBound hfejer B))

lemma summable_gCoeff (E : CayleyExtraction S) :
    Summable E.gCoeff :=
  E.summable_gCoeff_of_forall_fejerPairCoeffLowerBound
    (fun B _ hM => E.exists_fejerPairCoeffLowerBound B hM)

lemma tsum_gCoeff_le_one (E : CayleyExtraction S) :
    (∑' γ : E.Group, E.gCoeff γ) ≤ 1 :=
  E.tsum_gCoeff_le_one_of_forall_fejerPairCoeffLowerBound
    (fun B _ hM => E.exists_fejerPairCoeffLowerBound B hM)

/-- Complex Fourier-series term for the complement kernel. -/
noncomputable def gComplexTerm
    (E : CayleyExtraction S) (γ : E.Group) (z : E.CompactAddDual) : ℂ :=
  (E.gCoeff γ : ℂ) * E.addCharacterValue z γ

/-- Complex Fourier series for the compact complement kernel.  The definition
is meaningful without proving summability, but all analytic use below is under
an explicit `Summable E.gCoeff` hypothesis. -/
noncomputable def gComplex
    (E : CayleyExtraction S) (z : E.CompactAddDual) : ℂ :=
  ∑' γ : E.Group, E.gComplexTerm γ z

/-- Real-valued compact complement kernel, obtained as the real part of the
complex Fourier series. -/
noncomputable def gReal
    (E : CayleyExtraction S) (z : E.CompactAddDual) : ℝ :=
  (E.gComplex z).re

/-- Allowed compact kernel `f = 1 - g`. -/
noncomputable def fReal
    (E : CayleyExtraction S) (z : E.CompactAddDual) : ℝ :=
  1 - E.gReal z

lemma norm_gComplexTerm_le_gCoeff
    (E : CayleyExtraction S) (γ : E.Group) (z : E.CompactAddDual) :
    ‖E.gComplexTerm γ z‖ ≤ E.gCoeff γ := by
  rw [gComplexTerm, norm_mul, E.norm_addCharacterValue]
  simp [Real.norm_eq_abs, abs_of_nonneg (E.gCoeff_nonneg γ)]

lemma norm_gComplexTerm_eq_gCoeff
    (E : CayleyExtraction S) (γ : E.Group) (z : E.CompactAddDual) :
    ‖E.gComplexTerm γ z‖ = E.gCoeff γ := by
  rw [gComplexTerm, norm_mul, E.norm_addCharacterValue]
  simp [Real.norm_eq_abs, abs_of_nonneg (E.gCoeff_nonneg γ)]

lemma gComplexTerm_continuous
    (E : CayleyExtraction S) (γ : E.Group) :
    Continuous (fun z : E.CompactAddDual => E.gComplexTerm γ z) := by
  exact continuous_const.mul (E.addCharacterValue_continuous γ)

lemma star_gComplexTerm
    (E : CayleyExtraction S) (γ : E.Group) (z : E.CompactAddDual) :
    star (E.gComplexTerm γ z) = E.gComplexTerm (-γ) z := by
  unfold gComplexTerm
  simp [E.star_addCharacterValue, E.gCoeff_neg_eq γ, mul_comm]

lemma gComplexTerm_integrable
    (E : CayleyExtraction S) (γ : E.Group) :
    Integrable (fun z : E.CompactAddDual => E.gComplexTerm γ z) E.haar :=
  (E.gComplexTerm_continuous γ).integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)

lemma integral_norm_gComplexTerm
    (E : CayleyExtraction S) (γ : E.Group) :
    ∫ z : E.CompactAddDual, ‖E.gComplexTerm γ z‖ ∂E.haar =
      E.gCoeff γ := by
  simp [E.norm_gComplexTerm_eq_gCoeff γ]

lemma integral_gComplexTerm
    (E : CayleyExtraction S) (γ : E.Group) :
    ∫ z : E.CompactAddDual, E.gComplexTerm γ z ∂E.haar =
      if γ = 0 then (E.gCoeff γ : ℂ) else 0 := by
  unfold gComplexTerm
  rw [show
      (∫ z : E.CompactAddDual, (E.gCoeff γ : ℂ) * E.addCharacterValue z γ ∂E.haar) =
        (E.gCoeff γ : ℂ) * ∫ z : E.CompactAddDual, E.addCharacterValue z γ ∂E.haar by
    simpa using
      (integral_const_mul (μ := E.haar) (E.gCoeff γ : ℂ)
        (fun z : E.CompactAddDual => E.addCharacterValue z γ))]
  rw [E.integral_addCharacterValue]
  by_cases hγ : γ = 0 <;> simp [hγ]

lemma gComplex_continuous
    (E : CayleyExtraction S) (hsum : Summable E.gCoeff) :
    Continuous E.gComplex := by
  unfold gComplex
  exact continuous_tsum
    (fun γ => E.gComplexTerm_continuous γ)
    hsum
    (fun γ z => E.norm_gComplexTerm_le_gCoeff γ z)

lemma gReal_continuous
    (E : CayleyExtraction S) (hsum : Summable E.gCoeff) :
    Continuous E.gReal :=
  Complex.continuous_re.comp (E.gComplex_continuous hsum)

lemma fReal_continuous
    (E : CayleyExtraction S) (hsum : Summable E.gCoeff) :
    Continuous E.fReal :=
  continuous_const.sub (E.gReal_continuous hsum)

lemma star_gComplex
    (E : CayleyExtraction S) (z : E.CompactAddDual) :
    star (E.gComplex z) = E.gComplex z := by
  unfold gComplex
  calc
    star (∑' γ : E.Group, E.gComplexTerm γ z)
        = ∑' γ : E.Group, star (E.gComplexTerm γ z) := by
          simpa using
            (Complex.conj_tsum (fun γ : E.Group => E.gComplexTerm γ z))
    _ = ∑' γ : E.Group, E.gComplexTerm (-γ) z := by
          exact tsum_congr fun γ => E.star_gComplexTerm γ z
    _ = ∑' γ : E.Group, E.gComplexTerm γ z := by
          exact (Equiv.neg E.Group).tsum_eq (fun γ : E.Group =>
            E.gComplexTerm γ z)

lemma gComplex_im_eq_zero
    (E : CayleyExtraction S) (z : E.CompactAddDual) :
    (E.gComplex z).im = 0 :=
  Complex.conj_eq_iff_im.mp (E.star_gComplex z)

lemma gComplex_zero_eq_tsum_gCoeff
    (E : CayleyExtraction S) :
    E.gComplex (0 : E.CompactAddDual) =
      ((∑' γ : E.Group, E.gCoeff γ) : ℂ) := by
  unfold gComplex gComplexTerm
  simp

lemma gReal_zero_eq_tsum_gCoeff
    (E : CayleyExtraction S) :
    E.gReal (0 : E.CompactAddDual) =
      ∑' γ : E.Group, E.gCoeff γ := by
  unfold gReal
  rw [E.gComplex_zero_eq_tsum_gCoeff]
  rw [← Complex.ofReal_tsum (fun γ : E.Group => E.gCoeff γ)]
  simp

lemma gComplex_integrable
    (E : CayleyExtraction S) (hsum : Summable E.gCoeff) :
    Integrable E.gComplex E.haar :=
  (E.gComplex_continuous hsum).integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)

lemma gReal_integrable
    (E : CayleyExtraction S) (hsum : Summable E.gCoeff) :
    Integrable E.gReal E.haar :=
  (E.gComplex_integrable hsum).re

lemma fReal_integrable
    (E : CayleyExtraction S) (hsum : Summable E.gCoeff) :
    Integrable E.fReal E.haar :=
  (integrable_const (1 : ℝ)).sub (E.gReal_integrable hsum)

lemma integral_gComplex
    (E : CayleyExtraction S) (hsum : Summable E.gCoeff) :
    ∫ z : E.CompactAddDual, E.gComplex z ∂E.haar =
      (E.gCoeff 0 : ℂ) := by
  have hterm_int :
      ∀ γ : E.Group,
        Integrable (fun z : E.CompactAddDual => E.gComplexTerm γ z) E.haar :=
    fun γ => E.gComplexTerm_integrable γ
  have hnorm_sum :
      Summable
        (fun γ : E.Group =>
          ∫ z : E.CompactAddDual, ‖E.gComplexTerm γ z‖ ∂E.haar) := by
    simpa [E.integral_norm_gComplexTerm] using hsum
  unfold gComplex
  rw [← integral_tsum_of_summable_integral_norm hterm_int hnorm_sum]
  calc
    (∑' γ : E.Group,
        ∫ z : E.CompactAddDual, E.gComplexTerm γ z ∂E.haar)
        =
      ∑' γ : E.Group, if γ = 0 then (E.gCoeff γ : ℂ) else 0 := by
        exact tsum_congr fun γ => E.integral_gComplexTerm γ
    _ = (E.gCoeff 0 : ℂ) := by
        rw [tsum_eq_single (0 : E.Group)]
        · simp
        · intro γ hγ
          simp [hγ]

lemma integral_gReal
    (E : CayleyExtraction S) (hsum : Summable E.gCoeff) :
    ∫ z : E.CompactAddDual, E.gReal z ∂E.haar =
      E.gCoeff 0 := by
  unfold gReal
  have hre :=
    integral_re (μ := E.haar) (f := E.gComplex)
      (E.gComplex_integrable hsum)
  calc
    ∫ z : E.CompactAddDual, (E.gComplex z).re ∂E.haar =
        RCLike.re (∫ z : E.CompactAddDual, E.gComplex z ∂E.haar) := by
      simpa using hre
    _ = E.gCoeff 0 := by
      rw [E.integral_gComplex hsum]
      simp

lemma integral_fReal_eq_coeff_zero_re
    (E : CayleyExtraction S) (hsum : Summable E.gCoeff) :
    ∫ z : E.CompactAddDual, E.fReal z ∂E.haar =
      (E.coeff (0 : E.Group)).re := by
  unfold fReal
  rw [integral_sub (integrable_const (1 : ℝ)) (E.gReal_integrable hsum)]
  rw [E.integral_gReal hsum, E.gCoeff_zero]
  simp

lemma integral_fReal_ge_eta
    (E : CayleyExtraction S) (hsum : Summable E.gCoeff) :
    η ≤ ∫ z : E.CompactAddDual, E.fReal z ∂E.haar := by
  rw [E.integral_fReal_eq_coeff_zero_re hsum]
  exact E.coeff_zero_ge_eta

lemma integral_gReal_le_one_sub_eta
    (E : CayleyExtraction S) (hsum : Summable E.gCoeff) :
    ∫ z : E.CompactAddDual, E.gReal z ∂E.haar ≤ 1 - η := by
  rw [E.integral_gReal hsum]
  exact E.gCoeff_zero_le_one_sub_eta

lemma addCharacterValue_re_le_one
    (E : CayleyExtraction S) (z : E.CompactAddDual) (γ : E.Group) :
    (E.addCharacterValue z γ).re ≤ 1 := by
  exact (Complex.re_le_norm (E.addCharacterValue z γ)).trans
    (by simp)

lemma neg_one_le_addCharacterValue_re
    (E : CayleyExtraction S) (z : E.CompactAddDual) (γ : E.Group) :
    -1 ≤ (E.addCharacterValue z γ).re := by
  have h_abs :
      |(E.addCharacterValue z γ).re| ≤ (1 : ℝ) := by
    simpa [E.norm_addCharacterValue z γ] using
      Complex.abs_re_le_norm (E.addCharacterValue z γ)
  exact (abs_le.mp h_abs).1

lemma shiftedFejer_weighted_gCoeff_character_sum_nonneg
    (E : CayleyExtraction S) (Q : Finset E.Group) (z : E.CompactAddDual)
    (hQ : Q ≠ ∅) :
    0 ≤
      ∑ γ ∈ (E.shiftedFejerTrigPoly Q z).support,
        ((E.fejerTrigPoly Q) γ).re * E.gCoeff γ *
          (E.addCharacterValue z γ).re := by
  have h := E.shiftedFejer_complementFunctional_re_nonneg Q z
  rwa [E.shiftedFejer_complementFunctional_re_eq_sum_gCoeff_mul_character_re
    Q z hQ] at h

lemma sum_gCoeff_mul_character_re_ge_neg_of_fejerPairCoeffLowerBound
    (E : CayleyExtraction S) (Q B : Finset E.Group) (z : E.CompactAddDual)
    {M : ℝ} (hQ : Q ≠ ∅) (hM_lt : M < 1)
    (hlower : E.FejerPairCoeffLowerBound Q B M) :
    - (∑ γ ∈ (E.shiftedFejerTrigPoly Q z).support \ B, E.gCoeff γ) -
        M * (∑ γ ∈ B, E.gCoeff γ) ≤
      ∑ γ ∈ B, E.gCoeff γ * (E.addCharacterValue z γ).re := by
  classical
  let P : E.TrigPoly := E.shiftedFejerTrigPoly Q z
  let K : E.TrigPoly := E.fejerTrigPoly Q
  let a : E.Group → ℝ :=
    fun γ => E.gCoeff γ * (E.addCharacterValue z γ).re
  let w : E.Group → ℝ := fun γ => (K γ).re
  have hBsupport : B ⊆ P.support := by
    intro γ hγ
    have hratio :
        1 - M ≤ ((pairFiber Q γ).card : ℝ) / (Q.card : ℝ) :=
      hlower γ hγ
    have hw_pos : 0 < w γ := by
      have hpos : 0 < 1 - M := by linarith
      exact lt_of_lt_of_le hpos (by
        simpa [w, K, E.fejerTrigPoly_apply_re_eq_pairRatio Q γ] using hratio)
    have hK_ne : K γ ≠ 0 := by
      intro hzero
      have : w γ = 0 := by simp [w, hzero]
      linarith
    have hchar_ne : E.addCharacterValue z γ ≠ 0 := by
      intro hzero
      have hnorm := E.norm_addCharacterValue z γ
      rw [hzero] at hnorm
      norm_num at hnorm
    rw [Finsupp.mem_support_iff]
    rw [show P γ = K γ * E.addCharacterValue z γ by
      simpa [P, K] using E.shiftedFejerTrigPoly_apply Q z γ]
    exact mul_ne_zero hK_ne hchar_ne
  have hweighted :
      0 ≤ ∑ γ ∈ P.support, w γ * a γ := by
    simpa [P, K, w, a, mul_assoc] using
      E.shiftedFejer_weighted_gCoeff_character_sum_nonneg Q z hQ
  have hsplit :
      ∑ γ ∈ P.support, w γ * a γ =
        (∑ γ ∈ P.support \ B, w γ * a γ) +
          ∑ γ ∈ B, w γ * a γ := by
    exact (Finset.sum_sdiff hBsupport).symm
  have htail_le :
      (∑ γ ∈ P.support \ B, w γ * a γ) ≤
        ∑ γ ∈ P.support \ B, E.gCoeff γ := by
    refine Finset.sum_le_sum ?_
    intro γ _hγ
    have hw_nonneg : 0 ≤ w γ := by
      simpa [w, K] using E.fejerTrigPoly_apply_re_nonneg Q γ
    have hw_le_one : w γ ≤ 1 := by
      simpa [w, K] using E.fejerTrigPoly_apply_re_le_one Q γ
    have ha_le : a γ ≤ E.gCoeff γ := by
      dsimp [a]
      simpa using
        mul_le_mul_of_nonneg_left
          (E.addCharacterValue_re_le_one z γ) (E.gCoeff_nonneg γ)
    have hwg_le : w γ * E.gCoeff γ ≤ E.gCoeff γ := by
      nlinarith [hw_nonneg, hw_le_one, E.gCoeff_nonneg γ]
    exact (mul_le_mul_of_nonneg_left ha_le hw_nonneg).trans hwg_le
  have hB_le :
      (∑ γ ∈ B, w γ * a γ) -
          M * (∑ γ ∈ B, E.gCoeff γ) ≤
        ∑ γ ∈ B, a γ := by
    calc
      (∑ γ ∈ B, w γ * a γ) -
          M * (∑ γ ∈ B, E.gCoeff γ)
          = ∑ γ ∈ B, (w γ * a γ - M * E.gCoeff γ) := by
              rw [Finset.sum_sub_distrib, Finset.mul_sum]
      _ ≤ ∑ γ ∈ B, a γ := by
          refine Finset.sum_le_sum ?_
          intro γ hγ
          have hratio :
              1 - M ≤ ((pairFiber Q γ).card : ℝ) / (Q.card : ℝ) :=
            hlower γ hγ
          have hw_lower : 1 - M ≤ w γ := by
            simpa [w, K, E.fejerTrigPoly_apply_re_eq_pairRatio Q γ] using
              hratio
          have hw_le_one : w γ ≤ 1 := by
            simpa [w, K] using E.fejerTrigPoly_apply_re_le_one Q γ
          have hone_minus_nonneg : 0 ≤ 1 - w γ := by linarith
          have hone_minus_le : 1 - w γ ≤ M := by linarith
          have ha_ge_neg : -E.gCoeff γ ≤ a γ := by
            dsimp [a]
            have hg : 0 ≤ E.gCoeff γ := E.gCoeff_nonneg γ
            have hre := E.neg_one_le_addCharacterValue_re z γ
            calc
              -E.gCoeff γ = E.gCoeff γ * (-1) := by ring
              _ ≤ E.gCoeff γ * (E.addCharacterValue z γ).re :=
                  mul_le_mul_of_nonneg_left hre hg
          have herror :
              -M * E.gCoeff γ ≤ (1 - w γ) * a γ := by
            have hleft :
                -(1 - w γ) * E.gCoeff γ ≤ (1 - w γ) * a γ := by
              calc
                -(1 - w γ) * E.gCoeff γ
                    = (1 - w γ) * (-E.gCoeff γ) := by ring
                _ ≤ (1 - w γ) * a γ :=
                    mul_le_mul_of_nonneg_left ha_ge_neg hone_minus_nonneg
            have hright :
                -M * E.gCoeff γ ≤ -(1 - w γ) * E.gCoeff γ := by
              have hmul :
                  (1 - w γ) * E.gCoeff γ ≤ M * E.gCoeff γ :=
                mul_le_mul_of_nonneg_right hone_minus_le
                  (E.gCoeff_nonneg γ)
              linarith
            exact hright.trans hleft
          nlinarith
  have hB_lower :
      - (∑ γ ∈ P.support \ B, E.gCoeff γ) ≤
        ∑ γ ∈ B, w γ * a γ := by
    have hweighted_split :
        0 ≤ (∑ γ ∈ P.support \ B, w γ * a γ) +
              ∑ γ ∈ B, w γ * a γ := by
      simpa [hsplit] using hweighted
    linarith
  have hmain :
      - (∑ γ ∈ P.support \ B, E.gCoeff γ) -
          M * (∑ γ ∈ B, E.gCoeff γ) ≤
        (∑ γ ∈ B, w γ * a γ) -
          M * (∑ γ ∈ B, E.gCoeff γ) := by
    linarith
  exact hmain.trans (by simpa [a] using hB_le)

lemma addCharacterValue_eq_one_of_re_eq_one
    (E : CayleyExtraction S) (z : E.CompactAddDual) (γ : E.Group)
    (hre : (E.addCharacterValue z γ).re = 1) :
    E.addCharacterValue z γ = 1 := by
  have hnormSq : Complex.normSq (E.addCharacterValue z γ) = 1 := by
    rw [Complex.normSq_eq_norm_sq, E.norm_addCharacterValue]
    norm_num
  have him : (E.addCharacterValue z γ).im = 0 := by
    rw [Complex.normSq_apply, hre] at hnormSq
    nlinarith [sq_nonneg (E.addCharacterValue z γ).im]
  apply Complex.ext
  · simp [hre]
  · simp [him]

lemma summable_gCoeff_mul_character_re
    (E : CayleyExtraction S) (hsum : Summable E.gCoeff)
    (z : E.CompactAddDual) :
    Summable fun γ : E.Group =>
      E.gCoeff γ * (E.addCharacterValue z γ).re := by
  refine hsum.of_norm_bounded ?_
  intro γ
  have hcoeff_nonneg : 0 ≤ E.gCoeff γ := E.gCoeff_nonneg γ
  have hre_abs : |(E.addCharacterValue z γ).re| ≤ 1 := by
    exact (Complex.abs_re_le_norm (E.addCharacterValue z γ)).trans
      (by simp)
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hcoeff_nonneg]
  nlinarith [mul_le_mul_of_nonneg_left hre_abs hcoeff_nonneg]

lemma gReal_eq_tsum_gCoeff_mul_character_re
    (E : CayleyExtraction S) (hsum : Summable E.gCoeff)
    (z : E.CompactAddDual) :
    E.gReal z =
      ∑' γ : E.Group, E.gCoeff γ * (E.addCharacterValue z γ).re := by
  have hterm : Summable fun γ : E.Group => E.gComplexTerm γ z :=
    hsum.of_norm_bounded (fun γ => E.norm_gComplexTerm_le_gCoeff γ z)
  unfold gReal gComplex
  rw [Complex.re_tsum hterm]
  refine tsum_congr ?_
  intro γ
  simp [gComplexTerm, Complex.mul_re]

lemma fReal_eq_coeff_zero_sub_tsum_nonzero_gCoeff
    (E : CayleyExtraction S) (z : E.CompactAddDual) :
    E.fReal z =
      (E.coeff (0 : E.Group)).re -
        ∑' γ : E.Group,
          if γ = 0 then 0 else E.gCoeff γ * (E.addCharacterValue z γ).re := by
  let a : E.Group → ℝ :=
    fun γ => E.gCoeff γ * (E.addCharacterValue z γ).re
  have hsumA : Summable a := by
    simpa [a] using E.summable_gCoeff_mul_character_re E.summable_gCoeff z
  have hsplit := hsumA.tsum_eq_add_tsum_ite (0 : E.Group)
  have hzero : a 0 = E.gCoeff 0 := by
    simp [a]
  unfold fReal
  rw [E.gReal_eq_tsum_gCoeff_mul_character_re E.summable_gCoeff z]
  change 1 - (∑' γ : E.Group, a γ) =
    (E.coeff (0 : E.Group)).re -
      ∑' γ : E.Group, if γ = 0 then 0 else a γ
  rw [hsplit, hzero, E.gCoeff_zero]
  ring

lemma compactSmoothReal_eq_coeff_zero_sub_sum_nonzero_gCoeff
    (E : CayleyExtraction S) (Q : Finset E.Group) (hQ : Q ≠ ∅)
    (z : E.CompactAddDual) (A : Finset E.Group)
    (hA0 : (0 : E.Group) ∈ A)
    (hAsupport : (E.compactSmoothTrigPoly Q).support ⊆ A) :
    E.compactSmoothReal Q z =
      (E.coeff (0 : E.Group)).re -
        ∑ γ ∈ A,
          if γ = 0 then 0
          else (E.fejerTrigPoly Q γ).re * E.gCoeff γ *
            (E.addCharacterValue z γ).re := by
  classical
  rw [E.compactSmoothReal_eq_sum_of_support_subset Q z A hAsupport]
  let t : E.Group → ℝ :=
    fun γ => (E.fejerTrigPoly Q γ).re * (E.coeff γ).re *
      (E.addCharacterValue z γ).re
  let b : E.Group → ℝ :=
    fun γ => if γ = 0 then 0
      else (E.fejerTrigPoly Q γ).re * E.gCoeff γ *
        (E.addCharacterValue z γ).re
  have ht0 : t 0 = (E.coeff (0 : E.Group)).re := by
    have hK0c : E.fejerTrigPoly Q (0 : E.Group) = 1 := by
      simpa [TrigPoly.compactAverage] using
        E.fejerTrigPoly_compactAverage_eq_one_of_nonempty Q hQ
    simp [t, hK0c]
  have ht_ne : ∀ γ ∈ A \ ({0} : Finset E.Group), t γ = -b γ := by
    intro γ hγ
    have hne : γ ≠ 0 := by
      intro hzero
      exact (Finset.mem_sdiff.mp hγ).2 (by simp [hzero])
    simp [t, b, hne, E.gCoeff_of_ne_zero hne, mul_assoc]
  have hsum_t :
      (∑ γ ∈ A, t γ) =
        (E.coeff (0 : E.Group)).re +
          ∑ γ ∈ A \ ({0} : Finset E.Group), -b γ := by
    rw [Finset.sum_eq_add_sum_sdiff_singleton_of_mem hA0, ht0]
    congr 1
    exact Finset.sum_congr rfl ht_ne
  have hsum_b :
      (∑ γ ∈ A, b γ) =
        ∑ γ ∈ A \ ({0} : Finset E.Group), b γ := by
    rw [Finset.sum_eq_add_sum_sdiff_singleton_of_mem hA0]
    simp [b]
  change (∑ γ ∈ A, t γ) =
    (E.coeff (0 : E.Group)).re - ∑ γ ∈ A, b γ
  rw [hsum_t, hsum_b]
  rw [Finset.sum_neg_distrib]
  ring

lemma abs_compactSmoothReal_sub_fReal_le_of_tsum_tail
    (E : CayleyExtraction S) (Q : Finset E.Group) (hQ : Q ≠ ∅)
    (z : E.CompactAddDual) (A : Finset E.Group)
    (hA0 : (0 : E.Group) ∈ A)
    (hAsupport : (E.compactSmoothTrigPoly Q).support ⊆ A)
    {M δ : ℝ} (hM_nonneg : 0 ≤ M)
    (hclose : ∀ γ ∈ A, ‖1 - E.fejerTrigPoly Q γ‖ ≤ M)
    (htail :
      |(∑ γ ∈ A,
          if γ = 0 then 0
          else E.gCoeff γ * (E.addCharacterValue z γ).re) -
        ∑' γ : E.Group,
          if γ = 0 then 0
          else E.gCoeff γ * (E.addCharacterValue z γ).re| ≤ δ) :
    |E.compactSmoothReal Q z - E.fReal z| ≤
      δ + M * ∑ γ ∈ A, E.gCoeff γ := by
  classical
  let a : E.Group → ℝ :=
    fun γ => if γ = 0 then 0
      else E.gCoeff γ * (E.addCharacterValue z γ).re
  let b : E.Group → ℝ :=
    fun γ => if γ = 0 then 0
      else (E.fejerTrigPoly Q γ).re * E.gCoeff γ *
        (E.addCharacterValue z γ).re
  have hcompact :
      E.compactSmoothReal Q z =
        (E.coeff (0 : E.Group)).re - ∑ γ ∈ A, b γ := by
    simpa [b] using
      E.compactSmoothReal_eq_coeff_zero_sub_sum_nonzero_gCoeff
        Q hQ z A hA0 hAsupport
  have hf :
      E.fReal z =
        (E.coeff (0 : E.Group)).re - ∑' γ : E.Group, a γ := by
    simpa [a] using E.fReal_eq_coeff_zero_sub_tsum_nonzero_gCoeff z
  have htail' : |(∑ γ ∈ A, a γ) - ∑' γ : E.Group, a γ| ≤ δ := by
    simpa [a] using htail
  have hfinite :
      |(∑ γ ∈ A, a γ) - ∑ γ ∈ A, b γ| ≤
        M * ∑ γ ∈ A, E.gCoeff γ := by
    rw [← Finset.sum_sub_distrib]
    calc
      |∑ γ ∈ A, (a γ - b γ)|
          ≤ ∑ γ ∈ A, |a γ - b γ| := by
            exact Finset.abs_sum_le_sum_abs (fun γ => a γ - b γ) A
      _ ≤ ∑ γ ∈ A, M * E.gCoeff γ := by
            refine Finset.sum_le_sum ?_
            intro γ hγ
            by_cases hzero : γ = 0
            · simpa [a, b, hzero] using
                mul_nonneg hM_nonneg (E.gCoeff_nonneg γ)
            · have hK_abs : |1 - (E.fejerTrigPoly Q γ).re| ≤ M := by
                have hre :
                    |(1 - E.fejerTrigPoly Q γ).re| ≤
                      ‖1 - E.fejerTrigPoly Q γ‖ :=
                  Complex.abs_re_le_norm _
                have hnorm := hclose γ hγ
                have hrewrite :
                    (1 - E.fejerTrigPoly Q γ).re =
                      1 - (E.fejerTrigPoly Q γ).re := by simp
                simpa [hrewrite] using hre.trans hnorm
              have hchar_abs :
                  |(E.addCharacterValue z γ).re| ≤ 1 :=
                (Complex.abs_re_le_norm (E.addCharacterValue z γ)).trans
                  (by simp [E.norm_addCharacterValue z γ])
              have hg_nonneg : 0 ≤ E.gCoeff γ := E.gCoeff_nonneg γ
              have hdiff :
                  a γ - b γ =
                    (1 - (E.fejerTrigPoly Q γ).re) *
                      E.gCoeff γ * (E.addCharacterValue z γ).re := by
                simp [a, b, hzero, mul_assoc]
                ring
              calc
                |a γ - b γ|
                    = |(1 - (E.fejerTrigPoly Q γ).re) *
                        E.gCoeff γ * (E.addCharacterValue z γ).re| := by
                          rw [hdiff]
                _ = |1 - (E.fejerTrigPoly Q γ).re| *
                    E.gCoeff γ * |(E.addCharacterValue z γ).re| := by
                      rw [abs_mul, abs_mul, abs_of_nonneg hg_nonneg]
                _ ≤ M * E.gCoeff γ * 1 := by
                          exact mul_le_mul
                            (mul_le_mul hK_abs le_rfl hg_nonneg hM_nonneg)
                            hchar_abs
                            (abs_nonneg _)
                            (mul_nonneg hM_nonneg hg_nonneg)
                _ = M * E.gCoeff γ := by ring
      _ = M * ∑ γ ∈ A, E.gCoeff γ := by
            rw [Finset.mul_sum]
  rw [hcompact, hf]
  have hdecomp :
      ((E.coeff (0 : E.Group)).re - ∑ γ ∈ A, b γ) -
          ((E.coeff (0 : E.Group)).re - ∑' γ : E.Group, a γ) =
        ((∑' γ : E.Group, a γ) - ∑ γ ∈ A, a γ) +
          ((∑ γ ∈ A, a γ) - ∑ γ ∈ A, b γ) := by
    ring
  rw [hdecomp]
  calc
    |((∑' γ : E.Group, a γ) - ∑ γ ∈ A, a γ) +
        ((∑ γ ∈ A, a γ) - ∑ γ ∈ A, b γ)|
        ≤ |(∑' γ : E.Group, a γ) - ∑ γ ∈ A, a γ| +
          |(∑ γ ∈ A, a γ) - ∑ γ ∈ A, b γ| := abs_add_le _ _
    _ ≤ δ + M * ∑ γ ∈ A, E.gCoeff γ := by
      have htail_sym :
          |(∑' γ : E.Group, a γ) - ∑ γ ∈ A, a γ| ≤ δ := by
        simpa [abs_sub_comm] using htail'
      exact add_le_add htail_sym hfinite

lemma abs_sum_sub_tsum_nonzero_gCoeff_character_re_le_tsum_compl
    (E : CayleyExtraction S) (A : Finset E.Group)
    (z : E.CompactAddDual) :
    |(∑ γ ∈ A,
        if γ = 0 then 0
        else E.gCoeff γ * (E.addCharacterValue z γ).re) -
      ∑' γ : E.Group,
        if γ = 0 then 0
        else E.gCoeff γ * (E.addCharacterValue z γ).re| ≤
      ∑' γ : ↑((↑A : Set E.Group)ᶜ), E.gCoeff γ := by
  classical
  let a : E.Group → ℝ :=
    fun γ => if γ = 0 then 0
      else E.gCoeff γ * (E.addCharacterValue z γ).re
  have ha_bound : ∀ γ : E.Group, ‖a γ‖ ≤ E.gCoeff γ := by
    intro γ
    by_cases hzero : γ = 0
    · simpa [a, hzero] using E.gCoeff_nonneg γ
    · have hchar_abs : |(E.addCharacterValue z γ).re| ≤ 1 :=
        (Complex.abs_re_le_norm (E.addCharacterValue z γ)).trans
          (by simp [E.norm_addCharacterValue z γ])
      have hg_nonneg : 0 ≤ E.gCoeff γ := E.gCoeff_nonneg γ
      simpa [a, hzero, Real.norm_eq_abs, abs_mul,
        abs_of_nonneg hg_nonneg] using
        mul_le_of_le_one_right hg_nonneg hchar_abs
  have hsumA : Summable a := by
    exact E.summable_gCoeff.of_norm_bounded ha_bound
  have hsplit := hsumA.sum_add_tsum_compl (s := A)
  have htail_eq :
      (∑ γ ∈ A, a γ) - ∑' γ : E.Group, a γ =
        - ∑' γ : ↑((↑A : Set E.Group)ᶜ), a γ := by
    rw [← hsplit]
    ring
  have hsub_g :
      Summable (fun γ : ↑((↑A : Set E.Group)ᶜ) => E.gCoeff γ) :=
    E.summable_gCoeff.subtype _
  have hnorm_summable :
      Summable (fun γ : ↑((↑A : Set E.Group)ᶜ) => ‖a γ‖) := by
    refine hsub_g.of_norm_bounded ?_
    intro γ
    simpa [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg (a γ))] using
      ha_bound (γ : E.Group)
  have htail_norm :
      ‖∑' γ : ↑((↑A : Set E.Group)ᶜ), a γ‖ ≤
        ∑' γ : ↑((↑A : Set E.Group)ᶜ), ‖a γ‖ :=
    norm_tsum_le_tsum_norm hnorm_summable
  have htail_norm_le_g :
      (∑' γ : ↑((↑A : Set E.Group)ᶜ), ‖a γ‖) ≤
        ∑' γ : ↑((↑A : Set E.Group)ᶜ), E.gCoeff γ := by
    refine Summable.tsum_le_tsum ?_ hnorm_summable hsub_g
    intro γ
    exact ha_bound (γ : E.Group)
  simpa [a, htail_eq, Real.norm_eq_abs] using htail_norm.trans htail_norm_le_g

lemma abs_sum_sub_tsum_nonzero_gCoeff_character_re_le_gCoeff_tail
    (E : CayleyExtraction S) (A : Finset E.Group)
    (z : E.CompactAddDual) :
    |(∑ γ ∈ A,
        if γ = 0 then 0
        else E.gCoeff γ * (E.addCharacterValue z γ).re) -
      ∑' γ : E.Group,
        if γ = 0 then 0
        else E.gCoeff γ * (E.addCharacterValue z γ).re| ≤
      (∑' γ : E.Group, E.gCoeff γ) - ∑ γ ∈ A, E.gCoeff γ := by
  have htail :=
    E.abs_sum_sub_tsum_nonzero_gCoeff_character_re_le_tsum_compl A z
  have hsplit := E.summable_gCoeff.sum_add_tsum_compl (s := A)
  have htail_eq :
      (∑' γ : ↑((↑A : Set E.Group)ᶜ), E.gCoeff γ) =
        (∑' γ : E.Group, E.gCoeff γ) - ∑ γ ∈ A, E.gCoeff γ := by
    rw [← hsplit]
    ring
  simpa [htail_eq] using htail

lemma abs_sum_sub_tsum_nonzero_gCoeff_character_re_le_of_gCoeff_tail
    (E : CayleyExtraction S) (A : Finset E.Group)
    (z : E.CompactAddDual) {δ : ℝ}
    (htail :
      |(∑ γ ∈ A, E.gCoeff γ) - ∑' γ : E.Group, E.gCoeff γ| ≤ δ) :
    |(∑ γ ∈ A,
        if γ = 0 then 0
        else E.gCoeff γ * (E.addCharacterValue z γ).re) -
      ∑' γ : E.Group,
        if γ = 0 then 0
        else E.gCoeff γ * (E.addCharacterValue z γ).re| ≤ δ := by
  have h :=
    E.abs_sum_sub_tsum_nonzero_gCoeff_character_re_le_gCoeff_tail A z
  have htail_upper :
      (∑' γ : E.Group, E.gCoeff γ) - ∑ γ ∈ A, E.gCoeff γ ≤ δ := by
    have hle := (abs_le.mp htail).1
    linarith
  exact h.trans htail_upper

lemma abs_compactSmoothReal_sub_fReal_le_of_gCoeff_tail
    (E : CayleyExtraction S) (Q : Finset E.Group) (hQ : Q ≠ ∅)
    (z : E.CompactAddDual) (A : Finset E.Group)
    (hA0 : (0 : E.Group) ∈ A)
    (hAsupport : (E.compactSmoothTrigPoly Q).support ⊆ A)
    {M δ : ℝ} (hM_nonneg : 0 ≤ M)
    (hclose : ∀ γ ∈ A, ‖1 - E.fejerTrigPoly Q γ‖ ≤ M)
    (hg_tail :
      |(∑ γ ∈ A, E.gCoeff γ) - ∑' γ : E.Group, E.gCoeff γ| ≤ δ) :
    |E.compactSmoothReal Q z - E.fReal z| ≤
      δ + M * ∑ γ ∈ A, E.gCoeff γ := by
  exact E.abs_compactSmoothReal_sub_fReal_le_of_tsum_tail Q hQ z A hA0
    hAsupport hM_nonneg hclose
    (E.abs_sum_sub_tsum_nonzero_gCoeff_character_re_le_of_gCoeff_tail A z
      hg_tail)

lemma sum_gCoeff_sdiff_le_of_gCoeff_tail
    (E : CayleyExtraction S) (B A : Finset E.Group) {δ : ℝ}
    (hg_tail :
      |(∑ γ ∈ B, E.gCoeff γ) - ∑' γ : E.Group, E.gCoeff γ| ≤ δ) :
    (∑ γ ∈ A \ B, E.gCoeff γ) ≤ δ := by
  classical
  let c : E.Group → ℝ := fun γ => if γ ∈ B then 0 else E.gCoeff γ
  have hc_nonneg : ∀ γ, 0 ≤ c γ := by
    intro γ
    by_cases hγ : γ ∈ B
    · simp [c, hγ]
    · simp [c, hγ, E.gCoeff_nonneg γ]
  have hc_bound : ∀ γ, ‖c γ‖ ≤ E.gCoeff γ := by
    intro γ
    by_cases hγ : γ ∈ B
    · simp [c, hγ, E.gCoeff_nonneg γ]
    · simp [c, hγ, Real.norm_eq_abs,
        abs_of_nonneg (E.gCoeff_nonneg γ)]
  have hc : Summable c := E.summable_gCoeff.of_norm_bounded hc_bound
  have hsum_sdiff :
      (∑ γ ∈ A \ B, E.gCoeff γ) = ∑ γ ∈ A \ B, c γ := by
    refine Finset.sum_congr rfl ?_
    intro γ hγ
    have hnot : γ ∉ B := (Finset.mem_sdiff.mp hγ).2
    simp [c, hnot]
  have hle_tsum :
      (∑ γ ∈ A \ B, c γ) ≤ ∑' γ : E.Group, c γ :=
    hc.sum_le_tsum (A \ B) (fun γ _hγ => hc_nonneg γ)
  have hsumB_c : (∑ γ ∈ B, c γ) = 0 := by
    rw [Finset.sum_eq_zero]
    intro γ hγ
    simp [c, hγ]
  have hcompl_c :
      (∑' γ : ↑((↑B : Set E.Group)ᶜ), c γ) =
        ∑' γ : ↑((↑B : Set E.Group)ᶜ), E.gCoeff γ := by
    refine tsum_congr ?_
    intro γ
    have hnot : (γ : E.Group) ∉ B := by
      exact γ.property
    simp [c, hnot]
  have hc_split := hc.sum_add_tsum_compl (s := B)
  have hg_split := E.summable_gCoeff.sum_add_tsum_compl (s := B)
  have htail_c :
      (∑' γ : E.Group, c γ) =
        (∑' γ : E.Group, E.gCoeff γ) - ∑ γ ∈ B, E.gCoeff γ := by
    calc
      (∑' γ : E.Group, c γ)
          = (∑ γ ∈ B, c γ) +
              ∑' γ : ↑((↑B : Set E.Group)ᶜ), c γ := by
            exact hc_split.symm
      _ = ∑' γ : ↑((↑B : Set E.Group)ᶜ), E.gCoeff γ := by
            rw [hsumB_c, zero_add, hcompl_c]
      _ = (∑' γ : E.Group, E.gCoeff γ) - ∑ γ ∈ B, E.gCoeff γ := by
            rw [← hg_split]
            ring
  have htail_upper :
      (∑' γ : E.Group, E.gCoeff γ) - ∑ γ ∈ B, E.gCoeff γ ≤ δ := by
    have hle := (abs_le.mp hg_tail).1
    linarith
  rw [hsum_sdiff]
  exact hle_tsum.trans (by simpa [htail_c] using htail_upper)

lemma abs_fejer_nonzero_gCoeff_character_re_le_gCoeff
    (E : CayleyExtraction S) (Q : Finset E.Group)
    (z : E.CompactAddDual) (γ : E.Group) :
    |(if γ = 0 then 0
      else (E.fejerTrigPoly Q γ).re * E.gCoeff γ *
        (E.addCharacterValue z γ).re)| ≤ E.gCoeff γ := by
  by_cases hzero : γ = 0
  · simpa [hzero] using E.gCoeff_nonneg γ
  · have hK_nonneg : 0 ≤ (E.fejerTrigPoly Q γ).re :=
      E.fejerTrigPoly_apply_re_nonneg Q γ
    have hK_le : (E.fejerTrigPoly Q γ).re ≤ 1 :=
      E.fejerTrigPoly_apply_re_le_one Q γ
    have hK_abs_le : |(E.fejerTrigPoly Q γ).re| ≤ 1 := by
      simpa [abs_of_nonneg hK_nonneg] using hK_le
    have hg_nonneg : 0 ≤ E.gCoeff γ := E.gCoeff_nonneg γ
    have hchar_abs : |(E.addCharacterValue z γ).re| ≤ 1 :=
      (Complex.abs_re_le_norm (E.addCharacterValue z γ)).trans
        (by simp [E.norm_addCharacterValue z γ])
    calc
      |(if γ = 0 then 0
        else (E.fejerTrigPoly Q γ).re * E.gCoeff γ *
          (E.addCharacterValue z γ).re)|
          = |(E.fejerTrigPoly Q γ).re| * E.gCoeff γ *
              |(E.addCharacterValue z γ).re| := by
                simp [hzero, abs_mul, abs_of_nonneg hK_nonneg,
                  abs_of_nonneg hg_nonneg]
      _ ≤ 1 * E.gCoeff γ * 1 := by
            exact mul_le_mul
              (mul_le_mul hK_abs_le le_rfl hg_nonneg zero_le_one)
              hchar_abs
              (abs_nonneg _)
              (mul_nonneg zero_le_one hg_nonneg)
      _ = E.gCoeff γ := by ring

lemma abs_nonzero_gCoeff_character_re_sub_fejer_le
    (E : CayleyExtraction S) (Q : Finset E.Group)
    (z : E.CompactAddDual) (γ : E.Group)
    {M : ℝ} (hM_nonneg : 0 ≤ M)
    (hclose : ‖1 - E.fejerTrigPoly Q γ‖ ≤ M) :
    |(if γ = 0 then 0
        else E.gCoeff γ * (E.addCharacterValue z γ).re) -
      (if γ = 0 then 0
        else (E.fejerTrigPoly Q γ).re * E.gCoeff γ *
          (E.addCharacterValue z γ).re)| ≤ M * E.gCoeff γ := by
  by_cases hzero : γ = 0
  · simpa [hzero] using mul_nonneg hM_nonneg (E.gCoeff_nonneg γ)
  · have hK_abs : |1 - (E.fejerTrigPoly Q γ).re| ≤ M := by
      have hre :
          |(1 - E.fejerTrigPoly Q γ).re| ≤
            ‖1 - E.fejerTrigPoly Q γ‖ :=
        Complex.abs_re_le_norm _
      have hrewrite :
          (1 - E.fejerTrigPoly Q γ).re =
            1 - (E.fejerTrigPoly Q γ).re := by simp
      simpa [hrewrite] using hre.trans hclose
    have hchar_abs : |(E.addCharacterValue z γ).re| ≤ 1 :=
      (Complex.abs_re_le_norm (E.addCharacterValue z γ)).trans
        (by simp [E.norm_addCharacterValue z γ])
    have hg_nonneg : 0 ≤ E.gCoeff γ := E.gCoeff_nonneg γ
    have hdiff :
        (if γ = 0 then 0 else E.gCoeff γ * (E.addCharacterValue z γ).re) -
          (if γ = 0 then 0
            else (E.fejerTrigPoly Q γ).re * E.gCoeff γ *
              (E.addCharacterValue z γ).re) =
        (1 - (E.fejerTrigPoly Q γ).re) *
          E.gCoeff γ * (E.addCharacterValue z γ).re := by
      simp [hzero, mul_assoc]
      ring
    calc
      |(if γ = 0 then 0 else E.gCoeff γ * (E.addCharacterValue z γ).re) -
        (if γ = 0 then 0
          else (E.fejerTrigPoly Q γ).re * E.gCoeff γ *
            (E.addCharacterValue z γ).re)|
          = |(1 - (E.fejerTrigPoly Q γ).re) *
              E.gCoeff γ * (E.addCharacterValue z γ).re| := by
                rw [hdiff]
      _ = |1 - (E.fejerTrigPoly Q γ).re| *
            E.gCoeff γ * |(E.addCharacterValue z γ).re| := by
              rw [abs_mul, abs_mul, abs_of_nonneg hg_nonneg]
      _ ≤ M * E.gCoeff γ * 1 := by
            exact mul_le_mul
              (mul_le_mul hK_abs le_rfl hg_nonneg hM_nonneg)
              hchar_abs
              (abs_nonneg _)
              (mul_nonneg hM_nonneg hg_nonneg)
      _ = M * E.gCoeff γ := by ring

lemma abs_compactSmoothReal_sub_fReal_le_of_core_fejer_and_gCoeff_tail
    (E : CayleyExtraction S) (Q : Finset E.Group) (hQ : Q ≠ ∅)
    (z : E.CompactAddDual) (B : Finset E.Group)
    (hB0 : (0 : E.Group) ∈ B)
    {M δ : ℝ} (hM_nonneg : 0 ≤ M)
    (hclose : ∀ γ ∈ B, ‖1 - E.fejerTrigPoly Q γ‖ ≤ M)
    (hg_tail :
      |(∑ γ ∈ B, E.gCoeff γ) - ∑' γ : E.Group, E.gCoeff γ| ≤ δ) :
    |E.compactSmoothReal Q z - E.fReal z| ≤
      2 * δ + M * ∑ γ ∈ B, E.gCoeff γ := by
  classical
  let A : Finset E.Group := B ∪ (E.compactSmoothTrigPoly Q).support
  let a : E.Group → ℝ :=
    fun γ => if γ = 0 then 0
      else E.gCoeff γ * (E.addCharacterValue z γ).re
  let b : E.Group → ℝ :=
    fun γ => if γ = 0 then 0
      else (E.fejerTrigPoly Q γ).re * E.gCoeff γ *
        (E.addCharacterValue z γ).re
  have hBsubA : B ⊆ A := by
    intro γ hγ
    exact Finset.mem_union.mpr (Or.inl hγ)
  have hA0 : (0 : E.Group) ∈ A := hBsubA hB0
  have hAsupport : (E.compactSmoothTrigPoly Q).support ⊆ A := by
    intro γ hγ
    exact Finset.mem_union.mpr (Or.inr hγ)
  have hcompact :
      E.compactSmoothReal Q z =
        (E.coeff (0 : E.Group)).re - ∑ γ ∈ A, b γ := by
    simpa [b] using
      E.compactSmoothReal_eq_coeff_zero_sub_sum_nonzero_gCoeff
        Q hQ z A hA0 hAsupport
  have hf :
      E.fReal z =
        (E.coeff (0 : E.Group)).re - ∑' γ : E.Group, a γ := by
    simpa [a] using E.fReal_eq_coeff_zero_sub_tsum_nonzero_gCoeff z
  have hsplit_b :
      (∑ γ ∈ A, b γ) =
        (∑ γ ∈ B, b γ) + ∑ γ ∈ A \ B, b γ := by
    have h := Finset.sum_sdiff (s₁ := B) (s₂ := A) (f := b) hBsubA
    rw [← h]
    ring
  have htail_signed :
      |(∑' γ : E.Group, a γ) - ∑ γ ∈ B, a γ| ≤ δ := by
    have h :=
      E.abs_sum_sub_tsum_nonzero_gCoeff_character_re_le_of_gCoeff_tail B z
        hg_tail
    simpa [a, abs_sub_comm] using h
  have hcore :
      |(∑ γ ∈ B, a γ) - ∑ γ ∈ B, b γ| ≤
        M * ∑ γ ∈ B, E.gCoeff γ := by
    rw [← Finset.sum_sub_distrib]
    calc
      |∑ γ ∈ B, (a γ - b γ)|
          ≤ ∑ γ ∈ B, |a γ - b γ| := by
            exact Finset.abs_sum_le_sum_abs (fun γ => a γ - b γ) B
      _ ≤ ∑ γ ∈ B, M * E.gCoeff γ := by
            refine Finset.sum_le_sum ?_
            intro γ hγ
            simpa [a, b] using
              E.abs_nonzero_gCoeff_character_re_sub_fejer_le Q z γ
                hM_nonneg (hclose γ hγ)
      _ = M * ∑ γ ∈ B, E.gCoeff γ := by
            rw [Finset.mul_sum]
  have hextra :
      |∑ γ ∈ A \ B, b γ| ≤ δ := by
    calc
      |∑ γ ∈ A \ B, b γ|
          ≤ ∑ γ ∈ A \ B, |b γ| := by
            exact Finset.abs_sum_le_sum_abs b (A \ B)
      _ ≤ ∑ γ ∈ A \ B, E.gCoeff γ := by
            refine Finset.sum_le_sum ?_
            intro γ _hγ
            simpa [b] using
              E.abs_fejer_nonzero_gCoeff_character_re_le_gCoeff Q z γ
      _ ≤ δ := E.sum_gCoeff_sdiff_le_of_gCoeff_tail B A hg_tail
  rw [hcompact, hf, hsplit_b]
  have hdecomp :
      ((E.coeff (0 : E.Group)).re -
          ((∑ γ ∈ B, b γ) + ∑ γ ∈ A \ B, b γ)) -
        ((E.coeff (0 : E.Group)).re - ∑' γ : E.Group, a γ) =
      ((∑' γ : E.Group, a γ) - ∑ γ ∈ B, a γ) +
        ((∑ γ ∈ B, a γ) - ∑ γ ∈ B, b γ) -
          ∑ γ ∈ A \ B, b γ := by
    ring
  rw [hdecomp]
  calc
    |((∑' γ : E.Group, a γ) - ∑ γ ∈ B, a γ) +
        ((∑ γ ∈ B, a γ) - ∑ γ ∈ B, b γ) -
          ∑ γ ∈ A \ B, b γ|
        ≤ |(∑' γ : E.Group, a γ) - ∑ γ ∈ B, a γ| +
            |(∑ γ ∈ B, a γ) - ∑ γ ∈ B, b γ| +
              |∑ γ ∈ A \ B, b γ| := by
          calc
            |((∑' γ : E.Group, a γ) - ∑ γ ∈ B, a γ) +
                ((∑ γ ∈ B, a γ) - ∑ γ ∈ B, b γ) -
                  ∑ γ ∈ A \ B, b γ|
                = |(((∑' γ : E.Group, a γ) - ∑ γ ∈ B, a γ) +
                    ((∑ γ ∈ B, a γ) - ∑ γ ∈ B, b γ)) +
                    (-(∑ γ ∈ A \ B, b γ))| := by ring_nf
            _ ≤ |((∑' γ : E.Group, a γ) - ∑ γ ∈ B, a γ) +
                    ((∑ γ ∈ B, a γ) - ∑ γ ∈ B, b γ)| +
                  |-(∑ γ ∈ A \ B, b γ)| := abs_add_le _ _
            _ ≤ (|(∑' γ : E.Group, a γ) - ∑ γ ∈ B, a γ| +
                    |(∑ γ ∈ B, a γ) - ∑ γ ∈ B, b γ|) +
                  |∑ γ ∈ A \ B, b γ| := by
                    simpa [abs_neg] using
                      add_le_add_right
                        (abs_add_le
                          ((∑' γ : E.Group, a γ) - ∑ γ ∈ B, a γ)
                          ((∑ γ ∈ B, a γ) - ∑ γ ∈ B, b γ))
                        |∑ γ ∈ A \ B, b γ|
            _ = |(∑' γ : E.Group, a γ) - ∑ γ ∈ B, a γ| +
                    |(∑ γ ∈ B, a γ) - ∑ γ ∈ B, b γ| +
                  |∑ γ ∈ A \ B, b γ| := by ring
    _ ≤ δ + M * ∑ γ ∈ B, E.gCoeff γ + δ := by
          exact add_le_add (add_le_add htail_signed hcore) hextra
    _ = 2 * δ + M * ∑ γ ∈ B, E.gCoeff γ := by ring

theorem exists_compactSmoothReal_uniform_close
    (E : CayleyExtraction S) {ε : ℝ} (hε : 0 < ε) :
    ∃ Q : Finset E.Group, Q ≠ ∅ ∧
      ∀ z : E.CompactAddDual,
        |E.compactSmoothReal Q z - E.fReal z| ≤ ε := by
  classical
  let δ : ℝ := ε / 4
  have hδ_pos : 0 < δ := by
    dsimp [δ]
    positivity
  let Gtot : ℝ := ∑' γ : E.Group, E.gCoeff γ
  have htail_event :
      ∀ᶠ B : Finset E.Group in atTop,
        |(∑ γ ∈ B, E.gCoeff γ) - Gtot| < δ := by
    have h := (Metric.tendsto_nhds.mp E.summable_gCoeff.hasSum δ hδ_pos)
    filter_upwards [h] with B hB
    simpa [Real.dist_eq, Gtot] using hB
  obtain ⟨B₀, hB₀⟩ := Filter.eventually_atTop.mp htail_event
  let B : Finset E.Group := insert 0 B₀
  have hB_ge : B ≥ B₀ := by
    intro γ hγ
    exact Finset.mem_insert.mpr (Or.inr hγ)
  have hB_tail_lt : |(∑ γ ∈ B, E.gCoeff γ) - Gtot| < δ :=
    hB₀ B hB_ge
  have hB_tail :
      |(∑ γ ∈ B, E.gCoeff γ) - ∑' γ : E.Group, E.gCoeff γ| ≤ δ := by
    simpa [Gtot] using le_of_lt hB_tail_lt
  have hB0 : (0 : E.Group) ∈ B := Finset.mem_insert_self _ _
  let SB : ℝ := ∑ γ ∈ B, E.gCoeff γ
  have hSB_nonneg : 0 ≤ SB := by
    dsimp [SB]
    exact Finset.sum_nonneg fun γ _hγ => E.gCoeff_nonneg γ
  let M : ℝ := δ / (SB + 1)
  have hden_pos : 0 < SB + 1 := by
    nlinarith
  have hM_pos : 0 < M := by
    dsimp [M]
    exact div_pos hδ_pos hden_pos
  obtain ⟨Q, hQ, hlower⟩ := E.exists_fejerPairCoeffLowerBound B hM_pos
  have hclose : ∀ γ ∈ B, ‖1 - E.fejerTrigPoly Q γ‖ ≤ M :=
    E.fejerCoeffBound_of_pairCoeffLowerBound hQ hlower
  refine ⟨Q, hQ, ?_⟩
  intro z
  have hmain :=
    E.abs_compactSmoothReal_sub_fReal_le_of_core_fejer_and_gCoeff_tail
      Q hQ z B hB0 (le_of_lt hM_pos) hclose hB_tail
  have hM_mul : M * SB ≤ δ := by
    dsimp [M]
    rw [div_mul_eq_mul_div, div_le_iff₀ hden_pos]
    nlinarith
  calc
    |E.compactSmoothReal Q z - E.fReal z|
        ≤ 2 * δ + M * ∑ γ ∈ B, E.gCoeff γ := hmain
    _ = 2 * δ + M * SB := by rfl
    _ ≤ 2 * δ + δ := by
          nlinarith
    _ ≤ ε := by
          dsimp [δ]
          nlinarith

theorem exists_compactSmoothReal_uniform_close_and_fejerPairCoeffLowerBound
    (E : CayleyExtraction S) (Bextra : Finset E.Group)
    {ε Mlarge : ℝ} (hε : 0 < ε) (hMlarge : 0 < Mlarge) :
    ∃ Q : Finset E.Group, Q ≠ ∅ ∧
      E.FejerPairCoeffLowerBound Q Bextra Mlarge ∧
      ∀ z : E.CompactAddDual,
        |E.compactSmoothReal Q z - E.fReal z| ≤ ε := by
  classical
  let δ : ℝ := ε / 4
  have hδ_pos : 0 < δ := by
    dsimp [δ]
    positivity
  let Gtot : ℝ := ∑' γ : E.Group, E.gCoeff γ
  have htail_event :
      ∀ᶠ B : Finset E.Group in atTop,
        |(∑ γ ∈ B, E.gCoeff γ) - Gtot| < δ := by
    have h := (Metric.tendsto_nhds.mp E.summable_gCoeff.hasSum δ hδ_pos)
    filter_upwards [h] with B hB
    simpa [Real.dist_eq, Gtot] using hB
  obtain ⟨B₀, hB₀⟩ := Filter.eventually_atTop.mp htail_event
  let Bcore : Finset E.Group := insert 0 B₀
  let B : Finset E.Group := Bcore ∪ Bextra
  have hB_ge : B ≥ B₀ := by
    intro γ hγ
    exact Finset.mem_union_left Bextra (Finset.mem_insert.mpr (Or.inr hγ))
  have hB_tail_lt : |(∑ γ ∈ B, E.gCoeff γ) - Gtot| < δ :=
    hB₀ B hB_ge
  have hB_tail :
      |(∑ γ ∈ B, E.gCoeff γ) - ∑' γ : E.Group, E.gCoeff γ| ≤ δ := by
    simpa [Gtot] using le_of_lt hB_tail_lt
  have hB0 : (0 : E.Group) ∈ B := by
    exact Finset.mem_union_left Bextra (Finset.mem_insert_self _ _)
  let SB : ℝ := ∑ γ ∈ B, E.gCoeff γ
  have hSB_nonneg : 0 ≤ SB := by
    dsimp [SB]
    exact Finset.sum_nonneg fun γ _hγ => E.gCoeff_nonneg γ
  let Mapprox : ℝ := δ / (SB + 1)
  have hden_pos : 0 < SB + 1 := by
    nlinarith
  have hMapprox_pos : 0 < Mapprox := by
    dsimp [Mapprox]
    exact div_pos hδ_pos hden_pos
  let Mchoose : ℝ := min Mapprox Mlarge
  have hMchoose_pos : 0 < Mchoose := by
    dsimp [Mchoose]
    exact lt_min hMapprox_pos hMlarge
  obtain ⟨Q, hQ, hlower⟩ := E.exists_fejerPairCoeffLowerBound B hMchoose_pos
  have hchoose_le_approx : Mchoose ≤ Mapprox := by
    dsimp [Mchoose]
    exact min_le_left _ _
  have hchoose_le_large : Mchoose ≤ Mlarge := by
    dsimp [Mchoose]
    exact min_le_right _ _
  have hclose_choose : ∀ γ ∈ B, ‖1 - E.fejerTrigPoly Q γ‖ ≤ Mchoose :=
    E.fejerCoeffBound_of_pairCoeffLowerBound hQ hlower
  have hclose : ∀ γ ∈ B, ‖1 - E.fejerTrigPoly Q γ‖ ≤ Mapprox := by
    intro γ hγ
    exact (hclose_choose γ hγ).trans hchoose_le_approx
  have hBextra :
      E.FejerPairCoeffLowerBound Q Bextra Mlarge := by
    intro γ hγ
    have hγB : γ ∈ B := Finset.mem_union_right Bcore hγ
    have hlow := hlower γ hγB
    have hle : 1 - Mlarge ≤ 1 - Mchoose := by linarith
    exact hle.trans hlow
  refine ⟨Q, hQ, hBextra, ?_⟩
  intro z
  have hmain :=
    E.abs_compactSmoothReal_sub_fReal_le_of_core_fejer_and_gCoeff_tail
      Q hQ z B hB0 (le_of_lt hMapprox_pos) hclose hB_tail
  have hM_mul : Mapprox * SB ≤ δ := by
    dsimp [Mapprox]
    rw [div_mul_eq_mul_div, div_le_iff₀ hden_pos]
    nlinarith
  calc
    |E.compactSmoothReal Q z - E.fReal z|
        ≤ 2 * δ + Mapprox * ∑ γ ∈ B, E.gCoeff γ := hmain
    _ = 2 * δ + Mapprox * SB := by rfl
    _ ≤ 2 * δ + δ := by
          nlinarith
    _ ≤ ε := by
          dsimp [δ]
          nlinarith

lemma gReal_nonneg (E : CayleyExtraction S) :
    ∀ z : E.CompactAddDual, 0 ≤ E.gReal z := by
  intro z
  rw [E.gReal_eq_tsum_gCoeff_mul_character_re E.summable_gCoeff z]
  let a : E.Group → ℝ :=
    fun γ => E.gCoeff γ * (E.addCharacterValue z γ).re
  let T : ℝ := ∑' γ : E.Group, a γ
  change 0 ≤ T
  refine le_of_forall_pos_le_add ?_
  intro ε hε
  let δ : ℝ := ε / 4
  have hδ : 0 < δ := by positivity
  have hsumA : Summable a := by
    simpa [a] using E.summable_gCoeff_mul_character_re E.summable_gCoeff z
  have hsumG : Summable E.gCoeff := E.summable_gCoeff
  let Gtot : ℝ := ∑' γ : E.Group, E.gCoeff γ
  have hA_event :
      ∀ᶠ B : Finset E.Group in atTop,
        |(∑ γ ∈ B, a γ) - T| < δ := by
    have h := (Metric.tendsto_nhds.mp hsumA.hasSum δ hδ)
    filter_upwards [h] with B hB
    simpa [Real.dist_eq, T] using hB
  have hG_event :
      ∀ᶠ B : Finset E.Group in atTop,
        |(∑ γ ∈ B, E.gCoeff γ) - Gtot| < δ := by
    have h := (Metric.tendsto_nhds.mp hsumG.hasSum δ hδ)
    filter_upwards [h] with B hB
    simpa [Real.dist_eq, Gtot] using hB
  obtain ⟨B, hB⟩ :=
    (Filter.eventually_atTop.mp (hA_event.and hG_event))
  have hB_self := hB B (le_rfl : B ≥ B)
  have hA_B : |(∑ γ ∈ B, a γ) - T| < δ := hB_self.1
  have hG_B : |(∑ γ ∈ B, E.gCoeff γ) - Gtot| < δ := hB_self.2
  let GB : ℝ := ∑ γ ∈ B, E.gCoeff γ
  have hGB_nonneg : 0 ≤ GB := by
    dsimp [GB]
    exact Finset.sum_nonneg (fun γ _hγ => E.gCoeff_nonneg γ)
  let M : ℝ := δ / ((GB + 1) * (δ + 1))
  have hden_pos : 0 < (GB + 1) * (δ + 1) := by positivity
  have hM_pos : 0 < M := by
    dsimp [M]
    exact div_pos hδ hden_pos
  have hM_lt : M < 1 := by
    dsimp [M]
    rw [div_lt_iff₀ hden_pos]
    nlinarith [hGB_nonneg, hδ]
  have hMGB_le : M * GB ≤ δ := by
    dsimp [M]
    rw [div_mul_eq_mul_div, div_le_iff₀ hden_pos]
    have hden_ge : GB ≤ (GB + 1) * (δ + 1) := by
      nlinarith [hGB_nonneg, hδ]
    exact mul_le_mul_of_nonneg_left hden_ge (le_of_lt hδ)
  obtain ⟨Q, hQ, hlower⟩ := E.exists_fejerPairCoeffLowerBound B hM_pos
  let P : E.TrigPoly := E.shiftedFejerTrigPoly Q z
  let C : Finset E.Group := P.support \ B
  let D : Finset E.Group := B ∪ C
  have hD_ge : D ≥ B := by
    intro γ hγ
    exact Finset.mem_union.mpr (Or.inl hγ)
  have hD_close := hB D hD_ge
  have hG_D : |(∑ γ ∈ D, E.gCoeff γ) - Gtot| < δ := hD_close.2
  have hdisj : Disjoint B C := by
    rw [Finset.disjoint_left]
    intro γ hγB hγC
    exact (Finset.mem_sdiff.mp hγC).2 hγB
  have hsumD :
      (∑ γ ∈ D, E.gCoeff γ) =
        (∑ γ ∈ B, E.gCoeff γ) + ∑ γ ∈ C, E.gCoeff γ := by
    dsimp [D]
    rw [Finset.sum_union hdisj]
  have hC_lt : (∑ γ ∈ C, E.gCoeff γ) < 2 * δ := by
    have hD_upper : (∑ γ ∈ D, E.gCoeff γ) - Gtot < δ :=
      (abs_sub_lt_iff.mp hG_D).1
    have hB_lower : Gtot - (∑ γ ∈ B, E.gCoeff γ) < δ :=
      (abs_sub_lt_iff.mp hG_B).2
    linarith
  have hfinite :=
    E.sum_gCoeff_mul_character_re_ge_neg_of_fejerPairCoeffLowerBound
      Q B z hQ hM_lt hlower
  have hsumB_lower : -(3 * δ) < ∑ γ ∈ B, a γ := by
    dsimp [C, P, a, GB] at hfinite hC_lt hMGB_le
    nlinarith
  have hT_lower : -(4 * δ) < T := by
    have hA_lower : (∑ γ ∈ B, a γ) - T < δ :=
      (abs_sub_lt_iff.mp hA_B).1
    nlinarith
  have hδ_eq : 4 * δ = ε := by
    dsimp [δ]
    ring
  linarith

lemma norm_gComplex_le_tsum_gCoeff
    (E : CayleyExtraction S) (hsum : Summable E.gCoeff)
    (z : E.CompactAddDual) :
    ‖E.gComplex z‖ ≤ ∑' γ : E.Group, E.gCoeff γ := by
  have hnorm_summable :
      Summable fun γ : E.Group => ‖E.gComplexTerm γ z‖ := by
    simpa [E.norm_gComplexTerm_eq_gCoeff] using hsum
  unfold gComplex
  calc
    ‖∑' γ : E.Group, E.gComplexTerm γ z‖
        ≤ ∑' γ : E.Group, ‖E.gComplexTerm γ z‖ :=
      norm_tsum_le_tsum_norm hnorm_summable
    _ = ∑' γ : E.Group, E.gCoeff γ := by
      exact tsum_congr fun γ => E.norm_gComplexTerm_eq_gCoeff γ z

lemma gReal_le_tsum_gCoeff
    (E : CayleyExtraction S) (hsum : Summable E.gCoeff)
    (z : E.CompactAddDual) :
    E.gReal z ≤ ∑' γ : E.Group, E.gCoeff γ := by
  unfold gReal
  exact (Complex.re_le_norm (E.gComplex z)).trans
    (E.norm_gComplex_le_tsum_gCoeff hsum z)

lemma gReal_le_one (E : CayleyExtraction S) :
    ∀ z : E.CompactAddDual, E.gReal z ≤ 1 := by
  intro z
  exact (E.gReal_le_tsum_gCoeff E.summable_gCoeff z).trans
    E.tsum_gCoeff_le_one

lemma fReal_nonneg (E : CayleyExtraction S) :
    ∀ z : E.CompactAddDual, 0 ≤ E.fReal z := by
  intro z
  unfold fReal
  linarith [E.gReal_le_one z]

lemma fReal_le_one (E : CayleyExtraction S) :
    ∀ z : E.CompactAddDual, E.fReal z ≤ 1 := by
  intro z
  unfold fReal
  linarith [E.gReal_nonneg z]

lemma levelOne_character_eq_one_of_gReal_eq_one
    (E : CayleyExtraction S)
    (hsum : Summable E.gCoeff)
    (htsum : (∑' γ : E.Group, E.gCoeff γ) = 1)
    {x : E.CompactAddDual} (hx : E.gReal x = 1)
    {γ : E.Group} (hγ : 0 < E.gCoeff γ) :
    E.addCharacterValue x γ = 1 := by
  classical
  have hre_le : ∀ δ : E.Group, (E.addCharacterValue x δ).re ≤ 1 :=
    fun δ => E.addCharacterValue_re_le_one x δ
  have hmul_summable := E.summable_gCoeff_mul_character_re hsum x
  have hdef_nonneg :
      ∀ δ : E.Group,
        0 ≤ E.gCoeff δ - E.gCoeff δ * (E.addCharacterValue x δ).re := by
    intro δ
    have hcoeff_nonneg : 0 ≤ E.gCoeff δ := E.gCoeff_nonneg δ
    have hfactor_nonneg : 0 ≤ 1 - (E.addCharacterValue x δ).re := by
      linarith [hre_le δ]
    nlinarith [mul_nonneg hcoeff_nonneg hfactor_nonneg]
  let dNN : E.Group → NNReal := fun δ =>
    ⟨E.gCoeff δ - E.gCoeff δ * (E.addCharacterValue x δ).re,
      hdef_nonneg δ⟩
  have hdef_summable :
      Summable fun δ : E.Group =>
        (E.gCoeff δ - E.gCoeff δ * (E.addCharacterValue x δ).re) := by
    exact hsum.sub hmul_summable
  have hdNN_summable : Summable dNN := by
    rw [← NNReal.summable_coe]
    change Summable fun δ : E.Group =>
      E.gCoeff δ - E.gCoeff δ * (E.addCharacterValue x δ).re
    exact hdef_summable
  have hdef_tsum_zero :
      (∑' δ : E.Group,
        (E.gCoeff δ - E.gCoeff δ * (E.addCharacterValue x δ).re)) = 0 := by
    have hsub :=
      hsum.hasSum.sub hmul_summable.hasSum
    have hsub_tsum :
        (∑' δ : E.Group,
          (E.gCoeff δ - E.gCoeff δ * (E.addCharacterValue x δ).re)) =
          (∑' δ : E.Group, E.gCoeff δ) -
            (∑' δ : E.Group,
              E.gCoeff δ * (E.addCharacterValue x δ).re) := by
      exact hsub.tsum_eq
    rw [hsub_tsum]
    rw [htsum, ← E.gReal_eq_tsum_gCoeff_mul_character_re hsum x, hx]
    ring
  have hdNN_tsum_zero : (∑' δ : E.Group, dNN δ) = 0 := by
    apply NNReal.eq
    rw [NNReal.coe_tsum]
    change
      (∑' δ : E.Group,
        (E.gCoeff δ - E.gCoeff δ * (E.addCharacterValue x δ).re)) = 0
    exact hdef_tsum_zero
  by_contra hne
  have hre_lt : (E.addCharacterValue x γ).re < 1 := by
    have hle := hre_le γ
    by_contra hnot
    have hre_eq : (E.addCharacterValue x γ).re = 1 := le_antisymm hle (not_lt.mp hnot)
    exact hne (E.addCharacterValue_eq_one_of_re_eq_one x γ hre_eq)
  have hdNN_pos : 0 < dNN γ := by
    rw [show dNN γ =
        ⟨E.gCoeff γ - E.gCoeff γ * (E.addCharacterValue x γ).re,
          hdef_nonneg γ⟩ by rfl]
    rw [← NNReal.coe_pos]
    change 0 < E.gCoeff γ - E.gCoeff γ * (E.addCharacterValue x γ).re
    nlinarith [mul_lt_mul_of_pos_left hre_lt hγ]
  have htsum_pos : 0 < ∑' δ : E.Group, dNN δ :=
    NNReal.tsum_pos hdNN_summable γ hdNN_pos
  exact (ne_of_gt htsum_pos) hdNN_tsum_zero

/-- Conditional level-one subgroup closure for the compact complement kernel.

The remaining positive-definite equality case has to prove `hchars`: if
`gReal x = 1`, then every character with positive coefficient is trivial at
`x`.  Once that is known, closure under subtraction is just character algebra
and termwise equality of the Fourier series. -/
lemma levelOneSubgroupKernel_gReal_of_levelOne_chars
    (E : CayleyExtraction S)
    (hg0 : E.gReal (0 : E.CompactAddDual) = 1)
    (hchars :
      ∀ x : E.CompactAddDual, E.gReal x = 1 →
        ∀ γ : E.Group, 0 < E.gCoeff γ →
          E.addCharacterValue x γ = 1) :
    LevelOneSubgroupKernel E.gReal where
  map_zero := hg0
  sub_mem := by
    intro x y hx hy
    have hcomplex :
        E.gComplex (x - y) = E.gComplex (0 : E.CompactAddDual) := by
      unfold gComplex
      refine tsum_congr ?_
      intro γ
      by_cases hpos : 0 < E.gCoeff γ
      · have hxγ : E.addCharacterValue x γ = 1 := hchars x hx γ hpos
        have hyγ : E.addCharacterValue y γ = 1 := hchars y hy γ hpos
        have hxyγ : E.addCharacterValue (x - y) γ = 1 := by
          rw [sub_eq_add_neg, E.addCharacterValue_add_point,
            E.addCharacterValue_neg_point, hxγ, hyγ]
          simp
        unfold gComplexTerm
        simp [hxyγ]
      · have hzero : E.gCoeff γ = 0 :=
          le_antisymm (not_lt.mp hpos) (E.gCoeff_nonneg γ)
        simp [gComplexTerm, hzero]
    change (E.gComplex (x - y)).re = 1
    rw [hcomplex]
    simpa [gReal] using hg0

lemma levelOneSubgroupKernel_gReal_of_gReal_zero_eq_one
    (E : CayleyExtraction S)
    (hsum : Summable E.gCoeff)
    (hg0 : E.gReal (0 : E.CompactAddDual) = 1) :
    LevelOneSubgroupKernel E.gReal := by
  have htsum : (∑' γ : E.Group, E.gCoeff γ) = 1 := by
    rw [← E.gReal_zero_eq_tsum_gCoeff]
    exact hg0
  exact E.levelOneSubgroupKernel_gReal_of_levelOne_chars hg0
    (fun x hx γ hpos =>
      E.levelOne_character_eq_one_of_gReal_eq_one hsum htsum hx hpos)

lemma exists_ne_zero_gCoeff_pos_of_gReal_zero_eq_one
    (E : CayleyExtraction S) (hη : 0 < η)
    (hg0 : E.gReal (0 : E.CompactAddDual) = 1) :
    ∃ γ : E.Group, γ ≠ 0 ∧ 0 < E.gCoeff γ := by
  classical
  by_contra hnone
  push Not at hnone
  have hzero_nonzero : ∀ γ : E.Group, γ ≠ 0 → E.gCoeff γ = 0 := by
    intro γ hγ
    exact le_antisymm (hnone γ hγ) (E.gCoeff_nonneg γ)
  have htsum_single :
      (∑' γ : E.Group, E.gCoeff γ) = E.gCoeff 0 := by
    exact tsum_eq_single (0 : E.Group) (by
      intro γ hγ
      exact hzero_nonzero γ hγ)
  have htsum_one :
      (∑' γ : E.Group, E.gCoeff γ) = 1 := by
    rw [← E.gReal_zero_eq_tsum_gCoeff]
    exact hg0
  have hcoeff_zero_one : E.gCoeff 0 = 1 := by
    rw [← htsum_single, htsum_one]
  have hle := E.gCoeff_zero_le_one_sub_eta
  nlinarith

lemma levelOneAddSubgroup_gReal_not_finiteIndex_of_gReal_zero_eq_one
    (E : CayleyExtraction S)
    (hsum : Summable E.gCoeff) (hη : 0 < η)
    {hg_level : LevelOneSubgroupKernel E.gReal}
    (hg0 : E.gReal (0 : E.CompactAddDual) = 1) :
    ¬ (levelOneAddSubgroup E.gReal hg_level :
      AddSubgroup E.CompactAddDual).FiniteIndex := by
  classical
  intro hfinite
  let H : AddSubgroup E.CompactAddDual :=
    levelOneAddSubgroup E.gReal hg_level
  obtain ⟨γ, hγ_ne, hγ_pos⟩ :=
    E.exists_ne_zero_gCoeff_pos_of_gReal_zero_eq_one hη hg0
  have htsum :
      (∑' δ : E.Group, E.gCoeff δ) = 1 := by
    rw [← E.gReal_zero_eq_tsum_gCoeff]
    exact hg0
  have hchar_on_H :
      ∀ x : E.CompactAddDual, x ∈ H → E.addCharacterValue x γ = 1 := by
    intro x hx
    exact E.levelOne_character_eq_one_of_gReal_eq_one hsum htsum
      (mem_levelOneAddSubgroup.mp hx) hγ_pos
  let N : ℕ := Nat.factorial H.index
  have hN_pos : 0 < N := Nat.factorial_pos H.index
  have hN_mem_H : ∀ x : E.CompactAddDual, N • x ∈ H := by
    intro x
    exact AddSubgroup.nsmul_mem_of_index_ne_zero_of_dvd
      (H := H) hfinite.index_ne_zero x
      (n := N) (fun m hm_pos hm_le => Nat.dvd_factorial hm_pos hm_le)
  have hchar_nsmul_all :
      ∀ x : E.CompactAddDual, E.addCharacterValue x (N • γ) = 1 := by
    intro x
    have hxchar : E.addCharacterValue (N • x) γ = 1 :=
      hchar_on_H (N • x) (hN_mem_H x)
    rw [E.addCharacterValue_nsmul_point] at hxchar
    rw [E.addCharacterValue_nsmul_frequency]
    exact hxchar
  have hNγ_zero : N • γ = 0 := by
    by_contra hNγ_ne
    rcases E.exists_dual_point_ne_one hNγ_ne with ⟨x, hx⟩
    exact hx (hchar_nsmul_all x)
  have hγ_zero : γ = 0 := by
    have hinj := nsmul_right_injective (M := E.Group) (Nat.ne_of_gt hN_pos)
    exact hinj (by simpa using hNγ_zero)
  exact hγ_ne hγ_zero

lemma fReal_nonneg_of_gReal_le_one
    (E : CayleyExtraction S)
    (hg_le : ∀ x : E.CompactAddDual, E.gReal x ≤ 1) :
    ∀ x : E.CompactAddDual, 0 ≤ E.fReal x := by
  intro x
  unfold fReal
  linarith [hg_le x]

lemma fReal_le_one_of_gReal_nonneg
    (E : CayleyExtraction S)
    (hg_nonneg : ∀ x : E.CompactAddDual, 0 ≤ E.gReal x) :
    ∀ x : E.CompactAddDual, E.fReal x ≤ 1 := by
  intro x
  unfold fReal
  linarith [hg_nonneg x]

theorem compact_limit_cliqueDensity_pos_of_gReal_bounds
    (E : CayleyExtraction S)
    (_hℓ : 2 ≤ ℓ) (hη : 0 < η)
    [ConnectedSpace E.CompactAddDual]
    (hsum : Summable E.gCoeff)
    (hg_nonneg : ∀ x : E.CompactAddDual, 0 ≤ E.gReal x)
    (hg_le : ∀ x : E.CompactAddDual, E.gReal x ≤ 1) :
    0 < continuousCliqueDensity E.haar ℓ E.fReal := by
  classical
  letI : CompactSpace E.CompactAddDual := E.compactAddDual_compactSpace
  letI : T2Space E.CompactAddDual := E.compactAddDual_t2Space
  letI : IsTopologicalAddGroup E.CompactAddDual :=
    E.compactAddDual_isTopologicalAddGroup
  have hbranch :
      E.gReal (0 : E.CompactAddDual) < 1 ∨
        LevelOneSubgroupKernel E.gReal := by
    by_cases hlt : E.gReal (0 : E.CompactAddDual) < 1
    · exact Or.inl hlt
    · have hg0 : E.gReal (0 : E.CompactAddDual) = 1 :=
        le_antisymm (hg_le 0) (not_lt.mp hlt)
      exact Or.inr (E.levelOneSubgroupKernel_gReal_of_gReal_zero_eq_one hsum hg0)
  change
    0 < continuousCliqueDensity E.haar ℓ
      (fun x : E.CompactAddDual => 1 - E.gReal x)
  exact
    continuousCliqueDensity_pos_of_lt_one_or_levelOneSubgroupKernel
      E.haar ℓ E.gReal (E.gReal_continuous hsum)
      hg_nonneg hg_le hη (E.integral_gReal_le_one_sub_eta hsum) hbranch

/-- Variant of `compact_limit_cliqueDensity_pos_of_gReal_bounds` that replaces
connectedness of the whole compact dual by the exact infinite-index certificate
for every level-one subgroup structure on `E.gReal`. -/
theorem compact_limit_cliqueDensity_pos_of_gReal_bounds_not_finiteIndex
    (E : CayleyExtraction S)
    (_hℓ : 2 ≤ ℓ) (_hη : 0 < η)
    (hsum : Summable E.gCoeff)
    (hg_nonneg : ∀ x : E.CompactAddDual, 0 ≤ E.gReal x)
    (hg_le : ∀ x : E.CompactAddDual, E.gReal x ≤ 1)
    (hlevel_not_finiteIndex :
      ∀ hg_level : LevelOneSubgroupKernel E.gReal,
        ¬ (levelOneAddSubgroup E.gReal hg_level :
          AddSubgroup E.CompactAddDual).FiniteIndex) :
    0 < continuousCliqueDensity E.haar ℓ E.fReal := by
  classical
  letI : CompactSpace E.CompactAddDual := E.compactAddDual_compactSpace
  letI : T2Space E.CompactAddDual := E.compactAddDual_t2Space
  letI : IsTopologicalAddGroup E.CompactAddDual :=
    E.compactAddDual_isTopologicalAddGroup
  have hbranch :
      E.gReal (0 : E.CompactAddDual) < 1 ∨
        ∃ hg_level : LevelOneSubgroupKernel E.gReal,
          ¬ (levelOneAddSubgroup E.gReal hg_level :
            AddSubgroup E.CompactAddDual).FiniteIndex := by
    by_cases hlt : E.gReal (0 : E.CompactAddDual) < 1
    · exact Or.inl hlt
    · have hg0 : E.gReal (0 : E.CompactAddDual) = 1 :=
        le_antisymm (hg_le 0) (not_lt.mp hlt)
      let hg_level : LevelOneSubgroupKernel E.gReal :=
        E.levelOneSubgroupKernel_gReal_of_gReal_zero_eq_one hsum hg0
      exact Or.inr ⟨hg_level, hlevel_not_finiteIndex hg_level⟩
  change
    0 < continuousCliqueDensity E.haar ℓ
      (fun x : E.CompactAddDual => 1 - E.gReal x)
  exact
    continuousCliqueDensity_pos_of_lt_one_or_levelOneSubgroupKernel_not_finiteIndex
      E.haar ℓ E.gReal (E.gReal_continuous hsum)
      hg_nonneg hg_le hbranch

/-- Compact positive clique-density endpoint with connectedness replaced by the
finite-index contradiction proved from extraction torsion-freeness and the mean
gap.  The remaining analytic input is the pointwise bound `0 ≤ gReal ≤ 1` and
summability of `gCoeff`. -/
theorem compact_limit_cliqueDensity_pos_of_gReal_bounds_infiniteIndex
    (E : CayleyExtraction S)
    (_hℓ : 2 ≤ ℓ) (hη : 0 < η)
    (hsum : Summable E.gCoeff)
    (hg_nonneg : ∀ x : E.CompactAddDual, 0 ≤ E.gReal x)
    (hg_le : ∀ x : E.CompactAddDual, E.gReal x ≤ 1) :
    0 < continuousCliqueDensity E.haar ℓ E.fReal := by
  classical
  letI : CompactSpace E.CompactAddDual := E.compactAddDual_compactSpace
  letI : T2Space E.CompactAddDual := E.compactAddDual_t2Space
  letI : IsTopologicalAddGroup E.CompactAddDual :=
    E.compactAddDual_isTopologicalAddGroup
  have hbranch :
      E.gReal (0 : E.CompactAddDual) < 1 ∨
        ∃ hg_level : LevelOneSubgroupKernel E.gReal,
          ¬ (levelOneAddSubgroup E.gReal hg_level :
            AddSubgroup E.CompactAddDual).FiniteIndex := by
    by_cases hlt : E.gReal (0 : E.CompactAddDual) < 1
    · exact Or.inl hlt
    · have hg0 : E.gReal (0 : E.CompactAddDual) = 1 :=
        le_antisymm (hg_le 0) (not_lt.mp hlt)
      let hg_level : LevelOneSubgroupKernel E.gReal :=
        E.levelOneSubgroupKernel_gReal_of_gReal_zero_eq_one hsum hg0
      have hnot :
          ¬ (levelOneAddSubgroup E.gReal hg_level :
            AddSubgroup E.CompactAddDual).FiniteIndex :=
        E.levelOneAddSubgroup_gReal_not_finiteIndex_of_gReal_zero_eq_one
          hsum hη hg0
      exact Or.inr ⟨hg_level, hnot⟩
  change
    0 < continuousCliqueDensity E.haar ℓ
      (fun x : E.CompactAddDual => 1 - E.gReal x)
  exact
    continuousCliqueDensity_pos_of_lt_one_or_levelOneSubgroupKernel_not_finiteIndex
      E.haar ℓ E.gReal (E.gReal_continuous hsum)
      hg_nonneg hg_le hbranch

/-- Compact positive clique-density endpoint with summability and the upper
pointwise bound already discharged. -/
theorem compact_limit_cliqueDensity_pos_of_gReal_nonneg
    (E : CayleyExtraction S)
    (hℓ : 2 ≤ ℓ) (hη : 0 < η)
    (hg_nonneg : ∀ x : E.CompactAddDual, 0 ≤ E.gReal x) :
    0 < continuousCliqueDensity E.haar ℓ E.fReal :=
  E.compact_limit_cliqueDensity_pos_of_gReal_bounds_infiniteIndex
    hℓ hη E.summable_gCoeff hg_nonneg E.gReal_le_one

/-- Compact positive clique-density endpoint for the compact-Cayley extraction
kernel, with all pointwise bounds discharged. -/
theorem compact_limit_cliqueDensity_pos
    (E : CayleyExtraction S)
    (hℓ : 2 ≤ ℓ) (hη : 0 < η) :
    0 < continuousCliqueDensity E.haar ℓ E.fReal :=
  E.compact_limit_cliqueDensity_pos_of_gReal_nonneg hℓ hη E.gReal_nonneg

theorem compactSmoothReal_cliqueDensity_pos_of_close
    (E : CayleyExtraction S) (Q : Finset E.Group) {κ : ℝ}
    (hκ_nonneg : 0 ≤ κ) (hκ_le_one : κ ≤ 1)
    (hclose : ∀ z : E.CompactAddDual,
      |E.fReal z - E.compactSmoothReal Q z| ≤ κ)
    (hmargin :
      (((continuousCliqueEdgePairs ℓ).card : ℝ) * κ) *
          (2 : ℝ) ^ (continuousCliqueEdgePairs ℓ).card <
        continuousCliqueDensity E.haar ℓ E.fReal) :
    0 < continuousCliqueDensity E.haar ℓ (E.compactSmoothReal Q) := by
  classical
  let C : ℝ := (((continuousCliqueEdgePairs ℓ).card : ℝ) * κ) *
    (2 : ℝ) ^ (continuousCliqueEdgePairs ℓ).card
  have hf_abs : ∀ z : E.CompactAddDual, |E.fReal z| ≤ 2 := by
    intro z
    have hnonneg := E.fReal_nonneg z
    have hle := E.fReal_le_one z
    rw [abs_of_nonneg hnonneg]
    linarith
  have hs_abs : ∀ z : E.CompactAddDual, |E.compactSmoothReal Q z| ≤ 2 := by
    intro z
    have hf_abs_one : |E.fReal z| ≤ 1 := by
      have hnonneg := E.fReal_nonneg z
      have hle := E.fReal_le_one z
      rw [abs_of_nonneg hnonneg]
      exact hle
    have hclose' : |E.compactSmoothReal Q z - E.fReal z| ≤ κ := by
      simpa [abs_sub_comm] using hclose z
    calc
      |E.compactSmoothReal Q z|
          = |(E.compactSmoothReal Q z - E.fReal z) + E.fReal z| := by ring_nf
      _ ≤ |E.compactSmoothReal Q z - E.fReal z| + |E.fReal z| := abs_add_le _ _
      _ ≤ κ + 1 := add_le_add hclose' hf_abs_one
      _ ≤ 2 := by linarith
  have hdiff :=
    continuousCliqueDensity_lipschitz_sup_two_pow
      E.haar ℓ
      (E.fReal_continuous E.summable_gCoeff).measurable
      (E.compactSmoothReal_continuous Q).measurable
      hf_abs hs_abs hκ_nonneg hclose
  have hlow :
      continuousCliqueDensity E.haar ℓ E.fReal -
        continuousCliqueDensity E.haar ℓ (E.compactSmoothReal Q) ≤ C := by
    exact (le_abs_self _).trans (by simpa [C] using hdiff)
  have hC_lt :
      C < continuousCliqueDensity E.haar ℓ E.fReal := by
    simpa [C] using hmargin
  linarith

theorem compactSmoothReal_cliqueDensity_ge_sub_error_of_close
    (E : CayleyExtraction S) (Q : Finset E.Group) {κ : ℝ}
    (hκ_nonneg : 0 ≤ κ) (hκ_le_one : κ ≤ 1)
    (hclose : ∀ z : E.CompactAddDual,
      |E.fReal z - E.compactSmoothReal Q z| ≤ κ) :
    continuousCliqueDensity E.haar ℓ E.fReal -
        ((((continuousCliqueEdgePairs ℓ).card : ℝ) * κ) *
          (2 : ℝ) ^ (continuousCliqueEdgePairs ℓ).card) ≤
      continuousCliqueDensity E.haar ℓ (E.compactSmoothReal Q) := by
  classical
  let C : ℝ := (((continuousCliqueEdgePairs ℓ).card : ℝ) * κ) *
    (2 : ℝ) ^ (continuousCliqueEdgePairs ℓ).card
  have hf_abs : ∀ z : E.CompactAddDual, |E.fReal z| ≤ 2 := by
    intro z
    have hnonneg := E.fReal_nonneg z
    have hle := E.fReal_le_one z
    rw [abs_of_nonneg hnonneg]
    linarith
  have hs_abs : ∀ z : E.CompactAddDual, |E.compactSmoothReal Q z| ≤ 2 := by
    intro z
    have hf_abs_one : |E.fReal z| ≤ 1 := by
      have hnonneg := E.fReal_nonneg z
      have hle := E.fReal_le_one z
      rw [abs_of_nonneg hnonneg]
      exact hle
    have hclose' : |E.compactSmoothReal Q z - E.fReal z| ≤ κ := by
      simpa [abs_sub_comm] using hclose z
    calc
      |E.compactSmoothReal Q z|
          = |(E.compactSmoothReal Q z - E.fReal z) + E.fReal z| := by ring_nf
      _ ≤ |E.compactSmoothReal Q z - E.fReal z| + |E.fReal z| := abs_add_le _ _
      _ ≤ κ + 1 := add_le_add hclose' hf_abs_one
      _ ≤ 2 := by linarith
  have hdiff :=
    continuousCliqueDensity_lipschitz_sup_two_pow
      E.haar ℓ
      (E.fReal_continuous E.summable_gCoeff).measurable
      (E.compactSmoothReal_continuous Q).measurable
      hf_abs hs_abs hκ_nonneg hclose
  have hlow :
      continuousCliqueDensity E.haar ℓ E.fReal -
        continuousCliqueDensity E.haar ℓ (E.compactSmoothReal Q) ≤ C := by
    exact (le_abs_self _).trans (by simpa [C] using hdiff)
  have htarget :
      continuousCliqueDensity E.haar ℓ E.fReal - C ≤
        continuousCliqueDensity E.haar ℓ (E.compactSmoothReal Q) := by
    linarith
  simpa [C] using htarget

theorem exists_compactSmoothReal_cliqueDensity_pos
    (E : CayleyExtraction S) (hℓ : 2 ≤ ℓ) (hη : 0 < η) :
    ∃ Q : Finset E.Group, Q ≠ ∅ ∧
      0 < continuousCliqueDensity E.haar ℓ (E.compactSmoothReal Q) := by
  classical
  let ρ : ℝ := continuousCliqueDensity E.haar ℓ E.fReal
  have hρ_pos : 0 < ρ := by
    dsimp [ρ]
    exact E.compact_limit_cliqueDensity_pos hℓ hη
  let edgeCount : ℝ := ((continuousCliqueEdgePairs ℓ).card : ℝ)
  let P : ℝ := (2 : ℝ) ^ (continuousCliqueEdgePairs ℓ).card
  let A : ℝ := (edgeCount + 1) * (P + 1)
  have hedge_nonneg : 0 ≤ edgeCount := by
    dsimp [edgeCount]
    exact Nat.cast_nonneg _
  have hP_nonneg : 0 ≤ P := by
    dsimp [P]
    positivity
  have hA_pos : 0 < A := by
    dsimp [A]
    nlinarith
  let κ : ℝ := min 1 (ρ / (2 * A))
  have hκ_pos : 0 < κ := by
    dsimp [κ]
    exact lt_min zero_lt_one (div_pos hρ_pos (mul_pos two_pos hA_pos))
  have hκ_nonneg : 0 ≤ κ := le_of_lt hκ_pos
  have hκ_le_one : κ ≤ 1 := by
    dsimp [κ]
    exact min_le_left _ _
  obtain ⟨Q, hQ, hclose₀⟩ := E.exists_compactSmoothReal_uniform_close hκ_pos
  have hclose : ∀ z : E.CompactAddDual,
      |E.fReal z - E.compactSmoothReal Q z| ≤ κ := by
    intro z
    simpa [abs_sub_comm] using hclose₀ z
  have hκA_le : κ * A ≤ ρ / 2 := by
    have hκ_le : κ ≤ ρ / (2 * A) := by
      dsimp [κ]
      exact min_le_right _ _
    calc
      κ * A ≤ (ρ / (2 * A)) * A :=
        mul_le_mul_of_nonneg_right hκ_le (le_of_lt hA_pos)
      _ = ρ / 2 := by
        field_simp [ne_of_gt hA_pos]
  have hedgeP_le_A : edgeCount * P ≤ A := by
    dsimp [A]
    nlinarith
  have hmargin :
      (edgeCount * κ) * P < ρ := by
    have hC_le : (edgeCount * κ) * P ≤ κ * A := by
      have h := mul_le_mul_of_nonneg_left hedgeP_le_A hκ_nonneg
      nlinarith
    nlinarith
  refine ⟨Q, hQ, ?_⟩
  exact E.compactSmoothReal_cliqueDensity_pos_of_close Q
    hκ_nonneg hκ_le_one hclose (by
      simpa [edgeCount, P, ρ] using hmargin)

theorem exists_compactSmoothReal_cliqueDensity_pos_and_fejerPairCoeffLowerBound
    (E : CayleyExtraction S) (hℓ : 2 ≤ ℓ) (hη : 0 < η)
    (Bextra : Finset E.Group) {Mlarge : ℝ} (hMlarge : 0 < Mlarge) :
    ∃ Q : Finset E.Group, Q ≠ ∅ ∧
      E.FejerPairCoeffLowerBound Q Bextra Mlarge ∧
      0 < continuousCliqueDensity E.haar ℓ (E.compactSmoothReal Q) ∧
      continuousCliqueDensity E.haar ℓ E.fReal / 2 ≤
        continuousCliqueDensity E.haar ℓ (E.compactSmoothReal Q) := by
  classical
  let ρ : ℝ := continuousCliqueDensity E.haar ℓ E.fReal
  have hρ_pos : 0 < ρ := by
    dsimp [ρ]
    exact E.compact_limit_cliqueDensity_pos hℓ hη
  let edgeCount : ℝ := ((continuousCliqueEdgePairs ℓ).card : ℝ)
  let P : ℝ := (2 : ℝ) ^ (continuousCliqueEdgePairs ℓ).card
  let A : ℝ := (edgeCount + 1) * (P + 1)
  have hedge_nonneg : 0 ≤ edgeCount := by
    dsimp [edgeCount]
    exact Nat.cast_nonneg _
  have hP_nonneg : 0 ≤ P := by
    dsimp [P]
    positivity
  have hA_pos : 0 < A := by
    dsimp [A]
    nlinarith
  let κ : ℝ := min 1 (ρ / (2 * A))
  have hκ_pos : 0 < κ := by
    dsimp [κ]
    exact lt_min zero_lt_one (div_pos hρ_pos (mul_pos two_pos hA_pos))
  have hκ_nonneg : 0 ≤ κ := le_of_lt hκ_pos
  have hκ_le_one : κ ≤ 1 := by
    dsimp [κ]
    exact min_le_left _ _
  obtain ⟨Q, hQ, hBextra, hclose₀⟩ :=
    E.exists_compactSmoothReal_uniform_close_and_fejerPairCoeffLowerBound
      Bextra hκ_pos hMlarge
  have hclose : ∀ z : E.CompactAddDual,
      |E.fReal z - E.compactSmoothReal Q z| ≤ κ := by
    intro z
    simpa [abs_sub_comm] using hclose₀ z
  have hκA_le : κ * A ≤ ρ / 2 := by
    have hκ_le : κ ≤ ρ / (2 * A) := by
      dsimp [κ]
      exact min_le_right _ _
    calc
      κ * A ≤ (ρ / (2 * A)) * A :=
        mul_le_mul_of_nonneg_right hκ_le (le_of_lt hA_pos)
      _ = ρ / 2 := by
        field_simp [ne_of_gt hA_pos]
  have hedgeP_le_A : edgeCount * P ≤ A := by
    dsimp [A]
    nlinarith
  have hmargin :
      (edgeCount * κ) * P < ρ := by
    have hC_le : (edgeCount * κ) * P ≤ κ * A := by
      have h := mul_le_mul_of_nonneg_left hedgeP_le_A hκ_nonneg
      nlinarith
    nlinarith
  have hge :
      continuousCliqueDensity E.haar ℓ E.fReal / 2 ≤
        continuousCliqueDensity E.haar ℓ (E.compactSmoothReal Q) := by
    have hlower :=
      E.compactSmoothReal_cliqueDensity_ge_sub_error_of_close Q
        hκ_nonneg hκ_le_one hclose
    have hC_le :
        (((continuousCliqueEdgePairs ℓ).card : ℝ) * κ) *
            (2 : ℝ) ^ (continuousCliqueEdgePairs ℓ).card ≤
          ρ / 2 := by
      have hC_le_A : (edgeCount * κ) * P ≤ κ * A := by
        have h := mul_le_mul_of_nonneg_left hedgeP_le_A hκ_nonneg
        nlinarith
      simpa [edgeCount, P] using hC_le_A.trans hκA_le
    dsimp [ρ] at hC_le
    linarith
  have hpos :
      0 < continuousCliqueDensity E.haar ℓ (E.compactSmoothReal Q) :=
    lt_of_lt_of_le (half_pos hρ_pos) (by simpa [ρ] using hge)
  refine ⟨Q, hQ, hBextra, hpos, hge⟩

end CayleyExtraction

end

end Erdos42.CompactCayley


/-! =============================================================
    Section from: Erdos/P42/CompactCayley/SmoothDensityConvergence.lean
    ============================================================= -/

/-
Erdős Problem 42 — finite-to-compact density convergence for smoothed kernels.

This file contains the finite edge-frequency bookkeeping needed to turn the
fixed-`Q` finite Fejér-smoothed clique density into a compact Haar integral.
-/


namespace Erdos42.CompactCayley

open Filter MeasureTheory
open scoped BigOperators Topology

noncomputable section

namespace CayleyExtraction

variable {ℓ : ℕ} {η : ℝ} {S : CayleyCounterSeq ℓ η}

/-- The finite type of oriented clique edges. -/
abbrev CliqueEdgeIndex (M : ℕ) : Type :=
  {e : Fin M × Fin M // e ∈ cliqueEdgePairs M}

/-- Extend an assignment on clique edges by zero off the clique-edge set. -/
noncomputable def extendCliqueEdgeAssignment
    (E : CayleyExtraction S) {M : ℕ}
    (ω : CliqueEdgeIndex M → E.Group) :
    Fin M × Fin M → E.Group :=
  fun e => if h : e ∈ cliqueEdgePairs M then ω ⟨e, h⟩ else 0

@[simp]
lemma extendCliqueEdgeAssignment_apply_mem
    (E : CayleyExtraction S) {M : ℕ}
    (ω : CliqueEdgeIndex M → E.Group) (e : Fin M × Fin M)
    (he : e ∈ cliqueEdgePairs M) :
    E.extendCliqueEdgeAssignment ω e = ω ⟨e, he⟩ := by
  simp [extendCliqueEdgeAssignment, he]

/-- Coefficient product attached to an assignment of frequencies to the clique
edges. -/
noncomputable def cliqueEdgeAssignmentCoeff
    (E : CayleyExtraction S) {M : ℕ}
    (P : E.TrigPoly) (ω : CliqueEdgeIndex M → E.Group) : ℂ :=
  ∏ e : CliqueEdgeIndex M, P (ω e)

lemma TrigPoly.evalFinite_eq_sum_support
    (E : CayleyExtraction S) (P : E.TrigPoly) (n : ℕ)
    (x : ZMod (S.p (E.φ n))) [NeZero (S.p (E.φ n))] :
    TrigPoly.evalFinite P n x =
      ∑ γ ∈ P.support,
        P γ * ZMod.stdAddChar (-(E.lift n γ * x)) := by
  classical
  unfold TrigPoly.evalFinite
  rw [Finsupp.sum_of_support_subset
    (f := P) (s := P.support) (by intro γ hγ; exact hγ)]
  intro γ _hγ
  simp

lemma TrigPoly.evalFinite_eq_sum_of_support_subset
    (E : CayleyExtraction S) (P : E.TrigPoly) (n : ℕ)
    (A : Finset E.Group) (hP : P.support ⊆ A)
    (x : ZMod (S.p (E.φ n))) [NeZero (S.p (E.φ n))] :
    TrigPoly.evalFinite P n x =
      ∑ γ ∈ A, P γ * ZMod.stdAddChar (-(E.lift n γ * x)) := by
  classical
  unfold TrigPoly.evalFinite
  rw [Finsupp.sum_of_support_subset (f := P) (s := A) hP]
  intro γ _hγ
  simp

lemma TrigPoly.evalAdd_eq_sum_support
    (E : CayleyExtraction S) (P : E.TrigPoly)
    (z : E.CompactAddDual) :
    TrigPoly.evalAdd P z =
      ∑ γ ∈ P.support, P γ * E.addCharacterValue z γ := by
  classical
  unfold TrigPoly.evalAdd
  rw [Finsupp.sum_of_support_subset
    (f := P) (s := P.support) (by intro γ hγ; exact hγ)]
  intro γ _hγ
  simp

lemma TrigPoly.evalAdd_eq_sum_of_support_subset
    (E : CayleyExtraction S) (P : E.TrigPoly)
    (A : Finset E.Group) (hP : P.support ⊆ A)
    (z : E.CompactAddDual) :
    TrigPoly.evalAdd P z =
      ∑ γ ∈ A, P γ * E.addCharacterValue z γ := by
  classical
  unfold TrigPoly.evalAdd
  rw [Finsupp.sum_of_support_subset (f := P) (s := A) hP]
  intro γ _hγ
  simp

lemma addCharacterValue_sum
    (E : CayleyExtraction S) {ι : Type*} (s : Finset ι)
    (z : E.CompactAddDual) (f : ι → E.Group) :
    E.addCharacterValue z (∑ i ∈ s, f i) =
      ∏ i ∈ s, E.addCharacterValue z (f i) := by
  classical
  refine Finset.induction_on s ?base ?step
  · simp
  · intro a s ha ih
    rw [Finset.sum_insert ha, Finset.prod_insert ha]
    rw [E.addCharacterValue_add, ih]

lemma addCharacterValue_sum_univ
    (E : CayleyExtraction S) {ι : Type*} [Fintype ι]
    (z : E.CompactAddDual) (f : ι → E.Group) :
    E.addCharacterValue z (∑ i, f i) =
      ∏ i, E.addCharacterValue z (f i) := by
  simpa using E.addCharacterValue_sum (Finset.univ : Finset ι) z f

lemma stdAddChar_neg_sum_mul
    {p : ℕ} [NeZero p] {ι : Type*} (s : Finset ι)
    (f : ι → ZMod p) (x : ZMod p) :
    ZMod.stdAddChar (-((∑ i ∈ s, f i) * x)) =
      ∏ i ∈ s, ZMod.stdAddChar (-(f i * x)) := by
  classical
  refine Finset.induction_on s ?base ?step
  · simp
  · intro a s ha ih
    rw [Finset.sum_insert ha, Finset.prod_insert ha]
    rw [← ih]
    rw [← ZMod.stdAddChar.map_add_eq_mul]
    congr 1
    ring

lemma stdAddChar_sum
    {p : ℕ} [NeZero p] {ι : Type*} (s : Finset ι)
    (f : ι → ZMod p) :
    ZMod.stdAddChar (∑ i ∈ s, f i) =
      ∏ i ∈ s, ZMod.stdAddChar (f i) := by
  classical
  refine Finset.induction_on s ?base ?step
  · simp
  · intro a s ha ih
    rw [Finset.sum_insert ha, Finset.prod_insert ha]
    rw [ZMod.stdAddChar.map_add_eq_mul, ih]

lemma stdAddChar_sum_univ
    {p : ℕ} [NeZero p] {ι : Type*} [Fintype ι]
    (f : ι → ZMod p) :
    ZMod.stdAddChar (∑ i, f i) =
      ∏ i, ZMod.stdAddChar (f i) := by
  simpa using stdAddChar_sum (Finset.univ : Finset ι) f

lemma stdAddChar_neg_sum_univ_mul
    {p : ℕ} [NeZero p] {ι : Type*} [Fintype ι]
    (f : ι → ZMod p) (x : ZMod p) :
    ZMod.stdAddChar (-((∑ i, f i) * x)) =
      ∏ i, ZMod.stdAddChar (-(f i * x)) := by
  simpa using stdAddChar_neg_sum_mul (Finset.univ : Finset ι) f x

lemma finitePiAverage_prod_zmod {p M : ℕ} [NeZero p]
    (φ : Fin M → ZMod p → ℂ) :
    ((Fintype.card (Fin M → ZMod p) : ℂ)⁻¹) *
        ∑ x : Fin M → ZMod p, ∏ i : Fin M, φ i (x i) =
      ∏ i : Fin M, avgZMod (φ i) := by
  classical
  have hcard_nat : Fintype.card (Fin M → ZMod p) = p ^ M := by
    simp [ZMod.card]
  have hcard_complex : (Fintype.card (Fin M → ZMod p) : ℂ) = (p : ℂ) ^ M := by
    rw [hcard_nat]
    norm_cast
  unfold avgZMod
  rw [hcard_complex]
  rw [Finset.prod_mul_distrib]
  rw [Finset.prod_univ_sum]
  rw [Fintype.piFinset_univ]
  simp

lemma finitePiAverage_prod_stdAddChar_neg_mul
    {p M : ℕ} [Fact p.Prime] [NeZero p]
    (β : Fin M → ZMod p) :
    ((Fintype.card (Fin M → ZMod p) : ℂ)⁻¹) *
        ∑ x : Fin M → ZMod p,
          ∏ i : Fin M, ZMod.stdAddChar (-(β i * x i)) =
      ∏ i : Fin M, if β i = 0 then (1 : ℂ) else 0 := by
  rw [show
      ((Fintype.card (Fin M → ZMod p) : ℂ)⁻¹) *
          ∑ x : Fin M → ZMod p,
            ∏ i : Fin M, ZMod.stdAddChar (-(β i * x i)) =
        ∏ i : Fin M,
          avgZMod (fun x : ZMod p => ZMod.stdAddChar (-(β i * x))) by
        simpa using
          finitePiAverage_prod_zmod
            (p := p) (M := M)
            (fun i x => ZMod.stdAddChar (-(β i * x)))]
  refine Finset.prod_congr rfl ?_
  intro i _hi
  exact avgZMod_stdAddChar_neg_mul_eq_ite (β i)

lemma finitePiAverage_prod_stdAddChar_neg_mul_eq_if
    {p M : ℕ} [Fact p.Prime] [NeZero p]
    (β : Fin M → ZMod p) :
    ((Fintype.card (Fin M → ZMod p) : ℂ)⁻¹) *
        ∑ x : Fin M → ZMod p,
          ∏ i : Fin M, ZMod.stdAddChar (-(β i * x i)) =
      if (∀ i : Fin M, β i = 0) then 1 else 0 := by
  rw [finitePiAverage_prod_stdAddChar_neg_mul β]
  by_cases hβ : ∀ i : Fin M, β i = 0
  · simp [hβ]
  · rw [if_neg hβ]
    push Not at hβ
    rcases hβ with ⟨i, hi⟩
    exact Finset.prod_eq_zero (by simp : i ∈ (Finset.univ : Finset (Fin M)))
      (by simp [hi])

/-- Net finite frequency at a vertex for an arbitrary finite set of oriented
edges. The compact-Cayley clique balance is this construction specialized to
`cliqueEdgePairs`. -/
noncomputable def finiteEdgeFrequencyBalanceOn
    {p M : ℕ} (s : Finset (Fin M × Fin M))
    (r : Fin M × Fin M → ZMod p) (i : Fin M) : ZMod p :=
  (∑ e ∈ s.filter (fun e => e.1 = i), r e) -
  (∑ e ∈ s.filter (fun e => e.2 = i), r e)

lemma sum_vertex_outgoing_eq_edge_sum
    {p M : ℕ} (s : Finset (Fin M × Fin M))
    (r : Fin M × Fin M → ZMod p) (x : Fin M → ZMod p) :
    (∑ i : Fin M, (∑ e ∈ s, if e.1 = i then r e else 0) * x i) =
      ∑ e ∈ s, r e * x e.1 := by
  classical
  calc
    (∑ i : Fin M, (∑ e ∈ s, if e.1 = i then r e else 0) * x i)
        = ∑ i : Fin M, ∑ e ∈ s, (if e.1 = i then r e else 0) * x i := by
          simp [Finset.sum_mul]
    _ = ∑ e ∈ s, ∑ i : Fin M, (if e.1 = i then r e else 0) * x i := by
          rw [Finset.sum_comm]
    _ = ∑ e ∈ s, r e * x e.1 := by
          refine Finset.sum_congr rfl ?_
          intro e _he
          rw [Finset.sum_eq_single e.1]
          · simp
          · intro i _hi hne
            simp [Ne.symm hne]
          · intro hnot
            exact (hnot (by simp)).elim

lemma sum_vertex_incoming_eq_edge_sum
    {p M : ℕ} (s : Finset (Fin M × Fin M))
    (r : Fin M × Fin M → ZMod p) (x : Fin M → ZMod p) :
    (∑ i : Fin M, (∑ e ∈ s, if e.2 = i then r e else 0) * x i) =
      ∑ e ∈ s, r e * x e.2 := by
  classical
  calc
    (∑ i : Fin M, (∑ e ∈ s, if e.2 = i then r e else 0) * x i)
        = ∑ i : Fin M, ∑ e ∈ s, (if e.2 = i then r e else 0) * x i := by
          simp [Finset.sum_mul]
    _ = ∑ e ∈ s, ∑ i : Fin M, (if e.2 = i then r e else 0) * x i := by
          rw [Finset.sum_comm]
    _ = ∑ e ∈ s, r e * x e.2 := by
          refine Finset.sum_congr rfl ?_
          intro e _he
          rw [Finset.sum_eq_single e.2]
          · simp
          · intro i _hi hne
            simp [Ne.symm hne]
          · intro hnot
            exact (hnot (by simp)).elim

lemma finiteEdgeFrequencyBalanceOn_exponent_identity
    {p M : ℕ} (s : Finset (Fin M × Fin M))
    (r : Fin M × Fin M → ZMod p) (x : Fin M → ZMod p) :
    (∑ e ∈ s, -(r e * (x e.1 - x e.2))) =
      ∑ i : Fin M, -(finiteEdgeFrequencyBalanceOn s r i * x i) := by
  classical
  simp only [Finset.sum_neg_distrib, neg_inj]
  unfold finiteEdgeFrequencyBalanceOn
  simp only [Finset.sum_filter]
  rw [show
      (∑ i : Fin M,
        ((∑ e ∈ s, if e.1 = i then r e else 0) -
          (∑ e ∈ s, if e.2 = i then r e else 0)) * x i) =
        (∑ i : Fin M, (∑ e ∈ s, if e.1 = i then r e else 0) * x i) -
          (∑ i : Fin M, (∑ e ∈ s, if e.2 = i then r e else 0) * x i) by
        simp [sub_mul, Finset.sum_sub_distrib]]
  rw [sum_vertex_outgoing_eq_edge_sum s r x,
    sum_vertex_incoming_eq_edge_sum s r x]
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl ?_
  intro e _he
  ring

lemma prod_stdAddChar_edge_eq_prod_balance
    {p M : ℕ} [NeZero p] (s : Finset (Fin M × Fin M))
    (r : Fin M × Fin M → ZMod p) (x : Fin M → ZMod p) :
    (∏ e ∈ s, ZMod.stdAddChar (-(r e * (x e.1 - x e.2)))) =
      ∏ i : Fin M,
        ZMod.stdAddChar (-(finiteEdgeFrequencyBalanceOn s r i * x i)) := by
  rw [← stdAddChar_sum s (fun e => -(r e * (x e.1 - x e.2)))]
  rw [← stdAddChar_sum_univ
    (fun i : Fin M => -(finiteEdgeFrequencyBalanceOn s r i * x i))]
  rw [finiteEdgeFrequencyBalanceOn_exponent_identity]

lemma prod_vertex_outgoing_eq_edge_prod
    {M : ℕ} {A : Type*} [CommMonoid A]
    (s : Finset (Fin M × Fin M)) (F : (Fin M × Fin M) → Fin M → A) :
    (∏ i : Fin M, ∏ e ∈ s, if e.1 = i then F e i else 1) =
      ∏ e ∈ s, F e e.1 := by
  classical
  calc
    (∏ i : Fin M, ∏ e ∈ s, if e.1 = i then F e i else 1)
        = ∏ e ∈ s, ∏ i : Fin M, if e.1 = i then F e i else 1 := by
          rw [Finset.prod_comm]
    _ = ∏ e ∈ s, F e e.1 := by
          refine Finset.prod_congr rfl ?_
          intro e _he
          rw [Finset.prod_eq_single e.1]
          · simp
          · intro i _hi hne
            simp [Ne.symm hne]
          · intro hnot
            exact (hnot (by simp)).elim

lemma prod_vertex_incoming_eq_edge_prod
    {M : ℕ} {A : Type*} [CommMonoid A]
    (s : Finset (Fin M × Fin M)) (F : (Fin M × Fin M) → Fin M → A) :
    (∏ i : Fin M, ∏ e ∈ s, if e.2 = i then F e i else 1) =
      ∏ e ∈ s, F e e.2 := by
  classical
  calc
    (∏ i : Fin M, ∏ e ∈ s, if e.2 = i then F e i else 1)
        = ∏ e ∈ s, ∏ i : Fin M, if e.2 = i then F e i else 1 := by
          rw [Finset.prod_comm]
    _ = ∏ e ∈ s, F e e.2 := by
          refine Finset.prod_congr rfl ?_
          intro e _he
          rw [Finset.prod_eq_single e.2]
          · simp
          · intro i _hi hne
            simp [Ne.symm hne]
          · intro hnot
            exact (hnot (by simp)).elim

lemma compactPiIntegral_prod_addCharacterValue
    (E : CayleyExtraction S) {M : ℕ}
    (β : Fin M → E.Group) :
    (∫ x : Fin M → E.CompactAddDual,
        ∏ i : Fin M, E.addCharacterValue (x i) (β i)
        ∂Measure.pi (fun _ : Fin M => E.haar)) =
      ∏ i : Fin M, if β i = 0 then (1 : ℂ) else 0 := by
  calc
    (∫ x : Fin M → E.CompactAddDual,
        ∏ i : Fin M, E.addCharacterValue (x i) (β i)
        ∂Measure.pi (fun _ : Fin M => E.haar)) =
      ∏ i : Fin M, ∫ z : E.CompactAddDual, E.addCharacterValue z (β i) ∂E.haar := by
        simpa using
          (MeasureTheory.integral_fintype_prod_eq_prod
            (μ := fun _ : Fin M => E.haar)
            (f := fun i (z : E.CompactAddDual) => E.addCharacterValue z (β i)))
    _ = ∏ i : Fin M, if β i = 0 then (1 : ℂ) else 0 := by
      refine Finset.prod_congr rfl ?_
      intro i _hi
      exact E.integral_addCharacterValue (β i)

lemma compactPiIntegral_prod_addCharacterValue_eq_if
    (E : CayleyExtraction S) {M : ℕ}
    (β : Fin M → E.Group) :
    (∫ x : Fin M → E.CompactAddDual,
        ∏ i : Fin M, E.addCharacterValue (x i) (β i)
        ∂Measure.pi (fun _ : Fin M => E.haar)) =
      if (∀ i : Fin M, β i = 0) then 1 else 0 := by
  rw [E.compactPiIntegral_prod_addCharacterValue β]
  by_cases hβ : ∀ i : Fin M, β i = 0
  · simp [hβ]
  · rw [if_neg hβ]
    push Not at hβ
    rcases hβ with ⟨i, hi⟩
    exact Finset.prod_eq_zero (by simp : i ∈ (Finset.univ : Finset (Fin M)))
      (by simp [hi])

/-- Sum of edge frequencies leaving a vertex in the oriented clique edge set. -/
noncomputable def cliqueOutgoingFreq
    (E : CayleyExtraction S) {M : ℕ}
    (ω : Fin M × Fin M → E.Group) (i : Fin M) : E.Group :=
  ∑ e ∈ (cliqueEdgePairs M).filter (fun e => e.1 = i), ω e

/-- Sum of edge frequencies entering a vertex in the oriented clique edge set. -/
noncomputable def cliqueIncomingFreq
    (E : CayleyExtraction S) {M : ℕ}
    (ω : Fin M × Fin M → E.Group) (i : Fin M) : E.Group :=
  ∑ e ∈ (cliqueEdgePairs M).filter (fun e => e.2 = i), ω e

/-- Net compact frequency at a vertex after multiplying edge characters
`χ_γ(x_i - x_j)` over all oriented clique edges `i < j`. -/
noncomputable def cliqueFrequencyBalance
    (E : CayleyExtraction S) {M : ℕ}
    (ω : Fin M × Fin M → E.Group) (i : Fin M) : E.Group :=
  E.cliqueOutgoingFreq ω i - E.cliqueIncomingFreq ω i

/-- Finite cyclic lift of the vertex frequency balance attached to an
edge-frequency assignment. -/
noncomputable def finiteCliqueFrequencyBalance
    (E : CayleyExtraction S) {M : ℕ}
    (ω : Fin M × Fin M → E.Group) (n : ℕ) (i : Fin M) :
    ZMod (S.p (E.φ n)) :=
  (∑ e ∈ (cliqueEdgePairs M).filter (fun e => e.1 = i),
    E.lift n (ω e)) -
  (∑ e ∈ (cliqueEdgePairs M).filter (fun e => e.2 = i),
    E.lift n (ω e))

lemma finiteLift_cliqueOutgoingFreq_eventually_eq
    (E : CayleyExtraction S) {M : ℕ}
    (ω : Fin M × Fin M → E.Group) (i : Fin M) :
    ∀ᶠ n in atTop,
      E.lift n (E.cliqueOutgoingFreq ω i) =
        ∑ e ∈ (cliqueEdgePairs M).filter (fun e => e.1 = i),
          E.lift n (ω e) := by
  let s : Finset (Fin M × Fin M) :=
    (cliqueEdgePairs M).filter (fun e => e.1 = i)
  change
    ∀ᶠ n in atTop,
      E.data.finiteLift n (∑ e ∈ s, ω e) =
        ∑ e ∈ s, E.data.finiteLift n (ω e)
  exact E.data.finiteLift_sum_eventually_eq s ω

lemma finiteLift_cliqueIncomingFreq_eventually_eq
    (E : CayleyExtraction S) {M : ℕ}
    (ω : Fin M × Fin M → E.Group) (i : Fin M) :
    ∀ᶠ n in atTop,
      E.lift n (E.cliqueIncomingFreq ω i) =
        ∑ e ∈ (cliqueEdgePairs M).filter (fun e => e.2 = i),
          E.lift n (ω e) := by
  let s : Finset (Fin M × Fin M) :=
    (cliqueEdgePairs M).filter (fun e => e.2 = i)
  change
    ∀ᶠ n in atTop,
      E.data.finiteLift n (∑ e ∈ s, ω e) =
        ∑ e ∈ s, E.data.finiteLift n (ω e)
  exact E.data.finiteLift_sum_eventually_eq s ω

lemma finiteLift_cliqueFrequencyBalance_eventually_eq
    (E : CayleyExtraction S) {M : ℕ}
    (ω : Fin M × Fin M → E.Group) (i : Fin M) :
    ∀ᶠ n in atTop,
      E.lift n (E.cliqueFrequencyBalance ω i) =
        E.finiteCliqueFrequencyBalance ω n i := by
  filter_upwards
    [E.data.finiteLift_sub_eventually_eq
      (E.cliqueOutgoingFreq ω i) (E.cliqueIncomingFreq ω i),
      E.finiteLift_cliqueOutgoingFreq_eventually_eq ω i,
      E.finiteLift_cliqueIncomingFreq_eventually_eq ω i] with n hsub hout hin
  unfold finiteCliqueFrequencyBalance cliqueFrequencyBalance lift at *
  rw [hsub, hout, hin]
  rfl

lemma finiteLift_cliqueFrequencyBalance_all_eventually_eq
    (E : CayleyExtraction S) {M : ℕ}
    (ω : Fin M × Fin M → E.Group) :
    ∀ᶠ n in atTop, ∀ i : Fin M,
      E.lift n (E.cliqueFrequencyBalance ω i) =
        E.finiteCliqueFrequencyBalance ω n i := by
  have h :
      ∀ᶠ n in atTop, ∀ i ∈ (Finset.univ : Finset (Fin M)),
        E.lift n (E.cliqueFrequencyBalance ω i) =
          E.finiteCliqueFrequencyBalance ω n i := by
    rw [(Finset.univ : Finset (Fin M)).eventually_all]
    intro i _hi
    exact E.finiteLift_cliqueFrequencyBalance_eventually_eq ω i
  filter_upwards [h] with n hn i
  exact hn i (by simp)

lemma finiteLift_cliqueFrequencyBalance_zero_iff_eventually
    (E : CayleyExtraction S) {M : ℕ}
    (ω : Fin M × Fin M → E.Group) :
    ∀ᶠ n in atTop, ∀ i : Fin M,
      E.lift n (E.cliqueFrequencyBalance ω i) = 0 ↔
        E.cliqueFrequencyBalance ω i = 0 := by
  have h :
      ∀ᶠ n in atTop, ∀ i ∈ (Finset.univ : Finset (Fin M)),
        E.lift n (E.cliqueFrequencyBalance ω i) = 0 ↔
          E.cliqueFrequencyBalance ω i = 0 := by
    rw [(Finset.univ : Finset (Fin M)).eventually_all]
    intro i _hi
    by_cases hbal : E.cliqueFrequencyBalance ω i = 0
    · filter_upwards [E.data.finiteLift_zero_eventually_eq_zero] with n hzero
      constructor
      · intro _h
        exact hbal
      · intro _h
        rw [hbal]
        change E.data.finiteLift n (0 : E.data.Group) = 0
        exact hzero
    · filter_upwards [E.finiteLift_eventually_ne_zero hbal] with n hn
      constructor
      · intro hzero
        exact (hn hzero).elim
      · intro h
        exact (hbal h).elim
  filter_upwards [h] with n hn i
  exact hn i (by simp)

lemma finiteCliqueFrequencyBalance_all_zero_iff_eventually
    (E : CayleyExtraction S) {M : ℕ}
    (ω : Fin M × Fin M → E.Group) :
    ∀ᶠ n in atTop,
      ((∀ i : Fin M, E.finiteCliqueFrequencyBalance ω n i = 0) ↔
        ∀ i : Fin M, E.cliqueFrequencyBalance ω i = 0) := by
  filter_upwards
    [E.finiteLift_cliqueFrequencyBalance_all_eventually_eq ω,
      E.finiteLift_cliqueFrequencyBalance_zero_iff_eventually ω] with n heq hzero
  constructor
  · intro hfin i
    exact (hzero i).mp (by rw [heq i, hfin i])
  · intro hcompact i
    have hlift_zero : E.lift n (E.cliqueFrequencyBalance ω i) = 0 :=
      (hzero i).mpr (hcompact i)
    rwa [heq i] at hlift_zero

lemma finiteCliqueFrequencyBalance_eq_finiteEdgeFrequencyBalanceOn
    (E : CayleyExtraction S) {M : ℕ}
    (ω : Fin M × Fin M → E.Group) (n : ℕ) (i : Fin M) :
    E.finiteCliqueFrequencyBalance ω n i =
      finiteEdgeFrequencyBalanceOn (cliqueEdgePairs M)
        (fun e => E.lift n (ω e)) i := by
  rfl

lemma prod_stdAddChar_cliqueEdge_eq_prod_finiteCliqueBalance
    (E : CayleyExtraction S) {M : ℕ}
    (ω : Fin M × Fin M → E.Group) (n : ℕ)
    (x : Fin M → ZMod (S.p (E.φ n))) [NeZero (S.p (E.φ n))] :
    (∏ e ∈ cliqueEdgePairs M,
        ZMod.stdAddChar
          (-(E.lift n (ω e) * (x e.1 - x e.2)))) =
      ∏ i : Fin M,
        ZMod.stdAddChar (-(E.finiteCliqueFrequencyBalance ω n i * x i)) := by
  simpa [E.finiteCliqueFrequencyBalance_eq_finiteEdgeFrequencyBalanceOn ω n] using
    prod_stdAddChar_edge_eq_prod_balance (cliqueEdgePairs M)
      (fun e => E.lift n (ω e)) x

lemma finiteCliqueAssignmentAverage_eq_if
    (E : CayleyExtraction S) {M : ℕ}
    (ω : Fin M × Fin M → E.Group) (n : ℕ)
    [Fact (S.p (E.φ n)).Prime] [NeZero (S.p (E.φ n))] :
    ((Fintype.card (Fin M → ZMod (S.p (E.φ n))) : ℂ)⁻¹) *
        ∑ x : Fin M → ZMod (S.p (E.φ n)),
          ∏ e ∈ cliqueEdgePairs M,
            ZMod.stdAddChar
              (-(E.lift n (ω e) * (x e.1 - x e.2))) =
      if (∀ i : Fin M, E.finiteCliqueFrequencyBalance ω n i = 0)
      then 1 else 0 := by
  rw [show
      ((Fintype.card (Fin M → ZMod (S.p (E.φ n))) : ℂ)⁻¹) *
          ∑ x : Fin M → ZMod (S.p (E.φ n)),
            ∏ e ∈ cliqueEdgePairs M,
              ZMod.stdAddChar
                (-(E.lift n (ω e) * (x e.1 - x e.2))) =
        ((Fintype.card (Fin M → ZMod (S.p (E.φ n))) : ℂ)⁻¹) *
          ∑ x : Fin M → ZMod (S.p (E.φ n)),
            ∏ i : Fin M,
              ZMod.stdAddChar
                (-(E.finiteCliqueFrequencyBalance ω n i * x i)) by
        congr 1
        refine Finset.sum_congr rfl ?_
        intro x _hx
        exact E.prod_stdAddChar_cliqueEdge_eq_prod_finiteCliqueBalance ω n x]
  exact finitePiAverage_prod_stdAddChar_neg_mul_eq_if
    (fun i : Fin M => E.finiteCliqueFrequencyBalance ω n i)

lemma finiteCliqueKernelWeight_evalFinite_eq_sum_edgeAssignments
    (E : CayleyExtraction S) {M : ℕ}
    (P : E.TrigPoly) (n : ℕ)
    (x : Fin M → ZMod (S.p (E.φ n))) [NeZero (S.p (E.φ n))] :
    finiteCliqueKernelWeight (ℓ := M)
        (fun z : ZMod (S.p (E.φ n)) => TrigPoly.evalFinite P n z) x =
      ∑ ω ∈ Fintype.piFinset (fun _ : CliqueEdgeIndex M => P.support),
        E.cliqueEdgeAssignmentCoeff P ω *
          ∏ e : CliqueEdgeIndex M,
            ZMod.stdAddChar
              (-(E.lift n (ω e) * (x e.1.1 - x e.1.2))) := by
  classical
  unfold finiteCliqueKernelWeight
  rw [show
      (∏ e ∈ cliqueEdgePairs M,
          TrigPoly.evalFinite P n (x e.1 - x e.2)) =
        ∏ e : CliqueEdgeIndex M,
          TrigPoly.evalFinite P n (x e.1.1 - x e.1.2) by
        simpa [CliqueEdgeIndex] using
          (Finset.prod_attach (s := cliqueEdgePairs M)
            (f := fun e : Fin M × Fin M =>
              TrigPoly.evalFinite P n (x e.1 - x e.2))).symm]
  rw [show
      (∏ e : CliqueEdgeIndex M,
          TrigPoly.evalFinite P n (x e.1.1 - x e.1.2)) =
        ∏ e : CliqueEdgeIndex M,
          ∑ γ ∈ P.support,
            P γ * ZMod.stdAddChar
              (-(E.lift n γ * (x e.1.1 - x e.1.2))) by
        refine Finset.prod_congr rfl ?_
        intro e _he
        exact TrigPoly.evalFinite_eq_sum_support E P n
          (x e.1.1 - x e.1.2)]
  rw [Finset.prod_univ_sum]
  refine Finset.sum_congr rfl ?_
  intro ω hω
  rw [Finset.prod_mul_distrib]
  rfl

lemma finiteCliqueKernelWeight_evalFinite_eq_sum_edgeAssignments_of_support_subset
    (E : CayleyExtraction S) {M : ℕ}
    (P : E.TrigPoly) (A : Finset E.Group) (hP : P.support ⊆ A)
    (n : ℕ)
    (x : Fin M → ZMod (S.p (E.φ n))) [NeZero (S.p (E.φ n))] :
    finiteCliqueKernelWeight (ℓ := M)
        (fun z : ZMod (S.p (E.φ n)) => TrigPoly.evalFinite P n z) x =
      ∑ ω ∈ Fintype.piFinset (fun _ : CliqueEdgeIndex M => A),
        E.cliqueEdgeAssignmentCoeff P ω *
          ∏ e : CliqueEdgeIndex M,
            ZMod.stdAddChar
              (-(E.lift n (ω e) * (x e.1.1 - x e.1.2))) := by
  classical
  unfold finiteCliqueKernelWeight
  rw [show
      (∏ e ∈ cliqueEdgePairs M,
          TrigPoly.evalFinite P n (x e.1 - x e.2)) =
        ∏ e : CliqueEdgeIndex M,
          TrigPoly.evalFinite P n (x e.1.1 - x e.1.2) by
        simpa [CliqueEdgeIndex] using
          (Finset.prod_attach (s := cliqueEdgePairs M)
            (f := fun e : Fin M × Fin M =>
              TrigPoly.evalFinite P n (x e.1 - x e.2))).symm]
  rw [show
      (∏ e : CliqueEdgeIndex M,
          TrigPoly.evalFinite P n (x e.1.1 - x e.1.2)) =
        ∏ e : CliqueEdgeIndex M,
          ∑ γ ∈ A,
            P γ * ZMod.stdAddChar
              (-(E.lift n γ * (x e.1.1 - x e.1.2))) by
        refine Finset.prod_congr rfl ?_
        intro e _he
        exact TrigPoly.evalFinite_eq_sum_of_support_subset E P n A hP
          (x e.1.1 - x e.1.2)]
  rw [Finset.prod_univ_sum]
  refine Finset.sum_congr rfl ?_
  intro ω _hω
  rw [Finset.prod_mul_distrib]
  rfl

lemma prod_stdAddChar_cliqueEdgeIndex_eq_extend
    (E : CayleyExtraction S) {M : ℕ}
    (ω : CliqueEdgeIndex M → E.Group) (n : ℕ)
    (x : Fin M → ZMod (S.p (E.φ n))) [NeZero (S.p (E.φ n))] :
    (∏ e : CliqueEdgeIndex M,
        ZMod.stdAddChar
          (-(E.lift n (ω e) * (x e.1.1 - x e.1.2)))) =
      ∏ e ∈ cliqueEdgePairs M,
        ZMod.stdAddChar
          (-(E.lift n (E.extendCliqueEdgeAssignment ω e) *
              (x e.1 - x e.2))) := by
  simpa [CliqueEdgeIndex] using
    (Finset.prod_attach (s := cliqueEdgePairs M)
      (f := fun e : Fin M × Fin M =>
        ZMod.stdAddChar
          (-(E.lift n (E.extendCliqueEdgeAssignment ω e) *
              (x e.1 - x e.2)))))

lemma finiteCliqueKernelDensity_evalFinite_eq_sum_edgeAssignments
    (E : CayleyExtraction S) {M : ℕ}
    (P : E.TrigPoly) (n : ℕ)
    [Fact (S.p (E.φ n)).Prime] [NeZero (S.p (E.φ n))] :
    finiteCliqueKernelDensity (p := S.p (E.φ n)) (ℓ := M)
        (fun z : ZMod (S.p (E.φ n)) => TrigPoly.evalFinite P n z) =
      ∑ ω ∈ Fintype.piFinset (fun _ : CliqueEdgeIndex M => P.support),
        E.cliqueEdgeAssignmentCoeff P ω *
          (if (∀ i : Fin M,
              E.finiteCliqueFrequencyBalance
                (E.extendCliqueEdgeAssignment ω) n i = 0)
            then 1 else 0) := by
  classical
  unfold finiteCliqueKernelDensity
  rw [show
      (∑ x : Fin M → ZMod (S.p (E.φ n)),
          finiteCliqueKernelWeight
            (fun z : ZMod (S.p (E.φ n)) =>
              TrigPoly.evalFinite P n z) x) =
        ∑ x : Fin M → ZMod (S.p (E.φ n)),
          ∑ ω ∈ Fintype.piFinset (fun _ : CliqueEdgeIndex M => P.support),
            E.cliqueEdgeAssignmentCoeff P ω *
              ∏ e : CliqueEdgeIndex M,
                ZMod.stdAddChar
                  (-(E.lift n (ω e) * (x e.1.1 - x e.1.2))) by
        refine Finset.sum_congr rfl ?_
        intro x _hx
        exact E.finiteCliqueKernelWeight_evalFinite_eq_sum_edgeAssignments P n x]
  rw [Finset.sum_comm]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl ?_
  intro ω hω
  rw [← Finset.mul_sum]
  rw [show
      ((Fintype.card (Fin M → ZMod (S.p (E.φ n))) : ℂ)⁻¹) *
          (E.cliqueEdgeAssignmentCoeff P ω *
            ∑ x : Fin M → ZMod (S.p (E.φ n)),
              ∏ e : CliqueEdgeIndex M,
                ZMod.stdAddChar
                  (-(E.lift n (ω e) * (x e.1.1 - x e.1.2)))) =
        E.cliqueEdgeAssignmentCoeff P ω *
          (((Fintype.card (Fin M → ZMod (S.p (E.φ n))) : ℂ)⁻¹) *
            ∑ x : Fin M → ZMod (S.p (E.φ n)),
              ∏ e : CliqueEdgeIndex M,
                ZMod.stdAddChar
                  (-(E.lift n (ω e) * (x e.1.1 - x e.1.2)))) by
        ring]
  rw [show
      ((Fintype.card (Fin M → ZMod (S.p (E.φ n))) : ℂ)⁻¹) *
          ∑ x : Fin M → ZMod (S.p (E.φ n)),
            ∏ e : CliqueEdgeIndex M,
              ZMod.stdAddChar
                (-(E.lift n (ω e) * (x e.1.1 - x e.1.2))) =
        ((Fintype.card (Fin M → ZMod (S.p (E.φ n))) : ℂ)⁻¹) *
          ∑ x : Fin M → ZMod (S.p (E.φ n)),
            ∏ e ∈ cliqueEdgePairs M,
              ZMod.stdAddChar
                (-(E.lift n (E.extendCliqueEdgeAssignment ω e) *
                    (x e.1 - x e.2))) by
        congr 1
        refine Finset.sum_congr rfl ?_
        intro x _hx
        exact E.prod_stdAddChar_cliqueEdgeIndex_eq_extend ω n x]
  rw [E.finiteCliqueAssignmentAverage_eq_if (E.extendCliqueEdgeAssignment ω) n]

lemma finiteCliqueKernelDensity_evalFinite_eq_sum_edgeAssignments_of_support_subset
    (E : CayleyExtraction S) {M : ℕ}
    (P : E.TrigPoly) (A : Finset E.Group) (hP : P.support ⊆ A) (n : ℕ)
    [Fact (S.p (E.φ n)).Prime] [NeZero (S.p (E.φ n))] :
    finiteCliqueKernelDensity (p := S.p (E.φ n)) (ℓ := M)
        (fun z : ZMod (S.p (E.φ n)) => TrigPoly.evalFinite P n z) =
      ∑ ω ∈ Fintype.piFinset (fun _ : CliqueEdgeIndex M => A),
        E.cliqueEdgeAssignmentCoeff P ω *
          (if (∀ i : Fin M,
              E.finiteCliqueFrequencyBalance
                (E.extendCliqueEdgeAssignment ω) n i = 0)
            then 1 else 0) := by
  classical
  unfold finiteCliqueKernelDensity
  rw [show
      (∑ x : Fin M → ZMod (S.p (E.φ n)),
          finiteCliqueKernelWeight
            (fun z : ZMod (S.p (E.φ n)) =>
              TrigPoly.evalFinite P n z) x) =
        ∑ x : Fin M → ZMod (S.p (E.φ n)),
          ∑ ω ∈ Fintype.piFinset (fun _ : CliqueEdgeIndex M => A),
            E.cliqueEdgeAssignmentCoeff P ω *
              ∏ e : CliqueEdgeIndex M,
                ZMod.stdAddChar
                  (-(E.lift n (ω e) * (x e.1.1 - x e.1.2))) by
        refine Finset.sum_congr rfl ?_
        intro x _hx
        exact E.finiteCliqueKernelWeight_evalFinite_eq_sum_edgeAssignments_of_support_subset
          P A hP n x]
  rw [Finset.sum_comm]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl ?_
  intro ω hω
  rw [← Finset.mul_sum]
  rw [show
      ((Fintype.card (Fin M → ZMod (S.p (E.φ n))) : ℂ)⁻¹) *
          (E.cliqueEdgeAssignmentCoeff P ω *
            ∑ x : Fin M → ZMod (S.p (E.φ n)),
              ∏ e : CliqueEdgeIndex M,
                ZMod.stdAddChar
                  (-(E.lift n (ω e) * (x e.1.1 - x e.1.2)))) =
        E.cliqueEdgeAssignmentCoeff P ω *
          (((Fintype.card (Fin M → ZMod (S.p (E.φ n))) : ℂ)⁻¹) *
            ∑ x : Fin M → ZMod (S.p (E.φ n)),
              ∏ e : CliqueEdgeIndex M,
                ZMod.stdAddChar
                  (-(E.lift n (ω e) * (x e.1.1 - x e.1.2)))) by
        ring]
  rw [show
      ((Fintype.card (Fin M → ZMod (S.p (E.φ n))) : ℂ)⁻¹) *
          ∑ x : Fin M → ZMod (S.p (E.φ n)),
            ∏ e : CliqueEdgeIndex M,
              ZMod.stdAddChar
                (-(E.lift n (ω e) * (x e.1.1 - x e.1.2))) =
        ((Fintype.card (Fin M → ZMod (S.p (E.φ n))) : ℂ)⁻¹) *
          ∑ x : Fin M → ZMod (S.p (E.φ n)),
            ∏ e ∈ cliqueEdgePairs M,
              ZMod.stdAddChar
                (-(E.lift n (E.extendCliqueEdgeAssignment ω e) *
                    (x e.1 - x e.2))) by
        congr 1
        refine Finset.sum_congr rfl ?_
        intro x _hx
        exact E.prod_stdAddChar_cliqueEdgeIndex_eq_extend ω n x]
  rw [E.finiteCliqueAssignmentAverage_eq_if (E.extendCliqueEdgeAssignment ω) n]

/-- Compact character product for one edge-frequency assignment, regrouped by
vertex balances. -/
lemma prod_addCharacterValue_cliqueEdge_eq_prod_balance
    (E : CayleyExtraction S) {M : ℕ}
    (ω : Fin M × Fin M → E.Group) (x : Fin M → E.CompactAddDual) :
    (∏ e ∈ cliqueEdgePairs M,
        E.addCharacterValue (x e.1 - x e.2) (ω e)) =
      ∏ i : Fin M, E.addCharacterValue (x i) (E.cliqueFrequencyBalance ω i) := by
  classical
  unfold cliqueFrequencyBalance cliqueOutgoingFreq cliqueIncomingFreq
  rw [show
      (∏ i : Fin M,
          E.addCharacterValue (x i)
            ((∑ e ∈ (cliqueEdgePairs M).filter (fun e => e.1 = i), ω e) -
              ∑ e ∈ (cliqueEdgePairs M).filter (fun e => e.2 = i), ω e)) =
        (∏ i : Fin M,
          (∏ e ∈ cliqueEdgePairs M,
            if e.1 = i then E.addCharacterValue (x i) (ω e) else 1) *
          (∏ e ∈ cliqueEdgePairs M,
            if e.2 = i then E.addCharacterValue (x i) (-ω e) else 1)) by
        refine Finset.prod_congr rfl ?_
        intro i _hi
        rw [sub_eq_add_neg, E.addCharacterValue_add]
        rw [E.addCharacterValue_sum]
        rw [show
            E.addCharacterValue (x i)
                (-(∑ e ∈ (cliqueEdgePairs M).filter (fun e => e.2 = i), ω e)) =
              E.addCharacterValue (x i)
                (∑ e ∈ (cliqueEdgePairs M).filter (fun e => e.2 = i), -ω e) by
              simp]
        rw [E.addCharacterValue_sum]
        rw [Finset.prod_filter, Finset.prod_filter]]
  rw [Finset.prod_mul_distrib]
  rw [prod_vertex_outgoing_eq_edge_prod (cliqueEdgePairs M)
    (fun e i => E.addCharacterValue (x i) (ω e))]
  rw [prod_vertex_incoming_eq_edge_prod (cliqueEdgePairs M)
    (fun e i => E.addCharacterValue (x i) (-ω e))]
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl ?_
  intro e _he
  simp [sub_eq_add_neg, E.addCharacterValue_add_point]

lemma compactCliqueAssignmentIntegral_eq_if
    (E : CayleyExtraction S) {M : ℕ}
    (ω : Fin M × Fin M → E.Group) :
    (∫ x : Fin M → E.CompactAddDual,
        (∏ e ∈ cliqueEdgePairs M,
          E.addCharacterValue (x e.1 - x e.2) (ω e))
        ∂Measure.pi (fun _ : Fin M => E.haar)) =
      if (∀ i : Fin M, E.cliqueFrequencyBalance ω i = 0)
      then 1 else 0 := by
  rw [show
      (∫ x : Fin M → E.CompactAddDual,
          (∏ e ∈ cliqueEdgePairs M,
            E.addCharacterValue (x e.1 - x e.2) (ω e))
          ∂Measure.pi (fun _ : Fin M => E.haar)) =
        ∫ x : Fin M → E.CompactAddDual,
          ∏ i : Fin M, E.addCharacterValue (x i)
            (E.cliqueFrequencyBalance ω i)
          ∂Measure.pi (fun _ : Fin M => E.haar) by
        congr 1
        funext x
        exact E.prod_addCharacterValue_cliqueEdge_eq_prod_balance ω x]
  exact E.compactPiIntegral_prod_addCharacterValue_eq_if
    (fun i : Fin M => E.cliqueFrequencyBalance ω i)

lemma continuous_cliqueEdgeAssignmentCharacterProduct
    (E : CayleyExtraction S) {M : ℕ}
    (ω : CliqueEdgeIndex M → E.Group) :
    Continuous (fun x : Fin M → E.CompactAddDual =>
      ∏ e : CliqueEdgeIndex M,
        E.addCharacterValue (x e.1.1 - x e.1.2) (ω e)) := by
  simpa using
    (continuous_finsetProd (Finset.univ : Finset (CliqueEdgeIndex M))
      (fun e _he =>
        (E.addCharacterValue_continuous (ω e)).comp
          ((continuous_apply e.1.1).sub (continuous_apply e.1.2))))

lemma integrable_cliqueEdgeAssignmentTerm
    (E : CayleyExtraction S) {M : ℕ}
    (P : E.TrigPoly) (ω : CliqueEdgeIndex M → E.Group) :
    Integrable
      (fun x : Fin M → E.CompactAddDual =>
        E.cliqueEdgeAssignmentCoeff P ω *
          ∏ e : CliqueEdgeIndex M,
            E.addCharacterValue (x e.1.1 - x e.1.2) (ω e))
      (Measure.pi (fun _ : Fin M => E.haar)) :=
  (continuous_const.mul
      (E.continuous_cliqueEdgeAssignmentCharacterProduct ω)).integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)

lemma compactCliqueKernel_evalAdd_eq_sum_edgeAssignments
    (E : CayleyExtraction S) {M : ℕ}
    (P : E.TrigPoly) (x : Fin M → E.CompactAddDual) :
    (∏ e ∈ cliqueEdgePairs M,
        TrigPoly.evalAdd P (x e.1 - x e.2)) =
      ∑ ω ∈ Fintype.piFinset (fun _ : CliqueEdgeIndex M => P.support),
        E.cliqueEdgeAssignmentCoeff P ω *
          ∏ e : CliqueEdgeIndex M,
            E.addCharacterValue (x e.1.1 - x e.1.2) (ω e) := by
  classical
  rw [show
      (∏ e ∈ cliqueEdgePairs M,
          TrigPoly.evalAdd P (x e.1 - x e.2)) =
        ∏ e : CliqueEdgeIndex M,
          TrigPoly.evalAdd P (x e.1.1 - x e.1.2) by
        simpa [CliqueEdgeIndex] using
          (Finset.prod_attach (s := cliqueEdgePairs M)
            (f := fun e : Fin M × Fin M =>
              TrigPoly.evalAdd P (x e.1 - x e.2))).symm]
  rw [show
      (∏ e : CliqueEdgeIndex M,
          TrigPoly.evalAdd P (x e.1.1 - x e.1.2)) =
        ∏ e : CliqueEdgeIndex M,
          ∑ γ ∈ P.support,
            P γ * E.addCharacterValue (x e.1.1 - x e.1.2) γ by
        refine Finset.prod_congr rfl ?_
        intro e _he
        exact TrigPoly.evalAdd_eq_sum_support E P (x e.1.1 - x e.1.2)]
  rw [Finset.prod_univ_sum]
  refine Finset.sum_congr rfl ?_
  intro ω _hω
  rw [Finset.prod_mul_distrib]
  rfl

lemma compactCliqueKernel_evalAdd_eq_sum_edgeAssignments_of_support_subset
    (E : CayleyExtraction S) {M : ℕ}
    (P : E.TrigPoly) (A : Finset E.Group) (hP : P.support ⊆ A)
    (x : Fin M → E.CompactAddDual) :
    (∏ e ∈ cliqueEdgePairs M,
        TrigPoly.evalAdd P (x e.1 - x e.2)) =
      ∑ ω ∈ Fintype.piFinset (fun _ : CliqueEdgeIndex M => A),
        E.cliqueEdgeAssignmentCoeff P ω *
          ∏ e : CliqueEdgeIndex M,
            E.addCharacterValue (x e.1.1 - x e.1.2) (ω e) := by
  classical
  rw [show
      (∏ e ∈ cliqueEdgePairs M,
          TrigPoly.evalAdd P (x e.1 - x e.2)) =
        ∏ e : CliqueEdgeIndex M,
          TrigPoly.evalAdd P (x e.1.1 - x e.1.2) by
        simpa [CliqueEdgeIndex] using
          (Finset.prod_attach (s := cliqueEdgePairs M)
            (f := fun e : Fin M × Fin M =>
              TrigPoly.evalAdd P (x e.1 - x e.2))).symm]
  rw [show
      (∏ e : CliqueEdgeIndex M,
          TrigPoly.evalAdd P (x e.1.1 - x e.1.2)) =
        ∏ e : CliqueEdgeIndex M,
          ∑ γ ∈ A,
            P γ * E.addCharacterValue (x e.1.1 - x e.1.2) γ by
        refine Finset.prod_congr rfl ?_
        intro e _he
        exact TrigPoly.evalAdd_eq_sum_of_support_subset E P A hP
          (x e.1.1 - x e.1.2)]
  rw [Finset.prod_univ_sum]
  refine Finset.sum_congr rfl ?_
  intro ω _hω
  rw [Finset.prod_mul_distrib]
  rfl

lemma prod_addCharacterValue_cliqueEdgeIndex_eq_extend
    (E : CayleyExtraction S) {M : ℕ}
    (ω : CliqueEdgeIndex M → E.Group)
    (x : Fin M → E.CompactAddDual) :
    (∏ e : CliqueEdgeIndex M,
        E.addCharacterValue (x e.1.1 - x e.1.2) (ω e)) =
      ∏ e ∈ cliqueEdgePairs M,
        E.addCharacterValue (x e.1 - x e.2)
          (E.extendCliqueEdgeAssignment ω e) := by
  simpa [CliqueEdgeIndex] using
    (Finset.prod_attach (s := cliqueEdgePairs M)
      (f := fun e : Fin M × Fin M =>
        E.addCharacterValue (x e.1 - x e.2)
          (E.extendCliqueEdgeAssignment ω e)))

lemma compactCliqueDensity_evalAdd_eq_sum_edgeAssignments
    (E : CayleyExtraction S) {M : ℕ}
    (P : E.TrigPoly) :
    (∫ x : Fin M → E.CompactAddDual,
        (∏ e ∈ cliqueEdgePairs M,
          TrigPoly.evalAdd P (x e.1 - x e.2))
        ∂Measure.pi (fun _ : Fin M => E.haar)) =
      ∑ ω ∈ Fintype.piFinset (fun _ : CliqueEdgeIndex M => P.support),
        E.cliqueEdgeAssignmentCoeff P ω *
          (if (∀ i : Fin M,
              E.cliqueFrequencyBalance
                (E.extendCliqueEdgeAssignment ω) i = 0)
            then 1 else 0) := by
  classical
  rw [show
      (∫ x : Fin M → E.CompactAddDual,
          (∏ e ∈ cliqueEdgePairs M,
            TrigPoly.evalAdd P (x e.1 - x e.2))
          ∂Measure.pi (fun _ : Fin M => E.haar)) =
        ∫ x : Fin M → E.CompactAddDual,
          ∑ ω ∈ Fintype.piFinset (fun _ : CliqueEdgeIndex M => P.support),
            E.cliqueEdgeAssignmentCoeff P ω *
              ∏ e : CliqueEdgeIndex M,
                E.addCharacterValue (x e.1.1 - x e.1.2) (ω e)
          ∂Measure.pi (fun _ : Fin M => E.haar) by
        congr 1
        funext x
        exact E.compactCliqueKernel_evalAdd_eq_sum_edgeAssignments P x]
  rw [MeasureTheory.integral_finsetSum]
  · refine Finset.sum_congr rfl ?_
    intro ω _hω
    rw [show
        (∫ x : Fin M → E.CompactAddDual,
            E.cliqueEdgeAssignmentCoeff P ω *
              ∏ e : CliqueEdgeIndex M,
                E.addCharacterValue (x e.1.1 - x e.1.2) (ω e)
            ∂Measure.pi (fun _ : Fin M => E.haar)) =
          E.cliqueEdgeAssignmentCoeff P ω *
            ∫ x : Fin M → E.CompactAddDual,
              ∏ e : CliqueEdgeIndex M,
                E.addCharacterValue (x e.1.1 - x e.1.2) (ω e)
            ∂Measure.pi (fun _ : Fin M => E.haar) by
      simpa using
        (MeasureTheory.integral_const_mul
          (μ := Measure.pi (fun _ : Fin M => E.haar))
          (E.cliqueEdgeAssignmentCoeff P ω)
          (fun x : Fin M → E.CompactAddDual =>
            ∏ e : CliqueEdgeIndex M,
              E.addCharacterValue (x e.1.1 - x e.1.2) (ω e)))]
    rw [show
        (∫ x : Fin M → E.CompactAddDual,
            (∏ e : CliqueEdgeIndex M,
              E.addCharacterValue (x e.1.1 - x e.1.2) (ω e))
            ∂Measure.pi (fun _ : Fin M => E.haar)) =
          ∫ x : Fin M → E.CompactAddDual,
            (∏ e ∈ cliqueEdgePairs M,
              E.addCharacterValue (x e.1 - x e.2)
                (E.extendCliqueEdgeAssignment ω e))
            ∂Measure.pi (fun _ : Fin M => E.haar) by
          congr 1
          funext x
          exact E.prod_addCharacterValue_cliqueEdgeIndex_eq_extend ω x]
    rw [E.compactCliqueAssignmentIntegral_eq_if (E.extendCliqueEdgeAssignment ω)]
  · intro ω _hω
    exact E.integrable_cliqueEdgeAssignmentTerm P ω

lemma compactCliqueDensity_evalAdd_eq_sum_edgeAssignments_of_support_subset
    (E : CayleyExtraction S) {M : ℕ}
    (P : E.TrigPoly) (A : Finset E.Group) (hP : P.support ⊆ A) :
    (∫ x : Fin M → E.CompactAddDual,
        (∏ e ∈ cliqueEdgePairs M,
          TrigPoly.evalAdd P (x e.1 - x e.2))
        ∂Measure.pi (fun _ : Fin M => E.haar)) =
      ∑ ω ∈ Fintype.piFinset (fun _ : CliqueEdgeIndex M => A),
        E.cliqueEdgeAssignmentCoeff P ω *
          (if (∀ i : Fin M,
              E.cliqueFrequencyBalance
                (E.extendCliqueEdgeAssignment ω) i = 0)
            then 1 else 0) := by
  classical
  rw [show
      (∫ x : Fin M → E.CompactAddDual,
          (∏ e ∈ cliqueEdgePairs M,
            TrigPoly.evalAdd P (x e.1 - x e.2))
          ∂Measure.pi (fun _ : Fin M => E.haar)) =
        ∫ x : Fin M → E.CompactAddDual,
          ∑ ω ∈ Fintype.piFinset (fun _ : CliqueEdgeIndex M => A),
            E.cliqueEdgeAssignmentCoeff P ω *
              ∏ e : CliqueEdgeIndex M,
                E.addCharacterValue (x e.1.1 - x e.1.2) (ω e)
          ∂Measure.pi (fun _ : Fin M => E.haar) by
        congr 1
        funext x
        exact E.compactCliqueKernel_evalAdd_eq_sum_edgeAssignments_of_support_subset
          P A hP x]
  rw [MeasureTheory.integral_finsetSum]
  · refine Finset.sum_congr rfl ?_
    intro ω _hω
    rw [show
        (∫ x : Fin M → E.CompactAddDual,
            E.cliqueEdgeAssignmentCoeff P ω *
              ∏ e : CliqueEdgeIndex M,
                E.addCharacterValue (x e.1.1 - x e.1.2) (ω e)
            ∂Measure.pi (fun _ : Fin M => E.haar)) =
          E.cliqueEdgeAssignmentCoeff P ω *
            ∫ x : Fin M → E.CompactAddDual,
              ∏ e : CliqueEdgeIndex M,
                E.addCharacterValue (x e.1.1 - x e.1.2) (ω e)
            ∂Measure.pi (fun _ : Fin M => E.haar) by
      simpa using
        (MeasureTheory.integral_const_mul
          (μ := Measure.pi (fun _ : Fin M => E.haar))
          (E.cliqueEdgeAssignmentCoeff P ω)
          (fun x : Fin M → E.CompactAddDual =>
            ∏ e : CliqueEdgeIndex M,
              E.addCharacterValue (x e.1.1 - x e.1.2) (ω e)))]
    rw [show
        (∫ x : Fin M → E.CompactAddDual,
            (∏ e : CliqueEdgeIndex M,
              E.addCharacterValue (x e.1.1 - x e.1.2) (ω e))
            ∂Measure.pi (fun _ : Fin M => E.haar)) =
          ∫ x : Fin M → E.CompactAddDual,
            (∏ e ∈ cliqueEdgePairs M,
              E.addCharacterValue (x e.1 - x e.2)
                (E.extendCliqueEdgeAssignment ω e))
            ∂Measure.pi (fun _ : Fin M => E.haar) by
          congr 1
          funext x
          exact E.prod_addCharacterValue_cliqueEdgeIndex_eq_extend ω x]
    rw [E.compactCliqueAssignmentIntegral_eq_if (E.extendCliqueEdgeAssignment ω)]
  · intro ω _hω
    exact E.integrable_cliqueEdgeAssignmentTerm P ω

lemma finiteCliqueKernelDensity_evalFinite_eventually_eq_compact
    (E : CayleyExtraction S) {M : ℕ}
    (P : E.TrigPoly) :
    ∀ᶠ n in atTop,
      (letI : Fact (S.p (E.φ n)).Prime := ⟨S.prime (E.φ n)⟩
       letI : NeZero (S.p (E.φ n)) := ⟨(S.prime (E.φ n)).ne_zero⟩
       finiteCliqueKernelDensity (p := S.p (E.φ n)) (ℓ := M)
        (fun z : ZMod (S.p (E.φ n)) => TrigPoly.evalFinite P n z)) =
      (∫ x : Fin M → E.CompactAddDual,
        (∏ e ∈ cliqueEdgePairs M,
          TrigPoly.evalAdd P (x e.1 - x e.2))
        ∂Measure.pi (fun _ : Fin M => E.haar)) := by
  classical
  let A : Finset (CliqueEdgeIndex M → E.Group) :=
    Fintype.piFinset (fun _ : CliqueEdgeIndex M => P.support)
  have hbalance :
      ∀ᶠ n in atTop, ∀ ω ∈ A,
        ((∀ i : Fin M,
            E.finiteCliqueFrequencyBalance
              (E.extendCliqueEdgeAssignment ω) n i = 0) ↔
          ∀ i : Fin M,
            E.cliqueFrequencyBalance
              (E.extendCliqueEdgeAssignment ω) i = 0) := by
    rw [A.eventually_all]
    intro ω _hω
    exact E.finiteCliqueFrequencyBalance_all_zero_iff_eventually
      (E.extendCliqueEdgeAssignment ω)
  filter_upwards [hbalance] with n hbalance_n
  haveI : Fact (S.p (E.φ n)).Prime := ⟨S.prime (E.φ n)⟩
  haveI : NeZero (S.p (E.φ n)) := ⟨(S.prime (E.φ n)).ne_zero⟩
  rw [E.finiteCliqueKernelDensity_evalFinite_eq_sum_edgeAssignments P n]
  rw [E.compactCliqueDensity_evalAdd_eq_sum_edgeAssignments P]
  dsimp [A] at hbalance_n
  refine Finset.sum_congr rfl ?_
  intro ω hω
  by_cases hfin :
      ∀ i : Fin M,
        E.finiteCliqueFrequencyBalance
          (E.extendCliqueEdgeAssignment ω) n i = 0
  · have hcompact :
        ∀ i : Fin M,
          E.cliqueFrequencyBalance
            (E.extendCliqueEdgeAssignment ω) i = 0 :=
      (hbalance_n ω hω).mp hfin
    simp [hfin, hcompact]
  · have hcompact :
        ¬ ∀ i : Fin M,
          E.cliqueFrequencyBalance
            (E.extendCliqueEdgeAssignment ω) i = 0 := by
      intro hc
      exact hfin ((hbalance_n ω hω).mpr hc)
    simp [hfin, hcompact]

lemma finiteCliqueKernelDensity_evalFinite_tendsto_compact_of_coeff_tendsto
    (E : CayleyExtraction S) {M : ℕ}
    (Pseq : ℕ → E.TrigPoly) (P : E.TrigPoly) (A : Finset E.Group)
    (hPseq_support : ∀ᶠ n in atTop, (Pseq n).support ⊆ A)
    (hP_support : P.support ⊆ A)
    (hcoeff :
      ∀ γ ∈ A, Tendsto (fun n => Pseq n γ) atTop (𝓝 (P γ))) :
    Tendsto
      (fun n =>
        letI : Fact (S.p (E.φ n)).Prime := ⟨S.prime (E.φ n)⟩
        letI : NeZero (S.p (E.φ n)) := ⟨(S.prime (E.φ n)).ne_zero⟩
        finiteCliqueKernelDensity (p := S.p (E.φ n)) (ℓ := M)
          (fun z : ZMod (S.p (E.φ n)) =>
            TrigPoly.evalFinite (Pseq n) n z))
      atTop
      (𝓝
        (∫ x : Fin M → E.CompactAddDual,
          (∏ e ∈ cliqueEdgePairs M,
            TrigPoly.evalAdd P (x e.1 - x e.2))
          ∂Measure.pi (fun _ : Fin M => E.haar))) := by
  classical
  let W : Finset (CliqueEdgeIndex M → E.Group) :=
    Fintype.piFinset (fun _ : CliqueEdgeIndex M => A)
  let compactTerm : (CliqueEdgeIndex M → E.Group) → ℂ := fun ω =>
    E.cliqueEdgeAssignmentCoeff P ω *
      (if (∀ i : Fin M,
          E.cliqueFrequencyBalance
            (E.extendCliqueEdgeAssignment ω) i = 0)
        then 1 else 0)
  let finiteTerm : ℕ → (CliqueEdgeIndex M → E.Group) → ℂ := fun n ω =>
    E.cliqueEdgeAssignmentCoeff (Pseq n) ω *
      (if (∀ i : Fin M,
          E.finiteCliqueFrequencyBalance
            (E.extendCliqueEdgeAssignment ω) n i = 0)
        then 1 else 0)
  have hfinite_exp :
      (fun n =>
        letI : Fact (S.p (E.φ n)).Prime := ⟨S.prime (E.φ n)⟩
        letI : NeZero (S.p (E.φ n)) := ⟨(S.prime (E.φ n)).ne_zero⟩
        finiteCliqueKernelDensity (p := S.p (E.φ n)) (ℓ := M)
          (fun z : ZMod (S.p (E.φ n)) =>
            TrigPoly.evalFinite (Pseq n) n z)) =ᶠ[atTop]
      (fun n => ∑ ω ∈ W, finiteTerm n ω) := by
    filter_upwards [hPseq_support] with n hn_support
    haveI : Fact (S.p (E.φ n)).Prime := ⟨S.prime (E.φ n)⟩
    haveI : NeZero (S.p (E.φ n)) := ⟨(S.prime (E.φ n)).ne_zero⟩
    rw [E.finiteCliqueKernelDensity_evalFinite_eq_sum_edgeAssignments_of_support_subset
      (Pseq n) A hn_support n]
  have hcompact_exp :
      (∫ x : Fin M → E.CompactAddDual,
          (∏ e ∈ cliqueEdgePairs M,
            TrigPoly.evalAdd P (x e.1 - x e.2))
          ∂Measure.pi (fun _ : Fin M => E.haar)) =
        ∑ ω ∈ W, compactTerm ω := by
    rw [E.compactCliqueDensity_evalAdd_eq_sum_edgeAssignments_of_support_subset
      P A hP_support]
  have hterm :
      ∀ ω ∈ W, Tendsto (fun n => finiteTerm n ω) atTop (𝓝 (compactTerm ω)) := by
    intro ω hω
    have hω_mem : ∀ e : CliqueEdgeIndex M, ω e ∈ A :=
      Fintype.mem_piFinset.mp hω
    have hcoeff_prod :
        Tendsto (fun n => E.cliqueEdgeAssignmentCoeff (Pseq n) ω)
          atTop (𝓝 (E.cliqueEdgeAssignmentCoeff P ω)) := by
      unfold cliqueEdgeAssignmentCoeff
      exact tendsto_finsetProd (Finset.univ : Finset (CliqueEdgeIndex M))
        (fun e _he => hcoeff (ω e) (hω_mem e))
    have hif :
        (fun n =>
          if (∀ i : Fin M,
              E.finiteCliqueFrequencyBalance
                (E.extendCliqueEdgeAssignment ω) n i = 0)
          then (1 : ℂ) else 0) =ᶠ[atTop]
        (fun _n =>
          if (∀ i : Fin M,
              E.cliqueFrequencyBalance
                (E.extendCliqueEdgeAssignment ω) i = 0)
          then (1 : ℂ) else 0) := by
      filter_upwards
        [E.finiteCliqueFrequencyBalance_all_zero_iff_eventually
          (E.extendCliqueEdgeAssignment ω)] with n hn
      by_cases hfin :
          ∀ i : Fin M,
            E.finiteCliqueFrequencyBalance
              (E.extendCliqueEdgeAssignment ω) n i = 0
      · have hcompact :
            ∀ i : Fin M,
              E.cliqueFrequencyBalance
                (E.extendCliqueEdgeAssignment ω) i = 0 :=
          hn.mp hfin
        simp [hfin, hcompact]
      · have hcompact :
            ¬ ∀ i : Fin M,
              E.cliqueFrequencyBalance
                (E.extendCliqueEdgeAssignment ω) i = 0 := by
          intro hc
          exact hfin (hn.mpr hc)
        simp [hfin, hcompact]
    have hif_tendsto :
        Tendsto
          (fun n =>
            if (∀ i : Fin M,
                E.finiteCliqueFrequencyBalance
                  (E.extendCliqueEdgeAssignment ω) n i = 0)
            then (1 : ℂ) else 0)
          atTop
          (𝓝
            (if (∀ i : Fin M,
                E.cliqueFrequencyBalance
                  (E.extendCliqueEdgeAssignment ω) i = 0)
              then (1 : ℂ) else 0)) :=
      tendsto_const_nhds.congr' hif.symm
    exact (hcoeff_prod.mul hif_tendsto).congr' (Filter.Eventually.of_forall fun n => rfl)
  have hsum :
      Tendsto (fun n => ∑ ω ∈ W, finiteTerm n ω)
        atTop (𝓝 (∑ ω ∈ W, compactTerm ω)) :=
    tendsto_finsetSum W hterm
  rw [hcompact_exp]
  exact hsum.congr' hfinite_exp.symm

lemma finiteSmoothModelTrigPoly_support_subset_fejer
    (E : CayleyExtraction S) (Q : Finset E.Group) (n : ℕ) :
    (E.finiteSmoothModelTrigPoly Q n).support ⊆
      (E.fejerTrigPoly Q).support := by
  intro γ hγ
  rw [Finsupp.mem_support_iff] at hγ ⊢
  intro hfejer
  have hzero : E.finiteSmoothModelTrigPoly Q n γ = 0 := by
    rw [E.finiteSmoothModelTrigPoly_apply Q n γ, hfejer]
    simp
  exact hγ hzero

lemma compactSmoothTrigPoly_support_subset_fejer
    (E : CayleyExtraction S) (Q : Finset E.Group) :
    (E.compactSmoothTrigPoly Q).support ⊆
      (E.fejerTrigPoly Q).support := by
  intro γ hγ
  rw [Finsupp.mem_support_iff] at hγ ⊢
  intro hfejer
  have hzero : E.compactSmoothTrigPoly Q γ = 0 := by
    rw [E.compactSmoothTrigPoly_apply Q γ, hfejer]
    simp
  exact hγ hzero

lemma finiteCliqueKernelDensity_finiteSmoothModelTrigPoly_tendsto_compactSmooth
    (E : CayleyExtraction S) (Q : Finset E.Group) (M : ℕ) :
    Tendsto
      (fun n =>
        letI : Fact (S.p (E.φ n)).Prime := ⟨S.prime (E.φ n)⟩
        letI : NeZero (S.p (E.φ n)) := ⟨(S.prime (E.φ n)).ne_zero⟩
        finiteCliqueKernelDensity (p := S.p (E.φ n)) (ℓ := M)
          (fun z : ZMod (S.p (E.φ n)) =>
            TrigPoly.evalFinite (E.finiteSmoothModelTrigPoly Q n) n z))
      atTop
      (𝓝
        (∫ x : Fin M → E.CompactAddDual,
          (∏ e ∈ cliqueEdgePairs M,
            E.compactSmooth Q (x e.1 - x e.2))
          ∂Measure.pi (fun _ : Fin M => E.haar))) := by
  simpa [compactSmooth] using
    E.finiteCliqueKernelDensity_evalFinite_tendsto_compact_of_coeff_tendsto
      (fun n => E.finiteSmoothModelTrigPoly Q n)
      (E.compactSmoothTrigPoly Q)
      (E.fejerTrigPoly Q).support
      (Filter.Eventually.of_forall
        (fun n => E.finiteSmoothModelTrigPoly_support_subset_fejer Q n))
      (E.compactSmoothTrigPoly_support_subset_fejer Q)
      (fun γ _hγ =>
        E.finiteSmoothModelTrigPoly_apply_tendsto_compactSmoothTrigPoly Q γ)

lemma finiteCliqueKernelDensity_finiteSmooth_tendsto_compactSmooth
    (E : CayleyExtraction S) (Q : Finset E.Group) (M : ℕ) :
    Tendsto
      (fun n =>
        letI : Fact (S.p (E.φ n)).Prime := ⟨S.prime (E.φ n)⟩
        letI : NeZero (S.p (E.φ n)) := ⟨(S.prime (E.φ n)).ne_zero⟩
        finiteCliqueKernelDensity (p := S.p (E.φ n)) (ℓ := M)
          (E.finiteSmooth Q n))
      atTop
      (𝓝
        (∫ x : Fin M → E.CompactAddDual,
          (∏ e ∈ cliqueEdgePairs M,
            E.compactSmooth Q (x e.1 - x e.2))
          ∂Measure.pi (fun _ : Fin M => E.haar))) := by
  refine
    (E.finiteCliqueKernelDensity_finiteSmoothModelTrigPoly_tendsto_compactSmooth
      Q M).congr' ?_
  filter_upwards
    [E.finiteSmooth_eq_evalFinite_finiteSmoothModelTrigPoly_eventually Q]
    with n hn
  haveI : Fact (S.p (E.φ n)).Prime := ⟨S.prime (E.φ n)⟩
  haveI : NeZero (S.p (E.φ n)) := ⟨(S.prime (E.φ n)).ne_zero⟩
  congr 1
  funext z
  exact (hn z).symm

lemma compactSmooth_cliqueDensity_integral_re_eq_continuousCliqueDensity
    (E : CayleyExtraction S) (Q : Finset E.Group) (M : ℕ) :
    (∫ x : Fin M → E.CompactAddDual,
        (∏ e ∈ cliqueEdgePairs M,
          E.compactSmooth Q (x e.1 - x e.2))
        ∂Measure.pi (fun _ : Fin M => E.haar)).re =
      continuousCliqueDensity E.haar M (E.compactSmoothReal Q) := by
  classical
  let μ : Measure (Fin M → E.CompactAddDual) :=
    Measure.pi (fun _ : Fin M => E.haar)
  have hprod :
      (fun x : Fin M → E.CompactAddDual =>
        ∏ e ∈ cliqueEdgePairs M,
          E.compactSmooth Q (x e.1 - x e.2)) =
      (fun x : Fin M → E.CompactAddDual =>
        ((∏ e ∈ cliqueEdgePairs M,
          E.compactSmoothReal Q (x e.1 - x e.2)) : ℂ)) := by
    funext x
    calc
      (∏ e ∈ cliqueEdgePairs M,
          E.compactSmooth Q (x e.1 - x e.2))
          =
        ∏ e ∈ cliqueEdgePairs M,
          ((E.compactSmoothReal Q (x e.1 - x e.2)) : ℂ) := by
            refine Finset.prod_congr rfl ?_
            intro e _he
            exact E.compactSmooth_eq_ofReal_compactSmoothReal Q
              (x e.1 - x e.2)
      _ =
        ((∏ e ∈ cliqueEdgePairs M,
          E.compactSmoothReal Q (x e.1 - x e.2)) : ℂ) := by
            simp
  have hintegral :
      (∫ x : Fin M → E.CompactAddDual,
          (∏ e ∈ cliqueEdgePairs M,
            E.compactSmooth Q (x e.1 - x e.2))
          ∂μ) =
        ∫ x : Fin M → E.CompactAddDual,
          ((∏ e ∈ cliqueEdgePairs M,
            E.compactSmoothReal Q (x e.1 - x e.2)) : ℂ) ∂μ := by
    rw [hprod]
  have hcont :
      Continuous (fun x : Fin M → E.CompactAddDual =>
        ∏ e ∈ cliqueEdgePairs M,
          ((E.compactSmoothReal Q (x e.1 - x e.2)) : ℂ)) := by
    refine continuous_finsetProd (cliqueEdgePairs M) ?_
    intro e _he
    exact Complex.continuous_ofReal.comp
      ((E.compactSmoothReal_continuous Q).comp
        ((continuous_apply e.1).sub (continuous_apply e.2)))
  have hint :
      Integrable
        (fun x : Fin M → E.CompactAddDual =>
          ∏ e ∈ cliqueEdgePairs M,
            ((E.compactSmoothReal Q (x e.1 - x e.2)) : ℂ)) μ :=
    hcont.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  rw [hintegral]
  change RCLike.re
      (∫ x : Fin M → E.CompactAddDual,
        ∏ e ∈ cliqueEdgePairs M,
          ((E.compactSmoothReal Q (x e.1 - x e.2)) : ℂ) ∂μ) =
    continuousCliqueDensity E.haar M (E.compactSmoothReal Q)
  refine (integral_re (μ := μ) (f := fun x : Fin M → E.CompactAddDual =>
    ∏ e ∈ cliqueEdgePairs M,
      ((E.compactSmoothReal Q (x e.1 - x e.2)) : ℂ)) hint).symm.trans ?_
  have hre_fun :
      (fun x : Fin M → E.CompactAddDual =>
        RCLike.re
          (∏ e ∈ cliqueEdgePairs M,
            ((E.compactSmoothReal Q (x e.1 - x e.2)) : ℂ))) =
      (fun x : Fin M → E.CompactAddDual =>
        ∏ e ∈ cliqueEdgePairs M,
          E.compactSmoothReal Q (x e.1 - x e.2)) := by
    funext x
    have hprod_cast :=
      (Complex.ofReal_prod (cliqueEdgePairs M)
        (fun e : Fin M × Fin M =>
          E.compactSmoothReal Q (x e.1 - x e.2))).symm
    rw [hprod_cast]
    exact Complex.ofReal_re _
  rw [hre_fun]
  simp [continuousCliqueDensity, continuousCliqueKernel,
    continuousCliqueEdgePairs, cliqueEdgePairs, μ]

lemma finiteCliqueKernelDensity_finiteSmooth_re_tendsto_compactSmoothReal
    (E : CayleyExtraction S) (Q : Finset E.Group) (M : ℕ) :
    Tendsto
      (fun n =>
        (letI : Fact (S.p (E.φ n)).Prime := ⟨S.prime (E.φ n)⟩
         letI : NeZero (S.p (E.φ n)) := ⟨(S.prime (E.φ n)).ne_zero⟩
         finiteCliqueKernelDensity (p := S.p (E.φ n)) (ℓ := M)
          (E.finiteSmooth Q n)).re)
      atTop
      (𝓝 (continuousCliqueDensity E.haar M (E.compactSmoothReal Q))) := by
  have hcomplex :=
    E.finiteCliqueKernelDensity_finiteSmooth_tendsto_compactSmooth Q M
  have hre :=
    (Complex.continuous_re.tendsto
      (∫ x : Fin M → E.CompactAddDual,
        (∏ e ∈ cliqueEdgePairs M,
          E.compactSmooth Q (x e.1 - x e.2))
        ∂Measure.pi (fun _ : Fin M => E.haar))).comp hcomplex
  simpa [Function.comp_def,
    E.compactSmooth_cliqueDensity_integral_re_eq_continuousCliqueDensity Q M]
    using hre

end CayleyExtraction

end

end Erdos42.CompactCayley


/-! =============================================================
    Section from: Erdos/P42/CompactCayley/Contradiction.lean
    ============================================================= -/

/-
Erdős Problem 42 — contradiction from a compact-Cayley counterexample sequence.
-/


namespace Erdos42.CompactCayley

open Filter Erdos42
open scoped Topology

noncomputable section

theorem CayleyCounterSeq.false
    {ℓ : ℕ} {η : ℝ} (hℓ : 2 ≤ ℓ) (hη : 0 < η)
    (S : CayleyCounterSeq ℓ η) :
    False := by
  classical
  obtain ⟨E, _⟩ := exists_cayleyExtraction S
  let ρ : ℝ := continuousCliqueDensity E.haar ℓ E.fReal
  have hρ_pos : 0 < ρ := by
    dsimp [ρ]
    exact E.compact_limit_cliqueDensity_pos hℓ hη
  let L : ℝ := ((ℓ * ℓ : ℕ) : ℝ)
  have hℓ_pos : 0 < ℓ := by omega
  have hL_pos : 0 < L := by
    dsimp [L]
    exact_mod_cast Nat.mul_pos hℓ_pos hℓ_pos
  have htarget_pos : 0 < ρ / (8 * L) := by
    exact div_pos hρ_pos (mul_pos (by norm_num) hL_pos)
  obtain ⟨qNat, hqNat_pos, hqNat_inv⟩ :=
    Real.exists_nat_pos_inv_lt htarget_pos
  let q : ℕ+ := ⟨qNat, hqNat_pos⟩
  let qinv : ℝ := ((q : ℝ)⁻¹ : ℝ)
  have hq_pos_real : 0 < (q : ℝ) := by
    exact_mod_cast q.pos
  have hqinv_pos : 0 < qinv := by
    dsimp [qinv]
    exact inv_pos.mpr hq_pos_real
  have hqinv_lt : qinv < ρ / (8 * L) := by
    simpa [q, qinv] using hqNat_inv
  have hq_margin : L * (2 * qinv) < ρ / 4 := by
    have hmul :
        (2 * L) * qinv < (2 * L) * (ρ / (8 * L)) :=
      mul_lt_mul_of_pos_left hqinv_lt (mul_pos (by norm_num) hL_pos)
    have hcalc : (2 * L) * (ρ / (8 * L)) = ρ / 4 := by
      field_simp [ne_of_gt hL_pos]
      ring
    nlinarith
  let Bextra : Finset E.Group :=
    (E.data.largeSpectrumGenerators q).image Neg.neg
  obtain ⟨Q, hQ, hlower, _hQdensity_pos, hQdensity_ge⟩ :=
    E.exists_compactSmoothReal_cliqueDensity_pos_and_fejerPairCoeffLowerBound
      hℓ hη Bextra hqinv_pos
  let Merr : ℝ := max (2 * qinv) qinv
  have hMerr_eq : Merr = 2 * qinv := by
    dsimp [Merr]
    exact max_eq_left (by nlinarith [le_of_lt hqinv_pos])
  have hMerr_nonneg : 0 ≤ Merr := by
    rw [hMerr_eq]
    positivity
  have hMerr_margin : L * Merr < ρ / 4 := by
    simpa [Merr, hMerr_eq] using hq_margin
  have hthreshold_lt_limit :
      L * Merr <
        continuousCliqueDensity E.haar ℓ (E.compactSmoothReal Q) := by
    have hquarter_half : ρ / 4 < ρ / 2 := by nlinarith
    exact lt_of_lt_of_le (lt_trans hMerr_margin hquarter_half)
      (by simpa [ρ] using hQdensity_ge)
  have hdensity_eventually :
      ∀ᶠ n in atTop,
        L * Merr <
          (letI : Fact (S.p (E.φ n)).Prime := ⟨S.prime (E.φ n)⟩
           letI : NeZero (S.p (E.φ n)) := ⟨(S.prime (E.φ n)).ne_zero⟩
           finiteCliqueKernelDensity (p := S.p (E.φ n)) (ℓ := ℓ)
            (E.finiteSmooth Q n)).re := by
    have hconv :=
      E.finiteCliqueKernelDensity_finiteSmooth_re_tendsto_compactSmoothReal
        Q ℓ
    exact hconv.eventually (isOpen_Ioi.mem_nhds hthreshold_lt_limit)
  have hnorm_eventually := E.finiteSmooth_norm_le_one_eventually Q hQ
  have hspectral_eventually :
      ∀ᶠ n in atTop,
        (letI : NeZero (S.p (E.φ n)) := ⟨(S.prime (E.φ n)).ne_zero⟩;
          SpectralBound
            (fun z : ZMod (S.p (E.φ n)) =>
              indicatorC (S.T (E.φ n)) z - E.finiteSmooth Q n z)
            Merr) := by
    have hspec :=
      E.spectralBound_indicator_sub_finiteSmooth_eventually_of_lowerBound_neg
        q Q hQ hlower
    refine hspec.mono ?_
    intro n hn
    simpa [Merr, qinv] using hn
  have hall :
      ∀ᶠ n in atTop,
        (∀ z : ZMod (S.p (E.φ n)), ‖E.finiteSmooth Q n z‖ ≤ 1) ∧
        (letI : NeZero (S.p (E.φ n)) := ⟨(S.prime (E.φ n)).ne_zero⟩;
          SpectralBound
            (fun z : ZMod (S.p (E.φ n)) =>
              indicatorC (S.T (E.φ n)) z - E.finiteSmooth Q n z)
            Merr) ∧
        L * Merr <
          (letI : Fact (S.p (E.φ n)).Prime := ⟨S.prime (E.φ n)⟩
           letI : NeZero (S.p (E.φ n)) := ⟨(S.prime (E.φ n)).ne_zero⟩
           finiteCliqueKernelDensity (p := S.p (E.φ n)) (ℓ := ℓ)
            (E.finiteSmooth Q n)).re :=
    hnorm_eventually.and (hspectral_eventually.and hdensity_eventually)
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp hall
  rcases hN N le_rfl with ⟨hnorm, hspectral, hdensity⟩
  haveI : Fact (S.p (E.φ N)).Prime := ⟨S.prime (E.φ N)⟩
  haveI : NeZero (S.p (E.φ N)) := ⟨(S.prime (E.φ N)).ne_zero⟩
  have hdensity' :
      ((ℓ * ℓ : ℕ) : ℝ) * Merr <
        (finiteCliqueKernelDensity (p := S.p (E.φ N)) (ℓ := ℓ)
          (E.finiteSmooth Q N)).re := by
    simpa [L] using hdensity
  have hclique :
      ∃ C : Finset (ZMod (S.p (E.φ N))),
        C.card = ℓ ∧ CliqueInCayley (S.T (E.φ N)) C :=
    exists_clique_of_spectral_density_transfer_sq
      (T := S.T (E.φ N))
      (g := E.finiteSmooth Q N)
      (M := Merr)
      (S.T_sym (E.φ N))
      (S.T_zero (E.φ N))
      hMerr_nonneg
      hnorm
      hspectral
      hdensity'
  exact S.no_clique (E.φ N) hclique

end

end Erdos42.CompactCayley


/-! =============================================================
    Section from: Erdos/P42/CompactCayley/CliqueAxiom.lean
    ============================================================= -/

/-
Erdős Problem 42 — Route B trust boundary: compact Cayley clique theorem.

Theorem 2.1 of `erdos42_compact_sidon_clean.pdf` (Google Drive link in
`forum.md`). A dense symmetric Cayley graph on `ZMod p`, with `0 ∉ T`
and small nontrivial Fourier coefficients (upper bound), contains a clique of
any prescribed size for all sufficiently large primes.

Mathematically: classical, unconditional. The compact-Cayley PDF proves it via
Fourier extraction (Lemma 2.2), equidistribution of finite lifts (2.3), basic
limit properties (2.4), spectral cut-norm control (2.5), counting convergence
(2.6), and clique forcing on connected compact groups (2.7).

This file now closes the former Route B trust boundary by deriving the compact
Cayley clique theorem from the axiom-free countersequence contradiction.
-/


namespace Erdos42

namespace CompactCayley

/-- **Compact Cayley clique theorem (compact PDF Theorem 2.1).** Trust
boundary for Route B. For every clique size `ℓ ≥ 2` and every density `η > 0`,
there exists `ε > 0` such that for all sufficiently large primes `p`, every
symmetric `T ⊆ ZMod p` with `0 ∉ T`, density `≥ η`, and Fourier upper bound
`≤ ε` (at every nontrivial character) contains an `ℓ`-clique in its Cayley
graph. -/
theorem compact_cayley_clique
    (ℓ : ℕ) (η : ℝ) (_hℓ : 2 ≤ ℓ) (_hη : 0 < η) :
    ∃ ε : ℝ, 0 < ε ∧
    ∃ p₀ : ℕ, ∀ p : ℕ, [Fact p.Prime] → p₀ < p →
    ∀ T : Finset (ZMod p),
      SymmetricFinset T →
      (0 : ZMod p) ∉ T →
      η * (p : ℝ) ≤ (T.card : ℝ) →
      FourierUpperIndicator T ε →
      ∃ C : Finset (ZMod p),
        C.card = ℓ ∧ CliqueInCayley T C := by
  classical
  by_contra hfail
  have hexplicit_fail : ¬ CompactCayleyCliqueStatementExplicit ℓ η := by
    intro hexplicit
    exact hfail (compactCayleyCliqueStatement_from_explicit hexplicit)
  obtain ⟨S, _⟩ :=
    exists_cayleyCounterSeq_of_not_compactCayleyCliqueStatementExplicit
      hexplicit_fail
  exact S.false _hℓ _hη

end CompactCayley

end Erdos42


/-! =============================================================
    Section from: Erdos/P42/CompactCayley/Main.lean
    ============================================================= -/

/-
Erdős Problem 42 — Route B final assembly.

This is the compact-Cayley downstream file that imports the proved
`compact_cayley_clique` theorem. The finite allowed-difference Fourier
estimates and greedy Sidon extraction stay in `FiniteReduction.lean`, outside
the compact-Cayley namespace, so Route A can reuse them independently.
-/


namespace Erdos42.CompactCayley

open Finset Erdos42

/-! ## Final assembly: Theorem 1.1 from `compact_cayley_clique` -/

/-- **Theorem 1.1, Route B.** For every `M ≥ 1`, there is `N₀` such that for
all `N ≥ N₀` and every non-empty Sidon `A ⊆ [1, N] ⊂ ℤ`, there is a Sidon
`B ⊆ [1, N]` with `|B| = M` and no nonzero common difference, using the
proved compact-Cayley clique theorem. -/
theorem theorem_1_1_from_compact_cayley
    (M : ℕ) (_hM : 1 ≤ M) :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      ∀ A : Finset ℤ,
        (∀ a ∈ A, 1 ≤ a ∧ a ≤ (N : ℤ)) → IsSidonInt A → A.Nonempty →
        ∃ B : Finset ℤ,
          (∀ b ∈ B, 1 ≤ b ∧ b ≤ (N : ℤ)) ∧
          IsSidonInt B ∧ B.card = M ∧
          AvoidsNonzeroDiff A B := by
  classical
  let R := greedySidonThreshold M
  have hRpos : 0 < R := by
    dsimp [R, greedySidonThreshold]
    omega
  have hCliqueSize : 2 ≤ 8 * R := by omega
  obtain ⟨ε, hεpos, p₀, hcompact⟩ :=
    compact_cayley_clique (8 * R) (1 / 2 : ℝ) hCliqueSize (by norm_num)
  obtain ⟨Nε, hNε⟩ := sidon_card_minus_one_div_prime_eventually_small ε hεpos
  refine ⟨max (p₀ + 1) Nε, ?_⟩
  intro N hN A hAint hSidon _hAnonempty
  have hNpos : 0 < N := by omega
  obtain ⟨p, hpprime, hpgt, hple⟩ :=
    Nat.exists_prime_lt_and_le_two_mul (4 * N) (by omega)
  haveI : Fact p.Prime := ⟨hpprime⟩
  have hp₀lt : p₀ < p := by omega
  have hpN : N < p := by omega
  have hpupper : p < 8 * N := by
    have hple' : p ≤ 8 * N := by omega
    have hpne2 : p ≠ 2 := by omega
    have hpodd : Odd p := hpprime.odd_of_ne_two hpne2
    have hpne : p ≠ 8 * N := by
      intro hpeq
      have heven : Even p := by
        rw [hpeq, even_iff_two_dvd]
        exact ⟨4 * N, by ring⟩
      exact (Nat.not_even_iff_odd.mpr hpodd) heven
    omega
  let T : Finset (ZMod p) := allowedDiffSetMod p A
  have hT_sym : SymmetricFinset T := by
    simpa [T] using allowedDiffSetMod_symmetric p A
  have hT_zero : (0 : ZMod p) ∉ T := by
    simpa [T] using zero_notMem_allowedDiffSetMod p A
  have hT_density : (1 / 2 : ℝ) * p ≤ (T.card : ℝ) := by
    simpa [T] using allowedDiffSetMod_density (p := p) (N := N) hpgt A hAint hSidon
  have hsmall : ((A.card - 1 : ℕ) : ℝ) / p ≤ ε :=
    hNε N p (by omega) hpgt A hAint hSidon
  have hT_fourier : FourierUpperIndicator T ε := by
    simpa [T] using
      allowedDiffs_fourier_upper (p := p) (N := N) hpgt A hAint hSidon ε hsmall
  obtain ⟨C, hCcard, hCclique⟩ :=
    hcompact p hp₀lt T hT_sym hT_zero hT_density hT_fourier
  obtain ⟨s, hs⟩ :=
    exists_large_intersection_cyclicInterval (p := p) (N := N) (R := R)
      hpN C (by simpa [R] using hCcard) hpupper
  let X : Finset ℤ := intervalLiftSet p N s C
  have hXcard : R ≤ X.card := by
    dsimp [X]
    rw [intervalLiftSet_card_eq hpN]
    exact hs
  obtain ⟨B, hBX, hBcard, hBsidon⟩ := exists_sidon_subset_of_card_ge M X hXcard
  refine ⟨B, ?_, hBsidon, hBcard, ?_⟩
  · intro b hb
    rcases mem_intervalLiftSet.mp (hBX hb) with ⟨i, hiN, _hiC, rfl⟩
    constructor <;> omega
  · intro d hdA hdB
    rw [mem_diffFinset] at hdA hdB
    rcases hdA with ⟨a₁, ha₁, a₂, ha₂, rfl⟩
    rcases hdB with ⟨b₁, hb₁, b₂, hb₂, hbDiff⟩
    by_cases hzero : a₁ - a₂ = 0
    · exact hzero
    · exfalso
      rcases mem_intervalLiftSet.mp (hBX hb₁) with ⟨i₁, hi₁N, hi₁C, hb₁eq⟩
      rcases mem_intervalLiftSet.mp (hBX hb₂) with ⟨i₂, hi₂N, hi₂C, hb₂eq⟩
      have hbne : b₁ ≠ b₂ := by
        intro hb
        apply hzero
        rw [hb] at hbDiff
        linarith
      have hine : i₁ ≠ i₂ := by
        intro hi
        apply hbne
        rw [hb₁eq, hb₂eq, hi]
      let y₁ : ZMod p := s + (i₁ : ZMod p)
      let y₂ : ZMod p := s + (i₂ : ZMod p)
      have hyne : y₁ ≠ y₂ := by
        intro hy
        apply hine
        apply nat_eq_of_zmod_eq_of_lt
          (Nat.lt_trans hi₁N hpN) (Nat.lt_trans hi₂N hpN)
        apply add_left_cancel (a := s)
        simpa [y₁, y₂] using hy
      have hallowed : y₁ - y₂ ∈ T := hCclique y₁ hi₁C y₂ hi₂C hyne
      have hyDiff : y₁ - y₂ = ((a₁ - a₂ : ℤ) : ZMod p) := by
        calc
          y₁ - y₂ = (i₁ : ZMod p) - (i₂ : ZMod p) := by
            simp [y₁, y₂]
          _ = ((b₁ - b₂ : ℤ) : ZMod p) := by
            rw [hb₁eq, hb₂eq]
            norm_num
          _ = ((a₁ - a₂ : ℤ) : ZMod p) := by
            rw [hbDiff]
      have hcast : ((a₁ - a₂ : ℤ) : ZMod p) ∈ allowedDiffSetMod p A := by
        simpa [T, hyDiff] using hallowed
      rw [allowedDiffSetMod, Finset.mem_filter] at hcast
      exact hcast.2.2 a₁ ha₁ a₂ ha₂ rfl

end Erdos42.CompactCayley


/-! =============================================================
    FC bridge: public `Set ℕ` wrapper + FC iff form (Route B)
    ============================================================= -/

namespace Erdos42

open Filter Set
open scoped Pointwise

/-! ## §1 FC-aligned Sidon predicate over `Set ℕ` -/

/-- `A ⊆ ℕ` is Sidon iff every additive collision is trivial. Matches the FC
skeleton's definition. -/
def IsSidon (A : Set ℕ) : Prop :=
  ∀ ⦃a₁⦄, a₁ ∈ A → ∀ ⦃a₂⦄, a₂ ∈ A → ∀ ⦃a₃⦄, a₃ ∈ A → ∀ ⦃a₄⦄, a₄ ∈ A →
    a₁ + a₂ = a₃ + a₄ → (a₁ = a₃ ∧ a₂ = a₄) ∨ (a₁ = a₄ ∧ a₂ = a₃)

/-- The FC `IsMaximalSidonSetIn` predicate. -/
def IsMaximalSidonSetIn (A : Set ℕ) (N : ℕ) : Prop :=
  A ⊆ Set.Icc 1 N ∧ IsSidon A ∧
    ∀ x ∈ Set.Icc 1 N, x ∉ A → ¬ IsSidon (insert x A)

/-! ## §2 Bridge `Finset ℤ` ↔ `Set ℕ` for Sidon sets in `[1, N]` -/

theorem isSidonInt_of_isSidon
    {A : Set ℕ} {N : ℕ} (hA : A ⊆ Set.Icc 1 N) (hSidon : IsSidon A) :
    ∃ A' : Finset ℤ,
      (∀ a ∈ A', 1 ≤ a ∧ a ≤ (N : ℤ)) ∧ IsSidonInt A' ∧
      (A.ncard = A'.card) ∧
      (∀ x : ℕ, x ∈ A ↔ ((x : ℤ) ∈ A')) := by
  classical
  let An : Finset ℕ := (Finset.Icc 1 N).filter (fun n : ℕ => n ∈ A)
  let A' : Finset ℤ := An.image (fun n : ℕ => (n : ℤ))
  have hAn_mem : ∀ x : ℕ, x ∈ An ↔ x ∈ A := by
    intro x
    constructor
    · intro hx
      change x ∈ (Finset.Icc 1 N).filter (fun n : ℕ => n ∈ A) at hx
      rw [Finset.mem_filter] at hx
      exact hx.2
    · intro hx
      have hxIcc : x ∈ Finset.Icc 1 N := by
        rw [Finset.mem_Icc]
        exact hA hx
      change x ∈ (Finset.Icc 1 N).filter (fun n : ℕ => n ∈ A)
      rw [Finset.mem_filter]
      exact ⟨hxIcc, hx⟩
  have hA'_mem_nat : ∀ x : ℕ, ((x : ℤ) ∈ A') ↔ x ∈ A := by
    intro x
    constructor
    · intro hx
      change (x : ℤ) ∈ An.image (fun n : ℕ => (n : ℤ)) at hx
      rw [Finset.mem_image] at hx
      rcases hx with ⟨y, hy, hyx⟩
      have hyx_nat : y = x := by exact_mod_cast hyx
      rw [← hyx_nat]
      exact (hAn_mem y).mp hy
    · intro hx
      change (x : ℤ) ∈ An.image (fun n : ℕ => (n : ℤ))
      rw [Finset.mem_image]
      exact ⟨x, (hAn_mem x).mpr hx, rfl⟩
  refine ⟨A', ?_, ?_, ?_, ?_⟩
  · intro a ha
    change a ∈ An.image (fun n : ℕ => (n : ℤ)) at ha
    rw [Finset.mem_image] at ha
    rcases ha with ⟨x, hx, rfl⟩
    have hxA : x ∈ A := (hAn_mem x).mp hx
    exact_mod_cast hA hxA
  · intro a₁ ha₁ a₂ ha₂ a₃ ha₃ a₄ ha₄ hsum
    change a₁ ∈ An.image (fun n : ℕ => (n : ℤ)) at ha₁
    change a₂ ∈ An.image (fun n : ℕ => (n : ℤ)) at ha₂
    change a₃ ∈ An.image (fun n : ℕ => (n : ℤ)) at ha₃
    change a₄ ∈ An.image (fun n : ℕ => (n : ℤ)) at ha₄
    rw [Finset.mem_image] at ha₁ ha₂ ha₃ ha₄
    rcases ha₁ with ⟨n₁, hn₁, rfl⟩
    rcases ha₂ with ⟨n₂, hn₂, rfl⟩
    rcases ha₃ with ⟨n₃, hn₃, rfl⟩
    rcases ha₄ with ⟨n₄, hn₄, rfl⟩
    have hsum_nat : n₁ + n₂ = n₃ + n₄ := by exact_mod_cast hsum
    rcases hSidon ((hAn_mem n₁).mp hn₁) ((hAn_mem n₂).mp hn₂)
        ((hAn_mem n₃).mp hn₃) ((hAn_mem n₄).mp hn₄) hsum_nat with h | h
    · exact Or.inl ⟨by exact_mod_cast h.1, by exact_mod_cast h.2⟩
    · exact Or.inr ⟨by exact_mod_cast h.1, by exact_mod_cast h.2⟩
  · have hAset : A = (An : Set ℕ) := by
      ext x
      exact (hAn_mem x).symm
    have hAcard : A.ncard = An.card := by
      rw [hAset, Set.ncard_coe_finset]
    have hA'card : A'.card = An.card := by
      change (An.image (fun n : ℕ => (n : ℤ))).card = An.card
      apply Finset.card_image_of_injOn
      intro x _hx y _hy hxy
      exact Int.ofNat_injective hxy
    exact hAcard.trans hA'card.symm
  · intro x
    exact (hA'_mem_nat x).symm

/-! ## §3 Theorem 1.1 (Set ℕ form, Route B) -/

theorem theorem_1_1_via_cayley :
    ∀ M : ℕ, 1 ≤ M → ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      ∀ A : Set ℕ, A ⊆ Set.Icc 1 N → IsSidon A → A.Nonempty →
        ∃ B : Set ℕ, B ⊆ Set.Icc 1 N ∧ IsSidon B ∧ B.ncard = M ∧
          ((A - A) ∩ (B - B) : Set ℕ) = {0} := by
  intro M hM
  classical
  obtain ⟨N₀, hN₀⟩ := CompactCayley.theorem_1_1_from_compact_cayley M hM
  refine ⟨N₀, ?_⟩
  intro N hN A hAint hSidon hAnonempty
  obtain ⟨A', hA'int, hA'sidon, _hAcard, hA'mem⟩ :=
    isSidonInt_of_isSidon (A := A) (N := N) hAint hSidon
  have hA'nonempty : A'.Nonempty := by
    obtain ⟨a, ha⟩ := hAnonempty
    exact ⟨(a : ℤ), (hA'mem a).mp ha⟩
  obtain ⟨B', hB'int, hB'sidon, hB'card, hAvoid⟩ :=
    hN₀ N hN A' hA'int hA'sidon hA'nonempty
  let Bn : Finset ℕ := B'.image Int.toNat
  let B : Set ℕ := (Bn : Set ℕ)
  have hB'_nonneg : ∀ b ∈ B', 0 ≤ b := by
    intro b hb
    exact le_trans (by norm_num) (hB'int b hb).1
  have hB'_mem_nat : ∀ x : ℕ, x ∈ B ↔ ((x : ℤ) ∈ B') := by
    intro x
    constructor
    · intro hx
      change x ∈ Bn at hx
      change x ∈ B'.image Int.toNat at hx
      rw [Finset.mem_image] at hx
      rcases hx with ⟨z, hz, hzx⟩
      have hz_nonneg : 0 ≤ z := hB'_nonneg z hz
      have hz_cast : (z.toNat : ℤ) = z := Int.toNat_of_nonneg hz_nonneg
      rw [← hzx, hz_cast]
      exact hz
    · intro hx
      change x ∈ Bn
      change x ∈ B'.image Int.toNat
      rw [Finset.mem_image]
      refine ⟨(x : ℤ), hx, ?_⟩
      simp
  have hBn_card : Bn.card = B'.card := by
    change (B'.image Int.toNat).card = B'.card
    apply Finset.card_image_of_injOn
    intro x hx y hy hxy
    have hx_nonneg : 0 ≤ x := hB'_nonneg x hx
    have hy_nonneg : 0 ≤ y := hB'_nonneg y hy
    calc
      x = (x.toNat : ℤ) := (Int.toNat_of_nonneg hx_nonneg).symm
      _ = (y.toNat : ℤ) := by rw [hxy]
      _ = y := Int.toNat_of_nonneg hy_nonneg
  have hBn_cardM : Bn.card = M := by
    rw [hBn_card, hB'card]
  have hB_nonempty : B.Nonempty := by
    have hBn_pos : 0 < Bn.card := by omega
    obtain ⟨b, hb⟩ := Finset.card_pos.mp hBn_pos
    exact ⟨b, hb⟩
  refine ⟨B, ?_, ?_, ?_, ?_⟩
  · intro b hb
    have hb' : (b : ℤ) ∈ B' := (hB'_mem_nat b).mp hb
    have hb_bounds := hB'int (b : ℤ) hb'
    exact_mod_cast hb_bounds
  · intro b₁ hb₁ b₂ hb₂ b₃ hb₃ b₄ hb₄ hsum
    have hb₁' : (b₁ : ℤ) ∈ B' := (hB'_mem_nat b₁).mp hb₁
    have hb₂' : (b₂ : ℤ) ∈ B' := (hB'_mem_nat b₂).mp hb₂
    have hb₃' : (b₃ : ℤ) ∈ B' := (hB'_mem_nat b₃).mp hb₃
    have hb₄' : (b₄ : ℤ) ∈ B' := (hB'_mem_nat b₄).mp hb₄
    have hsum_int : (b₁ : ℤ) + (b₂ : ℤ) = (b₃ : ℤ) + (b₄ : ℤ) := by
      exact_mod_cast hsum
    rcases hB'sidon hb₁' hb₂' hb₃' hb₄' hsum_int with h | h
    · exact Or.inl ⟨by exact_mod_cast h.1, by exact_mod_cast h.2⟩
    · exact Or.inr ⟨by exact_mod_cast h.1, by exact_mod_cast h.2⟩
  · rw [Set.ncard_coe_finset, hBn_cardM]
  · ext d
    constructor
    · intro hd
      rw [Set.mem_inter_iff] at hd
      rcases hd with ⟨hdA, hdB⟩
      rw [Set.mem_sub] at hdA hdB
      rcases hdA with ⟨a₁, ha₁, a₂, ha₂, haDiff⟩
      rcases hdB with ⟨b₁, hb₁, b₂, hb₂, hbDiff⟩
      rw [Set.mem_singleton_iff]
      by_cases hd0 : d = 0
      · exact hd0
      · exfalso
        have hDiffA_int : (a₁ : ℤ) - (a₂ : ℤ) = (d : ℤ) := by omega
        have hDiffB_int : (b₁ : ℤ) - (b₂ : ℤ) = (d : ℤ) := by omega
        have hdA' : (d : ℤ) ∈ DiffFinset A' A' := by
          rw [mem_diffFinset]
          exact ⟨(a₁ : ℤ), (hA'mem a₁).mp ha₁, (a₂ : ℤ), (hA'mem a₂).mp ha₂,
            hDiffA_int⟩
        have hdB' : (d : ℤ) ∈ DiffFinset B' B' := by
          rw [mem_diffFinset]
          exact ⟨(b₁ : ℤ), (hB'_mem_nat b₁).mp hb₁, (b₂ : ℤ), (hB'_mem_nat b₂).mp hb₂,
            hDiffB_int⟩
        have hd_int_zero : (d : ℤ) = 0 := hAvoid (d : ℤ) hdA' hdB'
        have : d = 0 := by exact_mod_cast hd_int_zero
        exact hd0 this
    · intro hd
      rw [Set.mem_singleton_iff] at hd
      subst d
      rw [Set.mem_inter_iff]
      constructor
      · rw [Set.mem_sub]
        obtain ⟨a, ha⟩ := hAnonempty
        exact ⟨a, ha, a, ha, by simp⟩
      · rw [Set.mem_sub]
        obtain ⟨b, hb⟩ := hB_nonempty
        exact ⟨b, hb, b, hb, by simp⟩

/-! ## §4 FC iff form (Route B) -/

theorem erdos_42_via_cayley :
    True ↔ ∀ M ≥ 1, ∀ᶠ N in atTop, ∀ (A : Set ℕ) (_ : IsMaximalSidonSetIn A N),
      ∃ (B : Set ℕ), B ⊆ Set.Icc 1 N ∧ IsSidon B ∧ B.ncard = M ∧
        ((A - A) ∩ (B - B) : Set ℕ) = {0} := by
  constructor
  · intro _ M hM
    obtain ⟨N₀, hN₀⟩ := theorem_1_1_via_cayley M hM
    refine eventually_atTop.2 ⟨max N₀ 1, ?_⟩
    intro N hN A hMax
    have hN₀le : N₀ ≤ N := (Nat.le_max_left N₀ 1).trans hN
    have hNpos : 1 ≤ N := (Nat.le_max_right N₀ 1).trans hN
    rcases hMax with ⟨hAint, hSidon, hMaximal⟩
    have hAnonempty : A.Nonempty := by
      by_contra hne
      have hAempty : A = ∅ := Set.not_nonempty_iff_eq_empty.mp hne
      have h1Icc : 1 ∈ Set.Icc 1 N := ⟨le_rfl, hNpos⟩
      have h1notA : 1 ∉ A := by simp [hAempty]
      have hnot := hMaximal 1 h1Icc h1notA
      apply hnot
      rw [hAempty]
      intro a₁ ha₁ a₂ ha₂ a₃ ha₃ a₄ ha₄ _hsum
      simp only [Set.mem_insert_iff, Set.mem_empty_iff_false, or_false] at ha₁ ha₂ ha₃ ha₄
      subst a₁
      subst a₂
      subst a₃
      subst a₄
      exact Or.inl ⟨rfl, rfl⟩
    exact hN₀ N hN₀le A hAint hSidon hAnonempty
  · intro _
    trivial

/-! ## §5 FC-shape variant (matches FC's `∃ᵉ` and FC's local Sidon predicates) -/

namespace FormalConjecturesShape

universe u

/-- Local stand-in for FC's explicit-exists binder `∃ᵉ`. -/
def ExplicitExists {α : Sort u} (P : α → Prop) : Prop :=
  ∃ x, P x

theorem explicitExists_iff_exists {α : Sort u} {P : α → Prop} :
    ExplicitExists P ↔ ∃ x, P x := by
  rfl

/-- FC-shaped Sidon predicate. Definitionally equal to `Erdos42.IsSidon`. -/
def IsSidon (A : Set ℕ) : Prop :=
  ∀ ⦃a₁⦄, a₁ ∈ A → ∀ ⦃a₂⦄, a₂ ∈ A → ∀ ⦃a₃⦄, a₃ ∈ A → ∀ ⦃a₄⦄, a₄ ∈ A →
    a₁ + a₂ = a₃ + a₄ → (a₁ = a₃ ∧ a₂ = a₄) ∨ (a₁ = a₄ ∧ a₂ = a₃)

theorem isSidon_iff_local (A : Set ℕ) :
    IsSidon A ↔ Erdos42.IsSidon A := by
  rfl

/-- FC-shaped maximal Sidon predicate. Definitionally equal to
`Erdos42.IsMaximalSidonSetIn`. -/
def IsMaximalSidonSetIn (A : Set ℕ) (N : ℕ) : Prop :=
  A ⊆ Set.Icc 1 N ∧ IsSidon A ∧
    ∀ x ∈ Set.Icc 1 N, x ∉ A → ¬ IsSidon (insert x A)

theorem isMaximalSidonSetIn_iff_local (A : Set ℕ) (N : ℕ) :
    IsMaximalSidonSetIn A N ↔ Erdos42.IsMaximalSidonSetIn A N := by
  rfl

/-- The literal RHS shape that FC uses for `erdos_42` (with `∃ᵉ`). -/
def erdos42RHS : Prop :=
  ∀ M ≥ 1, ∀ᶠ N in atTop, ∀ (A : Set ℕ) (_ : IsMaximalSidonSetIn A N),
    ExplicitExists fun (B : Set ℕ) => B ⊆ Set.Icc 1 N ∧ IsSidon B ∧ B.ncard = M ∧
      ((A - A) ∩ (B - B) : Set ℕ) = {0}

/-- Our local-shape RHS, using `∃` and the local predicates. -/
def localRHS : Prop :=
  ∀ M ≥ 1, ∀ᶠ N in atTop, ∀ (A : Set ℕ) (_ : Erdos42.IsMaximalSidonSetIn A N),
    ∃ (B : Set ℕ), B ⊆ Set.Icc 1 N ∧ Erdos42.IsSidon B ∧ B.ncard = M ∧
      ((A - A) ∩ (B - B) : Set ℕ) = {0}

theorem erdos42RHS_iff_localRHS :
    erdos42RHS ↔ localRHS := by
  unfold erdos42RHS localRHS ExplicitExists IsMaximalSidonSetIn IsSidon
    Erdos42.IsMaximalSidonSetIn Erdos42.IsSidon
  rfl

/-- **Formal-conjectures shape for #42 (Route B).** Matches FC's literal
statement after `answer := True` and `∃ᵉ ↦ ExplicitExists`. Mathlib core only. -/
theorem erdos_42_via_cayley :
    True ↔ erdos42RHS :=
  Iff.trans Erdos42.erdos_42_via_cayley erdos42RHS_iff_localRHS.symm

end FormalConjecturesShape

end Erdos42

/-! ## Axiom audit -/

#print axioms Erdos42.CompactCayley.compact_cayley_clique
-- 'Erdos42.CompactCayley.compact_cayley_clique' depends on axioms: [propext, Classical.choice,
-- Quot.sound]
#print axioms Erdos42.CompactCayley.theorem_1_1_from_compact_cayley
-- 'Erdos42.CompactCayley.theorem_1_1_from_compact_cayley' depends on axioms: [propext,
-- Classical.choice, Quot.sound]
#print axioms Erdos42.theorem_1_1_via_cayley
-- 'Erdos42.theorem_1_1_via_cayley' depends on axioms: [propext, Classical.choice, Quot.sound]
#print axioms Erdos42.erdos_42_via_cayley
-- 'Erdos42.erdos_42_via_cayley' depends on axioms: [propext, Classical.choice, Quot.sound]
#print axioms Erdos42.FormalConjecturesShape.erdos_42_via_cayley
-- 'Erdos42.FormalConjecturesShape.erdos_42_via_cayley' depends on axioms: [propext,
-- Classical.choice, Quot.sound]
