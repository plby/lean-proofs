module
public import Mathlib.Analysis.Asymptotics.Defs
public import Mathlib.Analysis.Normed.Group.Basic
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Topology.Algebra.InfiniteSum.Defs
import Mathlib.Analysis.CStarAlgebra.Basic
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.Real.Sqrt

/-!
## Sequences that grow subexponentially

These are common in power series, so we write some `fun_prop` support for fun.
-/

open Asymptotics
open Filter (atTop)

/-!
### Definition
-/

variable {X : Type} [Norm X]
variable {E : Type} [NormedAddCommGroup E]
variable {R : Type} [NormedRing R]

/-- A function `ℕ → X` is subexponential if it is `O(a ^ n)` for all `1 < a` -/
@[fun_prop] public structure Subexp (f : ℕ → X) : Prop where
  subexp : ∀ {a : ℝ}, 1 < a → f =O[atTop] fun n ↦ a ^ n

public lemma subexp_def (f : ℕ → X) : Subexp f ↔ ∀ {a : ℝ}, 1 < a → f =O[atTop] fun n ↦ a ^ n :=
  ⟨fun s ↦ s.subexp, fun s ↦ ⟨s⟩⟩

/-!
### For now, we only prove that polynomials are subexponential
-/

/-- Constants are subexponential -/
@[fun_prop] public lemma subexp_const (c : X) : Subexp (fun _ ↦ c) := by
  rw [subexp_def]
  intro a a1
  have a0 : 0 < a := by positivity
  refine IsBigO.trans_le (isBigO_const_one ℝ _ _) fun n ↦ ?_
  simp only [one_mem, CStarRing.norm_of_mem_unitary, norm_pow, Real.norm_eq_abs, abs_of_pos a0]
  bound

/-- The identity function is subexponential, real version -/
@[fun_prop] public lemma Real.subexp_natCast : Subexp (fun n : ℕ ↦ (n : ℝ)) := by
  rw [subexp_def]
  intro a a1
  exact (isLittleO_coe_const_pow_of_one_lt a1).isBigO

/-- Multiplication preserves subexponentiality -/
@[fun_prop] public lemma Subexp.mul {f g : ℕ → R} (fs : Subexp f) (gs : Subexp g) :
    Subexp (fun n ↦ f n * g n) := by
  rw [subexp_def] at fs gs ⊢
  intro a a1
  have a0 : 0 < a := by positivity
  have s1 : 1 < Real.sqrt a := by rwa [Real.lt_sqrt (by norm_num), one_pow]
  have m := (fs s1).mul (gs s1)
  simpa only [← mul_pow, ← pow_two √a, Real.sq_sqrt a0.le] using m

/-- Equivalence to the real case -/
public lemma subexp_iff_norm {f : ℕ → E} : Subexp f ↔ Subexp fun n ↦ ‖f n‖ := by
  simp only [subexp_def, isBigO_norm_left]

/-- Norms are subexponential -/
@[fun_prop] public lemma Subexp.norm {f : ℕ → E} (h : Subexp f) : Subexp fun n ↦ ‖f n‖ := by
  rwa [← subexp_iff_norm]

/-- The identity function is subexponential, general version -/
@[fun_prop] public lemma subexp_natCast [NormSMulClass ℤ R] : Subexp (fun n : ℕ ↦ (n : R)) := by
  simp only [subexp_iff_norm (E := R), norm_natCast_eq_mul_norm_one]
  fun_prop

/-- Addition preserves subexponentiality -/
@[fun_prop] public lemma Subexp.add {f g : ℕ → R} (fs : Subexp f) (gs : Subexp g) :
    Subexp (fun n ↦ f n + g n) := by
  rw [subexp_def] at fs gs ⊢
  exact fun a1 ↦ (fs a1).add (gs a1)

/-- Negation preserves subexponentiality -/
@[fun_prop] public lemma Subexp.neg {f : ℕ → E} (fs : Subexp f) : Subexp (fun n ↦ -f n) := by
  rw [subexp_iff_norm] at fs ⊢
  simpa only [norm_neg]

/-- Subtraction preserves subexponentiality -/
@[fun_prop] public lemma Subexp.sub {f g : ℕ → R} (fs : Subexp f) (gs : Subexp g) :
    Subexp (fun n ↦ f n - g n) := by
  simp only [sub_eq_add_neg]
  exact fs.add gs.neg

/-!
### Summability involving subexponential sequences
-/

/-- A subexponential times a decreasing exponential is bounded by a decreasing exponential -/
public lemma Subexp.le_exp {f : ℕ → E} (fs : Subexp f) (a : ℝ) (a0 : 0 ≤ a) (a1 : a < 1) :
    ∃ C, ∃ b, 0 < b ∧ b < 1 ∧ ∀ n, ‖f n‖ * a ^ n ≤ C * b ^ n := by
  by_cases az : a = 0
  · refine ⟨‖f 0‖, 1 / 2, by norm_num, by norm_num, ?_⟩
    intro n
    match n with
    | 0 => simp
    | n + 1 => simp [az]
  replace a0 : 0 < a := by positivity
  have s0 : 0 < Real.sqrt a := by positivity
  have s1 : Real.sqrt a < 1 := by rwa [Real.sqrt_lt a0.le (by norm_num), one_pow]
  set b := (Real.sqrt a)⁻¹
  have b1 : 1 < b := by simpa only [b, one_lt_inv₀ s0]
  have b0 : 0 < b := by positivity
  have o := (fs.norm.subexp b1).mul (isBigO_refl (fun n : ℕ ↦ a ^ n) atTop)
  rw [Asymptotics.isBigO_nat_atTop_iff] at o
  · obtain ⟨C,le⟩ := o
    refine ⟨C, b * a, by bound, ?_, ?_⟩
    · rw [← Real.sq_sqrt a0.le]
      simpa only [b, pow_two, ← mul_assoc, inv_mul_cancel₀ s0.ne', one_mul]
    · intro n
      simpa [abs_of_pos a0, abs_of_pos b0, ← mul_pow] using le n
  · intro n z
    contrapose z
    positivity

/-- Subexpential times a decreasing exponential is summable -/
public lemma summable_subexp_mul_pow {a : ℝ} (a0 : 0 ≤ a) (a1 : a < 1) {f : ℕ → ℝ}
    (fs : Subexp f := by fun_prop) : Summable fun n : ℕ ↦ f n * a ^ n := by
  obtain ⟨C,b,b0,b1,le⟩ := fs.le_exp a a0 a1
  refine Summable.of_norm_bounded (g := fun n ↦ C * b ^ n) ?_ ?_
  · exact (summable_geometric_of_lt_one (by bound) b1).mul_left _
  · intro n
    simpa [abs_of_nonneg a0] using le n
