import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Data.Set.Card
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Integral binary quadratic forms and their represented-value count

The counting function counts values, not representations. In particular,
changes of integral coordinates preserve it without any multiplicity factor.
-/

/-- An (integral) binary quadratic form `f(X,Y) = a X^2 + b X Y + c Y^2`. -/
structure BinQuadForm where
  a : ℤ
  b : ℤ
  c : ℤ

namespace BinQuadForm

/-- Evaluate the form on integer inputs. -/
def eval (f : BinQuadForm) (x y : ℤ) : ℤ :=
  f.a * x * x + f.b * x * y + f.c * y * y

/-- Discriminant `Δ = b^2 - 4ac`. -/
def discr (f : BinQuadForm) : ℤ :=
  f.b * f.b - 4 * f.a * f.c

/-- `f` is primitive if `gcd(a,b,c) = 1`. -/
def Primitive (f : BinQuadForm) : Prop :=
  Int.gcd f.a (Int.gcd f.b f.c) = 1

/--
A convenient (sufficient) positive-definiteness condition for integral binary quadratic forms:
`a > 0` and discriminant is negative.
(For integer forms this is equivalent to positive definiteness over `ℝ`.)
-/
def PosDef (f : BinQuadForm) : Prop :=
  0 < f.a ∧ f.discr < 0

/--
Counting function `B_f(x)`: number of *natural numbers* `n ≤ x` represented by `f`.
(Here “represented” means `∃ u v : ℤ, f(u,v) = n`.)
-/
noncomputable def B (f : BinQuadForm) (x : ℝ) : ℕ :=
  Nat.card {n : ℕ | (n : ℝ) ≤ x ∧ ∃ u v : ℤ, f.eval u v = (n : ℤ)}

theorem eval_zero_zero (f : BinQuadForm) : f.eval 0 0 = 0 := by
  simp [eval]

/-- Completing the square in integral coordinates. -/
theorem four_mul_a_mul_eval (f : BinQuadForm) (u v : ℤ) :
    4 * f.a * f.eval u v = (2 * f.a * u + f.b * v) ^ 2 - f.discr * v ^ 2 := by
  simp only [eval, discr]
  ring

theorem eval_mul (f : BinQuadForm) (k u v : ℤ) :
    f.eval (k * u) (k * v) = k ^ 2 * f.eval u v := by
  simp only [eval]
  ring

theorem PosDef.discr_nonsquare {f : BinQuadForm} (hf : f.PosDef) :
    ¬ ∃ z : ℤ, z * z = f.discr := by
  rintro ⟨z, hz⟩
  exact (mul_self_nonneg z).not_gt (hz ▸ hf.2)

theorem PosDef.eval_nonneg {f : BinQuadForm} (hf : f.PosDef) (u v : ℤ) :
    0 ≤ f.eval u v := by
  have h := f.four_mul_a_mul_eval u v
  have hprod : 0 ≤ -f.discr * v ^ 2 := mul_nonneg (neg_nonneg.mpr hf.2.le) (sq_nonneg v)
  have ha : 0 < 4 * f.a := mul_pos (by norm_num) hf.1
  have hnonneg : 0 ≤ 4 * f.a * f.eval u v := by
    rw [h]
    linarith [sq_nonneg (2 * f.a * u + f.b * v)]
  exact (mul_nonneg_iff_of_pos_left ha).mp hnonneg

theorem PosDef.eval_eq_zero_iff {f : BinQuadForm} (hf : f.PosDef) (u v : ℤ) :
    f.eval u v = 0 ↔ u = 0 ∧ v = 0 := by
  constructor
  · intro hzero
    have h := f.four_mul_a_mul_eval u v
    rw [hzero, mul_zero] at h
    have hv : v = 0 := by
      by_contra hv
      have hpos : 0 < -f.discr * v ^ 2 :=
        mul_pos (neg_pos.mpr hf.2) (sq_pos_of_ne_zero hv)
      linarith [sq_nonneg (2 * f.a * u + f.b * v)]
    refine ⟨?_, hv⟩
    have hu : (2 * f.a * u) ^ 2 = 0 := by simpa [hv] using h.symm
    have hmul : 2 * f.a * u = 0 := sq_eq_zero_iff.mp hu
    exact (mul_eq_zero.mp hmul).resolve_left (mul_ne_zero (by norm_num) hf.1.ne')
  · rintro ⟨rfl, rfl⟩
    exact f.eval_zero_zero

/-- Bounded represented values form a finite set, independently of definiteness. -/
theorem finite_counted_values (f : BinQuadForm) (x : ℝ) :
    Set.Finite {n : ℕ | (n : ℝ) ≤ x ∧ ∃ u v : ℤ, f.eval u v = (n : ℤ)} := by
  apply (Finset.finite_toSet (Finset.range (⌊x⌋₊ + 1))).subset
  intro n hn
  exact Finset.mem_range.mpr (Nat.lt_succ_of_le (Nat.le_floor hn.1))

open scoped Classical in
/-- A finite-set presentation of the exact counting function. -/
theorem B_eq_card_filter (f : BinQuadForm) {x : ℝ} (hx : 0 ≤ x) :
    f.B x = ((Finset.range (⌊x⌋₊ + 1)).filter
      (fun n : ℕ => ∃ u v : ℤ, f.eval u v = (n : ℤ))).card := by
  classical
  unfold B
  have hset : {n : ℕ | (n : ℝ) ≤ x ∧ ∃ u v : ℤ, f.eval u v = (n : ℤ)} =
      ↑((Finset.range (⌊x⌋₊ + 1)).filter
        (fun n : ℕ => ∃ u v : ℤ, f.eval u v = (n : ℤ))) := by
    ext n
    simp only [Set.mem_ofPred_eq, Finset.mem_coe, Finset.mem_filter,
      Finset.mem_range, Nat.lt_succ_iff, Nat.le_floor_iff hx]
  rw [hset, Nat.card_coe_set_eq, Set.ncard_coe_finset]

theorem B_eq_zero_of_neg (f : BinQuadForm) {x : ℝ} (hx : x < 0) : f.B x = 0 := by
  unfold B
  have hset : {n : ℕ | (n : ℝ) ≤ x ∧ ∃ u v : ℤ, f.eval u v = (n : ℤ)} = ∅ := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro n hn
    exact (Nat.cast_nonneg n).not_gt (hn.1.trans_lt hx)
  simp [hset]

theorem B_mono (f : BinQuadForm) : Monotone f.B := by
  intro x y hxy
  exact Set.ncard_le_ncard (fun n hn => ⟨hn.1.trans hxy, hn.2⟩)
    (f.finite_counted_values y)

theorem B_eq_of_represented_iff {f g : BinQuadForm}
    (h : ∀ n : ℕ, (∃ u v : ℤ, f.eval u v = (n : ℤ)) ↔
      ∃ u v : ℤ, g.eval u v = (n : ℤ)) : f.B = g.B := by
  funext x
  unfold B
  apply congrArg (fun s : Set ℕ => Nat.card s)
  exact Set.ext fun n => and_congr_right fun _ => h n

/-- Representation by the form is exactly representation by its completed-square
norm together with the original lattice congruence. -/
theorem represented_iff_norm_congruence (f : BinQuadForm) (ha : f.a ≠ 0) (n : ℤ) :
    (∃ u v : ℤ, f.eval u v = n) ↔
      ∃ z v : ℤ, (2 * f.a) ∣ z - f.b * v ∧
        z ^ 2 - f.discr * v ^ 2 = 4 * f.a * n := by
  constructor
  · rintro ⟨u, v, rfl⟩
    refine ⟨2 * f.a * u + f.b * v, v, ?_, (f.four_mul_a_mul_eval u v).symm⟩
    exact ⟨u, by ring⟩
  · rintro ⟨z, v, ⟨u, hu⟩, hnorm⟩
    have hz : z = 2 * f.a * u + f.b * v := by linarith
    refine ⟨u, v, ?_⟩
    apply mul_left_cancel₀ (mul_ne_zero (by norm_num : (4 : ℤ) ≠ 0) ha)
    rw [f.four_mul_a_mul_eval, ← hz, hnorm]

end BinQuadForm
