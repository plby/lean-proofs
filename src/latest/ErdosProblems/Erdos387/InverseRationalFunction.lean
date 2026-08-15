/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos387.FiniteWeylInequality
import Mathlib.FieldTheory.Finite.Basic

/-!
# Cleared rational functions after reciprocal Weyl differencing

The mixed finite differences of `c/(a+x)` are represented recursively by a
numerator and a product denominator.  This is the algebraic input required
before applying a rational-function character-sum estimate.
-/

namespace Erdos387

namespace InverseRational

/-- Denominator obtained after the stored positive shifts. -/
noncomputable def denominator
    (q : ℕ) [NeZero q] (a : ZMod q) : List ℕ → ℕ → ZMod q
  | [], x => a + (x : ZMod q)
  | h :: hs, x =>
      denominator q a hs (x + h + 1) * denominator q a hs x

/-- Cleared numerator obtained after the stored positive shifts. -/
noncomputable def numerator
    (q : ℕ) [NeZero q] (c a : ZMod q) : List ℕ → ℕ → ZMod q
  | [], _x => c
  | h :: hs, x =>
      numerator q c a hs (x + h + 1) * denominator q a hs x -
        numerator q c a hs x * denominator q a hs (x + h + 1)

/-- The recursive denominator is nonzero at every point if and only if the
child denominator is nonzero at every point; only the forward implication
is needed in the induction below. -/
theorem child_denominator_ne_zero
    {q : ℕ} [NeZero q] [Fact q.Prime]
    (a : ZMod q) (h : ℕ) (hs : List ℕ)
    (hden : ∀ x, denominator q a (h :: hs) x ≠ 0) :
    ∀ x, denominator q a hs x ≠ 0 := by
  intro x
  have hx := hden x
  simp only [denominator] at hx
  exact (mul_ne_zero_iff.mp hx).2

/-- Away from its recursively listed poles, the iterated inverse phase is
the cleared numerator divided by the product denominator. -/
theorem iteratedInversePhase_eq_numerator_mul_inv_denominator
    {q : ℕ} [NeZero q] [Fact q.Prime]
    (c a : ZMod q) (hs : List ℕ)
    (hden : ∀ x, denominator q a hs x ≠ 0) (x : ℕ) :
    InverseWeyl.iteratedInversePhase q c a hs x =
      numerator q c a hs x * (denominator q a hs x)⁻¹ := by
  induction hs generalizing x with
  | nil => rfl
  | cons h hs ih =>
      have hchild : ∀ y, denominator q a hs y ≠ 0 :=
        child_denominator_ne_zero a h hs hden
      simp only [InverseWeyl.iteratedInversePhase, numerator, denominator]
      rw [ih hchild, ih hchild]
      field_simp [hchild]

/-- The one-step cleared numerator simplifies to the negative shift times
the original coefficient. -/
theorem numerator_singleton
    {q : ℕ} [NeZero q] (c a : ZMod q) (h x : ℕ) :
    numerator q c a [h] x = -c * ((h + 1 : ℕ) : ZMod q) := by
  simp only [numerator, denominator]
  push_cast
  ring

/-- The one-step denominator is the product of the two translated linear
factors. -/
theorem denominator_singleton
    {q : ℕ} [NeZero q] (a : ZMod q) (h x : ℕ) :
    denominator q a [h] x =
      (a + ((x + h + 1 : ℕ) : ZMod q)) *
        (a + (x : ZMod q)) := rfl

/-- The multiset of translated pole offsets produced by the successive
positive differences.  A list is used deliberately: coincident subset sums
give repeated linear factors in the cleared denominator. -/
def poleOffsets : List ℕ → List ℕ
  | [] => [0]
  | h :: hs =>
      (poleOffsets hs).map (fun v => v + h + 1) ++ poleOffsets hs

/-- After `j` differences there are exactly `2^j` pole factors, counted
with multiplicity. -/
theorem length_poleOffsets (hs : List ℕ) :
    (poleOffsets hs).length = 2 ^ hs.length := by
  induction hs with
  | nil => simp [poleOffsets]
  | cons h hs ih =>
      simpa [poleOffsets, ih, pow_succ, Nat.mul_comm, two_mul]

/-- The recursively defined denominator is exactly the product of the
translated affine factors indexed by `poleOffsets`. -/
theorem denominator_eq_poleOffsets_prod
    {q : ℕ} [NeZero q] (a : ZMod q) (hs : List ℕ) (x : ℕ) :
    denominator q a hs x =
      ((poleOffsets hs).map
        (fun v => a + ((x + v : ℕ) : ZMod q))).prod := by
  induction hs generalizing x with
  | nil => simp [denominator, poleOffsets]
  | cons h hs ih =>
      rw [denominator, poleOffsets, List.map_append, List.prod_append,
        ih, ih]
      congr 1
      simp only [List.map_map]
      apply congrArg List.prod
      apply List.map_congr_left
      intro v hv
      rw [show x + h + 1 + v = x + (v + h + 1) by omega]
      rfl

/-- Nonvanishing of the cleared denominator is equivalent to avoiding every
translated pole, including multiplicity. -/
theorem denominator_ne_zero_iff
    {q : ℕ} [NeZero q] [Fact q.Prime]
    (a : ZMod q) (hs : List ℕ) (x : ℕ) :
    denominator q a hs x ≠ 0 ↔
      ∀ v ∈ poleOffsets hs, a + ((x + v : ℕ) : ZMod q) ≠ 0 := by
  rw [denominator_eq_poleOffsets_prod]
  rw [ne_eq, List.prod_eq_zero_iff]
  constructor
  · intro h v hv hvzero
    apply h
    exact List.mem_map.mpr ⟨v, hv, hvzero⟩
  · intro h hzero
    obtain ⟨v, hv, hvzero⟩ := List.mem_map.mp hzero
    exact h v hv hvzero

end InverseRational

end Erdos387
