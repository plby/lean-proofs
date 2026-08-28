import Mathlib.Data.Sign.Basic
import Mathlib.Data.Finset.Card

/-!
# The finite signed count under actual pair deletion

Deleting two opposite unit signs preserves the integer sum and reduces the
cardinality by two. Once no opposite pair remains, the number of points is
the absolute value of the signed sum. These algebraic facts will be applied
to the actual finite Morse intersection sets and their constructed moves.
-/

open scoped BigOperators

namespace Wikipedia.SmoothSixDPoincare.FiniteSignedCancellation

variable {X : Type*}

theorem opposite_signs_distinct {a b : SignType} (h : a * b = -1) : a ≠ b := by
  cases a <;> cases b <;> simp_all

theorem cast_add_eq_zero_of_opposite {a b : SignType} (h : a * b = -1) :
    (a : ℤ) + (b : ℤ) = 0 := by
  cases a <;> cases b <;> simp_all

/-- Opposite pair deletion preserves the entire integer-weighted count. -/
theorem sum_sdiff_pair [DecidableEq X] (s : Finset X) (σ : X → SignType) {x y : X}
    (hx : x ∈ s) (hy : y ∈ s) (hxy : σ x * σ y = -1) :
    ∑ z ∈ s \ {x, y}, (σ z : ℤ) = ∑ z ∈ s, (σ z : ℤ) := by
  classical
  have hne : x ≠ y := fun h => opposite_signs_distinct hxy (congrArg σ h)
  have hsub : ({x, y} : Finset X) ⊆ s := by
    intro z hz
    rcases Finset.mem_insert.mp hz with rfl | hz
    · exact hx
    · exact Finset.mem_singleton.mp hz ▸ hy
  have hsum : ∑ z ∈ ({x, y} : Finset X), (σ z : ℤ) = 0 := by
    rw [Finset.sum_pair hne]
    exact cast_add_eq_zero_of_opposite hxy
  have h := Finset.sum_sdiff (f := fun z => (σ z : ℤ)) hsub
  simpa only [hsum, add_zero] using h

/-- The signs may be represented by a new function if they agree at all surviving points. -/
theorem sum_sdiff_pair_of_eq [DecidableEq X] (s : Finset X) (σ τ : X → SignType) {x y : X}
    (hx : x ∈ s) (hy : y ∈ s) (hxy : σ x * σ y = -1)
    (heq : ∀ z ∈ s \ {x, y}, τ z = σ z) :
    ∑ z ∈ s \ {x, y}, (τ z : ℤ) = ∑ z ∈ s, (σ z : ℤ) := by
  calc
    _ = ∑ z ∈ s \ {x, y}, (σ z : ℤ) :=
      Finset.sum_congr rfl (fun z hz => congrArg (fun a : SignType => (a : ℤ)) (heq z hz))
    _ = _ := sum_sdiff_pair s σ hx hy hxy

/-- Exactly two distinct points disappear in an opposite-sign deletion. -/
theorem card_sdiff_pair_add_two [DecidableEq X] (s : Finset X) (σ : X → SignType) {x y : X}
    (hx : x ∈ s) (hy : y ∈ s) (hxy : σ x * σ y = -1) :
    (s \ {x, y}).card + 2 = s.card := by
  classical
  have hne : x ≠ y := fun h => opposite_signs_distinct hxy (congrArg σ h)
  have hsub : ({x, y} : Finset X) ⊆ s := by
    intro z hz
    rcases Finset.mem_insert.mp hz with rfl | hz
    · exact hx
    · exact Finset.mem_singleton.mp hz ▸ hy
  simpa only [Finset.card_pair hne] using Finset.card_sdiff_add_card_eq_card hsub

/-- With only unit signs, absence of opposite pairs leaves exactly the absolute signed count. -/
theorem card_eq_natAbs_sum_of_no_opposite (s : Finset X) (σ : X → SignType)
    (hunit : ∀ x ∈ s, σ x = 1 ∨ σ x = -1)
    (hno : ∀ x ∈ s, ∀ y ∈ s, σ x * σ y ≠ -1) :
    s.card = (∑ x ∈ s, (σ x : ℤ)).natAbs := by
  classical
  rcases s.eq_empty_or_nonempty with rfl | ⟨x, hx⟩
  · simp
  have heq (y : X) (hy : y ∈ s) : σ y = σ x := by
    rcases hunit x hx with hxp | hxn <;> rcases hunit y hy with hyp | hyn
    · exact hyp.trans hxp.symm
    · exact (hno x hx y hy (by rw [hxp, hyn]; simp)).elim
    · exact (hno x hx y hy (by rw [hxn, hyp]; simp)).elim
    · exact hyn.trans hxn.symm
  have hsum : (∑ y ∈ s, (σ y : ℤ)) = ∑ _ ∈ s, (σ x : ℤ) := by
    apply Finset.sum_congr rfl
    intro y hy
    rw [heq y hy]
  rw [hsum]
  rcases hunit x hx with hp | hn
  · simp [hp]
  · simp [hn]

end Wikipedia.SmoothSixDPoincare.FiniteSignedCancellation
