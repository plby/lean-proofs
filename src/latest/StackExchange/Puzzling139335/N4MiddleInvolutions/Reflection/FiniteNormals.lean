import Mathlib.Analysis.Complex.Circle
import Mathlib.Data.Finset.Card

/-!
# At most three normals invariant under rotation and reflection

A finite set of complex numbers, of cardinality at most three, that is closed
under conjugation and multiplication by a nonidentity scalar either contains
a real number or consists entirely of purely imaginary numbers.

The argument uses only finite cardinality and complex algebra.  No restriction
on the norms of the members is needed.
-/

namespace Puzzling139335.N4MiddleInvolutions.Reflection

open ComplexConjugate

/-- Without a real member, conjugation closure and a bound of three members
force every member to belong to the same conjugate pair. -/
theorem eq_or_eq_conj_of_card_le_three (s : Finset ℂ)
    (hcard : s.card ≤ 3)
    (hconj : ∀ w ∈ s, conj w ∈ s)
    (him : ∀ w ∈ s, w.im ≠ 0)
    {z w : ℂ} (hz : z ∈ s) (hw : w ∈ s) :
    w = z ∨ w = conj z := by
  classical
  by_contra h
  have hwz : w ≠ z := fun he => h (Or.inl he)
  have hwcz : w ≠ conj z := fun he => h (Or.inr he)
  have hzc : z ≠ conj z := fun he =>
    him z hz (Complex.conj_eq_iff_im.mp he.symm)
  have hwc : w ≠ conj w := fun he =>
    him w hw (Complex.conj_eq_iff_im.mp he.symm)
  have hcwz : conj w ≠ z := by
    intro he
    apply hwcz
    simpa using congrArg conj he
  have hcwcz : conj w ≠ conj z := by
    intro he
    apply hwz
    simpa using congrArg conj he
  have hfour : ({z, conj z, w, conj w} : Finset ℂ).card = 4 :=
    Finset.card_eq_four.mpr
      ⟨z, conj z, w, conj w, hzc, hwz.symm, hcwz.symm,
        hwcz.symm, hcwcz.symm, hwc, rfl⟩
  have hsub : ({z, conj z, w, conj w} : Finset ℂ) ⊆ s := by
    intro v hv
    simp only [Finset.mem_insert, Finset.mem_singleton] at hv
    rcases hv with rfl | rfl | rfl | rfl
    · exact hz
    · exact hconj z hz
    · exact hw
    · exact hconj w hw
  have hfourle := Finset.card_le_card hsub
  rw [hfour] at hfourle
  exact (by decide : ¬ (4 : ℕ) ≤ 3) (hfourle.trans hcard)

/-- A nonidentity scalar and conjugation cannot preserve at most three
complex numbers containing a member with nonzero real part unless the set
also contains a real number. -/
theorem re_eq_zero_or_exists_im_eq_zero_of_mul (s : Finset ℂ)
    (hcard : s.card ≤ 3) (a : ℂ) (ha : a ≠ 1)
    (hmul : ∀ w ∈ s, a * w ∈ s)
    (hconj : ∀ w ∈ s, conj w ∈ s)
    {z : ℂ} (hz : z ∈ s) :
    z.re = 0 ∨ ∃ w ∈ s, w.im = 0 := by
  classical
  by_cases hreal : ∃ w ∈ s, w.im = 0
  · exact Or.inr hreal
  left
  have him : ∀ w ∈ s, w.im ≠ 0 := fun w hw he => hreal ⟨w, hw, he⟩
  have hne : ∀ w ∈ s, a * w ≠ w := by
    intro w hw he
    have hw0 : w ≠ 0 := by
      intro he0
      exact him w hw (by simp [he0])
    exact ha ((mul_eq_right₀ hw0).mp he)
  have hpair : ∀ w ∈ s, w = z ∨ w = conj z :=
    fun w hw => eq_or_eq_conj_of_card_le_three s hcard hconj him hz hw
  have hcz : conj z ∈ s := hconj z hz
  have haz : a * z = conj z := (hpair _ (hmul z hz)).resolve_left (hne z hz)
  have hacz : a * conj z = z := (hpair _ (hmul _ hcz)).resolve_right (hne _ hcz)
  have hadd : a * (z + conj z) = z + conj z := by
    rw [mul_add, haz, hacz, add_comm]
  have hsum : z + conj z = 0 := by
    by_contra hn
    exact ha ((mul_eq_right₀ hn).mp hadd)
  apply add_self_eq_zero.mp
  simpa using congrArg Complex.re hsum

/-- Unit-circle version of the finite rotation-and-reflection argument.
The members of `s` need not themselves have unit norm. -/
theorem re_eq_zero_or_exists_im_eq_zero (s : Finset ℂ)
    (hcard : s.card ≤ 3) (a : Circle) (ha : a ≠ 1)
    (hrot : ∀ w ∈ s, (a : ℂ) * w ∈ s)
    (hconj : ∀ w ∈ s, conj w ∈ s)
    {z : ℂ} (hz : z ∈ s) :
    z.re = 0 ∨ ∃ w ∈ s, w.im = 0 :=
  re_eq_zero_or_exists_im_eq_zero_of_mul s hcard (a : ℂ)
    (fun he => ha (Circle.coe_eq_one.mp he)) hrot hconj hz

end Puzzling139335.N4MiddleInvolutions.Reflection
