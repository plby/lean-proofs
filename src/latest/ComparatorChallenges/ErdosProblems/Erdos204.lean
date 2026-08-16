import Mathlib

namespace Erdos204

set_option linter.style.setOption false
set_option linter.style.longLine false
set_option linter.flexible false
set_option linter.unusedVariables false

open scoped Real
open scoped Nat

attribute [local instance] Classical.propDecidable

noncomputable section

structure Congruence where
  a : ℤ
  d : ℕ
  d_pos : 0 < d
def Congruence.overlaps (c1 c2 : Congruence) : Prop :=
  ∃ x : ℤ, x ≡ c1.a [ZMOD c1.d] ∧ x ≡ c2.a [ZMOD c2.d]
def IsCD (S : Finset Congruence) : Prop :=
  ∀ c1 ∈ S, ∀ c2 ∈ S, c1 ≠ c2 → c1.overlaps c2 → c1.d.Coprime c2.d
def IsCovering (S : Finset Congruence) : Prop :=
  ∀ x : ℤ, ∃ c ∈ S, x ≡ c.a [ZMOD c.d]
instance : DecidableEq Congruence := fun c1 c2 =>
  match c1, c2 with
  | ⟨a1, d1, _⟩, ⟨a2, d2, _⟩ =>
    if h : a1 = a2 ∧ d1 = d2 then
      isTrue (by cases c1; cases c2; simp_all)
    else
      isFalse (by intro h_eq; cases c1; cases c2; simp_all)
def congruences (n : ℕ) (a : ℕ → ℤ) : Finset Congruence :=
  let divs := (Nat.divisors n).filter (fun d => 1 < d)
  let divs_list := divs.toList
  let cong_list := divs_list.attach.map (fun ⟨d, hd⟩ =>
    { a := a d,
      d := d,
      d_pos := by
        have : d ∈ divs := Finset.mem_toList.mp hd
        rw [Finset.mem_filter] at this
        exact lt_trans Nat.zero_lt_one this.2
    })
  cong_list.toFinset
def IsCDCovering (n : ℕ) : Prop :=
  ∃ a : ℕ → ℤ, IsCD (congruences n a) ∧ IsCovering (congruences n a)
end

end Erdos204

attribute [local instance] Classical.propDecidable

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Pointwise

namespace Erdos204

theorem T1 : ¬ ∃ n, IsCDCovering n := by
  sorry


theorem erdos_204 : ¬ ∃ (n : ℕ) (a : ℕ → ℤ),
    let D := {d : ℕ | d ∣ n ∧ d > 1}
    (∀ x : ℤ, ∃ d ∈ D, x ≡ a d [ZMOD d]) ∧
    (∀ d ∈ D, ∀ d' ∈ D, d ≠ d' → (∃ x : ℤ, x ≡ a d [ZMOD d] → x ≡ a d' [ZMOD d']) →
      Nat.gcd d d' = 1) := by
  sorry

end Erdos204
