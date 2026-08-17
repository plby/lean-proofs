module

public import ErdosProblems.Erdos179.AddCombi.Mathlib.Algebra.Notation.Indicator
public import Mathlib.Algebra.Star.Pi

open scoped ComplexConjugate Indicator

public section

namespace Set
variable {α R : Type*} [CommSemiring R] [StarRing R]

@[simp] lemma conj_indicator_one_apply (s : Set α) (a : α) : conj (𝟭_[s, R] a) = 𝟭_[s] a := by
  classical simp [indicator_apply]

@[simp] lemma conj_indicator_one (s : Set α) : conj 𝟭_[s, R] = 𝟭_[s] := by ext; simp

end Set
