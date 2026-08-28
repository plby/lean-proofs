import Wikipedia.HopfProblem.SpecialPeriodsTrianglePresentation
import Wikipedia.HopfProblem.SpecialPeriodsTriangleRegularCentralizers

/-!
# Centralizers of the triangle generators

The centralizer of each distinguished generator in the actual free product
`TriangleGroup` is exactly the cyclic factor containing that generator. We
describe it by bounded natural powers, including the identity power.
-/

namespace Wikipedia.HopfProblem.SpecialPeriods

private theorem cyclic_eq_bounded_generator_pow {n : ℕ} [NeZero n]
    (a : Multiplicative (ZMod n)) :
    ∃ k : ℕ, k < n ∧ a = Multiplicative.ofAdd (1 : ZMod n) ^ k := by
  refine ⟨a.toAdd.val, ZMod.val_lt _, ?_⟩
  change a.toAdd = a.toAdd.val • (1 : ZMod n)
  simp only [nsmul_eq_mul, mul_one, ZMod.natCast_zmod_val]

/-- An element commuting with the order-three generator belongs to its
cyclic factor, with a representative exponent less than three. -/
theorem triangleGenerator₁_commute_eq_pow (g : TriangleGroup)
    (h : Commute triangleGenerator₁ g) :
    ∃ n : ℕ, n < 3 ∧ g = triangleGenerator₁ ^ n := by
  obtain ⟨a, ha⟩ := CoprodTorsion.coprod_commute_inl
    (Multiplicative.ofAdd (1 : ZMod 3)) (by decide) g h
  obtain ⟨n, hn, rfl⟩ := cyclic_eq_bounded_generator_pow a
  exact ⟨n, hn, by simpa only [map_pow, triangleGenerator₁] using ha⟩

/-- An element commuting with the order-four generator belongs to its
cyclic factor, with a representative exponent less than four. -/
theorem triangleGenerator₂_commute_eq_pow (g : TriangleGroup)
    (h : Commute triangleGenerator₂ g) :
    ∃ n : ℕ, n < 4 ∧ g = triangleGenerator₂ ^ n := by
  obtain ⟨a, ha⟩ := CoprodTorsion.coprod_commute_inr
    (Multiplicative.ofAdd (1 : ZMod 4)) (by decide) g h
  obtain ⟨n, hn, rfl⟩ := cyclic_eq_bounded_generator_pow a
  exact ⟨n, hn, by simpa only [map_pow, triangleGenerator₂] using ha⟩

/-- The centralizer of the first triangle generator is exactly its three
bounded powers. -/
theorem triangleGenerator₁_commute_iff (g : TriangleGroup) :
    Commute triangleGenerator₁ g ↔ ∃ n : ℕ, n < 3 ∧ g = triangleGenerator₁ ^ n := by
  constructor
  · exact triangleGenerator₁_commute_eq_pow g
  · rintro ⟨n, _, rfl⟩
    exact Commute.self_pow _ _

/-- The centralizer of the second triangle generator is exactly its four
bounded powers. -/
theorem triangleGenerator₂_commute_iff (g : TriangleGroup) :
    Commute triangleGenerator₂ g ↔ ∃ n : ℕ, n < 4 ∧ g = triangleGenerator₂ ^ n := by
  constructor
  · exact triangleGenerator₂_commute_eq_pow g
  · rintro ⟨n, _, rfl⟩
    exact Commute.self_pow _ _

end Wikipedia.HopfProblem.SpecialPeriods
