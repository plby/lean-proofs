import Mathlib

open Filter

noncomputable section


namespace Erdos121

open scoped Classical in
structure FiniteWeight (Ω : Type*) where
  support : Finset Ω
  weight : Ω → ℝ
  weight_nonneg : ∀ ω ∈ support, 0 ≤ weight ω

end Erdos121

namespace Erdos121.FiniteWeight

open scoped Classical in
noncomputable def prod {Ξ : Type*} (W : FiniteWeight Ω) (V : FiniteWeight Ξ) :
    FiniteWeight (Ω × Ξ) := by
  classical
  exact
    { support := W.support ×ˢ V.support
      weight := fun p => W.weight p.1 * V.weight p.2
      weight_nonneg := by
        intro p hp
        have hp' := Finset.mem_product.mp hp
        exact mul_nonneg (W.weight_nonneg p.1 hp'.1) (V.weight_nonneg p.2 hp'.2) }

end Erdos121.FiniteWeight

namespace Erdos121

open scoped Classical in
def HasSquareProduct (S : Finset ℕ) : Prop :=
  IsSquare (S.prod id)

end Erdos121

namespace Erdos121

open scoped Classical in
def IsAdmissible (k N : ℕ) (A : Finset ℕ) : Prop :=
  A ⊆ Finset.Icc 1 N ∧
    ∀ S : Finset ℕ, S ⊆ A → S.card = k → ¬ HasSquareProduct S

end Erdos121

namespace Erdos121

open scoped Classical in
def Attainable (k N m : ℕ) : Prop :=
  ∃ A : Finset ℕ, IsAdmissible k N A ∧ A.card = m

end Erdos121

namespace Erdos121

open scoped Classical in
noncomputable def extremalSize (k N : ℕ) : ℕ := by
  classical
  exact Nat.findGreatest (Attainable k N) N

end Erdos121

namespace Erdos121

open scoped Classical in
theorem erdos_121 :
    ∀ k : ℕ, 4 ≤ k → ∃ c : ℝ, 0 < c ∧ ∀ᶠ N : ℕ in atTop,
      (extremalSize k N : ℝ) ≤ (1 - c) * N := by
  sorry

end Erdos121

end
