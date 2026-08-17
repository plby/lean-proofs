import Mathlib

open Filter Metric
open scoped BigOperators EuclideanGeometry RealInnerProductSpace
open Finset

noncomputable section

attribute [local instance] Classical.propDecidable

namespace Erdos754

abbrev E4 := EuclideanSpace ℝ (Fin 4)

end Erdos754

namespace Erdos754

def IsFavorite {W : Type*} (p : W → E4) (c : W → ℝ) (x y : W) : Prop :=
  x ≠ y ∧ dist (p x) (p y) = c x

end Erdos754

namespace Erdos754

noncomputable def favoriteDegree (P : Finset E4) (c : P → ℝ) (x : P) : ℕ :=
  open scoped Classical in
  (Finset.univ.filter fun y : P => IsFavorite (fun z : P => (z : E4)) c x y).card

end Erdos754

namespace Erdos754

def Attainable (n k : ℕ) : Prop :=
  ∃ P : Finset E4, P.card = n ∧
    ∃ c : P → ℝ, (∀ x, 0 < c x) ∧ ∀ x, k ≤ favoriteDegree P c x

end Erdos754

namespace Erdos754

noncomputable def f (n : ℕ) : ℕ :=
  if n = 0 then 0 else sSup {k : ℕ | Attainable n k}

end Erdos754

namespace Erdos754

theorem erdos_754 : ∃ C : ℝ, ∀ n : ℕ, (f n : ℝ) ≤ (n : ℝ) / 2 + C := by
  sorry

end Erdos754

end
