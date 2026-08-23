/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import Mathlib

open Filter Metric
open scoped BigOperators EuclideanGeometry RealInnerProductSpace
open Finset

noncomputable section


namespace Erdos754

open scoped Classical in
abbrev E4 := EuclideanSpace ℝ (Fin 4)

end Erdos754

namespace Erdos754

open scoped Classical in
def IsFavorite {W : Type*} (p : W → E4) (c : W → ℝ) (x y : W) : Prop :=
  x ≠ y ∧ dist (p x) (p y) = c x

end Erdos754

namespace Erdos754

open scoped Classical in
noncomputable def favoriteDegree (P : Finset E4) (c : P → ℝ) (x : P) : ℕ :=
  open scoped Classical in
  (Finset.univ.filter fun y : P => IsFavorite (fun z : P => (z : E4)) c x y).card

end Erdos754

namespace Erdos754

open scoped Classical in
def Attainable (n k : ℕ) : Prop :=
  ∃ P : Finset E4, P.card = n ∧
    ∃ c : P → ℝ, (∀ x, 0 < c x) ∧ ∀ x, k ≤ favoriteDegree P c x

end Erdos754

namespace Erdos754

open scoped Classical in
noncomputable def f (n : ℕ) : ℕ :=
  if n = 0 then 0 else sSup {k : ℕ | Attainable n k}

end Erdos754

namespace Erdos754

open scoped Classical in
theorem erdos_754 : ∃ C : ℝ, ∀ n : ℕ, (f n : ℝ) ≤ (n : ℝ) / 2 + C := by
  sorry

end Erdos754

end
