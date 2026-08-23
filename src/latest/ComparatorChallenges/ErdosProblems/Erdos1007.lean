/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import Mathlib

namespace Erdos1007

set_option linter.style.setOption false
set_option linter.style.longLine false
set_option linter.flexible false


open SimpleGraph

open scoped Classical in
def IsUnitDistanceEmbedding {V : Type*} (G : SimpleGraph V) (d : ℕ) (f : V → EuclideanSpace ℝ (Fin d)) : Prop :=
  Function.Injective f ∧ ∀ {u v}, G.Adj u v → dist (f u) (f v) = 1
open scoped Classical in
def HasUnitDistanceEmbedding {V : Type*} (G : SimpleGraph V) (d : ℕ) : Prop :=
  ∃ f : V → EuclideanSpace ℝ (Fin d), IsUnitDistanceEmbedding G d f
open scoped Classical in
noncomputable def GraphDimension {V : Type*} (G : SimpleGraph V) : ℕ :=
  sInf { d | HasUnitDistanceEmbedding G d }
end Erdos1007



open SimpleGraph

namespace Erdos1007

open scoped Classical in
theorem erdos_1007 : IsLeast {n : ℕ | ∃ (V : Type) (_ : Fintype V) (_ : DecidableEq V) (G : SimpleGraph V), GraphDimension G = 4 ∧ G.edgeFinset.card = n} 9 := by
  sorry

end Erdos1007
