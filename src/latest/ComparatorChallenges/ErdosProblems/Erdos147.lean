import Mathlib

open Filter
open Asymptotics
open scoped SimpleGraph Topology

noncomputable section

attribute [local instance] Classical.propDecidable

namespace Erdos147

noncomputable def polynomialGrowth (a : ℝ) (n : ℕ) : ℝ :=
  (n : ℝ) ^ a

end Erdos147

namespace Erdos147

noncomputable def extremalGrowth {W : Type*} (H : SimpleGraph W) (n : ℕ) : ℝ :=
  SimpleGraph.extremalNumber n H

end Erdos147

namespace Erdos147

def HasConjecturedLowerBound {W : Type*} (H : SimpleGraph W) (r : ℕ) : Prop :=
  ∃ ε : ℝ, 0 < ε ∧
    (polynomialGrowth (2 - 1 / ((r : ℝ) - 1) + ε)) =O[atTop] extremalGrowth H

end Erdos147

namespace Erdos147

def ErdosSimonovitsConjecture : Prop :=
  ∀ (W : Type) [Fintype W] [Nonempty W]
    (H : SimpleGraph W) [DecidableRel H.Adj] (r : ℕ),
      H.IsBipartite → H.minDegree = r → HasConjecturedLowerBound H r

end Erdos147

namespace Erdos147

theorem not_erdosSimonovitsConjecture : ¬ErdosSimonovitsConjecture := by
  sorry

end Erdos147

end
