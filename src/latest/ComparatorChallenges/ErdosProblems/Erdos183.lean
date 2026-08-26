/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/- Released under the Apache 2.0 license. This file has been modified. -/

import Mathlib

open Filter

namespace Erdos183

def TriangleFree {n k : ℕ}
    (C : SimpleGraph.TopEdgeLabeling (Fin n) (Fin k)) : Prop :=
  ∀ colour : Fin k, (C.labelGraph colour).CliqueFree 3

def ForcesMonochromaticTriangle (n k : ℕ) : Prop :=
  ∀ C : SimpleGraph.TopEdgeLabeling (Fin n) (Fin k), ¬ TriangleFree C

noncomputable def triangleRamseyNumber (k : ℕ) : ℕ :=
  sInf {n : ℕ | ForcesMonochromaticTriangle n k}

theorem erdos_183 :
    Filter.Tendsto
      (fun k : ℕ =>
        (triangleRamseyNumber k : ℝ) ^ ((1 : ℝ) / (k : ℝ)))
      atTop atTop := by
  sorry

end Erdos183
