/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Copyright 2026 The Formal Conjectures Authors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/

import ErdosProblems.Erdos735.ConcreteStage3ObstructionRecognition
import ErdosProblems.Erdos735.ReducedCore

/-!
# Stage-3 obstruction recognition for a selected reduced-core setup

This module is deliberately separated from the concrete recognizer so that
the latter remains independent of the higher-level `ReducedCore.Setup`
packaging.
-/

open Classical
noncomputable section

namespace Erdos735.ReducedCore.Setup

open ProjectiveArrangement

variable {P : Finset ProjectiveArrangement.Point}
variable {w : ProjectiveArrangement.Point → ℝ} {c : ℝ}

/-- Every concrete Stage-3 local obstruction carried by a reduced-core
setup is the failed-Fano exception. -/
theorem isFailedFano_of_stage3LocalObstruction
    (S : ReducedCore.Setup P w c)
    (hobs : S.D.Stage3LocalObstruction) : IsFailedFano P := by
  let _ := S.lineNonempty
  exact
    ConcreteStage3ObstructionRecognition.isFailedFano_of_stage3LocalObstruction
      S.hred S.ha S.hb S.hd S.hncol S.hAcard hobs

/-- Away from failed Fano, the complete reduced Stage-3 geometry is
constructible with no additional local assumptions. -/
theorem reducedStage3Geometry_of_not_isFailedFano
    (S : ReducedCore.Setup P w c) (hnot : ¬ IsFailedFano P) :
    Nonempty S.D.ReducedStage3Geometry := by
  rcases S.stage3Dichotomy with hobs | hgeometry
  · exact (hnot (S.isFailedFano_of_stage3LocalObstruction hobs)).elim
  · exact hgeometry

/-- The assumption-free Stage-3 disjunction for the selected concrete
reduced-core setup. -/
theorem failedFano_or_reducedStage3Geometry
    (S : ReducedCore.Setup P w c) :
    IsFailedFano P ∨ Nonempty S.D.ReducedStage3Geometry := by
  by_cases h : IsFailedFano P
  · exact Or.inl h
  · exact Or.inr (S.reducedStage3Geometry_of_not_isFailedFano h)

end Erdos735.ReducedCore.Setup
