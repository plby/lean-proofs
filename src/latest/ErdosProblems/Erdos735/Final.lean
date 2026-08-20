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

import ErdosProblems.Erdos735.Primal
import ErdosProblems.Erdos735.ReducedCoreStage4
import ErdosProblems.Erdos735.ConcreteProjectiveLeviPathExtraction
import ErdosProblems.Erdos735.ConcreteStage4BeltCoverage

/-!
# Final assembly for Erdős Problem 735

This module connects the concrete occupied-line-belt theorem to the
projective Levi path extraction, the Stage-4 discharging contradiction,
and finally the primal classification reduction.
-/

open Classical
noncomputable section

namespace Erdos735

/-- Every reduced magic red--blue core is the failed-Fano configuration. -/
theorem isFailedFano_of_reducedMagic
    {P : Finset Point} {w : Point → ℝ} {c : ℝ}
    (hAcard : 3 ≤ (ordinaryPoints P).card)
    (hB : (nonordinaryPoints P).Nonempty)
    (hred : IsReducedMagic P w c) :
    IsFailedFano P := by
  let S := ReducedCore.setup hAcard hB hred
  apply S.isFailedFano_of_projectiveLeviPathExtraction
  intro hnot
  letI := S.lineNonempty
  exact ConcreteProjectiveLeviPathExtraction.projectiveLeviPathExtraction_of_occupied
    S.hred S.ha S.hb S.hd S.hncol S.hAcard hnot
    (ConcreteStage4BeltCoverage.occupiedStarts_eq_univ
      S.hred S.ha S.hb S.hd S.hncol S.hAcard hnot)

/-- Erdős Problem 735.  A finite planar point set has positive weights
with one common sum on every spanned line exactly in the four classified
cases: collinear, general position, a near-pencil, or failed Fano. -/
theorem erdos_735 (P : Finset Point) :
    IsMagic P ↔
      IsCollinearConfig P ∨ InGeneralPosition P ∨
        IsNearPencil P ∨ IsFailedFano P := by
  constructor
  · exact classified_of_magic_of_reduced_core_all
      (fun hAcard hB hred ↦
        isFailedFano_of_reducedMagic hAcard hB hred)
  · exact isMagic_of_classified_all

end Erdos735

