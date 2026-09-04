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

import ErdosProblems.Erdos735.ConcreteStage3SetupRecognition
import ErdosProblems.Erdos735.ConcreteStage4FlankComplete
import ErdosProblems.Erdos735.Discharging4ConcreteLevi

/-!
# Reduced-core Stage-4 assembly

This module joins the assumption-free Stage-3 recognition, the concrete
flank graph, the projectively correct six-face Levi theorem, and an explicit
projective continuation extraction.  It leaves only construction of that
last extraction to the literal line-belt modules.
-/

open Classical
noncomputable section

namespace Erdos735.ReducedCore.Setup

open ProjectiveArrangement ProjectiveBoundaryExtraction
open SignVectorArrangement

abbrev Point := ProjectiveArrangement.Point

variable {P : Finset Point} {w : Point → ℝ} {c : ℝ}

/-- Availability of the canonical projective continuation for a selected
reduced-core setup.  The setup itself supplies the nonempty blue-line index
type needed by the concrete polar construction. -/
def CanonicalProjectivePathAvailable (S : ReducedCore.Setup P w c) : Prop :=
  letI := S.lineNonempty
  ∀ hnot : ¬ IsFailedFano P,
    let L := ConcreteStage4FlankComplete.flankSystem
      S.hred S.ha S.hb S.hd S.hncol S.hAcard hnot
    Nonempty (ABKPR.Data.ProjectiveLeviPathExtraction
      (B := ConcretePolarCellulation.boundaryExtraction
        (nonordinaryPoints P) S.ha S.hb S.hd S.hncol) L)

/-- Once the concrete projective continuation is available for every
non-failed-Fano setup, the Stage-4 charge contradiction forces failed Fano.
All incidence, packing, graph-degree, and Levi inputs are supplied by the
checked reduced-core setup. -/
theorem isFailedFano_of_projectiveLeviPathExtraction
    (S : ReducedCore.Setup P w c)
    (hpath : CanonicalProjectivePathAvailable S) :
    IsFailedFano P := by
  by_contra hnot
  let := S.lineNonempty
  let L := ConcreteStage4FlankComplete.flankSystem
    S.hred S.ha S.hb S.hd S.hncol S.hAcard hnot
  obtain ⟨G⟩ := S.reducedStage3Geometry_of_not_isFailedFano hnot
  obtain ⟨X⟩ := hpath hnot
  exact X.contradiction G S.endpointRestriction S.leviProperty

/-- Reduced-core interface in the exact form consumed by the primal
classification reduction. -/
theorem isFailedFano_of_reducedMagic_of_projectivePath
    (hAcard : 3 ≤ (ordinaryPoints P).card)
    (hB : (nonordinaryPoints P).Nonempty)
    (hred : IsReducedMagic P w c)
    (hpath : CanonicalProjectivePathAvailable
      (ReducedCore.setup hAcard hB hred)) :
    IsFailedFano P :=
  (ReducedCore.setup hAcard hB hred).isFailedFano_of_projectiveLeviPathExtraction
    hpath

end Erdos735.ReducedCore.Setup
