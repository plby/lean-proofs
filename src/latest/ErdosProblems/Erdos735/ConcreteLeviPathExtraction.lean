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

import ErdosProblems.Erdos735.Stage4ContinuationExtraction
import ErdosProblems.Erdos735.ConcretePolarRecognition
import ErdosProblems.Erdos735.ConcretePolarABKPRData
import ErdosProblems.Erdos735.ConcreteOppositeLineCoherence
import ErdosProblems.Erdos735.ConcreteStage4FlankComplete

/-!
# Concrete specialization of the corrected Levi-path extraction

This is the assembly-facing specialization for the literal polar
cellulation.  Its `resolve` premise is deliberately stated as the exact
remaining local theorem: for the canonical Hall-deficient path, either the
three-edge recognition gives failed Fano or the two continuation triangles
on the common opposite line satisfy the exhaustive Levi certificate.
-/

open Classical
noncomputable section

namespace Erdos735.ConcreteLeviPathExtraction

open ProjectiveArrangement ProjectiveBoundaryExtraction SignVector
open SignVectorArrangement

abbrev Point := ProjectiveArrangement.Point

variable {P : Finset Point} {w : Point → ℝ} {c : ℝ}
variable (hred : IsReducedMagic P w c)
variable {a b d : Point}
variable (ha : a ∈ nonordinaryPoints P) (hb : b ∈ nonordinaryPoints P)
variable (hd : d ∈ nonordinaryPoints P)
variable (hncol : ¬ ProjectiveDuality.Collinear3 a b d)
variable [Nonempty (ProjectiveBoundaryExtraction.Line (nonordinaryPoints P))]

private abbrev B := nonordinaryPoints P
private abbrev C := ConcretePolarCellulation.blueCellulation
  (B (P := P)) ha hb hd hncol
private abbrev D := ConcretePolarABKPRData.concreteData hred ha hb hd hncol
private abbrev X := ConcretePolarCellulation.boundaryExtraction
  (B (P := P)) ha hb hd hncol

variable (L : (D hred ha hb hd hncol).FlankSystem
  (ProjectiveBoundaryExtraction.Line (B (P := P))))

/-- Concrete failed-Fano-or-Levi-extraction dichotomy after the local
opposite-edge and continuation analysis has been supplied. -/
theorem isFailedFano_or_leviPathExtraction
    (hedge : L.edgeLine = strictEdgeOwner)
    (resolve : ∀ hHall : ¬ L.toHelpingGraph.NoEvilEvilPath,
      IsFailedFano P ∨ Nonempty
        (ABKPR.Data.DeficientPathContinuation L hHall)) :
    IsFailedFano P ∨ Nonempty
      (ABKPR.Data.LeviPathExtraction (B := X ha hb hd hncol) L) := by
  have hedge' : L.edgeLine = ConcretePolarFlankBounds.edgeLine := by
    calc
      L.edgeLine = strictEdgeOwner := hedge
      _ = ConcretePolarFlankBounds.edgeLine := by funext e; rfl
  let K := ConcreteOppositeLineCoherence.oppositeLineCoherence
    hred ha hb hd hncol L hedge'
  exact ABKPR.Data.exceptional_or_leviPathExtraction L K hedge resolve

/-- Non-failed-Fano form consumed by the reduced-core proof. -/
theorem concreteLeviPathExtraction_of_not_failedFano
    (hnotFF : ¬ IsFailedFano P)
    (hedge : L.edgeLine = strictEdgeOwner)
    (resolve : ∀ hHall : ¬ L.toHelpingGraph.NoEvilEvilPath,
      IsFailedFano P ∨ Nonempty
        (ABKPR.Data.DeficientPathContinuation L hHall)) :
    Nonempty (ABKPR.Data.LeviPathExtraction
      (B := X ha hb hd hncol) L) := by
  have hedge' : L.edgeLine = ConcretePolarFlankBounds.edgeLine := by
    calc
      L.edgeLine = strictEdgeOwner := hedge
      _ = ConcretePolarFlankBounds.edgeLine := by funext e; rfl
  let K := ConcreteOppositeLineCoherence.oppositeLineCoherence
    hred ha hb hd hncol L hedge'
  exact ABKPR.Data.leviPathExtraction_of_not_exceptional
    L K hedge resolve hnotFF

/-- Assembly form for the canonical complete geometric flank system.  The
only remaining input is the continuation/exhaustion theorem for a deficient
component; opposite-line coherence and owner correctness are now derived. -/
theorem canonicalLeviPathExtraction_of_not_failedFano
    (hAcard : 3 ≤ (ordinaryPoints P).card)
    (hnotFF : ¬ IsFailedFano P)
    (resolve :
      let L₀ := ConcreteStage4FlankComplete.flankSystem
        hred ha hb hd hncol hAcard hnotFF
      ∀ hHall : ¬ L₀.toHelpingGraph.NoEvilEvilPath,
        IsFailedFano P ∨ Nonempty
          (ABKPR.Data.DeficientPathContinuation L₀ hHall)) :
    let L₀ := ConcreteStage4FlankComplete.flankSystem
      hred ha hb hd hncol hAcard hnotFF
    Nonempty (ABKPR.Data.LeviPathExtraction
      (B := X ha hb hd hncol) L₀) := by
  let L₀ := ConcreteStage4FlankComplete.flankSystem
    hred ha hb hd hncol hAcard hnotFF
  have hedge : L₀.edgeLine = strictEdgeOwner := by
    calc
      L₀.edgeLine = ConcretePolarFlankBounds.edgeLine := rfl
      _ = strictEdgeOwner := by funext e; rfl
  exact concreteLeviPathExtraction_of_not_failedFano
    hred ha hb hd hncol L₀ hnotFF hedge resolve

end Erdos735.ConcreteLeviPathExtraction
