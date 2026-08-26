/-
Copyright 2026 The Lean-Proofs Authors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    http://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/
import ErdosProblems.Erdos76.PentagonTwoBlob

/-!
# The finite colour-pattern core of the pentagon extension argument

Section 7 of Gruslys--Letzter repeatedly uses the same elementary fact about
the five edges from a new vertex to one transversal of a pentagon blow-up.
This module isolates that `2^5`-pattern calculation.  The declarations below
do not enumerate graphs or use a published certificate: they are the direct
Boolean versions of Observation 7.9 and Proposition 7.10.
-/

namespace Erdos76

/-- Whether the template edge between two pentagon labels is red. -/
def pentagonTemplateRed (i j : Fin 5) : Bool :=
  decide ((SimpleGraph.cycleGraph 5).Adj i j)

/-- For a Boolean pattern of red neighbours of the new vertex, labels `i,j`
form a monochromatic triangle through the new vertex. -/
def pentagonMonoPair (r : Fin 5 → Bool) (i j : Fin 5) : Bool :=
  (r i && r j && pentagonTemplateRed i j) ||
    (!r i && !r j && !pentagonTemplateRed i j)

/-- The two bad configurations from Section 7: three red neighbours in
positions `i,i+2,i+3`, or three blue neighbours in positions `i,i+1,i+2`.
Arithmetic in `Fin 5` is cyclic. -/
def pentagonBadPattern (r : Fin 5 → Bool) : Bool :=
  ([0, 1, 2, 3, 4] : List (Fin 5)).any fun i ↦
    (r i && r (i + 2) && r (i + 3)) ||
      (!r i && !r (i + 1) && !r (i + 2))

/-- A new vertex and every transversal of the five blobs span a
monochromatic triangle through the new vertex (Observation 7.9, first
part). -/
theorem pentagon_exists_mono_pair :
    ∀ r : Fin 5 → Bool, ∃ i j : Fin 5,
      i ≠ j ∧ pentagonMonoPair r i j = true := by
  decide

/-- A bad configuration yields two such triangles whose two old-vertex
pairs are vertex-disjoint (Observation 7.9, second part).  Since both
triangles contain the new vertex, this is precisely the condition ensuring
that their three-edge sets are disjoint. -/
theorem pentagon_bad_exists_two_disjoint_mono_pairs :
    ∀ r : Fin 5 → Bool, pentagonBadPattern r = true →
      ∃ i j k l : Fin 5,
        i ≠ j ∧ k ≠ l ∧ i ≠ k ∧ i ≠ l ∧ j ≠ k ∧ j ≠ l ∧
          pentagonMonoPair r i j = true ∧
          pentagonMonoPair r k l = true := by
  decide

/-- In the absence of a bad configuration, the five colours are consistent
with adjoining the new vertex to one blob.  The colour at the chosen blob
itself is intentionally unrestricted, just as edges internal to a blob are
unrestricted in `IsPentagonBlowup` (Proposition 7.10's finite core). -/
theorem pentagon_no_bad_extends_one_blob :
    ∀ r : Fin 5 → Bool, pentagonBadPattern r = false →
      ∃ s : Fin 5, ∀ j : Fin 5, j ≠ s →
        r j = pentagonTemplateRed s j := by
  decide

/-- Rigidity under replacing one coordinate of a transversal.  If two
bad-free patterns agree away from `j`, and the first pattern extends blob
`s ≠ j`, then the replacement coordinate is forced to have the same
template colour.  This is the finite core that makes the extension label
independent of the chosen transversal. -/
theorem pentagon_no_bad_stable_replacement :
    ∀ r r' : Fin 5 → Bool, ∀ j s : Fin 5,
      pentagonBadPattern r = false →
      pentagonBadPattern r' = false →
      (∀ q : Fin 5, q ≠ j → r' q = r q) →
      (∀ q : Fin 5, q ≠ s → r q = pentagonTemplateRed s q) →
      j ≠ s → r' j = pentagonTemplateRed s j := by
  decide

end Erdos76
