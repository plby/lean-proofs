/- leanprover/lean4:v4.33.0 mathlib v4.33.0 -/
/-
Copyright 2026 The Formal Conjectures Authors.

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

import ErdosProblems.Erdos1165.AsymmetricCompatibleRadialFamily

/-!
# Full-profile construction of scanner-compatible asymmetric rows

The split-level insertion restricts the erased `y` return words to those
which have the source scanner transition.  This restriction is never
estimated directly.  Instead its row product is bounded coordinatewise by
the unrestricted renewal row.  The latter is compared with the transition
product of the actual complete constrained profile carried by the retained
code.  The fixed-prefix A.11 certificate then performs the only profile
mixture used in the argument.

Thus the exported `CompatibleRadialFamily` has no scalar radial-tail
comparison as input.  Its quantitative input is the source-facing
unrestricted-row estimate for one actual full profile.
-/

open MeasureTheory Set
open scoped BigOperators ENNReal

namespace Erdos1165.AsymmetricCompatibleFullProfileRows

open AppendixFirstMoment AppendixPair AppendixPairCrossingTail AppendixPairMoment
open AsymmetricActualFarPairData
open AsymmetricCompatibleRadialFamily AsymmetricSplitLevelSplice
open MarkedBridgeFactorization ProfileListExponent ProfileWeightUpper
open Proposition13Scales

noncomputable section

/-- Literal retained rows before imposing scanner compatibility.  The
`unrestricted_row` field is the A.6 renewal estimate for the actual full
profile encoded by `r`; it is not an event-probability or final pair
comparison premise. -/
structure FullProfileCompatibleRows
    {delta : ℝ} {n : ℕ} {x y : Point}
    (successful retained : Set StepPath)
    (certificate : ProfileRadialTailCertificate delta n x y) : Type 2 where
  RetainedCode : Type
  retainedCode_countable : Countable RetainedCode
  coordinateCount : RetainedCode → ℕ
  Bridge : (r : RetainedCode) → Fin (coordinateCount r) → Type
  bridge_countable : ∀ r j, Countable (Bridge r j)
  atom : (r : RetainedCode) → ComplementarySkeletonAtom
    (coordinateCount r) Unit (Bridge r)
  admissible : (r : RetainedCode) → (j : Fin (coordinateCount r)) →
    Bridge r j → Prop
  profile : RetainedCode → Profile (scaleIndex delta n)
  profile_mem : ∀ r,
    profile r ∈ constrainedProfiles (scaleIndex delta n) profileUpperDelta
  successful_subset : successful ⊆ ⋃ r,
    (restrictBridges (atom r) (admissible r)).event
  retained_eq : retained = ⋃ r,
    stoppedWordCylinder ((atom r).complementWord Unit.unit)
  retained_prefixFree : PrefixFree fun r ↦
    (atom r).complementWord Unit.unit
  unrestricted_ne_top : ∀ r, (∏ j, (atom r).kernel j) ≠ ∞
  unrestricted_row : ∀ r,
    (∏ j, (atom r).kernel j).toReal ≤ certificate.coefficient *
      transitionSegmentProduct
        (pairPrefixScale (scaleIndex delta n)
          (separationLevel (scaleIndex delta n) x y))
        (scaleIndex delta n -
          pairPrefixScale (scaleIndex delta n)
            (separationLevel (scaleIndex delta n) x y))
        (profileAtScale (profile r))

attribute [instance] FullProfileCompatibleRows.retainedCode_countable
attribute [instance] FullProfileCompatibleRows.bridge_countable

/-- Scanner restriction of a literal full-profile row is automatically a
`CompatibleRadialFamily` with the certified uniform A.11 radial tail. -/
def FullProfileCompatibleRows.toCompatibleRadialFamily
    {delta : ℝ} {n : ℕ} {x y : Point}
    {successful retained : Set StepPath}
    {certificate : ProfileRadialTailCertificate delta n x y}
    (rows : FullProfileCompatibleRows successful retained certificate) :
    CompatibleRadialFamily successful retained certificate.radialTail where
  RetainedCode := rows.RetainedCode
  retainedCode_countable := rows.retainedCode_countable
  coordinateCount := rows.coordinateCount
  Bridge := rows.Bridge
  bridge_countable := rows.bridge_countable
  atom := rows.atom
  admissible := rows.admissible
  successful_subset := rows.successful_subset
  retained_eq := rows.retained_eq
  retained_prefixFree := rows.retained_prefixFree
  row_le := by
    intro r
    let restricted := ∏ j,
      (restrictBridges (rows.atom r) (rows.admissible r)).kernel j
    let unrestricted := ∏ j, (rows.atom r).kernel j
    have hle : restricted ≤ unrestricted := by
      exact compatibleFixedComplementWeight_le
        (rows.atom r) (rows.admissible r)
    have hrestricted : restricted ≠ ∞ := by
      exact ne_top_of_le_ne_top (rows.unrestricted_ne_top r) hle
    have hreal : restricted.toReal ≤ unrestricted.toReal :=
      ENNReal.toReal_mono (rows.unrestricted_ne_top r) hle
    exact certificate.ennreal_le_of_fullProfileRow
      (rows.profile r) (rows.profile_mem r) hrestricted
      (hreal.trans (rows.unrestricted_row r))

end

end Erdos1165.AsymmetricCompatibleFullProfileRows
