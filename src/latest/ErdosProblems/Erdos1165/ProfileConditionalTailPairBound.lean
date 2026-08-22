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

import ErdosProblems.Erdos1165.ProfileConditionalTailUpper
import ErdosProblems.Erdos1165.AppendixPairReferenceMass

/-!
# A fixed-prefix continuation bound in pair-correlation form

The exact profile disintegration gives a particularly useful one-sided
statement.  If one admissible prefix atom has mass at least `prefixLower`,
then the full constrained profile mass dominates `prefixLower` times the
continuation mass in that atom.  Dividing by the positive prefix lower bound
produces precisely the reference-tail shape used in HLOZ (A.16)--(A.17).

The final adapter deliberately assumes only that the literal stopped
reference event is contained in (or otherwise bounded by) that exact
continuation.  It does not assume the desired quotient estimate itself.
-/

open MeasureTheory
open scoped ENNReal

namespace Erdos1165.ProfileConditionalTailPairBound

open AppendixFirstMoment AppendixPairMoment AppendixPairReferenceMass
open MarkedTerminalDisintegration ProfileConditionalTailUpper Proposition13Scales

noncomputable section

/-- One exact constrained prefix term is bounded by the full constrained
profile mass. -/
theorem profileWeight_mul_constrainedProfileTailWeight_le
    {n start : ℕ} (hstart : 2 ≤ start) (hstartn : start ≤ n)
    {pref : Profile start} {delta : ℝ}
    (hpref : pref ∈ constrainedProfiles start delta) :
    profileWeight pref *
        constrainedProfileTailWeight n start hstart hstartn pref delta ≤
      constrainedProfileWeight n delta := by
  rw [constrainedProfileWeight_eq_sum_prefix_mul_tail hstart hstartn delta]
  exact Finset.single_le_sum
    (fun q _ ↦ mul_nonneg (profileWeight_nonneg q)
      (constrainedProfileTailWeight_nonneg n start hstart hstartn q delta))
    hpref

/-- Dividing the preceding exact-prefix inequality by any positive lower
bound for that prefix gives the conditional continuation estimate. -/
theorem constrainedProfileTailWeight_le_div_of_prefixLower
    {n start : ℕ} (hstart : 2 ≤ start) (hstartn : start ≤ n)
    {pref : Profile start} {delta prefixLower : ℝ}
    (hpref : pref ∈ constrainedProfiles start delta)
    (hlower0 : 0 < prefixLower)
    (hlower : prefixLower ≤ profileWeight pref) :
    constrainedProfileTailWeight n start hstart hstartn pref delta ≤
      constrainedProfileWeight n delta / prefixLower := by
  have htail0 := constrainedProfileTailWeight_nonneg
    n start hstart hstartn pref delta
  have hmul : prefixLower *
        constrainedProfileTailWeight n start hstart hstartn pref delta ≤
      constrainedProfileWeight n delta :=
    (mul_le_mul_of_nonneg_right hlower htail0).trans
      (profileWeight_mul_constrainedProfileTailWeight_le
        hstart hstartn hpref)
  exact (le_div_iff₀ hlower0).2 (by simpa [mul_comm] using hmul)

/-- Specialization to the explicit denominator used by the far-pair
certificate.  The remaining prefix premise is a literal lower bound for the
particular retained profile atom, rather than an aggregate independence
statement. -/
theorem constrainedProfileTailWeight_le_pairPrefixQuotient
    {n start : ℕ} (hstart : 2 ≤ start) (hstartn : start ≤ n)
    {pref : Profile start}
    (hpref : pref ∈ constrainedProfiles start chosenProfileDelta)
    (hprefLower : prefixProfileLower start ≤ profileWeight pref) :
    constrainedProfileTailWeight n start hstart hstartn pref
        chosenProfileDelta ≤
      constrainedProfileWeight n chosenProfileDelta /
        prefixProfileLower start := by
  exact constrainedProfileTailWeight_le_div_of_prefixLower
    hstart hstartn hpref (prefixProfileLower_pos start) hprefLower

/-- Walk-facing reference-tail adapter.  Once the literal reference event
has been bounded by one exact continuation fibre, the source-aligned
`pointUpper / prefixProfileLower` field follows. -/
theorem referenceEventMass_le_pairPrefixQuotient
    {m n start : ℕ}
    (referenceMass : Fin m → ℕ → ℝ≥0∞)
    (visitEvent : Set (Fin m → ℕ))
    (hstart : 2 ≤ start) (hstartn : start ≤ n)
    {pref : Profile start}
    (hpref : pref ∈ constrainedProfiles start chosenProfileDelta)
    (hprefLower : prefixProfileLower start ≤ profileWeight pref)
    (href : (referenceEventMass referenceMass visitEvent).toReal ≤
      constrainedProfileTailWeight n start hstart hstartn pref
        chosenProfileDelta) :
    (referenceEventMass referenceMass visitEvent).toReal ≤
      constrainedProfileWeight n chosenProfileDelta /
        prefixProfileLower start := by
  exact href.trans (constrainedProfileTailWeight_le_pairPrefixQuotient
    hstart hstartn hpref hprefLower)

end

end Erdos1165.ProfileConditionalTailPairBound
