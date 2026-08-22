/- leanprover/lean4:v4.33.0 mathlib v4.33.0 -/
import ErdosProblems.Erdos1165.AsymmetricCompatibleFullProfileRows
import ErdosProblems.Erdos1165.AsymmetricCompatibleRadialCompletionFamily

/-!
# Full-profile rows over genuine coarse completion atoms

The retained atom in this adapter is an arbitrary measurable coarse
completion event.  A second complementary-skeleton factor starts from that
event: its complement weight is proved equal to the mass of the coarse atom,
and only its bridge coordinates carry the fine right-hand signature.  Thus
the usual stopped-word product law gives the exact conditional tail mass,
without identifying the coarse completion with a synthetic cylinder.

The fine row is scanner-restricted.  Its product is bounded by the
unrestricted row, and the existing full-profile radial certificate supplies
the uniform tail bound.
-/

open MeasureTheory Set
open scoped BigOperators ENNReal

namespace Erdos1165.AsymmetricFullProfileNestedCompletionRows

open AppendixFirstMoment AppendixPair AppendixPairCrossingTail
open AppendixPairMoment AsymmetricActualFarPairData
open AsymmetricCompatibleRadialCompletionFamily
open AsymmetricSplitLevelSplice MarkedBridgeFactorization
open ProfileListExponent ProfileWeightUpper Proposition13Scales

noncomputable section

/-- Source-facing nested rows.  `retained_weight` is the genuine renewal
completion factorization: it compares the outer weight of the *deeper*
factor with the mass of the already-completed coarse atom.  It says nothing
about a stopped cylinder representing that coarse atom. -/
structure FullProfileNestedCompletionRows
    {delta : ℝ} {n : ℕ} {x y : Point}
    (successful retained gammaX : Set StepPath)
    (certificate : ProfileRadialTailCertificate delta n x y) : Type 2 where
  RetainedCode : Type
  retainedCode_countable : Countable RetainedCode
  coordinateCount : RetainedCode → ℕ
  Complement : RetainedCode → Type
  complement_countable : ∀ r, Countable (Complement r)
  Bridge : (r : RetainedCode) → Fin (coordinateCount r) → Type
  bridge_countable : ∀ r j, Countable (Bridge r j)
  atom : (r : RetainedCode) → ComplementarySkeletonAtom
    (coordinateCount r) (Complement r) (Bridge r)
  admissible : (r : RetainedCode) → (j : Fin (coordinateCount r)) →
    Bridge r j → Prop
  retainedAtom : RetainedCode → Set StepPath
  successful_subset : successful ⊆ ⋃ r,
    (restrictBridges (atom r) (admissible r)).event
  retained_eq : retained = ⋃ r, retainedAtom r
  retained_measurable : ∀ r, MeasurableSet (retainedAtom r)
  retained_pairwise : Pairwise fun r s ↦
    Disjoint (retainedAtom r) (retainedAtom s)
  retained_subset : retained ⊆ gammaX
  retained_weight : ∀ r,
    (atom r).weight = fairSteps (retainedAtom r)
  profile : RetainedCode → Profile (scaleIndex delta n)
  profile_mem : ∀ r,
    profile r ∈ constrainedProfiles (scaleIndex delta n) profileUpperDelta
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

attribute [instance]
  FullProfileNestedCompletionRows.retainedCode_countable
attribute [instance]
  FullProfileNestedCompletionRows.complement_countable
attribute [instance]
  FullProfileNestedCompletionRows.bridge_countable

/-- The deeper restricted bridge product is a certified radial-tail row. -/
theorem FullProfileNestedCompletionRows.restricted_row_le
    {delta : ℝ} {n : ℕ} {x y : Point}
    {successful retained gammaX : Set StepPath}
    {certificate : ProfileRadialTailCertificate delta n x y}
    (rows : FullProfileNestedCompletionRows
      successful retained gammaX certificate) (r : rows.RetainedCode) :
    ∏ j, (restrictBridges (rows.atom r) (rows.admissible r)).kernel j ≤
      ENNReal.ofReal certificate.radialTail := by
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

/-- Package genuine coarse completion atoms and their deeper fine rows as
the completion family consumed by the sound far-pair constructor. -/
def FullProfileNestedCompletionRows.toCompatibleRadialCompletionFamily
    {delta : ℝ} {n : ℕ} {x y : Point}
    {successful retained gammaX : Set StepPath}
    {certificate : ProfileRadialTailCertificate delta n x y}
    (rows : FullProfileNestedCompletionRows
      successful retained gammaX certificate) :
    CompatibleRadialCompletionFamily successful retained gammaX
      certificate.radialTail where
  RetainedCode := rows.RetainedCode
  retainedCode_countable := rows.retainedCode_countable
  TailCode := fun _ ↦ Unit
  tailCode_countable := fun _ ↦ inferInstance
  retainedAtom := rows.retainedAtom
  tailAtom := fun r _ ↦
    (restrictBridges (rows.atom r) (rows.admissible r)).event
  tailWeight := fun r _ ↦
    ∏ j, (restrictBridges (rows.atom r) (rows.admissible r)).kernel j
  successful_subset := by
    intro omega homega
    obtain ⟨r, hr⟩ := Set.mem_iUnion.mp (rows.successful_subset homega)
    exact Set.mem_iUnion.mpr ⟨r,
      Set.mem_iUnion.mpr ⟨Unit.unit, hr⟩⟩
  retained_eq := rows.retained_eq
  retained_measurable := rows.retained_measurable
  retained_pairwise := rows.retained_pairwise
  tail_mass := by
    intro r u
    rw [fairSteps_restrictBridges, rows.retained_weight]
    exact mul_comm _ _
  row_le := by
    intro r
    simpa using rows.restricted_row_le r
  retained_subset := rows.retained_subset

end

end Erdos1165.AsymmetricFullProfileNestedCompletionRows
