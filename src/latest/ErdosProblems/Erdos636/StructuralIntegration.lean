/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
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

import ErdosProblems.Erdos636.AsymptoticThresholds
import ErdosProblems.Erdos636.CandidateThresholds
import ErdosProblems.Erdos636.SlicePersistence
import ErdosProblems.Erdos636.StructuralEndpoint
import ErdosProblems.Erdos636.StructuralRandom

/-!
# Finite integration of the structural first exposure

This file contains the exact adapters between the random first-exposure
output and the deterministic structural endpoint.  The persistence tests
are only the polynomial family of pairs of sets of size at most `K`.
-/

open Classical SimpleGraph

namespace Erdos636.StructuralIntegration

universe u

noncomputable section

variable {V : Type u} [Fintype V] [DecidableEq V]

/-! ## Fixed constants -/

/-- The support-density parameter used in the structural random slice. -/
def fixedStructuralTheta (eps : ℝ) : ℝ :=
  eps ^ structuralUniformity * (eps / 2)

/-- The fixed point-mass coefficient in the graph-slice collision estimate. -/
def fixedStructuralCollisionConstant (cR eps : ℝ) : ℝ :=
  AntiConcentration.variancePointMassConstant
    (AsymptoticThresholds.structuralDensity cR)
    (eps * fixedStructuralTheta eps) 1

/-- A collision-edge coefficient leaving a strict unit of slack. -/
def fixedStructuralEdgeCoefficient (cR eps : ℝ) : ℝ :=
  2 * fixedStructuralCollisionConstant cR eps + 1

/-- The degree-pruning coefficient, chosen after the edge coefficient. -/
def fixedStructuralDegreeCoefficient (cR eps : ℝ) : ℝ :=
  64 * fixedStructuralEdgeCoefficient cR eps / cR

/-- The degree-gap density, chosen last so the middle sorting block remains. -/
def fixedStructuralGapDensity (cR eps : ℝ) : ℝ :=
  cR / (64 * fixedStructuralDegreeCoefficient cR eps)

/-- All sign and compatibility facts for the sequential fixed-constant
choice used below. -/
lemma fixedStructural_constants
    {cR eps : ℝ} (hcR : 0 < cR) (heps : 0 < eps) :
    let theta := fixedStructuralTheta eps
    let A := fixedStructuralCollisionConstant cR eps
    let QE := fixedStructuralEdgeCoefficient cR eps
    let QD := fixedStructuralDegreeCoefficient cR eps
    let cGap := fixedStructuralGapDensity cR eps
    0 < theta ∧ 0 < A ∧ 0 < QE ∧ 2 * A < QE ∧
      0 < QD ∧ 32 * QE ≤ cR * QD ∧ 0 < cGap ∧
      4 * QD * cGap < cR / 8 := by
  dsimp only [fixedStructuralTheta, fixedStructuralCollisionConstant,
    fixedStructuralEdgeCoefficient, fixedStructuralDegreeCoefficient,
    fixedStructuralGapDensity]
  let theta : ℝ := eps ^ structuralUniformity * (eps / 2)
  let A : ℝ := AntiConcentration.variancePointMassConstant
    (AsymptoticThresholds.structuralDensity cR) (eps * theta) 1
  let QE : ℝ := 2 * A + 1
  let QD : ℝ := 64 * QE / cR
  change 0 < theta ∧ 0 < A ∧ 0 < QE ∧ 2 * A < QE ∧
    0 < QD ∧ 32 * QE ≤ cR * QD ∧
    0 < cR / (64 * QD) ∧ 4 * QD * (cR / (64 * QD)) < cR / 8
  have htheta : 0 < theta := by
    dsimp only [theta]
    positivity
  have hcS : 0 < AsymptoticThresholds.structuralDensity cR := by
    simp only [AsymptoticThresholds.structuralDensity]
    positivity
  have hA : 0 < A := by
    dsimp only [A]
    exact AntiConcentration.variancePointMassConstant_pos hcS
      (mul_pos heps htheta) (by omega)
  have hQE : 0 < QE := by dsimp only [QE]; positivity
  have hQD : 0 < QD := by dsimp only [QD]; positivity
  refine ⟨htheta, hA, hQE, by linarith, hQD, ?_, by positivity, ?_⟩
  · have heq : cR * QD = 64 * QE := by
      dsimp only [QD]
      field_simp [hcR.ne']
    rw [heq]
    nlinarith
  · have heq : 4 * QD * (cR / (64 * QD)) = cR / 16 := by
      field_simp [hQD.ne']
      ring
    rw [heq]
    linarith

/-- The fixed first-exposure lower-tail is dominated by the common
exponential budget used for all structural persistence estimates. -/
lemma fixedStructural_firstExposure_exp_le
    {cS theta : ℝ} {n ell : ℕ}
    (hcS : 0 < cS) (htheta : 0 < theta) (hn : 0 < n)
    (hellPos : 0 < ell)
    (hellUpper : (ell : ℝ) ≤ 2 * cS * n) :
    Real.exp (-(cS * theta * n) ^ 2 / (8 * (2 * ell : ℕ))) ≤
      Real.exp (-(theta ^ 2 / 512) * ell) := by
  have hell0 : (0 : ℝ) ≤ ell := by positivity
  have hupper0 : (0 : ℝ) ≤ 2 * cS * n := by positivity
  have hfactor : 0 ≤
      (2 * cS * n - ell) * (2 * cS * n + ell) :=
    mul_nonneg (sub_nonneg.mpr hellUpper) (add_nonneg hupper0 hell0)
  have hellSq : (ell : ℝ) ^ 2 ≤ (2 * cS * n) ^ 2 := by
    nlinarith
  have hscaled := mul_le_mul_of_nonneg_left hellSq (sq_nonneg theta)
  apply Real.exp_le_exp.mpr
  have htarget : (theta ^ 2 / 512) * ell ≤
      (cS * theta * n) ^ 2 / (8 * (2 * ell : ℕ)) := by
    rw [le_div_iff₀ (show (0 : ℝ) < 8 * (2 * ell : ℕ) by positivity)]
    push_cast
    nlinarith
  calc
    -(cS * theta * (n : ℝ)) ^ 2 / (8 * (2 * ell : ℕ)) =
        -((cS * theta * (n : ℝ)) ^ 2 / (8 * (2 * ell : ℕ))) := by ring
    _ ≤ -((theta ^ 2 / 512) * ell) := neg_le_neg htarget
    _ = -(theta ^ 2 / 512) * ell := by ring

/-- The random-half lower-tail is dominated by the same common exponential
budget. -/
lemma fixedStructural_halfExposure_exp_le
    {cS theta : ℝ} {n ell : ℕ}
    (hcS : 0 < cS) (htheta : 0 < theta) (hn : 0 < n)
    (hellPos : 0 < ell)
    (hellUpper : (ell : ℝ) ≤ 2 * cS * n) :
    Real.exp (-((cS * theta * n / 4) ^ 2 / (8 * ell))) ≤
      Real.exp (-(theta ^ 2 / 512) * ell) := by
  have hell0 : (0 : ℝ) ≤ ell := by positivity
  have hupper0 : (0 : ℝ) ≤ 2 * cS * n := by positivity
  have hfactor : 0 ≤
      (2 * cS * n - ell) * (2 * cS * n + ell) :=
    mul_nonneg (sub_nonneg.mpr hellUpper) (add_nonneg hupper0 hell0)
  have hellSq : (ell : ℝ) ^ 2 ≤ (2 * cS * n) ^ 2 := by
    nlinarith
  have hscaled := mul_le_mul_of_nonneg_left hellSq (sq_nonneg theta)
  apply Real.exp_le_exp.mpr
  have htarget : (theta ^ 2 / 512) * ell ≤
      (cS * theta * n / 4) ^ 2 / (8 * ell) := by
    rw [le_div_iff₀ (show (0 : ℝ) < 8 * ell by positivity)]
    push_cast
    nlinarith
  calc
    -((cS * theta * (n : ℝ) / 4) ^ 2 / (8 * ell)) ≤
        -((theta ^ 2 / 512) * ell) := neg_le_neg htarget
    _ = -(theta ^ 2 / 512) * ell := by ring

/-- Failure of one bounded support-persistence test in a fixed reservoir. -/
def supportPersistenceFailure (G : SimpleGraph V) (U0 : Finset V)
    (localThreshold : ℝ) (p : Finset V × Finset V) : Prop :=
  incidenceDiffMass G U0 p.1 p.2 < localThreshold

/-- The ambient incidence-support, viewed as a finset of a prescribed
vertex reservoir. -/
def supportWithin (G : SimpleGraph V) (U : Finset V)
    (p : Finset V × Finset V) : Finset U :=
  Finset.univ.filter fun u ↦
    (u : V) ∈ supportDiff G Finset.univ p.1 p.2

/-- Counting support through the subtype of `U` is the same as restricting
the ambient support to `U`. -/
lemma card_supportWithin (G : SimpleGraph V) (U : Finset V)
    (p : Finset V × Finset V) :
    (supportWithin G U p).card = supportDiffCard G U p.1 p.2 := by
  have hlift :
      liftInducedFinset (supportWithin G U p) =
        U ∩ supportDiff G Finset.univ p.1 p.2 := by
    ext v
    simp [supportWithin, liftInducedFinset, and_comm]
  calc
    (supportWithin G U p).card =
        (liftInducedFinset (supportWithin G U p)).card :=
      (card_liftInducedFinset _).symm
    _ = (U ∩ supportDiff G Finset.univ p.1 p.2).card :=
      congrArg Finset.card hlift
    _ = supportDiffCard G U p.1 p.2 :=
      (supportDiffCard_eq_card_inter_univ G U p.1 p.2).symm

/-- Intersecting a Boolean half-slice with the subtype support becomes the
ambient support cardinality after lifting the sampled subtype finset. -/
lemma intersectionCount_supportWithin_eq
    (G : SimpleGraph V) (U : Finset V)
    (p : Finset V × Finset V) (ell : ℕ)
    (omega : Erdos88.Fourier.BoolSlice U ell) :
    SlicePersistence.intersectionCount (supportWithin G U p) ell omega =
      (supportDiffCard G
        (liftInducedFinset (SlicePersistence.sampleFinset ell omega))
        p.1 p.2 : ℝ) := by
  let S := SlicePersistence.sampleFinset ell omega ∩ supportWithin G U p
  have hlift :
      liftInducedFinset S =
        liftInducedFinset (SlicePersistence.sampleFinset ell omega) ∩
          supportDiff G Finset.univ p.1 p.2 := by
    ext v
    simp [S, supportWithin, liftInducedFinset]
  have hcard :
      S.card = supportDiffCard G
        (liftInducedFinset (SlicePersistence.sampleFinset ell omega))
        p.1 p.2 := by
    calc
      S.card = (liftInducedFinset S).card :=
        (card_liftInducedFinset _).symm
      _ = (liftInducedFinset
            (SlicePersistence.sampleFinset ell omega) ∩
          supportDiff G Finset.univ p.1 p.2).card :=
        congrArg Finset.card hlift
      _ = supportDiffCard G
          (liftInducedFinset (SlicePersistence.sampleFinset ell omega))
          p.1 p.2 :=
        (supportDiffCard_eq_card_inter_univ G _ p.1 p.2).symm
  change (S.card : ℝ) = _
  exact_mod_cast hcard

/-- Support-cardinality persistence is the paper-correct first-exposure
property.  It is stronger than the incidence-mass persistence eventually
consumed by the structural constructor. -/
def SupportCardPersists (G : SimpleGraph V) (U0 : Finset V) (K : ℕ)
    (globalThreshold localThreshold : ℝ) : Prop :=
  ∀ X Y : Finset V,
    X.card ≤ K → Y.card ≤ K →
      globalThreshold ≤ supportDiffCard G Finset.univ X Y →
      localThreshold ≤ supportDiffCard G U0 X Y

/-- The explicit no-lower-tail conclusion of the graph-slice selector is
the support-cardinality persistence property. -/
theorem supportCardPersists_of_no_intersectionFailure
    (G : SimpleGraph V) (s K : ℕ) (globalThreshold localThreshold : ℝ)
    (omega : Erdos88.Fourier.BoolSlice V s)
    (hnofail : ∀ p ∈ supportPersistenceTests G K globalThreshold,
      ¬ SlicePersistence.intersectionCount
        (supportDiff G Finset.univ p.1 p.2) s omega < localThreshold) :
    SupportCardPersists G (StructuralRandom.sliceFinset s omega) K
      globalThreshold localThreshold := by
  intro X Y hX hY hglobal
  have hp : (X, Y) ∈ supportPersistenceTests G K globalThreshold :=
    mem_supportPersistenceTests.mpr ⟨hX, hY, hglobal⟩
  have h := hnofail (X, Y) hp
  simp only [not_lt, SlicePersistence.intersectionCount] at h
  rw [supportDiffCard_eq_card_inter_univ]
  simpa only [StructuralRandom.sliceFinset, SlicePersistence.sampleFinset]
    using h

/-- Support-cardinality persistence implies incidence-mass persistence,
with any smaller local threshold. -/
theorem supportPersists_of_supportCardPersists
    (G : SimpleGraph V) (U0 : Finset V) (K : ℕ)
    (globalThreshold supportThreshold localThreshold : ℝ)
    (hcard : SupportCardPersists G U0 K
      globalThreshold supportThreshold)
    (hlocal : localThreshold ≤ supportThreshold) :
    StructuralEndpoint.SupportPersists G U0 K
      globalThreshold localThreshold := by
  intro X Y hX hY hglobal
  have hsupport := hcard X Y hX hY hglobal
  exact hlocal.trans (hsupport.trans (by
    exact_mod_cast supportDiffCard_le_incidenceDiffMass G U0 X Y))

/-- A finite family of support-cardinality lower tails on a random half of
`U1` gives exactly the strict failure estimate required by the deterministic
endpoint.  The density in `U1` is `theta / 2`: since `|U1| = 2*ell`, the
first-exposure lower bound `theta*ell` is precisely that density. -/
theorem halfSupportPersists_failure_probability_lt_half
    (G : SimpleGraph V) (U1 : Finset V) (ell K : ℕ)
    (hU1card : U1.card = 2 * ell) (hellPos : 0 < ell)
    (globalThreshold theta localThreshold : ℝ)
    (htheta : 0 ≤ theta)
    (hfull : SupportCardPersists G U1 K globalThreshold
      (theta * ell))
    (hlocal : localThreshold ≤ (theta / 2) * ell / 2)
    (hbudget :
      (supportPersistenceTests G K globalThreshold).card *
          (2 * Real.exp
            (-((theta / 2) * ell / 2) ^ 2 / (8 * ell))) <
        (1 : ℝ) / 2) :
    HalfSample.sliceProbability (by simpa using hU1card) (fun omega ↦
      ¬ StructuralEndpoint.SupportPersists G
        (StructuralEndpoint.halfSubset omega) K
        globalThreshold localThreshold) < (1 : ℝ) / 2 := by
  let hcard : Fintype.card U1 = 2 * ell := by
    simpa using hU1card
  let E : Erdos88.Fourier.BoolSlice U1 ell ≃
      HalfSample.Slice U1 ell :=
    Erdos88.Fourier.boolSliceEquivFinsetLen U1 ell
  letI : Nonempty (Erdos88.Fourier.BoolSlice U1 ell) :=
    ⟨E.symm (Classical.choice (HalfSample.sliceNonempty hcard))⟩
  letI : Nonempty (HalfSample.Slice U1 ell) :=
    HalfSample.sliceNonempty hcard
  have hell : ell ≤ Fintype.card U1 := by
    rw [hcard]
    omega
  have hfamily :=
    SlicePersistence.support_persistence_family_failure_probability_lt_half
      (supportPersistenceTests G K globalThreshold)
      (supportWithin G U1) ell hell hellPos (theta / 2)
      (by positivity) (by
        intro p hp
        rcases mem_supportPersistenceTests.mp hp with
          ⟨hX, hY, hglobal⟩
        rw [card_supportWithin, hcard]
        have hs := hfull p.1 p.2 hX hY hglobal
        convert hs using 1 <;> push_cast <;> ring) hbudget
  let Bad : HalfSample.Slice U1 ell → Prop := fun omega ↦
    ¬ StructuralEndpoint.SupportPersists G
      (StructuralEndpoint.halfSubset omega) K
      globalThreshold localThreshold
  have hpoint : ∀ beta : Erdos88.Fourier.BoolSlice U1 ell,
      Bad (E beta) →
        ∃ p ∈ supportPersistenceTests G K globalThreshold,
          SlicePersistence.intersectionCount (supportWithin G U1 p)
              ell beta <
            (theta / 2) * ell / 2 := by
    intro beta hbad
    by_contra hnone
    simp only [not_exists, not_and, not_lt] at hnone
    apply hbad
    intro X Y hX hY hglobal
    have hp : (X, Y) ∈ supportPersistenceTests G K globalThreshold :=
      mem_supportPersistenceTests.mpr ⟨hX, hY, hglobal⟩
    have hinter := hnone (X, Y) hp
    rw [intersectionCount_supportWithin_eq] at hinter
    have hE : StructuralEndpoint.halfSubset (E beta) =
        liftInducedFinset (SlicePersistence.sampleFinset ell beta) := by
      rfl
    rw [hE]
    exact hlocal.trans (hinter.trans (by
      exact_mod_cast supportDiffCard_le_incidenceDiffMass G
        (liftInducedFinset (SlicePersistence.sampleFinset ell beta)) X Y))
  have hmono := Erdos88.Concentration.uniformProbability_mono
    (fun beta hbad ↦ hpoint beta hbad)
  have hequiv := SlicePersistence.uniformProbability_equiv E Bad
  have hprobability :
      HalfSample.sliceProbability hcard Bad =
        Erdos88.Concentration.uniformProbability Bad := by
    rfl
  have hresult : HalfSample.sliceProbability hcard Bad < (1 : ℝ) / 2 := by
    rw [hprobability, ← hequiv]
    exact hmono.trans_lt hfamily
  simpa only [Bad] using hresult

/-- Avoiding all tests in `supportPersistenceTests` is exactly the
`K`-bounded persistence input consumed by `StructuralEndpoint`. -/
theorem supportPersists_of_noFailure
    (G : SimpleGraph V) (U0 : Finset V) (K : ℕ)
    (globalThreshold localThreshold : ℝ)
    (hnofail : ∀ p ∈ supportPersistenceTests G K globalThreshold,
      ¬ supportPersistenceFailure G U0 localThreshold p) :
    StructuralEndpoint.SupportPersists G U0 K
      globalThreshold localThreshold := by
  intro X Y hX hY hglobal
  have hp : (X, Y) ∈ supportPersistenceTests G K globalThreshold := by
    exact mem_supportPersistenceTests.mpr ⟨hX, hY, hglobal⟩
  have hnot := hnofail (X, Y) hp
  simpa only [supportPersistenceFailure, not_lt] using hnot

/-- Conversely, persistence rules out every member of the finite test
family.  This direction is useful when transferring events across the
Boolean-slice/finset-slice equivalence. -/
theorem noFailure_of_supportPersists
    (G : SimpleGraph V) (U0 : Finset V) (K : ℕ)
    (globalThreshold localThreshold : ℝ)
    (hpersists : StructuralEndpoint.SupportPersists G U0 K
      globalThreshold localThreshold) :
    ∀ p ∈ supportPersistenceTests G K globalThreshold,
      ¬ supportPersistenceFailure G U0 localThreshold p := by
  intro p hp
  rcases mem_supportPersistenceTests.mp hp with ⟨hX, hY, hglobal⟩
  exact not_lt_of_ge (hpersists p.1 p.2 hX hY hglobal)

/-- Failure of `SupportPersists` is contained in the union of its explicit
finite tests.  This implication is the direction needed for a union-bound
estimate on a second half exposure. -/
theorem not_supportPersists_imp_exists_failure
    (G : SimpleGraph V) (U0 : Finset V) (K : ℕ)
    (globalThreshold localThreshold : ℝ)
    (hbad : ¬ StructuralEndpoint.SupportPersists G U0 K
      globalThreshold localThreshold) :
    ∃ p ∈ supportPersistenceTests G K globalThreshold,
      supportPersistenceFailure G U0 localThreshold p := by
  by_contra hnone
  push Not at hnone
  exact hbad (supportPersists_of_noFailure G U0 K globalThreshold
    localThreshold hnone)

/-- An exact-size sorting reservoir can be carved out of the retained
vertices after removing the first-exposure slice. -/
theorem exists_subset_card_eq_disjoint
    (retained U1 : Finset V) (wSize : ℕ)
    (havailable : wSize ≤ (retained \ U1).card) :
    ∃ W : Finset V,
      W ⊆ retained \ U1 ∧ Disjoint W U1 ∧ W.card = wSize := by
  obtain ⟨W, hWsub, hWcard⟩ :=
    Finset.exists_subset_card_eq havailable
  refine ⟨W, hWsub, ?_, hWcard⟩
  exact Finset.disjoint_left.mpr fun _ hxW hxU ↦
    (Finset.mem_sdiff.mp (hWsub hxW)).2 hxU

/-- Restricting a natural-valued degree-fibre bound to a subset gives the
integer-valued fibre bound expected by degree sorting. -/
theorem intDegreeFiber_le_of_subset
    (G : SimpleGraph V) (U1 retained W : Finset V) (Q : ℕ)
    (hWsub : W ⊆ retained)
    (hfiber : ∀ z : ℕ,
      (retained.filter fun x ↦
        (Erdos88.neighborsIn G x U1).card = z).card ≤ Q) :
    ∀ z : ℤ,
      (W.filter fun x ↦
        ((Erdos88.neighborsIn G x U1).card : ℤ) = z).card ≤ Q := by
  intro z
  by_cases hz : 0 ≤ z
  · let q : ℕ := z.toNat
    have hq : (q : ℤ) = z := by
      exact Int.toNat_of_nonneg hz
    apply (Finset.card_le_card ?_).trans (hfiber q)
    intro x hx
    rw [Finset.mem_filter] at hx ⊢
    refine ⟨hWsub hx.1, ?_⟩
    rw [← hq] at hx
    exact_mod_cast hx.2
  · have hempty :
        W.filter (fun x ↦
          ((Erdos88.neighborsIn G x U1).card : ℤ) = z) = ∅ := by
      ext x
      rw [Finset.mem_filter]
      constructor
      · rintro ⟨_hxW, hx⟩
        have hnonneg :
            (0 : ℤ) ≤ ((Erdos88.neighborsIn G x U1).card : ℤ) := by
          exact Int.natCast_nonneg _
        have : False := by omega
        exact this.elim
      · intro hx
        simpa using hx
    rw [hempty]
    exact Nat.zero_le _

/-- Finite graph-facing assembly after the first slice has been selected.

The retained set may still meet `U1`; the theorem requires capacity only
in `retained \ U1` and selects exactly `wSize` vertices there.  The final
`candidateSize` vertices are then selected outside `W ∪ U1`, so the
capacity hypothesis accounts for all three reservoirs. -/
theorem structuralWitness_of_selectedSlice_and_candidateReservoir
    [Nonempty V] {G : SimpleGraph V}
    {ε aDisc aDiv b α : ℝ}
    {scale nW ell K r Q g wSize candidateSize : ℕ}
    (hε : 0 < ε) (hεone : ε ≤ 1)
    (hrich : KwanSudakovRich G (ε ^ K) ε)
    (U1 retained : Finset V)
    (hU1card : U1.card = 2 * ell)
    (hretained : wSize ≤ (retained \ U1).card)
    (hfiber : ∀ z : ℕ,
      ((retained \ U1).filter fun x ↦
        (Erdos88.neighborsIn G x U1).card = z).card ≤ Q)
    (hfit : wSize + 2 * ell + candidateSize ≤ Fintype.card V)
    (halpha : 0 ≤ α)
    (hnW : 0 < nW)
    (hWsize : 2 * nW ≤ wSize)
    (hmiddle : Q * (g + 1) < wSize - 2 * nW)
    (hscoreScale :
      4 * (aDisc * scale * Real.sqrt scale) ≤
        α * nW * (g + 1))
    (hfullPersist : StructuralEndpoint.SupportPersists G U1 K
      (ε ^ K * (ε / 2) * Fintype.card V) (aDiv * scale))
    (hhalfFail :
      HalfSample.sliceProbability (by simpa using hU1card) (fun omega ↦
        ¬ StructuralEndpoint.SupportPersists G
          (StructuralEndpoint.halfSubset omega) K
          (ε ^ K * (ε / 2) * Fintype.card V) (aDiv * scale)) <
        (1 : ℝ) / 2)
    (hK : 1 ≤ K)
    (hr : 2 ≤ r)
    (hnumerical :
      K * Fintype.card V ^ (K - 1) *
            ⌈(Fintype.card V : ℝ) ^ (1 / 5 : ℝ)⌉₊ +
          K.factorial * (r - 1) ^ K *
            (K * Fintype.card V + 1) ^ 3 <
        candidateSize.choose K)
    (hmatchingLarge :
      b * (scale : ℝ) ^ (3 / 4 : ℝ) *
          (⌈(Fintype.card V : ℝ) ^ (1 / 5 : ℝ)⌉₊ + 1) ≤ r) :
    Nonempty (StructuralWitness G scale nW ell K α aDisc aDiv b) := by
  obtain ⟨W, hWsub, hWU1, hWcard⟩ :=
    exists_subset_card_eq_disjoint retained U1 wSize hretained
  let target := K.factorial * (r - 1) ^ K *
    (K * Fintype.card V + 1) ^ 3
  have hbaseCard : (W ∪ U1).card = wSize + 2 * ell := by
    rw [Finset.card_union_of_disjoint hWU1, hWcard, hU1card]
  have hcapacity : candidateSize ≤ (Finset.univ \ (W ∪ U1)).card := by
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ _),
      Finset.card_univ, hbaseCard]
    omega
  have hnumerical' :
      K * Fintype.card V ^ (K - 1) *
            ⌈(Fintype.card V : ℝ) ^ (1 / 5 : ℝ)⌉₊ + target <
        candidateSize.choose K := by
    simpa only [target] using hnumerical
  obtain ⟨A, candidates, hAsub, _hAcard, _hcandidates,
      hcandidateSub, hcandidateUniform, hcandidateCommon, hlarge⟩ :=
    exists_goodCandidateReservoir_package (G := G) (epsilon := ε)
      (K := K) (s := candidateSize) (target := target) (W ∪ U1)
      hK hε hεone hrich hcapacity hnumerical'
  have hAaway : Disjoint A (W ∪ U1) := by
    rw [Finset.disjoint_left]
    intro x hxA hxbase
    exact (Finset.mem_sdiff.mp (hAsub hxA)).2 hxbase
  apply StructuralEndpoint.structuralWitness_of_sorted_twiceReservoir
    (G := G) (δ := ε ^ K) (ε := ε)
    (scale := scale) (nW := nW) (ell := ell) (K := K)
    (r := r) (Q := Q) (g := g)
    (aDisc := aDisc) (aDiv := aDiv) (b := b) (α := α)
    (candidates := candidates)
    (by positivity) hε hrich U1 W A
    (by simpa using hU1card) hWU1 hAaway halpha hnW
  · simpa only [hWcard] using hWsize
  · exact intDegreeFiber_le_of_subset G U1 (retained \ U1) W Q hWsub hfiber
  · simpa only [hWcard] using hmiddle
  · exact hscoreScale
  · exact hfullPersist
  · simpa only using hhalfFail
  · exact hcandidateSub
  · exact hcandidateUniform
  · exact hcandidateCommon
  · exact hr
  · simpa only [target] using hlarge
  · exact hmatchingLarge

/-! ## Unconditional eventual structural endpoint -/

/-- The finite collection of numerical estimates needed at one ambient size.
Keeping this package separate from the graph construction also keeps the
eventual-quantifier wrapper computationally small. -/
structure FixedStructuralNumericalData (cR eps : ℝ) (n m ell : ℕ) : Prop where
  fixed : AsymptoticThresholds.FixedAmbientBounds cR
    (fixedStructuralGapDensity cR eps) n m ell
  unionBudget :
    ((AsymptoticThresholds.structuralEdgeBudget
          (fixedStructuralEdgeCoefficient cR eps) n + 1 : ℕ) : ℝ) *
        AsymptoticThresholds.structuralTestCount m *
        (2 * Real.exp (-((fixedStructuralTheta eps) ^ 2 / 512) * ell)) < 1
  middleRoom :
    (AsymptoticThresholds.structuralDegreeBudget
          (fixedStructuralDegreeCoefficient cR eps) n + 1) *
        (AsymptoticThresholds.structuralGapSize
          (fixedStructuralGapDensity cR eps) n + 1) <
      AsymptoticThresholds.structuralSortingSize cR n -
        2 * AsymptoticThresholds.structuralSwitchingSize cR n
  pruningBudget :
    AsymptoticThresholds.structuralExceptionalSize m +
        (2 * AsymptoticThresholds.structuralEdgeBudget
          (fixedStructuralEdgeCoefficient cR eps) n) /
          (AsymptoticThresholds.structuralDegreeBudget
            (fixedStructuralDegreeCoefficient cR eps) n + 1) +
        2 * ell ≤ m / 2
  collisionBudget :
    (m : ℝ) * AsymptoticThresholds.structuralExceptionalSize m +
        m.choose 2 *
          (fixedStructuralCollisionConstant cR eps / Real.sqrt m) <
      AsymptoticThresholds.structuralEdgeBudget
        (fixedStructuralEdgeCoefficient cR eps) n
  sunflowerSize : 2 ≤ CandidateThresholds.sunflowerSize n
  candidateNumerical :
    64 * m ^ (64 - 1) * CandidateThresholds.exceptionalSize m +
        CandidateThresholds.candidateTarget n m <
      (CandidateThresholds.reservoirSize cR n).choose 64
  matchingLarge :
    (1 / 4 : ℝ) * (n : ℝ) ^ (3 / 4 : ℝ) *
        (CandidateThresholds.exceptionalSize m + 1) ≤
      CandidateThresholds.sunflowerSize n

/-- The second (random-half) persistence exposure, isolated from the
first-slice selection so that both finite arguments elaborate independently. -/
theorem fixedAmbient_halfSupport_failure_probability_lt_half
    {cR eps : ℝ} (hcR : 0 < cR) (heps : 0 < eps)
    {n ell : ℕ} {V : Type u} [Fintype V] [DecidableEq V] [Nonempty V]
    (G : SimpleGraph V) (U1 : Finset V) (hUcard : U1.card = 2 * ell)
    (hnPos : 0 < n) (hellPos : 0 < ell)
    (hellUpper : (ell : ℝ) ≤
      2 * AsymptoticThresholds.structuralDensity cR * n)
    (hfullCard : SupportCardPersists G U1 structuralUniformity
      (fixedStructuralTheta eps * Fintype.card V)
      (AsymptoticThresholds.structuralDensity cR *
        fixedStructuralTheta eps * n))
    (hunion :
      ((AsymptoticThresholds.structuralEdgeBudget
            (fixedStructuralEdgeCoefficient cR eps) n + 1 : ℕ) : ℝ) *
          AsymptoticThresholds.structuralTestCount (Fintype.card V) *
          (2 * Real.exp (-((fixedStructuralTheta eps) ^ 2 / 512) * ell)) < 1) :
    HalfSample.sliceProbability (by simpa using hUcard) (fun beta ↦
      ¬ StructuralEndpoint.SupportPersists G
        (StructuralEndpoint.halfSubset beta) structuralUniformity
        (fixedStructuralTheta eps * Fintype.card V)
        (AsymptoticThresholds.structuralDensity cR *
          fixedStructuralTheta eps / 4 * n)) < (1 : ℝ) / 2 := by
  let cS : ℝ := AsymptoticThresholds.structuralDensity cR
  let theta : ℝ := fixedStructuralTheta eps
  let QE : ℝ := fixedStructuralEdgeCoefficient cR eps
  let q : ℝ := theta ^ 2 / 512
  let global : ℝ := theta * Fintype.card V
  let firstLocal : ℝ := cS * theta * n
  let aDiv : ℝ := cS * theta / 4
  let edgeBudget : ℕ := AsymptoticThresholds.structuralEdgeBudget QE n
  let tests := supportPersistenceTests G structuralUniformity global
  have hcS : 0 < cS := by
    dsimp only [cS, AsymptoticThresholds.structuralDensity]
    positivity
  have htheta : 0 < theta := by
    dsimp only [theta, fixedStructuralTheta]
    positivity
  have hA : 0 < fixedStructuralCollisionConstant cR eps := by
    dsimp only [fixedStructuralCollisionConstant]
    exact AntiConcentration.variancePointMassConstant_pos hcS
      (mul_pos heps htheta) (by omega)
  have hQE : 0 < QE := by
    dsimp only [QE, fixedStructuralEdgeCoefficient]
    positivity
  have htests : tests.card ≤
      AsymptoticThresholds.structuralTestCount (Fintype.card V) := by
    dsimp only [tests, AsymptoticThresholds.structuralTestCount]
    simpa only [structuralUniformity] using
      card_supportPersistenceTests_le G structuralUniformity global
  have hhalfDecay :
      Real.exp (-((aDiv * n) ^ 2 / (8 * ell))) ≤
        Real.exp (-q * ell) := by
    have ha : (cS * theta / 4) * (n : ℝ) = cS * theta * n / 4 := by ring
    dsimp only [aDiv, q]
    rw [ha]
    exact fixedStructural_halfExposure_exp_le
      hcS htheta hnPos hellPos hellUpper
  have hunion' :
      ((edgeBudget + 1 : ℕ) : ℝ) *
          AsymptoticThresholds.structuralTestCount (Fintype.card V) *
          (2 * Real.exp (-q * ell)) < 1 := by
    simpa only [edgeBudget, QE, q] using hunion
  have hcoef : ((edgeBudget + 1 : ℕ) : ℝ) * tests.card ≤
      ((edgeBudget + 1 : ℕ) : ℝ) *
        AsymptoticThresholds.structuralTestCount (Fintype.card V) := by
    apply mul_le_mul_of_nonneg_left
    · exact_mod_cast htests
    · positivity
  have htail : 2 * Real.exp (-((aDiv * n) ^ 2 / (8 * ell))) ≤
      2 * Real.exp (-q * ell) :=
    mul_le_mul_of_nonneg_left hhalfDecay (by norm_num)
  have hhalfScaled :
      ((edgeBudget + 1 : ℕ) : ℝ) * tests.card *
          (2 * Real.exp (-((aDiv * n) ^ 2 / (8 * ell)))) < 1 :=
    lt_of_le_of_lt (mul_le_mul hcoef htail (by positivity) (by positivity))
      hunion'
  have hedgePos : 0 < edgeBudget := by
    dsimp only [edgeBudget, AsymptoticThresholds.structuralEdgeBudget]
    exact Nat.ceil_pos.mpr (by positivity)
  have hhalfBudget :
      tests.card * (2 * Real.exp (-((aDiv * n) ^ 2 / (8 * ell)))) <
        (1 : ℝ) / 2 := by
    have htail0 : 0 ≤ tests.card *
        (2 * Real.exp (-((aDiv * n) ^ 2 / (8 * ell)))) := by positivity
    have hfactor : (2 : ℝ) ≤ edgeBudget + 1 := by
      exact_mod_cast (show 2 ≤ edgeBudget + 1 by omega)
    have hscaled := mul_le_mul_of_nonneg_right hfactor htail0
    have hhalfScaled' : (edgeBudget + 1 : ℝ) *
        (tests.card * (2 * Real.exp (-((aDiv * n) ^ 2 / (8 * ell))))) < 1 := by
      simpa only [mul_assoc, Nat.cast_add, Nat.cast_one] using hhalfScaled
    have htwoLt := hscaled.trans_lt hhalfScaled'
    apply (lt_div_iff₀ (by norm_num : (0 : ℝ) < 2)).2
    nlinarith only [htwoLt]
  let thetaHalf : ℝ := firstLocal / ell
  have hthetaHalf : 0 ≤ thetaHalf := by
    dsimp only [thetaHalf, firstLocal]
    positivity
  have hfullHalf : SupportCardPersists G U1 structuralUniformity global
      (thetaHalf * ell) := by
    have heq : thetaHalf * (ell : ℝ) = firstLocal := by
      dsimp only [thetaHalf]
      field_simp [show (ell : ℝ) ≠ 0 by positivity]
    have hf : SupportCardPersists G U1 structuralUniformity global
        firstLocal := by
      simpa only [global, firstLocal, cS, theta] using hfullCard
    rwa [heq]
  apply halfSupportPersists_failure_probability_lt_half G U1 ell
    structuralUniformity (by simpa using hUcard) hellPos
    global thetaHalf (aDiv * n) hthetaHalf hfullHalf
  · have heq : (thetaHalf / 2) * (ell : ℝ) / 2 = aDiv * n := by
      dsimp only [thetaHalf, firstLocal, aDiv]
      field_simp [show (ell : ℝ) ≠ 0 by positivity]
      ring
    rw [heq]
  · have heq : (thetaHalf / 2) * (ell : ℝ) / 2 = aDiv * n := by
      dsimp only [thetaHalf, firstLocal, aDiv]
      field_simp [show (ell : ℝ) ≠ 0 by positivity]
      ring
    have hexp : -((aDiv * n) ^ 2 / (8 * ell)) =
        -(aDiv * n) ^ 2 / (8 * ell) := by ring
    simpa only [tests, heq, global, aDiv, cS, theta, hexp] using hhalfBudget

/-- The selected first slice together with every graph-facing fact consumed
by the deterministic endpoint. -/
structure FixedAmbientSelectedSliceData (G : SimpleGraph V)
    (cR eps : ℝ) (n ell : ℕ) where
  U1 : Finset V
  retained : Finset V
  hUcard : Fintype.card U1 = 2 * ell
  hretained : AsymptoticThresholds.structuralSortingSize cR n ≤
    (retained \ U1).card
  hfiber : ∀ z : ℕ, ((retained \ U1).filter fun x ↦
    (Erdos88.neighborsIn G x U1).card = z).card ≤
      AsymptoticThresholds.structuralDegreeBudget
        (fixedStructuralDegreeCoefficient cR eps) n + 1
  hfullPersist : StructuralEndpoint.SupportPersists G U1 structuralUniformity
    (fixedStructuralTheta eps * Fintype.card V)
    (AsymptoticThresholds.structuralDensity cR *
      fixedStructuralTheta eps / 4 * n)
  hhalfFail : HalfSample.sliceProbability hUcard (fun beta ↦
    ¬ StructuralEndpoint.SupportPersists G
      (StructuralEndpoint.halfSubset beta) structuralUniformity
      (fixedStructuralTheta eps * Fintype.card V)
      (AsymptoticThresholds.structuralDensity cR *
        fixedStructuralTheta eps / 4 * n)) < (1 : ℝ) / 2

/-- Select the first random slice and discharge both the full-slice and
random-half persistence estimates. -/
theorem exists_fixedAmbient_selectedSlice
    {cR eps : ℝ} (hcR : 0 < cR) (hcR1 : cR ≤ 1)
    (heps : 0 < eps) (heps1 : eps < 1)
    {n m ell : ℕ} {V : Type u} [Fintype V] [DecidableEq V] [Nonempty V]
    (hmCard : m = Fintype.card V)
    (hmLower : cR * n ≤ (m : ℝ)) (hmUpper : (m : ℝ) ≤ n)
    (G : SimpleGraph V)
    (hrich : KwanSudakovRich G (eps ^ structuralUniformity) eps)
    (hellLower : AsymptoticThresholds.structuralDensity cR * n ≤ ell)
    (hellUpper : (ell : ℝ) ≤
      2 * AsymptoticThresholds.structuralDensity cR * n)
    (hnum : FixedStructuralNumericalData cR eps n m ell) :
    Nonempty (FixedAmbientSelectedSliceData G cR eps n ell) := by
  subst m
  let cS : ℝ := AsymptoticThresholds.structuralDensity cR
  let theta : ℝ := fixedStructuralTheta eps
  let A : ℝ := fixedStructuralCollisionConstant cR eps
  let QE : ℝ := fixedStructuralEdgeCoefficient cR eps
  let QD : ℝ := fixedStructuralDegreeCoefficient cR eps
  let cGap : ℝ := fixedStructuralGapDensity cR eps
  let aDiv : ℝ := cS * theta / 4
  let q : ℝ := theta ^ 2 / 512
  have htheta : 0 < theta := by
    dsimp only [theta, fixedStructuralTheta]
    positivity
  have hcS : 0 < cS := by
    dsimp only [cS, AsymptoticThresholds.structuralDensity]
    positivity
  have hA : 0 < A := by
    dsimp only [A, fixedStructuralCollisionConstant]
    exact AntiConcentration.variancePointMassConstant_pos hcS
      (mul_pos heps htheta) (by omega)
  have hQE : 0 < QE := by
    dsimp only [QE, fixedStructuralEdgeCoefficient]
    positivity
  classical
  letI : LinearOrder V :=
    LinearOrder.lift' (Fintype.equivFin V) (Fintype.equivFin V).injective
  let m : ℕ := Fintype.card V
  have hmPos : 0 < m := by dsimp only [m]; exact Fintype.card_pos
  have hmUpperNat : m ≤ n := by exact_mod_cast hmUpper
  have hnPos : 0 < n := lt_of_lt_of_le hmPos hmUpperNat
  have hellPosReal : (0 : ℝ) < ell :=
    (mul_pos hcS (by exact_mod_cast hnPos)).trans_le hellLower
  have hellPos : 0 < ell := by exact_mod_cast hellPosReal
  have hfixedNow := hnum.fixed
  have hunionNow := hnum.unionBudget
  have hmiddleNow := hnum.middleRoom
  have hpruneNow := hnum.pruningBudget
  have hcollisionNow := hnum.collisionBudget
  have hr := hnum.sunflowerSize
  have hcandidateNumerical := hnum.candidateNumerical
  have hmatchingLarge := hnum.matchingLarge
  let global : ℝ := theta * m
  let firstLocal : ℝ := cS * theta * n
  let edgeBudget : ℕ := AsymptoticThresholds.structuralEdgeBudget QE n
  let degreeBudget : ℕ := AsymptoticThresholds.structuralDegreeBudget QD n
  let tests := supportPersistenceTests G structuralUniformity global
  have htests : tests.card ≤ AsymptoticThresholds.structuralTestCount m := by
    dsimp only [tests, AsymptoticThresholds.structuralTestCount]
    simpa only [structuralUniformity] using
      card_supportPersistenceTests_le G structuralUniformity global
  have hfirstDecay :
      Real.exp (-firstLocal ^ 2 / (8 * (2 * ell : ℕ))) ≤
        Real.exp (-q * ell) := by
    simpa only [firstLocal, q] using
      fixedStructural_firstExposure_exp_le hcS htheta hnPos hellPos hellUpper
  have hpersistBudget :
      ((edgeBudget + 1 : ℕ) : ℝ) * tests.card *
          (2 * Real.exp (-firstLocal ^ 2 / (8 * (2 * ell : ℕ)))) < 1 := by
    apply lt_of_le_of_lt _ hunionNow
    dsimp only [edgeBudget]
    gcongr
  have hcoreCard : (StructuralRandom.richCore G eps).card ≤ m := by
    exact Finset.card_le_card (Finset.subset_univ _)
  have hcollisionActual :
      ((StructuralRandom.richCore G eps).card : ℝ) *
            AsymptoticThresholds.structuralExceptionalSize m +
          (StructuralRandom.richCore G eps).card.choose 2 *
            (A / Real.sqrt m) < edgeBudget := by
    apply lt_of_le_of_lt _ hcollisionNow
    apply add_le_add
    · gcongr
    · gcongr
  have hselectionBudget :
      ((edgeBudget + 1 : ℕ) : ℝ) * tests.card *
            (2 * Real.exp (-firstLocal ^ 2 / (8 * (2 * ell : ℕ)))) +
          (StructuralRandom.richCore G eps).card *
            ⌈(m : ℝ) ^ (1 / 5 : ℝ)⌉₊ +
          (StructuralRandom.richCore G eps).card.choose 2 *
            (AntiConcentration.variancePointMassConstant
                cS (eps * theta) 1 / Real.sqrt m) <
        edgeBudget + 1 := by
    have hAeq : AntiConcentration.variancePointMassConstant
        cS (eps * theta) 1 = A := by
      rfl
    have hexceptional : AsymptoticThresholds.structuralExceptionalSize m =
        ⌈(m : ℝ) ^ (1 / 5 : ℝ)⌉₊ := rfl
    rw [← hexceptional, hAeq]
    nlinarith
  have hepsLe : eps ≤ 1 := heps1.le
  have hdeltaEps : eps ^ structuralUniformity ≤ eps := by
    simpa only [pow_one] using
      (pow_le_pow_of_le_one heps.le hepsLe
        (by simp [structuralUniformity] : 1 ≤ structuralUniformity))
  have hdeltaOne : eps ^ structuralUniformity ≤ 1 :=
    hdeltaEps.trans hepsLe
  have hthetaUpper : theta ≤ eps ^ 2 / 2 := by
    dsimp only [theta, fixedStructuralTheta]
    calc
      eps ^ structuralUniformity * (eps / 2) ≤
          eps * (eps / 2) :=
        mul_le_mul_of_nonneg_right hdeltaEps (by positivity)
      _ = eps ^ 2 / 2 := by ring
  have hmargin : ∀ p ∈ tests,
      2 * firstLocal ≤ (2 * ell : ℕ) / (m : ℝ) *
        supportDiffCard G Finset.univ p.1 p.2 := by
    intro p hp
    have hpGlobal : global ≤
        supportDiffCard G Finset.univ p.1 p.2 :=
      (mem_supportPersistenceTests.mp hp).2.2
    have hmReal : (0 : ℝ) < m := by exact_mod_cast hmPos
    have hscaled := mul_le_mul_of_nonneg_left hpGlobal
      (show 0 ≤ (2 * ell : ℕ) / (m : ℝ) by positivity)
    calc
      2 * firstLocal = 2 * cS * theta * n := by simp only [firstLocal]; ring
      _ ≤ theta * (2 * ell : ℕ) := by
        push_cast
        calc
          2 * cS * theta * (n : ℝ) =
              theta * (2 * (cS * n)) := by ring
          _ ≤ theta * (2 * (ell : ℝ)) := by gcongr
          _ = theta * (2 * (ell : ℝ)) := rfl
      _ = (2 * ell : ℕ) / (m : ℝ) * global := by
        dsimp only [global]
        field_simp [hmReal.ne']
      _ ≤ (2 * ell : ℕ) / (m : ℝ) *
          supportDiffCard G Finset.univ p.1 p.2 := hscaled
  letI : Nonempty (Erdos88.Fourier.BoolSlice V (2 * ell)) := by
    have hsle : 2 * ell ≤ Fintype.card V := by
      simpa only [m] using hfixedNow.two_parameter_le
    obtain ⟨S, _hSsub, hScard⟩ :=
      Finset.exists_subset_card_eq (s := (Finset.univ : Finset V)) hsle
    exact ⟨(Erdos88.Fourier.boolSliceEquivFinsetLen V (2 * ell)).symm
      ⟨S, hScard⟩⟩
  obtain ⟨omega, W, hUcard, _hfullIncidence, hnofail,
      _hcoreW, _hcoreAmbient, hambient, _hWsub, _hWU1, hfiber⟩ :=
    StructuralRandom.exists_rich_graphSlice_supportPersistent_lowCollision
      G (eps ^ structuralUniformity) eps theta (2 * ell)
      structuralUniformity global firstLocal cS edgeBudget degreeBudget
      (by positivity) heps hdeltaEps hdeltaOne htheta hthetaUpper hrich
      hmPos hfixedNow.two_parameter_le (by omega) hcS
      (by dsimp only [cS, AsymptoticThresholds.structuralDensity]; nlinarith)
      (by
        simpa only [cS, m, Nat.cast_mul, Nat.cast_ofNat] using
          hfixedNow.selected_balance)
      (by
        have h := hfixedNow.unselected_balance
        rw [Nat.cast_sub hfixedNow.two_parameter_le] at h
        simpa only [cS, m, Nat.cast_mul, Nat.cast_ofNat] using h)
      (by dsimp only [firstLocal]; positivity)
      hmargin (by
        simpa only [tests, m, Nat.cast_add, Nat.cast_one] using
          hselectionBudget)
  let U1 := StructuralRandom.sliceFinset (2 * ell) omega
  let retained := W.image Subtype.val
  have hfullCard : SupportCardPersists G U1 structuralUniformity global firstLocal :=
    supportCardPersists_of_no_intersectionFailure G (2 * ell)
      structuralUniformity global firstLocal omega hnofail
  have hfullEndpoint : StructuralEndpoint.SupportPersists G U1
      structuralUniformity global (aDiv * n) :=
    supportPersists_of_supportCardPersists G U1 structuralUniformity
      global firstLocal (aDiv * n) hfullCard (by
        dsimp only [firstLocal, aDiv]
        nlinarith [mul_pos hcS htheta])
  have hhalfFail :
      HalfSample.sliceProbability
        (by simpa only [Fintype.card_coe, U1] using hUcard)
        (fun beta : HalfSample.Slice U1 ell ↦
          ¬ StructuralEndpoint.SupportPersists G
          (StructuralEndpoint.halfSubset beta) structuralUniformity
          global (aDiv * n)) < (1 : ℝ) / 2 := by
    have hcard : U1.card = 2 * ell := by simpa only [U1] using hUcard
    have hf : SupportCardPersists G U1 structuralUniformity
        (fixedStructuralTheta eps * Fintype.card V)
        (AsymptoticThresholds.structuralDensity cR *
          fixedStructuralTheta eps * n) := by
      simpa only [global, firstLocal, cS, theta, m] using hfullCard
    have hu := fixedAmbient_halfSupport_failure_probability_lt_half
      hcR heps G U1 hcard hnPos hellPos hellUpper hf
      (by simpa only [m] using hunionNow)
    simpa only [global, aDiv, cS, theta, m] using hu
  have hsortUpper :
      (AsymptoticThresholds.structuralSortingSize cR n : ℝ) ≤
        cR / 2 * n := by
    exact Nat.floor_le (by positivity)
  have htwoSort :
      2 * AsymptoticThresholds.structuralSortingSize cR n ≤ m := by
    exact_mod_cast (calc
      (((2 * AsymptoticThresholds.structuralSortingSize cR n : ℕ) : ℝ)) =
          2 * (AsymptoticThresholds.structuralSortingSize cR n : ℝ) := by
            push_cast
            rfl
      _ ≤ 2 * (cR / 2 * n) :=
        mul_le_mul_of_nonneg_left hsortUpper (by norm_num)
      _ = cR * n := by ring
      _ ≤ m := hmLower)
  have hretained : AsymptoticThresholds.structuralSortingSize cR n ≤
      (retained \ U1).card := by
    have hp : AsymptoticThresholds.structuralExceptionalSize m +
          (2 * edgeBudget) / (degreeBudget + 1) + 2 * ell ≤ m / 2 := by
      simpa only [m, edgeBudget, degreeBudget, QE, QD] using hpruneNow
    have ha : m ≤ (retained \ U1).card + 2 * ell +
        (2 * edgeBudget) / (degreeBudget + 1) +
        AsymptoticThresholds.structuralExceptionalSize m := by
      simpa only [m, retained, U1,
        AsymptoticThresholds.structuralExceptionalSize] using hambient
    have hs : AsymptoticThresholds.structuralSortingSize cR n ≤ m / 2 := by
      rw [Nat.le_div_iff_mul_le (by omega : 0 < (2 : ℕ))]
      omega
    have hw : m / 2 ≤ (retained \ U1).card := by omega
    exact hs.trans hw
  let hcard : Fintype.card U1 = 2 * ell := by
    simpa only [Fintype.card_coe, U1] using hUcard
  refine ⟨{
    U1 := U1
    retained := retained
    hUcard := hcard
    hretained := hretained
    hfiber := ?_
    hfullPersist := ?_
    hhalfFail := ?_ }⟩
  · simpa only [degreeBudget, QD] using hfiber
  · simpa only [global, theta, m, aDiv, cS] using hfullEndpoint
  · simpa only [global, theta, m, aDiv, cS] using hhalfFail

/-- Pointwise graph-facing assembly.  Its hypotheses are precisely the
numerical facts supplied eventually by the asymptotic threshold lemmas. -/
theorem nonempty_structuralWitness_of_fixedAmbient_numerical
    {cR eps : ℝ} (hcR : 0 < cR) (hcR1 : cR ≤ 1)
    (heps : 0 < eps) (heps1 : eps < 1)
    {n m ell : ℕ} {V : Type u} [Fintype V] [DecidableEq V] [Nonempty V]
    (hmCard : m = Fintype.card V)
    (hmLower : cR * n ≤ (m : ℝ)) (hmUpper : (m : ℝ) ≤ n)
    (G : SimpleGraph V)
    (hrich : KwanSudakovRich G (eps ^ structuralUniformity) eps)
    (alpha : ℝ) (halpha : (1 : ℝ) / 2 ≤ alpha)
    (hellLower : AsymptoticThresholds.structuralDensity cR * n ≤ ell)
    (hellUpper : (ell : ℝ) ≤
      2 * AsymptoticThresholds.structuralDensity cR * n)
    (hnum : FixedStructuralNumericalData cR eps n m ell) :
    Nonempty (StructuralWitness G n
      ⌊AsymptoticThresholds.structuralDensity cR * n⌋₊ ell
      structuralUniformity alpha
      (cR * fixedStructuralGapDensity cR eps / 1600)
      (AsymptoticThresholds.structuralDensity cR *
        fixedStructuralTheta eps / 4) ((1 : ℝ) / 4)) := by
  subst m
  let cS : ℝ := AsymptoticThresholds.structuralDensity cR
  let theta : ℝ := fixedStructuralTheta eps
  let QD : ℝ := fixedStructuralDegreeCoefficient cR eps
  let cGap : ℝ := fixedStructuralGapDensity cR eps
  let aDisc : ℝ := cR * cGap / 1600
  let aDiv : ℝ := cS * theta / 4
  have hcS : 0 < cS := by
    dsimp only [cS, AsymptoticThresholds.structuralDensity]
    positivity
  have hepsLe : eps ≤ 1 := heps1.le
  classical
  letI : LinearOrder V :=
    LinearOrder.lift' (Fintype.equivFin V) (Fintype.equivFin V).injective
  let m : ℕ := Fintype.card V
  have hfixedNow := hnum.fixed
  have hmiddleNow := hnum.middleRoom
  have hr := hnum.sunflowerSize
  have hcandidateNumerical := hnum.candidateNumerical
  have hmatchingLarge := hnum.matchingLarge
  obtain ⟨⟨U1, retained, hUcard, hretained, hfiber,
      hfullEndpoint, hhalfFail⟩⟩ :=
    exists_fixedAmbient_selectedSlice hcR hcR1 heps heps1
      (n := n) (m := m) (ell := ell) (V := V) rfl hmLower hmUpper
      G hrich hellLower hellUpper (by simpa only [m] using hnum)
  have hfit : AsymptoticThresholds.structuralSortingSize cR n + 2 * ell +
      AsymptoticThresholds.structuralCandidateSize cR n ≤ m := by
    have hsortUpper :
        (AsymptoticThresholds.structuralSortingSize cR n : ℝ) ≤
          cR / 2 * n := Nat.floor_le (by positivity)
    have hcandidateUpper :
        (AsymptoticThresholds.structuralCandidateSize cR n : ℝ) ≤
          cR / 4 * n := Nat.floor_le (by positivity)
    exact_mod_cast (calc
      (AsymptoticThresholds.structuralSortingSize cR n : ℝ) +
            (2 * ell : ℕ) +
            AsymptoticThresholds.structuralCandidateSize cR n
          ≤ cR / 2 * n + 4 * cS * n + cR / 4 * n := by
            push_cast
            nlinarith
      _ ≤ cR * n := by
        dsimp only [cS, AsymptoticThresholds.structuralDensity]
        nlinarith [mul_nonneg hcR.le (Nat.cast_nonneg n)]
      _ ≤ m := hmLower)
  have hWsize : 2 * AsymptoticThresholds.structuralSwitchingSize cR n ≤
      AsymptoticThresholds.structuralSortingSize cR n := by omega
  have hscore :
      4 * (aDisc * n * Real.sqrt n) ≤
        alpha * AsymptoticThresholds.structuralSwitchingSize cR n *
          (AsymptoticThresholds.structuralGapSize cGap n + 1) := by
    have hnonneg : 0 ≤
        (AsymptoticThresholds.structuralSwitchingSize cR n : ℝ) *
          (AsymptoticThresholds.structuralGapSize cGap n + 1) := by positivity
    dsimp only [aDisc]
    nlinarith [hfixedNow.score_lower,
      mul_le_mul_of_nonneg_right halpha hnonneg]
  apply structuralWitness_of_selectedSlice_and_candidateReservoir
    (G := G) (ε := eps) (aDisc := aDisc) (aDiv := aDiv)
    (b := (1 : ℝ) / 4) (α := alpha) (scale := n)
    (nW := AsymptoticThresholds.structuralSwitchingSize cR n)
    (ell := ell) (K := structuralUniformity)
    (r := CandidateThresholds.sunflowerSize n)
    (Q := AsymptoticThresholds.structuralDegreeBudget QD n + 1)
    (g := AsymptoticThresholds.structuralGapSize cGap n)
    (wSize := AsymptoticThresholds.structuralSortingSize cR n)
    (candidateSize := AsymptoticThresholds.structuralCandidateSize cR n)
    (hε := heps) (hεone := hepsLe) (hrich := hrich)
    (U1 := U1) (retained := retained)
    (hU1card := by simpa only [Fintype.card_coe] using hUcard)
    (hretained := hretained) (hfiber := by simpa only [QD] using hfiber)
    (hfit := by simpa only [m] using hfit) (halpha := by linarith)
    (hnW := hfixedNow.switching_pos) (hWsize := hWsize)
    (hmiddle := hmiddleNow) (hscoreScale := hscore) (hr := hr)
  · simpa only [fixedStructuralTheta, aDiv, cS, theta] using hfullEndpoint
  · simpa only [fixedStructuralTheta, aDiv, cS, theta] using hhalfFail
  · simp [structuralUniformity]
  · simpa only [structuralUniformity,
      AsymptoticThresholds.structuralCandidateSize,
      CandidateThresholds.reservoirSize,
      CandidateThresholds.exceptionalSize,
      AsymptoticThresholds.structuralExceptionalSize,
      CandidateThresholds.candidateTarget] using hcandidateNumerical
  · simpa only [CandidateThresholds.exceptionalSize,
      AsymptoticThresholds.structuralExceptionalSize] using hmatchingLarge

/-- Exact eventual structural lemma for a fixed rich ambient graph.  All
probabilistic choices and numerical estimates have been discharged; the only
graph hypothesis is the Kwan--Sudakov richness condition itself. -/
theorem eventually_nonempty_structuralWitness_of_ksRich_fixedAmbient
    {cR eps : ℝ} (hcR : 0 < cR) (hcR1 : cR ≤ 1)
    (heps : 0 < eps) (heps1 : eps < 1) :
    ∃ cW cS aDisc aDiv b : ℝ,
      0 < cW ∧ 0 < cS ∧ 0 < aDisc ∧ 0 < aDiv ∧ 0 < b ∧
      ∃ N : ℕ, ∀ n ≥ N,
        ∀ (V : Type u) [Fintype V] [DecidableEq V] [Nonempty V],
          cR * n ≤ Fintype.card V →
          (Fintype.card V : ℝ) ≤ n →
          ∀ G : SimpleGraph V,
            KwanSudakovRich G (eps ^ structuralUniformity) eps →
            ∀ alpha : ℝ, (1 : ℝ) / 2 ≤ alpha → alpha ≤ 1 →
            ∀ ell : ℕ, cS * n ≤ ell →
              (ell : ℝ) ≤ 2 * cS * n →
              Nonempty (StructuralWitness G n ⌊cW * n⌋₊ ell
                structuralUniformity alpha aDisc aDiv b) := by
  let cS : ℝ := AsymptoticThresholds.structuralDensity cR
  let theta : ℝ := fixedStructuralTheta eps
  let A : ℝ := fixedStructuralCollisionConstant cR eps
  let QE : ℝ := fixedStructuralEdgeCoefficient cR eps
  let QD : ℝ := fixedStructuralDegreeCoefficient cR eps
  let cGap : ℝ := fixedStructuralGapDensity cR eps
  let aDisc : ℝ := cR * cGap / 1600
  let aDiv : ℝ := cS * theta / 4
  let q : ℝ := theta ^ 2 / 512
  obtain ⟨htheta, hA, hQE, hAQE, hQD, hpruneConstants,
      hcGap, hmiddleConstants⟩ := fixedStructural_constants hcR heps
  have hcS : 0 < cS := by
    dsimp only [cS, AsymptoticThresholds.structuralDensity]
    positivity
  have haDisc : 0 < aDisc := by dsimp only [aDisc]; positivity
  have haDiv : 0 < aDiv := by dsimp only [aDiv]; positivity
  have hq : 0 < q := by dsimp only [q]; positivity
  obtain ⟨Nfixed, hfixed⟩ :=
    AsymptoticThresholds.exists_fixedAmbientBounds hcR hcR1 hcGap
  obtain ⟨Nunion, hunion⟩ :=
    AsymptoticThresholds.exists_structuralUnionBudget hcR hQE hq
  obtain ⟨Nmiddle, hmiddle⟩ :=
    AsymptoticThresholds.exists_structuralMiddleRoom hcR hQD hcGap
      hmiddleConstants
  obtain ⟨Nprune, hprune⟩ :=
    AsymptoticThresholds.exists_structuralPruningBudget hcR hQE hQD
      hpruneConstants
  obtain ⟨Ncollision, hcollision⟩ :=
    AsymptoticThresholds.exists_structuralCollisionBudget hA.le hQE hAQE
  obtain ⟨Ncandidate, hcandidate⟩ :=
    CandidateThresholds.exists_candidateThreshold cR hcR
  let N := Nfixed + Nunion + Nmiddle + Nprune + Ncollision + Ncandidate
  refine ⟨cS, cS, aDisc, aDiv, (1 : ℝ) / 4,
    hcS, hcS, haDisc, haDiv, by norm_num, N, ?_⟩
  intro n hn V _instFintype _instDecidable _instNonempty
    hmLower hmUpper G hrich alpha halpha _halphaUpper ell hellLower hellUpper
  let m : ℕ := Fintype.card V
  have hmPos : 0 < m := by dsimp only [m]; exact Fintype.card_pos
  have hmUpperNat : m ≤ n := by exact_mod_cast hmUpper
  have hNfixed : Nfixed ≤ n := by dsimp only [N] at hn; omega
  have hNunion : Nunion ≤ n := by dsimp only [N] at hn; omega
  have hNmiddle : Nmiddle ≤ n := by dsimp only [N] at hn; omega
  have hNprune : Nprune ≤ n := by dsimp only [N] at hn; omega
  have hNcollision : Ncollision ≤ n := by dsimp only [N] at hn; omega
  have hNcandidate : Ncandidate ≤ n := by dsimp only [N] at hn; omega
  have hfixedNow := hfixed n hNfixed m ell hmLower hmUpperNat
    hellLower hellUpper
  have hunionNow := hunion n hNunion m ell hmUpperNat hellLower
  have hmiddleNow := hmiddle n hNmiddle
  have hpruneNow := hprune n hNprune m ell hmLower hmUpperNat hellUpper
  have hcollisionNow := hcollision n hNcollision m hmPos hmUpperNat
  obtain ⟨hr, hcandidateNumerical, hmatchingLarge,
      _hcandidateUpper, _hcandidateLower⟩ :=
    hcandidate n hNcandidate m hmLower hmUpperNat
  have hnum : FixedStructuralNumericalData cR eps n m ell := {
    fixed := by simpa only [cGap] using hfixedNow
    unionBudget := by simpa only [QE, q, theta] using hunionNow
    middleRoom := by simpa only [QD, cGap] using hmiddleNow
    pruningBudget := by simpa only [QE, QD] using hpruneNow
    collisionBudget := by simpa only [A, QE] using hcollisionNow
    sunflowerSize := hr
    candidateNumerical := hcandidateNumerical
    matchingLarge := hmatchingLarge }
  have hout := nonempty_structuralWitness_of_fixedAmbient_numerical
    hcR hcR1 heps heps1 (n := n) (m := m) (ell := ell) (V := V)
    rfl hmLower hmUpper G hrich alpha halpha hellLower hellUpper hnum
  simpa only [cS, cGap, aDisc, aDiv, theta] using hout

end

end Erdos636.StructuralIntegration
