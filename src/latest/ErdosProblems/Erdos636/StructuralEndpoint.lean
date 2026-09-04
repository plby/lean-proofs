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

import ErdosProblems.Erdos636.DegreeSorting
import ErdosProblems.Erdos636.HalfSample
import ErdosProblems.Erdos636.Structural

/-!
# Deterministic endpoint of the structural argument

This file joins the two deterministic choices at the end of the
Kwan--Sudakov structural argument.  A bounded fibre for the degrees into a
fixed twice-reservoir `U1` separates equal bottom and top blocks of `W`.
If their full-reservoir weighted scores are already separated, `U1` is the
two-copy reservoir.  Otherwise half-sample symmetry selects an `ell`-subset
of `U1` for which the reversed weighted score is separated.  A supplied
strict half-sample failure bound makes that choice simultaneously preserve
all global support differences needed by the candidate-family thinning.

The last theorem calls `structuralWitness_of_candidateFamily`; consequently
all losses from common-neighbourhood counting, sunflower extraction, and
Turán thinning remain explicit in its hypotheses.
-/

open Classical SimpleGraph
open scoped BigOperators

namespace Erdos636.StructuralEndpoint

open Erdos88.Fourier

universe u

noncomputable section

variable {V : Type u} [Fintype V] [DecidableEq V]

/-- Cross-incidences can be summed from either endpoint class. -/
lemma degreeInto_comm (G : SimpleGraph V) (A B : Finset V) :
    degreeInto G A B = degreeInto G B A := by
  classical
  simp only [degreeInto, Erdos88.neighborsIn, Finset.card_filter,
    Finset.sum_filter]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro b hb
  apply Finset.sum_congr rfl
  intro a ha
  simp only [G.adj_comm a b]

/-- The graph-facing degree sum is the sorted sum of singleton degrees. -/
lemma crossEdges_eq_sum_degreeInto_singleton
    (G : SimpleGraph V) (U W : Finset V) :
    (crossEdges G U W : ℤ) =
      ∑ w ∈ W, ((Erdos88.neighborsIn G w U).card : ℤ) := by
  rw [crossEdges, degreeInto_comm]
  simp [degreeInto]

/-- Lift a point of the half-slice of `U1` to an ambient vertex set. -/
def halfSubset {U1 : Finset V} {ell : ℕ}
    (omega : HalfSample.Slice U1 ell) : Finset V :=
  liftInducedFinset omega.1

@[simp] lemma card_halfSubset {U1 : Finset V} {ell : ℕ}
    (omega : HalfSample.Slice U1 ell) :
    (halfSubset omega).card = ell := by
  simp [halfSubset, omega.2]

lemma halfSubset_subset {U1 : Finset V} {ell : ℕ}
    (omega : HalfSample.Slice U1 ell) :
    halfSubset omega ⊆ U1 := by
  intro v hv
  obtain ⟨u, _hu, rfl⟩ := mem_liftInducedFinset.mp hv
  exact u.2

/-- The exact support-persistence property required after the first random
exposure.  It is deliberately phrased with global support cardinality and
local incidence mass: global `ℓ¹` mass does not imply this statement. -/
def SupportPersists (G : SimpleGraph V) (U0 : Finset V) (K : ℕ)
    (globalThreshold localThreshold : ℝ) : Prop :=
  ∀ X Y : Finset V,
    X.card ≤ K → Y.card ≤ K →
      globalThreshold ≤ supportDiffCard G Finset.univ X Y →
      localThreshold ≤ incidenceDiffMass G U0 X Y

/-- The cross-edge difference over a lifted half-slice is an affine
half-sample sum. -/
lemma crossEdges_sub_eq_sliceSum
    (G : SimpleGraph V) {U1 low high : Finset V} {ell : ℕ}
    (omega : HalfSample.Slice U1 ell) :
    ((crossEdges G (halfSubset omega) low : ℝ) -
        crossEdges G (halfSubset omega) high) =
      HalfSample.sliceSum
        (fun u : U1 ↦
          ((Erdos88.neighborsIn G u.1 low).card : ℝ) -
            (Erdos88.neighborsIn G u.1 high).card) omega := by
  rw [crossEdges, crossEdges, degreeInto, degreeInto,
    HalfSample.sliceSum, Finset.sum_sub_distrib]
  simp only [halfSubset, liftInducedFinset]
  rw [
    Finset.sum_image (s := omega.1) (g := Subtype.val)
      Subtype.val_injective.injOn,
    Finset.sum_image (s := omega.1) (g := Subtype.val)
      Subtype.val_injective.injOn]
  norm_cast

/-- The total coefficient sum in the half-sample identity is the
full-reservoir cross-edge difference. -/
lemma crossEdges_sub_eq_sum_subtype
    (G : SimpleGraph V) (U1 low high : Finset V) :
    ((crossEdges G U1 low : ℝ) - crossEdges G U1 high) =
      ∑ u : U1,
        (((Erdos88.neighborsIn G (u : V) low).card : ℝ) -
          (Erdos88.neighborsIn G (u : V) high).card) := by
  rw [crossEdges, crossEdges, degreeInto, degreeInto]
  change
    (↑(∑ u ∈ U1, (Erdos88.neighborsIn G u low).card) : ℝ) -
        ↑(∑ u ∈ U1, (Erdos88.neighborsIn G u high).card) = _
  have hlowNat :
      (∑ u ∈ U1, (Erdos88.neighborsIn G u low).card) =
        ∑ u : U1, (Erdos88.neighborsIn G (u : V) low).card := by
    rw [← Finset.sum_attach, Finset.attach_eq_univ]
  have hhighNat :
      (∑ u ∈ U1, (Erdos88.neighborsIn G u high).card) =
        ∑ u : U1, (Erdos88.neighborsIn G (u : V) high).card := by
    rw [← Finset.sum_attach, Finset.attach_eq_univ]
  rw [hlowNat, hhighNat, Nat.cast_sum, Nat.cast_sum]
  simpa only using (Finset.sum_sub_distrib
    (s := (Finset.univ : Finset U1))
    (fun u ↦ ((Erdos88.neighborsIn G (u : V) low).card : ℝ))
    (fun u ↦ ((Erdos88.neighborsIn G (u : V) high).card : ℝ))).symm

/-- A strict `< 1/2` failure estimate intersects the half-symmetry event. -/
theorem exists_halfSubset_ge_half_total_and_not_bad
    {U1 : Finset V} {ell : ℕ}
    (hcard : Fintype.card U1 = 2 * ell)
    (a : U1 → ℝ) (Bad : HalfSample.Slice U1 ell → Prop)
    (hbad : HalfSample.sliceProbability hcard Bad < (1 : ℝ) / 2) :
    ∃ omega : HalfSample.Slice U1 ell,
      (∑ u, a u) / 2 ≤ HalfSample.sliceSum a omega ∧ ¬ Bad omega := by
  let : Nonempty (HalfSample.Slice U1 ell) := HalfSample.sliceNonempty hcard
  have hgood :=
    HalfSample.one_half_le_sliceProbability_ge_half_total hcard a
  by_contra hnone
  push_neg at hnone
  have hmono :
      HalfSample.sliceProbability hcard (fun omega ↦
          (∑ u, a u) / 2 ≤ HalfSample.sliceSum a omega) ≤
        HalfSample.sliceProbability hcard Bad := by
    simpa only [HalfSample.sliceProbability] using
      finProbability_mono (HalfSample.Slice U1 ell)
        (fun omega homega ↦ hnone omega homega)
  exact (not_lt_of_ge (hgood.trans hmono)) hbad

/-- Deterministic completion of the endpoint/reservoir stage.

The degree fibre bound is the graph-facing consequence of the bounded
collision degree furnished by the first random exposure.  The last strict
probability hypothesis is precisely the support-difference persistence
estimate for the possible half-reservoir. -/
theorem structuralWitness_of_sorted_twiceReservoir
    [Nonempty V] {G : SimpleGraph V}
    {δ ε aDisc aDiv b α : ℝ}
    {scale nW ell K r Q g : ℕ}
    (hδ : 0 < δ) (hε : 0 < ε)
    (hrich : KwanSudakovRich G δ ε)
    (U1 W A0 : Finset V)
    (hU1card : Fintype.card U1 = 2 * ell)
    (hWU1 : Disjoint W U1)
    (hAaway : Disjoint A0 (W ∪ U1))
    (halpha : 0 ≤ α)
    (hnW : 0 < nW)
    (hWsize : 2 * nW ≤ W.card)
    (hfiber : ∀ z : ℤ,
      (W.filter fun x ↦ ((Erdos88.neighborsIn G x U1).card : ℤ) = z).card ≤ Q)
    (hmiddle : Q * (g + 1) < W.card - 2 * nW)
    (hscoreScale :
      4 * (aDisc * scale * Real.sqrt scale) ≤
        α * nW * (g + 1))
    (hfullPersist : SupportPersists G U1 K
      (δ * (ε / 2) * Fintype.card V) (aDiv * scale))
    (hhalfFail :
      HalfSample.sliceProbability hU1card (fun omega ↦
        ¬ SupportPersists G (halfSubset omega) K
          (δ * (ε / 2) * Fintype.card V) (aDiv * scale)) < (1 : ℝ) / 2)
    (candidates : Finset (Finset V))
    (hcandidateSub : ∀ X ∈ candidates, X ⊆ A0)
    (hcandidateUniform : ∀ X ∈ candidates, X.card = K)
    (hcandidateCommon : ∀ X ∈ candidates,
      δ * Fintype.card V ≤ (Erdos88.commonNeighborFinset G X).card)
    (hr : 2 ≤ r)
    (hlarge :
      K.factorial * (r - 1) ^ K *
          (K * Fintype.card V + 1) ^ 3 < candidates.card)
    (hmatchingLarge :
      b * (scale : ℝ) ^ (3 / 4 : ℝ) *
          (⌈(Fintype.card V : ℝ) ^ (1 / 5 : ℝ)⌉₊ + 1) ≤ r) :
    Nonempty (StructuralWitness G scale nW ell K α aDisc aDiv b) := by
  obtain ⟨D, hsumGap⟩ :=
    DegreeSorting.exists_orderedThreeWaySplit_with_weighted_sum_gap
      W (fun x ↦ ((Erdos88.neighborsIn G x U1).card : ℤ))
      nW Q g α hnW hWsize hfiber hmiddle halpha
  have hhighCross :
      (∑ y ∈ D.high,
          ((((Erdos88.neighborsIn G y U1).card : ℤ)) : ℝ)) =
        (crossEdges G U1 D.high : ℝ) := by
    exact_mod_cast
      (crossEdges_eq_sum_degreeInto_singleton G U1 D.high).symm
  have hlowCross :
      (∑ x ∈ D.low,
          ((((Erdos88.neighborsIn G x U1).card : ℤ)) : ℝ)) =
        (crossEdges G U1 D.low : ℝ) := by
    exact_mod_cast
      (crossEdges_eq_sum_degreeInto_singleton G U1 D.low).symm
  have hcrossGap :
      α * (nW : ℝ) * (g + 1 : ℝ) ≤
        α * ((crossEdges G U1 D.high : ℝ) - crossEdges G U1 D.low) := by
    simpa only [hhighCross, hlowCross] using hsumGap
  have hlowHigh : Disjoint D.low D.high :=
    D.low_disjoint_rest.mono_right Finset.subset_union_right
  have hlowU1 : Disjoint D.low U1 :=
    hWU1.mono_left D.low_subset
  have hhighU1 : Disjoint D.high U1 :=
    hWU1.mono_left D.high_subset
  have hbaseFull : D.low ∪ D.high ∪ U1 ⊆ W ∪ U1 := by
    intro v hv
    rcases Finset.mem_union.mp hv with hv | hv
    · rcases Finset.mem_union.mp hv with hv | hv
      · exact Finset.mem_union_left _ (D.low_subset hv)
      · exact Finset.mem_union_left _ (D.high_subset hv)
    · exact Finset.mem_union_right _ hv
  let target : ℝ := aDisc * scale * Real.sqrt scale
  by_cases hfull : target ≤
      weightedScore G α U1 D.high - weightedScore G α U1 D.low
  · apply structuralWitness_of_candidateFamily hδ hε hrich
      D.low D.high U1 A0 hlowHigh hlowU1 hhighU1
      (hAaway.mono_right hbaseFull) D.low_card D.high_card
      (Or.inr (by simpa using hU1card))
      (by simpa only [target] using hfull)
      candidates hcandidateSub hcandidateUniform hcandidateCommon hr hlarge
    · intro X Y hX hY hXY
      exact hfullPersist X Y hX hY hXY
    · exact hmatchingLarge
  · have hfullLt :
        weightedScore G α U1 D.high - weightedScore G α U1 D.low < target :=
      lt_of_not_ge hfull
    let coeff : U1 → ℝ := fun u ↦
      α * (((Erdos88.neighborsIn G (u : V) D.low).card : ℝ) -
        (Erdos88.neighborsIn G (u : V) D.high).card)
    let Bad : HalfSample.Slice U1 ell → Prop := fun omega ↦
      ¬ SupportPersists G (halfSubset omega) K
        (δ * (ε / 2) * Fintype.card V) (aDiv * scale)
    obtain ⟨omega, homegaScore, homegaGood⟩ :=
      exists_halfSubset_ge_half_total_and_not_bad
        hU1card coeff Bad (by simpa only [Bad] using hhalfFail)
    let U0 := halfSubset omega
    have hU0sub : U0 ⊆ U1 := halfSubset_subset omega
    have hlowU0 : Disjoint D.low U0 := hlowU1.mono_right hU0sub
    have hhighU0 : Disjoint D.high U0 := hhighU1.mono_right hU0sub
    have hbaseHalf : D.low ∪ D.high ∪ U0 ⊆ W ∪ U1 := by
      intro v hv
      rcases Finset.mem_union.mp hv with hv | hv
      · rcases Finset.mem_union.mp hv with hv | hv
        · exact Finset.mem_union_left _ (D.low_subset hv)
        · exact Finset.mem_union_left _ (D.high_subset hv)
      · exact Finset.mem_union_right _ (hU0sub hv)
    have hcoeffTotal :
        (∑ u, coeff u) =
          α * ((crossEdges G U1 D.low : ℝ) - crossEdges G U1 D.high) := by
      calc
        (∑ u, coeff u) = α * ∑ u : U1,
            (((Erdos88.neighborsIn G (u : V) D.low).card : ℝ) -
              (Erdos88.neighborsIn G (u : V) D.high).card) := by
          change (∑ u ∈ (Finset.univ : Finset U1), α *
            (((Erdos88.neighborsIn G (u : V) D.low).card : ℝ) -
              (Erdos88.neighborsIn G (u : V) D.high).card)) = _
          exact ((Finset.mul_sum _ _) α).symm
        _ = α * ((crossEdges G U1 D.low : ℝ) -
            crossEdges G U1 D.high) := by
          rw [crossEdges_sub_eq_sum_subtype]
    have hmean : target ≤
        (Erdos88.inducedEdges G D.low : ℝ) - Erdos88.inducedEdges G D.high +
          (∑ u, coeff u) / 2 := by
      rw [hcoeffTotal]
      dsimp only [target] at hscoreScale ⊢
      simp only [weightedScore] at hfullLt
      nlinarith
    have hscoreHalf : target ≤
        weightedScore G α U0 D.low - weightedScore G α U0 D.high := by
      have hslice :
          ((Erdos88.inducedEdges G D.low : ℝ) - Erdos88.inducedEdges G D.high) +
              (∑ u, coeff u) / 2 ≤
            ((Erdos88.inducedEdges G D.low : ℝ) - Erdos88.inducedEdges G D.high) +
              HalfSample.sliceSum coeff omega :=
        by
          simpa only [add_comm] using
            add_le_add_left homegaScore
              ((Erdos88.inducedEdges G D.low : ℝ) -
                Erdos88.inducedEdges G D.high)
      apply hmean.trans
      rw [show HalfSample.sliceSum coeff omega =
          α * ((crossEdges G U0 D.low : ℝ) - crossEdges G U0 D.high) by
        rw [show HalfSample.sliceSum coeff omega =
            α * HalfSample.sliceSum
              (fun u : U1 ↦
                ((Erdos88.neighborsIn G (u : V) D.low).card : ℝ) -
                  (Erdos88.neighborsIn G (u : V) D.high).card) omega by
          rw [HalfSample.sliceSum, HalfSample.sliceSum]
          exact ((Finset.mul_sum _ _) α).symm]
        rw [← crossEdges_sub_eq_sliceSum G omega]] at hslice
      have hweighted :
          weightedScore G α U0 D.low - weightedScore G α U0 D.high =
            (Erdos88.inducedEdges G D.low : ℝ) -
              Erdos88.inducedEdges G D.high +
                α * ((crossEdges G U0 D.low : ℝ) -
                  crossEdges G U0 D.high) := by
        change
          ((Erdos88.inducedEdges G D.low : ℝ) +
              α * crossEdges G U0 D.low) -
            ((Erdos88.inducedEdges G D.high : ℝ) +
              α * crossEdges G U0 D.high) = _
        ring
      rw [hweighted]
      exact hslice
    have hpersist : SupportPersists G U0 K
        (δ * (ε / 2) * Fintype.card V) (aDiv * scale) := by
      exact not_not.mp (by simpa only [Bad, U0] using homegaGood)
    apply structuralWitness_of_candidateFamily hδ hε hrich
      D.high D.low U0 A0 hlowHigh.symm hhighU0 hlowU0
      (hAaway.mono_right (by
        intro v hv
        rcases Finset.mem_union.mp hv with hv | hv
        · rcases Finset.mem_union.mp hv with hv | hv
          · exact Finset.mem_union_left _ (D.high_subset hv)
          · exact Finset.mem_union_left _ (D.low_subset hv)
        · exact Finset.mem_union_right _ (hU0sub hv)))
      D.high_card D.low_card
      (Or.inl (by simp [U0]))
      (by simpa only [target] using hscoreHalf)
      candidates hcandidateSub hcandidateUniform hcandidateCommon hr hlarge
    · intro X Y hX hY hXY
      exact hpersist X Y hX hY hXY
    · exact hmatchingLarge

end

end Erdos636.StructuralEndpoint
