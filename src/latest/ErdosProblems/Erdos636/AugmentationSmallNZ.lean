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

import ErdosProblems.Erdos636.AugmentationGraphFull
import ErdosProblems.Erdos636.AugmentationGraphFullIdentity
import ErdosProblems.Erdos636.AugmentationGraphFullState

/-!
# The bounded-`nZ` augmentation branch

When the number `nZ` of matching cells in the augmentation is bounded, no
switching path is needed.  Fix `nZ - 1` cells, expose one further cell, and
apply the balanced-slice point-mass estimate to the resulting one-state
collision graph.  Markov's inequality controls both collision edges and
degree-window exceptions; Turan thinning then leaves many distinct induced
edge counts in one common window.

The first theorem below is the exact finite one-state endpoint.  It is useful
independently of the asymptotic choice of constants: unlike the long-path
endpoint it works also for `nZ = 1`, where the fixed state is empty.
-/

open Classical SimpleGraph
open scoped BigOperators

namespace Erdos636
namespace AugmentationSmallNZ

open Erdos88.Concentration
open Erdos88.Fourier

universe u

noncomputable section

variable {V : Type u} [Fintype V] [DecidableEq V]

/-- The literal value obtained from one fixed state and one candidate cell. -/
def oneStateValue (G : SimpleGraph V) (W U0 D : Finset V)
    (state : Finset (Finset V)) (x : Finset V) : Nat :=
  Erdos88.inducedEdges G
    (AugmentationGraphFull.exposedBase W U0 D (fun _ : Unit => state) () ∪ x)

/-- The increasing-pair representation of collisions between one-state
augmentation values. -/
def oneStateCollisionEdges (G : SimpleGraph V) (W U0 D : Finset V)
    (state C : Finset (Finset V)) :
    Finset (Finset V × Finset V) := by
  letI : LinearOrder (Finset V) := AugmentationGraphPartial.cellLinearOrder
  exact CollisionCounting.collisionEdges C
    (fun x (_ : Unit) => oneStateValue G W U0 D state x) ()

/-- The inner half-slice deviation of one candidate's deletion degree. -/
def innerDegreeBad (G : SimpleGraph V) (D1 : Finset V) (nD : Nat)
    (deviation : Real) (x : Finset V) (omega : BoolSlice D1 nD) : Prop :=
  deviation ≤
    |(degreeInto G (AugmentationGraphPartial.sampleFinset D1 nD omega) x : Real) -
      (nD : Real) / D1.card * degreeInto G D1 x|

/-- The explicit bounded-difference failure bound on an inner `nD`-slice. -/
def innerLinearFailure (nD K : Nat) (deviation : Real) : Real :=
  2 * Real.exp (-deviation ^ 2 / (2 * nD * (4 * K) ^ 2))

/-- One candidate's inner deletion degree has the claimed common explicit
bounded-difference tail.  This is the degree-risk input used by the
one-state endpoint; it is proved here rather than retained as a probability
hypothesis. -/
theorem uniformProbability_innerDegreeBad_le
    (G : SimpleGraph V) (D1 x : Finset V) (nD K : Nat)
    (deviation : Real)
    (hnD : 0 < nD) (hhalf : D1.card = 2 * nD)
    (hK : 1 ≤ K) (hxK : x.card ≤ K) (hdev : 0 ≤ deviation) :
    uniformProbability (innerDegreeBad G D1 nD deviation x) ≤
      innerLinearFailure nD K deviation := by
  classical
  have hfeasible : nD ≤ Fintype.card D1 := by simp [hhalf]; omega
  letI : Nonempty D1 := by
    have : 0 < D1.card := by omega
    obtain ⟨v, hv⟩ := Finset.card_pos.mp this
    exact ⟨⟨v, hv⟩⟩
  letI : Nonempty
      (Erdos88.BooleanSlices.BooleanSlicePoint D1 nD) :=
    SliceMoments.nonempty_booleanSlicePoint D1 nD (by simpa using hfeasible)
  let E := AugmentationGraphPartial.boolSliceEquivBooleanSlicePoint D1 nD
  letI : Nonempty (BoolSlice D1 nD) := E.nonempty_congr.mpr inferInstance
  let q : D1 -> Real := fun u => incidence G x u.1
  have hqbound : ∀ u, |q u| ≤ (K : Real) := by
    intro u
    change |(incidence G x u.1 : Real)| ≤ (K : Real)
    rw [abs_of_nonneg (by positivity)]
    exact_mod_cast (incidence_le_card G x u.1).trans hxK
  have htail := AugmentationGraphPartial.boolSlice_sum_two_sided_probability
    (I := D1) nD (by simpa using hfeasible) hnD q K deviation
      (by exact_mod_cast hK) hdev hqbound
  have hmean : uniformExpectation (AugmentationGraphPartial.sliceSum nD q) =
        (nD : Real) / D1.card * degreeInto G D1 x := by
    rw [AugmentationGraphPartial.uniformExpectation_sliceSum nD
      (by simpa using hfeasible) q]
    have hsum : ∑ u, q u = degreeInto G D1 x := by
      have hz := AugmentationGraphPartial.sum_incidenceVector_eq_degreeInto
        G D1 x
      simpa [q, AugmentationGraphPartial.incidenceVector] using
        congrArg (fun z : Int => (z : Real)) hz
    rw [hsum]
    simp
  have hsample (omega : BoolSlice D1 nD) :
      AugmentationGraphPartial.sliceSum nD q omega =
        degreeInto G
          (AugmentationGraphPartial.sampleFinset D1 nD omega) x := by
    simpa [q, AugmentationGraphPartial.incidenceVector] using
      AugmentationGraphPartial.sliceSum_incidenceVector_eq_degreeInto_sampleFinset
        G D1 x nD omega
  rw [hmean] at htail
  simp_rw [hsample] at htail
  change uniformProbability (fun omega : BoolSlice D1 nD =>
      deviation ≤
        |(degreeInto G
            (AugmentationGraphPartial.sampleFinset D1 nD omega) x : Real) -
          (nD : Real) / D1.card * degreeInto G D1 x|) ≤ _
  exact htail

/-- Regard a Fourier Boolean-slice point as the corresponding finset
half-sample. -/
def boolSliceAsHalf (D1 : Finset V) (nD : Nat) (omega : BoolSlice D1 nD) :
    HalfSample.Slice D1 nD :=
  ⟨SlicePersistence.sampleFinset nD omega,
    SlicePersistence.card_sampleFinset nD omega⟩

@[simp] lemma halfDeletion_boolSliceAsHalf
    (D1 : Finset V) (nD : Nat) (omega : BoolSlice D1 nD) :
    AugmentationGraphFullIdentity.halfDeletion D1 nD
        (boolSliceAsHalf D1 nD omega) =
      AugmentationGraphPartial.sampleFinset D1 nD omega :=
  rfl

/-- The fixed-state vertex union is disjoint from every matching cell not
used by that state. -/
lemma cellUnion_disjoint_cell_of_mem_not_mem
    {scale nW ell K : Nat} {alpha aDisc aDiv b : Real}
    {G : SimpleGraph V}
    (S : StructuralWitness G scale nW ell K alpha aDisc aDiv b)
    (state : Finset (Finset V)) (hstate : state ⊆ S.matching)
    (x : Finset V) (hx : x ∈ S.matching) (hxstate : x ∉ state) :
    Disjoint (AugmentationGraphFull.cellUnion state) x := by
  rw [Finset.disjoint_left]
  intro v hvstate hvx
  obtain ⟨z, hzstate, hvz⟩ := Finset.mem_biUnion.mp hvstate
  have hzx : z ≠ x := by
    intro h
    subst z
    exact hxstate hzstate
  exact Finset.disjoint_left.mp
    (S.matching_pairwiseDisjoint (hstate hzstate) hx hzx) hvz hvx

/-- A fixed state's union avoids either structural base and the reservoir. -/
lemma cellUnion_disjoint_structuralBase_union_U0
    {scale nW ell K : Nat} {alpha aDisc aDiv b : Real}
    {G : SimpleGraph V}
    (S : StructuralWitness G scale nW ell K alpha aDisc aDiv b)
    (branch : Bool) (state : Finset (Finset V))
    (hstate : state ⊆ S.matching) :
    Disjoint (AugmentationGraphFull.cellUnion state)
      (Augmentation.structuralBase S branch ∪ S.U0) := by
  rw [Finset.disjoint_left]
  intro v hvstate hvbase
  obtain ⟨z, hzstate, hvz⟩ := Finset.mem_biUnion.mp hvstate
  exact Finset.disjoint_left.mp
    (Augmentation.structural_matching_away_base_union_U0
      S branch z (hstate hzstate)) hvz hvbase

/-- The common structural-base degree of every matching cell. -/
def structuralBaseDegree
    {scale nW ell K : Nat} {alpha aDisc aDiv b : Real}
    {G : SimpleGraph V}
    (S : StructuralWitness G scale nW ell K alpha aDisc aDiv b)
    (branch : Bool) : Nat :=
  if branch then S.dPlus else S.dMinus

lemma degreeInto_structuralBase
    {scale nW ell K : Nat} {alpha aDisc aDiv b : Real}
    {G : SimpleGraph V}
    (S : StructuralWitness G scale nW ell K alpha aDisc aDiv b)
    (branch : Bool) (x : Finset V) (hx : x ∈ S.matching) :
    degreeInto G (Augmentation.structuralBase S branch) x =
      structuralBaseDegree S branch := by
  cases branch <;> simp [Augmentation.structuralBase, structuralBaseDegree,
    S.degree_Wminus x hx, S.degree_Wplus x hx]

/-- The D-dependent common centre for a bounded-state augmentation. -/
def smallNZCenter
    {scale nW ell K : Nat} {alpha aDisc aDiv b : Real}
    {G : SimpleGraph V}
    (S : StructuralWitness G scale nW ell K alpha aDisc aDiv b)
    (branch : Bool) (D1 : Finset V) (nD : Nat)
    (state : Finset (Finset V)) (outerCenter : Real)
    (D : Finset V) : Real :=
  (Erdos88.inducedEdges G
      (AugmentationGraphFull.exposedBase
        (Augmentation.structuralBase S branch) S.U0 D
        (fun _ : Unit => state) ()) : Real) +
    structuralBaseDegree S branch + S.d0 -
      (nD : Real) / D1.card * outerCenter

/-- The exact window around `smallNZCenter`. -/
def smallNZRadius (K nZ nD : Nat) (D1 : Finset V)
    (innerDeviation outerRadius : Real) : Real :=
  K ^ 2 * nZ + innerDeviation +
    (nD : Real) / D1.card * outerRadius

/-- Every inner-degree-good candidate lies in the common bounded-`nZ`
window.  All disjointness and degree identities are discharged from the
structural witness. -/
theorem oneStateValue_mem_smallNZWindow
    {scale nW ell K : Nat} {alpha aDisc aDiv b : Real}
    {G : SimpleGraph V}
    (S : StructuralWitness G scale nW ell K alpha aDisc aDiv b)
    (branch : Bool) (D1 : Finset V) (nD nZ : Nat)
    (state : Finset (Finset V)) (x : Finset V)
    (outerCenter outerRadius innerDeviation : Real)
    (hnZ : 1 ≤ nZ) (hhalf : D1.card = 2 * nD) (hD1 : D1 ⊆ S.U0)
    (hstate : state ⊆ S.matching) (hstateCard : state.card = nZ - 1)
    (hx : x ∈ S.matching) (hxstate : x ∉ state)
    (hxOuter : AugmentationGraphPartial.DegreeGood
      G D1 x outerCenter outerRadius)
    (omega : BoolSlice D1 nD)
    (hxInner : ¬ innerDegreeBad G D1 nD innerDeviation x omega) :
    |(oneStateValue G (Augmentation.structuralBase S branch) S.U0
          (AugmentationGraphPartial.sampleFinset D1 nD omega) state x : Real) -
        smallNZCenter S branch D1 nD state outerCenter
          (AugmentationGraphPartial.sampleFinset D1 nD omega)| ≤
      smallNZRadius K nZ nD D1 innerDeviation outerRadius := by
  classical
  let D := AugmentationGraphPartial.sampleFinset D1 nD omega
  let Z := AugmentationGraphFull.cellUnion state
  have hDU : D ⊆ S.U0 :=
    (AugmentationGraphPartial.sampleFinset_subset D1 nD omega).trans hD1
  have hstateBase := cellUnion_disjoint_structuralBase_union_U0
    S branch state hstate
  have hWZ : Disjoint (Augmentation.structuralBase S branch) Z :=
    (hstateBase.mono_right Finset.subset_union_left).symm
  have hUZ : Disjoint S.U0 Z :=
    (hstateBase.mono_right Finset.subset_union_right).symm
  have hZx : Disjoint Z x :=
    cellUnion_disjoint_cell_of_mem_not_mem S state hstate x hx hxstate
  have hWx : Disjoint (Augmentation.structuralBase S branch) x :=
    ((Augmentation.structural_matching_away_base_union_U0 S branch x hx).mono_right
      Finset.subset_union_left).symm
  have hUx : Disjoint S.U0 x :=
    ((Augmentation.structural_matching_away_base_union_U0 S branch x hx).mono_right
      Finset.subset_union_right).symm
  have hpair : (state : Set (Finset V)).PairwiseDisjoint id := by
    intro a ha b hb hab
    exact S.matching_pairwiseDisjoint (hstate ha) (hstate hb) hab
  have hZcardEq : Z.card = state.card * S.k := by
    exact card_matching_biUnion_eq_mul hpair (fun z hz =>
      S.matching_uniform z (hstate hz))
  have hZcard : Z.card ≤ K * (nZ - 1) := by
    rw [hZcardEq, hstateCard]
    nlinarith [S.k_le]
  have hxK : x.card ≤ K := (S.matching_uniform x hx).le.trans S.k_le
  have hcellBound : Erdos88.inducedEdges G x + (G.interedges Z x).card ≤
      K ^ 2 * nZ :=
    matchingCellIncrement_le G hnZ hZcard hxK
  have hbaseDegree : (G.interedges
      (Augmentation.structuralBase S branch) x).card =
      structuralBaseDegree S branch := by
    rw [AugmentationGraphFullIdentity.card_interedges_eq_degreeInto]
    exact degreeInto_structuralBase S branch x hx
  have hUdegree : degreeInto G S.U0 x = S.d0 := S.degree_U0 x hx
  have hid := AugmentationGraphFullIdentity.literalCandidateExtension_sub_base_int
    G (Augmentation.structuralBase S branch) S.U0 D Z x hDU
      (Augmentation.structuralBase_disjoint_U0 S branch)
      hWZ hUZ hWx hUx hZx
  simp only [AugmentationGraphFullIdentity.candidateOffsetInt] at hid
  rw [hbaseDegree, hUdegree] at hid
  have hidReal :
      (oneStateValue G (Augmentation.structuralBase S branch) S.U0 D state x : Real) -
          Erdos88.inducedEdges G
            (AugmentationGraphFull.exposedBase
              (Augmentation.structuralBase S branch) S.U0 D
              (fun _ : Unit => state) ()) =
        (Erdos88.inducedEdges G x : Real) +
          (G.interedges Z x).card + structuralBaseDegree S branch + S.d0 -
            degreeInto G D x := by
    have hid' := congrArg (fun z : Int => (z : Real)) hid
    push_cast at hid'
    simp only [oneStateValue, AugmentationGraphFull.exposedBase,
      AugmentationGraphFullIdentity.literalState,
      AugmentationGraphFullIdentity.deletionBase,
      AugmentationGraphFullIdentity.literalPathNat,
      Z] at hid'
    simp only [oneStateValue, AugmentationGraphFull.exposedBase,
      AugmentationGraphFullIdentity.literalState,
      AugmentationGraphFullIdentity.deletionBase,
      AugmentationGraphFullIdentity.literalPathNat,
      Z]
    linarith
  let r : Real := (nD : Real) / D1.card
  have hr : 0 ≤ r := by positivity
  have hinner : |(degreeInto G D x : Real) - r * degreeInto G D1 x| ≤
      innerDeviation := by
    have hlt := lt_of_not_ge hxInner
    exact hlt.le
  have houter : |r * (degreeInto G D1 x : Real) - r * outerCenter| ≤
      r * outerRadius := by
    rw [← mul_sub, abs_mul, abs_of_nonneg hr]
    exact mul_le_mul_of_nonneg_left hxOuter hr
  have herror : |r * outerCenter - (degreeInto G D x : Real)| ≤
      innerDeviation + r * outerRadius := by
    calc
      |r * outerCenter - (degreeInto G D x : Real)| =
          |(r * outerCenter - r * degreeInto G D1 x) +
            (r * degreeInto G D1 x - degreeInto G D x)| := by ring_nf
      _ ≤ |r * outerCenter - r * degreeInto G D1 x| +
          |r * degreeInto G D1 x - degreeInto G D x| := abs_add_le _ _
      _ = |r * degreeInto G D1 x - r * outerCenter| +
          |(degreeInto G D x : Real) - r * degreeInto G D1 x| := by
            congr 1
            · exact abs_sub_comm _ _
            · exact abs_sub_comm _ _
      _ ≤ r * outerRadius + innerDeviation := add_le_add houter hinner
      _ = innerDeviation + r * outerRadius := by ring
  have hmain :
      |(oneStateValue G (Augmentation.structuralBase S branch) S.U0 D state x : Real) -
          smallNZCenter S branch D1 nD state outerCenter D| ≤
        (K ^ 2 * nZ : Nat) + innerDeviation + r * outerRadius := by
    rw [smallNZCenter]
    have heq :
        (oneStateValue G (Augmentation.structuralBase S branch) S.U0 D state x : Real) -
            ((Erdos88.inducedEdges G
              (AugmentationGraphFull.exposedBase
                (Augmentation.structuralBase S branch) S.U0 D
                (fun _ : Unit => state) ()) : Real) +
              structuralBaseDegree S branch + S.d0 - r * outerCenter) =
          ((Erdos88.inducedEdges G x : Real) + (G.interedges Z x).card) +
            (r * outerCenter - degreeInto G D x) := by
      linarith [hidReal]
    rw [show (nD : Real) / D1.card = r by rfl, heq]
    calc
      |((Erdos88.inducedEdges G x : Real) + (G.interedges Z x).card) +
          (r * outerCenter - degreeInto G D x)| ≤
          |((Erdos88.inducedEdges G x : Real) + (G.interedges Z x).card)| +
            |r * outerCenter - degreeInto G D x| := abs_add_le _ _
      _ = ((Erdos88.inducedEdges G x : Real) + (G.interedges Z x).card) +
            |r * outerCenter - degreeInto G D x| := by
              rw [abs_of_nonneg (by positivity)]
      _ ≤ (K ^ 2 * nZ : Nat) + (innerDeviation + r * outerRadius) := by
            gcongr
            exact_mod_cast hcellBound
      _ = (K ^ 2 * nZ : Nat) + innerDeviation + r * outerRadius := by ring
  simpa [D, smallNZRadius, r] using hmain

/-- The graph-specific one-state collision probability.  `PartialGood`
supplies `hdiverse`, `hxOuter`, and `hyOuter`; this theorem turns them into
the actual collision estimate for induced edge counts, including all fixed
state offsets. -/
theorem uniformProbability_oneStateValue_collision_le
    {scale nW ell K : Nat} {alpha aDisc aDiv b : Real}
    {G : SimpleGraph V}
    (S : StructuralWitness G scale nW ell K alpha aDisc aDiv b)
    (branch : Bool) (D1 : Finset V) (nD : Nat)
    (state : Finset (Finset V)) (x y : Finset V)
    (c theta outerCenter outerRadius : Real)
    (hnD : 0 < nD) (hhalf : D1.card = 2 * nD) (hD1 : D1 ⊆ S.U0)
    (hstate : state ⊆ S.matching)
    (hx : x ∈ S.matching) (hy : y ∈ S.matching)
    (hxstate : x ∉ state) (hystate : y ∉ state)
    (hxy : x ≠ y)
    (hxOuter : AugmentationGraphPartial.DegreeGood
      G D1 x outerCenter outerRadius)
    (hyOuter : AugmentationGraphPartial.DegreeGood
      G D1 y outerCenter outerRadius)
    (hdiverse : theta * D1.card ≤ incidenceDiffMass G D1 x y)
    (hc0 : 0 < c) (hc1 : c ≤ 1 / 2) (htheta : 0 < theta)
    (hK : 1 ≤ K)
    (hsmall : 2 * outerRadius < theta / 2 * D1.card)
    (hselected : c * D1.card ≤ (nD : Real))
    (hunselected : c * D1.card ≤ ((D1.card - nD : Nat) : Real)) :
    uniformProbability (fun omega : BoolSlice D1 nD =>
      oneStateValue G (Augmentation.structuralBase S branch) S.U0
          (AugmentationGraphPartial.sampleFinset D1 nD omega) state x =
        oneStateValue G (Augmentation.structuralBase S branch) S.U0
          (AugmentationGraphPartial.sampleFinset D1 nD omega) state y) ≤
      AntiConcentration.variancePointMassConstant
          c (theta ^ 2 / 4) K / Real.sqrt (D1.card : Real) := by
  classical
  have hD1pos : 0 < Fintype.card D1 := by
    simp only [Fintype.card_coe, hhalf]
    omega
  letI : Nonempty
      (Erdos88.BooleanSlices.BooleanSlicePoint D1 nD) :=
    SliceMoments.nonempty_booleanSlicePoint D1 nD (by omega)
  let E := AugmentationGraphPartial.boolSliceEquivBooleanSlicePoint D1 nD
  letI : Nonempty (BoolSlice D1 nD) := E.nonempty_congr.mpr inferInstance
  let a : D1 -> Int := fun u =>
    AugmentationGraphFullIdentity.reservoirIncidence G D1 y u -
      AugmentationGraphFullIdentity.reservoirIncidence G D1 x u
  let mu : Real := (∑ u, (a u : Real)) / Fintype.card D1
  have hbounded : ∀ u, |a u| ≤ (K : Int) := by
    intro u
    exact AugmentationGraphFullIdentity.abs_reservoirIncidence_sub_le_of_card_le
      G D1 x y K (S.matching_uniform x hx |>.le.trans S.k_le)
        (S.matching_uniform y hy |>.le.trans S.k_le) u
  have hmean : (Fintype.card D1 : Real) * mu = ∑ u, (a u : Real) := by
    dsimp only [mu]
    field_simp [ne_of_gt (by exact_mod_cast hD1pos)]
  have hlone : theta * Fintype.card D1 ≤ ∑ u, |(a u : Real)| := by
    rw [show (∑ u, |(a u : Real)|) = incidenceDiffMass G D1 x y by
      simpa [a, AugmentationGraphFullIdentity.replacementCoeff] using
        AugmentationGraphFullIdentity.sum_abs_replacementCoeff_eq_incidenceDiffMass
          G D1 x y]
    simpa using hdiverse
  have hsigned : ∑ u, (a u : Real) =
      (degreeInto G D1 y : Real) - degreeInto G D1 x := by
    simpa [a, AugmentationGraphFullIdentity.replacementCoeff] using
      AugmentationGraphFullIdentity.sum_replacementCoeff_eq_degreeInto_sub
        G D1 x y
  have hsignedSmall : |∑ u, (a u : Real)| <
      theta / 2 * Fintype.card D1 := by
    rw [hsigned]
    have htri : |(degreeInto G D1 y : Real) - degreeInto G D1 x| ≤
        |(degreeInto G D1 y : Real) - outerCenter| +
          |(degreeInto G D1 x : Real) - outerCenter| := by
      calc
        |(degreeInto G D1 y : Real) - degreeInto G D1 x| =
            |((degreeInto G D1 y : Real) - outerCenter) -
              ((degreeInto G D1 x : Real) - outerCenter)| := by ring_nf
        _ ≤ _ := abs_sub _ _
    have htwo : |(degreeInto G D1 y : Real) - outerCenter| +
        |(degreeInto G D1 x : Real) - outerCenter| ≤ 2 * outerRadius := by
      dsimp only [AugmentationGraphPartial.DegreeGood] at hxOuter hyOuter
      linarith
    exact (htri.trans htwo).trans_lt (by simpa using hsmall)
  let target : Real :=
    (AugmentationGraphFullIdentity.candidateOffsetInt G
        (Augmentation.structuralBase S branch) S.U0
        (AugmentationGraphFull.cellUnion state) y -
      AugmentationGraphFullIdentity.candidateOffsetInt G
        (Augmentation.structuralBase S branch) S.U0
        (AugmentationGraphFull.cellUnion state) x : Int)
  have hanti :=
    AntiConcentration.slice_point_probability_le_of_integer_l1_small_sum
      a mu c theta K nD hc0 hc1 htheta hK hD1pos hbounded hmean hlone
        hsignedSmall (by simpa using hselected)
        (by
          rw [Fintype.card_coe,
            ← Nat.cast_sub (R := Real) (show nD ≤ D1.card by omega)]
          exact hunselected) target
  have hstateBase := cellUnion_disjoint_structuralBase_union_U0
    S branch state hstate
  have hWZ : Disjoint (Augmentation.structuralBase S branch)
      (AugmentationGraphFull.cellUnion state) :=
    (hstateBase.mono_right Finset.subset_union_left).symm
  have hUZ : Disjoint S.U0 (AugmentationGraphFull.cellUnion state) :=
    (hstateBase.mono_right Finset.subset_union_right).symm
  have hZx := cellUnion_disjoint_cell_of_mem_not_mem S state hstate x hx hxstate
  have hZy := cellUnion_disjoint_cell_of_mem_not_mem S state hstate y hy hystate
  have hxAway := Augmentation.structural_matching_away_base_union_U0
    S branch x hx
  have hyAway := Augmentation.structural_matching_away_base_union_U0
    S branch y hy
  have hWx : Disjoint (Augmentation.structuralBase S branch) x :=
    (hxAway.mono_right Finset.subset_union_left).symm
  have hUx : Disjoint S.U0 x :=
    (hxAway.mono_right Finset.subset_union_right).symm
  have hWy : Disjoint (Augmentation.structuralBase S branch) y :=
    (hyAway.mono_right Finset.subset_union_left).symm
  have hUy : Disjoint S.U0 y :=
    (hyAway.mono_right Finset.subset_union_right).symm
  have hstat (omega : BoolSlice D1 nD) :
      AntiConcentration.sliceLinear nD (fun u => (a u : Real)) omega =
        HalfSample.sliceSum
          (AugmentationGraphFullIdentity.replacementCoeff G D1 x y)
          (boolSliceAsHalf D1 nD omega) := by
    change AugmentationPartial.incidenceSum nD a omega = _
    rw [AugmentationGraphPartial.incidenceSum_eq_sliceSum]
    rfl
  have hmono : uniformProbability (fun omega : BoolSlice D1 nD =>
      oneStateValue G (Augmentation.structuralBase S branch) S.U0
          (AugmentationGraphPartial.sampleFinset D1 nD omega) state x =
        oneStateValue G (Augmentation.structuralBase S branch) S.U0
          (AugmentationGraphPartial.sampleFinset D1 nD omega) state y) ≤
      uniformProbability (fun omega : BoolSlice D1 nD =>
        AntiConcentration.sliceLinear nD (fun u => (a u : Real)) omega =
          target) := by
    apply uniformProbability_mono
    intro omega hcollisionValue
    have hiff := AugmentationGraphFullIdentity.literalCandidateCollision_iff
      G (Augmentation.structuralBase S branch) S.U0 D1
        (AugmentationGraphFull.cellUnion state) x y nD
        (boolSliceAsHalf D1 nD omega) hD1
        (Augmentation.structuralBase_disjoint_U0 S branch)
        hWZ hUZ
        hWx hUx
        hZx
        hWy hUy
        hZy
    rw [halfDeletion_boolSliceAsHalf] at hiff
    have heq : HalfSample.sliceSum
        (AugmentationGraphFullIdentity.replacementCoeff G D1 x y)
        (boolSliceAsHalf D1 nD omega) = target := by
      apply hiff.mp
      simpa [oneStateValue, AugmentationGraphFull.exposedBase,
        AugmentationGraphFullIdentity.literalState,
        AugmentationGraphFullIdentity.deletionBase] using hcollisionValue
    rw [hstat omega]
    exact heq
  exact hmono.trans (by
    change Erdos88.Fourier.finProbability (BoolSlice D1 nD)
        (fun omega => AntiConcentration.sliceLinear nD
          (fun u => (a u : Real)) omega = target) ≤ _
    simpa only [Fintype.card_coe] using hanti)

/-- The generic finite one-state probability/Turan endpoint.

All probabilistic assumptions are per-pair or per-candidate estimates.  The
displayed risk inequality is the complete union-bound calculation, and the
last multiplication inequality is the complete Turan calculation.  Thus the
conclusion has no assumed success-probability statement. -/
theorem one_third_le_layerProbability_innerWindowGood_oneState
    (G : SimpleGraph V) (W U0 D1 : Finset V)
    (M C state : Finset (Finset V)) (nD nS : Nat)
    (L radius pCollision pDegree E tDegree : Real)
    (center : Finset V -> Real)
    (edgeBudget badDegree piece : Nat)
    (hhalf : D1.card = 2 * nD)
    (hCM : C ⊆ M)
    (hstateM : state ⊆ M)
    (hstateCard : state.card = nS)
    (haway : ∀ x ∈ C, x ∉ state)
    (hcollision : ∀ x ∈ C, ∀ y ∈ C, x ≠ y ->
      uniformProbability (fun omega : BoolSlice D1 nD =>
        oneStateValue G W U0
          (AugmentationGraphPartial.sampleFinset D1 nD omega) state x =
        oneStateValue G W U0
          (AugmentationGraphPartial.sampleFinset D1 nD omega) state y) ≤
        pCollision)
    (degreeBad : Finset V -> BoolSlice D1 nD -> Prop)
    (hdegree : ∀ x ∈ C,
      uniformProbability (degreeBad x) ≤ pDegree)
    (hwindow : ∀ omega : BoolSlice D1 nD, ∀ x ∈ C,
      ¬ degreeBad x omega ->
      |(oneStateValue G W U0
          (AugmentationGraphPartial.sampleFinset D1 nD omega) state x : Real) -
          center (AugmentationGraphPartial.sampleFinset D1 nD omega)| ≤ radius)
    (hE : 0 < E) (htDegree : 0 < tDegree)
    (hrisk : C.card.choose 2 * pCollision / E +
        C.card * pDegree / tDegree ≤ 2 / 3)
    (hEbudget : E ≤ (edgeBudget : Real) + 1)
    (htDegreeBudget : tDegree ≤ (badDegree : Real) + 1)
    (hbadDegree : badDegree < C.card)
    (hpiece : piece * (C.card + 2 * edgeBudget) ≤
      (C.card - badDegree) ^ 2)
    (hpiecePos : 0 < piece)
    (hL : L ≤ piece) :
    (1 / 3 : Real) ≤ NestedUniform.layerProbability D1 nD
      (fun D => AugmentationGraphFull.innerWindowGood
        G W U0 M (nS + 1) L (center D) radius D) := by
  classical
  letI : LinearOrder (Finset V) := AugmentationGraphPartial.cellLinearOrder
  have hnD : nD ≤ D1.card := by omega
  letI : Nonempty
      (Erdos88.BooleanSlices.BooleanSlicePoint D1 nD) :=
    SliceMoments.nonempty_booleanSlicePoint D1 nD hnD
  let BS := AugmentationGraphPartial.boolSliceEquivBooleanSlicePoint D1 nD
  letI : Nonempty (BoolSlice D1 nD) := BS.nonempty_congr.mpr inferInstance
  let value : Finset V -> BoolSlice D1 nD -> Nat := fun x omega =>
    oneStateValue G W U0
      (AugmentationGraphPartial.sampleFinset D1 nD omega) state x
  let collisionBad : BoolSlice D1 nD -> Prop := fun omega =>
    E ≤ ((CollisionCounting.collisionEdges C value omega).card : Real)
  let degreeCountBad : BoolSlice D1 nD -> Prop := fun omega =>
    tDegree ≤ CollisionCounting.eventCount C degreeBad omega
  have hcollisionProb : uniformProbability collisionBad ≤
      C.card.choose 2 * pCollision / E := by
    exact CollisionCounting.uniformProbability_card_collisionEdges_ge_le
      C value pCollision E hE (by
        intro x hx y hy hxy
        simpa only [value] using hcollision x hx y hy hxy)
  have hdegreeProb : uniformProbability degreeCountBad ≤
      C.card * pDegree / tDegree := by
    exact CollisionCounting.uniformProbability_eventCount_ge_le
      C degreeBad pDegree tDegree htDegree hdegree
  have hfalse : uniformProbability (fun _ : BoolSlice D1 nD => False) ≤ 0 := by
    simp [uniformProbability]
  have hgoodRaw := AugmentationPartial.one_sub_four_failure_bounds_le_probability_good
    collisionBad degreeCountBad
      (fun _ : BoolSlice D1 nD => False)
      (fun _ : BoolSlice D1 nD => False)
      (C.card.choose 2 * pCollision / E)
      (C.card * pDegree / tDegree) 0 0
      hcollisionProb hdegreeProb hfalse hfalse
  have hgood : (1 / 3 : Real) ≤ uniformProbability (fun omega : BoolSlice D1 nD =>
      ¬ collisionBad omega ∧ ¬ degreeCountBad omega) := by
    have hmono : uniformProbability (fun omega : BoolSlice D1 nD =>
        ¬ collisionBad omega ∧ ¬ degreeCountBad omega ∧
          ¬ False ∧ ¬ False) ≤
        uniformProbability (fun omega : BoolSlice D1 nD =>
          ¬ collisionBad omega ∧ ¬ degreeCountBad omega) := by
      apply uniformProbability_mono
      aesop
    calc
      (1 / 3 : Real) ≤
          1 - (C.card.choose 2 * pCollision / E +
            C.card * pDegree / tDegree + 0 + 0) := by linarith
      _ ≤ uniformProbability (fun omega : BoolSlice D1 nD =>
          ¬ collisionBad omega ∧ ¬ degreeCountBad omega ∧
            ¬ False ∧ ¬ False) := hgoodRaw
      _ ≤ uniformProbability (fun omega : BoolSlice D1 nD =>
          ¬ collisionBad omega ∧ ¬ degreeCountBad omega) := hmono
  have hpoint : ∀ omega : BoolSlice D1 nD,
      ¬ collisionBad omega ∧ ¬ degreeCountBad omega ->
      AugmentationGraphFull.innerWindowGood G W U0 M (nS + 1) L
        (center (AugmentationGraphPartial.sampleFinset D1 nD omega)) radius
        (AugmentationGraphPartial.sampleFinset D1 nD omega) := by
    intro omega hgoodOmega
    let D := AugmentationGraphPartial.sampleFinset D1 nD omega
    let Cgood : Finset (Finset V) := C.filter fun x => ¬ degreeBad x omega
    have hcollisionNat :
        (CollisionCounting.collisionEdges C value omega).card ≤ edgeBudget := by
      have hlt : ((CollisionCounting.collisionEdges C value omega).card : Real) <
          E := lt_of_not_ge hgoodOmega.1
      have hlt' : ((CollisionCounting.collisionEdges C value omega).card : Real) <
          (edgeBudget : Real) + 1 := hlt.trans_le hEbudget
      have hltNat : (CollisionCounting.collisionEdges C value omega).card <
          edgeBudget + 1 := by exact_mod_cast hlt'
      omega
    have hdegreeNat : (C.filter fun x => degreeBad x omega).card ≤
        badDegree := by
      have hlt : ((CollisionCounting.eventCount C degreeBad omega : Nat) : Real) <
          tDegree := lt_of_not_ge hgoodOmega.2
      have hlt' : ((CollisionCounting.eventCount C degreeBad omega : Nat) : Real) <
          (badDegree : Real) + 1 := hlt.trans_le htDegreeBudget
      have hltNat : CollisionCounting.eventCount C degreeBad omega <
          badDegree + 1 := by exact_mod_cast hlt'
      change (C.filter fun x => degreeBad x omega).card ≤ badDegree
      change (C.filter fun x => degreeBad x omega).card < badDegree + 1 at hltNat
      omega
    have hCgoodCard : C.card - badDegree ≤ Cgood.card := by
      have hpartition := Finset.card_filter_add_card_filter_not
        (s := C) (p := fun x => degreeBad x omega)
      change (C.filter fun x => degreeBad x omega).card + Cgood.card = C.card
        at hpartition
      omega
    have hcollisionGood :
        (CollisionCounting.collisionEdges Cgood value omega).card ≤ edgeBudget :=
      (Finset.card_le_card (AugmentationGraphFullState.collisionEdges_mono
        (Finset.filter_subset _ _) value omega)).trans hcollisionNat
    have hgraphEdges :
        (AugmentationFull.valueCollisionGraph Cgood
          (fun x => value x omega)).edgeFinset.card ≤ edgeBudget :=
      (AugmentationGraphFullState.valueCollisionGraph_edgeFinset_card_le_collisionEdges
        Cgood (fun x => value x omega)).trans hcollisionGood
    obtain ⟨Y, hYC, hYinj, hYbound⟩ :=
      AugmentationFull.exists_injective_subfamily_card_sq_le_of_edges_le
        Cgood (fun x => value x omega) edgeBudget hgraphEdges
    have hdenPos : 0 < Cgood.card + 2 * edgeBudget := by
      have hCgoodPos : 0 < Cgood.card := by
        have : 0 < C.card - badDegree := Nat.sub_pos_of_lt hbadDegree
        omega
      omega
    have hpieceY : piece ≤ Y.card := by
      by_contra hnot
      have hltmul : Y.card * (Cgood.card + 2 * edgeBudget) <
          piece * (Cgood.card + 2 * edgeBudget) :=
        Nat.mul_lt_mul_of_pos_right (Nat.lt_of_not_ge hnot) hdenPos
      have hpieceDen : piece * (Cgood.card + 2 * edgeBudget) ≤
          Cgood.card ^ 2 := by
        calc
          piece * (Cgood.card + 2 * edgeBudget) ≤
              piece * (C.card + 2 * edgeBudget) := by
                exact Nat.mul_le_mul_left piece (Nat.add_le_add_right
                  (Finset.card_le_card (Finset.filter_subset _ _)) _)
          _ ≤ (C.card - badDegree) ^ 2 := hpiece
          _ ≤ Cgood.card ^ 2 := Nat.pow_le_pow_left hCgoodCard 2
      omega
    let values : Finset Nat := Augmentation.edgeValues G
      (AugmentationGraphFull.exposedBase W U0 D (fun _ : Unit => state) ()) Y
    have hvaluesCard : values.card = Y.card := by
      apply Augmentation.card_edgeValues_eq
      intro x hx y hy hxy
      exact hYinj hx hy (by
        simpa only [value, oneStateValue, D,
          AugmentationGraphFull.exposedValue] using hxy)
    refine ⟨values, ?_, ?_, ?_⟩
    · intro e he
      obtain ⟨x, hxY, rfl⟩ := Augmentation.mem_edgeValues.mp he
      have hxC : x ∈ C := (Finset.filter_subset _ _) (hYC hxY)
      apply AugmentationGraphFull.exposedValue_mem_augmentationEdgeValues
        G W U0 D M nS (fun _ : Unit => state) () x
      · exact hstateM
      · exact hstateCard
      · exact hCM hxC
      · exact haway x hxC
    · rw [hvaluesCard]
      exact_mod_cast hL.trans (by exact_mod_cast hpieceY)
    · intro e he
      obtain ⟨x, hxY, rfl⟩ := Augmentation.mem_edgeValues.mp he
      have hxGood := (Finset.mem_filter.mp (hYC hxY)).2
      simpa only [value, oneStateValue, D,
        AugmentationGraphFull.exposedValue] using
          hwindow omega x ((Finset.filter_subset _ _) (hYC hxY)) hxGood
  have htransport : uniformProbability (fun omega : BoolSlice D1 nD =>
      ¬ collisionBad omega ∧ ¬ degreeCountBad omega) ≤
      uniformProbability (fun omega : BoolSlice D1 nD =>
        AugmentationGraphFull.innerWindowGood G W U0 M (nS + 1) L
          (center (AugmentationGraphPartial.sampleFinset D1 nD omega)) radius
          (AugmentationGraphPartial.sampleFinset D1 nD omega)) := by
    exact uniformProbability_mono hpoint
  have hdecode :=
    AugmentationGraphPartial.uniformProbability_sampleFinset_eq_layerProbability
      D1 nD (fun D => AugmentationGraphFull.innerWindowGood
        G W U0 M (nS + 1) L (center D) radius D)
  exact hgood.trans (htransport.trans_eq hdecode)

/-- **Bounded-`nZ` graph endpoint.**

This is the consumable small-augmentation branch.  A `PartialGood` outer
exposure supplies two disjoint matching families.  We freeze `nZ - 1`
members of the first and use the outer-degree-good members of the second as
candidates.  The two probability inputs of the generic one-state theorem
are then discharged by `uniformProbability_oneStateValue_collision_le` and
`uniformProbability_innerDegreeBad_le`; the remaining hypotheses are only
the displayed finite numerical inequalities.  In particular the statement
includes `nZ = 1`, when the frozen state is empty. -/
theorem one_third_le_layerProbability_innerWindowGood_smallNZ_of_partialGood
    {scale nW ell K : Nat} {alpha aDisc aDiv b : Real}
    {G : SimpleGraph V}
    (S : StructuralWitness G scale nW ell K alpha aDisc aDiv b)
    (branch : Bool) (D1 : Finset V) (nD nZ s0 : Nat)
    (diversityThreshold outerCenter outerRadius tS tX tCollision : Real)
    (c theta innerDeviation E tDegree L : Real)
    (outerBad edgeBudget badDegree piece : Nat)
    (hpartial : AugmentationGraphPartial.PartialGood G S.matching s0
      diversityThreshold outerCenter outerRadius tS tX tCollision D1)
    (hnD : 0 < nD) (hnZ : 1 ≤ nZ) (hhalf : D1.card = 2 * nD)
    (hD1 : D1 ⊆ S.U0) (hstateSize : nZ - 1 ≤ s0)
    (hK : 1 ≤ K)
    (hdiversityScale : theta * D1.card ≤ diversityThreshold)
    (hc0 : 0 < c) (hc1 : c ≤ 1 / 2) (htheta : 0 < theta)
    (hsmall : 2 * outerRadius < theta / 2 * D1.card)
    (hselected : c * D1.card ≤ (nD : Real))
    (hunselected : c * D1.card ≤ ((D1.card - nD : Nat) : Real))
    (hinnerDeviation : 0 ≤ innerDeviation)
    (htXBudget : tX ≤ (outerBad : Real) + 1)
    (hgoodLower : badDegree < s0 - outerBad)
    (hE : 0 < E) (htDegree : 0 < tDegree)
    (hrisk :
      let pCollision := AntiConcentration.variancePointMassConstant
        c (theta ^ 2 / 4) K / Real.sqrt (D1.card : Real)
      let pDegree := innerLinearFailure nD K innerDeviation
      (s0 : Real) ^ 2 * pCollision / E +
          s0 * pDegree / tDegree ≤ 2 / 3)
    (hEbudget : E ≤ (edgeBudget : Real) + 1)
    (htDegreeBudget : tDegree ≤ (badDegree : Real) + 1)
    (hpiece : piece * (s0 + 2 * edgeBudget) ≤
      (s0 - outerBad - badDegree) ^ 2)
    (hpiecePos : 0 < piece) (hL : L ≤ piece) :
    ∃ state : Finset (Finset V),
      state ⊆ S.matching ∧ state.card = nZ - 1 ∧
        (1 / 3 : Real) ≤ NestedUniform.layerProbability D1 nD
          (fun D => AugmentationGraphFull.innerWindowGood G
            (Augmentation.structuralBase S branch) S.U0 S.matching nZ L
            (smallNZCenter S branch D1 nD state outerCenter D)
            (smallNZRadius K nZ nD D1 innerDeviation outerRadius) D) := by
  classical
  let pCollision := AntiConcentration.variancePointMassConstant
    c (theta ^ 2 / 4) K / Real.sqrt (D1.card : Real)
  let pDegree := innerLinearFailure nD K innerDeviation
  obtain ⟨S0, X0, hS0M, hX0M, hS0card, hX0card, hdisjoint,
    hdiverse, _hbadS, hbadX, _hcoll⟩ := hpartial
  have hstateSize' : nZ - 1 ≤ S0.card := by omega
  obtain ⟨state, hstateS0, hstateCard⟩ :=
    Finset.exists_subset_card_eq hstateSize'
  have hstateM : state ⊆ S.matching := hstateS0.trans hS0M
  let C := AugmentationGraphPartial.goodCells
    G D1 outerCenter outerRadius X0
  have hCM : C ⊆ S.matching :=
    (Finset.filter_subset _ _).trans hX0M
  have hCcardUpper : C.card ≤ s0 := by
    rw [← hX0card]
    exact Finset.card_le_card (Finset.filter_subset _ _)
  have hbadOuter :
      (X0.filter fun x => ¬ AugmentationGraphPartial.DegreeGood
        G D1 x outerCenter outerRadius).card ≤ outerBad := by
    have hlt :
        ((X0.filter fun x => ¬ AugmentationGraphPartial.DegreeGood
          G D1 x outerCenter outerRadius).card : Real) <
          (outerBad : Real) + 1 := hbadX.trans_le htXBudget
    have hltNat :
        (X0.filter fun x => ¬ AugmentationGraphPartial.DegreeGood
          G D1 x outerCenter outerRadius).card < outerBad + 1 := by
      exact_mod_cast hlt
    omega
  have hCcardLower : s0 - outerBad ≤ C.card := by
    have hpartition := Finset.card_filter_add_card_filter_not
      (s := X0) (p := fun x => AugmentationGraphPartial.DegreeGood
        G D1 x outerCenter outerRadius)
    change (X0.filter fun x => AugmentationGraphPartial.DegreeGood
        G D1 x outerCenter outerRadius).card +
      (X0.filter fun x => ¬ AugmentationGraphPartial.DegreeGood
        G D1 x outerCenter outerRadius).card = X0.card at hpartition
    change C.card +
      (X0.filter fun x => ¬ AugmentationGraphPartial.DegreeGood
        G D1 x outerCenter outerRadius).card = X0.card at hpartition
    omega
  have haway : ∀ x ∈ C, x ∉ state := by
    intro x hxC hxstate
    have hxX0 : x ∈ X0 := (Finset.filter_subset _ _) hxC
    exact Finset.disjoint_left.mp hdisjoint (hstateS0 hxstate) hxX0
  have hcollision : ∀ x ∈ C, ∀ y ∈ C, x ≠ y ->
      uniformProbability (fun omega : BoolSlice D1 nD =>
        oneStateValue G (Augmentation.structuralBase S branch) S.U0
            (AugmentationGraphPartial.sampleFinset D1 nD omega) state x =
          oneStateValue G (Augmentation.structuralBase S branch) S.U0
            (AugmentationGraphPartial.sampleFinset D1 nD omega) state y) ≤
        pCollision := by
    intro x hxC y hyC hxy
    have hxX0 : x ∈ X0 := (Finset.filter_subset _ _) hxC
    have hyX0 : y ∈ X0 := (Finset.filter_subset _ _) hyC
    apply uniformProbability_oneStateValue_collision_le S branch D1 nD
      state x y c theta outerCenter outerRadius hnD hhalf hD1 hstateM
      (hX0M hxX0) (hX0M hyX0) (haway x hxC) (haway y hyC) hxy
      (Finset.mem_filter.mp hxC).2 (Finset.mem_filter.mp hyC).2
      (hdiversityScale.trans (hdiverse x hxX0 y hyX0 hxy))
      hc0 hc1 htheta hK hsmall hselected hunselected
  have hdegree : ∀ x ∈ C,
      uniformProbability (innerDegreeBad G D1 nD innerDeviation x) ≤
        pDegree := by
    intro x hxC
    exact uniformProbability_innerDegreeBad_le G D1 x nD K innerDeviation
      hnD hhalf hK
      ((S.matching_uniform x (hCM hxC)).le.trans S.k_le)
      hinnerDeviation
  have hwindow : ∀ omega : BoolSlice D1 nD, ∀ x ∈ C,
      ¬ innerDegreeBad G D1 nD innerDeviation x omega ->
      |(oneStateValue G (Augmentation.structuralBase S branch) S.U0
          (AugmentationGraphPartial.sampleFinset D1 nD omega) state x : Real) -
          smallNZCenter S branch D1 nD state outerCenter
            (AugmentationGraphPartial.sampleFinset D1 nD omega)| ≤
        smallNZRadius K nZ nD D1 innerDeviation outerRadius := by
    intro omega x hxC hxGood
    exact oneStateValue_mem_smallNZWindow S branch D1 nD nZ state x
      outerCenter outerRadius innerDeviation hnZ hhalf hD1 hstateM
      hstateCard (hCM hxC) (haway x hxC)
      (Finset.mem_filter.mp hxC).2 omega hxGood
  have hpCollision : 0 ≤ pCollision := by
    dsimp only [pCollision]
    apply div_nonneg
    · exact (AntiConcentration.variancePointMassConstant_pos hc0
        (by positivity) (by omega)).le
    · positivity
  have hpDegree : 0 ≤ pDegree := by
    dsimp only [pDegree, innerLinearFailure]
    positivity
  have hchoose : ((C.card.choose 2 : Nat) : Real) ≤ (s0 : Real) ^ 2 := by
    exact_mod_cast ((Nat.choose_le_pow C.card 2).trans
      (Nat.pow_le_pow_left hCcardUpper 2))
  have hcardReal : (C.card : Real) ≤ s0 := by exact_mod_cast hCcardUpper
  have hriskExact : C.card.choose 2 * pCollision / E +
      C.card * pDegree / tDegree ≤ 2 / 3 := by
    calc
      C.card.choose 2 * pCollision / E + C.card * pDegree / tDegree ≤
          (s0 : Real) ^ 2 * pCollision / E +
            s0 * pDegree / tDegree := by
        apply add_le_add
        · exact div_le_div_of_nonneg_right
            (mul_le_mul_of_nonneg_right hchoose hpCollision) hE.le
        · exact div_le_div_of_nonneg_right
            (mul_le_mul_of_nonneg_right hcardReal hpDegree) htDegree.le
      _ ≤ 2 / 3 := by simpa [pCollision, pDegree] using hrisk
  have hbadDegreeC : badDegree < C.card := hgoodLower.trans_le hCcardLower
  have hpieceExact : piece * (C.card + 2 * edgeBudget) ≤
      (C.card - badDegree) ^ 2 := by
    calc
      piece * (C.card + 2 * edgeBudget) ≤
          piece * (s0 + 2 * edgeBudget) := by
            exact Nat.mul_le_mul_left piece
              (Nat.add_le_add_right hCcardUpper _)
      _ ≤ (s0 - outerBad - badDegree) ^ 2 := hpiece
      _ ≤ (C.card - badDegree) ^ 2 := by
        exact Nat.pow_le_pow_left (Nat.sub_le_sub_right hCcardLower badDegree) 2
  have hmain := one_third_le_layerProbability_innerWindowGood_oneState
    G (Augmentation.structuralBase S branch) S.U0 D1 S.matching C state
      nD (nZ - 1) L
      (smallNZRadius K nZ nD D1 innerDeviation outerRadius)
      pCollision pDegree E tDegree
      (smallNZCenter S branch D1 nD state outerCenter)
      edgeBudget badDegree piece hhalf hCM hstateM hstateCard haway
      hcollision (innerDegreeBad G D1 nD innerDeviation) hdegree hwindow
      hE htDegree hriskExact hEbudget htDegreeBudget hbadDegreeC
      hpieceExact hpiecePos hL
  refine ⟨state, hstateM, hstateCard, ?_⟩
  simpa [Nat.sub_add_cancel hnZ] using hmain

/-! ## Arbitrary crowded-time graph wrapper -/

/-- The one-state centre at an arbitrary switching time `W`.  The real
parameter `wCenter` is a common centre for the `W`-degrees of the crowd,
and `d0` is its common degree into the reservoir. -/
def generalSmallNZCenter (G : SimpleGraph V) (W U0 D1 : Finset V)
    (nD : Nat) (state : Finset (Finset V))
    (wCenter d0 outerCenter : Real) (D : Finset V) : Real :=
  (Erdos88.inducedEdges G
      (AugmentationGraphFull.exposedBase W U0 D
        (fun _ : Unit => state) ()) : Real) +
    wCenter + d0 - (nD : Real) / D1.card * outerCenter

/-- The common arbitrary-time radius. -/
def generalSmallNZRadius (K nZ nD : Nat) (D1 : Finset V)
    (wDeviation innerDeviation outerRadius : Real) : Real :=
  K ^ 2 * nZ + wDeviation + innerDeviation +
    (nD : Real) / D1.card * outerRadius

/-- Deterministic common-window estimate for an arbitrary matching crowd
away from `W ∪ U0`. -/
theorem oneStateValue_mem_generalSmallNZWindow
    (G : SimpleGraph V) (W U0 D1 : Finset V)
    (M : Finset (Finset V)) (k K nD nZ d0 : Nat)
    (state : Finset (Finset V)) (x : Finset V)
    (wCenter wDeviation outerCenter outerRadius innerDeviation : Real)
    (hnZ : 1 ≤ nZ) (hD1 : D1 ⊆ U0) (hWU0 : Disjoint W U0)
    (hpair : (M : Set (Finset V)).PairwiseDisjoint id)
    (huniform : ∀ z ∈ M, z.card = k) (hk : k ≤ K)
    (haway : ∀ z ∈ M, Disjoint z (W ∪ U0))
    (hstate : state ⊆ M) (hstateCard : state.card = nZ - 1)
    (hx : x ∈ M) (hxstate : x ∉ state)
    (hUdegree : degreeInto G U0 x = d0)
    (hWdegree : |(degreeInto G W x : Real) - wCenter| ≤ wDeviation)
    (hxOuter : AugmentationGraphPartial.DegreeGood
      G D1 x outerCenter outerRadius)
    (omega : BoolSlice D1 nD)
    (hxInner : ¬ innerDegreeBad G D1 nD innerDeviation x omega) :
    |(oneStateValue G W U0
          (AugmentationGraphPartial.sampleFinset D1 nD omega) state x : Real) -
        generalSmallNZCenter G W U0 D1 nD state wCenter d0 outerCenter
          (AugmentationGraphPartial.sampleFinset D1 nD omega)| ≤
      generalSmallNZRadius K nZ nD D1
        wDeviation innerDeviation outerRadius := by
  classical
  let D := AugmentationGraphPartial.sampleFinset D1 nD omega
  let Z := AugmentationGraphFull.cellUnion state
  have hDU : D ⊆ U0 :=
    (AugmentationGraphPartial.sampleFinset_subset D1 nD omega).trans hD1
  have hWZ : Disjoint W Z :=
    (AugmentationGraphFull.cellUnion_disjoint_right_of_away hstate
      (fun z hz => (haway z hz).mono_right Finset.subset_union_left)).symm
  have hUZ : Disjoint U0 Z :=
    (AugmentationGraphFull.cellUnion_disjoint_right_of_away hstate
      (fun z hz => (haway z hz).mono_right Finset.subset_union_right)).symm
  have hZx : Disjoint Z x :=
    AugmentationGraphFull.cellUnion_disjoint_cell_of_pairwise
      hpair hstate hx hxstate
  have hWx : Disjoint W x :=
    ((haway x hx).mono_right Finset.subset_union_left).symm
  have hUx : Disjoint U0 x :=
    ((haway x hx).mono_right Finset.subset_union_right).symm
  have hpairState : (state : Set (Finset V)).PairwiseDisjoint id := by
    intro a ha b hb hab
    exact hpair (hstate ha) (hstate hb) hab
  have hZcardEq : Z.card = state.card * k :=
    card_matching_biUnion_eq_mul hpairState
      (fun z hz => huniform z (hstate hz))
  have hZcard : Z.card ≤ K * (nZ - 1) := by
    rw [hZcardEq, hstateCard]
    simpa [Nat.mul_comm] using Nat.mul_le_mul_right (nZ - 1) hk
  have hxK : x.card ≤ K := (huniform x hx).le.trans hk
  have hcellBound : Erdos88.inducedEdges G x + (G.interedges Z x).card ≤
      K ^ 2 * nZ :=
    matchingCellIncrement_le G hnZ hZcard hxK
  have hWdegreeNat : (G.interedges W x).card = degreeInto G W x :=
    AugmentationGraphFullIdentity.card_interedges_eq_degreeInto G W x
  have hid := AugmentationGraphFullIdentity.literalCandidateExtension_sub_base_int
    G W U0 D Z x hDU hWU0 hWZ hUZ hWx hUx hZx
  simp only [AugmentationGraphFullIdentity.candidateOffsetInt] at hid
  rw [hWdegreeNat, hUdegree] at hid
  have hidReal :
      (oneStateValue G W U0 D state x : Real) -
          Erdos88.inducedEdges G
            (AugmentationGraphFull.exposedBase W U0 D
              (fun _ : Unit => state) ()) =
        (Erdos88.inducedEdges G x : Real) + (G.interedges Z x).card +
          degreeInto G W x + d0 - degreeInto G D x := by
    have hid' := congrArg (fun z : Int => (z : Real)) hid
    push_cast at hid'
    simp only [oneStateValue, AugmentationGraphFull.exposedBase,
      AugmentationGraphFullIdentity.literalState,
      AugmentationGraphFullIdentity.deletionBase,
      AugmentationGraphFullIdentity.literalPathNat, Z] at hid'
    simp only [oneStateValue, AugmentationGraphFull.exposedBase,
      AugmentationGraphFullIdentity.literalState,
      AugmentationGraphFullIdentity.deletionBase,
      AugmentationGraphFullIdentity.literalPathNat, Z]
    linarith
  let r : Real := (nD : Real) / D1.card
  have hr : 0 ≤ r := by positivity
  have hinner : |(degreeInto G D x : Real) - r * degreeInto G D1 x| ≤
      innerDeviation := (lt_of_not_ge hxInner).le
  have houter : |r * (degreeInto G D1 x : Real) - r * outerCenter| ≤
      r * outerRadius := by
    rw [← mul_sub, abs_mul, abs_of_nonneg hr]
    exact mul_le_mul_of_nonneg_left hxOuter hr
  have hdeletion : |r * outerCenter - (degreeInto G D x : Real)| ≤
      innerDeviation + r * outerRadius := by
    calc
      |r * outerCenter - (degreeInto G D x : Real)| =
          |(r * outerCenter - r * degreeInto G D1 x) +
            (r * degreeInto G D1 x - degreeInto G D x)| := by ring_nf
      _ ≤ |r * outerCenter - r * degreeInto G D1 x| +
          |r * degreeInto G D1 x - degreeInto G D x| := abs_add_le _ _
      _ = |r * degreeInto G D1 x - r * outerCenter| +
          |(degreeInto G D x : Real) - r * degreeInto G D1 x| := by
            congr 1 <;> exact abs_sub_comm _ _
      _ ≤ r * outerRadius + innerDeviation := add_le_add houter hinner
      _ = innerDeviation + r * outerRadius := by ring
  have hmain :
      |(oneStateValue G W U0 D state x : Real) -
          generalSmallNZCenter G W U0 D1 nD state
            wCenter d0 outerCenter D| ≤
        (K ^ 2 * nZ : Nat) + wDeviation + innerDeviation +
          r * outerRadius := by
    rw [generalSmallNZCenter]
    have heq :
        (oneStateValue G W U0 D state x : Real) -
            ((Erdos88.inducedEdges G
              (AugmentationGraphFull.exposedBase W U0 D
                (fun _ : Unit => state) ()) : Real) +
              wCenter + d0 - r * outerCenter) =
          ((Erdos88.inducedEdges G x : Real) + (G.interedges Z x).card) +
            ((degreeInto G W x : Real) - wCenter) +
            (r * outerCenter - degreeInto G D x) := by
      linarith [hidReal]
    rw [show (nD : Real) / D1.card = r by rfl, heq]
    calc
      |((Erdos88.inducedEdges G x : Real) + (G.interedges Z x).card) +
          ((degreeInto G W x : Real) - wCenter) +
          (r * outerCenter - degreeInto G D x)| ≤
          |((Erdos88.inducedEdges G x : Real) + (G.interedges Z x).card)| +
            |(degreeInto G W x : Real) - wCenter| +
            |r * outerCenter - degreeInto G D x| := by
              calc
                _ ≤ |((Erdos88.inducedEdges G x : Real) +
                      (G.interedges Z x).card) +
                    ((degreeInto G W x : Real) - wCenter)| +
                    |r * outerCenter - degreeInto G D x| := abs_add_le _ _
                _ ≤ _ := by
                  gcongr
                  exact abs_add_le _ _
      _ = ((Erdos88.inducedEdges G x : Real) + (G.interedges Z x).card) +
            |(degreeInto G W x : Real) - wCenter| +
            |r * outerCenter - degreeInto G D x| := by
              rw [abs_of_nonneg (by positivity)]
      _ ≤ (K ^ 2 * nZ : Nat) + wDeviation +
            (innerDeviation + r * outerRadius) := by
              gcongr
              exact_mod_cast hcellBound
      _ = (K ^ 2 * nZ : Nat) + wDeviation + innerDeviation +
            r * outerRadius := by ring
  simpa [D, generalSmallNZRadius, r] using hmain

/-- Collision anti-concentration for an arbitrary switching-time crowd.
All fixed `W`, reservoir, and frozen-state contributions are absorbed into
the target value of the slice-linear form. -/
theorem uniformProbability_oneStateValue_collision_le_general
    (G : SimpleGraph V) (W U0 D1 : Finset V)
    (M : Finset (Finset V)) (k K nD : Nat)
    (state : Finset (Finset V)) (x y : Finset V)
    (c theta outerCenter outerRadius : Real)
    (hnD : 0 < nD) (hhalf : D1.card = 2 * nD) (hD1 : D1 ⊆ U0)
    (hWU0 : Disjoint W U0)
    (hpair : (M : Set (Finset V)).PairwiseDisjoint id)
    (huniform : ∀ z ∈ M, z.card = k) (hk : k ≤ K)
    (haway : ∀ z ∈ M, Disjoint z (W ∪ U0))
    (hstate : state ⊆ M)
    (hx : x ∈ M) (hy : y ∈ M)
    (hxstate : x ∉ state) (hystate : y ∉ state) (hxy : x ≠ y)
    (hxOuter : AugmentationGraphPartial.DegreeGood
      G D1 x outerCenter outerRadius)
    (hyOuter : AugmentationGraphPartial.DegreeGood
      G D1 y outerCenter outerRadius)
    (hdiverse : theta * D1.card ≤ incidenceDiffMass G D1 x y)
    (hc0 : 0 < c) (hc1 : c ≤ 1 / 2) (htheta : 0 < theta)
    (hK : 1 ≤ K)
    (hsmall : 2 * outerRadius < theta / 2 * D1.card)
    (hselected : c * D1.card ≤ (nD : Real))
    (hunselected : c * D1.card ≤ ((D1.card - nD : Nat) : Real)) :
    uniformProbability (fun omega : BoolSlice D1 nD =>
      oneStateValue G W U0
          (AugmentationGraphPartial.sampleFinset D1 nD omega) state x =
        oneStateValue G W U0
          (AugmentationGraphPartial.sampleFinset D1 nD omega) state y) ≤
      AntiConcentration.variancePointMassConstant
          c (theta ^ 2 / 4) K / Real.sqrt (D1.card : Real) := by
  classical
  have hD1pos : 0 < Fintype.card D1 := by
    simp only [Fintype.card_coe, hhalf]
    omega
  letI : Nonempty
      (Erdos88.BooleanSlices.BooleanSlicePoint D1 nD) :=
    SliceMoments.nonempty_booleanSlicePoint D1 nD (by omega)
  let E := AugmentationGraphPartial.boolSliceEquivBooleanSlicePoint D1 nD
  letI : Nonempty (BoolSlice D1 nD) := E.nonempty_congr.mpr inferInstance
  let a : D1 -> Int := fun u =>
    AugmentationGraphFullIdentity.reservoirIncidence G D1 y u -
      AugmentationGraphFullIdentity.reservoirIncidence G D1 x u
  let mu : Real := (∑ u, (a u : Real)) / Fintype.card D1
  have hbounded : ∀ u, |a u| ≤ (K : Int) := by
    intro u
    exact AugmentationGraphFullIdentity.abs_reservoirIncidence_sub_le_of_card_le
      G D1 x y K ((huniform x hx).le.trans hk)
        ((huniform y hy).le.trans hk) u
  have hmean : (Fintype.card D1 : Real) * mu = ∑ u, (a u : Real) := by
    dsimp only [mu]
    field_simp [ne_of_gt (by exact_mod_cast hD1pos)]
  have hlone : theta * Fintype.card D1 ≤ ∑ u, |(a u : Real)| := by
    rw [show (∑ u, |(a u : Real)|) = incidenceDiffMass G D1 x y by
      simpa [a, AugmentationGraphFullIdentity.replacementCoeff] using
        AugmentationGraphFullIdentity.sum_abs_replacementCoeff_eq_incidenceDiffMass
          G D1 x y]
    simpa using hdiverse
  have hsigned : ∑ u, (a u : Real) =
      (degreeInto G D1 y : Real) - degreeInto G D1 x := by
    simpa [a, AugmentationGraphFullIdentity.replacementCoeff] using
      AugmentationGraphFullIdentity.sum_replacementCoeff_eq_degreeInto_sub
        G D1 x y
  have hsignedSmall : |∑ u, (a u : Real)| <
      theta / 2 * Fintype.card D1 := by
    rw [hsigned]
    have htri : |(degreeInto G D1 y : Real) - degreeInto G D1 x| ≤
        |(degreeInto G D1 y : Real) - outerCenter| +
          |(degreeInto G D1 x : Real) - outerCenter| := by
      calc
        |(degreeInto G D1 y : Real) - degreeInto G D1 x| =
            |((degreeInto G D1 y : Real) - outerCenter) -
              ((degreeInto G D1 x : Real) - outerCenter)| := by ring_nf
        _ ≤ _ := abs_sub _ _
    have htwo : |(degreeInto G D1 y : Real) - outerCenter| +
        |(degreeInto G D1 x : Real) - outerCenter| ≤ 2 * outerRadius := by
      dsimp only [AugmentationGraphPartial.DegreeGood] at hxOuter hyOuter
      linarith
    exact (htri.trans htwo).trans_lt (by simpa using hsmall)
  let target : Real :=
    (AugmentationGraphFullIdentity.candidateOffsetInt G W U0
        (AugmentationGraphFull.cellUnion state) y -
      AugmentationGraphFullIdentity.candidateOffsetInt G W U0
        (AugmentationGraphFull.cellUnion state) x : Int)
  have hanti :=
    AntiConcentration.slice_point_probability_le_of_integer_l1_small_sum
      a mu c theta K nD hc0 hc1 htheta hK hD1pos hbounded hmean hlone
        hsignedSmall (by simpa using hselected)
        (by
          rw [Fintype.card_coe,
            ← Nat.cast_sub (R := Real) (show nD ≤ D1.card by omega)]
          exact hunselected) target
  have hWZ : Disjoint W (AugmentationGraphFull.cellUnion state) :=
    (AugmentationGraphFull.cellUnion_disjoint_right_of_away hstate
      (fun z hz => (haway z hz).mono_right Finset.subset_union_left)).symm
  have hUZ : Disjoint U0 (AugmentationGraphFull.cellUnion state) :=
    (AugmentationGraphFull.cellUnion_disjoint_right_of_away hstate
      (fun z hz => (haway z hz).mono_right Finset.subset_union_right)).symm
  have hZx := AugmentationGraphFull.cellUnion_disjoint_cell_of_pairwise
    hpair hstate hx hxstate
  have hZy := AugmentationGraphFull.cellUnion_disjoint_cell_of_pairwise
    hpair hstate hy hystate
  have hWx : Disjoint W x :=
    ((haway x hx).mono_right Finset.subset_union_left).symm
  have hUx : Disjoint U0 x :=
    ((haway x hx).mono_right Finset.subset_union_right).symm
  have hWy : Disjoint W y :=
    ((haway y hy).mono_right Finset.subset_union_left).symm
  have hUy : Disjoint U0 y :=
    ((haway y hy).mono_right Finset.subset_union_right).symm
  have hstat (omega : BoolSlice D1 nD) :
      AntiConcentration.sliceLinear nD (fun u => (a u : Real)) omega =
        HalfSample.sliceSum
          (AugmentationGraphFullIdentity.replacementCoeff G D1 x y)
          (boolSliceAsHalf D1 nD omega) := by
    change AugmentationPartial.incidenceSum nD a omega = _
    rw [AugmentationGraphPartial.incidenceSum_eq_sliceSum]
    rfl
  have hmono : uniformProbability (fun omega : BoolSlice D1 nD =>
      oneStateValue G W U0
          (AugmentationGraphPartial.sampleFinset D1 nD omega) state x =
        oneStateValue G W U0
          (AugmentationGraphPartial.sampleFinset D1 nD omega) state y) ≤
      uniformProbability (fun omega : BoolSlice D1 nD =>
        AntiConcentration.sliceLinear nD (fun u => (a u : Real)) omega =
          target) := by
    apply uniformProbability_mono
    intro omega hcollisionValue
    have hiff := AugmentationGraphFullIdentity.literalCandidateCollision_iff
      G W U0 D1 (AugmentationGraphFull.cellUnion state) x y nD
        (boolSliceAsHalf D1 nD omega) hD1 hWU0 hWZ hUZ
        hWx hUx hZx hWy hUy hZy
    rw [halfDeletion_boolSliceAsHalf] at hiff
    have heq : HalfSample.sliceSum
        (AugmentationGraphFullIdentity.replacementCoeff G D1 x y)
        (boolSliceAsHalf D1 nD omega) = target := by
      apply hiff.mp
      simpa [oneStateValue, AugmentationGraphFull.exposedBase,
        AugmentationGraphFullIdentity.literalState,
        AugmentationGraphFullIdentity.deletionBase] using hcollisionValue
    rw [hstat omega]
    exact heq
  exact hmono.trans (by
    change Erdos88.Fourier.finProbability (BoolSlice D1 nD)
        (fun omega => AntiConcentration.sliceLinear nD
          (fun u => (a u : Real)) omega = target) ≤ _
    simpa only [Fintype.card_coe] using hanti)

/-- **General bounded-`nZ` graph endpoint.**

This is the version used at each time of a crowded switching path.  It is
fully general in `W`, `U0`, and the current crowd `M`.  A partial-good
exposure supplies the two candidate families; the graph assumptions below
discharge both point-collision and inner-degree probabilities. -/
theorem one_third_le_layerProbability_innerWindowGood_general_of_partialGood
    (G : SimpleGraph V) (W U0 : Finset V) (M : Finset (Finset V))
    (k K d0 nD nZ s0 : Nat)
    (D1 : Finset V)
    (diversityThreshold outerCenter outerRadius tS tX tCollision : Real)
    (wCenter wDeviation c theta innerDeviation E tDegree L : Real)
    (outerBad edgeBudget badDegree piece : Nat)
    (hpartial : AugmentationGraphPartial.PartialGood G M s0
      diversityThreshold outerCenter outerRadius tS tX tCollision D1)
    (hnD : 0 < nD) (hnZ : 1 ≤ nZ) (hhalf : D1.card = 2 * nD)
    (hD1 : D1 ⊆ U0) (hstateSize : nZ - 1 ≤ s0)
    (hWU0 : Disjoint W U0)
    (hpair : (M : Set (Finset V)).PairwiseDisjoint id)
    (huniform : ∀ x ∈ M, x.card = k) (hk : k ≤ K)
    (haway : ∀ x ∈ M, Disjoint x (W ∪ U0))
    (hUdegree : ∀ x ∈ M, degreeInto G U0 x = d0)
    (hWdegree : ∀ x ∈ M,
      |(degreeInto G W x : Real) - wCenter| ≤ wDeviation)
    (hK : 1 ≤ K)
    (hdiversityScale : theta * D1.card ≤ diversityThreshold)
    (hc0 : 0 < c) (hc1 : c ≤ 1 / 2) (htheta : 0 < theta)
    (hsmall : 2 * outerRadius < theta / 2 * D1.card)
    (hselected : c * D1.card ≤ (nD : Real))
    (hunselected : c * D1.card ≤ ((D1.card - nD : Nat) : Real))
    (hinnerDeviation : 0 ≤ innerDeviation)
    (htXBudget : tX ≤ (outerBad : Real) + 1)
    (hgoodLower : badDegree < s0 - outerBad)
    (hE : 0 < E) (htDegree : 0 < tDegree)
    (hrisk :
      let pCollision := AntiConcentration.variancePointMassConstant
        c (theta ^ 2 / 4) K / Real.sqrt (D1.card : Real)
      let pDegree := innerLinearFailure nD K innerDeviation
      (s0 : Real) ^ 2 * pCollision / E +
          s0 * pDegree / tDegree ≤ 2 / 3)
    (hEbudget : E ≤ (edgeBudget : Real) + 1)
    (htDegreeBudget : tDegree ≤ (badDegree : Real) + 1)
    (hpiece : piece * (s0 + 2 * edgeBudget) ≤
      (s0 - outerBad - badDegree) ^ 2)
    (hpiecePos : 0 < piece) (hL : L ≤ piece) :
    ∃ state : Finset (Finset V),
      state ⊆ M ∧ state.card = nZ - 1 ∧
        (1 / 3 : Real) ≤ NestedUniform.layerProbability D1 nD
          (fun D => AugmentationGraphFull.innerWindowGood G W U0 M nZ L
            (generalSmallNZCenter G W U0 D1 nD state
              wCenter d0 outerCenter D)
            (generalSmallNZRadius K nZ nD D1
              wDeviation innerDeviation outerRadius) D) := by
  classical
  let pCollision := AntiConcentration.variancePointMassConstant
    c (theta ^ 2 / 4) K / Real.sqrt (D1.card : Real)
  let pDegree := innerLinearFailure nD K innerDeviation
  obtain ⟨S0, X0, hS0M, hX0M, hS0card, hX0card, hdisjoint,
    hdiverse, _hbadS, hbadX, _hcoll⟩ := hpartial
  have hstateSize' : nZ - 1 ≤ S0.card := by omega
  obtain ⟨state, hstateS0, hstateCard⟩ :=
    Finset.exists_subset_card_eq hstateSize'
  have hstateM : state ⊆ M := hstateS0.trans hS0M
  let C := AugmentationGraphPartial.goodCells
    G D1 outerCenter outerRadius X0
  have hCM : C ⊆ M := (Finset.filter_subset _ _).trans hX0M
  have hCcardUpper : C.card ≤ s0 := by
    rw [← hX0card]
    exact Finset.card_le_card (Finset.filter_subset _ _)
  have hbadOuter :
      (X0.filter fun x => ¬ AugmentationGraphPartial.DegreeGood
        G D1 x outerCenter outerRadius).card ≤ outerBad := by
    have hlt :
        ((X0.filter fun x => ¬ AugmentationGraphPartial.DegreeGood
          G D1 x outerCenter outerRadius).card : Real) <
          (outerBad : Real) + 1 := hbadX.trans_le htXBudget
    have hltNat :
        (X0.filter fun x => ¬ AugmentationGraphPartial.DegreeGood
          G D1 x outerCenter outerRadius).card < outerBad + 1 := by
      exact_mod_cast hlt
    omega
  have hCcardLower : s0 - outerBad ≤ C.card := by
    have hpartition := Finset.card_filter_add_card_filter_not
      (s := X0) (p := fun x => AugmentationGraphPartial.DegreeGood
        G D1 x outerCenter outerRadius)
    change (X0.filter fun x => AugmentationGraphPartial.DegreeGood
        G D1 x outerCenter outerRadius).card +
      (X0.filter fun x => ¬ AugmentationGraphPartial.DegreeGood
        G D1 x outerCenter outerRadius).card = X0.card at hpartition
    change C.card +
      (X0.filter fun x => ¬ AugmentationGraphPartial.DegreeGood
        G D1 x outerCenter outerRadius).card = X0.card at hpartition
    omega
  have hstateAway : ∀ x ∈ C, x ∉ state := by
    intro x hxC hxstate
    have hxX0 : x ∈ X0 := (Finset.filter_subset _ _) hxC
    exact Finset.disjoint_left.mp hdisjoint (hstateS0 hxstate) hxX0
  have hcollision : ∀ x ∈ C, ∀ y ∈ C, x ≠ y ->
      uniformProbability (fun omega : BoolSlice D1 nD =>
        oneStateValue G W U0
            (AugmentationGraphPartial.sampleFinset D1 nD omega) state x =
          oneStateValue G W U0
            (AugmentationGraphPartial.sampleFinset D1 nD omega) state y) ≤
        pCollision := by
    intro x hxC y hyC hxy
    have hxX0 : x ∈ X0 := (Finset.filter_subset _ _) hxC
    have hyX0 : y ∈ X0 := (Finset.filter_subset _ _) hyC
    apply uniformProbability_oneStateValue_collision_le_general
      G W U0 D1 M k K nD state x y c theta outerCenter outerRadius
      hnD hhalf hD1 hWU0 hpair huniform hk haway hstateM
      (hX0M hxX0) (hX0M hyX0) (hstateAway x hxC) (hstateAway y hyC) hxy
      (Finset.mem_filter.mp hxC).2 (Finset.mem_filter.mp hyC).2
      (hdiversityScale.trans (hdiverse x hxX0 y hyX0 hxy))
      hc0 hc1 htheta hK hsmall hselected hunselected
  have hdegree : ∀ x ∈ C,
      uniformProbability (innerDegreeBad G D1 nD innerDeviation x) ≤
        pDegree := by
    intro x hxC
    exact uniformProbability_innerDegreeBad_le G D1 x nD K innerDeviation
      hnD hhalf hK ((huniform x (hCM hxC)).le.trans hk) hinnerDeviation
  have hwindow : ∀ omega : BoolSlice D1 nD, ∀ x ∈ C,
      ¬ innerDegreeBad G D1 nD innerDeviation x omega ->
      |(oneStateValue G W U0
          (AugmentationGraphPartial.sampleFinset D1 nD omega) state x : Real) -
          generalSmallNZCenter G W U0 D1 nD state wCenter d0 outerCenter
            (AugmentationGraphPartial.sampleFinset D1 nD omega)| ≤
        generalSmallNZRadius K nZ nD D1
          wDeviation innerDeviation outerRadius := by
    intro omega x hxC hxGood
    exact oneStateValue_mem_generalSmallNZWindow G W U0 D1 M
      k K nD nZ d0 state x wCenter wDeviation outerCenter outerRadius
      innerDeviation hnZ hD1 hWU0 hpair huniform hk haway hstateM
      hstateCard (hCM hxC) (hstateAway x hxC) (hUdegree x (hCM hxC))
      (hWdegree x (hCM hxC)) (Finset.mem_filter.mp hxC).2 omega hxGood
  have hpCollision : 0 ≤ pCollision := by
    dsimp only [pCollision]
    apply div_nonneg
    · exact (AntiConcentration.variancePointMassConstant_pos hc0
        (by positivity) (by omega)).le
    · positivity
  have hpDegree : 0 ≤ pDegree := by
    dsimp only [pDegree, innerLinearFailure]
    positivity
  have hchoose : ((C.card.choose 2 : Nat) : Real) ≤ (s0 : Real) ^ 2 := by
    exact_mod_cast ((Nat.choose_le_pow C.card 2).trans
      (Nat.pow_le_pow_left hCcardUpper 2))
  have hcardReal : (C.card : Real) ≤ s0 := by exact_mod_cast hCcardUpper
  have hriskExact : C.card.choose 2 * pCollision / E +
      C.card * pDegree / tDegree ≤ 2 / 3 := by
    calc
      C.card.choose 2 * pCollision / E + C.card * pDegree / tDegree ≤
          (s0 : Real) ^ 2 * pCollision / E +
            s0 * pDegree / tDegree := by
        apply add_le_add
        · exact div_le_div_of_nonneg_right
            (mul_le_mul_of_nonneg_right hchoose hpCollision) hE.le
        · exact div_le_div_of_nonneg_right
            (mul_le_mul_of_nonneg_right hcardReal hpDegree) htDegree.le
      _ ≤ 2 / 3 := by simpa [pCollision, pDegree] using hrisk
  have hbadDegreeC : badDegree < C.card := hgoodLower.trans_le hCcardLower
  have hpieceExact : piece * (C.card + 2 * edgeBudget) ≤
      (C.card - badDegree) ^ 2 := by
    calc
      piece * (C.card + 2 * edgeBudget) ≤
          piece * (s0 + 2 * edgeBudget) := by
            exact Nat.mul_le_mul_left piece
              (Nat.add_le_add_right hCcardUpper _)
      _ ≤ (s0 - outerBad - badDegree) ^ 2 := hpiece
      _ ≤ (C.card - badDegree) ^ 2 := by
        exact Nat.pow_le_pow_left
          (Nat.sub_le_sub_right hCcardLower badDegree) 2
  have hmain := one_third_le_layerProbability_innerWindowGood_oneState
    G W U0 D1 M C state nD (nZ - 1) L
      (generalSmallNZRadius K nZ nD D1
        wDeviation innerDeviation outerRadius)
      pCollision pDegree E tDegree
      (generalSmallNZCenter G W U0 D1 nD state wCenter d0 outerCenter)
      edgeBudget badDegree piece hhalf hCM hstateM hstateCard hstateAway
      hcollision (innerDegreeBad G D1 nD innerDeviation) hdegree hwindow
      hE htDegree hriskExact hEbudget htDegreeBudget hbadDegreeC
      hpieceExact hpiecePos hL
  refine ⟨state, hstateM, hstateCard, ?_⟩
  simpa [Nat.sub_add_cancel hnZ] using hmain

/-- A composable one-state centre.  The frozen state is fixed before the
intermediate exposure, and the half-slice ratio is written as `1 / 2`;
hence this is a function of the final deletion only. -/
def fixedStateSmallNZCenter (G : SimpleGraph V) (W U0 : Finset V)
    (state : Finset (Finset V)) (wCenter d0 outerCenter : Real)
    (D : Finset V) : Real :=
  (Erdos88.inducedEdges G
      (AugmentationGraphFull.exposedBase W U0 D
        (fun _ : Unit => state) ()) : Real) +
    wCenter + d0 - (1 / 2 : Real) * outerCenter

/-- Fixed-state, arbitrary-time bounded-`nZ` endpoint.

Unlike the existential-state form, this theorem quantifies `state` before
`D1`.  The candidates in `X0` that happen to belong to `state` are removed,
costing at most `nZ - 1` vertices.  Its conclusion therefore has one centre
which depends only on the eventual deletion `D`, as required by the nested
outer/inner and shared-deletion compositions. -/
theorem one_third_le_layerProbability_innerWindowGood_fixedState_of_partialGood
    (G : SimpleGraph V) (W U0 : Finset V) (M : Finset (Finset V))
    (k K d0 nD nZ s0 : Nat) (state : Finset (Finset V))
    (D1 : Finset V)
    (diversityThreshold outerCenter outerRadius tS tX tCollision : Real)
    (wCenter wDeviation c theta innerDeviation E tDegree L : Real)
    (outerBad edgeBudget badDegree piece : Nat)
    (hpartial : AugmentationGraphPartial.PartialGood G M s0
      diversityThreshold outerCenter outerRadius tS tX tCollision D1)
    (hnD : 0 < nD) (hnZ : 1 ≤ nZ) (hhalf : D1.card = 2 * nD)
    (hD1 : D1 ⊆ U0)
    (hWU0 : Disjoint W U0)
    (hpair : (M : Set (Finset V)).PairwiseDisjoint id)
    (huniform : ∀ x ∈ M, x.card = k) (hk : k ≤ K)
    (haway : ∀ x ∈ M, Disjoint x (W ∪ U0))
    (hUdegree : ∀ x ∈ M, degreeInto G U0 x = d0)
    (hWdegree : ∀ x ∈ M,
      |(degreeInto G W x : Real) - wCenter| ≤ wDeviation)
    (hstate : state ⊆ M) (hstateCard : state.card = nZ - 1)
    (hK : 1 ≤ K)
    (hdiversityScale : theta * D1.card ≤ diversityThreshold)
    (hc0 : 0 < c) (hc1 : c ≤ 1 / 2) (htheta : 0 < theta)
    (hsmall : 2 * outerRadius < theta / 2 * D1.card)
    (hselected : c * D1.card ≤ (nD : Real))
    (hunselected : c * D1.card ≤ ((D1.card - nD : Nat) : Real))
    (hinnerDeviation : 0 ≤ innerDeviation)
    (htXBudget : tX ≤ (outerBad : Real) + 1)
    (hgoodLower : badDegree < s0 - outerBad - (nZ - 1))
    (hE : 0 < E) (htDegree : 0 < tDegree)
    (hrisk :
      let pCollision := AntiConcentration.variancePointMassConstant
        c (theta ^ 2 / 4) K / Real.sqrt (D1.card : Real)
      let pDegree := innerLinearFailure nD K innerDeviation
      (s0 : Real) ^ 2 * pCollision / E +
          s0 * pDegree / tDegree ≤ 2 / 3)
    (hEbudget : E ≤ (edgeBudget : Real) + 1)
    (htDegreeBudget : tDegree ≤ (badDegree : Real) + 1)
    (hpiece : piece * (s0 + 2 * edgeBudget) ≤
      (s0 - outerBad - (nZ - 1) - badDegree) ^ 2)
    (hpiecePos : 0 < piece) (hL : L ≤ piece) :
    (1 / 3 : Real) ≤ NestedUniform.layerProbability D1 nD
      (fun D => AugmentationGraphFull.innerWindowGood G W U0 M nZ L
        (fixedStateSmallNZCenter G W U0 state wCenter d0 outerCenter D)
        (generalSmallNZRadius K nZ nD D1
          wDeviation innerDeviation outerRadius) D) := by
  classical
  let pCollision := AntiConcentration.variancePointMassConstant
    c (theta ^ 2 / 4) K / Real.sqrt (D1.card : Real)
  let pDegree := innerLinearFailure nD K innerDeviation
  obtain ⟨_S0, X0, _hS0M, hX0M, _hS0card, hX0card, _hdisjoint,
    hdiverse, _hbadS, hbadX, _hcoll⟩ := hpartial
  let C0 := AugmentationGraphPartial.goodCells
    G D1 outerCenter outerRadius X0
  let C := C0 \ state
  have hC0M : C0 ⊆ M := (Finset.filter_subset _ _).trans hX0M
  have hCM : C ⊆ M := (Finset.sdiff_subset.trans hC0M)
  have hCcardUpper : C.card ≤ s0 := by
    calc
      C.card ≤ C0.card := Finset.card_le_card Finset.sdiff_subset
      _ ≤ X0.card := Finset.card_le_card (Finset.filter_subset _ _)
      _ = s0 := hX0card
  have hbadOuter :
      (X0.filter fun x => ¬ AugmentationGraphPartial.DegreeGood
        G D1 x outerCenter outerRadius).card ≤ outerBad := by
    have hlt :
        ((X0.filter fun x => ¬ AugmentationGraphPartial.DegreeGood
          G D1 x outerCenter outerRadius).card : Real) <
          (outerBad : Real) + 1 := hbadX.trans_le htXBudget
    have hltNat :
        (X0.filter fun x => ¬ AugmentationGraphPartial.DegreeGood
          G D1 x outerCenter outerRadius).card < outerBad + 1 := by
      exact_mod_cast hlt
    omega
  have hC0cardLower : s0 - outerBad ≤ C0.card := by
    have hpartition := Finset.card_filter_add_card_filter_not
      (s := X0) (p := fun x => AugmentationGraphPartial.DegreeGood
        G D1 x outerCenter outerRadius)
    change (X0.filter fun x => AugmentationGraphPartial.DegreeGood
        G D1 x outerCenter outerRadius).card +
      (X0.filter fun x => ¬ AugmentationGraphPartial.DegreeGood
        G D1 x outerCenter outerRadius).card = X0.card at hpartition
    change C0.card +
      (X0.filter fun x => ¬ AugmentationGraphPartial.DegreeGood
        G D1 x outerCenter outerRadius).card = X0.card at hpartition
    omega
  have hCcardLower : s0 - outerBad - (nZ - 1) ≤ C.card := by
    rw [Finset.card_sdiff]
    have hinter : (state ∩ C0).card ≤ state.card :=
      Finset.card_le_card Finset.inter_subset_left
    omega
  have hstateAway : ∀ x ∈ C, x ∉ state := by
    intro x hx
    exact (Finset.mem_sdiff.mp hx).2
  have hcollision : ∀ x ∈ C, ∀ y ∈ C, x ≠ y ->
      uniformProbability (fun omega : BoolSlice D1 nD =>
        oneStateValue G W U0
            (AugmentationGraphPartial.sampleFinset D1 nD omega) state x =
          oneStateValue G W U0
            (AugmentationGraphPartial.sampleFinset D1 nD omega) state y) ≤
        pCollision := by
    intro x hxC y hyC hxy
    have hxC0 : x ∈ C0 := (Finset.mem_sdiff.mp hxC).1
    have hyC0 : y ∈ C0 := (Finset.mem_sdiff.mp hyC).1
    have hxX0 : x ∈ X0 := (Finset.filter_subset _ _) hxC0
    have hyX0 : y ∈ X0 := (Finset.filter_subset _ _) hyC0
    apply uniformProbability_oneStateValue_collision_le_general
      G W U0 D1 M k K nD state x y c theta outerCenter outerRadius
      hnD hhalf hD1 hWU0 hpair huniform hk haway hstate
      (hX0M hxX0) (hX0M hyX0) (hstateAway x hxC) (hstateAway y hyC) hxy
      (Finset.mem_filter.mp hxC0).2 (Finset.mem_filter.mp hyC0).2
      (hdiversityScale.trans (hdiverse x hxX0 y hyX0 hxy))
      hc0 hc1 htheta hK hsmall hselected hunselected
  have hdegree : ∀ x ∈ C,
      uniformProbability (innerDegreeBad G D1 nD innerDeviation x) ≤
        pDegree := by
    intro x hxC
    exact uniformProbability_innerDegreeBad_le G D1 x nD K innerDeviation
      hnD hhalf hK ((huniform x (hCM hxC)).le.trans hk) hinnerDeviation
  have hratio : (nD : Real) / D1.card = 1 / 2 := by
    rw [hhalf]
    push_cast
    field_simp
  have hwindow : ∀ omega : BoolSlice D1 nD, ∀ x ∈ C,
      ¬ innerDegreeBad G D1 nD innerDeviation x omega ->
      |(oneStateValue G W U0
          (AugmentationGraphPartial.sampleFinset D1 nD omega) state x : Real) -
          fixedStateSmallNZCenter G W U0 state wCenter d0 outerCenter
            (AugmentationGraphPartial.sampleFinset D1 nD omega)| ≤
        generalSmallNZRadius K nZ nD D1
          wDeviation innerDeviation outerRadius := by
    intro omega x hxC hxGood
    have hbase := oneStateValue_mem_generalSmallNZWindow G W U0 D1 M
      k K nD nZ d0 state x wCenter wDeviation outerCenter outerRadius
      innerDeviation hnZ hD1 hWU0 hpair huniform hk haway hstate
      hstateCard (hCM hxC) (hstateAway x hxC) (hUdegree x (hCM hxC))
      (hWdegree x (hCM hxC))
      (Finset.mem_filter.mp (Finset.mem_sdiff.mp hxC).1).2 omega hxGood
    simpa [generalSmallNZCenter, fixedStateSmallNZCenter, hratio] using hbase
  have hpCollision : 0 ≤ pCollision := by
    dsimp only [pCollision]
    apply div_nonneg
    · exact (AntiConcentration.variancePointMassConstant_pos hc0
        (by positivity) (by omega)).le
    · positivity
  have hpDegree : 0 ≤ pDegree := by
    dsimp only [pDegree, innerLinearFailure]
    positivity
  have hchoose : ((C.card.choose 2 : Nat) : Real) ≤ (s0 : Real) ^ 2 := by
    exact_mod_cast ((Nat.choose_le_pow C.card 2).trans
      (Nat.pow_le_pow_left hCcardUpper 2))
  have hcardReal : (C.card : Real) ≤ s0 := by exact_mod_cast hCcardUpper
  have hriskExact : C.card.choose 2 * pCollision / E +
      C.card * pDegree / tDegree ≤ 2 / 3 := by
    calc
      C.card.choose 2 * pCollision / E + C.card * pDegree / tDegree ≤
          (s0 : Real) ^ 2 * pCollision / E +
            s0 * pDegree / tDegree := by
        apply add_le_add
        · exact div_le_div_of_nonneg_right
            (mul_le_mul_of_nonneg_right hchoose hpCollision) hE.le
        · exact div_le_div_of_nonneg_right
            (mul_le_mul_of_nonneg_right hcardReal hpDegree) htDegree.le
      _ ≤ 2 / 3 := by simpa [pCollision, pDegree] using hrisk
  have hbadDegreeC : badDegree < C.card := hgoodLower.trans_le hCcardLower
  have hpieceExact : piece * (C.card + 2 * edgeBudget) ≤
      (C.card - badDegree) ^ 2 := by
    calc
      piece * (C.card + 2 * edgeBudget) ≤
          piece * (s0 + 2 * edgeBudget) := by
            exact Nat.mul_le_mul_left piece
              (Nat.add_le_add_right hCcardUpper _)
      _ ≤ (s0 - outerBad - (nZ - 1) - badDegree) ^ 2 := hpiece
      _ ≤ (C.card - badDegree) ^ 2 := by
        exact Nat.pow_le_pow_left
          (Nat.sub_le_sub_right hCcardLower badDegree) 2
  have hmain := one_third_le_layerProbability_innerWindowGood_oneState
    G W U0 D1 M C state nD (nZ - 1) L
      (generalSmallNZRadius K nZ nD D1
        wDeviation innerDeviation outerRadius)
      pCollision pDegree E tDegree
      (fixedStateSmallNZCenter G W U0 state wCenter d0 outerCenter)
      edgeBudget badDegree piece hhalf hCM hstate hstateCard hstateAway
      hcollision (innerDegreeBad G D1 nD innerDeviation) hdegree hwindow
      hE htDegree hriskExact hEbudget htDegreeBudget hbadDegreeC
      hpieceExact hpiecePos hL
  simpa [Nat.sub_add_cancel hnZ] using hmain

end

end AugmentationSmallNZ
end Erdos636
