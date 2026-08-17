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

import ErdosProblems.Erdos636.CommonNeighborhood
import ErdosProblems.Erdos636.HypergraphThinning
import ErdosProblems.Erdos636.RichnessBridge
import ErdosProblems.Erdos636.SetDiversity
import ErdosProblems.Erdos636.Sunflower
import ErdosProblems.Erdos636.Turan

/-!
# The structural interface for Erdős Problem 636

This file fixes the exact finite object passed from the rich-graph argument
to the augmentation and switching arguments.  Neighbourhood unions are
counted with multiplicity: this is the formulation for which deleting the
core of a sunflower preserves all degree differences.

The final theorem in this file is the deterministic diversity thinning step.
Starting from a disjoint uniform family whose members have large common
neighbourhoods, corrected richness and a Turán argument produce a large
subfamily whose pairwise incidence-difference mass is large.
-/

open Classical SimpleGraph

namespace Erdos636

universe u

noncomputable section

variable {V : Type u} [Fintype V] [DecidableEq V]

/-- A fixed uniformity for which the sunflower exponent beats the combined
degree-fibre and diversity losses: `(64 - 3) / 64 > 3/4 + 1/5`. -/
def structuralUniformity : ℕ := 64

@[simp] lemma structuralUniformity_pos : 0 < structuralUniformity := by
  decide

/-! ## The polynomial family of persistence tests -/

/-- All vertex sets of cardinality at most `K`.  Persistence is only needed
for pairs from this family, so a union bound has polynomial rather than
exponential size. -/
def boundedVertexSets (K : ℕ) : Finset (Finset V) :=
  Finset.univ.powerset.filter fun X ↦ X.card ≤ K

@[simp] lemma mem_boundedVertexSets {K : ℕ} {X : Finset V} :
    X ∈ boundedVertexSets (V := V) K ↔ X.card ≤ K := by
  simp [boundedVertexSets]

/-- Coarse polynomial count for the bounded sets used as persistence tests. -/
lemma card_boundedVertexSets_le (K : ℕ) [Nonempty V] :
    (boundedVertexSets (V := V) K).card ≤
      (K + 1) * Fintype.card V ^ K := by
  let layers : Finset (Finset V) :=
    (Finset.range (K + 1)).biUnion fun q ↦ Finset.univ.powersetCard q
  have heq : boundedVertexSets (V := V) K = layers := by
    ext X
    simp only [boundedVertexSets, Finset.mem_filter, Finset.mem_powerset,
      Finset.subset_univ, true_and, layers, Finset.mem_biUnion,
      Finset.mem_range, Finset.mem_powersetCard]
    constructor
    · intro hX
      exact ⟨X.card, by omega, rfl⟩
    · rintro ⟨q, hq, hcard⟩
      omega
  rw [heq]
  calc
    layers.card ≤ ∑ q ∈ Finset.range (K + 1),
        (Finset.univ.powersetCard q).card := Finset.card_biUnion_le
    _ = ∑ q ∈ Finset.range (K + 1), (Fintype.card V).choose q := by
      apply Finset.sum_congr rfl
      intro q _hq
      simp
    _ ≤ ∑ _q ∈ Finset.range (K + 1), Fintype.card V ^ K := by
      apply Finset.sum_le_sum
      intro q hq
      have hqK : q ≤ K := by
        simp only [Finset.mem_range] at hq
        omega
      exact (Nat.choose_le_pow _ _).trans
        (Nat.pow_le_pow_right (Fintype.card_pos) hqK)
    _ = (K + 1) * Fintype.card V ^ K := by
      simp [Nat.mul_comm]

/-- Ordered pairs of bounded vertex sets; this is the test index set in the
simultaneous first-exposure lemma. -/
def boundedSetPairs (K : ℕ) : Finset (Finset V × Finset V) :=
  boundedVertexSets (V := V) K ×ˢ boundedVertexSets (V := V) K

@[simp] lemma mem_boundedSetPairs {K : ℕ} {p : Finset V × Finset V} :
    p ∈ boundedSetPairs (V := V) K ↔ p.1.card ≤ K ∧ p.2.card ≤ K := by
  simp [boundedSetPairs]

lemma card_boundedSetPairs_le (K : ℕ) [Nonempty V] :
    (boundedSetPairs (V := V) K).card ≤
      ((K + 1) * Fintype.card V ^ K) ^ 2 := by
  rw [boundedSetPairs, Finset.card_product, pow_two]
  exact Nat.mul_le_mul (card_boundedVertexSets_le K)
    (card_boundedVertexSets_le K)

/-- The bounded pairs whose ambient support is large enough to require
persistence under the first and (if needed) second random exposure. -/
def supportPersistenceTests (G : SimpleGraph V) (K : ℕ) (t : ℝ) :
    Finset (Finset V × Finset V) :=
  (boundedSetPairs (V := V) K).filter fun p ↦
    t ≤ supportDiffCard G Finset.univ p.1 p.2

lemma card_supportPersistenceTests_le (G : SimpleGraph V) (K : ℕ)
    (t : ℝ) [Nonempty V] :
    (supportPersistenceTests G K t).card ≤
      ((K + 1) * Fintype.card V ^ K) ^ 2 := by
  exact (Finset.card_le_card (Finset.filter_subset _ _)).trans
    (card_boundedSetPairs_le K)

@[simp] lemma mem_supportPersistenceTests {G : SimpleGraph V} {K : ℕ}
    {t : ℝ} {p : Finset V × Finset V} :
    p ∈ supportPersistenceTests G K t ↔
      p.1.card ≤ K ∧ p.2.card ≤ K ∧
        t ≤ supportDiffCard G Finset.univ p.1 p.2 := by
  simp [supportPersistenceTests, and_assoc]

/-- Rounded thresholds for the common-neighbourhood induction.  The ceiling
is important: membership at level `q` then implies the real lower bound
`ε^q |V|` needed to invoke richness. -/
def ksCommonThreshold (ε : ℝ) (q : ℕ) : ℕ :=
  ⌈ε ^ q * Fintype.card V⌉₊

/-- Corrected richness bounds the number of ordered tuples with a small
common neighbourhood.  This is the finite form of the first deterministic
counting step in Kwan--Sudakov's structural lemma. -/
theorem card_badOrderedTuples_ksCommonThreshold_le
    {G : SimpleGraph V} {δ ε : ℝ} {k : ℕ}
    (hk : 1 ≤ k) (hε0 : 0 < ε) (hε1 : ε ≤ 1)
    (hδpow : δ ≤ ε ^ (k - 1))
    (hrich : KwanSudakovRich G δ ε) :
    (badOrderedTuples
      (HasLargeCommonNeighborhood G (ksCommonThreshold (V := V) ε)) k).card ≤
      k * Fintype.card V ^ (k - 1) *
        ⌈(Fintype.card V : ℝ) ^ (1 / 5 : ℝ)⌉₊ := by
  simp only [badOrderedTuples, HasLargeCommonNeighborhood, not_le]
  apply card_orderedTuples_small_commonNeighbors_le
    G (ksCommonThreshold (V := V) ε) k
      ⌈(Fintype.card V : ℝ) ^ (1 / 5 : ℝ)⌉₊ hk
  · simp [ksCommonThreshold]
  · intro q hq x hx
    let W : Finset V := commonNeighbors G x
    have hqle : q ≤ k - 1 := by omega
    have hpowmono : ε ^ (k - 1) ≤ ε ^ q :=
      pow_le_pow_of_le_one hε0.le hε1 hqle
    have hthresholdReal :
        ε ^ q * Fintype.card V ≤ (ksCommonThreshold (V := V) ε q : ℕ) := by
      exact Nat.le_ceil _
    have hWreal : ε ^ q * Fintype.card V ≤ (W.card : ℝ) := by
      exact hthresholdReal.trans (by exact_mod_cast hx)
    have hWlarge : δ * Fintype.card V ≤ W.card := by
      calc
        δ * (Fintype.card V : ℝ) ≤
            ε ^ (k - 1) * Fintype.card V := by
          gcongr
        _ ≤ ε ^ q * Fintype.card V := by gcongr
        _ ≤ W.card := hWreal
    have hsub :
        (Finset.univ.filter fun v : V ↦
          (Erdos88.neighborsIn G v W).card <
            ksCommonThreshold (V := V) ε (q + 1)) ⊆
          strictExceptionalVertices G W ε := by
      intro v hv
      have hvltNat := (Finset.mem_filter.mp hv).2
      have hvlt :
          ((Erdos88.neighborsIn G v W).card : ℝ) <
            ε ^ (q + 1) * Fintype.card V := by
        exact Nat.lt_ceil.mp hvltNat
      have hnext : ε ^ (q + 1) * Fintype.card V ≤ ε * W.card := by
        rw [pow_succ]
        nlinarith
      exact mem_strictExceptionalVertices.mpr (Or.inl (hvlt.trans_le hnext))
    have hcardNat :
        (Finset.univ.filter fun v : V ↦
          (Erdos88.neighborsIn G v W).card <
            ksCommonThreshold (V := V) ε (q + 1)).card ≤
          ⌈(Fintype.card V : ℝ) ^ (1 / 5 : ℝ)⌉₊ := by
      have hsubReal :
          ((Finset.univ.filter fun v : V ↦
            (Erdos88.neighborsIn G v W).card <
              ksCommonThreshold (V := V) ε (q + 1)).card : ℝ) ≤
            (strictExceptionalVertices G W ε).card := by
        exact_mod_cast Finset.card_le_card hsub
      have hreal := hsubReal.trans (hrich W hWlarge)
      have hceil :
          (Fintype.card V : ℝ) ^ (1 / 5 : ℝ) ≤
            ((⌈(Fintype.card V : ℝ) ^ (1 / 5 : ℝ)⌉₊ : ℕ) : ℝ) :=
        Nat.le_ceil _
      exact_mod_cast hreal.trans hceil
    simpa [W, commonNeighbors_cons] using hcardNat

/-- The sum, over the vertices of `x`, of their degrees into `U`. -/
def degreeInto (G : SimpleGraph V) (U x : Finset V) : ℕ :=
  ∑ v ∈ x, (Erdos88.neighborsIn G v U).card

lemma degreeInto_sdiff_add (G : SimpleGraph V) (U : Finset V)
    {C X : Finset V} (hCX : C ⊆ X) :
    degreeInto G U (X \ C) + degreeInto G U C = degreeInto G U X := by
  exact Finset.sum_sdiff hCX

lemma degreeInto_le_card_mul_card (G : SimpleGraph V) (U X : Finset V) :
    degreeInto G U X ≤ X.card * U.card := by
  calc
    degreeInto G U X ≤ ∑ _x ∈ X, U.card := by
      apply Finset.sum_le_sum
      intro x _hx
      apply Finset.card_le_card
      intro y hy
      exact (Erdos88.mem_neighborsIn.mp hy).1
    _ = X.card * U.card := by simp

/-- The number of ordered incidences from `A` into `B`.  When `A` and `B`
are disjoint this is the ordinary number of edges between them. -/
def crossEdges (G : SimpleGraph V) (A B : Finset V) : ℕ :=
  degreeInto G B A

/-- The weighted score used to choose the two switching endpoints. -/
def weightedScore (G : SimpleGraph V) (α : ℝ) (U W : Finset V) : ℝ :=
  Erdos88.inducedEdges G W + α * crossEdges G U W

/-- Forget the subtype proof on a finite vertex set of an induced graph. -/
def liftInducedFinset {U : Finset V} (S : Finset U) : Finset V :=
  S.image Subtype.val

@[simp] lemma mem_liftInducedFinset {U : Finset V} {S : Finset U} {v : V} :
    v ∈ liftInducedFinset S ↔ ∃ u ∈ S, (u : V) = v := by
  simp [liftInducedFinset]

@[simp] lemma card_liftInducedFinset {U : Finset V} (S : Finset U) :
    (liftInducedFinset S).card = S.card := by
  exact Finset.card_image_of_injective S Subtype.val_injective

lemma liftInducedFinset_union {U : Finset V} (S T : Finset U) :
    liftInducedFinset (S ∪ T) = liftInducedFinset S ∪ liftInducedFinset T := by
  exact Finset.image_union S T

lemma disjoint_liftInducedFinset {U : Finset V} {S T : Finset U} :
    Disjoint (liftInducedFinset S) (liftInducedFinset T) ↔ Disjoint S T := by
  simpa only [liftInducedFinset] using
    (Finset.disjoint_image (s := S) (t := T) Subtype.val_injective)

lemma degreeInto_liftInducedFinset {G : SimpleGraph V} {U : Finset V}
    (A X : Finset U) :
    degreeInto G (liftInducedFinset A) (liftInducedFinset X) =
      degreeInto (G.induce (U : Set V)) A X := by
  simp only [degreeInto, liftInducedFinset]
  rw [Finset.sum_image (s := X) (g := Subtype.val)
    Subtype.val_injective.injOn]
  apply Finset.sum_congr rfl
  intro x _hx
  change
    (Erdos88.neighborsIn G x.1 (A.image Subtype.val)).card =
      (Erdos88.neighborsIn (G.induce (U : Set V)) x A).card
  exact (Erdos88.card_neighborsIn_induce (G := G) x A).symm

lemma crossEdges_liftInducedFinset {G : SimpleGraph V} {U : Finset V}
    (A B : Finset U) :
    crossEdges G (liftInducedFinset A) (liftInducedFinset B) =
      crossEdges (G.induce (U : Set V)) A B :=
  degreeInto_liftInducedFinset B A

/-- The vertex equivalence underlying the twice-induced/ambient-induced
graph isomorphism. -/
def liftInducedSubtypeEquiv {U : Finset V} (S : Finset U) :
    {x // x ∈ S} ≃ {v // v ∈ liftInducedFinset S} :=
  Equiv.ofBijective
    (fun x ↦ ⟨(x.1.1 : V), mem_liftInducedFinset.mpr ⟨x.1, x.2, rfl⟩⟩)
    ⟨by
      intro x y h
      have hamb : (x.1.1 : V) = y.1.1 :=
        congrArg (fun z : {v // v ∈ liftInducedFinset S} ↦ z.1) h
      exact Subtype.ext (Subtype.ext hamb),
    by
      intro v
      obtain ⟨u, huS, huv⟩ := mem_liftInducedFinset.mp v.2
      refine ⟨⟨u, huS⟩, ?_⟩
      apply Subtype.ext
      exact huv⟩

/-- Inducing first on `U` and then on `S` is isomorphic to inducing the
ambient graph on the lifted copy of `S`. -/
def inducedLiftIso (G : SimpleGraph V) {U : Finset V} (S : Finset U) :
    (G.induce (U : Set V)).induce (S : Set U) ≃g
      G.induce (liftInducedFinset S : Set V) where
  toEquiv := liftInducedSubtypeEquiv S
  map_rel_iff' := by
    intro x y
    rfl

lemma inducedEdges_liftInducedFinset {G : SimpleGraph V} {U : Finset V}
    (S : Finset U) :
    Erdos88.inducedEdges G (liftInducedFinset S) =
      Erdos88.inducedEdges (G.induce (U : Set V)) S := by
  classical
  rw [Erdos88.inducedEdges_eq_card_edgeFinset_induce,
    Erdos88.inducedEdges_eq_card_edgeFinset_induce]
  exact (inducedLiftIso G S).card_edgeFinset_eq.symm

lemma weightedScore_liftInducedFinset {G : SimpleGraph V} {U : Finset V}
    (α : ℝ) (A W : Finset U) :
    weightedScore G α (liftInducedFinset A) (liftInducedFinset W) =
      weightedScore (G.induce (U : Set V)) α A W := by
  simp [weightedScore, inducedEdges_liftInducedFinset,
    crossEdges_liftInducedFinset]

lemma incidence_liftInducedFinset {G : SimpleGraph V} {U : Finset V}
    (X : Finset U) (u : U) :
    incidence G (liftInducedFinset X) u.1 =
      incidence (G.induce (U : Set V)) X u := by
  simp only [incidence, liftInducedFinset]
  rw [Finset.filter_image]
  rw [Finset.card_image_of_injective _ Subtype.val_injective]
  congr 1

lemma incidenceDiffTerm_liftInducedFinset {G : SimpleGraph V} {U : Finset V}
    (X Y : Finset U) (u : U) :
    incidenceDiffTerm G (liftInducedFinset X) (liftInducedFinset Y) u.1 =
      incidenceDiffTerm (G.induce (U : Set V)) X Y u := by
  simp [incidenceDiffTerm, incidence_liftInducedFinset]

lemma incidenceDiffMass_liftInducedFinset {G : SimpleGraph V} {U : Finset V}
    (A X Y : Finset U) :
    incidenceDiffMass G (liftInducedFinset A)
        (liftInducedFinset X) (liftInducedFinset Y) =
      incidenceDiffMass (G.induce (U : Set V)) A X Y := by
  simp only [incidenceDiffMass, liftInducedFinset]
  rw [Finset.sum_image (s := A) (g := Subtype.val)
    Subtype.val_injective.injOn]
  apply Finset.sum_congr rfl
  intro u _hu
  exact incidenceDiffTerm_liftInducedFinset X Y u

/-- A finite Kwan--Sudakov structural witness.

`scale` is the order of the original Ramsey graph (rather than necessarily
the order of the rich induced subgraph).  The family `matching` consists of
pairwise-disjoint `k`-sets and is the object later sampled by augmentation.
-/
structure StructuralWitness (G : SimpleGraph V) (scale nW ell K : ℕ)
    (α aDisc aDiv b : ℝ) where
  k : ℕ
  Wminus : Finset V
  Wplus : Finset V
  U0 : Finset V
  matching : Finset (Finset V)
  k_pos : 1 ≤ k
  k_le : k ≤ K
  disjoint_Wminus_Wplus : Disjoint Wminus Wplus
  disjoint_Wminus_U0 : Disjoint Wminus U0
  disjoint_Wplus_U0 : Disjoint Wplus U0
  matching_pairwiseDisjoint :
    (matching : Set (Finset V)).PairwiseDisjoint id
  matching_away : ∀ x ∈ matching,
    Disjoint x (Wminus ∪ Wplus ∪ U0)
  card_Wminus : Wminus.card = nW
  card_Wplus : Wplus.card = nW
  card_U0 : U0.card = ell ∨ U0.card = 2 * ell
  matching_uniform : ∀ x ∈ matching, x.card = k
  matching_large :
    b * (scale : ℝ) ^ (3 / 4 : ℝ) ≤ matching.card
  discrepancy :
    aDisc * scale * Real.sqrt scale ≤
      weightedScore G α U0 Wplus - weightedScore G α U0 Wminus
  dMinus : ℕ
  dPlus : ℕ
  d0 : ℕ
  degree_Wminus : ∀ x ∈ matching, degreeInto G Wminus x = dMinus
  degree_Wplus : ∀ x ∈ matching, degreeInto G Wplus x = dPlus
  degree_U0 : ∀ x ∈ matching, degreeInto G U0 x = d0
  diverse : ∀ x ∈ matching, ∀ y ∈ matching, x ≠ y →
    aDiv * scale ≤ incidenceDiffMass G U0 x y

/-- Lift a family of finite sets out of an induced vertex subtype. -/
def liftInducedFamily {U : Finset V} (M : Finset (Finset U)) :
    Finset (Finset V) :=
  M.image liftInducedFinset

lemma liftInducedFinset_injective {U : Finset V} :
    Function.Injective (liftInducedFinset (V := V) (U := U)) := by
  intro S T h
  exact (Finset.image_inj Subtype.val_injective).mp h

@[simp] lemma card_liftInducedFamily {U : Finset V}
    (M : Finset (Finset U)) :
    (liftInducedFamily M).card = M.card := by
  exact Finset.card_image_of_injective M liftInducedFinset_injective

/-- A structural witness inside an induced graph lifts without any loss to
the ambient graph.  In particular, the external scale and all four
quantitative constants remain unchanged. -/
def StructuralWitness.liftInduce {G : SimpleGraph V} {U : Finset V}
    {scale nW ell K : ℕ} {α aDisc aDiv b : ℝ}
    (S : StructuralWitness (G.induce (U : Set V))
      scale nW ell K α aDisc aDiv b) :
    StructuralWitness G scale nW ell K α aDisc aDiv b where
  k := S.k
  Wminus := liftInducedFinset S.Wminus
  Wplus := liftInducedFinset S.Wplus
  U0 := liftInducedFinset S.U0
  matching := liftInducedFamily S.matching
  k_pos := S.k_pos
  k_le := S.k_le
  disjoint_Wminus_Wplus :=
    disjoint_liftInducedFinset.mpr S.disjoint_Wminus_Wplus
  disjoint_Wminus_U0 :=
    disjoint_liftInducedFinset.mpr S.disjoint_Wminus_U0
  disjoint_Wplus_U0 :=
    disjoint_liftInducedFinset.mpr S.disjoint_Wplus_U0
  matching_pairwiseDisjoint := by
    intro X hX Y hY hXY
    obtain ⟨x, hxM, rfl⟩ := Finset.mem_image.mp hX
    obtain ⟨y, hyM, rfl⟩ := Finset.mem_image.mp hY
    apply disjoint_liftInducedFinset.mpr
    apply S.matching_pairwiseDisjoint hxM hyM
    intro hxy
    exact hXY (congrArg liftInducedFinset hxy)
  matching_away := by
    intro X hX
    obtain ⟨x, hxM, rfl⟩ := Finset.mem_image.mp hX
    rw [← liftInducedFinset_union, ← liftInducedFinset_union]
    exact disjoint_liftInducedFinset.mpr (S.matching_away x hxM)
  card_Wminus := (card_liftInducedFinset S.Wminus).trans S.card_Wminus
  card_Wplus := (card_liftInducedFinset S.Wplus).trans S.card_Wplus
  card_U0 := by
    rw [card_liftInducedFinset]
    exact S.card_U0
  matching_uniform := by
    intro X hX
    obtain ⟨x, hxM, rfl⟩ := Finset.mem_image.mp hX
    exact (card_liftInducedFinset x).trans (S.matching_uniform x hxM)
  matching_large := by
    rw [card_liftInducedFamily]
    exact S.matching_large
  discrepancy := by
    rw [weightedScore_liftInducedFinset,
      weightedScore_liftInducedFinset]
    exact S.discrepancy
  dMinus := S.dMinus
  dPlus := S.dPlus
  d0 := S.d0
  degree_Wminus := by
    intro X hX
    obtain ⟨x, hxM, rfl⟩ := Finset.mem_image.mp hX
    exact (degreeInto_liftInducedFinset S.Wminus x).trans
      (S.degree_Wminus x hxM)
  degree_Wplus := by
    intro X hX
    obtain ⟨x, hxM, rfl⟩ := Finset.mem_image.mp hX
    exact (degreeInto_liftInducedFinset S.Wplus x).trans
      (S.degree_Wplus x hxM)
  degree_U0 := by
    intro X hX
    obtain ⟨x, hxM, rfl⟩ := Finset.mem_image.mp hX
    exact (degreeInto_liftInducedFinset S.U0 x).trans
      (S.degree_U0 x hxM)
  diverse := by
    intro X hX Y hY hXY
    obtain ⟨x, hxM, rfl⟩ := Finset.mem_image.mp hX
    obtain ⟨y, hyM, rfl⟩ := Finset.mem_image.mp hY
    rw [incidenceDiffMass_liftInducedFinset]
    apply S.diverse x hxM y hyM
    intro hxy
    exact hXY (congrArg liftInducedFinset hxy)

/-- Nonempty transport form used after extracting a rich induced subgraph. -/
theorem nonempty_structuralWitness_liftInduce {G : SimpleGraph V}
    {U : Finset V} {scale nW ell K : ℕ} {α aDisc aDiv b : ℝ}
    (h : Nonempty (StructuralWitness (G.induce (U : Set V))
      scale nW ell K α aDisc aDiv b)) :
    Nonempty (StructuralWitness G scale nW ell K α aDisc aDiv b) := by
  obtain ⟨S⟩ := h
  exact ⟨S.liftInduce⟩

/-- The union of all matching edges in a structural witness. -/
def StructuralWitness.A {G : SimpleGraph V} {scale nW ell K : ℕ}
    {α aDisc aDiv b : ℝ}
    (S : StructuralWitness G scale nW ell K α aDisc aDiv b) : Finset V :=
  S.matching.biUnion id

lemma StructuralWitness.card_A_eq_mul {G : SimpleGraph V}
    {scale nW ell K : ℕ} {α aDisc aDiv b : ℝ}
    (S : StructuralWitness G scale nW ell K α aDisc aDiv b) :
    S.A.card = S.matching.card * S.k := by
  rw [StructuralWitness.A]
  rw [Finset.card_biUnion S.matching_pairwiseDisjoint]
  exact Finset.sum_const_nat S.matching_uniform

lemma StructuralWitness.disjoint_A_base {G : SimpleGraph V}
    {scale nW ell K : ℕ} {α aDisc aDiv b : ℝ}
    (S : StructuralWitness G scale nW ell K α aDisc aDiv b) :
    Disjoint S.A (S.Wminus ∪ S.Wplus ∪ S.U0) := by
  rw [Finset.disjoint_left]
  intro v hvA hvbase
  obtain ⟨x, hxM, hvx⟩ := Finset.mem_biUnion.mp hvA
  exact Finset.disjoint_left.mp (S.matching_away x hxM) hvx hvbase

/-- The symmetry of multiset-incidence difference. -/
lemma incidenceDiffTerm_comm (G : SimpleGraph V) (x y : Finset V) (u : V) :
    incidenceDiffTerm G x y u = incidenceDiffTerm G y x u := by
  rw [incidenceDiffTerm, incidenceDiffTerm]
  have hneg :
      (incidence G y u : ℤ) - incidence G x u =
        -((incidence G x u : ℤ) - incidence G y u) := by ring
  rw [hneg, Int.natAbs_neg]

lemma incidenceDiffMass_comm (G : SimpleGraph V) (A x y : Finset V) :
    incidenceDiffMass G A x y = incidenceDiffMass G A y x := by
  simp only [incidenceDiffMass]
  apply Finset.sum_congr rfl
  intro u _hu
  exact incidenceDiffTerm_comm G x y u

/-- Symmetry of the paper's incidence-difference support. -/
lemma supportDiffCard_comm (G : SimpleGraph V) (A x y : Finset V) :
    supportDiffCard G A x y = supportDiffCard G A y x := by
  rw [supportDiffCard, supportDiffCard]
  congr 1
  ext u
  simp only [mem_supportDiff]
  tauto

/-- Restricting incidence-difference support is literal intersection with
the ambient support. -/
lemma supportDiff_eq_inter_univ (G : SimpleGraph V) (A x y : Finset V) :
    supportDiff G A x y = A ∩ supportDiff G Finset.univ x y := by
  ext u
  simp only [mem_supportDiff, Finset.mem_inter, Finset.mem_univ, true_and]

lemma supportDiffCard_eq_card_inter_univ
    (G : SimpleGraph V) (A x y : Finset V) :
    supportDiffCard G A x y =
      (A ∩ supportDiff G Finset.univ x y).card := by
  rw [supportDiffCard, supportDiff_eq_inter_univ]

lemma incidenceDiffMass_mono (G : SimpleGraph V) {A B x y : Finset V}
    (hAB : A ⊆ B) :
    incidenceDiffMass G A x y ≤ incidenceDiffMass G B x y := by
  exact Finset.sum_le_sum_of_subset hAB

/-- The graph of pairs whose incidence-difference mass is too small. -/
def lowDiversityGraph (G : SimpleGraph V) (U : Finset V) (t : ℝ)
    (P : Finset (Finset V)) : SimpleGraph {x // x ∈ P} :=
  SimpleGraph.mk
    (fun x y ↦ x ≠ y ∧ (incidenceDiffMass G U x y : ℝ) < t)
    (symm := ⟨by
        intro x y h
        refine ⟨Ne.symm h.1, ?_⟩
        rw [incidenceDiffMass_comm G U y x]
        exact h.2⟩)
    (loopless := ⟨by intro x h; exact h.1 rfl⟩)

@[simp] lemma lowDiversityGraph_adj {G : SimpleGraph V} {U : Finset V}
    {t : ℝ} {P : Finset (Finset V)} {x y : {x // x ∈ P}} :
    (lowDiversityGraph G U t P).Adj x y ↔
      x ≠ y ∧ (incidenceDiffMass G U x y : ℝ) < t :=
  by simp [lowDiversityGraph]

/-- A corrected-richness bound whose threshold is half that of the strict
Kwan--Sudakov predicate.  Halving resolves the strict/non-strict endpoint. -/
lemma correctedRichWithBound_of_kwanSudakovRich
    [Nonempty V] {G : SimpleGraph V} {δ ε : ℝ}
    (hδ : 0 < δ) (hε : 0 < ε) (hrich : KwanSudakovRich G δ ε) :
    CorrectedRichWithBound G δ (ε / 2)
      ⌈(Fintype.card V : ℝ) ^ (1 / 5 : ℝ)⌉₊ := by
  intro W hW
  have hmpos : 0 < Fintype.card V := Fintype.card_pos
  have hWposReal : 0 < (W.card : ℝ) := by
    have hmposReal : (0 : ℝ) < Fintype.card V := by exact_mod_cast hmpos
    have : 0 < δ * (Fintype.card V : ℝ) := mul_pos hδ hmposReal
    exact this.trans_le hW
  have hsub : Erdos88.exceptionalVertices G W (ε / 2) ⊆
      strictExceptionalVertices G W ε := by
    intro v hv
    simp only [Erdos88.mem_exceptionalVertices] at hv
    simp only [mem_strictExceptionalVertices]
    rcases hv with hv | hv
    · left
      calc
        ((Erdos88.neighborsIn G v W).card : ℝ) ≤ (ε / 2) * W.card := hv
        _ < ε * W.card := by nlinarith
    · right
      calc
        (((W \ Erdos88.neighborsIn G v W).card : ℕ) : ℝ) ≤
            (ε / 2) * W.card := hv
        _ < ε * W.card := by nlinarith
  have hcardReal :
      ((Erdos88.exceptionalVertices G W (ε / 2)).card : ℝ) ≤
        (Fintype.card V : ℝ) ^ (1 / 5 : ℝ) := by
    have hcast :
        ((Erdos88.exceptionalVertices G W (ε / 2)).card : ℝ) ≤
          (strictExceptionalVertices G W ε).card := by
      exact_mod_cast Finset.card_le_card hsub
    exact hcast.trans (hrich W hW)
  have hceil :
      (Fintype.card V : ℝ) ^ (1 / 5 : ℝ) ≤
        ((⌈(Fintype.card V : ℝ) ^ (1 / 5 : ℝ)⌉₊ : ℕ) : ℝ) := Nat.le_ceil _
  exact_mod_cast hcardReal.trans hceil

/-- A single low-diversity neighbourhood in a uniform matching is bounded
by corrected richness.  This is the local input required by the generic
sunflower/Turán thinning theorem. -/
theorem card_filter_lowDiversity_le
    {G : SimpleGraph V} {δ ρ : ℝ} {b k : ℕ}
    {P : Finset (Finset V)} {x : Finset V}
    (hrich : CorrectedRichWithBound G δ ρ b)
    (hρ : 0 ≤ ρ) (hk : 0 < k)
    (hxP : x ∈ P)
    (huniform : ∀ y ∈ P, y.card = k)
    (hPdisjoint : (P : Set (Finset V)).PairwiseDisjoint id)
    (hcommon : ∀ y ∈ P,
      δ * Fintype.card V ≤ (Erdos88.commonNeighborFinset G y).card) :
    (P.filter fun y ↦ x ≠ y ∧
      (incidenceDiffMass G Finset.univ x y : ℝ) <
        δ * ρ * Fintype.card V).card ≤ b := by
  let Y := P.filter fun y ↦ x ≠ y ∧
    (incidenceDiffMass G Finset.univ x y : ℝ) <
      δ * ρ * Fintype.card V
  have hYsub : Y ⊆ P := Finset.filter_subset _ _
  have hYuniform : ∀ y ∈ Y, y.card = k :=
    fun y hy ↦ huniform y (hYsub hy)
  have hYbase : ∀ y ∈ Y, Disjoint x y := by
    intro y hy
    have hxy := (Finset.mem_filter.mp hy).2.1
    exact hPdisjoint hxP (hYsub hy) hxy
  have hYpairwise : (Y : Set (Finset V)).PairwiseDisjoint id := by
    intro y hy z hz hyz
    exact hPdisjoint (hYsub hy) (hYsub hz) hyz
  have hYmass : ∀ y ∈ Y,
      (incidenceDiffMass G (Erdos88.commonNeighborFinset G x) x y : ℝ) <
        δ * ρ * Fintype.card V := by
    intro y hy
    have hmonoNat := incidenceDiffMass_mono G
      (A := Erdos88.commonNeighborFinset G x) (B := Finset.univ)
      (x := x) (y := y) (Finset.subset_univ _)
    have hmono :
        (incidenceDiffMass G (Erdos88.commonNeighborFinset G x) x y : ℝ) ≤
          incidenceDiffMass G Finset.univ x y := by exact_mod_cast hmonoNat
    exact hmono.trans_lt (Finset.mem_filter.mp hy).2.2
  exact setDiversity_of_globalMass_lt
    (W := Erdos88.commonNeighborFinset G x) (x := x) (Y := Y)
    hrich (hcommon x hxP) hρ hk Finset.Subset.rfl (huniform x hxP)
    hYuniform hYbase hYpairwise hYmass

/-- Paper-correct support version of `card_filter_lowDiversity_le`.  It is
this formulation that can subsequently be restricted to a random vertex
sample: a linear ambient support has a linear expected sampled support. -/
theorem card_filter_lowSupportDiversity_le
    {G : SimpleGraph V} {δ ρ : ℝ} {b k : ℕ}
    {P : Finset (Finset V)} {x : Finset V}
    (hrich : CorrectedRichWithBound G δ ρ b)
    (hρ : 0 ≤ ρ) (hk : 0 < k)
    (hxP : x ∈ P)
    (huniform : ∀ y ∈ P, y.card = k)
    (hPdisjoint : (P : Set (Finset V)).PairwiseDisjoint id)
    (hcommon : ∀ y ∈ P,
      δ * Fintype.card V ≤ (Erdos88.commonNeighborFinset G y).card) :
    (P.filter fun y ↦ x ≠ y ∧
      (supportDiffCard G Finset.univ x y : ℝ) <
        δ * ρ * Fintype.card V).card ≤ b := by
  let Y := P.filter fun y ↦ x ≠ y ∧
    (supportDiffCard G Finset.univ x y : ℝ) <
      δ * ρ * Fintype.card V
  have hYsub : Y ⊆ P := Finset.filter_subset _ _
  have hYuniform : ∀ y ∈ Y, y.card = k :=
    fun y hy ↦ huniform y (hYsub hy)
  have hYbase : ∀ y ∈ Y, Disjoint x y := by
    intro y hy
    have hxy := (Finset.mem_filter.mp hy).2.1
    exact hPdisjoint hxP (hYsub hy) hxy
  have hYpairwise : (Y : Set (Finset V)).PairwiseDisjoint id := by
    intro y hy z hz hyz
    exact hPdisjoint (hYsub hy) (hYsub hz) hyz
  have hYsupport : ∀ y ∈ Y,
      (supportDiffCard G (Erdos88.commonNeighborFinset G x) x y : ℝ) <
        δ * ρ * Fintype.card V := by
    intro y hy
    have hsub : supportDiff G (Erdos88.commonNeighborFinset G x) x y ⊆
        supportDiff G Finset.univ x y := by
      intro u hu
      rw [mem_supportDiff] at hu ⊢
      exact ⟨Finset.mem_univ u, hu.2⟩
    have hmono :
        supportDiffCard G (Erdos88.commonNeighborFinset G x) x y ≤
          supportDiffCard G Finset.univ x y := by
      exact Finset.card_le_card hsub
    have hmonoReal :
        (supportDiffCard G (Erdos88.commonNeighborFinset G x) x y : ℝ) ≤
          supportDiffCard G Finset.univ x y := by
      exact_mod_cast hmono
    exact hmonoReal.trans_lt (Finset.mem_filter.mp hy).2.2
  exact setDiversity_support_of_globalCard_lt
    (W := Erdos88.commonNeighborFinset G x) (x := x) (Y := Y)
    hrich (hcommon x hxP) hρ hk Finset.Subset.rfl (huniform x hxP)
    hYuniform hYbase hYpairwise hYsupport

/-- Deterministic richness-to-diversity thinning.

The input family is already a matching.  Each low-diversity neighbourhood in
the auxiliary graph has at most `b` members by `setDiversity`; the coarse
Turán bound therefore retains at least a `1 / (b+1)` fraction. -/
theorem exists_diverse_subfamily
    {G : SimpleGraph V} {δ ρ : ℝ} {b k : ℕ}
    {P : Finset (Finset V)}
    (hrich : CorrectedRichWithBound G δ ρ b)
    (hρ : 0 ≤ ρ) (hk : 0 < k)
    (huniform : ∀ x ∈ P, x.card = k)
    (hPdisjoint : (P : Set (Finset V)).PairwiseDisjoint id)
    (hcommon : ∀ x ∈ P,
      δ * Fintype.card V ≤ (Erdos88.commonNeighborFinset G x).card) :
    ∃ M : Finset (Finset V),
      M ⊆ P ∧
      (M : Set (Finset V)).PairwiseDisjoint id ∧
      (∀ x ∈ M, ∀ y ∈ M, x ≠ y →
        δ * ρ * Fintype.card V ≤ incidenceDiffMass G Finset.univ x y) ∧
      P.card ≤ M.card * (b + 1) := by
  let t : ℝ := δ * ρ * Fintype.card V
  let H : SimpleGraph {x // x ∈ P} :=
    lowDiversityGraph G Finset.univ t P
  letI : DecidableRel H.Adj := Classical.decRel H.Adj
  have hdegree : ∀ x : {x // x ∈ P}, H.degree x ≤ b := by
    intro x
    let Y : Finset (Finset V) := (H.neighborFinset x).image Subtype.val
    have hYcard : Y.card = H.degree x := by
      dsimp [Y]
      rw [Finset.card_image_of_injective _ Subtype.val_injective]
      exact H.card_neighborFinset_eq_degree x
    have hYsub : Y ⊆ P := by
      intro y hy
      obtain ⟨z, _hz, rfl⟩ := Finset.mem_image.mp hy
      exact z.property
    have hYuniform : ∀ y ∈ Y, y.card = k := by
      intro y hy
      exact huniform y (hYsub hy)
    have hYbase : ∀ y ∈ Y, Disjoint x.1 y := by
      intro y hy
      obtain ⟨z, hzN, hzy⟩ := Finset.mem_image.mp hy
      have hadj : H.Adj x z := (H.mem_neighborFinset x z).mp hzN
      have hxz : x ≠ z := H.ne_of_adj hadj
      subst y
      exact hPdisjoint x.property z.property (fun h ↦ hxz (Subtype.ext h))
    have hYpairwise : (Y : Set (Finset V)).PairwiseDisjoint id := by
      intro y hy z hz hyz
      exact hPdisjoint (hYsub hy) (hYsub hz) hyz
    have hYmass : ∀ y ∈ Y,
        (incidenceDiffMass G Finset.univ x y : ℝ) <
          δ * ρ * Fintype.card V := by
      intro y hy
      obtain ⟨z, hzN, hzy⟩ := Finset.mem_image.mp hy
      subst y
      have hadj : H.Adj x z := (H.mem_neighborFinset x z).mp hzN
      have hadj' : (lowDiversityGraph G Finset.univ t P).Adj x z := by
        exact hadj
      simpa [t] using (lowDiversityGraph_adj.mp hadj').2
    have hYmassCommon : ∀ y ∈ Y,
        (incidenceDiffMass G (Erdos88.commonNeighborFinset G x.1) x y : ℝ) <
          δ * ρ * Fintype.card V := by
      intro y hy
      have hmono :
          incidenceDiffMass G (Erdos88.commonNeighborFinset G x.1) x y ≤
            incidenceDiffMass G Finset.univ x y :=
        incidenceDiffMass_mono G (Finset.subset_univ _)
      have hmonoReal :
          (incidenceDiffMass G (Erdos88.commonNeighborFinset G x.1) x y : ℝ) ≤
            incidenceDiffMass G Finset.univ x y := by exact_mod_cast hmono
      exact hmonoReal.trans_lt (hYmass y hy)
    have hbound : Y.card ≤ b :=
      setDiversity_of_globalMass_lt
        (W := Erdos88.commonNeighborFinset G x.1) (x := x.1) (Y := Y)
        hrich (hcommon x.1 x.2) hρ hk (by exact Finset.Subset.rfl)
        (huniform x.1 x.2) hYuniform hYbase hYpairwise hYmassCommon
    rwa [hYcard] at hbound
  have hmax : H.maxDegree ≤ b :=
    H.maxDegree_le_of_forall_degree_le b hdegree
  obtain ⟨S, hSind, hScard⟩ := exists_indepSet_card_mul_maxDegree_add_one H
  let M : Finset (Finset V) := S.image Subtype.val
  have hMcard : M.card = S.card := by
    exact Finset.card_image_of_injective S Subtype.val_injective
  have hMsub : M ⊆ P := by
    intro x hx
    obtain ⟨y, _hyS, rfl⟩ := Finset.mem_image.mp hx
    exact y.property
  have hMpairwise : (M : Set (Finset V)).PairwiseDisjoint id := by
    intro x hx y hy hxy
    exact hPdisjoint (hMsub hx) (hMsub hy) hxy
  have hMdiverse : ∀ x ∈ M, ∀ y ∈ M, x ≠ y →
      δ * ρ * Fintype.card V ≤ incidenceDiffMass G Finset.univ x y := by
    intro x hx y hy hxy
    obtain ⟨sx, hsxS, hsx⟩ := Finset.mem_image.mp hx
    obtain ⟨sy, hsyS, hsy⟩ := Finset.mem_image.mp hy
    subst x
    subst y
    have hsxy : sx ≠ sy := by
      intro h
      exact hxy (congrArg Subtype.val h)
    have hnotAdj : ¬ H.Adj sx sy :=
      (H.isIndepSet_iff.mp hSind) hsxS hsyS hsxy
    by_contra hlt
    have hlt' :
        (incidenceDiffMass G Finset.univ sx sy : ℝ) <
          δ * ρ * Fintype.card V := lt_of_not_ge hlt
    apply hnotAdj
    change (lowDiversityGraph G Finset.univ t P).Adj sx sy
    apply lowDiversityGraph_adj.mpr
    exact ⟨hsxy, by simpa [t] using hlt'⟩
  refine ⟨M, hMsub, hMpairwise, hMdiverse, ?_⟩
  rw [hMcard]
  calc
    P.card = Fintype.card {x // x ∈ P} := by simp
    _ ≤ S.card * (H.maxDegree + 1) := hScard
    _ ≤ S.card * (b + 1) := by gcongr

/-- Direct Kwan--Sudakov-rich form of `exists_diverse_subfamily`.

The surviving family has pairwise global incidence-difference at least
`δ (ε/2) |V|`, and loses only the explicit exceptional-set factor
`ceil (|V|^(1/5)) + 1`. -/
theorem exists_diverse_subfamily_of_kwanSudakovRich
    [Nonempty V] {G : SimpleGraph V} {δ ε : ℝ} {k : ℕ}
    {P : Finset (Finset V)}
    (hδ : 0 < δ) (hε : 0 < ε)
    (hrich : KwanSudakovRich G δ ε)
    (hk : 0 < k)
    (huniform : ∀ x ∈ P, x.card = k)
    (hPdisjoint : (P : Set (Finset V)).PairwiseDisjoint id)
    (hcommon : ∀ x ∈ P,
      δ * Fintype.card V ≤ (Erdos88.commonNeighborFinset G x).card) :
    ∃ M : Finset (Finset V),
      M ⊆ P ∧
      (M : Set (Finset V)).PairwiseDisjoint id ∧
      (∀ x ∈ M, ∀ y ∈ M, x ≠ y →
        δ * (ε / 2) * Fintype.card V ≤
          incidenceDiffMass G Finset.univ x y) ∧
      P.card ≤ M.card *
        (⌈(Fintype.card V : ℝ) ^ (1 / 5 : ℝ)⌉₊ + 1) := by
  exact exists_diverse_subfamily
    (correctedRichWithBound_of_kwanSudakovRich hδ hε hrich)
    (by positivity) hk huniform hPdisjoint hcommon

/-! ## Deterministic completion of the structural package -/

/-- Once the endpoint/reservoir stage has supplied the three base sets and
a sufficiently large family of good `K`-sets away from them, richness,
sunflower thinning, and Turán produce the exact `StructuralWitness` consumed
by augmentation.  All polynomial losses are visible in the hypotheses. -/
theorem structuralWitness_of_candidateFamily
    [Nonempty V] {G : SimpleGraph V}
    {δ ε aDisc aDiv b α : ℝ} {scale nW ell K r : ℕ}
    (hδ : 0 < δ) (hε : 0 < ε)
    (hrich : KwanSudakovRich G δ ε)
    (Wminus Wplus U0 A0 : Finset V)
    (hWmWp : Disjoint Wminus Wplus)
    (hWmU : Disjoint Wminus U0) (hWpU : Disjoint Wplus U0)
    (hAaway : Disjoint A0 (Wminus ∪ Wplus ∪ U0))
    (hWmcard : Wminus.card = nW) (hWpcard : Wplus.card = nW)
    (hUcard : U0.card = ell ∨ U0.card = 2 * ell)
    (hdisc : aDisc * scale * Real.sqrt scale ≤
      weightedScore G α U0 Wplus - weightedScore G α U0 Wminus)
    (candidates : Finset (Finset V))
    (hcandidateSub : ∀ X ∈ candidates, X ⊆ A0)
    (hcandidateUniform : ∀ X ∈ candidates, X.card = K)
    (hcandidateCommon : ∀ X ∈ candidates,
      δ * Fintype.card V ≤ (Erdos88.commonNeighborFinset G X).card)
    (hr : 2 ≤ r)
    (hlarge :
      K.factorial * (r - 1) ^ K *
          (K * Fintype.card V + 1) ^ 3 < candidates.card)
    (hrestrict : ∀ X Y : Finset V,
      X.card ≤ K → Y.card ≤ K →
      δ * (ε / 2) * Fintype.card V ≤
          supportDiffCard G Finset.univ X Y →
        aDiv * scale ≤ incidenceDiffMass G U0 X Y)
    (hmatchingLarge :
      b * (scale : ℝ) ^ (3 / 4 : ℝ) *
          (⌈(Fintype.card V : ℝ) ^ (1 / 5 : ℝ)⌉₊ + 1) ≤ r) :
    Nonempty (StructuralWitness G scale nW ell K α aDisc aDiv b) := by
  let exceptional : ℕ := ⌈(Fintype.card V : ℝ) ^ (1 / 5 : ℝ)⌉₊
  let threshold : ℝ := δ * (ε / 2) * Fintype.card V
  let Conflict : Finset V → Finset V → Prop := fun X Y ↦
    X ≠ Y ∧ (supportDiffCard G Finset.univ X Y : ℝ) < threshold
  have hConflictSymm : Std.Symm Conflict := ⟨by
    intro X Y h
    refine ⟨Ne.symm h.1, ?_⟩
    rw [supportDiffCard_comm G Finset.univ Y X]
    exact h.2⟩
  have hConflictIrrefl : Std.Irrefl Conflict := ⟨by
    intro X h
    exact h.1 rfl⟩
  have hdegreeBounded : ∀ X ∈ candidates,
      degreeInto G Wminus X ≤ K * Fintype.card V ∧
      degreeInto G Wplus X ≤ K * Fintype.card V ∧
      degreeInto G U0 X ≤ K * Fintype.card V := by
    intro X hX
    have hbound (S : Finset V) : degreeInto G S X ≤ K * Fintype.card V := by
      calc
        degreeInto G S X ≤ X.card * S.card := degreeInto_le_card_mul_card G S X
        _ ≤ K * Fintype.card V := by
          rw [hcandidateUniform X hX]
          gcongr
          exact Finset.card_le_univ S
    exact ⟨hbound Wminus, hbound Wplus, hbound U0⟩
  have hconflictDegree :
      ∀ (family : Finset (Finset V)) (core : Finset V),
        family ⊆ candidates → family.card = r → IsSunflower family core →
        ∀ P ∈ petalFamily family core,
          ((petalFamily family core).filter fun Q ↦ Conflict P Q).card ≤
            exceptional := by
    intro family core hfamilySub hfamilyCard hsun P hP
    have hfamilyUniform : ∀ X ∈ family, X.card = K := by
      intro X hX
      exact hcandidateUniform X (hfamilySub hX)
    have hcorelt : core.card < K :=
      hsun.core_card_lt_uniform_card (by omega) hfamilyUniform
    let petals := petalFamily family core
    have hpetalsDisjoint :
        (petals : Set (Finset V)).PairwiseDisjoint id := by
      exact hsun.petalFamily_pairwiseDisjoint
    have hpetalsUniform : ∀ X ∈ petals, X.card = K - core.card := by
      intro X hX
      exact hsun.card_eq_sub_core_of_mem_petalFamily (by omega)
        hfamilyUniform hX
    have hpetalsCommon : ∀ X ∈ petals,
        δ * Fintype.card V ≤ (Erdos88.commonNeighborFinset G X).card := by
      intro X hX
      obtain ⟨A, hAfamily, rfl⟩ := Finset.mem_image.mp hX
      have hsub : A \ core ⊆ A := Finset.sdiff_subset
      have hCN := Erdos88.commonNeighborFinset_anti (G := G) hsub
      have hCNreal :
          ((Erdos88.commonNeighborFinset G A).card : ℝ) ≤
            (Erdos88.commonNeighborFinset G (A \ core)).card := by
        exact_mod_cast Finset.card_le_card hCN
      exact (hcandidateCommon A (hfamilySub hAfamily)).trans hCNreal
    have hbound := card_filter_lowSupportDiversity_le
      (P := petals) (x := P)
      (correctedRichWithBound_of_kwanSudakovRich hδ hε hrich)
      (by positivity) (by omega) hP hpetalsUniform hpetalsDisjoint hpetalsCommon
    simpa [petals, Conflict, threshold, exceptional] using hbound
  obtain ⟨qMinus, qPlus, q0, family, core, petals, matching, k,
      _hqMinus, _hqPlus, _hq0, hfamilySub, hfamilyCard, hsun,
      hrawDegrees, hpetalsDef, _hpetalsCard, hkpos, hkK,
      _hpetalsUniform, _hpetalsDisjoint, hmatchingSub, hmatchingDisjoint,
      hmatchingUniform, hmatchingCompatible, hmatchingCard⟩ :=
    exists_bounded_triple_sunflower_turan_thinning
      candidates (degreeInto G Wminus) (degreeInto G Wplus)
      (degreeInto G U0) (K * Fintype.card V) Conflict
      hConflictSymm hConflictIrrefl K r exceptional hr hcandidateUniform
      hdegreeBounded hlarge
      (fun family core hsub hcard hsun P hP ↦
        by simpa [Conflict] using
          hconflictDegree family core hsub hcard hsun P hP)
  have hmatchingAway : ∀ X ∈ matching,
      Disjoint X (Wminus ∪ Wplus ∪ U0) := by
    intro X hX
    have hXP := hmatchingSub hX
    rw [hpetalsDef] at hXP
    obtain ⟨A, hAfamily, rfl⟩ := Finset.mem_image.mp hXP
    exact hAaway.mono_left
      ((Finset.sdiff_subset).trans (hcandidateSub A (hfamilySub hAfamily)))
  have hpetalDegree (S : Finset V) (q : ℕ)
      (hraw : ∀ A ∈ family, degreeInto G S A = q) :
      ∀ X ∈ matching, degreeInto G S X = q - degreeInto G S core := by
    intro X hX
    have hXP := hmatchingSub hX
    rw [hpetalsDef] at hXP
    obtain ⟨A, hAfamily, rfl⟩ := Finset.mem_image.mp hXP
    have hcoreSub := hsun.core_subset_of_two_le_card (by omega) hAfamily
    have hadd := degreeInto_sdiff_add G S hcoreSub
    rw [hraw A hAfamily] at hadd
    omega
  have hdegreeMinus : ∀ X ∈ matching,
      degreeInto G Wminus X = qMinus - degreeInto G Wminus core :=
    hpetalDegree Wminus qMinus (fun A hA ↦ (hrawDegrees A hA).1)
  have hdegreePlus : ∀ X ∈ matching,
      degreeInto G Wplus X = qPlus - degreeInto G Wplus core :=
    hpetalDegree Wplus qPlus (fun A hA ↦ (hrawDegrees A hA).2.1)
  have hdegree0 : ∀ X ∈ matching,
      degreeInto G U0 X = q0 - degreeInto G U0 core :=
    hpetalDegree U0 q0 (fun A hA ↦ (hrawDegrees A hA).2.2)
  have hdiverse : ∀ X ∈ matching, ∀ Y ∈ matching, X ≠ Y →
      aDiv * scale ≤ incidenceDiffMass G U0 X Y := by
    intro X hX Y hY hXY
    apply hrestrict X Y
    · rw [hmatchingUniform X hX]
      exact hkK
    · rw [hmatchingUniform Y hY]
      exact hkK
    have hnot := hmatchingCompatible X hX Y hY hXY
    have hge : threshold ≤
        (supportDiffCard G Finset.univ X Y : ℝ) := by
      by_contra hlt
      exact hnot ⟨hXY, lt_of_not_ge hlt⟩
    simpa [threshold] using hge
  have hmatchingLarge' :
      b * (scale : ℝ) ^ (3 / 4 : ℝ) ≤ matching.card := by
    have hexcPos : (0 : ℝ) < exceptional + 1 := by positivity
    apply (mul_le_mul_iff_left₀ hexcPos).mp
    calc
      b * (scale : ℝ) ^ (3 / 4 : ℝ) * (exceptional + 1) ≤ r := by
        simpa [exceptional] using hmatchingLarge
      _ ≤ (matching.card : ℝ) * (exceptional + 1) := by
        exact_mod_cast hmatchingCard
  exact ⟨{
    k := k
    Wminus := Wminus
    Wplus := Wplus
    U0 := U0
    matching := matching
    k_pos := hkpos
    k_le := hkK
    disjoint_Wminus_Wplus := hWmWp
    disjoint_Wminus_U0 := hWmU
    disjoint_Wplus_U0 := hWpU
    matching_pairwiseDisjoint := hmatchingDisjoint
    matching_away := hmatchingAway
    card_Wminus := hWmcard
    card_Wplus := hWpcard
    card_U0 := hUcard
    matching_uniform := hmatchingUniform
    matching_large := hmatchingLarge'
    discrepancy := hdisc
    dMinus := qMinus - degreeInto G Wminus core
    dPlus := qPlus - degreeInto G Wplus core
    d0 := q0 - degreeInto G U0 core
    degree_Wminus := hdegreeMinus
    degree_Wplus := hdegreePlus
    degree_U0 := hdegree0
    diverse := hdiverse }⟩

end

end Erdos636
