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
import ErdosProblems.Erdos722.Probability
import Mathlib

/-!
# Random common-neighbourhood concentration for Erdős 722

For a fixed family of `(r-1)`-faces, candidate vertices outside every face
use pairwise disjoint collections of random `r`-edge coordinates.  Hence the
common-neighbourhood indicators are independent Bernoulli variables of mean
`p ^ roots.card`.  This file packages that exact injection and applies the
finite Chernoff estimates.
-/

namespace Erdos722.Typicality

open Finset MeasureTheory ProbabilityTheory

/-- The complete family of `r`-edges, kept local to avoid a cyclic import
with the main problem file. -/
def uniformEdges (n r : ℕ) : Finset (Finset (Fin n)) :=
  (Finset.univ : Finset (Fin n)).powersetCard r

@[simp] lemma mem_uniformEdges {e : Finset (Fin n)} :
    e ∈ uniformEdges n r ↔ e.card = r := by
  simp [uniformEdges]

/-- Vertices not already named by any root face. -/
def cleanVertices (n : ℕ) (roots : Finset (Finset (Fin n))) : Finset (Fin n) :=
  (Finset.univ : Finset (Fin n)).filter fun x ↦
    ∀ f ∈ roots, x ∉ f

lemma mem_cleanVertices {roots : Finset (Finset (Fin n))} {x : Fin n} :
    x ∈ cleanVertices n roots ↔ ∀ f ∈ roots, x ∉ f := by
  simp [cleanVertices]

/-- The random edge requested by a clean vertex and one root face. -/
def commonEdgeCoord (n r : ℕ) (roots : Finset (Finset (Fin n)))
    (hr : 0 < r)
    (hroot : ∀ f ∈ roots, f.card = r - 1)
    (s : (x : cleanVertices n roots) × {f // f ∈ roots}) :
    {e // e ∈ uniformEdges n r} := by
  let x : Fin n := s.1
  let f : Finset (Fin n) := s.2
  have hxf : x ∉ f := mem_cleanVertices.mp s.1.property f s.2.property
  refine ⟨insert x f, ?_⟩
  rw [mem_uniformEdges, card_insert_of_notMem hxf, hroot f s.2.property]
  omega

lemma commonEdgeCoord_injective
    {n r : ℕ} {roots : Finset (Finset (Fin n))}
    (hr : 0 < r)
    (hroot : ∀ f ∈ roots, f.card = r - 1) :
    Function.Injective (commonEdgeCoord n r roots hr hroot) := by
  classical
  rintro ⟨x, f⟩ ⟨y, g⟩ hcoord
  have hedge : insert (x : Fin n) (f : Finset (Fin n)) =
      insert (y : Fin n) (g : Finset (Fin n)) := by
    exact Subtype.ext_iff.mp hcoord
  have hxf : (x : Fin n) ∉ (f : Finset (Fin n)) :=
    mem_cleanVertices.mp x.property f f.property
  have hxg : (x : Fin n) ∉ (g : Finset (Fin n)) :=
    mem_cleanVertices.mp x.property g g.property
  have hyf : (y : Fin n) ∉ (f : Finset (Fin n)) :=
    mem_cleanVertices.mp y.property f f.property
  have hyg : (y : Fin n) ∉ (g : Finset (Fin n)) :=
    mem_cleanVertices.mp y.property g g.property
  have hxyval : (x : Fin n) = y := by
    by_contra hxy
    have hxmem : (x : Fin n) ∈ insert (y : Fin n) (g : Finset (Fin n)) := by
      rw [← hedge]
      exact mem_insert_self _ _
    rcases mem_insert.mp hxmem with h | h
    · exact hxy h
    · exact hxg h
  have hxy : x = y := Subtype.ext hxyval
  subst y
  have hfgval : (f : Finset (Fin n)) = g := by
    have herase := congrArg (fun e : Finset (Fin n) ↦ e.erase x) hedge
    simpa [Finset.erase_insert hxf, Finset.erase_insert hxg] using herase
  have hfg : f = g := Subtype.ext hfgval
  subst g
  rfl

/-- Indicator that adjoining `x` to every root produces a selected edge. -/
def commonNeighborIndicator
    (n r : ℕ) (roots : Finset (Finset (Fin n)))
    (hr : 0 < r)
    (hroot : ∀ f ∈ roots, f.card = r - 1)
    (x : cleanVertices n roots)
    (ω : {e // e ∈ uniformEdges n r} → Bool) : ℝ :=
  Probability.blockIndicator (commonEdgeCoord n r roots hr hroot) x ω

lemma commonNeighborIndicator_measurable
    (n r : ℕ) (roots : Finset (Finset (Fin n)))
    (hr : 0 < r)
    (hroot : ∀ f ∈ roots, f.card = r - 1)
    (x : cleanVertices n roots) :
    Measurable (commonNeighborIndicator n r roots hr hroot x) :=
  Probability.blockIndicator_measurable _ _

lemma commonNeighborIndicator_iIndep
    (n r : ℕ) (roots : Finset (Finset (Fin n)))
    (hr : 0 < r)
    (hroot : ∀ f ∈ roots, f.card = r - 1)
    (p : Set.Icc (0 : ℝ) 1) :
    iIndepFun (fun x ↦ commonNeighborIndicator n r roots hr hroot x)
      (Probability.bernoulliProductMeasure
        (ι := {e // e ∈ uniformEdges n r}) p) :=
  Probability.blockIndicator_iIndep p _ (commonEdgeCoord_injective hr hroot)

lemma integral_commonNeighborIndicator
    (n r : ℕ) (roots : Finset (Finset (Fin n)))
    (hr : 0 < r)
    (hroot : ∀ f ∈ roots, f.card = r - 1)
    (p : Set.Icc (0 : ℝ) 1) (x : cleanVertices n roots) :
    ∫ ω, commonNeighborIndicator n r roots hr hroot x ω
      ∂Probability.bernoulliProductMeasure
        (ι := {e // e ∈ uniformEdges n r}) p =
      (p : ℝ) ^ roots.card := by
  simpa [commonNeighborIndicator] using Probability.integral_blockIndicator p
    (commonEdgeCoord n r roots hr hroot) (commonEdgeCoord_injective hr hroot) x

lemma commonNeighborIndicator_zero_or_one
    (n r : ℕ) (roots : Finset (Finset (Fin n)))
    (hr : 0 < r)
    (hroot : ∀ f ∈ roots, f.card = r - 1)
    (x : cleanVertices n roots)
    (ω : {e // e ∈ uniformEdges n r} → Bool) :
    commonNeighborIndicator n r roots hr hroot x ω = 0 ∨
      commonNeighborIndicator n r roots hr hroot x ω = 1 :=
  Probability.blockIndicator_zero_or_one _ _ _

/-- Lower-tail estimate for one common neighbourhood. -/
theorem commonNeighbor_lower_half
    (n r : ℕ) (roots : Finset (Finset (Fin n)))
    (hr : 0 < r)
    (hroot : ∀ f ∈ roots, f.card = r - 1)
    (p : Set.Icc (0 : ℝ) 1) :
    (Probability.bernoulliProductMeasure
      (ι := {e // e ∈ uniformEdges n r}) p).real
      {ω | Probability.finiteRandomSum
          (fun x ↦ commonNeighborIndicator n r roots hr hroot x) ω ≤
        (cleanVertices n roots).card * (p : ℝ) ^ roots.card / 2} ≤
      Real.exp (-((cleanVertices n roots).card *
        (p : ℝ) ^ roots.card) / 10) := by
  simpa using Probability.finiteRandomSum_lower_half
    (P := Probability.bernoulliProductMeasure
      (ι := {e // e ∈ uniformEdges n r}) p)
    (fun x ↦ commonNeighborIndicator n r roots hr hroot x)
    (fun x ↦ commonNeighborIndicator_measurable n r roots hr hroot x)
    (commonNeighborIndicator_iIndep n r roots hr hroot p)
    (fun x ↦ commonNeighborIndicator_zero_or_one n r roots hr hroot x)
    (fun _ : cleanVertices n roots ↦ (p : ℝ) ^ roots.card)
    (fun x ↦ integral_commonNeighborIndicator n r roots hr hroot p x)
    (fun _ ↦ pow_nonneg p.property.1 _)

/-- Upper-tail estimate for one common neighbourhood. -/
theorem commonNeighbor_upper_twice
    (n r : ℕ) (roots : Finset (Finset (Fin n)))
    (hr : 0 < r)
    (hroot : ∀ f ∈ roots, f.card = r - 1)
    (p : Set.Icc (0 : ℝ) 1) :
    (Probability.bernoulliProductMeasure
      (ι := {e // e ∈ uniformEdges n r}) p).real
      {ω | 2 * ((cleanVertices n roots).card * (p : ℝ) ^ roots.card) ≤
        Probability.finiteRandomSum
          (fun x ↦ commonNeighborIndicator n r roots hr hroot x) ω} ≤
      Real.exp (-((cleanVertices n roots).card *
        (p : ℝ) ^ roots.card) / 5) := by
  simpa using Probability.finiteRandomSum_upper_twice
    (P := Probability.bernoulliProductMeasure
      (ι := {e // e ∈ uniformEdges n r}) p)
    (fun x ↦ commonNeighborIndicator n r roots hr hroot x)
    (fun x ↦ commonNeighborIndicator_measurable n r roots hr hroot x)
    (commonNeighborIndicator_iIndep n r roots hr hroot p)
    (fun x ↦ commonNeighborIndicator_zero_or_one n r roots hr hroot x)
    (fun _ : cleanVertices n roots ↦ (p : ℝ) ^ roots.card)
    (fun x ↦ integral_commonNeighborIndicator n r roots hr hroot p x)
    (fun _ ↦ pow_nonneg p.property.1 _)

/-- All families of at most `h` many `(r-1)`-faces. -/
def rootFamilies (n r h : ℕ) : Finset (Finset (Finset (Fin n))) :=
  ((uniformEdges n (r - 1)).powerset).filter fun roots ↦ roots.card ≤ h

lemma mem_rootFamilies {roots : Finset (Finset (Fin n))} :
    roots ∈ rootFamilies n r h ↔
      roots ⊆ uniformEdges n (r - 1) ∧ roots.card ≤ h := by
  simp [rootFamilies]

lemma root_card_of_mem_rootFamilies
    {n r h : ℕ} {roots : Finset (Finset (Fin n))}
    (hroots : roots ∈ rootFamilies n r h) (f : Finset (Fin n))
    (hf : f ∈ roots) :
    f.card = r - 1 := by
  exact mem_uniformEdges.mp ((mem_rootFamilies.mp hroots).1 hf)

/-- The expected clean common-neighbourhood size. -/
def commonMean (n : ℕ) (roots : Finset (Finset (Fin n)))
    (p : Set.Icc (0 : ℝ) 1) : ℝ :=
  (cleanVertices n roots).card * (p : ℝ) ^ roots.card

/-- Failure of either the lower-half or upper-twice estimate for one root
family. -/
def commonBad (n r : ℕ) (roots : Finset (Finset (Fin n)))
    (hr : 0 < r) (hroot : ∀ f ∈ roots, f.card = r - 1)
    (p : Set.Icc (0 : ℝ) 1) :
    Set ({e // e ∈ uniformEdges n r} → Bool) :=
  { ω | Probability.finiteRandomSum
        (fun x ↦ commonNeighborIndicator n r roots hr hroot x) ω ≤
      commonMean n roots p / 2 } ∪
    { ω | 2 * commonMean n roots p ≤
      Probability.finiteRandomSum
        (fun x ↦ commonNeighborIndicator n r roots hr hroot x) ω }

lemma measureReal_commonBad_le
    (n r : ℕ) (roots : Finset (Finset (Fin n)))
    (hr : 0 < r) (hroot : ∀ f ∈ roots, f.card = r - 1)
    (p : Set.Icc (0 : ℝ) 1) :
    (Probability.bernoulliProductMeasure
      (ι := {e // e ∈ uniformEdges n r}) p).real
      (commonBad n r roots hr hroot p) ≤
      Real.exp (-(commonMean n roots p) / 10) +
        Real.exp (-(commonMean n roots p) / 5) := by
  apply (MeasureTheory.measureReal_union_le _ _).trans
  exact add_le_add
    (by simpa [commonMean] using
      commonNeighbor_lower_half n r roots hr hroot p)
    (by simpa [commonMean] using
      commonNeighbor_upper_twice n r roots hr hroot p)

/-- Simultaneous common-neighbourhood typicality for every root family of
size at most `h`.  The sole numerical premise is precisely the finite union
bound; later asymptotic estimates discharge it for the reserve density. -/
theorem exists_simultaneously_typical
    (n r h : ℕ) (hr : 0 < r) (p : Set.Icc (0 : ℝ) 1)
    (htail :
      ∑ roots ∈ rootFamilies n r h,
        (Real.exp (-(commonMean n roots p) / 10) +
          Real.exp (-(commonMean n roots p) / 5)) < 1) :
    ∃ ω : {e // e ∈ uniformEdges n r} → Bool,
      ∀ roots, ∀ hroots : roots ∈ rootFamilies n r h,
        commonMean n roots p / 2 <
          Probability.finiteRandomSum
            (fun x ↦ commonNeighborIndicator n r roots hr
              (root_card_of_mem_rootFamilies hroots) x) ω ∧
        Probability.finiteRandomSum
            (fun x ↦ commonNeighborIndicator n r roots hr
              (root_card_of_mem_rootFamilies hroots) x) ω <
          2 * commonMean n roots p := by
  let P := Probability.bernoulliProductMeasure
    (ι := {e // e ∈ uniformEdges n r}) p
  let bad : Set ({e // e ∈ uniformEdges n r} → Bool) :=
    ⋃ roots : {roots // roots ∈ rootFamilies n r h},
      commonBad n r roots.1 hr
        (root_card_of_mem_rootFamilies roots.2) p
  have hbad : P.real bad < 1 := by
    calc
      P.real bad ≤ ∑ roots : {roots // roots ∈ rootFamilies n r h},
          P.real (commonBad n r roots.1 hr
            (root_card_of_mem_rootFamilies roots.2) p) := by
        exact MeasureTheory.measureReal_iUnion_fintype_le _
      _ ≤ ∑ roots : {roots // roots ∈ rootFamilies n r h},
          (Real.exp (-(commonMean n roots.1 p) / 10) +
            Real.exp (-(commonMean n roots.1 p) / 5)) := by
        apply Finset.sum_le_sum
        intro roots hroots
        exact measureReal_commonBad_le n r roots.1 hr
          (root_card_of_mem_rootFamilies roots.2) p
      _ = ∑ roots ∈ rootFamilies n r h,
          (Real.exp (-(commonMean n roots p) / 10) +
            Real.exp (-(commonMean n roots p) / 5)) := by
        exact (Finset.sum_subtype (rootFamilies n r h)
          (fun _ ↦ Iff.rfl)
          (fun roots ↦
            Real.exp (-(commonMean n roots p) / 10) +
              Real.exp (-(commonMean n roots p) / 5))).symm
      _ < 1 := htail
  have hproper : bad ≠ Set.univ := by
    intro hbaduniv
    have : P.real bad = 1 := by simp [hbaduniv, P]
    linarith
  obtain ⟨ω, hω⟩ : ∃ ω, ω ∉ bad := by
    by_contra hall
    apply hproper
    rw [Set.eq_univ_iff_forall]
    intro ω
    by_contra hnot
    exact hall ⟨ω, hnot⟩
  refine ⟨ω, ?_⟩
  intro roots hroots
  have hnotBad : ω ∉ commonBad n r roots hr
      (root_card_of_mem_rootFamilies hroots) p := by
    intro hmem
    apply hω
    simp only [bad, Set.mem_iUnion]
    exact ⟨⟨roots, hroots⟩, hmem⟩
  rw [commonBad, Set.mem_union, Set.mem_setOf_eq, Set.mem_setOf_eq,
    not_or] at hnotBad
  exact ⟨lt_of_not_ge hnotBad.1, lt_of_not_ge hnotBad.2⟩

/-- The deterministic `r`-graph encoded by one Bernoulli outcome. -/
def sampledEdges (n r : ℕ)
    (ω : {e // e ∈ uniformEdges n r} → Bool) :
    Finset (Finset (Fin n)) :=
  (uniformEdges n r).filter fun e ↦
    if he : e ∈ uniformEdges n r then ω ⟨e, he⟩ = true else False

lemma sampledEdges_subset
    (ω : {e // e ∈ uniformEdges n r} → Bool) :
    sampledEdges n r ω ⊆ uniformEdges n r :=
  Finset.filter_subset _ _

lemma mem_sampledEdges {e : Finset (Fin n)}
    {ω : {e // e ∈ uniformEdges n r} → Bool} :
    e ∈ sampledEdges n r ω ↔
      ∃ he : e ∈ uniformEdges n r, ω ⟨e, he⟩ = true := by
  classical
  simp only [sampledEdges, Finset.mem_filter]
  constructor
  · rintro ⟨he, hω⟩
    exact ⟨he, by simpa [he] using hω⟩
  · rintro ⟨he, hω⟩
    exact ⟨he, by simpa [he] using hω⟩

/-- Clean vertices which complete every root face to a sampled edge. -/
def commonNeighbors (n r : ℕ) (roots : Finset (Finset (Fin n)))
    (hr : 0 < r) (hroot : ∀ f ∈ roots, f.card = r - 1)
    (ω : {e // e ∈ uniformEdges n r} → Bool) :
    Finset (cleanVertices n roots) :=
  Finset.univ.filter fun x ↦
    ∀ f : {f // f ∈ roots},
      ω (commonEdgeCoord n r roots hr hroot ⟨x, f⟩) = true

lemma commonNeighborIndicator_eq_one_iff
    (n r : ℕ) (roots : Finset (Finset (Fin n)))
    (hr : 0 < r) (hroot : ∀ f ∈ roots, f.card = r - 1)
    (x : cleanVertices n roots)
    (ω : {e // e ∈ uniformEdges n r} → Bool) :
    commonNeighborIndicator n r roots hr hroot x ω = 1 ↔
      ∀ f : {f // f ∈ roots},
        ω (commonEdgeCoord n r roots hr hroot ⟨x, f⟩) = true := by
  classical
  by_cases hall : ∀ f : {f // f ∈ roots},
      ω (commonEdgeCoord n r roots hr hroot ⟨x, f⟩) = true
  · simp [hall, commonNeighborIndicator, Probability.blockIndicator,
      Probability.coordinateIndicator]
  · simp only [hall, iff_false]
    obtain ⟨f, hf⟩ := not_forall.mp hall
    have hfalse : ω (commonEdgeCoord n r roots hr hroot ⟨x, f⟩) = false := by
      cases h : ω (commonEdgeCoord n r roots hr hroot ⟨x, f⟩)
      · rfl
      · exact (hf h).elim
    have hzero : commonNeighborIndicator n r roots hr hroot x ω = 0 := by
      unfold commonNeighborIndicator Probability.blockIndicator
      apply Finset.prod_eq_zero (Finset.mem_univ f)
      simp [Probability.coordinateIndicator, hfalse]
    simp [hzero]

/-- The random sum is literally the cardinality of the common-neighbour
set. -/
lemma card_commonNeighbors
    (n r : ℕ) (roots : Finset (Finset (Fin n)))
    (hr : 0 < r) (hroot : ∀ f ∈ roots, f.card = r - 1)
    (ω : {e // e ∈ uniformEdges n r} → Bool) :
    ((commonNeighbors n r roots hr hroot ω).card : ℝ) =
      Probability.finiteRandomSum
        (fun x ↦ commonNeighborIndicator n r roots hr hroot x) ω := by
  classical
  rw [Probability.finiteRandomSum]
  calc
    ((commonNeighbors n r roots hr hroot ω).card : ℝ) =
        ∑ x : cleanVertices n roots,
          if (∀ f : {f // f ∈ roots},
            ω (commonEdgeCoord n r roots hr hroot ⟨x, f⟩) = true)
          then 1 else 0 := by
      simp [commonNeighbors]
    _ = ∑ x : cleanVertices n roots,
        commonNeighborIndicator n r roots hr hroot x ω := by
      apply Finset.sum_congr rfl
      intro x hx
      by_cases hall : ∀ f : {f // f ∈ roots},
          ω (commonEdgeCoord n r roots hr hroot ⟨x, f⟩) = true
      · rw [if_pos hall]
        exact (commonNeighborIndicator_eq_one_iff n r roots hr hroot x ω).mpr hall |>.symm
      · rw [if_neg hall]
        rcases commonNeighborIndicator_zero_or_one n r roots hr hroot x ω with hz | ho
        · exact hz.symm
        · exact (hall ((commonNeighborIndicator_eq_one_iff
            n r roots hr hroot x ω).mp ho)).elim

end Erdos722.Typicality
