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
import ErdosProblems.Erdos722.Typicality
import ErdosProblems.Erdos722.Reserve
import Mathlib

set_option relaxedAutoImplicit true

/-!
# Simultaneous typicality for finitely many independent colours

The generator construction uses a fixed number of independently coloured
copies of the sparse random host.  A candidate vertex may have to complete
different root faces in different colours.  The coordinate map below is
still injective, so the same finite Chernoff argument as in `Typicality`
applies verbatim.
-/

namespace Erdos722.ColoredTypicality

open Finset MeasureTheory ProbabilityTheory
open Erdos722.Typicality

noncomputable section

/-- A root face together with the colour in which its completed edge is
required to lie. -/
abbrev ColoredRoot (u n : ℕ) := Fin u × Finset (Fin n)

/-- All coloured families of at most `h` uniform `(r-1)`-faces. -/
def coloredRootFamilies (u n r h : ℕ) :
    Finset (Finset (ColoredRoot u n)) :=
  (((Finset.univ : Finset (Fin u)) ×ˢ uniformEdges n (r - 1)).powerset).filter
    fun roots ↦ roots.card ≤ h

lemma mem_coloredRootFamilies
    {roots : Finset (ColoredRoot u n)} :
    roots ∈ coloredRootFamilies u n r h ↔
      roots ⊆ (Finset.univ : Finset (Fin u)) ×ˢ uniformEdges n (r - 1) ∧
        roots.card ≤ h := by
  simp [coloredRootFamilies]

/-- Vertices not already present in any underlying coloured root face. -/
def cleanColoredVertices (n : ℕ) (roots : Finset (ColoredRoot u n)) :
    Finset (Fin n) :=
  (Finset.univ : Finset (Fin n)).filter fun x ↦
    ∀ z ∈ roots, x ∉ z.2

lemma mem_cleanColoredVertices
    {roots : Finset (ColoredRoot u n)} {x : Fin n} :
    x ∈ cleanColoredVertices n roots ↔ ∀ z ∈ roots, x ∉ z.2 := by
  simp [cleanColoredVertices]

lemma coloredRoot_card_of_mem
    {roots : Finset (ColoredRoot u n)}
    (hroots : roots ∈ coloredRootFamilies u n r h)
    (z : ColoredRoot u n) (hz : z ∈ roots) : z.2.card = r - 1 := by
  have hzprod := (mem_coloredRootFamilies.mp hroots).1 hz
  exact mem_uniformEdges.mp (Finset.mem_product.mp hzprod).2

/-- The independent Bernoulli coordinate requested by a clean vertex and a
coloured root. -/
def coloredCommonEdgeCoord
    (u n r : ℕ) (roots : Finset (ColoredRoot u n))
    (hr : 0 < r) (hroot : ∀ z ∈ roots, z.2.card = r - 1)
    (s : (x : cleanColoredVertices n roots) × {z // z ∈ roots}) :
    Fin u × {e // e ∈ uniformEdges n r} := by
  let x : Fin n := s.1
  let z : ColoredRoot u n := s.2
  have hx : x ∉ z.2 :=
    mem_cleanColoredVertices.mp s.1.property z s.2.property
  refine ⟨z.1, ⟨insert x z.2, ?_⟩⟩
  rw [mem_uniformEdges, card_insert_of_notMem hx, hroot z s.2.property]
  omega

lemma coloredCommonEdgeCoord_injective
    {roots : Finset (ColoredRoot u n)}
    (hr : 0 < r) (hroot : ∀ z ∈ roots, z.2.card = r - 1) :
    Function.Injective (coloredCommonEdgeCoord u n r roots hr hroot) := by
  classical
  rintro ⟨x, z⟩ ⟨y, w⟩ hcoord
  have hcolor : z.1.1 = w.1.1 :=
    congrArg
      (fun t : Fin u × {e // e ∈ uniformEdges n r} ↦ t.1) hcoord
  have hedge : insert (x : Fin n) z.1.2 = insert (y : Fin n) w.1.2 := by
    exact Subtype.ext_iff.mp (congrArg
      (fun t : Fin u × {e // e ∈ uniformEdges n r} ↦ t.2) hcoord)
  have hxz : (x : Fin n) ∉ z.1.2 :=
    mem_cleanColoredVertices.mp x.property z.1 z.2
  have hxw : (x : Fin n) ∉ w.1.2 :=
    mem_cleanColoredVertices.mp x.property w.1 w.2
  have hyz : (y : Fin n) ∉ z.1.2 :=
    mem_cleanColoredVertices.mp y.property z.1 z.2
  have hyw : (y : Fin n) ∉ w.1.2 :=
    mem_cleanColoredVertices.mp y.property w.1 w.2
  have hxyVal : (x : Fin n) = y := by
    by_contra hxy
    have hxmem : (x : Fin n) ∈ insert (y : Fin n) w.1.2 := by
      rw [← hedge]
      exact Finset.mem_insert_self _ _
    rcases Finset.mem_insert.mp hxmem with h | h
    · exact hxy h
    · exact hxw h
  have hxy : x = y := Subtype.ext hxyVal
  subst y
  have hfaceVal : z.1.2 = w.1.2 := by
    have herase := congrArg (fun e : Finset (Fin n) ↦ e.erase x) hedge
    simpa [Finset.erase_insert hxz, Finset.erase_insert hxw] using herase
  have hrootVal : z.1 = w.1 := by
    apply Prod.ext hcolor
    exact hfaceVal
  have hzw : z = w := Subtype.ext hrootVal
  subst w
  rfl

/-- Indicator that `x` completes every coloured root in its prescribed
colour. -/
def coloredCommonNeighborIndicator
    (u n r : ℕ) (roots : Finset (ColoredRoot u n))
    (hr : 0 < r) (hroot : ∀ z ∈ roots, z.2.card = r - 1)
    (x : cleanColoredVertices n roots)
    (ω : (Fin u × {e // e ∈ uniformEdges n r}) → Bool) : ℝ :=
  Erdos722.Probability.blockIndicator
    (coloredCommonEdgeCoord u n r roots hr hroot) x ω

lemma coloredCommonNeighborIndicator_measurable
    (u n r : ℕ) (roots : Finset (ColoredRoot u n))
    (hr : 0 < r) (hroot : ∀ z ∈ roots, z.2.card = r - 1)
    (x : cleanColoredVertices n roots) :
    Measurable (coloredCommonNeighborIndicator u n r roots hr hroot x) :=
  Erdos722.Probability.blockIndicator_measurable _ _

lemma coloredCommonNeighborIndicator_iIndep
    (u n r : ℕ) (roots : Finset (ColoredRoot u n))
    (hr : 0 < r) (hroot : ∀ z ∈ roots, z.2.card = r - 1)
    (p : Set.Icc (0 : ℝ) 1) :
    iIndepFun
      (fun x ↦ coloredCommonNeighborIndicator u n r roots hr hroot x)
      (Erdos722.Probability.bernoulliProductMeasure
        (ι := Fin u × {e // e ∈ uniformEdges n r}) p) :=
  Erdos722.Probability.blockIndicator_iIndep p _
    (coloredCommonEdgeCoord_injective hr hroot)

lemma integral_coloredCommonNeighborIndicator
    (u n r : ℕ) (roots : Finset (ColoredRoot u n))
    (hr : 0 < r) (hroot : ∀ z ∈ roots, z.2.card = r - 1)
    (p : Set.Icc (0 : ℝ) 1) (x : cleanColoredVertices n roots) :
    ∫ ω, coloredCommonNeighborIndicator u n r roots hr hroot x ω
        ∂Erdos722.Probability.bernoulliProductMeasure
          (ι := Fin u × {e // e ∈ uniformEdges n r}) p =
      (p : ℝ) ^ roots.card := by
  simpa [coloredCommonNeighborIndicator] using
    Erdos722.Probability.integral_blockIndicator p
      (coloredCommonEdgeCoord u n r roots hr hroot)
      (coloredCommonEdgeCoord_injective hr hroot) x

lemma coloredCommonNeighborIndicator_zero_or_one
    (u n r : ℕ) (roots : Finset (ColoredRoot u n))
    (hr : 0 < r) (hroot : ∀ z ∈ roots, z.2.card = r - 1)
    (x : cleanColoredVertices n roots)
    (ω : (Fin u × {e // e ∈ uniformEdges n r}) → Bool) :
    coloredCommonNeighborIndicator u n r roots hr hroot x ω = 0 ∨
      coloredCommonNeighborIndicator u n r roots hr hroot x ω = 1 :=
  Erdos722.Probability.blockIndicator_zero_or_one _ _ _

/-- Clean vertices completing every prescribed face in its prescribed
colour. -/
def coloredCommonNeighbors
    (u n r : ℕ) (roots : Finset (ColoredRoot u n))
    (hr : 0 < r) (hroot : ∀ z ∈ roots, z.2.card = r - 1)
    (ω : (Fin u × {e // e ∈ uniformEdges n r}) → Bool) :
    Finset (cleanColoredVertices n roots) :=
  Finset.univ.filter fun x ↦
    ∀ z : {z // z ∈ roots},
      ω (coloredCommonEdgeCoord u n r roots hr hroot ⟨x, z⟩) = true

lemma coloredCommonNeighborIndicator_eq_one_iff
    (u n r : ℕ) (roots : Finset (ColoredRoot u n))
    (hr : 0 < r) (hroot : ∀ z ∈ roots, z.2.card = r - 1)
    (x : cleanColoredVertices n roots)
    (ω : (Fin u × {e // e ∈ uniformEdges n r}) → Bool) :
    coloredCommonNeighborIndicator u n r roots hr hroot x ω = 1 ↔
      ∀ z : {z // z ∈ roots},
        ω (coloredCommonEdgeCoord u n r roots hr hroot ⟨x, z⟩) = true := by
  classical
  by_cases hall : ∀ z : {z // z ∈ roots},
      ω (coloredCommonEdgeCoord u n r roots hr hroot ⟨x, z⟩) = true
  · simp [hall, coloredCommonNeighborIndicator,
      Erdos722.Probability.blockIndicator,
      Erdos722.Probability.coordinateIndicator]
  · simp only [hall, iff_false]
    obtain ⟨z, hz⟩ := not_forall.mp hall
    have hfalse :
        ω (coloredCommonEdgeCoord u n r roots hr hroot ⟨x, z⟩) = false := by
      cases h : ω (coloredCommonEdgeCoord u n r roots hr hroot ⟨x, z⟩)
      · rfl
      · exact (hz h).elim
    have hzero :
        coloredCommonNeighborIndicator u n r roots hr hroot x ω = 0 := by
      unfold coloredCommonNeighborIndicator
        Erdos722.Probability.blockIndicator
      apply Finset.prod_eq_zero (Finset.mem_univ z)
      simp [Erdos722.Probability.coordinateIndicator, hfalse]
    simp [hzero]

/-- The coloured common-neighbour random sum is its literal cardinality. -/
lemma card_coloredCommonNeighbors
    (u n r : ℕ) (roots : Finset (ColoredRoot u n))
    (hr : 0 < r) (hroot : ∀ z ∈ roots, z.2.card = r - 1)
    (ω : (Fin u × {e // e ∈ uniformEdges n r}) → Bool) :
    ((coloredCommonNeighbors u n r roots hr hroot ω).card : ℝ) =
      Erdos722.Probability.finiteRandomSum
        (fun x ↦ coloredCommonNeighborIndicator u n r roots hr hroot x) ω := by
  classical
  rw [Erdos722.Probability.finiteRandomSum]
  calc
    ((coloredCommonNeighbors u n r roots hr hroot ω).card : ℝ) =
        ∑ x : cleanColoredVertices n roots,
          if (∀ z : {z // z ∈ roots},
            ω (coloredCommonEdgeCoord u n r roots hr hroot ⟨x, z⟩) = true)
          then 1 else 0 := by
      simp [coloredCommonNeighbors]
    _ = ∑ x : cleanColoredVertices n roots,
        coloredCommonNeighborIndicator u n r roots hr hroot x ω := by
      apply Finset.sum_congr rfl
      intro x hx
      by_cases hall : ∀ z : {z // z ∈ roots},
          ω (coloredCommonEdgeCoord u n r roots hr hroot ⟨x, z⟩) = true
      · rw [if_pos hall]
        exact (coloredCommonNeighborIndicator_eq_one_iff
          u n r roots hr hroot x ω).mpr hall |>.symm
      · rw [if_neg hall]
        rcases coloredCommonNeighborIndicator_zero_or_one
          u n r roots hr hroot x ω with hz | ho
        · exact hz.symm
        · exact (hall ((coloredCommonNeighborIndicator_eq_one_iff
            u n r roots hr hroot x ω).mp ho)).elim

lemma mem_coloredCommonNeighbors
    {u n r : ℕ} {roots : Finset (ColoredRoot u n)}
    (hr : 0 < r) (hroot : ∀ z ∈ roots, z.2.card = r - 1)
    (ω : (Fin u × {e // e ∈ uniformEdges n r}) → Bool)
    {x : cleanColoredVertices n roots} :
    x ∈ coloredCommonNeighbors u n r roots hr hroot ω ↔
      ∀ z : {z // z ∈ roots},
        ω (coloredCommonEdgeCoord u n r roots hr hroot ⟨x, z⟩) = true := by
  simp [coloredCommonNeighbors]

/-- Expected size of a coloured common neighbourhood. -/
def coloredCommonMean (n : ℕ) (roots : Finset (ColoredRoot u n))
    (p : Set.Icc (0 : ℝ) 1) : ℝ :=
  (cleanColoredVertices n roots).card * (p : ℝ) ^ roots.card

/-- Lower typicality, rewritten as a literal lower bound for the finite
coloured common-neighbourhood. -/
lemma coloredTypical_card_commonNeighbors_lower
    {u n r h : ℕ} (hr : 0 < r)
    (p : Set.Icc (0 : ℝ) 1)
    (ω : (Fin u × {e // e ∈ uniformEdges n r}) → Bool)
    (htyp : ∀ roots, ∀ hroots : roots ∈ coloredRootFamilies u n r h,
      coloredCommonMean n roots p / 2 <
        Erdos722.Probability.finiteRandomSum
          (fun x ↦ coloredCommonNeighborIndicator u n r roots hr
            (coloredRoot_card_of_mem hroots) x) ω ∧
      Erdos722.Probability.finiteRandomSum
          (fun x ↦ coloredCommonNeighborIndicator u n r roots hr
            (coloredRoot_card_of_mem hroots) x) ω <
        2 * coloredCommonMean n roots p)
    {roots : Finset (ColoredRoot u n)}
    (hroots : roots ∈ coloredRootFamilies u n r h) :
    coloredCommonMean n roots p / 2 <
      ((coloredCommonNeighbors u n r roots hr
        (coloredRoot_card_of_mem hroots) ω).card : ℝ) := by
  rw [card_coloredCommonNeighbors]
  exact (htyp roots hroots).1

/-- A lower-typical coloured common neighbourhood contains a vertex outside
any finite avoidance set no larger than half its mean. -/
theorem exists_coloredCommonNeighbor_not_mem
    {u n r h : ℕ} (hr : 0 < r)
    (p : Set.Icc (0 : ℝ) 1)
    (ω : (Fin u × {e // e ∈ uniformEdges n r}) → Bool)
    (htyp : ∀ roots, ∀ hroots : roots ∈ coloredRootFamilies u n r h,
      coloredCommonMean n roots p / 2 <
        Erdos722.Probability.finiteRandomSum
          (fun x ↦ coloredCommonNeighborIndicator u n r roots hr
            (coloredRoot_card_of_mem hroots) x) ω ∧
      Erdos722.Probability.finiteRandomSum
          (fun x ↦ coloredCommonNeighborIndicator u n r roots hr
            (coloredRoot_card_of_mem hroots) x) ω <
        2 * coloredCommonMean n roots p)
    {roots : Finset (ColoredRoot u n)}
    (hroots : roots ∈ coloredRootFamilies u n r h)
    (avoid : Finset (Fin n))
    (havoid : (avoid.card : ℝ) ≤ coloredCommonMean n roots p / 2) :
    ∃ x : cleanColoredVertices n roots,
      x ∈ coloredCommonNeighbors u n r roots hr
        (coloredRoot_card_of_mem hroots) ω ∧ (x : Fin n) ∉ avoid := by
  let common := coloredCommonNeighbors u n r roots hr
    (coloredRoot_card_of_mem hroots) ω
  have hlarge : avoid.card < common.card := by
    have hreal : (avoid.card : ℝ) < (common.card : ℝ) :=
      lt_of_le_of_lt havoid
        (coloredTypical_card_commonNeighbors_lower hr p ω htyp hroots)
    exact_mod_cast hreal
  by_contra hnone
  push_neg at hnone
  have hle : common.card ≤ avoid.card := by
    apply Finset.card_le_card_of_injOn (fun x : cleanColoredVertices n roots ↦ x.1)
    · intro x hx
      exact hnone x hx
    · intro x hx y hy hxy
      exact Subtype.ext hxy
  omega

/-- Failure of either standard Chernoff estimate for one coloured root
family. -/
def coloredCommonBad
    (u n r : ℕ) (roots : Finset (ColoredRoot u n))
    (hr : 0 < r) (hroot : ∀ z ∈ roots, z.2.card = r - 1)
    (p : Set.Icc (0 : ℝ) 1) :
    Set ((Fin u × {e // e ∈ uniformEdges n r}) → Bool) :=
  {ω | Erdos722.Probability.finiteRandomSum
        (fun x ↦ coloredCommonNeighborIndicator u n r roots hr hroot x) ω ≤
      coloredCommonMean n roots p / 2} ∪
    {ω | 2 * coloredCommonMean n roots p ≤
      Erdos722.Probability.finiteRandomSum
        (fun x ↦ coloredCommonNeighborIndicator u n r roots hr hroot x) ω}

lemma measureReal_coloredCommonBad_le
    (u n r : ℕ) (roots : Finset (ColoredRoot u n))
    (hr : 0 < r) (hroot : ∀ z ∈ roots, z.2.card = r - 1)
    (p : Set.Icc (0 : ℝ) 1) :
    (Erdos722.Probability.bernoulliProductMeasure
      (ι := Fin u × {e // e ∈ uniformEdges n r}) p).real
        (coloredCommonBad u n r roots hr hroot p) ≤
      Real.exp (-(coloredCommonMean n roots p) / 10) +
        Real.exp (-(coloredCommonMean n roots p) / 5) := by
  apply (MeasureTheory.measureReal_union_le _ _).trans
  apply add_le_add
  · simpa [coloredCommonMean] using
      (Erdos722.Probability.finiteRandomSum_lower_half
        (P := Erdos722.Probability.bernoulliProductMeasure
          (ι := Fin u × {e // e ∈ uniformEdges n r}) p)
        (fun x ↦ coloredCommonNeighborIndicator u n r roots hr hroot x)
        (fun x ↦ coloredCommonNeighborIndicator_measurable
          u n r roots hr hroot x)
        (coloredCommonNeighborIndicator_iIndep u n r roots hr hroot p)
        (fun x ↦ coloredCommonNeighborIndicator_zero_or_one
          u n r roots hr hroot x)
        (fun _ : cleanColoredVertices n roots ↦ (p : ℝ) ^ roots.card)
        (fun x ↦ integral_coloredCommonNeighborIndicator
          u n r roots hr hroot p x)
        (fun _ ↦ pow_nonneg p.property.1 _))
  · simpa [coloredCommonMean] using
      (Erdos722.Probability.finiteRandomSum_upper_twice
        (P := Erdos722.Probability.bernoulliProductMeasure
          (ι := Fin u × {e // e ∈ uniformEdges n r}) p)
        (fun x ↦ coloredCommonNeighborIndicator u n r roots hr hroot x)
        (fun x ↦ coloredCommonNeighborIndicator_measurable
          u n r roots hr hroot x)
        (coloredCommonNeighborIndicator_iIndep u n r roots hr hroot p)
        (fun x ↦ coloredCommonNeighborIndicator_zero_or_one
          u n r roots hr hroot x)
        (fun _ : cleanColoredVertices n roots ↦ (p : ℝ) ^ roots.card)
        (fun x ↦ integral_coloredCommonNeighborIndicator
          u n r roots hr hroot p x)
        (fun _ ↦ pow_nonneg p.property.1 _))

/-- Simultaneous coloured typicality under the exact finite union-bound
premise. -/
theorem exists_simultaneously_coloredTypical
    (u n r h : ℕ) (hr : 0 < r) (p : Set.Icc (0 : ℝ) 1)
    (htail :
      ∑ roots ∈ coloredRootFamilies u n r h,
        (Real.exp (-(coloredCommonMean n roots p) / 10) +
          Real.exp (-(coloredCommonMean n roots p) / 5)) < 1) :
    ∃ ω : (Fin u × {e // e ∈ uniformEdges n r}) → Bool,
      ∀ roots, ∀ hroots : roots ∈ coloredRootFamilies u n r h,
        coloredCommonMean n roots p / 2 <
          Erdos722.Probability.finiteRandomSum
            (fun x ↦ coloredCommonNeighborIndicator u n r roots hr
              (coloredRoot_card_of_mem hroots) x) ω ∧
        Erdos722.Probability.finiteRandomSum
            (fun x ↦ coloredCommonNeighborIndicator u n r roots hr
              (coloredRoot_card_of_mem hroots) x) ω <
          2 * coloredCommonMean n roots p := by
  let P := Erdos722.Probability.bernoulliProductMeasure
    (ι := Fin u × {e // e ∈ uniformEdges n r}) p
  let bad : Set ((Fin u × {e // e ∈ uniformEdges n r}) → Bool) :=
    ⋃ roots : {roots // roots ∈ coloredRootFamilies u n r h},
      coloredCommonBad u n r roots.1 hr
        (coloredRoot_card_of_mem roots.2) p
  have hbad : P.real bad < 1 := by
    calc
      P.real bad ≤ ∑ roots : {roots //
          roots ∈ coloredRootFamilies u n r h},
          P.real (coloredCommonBad u n r roots.1 hr
            (coloredRoot_card_of_mem roots.2) p) := by
        exact MeasureTheory.measureReal_iUnion_fintype_le _
      _ ≤ ∑ roots : {roots // roots ∈ coloredRootFamilies u n r h},
          (Real.exp (-(coloredCommonMean n roots.1 p) / 10) +
            Real.exp (-(coloredCommonMean n roots.1 p) / 5)) := by
        apply Finset.sum_le_sum
        intro roots hroots
        exact measureReal_coloredCommonBad_le u n r roots.1 hr
          (coloredRoot_card_of_mem roots.2) p
      _ = ∑ roots ∈ coloredRootFamilies u n r h,
          (Real.exp (-(coloredCommonMean n roots p) / 10) +
            Real.exp (-(coloredCommonMean n roots p) / 5)) := by
        exact (Finset.sum_subtype (coloredRootFamilies u n r h)
          (fun _ ↦ Iff.rfl)
          (fun roots ↦
            Real.exp (-(coloredCommonMean n roots p) / 10) +
              Real.exp (-(coloredCommonMean n roots p) / 5))).symm
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
  have hnotBad : ω ∉ coloredCommonBad u n r roots hr
      (coloredRoot_card_of_mem hroots) p := by
    intro hmem
    apply hω
    simp only [bad, Set.mem_iUnion]
    exact ⟨⟨roots, hroots⟩, hmem⟩
  rw [coloredCommonBad, Set.mem_union, Set.mem_setOf_eq,
    Set.mem_setOf_eq, not_or] at hnotBad
  exact ⟨lt_of_not_ge hnotBad.1, lt_of_not_ge hnotBad.2⟩

/-- The deterministic `r`-graph in one colour of a coloured Bernoulli
outcome. -/
def sampledColorEdges (u n r : ℕ)
    (ω : (Fin u × {e // e ∈ uniformEdges n r}) → Bool)
    (i : Fin u) : Finset (Finset (Fin n)) :=
  (uniformEdges n r).filter fun e ↦
    if he : e ∈ uniformEdges n r then ω (i, ⟨e, he⟩) = true else False

lemma sampledColorEdges_subset
    (ω : (Fin u × {e // e ∈ uniformEdges n r}) → Bool) (i : Fin u) :
    sampledColorEdges u n r ω i ⊆ uniformEdges n r :=
  Finset.filter_subset _ _

lemma mem_sampledColorEdges {e : Finset (Fin n)}
    {ω : (Fin u × {e // e ∈ uniformEdges n r}) → Bool} {i : Fin u} :
    e ∈ sampledColorEdges u n r ω i ↔
      ∃ he : e ∈ uniformEdges n r, ω (i, ⟨e, he⟩) = true := by
  classical
  simp only [sampledColorEdges, Finset.mem_filter]
  constructor
  · rintro ⟨he, hω⟩
    exact ⟨he, by simpa [he] using hω⟩
  · rintro ⟨he, hω⟩
    exact ⟨he, by simpa [he] using hω⟩

/-- The coloured common-neighbour count for one singleton root is exactly
the local degree of that colour. -/
def colorOutcome
    (ω : (Fin u × {e // e ∈ uniformEdges n r}) → Bool) (i : Fin u) :
    {e // e ∈ uniformEdges n r} → Bool := fun e ↦ ω (i, e)

lemma sampledColorEdges_eq_sampledEdges
    (ω : (Fin u × {e // e ∈ uniformEdges n r}) → Bool) (i : Fin u) :
    sampledColorEdges u n r ω i =
      sampledEdges n r (colorOutcome ω i) := by
  classical
  ext e
  simp [sampledColorEdges, sampledEdges, colorOutcome]

def cleanSingletonEquiv (i : Fin u) (I : Finset (Fin n)) :
    ↑(cleanColoredVertices n ({(i, I)} : Finset (ColoredRoot u n))) ≃
      ↑(cleanVertices n ({I} : Finset (Finset (Fin n)))) where
  toFun x := ⟨x.1, by
    simpa [cleanColoredVertices, cleanVertices] using x.2⟩
  invFun x := ⟨x.1, by
    simpa [cleanColoredVertices, cleanVertices] using x.2⟩
  left_inv x := Subtype.ext rfl
  right_inv x := Subtype.ext rfl

lemma coloredCommonNeighborIndicator_singleton
    {u n r : ℕ} (hr : 0 < r) (i : Fin u)
    (I : Finset (Fin n)) (hI : I.card = r - 1)
    (ω : (Fin u × {e // e ∈ uniformEdges n r}) → Bool)
    (x : ↑(cleanColoredVertices n ({(i, I)} :
      Finset (ColoredRoot u n)))) :
    coloredCommonNeighborIndicator u n r {(i, I)} hr
        (by simpa using hI) x ω =
      commonNeighborIndicator n r {I} hr (by simpa using hI)
        (cleanSingletonEquiv i I x) (colorOutcome ω i) := by
  classical
  simp [coloredCommonNeighborIndicator, commonNeighborIndicator,
    Erdos722.Probability.blockIndicator, coloredCommonEdgeCoord,
    commonEdgeCoord, cleanSingletonEquiv, colorOutcome,
    Erdos722.Probability.coordinateIndicator]
  congr 3

lemma localDegree_sampledColorEdges_eq_commonSum
    {u n r : ℕ} (hr : 0 < r) (i : Fin u)
    (I : Finset (Fin n)) (hI : I.card = r - 1)
    (ω : (Fin u × {e // e ∈ uniformEdges n r}) → Bool) :
    (((sampledColorEdges u n r ω i).filter fun e ↦ I ⊆ e).card : ℝ) =
      Erdos722.Probability.finiteRandomSum
        (fun x ↦ coloredCommonNeighborIndicator u n r {(i, I)} hr
          (by simpa using hI) x) ω := by
  rw [sampledColorEdges_eq_sampledEdges]
  have hdegree :=
    Erdos722.Reserve.localDegree_sampledEdges_eq_commonNeighbors
      hr I hI (colorOutcome ω i)
  change ((sampledEdges n r (colorOutcome ω i)).filter
      fun e ↦ I ⊆ e).card =
    (commonNeighbors n r {I} hr (by simpa using hI)
      (colorOutcome ω i)).card at hdegree
  rw [hdegree]
  rw [card_commonNeighbors]
  rw [Erdos722.Probability.finiteRandomSum,
    Erdos722.Probability.finiteRandomSum]
  exact Fintype.sum_equiv (cleanSingletonEquiv i I).symm
    (fun x ↦ commonNeighborIndicator n r {I} hr (by simpa using hI)
      x (colorOutcome ω i))
    (fun x ↦ coloredCommonNeighborIndicator u n r {(i, I)} hr
      (by simpa using hI) x ω)
    (fun x ↦ by
      simpa using (coloredCommonNeighborIndicator_singleton
        hr i I hI ω ((cleanSingletonEquiv i I).symm x)).symm)

/-- Singleton-root upper typicality gives the degree bound for each colour. -/
theorem coloredTypical_localDegree_upper
    {u n r h : ℕ} (hr : 0 < r) (hh : 0 < h)
    (p : Set.Icc (0 : ℝ) 1)
    (ω : (Fin u × {e // e ∈ uniformEdges n r}) → Bool)
    (htyp : ∀ roots, ∀ hroots : roots ∈ coloredRootFamilies u n r h,
      coloredCommonMean n roots p / 2 <
        Erdos722.Probability.finiteRandomSum
          (fun x ↦ coloredCommonNeighborIndicator u n r roots hr
            (coloredRoot_card_of_mem hroots) x) ω ∧
      Erdos722.Probability.finiteRandomSum
          (fun x ↦ coloredCommonNeighborIndicator u n r roots hr
            (coloredRoot_card_of_mem hroots) x) ω <
        2 * coloredCommonMean n roots p) :
    ∀ i I, I.card = r - 1 →
      (((sampledColorEdges u n r ω i).filter fun e ↦ I ⊆ e).card : ℝ) <
        2 * n * (p : ℝ) := by
  intro i I hI
  have hroots : ({(i, I)} : Finset (ColoredRoot u n)) ∈
      coloredRootFamilies u n r h := by
    rw [mem_coloredRootFamilies]
    constructor
    · simp [hI]
    · simp
      omega
  have hupp := (htyp {(i, I)} hroots).2
  rw [← localDegree_sampledColorEdges_eq_commonSum hr i I hI ω] at hupp
  calc
    (((sampledColorEdges u n r ω i).filter fun e ↦ I ⊆ e).card : ℝ) <
        2 * coloredCommonMean n {(i, I)} p := hupp
    _ ≤ 2 * n * (p : ℝ) := by
      unfold coloredCommonMean
      simp only [Finset.card_singleton, pow_one]
      have hc : ((cleanColoredVertices n {(i, I)}).card : ℝ) ≤ n := by
        have hcNat : (cleanColoredVertices n {(i, I)}).card ≤ n := by
          simpa using Finset.card_le_univ (cleanColoredVertices n {(i, I)})
        exact_mod_cast hcNat
      nlinarith [p.property.1]

lemma cleanColoredVertices_eq_sdiff_biUnion
    (roots : Finset (ColoredRoot u n)) :
    cleanColoredVertices n roots =
      (Finset.univ : Finset (Fin n)) \ roots.biUnion (fun z ↦ z.2) := by
  classical
  ext x
  simp [cleanColoredVertices]

lemma cleanColoredVertices_card_lower
    {roots : Finset (ColoredRoot u n)}
    (hroot : ∀ z ∈ roots, z.2.card = r - 1)
    (hroots : roots.card ≤ h) :
    n - h * (r - 1) ≤ (cleanColoredVertices n roots).card := by
  classical
  have hunion : (roots.biUnion (fun z ↦ z.2)).card ≤
      roots.card * (r - 1) := by
    calc
      (roots.biUnion (fun z ↦ z.2)).card ≤ ∑ z ∈ roots, z.2.card :=
        Finset.card_biUnion_le
      _ = roots.card * (r - 1) := by
        apply Finset.sum_const_nat hroot
  have hunion' : (roots.biUnion (fun z ↦ z.2)).card ≤ h * (r - 1) :=
    hunion.trans (Nat.mul_le_mul_right (r - 1) hroots)
  rw [cleanColoredVertices_eq_sdiff_biUnion,
    Finset.card_sdiff_of_subset (Finset.subset_univ _)]
  simpa using Nat.sub_le_sub_left hunion' n

lemma card_coloredRootFamilies_le (u n r h : ℕ) :
    (coloredRootFamilies u n r h).card ≤
      (h + 1) *
        (((Finset.univ : Finset (Fin u)) ×ˢ
          uniformEdges n (r - 1)).card + 1) ^ h := by
  classical
  let U := (Finset.univ : Finset (Fin u)) ×ˢ uniformEdges n (r - 1)
  have hsub : coloredRootFamilies u n r h ⊆
      (Finset.range (h + 1)).biUnion fun i ↦ U.powersetCard i := by
    intro roots hroots
    have hm := mem_coloredRootFamilies.mp hroots
    apply Finset.mem_biUnion.mpr
    exact ⟨roots.card, Finset.mem_range.mpr (by omega),
      Finset.mem_powersetCard.mpr ⟨hm.1, rfl⟩⟩
  calc
    (coloredRootFamilies u n r h).card ≤
        ((Finset.range (h + 1)).biUnion fun i ↦ U.powersetCard i).card :=
      Finset.card_le_card hsub
    _ ≤ ∑ i ∈ Finset.range (h + 1), (U.powersetCard i).card :=
      Finset.card_biUnion_le
    _ ≤ ∑ _i ∈ Finset.range (h + 1), (U.card + 1) ^ h := by
      apply Finset.sum_le_sum
      intro i hi
      rw [Finset.card_powersetCard]
      have hih : i ≤ h := by simpa using Finset.mem_range.mp hi
      exact (Nat.choose_le_pow _ _).trans
        ((Nat.pow_le_pow_left (Nat.le_succ _) _).trans
          (Nat.pow_le_pow_right (by omega) hih))
    _ = (h + 1) * (U.card + 1) ^ h := by simp

lemma coloredCommonMean_lower_of_mem
    {roots : Finset (ColoredRoot u n)}
    (p : Set.Icc (0 : ℝ) 1)
    (hroots : roots ∈ coloredRootFamilies u n r h) :
    ((n - h * (r - 1) : ℕ) : ℝ) * (p : ℝ) ^ h ≤
      coloredCommonMean n roots p := by
  have hroot := coloredRoot_card_of_mem hroots
  have hcleanNat := cleanColoredVertices_card_lower hroot
    (mem_coloredRootFamilies.mp hroots).2
  have hclean : ((n - h * (r - 1) : ℕ) : ℝ) ≤
      (cleanColoredVertices n roots).card := by exact_mod_cast hcleanNat
  have hpow : (p : ℝ) ^ h ≤ (p : ℝ) ^ roots.card :=
    pow_le_pow_of_le_one p.property.1 p.property.2
      (mem_coloredRootFamilies.mp hroots).2
  unfold coloredCommonMean
  exact mul_le_mul hclean hpow (pow_nonneg p.property.1 _) (by positivity)

/-- Any fixed finite avoidance budget is eventually smaller than half of
every coloured common-neighbour mean.  This is the uniform quantitative
input for greedy embeddings of fixed coloured patterns. -/
theorem eventually_fixed_le_half_coloredCommonMean
    (u r h D v : ℕ) (hD : 0 < D) (hhD : h < D) :
    ∀ᶠ n : ℕ in Filter.atTop,
      ∀ hn : 0 < n, ∀ roots,
      ∀ hroots : roots ∈ coloredRootFamilies u n r h,
        (v : ℝ) ≤ coloredCommonMean n roots
          (Erdos722.Reserve.reserveProbabilityIcc n D hn) / 2 := by
  let a : ℝ := 1 - (h : ℝ) / (D : ℝ)
  have ha : 0 < a := by
    dsimp [a]
    have hDr : (0 : ℝ) < D := by exact_mod_cast hD
    have hhDr : (h : ℝ) < D := by exact_mod_cast hhD
    exact sub_pos.mpr ((div_lt_one hDr).mpr hhDr)
  have hrpowT : Filter.Tendsto (fun n : ℕ ↦ (n : ℝ) ^ a)
      Filter.atTop Filter.atTop :=
    (tendsto_rpow_atTop ha).comp tendsto_natCast_atTop_atTop
  have hquarter : Filter.Tendsto (fun n : ℕ ↦ (n : ℝ) ^ a / 4)
      Filter.atTop Filter.atTop :=
    hrpowT.atTop_div_const (by norm_num)
  have hgrow : ∀ᶠ n : ℕ in Filter.atTop,
      (v : ℝ) ≤ (n : ℝ) ^ a / 4 :=
    hquarter.eventually_ge_atTop v
  filter_upwards [hgrow,
    Filter.eventually_ge_atTop (max 1 (2 * (h * (r - 1))))] with n hnGrow hnLarge
  intro hn roots hroots
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hbaseNat : 2 * (h * (r - 1)) ≤ n :=
    (le_max_right 1 (2 * (h * (r - 1)))).trans hnLarge
  have hbase : (n : ℝ) / 2 ≤ ((n - h * (r - 1) : ℕ) : ℝ) := by
    rw [Nat.cast_sub (by omega : h * (r - 1) ≤ n)]
    have hbaseCast : (2 : ℝ) * ((h * (r - 1) : ℕ) : ℝ) ≤ n := by
      exact_mod_cast hbaseNat
    linarith
  have hph : Erdos722.Reserve.reserveProbability n D ^ h =
      (n : ℝ) ^ (-((h : ℝ) / (D : ℝ))) :=
    Erdos722.Reserve.reserveProbability_pow_nat hn hD h
  have hrpow : (n : ℝ) *
      (n : ℝ) ^ (-((h : ℝ) / (D : ℝ))) = (n : ℝ) ^ a := by
    calc
      (n : ℝ) * (n : ℝ) ^ (-((h : ℝ) / (D : ℝ))) =
          (n : ℝ) ^ (1 : ℝ) *
            (n : ℝ) ^ (-((h : ℝ) / (D : ℝ))) := by
        rw [Real.rpow_one]
      _ = (n : ℝ) ^ ((1 : ℝ) + -((h : ℝ) / (D : ℝ))) :=
        (Real.rpow_add hnR _ _).symm
      _ = (n : ℝ) ^ a := by congr 1
  have hmeanBase : (n : ℝ) ^ a / 2 ≤
      ((n - h * (r - 1) : ℕ) : ℝ) *
        Erdos722.Reserve.reserveProbability n D ^ h := by
    rw [hph]
    calc
      (n : ℝ) ^ a / 2 = ((n : ℝ) / 2) *
          (n : ℝ) ^ (-((h : ℝ) / (D : ℝ))) := by
        rw [← hrpow]
        ring
      _ ≤ ((n - h * (r - 1) : ℕ) : ℝ) *
          (n : ℝ) ^ (-((h : ℝ) / (D : ℝ))) := by
        exact mul_le_mul_of_nonneg_right hbase (Real.rpow_nonneg hnR.le _)
  have hmean := coloredCommonMean_lower_of_mem
    (Erdos722.Reserve.reserveProbabilityIcc n D hn) hroots
  have hquarterMean : (n : ℝ) ^ a / 4 ≤
      coloredCommonMean n roots
        (Erdos722.Reserve.reserveProbabilityIcc n D hn) / 2 := by
    have hpVal :
        ((Erdos722.Reserve.reserveProbabilityIcc n D hn :
          Set.Icc (0 : ℝ) 1) : ℝ) =
          Erdos722.Reserve.reserveProbability n D := rfl
    rw [hpVal] at hmean
    linarith
  exact hnGrow.trans hquarterMean

theorem coloredTail_sum_lt_one_of_scalar_bound
    (u n r h : ℕ) (p : Set.Icc (0 : ℝ) 1)
    (hscalar :
      ((coloredRootFamilies u n r h).card : ℝ) * 2 *
          Real.exp (-(((n - h * (r - 1) : ℕ) : ℝ) *
            (p : ℝ) ^ h) / 10) < 1) :
    ∑ roots ∈ coloredRootFamilies u n r h,
      (Real.exp (-(coloredCommonMean n roots p) / 10) +
        Real.exp (-(coloredCommonMean n roots p) / 5)) < 1 := by
  let M : ℝ := ((n - h * (r - 1) : ℕ) : ℝ) * (p : ℝ) ^ h
  have hM : 0 ≤ M := mul_nonneg (by positivity) (pow_nonneg p.property.1 _)
  calc
    (∑ roots ∈ coloredRootFamilies u n r h,
        (Real.exp (-(coloredCommonMean n roots p) / 10) +
          Real.exp (-(coloredCommonMean n roots p) / 5))) ≤
        ∑ _roots ∈ coloredRootFamilies u n r h,
          (2 * Real.exp (-M / 10)) := by
      apply Finset.sum_le_sum
      intro roots hroots
      have hm := coloredCommonMean_lower_of_mem p hroots
      have hfirst : Real.exp (-(coloredCommonMean n roots p) / 10) ≤
          Real.exp (-M / 10) := by
        apply Real.exp_le_exp.mpr
        linarith
      have hsecond : Real.exp (-(coloredCommonMean n roots p) / 5) ≤
          Real.exp (-M / 10) := by
        apply Real.exp_le_exp.mpr
        linarith
      linarith
    _ = ((coloredRootFamilies u n r h).card : ℝ) * 2 *
        Real.exp (-M / 10) := by simp; ring
    _ < 1 := by simpa [M] using hscalar

/-- For fixed numbers of colours and roots, the scalar union bound needed
for simultaneous coloured typicality holds at density `n⁻¹˰ᴰ`, provided the
number `h` of imposed coloured faces is strictly smaller than `D`. -/
theorem eventually_colored_scalar_bound
    (u r h D : ℕ) (hD : 0 < D) (hhD : h < D) :
    ∀ᶠ n : ℕ in Filter.atTop,
      ((coloredRootFamilies u n r h).card : ℝ) * 2 *
          Real.exp (-(((n - h * (r - 1) : ℕ) : ℝ) *
            Erdos722.Reserve.reserveProbability n D ^ h) / 10) < 1 := by
  let P := r * h
  let a : ℝ := 1 - (h : ℝ) / (D : ℝ)
  let C₀ : ℝ := 2 * (h + 1) * (u + 1) ^ h
  have ha : 0 < a := by
    dsimp [a]
    have hDr : (0 : ℝ) < D := by exact_mod_cast hD
    have hhDr : (h : ℝ) < D := by exact_mod_cast hhD
    exact sub_pos.mpr ((div_lt_one hDr).mpr hhDr)
  have hdecay := Erdos722.Reserve.tendsto_pow_mul_exp_neg_rpow_atTop
    P ha (by norm_num : (0 : ℝ) < 1 / 20)
  have hconst : Filter.Tendsto
      (fun x : ℝ ↦ C₀ * (x ^ P * Real.exp (-(1 / 20 : ℝ) * x ^ a)))
      Filter.atTop (nhds 0) := by
    have hC₀ : Filter.Tendsto (fun _ : ℝ ↦ C₀)
        Filter.atTop (nhds C₀) := tendsto_const_nhds
    simpa only [mul_zero] using hC₀.mul hdecay
  have hnat := hconst.comp tendsto_natCast_atTop_atTop
  have hsmall : ∀ᶠ n : ℕ in Filter.atTop,
      C₀ * (((n : ℝ) ^ P) *
        Real.exp (-(1 / 20 : ℝ) * (n : ℝ) ^ a)) < 1 :=
    (tendsto_order.1 hnat).2 _ (by norm_num)
  filter_upwards [hsmall,
    Filter.eventually_ge_atTop (max 1 (2 * (h * (r - 1))))] with n hnsmall hnlarge
  have hn : 0 < n :=
    lt_of_lt_of_le (by omega : 0 < 1) (le_trans (le_max_left _ _) hnlarge)
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hnOne : 1 ≤ n := hn
  have hface : (uniformEdges n (r - 1)).card ≤ n ^ r := by
    rw [show (uniformEdges n (r - 1)).card = Nat.choose n (r - 1) by
      simp [uniformEdges]]
    calc
      Nat.choose n (r - 1) ≤ n ^ (r - 1) := Nat.choose_le_pow _ _
      _ ≤ n ^ r := Nat.pow_le_pow_right hn (by omega)
  let U := (Finset.univ : Finset (Fin u)) ×ˢ uniformEdges n (r - 1)
  have hU : U.card + 1 ≤ (u + 1) * n ^ r := by
    dsimp [U]
    rw [Finset.card_product, Finset.card_univ, Fintype.card_fin]
    have hone : 1 ≤ n ^ r := one_le_pow₀ hnOne
    nlinarith
  have hrootNat : (coloredRootFamilies u n r h).card ≤
      (h + 1) * ((u + 1) ^ h * n ^ P) := by
    calc
      (coloredRootFamilies u n r h).card ≤
          (h + 1) * (U.card + 1) ^ h := by
        simpa [U] using card_coloredRootFamilies_le u n r h
      _ ≤ (h + 1) * ((u + 1) * n ^ r) ^ h := by
        exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hU h)
      _ = (h + 1) * ((u + 1) ^ h * n ^ P) := by
        rw [mul_pow, ← pow_mul]
  have hroot : ((coloredRootFamilies u n r h).card : ℝ) * 2 ≤
      C₀ * (n : ℝ) ^ P := by
    have hrootCast : ((coloredRootFamilies u n r h).card : ℝ) ≤
        (((h + 1) * ((u + 1) ^ h * n ^ P) : ℕ) : ℝ) := by
      exact_mod_cast hrootNat
    calc
      ((coloredRootFamilies u n r h).card : ℝ) * 2 ≤
          (((h + 1) * ((u + 1) ^ h * n ^ P) : ℕ) : ℝ) * 2 :=
        mul_le_mul_of_nonneg_right hrootCast (by norm_num)
      _ = C₀ * (n : ℝ) ^ P := by
        push_cast
        dsimp [C₀]
        ring
  have hbaseNat : 2 * (h * (r - 1)) ≤ n :=
    (le_max_right 1 (2 * (h * (r - 1)))).trans hnlarge
  have hbase : (n : ℝ) / 2 ≤ ((n - h * (r - 1) : ℕ) : ℝ) := by
    rw [Nat.cast_sub (by omega : h * (r - 1) ≤ n)]
    have hbaseCast : (2 : ℝ) * ((h * (r - 1) : ℕ) : ℝ) ≤ n := by
      exact_mod_cast hbaseNat
    linarith
  have hph : Erdos722.Reserve.reserveProbability n D ^ h =
      (n : ℝ) ^ (-((h : ℝ) / (D : ℝ))) :=
    Erdos722.Reserve.reserveProbability_pow_nat hn hD h
  have hrpow : (n : ℝ) *
      (n : ℝ) ^ (-((h : ℝ) / (D : ℝ))) = (n : ℝ) ^ a := by
    calc
      (n : ℝ) * (n : ℝ) ^ (-((h : ℝ) / (D : ℝ))) =
          (n : ℝ) ^ (1 : ℝ) *
            (n : ℝ) ^ (-((h : ℝ) / (D : ℝ))) := by
        rw [Real.rpow_one]
      _ = (n : ℝ) ^ ((1 : ℝ) + -((h : ℝ) / (D : ℝ))) :=
        (Real.rpow_add hnR _ _).symm
      _ = (n : ℝ) ^ a := by congr 1
  have hmean : (1 / 2 : ℝ) * (n : ℝ) ^ a ≤
      ((n - h * (r - 1) : ℕ) : ℝ) *
        Erdos722.Reserve.reserveProbability n D ^ h := by
    rw [hph]
    calc
      (1 / 2 : ℝ) * (n : ℝ) ^ a =
          ((n : ℝ) / 2) *
            (n : ℝ) ^ (-((h : ℝ) / (D : ℝ))) := by
        rw [← hrpow]
        ring
      _ ≤ ((n - h * (r - 1) : ℕ) : ℝ) *
          (n : ℝ) ^ (-((h : ℝ) / (D : ℝ))) := by
        exact mul_le_mul_of_nonneg_right hbase (Real.rpow_nonneg hnR.le _)
  have hexp : Real.exp (-(((n - h * (r - 1) : ℕ) : ℝ) *
        Erdos722.Reserve.reserveProbability n D ^ h) / 10) ≤
      Real.exp (-(1 / 20 : ℝ) * (n : ℝ) ^ a) := by
    apply Real.exp_le_exp.mpr
    linarith
  calc
    ((coloredRootFamilies u n r h).card : ℝ) * 2 *
        Real.exp (-(((n - h * (r - 1) : ℕ) : ℝ) *
          Erdos722.Reserve.reserveProbability n D ^ h) / 10) ≤
        (C₀ * (n : ℝ) ^ P) *
          Real.exp (-(1 / 20 : ℝ) * (n : ℝ) ^ a) :=
      mul_le_mul hroot hexp (Real.exp_nonneg _) (by positivity)
    _ = C₀ * ((n : ℝ) ^ P *
        Real.exp (-(1 / 20 : ℝ) * (n : ℝ) ^ a)) := by ring
    _ < 1 := hnsmall

/-- Upper coloured typicality at density `n⁻¹˰ᴰ` implies the
power-cleared maximum `(r-1)`-degree estimate in every colour. -/
theorem coloredTypical_localDegree_power_bound
    {u n r h D : ℕ} (hn : 0 < n) (hr : 0 < r)
    (hh : 0 < h) (hD : 0 < D)
    (ω : (Fin u × {e // e ∈ uniformEdges n r}) → Bool)
    (htyp : ∀ roots, ∀ hroots : roots ∈ coloredRootFamilies u n r h,
      coloredCommonMean n roots
              (Erdos722.Reserve.reserveProbabilityIcc n D hn) / 2 <
            Erdos722.Probability.finiteRandomSum
              (fun x ↦ coloredCommonNeighborIndicator u n r roots hr
                (coloredRoot_card_of_mem hroots) x) ω ∧
      Erdos722.Probability.finiteRandomSum
              (fun x ↦ coloredCommonNeighborIndicator u n r roots hr
                (coloredRoot_card_of_mem hroots) x) ω <
            2 * coloredCommonMean n roots
              (Erdos722.Reserve.reserveProbabilityIcc n D hn)) :
    ∀ i I, I.card = r - 1 →
      ((sampledColorEdges u n r ω i).filter fun e ↦ I ⊆ e).card ^ D ≤
        2 ^ D * n ^ (D - 1) := by
  intro i I hI
  have hdeg := coloredTypical_localDegree_upper hr hh
    (Erdos722.Reserve.reserveProbabilityIcc n D hn) ω htyp i I hI
  have hpow :
      ((((sampledColorEdges u n r ω i).filter
        fun e ↦ I ⊆ e).card : ℕ) : ℝ) ^ D ≤
        (2 * n * Erdos722.Reserve.reserveProbability n D) ^ D := by
    exact pow_le_pow_left₀ (by positivity) hdeg.le D
  have hnreal : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  have hident :
      (2 * (n : ℝ) * Erdos722.Reserve.reserveProbability n D) ^ D =
        ((2 ^ D * n ^ (D - 1) : ℕ) : ℝ) := by
    have hnPow : (n : ℝ) ^ D * (n : ℝ)⁻¹ =
        (n : ℝ) ^ (D - 1) := by
      have hDs : D = (D - 1) + 1 := by omega
      nth_rw 1 [hDs]
      rw [pow_succ]
      field_simp
    rw [mul_pow, mul_pow,
      Erdos722.Reserve.reserveProbability_pow hn hD]
    push_cast
    rw [mul_assoc, hnPow]
  rw [hident] at hpow
  exact_mod_cast hpow

/-- A deterministic outcome simultaneously realizes all fixed-size
coloured common-neighbour estimates, with each colour individually sparse. -/
theorem exists_colored_typical_sample
    {u n r h D : ℕ} (hn : 0 < n) (hr : 0 < r)
    (hh : 0 < h) (hD : 0 < D)
    (hscalar :
      ((coloredRootFamilies u n r h).card : ℝ) * 2 *
          Real.exp (-(((n - h * (r - 1) : ℕ) : ℝ) *
            Erdos722.Reserve.reserveProbability n D ^ h) / 10) < 1) :
    ∃ ω : (Fin u × {e // e ∈ uniformEdges n r}) → Bool,
      (∀ roots, ∀ hroots : roots ∈ coloredRootFamilies u n r h,
        coloredCommonMean n roots
                (Erdos722.Reserve.reserveProbabilityIcc n D hn) / 2 <
              Erdos722.Probability.finiteRandomSum
                (fun x ↦ coloredCommonNeighborIndicator u n r roots hr
                  (coloredRoot_card_of_mem hroots) x) ω ∧
        Erdos722.Probability.finiteRandomSum
                (fun x ↦ coloredCommonNeighborIndicator u n r roots hr
                  (coloredRoot_card_of_mem hroots) x) ω <
              2 * coloredCommonMean n roots
                (Erdos722.Reserve.reserveProbabilityIcc n D hn)) ∧
      (∀ i, sampledColorEdges u n r ω i ⊆ uniformEdges n r) ∧
      (∀ i I, I.card = r - 1 →
        ((sampledColorEdges u n r ω i).filter fun e ↦ I ⊆ e).card ^ D ≤
          2 ^ D * n ^ (D - 1)) := by
  let p := Erdos722.Reserve.reserveProbabilityIcc n D hn
  have htail :
      ∑ roots ∈ coloredRootFamilies u n r h,
        (Real.exp (-(coloredCommonMean n roots p) / 10) +
          Real.exp (-(coloredCommonMean n roots p) / 5)) < 1 := by
    apply coloredTail_sum_lt_one_of_scalar_bound
    simpa [p, Erdos722.Reserve.reserveProbabilityIcc] using hscalar
  obtain ⟨ω, htyp⟩ := exists_simultaneously_coloredTypical
    u n r h hr p htail
  refine ⟨ω, ?_, fun i ↦ sampledColorEdges_subset ω i, ?_⟩
  · simpa [p] using htyp
  · exact coloredTypical_localDegree_power_bound hn hr hh hD ω (by
      simpa [p] using htyp)

/-- Eventual source-facing form of the coloured sampling lemma. -/
theorem eventually_exists_colored_typical_sample
    (u r h D : ℕ) (hr : 0 < r) (hh : 0 < h)
    (hD : 0 < D) (hhD : h < D) :
    ∀ᶠ n : ℕ in Filter.atTop,
      ∃ hn : 0 < n,
      ∃ ω : (Fin u × {e // e ∈ uniformEdges n r}) → Bool,
        (∀ roots, ∀ hroots : roots ∈ coloredRootFamilies u n r h,
          coloredCommonMean n roots
                  (Erdos722.Reserve.reserveProbabilityIcc n D hn) / 2 <
                Erdos722.Probability.finiteRandomSum
                  (fun x ↦ coloredCommonNeighborIndicator u n r roots hr
                    (coloredRoot_card_of_mem hroots) x) ω ∧
          Erdos722.Probability.finiteRandomSum
                  (fun x ↦ coloredCommonNeighborIndicator u n r roots hr
                    (coloredRoot_card_of_mem hroots) x) ω <
                2 * coloredCommonMean n roots
                  (Erdos722.Reserve.reserveProbabilityIcc n D hn)) ∧
        (∀ i, sampledColorEdges u n r ω i ⊆ uniformEdges n r) ∧
        (∀ i I, I.card = r - 1 →
          ((sampledColorEdges u n r ω i).filter fun e ↦ I ⊆ e).card ^ D ≤
            2 ^ D * n ^ (D - 1)) := by
  filter_upwards [eventually_colored_scalar_bound u r h D hD hhD,
    Filter.eventually_ge_atTop 1] with n hscalar hn
  exact ⟨by omega, exists_colored_typical_sample (by omega) hr hh hD hscalar⟩

end

end Erdos722.ColoredTypicality
