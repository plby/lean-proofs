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

import ErdosProblems.Erdos636.AntiConcentration
import ErdosProblems.Erdos636.AugmentationIdentity
import ErdosProblems.Erdos636.AugmentationFull
import ErdosProblems.Erdos636.AugmentationPartial
import ErdosProblems.Erdos636.NestedUniform
import ErdosProblems.Erdos636.Switching
import ErdosProblems.Erdos636.TuranEdges
import ErdosProblems.Erdos88.Foundations
import ErdosProblems.Erdos88.BooleanSlices

/-!
# The deterministic augmentation step for Erdős Problem 636

The probabilistic part of Kwan--Sudakov's augmentation lemma produces a
finite set of retained base configurations.  For every retained base it
also produces many extensions with distinct edge counts.  All edge counts
arising from one base lie in a short interval, while the interval centres
for different bases are separated by more than twice the interval radius.

This file proves the exact graph-facing counting statement needed after
that construction.  It deliberately works with actual induced edge counts,
rather than an abstract surrogate.  Thus the conclusion is immediately a
fixed-order induced-subgraph spectrum bound.

The name `balanced` refers to the two-sided error window around each centre.
In the paper that window is furnished by balanced fixed-size sampling.
-/

open Classical SimpleGraph
open scoped BigOperators

namespace Erdos636
namespace Augmentation

universe u v

noncomputable section

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {ι : Type v} [DecidableEq ι]

/-- Induced edge count is monotone under inclusion of vertex sets. -/
lemma inducedEdges_mono (G : SimpleGraph V) {S T : Finset V} (hST : S ⊆ T) :
    Erdos88.inducedEdges G S ≤ Erdos88.inducedEdges G T := by
  rw [Erdos88.inducedEdges_eq_card_filter,
    Erdos88.inducedEdges_eq_card_filter]
  apply Finset.card_le_card
  intro e he
  rw [Finset.mem_filter] at he ⊢
  exact ⟨he.1, fun v hv ↦ hST (he.2 hv)⟩

/-- The exact number of new induced edges created by adjoining a vertex cell
`x` to a base `U`.  This subtraction is exact because induced edge count is
monotone under vertex-set inclusion. -/
def increment (G : SimpleGraph V) (U x : Finset V) : ℕ :=
  Erdos88.inducedEdges G (U ∪ x) - Erdos88.inducedEdges G U

/-- For a disjoint augmentation cell, the final edge count is the base edge
count plus the augmentation increment. -/
lemma inducedEdges_union_eq_add_increment
    (G : SimpleGraph V) {U x : Finset V} (_hUx : Disjoint U x) :
    Erdos88.inducedEdges G (U ∪ x) =
      Erdos88.inducedEdges G U + increment G U x := by
  rw [increment]
  have hmono := inducedEdges_mono G (S := U) (T := U ∪ x)
    Finset.subset_union_left
  omega

/-- Edge counts obtained by adjoining one of the extensions in `X` to the
base vertex set `U`. -/
def edgeValues (G : SimpleGraph V) (U : Finset V)
    (X : Finset (Finset V)) : Finset ℕ :=
  X.image fun x ↦ Erdos88.inducedEdges G (U ∪ x)

@[simp] lemma mem_edgeValues {G : SimpleGraph V} {U : Finset V}
    {X : Finset (Finset V)} {m : ℕ} :
    m ∈ edgeValues G U X ↔
      ∃ x ∈ X, Erdos88.inducedEdges G (U ∪ x) = m := by
  simp [edgeValues]

/-- All edge counts of induced subgraphs having exactly `q` vertices.  This
is kept local to the augmentation module so that the module does not import
the final Problem 636 file. -/
def fixedOrderEdgeValues (G : SimpleGraph V) (q : ℕ) : Finset ℕ :=
  (Finset.univ.filter fun S : Finset V ↦ S.card = q).image
    (Erdos88.inducedEdges G)

@[simp] lemma mem_fixedOrderEdgeValues {G : SimpleGraph V} {q m : ℕ} :
    m ∈ fixedOrderEdgeValues G q ↔
      ∃ S : Finset V, S.card = q ∧ Erdos88.inducedEdges G S = m := by
  simp [fixedOrderEdgeValues]

/-- If every augmented set has order `q`, all of its edge values belong to
the order-`q` spectrum. -/
lemma edgeValues_subset_fixedOrderEdgeValues
    (G : SimpleGraph V) (U : Finset V) (X : Finset (Finset V)) (q : ℕ)
    (horder : ∀ x ∈ X, (U ∪ x).card = q) :
    edgeValues G U X ⊆ fixedOrderEdgeValues G q := by
  intro m hm
  obtain ⟨x, hx, rfl⟩ := mem_edgeValues.mp hm
  exact mem_fixedOrderEdgeValues.mpr ⟨U ∪ x, horder x hx, rfl⟩

/-- The image has the full extension-family cardinality when distinct
extensions give distinct augmented edge counts. -/
lemma card_edgeValues_eq
    (G : SimpleGraph V) (U : Finset V) (X : Finset (Finset V))
    (hinj : Set.InjOn
      (fun x ↦ Erdos88.inducedEdges G (U ∪ x)) (X : Set (Finset V))) :
    (edgeValues G U X).card = X.card := by
  rw [edgeValues, Finset.card_image_iff.mpr]
  intro x hx y hy hxy
  exact hinj (by simpa using hx) (by simpa using hy) hxy

/-- Two integer intervals of radius `R` whose centres are more than `2R`
apart are disjoint.  This is the numerical core of the augmentation count. -/
lemma ne_of_mem_separated_windows {m n : ℕ} {c d : ℤ} {R : ℕ}
    (hm : |(m : ℤ) - c| ≤ R) (hn : |(n : ℤ) - d| ≤ R)
    (hsep : (2 * R : ℕ) < |c - d|) : m ≠ n := by
  intro hmn
  subst n
  have htriangle : |c - d| ≤ |c - (m : ℤ)| + |(m : ℤ) - d| := by
    calc
      |c - d| = |(c - (m : ℤ)) + ((m : ℤ) - d)| := by ring_nf
      _ ≤ |c - (m : ℤ)| + |(m : ℤ) - d| := abs_add_le _ _
  have hm' : |c - (m : ℤ)| ≤ (R : ℤ) := by
    simpa [abs_sub_comm] using hm
  have hn' : |(m : ℤ) - d| ≤ (R : ℤ) := hn
  have hupper : |c - d| ≤ (2 * R : ℕ) := by
    have hupper' : |c - d| ≤ (2 : ℤ) * R := by
      calc
        |c - d| ≤ |c - (m : ℤ)| + |(m : ℤ) - d| := htriangle
        _ ≤ (R : ℤ) + R := add_le_add hm' hn'
        _ = (2 : ℤ) * R := by ring
    exact_mod_cast hupper'
  exact (not_lt_of_ge hupper) hsep

/-- Balanced windows around pairwise separated centres give pairwise
disjoint edge-value sets. -/
lemma edgeValues_pairwiseDisjoint_of_windows
    (G : SimpleGraph V) (J : Finset ι)
    (U : ι → Finset V) (X : ι → Finset (Finset V))
    (center : ι → ℤ) (R : ℕ)
    (hwindow : ∀ i ∈ J, ∀ m ∈ edgeValues G (U i) (X i),
      |(m : ℤ) - center i| ≤ R)
    (hsep : ∀ i ∈ J, ∀ j ∈ J, i ≠ j →
      (2 * R : ℕ) < |center i - center j|) :
    (J : Set ι).PairwiseDisjoint fun i ↦ edgeValues G (U i) (X i) := by
  intro i hi j hj hij
  change Disjoint (edgeValues G (U i) (X i)) (edgeValues G (U j) (X j))
  rw [Finset.disjoint_left]
  intro m hmi hmj
  exact ne_of_mem_separated_windows
    (hwindow i hi m hmi) (hwindow j hj m hmj) (hsep i hi j hj hij) rfl

/-- Real-centred version of separated balanced windows.  This is convenient
when the centres come from the real-valued switching path. -/
lemma edgeValues_pairwiseDisjoint_of_real_windows
    (G : SimpleGraph V) (J : Finset ι)
    (U : ι → Finset V) (X : ι → Finset (Finset V))
    (center : ι → ℝ) (R : ℝ)
    (hwindow : ∀ i ∈ J, ∀ m ∈ edgeValues G (U i) (X i),
      |(m : ℝ) - center i| ≤ R)
    (hsep : ∀ i ∈ J, ∀ j ∈ J, i ≠ j →
      2 * R < |center i - center j|) :
    (J : Set ι).PairwiseDisjoint fun i ↦ edgeValues G (U i) (X i) := by
  intro i hi j hj hij
  change Disjoint (edgeValues G (U i) (X i)) (edgeValues G (U j) (X j))
  rw [Finset.disjoint_left]
  intro m hmi hmj
  have hwi := hwindow i hi m hmi
  have hwj := hwindow j hj m hmj
  have htriangle : |center i - center j| ≤
      |center i - (m : ℝ)| + |(m : ℝ) - center j| := by
    calc
      |center i - center j| =
          |(center i - (m : ℝ)) + ((m : ℝ) - center j)| := by ring_nf
      _ ≤ |center i - (m : ℝ)| + |(m : ℝ) - center j| := abs_add_le _ _
  have hupper : |center i - center j| ≤ 2 * R := by
    calc
      |center i - center j| ≤
          |center i - (m : ℝ)| + |(m : ℝ) - center j| := htriangle
      _ ≤ R + R := add_le_add (by simpa [abs_sub_comm] using hwi) hwj
      _ = 2 * R := by ring
  exact ((not_lt_of_ge hupper) (hsep i hi j hj hij)).elim

/-- Real-window version of the deterministic augmentation sum. -/
theorem sum_card_extensions_le_fixedOrderEdgeValues_real_windows
    (G : SimpleGraph V) (J : Finset ι)
    (U : ι → Finset V) (X : ι → Finset (Finset V))
    (q : ℕ) (R : ℝ) (center : ι → ℝ)
    (horder : ∀ i ∈ J, ∀ x ∈ X i, (U i ∪ x).card = q)
    (hinj : ∀ i ∈ J, Set.InjOn
      (fun x ↦ Erdos88.inducedEdges G (U i ∪ x))
      (X i : Set (Finset V)))
    (hwindow : ∀ i ∈ J, ∀ m ∈ edgeValues G (U i) (X i),
      |(m : ℝ) - center i| ≤ R)
    (hsep : ∀ i ∈ J, ∀ j ∈ J, i ≠ j →
      2 * R < |center i - center j|) :
    ∑ i ∈ J, (X i).card ≤ (fixedOrderEdgeValues G q).card := by
  let E : ι → Finset ℕ := fun i ↦ edgeValues G (U i) (X i)
  have hdisj : (J : Set ι).PairwiseDisjoint E :=
    edgeValues_pairwiseDisjoint_of_real_windows
      G J U X center R hwindow hsep
  have hsub : J.biUnion E ⊆ fixedOrderEdgeValues G q := by
    intro m hm
    obtain ⟨i, hiJ, hmi⟩ := Finset.mem_biUnion.mp hm
    exact edgeValues_subset_fixedOrderEdgeValues G (U i) (X i) q
      (horder i hiJ) hmi
  calc
    ∑ i ∈ J, (X i).card = ∑ i ∈ J, (E i).card := by
      apply Finset.sum_congr rfl
      intro i hi
      exact (card_edgeValues_eq G (U i) (X i) (hinj i hi)).symm
    _ = (J.biUnion E).card := (Finset.card_biUnion hdisj).symm
    _ ≤ (fixedOrderEdgeValues G q).card := Finset.card_le_card hsub

/-- **Deterministic balanced augmentation theorem.**

For every retained base `i`, suppose the augmented edge-count map is
injective on its extension family and all resulting sets have the same
order `q`.  Suppose furthermore that the edge counts lie in a radius-`R`
window about `center i`, and distinct centres are more than `2R` apart.
Then the fixed-order spectrum contains the sum of all extension-family
cardinalities.

This is precisely the final multiplication step in the Kwan--Sudakov
augmentation package: the retained switching indices supply `J`, while the
anti-concentrated extra matching edges supply `X i`. -/
theorem sum_card_extensions_le_fixedOrderEdgeValues
    (G : SimpleGraph V) (J : Finset ι)
    (U : ι → Finset V) (X : ι → Finset (Finset V))
    (q R : ℕ) (center : ι → ℤ)
    (horder : ∀ i ∈ J, ∀ x ∈ X i, (U i ∪ x).card = q)
    (hinj : ∀ i ∈ J, Set.InjOn
      (fun x ↦ Erdos88.inducedEdges G (U i ∪ x))
      (X i : Set (Finset V)))
    (hwindow : ∀ i ∈ J, ∀ m ∈ edgeValues G (U i) (X i),
      |(m : ℤ) - center i| ≤ R)
    (hsep : ∀ i ∈ J, ∀ j ∈ J, i ≠ j →
      (2 * R : ℕ) < |center i - center j|) :
    ∑ i ∈ J, (X i).card ≤ (fixedOrderEdgeValues G q).card := by
  let E : ι → Finset ℕ := fun i ↦ edgeValues G (U i) (X i)
  have hdisj : (J : Set ι).PairwiseDisjoint E := by
    exact edgeValues_pairwiseDisjoint_of_windows G J U X center R hwindow hsep
  have hsub : J.biUnion E ⊆ fixedOrderEdgeValues G q := by
    intro m hm
    obtain ⟨i, hiJ, hmi⟩ := Finset.mem_biUnion.mp hm
    exact edgeValues_subset_fixedOrderEdgeValues G (U i) (X i) q
      (horder i hiJ) hmi
  calc
    ∑ i ∈ J, (X i).card = ∑ i ∈ J, (E i).card := by
      apply Finset.sum_congr rfl
      intro i hi
      exact (card_edgeValues_eq G (U i) (X i) (hinj i hi)).symm
    _ = (J.biUnion E).card := (Finset.card_biUnion hdisj).symm
    _ ≤ (fixedOrderEdgeValues G q).card := Finset.card_le_card hsub

/-- Uniform-cardinality form of balanced augmentation.  If each retained
base has at least `r` extensions, the spectrum contains at least
`|J| * r` distinct edge counts. -/
theorem card_mul_le_fixedOrderEdgeValues
    (G : SimpleGraph V) (J : Finset ι)
    (U : ι → Finset V) (X : ι → Finset (Finset V))
    (q R r : ℕ) (center : ι → ℤ)
    (horder : ∀ i ∈ J, ∀ x ∈ X i, (U i ∪ x).card = q)
    (hinj : ∀ i ∈ J, Set.InjOn
      (fun x ↦ Erdos88.inducedEdges G (U i ∪ x))
      (X i : Set (Finset V)))
    (hcard : ∀ i ∈ J, r ≤ (X i).card)
    (hwindow : ∀ i ∈ J, ∀ m ∈ edgeValues G (U i) (X i),
      |(m : ℤ) - center i| ≤ R)
    (hsep : ∀ i ∈ J, ∀ j ∈ J, i ≠ j →
      (2 * R : ℕ) < |center i - center j|) :
    J.card * r ≤ (fixedOrderEdgeValues G q).card := by
  calc
    J.card * r = ∑ _i ∈ J, r := by simp
    _ ≤ ∑ i ∈ J, (X i).card :=
      Finset.sum_le_sum fun i hi ↦ hcard i hi
    _ ≤ (fixedOrderEdgeValues G q).card :=
      sum_card_extensions_le_fixedOrderEdgeValues
        G J U X q R center horder hinj hwindow hsep

/-- Asymptotic-scale form of deterministic balanced augmentation.  If the
number of retained bases is at least `a * nZ` and every base has at least
`b * sqrt nD` distinct extensions, their separated windows contain at least
`a * b * nZ * sqrt nD` fixed-order edge counts. -/
theorem mul_mul_sqrt_le_fixedOrderEdgeValues
    (G : SimpleGraph V) (J : Finset ι)
    (U : ι → Finset V) (X : ι → Finset (Finset V))
    (q R nZ nD : ℕ) (a b : ℝ) (center : ι → ℤ)
    (_ha : 0 ≤ a) (hb : 0 ≤ b)
    (hJ : a * nZ ≤ J.card)
    (horder : ∀ i ∈ J, ∀ x ∈ X i, (U i ∪ x).card = q)
    (hinj : ∀ i ∈ J, Set.InjOn
      (fun x ↦ Erdos88.inducedEdges G (U i ∪ x))
      (X i : Set (Finset V)))
    (hcard : ∀ i ∈ J, b * Real.sqrt nD ≤ (X i).card)
    (hwindow : ∀ i ∈ J, ∀ m ∈ edgeValues G (U i) (X i),
      |(m : ℤ) - center i| ≤ R)
    (hsep : ∀ i ∈ J, ∀ j ∈ J, i ≠ j →
      (2 * R : ℕ) < |center i - center j|) :
    (a * b) * nZ * Real.sqrt nD ≤
      (fixedOrderEdgeValues G q).card := by
  have hscale : 0 ≤ b * Real.sqrt nD :=
    mul_nonneg hb (Real.sqrt_nonneg _)
  have hsum :
      ∑ i ∈ J, b * Real.sqrt nD ≤
        ∑ i ∈ J, ((X i).card : ℝ) :=
    Finset.sum_le_sum hcard
  have hspectrum :
      (∑ i ∈ J, ((X i).card : ℝ)) ≤
        ((fixedOrderEdgeValues G q).card : ℝ) := by
    exact_mod_cast sum_card_extensions_le_fixedOrderEdgeValues
      G J U X q R center horder hinj hwindow hsep
  calc
    (a * b) * (nZ : ℝ) * Real.sqrt nD =
        (a * nZ) * (b * Real.sqrt nD) := by ring
    _ ≤ (J.card : ℝ) * (b * Real.sqrt nD) :=
      mul_le_mul_of_nonneg_right hJ hscale
    _ = ∑ _i ∈ J, b * Real.sqrt nD := by simp
    _ ≤ ∑ i ∈ J, ((X i).card : ℝ) := hsum
    _ ≤ ((fixedOrderEdgeValues G q).card : ℝ) := hspectrum

/-- **Graph-increment form of deterministic balanced augmentation.**

This is the form closest to the output of the full-exposure argument.  Each
extension is disjoint from its base.  The genuine number of newly created
edges is injective within a retained base and lies in a balanced window
about `incrementCenter i`.  The corresponding *total* centres, obtained by
adding the base edge count, are separated.  Consequently the order-`q`
spectrum has at least `|J| * r` elements.

No edge-count identity is assumed: it follows internally from monotonicity
of induced edge count under adjoining vertices. -/
theorem card_mul_le_fixedOrderEdgeValues_of_increments
    (G : SimpleGraph V)
    (J : Finset ι) (U : ι → Finset V)
    (X : ι → Finset (Finset V))
    (q R r : ℕ) (incrementCenter : ι → ℤ)
    (hdisjoint : ∀ i ∈ J, ∀ x ∈ X i, Disjoint (U i) x)
    (horder : ∀ i ∈ J, ∀ x ∈ X i, (U i ∪ x).card = q)
    (hincrement : ∀ i ∈ J,
      Set.InjOn (increment G (U i)) (X i : Set (Finset V)))
    (hcard : ∀ i ∈ J, r ≤ (X i).card)
    (hwindow : ∀ i ∈ J, ∀ x ∈ X i,
      |(increment G (U i) x : ℤ) - incrementCenter i| ≤ R)
    (hsep : ∀ i ∈ J, ∀ j ∈ J, i ≠ j →
      (2 * R : ℕ) <
        |((Erdos88.inducedEdges G (U i) : ℤ) + incrementCenter i) -
          ((Erdos88.inducedEdges G (U j) : ℤ) + incrementCenter j)|) :
    J.card * r ≤ (fixedOrderEdgeValues G q).card := by
  let center : ι → ℤ := fun i ↦
    (Erdos88.inducedEdges G (U i) : ℤ) + incrementCenter i
  have hedgeInj : ∀ i ∈ J, Set.InjOn
      (fun x ↦ Erdos88.inducedEdges G (U i ∪ x))
      (X i : Set (Finset V)) := by
    intro i hi x hx y hy hxy
    apply hincrement i hi hx hy
    have hxid := inducedEdges_union_eq_add_increment G (hdisjoint i hi x hx)
    have hyid := inducedEdges_union_eq_add_increment G (hdisjoint i hi y hy)
    exact Nat.add_left_cancel (hxid.symm.trans (hxy.trans hyid))
  have hedgeWindow : ∀ i ∈ J, ∀ m ∈ edgeValues G (U i) (X i),
      |(m : ℤ) - center i| ≤ R := by
    intro i hi m hm
    obtain ⟨x, hx, rfl⟩ := mem_edgeValues.mp hm
    have hid := inducedEdges_union_eq_add_increment G (hdisjoint i hi x hx)
    have hw := hwindow i hi x hx
    dsimp only [center]
    rw [hid]
    push_cast
    simpa only [add_sub_add_left_eq_sub] using hw
  apply card_mul_le_fixedOrderEdgeValues G J U X q R r center
    horder hedgeInj hcard hedgeWindow
  intro i hi j hj hij
  exact hsep i hi j hj hij

/-- Quantitative real-scale version of the graph-increment theorem.  This
is the exact deterministic conclusion used by the balanced augmentation
package: linearly many switching states in `nZ`, each with square-root many
anti-concentrated extensions in `nD`, yield the product scale
`nZ * sqrt nD`. -/
theorem mul_mul_sqrt_le_fixedOrderEdgeValues_of_increments
    (G : SimpleGraph V)
    (J : Finset ι) (U : ι → Finset V)
    (X : ι → Finset (Finset V))
    (q R nZ nD : ℕ) (a b : ℝ) (incrementCenter : ι → ℤ)
    (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hJ : a * nZ ≤ J.card)
    (hdisjoint : ∀ i ∈ J, ∀ x ∈ X i, Disjoint (U i) x)
    (horder : ∀ i ∈ J, ∀ x ∈ X i, (U i ∪ x).card = q)
    (hincrement : ∀ i ∈ J,
      Set.InjOn (increment G (U i)) (X i : Set (Finset V)))
    (hcard : ∀ i ∈ J, b * Real.sqrt nD ≤ (X i).card)
    (hwindow : ∀ i ∈ J, ∀ x ∈ X i,
      |(increment G (U i) x : ℤ) - incrementCenter i| ≤ R)
    (hsep : ∀ i ∈ J, ∀ j ∈ J, i ≠ j →
      (2 * R : ℕ) <
        |((Erdos88.inducedEdges G (U i) : ℤ) + incrementCenter i) -
          ((Erdos88.inducedEdges G (U j) : ℤ) + incrementCenter j)|) :
    (a * b) * nZ * Real.sqrt nD ≤
      (fixedOrderEdgeValues G q).card := by
  let center : ι → ℤ := fun i ↦
    (Erdos88.inducedEdges G (U i) : ℤ) + incrementCenter i
  have hedgeInj : ∀ i ∈ J, Set.InjOn
      (fun x ↦ Erdos88.inducedEdges G (U i ∪ x))
      (X i : Set (Finset V)) := by
    intro i hi x hx y hy hxy
    apply hincrement i hi hx hy
    have hxid := inducedEdges_union_eq_add_increment G (hdisjoint i hi x hx)
    have hyid := inducedEdges_union_eq_add_increment G (hdisjoint i hi y hy)
    exact Nat.add_left_cancel (hxid.symm.trans (hxy.trans hyid))
  have hedgeWindow : ∀ i ∈ J, ∀ m ∈ edgeValues G (U i) (X i),
      |(m : ℤ) - center i| ≤ R := by
    intro i hi m hm
    obtain ⟨x, hx, rfl⟩ := mem_edgeValues.mp hm
    have hid := inducedEdges_union_eq_add_increment G (hdisjoint i hi x hx)
    have hw := hwindow i hi x hx
    dsimp only [center]
    rw [hid]
    push_cast
    simpa only [add_sub_add_left_eq_sub] using hw
  apply mul_mul_sqrt_le_fixedOrderEdgeValues G J U X q R nZ nD a b center
    ha hb hJ horder hedgeInj hcard hedgeWindow
  intro i hi j hj hij
  exact hsep i hi j hj hij

/-! ## The balanced local-limit input used during exposure -/

/-- A bounded integer population with positive linear centred variance has a
nonempty disjoint unequal-coefficient matching, and hence an explicit
balanced-slice point-mass bound.

This theorem is the complete bridge

`centred variance → disjoint pairs → PairEmbedding → Fourier decay → Esseen`

used in each collision estimate of the augmentation argument.  The matching
size remains in the conclusion, together with its quantitative lower bound,
so later applications can convert the displayed estimate to
`O(1 / sqrt |I|)` using their instance-specific variance lower bound. -/
theorem exists_matching_slice_point_probability_le
    {I : Type u} [Fintype I] [DecidableEq I]
    (S : Finset I) (coeff : I → ℤ) (B : ℕ) (eta mu c : ℝ)
    (s : ℕ) [Nonempty (Erdos88.Fourier.BoolSlice I s)]
    (hB : 1 ≤ B) (heta : 0 < eta) (hS : S.Nonempty)
    (hbounded : ∀ i ∈ S, |coeff i| ≤ (B : ℤ))
    (hcentered : ∑ i ∈ S, ((coeff i : ℝ) - mu) = 0)
    (hvariance : eta * (S.card : ℝ) ≤
      ∑ i ∈ S, ((coeff i : ℝ) - mu) ^ 2)
    (hc0 : 0 < c) (hc1 : c ≤ 1 / 2)
    (hsel : c * Fintype.card I ≤ s)
    (hunsel : c * Fintype.card I ≤ Fintype.card I - s) :
    ∃ M : Finset (Sym2 I),
      eta * (S.card : ℝ) ≤
        8 * (B : ℝ) ^ 2 * (M.card : ℝ) ∧
      ∀ x : ℝ,
        Erdos88.Fourier.finProbability (Erdos88.Fourier.BoolSlice I s)
            (fun omega ↦
              AntiConcentration.sliceLinear s (fun i ↦ (coeff i : ℝ)) omega = x) ≤
          16 * (2 * B) * Real.exp 1 *
            Real.sqrt (Real.pi /
              ((c ^ 3 / 256) * M.card / (4 * Real.pi ^ 2))) := by
  obtain ⟨M, hM, hgap, hMcard⟩ :=
    Pairing.exists_many_disjoint_coefficient_pairs
      S coeff B eta mu hbounded hcentered hvariance
  have hleftPos : 0 < eta * (S.card : ℝ) := by
    exact mul_pos heta (by exact_mod_cast Finset.card_pos.mpr hS)
  have hMpos : 0 < M.card := by
    by_contra hMzero
    have hz : M.card = 0 := Nat.eq_zero_of_not_pos hMzero
    rw [hz] at hMcard
    norm_num at hMcard
    exact (not_lt_of_ge hMcard) hleftPos
  let H : SimpleGraph I := Pairing.coefficientGraph S coeff
  let p : Erdos88.Fourier.PairEmbedding
      (PairEmbeddingAdapter.MatchingIndex M) I :=
    PairEmbeddingAdapter.pairEmbeddingOfEdgeMatching H M hM
  have hgaps := PairEmbeddingAdapter.coefficient_gap_real_of_edgeMatching
    H M hM coeff 1 (2 * (B : ℤ)) hgap
  refine ⟨M, hMcard, ?_⟩
  intro x
  have hanti := AntiConcentration.slice_point_probability_le_of_pairs
    p s (fun i ↦ (coeff i : ℝ)) c (2 * (B : ℝ))
      hc0 hc1 hsel hunsel (by exact_mod_cast (show 1 ≤ 2 * B by omega))
      (fun k ↦ by simpa [p] using (hgaps k).1)
      (fun k ↦ by simpa [p] using (hgaps k).2)
      (by simpa [PairEmbeddingAdapter.card_matchingIndex] using hMpos) x
  simpa [p, PairEmbeddingAdapter.card_matchingIndex] using hanti

/-! ## Collision thinning -/

/-- The graph joining distinct members of `X` which have the same value
under `f`.  Independent sets in this graph are precisely subfamilies on
which `f` is injective. -/
def valueCollisionGraph {A : Type*} (X : Finset A) {B : Type*}
    (f : A → B) : SimpleGraph {x // x ∈ X} :=
  SimpleGraph.mk
    (fun x y ↦ x ≠ y ∧ f x = f y)
    ⟨by
      intro x y h
      exact ⟨h.1.symm, h.2.symm⟩⟩
    ⟨by intro x h; exact h.1 rfl⟩

@[simp] lemma valueCollisionGraph_adj
    {A : Type*} {X : Finset A} {B : Type*} {f : A → B}
    {x y : {x // x ∈ X}} :
    (valueCollisionGraph X f).Adj x y ↔ x ≠ y ∧ f x = f y := by
  simp [valueCollisionGraph]

/-- Total collision edges can be thinned to an injective subfamily with the
exact Caro--Wei/Turán cardinal inequality.  This is the deterministic step
used after the first-moment collision estimates in both exposures. -/
theorem exists_injective_subfamily_card_sq_le
    {A : Type*} [DecidableEq A] (X : Finset A)
    {B : Type*} (f : A → B) :
    ∃ Y : Finset A, Y ⊆ X ∧ Set.InjOn f (Y : Set A) ∧
      X.card ^ 2 ≤ Y.card *
        (X.card + 2 * (valueCollisionGraph X f).edgeFinset.card) := by
  classical
  let H := valueCollisionGraph X f
  let : DecidableRel H.Adj := Classical.decRel _
  obtain ⟨S, hSind, hbound⟩ :=
    exists_indepSet_card_sq_le_card_mul_card_add_twice_edges H
  let Y : Finset A := S.image Subtype.val
  have hYsub : Y ⊆ X := by
    intro x hx
    obtain ⟨y, _hyS, rfl⟩ := Finset.mem_image.mp hx
    exact y.2
  have hYcard : Y.card = S.card := by
    change (S.image Subtype.val).card = S.card
    rw [Finset.card_image_iff.mpr]
    intro x _hx y _hy hxy
    exact Subtype.ext hxy
  have hYinj : Set.InjOn f (Y : Set A) := by
    intro x hx y hy hxy
    obtain ⟨x', hx'S, hx'⟩ := Finset.mem_image.mp hx
    obtain ⟨y', hy'S, hy'⟩ := Finset.mem_image.mp hy
    subst x
    subst y
    apply congrArg Subtype.val
    by_contra hne
    exact hSind hx'S hy'S hne
      (valueCollisionGraph_adj.mpr ⟨hne, hxy⟩)
  refine ⟨Y, hYsub, hYinj, ?_⟩
  simpa [H, hYcard] using hbound

/-- A supplied numerical upper bound on the number of collision edges gives
the corresponding clean injective-subfamily estimate. -/
theorem exists_injective_subfamily_card_sq_le_of_edges_le
    {A : Type*} [DecidableEq A] (X : Finset A)
    {B : Type*} (f : A → B) (E : ℕ)
    (hedges : (valueCollisionGraph X f).edgeFinset.card ≤ E) :
    ∃ Y : Finset A, Y ⊆ X ∧ Set.InjOn f (Y : Set A) ∧
      X.card ^ 2 ≤ Y.card * (X.card + 2 * E) := by
  obtain ⟨Y, hYX, hYinj, hY⟩ := exists_injective_subfamily_card_sq_le X f
  refine ⟨Y, hYX, hYinj, hY.trans ?_⟩
  exact Nat.mul_le_mul_left Y.card (Nat.add_le_add_left
    (Nat.mul_le_mul_left 2 hedges) X.card)

/-! ## Switching directly into augmentation windows -/

/-- If consecutive values of a finite real chain rise by at least `sigma`,
then every two distinct chain values are separated by at least `sigma`.
The conclusion is phrased with an absolute value so it has no orientation
condition on the two indices. -/
lemma sigma_le_abs_sub_of_chain
    {m : ℕ} (q : Fin (m + 1) → ℝ) {sigma : ℝ}
    (hsigma : 0 < sigma)
    (hstep : ∀ j : Fin m, sigma ≤ q j.succ - q j.castSucc)
    {i j : Fin (m + 1)} (hij : i ≠ j) :
    sigma ≤ |q i - q j| := by
  have hqStrict : StrictMono q := by
    rw [Fin.strictMono_iff_lt_succ]
    intro k
    have hk := hstep k
    linarith
  have hforward : ∀ {a b : Fin (m + 1)}, a < b →
      sigma ≤ |q a - q b| := by
    intro a b hab
    have ham : a.val < m := by omega
    let k : Fin m := ⟨a.val, ham⟩
    have hkcast : k.castSucc = a := by
      apply Fin.ext
      rfl
    have hksucc : k.succ ≤ b := by
      rw [Fin.mk_le_mk]
      exact Nat.succ_le_of_lt (Fin.val_fin_lt.mpr hab)
    have hmono : q k.succ ≤ q b := hqStrict.monotone hksucc
    have hs := hstep k
    rw [hkcast] at hs
    have habq : q a ≤ q b := hqStrict.monotone hab.le
    rw [abs_of_nonpos (sub_nonpos.mpr habq)]
    linarith
  rcases lt_or_gt_of_ne hij with hij | hji
  · exact hforward hij
  · simpa [abs_sub_comm] using hforward hji

/-- The separated-switching lemma followed by balanced augmentation.

The switching hypotheses produce `m + 1` retained times whose consecutive
centres rise by `sigma`.  If the edge-count window radius is less than
`sigma / 2`, those windows are pairwise disjoint.  Injective extensions at
every time therefore contribute `(m + 1) * r` distinct order-`q` edge
counts.  This theorem combines the two deterministic final steps of the
Kwan--Sudakov augmentation proof. -/
theorem separatedSwitching_card_mul_le_fixedOrderEdgeValues
    {τ m : ℕ} (p : ℕ → ℝ) {lam κ rho sigma R : ℝ}
    (hm : 1 ≤ m) (hrho : 0 < rho) (hsigma : 0 < sigma)
    (hrise : lam ≤ p τ - p 0)
    (hlarge : Switching.largeIncrementSum p rho τ ≤ κ)
    (hbudget : (m : ℝ) * (rho + sigma) + κ ≤ lam)
    (hRsep : 2 * R < sigma)
    (G : SimpleGraph V) (U : ℕ → Finset V)
    (X : ℕ → Finset (Finset V)) (q r : ℕ)
    (horder : ∀ i ≤ τ, ∀ x ∈ X i, (U i ∪ x).card = q)
    (hinj : ∀ i ≤ τ, Set.InjOn
      (fun x ↦ Erdos88.inducedEdges G (U i ∪ x))
      (X i : Set (Finset V)))
    (hcard : ∀ i ≤ τ, r ≤ (X i).card)
    (hwindow : ∀ i ≤ τ, ∀ e ∈ edgeValues G (U i) (X i),
      |(e : ℝ) - p i| ≤ R) :
    (m + 1) * r ≤ (fixedOrderEdgeValues G q).card := by
  obtain ⟨idx, hidx, _hzero, hlast, hstep⟩ :=
    Switching.separatedSwitchingSubsequence
      p hm hrho hsigma hrise hlarge hbudget
  let U' : Fin (m + 1) → Finset V := fun i ↦ U (idx i)
  let X' : Fin (m + 1) → Finset (Finset V) := fun i ↦ X (idx i)
  let center : Fin (m + 1) → ℝ := fun i ↦ p (idx i)
  have hidxLe : ∀ i : Fin (m + 1), idx i ≤ τ := by
    intro i
    rw [← hlast]
    exact hidx.monotone (Fin.le_last i)
  have horder' : ∀ i ∈ (Finset.univ : Finset (Fin (m + 1))),
      ∀ x ∈ X' i, (U' i ∪ x).card = q := by
    intro i _hi x hx
    exact horder (idx i) (hidxLe i) x hx
  have hinj' : ∀ i ∈ (Finset.univ : Finset (Fin (m + 1))),
      Set.InjOn (fun x ↦ Erdos88.inducedEdges G (U' i ∪ x))
        (X' i : Set (Finset V)) := by
    intro i _hi
    exact hinj (idx i) (hidxLe i)
  have hwindow' : ∀ i ∈ (Finset.univ : Finset (Fin (m + 1))),
      ∀ e ∈ edgeValues G (U' i) (X' i), |(e : ℝ) - center i| ≤ R := by
    intro i _hi e he
    exact hwindow (idx i) (hidxLe i) e he
  have hsep' : ∀ i ∈ (Finset.univ : Finset (Fin (m + 1))),
      ∀ j ∈ (Finset.univ : Finset (Fin (m + 1))), i ≠ j →
        2 * R < |center i - center j| := by
    intro i _hi j _hj hij
    exact hRsep.trans_le
      (sigma_le_abs_sub_of_chain center hsigma hstep hij)
  have hsum := sum_card_extensions_le_fixedOrderEdgeValues_real_windows
    G (Finset.univ : Finset (Fin (m + 1))) U' X' q R center
      horder' hinj' hwindow' hsep'
  calc
    (m + 1) * r = ∑ _i : Fin (m + 1), r := by simp
    _ ≤ ∑ i : Fin (m + 1), (X' i).card := by
      apply Finset.sum_le_sum
      intro i _hi
      exact hcard (idx i) (hidxLe i)
    _ ≤ (fixedOrderEdgeValues G q).card := by
      simpa using hsum

/-! ## Canonical balanced-augmentation event -/

/-- The actual edge values obtained after deleting `D` from `U0` and
adjoining the union of exactly `nZ` cells of `M` to the fixed set `W`.

This is the graph-facing random variable in the balanced augmentation
lemma.  It is defined as an image, so its cardinality is exactly the number
of distinct induced-edge counts produced by the allowed augmentations. -/
def augmentationEdgeValues (G : SimpleGraph V) (W U0 D : Finset V)
    (M : Finset (Finset V)) (nZ : ℕ) : Finset ℕ :=
  (M.powersetCard nZ).image fun Z ↦
    Erdos88.inducedEdges G (W ∪ (U0 \ D) ∪ Z.biUnion id)

@[simp] lemma mem_augmentationEdgeValues
    {G : SimpleGraph V} {W U0 D : Finset V}
    {M : Finset (Finset V)} {nZ e : ℕ} :
    e ∈ augmentationEdgeValues G W U0 D M nZ ↔
      ∃ Z ⊆ M, Z.card = nZ ∧
        Erdos88.inducedEdges G
          (W ∪ (U0 \ D) ∪ Z.biUnion id) = e := by
  simp [augmentationEdgeValues, and_assoc]

/-- The exact order of every graph counted by `augmentationEdgeValues`. -/
def augmentationOrder (W U0 : Finset V) (nD nZ k : ℕ) : ℕ :=
  W.card + (U0.card - nD) + nZ * k

/-- All augmentations in the canonical family have the same order.

The hypotheses are precisely the finite matching hypotheses supplied by a
Kwan--Sudakov structural witness: the base parts are disjoint, the matching
cells are pairwise disjoint and `k`-uniform, and every cell avoids the base. -/
lemma card_augmentation_vertex_set
    (W U0 D : Finset V) (M Z : Finset (Finset V)) (nD nZ k : ℕ)
    (hDU0 : D ⊆ U0) (hDcard : D.card = nD)
    (hWU0 : Disjoint W U0)
    (hZM : Z ⊆ M) (hZcard : Z.card = nZ)
    (hMdisj : (M : Set (Finset V)).PairwiseDisjoint id)
    (hMuniform : ∀ x ∈ M, x.card = k)
    (hMaway : ∀ x ∈ M, Disjoint x (W ∪ U0)) :
    (W ∪ (U0 \ D) ∪ Z.biUnion id).card =
      augmentationOrder W U0 nD nZ k := by
  have hWUD : Disjoint W (U0 \ D) :=
    hWU0.mono_right Finset.sdiff_subset
  have hbaseCells : Disjoint (W ∪ (U0 \ D)) (Z.biUnion id) := by
    rw [Finset.disjoint_left]
    intro v hvbase hvZ
    obtain ⟨x, hxZ, hvx⟩ := Finset.mem_biUnion.mp hvZ
    have hxM : x ∈ M := hZM hxZ
    have hxaway := Finset.disjoint_left.mp (hMaway x hxM)
    rcases Finset.mem_union.mp hvbase with hvW | hvUD
    · exact hxaway hvx (Finset.mem_union_left U0 hvW)
    · exact hxaway hvx (Finset.mem_union_right W
        (Finset.sdiff_subset hvUD))
  have hZdisj : (Z : Set (Finset V)).PairwiseDisjoint id := by
    intro x hx y hy hxy
    exact hMdisj (hZM hx) (hZM hy) hxy
  have hZuniform : ∀ x ∈ Z, x.card = k := by
    intro x hx
    exact hMuniform x (hZM hx)
  rw [Finset.card_union_of_disjoint hbaseCells,
    Finset.card_union_of_disjoint hWUD,
    Finset.card_sdiff_of_subset hDU0,
    card_matching_biUnion_eq_mul hZdisj hZuniform,
    hDcard, hZcard]
  rfl

/-- The canonical augmentation image is contained in the fixed-order
spectrum. -/
lemma augmentationEdgeValues_subset_fixedOrderEdgeValues
    (G : SimpleGraph V) (W U0 D : Finset V)
    (M : Finset (Finset V)) (nD nZ k : ℕ)
    (hDU0 : D ⊆ U0) (hDcard : D.card = nD)
    (hWU0 : Disjoint W U0)
    (hMdisj : (M : Set (Finset V)).PairwiseDisjoint id)
    (hMuniform : ∀ x ∈ M, x.card = k)
    (hMaway : ∀ x ∈ M, Disjoint x (W ∪ U0)) :
    augmentationEdgeValues G W U0 D M nZ ⊆
      fixedOrderEdgeValues G (augmentationOrder W U0 nD nZ k) := by
  intro e he
  obtain ⟨Z, hZM, hZcard, rfl⟩ := mem_augmentationEdgeValues.mp he
  exact mem_fixedOrderEdgeValues.mpr ⟨_,
    card_augmentation_vertex_set W U0 D M Z nD nZ k hDU0 hDcard
      hWU0 hZM hZcard hMdisj hMuniform hMaway,
    rfl⟩

/-- A genuinely positive lower bound on uniform layer probability supplies
an actual successful fixed-size deletion set. -/
lemma exists_mem_layer_of_one_fourth_le_probability
    {A : Type*} (U : Finset A) (d : ℕ) (event : Finset A → Prop)
    [DecidablePred event]
    (hprob : (1 / 4 : ℝ) ≤ NestedUniform.layerProbability U d event) :
    ∃ D ∈ NestedUniform.layer U d, event D := by
  have hp : 0 < NestedUniform.layerProbability U d event := by
    exact (by norm_num : (0 : ℝ) < 1 / 4).trans_le hprob
  have hcard : 0 < ((NestedUniform.layer U d).filter event).card := by
    by_contra hnot
    have hz : ((NestedUniform.layer U d).filter event).card = 0 :=
      Nat.eq_zero_of_not_pos hnot
    rw [NestedUniform.layerProbability, hz] at hp
    norm_num at hp
  obtain ⟨D, hD⟩ := Finset.card_pos.mp hcard
  exact ⟨D, (Finset.mem_filter.mp hD).1, (Finset.mem_filter.mp hD).2⟩

/-- **Probability-to-fixed-spectrum endpoint for balanced augmentation.**

Suppose a uniform `nD`-subset `D` of `U0` has, with probability at least
`1/4`, at least `L` genuinely distinct edge values among all unions of
`nZ` matching cells.  Then some deletion set realizes those values, and
the fixed-order induced spectrum contains at least `L` values.

This theorem is the intended endpoint of Claims 4.8 and 4.9: after those
claims establish the displayed probability hypothesis, the outer proof no
longer needs to manipulate a probability space. -/
theorem fixedOrderEdgeValues_of_balanced_augmentation_probability
    (G : SimpleGraph V) (W U0 : Finset V)
    (M : Finset (Finset V)) (nD nZ k L : ℕ)
    (hWU0 : Disjoint W U0)
    (hMdisj : (M : Set (Finset V)).PairwiseDisjoint id)
    (hMuniform : ∀ x ∈ M, x.card = k)
    (hMaway : ∀ x ∈ M, Disjoint x (W ∪ U0))
    (hprob : (1 / 4 : ℝ) ≤ NestedUniform.layerProbability U0 nD
      (fun D ↦ L ≤ (augmentationEdgeValues G W U0 D M nZ).card)) :
    L ≤
      (fixedOrderEdgeValues G (augmentationOrder W U0 nD nZ k)).card := by
  obtain ⟨D, hDlayer, hlarge⟩ :=
    exists_mem_layer_of_one_fourth_le_probability U0 nD
      (fun D ↦ L ≤ (augmentationEdgeValues G W U0 D M nZ).card) hprob
  have hmem := NestedUniform.mem_layer.mp hDlayer
  exact hlarge.trans (Finset.card_le_card
    (augmentationEdgeValues_subset_fixedOrderEdgeValues
      G W U0 D M nD nZ k hmem.1 hmem.2 hWU0
        hMdisj hMuniform hMaway))

/-- Real-scale version of the probability-to-spectrum endpoint.  This is
the convenient quantitative form when Claims 4.8 and 4.9 produce the
paper's lower bound `a₂ * nZ * sqrt nD`. -/
theorem real_le_fixedOrderEdgeValues_of_balanced_augmentation_probability
    (G : SimpleGraph V) (W U0 : Finset V)
    (M : Finset (Finset V)) (nD nZ k : ℕ) (L : ℝ)
    (hWU0 : Disjoint W U0)
    (hMdisj : (M : Set (Finset V)).PairwiseDisjoint id)
    (hMuniform : ∀ x ∈ M, x.card = k)
    (hMaway : ∀ x ∈ M, Disjoint x (W ∪ U0))
    (hprob : (1 / 4 : ℝ) ≤ NestedUniform.layerProbability U0 nD
      (fun D ↦ L ≤
        ((augmentationEdgeValues G W U0 D M nZ).card : ℝ))) :
    L ≤
      ((fixedOrderEdgeValues G
        (augmentationOrder W U0 nD nZ k)).card : ℝ) := by
  obtain ⟨D, hDlayer, hlarge⟩ :=
    exists_mem_layer_of_one_fourth_le_probability U0 nD
      (fun D ↦ L ≤
        ((augmentationEdgeValues G W U0 D M nZ).card : ℝ)) hprob
  have hmem := NestedUniform.mem_layer.mp hDlayer
  have hcard := Finset.card_le_card
    (augmentationEdgeValues_subset_fixedOrderEdgeValues
      G W U0 D M nD nZ k hmem.1 hmem.2 hWU0
        hMdisj hMuniform hMaway)
  exact hlarge.trans (by exact_mod_cast hcard)

/-- Select the `W⁻` or `W⁺` base of a structural witness. -/
def structuralBase
    {scale nW ell K : ℕ} {α aDisc aDiv b : ℝ}
    {G : SimpleGraph V}
    (S : StructuralWitness G scale nW ell K α aDisc aDiv b)
    (branch : Bool) : Finset V :=
  if branch then S.Wplus else S.Wminus

/-- Either selected structural base is disjoint from the reservoir. -/
lemma structuralBase_disjoint_U0
    {scale nW ell K : ℕ} {α aDisc aDiv b : ℝ}
    {G : SimpleGraph V}
    (S : StructuralWitness G scale nW ell K α aDisc aDiv b)
    (branch : Bool) : Disjoint (structuralBase S branch) S.U0 := by
  cases branch <;> simp [structuralBase,
    S.disjoint_Wminus_U0, S.disjoint_Wplus_U0]

/-- Every matching cell avoids either selected structural base together
with the reservoir. -/
lemma structural_matching_away_base_union_U0
    {scale nW ell K : ℕ} {α aDisc aDiv b : ℝ}
    {G : SimpleGraph V}
    (S : StructuralWitness G scale nW ell K α aDisc aDiv b)
    (branch : Bool) (x : Finset V) (hx : x ∈ S.matching) :
    Disjoint x (structuralBase S branch ∪ S.U0) := by
  apply (S.matching_away x hx).mono_right
  intro v hv
  cases branch
  · simp only [structuralBase, Bool.false_eq_true, ↓reduceIte,
      Finset.mem_union] at hv
    rcases hv with hv | hv
    · exact Finset.mem_union_left _ (Finset.mem_union_left _ hv)
    · exact Finset.mem_union_right _ hv
  · simp only [structuralBase, ↓reduceIte, Finset.mem_union] at hv
    rcases hv with hv | hv
    · exact Finset.mem_union_left _ (Finset.mem_union_right _ hv)
    · exact Finset.mem_union_right _ hv

/-- Structural-witness specialization of the real balanced-augmentation
endpoint.  It discharges all disjointness, uniformity, and fixed-order
bookkeeping from the fields of `StructuralWitness`.

Consequently, the only remaining obligation for the probabilistic Claims
4.8 and 4.9 is exactly the displayed `1/4` success-probability estimate. -/
theorem real_le_fixedOrderEdgeValues_of_structural_augmentation_probability
    {scale nW ell K : ℕ} {α aDisc aDiv b : ℝ}
    {G : SimpleGraph V}
    (S : StructuralWitness G scale nW ell K α aDisc aDiv b)
    (branch : Bool) (nD nZ : ℕ) (L : ℝ)
    (hprob : (1 / 4 : ℝ) ≤ NestedUniform.layerProbability S.U0 nD
      (fun D ↦ L ≤
        ((augmentationEdgeValues G (structuralBase S branch) S.U0 D
          S.matching nZ).card : ℝ))) :
    L ≤
      ((fixedOrderEdgeValues G
        (augmentationOrder (structuralBase S branch) S.U0
          nD nZ S.k)).card : ℝ) := by
  exact real_le_fixedOrderEdgeValues_of_balanced_augmentation_probability
    G (structuralBase S branch) S.U0 S.matching nD nZ S.k L
      (structuralBase_disjoint_U0 S branch)
      S.matching_pairwiseDisjoint S.matching_uniform
      (structural_matching_away_base_union_U0 S branch) hprob

/-! ## Boolean-slice / finset-layer adapter -/

/-- Map a finite set of vertices of the subtype `↑U` back to the ambient
vertex type. -/
def mapSubtypeFinset (U : Finset V) (S : Finset U) : Finset V :=
  S.map (Function.Embedding.subtype fun v : V ↦ v ∈ U)

lemma mapSubtypeFinset_subset (U : Finset V) (S : Finset U) :
    mapSubtypeFinset U S ⊆ U := by
  intro v hv
  obtain ⟨u, _hu, rfl⟩ := Finset.mem_map.mp hv
  exact u.2

@[simp] lemma card_mapSubtypeFinset (U : Finset V) (S : Finset U) :
    (mapSubtypeFinset U S).card = S.card := by
  exact Finset.card_map _

/-- Finsets of the subtype `↑U` are equivalent to finsets of ambient
vertices contained in `U`, with cardinality preserved. -/
noncomputable def finsetSubtypeEquivBooleanSlicePoint
    (U : Finset V) (d : ℕ) :
    {S : Finset U // S.card = d} ≃
      Erdos88.BooleanSlices.BooleanSlicePoint U d where
  toFun S := ⟨mapSubtypeFinset U S.1, by
    rw [Erdos88.BooleanSlices.mem_booleanSlice]
    exact ⟨mapSubtypeFinset_subset U S.1,
      (card_mapSubtypeFinset U S.1).trans S.2⟩⟩
  invFun D :=
    ⟨Erdos88.BooleanSlices.finsetLift U D.1, by
      rw [Erdos88.BooleanSlices.card_finsetLift U D.1
        (Erdos88.BooleanSlices.mem_booleanSlice.mp D.2).1]
      exact (Erdos88.BooleanSlices.mem_booleanSlice.mp D.2).2⟩
  left_inv S := by
    apply Subtype.ext
    apply Finset.map_injective
      (Function.Embedding.subtype fun v : V ↦ v ∈ U)
    rw [Erdos88.BooleanSlices.map_finsetLift]
    · rfl
    · exact mapSubtypeFinset_subset U S.1
  right_inv D := by
    apply Subtype.ext
    exact Erdos88.BooleanSlices.map_finsetLift U D.1
      (Erdos88.BooleanSlices.mem_booleanSlice.mp D.2).1

/-- The function-valued Fourier slice on coordinates `↑U` is exactly
equivalent to the finset-valued uniform layer on `U`. -/
noncomputable def boolSliceEquivBooleanSlicePoint (U : Finset V) (d : ℕ) :
    Erdos88.Fourier.BoolSlice U d ≃
      Erdos88.BooleanSlices.BooleanSlicePoint U d :=
  (Erdos88.Fourier.boolSliceEquivFinsetLen U d).trans
    (finsetSubtypeEquivBooleanSlicePoint U d)

/-- Decode a function-valued Fourier slice point as its selected ambient
vertex finset. -/
noncomputable def boolSliceDeletion (U : Finset V) (d : ℕ)
    (omega : Erdos88.Fourier.BoolSlice U d) : Finset V :=
  (boolSliceEquivBooleanSlicePoint U d omega).1

@[simp] lemma boolSliceDeletion_mem_layer (U : Finset V) (d : ℕ)
    (omega : Erdos88.Fourier.BoolSlice U d) :
    boolSliceDeletion U d omega ∈ NestedUniform.layer U d := by
  exact (boolSliceEquivBooleanSlicePoint U d omega).2

/-- Uniform probability is invariant under a finite equivalence. -/
lemma finProbability_equiv
    {A B : Type*} [Fintype A] [Fintype B] [Nonempty A] [Nonempty B]
    (e : A ≃ B) (event : B → Prop) :
    Erdos88.Fourier.finProbability A (fun a ↦ event (e a)) =
      Erdos88.Fourier.finProbability B event := by
  classical
  have hnum :
      ((Finset.univ : Finset A).filter fun a ↦ event (e a)).card =
        ((Finset.univ : Finset B).filter event).card := by
    rw [← Fintype.card_subtype, ← Fintype.card_subtype]
    exact Fintype.card_congr
      (e.subtypeEquiv fun _ ↦ Iff.rfl)
  have hden : Fintype.card A = Fintype.card B := Fintype.card_congr e
  simp only [Erdos88.Fourier.finProbability, hnum, hden]

/-- The Fourier `BoolSlice` probability of an event depending on its
decoded deletion set equals `NestedUniform.layerProbability` exactly. -/
theorem finProbability_boolSliceDeletion_eq_layerProbability
    (U : Finset V) (d : ℕ)
    [Nonempty (Erdos88.Fourier.BoolSlice U d)]
    [Nonempty (Erdos88.BooleanSlices.BooleanSlicePoint U d)]
    (event : Finset V → Prop) [DecidablePred event] :
    Erdos88.Fourier.finProbability (Erdos88.Fourier.BoolSlice U d)
        (fun omega ↦ event (boolSliceDeletion U d omega)) =
      NestedUniform.layerProbability U d event := by
  let eventB : Erdos88.BooleanSlices.BooleanSlicePoint U d → Prop :=
    fun D ↦ event D.1
  let : DecidablePred eventB := Classical.decPred eventB
  calc
    Erdos88.Fourier.finProbability (Erdos88.Fourier.BoolSlice U d)
        (fun omega ↦ event (boolSliceDeletion U d omega)) =
      Erdos88.Fourier.finProbability
        (Erdos88.BooleanSlices.BooleanSlicePoint U d)
        eventB := by
      simpa only [eventB, boolSliceDeletion] using
        finProbability_equiv (boolSliceEquivBooleanSlicePoint U d) eventB
    _ = NestedUniform.layerProbability U d event := by
      simp only [Erdos88.Fourier.finProbability,
        NestedUniform.layerProbability]
      have hnum :
          ((Finset.univ : Finset
              (Erdos88.BooleanSlices.BooleanSlicePoint U d)).filter
                eventB).card =
            ((NestedUniform.layer U d).filter event).card := by
        let e : {D // eventB D} ≃
              {D : Finset V // D ∈
                (NestedUniform.layer U d).filter event} :=
          { toFun := fun D ↦ ⟨D.1.1, Finset.mem_filter.mpr ⟨by
                simpa [Erdos88.BooleanSlices.booleanSlice,
                  NestedUniform.layer] using D.1.2, by
                simpa [eventB] using D.2⟩⟩
            invFun := fun D ↦ ⟨⟨D.1, by
                simpa [Erdos88.BooleanSlices.booleanSlice,
                  NestedUniform.layer] using
                    (Finset.mem_filter.mp D.2).1⟩, by
                simpa [eventB] using (Finset.mem_filter.mp D.2).2⟩
            left_inv := by intro D; rfl
            right_inv := by intro D; rfl }
        rw [← Fintype.card_subtype, ← Fintype.card_coe]
        exact Fintype.card_congr e
      congr 1
      · exact_mod_cast hnum
      · simp [Erdos88.BooleanSlices.card_booleanSlicePoint,
          NestedUniform.card_layer]

/-- If at least three quarters of the outer `2d`-sets are good and every
good outer set has inner success probability at least one third, then the
uniform marginal `d`-set succeeds with probability at least one quarter. -/
theorem one_fourth_le_layerProbability_of_nested
    {A : Type*} (U : Finset A) (d : ℕ)
    (outerGood event : Finset A → Prop)
    [DecidablePred outerGood] [DecidablePred event]
    (hfeasible : 2 * d ≤ U.card)
    (houter : (3 / 4 : ℝ) ≤
      NestedUniform.layerProbability U (2 * d) outerGood)
    (hinner : ∀ D₁ ∈ NestedUniform.layer U (2 * d), outerGood D₁ →
      (1 / 3 : ℝ) ≤ NestedUniform.layerProbability D₁ d event) :
    (1 / 4 : ℝ) ≤ NestedUniform.layerProbability U d event := by
  classical
  have hpoint : ∀ D₁ ∈ NestedUniform.layer U (2 * d),
      (1 / 3 : ℝ) * (if outerGood D₁ then 1 else 0) ≤
        NestedUniform.layerProbability D₁ d event := by
    intro D₁ hD₁
    by_cases hgood : outerGood D₁
    · simpa [hgood] using hinner D₁ hD₁ hgood
    · simp only [hgood, if_false, mul_zero]
      exact div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  have hweighted :
      (1 / 3 : ℝ) * NestedUniform.layerProbability U (2 * d) outerGood ≤
        NestedUniform.iteratedProbability U d event := by
    rw [NestedUniform.layerProbability_eq_layerExpectation_indicator,
      NestedUniform.iteratedProbability]
    change (1 / 3 : ℝ) *
        (NestedUniform.layer U (2 * d)).expect
          (fun D₁ ↦ if outerGood D₁ then 1 else 0) ≤
      (NestedUniform.layer U (2 * d)).expect
        (fun D₁ ↦ NestedUniform.layerProbability D₁ d event)
    simp only [Finset.expect_eq_sum_div_card]
    rw [mul_div, Finset.mul_sum]
    apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
    exact Finset.sum_le_sum hpoint
  rw [NestedUniform.iteratedProbability_eq_layerProbability
    U d hfeasible event] at hweighted
  nlinarith

/-! ## One shared deletion outcome across a switching path -/

/-- Some point of a nonempty finite probability space is no larger than
its uniform expectation. -/
lemma exists_le_uniformExpectation
    {Omega : Type*} [Fintype Omega] [Nonempty Omega]
    (Y : Omega → ℝ) :
    ∃ omega, Y omega ≤ Erdos88.Concentration.uniformExpectation Y := by
  have hcard : (0 : ℝ) < Fintype.card Omega := by
    exact_mod_cast Fintype.card_pos
  have hmean : Erdos88.Concentration.uniformExpectation Y ≤
      Erdos88.Concentration.uniformExpectation Y := le_rfl
  rw [Erdos88.Concentration.uniformExpectation] at hmean
  have hsum : ∑ omega, Y omega ≤
      ∑ _omega : Omega, Erdos88.Concentration.uniformExpectation Y := by
    simpa [Erdos88.Concentration.uniformExpectation, nsmul_eq_mul,
      mul_comm] using (div_le_iff₀ hcard).1 hmean
  obtain ⟨omega, _homega, hle⟩ := Finset.exists_le_of_sum_le
    (s := (Finset.univ : Finset Omega)) (by simp) hsum
  exact ⟨omega, hle⟩

/-- **Shared-outcome averaging lemma.**

Suppose every time in `I` is good with probability at least `p`, and a
nonnegative error budget has expectation at most `B`.  Then one and the
same outcome is good at at least half the expected density of times and
has total error at most `2 * B / p`.

This is the finite quantifier bridge needed in the outer Kwan--Sudakov
switching argument: pointwise augmentation probabilities are not replaced
by independently chosen deletion sets. -/
theorem exists_shared_outcome_many_good_and_error_le
    {Omega J : Type*} [Fintype Omega] [Nonempty Omega]
    (I : Finset J) (good : J → Omega → Prop) (error : Omega → ℝ)
    (p B : ℝ) (hp : 0 < p) (hp_one : p ≤ 1) (hB : 0 < B)
    (hgood : ∀ j ∈ I, p ≤
      Erdos88.Concentration.uniformProbability (good j))
    (herror_nonneg : ∀ omega, 0 ≤ error omega)
    (herror_mean : Erdos88.Concentration.uniformExpectation error ≤ B) :
    ∃ omega,
      p / 2 * I.card ≤
          (CollisionCounting.eventCount I good omega : ℝ) ∧
        error omega ≤ 2 * B / p := by
  classical
  by_cases hI : I.card = 0
  · obtain ⟨omega, homega⟩ := exists_le_uniformExpectation error
    refine ⟨omega, ?_, ?_⟩
    · simp [hI]
    · have hBp : B * p ≤ B :=
        mul_le_of_le_one_right hB.le hp_one
      apply (le_div_iff₀ hp).2
      have herrp := mul_le_mul_of_nonneg_right
        (homega.trans herror_mean) hp.le
      nlinarith
  · have hIpos : 0 < (I.card : ℝ) := by
      exact_mod_cast Nat.pos_of_ne_zero hI
    let count : Omega → ℝ := fun omega ↦
      CollisionCounting.eventCount I good omega
    let c : ℝ := p * I.card / (2 * B)
    let score : Omega → ℝ := fun omega ↦
      count omega - c * error omega
    have hcount_mean :
        p * I.card ≤ Erdos88.Concentration.uniformExpectation count := by
      rw [CollisionCounting.uniformExpectation_eventCount]
      simpa [count, mul_comm] using
        (Finset.sum_le_sum fun j hj ↦ hgood j hj)
    have hc_nonneg : 0 ≤ c := by
      dsimp only [c]
      positivity
    have hc_pos : 0 < c := by
      dsimp only [c]
      positivity
    have hcB : c * B = p * I.card / 2 := by
      dsimp only [c]
      field_simp
    have hscore_mean :
        p * I.card / 2 ≤
          Erdos88.Concentration.uniformExpectation score := by
      have hmean_eq : Erdos88.Concentration.uniformExpectation score =
          Erdos88.Concentration.uniformExpectation count -
            c * Erdos88.Concentration.uniformExpectation error := by
        simp only [score, Erdos88.Concentration.uniformExpectation,
          Finset.sum_sub_distrib]
        rw [← Finset.mul_sum]
        ring
      rw [hmean_eq]
      have hcerr := mul_le_mul_of_nonneg_left herror_mean hc_nonneg
      nlinarith
    obtain ⟨omega, homega⟩ := exists_le_uniformExpectation
      (fun omega ↦ -score omega)
    have hscore_omega : p * I.card / 2 ≤ score omega := by
      have hneg_mean :
          Erdos88.Concentration.uniformExpectation (fun omega ↦ -score omega) =
            -Erdos88.Concentration.uniformExpectation score := by
        simp only [Erdos88.Concentration.uniformExpectation,
          Finset.sum_neg_distrib]
        ring
      rw [hneg_mean] at homega
      linarith
    have hcount_le : count omega ≤ I.card := by
      dsimp only [count, CollisionCounting.eventCount]
      exact_mod_cast Finset.card_le_card (Finset.filter_subset _ _)
    have hscore_le_count : score omega ≤ count omega := by
      dsimp only [score]
      exact sub_le_self _ (mul_nonneg hc_nonneg (herror_nonneg omega))
    have herror_charged : c * error omega ≤ I.card := by
      dsimp only [score] at hscore_omega
      nlinarith
    have hctarget : c * (2 * B / p) = I.card := by
      dsimp only [c]
      field_simp
    refine ⟨omega, ?_, ?_⟩
    · nlinarith
    · calc
        error omega ≤ I.card / c := (le_div_iff₀ hc_pos).2 (by
          simpa [mul_comm] using herror_charged)
        _ = 2 * B / p := by
          apply (mul_left_cancel₀ (ne_of_gt hc_pos))
          rw [hctarget]
          field_simp

/-- The constants used in the Kwan--Sudakov application: pointwise
success probability `1/4` gives one deletion which is successful at an
`1/8` fraction of the switching times, while paying at most eight times
the expected total error. -/
theorem exists_shared_outcome_one_eighth_good_and_error_le_eight
    {Omega J : Type*} [Fintype Omega] [Nonempty Omega]
    (I : Finset J) (good : J → Omega → Prop) (error : Omega → ℝ)
    (B : ℝ) (hB : 0 < B)
    (hgood : ∀ j ∈ I, (1 / 4 : ℝ) ≤
      Erdos88.Concentration.uniformProbability (good j))
    (herror_nonneg : ∀ omega, 0 ≤ error omega)
    (herror_mean : Erdos88.Concentration.uniformExpectation error ≤ B) :
    ∃ omega,
      (1 / 8 : ℝ) * I.card ≤
          (CollisionCounting.eventCount I good omega : ℝ) ∧
        error omega ≤ 8 * B := by
  obtain ⟨omega, hcount, herror⟩ :=
    exists_shared_outcome_many_good_and_error_le I good error
      (1 / 4) B (by norm_num) (by norm_num) hB hgood
      herror_nonneg herror_mean
  refine ⟨omega, ?_, ?_⟩
  · norm_num at hcount ⊢
    exact hcount
  · norm_num at herror ⊢
    linarith

/-- Canonical uniform-layer specialization of the shared-outcome lemma.

The hypotheses are stated using `NestedUniform.layerProbability`, while
the returned deletion is a Fourier `BoolSlice` point so that the linear
statistics and moment bounds from the exposure modules apply directly. -/
theorem exists_shared_deletion_one_eighth_good_and_error_le_eight
    {J : Type*} (U : Finset V) (d : ℕ) (I : Finset J)
    (good : J → Finset V → Prop)
    (error : Erdos88.Fourier.BoolSlice U d → ℝ) (B : ℝ)
    [Nonempty (Erdos88.Fourier.BoolSlice U d)]
    [Nonempty (Erdos88.BooleanSlices.BooleanSlicePoint U d)]
    (hB : 0 < B)
    (hgood : ∀ j ∈ I, (1 / 4 : ℝ) ≤
      NestedUniform.layerProbability U d (good j))
    (herror_nonneg : ∀ omega, 0 ≤ error omega)
    (herror_mean : Erdos88.Concentration.uniformExpectation error ≤ B) :
    ∃ omega : Erdos88.Fourier.BoolSlice U d,
      (1 / 8 : ℝ) * I.card ≤
          (CollisionCounting.eventCount I
            (fun j omega ↦ good j (boolSliceDeletion U d omega)) omega : ℝ) ∧
        error omega ≤ 8 * B := by
  classical
  apply exists_shared_outcome_one_eighth_good_and_error_le_eight
    I (fun j omega ↦ good j (boolSliceDeletion U d omega)) error B hB
  · intro j hj
    have heq := finProbability_boolSliceDeletion_eq_layerProbability
      U d (good j)
    have hjp := hgood j hj
    rw [← heq] at hjp
    simpa [Erdos88.Concentration.uniformProbability,
      Erdos88.Fourier.finProbability] using hjp
  · exact herror_nonneg
  · exact herror_mean

/-- The marked indices selected by an event-count are literally the
corresponding filtered finset.  This small bridge keeps the common-outcome
choice theorem compatible with the marked-packing API. -/
@[simp] theorem card_filter_eq_eventCount
    {Omega J : Type*} [Fintype Omega] [Nonempty Omega]
    (I : Finset J) (good : J → Omega → Prop) (omega : Omega) :
    (I.filter fun j ↦ good j omega).card =
      CollisionCounting.eventCount I good omega := by
  rfl

/-- Total variation of a finite real sequence is at most twice its
pointwise `ℓ¹` mass.  Applied to the random centre errors, this converts the
shared deletion's global error budget into the consecutive-error budget
used by marked packing. -/
theorem sum_abs_sub_previous_le_two_sum_abs
    (epsilon : ℕ → ℝ) (t : ℕ) :
    ∑ u ∈ Finset.Icc 1 t, |epsilon u - epsilon (u - 1)| ≤
      2 * ∑ j ∈ Finset.range (t + 1), |epsilon j| := by
  have htriangle :
      ∑ u ∈ Finset.Icc 1 t, |epsilon u - epsilon (u - 1)| ≤
        ∑ u ∈ Finset.Icc 1 t,
          (|epsilon u| + |epsilon (u - 1)|) := by
    apply Finset.sum_le_sum
    intro u hu
    exact abs_sub _ _
  have hcurrent :
      ∑ u ∈ Finset.Icc 1 t, |epsilon u| ≤
        ∑ j ∈ Finset.range (t + 1), |epsilon j| := by
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro u hu
      simp only [Finset.mem_Icc, Finset.mem_range] at hu ⊢
      omega
    · intro i hi _hnot
      positivity
  have hshiftEq :
      ∑ u ∈ Finset.Icc 1 t, |epsilon (u - 1)| =
        ∑ j ∈ Finset.range t, |epsilon j| := by
    apply Finset.sum_bij (fun u _hu ↦ u - 1)
    · intro u hu
      simp only [Finset.mem_Icc, Finset.mem_range] at hu ⊢
      omega
    · intro a ha b hb hab
      simp only [Finset.mem_Icc] at ha hb
      omega
    · intro j hj
      refine ⟨j + 1, ?_, ?_⟩
      · simp only [Finset.mem_Icc, Finset.mem_range] at hj ⊢
        omega
      · omega
    · intro u hu
      rfl
  have hprevious :
      ∑ u ∈ Finset.Icc 1 t, |epsilon (u - 1)| ≤
        ∑ j ∈ Finset.range (t + 1), |epsilon j| := by
    rw [hshiftEq]
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · exact Finset.range_mono (Nat.le_succ t)
    · intro i hi _hnot
      positivity
  calc
    ∑ u ∈ Finset.Icc 1 t, |epsilon u - epsilon (u - 1)| ≤
        ∑ u ∈ Finset.Icc 1 t,
          (|epsilon u| + |epsilon (u - 1)|) := htriangle
    _ = (∑ u ∈ Finset.Icc 1 t, |epsilon u|) +
          ∑ u ∈ Finset.Icc 1 t, |epsilon (u - 1)| := by
      rw [Finset.sum_add_distrib]
    _ ≤ (∑ j ∈ Finset.range (t + 1), |epsilon j|) +
          ∑ j ∈ Finset.range (t + 1), |epsilon j| :=
      add_le_add hcurrent hprevious
    _ = 2 * ∑ j ∈ Finset.range (t + 1), |epsilon j| := by ring

/-! ## Graph-facing output of the full-exposure abstraction -/

/-- Feed the separated-window witness produced by
`AugmentationFull.exists_injective_separated_windows` into the genuine
fixed-order graph spectrum.

The single graph-specific compatibility equation `hvalue` identifies the
abstract full-exposure integer with the induced edge count.  All thinning,
injectivity, balanced-window, and separated-centre bookkeeping is then
performed internally. -/
theorem fullExposure_sum_card_le_fixedOrderEdgeValues
    {D : Type u} [Fintype D]
    {s tau m edgeBudget : ℕ}
    (P : AugmentationFull.PartialExposureData D (Finset V) s tau)
    (omega : AugmentationFull.Sample D s)
    (idx : Fin (m + 1) → ℕ) (J : Finset (Fin (m + 1)))
    {sigma R : ℝ}
    (hsigma : 0 < sigma) (hR : 2 * R < sigma)
    (hidx : StrictMono idx) (hlast : idx (Fin.last m) = tau)
    (hstep : ∀ j : Fin m,
      sigma ≤ P.path omega (idx j.succ) -
        P.path omega (idx j.castSucc))
    (hgoodIndex : ∀ j ∈ J, ¬ P.geometricBad (idx j) omega)
    (hwindow : ∀ i ≤ tau, ∀ x ∈ P.candidates,
      ¬ P.geometricBad i omega → ¬ P.degreeBad x omega →
        |(P.value i x omega : ℝ) - P.path omega i| ≤ R)
    (hedges : ∀ j ∈ J,
      (AugmentationFull.valueCollisionGraph
        (AugmentationFull.goodCandidates P omega)
        (fun x ↦ P.value (idx j) x omega)).edgeFinset.card ≤ edgeBudget)
    (G : SimpleGraph V) (U : Fin (m + 1) → Finset V) (q : ℕ)
    (hvalue : ∀ j ∈ J, ∀ x ∈ AugmentationFull.goodCandidates P omega,
      P.value (idx j) x omega =
        (Erdos88.inducedEdges G (U j ∪ x) : ℤ))
    (horder : ∀ j ∈ J, ∀ x ∈ AugmentationFull.goodCandidates P omega,
      (U j ∪ x).card = q) :
    ∃ Y : Fin (m + 1) → Finset (Finset V),
      (∀ j ∈ J, Y j ⊆ AugmentationFull.goodCandidates P omega) ∧
      (∀ j ∈ J,
        (AugmentationFull.goodCandidates P omega).card ^ 2 ≤
          (Y j).card *
            ((AugmentationFull.goodCandidates P omega).card +
              2 * edgeBudget)) ∧
      ∑ j ∈ J, (Y j).card ≤ (fixedOrderEdgeValues G q).card := by
  obtain ⟨Y, hYsub, hYinj, hYcard, hYwindow, hYsep⟩ :=
    AugmentationFull.exists_injective_separated_windows
      P omega idx J hsigma hR hidx hlast hstep hgoodIndex hwindow hedges
  refine ⟨Y, hYsub, hYcard, ?_⟩
  apply sum_card_extensions_le_fixedOrderEdgeValues_real_windows
    G J U Y q R (fun j ↦ P.path omega (idx j))
  · intro j hj x hx
    exact horder j hj x (hYsub j hj hx)
  · intro j hj x hx y hy hxy
    apply hYinj j hj hx hy
    change P.value (idx j) x omega = P.value (idx j) y omega
    rw [hvalue j hj x (hYsub j hj hx),
      hvalue j hj y (hYsub j hj hy)]
    change Erdos88.inducedEdges G (U j ∪ x) =
      Erdos88.inducedEdges G (U j ∪ y) at hxy
    exact_mod_cast hxy
  · intro j hj e he
    obtain ⟨x, hx, rfl⟩ := mem_edgeValues.mp he
    have hw := hYwindow j hj x hx
    rw [hvalue j hj x (hYsub j hj hx)] at hw
    norm_cast at hw ⊢
  · exact hYsep

end

end Augmentation
end Erdos636
