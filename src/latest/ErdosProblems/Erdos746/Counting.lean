import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Combinatorics.SetFamily.LYM
import Mathlib.Probability.Distributions.Uniform
import Mathlib.Tactic

/-!
# Counting lemmas for the uniform fixed-edge random-graph model

This file records two equivalent finite models useful for `G(n, m)`:

* an ordered sample is an embedding of `Fin m` into the edge set of the
  complete graph;
* an unordered sample is an `m`-element subset of the complete graph's
  edge finset.

For the unordered model we construct the uniform probability mass function,
compute the exact sample-space cardinality and event probability, and count
the samples containing a prescribed set of edges.  The last section derives
the upward local LYM inequality from Mathlib's downward version; this is the
counting input for monotonicity of increasing graph properties across the
layers of the Boolean lattice.
-/

open scoped Classical ENNReal FinsetFamily NNReal

namespace Erdos746.Counting

noncomputable section

/-! ## Uniform graphs as a subtype of all simple graphs -/

/-- The subtype of labelled graphs on `Fin n` having exactly `m` edges. -/
abbrev MGraph (n m : ℕ) :=
  {G : SimpleGraph (Fin n) // G.edgeFinset.card = m}

/-- The uniform PMF on the subtype of labelled `m`-edge graphs. -/
def randomGraph (n m : ℕ) [Nonempty (MGraph n m)] : PMF (MGraph n m) :=
  PMF.uniformOfFintype (MGraph n m)

/-- In the uniform graph-subtype model, event probability is the ratio of
the number of favourable graphs to the total number of graphs. -/
theorem randomGraph_event (n m : ℕ) [Nonempty (MGraph n m)]
    (P : SimpleGraph (Fin n) → Prop) :
    (randomGraph n m).toOuterMeasure {x | P x.1} =
      Fintype.card {x : MGraph n m // P x.1} /
        Fintype.card (MGraph n m) := by
  exact PMF.toOuterMeasure_uniformOfFintype_apply _

/-! ## Ordered samples and prefix graphs -/

/-- The finite type of possible edges on `Fin n`. -/
abbrev Edge (n : ℕ) := (⊤ : SimpleGraph (Fin n)).edgeSet

/-- An ordered list of `m` distinct edges on `Fin n`. -/
abbrev EdgeInjection (n m : ℕ) := Fin m ↪ Edge n

/-- There are `n.choose 2` possible edges on `Fin n`. -/
@[simp]
theorem card_edge (n : ℕ) : Fintype.card (Edge n) = n.choose 2 := by
  rw [SimpleGraph.card_edgeSet,
    SimpleGraph.card_edgeFinset_top_eq_card_choose_two]
  simp

/-- The number of ordered lists of `m` distinct possible edges is the
descending factorial `(n.choose 2).descFactorial m`. -/
@[simp]
theorem card_edgeInjection (n m : ℕ) :
    Fintype.card (EdgeInjection n m) =
      (n.choose 2).descFactorial m := by
  rw [Fintype.card_embedding_eq, card_edge]
  simp

/-- Ordered `m`-edge samples exist exactly up to the size of the complete
edge set. -/
theorem nonempty_edgeInjection_iff {n m : ℕ} :
    Nonempty (EdgeInjection n m) ↔ m ≤ n.choose 2 := by
  rw [Function.Embedding.nonempty_iff_card_le, Fintype.card_fin, card_edge]

/-- The graph whose edge set is the range of an ordered edge sample. -/
def graphOfInjection {n m : ℕ} (f : EdgeInjection n m) :
    SimpleGraph (Fin n) :=
  SimpleGraph.fromEdgeSet (Set.range (fun i ↦ (f i : Edge n).1))

theorem range_avoids_diag {n m : ℕ} (f : EdgeInjection n m) :
    Disjoint (Set.range (fun i ↦ (f i : Edge n).1)) Sym2.diagSet := by
  rw [Set.disjoint_left]
  rintro e ⟨i, rfl⟩ he
  exact (⊤ : SimpleGraph (Fin n)).not_isDiag_of_mem_edgeSet
    (f i).property he

@[simp]
theorem edgeSet_graphOfInjection {n m : ℕ} (f : EdgeInjection n m) :
    (graphOfInjection f).edgeSet =
      Set.range (fun i ↦ (f i : Edge n).1) := by
  rw [graphOfInjection, SimpleGraph.edgeSet_fromEdgeSet]
  exact sdiff_eq_left.mpr (range_avoids_diag f)

/-- An injective ordered sample of length `m` produces exactly `m` edges. -/
@[simp]
theorem card_graphOfInjection {n m : ℕ} (f : EdgeInjection n m) :
    (graphOfInjection f).edgeFinset.card = m := by
  let g : Fin m → Sym2 (Fin n) := fun i ↦ (f i : Edge n).1
  have hg : Function.Injective g := by
    intro i j h
    apply f.injective
    exact Subtype.ext h
  calc
    (graphOfInjection f).edgeFinset.card =
        ((↑(graphOfInjection f).edgeFinset : Set (Sym2 (Fin n))).ncard) :=
      (Set.ncard_coe_finset _).symm
    _ = (graphOfInjection f).edgeSet.ncard := by
      rw [SimpleGraph.coe_edgeFinset]
    _ = (Set.range g).ncard := by rw [edgeSet_graphOfInjection]
    _ = Nat.card (Fin m) := Set.ncard_range_of_injective hg
    _ = m := Nat.card_fin m

/-- Restricting an ordered sample to a shorter prefix produces a subgraph. -/
theorem graphOfInjection_mono {n m k : ℕ} (f : EdgeInjection n k)
    (h : m ≤ k) :
    graphOfInjection ((Fin.castLEEmb h).trans f) ≤ graphOfInjection f := by
  rw [← SimpleGraph.edgeSet_subset_edgeSet, edgeSet_graphOfInjection,
    edgeSet_graphOfInjection]
  rintro e ⟨i, rfl⟩
  exact ⟨Fin.castLE h i, rfl⟩

/-! ## Uniform unordered edge subsets -/

/-- The complete finset of possible edges on `Fin n`. -/
def edgeUniverse (n : ℕ) : Finset (Sym2 (Fin n)) :=
  (⊤ : SimpleGraph (Fin n)).edgeFinset

/-- The exact unordered sample space for `G(n, m)`. -/
abbrev EdgeChoices (n m : ℕ) := (edgeUniverse n).powersetCard m

/-- Turn an unordered edge sample into its simple graph. -/
def graphOfChoice {n m : ℕ} (s : EdgeChoices n m) :
    SimpleGraph (Fin n) :=
  SimpleGraph.fromEdgeSet (s.1 : Set (Sym2 (Fin n)))

@[simp]
theorem edgeUniverse_card (n : ℕ) : (edgeUniverse n).card = n.choose 2 := by
  unfold edgeUniverse
  rw [SimpleGraph.card_edgeFinset_top_eq_card_choose_two]
  simp

/-- The exact number of unordered `m`-edge samples. -/
@[simp]
theorem card_edgeChoices (n m : ℕ) :
    Fintype.card (EdgeChoices n m) = (n.choose 2).choose m := by
  change Fintype.card ↥((edgeUniverse n).powersetCard m) = _
  rw [Fintype.card_coe, Finset.card_powersetCard, edgeUniverse_card]

theorem nonempty_edgeChoices_iff {n m : ℕ} :
    Nonempty (EdgeChoices n m) ↔ m ≤ n.choose 2 := by
  rw [Finset.nonempty_coe_sort, Finset.powersetCard_nonempty,
    edgeUniverse_card]

/-- Converting an edge subset into a graph loses no edges. -/
@[simp]
theorem edgeFinset_graphOfChoice {n m : ℕ} (s : EdgeChoices n m) :
    (graphOfChoice s).edgeFinset = s.1 := by
  apply Finset.ext
  intro e
  rw [SimpleGraph.mem_edgeFinset, graphOfChoice,
    SimpleGraph.edgeSet_fromEdgeSet]
  simp only [Set.mem_sdiff, Finset.mem_coe, and_iff_left_iff_imp]
  intro he hdiag
  have heU : e ∈ edgeUniverse n :=
    (Finset.mem_powersetCard.mp s.2).1 he
  exact (⊤ : SimpleGraph (Fin n)).not_isDiag_of_mem_edgeSet
    (SimpleGraph.mem_edgeFinset.mp heU) hdiag

/-- Every unordered sample produces a graph with exactly `m` edges. -/
@[simp]
theorem card_graphOfChoice {n m : ℕ} (s : EdgeChoices n m) :
    (graphOfChoice s).edgeFinset.card = m := by
  rw [edgeFinset_graphOfChoice,
    (Finset.mem_powersetCard.mp s.2).2]

/-- The uniform PMF on unordered `m`-edge samples. -/
def uniformChoices (n m : ℕ) [Nonempty (EdgeChoices n m)] :
    PMF (EdgeChoices n m) :=
  PMF.uniformOfFintype (EdgeChoices n m)

/-- Exact finite-count formula for every graph event in the unordered model. -/
theorem uniformChoices_event (n m : ℕ) [Nonempty (EdgeChoices n m)]
    (P : SimpleGraph (Fin n) → Prop) :
    (uniformChoices n m).toOuterMeasure {s | P (graphOfChoice s)} =
      Fintype.card
          ↥({s : EdgeChoices n m | P (graphOfChoice s)} :
            Set (EdgeChoices n m)) /
        ((n.choose 2).choose m) := by
  unfold uniformChoices
  rw [PMF.toOuterMeasure_uniformOfFintype_apply, card_edgeChoices]

/-- The number of `m`-edge samples containing a fixed edge set `a`. -/
theorem card_choices_containing {n m : ℕ}
    (a : Finset (Sym2 (Fin n))) (haU : a ⊆ edgeUniverse n)
    (ham : a.card ≤ m) :
    Fintype.card {s : EdgeChoices n m // a ⊆ s.1} =
      Nat.choose (n.choose 2 - a.card) (m - a.card) := by
  let t := ((edgeUniverse n).powersetCard m).filter (fun s ↦ a ⊆ s)
  let e : {s : EdgeChoices n m // a ⊆ s.1} ≃ ↥t :=
    { toFun := fun s ↦
        ⟨s.1.1, Finset.mem_filter.mpr ⟨s.1.2, s.2⟩⟩
      invFun := fun s ↦
        ⟨⟨s.1, (Finset.mem_filter.mp s.2).1⟩,
          (Finset.mem_filter.mp s.2).2⟩
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ rfl }
  rw [Fintype.card_congr e, Fintype.card_coe]
  change
    (((edgeUniverse n).powersetCard m).filter
      (fun s ↦ a ⊆ s)).card = _
  rw [Finset.card_filter_powersetCard_subset a (edgeUniverse n) m haU ham,
    edgeUniverse_card]

/-- Exact probability that a uniform `m`-edge sample contains a prescribed
edge set `a`. -/
theorem uniformChoices_containing {n m : ℕ}
    [Nonempty (EdgeChoices n m)] (a : Finset (Sym2 (Fin n)))
    (haU : a ⊆ edgeUniverse n) (ham : a.card ≤ m) :
    (uniformChoices n m).toOuterMeasure {s | a ⊆ s.1} =
      (Nat.choose (n.choose 2 - a.card) (m - a.card) : ℝ≥0∞) /
        Nat.choose (n.choose 2) m := by
  unfold uniformChoices
  rw [PMF.toOuterMeasure_uniformOfFintype_apply, card_edgeChoices]
  congr 1
  exact_mod_cast card_choices_containing a haU ham

/-! ## Upward local LYM -/

/-- The upward local LYM inequality.  Mathlib supplies the downward form;
applying it to complements and using `shadow_compls` gives this version. -/
theorem local_upLYM_div {α : Type*} [Fintype α] [DecidableEq α]
    {A : Finset (Finset α)} {r : ℕ} (hr : r < Fintype.card α)
    (hA : (A : Set (Finset α)).Sized r) :
    (A.card : ℚ≥0) / (Fintype.card α).choose r ≤
      (A.upShadow.card : ℚ≥0) /
        (Fintype.card α).choose (r + 1) := by
  have h := Finset.local_lubell_yamamoto_meshalkin_inequality_div
    (𝕜 := ℚ≥0) (Nat.ne_of_gt (Nat.sub_pos_of_lt hr)) hA.compls
  rw [Finset.card_compls, Finset.shadow_compls, Finset.card_compls,
    Nat.choose_symm hr.le, Nat.sub_sub,
    Nat.choose_symm (Nat.succ_le_iff.mpr hr)] at h
  exact h

end

end Erdos746.Counting
