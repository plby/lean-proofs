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
import ErdosProblems.Erdos565.ContainerInvariants
import ErdosProblems.Erdos565.ContainerWeight

/-!
# The canonical selector in the finite hypergraph container algorithm

This file formalizes the choice made at a nonterminal state.  The stop test is
exactly

`wₚ(H^{>1}) ≤ p |C(H)|`,

where `C(H)` is the set of vertices not forbidden by a singleton edge.  When
the test fails, weighted incidence double counting produces a legal heavy
singleton seed.  Finite minimization then chooses the least possible layer and
an inclusion-maximal heavy seed in that layer.
-/

open scoped BigOperators

namespace Erdos565
namespace ContainerSelector

open Hypergraph

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Layers in which the algorithm searches for a seed. -/
def activeLayers (s : ℕ) : Finset ℕ := Finset.Icc 2 s

/-- The exact link weight used by the Campos--Samotij algorithm. -/
def linkWeight (p : ℝ) (H : Hypergraph V) (a : ℕ) (L : Finset V) : ℝ :=
  ((H.layer a).link L).pWeight p

/-- The exact threshold for a legal seed. -/
noncomputable def threshold (s : ℕ) : ℝ := 1 / (4 * (s : ℝ))

/-- The algorithm stops when the non-singleton part has sufficiently small
weight compared with the available container vertices. -/
def Stop (p : ℝ) (H : Hypergraph V) : Prop :=
  H.aboveOne.pWeight p ≤ p * H.containerVertices.card

/-- A heavy layer/seed pair with all structural facts needed to perform one
update. -/
structure Candidate (H : Hypergraph V) (p : ℝ) (s : ℕ) where
  layerIndex : ℕ
  seed : Finset V
  two_le_layer : 2 ≤ layerIndex
  layer_le_rank : layerIndex ≤ s
  seed_nonempty : seed.Nonempty
  seed_not_edge : seed ∉ H
  extension : ∃ E ∈ H.layer layerIndex, seed ⊆ E
  heavy : threshold s ≤ linkWeight p H layerIndex seed

/-- The least-layer, inclusion-maximal candidate used by the deterministic
algorithm. -/
structure Choice (H : Hypergraph V) (p : ℝ) (s : ℕ) extends Candidate H p s where
  lower_layer : ∀ b, 2 ≤ b → b < layerIndex → ∀ K : Finset V,
    K.Nonempty → K ∉ H → (∃ E ∈ H.layer b, K ⊆ E) →
      linkWeight p H b K < threshold s
  maximal_seed : ∀ K : Finset V, seed ⊂ K → K ∉ H →
    (∃ E ∈ H.layer layerIndex, K ⊆ E) →
      linkWeight p H layerIndex K < threshold s

/-- Finite minimization in the layer followed by maximum seed cardinality
produces a least-layer, inclusion-maximal heavy seed. -/
theorem exists_choice_of_candidate {H : Hypergraph V} {p : ℝ} {s : ℕ}
    (hex : Nonempty (Candidate H p s)) : Nonempty (Choice H p s) := by
  classical
  let P : ℕ → Prop := fun a => ∃ c : Candidate H p s, c.layerIndex = a
  have hP : ∃ a, P a := by
    obtain ⟨c⟩ := hex
    exact ⟨c.layerIndex, c, rfl⟩
  let a := Nat.find hP
  obtain ⟨c₀, hc₀a⟩ := Nat.find_spec hP
  let seeds : Finset (Finset V) :=
    Finset.univ.filter fun L => ∃ c : Candidate H p s,
      c.layerIndex = a ∧ c.seed = L
  have hseeds : seeds.Nonempty := by
    refine ⟨c₀.seed, ?_⟩
    simp only [seeds, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨c₀, hc₀a, rfl⟩
  obtain ⟨L, hLseed, hLmax⟩ := Finset.exists_max_image seeds Finset.card hseeds
  have hLcand : ∃ c : Candidate H p s,
      c.layerIndex = a ∧ c.seed = L := by
    simpa only [seeds, Finset.mem_filter, Finset.mem_univ, true_and] using hLseed
  obtain ⟨c, hca, hcL⟩ := hLcand
  refine ⟨{
    toCandidate := c
    lower_layer := ?_
    maximal_seed := ?_ }⟩
  · intro b hb2 hba K hKnon hKnot hKext
    by_contra hnotlt
    have hheavy : threshold s ≤ linkWeight p H b K := le_of_not_gt hnotlt
    let d : Candidate H p s := {
      layerIndex := b
      seed := K
      two_le_layer := hb2
      layer_le_rank := (Nat.le_of_lt hba).trans c.layer_le_rank
      seed_nonempty := hKnon
      seed_not_edge := hKnot
      extension := hKext
      heavy := hheavy }
    have hmin₀ := Nat.find_min' hP ⟨d, rfl⟩
    have hmin : c.layerIndex ≤ b := by simpa [a, hca] using hmin₀
    omega
  · intro K hcK hKnot hKext
    by_contra hnotlt
    have hheavy : threshold s ≤ linkWeight p H c.layerIndex K := le_of_not_gt hnotlt
    let d : Candidate H p s := {
      layerIndex := c.layerIndex
      seed := K
      two_le_layer := c.two_le_layer
      layer_le_rank := c.layer_le_rank
      seed_nonempty := c.seed_nonempty.mono hcK.1
      seed_not_edge := hKnot
      extension := hKext
      heavy := hheavy }
    have hKseed : K ∈ seeds := by
      simp only [seeds, Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨d, hca, rfl⟩
    have hcardleL : K.card ≤ L.card := hLmax K hKseed
    have hcardle : K.card ≤ c.seed.card := by simpa [hcL] using hcardleL
    have hcardlt := Finset.card_lt_card hcK
    omega

@[simp] theorem mem_activeLayers {s a : ℕ} :
    a ∈ activeLayers s ↔ 2 ≤ a ∧ a ≤ s := by
  simp [activeLayers]

theorem activeLayers_subset_range_succ (s : ℕ) :
    activeLayers s ⊆ Finset.range (s + 1) := by
  intro a ha
  exact Finset.mem_range.mpr (Nat.lt_succ_of_le (mem_activeLayers.mp ha).2)

theorem card_activeLayers_le_succ (s : ℕ) :
    (activeLayers s).card ≤ s + 1 := by
  exact (Finset.card_le_card (activeLayers_subset_range_succ s)) |>.trans_eq
    (by simp)

/-- Every non-singleton edge of a rank-`s` family belongs to one of the active
uniform layers. -/
theorem aboveOne_subset_biUnion_layers {H : Hypergraph V} {s : ℕ}
    (hbounded : H.IsBounded s) :
    H.aboveOne ⊆ (activeLayers s).biUnion H.layer := by
  intro E hE
  obtain ⟨hEH, htwo⟩ := mem_aboveOne.mp hE
  rw [Finset.mem_biUnion]
  exact ⟨E.card, mem_activeLayers.mpr ⟨htwo, hbounded E hEH⟩,
    mem_layer.mpr ⟨hEH, rfl⟩⟩

/-- A vertex outside the current container cannot occur in an active-layer
edge of an antichain. -/
theorem strictLink_layer_eq_empty_of_not_mem_container {H : Hypergraph V}
    (hanti : H.IsAntichain) {a : ℕ} (ha : 2 ≤ a) {v : V}
    (hv : v ∉ H.containerVertices) :
    (H.layer a).strictLink {v} = ∅ := by
  ext F
  simp only [Finset.notMem_empty, iff_false]
  intro hF
  obtain ⟨_, E, hE, hvE, -⟩ := mem_strictLink.mp hF
  have hsv : ({v} : Finset V) ∈ H := by
    simpa [containerVertices] using hv
  have hEq : ({v} : Finset V) = E := hanti hsv (mem_layer.mp hE).1 hvE
  have hcard : E.card = 1 := by simpa [← hEq]
  have haEq : E.card = a := (mem_layer.mp hE).2
  omega

theorem linkWeight_eq_zero_of_not_mem_container {H : Hypergraph V}
    (hanti : H.IsAntichain) {p : ℝ} {s a : ℕ} (ha : a ∈ activeLayers s)
    {v : V} (hv : v ∉ H.containerVertices) :
    linkWeight p H a {v} = 0 := by
  have hcard : ({v} : Finset V).card < a := by
    simp only [Finset.card_singleton]
    exact (mem_activeLayers.mp ha).1
  rw [linkWeight, ← ContainerWeight.strictLink_layer_eq_link_of_card_lt hcard,
    strictLink_layer_eq_empty_of_not_mem_container hanti (mem_activeLayers.mp ha).1 hv]
  exact pWeight_empty p

theorem aboveOne_pWeight_le_sum_layers {H : Hypergraph V} {s : ℕ}
    (hbounded : H.IsBounded s) {p : ℝ} (hp : 0 ≤ p) :
    H.aboveOne.pWeight p ≤
      ∑ a ∈ activeLayers s, (H.layer a).pWeight p := by
  calc
    H.aboveOne.pWeight p ≤
        Hypergraph.pWeight ((activeLayers s).biUnion H.layer) p :=
      pWeight_mono (aboveOne_subset_biUnion_layers hbounded) hp
    _ ≤ ∑ a ∈ activeLayers s, (H.layer a).pWeight p :=
      ContainerWeight.pWeight_biUnion_le _ _ hp

theorem sum_layers_le_weighted_sum (H : Hypergraph V) (s : ℕ) {p : ℝ}
    (hp : 0 ≤ p) :
    ∑ a ∈ activeLayers s, (H.layer a).pWeight p ≤
      ∑ a ∈ activeLayers s, (a : ℝ) * (H.layer a).pWeight p := by
  apply Finset.sum_le_sum
  intro a ha
  have hnonneg := (H.layer a).pWeight_nonneg hp
  have haR : (1 : ℝ) ≤ a := by
    exact_mod_cast (show 1 ≤ a from (mem_activeLayers.mp ha).1.trans' (by omega))
  nlinarith

theorem weighted_sum_eq_incidence (H : Hypergraph V) (s : ℕ) (p : ℝ) :
    ∑ a ∈ activeLayers s, (a : ℝ) * (H.layer a).pWeight p =
      ∑ v : V, p * ∑ a ∈ activeLayers s, linkWeight p H a {v} := by
  calc
    ∑ a ∈ activeLayers s, (a : ℝ) * (H.layer a).pWeight p =
        ∑ a ∈ activeLayers s, ∑ v : V, p * linkWeight p H a {v} := by
      apply Finset.sum_congr rfl
      intro a ha
      rw [← ContainerWeight.sum_singleton_strictLink_pWeight_layer H a
        (mem_activeLayers.mp ha).1 p]
      apply Finset.sum_congr rfl
      intro v _
      have hcard : ({v} : Finset V).card < a := by
        simp only [Finset.card_singleton]
        exact (mem_activeLayers.mp ha).1
      rw [ContainerWeight.strictLink_layer_eq_link_of_card_lt hcard]
      rfl
    _ = ∑ v : V, ∑ a ∈ activeLayers s, p * linkWeight p H a {v} := by
      rw [Finset.sum_comm]
    _ = ∑ v : V, p * ∑ a ∈ activeLayers s, linkWeight p H a {v} := by
      apply Finset.sum_congr rfl
      intro v _
      rw [Finset.mul_sum]

theorem incidence_eq_container_sum {H : Hypergraph V} (hanti : H.IsAntichain)
    (s : ℕ) (p : ℝ) :
    (∑ v : V, p * ∑ a ∈ activeLayers s, linkWeight p H a {v}) =
      ∑ v ∈ H.containerVertices,
        p * ∑ a ∈ activeLayers s, linkWeight p H a {v} := by
  symm
  apply Finset.sum_subset (Finset.subset_univ H.containerVertices)
  intro v _ hv
  have hzero : ∀ a ∈ activeLayers s, linkWeight p H a {v} = 0 :=
    fun a ha => linkWeight_eq_zero_of_not_mem_container hanti ha hv
  have hsum : ∑ a ∈ activeLayers s, linkWeight p H a {v} = 0 := by
    exact Finset.sum_eq_zero hzero
  rw [hsum, mul_zero]

theorem card_activeLayers_cast_div_le_one {s : ℕ} (hs : 0 < s) :
    ((activeLayers s).card : ℝ) * (1 / ((s : ℝ) + 1)) ≤ 1 := by
  have hcard := card_activeLayers_le_succ s
  have hcast : ((activeLayers s).card : ℝ) ≤ (s : ℝ) + 1 := by
    exact_mod_cast hcard
  have hpos : (0 : ℝ) < (s : ℝ) + 1 := by positivity
  calc
    ((activeLayers s).card : ℝ) * (1 / ((s : ℝ) + 1)) ≤
        ((s : ℝ) + 1) * (1 / ((s : ℝ) + 1)) :=
      mul_le_mul_of_nonneg_right hcast (by positivity)
    _ = 1 := by simp [one_div, hpos.ne']

theorem threshold_le_succ_recip {s : ℕ} (hs : 0 < s) :
    threshold s ≤ 1 / ((s : ℝ) + 1) := by
  have hsR : (0 : ℝ) < s := by exact_mod_cast hs
  have hsOne : (1 : ℝ) ≤ s := by exact_mod_cast hs
  rw [threshold]
  apply one_div_le_one_div_of_le (by positivity)
  nlinarith

/-- Failure of the exact stopping test produces a legal heavy singleton seed.

The proof preserves the quantitative argument: total weighted singleton-link
incidence dominates `wₚ(H^{>1})`; vertices outside the container contribute
zero; averaging first over container vertices and then over at most `s + 1`
active layers gives a link heavier than `1/(s+1)`, hence heavier than the
required `1/(4s)` threshold. -/
theorem exists_candidate_of_not_stop {H : Hypergraph V} {p : ℝ} {s : ℕ}
    (hs : 0 < s) (hp : 0 < p) (hanti : H.IsAntichain)
    (hbounded : H.IsBounded s) (hstop : ¬ Stop p H) :
    Nonempty (Candidate H p s) := by
  classical
  have hfailed : p * (H.containerVertices.card : ℝ) < H.aboveOne.pWeight p := by
    simpa [Stop] using lt_of_not_ge hstop
  have htotal : p * (H.containerVertices.card : ℝ) <
      ∑ v ∈ H.containerVertices,
        p * ∑ a ∈ activeLayers s, linkWeight p H a {v} := by
    calc
      p * (H.containerVertices.card : ℝ) < H.aboveOne.pWeight p := hfailed
      _ ≤ ∑ a ∈ activeLayers s, (H.layer a).pWeight p :=
        aboveOne_pWeight_le_sum_layers hbounded hp.le
      _ ≤ ∑ a ∈ activeLayers s, (a : ℝ) * (H.layer a).pWeight p :=
        sum_layers_le_weighted_sum H s hp.le
      _ = ∑ v : V, p * ∑ a ∈ activeLayers s, linkWeight p H a {v} :=
        weighted_sum_eq_incidence H s p
      _ = ∑ v ∈ H.containerVertices,
          p * ∑ a ∈ activeLayers s, linkWeight p H a {v} :=
        incidence_eq_container_sum hanti s p
  have havg : (H.containerVertices.card : ℝ) <
      ∑ v ∈ H.containerVertices,
        ∑ a ∈ activeLayers s, linkWeight p H a {v} := by
    rw [← Finset.mul_sum] at htotal
    nlinarith
  have hvsum : ∃ v ∈ H.containerVertices,
      1 < ∑ a ∈ activeLayers s, linkWeight p H a {v} := by
    have : (∑ _v ∈ H.containerVertices, (1 : ℝ)) <
        ∑ v ∈ H.containerVertices,
          ∑ a ∈ activeLayers s, linkWeight p H a {v} := by
      simpa using havg
    exact Finset.exists_lt_of_sum_lt this
  obtain ⟨v, hvC, hvsum⟩ := hvsum
  have hbenchmark :
      ∑ _a ∈ activeLayers s, (1 / ((s : ℝ) + 1)) <
        ∑ a ∈ activeLayers s, linkWeight p H a {v} := by
    have hconst : ∑ _a ∈ activeLayers s, (1 / ((s : ℝ) + 1)) ≤ 1 := by
      simpa using card_activeLayers_cast_div_le_one hs
    exact hconst.trans_lt hvsum
  obtain ⟨a, ha, haheavy⟩ := Finset.exists_lt_of_sum_lt hbenchmark
  have hlinkpos : 0 < linkWeight p H a {v} := by
    have : (0 : ℝ) < 1 / ((s : ℝ) + 1) := by positivity
    exact this.trans haheavy
  have hlinknonempty : ((H.layer a).link {v}).Nonempty := by
    by_contra hempty
    have heq : (H.layer a).link {v} = ∅ := Finset.not_nonempty_iff_eq_empty.mp hempty
    rw [linkWeight, heq, pWeight_empty] at hlinkpos
    exact lt_irrefl 0 hlinkpos
  obtain ⟨F, hF⟩ := hlinknonempty
  obtain ⟨E, hE, hvE, -⟩ := mem_link.mp hF
  refine ⟨{
    layerIndex := a
    seed := {v}
    two_le_layer := (mem_activeLayers.mp ha).1
    layer_le_rank := (mem_activeLayers.mp ha).2
    seed_nonempty := by simp
    seed_not_edge := mem_containerVertices.mp hvC
    extension := ⟨E, hE, hvE⟩
    heavy := (threshold_le_succ_recip hs).trans haheavy.le }⟩

theorem exists_choice_of_not_stop {H : Hypergraph V} {p : ℝ} {s : ℕ}
    (hs : 0 < s) (hp : 0 < p) (hanti : H.IsAntichain)
    (hbounded : H.IsBounded s) (hstop : ¬ Stop p H) :
    Nonempty (Choice H p s) :=
  exists_choice_of_candidate
    (exists_candidate_of_not_stop hs hp hanti hbounded hstop)

/-- A canonical family-dependent selector.  Its output depends only on `H`,
not on the independent set whose membership determines the branch. -/
structure Selector (p : ℝ) (s : ℕ) where
  choose : ∀ H : Hypergraph V, H.IsAntichain → H.IsBounded s → ¬ Stop p H →
    Choice H p s

noncomputable def canonicalSelector (p : ℝ) (s : ℕ) (hs : 0 < s) (hp : 0 < p) :
    Selector (V := V) p s where
  choose H hanti hbounded hstop :=
    Classical.choice (exists_choice_of_not_stop hs hp hanti hbounded hstop)

/-! ## Preservation of the low-link invariant -/

/-- Every proper lower-rank nonempty seed has small link weight. -/
def LowLinks (H : Hypergraph V) (p : ℝ) (s : ℕ) : Prop :=
  ∀ a, a < s → ∀ L : Finset V, L.Nonempty → L.card < a →
    linkWeight p H a L ≤ 1 / (2 * (s : ℝ))

/-- Every layer of an update is contained in the union of the corresponding
old and inserted layers. -/
theorem layer_update_subset_union (H C : Hypergraph V) (a : ℕ) :
    (H.update C).layer a ⊆ H.layer a ∪ C.layer a := by
  intro E hE
  obtain ⟨hEup, hcard⟩ := mem_layer.mp hE
  rcases mem_update.mp hEup with hEold | hEC
  · exact Finset.mem_union_left _ (mem_layer.mpr ⟨hEold.1, hcard⟩)
  · exact Finset.mem_union_right _ (mem_layer.mpr ⟨hEC, hcard⟩)

theorem link_layer_update_subset_union (H C : Hypergraph V) (a : ℕ)
    (L : Finset V) :
    ((H.update C).layer a).link L ⊆
      (H.layer a).link L ∪ (C.layer a).link L := by
  intro F hF
  obtain ⟨E, hE, hLE, hdiff⟩ := mem_link.mp hF
  rcases layer_update_subset_union H C a hE |> Finset.mem_union.mp with hEH | hEC
  · exact Finset.mem_union_left _ (mem_link.mpr ⟨E, hEH, hLE, hdiff⟩)
  · exact Finset.mem_union_right _ (mem_link.mpr ⟨E, hEC, hLE, hdiff⟩)

theorem linkWeight_update_le_add (H C : Hypergraph V) (a : ℕ) (L : Finset V)
    {p : ℝ} (hp : 0 ≤ p) :
    linkWeight p (H.update C) a L ≤
      linkWeight p H a L + linkWeight p C a L := by
  calc
    linkWeight p (H.update C) a L ≤
        Hypergraph.pWeight ((H.layer a).link L ∪ (C.layer a).link L) p :=
      pWeight_mono (link_layer_update_subset_union H C a L) hp
    _ ≤ linkWeight p H a L + linkWeight p C a L :=
      ContainerWeight.pWeight_union_le _ _ hp

theorem layer_eq_empty_of_uniform_of_ne {C : Hypergraph V} {u a : ℕ}
    (hC : C.IsUniform u) (hau : a ≠ u) : C.layer a = ∅ := by
  ext E
  simp only [mem_layer, Finset.notMem_empty, iff_false]
  rintro ⟨hEC, hcard⟩
  exact hau (hcard ▸ hC E hEC)

theorem linkWeight_layer_eq_zero_of_uniform_of_ne {C : Hypergraph V} {u a : ℕ}
    (hC : C.IsUniform u) (hau : a ≠ u) (p : ℝ) (L : Finset V) :
    linkWeight p C a L = 0 := by
  rw [linkWeight, layer_eq_empty_of_uniform_of_ne hC hau]
  have hlink : (∅ : Hypergraph V).link L = ∅ := by
    ext E
    simp [Hypergraph.link]
  rw [hlink, pWeight_empty]

theorem linkWeight_update_le_old_of_uniform_of_ne {H C : Hypergraph V}
    {u a : ℕ} (hC : C.IsUniform u) (hau : a ≠ u) {p : ℝ}
    (hp : 0 ≤ p) (L : Finset V) :
    linkWeight p (H.update C) a L ≤ linkWeight p H a L := by
  have h := linkWeight_update_le_add H C a L hp
  rw [linkWeight_layer_eq_zero_of_uniform_of_ne hC hau p L, add_zero] at h
  exact h

theorem Choice.old_link_lt_threshold {H : Hypergraph V} {p : ℝ} {s : ℕ}
    (choice : Choice H p s) (hanti : H.IsAntichain) (hs : 0 < s)
    {b : ℕ} (hb : b < choice.layerIndex) {K : Finset V}
    (hK : K.Nonempty) (hKb : K.card < b) :
    linkWeight p H b K < threshold s := by
  have hb2 : 2 ≤ b := by
    have hKpos : 0 < K.card := Finset.card_pos.mpr hK
    omega
  by_cases hlink : ((H.layer b).link K).Nonempty
  · obtain ⟨F, hF⟩ := hlink
    obtain ⟨E, hE, hKE, -⟩ := mem_link.mp hF
    have hne : K ≠ E := by
      intro hEq
      have hcardE : E.card = b := (mem_layer.mp hE).2
      subst E
      omega
    have hproper : K ⊂ E := Finset.ssubset_iff_subset_ne.mpr ⟨hKE, hne⟩
    have hKnot : K ∉ H := by
      intro hKH
      exact hne (hanti hKH (mem_layer.mp hE).1 hKE)
    exact choice.lower_layer b hb2 hb K hK hKnot ⟨E, hE, hKE⟩
  · have heq : (H.layer b).link K = ∅ := Finset.not_nonempty_iff_eq_empty.mp hlink
    rw [linkWeight, heq, pWeight_empty]
    rw [threshold]
    positivity

/-- The singleton rejection family is uniform of rank equal to the seed size. -/
theorem singleton_isUniform (L : Finset V) :
    ({L} : Hypergraph V).IsUniform L.card := by
  intro E hE
  have hEq : E = L := Finset.mem_singleton.mp hE
  subst E
  rfl

/-- Link weight inside a singleton replacement is at most `p` below its
uniform rank. -/
theorem linkWeight_singleton_le_p {p : ℝ} (hp : 0 ≤ p) (hp1 : p ≤ 1)
    {L K : Finset V} (hKcard : K.card < L.card) :
    linkWeight p ({L} : Hypergraph V) L.card K ≤ p := by
  have hlayer : ({L} : Hypergraph V).layer L.card = {L} :=
    (isUniform_iff_layer_eq ({L} : Hypergraph V) L.card).mp (singleton_isUniform L)
  by_cases hKL : K ⊆ L
  · rw [linkWeight, hlayer, link_singleton_of_subset hKL, pWeight, weight]
    simp only [Finset.sum_singleton, Nat.cast_id]
    rw [Finset.card_sdiff_of_subset hKL]
    have hone : 1 ≤ L.card - K.card := by omega
    simpa using (pow_le_pow_of_le_one hp hp1 hone)
  · rw [linkWeight, hlayer, link_singleton_of_not_subset hKL, pWeight_empty]
    exact hp

theorem two_threshold_eq {s : ℕ} :
    threshold s + threshold s = 1 / (2 * (s : ℝ)) := by
  rw [threshold]
  ring

/-- Rejecting the selected seed preserves all low-link bounds. -/
theorem lowLinks_update_reject {H : Hypergraph V} {p : ℝ} {s : ℕ}
    (hs : 0 < s) (hp : 0 ≤ p) (hp1 : p ≤ 1) (hpThreshold : p ≤ threshold s)
    (hanti : H.IsAntichain) (hlow : LowLinks H p s) (choice : Choice H p s) :
    LowLinks (H.update ({choice.seed} : Hypergraph V)) p s := by
  intro b hbs K hK hKb
  let u := choice.seed.card
  have hCu : ({choice.seed} : Hypergraph V).IsUniform u := singleton_isUniform choice.seed
  have hseedlt : choice.seed.card < choice.layerIndex :=
    seed_card_lt_layer choice.extension choice.seed_not_edge
  by_cases hbu : b = u
  · subst b
    have hold : linkWeight p H u K < threshold s :=
      choice.old_link_lt_threshold hanti hs hseedlt hK hKb
    have hnew : linkWeight p ({choice.seed} : Hypergraph V) u K ≤ threshold s :=
      (linkWeight_singleton_le_p hp hp1 hKb).trans hpThreshold
    have hup := linkWeight_update_le_add H ({choice.seed} : Hypergraph V) u K hp
    have hstrict :
        linkWeight p (H.update ({choice.seed} : Hypergraph V)) u K <
          1 / (2 * (s : ℝ)) := by
      calc
        linkWeight p (H.update ({choice.seed} : Hypergraph V)) u K ≤
            linkWeight p H u K + linkWeight p ({choice.seed} : Hypergraph V) u K := hup
        _ < threshold s + threshold s := add_lt_add_of_lt_of_le hold hnew
        _ = 1 / (2 * (s : ℝ)) := two_threshold_eq
    exact hstrict.le
  · exact (linkWeight_update_le_old_of_uniform_of_ne hCu hbu hp K).trans
      (hlow b hbs K hK hKb)

/-- The accepting replacement has the expected lower uniform rank. -/
theorem acceptReplacement_isUniform {H : Hypergraph V} {p : ℝ} {s : ℕ}
    (choice : Choice H p s) :
    ((H.layer choice.layerIndex).link choice.seed).IsUniform
      (choice.layerIndex - choice.seed.card) :=
  link_layer_isUniform H choice.layerIndex choice.seed

/-- Maximality of the chosen seed controls every lower link inside the
accepting replacement. -/
theorem Choice.accept_link_lt_threshold {H : Hypergraph V} {p : ℝ} {s : ℕ}
    (choice : Choice H p s) (hanti : H.IsAntichain) (hs : 0 < s)
    {K : Finset V} (hK : K.Nonempty)
    (hKcard : K.card < choice.layerIndex - choice.seed.card) :
    linkWeight p ((H.layer choice.layerIndex).link choice.seed)
      (choice.layerIndex - choice.seed.card) K < threshold s := by
  let C := (H.layer choice.layerIndex).link choice.seed
  let u := choice.layerIndex - choice.seed.card
  have hCu : C.IsUniform u := acceptReplacement_isUniform choice
  have hlayer : C.layer u = C := (isUniform_iff_layer_eq C u).mp hCu
  change linkWeight p C u K < threshold s
  by_cases hlink : (C.layer u).link K |>.Nonempty
  · obtain ⟨F, hF⟩ := hlink
    obtain ⟨G, hG, hKG, -⟩ := mem_link.mp hF
    have hGC : G ∈ C := hlayer ▸ hG
    obtain ⟨E, hE, hseedE, hdiff⟩ := mem_link.mp hGC
    have hGdis : Disjoint G choice.seed := link_edge_disjoint hGC
    have hdis : Disjoint choice.seed K := by
      rw [Finset.disjoint_left]
      intro x hxseed hxK
      exact (Finset.disjoint_left.mp hGdis) (hKG hxK) hxseed
    have hseedUnion : choice.seed ⊂ choice.seed ∪ K := by
      refine Finset.ssubset_iff_subset_ne.mpr ⟨Finset.subset_union_left, ?_⟩
      intro heq
      have hKsub : K ⊆ choice.seed := by
        intro x hxK
        exact heq ▸ Finset.mem_union_right choice.seed hxK
      obtain ⟨x, hxK⟩ := hK
      exact (Finset.disjoint_left.mp hdis) (hKsub hxK) hxK
    have hUnionE : choice.seed ∪ K ⊆ E := by
      apply Finset.union_subset hseedE
      exact hKG.trans (hdiff ▸ Finset.sdiff_subset)
    have hseedle : choice.seed.card ≤ choice.layerIndex := by
      exact (seed_card_lt_layer choice.extension choice.seed_not_edge).le
    have hUnionCard : (choice.seed ∪ K).card < choice.layerIndex := by
      rw [Finset.card_union_of_disjoint hdis]
      omega
    have hUnionNe : choice.seed ∪ K ≠ E := by
      intro heq
      have hEcard : E.card = choice.layerIndex := (mem_layer.mp hE).2
      rw [heq, hEcard] at hUnionCard
      exact (lt_irrefl _ hUnionCard)
    have hUnionNot : choice.seed ∪ K ∉ H := by
      intro hmem
      exact hUnionNe (hanti hmem (mem_layer.mp hE).1 hUnionE)
    have hmax := choice.maximal_seed (choice.seed ∪ K) hseedUnion hUnionNot
      ⟨E, hE, hUnionE⟩
    rw [linkWeight, hlayer]
    change (((H.layer choice.layerIndex).link choice.seed).link K).pWeight p < threshold s
    rw [link_link_of_disjoint (H.layer choice.layerIndex) hdis]
    exact hmax
  · have heq : (C.layer u).link K = ∅ := Finset.not_nonempty_iff_eq_empty.mp hlink
    rw [linkWeight, heq, pWeight_empty]
    rw [threshold]
    positivity

/-- Accepting the selected seed preserves all low-link bounds. -/
theorem lowLinks_update_accept {H : Hypergraph V} {p : ℝ} {s : ℕ}
    (hs : 0 < s) (hp : 0 ≤ p) (hanti : H.IsAntichain)
    (hlow : LowLinks H p s) (choice : Choice H p s) :
    LowLinks
      (H.update ((H.layer choice.layerIndex).link choice.seed)) p s := by
  intro b hbs K hK hKb
  let C := (H.layer choice.layerIndex).link choice.seed
  let u := choice.layerIndex - choice.seed.card
  have hCu : C.IsUniform u := acceptReplacement_isUniform choice
  have hseedlt : choice.seed.card < choice.layerIndex :=
    seed_card_lt_layer choice.extension choice.seed_not_edge
  have hult : u < choice.layerIndex := by
    dsimp [u]
    have hpos : 0 < choice.seed.card := Finset.card_pos.mpr choice.seed_nonempty
    omega
  by_cases hbu : b = u
  · subst b
    have hold : linkWeight p H u K < threshold s :=
      choice.old_link_lt_threshold hanti hs hult hK hKb
    have hnew : linkWeight p C u K < threshold s := by
      exact choice.accept_link_lt_threshold hanti hs hK hKb
    have hup := linkWeight_update_le_add H C u K hp
    have hstrict :
        linkWeight p (H.update ((H.layer choice.layerIndex).link choice.seed)) u K <
          1 / (2 * (s : ℝ)) := by
      calc
        linkWeight p (H.update ((H.layer choice.layerIndex).link choice.seed)) u K =
            linkWeight p (H.update C) u K := rfl
        _ ≤ linkWeight p H u K + linkWeight p C u K := hup
        _ < threshold s + threshold s := add_lt_add hold hnew
        _ = 1 / (2 * (s : ℝ)) := two_threshold_eq
    exact hstrict.le
  · exact (linkWeight_update_le_old_of_uniform_of_ne hCu hbu hp K).trans
      (hlow b hbs K hK hKb)

end ContainerSelector
end Erdos565
