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
import ErdosProblems.Erdos722.Generators
import ErdosProblems.Erdos722.Reserve
import Mathlib

set_option relaxedAutoImplicit true

/-!
# Sparse modular generators for the integral absorber

This file specializes the abstract greedy theorem to `q`-cliques of a
sparse `r`-graph.  It also supplies the deterministic double counts which
convert common-neighbour branching estimates into bounds for saturated
cliques.  These are the finite parts of Lemma 6.2 in the short proof.
-/

namespace Erdos722.IntegralGenerators

open Finset
open Erdos722.Typicality
open Erdos722.Reserve
open Erdos722.Generators

noncomputable section

/-- `q`-sets whose every `r`-edge belongs to `K`. -/
def cliquesIn (n q r : ℕ) (K : Finset (Finset (Fin n))) :
    Finset (Finset (Fin n)) :=
  (uniformEdges n q).filter fun Q ↦ Q.powersetCard r ⊆ K

lemma mem_cliquesIn {Q : Finset (Fin n)} :
    Q ∈ cliquesIn n q r K ↔ Q.card = q ∧ Q.powersetCard r ⊆ K := by
  simp [cliquesIn, mem_uniformEdges]

/-- Edges of `K` extending a prescribed `(r-1)`-face. -/
def rootEdges (K : Finset (Finset (Fin n))) (f : Finset (Fin n)) :
    Finset (Finset (Fin n)) :=
  K.filter fun e ↦ f ⊆ e

lemma rootEdges_uniform {n r : ℕ}
    {K : Finset (Finset (Fin n))} {f : Finset (Fin n)}
    (huniform : ∀ e ∈ K, e.card = r)
    {e : Finset (Fin n)} (he : e ∈ rootEdges K f) : e.card = r := by
  exact huniform e (Finset.mem_filter.mp he).1

private lemma clique_has_rootEdge
    {n q r : ℕ} (hr : 0 < r) (hrq : r ≤ q)
    {K : Finset (Finset (Fin n))} {f Q : Finset (Fin n)}
    (hfcard : f.card = r - 1) (hQ : Q ∈ cliquesIn n q r K)
    (hfQ : f ⊆ Q) :
    ∃ e ∈ rootEdges K f, e ⊆ Q := by
  classical
  have hQcard := (mem_cliquesIn.mp hQ).1
  have hdiffCard : (Q \ f).card = q - (r - 1) := by
    rw [Finset.card_sdiff_of_subset hfQ, hQcard, hfcard]
  have hdiff : (Q \ f).Nonempty := Finset.card_pos.mp (by omega)
  let x := hdiff.choose
  have hx := hdiff.choose_spec
  let e := insert x f
  have hxNotF : x ∉ f := (Finset.mem_sdiff.mp hx).2
  have hecard : e.card = r := by
    change (insert x f).card = r
    rw [Finset.card_insert_of_notMem hxNotF, hfcard]
    omega
  have heQ : e ⊆ Q := by
    intro y hy
    rcases Finset.mem_insert.mp hy with rfl | hy
    · exact (Finset.mem_sdiff.mp hx).1
    · exact hfQ hy
  have heK : e ∈ K := (mem_cliquesIn.mp hQ).2
    (Finset.mem_powersetCard.mpr ⟨heQ, hecard⟩)
  exact ⟨e, Finset.mem_filter.mpr ⟨heK, Finset.subset_insert _ _⟩, heQ⟩

private lemma cliques_through_edge_subset_extensionLevel
    {n q r : ℕ} (hrq : r ≤ q)
    {K : Finset (Finset (Fin n))} {f e : Finset (Fin n)} :
    ((cliquesIn n q r K).filter fun Q ↦ f ⊆ Q ∧ e ⊆ Q) ⊆
      extensionLevel n q r K e (q - r) := by
  intro Q hQ
  have hm := Finset.mem_filter.mp hQ
  have hclique := mem_cliquesIn.mp hm.1
  apply Finset.mem_filter.mpr
  refine ⟨mem_uniformEdges.mpr ?_, hm.2.2, ?_⟩
  · rw [hclique.1, Nat.add_sub_of_le hrq]
  · intro A hA
    exact hclique.2 (Finset.mem_sdiff.mp hA).1

/-- If every root edge has at most `M` full extensions, then a lower face
is contained in at most `|K(f)| * M` cliques of `K`. -/
theorem card_cliques_through_face_le
    {n q r M : ℕ} (hr : 0 < r) (hrq : r ≤ q)
    {K : Finset (Finset (Fin n))}
    (huniform : ∀ e ∈ K, e.card = r)
    (hext : ∀ e ∈ K,
      (extensionLevel n q r K e (q - r)).card ≤ M)
    {f : Finset (Fin n)} (hfcard : f.card = r - 1) :
    ((cliquesIn n q r K).filter fun Q ↦ f ⊆ Q).card ≤
      (rootEdges K f).card * M := by
  let left := (cliquesIn n q r K).filter fun Q ↦ f ⊆ Q
  let right := rootEdges K f
  have hrel := card_mul_le_card_mul_of_relation left right
    (fun Q e ↦ e ⊆ Q) 1 M
    (by
      intro Q hQ
      have hQdata := Finset.mem_filter.mp hQ
      obtain ⟨e, he, heQ⟩ := clique_has_rootEdge hr hrq hfcard
        hQdata.1 hQdata.2
      exact Finset.card_pos.mpr
        ⟨e, Finset.mem_filter.mpr ⟨he, heQ⟩⟩)
    (by
      intro e he
      have hsubAll := cliques_through_edge_subset_extensionLevel
        (n := n) (q := q) (r := r) hrq (K := K) (f := f) (e := e)
      have hsub : (left.filter fun Q ↦ e ⊆ Q) ⊆
          extensionLevel n q r K e (q - r) := by
        intro Q hQ
        have hm := Finset.mem_filter.mp hQ
        have hleft := Finset.mem_filter.mp hm.1
        exact hsubAll (Finset.mem_filter.mpr
          ⟨hleft.1, hleft.2, hm.2⟩)
      exact (Finset.card_le_card hsub).trans
        (hext e (Finset.mem_filter.mp he).1))
  simpa [left, right] using hrel

/-- The exact number of `(r-1)`-faces of one uniform `q`-set. -/
lemma card_lowerFaces_of_mem_cliquesIn
    {Q : Finset (Fin n)} (hQ : Q ∈ cliquesIn n q r K) :
    (((uniformEdges n (r - 1)).filter fun f ↦ f ⊆ Q).card) =
      Nat.choose q (r - 1) := by
  have hQcard := (mem_cliquesIn.mp hQ).1
  have heq : (uniformEdges n (r - 1)).filter (fun f ↦ f ⊆ Q) =
      Q.powersetCard (r - 1) := by
    ext f
    simp [uniformEdges, Finset.mem_powersetCard, and_comm]
  rw [heq, Finset.card_powersetCard, hQcard]

/-- Combining the subgroup-chain bound with incidence double-counting gives
the paper's finite saturated-face estimate. -/
theorem exists_generators_with_saturatedFace_bound
    {N n q r cap : ℕ} (hN : 0 < N)
    (K : Finset (Finset (Fin n))) :
    ∃ selected : Finset (Finset (Fin n)),
      selected ⊆ cliquesIn n q r K ∧
      selected.card ≤ N * K.card ∧
      (∀ f : Finset (Fin n), f.card = r - 1 →
        counterLoad (fun f Q ↦ f ⊆ Q) selected f ≤ cap) ∧
      cap * ((uniformEdges n (r - 1)).filter fun f ↦
        cap ≤ counterLoad (fun f Q ↦ f ⊆ Q) selected f).card ≤
        (N * K.card) * Nat.choose q (r - 1) ∧
      ∀ Q ∈ cliquesIn n q r K,
        InRestrictedModularSpan N r K selected
          (modCliqueBoundaryOn N r K Q) ∨
          ∃ f : Finset (Fin n), f.card = r - 1 ∧ f ⊆ Q ∧
            cap ≤ counterLoad (fun f Q ↦ f ⊆ Q) selected f := by
  obtain ⟨selected, hsub, hcard, hload, hresolve⟩ :=
    exists_bounded_restricted_modular_generators_lowerFaces hN K
      (cliquesIn n q r K)
  have hsat := card_saturatedCounters_mul_le
    (fun f Q : Finset (Fin n) ↦ f ⊆ Q)
    (uniformEdges n (r - 1)) selected cap (Nat.choose q (r - 1))
    (fun Q hQ ↦ by
      rw [card_lowerFaces_of_mem_cliquesIn (hsub hQ)])
  refine ⟨selected, hsub, hcard, hload, ?_, hresolve⟩
  exact hsat.trans (Nat.mul_le_mul_right _ hcard)

noncomputable def saturatedFaces (n r cap : ℕ)
    (selected : Finset (Finset (Fin n))) : Finset (Finset (Fin n)) := by
  classical
  exact (uniformEdges n (r - 1)).filter fun f ↦
    cap ≤ counterLoad (fun f Q ↦ f ⊆ Q) selected f

noncomputable def saturatedCliques (n q r cap : ℕ)
    (K selected : Finset (Finset (Fin n))) : Finset (Finset (Fin n)) := by
  classical
  exact (cliquesIn n q r K).filter fun Q ↦
    ∃ f, f ∈ uniformEdges n (r - 1) ∧ f ⊆ Q ∧
      cap ≤ counterLoad (fun f Q ↦ f ⊆ Q) selected f

lemma mem_saturatedFaces {f : Finset (Fin n)} :
    f ∈ saturatedFaces n r cap selected ↔
      f ∈ uniformEdges n (r - 1) ∧
        cap ≤ counterLoad (fun f Q ↦ f ⊆ Q) selected f := by
  classical
  simp [saturatedFaces]

lemma mem_saturatedCliques {Q : Finset (Fin n)} :
    Q ∈ saturatedCliques n q r cap K selected ↔
      Q ∈ cliquesIn n q r K ∧
        ∃ f, f ∈ uniformEdges n (r - 1) ∧ f ⊆ Q ∧
          cap ≤ counterLoad (fun f Q ↦ f ⊆ Q) selected f := by
  classical
  simp [saturatedCliques]

/-- A saturated clique contains a saturated lower face, so a uniform
per-face clique count bounds the whole saturated family. -/
theorem card_saturatedCliques_le
    {n q r cap M : ℕ} {K selected : Finset (Finset (Fin n))}
    (hface : ∀ f ∈ uniformEdges n (r - 1),
      ((cliquesIn n q r K).filter fun Q ↦ f ⊆ Q).card ≤ M) :
    (saturatedCliques n q r cap K selected).card ≤
      (saturatedFaces n r cap selected).card * M := by
  classical
  let satFaces := saturatedFaces n r cap selected
  let satCliques := saturatedCliques n q r cap K selected
  have hsub : satCliques ⊆
      satFaces.biUnion (fun f ↦ (cliquesIn n q r K).filter (f ⊆ ·)) := by
    intro Q hQ
    have hm : Q ∈ cliquesIn n q r K ∧
        ∃ f, f ∈ uniformEdges n (r - 1) ∧ f ⊆ Q ∧
          cap ≤ counterLoad (fun f Q ↦ f ⊆ Q) selected f := by
      simpa [satCliques, saturatedCliques] using hQ
    obtain ⟨f, hf, hfQ, hsat⟩ := hm.2
    apply Finset.mem_biUnion.mpr
    exact ⟨f, Finset.mem_filter.mpr ⟨hf, hsat⟩,
      Finset.mem_filter.mpr ⟨hm.1, hfQ⟩⟩
  have hcard := Finset.card_le_card hsub
  simpa [satFaces, satCliques] using hcard.trans (by
    calc
      (satFaces.biUnion fun f ↦
          (cliquesIn n q r K).filter (f ⊆ ·)).card ≤
          ∑ f ∈ satFaces, ((cliquesIn n q r K).filter (f ⊆ ·)).card :=
        Finset.card_biUnion_le
      _ ≤ ∑ _f ∈ satFaces, M := by
        apply Finset.sum_le_sum
        intro f hf
        exact hface f (Finset.mem_filter.mp hf).1
      _ = satFaces.card * M := by simp)

/-! ## Independent face and edge caps

The multiplicity-flattening potential needs a small cap on selected
cliques through an `r`-edge, while the modular greedy argument uses a larger
cap on `(r-1)`-faces.  These definitions package the two-threshold output
of `Generators.exists_twoCap_restricted_modular_generators`. -/

noncomputable def saturatedEdges (n r edgeCap : ℕ)
    (selected : Finset (Finset (Fin n))) : Finset (Finset (Fin n)) := by
  classical
  exact (uniformEdges n r).filter fun e ↦
    edgeCap ≤ counterLoad (fun e Q ↦ e ⊆ Q) selected e

noncomputable def twoCapSaturatedCliques
    (n q r faceCap edgeCap : ℕ)
    (K selected : Finset (Finset (Fin n))) :
    Finset (Finset (Fin n)) := by
  classical
  exact (cliquesIn n q r K).filter fun Q ↦
    (∃ f, f.card = r - 1 ∧ f ⊆ Q ∧
      faceCap ≤ counterLoad (fun f Q ↦ f ⊆ Q) selected f) ∨
    ∃ e, e.card = r ∧ e ⊆ Q ∧
      edgeCap ≤ counterLoad (fun e Q ↦ e ⊆ Q) selected e

noncomputable def twoCapUnsaturatedCliques
    (n q r faceCap edgeCap : ℕ)
    (K selected : Finset (Finset (Fin n))) :
    Finset (Finset (Fin n)) :=
  cliquesIn n q r K \
    twoCapSaturatedCliques n q r faceCap edgeCap K selected

lemma mem_saturatedEdges {e : Finset (Fin n)} :
    e ∈ saturatedEdges n r edgeCap selected ↔
      e.card = r ∧
        edgeCap ≤ counterLoad (fun e Q ↦ e ⊆ Q) selected e := by
  classical
  simp [saturatedEdges, uniformEdges]

lemma mem_twoCapSaturatedCliques {Q : Finset (Fin n)} :
    Q ∈ twoCapSaturatedCliques n q r faceCap edgeCap K selected ↔
      Q ∈ cliquesIn n q r K ∧
      ((∃ f, f.card = r - 1 ∧ f ⊆ Q ∧
        faceCap ≤ counterLoad (fun f Q ↦ f ⊆ Q) selected f) ∨
      ∃ e, e.card = r ∧ e ⊆ Q ∧
        edgeCap ≤ counterLoad (fun e Q ↦ e ⊆ Q) selected e) := by
  classical
  simp [twoCapSaturatedCliques]

lemma mem_twoCapUnsaturatedCliques {Q : Finset (Fin n)} :
    Q ∈ twoCapUnsaturatedCliques n q r faceCap edgeCap K selected ↔
      Q ∈ cliquesIn n q r K ∧
        Q ∉ twoCapSaturatedCliques n q r faceCap edgeCap K selected := by
  simp [twoCapUnsaturatedCliques]

/-- A two-cap saturated clique is charged either to a saturated lower face
or to a saturated edge.  Uniform upper bounds on the two corresponding
clique stars therefore bound the whole exceptional family. -/
theorem card_twoCapSaturatedCliques_le
    {n q r faceCap edgeCap Mface Medge : ℕ}
    {K selected : Finset (Finset (Fin n))}
    (hface : ∀ f ∈ uniformEdges n (r - 1),
      ((cliquesIn n q r K).filter fun Q ↦ f ⊆ Q).card ≤ Mface)
    (hedge : ∀ e ∈ uniformEdges n r,
      ((cliquesIn n q r K).filter fun Q ↦ e ⊆ Q).card ≤ Medge) :
    (twoCapSaturatedCliques n q r faceCap edgeCap K selected).card ≤
      (saturatedFaces n r faceCap selected).card * Mface +
        (saturatedEdges n r edgeCap selected).card * Medge := by
  classical
  let satFaces := saturatedFaces n r faceCap selected
  let satEdges := saturatedEdges n r edgeCap selected
  let faceCover := satFaces.biUnion fun f ↦
    (cliquesIn n q r K).filter fun Q ↦ f ⊆ Q
  let edgeCover := satEdges.biUnion fun e ↦
    (cliquesIn n q r K).filter fun Q ↦ e ⊆ Q
  have hsub : twoCapSaturatedCliques n q r faceCap edgeCap K selected ⊆
      faceCover ∪ edgeCover := by
    intro Q hQ
    have hQdata := mem_twoCapSaturatedCliques.mp hQ
    rcases hQdata.2 with hsat | hsat
    · obtain ⟨f, hfcard, hfQ, hfload⟩ := hsat
      apply Finset.mem_union_left
      apply Finset.mem_biUnion.mpr
      refine ⟨f, ?_, Finset.mem_filter.mpr ⟨hQdata.1, hfQ⟩⟩
      exact mem_saturatedFaces.mpr
        ⟨mem_uniformEdges.mpr hfcard, hfload⟩
    · obtain ⟨e, hecard, heQ, heload⟩ := hsat
      apply Finset.mem_union_right
      apply Finset.mem_biUnion.mpr
      refine ⟨e, ?_, Finset.mem_filter.mpr ⟨hQdata.1, heQ⟩⟩
      exact mem_saturatedEdges.mpr ⟨hecard, heload⟩
  calc
    (twoCapSaturatedCliques n q r faceCap edgeCap K selected).card ≤
        (faceCover ∪ edgeCover).card := Finset.card_le_card hsub
    _ ≤ faceCover.card + edgeCover.card := Finset.card_union_le _ _
    _ ≤ satFaces.card * Mface + satEdges.card * Medge := by
      apply Nat.add_le_add
      · calc
          faceCover.card ≤ ∑ f ∈ satFaces,
              ((cliquesIn n q r K).filter fun Q ↦ f ⊆ Q).card :=
            Finset.card_biUnion_le
          _ ≤ ∑ _f ∈ satFaces, Mface := by
            apply Finset.sum_le_sum
            intro f hf
            exact hface f (mem_saturatedFaces.mp hf).1
          _ = satFaces.card * Mface := by simp
      · calc
          edgeCover.card ≤ ∑ e ∈ satEdges,
              ((cliquesIn n q r K).filter fun Q ↦ e ⊆ Q).card :=
            Finset.card_biUnion_le
          _ ≤ ∑ _e ∈ satEdges, Medge := by
            apply Finset.sum_le_sum
            intro e he
            exact hedge e (mem_uniformEdges.mpr
              (mem_saturatedEdges.mp he).1)
          _ = satEdges.card * Medge := by simp

lemma card_edges_of_mem_cliquesIn
    {Q : Finset (Fin n)} (hQ : Q ∈ cliquesIn n q r K) :
    ((uniformEdges n r).filter fun e ↦ e ⊆ Q).card = Nat.choose q r := by
  have hQcard := (mem_cliquesIn.mp hQ).1
  have heq : (uniformEdges n r).filter (fun e ↦ e ⊆ Q) =
      Q.powersetCard r := by
    ext e
    simp [uniformEdges, Finset.mem_powersetCard, and_comm]
  rw [heq, Finset.card_powersetCard, hQcard]

/-- Complete two-threshold greedy output.  Besides both load caps it records
the two incidence double counts and modular generation of every clique that
is unsaturated in both senses. -/
theorem exists_twoCap_generators
    {N n q r faceCap edgeCap : ℕ} (hN : 0 < N)
    (K : Finset (Finset (Fin n))) :
    ∃ selected : Finset (Finset (Fin n)),
      selected ⊆ cliquesIn n q r K ∧
      selected.card ≤ N * K.card ∧
      (∀ f : Finset (Fin n), f.card = r - 1 →
        counterLoad (fun f Q ↦ f ⊆ Q) selected f ≤ faceCap) ∧
      (∀ e : Finset (Fin n), e.card = r →
        counterLoad (fun e Q ↦ e ⊆ Q) selected e ≤ edgeCap) ∧
      faceCap * (saturatedFaces n r faceCap selected).card ≤
        (N * K.card) * Nat.choose q (r - 1) ∧
      edgeCap * (saturatedEdges n r edgeCap selected).card ≤
        (N * K.card) * Nat.choose q r ∧
      ∀ Q ∈ twoCapUnsaturatedCliques
          n q r faceCap edgeCap K selected,
        InRestrictedModularSpan N r K selected
          (modCliqueBoundaryOn N r K Q) := by
  obtain ⟨selected, hselected, hselectedCard, hfaceLoad, hedgeLoad,
      hresolve⟩ :=
    exists_twoCap_restricted_modular_generators hN K
      (cliquesIn n q r K)
  have hfaceCount : faceCap * (saturatedFaces n r faceCap selected).card ≤
      selected.card * Nat.choose q (r - 1) := by
    simpa [saturatedFaces] using card_saturatedCounters_mul_le
      (fun f Q : Finset (Fin n) ↦ f ⊆ Q)
      (uniformEdges n (r - 1)) selected faceCap (Nat.choose q (r - 1))
      (fun Q hQ ↦ by
        rw [card_lowerFaces_of_mem_cliquesIn (hselected hQ)])
  have hedgeCount : edgeCap * (saturatedEdges n r edgeCap selected).card ≤
      selected.card * Nat.choose q r := by
    simpa [saturatedEdges] using card_saturatedCounters_mul_le
      (fun e Q : Finset (Fin n) ↦ e ⊆ Q)
      (uniformEdges n r) selected edgeCap (Nat.choose q r)
      (fun Q hQ ↦ by
        rw [card_edges_of_mem_cliquesIn (hselected hQ)])
  refine ⟨selected, hselected, hselectedCard, hfaceLoad, hedgeLoad,
    hfaceCount.trans (Nat.mul_le_mul_right _ hselectedCard),
    hedgeCount.trans (Nat.mul_le_mul_right _ hselectedCard), ?_⟩
  intro Q hQ
  have hQdata := mem_twoCapUnsaturatedCliques.mp hQ
  rcases hresolve Q hQdata.1 with hspan | hsat
  · exact hspan
  · exfalso
    apply hQdata.2
    apply mem_twoCapSaturatedCliques.mpr
    exact ⟨hQdata.1, hsat⟩

/-! ## Consequences of the simultaneous reserve-typicality event -/

/-- The upper half of simultaneous typicality, with the trivial
`|cleanVertices| ≤ n` estimate made explicit.  Keeping the number of roots
in the exponent is essential in the integral-absorber count. -/
theorem typical_commonNeighbors_upper
    {n q r : ℕ} (hr : 0 < r)
    (p : Set.Icc (0 : ℝ) 1)
    (ω : {a // a ∈ uniformEdges n r} → Bool)
    (htyp : ∀ roots, ∀ hroots :
      roots ∈ rootFamilies n r (Nat.choose q r),
      commonMean n roots p / 2 <
        Erdos722.Probability.finiteRandomSum
          (fun x ↦ commonNeighborIndicator n r roots hr
            (root_card_of_mem_rootFamilies hroots) x) ω ∧
      Erdos722.Probability.finiteRandomSum
          (fun x ↦ commonNeighborIndicator n r roots hr
            (root_card_of_mem_rootFamilies hroots) x) ω <
        2 * commonMean n roots p)
    {roots : Finset (Finset (Fin n))}
    (hroots : roots ∈ rootFamilies n r (Nat.choose q r)) :
    ((commonNeighbors n r roots hr
        (root_card_of_mem_rootFamilies hroots) ω).card : ℝ) <
      2 * n * (p : ℝ) ^ roots.card := by
  have hupp := (htyp roots hroots).2
  rw [← card_commonNeighbors n r roots hr
    (root_card_of_mem_rootFamilies hroots) ω] at hupp
  have hcleanNat : (cleanVertices n roots).card ≤ n := by
    simpa using Finset.card_le_univ (cleanVertices n roots)
  have hclean : ((cleanVertices n roots).card : ℝ) ≤ n := by
    exact_mod_cast hcleanNat
  calc
    ((commonNeighbors n r roots hr
        (root_card_of_mem_rootFamilies hroots) ω).card : ℝ) <
        2 * commonMean n roots p := hupp
    _ ≤ 2 * n * (p : ℝ) ^ roots.card := by
      unfold commonMean
      have hp : 0 ≤ (p : ℝ) ^ roots.card :=
        pow_nonneg p.property.1 _
      simpa [mul_assoc] using mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hclean (by norm_num : (0 : ℝ) ≤ 2)) hp

/-- Natural-number ceiling of the typical common-neighbour count at
extension level `i`. -/
noncomputable def typicalUpperBranching
    (n r : ℕ) (p : Set.Icc (0 : ℝ) 1) (i : ℕ) : ℕ :=
  Nat.ceil (2 * (n : ℝ) * (p : ℝ) ^ Nat.choose (r + i) (r - 1))

/-- Natural-number ceiling of the typical degree of an `(r-1)`-face. -/
noncomputable def typicalFaceDegreeCap
    (n : ℕ) (p : Set.Icc (0 : ℝ) 1) : ℕ :=
  Nat.ceil (2 * (n : ℝ) * (p : ℝ))

lemma le_typicalUpperBranching_cast
    (n r : ℕ) (p : Set.Icc (0 : ℝ) 1) (i : ℕ) :
    2 * (n : ℝ) * (p : ℝ) ^ Nat.choose (r + i) (r - 1) ≤
      typicalUpperBranching n r p i := by
  exact Nat.le_ceil _

lemma le_typicalFaceDegreeCap_cast
    (n : ℕ) (p : Set.Icc (0 : ℝ) 1) :
    2 * (n : ℝ) * (p : ℝ) ≤ typicalFaceDegreeCap n p := by
  exact Nat.le_ceil _

/-- Simultaneous typicality supplies a level-dependent upper branching
cap for every partial clique in the extension tree. -/
theorem typical_extension_upper
    {n q r : ℕ} (hr : 1 < r) (hrq : r < q)
    (p : Set.Icc (0 : ℝ) 1)
    (ω : {a // a ∈ uniformEdges n r} → Bool)
    (U : ℕ → ℕ)
    (htyp : ∀ roots, ∀ hroots :
      roots ∈ rootFamilies n r (Nat.choose q r),
      commonMean n roots p / 2 <
        Erdos722.Probability.finiteRandomSum
          (fun x ↦ commonNeighborIndicator n r roots (by omega)
            (root_card_of_mem_rootFamilies hroots) x) ω ∧
      Erdos722.Probability.finiteRandomSum
          (fun x ↦ commonNeighborIndicator n r roots (by omega)
            (root_card_of_mem_rootFamilies hroots) x) ω <
        2 * commonMean n roots p)
    (hU : ∀ i < q - r,
      2 * (n : ℝ) * (p : ℝ) ^ Nat.choose (r + i) (r - 1) ≤ U i) :
    ∀ e : Finset (Fin n), ∀ i < q - r, ∀ S ∈
      extensionLevel n q r (sampledEdges n r ω) e i,
      (commonNeighbors n r (extensionRoots S r) (by omega)
        (fun f hf ↦ (mem_extensionRoots.mp hf).2) ω).card ≤ U i := by
  intro e i hi S hS
  have hSdata := mem_extensionLevel_data hS
  have hSq : S.card < q := by omega
  have hroots : extensionRoots S r ∈
      rootFamilies n r (Nat.choose q r) :=
    extensionRoots_mem_rootFamilies hSq
  have hrootsCard : (extensionRoots S r).card =
      Nat.choose (r + i) (r - 1) := by
    rw [card_extensionRoots, hSdata.1]
  have hupp := typical_commonNeighbors_upper (q := q) (by omega) p ω htyp hroots
  have hcast :
      ((commonNeighbors n r (extensionRoots S r) (by omega)
          (root_card_of_mem_rootFamilies hroots) ω).card : ℝ) < U i := by
    rw [hrootsCard] at hupp
    exact hupp.trans_le (hU i hi)
  exact_mod_cast hcast.le

/-- The upper extension-tree product furnished by typicality. -/
theorem extensionLevel_final_typical_le
    {n q r : ℕ} (hr : 1 < r) (hrq : r < q)
    (p : Set.Icc (0 : ℝ) 1)
    (ω : {a // a ∈ uniformEdges n r} → Bool)
    (U : ℕ → ℕ)
    (htyp : ∀ roots, ∀ hroots :
      roots ∈ rootFamilies n r (Nat.choose q r),
      commonMean n roots p / 2 <
        Erdos722.Probability.finiteRandomSum
          (fun x ↦ commonNeighborIndicator n r roots (by omega)
            (root_card_of_mem_rootFamilies hroots) x) ω ∧
      Erdos722.Probability.finiteRandomSum
          (fun x ↦ commonNeighborIndicator n r roots (by omega)
            (root_card_of_mem_rootFamilies hroots) x) ω <
        2 * commonMean n roots p)
    (hU : ∀ i < q - r,
      2 * (n : ℝ) * (p : ℝ) ^ Nat.choose (r + i) (r - 1) ≤ U i)
    {e : Finset (Fin n)} (hecard : e.card = r) :
    (extensionLevel n q r (sampledEdges n r ω) e (q - r)).card ≤
      ∏ i ∈ Finset.range (q - r), U i := by
  have hiter := extensionLevel_iterate_upper hr (le_refl (q - r))
    hecard ω U
    (typical_extension_upper hr hrq p ω U htyp hU e)
  simpa [extensionLevel_zero hecard] using hiter

/-- In a typical sampled host, the number of `q`-cliques through a fixed
`(r-1)`-face is bounded by its sampled degree times the full upper
extension-tree product. -/
theorem card_cliques_through_face_typical_le
    {n q r : ℕ} (hr : 1 < r) (hrq : r < q)
    (p : Set.Icc (0 : ℝ) 1)
    (ω : {a // a ∈ uniformEdges n r} → Bool)
    (U : ℕ → ℕ)
    (htyp : ∀ roots, ∀ hroots :
      roots ∈ rootFamilies n r (Nat.choose q r),
      commonMean n roots p / 2 <
        Erdos722.Probability.finiteRandomSum
          (fun x ↦ commonNeighborIndicator n r roots (by omega)
            (root_card_of_mem_rootFamilies hroots) x) ω ∧
      Erdos722.Probability.finiteRandomSum
          (fun x ↦ commonNeighborIndicator n r roots (by omega)
            (root_card_of_mem_rootFamilies hroots) x) ω <
        2 * commonMean n roots p)
    (hU : ∀ i < q - r,
      2 * (n : ℝ) * (p : ℝ) ^ Nat.choose (r + i) (r - 1) ≤ U i)
    {f : Finset (Fin n)} (hfcard : f.card = r - 1) :
    ((cliquesIn n q r (sampledEdges n r ω)).filter fun Q ↦ f ⊆ Q).card ≤
      (rootEdges (sampledEdges n r ω) f).card *
        ∏ i ∈ Finset.range (q - r), U i := by
  apply card_cliques_through_face_le (by omega) hrq.le
  · intro e he
    exact mem_uniformEdges.mp (mem_sampledEdges.mp he).1
  · intro e he
    exact extensionLevel_final_typical_le hr hrq p ω U htyp hU
      (mem_uniformEdges.mp (mem_sampledEdges.mp he).1)
  · exact hfcard

/-- Fully explicit ceiling form of the preceding extension-tree bound. -/
theorem card_cliques_through_face_typicalUpper_le
    {n q r : ℕ} (hr : 1 < r) (hrq : r < q)
    (p : Set.Icc (0 : ℝ) 1)
    (ω : {a // a ∈ uniformEdges n r} → Bool)
    (htyp : ∀ roots, ∀ hroots :
      roots ∈ rootFamilies n r (Nat.choose q r),
      commonMean n roots p / 2 <
        Erdos722.Probability.finiteRandomSum
          (fun x ↦ commonNeighborIndicator n r roots (by omega)
            (root_card_of_mem_rootFamilies hroots) x) ω ∧
      Erdos722.Probability.finiteRandomSum
          (fun x ↦ commonNeighborIndicator n r roots (by omega)
            (root_card_of_mem_rootFamilies hroots) x) ω <
        2 * commonMean n roots p)
    {f : Finset (Fin n)} (hfcard : f.card = r - 1) :
    ((cliquesIn n q r (sampledEdges n r ω)).filter fun Q ↦ f ⊆ Q).card ≤
      typicalFaceDegreeCap n p *
        ∏ i ∈ Finset.range (q - r), typicalUpperBranching n r p i := by
  have htree := card_cliques_through_face_typical_le hr hrq p ω
    (typicalUpperBranching n r p) htyp
    (fun i _hi ↦ le_typicalUpperBranching_cast n r p i) hfcard
  have hdegreeReal :
      ((rootEdges (sampledEdges n r ω) f).card : ℝ) <
        2 * n * (p : ℝ) := by
    have hdegree := typical_localDegree_upper (q := q) (by omega) hrq.le
      p ω htyp f hfcard
    simpa [rootEdges, Erdos722.Reserve.localDegree] using hdegree
  have hdegreeNat :
      (rootEdges (sampledEdges n r ω) f).card ≤
        typicalFaceDegreeCap n p := by
    exact_mod_cast hdegreeReal.le.trans (le_typicalFaceDegreeCap_cast n p)
  exact htree.trans (Nat.mul_le_mul_right _ hdegreeNat)

/-- If the distinguished edge already belongs to the host, reserve-style
extensions are exactly the host cliques through that edge. -/
lemma reserveCandidates_eq_cliquesIn_filter
    {n q r : ℕ} {K : Finset (Finset (Fin n))}
    {e : Finset (Fin n)} (heK : e ∈ K) :
    Erdos722.Reserve.reserveCandidates n q r K e =
      (cliquesIn n q r K).filter fun Q ↦ e ⊆ Q := by
  classical
  ext Q
  constructor
  · intro hQ
    have hQdata := Finset.mem_filter.mp hQ
    apply Finset.mem_filter.mpr
    refine ⟨mem_cliquesIn.mpr ⟨
      (mem_uniformEdges.mp hQdata.1), ?_⟩, hQdata.2.1⟩
    intro g hg
    by_cases hge : g = e
    · simpa [hge] using heK
    · exact hQdata.2.2 (Finset.mem_sdiff.mpr ⟨hg, by simpa using hge⟩)
  · intro hQ
    have hQdata := Finset.mem_filter.mp hQ
    have hclique := mem_cliquesIn.mp hQdata.1
    apply Finset.mem_filter.mpr
    refine ⟨mem_uniformEdges.mpr hclique.1, hQdata.2, ?_⟩
    intro g hg
    exact hclique.2 (Finset.mem_sdiff.mp hg).1

/-- Typicality bounds the number of host cliques through a fixed host
edge by the same upper extension-tree product used at lower faces. -/
theorem card_cliques_through_edge_typicalUpper_le
    {n q r : ℕ} (hr : 1 < r) (hrq : r < q)
    (p : Set.Icc (0 : ℝ) 1)
    (ω : {a // a ∈ uniformEdges n r} → Bool)
    (htyp : ∀ roots, ∀ hroots :
      roots ∈ rootFamilies n r (Nat.choose q r),
      commonMean n roots p / 2 <
        Erdos722.Probability.finiteRandomSum
          (fun x ↦ commonNeighborIndicator n r roots (by omega)
            (root_card_of_mem_rootFamilies hroots) x) ω ∧
      Erdos722.Probability.finiteRandomSum
          (fun x ↦ commonNeighborIndicator n r roots (by omega)
            (root_card_of_mem_rootFamilies hroots) x) ω <
        2 * commonMean n roots p)
    {e : Finset (Fin n)} (hecard : e.card = r) :
    ((cliquesIn n q r (sampledEdges n r ω)).filter fun Q ↦ e ⊆ Q).card ≤
      ∏ i ∈ Finset.range (q - r), typicalUpperBranching n r p i := by
  have hsub :
      ((cliquesIn n q r (sampledEdges n r ω)).filter fun Q ↦ e ⊆ Q) ⊆
        Erdos722.Reserve.extensionLevel n q r
          (sampledEdges n r ω) e (q - r) := by
    intro Q hQ
    have hQdata := Finset.mem_filter.mp hQ
    have hclique := mem_cliquesIn.mp hQdata.1
    apply Finset.mem_filter.mpr
    refine ⟨mem_uniformEdges.mpr (by
      simpa [Nat.add_sub_of_le hrq.le] using hclique.1),
      hQdata.2, ?_⟩
    intro g hg
    exact hclique.2 (Finset.mem_sdiff.mp hg).1
  exact (Finset.card_le_card hsub).trans
    (extensionLevel_final_typical_le hr hrq p ω
      (typicalUpperBranching n r p) htyp
      (fun i _hi ↦ le_typicalUpperBranching_cast n r p i) hecard)

/-- Incidence double counting converts a uniform lower degree at all
`(r-1)`-faces into a global lower bound for the host size. -/
theorem card_uniformEdges_mul_lower_le_card_mul_choose
    {n r L : ℕ} {K : Finset (Finset (Fin n))}
    (hK : ∀ e ∈ K, e.card = r)
    (hlower : ∀ f ∈ uniformEdges n (r - 1),
      L ≤ (rootEdges K f).card) :
    (uniformEdges n (r - 1)).card * L ≤
      K.card * Nat.choose r (r - 1) := by
  apply Erdos722.Reserve.card_mul_le_card_mul_of_relation
    (uniformEdges n (r - 1)) K (fun f e ↦ f ⊆ e) L
      (Nat.choose r (r - 1)) hlower
  intro e he
  have hecard := hK e he
  have heq :
      ((uniformEdges n (r - 1)).filter fun f ↦ f ⊆ e) =
        e.powersetCard (r - 1) := by
    ext f
    simp [uniformEdges, Finset.mem_powersetCard, and_comm]
  rw [heq, Finset.card_powersetCard, hecard]

/-- Singleton-root lower typicality gives a uniform natural lower bound on
the sampled degree of every `(r-1)`-face. -/
theorem typical_rootEdges_lower
    {n q r L : ℕ} (hr : 0 < r) (hrq : r ≤ q)
    (p : Set.Icc (0 : ℝ) 1)
    (ω : {a // a ∈ uniformEdges n r} → Bool)
    (htyp : ∀ roots, ∀ hroots :
      roots ∈ rootFamilies n r (Nat.choose q r),
      commonMean n roots p / 2 <
        Erdos722.Probability.finiteRandomSum
          (fun x ↦ commonNeighborIndicator n r roots hr
            (root_card_of_mem_rootFamilies hroots) x) ω ∧
      Erdos722.Probability.finiteRandomSum
          (fun x ↦ commonNeighborIndicator n r roots hr
            (root_card_of_mem_rootFamilies hroots) x) ω <
        2 * commonMean n roots p)
    (hL : (L : ℝ) ≤ ((n - (r - 1) : ℕ) : ℝ) * (p : ℝ) / 2) :
    ∀ f ∈ uniformEdges n (r - 1),
      L ≤ (rootEdges (sampledEdges n r ω) f).card := by
  intro f hf
  have hfcard := mem_uniformEdges.mp hf
  have hroots : ({f} : Finset (Finset (Fin n))) ∈
      rootFamilies n r (Nat.choose q r) := by
    rw [mem_rootFamilies]
    constructor
    · intro g hg
      have hgf : g = f := Finset.mem_singleton.mp hg
      simpa [hgf] using hf
    have hchoose : 0 < Nat.choose q r := Nat.choose_pos hrq
    exact (Nat.one_le_iff_ne_zero).mpr (Nat.ne_of_gt hchoose)
  have hlower := (htyp {f} hroots).1
  have hclean : (cleanVertices n ({f} : Finset (Finset (Fin n)))).card =
      n - (r - 1) := by
    rw [Erdos722.Reserve.cleanVertices_eq_sdiff_biUnion]
    have hbi : ({f} : Finset (Finset (Fin n))).biUnion id = f := by
      ext x
      simp
    rw [hbi]
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ f),
      Finset.card_univ, Fintype.card_fin, hfcard]
  have hmean : commonMean n {f} p =
      ((n - (r - 1) : ℕ) : ℝ) * (p : ℝ) := by
    simp [commonMean, hclean]
  rw [hmean] at hlower
  rw [← card_commonNeighbors n r {f} hr
    (root_card_of_mem_rootFamilies hroots) ω] at hlower
  have hdegree := Erdos722.Reserve.localDegree_sampledEdges_eq_commonNeighbors
    hr f hfcard ω
  have hrootEq : (rootEdges (sampledEdges n r ω) f).card =
      (commonNeighbors n r {f} hr
        (root_card_of_mem_rootFamilies hroots) ω).card := by
    simpa [rootEdges, Erdos722.Reserve.localDegree] using hdegree
  rw [hrootEq]
  exact_mod_cast hL.trans hlower.le

end

end Erdos722.IntegralGenerators
