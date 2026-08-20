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
import ErdosProblems.Erdos722.IntegralGenerators
import Mathlib

set_option relaxedAutoImplicit true

/-!
# Pruning saturated cliques in the integral absorber

After the modular greedy construction, Section 6 of the short proof deletes
every edge lying in too many saturated cliques.  This file proves the exact
finite incidence inequalities behind that deletion.  No asymptotic estimate
is hidden here: the density powers can be substituted later.
-/

namespace Erdos722.Prune

open Finset
open Erdos722.Typicality
open Erdos722.Generators
open Erdos722.IntegralGenerators

noncomputable section

/-- Number of cliques in `family` containing the `r`-edge `e`. -/
def cliqueLoad (r : ℕ) (family : Finset (Finset (Fin n)))
    (e : Finset (Fin n)) : ℕ :=
  (family.filter fun Q ↦ e ∈ Q.powersetCard r).card

/-- Edges whose saturated-clique load has reached a deletion threshold. -/
def heavyEdges (r threshold : ℕ) (K family : Finset (Finset (Fin n))) :
    Finset (Finset (Fin n)) :=
  K.filter fun e ↦ threshold ≤ cliqueLoad r family e

lemma heavyEdges_subset (r threshold : ℕ)
    (K family : Finset (Finset (Fin n))) :
    heavyEdges r threshold K family ⊆ K :=
  Finset.filter_subset _ _

/-- The sparse host after all heavy edges have been deleted. -/
def prunedEdges (r threshold : ℕ) (K family : Finset (Finset (Fin n))) :
    Finset (Finset (Fin n)) :=
  K \ heavyEdges r threshold K family

/-- Candidate cliques not declared saturated by the lower-face cap. -/
def unsaturatedCliques (n q r cap : ℕ)
    (K selected : Finset (Finset (Fin n))) :
    Finset (Finset (Fin n)) :=
  cliquesIn n q r K \ saturatedCliques n q r cap K selected

lemma mem_unsaturatedCliques {Q : Finset (Fin n)} :
    Q ∈ unsaturatedCliques n q r cap K selected ↔
      Q ∈ cliquesIn n q r K ∧
        Q ∉ saturatedCliques n q r cap K selected := by
  simp [unsaturatedCliques]

/-- Double-counting saturated-clique/edge incidences. -/
theorem threshold_mul_card_heavyEdges_le
    {n q r threshold : ℕ}
    {K family : Finset (Finset (Fin n))}
    (hfamily : family ⊆ cliquesIn n q r K) :
    threshold * (heavyEdges r threshold K family).card ≤
      family.card * Nat.choose q r := by
  have hcount := card_saturatedCounters_mul_le
    (fun e Q : Finset (Fin n) ↦ e ∈ Q.powersetCard r)
    K family threshold (Nat.choose q r) (by
      intro Q hQ
      have hclique := mem_cliquesIn.mp (hfamily hQ)
      have heq :
          (K.filter fun e ↦ e ∈ Q.powersetCard r) =
            Q.powersetCard r := by
        ext e
        constructor
        · intro he
          exact (Finset.mem_filter.mp he).2
        · intro he
          exact Finset.mem_filter.mpr ⟨hclique.2 he, he⟩
      rw [heq, Finset.card_powersetCard, hclique.1])
  simpa [heavyEdges, cliqueLoad, counterLoad] using hcount

lemma prunedEdges_subset
    (r threshold : ℕ) (K family : Finset (Finset (Fin n))) :
    prunedEdges r threshold K family ⊆ K := by
  exact Finset.sdiff_subset

/-- Every surviving edge has saturated-clique load strictly below the
deletion threshold. -/
theorem cliqueLoad_lt_of_mem_prunedEdges
    {e : Finset (Fin n)}
    (he : e ∈ prunedEdges r threshold K family) :
    cliqueLoad r family e < threshold := by
  have hm := Finset.mem_sdiff.mp he
  have hnot : ¬ threshold ≤ cliqueLoad r family e := by
    intro hload
    exact hm.2 (Finset.mem_filter.mpr ⟨hm.1, hload⟩)
  omega

/-- A non-saturated candidate is generated modulo `N`: this is the direct
logical use of the greedy span-or-saturated alternative. -/
theorem inRestrictedModularSpan_of_mem_unsaturated
    {N n q r cap : ℕ} {K selected : Finset (Finset (Fin n))}
    (hresolve : ∀ Q ∈ cliquesIn n q r K,
      InRestrictedModularSpan N r K selected
          (modCliqueBoundaryOn N r K Q) ∨
        ∃ f : Finset (Fin n), f.card = r - 1 ∧ f ⊆ Q ∧
          cap ≤ counterLoad (fun f Q ↦ f ⊆ Q) selected f)
    {Q : Finset (Fin n)}
    (hQ : Q ∈ unsaturatedCliques n q r cap K selected) :
    InRestrictedModularSpan N r K selected
      (modCliqueBoundaryOn N r K Q) := by
  have hm := mem_unsaturatedCliques.mp hQ
  rcases hresolve Q hm.1 with hspan | hsat
  · exact hspan
  · obtain ⟨f, hfcard, hfQ, hload⟩ := hsat
    exfalso
    apply hm.2
    apply mem_saturatedCliques.mpr
    refine ⟨hm.1, f, mem_uniformEdges.mpr hfcard, hfQ, hload⟩

/-! ## From the restricted span to the ambient span -/

/-- Extend a vector indexed by the edges of `K` by zero outside `K`. -/
def extendByZero (K : Finset (Finset (Fin n)))
    (x : ↑K → ZMod N) : Finset (Fin n) → ZMod N :=
  fun e ↦ if he : e ∈ K then x ⟨e, he⟩ else 0

lemma extendByZero_zero (K : Finset (Finset (Fin n))) :
    extendByZero (N := N) K 0 = 0 := by
  funext e
  simp [extendByZero]

lemma extendByZero_add (K : Finset (Finset (Fin n)))
    (x y : ↑K → ZMod N) :
    extendByZero K (x + y) = extendByZero K x + extendByZero K y := by
  funext e
  by_cases he : e ∈ K <;> simp [extendByZero, he]

lemma extendByZero_neg (K : Finset (Finset (Fin n)))
    (x : ↑K → ZMod N) :
    extendByZero K (-x) = -extendByZero K x := by
  funext e
  by_cases he : e ∈ K <;> simp [extendByZero, he]

/-- A clique all of whose `r`-edges lie in `K` has the same boundary after
restricting to `K` and extending by zero. -/
lemma extendByZero_modCliqueBoundaryOn
    {N n q r : ℕ} {K : Finset (Finset (Fin n))}
    {Q : Finset (Fin n)}
    (hQ : Q ∈ cliquesIn n q r K) :
    extendByZero K (modCliqueBoundaryOn N r K Q) =
      modCliqueBoundary N n r Q := by
  funext e
  by_cases her : e.card = r
  · by_cases heQ : e ⊆ Q
    · have heK : e ∈ K := (mem_cliquesIn.mp hQ).2
        (Finset.mem_powersetCard.mpr ⟨heQ, her⟩)
      simp [extendByZero, modCliqueBoundaryOn, modCliqueBoundary,
        heK, her, heQ]
    · simp [extendByZero, modCliqueBoundaryOn, modCliqueBoundary,
        her, heQ]
  · simp [extendByZero, modCliqueBoundaryOn, modCliqueBoundary, her]

/-- Restricted modular generation inside a host clique lifts to modular
generation of its full ambient boundary, because both the target and every
selected generator vanish off the host. -/
theorem inModularSpan_of_inRestrictedModularSpan
    {N n q r : ℕ} {K selected : Finset (Finset (Fin n))}
    (hselected : selected ⊆ cliquesIn n q r K)
    {Q : Finset (Fin n)} (hQ : Q ∈ cliquesIn n q r K)
    (hspan : InRestrictedModularSpan N r K selected
      (modCliqueBoundaryOn N r K Q)) :
    InModularSpan N n r selected (modCliqueBoundary N n r Q) := by
  classical
  let restrictedSet : Set (↑K → ZMod N) :=
    modCliqueBoundaryOn N r K '' (↑selected : Set (Finset (Fin n)))
  let fullSpan := AddSubgroup.closure
    (modCliqueBoundary N n r ''
      (↑selected : Set (Finset (Fin n))))
  have hlift : ∀ x,
      x ∈ AddSubgroup.closure restrictedSet →
      extendByZero K x ∈ fullSpan := by
    intro x hx
    induction hx using AddSubgroup.closure_induction with
    | mem x hx =>
        obtain ⟨B, hB, rfl⟩ := hx
        rw [extendByZero_modCliqueBoundaryOn (hselected hB)]
        exact AddSubgroup.subset_closure ⟨B, hB, rfl⟩
    | zero =>
        rw [extendByZero_zero]
        exact AddSubgroup.zero_mem _
    | add x y _hx _hy hx hy =>
        rw [extendByZero_add]
        exact AddSubgroup.add_mem _ hx hy
    | neg x _hx hx =>
        rw [extendByZero_neg]
        exact AddSubgroup.neg_mem _ hx
  change modCliqueBoundaryOn N r K Q ∈
      AddSubgroup.closure restrictedSet at hspan
  change modCliqueBoundary N n r Q ∈ fullSpan
  rw [← extendByZero_modCliqueBoundaryOn hQ]
  exact hlift _ hspan

/-- Every clique through an `r`-edge is either unsaturated or contributes
to that edge's saturated-clique load. -/
theorem card_cliques_through_edge_le_unsaturated_add_load
    {n q r cap : ℕ} {K selected : Finset (Finset (Fin n))}
    {e : Finset (Fin n)} (hecard : e.card = r) :
    ((cliquesIn n q r K).filter fun Q ↦ e ⊆ Q).card ≤
      ((unsaturatedCliques n q r cap K selected).filter
          fun Q ↦ e ⊆ Q).card +
        cliqueLoad r (saturatedCliques n q r cap K selected) e := by
  let all := (cliquesIn n q r K).filter fun Q ↦ e ⊆ Q
  let good := (unsaturatedCliques n q r cap K selected).filter
    fun Q ↦ e ⊆ Q
  let bad := (saturatedCliques n q r cap K selected).filter
    fun Q ↦ e ∈ Q.powersetCard r
  have hsub : all ⊆ good ∪ bad := by
    intro Q hQ
    have hall := Finset.mem_filter.mp hQ
    by_cases hsat : Q ∈ saturatedCliques n q r cap K selected
    · apply Finset.mem_union_right
      exact Finset.mem_filter.mpr
        ⟨hsat, Finset.mem_powersetCard.mpr ⟨hall.2, hecard⟩⟩
    · apply Finset.mem_union_left
      exact Finset.mem_filter.mpr
        ⟨mem_unsaturatedCliques.mpr ⟨hall.1, hsat⟩, hall.2⟩
  calc
    all.card ≤ (good ∪ bad).card := Finset.card_le_card hsub
    _ ≤ good.card + bad.card := Finset.card_union_le _ _
    _ = ((unsaturatedCliques n q r cap K selected).filter
          fun Q ↦ e ⊆ Q).card +
        cliqueLoad r (saturatedCliques n q r cap K selected) e := by
      rfl

/-- On a surviving edge, deleting all saturated cliques loses fewer than
`threshold` candidates. -/
theorem card_cliques_sub_threshold_le_unsaturated
    {n q r cap threshold : ℕ}
    {K selected : Finset (Finset (Fin n))}
    {e : Finset (Fin n)} (hecard : e.card = r)
    (he : e ∈ prunedEdges r threshold K
      (saturatedCliques n q r cap K selected)) :
    ((cliquesIn n q r K).filter fun Q ↦ e ⊆ Q).card - threshold ≤
      ((unsaturatedCliques n q r cap K selected).filter
        fun Q ↦ e ⊆ Q).card := by
  have hpartition := card_cliques_through_edge_le_unsaturated_add_load
    (n := n) (q := q) (cap := cap) (K := K) (selected := selected) hecard
  have hload := cliqueLoad_lt_of_mem_prunedEdges he
  omega

/-- Multiplicative form of the three consecutive double counts.  It avoids
all divisions and is therefore the convenient statement for power-cleared
asymptotic estimates in Lean. -/
theorem cap_mul_threshold_mul_heavy_le
    {cap threshold saturatedFaceCount selectedCount lowerFaceCount
      saturatedCliqueCount faceCliqueCap heavyCount cliqueEdgeCount : ℕ}
    (hfaces : cap * saturatedFaceCount ≤ selectedCount * lowerFaceCount)
    (hcliques : saturatedCliqueCount ≤
      saturatedFaceCount * faceCliqueCap)
    (hheavy : threshold * heavyCount ≤
      saturatedCliqueCount * cliqueEdgeCount) :
    cap * threshold * heavyCount ≤
      selectedCount * lowerFaceCount * faceCliqueCap * cliqueEdgeCount := by
  calc
    cap * threshold * heavyCount = cap * (threshold * heavyCount) := by ring
    _ ≤ cap * (saturatedCliqueCount * cliqueEdgeCount) :=
      Nat.mul_le_mul_left cap hheavy
    _ = (cap * saturatedCliqueCount) * cliqueEdgeCount := by ring
    _ ≤ (cap * (saturatedFaceCount * faceCliqueCap)) * cliqueEdgeCount :=
      Nat.mul_le_mul_right cliqueEdgeCount
        (Nat.mul_le_mul_left cap hcliques)
    _ = ((cap * saturatedFaceCount) * faceCliqueCap) * cliqueEdgeCount := by
      ring
    _ ≤ ((selectedCount * lowerFaceCount) * faceCliqueCap) *
          cliqueEdgeCount :=
      Nat.mul_le_mul_right cliqueEdgeCount
        (Nat.mul_le_mul_right faceCliqueCap hfaces)

/-- The first two double counts, also in division-free form. -/
theorem cap_mul_saturatedCliqueCount_le
    {cap saturatedFaceCount selectedCount lowerFaceCount
      saturatedCliqueCount faceCliqueCap : ℕ}
    (hfaces : cap * saturatedFaceCount ≤ selectedCount * lowerFaceCount)
    (hcliques : saturatedCliqueCount ≤
      saturatedFaceCount * faceCliqueCap) :
    cap * saturatedCliqueCount ≤
      selectedCount * lowerFaceCount * faceCliqueCap := by
  calc
    cap * saturatedCliqueCount ≤ cap *
        (saturatedFaceCount * faceCliqueCap) :=
      Nat.mul_le_mul_left cap hcliques
    _ = (cap * saturatedFaceCount) * faceCliqueCap := by ring
    _ ≤ (selectedCount * lowerFaceCount) * faceCliqueCap :=
      Nat.mul_le_mul_right faceCliqueCap hfaces

/-- Combined two-cap charging inequality.  This is the exact quantitative
loss bound used after deleting edges that lie in too many exceptional
cliques.  Keeping it division-free makes the later power comparison purely
natural-number arithmetic. -/
theorem faceCap_mul_edgeCap_mul_threshold_mul_heavy_le
    {faceCap edgeCap threshold N Kcard Mface Medge q r
      saturatedFaceCount saturatedEdgeCount saturatedCliqueCount
      heavyCount : ℕ}
    (hfaces : faceCap * saturatedFaceCount ≤
      (N * Kcard) * Nat.choose q (r - 1))
    (hedges : edgeCap * saturatedEdgeCount ≤
      (N * Kcard) * Nat.choose q r)
    (hcliques : saturatedCliqueCount ≤
      saturatedFaceCount * Mface + saturatedEdgeCount * Medge)
    (hheavy : threshold * heavyCount ≤
      saturatedCliqueCount * Nat.choose q r) :
    faceCap * edgeCap * threshold * heavyCount ≤
      (N * Kcard) *
        (Nat.choose q (r - 1) * edgeCap * Mface +
          Nat.choose q r * faceCap * Medge) * Nat.choose q r := by
  calc
    faceCap * edgeCap * threshold * heavyCount =
        faceCap * edgeCap * (threshold * heavyCount) := by ring
    _ ≤ faceCap * edgeCap *
        (saturatedCliqueCount * Nat.choose q r) :=
      Nat.mul_le_mul_left _ hheavy
    _ ≤ faceCap * edgeCap *
        ((saturatedFaceCount * Mface +
          saturatedEdgeCount * Medge) * Nat.choose q r) :=
      Nat.mul_le_mul_left _
        (Nat.mul_le_mul_right _ hcliques)
    _ = (edgeCap * (faceCap * saturatedFaceCount) * Mface +
          faceCap * (edgeCap * saturatedEdgeCount) * Medge) *
            Nat.choose q r := by ring
    _ ≤ (edgeCap * ((N * Kcard) * Nat.choose q (r - 1)) * Mface +
          faceCap * ((N * Kcard) * Nat.choose q r) * Medge) *
            Nat.choose q r := by
      apply Nat.mul_le_mul_right
      apply Nat.add_le_add
      · exact Nat.mul_le_mul_right Mface
          (Nat.mul_le_mul_left edgeCap hfaces)
      · exact Nat.mul_le_mul_right Medge
          (Nat.mul_le_mul_left faceCap hedges)
    _ = (N * Kcard) *
        (Nat.choose q (r - 1) * edgeCap * Mface +
          Nat.choose q r * faceCap * Medge) * Nat.choose q r := by ring

/-- Complete deterministic output of the greedy-and-prune stage.  The
parameters `cap`, `threshold`, and `M` are left symbolic, so the subsequent
asymptotic file only has to verify scalar inequalities. -/
theorem exists_pruned_modular_generators
    {N n q r cap threshold M : ℕ} (hN : 0 < N)
    (K : Finset (Finset (Fin n)))
    (huniform : ∀ e ∈ K, e.card = r)
    (hface : ∀ f ∈ uniformEdges n (r - 1),
      ((cliquesIn n q r K).filter fun Q ↦ f ⊆ Q).card ≤ M) :
    ∃ selected Kstar : Finset (Finset (Fin n)),
      selected ⊆ cliquesIn n q r K ∧
      selected.card ≤ N * K.card ∧
      Kstar ⊆ K ∧
      (∀ f : Finset (Fin n), f.card = r - 1 →
        counterLoad (fun f Q ↦ f ⊆ Q) selected f ≤ cap) ∧
      cap * (saturatedFaces n r cap selected).card ≤
        (N * K.card) * Nat.choose q (r - 1) ∧
      (saturatedCliques n q r cap K selected).card ≤
        (saturatedFaces n r cap selected).card * M ∧
      threshold *
          (heavyEdges r threshold K
            (saturatedCliques n q r cap K selected)).card ≤
        (saturatedCliques n q r cap K selected).card * Nat.choose q r ∧
      (∀ e ∈ Kstar,
        ((cliquesIn n q r K).filter fun Q ↦ e ⊆ Q).card - threshold ≤
          ((unsaturatedCliques n q r cap K selected).filter
            fun Q ↦ e ⊆ Q).card) ∧
      ∀ Q ∈ unsaturatedCliques n q r cap K selected,
        InRestrictedModularSpan N r K selected
          (modCliqueBoundaryOn N r K Q) := by
  obtain ⟨selected, hselected, hselectedCard, hload, hsatFaces,
      hresolve⟩ :=
    exists_generators_with_saturatedFace_bound hN K
  let sat := saturatedCliques n q r cap K selected
  let Kstar := prunedEdges r threshold K sat
  have hsatSub : sat ⊆ cliquesIn n q r K := by
    intro Q hQ
    exact (mem_saturatedCliques.mp hQ).1
  have hsatCard : sat.card ≤
      (saturatedFaces n r cap selected).card * M := by
    exact card_saturatedCliques_le hface
  have hheavy : threshold * (heavyEdges r threshold K sat).card ≤
      sat.card * Nat.choose q r :=
    threshold_mul_card_heavyEdges_le hsatSub
  refine ⟨selected, Kstar, hselected, hselectedCard,
    prunedEdges_subset r threshold K sat, hload, hsatFaces,
    ?_, ?_, ?_, ?_⟩
  · simpa [sat] using hsatCard
  · simpa [sat] using hheavy
  · intro e he
    have heKstar : e ∈ prunedEdges r threshold K
        (saturatedCliques n q r cap K selected) := by
      simpa [Kstar, sat] using he
    have hecard : e.card = r := by
      have heK : e ∈ K :=
        prunedEdges_subset r threshold K sat (by simpa [Kstar] using he)
      exact huniform e heK
    exact card_cliques_sub_threshold_le_unsaturated hecard heKstar
  · intro Q hQ
    exact inRestrictedModularSpan_of_mem_unsaturated hresolve hQ

/-! ## Independent face/edge caps -/

/-- Every clique through an edge is either good for both caps or is counted
by the two-cap exceptional load at that edge. -/
theorem card_cliques_through_edge_le_twoCapUnsaturated_add_load
    {n q r faceCap edgeCap : ℕ}
    {K selected : Finset (Finset (Fin n))}
    {e : Finset (Fin n)} (hecard : e.card = r) :
    ((cliquesIn n q r K).filter fun Q ↦ e ⊆ Q).card ≤
      ((twoCapUnsaturatedCliques n q r faceCap edgeCap K selected).filter
          fun Q ↦ e ⊆ Q).card +
        cliqueLoad r
          (twoCapSaturatedCliques n q r faceCap edgeCap K selected) e := by
  let all := (cliquesIn n q r K).filter fun Q ↦ e ⊆ Q
  let good :=
    (twoCapUnsaturatedCliques n q r faceCap edgeCap K selected).filter
      fun Q ↦ e ⊆ Q
  let bad :=
    (twoCapSaturatedCliques n q r faceCap edgeCap K selected).filter
      fun Q ↦ e ∈ Q.powersetCard r
  have hsub : all ⊆ good ∪ bad := by
    intro Q hQ
    have hall := Finset.mem_filter.mp hQ
    by_cases hsat :
        Q ∈ twoCapSaturatedCliques n q r faceCap edgeCap K selected
    · apply Finset.mem_union_right
      exact Finset.mem_filter.mpr
        ⟨hsat, Finset.mem_powersetCard.mpr ⟨hall.2, hecard⟩⟩
    · apply Finset.mem_union_left
      exact Finset.mem_filter.mpr
        ⟨mem_twoCapUnsaturatedCliques.mpr ⟨hall.1, hsat⟩, hall.2⟩
  calc
    all.card ≤ (good ∪ bad).card := Finset.card_le_card hsub
    _ ≤ good.card + bad.card := Finset.card_union_le _ _
    _ = ((twoCapUnsaturatedCliques n q r faceCap edgeCap K selected).filter
          fun Q ↦ e ⊆ Q).card +
        cliqueLoad r
          (twoCapSaturatedCliques n q r faceCap edgeCap K selected) e := by
      rfl

/-- On an edge surviving the two-cap pruning, fewer than `threshold`
exceptional cliques were removed. -/
theorem card_cliques_sub_threshold_le_twoCapUnsaturated
    {n q r faceCap edgeCap threshold : ℕ}
    {K selected : Finset (Finset (Fin n))}
    {e : Finset (Fin n)} (hecard : e.card = r)
    (he : e ∈ prunedEdges r threshold K
      (twoCapSaturatedCliques n q r faceCap edgeCap K selected)) :
    ((cliquesIn n q r K).filter fun Q ↦ e ⊆ Q).card - threshold ≤
      ((twoCapUnsaturatedCliques n q r faceCap edgeCap K selected).filter
        fun Q ↦ e ⊆ Q).card := by
  have hpartition :=
    card_cliques_through_edge_le_twoCapUnsaturated_add_load
      (n := n) (q := q) (faceCap := faceCap) (edgeCap := edgeCap)
      (K := K) (selected := selected) hecard
  have hload := cliqueLoad_lt_of_mem_prunedEdges he
  omega

/-- Complete finite greedy-and-prune output with independent caps on
lower-face load and edge multiplicity. -/
theorem exists_twoCap_pruned_modular_generators
    {N n q r faceCap edgeCap threshold Mface Medge : ℕ}
    (hN : 0 < N) (K : Finset (Finset (Fin n)))
    (huniform : ∀ e ∈ K, e.card = r)
    (hface : ∀ f ∈ uniformEdges n (r - 1),
      ((cliquesIn n q r K).filter fun Q ↦ f ⊆ Q).card ≤ Mface)
    (hedge : ∀ e ∈ uniformEdges n r,
      ((cliquesIn n q r K).filter fun Q ↦ e ⊆ Q).card ≤ Medge) :
    ∃ selected Kstar : Finset (Finset (Fin n)),
      selected ⊆ cliquesIn n q r K ∧
      selected.card ≤ N * K.card ∧
      Kstar ⊆ K ∧
      Kstar = prunedEdges r threshold K
        (twoCapSaturatedCliques
          n q r faceCap edgeCap K selected) ∧
      (∀ f : Finset (Fin n), f.card = r - 1 →
        counterLoad (fun f Q ↦ f ⊆ Q) selected f ≤ faceCap) ∧
      (∀ e : Finset (Fin n), e.card = r →
        counterLoad (fun e Q ↦ e ⊆ Q) selected e ≤ edgeCap) ∧
      faceCap * (saturatedFaces n r faceCap selected).card ≤
        (N * K.card) * Nat.choose q (r - 1) ∧
      edgeCap * (saturatedEdges n r edgeCap selected).card ≤
        (N * K.card) * Nat.choose q r ∧
      (twoCapSaturatedCliques
          n q r faceCap edgeCap K selected).card ≤
        (saturatedFaces n r faceCap selected).card * Mface +
          (saturatedEdges n r edgeCap selected).card * Medge ∧
      threshold *
          (heavyEdges r threshold K
            (twoCapSaturatedCliques
              n q r faceCap edgeCap K selected)).card ≤
        (twoCapSaturatedCliques
          n q r faceCap edgeCap K selected).card * Nat.choose q r ∧
      (∀ e ∈ Kstar,
        ((cliquesIn n q r K).filter fun Q ↦ e ⊆ Q).card - threshold ≤
          ((twoCapUnsaturatedCliques
            n q r faceCap edgeCap K selected).filter
              fun Q ↦ e ⊆ Q).card) ∧
      ∀ Q ∈ twoCapUnsaturatedCliques
          n q r faceCap edgeCap K selected,
        InRestrictedModularSpan N r K selected
          (modCliqueBoundaryOn N r K Q) := by
  obtain ⟨selected, hselected, hselectedCard, hfaceLoad, hedgeLoad,
      hsatFaces, hsatEdges, hresolve⟩ := exists_twoCap_generators hN K
  let sat := twoCapSaturatedCliques
    n q r faceCap edgeCap K selected
  let Kstar := prunedEdges r threshold K sat
  have hsatSub : sat ⊆ cliquesIn n q r K := by
    intro Q hQ
    exact (mem_twoCapSaturatedCliques.mp hQ).1
  have hsatCard : sat.card ≤
      (saturatedFaces n r faceCap selected).card * Mface +
        (saturatedEdges n r edgeCap selected).card * Medge := by
    simpa [sat] using card_twoCapSaturatedCliques_le hface hedge
  have hheavy : threshold * (heavyEdges r threshold K sat).card ≤
      sat.card * Nat.choose q r :=
    threshold_mul_card_heavyEdges_le hsatSub
  refine ⟨selected, Kstar, hselected, hselectedCard,
    prunedEdges_subset r threshold K sat, ?_, hfaceLoad, hedgeLoad,
    hsatFaces, hsatEdges, hsatCard, hheavy, ?_, hresolve⟩
  · rfl
  intro e he
  have heKstar : e ∈ prunedEdges r threshold K
      (twoCapSaturatedCliques
        n q r faceCap edgeCap K selected) := by
    simpa [Kstar, sat] using he
  have hecard : e.card = r := by
    have heK : e ∈ K :=
      prunedEdges_subset r threshold K sat (by simpa [Kstar] using he)
    exact huniform e heK
  exact card_cliques_sub_threshold_le_twoCapUnsaturated hecard heKstar

end

end Erdos722.Prune
