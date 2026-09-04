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
import ErdosProblems.Erdos76.AlmostComplete
import ErdosProblems.Erdos76.AlmostCompleteCompactness
import ErdosProblems.Erdos76.InducedTransport
import ErdosProblems.Erdos76.LPDuality
import Mathlib.Combinatorics.SimpleGraph.Bipartite
import Mathlib.Combinatorics.SimpleGraph.CycleGraph
import Mathlib.Combinatorics.SimpleGraph.DeleteEdges
import Mathlib.Combinatorics.SimpleGraph.Matching
import Mathlib.Data.Finset.CastCard
import Mathlib.Tactic

/-!
# Structural ingredients in the Gruslys--Letzter theorem

This file introduces the graph notions used in the proof of the sharp
fractional theorem and proves the averaging calculation in Observation 2.5.

The averaging lemma is deliberately stated for a family of weights on one
fixed vertex type.  `IsDeletionPacking G u w` says exactly what the averaging
calculation uses from a packing of `G - u`: it is feasible in `G`, and every
edge incident with `u` has zero load.  Transporting a packing of the induced
graph on `{v // v != u}` to this representation is a separate, purely finite
renaming lemma.
-/

open Finset
open scoped BigOperators

namespace Erdos76

noncomputable section

attribute [local instance] Classical.propDecidable

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- Covered-edge weight of a red and a blue fractional triangle packing.
This is the paper's `pack(G)` objective evaluated at specified feasible
weights, rather than maximized over the two packing polytopes. -/
def twoColorCoveredSize (G : SimpleGraph α)
    (wR wB : Finset α → ℝ) : ℝ :=
  fractionalCoveredSize G wR + fractionalCoveredSize Gᶜ wB

/-- Existential form of the statement that a colouring has fractional
covered-edge weight at least `q`. -/
def HasFractionalCoveredSizeAtLeast (G : SimpleGraph α) (q : ℝ) : Prop :=
  ∃ wR wB : Finset α → ℝ,
    IsFractionalPacking G wR ∧ IsFractionalPacking Gᶜ wB ∧
      q ≤ twoColorCoveredSize G wR wB

/-- Universal upper-bound form of the paper's optimized `pack(G)` value. -/
def FractionalCoveredSizeAtMost (G : SimpleGraph α) (q : ℝ) : Prop :=
  ∀ wR wB : Finset α → ℝ,
    IsFractionalPacking G wR → IsFractionalPacking Gᶜ wB →
      twoColorCoveredSize G wR wB ≤ q

/-- Attainment of the two finite packing LPs gives the exact lower/upper
dichotomy used by the stability induction. -/
lemma fractionalCoveredSize_dichotomy (G : SimpleGraph α) (q : ℝ) :
    HasFractionalCoveredSizeAtLeast G q ∨ FractionalCoveredSizeAtMost G q := by
  obtain ⟨wR, wB, hwR, hwB, hmax⟩ :=
    LPDuality.exists_maximal_twoColor_fractionalCoveredSize G
  by_cases hq : q ≤ twoColorCoveredSize G wR wB
  · exact Or.inl ⟨wR, wB, hwR, hwB, hq⟩
  · right
    intro uR uB huR huB
    exact (hmax uR uB huR huB).trans (le_of_not_ge hq)

/-- Exact weighted-decomposition corollary of the compact weighted
reduction.  This is Corollary 2.12 in the form used in Proposition 4.2: a
strong packing with uncovered bound zero must realize every capacity
exactly. -/
theorem capacityDecomposition_of_weightedReduction
    {m : ℕ} (c : Sym2 α → ℝ)
    (hc : IsEdgeCapacity (⊤ : SimpleGraph α) c)
    (hmissing : capacityMissingWeight c ≤ (m : ℝ))
    (hgraphs : ∀ H : SimpleGraph α, missingEdgeCount H ≤ m →
      HasStrongFractionalPacking H 0) :
    ∃ w : Finset α → ℝ,
      IsCapacityDecomposition (⊤ : SimpleGraph α) c w := by
  obtain ⟨w, hw, huncovered, _hhalf⟩ :=
    weightedReduction c hc hmissing 0 hgraphs
  have hzero : capacityUncoveredWeight (⊤ : SimpleGraph α) c w = 0 :=
    le_antisymm huncovered (capacityUncoveredWeight_nonneg hw)
  refine ⟨w, hw, ?_⟩
  let E : Finset (Sym2 α) :=
    @SimpleGraph.edgeFinset α (⊤ : SimpleGraph α)
      (@SimpleGraph.fintypeEdgeSet α (⊤ : SimpleGraph α) Sym2.instFintype
        (fun a b ↦ Classical.propDecidable ((⊤ : SimpleGraph α).Adj a b)))
  have hterms : ∀ e ∈ E,
      0 ≤ c e - fractionalEdgeLoad (⊤ : SimpleGraph α) w e := by
    intro e he
    exact sub_nonneg.mpr (hw.2 e he)
  have hsum : ∑ e ∈ E,
      (c e - fractionalEdgeLoad (⊤ : SimpleGraph α) w e) = 0 := by
    simpa only [capacityUncoveredWeight, E] using hzero
  have hall := (Finset.sum_eq_zero_iff_of_nonneg hterms).mp hsum
  intro e he
  have heq := hall e he
  linarith

/-- Whether the two endpoints of an unordered pair lie on the same side of
a proposed bipartition. -/
def SameSide (s : Set α) : Sym2 α → Prop :=
  Sym2.lift ⟨fun u v ↦ (u ∈ s ↔ v ∈ s), fun _ _ ↦ propext iff_comm⟩

omit [Fintype α] [DecidableEq α] in
@[simp] lemma sameSide_mk (s : Set α) (u v : α) :
    SameSide s s(u, v) ↔ (u ∈ s ↔ v ∈ s) := Iff.rfl

@[simp] lemma sameSide_set_compl (s : Set α) (e : Sym2 α) :
    SameSide sᶜ e ↔ SameSide s e := by
  induction e using Sym2.inductionOn with
  | hf u v =>
      simp only [sameSide_mk, Set.mem_compl_iff]
      tauto

/-- Edges internal to the two sides `s` and `sᶜ`. -/
def internalEdgeFinset (G : SimpleGraph α) (s : Set α) : Finset (Sym2 α) :=
  G.edgeFinset.filter (SameSide s)

@[simp] lemma internalEdgeFinset_set_compl (G : SimpleGraph α) (s : Set α) :
    internalEdgeFinset G sᶜ = internalEdgeFinset G s := by
  ext e
  simp [internalEdgeFinset]

/-- Partition-witness form of being close to bipartite. -/
def PartitionCloseToBipartite (G : SimpleGraph α) (k : ℕ) : Prop :=
  ∃ s : Set α, (internalEdgeFinset G s).card ≤ k

/-- A graph can be made bipartite by deleting at most `k` of its edges. -/
def CloseToBipartite (G : SimpleGraph α) (k : ℕ) : Prop :=
  ∃ D : Finset (Sym2 α),
    D ⊆ G.edgeFinset ∧ D.card ≤ k ∧ (G.deleteEdges (D : Set (Sym2 α))).IsBipartite

omit [DecidableEq α] in
lemma CloseToBipartite.mono {G : SimpleGraph α} {k l : ℕ}
    (h : CloseToBipartite G k) (hkl : k ≤ l) : CloseToBipartite G l := by
  obtain ⟨D, hD, hcard, hbip⟩ := h
  exact ⟨D, hD, hcard.trans hkl, hbip⟩

lemma CloseToBipartite.partition_witness {G : SimpleGraph α} {k : ℕ}
    (h : CloseToBipartite G k) : PartitionCloseToBipartite G k := by
  obtain ⟨D, hDG, hDcard, hDbip⟩ := h
  obtain ⟨s, t, hst⟩ := hDbip.exists_isBipartiteWith
  refine ⟨s, (card_le_card ?_).trans hDcard⟩
  intro e heInternal
  rcases mem_filter.mp heInternal with ⟨heG, heSame⟩
  by_contra heD
  induction e using Sym2.inductionOn with
  | hf u v =>
      have hGuv : G.Adj u v := by
        simpa [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet] using heG
      have hdeleted :
          (G.deleteEdges (D : Set (Sym2 α))).Adj u v := by
        simp [hGuv, heD]
      rcases hst.mem_of_adj hdeleted with huv | huv
      · exact (Set.disjoint_left.mp hst.disjoint
          ((sameSide_mk s u v).mp heSame |>.mp huv.1)) huv.2
      · exact (Set.disjoint_left.mp hst.disjoint
          ((sameSide_mk s u v).mp heSame |>.mpr huv.2)) huv.1

/-- A labelling of the vertices by five nonempty blobs witnesses a pentagon
blow-up when edges between distinct blobs are red precisely for consecutive
labels on the five-cycle.  Edges within a blob are intentionally unrestricted. -/
def IsPentagonBlowup (G : SimpleGraph α) (blob : α → Fin 5) : Prop :=
  Function.Surjective blob ∧
    ∀ {u v : α}, blob u ≠ blob v →
      (G.Adj u v ↔ (SimpleGraph.cycleGraph 5).Adj (blob u) (blob v))

/-- Number of edge-colour flips separating two colourings. -/
def edgeFlipDistance (G H : SimpleGraph α) : ℕ :=
  (G.edgeFinset \ H.edgeFinset).card + (H.edgeFinset \ G.edgeFinset).card

/-- The second exceptional family in the order-17 finite classification. -/
def IsOneEdgeFlipFromPentagonBlowup (G : SimpleGraph α) : Prop :=
  ∃ H : SimpleGraph α, ∃ blob : α → Fin 5,
    IsPentagonBlowup H blob ∧ edgeFlipDistance G H = 1

/-- A convenient certified superset of the exceptional pentagon families in
Section 7.  The actual lists `B₁` and `B₂` refine this predicate; the only
order fact used by the no-chain deduction is that all listed graphs have at
most 25 vertices. -/
def IsPentagonExceptional (G : SimpleGraph α) : Prop :=
  Fintype.card α ≤ 25 ∧
    ((∃ blob : α → Fin 5, IsPentagonBlowup G blob) ∨
      IsOneEdgeFlipFromPentagonBlowup G)

/-- `G` is obtained from `H` by adjoining one final vertex, with all old
edge colours unchanged. -/
def IsInitialVertexExtension {n : ℕ}
    (H : SimpleGraph (Fin n)) (G : SimpleGraph (Fin (n + 1))) : Prop :=
  ∀ u v : Fin n, H.Adj u v ↔ G.Adj u.castSucc v.castSucc

/-- Exact interface of the Section 7 extension calculation. -/
def PentagonExtensionStep : Prop :=
  ∀ n : ℕ, 17 ≤ n → n < 26 →
    ∀ (H : SimpleGraph (Fin n)) (G : SimpleGraph (Fin (n + 1))),
      IsInitialVertexExtension H G → IsPentagonExceptional H →
      FractionalCoveredSizeAtMost G
        (((n + 1 : ℕ) : ℝ) * (n : ℝ) / 4) →
      IsPentagonExceptional G

/-- A weight on `G` obtained by extending a packing of `G - u` by zero has
these two properties.  The edge-load formulation is exactly what is needed
in Observation 2.5. -/
def IsDeletionPacking (G : SimpleGraph α) (u : α)
    (w : Finset α → ℝ) : Prop :=
  IsFractionalPacking G w ∧
    ∀ e ∈ G.edgeFinset, u ∈ e.toFinset → fractionalEdgeLoad G w e = 0

/-- The optimum of the colouring with `u` deleted is at most `q`, expressed
after extension by zero to the original vertex type. -/
def DeletionFractionalCoveredSizeAtMost (G : SimpleGraph α) (u : α) (q : ℝ) : Prop :=
  ∀ wR wB : Finset α → ℝ,
    IsDeletionPacking G u wR → IsDeletionPacking Gᶜ u wB →
      twoColorCoveredSize G wR wB ≤ q

/-- The normalized average of one extended deletion-packing per vertex. -/
def deletionAverageWeight (w : α → Finset α → ℝ)
    (t : Finset α) : ℝ :=
  (∑ u : α, w u t) / ((Fintype.card α : ℝ) - 2)

lemma fractionalEdgeLoad_deletionAverageWeight (G : SimpleGraph α)
    (w : α → Finset α → ℝ) (e : Sym2 α) :
    fractionalEdgeLoad G (deletionAverageWeight w) e =
      (∑ u : α, fractionalEdgeLoad G (w u) e) /
        ((Fintype.card α : ℝ) - 2) := by
  simp only [fractionalEdgeLoad, deletionAverageWeight, sum_div]
  rw [sum_comm]

lemma fractionalSize_deletionAverageWeight (G : SimpleGraph α)
    (w : α → Finset α → ℝ) :
    fractionalSize G (deletionAverageWeight w) =
      (∑ u : α, fractionalSize G (w u)) /
        ((Fintype.card α : ℝ) - 2) := by
  simp only [fractionalSize, deletionAverageWeight, sum_div]
  rw [sum_comm]

lemma sum_edge_avoidance_indicator (G : SimpleGraph α) {e : Sym2 α}
    (he : e ∈ G.edgeFinset) :
    (∑ u : α, if u ∈ e.toFinset then (0 : ℝ) else 1) =
      (Fintype.card α : ℝ) - 2 := by
  have hedge : e.toFinset.card = 2 :=
    SimpleGraph.card_toFinset_mem_edgeFinset ⟨e, he⟩
  calc
    (∑ u : α, if u ∈ e.toFinset then (0 : ℝ) else 1) =
        (∑ u ∈ (Finset.univ : Finset α), if u ∉ e.toFinset then (1 : ℝ) else 0) := by
          apply sum_congr rfl
          intro u hu
          by_cases hmem : u ∈ e.toFinset <;> simp [hmem]
    _ = ((Finset.univ.filter fun u ↦ u ∉ e.toFinset).card : ℝ) := by
          exact Finset.sum_boole (fun u ↦ u ∉ e.toFinset) Finset.univ
    _ = ((Finset.univ \ e.toFinset).card : ℝ) := by
          have hfilter :
              Finset.univ.filter (fun u ↦ u ∉ e.toFinset) =
                Finset.univ \ e.toFinset := by
            ext u
            simp
          rw [hfilter]
    _ = (Finset.univ.card : ℝ) - (e.toFinset.card : ℝ) := by
          rw [Finset.cast_card_sdiff]
          exact Finset.subset_univ _
    _ = (Fintype.card α : ℝ) - 2 := by simp [hedge]

/-- Feasibility half of Observation 2.5: averaging extended packings of all
one-vertex deletions, with normalization `|V|-2`, is feasible. -/
lemma isFractionalPacking_deletionAverageWeight (G : SimpleGraph α)
    (w : α → Finset α → ℝ) (hcard : 3 ≤ Fintype.card α)
    (hw : ∀ u, IsDeletionPacking G u (w u)) :
    IsFractionalPacking G (deletionAverageWeight w) := by
  have hdenom : 0 < (Fintype.card α : ℝ) - 2 := by
    have hc : (3 : ℝ) ≤ Fintype.card α := by exact_mod_cast hcard
    linarith
  constructor
  · intro t ht
    apply div_nonneg
    · exact sum_nonneg fun u _ ↦ (hw u).1.nonneg_on ht
    · exact hdenom.le
  · intro e he
    rw [fractionalEdgeLoad_deletionAverageWeight]
    rw [div_le_one hdenom]
    calc
      (∑ u : α, fractionalEdgeLoad G (w u) e) ≤
          ∑ u : α, if u ∈ e.toFinset then (0 : ℝ) else 1 := by
        apply sum_le_sum
        intro u hu
        by_cases hue : u ∈ e.toFinset
        · simp [hue, (hw u).2 e he hue]
        · simpa [hue] using (hw u).1.edgeLoad_le_one he
      _ = (Fintype.card α : ℝ) - 2 := sum_edge_avoidance_indicator G he

lemma fractionalCoveredSize_deletionAverageWeight (G : SimpleGraph α)
    (w : α → Finset α → ℝ) :
    fractionalCoveredSize G (deletionAverageWeight w) =
      (∑ u : α, fractionalCoveredSize G (w u)) /
        ((Fintype.card α : ℝ) - 2) := by
  rw [fractionalCoveredSize, fractionalSize_deletionAverageWeight]
  simp only [fractionalCoveredSize]
  rw [← mul_div_assoc, Finset.mul_sum]

lemma twoColorCoveredSize_deletionAverageWeight (G : SimpleGraph α)
    (wR wB : α → Finset α → ℝ) :
    twoColorCoveredSize G (deletionAverageWeight wR) (deletionAverageWeight wB) =
      (∑ u : α, twoColorCoveredSize G (wR u) (wB u)) /
        ((Fintype.card α : ℝ) - 2) := by
  rw [twoColorCoveredSize, fractionalCoveredSize_deletionAverageWeight,
    fractionalCoveredSize_deletionAverageWeight]
  simp only [twoColorCoveredSize, sum_add_distrib, add_div]

/-- Observation 2.5 in witness form.  The numbers `q u` may in particular be
the optimum covered sizes of the induced colourings with vertex `u` deleted.
The induced-subgraph transport and attainment of the finite LP optima are the
only ingredients not used in this averaging calculation. -/
theorem vertexDeletionAveraging
    (G : SimpleGraph α) (q : α → ℝ)
    (wR wB : α → Finset α → ℝ)
    (hcard : 3 ≤ Fintype.card α)
    (hwR : ∀ u, IsDeletionPacking G u (wR u))
    (hwB : ∀ u, IsDeletionPacking Gᶜ u (wB u))
    (hq : ∀ u, q u ≤ twoColorCoveredSize G (wR u) (wB u)) :
    HasFractionalCoveredSizeAtLeast G
      ((∑ u : α, q u) / ((Fintype.card α : ℝ) - 2)) := by
  have hdenom : 0 ≤ (Fintype.card α : ℝ) - 2 := by
    have hc : (3 : ℝ) ≤ Fintype.card α := by exact_mod_cast hcard
    linarith
  refine ⟨deletionAverageWeight wR, deletionAverageWeight wB,
    isFractionalPacking_deletionAverageWeight G wR hcard hwR,
    isFractionalPacking_deletionAverageWeight Gᶜ wB hcard hwB, ?_⟩
  rw [twoColorCoveredSize_deletionAverageWeight]
  exact div_le_div_of_nonneg_right (sum_le_sum fun u _ ↦ hq u) hdenom

/-- The inductive consequence of Observation 2.5.  If the whole colouring
has covered size at most `Q`, and `Q` is no larger than the normalized value
corresponding to the deletion threshold `q`, some vertex deletion has covered
size at most `q`.

For a colouring on `n+1` vertices, substituting
`Q = n*(n+1)/4` and `q = n*(n-1)/4` makes `hscale` an equality. -/
theorem exists_deletion_fractionalCoveredSizeAtMost
    (G : SimpleGraph α) (Q q : ℝ)
    (hcard : 3 ≤ Fintype.card α)
    (hG : FractionalCoveredSizeAtMost G Q)
    (hscale : Q ≤ (Fintype.card α : ℝ) * q /
      ((Fintype.card α : ℝ) - 2)) :
    ∃ u : α, DeletionFractionalCoveredSizeAtMost G u q := by
  have hdenom : 0 < (Fintype.card α : ℝ) - 2 := by
    have hc : (3 : ℝ) ≤ Fintype.card α := by exact_mod_cast hcard
    linarith
  obtain ⟨u0⟩ : Nonempty α := Fintype.card_pos_iff.mp (by omega)
  by_contra hnone
  have hall : ∀ u : α, ¬ DeletionFractionalCoveredSizeAtMost G u q := by
    simpa using hnone
  have hex : ∀ u : α, ∃ wR wB : Finset α → ℝ,
      IsDeletionPacking G u wR ∧ IsDeletionPacking Gᶜ u wB ∧
        q < twoColorCoveredSize G wR wB := by
    intro u
    simpa [DeletionFractionalCoveredSizeAtMost] using hall u
  choose wR wB hwR hwB hgt using hex
  have havg := vertexDeletionAveraging G
    (fun u ↦ twoColorCoveredSize G (wR u) (wB u)) wR wB hcard hwR hwB
    (fun _ ↦ le_rfl)
  obtain ⟨wRavg, wBavg, hwRavg, hwBavg, havgSize⟩ := havg
  have hsum :
      (∑ _u : α, q) <
        ∑ u : α, twoColorCoveredSize G (wR u) (wB u) := by
    exact Finset.sum_lt_sum_of_nonempty ⟨u0, Finset.mem_univ u0⟩
      (fun u _ ↦ hgt u)
  have hsum' :
      (Fintype.card α : ℝ) * q <
        ∑ u : α, twoColorCoveredSize G (wR u) (wB u) := by
    simpa using hsum
  have hquot :
      (Fintype.card α : ℝ) * q / ((Fintype.card α : ℝ) - 2) <
        (∑ u : α, twoColorCoveredSize G (wR u) (wB u)) /
          ((Fintype.card α : ℝ) - 2) :=
    (div_lt_div_iff_of_pos_right hdenom).2 hsum'
  have havgUpper := hG wRavg wBavg hwRavg hwBavg
  linarith

/-- Lemma 2.9's finite chain deduction from the Section 7 one-vertex
extension calculation.  The nine applications are written explicitly so
that every order and threshold is visible to the kernel. -/
theorem no_pentagon_chain_of_extension_step
    (hstep : PentagonExtensionStep) :
    ¬ ∃ G : ∀ n : ℕ, SimpleGraph (Fin n),
      IsPentagonExceptional (G 17) ∧
      (∀ n : ℕ, 17 ≤ n → n < 26 →
        IsInitialVertexExtension (G n) (G (n + 1))) ∧
      (∀ n : ℕ, 18 ≤ n → n ≤ 26 →
        FractionalCoveredSizeAtMost (G n)
          ((n : ℝ) * ((n : ℝ) - 1) / 4)) := by
  rintro ⟨G, h17, hext, hsmall⟩
  have h18 : IsPentagonExceptional (G 18) := by
    simpa using hstep 17 (by norm_num) (by norm_num) (G 17) (G 18)
      (hext 17 (by norm_num) (by norm_num)) h17
      (by convert hsmall 18 (by norm_num) (by norm_num) using 1 <;> norm_num)
  have h19 : IsPentagonExceptional (G 19) := by
    simpa using hstep 18 (by norm_num) (by norm_num) (G 18) (G 19)
      (hext 18 (by norm_num) (by norm_num)) h18
      (by convert hsmall 19 (by norm_num) (by norm_num) using 1 <;> norm_num)
  have h20 : IsPentagonExceptional (G 20) := by
    simpa using hstep 19 (by norm_num) (by norm_num) (G 19) (G 20)
      (hext 19 (by norm_num) (by norm_num)) h19
      (by convert hsmall 20 (by norm_num) (by norm_num) using 1 <;> norm_num)
  have h21 : IsPentagonExceptional (G 21) := by
    simpa using hstep 20 (by norm_num) (by norm_num) (G 20) (G 21)
      (hext 20 (by norm_num) (by norm_num)) h20
      (by convert hsmall 21 (by norm_num) (by norm_num) using 1 <;> norm_num)
  have h22 : IsPentagonExceptional (G 22) := by
    simpa using hstep 21 (by norm_num) (by norm_num) (G 21) (G 22)
      (hext 21 (by norm_num) (by norm_num)) h21
      (by convert hsmall 22 (by norm_num) (by norm_num) using 1 <;> norm_num)
  have h23 : IsPentagonExceptional (G 23) := by
    simpa using hstep 22 (by norm_num) (by norm_num) (G 22) (G 23)
      (hext 22 (by norm_num) (by norm_num)) h22
      (by convert hsmall 23 (by norm_num) (by norm_num) using 1 <;> norm_num)
  have h24 : IsPentagonExceptional (G 24) := by
    simpa using hstep 23 (by norm_num) (by norm_num) (G 23) (G 24)
      (hext 23 (by norm_num) (by norm_num)) h23
      (by convert hsmall 24 (by norm_num) (by norm_num) using 1 <;> norm_num)
  have h25 : IsPentagonExceptional (G 25) := by
    simpa using hstep 24 (by norm_num) (by norm_num) (G 24) (G 25)
      (hext 24 (by norm_num) (by norm_num)) h24
      (by convert hsmall 25 (by norm_num) (by norm_num) using 1 <;> norm_num)
  have h26 : IsPentagonExceptional (G 26) := by
    simpa using hstep 25 (by norm_num) (by norm_num) (G 25) (G 26)
      (hext 25 (by norm_num) (by norm_num)) h25
      (by convert hsmall 26 (by norm_num) (by norm_num) using 1 <;> norm_num)
  have : 26 ≤ 25 := by simpa [IsPentagonExceptional] using h26.1
  omega

/-! ## Exact structural obligations in the published proof -/

/-- The dichotomy proved in Theorem 2.6 of Gruslys--Letzter, in the exact
existential language used by this development.  Its proof is where the
certified finite classification through orders `17` and `22`, the exclusion
of pentagon chains through order `26`, and the almost-bipartite extension
lemma are required. -/
def FractionalStabilityDichotomy : Prop :=
  ∀ n : ℕ, 26 ≤ n → ∀ G : SimpleGraph (Fin n),
    HasFractionalCoveredSizeAtLeast G
        ((n : ℝ) * ((n : ℝ) - 1) / 4) ∨
      CloseToBipartite G (n / 8) ∨ CloseToBipartite Gᶜ (n / 8)

/-- Direct upper-bound formulation of Theorem 2.6. -/
def FractionalStabilityUpperBound : Prop :=
  ∀ n : ℕ, 26 ≤ n → ∀ G : SimpleGraph (Fin n),
    FractionalCoveredSizeAtMost G ((n : ℝ) * ((n : ℝ) - 1) / 4) →
      CloseToBipartite G (n / 8) ∨ CloseToBipartite Gᶜ (n / 8)

theorem fractionalStabilityDichotomy_of_upperBound
    (hstable : FractionalStabilityUpperBound) :
    FractionalStabilityDichotomy := by
  intro n hn G
  rcases fractionalCoveredSize_dichotomy G
      ((n : ℝ) * ((n : ℝ) - 1) / 4) with hlarge | hsmall
  · exact Or.inl hlarge
  · exact Or.inr (hstable n hn G hsmall)

/-- The Section 5 estimate in the almost-bipartite case.  In the paper this
is obtained by packing every internal edge of the close colour into a cross
triangle and applying `AlmostCompleteFractionalDecomposition` to the two
residual graphs inside the parts. -/
def AlmostBipartiteSharpBound : Prop :=
  ∀ n : ℕ, 26 ≤ n → ∀ G : SimpleGraph (Fin n),
    (CloseToBipartite G (n / 8) ∨ CloseToBipartite Gᶜ (n / 8)) →
      HasFractionalCoveredSizeAtLeast G ((((n - 1) ^ 2 / 4 : ℕ) : ℝ))

/-- The substantive packing statement supplied by Propositions 4.1 and 4.2
and the almost-complete decomposition theorem: relative to a partition with
few internal edges of one colour, the two colours together cover at least
the number of pairs internal to the two parts. -/
def AlmostBipartiteInternalPairBound : Prop :=
  ∀ n : ℕ, 26 ≤ n → ∀ (G : SimpleGraph (Fin n)) (s : Set (Fin n)),
    (internalEdgeFinset G s).card ≤ n / 8 →
      FractionalCoveredSizeAtMost G ((n : ℝ) * ((n : ℝ) - 1) / 4) →
      HasFractionalCoveredSizeAtLeast G
        (((s.ncard.choose 2 + sᶜ.ncard.choose 2 : ℕ) : ℝ))

/-- Output of the cross-triangle packing in Proposition 4.2: the internal
edges of `G` support blue triangle weight whose covered size is at least
three times their number. -/
def HasInternalEdgeCrossPacking (G : SimpleGraph α) (s : Set α) : Prop :=
  ∃ w : Finset α → ℝ, IsFractionalPacking G w ∧
    3 * (internalEdgeFinset G s).card ≤ fractionalCoveredSize G w

/-- Output of the two residual almost-complete decompositions: the opposite
colour covers all but the internal edges of `G` inside the two parts. -/
def HasResidualInternalDecompositions (G : SimpleGraph α) (s : Set α) : Prop :=
  ∃ w : Finset α → ℝ, IsFractionalPacking Gᶜ w ∧
    ((s.ncard.choose 2 + sᶜ.ncard.choose 2 : ℕ) : ℝ) -
        (internalEdgeFinset G s).card ≤ fractionalCoveredSize Gᶜ w

/-! ### Combining the two residual decompositions -/

/-- A triangle has exactly three graph edges.  This type-generic version of
the certificate checker's incidence lemma is needed for decompositions on
the two induced vertex subtypes. -/
lemma card_edgeFinset_filter_triangle_generic {G : SimpleGraph α}
    (t : Finset α) (ht : G.IsNClique 3 t) :
    ((G.edgeFinset).filter fun e ↦ e ∈ t.sym2).card = 3 := by
  classical
  rw [show (G.edgeFinset.filter fun e ↦ e ∈ t.sym2) =
      {e ∈ G.edgeFinset | e.toFinset ⊆ t} by
    ext e
    simp [Finset.mem_sym2_iff, subset_iff]]
  rw [G.card_filter_edgeFinset_toFinset_subset t]
  have htop : G.induce (↑t : Set α) = ⊤ := G.induce_eq_top.mpr ht.isClique
  calc
    #(G.induce (↑t : Set α)).edgeFinset =
        Nat.card (G.induce (↑t : Set α)).edgeSet := by
          rw [Nat.card_eq_fintype_card, SimpleGraph.card_edgeSet]
    _ = Nat.card (⊤ : SimpleGraph t).edgeSet :=
      congrArg (fun H : SimpleGraph t ↦ Nat.card H.edgeSet) htop
    _ = #((⊤ : SimpleGraph t).edgeFinset) := by
      rw [Nat.card_eq_fintype_card, SimpleGraph.card_edgeSet]
    _ = (Fintype.card t).choose 2 :=
      SimpleGraph.card_edgeFinset_top_eq_card_choose_two
    _ = 3 := by simp [ht.card_eq]

/-- Double-counting triangle--edge incidences on an arbitrary finite vertex
type. -/
lemma sum_fractionalEdgeLoad_eq_three_mul_fractionalSize_generic
    (G : SimpleGraph α) (w : Finset α → ℝ) :
    ∑ e ∈ G.edgeFinset, fractionalEdgeLoad G w e =
      3 * fractionalSize G w := by
  rw [fractionalSize]
  simp_rw [fractionalEdgeLoad, Finset.sum_filter]
  rw [Finset.sum_comm, mul_sum]
  apply Finset.sum_congr rfl
  intro t ht
  rw [show (∑ e ∈ G.edgeFinset, if e ∈ t.sym2 then w t else 0) =
      ∑ e ∈ (G.edgeFinset.filter fun e ↦ e ∈ t.sym2), w t by
    rw [Finset.sum_filter]]
  rw [Finset.sum_const, nsmul_eq_mul]
  rw [card_edgeFinset_filter_triangle_generic t
    (SimpleGraph.mem_cliqueFinset_iff.mp ht)]
  norm_num

/-- A fractional decomposition covers precisely as much edge weight as the
number of present edges. -/
lemma fractionalCoveredSize_eq_card_of_decomposition
    {G : SimpleGraph α} {w : Finset α → ℝ}
    (hw : IsFractionalDecomposition G w) :
    fractionalCoveredSize G w = G.edgeFinset.card := by
  calc
    fractionalCoveredSize G w =
        ∑ e ∈ G.edgeFinset, fractionalEdgeLoad G w e := by
      rw [fractionalCoveredSize,
        sum_fractionalEdgeLoad_eq_three_mul_fractionalSize_generic]
    _ = ∑ _e ∈ G.edgeFinset, (1 : ℝ) := by
      apply Finset.sum_congr rfl
      intro e he
      rw [hw.edgeLoad_eq_one he]
    _ = G.edgeFinset.card := by simp

/-- If one endpoint is outside an induced vertex set, its zero-extended
packing places no load on that pair. -/
lemma fractionalEdgeLoad_extendInducedWeight_eq_zero_of_not_mem
    (G : SimpleGraph α) (S : Finset α) (w : Finset S → ℝ)
    (a b : α) (ha : a ∉ S) :
    fractionalEdgeLoad G (extendInducedWeight S w) s(a, b) = 0 := by
  classical
  unfold fractionalEdgeLoad
  apply Finset.sum_eq_zero
  intro t ht
  simp only [Finset.mem_filter] at ht
  rw [extendInducedWeight, dif_neg]
  intro hsub
  exact ha (hsub (Finset.mk_mem_sym2_iff.mp ht.2).1)

/-- Sum two triangle weights pointwise. -/
def addTriangleWeight (w₁ w₂ : Finset α → ℝ) : Finset α → ℝ :=
  fun t ↦ w₁ t + w₂ t

lemma fractionalSize_addTriangleWeight (G : SimpleGraph α)
    (w₁ w₂ : Finset α → ℝ) :
    fractionalSize G (addTriangleWeight w₁ w₂) =
      fractionalSize G w₁ + fractionalSize G w₂ := by
  simp [fractionalSize, addTriangleWeight, sum_add_distrib]

/-- Zero-extend decompositions on disjoint induced vertex sets and add them.
No graph edge can receive positive load from both extensions. -/
lemma isFractionalPacking_add_extendInduced_of_disjoint
    (G : SimpleGraph α) (S T : Finset α) (hST : Disjoint S T)
    (wS : Finset S → ℝ) (wT : Finset T → ℝ)
    (hwS : IsFractionalPacking (G.induce (S : Set α)) wS)
    (hwT : IsFractionalPacking (G.induce (T : Set α)) wT) :
    IsFractionalPacking G
      (addTriangleWeight (extendInducedWeight S wS) (extendInducedWeight T wT)) := by
  have hS := hwS.extendInduced
  have hT := hwT.extendInduced
  constructor
  · intro t ht
    exact add_nonneg (hS.nonneg_on ht) (hT.nonneg_on ht)
  · intro e he
    induction e using Sym2.inductionOn with
    | hf a b =>
      change fractionalEdgeLoad G
        (fun t ↦ extendInducedWeight S wS t + extendInducedWeight T wT t)
          s(a, b) ≤ 1
      rw [fractionalEdgeLoad_add]
      by_cases haS : a ∈ S
      · by_cases hbS : b ∈ S
        · have haT : a ∉ T := fun haT ↦
            Finset.disjoint_left.mp hST haS haT
          rw [fractionalEdgeLoad_extendInducedWeight_eq_zero_of_not_mem
            G T wT a b haT, add_zero]
          exact hS.edgeLoad_le_one he
        · rw [show s(a, b) = s(b, a) from
              Sym2.sound (Sym2.Rel.swap a b),
            fractionalEdgeLoad_extendInducedWeight_eq_zero_of_not_mem
              G S wS b a hbS]
          norm_num
          have he' : s(b, a) ∈ G.edgeFinset := by
            rw [show s(b, a) = s(a, b) from
              Sym2.sound (Sym2.Rel.swap b a)]
            exact he
          exact hT.edgeLoad_le_one he'
      · rw [fractionalEdgeLoad_extendInducedWeight_eq_zero_of_not_mem
            G S wS a b haS, zero_add]
        exact hT.edgeLoad_le_one he

/-- The residual construction, before applying the almost-complete theorem:
decompositions on the two parts combine into an ambient feasible packing
whose covered size is the sum of their edge counts. -/
theorem residualPacking_of_sideDecompositions
    (G : SimpleGraph α) (S T : Finset α) (hST : Disjoint S T)
    (wS : Finset S → ℝ) (wT : Finset T → ℝ)
    (hwS : IsFractionalDecomposition (G.induce (S : Set α)) wS)
    (hwT : IsFractionalDecomposition (G.induce (T : Set α)) wT) :
    ∃ w : Finset α → ℝ, IsFractionalPacking G w ∧
      fractionalCoveredSize G w =
        Nat.card (G.induce (S : Set α)).edgeSet +
          Nat.card (G.induce (T : Set α)).edgeSet := by
  let w := addTriangleWeight (extendInducedWeight S wS)
    (extendInducedWeight T wT)
  refine ⟨w, isFractionalPacking_add_extendInduced_of_disjoint
    G S T hST wS wT hwS.isPacking hwT.isPacking, ?_⟩
  rw [fractionalCoveredSize, fractionalSize_addTriangleWeight,
    fractionalSize_extendInducedWeight, fractionalSize_extendInducedWeight]
  rw [mul_add]
  change fractionalCoveredSize (G.induce (S : Set α)) wS +
      fractionalCoveredSize (G.induce (T : Set α)) wT = _
  rw [fractionalCoveredSize_eq_card_of_decomposition hwS,
    fractionalCoveredSize_eq_card_of_decomposition hwT]
  rw [SimpleGraph.edgeFinset_card, SimpleGraph.edgeFinset_card,
    ← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card]

/-- Edges of `G` whose two endpoints lie in the specified finite side. -/
def sideEdgeFinset (G : SimpleGraph α) (S : Finset α) : Finset (Sym2 α) :=
  G.edgeFinset.filter fun e ↦ e.toFinset ⊆ S

lemma card_sideEdgeFinset (G : SimpleGraph α) (S : Finset α) :
    (sideEdgeFinset G S).card =
      (G.induce (S : Set α)).edgeFinset.card := by
  simpa [sideEdgeFinset] using G.card_filter_edgeFinset_toFinset_subset S

lemma sameSide_iff_subset_side_or_compl (s : Set α) (e : Sym2 α) :
    SameSide s e ↔
      e.toFinset ⊆ s.toFinset ∨ e.toFinset ⊆ sᶜ.toFinset := by
  induction e using Sym2.inductionOn with
  | hf u v =>
      by_cases hu : u ∈ s <;> by_cases hv : v ∈ s <;>
        simp [sameSide_mk, hu, hv, subset_iff]

lemma internalEdgeFinset_eq_union_sides (G : SimpleGraph α) (s : Set α) :
    internalEdgeFinset G s =
      sideEdgeFinset G s.toFinset ∪ sideEdgeFinset G sᶜ.toFinset := by
  ext e
  simp only [internalEdgeFinset, sideEdgeFinset, mem_filter, mem_union]
  rw [sameSide_iff_subset_side_or_compl]
  tauto

lemma sideEdgeFinset_disjoint_compl (G : SimpleGraph α) (s : Set α) :
    Disjoint (sideEdgeFinset G s.toFinset)
      (sideEdgeFinset G sᶜ.toFinset) := by
  rw [Finset.disjoint_left]
  intro e heS heT
  rcases mem_filter.mp heS with ⟨heG, hS⟩
  rcases mem_filter.mp heT with ⟨_, hT⟩
  induction e using Sym2.inductionOn with
  | hf u v =>
      have huPair : u ∈ s(u, v).toFinset := by simp
      have huS : u ∈ s := by simpa using hS huPair
      have huT : u ∉ s := by simpa using hT huPair
      exact huT huS

lemma card_internalEdgeFinset_eq_card_induced_sides
    (G : SimpleGraph α) (s : Set α) :
    (internalEdgeFinset G s).card =
      Nat.card (G.induce (s.toFinset : Set α)).edgeSet +
        Nat.card (G.induce (sᶜ.toFinset : Set α)).edgeSet := by
  rw [internalEdgeFinset_eq_union_sides,
    card_union_of_disjoint (sideEdgeFinset_disjoint_compl G s),
    card_sideEdgeFinset, card_sideEdgeFinset]
  rw [SimpleGraph.edgeFinset_card, SimpleGraph.edgeFinset_card,
    ← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card]

lemma internalEdgeFinset_disjoint_compl (G : SimpleGraph α) (s : Set α) :
    Disjoint (internalEdgeFinset G s) (internalEdgeFinset Gᶜ s) := by
  rw [Finset.disjoint_left]
  intro e heG heGc
  rcases mem_filter.mp heG with ⟨heG, _⟩
  rcases mem_filter.mp heGc with ⟨heGc, _⟩
  induction e using Sym2.inductionOn with
  | hf u v =>
      have huv : G.Adj u v := by
        simpa [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet] using heG
      have hnuv : u ≠ v ∧ ¬ G.Adj u v := by
        simpa [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet,
          SimpleGraph.compl_adj] using heGc
      exact hnuv.2 huv

lemma internalEdgeFinset_union_compl (G : SimpleGraph α) (s : Set α) :
    internalEdgeFinset G s ∪ internalEdgeFinset Gᶜ s =
      internalEdgeFinset (⊤ : SimpleGraph α) s := by
  ext e
  induction e using Sym2.inductionOn with
  | hf u v =>
      simp only [internalEdgeFinset, mem_union, mem_filter,
        SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet,
        SimpleGraph.compl_adj, sameSide_mk, SimpleGraph.top_adj]
      constructor
      · rintro (⟨huv, hs⟩ | ⟨⟨hne, _⟩, hs⟩)
        · exact ⟨huv.ne, hs⟩
        · exact ⟨hne, hs⟩
      · rintro ⟨hne, hs⟩
        by_cases huv : G.Adj u v
        · exact Or.inl ⟨huv, hs⟩
        · exact Or.inr ⟨⟨hne, huv⟩, hs⟩

lemma card_internalEdgeFinset_top (s : Set α) :
    (internalEdgeFinset (⊤ : SimpleGraph α) s).card =
      s.ncard.choose 2 + sᶜ.ncard.choose 2 := by
  rw [card_internalEdgeFinset_eq_card_induced_sides]
  have hS :
      Nat.card ((⊤ : SimpleGraph α).induce
        (s.toFinset : Set α)).edgeSet =
        s.ncard.choose 2 := by
    have htop : (⊤ : SimpleGraph α).induce (s.toFinset : Set α) = ⊤ :=
      SimpleGraph.induce_top _
    calc
      Nat.card ((⊤ : SimpleGraph α).induce
          (s.toFinset : Set α)).edgeSet =
          Nat.card (⊤ : SimpleGraph (s.toFinset : Set α)).edgeSet :=
        congrArg (fun H : SimpleGraph (s.toFinset : Set α) ↦
          Nat.card H.edgeSet) htop
      _ = ((⊤ : SimpleGraph (s.toFinset : Set α)).edgeFinset).card := by
        rw [Nat.card_eq_fintype_card, SimpleGraph.card_edgeSet]
      _ = (Fintype.card (s.toFinset : Set α)).choose 2 :=
        SimpleGraph.card_edgeFinset_top_eq_card_choose_two
      _ = s.ncard.choose 2 := by
        apply congrArg (fun n : ℕ ↦ n.choose 2)
        simpa using (Set.ncard_eq_toFinset_card' s).symm
  have hT :
      Nat.card ((⊤ : SimpleGraph α).induce
        (sᶜ.toFinset : Set α)).edgeSet =
        sᶜ.ncard.choose 2 := by
    have htop : (⊤ : SimpleGraph α).induce (sᶜ.toFinset : Set α) = ⊤ :=
      SimpleGraph.induce_top _
    calc
      Nat.card ((⊤ : SimpleGraph α).induce
          (sᶜ.toFinset : Set α)).edgeSet =
          Nat.card (⊤ : SimpleGraph (sᶜ.toFinset : Set α)).edgeSet :=
        congrArg (fun H : SimpleGraph (sᶜ.toFinset : Set α) ↦
          Nat.card H.edgeSet) htop
      _ = ((⊤ : SimpleGraph (sᶜ.toFinset : Set α)).edgeFinset).card := by
        rw [Nat.card_eq_fintype_card, SimpleGraph.card_edgeSet]
      _ = (Fintype.card (sᶜ.toFinset : Set α)).choose 2 :=
        SimpleGraph.card_edgeFinset_top_eq_card_choose_two
      _ = sᶜ.ncard.choose 2 := by
        apply congrArg (fun n : ℕ ↦ n.choose 2)
        calc
          Fintype.card (sᶜ.toFinset : Set α) =
              (sᶜ.toFinset).card := by
            symm
            simpa using Set.toFinset_card (sᶜ.toFinset : Set α)
          _ = sᶜ.ncard :=
            (Set.ncard_eq_toFinset_card' (sᶜ : Set α)).symm
  omega

/-- On the internal pairs of a bipartition, the two colours partition all
available pairs. -/
lemma card_internalEdgeFinset_compl (G : SimpleGraph α) (s : Set α) :
    (internalEdgeFinset Gᶜ s).card =
      s.ncard.choose 2 + sᶜ.ncard.choose 2 -
        (internalEdgeFinset G s).card := by
  have hsum :
      (internalEdgeFinset G s).card + (internalEdgeFinset Gᶜ s).card =
        s.ncard.choose 2 + sᶜ.ncard.choose 2 := by
    rw [← card_internalEdgeFinset_top s, ← internalEdgeFinset_union_compl G s,
      card_union_of_disjoint (internalEdgeFinset_disjoint_compl G s)]
  omega

/-- Exact Section 5 residual conclusion from decompositions of the two
induced graphs in the opposite colour. -/
theorem hasResidualInternalDecompositions_of_sideDecompositions
    (G : SimpleGraph α) (s : Set α)
    (wS : Finset s.toFinset → ℝ) (wT : Finset sᶜ.toFinset → ℝ)
    (hwS : IsFractionalDecomposition
      (Gᶜ.induce (s.toFinset : Set α)) wS)
    (hwT : IsFractionalDecomposition
      (Gᶜ.induce (sᶜ.toFinset : Set α)) wT) :
    HasResidualInternalDecompositions G s := by
  have hST : Disjoint s.toFinset sᶜ.toFinset := by
    rw [Finset.disjoint_left]
    intro x hxs hxc
    have hxs' : x ∈ s := by simpa using hxs
    have hxc' : x ∉ s := by simpa using hxc
    exact hxc' hxs'
  obtain ⟨w, hw, hsize⟩ := residualPacking_of_sideDecompositions
    Gᶜ s.toFinset sᶜ.toFinset hST wS wT hwS hwT
  refine ⟨w, hw, ?_⟩
  rw [hsize]
  have hk : (internalEdgeFinset G s).card ≤
      s.ncard.choose 2 + sᶜ.ncard.choose 2 := by
    rw [← card_internalEdgeFinset_top s]
    rw [← internalEdgeFinset_union_compl G s]
    exact card_le_card subset_union_left
  have hparts : (internalEdgeFinset Gᶜ s).card =
      Nat.card (Gᶜ.induce (s.toFinset : Set α)).edgeSet +
        Nat.card (Gᶜ.induce (sᶜ.toFinset : Set α)).edgeSet :=
    card_internalEdgeFinset_eq_card_induced_sides Gᶜ s
  have hcomp := card_internalEdgeFinset_compl G s
  calc
    ((s.ncard.choose 2 + sᶜ.ncard.choose 2 : ℕ) : ℝ) -
        (internalEdgeFinset G s).card =
        ((s.ncard.choose 2 + sᶜ.ncard.choose 2 -
          (internalEdgeFinset G s).card : ℕ) : ℝ) := by
            rw [Nat.cast_sub hk]
    _ = ((internalEdgeFinset Gᶜ s).card : ℝ) := by
          exact_mod_cast hcomp.symm
    _ = ((Nat.card (Gᶜ.induce (s.toFinset : Set α)).edgeSet +
        Nat.card (Gᶜ.induce (sᶜ.toFinset : Set α)).edgeSet : ℕ) : ℝ) := by
          exact_mod_cast hparts
    _ ≤ (Nat.card (Gᶜ.induce (s.toFinset : Set α)).edgeSet : ℝ) +
        Nat.card (Gᶜ.induce (sᶜ.toFinset : Set α)).edgeSet := by
          norm_num

private lemma IsFractionalDecomposition.relabelGL
    {G : SimpleGraph α} {w : Finset α → ℝ}
    (hw : IsFractionalDecomposition G w) { β : Type* }
    [Fintype β] [DecidableEq β] (e : α ≃ β) :
    IsFractionalDecomposition (G.map e.toEmbedding) (relabelWeight e w) := by
  refine ⟨hw.isPacking.relabel e, ?_⟩
  intro p hp
  have hp' : p ∈ (G.map e.toEmbedding).edgeSet := by
    simpa only [SimpleGraph.mem_edgeFinset] using hp
  rw [SimpleGraph.edgeSet_map e.toEmbedding G] at hp'
  obtain ⟨q, hq, rfl⟩ := hp'
  rw [fractionalEdgeLoad_relabel]
  apply hw.edgeLoad_eq_one
  simpa only [SimpleGraph.mem_edgeFinset] using hq

/-- A private generic-cardinality transport of the companion theorem.  The
public conclusion below deliberately retains `hAC` as an argument until the
companion module exports its unconditional theorem. -/
private lemma almostCompleteFractionalDecomposition_fintype
    (hAC : AlmostCompleteFractionalDecomposition)
    { β : Type* } [Fintype β] [DecidableEq β]
    (G : SimpleGraph β) (hcard : 7 ≤ Fintype.card β)
    (hmissing : missingEdgeCount G ≤ Fintype.card β - 4) :
    ∃ w : Finset β → ℝ, IsFractionalDecomposition G w := by
  let e : β ≃ Fin (Fintype.card β) := Fintype.equivFinOfCardEq rfl
  let H : SimpleGraph (Fin (Fintype.card β)) := G.map e.toEmbedding
  let : DecidableRel H.Adj := Classical.decRel _
  have hmissH : missingEdgeCount H ≤ Fintype.card β - 4 := by
    have hc : Hᶜ = Gᶜ.map e.toEmbedding := compl_map_equiv G e
    have hedge : Hᶜ.edgeFinset = (Gᶜ.map e.toEmbedding).edgeFinset := by
      ext p
      simp only [SimpleGraph.mem_edgeFinset]
      rw [hc]
    unfold missingEdgeCount at hmissing ⊢
    calc
      Hᶜ.edgeFinset.card = (Gᶜ.map e.toEmbedding).edgeFinset.card :=
        congrArg Finset.card hedge
      _ = Gᶜ.edgeFinset.card :=
        SimpleGraph.card_edgeFinset_map e.toEmbedding Gᶜ
      _ ≤ Fintype.card β - 4 := hmissing
  obtain ⟨w, hw⟩ := hAC (Fintype.card β) hcard H hmissH
  let u : Finset β → ℝ := relabelWeight e.symm w
  have hmap : H.map e.symm.toEmbedding = G := by
    dsimp only [H]
    rw [SimpleGraph.map_map]
    simpa using G.map_id
  refine ⟨u, ?_⟩
  simpa only [u, hmap] using hw.relabelGL e.symm

private lemma missingEdgeCount_compl_induce_GL
    (G : SimpleGraph α) (S : Finset α) :
    missingEdgeCount (Gᶜ.induce (S : Set α)) =
      (G.induce (S : Set α)).edgeFinset.card := by
  have hgraph : (Gᶜ.induce (S : Set α))ᶜ =
      G.induce (S : Set α) := by
    rw [compl_induce, compl_compl]
  unfold missingEdgeCount
  congr 1
  ext e
  simp only [SimpleGraph.mem_edgeFinset]
  rw [hgraph]

private lemma internal_missing_sum_GL (G : SimpleGraph α) (s : Set α) :
    missingEdgeCount (Gᶜ.induce (s.toFinset : Set α)) +
        missingEdgeCount (Gᶜ.induce (sᶜ.toFinset : Set α)) =
      (internalEdgeFinset G s).card := by
  rw [missingEdgeCount_compl_induce_GL, missingEdgeCount_compl_induce_GL]
  have hS : (G.induce (s.toFinset : Set α)).edgeFinset.card =
      Nat.card (G.induce (s.toFinset : Set α)).edgeSet := by
    rw [SimpleGraph.edgeFinset_card, ← Nat.card_eq_fintype_card]
  have hT : (G.induce (sᶜ.toFinset : Set α)).edgeFinset.card =
      Nat.card (G.induce (sᶜ.toFinset : Set α)).edgeSet := by
    rw [SimpleGraph.edgeFinset_card, ← Nat.card_eq_fintype_card]
  rw [hS, hT]
  exact (card_internalEdgeFinset_eq_card_induced_sides G s).symm

/-- The actual residual half of the almost-bipartite construction.  Once
Proposition 4.1 supplies the two part-size inequalities, the companion
almost-complete theorem decomposes the opposite colour on each side; zero
extension then combines those decompositions without using any cross edge. -/
theorem hasResidualInternalDecompositions_of_almostComplete
    (hAC : AlmostCompleteFractionalDecomposition)
    (G : SimpleGraph α) (s : Set α)
    (hsizeS : (internalEdgeFinset G s).card + 4 ≤ s.ncard)
    (hsizeT : (internalEdgeFinset G s).card + 4 ≤ sᶜ.ncard)
    (hsevenS : 7 ≤ s.ncard) (hsevenT : 7 ≤ sᶜ.ncard) :
    HasResidualInternalDecompositions G s := by
  let S := s.toFinset
  let T := sᶜ.toFinset
  let HS := Gᶜ.induce (S : Set α)
  let HT := Gᶜ.induce (T : Set α)
  have hsum := internal_missing_sum_GL G s
  have hmissS : missingEdgeCount HS ≤ (internalEdgeFinset G s).card := by
    dsimp only [HS, S]
    omega
  have hmissT : missingEdgeCount HT ≤ (internalEdgeFinset G s).card := by
    dsimp only [HT, T]
    omega
  have hcardS : Fintype.card S = s.ncard := by
    rw [Fintype.card_coe]
    exact (Set.ncard_eq_toFinset_card' s).symm
  have hcardT : Fintype.card T = sᶜ.ncard := by
    rw [Fintype.card_coe]
    exact (Set.ncard_eq_toFinset_card' (sᶜ : Set α)).symm
  have hboundS : missingEdgeCount HS ≤ Fintype.card S - 4 := by
    rw [hcardS]
    omega
  have hboundT : missingEdgeCount HT ≤ Fintype.card T - 4 := by
    rw [hcardT]
    omega
  have hsevenS' : 7 ≤ Fintype.card S := by rwa [hcardS]
  have hsevenT' : 7 ≤ Fintype.card T := by rwa [hcardT]
  obtain ⟨wS, hwS⟩ := almostCompleteFractionalDecomposition_fintype
    hAC HS hsevenS' hboundS
  obtain ⟨wT, hwT⟩ := almostCompleteFractionalDecomposition_fintype
    hAC HT hsevenT' hboundT
  exact hasResidualInternalDecompositions_of_sideDecompositions
    G s wS wT (by simpa [HS, S] using hwS) (by simpa [HT, T] using hwT)

/-- The exact remaining combinatorial assertion in the almost-bipartite
branch, split into the cross packing and the residual decompositions used in
the paper. -/
def AlmostBipartiteCrossAndResidual : Prop :=
  ∀ n : ℕ, 26 ≤ n → ∀ (G : SimpleGraph (Fin n)) (s : Set (Fin n)),
    (internalEdgeFinset G s).card ≤ n / 8 →
      FractionalCoveredSizeAtMost G ((n : ℝ) * ((n : ℝ) - 1) / 4) →
      HasInternalEdgeCrossPacking G s ∧ HasResidualInternalDecompositions G s

/-- Proposition 4.1 in the exact form consumed by the Section 5 proof. -/
def AlmostBipartitePartSizeBounds : Prop :=
  ∀ n : ℕ, 19 ≤ n → ∀ (G : SimpleGraph (Fin n)) (s : Set (Fin n)),
    let k := (internalEdgeFinset G s).card
    k ≤ n / 8 →
      FractionalCoveredSizeAtMost G ((n : ℝ) * ((n : ℝ) - 1) / 4) →
        k + 4 ≤ s.ncard ∧ k + 4 ≤ sᶜ.ncard ∧
          7 ≤ s.ncard ∧ 7 ≤ sᶜ.ncard

/-- Proposition 4.2 under the optimized upper-bound hypothesis in force in
Section 5.  Unlike the earlier unconditional interface, this statement has
the hypothesis needed to rule out colourings with no cross triangle. -/
def AlmostBipartiteCrossPacking : Prop :=
  ∀ n : ℕ, 22 ≤ n → ∀ (G : SimpleGraph (Fin n)) (s : Set (Fin n)),
    (internalEdgeFinset G s).card ≤ n / 8 →
      FractionalCoveredSizeAtMost G ((n : ℝ) * ((n : ℝ) - 1) / 4) →
        HasInternalEdgeCrossPacking G s

/-- Proposition 4.1, Proposition 4.2, and the companion almost-complete
theorem together discharge the full close-colour construction. -/
theorem almostBipartiteCrossAndResidual_of_components
    (hAC : AlmostCompleteFractionalDecomposition)
    (hparts : AlmostBipartitePartSizeBounds)
    (hcross : AlmostBipartiteCrossPacking) :
    AlmostBipartiteCrossAndResidual := by
  intro n hn G s hk hupper
  obtain ⟨hsizeS, hsizeT, hsevenS, hsevenT⟩ :=
    hparts n (by omega) G s hk hupper
  exact ⟨hcross n (by omega) G s hk hupper,
    hasResidualInternalDecompositions_of_almostComplete
      hAC G s hsizeS hsizeT hsevenS hsevenT⟩

/-- Unit weights attached to an integral triangle packing. -/
def integralPackingWeight (P : Finset (Finset α)) (t : Finset α) : ℝ :=
  if t ∈ P then 1 else 0

lemma fractionalSize_integralPackingWeight {G : SimpleGraph α}
    {P : Finset (Finset α)} (hP : ∀ t ∈ P, G.IsNClique 3 t) :
    fractionalSize G (integralPackingWeight P) = P.card := by
  unfold fractionalSize integralPackingWeight
  rw [← sum_subset (s₁ := P) (s₂ := G.cliqueFinset 3)]
  · simp
  · intro t ht
    exact SimpleGraph.mem_cliqueFinset_iff.mpr (hP t ht)
  · intro t htG htP
    simp [htP]

lemma isFractionalPacking_integralPackingWeight {G : SimpleGraph α}
    {P : Finset (Finset α)}
    (hed : EdgeDisjoint P) :
    IsFractionalPacking G (integralPackingWeight P) := by
  constructor
  · intro t ht
    unfold integralPackingWeight
    split <;> norm_num
  · intro e he
    let S := (G.cliqueFinset 3).filter fun t ↦ e ∈ t.sym2 ∧ t ∈ P
    have hScard : S.card ≤ 1 := by
      rw [card_le_one]
      intro s hs t ht
      rcases mem_filter.mp hs with ⟨hsG, hse, hsP⟩
      rcases mem_filter.mp ht with ⟨htG, hte, htP⟩
      by_contra hst
      have hinter : 2 ≤ (s ∩ t).card := by
        have hesub : e.toFinset ⊆ s ∩ t := by
          intro u hu
          have hue : u ∈ e := by simpa using hu
          exact mem_inter.mpr ⟨(mem_sym2_iff.mp hse) u hue,
            (mem_sym2_iff.mp hte) u hue⟩
        have hecard : e.toFinset.card = 2 :=
          SimpleGraph.card_toFinset_mem_edgeFinset ⟨e, he⟩
        simpa [hecard] using card_le_card hesub
      have hle := hed hsP htP hst
      omega
    unfold fractionalEdgeLoad integralPackingWeight
    have hS :
        ((G.cliqueFinset 3).filter fun t ↦ e ∈ t.sym2).filter (fun t ↦ t ∈ P) = S := by
      ext t
      simp [S, and_comm, and_left_comm, and_assoc]
    calc
      (∑ t ∈ (G.cliqueFinset 3).filter (fun t ↦ e ∈ t.sym2),
          if t ∈ P then 1 else 0) = (S.card : ℝ) := by
            rw [Finset.sum_boole, hS]
      _ ≤ 1 := by exact_mod_cast hScard

/-! ### The maximal cross-triangle family in Proposition 4.2 -/

/-- The triangles of `G` having exactly one edge internal to the two parts.
The other two edges necessarily cross the partition, so these are precisely
the cross triangles considered at the start of Proposition 4.2. -/
def internalCrossTriangles (G : SimpleGraph α) (s : Set α) :
    Finset (Finset α) :=
  (G.cliqueFinset 3).filter fun t ↦
    ((internalEdgeFinset G s).filter fun e ↦ e ∈ t.sym2).card = 1

/-- An edge-disjoint family of cross triangles relative to `s`. -/
def IsInternalCrossPacking (G : SimpleGraph α) (s : Set α)
    (P : Finset (Finset α)) : Prop :=
  P ⊆ internalCrossTriangles G s ∧ EdgeDisjoint P

/-- All integral cross-triangle packings.  This is finite, and hence it has a
maximum-cardinality member without any choice or compactness assumption. -/
def internalCrossPackings (G : SimpleGraph α) (s : Set α) :
    Finset (Finset (Finset α)) :=
  (internalCrossTriangles G s).powerset.filter
    (IsInternalCrossPacking G s)

@[simp] lemma mem_internalCrossTriangles {G : SimpleGraph α} {s : Set α}
    {t : Finset α} :
    t ∈ internalCrossTriangles G s ↔
      G.IsNClique 3 t ∧
        ((internalEdgeFinset G s).filter fun e ↦ e ∈ t.sym2).card = 1 := by
  simp [internalCrossTriangles]

@[simp] lemma internalCrossTriangles_set_compl
    (G : SimpleGraph α) (s : Set α) :
    internalCrossTriangles G sᶜ = internalCrossTriangles G s := by
  ext t
  simp [internalCrossTriangles]

lemma isInternalCrossPacking_set_compl_iff
    (G : SimpleGraph α) (s : Set α) (P : Finset (Finset α)) :
    IsInternalCrossPacking G sᶜ P ↔ IsInternalCrossPacking G s P := by
  simp [IsInternalCrossPacking]

@[simp] lemma mem_internalCrossPackings {G : SimpleGraph α} {s : Set α}
    {P : Finset (Finset α)} :
    P ∈ internalCrossPackings G s ↔ IsInternalCrossPacking G s P := by
  simp [internalCrossPackings, IsInternalCrossPacking]

lemma empty_isInternalCrossPacking (G : SimpleGraph α) (s : Set α) :
    IsInternalCrossPacking G s ∅ := by
  simp [IsInternalCrossPacking, EdgeDisjoint]

/-- Two integral cross packings whose triangles meet pairwise in at most one
vertex may be united.  The same hypothesis also guarantees that the two
triangle families are disjoint, so cardinalities add. -/
lemma IsInternalCrossPacking.union_of_cross_inter_card_le_one
    {G : SimpleGraph α} {s : Set α} {P Q : Finset (Finset α)}
    (hP : IsInternalCrossPacking G s P)
    (hQ : IsInternalCrossPacking G s Q)
    (hcross : ∀ t ∈ P, ∀ u ∈ Q, (t ∩ u).card ≤ 1) :
    IsInternalCrossPacking G s (P ∪ Q) ∧
      (P ∪ Q).card = P.card + Q.card := by
  have hPQ : Disjoint P Q := by
    rw [Finset.disjoint_left]
    intro t htP htQ
    have hle := hcross t htP t htQ
    rw [inter_self] at hle
    have htCard := (mem_internalCrossTriangles.mp (hP.1 htP)).1.card_eq
    omega
  refine ⟨⟨union_subset hP.1 hQ.1, ?_⟩,
    card_union_of_disjoint hPQ⟩
  intro t ht u hu htu
  rcases mem_union.mp ht with htP | htQ
  · rcases mem_union.mp hu with huP | huQ
    · exact hP.2 htP huP htu
    · exact hcross t htP u huQ
  · rcases mem_union.mp hu with huP | huQ
    · simpa [inter_comm] using hcross u huP t htQ
    · exact hQ.2 htQ huQ htu

lemma internalCrossPackings_nonempty (G : SimpleGraph α) (s : Set α) :
    (internalCrossPackings G s).Nonempty := by
  exact ⟨∅, mem_internalCrossPackings.mpr (empty_isInternalCrossPacking G s)⟩

/-- The maximum family whose existence is invoked at the start of
Proposition 4.2.  The final field is its exact extremal property, stated
without introducing a separate numerical supremum. -/
theorem exists_maximum_internalCrossPacking (G : SimpleGraph α) (s : Set α) :
    ∃ P : Finset (Finset α), IsInternalCrossPacking G s P ∧
      ∀ Q : Finset (Finset α), IsInternalCrossPacking G s Q →
        Q.card ≤ P.card := by
  obtain ⟨P, hP, hmax⟩ :=
    Finset.exists_max_image (internalCrossPackings G s) Finset.card
      (internalCrossPackings_nonempty G s)
  exact ⟨P, mem_internalCrossPackings.mp hP, fun Q hQ ↦
    hmax Q (mem_internalCrossPackings.mpr hQ)⟩

/-- Finite column type for the LP of fractional cross-triangle packings. -/
abbrev InternalCrossTriangleIndex (G : SimpleGraph α) (s : Set α) :=
  {t : Finset α // t ∈ internalCrossTriangles G s}

noncomputable instance internalCrossTriangleIndexFintype
    (G : SimpleGraph α) (s : Set α) :
    Fintype (InternalCrossTriangleIndex G s) :=
  Fintype.ofFinite _

/-- Edge--cross-triangle incidence matrix.  Rows retain all graph edges, so
the LP has exactly the edge-capacity constraints of a fractional packing. -/
noncomputable def internalCrossIncidenceMatrix (G : SimpleGraph α) (s : Set α) :
    Matrix (LPDuality.EdgeIndex G) (InternalCrossTriangleIndex G s) ℝ := by
  classical
  exact fun e t ↦ if e.val ∈ t.val.sym2 then 1 else 0

/-- Extend a vector indexed by cross triangles by zero to all vertex sets. -/
noncomputable def internalCrossWeight (G : SimpleGraph α) (s : Set α)
    (x : InternalCrossTriangleIndex G s → ℝ) : Finset α → ℝ := by
  classical
  exact fun t ↦ if ht : t ∈ internalCrossTriangles G s then x ⟨t, ht⟩ else 0

@[simp] lemma internalCrossWeight_index (G : SimpleGraph α) (s : Set α)
    (x : InternalCrossTriangleIndex G s → ℝ)
    (t : InternalCrossTriangleIndex G s) :
    internalCrossWeight G s x t.val = x t := by
  classical
  rw [internalCrossWeight, dif_pos t.property]

lemma internalCrossIncidenceMatrix_exists_one (G : SimpleGraph α) (s : Set α)
    (t : InternalCrossTriangleIndex G s) :
    ∃ e : LPDuality.EdgeIndex G, internalCrossIncidenceMatrix G s e t = 1 := by
  let t' : LPDuality.TriangleIndex G :=
    ⟨t.val, (mem_internalCrossTriangles.mp t.property).1⟩
  obtain ⟨e, he⟩ := LPDuality.triangleIncidenceMatrix_exists_one G t'
  exact ⟨e, by simpa [internalCrossIncidenceMatrix,
    LPDuality.triangleIncidenceMatrix, t'] using he⟩

lemma internalCrossIncidence_mulVec_apply (G : SimpleGraph α) (s : Set α)
    (x : InternalCrossTriangleIndex G s → ℝ) (e : LPDuality.EdgeIndex G) :
    Matrix.mulVec (internalCrossIncidenceMatrix G s) x e =
      fractionalEdgeLoad G (internalCrossWeight G s x) e.val := by
  classical
  rw [Matrix.mulVec, dotProduct, fractionalEdgeLoad]
  calc
    ∑ i, internalCrossIncidenceMatrix G s e i * x i =
        ∑ i : InternalCrossTriangleIndex G s,
          (if e.val ∈ i.val.sym2 then 1 else 0) *
            internalCrossWeight G s x i.val := by
      apply sum_congr rfl
      intro i _hi
      rw [internalCrossWeight_index]
      rfl
    _ = ∑ t ∈ internalCrossTriangles G s,
          (if e.val ∈ t.sym2 then 1 else 0) * internalCrossWeight G s x t :=
      (sum_subtype (internalCrossTriangles G s) (fun _t ↦ Iff.rfl)
        (fun t ↦ (if e.val ∈ t.sym2 then 1 else 0) *
          internalCrossWeight G s x t)).symm
    _ = ∑ t ∈ internalCrossTriangles G s with e.val ∈ t.sym2,
          internalCrossWeight G s x t := by
      rw [sum_filter]
      apply sum_congr rfl
      intro t _ht
      by_cases het : e.val ∈ t.sym2 <;> simp [het]
    _ = ∑ t ∈ G.cliqueFinset 3 with e.val ∈ t.sym2,
          internalCrossWeight G s x t := by
      apply sum_subset
      · intro t ht
        rcases mem_filter.mp ht with ⟨htCross, het⟩
        exact mem_filter.mpr ⟨
          SimpleGraph.mem_cliqueFinset_iff.mpr
            (mem_internalCrossTriangles.mp htCross).1, het⟩
      · intro t htG htCross
        rw [internalCrossWeight, dif_neg]
        intro ht
        exact htCross (mem_filter.mpr ⟨ht, (mem_filter.mp htG).2⟩)

lemma fractionalSize_internalCrossWeight (G : SimpleGraph α) (s : Set α)
    (x : InternalCrossTriangleIndex G s → ℝ) :
    fractionalSize G (internalCrossWeight G s x) = ∑ t, x t := by
  classical
  calc
    fractionalSize G (internalCrossWeight G s x) =
        ∑ t ∈ G.cliqueFinset 3, internalCrossWeight G s x t := rfl
    _ = ∑ t ∈ internalCrossTriangles G s, internalCrossWeight G s x t := by
      symm
      apply sum_subset
      · intro t ht
        exact SimpleGraph.mem_cliqueFinset_iff.mpr
          (mem_internalCrossTriangles.mp ht).1
      · intro t _htG htCross
        rw [internalCrossWeight, dif_neg htCross]
    _ = ∑ t : InternalCrossTriangleIndex G s,
        internalCrossWeight G s x t.val :=
      sum_subtype (internalCrossTriangles G s) (fun _t ↦ Iff.rfl)
        (internalCrossWeight G s x)
    _ = ∑ t, x t := sum_congr rfl fun t _ ↦
      internalCrossWeight_index G s x t

/-- Feasible fractional packing supported only on cross triangles. -/
def IsFractionalInternalCrossPacking (G : SimpleGraph α) (s : Set α)
    (w : Finset α → ℝ) : Prop :=
  IsFractionalPacking G w ∧
    ∀ t : Finset α, t ∉ internalCrossTriangles G s → w t = 0

/-- A cross triangle contains exactly one internal edge, so summing the
loads of the internal edges counts every supported triangle weight exactly
once.  This is the bookkeeping identity used to compute the missing weight
of the two residual capacities in Proposition 4.2. -/
lemma sum_internalEdge_fractionalEdgeLoad_eq_fractionalSize
    {G : SimpleGraph α} {s : Set α} {w : Finset α → ℝ}
    (hw : IsFractionalInternalCrossPacking G s w) :
    (∑ e ∈ internalEdgeFinset G s, fractionalEdgeLoad G w e) =
      fractionalSize G w := by
  rw [fractionalSize]
  simp_rw [fractionalEdgeLoad, Finset.sum_filter]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro t ht
  rw [show
      (∑ e ∈ internalEdgeFinset G s, if e ∈ t.sym2 then w t else 0) =
        ∑ e ∈ (internalEdgeFinset G s).filter (fun e ↦ e ∈ t.sym2), w t by
    rw [Finset.sum_filter]]
  rw [Finset.sum_const, nsmul_eq_mul]
  by_cases htCross : t ∈ internalCrossTriangles G s
  · rw [(mem_internalCrossTriangles.mp htCross).2]
    norm_num
  · rw [hw.2 t htCross]
    simp

/-- The load carried by either one of the two sides is at most the total
cross-triangle weight.  Together with exact truncation, this is the simple
capacity estimate used when the saturated side has eleven vertices in the
`n = 24` boundary case. -/
lemma sum_sideEdge_fractionalEdgeLoad_le_fractionalSize
    {G : SimpleGraph α} {s : Set α} {w : Finset α → ℝ}
    (hw : IsFractionalInternalCrossPacking G s w) :
    (∑ e ∈ sideEdgeFinset G s.toFinset, fractionalEdgeLoad G w e) ≤
      fractionalSize G w := by
  have htotal := sum_internalEdge_fractionalEdgeLoad_eq_fractionalSize hw
  rw [internalEdgeFinset_eq_union_sides,
    sum_union (sideEdgeFinset_disjoint_compl G s)] at htotal
  have hother : 0 ≤
      ∑ e ∈ sideEdgeFinset G sᶜ.toFinset, fractionalEdgeLoad G w e := by
    apply sum_nonneg
    intro e _he
    unfold fractionalEdgeLoad
    apply sum_nonneg
    intro t ht
    exact hw.1.nonneg_on (mem_filter.mp ht).1
  linarith

lemma isFractionalInternalCrossPacking_internalCrossWeight
    (G : SimpleGraph α) (s : Set α)
    (x : InternalCrossTriangleIndex G s → ℝ)
    (hx : ∀ t, 0 ≤ x t)
    (hload : ∀ e, Matrix.mulVec (internalCrossIncidenceMatrix G s) x e ≤ 1) :
    IsFractionalInternalCrossPacking G s (internalCrossWeight G s x) := by
  constructor
  · constructor
    · intro t _htG
      rw [internalCrossWeight]
      split
      · exact hx _
      · exact le_rfl
    · intro e heG
      let e' : LPDuality.EdgeIndex G :=
        ⟨e, SimpleGraph.mem_edgeFinset.mp heG⟩
      rw [← internalCrossIncidence_mulVec_apply G s x e']
      exact hload e'
  · intro t ht
    rw [internalCrossWeight, dif_neg ht]

lemma fractionalSize_eq_sum_internalCross_of_supported
    {G : SimpleGraph α} {s : Set α} {w : Finset α → ℝ}
    (hw : ∀ t : Finset α, t ∉ internalCrossTriangles G s → w t = 0) :
    fractionalSize G w = ∑ t : InternalCrossTriangleIndex G s, w t.val := by
  classical
  calc
    fractionalSize G w = ∑ t ∈ G.cliqueFinset 3, w t := rfl
    _ = ∑ t ∈ internalCrossTriangles G s, w t := by
      symm
      apply sum_subset
      · intro t ht
        exact SimpleGraph.mem_cliqueFinset_iff.mpr
          (mem_internalCrossTriangles.mp ht).1
      · intro t _htG htCross
        exact hw t htCross
    _ = ∑ t : InternalCrossTriangleIndex G s, w t.val :=
      sum_subtype (internalCrossTriangles G s) (fun _t ↦ Iff.rfl) w

/-- Strong finite LP attainment for the restricted cross-triangle problem.
This supplies the maximum fractional red cross packing `T_R` selected in the
proof of Proposition 4.2, including its exact support condition. -/
theorem exists_maximal_fractionalInternalCrossPacking
    (G : SimpleGraph α) (s : Set α) :
    ∃ w : Finset α → ℝ, IsFractionalInternalCrossPacking G s w ∧
      ∀ u : Finset α → ℝ, IsFractionalInternalCrossPacking G s u →
        fractionalSize G u ≤ fractionalSize G w := by
  classical
  by_cases hcross : (internalCrossTriangles G s).Nonempty
  · let : Nonempty (InternalCrossTriangleIndex G s) :=
      ⟨⟨hcross.choose, hcross.choose_spec⟩⟩
    let : Nonempty (LPDuality.EdgeIndex G) := by
      obtain ⟨e, _he⟩ := internalCrossIncidenceMatrix_exists_one G s
        (Classical.arbitrary (InternalCrossTriangleIndex G s))
      exact ⟨e⟩
    obtain ⟨x, y, hx, hload, hy, hcover, hxy⟩ :=
      LPDuality.matrix_fractional_matching_cover_of_column_pos
        (internalCrossIncidenceMatrix G s)
        (by
          intro e t
          by_cases h : e.val ∈ t.val.sym2 <;>
            simp [internalCrossIncidenceMatrix, h])
        (by
          intro t
          obtain ⟨e, he⟩ := internalCrossIncidenceMatrix_exists_one G s t
          exact ⟨e, he ▸ zero_lt_one⟩)
    refine ⟨internalCrossWeight G s x,
      isFractionalInternalCrossPacking_internalCrossWeight G s x hx hload, ?_⟩
    intro u hu
    let xu : InternalCrossTriangleIndex G s → ℝ := fun t ↦ u t.val
    have hxu : ∀ t, 0 ≤ xu t := by
      intro t
      exact hu.1.nonneg_on
        (SimpleGraph.mem_cliqueFinset_iff.mpr
          (mem_internalCrossTriangles.mp t.property).1)
    have hloadu : ∀ e,
        Matrix.mulVec (internalCrossIncidenceMatrix G s) xu e ≤ 1 := by
      intro e
      rw [internalCrossIncidence_mulVec_apply]
      calc
        fractionalEdgeLoad G (internalCrossWeight G s xu) e.val =
            fractionalEdgeLoad G u e.val := by
          unfold fractionalEdgeLoad
          apply sum_congr rfl
          intro t ht
          by_cases htCross : t ∈ internalCrossTriangles G s
          · rw [internalCrossWeight, dif_pos htCross]
          · rw [internalCrossWeight, dif_neg htCross, hu.2 t htCross]
        _ ≤ 1 := hu.1.edgeLoad_le_one
          (SimpleGraph.mem_edgeFinset.mpr e.property)
    calc
      fractionalSize G u = ∑ t, xu t := by
        rw [fractionalSize_eq_sum_internalCross_of_supported hu.2]
      _ ≤ ∑ e, y e :=
        LPDuality.weak_fractional_matching_cover_duality
          (internalCrossIncidenceMatrix G s) xu y hxu hloadu hy hcover
      _ = ∑ t, x t := hxy.symm
      _ = fractionalSize G (internalCrossWeight G s x) :=
        (fractionalSize_internalCrossWeight G s x).symm
  · let : IsEmpty (InternalCrossTriangleIndex G s) :=
      ⟨fun t ↦ hcross ⟨t.val, t.property⟩⟩
    refine ⟨fun _ ↦ 0, ⟨isFractionalPacking_zero G, by simp⟩, ?_⟩
    intro u hu
    rw [fractionalSize_eq_sum_internalCross_of_supported hu.2]
    simp

/-- Scale every triangle weight by the same real factor. -/
def scaleTriangleWeight (c : ℝ) (w : Finset α → ℝ) : Finset α → ℝ :=
  fun t ↦ c * w t

lemma fractionalSize_scaleTriangleWeight (G : SimpleGraph α) (c : ℝ)
    (w : Finset α → ℝ) :
    fractionalSize G (scaleTriangleWeight c w) = c * fractionalSize G w := by
  unfold fractionalSize scaleTriangleWeight
  rw [mul_sum]

lemma isFractionalPacking_scaleTriangleWeight
    {G : SimpleGraph α} {w : Finset α → ℝ} (hw : IsFractionalPacking G w)
    {c : ℝ} (hc0 : 0 ≤ c) (hc1 : c ≤ 1) :
    IsFractionalPacking G (scaleTriangleWeight c w) := by
  constructor
  · intro t ht
    exact mul_nonneg hc0 (hw.nonneg_on ht)
  · intro e he
    change fractionalEdgeLoad G (fun t ↦ c * w t) e ≤ 1
    rw [fractionalEdgeLoad_smul]
    calc
      c * fractionalEdgeLoad G w e ≤ c * 1 :=
        mul_le_mul_of_nonneg_left (hw.edgeLoad_le_one he) hc0
      _ ≤ 1 := by simpa using hc1

lemma isFractionalInternalCrossPacking_scaleTriangleWeight
    {G : SimpleGraph α} {s : Set α} {w : Finset α → ℝ}
    (hw : IsFractionalInternalCrossPacking G s w)
    {c : ℝ} (hc0 : 0 ≤ c) (hc1 : c ≤ 1) :
    IsFractionalInternalCrossPacking G s (scaleTriangleWeight c w) := by
  refine ⟨isFractionalPacking_scaleTriangleWeight hw.1 hc0 hc1, ?_⟩
  intro t ht
  simp [scaleTriangleWeight, hw.2 t ht]

/-- Any feasible fractional cross packing can be truncated to every total
weight between zero and its current weight. -/
lemma exists_fractionalInternalCrossPacking_of_size_between
    {G : SimpleGraph α} {s : Set α} {w : Finset α → ℝ}
    (hw : IsFractionalInternalCrossPacking G s w) {q : ℝ}
    (hq0 : 0 ≤ q) (hq : q ≤ fractionalSize G w) :
    ∃ u : Finset α → ℝ,
      IsFractionalInternalCrossPacking G s u ∧ fractionalSize G u = q := by
  by_cases hzero : fractionalSize G w = 0
  · have hqzero : q = 0 := by
      have hw0 : 0 ≤ fractionalSize G w :=
        fractionalSize_nonneg hw.1
      linarith
    exact ⟨w, hw, hzero.trans hqzero.symm⟩
  · have hwpos : 0 < fractionalSize G w := by
      exact lt_of_le_of_ne (fractionalSize_nonneg hw.1) (Ne.symm hzero)
    let c := q / fractionalSize G w
    have hc0 : 0 ≤ c := div_nonneg hq0 hwpos.le
    have hc1 : c ≤ 1 := (div_le_one hwpos).mpr hq
    refine ⟨scaleTriangleWeight c w,
      isFractionalInternalCrossPacking_scaleTriangleWeight hw hc0 hc1, ?_⟩
    rw [fractionalSize_scaleTriangleWeight]
    dsimp only [c]
    exact div_mul_cancel₀ q hzero

/-- An integral edge-disjoint family of cross triangles is, with unit
weights, a feasible point of the restricted fractional cross-triangle LP.
This is the bridge used when the explicit matchings in Claims 4.3 and 4.4
are compared with the maximum fractional red packing. -/
lemma isFractionalInternalCrossPacking_integralPackingWeight
    {G : SimpleGraph α} {s : Set α} {P : Finset (Finset α)}
    (hP : IsInternalCrossPacking G s P) :
    IsFractionalInternalCrossPacking G s (integralPackingWeight P) := by
  refine ⟨isFractionalPacking_integralPackingWeight hP.2, ?_⟩
  intro t htCross
  rw [integralPackingWeight, if_neg]
  intro htP
  exact htCross (hP.1 htP)

/-- Every integral cross packing gives a cardinality lower bound on a
maximal fractional cross packing. -/
lemma card_le_fractionalSize_of_maximal_fractionalInternalCrossPacking
    {G : SimpleGraph α} {s : Set α} {w : Finset α → ℝ}
    (hmax : ∀ u : Finset α → ℝ, IsFractionalInternalCrossPacking G s u →
      fractionalSize G u ≤ fractionalSize G w)
    {P : Finset (Finset α)} (hP : IsInternalCrossPacking G s P) :
    (P.card : ℝ) ≤ fractionalSize G w := by
  have hcandidate := hmax (integralPackingWeight P)
    (isFractionalInternalCrossPacking_integralPackingWeight hP)
  rwa [fractionalSize_integralPackingWeight
    (fun t htP ↦ (mem_internalCrossTriangles.mp (hP.1 htP)).1)] at hcandidate

omit [Fintype α] in
lemma edgeDisjoint_insert_of_inter_card_le_one
    {P : Finset (Finset α)} {t : Finset α}
    (hP : EdgeDisjoint P)
    (ht : ∀ u ∈ P, (t ∩ u).card ≤ 1) :
    EdgeDisjoint (insert t P) := by
  intro a ha b hb hab
  rcases mem_insert.mp ha with rfl | ha
  · rcases mem_insert.mp hb with rfl | hb
    · exact (hab rfl).elim
    · exact ht b hb
  · rcases mem_insert.mp hb with hbt | hb
    · subst b
      simpa [inter_comm] using ht a ha
    · exact hP ha hb hab

/-- Maximality obstruction for the chosen family: every eligible triangle
not already selected shares an edge (two vertices) with a selected triangle.
This is the precise insertion argument used repeatedly in Proposition 4.2. -/
lemma maximum_internalCrossPacking_blocks_triangle
    {G : SimpleGraph α} {s : Set α} {P : Finset (Finset α)}
    (hP : IsInternalCrossPacking G s P)
    (hmax : ∀ Q : Finset (Finset α), IsInternalCrossPacking G s Q →
      Q.card ≤ P.card)
    {t : Finset α} (ht : t ∈ internalCrossTriangles G s) (htP : t ∉ P) :
    ∃ u ∈ P, 2 ≤ (t ∩ u).card := by
  by_contra hblocked
  push Not at hblocked
  have hinter : ∀ u ∈ P, (t ∩ u).card ≤ 1 := by
    intro u hu
    have hnot := hblocked u hu
    omega
  have hins : IsInternalCrossPacking G s (insert t P) := by
    refine ⟨?_, edgeDisjoint_insert_of_inter_card_le_one hP.2 hinter⟩
    exact insert_subset ht hP.1
  have hcard := hmax (insert t P) hins
  rw [card_insert_of_notMem htP] at hcard
  omega

/-- In particular, an eligible triangle through an internal edge left
uncovered by a maximum packing is blocked by another edge of a selected
triangle. -/
lemma maximum_internalCrossPacking_blocks_uncovered_edge
    {G : SimpleGraph α} {s : Set α} {P : Finset (Finset α)}
    (hP : IsInternalCrossPacking G s P)
    (hmax : ∀ Q : Finset (Finset α), IsInternalCrossPacking G s Q →
      Q.card ≤ P.card)
    {e : Sym2 α} (_he : e ∈ internalEdgeFinset G s)
    (heP : ∀ u ∈ P, e ∉ u.sym2)
    {t : Finset α} (ht : t ∈ internalCrossTriangles G s)
    (het : e ∈ t.sym2) :
    ∃ u ∈ P, 2 ≤ (t ∩ u).card := by
  apply maximum_internalCrossPacking_blocks_triangle hP hmax ht
  intro htP
  exact heP t htP het

/-- Vertices used by an integral triangle family. -/
def packingVertices (P : Finset (Finset α)) : Finset α :=
  P.biUnion id

@[simp] lemma mem_packingVertices {P : Finset (Finset α)} {v : α} :
    v ∈ packingVertices P ↔ ∃ t ∈ P, v ∈ t := by
  simp [packingVertices]

/-- The vertex support of an integral cross-triangle packing has size at
most three times the number of selected triangles.  This is the
`|T₁| + |T₂| ≤ 3m` estimate in Claim 4.3. -/
lemma card_packingVertices_le_three_mul
    {G : SimpleGraph α} {s : Set α} {P : Finset (Finset α)}
    (hP : IsInternalCrossPacking G s P) :
    (packingVertices P).card ≤ 3 * P.card := by
  calc
    (packingVertices P).card = (P.biUnion id).card := rfl
    _ ≤ ∑ t ∈ P, t.card := card_biUnion_le
    _ = ∑ _t ∈ P, 3 := by
      apply sum_congr rfl
      intro t htP
      exact (mem_internalCrossTriangles.mp (hP.1 htP)).1.card_eq
    _ = 3 * P.card := by simp [mul_comm]

lemma internal_triangle_edges_eq_of_subset
    {G : SimpleGraph α} {s : Set α} {t : Finset α}
    (hts : (↑t : Set α) ⊆ s) :
    (internalEdgeFinset G s).filter (fun e ↦ e ∈ t.sym2) =
      G.edgeFinset.filter (fun e ↦ e ∈ t.sym2) := by
  ext e
  simp only [internalEdgeFinset, mem_filter]
  constructor
  · rintro ⟨⟨heG, _heSide⟩, het⟩
    exact ⟨heG, het⟩
  · rintro ⟨heG, het⟩
    refine ⟨⟨heG, ?_⟩, het⟩
    induction e using Sym2.inductionOn with
    | hf a b =>
        rw [sameSide_mk]
        have hab := mem_sym2_iff.mp het
        exact iff_of_true (hts (by simpa using hab a (by simp)))
          (hts (by simpa using hab b (by simp)))

lemma internal_triangle_edges_eq_of_disjoint
    {G : SimpleGraph α} {s : Set α} {t : Finset α}
    (hts : ∀ v ∈ t, v ∉ s) :
    (internalEdgeFinset G s).filter (fun e ↦ e ∈ t.sym2) =
      G.edgeFinset.filter (fun e ↦ e ∈ t.sym2) := by
  ext e
  simp only [internalEdgeFinset, mem_filter]
  constructor
  · rintro ⟨⟨heG, _heSide⟩, het⟩
    exact ⟨heG, het⟩
  · rintro ⟨heG, het⟩
    refine ⟨⟨heG, ?_⟩, het⟩
    induction e using Sym2.inductionOn with
    | hf a b =>
        rw [sameSide_mk]
        have hab := mem_sym2_iff.mp het
        exact iff_of_false (hts a (hab a (by simp))) (hts b (hab b (by simp)))

/-- A cross triangle has at most two vertices in either fixed part. -/
lemma card_filter_mem_set_le_two_of_internalCrossTriangle
    {G : SimpleGraph α} {s : Set α} {t : Finset α}
    (ht : t ∈ internalCrossTriangles G s) :
    (t.filter fun v ↦ v ∈ s).card ≤ 2 := by
  have htData := mem_internalCrossTriangles.mp ht
  by_contra hcard
  have hthree : 3 ≤ (t.filter fun v ↦ v ∈ s).card := by omega
  have hfilterSub : (t.filter fun v ↦ v ∈ s) ⊆ t := filter_subset _ _
  have hfilterEq : (t.filter fun v ↦ v ∈ s) = t := by
    apply eq_of_subset_of_card_le hfilterSub
    rw [htData.1.card_eq]
    exact hthree
  have hts : (↑t : Set α) ⊆ s := by
    intro v hv
    have hvFilter : v ∈ t.filter fun v ↦ v ∈ s := by
      rw [hfilterEq]
      exact hv
    exact (mem_filter.mp hvFilter).2
  have hedgeEq := internal_triangle_edges_eq_of_subset (G := G) hts
  have hthreeEdges := card_edgeFinset_filter_triangle_generic t htData.1
  rw [hedgeEq, hthreeEdges] at htData
  omega

/-- Each part contains at most two used vertices per selected cross triangle.
This is the sharper `|T| ≤ 2m` support estimate used in Claim 4.4. -/
lemma card_packingVertices_filter_le_two_mul
    {G : SimpleGraph α} {s : Set α} {P : Finset (Finset α)}
    (hP : IsInternalCrossPacking G s P) :
    ((packingVertices P).filter fun v ↦ v ∈ s).card ≤ 2 * P.card := by
  have hfilter :
      (packingVertices P).filter (fun v ↦ v ∈ s) =
        P.biUnion (fun t ↦ t.filter fun v ↦ v ∈ s) := by
    ext v
    simp only [mem_filter, mem_packingVertices, mem_biUnion]
    constructor
    · rintro ⟨⟨t, htP, hvt⟩, hvs⟩
      exact ⟨t, htP, hvt, hvs⟩
    · rintro ⟨t, htP, hvt, hvs⟩
      exact ⟨⟨t, htP, hvt⟩, hvs⟩
  rw [hfilter]
  calc
    (P.biUnion (fun t ↦ t.filter fun v ↦ v ∈ s)).card ≤
        ∑ t ∈ P, (t.filter fun v ↦ v ∈ s).card := card_biUnion_le
    _ ≤ ∑ _t ∈ P, 2 := by
      apply sum_le_sum
      intro t htP
      exact card_filter_mem_set_le_two_of_internalCrossTriangle (hP.1 htP)
    _ = 2 * P.card := by simp [mul_comm]

/-- Select one endpoint of every unordered pair. -/
noncomputable def chosenEndpointCover (E : Finset (Sym2 α)) : Finset α :=
  E.image fun e ↦ e.out.1

lemma card_chosenEndpointCover_le (E : Finset (Sym2 α)) :
    (chosenEndpointCover E).card ≤ E.card := by
  exact card_image_le

lemma chosenEndpoint_mem_cover {E : Finset (Sym2 α)} {e : Sym2 α}
    (he : e ∈ E) : e.out.1 ∈ chosenEndpointCover E := by
  exact mem_image.mpr ⟨e, he, rfl⟩

lemma chosenEndpoint_mem_pair (e : Sym2 α) : e.out.1 ∈ e :=
  Sym2.out_fst_mem e

/-- The selected endpoints form a vertex cover of the displayed unordered
pairs, with at most one selected vertex per pair. -/
lemma exists_endpointCover (E : Finset (Sym2 α)) :
    ∃ C : Finset α, C.card ≤ E.card ∧
      ∀ e ∈ E, ∃ v ∈ C, v ∈ e := by
  refine ⟨chosenEndpointCover E, card_chosenEndpointCover_le E, ?_⟩
  intro e he
  exact ⟨e.out.1, chosenEndpoint_mem_cover he, chosenEndpoint_mem_pair e⟩

/-- Edges of `G` whose endpoints both lie in `X \ D`. -/
def edgesInsideOutside (G : SimpleGraph α) (X D : Finset α) :
    Finset (Sym2 α) :=
  G.edgeFinset.filter fun e ↦ e.toFinset ⊆ X \ D

/-- Selecting one endpoint of every `G`-edge inside `X \ D` leaves a clique
of the opposite colour.  This packages the vertex-cover-to-red-clique step
in the proof of Claim 4.3. -/
lemma compl_induce_remainder_eq_top (G : SimpleGraph α) (X D : Finset α) :
    let C := chosenEndpointCover (edgesInsideOutside G X D)
    Gᶜ.induce (((X \ D) \ C : Finset α) : Set α) = ⊤ := by
  classical
  intro C
  apply SimpleGraph.induce_eq_top.mpr
  intro a ha b hb hab
  rw [SimpleGraph.compl_adj]
  refine ⟨hab, ?_⟩
  intro hGab
  let e : Sym2 α := s(a, b)
  have heG : e ∈ G.edgeFinset :=
    SimpleGraph.mem_edgeFinset.mpr hGab
  have heSub : e.toFinset ⊆ X \ D := by
    intro v hve
    have hvab : v = a ∨ v = b := by
      simpa [e, Sym2.toFinset_mk_eq] using hve
    rcases hvab with rfl | rfl
    · exact (mem_sdiff.mp ha).1
    · exact (mem_sdiff.mp hb).1
  have heE : e ∈ edgesInsideOutside G X D :=
    mem_filter.mpr ⟨heG, heSub⟩
  have heC : e.out.1 ∈ C := chosenEndpoint_mem_cover heE
  have hout : e.out.1 = a ∨ e.out.1 = b := by
    have := chosenEndpoint_mem_pair e
    simpa [e, Sym2.mem_iff] using this
  rcases hout with hout | hout
  · exact (mem_sdiff.mp ha).2 (hout ▸ heC)
  · exact (mem_sdiff.mp hb).2 (hout ▸ heC)

/-- Every finite clique has a matching covering all but at most one of its
vertices.  In the even case this is a perfect matching; in the odd case we
delete one vertex and apply the even-clique matching theorem.  This is the
floor-sized matching input used in Claims 4.3 and 4.4. -/
lemma SimpleGraph.IsClique.exists_matching_cover_all_but_one
    {G : SimpleGraph α} {u : Set α} (hu : G.IsClique u) :
    ∃ M : G.Subgraph, M.IsMatching ∧ M.verts ⊆ u ∧
      u.ncard ≤ M.verts.toFinset.card + 1 := by
  classical
  by_cases heven : Even u.ncard
  · obtain ⟨M, hverts, hM⟩ :=
      (hu.even_iff_exists_isMatching (Set.toFinite u)).mp heven
    refine ⟨M, hM, hverts.le, ?_⟩
    rw [hverts, ← Set.ncard_eq_toFinset_card']
    exact Nat.le_add_right _ _
  · have hodd : Odd u.ncard := Nat.not_even_iff_odd.mp heven
    have hne : u.Nonempty := by
      rw [Set.nonempty_iff_ne_empty]
      intro huEmpty
      subst u
      exact heven (by simp)
    obtain ⟨x, hx⟩ := hne
    let v : Set α := u \ {x}
    have hvClique : G.IsClique v := hu.subset Set.diff_subset
    have hvEven : Even v.ncard := by
      change Even (u \ {x}).ncard
      rw [Set.ncard_sdiff_singleton_of_mem hx]
      have hone : 1 ≤ u.ncard := by
        obtain ⟨k, hk⟩ := hodd
        omega
      exact (Nat.even_sub hone).mpr (by simpa using heven)
    obtain ⟨M, hverts, hM⟩ :=
      (hvClique.even_iff_exists_isMatching (Set.toFinite v)).mp hvEven
    refine ⟨M, hM, hverts.le.trans Set.diff_subset, ?_⟩
    rw [← Set.ncard_sdiff_singleton_add_one hx (Set.toFinite u)]
    change v.ncard + 1 ≤ M.verts.toFinset.card + 1
    rw [← hverts, Set.ncard_eq_toFinset_card']

/-- A finite matching has exactly two vertices per edge.  This proof counts
the two-element fibres of `IsMatching.toEdge`; unlike a degree-sum proof it
does not depend on choosing definitionally identical local finiteness
instances for a subgraph and its coerced simple graph. -/
lemma SimpleGraph.Subgraph.IsMatching.card_verts_eq_two_mul_card_edgeFinset_GL
    {G : SimpleGraph α} {M : G.Subgraph} (hM : M.IsMatching) :
    M.verts.toFinset.card = 2 * Fintype.card M.edgeSet := by
  classical
  calc
    M.verts.toFinset.card = Fintype.card M.verts := Set.toFinset_card _
    _ = ∑ e : M.edgeSet,
        ((Finset.univ : Finset M.verts).filter fun v ↦ hM.toEdge v = e).card := by
      rw [← Finset.card_univ]
      exact Finset.card_eq_sum_card_fiberwise (by simp)
    _ = ∑ _e : M.edgeSet, 2 := by
      apply sum_congr rfl
      rintro e _he
      obtain ⟨⟨u, v⟩, huv⟩ := e
      have hfiber := hM.toEdge_preimage_singleton huv
      rw [← Set.ncard_coe_finset]
      rw [show (↑((Finset.univ : Finset M.verts).filter fun x ↦
          hM.toEdge x = ⟨s(u, v), huv⟩) : Set M.verts) =
          hM.toEdge ⁻¹' {⟨s(u, v), huv⟩} by ext x; simp,
        hfiber]
      simp [huv.ne]
    _ = 2 * Fintype.card M.edgeSet := by
      simp [Nat.mul_comm]

/-- Distinct edges of a matching have disjoint endpoint sets.  The proof
uses the canonical incident edge supplied by `IsMatching.toEdge`, avoiding
any conversion through degree instances. -/
lemma SimpleGraph.Subgraph.IsMatching.disjoint_edge_toFinset_GL
    {G : SimpleGraph α} {M : G.Subgraph} (hM : M.IsMatching)
    {e f : M.edgeSet} (hef : e ≠ f) :
    Disjoint e.1.toFinset f.1.toFinset := by
  classical
  rw [Finset.disjoint_left]
  intro x hxe hxf
  have hxverts : x ∈ M.verts :=
    M.mem_verts_of_mem_edge e.property (by simpa using hxe)
  have hedge : ∀ (q : M.edgeSet), x ∈ q.1.toFinset →
      hM.toEdge ⟨x, hxverts⟩ = q := by
    rintro ⟨⟨a, b⟩, hab⟩ hxq
    have hxab : x = a ∨ x = b := by
      simpa [Sym2.toFinset_mk_eq] using hxq
    rcases hxab with rfl | rfl
    · exact hM.toEdge_eq_of_adj hab
    · simpa only [Sym2.eq_swap] using hM.toEdge_eq_of_adj hab.symm
  exact hef ((hedge e hxe).symm.trans (hedge f hxf))

/-- Attach a fixed vertex to every edge of a matching. -/
def attachedMatchingTriangles {G : SimpleGraph α} (M : G.Subgraph) (z : α) :
    Finset (Finset α) :=
  Finset.univ.image fun e : M.edgeSet ↦ insert z e.1.toFinset

/-- Every vertex used by a matching star is either the attachment vertex or
one of the matched vertices.  Recording this support is what lets the two
opposite-side constructions in Claim 4.3 be united without creating a
cross-family edge intersection. -/
lemma packingVertices_attachedMatchingTriangles_subset
    {G : SimpleGraph α} (M : G.Subgraph) (z : α) :
    packingVertices (attachedMatchingTriangles M z) ⊆
      insert z M.verts.toFinset := by
  classical
  intro x hx
  obtain ⟨t, ht, hxt⟩ := mem_packingVertices.mp hx
  obtain ⟨e, _he, rfl⟩ := mem_image.mp ht
  rcases mem_insert.mp hxt with rfl | hxe
  · exact mem_insert_self _ _
  · exact mem_insert_of_mem (by
      simpa using M.mem_verts_of_mem_edge e.property (by simpa using hxe))

/-- Disjoint vertex supports are a convenient sufficient condition for
uniting two cross packings. -/
lemma IsInternalCrossPacking.union_of_disjoint_packingVertices
    {G : SimpleGraph α} {s : Set α} {P Q : Finset (Finset α)}
    (hP : IsInternalCrossPacking G s P)
    (hQ : IsInternalCrossPacking G s Q)
    (hdis : Disjoint (packingVertices P) (packingVertices Q)) :
    IsInternalCrossPacking G s (P ∪ Q) ∧
      (P ∪ Q).card = P.card + Q.card := by
  apply hP.union_of_cross_inter_card_le_one hQ
  intro t htP u huQ
  have htu : Disjoint t u := by
    rw [Finset.disjoint_left]
    intro x hxt hxu
    exact Finset.disjoint_left.mp hdis
      (mem_packingVertices.mpr ⟨t, htP, hxt⟩)
      (mem_packingVertices.mpr ⟨u, huQ, hxu⟩)
  rw [Finset.disjoint_iff_inter_eq_empty.mp htu]
  simp

/-- Attaching a vertex outside the matching does not identify two matching
edges, so the resulting family has exactly one triangle per edge. -/
lemma card_attachedMatchingTriangles {G : SimpleGraph α} {M : G.Subgraph}
    (z : α) (hz : z ∉ M.verts) :
    (attachedMatchingTriangles M z).card = Fintype.card M.edgeSet := by
  classical
  have hinj : Function.Injective
      (fun e : M.edgeSet ↦ insert z e.1.toFinset) := by
    intro e f hef
    have hno : ∀ q : M.edgeSet, z ∉ q.1.toFinset := by
      intro q hzq
      exact hz (M.mem_verts_of_mem_edge q.property (by simpa using hzq))
    have hers := congrArg (fun t : Finset α ↦ t.erase z) hef
    have hpair : e.1.toFinset = f.1.toFinset := by
      simpa [hno e, hno f] using hers
    apply Subtype.ext
    apply Sym2.ext
    intro x
    simpa using Finset.ext_iff.mp hpair x
  calc
    (attachedMatchingTriangles M z).card =
        (Finset.univ : Finset M.edgeSet).card := by
      exact card_image_of_injective _ hinj
    _ = Fintype.card M.edgeSet := Finset.card_univ

/-- If the attachment vertex is adjacent to every matched vertex, every
attached set is a graph triangle. -/
lemma attachedMatchingTriangles_are_triangles
    {G : SimpleGraph α} {M : G.Subgraph} {z : α}
    (hz : z ∉ M.verts)
    (hstar : ∀ v ∈ M.verts, G.Adj z v) :
    ∀ t ∈ attachedMatchingTriangles M z, G.IsNClique 3 t := by
  classical
  intro t ht
  obtain ⟨⟨⟨u, v⟩, huv⟩, _he, rfl⟩ := mem_image.mp ht
  rw [Sym2.toFinset_mk_eq]
  apply SimpleGraph.is3Clique_triple_iff.mpr
  exact ⟨hstar u (M.edge_vert huv),
    hstar v (M.edge_vert huv.symm), M.adj_sub huv⟩

/-- Triangles obtained by attaching one vertex to the distinct edges of a
matching are pairwise edge-disjoint: their only possible common vertex is
the attachment vertex. -/
lemma attachedMatchingTriangles_edgeDisjoint
    {G : SimpleGraph α} {M : G.Subgraph} {z : α}
    (hM : M.IsMatching) : EdgeDisjoint (attachedMatchingTriangles M z) := by
  classical
  intro t ht u hu htu
  obtain ⟨e, _he, rfl⟩ := mem_image.mp ht
  obtain ⟨f, _hf, rfl⟩ := mem_image.mp hu
  have hef : e ≠ f := by
    intro hef
    exact htu (congrArg (fun q : M.edgeSet ↦ insert z q.1.toFinset) hef)
  have hdis :=
    SimpleGraph.Subgraph.IsMatching.disjoint_edge_toFinset_GL hM hef
  apply (card_le_one).mpr
  intro x hx y hy
  have hx' := mem_inter.mp hx
  have hy' := mem_inter.mp hy
  have classify : ∀ q : M.edgeSet, ∀ a,
      a ∈ insert z q.1.toFinset → a = z ∨ a ∈ q.1.toFinset := by
    intro q a ha
    simpa using ha
  rcases classify e x hx'.1 with rfl | hxe
  · rcases classify e y hy'.1 with rfl | hye
    · rfl
    · rcases classify f y hy'.2 with rfl | hyf
      · rfl
      · exact (Finset.disjoint_left.mp hdis hye hyf).elim
  · rcases classify f x hx'.2 with rfl | hxf
    · rcases classify e y hy'.1 with rfl | hye
      · rfl
      · rcases classify f y hy'.2 with rfl | hyf
        · rfl
        · exact (Finset.disjoint_left.mp hdis hye hyf).elim
    · exact (Finset.disjoint_left.mp hdis hxe hxf).elim

/-- Packaged one-star construction used twice in each of Claims 4.3 and
4.4. -/
lemma attachedMatchingTriangles_certificate
    {G : SimpleGraph α} {M : G.Subgraph} {z : α}
    (hM : M.IsMatching) (hz : z ∉ M.verts)
    (hstar : ∀ v ∈ M.verts, G.Adj z v) :
    (∀ t ∈ attachedMatchingTriangles M z, G.IsNClique 3 t) ∧
      EdgeDisjoint (attachedMatchingTriangles M z) ∧
      (attachedMatchingTriangles M z).card = Fintype.card M.edgeSet := by
  exact ⟨attachedMatchingTriangles_are_triangles hz hstar,
    attachedMatchingTriangles_edgeDisjoint hM,
    card_attachedMatchingTriangles z hz⟩

/-- If a matching lies in one side of a bipartition and the attachment
vertex lies in the other side, its attached triangles form an integral
cross packing. -/
lemma attachedMatchingTriangles_isInternalCrossPacking
    {G : SimpleGraph α} {M : G.Subgraph} {z : α} {s : Set α}
    (hM : M.IsMatching) (hverts : M.verts ⊆ s) (hzside : z ∉ s)
    (hstar : ∀ v ∈ M.verts, G.Adj z v) :
    IsInternalCrossPacking G s (attachedMatchingTriangles M z) := by
  refine ⟨?_, attachedMatchingTriangles_edgeDisjoint hM⟩
  intro t ht
  have htClique := attachedMatchingTriangles_are_triangles
    (M := M) (z := z) (fun hz ↦ hzside (hverts hz)) hstar t ht
  obtain ⟨⟨⟨u, v⟩, huv⟩, _he, htForm⟩ := mem_image.mp ht
  rw [← htForm] at htClique ⊢
  apply mem_internalCrossTriangles.mpr
  refine ⟨htClique, ?_⟩
  rw [show (internalEdgeFinset G s).filter
      (fun e ↦ e ∈ (insert z s(u, v).toFinset).sym2) = {s(u, v)} by
    ext q
    induction q using Sym2.inductionOn with
    | hf a b =>
        simp only [mem_filter, internalEdgeFinset, SimpleGraph.mem_edgeFinset,
          sameSide_mk, Finset.mk_mem_sym2_iff, Sym2.toFinset_mk_eq,
          mem_insert, mem_singleton]
        have hu : u ∈ s := hverts (M.edge_vert huv)
        have hv : v ∈ s := hverts (M.edge_vert huv.symm)
        constructor
        · rintro ⟨⟨hab, hsab⟩, ha, hb⟩
          rcases ha with rfl | rfl | rfl <;>
            rcases hb with rfl | rfl | rfl <;>
            simp_all [huv.ne, Sym2.eq_swap]
        · intro hab
          rcases Sym2.eq_iff.mp hab with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
          · exact ⟨⟨M.adj_sub huv, iff_of_true hu hv⟩, by simp, by simp⟩
          · exact ⟨⟨M.adj_sub huv.symm, iff_of_true hv hu⟩, by simp, by simp⟩]
  simp

/-- With disjoint matching bases and attachment vertices outside the other
base, triangles belonging to two different stars are vertex-disjoint. -/
lemma attachedMatchingTriangles_cross_inter_eq_empty
    {G : SimpleGraph α} {M N : G.Subgraph} {z w : α}
    (hMN : Disjoint M.verts N.verts) (hzw : z ≠ w)
    (hzN : z ∉ N.verts) (hwM : w ∉ M.verts) :
    ∀ t ∈ attachedMatchingTriangles M z,
      ∀ u ∈ attachedMatchingTriangles N w, t ∩ u = ∅ := by
  classical
  intro t ht u hu
  obtain ⟨e, _he, rfl⟩ := mem_image.mp ht
  obtain ⟨f, _hf, rfl⟩ := mem_image.mp hu
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro x hx
  have hx' := mem_inter.mp hx
  have hxe : x = z ∨ x ∈ e.1.toFinset := by simpa using hx'.1
  have hxf : x = w ∨ x ∈ f.1.toFinset := by simpa using hx'.2
  rcases hxe with rfl | hxe
  · rcases hxf with hzw' | hzf
    · exact hzw hzw'
    · exact hzN (N.mem_verts_of_mem_edge f.property (by simpa using hzf))
  · rcases hxf with rfl | hxf
    · exact hwM (M.mem_verts_of_mem_edge e.property (by simpa using hxe))
    · exact Set.disjoint_left.mp hMN
        (M.mem_verts_of_mem_edge e.property (by simpa using hxe))
        (N.mem_verts_of_mem_edge f.property (by simpa using hxf))

/-- Two-star matching construction.  This is the exact finite certificate
used when Claim 4.3 or Claim 4.4 attaches two disjoint red matchings to the
two endpoints of an uncovered blue edge. -/
lemma attachedMatchingTriangles_union_certificate
    {G : SimpleGraph α} {M N : G.Subgraph} {z w : α}
    (hM : M.IsMatching) (hN : N.IsMatching)
    (hMN : Disjoint M.verts N.verts) (hzw : z ≠ w)
    (hzM : z ∉ M.verts) (hzN : z ∉ N.verts)
    (hwM : w ∉ M.verts) (hwN : w ∉ N.verts)
    (hstarM : ∀ v ∈ M.verts, G.Adj z v)
    (hstarN : ∀ v ∈ N.verts, G.Adj w v) :
    let P := attachedMatchingTriangles M z
    let Q := attachedMatchingTriangles N w
    (∀ t ∈ P ∪ Q, G.IsNClique 3 t) ∧ EdgeDisjoint (P ∪ Q) ∧
      (P ∪ Q).card = Fintype.card M.edgeSet + Fintype.card N.edgeSet := by
  classical
  intro P Q
  have hPc := attachedMatchingTriangles_certificate hM hzM hstarM
  have hQc := attachedMatchingTriangles_certificate hN hwN hstarN
  have hcross : ∀ t ∈ P, ∀ u ∈ Q, t ∩ u = ∅ := by
    exact attachedMatchingTriangles_cross_inter_eq_empty hMN hzw hzN hwM
  have hPQ : Disjoint P Q := by
    rw [Finset.disjoint_left]
    intro t htP htQ
    have hempty := hcross t htP t htQ
    have hcard := (hPc.1 t htP).card_eq
    have htEmpty : t = ∅ := by simpa using hempty
    subst t
    simp at hcard
  refine ⟨?_, ?_, ?_⟩
  · intro t ht
    rcases mem_union.mp ht with htP | htQ
    · exact hPc.1 t htP
    · exact hQc.1 t htQ
  · intro t ht u hu htu
    rcases mem_union.mp ht with htP | htQ
    · rcases mem_union.mp hu with huP | huQ
      · exact hPc.2.1 htP huP htu
      · rw [hcross t htP u huQ]
        simp
    · rcases mem_union.mp hu with huP | huQ
      · rw [Finset.inter_comm, hcross u huP t htQ]
        simp
      · exact hQc.2.1 htQ huQ htu
  · rw [card_union_of_disjoint hPQ, hPc.2.2, hQc.2.2]

/-- Cross-packing form of the two-star construction.  Both matching bases
lie in one side and both attachment vertices lie in the opposite side. -/
lemma attachedMatchingTriangles_union_isInternalCrossPacking
    {G : SimpleGraph α} {M N : G.Subgraph} {z w : α} {s : Set α}
    (hM : M.IsMatching) (hN : N.IsMatching)
    (hMN : Disjoint M.verts N.verts) (hzw : z ≠ w)
    (hMverts : M.verts ⊆ s) (hNverts : N.verts ⊆ s)
    (hzside : z ∉ s) (hwside : w ∉ s)
    (hstarM : ∀ v ∈ M.verts, G.Adj z v)
    (hstarN : ∀ v ∈ N.verts, G.Adj w v) :
    let P := attachedMatchingTriangles M z
    let Q := attachedMatchingTriangles N w
    IsInternalCrossPacking G s (P ∪ Q) ∧
      (P ∪ Q).card =
        Fintype.card M.edgeSet + Fintype.card N.edgeSet := by
  classical
  intro P Q
  have hzM : z ∉ M.verts := fun hz ↦ hzside (hMverts hz)
  have hzN : z ∉ N.verts := fun hz ↦ hzside (hNverts hz)
  have hwM : w ∉ M.verts := fun hw ↦ hwside (hMverts hw)
  have hwN : w ∉ N.verts := fun hw ↦ hwside (hNverts hw)
  have hPM := attachedMatchingTriangles_isInternalCrossPacking
    hM hMverts hzside hstarM
  have hQN := attachedMatchingTriangles_isInternalCrossPacking
    hN hNverts hwside hstarN
  have hcert := attachedMatchingTriangles_union_certificate hM hN hMN hzw
    hzM hzN hwM hwN hstarM hstarN
  exact ⟨⟨union_subset hPM.1 hQN.1, hcert.2.1⟩, hcert.2.2⟩

/-- Matching consequence used in Claim 4.3.  Two disjoint red cliques on
one side of the partition, attached to two different vertices on the other
side, give a red cross packing which uses all but at most one vertex of
each clique. -/
lemma exists_twoStarCrossPacking_of_disjoint_cliques
    {G : SimpleGraph α} {s : Set α} {A B : Finset α} {z w : α}
    (hA : G.IsClique (A : Set α)) (hB : G.IsClique (B : Set α))
    (hAB : Disjoint A B)
    (hAs : ∀ x ∈ A, x ∈ s) (hBs : ∀ x ∈ B, x ∈ s)
    (hzside : z ∉ s) (hwside : w ∉ s) (hzw : z ≠ w)
    (hzA : ∀ x ∈ A, G.Adj z x)
    (hwB : ∀ x ∈ B, G.Adj w x) :
    ∃ P : Finset (Finset α), IsInternalCrossPacking G s P ∧
      A.card + B.card ≤ 2 * P.card + 2 := by
  classical
  obtain ⟨MA, hMA, hMAverts, hMAcard⟩ :=
    SimpleGraph.IsClique.exists_matching_cover_all_but_one hA
  obtain ⟨MB, hMB, hMBverts, hMBcard⟩ :=
    SimpleGraph.IsClique.exists_matching_cover_all_but_one hB
  have hMAs : MA.verts ⊆ s := fun x hx ↦
    hAs x (by exact hMAverts hx)
  have hMBs : MB.verts ⊆ s := fun x hx ↦
    hBs x (by exact hMBverts hx)
  have hMAMB : Disjoint MA.verts MB.verts := by
    rw [Set.disjoint_left]
    intro x hxA hxB
    exact Finset.disjoint_left.mp hAB (hMAverts hxA) (hMBverts hxB)
  have hzMA : ∀ x ∈ MA.verts, G.Adj z x := fun x hx ↦
    hzA x (hMAverts hx)
  have hwMB : ∀ x ∈ MB.verts, G.Adj w x := fun x hx ↦
    hwB x (hMBverts hx)
  let P := attachedMatchingTriangles MA z ∪ attachedMatchingTriangles MB w
  have hP := attachedMatchingTriangles_union_isInternalCrossPacking
    hMA hMB hMAMB hzw hMAs hMBs hzside hwside hzMA hwMB
  refine ⟨P, hP.1, ?_⟩
  have hAc : A.card ≤ 2 * Fintype.card MA.edgeSet + 1 := by
    calc
      A.card = ((A : Set α)).ncard := by simp
      _ ≤ MA.verts.toFinset.card + 1 := hMAcard
      _ = 2 * Fintype.card MA.edgeSet + 1 := by
        rw [SimpleGraph.Subgraph.IsMatching.card_verts_eq_two_mul_card_edgeFinset_GL hMA]
  have hBc : B.card ≤ 2 * Fintype.card MB.edgeSet + 1 := by
    calc
      B.card = ((B : Set α)).ncard := by simp
      _ ≤ MB.verts.toFinset.card + 1 := hMBcard
      _ = 2 * Fintype.card MB.edgeSet + 1 := by
        rw [SimpleGraph.Subgraph.IsMatching.card_verts_eq_two_mul_card_edgeFinset_GL hMB]
  dsimp only [P]
  rw [hP.2]
  omega

/-- Support-refined version of the two-star construction.  The additional
last field is needed when the constructions on the two opposite sides are
combined in Claim 4.3. -/
lemma exists_twoStarCrossPacking_of_disjoint_cliques_with_support
    {G : SimpleGraph α} {s : Set α} {A B : Finset α} {z w : α}
    (hA : G.IsClique (A : Set α)) (hB : G.IsClique (B : Set α))
    (hAB : Disjoint A B)
    (hAs : ∀ x ∈ A, x ∈ s) (hBs : ∀ x ∈ B, x ∈ s)
    (hzside : z ∉ s) (hwside : w ∉ s) (hzw : z ≠ w)
    (hzA : ∀ x ∈ A, G.Adj z x)
    (hwB : ∀ x ∈ B, G.Adj w x) :
    ∃ P : Finset (Finset α), IsInternalCrossPacking G s P ∧
      A.card + B.card ≤ 2 * P.card + 2 ∧
      packingVertices P ⊆ A ∪ B ∪ {z, w} := by
  classical
  obtain ⟨MA, hMA, hMAverts, hMAcard⟩ :=
    SimpleGraph.IsClique.exists_matching_cover_all_but_one hA
  obtain ⟨MB, hMB, hMBverts, hMBcard⟩ :=
    SimpleGraph.IsClique.exists_matching_cover_all_but_one hB
  have hMAs : MA.verts ⊆ s := fun x hx ↦ hAs x (hMAverts hx)
  have hMBs : MB.verts ⊆ s := fun x hx ↦ hBs x (hMBverts hx)
  have hMAMB : Disjoint MA.verts MB.verts := by
    rw [Set.disjoint_left]
    intro x hxA hxB
    exact Finset.disjoint_left.mp hAB (hMAverts hxA) (hMBverts hxB)
  have hzMA : ∀ x ∈ MA.verts, G.Adj z x := fun x hx ↦
    hzA x (hMAverts hx)
  have hwMB : ∀ x ∈ MB.verts, G.Adj w x := fun x hx ↦
    hwB x (hMBverts hx)
  let PA := attachedMatchingTriangles MA z
  let PB := attachedMatchingTriangles MB w
  let P := PA ∪ PB
  have hP := attachedMatchingTriangles_union_isInternalCrossPacking
    hMA hMB hMAMB hzw hMAs hMBs hzside hwside hzMA hwMB
  have hAc : A.card ≤ 2 * Fintype.card MA.edgeSet + 1 := by
    calc
      A.card = ((A : Set α)).ncard := by simp
      _ ≤ MA.verts.toFinset.card + 1 := hMAcard
      _ = 2 * Fintype.card MA.edgeSet + 1 := by
        rw [SimpleGraph.Subgraph.IsMatching.card_verts_eq_two_mul_card_edgeFinset_GL hMA]
  have hBc : B.card ≤ 2 * Fintype.card MB.edgeSet + 1 := by
    calc
      B.card = ((B : Set α)).ncard := by simp
      _ ≤ MB.verts.toFinset.card + 1 := hMBcard
      _ = 2 * Fintype.card MB.edgeSet + 1 := by
        rw [SimpleGraph.Subgraph.IsMatching.card_verts_eq_two_mul_card_edgeFinset_GL hMB]
  refine ⟨P, hP.1, ?_, ?_⟩
  · dsimp only [P, PA, PB]
    rw [hP.2]
    omega
  · intro x hx
    obtain ⟨t, htP, hxt⟩ := mem_packingVertices.mp hx
    rcases mem_union.mp htP with htA | htB
    · have hxPA : x ∈ packingVertices PA :=
        mem_packingVertices.mpr ⟨t, htA, hxt⟩
      have hxBound := packingVertices_attachedMatchingTriangles_subset MA z hxPA
      rcases mem_insert.mp hxBound with rfl | hxMA
      · simp [P]
      · have hxA : x ∈ A := hMAverts (by simpa using hxMA)
        simp [P, hxA]
    · have hxPB : x ∈ packingVertices PB :=
        mem_packingVertices.mpr ⟨t, htB, hxt⟩
      have hxBound := packingVertices_attachedMatchingTriangles_subset MB w hxPB
      rcases mem_insert.mp hxBound with rfl | hxMB
      · simp [P]
      · have hxB : x ∈ B := hMBverts (by simpa using hxMB)
        simp [P, hxB]

/-- The two opposite-side two-star constructions of Claim 4.3 combine into
one cross packing.  The disjoint-envelope hypothesis is the exact support
condition later obtained by deleting the packing support and the two chosen
uncovered edges before forming the red cliques. -/
lemma exists_fourStarCrossPacking_of_disjoint_envelopes
    {G : SimpleGraph α} {s : Set α}
    {A₁ B₁ A₂ B₂ : Finset α} {z₁ w₁ z₂ w₂ : α}
    (hA₁ : G.IsClique (A₁ : Set α)) (hB₁ : G.IsClique (B₁ : Set α))
    (hA₂ : G.IsClique (A₂ : Set α)) (hB₂ : G.IsClique (B₂ : Set α))
    (hAB₁ : Disjoint A₁ B₁) (hAB₂ : Disjoint A₂ B₂)
    (hA₁s : ∀ x ∈ A₁, x ∈ s) (hB₁s : ∀ x ∈ B₁, x ∈ s)
    (hA₂s : ∀ x ∈ A₂, x ∈ sᶜ) (hB₂s : ∀ x ∈ B₂, x ∈ sᶜ)
    (hz₁side : z₁ ∉ s) (hw₁side : w₁ ∉ s)
    (hz₂side : z₂ ∉ sᶜ) (hw₂side : w₂ ∉ sᶜ)
    (hzw₁ : z₁ ≠ w₁) (hzw₂ : z₂ ≠ w₂)
    (hzA₁ : ∀ x ∈ A₁, G.Adj z₁ x)
    (hwB₁ : ∀ x ∈ B₁, G.Adj w₁ x)
    (hzA₂ : ∀ x ∈ A₂, G.Adj z₂ x)
    (hwB₂ : ∀ x ∈ B₂, G.Adj w₂ x)
    (henv : Disjoint (A₁ ∪ B₁ ∪ {z₁, w₁})
      (A₂ ∪ B₂ ∪ {z₂, w₂})) :
    ∃ P : Finset (Finset α), IsInternalCrossPacking G s P ∧
      A₁.card + B₁.card + A₂.card + B₂.card ≤ 2 * P.card + 4 := by
  obtain ⟨P₁, hP₁, hcard₁, hsupp₁⟩ :=
    exists_twoStarCrossPacking_of_disjoint_cliques_with_support
      hA₁ hB₁ hAB₁ hA₁s hB₁s hz₁side hw₁side hzw₁ hzA₁ hwB₁
  obtain ⟨P₂, hP₂c, hcard₂, hsupp₂⟩ :=
    exists_twoStarCrossPacking_of_disjoint_cliques_with_support
      hA₂ hB₂ hAB₂ hA₂s hB₂s hz₂side hw₂side hzw₂ hzA₂ hwB₂
  have hP₂ : IsInternalCrossPacking G s P₂ :=
    (isInternalCrossPacking_set_compl_iff G s P₂).mp (by
      simpa only [compl_compl] using hP₂c)
  have hdis : Disjoint (packingVertices P₁) (packingVertices P₂) := by
    rw [Finset.disjoint_left]
    intro x hx₁ hx₂
    exact Finset.disjoint_left.mp henv (hsupp₁ hx₁) (hsupp₂ hx₂)
  have hP := hP₁.union_of_disjoint_packingVertices hP₂ hdis
  refine ⟨P₁ ∪ P₂, hP.1, ?_⟩
  rw [hP.2]
  omega

/-- LP comparison form of the complete four-star construction in Claim
4.3. -/
lemma fourStarClique_card_le_maximal_fractionalInternalCrossPacking
    {G : SimpleGraph α} {s : Set α}
    {A₁ B₁ A₂ B₂ : Finset α} {z₁ w₁ z₂ w₂ : α}
    {weight : Finset α → ℝ}
    (hmax : ∀ u : Finset α → ℝ, IsFractionalInternalCrossPacking G s u →
      fractionalSize G u ≤ fractionalSize G weight)
    (hA₁ : G.IsClique (A₁ : Set α)) (hB₁ : G.IsClique (B₁ : Set α))
    (hA₂ : G.IsClique (A₂ : Set α)) (hB₂ : G.IsClique (B₂ : Set α))
    (hAB₁ : Disjoint A₁ B₁) (hAB₂ : Disjoint A₂ B₂)
    (hA₁s : ∀ x ∈ A₁, x ∈ s) (hB₁s : ∀ x ∈ B₁, x ∈ s)
    (hA₂s : ∀ x ∈ A₂, x ∈ sᶜ) (hB₂s : ∀ x ∈ B₂, x ∈ sᶜ)
    (hz₁side : z₁ ∉ s) (hw₁side : w₁ ∉ s)
    (hz₂side : z₂ ∉ sᶜ) (hw₂side : w₂ ∉ sᶜ)
    (hzw₁ : z₁ ≠ w₁) (hzw₂ : z₂ ≠ w₂)
    (hzA₁ : ∀ x ∈ A₁, G.Adj z₁ x)
    (hwB₁ : ∀ x ∈ B₁, G.Adj w₁ x)
    (hzA₂ : ∀ x ∈ A₂, G.Adj z₂ x)
    (hwB₂ : ∀ x ∈ B₂, G.Adj w₂ x)
    (henv : Disjoint (A₁ ∪ B₁ ∪ {z₁, w₁})
      (A₂ ∪ B₂ ∪ {z₂, w₂})) :
    (((A₁.card + B₁.card + A₂.card + B₂.card : ℕ) : ℝ)) ≤
      2 * fractionalSize G weight + 4 := by
  obtain ⟨P, hP, hcard⟩ :=
    exists_fourStarCrossPacking_of_disjoint_envelopes
      hA₁ hB₁ hA₂ hB₂ hAB₁ hAB₂ hA₁s hB₁s hA₂s hB₂s
      hz₁side hw₁side hz₂side hw₂side hzw₁ hzw₂
      hzA₁ hwB₁ hzA₂ hwB₂ henv
  have hPmax : (P.card : ℝ) ≤ fractionalSize G weight :=
    card_le_fractionalSize_of_maximal_fractionalInternalCrossPacking hmax hP
  have hcardR :
      (((A₁.card + B₁.card + A₂.card + B₂.card : ℕ) : ℝ)) ≤
        ((2 * P.card + 4 : ℕ) : ℝ) := by
    exact_mod_cast hcard
  push_cast at hcardR
  push_cast
  linarith

/-- LP comparison form of `exists_twoStarCrossPacking_of_disjoint_cliques`:
the maximal fractional cross packing has at least half the two clique sizes,
up to the two parity losses. -/
lemma twoStarClique_card_le_maximal_fractionalInternalCrossPacking
    {G : SimpleGraph α} {s : Set α} {A B : Finset α} {z w : α}
    {weight : Finset α → ℝ}
    (hmax : ∀ u : Finset α → ℝ, IsFractionalInternalCrossPacking G s u →
      fractionalSize G u ≤ fractionalSize G weight)
    (hA : G.IsClique (A : Set α)) (hB : G.IsClique (B : Set α))
    (hAB : Disjoint A B)
    (hAs : ∀ x ∈ A, x ∈ s) (hBs : ∀ x ∈ B, x ∈ s)
    (hzside : z ∉ s) (hwside : w ∉ s) (hzw : z ≠ w)
    (hzA : ∀ x ∈ A, G.Adj z x)
    (hwB : ∀ x ∈ B, G.Adj w x) :
    ((A.card + B.card : ℕ) : ℝ) ≤
      2 * fractionalSize G weight + 2 := by
  obtain ⟨P, hP, hcard⟩ := exists_twoStarCrossPacking_of_disjoint_cliques
    hA hB hAB hAs hBs hzside hwside hzw hzA hwB
  have hPmax : (P.card : ℝ) ≤ fractionalSize G weight :=
    card_le_fractionalSize_of_maximal_fractionalInternalCrossPacking hmax hP
  have hcardR : ((A.card + B.card : ℕ) : ℝ) ≤
      (2 * P.card + 2 : ℕ) := by exact_mod_cast hcard
  push_cast at hcardR
  push_cast
  linarith

/-- The explicit Claim 4.3 output of the endpoint-cover construction: the
opposite-colour graph has a matching covering all but at most one vertex of
the uncovered remainder. -/
lemma exists_matching_in_compl_remainder
    (G : SimpleGraph α) (X D : Finset α) :
    let C := chosenEndpointCover (edgesInsideOutside G X D)
    ∃ M : Gᶜ.Subgraph, M.IsMatching ∧
      M.verts ⊆ (((X \ D) \ C : Finset α) : Set α) ∧
      ((X \ D) \ C).card ≤ M.verts.toFinset.card + 1 := by
  classical
  intro C
  have hClique : Gᶜ.IsClique ((((X \ D) \ C : Finset α) : Set α)) :=
    SimpleGraph.induce_eq_top.mp (compl_induce_remainder_eq_top G X D)
  obtain ⟨M, hM, hverts, hcard⟩ :=
    SimpleGraph.IsClique.exists_matching_cover_all_but_one hClique
  refine ⟨M, hM, hverts, ?_⟩
  calc
    ((X \ D) \ C).card =
        ((((X \ D) \ C : Finset α) : Set α)).ncard := by
      rw [Set.ncard_coe_finset]
    _ ≤ M.verts.toFinset.card + 1 := hcard

/-- Edge-count form of the preceding matching estimate.  It is this form
that turns directly into the lower bounds for the red cross-triangle
packing in Claims 4.3 and 4.4. -/
lemma exists_matching_in_compl_remainder_edgeCount
    (G : SimpleGraph α) (X D : Finset α) :
    let C := chosenEndpointCover (edgesInsideOutside G X D)
    ∃ M : Gᶜ.Subgraph, M.IsMatching ∧
      M.verts ⊆ (((X \ D) \ C : Finset α) : Set α) ∧
      ((X \ D) \ C).card ≤ 2 * Fintype.card M.edgeSet + 1 := by
  classical
  intro C
  obtain ⟨M, hM, hverts, hcard⟩ := exists_matching_in_compl_remainder G X D
  refine ⟨M, hM, hverts, ?_⟩
  rw [← SimpleGraph.Subgraph.IsMatching.card_verts_eq_two_mul_card_edgeFinset_GL hM]
  exact hcard

/-- Adding a common neighbour from the opposite side to an internal edge
produces an eligible cross triangle. -/
lemma insert_mem_internalCrossTriangles_of_opposite
    {G : SimpleGraph α} {s : Set α} {a b x : α}
    (hab : G.Adj a b) (hsame : a ∈ s ↔ b ∈ s)
    (hxside : ¬ (x ∈ s ↔ a ∈ s))
    (hxa : G.Adj x a) (hxb : G.Adj x b) :
    insert x ({a, b} : Finset α) ∈ internalCrossTriangles G s := by
  apply mem_internalCrossTriangles.mpr
  refine ⟨SimpleGraph.is3Clique_triple_iff.mpr ⟨hxa, hxb, hab⟩, ?_⟩
  rw [show (internalEdgeFinset G s).filter
      (fun e ↦ e ∈ (insert x ({a, b} : Finset α)).sym2) = {s(a, b)} by
    ext q
    induction q using Sym2.inductionOn with
    | hf u v =>
        simp only [mem_filter, internalEdgeFinset, SimpleGraph.mem_edgeFinset,
          sameSide_mk, Finset.mk_mem_sym2_iff, mem_insert, mem_singleton]
        constructor
        · rintro ⟨⟨huv, hsuv⟩, hu, hv⟩
          rcases hu with rfl | rfl | rfl <;>
            rcases hv with rfl | rfl | rfl <;>
            simp_all [Sym2.eq_swap]
        · intro huv
          rcases Sym2.eq_iff.mp huv with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
          · exact ⟨⟨hab, hsame⟩, by simp, by simp⟩
          · exact ⟨⟨hab.symm, hsame.symm⟩, by simp, by simp⟩]
  simp

/-- Maximality forbids an unused opposite-side common neighbour of an
uncovered internal edge.  This is the first sentence of Claim 4.3 and is
also the neighbourhood input in Claim 4.4. -/
lemma maximum_internalCrossPacking_no_common_unused_opposite_neighbor
    {G : SimpleGraph α} {s : Set α} {P : Finset (Finset α)}
    (hP : IsInternalCrossPacking G s P)
    (hmax : ∀ Q : Finset (Finset α), IsInternalCrossPacking G s Q →
      Q.card ≤ P.card)
    {a b x : α}
    (he : s(a, b) ∈ internalEdgeFinset G s)
    (heP : ∀ u ∈ P, s(a, b) ∉ u.sym2)
    (hxside : ¬ (x ∈ s ↔ a ∈ s))
    (hxunused : x ∉ packingVertices P) :
    ¬ (G.Adj a x ∧ G.Adj b x) := by
  rintro ⟨hax, hbx⟩
  have hedata := mem_filter.mp he
  have habG : G.Adj a b := SimpleGraph.mem_edgeFinset.mp hedata.1
  have ht : insert x ({a, b} : Finset α) ∈ internalCrossTriangles G s :=
    insert_mem_internalCrossTriangles_of_opposite habG
      (by simpa [sameSide_mk] using hedata.2) hxside hax.symm hbx.symm
  obtain ⟨u, huP, htwo⟩ :=
    maximum_internalCrossPacking_blocks_uncovered_edge hP hmax he heP ht
      (by simp [Sym2.toFinset_mk_eq])
  have hxu : x ∉ u := by
    intro hxu
    exact hxunused (mem_packingVertices.mpr ⟨u, huP, hxu⟩)
  have hinter : insert x ({a, b} : Finset α) ∩ u = {a, b} ∩ u := by
    ext v
    simp [hxu]
  rw [hinter] at htwo
  have habcard : ({a, b} : Finset α).card = 2 := by
    simp [habG.ne]
  have hinterEq : ({a, b} : Finset α) ∩ u = {a, b} := by
    apply eq_of_subset_of_card_le inter_subset_left
    omega
  have haInter : a ∈ ({a, b} : Finset α) ∩ u := by
    rw [hinterEq]
    simp
  have hbInter : b ∈ ({a, b} : Finset α) ∩ u := by
    rw [hinterEq]
    simp
  exact heP u huP (Finset.mk_mem_sym2_iff.mpr ⟨
    (mem_inter.mp haInter).2, (mem_inter.mp hbInter).2⟩)

/-- Maximality consequence used in Claim 4.3.  If `e` is an uncovered
internal edge and `e ∪ {z}` is an eligible cross triangle, then `z` already
occurs in the chosen packing.  Otherwise the blocking triangle supplied by
maximality would have to contain both endpoints of `e`, contradicting that
`e` is uncovered. -/
lemma maximum_internalCrossPacking_forces_third_vertex_used
    {G : SimpleGraph α} {s : Set α} {P : Finset (Finset α)}
    (hP : IsInternalCrossPacking G s P)
    (hmax : ∀ Q : Finset (Finset α), IsInternalCrossPacking G s Q →
      Q.card ≤ P.card)
    {e : Sym2 α} (he : e ∈ internalEdgeFinset G s)
    (heP : ∀ u ∈ P, e ∉ u.sym2)
    {t : Finset α} (ht : t ∈ internalCrossTriangles G s)
    {z : α} (htForm : t = insert z e.toFinset) :
    z ∈ packingVertices P := by
  obtain ⟨u, huP, htwo⟩ :=
    maximum_internalCrossPacking_blocks_uncovered_edge hP hmax he heP ht
      (by
        subst t
        apply mem_sym2_iff.mpr
        intro v hv
        exact mem_insert_of_mem (by simpa using hv))
  by_contra hzUsed
  have hzu : z ∉ u := by
    intro hzu
    exact hzUsed (mem_packingVertices.mpr ⟨u, huP, hzu⟩)
  have hinter : insert z e.toFinset ∩ u = e.toFinset ∩ u := by
    ext v
    simp [hzu]
  rw [htForm, hinter] at htwo
  have heG : e ∈ G.edgeFinset := (mem_filter.mp he).1
  have hecard : e.toFinset.card = 2 :=
    SimpleGraph.card_toFinset_mem_edgeFinset ⟨e, heG⟩
  have hinterEq : e.toFinset ∩ u = e.toFinset := by
    apply eq_of_subset_of_card_le inter_subset_left
    omega
  have hesub : e.toFinset ⊆ u := by
    intro v hv
    have hv' : v ∈ e.toFinset ∩ u := by simpa [hinterEq] using hv
    exact (mem_inter.mp hv').2
  exact heP u huP (mem_sym2_iff.mpr fun v hv ↦ hesub (by simpa using hv))

/-- Internal edges covered by a selected family of cross triangles. -/
def coveredInternalEdges (G : SimpleGraph α) (s : Set α)
    (P : Finset (Finset α)) : Finset (Sym2 α) :=
  (internalEdgeFinset G s).filter fun e ↦ ∃ t ∈ P, e ∈ t.sym2

@[simp] lemma coveredInternalEdges_set_compl
    (G : SimpleGraph α) (s : Set α) (P : Finset (Finset α)) :
    coveredInternalEdges G sᶜ P = coveredInternalEdges G s P := by
  simp [coveredInternalEdges]

lemma coveredInternalEdges_eq_biUnion (G : SimpleGraph α) (s : Set α)
    (P : Finset (Finset α)) :
    coveredInternalEdges G s P =
      P.biUnion fun t ↦
        (internalEdgeFinset G s).filter fun e ↦ e ∈ t.sym2 := by
  ext e
  simp only [coveredInternalEdges, mem_filter, mem_biUnion]
  constructor
  · rintro ⟨he, t, htP, het⟩
    exact ⟨t, htP, he, het⟩
  · rintro ⟨t, htP, he, het⟩
    exact ⟨he, t, htP, het⟩

/-- Edge-disjoint triangles have pairwise disjoint sets of internal edges. -/
lemma pairwiseDisjoint_internalEdges_of_edgeDisjoint
    {G : SimpleGraph α} {s : Set α} {P : Finset (Finset α)}
    (hP : EdgeDisjoint P) :
    (P : Set (Finset α)).PairwiseDisjoint fun t ↦
      (internalEdgeFinset G s).filter fun e ↦ e ∈ t.sym2 := by
  intro t htP u huP htu
  change Disjoint
    ((internalEdgeFinset G s).filter fun e ↦ e ∈ t.sym2)
    ((internalEdgeFinset G s).filter fun e ↦ e ∈ u.sym2)
  rw [Finset.disjoint_left]
  intro e het heu
  rcases mem_filter.mp het with ⟨heInternal, het⟩
  rcases mem_filter.mp heu with ⟨_, heu⟩
  have hesub : e.toFinset ⊆ t ∩ u := by
    intro v hve
    have hve' : v ∈ e := by simpa using hve
    exact mem_inter.mpr ⟨(mem_sym2_iff.mp het) v hve',
      (mem_sym2_iff.mp heu) v hve'⟩
  have heG : e ∈ G.edgeFinset := (mem_filter.mp heInternal).1
  have hecard : e.toFinset.card = 2 :=
    SimpleGraph.card_toFinset_mem_edgeFinset ⟨e, heG⟩
  have htwo : 2 ≤ (t ∩ u).card := by
    simpa [hecard] using card_le_card hesub
  have hone := hP htP huP htu
  omega

/-- Every selected cross triangle contributes one different internal edge.
Consequently the number `m` of covered internal edges in the paper is exactly
the cardinality of the integral cross-triangle packing. -/
lemma card_coveredInternalEdges_eq_card
    {G : SimpleGraph α} {s : Set α} {P : Finset (Finset α)}
    (hP : IsInternalCrossPacking G s P) :
    (coveredInternalEdges G s P).card = P.card := by
  rw [coveredInternalEdges_eq_biUnion,
    card_biUnion (pairwiseDisjoint_internalEdges_of_edgeDisjoint hP.2)]
  calc
    (∑ t ∈ P,
        ((internalEdgeFinset G s).filter fun e ↦ e ∈ t.sym2).card) =
        ∑ _t ∈ P, 1 := by
      apply sum_congr rfl
      intro t htP
      exact (mem_internalCrossTriangles.mp (hP.1 htP)).2
    _ = P.card := by simp

/-- Covered internal edges whose two endpoints lie in a specified finite
side. -/
def coveredSideEdges (G : SimpleGraph α) (s : Set α)
    (P : Finset (Finset α)) (X : Finset α) : Finset (Sym2 α) :=
  coveredInternalEdges G s P ∩ sideEdgeFinset G X

lemma coveredSideEdges_subset_sideEdgeFinset
    (G : SimpleGraph α) (s : Set α) (P : Finset (Finset α))
    (X : Finset α) :
    coveredSideEdges G s P X ⊆ sideEdgeFinset G X :=
  inter_subset_right

/-- The covered internal edges split between the two sides of the
bipartition. -/
lemma coveredInternalEdges_eq_union_coveredSideEdges
    (G : SimpleGraph α) (s : Set α) (P : Finset (Finset α)) :
    coveredInternalEdges G s P =
      coveredSideEdges G s P s.toFinset ∪
        coveredSideEdges G s P sᶜ.toFinset := by
  classical
  ext e
  have hside := internalEdgeFinset_eq_union_sides G s
  simp only [coveredInternalEdges, coveredSideEdges, mem_filter, mem_inter,
    mem_union]
  constructor
  · rintro ⟨heInternal, heCovered⟩
    have heSides : e ∈ sideEdgeFinset G s.toFinset ∨
        e ∈ sideEdgeFinset G sᶜ.toFinset := by
      have heInternal' := heInternal
      rw [hside] at heInternal'
      exact mem_union.mp heInternal'
    exact heSides.elim (fun h ↦ Or.inl ⟨⟨heInternal, heCovered⟩, h⟩)
      (fun h ↦ Or.inr ⟨⟨heInternal, heCovered⟩, h⟩)
  · rintro (⟨⟨heInternal, heCovered⟩, _⟩ |
      ⟨⟨heInternal, heCovered⟩, _⟩) <;>
      exact ⟨heInternal, heCovered⟩

lemma coveredSideEdges_disjoint_compl
    (G : SimpleGraph α) (s : Set α) (P : Finset (Finset α)) :
    Disjoint (coveredSideEdges G s P s.toFinset)
      (coveredSideEdges G s P sᶜ.toFinset) := by
  rw [Finset.disjoint_left]
  intro e heS heT
  exact Finset.disjoint_left.mp (sideEdgeFinset_disjoint_compl G s)
    (coveredSideEdges_subset_sideEdgeFinset G s P s.toFinset heS)
    (coveredSideEdges_subset_sideEdgeFinset G s P sᶜ.toFinset heT)

/-- The numbers of covered internal edges on the two sides add to the
number of selected blue cross triangles. -/
lemma card_coveredSideEdges_add_compl
    {G : SimpleGraph α} {s : Set α} {P : Finset (Finset α)}
    (hP : IsInternalCrossPacking G s P) :
    (coveredSideEdges G s P s.toFinset).card +
      (coveredSideEdges G s P sᶜ.toFinset).card = P.card := by
  rw [← card_union_of_disjoint (coveredSideEdges_disjoint_compl G s P),
    ← coveredInternalEdges_eq_union_coveredSideEdges,
    card_coveredInternalEdges_eq_card hP]

/-- Both endpoints of an edge covered by a triangle of `P` occur in the
vertex support of `P`. -/
lemma coveredInternalEdge_toFinset_subset_packingVertices
    {G : SimpleGraph α} {s : Set α} {P : Finset (Finset α)}
    {e : Sym2 α} (he : e ∈ coveredInternalEdges G s P) :
    e.toFinset ⊆ packingVertices P := by
  rcases mem_filter.mp he with ⟨_heInternal, t, htP, het⟩
  intro v hve
  apply mem_packingVertices.mpr
  refine ⟨t, htP, ?_⟩
  exact (mem_sym2_iff.mp het) v (by simpa using hve)

/-- Claim 4.3 side bookkeeping.  After deleting the packing support and a
distinguished uncovered internal edge, the remaining edges, the covered
edges in this side, and the distinguished edge form three disjoint families
inside the side-edge set. -/
lemma card_edgesInsideOutside_add_coveredSideEdges_add_one_le
    {G : SimpleGraph α} {s : Set α} {P : Finset (Finset α)}
    {X : Finset α} {e : Sym2 α}
    (heX : e ∈ sideEdgeFinset G X)
    (heUncovered : e ∉ coveredInternalEdges G s P) :
    let D := packingVertices P ∪ e.toFinset
    (edgesInsideOutside G X D).card +
        (coveredSideEdges G s P X).card + 1 ≤
      (sideEdgeFinset G X).card := by
  classical
  intro D
  let E := edgesInsideOutside G X D
  let C := coveredSideEdges G s P X
  have hEsub : E ⊆ sideEdgeFinset G X := by
    intro q hq
    rcases mem_filter.mp hq with ⟨hqG, hqSub⟩
    exact mem_filter.mpr ⟨hqG, hqSub.trans sdiff_subset⟩
  have hCsub : C ⊆ sideEdgeFinset G X :=
    coveredSideEdges_subset_sideEdgeFinset G s P X
  have heC : e ∉ C := by
    intro he
    exact heUncovered (mem_inter.mp he).1
  have hCE : Disjoint C E := by
    rw [Finset.disjoint_left]
    intro q hqC hqE
    have hqSupport := coveredInternalEdge_toFinset_subset_packingVertices
      (mem_inter.mp hqC).1
    have hqAvoid := (mem_filter.mp hqE).2
    have hvq : q.out.1 ∈ q.toFinset := by
      simpa using Sym2.out_fst_mem q
    have hvSupport : q.out.1 ∈ packingVertices P := hqSupport hvq
    have hvAvoid : q.out.1 ∈ X \ D := hqAvoid hvq
    exact (mem_sdiff.mp hvAvoid).2 (mem_union_left _ hvSupport)
  have heE : e ∉ E := by
    intro heE
    have hAvoid := (mem_filter.mp heE).2
    have hv : e.out.1 ∈ e.toFinset := by
      simpa using Sym2.out_fst_mem e
    have hvAvoid : e.out.1 ∈ X \ D := hAvoid hv
    exact (mem_sdiff.mp hvAvoid).2 (mem_union_right _ hv)
  have hdisj : Disjoint ({e} ∪ C) E := by
    rw [Finset.disjoint_left]
    intro q hq hqE
    rcases mem_union.mp hq with hqe | hqC
    · have hqe' : q = e := by simpa using hqe
      subst q
      exact heE hqE
    · exact Finset.disjoint_left.mp hCE hqC hqE
  have hunionSub : {e} ∪ C ∪ E ⊆ sideEdgeFinset G X := by
    intro q hq
    rcases mem_union.mp hq with hq | hqE
    · rcases mem_union.mp hq with hqe | hqC
      · have hqe' : q = e := by simpa using hqe
        subst q
        exact heX
      · exact hCsub hqC
    · exact hEsub hqE
  have hcard := card_le_card hunionSub
  rw [card_union_of_disjoint hdisj,
    card_union_of_disjoint (Finset.disjoint_singleton_left.mpr heC)] at hcard
  simp only [card_singleton] at hcard
  change E.card + C.card + 1 ≤ (sideEdgeFinset G X).card
  omega

/-- Summed endpoint-cover estimate in Claim 4.3.  If one internal edge is
left uncovered on each side, then after deleting the packing support and
those two edges, the two chosen endpoint covers together use at most
`k - m - 2` vertices.  It is stated without subtraction so no side
condition on natural subtraction is hidden. -/
lemma card_chosenEndpointCovers_add_card_packing_add_two_le_internal
    {G : SimpleGraph α} {s : Set α} {P : Finset (Finset α)}
    {e₁ e₂ : Sym2 α}
    (hP : IsInternalCrossPacking G s P)
    (he₁ : e₁ ∈ sideEdgeFinset G s.toFinset)
    (he₂ : e₂ ∈ sideEdgeFinset G sᶜ.toFinset)
    (he₁Uncovered : e₁ ∉ coveredInternalEdges G s P)
    (he₂Uncovered : e₂ ∉ coveredInternalEdges G s P) :
    let D₁ := packingVertices P ∪ e₁.toFinset
    let D₂ := packingVertices P ∪ e₂.toFinset
    let C₁ := chosenEndpointCover (edgesInsideOutside G s.toFinset D₁)
    let C₂ := chosenEndpointCover (edgesInsideOutside G sᶜ.toFinset D₂)
    C₁.card + C₂.card + P.card + 2 ≤
      (internalEdgeFinset G s).card := by
  classical
  intro D₁ D₂ C₁ C₂
  let E₁ := edgesInsideOutside G s.toFinset D₁
  let E₂ := edgesInsideOutside G sᶜ.toFinset D₂
  let K₁ := coveredSideEdges G s P s.toFinset
  let K₂ := coveredSideEdges G s P sᶜ.toFinset
  have hbook₁ : E₁.card + K₁.card + 1 ≤
      (sideEdgeFinset G s.toFinset).card := by
    exact card_edgesInsideOutside_add_coveredSideEdges_add_one_le
      he₁ he₁Uncovered
  have hbook₂ : E₂.card + K₂.card + 1 ≤
      (sideEdgeFinset G sᶜ.toFinset).card := by
    exact card_edgesInsideOutside_add_coveredSideEdges_add_one_le
      he₂ he₂Uncovered
  have hC₁ : C₁.card ≤ E₁.card := card_chosenEndpointCover_le E₁
  have hC₂ : C₂.card ≤ E₂.card := card_chosenEndpointCover_le E₂
  have hcovered : K₁.card + K₂.card = P.card :=
    card_coveredSideEdges_add_compl hP
  have hinternal :
      (internalEdgeFinset G s).card =
        (sideEdgeFinset G s.toFinset).card +
          (sideEdgeFinset G sᶜ.toFinset).card := by
    rw [internalEdgeFinset_eq_union_sides,
      card_union_of_disjoint (sideEdgeFinset_disjoint_compl G s)]
  omega

/-- Elementary finite-set accounting: a set is partitioned between the
twice-deleted remainder, the part of the first deletion set lying in it,
and the second deletion set. -/
lemma card_le_card_sdiff_sdiff_add_card_filter_add_card
    (X D C : Finset α) :
    X.card ≤ ((X \ D) \ C).card +
      (D.filter fun x ↦ x ∈ X).card + C.card := by
  classical
  let R := (X \ D) \ C
  let F := D.filter fun x ↦ x ∈ X
  have hsub : X ⊆ R ∪ F ∪ C := by
    intro x hxX
    by_cases hxD : x ∈ D
    · exact mem_union_left _ (mem_union_right _ (mem_filter.mpr ⟨hxD, hxX⟩))
    · by_cases hxC : x ∈ C
      · exact mem_union_right _ hxC
      · exact mem_union_left _ (mem_union_left _
          (mem_sdiff.mpr ⟨mem_sdiff.mpr ⟨hxX, hxD⟩, hxC⟩))
  have hcard := card_le_card hsub
  have h₁ := card_union_le R F
  have h₂ := card_union_le (R ∪ F) C
  change X.card ≤ R.card + F.card + C.card
  omega

/-- On both sides together, deleting the blue packing support and the two
uncovered internal edges costs at most `3m + 4` vertices.  The endpoint
covers are left explicit for the subsequent `k-m-2` substitution. -/
lemma card_sides_le_remainders_add_packingSupport_add_four_add_covers
    {G : SimpleGraph α} {s : Set α} {P : Finset (Finset α)}
    {e₁ e₂ : Sym2 α}
    (he₁ : e₁ ∈ sideEdgeFinset G s.toFinset)
    (he₂ : e₂ ∈ sideEdgeFinset G sᶜ.toFinset) :
    let D₁ := packingVertices P ∪ e₁.toFinset
    let D₂ := packingVertices P ∪ e₂.toFinset
    let C₁ := chosenEndpointCover (edgesInsideOutside G s.toFinset D₁)
    let C₂ := chosenEndpointCover (edgesInsideOutside G sᶜ.toFinset D₂)
    let R₁ := (s.toFinset \ D₁) \ C₁
    let R₂ := (sᶜ.toFinset \ D₂) \ C₂
    Fintype.card α ≤ R₁.card + R₂.card +
      (packingVertices P).card + 4 + C₁.card + C₂.card := by
  classical
  intro D₁ D₂ C₁ C₂ R₁ R₂
  let T₁ := (packingVertices P).filter fun x ↦ x ∈ s.toFinset
  let T₂ := (packingVertices P).filter fun x ↦ x ∈ sᶜ.toFinset
  have he₁G : e₁ ∈ G.edgeFinset := (mem_filter.mp he₁).1
  have he₂G : e₂ ∈ G.edgeFinset := (mem_filter.mp he₂).1
  have he₁card : e₁.toFinset.card = 2 :=
    SimpleGraph.card_toFinset_mem_edgeFinset ⟨e₁, he₁G⟩
  have he₂card : e₂.toFinset.card = 2 :=
    SimpleGraph.card_toFinset_mem_edgeFinset ⟨e₂, he₂G⟩
  have hD₁ : (D₁.filter fun x ↦ x ∈ s.toFinset).card ≤ T₁.card + 2 := by
    have hsub : (D₁.filter fun x ↦ x ∈ s.toFinset) ⊆
        T₁ ∪ e₁.toFinset := by
      intro x hx
      rcases mem_filter.mp hx with ⟨hxD, hxS⟩
      rcases mem_union.mp hxD with hxP | hxe
      · exact mem_union_left _ (mem_filter.mpr ⟨hxP, hxS⟩)
      · exact mem_union_right _ hxe
    have hc := card_le_card hsub
    have hu := card_union_le T₁ e₁.toFinset
    omega
  have hD₂ : (D₂.filter fun x ↦ x ∈ sᶜ.toFinset).card ≤ T₂.card + 2 := by
    have hsub : (D₂.filter fun x ↦ x ∈ sᶜ.toFinset) ⊆
        T₂ ∪ e₂.toFinset := by
      intro x hx
      rcases mem_filter.mp hx with ⟨hxD, hxS⟩
      rcases mem_union.mp hxD with hxP | hxe
      · exact mem_union_left _ (mem_filter.mpr ⟨hxP, hxS⟩)
      · exact mem_union_right _ hxe
    have hc := card_le_card hsub
    have hu := card_union_le T₂ e₂.toFinset
    omega
  have hR₁ := card_le_card_sdiff_sdiff_add_card_filter_add_card
    s.toFinset D₁ C₁
  have hR₂ := card_le_card_sdiff_sdiff_add_card_filter_add_card
    sᶜ.toFinset D₂ C₂
  have hR₁' : s.toFinset.card ≤ R₁.card +
      (D₁.filter fun x ↦ x ∈ s.toFinset).card + C₁.card := by
    simpa only [R₁] using hR₁
  have hR₂' : sᶜ.toFinset.card ≤ R₂.card +
      (D₂.filter fun x ↦ x ∈ sᶜ.toFinset).card + C₂.card := by
    simpa only [R₂] using hR₂
  have hT : T₁.card + T₂.card = (packingVertices P).card := by
    have hT₂ : T₂ = (packingVertices P).filter
        (fun x ↦ ¬ x ∈ s.toFinset) := by
      ext x
      simp [T₂]
    rw [hT₂]
    exact Finset.card_filter_add_card_filter_not _
  have hsides : s.toFinset.card + sᶜ.toFinset.card = Fintype.card α := by
    have h := Set.ncard_add_ncard_compl s
    simpa [Set.ncard_eq_toFinset_card'] using h
  change Fintype.card α ≤ R₁.card + R₂.card +
    (packingVertices P).card + 4 + C₁.card + C₂.card
  omega

/-! ### The numerical conclusion of Proposition 4.2 -/

/-- Exact arithmetic aggregation for Claim 4.3.  The hypotheses correspond,
in order, to: the two remainder counts, the `3m` blue-support bound, the
`k-m-2` endpoint-cover bound, the two lost forbidden-neighbour pairs, and
the four parity losses in the combined red matching construction. -/
lemma claim43_lower_bound_of_card_estimates
    (n k m p c₁ c₂ r₁ r₂ a₁ b₁ a₂ b₂ : ℕ) (r : ℝ)
    (hremainder : n ≤ r₁ + r₂ + p + 4 + c₁ + c₂)
    (hsupport : p ≤ 3 * m)
    (hcovers : c₁ + c₂ + m + 2 ≤ k)
    (hneigh₁ : r₁ ≤ a₁ + b₁ + 2)
    (hneigh₂ : r₂ ≤ a₂ + b₂ + 2)
    (hred : (((a₁ + b₁ + a₂ + b₂ : ℕ) : ℝ)) ≤ 2 * r + 4) :
    (n : ℝ) - 2 * (m : ℝ) - (k : ℝ) - 10 ≤ 2 * r := by
  have hremainderR : (n : ℝ) ≤
      r₁ + r₂ + p + 4 + c₁ + c₂ := by exact_mod_cast hremainder
  have hsupportR : (p : ℝ) ≤ 3 * m := by exact_mod_cast hsupport
  have hcoversR : (c₁ : ℝ) + c₂ + m + 2 ≤ k := by exact_mod_cast hcovers
  have hneigh₁R : (r₁ : ℝ) ≤ a₁ + b₁ + 2 := by exact_mod_cast hneigh₁
  have hneigh₂R : (r₂ : ℝ) ≤ a₂ + b₂ + 2 := by exact_mod_cast hneigh₂
  push_cast at hred
  norm_num at hremainderR hsupportR hcoversR hneigh₁R hneigh₂R hred ⊢
  linarith

/-- A lower-level arithmetic interface for Claim 4.3 after the red matching
construction has already been summarized as a bound on the two remainder
sizes. -/
lemma claim43_lower_bound_of_remainder_bound
    (n k m p c₁ c₂ r₁ r₂ : ℕ) (r : ℝ)
    (hremainder : n ≤ r₁ + r₂ + p + 4 + c₁ + c₂)
    (hsupport : p ≤ 3 * m)
    (hcovers : c₁ + c₂ + m + 2 ≤ k)
    (hredRemainder : (((r₁ + r₂ : ℕ) : ℝ)) ≤ 2 * r + 8) :
    (n : ℝ) - 2 * (m : ℝ) - (k : ℝ) - 10 ≤ 2 * r := by
  have hremainderR : (n : ℝ) ≤
      r₁ + r₂ + p + 4 + c₁ + c₂ := by exact_mod_cast hremainder
  have hsupportR : (p : ℝ) ≤ 3 * m := by exact_mod_cast hsupport
  have hcoversR : (c₁ : ℝ) + c₂ + m + 2 ≤ k := by exact_mod_cast hcovers
  push_cast at hredRemainder
  norm_num at hremainderR hsupportR hcoversR hredRemainder ⊢
  linarith

/-- The paper's displayed covered-size calculation implies its master
inequality (2).  All graph theory and weighted decompositions are isolated
in the single lower-bound hypothesis; this lemma performs the exact
normalization against `pack(G) ≤ n(n-1)/4`. -/
lemma proposition42_master_inequality_of_coveredSize
    {n k m : ℕ} {G : SimpleGraph (Fin n)} (x r : ℝ)
    (hcovered : HasFractionalCoveredSizeAtLeast G
      ((n : ℝ) ^ 2 / 4 - (n : ℝ) / 2 + x ^ 2 - (k : ℝ) +
        3 * (m : ℝ) + 2 * r))
    (hupper : FractionalCoveredSizeAtMost G
      ((n : ℝ) * ((n : ℝ) - 1) / 4)) :
    2 * r - (n : ℝ) / 4 + 3 * (m : ℝ) - (k : ℝ) + x ^ 2 ≤ 0 := by
  obtain ⟨wG, wGc, hwG, hwGc, hsize⟩ := hcovered
  have hbound := hupper wG wGc hwG hwGc
  nlinarith

/-- Arithmetic audit of the corrected, capacity-safe truncation in
Proposition 4.2.  Corollary 2.12 applies on both sides if the retained red
cross weight is at most `n / 2 - x - 4 - k` (the printed proof has `m` in
place of `k`).  If the master inequality does not already contradict this
truncation, all parameters are forced to the single boundary case
`n = 24`, `k = 3`, `m = 0`, `x = 1`. -/
lemma proposition42_safe_truncation_boundary
    (n k m : ℕ) (x : ℝ) (hn : 22 ≤ n) (hk : k ≤ n / 8)
    (hmk : m < k)
    (hmaster :
      2 * ((n : ℝ) / 2 - x - 4 - (k : ℝ)) - (n : ℝ) / 4 +
          3 * (m : ℝ) - (k : ℝ) + x ^ 2 ≤ 0) :
    n = 24 ∧ k = 3 ∧ m = 0 ∧ x = 1 := by
  have hk8 : 8 * k ≤ n := by omega
  have hnR : (22 : ℝ) ≤ n := by exact_mod_cast hn
  have hmR : (0 : ℝ) ≤ m := by positivity
  have hcoarseR : (n : ℝ) ≤ 12 + 4 * (k : ℝ) := by
    nlinarith [sq_nonneg (x - 1)]
  have hcoarse : n ≤ 12 + 4 * k := by exact_mod_cast hcoarseR
  have hn24 : n = 24 := by omega
  have hk3 : k = 3 := by omega
  subst n
  subst k
  have hm0R : (m : ℝ) = 0 := by
    norm_num at hmaster
    nlinarith [sq_nonneg (x - 1)]
  have hm0 : m = 0 := by exact_mod_cast hm0R
  subst m
  have hx : x = 1 := by
    norm_num at hmaster
    nlinarith [sq_nonneg (x - 1)]
  exact ⟨rfl, rfl, rfl, hx⟩

/-- The arithmetic at the end of Proposition 4.2.  The first alternative is
Claim 4.3.  The other two are Claim 4.4 split according as `k ≥ 3` or
`k ≤ 2`, so that the indicator term in the paper is represented exactly.
Together with the master inequality (2), each case is impossible for
`n ≥ 22` and `k ≤ n / 8`. -/
lemma proposition42_master_inequality_contradiction
    (n k m : ℕ) (x r : ℝ)
    (hn : 22 ≤ n) (hk : k ≤ n / 8)
    (hmaster :
      2 * r - (n : ℝ) / 4 + 3 * (m : ℝ) - (k : ℝ) + x ^ 2 ≤ 0)
    (hlower :
      (n : ℝ) - 2 * (m : ℝ) - (k : ℝ) - 10 ≤ 2 * r ∨
      (3 ≤ k ∧
        (n : ℝ) / 2 - x - 3 * (m : ℝ) - 2 ≤ 2 * r) ∨
      (k ≤ 2 ∧
        (n : ℝ) / 2 - x - 3 * (m : ℝ) - 3 ≤ 2 * r)) :
    False := by
  have h8k : 8 * k ≤ n := by omega
  have hnR : (22 : ℝ) ≤ n := by exact_mod_cast hn
  have h8kR : (8 : ℝ) * k ≤ n := by exact_mod_cast h8k
  rcases hlower with hboth | hrest
  · have hmR : (0 : ℝ) ≤ m := by positivity
    nlinarith [sq_nonneg x]
  · rcases hrest with ⟨hk3, hone⟩ | ⟨hk2, hone⟩
    · nlinarith [sq_nonneg (x - (1 / 2 : ℝ))]
    · have hkR : (k : ℝ) ≤ 2 := by exact_mod_cast hk2
      nlinarith [sq_nonneg (x - (1 / 2 : ℝ))]

/-- Final contradiction wrapper for Proposition 4.2.  Once the maximal
blue family leaves an internal edge uncovered, the weighted construction
supplies `hcovered`, while Claims 4.3/4.4 supply one of the three alternatives
in `hlower`; no further numerical argument remains. -/
lemma proposition42_contradiction_of_coveredSize_and_claims
    {n k m : ℕ} {G : SimpleGraph (Fin n)} (x r : ℝ)
    (hn : 22 ≤ n) (hk : k ≤ n / 8)
    (hupper : FractionalCoveredSizeAtMost G
      ((n : ℝ) * ((n : ℝ) - 1) / 4))
    (hcovered : HasFractionalCoveredSizeAtLeast G
      ((n : ℝ) ^ 2 / 4 - (n : ℝ) / 2 + x ^ 2 - (k : ℝ) +
        3 * (m : ℝ) + 2 * r))
    (hlower :
      (n : ℝ) - 2 * (m : ℝ) - (k : ℝ) - 10 ≤ 2 * r ∨
      (3 ≤ k ∧
        (n : ℝ) / 2 - x - 3 * (m : ℝ) - 2 ≤ 2 * r) ∨
      (k ≤ 2 ∧
        (n : ℝ) / 2 - x - 3 * (m : ℝ) - 3 ≤ 2 * r)) :
    False := by
  exact proposition42_master_inequality_contradiction n k m x r hn hk
    (proposition42_master_inequality_of_coveredSize x r hcovered hupper) hlower

/-- Integral form of Proposition 4.2.  The last two fields record that every
internal edge is covered and that every selected cross triangle accounts for
exactly one such edge; `card_eq` is retained explicitly as the convenient
certificate field checked by the finite construction. -/
def IsInternalEdgeCoveringCrossPacking (G : SimpleGraph α) (s : Set α)
    (P : Finset (Finset α)) : Prop :=
  (∀ t ∈ P, G.IsNClique 3 t) ∧ EdgeDisjoint P ∧
    (∀ e ∈ internalEdgeFinset G s, ∃ t ∈ P, e ∈ t.sym2) ∧
    (∀ t ∈ P,
      ((internalEdgeFinset G s).filter fun e ↦ e ∈ t.sym2).card = 1) ∧
    P.card = (internalEdgeFinset G s).card

/-- Once the maximal family covers all internal edges, all fields of the
explicit Proposition 4.2 certificate follow automatically. -/
lemma isInternalEdgeCoveringCrossPacking_of_covers
    {G : SimpleGraph α} {s : Set α} {P : Finset (Finset α)}
    (hP : IsInternalCrossPacking G s P)
    (hcover : ∀ e ∈ internalEdgeFinset G s, ∃ t ∈ P, e ∈ t.sym2) :
    IsInternalEdgeCoveringCrossPacking G s P := by
  have hcovered : coveredInternalEdges G s P = internalEdgeFinset G s := by
    apply Subset.antisymm
    · intro e he
      exact (mem_filter.mp he).1
    · intro e he
      exact mem_filter.mpr ⟨he, hcover e he⟩
  refine ⟨fun t htP ↦ (mem_internalCrossTriangles.mp (hP.1 htP)).1,
    hP.2, hcover, fun t htP ↦
      (mem_internalCrossTriangles.mp (hP.1 htP)).2, ?_⟩
  rw [← card_coveredInternalEdges_eq_card hP, hcovered]

/-- A matching between the two sides of a proposed bipartition.  The first
field says every forbidden pair is cross-part, while the second says no two
forbidden pairs share a vertex.  Proposition 4.2 in the paper is uniform in
such a matching. -/
def IsCrossMatching (s : Set α) (M : Finset (Sym2 α)) : Prop :=
  (∀ e ∈ M, ¬ SameSide s e) ∧
    (M : Set (Sym2 α)).PairwiseDisjoint fun e ↦ e.toFinset

@[simp] lemma isCrossMatching_set_compl (s : Set α)
    (M : Finset (Sym2 α)) :
    IsCrossMatching sᶜ M ↔ IsCrossMatching s M := by
  simp only [IsCrossMatching, sameSide_set_compl]

/-- A vertex is incident to at most one pair of a cross matching. -/
lemma IsCrossMatching.unique_other_endpoint
    {s : Set α} {M : Finset (Sym2 α)} (hM : IsCrossMatching s M)
    {a b c : α} (hab : s(a, b) ∈ M) (hac : s(a, c) ∈ M) : b = c := by
  classical
  by_cases heq : s(a, b) = s(a, c)
  · rcases Sym2.eq_iff.mp heq with ⟨_haa, hbc⟩ | ⟨hac', hba⟩
    · exact hbc
    · exact hba.trans hac'
  · have hdis : Disjoint s(a, b).toFinset s(a, c).toFinset :=
      hM.2 hab hac heq
    have ha1 : a ∈ s(a, b).toFinset := by simp
    have ha2 : a ∈ s(a, c).toFinset := by simp
    exact (Finset.disjoint_left.mp hdis ha1 ha2).elim

/-- Forbidden partners of one vertex, restricted to a finite test set. -/
def forbiddenNeighborFinset (M : Finset (Sym2 α)) (a : α)
    (U : Finset α) : Finset α :=
  U.filter fun x ↦ s(a, x) ∈ M

lemma card_forbiddenNeighborFinset_le_one
    {s : Set α} {M : Finset (Sym2 α)} (hM : IsCrossMatching s M)
    (a : α) (U : Finset α) :
    (forbiddenNeighborFinset M a U).card ≤ 1 := by
  classical
  rw [card_le_one]
  intro b hb c hc
  exact hM.unique_other_endpoint (mem_filter.mp hb).2 (mem_filter.mp hc).2

/-- Red neighbors of `a` inside a displayed finite set, when `G` is the
blue graph. -/
def redNeighborFinset (G : SimpleGraph α) (a : α)
    (U : Finset α) : Finset α :=
  U.filter fun x ↦ Gᶜ.Adj a x

/-- The counting core behind the estimates
`|A_i| + |B_i| ≥ |U_i| - 2` in Claims 4.3 and 4.4.  If `a,b` have no
common blue neighbor in `G \ M`, their successive red neighborhoods cover
`U` except for at most the one forbidden partner of `a` and the one
forbidden partner of `b`. -/
lemma redNeighborFinset_add_card_ge_of_no_common_deleteEdges_neighbor
    {s : Set α} {M : Finset (Sym2 α)} (hM : IsCrossMatching s M)
    (G : SimpleGraph α) (U : Finset α) (a b : α)
    (haU : a ∉ U) (hbU : b ∉ U)
    (hcommon : ∀ x ∈ U,
      ¬ ((G.deleteEdges (M : Set (Sym2 α))).Adj a x ∧
        (G.deleteEdges (M : Set (Sym2 α))).Adj b x)) :
    let A := redNeighborFinset G a U
    let B := redNeighborFinset G b (U \ A)
    U.card ≤ A.card + B.card + 2 := by
  classical
  intro A B
  let Fa := forbiddenNeighborFinset M a U
  let Fb := forbiddenNeighborFinset M b U
  have hFa : Fa.card ≤ 1 := card_forbiddenNeighborFinset_le_one hM a U
  have hFb : Fb.card ≤ 1 := card_forbiddenNeighborFinset_le_one hM b U
  have hsub : U ⊆ A ∪ B ∪ Fa ∪ Fb := by
    intro x hxU
    by_cases hxA : x ∈ A
    · exact mem_union_left _ (mem_union_left _ (mem_union_left _ hxA))
    have hnotRedA : ¬ Gᶜ.Adj a x := by
      intro hred
      exact hxA (mem_filter.mpr ⟨hxU, hred⟩)
    have hax : a ≠ x := by
      intro hax
      subst x
      exact haU hxU
    have hblueA : G.Adj a x := by
      by_contra hnot
      exact hnotRedA (by simpa [SimpleGraph.compl_adj, hax] using hnot)
    by_cases hxFa : x ∈ Fa
    · exact mem_union_left _ (mem_union_right _ hxFa)
    have hnotForbidA : s(a, x) ∉ M := by
      intro hforbid
      exact hxFa (mem_filter.mpr ⟨hxU, hforbid⟩)
    have hblueA' : (G.deleteEdges (M : Set (Sym2 α))).Adj a x := by
      simpa [SimpleGraph.deleteEdges_adj, hnotForbidA] using hblueA
    by_cases hxFb : x ∈ Fb
    · exact mem_union_right _ hxFb
    have hnotForbidB : s(b, x) ∉ M := by
      intro hforbid
      exact hxFb (mem_filter.mpr ⟨hxU, hforbid⟩)
    have hbx : b ≠ x := by
      intro hbx
      subst x
      exact hbU hxU
    have hnotBlueB : ¬ G.Adj b x := by
      intro hblueB
      have hblueB' : (G.deleteEdges (M : Set (Sym2 α))).Adj b x := by
        simpa [SimpleGraph.deleteEdges_adj, hnotForbidB] using hblueB
      exact hcommon x hxU ⟨hblueA', hblueB'⟩
    have hredB : Gᶜ.Adj b x := by
      simpa [SimpleGraph.compl_adj, hbx] using hnotBlueB
    have hxB : x ∈ B := by
      exact mem_filter.mpr ⟨mem_sdiff.mpr ⟨hxU, hxA⟩, hredB⟩
    exact mem_union_left _ (mem_union_left _ (mem_union_right _ hxB))
  have hU := card_le_card hsub
  have h1 := card_union_le A B
  have h2 := card_union_le (A ∪ B) Fa
  have h3 := card_union_le (A ∪ B ∪ Fa) Fb
  omega

/-- One-side graph-theoretic package in Claim 4.3.  The edge `f` is the
uncovered edge on the side currently being processed and is deleted from
the red-clique remainder.  The edge `s(a,b)` is an uncovered blue edge on
the opposite side; maximality says its endpoints have no common unused
blue neighbour in the current remainder.  Successive red neighbourhoods
therefore lose at most the two forbidden matching partners. -/
lemma exists_claim43_side_cliques
    {G : SimpleGraph α} {u : Set α} {M : Finset (Sym2 α)}
    (hM : IsCrossMatching u M)
    {P : Finset (Finset α)}
    (hP : IsInternalCrossPacking
      (G.deleteEdges (M : Set (Sym2 α))) u P)
    (hmax : ∀ Q : Finset (Finset α),
      IsInternalCrossPacking (G.deleteEdges (M : Set (Sym2 α))) u Q →
        Q.card ≤ P.card)
    {f : Sym2 α} {a b : α}
    (habInternal : s(a, b) ∈ internalEdgeFinset
      (G.deleteEdges (M : Set (Sym2 α))) u)
    (habUncovered : s(a, b) ∉ coveredInternalEdges
      (G.deleteEdges (M : Set (Sym2 α))) u P)
    (haOpp : a ∉ u) (hbOpp : b ∉ u) :
    let D := packingVertices P ∪ f.toFinset
    let C := chosenEndpointCover (edgesInsideOutside G u.toFinset D)
    let R := (u.toFinset \ D) \ C
    ∃ A B : Finset α,
      Gᶜ.IsClique (A : Set α) ∧ Gᶜ.IsClique (B : Set α) ∧
      Disjoint A B ∧
      (∀ x ∈ A, x ∈ u) ∧ (∀ x ∈ B, x ∈ u) ∧
      (∀ x ∈ A, Gᶜ.Adj a x) ∧ (∀ x ∈ B, Gᶜ.Adj b x) ∧
      A ∪ B ⊆ R ∧ Disjoint (A ∪ B) f.toFinset ∧
      R.card ≤ A.card + B.card + 2 := by
  classical
  intro D C R
  let A := redNeighborFinset G a R
  let B := redNeighborFinset G b (R \ A)
  have hRsub : ∀ x ∈ R, x ∈ u := by
    intro x hx
    simpa using (mem_sdiff.mp (mem_sdiff.mp hx).1).1
  have hRclique : Gᶜ.IsClique (R : Set α) := by
    exact SimpleGraph.induce_eq_top.mp (compl_induce_remainder_eq_top
      G u.toFinset D)
  have hAsub : A ⊆ R := fun x hx ↦ (mem_filter.mp hx).1
  have hBsub : B ⊆ R := fun x hx ↦
    (mem_sdiff.mp (mem_filter.mp hx).1).1
  have hAclique : Gᶜ.IsClique (A : Set α) := by
    apply hRclique.subset
    intro x hx
    exact hAsub hx
  have hBclique : Gᶜ.IsClique (B : Set α) := by
    apply hRclique.subset
    intro x hx
    exact hBsub hx
  have hAB : Disjoint A B := by
    rw [Finset.disjoint_left]
    intro x hxA hxB
    exact (mem_sdiff.mp (mem_filter.mp hxB).1).2 hxA
  have heP : ∀ t ∈ P, s(a, b) ∉ t.sym2 := by
    intro t htP het
    exact habUncovered (mem_filter.mpr
      ⟨habInternal, ⟨t, htP, het⟩⟩)
  have hcommon : ∀ x ∈ R,
      ¬ ((G.deleteEdges (M : Set (Sym2 α))).Adj a x ∧
        (G.deleteEdges (M : Set (Sym2 α))).Adj b x) := by
    intro x hxR
    have hxu : x ∈ u := hRsub x hxR
    have hxunused : x ∉ packingVertices P := by
      intro hxP
      exact (mem_sdiff.mp (mem_sdiff.mp hxR).1).2
        (mem_union_left _ hxP)
    exact maximum_internalCrossPacking_no_common_unused_opposite_neighbor
      hP hmax habInternal heP
        (by simp [hxu, haOpp]) hxunused
  have haR : a ∉ R := fun haR ↦ haOpp (hRsub a haR)
  have hbR : b ∉ R := fun hbR ↦ hbOpp (hRsub b hbR)
  have hcount := redNeighborFinset_add_card_ge_of_no_common_deleteEdges_neighbor
    hM G R a b haR hbR hcommon
  have havoid : Disjoint (A ∪ B) f.toFinset := by
    rw [Finset.disjoint_left]
    intro x hxAB hxf
    have hxR : x ∈ R := union_subset hAsub hBsub hxAB
    have hxnotD : x ∉ D := (mem_sdiff.mp (mem_sdiff.mp hxR).1).2
    exact hxnotD (mem_union_right _ hxf)
  refine ⟨A, B, hAclique, hBclique, hAB,
    fun x hx ↦ hRsub x (hAsub hx),
    fun x hx ↦ hRsub x (hBsub hx), ?_, ?_, ?_, ?_, ?_⟩
  · intro x hx
    exact (mem_filter.mp hx).2
  · intro x hx
    exact (mem_filter.mp hx).2
  · exact union_subset hAsub hBsub
  · exact havoid
  · exact hcount

@[simp] lemma isCrossMatching_empty (s : Set α) :
    IsCrossMatching s ∅ := by
  simp [IsCrossMatching]

/-- Deleting cross pairs does not delete an edge internal to either side. -/
lemma internalEdgeFinset_deleteEdges_of_cross
    (G : SimpleGraph α) (s : Set α) (M : Finset (Sym2 α))
    (hM : ∀ e ∈ M, ¬ SameSide s e) :
    internalEdgeFinset (G.deleteEdges (M : Set (Sym2 α))) s =
      internalEdgeFinset G s := by
  ext e
  simp only [internalEdgeFinset, mem_filter,
    SimpleGraph.edgeFinset_deleteEdges, mem_sdiff]
  constructor
  · rintro ⟨⟨heG, _heM⟩, heSide⟩
    exact ⟨heG, heSide⟩
  · rintro ⟨heG, heSide⟩
    refine ⟨⟨heG, ?_⟩, heSide⟩
    intro heM
    exact hM e heM heSide

lemma coveredInternalEdges_deleteEdges_of_cross
    (G : SimpleGraph α) (s : Set α) (M : Finset (Sym2 α))
    (P : Finset (Finset α))
    (hM : ∀ e ∈ M, ¬ SameSide s e) :
    coveredInternalEdges (G.deleteEdges (M : Set (Sym2 α))) s P =
      coveredInternalEdges G s P := by
  unfold coveredInternalEdges
  rw [internalEdgeFinset_deleteEdges_of_cross G s M hM]

/-- A cross packing after deleting cross pairs is still a cross packing in
the original graph. -/
lemma IsInternalCrossPacking.of_deleteEdges_cross
    {G : SimpleGraph α} {s : Set α} {M : Finset (Sym2 α)}
    {P : Finset (Finset α)}
    (hM : ∀ e ∈ M, ¬ SameSide s e)
    (hP : IsInternalCrossPacking
      (G.deleteEdges (M : Set (Sym2 α))) s P) :
    IsInternalCrossPacking G s P := by
  refine ⟨?_, hP.2⟩
  intro t htP
  have ht := mem_internalCrossTriangles.mp (hP.1 htP)
  apply mem_internalCrossTriangles.mpr
  refine ⟨ht.1.mono (G.deleteEdges_le _), ?_⟩
  rw [← internalEdgeFinset_deleteEdges_of_cross G s M hM]
  exact ht.2

lemma disjoint_fourStar_envelopes_of_cross_sides
    {s : Set α} {U₁ U₂ : Finset α} {z₁ w₁ z₂ w₂ : α}
    (hU₁s : ∀ x ∈ U₁, x ∈ s)
    (hU₂s : ∀ x ∈ U₂, x ∉ s)
    (hU₁E₂ : Disjoint U₁ {z₂, w₂})
    (hE₁U₂ : Disjoint {z₁, w₁} U₂)
    (hz₁ : z₁ ∉ s) (hw₁ : w₁ ∉ s)
    (hz₂ : z₂ ∈ s) (hw₂ : w₂ ∈ s) :
    Disjoint (U₁ ∪ {z₁, w₁}) (U₂ ∪ {z₂, w₂}) := by
  rw [Finset.disjoint_left]
  intro x hx₁ hx₂
  rcases mem_union.mp hx₁ with hxU₁ | hxE₁
  · rcases mem_union.mp hx₂ with hxU₂ | hxE₂
    · exact hU₂s x hxU₂ (hU₁s x hxU₁)
    · exact Finset.disjoint_left.mp hU₁E₂ hxU₁ hxE₂
  · rcases mem_union.mp hx₂ with hxU₂ | hxE₂
    · exact Finset.disjoint_left.mp hE₁U₂ hxE₁ hxU₂
    · have hxns : x ∉ s := by
        rcases mem_insert.mp hxE₁ with rfl | hx
        · exact hz₁
        · have hxw : x = w₁ := by simpa using hx
          subst x
          exact hw₁
      have hxs : x ∈ s := by
        rcases mem_insert.mp hxE₂ with rfl | hx
        · exact hz₂
        · have hxw : x = w₂ := by simpa using hx
          subst x
          exact hw₂
      exact hxns hxs

/-- Kernel-sized red-matching half of Claim 4.3.  It combines the two
one-side clique/neighbour estimates into the single fractional red packing
and records only the resulting bound on the two remainder sizes. -/
lemma claim43_red_remainders_bound
    {G : SimpleGraph α} {s : Set α}
    {A₁ B₁ A₂ B₂ : Finset α} {z₁ w₁ z₂ w₂ : α}
    {weight : Finset α → ℝ} {r₁ r₂ : ℕ}
    (hmax : ∀ q : Finset α → ℝ, IsFractionalInternalCrossPacking G s q →
      fractionalSize G q ≤ fractionalSize G weight)
    (hA₁ : G.IsClique (A₁ : Set α)) (hB₁ : G.IsClique (B₁ : Set α))
    (hA₂ : G.IsClique (A₂ : Set α)) (hB₂ : G.IsClique (B₂ : Set α))
    (hAB₁ : Disjoint A₁ B₁) (hAB₂ : Disjoint A₂ B₂)
    (hA₁s : ∀ x ∈ A₁, x ∈ s) (hB₁s : ∀ x ∈ B₁, x ∈ s)
    (hA₂s : ∀ x ∈ A₂, x ∈ sᶜ) (hB₂s : ∀ x ∈ B₂, x ∈ sᶜ)
    (hz₁ : z₁ ∉ s) (hw₁ : w₁ ∉ s)
    (hz₂ : z₂ ∈ s) (hw₂ : w₂ ∈ s)
    (hzw₁ : z₁ ≠ w₁) (hzw₂ : z₂ ≠ w₂)
    (hzA₁ : ∀ x ∈ A₁, G.Adj z₁ x)
    (hwB₁ : ∀ x ∈ B₁, G.Adj w₁ x)
    (hzA₂ : ∀ x ∈ A₂, G.Adj z₂ x)
    (hwB₂ : ∀ x ∈ B₂, G.Adj w₂ x)
    (havoid₁ : Disjoint (A₁ ∪ B₁) {z₂, w₂})
    (havoid₂ : Disjoint {z₁, w₁} (A₂ ∪ B₂))
    (hcount₁ : r₁ ≤ A₁.card + B₁.card + 2)
    (hcount₂ : r₂ ≤ A₂.card + B₂.card + 2) :
    (((r₁ + r₂ : ℕ) : ℝ)) ≤ 2 * fractionalSize G weight + 8 := by
  have hbase₁ : ∀ x ∈ A₁ ∪ B₁, x ∈ s := by
    intro x hx
    rcases mem_union.mp hx with hxA | hxB
    · exact hA₁s x hxA
    · exact hB₁s x hxB
  have hbase₂ : ∀ x ∈ A₂ ∪ B₂, x ∉ s := by
    intro x hx
    rcases mem_union.mp hx with hxA | hxB
    · simpa using hA₂s x hxA
    · simpa using hB₂s x hxB
  have henv : Disjoint (A₁ ∪ B₁ ∪ {z₁, w₁})
      (A₂ ∪ B₂ ∪ {z₂, w₂}) :=
    disjoint_fourStar_envelopes_of_cross_sides hbase₁ hbase₂
      havoid₁ havoid₂ hz₁ hw₁ hz₂ hw₂
  have hred := fourStarClique_card_le_maximal_fractionalInternalCrossPacking
    hmax hA₁ hB₁ hA₂ hB₂ hAB₁ hAB₂ hA₁s hB₁s hA₂s hB₂s
    hz₁ hw₁ (by simpa using hz₂) (by simpa using hw₂)
    hzw₁ hzw₂ hzA₁ hwB₁ hzA₂ hwB₂ henv
  have hcounts : r₁ + r₂ ≤
      A₁.card + B₁.card + A₂.card + B₂.card + 4 := by omega
  have hcountsR : ((r₁ + r₂ : ℕ) : ℝ) ≤
      ((A₁.card + B₁.card + A₂.card + B₂.card + 4 : ℕ) : ℝ) := by
    exact_mod_cast hcounts
  push_cast at hcountsR hred ⊢
  linarith

/- Staged Claim 4.3 assembly; this is being split into kernel-sized helper
declarations below so no declaration exceeds the default heartbeat budget.

/-- Claim 4.3 of Proposition 4.2, including the arbitrary forbidden cross
matching.  If a maximum blue cross packing leaves an internal edge
uncovered on both sides, then the maximum fractional red cross packing has
the lower bound used in the final contradiction. -/
theorem proposition42_claim43_both_sides_uncovered
    {G : SimpleGraph α} {s : Set α} {M : Finset (Sym2 α)}
    (hM : IsCrossMatching s M)
    {P : Finset (Finset α)}
    (hP : IsInternalCrossPacking
      (G.deleteEdges (M : Set (Sym2 α))) s P)
    (hPmax : ∀ Q : Finset (Finset α),
      IsInternalCrossPacking (G.deleteEdges (M : Set (Sym2 α))) s Q →
        Q.card ≤ P.card)
    {a₁ b₁ a₂ b₂ : α}
    (he₁ : s(a₁, b₁) ∈ sideEdgeFinset G s.toFinset)
    (he₂ : s(a₂, b₂) ∈ sideEdgeFinset G sᶜ.toFinset)
    (he₁Uncovered : s(a₁, b₁) ∉ coveredInternalEdges
      (G.deleteEdges (M : Set (Sym2 α))) s P)
    (he₂Uncovered : s(a₂, b₂) ∉ coveredInternalEdges
      (G.deleteEdges (M : Set (Sym2 α))) s P)
    {w : Finset α → ℝ}
    (hwmax : ∀ q : Finset α → ℝ,
      IsFractionalInternalCrossPacking Gᶜ s q →
        fractionalSize Gᶜ q ≤ fractionalSize Gᶜ w) :
    (Fintype.card α : ℝ) - 2 * (P.card : ℝ) -
        ((internalEdgeFinset G s).card : ℝ) - 10 ≤
      2 * fractionalSize Gᶜ w := by
  classical
  let e₁ : Sym2 α := s(a₁, b₁)
  let e₂ : Sym2 α := s(a₂, b₂)
  let H := G.deleteEdges (M : Set (Sym2 α))
  have he₁G : G.Adj a₁ b₁ := by
    exact SimpleGraph.mem_edgeFinset.mp (mem_filter.mp he₁).1
  have he₂G : G.Adj a₂ b₂ := by
    exact SimpleGraph.mem_edgeFinset.mp (mem_filter.mp he₂).1
  have ha₁s : a₁ ∈ s := by
    have hsub := (mem_filter.mp he₁).2
    simpa using hsub (by simp [e₁])
  have hb₁s : b₁ ∈ s := by
    have hsub := (mem_filter.mp he₁).2
    simpa using hsub (by simp [e₁])
  have ha₂s : a₂ ∉ s := by
    have hsub := (mem_filter.mp he₂).2
    have haPair : a₂ ∈ s(a₂, b₂).toFinset := by simp
    have ha : a₂ ∈ sᶜ.toFinset := hsub haPair
    simpa using ha
  have hb₂s : b₂ ∉ s := by
    have hsub := (mem_filter.mp he₂).2
    have hbPair : b₂ ∈ s(a₂, b₂).toFinset := by simp
    have hb : b₂ ∈ sᶜ.toFinset := hsub hbPair
    simpa using hb
  have he₁Internal : e₁ ∈ internalEdgeFinset H s := by
    have heG : e₁ ∈ internalEdgeFinset G s := by
      rw [internalEdgeFinset_eq_union_sides]
      exact mem_union_left _ he₁
    simpa only [H, internalEdgeFinset_deleteEdges_of_cross G s M hM.1]
      using heG
  have he₂Internal : e₂ ∈ internalEdgeFinset H s := by
    have heG : e₂ ∈ internalEdgeFinset G s := by
      rw [internalEdgeFinset_eq_union_sides]
      exact mem_union_right _ he₂
    simpa only [H, internalEdgeFinset_deleteEdges_of_cross G s M hM.1]
      using heG
  have hP_G : IsInternalCrossPacking G s P :=
    hP.of_deleteEdges_cross hM.1
  have he₁UncoveredG : e₁ ∉ coveredInternalEdges G s P := by
    rw [← coveredInternalEdges_deleteEdges_of_cross G s M P hM.1]
    exact he₁Uncovered
  have he₂UncoveredG : e₂ ∉ coveredInternalEdges G s P := by
    rw [← coveredInternalEdges_deleteEdges_of_cross G s M P hM.1]
    exact he₂Uncovered
  letI : DecidablePred (fun x : α ↦ x ∈ sᶜ) := Classical.decPred _
  let D₁ := packingVertices P ∪ e₁.toFinset
  let D₂ := packingVertices P ∪ e₂.toFinset
  let C₁ := chosenEndpointCover (edgesInsideOutside G s.toFinset D₁)
  let C₂ := chosenEndpointCover (edgesInsideOutside G sᶜ.toFinset D₂)
  let R₁ := (s.toFinset \ D₁) \ C₁
  let R₂ := (sᶜ.toFinset \ D₂) \ C₂
  obtain ⟨A₁, B₁, hA₁, hB₁, hAB₁, hA₁s, hB₁s,
      ha₂A₁, hb₂B₁, hsub₁, havoid₁, hcount₁⟩ :=
    exists_claim43_side_cliques (G := G) (u := s) (M := M) hM
      hP hPmax (f := e₁) (a := a₂) (b := b₂)
      he₂Internal he₂Uncovered ha₂s hb₂s
  have hMcompl : IsCrossMatching sᶜ M :=
    (isCrossMatching_set_compl s M).mpr hM
  have hPcompl : IsInternalCrossPacking H sᶜ P :=
    (isInternalCrossPacking_set_compl_iff H s P).mpr hP
  have hPmaxCompl : ∀ Q : Finset (Finset α),
      IsInternalCrossPacking H sᶜ Q → Q.card ≤ P.card := by
    intro Q hQ
    exact hPmax Q ((isInternalCrossPacking_set_compl_iff H s Q).mp hQ)
  obtain ⟨A₂, B₂, hA₂, hB₂, hAB₂, hA₂s, hB₂s,
      ha₁A₂, hb₁B₂, hsub₂, havoid₂, hcount₂⟩ :=
    exists_claim43_side_cliques (G := G) (u := sᶜ) (M := M) hMcompl
      hPcompl hPmaxCompl (f := e₂) (a := a₁) (b := b₁)
      (by simpa [H] using he₁Internal)
      (by simpa [H] using he₁Uncovered)
      (by simpa using ha₁s) (by simpa using hb₁s)
  have hbase₁s : ∀ x ∈ A₁ ∪ B₁, x ∈ s := by
    intro x hx
    rcases mem_union.mp hx with hxA | hxB
    · exact hA₁s x hxA
    · exact hB₁s x hxB
  have hbase₂s : ∀ x ∈ A₂ ∪ B₂, x ∉ s := by
    intro x hx
    rcases mem_union.mp hx with hxA | hxB
    · simpa using hA₂s x hxA
    · simpa using hB₂s x hxB
  have hno₁ : Disjoint (A₁ ∪ B₁) {a₁, b₁} := by
    simpa [e₁, Sym2.toFinset_mk_eq] using havoid₁
  have hno₂ : Disjoint {a₂, b₂} (A₂ ∪ B₂) := by
    simpa [e₂, Sym2.toFinset_mk_eq] using havoid₂.symm
  have henv : Disjoint (A₁ ∪ B₁ ∪ {a₂, b₂})
      (A₂ ∪ B₂ ∪ {a₁, b₁}) := by
    exact disjoint_fourStar_envelopes_of_cross_sides
      hbase₁s hbase₂s hno₁ hno₂ ha₂s hb₂s ha₁s hb₁s
  have hred := fourStarClique_card_le_maximal_fractionalInternalCrossPacking
    (G := Gᶜ) (s := s) (weight := w)
    hwmax hA₁ hB₁ hA₂ hB₂ hAB₁ hAB₂ hA₁s hB₁s hA₂s hB₂s
    ha₂s hb₂s (by simpa using ha₁s) (by simpa using hb₁s)
    he₂G.ne he₁G.ne ha₂A₁ hb₂B₁ ha₁A₂ hb₁B₂ henv
  have hremainder :=
    card_sides_le_remainders_add_packingSupport_add_four_add_covers
      (G := G) (s := s) (P := P) he₁ he₂
  have hsupport := card_packingVertices_le_three_mul hP_G
  have hcovers :=
    card_chosenEndpointCovers_add_card_packing_add_two_le_internal
      hP_G he₁ he₂ he₁UncoveredG he₂UncoveredG
  have hcount₂' : R₂.card ≤ A₂.card + B₂.card + 2 := by
    simpa only [R₂, D₂, C₂] using hcount₂
  exact claim43_lower_bound_of_card_estimates
    (Fintype.card α) (internalEdgeFinset G s).card P.card
    (packingVertices P).card C₁.card C₂.card R₁.card R₂.card
    A₁.card B₁.card A₂.card B₂.card (fractionalSize Gᶜ w)
    hremainder hsupport hcovers hcount₁ hcount₂' hred
-/

/-- The five numerical quantities passed from the graph-theoretic part of
Claim 4.3 to its short arithmetic conclusion. -/
def Claim43EstimateCertificate (n k m : ℕ) (r : ℝ) : Prop :=
  ∃ p c₁ c₂ r₁ r₂ : ℕ,
    n ≤ r₁ + r₂ + p + 4 + c₁ + c₂ ∧
    p ≤ 3 * m ∧ c₁ + c₂ + m + 2 ≤ k ∧
    (((r₁ + r₂ : ℕ) : ℝ)) ≤ 2 * r + 8

-- Graph-theoretic half of Claim 4.3, isolated from the final linear
-- arithmetic so the declaration remains within the default heartbeat budget.
-- Temporarily staged while the graph-theoretic construction is factored into
-- smaller kernel declarations below.  Keeping this oversized draft out of the
-- environment preserves a buildable checkpoint for downstream modules.
/-
theorem proposition42_claim43_estimateCertificate
    {G : SimpleGraph α} {s : Set α} {M : Finset (Sym2 α)}
    (hM : IsCrossMatching s M)
    {P : Finset (Finset α)}
    (hP : IsInternalCrossPacking
      (G.deleteEdges (M : Set (Sym2 α))) s P)
    (hPmax : ∀ Q : Finset (Finset α),
      IsInternalCrossPacking (G.deleteEdges (M : Set (Sym2 α))) s Q →
        Q.card ≤ P.card)
    {a₁ b₁ a₂ b₂ : α}
    (he₁ : s(a₁, b₁) ∈ sideEdgeFinset G s.toFinset)
    (he₂ : s(a₂, b₂) ∈ sideEdgeFinset G sᶜ.toFinset)
    (he₁Uncovered : s(a₁, b₁) ∉ coveredInternalEdges
      (G.deleteEdges (M : Set (Sym2 α))) s P)
    (he₂Uncovered : s(a₂, b₂) ∉ coveredInternalEdges
      (G.deleteEdges (M : Set (Sym2 α))) s P)
    {w : Finset α → ℝ}
    (hwmax : ∀ q : Finset α → ℝ,
      IsFractionalInternalCrossPacking Gᶜ s q →
        fractionalSize Gᶜ q ≤ fractionalSize Gᶜ w) :
    Claim43EstimateCertificate (Fintype.card α)
      (internalEdgeFinset G s).card P.card (fractionalSize Gᶜ w) := by
  classical
  let e₁ : Sym2 α := s(a₁, b₁)
  let e₂ : Sym2 α := s(a₂, b₂)
  let H := G.deleteEdges (M : Set (Sym2 α))
  have he₁G : G.Adj a₁ b₁ :=
    SimpleGraph.mem_edgeFinset.mp (mem_filter.mp he₁).1
  have he₂G : G.Adj a₂ b₂ :=
    SimpleGraph.mem_edgeFinset.mp (mem_filter.mp he₂).1
  have ha₁s : a₁ ∈ s := by
    have hsub := (mem_filter.mp he₁).2
    have haPair : a₁ ∈ s(a₁, b₁).toFinset := by simp
    simpa using hsub haPair
  have hb₁s : b₁ ∈ s := by
    have hsub := (mem_filter.mp he₁).2
    have hbPair : b₁ ∈ s(a₁, b₁).toFinset := by simp
    simpa using hsub hbPair
  have ha₂s : a₂ ∉ s := by
    have h := (mem_filter.mp he₂).2 (show a₂ ∈ s(a₂, b₂).toFinset by simp)
    simpa using h
  have hb₂s : b₂ ∉ s := by
    have h := (mem_filter.mp he₂).2 (show b₂ ∈ s(a₂, b₂).toFinset by simp)
    simpa using h
  have he₁Internal : e₁ ∈ internalEdgeFinset H s := by
    have heG : e₁ ∈ internalEdgeFinset G s := by
      rw [internalEdgeFinset_eq_union_sides]
      exact mem_union_left _ he₁
    simpa only [H, internalEdgeFinset_deleteEdges_of_cross G s M hM.1]
      using heG
  have he₂Internal : e₂ ∈ internalEdgeFinset H s := by
    have heG : e₂ ∈ internalEdgeFinset G s := by
      rw [internalEdgeFinset_eq_union_sides]
      exact mem_union_right _ he₂
    simpa only [H, internalEdgeFinset_deleteEdges_of_cross G s M hM.1]
      using heG
  have hP_G : IsInternalCrossPacking G s P :=
    hP.of_deleteEdges_cross hM.1
  have he₁UncoveredG : e₁ ∉ coveredInternalEdges G s P := by
    rw [← coveredInternalEdges_deleteEdges_of_cross G s M P hM.1]
    exact he₁Uncovered
  have he₂UncoveredG : e₂ ∉ coveredInternalEdges G s P := by
    rw [← coveredInternalEdges_deleteEdges_of_cross G s M P hM.1]
    exact he₂Uncovered
  letI : DecidablePred (fun x : α ↦ x ∈ sᶜ) := Classical.decPred _
  let D₁ := packingVertices P ∪ e₁.toFinset
  let D₂ := packingVertices P ∪ e₂.toFinset
  let C₁ := chosenEndpointCover (edgesInsideOutside G s.toFinset D₁)
  let C₂ := chosenEndpointCover (edgesInsideOutside G sᶜ.toFinset D₂)
  let R₁ := (s.toFinset \ D₁) \ C₁
  let R₂ := (sᶜ.toFinset \ D₂) \ C₂
  obtain ⟨A₁, B₁, hA₁, hB₁, hAB₁, hA₁s, hB₁s,
      ha₂A₁, hb₂B₁, _hsub₁, havoid₁, hcount₁⟩ :=
    exists_claim43_side_cliques (G := G) (u := s) (M := M) hM
      hP hPmax (f := e₁) (a := a₂) (b := b₂)
      he₂Internal he₂Uncovered ha₂s hb₂s
  have hMcompl : IsCrossMatching sᶜ M :=
    (isCrossMatching_set_compl s M).mpr hM
  have hPcompl : IsInternalCrossPacking H sᶜ P :=
    (isInternalCrossPacking_set_compl_iff H s P).mpr hP
  have hPmaxCompl : ∀ Q : Finset (Finset α),
      IsInternalCrossPacking H sᶜ Q → Q.card ≤ P.card := by
    intro Q hQ
    exact hPmax Q ((isInternalCrossPacking_set_compl_iff H s Q).mp hQ)
  obtain ⟨A₂, B₂, hA₂, hB₂, hAB₂, hA₂s, hB₂s,
      ha₁A₂, hb₁B₂, _hsub₂, havoid₂, hcount₂⟩ :=
    exists_claim43_side_cliques (G := G) (u := sᶜ) (M := M) hMcompl
      hPcompl hPmaxCompl (f := e₂) (a := a₁) (b := b₁)
      (by simpa [H] using he₁Internal)
      (by simpa [H] using he₁Uncovered)
      (by simpa using ha₁s) (by simpa using hb₁s)
  have hcount₂' : R₂.card ≤ A₂.card + B₂.card + 2 := by
    simpa only [R₂, D₂, C₂] using hcount₂
  have havoid₁' : Disjoint (A₁ ∪ B₁) {a₁, b₁} := by
    simpa [e₁, Sym2.toFinset_mk_eq] using havoid₁
  have havoid₂' : Disjoint {a₂, b₂} (A₂ ∪ B₂) := by
    simpa [e₂, Sym2.toFinset_mk_eq] using havoid₂.symm
  have hredR : (((R₁.card + R₂.card : ℕ) : ℝ)) ≤
      2 * fractionalSize Gᶜ w + 8 :=
    claim43_red_remainders_bound (G := Gᶜ) (s := s)
      (z₁ := a₂) (w₁ := b₂) (z₂ := a₁) (w₂ := b₁)
      (weight := w) (r₁ := R₁.card) (r₂ := R₂.card)
      hwmax hA₁ hB₁ hA₂ hB₂ hAB₁ hAB₂ hA₁s hB₁s hA₂s hB₂s
      ha₂s hb₂s ha₁s hb₁s he₂G.ne he₁G.ne
      ha₂A₁ hb₂B₁ ha₁A₂ hb₁B₂ havoid₁' havoid₂' hcount₁ hcount₂'
  have hremainder :=
    card_sides_le_remainders_add_packingSupport_add_four_add_covers
      (G := G) (s := s) (P := P) he₁ he₂
  have hsupport := card_packingVertices_le_three_mul hP_G
  have hcovers :=
    card_chosenEndpointCovers_add_card_packing_add_two_le_internal
      hP_G he₁ he₂ he₁UncoveredG he₂UncoveredG
  exact ⟨(packingVertices P).card, C₁.card, C₂.card, R₁.card, R₂.card,
    hremainder, hsupport, hcovers, hredR⟩

theorem proposition42_claim43_both_sides_uncovered
    {G : SimpleGraph α} {s : Set α} {M : Finset (Sym2 α)}
    (hM : IsCrossMatching s M)
    {P : Finset (Finset α)}
    (hP : IsInternalCrossPacking
      (G.deleteEdges (M : Set (Sym2 α))) s P)
    (hPmax : ∀ Q : Finset (Finset α),
      IsInternalCrossPacking (G.deleteEdges (M : Set (Sym2 α))) s Q →
        Q.card ≤ P.card)
    {a₁ b₁ a₂ b₂ : α}
    (he₁ : s(a₁, b₁) ∈ sideEdgeFinset G s.toFinset)
    (he₂ : s(a₂, b₂) ∈ sideEdgeFinset G sᶜ.toFinset)
    (he₁Uncovered : s(a₁, b₁) ∉ coveredInternalEdges
      (G.deleteEdges (M : Set (Sym2 α))) s P)
    (he₂Uncovered : s(a₂, b₂) ∉ coveredInternalEdges
      (G.deleteEdges (M : Set (Sym2 α))) s P)
    {w : Finset α → ℝ}
    (hwmax : ∀ q : Finset α → ℝ,
      IsFractionalInternalCrossPacking Gᶜ s q →
        fractionalSize Gᶜ q ≤ fractionalSize Gᶜ w) :
    (Fintype.card α : ℝ) - 2 * (P.card : ℝ) -
        ((internalEdgeFinset G s).card : ℝ) - 10 ≤
      2 * fractionalSize Gᶜ w := by
  obtain ⟨p, c₁, c₂, r₁, r₂, hrem, hp, hc, hr⟩ :=
    proposition42_claim43_estimateCertificate hM hP hPmax he₁ he₂
      he₁Uncovered he₂Uncovered hwmax
  exact claim43_lower_bound_of_remainder_bound
    (Fintype.card α) (internalEdgeFinset G s).card P.card
      p c₁ c₂ r₁ r₂ (fractionalSize Gᶜ w) hrem hp hc hr
-/

/-- Elementary preprocessing for Claim 4.3.  The two displayed blue edges
remain internal after deleting the forbidden cross matching, while the given
packing and its uncovered-edge facts may be lifted back to `G`. -/
lemma proposition42_claim43_endpointFacts
    {G : SimpleGraph α} {s : Set α} {M : Finset (Sym2 α)}
    (hM : IsCrossMatching s M)
    {P : Finset (Finset α)}
    (hP : IsInternalCrossPacking
      (G.deleteEdges (M : Set (Sym2 α))) s P)
    {a₁ b₁ a₂ b₂ : α}
    (he₁ : s(a₁, b₁) ∈ sideEdgeFinset G s.toFinset)
    (he₂ : s(a₂, b₂) ∈ sideEdgeFinset G sᶜ.toFinset)
    (he₁Uncovered : s(a₁, b₁) ∉ coveredInternalEdges
      (G.deleteEdges (M : Set (Sym2 α))) s P)
    (he₂Uncovered : s(a₂, b₂) ∉ coveredInternalEdges
      (G.deleteEdges (M : Set (Sym2 α))) s P) :
    G.Adj a₁ b₁ ∧ G.Adj a₂ b₂ ∧
      a₁ ∈ s ∧ b₁ ∈ s ∧ a₂ ∉ s ∧ b₂ ∉ s ∧
      s(a₁, b₁) ∈ internalEdgeFinset
        (G.deleteEdges (M : Set (Sym2 α))) s ∧
      s(a₂, b₂) ∈ internalEdgeFinset
        (G.deleteEdges (M : Set (Sym2 α))) s ∧
      IsInternalCrossPacking G s P ∧
      s(a₁, b₁) ∉ coveredInternalEdges G s P ∧
      s(a₂, b₂) ∉ coveredInternalEdges G s P := by
  classical
  have he₁G : G.Adj a₁ b₁ :=
    SimpleGraph.mem_edgeFinset.mp (mem_filter.mp he₁).1
  have he₂G : G.Adj a₂ b₂ :=
    SimpleGraph.mem_edgeFinset.mp (mem_filter.mp he₂).1
  have ha₁s : a₁ ∈ s := by
    have hsub := (mem_filter.mp he₁).2
    have haPair : a₁ ∈ s(a₁, b₁).toFinset := by simp
    simpa using hsub haPair
  have hb₁s : b₁ ∈ s := by
    have hsub := (mem_filter.mp he₁).2
    have hbPair : b₁ ∈ s(a₁, b₁).toFinset := by simp
    simpa using hsub hbPair
  have ha₂s : a₂ ∉ s := by
    have h := (mem_filter.mp he₂).2
      (show a₂ ∈ s(a₂, b₂).toFinset by simp)
    simpa using h
  have hb₂s : b₂ ∉ s := by
    have h := (mem_filter.mp he₂).2
      (show b₂ ∈ s(a₂, b₂).toFinset by simp)
    simpa using h
  have he₁InternalG : s(a₁, b₁) ∈ internalEdgeFinset G s := by
    rw [internalEdgeFinset_eq_union_sides]
    exact mem_union_left _ he₁
  have he₂InternalG : s(a₂, b₂) ∈ internalEdgeFinset G s := by
    rw [internalEdgeFinset_eq_union_sides]
    exact mem_union_right _ he₂
  have he₁Internal : s(a₁, b₁) ∈ internalEdgeFinset
      (G.deleteEdges (M : Set (Sym2 α))) s := by
    simpa only [internalEdgeFinset_deleteEdges_of_cross G s M hM.1]
      using he₁InternalG
  have he₂Internal : s(a₂, b₂) ∈ internalEdgeFinset
      (G.deleteEdges (M : Set (Sym2 α))) s := by
    simpa only [internalEdgeFinset_deleteEdges_of_cross G s M hM.1]
      using he₂InternalG
  have hP_G : IsInternalCrossPacking G s P :=
    hP.of_deleteEdges_cross hM.1
  have he₁UncoveredG : s(a₁, b₁) ∉ coveredInternalEdges G s P := by
    rw [← coveredInternalEdges_deleteEdges_of_cross G s M P hM.1]
    exact he₁Uncovered
  have he₂UncoveredG : s(a₂, b₂) ∉ coveredInternalEdges G s P := by
    rw [← coveredInternalEdges_deleteEdges_of_cross G s M P hM.1]
    exact he₂Uncovered
  exact ⟨he₁G, he₂G, ha₁s, hb₁s, ha₂s, hb₂s,
    he₁Internal, he₂Internal, hP_G, he₁UncoveredG, he₂UncoveredG⟩

/-- Vertices unavailable on one side in the construction for Claim 4.3. -/
def claim43DeletionSet (P : Finset (Finset α)) (e : Sym2 α) : Finset α :=
  packingVertices P ∪ e.toFinset

/-- The chosen endpoint cover on one side in Claim 4.3. -/
def claim43EndpointCover (G : SimpleGraph α) (u : Set α)
    (P : Finset (Finset α)) (e : Sym2 α) : Finset α :=
  chosenEndpointCover
    (edgesInsideOutside G u.toFinset (claim43DeletionSet P e))

/-- The one-side remainder after deleting the blue support, one uncovered
edge, and the chosen endpoint cover. -/
def claim43Remainder (G : SimpleGraph α) (u : Set α)
    (P : Finset (Finset α)) (e : Sym2 α) : Finset α :=
  (u.toFinset \ claim43DeletionSet P e) \
    claim43EndpointCover G u P e

/-- The red-packing half of Claim 4.3, with all auxiliary clique witnesses
hidden behind the two canonical remainder finsets. -/
lemma proposition42_claim43_redRemainderBound
    {G : SimpleGraph α} {s : Set α} {M : Finset (Sym2 α)}
    (hM : IsCrossMatching s M)
    {P : Finset (Finset α)}
    (hP : IsInternalCrossPacking
      (G.deleteEdges (M : Set (Sym2 α))) s P)
    (hPmax : ∀ Q : Finset (Finset α),
      IsInternalCrossPacking (G.deleteEdges (M : Set (Sym2 α))) s Q →
        Q.card ≤ P.card)
    {a₁ b₁ a₂ b₂ : α}
    (he₁ : s(a₁, b₁) ∈ sideEdgeFinset G s.toFinset)
    (he₂ : s(a₂, b₂) ∈ sideEdgeFinset G sᶜ.toFinset)
    (he₁Uncovered : s(a₁, b₁) ∉ coveredInternalEdges
      (G.deleteEdges (M : Set (Sym2 α))) s P)
    (he₂Uncovered : s(a₂, b₂) ∉ coveredInternalEdges
      (G.deleteEdges (M : Set (Sym2 α))) s P)
    {w : Finset α → ℝ}
    (hwmax : ∀ q : Finset α → ℝ,
      IsFractionalInternalCrossPacking Gᶜ s q →
        fractionalSize Gᶜ q ≤ fractionalSize Gᶜ w) :
    ((((claim43Remainder G s P s(a₁, b₁)).card +
        (claim43Remainder G sᶜ P s(a₂, b₂)).card : ℕ) : ℝ)) ≤
      2 * fractionalSize Gᶜ w + 8 := by
  classical
  rcases proposition42_claim43_endpointFacts hM hP he₁ he₂
      he₁Uncovered he₂Uncovered with
    ⟨he₁G, he₂G, ha₁s, hb₁s, ha₂s, hb₂s, he₁Internal,
      he₂Internal, _hP_G, _he₁UncoveredG, _he₂UncoveredG⟩
  obtain ⟨A₁, B₁, hA₁, hB₁, hAB₁, hA₁s, hB₁s,
      ha₂A₁, hb₂B₁, _hsub₁, havoid₁, hcount₁⟩ :=
    exists_claim43_side_cliques (G := G) (u := s) (M := M) hM
      hP hPmax (f := s(a₁, b₁)) (a := a₂) (b := b₂)
      he₂Internal he₂Uncovered ha₂s hb₂s
  have hMcompl : IsCrossMatching sᶜ M :=
    (isCrossMatching_set_compl s M).mpr hM
  have hPcompl : IsInternalCrossPacking
      (G.deleteEdges (M : Set (Sym2 α))) sᶜ P :=
    (isInternalCrossPacking_set_compl_iff
      (G.deleteEdges (M : Set (Sym2 α))) s P).mpr hP
  have hPmaxCompl : ∀ Q : Finset (Finset α),
      IsInternalCrossPacking
        (G.deleteEdges (M : Set (Sym2 α))) sᶜ Q → Q.card ≤ P.card := by
    intro Q hQ
    exact hPmax Q ((isInternalCrossPacking_set_compl_iff
      (G.deleteEdges (M : Set (Sym2 α))) s Q).mp hQ)
  obtain ⟨A₂, B₂, hA₂, hB₂, hAB₂, hA₂s, hB₂s,
      ha₁A₂, hb₁B₂, _hsub₂, havoid₂, hcount₂⟩ :=
    exists_claim43_side_cliques (G := G) (u := sᶜ) (M := M) hMcompl
      hPcompl hPmaxCompl (f := s(a₂, b₂)) (a := a₁) (b := b₁)
      (by simpa using he₁Internal) (by simpa using he₁Uncovered)
      (by simpa using ha₁s) (by simpa using hb₁s)
  have hcount₁' : (claim43Remainder G s P s(a₁, b₁)).card ≤
      A₁.card + B₁.card + 2 := by
    simpa [claim43Remainder, claim43EndpointCover, claim43DeletionSet]
      using hcount₁
  have hcount₂' : (claim43Remainder G sᶜ P s(a₂, b₂)).card ≤
      A₂.card + B₂.card + 2 := by
    simpa [claim43Remainder, claim43EndpointCover, claim43DeletionSet]
      using hcount₂
  have havoid₁' : Disjoint (A₁ ∪ B₁) {a₁, b₁} := by
    simpa [Sym2.toFinset_mk_eq] using havoid₁
  have havoid₂' : Disjoint {a₂, b₂} (A₂ ∪ B₂) := by
    simpa [Sym2.toFinset_mk_eq] using havoid₂.symm
  exact claim43_red_remainders_bound (G := Gᶜ) (s := s)
    (z₁ := a₂) (w₁ := b₂) (z₂ := a₁) (w₂ := b₁)
    (weight := w)
    (r₁ := (claim43Remainder G s P s(a₁, b₁)).card)
    (r₂ := (claim43Remainder G sᶜ P s(a₂, b₂)).card)
    hwmax hA₁ hB₁ hA₂ hB₂ hAB₁ hAB₂ hA₁s hB₁s hA₂s hB₂s
    ha₂s hb₂s ha₁s hb₁s he₂G.ne he₁G.ne
    ha₂A₁ hb₂B₁ ha₁A₂ hb₁B₂ havoid₁' havoid₂' hcount₁' hcount₂'

/-- The graph-theoretic counting package of Claim 4.3 after elementary
endpoint preprocessing.  The witnesses are the two endpoint-cover sizes and
the two red-clique remainder sizes. -/
lemma proposition42_claim43_numericalData
    {G : SimpleGraph α} {s : Set α} {M : Finset (Sym2 α)}
    (hM : IsCrossMatching s M)
    {P : Finset (Finset α)}
    (hP : IsInternalCrossPacking
      (G.deleteEdges (M : Set (Sym2 α))) s P)
    (hPmax : ∀ Q : Finset (Finset α),
      IsInternalCrossPacking (G.deleteEdges (M : Set (Sym2 α))) s Q →
        Q.card ≤ P.card)
    {a₁ b₁ a₂ b₂ : α}
    (he₁ : s(a₁, b₁) ∈ sideEdgeFinset G s.toFinset)
    (he₂ : s(a₂, b₂) ∈ sideEdgeFinset G sᶜ.toFinset)
    (he₁Uncovered : s(a₁, b₁) ∉ coveredInternalEdges
      (G.deleteEdges (M : Set (Sym2 α))) s P)
    (he₂Uncovered : s(a₂, b₂) ∉ coveredInternalEdges
      (G.deleteEdges (M : Set (Sym2 α))) s P)
    {w : Finset α → ℝ}
    (hwmax : ∀ q : Finset α → ℝ,
      IsFractionalInternalCrossPacking Gᶜ s q →
        fractionalSize Gᶜ q ≤ fractionalSize Gᶜ w) :
    ∃ c₁ c₂ r₁ r₂ : ℕ,
      Fintype.card α ≤ r₁ + r₂ + (packingVertices P).card + 4 + c₁ + c₂ ∧
      c₁ + c₂ + P.card + 2 ≤ (internalEdgeFinset G s).card ∧
      (((r₁ + r₂ : ℕ) : ℝ)) ≤ 2 * fractionalSize Gᶜ w + 8 := by
  classical
  rcases proposition42_claim43_endpointFacts hM hP he₁ he₂
      he₁Uncovered he₂Uncovered with
    ⟨_he₁G, _he₂G, _ha₁s, _hb₁s, _ha₂s, _hb₂s,
      _he₁Internal, _he₂Internal, hP_G, he₁UncoveredG, he₂UncoveredG⟩
  let C₁ := claim43EndpointCover G s P s(a₁, b₁)
  let C₂ := claim43EndpointCover G sᶜ P s(a₂, b₂)
  let R₁ := claim43Remainder G s P s(a₁, b₁)
  let R₂ := claim43Remainder G sᶜ P s(a₂, b₂)
  have hremainder : Fintype.card α ≤ R₁.card + R₂.card +
      (packingVertices P).card + 4 + C₁.card + C₂.card := by
    simpa [R₁, R₂, C₁, C₂, claim43Remainder, claim43EndpointCover,
      claim43DeletionSet] using
      (card_sides_le_remainders_add_packingSupport_add_four_add_covers
        (G := G) (s := s) (P := P) he₁ he₂)
  have hcovers : C₁.card + C₂.card + P.card + 2 ≤
      (internalEdgeFinset G s).card := by
    simpa [C₁, C₂, claim43EndpointCover, claim43DeletionSet] using
      (card_chosenEndpointCovers_add_card_packing_add_two_le_internal
        hP_G he₁ he₂ he₁UncoveredG he₂UncoveredG)
  have hred := proposition42_claim43_redRemainderBound
    hM hP hPmax he₁ he₂ he₁Uncovered he₂Uncovered hwmax
  exact ⟨C₁.card, C₂.card, R₁.card, R₂.card,
    hremainder, hcovers, by simpa [R₁, R₂] using hred⟩

/-- The graph-theoretic half of Claim 4.3, packaged in the five numerical
quantities consumed by its final linear-arithmetic step. -/
theorem proposition42_claim43_estimateCertificate
    {G : SimpleGraph α} {s : Set α} {M : Finset (Sym2 α)}
    (hM : IsCrossMatching s M)
    {P : Finset (Finset α)}
    (hP : IsInternalCrossPacking
      (G.deleteEdges (M : Set (Sym2 α))) s P)
    (hPmax : ∀ Q : Finset (Finset α),
      IsInternalCrossPacking (G.deleteEdges (M : Set (Sym2 α))) s Q →
        Q.card ≤ P.card)
    {a₁ b₁ a₂ b₂ : α}
    (he₁ : s(a₁, b₁) ∈ sideEdgeFinset G s.toFinset)
    (he₂ : s(a₂, b₂) ∈ sideEdgeFinset G sᶜ.toFinset)
    (he₁Uncovered : s(a₁, b₁) ∉ coveredInternalEdges
      (G.deleteEdges (M : Set (Sym2 α))) s P)
    (he₂Uncovered : s(a₂, b₂) ∉ coveredInternalEdges
      (G.deleteEdges (M : Set (Sym2 α))) s P)
    {w : Finset α → ℝ}
    (hwmax : ∀ q : Finset α → ℝ,
      IsFractionalInternalCrossPacking Gᶜ s q →
        fractionalSize Gᶜ q ≤ fractionalSize Gᶜ w) :
    Claim43EstimateCertificate (Fintype.card α)
      (internalEdgeFinset G s).card P.card (fractionalSize Gᶜ w) := by
  obtain ⟨c₁, c₂, r₁, r₂, hremainder, hcovers, hred⟩ :=
    proposition42_claim43_numericalData hM hP hPmax he₁ he₂
      he₁Uncovered he₂Uncovered hwmax
  have hsupport := card_packingVertices_le_three_mul
    (hP.of_deleteEdges_cross hM.1)
  exact ⟨(packingVertices P).card, c₁, c₂, r₁, r₂,
    hremainder, hsupport, hcovers, hred⟩

/-- Claim 4.3 of Proposition 4.2: when a maximum blue cross packing leaves an
internal edge uncovered on each side, the maximum fractional red cross
packing satisfies the paper's sharp lower bound. -/
theorem proposition42_claim43_both_sides_uncovered
    {G : SimpleGraph α} {s : Set α} {M : Finset (Sym2 α)}
    (hM : IsCrossMatching s M)
    {P : Finset (Finset α)}
    (hP : IsInternalCrossPacking
      (G.deleteEdges (M : Set (Sym2 α))) s P)
    (hPmax : ∀ Q : Finset (Finset α),
      IsInternalCrossPacking (G.deleteEdges (M : Set (Sym2 α))) s Q →
        Q.card ≤ P.card)
    {a₁ b₁ a₂ b₂ : α}
    (he₁ : s(a₁, b₁) ∈ sideEdgeFinset G s.toFinset)
    (he₂ : s(a₂, b₂) ∈ sideEdgeFinset G sᶜ.toFinset)
    (he₁Uncovered : s(a₁, b₁) ∉ coveredInternalEdges
      (G.deleteEdges (M : Set (Sym2 α))) s P)
    (he₂Uncovered : s(a₂, b₂) ∉ coveredInternalEdges
      (G.deleteEdges (M : Set (Sym2 α))) s P)
    {w : Finset α → ℝ}
    (hwmax : ∀ q : Finset α → ℝ,
      IsFractionalInternalCrossPacking Gᶜ s q →
        fractionalSize Gᶜ q ≤ fractionalSize Gᶜ w) :
    (Fintype.card α : ℝ) - 2 * (P.card : ℝ) -
        ((internalEdgeFinset G s).card : ℝ) - 10 ≤
      2 * fractionalSize Gᶜ w := by
  obtain ⟨p, c₁, c₂, r₁, r₂, hrem, hp, hc, hr⟩ :=
    proposition42_claim43_estimateCertificate hM hP hPmax he₁ he₂
      he₁Uncovered he₂Uncovered hwmax
  exact claim43_lower_bound_of_remainder_bound
    (Fintype.card α) (internalEdgeFinset G s).card P.card
      p c₁ c₂ r₁ r₂ (fractionalSize Gᶜ w) hrem hp hc hr

/-! ### Claim 4.4: exactly one side has an uncovered internal edge -/

/-- Vertices on one side not used by the selected blue cross packing. -/
def claim44UnusedSide (s : Set α) (P : Finset (Finset α)) : Finset α :=
  s.toFinset \ packingVertices P

/-- If every blue edge on one side is covered, deleting the vertices used by
the blue packing leaves a red clique on that side. -/
lemma claim44_unusedSide_isClique
    {G : SimpleGraph α} {s : Set α} {P : Finset (Finset α)}
    (hcover : ∀ e ∈ sideEdgeFinset G s.toFinset,
      e ∈ coveredInternalEdges G s P) :
    Gᶜ.IsClique (claim44UnusedSide s P : Set α) := by
  classical
  intro a ha b hb hab
  rw [SimpleGraph.compl_adj]
  refine ⟨hab, ?_⟩
  intro hGab
  have heSide : s(a, b) ∈ sideEdgeFinset G s.toFinset := by
    apply mem_filter.mpr
    refine ⟨SimpleGraph.mem_edgeFinset.mpr hGab, ?_⟩
    intro v hv
    have hvab : v = a ∨ v = b := by
      simpa [Sym2.toFinset_mk_eq] using hv
    rcases hvab with rfl | rfl
    · exact (mem_sdiff.mp ha).1
    · exact (mem_sdiff.mp hb).1
  have heCovered := hcover s(a, b) heSide
  have hsupport := coveredInternalEdge_toFinset_subset_packingVertices heCovered
  have haSupport : a ∈ packingVertices P := hsupport (by simp)
  exact (mem_sdiff.mp ha).2 haSupport

/-- A cross triangle uses at most two vertices of either side, so removing the
support of `m` selected triangles costs at most `2m` vertices on a fixed side. -/
lemma card_side_le_claim44UnusedSide_add_two_mul
    {G : SimpleGraph α} {s : Set α} {P : Finset (Finset α)}
    (hP : IsInternalCrossPacking G s P) :
    s.toFinset.card ≤ (claim44UnusedSide s P).card + 2 * P.card := by
  classical
  have hsupport := card_packingVertices_filter_le_two_mul hP
  have hinter : s.toFinset ∩ packingVertices P =
      (packingVertices P).filter fun v ↦ v ∈ s := by
    ext v
    simp [and_comm]
  have hpartition := card_sdiff_add_card_inter
    s.toFinset (packingVertices P)
  rw [hinter] at hpartition
  dsimp only [claim44UnusedSide]
  omega

/-- Elementary one-edge preprocessing for Claim 4.4.  An uncovered edge on
the opposite side survives deletion of the forbidden cross matching. -/
lemma proposition42_claim44_edgeFacts
    {G : SimpleGraph α} {s : Set α} {M : Finset (Sym2 α)}
    (hM : IsCrossMatching s M)
    {P : Finset (Finset α)}
    (hP : IsInternalCrossPacking
      (G.deleteEdges (M : Set (Sym2 α))) s P)
    {a b : α}
    (he : s(a, b) ∈ sideEdgeFinset G sᶜ.toFinset)
    (heUncovered : s(a, b) ∉ coveredInternalEdges
      (G.deleteEdges (M : Set (Sym2 α))) s P) :
    G.Adj a b ∧ a ∉ s ∧ b ∉ s ∧
      s(a, b) ∈ internalEdgeFinset
        (G.deleteEdges (M : Set (Sym2 α))) s ∧
      IsInternalCrossPacking G s P ∧
      s(a, b) ∉ coveredInternalEdges G s P := by
  classical
  have habG : G.Adj a b :=
    SimpleGraph.mem_edgeFinset.mp (mem_filter.mp he).1
  have has : a ∉ s := by
    have h := (mem_filter.mp he).2
      (show a ∈ s(a, b).toFinset by simp)
    simpa using h
  have hbs : b ∉ s := by
    have h := (mem_filter.mp he).2
      (show b ∈ s(a, b).toFinset by simp)
    simpa using h
  have heInternalG : s(a, b) ∈ internalEdgeFinset G s := by
    rw [internalEdgeFinset_eq_union_sides]
    exact mem_union_right _ he
  have heInternal : s(a, b) ∈ internalEdgeFinset
      (G.deleteEdges (M : Set (Sym2 α))) s := by
    simpa only [internalEdgeFinset_deleteEdges_of_cross G s M hM.1]
      using heInternalG
  have hP_G : IsInternalCrossPacking G s P :=
    hP.of_deleteEdges_cross hM.1
  have heUncoveredG : s(a, b) ∉ coveredInternalEdges G s P := by
    rw [← coveredInternalEdges_deleteEdges_of_cross G s M P hM.1]
    exact heUncovered
  exact ⟨habG, has, hbs, heInternal, hP_G, heUncoveredG⟩

/-- The finite red-neighbourhood witnesses in Claim 4.4.  If the side `s`
is saturated by the maximal blue packing and `s(a,b)` is an uncovered edge
on the other side, the unused vertices of `s` split, up to the two forbidden
matching partners, into two disjoint red cliques attached to `a` and `b`.
The last inequality includes the at most `2|P|` vertices of `s` used by the
blue cross packing. -/
lemma proposition42_claim44_sideCliques
    {G : SimpleGraph α} {s : Set α} {M : Finset (Sym2 α)}
    (hM : IsCrossMatching s M)
    {P : Finset (Finset α)}
    (hP : IsInternalCrossPacking
      (G.deleteEdges (M : Set (Sym2 α))) s P)
    (hPmax : ∀ Q : Finset (Finset α),
      IsInternalCrossPacking (G.deleteEdges (M : Set (Sym2 α))) s Q →
        Q.card ≤ P.card)
    (hcover : ∀ e ∈ sideEdgeFinset G s.toFinset,
      e ∈ coveredInternalEdges G s P)
    {a b : α}
    (he : s(a, b) ∈ sideEdgeFinset G sᶜ.toFinset)
    (heUncovered : s(a, b) ∉ coveredInternalEdges
      (G.deleteEdges (M : Set (Sym2 α))) s P) :
    ∃ A B : Finset α,
      Gᶜ.IsClique (A : Set α) ∧ Gᶜ.IsClique (B : Set α) ∧
      Disjoint A B ∧
      (∀ x ∈ A, x ∈ s) ∧ (∀ x ∈ B, x ∈ s) ∧
      (∀ x ∈ A, Gᶜ.Adj a x) ∧ (∀ x ∈ B, Gᶜ.Adj b x) ∧
      s.toFinset.card ≤ A.card + B.card + 2 * P.card + 2 := by
  classical
  rcases proposition42_claim44_edgeFacts hM hP he heUncovered with
    ⟨_habG, has, hbs, heInternal, hP_G, _heUncoveredG⟩
  let U := claim44UnusedSide s P
  let A := redNeighborFinset G a U
  let B := redNeighborFinset G b (U \ A)
  have hUsub : ∀ x ∈ U, x ∈ s := by
    intro x hx
    simpa only [Set.mem_toFinset] using (mem_sdiff.mp hx).1
  have hUclique : Gᶜ.IsClique (U : Set α) := by
    exact claim44_unusedSide_isClique hcover
  have hAsub : A ⊆ U := fun _x hx ↦ (mem_filter.mp hx).1
  have hBsub : B ⊆ U := fun _x hx ↦
    (mem_sdiff.mp (mem_filter.mp hx).1).1
  have hAclique : Gᶜ.IsClique (A : Set α) := by
    apply hUclique.subset
    intro x hx
    exact hAsub hx
  have hBclique : Gᶜ.IsClique (B : Set α) := by
    apply hUclique.subset
    intro x hx
    exact hBsub hx
  have hAB : Disjoint A B := by
    rw [Finset.disjoint_left]
    intro x hxA hxB
    exact (mem_sdiff.mp (mem_filter.mp hxB).1).2 hxA
  have heP : ∀ t ∈ P, s(a, b) ∉ t.sym2 := by
    intro t htP het
    exact heUncovered (mem_filter.mpr
      ⟨heInternal, ⟨t, htP, het⟩⟩)
  have hcommon : ∀ x ∈ U,
      ¬ ((G.deleteEdges (M : Set (Sym2 α))).Adj a x ∧
        (G.deleteEdges (M : Set (Sym2 α))).Adj b x) := by
    intro x hxU
    have hxs : x ∈ s := hUsub x hxU
    have hxunused : x ∉ packingVertices P := (mem_sdiff.mp hxU).2
    exact maximum_internalCrossPacking_no_common_unused_opposite_neighbor
      hP hPmax heInternal heP (by simp [hxs, has]) hxunused
  have haU : a ∉ U := fun haU ↦ has (hUsub a haU)
  have hbU : b ∉ U := fun hbU ↦ hbs (hUsub b hbU)
  have hcount : U.card ≤ A.card + B.card + 2 := by
    exact redNeighborFinset_add_card_ge_of_no_common_deleteEdges_neighbor
      hM G U a b haU hbU hcommon
  have hside := card_side_le_claim44UnusedSide_add_two_mul hP_G
  refine ⟨A, B, hAclique, hBclique, hAB, ?_, ?_, ?_, ?_, ?_⟩
  · intro x hx
    exact hUsub x (hAsub hx)
  · intro x hx
    exact hUsub x (hBsub hx)
  · intro x hx
    exact (mem_filter.mp hx).2
  · intro x hx
    exact (mem_filter.mp hx).2
  · change s.toFinset.card ≤ A.card + B.card + 2 * P.card + 2
    change s.toFinset.card ≤ U.card + 2 * P.card at hside
    omega

/-- Coarse fractional-packing conclusion of Claim 4.4.  The two red stars
obtained from the saturated side lose at most one vertex in each matching;
together with the two forbidden matching partners this gives the constant
four.  The paper's singleton refinement below improves this constant in the
small-`k` case. -/
lemma proposition42_claim44_saturatedSideLowerBound
    {G : SimpleGraph α} {s : Set α} {M : Finset (Sym2 α)}
    (hM : IsCrossMatching s M)
    {P : Finset (Finset α)}
    (hP : IsInternalCrossPacking
      (G.deleteEdges (M : Set (Sym2 α))) s P)
    (hPmax : ∀ Q : Finset (Finset α),
      IsInternalCrossPacking (G.deleteEdges (M : Set (Sym2 α))) s Q →
        Q.card ≤ P.card)
    (hcover : ∀ e ∈ sideEdgeFinset G s.toFinset,
      e ∈ coveredInternalEdges G s P)
    {a b : α}
    (he : s(a, b) ∈ sideEdgeFinset G sᶜ.toFinset)
    (heUncovered : s(a, b) ∉ coveredInternalEdges
      (G.deleteEdges (M : Set (Sym2 α))) s P)
    {w : Finset α → ℝ}
    (hwmax : ∀ q : Finset α → ℝ,
      IsFractionalInternalCrossPacking Gᶜ s q →
        fractionalSize Gᶜ q ≤ fractionalSize Gᶜ w) :
    (s.toFinset.card : ℝ) - 2 * (P.card : ℝ) - 4 ≤
      2 * fractionalSize Gᶜ w := by
  classical
  rcases proposition42_claim44_edgeFacts hM hP he heUncovered with
    ⟨habG, has, hbs, _heInternal, _hP_G, _heUncoveredG⟩
  obtain ⟨A, B, hA, hB, hAB, hAs, hBs, haA, hbB, hcount⟩ :=
    proposition42_claim44_sideCliques hM hP hPmax hcover he heUncovered
  have hred := twoStarClique_card_le_maximal_fractionalInternalCrossPacking
    (G := Gᶜ) (s := s) (A := A) (B := B) (z := a) (w := b)
      hwmax hA hB hAB hAs hBs has hbs habG.ne haA hbB
  have hcountR : (s.toFinset.card : ℝ) ≤
      ((A.card + B.card : ℕ) : ℝ) + 2 * (P.card : ℝ) + 2 := by
    exact_mod_cast hcount
  linarith

/-- The complete `m ≥ 2` branch of Claim 4.4.  In the notation of the
paper, `x` records the imbalance of the chosen bipartition, so the saturated
side has size at least `n/2-x`.  The two parity losses in the coarse
two-star construction are absorbed by the extra copy of `m`. -/
lemma proposition42_claim44_ge_two
    {G : SimpleGraph α} {s : Set α} {M : Finset (Sym2 α)}
    (hM : IsCrossMatching s M)
    {P : Finset (Finset α)}
    (hP : IsInternalCrossPacking
      (G.deleteEdges (M : Set (Sym2 α))) s P)
    (hPmax : ∀ Q : Finset (Finset α),
      IsInternalCrossPacking (G.deleteEdges (M : Set (Sym2 α))) s Q →
        Q.card ≤ P.card)
    (hcover : ∀ e ∈ sideEdgeFinset G s.toFinset,
      e ∈ coveredInternalEdges G s P)
    {a b : α}
    (he : s(a, b) ∈ sideEdgeFinset G sᶜ.toFinset)
    (heUncovered : s(a, b) ∉ coveredInternalEdges
      (G.deleteEdges (M : Set (Sym2 α))) s P)
    {w : Finset α → ℝ}
    (hwmax : ∀ q : Finset α → ℝ,
      IsFractionalInternalCrossPacking Gᶜ s q →
        fractionalSize Gᶜ q ≤ fractionalSize Gᶜ w)
    {n : ℕ} {x : ℝ}
    (hside : (n : ℝ) / 2 - x ≤ (s.toFinset.card : ℝ))
    (hm : 2 ≤ P.card) :
    (n : ℝ) / 2 - x - 3 * (P.card : ℝ) - 2 ≤
      2 * fractionalSize Gᶜ w := by
  have hcoarse := proposition42_claim44_saturatedSideLowerBound
    hM hP hPmax hcover he heUncovered hwmax
  have hmR : (2 : ℝ) ≤ P.card := by exact_mod_cast hm
  linarith

/-! #### Uniform fractional matchings for the singleton refinement -/

/-- Constant weight on a finite family of triangles. -/
def constantTriangleFamilyWeight (F : Finset (Finset α)) (d : ℕ) :
    Finset α → ℝ :=
  fun t ↦ if t ∈ F then ((d : ℝ))⁻¹ else 0

/-- A triangle family in which every graph edge occurs at most `d` times,
with `d > 0`, gives a fractional packing after assigning weight `1/d` to
each member. -/
lemma isFractionalPacking_constantTriangleFamilyWeight
    {G : SimpleGraph α} {F : Finset (Finset α)} {d : ℕ}
    (hd : 0 < d)
    (htri : ∀ t ∈ F, G.IsNClique 3 t)
    (hload : ∀ e ∈ G.edgeFinset,
      (F.filter fun t ↦ e ∈ t.sym2).card ≤ d) :
    IsFractionalPacking G (constantTriangleFamilyWeight F d) := by
  classical
  constructor
  · intro t _ht
    simp only [constantTriangleFamilyWeight]
    split <;> positivity
  · intro e he
    unfold fractionalEdgeLoad
    rw [← sum_subset
      (s₁ := F.filter fun t ↦ e ∈ t.sym2)
      (s₂ := (G.cliqueFinset 3).filter fun t ↦ e ∈ t.sym2)]
    · have hsum :
          (∑ t ∈ F with e ∈ t.sym2,
              constantTriangleFamilyWeight F d t) =
            (((F.filter fun t ↦ e ∈ t.sym2).card : ℕ) : ℝ) *
              (d : ℝ)⁻¹ := by
          calc
            (∑ t ∈ F with e ∈ t.sym2,
                constantTriangleFamilyWeight F d t) =
                ∑ _t ∈ F.filter (fun t ↦ e ∈ t.sym2),
                  (d : ℝ)⁻¹ := by
              apply sum_congr rfl
              intro t ht
              simp [constantTriangleFamilyWeight, (mem_filter.mp ht).1]
            _ = (((F.filter fun t ↦ e ∈ t.sym2).card : ℕ) : ℝ) *
                (d : ℝ)⁻¹ := by simp
      rw [hsum]
      have hcardR :
          (((F.filter fun t ↦ e ∈ t.sym2).card : ℕ) : ℝ) ≤ d := by
        exact_mod_cast hload e he
      calc
        (((F.filter fun t ↦ e ∈ t.sym2).card : ℕ) : ℝ) * (d : ℝ)⁻¹ ≤
            (d : ℝ) * (d : ℝ)⁻¹ := by
          exact mul_le_mul_of_nonneg_right hcardR (by positivity)
        _ = 1 := mul_inv_cancel₀ (by exact_mod_cast hd.ne')
    · intro t ht
      rcases mem_filter.mp ht with ⟨htF, het⟩
      exact mem_filter.mpr
        ⟨SimpleGraph.mem_cliqueFinset_iff.mpr (htri t htF), het⟩
    · intro t htBig htSmall
      have htF : t ∉ F := by
        intro htF
        exact htSmall (mem_filter.mpr ⟨htF, (mem_filter.mp htBig).2⟩)
      simp [constantTriangleFamilyWeight, htF]

/-- Total weight of a constant triangle family whose members are all graph
triangles. -/
lemma fractionalSize_constantTriangleFamilyWeight
    {G : SimpleGraph α} {F : Finset (Finset α)} {d : ℕ}
    (htri : ∀ t ∈ F, G.IsNClique 3 t) :
    fractionalSize G (constantTriangleFamilyWeight F d) =
      (F.card : ℝ) * (d : ℝ)⁻¹ := by
  classical
  unfold fractionalSize
  rw [← sum_subset (s₁ := F) (s₂ := G.cliqueFinset 3)]
  · simp [constantTriangleFamilyWeight]
  · intro t ht
    exact SimpleGraph.mem_cliqueFinset_iff.mpr (htri t ht)
  · intro t _htG htF
    simp [constantTriangleFamilyWeight, htF]

/-- All triangles obtained by attaching `z` to a two-element subset of
`A`.  When `z ∉ A`, the indexing pair is recovered by erasing `z`. -/
def cliqueStarTriangleFamily (z : α) (A : Finset α) :
    Finset (Finset α) :=
  (A.powersetCard 2).image (insert z)

lemma card_cliqueStarTriangleFamily
    {z : α} {A : Finset α} (hzA : z ∉ A) :
    (cliqueStarTriangleFamily z A).card = A.card.choose 2 := by
  classical
  have hinj : Set.InjOn (insert z) (A.powersetCard 2 : Set (Finset α)) := by
    intro p hp q hq hpq
    have hzp : z ∉ p := fun hzp ↦ hzA ((mem_powersetCard.mp hp).1 hzp)
    have hzq : z ∉ q := fun hzq ↦ hzA ((mem_powersetCard.mp hq).1 hzq)
    have hers := congrArg (fun t : Finset α ↦ t.erase z) hpq
    simpa [hzp, hzq] using hers
  unfold cliqueStarTriangleFamily
  rw [card_image_of_injOn hinj, card_powersetCard]

/-- A uniform star over a clique on one side consists entirely of eligible
internal-edge/cross triangles. -/
lemma cliqueStarTriangleFamily_subset_internalCrossTriangles
    {G : SimpleGraph α} {s : Set α} {z : α} {A : Finset α}
    (hA : G.IsClique (A : Set α))
    (hAs : ∀ x ∈ A, x ∈ s) (hzside : z ∉ s)
    (hzA : ∀ x ∈ A, G.Adj z x) :
    cliqueStarTriangleFamily z A ⊆ internalCrossTriangles G s := by
  classical
  intro t ht
  obtain ⟨p, hp, rfl⟩ := mem_image.mp ht
  rcases mem_powersetCard.mp hp with ⟨hpA, hpcard⟩
  obtain ⟨u, v, huv, rfl⟩ := card_eq_two.mp hpcard
  have huA : u ∈ A := hpA (by simp)
  have hvA : v ∈ A := hpA (by simp)
  exact insert_mem_internalCrossTriangles_of_opposite
    (hA huA hvA huv) (by simp [hAs u huA, hAs v hvA])
      (by simp [hzside, hAs u huA]) (hzA u huA) (hzA v hvA)

/-- An edge occurs in at most `|A|-1` triangles of the complete star over
`A`.  If the edge contains the attachment, one base vertex is prescribed;
otherwise both base vertices are prescribed. -/
lemma card_filter_cliqueStarTriangleFamily_le
    {z : α} {A : Finset α} (hAcard : 2 ≤ A.card) (hzA : z ∉ A)
    (e : Sym2 α) (hecard : e.toFinset.card = 2) :
    ((cliqueStarTriangleFamily z A).filter fun t ↦ e ∈ t.sym2).card ≤
      A.card - 1 := by
  classical
  let D := e.toFinset \ {z}
  let S := (A.powersetCard 2).filter fun p ↦ D ⊆ p
  by_cases hempty :
      ((cliqueStarTriangleFamily z A).filter fun t ↦ e ∈ t.sym2) = ∅
  · change
      ((cliqueStarTriangleFamily z A).filter fun t ↦ e ∈ t.sym2).card ≤
        A.card - 1
    rw [hempty]
    simp
  have hnonempty :
      ((cliqueStarTriangleFamily z A).filter fun t ↦ e ∈ t.sym2).Nonempty :=
    nonempty_iff_ne_empty.mpr hempty
  obtain ⟨t, ht⟩ := hnonempty
  rcases mem_filter.mp ht with ⟨htFamily, het⟩
  obtain ⟨p, hp, htp⟩ := mem_image.mp htFamily
  have hpA : p ⊆ A := (mem_powersetCard.mp hp).1
  have hDsubP : D ⊆ p := by
    intro x hxD
    have hxe : x ∈ e := by simpa [D] using (mem_sdiff.mp hxD).1
    have hxt : x ∈ t := (mem_sym2_iff.mp het) x hxe
    have hxInsert : x ∈ insert z p := by simpa [htp] using hxt
    rcases mem_insert.mp hxInsert with hxz | hxp
    · exact ((mem_sdiff.mp hxD).2 (by simpa [hxz])).elim
    · exact hxp
  have hDsubA : D ⊆ A := hDsubP.trans hpA
  have hDcardLe : D.card ≤ 2 := by
    exact (card_le_card sdiff_subset).trans_eq hecard
  have hInter : (e.toFinset ∩ {z}).card ≤ 1 := by
    calc
      (e.toFinset ∩ {z}).card ≤ ({z} : Finset α).card :=
        card_le_card inter_subset_right
      _ = 1 := card_singleton z
  have hpartition := card_sdiff_add_card_inter e.toFinset {z}
  have hDcardPos : 1 ≤ D.card := by
    change 1 ≤ (e.toFinset \ {z}).card
    omega
  have hsub :
      (cliqueStarTriangleFamily z A).filter (fun t ↦ e ∈ t.sym2) ⊆
        S.image (insert z) := by
    intro u hu
    rcases mem_filter.mp hu with ⟨huFamily, heu⟩
    obtain ⟨q, hq, rfl⟩ := mem_image.mp huFamily
    apply mem_image.mpr
    refine ⟨q, mem_filter.mpr ⟨hq, ?_⟩, rfl⟩
    intro x hxD
    have hxe : x ∈ e := by simpa [D] using (mem_sdiff.mp hxD).1
    have hxInsert : x ∈ insert z q := (mem_sym2_iff.mp heu) x hxe
    rcases mem_insert.mp hxInsert with hxz | hxq
    · exact ((mem_sdiff.mp hxD).2 (by simpa [hxz])).elim
    · exact hxq
  have hfamilyLe :
      ((cliqueStarTriangleFamily z A).filter fun t ↦ e ∈ t.sym2).card ≤
        S.card := by
    exact (card_le_card hsub).trans (card_image_le)
  have hScard : S.card = Nat.choose (A.card - D.card) (2 - D.card) := by
    exact card_filter_powersetCard_subset D A 2 hDsubA hDcardLe
  have hSle : S.card ≤ A.card - 1 := by
    rw [hScard]
    by_cases hDone : D.card = 1
    · simp [hDone]
    · have hDtwo : D.card = 2 := by omega
      simp [hDtwo]
      omega
  exact hfamilyLe.trans hSle

/-- A clique of at least two vertices has a perfect fractional matching:
put weight `1/(|A|-1)` on every pair and attach the opposite-side vertex
`z`.  The resulting cross-triangle packing has total weight `|A|/2`, with
no parity loss. -/
lemma uniformCliqueStar_isFractionalInternalCrossPacking
    {G : SimpleGraph α} {s : Set α} {z : α} {A : Finset α}
    (hAcard : 2 ≤ A.card)
    (hA : G.IsClique (A : Set α))
    (hAs : ∀ x ∈ A, x ∈ s) (hzside : z ∉ s)
    (hzA : ∀ x ∈ A, G.Adj z x) :
    let w := constantTriangleFamilyWeight
      (cliqueStarTriangleFamily z A) (A.card - 1)
    IsFractionalInternalCrossPacking G s w ∧
      2 * fractionalSize G w = (A.card : ℝ) := by
  classical
  intro w
  have hzAset : z ∉ A := fun hzA' ↦ hzside (hAs z hzA')
  have hcross := cliqueStarTriangleFamily_subset_internalCrossTriangles
    hA hAs hzside hzA
  have htri : ∀ t ∈ cliqueStarTriangleFamily z A, G.IsNClique 3 t := by
    intro t ht
    exact (mem_internalCrossTriangles.mp (hcross ht)).1
  have hd : 0 < A.card - 1 := by omega
  have hload : ∀ e ∈ G.edgeFinset,
      ((cliqueStarTriangleFamily z A).filter fun t ↦ e ∈ t.sym2).card ≤
        A.card - 1 := by
    intro e he
    exact card_filter_cliqueStarTriangleFamily_le hAcard hzAset e
      (SimpleGraph.card_toFinset_mem_edgeFinset ⟨e, he⟩)
  have hwPacking : IsFractionalPacking G w := by
    exact isFractionalPacking_constantTriangleFamilyWeight hd htri hload
  have hwSupport : ∀ t : Finset α,
      t ∉ internalCrossTriangles G s → w t = 0 := by
    intro t ht
    simp only [w, constantTriangleFamilyWeight]
    split
    · rename_i htFamily
      exact (ht (hcross htFamily)).elim
    · rfl
  refine ⟨⟨hwPacking, hwSupport⟩, ?_⟩
  rw [fractionalSize_constantTriangleFamilyWeight htri,
    card_cliqueStarTriangleFamily hzAset, Nat.cast_choose_two]
  have hcast : (((A.card - 1 : ℕ) : ℝ)) = (A.card : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega)]
    norm_num
  rw [hcast]
  have hne : (A.card : ℝ) - 1 ≠ 0 := by
    have : (2 : ℝ) ≤ A.card := by exact_mod_cast hAcard
    linarith
  field_simp [hne]
  <;> ring

/-- A clique star based in `s` puts no load on an edge internal to the
opposite side.  This oriented-support refinement is needed only in the
`n = 24` boundary of the capacity-safe correction to Proposition 4.2. -/
lemma uniformCliqueStar_complSide_edgeLoad_eq_zero
    {G : SimpleGraph α} {s : Set α} {z : α} {A : Finset α} {d : ℕ}
    (hAs : ∀ x ∈ A, x ∈ s) (hzside : z ∉ s)
    {e : Sym2 α} (he : e ∈ sideEdgeFinset G sᶜ.toFinset) :
    fractionalEdgeLoad G
      (constantTriangleFamilyWeight (cliqueStarTriangleFamily z A) d) e = 0 := by
  classical
  unfold fractionalEdgeLoad
  apply sum_eq_zero
  intro t ht
  by_cases htFamily : t ∈ cliqueStarTriangleFamily z A
  · have het : e ∈ t.sym2 := (mem_filter.mp ht).2
    obtain ⟨p, hp, rfl⟩ := mem_image.mp htFamily
    have hpA : p ⊆ A := (mem_powersetCard.mp hp).1
    have heSub : e.toFinset ⊆ insert z p := by
      intro x hxe
      have hxe' : x ∈ e := by simpa using hxe
      exact (mem_sym2_iff.mp het) x hxe'
    have heSubSingleton : e.toFinset ⊆ {z} := by
      intro x hxe
      rcases mem_insert.mp (heSub hxe) with rfl | hxp
      · simp
      · have hxA : x ∈ A := hpA hxp
        have hxComp : x ∈ sᶜ.toFinset := (mem_filter.mp he).2 hxe
        have hxNot : x ∉ s := by simpa using hxComp
        exact (hxNot (hAs x hxA)).elim
    have hecard : e.toFinset.card = 2 :=
      SimpleGraph.card_toFinset_mem_edgeFinset ⟨e, (mem_filter.mp he).1⟩
    have hle := card_le_card heSubSingleton
    simp only [card_singleton] at hle
    omega
  · simp [constantTriangleFamilyWeight, htFamily]

/-- If a weight is supported on a triangle family none of whose members
contains `e`, then its load on `e` is zero. -/
lemma fractionalEdgeLoad_eq_zero_of_family_avoids
    {G : SimpleGraph α} {F : Finset (Finset α)}
    {w : Finset α → ℝ} {e : Sym2 α}
    (hsupport : ∀ t, t ∉ F → w t = 0)
    (havoid : ∀ t ∈ F, e ∉ t.sym2) :
    fractionalEdgeLoad G w e = 0 := by
  classical
  unfold fractionalEdgeLoad
  apply sum_eq_zero
  intro t ht
  by_cases htF : t ∈ F
  · exact (havoid t htF (mem_filter.mp ht).2).elim
  · exact hsupport t htF

/-- Fractional triangle packings supported on cross-edge-disjoint families
may be added.  The intersection hypothesis is the weighted analogue of the
usual certificate for uniting two integral triangle packings. -/
lemma isFractionalPacking_add_of_cross_inter_card_le_one
    {G : SimpleGraph α} {F Q : Finset (Finset α)}
    {wF wQ : Finset α → ℝ}
    (hwF : IsFractionalPacking G wF)
    (hwQ : IsFractionalPacking G wQ)
    (hsupportF : ∀ t, t ∉ F → wF t = 0)
    (hsupportQ : ∀ t, t ∉ Q → wQ t = 0)
    (hcross : ∀ t ∈ F, ∀ u ∈ Q, (t ∩ u).card ≤ 1) :
    IsFractionalPacking G (addTriangleWeight wF wQ) := by
  classical
  constructor
  · intro t ht
    exact add_nonneg (hwF.nonneg_on ht) (hwQ.nonneg_on ht)
  · intro e he
    rw [show addTriangleWeight wF wQ = (fun t ↦ wF t + wQ t) by rfl,
      fractionalEdgeLoad_add]
    by_cases hex : ∃ t ∈ F, e ∈ t.sym2
    · obtain ⟨t, htF, het⟩ := hex
      have hQavoid : ∀ u ∈ Q, e ∉ u.sym2 := by
        intro u huQ heu
        have hesub : e.toFinset ⊆ t ∩ u := by
          intro x hxe
          have hxe' : x ∈ e := by simpa using hxe
          exact mem_inter.mpr ⟨(mem_sym2_iff.mp het) x hxe',
            (mem_sym2_iff.mp heu) x hxe'⟩
        have hecard : e.toFinset.card = 2 :=
          SimpleGraph.card_toFinset_mem_edgeFinset ⟨e, he⟩
        have hcard := card_le_card hesub
        have hinter := hcross t htF u huQ
        omega
      rw [fractionalEdgeLoad_eq_zero_of_family_avoids
        hsupportQ hQavoid, add_zero]
      exact hwF.edgeLoad_le_one he
    · have hFavoid : ∀ t ∈ F, e ∉ t.sym2 := by
        intro t htF het
        exact hex ⟨t, htF, het⟩
      rw [fractionalEdgeLoad_eq_zero_of_family_avoids
        hsupportF hFavoid, zero_add]
      exact hwQ.edgeLoad_le_one he

/-- The envelopes of two star families with disjoint bases in one side and
different attachment vertices in the other side are disjoint. -/
lemma cliqueStarTriangleFamilies_cross_inter_eq_empty
    {s : Set α} {A B : Finset α} {z w : α}
    (hAB : Disjoint A B)
    (hAs : ∀ x ∈ A, x ∈ s) (hBs : ∀ x ∈ B, x ∈ s)
    (hzside : z ∉ s) (hwside : w ∉ s) (hzw : z ≠ w) :
    ∀ t ∈ cliqueStarTriangleFamily z A,
      ∀ u ∈ cliqueStarTriangleFamily w B, t ∩ u = ∅ := by
  classical
  intro t ht u hu
  obtain ⟨p, hp, rfl⟩ := mem_image.mp ht
  obtain ⟨q, hq, rfl⟩ := mem_image.mp hu
  have hpA : p ⊆ A := (mem_powersetCard.mp hp).1
  have hqB : q ⊆ B := (mem_powersetCard.mp hq).1
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro x hx
  rcases mem_inter.mp hx with ⟨hxp, hxq⟩
  rcases mem_insert.mp hxp with hxz | hxp
  · subst x
    rcases mem_insert.mp hxq with hzw' | hzq
    · exact hzw hzw'
    · exact hzside (hBs z (hqB hzq))
  · rcases mem_insert.mp hxq with hxw | hxq
    · subst x
      exact hwside (hAs w (hpA hxp))
    · exact Finset.disjoint_left.mp hAB (hpA hxp) (hqB hxq)

/-- Two non-singleton red neighbourhood cliques attached to the endpoints
of an uncovered blue edge give a fractional cross packing of exact doubled
weight `|A|+|B|`. -/
lemma twoUniformCliqueStars_isFractionalInternalCrossPacking
    {G : SimpleGraph α} {s : Set α} {A B : Finset α} {z w : α}
    (hAcard : 2 ≤ A.card) (hBcard : 2 ≤ B.card)
    (hA : G.IsClique (A : Set α)) (hB : G.IsClique (B : Set α))
    (hAB : Disjoint A B)
    (hAs : ∀ x ∈ A, x ∈ s) (hBs : ∀ x ∈ B, x ∈ s)
    (hzside : z ∉ s) (hwside : w ∉ s) (hzw : z ≠ w)
    (hzA : ∀ x ∈ A, G.Adj z x)
    (hwB : ∀ x ∈ B, G.Adj w x) :
    let wA := constantTriangleFamilyWeight
      (cliqueStarTriangleFamily z A) (A.card - 1)
    let wB := constantTriangleFamilyWeight
      (cliqueStarTriangleFamily w B) (B.card - 1)
    IsFractionalInternalCrossPacking G s (addTriangleWeight wA wB) ∧
      2 * fractionalSize G (addTriangleWeight wA wB) =
        ((A.card + B.card : ℕ) : ℝ) := by
  classical
  intro wA wB
  have hwA := uniformCliqueStar_isFractionalInternalCrossPacking
    hAcard hA hAs hzside hzA
  have hwB := uniformCliqueStar_isFractionalInternalCrossPacking
    hBcard hB hBs hwside hwB
  have hsupportA : ∀ t, t ∉ cliqueStarTriangleFamily z A → wA t = 0 := by
    intro t ht
    simp [wA, constantTriangleFamilyWeight, ht]
  have hsupportB : ∀ t, t ∉ cliqueStarTriangleFamily w B → wB t = 0 := by
    intro t ht
    simp [wB, constantTriangleFamilyWeight, ht]
  have hcross : ∀ t ∈ cliqueStarTriangleFamily z A,
      ∀ u ∈ cliqueStarTriangleFamily w B, (t ∩ u).card ≤ 1 := by
    intro t ht u hu
    rw [cliqueStarTriangleFamilies_cross_inter_eq_empty
      hAB hAs hBs hzside hwside hzw t ht u hu]
    simp
  have hpack : IsFractionalPacking G (addTriangleWeight wA wB) :=
    isFractionalPacking_add_of_cross_inter_card_le_one
      hwA.1.1 hwB.1.1 hsupportA hsupportB hcross
  have hsupport : ∀ t : Finset α, t ∉ internalCrossTriangles G s →
      addTriangleWeight wA wB t = 0 := by
    intro t ht
    have hwAt : wA t = 0 := hwA.1.2 t ht
    have hwBt : wB t = 0 := hwB.1.2 t ht
    change wA t + wB t = 0
    rw [hwAt, hwBt, zero_add]
  refine ⟨⟨hpack, hsupport⟩, ?_⟩
  rw [fractionalSize_addTriangleWeight]
  push_cast
  linarith [hwA.2, hwB.2]

/-- The oriented two-star witness used in the `n = 24` boundary of the
capacity-safe Proposition 4.2 argument. -/
lemma exists_oriented_saturatedSideCrossPacking_nine_halves
    {G : SimpleGraph α} {s : Set α} {M : Finset (Sym2 α)}
    (hM : IsCrossMatching s M) {P : Finset (Finset α)}
    (hP : IsInternalCrossPacking
      (G.deleteEdges (M : Set (Sym2 α))) s P)
    (hPmax : ∀ Q : Finset (Finset α),
      IsInternalCrossPacking (G.deleteEdges (M : Set (Sym2 α))) s Q →
        Q.card ≤ P.card)
    (hcover : ∀ e ∈ sideEdgeFinset G s.toFinset,
      e ∈ coveredInternalEdges G s P)
    {a b : α} (he : s(a, b) ∈ sideEdgeFinset G sᶜ.toFinset)
    (heUncovered : s(a, b) ∉ coveredInternalEdges
      (G.deleteEdges (M : Set (Sym2 α))) s P)
    (hm : P.card = 0) (hsidecard : 13 ≤ s.toFinset.card) :
    ∃ q : Finset α → ℝ,
      IsFractionalInternalCrossPacking Gᶜ s q ∧
      (9 : ℝ) ≤ 2 * fractionalSize Gᶜ q ∧
      ∀ e ∈ sideEdgeFinset Gᶜ sᶜ.toFinset,
        fractionalEdgeLoad Gᶜ q e = 0 := by
  classical
  rcases proposition42_claim44_edgeFacts hM hP he heUncovered with
    ⟨habG, has, hbs, _heInternal, _hP_G, _heUncoveredG⟩
  obtain ⟨A, B, hA, hB, hAB, hAs, hBs, haA, hbB, hcount⟩ :=
    proposition42_claim44_sideCliques hM hP hPmax hcover he heUncovered
  have hsum : 11 ≤ A.card + B.card := by omega
  by_cases hAcard : 2 ≤ A.card
  · by_cases hBcard : 2 ≤ B.card
    · let wA := constantTriangleFamilyWeight
        (cliqueStarTriangleFamily a A) (A.card - 1)
      let wB := constantTriangleFamilyWeight
        (cliqueStarTriangleFamily b B) (B.card - 1)
      let q := addTriangleWeight wA wB
      have hq := twoUniformCliqueStars_isFractionalInternalCrossPacking
        (G := Gᶜ) (s := s) (A := A) (B := B) (z := a) (w := b)
        hAcard hBcard hA hB hAB hAs hBs has hbs habG.ne haA hbB
      refine ⟨q, by simpa only [q, wA, wB] using hq.1, ?_, ?_⟩
      · have h9 : (9 : ℝ) ≤ ((A.card + B.card : ℕ) : ℝ) := by
          exact_mod_cast (by omega : 9 ≤ A.card + B.card)
        exact h9.trans_eq (by simpa only [q, wA, wB] using hq.2.symm)
      · intro e heOpp
        change fractionalEdgeLoad Gᶜ (fun t ↦ wA t + wB t) e = 0
        rw [fractionalEdgeLoad_add,
          uniformCliqueStar_complSide_edgeLoad_eq_zero hAs has heOpp,
          uniformCliqueStar_complSide_edgeLoad_eq_zero hBs hbs heOpp,
          zero_add]
    · have hA9 : 9 ≤ A.card := by omega
      let q := constantTriangleFamilyWeight
        (cliqueStarTriangleFamily a A) (A.card - 1)
      have hq := uniformCliqueStar_isFractionalInternalCrossPacking
        (G := Gᶜ) (s := s) (z := a) (A := A) hAcard hA hAs has haA
      refine ⟨q, by simpa only [q] using hq.1, ?_, ?_⟩
      · have h9 : (9 : ℝ) ≤ (A.card : ℝ) := by exact_mod_cast hA9
        exact h9.trans_eq (by simpa only [q] using hq.2.symm)
      · intro e heOpp
        exact uniformCliqueStar_complSide_edgeLoad_eq_zero hAs has heOpp
  · have hBcard : 2 ≤ B.card := by omega
    have hB9 : 9 ≤ B.card := by omega
    let q := constantTriangleFamilyWeight
      (cliqueStarTriangleFamily b B) (B.card - 1)
    have hq := uniformCliqueStar_isFractionalInternalCrossPacking
      (G := Gᶜ) (s := s) (z := b) (A := B) hBcard hB hBs hbs hbB
    refine ⟨q, by simpa only [q] using hq.1, ?_, ?_⟩
    · have h9 : (9 : ℝ) ≤ (B.card : ℝ) := by exact_mod_cast hB9
      exact h9.trans_eq (by simpa only [q] using hq.2.symm)
    · intro e heOpp
      exact uniformCliqueStar_complSide_edgeLoad_eq_zero hBs hbs heOpp

/-- LP comparison form of the exact two-uniform-star construction. -/
lemma twoUniformCliqueStars_card_le_maximal
    {G : SimpleGraph α} {s : Set α} {A B : Finset α} {z w : α}
    {weight : Finset α → ℝ}
    (hmax : ∀ q : Finset α → ℝ,
      IsFractionalInternalCrossPacking G s q →
        fractionalSize G q ≤ fractionalSize G weight)
    (hAcard : 2 ≤ A.card) (hBcard : 2 ≤ B.card)
    (hA : G.IsClique (A : Set α)) (hB : G.IsClique (B : Set α))
    (hAB : Disjoint A B)
    (hAs : ∀ x ∈ A, x ∈ s) (hBs : ∀ x ∈ B, x ∈ s)
    (hzside : z ∉ s) (hwside : w ∉ s) (hzw : z ≠ w)
    (hzA : ∀ x ∈ A, G.Adj z x)
    (hwB : ∀ x ∈ B, G.Adj w x) :
    (((A.card + B.card : ℕ) : ℝ)) ≤
      2 * fractionalSize G weight := by
  let wA := constantTriangleFamilyWeight
    (cliqueStarTriangleFamily z A) (A.card - 1)
  let wB := constantTriangleFamilyWeight
    (cliqueStarTriangleFamily w B) (B.card - 1)
  let q := addTriangleWeight wA wB
  have hq := twoUniformCliqueStars_isFractionalInternalCrossPacking
    hAcard hBcard hA hB hAB hAs hBs hzside hwside hzw hzA hwB
  have hqmax : fractionalSize G q ≤ fractionalSize G weight := by
    exact hmax q hq.1
  dsimp only [q, wA, wB] at hqmax ⊢
  linarith [hq.2]

/-- If the two red neighbourhoods contain at least three vertices in total,
the singleton obstruction costs at most one vertex.  This is the precise
refinement invoked in Claim 4.4 when the maximal blue packing has size one. -/
lemma twoCliqueStars_card_sub_one_le_maximal
    {G : SimpleGraph α} {s : Set α} {A B : Finset α} {z w : α}
    {weight : Finset α → ℝ}
    (hmax : ∀ q : Finset α → ℝ,
      IsFractionalInternalCrossPacking G s q →
        fractionalSize G q ≤ fractionalSize G weight)
    (hcard : 3 ≤ A.card + B.card)
    (hA : G.IsClique (A : Set α)) (hB : G.IsClique (B : Set α))
    (hAB : Disjoint A B)
    (hAs : ∀ x ∈ A, x ∈ s) (hBs : ∀ x ∈ B, x ∈ s)
    (hzside : z ∉ s) (hwside : w ∉ s) (hzw : z ≠ w)
    (hzA : ∀ x ∈ A, G.Adj z x)
    (hwB : ∀ x ∈ B, G.Adj w x) :
    (((A.card + B.card : ℕ) : ℝ)) - 1 ≤
      2 * fractionalSize G weight := by
  by_cases hAcard : 2 ≤ A.card
  · by_cases hBcard : 2 ≤ B.card
    · have hboth := twoUniformCliqueStars_card_le_maximal hmax
        hAcard hBcard hA hB hAB hAs hBs hzside hwside hzw hzA hwB
      linarith
    · have hBle : B.card ≤ 1 := by omega
      let q := constantTriangleFamilyWeight
        (cliqueStarTriangleFamily z A) (A.card - 1)
      have hq := uniformCliqueStar_isFractionalInternalCrossPacking
        hAcard hA hAs hzside hzA
      have hqmax : fractionalSize G q ≤ fractionalSize G weight :=
        hmax q hq.1
      have hBleR : (B.card : ℝ) ≤ 1 := by exact_mod_cast hBle
      push_cast
      dsimp only [q] at hqmax
      linarith [hq.2]
  · have hAle : A.card ≤ 1 := by omega
    have hBlarge : 2 ≤ B.card := by omega
    let q := constantTriangleFamilyWeight
      (cliqueStarTriangleFamily w B) (B.card - 1)
    have hq := uniformCliqueStar_isFractionalInternalCrossPacking
      hBlarge hB hBs hwside hwB
    have hqmax : fractionalSize G q ≤ fractionalSize G weight :=
      hmax q hq.1
    have hAleR : (A.card : ℝ) ≤ 1 := by exact_mod_cast hAle
    push_cast
    dsimp only [q] at hqmax
    linarith [hq.2]

/-- The complete `m = 1` branch of Claim 4.4.  Proposition 4.1 gives at
least seven vertices on the saturated side.  After the two packing-support
vertices and two forbidden matching partners are removed, the two red
neighbourhood cliques have at least three vertices in total, so only one
singleton loss is possible. -/
lemma proposition42_claim44_eq_one
    {G : SimpleGraph α} {s : Set α} {M : Finset (Sym2 α)}
    (hM : IsCrossMatching s M)
    {P : Finset (Finset α)}
    (hP : IsInternalCrossPacking
      (G.deleteEdges (M : Set (Sym2 α))) s P)
    (hPmax : ∀ Q : Finset (Finset α),
      IsInternalCrossPacking (G.deleteEdges (M : Set (Sym2 α))) s Q →
        Q.card ≤ P.card)
    (hcover : ∀ e ∈ sideEdgeFinset G s.toFinset,
      e ∈ coveredInternalEdges G s P)
    {a b : α}
    (he : s(a, b) ∈ sideEdgeFinset G sᶜ.toFinset)
    (heUncovered : s(a, b) ∉ coveredInternalEdges
      (G.deleteEdges (M : Set (Sym2 α))) s P)
    {w : Finset α → ℝ}
    (hwmax : ∀ q : Finset α → ℝ,
      IsFractionalInternalCrossPacking Gᶜ s q →
        fractionalSize Gᶜ q ≤ fractionalSize Gᶜ w)
    (hm : P.card = 1) (hseven : 7 ≤ s.toFinset.card) :
    (s.toFinset.card : ℝ) - 3 * (P.card : ℝ) - 2 ≤
      2 * fractionalSize Gᶜ w := by
  classical
  rcases proposition42_claim44_edgeFacts hM hP he heUncovered with
    ⟨habG, has, hbs, _heInternal, _hP_G, _heUncoveredG⟩
  obtain ⟨A, B, hA, hB, hAB, hAs, hBs, haA, hbB, hcount⟩ :=
    proposition42_claim44_sideCliques hM hP hPmax hcover he heUncovered
  have hABcard : 3 ≤ A.card + B.card := by omega
  have hred := twoCliqueStars_card_sub_one_le_maximal
    (G := Gᶜ) (s := s) (A := A) (B := B) (z := a) (w := b)
      hwmax hABcard hA hB hAB hAs hBs has hbs habG.ne haA hbB
  have hcountR : (s.toFinset.card : ℝ) ≤
      ((A.card + B.card : ℕ) : ℝ) + 2 * (P.card : ℝ) + 2 := by
    exact_mod_cast hcount
  have hmR : (P.card : ℝ) = 1 := by exact_mod_cast hm
  linarith

/-! #### The exceptional `m = 0` case of Claim 4.4 -/

/-- If an edge does not contain the attachment of a complete star, it
determines its two base vertices and hence occurs in at most one member of
the star. -/
lemma card_filter_cliqueStarTriangleFamily_le_one_of_attachment_not_mem
    {z : α} {A : Finset α} (hzA : z ∉ A)
    (e : Sym2 α) (hecard : e.toFinset.card = 2)
    (hze : z ∉ e.toFinset) :
    ((cliqueStarTriangleFamily z A).filter fun t ↦ e ∈ t.sym2).card ≤ 1 := by
  classical
  rw [card_le_one]
  intro t ht u hu
  rcases mem_filter.mp ht with ⟨htStar, het⟩
  rcases mem_filter.mp hu with ⟨huStar, heu⟩
  obtain ⟨p, hp, rfl⟩ := mem_image.mp htStar
  obtain ⟨q, hq, rfl⟩ := mem_image.mp huStar
  have hesubp : e.toFinset ⊆ p := by
    intro x hxe
    have hxe' : x ∈ e := by simpa using hxe
    have hx : x ∈ insert z p := (mem_sym2_iff.mp het) x hxe'
    rcases mem_insert.mp hx with hxz | hxp
    · exact (hze (by simpa [hxz] using hxe)).elim
    · exact hxp
  have hesubq : e.toFinset ⊆ q := by
    intro x hxe
    have hxe' : x ∈ e := by simpa using hxe
    have hx : x ∈ insert z q := (mem_sym2_iff.mp heu) x hxe'
    rcases mem_insert.mp hx with hxz | hxq
    · exact (hze (by simpa [hxz] using hxe)).elim
    · exact hxq
  have hpcard : p.card = 2 := (mem_powersetCard.mp hp).2
  have hqcard : q.card = 2 := (mem_powersetCard.mp hq).2
  have hep : e.toFinset = p := by
    apply eq_of_subset_of_card_le hesubp
    omega
  have heq : e.toFinset = q := by
    apply eq_of_subset_of_card_le hesubq
    omega
  rw [← hep, ← heq]

/-- A star family avoids every edge containing a vertex different from its
attachment and outside its base. -/
lemma filter_cliqueStarTriangleFamily_eq_empty_of_contains_avoided
    {z x : α} {A : Finset α} (hxz : x ≠ z) (hxA : x ∉ A)
    (e : Sym2 α) (hxe : x ∈ e.toFinset) :
    (cliqueStarTriangleFamily z A).filter (fun t ↦ e ∈ t.sym2) = ∅ := by
  classical
  apply eq_empty_iff_forall_notMem.mpr
  intro t ht
  rcases mem_filter.mp ht with ⟨htStar, het⟩
  obtain ⟨p, hp, rfl⟩ := mem_image.mp htStar
  have hxe' : x ∈ e := by simpa using hxe
  have hx : x ∈ insert z p := (mem_sym2_iff.mp het) x hxe'
  rcases mem_insert.mp hx with hxz' | hxp
  · exact hxz hxz'
  · exact hxA ((mem_powersetCard.mp hp).1 hxp)

/-- LP comparison for one perfect fractional clique star. -/
lemma uniformCliqueStar_card_le_maximal
    {G : SimpleGraph α} {s : Set α} {A : Finset α} {z : α}
    {weight : Finset α → ℝ}
    (hmax : ∀ q : Finset α → ℝ,
      IsFractionalInternalCrossPacking G s q →
        fractionalSize G q ≤ fractionalSize G weight)
    (hAcard : 2 ≤ A.card) (hA : G.IsClique (A : Set α))
    (hAs : ∀ x ∈ A, x ∈ s) (hzside : z ∉ s)
    (hzA : ∀ x ∈ A, G.Adj z x) :
    (A.card : ℝ) ≤ 2 * fractionalSize G weight := by
  let q := constantTriangleFamilyWeight
    (cliqueStarTriangleFamily z A) (A.card - 1)
  have hq := uniformCliqueStar_isFractionalInternalCrossPacking
    hAcard hA hAs hzside hzA
  have hqmax := hmax q hq.1
  dsimp only [q] at hqmax
  linarith [hq.2]

/-- Empty cliques have no loss, and every non-singleton clique has a perfect
fractional matching.  Thus two successive red neighbourhoods lose nothing
provided neither has cardinality one. -/
lemma twoCliqueStars_no_singleton_card_le_maximal
    {G : SimpleGraph α} {s : Set α} {A B : Finset α} {z w : α}
    {weight : Finset α → ℝ}
    (hmax : ∀ q : Finset α → ℝ,
      IsFractionalInternalCrossPacking G s q →
        fractionalSize G q ≤ fractionalSize G weight)
    (hAone : A.card ≠ 1) (hBone : B.card ≠ 1)
    (hA : G.IsClique (A : Set α)) (hB : G.IsClique (B : Set α))
    (hAB : Disjoint A B)
    (hAs : ∀ x ∈ A, x ∈ s) (hBs : ∀ x ∈ B, x ∈ s)
    (hzside : z ∉ s) (hwside : w ∉ s) (hzw : z ≠ w)
    (hzA : ∀ x ∈ A, G.Adj z x)
    (hwB : ∀ x ∈ B, G.Adj w x) :
    (((A.card + B.card : ℕ) : ℝ)) ≤
      2 * fractionalSize G weight := by
  by_cases hA0 : A.card = 0
  · by_cases hB0 : B.card = 0
    · have hzero := hmax (fun _t : Finset α ↦ (0 : ℝ))
          ⟨isFractionalPacking_zero G, by simp⟩
      have hsize_nonneg : 0 ≤ fractionalSize G weight := by
        simpa only [fractionalSize_zero] using hzero
      calc
        ((A.card + B.card : ℕ) : ℝ) = 0 := by
          simp only [hA0, hB0, add_zero, Nat.cast_zero]
        _ ≤ 2 * fractionalSize G weight :=
          mul_nonneg (by norm_num) hsize_nonneg
    · have hB2 : 2 ≤ B.card := by omega
      have hred := uniformCliqueStar_card_le_maximal
        hmax hB2 hB hBs hwside hwB
      push_cast
      simpa only [hA0, Nat.cast_zero, zero_add] using hred
  · have hA2 : 2 ≤ A.card := by omega
    by_cases hB0 : B.card = 0
    · have hred := uniformCliqueStar_card_le_maximal
        hmax hA2 hA hAs hzside hzA
      push_cast
      simpa only [hB0, Nat.cast_zero, add_zero] using hred
    · have hB2 : 2 ≤ B.card := by omega
      exact twoUniformCliqueStars_card_le_maximal hmax hA2 hB2
        hA hB hAB hAs hBs hzside hwside hzw hzA hwB

/-- If the desired `m = 0` lower bound fails for one uncovered blue edge,
the paper's two successive red neighbourhoods must have the unique bad
shape: after orienting the edge, the first has exactly `|s|-3` vertices and
the second is a singleton. -/
lemma claim44_bad_structure_of_lower_bound_failure
    {G : SimpleGraph α} {s : Set α} {M : Finset (Sym2 α)}
    (hM : IsCrossMatching s M)
    {a b : α} (habG : G.Adj a b) (has : a ∉ s) (hbs : b ∉ s)
    (hclique : Gᶜ.IsClique (s.toFinset : Set α))
    (hcommon : ∀ x ∈ s.toFinset,
      ¬ ((G.deleteEdges (M : Set (Sym2 α))).Adj a x ∧
        (G.deleteEdges (M : Set (Sym2 α))).Adj b x))
    {weight : Finset α → ℝ}
    (hmax : ∀ q : Finset α → ℝ,
      IsFractionalInternalCrossPacking Gᶜ s q →
        fractionalSize Gᶜ q ≤ fractionalSize Gᶜ weight)
    (hseven : 7 ≤ s.toFinset.card)
    (hfail : ¬ ((s.toFinset.card : ℝ) - 2 ≤
      2 * fractionalSize Gᶜ weight)) :
    ∃ z y : α,
      s(z, y) = s(a, b) ∧ z ∉ s ∧ y ∉ s ∧ G.Adj z y ∧
      let A := redNeighborFinset G z s.toFinset
      let B := redNeighborFinset G y (s.toFinset \ A)
      A.card = s.toFinset.card - 3 ∧ B.card = 1 := by
  classical
  let A := redNeighborFinset G a s.toFinset
  let B := redNeighborFinset G b (s.toFinset \ A)
  have haS : a ∉ s.toFinset := by simpa using has
  have hbS : b ∉ s.toFinset := by simpa using hbs
  have hcount : s.toFinset.card ≤ A.card + B.card + 2 := by
    exact redNeighborFinset_add_card_ge_of_no_common_deleteEdges_neighbor
      hM G s.toFinset a b haS hbS hcommon
  have hAsub : A ⊆ s.toFinset := fun _x hx ↦ (mem_filter.mp hx).1
  have hBsub : B ⊆ s.toFinset := fun _x hx ↦
    (mem_sdiff.mp (mem_filter.mp hx).1).1
  have hAclique : Gᶜ.IsClique (A : Set α) := by
    exact hclique.subset (fun _x hx ↦ hAsub hx)
  have hBclique : Gᶜ.IsClique (B : Set α) := by
    exact hclique.subset (fun _x hx ↦ hBsub hx)
  have hAB : Disjoint A B := by
    rw [Finset.disjoint_left]
    intro x hxA hxB
    exact (mem_sdiff.mp (mem_filter.mp hxB).1).2 hxA
  have hAs : ∀ x ∈ A, x ∈ s := by
    intro x hx
    simpa using hAsub hx
  have hBs : ∀ x ∈ B, x ∈ s := by
    intro x hx
    simpa using hBsub hx
  have haA : ∀ x ∈ A, Gᶜ.Adj a x := by
    intro x hx
    exact (mem_filter.mp hx).2
  have hbB : ∀ x ∈ B, Gᶜ.Adj b x := by
    intro x hx
    exact (mem_filter.mp hx).2
  have hsomeSingleton : A.card = 1 ∨ B.card = 1 := by
    by_contra hnone
    push_neg at hnone
    have hred := twoCliqueStars_no_singleton_card_le_maximal
      (G := Gᶜ) (s := s) (A := A) (B := B) (z := a) (w := b)
      hmax hnone.1 hnone.2 hAclique hBclique hAB hAs hBs
        has hbs habG.ne haA hbB
    have hcountR : (s.toFinset.card : ℝ) ≤
        ((A.card + B.card : ℕ) : ℝ) + 2 := by
      exact_mod_cast hcount
    exfalso
    apply hfail
    linarith
  rcases hsomeSingleton with hAone | hBone
  · let C := redNeighborFinset G b s.toFinset
    let D := redNeighborFinset G a (s.toFinset \ C)
    have hcount' : s.toFinset.card ≤ C.card + D.card + 2 := by
      exact redNeighborFinset_add_card_ge_of_no_common_deleteEdges_neighbor
        hM G s.toFinset b a hbS haS
          (fun x hx h ↦ hcommon x hx ⟨h.2, h.1⟩)
    have hBsubC : B ⊆ C := by
      intro x hxB
      exact mem_filter.mpr ⟨hBsub hxB, (mem_filter.mp hxB).2⟩
    have hBlarge : 4 ≤ B.card := by omega
    have hClarge : 4 ≤ C.card :=
      hBlarge.trans (card_le_card hBsubC)
    have hCsub : C ⊆ s.toFinset := fun _x hx ↦ (mem_filter.mp hx).1
    have hDsub : D ⊆ s.toFinset := fun _x hx ↦
      (mem_sdiff.mp (mem_filter.mp hx).1).1
    have hCclique : Gᶜ.IsClique (C : Set α) := by
      exact hclique.subset (fun _x hx ↦ hCsub hx)
    have hDclique : Gᶜ.IsClique (D : Set α) := by
      exact hclique.subset (fun _x hx ↦ hDsub hx)
    have hCD : Disjoint C D := by
      rw [Finset.disjoint_left]
      intro x hxC hxD
      exact (mem_sdiff.mp (mem_filter.mp hxD).1).2 hxC
    have hCs : ∀ x ∈ C, x ∈ s := by
      intro x hx
      simpa using hCsub hx
    have hDs : ∀ x ∈ D, x ∈ s := by
      intro x hx
      simpa using hDsub hx
    have hbC : ∀ x ∈ C, Gᶜ.Adj b x := by
      intro x hx
      exact (mem_filter.mp hx).2
    have haD : ∀ x ∈ D, Gᶜ.Adj a x := by
      intro x hx
      exact (mem_filter.mp hx).2
    have hDone : D.card = 1 := by
      by_contra hDone
      have hred := twoCliqueStars_no_singleton_card_le_maximal
        (G := Gᶜ) (s := s) (A := C) (B := D) (z := b) (w := a)
        hmax (by omega) hDone hCclique hDclique hCD hCs hDs
          hbs has habG.ne.symm hbC haD
      have hcountR : (s.toFinset.card : ℝ) ≤
          ((C.card + D.card : ℕ) : ℝ) + 2 := by
        exact_mod_cast hcount'
      exfalso
      apply hfail
      linarith
    have hCeq : C.card = s.toFinset.card - 3 := by
      have hlow : s.toFinset.card - 3 ≤ C.card := by omega
      have hupp : C.card ≤ s.toFinset.card - 3 := by
        by_contra hupp
        have hsideLe : s.toFinset.card - 2 ≤ C.card := by omega
        have hred := uniformCliqueStar_card_le_maximal
          (G := Gᶜ) (s := s) (A := C) (z := b)
          hmax (by omega) hCclique hCs hbs hbC
        have hsideLeR : ((s.toFinset.card - 2 : ℕ) : ℝ) ≤ C.card := by
          exact_mod_cast hsideLe
        have hcast : (((s.toFinset.card - 2 : ℕ) : ℝ)) =
            (s.toFinset.card : ℝ) - 2 := by
          rw [Nat.cast_sub (by omega)]
          norm_num
        exfalso
        apply hfail
        rw [← hcast]
        exact hsideLeR.trans hred
      omega
    refine ⟨b, a, ?_, hbs, has, habG.symm, ?_⟩
    · exact Sym2.eq_swap
    · dsimp only
      exact ⟨hCeq, hDone⟩
  · have hAlarge : 4 ≤ A.card := by omega
    have hAeq : A.card = s.toFinset.card - 3 := by
      have hlow : s.toFinset.card - 3 ≤ A.card := by omega
      have hupp : A.card ≤ s.toFinset.card - 3 := by
        by_contra hupp
        have hsideLe : s.toFinset.card - 2 ≤ A.card := by omega
        have hred := uniformCliqueStar_card_le_maximal
          (G := Gᶜ) (s := s) (A := A) (z := a)
          hmax (by omega) hAclique hAs has haA
        have hsideLeR : ((s.toFinset.card - 2 : ℕ) : ℝ) ≤ A.card := by
          exact_mod_cast hsideLe
        have hcast : (((s.toFinset.card - 2 : ℕ) : ℝ)) =
            (s.toFinset.card : ℝ) - 2 := by
          rw [Nat.cast_sub (by omega)]
          norm_num
        exfalso
        apply hfail
        rw [← hcast]
        exact hsideLeR.trans hred
      omega
    refine ⟨a, b, rfl, has, hbs, habG, ?_⟩
    dsimp only
    exact ⟨hAeq, hBone⟩

/-- Two complete fractional stars with different attachments may have
overlapping bases.  When both bases have the same size at least three, the
common internal edges still have load at most `2/(q-1) ≤ 1`, while an edge
at either attachment occurs only in its own star.  This is the certificate
used in the exceptional `m = 0` branch of Claim 4.4. -/
lemma twoOverlappingUniformCliqueStars_card_le_maximal
    {G : SimpleGraph α} {s : Set α} {A B : Finset α} {z w : α}
    {weight : Finset α → ℝ}
    (hmax : ∀ q : Finset α → ℝ,
      IsFractionalInternalCrossPacking G s q →
        fractionalSize G q ≤ fractionalSize G weight)
    {q : ℕ} (hq : 3 ≤ q) (hAcard : A.card = q) (hBcard : B.card = q)
    (hA : G.IsClique (A : Set α)) (hB : G.IsClique (B : Set α))
    (hAs : ∀ x ∈ A, x ∈ s) (hBs : ∀ x ∈ B, x ∈ s)
    (hzside : z ∉ s) (hwside : w ∉ s) (hzw : z ≠ w)
    (hzA : ∀ x ∈ A, G.Adj z x)
    (hwB : ∀ x ∈ B, G.Adj w x) :
    (2 * (q : ℝ)) ≤ 2 * fractionalSize G weight := by
  classical
  let FA := cliqueStarTriangleFamily z A
  let FB := cliqueStarTriangleFamily w B
  let F := FA ∪ FB
  let u := constantTriangleFamilyWeight F (q - 1)
  have hzA0 : z ∉ A := fun hz ↦ hzside (hAs z hz)
  have hwB0 : w ∉ B := fun hw ↦ hwside (hBs w hw)
  have hzB0 : z ∉ B := fun hz ↦ hzside (hBs z hz)
  have hwA0 : w ∉ A := fun hw ↦ hwside (hAs w hw)
  have hFAcross : FA ⊆ internalCrossTriangles G s := by
    exact cliqueStarTriangleFamily_subset_internalCrossTriangles
      hA hAs hzside hzA
  have hFBcross : FB ⊆ internalCrossTriangles G s := by
    exact cliqueStarTriangleFamily_subset_internalCrossTriangles
      hB hBs hwside hwB
  have htri : ∀ t ∈ F, G.IsNClique 3 t := by
    intro t ht
    rcases mem_union.mp ht with htA | htB
    · exact (mem_internalCrossTriangles.mp (hFAcross htA)).1
    · exact (mem_internalCrossTriangles.mp (hFBcross htB)).1
  have hload : ∀ e ∈ G.edgeFinset,
      (F.filter fun t ↦ e ∈ t.sym2).card ≤ q - 1 := by
    intro e he
    have hecard : e.toFinset.card = 2 :=
      SimpleGraph.card_toFinset_mem_edgeFinset ⟨e, he⟩
    have hfilterUnion :
        F.filter (fun t ↦ e ∈ t.sym2) =
          FA.filter (fun t ↦ e ∈ t.sym2) ∪
            FB.filter (fun t ↦ e ∈ t.sym2) := by
      ext t
      simp only [F, mem_filter, mem_union]
      tauto
    rw [hfilterUnion]
    by_cases hze : z ∈ e.toFinset
    · have hFBempty :=
        filter_cliqueStarTriangleFamily_eq_empty_of_contains_avoided
          (z := w) (x := z) (A := B) hzw hzB0 e hze
      have hFAle := card_filter_cliqueStarTriangleFamily_le
        (by omega : 2 ≤ A.card) hzA0 e hecard
      change
        (FA.filter (fun t ↦ e ∈ t.sym2) ∪
          FB.filter (fun t ↦ e ∈ t.sym2)).card ≤ q - 1
      change FB.filter (fun t ↦ e ∈ t.sym2) = ∅ at hFBempty
      rw [hFBempty, union_empty]
      simpa [hAcard] using hFAle
    · by_cases hwe : w ∈ e.toFinset
      · have hFAempty :=
          filter_cliqueStarTriangleFamily_eq_empty_of_contains_avoided
            (z := z) (x := w) (A := A) hzw.symm hwA0 e hwe
        have hFBle := card_filter_cliqueStarTriangleFamily_le
          (by omega : 2 ≤ B.card) hwB0 e hecard
        change
          (FA.filter (fun t ↦ e ∈ t.sym2) ∪
            FB.filter (fun t ↦ e ∈ t.sym2)).card ≤ q - 1
        change FA.filter (fun t ↦ e ∈ t.sym2) = ∅ at hFAempty
        rw [hFAempty, empty_union]
        simpa [hBcard] using hFBle
      · have hFAle :=
          card_filter_cliqueStarTriangleFamily_le_one_of_attachment_not_mem
            hzA0 e hecard hze
        have hFBle :=
          card_filter_cliqueStarTriangleFamily_le_one_of_attachment_not_mem
            hwB0 e hecard hwe
        calc
          (FA.filter (fun t ↦ e ∈ t.sym2) ∪
              FB.filter (fun t ↦ e ∈ t.sym2)).card ≤
              (FA.filter (fun t ↦ e ∈ t.sym2)).card +
                (FB.filter (fun t ↦ e ∈ t.sym2)).card := card_union_le _ _
          _ ≤ 1 + 1 := Nat.add_le_add hFAle hFBle
          _ ≤ q - 1 := by omega
  have huPacking : IsFractionalPacking G u := by
    exact isFractionalPacking_constantTriangleFamilyWeight (by omega) htri hload
  have huSupport : ∀ t : Finset α,
      t ∉ internalCrossTriangles G s → u t = 0 := by
    intro t ht
    simp only [u, constantTriangleFamilyWeight]
    split
    · rename_i htF
      rcases mem_union.mp htF with htA | htB
      · exact (ht (hFAcross htA)).elim
      · exact (ht (hFBcross htB)).elim
    · rfl
  have hFdis : Disjoint FA FB := by
    rw [Finset.disjoint_left]
    intro t htA htB
    obtain ⟨p, hp, htp⟩ := mem_image.mp htA
    obtain ⟨r, hr, htr⟩ := mem_image.mp htB
    have hzmem : z ∈ t := by rw [← htp]; simp
    have hzmem' : z ∈ insert w r := by simpa [htr] using hzmem
    rcases mem_insert.mp hzmem' with hzw' | hzr
    · exact hzw hzw'
    · exact hzB0 ((mem_powersetCard.mp hr).1 hzr)
  have hFcard : F.card = 2 * q.choose 2 := by
    rw [show F = FA ∪ FB by rfl, card_union_of_disjoint hFdis,
      show FA.card = A.card.choose 2 by
        exact card_cliqueStarTriangleFamily hzA0,
      show FB.card = B.card.choose 2 by
        exact card_cliqueStarTriangleFamily hwB0,
      hAcard, hBcard]
    omega
  have huSize : 2 * fractionalSize G u = 2 * (q : ℝ) := by
    rw [fractionalSize_constantTriangleFamilyWeight htri, hFcard]
    have hcast : (((q - 1 : ℕ) : ℝ)) = (q : ℝ) - 1 := by
      rw [Nat.cast_sub (by omega)]
      norm_num
    rw [Nat.cast_mul, Nat.cast_choose_two, hcast]
    have hne : (q : ℝ) - 1 ≠ 0 := by
      have hqR : (3 : ℝ) ≤ q := by exact_mod_cast hq
      linarith
    field_simp [hne]
    ring
  have huMax := hmax u ⟨huPacking, huSupport⟩
  linarith

/-- A perfect fractional clique star and one vertex-disjoint cross triangle
may be combined without losing any capacity.  The doubled weight increases
from `|A|` to `|A|+2`. -/
lemma uniformCliqueStar_add_disjoint_triangle_card_add_two_le_maximal
    {G : SimpleGraph α} {s : Set α} {A t : Finset α} {z : α}
    {weight : Finset α → ℝ}
    (hmax : ∀ q : Finset α → ℝ,
      IsFractionalInternalCrossPacking G s q →
        fractionalSize G q ≤ fractionalSize G weight)
    (hAcard : 2 ≤ A.card) (hA : G.IsClique (A : Set α))
    (hAs : ∀ x ∈ A, x ∈ s) (hzside : z ∉ s)
    (hzA : ∀ x ∈ A, G.Adj z x)
    (ht : t ∈ internalCrossTriangles G s)
    (hdis : Disjoint (insert z A) t) :
    ((A.card : ℝ) + 2) ≤ 2 * fractionalSize G weight := by
  classical
  let F := cliqueStarTriangleFamily z A
  let wF := constantTriangleFamilyWeight F (A.card - 1)
  let wT := integralPackingWeight {t}
  let u := addTriangleWeight wF wT
  have hwFdata := uniformCliqueStar_isFractionalInternalCrossPacking
    hAcard hA hAs hzside hzA
  have hwF : IsFractionalInternalCrossPacking G s wF := by
    simpa only [wF, F] using hwFdata.1
  have hsizeF : 2 * fractionalSize G wF = (A.card : ℝ) := by
    simpa only [wF, F] using hwFdata.2
  have hPt : IsInternalCrossPacking G s {t} := by
    refine ⟨?_, ?_⟩
    · intro q hq
      have hqt : q = t := by simpa using hq
      subst q
      exact ht
    · intro q hq r hr hqr
      have hqt : q = t := by simpa using hq
      have hrt : r = t := by simpa using hr
      subst q
      subst r
      exact (hqr rfl).elim
  have hwT : IsFractionalInternalCrossPacking G s wT :=
    isFractionalInternalCrossPacking_integralPackingWeight hPt
  have hsupportF : ∀ q, q ∉ F → wF q = 0 := by
    intro q hq
    simp [wF, constantTriangleFamilyWeight, hq]
  have hsupportT : ∀ q, q ∉ ({t} : Finset (Finset α)) → wT q = 0 := by
    intro q hq
    simp [wT, integralPackingWeight, hq]
  have hcross : ∀ q ∈ F, ∀ r ∈ ({t} : Finset (Finset α)),
      (q ∩ r).card ≤ 1 := by
    intro q hq r hr
    have hqsub : q ⊆ insert z A := by
      obtain ⟨p, hp, rfl⟩ := mem_image.mp hq
      intro x hx
      rcases mem_insert.mp hx with rfl | hxp
      · simp
      · exact mem_insert_of_mem ((mem_powersetCard.mp hp).1 hxp)
    have hrt : r = t := by simpa using hr
    subst r
    have hqt : Disjoint q t := by
      rw [Finset.disjoint_left]
      intro x hxq hxt
      exact Finset.disjoint_left.mp hdis (hqsub hxq) hxt
    rw [Finset.disjoint_iff_inter_eq_empty.mp hqt]
    simp
  have huPack : IsFractionalPacking G u := by
    exact isFractionalPacking_add_of_cross_inter_card_le_one
      hwF.1 hwT.1 hsupportF hsupportT hcross
  have huSupport : ∀ q : Finset α, q ∉ internalCrossTriangles G s →
      u q = 0 := by
    intro q hq
    have hF0 := hwF.2 q hq
    have hT0 := hwT.2 q hq
    change wF q + wT q = 0
    calc
      wF q + wT q = 0 + 0 := congrArg₂ (· + ·) hF0 hT0
      _ = 0 := zero_add 0
  have huMax := hmax u ⟨huPack, huSupport⟩
  have hsizeT : fractionalSize G wT = 1 := by
    rw [fractionalSize_integralPackingWeight]
    · simp
    · intro q hq
      have hqt : q = t := by simpa using hq
      subst q
      exact (mem_internalCrossTriangles.mp ht).1
  rw [fractionalSize_addTriangleWeight] at huMax
  linarith

/-- Applying the bad-structure lemma to any opposite-side blue edge when
the maximal blue cross packing is empty. -/
lemma claim44_bad_structure_of_opposite_edge_of_zero
    {G : SimpleGraph α} {s : Set α} {M : Finset (Sym2 α)}
    (hM : IsCrossMatching s M)
    {P : Finset (Finset α)}
    (hP : IsInternalCrossPacking
      (G.deleteEdges (M : Set (Sym2 α))) s P)
    (hPmax : ∀ Q : Finset (Finset α),
      IsInternalCrossPacking (G.deleteEdges (M : Set (Sym2 α))) s Q →
        Q.card ≤ P.card)
    (hm : P.card = 0)
    (hclique : Gᶜ.IsClique (s.toFinset : Set α))
    {a b : α} (he : s(a, b) ∈ sideEdgeFinset G sᶜ.toFinset)
    {weight : Finset α → ℝ}
    (hmax : ∀ q : Finset α → ℝ,
      IsFractionalInternalCrossPacking Gᶜ s q →
        fractionalSize Gᶜ q ≤ fractionalSize Gᶜ weight)
    (hseven : 7 ≤ s.toFinset.card)
    (hfail : ¬ ((s.toFinset.card : ℝ) - 2 ≤
      2 * fractionalSize Gᶜ weight)) :
    ∃ z y : α,
      s(z, y) = s(a, b) ∧ z ∉ s ∧ y ∉ s ∧ G.Adj z y ∧
      let A := redNeighborFinset G z s.toFinset
      let B := redNeighborFinset G y (s.toFinset \ A)
      A.card = s.toFinset.card - 3 ∧ B.card = 1 := by
  classical
  have hPempty : P = ∅ := card_eq_zero.mp hm
  have heUncovered : s(a, b) ∉ coveredInternalEdges
      (G.deleteEdges (M : Set (Sym2 α))) s P := by
    intro heCov
    rcases (mem_filter.mp heCov).2 with ⟨t, htP, _het⟩
    rw [hPempty] at htP
    simp at htP
  rcases proposition42_claim44_edgeFacts hM hP he heUncovered with
    ⟨habG, has, hbs, heInternal, _hPG, _heUncoveredG⟩
  have heP : ∀ t ∈ P, s(a, b) ∉ t.sym2 := by
    intro t htP
    rw [hPempty] at htP
    simp at htP
  have hcommon : ∀ x ∈ s.toFinset,
      ¬ ((G.deleteEdges (M : Set (Sym2 α))).Adj a x ∧
        (G.deleteEdges (M : Set (Sym2 α))).Adj b x) := by
    intro x hxs
    have hxunused : x ∉ packingVertices P := by
      rw [hPempty]
      simp [packingVertices]
    have hxs' : x ∈ s := by
      simpa only [Set.mem_toFinset] using hxs
    exact maximum_internalCrossPacking_no_common_unused_opposite_neighbor
      hP hPmax heInternal heP (by simp [hxs', has]) hxunused
  exact claim44_bad_structure_of_lower_bound_failure hM habG has hbs
    hclique hcommon hmax hseven hfail

/-- The large red-neighbour endpoint appearing in the exceptional branch. -/
def Claim44HighVertex (G : SimpleGraph α) (s : Set α) (z : α) : Prop :=
  z ∉ s ∧
    (redNeighborFinset G z s.toFinset).card = s.toFinset.card - 3

/-- Under failure of the desired lower bound there cannot be two distinct
large-neighbour endpoints: the overlapping-star certificate would already
be too large. -/
lemma claim44_highVertex_unique_of_lower_bound_failure
    {G : SimpleGraph α} {s : Set α} {weight : Finset α → ℝ}
    (hclique : Gᶜ.IsClique (s.toFinset : Set α))
    (hmax : ∀ q : Finset α → ℝ,
      IsFractionalInternalCrossPacking Gᶜ s q →
        fractionalSize Gᶜ q ≤ fractionalSize Gᶜ weight)
    (hseven : 7 ≤ s.toFinset.card)
    (hfail : ¬ ((s.toFinset.card : ℝ) - 2 ≤
      2 * fractionalSize Gᶜ weight))
    {z w : α} (hz : Claim44HighVertex G s z)
    (hw : Claim44HighVertex G s w) : z = w := by
  classical
  by_contra hzw
  let A := redNeighborFinset G z s.toFinset
  let B := redNeighborFinset G w s.toFinset
  have hAsub : A ⊆ s.toFinset := fun _x hx ↦ (mem_filter.mp hx).1
  have hBsub : B ⊆ s.toFinset := fun _x hx ↦ (mem_filter.mp hx).1
  have hAclique : Gᶜ.IsClique (A : Set α) := by
    exact hclique.subset (fun _x hx ↦ hAsub hx)
  have hBclique : Gᶜ.IsClique (B : Set α) := by
    exact hclique.subset (fun _x hx ↦ hBsub hx)
  have hAs : ∀ x ∈ A, x ∈ s := by
    intro x hx
    simpa using hAsub hx
  have hBs : ∀ x ∈ B, x ∈ s := by
    intro x hx
    simpa using hBsub hx
  have hzA : ∀ x ∈ A, Gᶜ.Adj z x := by
    intro x hx
    exact (mem_filter.mp hx).2
  have hwB : ∀ x ∈ B, Gᶜ.Adj w x := by
    intro x hx
    exact (mem_filter.mp hx).2
  have hq : 3 ≤ s.toFinset.card - 3 := by omega
  have hred := twoOverlappingUniformCliqueStars_card_le_maximal
    (G := Gᶜ) (s := s) (A := A) (B := B) (z := z) (w := w)
    hmax hq hz.2 hw.2 hAclique hBclique hAs hBs hz.1 hw.1 hzw hzA hwB
  apply hfail
  have hside : ((s.toFinset.card - 2 : ℕ) : ℝ) ≤
      2 * ((s.toFinset.card - 3 : ℕ) : ℝ) := by
    exact_mod_cast (by omega : s.toFinset.card - 2 ≤
      2 * (s.toFinset.card - 3))
  have hcast2 : (((s.toFinset.card - 2 : ℕ) : ℝ)) =
      (s.toFinset.card : ℝ) - 2 := by
    rw [Nat.cast_sub (by omega)]
    norm_num
  rw [← hcast2]
  exact hside.trans hred

/-- The complete exceptional `m = 0`, `k ≥ 3` branch of Claim 4.4.  Three
blue edges on the uncovered side force a unique common high-neighbour
endpoint.  The third leaf then avoids the one forbidden partner and yields
either an extra red triangle or a blue cross triangle, the latter
contradicting maximality of the empty blue packing. -/
lemma proposition42_claim44_eq_zero_ge_three
    {G : SimpleGraph α} {s : Set α} {M : Finset (Sym2 α)}
    (hM : IsCrossMatching s M)
    {P : Finset (Finset α)}
    (hP : IsInternalCrossPacking
      (G.deleteEdges (M : Set (Sym2 α))) s P)
    (hPmax : ∀ Q : Finset (Finset α),
      IsInternalCrossPacking (G.deleteEdges (M : Set (Sym2 α))) s Q →
        Q.card ≤ P.card)
    (hcover : ∀ e ∈ sideEdgeFinset G s.toFinset,
      e ∈ coveredInternalEdges G s P)
    {weight : Finset α → ℝ}
    (hmax : ∀ q : Finset α → ℝ,
      IsFractionalInternalCrossPacking Gᶜ s q →
        fractionalSize Gᶜ q ≤ fractionalSize Gᶜ weight)
    (hm : P.card = 0)
    (hk3 : 3 ≤ (internalEdgeFinset G s).card)
    (hseven : 7 ≤ s.toFinset.card) :
    (s.toFinset.card : ℝ) - 2 ≤
      2 * fractionalSize Gᶜ weight := by
  classical
  by_contra hfail
  have hPempty : P = ∅ := card_eq_zero.mp hm
  have hclique : Gᶜ.IsClique (s.toFinset : Set α) := by
    have h := claim44_unusedSide_isClique hcover
    have hUnused : claim44UnusedSide s P = s.toFinset := by
      simp [claim44UnusedSide, hPempty, packingVertices]
    simpa only [hUnused] using h
  let E := sideEdgeFinset G sᶜ.toFinset
  have hsideEmpty : sideEdgeFinset G s.toFinset = ∅ := by
    apply eq_empty_iff_forall_notMem.mpr
    intro e he
    have heCov := hcover e he
    rcases (mem_filter.mp heCov).2 with ⟨t, htP, _het⟩
    rw [hPempty] at htP
    simp at htP
  have hEcard : 3 ≤ E.card := by
    have hunion := internalEdgeFinset_eq_union_sides G s
    have hcard : (internalEdgeFinset G s).card = E.card := by
      rw [hunion, hsideEmpty, empty_union]
    omega
  have hbad : ∀ e ∈ E, ∃ z y : α,
      e = s(z, y) ∧ Claim44HighVertex G s z ∧ y ∉ s ∧ G.Adj z y ∧
        (redNeighborFinset G y
          (s.toFinset \ redNeighborFinset G z s.toFinset)).card = 1 := by
    intro e heE
    induction e using Sym2.inductionOn with
    | hf a b =>
      obtain ⟨z, y, hzy, hzs, hys, hGzy, hA, hB⟩ :=
        claim44_bad_structure_of_opposite_edge_of_zero
          hM hP hPmax hm hclique heE hmax hseven hfail
      exact ⟨z, y, hzy.symm, ⟨hzs, hA⟩, hys, hGzy, hB⟩
  have hhighUnique : ∀ {z w : α}, Claim44HighVertex G s z →
      Claim44HighVertex G s w → z = w := by
    intro z w hz hw
    exact claim44_highVertex_unique_of_lower_bound_failure
      hclique hmax hseven hfail hz hw
  have hNoBlueCross : ∀ t ∈ internalCrossTriangles
      (G.deleteEdges (M : Set (Sym2 α))) s, False := by
    intro t ht
    have hsingle : IsInternalCrossPacking
        (G.deleteEdges (M : Set (Sym2 α))) s {t} := by
      refine ⟨?_, ?_⟩
      · intro q hq
        have hqt : q = t := by simpa using hq
        subst q
        exact ht
      · intro q hq r hr hqr
        have hqt : q = t := by simpa using hq
        have hrt : r = t := by simpa using hr
        subst q
        subst r
        exact (hqr rfl).elim
    have := hPmax {t} hsingle
    simp [hm] at this
  obtain ⟨e₀, he₀⟩ := card_pos.mp (lt_of_lt_of_le (by omega : 0 < 3) hEcard)
  obtain ⟨a, b₀, he₀eq, haHigh, hb₀s, hab₀, hB₀card⟩ := hbad e₀ he₀
  have hErase : 1 < (E.erase e₀).card := by
    rw [card_erase_of_mem he₀]
    omega
  obtain ⟨e₁, he₁, e₂, he₂, he₁₂⟩ := one_lt_card.mp hErase
  have he₁E : e₁ ∈ E := (mem_erase.mp he₁).2
  have he₂E : e₂ ∈ E := (mem_erase.mp he₂).2
  have he₁₀ : e₁ ≠ e₀ := (mem_erase.mp he₁).1
  have he₂₀ : e₂ ≠ e₀ := (mem_erase.mp he₂).1
  obtain ⟨z₁, b₁, he₁eq, hz₁High, hb₁s, hz₁b₁, hB₁card⟩ := hbad e₁ he₁E
  obtain ⟨z₂, b₂, he₂eq, hz₂High, hb₂s, hz₂b₂, _hB₂card⟩ := hbad e₂ he₂E
  have hz₁a : z₁ = a := hhighUnique hz₁High haHigh
  have hz₂a : z₂ = a := hhighUnique hz₂High haHigh
  subst z₁
  subst z₂
  have hab₁ : G.Adj a b₁ := hz₁b₁
  have hab₂ : G.Adj a b₂ := hz₂b₂
  have hab₀ne : a ≠ b₀ := hab₀.ne
  have hab₁ne : a ≠ b₁ := hab₁.ne
  have hab₂ne : a ≠ b₂ := hab₂.ne
  have hb₀b₁ : b₀ ≠ b₁ := by
    intro h
    subst b₁
    exact he₁₀ (he₁eq.trans he₀eq.symm)
  have hb₀b₂ : b₀ ≠ b₂ := by
    intro h
    subst b₂
    exact he₂₀ (he₂eq.trans he₀eq.symm)
  have hb₁b₂ : b₁ ≠ b₂ := by
    intro h
    subst b₂
    exact he₁₂ (he₁eq.trans he₂eq.symm)
  have hLeavesRed : ∀ {u v : α}, u ∉ s → v ∉ s →
      u ≠ a → v ≠ a → u ≠ v → Gᶜ.Adj u v := by
    intro u v hus hvs hua hva huv
    rw [SimpleGraph.compl_adj]
    refine ⟨huv, ?_⟩
    intro huvG
    have huvE : s(u, v) ∈ E := by
      apply mem_filter.mpr
      refine ⟨SimpleGraph.mem_edgeFinset.mpr huvG, ?_⟩
      intro x hx
      have hxuv : x = u ∨ x = v := by
        simpa [Sym2.toFinset_mk_eq] using hx
      rcases hxuv with rfl | rfl <;> simpa using ‹_ ∉ s›
    obtain ⟨z, y, hzy, hzHigh, _hys, _hzyG, _hB⟩ := hbad s(u, v) huvE
    have hza : z = a := hhighUnique hzHigh haHigh
    subst z
    rcases Sym2.eq_iff.mp hzy with ⟨hau, _⟩ | ⟨_, hav⟩
    · exact hua hau
    · exact hva hav
  have hb₀b₁R : Gᶜ.Adj b₀ b₁ :=
    hLeavesRed hb₀s hb₁s (Ne.symm hab₀ne) (Ne.symm hab₁ne) hb₀b₁
  have hb₀b₂R : Gᶜ.Adj b₀ b₂ :=
    hLeavesRed hb₀s hb₂s (Ne.symm hab₀ne) (Ne.symm hab₂ne) hb₀b₂
  have hb₁b₂R : Gᶜ.Adj b₁ b₂ :=
    hLeavesRed hb₁s hb₂s (Ne.symm hab₁ne) (Ne.symm hab₂ne) hb₁b₂
  let A := redNeighborFinset G a s.toFinset
  have hAsub : A ⊆ s.toFinset := fun _x hx ↦ (mem_filter.mp hx).1
  have hAclique : Gᶜ.IsClique (A : Set α) := by
    exact hclique.subset (fun _x hx ↦ hAsub hx)
  have hAs : ∀ x ∈ A, x ∈ s := by
    intro x hx
    simpa using hAsub hx
  have haA : ∀ x ∈ A, Gᶜ.Adj a x := by
    intro x hx
    exact (mem_filter.mp hx).2
  have hAcard : A.card = s.toFinset.card - 3 := haHigh.2
  have hredExtra : ∀ {p d c : α},
      p ∉ s → d ∉ s → c ∈ s → c ∉ A →
      a ≠ p → a ≠ d → p ≠ d →
      Gᶜ.Adj p d → Gᶜ.Adj p c → Gᶜ.Adj d c → False := by
    intro p d c hps hds hcs hcA hap had hpd hpdR hpcR hdcR
    let t := insert c ({p, d} : Finset α)
    have htRed : t ∈ internalCrossTriangles Gᶜ s :=
      insert_mem_internalCrossTriangles_of_opposite hpdR
        (by simp [hps, hds]) (by simp [hcs, hps]) hpcR.symm hdcR.symm
    have hdis : Disjoint (insert a A) t := by
      rw [Finset.disjoint_left]
      intro x hxStar hxt
      rcases mem_insert.mp hxStar with rfl | hxA
      · simp only [t, mem_insert, mem_singleton] at hxt
        rcases hxt with h | h | h
        · exact haHigh.1 (h ▸ hcs)
        · exact hap h
        · exact had h
      · have hxs : x ∈ s := by simpa using hAsub hxA
        simp only [t, mem_insert, mem_singleton] at hxt
        rcases hxt with h | h | h
        · exact hcA (h ▸ hxA)
        · exact hps (h ▸ hxs)
        · exact hds (h ▸ hxs)
    have hred := uniformCliqueStar_add_disjoint_triangle_card_add_two_le_maximal
      (G := Gᶜ) (s := s) (A := A) (t := t) (z := a)
      hmax (by omega) hAclique hAs haHigh.1 haA htRed hdis
    have hcast : (((s.toFinset.card - 2 : ℕ) : ℝ)) =
        (s.toFinset.card : ℝ) - 2 := by
      rw [Nat.cast_sub (by omega)]
      norm_num
    apply hfail
    rw [← hcast]
    have hnat : s.toFinset.card - 2 ≤ A.card + 2 := by omega
    have hnatR : (((s.toFinset.card - 2 : ℕ) : ℝ)) ≤
        ((A.card + 2 : ℕ) : ℝ) := by
      exact_mod_cast hnat
    push_cast at hnatR
    exact hnatR.trans hred
  have hfinish : ∀ {p d c : α},
      p ∉ s → d ∉ s → c ∈ s → c ∉ A →
      a ≠ p → a ≠ d → p ≠ d →
      G.Adj a p → G.Adj a d → G.Adj a c →
      Gᶜ.Adj p d → Gᶜ.Adj p c →
      s(a, c) ∉ M → s(d, c) ∉ M → False := by
    intro p d c hps hds hcs hcA hap had hpd hapG hadG hacG hpdR hpcR hacM hdcM
    by_cases hdcG : G.Adj d c
    · have hadM : s(a, d) ∉ M := by
        intro hadM
        exact hM.1 s(a, d) hadM (by simp [haHigh.1, hds])
      have hadDel : (G.deleteEdges (M : Set (Sym2 α))).Adj a d := by
        simpa [SimpleGraph.deleteEdges_adj, hadM] using hadG
      have hacDel : (G.deleteEdges (M : Set (Sym2 α))).Adj a c := by
        simpa [SimpleGraph.deleteEdges_adj, hacM] using hacG
      have hdcDel : (G.deleteEdges (M : Set (Sym2 α))).Adj d c := by
        simpa [SimpleGraph.deleteEdges_adj, hdcM] using hdcG
      have htBlue : insert c ({a, d} : Finset α) ∈
          internalCrossTriangles (G.deleteEdges (M : Set (Sym2 α))) s :=
        insert_mem_internalCrossTriangles_of_opposite hadDel
          (by simp [haHigh.1, hds]) (by simp [hcs, haHigh.1]) hacDel.symm hdcDel.symm
      exact hNoBlueCross _ htBlue
    · have hdcR : Gᶜ.Adj d c := by
        have hdcne : d ≠ c := by
          intro h
          subst c
          exact hds hcs
        simpa [SimpleGraph.compl_adj, hdcne] using hdcG
      exact hredExtra hps hds hcs hcA hap had hpd hpdR hpcR hdcR
  let B₀ := redNeighborFinset G b₀ (s.toFinset \ A)
  have hB₀card' : B₀.card = 1 := by simpa [A, B₀] using hB₀card
  obtain ⟨c₀, hc₀B⟩ := card_pos.mp (by omega : 0 < B₀.card)
  have hc₀diff := (mem_filter.mp hc₀B).1
  have hc₀s : c₀ ∈ s := by
    simpa using (mem_sdiff.mp hc₀diff).1
  have hc₀A : c₀ ∉ A := (mem_sdiff.mp hc₀diff).2
  have hb₀c₀R : Gᶜ.Adj b₀ c₀ := (mem_filter.mp hc₀B).2
  have hac₀ne : a ≠ c₀ := by
    intro h
    subst c₀
    exact haHigh.1 hc₀s
  have hac₀G : G.Adj a c₀ := by
    by_contra h
    have hred : Gᶜ.Adj a c₀ := by
      simpa [SimpleGraph.compl_adj, hac₀ne] using h
    exact hc₀A (mem_filter.mpr ⟨by simpa using hc₀s, hred⟩)
  have exists_leaf_avoiding : ∀ {x y c : α}, x ≠ y →
      ∃ d, (d = x ∨ d = y) ∧ s(d, c) ∉ M := by
    intro x y c hxy
    by_cases hx : s(x, c) ∈ M
    · by_cases hy : s(y, c) ∈ M
      · have hxc : s(c, x) ∈ M := by simpa [Sym2.eq_swap] using hx
        have hyc : s(c, y) ∈ M := by simpa [Sym2.eq_swap] using hy
        exact (hxy (hM.unique_other_endpoint hxc hyc)).elim
      · exact ⟨y, Or.inr rfl, hy⟩
    · exact ⟨x, Or.inl rfl, hx⟩
  by_cases hac₀M : s(a, c₀) ∈ M
  · let B₁ := redNeighborFinset G b₁ (s.toFinset \ A)
    have hB₁card' : B₁.card = 1 := by simpa [A, B₁] using hB₁card
    obtain ⟨c₁, hc₁B⟩ := card_pos.mp (by omega : 0 < B₁.card)
    have hc₁diff := (mem_filter.mp hc₁B).1
    have hc₁s : c₁ ∈ s := by
      simpa using (mem_sdiff.mp hc₁diff).1
    have hc₁A : c₁ ∉ A := (mem_sdiff.mp hc₁diff).2
    have hb₁c₁R : Gᶜ.Adj b₁ c₁ := (mem_filter.mp hc₁B).2
    by_cases hc : c₁ = c₀
    · subst c₁
      exact hredExtra hb₀s hb₁s hc₀s hc₀A
        hab₀ne hab₁ne hb₀b₁ hb₀b₁R hb₀c₀R hb₁c₁R
    · have hac₁M : s(a, c₁) ∉ M := by
        intro h
        have heq : c₀ = c₁ :=
          hM.unique_other_endpoint (a := a) (b := c₀) (c := c₁) hac₀M h
        exact hc heq.symm
      have hac₁ne : a ≠ c₁ := by
        intro h
        subst c₁
        exact haHigh.1 hc₁s
      have hac₁G : G.Adj a c₁ := by
        by_contra h
        have hred : Gᶜ.Adj a c₁ := by
          simpa [SimpleGraph.compl_adj, hac₁ne] using h
        exact hc₁A (mem_filter.mpr ⟨by simpa using hc₁s, hred⟩)
      obtain ⟨d, hd, hdcM⟩ := exists_leaf_avoiding hb₀b₂ (c := c₁)
      rcases hd with rfl | rfl
      · exact hfinish hb₁s hb₀s hc₁s hc₁A hab₁ne hab₀ne hb₀b₁.symm
          hab₁ hab₀ hac₁G hb₀b₁R.symm hb₁c₁R hac₁M hdcM
      · exact hfinish hb₁s hb₂s hc₁s hc₁A hab₁ne hab₂ne hb₁b₂
          hab₁ hab₂ hac₁G hb₁b₂R hb₁c₁R hac₁M hdcM
  · obtain ⟨d, hd, hdcM⟩ := exists_leaf_avoiding hb₁b₂ (c := c₀)
    rcases hd with rfl | rfl
    · exact hfinish hb₀s hb₁s hc₀s hc₀A hab₀ne hab₁ne hb₀b₁
        hab₀ hab₁ hac₀G hb₀b₁R hb₀c₀R hac₀M hdcM
    · exact hfinish hb₀s hb₂s hc₀s hc₀A hab₀ne hab₂ne hb₀b₂
        hab₀ hab₂ hac₀G hb₀b₂R hb₀c₀R hac₀M hdcM

/-- The `m = 0` estimate with the one-vertex singleton loss retained.  This
is the form needed when `k ≤ 2`; in fact the argument only uses that the
saturated side has at least seven vertices. -/
lemma proposition42_claim44_eq_zero
    {G : SimpleGraph α} {s : Set α} {M : Finset (Sym2 α)}
    (hM : IsCrossMatching s M)
    {P : Finset (Finset α)}
    (hP : IsInternalCrossPacking
      (G.deleteEdges (M : Set (Sym2 α))) s P)
    (hPmax : ∀ Q : Finset (Finset α),
      IsInternalCrossPacking (G.deleteEdges (M : Set (Sym2 α))) s Q →
        Q.card ≤ P.card)
    (hcover : ∀ e ∈ sideEdgeFinset G s.toFinset,
      e ∈ coveredInternalEdges G s P)
    {a b : α}
    (he : s(a, b) ∈ sideEdgeFinset G sᶜ.toFinset)
    (heUncovered : s(a, b) ∉ coveredInternalEdges
      (G.deleteEdges (M : Set (Sym2 α))) s P)
    {weight : Finset α → ℝ}
    (hmax : ∀ q : Finset α → ℝ,
      IsFractionalInternalCrossPacking Gᶜ s q →
        fractionalSize Gᶜ q ≤ fractionalSize Gᶜ weight)
    (hm : P.card = 0) (hseven : 7 ≤ s.toFinset.card) :
    (s.toFinset.card : ℝ) - 3 ≤
      2 * fractionalSize Gᶜ weight := by
  classical
  rcases proposition42_claim44_edgeFacts hM hP he heUncovered with
    ⟨habG, has, hbs, _heInternal, _hP_G, _heUncoveredG⟩
  obtain ⟨A, B, hA, hB, hAB, hAs, hBs, haA, hbB, hcount⟩ :=
    proposition42_claim44_sideCliques hM hP hPmax hcover he heUncovered
  have hABcard : 3 ≤ A.card + B.card := by omega
  have hred := twoCliqueStars_card_sub_one_le_maximal
    (G := Gᶜ) (s := s) (A := A) (B := B) (z := a) (w := b)
      hmax hABcard hA hB hAB hAs hBs has hbs habG.ne haA hbB
  have hcountR : (s.toFinset.card : ℝ) ≤
      ((A.card + B.card : ℕ) : ℝ) + 2 * (P.card : ℝ) + 2 := by
    exact_mod_cast hcount
  have hmR : (P.card : ℝ) = 0 := by exact_mod_cast hm
  linarith

/-- Claim 4.4 in the `k ≥ 3` branch, with all three possible values/ranges
of the maximum blue packing size assembled. -/
lemma proposition42_claim44_ge_three
    {G : SimpleGraph α} {s : Set α} {M : Finset (Sym2 α)}
    (hM : IsCrossMatching s M)
    {P : Finset (Finset α)}
    (hP : IsInternalCrossPacking
      (G.deleteEdges (M : Set (Sym2 α))) s P)
    (hPmax : ∀ Q : Finset (Finset α),
      IsInternalCrossPacking (G.deleteEdges (M : Set (Sym2 α))) s Q →
        Q.card ≤ P.card)
    (hcover : ∀ e ∈ sideEdgeFinset G s.toFinset,
      e ∈ coveredInternalEdges G s P)
    {a b : α}
    (he : s(a, b) ∈ sideEdgeFinset G sᶜ.toFinset)
    (heUncovered : s(a, b) ∉ coveredInternalEdges
      (G.deleteEdges (M : Set (Sym2 α))) s P)
    {weight : Finset α → ℝ}
    (hmax : ∀ q : Finset α → ℝ,
      IsFractionalInternalCrossPacking Gᶜ s q →
        fractionalSize Gᶜ q ≤ fractionalSize Gᶜ weight)
    {n : ℕ} {x : ℝ}
    (hside : (n : ℝ) / 2 - x ≤ (s.toFinset.card : ℝ))
    (hk3 : 3 ≤ (internalEdgeFinset G s).card)
    (hseven : 7 ≤ s.toFinset.card) :
    (n : ℝ) / 2 - x - 3 * (P.card : ℝ) - 2 ≤
      2 * fractionalSize Gᶜ weight := by
  by_cases hm0 : P.card = 0
  · have hzero := proposition42_claim44_eq_zero_ge_three
      hM hP hPmax hcover hmax hm0 hk3 hseven
    have hm0R : (P.card : ℝ) = 0 := by exact_mod_cast hm0
    linarith
  · by_cases hm1 : P.card = 1
    · have hone := proposition42_claim44_eq_one hM hP hPmax hcover
        he heUncovered hmax hm1 hseven
      linarith
    · have hm2 : 2 ≤ P.card := by omega
      exact proposition42_claim44_ge_two hM hP hPmax hcover
        he heUncovered hmax hside hm2

/-- Claim 4.4 in the `k ≤ 2` branch.  The weaker constant three absorbs
the singleton loss when the maximum blue packing is empty. -/
lemma proposition42_claim44_le_two
    {G : SimpleGraph α} {s : Set α} {M : Finset (Sym2 α)}
    (hM : IsCrossMatching s M)
    {P : Finset (Finset α)}
    (hP : IsInternalCrossPacking
      (G.deleteEdges (M : Set (Sym2 α))) s P)
    (hPmax : ∀ Q : Finset (Finset α),
      IsInternalCrossPacking (G.deleteEdges (M : Set (Sym2 α))) s Q →
        Q.card ≤ P.card)
    (hcover : ∀ e ∈ sideEdgeFinset G s.toFinset,
      e ∈ coveredInternalEdges G s P)
    {a b : α}
    (he : s(a, b) ∈ sideEdgeFinset G sᶜ.toFinset)
    (heUncovered : s(a, b) ∉ coveredInternalEdges
      (G.deleteEdges (M : Set (Sym2 α))) s P)
    {weight : Finset α → ℝ}
    (hmax : ∀ q : Finset α → ℝ,
      IsFractionalInternalCrossPacking Gᶜ s q →
        fractionalSize Gᶜ q ≤ fractionalSize Gᶜ weight)
    {n : ℕ} {x : ℝ}
    (hside : (n : ℝ) / 2 - x ≤ (s.toFinset.card : ℝ))
    (hseven : 7 ≤ s.toFinset.card) :
    (n : ℝ) / 2 - x - 3 * (P.card : ℝ) - 3 ≤
      2 * fractionalSize Gᶜ weight := by
  by_cases hm0 : P.card = 0
  · have hzero := proposition42_claim44_eq_zero
      hM hP hPmax hcover he heUncovered hmax hm0 hseven
    have hm0R : (P.card : ℝ) = 0 := by exact_mod_cast hm0
    linarith
  · by_cases hm1 : P.card = 1
    · have hone := proposition42_claim44_eq_one hM hP hPmax hcover
        he heUncovered hmax hm1 hseven
      linarith
    · have hm2 : 2 ≤ P.card := by omega
      have htwo := proposition42_claim44_ge_two hM hP hPmax hcover
        he heUncovered hmax hside hm2
      linarith

/-- Exact alternative furnished by Claim 4.4 for the final master
inequality: the constant is two for `k ≥ 3` and three for `k ≤ 2`. -/
lemma proposition42_claim44
    {G : SimpleGraph α} {s : Set α} {M : Finset (Sym2 α)}
    (hM : IsCrossMatching s M)
    {P : Finset (Finset α)}
    (hP : IsInternalCrossPacking
      (G.deleteEdges (M : Set (Sym2 α))) s P)
    (hPmax : ∀ Q : Finset (Finset α),
      IsInternalCrossPacking (G.deleteEdges (M : Set (Sym2 α))) s Q →
        Q.card ≤ P.card)
    (hcover : ∀ e ∈ sideEdgeFinset G s.toFinset,
      e ∈ coveredInternalEdges G s P)
    {a b : α}
    (he : s(a, b) ∈ sideEdgeFinset G sᶜ.toFinset)
    (heUncovered : s(a, b) ∉ coveredInternalEdges
      (G.deleteEdges (M : Set (Sym2 α))) s P)
    {weight : Finset α → ℝ}
    (hmax : ∀ q : Finset α → ℝ,
      IsFractionalInternalCrossPacking Gᶜ s q →
        fractionalSize Gᶜ q ≤ fractionalSize Gᶜ weight)
    {n : ℕ} {x : ℝ}
    (hside : (n : ℝ) / 2 - x ≤ (s.toFinset.card : ℝ))
    (hseven : 7 ≤ s.toFinset.card) :
    (3 ≤ (internalEdgeFinset G s).card ∧
      (n : ℝ) / 2 - x - 3 * (P.card : ℝ) - 2 ≤
        2 * fractionalSize Gᶜ weight) ∨
    ((internalEdgeFinset G s).card ≤ 2 ∧
      (n : ℝ) / 2 - x - 3 * (P.card : ℝ) - 3 ≤
        2 * fractionalSize Gᶜ weight) := by
  by_cases hk3 : 3 ≤ (internalEdgeFinset G s).card
  · exact Or.inl ⟨hk3, proposition42_claim44_ge_three
      hM hP hPmax hcover he heUncovered hmax hside hk3 hseven⟩
  · have hk2 : (internalEdgeFinset G s).card ≤ 2 := by omega
    exact Or.inr ⟨hk2, proposition42_claim44_le_two
      hM hP hPmax hcover he heUncovered hmax hside hseven⟩

/-- Symmetric-pair wrapper for Claim 4.4, avoiding an arbitrary choice of
an ordering of the uncovered edge. -/
lemma proposition42_claim44_pair
    {G : SimpleGraph α} {s : Set α} {M : Finset (Sym2 α)}
    (hM : IsCrossMatching s M) {P : Finset (Finset α)}
    (hP : IsInternalCrossPacking
      (G.deleteEdges (M : Set (Sym2 α))) s P)
    (hPmax : ∀ Q : Finset (Finset α),
      IsInternalCrossPacking (G.deleteEdges (M : Set (Sym2 α))) s Q →
        Q.card ≤ P.card)
    (hcover : ∀ e ∈ sideEdgeFinset G s.toFinset,
      e ∈ coveredInternalEdges G s P)
    {e : Sym2 α} (he : e ∈ sideEdgeFinset G sᶜ.toFinset)
    (heUncovered : e ∉ coveredInternalEdges
      (G.deleteEdges (M : Set (Sym2 α))) s P)
    {weight : Finset α → ℝ}
    (hmax : ∀ q : Finset α → ℝ,
      IsFractionalInternalCrossPacking Gᶜ s q →
        fractionalSize Gᶜ q ≤ fractionalSize Gᶜ weight)
    {n : ℕ} {x : ℝ}
    (hside : (n : ℝ) / 2 - x ≤ (s.toFinset.card : ℝ))
    (hseven : 7 ≤ s.toFinset.card) :
    (3 ≤ (internalEdgeFinset G s).card ∧
      (n : ℝ) / 2 - x - 3 * (P.card : ℝ) - 2 ≤
        2 * fractionalSize Gᶜ weight) ∨
    ((internalEdgeFinset G s).card ≤ 2 ∧
      (n : ℝ) / 2 - x - 3 * (P.card : ℝ) - 3 ≤
        2 * fractionalSize Gᶜ weight) := by
  induction e using Sym2.inductionOn with
  | hf a b =>
      exact proposition42_claim44 hM hP hPmax hcover he heUncovered
        hmax hside hseven

/-- Symmetric-pair wrapper for Claim 4.3. -/
lemma proposition42_claim43_pairs
    {G : SimpleGraph α} {s : Set α} {M : Finset (Sym2 α)}
    (hM : IsCrossMatching s M) {P : Finset (Finset α)}
    (hP : IsInternalCrossPacking
      (G.deleteEdges (M : Set (Sym2 α))) s P)
    (hPmax : ∀ Q : Finset (Finset α),
      IsInternalCrossPacking (G.deleteEdges (M : Set (Sym2 α))) s Q →
        Q.card ≤ P.card)
    {e₁ e₂ : Sym2 α}
    (he₁ : e₁ ∈ sideEdgeFinset G s.toFinset)
    (he₂ : e₂ ∈ sideEdgeFinset G sᶜ.toFinset)
    (he₁Uncovered : e₁ ∉ coveredInternalEdges
      (G.deleteEdges (M : Set (Sym2 α))) s P)
    (he₂Uncovered : e₂ ∉ coveredInternalEdges
      (G.deleteEdges (M : Set (Sym2 α))) s P)
    {w : Finset α → ℝ}
    (hwmax : ∀ q : Finset α → ℝ,
      IsFractionalInternalCrossPacking Gᶜ s q →
        fractionalSize Gᶜ q ≤ fractionalSize Gᶜ w) :
    (Fintype.card α : ℝ) - 2 * (P.card : ℝ) -
        ((internalEdgeFinset G s).card : ℝ) - 10 ≤
      2 * fractionalSize Gᶜ w := by
  induction e₁ using Sym2.inductionOn with
  | hf a₁ b₁ =>
      induction e₂ using Sym2.inductionOn with
      | hf a₂ b₂ =>
          exact proposition42_claim43_both_sides_uncovered hM hP hPmax
            he₁ he₂ he₁Uncovered he₂Uncovered hwmax

/-- The maximum-packing contradiction at the end of Proposition 4.2.  The
capacity-decomposition construction is isolated in `hcovered`; all remaining
work here is the exact Claims 4.3/4.4 case split and the published master
inequality. -/
lemma isInternalEdgeCoveringCrossPacking_of_proposition42_data
    {n : ℕ} (hn : 22 ≤ n) {G : SimpleGraph (Fin n)} {s : Set (Fin n)}
    {M : Finset (Sym2 (Fin n))} (hM : IsCrossMatching s M)
    (hk : (internalEdgeFinset G s).card ≤ n / 8)
    (hupper : FractionalCoveredSizeAtMost G
      ((n : ℝ) * ((n : ℝ) - 1) / 4))
    {P : Finset (Finset (Fin n))}
    (hP : IsInternalCrossPacking
      (G.deleteEdges (M : Set (Sym2 (Fin n)))) s P)
    (hPmax : ∀ Q : Finset (Finset (Fin n)),
      IsInternalCrossPacking
          (G.deleteEdges (M : Set (Sym2 (Fin n)))) s Q →
        Q.card ≤ P.card)
    {w : Finset (Fin n) → ℝ}
    (hwmax : ∀ q : Finset (Fin n) → ℝ,
      IsFractionalInternalCrossPacking Gᶜ s q →
        fractionalSize Gᶜ q ≤ fractionalSize Gᶜ w)
    {x : ℝ}
    (hsideS : (n : ℝ) / 2 - x ≤ (s.toFinset.card : ℝ))
    (hsideT : (n : ℝ) / 2 - x ≤ (sᶜ.toFinset.card : ℝ))
    (hsevenS : 7 ≤ s.toFinset.card) (hsevenT : 7 ≤ sᶜ.toFinset.card)
    (hcovered : HasFractionalCoveredSizeAtLeast G
      ((n : ℝ) ^ 2 / 4 - (n : ℝ) / 2 + x ^ 2 -
        ((internalEdgeFinset G s).card : ℝ) + 3 * (P.card : ℝ) +
          2 * fractionalSize Gᶜ w)) :
    IsInternalEdgeCoveringCrossPacking
      (G.deleteEdges (M : Set (Sym2 (Fin n)))) s P := by
  classical
  let H := G.deleteEdges (M : Set (Sym2 (Fin n)))
  have hcoveredEq : coveredInternalEdges H s P =
      coveredInternalEdges G s P := by
    exact coveredInternalEdges_deleteEdges_of_cross G s M P hM.1
  have hAll : ∀ e ∈ internalEdgeFinset H s,
      e ∈ coveredInternalEdges H s P := by
    by_contra hnot
    push_neg at hnot
    obtain ⟨e, heH, heUncovered⟩ := hnot
    have heG : e ∈ internalEdgeFinset G s := by
      simpa only [H, internalEdgeFinset_deleteEdges_of_cross G s M hM.1]
        using heH
    have heSide := heG
    rw [internalEdgeFinset_eq_union_sides] at heSide
    by_cases hcoverS : ∀ f ∈ sideEdgeFinset G s.toFinset,
        f ∈ coveredInternalEdges H s P
    · by_cases hcoverT : ∀ f ∈ sideEdgeFinset G sᶜ.toFinset,
          f ∈ coveredInternalEdges H s P
      · rcases mem_union.mp heSide with heS | heT
        · exact heUncovered (hcoverS e heS)
        · exact heUncovered (hcoverT e heT)
      · push_neg at hcoverT
        obtain ⟨f, hfT, hfUncovered⟩ := hcoverT
        have hcoverSG : ∀ q ∈ sideEdgeFinset G s.toFinset,
            q ∈ coveredInternalEdges G s P := by
          intro q hq
          rw [← hcoveredEq]
          exact hcoverS q hq
        have hlower := proposition42_claim44_pair hM hP hPmax hcoverSG
          hfT hfUncovered hwmax hsideS hsevenS
        exact proposition42_contradiction_of_coveredSize_and_claims
          (n := n) (k := (internalEdgeFinset G s).card) (m := P.card)
          (G := G) x (fractionalSize Gᶜ w) hn hk hupper hcovered
          (Or.inr hlower)
    · push_neg at hcoverS
      obtain ⟨eS, heS, heSUncovered⟩ := hcoverS
      by_cases hcoverT : ∀ f ∈ sideEdgeFinset G sᶜ.toFinset,
          f ∈ coveredInternalEdges H s P
      · have hMcomp : IsCrossMatching sᶜ M :=
          (isCrossMatching_set_compl s M).2 hM
        have hPcomp : IsInternalCrossPacking H sᶜ P :=
          (isInternalCrossPacking_set_compl_iff H s P).2 hP
        have hPmaxComp : ∀ Q : Finset (Finset (Fin n)),
            IsInternalCrossPacking H sᶜ Q → Q.card ≤ P.card := by
          intro Q hQ
          exact hPmax Q ((isInternalCrossPacking_set_compl_iff H s Q).1 hQ)
        have hwmaxComp : ∀ q : Finset (Fin n) → ℝ,
            IsFractionalInternalCrossPacking Gᶜ sᶜ q →
              fractionalSize Gᶜ q ≤ fractionalSize Gᶜ w := by
          intro q hq
          apply hwmax q
          simpa [IsFractionalInternalCrossPacking] using hq
        have hlowerComp := proposition42_claim44_pair hMcomp hPcomp hPmaxComp
          (by
            intro q hq
            have hq' : q ∈ sideEdgeFinset G sᶜ.toFinset := by
              simpa [sideEdgeFinset] using hq
            have hqH : q ∈ coveredInternalEdges H s P := hcoverT q hq'
            have hqG : q ∈ coveredInternalEdges G s P := by
              rw [← hcoveredEq]
              exact hqH
            simpa only [coveredInternalEdges_set_compl] using hqG)
          (by simpa only [compl_compl] using heS) (by
            simpa only [coveredInternalEdges_set_compl] using heSUncovered)
          hwmaxComp
          (by simpa only [← Set.ncard_eq_toFinset_card'] using hsideT)
          (by simpa only [← Set.ncard_eq_toFinset_card'] using hsevenT)
        have hlower :
            (3 ≤ (internalEdgeFinset G s).card ∧
              (n : ℝ) / 2 - x - 3 * (P.card : ℝ) - 2 ≤
                2 * fractionalSize Gᶜ w) ∨
            ((internalEdgeFinset G s).card ≤ 2 ∧
              (n : ℝ) / 2 - x - 3 * (P.card : ℝ) - 3 ≤
                2 * fractionalSize Gᶜ w) := by
          simpa only [internalEdgeFinset_set_compl] using hlowerComp
        exact proposition42_contradiction_of_coveredSize_and_claims
          (n := n) (k := (internalEdgeFinset G s).card) (m := P.card)
          (G := G) x (fractionalSize Gᶜ w) hn hk hupper hcovered
          (Or.inr hlower)
      · push_neg at hcoverT
        obtain ⟨eT, heT, heTUncovered⟩ := hcoverT
        have hboth := proposition42_claim43_pairs
          hM hP hPmax heS heT heSUncovered heTUncovered hwmax
        exact proposition42_contradiction_of_coveredSize_and_claims
          (n := n) (k := (internalEdgeFinset G s).card) (m := P.card)
          (G := G) x (fractionalSize Gᶜ w) hn hk hupper hcovered
          (Or.inl (by simpa using hboth))
  apply isInternalEdgeCoveringCrossPacking_of_covers hP
  intro e he
  have heCovered := hAll e he
  exact (mem_filter.mp heCovered).2

/-- Proposition 4.2 after isolating precisely the no-cycle inputs supplied by
Proposition 4.1 and Corollary 2.12.  This theorem makes both extremal choices
from the paper: `P` is a largest integral blue cross-triangle packing after
deleting the forbidden cross matching, and `w` is a largest fractional red
cross-triangle packing.  The remaining callback is exactly the weighted
capacity-decomposition/truncation construction, including the common
partition-imbalance parameter `x`.

Keeping that callback explicit here is important for the module dependency
graph: the theorem producing it imports the almost-bipartite part-size result,
which in turn imports this file. -/
theorem exists_internalEdgeCoveringCrossPacking_of_proposition42_completion
    {n : ℕ} (hn : 22 ≤ n) {G : SimpleGraph (Fin n)} {s : Set (Fin n)}
    {M : Finset (Sym2 (Fin n))} (hM : IsCrossMatching s M)
    (hk : (internalEdgeFinset G s).card ≤ n / 8)
    (hupper : FractionalCoveredSizeAtMost G
      ((n : ℝ) * ((n : ℝ) - 1) / 4))
    (hparts :
      (internalEdgeFinset G s).card + 4 ≤ s.ncard ∧
      (internalEdgeFinset G s).card + 4 ≤ sᶜ.ncard ∧
      7 ≤ s.ncard ∧ 7 ≤ sᶜ.ncard)
    (hcompletion :
      ∀ (P : Finset (Finset (Fin n))),
        IsInternalCrossPacking
            (G.deleteEdges (M : Set (Sym2 (Fin n)))) s P →
        (∀ Q : Finset (Finset (Fin n)),
          IsInternalCrossPacking
              (G.deleteEdges (M : Set (Sym2 (Fin n)))) s Q →
            Q.card ≤ P.card) →
        ∀ (w : Finset (Fin n) → ℝ),
          IsFractionalInternalCrossPacking Gᶜ s w →
          (∀ q : Finset (Fin n) → ℝ,
            IsFractionalInternalCrossPacking Gᶜ s q →
              fractionalSize Gᶜ q ≤ fractionalSize Gᶜ w) →
          ∃ x : ℝ,
            (n : ℝ) / 2 - x ≤ (s.toFinset.card : ℝ) ∧
            (n : ℝ) / 2 - x ≤ (sᶜ.toFinset.card : ℝ) ∧
            HasFractionalCoveredSizeAtLeast G
              ((n : ℝ) ^ 2 / 4 - (n : ℝ) / 2 + x ^ 2 -
                ((internalEdgeFinset G s).card : ℝ) +
                3 * (P.card : ℝ) + 2 * fractionalSize Gᶜ w)) :
    ∃ P : Finset (Finset (Fin n)),
      IsInternalEdgeCoveringCrossPacking
        (G.deleteEdges (M : Set (Sym2 (Fin n)))) s P := by
  classical
  obtain ⟨P, hP, hPmax⟩ :=
    exists_maximum_internalCrossPacking
      (G.deleteEdges (M : Set (Sym2 (Fin n)))) s
  obtain ⟨w, hw, hwmax⟩ :=
    exists_maximal_fractionalInternalCrossPacking Gᶜ s
  obtain ⟨x, hsideS, hsideT, hcovered⟩ :=
    hcompletion P hP hPmax w hw hwmax
  refine ⟨P, isInternalEdgeCoveringCrossPacking_of_proposition42_data
    hn hM hk hupper hP hPmax hwmax hsideS hsideT ?_ ?_ hcovered⟩
  · simpa only [Set.ncard_eq_toFinset_card'] using hparts.2.2.1
  · simpa only [Set.ncard_eq_toFinset_card'] using hparts.2.2.2

/-- Full matching-avoidance form of Proposition 4.2.  The forbidden matching
is arbitrary and need not consist of edges of `G`: deleting a nonedge has no
effect.  This is the form required in the almost-bipartite extension lemma. -/
def AlmostBipartiteIntegralCrossPackingAvoiding : Prop :=
  ∀ n : ℕ, 22 ≤ n → ∀ (G : SimpleGraph (Fin n)) (s : Set (Fin n))
      (M : Finset (Sym2 (Fin n))),
    IsCrossMatching s M →
      (internalEdgeFinset G s).card ≤ n / 8 →
        FractionalCoveredSizeAtMost G ((n : ℝ) * ((n : ℝ) - 1) / 4) →
          ∃ P : Finset (Finset (Fin n)),
            IsInternalEdgeCoveringCrossPacking
              (G.deleteEdges (M : Set (Sym2 (Fin n)))) s P

/-- Finite certificate target for Proposition 4.2.  A proof may construct the
paper's maximal family of cross triangles, while a checker may instead return
the family directly; the kernel verifies all triangle, edge-disjointness, and
coverage fields through `IsInternalEdgeCoveringCrossPacking`. -/
def AlmostBipartiteIntegralCrossPacking : Prop :=
  ∀ n : ℕ, 22 ≤ n → ∀ (G : SimpleGraph (Fin n)) (s : Set (Fin n)),
    (internalEdgeFinset G s).card ≤ n / 8 →
      FractionalCoveredSizeAtMost G ((n : ℝ) * ((n : ℝ) - 1) / 4) →
        ∃ P : Finset (Finset (Fin n)),
          IsInternalEdgeCoveringCrossPacking G s P

/-- The previously used empty-forbidden-set statement is the `M = ∅`
specialization of the paper's full Proposition 4.2. -/
theorem almostBipartiteIntegralCrossPacking_of_avoiding
    (h : AlmostBipartiteIntegralCrossPackingAvoiding) :
    AlmostBipartiteIntegralCrossPacking := by
  intro n hn G s hk hupper
  obtain ⟨P, hP⟩ := h n hn G s ∅ (isCrossMatching_empty s) hk hupper
  refine ⟨P, ?_⟩
  simpa [SimpleGraph.deleteEdges_empty] using hP

/-- Certificate-oriented version: Proposition 4.2 returns an explicit
integral packing, while the companion theorem returns the residual weight. -/
def AlmostBipartiteIntegralAndResidual : Prop :=
  ∀ n : ℕ, 26 ≤ n → ∀ (G : SimpleGraph (Fin n)) (s : Set (Fin n)),
    (internalEdgeFinset G s).card ≤ n / 8 →
      FractionalCoveredSizeAtMost G ((n : ℝ) * ((n : ℝ) - 1) / 4) →
      ∃ P : Finset (Finset (Fin n)),
        IsInternalEdgeCoveringCrossPacking G s P ∧
          HasResidualInternalDecompositions G s

lemma hasInternalEdgeCrossPacking_of_integral
    {G : SimpleGraph α} {s : Set α} {P : Finset (Finset α)}
    (hP : IsInternalEdgeCoveringCrossPacking G s P) :
    HasInternalEdgeCrossPacking G s := by
  refine ⟨integralPackingWeight P,
    isFractionalPacking_integralPackingWeight hP.2.1, ?_⟩
  rw [fractionalCoveredSize, fractionalSize_integralPackingWeight hP.1,
    hP.2.2.2.2]

theorem almostBipartiteCrossPacking_of_integral
    (h : AlmostBipartiteIntegralCrossPacking) :
    AlmostBipartiteCrossPacking := by
  intro n hn G s hk hupper
  obtain ⟨P, hP⟩ := h n hn G s hk hupper
  exact hasInternalEdgeCrossPacking_of_integral hP

theorem almostBipartiteCrossAndResidual_of_integralAndResidual
    (h : AlmostBipartiteIntegralAndResidual) :
    AlmostBipartiteCrossAndResidual := by
  intro n hn G s hs hupper
  obtain ⟨P, hP, hres⟩ := h n hn G s hs hupper
  exact ⟨hasInternalEdgeCrossPacking_of_integral hP, hres⟩

lemma HasFractionalCoveredSizeAtLeast.mono {G : SimpleGraph α} {q r : ℝ}
    (hqr : q ≤ r) (h : HasFractionalCoveredSizeAtLeast G r) :
    HasFractionalCoveredSizeAtLeast G q := by
  obtain ⟨wR, wB, hwR, hwB, hsize⟩ := h
  exact ⟨wR, wB, hwR, hwB, hqr.trans hsize⟩

lemma twoColorCoveredSize_compl (G : SimpleGraph α)
    (wR wB : Finset α → ℝ) :
    twoColorCoveredSize Gᶜ wR wB = twoColorCoveredSize G wB wR := by
  simp [twoColorCoveredSize, add_comm]

lemma FractionalCoveredSizeAtMost.compl {G : SimpleGraph α} {q : ℝ}
    (h : FractionalCoveredSizeAtMost G q) :
    FractionalCoveredSizeAtMost Gᶜ q := by
  intro wR wB hwR hwB
  have hwB' : IsFractionalPacking G wB := by simpa using hwB
  have hbound := h wB wR hwB' hwR
  simpa [twoColorCoveredSize, add_comm] using hbound

lemma HasFractionalCoveredSizeAtLeast.compl {G : SimpleGraph α} {q : ℝ}
    (h : HasFractionalCoveredSizeAtLeast Gᶜ q) :
    HasFractionalCoveredSizeAtLeast G q := by
  obtain ⟨wR, wB, hwR, hwB, hsize⟩ := h
  refine ⟨wB, wR, ?_, hwR, ?_⟩
  · simpa using hwB
  · simpa [twoColorCoveredSize_compl] using hsize

lemma hasFractionalCoveredSizeAtLeast_of_cross_and_residual
    {G : SimpleGraph α} {s : Set α}
    (hcross : HasInternalEdgeCrossPacking G s)
    (hres : HasResidualInternalDecompositions G s) :
    HasFractionalCoveredSizeAtLeast G
      (((s.ncard.choose 2 + sᶜ.ncard.choose 2 : ℕ) : ℝ)) := by
  obtain ⟨wG, hwG, hGsize⟩ := hcross
  obtain ⟨wGc, hwGc, hGcsize⟩ := hres
  refine ⟨wG, wGc, hwG, hwGc, ?_⟩
  simp only [twoColorCoveredSize]
  have hk : (0 : ℝ) ≤ (internalEdgeFinset G s).card := by positivity
  nlinarith

theorem almostBipartiteInternalPairBound_of_crossAndResidual
    (hCR : AlmostBipartiteCrossAndResidual) :
    AlmostBipartiteInternalPairBound := by
  intro n hn G s hs hupper
  exact hasFractionalCoveredSizeAtLeast_of_cross_and_residual
    (hCR n hn G s hs hupper).1 (hCR n hn G s hs hupper).2

lemma sharpCoveredThreshold_le_stabilityThreshold {n : ℕ} (hn : 1 ≤ n) :
    ((((n - 1) ^ 2 / 4 : ℕ) : ℝ)) ≤
      (n : ℝ) * ((n : ℝ) - 1) / 4 := by
  calc
    ((((n - 1) ^ 2 / 4 : ℕ) : ℝ)) ≤
        (((n - 1) ^ 2 : ℕ) : ℝ) / (4 : ℕ) := Nat.cast_div_le
    _ = ((n : ℝ) - 1) ^ 2 / 4 := by
      rw [Nat.cast_pow, Nat.cast_sub hn]
      norm_num
    _ ≤ (n : ℝ) * ((n : ℝ) - 1) / 4 := by
      have hnreal : (1 : ℝ) ≤ n := by exact_mod_cast hn
      nlinarith

/-- The balanced bipartition minimizes the number of pairs internal to its
two parts.  This floor-sensitive form is the numerical core of Section 5. -/
lemma sharpThreshold_le_chooseTwo_add_chooseTwo
    {a b n : ℕ} (hn : 1 ≤ n) (hab : a + b = n) :
    (n - 1) ^ 2 / 4 ≤ a.choose 2 + b.choose 2 := by
  have habReal : (a : ℝ) + b = n := by exact_mod_cast hab
  have hpolyReal :
      (((n - 1) ^ 2 : ℕ) : ℝ) <
        4 * (((a.choose 2 + b.choose 2 : ℕ) : ℝ) + 1) := by
    rw [Nat.cast_pow, Nat.cast_sub hn, Nat.cast_add,
      Nat.cast_choose_two, Nat.cast_choose_two]
    have hsquare : 0 ≤ ((a : ℝ) - b) ^ 2 := sq_nonneg _
    nlinarith
  have hpolyNat :
      (n - 1) ^ 2 < 4 * (a.choose 2 + b.choose 2 + 1) := by
    exact_mod_cast hpolyReal
  have hdiv :
      (n - 1) ^ 2 / 4 < a.choose 2 + b.choose 2 + 1 := by
    rw [Nat.div_lt_iff_lt_mul (by norm_num)]
    simpa [mul_comm, mul_left_comm, mul_assoc] using hpolyNat
  omega

/-- Checked Section 5 deduction after the internal-edge/cross-triangle
construction has been supplied. -/
theorem almostBipartiteSharpBound_of_internalPairBound
    (hparts : AlmostBipartiteInternalPairBound) :
    AlmostBipartiteSharpBound := by
  intro n hn G hclose
  have hn1 : 1 ≤ n := by omega
  rcases fractionalCoveredSize_dichotomy G
      ((n : ℝ) * ((n : ℝ) - 1) / 4) with hlarge | hupper
  · exact hlarge.mono (sharpCoveredThreshold_le_stabilityThreshold hn1)
  · rcases hclose with hG | hGc
    · obtain ⟨s, hs⟩ := hG.partition_witness
      have hsum : s.ncard + sᶜ.ncard = n := by
        simpa using Set.ncard_add_ncard_compl s
      exact (hparts n hn G s hs hupper).mono (by
        exact_mod_cast sharpThreshold_le_chooseTwo_add_chooseTwo hn1 hsum)
    · obtain ⟨s, hs⟩ := hGc.partition_witness
      have hsum : s.ncard + sᶜ.ncard = n := by
        simpa using Set.ncard_add_ncard_compl s
      apply HasFractionalCoveredSizeAtLeast.compl
      exact (hparts n hn Gᶜ s hs hupper.compl).mono (by
        exact_mod_cast sharpThreshold_le_chooseTwo_add_chooseTwo hn1 hsum)

/-- The final non-computational deduction of Theorem 2.3 from its two
structural branches.  Thus the remaining work for the sharp theorem is
precisely to prove `FractionalStabilityDichotomy` (including its finite
certificates) and `AlmostBipartiteSharpBound` (including the companion
almost-complete decomposition theorem). -/
theorem gruslysLetzterFractional_of_structural
    (hstable : FractionalStabilityDichotomy)
    (hclose : AlmostBipartiteSharpBound) : GruslysLetzterFractional := by
  intro n hn G
  have hone : 1 ≤ n := by omega
  rcases hstable n hn G with hlarge | hnear
  · have hsharp := hlarge.mono (sharpCoveredThreshold_le_stabilityThreshold hone)
    obtain ⟨wR, wB, hwR, hwB, hsize⟩ := hsharp
    exact ⟨wR, wB, hwR, hwB, hsize⟩
  · obtain ⟨wR, wB, hwR, hwB, hsize⟩ := hclose n hn G hnear
    exact ⟨wR, wB, hwR, hwB, hsize⟩

end

end Erdos76
