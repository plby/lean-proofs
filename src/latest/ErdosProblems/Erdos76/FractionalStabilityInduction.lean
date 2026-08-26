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
import ErdosProblems.Erdos76.FractionalTransport
import ErdosProblems.Erdos76.GruslysLetzter
import Mathlib.Tactic

/-!
# The deletion induction for fractional stability

This downstream module isolates the human induction which turns the finite
classification and the almost-bipartite one-vertex extension lemma into the
fractional stability theorem.  The two computer- or case-analysis-heavy
ingredients remain explicit propositions.  Everything between them--vertex
deletion averaging, relabelling a deleted vertex to the final `Fin` point,
assembling a coherent chain, excluding its pentagon branch, and propagating
the close-to-bipartite branch--is proved here.
-/

open Finset
open scoped BigOperators

namespace Erdos76

noncomputable section

attribute [local instance] Classical.propDecidable

/-- The sharp quadratic threshold used throughout the fractional stability
induction. -/
def stabilityThreshold (n : ℕ) : ℝ :=
  (n : ℝ) * ((n : ℝ) - 1) / 4

/-- A standard labelled chain on the orders from `lo` through `hi`, with the
sharp stability upper bound at every order and with every transition given
by the canonical initial embedding `Fin m → Fin (m+1)`. -/
def IsStandardFractionalUpperChain
    (C : ∀ m : ℕ, SimpleGraph (Fin m)) (lo hi : ℕ) : Prop :=
  (∀ m : ℕ, lo ≤ m → m ≤ hi →
      FractionalCoveredSizeAtMost (C m) (stabilityThreshold m)) ∧
    ∀ m : ℕ, lo ≤ m → m < hi →
      IsInitialVertexExtension (C m) (C (m + 1))

/-- Kernel-facing interface of the finite classification.  Although `C` is
a family at every natural order, only its coherent segment from 17 through
22 is inspected. -/
def FiniteStabilityClassification : Prop :=
  ∀ C : ∀ m : ℕ, SimpleGraph (Fin m),
    IsStandardFractionalUpperChain C 17 22 →
      IsPentagonExceptional (C 17) ∨
        CloseToBipartite (C 22) 2 ∨ CloseToBipartite (C 22)ᶜ 2

/-- Human almost-bipartite extension interface.  This is the structural
one-vertex lemma iterated after the finite classification has produced a
two-close graph at order 22. -/
def AlmostBipartiteStabilityExtension : Prop :=
  ∀ n : ℕ, 22 ≤ n →
    ∀ (H : SimpleGraph (Fin n)) (G : SimpleGraph (Fin (n + 1))),
      IsInitialVertexExtension H G →
      FractionalCoveredSizeAtMost H (stabilityThreshold n) →
      FractionalCoveredSizeAtMost G (stabilityThreshold (n + 1)) →
      (CloseToBipartite H (n / 8) ∨ CloseToBipartite Hᶜ (n / 8)) →
      CloseToBipartite G ((n + 1) / 8) ∨
        CloseToBipartite Gᶜ ((n + 1) / 8)

private lemma FractionalCoveredSizeAtMost.relabel
    { α β : Type* } [Fintype α] [DecidableEq α]
    [Fintype β] [DecidableEq β]
    {G : SimpleGraph α} {q : ℝ}
    (hG : FractionalCoveredSizeAtMost G q) (φ : α ≃ β) :
    FractionalCoveredSizeAtMost (G.map φ.toEmbedding) q := by
  classical
  letI : DecidableRel G.Adj := Classical.decRel _
  letI : DecidableRel (G.map φ.toEmbedding).Adj := Classical.decRel _
  intro wR wB hwR hwB
  let uR : Finset α → ℝ := relabelWeight φ.symm wR
  let uB : Finset α → ℝ := relabelWeight φ.symm wB
  have hmap : (G.map φ.toEmbedding).map φ.symm.toEmbedding = G := by
    rw [SimpleGraph.map_map]
    simpa using G.map_id
  have huR : IsFractionalPacking G uR := by
    simpa only [uR, hmap] using hwR.relabel φ.symm
  have hc : (G.map φ.toEmbedding)ᶜ.map φ.symm.toEmbedding = Gᶜ := by
    rw [← compl_map_equiv (G.map φ.toEmbedding) φ.symm, hmap]
  have huB : IsFractionalPacking Gᶜ uB := by
    simpa only [uB, hc] using hwB.relabel φ.symm
  have hupper := hG uR uB huR huB
  have hsR : fractionalCoveredSize G uR =
      fractionalCoveredSize (G.map φ.toEmbedding) wR := by
    simpa only [uR, hmap] using
      fractionalCoveredSize_relabel (G.map φ.toEmbedding) φ.symm wR
  have hsB : fractionalCoveredSize Gᶜ uB =
      fractionalCoveredSize (G.map φ.toEmbedding)ᶜ wB := by
    simpa only [uB, hc] using
      fractionalCoveredSize_relabel (G.map φ.toEmbedding)ᶜ φ.symm wB
  simpa [twoColorCoveredSize, hsR, hsB] using hupper

private lemma partitionCloseToBipartite_relabel
    { α β : Type* } [Fintype α] [DecidableEq α]
    [Fintype β] [DecidableEq β]
    {G : SimpleGraph α} {k : ℕ}
    (hG : PartitionCloseToBipartite G k) (φ : α ≃ β) :
    PartitionCloseToBipartite (G.map φ.toEmbedding) k := by
  classical
  obtain ⟨s, hs⟩ := hG
  let t : Set β := φ '' s
  refine ⟨t, ?_⟩
  have hfinset :
      internalEdgeFinset (G.map φ.toEmbedding) t =
        (internalEdgeFinset G s).map φ.toEmbedding.sym2Map := by
    ext p
    induction p using Sym2.inductionOn with
    | hf a b =>
        let x := φ.symm a
        let y := φ.symm b
        have hax : φ x = a := φ.apply_symm_apply a
        have hby : φ y = b := φ.apply_symm_apply b
        have hmapAdj :
            (G.map φ.toEmbedding).Adj a b ↔ G.Adj x y := by
          rw [← hax, ← hby]
          exact SimpleGraph.map_adj_apply
        simp only [internalEdgeFinset, mem_filter, SimpleGraph.mem_edgeFinset,
          SimpleGraph.mem_edgeSet, sameSide_mk, mem_map]
        constructor
        · rintro ⟨hab, hside⟩
          refine ⟨s(x, y), ⟨?_, ?_⟩, ?_⟩
          · exact hmapAdj.mp hab
          · simpa [x, y, hax, hby, t] using hside
          · simpa [x, y, hax, hby]
        · rintro ⟨q, hq, hqeq⟩
          have hq' : q = s(x, y) := by
            apply φ.toEmbedding.sym2Map.injective
            simpa [x, y, hax, hby] using hqeq
          subst q
          exact ⟨hmapAdj.mpr hq.1,
            by simpa [x, y, hax, hby, t] using hq.2⟩
  rw [hfinset, card_map]
  exact hs

/-- A partition with at most `k` same-side edges gives an explicit deletion
witness making the graph bipartite. -/
theorem closeToBipartite_of_partitionClose
    { α : Type* } [Fintype α] [DecidableEq α]
    {G : SimpleGraph α} {k : ℕ}
    (hG : PartitionCloseToBipartite G k) : CloseToBipartite G k := by
  classical
  obtain ⟨s, hs⟩ := hG
  let D := internalEdgeFinset G s
  refine ⟨D, ?_, hs, ?_⟩
  · intro e he
    exact (mem_filter.mp he).1
  · have hbip :
        (G.deleteEdges (D : Set (Sym2 α))).IsBipartiteWith s sᶜ := by
      refine ⟨disjoint_compl_right, ?_⟩
      intro u v huv
      have huv' := SimpleGraph.deleteEdges_adj.mp huv
      have heG : s(u, v) ∈ G.edgeFinset := by
        simpa [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet] using huv'.1
      have hnSame : ¬ (u ∈ s ↔ v ∈ s) := by
        intro hsame
        exact huv'.2 (by
          change s(u, v) ∈ D
          exact mem_filter.mpr ⟨heG, hsame⟩)
      by_cases hu : u ∈ s
      · have hv : v ∉ s := by
          intro hv
          exact hnSame ⟨fun _ ↦ hv, fun _ ↦ hu⟩
        exact Or.inl ⟨hu, hv⟩
      · exact Or.inr ⟨by simpa using hu, by
            by_contra hv
            exact hnSame (iff_of_false hu hv)⟩
    exact hbip.isBipartite

private lemma CloseToBipartite.relabel
    { α β : Type* } [Fintype α] [DecidableEq α]
    [Fintype β] [DecidableEq β]
    {G : SimpleGraph α} {k : ℕ}
    (hG : CloseToBipartite G k) (φ : α ≃ β) :
    CloseToBipartite (G.map φ.toEmbedding) k :=
  closeToBipartite_of_partitionClose
    (partitionCloseToBipartite_relabel hG.partition_witness φ)

private lemma stabilityThreshold_scale (m : ℕ) (hm : 2 ≤ m) :
    stabilityThreshold (m + 1) =
      ((m + 1 : ℕ) : ℝ) * stabilityThreshold m /
        (((m + 1 : ℕ) : ℝ) - 2) := by
  have hne : (((m + 1 : ℕ) : ℝ) - 2) ≠ 0 := by
    have : (1 : ℝ) < m := by exact_mod_cast (show 1 < m by omega)
    norm_num
    linarith
  apply (eq_div_iff hne).2
  simp only [stabilityThreshold, Nat.cast_add, Nat.cast_one]
  ring

/-- A deletion-upper witness is exactly an upper bound for the induced graph
on the remaining vertices.  This is the transport step deliberately kept
separate from the averaging calculation in `GruslysLetzter`. -/
private lemma fractionalCoveredSizeAtMost_induce_erase
    { α : Type* } [Fintype α] [DecidableEq α]
    (G : SimpleGraph α) (u : α) (q : ℝ)
    (hdel : DeletionFractionalCoveredSizeAtMost G u q) :
    FractionalCoveredSizeAtMost
      (G.induce ((univ.erase u : Finset α) : Set α)) q := by
  classical
  let S : Finset α := univ.erase u
  let H : SimpleGraph S := G.induce (S : Set α)
  intro wR wB hwR hwB
  let vR : Finset α → ℝ := extendInducedWeight S wR
  let vB : Finset α → ℝ := extendInducedWeight S wB
  have huS : u ∉ S := by simp [S]
  have hzero (K : SimpleGraph α) (w : Finset S → ℝ) :
      ∀ e ∈ K.edgeFinset, u ∈ e.toFinset →
        fractionalEdgeLoad K (extendInducedWeight S w) e = 0 := by
    intro e he hue
    induction e using Sym2.inductionOn with
    | hf a b =>
        have hua : u = a ∨ u = b := by simpa using hue
        rcases hua with rfl | rfl
        · exact fractionalEdgeLoad_extendInducedWeight_eq_zero_of_not_mem
            K S w u b huS
        · rw [show s(a, u) = s(u, a) from
              Sym2.sound (Sym2.Rel.swap a u)]
          exact fractionalEdgeLoad_extendInducedWeight_eq_zero_of_not_mem
            K S w u a huS
  have hvR : IsDeletionPacking G u vR := by
    refine ⟨?_, ?_⟩
    · exact hwR.extendInduced
    · exact hzero G wR
  have hvB : IsDeletionPacking Gᶜ u vB := by
    refine ⟨?_, ?_⟩
    · exact hwB.extendInduced_compl
    · exact hzero Gᶜ wB
  have hupper := hdel vR vB hvR hvB
  dsimp only [vR, vB] at hupper
  rw [twoColorCoveredSize, fractionalCoveredSize_extendInducedWeight,
    fractionalCoveredSize_extendInducedWeight, compl_induce] at hupper
  simpa only [H, S, twoColorCoveredSize] using hupper

/-- One averaging step, followed by an explicit permutation which sends the
deleted vertex to `Fin.last m`, produces a standard initial extension. -/
private theorem exists_standard_deletion_step
    (m : ℕ) (hm : 17 ≤ m) (G : SimpleGraph (Fin (m + 1)))
    (hG : FractionalCoveredSizeAtMost G (stabilityThreshold (m + 1))) :
    ∃ (H : SimpleGraph (Fin m)) (P : SimpleGraph (Fin (m + 1)))
      (φ : Fin (m + 1) ≃ Fin (m + 1)),
      FractionalCoveredSizeAtMost H (stabilityThreshold m) ∧
      FractionalCoveredSizeAtMost P (stabilityThreshold (m + 1)) ∧
      IsInitialVertexExtension H P ∧ P = G.map φ.toEmbedding := by
  have hcard : 3 ≤ Fintype.card (Fin (m + 1)) := by simp; omega
  have hscale : stabilityThreshold (m + 1) ≤
      (Fintype.card (Fin (m + 1)) : ℝ) * stabilityThreshold m /
        ((Fintype.card (Fin (m + 1)) : ℝ) - 2) := by
    rw [Fintype.card_fin, ← stabilityThreshold_scale m (by omega)]
  obtain ⟨u, hu⟩ := exists_deletion_fractionalCoveredSizeAtMost
    G (stabilityThreshold (m + 1)) (stabilityThreshold m) hcard hG hscale
  let S : Finset (Fin (m + 1)) := univ.erase u
  have hScard : Fintype.card S = m := by
    rw [Fintype.card_coe]
    simp [S]
  let e : S ≃ Fin m := Fintype.equivFinOfCardEq hScard
  obtain ⟨φ, hφ⟩ := Equiv.Perm.exists_extending_pair
    (fun i : Fin m ↦ ((e.symm i : S) : Fin (m + 1)))
    (fun i : Fin m ↦ i.castSucc)
    (Subtype.val_injective.comp e.symm.injective) (Fin.castSucc_injective m)
  let K : SimpleGraph S := G.induce (S : Set (Fin (m + 1)))
  let H : SimpleGraph (Fin m) := K.map e.toEmbedding
  let P : SimpleGraph (Fin (m + 1)) := G.map φ.toEmbedding
  have hK : FractionalCoveredSizeAtMost K (stabilityThreshold m) := by
    simpa only [K, S] using fractionalCoveredSizeAtMost_induce_erase
      G u (stabilityThreshold m) hu
  have hH : FractionalCoveredSizeAtMost H (stabilityThreshold m) := by
    exact hK.relabel e
  have hP : FractionalCoveredSizeAtMost P (stabilityThreshold (m + 1)) := by
    exact hG.relabel φ
  refine ⟨H, P, φ, hH, hP, ?_, rfl⟩
  intro a b
  dsimp only [H, K, P]
  have hleft :
      ((G.induce (S : Set (Fin (m + 1)))).map e.toEmbedding).Adj a b ↔
        (G.induce (S : Set (Fin (m + 1)))).Adj (e.symm a) (e.symm b) := by
    rw [← SimpleGraph.comap_symm (G.induce (S : Set (Fin (m + 1)))) e]
    rfl
  rw [hleft]
  change G.Adj ((e.symm a : S) : Fin (m + 1))
      ((e.symm b : S) : Fin (m + 1)) ↔
    (G.map φ.toEmbedding).Adj a.castSucc b.castSucc
  rw [← hφ a, ← hφ b]
  exact (SimpleGraph.map_adj_apply
    (G := G) (f := φ.toEmbedding)
      (a := ((e.symm a : S) : Fin (m + 1)))
      (b := ((e.symm b : S) : Fin (m + 1)))).symm

private def replaceGraph
    (C : ∀ k : ℕ, SimpleGraph (Fin k)) (m : ℕ)
    (G : SimpleGraph (Fin m)) : ∀ k : ℕ, SimpleGraph (Fin k) :=
  fun k ↦ if h : k = m then
    cast (congrArg (fun r ↦ SimpleGraph (Fin r)) h.symm) G
  else C k

@[simp] private lemma replaceGraph_same
    (C : ∀ k : ℕ, SimpleGraph (Fin k)) (m : ℕ)
    (G : SimpleGraph (Fin m)) : replaceGraph C m G m = G := by
  simp [replaceGraph]

private lemma replaceGraph_of_ne
    (C : ∀ k : ℕ, SimpleGraph (Fin k)) (m k : ℕ)
    (G : SimpleGraph (Fin m)) (hkm : k ≠ m) :
    replaceGraph C m G k = C k := by
  simp [replaceGraph, hkm]

/-- Repeated averaging and the preceding permutation-extension step produce
one coherent standard chain.  Its top graph may be a relabelling of the
original graph; the relabelling is retained explicitly for the final
isomorphism-invariance step. -/
private theorem exists_standard_fractional_upper_chain :
    ∀ hi : ℕ, 17 ≤ hi → ∀ G : SimpleGraph (Fin hi),
      FractionalCoveredSizeAtMost G (stabilityThreshold hi) →
      ∃ (C : ∀ m : ℕ, SimpleGraph (Fin m)) (φ : Fin hi ≃ Fin hi),
        IsStandardFractionalUpperChain C 17 hi ∧
          C hi = G.map φ.toEmbedding := by
  intro hi hhi
  induction hi, hhi using Nat.le_induction with
  | base =>
      intro G hG
      let C : ∀ m : ℕ, SimpleGraph (Fin m) :=
        replaceGraph (fun m ↦ (⊥ : SimpleGraph (Fin m))) 17 G
      refine ⟨C, Equiv.refl (Fin 17), ?_, ?_⟩
      · constructor
        · intro m hm17 hmle
          have hm : m = 17 := by omega
          subst m
          simpa only [C, replaceGraph_same] using hG
        · intro m hm17 hmlt
          omega
      · change G = G.map (Equiv.refl (Fin 17)).toEmbedding
        ext a b
        simp [SimpleGraph.map_adj]
  | succ m hm ih =>
      intro G hG
      obtain ⟨H, P, φ, hH, hP, hHP, hPiso⟩ :=
        exists_standard_deletion_step m hm G hG
      obtain ⟨C, ψ, hC, htop⟩ := ih H hH
      obtain ⟨σ, hσ⟩ := Equiv.Perm.exists_extending_pair
        (fun i : Fin m ↦ i.castSucc)
        (fun i : Fin m ↦ (ψ i).castSucc)
        (Fin.castSucc_injective m)
        ((Fin.castSucc_injective m).comp ψ.injective)
      let P' : SimpleGraph (Fin (m + 1)) := P.map σ.toEmbedding
      have hP' : FractionalCoveredSizeAtMost P'
          (stabilityThreshold (m + 1)) := hP.relabel σ
      have hCP : IsInitialVertexExtension (C m) P' := by
        intro a b
        have hleft : (C m).Adj a b ↔
            H.Adj (ψ.symm a) (ψ.symm b) := by
          rw [htop, ← SimpleGraph.comap_symm H ψ]
          rfl
        rw [hleft, hHP]
        change P.Adj (ψ.symm a).castSucc (ψ.symm b).castSucc ↔
          (P.map σ.toEmbedding).Adj a.castSucc b.castSucc
        have hσa : σ ((ψ.symm a).castSucc) = a.castSucc := by
          simpa using hσ (ψ.symm a)
        have hσb : σ ((ψ.symm b).castSucc) = b.castSucc := by
          simpa using hσ (ψ.symm b)
        rw [← hσa, ← hσb]
        exact (SimpleGraph.map_adj_apply
          (G := P) (f := σ.toEmbedding)
            (a := (ψ.symm a).castSucc)
            (b := (ψ.symm b).castSucc)).symm
      let C' : ∀ r : ℕ, SimpleGraph (Fin r) :=
        replaceGraph C (m + 1) P'
      refine ⟨C', φ.trans σ, ?_, ?_⟩
      · constructor
        · intro r hr17 hrle
          by_cases hr : r = m + 1
          · subst r
            simpa only [C', replaceGraph_same] using hP'
          · dsimp only [C']
            rw [replaceGraph_of_ne C (m + 1) r P' hr]
            exact hC.1 r hr17 (by omega)
        · intro r hr17 hrlt
          by_cases hrm : r = m
          · subst r
            dsimp only [C']
            rw [replaceGraph_of_ne C (m + 1) m P' (by omega),
              replaceGraph_same]
            exact hCP
          · have hrm' : r < m := by omega
            dsimp only [C']
            rw [replaceGraph_of_ne C (m + 1) r P' (by omega),
              replaceGraph_of_ne C (m + 1) (r + 1) P' (by omega)]
            exact hC.2 r hr17 hrm'
      · dsimp only [C']
        rw [replaceGraph_same]
        dsimp only [P']
        rw [hPiso, SimpleGraph.map_map]
        rfl

private theorem closeToBipartite_of_standard_chain
    (hExt : AlmostBipartiteStabilityExtension)
    (hi : ℕ) (hhi : 22 ≤ hi)
    (C : ∀ m : ℕ, SimpleGraph (Fin m))
    (hC : IsStandardFractionalUpperChain C 17 hi)
    (h22 : CloseToBipartite (C 22) (22 / 8) ∨
      CloseToBipartite (C 22)ᶜ (22 / 8)) :
    CloseToBipartite (C hi) (hi / 8) ∨
      CloseToBipartite (C hi)ᶜ (hi / 8) := by
  induction hi, hhi using Nat.le_induction with
  | base => exact h22
  | succ m hm ih =>
      have hCm : IsStandardFractionalUpperChain C 17 m := by
        constructor
        · intro r hr17 hrm
          exact hC.1 r hr17 (by omega)
        · intro r hr17 hrm
          exact hC.2 r hr17 (by omega)
      exact hExt m hm (C m) (C (m + 1))
        (hC.2 m (by omega) (by omega))
        (hC.1 m (by omega) (by omega))
        (hC.1 (m + 1) (by omega) (by omega)) (ih hCm)

/-- The complete human induction.  The only hypotheses are the finite
classification, the verified pentagon one-step table, and the
almost-bipartite one-vertex extension lemma. -/
theorem fractionalStabilityUpperBound_of_classification_extension
    (hclass : FiniteStabilityClassification)
    (hpent : PentagonExtensionStep)
    (hExt : AlmostBipartiteStabilityExtension) :
    FractionalStabilityUpperBound := by
  intro n hn G hG
  change FractionalCoveredSizeAtMost G (stabilityThreshold n) at hG
  obtain ⟨C, φ, hC, htop⟩ :=
    exists_standard_fractional_upper_chain n (by omega) G hG
  have hC22 : IsStandardFractionalUpperChain C 17 22 := by
    constructor
    · intro m hm17 hm22
      exact hC.1 m hm17 (by omega)
    · intro m hm17 hm22
      exact hC.2 m hm17 (by omega)
  rcases hclass C hC22 with hExceptional | hClose22
  · exfalso
    apply no_pentagon_chain_of_extension_step hpent
    refine ⟨C, hExceptional, ?_, ?_⟩
    · intro m hm17 hm26
      exact hC.2 m hm17 (by omega)
    · intro m hm18 hm26
      change FractionalCoveredSizeAtMost (C m) (stabilityThreshold m)
      exact hC.1 m (by omega) (by omega)
  · have hClose22' : CloseToBipartite (C 22) (22 / 8) ∨
        CloseToBipartite (C 22)ᶜ (22 / 8) := by
      norm_num
      exact hClose22
    have hCloseTop := closeToBipartite_of_standard_chain
      hExt n (by omega) C hC hClose22'
    rw [htop] at hCloseTop
    have hmap : (G.map φ.toEmbedding).map φ.symm.toEmbedding = G := by
      rw [SimpleGraph.map_map]
      simpa using G.map_id
    rcases hCloseTop with hR | hB
    · left
      simpa only [hmap] using hR.relabel φ.symm
    · right
      have hc : (G.map φ.toEmbedding)ᶜ.map φ.symm.toEmbedding = Gᶜ := by
        rw [← compl_map_equiv (G.map φ.toEmbedding) φ.symm, hmap]
      simpa only [hc] using hB.relabel φ.symm

/-- Dichotomy form, obtained from the upper-bound induction by the general
finite-LP dichotomy already proved in `GruslysLetzter`. -/
theorem fractionalStabilityDichotomy_of_classification_extension
    (hclass : FiniteStabilityClassification)
    (hpent : PentagonExtensionStep)
    (hExt : AlmostBipartiteStabilityExtension) :
    FractionalStabilityDichotomy :=
  fractionalStabilityDichotomy_of_upperBound
    (fractionalStabilityUpperBound_of_classification_extension
      hclass hpent hExt)

end

end Erdos76
