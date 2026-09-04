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
import ErdosProblems.Erdos622.NashWilliamsBondy

/-!
# The elementary-separation part of Dirac stability

This file develops the separation branch of the Komlós--Sárközy--Szemerédi
stability lemma.  The central observation is exact (there are no asymptotic
losses): if every vertex has degree at least `k`, then every component has
more than `k` vertices, and every component after deleting a cut vertex has
at least `k` vertices.  Thus a disconnected graph, or a connected graph with
a cut vertex, already has the sparse-pair conclusion of the stability lemma,
with no crossing edges at all.

The remaining, two-connected branch is the longest-cycle/shifted-neighbourhood
argument from the appendix of Komlós--Sárközy--Szemerédi.  The definitions
below deliberately expose the exact finite separator statement needed by
that argument.
-/

open Finset
open scoped SimpleGraph

namespace Erdos622
namespace KSSStability

attribute [local instance] Classical.propDecidable

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V}

/-- The vertices reachable from `x`. -/
noncomputable def reachableFinset (G : SimpleGraph V) (x : V) : Finset V :=
  Finset.univ.filter fun y => G.Reachable x y

@[simp] theorem mem_reachableFinset {x y : V} :
    y ∈ reachableFinset G x ↔ G.Reachable x y := by
  simp [reachableFinset]

theorem self_mem_reachableFinset (x : V) : x ∈ reachableFinset G x := by
  simp

/-- A neighbour of a vertex in a reachability component is in the same
component. -/
theorem neighborFinset_subset_reachableFinset {x y : V}
    (hy : y ∈ reachableFinset G x) :
    G.neighborFinset y ⊆ reachableFinset G x := by
  intro z hz
  rw [mem_reachableFinset] at hy ⊢
  exact hy.trans ((G.mem_neighborFinset y z).mp hz).reachable

/-- Distinct reachability components have no edge between them. -/
theorem interedges_reachable_compl_eq_empty (x : V) :
    G.interedges (reachableFinset G x) (reachableFinset G x)ᶜ = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro e he
  have he' :
      (e.1 ∈ reachableFinset G x ∧ e.2 ∈ (reachableFinset G x)ᶜ) ∧
        G.Adj e.1 e.2 := by
    simpa [SimpleGraph.interedges_def] using he
  have hreach : G.Reachable x e.2 :=
    (mem_reachableFinset.mp he'.1.1).trans he'.2.reachable
  exact (Finset.mem_compl.mp he'.1.2) (mem_reachableFinset.mpr hreach)

/-- A component in a graph of minimum degree at least `k` has at least
`k+1` vertices. -/
theorem add_one_le_card_reachableFinset (hDegree : ∀ v : V, k ≤ G.degree v)
    (x : V) : k + 1 ≤ (reachableFinset G x).card := by
  have hsub : G.neighborFinset x ∪ {x} ⊆ reachableFinset G x := by
    intro y hy
    rcases Finset.mem_union.mp hy with hy | hy
    · exact mem_reachableFinset.mpr
        ((G.mem_neighborFinset x y).mp hy).reachable
    · have hyx : y = x := Finset.mem_singleton.mp hy
      subst y
      exact self_mem_reachableFinset (G := G) x
  have hcard := Finset.card_le_card hsub
  have hdisj : Disjoint (G.neighborFinset x) {x} :=
    Finset.disjoint_singleton_right.mpr (G.notMem_neighborFinset_self x)
  rw [Finset.card_union_of_disjoint hdisj,
    G.card_neighborFinset_eq_degree, Finset.card_singleton] at hcard
  exact (Nat.add_le_add_right (hDegree x) 1).trans hcard

/-- Failure of reachability exposes two disjoint large sets with no crossing
edges.  This is the disconnected branch of Dirac stability. -/
theorem hasSparsePairAt_of_not_reachable {k b : ℕ}
    (hDegree : ∀ v : V, k ≤ G.degree v) {x y : V}
    (hxy : ¬ G.Reachable x y) :
    DiracStability.HasSparsePairAt G k b := by
  let A := reachableFinset G x
  let B := Aᶜ
  have hxA : k ≤ A.card := by
    exact (Nat.le_succ k).trans
      (by simpa [A] using add_one_le_card_reachableFinset (G := G) hDegree x)
  have hyB : y ∈ B := by
    simp only [B, A, Finset.mem_compl, mem_reachableFinset]
    exact hxy
  have hBcard : k ≤ B.card := by
    have hsub : G.neighborFinset y ⊆ B.erase y := by
      intro z hz
      have hyz := (G.mem_neighborFinset y z).mp hz
      apply Finset.mem_erase.mpr
      refine ⟨hyz.ne.symm, ?_⟩
      simp only [B, A, Finset.mem_compl, mem_reachableFinset]
      intro hxz
      exact hxy (hxz.trans hyz.symm.reachable)
    have hcard := Finset.card_le_card hsub
    rw [G.card_neighborFinset_eq_degree,
      Finset.card_erase_of_mem hyB] at hcard
    have hk := hDegree y
    omega
  exact DiracStability.hasSparsePairAt_of_emptyCut G
    (Finset.disjoint_left.mpr fun _ ha hb => (Finset.mem_compl.mp hb) ha)
    hxA hBcard
    (by simpa [A, B] using interedges_reachable_compl_eq_empty (G := G) x)

/-- Every disconnected graph at the near-Dirac minimum-degree scale already
satisfies the sparse-pair alternative. -/
theorem stabilityAlternative_of_not_preconnected {k b : ℕ}
    (hDegree : ∀ v : V, k ≤ G.degree v) (hG : ¬ G.Preconnected) :
    DiracStability.StabilityAlternative G k b := by
  change ¬ ∀ x y : V, G.Reachable x y at hG
  push Not at hG
  obtain ⟨x, y, hxy⟩ := hG
  exact Or.inr (Or.inr (hasSparsePairAt_of_not_reachable hDegree hxy))

/-! ## A cut vertex -/

/-- The graph obtained by deleting one vertex. -/
abbrev deleteVertex (G : SimpleGraph V) (c : V) :
    SimpleGraph {v : V // v ≠ c} :=
  G.induce {v : V | v ≠ c}

/-- A cut-vertex witness in a form which also records two surviving vertices
in distinct components. -/
def IsCutVertexWitness (G : SimpleGraph V) (c : V) : Prop :=
  ∃ x y : {v : V // v ≠ c}, ¬ (deleteVertex G c).Reachable x y

/-- The image in `V` of one component of `G-c`. -/
noncomputable def cutComponent (G : SimpleGraph V) (c : V)
    (x : {v : V // v ≠ c}) : Finset V :=
  (reachableFinset (deleteVertex G c) x).map (Function.Embedding.subtype _)

@[simp] theorem mem_cutComponent {c : V} {x : {v : V // v ≠ c}} {z : V} :
    z ∈ cutComponent G c x ↔
      ∃ hz : z ≠ c, (deleteVertex G c).Reachable x ⟨z, hz⟩ := by
  simp [cutComponent]

theorem cutVertex_not_mem_cutComponent (c : V) (x : {v : V // v ≠ c}) :
    c ∉ cutComponent G c x := by
  simp

/-- No edge joins a component of `G-c` to another component of `G-c`. -/
theorem interedges_cutComponent_compl_erase_eq_empty (c : V)
    (x : {v : V // v ≠ c}) :
    G.interedges (cutComponent G c x)
      ((cutComponent G c x)ᶜ.erase c) = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro e he
  have he' :
      (e.1 ∈ cutComponent G c x ∧
        e.2 ∈ (cutComponent G c x)ᶜ.erase c) ∧ G.Adj e.1 e.2 := by
    simpa [SimpleGraph.interedges_def] using he
  obtain ⟨hu, hxu⟩ := mem_cutComponent.mp he'.1.1
  have hv : e.2 ≠ c := (Finset.mem_erase.mp he'.1.2).1
  have huv : (deleteVertex G c).Adj ⟨e.1, hu⟩ ⟨e.2, hv⟩ :=
    SimpleGraph.induce_adj.mpr he'.2
  have hxv : (deleteVertex G c).Reachable x ⟨e.2, hv⟩ :=
    hxu.trans huv.reachable
  exact (Finset.mem_compl.mp (Finset.mem_erase.mp he'.1.2).2)
    (mem_cutComponent.mpr ⟨hv, hxv⟩)

/-- In a graph of minimum degree at least `k`, every component remaining
after deletion of one vertex has at least `k` vertices. -/
theorem le_card_cutComponent (hDegree : ∀ v : V, k ≤ G.degree v)
    (c : V) (x : {v : V // v ≠ c}) :
    k ≤ (cutComponent G c x).card := by
  have hxmem : x.1 ∈ cutComponent G c x :=
    mem_cutComponent.mpr ⟨x.2, SimpleGraph.Reachable.rfl⟩
  have hsub : G.neighborFinset x.1 ⊆
      (cutComponent G c x).erase x.1 ∪ {c} := by
    intro z hz
    by_cases hzc : z = c
    · simp [hzc]
    · apply Finset.mem_union_left
      apply Finset.mem_erase.mpr
      have hxzG := (G.mem_neighborFinset x.1 z).mp hz
      refine ⟨hxzG.ne.symm, mem_cutComponent.mpr ⟨hzc, ?_⟩⟩
      have hxz : (deleteVertex G c).Adj x ⟨z, hzc⟩ :=
        SimpleGraph.induce_adj.mpr hxzG
      exact hxz.reachable
  have hcard := Finset.card_le_card hsub
  have hcnot : c ∉ cutComponent G c x := cutVertex_not_mem_cutComponent c x
  have hcnot' : c ∉ (cutComponent G c x).erase x.1 :=
    fun hc => hcnot (Finset.mem_erase.mp hc).2
  have hinter : (cutComponent G c x).erase x.1 ∩ {c} = ∅ := by
    simp [hcnot']
  have hcardUnion :
      ((cutComponent G c x).erase x.1 ∪ {c}).card =
        (cutComponent G c x).card := by
    rw [Finset.card_union, Finset.card_singleton, hinter, Finset.card_empty]
    exact Finset.card_erase_add_one hxmem
  rw [G.card_neighborFinset_eq_degree, hcardUnion] at hcard
  exact (hDegree x.1).trans hcard

/-- A genuine cut vertex gives the sparse-pair conclusion with zero crossing
edges. -/
theorem hasSparsePairAt_of_cutVertexWitness {k b : ℕ}
    (hDegree : ∀ v : V, k ≤ G.degree v) {c : V}
    (hc : IsCutVertexWitness G c) :
    DiracStability.HasSparsePairAt G k b := by
  obtain ⟨x, y, hxy⟩ := hc
  let A := cutComponent G c x
  let B := Aᶜ.erase c
  have hyB : y.1 ∈ B := by
    apply Finset.mem_erase.mpr
    refine ⟨y.2, ?_⟩
    apply Finset.mem_compl.mpr
    intro hyA
    obtain ⟨hyc, hreach⟩ := mem_cutComponent.mp hyA
    exact hxy (by simpa using hreach)
  have hAcard : k ≤ A.card := le_card_cutComponent (G := G) hDegree c x
  have hBcard : k ≤ B.card := by
    have hsub : G.neighborFinset y.1 ⊆ B.erase y.1 ∪ {c} := by
      intro z hz
      by_cases hzc : z = c
      · simp [hzc]
      · apply Finset.mem_union_left
        apply Finset.mem_erase.mpr
        have hyzG := (G.mem_neighborFinset y.1 z).mp hz
        refine ⟨hyzG.ne.symm, Finset.mem_erase.mpr ⟨hzc,
          Finset.mem_compl.mpr ?_⟩⟩
        intro hzA
        obtain ⟨hzc', hxz⟩ := mem_cutComponent.mp hzA
        have hzy : (deleteVertex G c).Adj ⟨z, hzc'⟩ y :=
          SimpleGraph.induce_adj.mpr hyzG.symm
        exact hxy (hxz.trans hzy.reachable)
    have hcard := Finset.card_le_card hsub
    have hcnot : c ∉ B := by simp [B]
    have hcnot' : c ∉ B.erase y.1 := fun hc => hcnot (Finset.mem_erase.mp hc).2
    have hinter : B.erase y.1 ∩ {c} = ∅ := by simp [hcnot']
    have hcardUnion : (B.erase y.1 ∪ {c}).card = B.card := by
      rw [Finset.card_union, Finset.card_singleton, hinter, Finset.card_empty]
      exact Finset.card_erase_add_one hyB
    rw [G.card_neighborFinset_eq_degree, hcardUnion] at hcard
    exact (hDegree y.1).trans hcard
  apply DiracStability.hasSparsePairAt_of_emptyCut G (A := A) (B := B)
  · exact Finset.disjoint_left.mpr fun _ ha hb =>
      (Finset.mem_compl.mp (Finset.mem_erase.mp hb).2) ha
  · exact hAcard
  · exact hBcard
  · simpa [A, B] using interedges_cutComponent_compl_erase_eq_empty
      (G := G) c x

/-- The cut-vertex branch, injected into the full stability alternative. -/
theorem stabilityAlternative_of_cutVertexWitness {k b : ℕ}
    (hDegree : ∀ v : V, k ≤ G.degree v) {c : V}
    (hc : IsCutVertexWitness G c) :
    DiracStability.StabilityAlternative G k b := by
  exact Or.inr (Or.inr (hasSparsePairAt_of_cutVertexWitness hDegree hc))

/-- The finite witness form of separability used in the Nash-Williams--Bondy
lemma: the graph is disconnected, or deletion of one vertex leaves two
surviving vertices in different components. -/
def HasSeparationWitness (G : SimpleGraph V) : Prop :=
  ¬ G.Preconnected ∨ ∃ c : V, IsCutVertexWitness G c

/-- The local separator formulation in the underlying
Nash--Williams--Bondy file is definitionally the same one. -/
theorem hasSeparationWitness_iff_nashWilliamsBondy :
    HasSeparationWitness G ↔
      NashWilliamsBondy.HasSeparationWitness G := by
  rfl

/-- Likewise, the independent-set conclusion of Nash--Williams--Bondy is
exactly the rounded independent-set predicate used by KSS stability. -/
theorem hasIndependentSetAt_iff_nashWilliamsBondy {k : ℕ} :
    DiracStability.HasIndependentSetAt G k ↔
      NashWilliamsBondy.HasIndependentSetAt G k := by
  rfl

/-- The entire separable branch of the Nash-Williams--Bondy alternative gives
the sparse-pair conclusion, and hence the KSS stability alternative. -/
theorem stabilityAlternative_of_separationWitness {k b : ℕ}
    (hDegree : ∀ v : V, k ≤ G.degree v)
    (hsep : HasSeparationWitness G) :
    DiracStability.StabilityAlternative G k b := by
  rcases hsep with hdisc | ⟨c, hc⟩
  · exact stabilityAlternative_of_not_preconnected hDegree hdisc
  · exact stabilityAlternative_of_cutVertexWitness hDegree hc

/-- Shrinking an independent set preserves independence. -/
theorem hasIndependentSetAt_mono {j k : ℕ} (hjk : j ≤ k)
    (h : DiracStability.HasIndependentSetAt G k) :
    DiracStability.HasIndependentSetAt G j := by
  obtain ⟨A, hAcard, hAind⟩ := h
  obtain ⟨B, hBA, hBcard⟩ := Finset.exists_subset_card_eq
    (show j ≤ A.card by omega)
  refine ⟨B, hBcard, ?_⟩
  intro u hu v hv huv
  exact hAind (hBA hu) (hBA hv) huv

/-- The final elementary assembly around the Nash-Williams--Bondy lemma.
The third input is deliberately stated with `k+1`: the shifted-neighbourhood
argument produces one more independent vertex than the minimum-degree
threshold, while KSS only needs an exact `k`-set. -/
theorem stabilityAlternative_of_nashWilliamsBondy_conclusions {k b : ℕ}
    (hDegree : ∀ v : V, k ≤ G.degree v)
    (h : G.IsHamiltonian ∨ HasSeparationWitness G ∨
      DiracStability.HasIndependentSetAt G (k + 1)) :
    DiracStability.StabilityAlternative G k b := by
  rcases h with hHam | hsep | hInd
  · exact Or.inl hHam
  · exact stabilityAlternative_of_separationWitness hDegree hsep
  · exact Or.inr (Or.inl (hasIndependentSetAt_mono (Nat.le_succ k) hInd))

/-! ## Rounding the near-Dirac threshold

The Nash--Williams--Bondy lemma is naturally stated for an integer minimum
degree `k` satisfying `|V| + 2 < 3k`.  The next two lemmas verify that the
rounded KSS threshold has exactly these properties once the fixed loss is at
most `1/12` and the graph has at least 21 vertices.  The constant is not
optimized; its role is to make the phrase "sufficiently small fixed positive
loss" completely explicit. -/

/-- A real minimum-degree hypothesis implies the corresponding lower bound
at the rounded natural-number threshold. -/
theorem exceptionalSize_le_degree {ε : ℝ} {N d : ℕ}
    (hε : ε ≤ 1 / 12)
    (hDegree : (1 / 2 - ε) * (N : ℝ) ≤ (d : ℝ)) :
    DiracStability.exceptionalSize ε N ≤ d := by
  have hnonneg : 0 ≤ (1 / 2 - ε) * (N : ℝ) := by
    have hcoef : 0 ≤ (1 / 2 : ℝ) - ε := by
      nlinarith
    exact mul_nonneg hcoef (Nat.cast_nonneg N)
  have hfloor :
      (DiracStability.exceptionalSize ε N : ℝ) ≤
        (1 / 2 - ε) * (N : ℝ) := by
    exact Nat.floor_le hnonneg
  exact_mod_cast hfloor.trans hDegree

/-- For loss at most `1/12`, the rounded near-half threshold lies strictly
above the one-third threshold in Nash--Williams--Bondy. -/
theorem card_add_two_lt_three_mul_exceptionalSize {ε : ℝ} {N : ℕ}
    (hε : ε ≤ 1 / 12) (hN : 21 ≤ N) :
    N + 2 < 3 * DiracStability.exceptionalSize ε N := by
  let x : ℝ := (1 / 2 - ε) * (N : ℝ)
  let k : ℕ := DiracStability.exceptionalSize ε N
  have hround : x < (k : ℝ) + 1 := by
    exact Nat.lt_floor_add_one x
  have hNreal : (21 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hreal : (N : ℝ) + 2 < 3 * (k : ℝ) := by
    dsimp only [x] at hround
    nlinarith
  exact_mod_cast hreal

/-! ## The unconditional fixed-loss stability theorem -/

/-- Explicit finite KSS stability at every fixed loss `ε ≤ 1/12`.

The order bound `21` is only the rounding margin needed to pass from the
real threshold to the strict integer inequality in Nash--Williams--Bondy.
The three alternatives, including the exact floor and the `|V|` crossing
edge budget, are precisely those in `DiracStability.StabilityStatement`. -/
theorem stabilityAlternative_exceptionalSize {ε : ℝ}
    (hε : ε ≤ 1 / 12) (hCard : 21 ≤ Fintype.card V)
    (hDegree : ∀ v : V,
      (1 / 2 - ε) * (Fintype.card V : ℝ) ≤ G.degree v) :
    DiracStability.StabilityAlternative G
      (DiracStability.exceptionalSize ε (Fintype.card V))
      (Fintype.card V) := by
  let k := DiracStability.exceptionalSize ε (Fintype.card V)
  have hDegreeNat : ∀ v : V, k ≤ G.degree v := by
    intro v
    exact exceptionalSize_le_degree hε (hDegree v)
  have hThird : Fintype.card V + 2 < 3 * k := by
    exact card_add_two_lt_three_mul_exceptionalSize hε hCard
  by_cases hSep : HasSeparationWitness G
  · exact stabilityAlternative_of_separationWitness hDegreeNat hSep
  have hSepNash : ¬ NashWilliamsBondy.HasSeparationWitness G := by
    intro h
    exact hSep (hasSeparationWitness_iff_nashWilliamsBondy.mpr h)
  have hTwo : Erdos58.TwoConnected G :=
    NashWilliamsBondy.twoConnected_of_not_separated
      (by omega : 3 ≤ Fintype.card V) hSepNash
  obtain ⟨z, c, hc, hmax⟩ :=
    NashWilliamsBondy.exists_isLongestCycle hTwo
  by_cases hSpan : c.support.toFinset = (Finset.univ : Finset V)
  · exact Or.inl
      (NashWilliamsBondy.isHamiltonian_of_cycle_support_eq_univ hc hSpan)
  have hOutside :
      G.IsIndepSet ((c.support.toFinset : Set V)ᶜ) :=
    NashWilliamsBondy.longest_cycle_complement_isIndepSet
      hTwo hThird hDegreeNat hc hmax
  obtain ⟨A, hAcard, hAind⟩ :=
    NashWilliamsBondy.independent_set_of_longest_cycle_complement_independent
      c hc (fun z' c' hc' ↦ hmax c' hc') hSpan hOutside hDegreeNat
  exact Or.inr (Or.inl (hasIndependentSetAt_mono (Nat.le_succ k)
    ⟨A, hAcard, hAind⟩))

/-- Uniform formulation of the fixed-positive-loss theorem.  Thus every
`0 < ε ≤ 1/12` satisfies the complete KSS stability statement with the
single explicit order threshold `21`. -/
theorem stabilityStatement_of_small_positive_loss {ε : ℝ}
    (hεpos : 0 < ε) (hε : ε ≤ 1 / 12) :
    DiracStability.StabilityStatement ε 21 := by
  refine ⟨hεpos, ?_⟩
  intro W _ _ H _ hCard hDegree
  let : DecidableRel H.Adj := Classical.decRel H.Adj
  have hDegree' : ∀ v : W,
      (1 / 2 - ε) * (Fintype.card W : ℝ) ≤ H.degree v := by
    intro v
    convert hDegree v using 1
    norm_cast
    unfold SimpleGraph.degree
    congr 1
    ext w
    simp only [SimpleGraph.mem_neighborFinset]
  exact stabilityAlternative_exceptionalSize (G := H) hε hCard hDegree'

end KSSStability
end Erdos622
