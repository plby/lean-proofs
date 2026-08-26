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
import ErdosProblems.Erdos76.PentagonBadConfigurations

/-!
# Transversal form of the pentagon bad-configuration lemmas

The finite statements in `PentagonBadConfigurations` concern five Boolean
colours.  This module connects them to an actual graph: choose one old vertex
from each blob and compare the five edges from a new vertex.  The first
theorem produces a monochromatic triangle through the new vertex.  In the
bad-pattern case the two triangles use disjoint pairs of old vertices and
are therefore edge-disjoint.
-/

open Finset

namespace Erdos76

noncomputable section

attribute [local instance] Classical.propDecidable

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- The five red/blue decisions from `u` to a chosen transversal. -/
def pentagonAdjacencyPattern (G : SimpleGraph α) (u : α)
    (v : Fin 5 → α) (i : Fin 5) : Bool :=
  decide (G.Adj u (v i))

/-- A pair of transversal vertices forms a monochromatic triangle with
`u`. -/
def IsPentagonMonochromaticPairThrough (G : SimpleGraph α) (u : α)
    (v : Fin 5 → α) (i j : Fin 5) : Prop :=
  (G.Adj u (v i) ∧ G.Adj u (v j) ∧ G.Adj (v i) (v j)) ∨
    (Gᶜ.Adj u (v i) ∧ Gᶜ.Adj u (v j) ∧ Gᶜ.Adj (v i) (v j))

/-- Interpret the Boolean monochromatic-pair test in an actual pentagon
transversal. -/
theorem pentagonMonoPair_adjacency_iff
    {G : SimpleGraph α} {u : α} {v : Fin 5 → α}
    (hv : Function.Injective v) (hu : ∀ i, u ≠ v i)
    (hcross : ∀ i j, i ≠ j →
      (G.Adj (v i) (v j) ↔
        (SimpleGraph.cycleGraph 5).Adj i j))
    {i j : Fin 5} (hij : i ≠ j) :
    pentagonMonoPair (pentagonAdjacencyPattern G u v) i j = true ↔
      IsPentagonMonochromaticPairThrough G u v i j := by
  simp [pentagonMonoPair, pentagonAdjacencyPattern,
    pentagonTemplateRed, IsPentagonMonochromaticPairThrough,
    hcross i j hij, SimpleGraph.compl_adj, hu i, hu j, hv.ne hij,
    and_assoc]

/-- Observation 7.9, first part, on an actual graph transversal. -/
theorem exists_monochromaticPair_through_pentagonTransversal
    {G : SimpleGraph α} {u : α} {v : Fin 5 → α}
    (hv : Function.Injective v) (hu : ∀ i, u ≠ v i)
    (hcross : ∀ i j, i ≠ j →
      (G.Adj (v i) (v j) ↔
        (SimpleGraph.cycleGraph 5).Adj i j)) :
    ∃ i j : Fin 5, i ≠ j ∧
      IsPentagonMonochromaticPairThrough G u v i j := by
  obtain ⟨i, j, hij, hmono⟩ :=
    pentagon_exists_mono_pair (pentagonAdjacencyPattern G u v)
  exact ⟨i, j, hij,
    (pentagonMonoPair_adjacency_iff hv hu hcross hij).mp hmono⟩

/-- The three vertices determined by a transversal pair. -/
def pentagonTransversalTriangle (u : α) (v : Fin 5 → α)
    (i j : Fin 5) : Finset α :=
  {u, v i, v j}

private lemma isNClique_pentagonTransversalTriangle_of_adj
    {G : SimpleGraph α} {u : α} {v : Fin 5 → α} {i j : Fin 5}
    (hui : G.Adj u (v i)) (huj : G.Adj u (v j))
    (hij : G.Adj (v i) (v j)) :
    G.IsNClique 3 (pentagonTransversalTriangle u v i j) := by
  constructor
  · rw [SimpleGraph.isClique_iff]
    intro a ha b hb hab
    simp only [pentagonTransversalTriangle, Finset.coe_insert,
      Finset.coe_singleton, Set.mem_insert_iff,
      Set.mem_singleton_iff] at ha hb
    rcases ha with rfl | rfl | rfl <;>
      rcases hb with rfl | rfl | rfl
    · exact (hab rfl).elim
    · exact hui
    · exact huj
    · exact hui.symm
    · exact (hab rfl).elim
    · exact hij
    · exact huj.symm
    · exact hij.symm
    · exact (hab rfl).elim
  · simp [pentagonTransversalTriangle, hui.ne, huj.ne, hij.ne]

/-- The proposition-level pair test is exactly a red or blue triangle. -/
theorem isNClique_pentagonTransversalTriangle
    {G : SimpleGraph α} {u : α} {v : Fin 5 → α} {i j : Fin 5}
    (hmono : IsPentagonMonochromaticPairThrough G u v i j) :
    G.IsNClique 3 (pentagonTransversalTriangle u v i j) ∨
      Gᶜ.IsNClique 3 (pentagonTransversalTriangle u v i j) := by
  rcases hmono with hred | hblue
  · exact Or.inl
      (isNClique_pentagonTransversalTriangle_of_adj
        hred.1 hred.2.1 hred.2.2)
  · exact Or.inr
      (isNClique_pentagonTransversalTriangle_of_adj
        hblue.1 hblue.2.1 hblue.2.2)

/-- Distinct transversal labels and injectivity make the two old pairs
vertex-disjoint.  Consequently their triangles through the common new
vertex share at most that vertex. -/
theorem inter_card_pentagonTransversalTriangle_le_one
    {u : α} {v : Fin 5 → α} (hv : Function.Injective v)
    {i j k l : Fin 5}
    (hik : i ≠ k) (hil : i ≠ l) (hjk : j ≠ k) (hjl : j ≠ l) :
    ((pentagonTransversalTriangle u v i j ∩
      pentagonTransversalTriangle u v k l).card) ≤ 1 := by
  apply (card_le_card (t := {u}) ?_).trans
  · simp
  · intro z hz
    simp only [pentagonTransversalTriangle, mem_inter, mem_insert,
      mem_singleton] at hz ⊢
    rcases hz with ⟨hz₁, hz₂⟩
    rcases hz₁ with rfl | hzi | hzj
    · rfl
    · rcases hz₂ with rfl | hzk | hzl
      · rfl
      · exact (hik (hv (hzi.symm.trans hzk))).elim
      · exact (hil (hv (hzi.symm.trans hzl))).elim
    · rcases hz₂ with rfl | hzk | hzl
      · rfl
      · exact (hjk (hv (hzj.symm.trans hzk))).elim
      · exact (hjl (hv (hzj.symm.trans hzl))).elim

/-- Observation 7.9, second part, on an actual graph transversal.  A bad
five-edge pattern supplies two monochromatic triangles through `u` whose old
vertex pairs are disjoint, hence whose edge sets are disjoint. -/
theorem badPattern_exists_two_edgeDisjoint_monochromaticTriangles
    {G : SimpleGraph α} {u : α} {v : Fin 5 → α}
    (hv : Function.Injective v) (hu : ∀ i, u ≠ v i)
    (hcross : ∀ i j, i ≠ j →
      (G.Adj (v i) (v j) ↔
        (SimpleGraph.cycleGraph 5).Adj i j))
    (hbad : pentagonBadPattern
      (pentagonAdjacencyPattern G u v) = true) :
    ∃ i j k l : Fin 5,
      i ≠ j ∧ k ≠ l ∧
      (G.IsNClique 3 (pentagonTransversalTriangle u v i j) ∨
        Gᶜ.IsNClique 3 (pentagonTransversalTriangle u v i j)) ∧
      (G.IsNClique 3 (pentagonTransversalTriangle u v k l) ∨
        Gᶜ.IsNClique 3 (pentagonTransversalTriangle u v k l)) ∧
      ((pentagonTransversalTriangle u v i j ∩
        pentagonTransversalTriangle u v k l).card ≤ 1) := by
  obtain ⟨i, j, k, l, hij, hkl, hik, hil, hjk, hjl, hmono₁, hmono₂⟩ :=
    pentagon_bad_exists_two_disjoint_mono_pairs
      (pentagonAdjacencyPattern G u v) hbad
  have htri₁ := isNClique_pentagonTransversalTriangle
    ((pentagonMonoPair_adjacency_iff hv hu hcross hij).mp hmono₁)
  have htri₂ := isNClique_pentagonTransversalTriangle
    ((pentagonMonoPair_adjacency_iff hv hu hcross hkl).mp hmono₂)
  refine ⟨i, j, k, l, hij, hkl, ?_⟩
  exact ⟨htri₁, htri₂,
    inter_card_pentagonTransversalTriangle_le_one hv hik hil hjk hjl⟩

/-- Packing form of the bad-pattern conclusion: the two triangles form an
actual two-element monochromatic packing.  Both contain the distinguished
new vertex, while their intersection contains no second vertex. -/
theorem badPattern_exists_two_monochromaticPacking
    {G : SimpleGraph α} {u : α} {v : Fin 5 → α}
    (hv : Function.Injective v) (hu : ∀ i, u ≠ v i)
    (hcross : ∀ i j, i ≠ j →
      (G.Adj (v i) (v j) ↔
        (SimpleGraph.cycleGraph 5).Adj i j))
    (hbad : pentagonBadPattern
      (pentagonAdjacencyPattern G u v) = true) :
    ∃ P : Finset (Finset α),
      IsMonochromaticPacking G P ∧ P.card = 2 ∧
        ∀ t ∈ P, u ∈ t := by
  obtain ⟨i, j, k, l, _hij, _hkl, htri₁, htri₂, hinter⟩ :=
    badPattern_exists_two_edgeDisjoint_monochromaticTriangles
      hv hu hcross hbad
  let t₁ := pentagonTransversalTriangle u v i j
  let t₂ := pentagonTransversalTriangle u v k l
  have ht₁card : t₁.card = 3 := by
    rcases htri₁ with hred | hblue
    · exact hred.card_eq
    · exact hblue.card_eq
  have htne : t₁ ≠ t₂ := by
    intro h
    subst t₂
    rw [← h] at hinter
    rw [inter_self, ht₁card] at hinter
    omega
  have hsub : {t₁, t₂} ⊆ monochromaticTriangles G := by
    intro t ht
    simp only [mem_insert, mem_singleton] at ht
    rcases ht with rfl | rfl
    · exact mem_monochromaticTriangles.mpr htri₁
    · exact mem_monochromaticTriangles.mpr htri₂
  have hedge : EdgeDisjoint ({t₁, t₂} : Finset (Finset α)) := by
    intro s hs t ht hst
    simp only [mem_insert, mem_singleton] at hs ht
    rcases hs with rfl | rfl <;> rcases ht with rfl | rfl
    · exact (hst rfl).elim
    · exact hinter
    · simpa [inter_comm] using hinter
    · exact (hst rfl).elim
  refine ⟨{t₁, t₂}, ⟨hsub, hedge⟩, ?_, ?_⟩
  · simp [htne]
  · intro t ht
    simp only [mem_insert, mem_singleton] at ht
    rcases ht with rfl | rfl <;>
      simp [t₁, t₂, pentagonTransversalTriangle]

/-- Proposition 7.10's consistency conclusion for whole blobs.  If every
choice of one vertex from each nonempty blob gives a bad-free five-edge
pattern, then one label `s` works simultaneously for every vertex outside
blob `s`.  The colour inside the chosen blob remains unrestricted. -/
theorem no_badPatterns_extend_one_blob
    {G : SimpleGraph α} {u : α} {B : Fin 5 → Finset α}
    (hne : ∀ i, (B i).Nonempty)
    (hnobad : ∀ v : Fin 5 → α, (∀ i, v i ∈ B i) →
      pentagonBadPattern (pentagonAdjacencyPattern G u v) = false) :
    ∃ s : Fin 5, ∀ j : Fin 5, j ≠ s → ∀ x ∈ B j,
      G.Adj u x ↔ (SimpleGraph.cycleGraph 5).Adj s j := by
  let v₀ : Fin 5 → α := fun i ↦ Classical.choose (hne i)
  have hv₀ (i : Fin 5) : v₀ i ∈ B i :=
    Classical.choose_spec (hne i)
  have hbad₀ : pentagonBadPattern
      (pentagonAdjacencyPattern G u v₀) = false :=
    hnobad v₀ hv₀
  obtain ⟨s, hs⟩ := pentagon_no_bad_extends_one_blob
    (pentagonAdjacencyPattern G u v₀) hbad₀
  refine ⟨s, ?_⟩
  intro j hjs x hx
  let v' : Fin 5 → α := fun q ↦ if q = j then x else v₀ q
  have hv' (q : Fin 5) : v' q ∈ B q := by
    by_cases hq : q = j
    · subst q
      simpa [v'] using hx
    · simpa [v', hq] using hv₀ q
  have hbad' : pentagonBadPattern
      (pentagonAdjacencyPattern G u v') = false :=
    hnobad v' hv'
  have hagree : ∀ q : Fin 5, q ≠ j →
      pentagonAdjacencyPattern G u v' q =
        pentagonAdjacencyPattern G u v₀ q := by
    intro q hq
    simp [pentagonAdjacencyPattern, v', hq]
  have hstable := pentagon_no_bad_stable_replacement
    (pentagonAdjacencyPattern G u v₀)
    (pentagonAdjacencyPattern G u v') j s
    hbad₀ hbad' hagree hs hjs
  simpa [pentagonAdjacencyPattern, pentagonTemplateRed, v'] using
    (decide_eq_decide.mp hstable)

/-- Indexed-type form of `no_badPatterns_extend_one_blob`.  This is the
convenient interface for actual blow-up fibres: the type `β i` can be the
subtype of old vertices carrying label `i`, so no image/preimage bookkeeping
is exposed to the extension proof. -/
theorem no_badPatterns_indexed_extend_one_blob
    {β : Fin 5 → Type*} [∀ i, Nonempty (β i)]
    {G : SimpleGraph α} {u : α}
    (vertex : ∀ i, β i → α)
    (hnobad : ∀ v : ∀ i, β i,
      pentagonBadPattern
        (pentagonAdjacencyPattern G u (fun i ↦ vertex i (v i))) = false) :
    ∃ s : Fin 5, ∀ j : Fin 5, j ≠ s → ∀ x : β j,
      G.Adj u (vertex j x) ↔
        (SimpleGraph.cycleGraph 5).Adj s j := by
  let v₀ : ∀ i, β i := fun i ↦ Classical.choice inferInstance
  have hbad₀ := hnobad v₀
  obtain ⟨s, hs⟩ := pentagon_no_bad_extends_one_blob
    (pentagonAdjacencyPattern G u (fun i ↦ vertex i (v₀ i))) hbad₀
  refine ⟨s, ?_⟩
  intro j hjs x
  let v' : ∀ i, β i := Function.update v₀ j x
  have hbad' := hnobad v'
  have hagree : ∀ q : Fin 5, q ≠ j →
      pentagonAdjacencyPattern G u (fun i ↦ vertex i (v' i)) q =
        pentagonAdjacencyPattern G u (fun i ↦ vertex i (v₀ i)) q := by
    intro q hq
    simp [pentagonAdjacencyPattern, v', Function.update_of_ne hq]
  have hstable := pentagon_no_bad_stable_replacement
    (pentagonAdjacencyPattern G u (fun i ↦ vertex i (v₀ i)))
    (pentagonAdjacencyPattern G u (fun i ↦ vertex i (v' i)))
    j s hbad₀ hbad' hagree hs hjs
  simpa [pentagonAdjacencyPattern, pentagonTemplateRed, v'] using
    (decide_eq_decide.mp hstable)

end

end Erdos76
