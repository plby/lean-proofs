/- Three attachments in a connected set have a common centre and disjoint arms. -/
import ErdosProblems.Erdos73.GraphPaths
import Mathlib.Tactic.FinCases
import Mathlib.Data.Fin.VecNotation

namespace Erdos73Infrastructure.SimpleGraph
noncomputable section
attribute [local instance] Classical.propDecidable Classical.decEq
variable {V : Type*} {G : _root_.SimpleGraph V}

/-- Arms may be trivial and their targets may coincide; distinct arms
can still meet only at their common source. -/
structure DisjointArms {I : Type*} (G : _root_.SimpleGraph V) (terminal : I → V) where
  center : V
  arm : I → GraphPath G
  source_eq : ∀ i, (arm i).source = center
  target_eq : ∀ i, (arm i).target = terminal i
  intersection : ∀ ⦃i j⦄, i ≠ j → ∀ v,
    v ∈ (arm i).vertexSet → v ∈ (arm j).vertexSet → v = center

abbrev ThreeArms (G : _root_.SimpleGraph V) (terminal : Fin 3 → V) :=
  DisjointArms G terminal

theorem exists_threeArms_in_connected_finset (S : Finset V)
    (hS : (G.induce (S : Set V)).Connected) (terminal : Fin 3 → V)
    (hterminal : ∀ i, terminal i ∈ S) :
    ∃ A : ThreeArms G terminal, A.center ∈ S ∧ ∀ i, (A.arm i).vertexSet ⊆ S := by
  let P := GraphPath.ofConnectedInduce S hS (terminal 0) (terminal 1)
    (hterminal 0) (hterminal 1)
  let Q := GraphPath.ofConnectedInduce S hS (terminal 2) (terminal 0)
    (hterminal 2) (hterminal 0)
  have hPS : P.vertexSet ⊆ S := GraphPath.ofConnectedInduce_vertexSet_subset _ _ _ _ _ _
  have hQS : Q.vertexSet ⊆ S := GraphPath.ofConnectedInduce_vertexSet_subset _ _ _ _ _ _
  have hhit : (Q.vertexSet ∩ P.vertexSet).Nonempty :=
    ⟨terminal 0, Finset.mem_inter.mpr ⟨Q.target_mem_vertexSet, P.source_mem_vertexSet⟩⟩
  let C := Q.cleanPrefixToSet P.vertexSet hhit
  have hCP : C.target ∈ P.vertexSet := Q.cleanPrefixToSet_target_mem P.vertexSet hhit
  let R₀ := (P.takeUntil hCP).reverse
  let R₁ := P.dropUntil hCP
  let R₂ := C.reverse
  have hR₀ : R₀.vertexSet ⊆ P.vertexSet := by
    rw [GraphPath.reverse_vertexSet]
    exact P.takeUntil_vertexSet_subset hCP
  have hR₁ : R₁.vertexSet ⊆ P.vertexSet := P.dropUntil_vertexSet_subset hCP
  have hR₂ : R₂.vertexSet ⊆ Q.vertexSet := by
    rw [GraphPath.reverse_vertexSet]
    exact Q.cleanPrefixToSet_vertexSet_subset P.vertexSet hhit
  have h01 (v : V) (h0 : v ∈ R₀.vertexSet) (h1 : v ∈ R₁.vertexSet) : v = C.target := by
    rw [GraphPath.reverse_vertexSet] at h0
    exact P.before_antisymm (P.before_of_mem_takeUntil hCP h0) ⟨hCP, h1⟩
  have h2 (v : V) (hvP : v ∈ P.vertexSet) (hv2 : v ∈ R₂.vertexSet) : v = C.target := by
    rw [GraphPath.reverse_vertexSet] at hv2
    have hv := Finset.mem_inter.mpr ⟨hvP, hv2⟩
    rw [Q.cleanPrefixToSet_inter_eq_singleton_target P.vertexSet hhit] at hv
    exact Finset.mem_singleton.mp hv
  let A : ThreeArms G terminal := {
    center := C.target
    arm := ![R₀, R₁, R₂]
    source_eq := by intro i; fin_cases i <;> rfl
    target_eq := by intro i; fin_cases i <;> rfl
    intersection := by
      intro i j hij v hvi hvj
      fin_cases i <;> fin_cases j
      · exact (hij rfl).elim
      · exact h01 v hvi hvj
      · exact h2 v (hR₀ hvi) hvj
      · exact h01 v hvj hvi
      · exact (hij rfl).elim
      · exact h2 v (hR₁ hvi) hvj
      · exact h2 v (hR₀ hvj) hvi
      · exact h2 v (hR₁ hvj) hvi
      · exact (hij rfl).elim }
  refine ⟨A, hPS hCP, fun i => ?_⟩
  fin_cases i
  · exact hR₀.trans hPS
  · exact hR₁.trans hPS
  · exact hR₂.trans hQS

/-- Any family of at most three attachments, including the empty family,
has a supported system of arms disjoint away from one common centre. -/
theorem exists_disjointArms_of_card_le_three {I : Type*} [Fintype I]
    (S : Finset V) (hS : (G.induce (S : Set V)).Connected)
    (terminal : I → V) (hterminal : ∀ i, terminal i ∈ S)
    (hcard : Fintype.card I ≤ 3) :
    ∃ A : DisjointArms G terminal, A.center ∈ S ∧ ∀ i, (A.arm i).vertexSet ⊆ S := by
  obtain ⟨v⟩ := hS.nonempty
  let e : I ↪ Fin 3 := Classical.choice (Function.Embedding.nonempty_of_card_le
    (show Fintype.card I ≤ Fintype.card (Fin 3) by simpa only [Fintype.card_fin] using hcard))
  let t : Fin 3 → V := Function.extend e terminal (fun _ => v.val)
  have ht (i : Fin 3) : t i ∈ S := by
    dsimp only [t, Function.extend]
    split
    · exact hterminal _
    · exact v.property
  obtain ⟨A, hA, hAS⟩ := exists_threeArms_in_connected_finset S hS t ht
  refine ⟨{
    center := A.center
    arm := fun i => A.arm (e i)
    source_eq := fun i => A.source_eq (e i)
    target_eq := fun i => (A.target_eq (e i)).trans (e.injective.extend_apply _ _ _)
    intersection := fun _ _ hij => A.intersection (e.injective.ne hij) }, hA,
    fun i => hAS (e i)⟩

end
end Erdos73Infrastructure.SimpleGraph
