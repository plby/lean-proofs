/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
import ErdosProblems.Erdos73.HavenSeparation
import Mathlib.Combinatorics.SimpleGraph.Acyclic

/-!
# Rooted trees at a forward-saturated bramble separator

Induction by deleting a leaf constructs any finite tree model on the left
of a saturated separator of its exact order. The adjacent right region is
connected and contains the bramble haven. This proves the rooted-tree part
of the Leaf--Seymour construction; proper linkage is a separate step.
-/

namespace Erdos73
universe u
noncomputable section
attribute [local instance] Classical.propDecidable Classical.decEq
variable {V : Type*} [Fintype V] {G : SimpleGraph V}

namespace LeftRootedModel
variable {I : Type*} {H : SimpleGraph I} {A B : Finset V}

noncomputable def empty [IsEmpty I] (hboundary : A ∩ B = ∅) :
    LeftRootedModel H G A B where
  branch := isEmptyElim
  root := isEmptyElim
  connected := isEmptyElim
  disjoint := fun i ↦ isEmptyElim i
  subset_left := isEmptyElim
  boundary := isEmptyElim
  covers := by intro v hv; rw [hboundary] at hv; exact (Finset.notMem_empty v hv).elim
  edge := fun {i} ↦ isEmptyElim i

/-- Add a new singleton branch attached to the roots of its neighbors. -/
noncomputable def addVertex {v : I}
    (M : LeftRootedModel (H.induce {v}ᶜ) G A B) {u : V} (hu : u ∈ B \ A)
    (hlink : ∀ t : {i : I // i ∈ ({v} : Set I)ᶜ}, H.Adj v t → G.Adj u (M.root t)) :
    LeftRootedModel H G (insert u A) B := by
  let b (i : I) : Finset V := if hi : i = v then {u} else M.branch ⟨i, hi⟩
  let r (i : I) : V := if hi : i = v then u else M.root ⟨i, hi⟩
  have hb₀ (i : I) (hi : i = v) : b i = {u} := dif_pos hi
  have hb₁ (i : I) (hi : i ≠ v) : b i = M.branch ⟨i, hi⟩ := dif_neg hi
  have hr₀ (i : I) (hi : i = v) : r i = u := dif_pos hi
  have hr₁ (i : I) (hi : i ≠ v) : r i = M.root ⟨i, hi⟩ := dif_neg hi
  have huB := (Finset.mem_sdiff.mp hu).1
  have huA := (Finset.mem_sdiff.mp hu).2
  refine {
    branch := b
    root := r
    connected := ?_
    disjoint := ?_
    subset_left := ?_
    boundary := ?_
    covers := ?_
    edge := ?_
  }
  · intro i
    by_cases hi : i = v
    · rw [hb₀ i hi, Finset.coe_singleton]
      exact SimpleGraph.Connected.of_subsingleton
    · rw [hb₁ i hi]
      exact M.connected ⟨i, hi⟩
  · intro i j hij
    by_cases hi : i = v
    · by_cases hj : j = v
      · exact (hij (hi.trans hj.symm)).elim
      · rw [hb₀ i hi, hb₁ j hj, Finset.disjoint_singleton_left]
        exact fun hum ↦ huA (M.subset_left ⟨j, hj⟩ hum)
    · by_cases hj : j = v
      · rw [hb₁ i hi, hb₀ j hj, Finset.disjoint_singleton_right]
        exact fun hum ↦ huA (M.subset_left ⟨i, hi⟩ hum)
      · rw [hb₁ i hi, hb₁ j hj]
        exact M.disjoint (fun heq ↦ hij (congrArg Subtype.val heq))
  · intro i
    by_cases hi : i = v
    · rw [hb₀ i hi]
      exact Finset.singleton_subset_iff.mpr (Finset.mem_insert_self u A)
    · rw [hb₁ i hi]
      exact (M.subset_left ⟨i, hi⟩).trans (Finset.subset_insert u A)
  · intro i
    by_cases hi : i = v
    · rw [hb₀ i hi, hr₀ i hi]
      simp [huB]
    · rw [hb₁ i hi, hr₁ i hi]
      exact M.boundary ⟨i, hi⟩
  · intro x hx
    obtain ⟨hxA, hxB⟩ := Finset.mem_inter.mp hx
    rcases Finset.mem_insert.mp hxA with hxu | hxA
    · exact ⟨v, by simp [r, hxu]⟩
    · obtain ⟨i, hi⟩ := M.covers x (Finset.mem_inter.mpr ⟨hxA, hxB⟩)
      exact ⟨i, by simpa only [r, dif_neg (show (i : I) ≠ v from i.2)] using hi⟩
  · intro i j hij
    by_cases hi : i = v
    · subst i
      have hj : j ≠ v := hij.ne.symm
      refine ⟨u, by simp [b], M.root ⟨j, hj⟩, ?_, hlink ⟨j, hj⟩ hij⟩
      rw [hb₁ j hj]
      exact M.root_mem ⟨j, hj⟩
    · by_cases hj : j = v
      · subst j
        refine ⟨M.root ⟨i, hi⟩, ?_, u, by simp [b], (hlink ⟨i, hi⟩ hij.symm).symm⟩
        rw [hb₁ i hi]
        exact M.root_mem ⟨i, hi⟩
      · rw [hb₁ i hi, hb₁ j hj]
        exact M.edge (show (H.induce {v}ᶜ).Adj ⟨i, hi⟩ ⟨j, hj⟩ from hij)

end LeftRootedModel

namespace BrambleHaven
variable {β : Finset (Finset V)} {q : ℕ}

theorem exists_saturated_extension (h : BrambleHaven G β q) {A B : Finset V}
    {I : Type*} {H : SimpleGraph I} {v : I}
    (M : LeftRootedModel (H.induce {v}ᶜ) G A B)
    (hAB : IsVertexSeparation G A B) (hpoint : h.PointsTo A B)
    (hsat : h.ForwardSaturated A B) {u : V} (hu : u ∈ B \ A)
    (hlink : ∀ t : {i : I // i ∈ ({v} : Set I)ᶜ}, H.Adj v t → G.Adj u (M.root t))
    (hsmall : (A ∩ B).card + 1 < q) :
    ∃ C D : Finset V, IsVertexSeparation G C D ∧
      (C ∩ D).card = (A ∩ B).card + 1 ∧ h.PointsTo C D ∧ h.ForwardSaturated C D ∧
      Nonempty (LeftRootedModel H G C D) := by
  have hcard : (insert u A ∩ B).card = (A ∩ B).card + 1 := by
    rw [Finset.insert_inter_of_mem (Finset.mem_sdiff.mp hu).1,
      Finset.card_insert_of_notMem (fun hv ↦ (Finset.mem_sdiff.mp hu).2
        (Finset.mem_inter.mp hv).1)]
  obtain ⟨C, D, hCD, _, _, hCDcard, hCDpoint, hCDsat, hM⟩ :=
    h.exists_saturated_rootedModel (M.addVertex hu hlink)
      (hAB.insert_left (Finset.mem_sdiff.mp hu).1)
      (h.pointsTo_insert_left hpoint (by rw [hcard]; exact hsmall))
      (h.saturated_insert_left_minimal hsat hu)
  exact ⟨C, D, hCD, hCDcard.trans hcard, hCDpoint, hCDsat, hM⟩

theorem exists_zero_saturated (h : BrambleHaven G β q) (hq : 0 < q) :
    ∃ A B : Finset V, IsVertexSeparation G A B ∧ (A ∩ B).card = 0 ∧
      h.PointsTo A B ∧ h.ForwardSaturated A B := by
  have hsep : IsVertexSeparation G ∅ Finset.univ := by
    constructor
    · simp
    · intro a b ha; exact (Finset.notMem_empty a ha).elim
  have hpoint : h.PointsTo ∅ Finset.univ := ⟨by simpa using hq, Finset.subset_univ _⟩
  have hmin : h.ForwardMinimal ∅ Finset.univ := by
    intro C D _ _ _ _
    simp
  obtain ⟨A, B, hAB, _, _, hcard, hpoint, hsat⟩ := h.exists_forwardSaturated hsep hpoint hmin
  exact ⟨A, B, hAB, by simpa using hcard, hpoint, hsat⟩

theorem exists_saturated_treeModel (h : BrambleHaven G β q)
    {I : Type u} [Fintype I] (T : SimpleGraph I) (hT : T.IsTree)
    (hsize : Fintype.card I < q) :
    ∃ A B : Finset V, IsVertexSeparation G A B ∧ (A ∩ B).card = Fintype.card I ∧
      h.PointsTo A B ∧ h.ForwardSaturated A B ∧ Nonempty (LeftRootedModel T G A B) := by
  have aux : ∀ n : ℕ, ∀ (J : Type u) [Fintype J] (T : SimpleGraph J),
      T.IsTree → Fintype.card J = n → n < q →
      ∃ A B : Finset V, IsVertexSeparation G A B ∧ (A ∩ B).card = n ∧
        h.PointsTo A B ∧ h.ForwardSaturated A B ∧ Nonempty (LeftRootedModel T G A B) := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro J _ T hT hcard hn
      have : Nonempty J := hT.connected.nonempty
      rcases subsingleton_or_nontrivial J with hJ | hJ
      · have : Subsingleton J := hJ
        have hn1 : n = 1 := by
          have hle := Fintype.card_le_one_iff_subsingleton.mpr hJ
          have hpos := Fintype.card_pos (α := J)
          omega
        let v : J := Classical.choice inferInstance
        have : IsEmpty {j : J // j ∈ ({v} : Set J)ᶜ} :=
          ⟨fun j ↦ j.2 (Subsingleton.elim j.1 v)⟩
        obtain ⟨A, B, hAB, hzero, hpoint, hsat⟩ := h.exists_zero_saturated (by omega)
        have hconn := (h.saturated_right_properties hAB hpoint hsat).1
        obtain ⟨u⟩ := hconn.nonempty
        let M : LeftRootedModel (T.induce {v}ᶜ) G A B :=
          LeftRootedModel.empty (Finset.card_eq_zero.mp hzero)
        obtain ⟨C, D, hCD, hCDcard, hCDpoint, hCDsat, hmodel⟩ :=
          h.exists_saturated_extension M hAB hpoint hsat u.2
            (fun t ↦ isEmptyElim t) (by omega)
        exact ⟨C, D, hCD, by omega, hCDpoint, hCDsat, hmodel⟩
      · have : Nontrivial J := hJ
        obtain ⟨v, hv⟩ := hT.exists_vert_degree_one_of_nontrivial
        let J' := {j : J // j ∈ ({v} : Set J)ᶜ}
        have hcard' : Fintype.card J' = n - 1 := by
          change Fintype.card {j : J // ¬j = v} = n - 1
          rw [Fintype.card_subtype_compl, hcard]
          have hsingle : Fintype.card {j : J // j = v} = 1 := Fintype.card_unique
          rw [hsingle]
        have hlt : Fintype.card J' < n := by
          rw [← hcard]
          exact Fintype.card_subtype_lt (x := v) (by simp)
        have hT' : (T.induce {v}ᶜ).IsTree :=
          ⟨hT.connected.induce_compl_singleton_of_degree_eq_one hv,
            hT.isAcyclic.induce {v}ᶜ⟩
        obtain ⟨A, B, hAB, hABcard, hpoint, hsat, ⟨M⟩⟩ :=
          ih (Fintype.card J') hlt J' (T.induce {v}ᶜ) hT' rfl (hlt.trans hn)
        obtain ⟨t, hvt, huniq⟩ := SimpleGraph.degree_eq_one_iff_existsUnique_adj.mp hv
        let t' : J' := ⟨t, hvt.ne.symm⟩
        obtain ⟨u, hu, hrootu⟩ := (h.saturated_right_properties hAB hpoint hsat).2
          (M.root t') (M.root_mem_separator t')
        have hlink (j : J') (hvj : T.Adj v j) : G.Adj u (M.root j) := by
          have hjt : j = t' := Subtype.ext (huniq j hvj)
          rw [hjt]
          exact hrootu.symm
        obtain ⟨C, D, hCD, hCDcard, hCDpoint, hCDsat, hmodel⟩ :=
          h.exists_saturated_extension M hAB hpoint hsat hu hlink (by omega)
        exact ⟨C, D, hCD, by omega, hCDpoint, hCDsat, hmodel⟩
  exact aux (Fintype.card I) I T hT rfl hsize

end BrambleHaven
end
end Erdos73

#print axioms Erdos73.BrambleHaven.exists_saturated_treeModel
