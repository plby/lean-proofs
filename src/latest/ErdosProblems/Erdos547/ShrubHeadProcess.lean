import ErdosProblems.Erdos547.ShrubPrivateStep
import ErdosProblems.Erdos547.ShrubPostponedHeads

/-!
# Processing all selected shrubs assigned to one head cluster
-/

namespace Erdos547.ShrubHostSetup

open Finset SimpleGraph

variable {U V I : Type*} [Fintype U] [Fintype I]
  [DecidableEq U] [DecidableEq V] [DecidableEq I]
  {T : SimpleGraph U} [DecidableRel T.Adj] {r : U} {ℓ : ℕ}
  {col : T.Coloring (Fin 2)} {P : FineTreePartition T r ℓ col}
  {G : SimpleGraph V} [DecidableRel G.Adj]
variable (H : ShrubHostSetup P G I)

structure HeadOutcome (E : H.State) (F L : Finset ↥P.shrubs) where
  state : H.State
  postponed : Finset ↥P.shrubs
  postponed_sub : postponed ⊆ L
  placed_eq : state.placed = E.placed ∪ (L \ postponed)
  occupied_mono : E.occupied ⊆ state.occupied
  load_mono : ∀ a j, E.farLoad a j ≤ state.farLoad a j
  reserved : Disjoint state.occupied (H.reserved (F \ L))
  capacity : ∀ a j, (state.farLoad a j : ℝ) ≤ H.capacity a j
  bound : H.ReservoirBound state ∅
  failed : ∀ S ∈ postponed, H.FailedAt state (F \ L) S

theorem HeadOutcome.disjoint_pending {E : H.State} {F L : Finset ↥P.shrubs}
    (O : H.HeadOutcome E F L) (hEF : Disjoint E.placed F) :
    Disjoint O.state.placed (F \ L) := by
  apply Finset.disjoint_left.mpr
  intro S hS hSF
  rw [O.placed_eq] at hS
  rcases Finset.mem_union.mp hS with hS | hS
  · exact Finset.disjoint_left.mp hEF hS (Finset.mem_sdiff.mp hSF).1
  · exact (Finset.mem_sdiff.mp hSF).2 (Finset.mem_sdiff.mp hS).1

theorem HeadOutcome.disjoint_postponed {E : H.State} {F L : Finset ↥P.shrubs}
    (O : H.HeadOutcome E F L) (hEL : Disjoint E.placed L) :
    Disjoint O.state.placed O.postponed := by
  apply Finset.disjoint_left.mpr
  intro S hS hSB
  rw [O.placed_eq] at hS
  rcases Finset.mem_union.mp hS with hS | hS
  · exact Finset.disjoint_left.mp hEL hS (O.postponed_sub hSB)
  · exact (Finset.mem_sdiff.mp hS).2 hSB

theorem process_same_head (hT : T.IsTree) (i : I) (L : Finset ↥P.shrubs)
    (hhead : ∀ S ∈ L, H.head S = i) (E : H.State) (F : Finset ↥P.shrubs)
    (hLF : L ⊆ F) (hEF : Disjoint E.placed F)
    (hcap : ∀ a j, (E.farLoad a j : ℝ) ≤ H.capacity a j)
    (hbound : H.ReservoirBound E ∅) (hreserved : Disjoint E.occupied (H.reserved F)) :
    Nonempty (H.HeadOutcome E F L) := by
  classical
  induction L using Finset.induction_on generalizing E F with
  | empty =>
      refine ⟨{
        state := E
        postponed := ∅
        postponed_sub := Finset.Subset.refl _
        placed_eq := by simp
        occupied_mono := Finset.Subset.refl _
        load_mono := fun _ _ ↦ le_rfl
        reserved := by simpa only [Finset.sdiff_empty] using hreserved
        capacity := hcap
        bound := hbound
        failed := fun _ h ↦ (Finset.notMem_empty _ h).elim
      }⟩
  | @insert S L hSL ih =>
      have hSF := hLF (Finset.mem_insert_self S L)
      have hSnot : S ∉ E.placed := fun h ↦ Finset.disjoint_left.mp hEF h hSF
      have hLhead : ∀ A ∈ L, H.head A = i := fun A hA ↦ hhead A (Finset.mem_insert_of_mem hA)
      have hLF' : L ⊆ F.erase S := by
        intro A hA
        exact Finset.mem_erase.mpr ⟨(fun he ↦ hSL (he ▸ hA)), hLF (Finset.mem_insert_of_mem hA)⟩
      have hremain : F.erase S \ L = F \ insert S L := by
        ext A
        simp only [Finset.mem_sdiff, Finset.mem_erase, Finset.mem_insert]
        tauto
      rcases H.private_step_or_failure hT E F hEF hcap hbound hreserved S hSF with hfail | hstep
      · obtain ⟨O⟩ := ih hLhead E (F.erase S) hLF'
          (hEF.mono_right (Finset.erase_subset _ _)) hcap hbound
          (hreserved.mono_right (H.reserved_mono (Finset.erase_subset _ _)))
        have hSfail : H.FailedAt O.state (F \ insert S L) S :=
          H.failedAt_after_removal E O.state F (insert S L) i hhead S
            (hhead S (Finset.mem_insert_self _ _)) O.occupied_mono O.load_mono hfail
        refine ⟨{
          state := O.state
          postponed := insert S O.postponed
          postponed_sub := Finset.insert_subset_insert S O.postponed_sub
          placed_eq := ?_
          occupied_mono := O.occupied_mono
          load_mono := O.load_mono
          reserved := by simpa only [hremain] using O.reserved
          capacity := O.capacity
          bound := O.bound
          failed := ?_
        }⟩
        · rw [O.placed_eq]
          have he : insert S L \ insert S O.postponed = L \ O.postponed := by
            ext A
            by_cases hAS : A = S
            · subst A
              simp only [Finset.mem_sdiff, Finset.mem_insert, true_or, not_true_eq_false,
                and_false, hSL, false_and]
            · simp only [Finset.mem_sdiff, Finset.mem_insert, hAS, false_or]
          rw [he]
        · intro A hA
          rcases Finset.mem_insert.mp hA with rfl | hA
          · exact hSfail
          · simpa only [hremain] using O.failed A hA
      · obtain ⟨E₁, j, hplaced₁, htail₁, hmono₁, hres₁, hcap₁, hbound₁⟩ := hstep
        have hEF₁ : Disjoint E₁.placed (F.erase S) := by
          rw [hplaced₁]
          exact Finset.disjoint_insert_left.mpr
            ⟨Finset.notMem_erase _ _, hEF.mono_right (Finset.erase_subset _ _)⟩
        obtain ⟨O⟩ := ih hLhead E₁ (F.erase S) hLF' hEF₁ hcap₁ hbound₁ hres₁
        have hSB : S ∉ O.postponed := fun h ↦ hSL (O.postponed_sub h)
        refine ⟨{
          state := O.state
          postponed := O.postponed
          postponed_sub := O.postponed_sub.trans (Finset.subset_insert _ _)
          placed_eq := ?_
          occupied_mono := hmono₁.trans O.occupied_mono
          load_mono := fun a k ↦ (H.farLoad_le_after_insert E E₁ S hSnot j hplaced₁ htail₁ a k).trans
            (O.load_mono a k)
          reserved := by simpa only [hremain] using O.reserved
          capacity := O.capacity
          bound := O.bound
          failed := fun A hA ↦ by simpa only [hremain] using O.failed A hA
        }⟩
        rw [O.placed_eq, hplaced₁]
        ext A
        by_cases hAS : A = S
        · subst A
          simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_sdiff, true_or,
            hSB, not_false_eq_true, and_true, or_true]
        · simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_sdiff, hAS, false_or]

end Erdos547.ShrubHostSetup

#print axioms Erdos547.ShrubHostSetup.process_same_head
