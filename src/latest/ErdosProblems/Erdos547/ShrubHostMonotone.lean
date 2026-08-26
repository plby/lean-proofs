import ErdosProblems.Erdos547.ShrubHostFree

/-!
# Monotonicity while a group of shrubs is processed
-/

namespace Erdos547.ShrubHostSetup

open Finset SimpleGraph

variable {U V I : Type*} [Fintype U] [Fintype I]
  [DecidableEq U] [DecidableEq V] [DecidableEq I]
  {T : SimpleGraph U} [DecidableRel T.Adj] {r : U} {ℓ : ℕ}
  {col : T.Coloring (Fin 2)} {P : FineTreePartition T r ℓ col}
  {G : SimpleGraph V} [DecidableRel G.Adj]
variable (H : ShrubHostSetup P G I)

theorem reserved_mono {F F' : Finset ↥P.shrubs} (hF : F ⊆ F') :
    H.reserved F ⊆ H.reserved F' := by
  intro v hv
  obtain ⟨S, hS, hvS⟩ := Finset.mem_biUnion.mp hv
  exact Finset.mem_biUnion.mpr ⟨S, hF hS, hvS⟩

theorem reserved_release (F : Finset ↥P.shrubs) (S : ↥P.shrubs) :
    H.reserved F ⊆ H.reserved (F.erase S) ∪ H.clusters (H.head S) := by
  intro v hv
  obtain ⟨A, hA, hvA⟩ := Finset.mem_biUnion.mp hv
  by_cases he : A = S
  · subst A
    exact Finset.mem_union_right _ (H.private_sub S hvA)
  · exact Finset.mem_union_left _
      (Finset.mem_biUnion.mpr ⟨A, Finset.mem_erase.mpr ⟨he, hA⟩, hvA⟩)

theorem private_avoid_remainder (F : Finset ↥P.shrubs) (S : ↥P.shrubs) :
    Disjoint (H.privateSet S) (H.reserved (F.erase S)) := by
  apply Finset.disjoint_left.mpr
  intro v hvS hv
  obtain ⟨A, hA, hvA⟩ := Finset.mem_biUnion.mp hv
  exact Finset.disjoint_left.mp (H.private_disjoint S A (Finset.mem_erase.mp hA).1.symm) hvS hvA

theorem free_mono_after_release (E E' : H.State) (F : Finset ↥P.shrubs)
    (S : ↥P.shrubs) (j : I) (hused : E.occupied ⊆ E'.occupied)
    (hdis : Disjoint (H.clusters j) (H.clusters (H.head S))) :
    H.free E' (F.erase S) j ⊆ H.free E F j :=
  available_mono_away_from_released_set (H.clusters j) (H.clusters (H.head S))
    (H.reservoir j) E.occupied E'.occupied (H.reserved F) (H.reserved (F.erase S))
    hdis hused (H.reserved_release F S)

theorem farLoad_le_after_insert (E E' : H.State) (S : ↥P.shrubs) (hS : S ∉ E.placed) (j : I)
    (hplaced : E'.placed = insert S E.placed) (htail : E'.tail = Function.update E.tail S j)
    (a : Fin 2 × I) (i : I) : E.farLoad a i ≤ E'.farLoad a i := by
  unfold ShrubState.farLoad
  rw [hplaced, htail]
  exact routedLoad_le_after_insert E.placed (ShrubState.shrubGroup P H.head) E.tail
    (fun S ↦ (P.farPart S).card) S hS j a i

theorem targets_shrink (E E' : H.State)
    (hload : ∀ a i, E.farLoad a i ≤ E'.farLoad a i)
    (S : ↥P.shrubs) (j : I) (hj : H.IsTarget E' S j) : H.IsTarget E S j := by
  refine ⟨hj.1, ?_⟩
  have hh : (E.farLoad (ShrubState.shrubGroup P H.head S) j : ℝ) ≤
      (E'.farLoad (ShrubState.shrubGroup P H.head S) j : ℝ) := by exact_mod_cast hload _ _
  exact hh.trans_lt hj.2

theorem reserved_sdiff_release (F L : Finset ↥P.shrubs) (i : I)
    (hhead : ∀ S ∈ L, H.head S = i) :
    H.reserved F ⊆ H.reserved (F \ L) ∪ H.clusters i := by
  intro v hv
  obtain ⟨S, hSF, hvS⟩ := Finset.mem_biUnion.mp hv
  by_cases hSL : S ∈ L
  · apply Finset.mem_union_right
    rw [← hhead S hSL]
    exact H.private_sub S hvS
  · exact Finset.mem_union_left _
      (Finset.mem_biUnion.mpr ⟨S, Finset.mem_sdiff.mpr ⟨hSF, hSL⟩, hvS⟩)

end Erdos547.ShrubHostSetup
