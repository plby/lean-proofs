import ErdosProblems.Erdos556.ProfileRefinementGeometry
import ErdosProblems.Erdos556.TwoColourSetStructure
import ErdosProblems.Erdos556.BipartiteDefect

/-! Refining one positive tiling profile into its edge cores. -/

namespace Erdos556

open SimpleGraph Finset

structure ProfileRefinement {V : Type*} [DecidableEq V]
    (c : ThreeColouring V) (p : CubeProfile) (A : Finset V) (L d : ℕ) where
  direction : Fin 3
  cores : Fin 4 → Finset V
  subprofile : ∀ l, evenCubeVertex l ∈ profileVertices p →
    profileVertices (matchingProfile l direction) ⊆ profileVertices p
  subset : ∀ l, evenCubeVertex l ∈ profileVertices p → cores l ⊆ A
  large : ∀ l, evenCubeVertex l ∈ profileVertices p → L ≤ (cores l).card
  profile_disjoint : ∀ l m, l ≠ m → evenCubeVertex l ∈ profileVertices p →
    evenCubeVertex m ∈ profileVertices p →
    Disjoint (profileVertices (matchingProfile l direction)) (profileVertices (matchingProfile m direction))
  core_disjoint : ∀ l m, l ≠ m → evenCubeVertex l ∈ profileVertices p →
    evenCubeVertex m ∈ profileVertices p → Disjoint (cores l) (cores m)
  dense : ∀ l m, evenCubeVertex l ∈ profileVertices p →
    evenCubeVertex m ∈ profileVertices p → ∀ i,
    uniqueProfileSeparator (matchingProfile l direction) (matchingProfile m direction) i →
    BipartiteDefect (c.graph i) (cores l) (cores m) d

theorem exists_edge_profile_refinement {V : Type*} [DecidableEq V]
    (c : ThreeColouring V) (p : CubeProfile) (A : Finset V) (L d : ℕ)
    (hp : profileDimension p = 1) (hA : L ≤ A.card) :
    Nonempty (ProfileRefinement c p A L d) := by
  obtain ⟨a, ha⟩ := edge_profile_direction p hp
  have hsame (l m : Fin 4) (hl : evenCubeVertex l ∈ profileVertices p)
      (hm : evenCubeVertex m ∈ profileVertices p) : l = m :=
    edge_profile_even_vertex_unique p l m hp hl hm
  refine ⟨{
    direction := a
    cores := fun _ => A
    subprofile := fun l hl => by rw [ha l hl]
    subset := fun _ _ => Subset.rfl
    large := fun _ _ => hA
    profile_disjoint := fun l m hlm hl hm => (hlm (hsame l m hl hm)).elim
    core_disjoint := fun l m hlm hl hm => (hlm (hsame l m hl hm)).elim
    dense := ?_ }⟩
  intro l m hl hm i hsep
  have hsame' := hsame l m hl hm
  subst m
  have hd := profileOppositeAt_disjoint _ _ i hsep.1
  have he : profileVertices (matchingProfile l a) = ∅ := by
    simpa only [disjoint_self, Finset.bot_eq_empty] using hd
  have hmem := evenCubeVertex_mem_matchingProfile l a
  rw [he] at hmem
  exact (notMem_empty _ hmem).elim

def boolCore {V : Type*} (S T : Finset V) (b : Bool) : Finset V := if b then T else S

theorem boolCore_subset {V : Type*} {S T A : Finset V}
    (hS : S ⊆ A) (hT : T ⊆ A) (b : Bool) : boolCore S T b ⊆ A := by
  cases b <;> assumption

theorem boolCore_card_le {V : Type*} {S T : Finset V} {L : ℕ}
    (hS : L ≤ S.card) (hT : L ≤ T.card) (b : Bool) : L ≤ (boolCore S T b).card := by
  cases b <;> assumption

theorem boolCore_disjoint {V : Type*} {S T : Finset V} (hdis : Disjoint S T)
    (a b : Bool) (hab : a ≠ b) : Disjoint (boolCore S T a) (boolCore S T b) := by
  cases a <;> cases b
  · exact (hab rfl).elim
  · exact hdis
  · exact hdis.symm
  · exact (hab rfl).elim

theorem boolCore_cross {V : Type*} {G : SimpleGraph V} {S T : Finset V}
    (hcross : ∀ u ∈ S, ∀ v ∈ T, G.Adj u v)
    (a b : Bool) (hab : a ≠ b) :
    ∀ u ∈ boolCore S T a, ∀ v ∈ boolCore S T b, G.Adj u v := by
  cases a <;> cases b
  · exact (hab rfl).elim
  · exact hcross
  · exact fun u hu v hv => (hcross v hv u hu).symm
  · exact (hab rfl).elim

theorem bipartiteDefect_of_complete_cross {V : Type*} [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (S T : Finset V) (d : ℕ)
    (hcross : ∀ u ∈ S, ∀ v ∈ T, G.Adj u v) : BipartiteDefect G S T d := by
  constructor
  · intro u hu
    have he : T.filter (fun v => ¬ G.Adj u v) = ∅ := by
      apply filter_eq_empty_iff.mpr
      intro v hv hn
      exact hn (hcross u hu v hv)
    rw [he, card_empty]
    exact Nat.zero_le _
  · intro v hv
    have he : S.filter (fun u => ¬ G.Adj v u) = ∅ := by
      apply filter_eq_empty_iff.mpr
      intro u hu hn
      exact hn (hcross u hu v hv).symm
    rw [he, card_empty]
    exact Nat.zero_le _

theorem exists_face_profile_refinement {V : Type*} [DecidableEq V]
    (c : ThreeColouring V) (A : Finset V) (r L d : ℕ) (i j k : Fin 3) (b : Bool)
    (hji : j ≠ i) (hki : k ≠ i) (hjk : j ≠ k)
    (hpart : TwoColourSetPartition c A r j k)
    (hS : L ≤ hpart.first.card) (hT : L ≤ hpart.second.card) :
    Nonempty (ProfileRefinement c (cubeFace i b) A L d) := by
  let B : Fin 4 → Finset V := fun l => boolCore hpart.first hpart.second (evenCubeVertex l k)
  have hbits (l m : Fin 4) (hlm : l ≠ m)
      (hl : evenCubeVertex l ∈ profileVertices (cubeFace i b))
      (hm : evenCubeVertex m ∈ profileVertices (cubeFace i b)) :
      evenCubeVertex l k ≠ evenCubeVertex m k := face_even_vertices_differ i k b l m hki hlm hl hm
  refine ⟨{
    direction := j
    cores := B
    subprofile := fun l hl => face_matching_profile_subset i j b l hji hl
    subset := fun l _ => boolCore_subset hpart.first_subset hpart.second_subset _
    large := fun l _ => boolCore_card_le hS hT _
    profile_disjoint := fun l m hlm hl hm => face_parallel_profiles_disjoint i j b l m hji hlm hl hm
    core_disjoint := fun l m hlm hl hm => boolCore_disjoint hpart.disjoint _ _ (hbits l m hlm hl hm)
    dense := ?_ }⟩
  intro l m hl hm z hsep
  have hzk := face_parallel_unique_separator i j k z b l m hji hki hjk hl hm hsep
  subst z
  have hlm : l ≠ m := by
    intro he
    subst m
    have hdis := profileOppositeAt_disjoint _ _ k hsep.1
    have he : profileVertices (matchingProfile l j) = ∅ := by
      simpa only [disjoint_self, Finset.bot_eq_empty] using hdis
    have hh := evenCubeVertex_mem_matchingProfile l j
    rw [he] at hh
    exact notMem_empty _ hh
  apply bipartiteDefect_of_complete_cross
  exact boolCore_cross hpart.cross _ _ (hbits l m hlm hl hm)

#print axioms exists_edge_profile_refinement
#print axioms exists_face_profile_refinement

end Erdos556
