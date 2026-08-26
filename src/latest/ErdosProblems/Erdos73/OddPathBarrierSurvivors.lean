import ErdosProblems.Erdos73.OddPathBarrierWitness

/-! Surviving vertices of the matching barrier and its component cutsets. -/

namespace Erdos73.OddPathBarrierWitness

open SimpleGraph Finset Erdos556 OddPathVertex

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} {A : Finset V} {k : ℕ}

theorem survives_removed_nonterminal (B : OddPathBarrierWitness G A k)
    {x : OddPathVertex A} (hx : projection x ∉ B.deletion) (hxW : x ∈ B.removed) :
    projection x ∉ A := by
  intro ht
  exact B.representative_not_removed (B.survives_terminal_mem_representatives hx ht) hxW

theorem survives_removed_mate_representative (B : OddPathBarrierWitness G A k)
    {x : OddPathVertex A} (hx : projection x ∉ B.deletion) (hxW : x ∈ B.removed) :
    mate x ∈ B.representatives := by
  have hxt := B.survives_removed_nonterminal hx hxW
  have hmW : mate x ∉ B.removed := by
    intro hmW
    exact B.survives_not_deletedPairs hx
      ((mem_oddPathDeletedPair_support B.removed x).mpr ⟨hxt, hxW, hmW⟩)
  apply B.survives_eligible_mem_representatives (by simpa only [projection_mate] using hx)
  apply Finset.mem_union_right
  apply (mem_oddPathExposedMates B.removed (mate x)).mpr
  simpa only [projection_mate, mate_mate] using And.intro hxt (And.intro hmW hxW)

open scoped Classical in
theorem representatives_independent (B : OddPathBarrierWitness G A k)
    {x y : OddPathVertex A} (hx : x ∈ B.representatives) (hy : y ∈ B.representatives) :
    ¬ (oddPathAuxiliary G A).Adj x y := by
  intro hxy
  obtain ⟨C, hxC⟩ := exists_deletedComponent_containing x (B.representative_not_removed hx)
  have hyC := deletedComponentVertices_closed (G := oddPathAuxiliary G A) C hxC
    (B.representative_not_removed hy) hxy
  exact hxy.ne (B.unique C x hx y hy hxC hyC)

open scoped Classical in
theorem surviving_removed_independent (B : OddPathBarrierWitness G A k)
    {x y : OddPathVertex A} (hx : projection x ∉ B.deletion) (hy : projection y ∉ B.deletion)
    (hxW : x ∈ B.removed) (hyW : y ∈ B.removed) :
    ¬ (oddPathAuxiliary G A).Adj x y := by
  intro hxy
  exact B.representatives_independent (B.survives_removed_mate_representative hx hxW)
    (B.survives_removed_mate_representative hy hyW)
    (oddPathAuxiliary_reflect hxy (B.survives_removed_nonterminal hx hxW)
      (B.survives_removed_nonterminal hy hyW))

open scoped Classical in
theorem survives_component_interior_mate (B : OddPathBarrierWitness G A k)
    (C : (vertexDeletedGraph (oddPathAuxiliary G A) B.removed).ConnectedComponent)
    {x : OddPathVertex A} (hx : projection x ∉ B.deletion)
    (hxC : x ∈ deletedComponentVertices C) (hxZ : x ∉ B.representatives) :
    projection x ∉ A ∧ mate x ∈ deletedComponentVertices C ∧ mate x ∉ B.representatives := by
  have hxt : projection x ∉ A := fun ht =>
    hxZ (B.survives_terminal_mem_representatives hx ht)
  have hxW := deletedComponentVertices_not_mem C hxC
  have hmW : mate x ∉ B.removed := by
    intro hmW
    apply hxZ
    apply B.survives_eligible_mem_representatives hx
    exact Finset.mem_union_right _ ((mem_oddPathExposedMates B.removed x).mpr ⟨hxt, hxW, hmW⟩)
  refine ⟨hxt, deletedComponentVertices_closed C hxC hmW (oddPathAuxiliary_adj_mate G A x hxt), ?_⟩
  intro hmZ
  have hmem := (Finset.mem_sdiff.mp (B.subset hmZ)).1
  rcases Finset.mem_union.mp hmem with hmT | hmB
  · have ht := (mem_oddPathTerminals A (mate x)).mp hmT
    exact hxt (by simpa only [projection_mate] using ht)
  · have hw := ((mem_oddPathExposedMates B.removed (mate x)).mp hmB).2.2
    exact hxW (by simpa only [mate_mate] using hw)

open scoped Classical in
noncomputable def componentCut (B : OddPathBarrierWitness G A k)
    (C : (vertexDeletedGraph (oddPathAuxiliary G A) B.removed).ConnectedComponent) :
    Finset (OddPathVertex A) :=
  (B.representatives ∩ deletedComponentVertices C) ∪
    (B.representatives ∩ deletedComponentVertices C).image mate

open scoped Classical in
theorem component_interior_boundary (B : OddPathBarrierWitness G A k)
    (C : (vertexDeletedGraph (oddPathAuxiliary G A) B.removed).ConnectedComponent)
    {x y : OddPathVertex A} (hx : projection x ∉ B.deletion) (hy : projection y ∉ B.deletion)
    (hxI : x ∈ deletedComponentVertices C \ B.representatives)
    (hyI : y ∉ deletedComponentVertices C \ B.representatives)
    (hxy : (oddPathAuxiliary G A).Adj x y) : y ∈ B.componentCut C := by
  obtain ⟨hxC, hxZ⟩ := Finset.mem_sdiff.mp hxI
  by_cases hyC : y ∈ deletedComponentVertices C
  · have hyZ : y ∈ B.representatives := by
      by_contra hn
      exact hyI (Finset.mem_sdiff.mpr ⟨hyC, hn⟩)
    exact Finset.mem_union_left _ (Finset.mem_inter.mpr ⟨hyZ, hyC⟩)
  · have hyW : y ∈ B.removed := by
      by_contra hn
      exact hyC (deletedComponentVertices_closed C hxC hn hxy)
    have hmZ := B.survives_removed_mate_representative hy hyW
    obtain ⟨hxt, hmC, _⟩ := B.survives_component_interior_mate C hx hxC hxZ
    have hmYC := deletedComponentVertices_closed C hmC (B.representative_not_removed hmZ)
      (oddPathAuxiliary_reflect hxy hxt (B.survives_removed_nonterminal hy hyW))
    exact Finset.mem_union_right _ (Finset.mem_image.mpr
      ⟨mate y, Finset.mem_inter.mpr ⟨hmZ, hmYC⟩, mate_mate y⟩)

end Erdos73.OddPathBarrierWitness
