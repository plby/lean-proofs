/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.CyclowarpDecomposition

/-!
# Finite modifications of a finite-character warp

Adding and deleting finitely many edges can join only finitely many of the
finite paths of a finite-character warp.  Consequently every weak component
of the modified edge relation is finite.  This is the component-finiteness
input used by the one-hole residual augmentation construction.
-/

namespace Erdos599
namespace DWeb

open Set DirectedPath
open Alternating

universe u

variable {V : Type u}

/-- Endpoints of the finitely many edges added to a warp. -/
private def finiteModificationTouched (F : Set (V × V)) : Set V :=
  Prod.fst '' F ∪ Prod.snd '' F

private theorem finiteModificationTouched_finite {F : Set (V × V)}
    (hF : F.Finite) : (finiteModificationTouched F).Finite := by
  exact (hF.image Prod.fst).union (hF.image Prod.snd)

/-- The added-edge endpoints together with every old warp path which they
touch. -/
private noncomputable def finiteModificationAffected
    (G : DWeb V) {J : Set G.DPath} (hJ : G.IsWarp J)
    (F : Set (V × V)) : Set V :=
  finiteModificationTouched F ∪
    ⋃ x ∈ finiteModificationTouched F, coveredPathSupport hJ x

private theorem finiteModificationAffected_finite
    (G : DWeb V) {J : Set G.DPath} (hJ : G.IsWarp J)
    (hJfin : G.HasFiniteCharacter J) {F : Set (V × V)}
    (hF : F.Finite) :
    (finiteModificationAffected G hJ F).Finite := by
  classical
  have htouched : (finiteModificationTouched F).Finite :=
    finiteModificationTouched_finite hF
  apply htouched.union
  exact htouched.biUnion fun x _ ↦
    coveredPathSupport_finite hJ hJfin x

private theorem coveredPathSupport_closed_left
    (G : DWeb V) {J : Set G.DPath} (hJ : G.IsWarp J)
    {a x y : V} (hxy : (x, y) ∈ familyEdges J)
    (hx : x ∈ coveredPathSupport hJ a) :
    y ∈ coveredPathSupport hJ a := by
  classical
  simp only [familyEdges, Set.mem_iUnion] at hxy
  rcases hxy with ⟨p, hpJ, hxyp⟩
  have hxp : x ∈ p.support := p.edgeSet_subset_support_prod hxyp |>.1
  have hyp : y ∈ p.support := p.edgeSet_subset_support_prod hxyp |>.2
  by_cases haJ : a ∈ G.vertexSet J
  · rw [coveredPathSupport, dif_pos haJ] at hx ⊢
    have hpath := DWeb.IsWarp.pathAt_mem hJ haJ
    have hpeq : p = DWeb.IsWarp.pathAt hJ haJ :=
      DWeb.IsWarp.eq_of_mem_support hJ hpJ hpath hxp hx
    simpa [← hpeq] using hyp
  · rw [coveredPathSupport, dif_neg haJ] at hx
    exact False.elim (by simpa using hx)

private theorem coveredPathSupport_closed_right
    (G : DWeb V) {J : Set G.DPath} (hJ : G.IsWarp J)
    {a x y : V} (hxy : (x, y) ∈ familyEdges J)
    (hy : y ∈ coveredPathSupport hJ a) :
    x ∈ coveredPathSupport hJ a := by
  classical
  simp only [familyEdges, Set.mem_iUnion] at hxy
  rcases hxy with ⟨p, hpJ, hxyp⟩
  have hxp : x ∈ p.support := p.edgeSet_subset_support_prod hxyp |>.1
  have hyp : y ∈ p.support := p.edgeSet_subset_support_prod hxyp |>.2
  by_cases haJ : a ∈ G.vertexSet J
  · rw [coveredPathSupport, dif_pos haJ] at hy ⊢
    have hpath := DWeb.IsWarp.pathAt_mem hJ haJ
    have hpeq : p = DWeb.IsWarp.pathAt hJ haJ :=
      DWeb.IsWarp.eq_of_mem_support hJ hpJ hpath hyp hy
    simpa [← hpeq] using hxp
  · rw [coveredPathSupport, dif_neg haJ] at hy
    exact False.elim (by simpa using hy)

private theorem finiteModificationAffected_closed_left
    (G : DWeb V) {J : Set G.DPath} (hJ : G.IsWarp J)
    {F : Set (V × V)} {x y : V}
    (hxy : (x, y) ∈ familyEdges J)
    (hx : x ∈ finiteModificationAffected G hJ F) :
    y ∈ finiteModificationAffected G hJ F := by
  classical
  simp only [familyEdges, Set.mem_iUnion] at hxy
  rcases hxy with ⟨p, hpJ, hxyp⟩
  rcases hx with hx | hx
  · right
    simp only [Set.mem_iUnion]
    exact ⟨x, hx, (coveredPathSupport_eq_of_mem hJ hpJ
      (p.edgeSet_subset_support_prod hxyp).1).symm ▸
        (p.edgeSet_subset_support_prod hxyp).2⟩
  · simp only [Set.mem_iUnion] at hx
    rcases hx with ⟨a, ha, hxa⟩
    right
    simp only [Set.mem_iUnion]
    have hxy : (x, y) ∈ familyEdges J := by
      simp only [familyEdges, Set.mem_iUnion]
      exact ⟨p, hpJ, hxyp⟩
    exact ⟨a, ha, coveredPathSupport_closed_left G hJ hxy hxa⟩

private theorem finiteModificationAffected_closed_right
    (G : DWeb V) {J : Set G.DPath} (hJ : G.IsWarp J)
    {F : Set (V × V)} {x y : V}
    (hxy : (x, y) ∈ familyEdges J)
    (hy : y ∈ finiteModificationAffected G hJ F) :
    x ∈ finiteModificationAffected G hJ F := by
  classical
  rcases hy with hy | hy
  · right
    simp only [Set.mem_iUnion]
    simp only [familyEdges, Set.mem_iUnion] at hxy
    rcases hxy with ⟨p, hpJ, hxyp⟩
    exact ⟨y, hy, (coveredPathSupport_eq_of_mem hJ hpJ
      (p.edgeSet_subset_support_prod hxyp).2).symm ▸
        (p.edgeSet_subset_support_prod hxyp).1⟩
  · simp only [Set.mem_iUnion] at hy
    rcases hy with ⟨a, ha, hya⟩
    right
    simp only [Set.mem_iUnion]
    exact ⟨a, ha, coveredPathSupport_closed_right G hJ hxy hya⟩

/-- A finite set containing the whole weak component of `root` after a
finite edge modification. -/
private noncomputable def finiteModificationComponentBound
    (G : DWeb V) {J : Set G.DPath} (hJ : G.IsWarp J)
    (F : Set (V × V)) (root : V) : Set V :=
  finiteModificationAffected G hJ F ∪
    coveredPathSupport hJ root ∪ {root}

private theorem finiteModificationComponentBound_finite
    (G : DWeb V) {J : Set G.DPath} (hJ : G.IsWarp J)
    (hJfin : G.HasFiniteCharacter J) {F : Set (V × V)}
    (hF : F.Finite) (root : V) :
    (finiteModificationComponentBound G hJ F root).Finite := by
  exact ((finiteModificationAffected_finite G hJ hJfin hF).union
    (coveredPathSupport_finite hJ hJfin root)).union
      (Set.finite_singleton root)

private theorem finiteModificationComponentBound_closed
    (G : DWeb V) {J : Set G.DPath} (hJ : G.IsWarp J)
    {B F : Set (V × V)} (root : V) {x y : V}
    (hstep : RelationComponents.WeakRel
      ((familyEdges J \ B) ∪ F) x y)
    (hx : x ∈ finiteModificationComponentBound G hJ F root) :
    y ∈ finiteModificationComponentBound G hJ F root := by
  classical
  have hold_left : ∀ {u v : V}, (u, v) ∈ familyEdges J →
      u ∈ finiteModificationComponentBound G hJ F root →
        v ∈ finiteModificationComponentBound G hJ F root := by
    intro u v huv hu
    rcases hu with hu | hu
    · rcases hu with hu | hu
      · exact Or.inl (Or.inl
          (finiteModificationAffected_closed_left G hJ huv hu))
      · exact Or.inl (Or.inr
          (coveredPathSupport_closed_left G hJ huv hu))
    · have hur : u = root := by simpa using hu
      subst u
      have huv' := huv
      simp only [familyEdges, Set.mem_iUnion] at huv'
      rcases huv' with ⟨p, hpJ, huvp⟩
      exact Or.inl (Or.inr
        ((coveredPathSupport_eq_of_mem hJ hpJ
          (p.edgeSet_subset_support_prod huvp).1).symm ▸
            (p.edgeSet_subset_support_prod huvp).2))
  have hold_right : ∀ {u v : V}, (u, v) ∈ familyEdges J →
      v ∈ finiteModificationComponentBound G hJ F root →
        u ∈ finiteModificationComponentBound G hJ F root := by
    intro u v huv hv
    rcases hv with hv | hv
    · rcases hv with hv | hv
      · exact Or.inl (Or.inl
          (finiteModificationAffected_closed_right G hJ huv hv))
      · exact Or.inl (Or.inr
          (coveredPathSupport_closed_right G hJ huv hv))
    · have hvr : v = root := by simpa using hv
      subst v
      simp only [familyEdges, Set.mem_iUnion] at huv
      rcases huv with ⟨p, hpJ, huvp⟩
      exact Or.inl (Or.inr
        ((coveredPathSupport_eq_of_mem hJ hpJ
          (p.edgeSet_subset_support_prod huvp).2).symm ▸
            (p.edgeSet_subset_support_prod huvp).1))
  rcases hstep with hxy | hyx
  · rcases hxy with hxy | hxy
    · exact hold_left hxy.1 hx
    · exact Or.inl (Or.inl (Or.inl
        (Or.inr ⟨(x, y), hxy, rfl⟩)))
  · rcases hyx with hyx | hyx
    · exact hold_right hyx.1 hx
    · exact Or.inl (Or.inl (Or.inl
        (Or.inl ⟨(y, x), hyx, rfl⟩)))

private theorem finiteModification_reachable_subset_componentBound
    (G : DWeb V) {J : Set G.DPath} (hJ : G.IsWarp J)
    {B F : Set (V × V)} (root : V) :
    {x | Relation.ReflTransGen
      (RelationComponents.WeakRel ((familyEdges J \ B) ∪ F)) root x} ⊆
      finiteModificationComponentBound G hJ F root := by
  intro x hx
  change Relation.ReflTransGen _ root x at hx
  induction hx with
  | refl => exact Or.inr (by simp)
  | tail hreach hstep ih =>
      exact finiteModificationComponentBound_closed G hJ root hstep ih

/-- Every weak component of a relation obtained from the edge relation of a
finite-character warp by deleting and adding finitely many edges is finite. -/
theorem finite_componentSupports_of_finiteModification_familyEdges
    (G : DWeb V) {J : Set G.DPath} (hJ : G.IsWarp J)
    (hJfin : G.HasFiniteCharacter J) {B F : Set (V × V)}
    (_hB : B.Finite) (hF : F.Finite) :
    ∀ c : RelationComponents.Component ((familyEdges J \ B) ∪ F),
      (RelationComponents.componentSupport
        ((familyEdges J \ B) ∪ F) c).Finite := by
  apply RelationComponents.finite_componentSupports_of_roots
  intro root
  exact (finiteModificationComponentBound_finite G hJ hJfin hF root).subset
    (finiteModification_reachable_subset_componentBound G hJ root)

end DWeb
end Erdos599
