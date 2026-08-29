/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.AlternatingMacroFlatten
import ErdosProblems.Erdos599.OmegaListFlatten

/-!
# The raw vertex stream of an endpoint-pure macro chain

This file specializes `OmegaBlocks` to the concrete finite auxiliary walks
realizing a `MacroChain`.  It supplies the raw vertex stream and proves that
every successive pair is a genuine `MacroEdge`.
-/

namespace Erdos599
namespace Alternating

open Set DirectedPath

universe u

variable {V : Type u} {Γ : DWeb V}

namespace Walk

/-- A nontrivial endpoint-indexed walk has at least two support vertices. -/
theorem two_le_support_length_of_ne {D : Digraph V} {a b : V}
    (p : Walk D a b) (hab : a ≠ b) : 2 ≤ p.support.length := by
  cases p with
  | nil => exact (hab rfl).elim
  | @cons a c b h p =>
      simp only [Walk.support_cons, List.length_cons]
      have hp : 0 < p.support.length :=
        List.length_pos_iff.mpr p.support_ne_nil
      omega

/-- Consecutive entries in a walk's support are joined by an ambient edge. -/
theorem adj_get_support {D : Digraph V} {a b : V}
    (p : Walk D a b) (j : ℕ) (hj : j + 1 < p.support.length) :
    D.Adj (p.support.get ⟨j, by omega⟩)
      (p.support.get ⟨j + 1, hj⟩) := by
  induction p generalizing j with
  | nil => simp at hj
  | @cons a c b h p ih =>
      cases j with
      | zero =>
          simp only [Walk.support_cons, List.get_eq_getElem,
            List.getElem_cons_zero, List.getElem_cons_succ]
          have hpos : 0 < p.support.length :=
            List.length_pos_iff.mpr p.support_ne_nil
          simpa only [List.getElem_zero hpos, p.head_support] using h
      | succ j =>
          simp only [Walk.support_cons, List.length_cons] at hj
          simp only [Walk.support_cons, List.get_eq_getElem,
            List.getElem_cons_succ]
          simpa only [List.get_eq_getElem] using ih (j := j) (by omega)

end Walk

namespace MacroChain

variable {Z Y : Set Γ.DPath} (C : MacroChain Z Y)

/-- Consecutive `Z` paths in a root-anchored macro chain have different
initial vertices. -/
theorem z_initial_ne_succ
    (hZ : Γ.IsWarp Z) (hY : Γ.IsWarp Y)
    (hroot : (C.z 0).1.initial ∉ Γ.vertexSet Y) (n : ℕ) :
    (C.z n).1.initial ≠ (C.z (n + 1)).1.initial := by
  intro hinit
  have hpaths : C.z n = C.z (n + 1) := by
    apply Subtype.ext
    exact DWeb.IsWarp.eq_of_mem_support hZ (C.z n).2 (C.z (n + 1)).2
      (C.z n).1.initial_mem_support
      (hinit ▸ (C.z (n + 1)).1.initial_mem_support)
  have hn : n = n + 1 := (C.z_injective hZ hY hroot) hpaths
  omega

/-- The concrete finite macro walks, packaged as joined positive-length
vertex blocks. -/
noncomputable def streamBlocks
    (hZ : Γ.IsWarp Z) (hY : Γ.IsWarp Y)
    (hZfin : Γ.HasFiniteCharacter Z) (hYfin : Γ.HasFiniteCharacter Y)
    (hroot : (C.z 0).1.initial ∉ Γ.vertexSet Y) : OmegaBlocks V where
  block n := (C.blockWalk hZfin hYfin n).support
  length_pos n :=
    Walk.two_le_support_length_of_ne (C.blockWalk hZfin hYfin n)
      (C.z_initial_ne_succ hZ hY hroot n)
  joins n := by
    rw [(C.blockWalk hZfin hYfin n).getLast_support,
      (C.blockWalk hZfin hYfin (n + 1)).head_support]

@[simp]
theorem support_blockWalk_stream
    (hZfin : Γ.HasFiniteCharacter Z) (hYfin : Γ.HasFiniteCharacter Y)
    (n : ℕ) :
    (C.blockWalk hZfin hYfin n).support =
      (C.zFinite hZfin n).walk.support ++
        (C.yFinite hYfin n).walk.support.dropLast.reverse := by
  let f := C.zBlockWalk (Y := Y) hZfin n
  let b := C.yBlockWalk (Z := Z) hYfin n
  have hfstart' : (C.zFinite hZfin n).start = (C.z n).1.initial :=
    (congrArg Path.initial (C.z_eq_zFinite hZfin n)).symm
  have hffinish : (C.zFinite hZfin n).finish = C.terminal n := by
    have h := C.z_terminal n
    rw [C.z_eq_zFinite hZfin n] at h
    exact Option.some.inj h
  have hbfinish : (C.yFinite hYfin n).finish = C.terminal n := by
    have h := C.y_terminal n
    rw [C.y_eq_yFinite hYfin n] at h
    exact Option.some.inj h
  have hjoin : (C.zFinite hZfin n).finish =
      (C.yFinite hYfin n).finish := hffinish.trans hbfinish.symm
  have hbstart : (C.yFinite hYfin n).start =
      (C.z (n + 1)).1.initial :=
    (congrArg Path.initial (C.y_eq_yFinite hYfin n)).symm.trans (C.joins n)
  change (Walk.castEndpoints hfstart' hbstart
    (f.append (Walk.castEndpoints hjoin.symm rfl b))).support = _
  calc
    _ = (f.append (Walk.castEndpoints hjoin.symm rfl b)).support :=
      Walk.support_castEndpoints _ _ _
    _ = f.support ++ (Walk.castEndpoints hjoin.symm rfl b).support.tail :=
      Walk.support_append _ _
    _ = _ := by simp [f, b]

/-- Every block vertex belongs to its forward `Z` carrier or its backward
`Y` carrier. -/
theorem mem_z_or_y_of_mem_blockWalk_stream
    (hZfin : Γ.HasFiniteCharacter Z) (hYfin : Γ.HasFiniteCharacter Y)
    {n : ℕ} {x : V} (hx : x ∈ (C.blockWalk hZfin hYfin n).support) :
    x ∈ (C.z n).1.support ∨ x ∈ (C.y n).1.support := by
  rw [C.support_blockWalk_stream hZfin hYfin] at hx
  simp only [List.mem_append, List.mem_reverse] at hx
  rcases hx with hx | hx
  · left
    rw [C.z_eq_zFinite hZfin n]
    exact hx
  · right
    rw [C.y_eq_yFinite hYfin n]
    exact List.mem_of_mem_dropLast hx

/-- Three macro blocks sharing one vertex cannot have three distinct
indices. -/
theorem block_indices_pair_stream
    (hZ : Γ.IsWarp Z) (hY : Γ.IsWarp Y)
    (hZfin : Γ.HasFiniteCharacter Z) (hYfin : Γ.HasFiniteCharacter Y)
    (hroot : (C.z 0).1.initial ∉ Γ.vertexSet Y)
    {x : V} {i j k : ℕ}
    (hxi : x ∈ (C.blockWalk hZfin hYfin i).support)
    (hxj : x ∈ (C.blockWalk hZfin hYfin j).support)
    (hxk : x ∈ (C.blockWalk hZfin hYfin k).support) :
    i = j ∨ i = k ∨ j = k := by
  have hi := C.mem_z_or_y_of_mem_blockWalk_stream hZfin hYfin hxi
  have hj := C.mem_z_or_y_of_mem_blockWalk_stream hZfin hYfin hxj
  have hk := C.mem_z_or_y_of_mem_blockWalk_stream hZfin hYfin hxk
  rcases hi with hiZ | hiY <;> rcases hj with hjZ | hjY <;>
      rcases hk with hkZ | hkY
  · left
    by_contra hij
    exact Set.disjoint_left.1 (C.z_support_disjoint hZ hY hroot hij) hiZ hjZ
  · left
    by_contra hij
    exact Set.disjoint_left.1 (C.z_support_disjoint hZ hY hroot hij) hiZ hjZ
  · right; left
    by_contra hik
    exact Set.disjoint_left.1 (C.z_support_disjoint hZ hY hroot hik) hiZ hkZ
  · right; right
    by_contra hjk
    exact Set.disjoint_left.1 (C.y_support_disjoint hZ hY hroot hjk) hjY hkY
  · right; right
    by_contra hjk
    exact Set.disjoint_left.1 (C.z_support_disjoint hZ hY hroot hjk) hjZ hkZ
  · right; left
    by_contra hik
    exact Set.disjoint_left.1 (C.y_support_disjoint hZ hY hroot hik) hiY hkY
  · left
    by_contra hij
    exact Set.disjoint_left.1 (C.y_support_disjoint hZ hY hroot hij) hiY hjY
  · left
    by_contra hij
    exact Set.disjoint_left.1 (C.y_support_disjoint hZ hY hroot hij) hiY hjY

/-- Cumulative number of raw macro edges before block `n`. -/
noncomputable def streamBoundary
    (hZ : Γ.IsWarp Z) (hY : Γ.IsWarp Y)
    (hZfin : Γ.HasFiniteCharacter Z) (hYfin : Γ.HasFiniteCharacter Y)
    (hroot : (C.z 0).1.initial ∉ Γ.vertexSet Y) (n : ℕ) : ℕ :=
  (C.streamBlocks hZ hY hZfin hYfin hroot).boundary n

/-- The raw vertex at global edge-time `k`. -/
noncomputable def rawMacroVertex
    (hZ : Γ.IsWarp Z) (hY : Γ.IsWarp Y)
    (hZfin : Γ.HasFiniteCharacter Z) (hYfin : Γ.HasFiniteCharacter Y)
    (hroot : (C.z 0).1.initial ∉ Γ.vertexSet Y) (k : ℕ) : V :=
  (C.streamBlocks hZ hY hZfin hYfin hroot).rawVertex k

@[simp]
theorem rawMacroVertex_boundary
    (hZ : Γ.IsWarp Z) (hY : Γ.IsWarp Y)
    (hZfin : Γ.HasFiniteCharacter Z) (hYfin : Γ.HasFiniteCharacter Y)
    (hroot : (C.z 0).1.initial ∉ Γ.vertexSet Y) (n : ℕ) :
    C.rawMacroVertex hZ hY hZfin hYfin hroot
        (C.streamBoundary hZ hY hZfin hYfin hroot n) =
      (C.z n).1.initial := by
  unfold rawMacroVertex streamBoundary
  rw [OmegaBlocks.rawVertex_boundary]
  exact (C.blockWalk hZfin hYfin n).head_support

/-- Every raw successor step is an edge of the auxiliary macro digraph. -/
theorem rawMacroVertex_adj
    (hZ : Γ.IsWarp Z) (hY : Γ.IsWarp Y)
    (hZfin : Γ.HasFiniteCharacter Z) (hYfin : Γ.HasFiniteCharacter Y)
    (hroot : (C.z 0).1.initial ∉ Γ.vertexSet Y) (k : ℕ) :
    MacroEdge Z Y
      (C.rawMacroVertex hZ hY hZfin hYfin hroot k)
      (C.rawMacroVertex hZ hY hZfin hYfin hroot (k + 1)) := by
  unfold rawMacroVertex
  apply OmegaBlocks.rawVertex_rel
  intro n j hj
  exact Walk.adj_get_support (C.blockWalk hZfin hYfin n) j hj

/-- Every closed local vertex interval of a macro block is read verbatim in
the raw stream. -/
theorem rawMacroVertex_block_interval
    (hZ : Γ.IsWarp Z) (hY : Γ.IsWarp Y)
    (hZfin : Γ.HasFiniteCharacter Z) (hYfin : Γ.HasFiniteCharacter Y)
    (hroot : (C.z 0).1.initial ∉ Γ.vertexSet Y)
    (n j : ℕ)
    (hj : j ≤ (C.streamBlocks hZ hY hZfin hYfin hroot).edgeLength n) :
    C.rawMacroVertex hZ hY hZfin hYfin hroot
        (C.streamBoundary hZ hY hZfin hYfin hroot n + j) =
      (C.blockWalk hZfin hYfin n).support.get ⟨j, by
        have htwo :=
          (C.streamBlocks hZ hY hZfin hYfin hroot).length_pos n
        change 2 ≤ (C.blockWalk hZfin hYfin n).support.length at htwo
        change j ≤ (C.blockWalk hZfin hYfin n).support.length - 1 at hj
        omega⟩ := by
  exact (C.streamBlocks hZ hY hZfin hYfin hroot).rawVertex_boundary_add n j hj

/-- A projected vertex belongs to only finitely many concrete macro blocks
(in fact, at most two). -/
theorem streamBlock_indices_finite
    (hZ : Γ.IsWarp Z) (hY : Γ.IsWarp Y)
    (hZfin : Γ.HasFiniteCharacter Z) (hYfin : Γ.HasFiniteCharacter Y)
    (hroot : (C.z 0).1.initial ∉ Γ.vertexSet Y) (x : V) :
    {n | x ∈ (C.streamBlocks hZ hY hZfin hYfin hroot).block n}.Finite := by
  apply OmegaBlocks.finite_of_triple_eq
  intro i hi j hj k hk
  change x ∈ (C.blockWalk hZfin hYfin i).support at hi
  change x ∈ (C.blockWalk hZfin hYfin j).support at hj
  change x ∈ (C.blockWalk hZfin hYfin k).support at hk
  exact C.block_indices_pair_stream hZ hY hZfin hYfin hroot hi hj hk

/-- Consequently every projected vertex has a finite occurrence fiber in
the raw stream, exactly the hypothesis required by chronological loop
erasure. -/
theorem rawMacroVertex_fiber_finite
    (hZ : Γ.IsWarp Z) (hY : Γ.IsWarp Y)
    (hZfin : Γ.HasFiniteCharacter Z) (hYfin : Γ.HasFiniteCharacter Y)
    (hroot : (C.z 0).1.initial ∉ Γ.vertexSet Y) (x : V) :
    {k | C.rawMacroVertex hZ hY hZfin hYfin hroot k = x}.Finite := by
  unfold rawMacroVertex
  apply OmegaBlocks.rawVertex_fiber_finite
  exact C.streamBlock_indices_finite hZ hY hZfin hYfin hroot

end MacroChain

end Alternating
end Erdos599
