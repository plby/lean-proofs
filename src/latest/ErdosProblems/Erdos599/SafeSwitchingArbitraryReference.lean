/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.SafeSwitchingAssembly

/-!
# The no-forward-sandwich lemma for arbitrary reference warps

The published safety definition allows a reference member to be a ray.
The earlier assembly theorem reduced its unique owner to a finite path by a
finite-character hypothesis.  Here the ray case is handled directly: path
subintervals are convex in the natural coordinate order of the owner ray.
-/

namespace Erdos599

open Set DirectedPath

universe u

namespace Alternating
namespace SwitchingCore
namespace ArbitraryReference

variable {V : Type u} {Gamma : DWeb V}

/-- Coordinates of a finite walk whose edges lie on an ambient ray. -/
theorem Walk.getElem_eq_ray_start_add
    {a b : V} (w : Walk Gamma.graph a b) (p : Ray Gamma.graph)
    (hE : w.edgeSet ⊆ p.edgeSet) (s : Nat) (hstart : a = p s) :
    ∀ n (hn : n ≤ w.length),
      w.support[n]'(by rw [Walk.support_length_eq]; omega) = p (s + n) := by
  intro n hn
  induction n with
  | zero =>
      have hzero :
          w.support[0]'(by rw [Walk.support_length_eq]; omega) = a :=
        (List.getElem_zero _).trans w.head_support
      exact hzero.trans (by simpa using hstart)
  | succ n ih =>
      have hnlt : n < w.length := by omega
      have hn₀ : n < w.support.length := by
        rw [Walk.support_length_eq]
        omega
      have hn₁ : n + 1 < w.support.length := by
        rw [Walk.support_length_eq]
        omega
      have hedge :
          (w.support[n]'hn₀, w.support[n + 1]'hn₁) ∈ w.edgeSet := by
        rw [Walk.mem_edgeSet_iff_exists_getVert w]
        exact ⟨n, hnlt, hn₁, rfl⟩
      obtain ⟨j, hj⟩ := hE hedge
      have hsource : w.support[n]'hn₀ = p j := congrArg Prod.fst hj
      have htarget : w.support[n + 1]'hn₁ = p (j + 1) :=
        congrArg Prod.snd hj
      have hindex : j = s + n := by
        apply p.injective
        exact hsource.symm.trans (ih (by omega))
      rw [hindex] at htarget
      simpa [Nat.add_assoc] using htarget

private theorem FinitePath.ray_edge_mem_iff
    (q : FinitePath Gamma.graph) (p : Ray Gamma.graph)
    (hsub : q.IsSubpathOf (.inr p)) (s : Nat) (hstart : q.start = p s)
    (j : Nat) :
    (p j, p (j + 1)) ∈ q.edgeSet ↔
      s ≤ j ∧ j < s + q.walk.length := by
  have hmap := Walk.getElem_eq_ray_start_add q.walk p hsub.2 s hstart
  constructor
  · intro he
    change (p j, p (j + 1)) ∈ q.walk.edgeSet at he
    rw [Walk.mem_edgeSet_iff_exists_getVert q.walk] at he
    obtain ⟨i, hi, hi₁, heq⟩ := he
    have hsource : p j = q.walk.support[i]'(by
        rw [Walk.support_length_eq]
        omega) := congrArg Prod.fst heq
    have hji : j = s + i := by
      apply p.injective
      exact hsource.trans (hmap i (by omega))
    omega
  · rintro ⟨hsj, hj⟩
    let i := j - s
    have hi : i < q.walk.length := by
      dsimp [i]
      omega
    have hi₁ : i + 1 < q.walk.support.length := by
      rw [Walk.support_length_eq]
      omega
    change (p j, p (j + 1)) ∈ q.walk.edgeSet
    rw [Walk.mem_edgeSet_iff_exists_getVert q.walk]
    refine ⟨i, hi, hi₁, ?_⟩
    apply Prod.ext
    · change p j = q.walk.support[i]
      rw [hmap i hi.le]
      dsimp [i]
      rw [Nat.add_sub_of_le hsj]
    · change p (j + 1) = q.walk.support[i + 1]
      rw [hmap (i + 1) (by omega)]
      dsimp [i]
      congr 1
      omega

private theorem Ray.apply_eq_ambient_start_add
    (q p : Ray Gamma.graph)
    (hsub : DirectedPath.Path.IsSubpathOf
      (Sum.inr q : Gamma.DPath) (Sum.inr p))
    (s : Nat) (hstart : q 0 = p s) :
    ∀ n, q n = p (s + n) := by
  intro n
  induction n with
  | zero => simpa using hstart
  | succ n ih =>
      have he : (q n, q (n + 1)) ∈ p.edgeSet := hsub.2 ⟨n, rfl⟩
      obtain ⟨j, hj⟩ := he
      have hsource : q n = p j := congrArg Prod.fst hj
      have htarget : q (n + 1) = p (j + 1) := congrArg Prod.snd hj
      have hindex : j = s + n := by
        apply p.injective
        exact hsource.symm.trans ih
      rw [hindex] at htarget
      simpa [Nat.add_assoc] using htarget

private theorem Ray.ray_edge_mem_iff
    (q p : Ray Gamma.graph)
    (hsub : DirectedPath.Path.IsSubpathOf
      (Sum.inr q : Gamma.DPath) (Sum.inr p))
    (s : Nat) (hstart : q 0 = p s) (j : Nat) :
    (p j, p (j + 1)) ∈ q.edgeSet ↔ s ≤ j := by
  have hmap := Ray.apply_eq_ambient_start_add q p hsub s hstart
  constructor
  · rintro ⟨i, heq⟩
    have hsource : p j = q i := congrArg Prod.fst heq
    have hji : j = s + i := by
      apply p.injective
      exact hsource.trans (hmap i)
    omega
  · intro hsj
    let i := j - s
    refine ⟨i, ?_⟩
    apply Prod.ext
    · change p j = q i
      rw [hmap i]
      dsimp [i]
      rw [Nat.add_sub_of_le hsj]
    · change p (j + 1) = q (i + 1)
      rw [hmap (i + 1)]
      dsimp [i]
      congr 1
      omega

/-- A subpath of a ray contains every ambient ray edge between two of its
edges. -/
private theorem Path.ray_edge_mem_of_between
    (p : Ray Gamma.graph) (q : Gamma.DPath)
    (hsub : q.IsSubpathOf (.inr p)) {i j k : Nat}
    (hi : (p i, p (i + 1)) ∈ q.edgeSet)
    (hk : (p k, p (k + 1)) ∈ q.edgeSet)
    (hij : i ≤ j) (hjk : j ≤ k) :
    (p j, p (j + 1)) ∈ q.edgeSet := by
  rcases q with q | q
  · have hstartMem : q.start ∈ p.support :=
      hsub.1 q.start_mem_support
    obtain ⟨s, hs⟩ := hstartMem
    have hstart : q.start = p s := hs.symm
    have hiPos := (FinitePath.ray_edge_mem_iff q p hsub s hstart i).1 hi
    have hkPos := (FinitePath.ray_edge_mem_iff q p hsub s hstart k).1 hk
    exact (FinitePath.ray_edge_mem_iff q p hsub s hstart j).2
      ⟨hiPos.1.trans hij, hjk.trans_lt hkPos.2⟩
  · have hstartMem : q 0 ∈ p.support := hsub.1 (q.apply_mem_support 0)
    obtain ⟨s, hs⟩ := hstartMem
    have hstart : q 0 = p s := hs.symm
    have hiPos := (Ray.ray_edge_mem_iff q p hsub s hstart i).1 hi
    exact (Ray.ray_edge_mem_iff q p hsub s hstart j).2
      (hiPos.trans hij)

/-- Convexity of an edge interval, expressed in the natural coordinates of
an ambient ray. -/
theorem IsEdgeInterval.mem_of_between_ray_positions
    {p : Ray Gamma.graph} {E : Set (V × V)}
    (hI : IsEdgeInterval E (.inr p)) {i j k : Nat}
    (hi : (p i, p (i + 1)) ∈ E) (hk : (p k, p (k + 1)) ∈ E)
    (hij : i ≤ j) (hjk : j ≤ k) :
    (p j, p (j + 1)) ∈ E := by
  rcases hI with rfl | ⟨q, hsub, rfl⟩
  · simpa using hi
  · exact Path.ray_edge_mem_of_between p q hsub hi hk hij hjk

/-- Contact coverage supplies an incoming backward edge on an arbitrary
finite-or-infinite reference owner. -/
private theorem IsSwitchingAlternating.exists_backward_edge_to_forward_target_path
    {Y : Set Gamma.DPath} {Q : AltPath Gamma.graph}
    (hAlt : IsSwitchingAlternating Y Q)
    {p : Gamma.DPath} (hpY : p ∈ Y)
    {a x : V} (hF : (a, x) ∈ Q.directionEdges .forward)
    (hxp : x ∈ p.support) :
    ∃ z, (z, x) ∈ p.edgeSet ∩ Q.directionEdges .backward := by
  have hxY : x ∈ Gamma.vertexSet Y := ⟨p, hpY, hxp⟩
  have hxF := (Q.directionEdge_endpoints hF).2
  have hxB := hAlt.contactsCovered ⟨hxF, hxY⟩
  simp only [AltPath.directionVertices, Set.mem_iUnion] at hxB
  rcases hxB with ⟨b, hbQ, hbdir, hxb⟩
  rcases hAlt.1.2.1 b hbQ hbdir with ⟨q, hqY, hbq⟩
  have hpq : q = p :=
    DWeb.IsWarp.eq_of_mem_support hAlt.1.1 hqY hpY (hbq.1 hxb) hxp
  subst q
  have hxne : x ≠ b.path.start := by
    simpa [Link.exit, hbdir] using
      Q.forward_target_backward_ne_exit hF hbQ hbdir hxb
  obtain ⟨z, hzx⟩ :=
    FinitePath.exists_edge_to_of_mem_of_ne_start b.path hxb hxne
  exact ⟨z, hbq.2 hzx, by
    simp only [AltPath.directionEdges, Set.mem_iUnion]
    exact ⟨b, hbQ, hbdir, hzx⟩⟩

private theorem IsSwitchingAlternating.exists_backward_edge_from_forward_source_path
    {Y : Set Gamma.DPath} {Q : AltPath Gamma.graph}
    (hAlt : IsSwitchingAlternating Y Q)
    {p : Gamma.DPath} (hpY : p ∈ Y)
    {x b : V} (hF : (x, b) ∈ Q.directionEdges .forward)
    (hxp : x ∈ p.support) :
    ∃ z, (x, z) ∈ p.edgeSet ∩ Q.directionEdges .backward := by
  have hxY : x ∈ Gamma.vertexSet Y := ⟨p, hpY, hxp⟩
  have hxF := (Q.directionEdge_endpoints hF).1
  have hxB := hAlt.contactsCovered ⟨hxF, hxY⟩
  simp only [AltPath.directionVertices, Set.mem_iUnion] at hxB
  rcases hxB with ⟨l, hlQ, hldir, hxl⟩
  rcases hAlt.1.2.1 l hlQ hldir with ⟨q, hqY, hlq⟩
  have hpq : q = p :=
    DWeb.IsWarp.eq_of_mem_support hAlt.1.1 hqY hpY (hlq.1 hxl) hxp
  subst q
  have hxne : x ≠ l.path.finish := by
    simpa [Link.entry, hldir] using
      Q.forward_source_backward_ne_entry hF hlQ hldir hxl
  obtain ⟨z, hxz⟩ :=
    FinitePath.exists_edge_from_of_mem_of_ne_finish l.path hxl hxne
  exact ⟨z, hlq.2 hxz, by
    simp only [AltPath.directionEdges, Set.mem_iUnion]
    exact ⟨l, hlQ, hldir, hxz⟩⟩

/-- The retained finite middle cannot lie on a ray member either. -/
private theorem IsSwitchingSafe.no_forward_retainedPath_forward_ray
    {Y : Set Gamma.DPath} {Q : AltPath Gamma.graph}
    (hSafe : IsSwitchingSafe Y Q)
    {p : Ray Gamma.graph} {r : FinitePath Gamma.graph}
    (hpY : (.inr p : Gamma.DPath) ∈ Y)
    (hrp : r.IsSubpathOf (.inr p))
    (hrne : r.start ≠ r.finish)
    (hret : r.edgeSet ⊆ familyEdges Y \ Q.directionEdges .backward)
    {a b : V}
    (hIn : (a, r.start) ∈ Q.directionEdges .forward)
    (hOut : (r.finish, b) ∈ Q.directionEdges .forward) : False := by
  have hAlt : IsSwitchingAlternating Y Q := hSafe.isSwitchingAlternating
  obtain ⟨z, hzP, hzB⟩ :=
    IsSwitchingAlternating.exists_backward_edge_to_forward_target_path
      hAlt hpY hIn (hrp.1 r.start_mem_support)
  obtain ⟨w, hwP, hwB⟩ :=
    IsSwitchingAlternating.exists_backward_edge_from_forward_source_path
      hAlt hpY hOut (hrp.1 r.finish_mem_support)
  obtain ⟨t, hrt⟩ :=
    FinitePath.exists_edge_from_of_mem_of_ne_finish r
      r.start_mem_support hrne
  have hrtRet := hret hrt
  obtain ⟨iz, hiz⟩ := hzP
  obtain ⟨ir, hir⟩ := hrp.2 hrt
  obtain ⟨iw, hiw⟩ := hwP
  have hirEq : ir = iz + 1 := by
    apply p.injective
    exact (congrArg Prod.fst hir).symm.trans (congrArg Prod.snd hiz)
  have hfinishMap : r.finish = p (ir + r.walk.length) := by
    have hmap := Walk.getElem_eq_ray_start_add r.walk p hrp.2 ir
      (congrArg Prod.fst hir)
    simpa [Walk.getElem_length_eq_end] using hmap r.walk.length le_rfl
  have hiwEq : ir + r.walk.length = iw := by
    apply p.injective
    exact hfinishMap.symm.trans (congrArg Prod.fst hiw)
  have hzI : (p iz, p (iz + 1)) ∈
      Q.directionEdges .backward ∩ p.edgeSet := by
    rw [← hiz]
    exact ⟨hzB, ⟨iz, hiz⟩⟩
  have hwI : (p iw, p (iw + 1)) ∈
      Q.directionEdges .backward ∩ p.edgeSet := by
    rw [← hiw]
    exact ⟨hwB, ⟨iw, hiw⟩⟩
  have hrtI : (p ir, p (ir + 1)) ∈
      Q.directionEdges .backward ∩ p.edgeSet :=
    IsEdgeInterval.mem_of_between_ray_positions
      (hSafe.1.2.1 (.inr p) hpY) hzI hwI (by omega) (by omega)
  apply hrtRet.2
  rw [hir]
  exact hrtI.1

/-- Source safeness forbids a forward--retained--forward sandwich for an
arbitrary reference warp; no finite-character hypothesis is needed. -/
theorem isSwitchingSafe_noForwardSandwich
    {Y : Set Gamma.DPath} {Q : AltPath Gamma.graph}
    (hSafe : IsSwitchingSafe Y Q) :
    NoForwardSandwich (D := Gamma.graph)
      (familyEdges Y \ Q.directionEdges .backward)
      (Q.directionEdges .forward) := by
  intro r hrne hrB a b hIn hOut
  have hfrag := finitePath_isFragmentOf_of_edgeSet_subset_familyEdges
    hSafe.1.1.1 r hrne (hrB.trans Set.diff_subset)
  rcases hfrag with ⟨p, hpY, hrp⟩
  rcases p with p | p
  · exact hSafe.no_forward_retainedPath_forward hpY hrp hrne hrB hIn hOut
  · exact IsSwitchingSafe.no_forward_retainedPath_forward_ray hSafe
      hpY hrp hrne hrB hIn hOut

#print axioms isSwitchingSafe_noForwardSandwich

end ArbitraryReference
end SwitchingCore
end Alternating
end Erdos599
