/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.SafeSwitching
import ErdosProblems.Erdos599.CyclowarpDecomposition

/-!
# Assembly of safe switching

This file packages the last relation-theoretic step in the proof of
Aharoni--Berger Lemma 4.9.  The source-specific part of the argument shows
that the switched relation of a safe alternating path has neither a directed
cycle nor a ray in either direction.  A locally bi-unique relation with those
three properties is the edge set of a finite-character warp.  The explicitly
retained isolated vertices are then added as singleton paths.
-/

namespace Erdos599
namespace Alternating

open Set DirectedPath

universe u

variable {V : Type u} {Gamma : DWeb V}

namespace RelationDecomposition

/-- The vertices incident with a directed edge relation. -/
def IncidentVertices (E : Set (V × V)) : Set V :=
  {x | ∃ y, (x, y) ∈ E ∨ (y, x) ∈ E}

theorem incident_of_edge_left {E : Set (V × V)} {x y : V}
    (hxy : (x, y) ∈ E) : x ∈ IncidentVertices E :=
  ⟨y, Or.inl hxy⟩

theorem incident_of_edge_right {E : Set (V × V)} {x y : V}
    (hxy : (x, y) ∈ E) : y ∈ IncidentVertices E :=
  ⟨x, Or.inr hxy⟩

namespace ForwardOrientation

variable {D : Digraph V} (O : ForwardOrientation D)

theorem orbit_mem_carrier_of_root_alive {r : V} (hr : O.IsRoot r)
    {n : ℕ} (h : O.Alive r n) : O.orbit r n ∈ O.carrier := by
  cases n with
  | zero => simpa using hr.1
  | succ n =>
      exact (O.endpoints_mem _ (O.orbit_edge h)).2

theorem rootPath_support_subset_carrier (r : O.Root) :
    (O.rootPath r).support ⊆ O.carrier := by
  intro x hx
  simp only [rootPath] at hx
  split at hx <;> rename_i hstop
  · rcases hx with ⟨n, rfl⟩
    exact O.orbit_mem_carrier_of_root_alive r.2 (fun k _ ↦ hstop k)
  · change x ∈ (O.orbitWalk r.1 (O.stoppingIndex hstop)
        (O.alive_stoppingIndex hstop)).support at hx
    rw [O.orbitWalk_support] at hx
    simp only [List.mem_ofFn] at hx
    rcases hx with ⟨i, rfl⟩
    exact O.orbit_mem_carrier_of_root_alive r.2
      (O.alive_mono (O.alive_stoppingIndex hstop) i.is_le)

end ForwardOrientation

namespace DWeb

variable (G : DWeb V)

/-- Singleton paths supported on a specified vertex set. -/
def isolatedPaths (I : Set V) : Set G.DPath :=
  G.trivialPath '' I

theorem isolatedPaths_isWarp (I : Set V) : G.IsWarp (isolatedPaths G I) := by
  intro p hp q hq hpq
  rcases hp with ⟨x, hx, rfl⟩
  rcases hq with ⟨y, hy, rfl⟩
  change Disjoint (G.trivialPath x).support (G.trivialPath y).support
  rw [G.support_trivialPath, G.support_trivialPath]
  apply Set.disjoint_singleton.2
  intro hxy
  subst y
  exact hpq rfl

theorem familyEdges_isolatedPaths (I : Set V) :
    familyEdges (isolatedPaths G I) = ∅ := by
  ext e
  simp only [familyEdges, isolatedPaths, Set.mem_iUnion, Set.mem_image,
    Set.mem_empty_iff_false, iff_false]
  rintro ⟨p, ⟨x, hx, rfl⟩, he⟩
  simpa [DWeb.trivialPath, Path.trivial, FinitePath.trivial,
    FinitePath.edgeSet, Walk.edgeSet] using he

theorem isolatedVertices_isolatedPaths (I : Set V) :
    isolatedVertices (isolatedPaths G I) = I := by
  ext x
  constructor
  · rintro ⟨y, hy, heq⟩
    have hxy := congrArg Path.initial heq
    have : x = y := by simpa using hxy.symm
    simpa [this] using hy
  · intro hx
    exact ⟨x, hx, rfl⟩

theorem hasFiniteCharacter_isolatedPaths (I : Set V) :
    G.HasFiniteCharacter (isolatedPaths G I) := by
  rintro p ⟨x, hx, rfl⟩
  exact ⟨FinitePath.trivial G.graph x, rfl⟩

theorem familyEdges_union_local (P T : Set G.DPath) :
    familyEdges (P ∪ T) = familyEdges P ∪ familyEdges T := by
  ext e
  simp only [familyEdges, Set.mem_iUnion, Set.mem_union]
  constructor
  · rintro ⟨p, hp | hp, he⟩
    · exact Or.inl ⟨p, hp, he⟩
    · exact Or.inr ⟨p, hp, he⟩
  · rintro (⟨p, hp, he⟩ | ⟨p, hp, he⟩)
    · exact ⟨p, Or.inl hp, he⟩
    · exact ⟨p, Or.inr hp, he⟩

/-- An orientation whose carrier consists of incident vertices has no
singleton root path. -/
theorem rootPaths_no_isolated
    (O : ForwardOrientation G.graph)
    (hcarrier : O.carrier = IncidentVertices O.edge) :
    isolatedVertices O.rootPaths = ∅ := by
  ext x
  simp only [isolatedVertices, Set.mem_setOf_eq, Set.mem_empty_iff_false,
    iff_false]
  rintro ⟨r, heq⟩
  have hrx : r.1 = x := by
    have := congrArg Path.initial heq
    simpa [O.rootPath_initial] using this
  have hrinc : r.1 ∈ IncidentVertices O.edge := by
    rw [← hcarrier]
    exact r.2.1
  rcases hrinc with ⟨y, hry | hyr⟩
  · have he : (r.1, y) ∈ (O.rootPath r).edgeSet := by
      have hcomp : O.component r.1 = r.1 := O.root_label r.2.1 r.2.2
      simpa [hcomp] using O.rootPath_contains_edge hry
    rw [heq] at he
    simpa [DWeb.trivialPath, Path.trivial, FinitePath.trivial,
      FinitePath.edgeSet, Walk.edgeSet] using he
  · have hrpred : ForwardOrientation.HasPredecessor O.edge r.1 :=
      ⟨y, hyr⟩
    have hdepth : O.depth r.1 = 0 := r.2.2
    have hrootNoPred : ¬ ForwardOrientation.HasPredecessor O.edge r.1 := by
      intro hp
      rcases hp with ⟨z, hzr⟩
      have hstep := O.depth_step hzr
      omega
    exact hrootNoPred hrpred

/-- Add the prescribed isolated vertices to the path decomposition supplied
by a forward orientation. -/
theorem exists_finiteWarp_realizing_orientation_with_isolated
    (E : Set (V × V)) (I : Set V)
    (O : ForwardOrientation G.graph)
    (hOE : O.edge = E)
    (hcarrier : O.carrier = IncidentVertices O.edge)
    (hnoRay : ¬ ContainsDirectedRay E)
    (hI : ∀ x ∈ I, ∀ y, (x, y) ∉ E ∧ (y, x) ∉ E) :
    ∃ W : Set G.DPath,
      G.IsWarp W ∧ familyEdges W = E ∧
        isolatedVertices W = I ∧ G.HasFiniteCharacter W := by
  let P : Set G.DPath := O.rootPaths
  let T : Set G.DPath := isolatedPaths G I
  have hPwarp : G.IsWarp P := by
    exact O.rootPaths_pairwiseDisjoint
  have hPE : familyEdges P = E := by
    change O.rootPathEdges = E
    rw [O.rootPathEdges_eq, hOE]
  have hPfin : G.HasFiniteCharacter P := by
    apply forwardOrientation_rootPaths_finite_of_noRay G O
    simpa [hOE] using hnoRay
  have hcross : ∀ p ∈ P, ∀ q ∈ T, Disjoint p.support q.support := by
    intro p hp q hq
    rcases hp with ⟨r, rfl⟩
    rcases hq with ⟨x, hxI, rfl⟩
    rw [G.support_trivialPath, Set.disjoint_singleton_right]
    intro hxr
    have hxcarrier : x ∈ O.carrier := O.rootPath_support_subset_carrier r hxr
    rw [hcarrier] at hxcarrier
    rcases hxcarrier with ⟨y, hxy | hyx⟩
    · exact (hI x hxI y).1 (hOE ▸ hxy)
    · exact (hI x hxI y).2 (hOE ▸ hyx)
  refine ⟨P ∪ T, ?_, ?_, ?_, ?_⟩
  · intro p hp q hq hpq
    rcases hp with hp | hp <;> rcases hq with hq | hq
    · exact hPwarp hp hq hpq
    · exact hcross p hp q hq
    · exact (hcross q hq p hp).symm
    · exact isolatedPaths_isWarp G I hp hq hpq
  · rw [familyEdges_union_local, hPE, familyEdges_isolatedPaths G I,
      Set.union_empty]
  · ext x
    simp only [isolatedVertices, Set.mem_setOf_eq, Set.mem_union]
    constructor
    · intro hx
      rcases hx with hx | hx
      · have hnone : x ∈ (∅ : Set V) := by
          rw [← rootPaths_no_isolated G O hcarrier]
          exact hx
        exact hnone.elim
      · exact (Set.ext_iff.mp (isolatedVertices_isolatedPaths G I) x).mp hx
    · intro hx
      exact Or.inr
        ((Set.ext_iff.mp (isolatedVertices_isolatedPaths G I) x).mpr hx)
  · intro p hp
    rcases hp with hp | hp
    · exact hPfin hp
    · exact hasFiniteCharacter_isolatedPaths G I hp

/-- A locally bi-unique relation without directed cycles or rays in either
orientation, together with disjoint isolated vertices, has an exact
finite-character warp realization. -/
theorem exists_finiteWarp_realizing_biUnique
    (E : Set (V × V)) (I : Set V)
    (hgraph : E ⊆ {e | G.graph.Adj e.1 e.2})
    (hunique : Relator.BiUnique (fun x y ↦ (x, y) ∈ E))
    (hcycle : ¬ ContainsDirectedCycle E)
    (hRay : ¬ ContainsDirectedRay E)
    (hReverseRay : ¬ ContainsReverseDirectedRay E)
    (hI : ∀ x ∈ I, ∀ y, (x, y) ∉ E ∧ (y, x) ∉ E) :
    ∃ W : Set G.DPath,
      G.IsWarp W ∧ familyEdges W = E ∧
        isolatedVertices W = I ∧ G.HasFiniteCharacter W := by
  let carrier := IncidentVertices E
  have hendpoints : ∀ e ∈ E, e.1 ∈ carrier ∧ e.2 ∈ carrier := by
    rintro ⟨x, y⟩ hxy
    exact ⟨incident_of_edge_left hxy, incident_of_edge_right hxy⟩
  let hwf : WellFounded (fun x y ↦ (x, y) ∈ E) :=
    ForwardOrientation.predecessor_wellFounded E hcycle hReverseRay
  let O : ForwardOrientation G.graph :=
    { edge := E
      carrier := carrier
      depth := ForwardOrientation.wellFoundedDepth E hwf
      component := ForwardOrientation.wellFoundedRoot E hwf
      edge_in_graph := hgraph
      endpoints_mem := hendpoints
      out_unique := fun hxy hxz ↦ hunique.2 hxy hxz
      in_unique := fun hxz hyz ↦ hunique.1 hxz hyz
      depth_step := fun hxy ↦
        ForwardOrientation.wellFoundedDepth_step E hunique hwf hxy
      component_step := fun hxy ↦
        ForwardOrientation.wellFoundedRoot_step E hunique hwf hxy
      root_label := fun _hx hdepth ↦
        ForwardOrientation.wellFoundedRoot_eq_self_of_depth_eq_zero E hwf hdepth
      predecessor := by
        intro x _hx hpos
        have hne : ForwardOrientation.wellFoundedDepth E hwf x ≠ 0 :=
          Nat.ne_of_gt hpos
        exact Classical.byContradiction fun hnot ↦
          hne ((ForwardOrientation.wellFoundedDepth_eq_zero_iff E hwf x).mpr hnot) }
  have hOE : O.edge = E := rfl
  apply exists_finiteWarp_realizing_orientation_with_isolated G E I O hOE
  · rfl
  · exact hRay
  · exact hI

end DWeb

end RelationDecomposition

/-! ## Finite segments of rays and cycles -/

namespace SwitchingCore

variable {D : Digraph V}

/-- The first `n` edges of a directed ray, bundled as a walk. -/
def rayPrefixWalk (r : Ray D) : (n : ℕ) → Walk D (r 0) (r n)
  | 0 => .nil
  | n + 1 => (rayPrefixWalk r n).concat (r.adj_succ n)

@[simp]
theorem rayPrefixWalk_support (r : Ray D) (n : ℕ) :
    (rayPrefixWalk r n).support = List.ofFn (fun i : Fin (n + 1) ↦ r i) := by
  induction n with
  | zero => simp [rayPrefixWalk]
  | succ n ih =>
      rw [rayPrefixWalk, Walk.support_concat, ih]
      rw [@List.ofFn_succ_last V (n + 1)
        (fun i : Fin ((n + 1) + 1) ↦ r i)]
      congr 1 <;> simp

theorem rayPrefixWalk_isPath (r : Ray D) (n : ℕ) :
    (rayPrefixWalk r n).IsPath := by
  rw [Walk.isPath_iff, rayPrefixWalk_support]
  exact List.nodup_ofFn.mpr fun i j hij ↦ Fin.ext (r.injective hij)

/-- The first `n` edges of a ray, as a finite path. -/
def rayPrefixPath (r : Ray D) (n : ℕ) : FinitePath D where
  start := r 0
  finish := r n
  walk := rayPrefixWalk r n
  isPath := rayPrefixWalk_isPath r n

theorem rayPrefixPath_edgeSet (r : Ray D) (n : ℕ) :
    (rayPrefixPath r n).edgeSet =
      {e | ∃ k < n, e = (r k, r (k + 1))} := by
  induction n with
  | zero => simp [rayPrefixPath, rayPrefixWalk, FinitePath.edgeSet,
      Walk.edgeSet]
  | succ n ih =>
      change (rayPrefixWalk r (n + 1)).edgeSet = _
      have ih' : (rayPrefixWalk r n).edgeSet =
          {e | ∃ k < n, e = (r k, r (k + 1))} := by
        simpa [rayPrefixPath, FinitePath.edgeSet] using ih
      rw [rayPrefixWalk, RelationComponents.walkEdgeSetConcatRC, ih']
      ext e
      simp only [Set.mem_union, Set.mem_setOf_eq, Set.mem_singleton_iff]
      constructor
      · rintro (⟨k, hk, rfl⟩ | rfl)
        · exact ⟨k, hk.trans (Nat.lt_succ_self n), rfl⟩
        · exact ⟨n, Nat.lt_succ_self n, rfl⟩
      · rintro ⟨k, hk, rfl⟩
        by_cases hkn : k < n
        · exact Or.inl ⟨k, hkn, rfl⟩
        · have : k = n := by omega
          subst k
          exact Or.inr rfl

/-- A finite segment of a ray, beginning at index `i` and using `n` edges. -/
def raySegmentPath (r : Ray D) (i n : ℕ) : FinitePath D :=
  rayPrefixPath (r.tail i) n

@[simp] theorem raySegmentPath_start (r : Ray D) (i n : ℕ) :
    (raySegmentPath r i n).start = r i := by
  simp [raySegmentPath, rayPrefixPath, Ray.initial]

@[simp] theorem raySegmentPath_finish (r : Ray D) (i n : ℕ) :
    (raySegmentPath r i n).finish = r (i + n) := by
  rfl

theorem raySegmentPath_edgeSet (r : Ray D) (i n : ℕ) :
    (raySegmentPath r i n).edgeSet =
      {e | ∃ k < n, e = (r (i + k), r (i + k + 1))} := by
  rw [raySegmentPath, rayPrefixPath_edgeSet]
  ext e
  simp only [Set.mem_setOf_eq]
  constructor
  · rintro ⟨k, hk, rfl⟩
    exact ⟨k, hk, by simp [Nat.add_assoc]⟩
  · rintro ⟨k, hk, rfl⟩
    exact ⟨k, hk, by simp [Nat.add_assoc]⟩

theorem raySegmentPath_nontrivial (r : Ray D) {i n : ℕ} (hn : 0 < n) :
    (raySegmentPath r i n).start ≠ (raySegmentPath r i n).finish := by
  simp only [raySegmentPath_start, raySegmentPath_finish]
  intro h
  have := r.injective h
  omega

theorem Walk.edgeSet_reverse_eq_swap_image {a b : V} (p : Walk D a b) :
    p.reverse.edgeSet = Prod.swap '' p.edgeSet := by
  induction p with
  | nil => simp [Walk.reverse, Walk.edgeSet]
  | @cons a b c h p ih =>
      rw [Walk.reverse, RelationComponents.walkEdgeSetConcatRC, ih]
      ext e
      simp only [Set.mem_union, Set.mem_singleton_iff, Set.mem_image,
        Walk.edgeSet_cons]
      constructor
      · rintro (he | rfl)
        · rcases he with ⟨z, hz, rfl⟩
          exact ⟨z, Or.inr hz, rfl⟩
        · exact ⟨(a, b), Or.inl rfl, rfl⟩
      · rintro ⟨z, hz | hz, rfl⟩
        · have hz' : z = (a, b) := hz
          subst z
          exact Or.inr rfl
        · exact Or.inl ⟨z, hz, rfl⟩

theorem FinitePath.mem_edgeSet_reverse_iff (p : FinitePath D)
    {x y : V} : (x, y) ∈ p.reverse.edgeSet ↔ (y, x) ∈ p.edgeSet := by
  rw [FinitePath.edgeSet, FinitePath.reverse, Walk.edgeSet_reverse_eq_swap_image]
  constructor
  · rintro ⟨z, hz, he⟩
    have hzy : z.2 = x := congrArg Prod.fst he
    have hzx : z.1 = y := congrArg Prod.snd he
    have hzEq : z = (y, x) := Prod.ext hzx hzy
    change (y, x) ∈ p.walk.edgeSet
    exact hzEq ▸ hz
  · intro h
    exact ⟨(y, x), h, rfl⟩

/-- A finite walk following a reverse-directed ray from index `n` back to
index zero. -/
def reverseRayPrefixWalk (R : DirectedRay V)
    (hAdj : ∀ n, D.Adj (R.vertex (n + 1)) (R.vertex n)) :
    (n : ℕ) → Walk D (R.vertex n) (R.vertex 0)
  | 0 => .nil
  | n + 1 => .cons (hAdj n) (reverseRayPrefixWalk R hAdj n)

@[simp]
theorem reverseRayPrefixWalk_support (R : DirectedRay V)
    (hAdj : ∀ n, D.Adj (R.vertex (n + 1)) (R.vertex n)) (n : ℕ) :
    (reverseRayPrefixWalk R hAdj n).support =
      (List.ofFn (fun i : Fin (n + 1) ↦ R.vertex i)).reverse := by
  induction n with
  | zero => simp [reverseRayPrefixWalk]
  | succ n ih =>
      rw [reverseRayPrefixWalk, Walk.support_cons, ih]
      rw [@List.ofFn_succ_last V (n + 1)
        (fun i : Fin ((n + 1) + 1) ↦ R.vertex i)]
      simp

theorem reverseRayPrefixWalk_isPath (R : DirectedRay V)
    (hAdj : ∀ n, D.Adj (R.vertex (n + 1)) (R.vertex n)) (n : ℕ) :
    (reverseRayPrefixWalk R hAdj n).IsPath := by
  rw [Walk.isPath_iff, reverseRayPrefixWalk_support, List.nodup_reverse]
  exact List.nodup_ofFn.mpr fun i j hij ↦ Fin.ext (R.injective hij)

def reverseRayPrefixPath (R : DirectedRay V)
    (hAdj : ∀ n, D.Adj (R.vertex (n + 1)) (R.vertex n))
    (n : ℕ) : FinitePath D where
  start := R.vertex n
  finish := R.vertex 0
  walk := reverseRayPrefixWalk R hAdj n
  isPath := reverseRayPrefixWalk_isPath R hAdj n

theorem reverseRayPrefixPath_edgeSet (R : DirectedRay V)
    (hAdj : ∀ n, D.Adj (R.vertex (n + 1)) (R.vertex n)) (n : ℕ) :
    (reverseRayPrefixPath R hAdj n).edgeSet =
      {e | ∃ k < n, e = (R.vertex (k + 1), R.vertex k)} := by
  induction n with
  | zero => simp [reverseRayPrefixPath, reverseRayPrefixWalk,
      FinitePath.edgeSet, Walk.edgeSet]
  | succ n ih =>
      change (reverseRayPrefixWalk R hAdj (n + 1)).edgeSet = _
      have ih' : (reverseRayPrefixWalk R hAdj n).edgeSet =
          {e | ∃ k < n, e = (R.vertex (k + 1), R.vertex k)} := by
        simpa [reverseRayPrefixPath, FinitePath.edgeSet] using ih
      rw [reverseRayPrefixWalk, Walk.edgeSet_cons, ih']
      ext e
      simp only [Set.mem_union, Set.mem_singleton_iff, Set.mem_setOf_eq]
      constructor
      · rintro (rfl | ⟨k, hk, rfl⟩)
        · exact ⟨n, Nat.lt_succ_self n, rfl⟩
        · exact ⟨k, hk.trans (Nat.lt_succ_self n), rfl⟩
      · rintro ⟨k, hk, rfl⟩
        by_cases hkn : k = n
        · subst k
          exact Or.inl rfl
        · exact Or.inr ⟨k, by omega, rfl⟩

/-- The reverse-oriented segment from index `i+n` down to index `i`. -/
def reverseRaySegmentPath (R : DirectedRay V)
    (hAdj : ∀ n, D.Adj (R.vertex (n + 1)) (R.vertex n))
    (i n : ℕ) : FinitePath D :=
  reverseRayPrefixPath
    ⟨fun k ↦ R.vertex (i + k), fun _ _ h ↦
      Nat.add_left_cancel (R.injective h)⟩
    (fun k ↦ by simpa [Nat.add_assoc] using hAdj (i + k)) n

@[simp]
theorem reverseRaySegmentPath_start (R : DirectedRay V)
    (hAdj : ∀ n, D.Adj (R.vertex (n + 1)) (R.vertex n))
    (i n : ℕ) :
    (reverseRaySegmentPath R hAdj i n).start = R.vertex (i + n) := by
  rfl

@[simp]
theorem reverseRaySegmentPath_finish (R : DirectedRay V)
    (hAdj : ∀ n, D.Adj (R.vertex (n + 1)) (R.vertex n))
    (i n : ℕ) :
    (reverseRaySegmentPath R hAdj i n).finish = R.vertex i := by
  simp [reverseRaySegmentPath, reverseRayPrefixPath]

theorem reverseRaySegmentPath_edgeSet (R : DirectedRay V)
    (hAdj : ∀ n, D.Adj (R.vertex (n + 1)) (R.vertex n))
    (i n : ℕ) :
    (reverseRaySegmentPath R hAdj i n).edgeSet =
      {e | ∃ k < n,
        e = (R.vertex (i + k + 1), R.vertex (i + k))} := by
  rw [reverseRaySegmentPath, reverseRayPrefixPath_edgeSet]
  ext e
  simp only [Set.mem_setOf_eq]
  constructor <;> rintro ⟨k, hk, rfl⟩ <;>
    exact ⟨k, hk, by simp [Nat.add_assoc]⟩

theorem reverseRaySegmentPath_nontrivial (R : DirectedRay V)
    (hAdj : ∀ n, D.Adj (R.vertex (n + 1)) (R.vertex n))
    {i n : ℕ} (hn : 0 < n) :
    (reverseRaySegmentPath R hAdj i n).start ≠
      (reverseRaySegmentPath R hAdj i n).finish := by
  simp only [reverseRaySegmentPath_start, reverseRaySegmentPath_finish]
  intro h
  have := R.injective h
  omega

/-! ## Finite segments of a directed cycle -/

private theorem addMod_injective {L s : ℕ} (hL : 0 < L) (hs : s < L) :
    Function.Injective
      (fun i : Fin L =>
        (⟨(s + i.1) % L, Nat.mod_lt _ hL⟩ : Fin L)) := by
  intro i j hij
  apply Fin.ext
  have hm := congrArg Fin.val hij
  change (s + i.1) % L = (s + j.1) % L at hm
  have hi2 : s + i.1 < L * 2 := by omega
  have hj2 : s + j.1 < L * 2 := by omega
  by_cases hi : s + i.1 < L <;> by_cases hj : s + j.1 < L
  · rw [Nat.mod_eq_of_lt hi, Nat.mod_eq_of_lt hj] at hm
    omega
  · have hsubj : s + j.1 - L < L := by omega
    rw [Nat.mod_eq_of_lt hi, Nat.mod_eq_sub_mod (Nat.le_of_not_gt hj),
      Nat.mod_eq_of_lt hsubj] at hm
    omega
  · have hsubi : s + i.1 - L < L := by omega
    rw [Nat.mod_eq_sub_mod (Nat.le_of_not_gt hi),
      Nat.mod_eq_of_lt hsubi, Nat.mod_eq_of_lt hj] at hm
    omega
  · have hsubi : s + i.1 - L < L := by omega
    have hsubj : s + j.1 - L < L := by omega
    rw [Nat.mod_eq_sub_mod (Nat.le_of_not_gt hi),
      Nat.mod_eq_of_lt hsubi,
      Nat.mod_eq_sub_mod (Nat.le_of_not_gt hj),
      Nat.mod_eq_of_lt hsubj] at hm
    omega

/-- Rotate the cyclic indexing so that `s` becomes index zero. -/
private def rotateCycle (C : DirectedCycle V) (s : Fin C.length) :
    DirectedCycle V where
  length := C.length
  positive := C.positive
  vertex i := C.vertex
    ⟨(s.1 + i.1) % C.length, Nat.mod_lt _ C.positive⟩
  injective := fun _ _ hij =>
    addMod_injective C.positive s.2 (C.injective hij)

private theorem rotateCycle_next (C : DirectedCycle V) (s i : Fin C.length) :
    (rotateCycle C s).vertex ((rotateCycle C s).next i) =
      C.vertex (C.next
        ⟨(s.1 + i.1) % C.length, Nat.mod_lt _ C.positive⟩) := by
  apply congrArg C.vertex
  apply Fin.ext
  simp [rotateCycle, DirectedCycle.next, Nat.add_mod_mod,
    Nat.mod_add_mod, Nat.add_assoc]

private theorem rotateCycle_edge_at (C : DirectedCycle V)
    (s i : Fin C.length) :
    ((rotateCycle C s).vertex i,
        (rotateCycle C s).vertex ((rotateCycle C s).next i)) =
      (C.vertex ⟨(s.1 + i.1) % C.length, Nat.mod_lt _ C.positive⟩,
        C.vertex (C.next
          ⟨(s.1 + i.1) % C.length, Nat.mod_lt _ C.positive⟩)) := by
  apply Prod.ext
  · rfl
  · exact rotateCycle_next C s i

private theorem rotateCycle_edgeSet_subset (C : DirectedCycle V)
    (s : Fin C.length) :
    (rotateCycle C s).EdgeSet ⊆ C.EdgeSet := by
  rintro _ ⟨i, rfl⟩
  let i' : Fin C.length := ⟨i.1, by simpa [rotateCycle] using i.2⟩
  refine ⟨⟨(s.1 + i'.1) % C.length, Nat.mod_lt _ C.positive⟩, ?_⟩
  apply Prod.ext
  · rfl
  · exact rotateCycle_next C s i'

/-- The first `n` edges of a directed cycle, before returning to its initial
vertex.  The strict bound makes its vertex support simple. -/
private def cyclePrefixWalk (C : DirectedCycle V)
    (hAdj : ∀ i, D.Adj (C.vertex i) (C.vertex (C.next i))) :
    (n : ℕ) → (hn : n < C.length) →
      Walk D (C.vertex ⟨0, C.positive⟩) (C.vertex ⟨n, hn⟩)
  | 0, _ => .nil
  | n + 1, hn =>
      (cyclePrefixWalk C hAdj n (by omega)).concat (by
        have hnext : C.next (⟨n, by omega⟩ : Fin C.length) =
            ⟨n + 1, hn⟩ := by
          apply Fin.ext
          exact Nat.mod_eq_of_lt hn
        simpa [hnext] using hAdj (⟨n, by omega⟩ : Fin C.length))

@[simp]
private theorem cyclePrefixWalk_support (C : DirectedCycle V)
    (hAdj : ∀ i, D.Adj (C.vertex i) (C.vertex (C.next i)))
    (n : ℕ) (hn : n < C.length) :
    (cyclePrefixWalk C hAdj n hn).support =
      List.ofFn (fun i : Fin (n + 1) =>
        C.vertex ⟨i.1, by omega⟩) := by
  induction n with
  | zero => simp [cyclePrefixWalk]
  | succ n ih =>
      rw [cyclePrefixWalk, Walk.support_concat, ih]
      rw [@List.ofFn_succ_last V (n + 1)
        (fun i : Fin ((n + 1) + 1) =>
          C.vertex ⟨i.1, by omega⟩)]
      congr 1 <;> simp

private theorem cyclePrefixWalk_isPath (C : DirectedCycle V)
    (hAdj : ∀ i, D.Adj (C.vertex i) (C.vertex (C.next i)))
    (n : ℕ) (hn : n < C.length) :
    (cyclePrefixWalk C hAdj n hn).IsPath := by
  rw [Walk.isPath_iff, cyclePrefixWalk_support]
  apply List.nodup_ofFn.mpr
  intro i j hij
  have hc : (⟨i.1, by omega⟩ : Fin C.length) =
      ⟨j.1, by omega⟩ := C.injective hij
  have hv :
      (⟨i.1, by omega⟩ : Fin C.length).val =
        (⟨j.1, by omega⟩ : Fin C.length).val :=
    congrArg (fun z : Fin C.length => z.val) hc
  exact Fin.ext hv

private def cyclePrefixPath (C : DirectedCycle V)
    (hAdj : ∀ i, D.Adj (C.vertex i) (C.vertex (C.next i)))
    (n : ℕ) (hn : n < C.length) : FinitePath D where
  start := C.vertex ⟨0, C.positive⟩
  finish := C.vertex ⟨n, hn⟩
  walk := cyclePrefixWalk C hAdj n hn
  isPath := cyclePrefixWalk_isPath C hAdj n hn

private theorem cyclePrefixPath_edgeSet (C : DirectedCycle V)
    (hAdj : ∀ i, D.Adj (C.vertex i) (C.vertex (C.next i)))
    (n : ℕ) (hn : n < C.length) :
    (cyclePrefixPath C hAdj n hn).edgeSet =
      {e | ∃ i : Fin C.length, i.1 < n ∧ e =
        (C.vertex i, C.vertex (C.next i))} := by
  induction n with
  | zero => simp [cyclePrefixPath, cyclePrefixWalk, FinitePath.edgeSet,
      Walk.edgeSet]
  | succ n ih =>
      change (cyclePrefixWalk C hAdj (n + 1) hn).edgeSet = _
      have ih' : (cyclePrefixWalk C hAdj n (by omega)).edgeSet =
          {e | ∃ i : Fin C.length, i.1 < n ∧ e =
            (C.vertex i, C.vertex (C.next i))} := by
        simpa [cyclePrefixPath, FinitePath.edgeSet] using ih (by omega)
      rw [cyclePrefixWalk, RelationComponents.walkEdgeSetConcatRC, ih']
      ext e
      simp only [Set.mem_union, Set.mem_setOf_eq, Set.mem_singleton_iff]
      constructor
      · rintro (⟨i, hi, rfl⟩ | rfl)
        · exact ⟨i, by omega, rfl⟩
        · refine ⟨⟨n, by omega⟩, Nat.lt_succ_self n, ?_⟩
          have hnext : C.next (⟨n, by omega⟩ : Fin C.length) =
              ⟨n + 1, hn⟩ := by
            apply Fin.ext
            exact Nat.mod_eq_of_lt hn
          rw [hnext]
      · rintro ⟨i, hi, rfl⟩
        by_cases hin : i.1 < n
        · exact Or.inl ⟨i, hin, rfl⟩
        · have hiv : i.1 = n := by omega
          have hieq : i = ⟨n, by omega⟩ := Fin.ext hiv
          rw [hieq]
          right
          have hnext : C.next (⟨n, by omega⟩ : Fin C.length) =
              ⟨n + 1, hn⟩ := by
            apply Fin.ext
            exact Nat.mod_eq_of_lt hn
          rw [hnext]

private theorem cyclePrefixPath_nontrivial (C : DirectedCycle V)
    (hAdj : ∀ i, D.Adj (C.vertex i) (C.vertex (C.next i)))
    {n : ℕ} (hn : n < C.length) (hnpos : 0 < n) :
    (cyclePrefixPath C hAdj n hn).start ≠
      (cyclePrefixPath C hAdj n hn).finish := by
  intro h
  have hi : (⟨0, C.positive⟩ : Fin C.length) = ⟨n, hn⟩ :=
    C.injective h
  have hv := congrArg Fin.val hi
  change 0 = n at hv
  omega

/-! ## A two-colour path cannot alternate twice across a retained block -/

/-- No nonempty finite `B`-path is bracketed by `F`-edges. -/
def NoForwardSandwich (B F : Set (V × V)) : Prop :=
  ∀ (p : FinitePath D), p.start ≠ p.finish → p.edgeSet ⊆ B →
    ∀ a b, (a, p.start) ∈ F → (p.finish, b) ∈ F → False

/-- The finite cyclic analogue of the monochromatic-tail argument: a mixed
cycle would contain a nonempty block of `B`-edges bracketed by `F`-edges. -/
theorem union_not_containsDirectedCycle
    (B F : Set (V × V))
    (hgraph : B ∪ F ⊆ {e | D.Adj e.1 e.2})
    (hdisj : Disjoint B F)
    (hno : NoForwardSandwich (D := D) B F)
    (hB : ¬ ContainsDirectedCycle B)
    (hF : ¬ ContainsDirectedCycle F) :
    ¬ ContainsDirectedCycle (B ∪ F) := by
  classical
  rintro ⟨C, hC⟩
  let edge : Fin C.length → V × V :=
    fun i => (C.vertex i, C.vertex (C.next i))
  have hcolour (i : Fin C.length) : edge i ∈ B ∨ edge i ∈ F :=
    hC ⟨i, rfl⟩
  by_cases hexF : ∃ i, edge i ∈ F
  · obtain ⟨s, hsF⟩ := hexF
    let C₁ := rotateCycle C s
    have hC₁ : C₁.EdgeSet ⊆ B ∪ F :=
      (rotateCycle_edgeSet_subset C s).trans hC
    have hC₁graph : ∀ i, D.Adj (C₁.vertex i) (C₁.vertex (C₁.next i)) :=
      fun i => hgraph (hC₁ ⟨i, rfl⟩)
    have hzeroF :
        (C₁.vertex ⟨0, C₁.positive⟩,
          C₁.vertex (C₁.next ⟨0, C₁.positive⟩)) ∈ F := by
      dsimp [edge] at hsF
      simpa [C₁, rotateCycle, DirectedCycle.next,
        Nat.mod_eq_of_lt s.2] using hsF
    by_cases hexB : ∃ i, (C₁.vertex i, C₁.vertex (C₁.next i)) ∈ B
    · have hexBNat : ∃ n, ∃ hn : n < C₁.length,
          (C₁.vertex ⟨n, hn⟩,
            C₁.vertex (C₁.next ⟨n, hn⟩)) ∈ B := by
        rcases hexB with ⟨i, hi⟩
        exact ⟨i.1, i.2, hi⟩
      let n := Nat.find hexBNat
      rcases Nat.find_spec hexBNat with ⟨hnlt, hnB'⟩
      have hnB :
          (C₁.vertex ⟨n, hnlt⟩,
            C₁.vertex (C₁.next ⟨n, hnlt⟩)) ∈ B := hnB'
      have hnpos : 0 < n := by
        apply Nat.pos_of_ne_zero
        intro hnzero
        have hnFin : (⟨n, hnlt⟩ : Fin C₁.length) =
            ⟨0, C₁.positive⟩ := Fin.ext hnzero
        rw [hnFin] at hnB
        exact Set.disjoint_left.1 hdisj hnB hzeroF
      have hbeforeNotB : ∀ k (hk : k < n),
          (C₁.vertex ⟨k, by omega⟩,
            C₁.vertex (C₁.next ⟨k, by omega⟩)) ∉ B := by
        intro k hk hkB
        have hle := Nat.find_min' hexBNat ⟨by omega, hkB⟩
        omega
      have hprevF :
          (C₁.vertex ⟨n - 1, by omega⟩,
            C₁.vertex (C₁.next ⟨n - 1, by omega⟩)) ∈ F := by
        have hc := hC₁ ⟨⟨n - 1, by omega⟩, rfl⟩
        exact hc.resolve_left (hbeforeNotB (n - 1) (by omega))
      let C₂ := rotateCycle C₁ (⟨n, hnlt⟩ : Fin C₁.length)
      have hC₂ : C₂.EdgeSet ⊆ B ∪ F :=
        (rotateCycle_edgeSet_subset C₁ ⟨n, hnlt⟩).trans hC₁
      have hC₂graph : ∀ i,
          D.Adj (C₂.vertex i) (C₂.vertex (C₂.next i)) :=
        fun i => hgraph (hC₂ ⟨i, rfl⟩)
      have hzeroB :
          (C₂.vertex ⟨0, C₂.positive⟩,
            C₂.vertex (C₂.next ⟨0, C₂.positive⟩)) ∈ B := by
        dsimp only [C₂]
        have heq := rotateCycle_edge_at C₁ ⟨n, hnlt⟩
          (⟨0, C₁.positive⟩ : Fin C₁.length)
        have hrhs :
            (C₁.vertex
                ⟨(n + 0) % C₁.length, Nat.mod_lt _ C₁.positive⟩,
              C₁.vertex (C₁.next
                ⟨(n + 0) % C₁.length, Nat.mod_lt _ C₁.positive⟩)) ∈ B := by
          have hidx :
              (⟨(n + 0) % C₁.length, Nat.mod_lt _ C₁.positive⟩ :
                Fin C₁.length) = ⟨n, hnlt⟩ := by
            apply Fin.ext
            simpa using Nat.mod_eq_of_lt hnlt
          rw [hidx]
          exact hnB
        exact heq.symm ▸ hrhs
      let last : Fin C₁.length :=
        ⟨C₁.length - 1, Nat.sub_lt C₁.positive (by omega)⟩
      have hlastIndex :
          ((n + (C₁.length - 1)) % C₁.length) = n - 1 := by
        have hadd : n + (C₁.length - 1) = C₁.length + (n - 1) := by
          omega
        rw [hadd, Nat.add_mod]
        simp [Nat.mod_eq_of_lt (show n - 1 < C₁.length by omega)]
      have hlastF :
          (C₂.vertex last, C₂.vertex (C₂.next last)) ∈ F := by
        dsimp only [C₂]
        have heq := rotateCycle_edge_at C₁ ⟨n, hnlt⟩
          last
        rw [heq]
        simpa [last, hlastIndex] using hprevF
      have hexF₂ : ∃ m, ∃ hm : m < C₂.length,
          (C₂.vertex ⟨m, hm⟩,
            C₂.vertex (C₂.next ⟨m, hm⟩)) ∈ F := by
        exact ⟨last.1, last.2, hlastF⟩
      let m := Nat.find hexF₂
      rcases Nat.find_spec hexF₂ with ⟨hmlt, hmF'⟩
      have hmF :
          (C₂.vertex ⟨m, hmlt⟩,
            C₂.vertex (C₂.next ⟨m, hmlt⟩)) ∈ F := hmF'
      have hmpos : 0 < m := by
        apply Nat.pos_of_ne_zero
        intro hmzero
        have hmFin : (⟨m, hmlt⟩ : Fin C₂.length) =
            ⟨0, C₂.positive⟩ := Fin.ext hmzero
        rw [hmFin] at hmF
        exact Set.disjoint_left.1 hdisj hzeroB hmF
      let p := cyclePrefixPath C₂ hC₂graph m hmlt
      have hpB : p.edgeSet ⊆ B := by
        intro e he
        rw [cyclePrefixPath_edgeSet] at he
        rcases he with ⟨i, hi, rfl⟩
        have hnotF :
            (C₂.vertex i, C₂.vertex (C₂.next i)) ∉ F := by
          intro hiF
          have hle := Nat.find_min' hexF₂ ⟨i.2, hiF⟩
          omega
        exact (hC₂ ⟨i, rfl⟩).resolve_right hnotF
      have hpne : p.start ≠ p.finish :=
        cyclePrefixPath_nontrivial C₂ hC₂graph hmlt hmpos
      have hnextLast : C₂.next last = ⟨0, C₂.positive⟩ := by
        apply Fin.ext
        change (C₁.length - 1 + 1) % C₁.length = 0
        rw [Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.2
          (Nat.ne_of_gt C₁.positive)), Nat.mod_self]
      apply hno p hpne hpB (C₂.vertex last)
        (C₂.vertex (C₂.next ⟨m, hmlt⟩))
      · simpa [p, cyclePrefixPath, hnextLast] using hlastF
      · simpa [p, cyclePrefixPath] using hmF
    · apply hF
      refine ⟨C₁, ?_⟩
      rintro e ⟨i, rfl⟩
      exact (hC₁ ⟨i, rfl⟩).resolve_left
        (fun hiB => hexB ⟨i, hiB⟩)
  · apply hB
    refine ⟨C, ?_⟩
    rintro e ⟨i, rfl⟩
    exact (hcolour i).resolve_right (fun hiF => hexF ⟨i, hiF⟩)

/-! ## Retained finite paths lie on one reference-warp member -/

variable {G : DWeb V}

private theorem Walk.support_subset_warp_member
    {a b : V} (w : Walk G.graph a b)
    {W : Set G.DPath} (hW : G.IsWarp W)
    {p₀ : G.DPath} (hp₀W : p₀ ∈ W) (ha : a ∈ p₀.support)
    (hE : w.edgeSet ⊆ familyEdges W) :
    ∀ x ∈ w.support, x ∈ p₀.support := by
  induction w with
  | nil =>
      intro x hx
      simp only [Walk.support_nil, List.mem_singleton] at hx
      subst x
      exact ha
  | @cons a c b hac w ih =>
      have hacW : (a, c) ∈ familyEdges W := hE (by simp)
      simp only [familyEdges, Set.mem_iUnion] at hacW
      rcases hacW with ⟨q, hqW, hacq⟩
      have hqa : a ∈ q.support := (q.edgeSet_subset_support_prod hacq).1
      have hqc : c ∈ q.support := (q.edgeSet_subset_support_prod hacq).2
      have hqp₀ : q = p₀ :=
        DWeb.IsWarp.eq_of_mem_support hW hqW hp₀W hqa ha
      have hc : c ∈ p₀.support := hqp₀ ▸ hqc
      have htail : w.edgeSet ⊆ familyEdges W := by
        intro e he
        apply hE
        simp [he]
      have ihtail := ih hc htail
      intro x hx
      simp only [Walk.support_cons, List.mem_cons] at hx
      rcases hx with rfl | hx
      · exact ha
      · exact ihtail x hx

/-- A nontrivial finite path using only warp edges is a subpath of the
unique warp member containing its first edge. -/
theorem finitePath_isFragmentOf_of_edgeSet_subset_familyEdges
    {W : Set G.DPath} (hW : G.IsWarp W)
    (r : FinitePath G.graph) (hrne : r.start ≠ r.finish)
    (hE : r.edgeSet ⊆ familyEdges W) :
    IsFragmentOf r W := by
  obtain ⟨z, hrz⟩ :=
    FinitePath.exists_edge_from_of_mem_of_ne_finish r r.start_mem_support hrne
  have hrzW := hE hrz
  simp only [familyEdges, Set.mem_iUnion] at hrzW
  rcases hrzW with ⟨p₀, hp₀W, hrzp₀⟩
  have hstart : r.start ∈ p₀.support :=
    (p₀.edgeSet_subset_support_prod hrzp₀).1
  have hsupp : r.support ⊆ p₀.support := by
    exact Walk.support_subset_warp_member r.walk hW hp₀W hstart hE
  have hedge : r.edgeSet ⊆ p₀.edgeSet := by
    intro e her
    have heW := hE her
    simp only [familyEdges, Set.mem_iUnion] at heW
    rcases heW with ⟨q, hqW, heq⟩
    have heEnds := r.edgeSet_subset_support_prod her
    have hqe := q.edgeSet_subset_support_prod heq
    have hqp₀ : q = p₀ :=
      DWeb.IsWarp.eq_of_mem_support hW hqW hp₀W hqe.1 (hsupp heEnds.1)
    exact hqp₀ ▸ heq
  exact ⟨p₀, hp₀W, hsupp, hedge⟩

/-- Source safeness forbids an inserted--retained--inserted sandwich once
the maximal-contact normalization has made the switch locally functional. -/
theorem isSwitchingSafe_noForwardSandwich
    {Y : Set G.DPath} {Q : AltPath G.graph}
    (hfin : G.HasFiniteCharacter Y) (hSafe : IsSwitchingSafe Y Q) :
    NoForwardSandwich (D := G.graph)
      (familyEdges Y \ Q.directionEdges .backward)
      (Q.directionEdges .forward) := by
  intro r hrne hrB a b hIn hOut
  have hfrag := finitePath_isFragmentOf_of_edgeSet_subset_familyEdges
    hSafe.1.1.1 r hrne (hrB.trans Set.diff_subset)
  rcases hfrag with ⟨p, hpY, hrp⟩
  rcases hfin hpY with ⟨q, rfl⟩
  exact hSafe.no_forward_retainedPath_forward hpY hrp hrne hrB hIn hOut

/-- Along a ray whose edges are coloured `B` or `F`, absence of an
`F-B⁺-F` sandwich forces a monochromatic tail. -/
theorem ray_eventually_left_or_right
    (r : Ray D) (B F : Set (V × V))
    (hcover : r.edgeSet ⊆ B ∪ F)
    (hno : NoForwardSandwich (D := D) B F) :
    (∃ N, (r.tail N).edgeSet ⊆ B) ∨
      ∃ N, (r.tail N).edgeSet ⊆ F := by
  classical
  let edge : ℕ → V × V := fun n ↦ (r n, r (n + 1))
  have hedge (n : ℕ) : edge n ∈ r.edgeSet := ⟨n, rfl⟩
  have hcolour (n : ℕ) : edge n ∈ B ∨ edge n ∈ F :=
    hcover (hedge n)
  by_cases hexF : ∃ i, edge i ∈ F
  · obtain ⟨i, hiF⟩ := hexF
    by_cases hallF : ∀ n, edge (i + n) ∈ F
    · right
      refine ⟨i, ?_⟩
      rintro e ⟨n, rfl⟩
      simpa [edge, Nat.add_assoc] using hallF n
    · have hexNotF : ∃ n, edge (i + n) ∉ F := by
        simpa only [not_forall] using hallF
      let n₀ := Nat.find hexNotF
      have hn₀notF : edge (i + n₀) ∉ F := Nat.find_spec hexNotF
      have hn₀pos : 0 < n₀ := by
        apply Nat.pos_of_ne_zero
        intro hn₀
        apply hn₀notF
        simpa [hn₀] using hiF
      let k := i + n₀
      have hprevF : edge (k - 1) ∈ F := by
        have hkprev : k - 1 = i + (n₀ - 1) := by
          dsimp [k]
          omega
        rw [hkprev]
        by_contra hnot
        have hfind : n₀ ≤ n₀ - 1 :=
          Nat.find_min' hexNotF (by simpa using hnot)
        omega
      left
      refine ⟨k, ?_⟩
      rintro e ⟨m, rfl⟩
      change edge (k + m) ∈ B
      by_contra hnotB
      have hsomeF : ∃ t, edge (k + t) ∈ F := by
        exact ⟨m, (hcolour (k + m)).resolve_left hnotB⟩
      let t₀ := Nat.find hsomeF
      have ht₀F : edge (k + t₀) ∈ F := Nat.find_spec hsomeF
      have hkNotF : edge k ∉ F := by
        simpa [k] using hn₀notF
      have ht₀pos : 0 < t₀ := by
        apply Nat.pos_of_ne_zero
        intro ht₀
        apply hkNotF
        simpa [ht₀] using ht₀F
      let p := raySegmentPath r k t₀
      have hpB : p.edgeSet ⊆ B := by
        intro e he
        change e ∈ (raySegmentPath r k t₀).edgeSet at he
        rw [raySegmentPath_edgeSet] at he
        rcases he with ⟨t, ht, rfl⟩
        change edge (k + t) ∈ B
        have hnotF : edge (k + t) ∉ F := by
          intro htF
          have := Nat.find_min' hsomeF htF
          omega
        exact (hcolour (k + t)).resolve_right hnotF
      have hpne : p.start ≠ p.finish := by
        exact raySegmentPath_nontrivial r ht₀pos
      apply hno p hpne hpB (r (k - 1)) (r (k + t₀ + 1))
      · have hkpos : 0 < k := by
          dsimp [k]
          omega
        simpa [p, edge, Nat.sub_add_cancel hkpos] using hprevF
      · simpa [p, edge, Nat.add_assoc] using ht₀F
  · left
    refine ⟨0, ?_⟩
    rintro e ⟨n, rfl⟩
    have hnNotF : edge n ∉ F := fun hnF ↦ hexF ⟨n, hnF⟩
    simpa [edge] using (hcolour n).resolve_right hnNotF

/-- The reverse-ray analogue of `ray_eventually_left_or_right`.  The
conclusion is stated on edge indices because a reverse ray is represented by
the unbundled vertex sequence used in `ContainsReverseDirectedRay`. -/
theorem reverseRay_eventually_left_or_right
    (R : DirectedRay V)
    (hAdj : ∀ n, D.Adj (R.vertex (n + 1)) (R.vertex n))
    (B F : Set (V × V))
    (hcover : ∀ n,
      (R.vertex (n + 1), R.vertex n) ∈ B ∪ F)
    (hno : NoForwardSandwich (D := D) B F) :
    (∃ N, ∀ n, (R.vertex (N + n + 1), R.vertex (N + n)) ∈ B) ∨
      ∃ N, ∀ n, (R.vertex (N + n + 1), R.vertex (N + n)) ∈ F := by
  classical
  let edge : ℕ → V × V :=
    fun n ↦ (R.vertex (n + 1), R.vertex n)
  have hcolour (n : ℕ) : edge n ∈ B ∨ edge n ∈ F := hcover n
  by_cases hexF : ∃ i, edge i ∈ F
  · obtain ⟨i, hiF⟩ := hexF
    by_cases hallF : ∀ n, edge (i + n) ∈ F
    · right
      refine ⟨i, ?_⟩
      intro n
      simpa [edge, Nat.add_assoc] using hallF n
    · have hexNotF : ∃ n, edge (i + n) ∉ F := by
        simpa only [not_forall] using hallF
      let n₀ := Nat.find hexNotF
      have hn₀notF : edge (i + n₀) ∉ F := Nat.find_spec hexNotF
      have hn₀pos : 0 < n₀ := by
        apply Nat.pos_of_ne_zero
        intro hn₀
        apply hn₀notF
        simpa [hn₀] using hiF
      let k := i + n₀
      have hprevF : edge (k - 1) ∈ F := by
        have hkprev : k - 1 = i + (n₀ - 1) := by
          dsimp [k]
          omega
        rw [hkprev]
        by_contra hnot
        have hfind : n₀ ≤ n₀ - 1 :=
          Nat.find_min' hexNotF (by simpa using hnot)
        omega
      left
      refine ⟨k, ?_⟩
      intro m
      change edge (k + m) ∈ B
      by_contra hnotB
      have hsomeF : ∃ t, edge (k + t) ∈ F :=
        ⟨m, (hcolour (k + m)).resolve_left hnotB⟩
      let t₀ := Nat.find hsomeF
      have ht₀F : edge (k + t₀) ∈ F := Nat.find_spec hsomeF
      have hkNotF : edge k ∉ F := by
        simpa [k] using hn₀notF
      have ht₀pos : 0 < t₀ := by
        apply Nat.pos_of_ne_zero
        intro ht₀
        apply hkNotF
        simpa [ht₀] using ht₀F
      let p := reverseRaySegmentPath R hAdj k t₀
      have hpB : p.edgeSet ⊆ B := by
        intro e he
        change e ∈ (reverseRaySegmentPath R hAdj k t₀).edgeSet at he
        rw [reverseRaySegmentPath_edgeSet] at he
        rcases he with ⟨t, ht, rfl⟩
        change edge (k + t) ∈ B
        have hnotF : edge (k + t) ∉ F := by
          intro htF
          have := Nat.find_min' hsomeF htF
          omega
        exact (hcolour (k + t)).resolve_right hnotF
      have hpne : p.start ≠ p.finish :=
        reverseRaySegmentPath_nontrivial R hAdj ht₀pos
      apply hno p hpne hpB (R.vertex (k + t₀ + 1)) (R.vertex (k - 1))
      · simpa [p, edge, Nat.add_assoc] using ht₀F
      · have hkpos : 0 < k := by
          dsimp [k]
          omega
        simpa [p, edge, Nat.sub_add_cancel hkpos] using hprevF
  · left
    refine ⟨0, ?_⟩
    intro n
    have hnNotF : edge n ∉ F := fun hnF ↦ hexF ⟨n, hnF⟩
    simpa [edge] using (hcolour n).resolve_right hnNotF

theorem union_not_containsDirectedRay
    (B F : Set (V × V))
    (hgraph : B ∪ F ⊆ {e | D.Adj e.1 e.2})
    (hno : NoForwardSandwich (D := D) B F)
    (hB : ¬ ContainsDirectedRay B)
    (hF : ¬ ContainsDirectedRay F) :
    ¬ ContainsDirectedRay (B ∪ F) := by
  rintro ⟨R, hR⟩
  let r : Ray D :=
    { toFun := R.vertex
      adj_succ := fun n ↦ hgraph (hR ⟨n, rfl⟩)
      injective := R.injective }
  rcases ray_eventually_left_or_right r B F hR hno with htail | htail
  · rcases htail with ⟨N, hN⟩
    apply hB
    let T : DirectedRay V :=
      { vertex := fun n ↦ R.vertex (N + n)
        injective := fun _ _ h ↦ Nat.add_left_cancel (R.injective h) }
    refine ⟨T, ?_⟩
    rintro e ⟨n, rfl⟩
    apply hN
    exact ⟨n, by simp [r, T, Nat.add_assoc]⟩
  · rcases htail with ⟨N, hN⟩
    apply hF
    let T : DirectedRay V :=
      { vertex := fun n ↦ R.vertex (N + n)
        injective := fun _ _ h ↦ Nat.add_left_cancel (R.injective h) }
    refine ⟨T, ?_⟩
    rintro e ⟨n, rfl⟩
    apply hN
    exact ⟨n, by simp [r, T, Nat.add_assoc]⟩

theorem union_not_containsReverseDirectedRay
    (B F : Set (V × V))
    (hgraph : B ∪ F ⊆ {e | D.Adj e.1 e.2})
    (hno : NoForwardSandwich (D := D) B F)
    (hB : ¬ ContainsReverseDirectedRay B)
    (hF : ¬ ContainsReverseDirectedRay F) :
    ¬ ContainsReverseDirectedRay (B ∪ F) := by
  rintro ⟨R, hR⟩
  have hAdj : ∀ n, D.Adj (R.vertex (n + 1)) (R.vertex n) :=
    fun n ↦ hgraph (hR n)
  rcases reverseRay_eventually_left_or_right R hAdj B F hR hno with
    htail | htail
  · rcases htail with ⟨N, hN⟩
    apply hB
    let T : DirectedRay V :=
      { vertex := fun n ↦ R.vertex (N + n)
        injective := fun _ _ h ↦ Nat.add_left_cancel (R.injective h) }
    refine ⟨T, ?_⟩
    intro n
    simpa [T, Nat.add_assoc] using hN n
  · rcases htail with ⟨N, hN⟩
    apply hF
    let T : DirectedRay V :=
      { vertex := fun n ↦ R.vertex (N + n)
        injective := fun _ _ h ↦ Nat.add_left_cancel (R.injective h) }
    refine ⟨T, ?_⟩
    intro n
    simpa [T, Nat.add_assoc] using hN n

/-! ## Monochromatic ingredients for the switched relation -/

theorem familyEdges_not_containsDirectedRay
    {W : Set G.DPath} (hW : G.IsWarp W)
    (hfin : G.HasFiniteCharacter W) :
    ¬ ContainsDirectedRay (familyEdges W) := by
  rintro ⟨R, hR⟩
  obtain ⟨p₀, hp₀W, hp₀edge⟩ :
      ∃ p₀ ∈ W, (R.vertex 0, R.vertex 1) ∈ p₀.edgeSet := by
    have hm := hR ⟨0, rfl⟩
    simp only [familyEdges, Set.mem_iUnion] at hm
    rcases hm with ⟨p₀, hp₀W, hp₀edge⟩
    exact ⟨p₀, hp₀W, by simpa using hp₀edge⟩
  have hedge : ∀ n, (R.vertex n, R.vertex (n + 1)) ∈ p₀.edgeSet := by
    intro n
    induction n with
    | zero => simpa using hp₀edge
    | succ n ih =>
        have hm := hR ⟨n + 1, rfl⟩
        simp only [familyEdges, Set.mem_iUnion] at hm
        rcases hm with ⟨p, hpW, hpedge⟩
        have hp₀shared : R.vertex (n + 1) ∈ p₀.support :=
          (p₀.edgeSet_subset_support_prod ih).2
        have hpshared : R.vertex (n + 1) ∈ p.support :=
          (p.edgeSet_subset_support_prod hpedge).1
        have hp : p = p₀ :=
          DWeb.IsWarp.eq_of_mem_support hW hpW hp₀W hpshared hp₀shared
        exact hp ▸ hpedge
  rcases hfin hp₀W with ⟨p, rfl⟩
  have hsupport : ∀ n, R.vertex n ∈ p.support := by
    intro n
    cases n with
    | zero => exact (p.edgeSet_subset_support_prod (hedge 0)).1
    | succ n => exact (p.edgeSet_subset_support_prod (hedge n)).2
  exact p.support_finite.not_infinite
    (Set.infinite_of_injective_forall_mem R.injective hsupport)

theorem familyEdges_not_containsDirectedCycle
    {W : Set G.DPath} (hW : G.IsWarp W)
    (hfin : G.HasFiniteCharacter W) :
    ¬ ContainsDirectedCycle (familyEdges W) := by
  rintro ⟨C, hC⟩
  let i₀ : Fin C.length := ⟨0, C.positive⟩
  obtain ⟨p₀, hp₀W, hp₀edge⟩ :
      ∃ p₀ ∈ W, (C.vertex i₀, C.vertex (C.next i₀)) ∈ p₀.edgeSet := by
    have hm := hC ⟨i₀, rfl⟩
    simp only [familyEdges, Set.mem_iUnion] at hm
    rcases hm with ⟨p₀, hp₀W, hp₀edge⟩
    exact ⟨p₀, hp₀W, hp₀edge⟩
  have hedgeNat : ∀ n (hn : n < C.length),
      (C.vertex ⟨n, hn⟩, C.vertex (C.next ⟨n, hn⟩)) ∈ p₀.edgeSet := by
    intro n
    induction n with
    | zero =>
        intro hn
        simpa [i₀] using hp₀edge
    | succ n ih =>
        intro hn
        have hn' : n < C.length := by omega
        have hnext : C.next (⟨n, hn'⟩ : Fin C.length) = ⟨n + 1, hn⟩ := by
          apply Fin.ext
          exact Nat.mod_eq_of_lt hn
        have hm := hC ⟨⟨n + 1, hn⟩, rfl⟩
        simp only [familyEdges, Set.mem_iUnion] at hm
        rcases hm with ⟨p, hpW, hpedge⟩
        have hp₀shared : C.vertex ⟨n + 1, hn⟩ ∈ p₀.support := by
          rw [← hnext]
          exact (p₀.edgeSet_subset_support_prod (ih hn')).2
        have hpshared : C.vertex ⟨n + 1, hn⟩ ∈ p.support :=
          (p.edgeSet_subset_support_prod hpedge).1
        have hp : p = p₀ :=
          DWeb.IsWarp.eq_of_mem_support hW hpW hp₀W hpshared hp₀shared
        exact hp ▸ hpedge
  have hCp₀ : C.EdgeSet ⊆ p₀.edgeSet := by
    rintro _ ⟨i, rfl⟩
    exact hedgeNat i.1 i.2
  rcases hfin hp₀W with ⟨p, rfl⟩
  exact FinitePath.edgeSet_not_containsDirectedCycle p ⟨C, hCp₀⟩

theorem familyEdges_not_containsReverseDirectedRay
    {W : Set G.DPath} (hW : G.IsWarp W)
    (hfin : G.HasFiniteCharacter W) :
    ¬ ContainsReverseDirectedRay (familyEdges W) := by
  rintro ⟨R, hR⟩
  obtain ⟨p₀, hp₀W, hp₀edge⟩ :
      ∃ p₀ ∈ W, (R.vertex 1, R.vertex 0) ∈ p₀.edgeSet := by
    have hm := hR 0
    simp only [familyEdges, Set.mem_iUnion] at hm
    simpa using hm
  have hedge : ∀ n, (R.vertex (n + 1), R.vertex n) ∈ p₀.edgeSet := by
    intro n
    induction n with
    | zero => simpa using hp₀edge
    | succ n ih =>
        have hm := hR (n + 1)
        simp only [familyEdges, Set.mem_iUnion] at hm
        rcases hm with ⟨p, hpW, hpedge⟩
        have hp₀shared : R.vertex (n + 1) ∈ p₀.support :=
          (p₀.edgeSet_subset_support_prod ih).1
        have hpshared : R.vertex (n + 1) ∈ p.support :=
          (p.edgeSet_subset_support_prod hpedge).2
        have hp : p = p₀ :=
          DWeb.IsWarp.eq_of_mem_support hW hpW hp₀W hpshared hp₀shared
        exact hp ▸ hpedge
  rcases hfin hp₀W with ⟨p, rfl⟩
  have hsupport : ∀ n, R.vertex n ∈ p.support := by
    intro n
    cases n with
    | zero => exact (p.edgeSet_subset_support_prod (hedge 0)).2
    | succ n => exact (p.edgeSet_subset_support_prod (hedge n)).1
  exact p.support_finite.not_infinite
    (Set.infinite_of_injective_forall_mem R.injective hsupport)

private theorem not_containsReverseDirectedRay_of_finite
    {E : Set (V × V)} (hE : E.Finite) :
    ¬ ContainsReverseDirectedRay E := by
  rintro ⟨R, hR⟩
  let f : ℕ → V × V := fun n => (R.vertex (n + 1), R.vertex n)
  have hf : Function.Injective f := by
    intro i j hij
    apply R.injective
    exact congrArg Prod.snd hij
  have hrange : Set.range f ⊆ E := by
    rintro _ ⟨n, rfl⟩
    exact hR n
  exact (hE.subset hrange).not_infinite (Set.infinite_range_of_injective hf)

theorem AltPath.forwardEdges_not_containsReverseDirectedRay
    (Q : AltPath G.graph) :
    ¬ ContainsReverseDirectedRay (Q.directionEdges .forward) := by
  cases Q with
  | trivial x =>
      apply not_containsReverseDirectedRay_of_finite
      simp [AltPath.directionEdges, AltPath.links]
  | finite Q =>
      apply not_containsReverseDirectedRay_of_finite
      have hfin : (AltPath.finite Q).edgeSet.Finite := by
        simpa only [AltPath.edgeSet, AltPath.links, FiniteTrace.links] using
          Q.edgeSet_finite
      apply hfin.subset
      rw [(AltPath.finite Q).edgeSet_eq_directionEdges_union]
      exact Set.subset_union_left
  | infinite Q =>
      exact Q.forwardEdges_not_containsReverseDirectedRay

end SwitchingCore

/-! ## Corrected safe-switching theorem -/

/-- For an alternating path, the edges outside the reference warp are
exactly its forward-direction edges. -/
theorem IsSwitchingAlternating.edgeSet_sdiff_familyEdges_eq_forward
    {Y : Set Gamma.DPath} {Q : AltPath Gamma.graph}
    (h : IsSwitchingAlternating Y Q) :
    Q.edgeSet \ familyEdges Y = Q.directionEdges .forward := by
  ext e
  constructor
  · rintro ⟨heQ, heY⟩
    rw [Q.edgeSet_eq_directionEdges_union] at heQ
    rcases heQ with heF | heB
    · exact heF
    · exfalso
      apply heY
      simp only [AltPath.directionEdges, Set.mem_iUnion] at heB
      rcases heB with ⟨l, hlQ, hldir, hel⟩
      rcases h.1.2.1 l hlQ hldir with ⟨p, hpY, hlp⟩
      simp only [familyEdges, Set.mem_iUnion]
      exact ⟨p, hpY, hlp.2 hel⟩
  · intro heF
    refine ⟨?_, ?_⟩
    · rw [Q.edgeSet_eq_directionEdges_union]
      exact Or.inl heF
    exact Set.disjoint_left.1 h.forwardLinksOff.directionEdges_disjoint heF

/-- Corrected Lemma 4.9.  The source safeness hypotheses are supplemented
by the explicit maximal-contact normalization `IsSwitchingSafe`; under this
necessary condition the exact switched edge relation is realized by a
finite-character warp. -/
theorem isSwitchingSafe_hasFiniteWarpRealization
    (Y : Set Gamma.DPath) (Q : AltPath Gamma.graph)
    (hfin : Gamma.HasFiniteCharacter Y)
    (hSafe : IsSwitchingSafe Y Q) :
    (Cyclowarp.application Y Q).HasFiniteWarpRealization := by
  let B : Set (V × V) :=
    familyEdges Y \ Q.directionEdges .backward
  let F : Set (V × V) := Q.directionEdges .forward
  have hAlt : IsAlternating Y Q := hSafe.1.1
  have hSwitchAlt : IsSwitchingAlternating Y Q :=
    hSafe.isSwitchingAlternating
  have hE : switchedEdges Y Q = B ∪ F := by
    simpa [B, F] using hSwitchAlt.switchedEdges_eq
  have hgraph : B ∪ F ⊆ {e | Gamma.graph.Adj e.1 e.2} := by
    rw [← hE]
    exact (Cyclowarp.application Y Q).edges_in_graph
  have hdisj : Disjoint B F := by
    rw [Set.disjoint_left]
    intro e heB heF
    exact Set.disjoint_left.1
      hSwitchAlt.forwardLinksOff.directionEdges_disjoint heF heB.1
  have hno : SwitchingCore.NoForwardSandwich
      (D := Gamma.graph) B F := by
    simpa [B, F] using
      SwitchingCore.isSwitchingSafe_noForwardSandwich hfin hSafe
  have hBcycle : ¬ ContainsDirectedCycle B := by
    rintro ⟨C, hC⟩
    exact SwitchingCore.familyEdges_not_containsDirectedCycle hAlt.1 hfin
      ⟨C, hC.trans (by intro e he; exact he.1)⟩
  have hBray : ¬ ContainsDirectedRay B := by
    rintro ⟨R, hR⟩
    exact SwitchingCore.familyEdges_not_containsDirectedRay hAlt.1 hfin
      ⟨R, hR.trans (by intro e he; exact he.1)⟩
  have hBreverse : ¬ ContainsReverseDirectedRay B := by
    rintro ⟨R, hR⟩
    exact SwitchingCore.familyEdges_not_containsReverseDirectedRay hAlt.1 hfin
      ⟨R, fun n => (hR n).1⟩
  have houtside : Q.edgeSet \ familyEdges Y = F := by
    simpa [F] using hSwitchAlt.edgeSet_sdiff_familyEdges_eq_forward
  have hFray : ¬ ContainsDirectedRay F := by
    rw [← houtside]
    exact hSafe.1.2.2.1
  have hFcycle : ¬ ContainsDirectedCycle F := by
    rw [← houtside]
    exact hSafe.1.2.2.2
  have hFreverse : ¬ ContainsReverseDirectedRay F := by
    simpa [F] using SwitchingCore.AltPath.forwardEdges_not_containsReverseDirectedRay Q
  have hcycle : ¬ ContainsDirectedCycle (B ∪ F) :=
    SwitchingCore.union_not_containsDirectedCycle B F hgraph hdisj hno
      hBcycle hFcycle
  have hRay : ¬ ContainsDirectedRay (B ∪ F) :=
    SwitchingCore.union_not_containsDirectedRay B F hgraph hno hBray hFray
  have hReverse : ¬ ContainsReverseDirectedRay (B ∪ F) :=
    SwitchingCore.union_not_containsReverseDirectedRay B F hgraph hno
      hBreverse hFreverse
  have hI : ∀ x ∈ isolatedVertices Y, ∀ y,
      (x, y) ∉ switchedEdges Y Q ∧ (y, x) ∉ switchedEdges Y Q := by
    intro x hx y
    constructor
    · intro hxy
      exact (hSafe.switchedEdge_not_incident_isolated hx hxy).1 rfl
    · intro hyx
      exact (hSafe.switchedEdge_not_incident_isolated hx hyx).2 rfl
  rcases RelationDecomposition.DWeb.exists_finiteWarp_realizing_biUnique
      Gamma (switchedEdges Y Q) (isolatedVertices Y)
      (Cyclowarp.application Y Q).edges_in_graph
      hSwitchAlt.switchedEdges_biUnique
      (by simpa [hE] using hcycle)
      (by simpa [hE] using hRay)
      (by simpa [hE] using hReverse) hI with
    ⟨W, hW, hWedges, hWiso, hWfin⟩
  exact ⟨W, ⟨hW, by simpa using hWedges, by simpa using hWiso⟩, hWfin⟩

end Alternating
end Erdos599
