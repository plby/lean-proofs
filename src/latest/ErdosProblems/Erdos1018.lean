/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
This is a Lean formalization of a solution to Erdős Problem 1018.
https://www.erdosproblems.com/forum/thread/1018

Informal authors:
- Alexandr Kostochka
- László Pyber

Formal authors:
- Codex
- GPT-5.6 Sol

URLs:
- https://github.com/plby/lean-proofs/blob/main/ErdosProblems/Erdos1018.md
-/
/-
This is a Lean formalization of the affirmative resolution of Erdős Problem 1018.
https://www.erdosproblems.com/1018

Kostochka and Pyber proved the stronger fact used here: polynomially dense
finite graphs contain a bounded-order subdivision of `K₅`.

The accompanying detailed proof and Leanization plan is `tex/1018.tex`.
-/

import Mathlib
import Mathlib.Data.Fintype.EquivFin
import ErdosProblems.Erdos1018.Layers
import ErdosProblems.Erdos1018.Paths
import ErdosProblems.Erdos1018.Density
import ErdosProblems.Erdos1018.Geometry

open Function Set
open SimpleGraph
open Finset
open scoped Sym2

namespace Erdos1018

/-! ### Topological clique models -/

/-- One ordered representative `(i,j)` with `i < j` for every edge of `K_r`. -/
abbrev CliqueEdge (r : ℕ) := {e : Fin r × Fin r // e.1 < e.2}

/-- The internal vertices of a walk, excluding its two endpoints. -/
def walkInteriorSet {V : Type*} {G : SimpleGraph V} {u v : V}
    (p : G.Walk u v) : Set V :=
  {x | x ∈ p.support ∧ x ≠ u ∧ x ≠ v}

/-- A faithful path model of a subdivision of `K_r`. -/
structure CliqueSubdivision {V : Type*} (G : SimpleGraph V) (r : ℕ) where
  branch : Fin r ↪ V
  path : ∀ e : CliqueEdge r, G.Walk (branch e.1.1) (branch e.1.2)
  path_isPath : ∀ e, (path e).IsPath
  interior_avoids_branch : ∀ e,
    Disjoint (walkInteriorSet (path e)) (Set.range branch)
  interior_pairwise : Pairwise fun e f =>
    Disjoint (walkInteriorSet (path e)) (walkInteriorSet (path f))

/-- `G` contains a subdivision of `K_r`. -/
def ContainsCliqueSubdivision {V : Type*} (G : SimpleGraph V) (r : ℕ) : Prop :=
  Nonempty (CliqueSubdivision G r)

lemma card_cliqueEdge (r : ℕ) :
    Fintype.card (CliqueEdge r) = Nat.choose r 2 := by
  rw [Fintype.card_subtype]
  simpa using (Fintype.card_product_filter_lt (α := Fin r))

/-! ### Kuratowski certificates -/

/-- The nine ordered left--right pairs indexing the edges of `K₃,₃`. -/
abbrev K33Edge := Fin 3 × Fin 3

/-- A faithful path model of a subdivision of `K₃,₃`. -/
structure K33Subdivision {V : Type*} (G : SimpleGraph V) where
  left : Fin 3 ↪ V
  right : Fin 3 ↪ V
  branch_disjoint : Disjoint (Set.range left) (Set.range right)
  path : ∀ e : K33Edge, G.Walk (left e.1) (right e.2)
  path_isPath : ∀ e, (path e).IsPath
  interior_avoids_branch : ∀ e,
    Disjoint (walkInteriorSet (path e))
      (Set.range left ∪ Set.range right)
  interior_pairwise : Pairwise fun e f =>
    Disjoint (walkInteriorSet (path e))
      (walkInteriorSet (path f))

/-- `G` contains a subdivision of `K₃,₃`. -/
def ContainsK33Subdivision {V : Type*} (G : SimpleGraph V) : Prop :=
  Nonempty (K33Subdivision G)

/-- Non-planarity, expressed by the exact finite Kuratowski characterization. -/
def IsNonplanar {V : Type*} (G : SimpleGraph V) : Prop :=
  ContainsCliqueSubdivision G 5 ∨ ContainsK33Subdivision G

theorem isNonplanar_of_containsCliqueSubdivision_five
    {V : Type*} {G : SimpleGraph V}
    (h : ContainsCliqueSubdivision G 5) : IsNonplanar G :=
  Or.inl h

/-- The vertices used by a clique-subdivision model. -/
def cliqueSubdivisionVerts {V : Type*} {G : SimpleGraph V} {r : ℕ}
    (s : CliqueSubdivision G r) : Set V :=
  Set.range s.branch ∪ ⋃ e, {v | v ∈ (s.path e).support}

namespace CliqueSubdivision

theorem branch_mem_verts {V : Type*} {G : SimpleGraph V} {r : ℕ}
    (s : CliqueSubdivision G r) (i : Fin r) :
    s.branch i ∈ cliqueSubdivisionVerts s := by
  exact Or.inl ⟨i, rfl⟩

theorem support_mem_verts {V : Type*} {G : SimpleGraph V} {r : ℕ}
    (s : CliqueSubdivision G r) (e : CliqueEdge r) {x : V}
    (hx : x ∈ (s.path e).support) :
    x ∈ cliqueSubdivisionVerts s := by
  right
  exact Set.mem_iUnion.2 ⟨e, hx⟩

private theorem supportSet_ncard_le_length_add_one {V : Type*}
    {G : SimpleGraph V} {u v : V} (p : G.Walk u v) :
    {x | x ∈ p.support}.ncard ≤ p.length + 1 := by
  classical
  have hset : {x | x ∈ p.support} = (p.support.toFinset : Set V) := by
    ext x
    simp
  rw [hset, Set.ncard_coe_finset, ← p.length_support]
  exact p.support.toFinset_card_le

theorem verts_ncard_le_of_path_length_le {V : Type*}
    {G : SimpleGraph V} {r L : ℕ} (s : CliqueSubdivision G r)
    (hlen : ∀ e, (s.path e).length ≤ L) :
    (cliqueSubdivisionVerts s).ncard ≤
      r + Fintype.card (CliqueEdge r) * (L + 1) := by
  classical
  calc
    (cliqueSubdivisionVerts s).ncard
        ≤ (Set.range s.branch).ncard +
            (⋃ e : CliqueEdge r, {x | x ∈ (s.path e).support}).ncard :=
      Set.ncard_union_le _ _
    _ ≤ r + ∑ e : CliqueEdge r, {x | x ∈ (s.path e).support}.ncard := by
      gcongr
      · simpa [Nat.card_eq_fintype_card] using
          (Set.ncard_range_of_injective s.branch.injective).le
      · exact Set.ncard_iUnion_le_of_fintype _
    _ ≤ r + ∑ _e : CliqueEdge r, (L + 1) := by
      gcongr with e
      exact (supportSet_ncard_le_length_add_one (s.path e)).trans
        (Nat.add_le_add_right (hlen e) 1)
    _ = r + Fintype.card (CliqueEdge r) * (L + 1) := by simp

theorem verts_ncard_le_of_path_length_le_k5 {V : Type*}
    {G : SimpleGraph V} {L : ℕ} (s : CliqueSubdivision G 5)
    (hlen : ∀ e, (s.path e).length ≤ L) :
    (cliqueSubdivisionVerts s).ncard ≤ 5 + 10 * (L + 1) := by
  have hchoose : Nat.choose 5 2 = 10 := by norm_num [Nat.choose]
  have hcard : Fintype.card (CliqueEdge 5) = 10 :=
    (card_cliqueEdge 5).trans hchoose
  simpa [hcard] using s.verts_ncard_le_of_path_length_le hlen

end CliqueSubdivision

/-! ### Finite routing and assembly helpers -/

theorem walkInteriorSet_subset_support {V : Type*} {G : SimpleGraph V}
    {u v : V} (p : G.Walk u v) :
    walkInteriorSet p ⊆ {x | x ∈ p.support} := fun _ hx ↦ hx.1

def throughCenter {V : Type*} {G : SimpleGraph V} {c a b : V}
    (p : G.Walk c a) (q : G.Walk c b) : G.Walk a b :=
  p.reverse.append q

def simpleThroughCenter {V : Type*} [DecidableEq V]
    {G : SimpleGraph V} {c a b : V}
    (p : G.Walk c a) (q : G.Walk c b) : G.Walk a b :=
  (throughCenter p q).bypass

theorem simpleThroughCenter_isPath {V : Type*} [DecidableEq V]
    {G : SimpleGraph V} {c a b : V}
    (p : G.Walk c a) (q : G.Walk c b) :
    (simpleThroughCenter p q).IsPath :=
  Walk.bypass_isPath _

theorem simpleThroughCenter_length_le {V : Type*} [DecidableEq V]
    {G : SimpleGraph V} {c a b : V}
    (p : G.Walk c a) (q : G.Walk c b) :
    (simpleThroughCenter p q).length ≤ p.length + q.length := by
  simpa only [simpleThroughCenter, throughCenter, Walk.length_append,
    Walk.length_reverse] using
      (throughCenter p q).length_bypass_le_length

theorem simpleThroughCenter_support_subset {V : Type*} [DecidableEq V]
    {G : SimpleGraph V} {c a b : V}
    (p : G.Walk c a) (q : G.Walk c b) :
    {x | x ∈ (simpleThroughCenter p q).support} ⊆
      {x | x ∈ p.support ∨ x ∈ q.support} := by
  intro x hx
  have hx' : x ∈ (throughCenter p q).support :=
    (throughCenter p q).support_bypass_subset_support hx
  simpa [throughCenter, Walk.mem_support_append_iff] using hx'

/-- A loop-erased route through a center has no internal vertex in the two
terminal distance layers when both endpoints lie in the nearer layer. -/
theorem simpleThroughCenter_interior_disjoint_layers
    {V : Type*} [Fintype V] [DecidableEq V]
    {J : SimpleGraph V} {center a b : V} {k : ℕ}
    (p : J.Walk center a) (q : J.Walk center b)
    (hpdist : p.length = J.dist center a) (hplen : p.length = k)
    (hqdist : q.length = J.dist center b) (hqlen : q.length = k) :
    Disjoint (walkInteriorSet (simpleThroughCenter p q))
      {x | J.dist center x = k ∨ J.dist center x = k + 1} := by
  rw [Set.disjoint_left]
  intro x hx hxlayers
  have hxsupp := simpleThroughCenter_support_subset p q hx.1
  rcases hxsupp with hxp | hxq
  · obtain ⟨j, hjx, hjle⟩ := Walk.mem_support_iff_exists_getVert.mp hxp
    have hdj := Erdos1018Aux.dist_getVert_eq_of_geodesic J hpdist hjle
    have hxd : J.dist center x = j := by simpa [← hjx] using hdj
    have hjk : j = k := by
      rcases hxlayers with h | h <;> omega
    have hxa : x = a := by
      calc
        x = p.getVert j := hjx.symm
        _ = p.getVert p.length := by rw [hjk, hplen]
        _ = a := p.getVert_length
    exact hx.2.1 hxa
  · obtain ⟨j, hjx, hjle⟩ := Walk.mem_support_iff_exists_getVert.mp hxq
    have hdj := Erdos1018Aux.dist_getVert_eq_of_geodesic J hqdist hjle
    have hxd : J.dist center x = j := by simpa [← hjx] using hdj
    have hjk : j = k := by
      rcases hxlayers with h | h <;> omega
    have hxb : x = b := by
      calc
        x = q.getVert j := hjx.symm
        _ = q.getVert q.length := by rw [hjk, hqlen]
        _ = b := q.getVert_length
    exact hx.2.2 hxb

/-- Mapping a route from a subgraph to its host preserves its internal
vertices and turns avoidance of a host vertex set into an annular inclusion. -/
theorem mapped_route_interior_subset
    {V : Type*} {G : SimpleGraph V} (J A : G.Subgraph)
    {a b : J.verts} (p : J.coe.Walk a b)
    (havoid : Disjoint (walkInteriorSet p)
      {x : J.verts | (x : V) ∈ A.verts}) :
    walkInteriorSet (p.map J.hom) ⊆ J.verts \ A.verts := by
  intro x hx
  have hxsupp : x ∈ (p.map J.hom).support := hx.1
  rw [Walk.support_map] at hxsupp
  rcases List.mem_map.mp hxsupp with ⟨y, hy, rfl⟩
  refine ⟨y.property, ?_⟩
  intro hyA
  have hyInterior : y ∈ walkInteriorSet p := by
    refine ⟨hy, ?_, ?_⟩
    · intro hya
      apply hx.2.1
      simpa [hya]
    · intro hyb
      apply hx.2.2
      simpa [hyb]
  exact Set.disjoint_left.mp havoid hyInterior hyA

/-- The five even, respectively odd, positions in a ten-vertex path. -/
def parityEmbedding (even : Bool) : Fin 5 ↪ Fin 10 where
  toFun i := ⟨2 * i.1 + if even then 0 else 1, by
    cases even <;> simp <;> omega⟩
  inj' := by
    intro i j hij
    apply Fin.ext
    simp only [Fin.mk.injEq] at hij
    omega

/-- The first ten vertices of a path of length at least nine. -/
def firstTen {V : Type*} {G : SimpleGraph V} {a b : V}
    {p : G.Walk a b} (hp : p.IsPath) (hlen : 9 ≤ p.length) :
    Fin 10 ↪ V where
  toFun i := p.getVert i.1
  inj' := by
    intro i j hij
    apply Fin.ext
    exact hp.getVert_injOn (by simp; omega) (by simp; omega) hij

/-- Along a ten-vertex path contained in two consecutive distance layers,
one parity class consists entirely of vertices in the nearer layer. -/
theorem exists_parity_in_near_layer {V : Type*} [Fintype V]
    {J : SimpleGraph V}
    (hconn : J.Connected) (hbip : J.IsBipartite) (center : V) (k : ℕ)
    {a b : V} (p : J.Walk a b) (hlen : 9 ≤ p.length)
    (hlayer : ∀ j : Fin 10,
      J.dist center (p.getVert j.1) = k ∨
        J.dist center (p.getVert j.1) = k + 1) :
    ∃ even : Bool, ∀ i : Fin 5,
      J.dist center (p.getVert (parityEmbedding even i).1) = k := by
  have htoggle (j : ℕ) (hj : j < 9) :
      J.dist center (p.getVert (j + 1)) = k ↔
        J.dist center (p.getVert j) = k + 1 := by
    have hjlen : j < p.length := by omega
    have hadj := p.adj_getVert_succ hjlen
    have hcon := Erdos1018Aux.adj_dist_consecutive J hbip hconn center hadj
    have hjlay := hlayer ⟨j, by omega⟩
    have hslay := hlayer ⟨j + 1, by omega⟩
    change J.dist center (p.getVert j) = k ∨
      J.dist center (p.getVert j) = k + 1 at hjlay
    change J.dist center (p.getVert (j + 1)) = k ∨
      J.dist center (p.getVert (j + 1)) = k + 1 at hslay
    omega
  have htwo (j : ℕ) (hj : j + 2 < 10)
      (hne : J.dist center (p.getVert j) = k) :
      J.dist center (p.getVert (j + 2)) = k := by
    have h1 := htoggle j (by omega)
    have h2 := htoggle (j + 1) (by omega)
    have hmid := hlayer ⟨j + 1, by omega⟩
    change J.dist center (p.getVert (j + 1)) = k ∨
      J.dist center (p.getVert (j + 1)) = k + 1 at hmid
    have hmidNot : J.dist center (p.getVert (j + 1)) ≠ k := by
      intro hm
      have := h1.mp hm
      omega
    have hmidFar : J.dist center (p.getVert (j + 1)) = k + 1 := by
      rcases hmid with h | h
      · exact (hmidNot h).elim
      · exact h
    exact h2.mpr hmidFar
  by_cases hzero : J.dist center (p.getVert 0) = k
  · have htwo' := htwo
    have h2 : J.dist center (p.getVert 2) = k := htwo' 0 (by omega) hzero
    have h4 : J.dist center (p.getVert 4) = k := htwo' 2 (by omega) h2
    have h6 : J.dist center (p.getVert 6) = k := htwo' 4 (by omega) h4
    have h8 : J.dist center (p.getVert 8) = k := htwo' 6 (by omega) h6
    refine ⟨true, ?_⟩
    intro i
    fin_cases i
    · simpa [parityEmbedding] using hzero
    · simpa [parityEmbedding] using h2
    · simpa [parityEmbedding] using h4
    · simpa [parityEmbedding] using h6
    · simpa [parityEmbedding] using h8
  · have hzeroFar : J.dist center (p.getVert 0) = k + 1 := by
      rcases hlayer 0 with h | h
      · exact (hzero h).elim
      · exact h
    have h1 : J.dist center (p.getVert 1) = k :=
      (htoggle 0 (by omega)).2 hzeroFar
    have h3 : J.dist center (p.getVert 3) = k := htwo 1 (by omega) h1
    have h5 : J.dist center (p.getVert 5) = k := htwo 3 (by omega) h3
    have h7 : J.dist center (p.getVert 7) = k := htwo 5 (by omega) h5
    have h9 : J.dist center (p.getVert 9) = k := htwo 7 (by omega) h7
    refine ⟨false, ?_⟩
    intro i
    fin_cases i
    · simpa [parityEmbedding] using h1
    · simpa [parityEmbedding] using h3
    · simpa [parityEmbedding] using h5
    · simpa [parityEmbedding] using h7
    · simpa [parityEmbedding] using h9

/-- Ten of twenty Boolean-labelled stages have a common label. -/
theorem exists_ten_stages_of_same_bool (side : Fin 20 → Bool) :
    ∃ b : Bool, ∃ slot : Fin 10 ↪ Fin 20, ∀ k, side (slot k) = b := by
  classical
  let yes : Finset (Fin 20) := Finset.univ.filter fun i ↦ side i = true
  let no : Finset (Fin 20) := Finset.univ.filter fun i ↦ side i = false
  have hsum : yes.card + no.card = 20 := by
    simpa [yes, no] using (Finset.card_filter_add_card_filter_not
      (s := (Finset.univ : Finset (Fin 20))) (fun i ↦ side i = true))
  by_cases hy : 10 ≤ yes.card
  · obtain ⟨slot, hslot⟩ := Function.Embedding.exists_of_card_le_finset
        (s := yes) (by simpa using hy : Fintype.card (Fin 10) ≤ yes.card)
    refine ⟨true, slot, ?_⟩
    intro k
    simpa [yes] using hslot ⟨k, rfl⟩
  · have hn : 10 ≤ no.card := by omega
    obtain ⟨slot, hslot⟩ := Function.Embedding.exists_of_card_le_finset
        (s := no) (by simpa using hn : Fintype.card (Fin 10) ≤ no.card)
    refine ⟨false, slot, ?_⟩
    intro k
    simpa [no] using hslot ⟨k, rfl⟩

theorem exists_cliqueEdge_stages_of_same_bool (side : Fin 20 → Bool) :
    ∃ b : Bool, ∃ slot : CliqueEdge 5 ↪ Fin 20,
      ∀ e, side (slot e) = b := by
  obtain ⟨b, stage, hstage⟩ := exists_ten_stages_of_same_bool side
  have hcard : Fintype.card (CliqueEdge 5) = Fintype.card (Fin 10) := by
    rw [card_cliqueEdge]
    norm_num [Nat.choose]
  let edgeEquiv : CliqueEdge 5 ≃ Fin 10 := Fintype.equivOfCardEq hcard
  exact ⟨b, edgeEquiv.toEmbedding.trans stage,
    fun e ↦ hstage (edgeEquiv e)⟩

theorem nested_subset_of_succ_subset {V : Type*} {q : ℕ}
    (core : ℕ → Set V)
    (hnested : ∀ i, i < q → core (i + 1) ⊆ core i)
    {i j : ℕ} (hij : i ≤ j) (hjq : j ≤ q) :
    core j ⊆ core i := by
  induction j, hij using Nat.le_induction with
  | base => exact Subset.rfl
  | succ j _ ih =>
      exact (hnested j (Nat.lt_of_succ_le hjq)).trans
        (ih (Nat.le_trans (Nat.le_succ j) hjq))

/-- Annular routes in nested cores assemble into a clique subdivision. -/
theorem exists_boundedCliqueSubdivision_of_nested_routes
    {V : Type*} {G : SimpleGraph V} {t q R : ℕ}
    (core : ℕ → Set V)
    (hnested : ∀ i, i < q → core (i + 1) ⊆ core i)
    (branch : Fin t ↪ V)
    (hbranch : Set.range branch ⊆ core q)
    (slot : CliqueEdge t ↪ Fin q)
    (hroute : ∀ e : CliqueEdge t,
      ∃ p : G.Walk (branch e.1.1) (branch e.1.2),
        p.IsPath ∧ p.length ≤ R ∧
          walkInteriorSet p ⊆
            core (slot e).val \ core ((slot e).val + 1)) :
    ∃ s : CliqueSubdivision G t, ∀ e, (s.path e).length ≤ R := by
  choose path hpath hlength hinterior using hroute
  let s : CliqueSubdivision G t := {
    branch := branch
    path := path
    path_isPath := hpath
    interior_avoids_branch := by
      intro e
      rw [Set.disjoint_left]
      intro x hx hxb
      have hxq : x ∈ core q := hbranch hxb
      exact (hinterior e hx).2
        (nested_subset_of_succ_subset core hnested
          (Nat.succ_le_iff.mpr (slot e).isLt) le_rfl hxq)
    interior_pairwise := by
      intro e f hef
      rw [Set.disjoint_left]
      intro x hxe hxf
      have hsneq : slot e ≠ slot f := fun h ↦ hef (slot.injective h)
      rcases lt_or_gt_of_ne hsneq with hlt | hgt
      · exact (hinterior e hxe).2
          (nested_subset_of_succ_subset core hnested
            (Nat.succ_le_of_lt hlt) (Nat.le_of_lt (slot f).isLt)
            (hinterior f hxf).1)
      · exact (hinterior f hxf).2
          (nested_subset_of_succ_subset core hnested
            (Nat.succ_le_of_lt hgt) (Nat.le_of_lt (slot e).isLt)
            (hinterior e hxe).1)
  }
  exact ⟨s, hlength⟩

/-- A clique subdivision together with a bound on the vertices it uses. -/
def ContainsBoundedCliqueSubdivision {V : Type*} (G : SimpleGraph V)
    (r C : ℕ) : Prop :=
  ∃ s : CliqueSubdivision G r,
    (cliqueSubdivisionVerts s).ncard ≤ C

/-- Restrict a clique subdivision to an induced graph containing every
branch vertex and every vertex used by every route. -/
def restrictCliqueSubdivisionInduce {V : Type*} {G : SimpleGraph V}
    {U : Set V} {r : ℕ} (s : CliqueSubdivision G r)
    (hbranch : ∀ i, s.branch i ∈ U)
    (hpath : ∀ e x, x ∈ (s.path e).support → x ∈ U) :
    CliqueSubdivision (G.induce U) r := by
  let branch : Fin r ↪ U :=
    ⟨fun i => ⟨s.branch i, hbranch i⟩,
      fun _ _ hij => s.branch.injective (congrArg Subtype.val hij)⟩
  let path (e : CliqueEdge r) :=
    (s.path e).induce U (hpath e)
  have interior_image (e : CliqueEdge r) :
      Set.MapsTo Subtype.val (walkInteriorSet (path e))
        (walkInteriorSet (s.path e)) := by
    intro x hx
    rcases hx with ⟨hxsupp, hxstart, hxend⟩
    refine ⟨?_, ?_, ?_⟩
    · rw [Walk.support_induce] at hxsupp
      exact (List.mem_attachWith (hpath e) x).mp hxsupp
    · intro hxval
      apply hxstart
      apply Subtype.ext
      simpa [path, branch] using hxval
    · intro hxval
      apply hxend
      apply Subtype.ext
      simpa [path, branch] using hxval
  refine {
    branch := branch
    path := path
    path_isPath := ?_
    interior_avoids_branch := ?_
    interior_pairwise := ?_
  }
  · intro e
    rw [Walk.isPath_def, Walk.support_induce]
    apply (List.nodup_map_iff Subtype.val_injective).mp
    simpa [List.map_attachWith] using (s.path_isPath e).support_nodup
  · intro e
    rw [Set.disjoint_left]
    intro x hx hxbranch
    have hx' := interior_image e hx
    obtain ⟨i, hi⟩ := hxbranch
    have hval : (x : V) = s.branch i := by
      calc
        (x : V) = ((branch i : U) : V) := congrArg Subtype.val hi.symm
        _ = s.branch i := rfl
    exact (Set.disjoint_left.mp (s.interior_avoids_branch e)) hx'
      ⟨i, hval.symm⟩
  · intro e f hef
    rw [Set.disjoint_left]
    intro x hxe hxf
    exact (Set.disjoint_left.mp (s.interior_pairwise hef))
      (interior_image e hxe) (interior_image f hxf)

/-- The canonical induced subgraph on a vertex set. -/
def inducedSubgraph {V : Type*} (G : SimpleGraph V) (U : Set V) : G.Subgraph :=
  (⊤ : G.Subgraph).induce U

@[simp] theorem inducedSubgraph_verts {V : Type*} (G : SimpleGraph V)
    (U : Set V) : (inducedSubgraph G U).verts = U :=
  rfl

theorem inducedSubgraph_coe {V : Type*} (G : SimpleGraph V) (U : Set V) :
    (inducedSubgraph G U).coe = G.induce U := by
  exact (SimpleGraph.induce_eq_coe_induce_top U).symm

theorem containsCliqueSubdivision_inducedSubgraph
    {V : Type*} {G : SimpleGraph V} {U : Set V} {r : ℕ}
    (s : CliqueSubdivision G r)
    (hbranch : ∀ i, s.branch i ∈ U)
    (hpath : ∀ e x, x ∈ (s.path e).support → x ∈ U) :
    ContainsCliqueSubdivision (inducedSubgraph G U).coe r := by
  rw [inducedSubgraph_coe]
  exact ⟨restrictCliqueSubdivisionInduce s hbranch hpath⟩

/-- A `K₅` subdivision supported in `U` gives an induced non-planar
subgraph with vertex set exactly `U`. -/
theorem exists_inducedSubgraph_isNonplanar_of_clique_five
    {V : Type*} {G : SimpleGraph V} {U : Set V}
    (s : CliqueSubdivision G 5)
    (hbranch : ∀ i, s.branch i ∈ U)
    (hpath : ∀ e x, x ∈ (s.path e).support → x ∈ U) :
    ∃ S : G.Subgraph, S.verts = U ∧ IsNonplanar S.coe := by
  refine ⟨inducedSubgraph G U, rfl, Or.inl ?_⟩
  exact containsCliqueSubdivision_inducedSubgraph s hbranch hpath

/-! ### The exact Erdős statement -/

/-- Erdős Problem 1018, with `n`-vertex graphs represented on `Fin n`.

The quantifier order makes the vertex bound and the eventual threshold depend
only on `ε`.  The real power is `Real.rpow`. -/
def Erdos1018 : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ C N : ℕ, ∀ n : ℕ, N ≤ n →
    ∀ G : SimpleGraph (Fin n),
      (n : ℝ) ^ ((1 : ℝ) + ε) ≤ (G.edgeSet.ncard : ℝ) →
        ∃ S : G.Subgraph,
          S.verts.ncard ≤ C ∧ IsNonplanar S.coe

/-! ### The exponent-gap reduction -/

open Filter
open scoped Topology

/-- The fixed coefficient in the compact-subdivision theorem can be absorbed
by using a smaller positive exponent. -/
theorem exponent_gap (ε : ℝ) (hε : 0 < ε) :
    let δ := min (ε / 2) (1 / 2)
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      (4 : ℝ) ^ 25 * (n : ℝ) ^ (1 + δ) ≤ (n : ℝ) ^ (1 + ε) := by
  dsimp only
  let δ : ℝ := min (ε / 2) (1 / 2)
  let γ : ℝ := ε - δ
  have hδε : δ < ε := by
    exact lt_of_le_of_lt (min_le_left _ _) (by linarith)
  have hγ : 0 < γ := sub_pos.mpr hδε
  have hgrowth : Tendsto (fun n : ℕ ↦ (n : ℝ) ^ γ) atTop atTop :=
    (tendsto_rpow_atTop hγ).comp tendsto_natCast_atTop_atTop
  have hlarge : ∀ᶠ n : ℕ in atTop, (4 : ℝ) ^ 25 ≤ (n : ℝ) ^ γ :=
    hgrowth.eventually (eventually_ge_atTop ((4 : ℝ) ^ 25))
  rw [← eventually_atTop]
  filter_upwards [hlarge, eventually_ge_atTop (1 : ℕ)] with n hn hnone
  have hnpos : (0 : ℝ) < n := by
    exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hnone)
  calc
    (4 : ℝ) ^ 25 * (n : ℝ) ^ (1 + δ)
        ≤ (n : ℝ) ^ γ * (n : ℝ) ^ (1 + δ) :=
      mul_le_mul_of_nonneg_right hn (Real.rpow_nonneg hnpos.le _)
    _ = (n : ℝ) ^ (1 + ε) := by
      rw [← Real.rpow_add hnpos]
      congr 1
      dsimp [γ]
      ring

/-! ### A bipartite subgraph retaining half the edges -/

section MaximumCut

noncomputable local instance graphEdgeFintype {V : Type*} [Finite V]
    (G : SimpleGraph V) : Fintype G.edgeSet :=
  Fintype.ofFinite G.edgeSet

private def flipAt {V : Type*} [DecidableEq V]
    (u : V) (c : V → Bool) : V → Bool :=
  Function.update c u (!(c u))

private lemma flipAt_apply_self {V : Type*} [DecidableEq V]
    (u : V) (c : V → Bool) : flipAt u c u = !(c u) := by
  simp [flipAt]

private lemma flipAt_apply_of_ne {V : Type*} [DecidableEq V]
    {u v : V} (huv : u ≠ v) (c : V → Bool) :
    flipAt u c v = c v := by
  simp [flipAt, Ne.symm huv]

private lemma flipAt_involutive {V : Type*} [DecidableEq V] (u : V) :
    Function.Involutive (flipAt u : (V → Bool) → V → Bool) := by
  intro c
  funext v
  by_cases huv : u = v
  · subst v
    simp [flipAt]
  · simp [flipAt]

private lemma flipAt_ne_iff_eq {V : Type*} [DecidableEq V]
    {u v : V} (huv : u ≠ v) (c : V → Bool) :
    flipAt u c u ≠ flipAt u c v ↔ c u = c v := by
  rw [flipAt_apply_self, flipAt_apply_of_ne huv]
  cases c u <;> cases c v <;> decide

private lemma card_colorings_ne_eq_half {V : Type*} [Fintype V]
    [DecidableEq V] {u v : V} (huv : u ≠ v) :
    2 * #(Finset.univ.filter fun c : V → Bool ↦ c u ≠ c v) =
      Fintype.card (V → Bool) := by
  let neColors := Finset.univ.filter fun c : V → Bool ↦ c u ≠ c v
  let eqColors := Finset.univ.filter fun c : V → Bool ↦ c u = c v
  have hcard : #neColors = #eqColors := by
    apply Finset.card_bij (fun c _ ↦ flipAt u c)
    · intro c hc
      simp only [eqColors, Finset.mem_filter, Finset.mem_univ, true_and]
      apply not_ne_iff.mp
      rw [flipAt_ne_iff_eq huv]
      simpa [neColors] using hc
    · intro c₁ _ c₂ _ h
      exact (flipAt_involutive u).injective h
    · intro d hd
      refine ⟨flipAt u d, ?_, ?_⟩
      · simp only [neColors, Finset.mem_filter, Finset.mem_univ, true_and]
        have hd' : d u = d v := by simpa [eqColors] using hd
        exact (flipAt_ne_iff_eq huv _).mpr hd'
      · exact flipAt_involutive u d
  have hpartition : #neColors + #eqColors = Fintype.card (V → Bool) := by
    rw [← Finset.card_union_of_disjoint]
    · congr 1
      ext c
      simp only [neColors, eqColors, Finset.mem_union, Finset.mem_filter,
        Finset.mem_univ, true_and]
      exact iff_true_intro (ne_or_eq (c u) (c v))
    · refine Finset.disjoint_left.mpr ?_
      intro c hcne hceq
      simp only [neColors, Finset.mem_filter, Finset.mem_univ, true_and] at hcne
      simp only [eqColors, Finset.mem_filter, Finset.mem_univ, true_and] at hceq
      exact hcne hceq
  simpa [neColors, hcard, two_mul] using hpartition

private def colorSet {V : Type*} (c : V → Bool) : Set V :=
  {v | c v = true}

private def cutGraph {V : Type*} (G : SimpleGraph V)
    (c : V → Bool) : SimpleGraph V :=
  G.between (colorSet c) (colorSet c)ᶜ

private lemma mk_mem_cutGraph_edgeFinset_iff {V : Type*} [Fintype V]
    [DecidableEq V] (G : SimpleGraph V) (c : V → Bool)
    {u v : V} (he : s(u, v) ∈ G.edgeFinset) :
    s(u, v) ∈ (cutGraph G c).edgeFinset ↔ c u ≠ c v := by
  classical
  have hadj : G.Adj u v := by simpa using he
  rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet]
  simp only [cutGraph, SimpleGraph.between_adj, colorSet, Set.mem_ofPred_eq,
    Set.mem_compl_iff, hadj, true_and]
  cases c u <;> cases c v <;> decide

private lemma cutGraph_edgeFinset_eq_filter {V : Type*} [Fintype V]
    [DecidableEq V] (G : SimpleGraph V) (c : V → Bool) :
    (cutGraph G c).edgeFinset =
      G.edgeFinset.filter fun e ↦ e ∈ (cutGraph G c).edgeFinset := by
  classical
  ext e
  simp only [Finset.mem_filter]
  constructor
  · intro he
    exact ⟨SimpleGraph.edgeFinset_mono SimpleGraph.between_le he, he⟩
  · exact And.right

private lemma card_colorings_edge_in_cut_eq_half {V : Type*} [Fintype V]
    [DecidableEq V] (G : SimpleGraph V) {e : Sym2 V}
    (he : e ∈ G.edgeFinset) :
    2 * #(Finset.univ.filter fun c : V → Bool ↦
      e ∈ (cutGraph G c).edgeFinset) = Fintype.card (V → Bool) := by
  classical
  induction e using Sym2.inductionOn with
  | _ u v =>
      have hadj : G.Adj u v := by simpa using he
      rw [← card_colorings_ne_eq_half hadj.ne]
      congr 2
      ext c
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact mk_mem_cutGraph_edgeFinset_iff G c he

private lemma sum_cutGraph_edge_card_double {V : Type*} [Fintype V]
    [DecidableEq V] (G : SimpleGraph V) :
    (∑ c : V → Bool, 2 * #(cutGraph G c).edgeFinset) =
      Fintype.card (V → Bool) * #G.edgeFinset := by
  classical
  calc
    (∑ c : V → Bool, 2 * #(cutGraph G c).edgeFinset) =
        ∑ c : V → Bool, ∑ e ∈ G.edgeFinset,
          if e ∈ (cutGraph G c).edgeFinset then 2 else 0 := by
      apply Finset.sum_congr rfl
      intro c _
      rw [cutGraph_edgeFinset_eq_filter, Finset.card_eq_sum_ones,
        Finset.mul_sum, Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro e he
      by_cases hcut : e ∈ (cutGraph G c).edgeFinset
      · have hcut' : e ∈ (cutGraph G c).edgeSet :=
          SimpleGraph.mem_edgeFinset.mp hcut
        simp [he, hcut, hcut']
      · have hcut' : e ∉ (cutGraph G c).edgeSet := fun he' ↦
          hcut (SimpleGraph.mem_edgeFinset.mpr he')
        simp [he, hcut, hcut']
    _ = ∑ e ∈ G.edgeFinset, ∑ c : V → Bool,
          if e ∈ (cutGraph G c).edgeFinset then 2 else 0 := by
      rw [Finset.sum_comm]
    _ = ∑ _e ∈ G.edgeFinset, Fintype.card (V → Bool) := by
      apply Finset.sum_congr rfl
      intro e he
      calc
        (∑ c : V → Bool,
            if e ∈ (cutGraph G c).edgeFinset then 2 else 0) =
            2 * ∑ c : V → Bool,
              if e ∈ (cutGraph G c).edgeFinset then 1 else 0 := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro c _
          by_cases hcut : e ∈ (cutGraph G c).edgeFinset <;> simp [hcut]
        _ = 2 * #(Finset.univ.filter fun c : V → Bool ↦
              e ∈ (cutGraph G c).edgeFinset) := by
          simp only [SimpleGraph.mem_edgeFinset]
          rw [Finset.sum_boole]
          simp
        _ = Fintype.card (V → Bool) :=
          card_colorings_edge_in_cut_eq_half G he
    _ = Fintype.card (V → Bool) * #G.edgeFinset := by
      simp [Nat.mul_comm]

/-- Every finite graph has a bipartite spanning subgraph containing at least
half of its edges. -/
theorem exists_bipartite_spanning_subgraph_half_edges
    {V : Type*} [Fintype V] (G : SimpleGraph V) :
    ∃ B : SimpleGraph V, B ≤ G ∧ B.IsBipartite ∧
      G.edgeSet.ncard ≤ 2 * B.edgeSet.ncard := by
  classical
  have hex : ∃ c : V → Bool,
      #G.edgeFinset ≤ 2 * #(cutGraph G c).edgeFinset := by
    by_contra! h
    have hsum_lt :
        (∑ c : V → Bool, 2 * #(cutGraph G c).edgeFinset) <
          ∑ _c : V → Bool, #G.edgeFinset := by
      apply Finset.sum_lt_sum
      · intro c _
        exact (h c).le
      · exact ⟨fun _ ↦ false, Finset.mem_univ _, h _⟩
    rw [sum_cutGraph_edge_card_double] at hsum_lt
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at hsum_lt
    exact lt_irrefl _ hsum_lt
  obtain ⟨c, hc⟩ := hex
  refine ⟨cutGraph G c, SimpleGraph.between_le,
    SimpleGraph.between_isBipartite disjoint_compl_right, ?_⟩
  rw [Set.ncard_eq_toFinset_card', Set.ncard_eq_toFinset_card']
  exact hc

end MaximumCut

/-! ### Fixed-host nested layer chains -/

noncomputable section

universe u

variable {V : Type u}

/-- The per-stage ball-growth factor. -/
def KPGrowth (n r : ℕ) : ℝ :=
  (n : ℝ) ^ ((1 : ℝ) / (r : ℝ))

/-- The exact coefficient retained after `i` radius/layer steps. -/
def KPCoeff (n : ℕ) (δ : ℝ) (r i : ℕ) : ℝ :=
  (4 : ℝ) ^ (25 - i) * (n : ℝ) ^ δ / (KPGrowth n r) ^ i

/-- The denominator-free density invariant at stage `i`.  The reference
cardinality `n` is fixed through the nested construction. -/
def KPDense {G : SimpleGraph V} (n : ℕ) (δ : ℝ) (r i : ℕ)
    (H : G.Subgraph) : Prop :=
  H.verts.Nonempty ∧
    KPCoeff n δ r i * (H.verts.ncard : ℝ) ≤
      2 * (H.edgeSet.ncard : ℝ)

/-- The density invariant together with the bipartiteness needed by the layer
averaging step. -/
def KPInvariant {G : SimpleGraph V} (n : ℕ) (δ : ℝ) (r i : ℕ)
    (H : G.Subgraph) : Prop :=
  H.coe.IsBipartite ∧ KPDense n δ r i H

lemma kpGrowth_pos (n r : ℕ) (hn : 0 < n) : 0 < KPGrowth n r := by
  exact Real.rpow_pos_of_pos (by exact_mod_cast hn) _

lemma one_le_kpGrowth (n r : ℕ) (hn : 0 < n) (hr : 0 < r) :
    1 ≤ KPGrowth n r := by
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hexp : (0 : ℝ) ≤ (1 : ℝ) / (r : ℝ) := by positivity
  simpa [KPGrowth] using Real.rpow_le_rpow_of_exponent_le hn1 hexp

lemma kpGrowth_pow (n r : ℕ) (hn : 0 < n) (hr : 0 < r) :
    (KPGrowth n r) ^ r = (n : ℝ) := by
  have hnnonneg : (0 : ℝ) ≤ n := by positivity
  have hmul : (1 : ℝ) / (r : ℝ) * (r : ℝ) = 1 := by
    field_simp
  have h := Real.rpow_mul_natCast hnnonneg ((1 : ℝ) / (r : ℝ)) r
  rw [hmul, Real.rpow_one] at h
  simpa [KPGrowth] using h.symm

lemma kpCoeff_pos (n : ℕ) (δ : ℝ) (r i : ℕ) (hn : 0 < n) :
    0 < KPCoeff n δ r i := by
  unfold KPCoeff
  positivity [kpGrowth_pos n r hn]

lemma kpCoeff_step (n : ℕ) (δ : ℝ) (r i : ℕ)
    (hi : i < 20) (hn : 0 < n) :
    KPCoeff n δ r i / (4 * KPGrowth n r) =
      KPCoeff n δ r (i + 1) := by
  have hsub : 25 - i = (25 - (i + 1)) + 1 := by omega
  have ha : KPGrowth n r ≠ 0 := ne_of_gt (kpGrowth_pos n r hn)
  unfold KPCoeff
  rw [hsub, pow_succ, pow_succ]
  field_simp

lemma kpCoeff_twenty_ge (n r : ℕ) (δ : ℝ)
    (hn : 0 < n) (hr : 0 < r)
    (hratio : (20 : ℝ) / (r : ℝ) ≤ δ) :
    (4 : ℝ) ^ 5 ≤ KPCoeff n δ r 20 := by
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hnnonneg : (0 : ℝ) ≤ n := by positivity
  have ha0 : 0 < KPGrowth n r := kpGrowth_pos n r hn
  have hpow20 : (KPGrowth n r) ^ 20 =
      (n : ℝ) ^ ((20 : ℝ) / (r : ℝ)) := by
    have h := Real.rpow_mul_natCast hnnonneg ((1 : ℝ) / (r : ℝ)) 20
    calc
      (KPGrowth n r) ^ 20 =
          (n : ℝ) ^ ((1 : ℝ) / (r : ℝ) * (20 : ℝ)) := by
        simpa [KPGrowth] using h.symm
      _ = (n : ℝ) ^ ((20 : ℝ) / (r : ℝ)) := by
        congr 1
        ring
  have hpowers : (KPGrowth n r) ^ 20 ≤ (n : ℝ) ^ δ := by
    rw [hpow20]
    exact Real.rpow_le_rpow_of_exponent_le hn1 hratio
  have hquot : 1 ≤ (n : ℝ) ^ δ / (KPGrowth n r) ^ 20 := by
    rw [le_div_iff₀ (pow_pos ha0 20)]
    simpa using hpowers
  unfold KPCoeff
  norm_num
  calc
    (1024 : ℝ) = 1024 * 1 := by ring
    _ ≤ 1024 * ((n : ℝ) ^ δ / KPGrowth n r ^ 20) :=
      mul_le_mul_of_nonneg_left hquot (by norm_num)
    _ = 1024 * (n : ℝ) ^ δ / KPGrowth n r ^ 20 := by ring

/-- A distance layer of a host subgraph, re-embedded in the host type. -/
abbrev hostLayer {G : SimpleGraph V} (J : G.Subgraph) (z : J.verts)
    (k : ℕ) : Set V :=
  Erdos1018Aux.hostLayer J z k

/-- The data produced by one bounded-radius/consecutive-layer step. -/
structure DensityLayerStep (G : SimpleGraph V) (r : ℕ)
    (before after : G.Subgraph) where
  J : G.Subgraph
  J_le : J ≤ before
  after_le : after ≤ J
  center : J.verts
  connected : J.coe.Connected
  bipartite : J.coe.IsBipartite
  radius_le : J.coe.radius ≤ (r : ℕ∞)
  center_dist_le : ∀ v : J.verts, J.coe.dist center v ≤ r
  k : ℕ
  layer_eq : after =
    J.induce (hostLayer J center k ∪ hostLayer J center (k + 1))

/-- Re-embed a finite set of vertices of a subgraph in the fixed host type. -/
def hostFinset {G : SimpleGraph V} (H : G.Subgraph)
    (S : Finset H.verts) : Set V :=
  {x | ∃ hx : x ∈ H.verts, (⟨x, hx⟩ : H.verts) ∈ S}

lemma hostFinset_subset_verts {G : SimpleGraph V} (H : G.Subgraph)
    (S : Finset H.verts) : hostFinset H S ⊆ H.verts := by
  rintro x ⟨hx, _⟩
  exact hx

lemma hostFinset_preimage {G : SimpleGraph V} (H : G.Subgraph)
    (S : Finset H.verts) :
    {x : H.verts | (x : V) ∈ hostFinset H S} = (S : Set H.verts) := by
  ext x
  constructor
  · rintro ⟨hx, hmem⟩
    have heq : (⟨(x : V), hx⟩ : H.verts) = x := Subtype.ext rfl
    simpa [heq] using hmem
  · intro hx
    refine ⟨x.property, ?_⟩
    have heq : (⟨(x : V), x.property⟩ : H.verts) = x := Subtype.ext rfl
    simpa [heq] using hx

lemma induce_hostFinset_le {G : SimpleGraph V} (H : G.Subgraph)
    (S : Finset H.verts) : H.induce (hostFinset H S) ≤ H := by
  calc
    H.induce (hostFinset H S) ≤ H.induce H.verts :=
      SimpleGraph.Subgraph.induce_mono_right (hostFinset_subset_verts H S)
    _ = H := SimpleGraph.Subgraph.induce_self_verts

/-- Host-subgraph form of the real bounded-radius density lemma. -/
theorem exists_host_bounded_radius_dense [Fintype V]
    {G : SimpleGraph V} (H : G.Subgraph)
    (D a : ℝ) (r : ℕ) (hD : 0 < D) (ha : 1 ≤ a) (hr : 0 < r)
    (hH : H.verts.Nonempty)
    (hpow : (H.verts.ncard : ℝ) ≤ a ^ r)
    (havg : D * (H.verts.ncard : ℝ) ≤
      2 * (H.edgeSet.ncard : ℝ)) :
    ∃ J : G.Subgraph, J ≤ H ∧
      ∃ center : J.verts,
        J.coe.Connected ∧ J.coe.radius ≤ (r : ℕ∞) ∧
          (∀ v : J.verts, J.coe.dist center v ≤ r) ∧
          (D / (2 * a)) * (J.verts.ncard : ℝ) ≤
            2 * (J.edgeSet.ncard : ℝ) := by
  classical
  letI : Fintype H.verts := Fintype.ofFinite H.verts
  letI : DecidableRel H.coe.Adj := Classical.decRel _
  have hcard : Fintype.card H.verts = H.verts.ncard := by
    rw [← Nat.card_eq_fintype_card, Nat.card_coe_set_eq]
  have hpos : 0 < Fintype.card H.verts := by
    exact Fintype.card_pos_iff.mpr ⟨hH.choose, hH.choose_spec⟩
  have hpow' : (Fintype.card H.verts : ℝ) ≤ a ^ r := by
    simpa [hcard] using hpow
  have havg' : D * (Fintype.card H.verts : ℝ) ≤
      2 * (#H.coe.edgeFinset : ℝ) := by
    have hedge : #H.coe.edgeFinset = H.edgeSet.ncard :=
      Erdos1018Aux.edgeFinset_card_eq_edgeSet_ncard H
    simpa only [hcard, hedge] using havg
  obtain ⟨S, z, hSne, hzS, hconn, hpaths, hdense⟩ :=
    Erdos1018Aux.bounded_radius_density H.coe D a r hD ha hr hpos hpow' havg'
  let U : Set V := hostFinset H S
  let J : G.Subgraph := H.induce U
  have hU : U ⊆ H.verts := by
    simpa [U] using hostFinset_subset_verts H S
  let T : Set H.verts := {x | (x : V) ∈ U}
  have hT : T = (S : Set H.verts) := by
    simpa [T, U] using hostFinset_preimage H S
  let e : J.coe ≃g H.coe.induce T := H.coeInduceIso U hU
  have hzT : z ∈ T := by
    rw [hT]
    exact hzS
  let zT : T := ⟨z, hzT⟩
  let center : J.verts := e.symm zT
  have hconnT : (H.coe.induce T).Connected := by
    rw [hT]
    exact hconn
  have hconnJ : J.coe.Connected := e.connected_iff.mpr hconnT
  have hcenterDist (v : J.verts) : J.coe.dist center v ≤ r := by
    have hvS : ((e v : T) : H.verts) ∈ S := by
      have hvU : ((((e v : T) : H.verts) : V)) ∈ U := (e v).property
      rcases hvU with ⟨hx, hmem⟩
      have heq :
          (⟨((((e v : T) : H.verts) : V)), hx⟩ : H.verts) =
            ((e v : T) : H.verts) := Subtype.ext rfl
      simpa [heq] using hmem
    obtain ⟨p, hplen, hpsupp⟩ := hpaths _ hvS
    have hpT : ∀ x ∈ p.support, x ∈ T := by
      intro x hx
      rw [hT]
      exact hpsupp x hx
    let pTi := p.induce T hpT
    let pT : (H.coe.induce T).Walk zT (e v) :=
      pTi.copy (Subtype.ext rfl) (Subtype.ext rfl)
    let q0 := pT.map e.symm.toHom
    let q : J.coe.Walk center v :=
      q0.copy rfl (e.symm_apply_apply v)
    calc
      J.coe.dist center v ≤ q.length := SimpleGraph.dist_le q
      _ = pT.length := by simp [q, q0]
      _ = pTi.length := by simp [pT]
      _ = p.length := Erdos1018Aux.length_induce_eq H.coe p hpT
      _ ≤ r := hplen
  have hradius : J.coe.radius ≤ (r : ℕ∞) := by
    calc
      J.coe.radius ≤ J.coe.eccent center := SimpleGraph.radius_le_eccent
      _ ≤ (r : ℕ∞) := by
        rw [SimpleGraph.eccent_le_iff]
        intro v
        have hreach : J.coe.Reachable center v := hconnJ.preconnected center v
        rw [← hreach.coe_dist_eq_edist]
        exact ENat.natCast_le_natCast.mpr (hcenterDist v)
  have hJverts : J.verts.ncard = S.card := by
    change Nat.card J.verts = S.card
    calc
      Nat.card J.verts = Nat.card T := Nat.card_congr e.toEquiv
      _ = T.ncard := Nat.card_coe_set_eq T
      _ = (S : Set H.verts).ncard := congrArg Set.ncard hT
      _ = S.card := Set.ncard_coe_finset S
  have hJedges : J.edgeSet.ncard =
      (H.coe.induce (S : Set H.verts)).edgeSet.ncard := by
    calc
      J.edgeSet.ncard = J.coe.edgeSet.ncard :=
        Erdos1018Aux.edgeSet_ncard_coe J
      _ = (H.coe.induce T).edgeSet.ncard := Nat.card_congr e.mapEdgeSet
      _ = (H.coe.induce (S : Set H.verts)).edgeSet.ncard := by rw [hT]
  have hdense' : (D / (2 * a)) * (J.verts.ncard : ℝ) ≤
      2 * (J.edgeSet.ncard : ℝ) := by
    have hedge : #(H.coe.induce (S : Set H.verts)).edgeFinset =
        (H.coe.induce (S : Set H.verts)).edgeSet.ncard := by
      rw [SimpleGraph.edgeFinset_card, ← Nat.card_eq_fintype_card,
        Nat.card_coe_set_eq]
    calc
      (D / (2 * a)) * (J.verts.ncard : ℝ) =
          (D / (2 * a)) * (S.card : ℝ) := by rw [hJverts]
      _ ≤ 2 * (#(H.coe.induce (S : Set H.verts)).edgeFinset : ℝ) := hdense
      _ = 2 * (J.edgeSet.ncard : ℝ) := by rw [hJedges, hedge]
  refine ⟨J, ?_, center, hconnJ, hradius, hcenterDist, hdense'⟩
  simpa [J, U] using induce_hostFinset_le H S

lemma isBipartite_subgraph_of_le {G : SimpleGraph V}
    {A B : G.Subgraph} (hAB : A ≤ B) (hB : B.coe.IsBipartite) :
    A.coe.IsBipartite :=
  ⟨hB.some.comp (SimpleGraph.Subgraph.inclusion hAB)⟩

/-- One exact Kostochka--Pyber radius/layer refinement step. -/
theorem kp_successor [Fintype V] {G : SimpleGraph V}
    (n : ℕ) (hcardV : Fintype.card V = n) (δ : ℝ) (r i : ℕ)
    (hn : 0 < n) (hr : 0 < r) (hi : i < 20)
    (H : G.Subgraph) (hInv : KPInvariant n δ r i H) :
    ∃ K : G.Subgraph, Nonempty (DensityLayerStep G r H K) ∧
      KPInvariant n δ r (i + 1) K := by
  classical
  let a := KPGrowth n r
  let D := KPCoeff n δ r i
  have ha : 1 ≤ a := one_le_kpGrowth n r hn hr
  have ha0 : 0 < a := lt_of_lt_of_le zero_lt_one ha
  have hD : 0 < D := kpCoeff_pos n δ r i hn
  have hHcard : H.verts.ncard ≤ n := by
    calc
      H.verts.ncard ≤ Set.univ.ncard := Set.ncard_le_ncard (Set.subset_univ _)
      _ = Nat.card V := Set.ncard_univ V
      _ = Fintype.card V := Nat.card_eq_fintype_card
      _ = n := hcardV
  have hpow : (H.verts.ncard : ℝ) ≤ a ^ r := by
    have hcast : (H.verts.ncard : ℝ) ≤ n := by exact_mod_cast hHcard
    simpa [a, kpGrowth_pow n r hn hr] using hcast
  obtain ⟨hHbip, hHne, hHdense⟩ := hInv
  obtain ⟨J, hJle, center, hJconn, hJradius, hJcenterDist, hJdense⟩ :=
    exists_host_bounded_radius_dense H D a r hD ha hr hHne hpow hHdense
  have hJbip : J.coe.IsBipartite :=
    isBipartite_subgraph_of_le hJle hHbip
  have hJcardpos : 0 < (J.verts.ncard : ℝ) := by
    have hnat : 0 < Nat.card J.verts :=
      Nat.card_pos_iff.mpr ⟨⟨center⟩, inferInstance⟩
    have hncard : 0 < J.verts.ncard := by
      simpa only [Nat.card_coe_set_eq] using hnat
    exact_mod_cast hncard
  have hJedgepos : 0 < J.edgeSet.ncard := by
    have hleft : 0 < (D / (2 * a)) * (J.verts.ncard : ℝ) := by positivity
    have hright : 0 < 2 * (J.edgeSet.ncard : ℝ) := hleft.trans_le hJdense
    exact_mod_cast (by nlinarith : (0 : ℝ) < J.edgeSet.ncard)
  obtain ⟨k, _hk, hKne, hLayer⟩ :=
    Erdos1018Aux.exists_host_pairedLayers_half_average
      J hJconn hJbip hJedgepos center
  let U := hostLayer J center k ∪ hostLayer J center (k + 1)
  let K : G.Subgraph := J.induce U
  have hU : U ⊆ J.verts := by
    simpa [U] using Erdos1018Aux.hostLayer_pair_subset_verts J center k
  have hKleJ : K ≤ J := by
    calc
      K ≤ J.induce J.verts :=
        SimpleGraph.Subgraph.induce_mono_right hU
      _ = J := SimpleGraph.Subgraph.induce_self_verts
  have hKbip : K.coe.IsBipartite :=
    isBipartite_subgraph_of_le hKleJ hJbip
  have hLayerR :
      (J.edgeSet.ncard : ℝ) * (K.verts.ncard : ℝ) ≤
        2 * (K.edgeSet.ncard : ℝ) * (J.verts.ncard : ℝ) := by
    exact_mod_cast hLayer
  have hmul1 := mul_le_mul_of_nonneg_right hJdense
    (show (0 : ℝ) ≤ K.verts.ncard by positivity)
  have hmul2 := mul_le_mul_of_nonneg_left hLayerR (show (0 : ℝ) ≤ 2 by norm_num)
  have hprod :
      ((D / (2 * a)) * (K.verts.ncard : ℝ)) * (J.verts.ncard : ℝ) ≤
        (4 * (K.edgeSet.ncard : ℝ)) * (J.verts.ncard : ℝ) := by
    nlinarith [hmul1, hmul2]
  have hcancel : (D / (2 * a)) * (K.verts.ncard : ℝ) ≤
      4 * (K.edgeSet.ncard : ℝ) :=
    le_of_mul_le_mul_right hprod hJcardpos
  have hnextdense : KPCoeff n δ r (i + 1) * (K.verts.ncard : ℝ) ≤
      2 * (K.edgeSet.ncard : ℝ) := by
    rw [← kpCoeff_step n δ r i hi hn]
    have heq : D / (4 * a) = (D / (2 * a)) / 2 := by
      field_simp
      norm_num
    change (D / (4 * a)) * (K.verts.ncard : ℝ) ≤ _
    rw [heq]
    nlinarith
  refine ⟨K, ⟨?_⟩, hKbip, hKne, hnextdense⟩
  exact {
    J := J
    J_le := hJle
    after_le := hKleJ
    center := center
    connected := hJconn
    bipartite := hJbip
    radius_le := hJradius
    center_dist_le := hJcenterDist
    k := k
    layer_eq := rfl
  }

/-- A finite chain of subgraphs of one host. -/
structure HostSubgraphChain (G : SimpleGraph V)
    (Inv : ℕ → G.Subgraph → Prop)
    (Step : G.Subgraph → G.Subgraph → Type*) (N : ℕ) where
  H : Fin (N + 1) → G.Subgraph
  transition : ∀ i : Fin N, Step (H i.castSucc) (H i.succ)
  invariant : ∀ i : Fin (N + 1), Inv i.val (H i)

namespace HostSubgraphChain

variable {G : SimpleGraph V}
variable {Inv : ℕ → G.Subgraph → Prop}
variable {Step : G.Subgraph → G.Subgraph → Type*}

def singleton (H0 : G.Subgraph) (h0 : Inv 0 H0) :
    HostSubgraphChain G Inv Step 0 where
  H := fun _ => H0
  transition := fun i => Fin.elim0 i
  invariant := by
    intro i
    simpa using h0

def snoc {N : ℕ} (C : HostSubgraphChain G Inv Step N)
    (next : G.Subgraph) (newStep : Step (C.H (Fin.last N)) next)
    (hnext : Inv (N + 1) next) :
    HostSubgraphChain G Inv Step (N + 1) where
  H := Fin.snoc C.H next
  transition := by
    intro i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simpa using newStep
    · have hidx : j.castSucc.succ = j.succ.castSucc :=
        (Fin.castSucc_succ j).symm
      rw [hidx]
      simpa only [Fin.snoc_castSucc] using C.transition j
  invariant := by
    intro i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simpa using hnext
    · simpa using C.invariant j

@[simp] theorem snoc_H_castSucc {N : ℕ}
    (C : HostSubgraphChain G Inv Step N)
    (next : G.Subgraph) (newStep : Step (C.H (Fin.last N)) next)
    (hnext : Inv (N + 1) next) (i : Fin (N + 1)) :
    (C.snoc next newStep hnext).H i.castSucc = C.H i := by
  simp [snoc]

/-- Iterate a one-step theorem exactly `N` times. -/
theorem exists_of_successor_bounded
    (N : ℕ) (H0 : G.Subgraph) (h0 : Inv 0 H0)
    (successor : ∀ (i : ℕ), i < N → ∀ (H : G.Subgraph), Inv i H →
      ∃ K : G.Subgraph, Nonempty (Step H K) ∧ Inv (i + 1) K) :
    ∃ C : HostSubgraphChain G Inv Step N, C.H 0 = H0 := by
  suffices ∀ k : ℕ, k ≤ N →
      ∃ C : HostSubgraphChain G Inv Step k, C.H 0 = H0 from
    this N le_rfl
  intro k
  induction k with
  | zero =>
      intro _
      exact ⟨singleton H0 h0, rfl⟩
  | succ k ih =>
      intro hkN
      obtain ⟨C, hfirst⟩ := ih (Nat.le_trans (Nat.le_succ k) hkN)
      have hlast : Inv k (C.H (Fin.last k)) := by
        simpa using C.invariant (Fin.last k)
      obtain ⟨K, ⟨s⟩, hK⟩ :=
        successor k (Nat.lt_of_succ_le hkN) (C.H (Fin.last k)) hlast
      let C' := C.snoc K s (by simpa [Nat.add_comm] using hK)
      refine ⟨C', ?_⟩
      change (C.snoc K s _).H (0 : Fin (k + 2)) = H0
      rw [show (0 : Fin (k + 2)) = (0 : Fin (k + 1)).castSucc by rfl,
        snoc_H_castSucc]
      exact hfirst

end HostSubgraphChain

/-- The twenty-stage chain used for `K₅`. -/
abbrev TwentyStageDensityChain (G : SimpleGraph V) (r : ℕ)
    (Inv : ℕ → G.Subgraph → Prop) :=
  HostSubgraphChain G Inv (DensityLayerStep G r) 20

namespace TwentyStageDensityChain

variable {G : SimpleGraph V} {r : ℕ}
variable {Inv : ℕ → G.Subgraph → Prop}

theorem antitone (C : TwentyStageDensityChain G r Inv) : Antitone C.H := by
  rw [Fin.antitone_iff_succ_le]
  intro i
  exact (C.transition i).after_le.trans (C.transition i).J_le

theorem later_le_earlier (C : TwentyStageDensityChain G r Inv)
    {i j : Fin 21} (hij : i ≤ j) : C.H j ≤ C.H i :=
  C.antitone hij

end TwentyStageDensityChain

/-! ### Constructing the twenty nested stages -/

theorem exists_twentyStageDensityChain
    (n : ℕ) (hn : 0 < n) (δ : ℝ) (r : ℕ) (hr : 0 < r)
    (G : SimpleGraph (Fin n))
    (hE : (4 : ℝ) ^ 25 * (n : ℝ) ^ ((1 : ℝ) + δ) ≤
      (G.edgeSet.ncard : ℝ)) :
    ∃ C : TwentyStageDensityChain G r (KPInvariant n δ r), True := by
  classical
  obtain ⟨B, hBG, hBbip, hhalf⟩ :=
    exists_bipartite_spanning_subgraph_half_edges G
  let H0 : G.Subgraph := SimpleGraph.toSubgraph B hBG
  have hH0verts : H0.verts = Set.univ := by
    simpa [H0] using SimpleGraph.toSubgraph_verts B hBG
  have hH0card : H0.verts.ncard = n := by
    rw [hH0verts, Set.ncard_univ, Nat.card_eq_fintype_card]
    simp
  have hH0ne : H0.verts.Nonempty := by
    obtain ⟨v : Fin n⟩ := Fin.pos_iff_nonempty.mp hn
    rw [hH0verts]
    exact ⟨v, Set.mem_univ v⟩
  have hH0edges : H0.edgeSet = B.edgeSet := by
    ext e
    induction e using Sym2.inductionOn with
    | hf u v => rfl
  have hH0bip : H0.coe.IsBipartite := by
    have hspan : H0.IsSpanning := by
      intro v
      rw [hH0verts]
      exact Set.mem_univ v
    let e := H0.spanningCoeEquivCoeOfSpanning hspan
    refine ⟨hBbip.some.comp e.symm.toHom⟩
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  have hpowequal : (n : ℝ) ^ δ * n = (n : ℝ) ^ ((1 : ℝ) + δ) := by
    calc
      (n : ℝ) ^ δ * n = (n : ℝ) ^ δ * (n : ℝ) ^ (1 : ℝ) := by
        rw [Real.rpow_one]
      _ = (n : ℝ) ^ (δ + 1) := (Real.rpow_add hnpos δ 1).symm
      _ = (n : ℝ) ^ ((1 : ℝ) + δ) := by ring_nf
  have hH0dense : KPDense n δ r 0 H0 := by
    refine ⟨hH0ne, ?_⟩
    have hhalfR : (G.edgeSet.ncard : ℝ) ≤
        2 * (B.edgeSet.ncard : ℝ) := by exact_mod_cast hhalf
    unfold KPCoeff
    simp only [Nat.sub_zero, pow_zero, div_one]
    rw [hH0card, hH0edges]
    calc
      (4 : ℝ) ^ 25 * (n : ℝ) ^ δ * n =
          (4 : ℝ) ^ 25 * ((n : ℝ) ^ δ * n) := by ring
      _ = (4 : ℝ) ^ 25 * (n : ℝ) ^ ((1 : ℝ) + δ) := by
        rw [hpowequal]
      _ ≤ (G.edgeSet.ncard : ℝ) := hE
      _ ≤ 2 * (B.edgeSet.ncard : ℝ) := hhalfR
  have hH0inv : KPInvariant n δ r 0 H0 := ⟨hH0bip, hH0dense⟩
  obtain ⟨C, _hfirst⟩ :=
    HostSubgraphChain.exists_of_successor_bounded
      (G := G) (Inv := KPInvariant n δ r)
      (Step := DensityLayerStep G r) 20 H0 hH0inv (by
        intro i hi H hInv
        exact kp_successor n (by simp) δ r i hn hr hi H hInv)
  exact ⟨C, trivial⟩

/-- The final core of the chain contains a path through ten distinct
vertices. -/
theorem finalCore_exists_path_ten
    {n r : ℕ} {hn : 0 < n} {δ : ℝ}
    (hr : 0 < r) (hratio : (20 : ℝ) / (r : ℝ) ≤ δ)
    {G : SimpleGraph (Fin n)}
    (C : TwentyStageDensityChain G r (KPInvariant n δ r)) :
    let Hf := C.H (Fin.last 20)
    ∃ (S : Finset Hf.verts) (a b : (S : Set Hf.verts))
      (p : (Hf.coe.induce (S : Set Hf.verts)).Walk a b),
      p.IsPath ∧ 9 ≤ p.length := by
  classical
  let Hf := C.H (Fin.last 20)
  have hInv : KPInvariant n δ r 20 Hf := by
    simpa [Hf] using C.invariant (Fin.last 20)
  have hcoeff := kpCoeff_twenty_ge n r δ hn hr hratio
  have hcardnonneg : (0 : ℝ) ≤ Hf.verts.ncard := by positivity
  have hstrong : (4 : ℝ) ^ 5 * (Hf.verts.ncard : ℝ) ≤
      2 * (Hf.edgeSet.ncard : ℝ) := by
    exact (mul_le_mul_of_nonneg_right hcoeff hcardnonneg).trans hInv.2.2
  letI : Fintype Hf.verts := Fintype.ofFinite Hf.verts
  letI : DecidableRel Hf.coe.Adj := Classical.decRel _
  have hcard : Fintype.card Hf.verts = Hf.verts.ncard := by
    rw [← Nat.card_eq_fintype_card, Nat.card_coe_set_eq]
  have hedge : #Hf.coe.edgeFinset = Hf.edgeSet.ncard :=
    Erdos1018Aux.edgeFinset_card_eq_edgeSet_ncard Hf
  have hcardpos : (0 : ℝ) < Hf.verts.ncard := by
    have hnat : 0 < Nat.card Hf.verts :=
      Nat.card_pos_iff.mpr ⟨⟨hInv.2.1.choose, hInv.2.1.choose_spec⟩,
        inferInstance⟩
    have hncard : 0 < Hf.verts.ncard := by
      simpa only [Nat.card_coe_set_eq] using hnat
    exact_mod_cast hncard
  have hpathEdges : 8 * Fintype.card Hf.verts < #Hf.coe.edgeFinset := by
    have hreal : (8 : ℝ) * Hf.verts.ncard < Hf.edgeSet.ncard := by
      norm_num at hstrong
      nlinarith
    have hnat : 8 * Hf.verts.ncard < Hf.edgeSet.ncard := by
      exact_mod_cast hreal
    simpa [hcard, hedge] using hnat
  exact Erdos1018Aux.exists_induced_path_length_nine Hf.coe hpathEdges

/-! ### Routing the final path through the nested stages -/

def induceToAmbientHom {V : Type*} (G : SimpleGraph V) (S : Set V) :
    G.induce S →g G where
  toFun := Subtype.val
  map_rel' h := h

def chainFinalVertex {n r : ℕ} {δ : ℝ}
    {G : SimpleGraph (Fin n)}
    (C : TwentyStageDensityChain G r (KPInvariant n δ r))
    (S : Finset (C.H (Fin.last 20)).verts)
    {a b : (S : Set (C.H (Fin.last 20)).verts)}
    {p : ((C.H (Fin.last 20)).coe.induce
      (S : Set (C.H (Fin.last 20)).verts)).Walk a b}
    (hp : p.IsPath) (hlen : 9 ≤ p.length) : Fin 10 ↪ Fin n :=
  ((firstTen hp hlen).trans
    (Function.Embedding.subtype (S : Set (C.H (Fin.last 20)).verts))).trans
      (Function.Embedding.subtype (C.H (Fin.last 20)).verts)

/-- At each stage, one parity class of the final ten-vertex path lies in the
nearer one of the two retained layers. -/
theorem chain_stage_parity {n r : ℕ} {δ : ℝ}
    {G : SimpleGraph (Fin n)}
    (C : TwentyStageDensityChain G r (KPInvariant n δ r))
    (S : Finset (C.H (Fin.last 20)).verts)
    {a b : (S : Set (C.H (Fin.last 20)).verts)}
    {p : ((C.H (Fin.last 20)).coe.induce
      (S : Set (C.H (Fin.last 20)).verts)).Walk a b}
    (hp : p.IsPath) (hlen : 9 ≤ p.length) (i : Fin 20) :
    ∃ even : Bool, ∀ j : Fin 5,
      chainFinalVertex C S hp hlen (parityEmbedding even j) ∈
        hostLayer (C.transition i).J (C.transition i).center
          (C.transition i).k := by
  classical
  let Hf := C.H (Fin.last 20)
  let step := C.transition i
  have hfAfter : Hf ≤ C.H i.succ := by
    apply C.later_le_earlier
    exact Fin.le_last _
  have hfJ : Hf ≤ step.J := hfAfter.trans step.after_le
  let f : (Hf.coe.induce (S : Set Hf.verts)) →g step.J.coe :=
    (SimpleGraph.Subgraph.inclusion hfJ).comp
      (induceToAmbientHom Hf.coe (S : Set Hf.verts))
  let pJ := p.map f
  have hpJlen : pJ.length = p.length := by simp [pJ]
  have hlayers : ∀ j : Fin 10,
      step.J.coe.dist step.center (pJ.getVert j.1) = step.k ∨
        step.J.coe.dist step.center (pJ.getVert j.1) = step.k + 1 := by
    intro j
    let vHf : Hf.verts := (p.getVert j.1 : S)
    have hvAfter : (vHf : Fin n) ∈ (C.H i.succ).verts :=
      hfAfter.1 vHf.property
    rw [step.layer_eq] at hvAfter
    change (vHf : Fin n) ∈
      hostLayer step.J step.center step.k ∪
        hostLayer step.J step.center (step.k + 1) at hvAfter
    have hget (hx : (vHf : Fin n) ∈ step.J.verts) :
        pJ.getVert j.1 = ⟨(vHf : Fin n), hx⟩ := by
      apply Subtype.ext
      dsimp [pJ]
      rw [Walk.getVert_map]
      rfl
    rcases hvAfter with hnear | hfar
    · left
      rcases hnear with ⟨hx, hd⟩
      rw [hget hx]
      exact hd
    · right
      rcases hfar with ⟨hx, hd⟩
      rw [hget hx]
      exact hd
  obtain ⟨even, hnear⟩ := exists_parity_in_near_layer
    step.connected step.bipartite step.center step.k pJ (by omega) hlayers
  refine ⟨even, ?_⟩
  intro j
  let idx := parityEmbedding even j
  let vHf : Hf.verts := (p.getVert idx.1 : S)
  have hvJ : (vHf : Fin n) ∈ step.J.verts := hfJ.1 vHf.property
  have hvhost : chainFinalVertex C S hp hlen idx ∈ step.J.verts := by
    change (vHf : Fin n) ∈ step.J.verts
    exact hvJ
  refine ⟨hvhost, ?_⟩
  have hget : pJ.getVert idx.1 =
      ⟨chainFinalVertex C S hp hlen idx, hvhost⟩ := by
    apply Subtype.ext
    dsimp [pJ]
    rw [Walk.getVert_map]
    rfl
  rw [← hget]
  exact hnear j

/-- The center of one retained annulus joins any prescribed pair in its
nearer layer by a simple route of length at most `2r`; the internal vertices
lie outside the next core. -/
theorem chain_route_at_stage {n r : ℕ} {δ : ℝ}
    {G : SimpleGraph (Fin n)}
    (C : TwentyStageDensityChain G r (KPInvariant n δ r))
    (S : Finset (C.H (Fin.last 20)).verts)
    {a b : (S : Set (C.H (Fin.last 20)).verts)}
    {p : ((C.H (Fin.last 20)).coe.induce
      (S : Set (C.H (Fin.last 20)).verts)).Walk a b}
    (hp : p.IsPath) (hlen : 9 ≤ p.length)
    (i : Fin 20) (even : Bool)
    (hnear : ∀ j : Fin 5,
      chainFinalVertex C S hp hlen (parityEmbedding even j) ∈
        hostLayer (C.transition i).J (C.transition i).center
          (C.transition i).k)
    (e : CliqueEdge 5) :
    ∃ route : G.Walk
        (chainFinalVertex C S hp hlen (parityEmbedding even e.1.1))
        (chainFinalVertex C S hp hlen (parityEmbedding even e.1.2)),
      route.IsPath ∧ route.length ≤ 2 * r ∧
        walkInteriorSet route ⊆
          (C.H i.castSucc).verts \ (C.H i.succ).verts := by
  classical
  let step := C.transition i
  let u := chainFinalVertex C S hp hlen (parityEmbedding even e.1.1)
  let v := chainFinalVertex C S hp hlen (parityEmbedding even e.1.2)
  obtain ⟨huJ, hdu⟩ := hnear e.1.1
  obtain ⟨hvJ, hdv⟩ := hnear e.1.2
  let uJ : step.J.verts := ⟨u, huJ⟩
  let vJ : step.J.verts := ⟨v, hvJ⟩
  obtain ⟨pu, hpuPath, hpuLen⟩ :=
    step.connected.exists_path_of_dist step.center uJ
  obtain ⟨pv, hpvPath, hpvLen⟩ :=
    step.connected.exists_path_of_dist step.center vJ
  have hpuK : pu.length = step.k := by
    rw [hpuLen]
    exact hdu
  have hpvK : pv.length = step.k := by
    rw [hpvLen]
    exact hdv
  let routeJ := simpleThroughCenter pu pv
  have hrouteJPath : routeJ.IsPath := simpleThroughCenter_isPath pu pv
  have havoidLayers : Disjoint (walkInteriorSet routeJ)
      {x : step.J.verts |
        step.J.coe.dist step.center x = step.k ∨
          step.J.coe.dist step.center x = step.k + 1} :=
    simpleThroughCenter_interior_disjoint_layers pu pv
      hpuLen hpuK hpvLen hpvK
  have havoidAfter : Disjoint (walkInteriorSet routeJ)
      {x : step.J.verts | (x : Fin n) ∈ (C.H i.succ).verts} := by
    rw [Set.disjoint_left]
    intro x hx hxAfter
    apply Set.disjoint_left.mp havoidLayers hx
    change (x : Fin n) ∈ (C.H i.succ).verts at hxAfter
    have hxInduced : (x : Fin n) ∈
        (step.J.induce
          (hostLayer step.J step.center step.k ∪
            hostLayer step.J step.center (step.k + 1))).verts := by
      simpa only [step.layer_eq] using hxAfter
    change (x : Fin n) ∈
      hostLayer step.J step.center step.k ∪
        hostLayer step.J step.center (step.k + 1) at hxInduced
    rcases hxInduced with hnearX | hfarX
    · exact Or.inl hnearX.2
    · exact Or.inr hfarX.2
  let route0 := routeJ.map step.J.hom
  have hroute0Path : route0.IsPath :=
    hrouteJPath.map SimpleGraph.Subgraph.hom_injective
  have hroute0Length : route0.length ≤ 2 * r := by
    have hku : step.k ≤ r := by
      rw [← hpuK, hpuLen]
      exact step.center_dist_le uJ
    have hkv : step.k ≤ r := by
      rw [← hpvK, hpvLen]
      exact step.center_dist_le vJ
    calc
      route0.length = routeJ.length := Walk.length_map _ _
      _ ≤ pu.length + pv.length := simpleThroughCenter_length_le pu pv
      _ = step.k + step.k := by rw [hpuK, hpvK]
      _ ≤ r + r := Nat.add_le_add hku hkv
      _ = 2 * r := by omega
  have hroute0Interior : walkInteriorSet route0 ⊆
      step.J.verts \ (C.H i.succ).verts := by
    exact mapped_route_interior_subset step.J (C.H i.succ) routeJ havoidAfter
  refine ⟨route0, hroute0Path, hroute0Length, ?_⟩
  · intro x hx
    exact ⟨step.J_le.1 (hroute0Interior hx).1,
      (hroute0Interior hx).2⟩

/-- The `m`-th core of a twenty-stage chain, extended by the empty set after
stage twenty so it can be supplied to the generic natural-number assembly
lemma. -/
def twentyCore {V : Type*} {G : SimpleGraph V} {r : ℕ}
    {Inv : ℕ → G.Subgraph → Prop}
    (C : TwentyStageDensityChain G r Inv) (m : ℕ) : Set V :=
  if hm : m ≤ 20 then C.H ⟨m, Nat.lt_succ_iff.mpr hm⟩ |>.verts else ∅

theorem twentyCore_succ_subset {V : Type*} {G : SimpleGraph V} {r : ℕ}
    {Inv : ℕ → G.Subgraph → Prop}
    (C : TwentyStageDensityChain G r Inv) (i : ℕ) (hi : i < 20) :
    twentyCore C (i + 1) ⊆ twentyCore C i := by
  rw [twentyCore, dif_pos (by omega), twentyCore, dif_pos (by omega)]
  let fi : Fin 21 := ⟨i, by omega⟩
  let fj : Fin 21 := ⟨i + 1, by omega⟩
  change (C.H fj).verts ⊆ (C.H fi).verts
  have hifj : fi ≤ fj := by
    change i ≤ i + 1
    omega
  exact (C.later_le_earlier (i := fi) (j := fj) hifj).1

/-- The twenty nested layer choices assemble into a bounded-order
subdivision of `K₅`. -/
theorem twentyStageChain_contains_compact_k5 {n r : ℕ} {δ : ℝ}
    {G : SimpleGraph (Fin n)}
    (C : TwentyStageDensityChain G r (KPInvariant n δ r))
    (S : Finset (C.H (Fin.last 20)).verts)
    {a b : (S : Set (C.H (Fin.last 20)).verts)}
    {p : ((C.H (Fin.last 20)).coe.induce
      (S : Set (C.H (Fin.last 20)).verts)).Walk a b}
    (hp : p.IsPath) (hlen : 9 ≤ p.length) :
    ∃ s : CliqueSubdivision G 5,
      (cliqueSubdivisionVerts s).ncard ≤ 5 + 10 * (2 * r + 1) := by
  classical
  let side : Fin 20 → Bool := fun i ↦
    Classical.choose (chain_stage_parity C S hp hlen i)
  have hside (i : Fin 20) : ∀ j : Fin 5,
      chainFinalVertex C S hp hlen (parityEmbedding (side i) j) ∈
        hostLayer (C.transition i).J (C.transition i).center
          (C.transition i).k :=
    Classical.choose_spec (chain_stage_parity C S hp hlen i)
  obtain ⟨even, slot, hslot⟩ :=
    exists_cliqueEdge_stages_of_same_bool side
  let branch : Fin 5 ↪ Fin n :=
    (parityEmbedding even).trans (chainFinalVertex C S hp hlen)
  have hbranch : Set.range branch ⊆ twentyCore C 20 := by
    rintro x ⟨j, rfl⟩
    rw [twentyCore, dif_pos (by omega)]
    change (((p.getVert (parityEmbedding even j).1 : S) :
      (C.H (Fin.last 20)).verts) : Fin n) ∈
        (C.H (Fin.last 20)).verts
    exact ((p.getVert (parityEmbedding even j).1 : S) :
      (C.H (Fin.last 20)).verts).property
  have hroute (e : CliqueEdge 5) :
      ∃ route : G.Walk (branch e.1.1) (branch e.1.2),
        route.IsPath ∧ route.length ≤ 2 * r ∧
          walkInteriorSet route ⊆
            twentyCore C (slot e).val \ twentyCore C ((slot e).val + 1) := by
    have hnear : ∀ j : Fin 5,
        chainFinalVertex C S hp hlen (parityEmbedding even j) ∈
          hostLayer (C.transition (slot e)).J
            (C.transition (slot e)).center (C.transition (slot e)).k := by
      rw [← hslot e]
      exact hside (slot e)
    obtain ⟨route, hpath, hlength, hinterior⟩ :=
      chain_route_at_stage C S hp hlen (slot e) even hnear e
    refine ⟨route, hpath, hlength, ?_⟩
    rw [twentyCore, dif_pos (Nat.le_of_lt (slot e).isLt),
      twentyCore, dif_pos (by omega)]
    convert hinterior using 1 <;> congr 2
  obtain ⟨s, hslen⟩ :=
    exists_boundedCliqueSubdivision_of_nested_routes
      (core := twentyCore C)
      (hnested := twentyCore_succ_subset C)
      branch hbranch slot hroute
  exact ⟨s, s.verts_ncard_le_of_path_length_le_k5 hslen⟩

/-! ### The compact Kostochka--Pyber theorem and Problem 1018 -/

/-- Explicit `K₅` case of the Kostochka--Pyber compact-subdivision theorem.
The route radius is `⌈20/δ⌉`, so the displayed bound depends only on `δ`. -/
theorem kostochka_pyber_compact_k5
    (δ : ℝ) (hδ : 0 < δ) (n : ℕ) (hn : 0 < n)
    (G : SimpleGraph (Fin n))
    (hE : (4 : ℝ) ^ 25 * (n : ℝ) ^ ((1 : ℝ) + δ) ≤
      (G.edgeSet.ncard : ℝ)) :
    ∃ s : CliqueSubdivision G 5,
      (cliqueSubdivisionVerts s).ncard ≤
        5 + 10 * (2 * Nat.ceil ((20 : ℝ) / δ) + 1) := by
  let r : ℕ := Nat.ceil ((20 : ℝ) / δ)
  have hquot : 0 < (20 : ℝ) / δ := div_pos (by norm_num) hδ
  have hr : 0 < r := Nat.ceil_pos.mpr hquot
  have hceil : (20 : ℝ) / δ ≤ (r : ℝ) := Nat.le_ceil _
  have hrR : (0 : ℝ) < r := by exact_mod_cast hr
  have hratio : (20 : ℝ) / (r : ℝ) ≤ δ := by
    rw [div_le_iff₀ hrR]
    have := (div_le_iff₀ hδ).mp hceil
    nlinarith
  obtain ⟨C, _⟩ := exists_twentyStageDensityChain n hn δ r hr G hE
  obtain ⟨S, a, b, p, hp, hlen⟩ :=
    finalCore_exists_path_ten (hn := hn) hr hratio C
  simpa [r] using twentyStageChain_contains_compact_k5 C S hp hlen

/-- The affirmative resolution of Erdős Problem 1018. -/
theorem erdos_1018 : Erdos1018 := by
  intro ε hε
  let δ : ℝ := min (ε / 2) (1 / 2)
  have hδ : 0 < δ := by
    dsimp [δ]
    exact lt_min (by linarith) (by norm_num)
  obtain ⟨N, hgap⟩ := exponent_gap ε hε
  let r : ℕ := Nat.ceil ((20 : ℝ) / δ)
  let C : ℕ := 5 + 10 * (2 * r + 1)
  refine ⟨C, max N 1, ?_⟩
  intro n hnLarge G hEdges
  have hN : N ≤ n := (le_max_left N 1).trans hnLarge
  have hnOne : 1 ≤ n := (le_max_right N 1).trans hnLarge
  have hn : 0 < n := Nat.zero_lt_of_lt hnOne
  have hDense : (4 : ℝ) ^ 25 * (n : ℝ) ^ ((1 : ℝ) + δ) ≤
      (G.edgeSet.ncard : ℝ) :=
    (hgap n hN).trans hEdges
  obtain ⟨s, hsbound⟩ :=
    kostochka_pyber_compact_k5 δ hδ n hn G hDense
  let U : Set (Fin n) := cliqueSubdivisionVerts s
  obtain ⟨T, hTverts, hTnonplanar⟩ :=
    exists_inducedSubgraph_isNonplanar_of_clique_five
      (U := U) s (fun i ↦ s.branch_mem_verts i)
        (fun e _ hx ↦ s.support_mem_verts e hx)
  refine ⟨T, ?_, hTnonplanar⟩
  rw [hTverts]
  simpa [C, r] using hsbound

end

end Erdos1018

#print axioms Erdos1018.erdos_1018
