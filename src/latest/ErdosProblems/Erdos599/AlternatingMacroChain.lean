/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.Alternating

/-!
# The endpoint-pure path-level alternating chain

For endpoint-pure warps there is a particularly simple path-level skeleton
behind the safe alternating-path construction.  From a member `p` of `Z`
whose terminal is covered by `Y`, take the unique member `q` of `Y` ending
there, and then the unique member of `Z` beginning at `q.initial`.

The step relation is injective in both directions.  Moreover, the first
`Z`-path, whose initial vertex is outside `V[Y]`, is not in the range of a
step.  Consequently every one-sided chain starting there visits pairwise
distinct `Z`-paths; its intervening `Y`-paths are pairwise distinct as well.
These are the path-level no-cycle and interval invariants used when the
edge-level walk is loop-erased and compressed into alternating links.
-/

namespace Erdos599
namespace Alternating

open Set DirectedPath

universe u

variable {V : Type u} {Γ : DWeb V}

/-- The edge relation traversed by the path-level chain: forward on `Z` and
backward on `Y`. -/
def MacroEdge (Z Y : Set Γ.DPath) (x y : V) : Prop :=
  (x, y) ∈ familyEdges Z ∨ (y, x) ∈ familyEdges Y

namespace Walk

/-- A finite walk reaches its endpoint in the reflexive-transitive closure
of its own directed edge set. -/
theorem reflTransGen_edgeSet {D : Digraph V} {a b : V}
    (p : Walk D a b) :
    Relation.ReflTransGen (fun x y ↦ (x, y) ∈ p.edgeSet) a b := by
  induction p with
  | nil => exact .refl
  | @cons a c b h p ih =>
      have ih' := Relation.ReflTransGen.mono (r := fun x y ↦
        (x, y) ∈ p.edgeSet) (p := fun x y ↦
        (x, y) ∈ (Walk.cons h p).edgeSet) (by
          intro x y hxy
          simp only [Walk.edgeSet_cons, Set.mem_union, Set.mem_singleton_iff]
          exact Or.inr hxy) c b ih
      exact ih'.head (by simp [Walk.edgeSet_cons])

/-- The reverse traversal of a finite walk reaches its start in the closure
of the reversed edge set. -/
theorem reflTransGen_reverseEdgeSet {D : Digraph V} {a b : V}
    (p : Walk D a b) :
    Relation.ReflTransGen (fun x y ↦ (y, x) ∈ p.edgeSet) b a := by
  induction p with
  | nil => exact .refl
  | @cons a c b h p ih =>
      have htail : Relation.ReflTransGen
          (fun x y ↦ (y, x) ∈ (Walk.cons h p).edgeSet) b c :=
        Relation.ReflTransGen.mono (r := fun x y ↦
          (y, x) ∈ p.edgeSet) (p := fun x y ↦
          (y, x) ∈ (Walk.cons h p).edgeSet) (by
          intro x y hxy
          simp only [Walk.edgeSet_cons, Set.mem_union, Set.mem_singleton_iff]
          exact Or.inr hxy) b c ih
      exact htail.tail (by simp [Walk.edgeSet_cons])

end Walk

/-- One full path-level step: `p : Z` ends where `q : Y` ends, and the next
`Z`-path `r` begins where `q` begins. -/
def MacroStep (Z Y : Set Γ.DPath) (p r : Z) : Prop :=
  ∃ q : Y, ∃ t : V,
    Γ.terminal? p.1 = some t ∧
      Γ.terminal? q.1 = some t ∧ q.1.initial = r.1.initial

namespace MacroStep

/-- Every macro step gives finite reachability in the auxiliary edge
relation.  This is the exact bridge from the path-level injective chain to
the subsequent loop-erasure argument. -/
theorem reachable
    {Z Y : Set Γ.DPath}
    (hZfin : Γ.HasFiniteCharacter Z) (hYfin : Γ.HasFiniteCharacter Y)
    {p r : Z} (hstep : MacroStep Z Y p r) :
    Relation.ReflTransGen (MacroEdge Z Y) p.1.initial r.1.initial := by
  rcases hstep with ⟨q, t, hpterm, hqterm, hqr⟩
  obtain ⟨fp, hfp⟩ := hZfin p.2
  obtain ⟨fq, hfq⟩ := hYfin q.2
  have hpfinish : fp.finish = t := by
    rw [hfp] at hpterm
    exact Option.some.inj hpterm
  have hqfinish : fq.finish = t := by
    rw [hfq] at hqterm
    exact Option.some.inj hqterm
  have hforward : Relation.ReflTransGen (MacroEdge Z Y)
      fp.start fp.finish :=
    Relation.ReflTransGen.mono (r := fun x y ↦
      (x, y) ∈ fp.walk.edgeSet) (p := MacroEdge Z Y) (by
      intro x y hxy
      left
      simp only [familyEdges, Set.mem_iUnion]
      refine ⟨p.1, p.2, ?_⟩
      rw [hfp]
      exact hxy) fp.start fp.finish (Walk.reflTransGen_edgeSet fp.walk)
  have hbackward : Relation.ReflTransGen (MacroEdge Z Y)
      fq.finish fq.start :=
    Relation.ReflTransGen.mono (r := fun x y ↦
      (y, x) ∈ fq.walk.edgeSet) (p := MacroEdge Z Y) (by
      intro x y hxy
      right
      simp only [familyEdges, Set.mem_iUnion]
      refine ⟨q.1, q.2, ?_⟩
      rw [hfq]
      exact hxy) fq.finish fq.start
        (Walk.reflTransGen_reverseEdgeSet fq.walk)
  have hpstart : p.1.initial = fp.start := congrArg Path.initial hfp
  have hqstart : q.1.initial = fq.start := congrArg Path.initial hfq
  have hforward' : Relation.ReflTransGen (MacroEdge Z Y)
      p.1.initial t := by
    rw [hpstart, ← hpfinish]
    exact hforward
  have hbackward' : Relation.ReflTransGen (MacroEdge Z Y)
      t r.1.initial := by
    rw [← hqfinish, ← hqr, hqstart]
    exact hbackward
  exact hforward'.trans hbackward'

/-- A covered terminal of an endpoint-pure `Z`-path supplies a macro step.
Normalization is used exactly once: a target vertex lying on a `Y`-path is
the terminal of that path. -/
theorem exists_of_terminal_mem
    (hΓ : Γ.IsNormalized) {Z Y : Set Γ.DPath}
    (hZB : Γ.terminalFrontier Z ⊆ Γ.target)
    (hZfin : Γ.HasFiniteCharacter Z)
    (hinit : Γ.initialSet Y ⊆ Γ.initialSet Z)
    (p : Z) (hpY : ∀ t, Γ.terminal? p.1 = some t → t ∈ Γ.vertexSet Y) :
    ∃ r : Z, MacroStep Z Y p r := by
  obtain ⟨fp, hfp⟩ := hZfin p.2
  have hpterm : Γ.terminal? p.1 = some fp.finish := by
    rw [hfp]
    rfl
  have htZ : fp.finish ∈ Γ.terminalFrontier Z :=
    ⟨p.1, p.2, hpterm⟩
  have htY : fp.finish ∈ Γ.vertexSet Y := hpY fp.finish hpterm
  have htYfront : fp.finish ∈ Γ.terminalFrontier Y :=
    DWeb.terminalFrontier_inter_vertexSet_subset hΓ hZB ⟨htZ, htY⟩
  rcases htYfront with ⟨q, hqY, hqterm⟩
  have hqinit : q.initial ∈ Γ.initialSet Y := ⟨q, hqY, rfl⟩
  rcases hinit hqinit with ⟨r, hrZ, hrinit⟩
  refine ⟨⟨r, hrZ⟩, ⟨⟨q, hqY⟩, fp.finish, hpterm, hqterm, ?_⟩⟩
  exact hrinit.symm

/-- The `Y`-path occurring in a macro step is determined by the preceding
`Z`-path. -/
theorem witness_eq_of_same_left
    {Z Y : Set Γ.DPath} (hY : Γ.IsWarp Y)
    {p r s : Z} {q q' : Y} {t t' : V}
    (h : Γ.terminal? p.1 = some t ∧
      Γ.terminal? q.1 = some t ∧ q.1.initial = r.1.initial)
    (h' : Γ.terminal? p.1 = some t' ∧
      Γ.terminal? q'.1 = some t' ∧ q'.1.initial = s.1.initial) :
    q = q' := by
  have htt' : t = t' := Option.some.inj (h.1.symm.trans h'.1)
  subst t'
  apply Subtype.ext
  exact DWeb.IsWarp.eq_of_mem_support hY q.2 q'.2
    (Γ.terminal_mem_support h.2.1)
    (Γ.terminal_mem_support h'.2.1)

/-- The macro step is right-unique. -/
theorem rightUnique
    {Z Y : Set Γ.DPath} (hZ : Γ.IsWarp Z) (hY : Γ.IsWarp Y) :
    Relator.RightUnique (MacroStep Z Y) := by
  intro p r s hpr hps
  rcases hpr with ⟨q, t, hpterm, hqterm, hqr⟩
  rcases hps with ⟨q', t', hpterm', hqterm', hq's⟩
  have hqq' : q = q' := witness_eq_of_same_left hY
    ⟨hpterm, hqterm, hqr⟩ ⟨hpterm', hqterm', hq's⟩
  subst q'
  apply Subtype.ext
  have hrs : r.1.initial = s.1.initial := hqr.symm.trans hq's
  exact DWeb.IsWarp.eq_of_mem_support hZ r.2 s.2
    r.1.initial_mem_support
    (hrs ▸ s.1.initial_mem_support)

/-- The macro step is left-unique.  Endpoint purity is encoded in the fact
that both preceding paths have an actual terminal at the common target. -/
theorem leftUnique
    {Z Y : Set Γ.DPath} (hZ : Γ.IsWarp Z) (hY : Γ.IsWarp Y) :
    Relator.LeftUnique (MacroStep Z Y) := by
  intro p p' r hpr hp'r
  rcases hpr with ⟨q, t, hpterm, hqterm, hqr⟩
  rcases hp'r with ⟨q', t', hp'term, hq'term, hq'r⟩
  have hqq' : q = q' := by
    apply Subtype.ext
    have hinit : q.1.initial = q'.1.initial := hqr.trans hq'r.symm
    exact DWeb.IsWarp.eq_of_mem_support hY q.2 q'.2
      q.1.initial_mem_support
      (hinit ▸ q'.1.initial_mem_support)
  subst q'
  have htt' : t = t' := Option.some.inj (hqterm.symm.trans hq'term)
  subst t'
  apply Subtype.ext
  exact DWeb.IsWarp.eq_of_mem_support hZ p.2 p'.2
    (Γ.terminal_mem_support hpterm)
    (Γ.terminal_mem_support hp'term)

/-- A `Z`-path whose initial vertex is outside `V[Y]` cannot be the target
of a macro step. -/
theorem not_mem_range_of_initial_not_mem
    {Z Y : Set Γ.DPath} (p : Z) (hp : p.1.initial ∉ Γ.vertexSet Y) :
    ¬ ∃ r : Z, MacroStep Z Y r p := by
  rintro ⟨r, q, t, _hrterm, _hqterm, hqp⟩
  apply hp
  exact ⟨q.1, q.2, hqp ▸ q.1.initial_mem_support⟩

end MacroStep

/-! ## A generic injective-chain lemma -/

/-- An infinite chain in a left-unique relation is injective when its root
has no predecessor.  This small cancellation lemma avoids choosing a total
successor function away from the actual orbit. -/
theorem injective_chain_of_leftUnique_of_root_not_range
    {A : Type*} {R : A → A → Prop} {f : ℕ → A}
    (hleft : Relator.LeftUnique R)
    (hstep : ∀ n, R (f n) (f (n + 1)))
    (hroot : ¬ ∃ a, R a (f 0)) :
    Function.Injective f := by
  have hne : ∀ i j, i < j → f i ≠ f j := by
    intro i
    induction i with
    | zero =>
        intro j hij heq
        obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : j ≠ 0)
        apply hroot
        exact ⟨f k, by simpa [heq] using hstep k⟩
    | succ i ih =>
        intro j hij heq
        obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : j ≠ 0)
        have hprev : f i = f k :=
          hleft (hstep i) (by simpa [heq] using hstep k)
        exact ih k (by omega) hprev
  intro i j hij
  by_contra hneij
  rcases lt_or_gt_of_ne hneij with hij' | hji'
  · exact hne i j hij' hij
  · exact hne j i hji' hij.symm

/-- A path-level alternating chain, retaining the actual intervening
`Y`-path so that its uniqueness can be used by the edge-level compiler. -/
structure MacroChain (Z Y : Set Γ.DPath) where
  z : ℕ → Z
  y : ℕ → Y
  terminal : ℕ → V
  z_terminal : ∀ n, Γ.terminal? (z n).1 = some (terminal n)
  y_terminal : ∀ n, Γ.terminal? (y n).1 = some (terminal n)
  joins : ∀ n, (y n).1.initial = (z (n + 1)).1.initial

namespace MacroChain

theorem step {Z Y : Set Γ.DPath} (C : MacroChain Z Y) (n : ℕ) :
    MacroStep Z Y (C.z n) (C.z (n + 1)) :=
  ⟨C.y n, C.terminal n, C.z_terminal n, C.y_terminal n, C.joins n⟩

/-- If every terminal reached on `Z` is covered by `Y`, dependent choice
produces the full infinite macro chain.  The selected `Y` witness and its
terminal are retained in the result rather than hidden behind the step
relation. -/
theorem exists_of_all_terminals_covered
    (hΓ : Γ.IsNormalized) {Z Y : Set Γ.DPath}
    (hZB : Γ.terminalFrontier Z ⊆ Γ.target)
    (hZfin : Γ.HasFiniteCharacter Z)
    (hinit : Γ.initialSet Y ⊆ Γ.initialSet Z)
    (p₀ : Z)
    (hcovered : ∀ p : Z, ∀ t,
      Γ.terminal? p.1 = some t → t ∈ Γ.vertexSet Y) :
    ∃ C : MacroChain Z Y, C.z 0 = p₀ := by
  classical
  have htotal : ∀ p : Z, ∃ r : Z, MacroStep Z Y p r :=
    fun p ↦ MacroStep.exists_of_terminal_mem hΓ hZB hZfin hinit p
      (hcovered p)
  let next : Z → Z := fun p ↦ Classical.choose (htotal p)
  have hnext (p : Z) : MacroStep Z Y p (next p) :=
    Classical.choose_spec (htotal p)
  let z : ℕ → Z := fun n ↦ Nat.rec p₀ (fun _ p ↦ next p) n
  have z_zero : z 0 = p₀ := rfl
  have z_succ (n : ℕ) : z (n + 1) = next (z n) := by
    simp [z]
  have hzstep (n : ℕ) : MacroStep Z Y (z n) (z (n + 1)) := by
    rw [z_succ]
    exact hnext (z n)
  let y : ℕ → Y := fun n ↦ Classical.choose (hzstep n)
  let terminal : ℕ → V := fun n ↦
    Classical.choose (Classical.choose_spec (hzstep n))
  have hspec (n : ℕ) :
      Γ.terminal? (z n).1 = some (terminal n) ∧
        Γ.terminal? (y n).1 = some (terminal n) ∧
          (y n).1.initial = (z (n + 1)).1.initial := by
    exact Classical.choose_spec (Classical.choose_spec (hzstep n))
  refine ⟨{
    z := z
    y := y
    terminal := terminal
    z_terminal := fun n ↦ (hspec n).1
    y_terminal := fun n ↦ (hspec n).2.1
    joins := fun n ↦ (hspec n).2.2
  }, z_zero⟩

/-- The `Z`-paths in a chain from an uncovered initial vertex are pairwise
distinct. -/
theorem z_injective {Z Y : Set Γ.DPath}
    (hZ : Γ.IsWarp Z) (hY : Γ.IsWarp Y)
    (C : MacroChain Z Y)
    (hroot : (C.z 0).1.initial ∉ Γ.vertexSet Y) :
    Function.Injective C.z := by
  apply injective_chain_of_leftUnique_of_root_not_range
    (MacroStep.leftUnique hZ hY) C.step
  exact MacroStep.not_mem_range_of_initial_not_mem (C.z 0) hroot

/-- The intervening `Y`-paths are pairwise distinct.  Thus using each of
them as one full backward run automatically gives the required one-interval
condition on every member of `Y`. -/
theorem y_injective {Z Y : Set Γ.DPath}
    (hZ : Γ.IsWarp Z) (hY : Γ.IsWarp Y)
    (C : MacroChain Z Y)
    (hroot : (C.z 0).1.initial ∉ Γ.vertexSet Y) :
    Function.Injective C.y := by
  have hz := C.z_injective hZ hY hroot
  intro i j hij
  apply hz
  apply Subtype.ext
  exact DWeb.IsWarp.eq_of_mem_support hZ (C.z i).2 (C.z j).2
    (Γ.terminal_mem_support (C.z_terminal i))
    (by
      have ht : C.terminal i = C.terminal j := by
        exact Option.some.inj
          ((C.y_terminal i).symm.trans (hij ▸ C.y_terminal j))
      rw [ht]
      exact Γ.terminal_mem_support (C.z_terminal j))

theorem z_support_disjoint {Z Y : Set Γ.DPath}
    (hZ : Γ.IsWarp Z) (hY : Γ.IsWarp Y)
    (C : MacroChain Z Y)
    (hroot : (C.z 0).1.initial ∉ Γ.vertexSet Y)
    {i j : ℕ} (hij : i ≠ j) :
    Disjoint (C.z i).1.support (C.z j).1.support := by
  exact DWeb.IsWarp.disjoint Γ hZ (C.z i).2 (C.z j).2
    (fun h ↦ hij ((C.z_injective hZ hY hroot) (Subtype.ext h)))

theorem y_support_disjoint {Z Y : Set Γ.DPath}
    (hZ : Γ.IsWarp Z) (hY : Γ.IsWarp Y)
    (C : MacroChain Z Y)
    (hroot : (C.z 0).1.initial ∉ Γ.vertexSet Y)
    {i j : ℕ} (hij : i ≠ j) :
    Disjoint (C.y i).1.support (C.y j).1.support := by
  exact DWeb.IsWarp.disjoint Γ hY (C.y i).2 (C.y j).2
    (fun h ↦ hij ((C.y_injective hZ hY hroot) (Subtype.ext h)))

/-- In particular, the successive covered target vertices are distinct. -/
theorem terminal_injective {Z Y : Set Γ.DPath}
    (hZ : Γ.IsWarp Z) (hY : Γ.IsWarp Y)
    (C : MacroChain Z Y)
    (hroot : (C.z 0).1.initial ∉ Γ.vertexSet Y) :
    Function.Injective C.terminal := by
  have hz := C.z_injective hZ hY hroot
  intro i j hij
  apply hz
  apply Subtype.ext
  exact DWeb.IsWarp.eq_of_mem_support hZ (C.z i).2 (C.z j).2
    (Γ.terminal_mem_support (C.z_terminal i))
    (by rw [hij]; exact Γ.terminal_mem_support (C.z_terminal j))

end MacroChain

end Alternating
end Erdos599
