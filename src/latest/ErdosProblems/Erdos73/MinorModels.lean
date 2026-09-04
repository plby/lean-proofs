/-
Adapted from the Apache-2.0-licensed polynomial-grid-minor-theorem development,
https://github.com/EdouardBonnet/polynomial-grid-minor-theorem,
commit fe2848173913a00d85c64d2a17af63f2cf0d4fbf,
proofs/Lax17Proofs/Source/{MinorContract,Minor,MinorTransitivity}.lean.
The ordinary branch-set definitions and proofs are isolated here; the
external grid definitions and assumption-bearing interfaces are not imported.
-/
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Subgraph
import Mathlib.Combinatorics.SimpleGraph.Copy

namespace Erdos73Infrastructure.SimpleGraph
universe u v w

structure MinorModel {W V : Type*}
    (H : _root_.SimpleGraph W) (G : _root_.SimpleGraph V) where
  /-- The branch set in `G` assigned to a vertex of `H`. -/
  branchSet : W → Finset V
  /-- Every branch set is nonempty. -/
  branch_nonempty : ∀ w : W, (branchSet w).Nonempty
  /-- Every branch set induces a connected subgraph of `G`. -/
  branch_connected :
    ∀ w : W, (G.induce {v : V | v ∈ branchSet w}).Connected
  /-- Distinct vertices of `H` have disjoint branch sets in `G`. -/
  branch_disjoint :
    ∀ ⦃u v : W⦄, u ≠ v → Disjoint (branchSet u) (branchSet v)
  /-- Every edge of `H` is represented by an edge of `G` between branch sets. -/
  adjacent :
    ∀ ⦃u v : W⦄, H.Adj u v →
      ∃ x ∈ branchSet u, ∃ y ∈ branchSet v, G.Adj x y

/-- `H` is a graph minor of `G` when there exists a branch-set model of `H` in
`G`. -/
def IsMinor {W V : Type*}
    (H : _root_.SimpleGraph W) (G : _root_.SimpleGraph V) : Prop :=
  Nonempty (MinorModel H G)


/-- An isomorphism maps an induced subgraph on a finite vertex set to the
induced subgraph on the image of that set. -/
noncomputable def inducedIsoMapFinset {V V' : Type*}
    {G : _root_.SimpleGraph V} {G' : _root_.SimpleGraph V'}
    (e : G ≃g G') (S : Finset V) :
    G.induce {v : V | v ∈ S} ≃g
      G'.induce {v : V' | v ∈ S.map e.toEquiv.toEmbedding} where
  toFun := fun v =>
    ⟨e v.1, by
      change e v.1 ∈ S.map e.toEquiv.toEmbedding
      exact Finset.mem_map.mpr ⟨v.1, v.2, rfl⟩⟩
  invFun := fun v =>
    ⟨e.symm v.1, by
      change e.symm v.1 ∈ S
      rcases Finset.mem_map.mp v.2 with ⟨w, hw, hwv⟩
      have hw_eq : w = e.symm v.1 := by
        rw [← hwv]
        simp
      simpa [← hw_eq] using hw⟩
  left_inv := by
    intro v
    apply Subtype.ext
    simp
  right_inv := by
    intro v
    apply Subtype.ext
    simp
  map_rel_iff' := by
    intro u v
    change G'.Adj (e u.1) (e v.1) ↔ G.Adj u.1 v.1
    exact _root_.SimpleGraph.Iso.map_adj_iff e

namespace MinorModel

/-- An ordinary, not necessarily induced, subgraph copy is a minor.
This addition uses only adjacency preservation, so extra host edges are harmless. -/
def of_copy {W V : Type*}
    {H : _root_.SimpleGraph W} {G : _root_.SimpleGraph V}
    (e : H.Copy G) : MinorModel H G where
  branchSet := fun w ↦ {e w}
  branch_nonempty := fun w ↦ Finset.singleton_nonempty _
  branch_connected := by
    intro w
    have heq : {x : V | x ∈ ({e w} : Finset V)} = {e w} := by ext x; simp
    rw [heq]
    exact _root_.SimpleGraph.Connected.of_subsingleton
  branch_disjoint := fun _ _ huv ↦ Finset.disjoint_singleton.mpr (e.injective.ne huv)
  adjacent := fun {_ _} huv ↦ ⟨_, Finset.mem_singleton_self _,
    _, Finset.mem_singleton_self _, e.toHom.map_adj huv⟩

/-- The singleton branch-set model witnessing that every graph is a minor of
itself. -/
def refl {V : Type*} (G : _root_.SimpleGraph V) : MinorModel G G where
  branchSet := fun v => {v}
  branch_nonempty := by
    intro v
    exact ⟨v, by simp⟩
  branch_connected := by
    intro v
    have : Nonempty {x : V | x ∈ ({v} : Finset V)} := ⟨⟨v, by simp⟩⟩
    have : Subsingleton {x : V | x ∈ ({v} : Finset V)} := by
      constructor
      intro x y
      apply Subtype.ext
      have hx : x.1 = v := by simpa using x.2
      have hy : y.1 = v := by simpa using y.2
      exact hx.trans hy.symm
    exact _root_.SimpleGraph.Connected.of_subsingleton
  branch_disjoint := by
    intro u v huv
    rw [Finset.disjoint_left]
    intro x hxu hxv
    have hxu' : x = u := by simpa using hxu
    have hxv' : x = v := by simpa using hxv
    exact huv (hxu'.symm.trans hxv')
  adjacent := by
    intro u v huv
    exact ⟨u, by simp, v, by simp, huv⟩

/-- A graph embedding gives a singleton-branch minor model. -/
def of_embedding {W V : Type*}
    {H : _root_.SimpleGraph W} {G : _root_.SimpleGraph V}
    (e : H ↪g G) : MinorModel H G where
  branchSet := fun w => {e w}
  branch_nonempty := by
    intro w
    exact ⟨e w, by simp⟩
  branch_connected := by
    intro w
    have : Nonempty {x : V | x ∈ ({e w} : Finset V)} := ⟨⟨e w, by simp⟩⟩
    have : Subsingleton {x : V | x ∈ ({e w} : Finset V)} := by
      constructor
      intro x y
      apply Subtype.ext
      have hx : x.1 = e w := by simpa using x.2
      have hy : y.1 = e w := by simpa using y.2
      exact hx.trans hy.symm
    exact _root_.SimpleGraph.Connected.of_subsingleton
  branch_disjoint := by
    intro u v huv
    rw [Finset.disjoint_left]
    intro x hxu hxv
    have hxu' : x = e u := by simpa using hxu
    have hxv' : x = e v := by simpa using hxv
    exact huv (e.injective (hxu'.symm.trans hxv'))
  adjacent := by
    intro u v huv
    exact ⟨e u, by simp, e v, by simp, e.map_rel_iff.mpr huv⟩

/-- The union of host branch sets visited by a walk in the pattern graph. -/
noncomputable def walkBranchUnion {W V : Type*} [DecidableEq W] [DecidableEq V]
    {H : _root_.SimpleGraph W} {G : _root_.SimpleGraph V}
    (M : MinorModel H G) {x y : W} (P : H.Walk x y) : Finset V :=
  P.support.toFinset.biUnion M.branchSet

/-- A vertex of a branch set visited by the walk belongs to the walk branch
union. -/
theorem mem_walkBranchUnion_of_mem_branch {W V : Type*}
    [DecidableEq W] [DecidableEq V]
    {H : _root_.SimpleGraph W} {G : _root_.SimpleGraph V}
    (M : MinorModel H G) {x y z : W} {P : H.Walk x y}
    (hz : z ∈ P.support.toFinset) {v : V}
    (hv : v ∈ M.branchSet z) :
    v ∈ M.walkBranchUnion P := by
  classical
  simpa [walkBranchUnion] using (Finset.mem_biUnion.2 ⟨z, hz, hv⟩)

/-- The union of host branch sets along a pattern walk induces a connected
subgraph of the host. -/
theorem walkBranchUnion_connected {W V : Type*} [DecidableEq W] [DecidableEq V]
    {H : _root_.SimpleGraph W} {G : _root_.SimpleGraph V}
    (M : MinorModel H G) :
    {x y : W} →
      (P : H.Walk x y) →
        (G.induce {v : V | v ∈ M.walkBranchUnion P}).Connected
  | x, _, _root_.SimpleGraph.Walk.nil' _ => by
      rw [show
        {v : V | v ∈ M.walkBranchUnion
          ((_root_.SimpleGraph.Walk.nil : H.Walk x x))}
          = {v : V | v ∈ M.branchSet x} by
          ext v
          simp [walkBranchUnion]]
      exact M.branch_connected x
  | x, z, _root_.SimpleGraph.Walk.cons' _ y _ hxy P => by
      classical
      have hbranch :
          (G.induce {v : V | v ∈ M.branchSet x}).Connected :=
        M.branch_connected x
      have htail :
          (G.induce {v : V | v ∈ M.walkBranchUnion P}).Connected :=
        M.walkBranchUnion_connected P
      rcases M.adjacent hxy with ⟨u, hu, v, hv, huv⟩
      have hvTail : v ∈ M.walkBranchUnion P :=
        M.mem_walkBranchUnion_of_mem_branch (by simp) hv
      have hconn :
          (G.induce
            ({v : V | v ∈ M.branchSet x} ∪
              {v : V | v ∈ M.walkBranchUnion P})).Connected :=
        _root_.SimpleGraph.connected_induce_union
          hbranch.preconnected htail.preconnected hu hvTail huv
      rw [show
        {w : V | w ∈ M.walkBranchUnion
          (_root_.SimpleGraph.Walk.cons hxy P)}
          =
        ({w : V | w ∈ M.branchSet x} ∪
          {w : V | w ∈ M.walkBranchUnion P}) by
          ext w
          simp [walkBranchUnion, _root_.SimpleGraph.Walk.support_cons,
            Finset.mem_biUnion]]
      exact hconn

/-- Transport the host graph of a minor model across a graph isomorphism. -/
noncomputable def of_iso_right {W V V' : Type*}
    {H : _root_.SimpleGraph W} {G : _root_.SimpleGraph V}
    {G' : _root_.SimpleGraph V'}
    (e : G ≃g G') (M : MinorModel H G) : MinorModel H G' where
  branchSet := fun w => (M.branchSet w).map e.toEquiv.toEmbedding
  branch_nonempty := by
    intro w
    rcases M.branch_nonempty w with ⟨x, hx⟩
    exact ⟨e x, by
      exact Finset.mem_map.mpr ⟨x, hx, rfl⟩⟩
  branch_connected := by
    intro w
    exact ((inducedIsoMapFinset e (M.branchSet w)).connected_iff).mp
      (M.branch_connected w)
  branch_disjoint := by
    intro u v huv
    rw [Finset.disjoint_left]
    intro x hxu hxv
    rcases Finset.mem_map.mp hxu with ⟨a, hau, hax⟩
    rcases Finset.mem_map.mp hxv with ⟨b, hbv, hbx⟩
    have hab : a = b := by
      apply e.toEquiv.injective
      exact hax.trans hbx.symm
    exact Finset.disjoint_left.mp (M.branch_disjoint huv) hau (by
      simpa [hab] using hbv)
  adjacent := by
    intro u v huv
    rcases M.adjacent huv with ⟨x, hx, y, hy, hxy⟩
    refine ⟨e x, ?_, e y, ?_, ?_⟩
    · change e x ∈ (M.branchSet u).map e.toEquiv.toEmbedding
      exact Finset.mem_map.mpr ⟨x, hx, rfl⟩
    · change e y ∈ (M.branchSet v).map e.toEquiv.toEmbedding
      exact Finset.mem_map.mpr ⟨y, hy, rfl⟩
    · exact (_root_.SimpleGraph.Iso.map_adj_iff e).mpr hxy

end MinorModel

namespace IsMinor

/-- Build a graph minor directly from branch-set data.  This is a named
constructor for the standard branch-set model, useful when a proof has already
assembled the nonempty connected branch sets, disjointness, and edge
realization obligations. -/
theorem of_branchSets {W V : Type*}
    {H : _root_.SimpleGraph W} {G : _root_.SimpleGraph V}
    (branchSet : W → Finset V)
    (branch_nonempty : ∀ w : W, (branchSet w).Nonempty)
    (branch_connected :
      ∀ w : W, (G.induce {v : V | v ∈ branchSet w}).Connected)
    (branch_disjoint :
      ∀ ⦃u v : W⦄, u ≠ v → Disjoint (branchSet u) (branchSet v))
    (adjacent :
      ∀ ⦃u v : W⦄, H.Adj u v →
        ∃ x ∈ branchSet u, ∃ y ∈ branchSet v, G.Adj x y) :
    IsMinor H G :=
  ⟨{
    branchSet := branchSet
    branch_nonempty := branch_nonempty
    branch_connected := branch_connected
    branch_disjoint := branch_disjoint
    adjacent := adjacent
  }⟩

/-- Every graph is a minor of itself. -/
theorem refl {V : Type*} (G : _root_.SimpleGraph V) : IsMinor G G :=
  ⟨MinorModel.refl G⟩

/-- Every embedded graph is a minor of its host. -/
theorem of_embedding {W V : Type*}
    {H : _root_.SimpleGraph W} {G : _root_.SimpleGraph V}
    (e : H ↪g G) : IsMinor H G :=
  ⟨MinorModel.of_embedding e⟩

/-- A minor model can be transported across an isomorphism of the pattern graph. -/
theorem of_iso_left {W W' V : Type*}
    {H : _root_.SimpleGraph W} {H' : _root_.SimpleGraph W'}
    {G : _root_.SimpleGraph V}
    (e : H' ≃g H) (hminor : IsMinor H G) :
    IsMinor H' G := by
  rcases hminor with ⟨M⟩
  refine ⟨{
    branchSet := fun w => M.branchSet (e w)
    branch_nonempty := ?_
    branch_connected := ?_
    branch_disjoint := ?_
    adjacent := ?_
  }⟩
  · intro w
    exact M.branch_nonempty (e w)
  · intro w
    exact M.branch_connected (e w)
  · intro u v huv
    exact M.branch_disjoint (fun h => huv (e.injective h))
  · intro u v huv
    exact M.adjacent ((_root_.SimpleGraph.Iso.map_adj_iff e).mpr huv)

/-- Minor containment is invariant under isomorphism of the pattern graph. -/
theorem iso_left_iff {W W' V : Type*}
    {H : _root_.SimpleGraph W} {H' : _root_.SimpleGraph W'}
    {G : _root_.SimpleGraph V}
    (e : H' ≃g H) :
    IsMinor H' G ↔ IsMinor H G :=
  ⟨of_iso_left e.symm, of_iso_left e⟩

/-- A minor model can be transported across an isomorphism of the host graph. -/
theorem of_iso_right {W V V' : Type*}
    {H : _root_.SimpleGraph W} {G : _root_.SimpleGraph V}
    {G' : _root_.SimpleGraph V'}
    (e : G ≃g G') (hminor : IsMinor H G) :
    IsMinor H G' := by
  rcases hminor with ⟨M⟩
  exact ⟨M.of_iso_right e⟩

/-- Minor containment is invariant under isomorphism of the host graph. -/
theorem iso_right_iff {W V V' : Type*}
    {H : _root_.SimpleGraph W} {G : _root_.SimpleGraph V}
    {G' : _root_.SimpleGraph V'}
    (e : G ≃g G') :
    IsMinor H G ↔ IsMinor H G' :=
  ⟨of_iso_right e, of_iso_right e.symm⟩

/-- Minor containment is invariant under simultaneous relabeling of the pattern
and host graphs. -/
theorem iso_iff {W W' V V' : Type*}
    {H : _root_.SimpleGraph W} {H' : _root_.SimpleGraph W'}
    {G : _root_.SimpleGraph V} {G' : _root_.SimpleGraph V'}
    (eH : H ≃g H') (eG : G ≃g G') :
    IsMinor H G ↔ IsMinor H' G' :=
  ⟨fun h => of_iso_left eH.symm (of_iso_right eG h),
    fun h => of_iso_left eH (of_iso_right eG.symm h)⟩

/-- Graph minors are monotone under adding edges to the host graph. -/
theorem mono {W V : Type*}
    {H : _root_.SimpleGraph W} {G G' : _root_.SimpleGraph V}
    (hminor : IsMinor H G) (hGG' : G ≤ G') :
    IsMinor H G' := by
  rcases hminor with ⟨M⟩
  refine ⟨{
    branchSet := M.branchSet
    branch_nonempty := M.branch_nonempty
    branch_connected := ?_
    branch_disjoint := M.branch_disjoint
    adjacent := ?_
  }⟩
  · intro w
    refine _root_.SimpleGraph.Connected.mono ?_ (M.branch_connected w)
    intro x y hxy
    exact hGG' hxy
  · intro u v huv
    rcases M.adjacent huv with ⟨x, hx, y, hy, hxy⟩
    exact ⟨x, hx, y, hy, hGG' hxy⟩

end IsMinor

namespace MinorModel

/-- Branch set used in the composition of two minor models. -/
def composeBranchSet {U W V : Type*}
    {F : _root_.SimpleGraph U} {H : _root_.SimpleGraph W}
    {G : _root_.SimpleGraph V}
    (M : MinorModel F H) (N : MinorModel H G) (u : U) : Finset V :=
  (M.branchSet u).disjiUnion N.branchSet (by
    intro a _ b _ hab
    exact N.branch_disjoint hab)

theorem mem_composeBranchSet {U W V : Type*}
    {F : _root_.SimpleGraph U} {H : _root_.SimpleGraph W}
    {G : _root_.SimpleGraph V}
    (M : MinorModel F H) (N : MinorModel H G) (u : U) (x : V) :
    x ∈ composeBranchSet M N u ↔
      ∃ w ∈ M.branchSet u, x ∈ N.branchSet w := by
  exact Finset.mem_disjiUnion

private theorem branchSet_subset_composeBranchSet {U W V : Type*}
    {F : _root_.SimpleGraph U} {H : _root_.SimpleGraph W}
    {G : _root_.SimpleGraph V}
    (M : MinorModel F H) (N : MinorModel H G) {u : U}
    {w : W} (hw : w ∈ M.branchSet u) :
    {x : V | x ∈ N.branchSet w} ⊆
      {x : V | x ∈ composeBranchSet M N u} := by
  intro x hx
  change x ∈ composeBranchSet M N u
  rw [mem_composeBranchSet]
  exact ⟨w, hw, hx⟩

private theorem reachable_in_composeBranchSet_of_walk {U W V : Type*}
    {F : _root_.SimpleGraph U} {H : _root_.SimpleGraph W}
    {G : _root_.SimpleGraph V}
    (M : MinorModel F H) (N : MinorModel H G) {u : U} :
    ∀ {a b : {w : W | w ∈ M.branchSet u}},
      (p : (H.induce {w : W | w ∈ M.branchSet u}).Walk a b) →
        ∀ {x y : V}, (hx : x ∈ N.branchSet a.1) → (hy : y ∈ N.branchSet b.1) →
          (G.induce {z : V | z ∈ composeBranchSet M N u}).Reachable
            ⟨x, by
              change x ∈ composeBranchSet M N u
              rw [mem_composeBranchSet]
              exact ⟨a.1, a.2, hx⟩⟩
            ⟨y, by
              change y ∈ composeBranchSet M N u
              rw [mem_composeBranchSet]
              exact ⟨b.1, b.2, hy⟩⟩
    := by
  intro a b p
  induction p with
  | @nil a =>
      intro x y hx hy
      have hsubset := branchSet_subset_composeBranchSet M N (u := u) a.2
      have hreach :
          (G.induce {z : V | z ∈ N.branchSet a.1}).Reachable
            ⟨x, hx⟩ ⟨y, by simpa using hy⟩ :=
        N.branch_connected a.1 ⟨x, hx⟩ ⟨y, by simpa using hy⟩
      have hreach' := hreach.map (G.induceHomOfLE hsubset).toHom
      exact hreach'
  | @cons a a' b haa' p ih =>
      intro x y hx hy
      rcases N.adjacent (_root_.SimpleGraph.induce_adj.mp haa') with
        ⟨x₀, hx₀, y₀, hy₀, hxy₀⟩
      have hsubseta := branchSet_subset_composeBranchSet M N (u := u) a.2
      have hreach_head :
          (G.induce {z : V | z ∈ N.branchSet a.1}).Reachable
            ⟨x, hx⟩ ⟨x₀, hx₀⟩ :=
        N.branch_connected a.1 ⟨x, hx⟩ ⟨x₀, hx₀⟩
      have hhead := hreach_head.map (G.induceHomOfLE hsubseta).toHom
      have hx₀c : x₀ ∈ composeBranchSet M N u := by
        rw [mem_composeBranchSet]
        exact ⟨a.1, a.2, hx₀⟩
      have hy₀c : y₀ ∈ composeBranchSet M N u := by
        rw [mem_composeBranchSet]
        exact ⟨a'.1, a'.2, hy₀⟩
      have hedge :
          (G.induce {z : V | z ∈ composeBranchSet M N u}).Reachable
            ⟨x₀, hx₀c⟩ ⟨y₀, hy₀c⟩ :=
        (_root_.SimpleGraph.induce_adj.mpr hxy₀).reachable
      have htail := ih hy₀ hy
      have hxc : x ∈ composeBranchSet M N u := by
        rw [mem_composeBranchSet]
        exact ⟨a.1, a.2, hx⟩
      have hhead' :
          (G.induce {z : V | z ∈ composeBranchSet M N u}).Reachable
            ⟨x, hxc⟩ ⟨x₀, hx₀c⟩ := by
        exact hhead
      exact hhead'.trans (hedge.trans htail)

/-- Compose two branch-set models of graph minors. -/
def trans {U W V : Type*}
    {F : _root_.SimpleGraph U} {H : _root_.SimpleGraph W}
    {G : _root_.SimpleGraph V}
    (M : MinorModel F H) (N : MinorModel H G) :
    MinorModel F G where
  branchSet := composeBranchSet M N
  branch_nonempty := by
    intro u
    rcases M.branch_nonempty u with ⟨w, hw⟩
    rcases N.branch_nonempty w with ⟨x, hx⟩
    exact ⟨x, by
      rw [mem_composeBranchSet]
      exact ⟨w, hw, hx⟩⟩
  branch_connected := by
    intro u
    rw [_root_.SimpleGraph.connected_iff_exists_forall_reachable]
    rcases M.branch_nonempty u with ⟨w₀, hw₀⟩
    rcases N.branch_nonempty w₀ with ⟨x₀, hx₀⟩
    refine ⟨⟨x₀, by
      change x₀ ∈ composeBranchSet M N u
      rw [mem_composeBranchSet]
      exact ⟨w₀, hw₀, hx₀⟩⟩, ?_⟩
    rintro ⟨y, hy⟩
    change y ∈ composeBranchSet M N u at hy
    rw [mem_composeBranchSet] at hy
    rcases hy with ⟨w, hw, hyw⟩
    have hwalk :
        (H.induce {z : W | z ∈ M.branchSet u}).Reachable
          ⟨w₀, hw₀⟩ ⟨w, hw⟩ :=
      M.branch_connected u ⟨w₀, hw₀⟩ ⟨w, hw⟩
    exact hwalk.elim fun p =>
      reachable_in_composeBranchSet_of_walk M N p hx₀ hyw
  branch_disjoint := by
    intro u v huv
    rw [Finset.disjoint_left]
    intro x hxu hxv
    rw [mem_composeBranchSet] at hxu hxv
    rcases hxu with ⟨a, hau, hxa⟩
    rcases hxv with ⟨b, hbv, hxb⟩
    by_cases hab : a = b
    · subst b
      exact Finset.disjoint_left.mp (M.branch_disjoint huv) hau hbv
    · exact Finset.disjoint_left.mp (N.branch_disjoint hab) hxa hxb
  adjacent := by
    intro u v huv
    rcases M.adjacent huv with ⟨a, hau, b, hbv, hab⟩
    rcases N.adjacent hab with ⟨x, hxa, y, hyb, hxy⟩
    refine ⟨x, ?_, y, ?_, hxy⟩
    · rw [mem_composeBranchSet]
      exact ⟨a, hau, hxa⟩
    · rw [mem_composeBranchSet]
      exact ⟨b, hbv, hyb⟩

end MinorModel

/-- Graph minors are transitive. -/
theorem IsMinor.trans {U W V : Type*}
    {F : _root_.SimpleGraph U} {H : _root_.SimpleGraph W}
    {G : _root_.SimpleGraph V}
    (hFH : IsMinor F H) (hHG : IsMinor H G) :
    IsMinor F G := by
  rcases hFH with ⟨M⟩
  rcases hHG with ⟨N⟩
  exact ⟨M.trans N⟩

/-- A non-induced copy maps an induced connected vertex set to a
connected induced graph on the image, even when the host has extra edges. -/
theorem connected_induce_map_copy {V W : Type*}
    {G : _root_.SimpleGraph V} {H : _root_.SimpleGraph W}
    (e : G.Copy H) (S : Finset V) (hS : (G.induce (S : Set V)).Connected) :
    (H.induce (↑(S.map e.toEmbedding) : Set W)).Connected := by
  let f : G.induce (S : Set V) →g H.induce (↑(S.map e.toEmbedding) : Set W) := {
    toFun := fun v ↦ ⟨e v.1, Finset.mem_map.mpr ⟨v.1, v.2, rfl⟩⟩
    map_rel' := fun {_ _} h ↦ e.toHom.map_adj h }
  have hf : Function.Surjective f := by
    rintro ⟨w, hw⟩
    obtain ⟨v, hv, hvw⟩ := Finset.mem_map.mp hw
    exact ⟨⟨v, hv⟩, Subtype.ext hvw⟩
  exact hS.map f hf

end Erdos73Infrastructure.SimpleGraph
