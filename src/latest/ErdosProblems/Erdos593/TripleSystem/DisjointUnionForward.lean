import ErdosProblems.Erdos593.TripleSystem.DisjointUnion
import ErdosProblems.Erdos593.TripleSystem.Embedding
import ErdosProblems.Erdos593.TripleSystem.Intrinsic
import Mathlib.Combinatorics.SimpleGraph.Sum

set_option relaxedAutoImplicit true
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Forward properties of disjoint unions

The tagged summands embed canonically in a disjoint union, and linearity is
inherited componentwise.
-/

namespace Erdos593

universe u v w z

namespace TripleSystem

variable {V : Type u} {E : Type v} {W : Type w} {D : Type z}

/-- The canonical embedding of the left factor into a disjoint union. -/
def Embedding.disjointUnionInl (F : TripleSystem V E) (G : TripleSystem W D) :
    F.Embedding (F.disjointUnion G) where
  vertex := ⟨Sum.inl, Sum.inl_injective⟩
  edge := Sum.inl
  map_edge e := (disjointUnion_edgeSet_inl F G e).symm

/-- The canonical embedding of the right factor into a disjoint union. -/
def Embedding.disjointUnionInr (F : TripleSystem V E) (G : TripleSystem W D) :
    G.Embedding (F.disjointUnion G) where
  vertex := ⟨Sum.inr, Sum.inr_injective⟩
  edge := Sum.inr
  map_edge d := (disjointUnion_edgeSet_inr F G d).symm

/-- A disjoint union of linear triple systems is linear. -/
theorem disjointUnion_linear (F : TripleSystem V E) (G : TripleSystem W D)
    (hF : F.Linear) (hG : G.Linear) :
    (F.disjointUnion G).Linear := by
  intro e f x y hef hxe hxf hye hyf
  rcases e with e | d <;> rcases f with f | c <;>
    rcases x with x | x <;> rcases y with y | y <;>
    simp only [disjointUnion_inc_inl_inl, disjointUnion_inc_inr_inr,
      disjointUnion_not_inc_inl_inr, disjointUnion_not_inc_inr_inl] at *
  · exact congrArg Sum.inl (hF (Sum.inl_injective.ne_iff.mp hef) hxe hxf hye hyf)
  · exact congrArg Sum.inr (hG (Sum.inr_injective.ne_iff.mp hef) hxe hxf hye hyf)

/-- The Levi graph of a triple-system disjoint union is the graph-theoretic
disjoint sum of the two factor Levi graphs, up to the canonical reassociation
of the four tagged node types. -/
-- ARISTOTLE_FORWARD_TARGET DU1
def disjointUnionLeviIso (F : TripleSystem V E) (G : TripleSystem W D) :
    (F.disjointUnion G).levi ≃g F.levi ⊕g G.levi := by
  let e : ((V ⊕ W) ⊕ (E ⊕ D)) ≃ ((V ⊕ E) ⊕ (W ⊕ D)) :=
    { toFun := fun
        | .inl (.inl x) => .inl (.inl x)
        | .inl (.inr y) => .inr (.inl y)
        | .inr (.inl a) => .inl (.inr a)
        | .inr (.inr b) => .inr (.inr b)
      invFun := fun
        | .inl (.inl x) => .inl (.inl x)
        | .inl (.inr a) => .inr (.inl a)
        | .inr (.inl y) => .inl (.inr y)
        | .inr (.inr b) => .inr (.inr b)
      left_inv := by rintro ((x | y) | (a | b)) <;> rfl
      right_inv := by rintro ((x | a) | (y | b)) <;> rfl }
  exact
    { toEquiv := e
      map_rel_iff' := by
        rintro ((x | y) | (a | b)) ((x' | y') | (a' | b')) <;>
          simp [e] }

private theorem isBridge_iff_of_iso {A B : Type*}
    {P : _root_.SimpleGraph A} {Q : _root_.SimpleGraph B}
    (f : P ≃g Q) (a b : A) :
    P.IsBridge s(a, b) ↔ Q.IsBridge s(f a, f b) := by
  let fd : P.deleteEdges {s(a, b)} ≃g
      Q.deleteEdges {s(f a, f b)} :=
    { toEquiv := f.toEquiv
      map_rel_iff' := by
        intro x y
        simp [f.map_adj_iff] }
  change (¬(P.deleteEdges {s(a, b)}).Reachable a b) ↔
    ¬(Q.deleteEdges {s(f a, f b)}).Reachable (f a) (f b)
  exact not_congr fd.reachable_iff.symm

private theorem reachable_sum_inl_iff {A B : Type*}
    (P : _root_.SimpleGraph A) (Q : _root_.SimpleGraph B) (a b : A) :
    (P ⊕g Q).Reachable (.inl a) (.inl b) ↔ P.Reachable a b := by
  constructor
  · rintro ⟨p⟩
    let pull {s t : A ⊕ B} (p : (P ⊕g Q).Walk s t) :
        ∀ a : A, s = .inl a →
          ∃ b : A, t = .inl b ∧ Nonempty (P.Walk a b) := by
      induction p with
      | nil =>
          intro a ha
          exact ⟨a, ha, ⟨.nil⟩⟩
      | @cons u v t h p ih =>
          intro a ha
          subst u
          cases v with
          | inl a' =>
              have h' : P.Adj a a' := by simpa using! h
              obtain ⟨b, hb, ⟨q⟩⟩ := ih a' rfl
              exact ⟨b, hb, ⟨.cons h' q⟩⟩
          | inr y => simp at h
    obtain ⟨b', hb', ⟨q⟩⟩ := pull p a rfl
    have hbb' : b = b' := Sum.inl_injective hb'
    subst b'
    exact ⟨q⟩
  · intro h
    exact h.map (_root_.SimpleGraph.Embedding.sumInl (G := P) (H := Q)).toHom

private theorem isBridge_sum_inl {A B : Type*}
    (P : _root_.SimpleGraph A) (Q : _root_.SimpleGraph B) (a b : A)
    (h : P.IsBridge s(a, b)) :
    (P ⊕g Q).IsBridge s(.inl a, .inl b) := by
  rw [_root_.SimpleGraph.isBridge_iff] at h ⊢
  intro hr
  apply h
  apply (reachable_sum_inl_iff (P.deleteEdges {s(a, b)}) Q a b).mp
  have hdelete :
      (P ⊕g Q).deleteEdges {s(.inl a, .inl b)} =
        P.deleteEdges {s(a, b)} ⊕g Q := by
    ext (x | x) (y | y) <;> simp
  rw [← hdelete]
  exact hr

private theorem isBridge_sum_inr {A B : Type*}
    (P : _root_.SimpleGraph A) (Q : _root_.SimpleGraph B) (a b : B)
    (h : Q.IsBridge s(a, b)) :
    (P ⊕g Q).IsBridge s(.inr a, .inr b) := by
  have hleft : (Q ⊕g P).IsBridge s(.inl a, .inl b) :=
    isBridge_sum_inl Q P a b h
  exact (isBridge_iff_of_iso (_root_.SimpleGraph.Iso.sumComm)
    (.inl a) (.inl b)).mp hleft

/-- A cycle in the left component of a graph sum lifts uniquely enough for
our purposes to a cycle of the same length in that component. -/
theorem exists_cycle_of_sum_inl {A B : Type*}
    (P : _root_.SimpleGraph A) (Q : _root_.SimpleGraph B)
    {a : A} (c : (P ⊕g Q).Walk (.inl a) (.inl a)) (hc : c.IsCycle) :
    ∃ (a' : A) (d : P.Walk a' a'), d.IsCycle ∧ c.length = d.length := by
  classical
  have hsupp : ∀ x ∈ c.support,
      x ∈ Set.range (Sum.inl : A → A ⊕ B) := by
    intro x hx
    cases x with
    | inl x => exact ⟨x, rfl⟩
    | inr y =>
        exact False.elim
          ((_root_.SimpleGraph.not_reachable_sum_inl_inr (G := P) (H := Q) a y)
            ⟨c.takeUntil (.inr y) hx⟩)
  let ci := c.induce (Set.range (Sum.inl : A → A ⊕ B)) hsupp
  let proj : (P ⊕g Q).induce (Set.range (Sum.inl : A → A ⊕ B)) →g P :=
    { toFun := fun x => Classical.choose x.2
      map_rel' := by
        intro x y hxy
        have hx := Classical.choose_spec x.2
        have hy := Classical.choose_spec y.2
        have hxy' : (P ⊕g Q).Adj x.1 y.1 :=
          _root_.SimpleGraph.induce_adj.mp hxy
        rw [← hx, ← hy] at hxy'
        simpa using! hxy' }
  have hproj : Function.Injective proj := by
    intro x y hxy
    apply Subtype.ext
    have hx := Classical.choose_spec x.2
    have hy := Classical.choose_spec y.2
    rw [← hx, ← hy]
    exact congrArg Sum.inl hxy
  have hmap_ci :
      ci.map (_root_.SimpleGraph.Embedding.induce
        (G := P ⊕g Q) (Set.range (Sum.inl : A → A ⊕ B))).toHom = c := by
    simp [ci]
  have hci : ci.IsCycle := by
    apply _root_.SimpleGraph.Walk.IsCycle.of_map
    rw [hmap_ci]
    exact hc
  let d := ci.map proj
  have hd : d.IsCycle := hci.map hproj
  have hci_len : ci.length = c.length := by
    calc
      ci.length =
          (ci.map (_root_.SimpleGraph.Embedding.induce
            (G := P ⊕g Q) (Set.range (Sum.inl : A → A ⊕ B))).toHom).length := by
        symm
        apply _root_.SimpleGraph.Walk.length_map
      _ = c.length := congrArg
        (fun w : (P ⊕g Q).Walk (.inl a) (.inl a) => w.length) hmap_ci
  have hd_len : d.length = ci.length := by simp [d]
  exact ⟨proj ⟨Sum.inl a, ⟨a, rfl⟩⟩, d, hd,
    hci_len.symm.trans hd_len.symm⟩

/-- The right-component counterpart of `exists_cycle_of_sum_inl`. -/
theorem exists_cycle_of_sum_inr {A B : Type*}
    (P : _root_.SimpleGraph A) (Q : _root_.SimpleGraph B)
    {b : B} (c : (P ⊕g Q).Walk (.inr b) (.inr b)) (hc : c.IsCycle) :
    ∃ (b' : B) (d : Q.Walk b' b'), d.IsCycle ∧ c.length = d.length := by
  let f : P ⊕g Q ≃g Q ⊕g P := _root_.SimpleGraph.Iso.sumComm
  let c' := c.map f.toHom
  have hc' : c'.IsCycle := hc.map f.injective
  obtain ⟨b', d, hd, hlen⟩ := exists_cycle_of_sum_inl Q P c' hc'
  refine ⟨b', d, hd, ?_⟩
  calc
    c.length = c'.length := by
      symm
      exact _root_.SimpleGraph.Walk.length_map f.toHom c
    _ = d.length := hlen

private theorem cycle_length_dvd_sum_inl {A B : Type*}
    (P : _root_.SimpleGraph A) (Q : _root_.SimpleGraph B) (n : ℕ)
    (hP : ∀ ⦃a : A⦄ (c : P.Walk a a), c.IsCycle → n ∣ c.length)
    {a : A} (c : (P ⊕g Q).Walk (.inl a) (.inl a)) (hc : c.IsCycle) :
    n ∣ c.length := by
  classical
  have hsupp : ∀ x ∈ c.support,
      x ∈ Set.range (Sum.inl : A → A ⊕ B) := by
    intro x hx
    cases x with
    | inl x => exact ⟨x, rfl⟩
    | inr y =>
        exact False.elim
          ((_root_.SimpleGraph.not_reachable_sum_inl_inr (G := P) (H := Q) a y)
            ⟨c.takeUntil (.inr y) hx⟩)
  let ci := c.induce (Set.range (Sum.inl : A → A ⊕ B)) hsupp
  let proj : (P ⊕g Q).induce (Set.range (Sum.inl : A → A ⊕ B)) →g P :=
    { toFun := fun x => Classical.choose x.2
      map_rel' := by
        intro x y hxy
        have hx := Classical.choose_spec x.2
        have hy := Classical.choose_spec y.2
        have hxy' : (P ⊕g Q).Adj x.1 y.1 :=
          _root_.SimpleGraph.induce_adj.mp hxy
        rw [← hx, ← hy] at hxy'
        simpa using! hxy' }
  have hproj : Function.Injective proj := by
    intro x y hxy
    apply Subtype.ext
    have hx := Classical.choose_spec x.2
    have hy := Classical.choose_spec y.2
    rw [← hx, ← hy]
    exact congrArg Sum.inl hxy
  have hmap_ci :
      ci.map (_root_.SimpleGraph.Embedding.induce
        (G := P ⊕g Q) (Set.range (Sum.inl : A → A ⊕ B))).toHom = c := by
    simp [ci]
  have hci : ci.IsCycle := by
    apply _root_.SimpleGraph.Walk.IsCycle.of_map
    rw [hmap_ci]
    exact hc
  let q := ci.map proj
  have hq : q.IsCycle := hci.map hproj
  have hci_len : ci.length = c.length := by
    calc
      ci.length =
          (ci.map (_root_.SimpleGraph.Embedding.induce
            (G := P ⊕g Q) (Set.range (Sum.inl : A → A ⊕ B))).toHom).length := by
        symm
        apply _root_.SimpleGraph.Walk.length_map
      _ = c.length := congrArg
        (fun w : (P ⊕g Q).Walk (.inl a) (.inl a) => w.length) hmap_ci
  have hq_len : q.length = ci.length := by simp [q]
  rw [← hci_len, ← hq_len]
  exact hP q hq

private theorem cycle_length_dvd_sum_inr {A B : Type*}
    (P : _root_.SimpleGraph A) (Q : _root_.SimpleGraph B) (n : ℕ)
    (hQ : ∀ ⦃b : B⦄ (c : Q.Walk b b), c.IsCycle → n ∣ c.length)
    {b : B} (c : (P ⊕g Q).Walk (.inr b) (.inr b)) (hc : c.IsCycle) :
    n ∣ c.length := by
  let f : P ⊕g Q ≃g Q ⊕g P := _root_.SimpleGraph.Iso.sumComm
  let c' := c.map f.toHom
  have hc' : c'.IsCycle := hc.map f.injective
  have hdiv := cycle_length_dvd_sum_inl Q P n hQ c' hc'
  rw [← _root_.SimpleGraph.Walk.length_map f.toHom c]
  exact hdiv

/-- The intrinsic bridge condition is preserved by disjoint union. -/
-- ARISTOTLE_FORWARD_TARGET DU2
theorem disjointUnion_bridgeAtEveryEdge (F : TripleSystem V E)
    (G : TripleSystem W D) (hF : F.BridgeAtEveryEdge)
    (hG : G.BridgeAtEveryEdge) :
    (F.disjointUnion G).BridgeAtEveryEdge := by
  intro e
  cases e with
  | inl e =>
      rcases hF e with ⟨x, hxedge, hxbridge⟩
      refine ⟨.inl x, ?_, ?_⟩
      · simpa using! hxedge
      · have hsum := isBridge_sum_inl F.levi G.levi
          (.inl x) (.inr e) hxbridge
        have hiso := (isBridge_iff_of_iso (disjointUnionLeviIso F G)
          (.inl (.inl x)) (.inr (.inl e))).mpr hsum
        simpa [disjointUnionLeviIso] using! hiso
  | inr e =>
      rcases hG e with ⟨y, hyedge, hybridge⟩
      refine ⟨.inr y, ?_, ?_⟩
      · simpa using! hyedge
      · have hsum := isBridge_sum_inr F.levi G.levi
          (.inl y) (.inr e) hybridge
        have hiso := (isBridge_iff_of_iso (disjointUnionLeviIso F G)
          (.inl (.inr y)) (.inr (.inr e))).mpr hsum
        simpa [disjointUnionLeviIso] using! hiso

/-- Divisibility by four of every Levi-cycle length is preserved by disjoint
union. -/
-- ARISTOTLE_FORWARD_TARGET DU3
theorem disjointUnion_evenBergeCycles (F : TripleSystem V E)
    (G : TripleSystem W D) (hF : F.EvenBergeCycles)
    (hG : G.EvenBergeCycles) :
    (F.disjointUnion G).EvenBergeCycles := by
  intro z c hc
  let f := disjointUnionLeviIso F G
  let c' := c.map f.toHom
  have hc' : c'.IsCycle := hc.map f.injective
  have hlen : c'.length = c.length := by simp [c']
  rw [← hlen]
  cases z with
  | inl z =>
      cases z with
      | inl x =>
          exact cycle_length_dvd_sum_inl F.levi G.levi 4 hF c' hc'
      | inr y =>
          exact cycle_length_dvd_sum_inr F.levi G.levi 4 hG c' hc'
  | inr z =>
      cases z with
      | inl e =>
          exact cycle_length_dvd_sum_inl F.levi G.levi 4 hF c' hc'
      | inr d =>
          exact cycle_length_dvd_sum_inr F.levi G.levi 4 hG c' hc'

/-- All three intrinsic conditions are preserved by disjoint union. -/
-- ARISTOTLE_FORWARD_TARGET DU4
theorem disjointUnion_intrinsic (F : TripleSystem V E)
    (G : TripleSystem W D) (hF : F.Intrinsic) (hG : G.Intrinsic) :
    (F.disjointUnion G).Intrinsic := by
  exact ⟨disjointUnion_linear F G hF.1 hG.1,
    disjointUnion_bridgeAtEveryEdge F G hF.2.1 hG.2.1,
    disjointUnion_evenBergeCycles F G hF.2.2 hG.2.2⟩

end TripleSystem

end Erdos593
