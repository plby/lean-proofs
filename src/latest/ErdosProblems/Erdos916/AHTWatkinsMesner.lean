/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos916.AHTSourceLemma
import ErdosProblems.Erdos916.WatkinsMesner

/-!
# The Watkins--Mesner source configuration

This file records the source-faithful seven-condition splitter used in
Section 5 of Aboulker--Havet--Trotignon, and proves the unconditional first
source step of the Watkins--Mesner argument.  Namely, in a finite
vertex-two-connected graph with no cycle through three prescribed vertices,
there is a cycle through the first two vertices and a path through the third
whose only vertices on that cycle are its two distinct ends.  This is the
theta-subdivision configuration from which the maximal two-separators in the
paper are chosen.
-/

attribute [local instance] Classical.propDecidable

namespace Erdos916

open SimpleGraph

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]

/-! ## A literal finite-set formulation of the AHT splitter -/

/-- `C` is a connected component after deleting `S`.  The last clause says
that no edge of the deleted graph leaves `C`; together with connectedness and
nonemptiness this is exactly the connected-component condition. -/
def IsComponentAfterDeleting (G : SimpleGraph V) (S C : Finset V) : Prop :=
  C.Nonempty ∧ Disjoint C S ∧ (G.induce (C : Set V)).Connected ∧
    ∀ u ∈ C, ∀ v, v ∉ S → G.Adj u v → v ∈ C

/-- Every edge from `C` to `T` has its `T`-end at `a`, and such an edge
actually exists. -/
def IsUniqueAttachment (G : SimpleGraph V) (C T : Finset V) (a : V) : Prop :=
  a ∈ T ∧ (∃ u ∈ C, G.Adj u a) ∧
    ∀ u ∈ C, ∀ t ∈ T, G.Adj u t → t = a

/-- The finite carrier of a Mathlib connected component outside `S`. -/
noncomputable def componentCarrier (S : Finset V) (C : G.ComponentCompl (S : Set V)) :
    Finset V :=
  (C : Set V).toFinset

@[simp] theorem mem_componentCarrier {S : Finset V}
    {C : G.ComponentCompl (S : Set V)} {v : V} :
    v ∈ componentCarrier S C ↔ v ∈ (C : Set V) := by
  simp [componentCarrier]

/-- Mathlib's component outside a finite deletion set satisfies the literal
component predicate used in the Watkins--Mesner certificate. -/
theorem isComponentAfterDeleting_componentCarrier (S : Finset V)
    (C : G.ComponentCompl (S : Set V)) :
    IsComponentAfterDeleting G S (componentCarrier S C) := by
  classical
  have hconn : (G.induce (C : Set V)).Connected := by
    let φ : C.toSimpleGraph →g G.induce (C : Set V) :=
      { toFun := fun w ↦ ⟨w.1.1, ⟨w.1.2, w.2⟩⟩
        map_rel' := fun h ↦ h }
    have hφ : Function.Surjective φ := by
      rintro ⟨v, hv⟩
      obtain ⟨hvS, hvC⟩ := hv
      exact ⟨⟨⟨v, hvS⟩, hvC⟩, rfl⟩
    exact C.connected_toSimpleGraph.map φ hφ
  have hcarrier : ((componentCarrier S C : Finset V) : Set V) =
      (C : Set V) := by
    ext v
    simp only [Set.mem_setOf_eq, Finset.mem_coe, mem_componentCarrier]
  refine ⟨?_, ?_, by rw [hcarrier]; exact hconn, ?_⟩
  · obtain ⟨v, hv⟩ := C.nonempty
    exact ⟨v, by simpa only [mem_componentCarrier] using hv⟩
  · rw [Finset.disjoint_left]
    intro v hvC hvS
    have hvC' : v ∈ (C : Set V) := by
      simpa only [mem_componentCarrier] using hvC
    exact (ComponentCompl.notMem_of_mem hvC') hvS
  · intro u hu v hvS huv
    have huC : u ∈ (C : Set V) := by
      simpa only [mem_componentCarrier] using hu
    have hvC : v ∈ (C : Set V) :=
      ComponentCompl.mem_of_adj u v huC hvS huv
    simpa only [mem_componentCarrier] using hvC

/-- A component outside `S₀` remains an exact component after deleting a
larger set `S`, provided the additional deleted vertices all lie outside the
component. -/
theorem isComponentAfterDeleting_componentCarrier_of_subset
    (S₀ S : Finset V) (C : G.ComponentCompl (S₀ : Set V))
    (hsub : S₀ ⊆ S) (hdis : Disjoint (componentCarrier S₀ C) S) :
    IsComponentAfterDeleting G S (componentCarrier S₀ C) := by
  classical
  have hbase := isComponentAfterDeleting_componentCarrier S₀ C
  refine ⟨hbase.1, hdis, hbase.2.2.1, ?_⟩
  intro u hu v hvS huv
  have hvS₀ : v ∉ S₀ := fun hv ↦ hvS (hsub hv)
  exact hbase.2.2.2 u hu v hvS₀ huv

/-- In a graph which remains connected after deleting one vertex, a
component outside a two-element set has an edge to each member of that set.
This is the elementary boundary fact used for all six named attachments. -/
theorem ComponentCompl.exists_adj_to_each_of_delete_connected
    {a b : V} (hab : a ≠ b)
    (hdelete : ∀ d : V, (G.induce fun w : V ↦ w ≠ d).Connected)
    (C : G.ComponentCompl (({a, b} : Finset V) : Set V)) :
    (∃ u ∈ (C : Set V), G.Adj u a) ∧
      ∃ u ∈ (C : Set V), G.Adj u b := by
  classical
  have one_side {s t : V} (hst : s ≠ t)
      (hpair : ({s, t} : Finset V) = ({a, b} : Finset V)) :
      ∃ u ∈ (C : Set V), G.Adj u s := by
    obtain ⟨c, hcC⟩ := C.nonempty
    have hct : c ≠ t := by
      intro h
      apply ComponentCompl.notMem_of_mem hcC
      rw [← hpair]
      simp [h]
    have hst' : s ≠ t := hst
    let c' : {w : V // w ≠ t} := ⟨c, hct⟩
    let s' : {w : V // w ≠ t} := ⟨s, hst'⟩
    obtain ⟨q, hq⟩ := ((hdelete t) c' s').exists_isPath
    let inc : G.induce (fun w : V ↦ w ≠ t) →g G :=
      (SimpleGraph.Embedding.induce
        (G := G) (s := fun w : V ↦ w ≠ t)).toHom
    let p : G.Walk c s := (q.map inc).copy rfl rfl
    have hsC : s ∉ (C : Set V) := by
      intro hs
      apply ComponentCompl.notMem_of_mem hs
      rw [← hpair]
      simp
    obtain ⟨d, hdp, hdC, hdnotC⟩ :=
      p.exists_boundary_dart (C : Set V) hcC hsC
    have hdt : d.snd ≠ t := by
      have hdsupp : d.snd ∈ p.support :=
        p.dart_snd_mem_support_of_mem_darts hdp
      change d.snd ∈ ((q.map inc).copy rfl rfl).support at hdsupp
      rw [Walk.support_copy, Walk.support_map] at hdsupp
      obtain ⟨w, -, hw⟩ := List.mem_map.mp hdsupp
      intro h
      apply w.2
      simpa [inc, h] using hw
    have hdDel : d.snd ∈ (({a, b} : Finset V) : Set V) := by
      by_contra hdnotDel
      exact hdnotC
        (ComponentCompl.mem_of_adj d.fst d.snd hdC hdnotDel d.adj)
    have hdDel' : d.snd ∈ (({s, t} : Finset V) : Set V) := by
      rw [hpair]
      exact hdDel
    have hds : d.snd = s := by
      have hcases : d.snd = s ∨ d.snd = t := by simpa using hdDel'
      exact hcases.resolve_right hdt
    exact ⟨d.fst, hdC, by simpa [hds] using d.adj⟩
  refine ⟨one_side hab rfl, ?_⟩
  exact one_side hab.symm (by ext v; simp [or_comm])

/-- A component outside `{a,b}` has `a` as its unique attachment in any
set `T` which contains `a`, omits `b`, and is disjoint from the component.
The existence of the attachment uses vertex-two-connectivity; uniqueness is
the component boundary property. -/
theorem ComponentCompl.isUniqueAttachment_left
    {a b : V} (hab : a ≠ b)
    (hdelete : ∀ d : V, (G.induce fun w : V ↦ w ≠ d).Connected)
    (C : G.ComponentCompl (({a, b} : Finset V) : Set V)) (T : Finset V)
    (haT : a ∈ T) (hbT : b ∉ T)
    (hdis : Disjoint (componentCarrier (G := G) {a, b} C) T) :
    IsUniqueAttachment G (componentCarrier (G := G) {a, b} C) T a := by
  classical
  refine ⟨haT, ?_, ?_⟩
  · obtain ⟨u, huC, hua⟩ :=
      (ComponentCompl.exists_adj_to_each_of_delete_connected
        (G := G) hab hdelete C).1
    exact ⟨u, by simpa only [mem_componentCarrier] using huC, hua⟩
  · intro u huC t htT hut
    have huC' : u ∈ (C : Set V) := by
      simpa only [mem_componentCarrier] using huC
    have htPair : t ∈ (({a, b} : Finset V) : Set V) := by
      by_contra htNotPair
      have htC : t ∈ (C : Set V) :=
        ComponentCompl.mem_of_adj u t huC' htNotPair hut
      have htCarrier : t ∈ componentCarrier (G := G) {a, b} C := by
        simpa only [mem_componentCarrier] using htC
      exact Finset.disjoint_left.mp hdis htCarrier htT
    simp only [Finset.mem_coe, Finset.mem_insert, Finset.mem_singleton] at htPair
    rcases htPair with (rfl | htb)
    · rfl
    · exact (hbT (htb ▸ htT)).elim

/-- Symmetric form of `isUniqueAttachment_left`. -/
theorem ComponentCompl.isUniqueAttachment_right
    {a b : V} (hab : a ≠ b)
    (hdelete : ∀ d : V, (G.induce fun w : V ↦ w ≠ d).Connected)
    (C : G.ComponentCompl (({a, b} : Finset V) : Set V)) (T : Finset V)
    (hbT : b ∈ T) (haT : a ∉ T)
    (hdis : Disjoint (componentCarrier (G := G) {a, b} C) T) :
    IsUniqueAttachment G (componentCarrier (G := G) {a, b} C) T b := by
  classical
  refine ⟨hbT, ?_, ?_⟩
  · obtain ⟨u, huC, hub⟩ :=
      (ComponentCompl.exists_adj_to_each_of_delete_connected
        (G := G) hab hdelete C).2
    exact ⟨u, by simpa only [mem_componentCarrier] using huC, hub⟩
  · intro u huC t htT hut
    have huC' : u ∈ (C : Set V) := by
      simpa only [mem_componentCarrier] using huC
    have htPair : t ∈ (({a, b} : Finset V) : Set V) := by
      by_contra htNotPair
      have htC : t ∈ (C : Set V) :=
        ComponentCompl.mem_of_adj u t huC' htNotPair hut
      have htCarrier : t ∈ componentCarrier (G := G) {a, b} C := by
        simpa only [mem_componentCarrier] using htC
      exact Finset.disjoint_left.mp hdis htCarrier htT
    simp only [Finset.mem_coe, Finset.mem_insert, Finset.mem_singleton] at htPair
    rcases htPair with (hta | rfl)
    · exact (haT (hta ▸ htT)).elim
    · rfl

/-- The ambient graph with the vertices of `C` removed is vertex-two-connected,
in the deletion formulation used throughout the Erdős 916 development. -/
def ComplementVertexTwoConnected (G : SimpleGraph V) (C : Finset V) : Prop :=
  (G.induce fun v : V ↦ v ∉ C).Connected ∧
    ∀ d : {v : V // v ∉ C},
      ((G.induce fun v : V ↦ v ∉ C).induce
        fun w : {v : V // v ∉ C} ↦ w ≠ d).Connected

/-- All neighbours outside `C` of vertices of `C` belong to `T`. -/
def HasExternalBoundaryIn (G : SimpleGraph V) (C T : Finset V) : Prop :=
  ∀ u ∈ C, ∀ v, G.Adj u v → v ∉ C → v ∈ T

/-- A Watkins--Mesner splitter, with all named attachments and all seven
conditions of AHT Section 5 made explicit.

The three displayed deletion components are `X`, `Y`, and `Z`.  Condition
(vii) quantifies over every component `D` of `G - (A ∪ B)`, not only the
three displayed ones. -/
structure WatkinsMesnerSplitter (G : SimpleGraph V) (x y z : V) where
  aSet : Finset V
  bSet : Finset V
  xPart : Finset V
  yPart : Finset V
  zPart : Finset V
  xA : V
  yA : V
  zA : V
  xB : V
  yB : V
  zB : V
  A_nonempty : aSet.Nonempty
  B_nonempty : bSet.Nonempty
  A_disjoint_B : Disjoint aSet bSet
  X_component : IsComponentAfterDeleting G (aSet ∪ bSet) xPart
  Y_component : IsComponentAfterDeleting G (aSet ∪ bSet) yPart
  Z_component : IsComponentAfterDeleting G (aSet ∪ bSet) zPart
  X_disjoint_Y : Disjoint xPart yPart
  X_disjoint_Z : Disjoint xPart zPart
  Y_disjoint_Z : Disjoint yPart zPart
  x_mem_X : x ∈ xPart
  y_mem_Y : y ∈ yPart
  z_mem_Z : z ∈ zPart
  X_A_attachment : IsUniqueAttachment G xPart aSet xA
  Y_A_attachment : IsUniqueAttachment G yPart aSet yA
  Z_A_attachment : IsUniqueAttachment G zPart aSet zA
  X_B_attachment : IsUniqueAttachment G xPart bSet xB
  Y_B_attachment : IsUniqueAttachment G yPart bSet yB
  Z_B_attachment : IsUniqueAttachment G zPart bSet zB
  A_eq : aSet = {xA, yA, zA}
  B_eq : bSet = {xB, yB, zB}
  A_card : aSet.card = 1 ∨ aSet.card = 3
  B_card : bSet.card = 1 ∨ bSet.card = 3
  twoConnected_compl_X : ComplementVertexTwoConnected G xPart
  twoConnected_compl_Y : ComplementVertexTwoConnected G yPart
  twoConnected_compl_Z : ComplementVertexTwoConnected G zPart
  matched_edges_of_both_triples :
    aSet.card = 3 → bSet.card = 3 →
      ∀ a ∈ aSet, ∀ b ∈ bSet, G.Adj a b →
        (a = xA ∧ b = xB) ∨ (a = yA ∧ b = yB) ∨ (a = zA ∧ b = zB)
  component_boundary_of_both_triples :
    aSet.card = 3 → bSet.card = 3 →
      ∀ D : Finset V, IsComponentAfterDeleting G (aSet ∪ bSet) D →
        HasExternalBoundaryIn G D aSet ∨ HasExternalBoundaryIn G D bSet ∨
          HasExternalBoundaryIn G D {xA, xB} ∨
          HasExternalBoundaryIn G D {yA, yB} ∨
          HasExternalBoundaryIn G D {zA, zB}

/-! ## Cycles through terminals and the first source configuration -/

/-- Three specified vertices occur on one simple cycle. -/
def HasCycleThroughThree (G : SimpleGraph V) (x y z : V) : Prop :=
  ∃ r : V, ∃ C : G.Walk r r,
    C.IsCycle ∧ x ∈ C.support ∧ y ∈ C.support ∧ z ∈ C.support

/-- A two-vertex separator between a terminal and a displayed cycle.  Its
`side` is the exact component containing the terminal after deleting the two
separator vertices. -/
structure VertexCycleSeparator {r : V} (C : G.Walk r r) (x : V) where
  left : V
  right : V
  left_ne_right : left ≠ right
  x_ne_left : x ≠ left
  x_ne_right : x ≠ right
  side : G.ComponentCompl (({left, right} : Finset V) : Set V)
  x_mem_side : x ∈ (side : Set V)
  rim_outside_side :
    ∀ w, w ∈ C.support → w ≠ left → w ≠ right → w ∉ (side : Set V)

/-- A cycle separator whose two vertices lie on the two specified arms from
the branch vertices to the terminal.  This is the family over which AHT
maximizes the terminal-side component. -/
structure RoutedCycleSeparator {a b x r : V}
    (pA : G.Walk a x) (pB : G.Walk b x) (C : G.Walk r r) extends
    VertexCycleSeparator C x where
  left_mem_aArm : left ∈ pA.support
  left_ne_terminal : left ≠ x
  right_mem_bArm : right ∈ pB.support
  right_ne_terminal : right ≠ x

/-- Maximality of a routed separator means maximality of the finite carrier
of its terminal-side component, exactly as in the proof of AHT Theorem 5.1. -/
def RoutedCycleSeparator.IsMaximal {a b x r : V}
    {pA : G.Walk a x} {pB : G.Walk b x} {C : G.Walk r r}
    (S : RoutedCycleSeparator pA pB C) : Prop :=
  ∀ T : RoutedCycleSeparator pA pB C,
    (componentCarrier (G := G) {T.left, T.right} T.side).card ≤
      (componentCarrier (G := G) {S.left, S.right} S.side).card

/-- Once one routed separator exists, finiteness supplies one with a largest
terminal-side component.  This isolates the finite maximization used three
times in AHT's proof. -/
theorem exists_maximal_routedCycleSeparator {a b x r : V}
    {pA : G.Walk a x} {pB : G.Walk b x} {C : G.Walk r r}
    (hne : Nonempty (RoutedCycleSeparator pA pB C)) :
    ∃ S : RoutedCycleSeparator pA pB C, S.IsMaximal := by
  classical
  letI : Nonempty (RoutedCycleSeparator pA pB C) := hne
  let size : RoutedCycleSeparator pA pB C → ℕ := fun S ↦
    (componentCarrier (G := G) {S.left, S.right} S.side).card
  have hfinite :
      (size '' (Set.univ : Set (RoutedCycleSeparator pA pB C))).Finite := by
    apply (Finset.finite_toSet (Finset.range (Fintype.card V + 1))).subset
    intro n hn
    obtain ⟨S, -, rfl⟩ := hn
    simp only [Finset.mem_coe, Finset.mem_range]
    exact Nat.lt_succ_of_le (Finset.card_le_univ _)
  obtain ⟨S, -, hS⟩ := Set.Finite.exists_maximalFor'
    size (Set.univ : Set (RoutedCycleSeparator pA pB C)) hfinite
    Set.univ_nonempty
  refine ⟨S, ?_⟩
  intro T
  rcases le_total (size T) (size S) with h | h
  · exact h
  · exact hS (by simp) h

/-- The unconditional theta source produced before the maximal-separator
choices in the Watkins--Mesner proof. -/
structure WatkinsMesnerThetaSource (G : SimpleGraph V) (x y z : V) where
  rimBase : V
  rim : G.Walk rimBase rimBase
  rim_isCycle : rim.IsCycle
  x_mem_rim : x ∈ rim.support
  y_mem_rim : y ∈ rim.support
  z_not_mem_rim : z ∉ rim.support
  left : V
  right : V
  left_mem_rim : left ∈ rim.support
  right_mem_rim : right ∈ rim.support
  left_ne_right : left ≠ right
  cross : G.Walk left right
  cross_isPath : cross.IsPath
  z_mem_cross : z ∈ cross.support
  cross_meets_rim_only_at_ends :
    ∀ w, w ∈ cross.support → w ∈ rim.support → w = left ∨ w = right

/-- Two simple paths with the same distinct ends and no other common vertex
form a simple cycle, provided the first path has a displayed internal
vertex. -/
theorem Walk.IsPath.isCycle_append_reverse_of_meet_only_ends
    {s t w : V} {p q : G.Walk s t} (hp : p.IsPath) (hq : q.IsPath)
    (hw : w ∈ p.support) (hws : w ≠ s) (hwt : w ≠ t)
    (hmeet : ∀ a, a ∈ p.support → a ∈ q.support → a = s ∨ a = t) :
    (p.append q.reverse).IsCycle := by
  apply hp.isCycle_append hq.reverse
  · rw [List.disjoint_left]
    intro a hap haqr
    have hap' : a ∈ p.support := List.mem_of_mem_tail hap
    have haq' : a ∈ q.support := by
      have : a ∈ q.reverse.support := List.mem_of_mem_tail haqr
      simpa only [Walk.support_reverse, List.mem_reverse] using this
    rcases hmeet a hap' haq' with rfl | rfl
    · have hnd := hp.support_nodup
      rw [← p.cons_tail_support] at hnd
      exact (List.nodup_cons.mp hnd).1 hap
    · have hnd := hq.reverse.support_nodup
      rw [← q.reverse.cons_tail_support] at hnd
      exact (List.nodup_cons.mp hnd).1 haqr
  · left
    by_contra hlen
    have hle : p.length ≤ 1 := by omega
    have hends : p.support = [s, t] ∨ s = t := by
      cases p with
      | nil => exact Or.inr rfl
      | @cons _ a _ hadj q =>
          cases q with
          | nil => simp
          | @cons _ b _ hab q => simp at hle
    rcases hends with hsupp | hst
    · have hwst : w = s ∨ w = t := by simpa [hsupp] using hw
      exact hwst.elim hws hwt
    · subst t
      have hpnil : p = .nil := Walk.isPath_iff_eq_nil.mp hp
      subst p
      exact hws (by simpa using hw)

/-- The `K_{3,2}` subdivision in the route form: three internally disjoint
routes between two branch vertices, with the three prescribed terminals in
the interiors of the respective routes.  Splitting each route at its named
terminal gives the six paths in AHT Lemma 3.6. -/
structure WatkinsMesnerK32Source (G : SimpleGraph V) (x y z : V) where
  branchA : V
  branchB : V
  branch_ne : branchA ≠ branchB
  xRoute : G.Walk branchA branchB
  yRoute : G.Walk branchA branchB
  zRoute : G.Walk branchA branchB
  xRoute_isPath : xRoute.IsPath
  yRoute_isPath : yRoute.IsPath
  zRoute_isPath : zRoute.IsPath
  x_mem : x ∈ xRoute.support
  y_mem : y ∈ yRoute.support
  z_mem : z ∈ zRoute.support
  x_internal : x ≠ branchA ∧ x ≠ branchB
  y_internal : y ≠ branchA ∧ y ≠ branchB
  z_internal : z ≠ branchA ∧ z ≠ branchB
  xRoute_inter_yRoute :
    ∀ w, w ∈ xRoute.support → w ∈ yRoute.support →
      w = branchA ∨ w = branchB
  xRoute_inter_zRoute :
    ∀ w, w ∈ xRoute.support → w ∈ zRoute.support →
      w = branchA ∨ w = branchB
  yRoute_inter_zRoute :
    ∀ w, w ∈ yRoute.support → w ∈ zRoute.support →
      w = branchA ∨ w = branchB

namespace WatkinsMesnerK32Source

variable {x y z : V} (T : WatkinsMesnerK32Source G x y z)

/-- The two halves of the `x`-route, oriented from the branch vertices to
`x`, and the opposite rim through `y,z`. -/
def xArmA : G.Walk T.branchA x := T.xRoute.takeUntil x T.x_mem
def xArmB : G.Walk T.branchB x := (T.xRoute.dropUntil x T.x_mem).reverse
def xRim : G.Walk T.branchA T.branchA :=
  T.yRoute.append T.zRoute.reverse

/-- The analogous routed data for `y`. -/
def yArmA : G.Walk T.branchA y := T.yRoute.takeUntil y T.y_mem
def yArmB : G.Walk T.branchB y := (T.yRoute.dropUntil y T.y_mem).reverse
def yRim : G.Walk T.branchA T.branchA :=
  T.xRoute.append T.zRoute.reverse

/-- The analogous routed data for `z`. -/
def zArmA : G.Walk T.branchA z := T.zRoute.takeUntil z T.z_mem
def zArmB : G.Walk T.branchB z := (T.zRoute.dropUntil z T.z_mem).reverse
def zRim : G.Walk T.branchA T.branchA :=
  T.xRoute.append T.yRoute.reverse

theorem xRim_isCycle : T.xRim.IsCycle := by
  exact Walk.IsPath.isCycle_append_reverse_of_meet_only_ends T.yRoute_isPath
    T.zRoute_isPath T.y_mem T.y_internal.1 T.y_internal.2
    T.yRoute_inter_zRoute

theorem yRim_isCycle : T.yRim.IsCycle := by
  exact Walk.IsPath.isCycle_append_reverse_of_meet_only_ends T.xRoute_isPath
    T.zRoute_isPath T.x_mem T.x_internal.1 T.x_internal.2
    T.xRoute_inter_zRoute

theorem zRim_isCycle : T.zRim.IsCycle := by
  exact Walk.IsPath.isCycle_append_reverse_of_meet_only_ends T.xRoute_isPath
    T.yRoute_isPath T.x_mem T.x_internal.1 T.x_internal.2
    T.xRoute_inter_yRoute

theorem x_not_mem_xRim : x ∉ T.xRim.support := by
  intro hx
  have hx' : x ∈ T.yRoute.support ∨ x ∈ T.zRoute.support := by
    simpa only [xRim, Walk.mem_support_append_iff, Walk.support_reverse,
      List.mem_reverse] using hx
  rcases hx' with hxY | hxZ
  · rcases T.xRoute_inter_yRoute x T.x_mem hxY with h | h
    · exact T.x_internal.1 h
    · exact T.x_internal.2 h
  · rcases T.xRoute_inter_zRoute x T.x_mem hxZ with h | h
    · exact T.x_internal.1 h
    · exact T.x_internal.2 h

theorem y_not_mem_yRim : y ∉ T.yRim.support := by
  intro hy
  have hy' : y ∈ T.xRoute.support ∨ y ∈ T.zRoute.support := by
    simpa only [yRim, Walk.mem_support_append_iff, Walk.support_reverse,
      List.mem_reverse] using hy
  rcases hy' with hyX | hyZ
  · rcases T.xRoute_inter_yRoute y hyX T.y_mem with h | h
    · exact T.y_internal.1 h
    · exact T.y_internal.2 h
  · rcases T.yRoute_inter_zRoute y T.y_mem hyZ with h | h
    · exact T.y_internal.1 h
    · exact T.y_internal.2 h

theorem z_not_mem_zRim : z ∉ T.zRim.support := by
  intro hz
  have hz' : z ∈ T.xRoute.support ∨ z ∈ T.yRoute.support := by
    simpa only [zRim, Walk.mem_support_append_iff, Walk.support_reverse,
      List.mem_reverse] using hz
  rcases hz' with hzX | hzY
  · rcases T.xRoute_inter_zRoute z hzX T.z_mem with h | h
    · exact T.z_internal.1 h
    · exact T.z_internal.2 h
  · rcases T.yRoute_inter_zRoute z hzY T.z_mem with h | h
    · exact T.z_internal.1 h
    · exact T.z_internal.2 h

end WatkinsMesnerK32Source

/-- Initial segment ending at the first hit of a finite target set. -/
theorem exists_initialPath_to_finset_wm
    (S : Finset V) {r s₀ : V} (hrs : r ∉ S) (hs₀ : s₀ ∈ S)
    (p : G.Walk r s₀) (hp : p.IsPath) :
    ∃ s : V, s ∈ S ∧ ∃ q : G.Walk r s,
      q.IsPath ∧ (∀ w, w ∈ q.support → w ∈ p.support) ∧
        ∀ w, w ∈ q.support → w ∈ S → w = s := by
  let P : ℕ → Prop := fun n ↦
    ∃ s : V, ∃ hs : s ∈ p.support,
      s ∈ S ∧ (p.takeUntil s hs).length = n
  have hP : ∃ n, P n := by
    exact ⟨(p.takeUntil s₀ p.end_mem_support).length,
      s₀, p.end_mem_support, hs₀, rfl⟩
  let n := Nat.find hP
  obtain ⟨s, hs, hsS, hlen⟩ := Nat.find_spec hP
  let q : G.Walk r s := p.takeUntil s hs
  have hq : q.IsPath := hp.takeUntil hs
  have hqSub : ∀ w, w ∈ q.support → w ∈ p.support := by
    intro w hw
    exact p.support_takeUntil_subset_support hs hw
  refine ⟨s, hsS, q, hq, hqSub, ?_⟩
  intro w hwq hwS
  by_contra hws
  have hwp : w ∈ p.support := hqSub w hwq
  have hcandidate : n ≤ (p.takeUntil w hwp).length := by
    apply Nat.find_min'
    exact ⟨w, hwp, hwS, rfl⟩
  have hshort : (q.takeUntil w hwq).length < q.length :=
    q.length_takeUntil_lt_length hwq hws
  have heq : q.takeUntil w hwq = p.takeUntil w hwp := by
    simpa only [q] using p.takeUntil_takeUntil hs hwq
  rw [heq, hlen] at hshort
  exact (Nat.not_lt_of_ge hcandidate) hshort

/-- The two-fan theorem in the path form needed below. -/
private theorem exists_targetPath_through_wm
    (S : Finset V) {r : V} (hrS : r ∉ S) (hcard : 2 ≤ S.card)
    (hconn : G.Connected)
    (hdelete : ∀ d : V, (G.induce fun w : V ↦ w ≠ d).Connected) :
    ∃ s t : V, s ∈ S ∧ t ∈ S ∧ s ≠ t ∧
      ∃ p : G.Walk s t, p.IsPath ∧ r ∈ p.support ∧
        ∀ w, w ∈ p.support → w ∈ S → w = s ∨ w = t := by
  obtain ⟨s₀, hs₀S⟩ := Finset.card_pos.mp (by omega : 0 < S.card)
  have hcardErase : 0 < (S.erase s₀).card := by
    rw [Finset.card_erase_of_mem hs₀S]
    omega
  obtain ⟨t₀, ht₀Erase⟩ := Finset.card_pos.mp hcardErase
  have ht₀S : t₀ ∈ S := Finset.mem_of_mem_erase ht₀Erase
  have hs₀t₀ : s₀ ≠ t₀ := by
    intro h
    subst t₀
    exact (Finset.notMem_erase s₀ S) ht₀Erase
  have hrs₀ : r ≠ s₀ := by intro h; exact hrS (h ▸ hs₀S)
  have hrt₀ : r ≠ t₀ := by intro h; exact hrS (h ▸ ht₀S)
  obtain ⟨p₀, hp₀, hrp₀⟩ := exists_rooted_three_path
    (r := s₀) (a := r) (b := t₀) hrs₀.symm hs₀t₀ hrt₀ hconn hdelete
  let left₀ : G.Walk r s₀ := (p₀.takeUntil r hrp₀).reverse
  let right₀ : G.Walk r t₀ := p₀.dropUntil r hrp₀
  have hleft₀ : left₀.IsPath := (hp₀.takeUntil hrp₀).reverse
  have hright₀ : right₀.IsPath := hp₀.dropUntil hrp₀
  obtain ⟨s, hsS, left, hleft, hleftSub, hleftFirst⟩ :=
    exists_initialPath_to_finset_wm S hrS hs₀S left₀ hleft₀
  obtain ⟨t, htS, right, hright, hrightSub, hrightFirst⟩ :=
    exists_initialPath_to_finset_wm S hrS ht₀S right₀ hright₀
  have hbaseDisj :
      (p₀.takeUntil r hrp₀).support.Disjoint
        (p₀.dropUntil r hrp₀).support.tail := by
    have hnd :
        ((p₀.takeUntil r hrp₀).support ++
          (p₀.dropUntil r hrp₀).support.tail).Nodup := by
      simpa only [← Walk.support_append, p₀.take_spec hrp₀]
        using hp₀.support_nodup
    rw [List.disjoint_left]
    intro w hwTake hwDrop
    exact ((List.nodup_append.mp hnd).2.2 w hwTake w hwDrop) rfl
  have hdisj : left.support.tail.Disjoint right.support.tail := by
    rw [List.disjoint_left]
    intro w hwleft hwright
    have hwleftFull : w ∈ left.support := List.mem_of_mem_tail hwleft
    have hwleft₀ : w ∈ left₀.support := hleftSub w hwleftFull
    have hwTake : w ∈ (p₀.takeUntil r hrp₀).support := by
      simpa only [left₀, Walk.support_reverse, List.mem_reverse] using hwleft₀
    have hwrightFull : w ∈ right.support := List.mem_of_mem_tail hwright
    have hwright₀ : w ∈ right₀.support := hrightSub w hwrightFull
    have hwr : w ≠ r := by
      intro h
      subst w
      have hnd := hright.support_nodup
      rw [← right.cons_tail_support] at hnd
      exact (List.nodup_cons.mp hnd).1 hwright
    have hwDropTail : w ∈ (p₀.dropUntil r hrp₀).support.tail := by
      have hwDrop : w ∈ (p₀.dropUntil r hrp₀).support := by
        simpa only [right₀] using hwright₀
      have hwCases : w = r ∨
          w ∈ (p₀.dropUntil r hrp₀).support.tail := by
        rw [← (p₀.dropUntil r hrp₀).cons_tail_support] at hwDrop
        exact List.mem_cons.mp hwDrop
      exact hwCases.resolve_left hwr
    exact List.disjoint_left.mp hbaseDisj hwTake hwDropTail
  have hst : s ≠ t := by
    intro hst
    have hsTail : s ∈ left.support.tail :=
      left.end_mem_tail_support_of_ne (by
        intro hrs
        apply hrS
        rw [hrs]
        exact hsS)
    have htTail : t ∈ right.support.tail :=
      right.end_mem_tail_support_of_ne (by
        intro hrt
        apply hrS
        rw [hrt]
        exact htS)
    exact List.disjoint_left.mp hdisj hsTail (hst ▸ htTail)
  let p : G.Walk s t := left.reverse.append right
  have hp : p.IsPath := by
    change (left.reverse.append right).IsPath
    rw [Walk.isPath_def, Walk.support_append, List.nodup_append']
    refine ⟨hleft.reverse.support_nodup, hright.support_nodup.tail, ?_⟩
    rw [List.disjoint_left]
    intro w hwleftRev hwrightTail
    have hwleft : w ∈ left.support := by
      simpa only [Walk.support_reverse, List.mem_reverse] using hwleftRev
    have hwr : w ≠ r := by
      intro hwr
      subst w
      have hnd := hright.support_nodup
      rw [← right.cons_tail_support] at hnd
      exact (List.nodup_cons.mp hnd).1 hwrightTail
    have hwleftTail : w ∈ left.support.tail := by
      rw [← left.cons_tail_support] at hwleft
      exact (List.mem_cons.mp hwleft).resolve_left hwr
    exact List.disjoint_left.mp hdisj hwleftTail hwrightTail
  have hrp : r ∈ p.support := by simp [p]
  refine ⟨s, t, hsS, htS, hst, p, hp, hrp, ?_⟩
  intro w hwp hwS
  have hwCases : w ∈ left.support ∨ w ∈ right.support := by
    simpa only [p, Walk.mem_support_append_iff, Walk.support_reverse,
      List.mem_reverse] using hwp
  exact hwCases.elim
    (fun hwleft ↦ Or.inl (hleftFirst w hwleft hwS))
    (fun hwright ↦ Or.inr (hrightFirst w hwright hwS))

/-- The two paths obtained by cutting a simple cycle at two distinct
vertices, both oriented from the first cut vertex to the second. -/
structure CycleArcPair {r : V} (C : G.Walk r r)
    (s t : V) where
  first : G.Walk s t
  second : G.Walk s t
  first_isPath : first.IsPath
  second_isPath : second.IsPath
  first_subset : ∀ w, w ∈ first.support → w ∈ C.support
  second_subset : ∀ w, w ∈ second.support → w ∈ C.support
  cover : ∀ w, w ∈ C.support → w ∈ first.support ∨ w ∈ second.support
  meet_only_ends : ∀ w, w ∈ first.support → w ∈ second.support →
    w = s ∨ w = t

theorem exists_cycleArcPair {r s t : V} {C : G.Walk r r}
    (hC : C.IsCycle) (hsC : s ∈ C.support) (htC : t ∈ C.support)
    (hst : s ≠ t) : Nonempty (CycleArcPair C s t) := by
  let R := C.rotate s hsC
  have hR : R.IsCycle := hC.rotate hsC
  have htR : t ∈ R.support := by
    have htSub : t ∈ C.toSubgraph.verts := by
      simpa only [Walk.mem_verts_toSubgraph] using htC
    have htSubR : t ∈ R.toSubgraph.verts := by
      simpa only [R, Walk.toSubgraph_rotate] using htSub
    simpa only [Walk.mem_verts_toSubgraph] using htSubR
  let P : G.Walk s t := R.takeUntil t htR
  let D : G.Walk t s := R.dropUntil t htR
  let Q : G.Walk s t := D.reverse
  have hP : P.IsPath := hR.isPath_takeUntil htR
  have hPNotNil : ¬P.Nil := by
    intro hnil
    have htP : t ∈ P.support := by simp [P]
    have hts : t = s := by
      simpa [Walk.nil_iff_support_eq.mp hnil] using htP
    exact hst hts.symm
  have hdecomp : R = P.append D := by
    have h := R.take_spec htR
    simpa only [P, D] using h.symm
  have hD : D.IsPath := by
    have hcycle : (P.append D).IsCycle := by rw [← hdecomp]; exact hR
    exact Walk.IsCycle.isPath_of_append_right hPNotNil hcycle
  have hQ : Q.IsPath := hD.reverse
  have htail : (P.support.tail ++ D.support.tail).Nodup := by
    have htailR : (P.append D).support.tail.Nodup := by
      rw [← hdecomp]
      exact hR.2
    simpa only [Walk.tail_support_append] using htailR
  have hdis : P.support.tail.Disjoint D.support.tail := by
    rw [List.disjoint_left]
    intro a ha hb
    exact ((List.nodup_append.mp htail).2.2 a ha a hb) rfl
  have hmeet : ∀ w, w ∈ P.support → w ∈ Q.support → w = s ∨ w = t := by
    intro w hwP hwQ
    have hwD : w ∈ D.support := by
      simpa only [Q, Walk.support_reverse, List.mem_reverse] using hwQ
    have hwPcases : w = s ∨ w ∈ P.support.tail := by
      rw [← P.cons_tail_support] at hwP
      exact List.mem_cons.mp hwP
    rcases hwPcases with hws | hwPt
    · exact Or.inl hws
    have hwDcases : w = t ∨ w ∈ D.support.tail := by
      rw [← D.cons_tail_support] at hwD
      exact List.mem_cons.mp hwD
    rcases hwDcases with hwt | hwDt
    · exact Or.inr hwt
    exact False.elim (List.disjoint_left.mp hdis hwPt hwDt)
  have hmemR_iff (w : V) : w ∈ R.support ↔ w ∈ C.support := by
    constructor
    · intro hw
      have hwSub : w ∈ R.toSubgraph.verts := by
        simpa only [Walk.mem_verts_toSubgraph] using hw
      have hwSubC : w ∈ C.toSubgraph.verts := by
        simpa only [R, Walk.toSubgraph_rotate] using hwSub
      simpa only [Walk.mem_verts_toSubgraph] using hwSubC
    · intro hw
      have hwSub : w ∈ C.toSubgraph.verts := by
        simpa only [Walk.mem_verts_toSubgraph] using hw
      have hwSubR : w ∈ R.toSubgraph.verts := by
        simpa only [R, Walk.toSubgraph_rotate] using hwSub
      simpa only [Walk.mem_verts_toSubgraph] using hwSubR
  refine ⟨{
    first := P
    second := Q
    first_isPath := hP
    second_isPath := hQ
    first_subset := ?_
    second_subset := ?_
    cover := ?_
    meet_only_ends := hmeet }⟩
  · intro w hwP
    apply (hmemR_iff w).mp
    exact R.support_takeUntil_subset_support htR hwP
  · intro w hwQ
    apply (hmemR_iff w).mp
    apply R.support_dropUntil_subset_support htR
    simpa only [Q, Walk.support_reverse, List.mem_reverse] using hwQ
  · intro w hwC
    have hwR : w ∈ R.support := (hmemR_iff w).mpr hwC
    rw [hdecomp, Walk.mem_support_append_iff] at hwR
    exact hwR.imp_right (by
      intro hwD
      simpa only [Q, Walk.support_reverse, List.mem_reverse] using hwD)

/-- Closing a simple path which has a displayed internal vertex by an edge
gives a simple cycle. -/
private theorem Walk.IsPath.isCycle_concat_of_mem
    {u v w : V} {p : G.Walk u v} (hp : p.IsPath)
    (hw : w ∈ p.support) (hwu : w ≠ u) (hwv : w ≠ v)
    (hvu : G.Adj v u) : (p.concat hvu).IsCycle := by
  change (p.append hvu.toWalk).IsCycle
  apply hp.isCycle_append (Walk.IsPath.of_adj hvu)
  · rw [List.disjoint_left]
    intro a ha hb
    have hau : a = u := by simpa using hb
    subst a
    have hnd := hp.support_nodup
    rw [← p.cons_tail_support] at hnd
    exact (List.nodup_cons.mp hnd).1 ha
  · left
    by_contra hlen
    have hle : p.length ≤ 1 := by omega
    have hends : p.support = [u, v] ∨ u = v := by
      cases p with
      | nil => exact Or.inr rfl
      | @cons _ a _ hadj q =>
          cases q with
          | nil => simp
          | @cons _ b _ hab r => simp at hle
    rcases hends with hsupp | huv
    · have hwuv : w = u ∨ w = v := by simpa [hsupp] using hw
      exact hwuv.elim hwu hwv
    · subst v
      have hpnil : p = .nil := Walk.isPath_iff_eq_nil.mp hp
      subst p
      exact hwu (by simpa using hw)

/-- Three distinct vertices force every one of them to have at least two
neighbours in a graph which stays connected after one vertex is deleted. -/
private theorem two_le_degree_of_vertexTwoConnected
    {x y z : V} (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (hconn : G.Connected)
    (hdelete : ∀ d : V, (G.induce fun w : V ↦ w ≠ d).Connected) :
    2 ≤ G.degree x := by
  have hpos : 0 < G.degree x :=
    (hconn x y).degree_pos_left hxy
  by_contra hnot
  have hone : G.degree x = 1 := by omega
  have hcard : (G.neighborFinset x).card = 1 := by
    simpa only [G.card_neighborFinset_eq_degree] using hone
  obtain ⟨a, ha⟩ := Finset.card_eq_one.mp hcard
  let t : V := if y = a then z else y
  have htx : t ≠ x := by
    simp only [t]
    split
    · exact hxz.symm
    · exact hxy.symm
  have hta : t ≠ a := by
    simp only [t]
    split
    · rename_i hya
      intro hza
      exact hyz (hya.trans hza.symm)
    · rename_i hya
      exact hya
  have hxa : x ≠ a := by
    have hamem : a ∈ G.neighborFinset x := by rw [ha]; simp
    exact G.ne_of_adj (by simpa using hamem)
  let x' : {w : V // w ≠ a} := ⟨x, hxa⟩
  let t' : {w : V // w ≠ a} := ⟨t, hta⟩
  have hx't' : x' ≠ t' := by
    intro h
    exact htx (congrArg Subtype.val h).symm
  have hreach := (hdelete a) x' t'
  obtain ⟨b, hb⟩ := hreach.nonempty_neighborSet_left hx't'
  have hbadj : G.Adj x b.1 := hb
  have hbmem : b.1 ∈ G.neighborFinset x := by simpa using hbadj
  have hba : b.1 = a := by simpa [ha] using hbmem
  exact b.2 hba

/-- Any two distinct vertices of a finite vertex-two-connected graph lie on
one simple cycle.  The third named vertex is used only to witness that the
graph has at least three vertices. -/
theorem exists_cycle_through_pair_of_vertexTwoConnected
    {x y z : V} (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (hconn : G.Connected)
    (hdelete : ∀ d : V, (G.induce fun w : V ↦ w ≠ d).Connected) :
    ∃ r : V, ∃ C : G.Walk r r,
      C.IsCycle ∧ x ∈ C.support ∧ y ∈ C.support := by
  have hdeg : 2 ≤ G.degree x :=
    two_le_degree_of_vertexTwoConnected hxy hxz hyz hconn hdelete
  by_cases hxyAdj : G.Adj x y
  · have hcard : 1 < (G.neighborFinset x).card := by
      rw [G.card_neighborFinset_eq_degree]
      omega
    obtain ⟨s, hsN, hsy⟩ := Finset.exists_mem_ne hcard y
    have hxs : G.Adj x s := by simpa using hsN
    have hsx : s ≠ x := (G.ne_of_adj hxs).symm
    let y' : {w : V // w ≠ x} := ⟨y, hxy.symm⟩
    let s' : {w : V // w ≠ x} := ⟨s, hsx⟩
    obtain ⟨p', hp'⟩ := ((hdelete x) y' s').exists_isPath
    let inc := SimpleGraph.Embedding.induce (G := G) (s := fun w : V ↦ w ≠ x)
    let p : G.Walk y s := (p'.map inc.toHom).copy rfl rfl
    have hp : p.IsPath :=
      (Walk.isPath_copy _ _ _).mpr (hp'.map inc.injective)
    have hxP : x ∉ p.support := by
      intro hxp
      change x ∈ ((p'.map inc.toHom).copy rfl rfl).support at hxp
      rw [Walk.support_copy, Walk.support_map] at hxp
      obtain ⟨w, -, hw⟩ := List.mem_map.mp hxp
      exact w.2 (by simpa [inc] using hw)
    let q : G.Walk y x := p.concat hxs.symm
    have hq : q.IsPath := hp.concat hxP hxs.symm
    have hsQ : s ∈ q.support := by simp [q]
    let C : G.Walk y y := q.concat hxyAdj
    have hC : C.IsCycle := by
      exact Walk.IsPath.isCycle_concat_of_mem hq hsQ hsy hsx hxyAdj
    exact ⟨y, C, hC, by simp [C, q], by simp [C]⟩
  · let S := G.neighborFinset x
    have hyS : y ∉ S := by simpa [S]
    have hcard : 2 ≤ S.card := by
      simpa only [S, G.card_neighborFinset_eq_degree] using hdeg
    obtain ⟨s, t, hsS, htS, hst, p, hp, hyp, hfirst⟩ :=
      exists_targetPath_through_wm S hyS hcard hconn hdelete
    have hxs : G.Adj x s := by simpa [S] using hsS
    have hxt : G.Adj x t := by simpa [S] using htS
    have hys : y ≠ s := by
      intro h
      exact hyS (h ▸ hsS)
    have hyt : y ≠ t := by
      intro h
      exact hyS (h ▸ htS)
    by_cases hxP : x ∈ p.support
    · let qL : G.Walk s x := p.takeUntil x hxP
      let qR : G.Walk x t := p.dropUntil x hxP
      have hyCases : y ∈ qL.support ∨ y ∈ qR.support := by
        have hyp' : y ∈ (qL.append qR).support := by
          rw [p.take_spec hxP]
          exact hyp
        simpa only [Walk.mem_support_append_iff] using hyp'
      rcases hyCases with hyL | hyR
      · have hqL : qL.IsPath := hp.takeUntil hxP
        let C : G.Walk s s := qL.concat hxs
        have hC : C.IsCycle :=
          Walk.IsPath.isCycle_concat_of_mem hqL hyL hys hxy.symm hxs
        exact ⟨s, C, hC, by simp [C, qL], by simp [C, hyL]⟩
      · have hqR : qR.IsPath := hp.dropUntil hxP
        let C : G.Walk x x := qR.concat hxt.symm
        have hC : C.IsCycle :=
          Walk.IsPath.isCycle_concat_of_mem hqR hyR hxy.symm hyt hxt.symm
        exact ⟨x, C, hC, by simp [C], by simp [C, hyR]⟩
    · let q : G.Walk x t := p.cons hxs
      have hq : q.IsPath := hp.cons hxP
      have hyQ : y ∈ q.support := by simp [q, hyp]
      let C : G.Walk x x := q.concat hxt.symm
      have hC : C.IsCycle :=
        Walk.IsPath.isCycle_concat_of_mem hq hyQ hxy.symm hyt hxt.symm
      exact ⟨x, C, hC, by simp [C], by simp [C, q, hyp]⟩

/-- **Unconditional Watkins--Mesner source theorem.**  If a finite
vertex-two-connected graph has no cycle through three distinct prescribed
vertices, a cycle through `x,y` has a two-ended ear through `z`, and the
interior of that ear is disjoint from the cycle.

This is the theta-subdivision alternative used at the start of the proof of
AHT Theorem 5.1, before its three maximal two-separators are selected. -/
theorem exists_watkinsMesnerThetaSource
    {x y z : V} (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (hconn : G.Connected)
    (hdelete : ∀ d : V, (G.induce fun w : V ↦ w ≠ d).Connected)
    (hno : ¬HasCycleThroughThree G x y z) :
    Nonempty (WatkinsMesnerThetaSource G x y z) := by
  obtain ⟨r, C, hC, hxC, hyC⟩ :=
    exists_cycle_through_pair_of_vertexTwoConnected
      hxy hxz hyz hconn hdelete
  have hzC : z ∉ C.support := by
    intro hzC
    exact hno ⟨r, C, hC, hxC, hyC, hzC⟩
  let S : Finset V := C.support.toFinset
  have hzS : z ∉ S := by simpa [S] using hzC
  have hcard : 2 ≤ S.card := by
    have hxS : x ∈ S := by simpa [S] using hxC
    have hyS : y ∈ S := by simpa [S] using hyC
    exact Finset.one_lt_card_iff.mpr ⟨x, y, hxS, hyS, hxy⟩
  obtain ⟨s, t, hsS, htS, hst, p, hp, hzp, hfirst⟩ :=
    exists_targetPath_through_wm S hzS hcard hconn hdelete
  refine ⟨{
    rimBase := r
    rim := C
    rim_isCycle := hC
    x_mem_rim := hxC
    y_mem_rim := hyC
    z_not_mem_rim := hzC
    left := s
    right := t
    left_mem_rim := by simpa [S] using hsS
    right_mem_rim := by simpa [S] using htS
    left_ne_right := hst
    cross := p
    cross_isPath := hp
    z_mem_cross := hzp
    cross_meets_rim_only_at_ends := ?_ }⟩
  intro w hwp hwC
  apply hfirst w hwp
  simpa [S] using hwC

/-- AHT Lemma 3.6 in its route form.  The rim arcs between the ends of the
theta ear put `x` and `y` on opposite arcs: if they were on the same arc,
that arc together with the ear would be a cycle through all three terminals.
Thus the two rim arcs and the ear are the three branches of a subdivision of
`K_{3,2}`. -/
theorem exists_watkinsMesnerK32Source
    {x y z : V} (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (hconn : G.Connected)
    (hdelete : ∀ d : V, (G.induce fun w : V ↦ w ≠ d).Connected)
    (hno : ¬HasCycleThroughThree G x y z) :
    Nonempty (WatkinsMesnerK32Source G x y z) := by
  obtain ⟨T⟩ :=
    exists_watkinsMesnerThetaSource hxy hxz hyz hconn hdelete hno
  obtain ⟨A⟩ := exists_cycleArcPair T.rim_isCycle T.left_mem_rim
    T.right_mem_rim T.left_ne_right
  have hzLeft : z ≠ T.left := by
    intro h
    apply T.z_not_mem_rim
    simpa only [h] using T.left_mem_rim
  have hzRight : z ≠ T.right := by
    intro h
    apply T.z_not_mem_rim
    simpa only [h] using T.right_mem_rim
  have cross_arc_cycle (q : G.Walk T.left T.right) (hq : q.IsPath)
      (hqSub : ∀ w, w ∈ q.support → w ∈ T.rim.support) :
      (T.cross.append q.reverse).IsCycle := by
    exact Walk.IsPath.isCycle_append_reverse_of_meet_only_ends
      T.cross_isPath hq T.z_mem_cross hzLeft hzRight
      (fun w hwCross hwq ↦
        T.cross_meets_rim_only_at_ends w hwCross (hqSub w hwq))
  have hnotFirst : ¬(x ∈ A.first.support ∧ y ∈ A.first.support) := by
    rintro ⟨hx, hy⟩
    let C : G.Walk T.left T.left := T.cross.append A.first.reverse
    apply hno
    refine ⟨T.left, C,
      cross_arc_cycle A.first A.first_isPath A.first_subset, ?_, ?_, ?_⟩
    · simpa only [C, Walk.mem_support_append_iff, Walk.support_reverse,
        List.mem_reverse] using Or.inr hx
    · simpa only [C, Walk.mem_support_append_iff, Walk.support_reverse,
        List.mem_reverse] using Or.inr hy
    · simpa only [C, Walk.mem_support_append_iff] using Or.inl T.z_mem_cross
  have hnotSecond : ¬(x ∈ A.second.support ∧ y ∈ A.second.support) := by
    rintro ⟨hx, hy⟩
    let C : G.Walk T.left T.left := T.cross.append A.second.reverse
    apply hno
    refine ⟨T.left, C,
      cross_arc_cycle A.second A.second_isPath A.second_subset, ?_, ?_, ?_⟩
    · simpa only [C, Walk.mem_support_append_iff, Walk.support_reverse,
        List.mem_reverse] using Or.inr hx
    · simpa only [C, Walk.mem_support_append_iff, Walk.support_reverse,
        List.mem_reverse] using Or.inr hy
    · simpa only [C, Walk.mem_support_append_iff] using Or.inl T.z_mem_cross
  rcases A.cover x T.x_mem_rim with hxFirst | hxSecond <;>
    rcases A.cover y T.y_mem_rim with hyFirst | hySecond
  · exact (hnotFirst ⟨hxFirst, hyFirst⟩).elim
  · have hxLeft : x ≠ T.left := by
      intro h
      apply hnotSecond
      refine ⟨?_, hySecond⟩
      simpa only [h] using A.second.start_mem_support
    have hxRight : x ≠ T.right := by
      intro h
      apply hnotSecond
      refine ⟨?_, hySecond⟩
      simpa only [h] using A.second.end_mem_support
    have hyLeft : y ≠ T.left := by
      intro h
      apply hnotFirst
      refine ⟨hxFirst, ?_⟩
      simpa only [h] using A.first.start_mem_support
    have hyRight : y ≠ T.right := by
      intro h
      apply hnotFirst
      refine ⟨hxFirst, ?_⟩
      simpa only [h] using A.first.end_mem_support
    exact ⟨{
      branchA := T.left
      branchB := T.right
      branch_ne := T.left_ne_right
      xRoute := A.first
      yRoute := A.second
      zRoute := T.cross
      xRoute_isPath := A.first_isPath
      yRoute_isPath := A.second_isPath
      zRoute_isPath := T.cross_isPath
      x_mem := hxFirst
      y_mem := hySecond
      z_mem := T.z_mem_cross
      x_internal := ⟨hxLeft, hxRight⟩
      y_internal := ⟨hyLeft, hyRight⟩
      z_internal := ⟨hzLeft, hzRight⟩
      xRoute_inter_yRoute := A.meet_only_ends
      xRoute_inter_zRoute := by
        intro w hwArc hwCross
        exact T.cross_meets_rim_only_at_ends w hwCross
          (A.first_subset w hwArc)
      yRoute_inter_zRoute := by
        intro w hwArc hwCross
        exact T.cross_meets_rim_only_at_ends w hwCross
          (A.second_subset w hwArc) }⟩
  · have hxLeft : x ≠ T.left := by
      intro h
      apply hnotFirst
      refine ⟨?_, hyFirst⟩
      simpa only [h] using A.first.start_mem_support
    have hxRight : x ≠ T.right := by
      intro h
      apply hnotFirst
      refine ⟨?_, hyFirst⟩
      simpa only [h] using A.first.end_mem_support
    have hyLeft : y ≠ T.left := by
      intro h
      apply hnotSecond
      refine ⟨hxSecond, ?_⟩
      simpa only [h] using A.second.start_mem_support
    have hyRight : y ≠ T.right := by
      intro h
      apply hnotSecond
      refine ⟨hxSecond, ?_⟩
      simpa only [h] using A.second.end_mem_support
    exact ⟨{
      branchA := T.left
      branchB := T.right
      branch_ne := T.left_ne_right
      xRoute := A.second
      yRoute := A.first
      zRoute := T.cross
      xRoute_isPath := A.second_isPath
      yRoute_isPath := A.first_isPath
      zRoute_isPath := T.cross_isPath
      x_mem := hxSecond
      y_mem := hyFirst
      z_mem := T.z_mem_cross
      x_internal := ⟨hxLeft, hxRight⟩
      y_internal := ⟨hyLeft, hyRight⟩
      z_internal := ⟨hzLeft, hzRight⟩
      xRoute_inter_yRoute := by
        intro w hwSecond hwFirst
        exact A.meet_only_ends w hwFirst hwSecond
      xRoute_inter_zRoute := by
        intro w hwArc hwCross
        exact T.cross_meets_rim_only_at_ends w hwCross
          (A.second_subset w hwArc)
      yRoute_inter_zRoute := by
        intro w hwArc hwCross
        exact T.cross_meets_rim_only_at_ends w hwCross
          (A.first_subset w hwArc) }⟩
  · exact (hnotSecond ⟨hxSecond, hySecond⟩).elim

/-- The source alternative in unconditional disjunctive form: either the
three terminals lie on a common cycle, or the Watkins--Mesner theta source
exists. -/
theorem hasCycleThroughThree_or_watkinsMesnerThetaSource
    {x y z : V} (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (hconn : G.Connected)
    (hdelete : ∀ d : V, (G.induce fun w : V ↦ w ≠ d).Connected) :
    HasCycleThroughThree G x y z ∨
      Nonempty (WatkinsMesnerThetaSource G x y z) := by
  by_cases hcycle : HasCycleThroughThree G x y z
  · exact Or.inl hcycle
  · exact Or.inr
      (exists_watkinsMesnerThetaSource hxy hxz hyz hconn hdelete hcycle)

/-! ## Three-path Menger input for the separator refinement -/

/-- Three explicitly indexed, fully vertex-disjoint paths between two
vertex sets.  Splitting a fan centre into three false twins turns this into
the ordinary three-fan used in AHT Lemma 3.5. -/
structure ThreeABLinkage {W : Type*} (H : SimpleGraph W) (A B : Set W) where
  left : Fin 3 → W
  right : Fin 3 → W
  path : ∀ i, H.Walk (left i) (right i)
  left_mem : ∀ i, left i ∈ A
  right_mem : ∀ i, right i ∈ B
  isPath : ∀ i, (path i).IsPath
  disjoint : Pairwise fun i j ↦
    Disjoint {v | v ∈ (path i).support} {v | v ∈ (path j).support}

/-- Finite vertex Menger, specialized to three paths. -/
theorem exists_threeABLinkage_of_separator_three_le {W : Type} [Finite W]
    (H : SimpleGraph W) (A B : Set W)
    (hsep : ∀ S, Erdos599.Separates H A B S → 3 ≤ S.ncard) :
    Nonempty (ThreeABLinkage H A B) := by
  classical
  have hEM : Erdos599.HasErdosMengerPair H A B :=
    Erdos599.hasErdosMengerPair_of_safePathRemoval_of_countable
      Erdos599.safePathRemoval H A B (Set.toFinite A).countable
  rcases hEM with ⟨ι, left, right, path, S, hleft, hright, hpath,
    hdisjoint, hSsub, horth, hseparates⟩
  have hScard : 3 ≤ S.ncard := hsep S hseparates
  have hSfinite : S.Finite := Set.toFinite S
  let _ : Fintype S := hSfinite.fintype
  have hcard : 3 ≤ Fintype.card S := by
    simpa [Set.fintypeCard_eq_ncard] using hScard
  have hthree : Fintype.card (Fin 3) ≤ Fintype.card S := by
    simpa using hcard
  rcases Function.Embedding.nonempty_of_card_le hthree with ⟨pickS⟩
  choose pickI hpickI using fun i : Fin 3 ↦ hSsub (pickS i).property
  have hpickI_inj : Function.Injective pickI := by
    intro i j hij
    by_contra hne
    have hi : (pickS i : W) ∈ S ∧
        (pickS i : W) ∈ (path (pickI i)).support :=
      ⟨(pickS i).property, hpickI i⟩
    have hj : (pickS j : W) ∈ S ∧
        (pickS j : W) ∈ (path (pickI i)).support := by
      rw [hij]
      exact ⟨(pickS j).property, hpickI j⟩
    have hsEq : (pickS i : W) = pickS j :=
      (horth (pickI i)).unique hi hj
    exact hne (pickS.injective (Subtype.ext hsEq))
  exact ⟨{
    left := fun i ↦ left (pickI i)
    right := fun i ↦ right (pickI i)
    path := fun i ↦ path (pickI i)
    left_mem := fun i ↦ hleft (pickI i)
    right_mem := fun i ↦ hright (pickI i)
    isPath := fun i ↦ hpath (pickI i)
    disjoint := fun i j hij ↦ hdisjoint (hpickI_inj.ne hij) }⟩

end Erdos916
