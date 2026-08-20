import ErdosProblems.Erdos751
import ErdosProblems.Erdos916.Blocks

/-!
# Maximum-component induced cycles for Erdős Problem 916

This file sets up the finite maximization used in Lemma 2 of Thomassen--Toft,
*Non-separating induced cycles in graphs*.  An admissible cycle is chordless and
avoids a prescribed connected vertex set `S`.  For a root `x ∈ S`, its target
is the component of the cycle complement containing `x`.

The file proves all of the finite-choice and connected-component bookkeeping:

* a connected prescribed set lies in the target component;
* the target induces a connected graph;
* the whole cycle complement is connected exactly when it is the target;
* a target-cardinality maximizing admissible cycle exists;
* every component of a cycle complement in a vertex-2-connected graph has two
  distinct attachments to the cycle;
* any strict target-augmentation theorem implies that the chosen maximizer is
  nonseparating.

The last item isolates the remaining graph-surgery step in the published proof:
one replaces a separating induced cycle by another admissible induced cycle
whose prescribed component is strictly larger.
-/

open Finset

attribute [local instance] Classical.propDecidable

namespace Erdos916

open SimpleGraph

namespace Nonseparating

open Erdos751.BV

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

/-! ## Admissible cycles and their rooted component -/

/-- An admissible cycle for a prescribed set is induced and vertex-disjoint
from that set. -/
def IsAdmissibleCycle (S : Set V) (C : Cycle (G := G)) : Prop :=
  C.IsChordless (G := G) ∧ Disjoint (C.vSet (G := G)) S

theorem IsAdmissibleCycle.not_mem_cycle {S : Set V} {C : Cycle (G := G)}
    (hC : IsAdmissibleCycle G S C) {x : V} (hx : x ∈ S) :
    x ∉ C.vSet (G := G) := by
  exact fun hxC ↦ Set.disjoint_left.mp hC.2 hxC hx

/-- The component of `G - C` containing `x`, regarded as a set of ambient
vertices.  It is empty when `x` lies on `C`; admissibility ensures this does
not happen for a prescribed root. -/
def targetSet (C : Cycle (G := G)) (x : V) : Set V :=
  {y | ∃ hx : x ∉ C.vSet (G := G), y ∈ G.componentComplMk hx}

/-- Cardinality of the rooted component. -/
noncomputable def targetCard (C : Cycle (G := G)) (x : V) : ℕ :=
  (targetSet G C x).ncard

theorem targetSet_eq_component {C : Cycle (G := G)} {x : V}
    (hx : x ∉ C.vSet (G := G)) :
    targetSet G C x = (G.componentComplMk hx : Set V) := by
  ext y
  constructor
  · rintro ⟨hx', hy⟩
    have hh : G.componentComplMk hx' = G.componentComplMk hx := by
      congr
    rw [hh] at hy
    exact hy
  · intro hy
    exact ⟨hx, hy⟩

theorem targetSet_subset_compl {C : Cycle (G := G)} {x : V}
    (hx : x ∉ C.vSet (G := G)) :
    targetSet G C x ⊆ (C.vSet (G := G))ᶜ := by
  rw [targetSet_eq_component G hx]
  intro y hy
  exact ComponentCompl.notMem_of_mem hy

theorem root_mem_targetSet {C : Cycle (G := G)} {x : V}
    (hx : x ∉ C.vSet (G := G)) : x ∈ targetSet G C x := by
  rw [targetSet_eq_component G hx]
  exact G.componentComplMk_mem hx

/-- The rooted component, by itself, is connected. -/
theorem targetSet_connected {C : Cycle (G := G)} {x : V}
    (hx : x ∉ C.vSet (G := G)) :
    (G.induce (targetSet G C x)).Connected := by
  rw [targetSet_eq_component G hx]
  let K := G.componentComplMk hx
  let f : K.toSimpleGraph →g G.induce (K : Set V) :=
    { toFun := fun v ↦ ⟨v.1.1, v.1.2, v.2⟩
      map_rel' := fun h ↦ h }
  have hf : Function.Surjective f := by
    rintro ⟨v, hv⟩
    obtain ⟨hvout, hvK⟩ := hv
    exact ⟨⟨⟨v, hvout⟩, hvK⟩, rfl⟩
  exact K.connected_toSimpleGraph.map f hf

theorem targetCard_le_card (C : Cycle (G := G)) (x : V) :
    targetCard G C x ≤ Fintype.card V := by
  simpa only [targetCard, Nat.card_eq_fintype_card] using
    Set.ncard_le_card (targetSet G C x)

theorem targetCard_pos {C : Cycle (G := G)} {x : V}
    (hx : x ∉ C.vSet (G := G)) : 0 < targetCard G C x := by
  rw [targetCard]
  exact (Set.ncard_pos (Set.toFinite (targetSet G C x))).mpr
    ⟨x, root_mem_targetSet G hx⟩

/-! ## A connected prescribed set lies in the target -/

/-- If the prescribed set is connected and the cycle avoids it, every
prescribed vertex belongs to the rooted component. -/
theorem prescribed_subset_target {S : Set V} (hS : (G.induce S).Connected)
    {C : Cycle (G := G)} (hC : IsAdmissibleCycle G S C)
    {x : V} (hxS : x ∈ S) : S ⊆ targetSet G C x := by
  intro y hyS
  have hxout : x ∉ C.vSet (G := G) :=
    IsAdmissibleCycle.not_mem_cycle (G := G) hC hxS
  have hyout : y ∉ C.vSet (G := G) :=
    IsAdmissibleCycle.not_mem_cycle (G := G) hC hyS
  let f : G.induce S →g G.induce (C.vSet (G := G))ᶜ :=
    { toFun := fun z ↦
        ⟨z.1, IsAdmissibleCycle.not_mem_cycle (G := G) hC z.2⟩
      map_rel' := by
        intro u v huv
        exact huv }
  have hreach :
      (G.induce (C.vSet (G := G))ᶜ).Reachable
        ⟨x, hxout⟩ ⟨y, hyout⟩ := by
    have hr := (hS.preconnected ⟨x, hxS⟩ ⟨y, hyS⟩).map f
    convert hr using 1 <;> apply Subtype.ext <;> rfl
  have heq : G.componentComplMk hxout = G.componentComplMk hyout := by
    rw [ConnectedComponent.eq]
    exact hreach
  refine ⟨hxout, ?_⟩
  exact ⟨hyout, heq.symm⟩

/-! ## Connectivity of the whole complement -/

/-- The cycle complement is connected exactly when every outside vertex is
in the rooted component. -/
theorem complement_connected_iff_target_eq {C : Cycle (G := G)} {x : V}
    (hx : x ∉ C.vSet (G := G)) :
    (G.induce (C.vSet (G := G))ᶜ).Connected ↔
      targetSet G C x = (C.vSet (G := G))ᶜ := by
  constructor
  · intro hconn
    apply Set.Subset.antisymm (targetSet_subset_compl G hx)
    intro y hyout
    have hreach :
        (G.induce (C.vSet (G := G))ᶜ).Reachable
          ⟨x, hx⟩ ⟨y, hyout⟩ := hconn.preconnected _ _
    have heq : G.componentComplMk hx = G.componentComplMk hyout := by
      rw [ConnectedComponent.eq]
      exact hreach
    exact ⟨hx, hyout, heq.symm⟩
  · intro htarget
    have hconn := targetSet_connected G hx
    rw [htarget] at hconn
    exact hconn

/-- If the complement is disconnected, there is an outside vertex not in the
rooted component. -/
theorem exists_outside_target_of_not_connected {C : Cycle (G := G)} {x : V}
    (hx : x ∉ C.vSet (G := G))
    (hdisc : ¬(G.induce (C.vSet (G := G))ᶜ).Connected) :
    ∃ y : V, y ∉ C.vSet (G := G) ∧ y ∉ targetSet G C x := by
  have hne : targetSet G C x ≠ (C.vSet (G := G))ᶜ := by
    intro heq
    exact hdisc ((complement_connected_iff_target_eq G hx).mpr heq)
  have hnsub : ¬(C.vSet (G := G))ᶜ ⊆ targetSet G C x := by
    intro hsub
    exact hne (Set.Subset.antisymm (targetSet_subset_compl G hx) hsub)
  obtain ⟨y, hyout, hytarget⟩ := Set.not_subset.mp hnsub
  exact ⟨y, hyout, hytarget⟩

/-- An edge cannot join two different components of the cycle complement. -/
theorem not_adj_target_of_not_mem {C : Cycle (G := G)} {x u y : V}
    (hx : x ∉ C.vSet (G := G)) (hu : u ∈ targetSet G C x)
    (hyout : y ∉ C.vSet (G := G)) (hy : y ∉ targetSet G C x) :
    ¬G.Adj u y := by
  intro huy
  rw [targetSet_eq_component G hx] at hu
  exact hy (by
    rw [targetSet_eq_component G hx]
    exact ComponentCompl.mem_of_adj u y hu hyout huy)

/-! ## Two attachments from vertex-2-connectivity -/

/-- The cycle vertex set is nonempty. -/
theorem cycle_vSet_nonempty (C : Cycle (G := G)) :
    (C.vSet (G := G)).Nonempty := by
  refine ⟨C.base, ?_⟩
  apply C.mem_vSet_iff.mpr
  simp [Cycle.verts]

/-- Every component of a cycle complement in a vertex-2-connected graph has
at least one attachment to the cycle. -/
theorem exists_attachment
    (h2 : VertexTwoConnected (G := G)) (C : Cycle (G := G))
    (K : Bridge (G := G) C) :
    ∃ x : V, x ∈ attachSet (G := G) C K := by
  obtain ⟨ck, hckK, hckC, hAdj⟩ :=
    ComponentCompl.exists_adj_boundary_pair h2.1.preconnected
      (cycle_vSet_nonempty G C) K
  refine ⟨ck.2, hckC, ck.1, ?_, ?_⟩
  · simpa [bridgeSet] using hckK
  · simpa only using hAdj.symm

/-- Every component of a cycle complement in a vertex-2-connected graph has
two distinct attachment vertices on the cycle. -/
theorem exists_two_attachments
    (h2 : VertexTwoConnected (G := G)) (C : Cycle (G := G))
    (K : Bridge (G := G) C) :
    ∃ x y : V, x ≠ y ∧
      x ∈ attachSet (G := G) C K ∧ y ∈ attachSet (G := G) C K := by
  classical
  obtain ⟨x, hx⟩ := exists_attachment G h2 C K
  by_contra hno
  have hsubset : attachSet (G := G) C K ⊆ ({x} : Set V) := by
    intro y hy
    by_cases hyx : y = x
    · simpa [hyx]
    · exfalso
      exact hno ⟨x, y, by simpa [ne_comm] using hyx, hx, hy⟩
  obtain ⟨u, huK⟩ := ComponentCompl.nonempty (C := K)
  have huK' : u ∈ bridgeSet (G := G) C K := by
    simpa only [bridgeSet] using huK
  have hxC : x ∈ C.vSet (G := G) := hx.1
  have hx_supp : x ∈ C.walk.support := by
    have hx' : x ∈ C.verts (G := G) := C.mem_vSet_iff.mp hxC
    simpa only [Cycle.verts, List.mem_toFinset] using hx'
  let r := C.walk.rotate x hx_supp
  have hr_cycle : r.IsCycle := C.isCycle.rotate hx_supp
  have hr_not_nil : ¬r.Nil := hr_cycle.not_nil
  let y₀ : V := r.snd
  have hy₀_ne_x : y₀ ≠ x := by
    have hadj : G.Adj x y₀ := Walk.adj_snd hr_not_nil
    exact hadj.ne.symm
  have hy₀C : y₀ ∈ C.vSet (G := G) := by
    have hy₀r : y₀ ∈ r.support := Walk.getVert_mem_support (p := r) 1
    have hy₀sub : y₀ ∈ r.toSubgraph.verts := by
      simpa only [Walk.mem_verts_toSubgraph] using hy₀r
    have hy₀sub' : y₀ ∈ C.walk.toSubgraph.verts := by
      simpa only [r, Walk.toSubgraph_rotate] using hy₀sub
    have hy₀supp : y₀ ∈ C.walk.support := by
      simpa only [Walk.mem_verts_toSubgraph] using hy₀sub'
    apply C.mem_vSet_iff.mpr
    simpa only [Cycle.verts, List.mem_toFinset] using hy₀supp
  let X : Set V := {v | v ≠ x}
  have hstay :
      ∀ {a b : {v // v ∈ X}} (p : (G.induce X).Walk a b),
        a.1 ∈ bridgeSet (G := G) C K → b.1 ∈ bridgeSet (G := G) C K := by
    intro a b p ha
    induction p with
    | nil => simpa only using ha
    | @cons a b c hab p ih =>
        have habG : G.Adj (a : V) (b : V) := hab
        have hb_ne : (b : V) ≠ x := b.property
        have hbK : (b : V) ∈ bridgeSet (G := G) C K := by
          by_cases hbC : (b : V) ∈ C.vSet (G := G)
          · have hbatt : (b : V) ∈ attachSet (G := G) C K :=
              ⟨hbC, a.1, ha, by simpa only using habG.symm⟩
            have hbx : (b : V) = x := by
              simpa only [Set.mem_singleton_iff] using hsubset hbatt
            exact (hb_ne hbx).elim
          · exact mem_bridge_of_adj_outside (G := G) C K ha hbC habG
        exact ih hbK
  have hu_ne_x : u ≠ x := by
    intro hux
    have huout : u ∉ C.vSet (G := G) := mem_bridge_imp_not_mem_cycle G C K huK'
    exact huout (hux ▸ hxC)
  have hreach :
      (G.induce X).Reachable ⟨u, hu_ne_x⟩ ⟨y₀, hy₀_ne_x⟩ :=
    (h2.2 x).preconnected _ _
  obtain ⟨p⟩ := hreach
  have hy₀K : y₀ ∈ bridgeSet (G := G) C K := hstay p huK'
  exact (mem_bridge_imp_not_mem_cycle G C K hy₀K) hy₀C

/-! ## Finite maximum of the prescribed component -/

/-- The rooted cardinality `n` occurs among admissible cycles. -/
def TargetCardOccurs (S : Set V) (x : V) (n : ℕ) : Prop :=
  ∃ C : Cycle (G := G), IsAdmissibleCycle G S C ∧ targetCard G C x = n

/-- Maximum rooted-component cardinality among admissible cycles. -/
noncomputable def maxTargetCard (S : Set V) (x : V) : ℕ :=
  Nat.findGreatest (TargetCardOccurs G S x) (Fintype.card V)

theorem targetCardOccurs_max {S : Set V} {x : V}
    (hseed : ∃ C : Cycle (G := G), IsAdmissibleCycle G S C) :
    TargetCardOccurs G S x (maxTargetCard G S x) := by
  obtain ⟨C, hC⟩ := hseed
  have hocc : TargetCardOccurs G S x (targetCard G C x) := ⟨C, hC, rfl⟩
  have hle := targetCard_le_card G C x
  simpa only [maxTargetCard] using
    Nat.findGreatest_spec (P := TargetCardOccurs G S x) hle hocc

/-- A chosen admissible induced cycle maximizing the component containing the
prescribed root. -/
noncomputable def maximizingCycle {S : Set V} (x : V)
    (hseed : ∃ C : Cycle (G := G), IsAdmissibleCycle G S C) : Cycle (G := G) :=
  Classical.choose (targetCardOccurs_max (x := x) G hseed)

theorem maximizingCycle_admissible {S : Set V} {x : V}
    (hseed : ∃ C : Cycle (G := G), IsAdmissibleCycle G S C) :
    IsAdmissibleCycle G S (maximizingCycle G x hseed) :=
  (Classical.choose_spec (targetCardOccurs_max (x := x) G hseed)).1

theorem targetCard_maximizingCycle {S : Set V} {x : V}
    (hseed : ∃ C : Cycle (G := G), IsAdmissibleCycle G S C) :
    targetCard G (maximizingCycle G x hseed) x = maxTargetCard G S x :=
  (Classical.choose_spec (targetCardOccurs_max (x := x) G hseed)).2

theorem targetCard_le_max {S : Set V} {x : V}
    (C : Cycle (G := G)) (hC : IsAdmissibleCycle G S C) :
    targetCard G C x ≤ maxTargetCard G S x := by
  by_contra hnot
  have hlt : maxTargetCard G S x < targetCard G C x := Nat.lt_of_not_ge hnot
  have hbound := targetCard_le_card G C x
  have hnotOcc : ¬TargetCardOccurs G S x (targetCard G C x) := by
    apply Nat.findGreatest_is_greatest (P := TargetCardOccurs G S x)
      (n := Fintype.card V)
    · simpa only [maxTargetCard] using hlt
    · exact hbound
  exact hnotOcc ⟨C, hC, rfl⟩

/-- The one graph-surgery property still needed from the combinatorial core
of Thomassen--Toft Lemma 2. -/
def TargetAugmentationProperty (S : Set V) (x : V) : Prop :=
  ∀ C : Cycle (G := G), IsAdmissibleCycle G S C →
    targetSet G C x ≠ (C.vSet (G := G))ᶜ →
      ∃ D : Cycle (G := G), IsAdmissibleCycle G S D ∧
        targetCard G C x < targetCard G D x

/-- Once strict augmentation is available, a maximizing admissible cycle has
connected complement.  This is the finite-maximality conclusion of TT Lemma 2. -/
theorem maximizingCycle_complement_connected_of_augmentation
    {S : Set V} {x : V} (hxS : x ∈ S)
    (hseed : ∃ C : Cycle (G := G), IsAdmissibleCycle G S C)
    (haug : TargetAugmentationProperty G S x) :
    (G.induce
      ((maximizingCycle G x hseed).vSet (G := G))ᶜ).Connected := by
  let C := maximizingCycle G x hseed
  have hC : IsAdmissibleCycle G S C := maximizingCycle_admissible G hseed
  have hxout : x ∉ C.vSet (G := G) :=
    IsAdmissibleCycle.not_mem_cycle (G := G) hC hxS
  rw [complement_connected_iff_target_eq G hxout]
  by_contra hne
  obtain ⟨D, hD, hlt⟩ := haug C hC hne
  have hle := targetCard_le_max (x := x) G D hD
  have heq := targetCard_maximizingCycle (x := x) G hseed
  change targetCard G C x = maxTargetCard G S x at heq
  omega

/-! ## Degree and connectivity hypotheses of the specialized TT lemma -/

/-- All vertices have degree at least three, except that `x₀` is allowed
to have degree two. -/
def AlmostMinDegreeThree (x₀ : V) : Prop :=
  2 ≤ G.degree x₀ ∧ ∀ v : V, v ≠ x₀ → 3 ≤ G.degree v

end Nonseparating

end Erdos916
