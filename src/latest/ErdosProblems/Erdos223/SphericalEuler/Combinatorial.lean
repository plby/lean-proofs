/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

import Mathlib.Combinatorics.SimpleGraph.Bipartite
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Finite
import Mathlib.GroupTheory.Perm.Cycle.Type
import Mathlib.Tactic

/-!
A purely combinatorial construction of genus-zero ribbon graphs.

The outer multiset indexes connected components.  The inner multiset records
the boundary-cycle lengths of that component.  Thus, unlike the connected
case, the inner cycles are *not* identified with the connected components of
the complement of a simultaneous drawing of all components on one sphere.

The constructors are the local changes made by:

* inserting an isolated vertex (a new component with one length-zero boundary);
* inserting a bridge between two components (two selected boundary cycles merge);
* inserting a non-bridge edge inside one boundary cycle (that cycle splits).

Multiset equality permits the selected component/cycle to be moved to the
head before applying a constructor.
-/

def boundaryCount (components : Multiset (Multiset ℕ)) : ℕ :=
  (components.map Multiset.card).sum

def perimeterSum (components : Multiset (Multiset ℕ)) : ℕ :=
  (components.map Multiset.sum).sum

inductive SphereRibbonConstruction :
    (vertices edges : ℕ) → Multiset (Multiset ℕ) → Prop
  | empty : SphereRibbonConstruction 0 0 0
  | isolated {v e components} :
      SphereRibbonConstruction v e components →
      SphereRibbonConstruction (v + 1) e ({0} ::ₘ components)
  | bridge {v e components p q a b} :
      SphereRibbonConstruction v e ((a ::ₘ p) ::ₘ (b ::ₘ q) ::ₘ components) →
      SphereRibbonConstruction v (e + 1)
        (((a + b + 2) ::ₘ (p + q)) ::ₘ components)
  | chord {v e components p a b} :
      SphereRibbonConstruction v e (((a + b) ::ₘ p) ::ₘ components) →
      SphereRibbonConstruction v (e + 1)
        (((a + 1) ::ₘ (b + 1) ::ₘ p) ::ₘ components)

namespace SphereRibbonConstruction

/-- The ribbon-graph Euler equation, summed over connected components. -/
theorem euler {v e : ℕ} {components : Multiset (Multiset ℕ)}
    (h : SphereRibbonConstruction v e components) :
    v + boundaryCount components = e + 2 * components.card := by
  induction h with
  | empty => simp [boundaryCount]
  | isolated h ih =>
      simp only [boundaryCount, Multiset.map_cons, Multiset.sum_cons,
        Multiset.card_cons, Multiset.card_singleton] at ih ⊢
      omega
  | bridge h ih =>
      simp only [boundaryCount, Multiset.map_cons, Multiset.sum_cons,
        Multiset.card_cons, Multiset.card_add] at ih ⊢
      omega
  | chord h ih =>
      simp only [boundaryCount, Multiset.map_cons, Multiset.sum_cons,
        Multiset.card_cons] at ih ⊢
      omega

/-- Each edge supplies exactly two darts among all boundary cycles. -/
theorem sum_perimeters {v e : ℕ} {components : Multiset (Multiset ℕ)}
    (h : SphereRibbonConstruction v e components) :
    perimeterSum components = 2 * e := by
  induction h with
  | empty => simp [perimeterSum]
  | isolated h ih =>
      simpa [perimeterSum] using ih
  | bridge h ih =>
      simp only [perimeterSum, Multiset.map_cons, Multiset.sum_cons,
        Multiset.sum_add] at ih ⊢
      omega
  | chord h ih =>
      simp only [perimeterSum, Multiset.map_cons, Multiset.sum_cons] at ih ⊢
      omega

private theorem four_mul_card_le_sum {p : Multiset ℕ}
    (h : ∀ k ∈ p, 4 ≤ k) : 4 * p.card ≤ p.sum := by
  induction p using Multiset.induction_on with
  | empty => simp
  | @cons k p ih =>
      simp only [Multiset.card_cons, Multiset.sum_cons, mul_add]
      have hk : 4 ≤ k := h k (by simp)
      have hp : 4 * p.card ≤ p.sum := ih (fun x hx ↦ h x (by simp [hx]))
      omega

private theorem four_mul_boundaryCount_le_perimeterSum
    {components : Multiset (Multiset ℕ)}
    (hface : ∀ p ∈ components, ∀ k ∈ p, 4 ≤ k) :
    4 * boundaryCount components ≤ perimeterSum components := by
  induction components using Multiset.induction_on with
  | empty => simp [boundaryCount, perimeterSum]
  | @cons p components ih =>
      have hp := four_mul_card_le_sum (fun k hk ↦ hface p (by simp) k hk)
      have hcomponents := ih (fun q hq k hk ↦ hface q (by simp [hq]) k hk)
      simpa only [boundaryCount, perimeterSum, Multiset.map_cons, Multiset.sum_cons,
        mul_add] using Nat.add_le_add hp hcomponents

/-- The bipartite planar bound in its componentwise sharp form. -/
theorem edge_add_four_mul_components_le_two_mul_vertices
    {v e : ℕ} {components : Multiset (Multiset ℕ)}
    (h : SphereRibbonConstruction v e components)
    (hface : ∀ p ∈ components, ∀ k ∈ p, 4 ≤ k) :
    e + 4 * components.card ≤ 2 * v := by
  have heuler := h.euler
  have hsum := h.sum_perimeters
  have hfaces := four_mul_boundaryCount_le_perimeterSum hface
  omega

/-- The usual nonempty bipartite planar bound. -/
theorem edge_add_four_le_two_mul_vertices
    {v e : ℕ} {components : Multiset (Multiset ℕ)}
    (h : SphereRibbonConstruction v e components)
    (hne : components ≠ 0)
    (hface : ∀ p ∈ components, ∀ k ∈ p, 4 ≤ k) :
    e + 4 ≤ 2 * v := by
  have hc : 0 < components.card := Multiset.card_pos.mpr hne
  have hbound := h.edge_add_four_mul_components_le_two_mul_vertices hface
  omega

end SphereRibbonConstruction

namespace SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V]

noncomputable def ribbonDartFlip (G : SimpleGraph V) : Equiv.Perm G.Dart where
  toFun := Dart.symm
  invFun := Dart.symm
  left_inv := Dart.symm_symm
  right_inv := Dart.symm_symm

noncomputable def ribbonFacePerm
    (G : SimpleGraph V) (rotation : Equiv.Perm G.Dart) : Equiv.Perm G.Dart :=
  rotation * ribbonDartFlip G

private def doubleCoverSide : V ⊕ V → Bool
  | .inl _ => false
  | .inr _ => true

/-- In the bipartite double cover, every boundary cycle of a genuine cyclic
vertex rotation has length at least four as soon as every vertex has degree at
least two.  This is independent of planarity/genus zero. -/
theorem face_cycle_ge_four_bipartiteDoubleCover
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (rotation : Equiv.Perm G.bipartiteDoubleCover.Dart)
    (hsource : ∀ d, (rotation d).fst = d.fst)
    (htrans : ∀ d d', d.fst = d'.fst →
      ∃ n : ℕ, (rotation : G.bipartiteDoubleCover.Dart →
        G.bipartiteDoubleCover.Dart)^[n] d = d')
    (hdegree : ∀ v, 2 ≤ G.bipartiteDoubleCover.degree v) :
    ∀ k ∈ (ribbonFacePerm G.bipartiteDoubleCover rotation).cycleType, 4 ≤ k := by
  let H := G.bipartiteDoubleCover
  let face := ribbonFacePerm H rotation
  have hface_source (d : H.Dart) : (face d).fst = d.snd := by
    change (rotation d.symm).fst = d.snd
    rw [hsource]
    rfl
  have hface_flip (d : H.Dart) :
      doubleCoverSide (face d).fst = !doubleCoverSide d.fst := by
    rw [hface_source]
    rcases d with ⟨⟨u, v⟩, hadj⟩
    cases u <;> cases v
    · exact False.elim hadj
    · rfl
    · rfl
    · exact False.elim hadj
  intro k hk
  have hk2 : 2 ≤ k := Equiv.Perm.two_le_of_mem_cycleType hk
  by_contra hk4
  have hk_cases : k = 2 ∨ k = 3 := by omega
  simp only [Equiv.Perm.cycleType_def, ← Finset.mem_def, Function.comp_apply,
    Multiset.mem_map, Equiv.Perm.mem_cycleFactorsFinset_iff] at hk
  obtain ⟨c, ⟨hcCycle, hcAction⟩, hkcard⟩ := hk
  obtain ⟨d, hd⟩ := Equiv.Perm.IsCycle.nonempty_support hcCycle
  have hcFactors : c ∈ face.cycleFactorsFinset :=
    Equiv.Perm.mem_cycleFactorsFinset_iff.mpr ⟨hcCycle, hcAction⟩
  have hcycleOf : c = face.cycleOf d :=
    Equiv.Perm.cycle_is_cycleOf hd hcFactors
  rcases hk_cases with rfl | rfl
  · have hcOrder : orderOf c = 2 := by
      rw [hcCycle.orderOf, hkcard]
    have hpow : (face ^ 2) d = d := by
      rw [← Equiv.Perm.cycleOf_pow_apply_self face d 2, ← hcycleOf,
        ← hcOrder, pow_orderOf_eq_one]
      rfl
    have hfaceface : face (face d) = d := by
      simpa [pow_two, mul_apply] using hpow
    have hface_eq_symm : face d = d.symm := by
      apply Dart.ext
      apply Prod.ext
      · exact hface_source d
      · have hs := hface_source (face d)
        rw [hfaceface] at hs
        exact hs.symm
    have hrotation_fixed : rotation d.symm = d.symm := by
      exact hface_eq_symm
    let w0 : H.neighborSet d.snd := ⟨d.fst, d.adj.symm⟩
    have hwcard : 1 < Fintype.card (H.neighborSet d.snd) := by
      rw [H.card_neighborSet_eq_degree]
      have hddegree : 2 ≤ H.degree d.snd := hdegree d.snd
      omega
    obtain ⟨w, hwne⟩ := Fintype.exists_ne_of_one_lt_card hwcard w0
    let q : H.Dart := H.dartOfNeighborSet d.snd w
    have hqne : q ≠ d.symm := by
      intro hq
      apply hwne
      apply Subtype.ext
      have hsnd := congrArg (fun z : H.Dart => z.snd) hq
      exact hsnd
    obtain ⟨n, hn⟩ := htrans d.symm q (by rfl)
    have hfixed := Function.iterate_fixed hrotation_fixed n
    rw [hfixed] at hn
    exact hqne hn.symm
  · have hcOrder : orderOf c = 3 := by
      rw [hcCycle.orderOf, hkcard]
    have hpow : (face ^ 3) d = d := by
      rw [← Equiv.Perm.cycleOf_pow_apply_self face d 3, ← hcycleOf,
        ← hcOrder, pow_orderOf_eq_one]
      rfl
    have hthree : face (face (face d)) = d := by
      simpa [pow_succ, mul_apply] using hpow
    have h1 := hface_flip d
    have h2 := hface_flip (face d)
    have h3 := hface_flip (face (face d))
    have hs := congrArg (fun z : H.Dart => doubleCoverSide z.fst) hthree
    cases hside : doubleCoverSide d.fst <;> simp_all

/-- A graph-specific certificate whose Euler equation is a consequence of the
inductive genus-zero construction, rather than a field of the certificate. -/
structure ConstructibleSphereRotationCertificate
    (G : SimpleGraph V) [DecidableRel G.Adj] where
  rotation : Equiv.Perm G.Dart
  rotation_source : ∀ d, (rotation d).fst = d.fst
  rotation_transitive : ∀ d d', d.fst = d'.fst →
    ∃ n : ℕ, (rotation : G.Dart → G.Dart)^[n] d = d'
  componentBoundaries : Multiset (Multiset ℕ)
  construction : SphereRibbonConstruction
    (Fintype.card V) G.edgeFinset.card componentBoundaries
  component_count : componentBoundaries.card =
    Fintype.card G.ConnectedComponent
  boundary_cycles : componentBoundaries.bind id =
    (ribbonFacePerm G rotation).cycleType
  face_cycle_ge_four : ∀ k ∈ (ribbonFacePerm G rotation).cycleType, 4 ≤ k

theorem ConstructibleSphereRotationCertificate.euler
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (C : ConstructibleSphereRotationCertificate G) :
    Fintype.card V + (ribbonFacePerm G C.rotation).cycleType.card =
    G.edgeFinset.card + 2 * Fintype.card G.ConnectedComponent := by
  have h := C.construction.euler
  have hbound : boundaryCount C.componentBoundaries =
      (ribbonFacePerm G C.rotation).cycleType.card := by
    simpa [boundaryCount, Multiset.card_bind] using
      congrArg Multiset.card C.boundary_cycles
  rw [hbound, C.component_count] at h
  exact h

theorem ConstructibleSphereRotationCertificate.edge_add_four_le_two_mul_vertex
    {G : SimpleGraph V} [DecidableRel G.Adj] [Nonempty V]
    (C : ConstructibleSphereRotationCertificate G) :
    G.edgeFinset.card + 4 ≤ 2 * Fintype.card V := by
  have hcomponents : C.componentBoundaries ≠ 0 := by
    intro hz
    have hzero : Fintype.card G.ConnectedComponent = 0 := by
      rw [← C.component_count, hz]
      simp
    exact Fintype.card_ne_zero hzero
  apply C.construction.edge_add_four_le_two_mul_vertices hcomponents
  intro p hp k hk
  apply C.face_cycle_ge_four k
  rw [← C.boundary_cycles]
  exact Multiset.mem_bind.mpr ⟨p, hp, hk⟩

theorem edge_add_two_le_two_mul_vertex_of_constructible_doubleCover_certificate
    {G : SimpleGraph V} [DecidableRel G.Adj] [Nonempty V]
    (C : ConstructibleSphereRotationCertificate G.bipartiteDoubleCover) :
    G.edgeFinset.card + 2 ≤ 2 * Fintype.card V := by
  have h := C.edge_add_four_le_two_mul_vertex
  rw [card_edgeFinset_bipartiteDoubleCover] at h
  simp only [Fintype.card_sum] at h
  omega

end SimpleGraph

