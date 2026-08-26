import ErdosProblems.Erdos73.TreeEdgeCuts
import ErdosProblems.Erdos73.PermutationCutCycles

/-! Splicing cyclic label fibres along the edges of a tree gives one contour cycle. -/

namespace Erdos73
noncomputable section
attribute [local instance] Classical.propDecidable Classical.decEq
open Equiv SimpleGraph

structure TreeSwitchSystem (D U : Type*) where
  label : D → U
  rotation : Perm D
  rotation_label : ∀ d, label (rotation d) = label d
  rotation_fiber : ∀ a b, label a = label b → rotation.SameCycle a b
  switch : Perm D
  switch_involutive : Function.Involutive switch
  tree : SimpleGraph U
  isTree : tree.IsTree
  switch_adj : ∀ d, switch d ≠ d → tree.Adj (label d) (label (switch d))
  edge_port : ∀ u v, tree.Adj u v → ∃ d, label d = u ∧ label (switch d) = v
  port_unique : ∀ d e, switch d ≠ d → label d = label e →
    label (switch d) = label (switch e) → d = e

namespace TreeSwitchSystem

variable {D U : Type*} [Finite D] (C : TreeSwitchSystem D U)

def contour : Perm D := C.rotation * C.switch

theorem contour_label (d : D) : C.label (C.contour d) = C.label (C.switch d) :=
  C.rotation_label _

theorem sameCycle_switch (a : D) : C.contour.SameCycle a (C.switch a) := by
  by_cases ha : C.switch a = a
  · exact ha.symm.sameCycle _
  let P : D → Prop := fun d => treeEdgeSide C.tree (C.label a) (C.label (C.switch a)) (C.label d)
  have hadj := C.switch_adj a ha
  apply sameCycle_switch_of_cut C.rotation C.switch a P
  · intro x
    dsimp only [P]
    rw [C.rotation_label]
  · exact treeEdgeSide_self _ _ _
  · exact treeEdgeSide_not_other _ C.isTree.isAcyclic hadj
  · intro x hx hSx
    have hne : C.switch x ≠ x := fun he => hx (he ▸ hSx)
    have he := treeEdgeSide_crossing C.tree C.isTree.isAcyclic hadj
      (C.switch_adj x hne).symm hSx hx
    have hax : C.switch (C.switch a) ≠ C.switch a := by
      rw [C.switch_involutive a]
      exact fun hh => ha hh.symm
    apply (C.port_unique (C.switch a) x hax he.2.symm ?_).symm
    rw [C.switch_involutive a]
    exact he.1.symm

theorem sameCycle_fiber {a b : D} (hab : C.label a = C.label b) :
    C.contour.SameCycle a b :=
  sameCycle_rotation_of_switch C.switch_involutive C.sameCycle_switch
    (C.rotation_fiber a b hab)

theorem sameCycle_of_walk {u v : U} (p : C.tree.Walk u v) :
    ∀ a b, C.label a = u → C.label b = v → C.contour.SameCycle a b := by
  induction p with
  | nil =>
    intro a b ha hb
    exact C.sameCycle_fiber (ha.trans hb.symm)
  | @cons u v w huv p ih =>
    intro a b ha hb
    obtain ⟨d, hd, hSd⟩ := C.edge_port u v huv
    exact (C.sameCycle_fiber (ha.trans hd.symm)).trans
      ((C.sameCycle_switch d).trans (ih (C.switch d) b hSd hb))

theorem sameCycle (a b : D) : C.contour.SameCycle a b := by
  obtain ⟨p⟩ := C.isTree.connected.preconnected (C.label a) (C.label b)
  exact C.sameCycle_of_walk p a b rfl rfl

theorem contour_isCycleOn : C.contour.IsCycleOn Set.univ := by
  refine ⟨?_, fun a _ b _ => C.sameCycle a b⟩
  exact ⟨fun _ _ => trivial, C.contour.injective.injOn,
    fun y _ => ⟨C.contour.symm y, trivial, C.contour.apply_symm_apply y⟩⟩

/-- A tree-edge cut has only the two selected ports as contour crossings. -/
theorem cut_crossing_ports {u v : U} (huv : C.tree.Adj u v) :
    ∃ a b : D, ∀ d,
      ¬(treeEdgeSide C.tree u v (C.label d) ↔
        treeEdgeSide C.tree u v (C.label (C.contour d))) → d = a ∨ d = b := by
  obtain ⟨a, ha, hSa⟩ := C.edge_port u v huv
  have hane : C.switch a ≠ a := by
    intro he
    exact huv.ne (ha.symm.trans ((congrArg C.label he).symm.trans hSa))
  refine ⟨a, C.switch a, ?_⟩
  intro d hd
  rw [C.contour_label] at hd
  have hdne : C.switch d ≠ d := by
    intro he
    exact hd (by rw [he])
  by_cases hside : treeEdgeSide C.tree u v (C.label d)
  · have hnside : ¬treeEdgeSide C.tree u v (C.label (C.switch d)) := by
      intro hh
      exact hd ⟨fun _ => hh, fun _ => hside⟩
    have hh := treeEdgeSide_crossing C.tree C.isTree.isAcyclic huv
      (C.switch_adj d hdne) hside hnside
    exact Or.inl (C.port_unique d a hdne (hh.1.trans ha.symm) (hh.2.trans hSa.symm))
  · have hother : treeEdgeSide C.tree u v (C.label (C.switch d)) := by
      by_contra hh
      exact hd ⟨fun hs => (hside hs).elim, fun hs => (hh hs).elim⟩
    have hh := treeEdgeSide_crossing C.tree C.isTree.isAcyclic huv
      (C.switch_adj d hdne).symm hother hside
    right
    apply C.port_unique d (C.switch a) hdne (hh.2.trans hSa.symm)
    rw [C.switch_involutive a]
    exact hh.1.trans ha.symm

end TreeSwitchSystem
end
end Erdos73
