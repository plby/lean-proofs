import ErdosProblems.Erdos577.JointBridgeTripleFactors
import ErdosProblems.Erdos577.StarRowBounds

/-! The four triple exclusions give the required independent-row bounds at both actual terminals. -/

namespace Erdos577.JointBridge

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

theorem arms_row_restrictions {c d : TriangleChain G} (hc : c.Feasible) (hd : d.Feasible)
    (p : Paw G) (hp : p.support = c.remainder) (u z1 z2 : V) (ht : d.terminal = u)
    {j : Finset V} (hj : j ∈ c.blocks) (hjd : j ∈ d.blocks)
    (hfour : (arms p u z1 z2).card = 4) (hdis : Disjoint (arms p u z1 z2) j)
    (hrj : p.center ∉ j) (hcenter : ∀ w ∈ arms p u z1 z2, G.Adj p.center w)
    (hno : ∀ w ∈ arms p u z1 z2,
      ¬LocalFactor G (insert p.center ((arms p u z1 z2).erase w) ∪ j))
    (hnine : 9 ≤ contacts G (arms p u z1 z2) j) :
    (∀ x ∈ arms p u z1 z2, ∀ y ∈ arms p u z1 z2, ∀ z ∈ arms p u z1 z2,
      x ≠ y → x ≠ z → y ≠ z → ¬CommonReplacement G x y z j) ∧
    (∀ z ∈ arms p u z1 z2, degreeIn G z j ≤ 3) ∧
      degreeIn G p.leaf j ≤ 2 ∧ degreeIn G u j ≤ 2 := by
  have htriples := fun t ht hthree ↦ triple_no_factor_of_erase hfour hno (s := t) ht hthree
  have hcommon := fun x hx y hy z hz hxy hxz hyz ↦ no_common_of_star_triples hdis hrj
    hcenter htriples (x := x) (y := y) (z := z) hx hy hz hxy hxz hyz
  have hquad := c.property.blocks_quad j hj
  have huniversal := fun z hz ↦ no_universal_of_nine_contacts hfour hquad.card hnine
    hcommon (z := z) hz
  have hx : degreeIn G p.leaf j ≤ 2 := by
    by_contra hlarge
    have hthree : 3 ≤ degreeIn G p.leaf j := by omega
    exact huniversal p.leaf (by simp [arms]) (fun _ hu ↦
      (hc.presentPaw_feasible p hp).terminal_universal_replace hj hthree hu)
  have hu : degreeIn G u j ≤ 2 := by
    by_contra hlarge
    apply huniversal u (by simp [arms])
    intro v hv
    have hh := hd.terminal_universal_replace hjd (by rw [ht]; omega) hv
    rwa [ht] at hh
  exact ⟨hcommon, row_le_three_of_nine_contacts hfour hquad hdis hnine hcommon, hx, hu⟩

end Erdos577.JointBridge
