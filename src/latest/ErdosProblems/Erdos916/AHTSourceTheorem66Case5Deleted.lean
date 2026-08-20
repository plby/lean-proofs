/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos916.AHTSourceLemma63
import ErdosProblems.Erdos916.AHTSourceLemma65
import ErdosProblems.Erdos916.AHTWatkinsMesner

/-!
# The singleton-separator claim on the centre-deleted graph

This file gives the type-correct form of AHT Theorem 6.6, claim (5).  The
Watkins--Mesner splitter belongs to `G - center`, not to the ambient graph
`G`: its vertices are the subtype `{w : V // w ≠ center}`.  The three edges
from `center` to the terminals, and the conclusion of AHT Lemma 6.3, remain
statements about the ambient graph.

Keeping the two graphs separate is essential.  If the splitter were placed
on `G` itself, component closure would force `center` into every terminal
component, contrary to the intended singleton description.
-/

namespace Erdos916

open SimpleGraph

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]
variable {center : V}
variable {x y z : {w : V // w ≠ center}}

/-- The source-exact local certificate for claim (5), with the
Watkins--Mesner splitter living on the graph obtained by deleting `center`.

The terminal and attachment vertices are therefore subtype vertices.  The
three displayed centre edges and the not-close hypothesis are deliberately
kept in the ambient graph. -/
structure AHTClaim5DeletedSplitter
    (G : SimpleGraph V) [DecidableRel G.Adj] (center : V)
    (x y z : {w : V // w ≠ center}) where
  splitter : WatkinsMesnerSplitter (deleteVertex G center) x y z
  xPart_eq : splitter.xPart = {x}
  yPart_eq : splitter.yPart = {y}
  zPart_eq : splitter.zPart = {z}
  center_adj_x : G.Adj center x.1
  center_adj_y : G.Adj center y.1
  center_adj_z : G.Adj center z.1
  center_not_close : ¬IsCloseToAHTTwin G center

namespace AHTClaim5DeletedSplitter

variable (C : AHTClaim5DeletedSplitter G center x y z)

include C in
theorem x_ne_y : x.1 ≠ y.1 := by
  intro hxy
  have hxy' : x = y := Subtype.ext hxy
  have hxX : x ∈ C.splitter.xPart := C.splitter.x_mem_X
  have hxY : x ∈ C.splitter.yPart := by
    simpa [hxy'] using C.splitter.y_mem_Y
  exact Finset.disjoint_left.mp C.splitter.X_disjoint_Y hxX hxY

include C in
theorem x_ne_z : x.1 ≠ z.1 := by
  intro hxz
  have hxz' : x = z := Subtype.ext hxz
  have hxX : x ∈ C.splitter.xPart := C.splitter.x_mem_X
  have hxZ : x ∈ C.splitter.zPart := by
    simpa [hxz'] using C.splitter.z_mem_Z
  exact Finset.disjoint_left.mp C.splitter.X_disjoint_Z hxX hxZ

include C in
theorem y_ne_z : y.1 ≠ z.1 := by
  intro hyz
  have hyz' : y = z := Subtype.ext hyz
  have hyY : y ∈ C.splitter.yPart := C.splitter.y_mem_Y
  have hyZ : y ∈ C.splitter.zPart := by
    simpa [hyz'] using C.splitter.z_mem_Z
  exact Finset.disjoint_left.mp C.splitter.Y_disjoint_Z hyY hyZ

/-- A splitter attachment is automatically different from the deleted
ambient centre, by its subtype proof. -/
theorem center_ne_xA : center ≠ C.splitter.xA.1 :=
  C.splitter.xA.2.symm

theorem center_ne_xB : center ≠ C.splitter.xB.1 :=
  C.splitter.xB.2.symm

/-- The unique `A`-attachment edge of the singleton `X`-component, mapped
from the induced graph back to the ambient graph. -/
theorem adj_x_xA : G.Adj x.1 C.splitter.xA.1 := by
  obtain ⟨w, hw, hwa⟩ := C.splitter.X_A_attachment.2.1
  have hwx : w = x := by simpa [C.xPart_eq] using hw
  simpa [hwx] using hwa

theorem adj_y_yA : G.Adj y.1 C.splitter.yA.1 := by
  obtain ⟨w, hw, hwa⟩ := C.splitter.Y_A_attachment.2.1
  have hwy : w = y := by simpa [C.yPart_eq] using hw
  simpa [hwy] using hwa

theorem adj_z_zA : G.Adj z.1 C.splitter.zA.1 := by
  obtain ⟨w, hw, hwa⟩ := C.splitter.Z_A_attachment.2.1
  have hwz : w = z := by simpa [C.zPart_eq] using hw
  simpa [hwz] using hwa

theorem adj_x_xB : G.Adj x.1 C.splitter.xB.1 := by
  obtain ⟨w, hw, hwb⟩ := C.splitter.X_B_attachment.2.1
  have hwx : w = x := by simpa [C.xPart_eq] using hw
  simpa [hwx] using hwb

theorem adj_y_yB : G.Adj y.1 C.splitter.yB.1 := by
  obtain ⟨w, hw, hwb⟩ := C.splitter.Y_B_attachment.2.1
  have hwy : w = y := by simpa [C.yPart_eq] using hw
  simpa [hwy] using hwb

theorem adj_z_zB : G.Adj z.1 C.splitter.zB.1 := by
  obtain ⟨w, hw, hwb⟩ := C.splitter.Z_B_attachment.2.1
  have hwz : w = z := by simpa [C.zPart_eq] using hw
  simpa [hwz] using hwb

private theorem eq_of_mem_of_card_eq_one
    {W : Type*} [DecidableEq W] {S : Finset W} {p q : W}
    (hp : p ∈ S) (hq : q ∈ S) (hcard : S.card = 1) : p = q := by
  obtain ⟨w, hS⟩ := Finset.card_eq_one.mp hcard
  have hpw : p = w := by simpa [hS] using hp
  have hqw : q = w := by simpa [hS] using hq
  exact hpw.trans hqw.symm

theorem attachmentsA_eq_of_card_eq_one
    (hcard : C.splitter.aSet.card = 1) :
    C.splitter.xA = C.splitter.yA ∧
      C.splitter.xA = C.splitter.zA := by
  constructor
  · exact eq_of_mem_of_card_eq_one C.splitter.X_A_attachment.1
      C.splitter.Y_A_attachment.1 hcard
  · exact eq_of_mem_of_card_eq_one C.splitter.X_A_attachment.1
      C.splitter.Z_A_attachment.1 hcard

theorem attachmentsB_eq_of_card_eq_one
    (hcard : C.splitter.bSet.card = 1) :
    C.splitter.xB = C.splitter.yB ∧
      C.splitter.xB = C.splitter.zB := by
  constructor
  · exact eq_of_mem_of_card_eq_one C.splitter.X_B_attachment.1
      C.splitter.Y_B_attachment.1 hcard
  · exact eq_of_mem_of_card_eq_one C.splitter.X_B_attachment.1
      C.splitter.Z_B_attachment.1 hcard

end AHTClaim5DeletedSplitter

/-- **AHT Theorem 6.6, claim (5), on the centre-deleted graph.**

If the three terminal components of the Watkins--Mesner splitter of
`G - center` are singletons, both splitter sides have cardinality three.
For a singleton side, its three attachments coincide.  Their ambient image
and `center` then have the three distinct common neighbours `x,y,z`, so AHT
Lemma 6.3 makes `center` a member of a degree-three false-twin pair,
contradicting its source choice. -/
theorem aht_theorem66_claim5_of_deletedSplitter
    (hthree : IsThreeConnected G) (halmost : AlmostWheelFree G)
    (C : AHTClaim5DeletedSplitter G center x y z) :
    C.splitter.aSet.card = 3 ∧ C.splitter.bSet.card = 3 := by
  constructor
  · rcases C.splitter.A_card with hcard | hcard
    · obtain ⟨hxyA, hxzA⟩ := C.attachmentsA_eq_of_card_eq_one hcard
      have hrigid :
          AreFalseTwins G center C.splitter.xA.1 ∧
            G.degree center = 3 :=
        aht_twinPair_of_three_common_neighbors hthree halmost
          C.center_ne_xA C.x_ne_y C.x_ne_z C.y_ne_z
          C.center_adj_x C.center_adj_y C.center_adj_z
          C.adj_x_xA.symm
          (by simpa [hxyA] using C.adj_y_yA.symm)
          (by simpa [hxzA] using C.adj_z_zA.symm)
      have htwin : AHTTwinPair G center C.splitter.xA.1 :=
        ⟨hrigid.1, hrigid.2⟩
      exact False.elim (C.center_not_close htwin.close_left)
    · exact hcard
  · rcases C.splitter.B_card with hcard | hcard
    · obtain ⟨hxyB, hxzB⟩ := C.attachmentsB_eq_of_card_eq_one hcard
      have hrigid :
          AreFalseTwins G center C.splitter.xB.1 ∧
            G.degree center = 3 :=
        aht_twinPair_of_three_common_neighbors hthree halmost
          C.center_ne_xB C.x_ne_y C.x_ne_z C.y_ne_z
          C.center_adj_x C.center_adj_y C.center_adj_z
          C.adj_x_xB.symm
          (by simpa [hxyB] using C.adj_y_yB.symm)
          (by simpa [hxzB] using C.adj_z_zB.symm)
      have htwin : AHTTwinPair G center C.splitter.xB.1 :=
        ⟨hrigid.1, hrigid.2⟩
      exact False.elim (C.center_not_close htwin.close_left)
    · exact hcard

end Erdos916
