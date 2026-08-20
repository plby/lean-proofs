/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos916.AHTSourceLemma63
import ErdosProblems.Erdos916.AHTSourceLemma65
import ErdosProblems.Erdos916.AHTWatkinsMesner

/-!
# The singleton-separator claim in AHT Theorem 6.6

This file formalizes claim (5) in the proof of Theorem 6.6 of
Aboulker--Havet--Trotignon.  In the case where the three Watkins--Mesner
terminal components are singletons, neither of the two splitter sets can
be a singleton: otherwise its three named attachments coincide, and that
attachment and the deleted vertex have the three terminals as common
neighbours.  AHT Lemma 6.3 makes them twins, contrary to the choice of the
deleted vertex.
-/

namespace Erdos916

open SimpleGraph

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]
variable {center x y z : V}

/-- The concrete local certificate used in AHT Theorem 6.6, claim (5).

The splitter is for the three neighbours `x,y,z` of the deleted vertex
`center`.  Its displayed terminal components are exactly the three
singletons.  The last two fields record the source choice of `center`: it
is outside the splitter and is not close to a twin. -/
structure AHTClaim5SingletonSplitter
    (G : SimpleGraph V) [DecidableRel G.Adj] (center x y z : V) where
  splitter : WatkinsMesnerSplitter G x y z
  xPart_eq : splitter.xPart = {x}
  yPart_eq : splitter.yPart = {y}
  zPart_eq : splitter.zPart = {z}
  center_adj_x : G.Adj center x
  center_adj_y : G.Adj center y
  center_adj_z : G.Adj center z
  center_not_mem_A : center ∉ splitter.aSet
  center_not_mem_B : center ∉ splitter.bSet
  center_not_close : ¬IsCloseToAHTTwin G center

namespace AHTClaim5SingletonSplitter

variable (C : AHTClaim5SingletonSplitter G center x y z)

include C in
theorem x_ne_y : x ≠ y := by
  intro h
  have hxX : x ∈ C.splitter.xPart := C.splitter.x_mem_X
  have hxY : x ∈ C.splitter.yPart := by simpa [h] using C.splitter.y_mem_Y
  exact Finset.disjoint_left.mp C.splitter.X_disjoint_Y hxX hxY

include C in
theorem x_ne_z : x ≠ z := by
  intro h
  have hxX : x ∈ C.splitter.xPart := C.splitter.x_mem_X
  have hxZ : x ∈ C.splitter.zPart := by simpa [h] using C.splitter.z_mem_Z
  exact Finset.disjoint_left.mp C.splitter.X_disjoint_Z hxX hxZ

include C in
theorem y_ne_z : y ≠ z := by
  intro h
  have hyY : y ∈ C.splitter.yPart := C.splitter.y_mem_Y
  have hyZ : y ∈ C.splitter.zPart := by simpa [h] using C.splitter.z_mem_Z
  exact Finset.disjoint_left.mp C.splitter.Y_disjoint_Z hyY hyZ

theorem center_ne_xA : center ≠ C.splitter.xA := by
  intro h
  have hmem := congrArg (fun w : V ↦ w ∈ C.splitter.aSet) h
  apply C.center_not_mem_A
  exact hmem.mpr C.splitter.X_A_attachment.1

theorem center_ne_xB : center ≠ C.splitter.xB := by
  intro h
  have hmem := congrArg (fun w : V ↦ w ∈ C.splitter.bSet) h
  apply C.center_not_mem_B
  exact hmem.mpr C.splitter.X_B_attachment.1

theorem adj_x_xA : G.Adj x C.splitter.xA := by
  obtain ⟨w, hw, hwa⟩ := C.splitter.X_A_attachment.2.1
  have hwx : w = x := by simpa [C.xPart_eq] using hw
  simpa [hwx] using hwa

theorem adj_y_yA : G.Adj y C.splitter.yA := by
  obtain ⟨w, hw, hwa⟩ := C.splitter.Y_A_attachment.2.1
  have hwy : w = y := by simpa [C.yPart_eq] using hw
  simpa [hwy] using hwa

theorem adj_z_zA : G.Adj z C.splitter.zA := by
  obtain ⟨w, hw, hwa⟩ := C.splitter.Z_A_attachment.2.1
  have hwz : w = z := by simpa [C.zPart_eq] using hw
  simpa [hwz] using hwa

theorem adj_x_xB : G.Adj x C.splitter.xB := by
  obtain ⟨w, hw, hwb⟩ := C.splitter.X_B_attachment.2.1
  have hwx : w = x := by simpa [C.xPart_eq] using hw
  simpa [hwx] using hwb

theorem adj_y_yB : G.Adj y C.splitter.yB := by
  obtain ⟨w, hw, hwb⟩ := C.splitter.Y_B_attachment.2.1
  have hwy : w = y := by simpa [C.yPart_eq] using hw
  simpa [hwy] using hwb

theorem adj_z_zB : G.Adj z C.splitter.zB := by
  obtain ⟨w, hw, hwb⟩ := C.splitter.Z_B_attachment.2.1
  have hwz : w = z := by simpa [C.zPart_eq] using hw
  simpa [hwz] using hwb

private theorem eq_of_mem_of_card_eq_one
    {S : Finset V} {p q : V} (hp : p ∈ S) (hq : q ∈ S)
    (hcard : S.card = 1) : p = q := by
  obtain ⟨w, hS⟩ := Finset.card_eq_one.mp hcard
  have hpw : p = w := by simpa [hS] using hp
  have hqw : q = w := by simpa [hS] using hq
  exact hpw.trans hqw.symm

theorem attachmentsA_eq_of_card_eq_one
    (hcard : C.splitter.aSet.card = 1) :
    C.splitter.xA = C.splitter.yA ∧ C.splitter.xA = C.splitter.zA := by
  constructor
  · exact eq_of_mem_of_card_eq_one C.splitter.X_A_attachment.1
      C.splitter.Y_A_attachment.1 hcard
  · exact eq_of_mem_of_card_eq_one C.splitter.X_A_attachment.1
      C.splitter.Z_A_attachment.1 hcard

theorem attachmentsB_eq_of_card_eq_one
    (hcard : C.splitter.bSet.card = 1) :
    C.splitter.xB = C.splitter.yB ∧ C.splitter.xB = C.splitter.zB := by
  constructor
  · exact eq_of_mem_of_card_eq_one C.splitter.X_B_attachment.1
      C.splitter.Y_B_attachment.1 hcard
  · exact eq_of_mem_of_card_eq_one C.splitter.X_B_attachment.1
      C.splitter.Z_B_attachment.1 hcard

end AHTClaim5SingletonSplitter

/-- **AHT Theorem 6.6, claim (5), singleton-component case.**

For a Watkins--Mesner splitter whose three displayed components are the
singletons containing the three neighbours `x,y,z` of `center`, both
splitter sets have cardinality three.  Indeed, if (say) `aSet` had
cardinality one, its three named attachments would coincide.  That common
attachment and `center` would then have the three distinct common neighbours
`x,y,z`; AHT Lemma 6.3 says that they are twins, contradicting that `center`
was chosen not close to a twin.  The argument for `bSet` is symmetric. -/
theorem aht_theorem66_claim5_of_singleton_splitter
    (hthree : IsThreeConnected G) (halmost : AlmostWheelFree G)
    (C : AHTClaim5SingletonSplitter G center x y z) :
    C.splitter.aSet.card = 3 ∧ C.splitter.bSet.card = 3 := by
  constructor
  · rcases C.splitter.A_card with hcard | hcard
    · obtain ⟨hxyA, hxzA⟩ := C.attachmentsA_eq_of_card_eq_one hcard
      have hrigid :
          AreFalseTwins G center C.splitter.xA ∧ G.degree center = 3 :=
        aht_twinPair_of_three_common_neighbors hthree halmost
          C.center_ne_xA C.x_ne_y C.x_ne_z C.y_ne_z
          C.center_adj_x C.center_adj_y C.center_adj_z
          C.adj_x_xA.symm
          (by simpa [hxyA] using C.adj_y_yA.symm)
          (by simpa [hxzA] using C.adj_z_zA.symm)
      have htwin : AHTTwinPair G center C.splitter.xA :=
        ⟨hrigid.1, hrigid.2⟩
      exact False.elim (C.center_not_close htwin.close_left)
    · exact hcard
  · rcases C.splitter.B_card with hcard | hcard
    · obtain ⟨hxyB, hxzB⟩ := C.attachmentsB_eq_of_card_eq_one hcard
      have hrigid :
          AreFalseTwins G center C.splitter.xB ∧ G.degree center = 3 :=
        aht_twinPair_of_three_common_neighbors hthree halmost
          C.center_ne_xB C.x_ne_y C.x_ne_z C.y_ne_z
          C.center_adj_x C.center_adj_y C.center_adj_z
          C.adj_x_xB.symm
          (by simpa [hxyB] using C.adj_y_yB.symm)
          (by simpa [hxzB] using C.adj_z_zB.symm)
      have htwin : AHTTwinPair G center C.splitter.xB :=
        ⟨hrigid.1, hrigid.2⟩
      exact False.elim (C.center_not_close htwin.close_left)
    · exact hcard

end Erdos916
