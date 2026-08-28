import Wikipedia.HopfProblem.SecondHurewiczSimplyConnectedPrism

/-!
# Literal cylinder maps and concatenation of actual homotopies

A continuous map on a cylinder is an actual homotopy between its endpoint
slices, without changing its underlying map. Native concatenation commutes
with spatial restriction, preserves constant cylinders, and depends only
on the two underlying cylinder maps, independently of endpoint proofs.
-/

noncomputable section

open scoped unitInterval Topology

namespace Wikipedia.HopfProblem.ThirdHurewicz

open SecondHurewicz.SimplyConnected

variable {A B X : Type} [TopologicalSpace A] [TopologicalSpace B] [TopologicalSpace X]

/-- A cylinder map, with its actual time-zero and time-one slices as endpoints. -/
def cylinderHomotopy (H : C(I × A, X)) :
    ContinuousMap.Homotopy (timeSlice H 0) (timeSlice H 1) where
  toContinuousMap := H
  map_zero_left _ := rfl
  map_one_left _ := rfl

@[simp] theorem cylinderHomotopy_toContinuousMap (H : C(I × A, X)) :
    (cylinderHomotopy H).toContinuousMap = H := rfl

@[simp] theorem cylinderHomotopy_apply (H : C(I × A, X)) (z : I × A) :
    cylinderHomotopy H z = H z := rfl

/-- Spatial restriction commutes with the actual native concatenation of homotopies. -/
theorem homotopyTrans_compContinuousMap {f₀ f₁ f₂ : C(A, X)}
    (F : f₀.Homotopy f₁) (G : f₁.Homotopy f₂) (f : C(B, A)) :
    (F.trans G).toContinuousMap.comp ((ContinuousMap.id I).prodMap f) =
      ((F.compContinuousMap f).trans (G.compContinuousMap f)).toContinuousMap := by
  ext z
  change (F.trans G) (z.1, f z.2) =
    ((F.compContinuousMap f).trans (G.compContinuousMap f)) z
  simp only [ContinuousMap.Homotopy.trans_apply]
  split_ifs <;> rfl

/-- Concatenation of two literally constant cylinders is literally constant. -/
theorem homotopyTrans_const {f₀ f₁ f₂ : C(A, X)}
    (F : f₀.Homotopy f₁) (G : f₁.Homotopy f₂) (x : X)
    (hF : F.toContinuousMap = ContinuousMap.const (I × A) x)
    (hG : G.toContinuousMap = ContinuousMap.const (I × A) x) :
    (F.trans G).toContinuousMap = ContinuousMap.const (I × A) x := by
  ext z
  change (F.trans G) z = x
  rw [ContinuousMap.Homotopy.trans_apply]
  split_ifs
  · exact ContinuousMap.congr_fun hF _
  · exact ContinuousMap.congr_fun hG _

/-- The underlying concatenated cylinder is independent of endpoint presentations. -/
theorem homotopyTrans_congr {f₀ f₁ f₂ g₀ g₁ g₂ : C(A, X)}
    (F : f₀.Homotopy f₁) (G : f₁.Homotopy f₂)
    (F' : g₀.Homotopy g₁) (G' : g₁.Homotopy g₂)
    (hF : F.toContinuousMap = F'.toContinuousMap)
    (hG : G.toContinuousMap = G'.toContinuousMap) :
    (F.trans G).toContinuousMap = (F'.trans G').toContinuousMap := by
  ext z
  change (F.trans G) z = (F'.trans G') z
  simp only [ContinuousMap.Homotopy.trans_apply]
  split_ifs
  · exact ContinuousMap.congr_fun hF _
  · exact ContinuousMap.congr_fun hG _

end Wikipedia.HopfProblem.ThirdHurewicz
