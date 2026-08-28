import Wikipedia.NoExoticSixSphere.EndingPathSpace
import Wikipedia.NoExoticSixSphere.HomotopyFiberDeformationRetract
import Wikipedia.NoExoticSixSphere.HomotopyFiberProjectionThree
import Wikipedia.NoExoticSixSphere.ContractibleNativeHomotopy

/-!
# Native homotopy maps of actual strong deformation retractions

The fiber of the identity is the original contractible ending-path space.
The checked deformation-retract transport therefore contracts every
actual fiber of the retraction. Its genuine fiber sequence proves that
the original retraction map induces bijections at every basepoint.
-/

noncomputable section

open scoped Topology
open Wikipedia.HopfProblem.OrbitPair

namespace NoExoticSixSphere.DeformationRetractionNativeHomotopy

open HomotopyFiber

variable {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]

def identityFiberHomeomorph (b : Y) : Space (ContinuousMap.id Y) b ≃ₜ EndingPath.Space b where
  toFun p := ⟨p.val.2, p.property.2⟩
  invFun p := ⟨(p.val 0, p.val), rfl, p.property⟩
  left_inv p := Subtype.ext (Prod.ext p.property.1 rfl)
  right_inv _ := rfl
  continuous_toFun := (continuous_snd.comp continuous_subtype_val).subtype_mk _
  continuous_invFun :=
    (((continuous_eval_const 0).comp continuous_subtype_val).prodMk
      continuous_subtype_val).subtype_mk _

variable (r : C(X, Y)) (i : C(Y, X)) (hri : ∀ y, r (i y) = y)
  (H : (ContinuousMap.id X).HomotopyRel (i.comp r) (Set.range i))

include hri H in
theorem fiber_contractible (b : Y) : ContractibleSpace (Space r b) := by
  have hc : r.comp i = ContinuousMap.id Y := ContinuousMap.ext hri
  let : ContractibleSpace (Space (r.comp i) b) := by
    rw [hc]
    exact (identityFiberHomeomorph b).contractibleSpace
  let e := HomotopyFiberDeformationRetract.equivalence r b i r (hri := hri) (H := H)
  exact e.symm.contractibleSpace

include hri H in
theorem map_bijective (d : ℕ) (hd : 0 < d) (x : X) :
    Function.Bijective (HigherHomotopy.map (N := Fin d) r (y := x) rfl) := by
  let : NeZero d := ⟨by omega⟩
  let : ContractibleSpace (Space r (r x)) := fiber_contractible r i hri H (r x)
  let : Subsingleton (π_ d (Space r (r x)) (basepoint r x)) :=
    ContractibleNativeHomotopy.subsingleton d _
  refine ⟨HomotopyFiberConnectivity.map_injective_of_fiber_subsingleton d r x, ?_⟩
  cases d with
  | zero => omega
  | succ k =>
    let : Subsingleton (π_ k (Space r (r x)) (basepoint r x)) :=
      ContractibleNativeHomotopy.subsingleton k _
    exact HomotopyFiberConnectivity.map_surjective_of_fiber_subsingleton k r x

end NoExoticSixSphere.DeformationRetractionNativeHomotopy
