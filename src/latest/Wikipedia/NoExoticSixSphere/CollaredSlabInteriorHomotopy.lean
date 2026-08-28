import Wikipedia.NoExoticSixSphere.CollaredIntervalPush
import Wikipedia.NoExoticSixSphere.SlabInterior
import Mathlib.Topology.Homotopy.Equiv

/-!
# The actual slab interior inclusion is a homotopy equivalence

For specified constant collars, the time push stays in the original
cylinder fiber. It moves the entire slab into its strict-time interior,
and the same homotopy preserves the interior throughout. The resulting
homotopy equivalence has the original subtype inclusion as its forward
map; it does not replace the slab by an unrelated equivalent space.
-/

noncomputable section

open Set
open scoped unitInterval ContinuousMap

namespace NoExoticSixSphere.CylinderFiberSlab.InteriorPush

variable {M N : Type*} [TopologicalSpace M] [TopologicalSpace N]
  (F : C(ℝ × M, N)) (z : N) (s t a b : ℝ)
  (hsa : s < a) (hab : a ≤ b) (hbt : b < t)
  (hleft : ∀ r ∈ Icc s a, ∀ x, F (r, x) = F (s, x))
  (hright : ∀ r ∈ Icc b t, ∀ x, F (r, x) = F (t, x))

def inclusion : C(interiorDomain F z s t, slab F z s t) :=
  ⟨Subtype.val, continuous_subtype_val⟩

def ambient : C(unitInterval × slab F z s t, ℝ × M) where
  toFun p := (CollaredIntervalPush.time a b hab (p.1, p.2.val.val.1), p.2.val.val.2)
  continuous_toFun := by
    have hp : Continuous (fun p : unitInterval × slab F z s t ↦ p.2.val.val) :=
      (continuous_subtype_val.comp continuous_subtype_val).comp continuous_snd
    exact ((CollaredIntervalPush.time a b hab).continuous.comp
      (continuous_fst.prodMk hp.fst)).prodMk hp.snd

def map : C(unitInterval × slab F z s t, slab F z s t) where
  toFun p := ⟨⟨ambient F z s t a b hab p,
    (CollaredIntervalPush.preserves a b hab F hleft hright p.2.property
      p.2.val.val.2 p.1).trans p.2.val.property⟩,
    CollaredIntervalPush.time_mem_Icc a b hab hsa.le hbt.le p.2.property p.1⟩
  continuous_toFun := ((ambient F z s t a b hab).continuous.subtype_mk _).subtype_mk _

theorem map_zero (p : slab F z s t) : map F z s t a b hsa hab hbt hleft hright (0, p) = p := by
  apply Subtype.ext
  apply Subtype.ext
  exact Prod.ext (CollaredIntervalPush.time_zero a b hab p.val.val.1) rfl

theorem map_interior (p : interiorDomain F z s t) (u : unitInterval) :
    map F z s t a b hsa hab hbt hleft hright (u, p.val) ∈ interiorDomain F z s t :=
  CollaredIntervalPush.time_mem_Ioo a b hab hsa hbt p.property u

theorem map_one_interior (p : slab F z s t) :
    map F z s t a b hsa hab hbt hleft hright (1, p) ∈ interiorDomain F z s t := by
  change CollaredIntervalPush.time a b hab (1, p.val.val.1) ∈ Ioo s t
  rw [CollaredIntervalPush.time_one]
  exact ⟨hsa.trans_le (projIcc a b hab p.val.val.1).property.1,
    (projIcc a b hab p.val.val.1).property.2.trans_lt hbt⟩

def push : C(slab F z s t, interiorDomain F z s t) where
  toFun p := ⟨map F z s t a b hsa hab hbt hleft hright (1, p),
    map_one_interior F z s t a b hsa hab hbt hleft hright p⟩
  continuous_toFun := ((map F z s t a b hsa hab hbt hleft hright).continuous.comp
    (continuous_const.prodMk continuous_id)).subtype_mk _

def deformation :
    (ContinuousMap.id (slab F z s t)).Homotopy
      ((inclusion F z s t).comp (push F z s t a b hsa hab hbt hleft hright)) where
  toFun := map F z s t a b hsa hab hbt hleft hright
  continuous_toFun := (map F z s t a b hsa hab hbt hleft hright).continuous
  map_zero_left := map_zero F z s t a b hsa hab hbt hleft hright
  map_one_left _ := rfl

def interiorDeformation :
    (ContinuousMap.id (interiorDomain F z s t)).Homotopy
      ((push F z s t a b hsa hab hbt hleft hright).comp (inclusion F z s t)) where
  toFun p := ⟨map F z s t a b hsa hab hbt hleft hright (p.1, p.2.val),
    map_interior F z s t a b hsa hab hbt hleft hright p.2 p.1⟩
  continuous_toFun := ((map F z s t a b hsa hab hbt hleft hright).continuous.comp
    (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd))).subtype_mk _
  map_zero_left p := Subtype.ext (map_zero F z s t a b hsa hab hbt hleft hright p.val)
  map_one_left _ := rfl

def homotopyEquiv : interiorDomain F z s t ≃ₕ slab F z s t where
  toFun := inclusion F z s t
  invFun := push F z s t a b hsa hab hbt hleft hright
  left_inv := ⟨(interiorDeformation F z s t a b hsa hab hbt hleft hright).symm⟩
  right_inv := ⟨(deformation F z s t a b hsa hab hbt hleft hright).symm⟩

theorem homotopyEquiv_toFun :
    (homotopyEquiv F z s t a b hsa hab hbt hleft hright).toFun = inclusion F z s t := rfl

theorem map_fixed (p : slab F z s t) (hp : p.val.val.1 ∈ Icc a b) (u : unitInterval) :
    map F z s t a b hsa hab hbt hleft hright (u, p) = p := by
  apply Subtype.ext
  apply Subtype.ext
  exact Prod.ext (CollaredIntervalPush.time_fixed a b hab u hp) rfl

end NoExoticSixSphere.CylinderFiberSlab.InteriorPush
