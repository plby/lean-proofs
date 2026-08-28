import Wikipedia.NoExoticSixSphere.CollaredSlabBoundaryTime
import Mathlib.Topology.Homotopy.Equiv

/-!
# The actual collar union retracts onto the endpoint fibers

The endpoint-time interpolation is lifted into the original regular
fiber and keeps both endpoints fixed. It gives an actual homotopy
equivalence whose forward map is the inclusion of the two endpoint
fibers into their collar neighborhood. For the checked slab atlas,
these endpoint fibers are precisely the manifold boundary.
-/

noncomputable section

open Set
open scoped unitInterval ContinuousMap

namespace NoExoticSixSphere.CylinderFiberSlab.BoundaryPush

variable {M N : Type*} [TopologicalSpace M] [TopologicalSpace N]
  (F : C(ℝ × M, N)) (z : N) (s t a b : ℝ)
  (hsa : s < a) (hab : a ≤ b) (hbt : b < t)
  (hleft : ∀ r ∈ Icc s a, ∀ x, F (r, x) = F (s, x))
  (hright : ∀ r ∈ Icc b t, ∀ x, F (r, x) = F (t, x))

def ends : Set (slab F z s t) := {p | p.val.val.1 = s ∨ p.val.val.1 = t}

include hsa hbt in
theorem ends_subset_domain : ends F z s t ⊆ domain F z s t a b := by
  intro p hp
  rcases hp with hs | ht
  · exact Or.inl (hs.trans_lt hsa)
  · exact Or.inr (hbt.trans_eq ht.symm)

def inclusion : C(ends F z s t, domain F z s t a b) where
  toFun p := ⟨p.val, ends_subset_domain F z s t a b hsa hbt p.property⟩
  continuous_toFun := continuous_subtype_val.subtype_mk _

def ambient : C(unitInterval × domain F z s t a b, ℝ × M) where
  toFun p := (timeHomotopy F z s t a b hab p, p.2.val.val.val.2)
  continuous_toFun := (timeHomotopy F z s t a b hab).continuous.prodMk
    (continuous_snd.comp (continuous_subtype_val.comp
      (continuous_subtype_val.comp (continuous_subtype_val.comp continuous_snd))))

def map : C(unitInterval × domain F z s t a b, domain F z s t a b) where
  toFun p := ⟨⟨⟨ambient F z s t a b hab p,
    timeHomotopy_preserves F z s t a b hab hsa hbt hleft hright p.2 p.1⟩,
    timeHomotopy_mem_interval F z s t a b hab hsa hbt p.2 p.1⟩,
    timeHomotopy_mem_collar F z s t a b hab hsa hbt p.2 p.1⟩
  continuous_toFun :=
    (((ambient F z s t a b hab).continuous.subtype_mk _).subtype_mk _).subtype_mk _

theorem map_zero (p : domain F z s t a b) :
    map F z s t a b hsa hab hbt hleft hright (0, p) = p := by
  apply Subtype.ext
  apply Subtype.ext
  apply Subtype.ext
  exact Prod.ext (timeHomotopy_zero F z s t a b hab p) rfl

theorem map_one_ends (p : domain F z s t a b) :
    (map F z s t a b hsa hab hbt hleft hright (1, p)).val ∈ ends F z s t := by
  change timeHomotopy F z s t a b hab (1, p) = s ∨
    timeHomotopy F z s t a b hab (1, p) = t
  rw [timeHomotopy_one]
  exact endpoint_eq_end F z s t a b hab p

theorem map_fixed (p : domain F z s t a b) (hp : p.val ∈ ends F z s t)
    (u : unitInterval) : map F z s t a b hsa hab hbt hleft hright (u, p) = p := by
  apply Subtype.ext
  apply Subtype.ext
  apply Subtype.ext
  exact Prod.ext (timeHomotopy_fixed F z s t a b hab hsa hbt p hp u) rfl

def retraction : C(domain F z s t a b, ends F z s t) where
  toFun p := ⟨(map F z s t a b hsa hab hbt hleft hright (1, p)).val,
    map_one_ends F z s t a b hsa hab hbt hleft hright p⟩
  continuous_toFun := (continuous_subtype_val.comp
    ((map F z s t a b hsa hab hbt hleft hright).continuous.comp
      (continuous_const.prodMk continuous_id))).subtype_mk _

theorem retraction_inclusion :
    (retraction F z s t a b hsa hab hbt hleft hright).comp
      (inclusion F z s t a b hsa hbt) = ContinuousMap.id (ends F z s t) := by
  apply ContinuousMap.ext
  intro p
  apply Subtype.ext
  exact congrArg (fun q : domain F z s t a b ↦ q.val)
    (map_fixed F z s t a b hsa hab hbt hleft hright
      (inclusion F z s t a b hsa hbt p) p.property 1)

def deformation : (ContinuousMap.id (domain F z s t a b)).Homotopy
    ((inclusion F z s t a b hsa hbt).comp
      (retraction F z s t a b hsa hab hbt hleft hright)) where
  toFun := map F z s t a b hsa hab hbt hleft hright
  continuous_toFun := (map F z s t a b hsa hab hbt hleft hright).continuous
  map_zero_left := map_zero F z s t a b hsa hab hbt hleft hright
  map_one_left _ := rfl

def homotopyEquiv : ends F z s t ≃ₕ domain F z s t a b where
  toFun := inclusion F z s t a b hsa hbt
  invFun := retraction F z s t a b hsa hab hbt hleft hright
  left_inv := by rw [retraction_inclusion]
  right_inv := ⟨(deformation F z s t a b hsa hab hbt hleft hright).symm⟩

theorem homotopyEquiv_toFun :
    (homotopyEquiv F z s t a b hsa hab hbt hleft hright).toFun =
      inclusion F z s t a b hsa hbt := rfl

end NoExoticSixSphere.CylinderFiberSlab.BoundaryPush
