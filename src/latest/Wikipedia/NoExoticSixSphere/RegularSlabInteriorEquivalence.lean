import Wikipedia.NoExoticSixSphere.CollaredSlabInteriorHomotopy
import Wikipedia.NoExoticSixSphere.RegularCollaredCylinder
import Wikipedia.NoExoticSixSphere.ModHomologyHomotopyEquiv
import Mathlib.Tactic.Linarith

/-!
# Interior equivalence for the original regular collared filling slabs

The given open constant-end neighborhoods supply two smaller closed
collars. The constructed push therefore gives a homotopy equivalence
whose forward map is precisely the original interior inclusion. Its
action on every finite-coefficient homology group is the original
inclusion map, now proved bijective.
-/

noncomputable section

open Set Topology TopologicalSpace
open scoped Manifold ContDiff ContinuousMap

namespace NoExoticSixSphere.RegularCollaredCylinder

variable {B H M C H' N : Type}
  [NormedAddCommGroup B] [NormedSpace ℝ B] [TopologicalSpace H]
  {I : ModelWithCorners ℝ B H} [TopologicalSpace M] [ChartedSpace H M]
  [NormedAddCommGroup C] [NormedSpace ℝ C] [TopologicalSpace H']
  {J : ModelWithCorners ℝ C H'} [TopologicalSpace N] [ChartedSpace H' N]
  {z : N} {s t : ℝ} (d : RegularCollaredCylinder (M := M) I J z s t)

theorem exists_inner_times : ∃ a b : ℝ, s < a ∧ a ≤ b ∧ b < t ∧
    Icc s a ⊆ d.leftTimes ∧ Icc b t ⊆ d.rightTimes := by
  obtain ⟨l₀, u₀, hs, hL⟩ := mem_nhds_iff_exists_Ioo_subset.mp
    (d.leftTimes.isOpen.mem_nhds d.left_mem)
  obtain ⟨l₁, u₁, ht, hR⟩ := mem_nhds_iff_exists_Ioo_subset.mp
    (d.rightTimes.isOpen.mem_nhds d.right_mem)
  let δ := min ((t - s) / 4) (min ((u₀ - s) / 2) ((t - l₁) / 2))
  have hδ : 0 < δ := lt_min (by linarith [d.time_lt])
    (lt_min (by linarith [hs.2]) (by linarith [ht.1]))
  have hδ₀ : δ ≤ (t - s) / 4 := min_le_left _ _
  have hδL : δ ≤ (u₀ - s) / 2 := (min_le_right _ _).trans (min_le_left _ _)
  have hδR : δ ≤ (t - l₁) / 2 := (min_le_right _ _).trans (min_le_right _ _)
  refine ⟨s + δ, t - δ, by linarith, by linarith [d.time_lt], by linarith, ?_, ?_⟩
  · intro r hr
    exact hL ⟨hs.1.trans_le hr.1, by linarith [hr.2, hs.2]⟩
  · intro r hr
    exact hR ⟨by linarith [hr.1, ht.1], hr.2.trans_lt ht.2⟩

def interiorHomotopyEquiv :
    CylinderFiberSlab.interiorDomain d.map z s t ≃ₕ CylinderFiberSlab.slab d.map z s t :=
  let a := d.exists_inner_times.choose
  let b := d.exists_inner_times.choose_spec.choose
  let h := d.exists_inner_times.choose_spec.choose_spec
  CylinderFiberSlab.InteriorPush.homotopyEquiv d.map z s t a b h.1 h.2.1 h.2.2.1
    (fun r hr x ↦ (d.left_eq r (h.2.2.2.1 hr) x).trans (d.left_eq s d.left_mem x).symm)
    (fun r hr x ↦ (d.right_eq r (h.2.2.2.2 hr) x).trans (d.right_eq t d.right_mem x).symm)

theorem interiorHomotopyEquiv_toFun :
    d.interiorHomotopyEquiv.toFun = CylinderFiberSlab.InteriorPush.inclusion d.map z s t := rfl

open Wikipedia.HopfProblem.SphereHomologyCoefficients

def interiorModHomologyEquiv (p n : ℕ) :
    ModHomology p (CylinderFiberSlab.interiorDomain d.map z s t) n ≃ₗ[ℤ]
      ModHomology p (CylinderFiberSlab.slab d.map z s t) n :=
  modHomologyHomotopyEquiv p d.interiorHomotopyEquiv n

theorem interiorModHomologyEquiv_toLinearMap (p n : ℕ) :
    (d.interiorModHomologyEquiv p n).toLinearMap =
      modHomologyMap p (CylinderFiberSlab.InteriorPush.inclusion d.map z s t) n := rfl

theorem modHomologyMap_interior_bijective (p n : ℕ) :
    Function.Bijective
      (modHomologyMap p (CylinderFiberSlab.InteriorPush.inclusion d.map z s t) n) :=
  (d.interiorModHomologyEquiv p n).bijective

end NoExoticSixSphere.RegularCollaredCylinder
