import Wikipedia.NoExoticSixSphere.OpenSubsetSmoothMaps

/-!
# Comparing smooth structures on overlapping open sets

The overlap map sends a point to the same ambient point in the other open
set. If both overlap maps are smooth for the two supplied atlases, the
ambient identity on the overlap is a genuine partial diffeomorphism.
-/

open scoped Manifold ContDiff
open Set TopologicalSpace

namespace NoExoticSixSphere.OpenOverlap

variable {X : Type*} [TopologicalSpace X] (U V : Opens X)

def domain : Opens U := ⟨Subtype.val ⁻¹' V, V.isOpen.preimage continuous_subtype_val⟩

def map (x : domain U V) : V := ⟨x.val.val, x.property⟩

noncomputable def homeomorph (hU : Nonempty U) (hV : Nonempty V) :
    OpenPartialHomeomorph U V :=
  (U.openPartialHomeomorphSubtypeCoe hU).trans (V.openPartialHomeomorphSubtypeCoe hV).symm

theorem homeomorph_source (hU : Nonempty U) (hV : Nonempty V) :
    (homeomorph U V hU hV).source = (domain U V : Set U) := by
  simp only [homeomorph, OpenPartialHomeomorph.trans_source,
    Opens.openPartialHomeomorphSubtypeCoe_source, OpenPartialHomeomorph.symm_source,
    Opens.openPartialHomeomorphSubtypeCoe_target, univ_inter]
  rfl

theorem homeomorph_apply_val (hU : Nonempty U) (hV : Nonempty V)
    (x : U) (hx : x ∈ domain U V) : (homeomorph U V hU hV x).val = x.val := by
  exact (V.openPartialHomeomorphSubtypeCoe hV).right_inv (by
    rwa [Opens.openPartialHomeomorphSubtypeCoe_target])

variable {B H : Type*} [NormedAddCommGroup B] [NormedSpace ℝ B] [TopologicalSpace H]
  {I : ModelWithCorners ℝ B H} [ChartedSpace H U] [ChartedSpace H V]

theorem contMDiffOn_homeomorph (hU : Nonempty U) (hV : Nonempty V)
    (h : ContMDiff I I ∞ (map U V)) :
    ContMDiffOn I I ∞ (homeomorph U V hU hV) (homeomorph U V hU hV).source := by
  rw [homeomorph_source]
  apply (contMDiffOn_iff_openSubset (domain U V) _).mpr
  have heq : (fun x : domain U V ↦ homeomorph U V hU hV x.val) = map U V := by
    funext x
    exact Subtype.ext (homeomorph_apply_val U V hU hV x.val x.property)
  rw [heq]
  exact h

noncomputable def partialDiffeomorph (hU : Nonempty U) (hV : Nonempty V)
    (hUV : ContMDiff I I ∞ (map U V)) (hVU : ContMDiff I I ∞ (map V U)) :
    PartialDiffeomorph I I U V ∞ where
  toPartialEquiv := (homeomorph U V hU hV).toPartialEquiv
  open_source := (homeomorph U V hU hV).open_source
  open_target := (homeomorph U V hU hV).open_target
  contMDiffOn_toFun := contMDiffOn_homeomorph U V hU hV hUV
  contMDiffOn_invFun := by
    change ContMDiffOn I I ∞ (homeomorph V U hV hU) (homeomorph V U hV hU).source
    exact contMDiffOn_homeomorph V U hV hU hVU

end NoExoticSixSphere.OpenOverlap
