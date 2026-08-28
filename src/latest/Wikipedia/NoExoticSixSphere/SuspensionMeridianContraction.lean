import Wikipedia.NoExoticSixSphere.SuspensionMeridian
import Wikipedia.NoExoticSixSphere.SphereConvexContraction
import Wikipedia.NoExoticSixSphere.OpenHomotopyExtension
import Mathlib.Topology.UrysohnsLemma

/-!
# A constructed whole-sphere homotopy contracts the actual meridian

The normalized convex contraction preserves the meridian's nonnegative
tail cone. A continuous clock equals one on that compact meridian and has
support away from its antipodal center. The existing open-domain extension
therefore gives a global sphere homotopy, preserving the exceptional fiber
at every time and mapping the entire fiber to its center at the endpoint.
-/

noncomputable section

open Set Filter Topology
open scoped unitInterval

namespace NoExoticSixSphere.SuspensionProductComparison

theorem meridian_subset_contraction_domain (n : ℕ) :
    meridian n ⊆ SphereConvexContraction.domain (meridianCenter n) := by
  intro x hx h
  exact neg_meridianCenter_not_mem n (h ▸ hx)

theorem localContraction_mem_meridian (n : ℕ) (t : I)
    (x : SphereConvexContraction.domain (meridianCenter n)) (hx : x.val ∈ meridian n) :
    SphereConvexContraction.localHomotopy (meridianCenter n) (t, x) ∈ meridian n := by
  obtain ⟨c, hc, htail⟩ := hx
  let z := SphereConvexContraction.vector (meridianCenter n) x.val t
  have hcoef : 0 ≤ (1 - (t : ℝ)) * c + (t : ℝ) :=
    add_nonneg (mul_nonneg (sub_nonneg.mpr t.2.2) hc) t.2.1
  have hz : SphereCylinder.tail n z =
      ((1 - (t : ℝ)) * c + (t : ℝ)) • (spherePole n).val := by
    dsimp only [z, SphereConvexContraction.vector]
    rw [map_add, map_smul, map_smul, htail, tail_meridianCenter, smul_smul, add_smul]
  refine ⟨‖z‖⁻¹ * ((1 - (t : ℝ)) * c + (t : ℝ)),
    mul_nonneg (inv_nonneg.mpr (norm_nonneg z)) hcoef, ?_⟩
  rw [SphereConvexContraction.localHomotopy_val]
  change SphereCylinder.tail n (‖z‖⁻¹ • z) = _
  rw [map_smul, hz, smul_smul]

/-- The homotopy is constructed on the entire original sphere, not just on the meridian. -/
theorem exists_meridian_contracting_homotopy (n : ℕ) :
    ∃ g : C(Sphere (n + 1), Sphere (n + 1)),
      ∃ H : (ContinuousMap.id (Sphere (n + 1))).Homotopy g,
        (∀ (t : I) (x : Sphere (n + 1)), x ∈ meridian n → H (t, x) ∈ meridian n) ∧
        ∀ x ∈ meridian n, g x = meridianCenter n := by
  let a := meridianCenter n
  let U := SphereConvexContraction.domain a
  let L := SphereConvexContraction.localHomotopy a
  have hU : IsOpen U := SphereConvexContraction.isOpen_domain a
  obtain ⟨β, hβsupport, hβone, hβbound⟩ := exists_tsupport_one_of_isOpen_isClosed hU
    isClosed_closure.isCompact (isClosed_meridian n) (meridian_subset_contraction_domain n)
  have hzero : ∀ x : U, L (0, x) = x.val := SphereConvexContraction.localHomotopy_zero a
  let g := OpenHomotopyExtension.endpoint L β hβbound hzero hU hβsupport
  let H := OpenHomotopyExtension.homotopy L β hβbound hzero hU hβsupport
    ∅ (fun _ _ h ↦ h.elim)
  refine ⟨g, H.toHomotopy, ?_, ?_⟩
  · intro t x hx
    have hxU : x ∈ U := meridian_subset_contraction_domain n hx
    change OpenHomotopyExtension.raw L β hβbound (t, x) ∈ meridian n
    rw [OpenHomotopyExtension.raw_of_mem L β hβbound hxU]
    exact localContraction_mem_meridian n _ ⟨x, hxU⟩ hx
  · intro x hx
    have hxU : x ∈ U := meridian_subset_contraction_domain n hx
    have hβx : β x = 1 := hβone hx
    change OpenHomotopyExtension.raw L β hβbound (1, x) = a
    rw [OpenHomotopyExtension.raw_of_mem L β hβbound hxU]
    have hclock : CutoffHomotopyGluing.clock β hβbound (1, x) = 1 := by
      apply Subtype.ext
      change (1 : ℝ) * β x = 1
      rw [hβx, mul_one]
    rw [hclock]
    exact SphereConvexContraction.localHomotopy_one a ⟨x, hxU⟩

end NoExoticSixSphere.SuspensionProductComparison
