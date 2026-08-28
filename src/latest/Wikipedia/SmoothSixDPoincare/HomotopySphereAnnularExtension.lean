import Wikipedia.SmoothSixDPoincare.ContinuousAnnularExtension
import Wikipedia.SmoothSixDPoincare.SphereAnnularNeighborhood
import Wikipedia.SmoothSixDPoincare.LowDimensionalNullhomotopy

/-!
# A boundary-neighborhood extension in the original homotopy six-sphere

The original homotopy equivalence supplies both circle nullhomotopies.
Their actual disk extensions glue to the given map on an entire annulus,
and the resulting continuous map is constant outside a compact disk.
-/

noncomputable section

open Set Function Metric Topology ContinuousMap

namespace Wikipedia.SmoothSixDPoincare

open AnnularExtension

variable {M : Type*} [TopologicalSpace M]

/-- Extend a continuous neighborhood of the standard circle, preserving a full open neighborhood. -/
theorem exists_circle_neighborhood_extension_of_circle_nullhomotopies
    (hnull : ∀ f : C(Hemisphere.Sphere 1, M),
      ∃ c, f.Homotopic (ContinuousMap.const _ c))
    {g : Hemisphere.Ambient 2 → M} {W : Set (Hemisphere.Ambient 2)}
    (hW : IsOpen W) (hg : ContinuousOn g W) (hSW : sphere (0 : Hemisphere.Ambient 2) 1 ⊆ W) :
    ∃ G : C(Hemisphere.Ambient 2, M), ∃ c : M, ∃ K : Set (Hemisphere.Ambient 2),
      IsCompact K ∧ (∀ x ∉ K, G x = c) ∧
      ∃ U : Set (Hemisphere.Ambient 2), IsOpen U ∧ sphere (0 : Hemisphere.Ambient 2) 1 ⊆ U ∧
        U ⊆ W ∧ EqOn G g U := by
  obtain ⟨a, b, ha, ha1, h1b, hAW⟩ := exists_closed_annulus_subset hW hSW
  have hab : a < b := ha1.trans h1b
  have hb : 0 < b := ha.trans hab
  let A : Set (Hemisphere.Ambient 2) := {x | a ≤ ‖x‖ ∧ ‖x‖ ≤ b}
  have hgA : ContinuousOn g A := hg.mono hAW
  have hscale (r : ℝ) (hr : r ∈ Icc a b) (v : Hemisphere.Sphere 1) :
      r • (v : Hemisphere.Ambient 2) ∈ A := by
    have hr0 : 0 < r := ha.trans_le hr.1
    have hnorm : ‖r • (v : Hemisphere.Ambient 2)‖ = r := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos hr0,
        mem_sphere_zero_iff_norm.mp v.property, mul_one]
    change a ≤ ‖r • (v : Hemisphere.Ambient 2)‖ ∧ ‖r • (v : Hemisphere.Ambient 2)‖ ≤ b
    rw [hnorm]
    exact hr
  have hcontinuous (r : ℝ) :
      Continuous (fun v : Hemisphere.Sphere 1 => r • (v : Hemisphere.Ambient 2)) := by fun_prop
  let f₀ : C(Hemisphere.Sphere 1, M) := ⟨fun v => g (a • (v : Hemisphere.Ambient 2)),
    hgA.comp_continuous (hcontinuous a) (hscale a ⟨le_rfl, hab.le⟩)⟩
  let f₁ : C(Hemisphere.Sphere 1, M) := ⟨fun v => g (b • (v : Hemisphere.Ambient 2)),
    hgA.comp_continuous (hcontinuous b) (hscale b ⟨hab.le, le_rfl⟩)⟩
  obtain ⟨c₀, ⟨H₀⟩⟩ := hnull f₀
  obtain ⟨c₁, ⟨H₁⟩⟩ := hnull f₁
  obtain ⟨v, hv⟩ : (sphere (0 : Hemisphere.Ambient 2) 1).Nonempty :=
    NormedSpace.sphere_nonempty.mpr zero_le_one
  let : Nonempty (sphere (0 : Hemisphere.Ambient 2) 1) := ⟨⟨v, hv⟩⟩
  let F₀ := DiskCone.extension f₀ c₀ H₀
  let F₁ := DiskCone.extension f₁ c₁ H₁
  obtain ⟨G, hGeq, hGconst⟩ := exists_continuous_annular_extension ha hab hgA F₀ F₁
    (DiskCone.extension_boundary f₀ c₀ H₀) (DiskCone.extension_boundary f₁ c₁ H₁)
  let U : Set (Hemisphere.Ambient 2) := {x | a < ‖x‖ ∧ ‖x‖ < b}
  have hU : IsOpen U := (isOpen_lt continuous_const continuous_norm).inter
    (isOpen_lt continuous_norm continuous_const)
  have hUA : U ⊆ A := fun _ hx => ⟨hx.1.le, hx.2.le⟩
  refine ⟨G, c₁, closedBall 0 (2 * b), isCompact_closedBall _ _, ?_, U, hU, ?_,
    hUA.trans hAW, hGeq.mono hUA⟩
  · intro x hx
    have hn : 2 * b < ‖x‖ := by simpa only [mem_closedBall_zero_iff, not_le] using hx
    rw [hGconst x hn.le]
    exact DiskCone.extension_zero f₁ c₁ H₁
  · intro x hx
    have hn : ‖x‖ = 1 := mem_sphere_zero_iff_norm.mp hx
    change a < ‖x‖ ∧ ‖x‖ < b
    rw [hn]
    exact ⟨ha1, h1b⟩

/-- The original homotopy equivalence supplies all circle contractions needed for the extension. -/
theorem exists_circle_neighborhood_extension_of_homotopySixSphere (e : M ≃ₕ SixSphere)
    {g : Hemisphere.Ambient 2 → M} {W : Set (Hemisphere.Ambient 2)}
    (hW : IsOpen W) (hg : ContinuousOn g W) (hSW : sphere (0 : Hemisphere.Ambient 2) 1 ⊆ W) :
    ∃ G : C(Hemisphere.Ambient 2, M), ∃ c : M, ∃ K : Set (Hemisphere.Ambient 2),
      IsCompact K ∧ (∀ x ∉ K, G x = c) ∧
      ∃ U : Set (Hemisphere.Ambient 2), IsOpen U ∧ sphere (0 : Hemisphere.Ambient 2) 1 ⊆ U ∧
        U ⊆ W ∧ EqOn G g U :=
  exists_circle_neighborhood_extension_of_circle_nullhomotopies
    (fun f => sphereMap_nullhomotopic_of_homotopySixSphere e (by norm_num : 1 < 6) f)
    hW hg hSW

end Wikipedia.SmoothSixDPoincare
