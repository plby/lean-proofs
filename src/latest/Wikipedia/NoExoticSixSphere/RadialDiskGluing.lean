import Wikipedia.NoExoticSixSphere.DiskBoundaryNullhomotopy
import Mathlib.Topology.Order.ProjIcc

/-!
# Gluing an actual inner disk to a prescribed radial annulus

Scale the inner disk to radius `ρ` and keep the given map unchanged
on the whole outer annulus. The sphere-cylinder quotient proves continuity
at the center, and the two continuous formulas agree exactly at the seam.
Interior avoidance is retained, with no smoothness assertion at the seam.
-/

noncomputable section

open Set Metric
open scoped unitInterval

namespace NoExoticSixSphere.RadialDiskGluing

open Wikipedia.HopfProblem.DegreeCollapse
open DiskCylinder

variable {E X : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace X]
  (ρ : ℝ) (hρ : 0 < ρ) (hρ1 : ρ < 1)
  (F : C(Disk (E := E), X)) (g : E → X)
  (hg : ContinuousOn g (closedBall (0 : E) 1 ∩ {x | ρ ≤ ‖x‖}))
  (hb : ∀ s : DiskCylinder.Sphere (E := E), F (boundaryToDisk s) = g (ρ • s.val))

def cylinder : C(unitInterval × DiskCylinder.Sphere (E := E), X) where
  toFun z := if (z.1 : ℝ) ≤ ρ then
    F (DiskCone.radial (projIcc 0 1 zero_le_one ((z.1 : ℝ) / ρ), z.2))
    else g ((z.1 : ℝ) • z.2.val)
  continuous_toFun := by
    apply continuous_if_le (continuous_subtype_val.comp continuous_fst) continuous_const
    · exact (F.continuous.comp (DiskCone.radial.continuous.comp
        (((continuous_projIcc.comp
          ((continuous_subtype_val.comp continuous_fst).div_const ρ))).prodMk
            continuous_snd))).continuousOn
    · apply hg.comp
        (((continuous_subtype_val.comp continuous_fst).smul
          (continuous_subtype_val.comp continuous_snd)).continuousOn)
      intro z hz
      have hn : ‖(z.1 : ℝ) • z.2.val‖ = (z.1 : ℝ) := by
        rw [norm_smul, Real.norm_of_nonneg z.1.property.1,
          mem_sphere_zero_iff_norm.mp z.2.property, mul_one]
      exact ⟨mem_closedBall_zero_iff.mpr (hn.trans_le z.1.property.2), hz.trans_eq hn.symm⟩
    · intro z hz
      change (z.1 : ℝ) = ρ at hz
      rw [hz, div_self hρ.ne']
      have hp : projIcc 0 1 zero_le_one (1 : ℝ) = (1 : unitInterval) :=
        projIcc_of_mem zero_le_one ⟨zero_le_one, le_rfl⟩
      rw [hp, DiskCone.radial_one, hb]

theorem cylinder_zero (s : DiskCylinder.Sphere (E := E)) :
    cylinder ρ hρ F g hg hb (0, s) = F ⟨0, by simp⟩ := by
  change (if (0 : ℝ) ≤ ρ then
    F (DiskCone.radial (projIcc 0 1 zero_le_one ((0 : ℝ) / ρ), s)) else _) = _
  rw [if_pos hρ.le, zero_div]
  have hp : projIcc 0 1 zero_le_one (0 : ℝ) = (0 : unitInterval) :=
    projIcc_of_mem zero_le_one ⟨le_rfl, zero_le_one⟩
  rw [hp, DiskCone.radial_zero]

def map (b : DiskCylinder.Sphere (E := E)) : C(Disk (E := E), X) :=
  DiskCone.extension b (cylinder ρ hρ F g hg hb) (F ⟨0, by simp⟩)
    (cylinder_zero ρ hρ F g hg hb)

theorem map_radial_of_le (b : DiskCylinder.Sphere (E := E)) (u : unitInterval)
    (hu : (u : ℝ) ≤ ρ) (s : DiskCylinder.Sphere (E := E)) :
    map ρ hρ F g hg hb b (DiskCone.radial (u, s)) =
      F (DiskCone.radial (projIcc 0 1 zero_le_one ((u : ℝ) / ρ), s)) := by
  rw [map, DiskCone.extension_radial]
  exact if_pos hu

theorem map_radial_of_ge (b : DiskCylinder.Sphere (E := E)) (u : unitInterval)
    (hu : ρ ≤ (u : ℝ)) (s : DiskCylinder.Sphere (E := E)) :
    map ρ hρ F g hg hb b (DiskCone.radial (u, s)) = g ((u : ℝ) • s.val) := by
  rw [map, DiskCone.extension_radial]
  change (if (u : ℝ) ≤ ρ then
    F (DiskCone.radial (projIcc 0 1 zero_le_one ((u : ℝ) / ρ), s)) else _) = _
  by_cases hle : (u : ℝ) ≤ ρ
  · have heq : (u : ℝ) = ρ := le_antisymm hle hu
    rw [if_pos hle, heq, div_self hρ.ne']
    have hp : projIcc 0 1 zero_le_one (1 : ℝ) = (1 : unitInterval) :=
      projIcc_of_mem zero_le_one ⟨zero_le_one, le_rfl⟩
    rw [hp, DiskCone.radial_one, hb]
  · exact if_neg hle

theorem map_annulus (b : DiskCylinder.Sphere (E := E)) (x : Disk (E := E))
    (hx : ρ ≤ ‖x.val‖) : map ρ hρ F g hg hb b x = g x.val := by
  obtain ⟨⟨u, s⟩, he⟩ := DiskCone.radial_surjective b x
  have hu : ρ ≤ (u : ℝ) := by rw [← DiskCone.radial_norm (u, s), he]; exact hx
  rw [← he]
  exact map_radial_of_ge ρ hρ F g hg hb b u hu s

include hρ1 in
theorem map_boundary (b s : DiskCylinder.Sphere (E := E)) :
    map ρ hρ F g hg hb b (boundaryToDisk s) = g s.val :=
  map_annulus ρ hρ F g hg hb b _ (by
    change ρ ≤ ‖s.val‖
    rw [mem_sphere_zero_iff_norm.mp s.property]
    exact hρ1.le)

theorem map_interior (b : DiskCylinder.Sphere (E := E)) (V : Set X)
    (hF : ∀ x, F x ∈ V)
    (hgV : ∀ x ∈ ball (0 : E) 1, ρ ≤ ‖x‖ → g x ∈ V)
    (x : Disk (E := E)) (hx : ‖x.val‖ < 1) : map ρ hρ F g hg hb b x ∈ V := by
  by_cases hle : ρ ≤ ‖x.val‖
  · rw [map_annulus ρ hρ F g hg hb b x hle]
    exact hgV x.val (mem_ball_zero_iff.mpr hx) hle
  · obtain ⟨⟨u, s⟩, he⟩ := DiskCone.radial_surjective b x
    have hu : (u : ℝ) ≤ ρ := by
      rw [← DiskCone.radial_norm (u, s), he]
      exact (lt_of_not_ge hle).le
    rw [← he, map_radial_of_le ρ hρ F g hg hb b u hu s]
    exact hF _

end NoExoticSixSphere.RadialDiskGluing
