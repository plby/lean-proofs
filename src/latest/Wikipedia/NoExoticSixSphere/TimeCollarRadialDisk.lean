import Wikipedia.NoExoticSixSphere.TimeCollarDiskExtension
import Wikipedia.NoExoticSixSphere.RadialDiskGluing

/-!
# Filling a prescribed inward annulus in an actual collared half

The inner sphere is homotopic in the half to the original boundary sphere.
Transfer its disk to the positive interior, then glue the exact annulus.
Every interior point of the resulting disk has positive time, and the
entire prescribed annulus is unchanged. This is a continuous construction.
-/

noncomputable section

open Set Metric
open scoped unitInterval

namespace NoExoticSixSphere.TimeCollarDisk

open Wikipedia.HopfProblem.DegreeCollapse
open DiskCylinder TimeCollar

variable {M B : Type} [TopologicalSpace M] [TopologicalSpace B] (t : M → ℝ)

def zeroToHalf : C({x : M // t x = 0}, NonnegativeHalf t) :=
  ⟨fun x ↦ ⟨x.val, x.property.ge⟩, continuous_subtype_val.subtype_mk _⟩

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  (C : TimeCollar t B) (b : DiskCylinder.Sphere (E := E))

include C b in
theorem exists_disk_with_prescribed_annulus
    (f : C(DiskCylinder.Sphere (E := E), {x : M // t x = 0}))
    (F : C(Disk (E := E), NonnegativeHalf t))
    (hF : ∀ s, F (boundaryToDisk s) = zeroToHalf t (f s))
    (ρ : ℝ) (hρ : 0 < ρ) (hρ1 : ρ < 1) (g : E → M)
    (hg : ContinuousOn g (closedBall (0 : E) 1 ∩ {x | ρ ≤ ‖x‖}))
    (hb : ∀ s : DiskCylinder.Sphere (E := E), g s.val = (f s).val)
    (hpos : ∀ x ∈ ball (0 : E) 1, ρ ≤ ‖x‖ → 0 < t (g x)) :
    ∃ G : C(Disk (E := E), M),
      (∀ s, G (boundaryToDisk s) = (f s).val) ∧
      (∀ x, ‖x.val‖ < 1 → 0 < t (G x)) ∧
      ∀ x : Disk (E := E), ρ ≤ ‖x.val‖ → G x = g x.val := by
  have hn (u : ℝ) (hu : 0 ≤ u) (s : DiskCylinder.Sphere (E := E)) :
      ‖u • s.val‖ = u := by
    rw [norm_smul, Real.norm_of_nonneg hu, mem_sphere_zero_iff_norm.mp s.property, mul_one]
  have hnonneg (x : E) (hx : x ∈ closedBall (0 : E) 1) (hrx : ρ ≤ ‖x‖) :
      0 ≤ t (g x) := by
    have hx1 : ‖x‖ ≤ 1 := mem_closedBall_zero_iff.mp hx
    by_cases heq : ‖x‖ = 1
    · let s : DiskCylinder.Sphere (E := E) := ⟨x, mem_sphere_zero_iff_norm.mpr heq⟩
      have he : t (g x) = 0 := (congrArg t (hb s)).trans (f s).property
      exact he.ge
    · exact (hpos x (mem_ball_zero_iff.mpr (lt_of_le_of_ne hx1 heq)) hrx).le
  have hinner (s : DiskCylinder.Sphere (E := E)) :
      ρ • s.val ∈ closedBall (0 : E) 1 ∩ {x | ρ ≤ ‖x‖} := by
    rw [mem_inter_iff, mem_closedBall_zero_iff, mem_setOf_eq, hn ρ hρ.le]
    exact ⟨hρ1.le, le_rfl⟩
  let fInner : C(DiskCylinder.Sphere (E := E), C.positiveInterior) :=
    ⟨fun s ↦ ⟨g (ρ • s.val), hpos _ (by rw [mem_ball_zero_iff, hn ρ hρ.le]; exact hρ1)
      (hinner s).2⟩,
      (hg.comp_continuous (continuous_const.smul continuous_subtype_val) hinner).subtype_mk _⟩
  let radius : unitInterval → ℝ := fun u ↦ 1 + (ρ - 1) * (u : ℝ)
  have hradius (u : unitInterval) : ρ ≤ radius u ∧ radius u ≤ 1 := by
    dsimp only [radius]
    constructor
    · have h := mul_le_mul_of_nonpos_left u.property.2 (sub_nonpos.mpr hρ1.le)
      linarith
    · have h := mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hρ1.le) u.property.1
      linarith
  have hradiusc : Continuous radius :=
    continuous_const.add (continuous_const.mul continuous_subtype_val)
  have hray (z : unitInterval × DiskCylinder.Sphere (E := E)) :
      radius z.1 • z.2.val ∈ closedBall (0 : E) 1 ∩ {x | ρ ≤ ‖x‖} := by
    rw [mem_inter_iff, mem_closedBall_zero_iff, mem_setOf_eq,
      hn (radius z.1) (hρ.le.trans (hradius z.1).1)]
    exact ⟨(hradius z.1).2, (hradius z.1).1⟩
  let H : ((zeroToHalf t).comp f).Homotopy (C.interiorToHalf.comp fInner) := {
    toFun z := ⟨g (radius z.1 • z.2.val), hnonneg _ (hray z).1 (hray z).2⟩
    continuous_toFun := (hg.comp_continuous
      ((hradiusc.comp continuous_fst).smul (continuous_subtype_val.comp continuous_snd))
      hray).subtype_mk _
    map_zero_left s := by
      apply Subtype.ext
      change g ((1 + (ρ - 1) * (0 : ℝ)) • s.val) = (f s).val
      simpa only [mul_zero, add_zero, one_smul] using hb s
    map_one_left s := by
      apply Subtype.ext
      change g ((1 + (ρ - 1) * (1 : ℝ)) • s.val) = g (ρ • s.val)
      congr 2
      ring
  }
  obtain ⟨FInnerHalf, hFInnerHalf⟩ := DiskBoundary.exists_extension_of_homotopic ⟨H⟩ F hF
  obtain ⟨FInner, hFInner⟩ := exists_interior_disk_extension C fInner FInnerHalf hFInnerHalf
  let FInnerM : C(Disk (E := E), M) :=
    ⟨fun x ↦ (FInner x).val, continuous_subtype_val.comp FInner.continuous⟩
  have hFInnerM (s : DiskCylinder.Sphere (E := E)) :
      FInnerM (boundaryToDisk s) = g (ρ • s.val) :=
    congrArg Subtype.val (hFInner s)
  refine ⟨RadialDiskGluing.map ρ hρ FInnerM g hg hFInnerM b, ?_, ?_, ?_⟩
  · intro s
    exact (RadialDiskGluing.map_boundary ρ hρ hρ1 FInnerM g hg hFInnerM b s).trans (hb s)
  · intro x hx
    exact RadialDiskGluing.map_interior ρ hρ FInnerM g hg hFInnerM b {x | 0 < t x}
      (fun x ↦ (FInner x).property) hpos x hx
  · exact RadialDiskGluing.map_annulus ρ hρ FInnerM g hg hFInnerM b

end NoExoticSixSphere.TimeCollarDisk
