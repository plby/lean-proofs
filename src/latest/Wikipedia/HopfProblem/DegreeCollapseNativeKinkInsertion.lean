import Wikipedia.HopfProblem.DegreeCollapseKinkPatchData
import Wikipedia.HopfProblem.DegreeCollapseScaledKinkDifferential
import Wikipedia.HopfProblem.DegreeCollapseCompactSourcePatchFamily

/-!
# The actual globally smooth inserted immersion

Fit the explicit model in the constructed native charts, and glue its
bounded-time family across its compact inner source support. All native
derivative factors are retained. This module proves smoothness, immersion,
and homotopy of the inserted endpoint, before its global pair count.
-/

noncomputable section

open Set Function Metric Topology
open scoped Manifold ContDiff

namespace Wikipedia.HopfProblem.DegreeCollapse.ImmersedSource.KinkPatchData

open NoExoticSixSphere NoExoticSixSphere.GLOrthonormalization SupportedCusp

variable {M : Type*} [TopologicalSpace M] [ChartedSpace (Vector 6) M]
  {F : Sphere 3 → M} (P : KinkPatchData F)

theorem inverse_mem_ball {x : Sphere 3} (hx : x ∈ P.sourcePatch) :
    (shiftedSourceChart P.center).symm x ∈ ball (0 : Vector 3) P.radius := by
  obtain ⟨u, hu, rfl⟩ := hx
  have he := (shiftedSourceChart P.center).left_inv
    (by rw [shiftedSourceChart_source]; exact mem_univ u)
  exact he.symm ▸ hu

theorem contMDiffAt_localFamily {t : ℝ} (ht : t ∈ Icc (-1 : ℝ) 1)
    {x : Sphere 3} (hx : x ∈ P.sourcePatch) :
    ContMDiffAt (𝓘(ℝ, ℝ).prod (𝓡 3)) (𝓡 6) ∞ P.localFamily (t, x) := by
  have hχ : ContMDiffAt (𝓡 3) (𝓡 3) ∞ (shiftedSourceChart P.center).symm x :=
    (shiftedSourceChart P.center).contMDiffOn_invFun.contMDiffAt
      ((shiftedSourceChart P.center).open_target.mem_nhds (P.sourcePatch_subset_target hx))
  have hcoords : ContMDiffAt (𝓘(ℝ, ℝ).prod (𝓡 3))
      𝓘(ℝ, ℝ × Vector 3) ∞
      (fun z : ℝ × Sphere 3 ↦ (z.1, (shiftedSourceChart P.center).symm z.2)) (t, x) :=
    contMDiffAt_fst.prodMk_space (hχ.comp (t, x) contMDiffAt_snd)
  have hmodel := (contDiff_scaledMap P.cutoff P.scale).contMDiff.contMDiffAt.comp (t, x) hcoords
  have htarget := P.chart.contMDiffOn_toFun.contMDiffAt
    (P.chart.open_source.mem_nhds (P.map_source ht (P.inverse_mem_ball hx)))
  exact htarget.comp (t, x) hmodel

theorem injective_mfderiv_localEndpoint {x : Sphere 3} (hx : x ∈ P.sourcePatch) :
    Injective (mfderiv (𝓡 3) (𝓡 6) (fun y ↦ P.localFamily (1, y)) x) := by
  let χ := shiftedSourceChart P.center
  let k := scaledMap P.cutoff P.scale (1 : ℝ)
  have hxχ : x ∈ χ.target := P.sourcePatch_subset_target hx
  have hχ := χ.symm.isLocalDiffeomorphAt (𝓡 3) (𝓡 3) ∞ hxχ
  have hk : ContDiff ℝ ∞ k := contDiff_scaledMap_slice P.cutoff P.scale 1
  have hΦ := P.chart.isLocalDiffeomorphAt (𝓡 6) (𝓡 6) ∞
    (P.map_source (by norm_num : (1 : ℝ) ∈ Icc (-1 : ℝ) 1) (P.inverse_mem_ball hx))
  have hχd : MDifferentiableAt (𝓡 3) (𝓡 3) χ.symm x := hχ.mdifferentiableAt (by simp)
  have hkd : MDifferentiableAt (𝓡 3) (𝓡 6) k (χ.symm x) :=
    hk.contMDiff.mdifferentiableAt (by simp)
  have hΦd : MDifferentiableAt (𝓡 6) (𝓡 6) P.chart (k (χ.symm x)) :=
    hΦ.mdifferentiableAt (by simp)
  have hχi : Injective (mfderiv (𝓡 3) (𝓡 3) χ.symm x) :=
    (hχ.mfderivToContinuousLinearEquiv (by simp)).injective
  have hki : Injective (mfderiv (𝓡 3) (𝓡 6) k (χ.symm x)) := by
    rw [mfderiv_eq_fderiv]
    exact injective_fderiv_scaledMap P.cutoff P.scale_pos.ne' one_ne_zero _
  have hΦi : Injective (mfderiv (𝓡 6) (𝓡 6) P.chart (k (χ.symm x))) :=
    (hΦ.mfderivToContinuousLinearEquiv (by simp)).injective
  change Injective (mfderiv (𝓡 3) (𝓡 6) (P.chart ∘ (k ∘ χ.symm)) x)
  rw [mfderiv_comp x hΦd (hkd.comp x hχd), mfderiv_comp x hkd hχd]
  exact hΦi.comp (hki.comp hχi)

def insertedMap (x : Sphere 3) : M :=
  SourcePatch.family F P.localFamily P.sourcePatch (1, x)

theorem insertedMap_fixed {x : Sphere 3} (hx : x ∉ P.sourceSupport) : P.insertedMap x = F x :=
  SourcePatch.family_fixed P.localFamily_fixed 1 hx

theorem insertedMap_on {x : Sphere 3} (hx : x ∈ P.sourcePatch) :
    P.insertedMap x = P.localFamily (1, x) :=
  SourcePatch.family_on F P.localFamily P.sourcePatch 1 hx

theorem exists_native_immersed_insertion (F : C(Sphere 3, M)) (P : KinkPatchData F)
    (hf : ContMDiff (𝓡 3) (𝓡 6) ∞ F)
    (hi : ∀ x, Injective (mfderiv (𝓡 3) (𝓡 6) F x)) :
    ∃ g : C(Sphere 3, M), ContMDiff (𝓡 3) (𝓡 6) ∞ g ∧ F.Homotopic g ∧
      (∀ x, Injective (mfderiv (𝓡 3) (𝓡 6) g x)) ∧
      (∀ x, g x = P.insertedMap x) ∧ (∀ x ∉ P.sourceSupport, g x = F x) := by
  exact SourcePatch.exists_immersed_endpoint_homotopic F P.isOpen_sourcePatch
    P.isCompact_sourceSupport.isClosed P.sourceSupport_subset hf hi
    (fun _ ht _ hx ↦ P.contMDiffAt_localFamily ht hx)
    (fun _ hx ↦ P.injective_mfderiv_localEndpoint hx) P.localFamily_start P.localFamily_fixed

end Wikipedia.HopfProblem.DegreeCollapse.ImmersedSource.KinkPatchData
