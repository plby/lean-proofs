import Wikipedia.HopfProblem.PeriodTorusLineBundleClassificationTopologicalInterval
import Mathlib.Topology.VectorBundle.Constructions
import Mathlib.Topology.UnitInterval

/-!
# Actual fibre-linear transport along a fixed path

Pull back an arbitrary native complex line bundle along a continuous path,
linearly trivialize that pullback over the unit interval, and transport vectors
in those coordinates. This gives continuous, fibrewise complex-linear transport
and lifts of paths that avoid the zero section.

The choice is made for one fixed path. No homotopy invariance or continuous
dependence on the path itself is asserted.
-/

noncomputable section

open Bundle Set Topology
open scoped unitInterval

namespace Wikipedia.HopfProblem.PeriodTorusLineBundleClassificationTopological

variable {M : Type*} [TopologicalSpace M] (V : M → Type*)
    [∀ x, AddCommMonoid (V x)] [∀ x, Module ℂ (V x)]
    [∀ x, TopologicalSpace (V x)] [TopologicalSpace (TotalSpace ℂ V)]
    [FiberBundle ℂ V] [VectorBundle ℂ ℂ V]

/-- Along any fixed continuous path there is actual complex-linear transport
whose total-space map is jointly continuous in time and the initial vector. -/
theorem exists_path_transport (γ : C(I, M)) :
    ∃ T : ∀ t : I, V (γ 0) ≃L[ℂ] V (γ t),
      T 0 = ContinuousLinearEquiv.refl ℂ (V (γ 0)) ∧
        Continuous (fun r : I × V (γ 0) =>
          (⟨γ r.1, T r.1 r.2⟩ : TotalSpace ℂ V)) := by
  let Vγ := (γ : I → M) *ᵖ V
  obtain ⟨e, he, hcover⟩ := exists_linear_trivialization_Icc_subset Vγ (0 : I) 1
  let := he
  have ht (t : I) : t ∈ e.baseSet := hcover ⟨bot_le, le_top⟩
  let c₀ := e.continuousLinearEquivAt ℂ 0 (ht 0)
  let T (t : I) : V (γ 0) ≃L[ℂ] V (γ t) :=
    c₀.trans (e.continuousLinearEquivAt ℂ t (ht t)).symm
  refine ⟨T, ?_, ?_⟩
  · ext v
    exact c₀.symm_apply_apply v
  · have hcoords : Continuous (fun r : I × V (γ 0) => (r.1, c₀ r.2)) :=
      continuous_fst.prodMk (c₀.continuous.comp continuous_snd)
    have hsection : Continuous (fun r : I × V (γ 0) =>
        (⟨r.1, e.symm r.1 (c₀ r.2)⟩ : TotalSpace ℂ Vγ)) :=
      e.continuousOn_symm.comp_continuous hcoords (fun r => ⟨ht r.1, mem_univ _⟩)
    exact (Pullback.continuous_lift ℂ V (γ : I → M)).comp hsection

/-- Every base path lifts through the complement of the zero section, starting
at any prescribed nonzero native fibre vector. -/
theorem exists_nonzero_path_lift (γ : C(I, M)) (v₀ : V (γ 0)) (hv₀ : v₀ ≠ 0) :
    ∃ Γ : C(I, TotalSpace ℂ V),
      (∀ t, (Γ t).proj = γ t) ∧ Γ 0 = ⟨γ 0, v₀⟩ ∧ ∀ t, (Γ t).2 ≠ 0 := by
  obtain ⟨T, hT, hc⟩ := exists_path_transport V γ
  let Γ : C(I, TotalSpace ℂ V) :=
    ⟨fun t => ⟨γ t, T t v₀⟩, hc.comp (continuous_id.prodMk continuous_const)⟩
  refine ⟨Γ, fun _ => rfl, ?_, ?_⟩
  · change (⟨γ 0, T 0 v₀⟩ : TotalSpace ℂ V) = ⟨γ 0, v₀⟩
    rw [hT]
    rfl
  · intro t h
    change T t v₀ = 0 at h
    exact hv₀ ((T t).injective (h.trans (map_zero _).symm))

end Wikipedia.HopfProblem.PeriodTorusLineBundleClassificationTopological
