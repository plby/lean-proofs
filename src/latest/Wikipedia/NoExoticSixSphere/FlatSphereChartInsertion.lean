import Wikipedia.SmoothSixDPoincare.VariableChartPerturbation
import Wikipedia.NoExoticSixSphere.GLOrthonormalization
import Wikipedia.NoExoticSixSphere.Definitions
import Mathlib.Geometry.Manifold.BumpFunction

/-!
# Inserting a prescribed chart model into a flat sphere map

Nested genuine smooth bumps replace a map near a flat basepoint by a bounded
smooth chart model. The constructed homotopy fixes the basepoint. A second
cutoff has its entire zero set inside an open region of exact agreement with
the model, so both values and native derivatives can subsequently be protected.
-/

noncomputable section

open Set Function Filter Metric
open scoped Manifold ContDiff Topology

namespace NoExoticSixSphere

open GLOrthonormalization
open Wikipedia.SmoothSixDPoincare.ChartMapPerturbation

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace M] [ChartedSpace (Vector 6) M]

theorem exists_flat_sphere_chart_insertion
    (Φ : PartialDiffeomorph 𝓘(ℝ, E) (𝓡 6) E M ∞)
    (hball : ball (0 : E) 3 ⊆ Φ.source)
    (f : C(Sphere 3, M)) (hf : ContMDiff (𝓡 3) (𝓡 6) ∞ f)
    (x : Sphere 3) (U : Set (Sphere 3)) (hU : IsOpen U) (hxU : x ∈ U)
    (hflat : EqOn f (fun _ ↦ Φ 0) U)
    (v : Sphere 3 → E) (hv : ContMDiff (𝓡 3) 𝓘(ℝ, E) ∞ v)
    (hbound : ∀ s, ‖v s‖ ≤ 2) (hxv : v x = 0) :
    ∃ F : C(Sphere 3, M), ContMDiff (𝓡 3) (𝓡 6) ∞ F ∧ f.HomotopicRel F {x} ∧
      ∃ χ : Sphere 3 → ℝ, ContMDiff (𝓡 3) 𝓘(ℝ, ℝ) ∞ χ ∧
        (∀ s, 0 ≤ χ s) ∧ (∀ s, ‖χ s‖ ≤ 1) ∧ χ x = 0 ∧
        ∃ W : Set (Sphere 3), IsOpen W ∧ {s | χ s = 0} ⊆ W ∧
          EqOn F (fun s ↦ Φ (v s)) W := by
  classical
  have h0 : (0 : E) ∈ Φ.source := hball (mem_ball_self (by norm_num))
  have hleft : Φ.symm (Φ 0) = 0 := Φ.left_inv h0
  obtain ⟨β, _, hβU⟩ :=
    (SmoothBumpFunction.nhds_basis_tsupport (I := 𝓡 3) x).mem_iff.mp (hU.mem_nhds hxU)
  let W : Set (Sphere 3) := interior {s | β s = 1}
  have hxW : x ∈ W := mem_interior_iff_mem_nhds.mpr β.eventuallyEq_one
  obtain ⟨γ, _, hγW⟩ :=
    (SmoothBumpFunction.nhds_basis_tsupport (I := 𝓡 3) x).mem_iff.mp
      (isOpen_interior.mem_nhds hxW)
  have hsupport : tsupport β ⊆ f ⁻¹' Φ.symm.source := by
    intro s hs
    change f s ∈ Φ.target
    rw [hflat (hβU hs)]
    exact Φ.map_source h0
  have hvalid : ∀ a : E, ‖a‖ < 3 → Valid Φ.symm f β a := by
    intro a ha s hs
    change Φ.symm (f s) + β s • a ∈ Φ.source
    rw [hflat (hβU hs)]
    change Φ.symm (Φ 0) + β s • a ∈ Φ.source
    rw [hleft, zero_add]
    apply hball
    rw [mem_ball_zero_iff, norm_smul, Real.norm_eq_abs, abs_of_nonneg β.nonneg]
    exact (mul_le_of_le_one_left (norm_nonneg a) β.le_one).trans_lt ha
  have hsmall : ∀ s, ‖v s‖ < 3 := fun s ↦ (hbound s).trans_lt (by norm_num)
  let F : C(Sphere 3, M) := ⟨variablePerturb Φ.symm f β v,
    continuous_variablePerturb Φ.symm f.continuous β.continuous hsupport hv.continuous
      (fun s ↦ hvalid _ (hsmall s))⟩
  have hF : ContMDiff (𝓡 3) (𝓡 6) ∞ F := fun s ↦
    contMDiffAt_variablePerturb Φ.symm hsupport (hf s) (β.contMDiff s) (hv s)
      (hvalid _ (hsmall s))
  have H : f.HomotopicRel F {x} := by
    refine ⟨variableHomotopyRel Φ.symm f.continuous β.continuous hsupport hv.continuous
      hvalid hsmall ?_⟩
    rintro s rfl
    exact Or.inr hxv
  let χ : Sphere 3 → ℝ := fun s ↦ 1 - γ s
  have hχ : ContMDiff (𝓡 3) 𝓘(ℝ, ℝ) ∞ χ := contMDiff_const.sub γ.contMDiff
  have hχn : ∀ s, 0 ≤ χ s := fun s ↦ sub_nonneg.mpr γ.le_one
  have hχb : ∀ s, ‖χ s‖ ≤ 1 := by
    intro s
    rw [Real.norm_eq_abs, abs_of_nonneg (hχn s)]
    exact sub_le_self 1 γ.nonneg
  have hχx : χ x = 0 := by simp only [χ, γ.eq_one, sub_self]
  refine ⟨F, hF, H, χ, hχ, hχn, hχb, hχx, W, isOpen_interior, ?_, ?_⟩
  · intro s hs
    have hγs : γ s = 1 := (sub_eq_zero.mp hs).symm
    exact hγW (subset_tsupport γ (by change γ s ≠ 0; rw [hγs]; exact one_ne_zero))
  · intro s hs
    have hβs : β s = 1 := interior_subset (s := {s : Sphere 3 | β s = 1}) hs
    have hsβ : s ∈ tsupport β :=
      subset_tsupport β (by change β s ≠ 0; rw [hβs]; exact one_ne_zero)
    have hsU : s ∈ U := hβU hsβ
    have hfs : f s ∈ Φ.symm.source := hsupport hsβ
    change perturb Φ.symm f β (v s) s = Φ (v s)
    simp only [perturb, hfs, if_pos, coordinateFamily]
    change Φ (Φ.symm (f s) + β s • v s) = Φ (v s)
    rw [hflat hsU]
    change Φ (Φ.symm (Φ 0) + β s • v s) = Φ (v s)
    rw [hleft, hβs, one_smul, zero_add]

end NoExoticSixSphere
