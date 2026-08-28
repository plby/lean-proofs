import Wikipedia.HomotopyGroupsOfSpheres.SymmetricUnitaryPolygonHessian

/-! # Negative sampled smooth families give negative constrained Hessian subspaces -/

noncomputable section

open scoped Matrix.Norms.Frobenius Manifold ContDiff Topology
open Set Filter

namespace Wikipedia.HomotopyGroupsOfSpheres.QuaternionicSymmetricMatrices.Polygon

open VertexSpace

variable {N : Type*} [Fintype N] [DecidableEq N] {m r : ℕ}

local instance smoothFamilyModelSelfChart :
    LocalLogarithm.NormedChartedSpace (Model N m) (Model N m) := chartedSpaceSelf _

theorem negative_hessianFamily_of_smooth_family (a b : SpecialSpace N)
    (τ : Fin (m + 2) → ℝ) (v : VertexSpace.Space N m) (hv : v ∈ admissible a b m)
    (hcrit : fderiv ℝ (localEnergy a b τ v) 0 = 0)
    (F : (Fin r → ℝ) → VertexSpace.Space N m)
    (hF : ContMDiff 𝓘(ℝ, Fin r → ℝ) 𝓘(ℝ, Model N m) ∞ F) (hFzero : F 0 = v)
    (hneg : ∀ c, c ≠ 0 → deriv (deriv (fun s : ℝ ↦ energy a b τ (F (s • c)))) 0 < 0) :
    ∃ L : (Fin r → ℝ) →ₗ[ℝ] Model N m, Function.Injective L ∧
      ∀ c, c ≠ 0 → localHessian a b τ v (L c) (L c) < 0 := by
  let G : (Fin r → ℝ) → Model N m := fun c ↦ atVertices v (F c)
  have hGzero : G 0 = 0 := by simp only [G, hFzero, atVertices_self]
  have hmem : F 0 ∈ (atVertices v).source := by
    rw [hFzero]
    exact mem_atVertices_source v
  have hG : ContDiffAt ℝ ∞ G 0 := by
    have h := (contMDiffAt_iff_target_of_mem_source
      (I := 𝓘(ℝ, Fin r → ℝ)) (I' := 𝓘(ℝ, Model N m)) (f := F) (x := 0) (y := v) hmem).mp
        hF.contMDiffAt
    simpa only [] using! h.2.contDiffAt
  let D : (Fin r → ℝ) →L[ℝ] Model N m := fderiv ℝ G 0
  have heq (c : Fin r → ℝ) :
      deriv (deriv (fun s : ℝ ↦ energy a b τ (F (s • c)))) 0 =
        localHessian a b τ v (D c) (D c) := by
    let γ : ℝ → Model N m := fun s ↦ G (s • c)
    have hγzero : γ 0 = 0 := by simp only [γ, zero_smul, hGzero]
    have hG' : ContDiffAt ℝ ∞ G ((0 : ℝ) • c) := by simpa only [zero_smul] using hG
    have hγ : ContDiffAt ℝ 2 γ 0 := by
      exact (hG'.comp 0 ((contDiff_id.smul contDiff_const).contDiffAt :
        ContDiffAt ℝ ∞ (fun s : ℝ ↦ s • c) 0)).of_le (WithTop.coe_le_coe.mpr le_top)
    have hf : ContDiffAt ℝ 2 (localEnergy a b τ v) (γ 0) := by
      rw [hγzero]
      exact (contDiffAt_localEnergy a b τ v hv).of_le (WithTop.coe_le_coe.mpr le_top)
    have hc : fderiv ℝ (localEnergy a b τ v) (γ 0) = 0 := by rwa [hγzero]
    have hs := NoExoticSixSphere.SecondDerivativeAtCritical.deriv_deriv_comp
      (E := Model N m) hf hγ hc
    have hD : HasFDerivAt G D ((0 : ℝ) • c) := by
      rw [zero_smul]
      exact (hG.differentiableAt (by simp)).hasFDerivAt
    have hd' : HasDerivAt γ (D c) 0 := by
      simpa only [Function.comp_def, γ] using!
        hD.comp_hasDerivAt 0 (real_hasDerivAt_smul c 0)
    have hd : deriv γ 0 = D c := real_deriv_eq_of_hasDerivAt (E := Model N m) hd'
    have hsource : ∀ᶠ s in 𝓝 (0 : ℝ), F (s • c) ∈ (atVertices v).source := by
      have ht : ContinuousAt (fun s : ℝ ↦ F (s • c)) 0 :=
        hF.continuous.continuousAt.comp (continuous_id.smul continuous_const).continuousAt
      exact ht.eventually ((atVertices v).open_source.mem_nhds
        (by simpa only [zero_smul] using hmem))
    have hevent : (fun s : ℝ ↦ energy a b τ (F (s • c))) =ᶠ[𝓝 (0 : ℝ)]
        (fun s ↦ localEnergy a b τ v (γ s)) := by
      filter_upwards [hsource] with s hs
      exact congrArg (energy a b τ) ((atVertices v).left_inv hs).symm
    rw [hevent.deriv.deriv_eq, hs, hγzero]
    exact congrArg₂ (fun X Y ↦ localHessian a b τ v X Y) hd hd
  have hDneg (c : Fin r → ℝ) (hc : c ≠ 0) : localHessian a b τ v (D c) (D c) < 0 := by
    rw [← heq]
    exact hneg c hc
  refine ⟨D.toLinearMap, ?_, hDneg⟩
  apply (injective_iff_map_eq_zero D.toLinearMap).mpr
  intro c hc
  by_contra hzero
  have h := hDneg c hzero
  change D c = 0 at hc
  simp only [hc, map_zero] at h
  exact lt_irrefl 0 h

end Wikipedia.HomotopyGroupsOfSpheres.QuaternionicSymmetricMatrices.Polygon
