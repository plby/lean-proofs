import Wikipedia.NoExoticSixSphere.DiskImmersiveOuterAnnulus

/-!
# Finite intrinsic singularities of the original generic four-disk

Native target charts and the original embedding preserve derivative
injectivity. Chartwise isolation therefore holds for the actual manifold
derivative. Its singular set on the closed disk is compact, and absence of
singularities in the protected outer annulus makes it finite. The actual
double-point regularity for the same parameter is retained in the existence
theorem, including mixed protected and unprotected pairs.
-/

noncomputable section

open Set Function Metric
open scoped Manifold ContDiff

namespace NoExoticSixSphere.GenericFourDisk

open GLOrthonormalization

variable {M : Type*} [TopologicalSpace M] [ChartedSpace (Vector 7) M]

theorem injective_chart_derivative_iff (g : Vector 4 → M) (x : Vector 4)
    (hg : MDifferentiableAt (𝓡 4) (𝓡 7) g x)
    (c : PartialDiffeomorph (𝓡 7) (𝓡 7) M (Vector 7) ∞) (hc : g x ∈ c.source) :
    Injective (fderiv ℝ (c ∘ g) x) ↔ Injective (mfderiv (𝓡 4) (𝓡 7) g x) := by
  have hcs := c.contMDiffOn_toFun.contMDiffAt (c.open_source.mem_nhds hc)
  have hlocal : IsLocalDiffeomorphAt (𝓡 7) (𝓡 7) ∞ c (g x) :=
    ⟨c, hc, fun _ _ ↦ rfl⟩
  have hi := (hlocal.mfderivToContinuousLinearEquiv (by simp)).injective
  change Injective (mfderiv (𝓡 7) (𝓡 7) c (g x)) at hi
  rw [← mfderiv_eq_fderiv, mfderiv_comp x (hcs.mdifferentiableAt (by simp)) hg]
  constructor
  · intro h u v huv
    exact h (congrArg (mfderiv (𝓡 7) (𝓡 7) c (g x)) huv)
  · exact hi.comp

theorem injective_embedded_derivative_iff (e : EuclideanEmbedding 7 M)
    (g : Vector 4 → M) (x : Vector 4) (hg : MDifferentiableAt (𝓡 4) (𝓡 7) g x) :
    Injective (fderiv ℝ (e.toFun ∘ g) x) ↔ Injective (mfderiv (𝓡 4) (𝓡 7) g x) := by
  rw [← mfderiv_eq_fderiv, mfderiv_comp x (e.smooth.mdifferentiableAt (by simp)) hg]
  constructor
  · intro h u v huv
    exact h (congrArg (mfderiv (𝓡 7) (𝓡 e.ambientDimension) e.toFun (g x)) huv)
  · exact (e.injective_mfderiv (g x)).comp

theorem isDiscrete_singular_of_chart_jets (g : Vector 4 → M) (U : Set (Vector 4))
    (hU : IsOpen U) (hg : ∀ x ∈ U, ContMDiffAt (𝓡 4) (𝓡 7) ∞ g x)
    (C : Set (PartialDiffeomorph (𝓡 7) (𝓡 7) M (Vector 7) ∞))
    (hcov : ∀ y : M, ∃ c ∈ C, y ∈ c.source)
    (hgen : ∀ c ∈ C, OperatorRank.RegularFourSevenOn
      (fun x ↦ fderiv ℝ (c ∘ g) x) (U ∩ g ⁻¹' c.source)) :
    IsDiscrete (U ∩ {x | ¬ Injective (mfderiv (𝓡 4) (𝓡 7) g x)}) := by
  apply isDiscrete_iff_forall_mem_exists_isOpen.mpr
  intro x hx
  obtain ⟨c, hc, hxc⟩ := hcov (g x)
  let V := U ∩ g ⁻¹' c.source
  have hV : IsOpen V :=
    (show ContinuousOn g U from fun y hy ↦
      (hg y hy).continuousAt.continuousWithinAt).isOpen_inter_preimage hU c.open_source
  have hcompare (y : Vector 4) (hy : y ∈ V) :
      Injective (fderiv ℝ (c ∘ g) y) ↔ Injective (mfderiv (𝓡 4) (𝓡 7) g y) :=
    injective_chart_derivative_iff g y ((hg y hy.1).mdifferentiableAt (by simp)) c hy.2
  have hxV : x ∈ V := ⟨hx.1, hxc⟩
  have hxsing : ¬ Injective (fderiv ℝ (c ∘ g) x) := (hcompare x hxV).not.mpr hx.2
  obtain ⟨O, hO, hOeq⟩ := isDiscrete_iff_forall_mem_exists_isOpen.mp
    (hgen c hc).isolated x ⟨hxV, hxsing⟩
  have hxO : x ∈ O := by
    have hm : x ∈ O ∩ (V ∩ {y | ¬ Injective (fderiv ℝ (c ∘ g) y)}) := by
      rw [hOeq]
      exact mem_singleton x
    exact hm.1
  refine ⟨O ∩ V, hO.inter hV, ?_⟩
  ext y
  constructor
  · rintro ⟨⟨hyO, hyV⟩, hyU, hys⟩
    have hm : y ∈ O ∩ (V ∩ {z | ¬ Injective (fderiv ℝ (c ∘ g) z)}) :=
      ⟨hyO, hyV, (hcompare y hyV).not.mpr hys⟩
    rwa [hOeq] at hm
  · rintro rfl
    exact ⟨⟨hxO, hxV⟩, hx⟩

theorem finite_singular_of_chart_jets (e : EuclideanEmbedding 7 M) (g : Vector 4 → M)
    (hg : ∀ x ∈ closedBall 0 1, ContMDiffAt (𝓡 4) (𝓡 7) ∞ g x)
    (ρ : ℝ) (hρ1 : ρ < 1)
    (hi : ∀ x ∈ closedBall 0 1, ρ ≤ ‖x‖ → Injective (fderiv ℝ (e.toFun ∘ g) x))
    (C : Set (PartialDiffeomorph (𝓡 7) (𝓡 7) M (Vector 7) ∞))
    (hcov : ∀ y : M, ∃ c ∈ C, y ∈ c.source)
    (hgen : ∀ c ∈ C, OperatorRank.RegularFourSevenOn
      (fun x ↦ fderiv ℝ (c ∘ g) x) {x | ‖x‖ < ρ ∧ g x ∈ c.source}) :
    (closedBall (0 : Vector 4) 1 ∩ {x | ¬ Injective (mfderiv (𝓡 4) (𝓡 7) g x)}).Finite := by
  let S := closedBall (0 : Vector 4) 1 ∩ {x | ¬ Injective (mfderiv (𝓡 4) (𝓡 7) g x)}
  have he : S = closedBall (0 : Vector 4) 1 ∩
      {x | ¬ Injective (fderiv ℝ (e.toFun ∘ g) x)} := by
    ext x
    apply and_congr_right
    intro hx
    exact (injective_embedded_derivative_iff e g x
      ((hg x hx).mdifferentiableAt (by simp))).not.symm
  have hD : ContinuousOn (fderiv ℝ (e.toFun ∘ g)) (closedBall 0 1) :=
    fun x hx ↦ ((e.smooth.contMDiffAt.comp x (hg x hx)).contDiffAt.continuousAt_fderiv
      (by simp)).continuousWithinAt
  have hclosed : IsClosed S := by
    rw [he]
    exact hD.preimage_isClosed_of_isClosed isClosed_closedBall
      ContinuousLinearMap.isOpen_injective.isClosed_compl
  have hcompact : IsCompact S :=
    (isCompact_closedBall (0 : Vector 4) 1).of_isClosed_subset hclosed inter_subset_left
  have hdis := isDiscrete_singular_of_chart_jets g {x | ‖x‖ < ρ}
    (isOpen_lt continuous_norm continuous_const)
    (fun x hx ↦ hg x (mem_closedBall_zero_iff.mpr (hx.trans hρ1).le)) C hcov hgen
  exact hcompact.finite (hdis.mono (by
    intro x hx
    refine ⟨?_, hx.2⟩
    change ‖x‖ < ρ
    apply lt_of_not_ge
    intro hn
    exact hx.2 ((injective_embedded_derivative_iff e g x
      ((hg x hx.1).mdifferentiableAt (by simp))).mp (hi x hx.1 hn))))

theorem exists_relative_finite_singularities [IsManifold (𝓡 7) ∞ M]
    (e : EuclideanEmbedding 7 M) (f : Vector 4 → M)
    (hf : ∀ x ∈ closedBall 0 1, ContMDiffAt (𝓡 4) (𝓡 7) ∞ f x)
    (hi : ∀ q : Sphere 3, Injective (fderiv ℝ (e.toFun ∘ f) q.val))
    (V : Set M) (hV : IsOpen V) (hfV : ∀ x ∈ ball 0 1, f x ∈ V) :
    ∃ ρ : ℝ, 3 / 4 < ρ ∧ ρ < 1 ∧ ∃ g : Vector 4 → M,
      (∀ x ∈ closedBall 0 1, ContMDiffAt (𝓡 4) (𝓡 7) ∞ g x) ∧
      (∀ x ∈ closedBall 0 1, ρ ≤ ‖x‖ → g x = f x) ∧
      (∀ x ∈ closedBall 0 1, ρ ≤ ‖x‖ →
        fderiv ℝ (e.toFun ∘ g) x = fderiv ℝ (e.toFun ∘ f) x) ∧
      (∀ x ∈ ball 0 1, g x ∈ V) ∧
      (∀ x ∈ closedBall 0 1, ρ ≤ ‖x‖ → Injective (fderiv ℝ (e.toFun ∘ g) x)) ∧
      (closedBall (0 : Vector 4) 1 ∩
        {x | ¬ Injective (mfderiv (𝓡 4) (𝓡 7) g x)}).Finite ∧
      ∃ C : Set (PartialDiffeomorph (𝓡 7) (𝓡 7) M (Vector 7) ∞),
        C.Countable ∧ (∀ y : M, ∃ c ∈ C, y ∈ c.source) ∧
        (∀ c ∈ C, OperatorRank.RegularFourSevenOn
          (fun x ↦ fderiv ℝ (c ∘ g) x) {x | ‖x‖ < ρ ∧ g x ∈ c.source}) ∧
        CompactRetractionAffineFamily.RegularDoublePointsOn g (ball 0 1) (ball 0 ρ) C := by
  obtain ⟨ρ, hρ, hρ1, hfi⟩ := exists_immersive_outer_annulus e f hf hi
  obtain ⟨g, hgs, hgeq, hgD, hgV, C, hC, hcov, hgen⟩ :=
    exists_relative e f hf ρ (by linarith) hρ1 V hV hfV
  have hgi : ∀ x ∈ closedBall 0 1, ρ ≤ ‖x‖ →
      Injective (fderiv ℝ (e.toFun ∘ g) x) := by
    intro x hx hxρ
    rw [hgD x hx hxρ]
    exact hfi x hx hxρ
  exact ⟨ρ, hρ, hρ1, g, hgs, hgeq, hgD, hgV, hgi,
    finite_singular_of_chart_jets e g hgs ρ hρ1 hgi C hcov hgen.1, C, hC, hcov, hgen⟩

end NoExoticSixSphere.GenericFourDisk
