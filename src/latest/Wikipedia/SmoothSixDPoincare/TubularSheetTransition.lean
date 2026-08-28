import Wikipedia.SmoothSixDPoincare.NativeStripBoundaryFrame

/-!
# Actual sheet transitions into tubular coordinates

Restrict the retained native ambient sheet chart to its zero normal section,
then apply the actual inverse tubular chart. Its normal differential is the
already constructed sheet frame. Preserved full strip germs identify the
entire center curve in tubular coordinates, including at boundary endpoints.
-/

noncomputable section

open Set Function Filter Topology
open scoped ContDiff Manifold

namespace Wikipedia.SmoothSixDPoincare.StripNormalData

variable {A B Z E M : Type*}
  [NormedAddCommGroup A] [NormedSpace ℝ A]
  [NormedAddCommGroup B] [NormedSpace ℝ B]
  [NormedAddCommGroup Z] [NormedSpace ℝ Z]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace M] [ChartedSpace E M]
  {S : Set M} {k : (ℝ × ℝ) → M} (d : StripNormalData A B (E := E) S k)
  (Ψ : PartialDiffeomorph 𝓘(ℝ, (ℝ × ℝ) × Z) 𝓘(ℝ, E) ((ℝ × ℝ) × Z) M ∞)

def sheetTransition : (ℝ × A) → ((ℝ × ℝ) × Z) :=
  (Ψ.symm ∘ d.chart) ∘ (ContinuousLinearMap.inl ℝ (ℝ × A) B)

def sheetDifferential (t : ℝ) : (ℝ × A) →L[ℝ] ((ℝ × ℝ) × Z) :=
  fderiv ℝ (d.sheetTransition Ψ) (t, 0)

theorem contDiffAt_tubularTransition {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1)
    (htarget : d.chart (StripCoordinates.center t) ∈ Ψ.target) :
    ContDiffAt ℝ ∞ (Ψ.symm ∘ d.chart) (StripCoordinates.center t) :=
  ((Ψ.contMDiffOn_invFun.contMDiffAt (Ψ.open_target.mem_nhds htarget)).comp
    (StripCoordinates.center t)
    (d.chart.contMDiffOn_toFun.contMDiffAt (d.chart.open_source.mem_nhds (d.line ht)))).contDiffAt

theorem contDiffAt_sheetTransition {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1)
    (htarget : d.chart (StripCoordinates.center t) ∈ Ψ.target) :
    ContDiffAt ℝ ∞ (d.sheetTransition Ψ) (t, 0) :=
  (d.contDiffAt_tubularTransition Ψ ht htarget).comp (t, 0)
    (ContinuousLinearMap.inl ℝ (ℝ × A) B).contDiff.contDiffAt

theorem sheetDifferential_eq {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1)
    (htarget : d.chart (StripCoordinates.center t) ∈ Ψ.target) :
    d.sheetDifferential Ψ t =
      (fderiv ℝ (Ψ.symm ∘ d.chart) (StripCoordinates.center t)).comp
        (ContinuousLinearMap.inl ℝ (ℝ × A) B) := by
  rw [sheetDifferential, sheetTransition, fderiv_comp (t, 0)
    ((d.contDiffAt_tubularTransition Ψ ht htarget).differentiableAt (by simp))
    (ContinuousLinearMap.inl ℝ (ℝ × A) B).differentiableAt,
    (ContinuousLinearMap.inl ℝ (ℝ × A) B).fderiv]
  rfl

/-- Compose the actual native sheet and inverse-tube derivatives to obtain the sheet transition. -/
theorem sheetDifferential_eq_native {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1)
    (htarget : d.chart (StripCoordinates.center t) ∈ Ψ.target) :
    d.sheetDifferential Ψ t =
      ((mfderiv 𝓘(ℝ, E) 𝓘(ℝ, (ℝ × ℝ) × Z) Ψ.symm
        (d.chart (StripCoordinates.center t))).comp
        (mfderiv 𝓘(ℝ, StripCoordinates.Space A B) 𝓘(ℝ, E) d.chart
          (StripCoordinates.center t))).comp (ContinuousLinearMap.inl ℝ (ℝ × A) B) := by
  rw [d.sheetDifferential_eq Ψ ht htarget, ← mfderiv_eq_fderiv,
    mfderiv_comp (StripCoordinates.center t) (Ψ.symm.mdifferentiableAt (by simp) htarget)
      (d.chart.mdifferentiableAt (by simp) (d.line ht))]
  rfl

/-- The normal block of the actual sheet differential is exactly its constructed normal frame. -/
theorem normal_sheetDifferential {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1)
    (htarget : d.chart (StripCoordinates.center t) ∈ Ψ.target) :
    (ContinuousLinearMap.snd ℝ (ℝ × ℝ) Z).comp
      ((d.sheetDifferential Ψ t).comp (ContinuousLinearMap.inr ℝ ℝ A)) =
        d.normalFrame Ψ t := by
  have hn : fderiv ℝ (TransverseCoordinates.normalCoordinate Ψ ∘ d.chart)
      (StripCoordinates.center t) =
      (ContinuousLinearMap.snd ℝ (ℝ × ℝ) Z).comp
        (fderiv ℝ (Ψ.symm ∘ d.chart) (StripCoordinates.center t)) := by
    change fderiv ℝ ((ContinuousLinearMap.snd ℝ (ℝ × ℝ) Z) ∘ (Ψ.symm ∘ d.chart))
      (StripCoordinates.center t) = _
    rw [fderiv_comp _ (ContinuousLinearMap.snd ℝ (ℝ × ℝ) Z).differentiableAt
      ((d.contDiffAt_tubularTransition Ψ ht htarget).differentiableAt (by simp)),
      (ContinuousLinearMap.snd ℝ (ℝ × ℝ) Z).fderiv]
  rw [d.sheetDifferential_eq Ψ ht htarget, normalFrame, hn]
  rfl

/-- A preserved strip germ determines the full tubular-coordinate center germ. -/
theorem sheetTransition_center_germ {f : (ℝ × ℝ) → M}
    (hzero : ∀ p, Ψ (p, 0) = f p) {q : ℝ → (ℝ × ℝ)} {t : ℝ}
    (hq : ContinuousAt q t) (hp : (q t, 0) ∈ Ψ.source)
    {c : (ℝ × ℝ) → (ℝ × ℝ)} (hcq : ∀ s, c (q s) = (s, 0))
    (hgerm : f =ᶠ[𝓝 (q t)] k ∘ c) :
    (fun s : ℝ => d.sheetTransition Ψ (s, 0)) =ᶠ[𝓝 t] fun s => (q s, 0) := by
  have hs := (hq.prodMk continuousAt_const).preimage_mem_nhds (Ψ.open_source.mem_nhds hp)
  filter_upwards [hs, hgerm.comp_tendsto hq.tendsto] with s hsource heq
  dsimp only [Function.comp_apply] at heq
  rw [hcq s] at heq
  change Ψ.invFun (d.chart (StripCoordinates.center s)) = (q s, 0)
  rw [← d.center s, ← heq, ← hzero (q s)]
  exact Ψ.left_inv' hsource

/-- The actual first sheet column is the derivative of the prescribed disk-boundary arc. -/
theorem sheetDifferential_arc_of_germ {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1)
    (htarget : d.chart (StripCoordinates.center t) ∈ Ψ.target)
    {q : ℝ → (ℝ × ℝ)} {v : ℝ × ℝ} (hq : HasDerivAt q v t)
    (hgerm : (fun s : ℝ => d.sheetTransition Ψ (s, 0)) =ᶠ[𝓝 t] fun s => (q s, 0)) :
    d.sheetDifferential Ψ t (1, 0) = (v, 0) := by
  have hF := (d.contDiffAt_sheetTransition Ψ ht htarget).differentiableAt (by simp)
  have hi : HasDerivAt (fun s : ℝ => (s, (0 : A))) (1, 0) t :=
    (hasDerivAt_id t).prodMk (hasDerivAt_const t (0 : A))
  have hd := hF.hasFDerivAt.comp_hasDerivAt t hi
  have hq' : HasDerivAt (fun s => (q s, (0 : Z))) (v, 0) t :=
    hq.prodMk (hasDerivAt_const t (0 : Z))
  exact hd.unique (hq'.congr_of_eventuallyEq hgerm)

end Wikipedia.SmoothSixDPoincare.StripNormalData
