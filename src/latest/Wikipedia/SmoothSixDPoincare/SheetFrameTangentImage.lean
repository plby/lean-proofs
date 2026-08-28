import Wikipedia.SmoothSixDPoincare.NativeStripBoundaryFrame

/-!
# The actual native sheet tangent image is covered by the boundary frame

Clean sheet coordinates make the inverse-chart derivative of every original
sheet tangent vector horizontal. If the tubular normal projection kills the
arc direction, its remaining image belongs to the constructed sheet frame.
This relates the boundary frame to the original native sheet map, not merely
to an unrelated linear subspace of the ambient model.
-/

noncomputable section

open Set Function
open Filter Topology
open scoped ContDiff Manifold

namespace Wikipedia.SmoothSixDPoincare.StripNormalData

variable {A B D Z E M N : Type*}
  [NormedAddCommGroup A] [NormedSpace ℝ A]
  [NormedAddCommGroup B] [NormedSpace ℝ B]
  [NormedAddCommGroup D] [NormedSpace ℝ D]
  [NormedAddCommGroup Z] [NormedSpace ℝ Z]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace M] [ChartedSpace E M]
  [TopologicalSpace N] [ChartedSpace D N]
  {F : N → M} {k : (ℝ × ℝ) → M}
  (d : StripNormalData A B (E := E) (range F) k)
  (Ψ : PartialDiffeomorph 𝓘(ℝ, (ℝ × ℝ) × Z) 𝓘(ℝ, E) ((ℝ × ℝ) × Z) M ∞)

/-- Every projected tangent vector of the original native sheet is in the actual frame image. -/
theorem normal_sheet_tangent_mem_frame
    (hF : ContMDiff 𝓘(ℝ, D) 𝓘(ℝ, E) ∞ F)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) {x : N}
    (hcenter : F x = d.chart (StripCoordinates.center t)) (htarget : F x ∈ Ψ.target)
    (hkill : (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, Z) (TransverseCoordinates.normalCoordinate Ψ) (F x))
      ((mfderiv 𝓘(ℝ, StripCoordinates.Space A B) 𝓘(ℝ, E) d.chart
        (StripCoordinates.center t)) (StripCoordinates.center 1)) = 0)
    (v : D) :
    (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, Z) (TransverseCoordinates.normalCoordinate Ψ) (F x))
      ((mfderiv 𝓘(ℝ, D) 𝓘(ℝ, E) F x) v) ∈ (d.normalFrame Ψ t).range := by
  let T : StripCoordinates.Space A B →L[ℝ] E :=
    mfderiv 𝓘(ℝ, StripCoordinates.Space A B) 𝓘(ℝ, E) d.chart (StripCoordinates.center t)
  let R : E →L[ℝ] StripCoordinates.Space A B :=
    mfderiv 𝓘(ℝ, E) 𝓘(ℝ, StripCoordinates.Space A B) d.chart.symm (F x)
  let Q : E →L[ℝ] Z :=
    mfderiv 𝓘(ℝ, E) 𝓘(ℝ, Z) (TransverseCoordinates.normalCoordinate Ψ) (F x)
  let DF : D →L[ℝ] E := mfderiv 𝓘(ℝ, D) 𝓘(ℝ, E) F x
  have hx : F x ∈ d.chart.target := by
    rw [hcenter]
    exact d.chart.map_source' (d.line ht)
  have hinv : d.chart.symm (F x) = StripCoordinates.center t := by
    rw [hcenter]
    exact d.chart.left_inv' (d.line ht)
  have hdiff : d.chart.toOpenPartialHomeomorph.MDifferentiable
      𝓘(ℝ, StripCoordinates.Space A B) 𝓘(ℝ, E) :=
    ⟨d.chart.mdifferentiableOn (by simp), d.chart.symm.mdifferentiableOn (by simp)⟩
  have hTR : T.comp R = ContinuousLinearMap.id ℝ E := by
    have heq := hdiff.comp_symm_deriv hx
    change (mfderiv 𝓘(ℝ, StripCoordinates.Space A B) 𝓘(ℝ, E) d.chart
      (d.chart.symm (F x))).comp R = ContinuousLinearMap.id ℝ E at heq
    rw [hinv] at heq
    exact heq
  have hTR_apply (w : E) : T (R w) = w := by
    change (T.comp R) w = w
    rw [hTR]
    rfl
  have hn : (R (DF v)).2 = 0 := by
    have heq := TransverseCoordinates.normalDerivative_comp_sheet_eq_zero
      d.chart hF d.sheet hx
    rw [TransverseCoordinates.mfderiv_normalCoordinate d.chart hx] at heq
    exact congrArg (fun C : D →L[ℝ] B => C v) heq
  let w := R (DF v)
  have hw : w = w.1.1 • StripCoordinates.center 1 +
      StripCoordinates.sheetTransverseInclusion w.1.2 := by
    apply Prod.ext
    · ext <;> simp [StripCoordinates.center, StripCoordinates.sheetTransverseInclusion_apply]
    · simpa [StripCoordinates.center, StripCoordinates.sheetTransverseInclusion_apply] using hn
  have hframe : d.normalFrame Ψ t = (Q.comp T).comp StripCoordinates.sheetTransverseInclusion := by
    have htarget' : d.chart (StripCoordinates.center t) ∈ Ψ.target := hcenter ▸ htarget
    rw [d.normalFrame_eq_native_comp Ψ ht htarget', ← hcenter]
    rfl
  have hkill' : Q (T (StripCoordinates.center 1)) = 0 := hkill
  refine ⟨w.1.2, ?_⟩
  rw [hframe]
  change Q (T (StripCoordinates.sheetTransverseInclusion w.1.2)) = Q (DF v)
  rw [← hTR_apply (DF v)]
  change Q (T (StripCoordinates.sheetTransverseInclusion w.1.2)) = Q (T w)
  conv_rhs => rw [hw]
  rw [map_add, map_smul, map_add, map_smul, hkill', smul_zero, zero_add]

/-- The preserved strip germ supplies the annihilation hypothesis for native sheet tangents. -/
theorem normal_sheet_tangent_mem_frame_of_strip_germ
    (hF : ContMDiff 𝓘(ℝ, D) 𝓘(ℝ, E) ∞ F)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1)
    (hk : ContMDiffAt 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, E) ∞ k (t, 0))
    {f : (ℝ × ℝ) → M} (hzero : ∀ p, Ψ (p, 0) = f p)
    {p : ℝ × ℝ} (hp : (p, 0) ∈ Ψ.source)
    {c : (ℝ × ℝ) → (ℝ × ℝ)} (hc : ContDiffAt ℝ ∞ c p)
    (hcp : c p = (t, 0)) (hcs : Surjective (fderiv ℝ c p))
    (hgerm : f =ᶠ[𝓝 p] k ∘ c) {x : N} (hx : F x = k (t, 0)) (v : D) :
    (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, Z) (TransverseCoordinates.normalCoordinate Ψ) (F x))
      ((mfderiv 𝓘(ℝ, D) 𝓘(ℝ, E) F x) v) ∈ (d.normalFrame Ψ t).range := by
  have hfp : f p = F x := by
    have heq := hgerm.eq_of_nhds
    dsimp only [Function.comp_apply] at heq
    rw [hcp] at heq
    exact heq.trans hx.symm
  have htarget : F x ∈ Ψ.target := by
    have heq := Ψ.map_source' hp
    rwa [hzero p, hfp] at heq
  have hkill := d.normalDerivative_kills_arc_of_strip_germ Ψ ht hk hzero hp hc hcp hcs hgerm
  rw [hfp] at hkill
  exact d.normal_sheet_tangent_mem_frame Ψ hF ht (hx.trans (d.center t)) htarget hkill v

end Wikipedia.SmoothSixDPoincare.StripNormalData
