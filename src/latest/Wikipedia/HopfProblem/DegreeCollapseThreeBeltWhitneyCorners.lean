import Wikipedia.HopfProblem.DegreeCollapseThreeBeltCornerSigns
import Wikipedia.SmoothSixDPoincare.MorseSignedIntersections
import Wikipedia.SmoothSixDPoincare.SphereSheetIntersectionSigns

/-!
# Actual three-belt intersection signs are the retained Whitney corner signs

The fixed original belt normal map and the outward sphere orientation give
the actual finite intersection signs. Recover the sphere's native chart from
the retained clean ambient chart; its orientation factor is constant along
the strip. The fixed normal-model change is accounted for explicitly. Thus
opposite actual signs give exactly the required Whitney framing condition.
-/

noncomputable section

open Set Function
open scoped ContDiff Manifold
open Wikipedia.SmoothSixDPoincare ManifoldMorse

namespace Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M] {f : M → ℝ} {p : M}

theorem opposite_three_beltIntersectionSigns_iff_Whitney_corners
    (D : MorseSurgeryData E f p) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    [Fact (Module.finrank ℝ D.chart.PositiveCoordinates = 3 + 1)]
    (hindex : Module.finrank ℝ D.chart.NegativeCoordinates = 3)
    (r : (ℝ × D.chart.NegativeCoordinates) ≃L[ℝ] Hemisphere.Ambient 4)
    (g : Hemisphere.Sphere 3 → D.UpperLevel)
    {a b : ℝ → D.UpperLevel} {k l : (ℝ × ℝ) → D.UpperLevel} {h : ℝ} :
    letI := RegularLevel.chartedSpace hf D.upper_regular
    ∀ (_hg : ContMDiff (𝓡 3) 𝓘(ℝ, RegularLevel.Model E) ∞ g)
      (_hinj : Injective g)
      (_hi : ∀ x, Injective (mfderiv (𝓡 3) 𝓘(ℝ, RegularLevel.Model E) g x))
      (_ht : ∀ x y, NativeTransversality.At (𝓡 3) (𝓡 3) 𝓘(ℝ, RegularLevel.Model E)
        g D.surgery.beltSphere x y)
      (tube : TubularBigon (E := RegularLevel.Model E)
        (range g) (range D.surgery.beltSphere) a b k l h)
      (d : StripNormalData (EuclideanSpace ℝ (Fin 2)) (EuclideanSpace ℝ (Fin 3))
        (E := RegularLevel.Model E) (range g) k)
      (e : StripNormalData (EuclideanSpace ℝ (Fin 2)) (EuclideanSpace ℝ (Fin 3))
        (E := RegularLevel.Model E) (range D.surgery.beltSphere) l)
      (x₀ x₁ : Hemisphere.Sphere 3),
      g x₀ = d.chart (StripCoordinates.center 0) →
      g x₁ = d.chart (StripCoordinates.center 1) →
      ((D.beltIntersectionSign 3 r g x₀ * D.beltIntersectionSign 3 r g x₁ = -1) ↔
        tube.sheetPairDet d e 0 * tube.sheetPairDet d e 1 < 0) := by
  let _ := RegularLevel.chartedSpace hf D.upper_regular
  let _ : Fact (Module.finrank ℝ (Hemisphere.Ambient 4) = 3 + 1) :=
    ⟨finrank_euclideanSpace_fin⟩
  intro hg hinj hi ht tube d e x₀ x₁ hx₀ hx₁
  let j : (ℝ × EuclideanSpace ℝ (Fin 2)) ≃L[ℝ] D.chart.NegativeCoordinates :=
    ContinuousLinearEquiv.ofFinrankEq (by simp [Module.finrank_prod, hindex])
  let q := nativeThreeBeltSheetNormal D j
  let r' := (ContinuousLinearEquiv.prodCongr (ContinuousLinearEquiv.refl ℝ ℝ) j).trans r
  have hjSmooth : ContMDiff 𝓘(ℝ, D.chart.NegativeCoordinates)
      𝓘(ℝ, ℝ × EuclideanSpace ℝ (Fin 2)) ∞ j.symm := j.symm.contDiff.contMDiff
  have hdata (x : Hemisphere.Sphere 3) (hx : g x ∈ range D.surgery.beltSphere) :
      ContMDiffAt 𝓘(ℝ, RegularLevel.Model E) 𝓘(ℝ, ℝ × EuclideanSpace ℝ (Fin 2)) ∞ q (g x) ∧
      (mfderiv (𝓡 3) 𝓘(ℝ, ℝ × EuclideanSpace ℝ (Fin 2)) (q ∘ g) x).IsInvertible ∧
      SphereNormalCoordinates.normalJacobian r' x
        (mfderiv (𝓡 3) 𝓘(ℝ, ℝ × EuclideanSpace ℝ (Fin 2)) (q ∘ g) x) =
        D.beltIntersectionJacobian 3 r g x := by
    obtain ⟨v, hv⟩ := hx
    have hxO : g x ∈ D.beltNormalDomain := hv ▸ D.belt_mem_normalDomain v
    have hnormal := (D.contMDiffOn_beltNormal hf).contMDiffAt
      (D.isOpen_beltNormalDomain.mem_nhds hxO)
    have hq : ContMDiffAt 𝓘(ℝ, RegularLevel.Model E)
        𝓘(ℝ, ℝ × EuclideanSpace ℝ (Fin 2)) ∞ q (g x) :=
      hjSmooth.contMDiffAt.comp _ hnormal
    let A : EuclideanSpace ℝ (Fin 3) →L[ℝ] D.chart.NegativeCoordinates :=
      mfderiv (𝓡 3) 𝓘(ℝ, D.chart.NegativeCoordinates) (D.beltNormal ∘ g) x
    let B : EuclideanSpace ℝ (Fin 3) →L[ℝ] (ℝ × EuclideanSpace ℝ (Fin 2)) :=
      mfderiv (𝓡 3) 𝓘(ℝ, ℝ × EuclideanSpace ℝ (Fin 2)) (q ∘ g) x
    have hAb : Bijective A :=
      D.bijective_beltNormal_comp_of_transverse hf 3 3 hindex g hg x v hv (ht x v hv)
    have hA : A.IsInvertible :=
      ⟨(LinearEquiv.ofBijective A.toLinearMap hAb).toContinuousLinearEquiv, rfl⟩
    have hJ : mfderiv 𝓘(ℝ, D.chart.NegativeCoordinates)
        𝓘(ℝ, ℝ × EuclideanSpace ℝ (Fin 2)) j.symm (D.beltNormal (g x)) =
        j.symm.toContinuousLinearMap := by
      rw [mfderiv_eq_fderiv]
      exact j.symm.toContinuousLinearMap.fderiv
    have hBA : B = j.symm.toContinuousLinearMap.comp A := by
      change mfderiv (𝓡 3) 𝓘(ℝ, ℝ × EuclideanSpace ℝ (Fin 2))
        (j.symm ∘ (D.beltNormal ∘ g)) x = _
      rw [mfderiv_comp x (hjSmooth.mdifferentiableAt (by simp))
        ((hnormal.comp x hg.contMDiffAt).mdifferentiableAt (by simp))]
      change (mfderiv 𝓘(ℝ, D.chart.NegativeCoordinates)
        𝓘(ℝ, ℝ × EuclideanSpace ℝ (Fin 2)) j.symm (D.beltNormal (g x)) :
          D.chart.NegativeCoordinates →L[ℝ] (ℝ × EuclideanSpace ℝ (Fin 2))).comp A = _
      exact congrArg (fun L : D.chart.NegativeCoordinates →L[ℝ]
        (ℝ × EuclideanSpace ℝ (Fin 2)) => L.comp A) hJ
    refine ⟨hq, ?_, ?_⟩
    · change B.IsInvertible
      rw [hBA]
      exact (show j.symm.toContinuousLinearMap.IsInvertible from ⟨j.symm, rfl⟩).comp hA
    · change SphereNormalCoordinates.normalJacobian r' x B =
        SphereNormalCoordinates.normalJacobian r x A
      rw [hBA]
      exact SphereNormalCoordinates.normalJacobian_change_normal_model r j x A hA
  have hcross (t : ℝ) (ht' : t = 0 ∨ t = 1) (x : Hemisphere.Sphere 3)
      (hx : g x = d.chart (StripCoordinates.center t)) : g x ∈ range D.surgery.beltSphere := by
    have htI : t ∈ Icc (0 : ℝ) 1 := by rcases ht' with rfl | rfl <;> simp
    rw [hx, tube.corner_sheet_charts_coincide d e ht']
    exact (e.sheet _ (e.line htI)).mpr rfl
  obtain ⟨hq₀, hi₀, hJ₀⟩ := hdata x₀ (hcross 0 (Or.inl rfl) x₀ hx₀)
  obtain ⟨hq₁, hi₁, hJ₁⟩ := hdata x₁ (hcross 1 (Or.inr rfl) x₁ hx₁)
  have hsign := SphereNormalCoordinates.opposite_normalJacobians_iff_retained_sheet
    d.chart g hg hinj hi d.sheet d.line (by simp [Module.finrank_prod]) q r'
    x₀ x₁ hx₀ hx₁ hq₀ hq₁ hi₀ hi₁
  rw [hJ₀, hJ₁] at hsign
  exact (D.beltIntersectionSigns_opposite_iff 3 r g x₀ x₁).trans
    (hsign.trans (opposite_three_belt_corners_iff_normal_determinants D hf j tube d e).symm)

end Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation
