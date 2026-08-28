import Wikipedia.HopfProblem.DegreeCollapseIntegralChartCoefficient

/-!
# One fixed chart sign for all original compact-supported classes

Original local detection upgrades the pointwise coordinate formula to
equality in every genuine compact-supported relative group of the chart.
The original chart-image equivalence retains the same sign. Applying
this to the constructed ambient primitive supplies a single sign for
all compact supports in any connected supplied chart.
-/

noncomputable section

open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.DegreeCollapse.IntegralChartCoefficient

open SingularMayerVietoris NoExoticSixSphere SupportedRelativeHomology
open IntegralLocalNormalization

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] (n : ℕ) [Fact (Module.finrank ℝ E = (n + 1) + 1)]
  {M : Type} [TopologicalSpace M] [T2Space M]

/-- Local detection turns the fixed chart coefficient into equality
of original supported classes. -/
theorem fromAbsolute_eq_signed_chartClass (a : SingularHomology M (n + 2))
    (e : OpenPartialHomeomorph M E) (ε : ℤ) (hε : ∀ x : e.source, coefficient n a e x = ε)
    (K : Set M) (hK : IsCompact K) (hKs : K ⊆ e.source) :
    fromAbsolute (ModuleCat.of ℤ ℤ) K (n + 2) a =
      ε • IntegralChartOrientation.fundamentalClass n e K hK hKs := by
  apply (IntegralCompactSupport.compact_chart_properties n e K hK hKs).detected
  intro x hx
  let x' : e.source := ⟨x, hKs hx⟩
  have hc : evaluate (ModuleCat.of ℤ ℤ) K x hx (n + 2)
      (IntegralChartOrientation.fundamentalClass n e K hK hKs) =
        (chartMark n e x (hKs hx)).symm 1 :=
    IntegralChartOrientation.fundamentalClass_evaluate n e K hK hKs x hx
  calc
    _ = fromAbsolute (ModuleCat.of ℤ ℤ) {x} (n + 2) a :=
      evaluate_fromAbsolute K x hx (n + 2) a
    _ = coefficient n a e x' • (chartMark n e x (hKs hx)).symm 1 :=
      localization_eq_coefficient_smul n a e x'
    _ = ε • (chartMark n e x (hKs hx)).symm 1 :=
      congrArg (fun k : ℤ => k • (chartMark n e x (hKs hx)).symm 1) (hε x')
    _ = _ := (congrArg (fun z => ε • z) hc.symm).trans
      (map_zsmul (evaluate (ModuleCat.of ℤ ℤ) K x hx (n + 2)) ε
        (IntegralChartOrientation.fundamentalClass n e K hK hKs)).symm

/-- The original chart-image homology map preserves that same integral comparison coefficient. -/
theorem chartImage_fromAbsolute (a : SingularHomology M (n + 2))
    (e : OpenPartialHomeomorph M E) (ε : ℤ) (hε : ∀ x : e.source, coefficient n a e x = ε)
    (K : Set M) (hK : IsCompact K) (hKs : K ⊆ e.source) :
    IntegralChartOrientation.supportEquiv n e K hK hKs
        (fromAbsolute (ModuleCat.of ℤ ℤ) K (n + 2) a) =
      ε • IntegralEuclideanOrientation.fundamentalClass E n (e '' K)
        (IntegralChartOrientation.image_compact e K hK hKs).isBounded := by
  let F := IntegralChartOrientation.supportEquiv n e K hK hKs
  have hf : F (IntegralChartOrientation.fundamentalClass n e K hK hKs) =
      IntegralEuclideanOrientation.fundamentalClass E n (e '' K)
        (IntegralChartOrientation.image_compact e K hK hKs).isBounded := F.apply_symm_apply _
  exact (congrArg F (fromAbsolute_eq_signed_chartClass n a e ε hε K hK hKs)).trans
    ((map_zsmul F ε (IntegralChartOrientation.fundamentalClass n e K hK hKs)).trans
      (congrArg (fun z => ε • z) hf))

/-- Primitivity and connectedness supply a single sign valid for every compact support. -/
theorem exists_sign_for_supported_classes (a : SingularHomology M (n + 2))
    (ha : IntegralManifoldFundamentalClass.IsFundamental (n + 2) a)
    (e : OpenPartialHomeomorph M E) [PreconnectedSpace e.source] :
    ∃ ε : ℤ, (ε = 1 ∨ ε = -1) ∧ ∀ (K : Set M) (hK : IsCompact K) (hKs : K ⊆ e.source),
      fromAbsolute (ModuleCat.of ℤ ℤ) K (n + 2) a =
        ε • IntegralChartOrientation.fundamentalClass n e K hK hKs := by
  obtain ⟨ε, hε, hc⟩ := exists_sign n a ha e
  exact ⟨ε, hε, fun K hK hKs => fromAbsolute_eq_signed_chartClass n a e ε hc K hK hKs⟩

/-- The same single sign works simultaneously on all original compact chart images. -/
theorem exists_sign_for_chart_images (a : SingularHomology M (n + 2))
    (ha : IntegralManifoldFundamentalClass.IsFundamental (n + 2) a)
    (e : OpenPartialHomeomorph M E) [PreconnectedSpace e.source] :
    ∃ ε : ℤ, (ε = 1 ∨ ε = -1) ∧ ∀ (K : Set M) (hK : IsCompact K) (hKs : K ⊆ e.source),
      IntegralChartOrientation.supportEquiv n e K hK hKs
          (fromAbsolute (ModuleCat.of ℤ ℤ) K (n + 2) a) =
        ε • IntegralEuclideanOrientation.fundamentalClass E n (e '' K)
          (IntegralChartOrientation.image_compact e K hK hKs).isBounded := by
  obtain ⟨ε, hε, hc⟩ := exists_sign n a ha e
  exact ⟨ε, hε, fun K hK hKs => chartImage_fromAbsolute n a e ε hc K hK hKs⟩

end Wikipedia.HopfProblem.DegreeCollapse.IntegralChartCoefficient

namespace Wikipedia.HopfProblem.DegreeCollapse.IntegralManifoldFundamentalClass

open NoExoticSixSphere SupportedRelativeHomology

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] (n : ℕ) [Fact (Module.finrank ℝ E = (n + 2) + 1)]
  (M : Type) [TopologicalSpace M] [T2Space M] [ChartedSpace E M] [CompactSpace M]
  [IsManifold 𝓘(ℝ, E) ∞ M] [SimplyConnectedSpace M]
  (e : OpenPartialHomeomorph M E) [PreconnectedSpace e.source]

/-- The constructed ambient primitive needs no supplied comparison sign on a connected chart. -/
theorem exists_chart_sign :
    ∃ ε : ℤ, (ε = 1 ∨ ε = -1) ∧ ∀ (K : Set M) (hK : IsCompact K) (hKs : K ⊆ e.source),
      supportedClass (E := E) n M K =
        ε • IntegralChartOrientation.fundamentalClass (n + 1) e K hK hKs :=
  IntegralChartCoefficient.exists_sign_for_supported_classes (n + 1)
    (fundamentalClass (E := E) n M) (fundamentalClass_isFundamental (E := E) n M) e

theorem exists_chart_image_sign :
    ∃ ε : ℤ, (ε = 1 ∨ ε = -1) ∧ ∀ (K : Set M) (hK : IsCompact K) (hKs : K ⊆ e.source),
      IntegralChartOrientation.supportEquiv (n + 1) e K hK hKs
          (supportedClass (E := E) n M K) =
        ε • IntegralEuclideanOrientation.fundamentalClass E (n + 1) (e '' K)
          (IntegralChartOrientation.image_compact e K hK hKs).isBounded :=
  IntegralChartCoefficient.exists_sign_for_chart_images (n + 1)
    (fundamentalClass (E := E) n M) (fundamentalClass_isFundamental (E := E) n M) e

end Wikipedia.HopfProblem.DegreeCollapse.IntegralManifoldFundamentalClass
