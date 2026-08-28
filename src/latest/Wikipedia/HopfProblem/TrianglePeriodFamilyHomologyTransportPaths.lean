import Wikipedia.HopfProblem.TrianglePeriodFamilyHomologyTransportMarking
import Wikipedia.HopfProblem.TrianglePeriodFamilyHomologyTransportFunctor

/-!
# Higher-homology transport along projected upstairs paths

The actual fibre marking is constant along a path lifted between its two
chosen upstairs endpoints. This proves flatness of the higher-homology
marking on the covering space, not merely the action of based loops.
-/

noncomputable section

namespace Wikipedia.HopfProblem.TrianglePeriodFamily.Data

open SpecialPeriods SingularMayerVietoris PeriodTorusHigherHomology

variable {V B : Type} [NormedAddCommGroup V] [NormedSpace ℂ V]
  [TopologicalSpace B] [ChartedSpace V B] [MulAction TriangleGroup B]
  (D : TrianglePeriodFamily.Data V B)
  (hq : IsQuotientCoveringMap D.baseQuotient TriangleGroup)

/-- With the actual lifted endpoint as final marking, fibre transport
keeps the real torus coordinate unchanged. -/
theorem transport_flatFibreHomeomorph_of_endpoint (b c : B)
    (γ : Path.Homotopic.Quotient (D.baseQuotient b) (D.baseQuotient c))
    (hγ : (hq.isCoveringMap.monodromy γ ⟨b, rfl⟩ : B) = c) (f : RealTorus₄) :
    D.transport hq γ (D.flatFibreHomeomorph hq b f) = D.flatFibreHomeomorph hq c f := by
  have hin : D.flatFibreHomeomorph hq b f = ⟨D.quotient (b, f), rfl⟩ :=
    Subtype.ext (D.flatFibreHomeomorph_coe hq b f)
  apply Subtype.ext
  rw [hin, D.flatFibreHomeomorph_coe]
  exact (D.transport_apply_quotient hq γ b rfl f).trans
    (congrArg (fun d => D.quotient (d, f)) hγ)

/-- The actual endpoint identity induces a commuting square in every homology degree. -/
theorem transport_inducedHomologyDegree_flat_of_endpoint (n : ℕ) (b c : B)
    (γ : Path.Homotopic.Quotient (D.baseQuotient b) (D.baseQuotient c))
    (hγ : (hq.isCoveringMap.monodromy γ ⟨b, rfl⟩ : B) = c)
    (a : SingularHomology RealTorus₄ n) :
    singularHomologyMap (D.transport hq γ :
      C(D.projection ⁻¹' {D.baseQuotient b}, D.projection ⁻¹' {D.baseQuotient c})) n
        (singularHomologyMap (D.flatFibreHomeomorph hq b :
          C(RealTorus₄, D.projection ⁻¹' {D.baseQuotient b})) n a) =
      singularHomologyMap (D.flatFibreHomeomorph hq c :
        C(RealTorus₄, D.projection ⁻¹' {D.baseQuotient c})) n a := by
  have he : (D.transport hq γ :
      C(D.projection ⁻¹' {D.baseQuotient b}, D.projection ⁻¹' {D.baseQuotient c})).comp
        (D.flatFibreHomeomorph hq b : C(RealTorus₄, D.projection ⁻¹' {D.baseQuotient b})) =
      (D.flatFibreHomeomorph hq c : C(RealTorus₄, D.projection ⁻¹' {D.baseQuotient c})) := by
    apply ContinuousMap.ext
    intro f
    exact D.transport_flatFibreHomeomorph_of_endpoint hq b c γ hγ f
  have hh := congrArg (fun f => singularHomologyMap f n) he
  rw [singularHomologyMap_comp] at hh
  exact LinearMap.congr_fun hh a

/-- The second-homology marking is constant along actual lifted paths. -/
theorem transport_singularH2_flat_of_endpoint (b c : B)
    (γ : Path.Homotopic.Quotient (D.baseQuotient b) (D.baseQuotient c))
    (hγ : (hq.isCoveringMap.monodromy γ ⟨b, rfl⟩ : B) = c)
    (a : SingularHomology (D.projection ⁻¹' {D.baseQuotient b}) 2) :
    D.fibreSingularH2Equiv hq c (D.homologyTransportDegree hq 2 γ a) =
      D.fibreSingularH2Equiv hq b a := by
  obtain ⟨a, rfl⟩ := (homeomorphHomologyEquiv (D.flatFibreHomeomorph hq b) 2).surjective a
  change D.fibreSingularH2Equiv hq c
    (singularHomologyMap (D.transport hq γ :
      C(D.projection ⁻¹' {D.baseQuotient b}, D.projection ⁻¹' {D.baseQuotient c})) 2
        (singularHomologyMap (D.flatFibreHomeomorph hq b :
          C(RealTorus₄, D.projection ⁻¹' {D.baseQuotient b})) 2 a)) =
      D.fibreSingularH2Equiv hq b
        (singularHomologyMap (D.flatFibreHomeomorph hq b :
          C(RealTorus₄, D.projection ⁻¹' {D.baseQuotient b})) 2 a)
  rw [D.transport_inducedHomologyDegree_flat_of_endpoint hq 2 b c γ hγ,
    D.fibreSingularH2Equiv_inducedHomology_flat,
    D.fibreSingularH2Equiv_inducedHomology_flat]

/-- The third-homology marking is constant along actual lifted paths. -/
theorem transport_singularH3_flat_of_endpoint (b c : B)
    (γ : Path.Homotopic.Quotient (D.baseQuotient b) (D.baseQuotient c))
    (hγ : (hq.isCoveringMap.monodromy γ ⟨b, rfl⟩ : B) = c)
    (a : SingularHomology (D.projection ⁻¹' {D.baseQuotient b}) 3) :
    D.fibreSingularH3Equiv hq c (D.homologyTransportDegree hq 3 γ a) =
      D.fibreSingularH3Equiv hq b a := by
  obtain ⟨a, rfl⟩ := (homeomorphHomologyEquiv (D.flatFibreHomeomorph hq b) 3).surjective a
  change D.fibreSingularH3Equiv hq c
    (singularHomologyMap (D.transport hq γ :
      C(D.projection ⁻¹' {D.baseQuotient b}, D.projection ⁻¹' {D.baseQuotient c})) 3
        (singularHomologyMap (D.flatFibreHomeomorph hq b :
          C(RealTorus₄, D.projection ⁻¹' {D.baseQuotient b})) 3 a)) =
      D.fibreSingularH3Equiv hq b
        (singularHomologyMap (D.flatFibreHomeomorph hq b :
          C(RealTorus₄, D.projection ⁻¹' {D.baseQuotient b})) 3 a)
  rw [D.transport_inducedHomologyDegree_flat_of_endpoint hq 3 b c γ hγ,
    D.fibreSingularH3Equiv_inducedHomology_flat,
    D.fibreSingularH3Equiv_inducedHomology_flat]

/-- Projecting an actual upstairs path preserves its second-homology marking,
with the lifted endpoint verified by the covering theorem. -/
theorem transport_singularH2_projectedPath {b c : B} (δ : Path.Homotopic.Quotient b c)
    (a : SingularHomology (D.projection ⁻¹' {D.baseQuotient b}) 2) :
    D.fibreSingularH2Equiv hq c
      (D.homologyTransportDegree hq 2 (δ.map ⟨D.baseQuotient, hq.continuous⟩) a) =
      D.fibreSingularH2Equiv hq b a := by
  apply D.transport_singularH2_flat_of_endpoint hq b c
  exact congrArg Subtype.val (hq.isCoveringMap.monodromy_map δ)

/-- Projecting an actual upstairs path preserves its third-homology marking,
without a separate endpoint assumption. -/
theorem transport_singularH3_projectedPath {b c : B} (δ : Path.Homotopic.Quotient b c)
    (a : SingularHomology (D.projection ⁻¹' {D.baseQuotient b}) 3) :
    D.fibreSingularH3Equiv hq c
      (D.homologyTransportDegree hq 3 (δ.map ⟨D.baseQuotient, hq.continuous⟩) a) =
      D.fibreSingularH3Equiv hq b a := by
  apply D.transport_singularH3_flat_of_endpoint hq b c
  exact congrArg Subtype.val (hq.isCoveringMap.monodromy_map δ)

end Wikipedia.HopfProblem.TrianglePeriodFamily.Data
