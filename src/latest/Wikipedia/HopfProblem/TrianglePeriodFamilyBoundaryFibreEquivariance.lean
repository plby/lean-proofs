import Wikipedia.HopfProblem.TrianglePeriodFamilyBoundaryLiftedHomotopy

/-!
# Fibre equivariance forced by a literal boundary map

Suppose an actual mapping-torus boundary map is written in the actual
regular quotient using a continuous lifted base curve and a continuous
fibre-coordinate map.  Once the base deck relation is proved, freeness of
the actual base covering forces the complete fibre map to obey the same
deck relation.  Thus even a logarithmic gauge need not be replaced or
assigned an additional equivariance hypothesis to descend a base homotopy.
-/

noncomputable section

open Set Topology
open scoped ContinuousMap

namespace Wikipedia.HopfProblem.TrianglePeriodFamily.Boundary

open SpecialPeriods MappingTorus
open SingularMayerVietoris PeriodTorusHigherHomology

attribute [local instance] triangleTorusAction triangleTorusAction_continuous

variable {X : Type} [TopologicalSpace X]
  (D : Data ℂ TriangleRegularPoint) (φ : X ≃ₜ X)

/-- The actual quotient is injective on every fixed marked real-torus fibre. -/
theorem quotient_same_base_injective (z : TriangleRegularPoint) :
    Function.Injective (fun x : RealTorus₄ => D.quotient (z, x)) :=
  DiagonalQuotient.fibreInclusion_injective (F := RealTorus₄)
    triangleRegularProject_covering z

variable (F : C(Torus φ, D.Space)) (L : C(ℝ, TriangleRegularPoint))
  (G : C(ℝ × X, RealTorus₄)) (g : TriangleGroup)
  (hF : ∀ p : ℝ × X, F (mk φ p) = D.quotient (L p.1, G p))
  (hL : ∀ (k : ℤ) t, L (t + k) = (g ^ (-k)) • L t)

include hF hL

/-- The complete fibre-coordinate deck identity follows from the actual
descended boundary map and the free base action. -/
theorem fibreMap_deck_of_actual (k : ℤ) (p : ℝ × X) :
    G (deck φ k p) = (g ^ (-k)) • G p := by
  have hraw : D.quotient (L (p.1 + k), G (deck φ k p)) = D.quotient (L p.1, G p) := by
    calc
      _ = F (mk φ (deck φ k p)) := (hF (deck φ k p)).symm
      _ = F (mk φ p) := congrArg F (mk_deck φ k p)
      _ = _ := hF p
  have hframe : D.quotient (L (p.1 + k), (g ^ (-k)) • G p) =
      D.quotient (L p.1, G p) := by
    rw [hL]
    exact D.quotient_smul (g ^ (-k)) (L p.1, G p)
  exact quotient_same_base_injective D (L (p.1 + k)) (hraw.trans hframe.symm)

/-- The constructed quotient map is the original map on every point,
with fibre equivariance proved from its representatives. -/
theorem familyBoundaryMap_eq_actual :
    familyBoundaryMap D φ L G g hL (fibreMap_deck_of_actual D φ F L G g hF hL) = F := by
  apply ContinuousMap.ext
  intro q
  obtain ⟨p, rfl⟩ := mk_surjective φ q
  exact (hF p).symm

variable (H : C(unitInterval × ℝ, TriangleRegularPoint))
  (hzero : ∀ t, H (0, t) = L t)
  (hH : ∀ (s : unitInterval) (k : ℤ) t, H (s, t + k) = (g ^ (-k)) • H (s, t))

include hzero

/-- The literal original boundary map is homotopic to the endpoint
quotient map, retaining its original full fibre-coordinate function. -/
theorem actualBoundary_homotopic_of_base :
    F.Homotopic
      (familyBoundaryMap D φ (baseHomotopySlice H 1) G g (hH 1)
        (fibreMap_deck_of_actual D φ F L G g hF hL)) := by
  have he : familyBoundaryMap D φ (baseHomotopySlice H 0) G g (hH 0)
      (fibreMap_deck_of_actual D φ F L G g hF hL) = F := by
    apply ContinuousMap.ext
    intro q
    obtain ⟨p, rfl⟩ := mk_surjective φ q
    change D.quotient (H (0, p.1), G p) = F (mk φ p)
    exact (congrArg (fun z => D.quotient (z, G p)) (hzero p.1)).trans (hF p).symm
  exact ⟨(familyBoundaryHomotopy D φ H G g hH
    (fibreMap_deck_of_actual D φ F L G g hF hL)).cast he rfl⟩

/-- The resulting equality concerns the actual singular-homology maps,
not a map chosen solely from its monodromy label. -/
theorem actualBoundary_homology_of_base (n : ℕ) :
    singularHomologyMap F n =
      singularHomologyMap
        (familyBoundaryMap D φ (baseHomotopySlice H 1) G g (hH 1)
          (fibreMap_deck_of_actual D φ F L G g hF hL)) n :=
  homotopic_homologyMap (actualBoundary_homotopic_of_base D φ F L G g hF hL H hzero hH) n

end Wikipedia.HopfProblem.TrianglePeriodFamily.Boundary
