import Wikipedia.SmoothSixDPoincare.SphereOutwardClass
import Wikipedia.SmoothSixDPoincare.MorseCollapsePointClasses
import Wikipedia.SmoothSixDPoincare.MorseCollapseBoundarySigns

/-!
# The original collapse homology is multiplication by the signed belt count

The constructed disjoint-cover sum uses the actual local source classes.
Their outward normalization is the same fixed global isomorphism at every
point. The proved local boundary signs therefore sum to the original signed
intersection count, with no degree or orientation formula as a hypothesis.
-/

noncomputable section

open Set Metric ContinuousMap
open scoped ContDiff Manifold

namespace Wikipedia.SmoothSixDPoincare.ManifoldMorse.MorseSurgeryData

open Wikipedia.HopfProblem.SphereHomology
  Wikipedia.HopfProblem.SingularMayerVietoris

local instance (n : ℕ) :
    Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin (n + 3))) = (n + 2) + 1) := ⟨by simp⟩

variable {E M : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ} {p : M} (d : MorseSurgeryData E f p)

open Classical in
theorem collapseLocalClass_eq_outward (n : ℕ)
    (j : (ℝ × d.chart.NegativeCoordinates) ≃L[ℝ] Hemisphere.Ambient ((n + 2) + 1))
    (B : EuclideanSpace ℝ (Fin (n + 2)) ≃L[ℝ] d.chart.NegativeCoordinates)
    (g : C(Hemisphere.Sphere (n + 2), d.UpperLevel))
    (D : d.CollapseNeighborhoods (n + 2) g) [Fintype (d.beltIntersectionPoints (n + 2) g)]
    (k : ℕ) (a : SingularHomology (UnitSphere (n + 2)) (k + 2))
    (i : d.beltIntersectionPoints (n + 2) g) :
    d.collapseLocalClass (n + 2) g D (k + 1) a i =
      (SignType.sign (SphereNormalCoordinates.chartJacobian
        (NativeParametrization.centered i.val) j B 0) : ℤ) •
          SpherePoint.outwardClass n j B k a := by
  rw [d.collapseLocalClass_singlePoint]
  exact SpherePoint.pointConnecting_eq_outward n j B i.val (D.data i) k a

variable [FiniteDimensional ℝ E] [T2Space M] [IsManifold 𝓘(ℝ, E) ∞ M]
  (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)

omit [T2Space M] in
open Classical in
theorem collapseLocalBoundary_outward (q n : ℕ)
    [Fact (Module.finrank ℝ d.chart.PositiveCoordinates = q + 1)]
    (hdim : Module.finrank ℝ d.chart.NegativeCoordinates = n + 2)
    (j : (ℝ × d.chart.NegativeCoordinates) ≃L[ℝ] Hemisphere.Ambient ((n + 2) + 1))
    (B : EuclideanSpace ℝ (Fin (n + 2)) ≃L[ℝ] d.chart.NegativeCoordinates)
    (g : C(Hemisphere.Sphere (n + 2), d.UpperLevel))
    (D : d.CollapseNeighborhoods (n + 2) g) [Fintype (d.beltIntersectionPoints (n + 2) g)] :
    letI := RegularLevel.chartedSpace hf d.upper_regular
    ∀ (_hg : ContMDiff (𝓡 (n + 2)) 𝓘(ℝ, RegularLevel.Model E) ∞ g)
      (_ht : ∀ x y, NativeTransversality.At (𝓡 (n + 2)) (𝓡 q) 𝓘(ℝ, RegularLevel.Model E)
        g d.surgery.beltSphere x y)
      (k : ℕ) (a : SingularHomology (UnitSphere (n + 2)) (k + 2))
      (i : d.beltIntersectionPoints (n + 2) g),
      singularHomologyMap (D.data i).innerBoundary.normalizedMap (k + 1)
        (d.collapseLocalClass (n + 2) g D (k + 1) a i) =
      (d.beltIntersectionSign (n + 2) j g i.val : ℤ) •
        singularHomologyMap (LinearSphereAction.sphereMap B.toContinuousLinearMap B.injective)
          (k + 1) (SpherePoint.outwardClass n j B k a) := by
  let _ := RegularLevel.chartedSpace hf d.upper_regular
  intro hg ht k a i
  rw [d.collapseLocalClass_eq_outward n j B g D k a i]
  exact d.collapseLocalBoundary_homology_sign_of_transverse hf q n hdim j B g hg ht
    i.val i.property (D.linear i) (D.derivative_eq i) (D.data i).innerBoundary k _

omit [FiniteDimensional ℝ E] [T2Space M] [IsManifold 𝓘(ℝ, E) ∞ M] in
open Classical in
theorem beltIntersectionCount_smul (m : ℕ)
    (j : (ℝ × d.chart.NegativeCoordinates) ≃L[ℝ] Hemisphere.Ambient (m + 1))
    (g : Hemisphere.Sphere m → d.UpperLevel) [Fintype (d.beltIntersectionPoints m g)]
    (hfin : (d.beltIntersectionPoints m g).Finite)
    {A : Type*} [AddCommGroup A] (a : A) :
    (∑ i : d.beltIntersectionPoints m g, (d.beltIntersectionSign m j g i.val : ℤ) • a) =
      d.beltIntersectionCount m j g hfin • a := by
  have hcount : (∑ i : d.beltIntersectionPoints m g,
      (d.beltIntersectionSign m j g i.val : ℤ)) = d.beltIntersectionCount m j g hfin :=
    (Finset.sum_subtype hfin.toFinset (fun _ => hfin.mem_toFinset)
      (fun x => (d.beltIntersectionSign m j g x : ℤ))).symm
  exact Finset.sum_smul.symm.trans (congrArg (fun z : ℤ => z • a) hcount)

open Classical in
/-- The original global collapse acts by the actual signed crossing count. -/
theorem collapseSphereConnecting_signed_count (q n : ℕ)
    [Fact (Module.finrank ℝ d.chart.PositiveCoordinates = q + 1)]
    (hdim : Module.finrank ℝ d.chart.NegativeCoordinates = n + 2)
    (j : (ℝ × d.chart.NegativeCoordinates) ≃L[ℝ] Hemisphere.Ambient ((n + 2) + 1))
    (B : EuclideanSpace ℝ (Fin (n + 2)) ≃L[ℝ] d.chart.NegativeCoordinates)
    (g : C(Hemisphere.Sphere (n + 2), d.UpperLevel))
    (D : d.CollapseNeighborhoods (n + 2) g) [Finite (d.beltIntersectionPoints (n + 2) g)] :
    letI := RegularLevel.chartedSpace hf d.upper_regular
    ∀ (_hg : ContMDiff (𝓡 (n + 2)) 𝓘(ℝ, RegularLevel.Model E) ∞ g)
      (_ht : ∀ x y, NativeTransversality.At (𝓡 (n + 2)) (𝓡 q) 𝓘(ℝ, RegularLevel.Model E)
        g d.surgery.beltSphere x y)
      (r : ℝ) (hr : 0 < r) (k : ℕ)
      (a : SingularHomology (UnitSphere (n + 2)) (k + 2)),
      OnePointCover.sphereConnecting r hr (k + 1)
        (singularHomologyMap (d.attachingCollapse hf.continuous (n + 2) g) (k + 2) a) =
          d.beltIntersectionCount (n + 2) j g (Set.toFinite _) •
            singularHomologyMap (LinearSphereAction.sphereMap B.toContinuousLinearMap B.injective)
              (k + 1) (SpherePoint.outwardClass n j B k a) := by
  let _ := RegularLevel.chartedSpace hf d.upper_regular
  let _ : Fintype (d.beltIntersectionPoints (n + 2) g) := Fintype.ofFinite _
  intro hg ht r hr k a
  apply (d.collapseSphereConnecting_sum hf.continuous (n + 2) g D r hr (k + 1) a).trans
  apply Eq.trans (Finset.sum_congr rfl (fun i _ =>
    d.collapseLocalBoundary_outward hf q n hdim j B g D hg ht k a i))
  exact d.beltIntersectionCount_smul (n + 2) j g (Set.toFinite _) _

end Wikipedia.SmoothSixDPoincare.ManifoldMorse.MorseSurgeryData
