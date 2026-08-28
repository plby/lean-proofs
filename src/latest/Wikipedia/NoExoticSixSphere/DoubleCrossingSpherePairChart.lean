import Wikipedia.NoExoticSixSphere.DoubleCrossingSpherePairAlignment
import Wikipedia.NoExoticSixSphere.SphereNativeDerivativeCoordinates

/-!
# The embedded two-crossing reference pair in an original manifold chart

The actual partial diffeomorphism preserves injectivity, native immersion,
and both transverse crossings. Both center fibers are unique, and the
intersection count is still exactly two. These are the input conditions
needed for the checked globally clean resolution construction.
-/

noncomputable section

open Set Function Metric
open scoped Manifold ContDiff

namespace NoExoticSixSphere.DoubleCrossingSpherePair

open GLOrthonormalization SphereSumNeck

variable {M : Type*} [TopologicalSpace M] [ChartedSpace (Vector 6) M]
  (Φ : PartialDiffeomorph 𝓘(ℝ, Vector 3 × Vector 3) (𝓡 6)
    (Vector 3 × Vector 3) M ∞)
  (hball : closedBall (0 : Vector 3 × Vector 3) 2 ⊆ Φ.source)

include hball

theorem alignedLeft_mem_source (x : Sphere 3) : alignedLeft x ∈ Φ.source :=
  hball (mem_closedBall_zero_iff.mpr (norm_alignedLeft_le_two x))

theorem alignedRight_mem_source (x : Sphere 3) : alignedRight x ∈ Φ.source :=
  hball (mem_closedBall_zero_iff.mpr (norm_alignedRight_le_two x))

theorem localDiffeomorph_chart_left (x : Sphere 3) :
    IsLocalDiffeomorphAt 𝓘(ℝ, Vector 3 × Vector 3) (𝓡 6) ∞ Φ (alignedLeft x) :=
  ⟨Φ, alignedLeft_mem_source Φ hball x, fun _ _ ↦ rfl⟩

theorem localDiffeomorph_chart_right (x : Sphere 3) :
    IsLocalDiffeomorphAt 𝓘(ℝ, Vector 3 × Vector 3) (𝓡 6) ∞ Φ (alignedRight x) :=
  ⟨Φ, alignedRight_mem_source Φ hball x, fun _ _ ↦ rfl⟩

theorem contMDiff_chart_left : ContMDiff (𝓡 3) (𝓡 6) ∞ (Φ ∘ alignedLeft) := by
  intro x
  exact (localDiffeomorph_chart_left Φ hball x).contMDiffAt.comp x (contMDiff_alignedLeft x)

theorem contMDiff_chart_right : ContMDiff (𝓡 3) (𝓡 6) ∞ (Φ ∘ alignedRight) := by
  intro x
  exact (localDiffeomorph_chart_right Φ hball x).contMDiffAt.comp x (contMDiff_alignedRight x)

def chartLeft : C(Sphere 3, M) := ⟨Φ ∘ alignedLeft, (contMDiff_chart_left Φ hball).continuous⟩

def chartRight : C(Sphere 3, M) := ⟨Φ ∘ alignedRight, (contMDiff_chart_right Φ hball).continuous⟩

def chartDerivative (z : Vector 3 × Vector 3) : (Vector 3 × Vector 3) →L[ℝ] Vector 6 :=
  mfderiv 𝓘(ℝ, Vector 3 × Vector 3) (𝓡 6) Φ z

theorem nativeDerivative_chartLeft (x : Sphere 3) :
    nativeSphereDerivative (chartLeft Φ hball) x =
      (chartDerivative Φ (alignedLeft x)).comp
        (mfderiv (𝓡 3) 𝓘(ℝ, Vector 3 × Vector 3) alignedLeft x) :=
  mfderiv_comp (f := alignedLeft) (g := Φ) x
    ((localDiffeomorph_chart_left Φ hball x).mdifferentiableAt (by simp))
    (contMDiff_alignedLeft.mdifferentiableAt (by simp))

theorem nativeDerivative_chartRight (x : Sphere 3) :
    nativeSphereDerivative (chartRight Φ hball) x =
      (chartDerivative Φ (alignedRight x)).comp
        (mfderiv (𝓡 3) 𝓘(ℝ, Vector 3 × Vector 3) alignedRight x) :=
  mfderiv_comp (f := alignedRight) (g := Φ) x
    ((localDiffeomorph_chart_right Φ hball x).mdifferentiableAt (by simp))
    (contMDiff_alignedRight.mdifferentiableAt (by simp))

theorem injective_mfderiv_chartLeft (x : Sphere 3) :
    Injective (mfderiv (𝓡 3) (𝓡 6) (chartLeft Φ hball) x) := by
  change Injective (nativeSphereDerivative (chartLeft Φ hball) x)
  rw [nativeDerivative_chartLeft Φ hball]
  exact ((localDiffeomorph_chart_left Φ hball x).mfderivToContinuousLinearEquiv
    (by simp)).injective.comp (injective_mfderiv_alignedLeft x)

theorem injective_mfderiv_chartRight (x : Sphere 3) :
    Injective (mfderiv (𝓡 3) (𝓡 6) (chartRight Φ hball) x) := by
  change Injective (nativeSphereDerivative (chartRight Φ hball) x)
  rw [nativeDerivative_chartRight Φ hball]
  exact ((localDiffeomorph_chart_right Φ hball x).mfderivToContinuousLinearEquiv
    (by simp)).injective.comp (injective_mfderiv_alignedRight x)

theorem injective_chartLeft : Injective (chartLeft Φ hball) := by
  intro x y h
  exact injective_alignedLeft (Φ.injOn
    (alignedLeft_mem_source Φ hball x) (alignedLeft_mem_source Φ hball y) h)

theorem injective_chartRight : Injective (chartRight Φ hball) := by
  intro x y h
  exact injective_alignedRight (Φ.injOn
    (alignedRight_mem_source Φ hball x) (alignedRight_mem_source Φ hball y) h)

theorem chart_coincidence_iff (x y : Sphere 3) :
    chartLeft Φ hball x = chartRight Φ hball y ↔ alignedLeft x = alignedRight y := by
  constructor
  · exact Φ.injOn (alignedLeft_mem_source Φ hball x) (alignedRight_mem_source Φ hball y)
  · exact congrArg Φ

theorem chart_pairTransverse :
    NativeSpherePairTransverse (chartLeft Φ hball) (chartRight Φ hball) := by
  intro x y h
  have hxy := (chart_coincidence_iff Φ hball x y).mp h
  have hD : Surjective (chartDerivative Φ (alignedLeft x)) :=
    ((localDiffeomorph_chart_left Φ hball x).mfderivToContinuousLinearEquiv (by simp)).surjective
  unfold NativeSphereTransverseAt
  rw [nativeDerivative_chartLeft Φ hball, nativeDerivative_chartRight Φ hball, ← hxy]
  intro w
  obtain ⟨z, hz⟩ := hD w
  obtain ⟨p, hp⟩ := aligned_pairTransverse x y hxy z
  refine ⟨p, ?_⟩
  change chartDerivative Φ (alignedLeft x)
      (mfderiv (𝓡 3) 𝓘(ℝ, Vector 3 × Vector 3) alignedLeft x p.1) +
    chartDerivative Φ (alignedLeft x)
      (mfderiv (𝓡 3) 𝓘(ℝ, Vector 3 × Vector 3) alignedRight y p.2) = w
  exact (map_add (chartDerivative Φ (alignedLeft x)) _ _).symm.trans
    ((congrArg (chartDerivative Φ (alignedLeft x)) hp).trans hz)

theorem chartLeft_selfTransverse : NativeSphereSelfTransverse (chartLeft Φ hball) :=
  fun _ _ hne he ↦ (hne (injective_chartLeft Φ hball he)).elim

theorem chartRight_selfTransverse : NativeSphereSelfTransverse (chartRight Φ hball) :=
  fun _ _ hne he ↦ (hne (injective_chartRight Φ hball he)).elim

theorem chart_intersectionPairs_ncard :
    (MapIntersections.pairs (chartLeft Φ hball) (chartRight Φ hball)).ncard = 2 := by
  have h : MapIntersections.pairs (chartLeft Φ hball) (chartRight Φ hball) =
      MapIntersections.pairs alignedLeft alignedRight := by
    ext p
    exact chart_coincidence_iff Φ hball p.1 p.2
  rw [h, aligned_intersectionPairs_ncard]

theorem chart_intersectionParity_zero :
    MapIntersections.parity (chartLeft Φ hball) (chartRight Φ hball) = 0 := by
  rw [MapIntersections.parity, chart_intersectionPairs_ncard Φ hball]
  decide

theorem chartLeft_center : chartLeft Φ hball (sourceChart 0) = Φ 0 :=
  congrArg Φ alignedLeft_center

theorem chartRight_center : chartRight Φ hball (sourceChart 0) = Φ 0 :=
  congrArg Φ alignedRight_center

theorem range_chartLeft : range (chartLeft Φ hball) ⊆ Φ.target := by
  rintro _ ⟨x, rfl⟩
  exact Φ.map_source (alignedLeft_mem_source Φ hball x)

theorem range_chartRight : range (chartRight Φ hball) ⊆ Φ.target := by
  rintro _ ⟨x, rfl⟩
  exact Φ.map_source (alignedRight_mem_source Φ hball x)

end NoExoticSixSphere.DoubleCrossingSpherePair
