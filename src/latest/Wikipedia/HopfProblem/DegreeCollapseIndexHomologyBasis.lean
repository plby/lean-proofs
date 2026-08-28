import Wikipedia.SmoothSixDPoincare.MorseIndexTwoBasisExtension

/-!+# A native handle adds its actual integral collapse coordinate

For an index k+2 handle with zero lower H(k+1), the actual collapse map
gives a split rank-one extension in degree k+2. The old sublevel map and
the new collapse coordinate are retained by the constructed equivalence.
The case k=1 will build a coherent H3 basis along the middle-only system.
-/

noncomputable section

open Set Metric Function Topology ContinuousMap
open Wikipedia.SmoothSixDPoincare ManifoldMorse

namespace Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation.MiddleBasis

open SingularMayerVietoris

variable {E M : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [T2Space M] {f : M → ℝ} {p : M}
  (d : MorseSurgeryData E f p) (k : ℕ)

def collapseModel (hindex : Module.finrank ℝ d.chart.NegativeCoordinates = k + 2) :
    EuclideanSpace ℝ (Fin (k + 2)) ≃L[ℝ] d.chart.NegativeCoordinates :=
  ContinuousLinearEquiv.ofFinrankEq (by simp [hindex])

def collapseCoordinate (hf : Continuous f)
    (hindex : Module.finrank ℝ d.chart.NegativeCoordinates = k + 2) :
    SingularHomology {y : M // f y ≤ f p + d.radius ^ 2} (k + 2) →ₗ[ℤ] ℤ :=
  (SpherePoint.targetCountMark k (collapseModel d k hindex)).toLinearMap.comp
    (singularHomologyMap (d.upperCollapseMap hf) (k + 2))

theorem coordinate_surjective (hf : Continuous f)
    (hindex : Module.finrank ℝ d.chart.NegativeCoordinates = k + 2)
    [Subsingleton (SingularHomology {y : M // f y ≤ f p - d.radius ^ 2} (k + 1))] :
    Surjective (collapseCoordinate d k hf hindex) :=
  (SpherePoint.targetCountMark k (collapseModel d k hindex)).surjective.comp
    (d.upperCollapse_surjective_of_lower hf k)

theorem coordinate_kernel (hf : Continuous f)
    (hindex : Module.finrank ℝ d.chart.NegativeCoordinates = k + 2) :
    LinearMap.ker (collapseCoordinate d k hf hindex) =
      LinearMap.range (d.lowerRealizationHomologyMap (k + 2)) := by
  rw [← d.upperCollapse_homology_kernel hf (k + 1)]
  ext a
  let C := SpherePoint.targetCountMark k (collapseModel d k hindex)
  change C (singularHomologyMap (d.upperCollapseMap hf) (k + 2) a) = 0 ↔
    singularHomologyMap (d.upperCollapseMap hf) (k + 2) a = 0
  constructor
  · intro h
    exact C.injective (h.trans (map_zero C).symm)
  · intro h
    rw [h, map_zero]

theorem lowerRealization_injective (hf : Continuous f)
    (hindex : Module.finrank ℝ d.chart.NegativeCoordinates = k + 2) :
    Injective (d.lowerRealizationHomologyMap (k + 2)) := by
  let : Subsingleton (SingularHomology (sphere (0 : d.chart.NegativeCoordinates) 1) (k + 2)) :=
    d.attachingHomology_subsingleton_of_index (k + 2) (by omega) (by omega) (by omega)
  apply LinearMap.ker_eq_bot.mp
  rw [← d.morse_exact_at_lower hf (k + 2) (by omega)]
  apply LinearMap.range_eq_bot.mpr
  apply LinearMap.ext
  intro a
  change d.coreBoundaryHomologyMap (k + 2) a = 0
  rw [Subsingleton.elim a 0, map_zero]

theorem exists_homology_split (hf : Continuous f)
    (hindex : Module.finrank ℝ d.chart.NegativeCoordinates = k + 2)
    [Subsingleton (SingularHomology {y : M // f y ≤ f p - d.radius ^ 2} (k + 1))] :
    ∃ H : (SingularHomology {y : M // f y ≤ f p - d.radius ^ 2} (k + 2) × ℤ) ≃ₗ[ℤ]
        SingularHomology {y : M // f y ≤ f p + d.radius ^ 2} (k + 2),
      (∀ a, H (a, 0) = d.lowerRealizationHomologyMap (k + 2) a) ∧
        ∀ z, collapseCoordinate d k hf hindex (H z) = z.2 := by
  obtain ⟨H, hH, hcoord⟩ :=
    HomologyTransport.exists_add_split_rank_one_extension (d.lowerRealizationHomologyMap (k + 2))
      (collapseCoordinate d k hf hindex) (lowerRealization_injective d k hf hindex)
      (coordinate_surjective d k hf hindex) (coordinate_kernel d k hf hindex)
  exact ⟨H.toIntLinearEquiv, hH, hcoord⟩

theorem exists_basis_extension (hf : Continuous f)
    (hindex : Module.finrank ℝ d.chart.NegativeCoordinates = k + 2)
    [Subsingleton (SingularHomology {y : M // f y ≤ f p - d.radius ^ 2} (k + 1))]
    (n : ℕ)
    (e : (Fin n → ℤ) ≃ₗ[ℤ] SingularHomology {y : M // f y ≤ f p - d.radius ^ 2} (k + 2)) :
    ∃ H : (Fin (n + 1) → ℤ) ≃ₗ[ℤ]
        SingularHomology {y : M // f y ≤ f p + d.radius ^ 2} (k + 2),
      (∀ v, H (Fin.cons 0 v) = d.lowerRealizationHomologyMap (k + 2) (e v)) ∧
        ∀ v, collapseCoordinate d k hf hindex (H v) = v 0 := by
  obtain ⟨H, hH, hcoord⟩ := exists_homology_split d k hf hindex
  let G := (HomologyTransport.integerCoordinateSplit n).trans
    ((e.toAddEquiv.prodCongr (AddEquiv.refl ℤ)).trans H.toAddEquiv)
  refine ⟨G.toIntLinearEquiv, ?_, ?_⟩
  · intro v
    exact hH (e v)
  · intro v
    exact hcoord (e (fun i => v i.succ), v 0)

end Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation.MiddleBasis
