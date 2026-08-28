import Wikipedia.HomotopyGroupsOfSpheres.QuaternionicComplexStructureVertexRetractionHomotopy
import Wikipedia.HomotopyGroupsOfSpheres.QuaternionicSecondMinimumRetractionEnergyBand
import Wikipedia.HomotopyGroupsOfSpheres.QuaternionicSecondMinimumPolygonPartition

/-!
# A relative homotopy onto minimum complex-structure polygons

Near the minimum locus, the retraction is connected to the inclusion by
short logarithmic segments inside the complex-structure space. The whole
homotopy stays below the chosen energy cap and fixes every minimum polygon.
Compactness gives a uniform energy sublevel on which this applies.
-/

open Set

namespace Wikipedia.HomotopyGroupsOfSpheres.QuaternionicColumns.ComplexStructurePolygon

open NoExoticSixSphere.GLOrthonormalization ComplexStructures ComplexStructureVertices

variable {n m : ℕ} {M : Type*} [TopologicalSpace M]
variable (a b : ComplexStructures.Space n) (τ : Fin (m + 2) → ℝ)
    (hτ : StrictMono τ) (hzero : τ 0 = 0) (hone : τ (Fin.last (m + 1)) = 1)
    (hanti : (Cayley.relative a b).val.val.val =
      -(1 : Vector (4 * n + 4) →L[ℝ] Vector (4 * n + 4)))
    (hsmall : ∀ P : AnticommutingStructures.Space a, ∀ i : Fin (m + 1),
      ‖(τ i.succ - τ i.castSucc) •
        (Real.pi • (AnticommutingStructures.generatorParameter P).val.val)‖ < ShortLog.radius n)
    (cap : ℝ) (hcap : ((4 * n + 4 : ℕ) : ℝ) * Real.pi ^ 2 < cap)
    (hcompact : IsCompact (energySublevel a b τ cap))

include hτ hzero hone hanti hsmall hcap hcompact

theorem exists_minimum_homotopy_neighborhood :
    ∃ V : Set (ComplexStructureVertices.Space n m),
      IsOpen V ∧ minimumSet a b τ ⊆ V ∧ V ⊆ admissible a b m ∧
      ∀ p : C(M, ComplexStructureVertices.Space n m), (∀ x, p x ∈ V) →
        ∃ q : C(M, ComplexStructureVertices.Space n m), (∀ x, q x ∈ minimumSet a b τ) ∧
          ∃ G : ContinuousMap.HomotopyRel p q (p ⁻¹' minimumSet a b τ),
            ∀ t x, G (t, x) ∈ energySublevel a b τ cap := by
  have hmincompact := isCompact_energySublevel_of_le a b τ hcap.le hcompact
  let r := minimumNeighborhoodRetraction a b τ hτ hzero hone hanti hsmall
  have hr : ∀ u : minimumRetractionDomain a b τ,
      u.1 ∈ minimumSet a b τ → (r u).1 = u.1 := by
    intro u hu
    exact congrArg Subtype.val (minimumNeighborhoodRetraction_eq_self
      a b τ hτ hzero hone hanti hsmall hmincompact ⟨u.1, hu⟩)
  let W := admissible a b m ∩ energy a b τ ⁻¹' Iio cap
  have hW : IsOpen W := (continuousOn_energy a b τ).isOpen_inter_preimage
    (isOpen_admissible a b m) isOpen_Iio
  have hminW : minimumSet a b τ ⊆ W := by
    intro v hv
    exact ⟨hv.1, by change energy a b τ v < cap; rw [hv.2]; exact hcap⟩
  obtain ⟨V, hV, hminV, hVU, hhom⟩ :=
    ComplexStructureVertices.exists_retraction_homotopy_neighborhood (M := M)
      (minimumRetractionDomain a b τ) (minimumSet a b τ) W
      (isOpen_minimumRetractionDomain a b τ)
      (minimumSet_subset_retractionDomain a b τ hτ hzero hone hanti hsmall hmincompact)
      r hr hW hminW
  refine ⟨V, hV, hminV, (fun _ hv ↦ (hVU hv).1), ?_⟩
  intro p hp
  obtain ⟨q, hq, G, hG⟩ := hhom p hp
  exact ⟨q, hq, G, fun t x ↦ ⟨(hG t x).1, (hG t x).2.le⟩⟩

theorem exists_near_minimum_homotopy :
    ∃ δ > 0, ((4 * n + 4 : ℕ) : ℝ) * Real.pi ^ 2 + δ < cap ∧
      ∀ p : C(M, ComplexStructureVertices.Space n m),
        (∀ x, p x ∈ energySublevel a b τ (((4 * n + 4 : ℕ) : ℝ) * Real.pi ^ 2 + δ)) →
        ∃ q : C(M, ComplexStructureVertices.Space n m), (∀ x, q x ∈ minimumSet a b τ) ∧
          ∃ G : ContinuousMap.HomotopyRel p q (p ⁻¹' minimumSet a b τ),
            ∀ t x, G (t, x) ∈ energySublevel a b τ cap := by
  obtain ⟨V, hV, hminV, _, hhom⟩ := exists_minimum_homotopy_neighborhood (M := M)
    a b τ hτ hzero hone hanti hsmall cap hcap hcompact
  obtain ⟨δ, hδ, htop, hsub⟩ := exists_near_minimum_sublevel_in_open
    a b τ hτ hzero hone hanti cap hcap hcompact V hV hminV
  exact ⟨δ, hδ, htop, fun p hp ↦ hhom p (fun x ↦ hsub (hp x))⟩

omit hτ hzero hone hanti hsmall hcap hcompact in
/-- A sufficiently fine uniform partition supplies all geometric hypotheses
for the relative near-minimum homotopy, for every antipodal endpoint pair. -/
theorem exists_partition_with_near_minimum_homotopy (n : ℕ) (cap : ℝ)
    (hcap : ((4 * n + 4 : ℕ) : ℝ) * Real.pi ^ 2 < cap) (N : ℕ) :
    ∃ m : ℕ, N ≤ m ∧ ∀ a b : ComplexStructures.Space n,
      (Cayley.relative a b).val.val.val =
        -(1 : Vector (4 * n + 4) →L[ℝ] Vector (4 * n + 4)) →
      ∃ δ > 0, ((4 * n + 4 : ℕ) : ℝ) * Real.pi ^ 2 + δ < cap ∧
        ∀ p : C(M, ComplexStructureVertices.Space n m),
          (∀ x, p x ∈ energySublevel a b (NoExoticSixSphere.UniformTimePartition.time m)
            (((4 * n + 4 : ℕ) : ℝ) * Real.pi ^ 2 + δ)) →
          ∃ q : C(M, ComplexStructureVertices.Space n m),
            (∀ x, q x ∈ minimumSet a b (NoExoticSixSphere.UniformTimePartition.time m)) ∧
            ∃ G : ContinuousMap.HomotopyRel p q
              (p ⁻¹' minimumSet a b (NoExoticSixSphere.UniformTimePartition.time m)),
              ∀ t x, G (t, x) ∈
                energySublevel a b (NoExoticSixSphere.UniformTimePartition.time m) cap := by
  obtain ⟨m, hNm, hlevels, hsmall⟩ := exists_minimum_partition n cap N
  refine ⟨m, hNm, ?_⟩
  intro a b hanti
  exact exists_near_minimum_homotopy (M := M)
    a b (NoExoticSixSphere.UniformTimePartition.time m)
    (NoExoticSixSphere.UniformTimePartition.strictMono_time m)
    (NoExoticSixSphere.UniformTimePartition.time_zero m)
    (NoExoticSixSphere.UniformTimePartition.time_last m) hanti (hsmall a)
    cap hcap (hlevels a b cap le_rfl)

end Wikipedia.HomotopyGroupsOfSpheres.QuaternionicColumns.ComplexStructurePolygon
