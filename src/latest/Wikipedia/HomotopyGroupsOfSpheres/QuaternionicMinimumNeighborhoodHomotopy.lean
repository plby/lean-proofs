import Wikipedia.HomotopyGroupsOfSpheres.QuaternionicVertexRetractionHomotopy
import Wikipedia.HomotopyGroupsOfSpheres.QuaternionicMinimumRetractionEnergyBand

/-!
# A controlled relative homotopy onto the minimum symplectic polygon locus

Near the minimum set, the actual neighborhood retraction is connected to the
identity by Cayley interpolation. The whole homotopy stays below the chosen
cap. Compactness then supplies an energy sublevel on which this applies.
-/

open Set

namespace Wikipedia.HomotopyGroupsOfSpheres.QuaternionicColumns.Polygon

open NoExoticSixSphere.GLOrthonormalization VertexSpace Exponential

variable {n m : ℕ} {M : Type*} [TopologicalSpace M]
variable (a b : symplecticSubgroup n) (τ : Fin (m + 2) → ℝ)
    (hτ : StrictMono τ) (hzero : τ 0 = 0) (hone : τ (Fin.last (m + 1)) = 1)
    (hanti : (a⁻¹ * b).val.val.val = -(1 : Vector (4 * n + 4) →L[ℝ] Vector (4 * n + 4)))
    (hsmall : ∀ J : ComplexStructures.Space n, ∀ i : Fin (m + 1),
      (τ i.succ - τ i.castSucc) • (Real.pi • J.1) ∈ compatibleTarget n)
    (cap : ℝ) (hcap : ((4 * n + 4 : ℕ) : ℝ) * Real.pi ^ 2 < cap)
    (hcompact : IsCompact (energySublevel a b τ cap))

include hτ hzero hone hanti hsmall hcap hcompact

theorem exists_minimum_homotopy_neighborhood :
    ∃ V : Set (Space n m), IsOpen V ∧ minimumSet a b τ ⊆ V ∧ V ⊆ admissible a b m ∧
      ∀ p : C(M, Space n m), (∀ x, p x ∈ V) →
        ∃ q : C(M, Space n m), (∀ x, q x ∈ minimumSet a b τ) ∧
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
  have hW : IsOpen W := (contMDiffOn_energy a b τ).continuousOn.isOpen_inter_preimage
    (isOpen_admissible a b m) isOpen_Iio
  have hminW : minimumSet a b τ ⊆ W := by
    intro v hv
    exact ⟨hv.1, by change energy a b τ v < cap; rw [hv.2]; exact hcap⟩
  obtain ⟨V, hV, hminV, hVU, hhom⟩ := exists_retraction_homotopy_neighborhood (M := M)
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
      ∀ p : C(M, Space n m),
        (∀ x, p x ∈ energySublevel a b τ (((4 * n + 4 : ℕ) : ℝ) * Real.pi ^ 2 + δ)) →
        ∃ q : C(M, Space n m), (∀ x, q x ∈ minimumSet a b τ) ∧
          ∃ G : ContinuousMap.HomotopyRel p q (p ⁻¹' minimumSet a b τ),
            ∀ t x, G (t, x) ∈ energySublevel a b τ cap := by
  obtain ⟨V, hV, hminV, _, hhom⟩ := exists_minimum_homotopy_neighborhood (M := M)
    a b τ hτ hzero hone hanti hsmall cap hcap hcompact
  obtain ⟨δ, hδ, htop, hsub⟩ := exists_near_minimum_sublevel_in_open
    a b τ hτ hzero hone hanti cap hcap hcompact V hV hminV
  exact ⟨δ, hδ, htop, fun p hp ↦ hhom p (fun x ↦ hsub (hp x))⟩

end Wikipedia.HomotopyGroupsOfSpheres.QuaternionicColumns.Polygon
