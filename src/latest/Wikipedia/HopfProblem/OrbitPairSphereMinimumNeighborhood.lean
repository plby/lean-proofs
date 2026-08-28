import Wikipedia.HopfProblem.OrbitPairSphereMinimumRetraction
import Wikipedia.HopfProblem.OrbitPairSphereRetractionHomotopy
import Wikipedia.NoExoticSixSphere.CompactEnergyBand

/-!
# A controlled relative deformation near the minimum energy

The explicit minimum retraction and normalized interpolation give a homotopy
on an open neighborhood of the minimum locus, fixed on that locus. Compactness
then places a whole small energy sublevel in this neighborhood. Every time
stays in the original admissible polygon space and below the prescribed cap.
-/

noncomputable section

open Set

namespace Wikipedia.HopfProblem.OrbitPair.SpherePolygonEnergy

open NoExoticSixSphere SphereVertexSpace FiniteControlledLowering

variable {n m : ℕ} {M : Type*} [TopologicalSpace M]

theorem minimum_mesh_of_cap (τ : Fin (m + 2) → ℝ) (hτ : StrictMono τ)
    (cap : ℝ) (hcap : Real.pi ^ 2 ≤ cap)
    (hmesh : ∀ i : Fin (m + 1), cap * (τ i.succ - τ i.castSucc) < Real.pi ^ 2) :
    ∀ i : Fin (m + 1), Real.pi ^ 2 * (τ i.succ - τ i.castSucc) < Real.pi ^ 2 := by
  intro i
  exact (mul_le_mul_of_nonneg_right hcap
    (sub_nonneg.mpr (hτ (show i.castSucc < i.succ by simp)).le)).trans_lt (hmesh i)

variable (a b : Sphere n) (τ : Fin (m + 2) → ℝ)
    (hτ : StrictMono τ) (hzero : τ 0 = 0) (hone : τ (Fin.last (m + 1)) = 1)
    (hanti : b.val = -a.val) (cap : ℝ) (hcap : Real.pi ^ 2 < cap)
    (hmesh : ∀ i : Fin (m + 1), cap * (τ i.succ - τ i.castSucc) < Real.pi ^ 2)

include hτ hzero hone hanti hcap hmesh

theorem exists_near_minimum_sublevel_in_open (U : Set (Space n m))
    (hU : IsOpen U) (hminU : minimumSet a b τ ⊆ U) :
    ∃ δ > 0, Real.pi ^ 2 + δ < cap ∧ energySublevel a b τ (Real.pi ^ 2 + δ) ⊆ U := by
  obtain ⟨d, hd, hband⟩ := exists_energy_band_in_open (energy a b τ)
    (energySublevel a b τ cap) (isCompact_energySublevel a b τ hτ cap hmesh)
    (continuous_energy a b τ).continuousOn (Real.pi ^ 2) U hU
    (fun _ hv he => hminU ⟨hv.1, he⟩)
  let δ := min (d / 2) ((cap - Real.pi ^ 2) / 2)
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hδd : δ ≤ d / 2 := min_le_left _ _
  have hδcap : δ ≤ (cap - Real.pi ^ 2) / 2 := min_le_right _ _
  have htop : Real.pi ^ 2 + δ < cap := by linarith
  refine ⟨δ, hδ, htop, ?_⟩
  intro v hv
  have hvcap : v ∈ energySublevel a b τ cap := ⟨hv.1, hv.2.trans htop.le⟩
  have hlow := antipodal_energy_ge_of_mesh a b τ hτ hzero hone hanti cap hmesh v hvcap.2
  apply hband v hvcap
  rw [abs_of_nonneg (sub_nonneg.mpr hlow)]
  have := hv.2
  linarith

theorem exists_minimum_homotopy_neighborhood (j : Fin m) :
    ∃ V : Set (Space n m), IsOpen V ∧ minimumSet a b τ ⊆ V ∧
      V ⊆ admissible (costDomain n) a b m ∧
      ∀ p : C(M, Space n m), (∀ x, p x ∈ V) →
        ∃ q : C(M, Space n m), (∀ x, q x ∈ minimumSet a b τ) ∧
          ∃ G : ContinuousMap.HomotopyRel p q (p ⁻¹' minimumSet a b τ),
            ∀ t x, G (t, x) ∈ energySublevel a b τ cap := by
  have hminmesh := minimum_mesh_of_cap τ hτ cap hcap.le hmesh
  let r := minimumNeighborhoodRetraction a b τ hτ hzero hone hanti hminmesh j
  have hr : ∀ u : minimumRetractionDomain a b j,
      u.val ∈ minimumSet a b τ → (r u).val = u.val := by
    intro u hu
    exact congrArg Subtype.val
      (minimumNeighborhoodRetraction_eq_self a b τ hτ hzero hone hanti hminmesh j ⟨u.val, hu⟩)
  let W := admissible (costDomain n) a b m ∩ energy a b τ ⁻¹' Iio cap
  have hW : IsOpen W := (isOpen_admissible (costDomain n) a b m).inter
    (isOpen_Iio.preimage (continuous_energy a b τ))
  have hminW : minimumSet a b τ ⊆ W := by
    intro v hv
    exact ⟨hv.1, by change energy a b τ v < cap; rw [hv.2]; exact hcap⟩
  obtain ⟨V, hV, hminV, hVU, hhom⟩ := exists_retraction_homotopy_neighborhood (M := M)
    (minimumRetractionDomain a b j) (minimumSet a b τ) W
    (isOpen_minimumRetractionDomain a b j)
    (minimumSet_subset_retractionDomain a b τ hτ hzero hone hanti hminmesh j)
    r hr hW hminW
  refine ⟨V, hV, hminV, (fun _ hv => (hVU hv).1), ?_⟩
  intro p hp
  obtain ⟨q, hq, G, hG⟩ := hhom p hp
  exact ⟨q, hq, G, fun t x => ⟨(hG t x).1, (hG t x).2.le⟩⟩

theorem exists_near_minimum_homotopy (j : Fin m) :
    ∃ δ > 0, Real.pi ^ 2 + δ < cap ∧
      ∀ p : C(M, Space n m), (∀ x, p x ∈ energySublevel a b τ (Real.pi ^ 2 + δ)) →
        ∃ q : C(M, Space n m), (∀ x, q x ∈ minimumSet a b τ) ∧
          ∃ G : ContinuousMap.HomotopyRel p q (p ⁻¹' minimumSet a b τ),
            ∀ t x, G (t, x) ∈ energySublevel a b τ cap := by
  obtain ⟨V, hV, hminV, _, hhom⟩ := exists_minimum_homotopy_neighborhood (M := M)
    a b τ hτ hzero hone hanti cap hcap hmesh j
  obtain ⟨δ, hδ, htop, hsub⟩ := exists_near_minimum_sublevel_in_open
    a b τ hτ hzero hone hanti cap hcap hmesh V hV hminV
  exact ⟨δ, hδ, htop, fun p hp => hhom p (fun x => hsub (hp x))⟩

end Wikipedia.HopfProblem.OrbitPair.SpherePolygonEnergy
