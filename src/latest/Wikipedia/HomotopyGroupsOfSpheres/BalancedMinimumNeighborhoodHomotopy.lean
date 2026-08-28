import Wikipedia.HomotopyGroupsOfSpheres.BalancedMinimumPolygonPartition
import Wikipedia.HomotopyGroupsOfSpheres.SymmetricUnitaryVertexInterpolation
import Wikipedia.NoExoticSixSphere.CompactEnergyBand

/-!
# Relative deformation of a uniform energy band into minimum constrained polygons

Short logarithmic segments connect the retraction to the inclusion while
fixing every minimum polygon. An open condition on the entire compact time
interval controls the energy throughout the homotopy. Compact sublevels
then supply a uniform band on which the construction applies.
-/

noncomputable section

open scoped Matrix.Norms.Frobenius
open Set

namespace Wikipedia.HomotopyGroupsOfSpheres.QuaternionicSymmetricMatrices.Polygon

open VertexSpace BalancedRealInvolutions ComplexSkewMatrices
open NoExoticSixSphere.FiniteControlledLowering

variable {m : ℕ} {M : Type*} [TopologicalSpace M]
variable (n : ℕ) (τ : Fin (m + 2) → ℝ) (hτ : StrictMono τ)
    (hzero : τ 0 = 0) (hone : τ (Fin.last (m + 1)) = 1)
    (hsmall : ∀ J : BalancedRealInvolutions.Space n, ∀ i : Fin (m + 1),
      ‖(τ i.succ - τ i.castSucc) • imaginaryDirection (minimumGenerator J)‖ <
        CompatibleLog.radius (Index n))
    (cap : ℝ) (hcap : (4 * n : ℝ) * Real.pi ^ 2 < cap)
    (hcompact : IsCompact (energySublevel specialIdentity (antipode n) τ cap))

include hτ hzero hone hcap hcompact

theorem exists_near_minimum_sublevel_in_open (U : Set (VertexSpace.Space (Index n) m))
    (hU : IsOpen U) (hminU : minimumSet n τ ⊆ U) :
    ∃ δ > 0, (4 * n : ℝ) * Real.pi ^ 2 + δ < cap ∧
      energySublevel specialIdentity (antipode n) τ ((4 * n : ℝ) * Real.pi ^ 2 + δ) ⊆ U := by
  obtain ⟨d, hd, hband⟩ := exists_energy_band_in_open (energy specialIdentity (antipode n) τ)
    (energySublevel specialIdentity (antipode n) τ cap) hcompact
    ((continuousOn_energy specialIdentity (antipode n) τ).mono (fun _ hv ↦ hv.1))
    ((4 * n : ℝ) * Real.pi ^ 2) U hU (fun _ hv he ↦ hminU ⟨hv.1, he⟩)
  let δ := min (d / 2) ((cap - (4 * n : ℝ) * Real.pi ^ 2) / 2)
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hδd : δ ≤ d / 2 := min_le_left _ _
  have hδcap : δ ≤ (cap - (4 * n : ℝ) * Real.pi ^ 2) / 2 := min_le_right _ _
  have htop : (4 * n : ℝ) * Real.pi ^ 2 + δ < cap := by linarith
  refine ⟨δ, hδ, htop, ?_⟩
  intro v hv
  have hvcap : v ∈ energySublevel specialIdentity (antipode n) τ cap :=
    ⟨hv.1, hv.2.trans htop.le⟩
  have hlow := antipodal_energy_ge_of_compact_sublevel n τ hτ hzero hone cap hcompact v hvcap
  apply hband v hvcap
  rw [abs_of_nonneg (sub_nonneg.mpr hlow)]
  have := hv.2
  linarith

include hsmall

theorem exists_minimum_homotopy_neighborhood :
    ∃ V : Set (VertexSpace.Space (Index n) m), IsOpen V ∧ minimumSet n τ ⊆ V ∧
      V ⊆ admissible specialIdentity (antipode n) m ∧
      ∀ p : C(M, VertexSpace.Space (Index n) m), (∀ x, p x ∈ V) →
        ∃ q : C(M, VertexSpace.Space (Index n) m), (∀ x, q x ∈ minimumSet n τ) ∧
          ∃ G : ContinuousMap.HomotopyRel p q (p ⁻¹' minimumSet n τ),
            ∀ t x, G (t, x) ∈ energySublevel specialIdentity (antipode n) τ cap := by
  have hmincompact := isCompact_energySublevel_of_le specialIdentity (antipode n) τ
    hcap.le hcompact
  let r := minimumNeighborhoodRetraction n τ hτ hzero hone hsmall
  have hr : ∀ u : minimumRetractionDomain n τ,
      u.val ∈ minimumSet n τ → (r u).val = u.val := by
    intro u hu
    exact congrArg Subtype.val (minimumNeighborhoodRetraction_eq_self
      n τ hτ hzero hone hsmall hmincompact ⟨u.val, hu⟩)
  let W := admissible specialIdentity (antipode n) m ∩
    energy specialIdentity (antipode n) τ ⁻¹' Iio cap
  have hW : IsOpen W := (continuousOn_energy specialIdentity (antipode n) τ).isOpen_inter_preimage
    (isOpen_admissible specialIdentity (antipode n) m) isOpen_Iio
  have hminW : minimumSet n τ ⊆ W := by
    intro v hv
    exact ⟨hv.1, by change energy specialIdentity (antipode n) τ v < cap; rw [hv.2]; exact hcap⟩
  obtain ⟨V, hV, hminV, hVU, hhom⟩ :=
    VertexSpace.exists_retraction_homotopy_neighborhood (M := M)
      (minimumRetractionDomain n τ) (minimumSet n τ) W
      (isOpen_minimumRetractionDomain n τ)
      (minimumSet_subset_retractionDomain n τ hτ hzero hone hsmall hmincompact)
      r hr hW hminW
  refine ⟨V, hV, hminV, (fun _ hv ↦ (hVU hv).1), ?_⟩
  intro p hp
  obtain ⟨q, hq, G, hG⟩ := hhom p hp
  exact ⟨q, hq, G, fun t x ↦ ⟨(hG t x).1, (hG t x).2.le⟩⟩

theorem exists_near_minimum_homotopy :
    ∃ δ > 0, (4 * n : ℝ) * Real.pi ^ 2 + δ < cap ∧
      ∀ p : C(M, VertexSpace.Space (Index n) m),
        (∀ x, p x ∈ energySublevel specialIdentity (antipode n) τ
          ((4 * n : ℝ) * Real.pi ^ 2 + δ)) →
        ∃ q : C(M, VertexSpace.Space (Index n) m), (∀ x, q x ∈ minimumSet n τ) ∧
          ∃ G : ContinuousMap.HomotopyRel p q (p ⁻¹' minimumSet n τ),
            ∀ t x, G (t, x) ∈ energySublevel specialIdentity (antipode n) τ cap := by
  obtain ⟨V, hV, hminV, _, hhom⟩ := exists_minimum_homotopy_neighborhood (M := M)
    n τ hτ hzero hone hsmall cap hcap hcompact
  obtain ⟨δ, hδ, htop, hsub⟩ := exists_near_minimum_sublevel_in_open
    n τ hτ hzero hone cap hcap hcompact V hV hminV
  exact ⟨δ, hδ, htop, fun p hp ↦ hhom p (fun x ↦ hsub (hp x))⟩

omit hτ hzero hone hsmall hcap hcompact in
theorem exists_partition_with_near_minimum_homotopy (n : ℕ) (cap : ℝ)
    (hcap : (4 * n : ℝ) * Real.pi ^ 2 < cap) (lower : ℕ) :
    ∃ m : ℕ, lower ≤ m ∧ ∃ δ > 0, (4 * n : ℝ) * Real.pi ^ 2 + δ < cap ∧
      ∀ p : C(M, VertexSpace.Space (Index n) m),
        (∀ x, p x ∈ energySublevel specialIdentity (antipode n)
          (NoExoticSixSphere.UniformTimePartition.time m) ((4 * n : ℝ) * Real.pi ^ 2 + δ)) →
        ∃ q : C(M, VertexSpace.Space (Index n) m),
          (∀ x, q x ∈ minimumSet n (NoExoticSixSphere.UniformTimePartition.time m)) ∧
          ∃ G : ContinuousMap.HomotopyRel p q
            (p ⁻¹' minimumSet n (NoExoticSixSphere.UniformTimePartition.time m)),
            ∀ t x, G (t, x) ∈ energySublevel specialIdentity (antipode n)
              (NoExoticSixSphere.UniformTimePartition.time m) cap := by
  obtain ⟨m, hm, hsmall, hcompact⟩ := exists_minimum_partition n cap lower
  refine ⟨m, hm, ?_⟩
  exact exists_near_minimum_homotopy (M := M) n (NoExoticSixSphere.UniformTimePartition.time m)
    (NoExoticSixSphere.UniformTimePartition.strictMono_time m)
    (NoExoticSixSphere.UniformTimePartition.time_zero m)
    (NoExoticSixSphere.UniformTimePartition.time_last m) hsmall cap hcap
    (hcompact cap (le_max_left _ _))

end Wikipedia.HomotopyGroupsOfSpheres.QuaternionicSymmetricMatrices.Polygon
