import Wikipedia.HomotopyGroupsOfSpheres.QuaternionicPartialGradientCoordinates
import Wikipedia.NoExoticSixSphere.PartialGradientSmallCrossing

/-!
# Relative local crossing at a nonminimal symplectic critical polygon

The crossing homotopy consists of actual symplectic polygon vertices. Its
endpoint energy is strictly below the critical energy, the prescribed lower
sublevel parameter set is fixed, and every intermediate polygon is admissible
with energy less than the critical energy plus an arbitrary positive allowance.

This is a local family theorem. It does not yet assemble a comparison across
the entire critical locus.
-/

open Set Module
open scoped ContDiff Manifold Topology

namespace Wikipedia.HomotopyGroupsOfSpheres.QuaternionicColumns.Polygon

open NoExoticSixSphere NoExoticSixSphere.GLOrthonormalization VertexSpace

variable {B H M : Type*} [NormedAddCommGroup B] [NormedSpace ℝ B]
  [FiniteDimensional ℝ B] [TopologicalSpace H] {I : ModelWithCorners ℝ B H}
  [I.Boundaryless] [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [T2Space M] {n m d : ℕ}

include I

theorem exists_local_crossing_of_data_in (a b : symplecticSubgroup n)
    (τ : Fin (m + 2) → ℝ) (v : Space n m)
    {L : (Fin d → ℝ) →L[ℝ] Model n m}
    (C : PartialGradientCoordinates.LocalData (localEnergy a b τ v) L (localAdmissible a b v))
    (N : Set (Space n m)) (hN : IsOpen N) (hvN : v ∈ N)
    (ε : ℝ) (hε : 0 < ε) (hd : finrank ℝ B < d) :
    ∃ V : Set (Space n m), IsOpen V ∧ v ∈ V ∧ V ⊆ admissible a b m ∩ N ∧
      ∃ l k : ℝ, l < k ∧ k < energy a b τ v ∧
        ∀ (p : C(M, Space n m)), (∀ x, p x ∈ V) →
          ∀ (S : Set M), IsCompact S → (∀ x ∈ S, energy a b τ (p x) ≤ l) →
            ∃ q : C(M, Space n m), (∀ x, energy a b τ (q x) < k) ∧
              ∃ G : ContinuousMap.HomotopyRel p q S,
                ∀ t x, G (t, x) ∈ admissible a b m ∧
                  energy a b τ (G (t, x)) < energy a b τ v + ε ∧ G (t, x) ∈ N := by
  have hd' : finrank ℝ B < finrank ℝ (Fin d → ℝ) := by simpa using hd
  obtain ⟨W, hW, hWzero, hWsource, l, k, hlk, hk, hcross⟩ :=
    C.exists_crossing_in_neighborhood (I := I) (M := M) (isOpen_localAdmissible a b v)
      (contDiffOn_localEnergy a b τ v) ((atVertices v).symm ⁻¹' N)
      (hN.preimage (contMDiff_atVertices_symm v).continuous)
      (by change (atVertices v).symm 0 ∈ N; rwa [atVertices_symm_zero]) ε hε hd'
  have hzero : localEnergy a b τ v 0 = energy a b τ v := by
    simp only [localEnergy, atVertices_symm_zero]
  let V := (atVertices v).source ∩ (atVertices v) ⁻¹' W
  have hV : IsOpen V := (atVertices v).isOpen_inter_preimage hW
  have hvV : v ∈ V := ⟨mem_atVertices_source v, by
    change atVertices v v ∈ W
    rw [atVertices_self]
    exact hWzero⟩
  have hVadm : V ⊆ admissible a b m ∩ N := by
    intro z hz
    have hh : (atVertices v).symm (atVertices v z) ∈ admissible a b m ∩ N :=
      ⟨C.source_subset (hWsource hz.2).1, (hWsource hz.2).2⟩
    rwa [(atVertices v).left_inv hz.1] at hh
  refine ⟨V, hV, hvV, hVadm, l, k, hlk, hzero ▸ hk, ?_⟩
  intro p hp S hS hLow
  let p' : C(M, Model n m) := ⟨fun x ↦ atVertices v (p x),
    (atVertices v).continuousOn.comp_continuous p.continuous (fun x ↦ (hp x).1)⟩
  have hp' : ∀ x, p' x ∈ W := fun x ↦ (hp x).2
  have hLow' : ∀ x ∈ S, localEnergy a b τ v (p' x) ≤ l := by
    intro x hx
    change energy a b τ ((atVertices v).symm (atVertices v (p x))) ≤ l
    rw [(atVertices v).left_inv (hp x).1]
    exact hLow x hx
  obtain ⟨q', hq', G', hG'⟩ := hcross p' hp' S hS hLow'
  let inverse : C(Model n m, Space n m) := ⟨(atVertices v).symm,
    (contMDiff_atVertices_symm v).continuous⟩
  have hround : inverse.comp p' = p := by
    exact ContinuousMap.ext (fun x ↦ (atVertices v).left_inv (hp x).1)
  let G := (G'.compContinuousMap inverse).cast hround rfl
  refine ⟨inverse.comp q', hq', G, fun t x ↦ ?_⟩
  have hh := hG' t x
  refine ⟨C.source_subset hh.1, ?_, hh.2.2⟩
  change localEnergy a b τ v (G' (t, x)) < energy a b τ v + ε
  simpa only [hzero] using hh.2.1

theorem exists_local_crossing_of_data (a b : symplecticSubgroup n)
    (τ : Fin (m + 2) → ℝ) (v : Space n m)
    {L : (Fin d → ℝ) →L[ℝ] Model n m}
    (C : PartialGradientCoordinates.LocalData (localEnergy a b τ v) L (localAdmissible a b v))
    (ε : ℝ) (hε : 0 < ε) (hd : finrank ℝ B < d) :
    ∃ V : Set (Space n m), IsOpen V ∧ v ∈ V ∧ V ⊆ admissible a b m ∧
      ∃ l k : ℝ, l < k ∧ k < energy a b τ v ∧
        ∀ (p : C(M, Space n m)), (∀ x, p x ∈ V) →
          ∀ (S : Set M), IsCompact S → (∀ x ∈ S, energy a b τ (p x) ≤ l) →
            ∃ q : C(M, Space n m), (∀ x, energy a b τ (q x) < k) ∧
              ∃ G : ContinuousMap.HomotopyRel p q S,
                ∀ t x, G (t, x) ∈ admissible a b m ∧
                  energy a b τ (G (t, x)) < energy a b τ v + ε := by
  obtain ⟨V, hV, hvV, hVsub, l, k, hlk, hk, hcross⟩ :=
    exists_local_crossing_of_data_in (I := I) (M := M) a b τ v C univ isOpen_univ
      (mem_univ _) ε hε hd
  refine ⟨V, hV, hvV, hVsub.trans inter_subset_left, l, k, hlk, hk, ?_⟩
  intro p hp S hS hLow
  obtain ⟨q, hq, G, hG⟩ := hcross p hp S hS hLow
  exact ⟨q, hq, G, fun t x ↦ ⟨(hG t x).1, (hG t x).2.1⟩⟩

theorem exists_critical_crossing_neighborhood_in (a b : symplecticSubgroup n)
    (τ : Fin (m + 2) → ℝ) (hτ : StrictMono τ)
    (hzero : τ 0 = 0) (hone : τ (Fin.last (m + 1)) = 1)
    (v : Space n m) (hv : v ∈ shortDomain a b m)
    (hcrit : mfderiv 𝓘(ℝ, Model n m) 𝓘(ℝ, ℝ) (energy a b τ) v = 0)
    (hanti : (a⁻¹ * b).val.val.val = -(1 : Vector (4 * n + 4) →L[ℝ] Vector (4 * n + 4)))
    (habove : ((4 * n + 4 : ℕ) : ℝ) * Real.pi ^ 2 < energy a b τ v)
    (N : Set (Space n m)) (hN : IsOpen N) (hvN : v ∈ N)
    (ε : ℝ) (hε : 0 < ε) (hd : finrank ℝ B < n) :
    ∃ V : Set (Space n m), IsOpen V ∧ v ∈ V ∧ V ⊆ admissible a b m ∩ N ∧
      ∃ l k : ℝ, l < k ∧ k < energy a b τ v ∧
        ∀ (p : C(M, Space n m)), (∀ x, p x ∈ V) →
          ∀ (S : Set M), IsCompact S → (∀ x ∈ S, energy a b τ (p x) ≤ l) →
            ∃ q : C(M, Space n m), (∀ x, energy a b τ (q x) < k) ∧
              ∃ G : ContinuousMap.HomotopyRel p q S,
                ∀ t x, G (t, x) ∈ admissible a b m ∧
                  energy a b τ (G (t, x)) < energy a b τ v + ε ∧ G (t, x) ∈ N := by
  obtain ⟨L, -, ⟨C⟩⟩ :=
    exists_partialGradient_coordinates a b τ hτ hzero hone v hv hcrit hanti habove
  exact exists_local_crossing_of_data_in (I := I) a b τ v C N hN hvN ε hε hd

theorem exists_critical_crossing_neighborhood (a b : symplecticSubgroup n)
    (τ : Fin (m + 2) → ℝ) (hτ : StrictMono τ)
    (hzero : τ 0 = 0) (hone : τ (Fin.last (m + 1)) = 1)
    (v : Space n m) (hv : v ∈ shortDomain a b m)
    (hcrit : mfderiv 𝓘(ℝ, Model n m) 𝓘(ℝ, ℝ) (energy a b τ) v = 0)
    (hanti : (a⁻¹ * b).val.val.val = -(1 : Vector (4 * n + 4) →L[ℝ] Vector (4 * n + 4)))
    (habove : ((4 * n + 4 : ℕ) : ℝ) * Real.pi ^ 2 < energy a b τ v)
    (ε : ℝ) (hε : 0 < ε) (hd : finrank ℝ B < n) :
    ∃ V : Set (Space n m), IsOpen V ∧ v ∈ V ∧ V ⊆ admissible a b m ∧
      ∃ l k : ℝ, l < k ∧ k < energy a b τ v ∧
        ∀ (p : C(M, Space n m)), (∀ x, p x ∈ V) →
          ∀ (S : Set M), IsCompact S → (∀ x ∈ S, energy a b τ (p x) ≤ l) →
            ∃ q : C(M, Space n m), (∀ x, energy a b τ (q x) < k) ∧
              ∃ G : ContinuousMap.HomotopyRel p q S,
                ∀ t x, G (t, x) ∈ admissible a b m ∧
                  energy a b τ (G (t, x)) < energy a b τ v + ε := by
  obtain ⟨V, hV, hvV, hVsub, l, k, hlk, hk, hcross⟩ :=
    exists_critical_crossing_neighborhood_in (I := I) (M := M) a b τ hτ hzero hone v hv
      hcrit hanti habove univ isOpen_univ (mem_univ _) ε hε hd
  refine ⟨V, hV, hvV, hVsub.trans inter_subset_left, l, k, hlk, hk, ?_⟩
  intro p hp S hS hLow
  obtain ⟨q, hq, G, hG⟩ := hcross p hp S hS hLow
  exact ⟨q, hq, G, fun t x ↦ ⟨(hG t x).1, (hG t x).2.1⟩⟩

end Wikipedia.HomotopyGroupsOfSpheres.QuaternionicColumns.Polygon
