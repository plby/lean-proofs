import Wikipedia.HomotopyGroupsOfSpheres.QuaternionicLocalCriticalCrossing
import Wikipedia.NoExoticSixSphere.LocalCrossingLocalization

/-!
# Localized relative crossing at a symplectic critical polygon

The original compact parameter family may leave the critical-point chart.
Only parameters whose original polygon lies in a small verified neighborhood
are moved. A chosen compact subset of those parameters is pushed below the
critical energy, while the prescribed lower-energy part stays fixed.
-/

open Set Module
open scoped ContDiff Manifold Topology

namespace Wikipedia.HomotopyGroupsOfSpheres.QuaternionicColumns.Polygon

open NoExoticSixSphere NoExoticSixSphere.GLOrthonormalization VertexSpace

variable {B H M : Type*} [NormedAddCommGroup B] [NormedSpace ℝ B]
  [FiniteDimensional ℝ B] [TopologicalSpace H] {I : ModelWithCorners ℝ B H}
  [I.Boundaryless] [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [T2Space M] {n m : ℕ}

include I

theorem exists_localized_critical_crossing_in (a b : symplecticSubgroup n)
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
        ∀ (p : C(M, Space n m)), (∀ x, p x ∈ admissible a b m) →
          ∀ (K : Set M), IsCompact K → K ⊆ p ⁻¹' V →
            ∀ (S : Set M), IsCompact S → (∀ x ∈ S, energy a b τ (p x) ≤ l) →
              ∃ q : C(M, Space n m), (∀ x ∈ K, energy a b τ (q x) < k) ∧
                ∃ G : ContinuousMap.HomotopyRel p q (S ∪ (p ⁻¹' V)ᶜ),
                  ∀ t x, G (t, x) ∈ admissible a b m ∧
                    energy a b τ (G (t, x)) ≤
                      max (energy a b τ (p x)) (energy a b τ v + ε) ∧
                        (G (t, x) = p x ∨ G (t, x) ∈ N) := by
  obtain ⟨W, hW, hvW, hWadm, l, k, hlk, hk, hcross⟩ :=
    exists_critical_crossing_neighborhood_in (I := I) (M := M) a b τ hτ hzero hone v hv
      hcrit hanti habove N hN hvN ε hε hd
  have htarget : (0 : Model n m) ∈ (atVertices v).target := by
    have hh := (atVertices v).map_source (mem_atVertices_source v)
    simpa only [atVertices_self] using hh
  obtain ⟨V, hV, hvV, hVW, hlocal⟩ := localize_crossing_controlled
    (M := M) (Y := Space n m) (E := Model n m) (atVertices v)
    (contMDiff_atVertices_symm v).continuous htarget (energy a b τ) (admissible a b m) W N
    hW (by simpa only [atVertices_symm_zero] using hvW) l k (energy a b τ v + ε) hcross
  exact ⟨V, hV, by simpa only [atVertices_symm_zero] using hvV,
    hVW.trans hWadm, l, k, hlk, hk, hlocal⟩

theorem exists_localized_critical_crossing (a b : symplecticSubgroup n)
    (τ : Fin (m + 2) → ℝ) (hτ : StrictMono τ)
    (hzero : τ 0 = 0) (hone : τ (Fin.last (m + 1)) = 1)
    (v : Space n m) (hv : v ∈ shortDomain a b m)
    (hcrit : mfderiv 𝓘(ℝ, Model n m) 𝓘(ℝ, ℝ) (energy a b τ) v = 0)
    (hanti : (a⁻¹ * b).val.val.val = -(1 : Vector (4 * n + 4) →L[ℝ] Vector (4 * n + 4)))
    (habove : ((4 * n + 4 : ℕ) : ℝ) * Real.pi ^ 2 < energy a b τ v)
    (ε : ℝ) (hε : 0 < ε) (hd : finrank ℝ B < n) :
    ∃ V : Set (Space n m), IsOpen V ∧ v ∈ V ∧ V ⊆ admissible a b m ∧
      ∃ l k : ℝ, l < k ∧ k < energy a b τ v ∧
        ∀ (p : C(M, Space n m)), (∀ x, p x ∈ admissible a b m) →
          ∀ (K : Set M), IsCompact K → K ⊆ p ⁻¹' V →
            ∀ (S : Set M), IsCompact S → (∀ x ∈ S, energy a b τ (p x) ≤ l) →
              ∃ q : C(M, Space n m), (∀ x ∈ K, energy a b τ (q x) < k) ∧
                ∃ G : ContinuousMap.HomotopyRel p q (S ∪ (p ⁻¹' V)ᶜ),
                  ∀ t x, G (t, x) ∈ admissible a b m ∧
                    energy a b τ (G (t, x)) ≤
                      max (energy a b τ (p x)) (energy a b τ v + ε) := by
  obtain ⟨V, hV, hvV, hVsub, l, k, hlk, hk, hcross⟩ :=
    exists_localized_critical_crossing_in (I := I) (M := M) a b τ hτ hzero hone v hv
      hcrit hanti habove univ isOpen_univ (mem_univ _) ε hε hd
  refine ⟨V, hV, hvV, hVsub.trans inter_subset_left, l, k, hlk, hk, ?_⟩
  intro p hp K hK hKV S hS hLow
  obtain ⟨q, hq, G, hG⟩ := hcross p hp K hK hKV S hS hLow
  exact ⟨q, hq, G, fun t x ↦ ⟨(hG t x).1, (hG t x).2.1⟩⟩

end Wikipedia.HomotopyGroupsOfSpheres.QuaternionicColumns.Polygon
