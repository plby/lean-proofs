import Wikipedia.NoExoticSixSphere.ChartCoreClearing
import Wikipedia.NoExoticSixSphere.OrthogonalPartialGradientCoordinates

/-!
# Core clearing at nonminimal critical orthogonal polygons

These homotopies consist of actual polygon vertices and accept arbitrary
admissible parameter families. An open inner core of the critical polygon
contains no high-energy endpoint. The moved part remains inside a prescribed
neighborhood, and parameters initially outside the compact outer core never
enter the inner core during the crossing.
-/

open Set Module
open scoped ContDiff Manifold Topology

namespace NoExoticSixSphere.OrthogonalPolygon

open GLOrthonormalization OrthogonalVertexSpace

variable {B H M : Type*} [NormedAddCommGroup B] [NormedSpace ℝ B]
  [FiniteDimensional ℝ B] [TopologicalSpace H] {I : ModelWithCorners ℝ B H}
  [I.Boundaryless] [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [T2Space M] {n m d : ℕ}

include I

theorem exists_core_clearing_of_data (a b : OrthogonalOperators n)
    (τ : Fin (m + 2) → ℝ) (v : Space n m)
    {L : (Fin d → ℝ) →L[ℝ] Model n m}
    (C : PartialGradientCoordinates.LocalData (localEnergy a b τ v) L (localAdmissible a b v))
    (N : Set (Space n m)) (hN : IsOpen N) (hvN : v ∈ N)
    (ε : ℝ) (hε : 0 < ε) (hd : finrank ℝ B < d) :
    ∃ V outer inner : Set (Space n m),
      IsOpen V ∧ v ∈ V ∧ V ⊆ admissible a b m ∩ N ∧
      IsCompact outer ∧ outer ⊆ V ∧
      IsOpen inner ∧ v ∈ inner ∧ inner ⊆ outer ∧
      ∃ l k : ℝ, l < k ∧ k < energy a b τ v ∧
        ∀ (p : C(M, Space n m)), (∀ x, p x ∈ admissible a b m) →
          ∀ (S : Set M), IsCompact S → (∀ x ∈ S, energy a b τ (p x) ≤ l) →
            ∃ q : C(M, Space n m), (∀ x, p x ∈ outer → energy a b τ (q x) < k) ∧
              (∀ x, k ≤ energy a b τ (q x) → q x ∉ inner) ∧
              ∃ G : ContinuousMap.HomotopyRel p q (S ∪ (p ⁻¹' V)ᶜ),
                ∀ t x, G (t, x) ∈ admissible a b m ∧
                  energy a b τ (G (t, x)) ≤ max (energy a b τ (p x)) (energy a b τ v + ε) ∧
                  (G (t, x) = p x ∨ G (t, x) ∈ N) ∧
                  (p x ∉ outer → G (t, x) ∉ inner) := by
  have htarget : (0 : Model n m) ∈ (atVertices v).target := by
    simpa only [atVertices_self] using (atVertices v).map_source (mem_atVertices_source v)
  have hh := C.exists_core_clearing_in_chart (I := I) (M := M)
    (isOpen_localAdmissible a b v) (contDiffOn_localEnergy a b τ v)
    (atVertices v) (contMDiff_atVertices_symm v).continuous htarget (energy a b τ)
    (fun _ ↦ rfl) (admissible a b m) C.source_subset N hN
    (by simpa only [atVertices_symm_zero] using hvN) ε hε (by simpa using hd)
  simpa only [atVertices_symm_zero] using hh

theorem exists_critical_core_clearing (a b : OrthogonalOperators n)
    (τ : Fin (m + 2) → ℝ) (hτ : StrictMono τ)
    (hzero : τ 0 = 0) (hone : τ (Fin.last (m + 1)) = 1)
    (v : Space n m) (hv : v ∈ shortDomain a b m)
    (hcrit : mfderiv 𝓘(ℝ, Model n m) 𝓘(ℝ, ℝ) (energy a b τ) v = 0)
    (hanti : (a⁻¹ * b).1.1 = -(1 : Vector n →L[ℝ] Vector n))
    (habove : (n : ℝ) * Real.pi ^ 2 < energy a b τ v)
    (N : Set (Space n m)) (hN : IsOpen N) (hvN : v ∈ N)
    (ε : ℝ) (hε : 0 < ε) (hd : finrank ℝ B + 2 < n) :
    ∃ V outer inner : Set (Space n m),
      IsOpen V ∧ v ∈ V ∧ V ⊆ admissible a b m ∩ N ∧
      IsCompact outer ∧ outer ⊆ V ∧
      IsOpen inner ∧ v ∈ inner ∧ inner ⊆ outer ∧
      ∃ l k : ℝ, l < k ∧ k < energy a b τ v ∧
        ∀ (p : C(M, Space n m)), (∀ x, p x ∈ admissible a b m) →
          ∀ (S : Set M), IsCompact S → (∀ x ∈ S, energy a b τ (p x) ≤ l) →
            ∃ q : C(M, Space n m), (∀ x, p x ∈ outer → energy a b τ (q x) < k) ∧
              (∀ x, k ≤ energy a b τ (q x) → q x ∉ inner) ∧
              ∃ G : ContinuousMap.HomotopyRel p q (S ∪ (p ⁻¹' V)ᶜ),
                ∀ t x, G (t, x) ∈ admissible a b m ∧
                  energy a b τ (G (t, x)) ≤ max (energy a b τ (p x)) (energy a b τ v + ε) ∧
                  (G (t, x) = p x ∨ G (t, x) ∈ N) ∧
                  (p x ∉ outer → G (t, x) ∉ inner) := by
  obtain ⟨d, L, hdim, -, ⟨C⟩⟩ :=
    exists_partialGradient_coordinates a b τ hτ hzero hone v hv hcrit hanti habove
  exact exists_core_clearing_of_data (I := I) a b τ v C N hN hvN ε hε (by omega)

end NoExoticSixSphere.OrthogonalPolygon
