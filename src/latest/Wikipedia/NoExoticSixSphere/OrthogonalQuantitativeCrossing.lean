import Wikipedia.NoExoticSixSphere.ChartQuantitativeCrossing
import Wikipedia.NoExoticSixSphere.QuantitativeCrossingLocalization
import Wikipedia.NoExoticSixSphere.OrthogonalPartialGradientCoordinates

/-!
# Quantitatively controlled localized crossings of actual polygon energy

The initial neighborhood and endpoint threshold do not depend on the later
spatial tolerance or energy-increase allowance. Every partial time of the
localized homotopy moves little whenever that parameter has lost little energy.
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

theorem exists_quantitative_crossing_of_data (a b : OrthogonalOperators n)
    (τ : Fin (m + 2) → ℝ) (v : Space n m)
    {L : (Fin d → ℝ) →L[ℝ] Model n m}
    (C : PartialGradientCoordinates.LocalData (localEnergy a b τ v) L (localAdmissible a b v))
    (N : Set (Space n m)) (hN : IsOpen N) (hvN : v ∈ N)
    (ε : ℝ) (hε : 0 < ε) (hd : finrank ℝ B < d) :
    ∃ V : Set (Space n m), IsOpen V ∧ v ∈ V ∧ V ⊆ admissible a b m ∩ N ∧
      ∃ l k : ℝ, l < k ∧ k < energy a b τ v ∧
        ∀ ρ > 0, ∃ ζ > 0, ∀ ξ : ℝ, 0 < ξ → ξ ≤ ζ →
          ∀ (p : C(M, Space n m)), (∀ x, p x ∈ admissible a b m) →
            ∀ (K : Set M), IsCompact K → K ⊆ p ⁻¹' V →
              ∀ (S : Set M), IsCompact S → (∀ x ∈ S, energy a b τ (p x) ≤ l) →
                ∃ q : C(M, Space n m), (∀ x ∈ K, energy a b τ (q x) < k) ∧
                  ∃ G : ContinuousMap.HomotopyRel p q (S ∪ (p ⁻¹' V)ᶜ),
                    ∀ t x, G (t, x) ∈ admissible a b m ∧
                      energy a b τ (G (t, x)) ≤ max (energy a b τ (p x)) (energy a b τ v + ε) ∧
                      (G (t, x) = p x ∨ G (t, x) ∈ N) ∧
                      energy a b τ (G (t, x)) < energy a b τ (p x) + ξ ∧
                      (energy a b τ (p x) - energy a b τ (G (t, x)) ≤ 2 * ζ →
                        dist (G (t, x)) (p x) < ρ) := by
  have htarget : (0 : Model n m) ∈ (atVertices v).target := by
    simpa only [atVertices_self] using (atVertices v).map_source (mem_atVertices_source v)
  obtain ⟨W, hW, hvW, hWsub, l, k, hlk, hk, hcross⟩ :=
    C.exists_quantitative_crossing_in_chart (I := I) (M := M)
      (isOpen_localAdmissible a b v) (contDiffOn_localEnergy a b τ v)
      (atVertices v) (contMDiff_atVertices_symm v).continuous htarget (energy a b τ)
      (fun _ ↦ rfl) (admissible a b m) C.source_subset N hN
      (by simpa only [atVertices_symm_zero] using hvN) ε hε (by simpa using hd)
  obtain ⟨V, hV, hvV, hVW, hlocal⟩ := localize_quantitative_crossing (M := M)
    (atVertices v) (contMDiff_atVertices_symm v).continuous htarget (energy a b τ)
    (admissible a b m) W N hW hvW l k (energy a b τ ((atVertices v).symm 0) + ε) hcross
  refine ⟨V, hV, ?_, hVW.trans hWsub, l, k, hlk, ?_, ?_⟩
  · simpa only [atVertices_symm_zero] using hvV
  · simpa only [atVertices_symm_zero] using hk
  · simpa only [atVertices_symm_zero] using hlocal

theorem exists_quantitative_critical_crossing (a b : OrthogonalOperators n)
    (τ : Fin (m + 2) → ℝ) (hτ : StrictMono τ)
    (hzero : τ 0 = 0) (hone : τ (Fin.last (m + 1)) = 1)
    (v : Space n m) (hv : v ∈ shortDomain a b m)
    (hcrit : mfderiv 𝓘(ℝ, Model n m) 𝓘(ℝ, ℝ) (energy a b τ) v = 0)
    (hanti : (a⁻¹ * b).1.1 = -(1 : Vector n →L[ℝ] Vector n))
    (habove : (n : ℝ) * Real.pi ^ 2 < energy a b τ v)
    (N : Set (Space n m)) (hN : IsOpen N) (hvN : v ∈ N)
    (ε : ℝ) (hε : 0 < ε) (hd : finrank ℝ B + 2 < n) :
    ∃ V : Set (Space n m), IsOpen V ∧ v ∈ V ∧ V ⊆ admissible a b m ∩ N ∧
      ∃ l k : ℝ, l < k ∧ k < energy a b τ v ∧
        ∀ ρ > 0, ∃ ζ > 0, ∀ ξ : ℝ, 0 < ξ → ξ ≤ ζ →
          ∀ (p : C(M, Space n m)), (∀ x, p x ∈ admissible a b m) →
            ∀ (K : Set M), IsCompact K → K ⊆ p ⁻¹' V →
              ∀ (S : Set M), IsCompact S → (∀ x ∈ S, energy a b τ (p x) ≤ l) →
                ∃ q : C(M, Space n m), (∀ x ∈ K, energy a b τ (q x) < k) ∧
                  ∃ G : ContinuousMap.HomotopyRel p q (S ∪ (p ⁻¹' V)ᶜ),
                    ∀ t x, G (t, x) ∈ admissible a b m ∧
                      energy a b τ (G (t, x)) ≤ max (energy a b τ (p x)) (energy a b τ v + ε) ∧
                      (G (t, x) = p x ∨ G (t, x) ∈ N) ∧
                      energy a b τ (G (t, x)) < energy a b τ (p x) + ξ ∧
                      (energy a b τ (p x) - energy a b τ (G (t, x)) ≤ 2 * ζ →
                        dist (G (t, x)) (p x) < ρ) := by
  obtain ⟨d, L, hdim, -, ⟨C⟩⟩ :=
    exists_partialGradient_coordinates a b τ hτ hzero hone v hv hcrit hanti habove
  exact exists_quantitative_crossing_of_data (I := I) a b τ v C N hN hvN ε hε (by omega)

theorem exists_quantitative_crossing_fixing_sublevel (a b : OrthogonalOperators n)
    (τ : Fin (m + 2) → ℝ) (hτ : StrictMono τ)
    (hzero : τ 0 = 0) (hone : τ (Fin.last (m + 1)) = 1)
    (v : Space n m) (hv : v ∈ shortDomain a b m)
    (hcrit : mfderiv 𝓘(ℝ, Model n m) 𝓘(ℝ, ℝ) (energy a b τ) v = 0)
    (hanti : (a⁻¹ * b).1.1 = -(1 : Vector n →L[ℝ] Vector n))
    (habove : (n : ℝ) * Real.pi ^ 2 < energy a b τ v)
    (N : Set (Space n m)) (hN : IsOpen N) (hvN : v ∈ N)
    (l ε : ℝ) (hl : l < energy a b τ v) (hε : 0 < ε) (hd : finrank ℝ B + 2 < n) :
    ∃ V : Set (Space n m), IsOpen V ∧ v ∈ V ∧ V ⊆ admissible a b m ∩ N ∧
      (∀ z ∈ V, l < energy a b τ z) ∧
      ∃ k : ℝ, l < k ∧ k < energy a b τ v ∧
        ∀ ρ > 0, ∃ ζ > 0, ∀ ξ : ℝ, 0 < ξ → ξ ≤ ζ →
          ∀ (p : C(M, Space n m)), (∀ x, p x ∈ admissible a b m) →
            ∀ (K : Set M), IsCompact K → K ⊆ p ⁻¹' V →
              ∃ q : C(M, Space n m), (∀ x ∈ K, energy a b τ (q x) < k) ∧
                ∃ G : ContinuousMap.HomotopyRel p q
                  ({x | energy a b τ (p x) ≤ l} ∪ (p ⁻¹' V)ᶜ),
                  ∀ t x, G (t, x) ∈ admissible a b m ∧
                    energy a b τ (G (t, x)) ≤ max (energy a b τ (p x)) (energy a b τ v + ε) ∧
                    (G (t, x) = p x ∨ G (t, x) ∈ N) ∧
                    energy a b τ (G (t, x)) < energy a b τ (p x) + ξ ∧
                    (energy a b τ (p x) - energy a b τ (G (t, x)) ≤ 2 * ζ →
                      dist (G (t, x)) (p x) < ρ) := by
  let N' := N ∩ (admissible a b m ∩ energy a b τ ⁻¹' Ioi l)
  have hN' : IsOpen N' := hN.inter
    ((contMDiffOn_energy a b τ).continuousOn.isOpen_inter_preimage
      (isOpen_admissible a b m) isOpen_Ioi)
  obtain ⟨V, hV, hvV, hVsub, l₀, k₀, -, hk₀, hcross⟩ :=
    exists_quantitative_critical_crossing (I := I) (M := M) a b τ hτ hzero hone v hv hcrit
      hanti habove N' hN' ⟨hvN, hv.1, hl⟩ ε hε hd
  let k := max k₀ ((l + energy a b τ v) / 2)
  have hlk : l < k := lt_of_lt_of_le (by linarith) (le_max_right _ _)
  have hk : k < energy a b τ v := max_lt hk₀ (by linarith)
  have hVlow : ∀ z ∈ V, l < energy a b τ z := fun z hz ↦ (hVsub hz).2.2.2
  refine ⟨V, hV, hvV, (fun z hz ↦ ⟨(hVsub hz).1, (hVsub hz).2.1⟩),
    hVlow, k, hlk, hk, ?_⟩
  intro ρ hρ
  obtain ⟨ζ, hζ, hcrossζ⟩ := hcross ρ hρ
  refine ⟨ζ, hζ, ?_⟩
  intro ξ hξ hξζ p hp K hK hKV
  obtain ⟨q, hq, G₀, hG₀⟩ := hcrossζ ξ hξ hξζ p hp K hK hKV ∅ isCompact_empty (by simp)
  let G : ContinuousMap.HomotopyRel p q
      ({x | energy a b τ (p x) ≤ l} ∪ (p ⁻¹' V)ᶜ) :=
    { toHomotopy := G₀.toHomotopy
      prop' := fun t x hx ↦ G₀.eq_fst t (Or.inr (hx.elim
        (fun hlow hm ↦ (not_lt_of_ge hlow) (hVlow (p x) hm)) id)) }
  exact ⟨q, fun x hx ↦ (hq x hx).trans_le (le_max_left _ _), G,
    fun t x ↦ ⟨(hG₀ t x).1, (hG₀ t x).2.1,
      (hG₀ t x).2.2.1.imp id (fun h ↦ h.1), (hG₀ t x).2.2.2.1, (hG₀ t x).2.2.2.2⟩⟩

end NoExoticSixSphere.OrthogonalPolygon
