import Wikipedia.NoExoticSixSphere.OrthogonalLocalizedCriticalCrossing

/-!
# A localized crossing fixing a prescribed lower sublevel

Confining the crossing neighborhood to energies strictly above a prescribed
threshold makes the entire lower sublevel fixed, independently of the
thresholds produced by the local negative-family construction. The endpoint
threshold is chosen between the prescribed threshold and the critical energy.
-/

open Set Module
open scoped ContDiff Manifold Topology

namespace NoExoticSixSphere.OrthogonalPolygon

open GLOrthonormalization OrthogonalVertexSpace

variable {B H M : Type*} [NormedAddCommGroup B] [NormedSpace ℝ B]
  [FiniteDimensional ℝ B] [TopologicalSpace H] {I : ModelWithCorners ℝ B H}
  [I.Boundaryless] [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [T2Space M] {n m : ℕ}

include I

theorem exists_crossing_fixing_sublevel (a b : OrthogonalOperators n)
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
        ∀ (p : C(M, Space n m)), (∀ x, p x ∈ admissible a b m) →
          ∀ (K : Set M), IsCompact K → K ⊆ p ⁻¹' V →
            ∃ q : C(M, Space n m), (∀ x ∈ K, energy a b τ (q x) < k) ∧
              ∃ G : ContinuousMap.HomotopyRel p q
                ({x | energy a b τ (p x) ≤ l} ∪ (p ⁻¹' V)ᶜ),
                ∀ t x, G (t, x) ∈ admissible a b m ∧
                  energy a b τ (G (t, x)) ≤ max (energy a b τ (p x)) (energy a b τ v + ε) ∧
                  (G (t, x) = p x ∨ G (t, x) ∈ N) := by
  let N' := N ∩ (admissible a b m ∩ energy a b τ ⁻¹' Ioi l)
  have hN' : IsOpen N' := hN.inter
    ((contMDiffOn_energy a b τ).continuousOn.isOpen_inter_preimage
      (isOpen_admissible a b m) isOpen_Ioi)
  obtain ⟨V, hV, hvV, hVsub, l₀, k₀, -, hk₀, hcross⟩ :=
    exists_localized_critical_crossing_in (I := I) (M := M) a b τ hτ hzero hone v hv
      hcrit hanti habove N' hN' ⟨hvN, hv.1, hl⟩ ε hε hd
  let k := max k₀ ((l + energy a b τ v) / 2)
  have hlk : l < k := lt_of_lt_of_le (by linarith) (le_max_right _ _)
  have hk : k < energy a b τ v := max_lt hk₀ (by linarith)
  have hVlow : ∀ z ∈ V, l < energy a b τ z := fun z hz ↦ (hVsub hz).2.2.2
  refine ⟨V, hV, hvV, (fun z hz ↦ ⟨(hVsub hz).1, (hVsub hz).2.1⟩), hVlow,
    k, hlk, hk, ?_⟩
  intro p hp K hK hKV
  obtain ⟨q, hq, G₀, hG₀⟩ := hcross p hp K hK hKV ∅ isCompact_empty (by simp)
  let G : ContinuousMap.HomotopyRel p q
      ({x | energy a b τ (p x) ≤ l} ∪ (p ⁻¹' V)ᶜ) :=
    { toHomotopy := G₀.toHomotopy
      prop' := fun t x hx ↦ G₀.eq_fst t (Or.inr (hx.elim
        (fun hlow hm ↦ (not_lt_of_ge hlow) (hVlow (p x) hm)) id)) }
  exact ⟨q, fun x hx ↦ (hq x hx).trans_le (le_max_left _ _), G,
    fun t x ↦ ⟨(hG₀ t x).1, (hG₀ t x).2.1, (hG₀ t x).2.2.imp id (fun h ↦ h.1)⟩⟩

end NoExoticSixSphere.OrthogonalPolygon
