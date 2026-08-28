import Wikipedia.NoExoticSixSphere.OrthogonalCoreClearing

/-!
# Clearing a critical neighborhood while fixing a prescribed lower sublevel

The moving neighborhood lies above the prescribed lower threshold. Shrinking
the inner core to energies above the endpoint threshold gives an open
neighborhood of the critical polygon missed by every endpoint, without any
energy qualification on the parameter.
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

theorem exists_core_clearing_fixing_sublevel (a b : OrthogonalOperators n)
    (τ : Fin (m + 2) → ℝ) (hτ : StrictMono τ)
    (hzero : τ 0 = 0) (hone : τ (Fin.last (m + 1)) = 1)
    (v : Space n m) (hv : v ∈ shortDomain a b m)
    (hcrit : mfderiv 𝓘(ℝ, Model n m) 𝓘(ℝ, ℝ) (energy a b τ) v = 0)
    (hanti : (a⁻¹ * b).1.1 = -(1 : Vector n →L[ℝ] Vector n))
    (habove : (n : ℝ) * Real.pi ^ 2 < energy a b τ v)
    (N : Set (Space n m)) (hN : IsOpen N) (hvN : v ∈ N)
    (l ε : ℝ) (hl : l < energy a b τ v) (hε : 0 < ε) (hd : finrank ℝ B + 2 < n) :
    ∃ V outer inner : Set (Space n m),
      IsOpen V ∧ v ∈ V ∧ V ⊆ admissible a b m ∩ N ∧
      (∀ z ∈ V, l < energy a b τ z) ∧
      IsCompact outer ∧ outer ⊆ V ∧
      IsOpen inner ∧ v ∈ inner ∧ inner ⊆ outer ∧
      ∃ k : ℝ, l < k ∧ k < energy a b τ v ∧
        ∀ (p : C(M, Space n m)), (∀ x, p x ∈ admissible a b m) →
          ∃ q : C(M, Space n m), (∀ x, p x ∈ outer → energy a b τ (q x) < k) ∧
            (∀ x, q x ∉ inner) ∧
            ∃ G : ContinuousMap.HomotopyRel p q
              ({x | energy a b τ (p x) ≤ l} ∪ (p ⁻¹' V)ᶜ),
              ∀ t x, G (t, x) ∈ admissible a b m ∧
                energy a b τ (G (t, x)) ≤ max (energy a b τ (p x)) (energy a b τ v + ε) ∧
                (G (t, x) = p x ∨ G (t, x) ∈ N) ∧
                (p x ∉ outer → G (t, x) ∉ inner) := by
  let N' := N ∩ (admissible a b m ∩ energy a b τ ⁻¹' Ioi l)
  have hN' : IsOpen N' := hN.inter
    ((contMDiffOn_energy a b τ).continuousOn.isOpen_inter_preimage
      (isOpen_admissible a b m) isOpen_Ioi)
  obtain ⟨V, outer, inner₀, hV, hvV, hVsub, houter, houterV,
    hinner₀, hvInner₀, hinnerOuter₀, l₀, k₀, -, hk₀, hcross⟩ :=
    exists_critical_core_clearing (I := I) (M := M) a b τ hτ hzero hone v hv hcrit hanti
      habove N' hN' ⟨hvN, hv.1, hl⟩ ε hε hd
  let k := max k₀ ((l + energy a b τ v) / 2)
  have hlk : l < k := lt_of_lt_of_le (by linarith) (le_max_right _ _)
  have hk : k < energy a b τ v := max_lt hk₀ (by linarith)
  let inner := inner₀ ∩ (admissible a b m ∩ energy a b τ ⁻¹' Ioi k)
  have hinner : IsOpen inner := hinner₀.inter
    ((contMDiffOn_energy a b τ).continuousOn.isOpen_inter_preimage
      (isOpen_admissible a b m) isOpen_Ioi)
  have hVlow : ∀ z ∈ V, l < energy a b τ z := fun z hz ↦ (hVsub hz).2.2.2
  refine ⟨V, outer, inner, hV, hvV, (fun z hz ↦ ⟨(hVsub hz).1, (hVsub hz).2.1⟩),
    hVlow, houter, houterV, hinner, ⟨hvInner₀, hv.1, hk⟩,
    inter_subset_left.trans hinnerOuter₀, k, hlk, hk, ?_⟩
  intro p hp
  obtain ⟨q, hq, hqNo, G₀, hG₀⟩ := hcross p hp ∅ isCompact_empty (by simp)
  let G : ContinuousMap.HomotopyRel p q
      ({x | energy a b τ (p x) ≤ l} ∪ (p ⁻¹' V)ᶜ) :=
    { toHomotopy := G₀.toHomotopy
      prop' := fun t x hx ↦ G₀.eq_fst t (Or.inr (hx.elim
        (fun hlow hm ↦ (not_lt_of_ge hlow) (hVlow (p x) hm)) id)) }
  refine ⟨q, fun x hx ↦ (hq x hx).trans_le (le_max_left _ _), ?_, G, fun t x ↦ ?_⟩
  · intro x hx
    exact hqNo x ((le_max_left _ _).trans hx.2.2.le) hx.1
  · exact ⟨(hG₀ t x).1, (hG₀ t x).2.1,
      (hG₀ t x).2.2.1.imp id (fun h ↦ h.1),
      fun hx hy ↦ (hG₀ t x).2.2.2 hx hy.1⟩

end NoExoticSixSphere.OrthogonalPolygon
