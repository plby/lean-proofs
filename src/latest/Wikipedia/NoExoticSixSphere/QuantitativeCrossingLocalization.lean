import Wikipedia.NoExoticSixSphere.LocalCrossingLocalization

/-!
# Localization retaining quantitative energy and movement control

The localization neighborhood is chosen before the spatial tolerance and energy
window. The supported cutoff retains additive energy control and the implication
that a small energy loss forces small movement, also on transition parameters.
-/

open Set
open scoped Topology

namespace NoExoticSixSphere

variable {M Y E : Type*} [TopologicalSpace M] [CompactSpace M] [T2Space M]
  [PseudoMetricSpace Y] [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem localize_quantitative_crossing (e : OpenPartialHomeomorph Y E)
    (hinv : Continuous e.symm) (hzero : (0 : E) ∈ e.target)
    (energy : Y → ℝ) (admissible W control : Set Y) (hW : IsOpen W) (hcenter : e.symm 0 ∈ W)
    (l k cap : ℝ)
    (hcross : ∀ ρ > 0, ∃ ζ > 0, ∀ ξ : ℝ, 0 < ξ → ξ ≤ ζ →
      ∀ (p : C(M, Y)), (∀ x, p x ∈ W) →
        ∀ (S : Set M), IsCompact S → (∀ x ∈ S, energy (p x) ≤ l) →
          ∃ q : C(M, Y), (∀ x, energy (q x) < k) ∧
            ∃ G : ContinuousMap.HomotopyRel p q S,
              ∀ t x, G (t, x) ∈ admissible ∧ energy (G (t, x)) < cap ∧ G (t, x) ∈ control ∧
                energy (G (t, x)) < energy (p x) + ξ ∧
                (energy (p x) - energy (G (t, x)) ≤ 2 * ζ → dist (G (t, x)) (p x) < ρ)) :
    ∃ V : Set Y, IsOpen V ∧ e.symm 0 ∈ V ∧ V ⊆ W ∧
      ∀ ρ > 0, ∃ ζ > 0, ∀ ξ : ℝ, 0 < ξ → ξ ≤ ζ →
        ∀ (p : C(M, Y)), (∀ x, p x ∈ admissible) →
          ∀ (K : Set M), IsCompact K → K ⊆ p ⁻¹' V →
            ∀ (S : Set M), IsCompact S → (∀ x ∈ S, energy (p x) ≤ l) →
              ∃ q : C(M, Y), (∀ x ∈ K, energy (q x) < k) ∧
                ∃ G : ContinuousMap.HomotopyRel p q (S ∪ (p ⁻¹' V)ᶜ),
                  ∀ t x, G (t, x) ∈ admissible ∧
                    energy (G (t, x)) ≤ max (energy (p x)) cap ∧
                    (G (t, x) = p x ∨ G (t, x) ∈ control) ∧
                    energy (G (t, x)) < energy (p x) + ξ ∧
                    (energy (p x) - energy (G (t, x)) ≤ 2 * ζ → dist (G (t, x)) (p x) < ρ) := by
  obtain ⟨V, hV, hcenterV, hVW, hlocal⟩ :=
    exists_relational_localization_neighborhood (M := M) e hinv hzero W hW hcenter
  refine ⟨V, hV, hcenterV, hVW, ?_⟩
  intro ρ hρ
  obtain ⟨ζ, hζ, hcrossζ⟩ := hcross ρ hρ
  refine ⟨ζ, hζ, ?_⟩
  intro ξ hξ hξζ p hp K hK hKV S hS hLow
  let R : Y → Y → Prop := fun y z ↦ z ∈ control ∧ energy z < energy y + ξ ∧
    (energy y - energy z ≤ 2 * ζ → dist z y < ρ)
  obtain ⟨q, hq, G, hG⟩ := hlocal energy admissible l k cap R
    (hcrossζ ξ hξ hξζ) p hp K hK hKV S hS hLow
  refine ⟨q, hq, G, fun t x ↦ ⟨(hG t x).1, (hG t x).2.1, ?_⟩⟩
  rcases (hG t x).2.2 with heq | hrel
  · refine ⟨Or.inl heq, ?_, ?_⟩
    · rw [heq]
      linarith
    · intro _
      rw [heq, dist_self]
      exact hρ
  · exact ⟨Or.inr hrel.1, hrel.2.1, hrel.2.2⟩

end NoExoticSixSphere
