import Wikipedia.NoExoticSixSphere.LocalCrossingLocalization

/-!
# Localizing a crossing without refilling an inner core

The localization neighborhood is chosen before the cores and the no-entry
condition. A cutoff equal to one on the preimage of the compact outer core
lowers every parameter there. Parameters outside that preimage cannot enter
the inner core, including during the cutoff transition. Consequently the
endpoint has no high-energy point in the inner core.
-/

open Set
open scoped Topology

namespace NoExoticSixSphere

variable {M Y E : Type*} [TopologicalSpace M] [CompactSpace M] [T2Space M]
  [TopologicalSpace Y] [T2Space Y] [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem exists_core_clearing_neighborhood
    (e : OpenPartialHomeomorph Y E) (hinv : Continuous e.symm)
    (hzero : (0 : E) ∈ e.target) (W : Set Y)
    (hW : IsOpen W) (hcenter : e.symm 0 ∈ W) :
    ∃ V : Set Y, IsOpen V ∧ e.symm 0 ∈ V ∧ V ⊆ W ∧
      ∀ (energy : Y → ℝ) (admissible outer inner : Set Y) (l k cap : ℝ),
        IsCompact outer → outer ⊆ V → inner ⊆ outer →
        (∀ (p : C(M, Y)), (∀ x, p x ∈ W) →
          ∀ (S : Set M), IsCompact S → (∀ x ∈ S, energy (p x) ≤ l) →
            ∃ q : C(M, Y), (∀ x, energy (q x) < k) ∧
              ∃ H : ContinuousMap.HomotopyRel p q S,
                ∀ t x, H (t, x) ∈ admissible ∧ energy (H (t, x)) < cap ∧
                  (p x ∉ outer → H (t, x) ∉ inner)) →
        ∀ (p : C(M, Y)), (∀ x, p x ∈ admissible) →
          ∀ (S : Set M), IsCompact S → (∀ x ∈ S, energy (p x) ≤ l) →
            ∃ q : C(M, Y), (∀ x, p x ∈ outer → energy (q x) < k) ∧
              (∀ x, k ≤ energy (q x) → q x ∉ inner) ∧
              ∃ H : ContinuousMap.HomotopyRel p q (S ∪ (p ⁻¹' V)ᶜ),
                ∀ t x, H (t, x) ∈ admissible ∧
                  energy (H (t, x)) ≤ max (energy (p x)) cap ∧
                  (p x ∉ outer → H (t, x) ∉ inner) := by
  obtain ⟨V, hV, hcenterV, hVW, hlocal⟩ :=
    exists_relational_localization_neighborhood (M := M) e hinv hzero W hW hcenter
  refine ⟨V, hV, hcenterV, hVW, ?_⟩
  intro energy admissible outer inner l k cap houter houterV hinner hcross p hp S hS hLow
  have hK : IsCompact (p ⁻¹' outer) := (houter.isClosed.preimage p.continuous).isCompact
  obtain ⟨q, hq, H, hH⟩ := hlocal energy admissible l k cap
    (fun y z ↦ y ∉ outer → z ∉ inner) hcross p hp (p ⁻¹' outer) hK
    (fun _ hx ↦ houterV hx) S hS hLow
  have hno (t) (x) (hx : p x ∉ outer) : H (t, x) ∉ inner := by
    rcases (hH t x).2.2 with heq | hrel
    · rw [heq]
      exact fun hi ↦ hx (hinner hi)
    · exact hrel hx
  refine ⟨q, hq, ?_, H, fun t x ↦ ⟨(hH t x).1, (hH t x).2.1, hno t x⟩⟩
  intro x hx
  have hout : p x ∉ outer := fun hi ↦ (not_lt_of_ge hx) (hq x hi)
  simpa only [H.apply_one] using hno 1 x hout

theorem exists_controlled_core_clearing_neighborhood
    (e : OpenPartialHomeomorph Y E) (hinv : Continuous e.symm)
    (hzero : (0 : E) ∈ e.target) (W : Set Y)
    (hW : IsOpen W) (hcenter : e.symm 0 ∈ W) :
    ∃ V : Set Y, IsOpen V ∧ e.symm 0 ∈ V ∧ V ⊆ W ∧
      ∀ (energy : Y → ℝ) (admissible outer inner control : Set Y) (l k cap : ℝ),
        IsCompact outer → outer ⊆ V → inner ⊆ outer →
        (∀ (p : C(M, Y)), (∀ x, p x ∈ W) →
          ∀ (S : Set M), IsCompact S → (∀ x ∈ S, energy (p x) ≤ l) →
            ∃ q : C(M, Y), (∀ x, energy (q x) < k) ∧
              ∃ H : ContinuousMap.HomotopyRel p q S,
                ∀ t x, H (t, x) ∈ admissible ∧ energy (H (t, x)) < cap ∧
                  H (t, x) ∈ control ∧ (p x ∉ outer → H (t, x) ∉ inner)) →
        ∀ (p : C(M, Y)), (∀ x, p x ∈ admissible) →
          ∀ (S : Set M), IsCompact S → (∀ x ∈ S, energy (p x) ≤ l) →
            ∃ q : C(M, Y), (∀ x, p x ∈ outer → energy (q x) < k) ∧
              (∀ x, k ≤ energy (q x) → q x ∉ inner) ∧
              ∃ H : ContinuousMap.HomotopyRel p q (S ∪ (p ⁻¹' V)ᶜ),
                ∀ t x, H (t, x) ∈ admissible ∧
                  energy (H (t, x)) ≤ max (energy (p x)) cap ∧
                  (H (t, x) = p x ∨ H (t, x) ∈ control) ∧
                  (p x ∉ outer → H (t, x) ∉ inner) := by
  obtain ⟨V, hV, hcenterV, hVW, hlocal⟩ :=
    exists_relational_localization_neighborhood (M := M) e hinv hzero W hW hcenter
  refine ⟨V, hV, hcenterV, hVW, ?_⟩
  intro energy admissible outer inner control l k cap houter houterV hinner hcross p hp S hS hLow
  have hK : IsCompact (p ⁻¹' outer) := (houter.isClosed.preimage p.continuous).isCompact
  obtain ⟨q, hq, H, hH⟩ := hlocal energy admissible l k cap
    (fun y z ↦ z ∈ control ∧ (y ∉ outer → z ∉ inner)) hcross p hp (p ⁻¹' outer) hK
    (fun _ hx ↦ houterV hx) S hS hLow
  have hno (t) (x) (hx : p x ∉ outer) : H (t, x) ∉ inner := by
    rcases (hH t x).2.2 with heq | hrel
    · rw [heq]
      exact fun hi ↦ hx (hinner hi)
    · exact hrel.2 hx
  refine ⟨q, hq, ?_, H, fun t x ↦ ⟨(hH t x).1, (hH t x).2.1,
    (hH t x).2.2.imp_right And.left, hno t x⟩⟩
  intro x hx
  have hout : p x ∉ outer := fun hi ↦ (not_lt_of_ge hx) (hq x hi)
  simpa only [H.apply_one] using hno 1 x hout

end NoExoticSixSphere
