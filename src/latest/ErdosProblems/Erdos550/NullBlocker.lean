import Mathlib
import ErdosProblems.Erdos550.Rounding

set_option relaxedAutoImplicit true
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Exact null-blocker rounding (Theorem 4.1 of the paper)

The central abstract "compactness-and-rounding" result, stated independently of
Ramsey theory.  For `q` probability spaces and events `A_i(x)` with densities
`ρ_i(x) = μ_i(A_i(x))`, under the three null-intersection hypotheses (N1)–(N3),
the ground set can be coloured by `[q]` after deleting at most `a-1` vertices, so
that no `D_i`-edge is monochromatic in colour `i`.
-/

open MeasureTheory Finset
open scoped ENNReal

namespace Erdos550

/-- **Exact null-blocker rounding (Theorem 4.1).**  `X` is finite or countable.
For each colour `i`, `(Ω i, μ i)` is a probability space and `A i x ⊆ Ω i` is
measurable, with density `ρ_i(x) = μ_i(A_i(x))`; `D i` is a hypergraph of
nonempty finite edges on `X`.  Under (N1)–(N3), there is a deletion set `Z` of
size `≤ a-1` and a colouring `φ` of the rest with no `D_i`-edge monochromatic in
colour `i`.

The nonemptiness hypothesis `hDne` is part of the paper's statement (Theorem 4.1)
and is kept for faithfulness; it is in fact not needed for the proof, since (N3)
already forces every edge to be nonempty (a probability measure cannot assign
measure `0` to the intersection over an empty edge, which is the whole space). -/
theorem exact_rounding
    (q : ℕ) (hq : 2 ≤ q) (a : ℕ) (ha : 1 ≤ a)
    (X : Type*) [Countable X]
    (Ω : Fin q → Type*) [∀ i, MeasurableSpace (Ω i)]
    (μ : ∀ i, Measure (Ω i)) [∀ i, IsProbabilityMeasure (μ i)]
    (A : ∀ i, X → Set (Ω i)) (hA : ∀ i x, MeasurableSet (A i x))
    (D : Fin q → Set (Finset X)) (_hDne : ∀ i, ∀ E ∈ D i, E.Nonempty)
    (hN1 : ∀ x : X, ((q : ℝ≥0∞) - 1) ≤ ∑ i, μ i (A i x))
    (hN2 : ∀ S : Finset X, S.card = a → ∃ i, μ i (⋂ x ∈ S, A i x) = 0)
    (hN3 : ∀ i : Fin q, ∀ E ∈ D i, ∃ j, j ≠ i ∧ μ j (⋂ x ∈ E, A j x) = 0) :
    ∃ (Z : Finset X) (φ : X → Fin q), Z.card ≤ a - 1 ∧
      ∀ i : Fin q, ∀ E ∈ D i, ¬ (∀ x ∈ E, x ∉ Z ∧ φ x = i) := by
  classical
  -- The countable index type of all edges across all colours.
  obtain ⟨ω, hfin, hncard, hblock⟩ :=
    exists_good_outcome μ A hq ha hA hN1 hN2
      (ι := Σ i : Fin q, {E : Finset X // E ∈ D i})
      (fun e => e.2.1) (fun e => Classical.choose (hN3 e.1 e.2.1 e.2.2))
      (fun e => (Classical.choose_spec (hN3 e.1 e.2.1 e.2.2)).2)
  refine ⟨hfin.toFinset,
    fun x => if h : ∃ k, ω k ∉ A k x then Classical.choose h else ⟨0, by omega⟩,
    ?_, ?_⟩
  · -- The deletion set has at most `a-1` vertices.
    rw [← Set.ncard_eq_toFinset_card _ hfin]
    exact hncard
  · -- No `D_i`-edge is monochromatic in colour `i`.
    intro i E hE hmono
    set e : (Σ i : Fin q, {E : Finset X // E ∈ D i}) := ⟨i, ⟨E, hE⟩⟩ with he
    obtain ⟨x₀, hx₀E, hmiss⟩ := hblock e
    obtain ⟨hx₀Z, hφ⟩ := hmono x₀ hx₀E
    have hge : q - 1 ≤ compatCount A ω x₀ := by
      rw [Set.Finite.mem_toFinset] at hx₀Z
      simp only [Set.mem_setOf_eq] at hx₀Z
      omega
    have hex : ∃ k, ω k ∉ A k x₀ := ⟨Classical.choose (hN3 e.1 e.2.1 e.2.2), hmiss⟩
    have hφx : Classical.choose hex = i := by
      have : (if h : ∃ k, ω k ∉ A k x₀ then Classical.choose h else ⟨0, by omega⟩) = i := hφ
      rwa [dif_pos hex] at this
    have hmissi : ω i ∉ A i x₀ := by
      have hspec := Classical.choose_spec hex
      rwa [hφx] at hspec
    have hjcol_ne : Classical.choose (hN3 e.1 e.2.1 e.2.2) ≠ i :=
      (Classical.choose_spec (hN3 e.1 e.2.1 e.2.2)).1
    exact hjcol_ne (missing_unique A ω x₀ hge hmiss hmissi)

end Erdos550
