import ErdosProblems.Erdos19.CompatibleColorings
import ErdosProblems.Erdos19.MediumProjectiveColoring

/-! # Extending a large-edge coloring across the medium edges

The old colors are preserved. Outside the reserved palette the original
coverage bound remains unchanged; inside it, coverage increases by at most
the prescribed medium-class bound.
-/

namespace Erdos19.SetHypergraph

open Finset

attribute [local instance] Classical.propDecidable

variable {V : Type*} [Fintype V]

theorem extend_coloring_into_palette (L M : SetHypergraph V) (n A p : ℕ)
    (color : L.EdgeColoring (Fin n)) (hbounded : L.IsCoverBoundedColoring color A)
    (palette : Finset (Fin n)) (cM : M.EdgeColoring palette)
    (hcompatible : ∀ e : M, ∀ f : L, (e.1 ∩ f.1).Nonempty →
      (cM.color e).1 ≠ color.color f)
    (hcover : ∀ x, (M.coveredVertices {e : M | cM.color e = x}).ncard ≤ p) :
    ∃ c : (L ∪ M).EdgeColoring (Fin n),
      (∀ e : L, c.color ⟨e.1, Or.inl e.2⟩ = color.color e) ∧
      (∀ e : M, e.1 ∉ L → c.color ⟨e.1, Or.inr e.2⟩ ∈ palette) ∧
      (∀ x, ((L ∪ M).coveredVertices {e | c.color e = x}).ncard ≤
        (L.coveredVertices {e | color.color e = x}).ncard + p) ∧
      (∀ x, x ∉ palette →
        ({e : ↥(L ∪ M) | c.color e = x} : Set ↥(L ∪ M)).ncard ≤ 1 ∨
          ((L ∪ M).coveredVertices {e | c.color e = x}).ncard ≤ A) := by
  classical
  let cM' : M.EdgeColoring (Fin n) :=
    { color := fun e ↦ (cM.color e).1
      valid := fun {e f} hne hinter heq ↦ cM.valid hne hinter (Subtype.ext heq) }
  have hcross : ∀ e : L, ∀ f : M, (e.1 ∩ f.1).Nonempty → color.color e ≠ cM'.color f := by
    intro e f hinter
    exact (hcompatible f e (by simpa only [Set.inter_comm] using hinter)).symm
  have hMcover (x : Fin n) : (M.coveredVertices {e | cM'.color e = x}).ncard ≤ p := by
    by_cases hx : x ∈ palette
    · have hclass : ({e : M | cM'.color e = x} : Set M) =
          {e : M | cM.color e = ⟨x, hx⟩} := by
        ext e
        change (cM.color e).1 = x ↔ cM.color e = ⟨x, hx⟩
        exact ⟨fun h ↦ Subtype.ext h, fun h ↦ congrArg (fun y : palette ↦ y.1) h⟩
      simpa only [hclass] using hcover ⟨x, hx⟩
    · have hclass : ({e : M | cM'.color e = x} : Set M) = ∅ := by
        apply Set.eq_empty_iff_forall_notMem.mpr
        intro e he
        apply hx
        have hmem := (cM.color e).2
        change (cM.color e).1 = x at he
        simpa only [he] using hmem
      simp [hclass, coveredVertices]
  let c := L.unionColoring M color cM' hcross
  refine ⟨c, ?_, ?_, ?_, ?_⟩
  · intro e
    exact L.unionColoring_left M color cM' hcross e
  · intro e he
    rw [show c.color ⟨e.1, Or.inr e.2⟩ = cM'.color e from
      L.unionColoring_right M color cM' hcross e he]
    exact (cM.color e).2
  · intro x
    exact (L.unionColoring_covered_card_le M color cM' hcross x).trans
      (Nat.add_le_add_left (hMcover x) _)
  · intro x hx
    apply L.unionColoring_coverBounded_left M color cM' hcross x A _ (hbounded x)
    intro e he
    apply hx
    have hmem := (cM.color e).2
    change (cM.color e).1 = x at he
    simpa only [he] using hmem

theorem eventually_extend_medium_edges_palette (R s a : ℕ)
    (hR : 0 < R) (hs : 0 < s) (ha : 0 < a) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      ∀ L M : SetHypergraph (Fin n), L.IsLinear → M.IsLinear →
      ∀ m : ℕ, ∀ color : L.EdgeColoring (Fin m), ∀ A : ℕ, L.IsCoverBoundedColoring color A →
      ∀ palette : Finset (Fin m), ∀ t : ℕ, 2 ≤ t →
        (∀ e : L, color.color e ∈ palette →
          projectiveScale n - projectiveScale n / t ≤ e.1.ncard) →
        (∀ e : M, 16 * a * s + 1 ≤ e.1.ncard) → (∀ e : M, e.1.ncard ≤ R) →
        2 * (n / s) ≤ palette.card →
        ∃ c : (L ∪ M).EdgeColoring (Fin m),
          (∀ e : L, c.color ⟨e.1, Or.inl e.2⟩ = color.color e) ∧
          (∀ e : M, e.1 ∉ L → c.color ⟨e.1, Or.inr e.2⟩ ∈ palette) ∧
          (∀ x, ((L ∪ M).coveredVertices {e | c.color e = x}).ncard ≤
            (L.coveredVertices {e | color.color e = x}).ncard + n / a) ∧
          (∀ x, x ∉ palette →
            ({e : ↥(L ∪ M) | c.color e = x} : Set ↥(L ∪ M)).ncard ≤ 1 ∨
              ((L ∪ M).coveredVertices {e | c.color e = x}).ncard ≤ A) := by
  obtain ⟨N, hN⟩ := eventually_color_medium_with_coverage_palette R s a hR hs ha
  refine ⟨N, ?_⟩
  intro n hn L M hL hM m color A hbounded palette t ht hcoremin hmin hmax hpalette
  obtain ⟨cM, hcompatible, hcover⟩ := hN n hn L M hL hM (Fin m) color palette t ht
    hcoremin hmin hmax hpalette
  exact L.extend_coloring_into_palette M m A (n / a) color hbounded palette cM hcompatible hcover


theorem eventually_extend_medium_edges (R s a : ℕ)
    (hR : 0 < R) (hs : 0 < s) (ha : 0 < a) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      ∀ L M : SetHypergraph (Fin n), L.IsLinear → M.IsLinear →
      ∀ color : L.EdgeColoring (Fin n), ∀ A : ℕ, L.IsCoverBoundedColoring color A →
      ∀ palette : Finset (Fin n), ∀ t : ℕ, 2 ≤ t →
        (∀ e : L, color.color e ∈ palette →
          projectiveScale n - projectiveScale n / t ≤ e.1.ncard) →
        (∀ e : M, 16 * a * s + 1 ≤ e.1.ncard) → (∀ e : M, e.1.ncard ≤ R) →
        2 * (n / s) ≤ palette.card →
        ∃ c : (L ∪ M).EdgeColoring (Fin n),
          (∀ e : L, c.color ⟨e.1, Or.inl e.2⟩ = color.color e) ∧
          (∀ e : M, e.1 ∉ L → c.color ⟨e.1, Or.inr e.2⟩ ∈ palette) ∧
          (∀ x, ((L ∪ M).coveredVertices {e | c.color e = x}).ncard ≤
            (L.coveredVertices {e | color.color e = x}).ncard + n / a) ∧
          (∀ x, x ∉ palette →
            ({e : ↥(L ∪ M) | c.color e = x} : Set ↥(L ∪ M)).ncard ≤ 1 ∨
              ((L ∪ M).coveredVertices {e | c.color e = x}).ncard ≤ A) := by
  obtain ⟨N, hN⟩ := eventually_color_medium_with_coverage R s a hR hs ha
  refine ⟨N, ?_⟩
  intro n hn L M hL hM color A hbounded palette t ht hcoremin hmin hmax hpalette
  obtain ⟨cM, hcompatible, hcover⟩ := hN n hn L M hL hM color palette t ht
    hcoremin hmin hmax hpalette
  exact L.extend_coloring_into_palette M n A (n / a) color hbounded palette cM hcompatible hcover

#print axioms eventually_extend_medium_edges_palette

#print axioms eventually_extend_medium_edges

end Erdos19.SetHypergraph
