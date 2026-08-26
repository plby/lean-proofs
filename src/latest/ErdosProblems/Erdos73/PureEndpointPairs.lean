import ErdosProblems.Erdos73.Foundations

/-! Finite Ramsey selection of separated, nested, or alternating endpoint pairs. -/

namespace Erdos73
noncomputable section
open scoped Classical

open Finset

inductive EndpointPairShape
  | series
  | nested
  | crossing
  deriving DecidableEq

def EndpointPairShape.Rel (s : EndpointPairShape) (a b c d : ℕ) : Prop :=
  match s with
  | .series => b < c ∨ d < a
  | .nested => (a < c ∧ d < b) ∨ (c < a ∧ b < d)
  | .crossing => (a < c ∧ c < b ∧ b < d) ∨ (c < a ∧ a < d ∧ d < b)

theorem EndpointPairShape.rel_symm (s : EndpointPairShape) (a b c d : ℕ) :
    s.Rel a b c d → s.Rel c d a b := by
  cases s <;> simp only [Rel] <;> tauto

theorem endpointPairs_crossing_of_not_series_not_nested {a b c d : ℕ}
    (hab : a < b) (hcd : c < d) (hneq : a ≠ c ∧ a ≠ d ∧ b ≠ c ∧ b ≠ d)
    (hs : ¬ EndpointPairShape.series.Rel a b c d)
    (hn : ¬ EndpointPairShape.nested.Rel a b c d) :
    EndpointPairShape.crossing.Rel a b c d := by
  dsimp only [EndpointPairShape.Rel] at hs hn ⊢
  omega

def pureEndpointPairBound (t : ℕ) : ℕ :=
  twoColorRamseyBound t (twoColorRamseyBound t t)

theorem exists_pure_endpoint_pairs {I : Type*} (s : Finset I) (lo hi : I → ℕ)
    (hlo : ∀ i ∈ s, lo i < hi i)
    (hneq : ∀ i ∈ s, ∀ j ∈ s, i ≠ j →
      lo i ≠ lo j ∧ lo i ≠ hi j ∧ hi i ≠ lo j ∧ hi i ≠ hi j)
    (t : ℕ) (hsize : pureEndpointPairBound t ≤ s.card) :
    ∃ u : Finset I, u ⊆ s ∧ t ≤ u.card ∧ ∃ shape : EndpointPairShape,
      (u : Set I).Pairwise (fun i j => shape.Rel (lo i) (hi i) (lo j) (hi j)) := by
  let R := fun i j => EndpointPairShape.series.Rel (lo i) (hi i) (lo j) (hi j)
  let N := fun i j => EndpointPairShape.nested.Rel (lo i) (hi i) (lo j) (hi j)
  have hR : Std.Symm R := ⟨fun i j => EndpointPairShape.rel_symm .series _ _ _ _⟩
  have hN : Std.Symm N := ⟨fun i j => EndpointPairShape.rel_symm .nested _ _ _ _⟩
  obtain ⟨u, hus, hu | hu⟩ := exists_pairwise_or_pairwise_compl R hR t
    (twoColorRamseyBound t t) s hsize
  · exact ⟨u, hus, hu.1, .series, hu.2⟩
  · obtain ⟨v, hvu, hv | hv⟩ := exists_pairwise_or_pairwise_compl N hN t t u hu.1
    · exact ⟨v, hvu.trans hus, hv.1, .nested, hv.2⟩
    · refine ⟨v, hvu.trans hus, hv.1, .crossing, ?_⟩
      intro i hi j hj hij
      exact endpointPairs_crossing_of_not_series_not_nested
        (hlo i (hus (hvu hi))) (hlo j (hus (hvu hj)))
        (hneq i (hus (hvu hi)) j (hus (hvu hj)) hij)
        (hu.2 (hvu hi) (hvu hj) hij) (hv.2 hi hj hij)

end
end Erdos73
