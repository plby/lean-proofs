import Wikipedia.HopfProblem.OrbitPairFinitePosetIterationAffine

/-!
# A uniform chain-cardinality bound through repeated subdivision

In a chain of nonempty faces, cardinality is injective: comparable faces
of equal size coincide. Consequently a bound on chain cardinalities is
preserved by the face-poset functor and by all its finite iterations.
-/

noncomputable section

universe u

open CategoryTheory Simplicial PartialOrder

namespace Wikipedia.HopfProblem.OrbitPair.FinitePoset

def ChainCardBound (P : Type u) [PartialOrder P] (N : ℕ) : Prop :=
  ∀ A : NonemptyFiniteChains P, A.finset.card ≤ N + 1

theorem chainCardBound_subdivision (P : Type u) [PartialOrder P] (N : ℕ)
    (h : ChainCardBound P N) : ChainCardBound (NonemptyFiniteChains P) N := by
  classical
  intro B
  let f : B.finset → Fin (N + 1) := fun A ↦
    ⟨A.val.finset.card - 1, by
      have ha := A.val.nonempty.card_pos
      have hb := h A.val
      omega⟩
  have hf : Function.Injective f := by
    intro A C hAC
    have he : A.val.finset.card = C.val.finset.card := by
      have he' := congrArg Fin.val hAC
      change A.val.finset.card - 1 = C.val.finset.card - 1 at he'
      have ha := A.val.nonempty.card_pos
      have hc := C.val.nonempty.card_pos
      omega
    apply Subtype.ext
    apply NonemptyFiniteChains.ext
    rcases B.comparable A C with hAC | hCA
    · exact Finset.eq_of_subset_of_card_le hAC he.symm.le
    · exact (Finset.eq_of_subset_of_card_le hCA he.le).symm
  simpa only [Fintype.card_coe, Fintype.card_fin] using Fintype.card_le_of_injective f hf

theorem iteratedChains_cardBound (P : PartOrd.{u}) (N : ℕ) (h : ChainCardBound P N)
    (r : ℕ) : ChainCardBound ((iteratedChains r).obj P) N := by
  induction r with
  | zero => exact h
  | succ r ih => exact chainCardBound_subdivision ((iteratedChains r).obj P) N ih

theorem chainCardBound_finite (P : Type u) [PartialOrder P] [Fintype P] :
    ChainCardBound P (Fintype.card P) := by
  intro A
  exact (Finset.card_le_univ A.finset).trans (Nat.le_succ _)

def simplexVertexChain (P : Type u) [PartialOrder P] (k : ℕ) (x : (nerve P) _⦋k⦌) :
    NonemptyFiniteChains P := by
  classical
  refine ⟨Finset.univ.image x.obj, Finset.image_nonempty.mpr Finset.univ_nonempty, ?_⟩
  intro a b
  obtain ⟨i, hi, he⟩ := Finset.mem_image.mp a.property
  obtain ⟨j, hj, hf⟩ := Finset.mem_image.mp b.property
  rcases le_total i j with hij | hji
  · exact Or.inl (by change a.val ≤ b.val; rw [← he, ← hf]; exact x.monotone hij)
  · exact Or.inr (by change b.val ≤ a.val; rw [← he, ← hf]; exact x.monotone hji)

theorem mem_simplexVertexChain (P : Type u) [PartialOrder P] (k : ℕ)
    (x : (nerve P) _⦋k⦌) (i : Fin (k + 1)) : x.obj i ∈ (simplexVertexChain P k x).finset := by
  classical
  exact Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩

end Wikipedia.HopfProblem.OrbitPair.FinitePoset
