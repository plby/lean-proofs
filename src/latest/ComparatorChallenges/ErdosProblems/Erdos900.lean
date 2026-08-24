/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import Mathlib

open Filter
open scoped SimpleGraph Topology

namespace Erdos88.Fourier

universe u

def boolWeight {I : Type u} [Fintype I] [DecidableEq I] (x : I → Bool) : ℕ :=
  (Finset.univ.filter fun i ↦ x i).card

def BoolSlice (I : Type u) [Fintype I] [DecidableEq I] (s : ℕ) :=
  {x : I → Bool // boolWeight x = s}

noncomputable instance {I : Type u} [Fintype I] [DecidableEq I] (s : ℕ) :
    Fintype (BoolSlice I s) := by
  letI : Fintype (I → Bool) := Pi.instFintype
  exact Fintype.ofInjective Subtype.val Subtype.val_injective

end Erdos88.Fourier

namespace Erdos88.Concentration

noncomputable def uniformProbability {Ω : Type*} [Fintype Ω]
    (P : Ω → Prop) : ℝ := by
  classical
  exact ((Finset.univ.filter P).card : ℝ) / Fintype.card Ω

end Erdos88.Concentration

namespace Erdos900

abbrev Density := Set.Ioi (1 / 2 : ℝ)

noncomputable def densityAtHalf : Filter Density :=
  Filter.comap ((↑) : Density → ℝ) (𝓝[>] (1 / 2 : ℝ))

noncomputable def edgeBudget (c : ℝ) (n : ℕ) : ℕ := ⌊c * n⌋₊

def boolSliceNonempty {I : Type*} [Fintype I] [DecidableEq I]
    {m : ℕ} (hm : m ≤ Fintype.card I) : Nonempty (Erdos88.Fourier.BoolSlice I m) := by
  classical
  obtain ⟨S, _hS, hcard⟩ := Finset.exists_subset_card_eq
    (show m ≤ (Finset.univ : Finset I).card by simpa using hm)
  refine ⟨⟨fun i ↦ decide (i ∈ S), ?_⟩⟩
  simpa [Erdos88.Fourier.boolWeight] using hcard

def HasLongPath (n : ℕ) (a : ℝ) (G : SimpleGraph (Fin n)) : Prop :=
  SimpleGraph.pathGraph (⌈a * n⌉₊ + 1) ⊑ G

abbrev Edge (n : ℕ) := ↥((⊤ : SimpleGraph (Fin n)).edgeFinset)

def graphFromBits {n : ℕ} (G : Edge n → Bool) : SimpleGraph (Fin n) :=
  SimpleGraph.fromEdgeSet
    {e | ∃ h : e ∈ (⊤ : SimpleGraph (Fin n)).edgeFinset,
      G ⟨e, h⟩ = true}

noncomputable def edgeEquiv (n : ℕ) : Fin (n.choose 2) ≃ Edge n :=
  (((⊤ : SimpleGraph (Fin n)).edgeFinset.equivFinOfCardEq
    (by simpa using
      SimpleGraph.card_edgeFinset_top_eq_card_choose_two (V := Fin n))).symm)

noncomputable def canonicalGraph (n : ℕ) (bits : Fin (n.choose 2) → Bool) :
    SimpleGraph (Fin n) :=
  graphFromBits fun e ↦ bits ((edgeEquiv n).symm e)

noncomputable def fixedPathProbability (c a : ℝ) (n : ℕ) : ℝ := by
  classical
  let m := edgeBudget c n
  if h : m ≤ n.choose 2 then
    letI : Nonempty (Erdos88.Fourier.BoolSlice (Fin (n.choose 2)) m) :=
      boolSliceNonempty (by simpa using h)
    exact Erdos88.Concentration.uniformProbability
      (fun omega : Erdos88.Fourier.BoolSlice (Fin (n.choose 2)) m ↦
        HasLongPath n a (canonicalGraph n omega.1))
  else
    exact 0

def WHP (c a : ℝ) : Prop :=
  Tendsto (fixedPathProbability c a) atTop (𝓝 1)

theorem erdos_900 :
    ∃ f : Density → ℝ,
      (∀ c, 0 < f c ∧ f c < 1) ∧
      Tendsto f densityAtHalf (𝓝 0) ∧
      Tendsto f atTop (𝓝 1) ∧
      ∀ c : Density, WHP (c : ℝ) (f c) := by
  sorry

end Erdos900
