import Mathlib

open scoped BigOperators
open Filter Asymptotics

noncomputable section


namespace Erdos772

open scoped Classical in
def IsSidon {α : Type*} [DecidableEq α] (a : α → ℕ) (S : Finset α) : Prop :=
  ∀ i ∈ S, ∀ j ∈ S, ∀ u ∈ S, ∀ v ∈ S,
    a i + a j = a u + a v → ({i, j} : Finset α) = {u, v}

end Erdos772

namespace Erdos772

open scoped Classical in
def Guarantees (k n r : ℕ) : Prop :=
  ∀ (A : Finset ℕ), A.card = n →
    (∀ t, ((A.product A).filter (fun p => p.1 + p.2 = t)).card ≤ k) →
    ∃ S : Finset ℕ, S ⊆ A ∧ IsSidon id S ∧ r ≤ S.card

end Erdos772

namespace Erdos772

open scoped Classical in
noncomputable def guaranteedSizes (k n : ℕ) : Finset ℕ := by
  classical
  exact (Finset.range (n + 1)).filter (Guarantees k n)

open scoped Classical in
lemma guaranteedSizes_nonempty (k n : ℕ) : (guaranteedSizes k n).Nonempty := by
  classical
  refine ⟨0, ?_⟩
  simp [guaranteedSizes, Guarantees]
  intro A hA hrep
  exact ⟨∅, by simp [IsSidon]⟩

end Erdos772

namespace Erdos772

open scoped Classical in
noncomputable def H (k n : ℕ) : ℕ :=
  (guaranteedSizes k n).max' (guaranteedSizes_nonempty k n)

end Erdos772

namespace Erdos772

open scoped Classical in
theorem erdos_772 (k : ℕ) (_hk : 1 ≤ k) :
    Tendsto (fun n : ℕ =>
      (H k n : ℝ) / (n : ℝ) ^ ((1 : ℝ) / 2)) atTop atTop ∧
    ∃ c : ℝ, 0 < c ∧
      ∀ᶠ n : ℕ in atTop,
        (n : ℝ) ^ ((1 : ℝ) / 2 + c) < H k n := by
  sorry

end Erdos772

end
