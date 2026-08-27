/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos4b.FGKMTNaturalBatches

/-! # Extending dependent assignments on disjoint literal batches -/

namespace Erdos4b.FGKMT

noncomputable section

theorem exists_dependent_batch_extension {I J : Type*} {T : I → Type*}
    (B : J → Finset I) (hB : ∀ j k, j ≠ k → Disjoint (B j) (B k))
    (f : ∀ j, ∀ i : B j, T i.val) (g₀ : ∀ i, T i) :
    ∃ g : ∀ i, T i, ∀ j, ∀ i : B j, g i.val = f j i := by
  classical
  let g (i : I) : T i :=
    if h : ∃ j, i ∈ B j then f h.choose ⟨i, h.choose_spec⟩ else g₀ i
  refine ⟨g, ?_⟩
  intro j i
  have hi : ∃ k, i.val ∈ B k := ⟨j, i.property⟩
  change (if h : ∃ k, i.val ∈ B k then f h.choose ⟨i.val, h.choose_spec⟩ else g₀ i.val) = _
  rw [dif_pos hi]
  have hj : hi.choose = j := by
    by_contra hne
    exact Finset.disjoint_left.mp (hB hi.choose j hne) hi.choose_spec i.property
  have hcongr {k l : J} (hkl : k = l) (q : I) (hk : q ∈ B k) (hl : q ∈ B l) :
      f k ⟨q, hk⟩ = f l ⟨q, hl⟩ := by
    subst l
    rfl
  exact hcongr hj i.val hi.choose_spec i.property

end

end Erdos4b.FGKMT
