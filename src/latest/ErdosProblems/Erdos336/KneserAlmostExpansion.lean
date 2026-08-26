import Mathlib
import ErdosProblems.Erdos336.KneserTheorem
import ErdosProblems.Erdos336.DenseCosetAddition

/- Ported from Lean 4.31.0 to 4.33.0; imports, helper namespaces, and elaboration adapted. -/
set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

namespace Erdos336

open scoped Pointwise

variable {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]

/-- If saturation by every nonzero proper subgroup grows `A` by at least one
full subgroup fibre, then Kneser gives expansion with loss at most one against
any nonempty `B`. -/
theorem card_add_add_one_ge_of_proper_saturation_growth
    {A B : Finset G} (hA : A.Nonempty) (hB : B.Nonempty)
    (hsize : A.card + B.card ≤ Fintype.card G + 1)
    (hsat : ∀ K : AddSubgroup G, K ≠ ⊥ → K ≠ ⊤ →
      A.card + (addSubgroupFinset K).card ≤
        (A + addSubgroupFinset K).card) :
    A.card + B.card ≤ (A + B).card + 1 := by
  let K : AddSubgroup G :=
    AddAction.stabilizer G (↑(A + B) : Set G)
  let H : Finset G := (A + B).addStab
  have hAB : (A + B).Nonempty := hA.add hB
  have hKH : addSubgroupFinset K = H := by
    ext x
    simp only [mem_addSubgroupFinset, H]
    change (x ∈ (K : Set G)) ↔ x ∈ (H : Set G)
    rw [Finset.coe_addStab hAB]
  have hzero : 0 ∈ H := Finset.zero_mem_addStab.mpr hAB
  have hAsub : A ⊆ A + H := by
    intro x hx
    exact Finset.mem_add.mpr ⟨x, hx, 0, hzero, by simp⟩
  have hBsub : B ⊆ B + H := by
    intro x hx
    exact Finset.mem_add.mpr ⟨x, hx, 0, hzero, by simp⟩
  have hkneser : (A + H).card + (B + H).card ≤
      (A + B).card + H.card := by
    simpa [H] using Finset.add_kneser A B
  by_cases hKbot : K = ⊥
  · have hHcard : H.card = 1 := by
      rw [← hKH, hKbot]
      simp [addSubgroupFinset]
    have hAc := Finset.card_le_card hAsub
    have hBc := Finset.card_le_card hBsub
    omega
  · by_cases hKtop : K = ⊤
    · have hHcard : H.card = Fintype.card G := by
        rw [← hKH, hKtop]
        simp [addSubgroupFinset]
      have hstabcard : H.card ≤ (A + B).card := by
        simpa [H] using (Finset.card_addStab_le_card (s := A + B))
      omega
    · have hsat' : A.card + H.card ≤ (A + H).card := by
        simpa [hKH] using hsat K hKbot hKtop
      have hBc := Finset.card_le_card hBsub
      omega

end Erdos336
