/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/- This file has been modified for Lean/Mathlib 4.33.0. -/
/-
Erdős Problem 330, positive upper density formulation.
Informal authors: GPT-5.5 Pro, David Turturean.
Formal authors: Codex, GPT-5.5 Pro, Allen Graham Hart.
Source: https://www.erdosproblems.com/forum/thread/330#post-6271
https://github.com/AllenGrahamHart/FormalConjectures-Bench/tree/6160036caab0dcee80395ba3beb7b6ef2731604e/formalizations/erdos330
Original Lean/Mathlib version: 4.27.0.
-/
import Mathlib.Combinatorics.Hall.Finite
import ErdosProblems.Erdos330.QuadraticResidue

set_option linter.mathlibStandardSet false
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-!
# Finite choice lemmas for Erdős Problem 330

These combinatorial lemmas support the safe-pairs part of the CRT gadget.
-/

namespace Erdos330

theorem exists_disjoint_subsets_card_eq {ι : Type*} [DecidableEq ι]
    (U : Finset ι) (a b : ℕ) (hab : a + b ≤ U.card) :
    ∃ S T : Finset ι,
      S ⊆ U ∧ T ⊆ U ∧ Disjoint S T ∧ S.card = a ∧ T.card = b := by
  obtain ⟨S, hSU, hScard⟩ :=
    Finset.exists_subset_card_eq (s := U) (n := a) (by omega)
  have hbU : b ≤ (U \ S).card := by
    rw [Finset.card_sdiff_of_subset hSU, hScard]
    omega
  obtain ⟨T, hTUS, hTcard⟩ := Finset.exists_subset_card_eq (s := U \ S) (n := b) hbU
  refine ⟨S, T, hSU, ?_, ?_, hScard, hTcard⟩
  · exact fun x hx => (Finset.mem_sdiff.mp (hTUS hx)).1
  · exact Finset.disjoint_left.mpr fun x hxS hxT => (Finset.mem_sdiff.mp (hTUS hxT)).2 hxS

theorem choose_disjoint_avoiding_two_forbidden_sets {ι : Type*} [DecidableEq ι]
    (U C0 D0 : Finset ι)
    (_hC : C0 ⊆ U) (_hD : D0 ⊆ U) (hdisj : Disjoint C0 D0)
    (a b : ℕ)
    (ha : a ≤ (U \ C0).card)
    (hb : b ≤ (U \ D0).card)
    (hab : a + b ≤ U.card) :
    ∃ S T : Finset ι,
      S ⊆ U \ C0 ∧ T ⊆ U \ D0 ∧ Disjoint S T ∧
      S.card = a ∧ T.card = b := by
  classical
  let slot := Sum (Fin a) (Fin b)
  let allowed : slot → Finset ι := fun s =>
    match s with
    | Sum.inl _ => U \ C0
    | Sum.inr _ => U \ D0
  have hHall : ∀ s : Finset slot, s.card ≤ (s.biUnion allowed).card := by
    intro s
    by_cases hs_empty : s = ∅
    · simp [hs_empty]
    · by_cases hLeft : ∃ i : Fin a, Sum.inl i ∈ s
      · by_cases hRight : ∃ j : Fin b, Sum.inr j ∈ s
        · have hbi : s.biUnion allowed = U := by
            ext x
            constructor
            · intro hx
              rcases Finset.mem_biUnion.mp hx with ⟨sl, _hsl, hxallow⟩
              cases sl with
              | inl _ => exact (Finset.mem_sdiff.mp hxallow).1
              | inr _ => exact (Finset.mem_sdiff.mp hxallow).1
            · intro hxU
              rcases hLeft with ⟨i, hi⟩
              rcases hRight with ⟨j, hj⟩
              by_cases hxC : x ∈ C0
              · refine Finset.mem_biUnion.mpr ⟨Sum.inr j, hj, ?_⟩
                exact Finset.mem_sdiff.mpr ⟨hxU, by
                  intro hxD
                  exact (Finset.disjoint_left.mp hdisj hxC hxD)⟩
              · refine Finset.mem_biUnion.mpr ⟨Sum.inl i, hi, ?_⟩
                exact Finset.mem_sdiff.mpr ⟨hxU, hxC⟩
          calc
            s.card ≤ Fintype.card slot := Finset.card_le_univ s
            _ = a + b := by simp [slot]
            _ ≤ U.card := hab
            _ = (s.biUnion allowed).card := by rw [hbi]
        · have hbi : s.biUnion allowed = U \ C0 := by
            ext x
            constructor
            · intro hx
              rcases Finset.mem_biUnion.mp hx with ⟨sl, hsl, hxallow⟩
              cases sl with
              | inl _ => exact hxallow
              | inr j => exact False.elim (hRight ⟨j, hsl⟩)
            · intro hx
              rcases hLeft with ⟨i, hi⟩
              exact Finset.mem_biUnion.mpr ⟨Sum.inl i, hi, hx⟩
          calc
            s.card ≤ Fintype.card (Fin a) := by
              let f : {x // x ∈ s} → Fin a
                | ⟨Sum.inl i, _⟩ => i
                | ⟨Sum.inr j, hj⟩ => False.elim (hRight ⟨j, hj⟩)
              have hf : Function.Injective f := by
                rintro ⟨sx, hsx⟩ ⟨sy, hsy⟩ hxy
                cases sx with
                | inl ix =>
                  cases sy with
                  | inl _ =>
                    simp [f] at hxy
                    subst hxy
                    rfl
                  | inr jy => exact False.elim (hRight ⟨jy, hsy⟩)
                | inr jx => exact False.elim (hRight ⟨jx, hsx⟩)
              have := Fintype.card_le_of_injective f hf
              simpa using this
            _ = a := by simp
            _ ≤ (U \ C0).card := ha
            _ = (s.biUnion allowed).card := by rw [hbi]
      · have hbi : s.biUnion allowed = U \ D0 := by
          ext x
          constructor
          · intro hx
            rcases Finset.mem_biUnion.mp hx with ⟨sl, hsl, hxallow⟩
            cases sl with
            | inl i => exact False.elim (hLeft ⟨i, hsl⟩)
            | inr _ => exact hxallow
          · intro hx
            have hRightNonempty : ∃ j : Fin b, Sum.inr j ∈ s := by
              obtain ⟨sl, hsl⟩ := Finset.nonempty_iff_ne_empty.mpr hs_empty
              cases sl with
              | inl i => exact False.elim (hLeft ⟨i, hsl⟩)
              | inr j => exact ⟨j, hsl⟩
            rcases hRightNonempty with ⟨j, hj⟩
            exact Finset.mem_biUnion.mpr ⟨Sum.inr j, hj, hx⟩
        calc
          s.card ≤ Fintype.card (Fin b) := by
            let f : {x // x ∈ s} → Fin b
              | ⟨Sum.inl i, hi⟩ => False.elim (hLeft ⟨i, hi⟩)
              | ⟨Sum.inr j, _⟩ => j
            have hf : Function.Injective f := by
              rintro ⟨sx, hsx⟩ ⟨sy, hsy⟩ hxy
              cases sx with
              | inl ix => exact False.elim (hLeft ⟨ix, hsx⟩)
              | inr jx =>
                cases sy with
                | inl iy => exact False.elim (hLeft ⟨iy, hsy⟩)
                | inr _ =>
                  simp [f] at hxy
                  subst hxy
                  rfl
            have := Fintype.card_le_of_injective f hf
            simpa using this
          _ = b := by simp
          _ ≤ (U \ D0).card := hb
          _ = (s.biUnion allowed).card := by rw [hbi]
  obtain ⟨f, hfinj, hfmem⟩ :=
    (Finset.all_card_le_biUnion_card_iff_existsInjective' allowed).mp hHall
  let S : Finset ι := Finset.univ.image fun i : Fin a => f (Sum.inl i)
  let T : Finset ι := Finset.univ.image fun j : Fin b => f (Sum.inr j)
  refine ⟨S, T, ?_, ?_, ?_, ?_, ?_⟩
  · intro x hx
    rcases Finset.mem_image.mp hx with ⟨i, _hi, rfl⟩
    exact hfmem (Sum.inl i)
  · intro x hx
    rcases Finset.mem_image.mp hx with ⟨j, _hj, rfl⟩
    exact hfmem (Sum.inr j)
  · exact Finset.disjoint_left.mpr (by
      intro x hxS hxT
      rcases Finset.mem_image.mp hxS with ⟨i, _hi, hix⟩
      rcases Finset.mem_image.mp hxT with ⟨j, _hj, hjx⟩
      have hEq : f (Sum.inl i) = f (Sum.inr j) := by rw [hix, hjx]
      have := hfinj hEq
      cases this)
  · dsimp [S]
    rw [Finset.card_image_of_injective]
    · simp
    · intro i j hij
      exact Sum.inl.inj (hfinj hij)
  · dsimp [T]
    rw [Finset.card_image_of_injective]
    · simp
    · intro i j hij
      exact Sum.inr.inj (hfinj hij)

end Erdos330
