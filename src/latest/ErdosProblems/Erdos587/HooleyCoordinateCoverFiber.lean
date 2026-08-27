import ErdosProblems.Erdos587.NVDevelopment

/-! # A dense translated fiber in a finite abelian-group cover -/

open scoped Pointwise BigOperators

namespace Erdos587.CFP

theorem delta_exists_dense_cover_fiber {G : Type*} [AddCommGroup G] [DecidableEq G]
    (A P F : Finset G) (hA : A.Nonempty) (hcover : A ⊆ F + P)
    {C : ℕ} (hFcard : F.card ≤ C) :
    ∃ f ∈ F, ∃ X ⊆ P, A.card ≤ C * X.card ∧ ({f} : Finset G) + X ⊆ A := by
  classical
  let piece (f : G) := A.filter (fun a => a - f ∈ P)
  have hF : F.Nonempty := by
    obtain ⟨a, ha⟩ := hA
    obtain ⟨f, hf, _, _, _⟩ := Finset.mem_add.mp (hcover ha)
    exact ⟨f, hf⟩
  obtain ⟨f, hf, hmax⟩ := Finset.exists_max_image F (fun g => (piece g).card) hF
  have hcover' : A ⊆ F.biUnion piece := by
    intro a ha
    obtain ⟨g, hg, p, hp, hgp⟩ := Finset.mem_add.mp (hcover ha)
    apply Finset.mem_biUnion.mpr
    refine ⟨g, hg, Finset.mem_filter.mpr ⟨ha, ?_⟩⟩
    have heq : a - g = p := by rw [← hgp]; abel
    exact heq ▸ hp
  have hcount : A.card ≤ C * (piece f).card := by
    calc
      _ ≤ (F.biUnion piece).card := Finset.card_le_card hcover'
      _ ≤ ∑ g ∈ F, (piece g).card := Finset.card_biUnion_le
      _ ≤ ∑ _g ∈ F, (piece f).card := Finset.sum_le_sum (fun g hg => hmax g hg)
      _ = F.card * (piece f).card := by simp
      _ ≤ C * (piece f).card := Nat.mul_le_mul_right _ hFcard
  let X := (piece f).image (fun a => a - f)
  have hXcard : X.card = (piece f).card :=
    Finset.card_image_of_injective _ (fun _ _ h => sub_left_injective h)
  refine ⟨f, hf, X, ?_, ?_, ?_⟩
  · intro x hx
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hx
    exact (Finset.mem_filter.mp ha).2
  · rwa [hXcard]
  · intro a ha
    obtain ⟨g, hg, x, hx, hsum⟩ := Finset.mem_add.mp ha
    have hgf : g = f := Finset.mem_singleton.mp hg
    subst g
    obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hx
    have hab : a = b := by rw [← hsum]; abel
    exact hab ▸ (Finset.mem_filter.mp hb).1

end Erdos587.CFP
