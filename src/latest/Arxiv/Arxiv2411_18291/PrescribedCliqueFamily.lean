import Arxiv.Arxiv2411_18291.PrescribedCliqueSelection
import Arxiv.Arxiv2411_18291.CliqueRefinementDegrees
import Arxiv.Arxiv2411_18291.CliquePairRootDegrees

/-! # An actual bounded clique family through every prescribed root edge -/

open Finset

noncomputable section

namespace Arxiv2411_18291

theorem exists_prescribed_clique_family {V : Type*} [Fintype V] [DecidableEq V]
    {q r : ℕ} (hqr : r + 1 ≤ q) (hn : q ≤ Fintype.card V) (hnpos : 0 < Fintype.card V)
    (B : Hypergraph V (r + 1)) (C : Block V (r + 1) → Finset (Block V q))
    {θ η : ℝ} (hθ : 0 ≤ θ) (hη : 0 < η) (hB : IsGraphBounded B θ)
    (hC : ∀ e Q, Q ∈ C e → e.val ⊆ Q.val)
    (hcount : ∀ e, η * (Fintype.card V : ℝ) ^ (q - (r + 1)) ≤ (C e).card)
    (hfailure : Fintype.card (Block V r) *
      Real.exp (-(2 * (r + 1).factorial * θ * Fintype.card V / η / 3)) < 1) :
    ∃ Q : B → Block V q, (∀ e, Q e ∈ C e.val) ∧
      IsCliqueFamilyBounded r (univ.image Q)
        ((q - r : ℕ) * (4 * (r + 1).factorial * θ / η)) := by
  classical
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hqr
  obtain ⟨a, _, ha⟩ := exists_subset_card_eq (s := (univ : Finset V))
    (by simpa only [card_univ] using (show r + 1 ≤ Fintype.card V by omega))
  let e₀ : Block V (r + 1) := ⟨a, ha⟩
  let enum : Fin B.card ≃ B := B.equivFin.symm
  let E : ℕ → Block V (r + 1) :=
    fun i => if hi : i < B.card then (enum ⟨i, hi⟩).val else e₀
  have hE (i : Fin B.card) : E i = (enum i).val := by
    dsimp only [E]
    rw [dif_pos i.isLt]
  have hroots (S : Block V r) :
      (familyDegree (fun i : Fin B.card => E i) S.val : ℝ) ≤ θ * Fintype.card V := by
    simp only [hE, familyDegree_reindex, familyDegree_subtype_eq]
    exact (hB S).le
  have hcontains (i : ℕ) : C (E i) ⊆ cliqueEnlargements (E i) d := by
    intro Q hQ
    exact mem_filter.mpr ⟨mem_univ _, hC (E i) Q hQ⟩
  have hcounts (i : ℕ) : η * (Fintype.card V : ℝ) ^ d ≤ (C (E i)).card := by
    simpa only [Nat.add_sub_cancel_left] using hcount (E i)
  obtain ⟨Z, hs, hZ⟩ := exists_prescribed_clique_selection E (fun i => C (E i))
    hθ hη hnpos hcontains hcounts hroots hfailure
  let Q : B → Block V (r + 1 + d) := fun e => Z (enum.symm e)
  refine ⟨Q, ?_, cliqueImage_bounded_of_face_bound Q (by omega) ?_⟩
  · intro e
    have h := hs (enum.symm e)
    simpa only [hE, Equiv.apply_symm_apply] using h
  · intro S
    simpa only [Q, familyDegree_reindex] using hZ S

end Arxiv2411_18291
