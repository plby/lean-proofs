import Arxiv.Arxiv2411_18291.CliqueFamilyBoundedness

/-!
# A boundary degree bound controls individual edge multiplicities

An edge contains a face of one smaller size, and its nonnegative boundary
coordinate is at most the degree at that face. Hence a sparse clique
boundary has sublinear maximum edge multiplicity.
-/

open Finset

noncomputable section

namespace Arxiv2411_18291

variable {V : Type*} [Fintype V] [DecidableEq V] {q r : ℕ}

theorem boundary_indicator_le_degree (D : Finset (Block V q))
    (e : Block V (r + 1)) (T : Finset V) (hT : T ⊆ e.val) :
    boundary (r + 1) (indicator D) e ≤ degree (boundary (r + 1) (indicator D)) T := by
  have hnonneg (f : Block V (r + 1)) : 0 ≤ boundary (r + 1) (indicator D) f := by
    rw [boundary_indicator]
    exact Nat.cast_nonneg _
  have h := single_le_sum (s := univ)
    (f := fun f : Block V (r + 1) => if T ⊆ f.val then boundary (r + 1) (indicator D) f else 0)
    (fun f _ => by
      split_ifs
      · exact hnonneg f
      · exact le_rfl) (mem_univ e)
  simpa only [degree, if_pos hT] using h

theorem IsCliqueFamilyBounded.multiplicity_lt {D : Finset (Block V q)} {θ : ℝ}
    (hD : IsCliqueFamilyBounded r D θ) (e : Block V (r + 1)) :
    ((D.filter fun Q => e.val ⊆ Q.val).card : ℝ) < θ * Fintype.card V := by
  obtain ⟨T, hTe, hT⟩ := exists_subset_card_eq (s := e.val)
    (show r ≤ e.val.card by rw [e.property]; omega)
  have h := boundary_indicator_le_degree D e T hTe
  rw [boundary_indicator] at h
  have hreal : ((D.filter fun Q => e.val ⊆ Q.val).card : ℝ) ≤
      ((degree (boundary (r + 1) (indicator D)) T : ℤ) : ℝ) := by exact_mod_cast h
  exact hreal.trans_lt (hD ⟨T, hT⟩)

end Arxiv2411_18291
