import Arxiv.Arxiv2411_18291.FiniteFractionalBoost

/-! # Decoder families supplied by relative clique counts -/

open Finset

noncomputable section

namespace Arxiv2411_18291

theorem fractional_boost_count_bounds (q r n : ℕ) (G : Hypergraph (Fin n) (r + 1))
    {ε : ℝ}
    (hcount : ∀ e ∈ G,
      |((rootedCliques G e q).card : ℝ) -
        (n : ℝ) ^ (q - (r + 1)) / (q - (r + 1)).factorial| ≤
          ε * ((n : ℝ) ^ (q - (r + 1)) / (q - (r + 1)).factorial))
    (hdecode : ∀ e ∈ G,
      |((rootedCliques G e (q + (r + 1))).card : ℝ) - (n : ℝ) ^ q / q.factorial| ≤
        (1 / 2) * ((n : ℝ) ^ q / q.factorial)) :
    let d : ℝ := (n : ℝ) ^ (q - (r + 1)) / (q - (r + 1)).factorial
    let L : ℝ := (n : ℝ) ^ q / (2 * q.factorial)
    let Z (e : Block (Fin n) (r + 1)) :=
      (cliqueFamily G (q + (r + 1))).filter fun z => e.val ⊆ z.val
    (∀ e ∈ G, ∀ z ∈ Z e, e.val ⊆ z.val) ∧
      (∀ e ∈ G, ∀ z ∈ Z e, cliqueEdges (r + 1) z ⊆ G) ∧
        (∀ e ∈ G, L ≤ ((Z e).card : ℝ)) ∧
          ∀ e ∈ G,
            |(((cliqueFamily G q).filter fun Q => e.val ⊆ Q.val).card : ℝ) - d| ≤
              2 * (ε * d / 2) := by
  dsimp only
  let Z (e : Block (Fin n) (r + 1)) :=
    (cliqueFamily G (q + (r + 1))).filter fun z => e.val ⊆ z.val
  have heclique (e : Block (Fin n) (r + 1)) (he : e ∈ G) : cliqueEdges (r + 1) e ⊆ G := by
    intro f hf
    have hfe : f = e := Subtype.ext (eq_of_subset_of_card_le
      ((mem_cliqueEdges _ _).mp hf) (by rw [f.property, e.property]))
    rwa [hfe]
  refine ⟨fun _ _ _ hz => (mem_filter.mp hz).2,
    fun _ _ _ hz => (mem_filter.mp (mem_filter.mp hz).1).2, ?_, ?_⟩
  · intro e he
    have hh := hdecode e he
    rw [rootedCliques_eq_filter_cliqueFamily G e (heclique e he)] at hh
    have hlo := (abs_le.mp hh).1
    change (n : ℝ) ^ q / (2 * q.factorial) ≤ ((Z e).card : ℝ)
    change -((1 / 2) * ((n : ℝ) ^ q / q.factorial)) ≤
      ((Z e).card : ℝ) - (n : ℝ) ^ q / q.factorial at hlo
    have hLid : (n : ℝ) ^ q / (2 * q.factorial) =
        (1 / 2) * ((n : ℝ) ^ q / q.factorial) := by field_simp
    rw [hLid]
    linarith only [hlo]
  · intro e he
    have hh := hcount e he
    rw [rootedCliques_eq_filter_cliqueFamily G e (heclique e he)] at hh
    convert hh using 1
    ring

end Arxiv2411_18291
