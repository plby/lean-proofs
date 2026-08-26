import ErdosProblems.Erdos547.EquipartitionTrimming

/-!
# Irregular-pair counts do not increase when nonempty clusters lose one vertex
-/

namespace Erdos547

open Finset SimpleGraph

open scoped Classical in
theorem trimmed_cluster_bad_count_le {V : Type*} [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (J : Finset (Finset V)) (C : ↥J → Finset V)
    (hsub : ∀ i, C i ⊆ i.val) (htrim : ∀ i, i.val.card ≤ (C i).card + 1)
    (hpos : ∀ i, 1 ≤ (C i).card) (δ ε b : ℝ) (hδε : 2 * δ ≤ ε) (hε : ε ≤ 1)
    (hrow : ∀ X ∈ J, ((J.filter (fun Y ↦ X ≠ Y ∧ ¬ G.IsUniform δ X Y)).card : ℝ) ≤ b) :
    ∀ i : ↥J, (((Finset.univ : Finset ↥J).filter
      (fun j ↦ i ≠ j ∧ ¬ G.IsUniform ε (C i) (C j))).card : ℝ) ≤ b := by
  classical
  intro i
  let B := (Finset.univ : Finset ↥J).filter (fun j ↦ i ≠ j ∧ ¬ G.IsUniform ε (C i) (C j))
  have hB : B.image Subtype.val ⊆ J.filter (fun Y ↦ i.val ≠ Y ∧ ¬ G.IsUniform δ i.val Y) := by
    intro Y hY
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hY
    obtain ⟨_, hij, hbad⟩ := Finset.mem_filter.mp hj
    refine Finset.mem_filter.mpr ⟨j.property, fun he ↦ hij (Subtype.ext he), ?_⟩
    intro hreg
    exact hbad (regular_pair_trim_one G hreg (hsub i) (hsub j) (htrim i) (htrim j)
      (hpos i) (hpos j) hδε hε)
  have hcard := Finset.card_le_card hB
  rw [Finset.card_image_of_injective _ Subtype.val_injective] at hcard
  exact (show (B.card : ℝ) ≤
    (J.filter (fun Y ↦ i.val ≠ Y ∧ ¬ G.IsUniform δ i.val Y)).card by exact_mod_cast hcard).trans
      (hrow i.val i.property)

end Erdos547

#print axioms Erdos547.trimmed_cluster_bad_count_le
