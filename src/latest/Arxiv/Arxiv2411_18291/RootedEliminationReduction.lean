import Arxiv.Arxiv2411_18291.RootedEliminationMultiplicity
import Arxiv.Arxiv2411_18291.EliminationBoundaryBounds
import Arxiv.Arxiv2411_18291.CliqueSupportBounds

/-!
# Integer span and sparsity after grouped elimination

Keep the representatives, replace every other group member by its exchange,
and use the balanced representative degrees to bound the resulting boundary.
The loss is constant and independent of group size and multiplicity.
-/

open Finset

noncomputable section

namespace Arxiv2411_18291

variable {W V : Type*} [Fintype W] [Fintype V] [DecidableEq W] [DecidableEq V]
variable {q r m : ℕ} {S : ExchangeSystem W q (r + 1)} {N : Block W q}
variable {e₀ : Block W (r + 1)} {D : Finset (Block V q)}
variable {B H : Hypergraph V (r + 1)} {θ η : ℝ}

theorem EliminationFamily.grouped_generation (R : RootedCliqueGrouping D B m)
    (Q : R.groups → Block V q) (hQ : ∀ c, Q c ∈ c.val)
    (F : EliminationFamily S N H (fun i : GroupEliminationIndex R.groups Q => Q i.1)
      (fun i => i.2.val) θ) (hpair : IsEliminationPair S N e₀)
    {J : Block V (r + 1) → ℤ} (hJ : GeneratedBy D J) :
    GeneratedBy (groupEliminationRetained D R.groups Q ∪ F.cliques) J := by
  apply groupElimination_preserves_generation D R.groups R.subset R.disjoint Q hQ
    _ subset_union_left _ hJ
  intro i
  have h := S.generatedBy_image_elimination hpair.negative_mem (F.embedding i)
    (groupEliminationRetained D R.groups Q ∪ F.cliques) (fun P hP =>
      mem_union_right _ (mem_biUnion.mpr ⟨i, mem_univ _,
        (mem_mapGraph _ _ _).mpr ⟨P, hP, rfl⟩⟩))
  simpa only [F.positive_root, F.negative_root] using h

theorem EliminationFamily.grouped_bounded (R : RootedCliqueGrouping D B m)
    (Q : R.groups → Block V q)
    (F : EliminationFamily S N H (fun i : GroupEliminationIndex R.groups Q => Q i.1)
      (fun i => i.2.val) θ) (hpair : IsEliminationPair S N e₀)
    (hqr : r + 1 ≤ q) (hη : 0 ≤ η) (hD : IsCliqueFamilyBounded r D η)
    (hrep : ∀ T : Block V r, (representativeDegree R.groups Q T.val : ℝ) ≤
      2 * η * Fintype.card V) :
    IsCliqueFamilyBounded r (groupEliminationRetained D R.groups Q ∪ F.cliques)
      ((1 + 4 * ((q - r : ℕ) : ℝ)) * η + 2 * θ) := by
  have hp (T : Block V r) :
      (familyDegree (fun i : GroupEliminationIndex R.groups Q => Q i.1) T.val : ℝ) ≤
        (2 * η) * Fintype.card V := by
    have h : (familyDegree (fun i : GroupEliminationIndex R.groups Q => Q i.1) T.val : ℝ) ≤
        (representativeDegree R.groups Q T.val : ℝ) := by
      exact_mod_cast groupEliminationLeft_degree_le R.groups Q T.val
    exact h.trans (hrep T)
  have hq (T : Block V r) :
      (familyDegree (fun i : GroupEliminationIndex R.groups Q => i.2.val) T.val : ℝ) ≤
        (2 * η) * Fintype.card V := by
    have h : (familyDegree (fun i : GroupEliminationIndex R.groups Q => i.2.val) T.val : ℝ) ≤
        ((degree (boundary (r + 1) (indicator D)) T.val : ℤ) : ℝ) := by
      have hcount := groupEliminationRight_degree_le D R.groups R.subset R.disjoint Q T.val
      have hface := face_clique_count_le_boundary_degree hqr D T
      exact_mod_cast (Int.ofNat_le.mpr hcount).trans hface
    have hn := mul_nonneg hη (Nat.cast_nonneg (Fintype.card V) : (0 : ℝ) ≤ _)
    have hd := hD T
    linarith
  have hkeep := hD.subfamily (show groupEliminationRetained D R.groups Q ⊆ D from sdiff_subset)
  convert hkeep.union (F.cliques_bounded_from_degrees hpair hp hq) using 1
  ring

end Arxiv2411_18291
