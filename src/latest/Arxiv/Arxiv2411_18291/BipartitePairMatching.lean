import Arxiv.Arxiv2411_18291.DegreeHallBounds
import Arxiv.Arxiv2411_18291.PairFamilyFromInjections

/-! # Pair matchings from degree bounds across a vertex partition -/

open Finset

noncomputable section

namespace Arxiv2411_18291

theorem exists_bipartite_pair_packing {V : Type*} [DecidableEq V]
    (S A : Finset V) (H : Finset (Block V 2)) (hHS : ∀ Q ∈ H, Q.val ⊆ S)
    {δ Δ : ℝ} (hΔ : 0 < Δ) (hδΔ : δ ≤ Δ)
    (hmin : ∀ a ∈ A, δ ≤ ((pairNeighbors H a ∩ (S \ A)).card : ℝ))
    (hmax : ∀ b ∈ S \ A, ((pairNeighbors H b ∩ A).card : ℝ) ≤ Δ)
    (d : ℕ) (hdefect : (Δ - δ) * A.card ≤ Δ * d) :
    ∃ C : Finset (Block V 2), C ⊆ H ∧ IsVertexPacking C ∧
      ((S \ vertexSupport C).card : ℝ) ≤ (S.card : ℝ) - 2 * A.card + 2 * d := by
  classical
  let t (a : A) := pairNeighbors H a.val ∩ (S \ A)
  have hlower (a : A) : δ ≤ ((t a).card : ℝ) := hmin a.val a.property
  have hupper (x : V) : ((univ.filter fun a : A => x ∈ t a).card : ℝ) ≤ Δ := by
    by_cases hx : x ∈ S \ A
    · have hcard : (univ.filter fun a : A => x ∈ t a).card ≤ (pairNeighbors H x ∩ A).card := by
        apply card_le_card_of_injOn (fun a : A => a.val)
        · intro a ha
          have hxa := (mem_inter.mp (mem_filter.mp ha).2).1
          have hax := ((mem_pairNeighbors H a.val x).mp hxa).symm
          exact mem_inter.mpr ⟨(mem_pairNeighbors H x a.val).mpr hax, a.property⟩
        · intro a _ b _ hab
          exact Subtype.ext hab
      exact (by exact_mod_cast hcard : ((univ.filter fun a : A => x ∈ t a).card : ℝ) ≤
        ((pairNeighbors H x ∩ A).card : ℝ)).trans (hmax x hx)
    · have hz : univ.filter (fun a : A => x ∈ t a) = ∅ := by
        apply eq_empty_iff_forall_notMem.mpr
        intro a ha
        exact hx (mem_inter.mp (mem_filter.mp ha).2).2
      simpa only [hz, card_empty, Nat.cast_zero] using hΔ.le
  obtain ⟨J, hJ, g, hginj, hg⟩ := exists_partial_transversal_of_degree_bounds t hΔ hδΔ
    hlower hupper d (by simpa only [Fintype.card_coe] using hdefect)
  let u (i : J) : V := i.val.val
  have huinj : Function.Injective u := by
    intro i j hij
    exact Subtype.ext (Subtype.ext hij)
  have hcross (i j : J) : u i ≠ g j := by
    intro hij
    have hgnot : g j ∉ A := (mem_sdiff.mp (mem_inter.mp (hg j)).2).2
    exact hgnot (hij ▸ i.val.property)
  have hadj (i : J) : PairAdjacent H (u i) (g i) :=
    (mem_pairNeighbors H (u i) (g i)).mp (mem_inter.mp (hg i)).1
  obtain ⟨C, hCH, hC, hCcard⟩ := exists_pair_family_of_injections H u g huinj hginj hcross hadj
  have hCcard' : C.card = J.card := by simpa only [Fintype.card_coe] using hCcard
  have hJ' : A.card ≤ J.card + d := by simpa only [Fintype.card_coe] using hJ
  rw [← hCcard'] at hJ'
  have hmatched : (A.card : ℝ) ≤ C.card + d := by exact_mod_cast hJ'
  have hsub : vertexSupport C ⊆ S := by
    intro x hx
    obtain ⟨Q, hQ, hxQ⟩ := mem_biUnion.mp hx
    exact hHS Q (hCH hQ) hxQ
  have hleave : ((S \ vertexSupport C).card : ℝ) = (S.card : ℝ) - 2 * C.card := by
    rw [card_sdiff_of_subset hsub, Nat.cast_sub (card_le_card hsub), hC.card_vertexSupport,
      Nat.cast_mul, Nat.cast_ofNat]
    ring
  refine ⟨C, hCH, hC, ?_⟩
  rw [hleave]
  linarith only [hmatched]

end Arxiv2411_18291
