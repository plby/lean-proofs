import Arxiv.Arxiv2411_18291.FrozenEdgeDrift

/-! # Frozen edge drift under upper and lower clique-degree bounds -/

open Finset
open scoped BigOperators

noncomputable section

namespace Arxiv2411_18291

variable {V : Type*} [Fintype V] [DecidableEq V] {q r : ℕ}

theorem other_clique_degrees_bounds (H : Finset (Block V q)) (e : Block V r)
    (P : Block V q) (hPH : P ∈ H) (heP : e.val ⊆ P.val)
    {dmin dmax : ℝ} (hd : ∀ f : Block V r, (H.filter fun Q => f.val ⊆ Q.val).Nonempty →
      dmin ≤ ((H.filter fun Q => f.val ⊆ Q.val).card : ℝ) ∧
        ((H.filter fun Q => f.val ⊆ Q.val).card : ℝ) ≤ dmax) :
    ((q.choose r - 1 : ℕ) : ℝ) * dmin ≤
        (∑ f ∈ (cliqueEdges r P).erase e, ((H.filter fun Q => f.val ⊆ Q.val).card : ℝ)) ∧
      (∑ f ∈ (cliqueEdges r P).erase e, ((H.filter fun Q => f.val ⊆ Q.val).card : ℝ)) ≤
        ((q.choose r - 1 : ℕ) : ℝ) * dmax := by
  have hcard : ((cliqueEdges r P).erase e).card = q.choose r - 1 := by
    rw [card_erase_of_mem ((mem_cliqueEdges _ _).mpr heP), card_cliqueEdges]
  have hf : ∀ f ∈ (cliqueEdges r P).erase e,
      dmin ≤ ((H.filter fun Q => f.val ⊆ Q.val).card : ℝ) ∧
        ((H.filter fun Q => f.val ⊆ Q.val).card : ℝ) ≤ dmax := by
    intro f hf
    exact hd f ⟨P, mem_filter.mpr ⟨hPH, (mem_cliqueEdges _ _).mp (mem_erase.mp hf).2⟩⟩
  constructor
  · have h := sum_le_sum (s := (cliqueEdges r P).erase e) (fun f hf' => (hf f hf').1)
    simpa only [sum_const, nsmul_eq_mul, hcard] using h
  · have h := sum_le_sum (s := (cliqueEdges r P).erase e) (fun f hf' => (hf f hf').2)
    simpa only [sum_const, nsmul_eq_mul, hcard] using h

theorem sum_other_clique_degrees_bounds (H : Finset (Block V q)) (e : Block V r)
    {dmin dmax : ℝ} (hd : ∀ f : Block V r, (H.filter fun Q => f.val ⊆ Q.val).Nonempty →
      dmin ≤ ((H.filter fun Q => f.val ⊆ Q.val).card : ℝ) ∧
        ((H.filter fun Q => f.val ⊆ Q.val).card : ℝ) ≤ dmax) :
    let A := ∑ P ∈ H.filter (fun P => e.val ⊆ P.val),
      ∑ f ∈ (cliqueEdges r P).erase e, ((H.filter fun Q => f.val ⊆ Q.val).card : ℝ)
    (H.filter fun P => e.val ⊆ P.val).card * ((q.choose r - 1 : ℕ) : ℝ) * dmin ≤ A ∧
      A ≤ (H.filter fun P => e.val ⊆ P.val).card * ((q.choose r - 1 : ℕ) : ℝ) * dmax := by
  let E := H.filter fun P => e.val ⊆ P.val
  let k : ℝ := (q.choose r - 1 : ℕ)
  let w := fun P : Block V q =>
    ∑ f ∈ (cliqueEdges r P).erase e, ((H.filter fun Q => f.val ⊆ Q.val).card : ℝ)
  have hterm : ∀ P ∈ E, k * dmin ≤ w P ∧ w P ≤ k * dmax := by
    intro P hP
    exact other_clique_degrees_bounds H e P (mem_filter.mp hP).1 (mem_filter.mp hP).2 hd
  change (E.card : ℝ) * k * dmin ≤ (∑ P ∈ E, w P) ∧
    (∑ P ∈ E, w P) ≤ (E.card : ℝ) * k * dmax
  constructor
  · have h : (∑ _P ∈ E, k * dmin) ≤ ∑ P ∈ E, w P :=
      sum_le_sum fun P hP => (hterm P hP).1
    simpa only [sum_const, nsmul_eq_mul, mul_assoc] using h
  · have h : (∑ P ∈ E, w P) ≤ ∑ _P ∈ E, k * dmax :=
      sum_le_sum fun P hP => (hterm P hP).2
    simpa only [sum_const, nsmul_eq_mul, mul_assoc] using h

theorem frozenEdgeLoss_average_of_degree_bounds (hqr : r < q) (H : Finset (Block V q))
    (hH : H.Nonempty) (e : Block V r) {dmin dmax : ℝ}
    (hd : ∀ f : Block V r, (H.filter fun Q => f.val ⊆ Q.val).Nonempty →
      dmin ≤ ((H.filter fun Q => f.val ⊆ Q.val).card : ℝ) ∧
        ((H.filter fun Q => f.val ⊆ Q.val).card : ℝ) ≤ dmax) :
    let d := ((H.filter fun P => e.val ⊆ P.val).card : ℝ) / H.card
    let k := ((q.choose r - 1 : ℕ) : ℝ)
    let C := ((q.choose r : ℝ) ^ 2 + q.choose r) * (Fintype.card V : ℝ) ^ (q - r - 1)
    let L := (∑ Q ∈ H, (frozenEdgeLoss H e Q : ℝ)) / H.card
    d * (k * dmin - C) ≤ L ∧ L ≤ d * k * dmax := by
  obtain ⟨hlo, hhi⟩ := sum_other_clique_degrees_bounds H e hd
  obtain ⟨havlo, havhi⟩ := frozenEdgeLoss_average_bounds hqr H hH e
  have hcard : (0 : ℝ) < H.card := by exact_mod_cast hH.card_pos
  dsimp only
  constructor
  · have h := sub_le_sub_right (div_le_div_of_nonneg_right hlo hcard.le)
      (((H.filter fun P => e.val ⊆ P.val).card : ℝ) / H.card *
        (((q.choose r : ℝ) ^ 2 + q.choose r) * (Fintype.card V : ℝ) ^ (q - r - 1)))
    have h' := h.trans havlo
    exact le_trans (le_of_eq (by ring)) h'
  · have h := havhi.trans (div_le_div_of_nonneg_right hhi hcard.le)
    exact h.trans (le_of_eq (by ring))

end Arxiv2411_18291
