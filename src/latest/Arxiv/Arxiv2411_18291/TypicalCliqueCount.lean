import Arxiv.Arxiv2411_18291.CliqueExtensionCount

/-!
# Lower bounds for punctured cliques in typical graphs

Iteration of the exact one-vertex count produces the factor `t!` and the
density exponent `choose (r+1+t) (r+1) - 1`, counting every nonexempt edge.
-/

open Finset
open scoped BigOperators

noncomputable section

namespace Arxiv2411_18291

theorem choose_face_le_clique {k q : ℕ} (r : ℕ) (hk : k < q) :
    k.choose r ≤ q.choose (r + 1) := by
  calc
    _ ≤ (k + 1).choose (r + 1) := by rw [Nat.choose_succ_succ]; omega
    _ ≤ _ := Nat.choose_le_choose _ hk

variable {V : Type*} [Fintype V] [DecidableEq V] {r q h : ℕ}

omit [DecidableEq V] in
theorem density_le_one (G : Hypergraph V r) : density G ≤ 1 := by
  unfold density
  apply div_le_one_of_le₀ _ (Nat.cast_nonneg _)
  have hc := card_le_univ G
  rw [Fintype.card_finset_len] at hc
  exact_mod_cast hc

theorem IsTypical.cliqueNextVertices_uniform {G : Hypergraph V (r + 1)} {c : ℝ}
    (hT : IsTypical G c h) (hqh : q.choose (r + 1) ≤ h) (hc : c ≤ 1 / 4)
    (hsize : (q : ℝ) ≤ Fintype.card V * density G ^ q.choose (r + 1) / 4)
    {k : ℕ} (hk : k < q) (U : Block V k) :
    (Fintype.card V : ℝ) / 2 * density G ^ k.choose r ≤
      ((cliqueNextVertices G U).card : ℝ) := by
  have hchoose := choose_face_le_clique r hk
  apply hT.cliqueNextVertices_half U (hchoose.trans hqh) hc
  have hpow : density G ^ q.choose (r + 1) ≤ density G ^ k.choose r :=
    pow_le_pow_of_le_one (density_nonneg G) (density_le_one G) hchoose
  calc
    (k : ℝ) ≤ q := by exact_mod_cast hk.le
    _ ≤ Fintype.card V * density G ^ q.choose (r + 1) / 4 := hsize
    _ ≤ _ := div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left hpow (Nat.cast_nonneg _)) (by norm_num)

/-- Count cliques after adding `t` vertices to the specified edge. -/
theorem IsTypical.puncturedCliques_factorial_lower {G : Hypergraph V (r + 1)} {c : ℝ}
    (hT : IsTypical G c h) (hqh : q.choose (r + 1) ≤ h) (hc : c ≤ 1 / 4)
    (hsize : (q : ℝ) ≤ Fintype.card V * density G ^ q.choose (r + 1) / 4)
    (e : Block V (r + 1)) (t : ℕ) (ht : r + 1 + t ≤ q) :
    ((Fintype.card V : ℝ) / 2) ^ t * density G ^ ((r + 1 + t).choose (r + 1) - 1) ≤
      (t.factorial : ℝ) * (puncturedCliques G e (r + 1 + t)).card := by
  induction t with
  | zero => simp [puncturedCliques_base]
  | succ t ih =>
    have ht' : r + 1 + t < q := by omega
    have hi := ih (by omega)
    have hstep := puncturedClique_step_lower G e (k := r + 1 + t) (by omega)
      (fun U _ => hT.cliqueNextVertices_uniform hqh hc hsize ht' U)
    have hstep' :
        (puncturedCliques G e (r + 1 + t)).card *
            ((Fintype.card V : ℝ) / 2 * density G ^ (r + 1 + t).choose r) ≤
          (t + 1 : ℕ) * ((puncturedCliques G e (r + 1 + (t + 1))).card : ℝ) := by
      rw [show r + 1 + t + 1 - (r + 1) = t + 1 by omega,
        show r + 1 + t + 1 = r + 1 + (t + 1) by omega] at hstep
      exact hstep
    have hexp : (r + 1 + (t + 1)).choose (r + 1) - 1 =
        ((r + 1 + t).choose (r + 1) - 1) + (r + 1 + t).choose r := by
      have hp := Nat.choose_pos (show r + 1 ≤ r + 1 + t by omega)
      rw [show r + 1 + (t + 1) = (r + 1 + t) + 1 by omega, Nat.choose_succ_succ]
      simp only [Nat.succ_eq_add_one]
      omega
    have hfactor : 0 ≤ (Fintype.card V : ℝ) / 2 * density G ^ (r + 1 + t).choose r :=
      mul_nonneg (by positivity) (pow_nonneg (density_nonneg G) _)
    calc
      _ = (((Fintype.card V : ℝ) / 2) ^ t *
          density G ^ ((r + 1 + t).choose (r + 1) - 1)) *
          ((Fintype.card V : ℝ) / 2 * density G ^ (r + 1 + t).choose r) := by
        rw [hexp, pow_add, pow_succ]
        ring
      _ ≤ ((t.factorial : ℝ) * (puncturedCliques G e (r + 1 + t)).card) *
          ((Fintype.card V : ℝ) / 2 * density G ^ (r + 1 + t).choose r) :=
        mul_le_mul_of_nonneg_right hi hfactor
      _ = (t.factorial : ℝ) * ((puncturedCliques G e (r + 1 + t)).card *
          ((Fintype.card V : ℝ) / 2 * density G ^ (r + 1 + t).choose r)) := by ring
      _ ≤ (t.factorial : ℝ) * ((t + 1 : ℕ) *
          ((puncturedCliques G e (r + 1 + (t + 1))).card : ℝ)) :=
        mul_le_mul_of_nonneg_left hstep' (Nat.cast_nonneg _)
      _ = _ := by rw [Nat.factorial_succ, Nat.cast_mul]; ring

/-- Distinct `q`-cliques, with the order of added vertices divided out. -/
theorem IsTypical.puncturedCliques_lower {G : Hypergraph V (r + 1)} {c : ℝ}
    (hT : IsTypical G c h) (hqh : q.choose (r + 1) ≤ h) (hc : c ≤ 1 / 4)
    (hsize : (q : ℝ) ≤ Fintype.card V * density G ^ q.choose (r + 1) / 4)
    (hqr : r + 1 ≤ q) (e : Block V (r + 1)) :
    (((Fintype.card V : ℝ) / 2) ^ (q - (r + 1)) * density G ^ (q.choose (r + 1) - 1)) /
        ((q - (r + 1)).factorial : ℝ) ≤ (puncturedCliques G e q).card := by
  have ht : r + 1 + (q - (r + 1)) = q := Nat.add_sub_of_le hqr
  have hl := hT.puncturedCliques_factorial_lower hqh hc hsize e (q - (r + 1)) ht.le
  rw [ht] at hl
  apply (div_le_iff₀ (by exact_mod_cast Nat.factorial_pos (q - (r + 1)))).mpr
  simpa only [mul_comm] using hl

end Arxiv2411_18291
