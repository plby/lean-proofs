import Arxiv.Arxiv2411_18291.UniformFlatteningRound
import Arxiv.Arxiv2411_18291.FlatteningIterationCost
import Arxiv.Arxiv2411_18291.CliqueMultiplicityBound

/-!
# Sparse integral-span preservation with a fixed multiplicity bound

For any fixed `0 < η < ρ < 1/2`, every sufficiently large `n` admits
flattening of every `n^(-ρ)`-bounded clique family to an `n^(-η)`-bounded
family with edge multiplicities at most 16 and containing its integer span.
The exchange patterns, balanced representatives, and all rounds are constructed.
-/

open Finset Filter
open scoped Topology

noncomputable section

namespace Arxiv2411_18291

theorem eventually_exists_sparse_flattening (q r : ℕ) (hqr : r + 1 < q)
    {η ρ : ℝ} (hη : 0 < η) (hηρ : η < ρ) (hρ : ρ < 1 / 2) :
    ∀ᶠ n : ℕ in atTop, ∀ D : Finset (Block (Fin n) q),
      IsCliqueFamilyBounded r D ((n : ℝ) ^ (-ρ)) →
      ∃ F : Finset (Block (Fin n) q), IsCliqueFamilyBounded r F ((n : ℝ) ^ (-η)) ∧
        (∀ J : Block (Fin n) (r + 1) → ℤ, GeneratedBy D J → GeneratedBy F J) ∧
        ∀ e : Block (Fin n) (r + 1), (F.filter fun Q => e.val ⊆ Q.val).card ≤ 16 := by
  obtain ⟨S, A, _, hA⟩ := exists_clique_exchange q (r + 1) (Nat.succ_pos r) hqr
  obtain ⟨E, N, e₀, hpair, _⟩ := exists_elimination_pattern q r hqr
  obtain ⟨C, hC, hround⟩ := eventually_exists_uniform_flattening_round S.system hA
    E.system N e₀ hpair hqr.le hη hηρ.le hρ
  filter_upwards [hround, eventually_exists_flattening_iterations hC (sub_pos.mpr hηρ),
    eventually_ge_atTop (16 : ℕ)] with n hround hcost hn
  intro D hD
  obtain ⟨k, hstop, hcost⟩ := hcost
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hθ : 0 ≤ (n : ℝ) ^ (-ρ) := Real.rpow_nonneg hnpos.le _
  have htotal : C ^ k * (n : ℝ) ^ (-ρ) ≤ (n : ℝ) ^ (-η) := by
    calc
      _ ≤ (n : ℝ) ^ (ρ - η) * (n : ℝ) ^ (-ρ) :=
        mul_le_mul_of_nonneg_right hcost hθ
      _ = _ := by rw [← Real.rpow_add hnpos]; congr 1; ring
  have hmult (e : Block (Fin n) (r + 1)) : (D.filter fun Q => e.val ⊆ Q.val).card ≤ n := by
    have hθ1 : (n : ℝ) ^ (-ρ) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos
      (by exact_mod_cast (show 1 ≤ n by omega)) (by linarith only [hη, hηρ])
    have hbound := (hD.multiplicity_lt e).le.trans
      (mul_le_mul_of_nonneg_right hθ1 (Nat.cast_nonneg (Fintype.card (Fin n))))
    simpa only [Fintype.card_fin, one_mul, Nat.cast_le] using hbound
  have hiter (j : ℕ) : j ≤ k → ∃ F : Finset (Block (Fin n) q),
      IsCliqueFamilyBounded r F (C ^ j * (n : ℝ) ^ (-ρ)) ∧
        (∀ J : Block (Fin n) (r + 1) → ℤ, GeneratedBy D J → GeneratedBy F J) ∧
        ∀ e : Block (Fin n) (r + 1), (F.filter fun Q => e.val ⊆ Q.val).card ≤
          (flatteningStep^[j]) n := by
    induction j with
    | zero =>
      intro _
      exact ⟨D, by simpa only [pow_zero, one_mul] using hD,
        fun _ h => h, by simpa only [Function.iterate_zero_apply] using hmult⟩
    | succ j ih =>
      intro hj
      obtain ⟨F, hF, hgen, hm⟩ := ih (by omega)
      have hlo : (n : ℝ) ^ (-ρ) ≤ C ^ j * (n : ℝ) ^ (-ρ) := by
        simpa only [one_mul] using mul_le_mul_of_nonneg_right (one_le_pow₀ hC) hθ
      have hhi : C ^ j * (n : ℝ) ^ (-ρ) ≤ (n : ℝ) ^ (-η) :=
        (mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hC (show j ≤ k by omega)) hθ).trans htotal
      obtain ⟨F', hF', hgen', hm'⟩ := hround (C ^ j * (n : ℝ) ^ (-ρ)) hlo hhi
        ((flatteningStep^[j]) n) (iterate_flatteningStep_le_initial hn j) F hF hm
      refine ⟨F', ?_, fun J hJ => hgen' J (hgen J hJ), ?_⟩
      · convert hF' using 1
        rw [pow_succ]
        ring
      · simpa only [Function.iterate_succ_apply'] using hm'
  obtain ⟨F, hF, hgen, hm⟩ := hiter k le_rfl
  exact ⟨F, hF.mono htotal, hgen, fun e => (hm e).trans hstop⟩

end Arxiv2411_18291
