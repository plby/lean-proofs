import ErdosProblems.Erdos421.CharacterCorrelation
import ErdosProblems.Erdos421.FiniteMomentBound

/-! # The moment bound for one repeated coordinate -/

namespace Erdos421

variable {q k : ℕ} [NeZero q]

def repeatedCongruenceCount {X : Type*} [Fintype X] (f : X → Fin k → ZMod q) (n : ℕ) : ℕ :=
  ((Finset.univ : Finset (((Fin n → X) × X) × (Fin (n + 2) → X))).filter
    (fun p ↦ (∑ i : Fin n, f (p.1.1 i)) + f p.1.2 + f p.1.2 =
      ∑ i : Fin (n + 2), f (p.2 i))).card

theorem repeatedCongruenceCount_le_moment {X : Type*} [Fintype X]
    (f : X → Fin k → ZMod q) (n : ℕ) (h2 : IsUnit (2 : ZMod q))
    {B : ℝ} (hB : 0 < B)
    (hfm : (∑ a : Fin k → ZMod q, ‖vectorCharacterSum Finset.univ f a‖ ^ (2 * (n + 2))) ≤
      (q : ℝ) ^ k * B ^ (2 * (n + 2))) :
    (repeatedCongruenceCount f n : ℝ) ≤ B ^ (2 * n + 3) := by
  classical
  let g : X → Fin k → ZMod q := fun x j ↦ (2 : ZMod q) * f x j
  have hgm : (∑ a : Fin k → ZMod q, ‖vectorCharacterSum Finset.univ g a‖ ^ (2 * (n + 2))) ≤
      (q : ℝ) ^ k * B ^ (2 * (n + 2)) := by
    obtain ⟨u, hu⟩ := h2
    have he := sum_norm_vectorCharacterSum_scale Finset.univ f u (2 * (n + 2))
    rw [hu] at he
    exact he.trans_le hfm
  have hcard : ((Finset.univ : Finset (Fin k → ZMod q)).card : ℝ) = (q : ℝ) ^ k := by
    simp only [Finset.card_univ, Fintype.card_fun, Fintype.card_fin, ZMod.card, Nat.cast_pow]
  have he : 2 * n + 2 + 2 = 2 * (n + 2) := by omega
  have hm := finite_mixed_moment_bound (Finset.univ : Finset (Fin k → ZMod q))
    (fun a ↦ ‖vectorCharacterSum Finset.univ f a‖)
    (fun a ↦ ‖vectorCharacterSum Finset.univ g a‖) (2 * n + 2) hB
    (fun a _ ↦ norm_nonneg _) (fun a _ ↦ norm_nonneg _)
    (by simpa only [he, hcard] using hfm) (by simpa only [he, hcard] using hgm)
  rw [hcard] at hm
  have hc := vectorCharacterSum_correlation_bound
    (Finset.univ : Finset ((Fin n → X) × X))
    (Finset.univ : Finset (Fin (n + 2) → X))
    (fun x ↦ (∑ i : Fin n, f (x.1 i)) + f x.2 + f x.2)
    (fun y ↦ ∑ i : Fin (n + 2), f (y i))
  have hnorm (a : Fin k → ZMod q) :
      ‖vectorCharacterSum Finset.univ
        (fun x : (Fin n → X) × X ↦ (∑ i : Fin n, f (x.1 i)) + f x.2 + f x.2) a‖ *
      ‖vectorCharacterSum Finset.univ
        (fun y : Fin (n + 2) → X ↦ ∑ i : Fin (n + 2), f (y i)) a‖ =
        ‖vectorCharacterSum Finset.univ f a‖ ^ (2 * n + 2) *
          ‖vectorCharacterSum Finset.univ g a‖ := by
    rw [vectorCharacterSum_repeated_factor, ← vectorCharacterSum_power,
      norm_mul, norm_pow, norm_pow]
    change (‖vectorCharacterSum Finset.univ f a‖ ^ n * ‖vectorCharacterSum Finset.univ g a‖) *
      ‖vectorCharacterSum Finset.univ f a‖ ^ (n + 2) = _
    rw [mul_right_comm, ← pow_add]
    rw [show n + (n + 2) = 2 * n + 2 by omega]
  simp_rw [hnorm] at hc
  rw [Finset.univ_product_univ] at hc
  have hq : (0 : ℝ) < (q : ℝ) ^ k := by
    exact pow_pos (Nat.cast_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne q))) k
  apply (mul_le_mul_iff_right₀ hq).mp
  exact hc.trans hm

end Erdos421
