import Mathlib.Data.Nat.Totient
import Mathlib.NumberTheory.Primorial
import Mathlib.Tactic

open Finset

namespace RoughShellCount

def roughModulus (Q : ℕ) : ℕ := ∏ p ∈ Nat.primesLE Q, p

def RoughUpTo (Q n : ℕ) : Prop :=
  ∀ p : ℕ, p.Prime → p ≤ Q → ¬ p ∣ n

def roughShell (Q N : ℕ) : Finset ℕ :=
  (Ico N (2 * N)).filter fun n ↦ (roughModulus Q).Coprime n

lemma roughModulus_eq_primorial (Q : ℕ) : roughModulus Q = primorial Q := by
  exact (primorial_eq_prod_primesLE Q).symm

lemma roughModulus_pos (Q : ℕ) : 0 < roughModulus Q := by
  rw [roughModulus_eq_primorial]
  exact primorial_pos Q

lemma card_filter_coprime_Ico_mul (M a t : ℕ) :
    ((Ico a (a + t * M)).filter fun n ↦ M.Coprime n).card =
      t * M.totient := by
  induction t with
  | zero => simp
  | succ t ih =>
      have hsplit :
          Ico a (a + (t + 1) * M) =
            Ico a (a + t * M) ∪ Ico (a + t * M) (a + t * M + M) := by
        rw [Nat.succ_mul]
        simpa only [add_assoc] using (Ico_union_Ico_eq_Ico
          (a := a) (b := a + t * M) (c := a + t * M + M)
          (by omega) (by omega)).symm
      rw [hsplit, filter_union]
      have hdisj :
          Disjoint
            ((Ico a (a + t * M)).filter fun n ↦ M.Coprime n)
            ((Ico (a + t * M) (a + t * M + M)).filter fun n ↦ M.Coprime n) := by
        exact disjoint_filter_filter
          (Ico_disjoint_Ico_consecutive a (a + t * M) (a + t * M + M))
      rw [card_union_of_disjoint hdisj, ih,
        Nat.filter_coprime_Ico_eq_totient M (a + t * M)]
      rw [Nat.succ_mul]

theorem card_roughShell_lower (Q N : ℕ) :
    (N / roughModulus Q) * (roughModulus Q).totient ≤
      (roughShell Q N).card := by
  let M := roughModulus Q
  let t := N / M
  have hM : 0 < M := roughModulus_pos Q
  have hlen : t * M ≤ N := by
    exact Nat.div_mul_le_self N M
  have hsub :
      (Ico N (N + t * M)).filter (fun n ↦ M.Coprime n) ⊆
        (Ico N (2 * N)).filter (fun n ↦ M.Coprime n) := by
    intro n hn
    simp only [mem_filter, mem_Ico] at hn ⊢
    exact ⟨⟨hn.1.1, by omega⟩, hn.2⟩
  have hcard := card_le_card hsub
  rw [card_filter_coprime_Ico_mul M N t] at hcard
  simpa [roughShell, M, t] using hcard

theorem twice_mul_card_roughShell_ge (Q N : ℕ)
    (hMN : roughModulus Q ≤ N) :
    N * (roughModulus Q).totient ≤
      2 * roughModulus Q * (roughShell Q N).card := by
  let M := roughModulus Q
  have hM : 0 < M := roughModulus_pos Q
  have hq : N < 2 * (N / M) * M := by
    have hdivpos : 0 < N / M := Nat.div_pos hMN hM
    have hmodlt := Nat.mod_lt N hM
    have hlt : N < (N / M + 1) * M := by
      calc
        N = N % M + M * (N / M) := (Nat.mod_add_div N M).symm
        _ < M + M * (N / M) := Nat.add_lt_add_right hmodlt _
        _ = (N / M + 1) * M := by ring
    have hcoef : N / M + 1 ≤ 2 * (N / M) := by omega
    exact hlt.trans_le (by
      calc
        (N / M + 1) * M ≤ (2 * (N / M)) * M := Nat.mul_le_mul_right M hcoef
        _ = 2 * (N / M) * M := by ring)
  have hcount := card_roughShell_lower Q N
  dsimp [M] at hq
  calc
    N * (roughModulus Q).totient
        ≤ (2 * (N / roughModulus Q) * roughModulus Q) *
            (roughModulus Q).totient := Nat.mul_le_mul_right _ hq.le
    _ = 2 * roughModulus Q *
          ((N / roughModulus Q) * (roughModulus Q).totient) := by ring
    _ ≤ 2 * roughModulus Q * (roughShell Q N).card := by
      exact Nat.mul_le_mul_left _ hcount

theorem mem_roughShell_rough (Q N n : ℕ) (hn : n ∈ roughShell Q N) :
    RoughUpTo Q n := by
  intro p hp hple hpdvd
  have hpM : p ∣ roughModulus Q := by
    rw [roughModulus]
    exact Finset.dvd_prod_of_mem id (Nat.mem_primesLE.mpr ⟨hple, hp⟩)
  have hcop : (roughModulus Q).Coprime n := (mem_filter.mp hn).2
  exact (Nat.Prime.not_coprime_iff_dvd.mpr
    ⟨p, hp, hpM, hpdvd⟩) hcop

end RoughShellCount
