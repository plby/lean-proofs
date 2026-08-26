import ErdosProblems.Erdos421.DistinctSolutions
import ErdosProblems.Erdos421.PrimePools

/-! # Selecting one prime for many complete-system solutions -/

namespace Erdos421

noncomputable def primeDistinctSolutions (s k N p : ℕ) :
    Finset ((Fin (k + s) → Fin N) × (Fin (k + s) → Fin N)) := by
  classical
  exact (vinogradovSolutions (k + s) k N 0).filter (fun x ↦
    Function.Injective (fun i : Fin k ↦ (x.1 (Fin.castAdd s i) : ZMod p)) ∧
      Function.Injective (fun i : Fin k ↦ (x.2 (Fin.castAdd s i) : ZMod p)))

theorem exists_prime_many_residue_distinct (s k N : ℕ) (hs : 2 ≤ k + s)
    (hN : (4 * ((k + s) * (k + s - 1))) ^ 2 < N)
    (S : Finset ℕ) (hne : S.Nonempty) (hS : ∀ p ∈ S, p.Prime)
    (hprod : N ^ (2 * (k * (k - 1))) < ∏ p ∈ S, p) :
    ∃ p ∈ S, vinogradovCount (k + s) k N ≤ 2 * S.card * (primeDistinctSolutions s k N p).card := by
  classical
  have hsub : distinctVinogradovSolutions (k + s) k N ⊆
      S.biUnion (primeDistinctSolutions s k N) := by
    intro z hz
    obtain ⟨hzS, hz1, hz2⟩ := Finset.mem_filter.mp hz
    let x : Fin k → ℕ := fun i ↦ z.1 (Fin.castAdd s i)
    let y : Fin k → ℕ := fun i ↦ z.2 (Fin.castAdd s i)
    have hx : Function.Injective x := by
      intro i j he
      apply Fin.castAdd_injective k s
      exact hz1 (Fin.ext he)
    have hy : Function.Injective y := by
      intro i j he
      apply Fin.castAdd_injective k s
      exact hz2 (Fin.ext he)
    obtain ⟨p, hp, hxyp⟩ := exists_prime_distinct_tuple_residues x y hx hy
      (fun i ↦ (z.1 (Fin.castAdd s i)).isLt.le)
      (fun i ↦ (z.2 (Fin.castAdd s i)).isLt.le) S hS hprod
    exact Finset.mem_biUnion.mpr ⟨p, hp, Finset.mem_filter.mpr ⟨hzS, hxyp⟩⟩
  obtain ⟨p, hp, hmax⟩ := S.exists_max_image (fun p ↦ (primeDistinctSolutions s k N p).card) hne
  have hc : (distinctVinogradovSolutions (k + s) k N).card ≤
      S.card * (primeDistinctSolutions s k N p).card := by
    calc
      _ ≤ (S.biUnion (primeDistinctSolutions s k N)).card := Finset.card_le_card hsub
      _ ≤ ∑ q ∈ S, (primeDistinctSolutions s k N q).card := Finset.card_biUnion_le
      _ ≤ ∑ _q ∈ S, (primeDistinctSolutions s k N p).card := Finset.sum_le_sum hmax
      _ = _ := by rw [Finset.sum_const, smul_eq_mul]
  refine ⟨p, hp, ?_⟩
  calc
    _ ≤ 2 * (distinctVinogradovSolutions (k + s) k N).card :=
      vinogradovCount_le_two_distinct_of_large (k + s) k N hs hN
    _ ≤ 2 * (S.card * (primeDistinctSolutions s k N p).card) := Nat.mul_le_mul_left 2 hc
    _ = _ := (mul_assoc _ _ _).symm

theorem exists_prime_many_residue_distinct_in_interval (s k N M r : ℕ)
    (hs : 2 ≤ k + s) (hN : (4 * ((k + s) * (k + s - 1))) ^ 2 < N)
    (hM : 0 < M) (hr : 0 < r) (hb : N ^ (2 * (k * (k - 1))) < M ^ r) :
    ∃ p : ℕ, p.Prime ∧ M < p ∧ p ≤ 2 ^ r * M ∧
      vinogradovCount (k + s) k N ≤ 2 * r * (primeDistinctSolutions s k N p).card := by
  obtain ⟨S, hcard, hS⟩ := exists_prime_pool M r hM
  have hne : S.Nonempty := Finset.card_pos.mp (hcard ▸ hr)
  have hp : N ^ (2 * (k * (k - 1))) < ∏ p ∈ S, p := by
    apply hb.trans_le
    calc
      M ^ r = ∏ _p ∈ S, M := by rw [Finset.prod_const, hcard]
      _ ≤ ∏ p ∈ S, p := Finset.prod_le_prod (fun _ _ ↦ Nat.zero_le _)
        (fun p hp ↦ (hS p hp).2.1.le)
  obtain ⟨p, hpS, hcount⟩ := exists_prime_many_residue_distinct s k N hs hN S hne
    (fun p hp ↦ (hS p hp).1) hp
  rw [hcard] at hcount
  exact ⟨p, (hS p hpS).1, (hS p hpS).2.1, (hS p hpS).2.2, hcount⟩

/-- A single prime at the root scale carries a fixed fraction of the full
solution count, and its `k`th power exceeds the interval length. -/
theorem exists_prime_many_residue_distinct_at_root_scale (s k N M : ℕ)
    (hs : 2 ≤ k + s) (hk : 0 < k)
    (hN : (4 * ((k + s) * (k + s - 1))) ^ 2 < N)
    (hM : 1 < M) (hNM : N ≤ M ^ k) :
    ∃ p : ℕ, p.Prime ∧ M < p ∧ p ≤ 2 ^ (2 * k ^ 3) * M ∧ N < p ^ k ∧
      vinogradovCount (k + s) k N ≤ 4 * k ^ 3 * (primeDistinctSolutions s k N p).card := by
  obtain ⟨p, hp, hMp, hup, hcount⟩ := exists_prime_many_residue_distinct_in_interval
    s k N M (2 * k ^ 3) hs hN (Nat.zero_lt_of_lt hM)
    (Nat.mul_pos (by decide) (pow_pos hk _)) (root_scale_prime_pool_bound hk hM hNM)
  refine ⟨p, hp, hMp, hup, hNM.trans_lt (Nat.pow_lt_pow_left hMp hk.ne'), ?_⟩
  convert hcount using 1
  ring

end Erdos421
