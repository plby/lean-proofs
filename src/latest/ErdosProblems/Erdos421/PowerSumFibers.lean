import ErdosProblems.Erdos421.DomainTuples
import Mathlib.Data.ZMod.Basic

/-! # Fiber counts for a complete power-sum system

Fixing the last `m` entries reduces a system with `n + m` entries to a
system with `n` entries. Newton identities then bound each remaining
fiber by `n!`. This also applies in prime fields when `n < p`.
-/

namespace Erdos421

section CommRing

variable {R : Type*} [CommRing R] {s n m : ℕ}

def powerSumVector (n : ℕ) (x : Fin s → R) : Fin n → R :=
  fun j ↦ ∑ i : Fin s, x i ^ ((j : ℕ) + 1)

theorem powerSumVector_eq_iff (x y : Fin s → R) :
    powerSumVector n x = powerSumVector n y ↔
      ∀ k : ℕ, 0 < k → k ≤ n → (∑ i : Fin s, x i ^ k) = ∑ i : Fin s, y i ^ k := by
  constructor
  · intro h k hk hkn
    have hi : k - 1 < n := by omega
    have he := congrFun h ⟨k - 1, hi⟩
    simpa only [powerSumVector, Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr hk.ne')]
      using he
  · intro h
    funext j
    exact h (j + 1) (Nat.succ_pos _) (Nat.succ_le_of_lt j.isLt)

theorem powerSumVector_split (x : Fin (n + m) → R) (k : ℕ) :
    powerSumVector k x =
      powerSumVector k (fun i : Fin n ↦ x (Fin.castAdd m i)) +
        powerSumVector k (fun i : Fin m ↦ x (Fin.natAdd n i)) := by
  funext j
  exact Fin.sum_univ_add (fun i : Fin (n + m) ↦ x i ^ ((j : ℕ) + 1))

end CommRing

section Domain

variable {R : Type*} [CommRing R] [IsDomain R] [DecidableEq R] {n m : ℕ}

theorem powerSumVector_fiber_card_le (S : Finset (Fin n → R)) (v : Fin n → R)
    (hunit : ∀ k : ℕ, 0 < k → k ≤ n → IsUnit (k : R)) :
    (S.filter (fun x ↦ powerSumVector n x = v)).card ≤ n.factorial := by
  classical
  by_cases hne : (S.filter (fun x ↦ powerSumVector n x = v)).Nonempty
  · obtain ⟨y, hy⟩ := hne
    let P : Finset (Fin n → R) :=
      Finset.univ.image (fun e : Equiv.Perm (Fin n) ↦ fun i ↦ y (e i))
    have hsub : S.filter (fun x ↦ powerSumVector n x = v) ⊆ P := by
      intro x hx
      have he := (Finset.mem_filter.mp hx).2.trans (Finset.mem_filter.mp hy).2.symm
      obtain ⟨e, he⟩ := domain_tuple_perm_of_power_sums x y hunit
        ((powerSumVector_eq_iff x y).mp he)
      exact Finset.mem_image.mpr ⟨e, Finset.mem_univ _, (funext he).symm⟩
    calc
      _ ≤ P.card := Finset.card_le_card hsub
      _ ≤ Fintype.card (Equiv.Perm (Fin n)) := Finset.card_image_le
      _ = n.factorial := by rw [Fintype.card_perm, Fintype.card_fin]
  · rw [Finset.not_nonempty_iff_eq_empty.mp hne, Finset.card_empty]
    exact Nat.zero_le _

theorem powerSumVector_long_fiber_card_le (A : Finset R) (v : Fin n → R)
    (hunit : ∀ k : ℕ, 0 < k → k ≤ n → IsUnit (k : R)) :
    ((Fintype.piFinset (fun _ : Fin (n + m) ↦ A)).filter
      (fun x ↦ powerSumVector n x = v)).card ≤ n.factorial * A.card ^ m := by
  classical
  let T := (Fintype.piFinset (fun _ : Fin (n + m) ↦ A)).filter
    (fun x ↦ powerSumVector n x = v)
  let tail : (Fin (n + m) → R) → (Fin m → R) := fun x i ↦ x (Fin.natAdd n i)
  let head : (Fin (n + m) → R) → (Fin n → R) := fun x i ↦ x (Fin.castAdd m i)
  let U := Fintype.piFinset (fun _ : Fin m ↦ A)
  have hmap : ∀ x ∈ T, tail x ∈ U := by
    intro x hx
    exact Fintype.mem_piFinset.mpr (fun i ↦
      Fintype.mem_piFinset.mp (Finset.mem_filter.mp hx).1 (Fin.natAdd n i))
  have hfiber : ∀ q ∈ U, (T.filter (fun x ↦ tail x = q)).card ≤ n.factorial := by
    intro q _
    let V := (Fintype.piFinset (fun _ : Fin n ↦ A)).filter
      (fun x ↦ powerSumVector n x = v - powerSumVector n q)
    have hmaps : Set.MapsTo head (T.filter (fun x ↦ tail x = q)) V := by
      intro x hx
      obtain ⟨hxT, htail⟩ := Finset.mem_filter.mp hx
      obtain ⟨hxA, hxv⟩ := Finset.mem_filter.mp hxT
      refine Finset.mem_filter.mpr ⟨Fintype.mem_piFinset.mpr (fun i ↦
        Fintype.mem_piFinset.mp hxA (Fin.castAdd m i)), ?_⟩
      apply eq_sub_iff_add_eq.mpr
      rw [← htail]
      exact (powerSumVector_split x n).symm.trans hxv
    have hinj : Set.InjOn head (T.filter (fun x ↦ tail x = q)) := by
      intro x hx y hy hhead
      apply (Fin.appendEquiv n m).symm.injective
      apply Prod.ext hhead
      exact (Finset.mem_filter.mp hx).2.trans (Finset.mem_filter.mp hy).2.symm
    exact (Finset.card_le_card_of_injOn head hmaps hinj).trans
      (powerSumVector_fiber_card_le _ _ hunit)
  calc
    T.card = ∑ q ∈ U, (T.filter (fun x ↦ tail x = q)).card :=
      Finset.card_eq_sum_card_fiberwise hmap
    _ ≤ ∑ _q ∈ U, n.factorial := Finset.sum_le_sum hfiber
    _ = n.factorial * A.card ^ m := by
      simp only [Finset.sum_const, smul_eq_mul, U, Fintype.card_piFinset_const,
        mul_comm]

end Domain

theorem prime_powerSumVector_fiber_card_le {p n m : ℕ} (hp : p.Prime) (hn : n < p)
    (v : Fin n → ZMod p) :
    let : NeZero p := ⟨hp.ne_zero⟩
    ((Finset.univ : Finset (Fin (n + m) → ZMod p)).filter
      (fun x ↦ powerSumVector n x = v)).card ≤ n.factorial * p ^ m := by
  let : NeZero p := ⟨hp.ne_zero⟩
  let : Fact p.Prime := ⟨hp⟩
  have hu : ∀ k : ℕ, 0 < k → k ≤ n → IsUnit (k : ZMod p) := by
    intro k hk hkn
    apply isUnit_iff_ne_zero.mpr
    exact fun he ↦ Nat.not_dvd_of_pos_of_lt hk (hkn.trans_lt hn)
      ((ZMod.natCast_eq_zero_iff k p).mp he)
  simpa only [Fintype.piFinset_univ, Finset.card_univ, ZMod.card] using
    powerSumVector_long_fiber_card_le (m := m) (Finset.univ : Finset (ZMod p)) v hu

end Erdos421
