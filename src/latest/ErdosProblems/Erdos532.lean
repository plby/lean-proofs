/- leanprover/lean4:v4.30.0  mathlib v4.30.0 -/
/-
This is a Lean formalization of a solution to Erdős Problem 532.
https://www.erdosproblems.com/forum/thread/532

Informal authors:
- Neil Hindman

Formal authors:
- David Wärn

URLs:
- https://www.erdosproblems.com/forum/thread/532#post-4004
- https://leanprover-community.github.io/mathlib4_docs/Mathlib/Combinatorics/Hindman.html
- https://github.com/leanprover-community/mathlib4/blob/20c3a51ac9205f8eeb30886a4f1744a22e981ebe/Mathlib/Combinatorics/Hindman.lean
-/
import Mathlib

namespace Erdos532

open scoped BigOperators

private theorem hindman_pnat (c : ℕ → Fin 2) :
    ∃ a : Stream' ℕ+, ∃ color : Fin 2,
      Hindman.FS a ⊆ {n : ℕ+ | c (n : ℕ) = color} := by
  let colorClass : Fin 2 → Set ℕ+ := fun color => {n : ℕ+ | c (n : ℕ) = color}
  let cover : Set (Set ℕ+) := Set.range colorClass
  have hcover_finite : cover.Finite := Set.finite_range colorClass
  have hcover : (⊤ : Set ℕ+) ⊆ ⋃₀ cover := by
    intro n hn
    exact ⟨colorClass (c (n : ℕ)), ⟨c (n : ℕ), rfl⟩, rfl⟩
  obtain ⟨C, hC, a, ha⟩ :=
    Hindman.exists_FS_of_finite_cover cover hcover_finite hcover
  rcases hC with ⟨color, rfl⟩
  exact ⟨a, color, ha⟩

private def pnatBlockSum (a : Stream' ℕ+) (start : ℕ) : ℕ → ℕ+
  | 0 => a.get start
  | k + 1 => a.get start + pnatBlockSum a (start + 1) k

private lemma pnatBlockSum_ge_length (a : Stream' ℕ+) (start k : ℕ) :
    k + 1 ≤ (pnatBlockSum a start k : ℕ) := by
  induction k generalizing start with
  | zero =>
      exact (a.get start).2
  | succ k ih =>
      have hhead : 1 ≤ (a.get start : ℕ) := (a.get start).2
      have htail : k + 1 ≤ (pnatBlockSum a (start + 1) k : ℕ) := ih (start + 1)
      simp [pnatBlockSum]
      omega

private lemma pnatBlockSum_mem_FS (a : Stream' ℕ+) (start k : ℕ) :
    pnatBlockSum a start k ∈ Hindman.FS (a.drop start) := by
  induction k generalizing start with
  | zero =>
      simpa [pnatBlockSum, Stream'.head_drop] using Hindman.FS.head (a.drop start)
  | succ k ih =>
      have htail :
          pnatBlockSum a (start + 1) k ∈ Hindman.FS (a.drop start).tail := by
        simpa [Stream'.tail_eq_drop, Stream'.drop_drop, add_comm, add_left_comm, add_assoc]
          using ih (start + 1)
      simpa [pnatBlockSum, Stream'.head_drop] using
        Hindman.FS.cons (a.drop start) (pnatBlockSum a (start + 1) k) htail

private lemma pnatBlockSum_add_mem_FS (a : Stream' ℕ+) (start k : ℕ) {m : ℕ+}
    (hm : m ∈ Hindman.FS (a.drop (start + (k + 1)))) :
    pnatBlockSum a start k + m ∈ Hindman.FS (a.drop start) := by
  induction k generalizing start with
  | zero =>
      have htail : m ∈ Hindman.FS (a.drop start).tail := by
        simpa [Stream'.tail_eq_drop, Stream'.drop_drop, add_comm, add_left_comm, add_assoc] using hm
      simpa [pnatBlockSum, Stream'.head_drop] using Hindman.FS.cons (a.drop start) m htail
  | succ k ih =>
      have htail :
          pnatBlockSum a (start + 1) k + m ∈ Hindman.FS (a.drop start).tail := by
        rw [Stream'.tail_eq_drop, Stream'.drop_drop]
        apply ih (start + 1)
        simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hm
      simpa [pnatBlockSum, Stream'.head_drop, add_assoc] using
        Hindman.FS.cons (a.drop start) (pnatBlockSum a (start + 1) k + m) htail

private def blockState (a : Stream' ℕ+) : ℕ → ℕ × ℕ
  | 0 => (0, 0)
  | n + 1 =>
      let state := blockState a n
      (state.1 + state.2 + 1, (pnatBlockSum a state.1 state.2 : ℕ))

private def blockStart (a : Stream' ℕ+) (n : ℕ) : ℕ := (blockState a n).1

private def blockLengthIndex (a : Stream' ℕ+) (n : ℕ) : ℕ := (blockState a n).2

private def blockStream (a : Stream' ℕ+) : Stream' ℕ+ :=
  fun n => pnatBlockSum a (blockStart a n) (blockLengthIndex a n)

private def blockStreamFrom (a : Stream' ℕ+) (n : ℕ) : Stream' ℕ+ :=
  fun i => blockStream a (n + i)

private lemma blockStart_succ (a : Stream' ℕ+) (n : ℕ) :
    blockStart a (n + 1) = blockStart a n + blockLengthIndex a n + 1 := by
  simp [blockStart, blockLengthIndex, blockState]

private lemma blockLengthIndex_succ (a : Stream' ℕ+) (n : ℕ) :
    blockLengthIndex a (n + 1) = (blockStream a n : ℕ) := by
  simp [blockLengthIndex, blockStream, blockStart, blockState]

private lemma blockStream_strictMono (a : Stream' ℕ+) :
    StrictMono fun n => (blockStream a n : ℕ) := by
  suffices hstep : ∀ n, (blockStream a n : ℕ) < (blockStream a (n + 1) : ℕ) by
    exact strictMono_nat_of_lt_succ hstep
  intro n
  have hge := pnatBlockSum_ge_length a (blockStart a (n + 1)) (blockLengthIndex a (n + 1))
  have hge' : (blockStream a n : ℕ) + 1 ≤ (blockStream a (n + 1) : ℕ) := by
    simpa [blockStream, blockLengthIndex_succ] using hge
  omega

private lemma blockStreamFrom_tail (a : Stream' ℕ+) (n : ℕ) :
    (blockStreamFrom a n).tail = blockStreamFrom a (n + 1) := by
  ext i
  simp [blockStreamFrom, Stream'.tail, Stream'.get, Nat.add_comm, Nat.add_left_comm]

private lemma blockStreamFrom_FS_subset (a : Stream' ℕ+) (n : ℕ) :
    Hindman.FS (blockStreamFrom a n) ⊆ Hindman.FS (a.drop (blockStart a n)) := by
  intro m hm
  refine Hindman.FS.recOn (motive := fun s m _ =>
      ∀ n, s = blockStreamFrom a n → m ∈ Hindman.FS (a.drop (blockStart a n))) hm ?_ ?_ ?_ n rfl
  · intro s n hs
    subst s
    simpa [blockStreamFrom, blockStream] using
      pnatBlockSum_mem_FS a (blockStart a n) (blockLengthIndex a n)
  · intro s m hm ih n hs
    subst s
    have hm' : m ∈ Hindman.FS (a.drop (blockStart a (n + 1))) := by
      apply ih (n + 1)
      exact blockStreamFrom_tail a n
    have hsubset :
        Hindman.FS (a.drop (blockStart a (n + 1))) ⊆
          Hindman.FS (a.drop (blockStart a n)) := by
      rw [blockStart_succ]
      simpa [Stream'.drop_drop, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        Hindman.FS_iter_tail_sub_FS (a.drop (blockStart a n)) (blockLengthIndex a n + 1)
    exact hsubset hm'
  · intro s m hm ih n hs
    subst s
    have hm' : m ∈ Hindman.FS (a.drop (blockStart a (n + 1))) := by
      apply ih (n + 1)
      exact blockStreamFrom_tail a n
    have hm'' : m ∈ Hindman.FS
        (a.drop (blockStart a n + (blockLengthIndex a n + 1))) := by
      simpa [blockStart_succ, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hm'
    simpa [blockStreamFrom, blockStream, Stream'.head, add_assoc] using
      pnatBlockSum_add_mem_FS a (blockStart a n) (blockLengthIndex a n) hm''

private lemma FS_nat_of_pnat_coe {a : Stream' ℕ+} {m : ℕ}
    (hm : m ∈ Hindman.FS (fun i => (a.get i : ℕ))) :
    ∃ p : ℕ+, p ∈ Hindman.FS a ∧ (p : ℕ) = m := by
  refine Hindman.FS.recOn (motive := fun s m _ =>
      ∀ a : Stream' ℕ+, s = (fun i => (a.get i : ℕ)) →
        ∃ p : ℕ+, p ∈ Hindman.FS a ∧ (p : ℕ) = m) hm ?_ ?_ ?_ a rfl
  · intro s a hs
    subst s
    exact ⟨a.head, Hindman.FS.head a, rfl⟩
  · intro s m hm ih a hs
    subst s
    obtain ⟨p, hp, hpval⟩ := ih a.tail (by
      ext i
      rfl)
    exact ⟨p, Hindman.FS.tail a p hp, hpval⟩
  · intro s m hm ih a hs
    subst s
    obtain ⟨p, hp, hpval⟩ := ih a.tail (by
      ext i
      rfl)
    exact ⟨a.head + p, Hindman.FS.cons a p hp, by
      change (((a.get 0) + p : ℕ+) : ℕ) = (a.get 0 : ℕ) + m
      rw [PNat.add_coe, hpval]⟩

/--
If the natural numbers are 2-colored, then there is an infinite set `A` of
natural numbers whose nonempty finite subset sums are all the same color.
-/
theorem erdos532 (c : ℕ → Fin 2) :
    ∃ A : Set ℕ, A.Infinite ∧
      ∃ color : Fin 2,
        ∀ S : Finset ℕ, S.Nonempty → ↑S ⊆ A →
          c (∑ n ∈ S, n) = color := by
  obtain ⟨a, color, hmono⟩ := hindman_pnat c
  let bNat : ℕ → ℕ := fun n => (blockStream a n : ℕ)
  have hb_strict : StrictMono bNat := blockStream_strictMono a
  refine ⟨Set.range bNat, Set.infinite_range_of_injective hb_strict.injective, color, ?_⟩
  intro S hS hSsub
  let T : Finset ℕ := S.preimage bNat hb_strict.injective.injOn
  have hT : T.Nonempty := by
    rcases hS with ⟨x, hx⟩
    rcases hSsub hx with ⟨i, rfl⟩
    exact ⟨i, by simpa [T, bNat] using hx⟩
  have himage : T.image bNat = S := by
    ext x
    constructor
    · intro hx
      rcases Finset.mem_image.mp hx with ⟨i, hi, rfl⟩
      simpa [T, bNat] using (Finset.mem_preimage.mp hi)
    · intro hx
      rcases hSsub hx with ⟨i, rfl⟩
      exact Finset.mem_image.mpr ⟨i, by simpa [T, bNat] using hx, rfl⟩
  have hsum : (∑ n ∈ S, n) = ∑ i ∈ T, bNat i := by
    rw [← himage]
    exact Finset.sum_image hb_strict.injective.injOn
  have hFSNat : (∑ i ∈ T, bNat i) ∈ Hindman.FS (fun i => bNat i) :=
    Hindman.FS.finset_sum (fun i => bNat i) T hT
  obtain ⟨p, hp_blocks, hpval⟩ :=
    FS_nat_of_pnat_coe (a := blockStream a) hFSNat
  have hp_blocks' : p ∈ Hindman.FS (blockStreamFrom a 0) := by
    have hstream : blockStreamFrom a 0 = blockStream a := by
      ext i
      change blockStream a (0 + i) = blockStream a i
      rw [Nat.zero_add]
    simpa [hstream] using hp_blocks
  have hp_a_drop : p ∈ Hindman.FS (a.drop (blockStart a 0)) :=
    blockStreamFrom_FS_subset a 0 hp_blocks'
  have hp_a : p ∈ Hindman.FS a := by
    simpa [blockStart, blockState] using hp_a_drop
  rw [hsum, ← hpval]
  exact hmono hp_a

#print axioms erdos532
-- 'Erdos532.erdos532' depends on axioms: [propext, Classical.choice, Quot.sound]

end Erdos532
