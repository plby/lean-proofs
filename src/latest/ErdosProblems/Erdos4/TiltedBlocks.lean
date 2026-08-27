import ErdosProblems.Erdos4.TiltedSieve
import Mathlib.Order.Partition.Finpartition

/-!
# All-fiber blocks

Every finite fiber can be partitioned into nonempty blocks of size at most
`K`, retaining the final short block. Small interval width forces distinct
members of one fiber into distinct residues at every sieve coordinate.
-/

open scoped BigOperators

namespace Erdos4.Tilted

theorem exists_bounded_partition {α : Type*} [DecidableEq α]
    (C : Finset α) {K : ℕ} (hK : 0 < K) :
    ∃ P : Finpartition C, (∀ E ∈ P.parts, E.card ≤ K) ∧
      P.parts.card * K ≤ C.card + K := by
  classical
  induction C using Finset.strongInductionOn with
  | _ C ih =>
    by_cases hC : C = ∅
    · subst C
      exact ⟨Finpartition.empty _, by simp⟩
    by_cases hcK : C.card ≤ K
    · refine ⟨Finpartition.indiscrete hC, ?_, ?_⟩
      · simpa using hcK
      · simp
    obtain ⟨E, hEC, hEcard⟩ := Finset.exists_subset_card_eq (Nat.le_of_lt (lt_of_not_ge hcK))
    have hE : E.Nonempty := Finset.card_pos.mp (hEcard.symm ▸ hK)
    obtain ⟨Q, hsize, hcount⟩ := ih (C \ E) (Finset.sdiff_ssubset hEC hE)
    let P : Finpartition C := Q.extend hE.ne_empty Finset.sdiff_disjoint
      (Finset.sdiff_union_of_subset hEC)
    refine ⟨P, ?_, ?_⟩
    · intro F hF
      change F ∈ insert E Q.parts at hF
      rcases Finset.mem_insert.mp hF with rfl | hF
      · exact hEcard.le
      · exact hsize F hF
    · have hc : P.parts.card = Q.parts.card + 1 := Q.card_extend E C
      have hcard := Finset.card_sdiff_add_card_eq_card hEC
      rw [hc, Nat.add_mul, Nat.one_mul]
      omega

theorem bounded_partition_lower {α : Type*} [DecidableEq α]
    {C : Finset α} (P : Finpartition C) {K : ℕ}
    (hsize : ∀ E ∈ P.parts, E.card ≤ K) :
    C.card ≤ P.parts.card * K := by
  rw [← P.sum_card_parts]
  calc
    _ ≤ ∑ _E ∈ P.parts, K := Finset.sum_le_sum hsize
    _ = _ := by simp

/-- Retaining all fibers costs at most one additional block per fiber. -/
theorem exists_all_fiber_partition {α β : Type*} [DecidableEq α]
    [Fintype β] [DecidableEq β] (C : Finset α) (f : α → β) {K : ℕ} (hK : 0 < K) :
    ∃ P : Finpartition C, (∀ E ∈ P.parts, E.card ≤ K) ∧
      (∀ E ∈ P.parts, ∀ n ∈ E, ∀ m ∈ E, f n = f m) ∧
      C.card ≤ P.parts.card * K ∧
      P.parts.card * K ≤ C.card + Fintype.card β * K := by
  classical
  let fiber (b : β) := C.filter (fun n => f n = b)
  choose Q hsize hcount using fun b : β => exists_bounded_partition (fiber b) hK
  let blocks := Finset.univ.biUnion (fun b : β => (Q b).parts)
  have hmem {E : Finset α} : E ∈ blocks ↔ ∃ b, E ∈ (Q b).parts := by
    simp [blocks]
  have hsub : ∀ E ∈ blocks, E ⊆ C := by
    intro E hE
    obtain ⟨b, hb⟩ := hmem.mp hE
    exact (Q b).subset hb |>.trans (Finset.filter_subset _ _)
  have huniq : ∀ n ∈ C, ∃! E ∈ blocks, n ∈ E := by
    intro n hn
    have hnf : n ∈ fiber (f n) := by simp [fiber, hn]
    obtain ⟨E, hE, hnE⟩ := (Q (f n)).exists_mem hnf
    refine ⟨E, ⟨hmem.mpr ⟨f n, hE⟩, hnE⟩, ?_⟩
    intro F hF
    obtain ⟨b, hb⟩ := hmem.mp hF.1
    have hnb : f n = b := (Finset.mem_filter.mp ((Q b).subset hb hF.2)).2
    subst b
    exact (Q (f n)).eq_of_mem_parts hb hE hF.2 hnE
  have hempty : ∅ ∉ blocks := by
    intro h
    obtain ⟨b, hb⟩ := hmem.mp h
    exact (Q b).empty_notMem_parts hb
  let P : Finpartition C := Finpartition.ofExistsUnique blocks hsub huniq hempty
  have hPsize : ∀ E ∈ P.parts, E.card ≤ K := by
    intro E hE
    obtain ⟨b, hb⟩ := hmem.mp hE
    exact hsize b E hb
  refine ⟨P, hPsize, ?_, bounded_partition_lower P hPsize, ?_⟩
  · intro E hE n hn m hm
    obtain ⟨b, hb⟩ := hmem.mp hE
    exact ((Finset.mem_filter.mp ((Q b).subset hb hn)).2).trans
      ((Finset.mem_filter.mp ((Q b).subset hb hm)).2).symm
  · have hc : C.card = ∑ b : β, (fiber b).card :=
      Finset.card_eq_sum_card_fiberwise (fun _ _ => Finset.mem_univ _)
    calc
      P.parts.card * K ≤ (∑ b : β, (Q b).parts.card) * K :=
        Nat.mul_le_mul_right K Finset.card_biUnion_le
      _ = ∑ b : β, (Q b).parts.card * K := by rw [Finset.sum_mul]
      _ ≤ ∑ b : β, ((fiber b).card + K) := Finset.sum_le_sum (fun b _ => hcount b)
      _ = C.card + Fintype.card β * K := by
        rw [Finset.sum_add_distrib, ← hc]
        simp

theorem eq_of_two_residues {p s n m : ℕ} (hps : p.Coprime s)
    (hn : n < p * s) (hm : m < p * s)
    (hp : (n : ZMod p) = (m : ZMod p)) (hs : (n : ZMod s) = (m : ZMod s)) :
    n = m := by
  have hp' := (ZMod.natCast_eq_natCast_iff n m p).mp hp
  have hs' := (ZMod.natCast_eq_natCast_iff n m s).mp hs
  have hboth : n ≡ m [MOD p * s] := (Nat.modEq_and_modEq_iff_modEq_mul hps).mp ⟨hp', hs'⟩
  simpa only [Nat.ModEq, Nat.mod_eq_of_lt hn, Nat.mod_eq_of_lt hm] using hboth

/-- Within a short color fiber, every sieve-coordinate residue is distinct. -/
theorem fiber_residue_injective {C : Finset ℕ} {p s Y : ℕ}
    (hp : p.Prime) (hs : s.Prime) (hps : p ≠ s) (hwidth : Y < p * s)
    (hbound : ∀ n ∈ C, n ≤ Y)
    (hfiber : ∀ n ∈ C, ∀ m ∈ C, (n : ZMod p) = (m : ZMod p)) :
    Set.InjOn (fun n : ℕ => (n : ZMod s)) C := by
  intro n hn m hm hnm
  exact eq_of_two_residues ((Nat.coprime_primes hp hs).mpr hps)
    ((hbound n hn).trans_lt hwidth) ((hbound m hm).trans_lt hwidth)
    (hfiber n hn m hm) hnm

/-- The arithmetic part of Lemma 4.1, with the interval-width hypothesis explicit. -/
theorem fiber_pairwise_coprime {C : Finset ℕ} {p w Y : ℕ}
    (hp : p.Prime) (hwidth : Y < p * w)
    (hbound : ∀ n ∈ C, n ≤ Y)
    (hrough : ∀ n ∈ C, ∀ s, s.Prime → s ∣ n → w < s)
    (hsmall : ∀ n ∈ C, ∀ s, s.Prime → s ∣ n → s < p)
    (hfiber : ∀ n ∈ C, ∀ m ∈ C, (n : ZMod p) = (m : ZMod p)) :
    (C : Set ℕ).Pairwise Nat.Coprime := by
  intro n hn m hm hnm
  by_contra hcop
  obtain ⟨s, hs, hsn, hsm⟩ := Nat.Prime.not_coprime_iff_dvd.mp hcop
  have hps : p ≠ s := (ne_of_gt (hsmall n hn s hs hsn))
  have hwidth' : Y < p * s := hwidth.trans_le (Nat.mul_le_mul_left p (hrough n hn s hs hsn).le)
  apply hnm
  apply fiber_residue_injective hp hs hps hwidth' hbound hfiber hn hm
  change (n : ZMod s) = (m : ZMod s)
  rw [(ZMod.natCast_eq_zero_iff n s).mpr hsn, (ZMod.natCast_eq_zero_iff m s).mpr hsm]

theorem fiber_product_squarefree {C : Finset ℕ}
    (hcop : (C : Set ℕ).Pairwise Nat.Coprime) (hsq : ∀ n ∈ C, Squarefree n) :
    Squarefree (∏ n ∈ C, n) := by
  apply Finset.squarefree_prod_of_pairwise_isCoprime _ hsq
  intro n hn m hm hnm
  exact Nat.coprime_iff_isRelPrime.mp (hcop hn hm hnm)

end Erdos4.Tilted
