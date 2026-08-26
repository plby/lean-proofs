import ErdosProblems.Erdos118.WordResponses

/-!
An infinite alphabet can dominate every bound depending on a completed finite
support. The literal model retains its full order type after this thinning.
As an application, all separated pairs, not just sufficiently late tails for
each first word, are red on one full-type family in a triangle-free graph.
This does not control interleaved pairs or arbitrary new architect choices.
-/

namespace Erdos118.ConservativeAlphabet

open Ordinal Negative Negative.Exact CoordinateModel WordResponses
open Erdos590.Larson

/-- A finite maximum, including the bound at the empty support. -/
def envelope (b : Finset ℕ → ℕ) (q : ℕ) : ℕ :=
  ((Finset.range (q + 1)).powerset).sup b

def sequence (b : Finset ℕ → ℕ) (f : ℕ → ℕ) : ℕ → ℕ
  | 0 => f (b ∅ + 1)
  | n + 1 => f (max (sequence b f n + 1) (envelope b (sequence b f n) + 1))

theorem sequence_strictMono (b : Finset ℕ → ℕ) {f : ℕ → ℕ}
    (hf : StrictMono f) : StrictMono (sequence b f) := by
  apply strictMono_nat_of_lt_succ
  intro n
  have h := hf.le_apply (x := max (sequence b f n + 1)
    (envelope b (sequence b f n) + 1))
  change sequence b f n < f _
  exact lt_of_lt_of_le (lt_of_lt_of_le (Nat.lt_succ_self _) (le_max_left _ _)) h

theorem sequence_bound (b : Finset ℕ → ℕ) {f : ℕ → ℕ}
    (hf : StrictMono f) (s : Finset ℕ) (n : ℕ)
    (hs : (↑s : Set ℕ) ⊆ Set.range (sequence b f))
    (hlt : ∀ y ∈ s, y < sequence b f n) : b s < sequence b f n := by
  have ha := sequence_strictMono b hf
  cases n with
  | zero =>
    have hempty : s = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro y hy
      obtain ⟨j, rfl⟩ := hs hy
      exact (not_lt_of_ge (ha.monotone (Nat.zero_le j))) (hlt _ hy)
    rw [hempty]
    exact lt_of_lt_of_le (Nat.lt_succ_self _) hf.le_apply
  | succ n =>
    have hsub : s ⊆ Finset.range (sequence b f n + 1) := by
      intro y hy
      obtain ⟨j, rfl⟩ := hs hy
      have hj : j < n + 1 := ha.lt_iff_lt.mp (hlt _ hy)
      exact Finset.mem_range.mpr (Nat.lt_succ_of_le
        (ha.monotone (Nat.le_of_lt_succ hj)))
    have henv : b s ≤ envelope b (sequence b f n) :=
      Finset.le_sup (Finset.mem_powerset.mpr hsub)
    have harg : envelope b (sequence b f n) <
        max (sequence b f n + 1) (envelope b (sequence b f n) + 1) :=
      lt_of_lt_of_le (Nat.lt_succ_self _) (le_max_right _ _)
    exact henv.trans_lt (harg.trans_le hf.le_apply)

/-- Every finite support below a new coordinate has already had its bound
dominated. There is no assumption that the support is nonempty. -/
theorem exists_alphabet (b : Finset ℕ → ℕ) {N : Set ℕ} (hN : N.Infinite) :
    ∃ H ⊆ N, H.Infinite ∧
      ∀ s : Finset ℕ, (↑s : Set ℕ) ⊆ H →
        ∀ x ∈ H, (∀ y ∈ s, y < x) → b s < x := by
  let f := enumOf N
  have hf : StrictMono f := enumOf_strictMono hN
  refine ⟨Set.range (sequence b f), ?_,
    Set.infinite_range_of_injective (sequence_strictMono b hf).injective, ?_⟩
  · rintro _ ⟨i, rfl⟩
    cases i with
    | zero => exact enumOf_mem hN _
    | succ i => exact enumOf_mem hN _
  · intro s hs x hx hlt
    obtain ⟨i, rfl⟩ := hx
    exact sequence_bound b hf s i hs hlt

/-- Finite-support conservativity retains the exact ordinal, not just its
cardinality. -/
theorem exists_full_type_alphabet (b : Finset ℕ → ℕ)
    {N : Set ℕ} (hN : N.Infinite) :
    ∃ H ⊆ N, H.Infinite ∧ typeLT (Supported H) = lambda ∧
      ∀ s : Finset ℕ, (↑s : Set ℕ) ⊆ H →
        ∀ x ∈ H, (∀ y ∈ s, y < x) → b s < x := by
  obtain ⟨H, hHN, hH, hb⟩ := exists_alphabet b hN
  exact ⟨H, hHN, hH, type_supported hH, hb⟩

/-- One full-order literal family has no blue pair with separated complete
coordinate intervals. No claim about interleaved pairs is made. -/
theorem separated_pairs_red (B : SimpleGraph G) (hB : B.CliqueFree 3)
    {N : Set ℕ} (hN : N.Infinite) :
    ∃ H ⊆ N, H.Infinite ∧ typeLT (Supported H) = lambda ∧
      ∀ s ∈ Supported H, ∀ t ∈ Supported H,
        (∀ x ∈ word s.1, ∀ y ∈ word t.1, x < y) → ¬ B.Adj s t := by
  classical
  obtain ⟨H₀, hHN, hH₀, b₀, hred⟩ := red_completion_thinning B hB hN
  have hbounds (s : G) : ∃ b : ℕ,
      s ∈ Supported H₀ → (∀ n ∈ word s.1, b₀ < n) →
      ∀ t ∈ Supported H₀, (∀ n ∈ word t.1, b < n) → ¬ B.Adj s t := by
    by_cases hs : s ∈ Supported H₀ ∧ ∀ n ∈ word s.1, b₀ < n
    · obtain ⟨b, hb⟩ := hred s hs.1 hs.2
      exact ⟨b, fun _ _ ↦ hb⟩
    · exact ⟨0, fun h₁ h₂ ↦ (hs ⟨h₁, h₂⟩).elim⟩
  choose b hb using hbounds
  let c : Finset ℕ → ℕ := Function.extend support b (fun _ ↦ 0)
  have hc (s : G) : c (support s) = b s := support_injective.extend_apply ..
  obtain ⟨H, hHH₀, hH, htype, hbound⟩ :=
    exists_full_type_alphabet (fun F ↦ max b₀ (c F)) hH₀
  have hbase (x : ℕ) (hx : x ∈ H) : b₀ < x :=
    (le_max_left _ _).trans_lt (hbound ∅ (by simp) x hx (by simp))
  refine ⟨H, hHH₀.trans hHN, hH, htype, ?_⟩
  intro s hs t ht hsep
  have hs₀ : s ∈ Supported H₀ := fun x hx ↦ hHH₀ (hs x hx)
  have ht₀ : t ∈ Supported H₀ := fun x hx ↦ hHH₀ (ht x hx)
  apply hb s hs₀ (fun x hx ↦ hbase x (hs x hx)) t ht₀
  intro y hy
  have hxy : ∀ x ∈ support s, x < y :=
    fun x hx ↦ hsep x (List.mem_toFinset.mp hx) y hy
  have h := hbound (support s) ((supported_iff s H).mp hs) y (ht y hy) hxy
  rw [hc] at h
  exact (le_max_right _ _).trans_lt h

end Erdos118.ConservativeAlphabet
