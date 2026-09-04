import ErdosProblems.Erdos192.Morphism

namespace Erdos192

private theorem keranenIterate_ASF (n : ℕ) : FinAbelianSquareFree (keranenIterate n) := by
  induction n with
  | zero => exact singleton_finASF 0
  | succ n ih => exact keranenG_preserves_ASF _ ih

/-- **Keränen 1992, computational content.** For every `n`, there exists a finite
abelian-square-free word of length `n` on four letters. -/
theorem exists_finASF_all_lengths :
    ∀ m : ℕ, ∃ w : List (Fin 4), w.length = m ∧ FinAbelianSquareFree w := by
  intro m
  obtain ⟨n, hn⟩ : ∃ n : ℕ, m ≤ 85 ^ n :=
    ⟨m, le_of_lt (lt_of_lt_of_le Nat.lt_two_pow_self (Nat.pow_le_pow_left (by omega) m))⟩
  exact ⟨(keranenIterate n).take m,
    by rw [List.length_take, keranenIterate_length]; omega,
    finASF_prefix _ (keranenIterate_ASF n) m (by rw [keranenIterate_length]; omega)⟩

theorem exists_inf_from_all_lengths
    (hall : ∀ m : ℕ, ∃ w : List (Fin 4), w.length = m ∧ FinAbelianSquareFree w) :
    ∃ f : ℕ → Fin 4, InfAbelianSquareFree f := by
  obtain ⟨f, hf⟩ :
      ∃ f : ℕ → Fin 4,
        ∀ m : ℕ, FinAbelianSquareFree (List.ofFn (fun i : Fin m => f i)) := by
    set extendable : List (Fin 4) → Prop := fun p =>
      ∀ m : ℕ, ∃ w : List (Fin 4),
        w.length = p.length + m ∧ FinAbelianSquareFree w ∧ w.take p.length = p
    have h_pigeonhole :
        ∀ p : List (Fin 4), extendable p → ∃ c : Fin 4, extendable (p ++ [c]) := by
      intro p hp
      by_contra h_contra
      push Not at h_contra
      have h_finite :
          ∀ c : Fin 4, ∃ m : ℕ, ∀ w : List (Fin 4),
            w.length = p.length + 1 + m → FinAbelianSquareFree w →
            w.take (p.length + 1) ≠ p ++ [c] := by
        intro c; specialize h_contra c; unfold extendable at h_contra; aesop
      obtain ⟨M, hM⟩ :
          ∃ M : ℕ, ∀ c : Fin 4, ∀ w : List (Fin 4),
            w.length = p.length + 1 + M → FinAbelianSquareFree w →
            w.take (p.length + 1) ≠ p ++ [c] := by
        choose m hm using h_finite
        use Finset.univ.sup m
        intros c w hwASF hw
        specialize hm c (w.take (p.length + 1 + m c)) ?_ ?_ <;>
          simp_all +decide only [List.length_take, inf_eq_left]
        · exact Finset.le_sup (f := m) (Finset.mem_univ c)
        · exact finASF_prefix _ hw _
            (by linarith [Finset.le_sup (f := m) (Finset.mem_univ c)])
      obtain ⟨w, hw₁, hw₂, hw₃⟩ := hp (1 + M)
      have h_take : ∃ c : Fin 4, List.take (p.length + 1) w = p ++ [c] := by
        rw [← List.take_append_drop p.length w, hw₃]
        rcases x : List.drop p.length w with (_ | ⟨c, _ | ⟨d, l⟩⟩) <;>
          simp_all +decide [List.take_append]
      grind
    choose! c hc using h_pigeonhole
    have h_rec :
        ∃ f : ℕ → Fin 4, ∀ n : ℕ,
          f n = c (List.ofFn (fun i : Fin n => f i)) := by
      have h_rec :
          ∀ n : ℕ, ∃ f : ℕ → Fin 4,
            ∀ i < n, f i = c (List.ofFn (fun j : Fin i => f j)) := by
        intro n
        induction' n with n ih
        · exact ⟨fun _ => 0, by norm_num⟩
        · obtain ⟨f, hf⟩ := ih
          use fun i =>
            if i < n then f i
            else c (List.ofFn (fun j : Fin i =>
              if j.val < n then f j.val
              else c (List.ofFn (fun k : Fin j.val => f k.val))))
          grind
      choose f hf using h_rec
      have h_eq : ∀ n m : ℕ, n ≤ m → ∀ i < n, f n i = f m i := by
        intros n m hnm i hi
        induction' i using Nat.strong_induction_on with i ih
        grind +qlia
      use fun n => f (n + 1) n
      grind
    obtain ⟨f, hf⟩ := h_rec
    use f
    have h_extendable : ∀ n : ℕ, extendable (List.ofFn (fun i : Fin n => f i)) := by
      intro n
      induction' n with n ih
      · exact fun m => by
          obtain ⟨w, hw₁, hw₂⟩ := hall m
          exact ⟨w, by simpa using hw₁, hw₂, by simp +decide⟩
      · rw [List.ofFn_succ_last]
        simpa only [Fin.val_castSucc, Fin.val_last, ← hf n] using hc _ ih
    intro m
    obtain ⟨w, hw₁, hw₂, hw₃⟩ := h_extendable m 0
    grind
  use f
  intro i l hl h
  have := hf (i + 2 * l)
  simp_all +decide [FinAbelianSquareFree]
  contrapose! hf
  refine ⟨i + 2 * l, i, l, hl, by linarith, ?_⟩
  convert h using 1 <;> (refine List.ext_get ?_ ?_ <;> simp +decide [infBlock] <;> omega)

/-- **Keränen 1992, Theorem 1.** There exists an infinite abelian-square-free
word over a four-letter alphabet. -/
theorem exists_inf_abelianSquareFree_four :
    ∃ f : ℕ → Fin 4, InfAbelianSquareFree f :=
  exists_inf_from_all_lengths exists_finASF_all_lengths

end Erdos192
