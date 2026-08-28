import Wikipedia.NoExoticSixSphere.JamesFiltration

/-!
# Exact-length strata in the actual reduced-word space

A Cartesian word has full length precisely when none of its entries is
the basepoint. On that locus the original array is uniquely recoverable.
These identities distinguish a James cell from its attaching boundary.
-/

noncomputable section

namespace NoExoticSixSphere.James

variable {X : Type*} (x₀ : X)

theorem size_word_eq_length_iff (l : List X) :
    size x₀ (word x₀ l) = l.length ↔ ∀ x ∈ l, x ≠ x₀ := by
  classical
  rw [← length_letters, letters_word, List.length_filter_eq_length_iff]
  simp only [decide_eq_true_eq]

theorem letters_word_of_forall_ne (l : List X) (hl : ∀ x ∈ l, x ≠ x₀) :
    letters x₀ (word x₀ l) = l := by
  classical
  rw [letters_word]
  exact List.filter_eq_self.mpr (by simpa only [decide_eq_true_eq] using hl)

theorem size_word_array_eq_iff (k : ℕ) (v : Fin k → X) :
    size x₀ (word x₀ (List.ofFn v)) = k ↔ ∀ i, v i ≠ x₀ := by
  have h := size_word_eq_length_iff x₀ (List.ofFn v)
  simpa only [List.length_ofFn, List.mem_ofFn, forall_exists_index,
    forall_apply_eq_imp_iff] using h

theorem word_array_injective_of_forall_ne {k : ℕ} {v w : Fin k → X}
    (hv : ∀ i, v i ≠ x₀) (hw : ∀ i, w i ≠ x₀)
    (h : word x₀ (List.ofFn v) = word x₀ (List.ofFn w)) : v = w := by
  apply List.ofFn_injective
  have hv' : ∀ x ∈ List.ofFn v, x ≠ x₀ := by
    intro x hx
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hx
    exact hv i
  have hw' : ∀ x ∈ List.ofFn w, x ≠ x₀ := by
    intro x hx
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hx
    exact hw i
  have he := congrArg (letters x₀) h
  rw [letters_word_of_forall_ne x₀ _ hv', letters_word_of_forall_ne x₀ _ hw'] at he
  exact he

theorem size_word_array_lt_iff (k : ℕ) (v : Fin k → X) :
    size x₀ (word x₀ (List.ofFn v)) < k ↔ ∃ i, v i = x₀ := by
  have hle : size x₀ (word x₀ (List.ofFn v)) ≤ k := by
    simpa only [List.length_ofFn] using size_word_le x₀ (List.ofFn v)
  rw [lt_iff_le_and_ne, and_iff_right hle, ne_eq, size_word_array_eq_iff]
  simp only [not_forall, not_not]

theorem size_eq_zero_iff (w : Space X x₀) : size x₀ w = 0 ↔ w = 1 :=
  FreeMonoid.length_eq_zero

end NoExoticSixSphere.James
