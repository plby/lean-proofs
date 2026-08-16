import Wikipedia.SzemeredisTheorem.Statement

namespace Wikipedia.SzemeredisTheorem

/-- `IsAPIn A k a d` says that the first `k` terms of the natural-number
arithmetic progression with initial term `a` and positive step `d` lie in
`A`. -/
def IsAPIn (A : Set ℕ) (k a d : ℕ) : Prop :=
  0 < d ∧ ∀ j : ℕ, j < k → a + d * j ∈ A

/-- A set contains an arithmetic progression of the specified length. -/
def ContainsAP (A : Set ℕ) (k : ℕ) : Prop :=
  ∃ a d : ℕ, IsAPIn A k a d

theorem isAPIn_iff (A : Set ℕ) (k a d : ℕ) :
    IsAPIn A k a d ↔
      0 < d ∧ ∀ j : ℕ, j < k → a + d * j ∈ A :=
  Iff.rfl

theorem containsAP_iff (A : Set ℕ) (k : ℕ) :
    ContainsAP A k ↔
      ∃ a d : ℕ, 0 < d ∧
        ∀ j : ℕ, j < k → a + d * j ∈ A :=
  Iff.rfl

/-- The local `ContainsAP` interface is equivalent to the predicate in the
LeanEval statement. -/
theorem containsArbitraryAPs_iff (A : Set ℕ) :
    SzemeredisTheorem.ContainsArbitraryAPs A ↔
      ∀ k : ℕ, ContainsAP A k := by
  constructor
  · intro h k
    obtain ⟨a, d, hd, hA⟩ := h k
    exact ⟨a, d, hd, hA⟩
  · intro h k
    obtain ⟨a, d, hd, hA⟩ := h k
    exact ⟨a, d, hd, hA⟩

/-- Enlarging the ambient set preserves a fixed arithmetic progression. -/
theorem IsAPIn.mono_set {A B : Set ℕ} {k a d : ℕ}
    (h : IsAPIn A k a d) (hAB : A ⊆ B) :
    IsAPIn B k a d :=
  ⟨h.1, fun j hj => hAB (h.2 j hj)⟩

/-- An initial segment of an arithmetic progression is an arithmetic
progression with the same initial term and step. -/
theorem IsAPIn.take {A : Set ℕ} {l k a d : ℕ}
    (h : IsAPIn A k a d) (hlk : l ≤ k) :
    IsAPIn A l a d :=
  ⟨h.1, fun j hj => h.2 j (lt_of_lt_of_le hj hlk)⟩

theorem ContainsAP.mono_set {A B : Set ℕ} {k : ℕ}
    (h : ContainsAP A k) (hAB : A ⊆ B) :
    ContainsAP B k := by
  obtain ⟨a, d, hap⟩ := h
  exact ⟨a, d, hap.mono_set hAB⟩

/-- Containing a progression is antitone in its requested length. -/
theorem ContainsAP.take {A : Set ℕ} {l k : ℕ}
    (h : ContainsAP A k) (hlk : l ≤ k) :
    ContainsAP A l := by
  obtain ⟨a, d, hap⟩ := h
  exact ⟨a, d, hap.take hlk⟩

theorem containsArbitraryAPs_mono {A B : Set ℕ}
    (hAB : A ⊆ B)
    (hA : SzemeredisTheorem.ContainsArbitraryAPs A) :
    SzemeredisTheorem.ContainsArbitraryAPs B := by
  intro k
  obtain ⟨a, d, hd, ha⟩ := hA k
  exact ⟨a, d, hd, fun j hj => hAB (ha j hj)⟩

theorem containsAP_zero (A : Set ℕ) : ContainsAP A 0 := by
  refine ⟨0, 1, Nat.zero_lt_one, ?_⟩
  intro j hj
  omega

theorem containsAP_one_iff (A : Set ℕ) :
    ContainsAP A 1 ↔ A.Nonempty := by
  constructor
  · rintro ⟨a, d, hd, ha⟩
    exact ⟨a, by simpa using ha 0 Nat.zero_lt_one⟩
  · rintro ⟨a, ha⟩
    refine ⟨a, 1, Nat.zero_lt_one, ?_⟩
    intro j hj
    have hj0 : j = 0 := by omega
    subst j
    simpa using ha

/-- Distributing an affine map across the terms of an arithmetic progression
changes the initial term from `a` to `W * a + r` and the step from `d` to
`W * d`. -/
theorem affine_term (W r a d j : ℕ) :
    W * (a + d * j) + r =
      (W * a + r) + (W * d) * j := by
  simp only [Nat.mul_add, Nat.mul_assoc]
  ac_rfl

/-- Affine lifting for a fixed progression.  If the index progression lies in
the preimage of `A` under `n ↦ W * n + r`, then its affine image is a
progression in `A`.  Positivity of `W` ensures that the new step is positive. -/
theorem IsAPIn.affine {A : Set ℕ} {k a d W r : ℕ}
    (h : IsAPIn {n : ℕ | W * n + r ∈ A} k a d)
    (hW : 0 < W) :
    IsAPIn A k (W * a + r) (W * d) := by
  refine ⟨Nat.mul_pos hW h.1, ?_⟩
  intro j hj
  rw [← affine_term]
  exact h.2 j hj

theorem ContainsAP.affine {A : Set ℕ} {k W r : ℕ}
    (h : ContainsAP {n : ℕ | W * n + r ∈ A} k)
    (hW : 0 < W) :
    ContainsAP A k := by
  obtain ⟨a, d, hap⟩ := h
  exact ⟨W * a + r, W * d, hap.affine hW⟩

theorem containsArbitraryAPs_affine {A : Set ℕ} {W r : ℕ}
    (hW : 0 < W)
    (hA :
      SzemeredisTheorem.ContainsArbitraryAPs
        {n : ℕ | W * n + r ∈ A}) :
    SzemeredisTheorem.ContainsArbitraryAPs A := by
  rw [containsArbitraryAPs_iff] at hA ⊢
  intro k
  exact (hA k).affine hW

/-- Prime-specialized affine lifting.  This is the W-trick bridge: primality
of the affine images of a positive-step progression of indices gives a
positive-step progression of natural primes. -/
theorem prime_isAPIn_of_affine {k W r a d : ℕ}
    (hW : 0 < W) (hd : 0 < d)
    (hprime :
      ∀ j : ℕ, j < k → Nat.Prime (W * (a + d * j) + r)) :
    IsAPIn {p : ℕ | Nat.Prime p} k
      (W * a + r) (W * d) := by
  apply IsAPIn.affine (W := W) (r := r)
  · exact ⟨hd, hprime⟩
  · exact hW

/-- The prime affine-lifting lemma in the exact witness shape required by
`SzemeredisTheorem.ContainsArbitraryAPs` at a fixed length `k`. -/
theorem prime_ap_witness_of_affine {k W r a d : ℕ}
    (hW : 0 < W) (hd : 0 < d)
    (hprime :
      ∀ j : ℕ, j < k → Nat.Prime (W * (a + d * j) + r)) :
    ∃ a' b' : ℕ, 1 ≤ b' ∧
      ∀ j : ℕ, j < k → Nat.Prime (a' + b' * j) := by
  have hap := prime_isAPIn_of_affine hW hd hprime
  exact ⟨W * a + r, W * d, hap.1, hap.2⟩

end Wikipedia.SzemeredisTheorem
