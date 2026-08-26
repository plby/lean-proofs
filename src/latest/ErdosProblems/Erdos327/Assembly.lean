import ErdosProblems.Erdos327.Basic

namespace Erdos327

/-- Odd host vertices that meet the doubled source in a mixed conflict. -/
noncomputable def mixedBad (O B : Finset ℕ) : Finset ℕ := by
  classical
  exact O.filter fun a => ∃ b ∈ B, ConflictOne a (2 * b)

@[simp] theorem mem_mixedBad {O B : Finset ℕ} {a : ℕ} :
    a ∈ mixedBad O B ↔
      a ∈ O ∧ ∃ b ∈ B, ConflictOne a (2 * b) := by
  classical
  simp [mixedBad]

theorem mixedBad_subset (O B : Finset ℕ) :
    mixedBad O B ⊆ O := by
  intro a ha
  exact (mem_mixedBad.mp ha).1

/-- The final set: retain the unblocked odd host and adjoin the doubled
two-admissible source. -/
noncomputable def assembledSet (O B : Finset ℕ) : Finset ℕ :=
  (O \ mixedBad O B) ∪ doubleSet B

theorem not_mixed_conflict_of_mem_sdiff
    {O B : Finset ℕ} {a b : ℕ}
    (ha : a ∈ O \ mixedBad O B) (hb : b ∈ B) :
    ¬ ConflictOne a (2 * b) := by
  intro hab
  have haO : a ∈ O := (Finset.mem_sdiff.mp ha).1
  have haBad : a ∈ mixedBad O B :=
    mem_mixedBad.mpr ⟨haO, b, hb, hab⟩
  exact (Finset.mem_sdiff.mp ha).2 haBad

/-- The odd and doubled parts of the construction are disjoint. -/
theorem disjoint_odd_doubleSet
    {O B : Finset ℕ} (hodd : ∀ a ∈ O, Odd a) :
    Disjoint O (doubleSet B) := by
  rw [Finset.disjoint_left]
  intro a haO haDouble
  rcases mem_doubleSet.mp haDouble with ⟨b, _hb, rfl⟩
  have hOdd : Odd (2 * b) := hodd (2 * b) haO
  have hEven : Even (2 * b) := even_two_mul b
  exact (Nat.not_even_iff_odd.mpr hOdd) hEven

/-- The combinatorial assembly is one-admissible.  No analytic estimate is
used here: all mixed conflicts have been removed by definition. -/
theorem oneAdmissible_assembledSet
    {O B : Finset ℕ}
    (hodd : ∀ a ∈ O, Odd a)
    (hB : TwoAdmissible B) :
    OneAdmissible (assembledSet O B) := by
  intro a ha b hb hab
  simp only [assembledSet, Finset.mem_union] at ha hb
  rcases ha with haOdd | haEven
  · rcases hb with hbOdd | hbEven
    · exact not_conflictOne_of_odd
        (hodd a (Finset.mem_sdiff.mp haOdd).1)
        (hodd b (Finset.mem_sdiff.mp hbOdd).1)
    · rcases mem_doubleSet.mp hbEven with ⟨d, hd, rfl⟩
      exact not_mixed_conflict_of_mem_sdiff haOdd hd
  · rcases hb with hbOdd | hbEven
    · rcases mem_doubleSet.mp haEven with ⟨d, hd, rfl⟩
      intro hconflict
      exact not_mixed_conflict_of_mem_sdiff hbOdd hd
        ((conflictOne_comm b (2 * d)).mpr hconflict)
    · exact oneAdmissible_doubleSet hB a haEven b hbEven hab

/-- If the odd host lies below `2N` and the source below `N`, so does the
assembled set. -/
theorem assembledSet_subset_upto
    {N : ℕ} {O B : Finset ℕ}
    (hO : O ⊆ upto (2 * N))
    (hB : B ⊆ upto N) :
    assembledSet O B ⊆ upto (2 * N) := by
  intro a ha
  simp only [assembledSet, Finset.mem_union] at ha
  rcases ha with haOdd | haEven
  · exact hO (Finset.mem_sdiff.mp haOdd).1
  · rcases mem_doubleSet.mp haEven with ⟨b, hb, rfl⟩
    have hbBounds := mem_upto.mp (hB hb)
    apply mem_upto.mpr
    constructor
    · omega
    · omega

/-- Exact cardinality accounting for the construction. -/
theorem card_assembledSet
    {O B : Finset ℕ} (hodd : ∀ a ∈ O, Odd a) :
    (assembledSet O B).card =
      O.card - (mixedBad O B).card + B.card := by
  have hdisj : Disjoint (O \ mixedBad O B) (doubleSet B) :=
    (disjoint_odd_doubleSet hodd).mono_left Finset.sdiff_subset
  rw [assembledSet, Finset.card_union_of_disjoint hdisj]
  rw [Finset.card_sdiff_of_subset (mixedBad_subset O B), card_doubleSet]

/-- Subtraction-free form of the exact cardinality identity. -/
theorem card_assembledSet_add_mixedBad
    {O B : Finset ℕ} (hodd : ∀ a ∈ O, Odd a) :
    (assembledSet O B).card + (mixedBad O B).card =
      O.card + B.card := by
  rw [card_assembledSet hodd]
  have hle :
      (mixedBad O B).card ≤ O.card :=
    Finset.card_le_card (mixedBad_subset O B)
  omega

/-- The `1/32, 1/32, 1/8` bookkeeping in the paper gives a net
`ρ/16` gain over the odd baseline. -/
theorem assembly_density_bound
    {N : ℕ} {ρ : ℝ} {O B : Finset ℕ}
    (hodd : ∀ a ∈ O, Odd a)
    (hOcard :
      (N : ℝ) - (N : ℝ) * ρ / 32 ≤ (O.card : ℝ))
    (hbad :
      ((mixedBad O B).card : ℝ) ≤ (N : ℝ) * ρ / 32)
    (hBcard :
      (N : ℝ) * ρ / 8 ≤ (B.card : ℝ)) :
    (1 + ρ / 16) * (N : ℝ) ≤ ((assembledSet O B).card : ℝ) := by
  have hcardNat :=
    card_assembledSet_add_mixedBad (O := O) (B := B) hodd
  have hcardReal :
      ((assembledSet O B).card : ℝ) +
          ((mixedBad O B).card : ℝ) =
        (O.card : ℝ) + (B.card : ℝ) := by
    exact_mod_cast hcardNat
  nlinarith

/-- Once the three quantitative finite-set estimates are supplied for one
fixed positive `ρ`, the construction proves the even-endpoint theorem.

This theorem deliberately exposes the exact boundary between the elementary
Lean development and the analytic mean-value estimates.
-/
theorem evenEndpointConclusion_of_witnesses
    {ρ : ℝ} (hρ : 0 < ρ) {N₀ : ℕ}
    (hwit :
      ∀ N ≥ N₀, ∃ O B : Finset ℕ,
        O ⊆ upto (2 * N) ∧
        B ⊆ upto N ∧
        (∀ a ∈ O, Odd a) ∧
        TwoAdmissible B ∧
        ((N : ℝ) - (N : ℝ) * ρ / 32 ≤ (O.card : ℝ)) ∧
        (((mixedBad O B).card : ℝ) ≤ (N : ℝ) * ρ / 32) ∧
        ((N : ℝ) * ρ / 8 ≤ (B.card : ℝ))) :
    EvenEndpointConclusion := by
  refine ⟨ρ / 16, by positivity, N₀, ?_⟩
  intro N hN
  rcases hwit N hN with
    ⟨O, B, hO, hB, hodd, hBadm, hOcard, hbad, hBcard⟩
  refine ⟨assembledSet O B, assembledSet_subset_upto hO hB,
    oneAdmissible_assembledSet hodd hBadm, ?_⟩
  exact assembly_density_bound hodd hOcard hbad hBcard

/-- Each bad odd vertex accounts for at least one mixed edge; in particular,
any external upper bound on the mixed edge count bounds the deletion count. -/
theorem card_mixedBad_le_card_product
    (O B : Finset ℕ) :
    (mixedBad O B).card ≤ (O ×ˢ B).card := by
  classical
  by_cases hB : B = ∅
  · subst B
    simp [mixedBad]
  calc
    (mixedBad O B).card ≤ O.card := Finset.card_le_card (mixedBad_subset O B)
    _ ≤ O.card * B.card := by
      have hBnonempty : B.Nonempty := Finset.nonempty_iff_ne_empty.mpr hB
      have : 1 ≤ B.card := Finset.one_le_card.mpr hBnonempty
      nlinarith
    _ = (O ×ˢ B).card := by simp

end Erdos327
