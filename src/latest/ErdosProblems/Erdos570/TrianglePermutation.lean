/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos570.TriangleCandidates

/-!
# Permutation averaging on fixed-cardinality subsets

The symmetric group acts transitively on the `δ`-subsets of a finite type.
Summing over the whole group therefore gives the same orbit sum from every
starting subset.  The last theorem packages the averaging consequence used
to place the core of the target graph in a blue clique.
-/

open scoped BigOperators

noncomputable section

namespace Erdos570

/-- The finite type of `δ`-subsets of `T`. -/
abbrev DeltaSubsets (T : Type*) [Fintype T] [DecidableEq T] (δ : ℕ) :=
  ↑((Finset.univ : Finset T).powersetCard δ)

/-- A permutation acts on fixed-cardinality subsets. -/
def permuteDeltaSubset {T : Type*} [Fintype T] [DecidableEq T] {δ : ℕ}
    (σ : Equiv.Perm T) : DeltaSubsets T δ ≃ DeltaSubsets T δ where
  toFun I := ⟨I.1.map σ.toEmbedding, by
    rw [Finset.mem_powersetCard]
    exact ⟨Finset.subset_univ _, by
      rw [Finset.card_map]
      exact (Finset.mem_powersetCard.mp I.2).2⟩⟩
  invFun I := ⟨I.1.map σ.symm.toEmbedding, by
    rw [Finset.mem_powersetCard]
    exact ⟨Finset.subset_univ _, by
      rw [Finset.card_map]
      exact (Finset.mem_powersetCard.mp I.2).2⟩⟩
  left_inv I := by
    apply Subtype.ext
    ext x
    simp
  right_inv I := by
    apply Subtype.ext
    ext x
    simp

@[simp]
theorem permuteDeltaSubset_val {T : Type*} [Fintype T] [DecidableEq T]
    {δ : ℕ} (σ : Equiv.Perm T) (I : DeltaSubsets T δ) :
    (permuteDeltaSubset σ I).1 = I.1.map σ.toEmbedding := rfl

@[simp]
theorem permuteDeltaSubset_refl {T : Type*} [Fintype T] [DecidableEq T]
    {δ : ℕ} (I : DeltaSubsets T δ) :
    permuteDeltaSubset (Equiv.refl T) I = I := by
  apply Subtype.ext
  ext x
  simp [permuteDeltaSubset]

theorem permuteDeltaSubset_mul {T : Type*} [Fintype T] [DecidableEq T]
    {δ : ℕ} (σ τ : Equiv.Perm T) (I : DeltaSubsets T δ) :
    permuteDeltaSubset (σ * τ) I =
      permuteDeltaSubset σ (permuteDeltaSubset τ I) := by
  apply Subtype.ext
  change I.1.map (σ * τ).toEmbedding =
    (I.1.map τ.toEmbedding).map σ.toEmbedding
  rw [Finset.map_map]
  rfl

/-- Any two fixed-cardinality subsets are related by a permutation. -/
theorem exists_permuteDeltaSubset_eq {T : Type*} [Fintype T]
    [DecidableEq T] {δ : ℕ} (I J : DeltaSubsets T δ) :
    ∃ σ : Equiv.Perm T, permuteDeltaSubset σ I = J := by
  have hcard : I.1.card = J.1.card := by
    rw [(Finset.mem_powersetCard.mp I.2).2,
      (Finset.mem_powersetCard.mp J.2).2]
  obtain ⟨σ, hσ⟩ := Equiv.Perm.exists_map_finset_eq I.1 J.1 hcard
  exact ⟨σ, Subtype.ext hσ⟩

/-- Orbit sums of the transitive permutation action are independent of the
starting `δ`-subset. -/
theorem sum_permutations_apply_eq
    {T : Type*} [Fintype T] [DecidableEq T] {δ : ℕ}
    (g : DeltaSubsets T δ → ℕ) (I J : DeltaSubsets T δ) :
    ∑ σ : Equiv.Perm T, g (permuteDeltaSubset σ I) =
      ∑ σ : Equiv.Perm T, g (permuteDeltaSubset σ J) := by
  obtain ⟨τ, hτ⟩ := exists_permuteDeltaSubset_eq I J
  calc
    ∑ σ : Equiv.Perm T, g (permuteDeltaSubset σ I) =
        ∑ σ : Equiv.Perm T,
          g (permuteDeltaSubset (σ * τ) I) := by
            simpa using Equiv.sum_comp (Equiv.mulRight τ)
              (fun σ : Equiv.Perm T ↦
                g (permuteDeltaSubset σ I)) |>.symm
    _ = ∑ σ : Equiv.Perm T,
          g (permuteDeltaSubset σ J) := by
            apply Finset.sum_congr rfl
            intro σ hσ
            rw [permuteDeltaSubset_mul, hτ]

/-- The exact orbit-sum identity for one fixed starting subset. -/
theorem card_mul_sum_permutations_apply
    {T : Type*} [Fintype T] [DecidableEq T] {δ : ℕ}
    (g : DeltaSubsets T δ → ℕ) (I : DeltaSubsets T δ) :
    Fintype.card (DeltaSubsets T δ) *
        (∑ σ : Equiv.Perm T, g (permuteDeltaSubset σ I)) =
      Fintype.card (Equiv.Perm T) * ∑ J : DeltaSubsets T δ, g J := by
  calc
    Fintype.card (DeltaSubsets T δ) *
        (∑ σ : Equiv.Perm T, g (permuteDeltaSubset σ I)) =
        ∑ J : DeltaSubsets T δ,
          ∑ σ : Equiv.Perm T, g (permuteDeltaSubset σ I) := by simp
    _ = ∑ J : DeltaSubsets T δ,
          ∑ σ : Equiv.Perm T, g (permuteDeltaSubset σ J) := by
            apply Finset.sum_congr rfl
            intro J hJ
            exact sum_permutations_apply_eq g I J
    _ = ∑ σ : Equiv.Perm T,
          ∑ J : DeltaSubsets T δ, g (permuteDeltaSubset σ J) := by
            rw [Finset.sum_comm]
    _ = ∑ σ : Equiv.Perm T, ∑ J : DeltaSubsets T δ, g J := by
            apply Finset.sum_congr rfl
            intro σ hσ
            exact (permuteDeltaSubset σ).sum_comp g
    _ = Fintype.card (Equiv.Perm T) *
        ∑ J : DeltaSubsets T δ, g J := by simp

/-- The exact permutation double average for an arbitrary family of
starting subsets. -/
theorem card_mul_sum_permutations_family
    {A T : Type*} [Fintype A] [Fintype T] [DecidableEq T] {δ : ℕ}
    (g : DeltaSubsets T δ → ℕ) (I : A → DeltaSubsets T δ) :
    Fintype.card (DeltaSubsets T δ) *
        (∑ σ : Equiv.Perm T, ∑ a : A,
          g (permuteDeltaSubset σ (I a))) =
      Fintype.card (Equiv.Perm T) * Fintype.card A *
        ∑ J : DeltaSubsets T δ, g J := by
  calc
    Fintype.card (DeltaSubsets T δ) *
        (∑ σ : Equiv.Perm T, ∑ a : A,
          g (permuteDeltaSubset σ (I a))) =
        ∑ a : A, Fintype.card (DeltaSubsets T δ) *
          (∑ σ : Equiv.Perm T,
            g (permuteDeltaSubset σ (I a))) := by
              rw [Finset.sum_comm]
              simp only [Finset.mul_sum]
    _ = ∑ _a : A, Fintype.card (Equiv.Perm T) *
          ∑ J : DeltaSubsets T δ, g J := by
            apply Finset.sum_congr rfl
            intro a ha
            exact card_mul_sum_permutations_apply g (I a)
    _ = Fintype.card (Equiv.Perm T) * Fintype.card A *
        ∑ J : DeltaSubsets T δ, g J := by
          simp
          ring

theorem exists_le_of_card_mul_le_sum
    {A : Type*} [Fintype A] [Nonempty A] (u : A → ℕ) {L : ℕ}
    (h : Fintype.card A * L ≤ ∑ a : A, u a) :
    ∃ a : A, L ≤ u a := by
  by_contra hnone
  push_neg at hnone
  have hstrict : (∑ a : A, u a) < ∑ _a : A, L := by
    apply Finset.sum_lt_sum_of_nonempty Finset.univ_nonempty
    intro a ha
    exact hnone a
  simp only [Finset.sum_const, Finset.card_univ,
    Nat.nsmul_eq_mul] at hstrict
  omega

/-- Permutation averaging: if the total mass on all `δ`-subsets dominates
the desired average, one placement of every prescribed starting subset has
at least that mass. -/
theorem exists_permutation_with_large_sum
    {A T : Type*} [Fintype A] [Nonempty A] [Fintype T] [DecidableEq T]
    {δ L : ℕ}
    (g : DeltaSubsets T δ → ℕ) (I : A → DeltaSubsets T δ)
    (h : Fintype.card (DeltaSubsets T δ) * L ≤
      Fintype.card A * ∑ J : DeltaSubsets T δ, g J) :
    ∃ σ : Equiv.Perm T, L ≤
      ∑ a : A, g (permuteDeltaSubset σ (I a)) := by
  have hpermPos : 0 < Fintype.card (Equiv.Perm T) :=
    Fintype.card_pos_iff.mpr ⟨Equiv.refl T⟩
  have hsubsetPos : 0 < Fintype.card (DeltaSubsets T δ) := by
    exact Fintype.card_pos_iff.mpr ⟨I (Classical.choice inferInstance)⟩
  have hscaled : Fintype.card (Equiv.Perm T) *
        (Fintype.card (DeltaSubsets T δ) * L) ≤
      Fintype.card (Equiv.Perm T) *
        (Fintype.card A * ∑ J : DeltaSubsets T δ, g J) :=
    Nat.mul_le_mul_left _ h
  have htotal : Fintype.card (Equiv.Perm T) * L ≤
      ∑ σ : Equiv.Perm T, ∑ a : A,
        g (permuteDeltaSubset σ (I a)) := by
    apply Nat.le_of_mul_le_mul_left (c := Fintype.card (DeltaSubsets T δ))
    · calc
        Fintype.card (DeltaSubsets T δ) *
            (Fintype.card (Equiv.Perm T) * L) =
            Fintype.card (Equiv.Perm T) *
              (Fintype.card (DeltaSubsets T δ) * L) := by ring
        _ ≤ Fintype.card (Equiv.Perm T) *
              (Fintype.card A * ∑ J : DeltaSubsets T δ, g J) := hscaled
        _ = Fintype.card (DeltaSubsets T δ) *
            (∑ σ : Equiv.Perm T, ∑ a : A,
              g (permuteDeltaSubset σ (I a))) := by
                rw [card_mul_sum_permutations_family]
                ring
    · exact hsubsetPos
  exact exists_le_of_card_mul_le_sum _ htotal

end Erdos570
