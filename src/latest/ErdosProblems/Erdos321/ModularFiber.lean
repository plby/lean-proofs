import ErdosProblems.Erdos321.Structural
import Mathlib.NumberTheory.Padics.PadicNorm

namespace Erdos321

/-- Distinct cofactor subset sums stay distinct modulo `p`: equivalently, every
nonzero difference is a `p`-adic unit. -/
def ModularlySeparated (p : ℕ) (B : Finset ℕ) : Prop :=
  ∀ U ∈ B.powerset, ∀ V ∈ B.powerset, U ≠ V →
    padicNorm p (reciprocalSubsetSum U - reciprocalSubsetSum V) = 1

private theorem padicNorm_inv_self_prime (p : ℕ) [Fact p.Prime] :
    padicNorm p ((p : ℚ)⁻¹) = (p : ℚ) := by
  rw [show ((p : ℚ)⁻¹) = (1 : ℚ) / p by simp, padicNorm.div,
    padicNorm.one, padicNorm.padicNorm_p_of_prime]
  simp

/-- Prime-fibre separation lemma.  If old denominators are `p`-adic units and
cofactor subset sums are separated modulo `p`, then no equality can mix the old
part with the scaled `p`-fibre except by matching both parts separately. -/
theorem prime_fiber_collision_separates
    {A B SA TA U V : Finset ℕ} {p : ℕ}
    (hp : p.Prime) (hA : Valid A)
    (hprivate : ∀ a ∈ A, ¬ p ∣ a)
    (hBmod : ModularlySeparated p B)
    (hSA : SA ∈ A.powerset) (hTA : TA ∈ A.powerset)
    (hU : U ∈ B.powerset) (hV : V ∈ B.powerset)
    (hEq : reciprocalSubsetSum SA + ((p : ℚ)⁻¹) * reciprocalSubsetSum U =
      reciprocalSubsetSum TA + ((p : ℚ)⁻¹) * reciprocalSubsetSum V) :
    SA = TA ∧ U = V := by
  classical
  letI : Fact p.Prime := ⟨hp⟩
  have hNormInvOld (a : ℕ) (ha : a ∈ A) :
      padicNorm p ((a : ℚ)⁻¹) = 1 := by
    have hnorm : padicNorm p (a : ℚ) = 1 :=
      (padicNorm.nat_eq_one_iff a).mpr (hprivate a ha)
    rw [show ((a : ℚ)⁻¹) = (1 : ℚ) / a by simp, padicNorm.div,
      padicNorm.one, hnorm]
    norm_num
  have norm_old_sum_le_one (S : Finset ℕ) (hS : S ∈ A.powerset) :
      padicNorm p (reciprocalSubsetSum S) ≤ 1 := by
    apply padicNorm.sum_le'
    · intro a ha
      rw [hNormInvOld a (Finset.mem_powerset.mp hS ha)]
    · norm_num
  have hNormOldDiff : padicNorm p
      (reciprocalSubsetSum SA - reciprocalSubsetSum TA) ≤ 1 :=
    padicNorm.sub.trans (max_le (norm_old_sum_le_one SA hSA)
      (norm_old_sum_le_one TA hTA))
  have hRel : reciprocalSubsetSum SA - reciprocalSubsetSum TA =
      -(((p : ℚ)⁻¹) *
        (reciprocalSubsetSum U - reciprocalSubsetSum V)) := by
    linarith
  have hUV : U = V := by
    by_contra hne
    have hNormFiber : padicNorm p
        (reciprocalSubsetSum U - reciprocalSubsetSum V) = 1 :=
      hBmod U hU V hV hne
    rw [hRel, padicNorm.neg, padicNorm.mul,
      padicNorm_inv_self_prime, hNormFiber, mul_one] at hNormOldDiff
    exact (not_le_of_gt (by exact_mod_cast hp.one_lt)) hNormOldDiff
  subst V
  have hOldEq : reciprocalSubsetSum SA = reciprocalSubsetSum TA := by
    linarith
  exact ⟨hA SA hSA TA hTA hOldEq, rfl⟩

/-- Scale every cofactor in `B` by `p`. -/
def scaleFinset (p : ℕ) (B : Finset ℕ) : Finset ℕ :=
  B.image (fun b => p * b)

private theorem mul_left_injective {p : ℕ} (hp : p ≠ 0) :
    Function.Injective (fun b : ℕ => p * b) := by
  intro a b h
  exact Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero hp) h

/-- Scaling denominators by `p` scales every reciprocal subset sum by `1/p`. -/
theorem reciprocalSubsetSum_scaleFinset {p : ℕ} (hp : p ≠ 0) (B : Finset ℕ) :
    reciprocalSubsetSum (scaleFinset p B) =
      ((p : ℚ)⁻¹) * reciprocalSubsetSum B := by
  have hinj := mul_left_injective hp
  simp only [scaleFinset, reciprocalSubsetSum, Finset.sum_image hinj.injOn,
    Nat.cast_mul]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro b hb
  rw [mul_inv_rev, mul_comm]

private theorem subset_union_scale_decomposition
    {A B S : Finset ℕ} {p : ℕ} (hS : S ⊆ A ∪ scaleFinset p B) :
    S = (S ∩ A) ∪ scaleFinset p (B.filter fun b => p * b ∈ S) := by
  ext n
  constructor
  · intro hnS
    rcases Finset.mem_union.mp (hS hnS) with hnA | hnScale
    · exact Finset.mem_union.mpr (Or.inl (Finset.mem_inter.mpr ⟨hnS, hnA⟩))
    · rcases Finset.mem_image.mp hnScale with ⟨b, hbB, rfl⟩
      apply Finset.mem_union.mpr
      right
      apply Finset.mem_image.mpr
      exact ⟨b, Finset.mem_filter.mpr ⟨hbB, hnS⟩, rfl⟩
  · intro hn
    rcases Finset.mem_union.mp hn with hnOld | hnScale
    · exact (Finset.mem_inter.mp hnOld).1
    · rcases Finset.mem_image.mp hnScale with ⟨b, hb, rfl⟩
      exact (Finset.mem_filter.mp hb).2

private theorem disjoint_old_scale
    {A B : Finset ℕ} {p : ℕ} (hprivate : ∀ a ∈ A, ¬p ∣ a) :
    Disjoint A (scaleFinset p B) := by
  rw [Finset.disjoint_left]
  intro a haA haScale
  rcases Finset.mem_image.mp haScale with ⟨b, hbB, hab⟩
  apply hprivate a haA
  rw [← hab]
  exact dvd_mul_right p b

/-- Every subset of an old-plus-fibre union has a unique old/cofactor sum
formula. -/
theorem reciprocalSubsetSum_union_scale_decomposition
    {A B S : Finset ℕ} {p : ℕ} (hp0 : p ≠ 0)
    (hprivate : ∀ a ∈ A, ¬p ∣ a) (hS : S ⊆ A ∪ scaleFinset p B) :
    reciprocalSubsetSum S =
      reciprocalSubsetSum (S ∩ A) + ((p : ℚ)⁻¹) *
        reciprocalSubsetSum (B.filter fun b => p * b ∈ S) := by
  have hDisjoint : Disjoint (S ∩ A)
      (scaleFinset p (B.filter fun b => p * b ∈ S)) :=
    (disjoint_old_scale hprivate).mono Finset.inter_subset_right
      (Finset.image_subset_image (Finset.filter_subset _ _))
  calc
    reciprocalSubsetSum S = reciprocalSubsetSum
        ((S ∩ A) ∪ scaleFinset p (B.filter fun b => p * b ∈ S)) :=
      congrArg reciprocalSubsetSum (subset_union_scale_decomposition hS)
    _ = reciprocalSubsetSum (S ∩ A) +
        reciprocalSubsetSum (scaleFinset p (B.filter fun b => p * b ∈ S)) := by
      exact Finset.sum_union hDisjoint
    _ = reciprocalSubsetSum (S ∩ A) + ((p : ℚ)⁻¹) *
        reciprocalSubsetSum (B.filter fun b => p * b ∈ S) := by
      rw [reciprocalSubsetSum_scaleFinset hp0]

/-- Modularly separated cofactors can be added as an entire scaled prime fibre
to any valid old set on which `p` is private. -/
theorem valid_union_scaleFinset_of_modularlySeparated
    {A B : Finset ℕ} {p : ℕ} (hp : p.Prime) (hA : Valid A)
    (hprivate : ∀ a ∈ A, ¬p ∣ a) (hBmod : ModularlySeparated p B) :
    Valid (A ∪ scaleFinset p B) := by
  classical
  intro S hS T hT hEq
  let SU := B.filter fun b => p * b ∈ S
  let TU := B.filter fun b => p * b ∈ T
  have hSsub : S ⊆ A ∪ scaleFinset p B := Finset.mem_powerset.mp hS
  have hTsub : T ⊆ A ∪ scaleFinset p B := Finset.mem_powerset.mp hT
  have hSdecomp := reciprocalSubsetSum_union_scale_decomposition hp.ne_zero
    hprivate hSsub
  have hTdecomp := reciprocalSubsetSum_union_scale_decomposition hp.ne_zero
    hprivate hTsub
  have hEqParts : reciprocalSubsetSum (S ∩ A) +
      ((p : ℚ)⁻¹) * reciprocalSubsetSum SU =
      reciprocalSubsetSum (T ∩ A) +
      ((p : ℚ)⁻¹) * reciprocalSubsetSum TU := by
    dsimp [SU, TU]
    linarith
  have hSeparated := prime_fiber_collision_separates hp hA hprivate hBmod
    (Finset.mem_powerset.mpr Finset.inter_subset_right)
    (Finset.mem_powerset.mpr Finset.inter_subset_right)
    (Finset.mem_powerset.mpr (Finset.filter_subset _ _))
    (Finset.mem_powerset.mpr (Finset.filter_subset _ _)) hEqParts
  have hSset := subset_union_scale_decomposition hSsub
  have hTset := subset_union_scale_decomposition hTsub
  rw [hSset, hTset, hSeparated.1, hSeparated.2]

end Erdos321
