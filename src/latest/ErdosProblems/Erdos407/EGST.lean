/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos407.Basic

/-!
# The elementary EGST reduction for Erdős 407

Evertse--Győry--Stewart--Tijdeman reduce Newman's conjecture to projective
finiteness for nondegenerate `{2,3}`-unit equations with at most six terms.
This file isolates a particularly small form of that input: the set of all
ratios occurring inside a minimal signed zero-sum block of at most six
positive `{2,3}`-integers is finite.

Everything after `RestrictedProjectiveU23Finiteness` is elementary and is
proved here.  The main argument compares every representation with one fixed
representation.  Every one of its three terms belongs to a minimal vanishing
block in the six-term difference; positivity forces that block to contain a
term of the fixed representation.  The quotient of the two terms belongs to
the fixed finite projective ratio set, giving a finite injective code.
-/

namespace Erdos407.EGST

open scoped BigOperators

/-- The six labelled terms in the difference of two three-term
representations.  The left copy has sign `+1` and the right copy sign `-1`. -/
abbrev Six := Fin 3 ⊕ Fin 3

def sixSign : Six → ℤ
  | Sum.inl _ => 1
  | Sum.inr _ => -1

/-- Positive integral `{2,3}`-units. -/
def IsSmooth23 (x : ℕ) : Prop :=
  ∃ a b : ℕ, x = 2 ^ a * 3 ^ b

def signedSum (x : Six → ℕ) (I : Finset Six) : ℤ :=
  ∑ i ∈ I, sixSign i * (x i : ℤ)

/-- A nonempty vanishing block with no proper nonempty vanishing sub-block. -/
def IsMinimalZeroBlock (x : Six → ℕ) (I : Finset Six) : Prop :=
  I.Nonempty ∧ signedSum x I = 0 ∧
    ∀ J : Finset Six, J.Nonempty → J ⊆ I → J ≠ I → signedSum x J ≠ 0

/-- Ratios occurring between two coordinates in a projectively normalized,
nondegenerate signed `{2,3}`-unit equation supported on at most six terms. -/
def projectiveU23Ratios : Set ℚ :=
  {q | ∃ (x : Six → ℕ) (I : Finset Six) (a b : Six),
    (∀ i, IsSmooth23 (x i) ∧ 0 < x i) ∧
    IsMinimalZeroBlock x I ∧ a ∈ I ∧ b ∈ I ∧
      q = (x a : ℚ) / (x b : ℚ)}

/-- The exact deep input used in this helper.  This is the rational,
`T = {2,3}`, at-most-six-term projective finiteness consequence of EGST
Corollary 1.3.  It is a proposition, not a local axiom. -/
def RestrictedProjectiveU23Finiteness : Prop :=
  projectiveU23Ratios.Finite

private theorem sum_encodeNat (r : Rep) :
    ∑ i, r.encodeNat i = r.value := by
  simp [Rep.encodeNat, Rep.value, Fin.sum_univ_succ, add_assoc]

private theorem encodeNat_smooth23 (r : Rep) (i : Fin 3) :
    IsSmooth23 (r.encodeNat i) := by
  fin_cases i
  · exact ⟨r.a, 0, by simp [Rep.encodeNat]⟩
  · exact ⟨0, r.b, by simp [Rep.encodeNat]⟩
  · exact ⟨r.c, r.d, by simp [Rep.encodeNat]⟩

private theorem encodeNat_pos (r : Rep) (i : Fin 3) :
    0 < r.encodeNat i := by
  fin_cases i <;> simp [Rep.encodeNat]

private def comparison (r s : Rep) : Six → ℕ
  | Sum.inl i => r.encodeNat i
  | Sum.inr i => s.encodeNat i

private theorem comparison_smooth23 (r s : Rep) (i : Six) :
    IsSmooth23 (comparison r s i) := by
  cases i with
  | inl i => exact encodeNat_smooth23 r i
  | inr i => exact encodeNat_smooth23 s i

private theorem comparison_pos (r s : Rep) (i : Six) :
    0 < comparison r s i := by
  cases i with
  | inl i => exact encodeNat_pos r i
  | inr i => exact encodeNat_pos s i

private theorem signedSum_univ_eq_zero {r s : Rep} {n : ℕ}
    (hr : r ∈ solutions n) (hs : s ∈ solutions n) :
    signedSum (comparison r s) Finset.univ = 0 := by
  change r.value = n at hr
  change s.value = n at hs
  have hrz : (∑ i : Fin 3, (r.encodeNat i : ℤ)) = (n : ℤ) := by
    exact_mod_cast (sum_encodeNat r).trans hr
  have hsz : (∑ i : Fin 3, (s.encodeNat i : ℤ)) = (n : ℤ) := by
    exact_mod_cast (sum_encodeNat s).trans hs
  simp [signedSum, Fintype.sum_sum_type, sixSign, comparison, hrz, hsz]

/-- Every specified term of a vanishing six-term sum lies in a minimal
vanishing block. -/
private theorem exists_minimalZeroBlock_containing
    (x : Six → ℕ) (a : Six) (hzero : signedSum x Finset.univ = 0) :
    ∃ I : Finset Six, a ∈ I ∧ IsMinimalZeroBlock x I := by
  classical
  let P : ℕ → Prop := fun k ↦
    ∃ I : Finset Six, a ∈ I ∧ signedSum x I = 0 ∧ I.card = k
  have hP : ∃ k, P k := by
    exact ⟨Finset.univ.card, Finset.univ, Finset.mem_univ _, hzero, rfl⟩
  obtain ⟨I, haI, hIz, hIcard⟩ := Nat.find_spec hP
  have hminimal (J : Finset Six) (haJ : a ∈ J)
      (hJz : signedSum x J = 0) : I.card ≤ J.card := by
    rw [hIcard]
    exact Nat.find_min' hP ⟨J, haJ, hJz, rfl⟩
  refine ⟨I, haI, ⟨⟨a, haI⟩, hIz, ?_⟩⟩
  intro J hJne hJI hJneq hJz
  by_cases haJ : a ∈ J
  · have hJltI : J.card < I.card :=
      Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr ⟨hJI, hJneq⟩)
    exact (not_lt_of_ge (hminimal J haJ hJz)) hJltI
  · let K := I \ J
    have haK : a ∈ K := by simp [K, haI, haJ]
    have hKz : signedSum x K = 0 := by
      have hsum := Finset.sum_sdiff hJI (f := fun i ↦ sixSign i * (x i : ℤ))
      change (∑ i ∈ I, sixSign i * (x i : ℤ)) = 0 at hIz
      change (∑ i ∈ J, sixSign i * (x i : ℤ)) = 0 at hJz
      change (∑ i ∈ I \ J, sixSign i * (x i : ℤ)) = 0
      omega
    have hKltI : K.card < I.card := by
      have hcard := Finset.card_sdiff_add_card_eq_card hJI
      change K.card + J.card = I.card at hcard
      have : 0 < J.card := Finset.card_pos.mpr hJne
      omega
    exact (not_lt_of_ge (hminimal K haK hKz)) hKltI

/-- Positivity forces a zero block containing a left term to contain a right
term as well. -/
private theorem exists_right_mem_minimalBlock
    (x : Six → ℕ) (hxpos : ∀ i, 0 < x i) {I : Finset Six}
    (hI : IsMinimalZeroBlock x I) :
    ∃ j : Fin 3, Sum.inr j ∈ I := by
  classical
  by_contra h
  push Not at h
  have hpos : 0 < signedSum x I := by
    unfold signedSum
    apply Finset.sum_pos
    · intro i hi
      cases i with
      | inl i => simpa [sixSign] using hxpos (Sum.inl i)
      | inr i => exact False.elim (h i hi)
    · exact hI.1
  rw [hI.2.1] at hpos
  exact (lt_irrefl 0 hpos)

/-- Each term of one representation is a projectively bounded ratio times
some term of any fixed representation of the same integer. -/
private theorem exists_projective_ratio
    {r s : Rep} {n : ℕ} (hr : r ∈ solutions n) (hs : s ∈ solutions n)
    (i : Fin 3) :
    ∃ (j : Fin 3) (q : projectiveU23Ratios),
      (r.encodeNat i : ℚ) = q.1 * (s.encodeNat j : ℚ) := by
  classical
  let x := comparison r s
  obtain ⟨I, hiI, hI⟩ :=
    exists_minimalZeroBlock_containing x (Sum.inl i)
      (signedSum_univ_eq_zero hr hs)
  obtain ⟨j, hjI⟩ :=
    exists_right_mem_minimalBlock x (comparison_pos r s) hI
  let q : ℚ := (x (Sum.inl i) : ℚ) / (x (Sum.inr j) : ℚ)
  have hq : q ∈ projectiveU23Ratios := by
    exact ⟨x, I, Sum.inl i, Sum.inr j,
      fun k ↦ ⟨comparison_smooth23 r s k, comparison_pos r s k⟩,
      hI, hiI, hjI, rfl⟩
  refine ⟨j, ⟨q, hq⟩, ?_⟩
  have hne : (x (Sum.inr j) : ℚ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt (comparison_pos r s (Sum.inr j)))
  dsimp [q]
  change (x (Sum.inl i) : ℚ) =
    (x (Sum.inl i) : ℚ) / (x (Sum.inr j) : ℚ) * (x (Sum.inr j) : ℚ)
  exact (div_mul_cancel₀ _ hne).symm

private theorem omega_le_w (n : ℕ) : omega n ≤ w n := by
  change (Rep.summands '' solutions n).ncard ≤ (solutions n).ncard
  exact Set.ncard_image_le (s := solutions n) (hs := solutions_finite n)

/-- The restricted projective `{2,3}`-unit theorem uniformly bounds the
unordered Newman representation classes. -/
theorem omega_bounded_of_restrictedProjectiveU23
    (hU : RestrictedProjectiveU23Finiteness) :
    ∃ C : ℕ, ∀ n : ℕ, omega n ≤ C := by
  classical
  let : Fintype projectiveU23Ratios := hU.fintype
  let Code := Fin 3 → Fin 3 × projectiveU23Ratios
  let C := Fintype.card Code
  refine ⟨C, fun n ↦ ?_⟩
  by_cases hne : (solutions n).Nonempty
  · let s : {r // r ∈ solutions n} := ⟨hne.choose, hne.choose_spec⟩
    have hrel : ∀ (r : {r // r ∈ solutions n}) (i : Fin 3),
        ∃ (j : Fin 3) (q : projectiveU23Ratios),
          (r.1.encodeNat i : ℚ) = q.1 * (s.1.encodeNat j : ℚ) := by
      intro r i
      exact exists_projective_ratio r.2 s.2 i
    choose j q hq using hrel
    let code : {r // r ∈ solutions n} → Code := fun r i ↦ (j r i, q r i)
    have hcode : Function.Injective code := by
      intro r t hrt
      apply Subtype.ext
      apply Rep.encodeNat_injective
      funext i
      have hi := congrFun hrt i
      have hj : j r i = j t i := congrArg Prod.fst hi
      have hqi : q r i = q t i := congrArg Prod.snd hi
      have hrq := hq r i
      have htq := hq t i
      rw [hj, hqi] at hrq
      exact_mod_cast hrq.trans htq.symm
    let : Fintype {r // r ∈ solutions n} := (solutions_finite n).fintype
    have hw : w n ≤ C := by
      change (solutions n).ncard ≤ Fintype.card Code
      rw [← Set.fintypeCard_eq_ncard]
      exact Fintype.card_le_of_injective code hcode
    exact (omega_le_w n).trans hw
  · have hempty : solutions n = ∅ := Set.not_nonempty_iff_eq_empty.mp hne
    simp [omega, classes, hempty]

/-- The literal ordered-exponent count is bounded as well, using the already
proved three-to-one comparison with unordered summand classes. -/
theorem erdos_407_of_restrictedProjectiveU23
    (hU : RestrictedProjectiveU23Finiteness) :
    ∃ C : ℕ, ∀ n : ℕ, w n ≤ C := by
  obtain ⟨C, hC⟩ := omega_bounded_of_restrictedProjectiveU23 hU
  refine ⟨3 * C, fun n ↦ ?_⟩
  exact (w_le_three_mul_omega n).trans (Nat.mul_le_mul_left 3 (hC n))

#print axioms omega_bounded_of_restrictedProjectiveU23
#print axioms erdos_407_of_restrictedProjectiveU23

end Erdos407.EGST
