import ErdosProblems.Erdos964.Admissibility
import ErdosProblems.Erdos964.SemiprimeProgressions

/-!
# Reduction to the three-form semiprime sieve theorem

All changes of variables, local admissibility checks, degenerate cases, and
infinitude transfers are elementary and proved here. The analytic theorem
`AdmissibleSemiprimeTriples` remains an explicit hypothesis, not an axiom.
-/

namespace Erdos964

/-- The analytic sieve input: two of three admissible, nonproportional forms
simultaneously take values that are products of two distinct large primes. -/
def AdmissibleSemiprimeTriples : Prop :=
  ∀ A B : Fin 3 → ℕ,
    (∀ i, 0 < A i) → (∀ i, 0 < B i) →
    (∀ i j, i ≠ j → A i * B j ≠ A j * B i) →
    (∀ p : ℕ, p.Prime → ∃ t : ℕ, ∀ i, ¬p ∣ A i * t + B i) →
    ∀ C : ℕ, ∃ i j, i < j ∧
      {t : ℕ | A i * t + B i ∈ E2 C ∧ A j * t + B j ∈ E2 C}.Infinite

private theorem reduced_form_identity (a r b M t : ℕ)
    (hrM : r ∣ M) (hrb : r ∣ L a b) :
    r * (a * (M / r) * t + L a b / r) = L a (M * t + b) := by
  rw [mul_add, Nat.mul_div_cancel' hrb]
  calc
    _ = a * (r * (M / r)) * t + L a b := by ring
    _ = _ := by rw [Nat.mul_div_cancel' hrM]; dsimp [L]; ring

/-- The original prescribed-factor statement follows from the standard
admissible-three-form statement, with no further number-theoretic hypothesis. -/
theorem gpy_of_admissible_semiprime_triples
    (hsieve : AdmissibleSemiprimeTriples) : GoldstonGrahamPintzYildirimStatement := by
  intro a r ha hr hra hdiff hrr C
  by_cases hinj : Function.Injective a
  · obtain ⟨b, hb⟩ := exists_prescribed_factor_progression a r hr hra hrr
    let M := progressionModulus r
    let A : Fin 3 → ℕ := fun i => a i * (M / r i)
    let B : Fin 3 → ℕ := fun i => L (a i) b / r i
    have hM : 0 < M := progressionModulus_pos r hr
    have hdiv i := (quotient_coprime_of_modEq _ _ (hr i) (hb i)).1
    have hriM i : r i ∣ M := dvd_progressionModulus r i
    have hA i : r i * A i = a i * M := by
      dsimp [A]
      rw [mul_left_comm, Nat.mul_div_cancel' (hriM i)]
    have hB i : r i * B i = L (a i) b := Nat.mul_div_cancel' (hdiv i)
    have hApos i : 0 < A i :=
      mul_pos (ha i) (Nat.div_pos (Nat.le_of_dvd hM (hriM i)) (hr i))
    have hBpos i : 0 < B i :=
      Nat.div_pos (Nat.le_of_dvd (Nat.succ_pos _) (hdiv i)) (hr i)
    have hnonprop : ∀ i j, i ≠ j → A i * B j ≠ A j * B i := by
      intro i j hij heq
      have hcross : (a i * M) * L (a j) b = (a j * M) * L (a i) b := by
        calc
          _ = (r i * r j) * (A i * B j) := by rw [← hA i, ← hB j]; ring
          _ = (r i * r j) * (A j * B i) := by rw [heq]
          _ = _ := by rw [← hA j, ← hB i]; ring
      have hc : a i * L (a j) b = a j * L (a i) b := by
        apply Nat.eq_of_mul_eq_mul_left hM
        simpa only [mul_assoc, mul_comm, mul_left_comm] using hcross
      apply hij (hinj ?_)
      dsimp [L] at hc
      nlinarith
    obtain ⟨i, j, hij, hInf⟩ := hsieve A B hApos hBpos hnonprop
      (reduced_forms_admissible a r b hr hdiff hb) C
    refine ⟨i, j, hij, ?_⟩
    have hmap : Function.Injective (fun t : ℕ => M * t + b) := by
      intro t u htu
      exact Nat.eq_of_mul_eq_mul_left hM (Nat.add_right_cancel htu)
    apply (hInf.image hmap.injOn).mono
    rintro x ⟨t, ht, rfl⟩
    have hform k : r k * (A k * t + B k) = L (a k) (M * t + b) :=
      reduced_form_identity _ _ _ _ _ (hriM k) (hdiv k)
    have hquot k : L (a k) (M * t + b) / r k = A k * t + B k := by
      rw [← hform k, Nat.mul_div_cancel_left _ (hr k)]
    exact ⟨⟨_, (hform i).symm⟩, ⟨_, (hform j).symm⟩,
      hquot i ▸ ht.1, hquot j ▸ ht.2⟩
  · exact gpy_of_repeated_coefficient a r ha hdiff hinj C

end Erdos964
