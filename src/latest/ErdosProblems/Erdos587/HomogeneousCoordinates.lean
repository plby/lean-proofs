import ErdosProblems.Erdos587.FinalAssembly
import ErdosProblems.Erdos587.FiniteStructure

/-! Positive natural coordinates for the homogeneous structural output. -/

open scoped BigOperators Pointwise

namespace Erdos587

open NVGeneration

theorem GeneralizedAP.HasHomogeneousBase.positiveForm {Q : GeneralizedAP}
    (hQ : Q.HasHomogeneousBase) : Q.positiveForm.HasHomogeneousBase := by
  intro d hd
  have hsteps : ∀ i, d ∣ Q.step i := fun i => (dvd_abs d (Q.step i)).mp (hd i)
  apply dvd_add (hQ d hsteps)
  apply Finset.dvd_sum
  intro i _
  split_ifs
  · exact dvd_mul_of_dvd_right (hsteps i) _
  · exact dvd_zero _

private theorem fin_all_one {d : ℕ} (hd : d = 1) (i : Fin d) :
    i = ⟨0, by omega⟩ := by
  apply Fin.ext
  have hi := i.isLt
  omega

private theorem fin_all_two {d : ℕ} (hd : d = 2) (i : Fin d) :
    i = ⟨0, by omega⟩ ∨ i = ⟨1, by omega⟩ := by
  have hi := i.isLt
  have : i.val = 0 ∨ i.val = 1 := by omega
  exact this.imp Fin.ext Fin.ext

theorem coefficientSpan_rank_one (Q : GeneralizedAP) (hrank : Q.rank = 1) :
    Q.coefficientSpan =
      (Q.length ⟨0, by omega⟩ : ℤ) * Q.positiveForm.step ⟨0, by simp [hrank]⟩ := by
  have huniv : (Finset.univ : Finset (Fin Q.rank)) = {⟨0, by omega⟩} := by
    ext i
    simp only [Finset.mem_univ, Finset.mem_singleton, true_iff]
    exact fin_all_one hrank i
  simp [GeneralizedAP.coefficientSpan, huniv, GeneralizedAP.positiveForm]

theorem coefficientSpan_rank_two (Q : GeneralizedAP) (hrank : Q.rank = 2) :
    Q.coefficientSpan =
      (Q.length ⟨0, by omega⟩ : ℤ) * Q.positiveForm.step ⟨0, by simp [hrank]⟩ +
      (Q.length ⟨1, by omega⟩ : ℤ) * Q.positiveForm.step ⟨1, by simp [hrank]⟩ := by
  have huniv : (Finset.univ : Finset (Fin Q.rank)) =
      {⟨0, by omega⟩, ⟨1, by omega⟩} := by
    ext i
    simp only [Finset.mem_univ, Finset.mem_insert, Finset.mem_singleton, true_iff]
    exact fin_all_two hrank i
  simp [GeneralizedAP.coefficientSpan, huniv, GeneralizedAP.positiveForm]

theorem exists_homogeneous_natAP_coordinates {A : Finset ℕ}
    (Q : GeneralizedAP) (hproper : Q.Proper) (hrank : Q.rank = 1)
    (hside : ∀ i, 0 < Q.length i) (hhom : Q.HasHomogeneousBase)
    (hsub : Q.carrier ⊆ natToIntFinset A.subsetSum) :
    ∃ r q L : ℕ, 0 < q ∧ 0 < L ∧ q ∣ r ∧
      L = Q.length ⟨0, by omega⟩ ∧ Q.carrier.card = L + 1 ∧
      ((r + q * L : ℕ) : ℤ) = Q.upperEndpoint ∧
      ((q * L : ℕ) : ℤ) = Q.coefficientSpan ∧ natAP r q L ⊆ A.subsetSum := by
  obtain ⟨r, q, L, hq, hr, hqstep, hL, hAP⟩ :=
    exists_natAP_of_translated_rank_one_GAP (A := A) Q 0 hproper hrank hside
      (by
        intro z hz
        obtain ⟨x, hx, y, hy, rfl⟩ := Finset.mem_add.mp hz
        simpa only [Finset.mem_singleton.mp hx, zero_add] using hsub hy)
  simp only [zero_add] at hr
  have hdiv : q ∣ r := by
    have hd : (q : ℤ) ∣ Q.positiveForm.base := hhom.positiveForm (q : ℤ) (by
      intro i
      rw [fin_all_one (show Q.positiveForm.rank = 1 from hrank) i, ← hqstep])
    rw [← hr] at hd
    exact_mod_cast hd
  have hspan : ((q * L : ℕ) : ℤ) = Q.coefficientSpan := by
    rw [coefficientSpan_rank_one Q hrank, Nat.cast_mul, hqstep, hL]
    ring
  refine ⟨r, q, L, hq, by simpa only [hL] using hside ⟨0, by omega⟩,
    hdiv, hL, ?_, ?_, hspan, hAP⟩
  · simpa only [hL] using carrier_card_eq_rank_one Q hproper hrank
  · rw [Nat.cast_add, hr, hspan]
    rfl

theorem exists_homogeneous_natGAP_two_coordinates {A : Finset ℕ}
    (Q : GeneralizedAP) (hproper : Q.Proper) (hrank : Q.rank = 2)
    (hside : ∀ i, 0 < Q.length i) (hhom : Q.HasHomogeneousBase)
    (hsub : Q.carrier ⊆ natToIntFinset A.subsetSum) :
    ∃ r q₁ q₂ L₁ L₂ : ℕ, 0 < q₁ ∧ 0 < q₂ ∧ 0 < L₁ ∧ 0 < L₂ ∧
      q₁.gcd q₂ ∣ r ∧
      L₁ = Q.length ⟨0, by omega⟩ ∧ L₂ = Q.length ⟨1, by omega⟩ ∧
      Q.carrier.card = (L₁ + 1) * (L₂ + 1) ∧
      ((r + q₁ * L₁ + q₂ * L₂ : ℕ) : ℤ) = Q.upperEndpoint ∧
      ((q₁ * L₁ + q₂ * L₂ : ℕ) : ℤ) = Q.coefficientSpan ∧
      (∀ x ≤ L₁, ∀ y ≤ L₂, r + q₁ * x + q₂ * y ∈ A.subsetSum) ∧
      (∀ x₁ ≤ L₁, ∀ y₁ ≤ L₂, ∀ x₂ ≤ L₁, ∀ y₂ ≤ L₂,
        r + q₁ * x₁ + q₂ * y₁ = r + q₁ * x₂ + q₂ * y₂ →
          x₁ = x₂ ∧ y₁ = y₂) := by
  obtain ⟨r, q₁, q₂, L₁, L₂, hq₁, hq₂, hr, hq₁step, hq₂step,
    hL₁, hL₂, hmem, hinj⟩ :=
    exists_natGAP_two_of_translated_rank_two_GAP (A := A) Q 0 hproper hrank hside
      (by
        intro z hz
        obtain ⟨x, hx, y, hy, rfl⟩ := Finset.mem_add.mp hz
        simpa only [Finset.mem_singleton.mp hx, zero_add] using hsub hy)
  simp only [zero_add] at hr
  have hdiv : q₁.gcd q₂ ∣ r := by
    have hd : ((q₁.gcd q₂ : ℕ) : ℤ) ∣ Q.positiveForm.base :=
      hhom.positiveForm _ (by
        intro i
        rcases fin_all_two (show Q.positiveForm.rank = 2 from hrank) i with rfl | rfl
        · rw [← hq₁step]; exact_mod_cast Nat.gcd_dvd_left q₁ q₂
        · rw [← hq₂step]; exact_mod_cast Nat.gcd_dvd_right q₁ q₂)
    rw [← hr] at hd
    exact_mod_cast hd
  have hspan : ((q₁ * L₁ + q₂ * L₂ : ℕ) : ℤ) = Q.coefficientSpan := by
    rw [coefficientSpan_rank_two Q hrank, Nat.cast_add, Nat.cast_mul,
      Nat.cast_mul, hq₁step, hq₂step, hL₁, hL₂]
    ring
  refine ⟨r, q₁, q₂, L₁, L₂, hq₁, hq₂,
    by simpa only [hL₁] using hside ⟨0, by omega⟩,
    by simpa only [hL₂] using hside ⟨1, by omega⟩,
    hdiv, hL₁, hL₂, ?_, ?_, hspan, hmem, hinj⟩
  · simpa only [hL₁, hL₂] using carrier_card_eq_rank_two Q hproper hrank
  · rw [Nat.add_assoc, Nat.cast_add, hr, hspan]
    rfl

end Erdos587
