import ErdosProblems.Erdos157.UniformTrials

/-! Uniform densities, change of finite coordinates, and conditioning. -/

namespace Erdos157.Elementary

noncomputable def finiteDensity {A : Type*} (p : A → Prop) : ℝ :=
  (Nat.card {a // p a} : ℝ) / Nat.card A

theorem finiteDensity_nonneg {A : Type*} (p : A → Prop) : 0 ≤ finiteDensity p := by
  unfold finiteDensity
  positivity

theorem finiteDensity_equiv {A B : Type*} (e : A ≃ B) (p : B → Prop) :
    finiteDensity (fun a => p (e a)) = finiteDensity p := by
  unfold finiteDensity
  rw [Nat.card_congr (e.subtypeEquiv (fun _ => Iff.rfl)), Nat.card_congr e]

theorem finiteDensity_congr {A : Type*} {p q : A → Prop} (h : ∀ a, p a ↔ q a) :
    finiteDensity p = finiteDensity q := by
  unfold finiteDensity
  rw [Nat.card_congr (Equiv.subtypeEquivRight h)]

theorem finiteDensity_mono {A : Type*} [Finite A] {p q : A → Prop}
    (h : ∀ a, p a → q a) : finiteDensity p ≤ finiteDensity q := by
  unfold finiteDensity
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  exact_mod_cast Nat.card_le_card_of_injective
    (fun a : {a // p a} => (⟨a.1, h a.1 a.2⟩ : {a // q a}))
    (fun _ _ he => Subtype.ext (congrArg (fun a : {a // q a} => a.1) he))

theorem finiteDensity_finset {A : Type*} [Fintype A] (s : Finset A) :
    finiteDensity (fun a => a ∈ s) = (s.card : ℝ) / Fintype.card A := by
  simp only [finiteDensity, Nat.card_eq_fintype_card, Fintype.card_coe]

theorem finiteDensity_exists_le_sum {A I : Type*} [Fintype A] [Fintype I]
    (p : I → A → Prop) :
    finiteDensity (fun a => ∃ i, p i a) ≤ ∑ i, finiteDensity (p i) := by
  classical
  let f : (Σ i, {a // p i a}) → {a // ∃ i, p i a} :=
    fun x => ⟨x.2.1, x.1, x.2.2⟩
  have hf : Function.Surjective f := by
    intro a
    obtain ⟨i, hi⟩ := a.2
    exact ⟨⟨i, a.1, hi⟩, Subtype.ext rfl⟩
  have hc : Fintype.card {a // ∃ i, p i a} ≤ ∑ i, Fintype.card {a // p i a} := by
    rw [← Fintype.card_sigma]
    exact Fintype.card_le_of_surjective f hf
  simp only [finiteDensity, Nat.card_eq_fintype_card, ← Finset.sum_div]
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  exact_mod_cast hc

theorem finiteDensity_exists_le {A I : Type*} [Fintype A] [Fintype I]
    (p : I → A → Prop) (δ : ℝ) (h : ∀ i, finiteDensity (p i) ≤ δ) :
    finiteDensity (fun a => ∃ i, p i a) ≤ Fintype.card I * δ := by
  calc
    _ ≤ ∑ i, finiteDensity (p i) := finiteDensity_exists_le_sum p
    _ ≤ ∑ _i : I, δ := Finset.sum_le_sum (fun i _ => h i)
    _ = _ := by simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]

/-- A bound holding after every value of one group of coordinates has been fixed
also holds before conditioning. -/
theorem finiteDensity_prod_le {A B : Type*} [Fintype A] [Fintype B]
    [Nonempty A] [Nonempty B] (p : A → B → Prop) (δ : ℝ)
    (h : ∀ a, finiteDensity (p a) ≤ δ) :
    finiteDensity (fun x : A × B => p x.1 x.2) ≤ δ := by
  classical
  have hB : (0 : ℝ) < Fintype.card B := by exact_mod_cast Fintype.card_pos (α := B)
  have hAB : (0 : ℝ) < Fintype.card A * Fintype.card B := by
    exact mul_pos (by exact_mod_cast Fintype.card_pos (α := A)) hB
  have hs (a : A) : (Fintype.card {b // p a b} : ℝ) ≤ δ * Fintype.card B := by
    have ha := h a
    simp only [finiteDensity, Nat.card_eq_fintype_card] at ha
    exact (div_le_iff₀ hB).mp ha
  have hc : Fintype.card {x : A × B // p x.1 x.2} =
      ∑ a : A, Fintype.card {b // p a b} := by
    rw [Fintype.card_congr (Equiv.subtypeProdEquivSigmaSubtype p), Fintype.card_sigma]
  simp only [finiteDensity, Nat.card_eq_fintype_card, hc, Fintype.card_prod,
    Nat.cast_mul, Nat.cast_sum]
  apply (div_le_iff₀ hAB).mpr
  calc
    _ ≤ ∑ _a : A, δ * Fintype.card B := Finset.sum_le_sum (fun a _ => hs a)
    _ = δ * ((Fintype.card A : ℝ) * Fintype.card B) := by
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      ring

theorem finiteDensity_split_le {I : Type*} {X : I → Type*} (p : I → Prop)
    [DecidablePred p] [Fintype I] [∀ i, Fintype (X i)] [∀ i, Nonempty (X i)]
    (bad : (∀ i, X i) → Prop) (δ : ℝ)
    (h : ∀ a : (∀ i : {i // p i}, X i),
      finiteDensity (fun b => bad ((Equiv.piEquivPiSubtypeProd p X).symm (a, b))) ≤ δ) :
    finiteDensity bad ≤ δ := by
  classical
  let A := ∀ i : {i // p i}, X i
  let B := ∀ i : {i // ¬p i}, X i
  let e : (∀ i, X i) ≃ A × B := Equiv.piEquivPiSubtypeProd p X
  have hp : finiteDensity (fun x : A × B => bad (e.symm x)) ≤ δ :=
    finiteDensity_prod_le (A := A) (B := B) (fun a b => bad (e.symm (a, b))) δ h
  rwa [finiteDensity_equiv e.symm bad] at hp

namespace UniformTrials

theorem finiteDensity_missed_le_exp {A G : Type*} [AddCommGroup A] [AddCommGroup G]
    [Fintype A] [Fintype G] {n : ℕ} (f : A →+ (Fin n → G))
    (hf : Function.Surjective f) (p : G → Prop) :
    finiteDensity (fun a => ∀ j, ¬ p (f a j)) ≤ Real.exp (-(n : ℝ) * finiteDensity p) := by
  classical
  let s := Finset.univ.filter p
  have hp : finiteDensity p = (s.card : ℝ) / Fintype.card G := by
    rw [← finiteDensity_finset s]
    exact finiteDensity_congr (fun a => by simp [s])
  have ha : finiteDensity (fun a => ∀ j, ¬ p (f a j)) =
      ((missed f s).card : ℝ) / Fintype.card A := by
    rw [← finiteDensity_finset (missed f s)]
    exact finiteDensity_congr (fun a => by simp [missed, s])
  rw [ha, hp]
  exact missed_density_le_exp f hf s

end UniformTrials
end Erdos157.Elementary
