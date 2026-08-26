import ErdosProblems.Erdos4.ProductCharacterEncoding

/-!
# The actual bounded-conductor Fourier family

The support records exactly the nonprincipal local components. Characters
whose support product exceeds the square of the divisor cutoff have zero
Fourier coefficient. The remaining characters embed injectively into the
primitive family with conductor at most that square.
-/

open scoped BigOperators

namespace Erdos4.FiniteCharacterSupport

variable {P : Type*} [Fintype P] [DecidableEq P]
    (ell : P → ℕ) [∀ p, Fact (ell p).Prime]

noncomputable def support (chi : ∀ p, DirichletCharacter ℂ (ell p)) : Finset P := by
  classical
  exact Finset.univ.filter (fun p => chi p ≠ 1)

theorem mem_support (chi : ∀ p, DirichletCharacter ℂ (ell p)) (p : P) :
    p ∈ support ell chi ↔ chi p ≠ 1 := by
  classical
  simp only [support, Finset.mem_filter, Finset.mem_univ, true_and]

theorem outside_support (chi : ∀ p, DirichletCharacter ℂ (ell p)) (p : P)
    (hp : p ∉ support ell chi) : chi p = 1 := by
  by_contra h
  exact hp ((mem_support ell chi p).mpr h)

theorem support_nonempty (chi : ∀ p, DirichletCharacter ℂ (ell p))
    (hchi : chi ≠ fun _ => 1) : (support ell chi).Nonempty := by
  classical
  by_contra h
  apply hchi
  funext p
  apply outside_support ell chi p
  exact fun hp => h ⟨p, hp⟩

noncomputable def smallCharacters (R : ℕ) : Finset (∀ p, DirichletCharacter ℂ (ell p)) := by
  classical
  exact Finset.univ.filter (fun chi => chi ≠ (fun _ => 1) ∧
    (∏ p ∈ support ell chi, ell p) ≤ R ^ 2)

theorem mem_smallCharacters (R : ℕ) (chi : ∀ p, DirichletCharacter ℂ (ell p)) :
    chi ∈ smallCharacters ell R ↔ chi ≠ (fun _ => 1) ∧
      (∏ p ∈ support ell chi, ell p) ≤ R ^ 2 := by
  classical
  simp only [smallCharacters, Finset.mem_filter, Finset.mem_univ, true_and]

theorem entry_conductor_le {R : ℕ} (chi : smallCharacters ell R) :
    (ProductCharacterEncoding.entry ell chi.val).1 ≤ R ^ 2 :=
  (ProductCharacterEncoding.conductor_le_support ell chi.val (support ell chi.val)
    (outside_support ell chi.val)).trans ((mem_smallCharacters ell R chi.val).mp chi.property).2

theorem family_injective {R : ℕ} (hinj : Function.Injective ell) :
    Function.Injective (fun chi : smallCharacters ell R => ProductCharacterEncoding.entry ell chi.val) := by
  exact (ProductCharacterEncoding.entry_injective ell
    (ProductCharacterEncoding.pairwise_coprime_of_prime ell
      (fun p => (Fact.out : (ell p).Prime)) hinj)).comp Subtype.val_injective

theorem family_valid {R : ℕ} (chi : smallCharacters ell R) :
    PrimitiveCharacterFamily.Valid (ProductCharacterEncoding.entry ell chi.val) :=
  ProductCharacterEncoding.entry_valid ell (fun p => (Fact.out : (ell p).Prime).pos) chi.val

theorem card_smallCharacters_le (R : ℕ) (hinj : Function.Injective ell) :
    (smallCharacters ell R).card ≤ R ^ 4 := by
  have hh := PrimitiveCharacterFamily.card_family_le_square
    (fun chi : smallCharacters ell R => ProductCharacterEncoding.entry ell chi.val)
    (family_valid ell) (family_injective ell hinj) (entry_conductor_le ell)
  simpa only [Fintype.card_coe, ← pow_mul] using hh

theorem coefficient_zero_outside {k : ℕ} (m : ℝ) (R : ℕ)
    (h : ∀ p, Fin k → ZMod (ell p)) (hh : ∀ p, Function.Injective (h p)) (j : Fin k)
    (chi : ∀ p, DirichletCharacter ℂ (ell p)) (hne : chi ≠ fun _ => 1)
    (hnot : chi ∉ smallCharacters ell R) : UnitFourier.coefficient ell m R h j chi = 0 := by
  have hlarge : R ^ 2 < ∏ p ∈ support ell chi, ell p := by
    by_contra hn
    exact hnot ((mem_smallCharacters ell R chi).mpr ⟨hne, by omega⟩)
  exact UnitFourier.coefficient_eq_zero_of_large_conductor ell m R h hh j chi
    (support ell chi) (fun p hp => (mem_support ell chi p).mp hp) hlarge

theorem norm_nonprincipal_coefficient_le {k : ℕ} {m : ℝ} (hm : 1 ≤ m)
    {R : ℕ} (hR : 2 ≤ R) (hell : ∀ p, k + 2 ≤ ell p)
    (h : ∀ p, Fin k → ZMod (ell p)) (hh : ∀ p, Function.Injective (h p)) (j : Fin k)
    (chi : ∀ p, DirichletCharacter ℂ (ell p)) (hne : chi ≠ fun _ => 1)
    {δ : ℝ} (hδ : δ ≤ 1) (hlocal : ∀ p, 20 * (k : ℝ) ^ 3 ≤ δ * ell p) :
    ‖UnitFourier.coefficient ell m R h j chi‖ ≤
      (RestrictedProductNorm.energy (DivisorCoefficients.coefficient (k := k) m R ell) /
        UnitFourier.unitDensity ell) * δ := by
  have hbound := UnitFourier.norm_coefficient_le ell hm hR hell h hh j chi (support ell chi)
    (fun p hp => (mem_support ell chi p).mp hp) (outside_support ell chi)
  have hprod := ConductorDecay.product_decay_le hδ ell
    (fun p => (Fact.out : (ell p).Prime).pos) (support ell chi)
    (support_nonempty ell chi hne) (fun p _hp => hlocal p)
  exact hbound.trans (mul_le_mul_of_nonneg_left hprod
    (div_nonneg (RestrictedProductNorm.energy_nonneg _) (UnitFourier.unitDensity_pos ell).le))

end Erdos4.FiniteCharacterSupport
