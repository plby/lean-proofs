import ErdosProblems.Erdos117.ModuleLength
import ErdosProblems.Erdos117.CentralSeries

/-!
# Composition length and orders of finite abelian p-groups

The bilinear length theorem becomes a bound on group order through the
identity `|A| = p^(length_ℤ A)`. The prime-factor characters used below were
constructed in `CentralSeries`; no structure theorem for abelian groups is
assumed.
-/

namespace Erdos117

theorem moduleLength_int_zmod (p : ℕ) [Fact p.Prime] :
    moduleLength ℤ (ZMod p) = 1 := by
  have h : Module.length ℤ (ZMod p) = Module.length (ZMod p) (ZMod p) :=
    Module.length_eq_of_surjective (by exact ZMod.intCast_surjective)
  unfold moduleLength
  rw [h, Module.length_eq_one]
  rfl

theorem card_eq_pow_moduleLength {p : ℕ} [Fact p.Prime]
    {A : Type*} [CommGroup A] [Finite A] (hA : IsPGroup p A) :
    Nat.card A = p ^ moduleLength ℤ (Additive A) := by
  classical
  generalize hcard : Nat.card A = d
  induction d using Nat.strong_induction_on generalizing A with
  | h d ih =>
    rcases subsingleton_or_nontrivial A with htriv | hnontriv
    · have : Subsingleton A := htriv
      have : Subsingleton (Additive A) := inferInstance
      have hlen : moduleLength ℤ (Additive A) = 0 :=
        moduleLength_eq_zero_iff.mpr inferInstance
      rw [hlen, pow_zero, ← hcard]
      exact Nat.card_eq_one_iff_unique.mpr ⟨htriv, ⟨1⟩⟩
    · have : Nontrivial A := hnontriv
      obtain ⟨χ, hχ, _, hmul⟩ := exists_prime_character hA
      let K := χ.ker
      have hKlt : Nat.card K < d := by
        have hpos : 0 < Nat.card K := Nat.card_pos
        have hp : 2 ≤ p := (Fact.out : p.Prime).two_le
        dsimp [K] at hpos ⊢
        nlinarith
      have hKcard := ih (Nat.card K) hKlt
        (hA.of_injective K.subtype K.subtype_injective) rfl
      let f : Additive K →ₗ[ℤ] Additive A := K.subtype.toAdditive.toIntLinearMap
      let g : Additive A →ₗ[ℤ] ZMod p := χ.toAdditiveLeft.toIntLinearMap
      have hf : Function.Injective f := K.subtype_injective
      have hg : Function.Surjective g := hχ
      have hfg : Function.Exact f g := by
        intro x
        constructor
        · intro hx
          exact ⟨Additive.ofMul ⟨x.toMul, hx⟩, rfl⟩
        · rintro ⟨x, rfl⟩
          exact x.toMul.property
      have hlen := moduleLength_eq_add_of_exact f g hf hg hfg
      rw [moduleLength_int_zmod] at hlen
      rw [hlen, pow_succ, ← hKcard, ← hcard]
      exact hmul.symm

theorem moduleLength_int_le_of_card_le {p b : ℕ} [Fact p.Prime]
    {A : Type*} [AddCommGroup A] [Finite A]
    (hA : IsPGroup p (Multiplicative A)) (hcard : Nat.card A ≤ p ^ b) :
    moduleLength ℤ A ≤ b := by
  have h := card_eq_pow_moduleLength hA
  change Nat.card A = p ^ moduleLength ℤ A at h
  rw [h] at hcard
  exact (Nat.pow_le_pow_iff_right (Fact.out : p.Prime).one_lt).mp hcard

end Erdos117
