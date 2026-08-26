import ErdosProblems.Erdos633.ConjugateAngleFormula
import Mathlib.Data.ZMod.Units

/-!
# Lifting reduced residues to cyclotomic conjugations

Every unit modulo an individual angle denominator lifts to a unit modulo
the common cyclotomic modulus. This connects the geometric conjugate-angle
inequalities to the elementary denominator bounds.
-/

namespace Erdos633

theorem exists_coprime_lift_mul_residue (m n M r : ℕ)
    (hM : 0 < M) (hd : n ∣ M) (hm : m.Coprime n)
    (hr : r.Coprime n) (hrn : r < n) :
    ∃ k : ℕ, k.Coprime M ∧ (k * m) % n = r := by
  let : NeZero M := ⟨ne_of_gt hM⟩
  let v : (ZMod n)ˣ := ZMod.unitOfCoprime r hr * (ZMod.unitOfCoprime m hm)⁻¹
  obtain ⟨u, hu⟩ := ZMod.unitsMap_surjective hd v
  let k : ℕ := (u : ZMod M).val
  have hku : (k : ZMod M) = u := ZMod.natCast_zmod_val _
  have hkn : (k : ZMod n) = ZMod.unitsMap hd u := by
    rw [ZMod.unitsMap_val, ← hku, ZMod.cast_natCast hd]
  have hmul : (k : ZMod n) * (m : ZMod n) = (r : ZMod n) := by
    calc
      _ = ((ZMod.unitsMap hd u * ZMod.unitOfCoprime m hm : (ZMod n)ˣ) : ZMod n) := by
        simp only [Units.val_mul, ZMod.coe_unitOfCoprime, hkn]
      _ = ((ZMod.unitOfCoprime r hr : (ZMod n)ˣ) : ZMod n) := by
        rw [hu]
        simp [v, mul_assoc]
      _ = _ := ZMod.coe_unitOfCoprime r hr
  refine ⟨k, ZMod.val_coe_unit_coprime u, ?_⟩
  have he := (ZMod.natCast_eq_natCast_iff' (k * m) r n).mp (by
    simpa only [Nat.cast_mul] using hmul)
  simpa only [Nat.mod_eq_of_lt hrn] using he

theorem rational_eq_natAbs_num_div_den (θ : ℚ) (hθ : 0 ≤ θ) :
    θ = (θ.num.natAbs : ℚ) / θ.den := by
  have hn : 0 ≤ θ.num := Rat.num_nonneg.mpr hθ
  have he : (θ.num.natAbs : ℤ) = θ.num := Int.natAbs_of_nonneg hn
  have hq : (θ.num : ℚ) = (θ.num.natAbs : ℚ) := by
    simpa only [Int.cast_natCast] using congrArg (fun z : ℤ => (z : ℚ)) he.symm
  calc
    θ = (θ.num : ℚ) / θ.den := θ.num_div_den.symm
    _ = _ := by rw [hq]

theorem exists_coprime_lift_rational_fract (θ : ℚ) (M r : ℕ)
    (hθ : 0 ≤ θ) (hM : 0 < M) (hd : θ.den ∣ M)
    (hr : r.Coprime θ.den) (hrn : r < θ.den) :
    ∃ k : ℕ, k.Coprime M ∧ Int.fract ((k : ℚ) * θ) = (r : ℚ) / θ.den := by
  obtain ⟨k, hk, he⟩ := exists_coprime_lift_mul_residue θ.num.natAbs θ.den M r
    hM hd θ.reduced hr hrn
  refine ⟨k, hk, ?_⟩
  have hmul : (k : ℚ) * θ = ((k * θ.num.natAbs : ℕ) : ℚ) / θ.den := by
    calc
      _ = (k : ℚ) * ((θ.num.natAbs : ℚ) / θ.den) := by
        congr 1
        exact rational_eq_natAbs_num_div_den θ hθ
      _ = _ := by push_cast; ring
  rw [hmul, Int.fract_div_natCast_eq_div_natCast_mod, he]

theorem rational_unit_bound_reduced_residues (θ : ℚ) (M p : ℕ)
    (hθ : 0 ≤ θ) (hM : 0 < M) (hd : θ.den ∣ M)
    (h : ∀ k : ℕ, k.Coprime M →
      (p : ℚ) * Int.fract ((k : ℚ) * θ) < 1 ∨
      (p : ℚ) * (1 - Int.fract ((k : ℚ) * θ)) < 1) :
    ∀ r : ℕ, 0 < r → r < θ.den → r.Coprime θ.den →
      p * r < θ.den ∨ p * (θ.den - r) < θ.den := by
  intro r _hr hrn hc
  obtain ⟨k, hk, he⟩ := exists_coprime_lift_rational_fract θ M r hθ hM hd hc hrn
  have hn : (0 : ℚ) < θ.den := by exact_mod_cast θ.den_pos
  rcases h k hk with hlo | hhi
  · rw [he, ← mul_div_assoc] at hlo
    have hh := (div_lt_iff₀ hn).mp hlo
    have hh' : (p : ℚ) * r < θ.den := by simpa only [one_mul] using hh
    left
    exact_mod_cast hh'
  · rw [he] at hhi
    have hsub : (1 : ℚ) - (r : ℚ) / θ.den = ((θ.den - r : ℕ) : ℚ) / θ.den := by
      rw [Nat.cast_sub hrn.le]
      field_simp
    rw [hsub, ← mul_div_assoc] at hhi
    have hh := (div_lt_iff₀ hn).mp hhi
    have hh' : (p : ℚ) * (θ.den - r : ℕ) < θ.den := by
      simpa only [one_mul] using hh
    right
    exact_mod_cast hh'

theorem rational_unit_bound_numerator (θ : ℚ) (p : ℕ)
    (hθ : 0 < θ) (hsmall : (p : ℚ) * θ < 1) :
    0 < θ.num.natAbs ∧ p * θ.num.natAbs < θ.den := by
  have hrep := rational_eq_natAbs_num_div_den θ hθ.le
  have hn : (0 : ℚ) < θ.den := by exact_mod_cast θ.den_pos
  have hnum : (0 : ℚ) < θ.num.natAbs := by
    have h : (0 : ℚ) < (θ.num.natAbs : ℚ) / θ.den := by rwa [← hrep]
    exact (div_pos_iff_of_pos_right hn).mp h
  have hp : (p : ℚ) * θ.num.natAbs < θ.den := by
    rw [hrep, ← mul_div_assoc] at hsmall
    simpa only [one_mul] using (div_lt_iff₀ hn).mp hsmall
  exact ⟨by exact_mod_cast hnum, by exact_mod_cast hp⟩

theorem rational_unit_bound_angle_cases (θ : ℚ) (M p : ℕ)
    (hθ : 0 < θ) (hM : 0 < M) (hd : θ.den ∣ M) (hp : 3 ≤ p)
    (hsmall : (p : ℚ) * θ < 1)
    (h : ∀ k : ℕ, k.Coprime M →
      (p : ℚ) * Int.fract ((k : ℚ) * θ) < 1 ∨
      (p : ℚ) * (1 - Int.fract ((k : ℚ) * θ)) < 1) :
    θ = 1 / 4 ∨ θ = 1 / 6 ∨ θ = 1 / 10 ∨ θ = 3 / 10 := by
  obtain ⟨hm, hmn⟩ := rational_unit_bound_numerator θ p hθ hsmall
  have hmden : θ.num.natAbs < θ.den := by nlinarith
  have hc := rational_unit_bound_reduced_residues θ M p hθ.le hM hd h
  have hrep := rational_eq_natAbs_num_div_den θ hθ.le
  rcases multiplicity_three_reduced_angle θ.num.natAbs θ.den p
      hm hmden θ.reduced hp hmn hc with h4 | h6 | h10 | h30
  · exact Or.inl (by simpa only [h4.1, h4.2, Nat.cast_one, Nat.cast_ofNat] using hrep)
  · exact Or.inr (Or.inl (by
      simpa only [h6.1, h6.2, Nat.cast_one, Nat.cast_ofNat] using hrep))
  · exact Or.inr (Or.inr (Or.inl (by
      simpa only [h10.1, h10.2, Nat.cast_one, Nat.cast_ofNat] using hrep)))
  · exact Or.inr (Or.inr (Or.inr (by
      simpa only [h30.1, h30.2, Nat.cast_ofNat] using hrep)))

theorem rational_unit_bound_multiplicity_le_five (θ : ℚ) (M p : ℕ)
    (hθ : 0 < θ) (hM : 0 < M) (hd : θ.den ∣ M) (hp : 3 ≤ p)
    (hsmall : (p : ℚ) * θ < 1)
    (h : ∀ k : ℕ, k.Coprime M →
      (p : ℚ) * Int.fract ((k : ℚ) * θ) < 1 ∨
      (p : ℚ) * (1 - Int.fract ((k : ℚ) * θ)) < 1) : p ≤ 5 := by
  obtain ⟨hm, hmn⟩ := rational_unit_bound_numerator θ p hθ hsmall
  have hmden : θ.num.natAbs < θ.den := by nlinarith
  exact rational_angle_outer_multiplicity_le_five θ.num.natAbs θ.den p
    hm hmden hp hmn (rational_unit_bound_reduced_residues θ M p hθ.le hM hd h)

theorem rational_unit_bound_angle_sixth (θ : ℚ) (M p : ℕ)
    (hθ : 0 < θ) (hM : 0 < M) (hd : θ.den ∣ M) (hp : 4 ≤ p)
    (hsmall : (p : ℚ) * θ < 1)
    (h : ∀ k : ℕ, k.Coprime M →
      (p : ℚ) * Int.fract ((k : ℚ) * θ) < 1 ∨
      (p : ℚ) * (1 - Int.fract ((k : ℚ) * θ)) < 1) : θ = 1 / 6 := by
  obtain ⟨hm, hmn⟩ := rational_unit_bound_numerator θ p hθ hsmall
  have hc := rational_unit_bound_reduced_residues θ M p hθ.le hM hd h
  have hn : θ.den = 6 := quarter_unit_residue_denominator θ.den (by nlinarith) (by
    intro r hr hrn hrc
    rcases hc r hr hrn hrc with hlow | hhigh
    · exact Or.inl (by nlinarith)
    · exact Or.inr (by nlinarith))
  have hnum : θ.num.natAbs = 1 := by rw [hn] at hmn; nlinarith
  simpa only [hn, hnum, Nat.cast_one, Nat.cast_ofNat] using
    rational_eq_natAbs_num_div_den θ hθ.le

end Erdos633
