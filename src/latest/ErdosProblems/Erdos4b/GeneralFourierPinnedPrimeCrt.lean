/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos4b.GeneralFourierPinnedSupportedCompatibility

/-!
# The exact reduced progression of a supported pinned divisor system

CRT constructs a witness using prime-local residues, but the period is
the lcm of the actual divisor coordinates, not the cutoff primorial.
-/

namespace Erdos4b

noncomputable section

open scoped BigOperators

def PinnedDivisorPrimeEquations {K : ℕ} (h : Fin K) (P : Finset ℕ) (w m p₀ q : ℕ)
    (d : (PinnedShiftIndex h ⊕ PinnedShiftIndex h) → Bool → ℕ) : Prop :=
  ∀ p : P,
    (∀ i, p.val ∣ Nat.lcm (d (.inl i) false) (d (.inl i) true) →
      (p₀ : ZMod p.val) + pinnedIndexSlope h w p.val i * (q : ZMod p.val) = 0) ∧
    (∀ i, p.val ∣ Nat.lcm (d (.inr i) false) (d (.inr i) true) →
      (m : ZMod p.val) * ((p₀ : ZMod p.val) +
        pinnedIndexSlope h w p.val i * (q : ZMod p.val)) = 1)

def pinnedFlatDivisorModulus {K : ℕ} (h : Fin K)
    (d : (PinnedShiftIndex h ⊕ PinnedShiftIndex h) → Bool → ℕ) : ℕ :=
  (Finset.univ : Finset ((PinnedShiftIndex h ⊕ PinnedShiftIndex h) × Bool)).lcm
    (fun ib ↦ d ib.1 ib.2)

theorem pinnedFlatDivisorModulus_dvd_cutoff {K : ℕ} (h : Fin K) (P : Finset ℕ)
    (d : (PinnedShiftIndex h ⊕ PinnedShiftIndex h) → Bool → ℕ)
    (hdiv : ∀ i b, d i b ∣ ∏ p ∈ P, p) : pinnedFlatDivisorModulus h d ∣ ∏ p ∈ P, p :=
  Finset.lcm_dvd fun ib _hib ↦ hdiv ib.1 ib.2

theorem dvd_pinnedFlatDivisorModulus {K : ℕ} (h : Fin K)
    (d : (PinnedShiftIndex h ⊕ PinnedShiftIndex h) → Bool → ℕ)
    (i : PinnedShiftIndex h ⊕ PinnedShiftIndex h) (b : Bool) :
    d i b ∣ pinnedFlatDivisorModulus h d := Finset.dvd_lcm (Finset.mem_univ (i, b))

theorem pinnedFlatDivisorModulus_squarefree {K : ℕ} (h : Fin K) (P : Finset ℕ)
    (hP : ∀ p ∈ P, p.Prime)
    (d : (PinnedShiftIndex h ⊕ PinnedShiftIndex h) → Bool → ℕ)
    (hdiv : ∀ i b, d i b ∣ ∏ p ∈ P, p) : Squarefree (pinnedFlatDivisorModulus h d) :=
  (primeFinsetProduct_squarefree P hP).squarefree_of_dvd
    (pinnedFlatDivisorModulus_dvd_cutoff h P d hdiv)

theorem exists_pinnedPrimeCrt_reduced_class
    {K w m p₀ : ℕ} (h : Fin K) (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (hrough : ∀ p ∈ P, w < p) (hKw : K ≤ w)
    (d : (PinnedShiftIndex h ⊕ PinnedShiftIndex h) → Bool → ℕ)
    (hdiv : ∀ i b, d i b ∣ ∏ p ∈ P, p)
    (hsol : ∀ p : P, PinnedLocalDivisorSolvable h w m p₀ p.val
      (fun i ↦ Nat.lcm (d (.inl i) false) (d (.inl i) true))
      (fun i ↦ Nat.lcm (d (.inr i) false) (d (.inr i) true))) :
    ∃ r : ℕ, r.Coprime (pinnedFlatDivisorModulus h d) ∧
      ∀ q : ℕ, PinnedDivisorPrimeEquations h P w m p₀ q d ↔
        q ≡ r [MOD pinnedFlatDivisorModulus h d] := by
  classical
  choose z hz0 hzD hzE using hsol
  have hpair : Set.Pairwise (Finset.univ : Finset P)
      (fun p r : P ↦ p.val.Coprime r.val) := by
    intro p hp r hr hpr
    apply (Nat.coprime_primes (hP p p.property) (hP r r.property)).mpr
    exact fun he ↦ hpr (Subtype.ext he)
  let crt := Nat.chineseRemainderOfFinset (fun p : P ↦ (z p).val) (fun p : P ↦ p.val)
    Finset.univ (fun p hp ↦ (hP p p.property).ne_zero) hpair
  let r : ℕ := crt.val
  have hr (p : P) : (r : ZMod p.val) = z p := by
    let : NeZero p.val := ⟨(hP p p.property).ne_zero⟩
    calc
      _ = ((z p).val : ZMod p.val) :=
        (ZMod.natCast_eq_natCast_iff r (z p).val p.val).mpr (crt.property p (Finset.mem_univ p))
      _ = _ := ZMod.natCast_zmod_val _
  have hrcop : r.Coprime (∏ p ∈ P, p) := by
    apply Nat.coprime_prod_right_iff.mpr
    intro p hp
    apply Nat.Coprime.symm
    apply ((hP p hp).coprime_iff_not_dvd).mpr
    intro hpr
    exact hz0 ⟨p, hp⟩ ((hr ⟨p, hp⟩).symm.trans ((ZMod.natCast_eq_zero_iff r p).mpr hpr))
  have hrD (p : P) (i : PinnedShiftIndex h)
      (hi : p.val ∣ Nat.lcm (d (.inl i) false) (d (.inl i) true)) :
      (p₀ : ZMod p.val) + pinnedIndexSlope h w p.val i * (r : ZMod p.val) = 0 := by
    rw [hr p]
    exact hzD p i hi
  have hrE (p : P) (i : PinnedShiftIndex h)
      (hi : p.val ∣ Nat.lcm (d (.inr i) false) (d (.inr i) true)) :
      (m : ZMod p.val) * ((p₀ : ZMod p.val) +
        pinnedIndexSlope h w p.val i * (r : ZMod p.val)) = 1 := by
    rw [hr p]
    exact hzE p i hi
  refine ⟨r, hrcop.coprime_dvd_right (pinnedFlatDivisorModulus_dvd_cutoff h P d hdiv), ?_⟩
  intro q
  constructor
  · intro hq
    apply modEq_finset_lcm
    rintro ⟨i, b⟩ hib
    apply (modEq_divisor_primeFinsetProduct_iff P hP (hdiv i b) q r).mpr
    intro p hp hpd
    have hp' := hP p hp
    have hwp := hrough p hp
    have hpL : p ∣ Nat.lcm (d i false) (d i true) := by
      cases b
      · exact hpd.trans (Nat.dvd_lcm_left _ _)
      · exact hpd.trans (Nat.dvd_lcm_right _ _)
    apply (ZMod.natCast_eq_natCast_iff q r p).mp
    cases i with
    | inl i =>
      exact ((pinnedFirstRoot_iff_affine_zero h hp' hKw hwp i _).mpr ((hq ⟨p, hp⟩).1 i hpL)).trans
        ((pinnedFirstRoot_iff_affine_zero h hp' hKw hwp i _).mpr (hrD ⟨p, hp⟩ i hpL)).symm
    | inr i =>
      let : Fact p.Prime := ⟨hp'⟩
      have hpm : ¬p ∣ m := by
        intro hpm
        have hm0 := (ZMod.natCast_eq_zero_iff m p).mpr hpm
        have he := hrE ⟨p, hp⟩ i hpL
        rw [hm0, zero_mul] at he
        exact zero_ne_one he
      exact ((pinnedCompanionRoot_iff_affine_one h hp' hKw hwp hpm i _).mpr
        ((hq ⟨p, hp⟩).2 i hpL)).trans
          ((pinnedCompanionRoot_iff_affine_one h hp' hKw hwp hpm i _).mpr
            (hrE ⟨p, hp⟩ i hpL)).symm
  · intro hq p
    have hcast (i : PinnedShiftIndex h ⊕ PinnedShiftIndex h)
        (hi : p.val ∣ Nat.lcm (d i false) (d i true)) : (q : ZMod p.val) = (r : ZMod p.val) := by
      apply (ZMod.natCast_eq_natCast_iff q r p.val).mpr
      apply hq.of_dvd
      exact hi.trans (Nat.lcm_dvd (dvd_pinnedFlatDivisorModulus h d i false)
        (dvd_pinnedFlatDivisorModulus h d i true))
    constructor
    · intro i hi
      rw [hcast (.inl i) hi]
      exact hrD p i hi
    · intro i hi
      rw [hcast (.inr i) hi]
      exact hrE p i hi

theorem exists_pinnedPrimeCrt_bounded_reduced_class
    {K w m p₀ : ℕ} (h : Fin K) (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (hrough : ∀ p ∈ P, w < p) (hKw : K ≤ w)
    (d : (PinnedShiftIndex h ⊕ PinnedShiftIndex h) → Bool → ℕ)
    (hdiv : ∀ i b, d i b ∣ ∏ p ∈ P, p)
    (hsol : ∀ p : P, PinnedLocalDivisorSolvable h w m p₀ p.val
      (fun i ↦ Nat.lcm (d (.inl i) false) (d (.inl i) true))
      (fun i ↦ Nat.lcm (d (.inr i) false) (d (.inr i) true))) :
    ∃ r : ℕ, r < pinnedFlatDivisorModulus h d ∧ r.Coprime (pinnedFlatDivisorModulus h d) ∧
      ∀ q : ℕ, PinnedDivisorPrimeEquations h P w m p₀ q d ↔
        q ≡ r [MOD pinnedFlatDivisorModulus h d] := by
  obtain ⟨r, hrcop, hr⟩ := exists_pinnedPrimeCrt_reduced_class h P hP hrough hKw d hdiv hsol
  have hQpos := (pinnedFlatDivisorModulus_squarefree h P hP d hdiv).ne_zero.bot_lt
  have hmod := Nat.mod_modEq r (pinnedFlatDivisorModulus h d)
  refine ⟨r % pinnedFlatDivisorModulus h d, Nat.mod_lt _ hQpos,
    (coprime_modulus_iff_of_modEq hmod).mpr hrcop, ?_⟩
  intro q
  rw [hr q]
  exact ⟨fun he ↦ he.trans hmod.symm, fun he ↦ he.trans hmod⟩

end

end Erdos4b
