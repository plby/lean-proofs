import ErdosProblems.Erdos1148.LocalCountInvariance

/-!
# Optimizing the local bound within a pair

If the mixed coefficient has smaller valuation than the common discriminant,
replace the first vector by the sum of the two. The resulting exponent is
half the common-content valuation of the binary source form.
-/

namespace Erdos1148.DukeArithmetic

lemma mapCoeffs_add {R S : Type*} [CommRing R] [CommRing S]
    (φ : R →+* S) (t u : R × R × R) :
    mapCoeffs φ (t + u) = mapCoeffs φ t + mapCoeffs φ u := by ext <;> simp [mapCoeffs]

lemma mapCoeffs_sub {R S : Type*} [CommRing R] [CommRing S]
    (φ : R →+* S) (t u : R × R × R) :
    mapCoeffs φ (t - u) = mapCoeffs φ t - mapCoeffs φ u := by ext <;> simp [mapCoeffs]

lemma coefficientLattice_add_mem {R S : Type*} [CommRing R] [CommRing S]
    (φ : R →+* S) (g : specialDiscrGroup S) {t u : S × S × S}
    (ht : t ∈ coefficientLattice φ g) (hu : u ∈ coefficientLattice φ g) :
    t + u ∈ coefficientLattice φ g := by
  obtain ⟨a, ha⟩ := ht
  obtain ⟨b, hb⟩ := hu
  refine ⟨a + b, ?_⟩
  rw [mapCoeffs_add, ha, hb, map_add]

lemma coefficientLattice_sub_mem {R S : Type*} [CommRing R] [CommRing S]
    (φ : R →+* S) (g : specialDiscrGroup S) {t u : S × S × S}
    (ht : t ∈ coefficientLattice φ g) (hu : u ∈ coefficientLattice φ g) :
    t - u ∈ coefficientLattice φ g := by
  obtain ⟨a, ha⟩ := ht
  obtain ⟨b, hb⟩ := hu
  refine ⟨a - b, ?_⟩
  rw [mapCoeffs_sub, ha, hb, map_sub]

lemma padicContainingLattices_add_first (p : ℕ) [Fact p.Prime]
    (t u : PadicInt p × PadicInt p × PadicInt p) :
    padicContainingLattices p (t + u) u = padicContainingLattices p t u := by
  let φ := algebraMap (PadicInt p) (Padic p)
  ext L
  constructor
  · rintro ⟨⟨g, rfl⟩, ht, hu⟩
    refine ⟨⟨g, rfl⟩, ?_, hu⟩
    have h := coefficientLattice_sub_mem φ g ht hu
    simpa only [← mapCoeffs_sub, add_sub_cancel_right] using h
  · rintro ⟨⟨g, rfl⟩, ht, hu⟩
    refine ⟨⟨g, rfl⟩, ?_, hu⟩
    rw [mapCoeffs_add]
    exact coefficientLattice_add_mem φ g ht hu

lemma pairResultant_add_first {R : Type*} [CommRing R] (t u : R × R × R) :
    pairResultant (t + u) u = pairResultant t u := by dsimp [pairResultant]; ring

lemma discr_add {R : Type*} [CommRing R] (t u : R × R × R) :
    discr (t + u) = discr t + discr u + pairing t u := by dsimp [discr, pairing]; ring

open Classical in
noncomputable def pairContentValuation (p : ℕ) [Fact p.Prime] (d ℓ : PadicInt p) : ℕ :=
  if ℓ = 0 then d.valuation else min d.valuation ℓ.valuation

theorem card_padicPairLattices_le_content (p : ℕ) [Fact p.Prime]
    {d ℓ : PadicInt p} (base : FormPair (PadicInt p) d ℓ)
    (hd : d ≠ 0) (hnd : ℓ ^ 2 ≠ 4 * d ^ 2) :
    Nat.card (padicContainingLattices p base.1.1 base.1.2) ≤
      16 * ((pairResultant base.1.1 base.1.2).valuation + 1) *
        p ^ (pairContentValuation p d ℓ / 2) := by
  classical
  have hres := pairResultant_ne_zero base hnd
  have hdt : discr base.1.1 ≠ 0 := by rwa [base.2.1]
  by_cases hℓ : ℓ = 0
  · have h := card_padicContainingLattices_le p base.1.1 base.1.2 hdt hres
    simpa only [base.2.1, pairContentValuation, hℓ, ↓reduceIte] using h
  by_cases hval : ℓ.valuation < d.valuation
  · have hsum : discr (base.1.1 + base.1.2) = 2 * d + ℓ := by
      rw [discr_add, base.2.1, base.2.2.1, base.2.2.2]
      ring
    have hcongr : (p : PadicInt p) ^ d.valuation ∣ (2 * d + ℓ) - ℓ := by
      simpa only [add_sub_cancel_right] using dvd_mul_of_dvd_right (padic_pow_valuation_dvd p d) 2
    have hshift := valuation_eq_of_deep_congruence p (2 * d + ℓ) ℓ hℓ d.valuation hval hcongr
    have hDsum : discr (base.1.1 + base.1.2) ≠ 0 := by rw [hsum]; exact hshift.1
    have hressum : pairResultant (base.1.1 + base.1.2) base.1.2 ≠ 0 := by
      rwa [pairResultant_add_first]
    have h := card_padicContainingLattices_le p (base.1.1 + base.1.2) base.1.2 hDsum hressum
    rw [padicContainingLattices_add_first, pairResultant_add_first, hsum, hshift.2] at h
    simpa only [pairContentValuation, hℓ, ↓reduceIte, min_eq_right hval.le] using h
  · have h := card_padicContainingLattices_le p base.1.1 base.1.2 hdt hres
    simpa only [base.2.1, pairContentValuation, hℓ, ↓reduceIte, min_eq_left (by omega :
      d.valuation ≤ ℓ.valuation)] using h

theorem card_padicPairOrbits_le_content (p : ℕ) [Fact p.Prime]
    {d ℓ : PadicInt p} (base : FormPair (PadicInt p) d ℓ)
    (hd : d ≠ 0) (hnd : ℓ ^ 2 ≠ 4 * d ^ 2) :
    Nat.card (SpecialPairOrbits (PadicInt p) d ℓ) ≤
      16 * ((pairResultant base.1.1 base.1.2).valuation + 1) *
        p ^ (pairContentValuation p d ℓ / 2) := by
  have hcard := card_pairOrbits_eq_containing_lattices
    (algebraMap (PadicInt p) (Padic p))
    (FaithfulSMul.algebraMap_injective (PadicInt p) (Padic p)) base hnd
  change Nat.card (SpecialPairOrbits (PadicInt p) d ℓ) =
    Nat.card (padicContainingLattices p base.1.1 base.1.2) at hcard
  rw [hcard]
  exact card_padicPairLattices_le_content p base hd hnd

end Erdos1148.DukeArithmetic
