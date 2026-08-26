import ErdosProblems.Erdos1148.CoefficientLattices

/-!
# From local pair orbits to lattices containing a fixed pair

The explicit transporter sends the fixed pair to an integral pair; pulling
back the standard lattice gives a lattice containing the fixed pair. Equal
lattices imply integrally equivalent pairs by the lattice-stabilizer theorem.
-/

namespace Erdos1148.DukeArithmetic

lemma exists_specialPair_transporter {K : Type*} [Field K] [CharZero K]
    {d ℓ : K} (p q : FormPair K d ℓ) (hnd : ℓ ^ 2 ≠ 4 * d ^ 2) :
    ∃ g : specialDiscrGroup K, g • p = q := by
  obtain ⟨f, hdet, hfirst, hsecond⟩ := exists_specialIsometry_of_nondegenerate_pair p q hnd
  refine ⟨⟨f.toLinearEquiv, ⟨fun t => f.map_app t, hdet⟩⟩, ?_⟩
  apply Subtype.ext
  exact Prod.ext hfirst hsecond

noncomputable def pairTransporter {R K : Type*} [CommRing R] [Field K] [CharZero K]
    (φ : R →+* K) (hφ : Function.Injective φ) {d ℓ : R}
    (base p : FormPair R d ℓ) (hnd : ℓ ^ 2 ≠ 4 * d ^ 2) : specialDiscrGroup K :=
  Classical.choose (exists_specialPair_transporter (mapFormPair φ base) (mapFormPair φ p)
    (map_nondegenerate φ hφ hnd))

lemma pairTransporter_spec {R K : Type*} [CommRing R] [Field K] [CharZero K]
    (φ : R →+* K) (hφ : Function.Injective φ) {d ℓ : R}
    (base p : FormPair R d ℓ) (hnd : ℓ ^ 2 ≠ 4 * d ^ 2) :
    pairTransporter φ hφ base p hnd • mapFormPair φ base = mapFormPair φ p :=
  Classical.choose_spec (exists_specialPair_transporter (mapFormPair φ base) (mapFormPair φ p)
    (map_nondegenerate φ hφ hnd))

def containingPairLattices {R K : Type*} [CommRing R] [CommRing K]
    (φ : R →+* K) {d ℓ : R} (base : FormPair R d ℓ) : Set (Set (K × K × K)) :=
  {L | (∃ g : specialDiscrGroup K, coefficientLattice φ g = L) ∧
    mapCoeffs φ base.1.1 ∈ L ∧ mapCoeffs φ base.1.2 ∈ L}

lemma transporter_lattice_mem {R K : Type*} [CommRing R] [CommRing K]
    (φ : R →+* K) {d ℓ : R} (base p : FormPair R d ℓ) (g : specialDiscrGroup K)
    (hg : g • mapFormPair φ base = mapFormPair φ p) :
    coefficientLattice φ g ∈ containingPairLattices φ base := by
  refine ⟨⟨g, rfl⟩, ?_, ?_⟩
  · exact ⟨p.1.1, (congrArg (fun q : FormPair K (φ d) (φ ℓ) => q.1.1) hg).symm⟩
  · exact ⟨p.1.2, (congrArg (fun q : FormPair K (φ d) (φ ℓ) => q.1.2) hg).symm⟩

noncomputable def pairOrbitToLattice {R K : Type*} [CommRing R] [Field K] [CharZero K]
    (φ : R →+* K) (hφ : Function.Injective φ) {d ℓ : R} (base : FormPair R d ℓ)
    (hnd : ℓ ^ 2 ≠ 4 * d ^ 2) (x : SpecialPairOrbits R d ℓ) : containingPairLattices φ base :=
  ⟨coefficientLattice φ (pairTransporter φ hφ base x.out hnd),
    transporter_lattice_mem φ base x.out _ (pairTransporter_spec φ hφ base x.out hnd)⟩

theorem pairOrbitToLattice_injective {R K : Type*} [CommRing R] [Field K] [CharZero K]
    (φ : R →+* K) (hφ : Function.Injective φ) {d ℓ : R} (base : FormPair R d ℓ)
    (hnd : ℓ ^ 2 ≠ 4 * d ^ 2) : Function.Injective (pairOrbitToLattice φ hφ base hnd) := by
  intro x y hxy
  have heq := pairOrbit_eq_of_transporter_lattice_eq φ hφ base x.out y.out
    (pairTransporter φ hφ base x.out hnd) (pairTransporter φ hφ base y.out hnd)
    (pairTransporter_spec φ hφ base x.out hnd)
    (pairTransporter_spec φ hφ base y.out hnd) (congrArg Subtype.val hxy)
  exact (Quotient.out_eq x).symm.trans (heq.trans (Quotient.out_eq y))

lemma exists_integral_pair_of_lattice_mem {R K : Type*} [CommRing R] [CommRing K]
    (φ : R →+* K) (hφ : Function.Injective φ) {d ℓ : R}
    (base : FormPair R d ℓ) (g : specialDiscrGroup K)
    (ht : mapCoeffs φ base.1.1 ∈ coefficientLattice φ g)
    (hu : mapCoeffs φ base.1.2 ∈ coefficientLattice φ g) :
    ∃ p : FormPair R d ℓ, g • mapFormPair φ base = mapFormPair φ p := by
  obtain ⟨t, ht⟩ := ht
  obtain ⟨u, hu⟩ := hu
  have hdt : discr t = d := by
    apply hφ
    rw [← discr_mapCoeffs, ht, g.2.1, discr_mapCoeffs, base.2.1]
  have hdu : discr u = d := by
    apply hφ
    rw [← discr_mapCoeffs, hu, g.2.1, discr_mapCoeffs, base.2.2.1]
  have hpair : pairing t u = ℓ := by
    apply hφ
    rw [← pairing_mapCoeffs, ht, hu, pairing_linearEquiv g.1 g.2.1,
      pairing_mapCoeffs, base.2.2.2]
  refine ⟨⟨(t, u), ⟨hdt, hdu, hpair⟩⟩, ?_⟩
  apply Subtype.ext
  exact Prod.ext ht.symm hu.symm

theorem pairOrbitToLattice_surjective {R K : Type*} [CommRing R] [Field K] [CharZero K]
    (φ : R →+* K) (hφ : Function.Injective φ) {d ℓ : R} (base : FormPair R d ℓ)
    (hnd : ℓ ^ 2 ≠ 4 * d ^ 2) : Function.Surjective (pairOrbitToLattice φ hφ base hnd) := by
  rintro ⟨L, ⟨g, rfl⟩, ht, hu⟩
  obtain ⟨p, hp⟩ := exists_integral_pair_of_lattice_mem φ hφ base g ht hu
  let x : SpecialPairOrbits R d ℓ := Quotient.mk _ p
  let h := pairTransporter φ hφ base x.out hnd
  have hh : h • mapFormPair φ base = mapFormPair φ x.out :=
    pairTransporter_spec φ hφ base x.out hnd
  have hrel : MulAction.orbitRel (specialDiscrGroup R) (FormPair R d ℓ) p x.out :=
    Quotient.exact (Quotient.out_eq x).symm
  obtain ⟨k, hk⟩ := MulAction.mem_orbit_iff.mp (MulAction.orbitRel_apply.mp hrel)
  have hg : specialDiscrBaseChange φ k * h = g := by
    apply specialPairAction_left_injective (mapFormPair φ base) (map_nondegenerate φ hφ hnd)
    dsimp only
    rw [mul_smul, hh, ← mapFormPair_smul, hk, hp]
  refine ⟨x, ?_⟩
  apply Subtype.ext
  change coefficientLattice φ h = coefficientLattice φ g
  rw [← hg, coefficientLattice_baseChange_mul]

noncomputable def pairOrbitEquivLattice {R K : Type*} [CommRing R] [Field K] [CharZero K]
    (φ : R →+* K) (hφ : Function.Injective φ) {d ℓ : R} (base : FormPair R d ℓ)
    (hnd : ℓ ^ 2 ≠ 4 * d ^ 2) : SpecialPairOrbits R d ℓ ≃ containingPairLattices φ base :=
  Equiv.ofBijective (pairOrbitToLattice φ hφ base hnd)
    ⟨pairOrbitToLattice_injective φ hφ base hnd, pairOrbitToLattice_surjective φ hφ base hnd⟩

theorem card_pairOrbits_eq_containing_lattices {R K : Type*}
    [CommRing R] [Field K] [CharZero K]
    (φ : R →+* K) (hφ : Function.Injective φ) {d ℓ : R} (base : FormPair R d ℓ)
    (hnd : ℓ ^ 2 ≠ 4 * d ^ 2) :
    Nat.card (SpecialPairOrbits R d ℓ) = Nat.card (containingPairLattices φ base) :=
  Nat.card_congr (pairOrbitEquivLattice φ hφ base hnd)

/-- Counting containing lattices bounds the local embedding count. -/
theorem card_pairOrbits_le_containing_lattices {R K : Type*}
    [CommRing R] [Field K] [CharZero K]
    (φ : R →+* K) (hφ : Function.Injective φ) {d ℓ : R} (base : FormPair R d ℓ)
    (hnd : ℓ ^ 2 ≠ 4 * d ^ 2) [Finite (containingPairLattices φ base)] :
    Nat.card (SpecialPairOrbits R d ℓ) ≤ Nat.card (containingPairLattices φ base) :=
  Nat.card_le_card_of_injective _ (pairOrbitToLattice_injective φ hφ base hnd)

end Erdos1148.DukeArithmetic
