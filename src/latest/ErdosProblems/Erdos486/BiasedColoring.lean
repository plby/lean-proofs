import ErdosProblems.Erdos486.BiasedSkeleton

/- Ported to Lean/Mathlib 4.33.0; see README.md for source and modifications. -/
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Finite colourings for the biased Erdős 486 block

The colour set has four elements; colour zero is called black.  Thus uniform
enumeration of all colourings gives black probability exactly `1/4`, without
introducing any measure-theoretic probability space.
-/

open scoped BigOperators

namespace Erdos486

instance biasedPrimeNeZero (k : ℕ) (i : Fin k) :
    NeZero (skeletonPrime k i) :=
  ⟨(skeletonPrime_spec k i).1.ne_zero⟩

/-- A coordinate consists of a prime index and a residue modulo that prime. -/
def BiasedCoordinate (j : ℕ) :=
  Σ i : Fin (biasedK j), ZMod (skeletonPrime (biasedK j) i)

noncomputable instance instDecidableEqBiasedCoordinate (j : ℕ) :
    DecidableEq (BiasedCoordinate j) :=
  Classical.decEq _

/-- The complete coordinate space at a fixed scale is finite.  Registering
this instance once keeps all later finite-colouring averages on the same
canonical enumeration. -/
noncomputable instance instFintypeBiasedCoordinate (j : ℕ) :
    Fintype (BiasedCoordinate j) := by
  classical
  unfold BiasedCoordinate
  infer_instance

/-- A four-colouring of all prime-residue coordinates at scale `j`. -/
abbrev BiasedColoring (j : ℕ) := BiasedCoordinate j → Fin 4

/-- The coordinate queried by endpoint `m` at prime index `i`. -/
noncomputable def endpointCoordinate (j m : ℕ) (i : Fin (biasedK j)) :
    BiasedCoordinate j :=
  ⟨i, (m : ZMod (skeletonPrime (biasedK j) i))⟩

/-- Indices whose queried coordinate is black. -/
noncomputable def selectedPrimes (j : ℕ) (c : BiasedColoring j) (m : ℕ) :
    Finset (Fin (biasedK j)) :=
  Finset.univ.filter fun i ↦ c (endpointCoordinate j m i) = 0

@[simp]
theorem mem_selectedPrimes_iff (j : ℕ) (c : BiasedColoring j)
    (m : ℕ) (i : Fin (biasedK j)) :
    i ∈ selectedPrimes j c m ↔ c (endpointCoordinate j m i) = 0 := by
  simp [selectedPrimes]

/-- The endpoint modulus selected by a colouring. -/
noncomputable def colouredModulus (j : ℕ) (c : BiasedColoring j) (m : ℕ) : ℕ :=
  biasedModulus j (selectedPrimes j c m)

theorem colouredModulus_pos (j : ℕ) (c : BiasedColoring j) (m : ℕ) :
    0 < colouredModulus j c m :=
  biasedModulus_pos _ _

theorem colouredModulus_bounds {j : ℕ} (hj : 400 ≤ j)
    (c : BiasedColoring j) (m : ℕ) :
    19 * 2 ^ j ≤ 20 * colouredModulus j c m ∧
      20 * colouredModulus j c m ≤ 21 * 2 ^ j :=
  biasedModulus_bounds hj _

/-- An endpoint lies strictly after its selected modulus. -/
theorem colouredModulus_lt_endpoint {j m : ℕ} (hj : 400 ≤ j)
    (c : BiasedColoring j) (hm : m ∈ biasedEndpoints j) :
    colouredModulus j c m < m := by
  have hq := (colouredModulus_bounds hj c m).2
  have hm' := (biasedEndpoint_bounds hj hm).1
  have hQ : 0 < 2 ^ j := by positivity
  omega

/-- An endpoint lies strictly before twice its selected modulus. -/
theorem endpoint_lt_two_colouredModulus {j m : ℕ} (hj : 400 ≤ j)
    (c : BiasedColoring j) (hm : m ∈ biasedEndpoints j) :
    m < 2 * colouredModulus j c m := by
  have hq := (colouredModulus_bounds hj c m).1
  have hQ := twoPow_eq_eight_mul_blockUnit (show 3 ≤ j by omega)
  have hunit : 0 < blockUnit j := by simp [blockUnit]
  rw [mem_biasedEndpoints_iff] at hm
  rw [hQ] at hq
  omega

/-- The endpoint interval has diameter smaller than every subset modulus. -/
theorem biasedEndpoint_dist_lt_modulus {j m n : ℕ} (hj : 400 ≤ j)
    (S : Finset (Fin (biasedK j)))
    (hm : m ∈ biasedEndpoints j) (hn : n ∈ biasedEndpoints j) :
    Nat.dist m n < biasedModulus j S := by
  have hq := (biasedModulus_bounds hj S).1
  have hQ := twoPow_eq_eight_mul_blockUnit (show 3 ≤ j by omega)
  have hunit : 0 < blockUnit j := by simp [blockUnit]
  rw [hQ] at hq
  rw [mem_biasedEndpoints_iff] at hm hn
  rcases le_total m n with hmn | hnm
  · rw [Nat.dist_eq_sub_of_le hmn]
    have hdiff : n - m ≤ 6 * blockUnit j := by omega
    have hq' : 6 * blockUnit j < biasedModulus j S := by omega
    exact hdiff.trans_lt hq'
  · rw [Nat.dist_eq_sub_of_le_right hnm]
    have hdiff : m - n ≤ 6 * blockUnit j := by omega
    have hq' : 6 * blockUnit j < biasedModulus j S := by omega
    exact hdiff.trans_lt hq'

/-- Consequently a residue class modulo a subset modulus contains at most
one endpoint in the block interval. -/
theorem biasedEndpoint_eq_of_cast_eq {j m n : ℕ} (hj : 400 ≤ j)
    (S : Finset (Fin (biasedK j)))
    (hm : m ∈ biasedEndpoints j) (hn : n ∈ biasedEndpoints j)
    (hcast : (m : ZMod (biasedModulus j S)) =
      (n : ZMod (biasedModulus j S))) :
    m = n := by
  have hmod : m ≡ n [MOD biasedModulus j S] :=
    (ZMod.natCast_eq_natCast_iff m n (biasedModulus j S)).mp hcast
  have hdist := biasedEndpoint_dist_lt_modulus hj S hm hn
  rcases le_total m n with hmn | hnm
  · have hdvd : biasedModulus j S ∣ n - m :=
      (Nat.modEq_iff_dvd' hmn).mp hmod
    have hlt : n - m < biasedModulus j S := by
      simpa [Nat.dist_eq_sub_of_le hmn] using hdist
    have hz : n - m = 0 := Nat.eq_zero_of_dvd_of_lt hdvd hlt
    omega
  · have hdvd : biasedModulus j S ∣ m - n :=
      (Nat.modEq_iff_dvd' hnm).mp hmod.symm
    have hlt : m - n < biasedModulus j S := by
      simpa [Nat.dist_eq_sub_of_le_right hnm] using hdist
    have hz : m - n = 0 := Nat.eq_zero_of_dvd_of_lt hdvd hlt
    omega

/-- Endpoints representing a prescribed residue modulo `q_S`. -/
noncomputable def candidateEndpoints (j : ℕ)
    (S : Finset (Fin (biasedK j))) (z : ZMod (biasedModulus j S)) :
    Finset ℕ :=
  (biasedEndpoints j).filter fun m ↦
    (m : ZMod (biasedModulus j S)) = z

theorem candidateEndpoints_card_le_one {j : ℕ} (hj : 400 ≤ j)
    (S : Finset (Fin (biasedK j))) (z : ZMod (biasedModulus j S)) :
    (candidateEndpoints j S z).card ≤ 1 := by
  classical
  rw [Finset.card_le_one_iff]
  intro m n hm hn
  rw [candidateEndpoints, Finset.mem_filter] at hm hn
  exact biasedEndpoint_eq_of_cast_eq hj S hm.1 hn.1 (hm.2.trans hn.2.symm)

/-- A common finite period for all subset moduli at one scale. -/
noncomputable def biasedPeriod (j : ℕ) : ℕ :=
  ∏ S : Finset (Fin (biasedK j)), biasedModulus j S

theorem biasedPeriod_pos (j : ℕ) : 0 < biasedPeriod j := by
  unfold biasedPeriod
  exact Finset.prod_pos fun S _ ↦ biasedModulus_pos j S

theorem biasedModulus_dvd_period (j : ℕ)
    (S : Finset (Fin (biasedK j))) :
    biasedModulus j S ∣ biasedPeriod j := by
  unfold biasedPeriod
  exact Finset.dvd_prod_of_mem (biasedModulus j) (Finset.mem_univ S)

/-- Reduction from the common period to a subset modulus. -/
noncomputable def reduceBiasedPeriod (j : ℕ)
    (S : Finset (Fin (biasedK j))) :
    ZMod (biasedPeriod j) →+* ZMod (biasedModulus j S) :=
  ZMod.castHom (biasedModulus_dvd_period j S) _

/-- The periodic footprint covered by the endpoint cylinders of a colouring. -/
def IsBiasedCovered (j : ℕ) (c : BiasedColoring j)
    (x : ZMod (biasedPeriod j)) : Prop :=
  ∃ m ∈ biasedEndpoints j,
    reduceBiasedPeriod j (selectedPrimes j c m) x =
      (m : ZMod (colouredModulus j c m))

/-- Number of covered residues in one common period. -/
noncomputable def biasedFootprintCount (j : ℕ) (c : BiasedColoring j) : ℕ := by
  letI : NeZero (biasedPeriod j) := ⟨(biasedPeriod_pos j).ne'⟩
  classical
  exact (Finset.univ.filter (IsBiasedCovered j c)).card

/-- Normalized periodic footprint, represented as an exact finite ratio. -/
noncomputable def biasedFootprint (j : ℕ) (c : BiasedColoring j) : ℝ :=
  biasedFootprintCount j c / biasedPeriod j

/-- Rational version of the same exact finite ratio.  Finite enumeration is
most convenient over `ℚ`; it is cast to the real-valued block interface only
after the deterministic colouring has been selected. -/
noncomputable def biasedFootprintRat (j : ℕ) (c : BiasedColoring j) : ℚ :=
  biasedFootprintCount j c / biasedPeriod j

theorem biasedFootprintRat_cast_real (j : ℕ) (c : BiasedColoring j) :
    ((biasedFootprintRat j c : ℚ) : ℝ) = biasedFootprint j c := by
  simp [biasedFootprintRat, biasedFootprint]

theorem biasedFootprintCount_le_period (j : ℕ) (c : BiasedColoring j) :
    biasedFootprintCount j c ≤ biasedPeriod j := by
  letI : NeZero (biasedPeriod j) := ⟨(biasedPeriod_pos j).ne'⟩
  classical
  unfold biasedFootprintCount
  simpa using (Finset.card_filter_le
    (s := (Finset.univ : Finset (ZMod (biasedPeriod j))))
    (p := IsBiasedCovered j c))

theorem biasedFootprint_nonneg (j : ℕ) (c : BiasedColoring j) :
    0 ≤ biasedFootprint j c := by
  unfold biasedFootprint
  positivity

theorem biasedFootprint_le_one (j : ℕ) (c : BiasedColoring j) :
    biasedFootprint j c ≤ 1 := by
  rw [biasedFootprint, div_le_one (by exact_mod_cast biasedPeriod_pos j)]
  exact_mod_cast biasedFootprintCount_le_period j c

end Erdos486
