/- Adapted from the checked repository proof in Erdos1148/LocalCountInvariance.lean. -/
import ErdosProblems.Erdos941.PairLocal.LocalCountBound
import ErdosProblems.Erdos941.PairLocal.PadicFormNormalization

/-!
# Removing the coordinate normalization from the local count

Integral isometries transport containing lattices injectively. Normalizing
the first vector therefore gives a bound for arbitrary integral pairs with
nonzero first discriminant and nonzero resultant, at every prime.
-/

namespace Erdos941.PairLocal

lemma pairResultant_specialIsometry {R : Type*} [CommRing R] [NoZeroDivisors R] [CharZero R]
    (g : specialDiscrGroup R) (t u : R × R × R) :
    pairResultant (g.1 t) (g.1 u) = pairResultant t u := by
  apply mul_left_cancel₀ (by norm_num : (16 : R) ≠ 0)
  rw [pairResultant_discr, pairResultant_discr, g.2.1, g.2.1,
    pairing_linearEquiv g.1 g.2.1]

noncomputable def transformContainingLattice (p : ℕ) [Fact p.Prime]
    (t u : PadicInt p × PadicInt p × PadicInt p) (k : specialDiscrGroup (PadicInt p))
    (L : padicContainingLattices p t u) : padicContainingLattices p (k.1 t) (k.1 u) := by
  let φ := algebraMap (PadicInt p) (Padic p)
  let gK := specialDiscrBaseChange φ k
  refine ⟨gK.1.symm ⁻¹' L.1, ?_, ?_, ?_⟩
  · obtain ⟨g, hg⟩ := L.2.1
    refine ⟨g * gK⁻¹, ?_⟩
    rw [← hg]
    rfl
  · change gK.1.symm (mapCoeffs φ (k.1 t)) ∈ L.1
    rw [← specialDiscrBaseChange_apply φ k t, LinearEquiv.symm_apply_apply]
    exact L.2.2.1
  · change gK.1.symm (mapCoeffs φ (k.1 u)) ∈ L.1
    rw [← specialDiscrBaseChange_apply φ k u, LinearEquiv.symm_apply_apply]
    exact L.2.2.2

lemma transformContainingLattice_injective (p : ℕ) [Fact p.Prime]
    (t u : PadicInt p × PadicInt p × PadicInt p) (k : specialDiscrGroup (PadicInt p)) :
    Function.Injective (transformContainingLattice p t u k) := by
  intro L M hLM
  apply Subtype.ext
  have h := congrArg (fun L : padicContainingLattices p (k.1 t) (k.1 u) => L.1) hLM
  have hsurj := (specialDiscrBaseChange (algebraMap (PadicInt p) (Padic p)) k).1.symm.surjective
  exact hsurj.preimage_injective h

lemma card_padicContainingLattices_le_transformed (p : ℕ) [Fact p.Prime]
    (t u : PadicInt p × PadicInt p × PadicInt p) (hres : pairResultant t u ≠ 0)
    (k : specialDiscrGroup (PadicInt p)) :
    Nat.card (padicContainingLattices p t u) ≤
      Nat.card (padicContainingLattices p (k.1 t) (k.1 u)) := by
  have hres' : pairResultant (k.1 t) (k.1 u) ≠ 0 := by rwa [pairResultant_specialIsometry]
  let := finite_padicContainingLattices p (k.1 t) (k.1 u) hres'
  exact Nat.card_le_card_of_injective _ (transformContainingLattice_injective p t u k)

/-- A direct local count, including at two, with the half-discriminant-valuation exponent. -/
theorem card_padicContainingLattices_le (p : ℕ) [Fact p.Prime]
    (t u : PadicInt p × PadicInt p × PadicInt p)
    (hD : discr t ≠ 0) (hres : pairResultant t u ≠ 0) :
    Nat.card (padicContainingLattices p t u) ≤
      16 * ((pairResultant t u).valuation + 1) * p ^ ((discr t).valuation / 2) := by
  have ht : t ≠ 0 := by
    intro ht
    exact hD (by simp [ht, discr])
  obtain ⟨k, r, s, hnorm, hs⟩ := exists_normalized_first_vector p t ht
  have hds : discr s ≠ 0 := by
    intro hzero
    have h := k.2.1 t
    rw [hnorm, discr_smul, hzero, mul_zero] at h
    exact hD h.symm
  have hres' : pairResultant ((p : PadicInt p) ^ r • s) (k.1 u) ≠ 0 := by
    rw [← hnorm, pairResultant_specialIsometry]
    exact hres
  have hcount := card_padicContainingLattices_le_of_scaled_unit p r s (k.1 u) hs hds hres'
  rw [← hnorm, pairResultant_specialIsometry, k.2.1] at hcount
  exact (card_padicContainingLattices_le_transformed p t u hres k).trans hcount

end Erdos941.PairLocal
