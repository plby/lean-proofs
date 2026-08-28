import Wikipedia.HopfProblem.OrbitPairFiniteCharacters
import Wikipedia.HopfProblem.OrbitPairComplexPhase

/-!
# Aligning nearby circle fibres by finite equivariant coordinates

Normalize the Hermitian pairing and act on the second representative.
The result does not change when the second representative is changed
by the original circle action. On the diagonal it is exactly the first
point. These are the algebraic identities for quotient fibre transport.
-/

noncomputable section

open Set Topology
open scoped ComplexConjugate

namespace Wikipedia.HopfProblem.OrbitPair

open SpecialPeriods SpecialPeriods.Threefold

attribute [local instance] Threefold.chartedSpace unitCircleMulAction unitCircleAction_continuous

theorem characterPairing_smul_right (s : Finset SmoothOrbitCharacter) (v : Circle)
    (x y : Threefold.Space) :
    characterPairing s x (v • y) = ((v⁻¹ : Circle) : ℂ) * characterPairing s x y := by
  simpa only [one_smul, Circle.coe_one, one_mul, Circle.coe_inv_eq_conj] using
    characterPairing_equivariant s 1 v x y

theorem characterPairing_smul_left (s : Finset SmoothOrbitCharacter) (u : Circle)
    (x y : Threefold.Space) :
    characterPairing s (u • x) y = (u : ℂ) * characterPairing s x y := by
  simpa only [one_smul, Circle.coe_one, map_one, mul_one] using
    characterPairing_equivariant s u 1 x y

def characterMatchingDomain (s : Finset SmoothOrbitCharacter) :
    TopologicalSpace.Opens (Threefold.Space × Threefold.Space) :=
  ⟨{p | characterPairing s p.1 p.2 ≠ 0}, isOpen_ne.preimage (characterPairing_continuous s)⟩

def characterMatching (s : Finset SmoothOrbitCharacter) (x y : Threefold.Space)
    (h : characterPairing s x y ≠ 0) : Threefold.Space := complexPhase (characterPairing s x y) h • y

theorem characterMatching_continuous (s : Finset SmoothOrbitCharacter) :
    Continuous (fun p : characterMatchingDomain s => characterMatching s p.val.1 p.val.2 p.property) :=
  (complexPhase_continuous ((characterPairing_continuous s).comp continuous_subtype_val)
    (fun p => p.property)).smul continuous_subtype_val.snd

theorem characterPairing_self_ne_zero (s : Finset SmoothOrbitCharacter)
    (x : finiteCharacterDomain s) : characterPairing s x.val x.val ≠ 0 := by
  rw [characterPairing_self]
  exact Complex.ofReal_ne_zero.mpr x.property.ne'

theorem characterMatching_self (s : Finset SmoothOrbitCharacter) (x : finiteCharacterDomain s) :
    characterMatching s x.val x.val (characterPairing_self_ne_zero s x) = x.val := by
  unfold characterMatching
  simp only [characterPairing_self, complexPhase_positive_real _ x.property, one_smul]

theorem characterMatching_right_invariant (s : Finset SmoothOrbitCharacter) (v : Circle)
    (x y : Threefold.Space) (h : characterPairing s x y ≠ 0)
    (h' : characterPairing s x (v • y) ≠ 0) :
    characterMatching s x (v • y) h' = characterMatching s x y h := by
  unfold characterMatching
  have hp : complexPhase (characterPairing s x (v • y)) h' =
      v⁻¹ * complexPhase (characterPairing s x y) h :=
    (complexPhase_congr h' (mul_ne_zero (v⁻¹).coe_ne_zero h)
      (characterPairing_smul_right s v x y)).trans
        (complexPhase_mul_circle v⁻¹ (characterPairing s x y) h)
  rw [hp, mul_smul]
  rw [smul_comm (complexPhase (characterPairing s x y) h) v y, inv_smul_smul]

theorem quotientMap_characterMatching (s : Finset SmoothOrbitCharacter)
    (x y : Threefold.Space) (h : characterPairing s x y ≠ 0) :
    CircleOrbitSpace.quotientMap (characterMatching s x y h) = CircleOrbitSpace.quotientMap y :=
  quotientMap_unitCircle_smul _ _

end Wikipedia.HopfProblem.OrbitPair
