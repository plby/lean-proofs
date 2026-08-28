import Wikipedia.HopfProblem.SpecialPeriodsThreefoldFiniteActionFixedEllipticArithmetic
import Wikipedia.HopfProblem.SpecialPeriodsThreefoldFiniteActionFixedPeriods
import Wikipedia.HopfProblem.SpecialPeriodsThreefoldVerticalActionEllipticSpecial

/-!
# Real-time stabilizers in the original affine elliptic fillings

The actual varying-period family has its fixed real-coordinate torus
as underlying fibre. Its finite affine generator changes the gamma
coordinate by a nonintegral fraction, whereas a real vertical flow
changes only the last coordinate. Thus a deck transformation relating
a real translate to its starting point must be the identity. The last
coordinate then shows that the translation time is an integer.

This proves the assertion on the full quotient, including its central
fibre, and on the original small elliptic pieces. No period-lattice
condition or absence of isotropy is assumed.
-/

noncomputable section

open scoped Matrix

namespace Wikipedia.HopfProblem.SpecialPeriods.Threefold.FiniteActionFixed.Elliptic

open Wikipedia.HopfProblem.Elliptic EllipticFilling

variable {j : Kind} (D : Equivariant.Data j)

/-- In the original real-coordinate family, real vertical time changes
only the primitive last lattice coordinate. -/
theorem real_periodFlow_mkQ (s : ℝ) (b : Disc) (x : RealCoordinates) :
    VerticalAction.Period.flow D.periods (s : ℂ) (b, standardLattice.mkQ x) =
      (b, standardLattice.mkQ (x + s • Pi.basisFun ℝ (Fin 4) 3)) := by
  simp only [VerticalAction.Period.flow, Period.inverse_vector_real, map_add]

/-- Equality between an actual cyclic deck translate and a real flow
translate gives the literal affine congruence in the fixed real lattice. -/
theorem flatCongruent_of_action_eq_real_flow (v : Lattice)
    (hv : j.matrix *ᵥ v = v) (g : CyclicGroup j) (s : ℝ)
    (b : Disc) (x : RealCoordinates) :
    letI := D.action v hv
    g • (b, standardLattice.mkQ x) =
        VerticalAction.Period.flow D.periods (s : ℂ) (b, standardLattice.mkQ x) →
      FlatCongruent ((flatAffine j v)^[g.toAdd.val] x)
        (x + s • Pi.basisFun ℝ (Fin 4) 3) := by
  let := D.action v hv
  intro h
  rw [D.action_apply, real_periodFlow_mkQ] at h
  apply (flatTorus_mkQ_eq_iff _ _).mp
  simpa only [flatTorusAffine_iterate_mkQ] using congrArg Prod.snd h

/-- Every real stabilizer of the genuine affine filling is integral,
for arbitrary actual equivariant periods and admissible twist. -/
theorem real_flow_eq_self_iff (v : Lattice) (hv : AdmissibleTwist j v)
    (s : ℝ) (x : D.Space v hv) :
    VerticalAction.Elliptic.flow D v hv (s : ℂ) x = x ↔
      ∃ n : ℤ, s = (n : ℝ) := by
  constructor
  · obtain ⟨y, rfl⟩ := D.quotient_surjective v hv x
    intro h
    rw [VerticalAction.Elliptic.flow_quotient] at h
    let := D.action v hv.1
    obtain ⟨g, hg⟩ := (D.quotient_eq_iff_mem_orbit v hv _ _).mp h
    obtain ⟨z, hz⟩ := standardLattice.mkQ_surjective y.2
    have hy : y = (y.1, standardLattice.mkQ z) := Prod.ext rfl hz.symm
    rw [hy] at hg
    have hc := flatCongruent_of_action_eq_real_flow D v hv.1 g s y.1 z hg
    exact (flatAffine_iterate_vertical_congruent j v hv g.toAdd.val
      (ZMod.val_lt _) z s hc).2
  · rintro ⟨n, rfl⟩
    simpa only [Complex.ofReal_intCast] using
      VerticalAction.Elliptic.flow_int_cast D v hv n x

/-- No nonintegral real time fixes any point of an original affine
elliptic quotient, including points in its central fibre. -/
theorem real_flow_ne_self (v : Lattice) (hv : AdmissibleTwist j v)
    (s : ℝ) (hs : ¬ ∃ n : ℤ, s = (n : ℝ)) (x : D.Space v hv) :
    VerticalAction.Elliptic.flow D v hv (s : ℂ) x ≠ x :=
  fun h => hs ((real_flow_eq_self_iff D v hv s x).mp h)

/-- The actual full special filling has precisely the integral real
stabilizers, with no hypothesis on its period family. -/
theorem real_specialFullFlow_eq_self_iff (j : Kind) (s : ℝ)
    (x : SpecialFullFilling j) :
    VerticalAction.Elliptic.specialFullFlow j (s : ℂ) x = x ↔
      ∃ n : ℤ, s = (n : ℝ) :=
  real_flow_eq_self_iff (specialLocalData j) j.twist (mainTwist_admissible j) s x

/-- The actual small elliptic pieces, with their unchanged inclusions,
also have precisely the integral real stabilizers. -/
theorem real_specialFlow_eq_self_iff (j : Kind) (s : ℝ)
    (x : EllipticGeometry.LocalSpace j) :
    VerticalAction.Elliptic.specialFlow j (s : ℂ) x = x ↔
      ∃ n : ℤ, s = (n : ℝ) := by
  constructor
  · intro h
    exact (real_specialFullFlow_eq_self_iff j s x.val).mp (congrArg Subtype.val h)
  · rintro ⟨n, rfl⟩
    simpa only [Complex.ofReal_intCast] using
      VerticalAction.Elliptic.specialFlow_int_cast j n x

/-- A nonintegral real time has no fixed point anywhere in the actual
full special elliptic filling. -/
theorem real_specialFullFlow_ne_self (j : Kind) (s : ℝ)
    (hs : ¬ ∃ n : ℤ, s = (n : ℝ)) (x : SpecialFullFilling j) :
    VerticalAction.Elliptic.specialFullFlow j (s : ℂ) x ≠ x :=
  fun h => hs ((real_specialFullFlow_eq_self_iff j s x).mp h)

/-- A nonintegral real time has no fixed point anywhere in either
original small elliptic filling. -/
theorem real_specialFlow_ne_self (j : Kind) (s : ℝ)
    (hs : ¬ ∃ n : ℤ, s = (n : ℝ)) (x : EllipticGeometry.LocalSpace j) :
    VerticalAction.Elliptic.specialFlow j (s : ℂ) x ≠ x :=
  fun h => hs ((real_specialFlow_eq_self_iff j s x).mp h)

end Wikipedia.HopfProblem.SpecialPeriods.Threefold.FiniteActionFixed.Elliptic
