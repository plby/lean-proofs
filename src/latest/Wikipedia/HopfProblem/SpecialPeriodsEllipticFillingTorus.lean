import Wikipedia.HopfProblem.TrianglePeriodFamilyGeometry
import Wikipedia.HopfProblem.EllipticLogGaugeQuotients
import Wikipedia.HopfProblem.SpecialPeriodsTriangleQuotientEllipticNeighborhoods

/-!
# The untwisted elliptic action and the genuine triangle monodromy

The actual triangle generator acts on the real period torus by precisely
the zero-twist affine action used in the elliptic filling.  This identity
is checked on every lattice representative, and extended to every cyclic
iterate and to the punctured varying-period family.
-/

noncomputable section

open scoped Matrix

namespace Wikipedia.HopfProblem.SpecialPeriods.EllipticFilling

open Elliptic

/-- The dual integral monodromy of the indicated actual elliptic generator. -/
theorem ellipticGenerator_dual_matrix (j : Kind) :
    (triangleDualRepresentation (Triangle.ellipticGenerator j) : LatticeMatrix) =
      j.matrix := by
  cases j
  · exact triangleDualRepresentation_generator₁_matrix
  · exact triangleDualRepresentation_generator₂_matrix

/-- On every real lattice representative the actual triangle action is
the prescribed elliptic linear map. -/
theorem ellipticGenerator_torus_mkQ (j : Kind) (x : RealCoordinates) :
    triangleTorusHomeomorph (Triangle.ellipticGenerator j) (standardLattice.mkQ x) =
      standardLattice.mkQ (flatLinear j x) := by
  rw [triangleTorusHomeomorph_mkQ, triangleRealEquiv_apply,
    ellipticGenerator_dual_matrix]
  rfl

/-- The actual triangle generator and the zero-twist elliptic generator
are the same homeomorphism of the actual quotient torus. -/
theorem ellipticGenerator_torus_eq (j : Kind) :
    triangleTorusHomeomorph (Triangle.ellipticGenerator j) = flatTorusAffine j 0 := by
  apply Homeomorph.ext
  intro x
  obtain ⟨u, rfl⟩ := standardLattice.mkQ_surjective x
  rw [ellipticGenerator_torus_mkQ, flatTorusAffine_mkQ]
  have hz : Elliptic.realCast (0 : Lattice) = 0 := by
    ext i
    simp [Elliptic.realCast]
  rw [flatAffine, hz, smul_zero, add_zero]

/-- Every untwisted elliptic iterate is the corresponding positive power
of the actual triangle generator; no inversion convention is imposed. -/
theorem flatTorusAffine_zero_iterate (j : Kind) (n : ℕ) (x : RealTorus₄) :
    (flatTorusAffine j 0)^[n] x =
      triangleTorusHomeomorph (Triangle.ellipticGenerator j ^ n) x := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Function.iterate_succ_apply', ih, pow_succ',
      triangleTorusHomeomorph_mul_apply, ellipticGenerator_torus_eq]

/-- The complete zero-twist cyclic action, in actual triangle torus coordinates. -/
theorem zeroAction_apply {j : Kind} (D : Equivariant.Data j)
    (g : CyclicGroup j) (x : D.TotalSpace) :
    letI := D.action 0 (Matrix.mulVec_zero j.matrix)
    g • x = ((familyRotation j)^[g.toAdd.val] x.1,
      triangleTorusHomeomorph (Triangle.ellipticGenerator j ^ g.toAdd.val) x.2) := by
  let := D.action 0 (Matrix.mulVec_zero j.matrix)
  rw [D.action_apply, flatTorusAffine_zero_iterate]

/-- On the literal punctured family, the zero-twist cyclic action is the
restriction of the same base rotation and actual triangle monodromy. -/
theorem zeroStarAction_coe {j : Kind} (D : Equivariant.Data j)
    (g : CyclicGroup j) (x : LogGauge.FamilyStar D.periods) :
    letI := LogGauge.starAction D 0 (Matrix.mulVec_zero j.matrix)
    ((g • x : LogGauge.FamilyStar D.periods) : D.TotalSpace) =
      ((familyRotation j)^[g.toAdd.val] x.1.1,
        triangleTorusHomeomorph (Triangle.ellipticGenerator j ^ g.toAdd.val) x.1.2) := by
  let := D.action 0 (Matrix.mulVec_zero j.matrix)
  let := LogGauge.starAction D 0 (Matrix.mulVec_zero j.matrix)
  rw [LogGauge.starAction_coe, zeroAction_apply]

/-- The base component of the actual zero-twist action on the punctured family. -/
theorem zeroStarAction_fst {j : Kind} (D : Equivariant.Data j)
    (g : CyclicGroup j) (x : LogGauge.FamilyStar D.periods) :
    letI := LogGauge.starAction D 0 (Matrix.mulVec_zero j.matrix)
    (g • x : LogGauge.FamilyStar D.periods).1.1 =
      (familyRotation j)^[g.toAdd.val] x.1.1 := by
  let := LogGauge.starAction D 0 (Matrix.mulVec_zero j.matrix)
  exact congrArg Prod.fst (zeroStarAction_coe D g x)

/-- The torus component of the actual zero-twist action on the punctured family. -/
theorem zeroStarAction_snd {j : Kind} (D : Equivariant.Data j)
    (g : CyclicGroup j) (x : LogGauge.FamilyStar D.periods) :
    letI := LogGauge.starAction D 0 (Matrix.mulVec_zero j.matrix)
    (g • x : LogGauge.FamilyStar D.periods).1.2 =
      triangleTorusHomeomorph (Triangle.ellipticGenerator j ^ g.toAdd.val) x.1.2 := by
  let := LogGauge.starAction D 0 (Matrix.mulVec_zero j.matrix)
  exact congrArg Prod.snd (zeroStarAction_coe D g x)

/-- A bounded power of the actual stabilizer generator is realized by
the corresponding residue class in the cyclic punctured-family action. -/
theorem zeroStarAction_natCast_coe {j : Kind} (D : Equivariant.Data j)
    (n : ℕ) (hn : n < j.order) (x : LogGauge.FamilyStar D.periods) :
    letI := LogGauge.starAction D 0 (Matrix.mulVec_zero j.matrix)
    ((Multiplicative.ofAdd (n : ZMod j.order) • x : LogGauge.FamilyStar D.periods) :
        D.TotalSpace) =
      ((familyRotation j)^[n] x.1.1,
        triangleTorusHomeomorph (Triangle.ellipticGenerator j ^ n) x.1.2) := by
  let := LogGauge.starAction D 0 (Matrix.mulVec_zero j.matrix)
  simpa only [toAdd_ofAdd, ZMod.val_natCast_of_lt hn] using
    zeroStarAction_coe D (Multiplicative.ofAdd (n : ZMod j.order)) x

end Wikipedia.HopfProblem.SpecialPeriods.EllipticFilling
