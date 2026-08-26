import ErdosProblems.Erdos1148.IntegralFormOrbits

/-! # The two individual form orbits underlying an integral pair orbit -/

namespace Erdos1148.DukeArithmetic

open scoped MatrixGroups

def pairFirstForm {d ℓ : ℤ} (p : FormPair ℤ d ℓ) : IntegralDiscrForm d := ⟨p.1.1, p.2.1⟩

def pairSecondForm {d ℓ : ℤ} (p : FormPair ℤ d ℓ) : IntegralDiscrForm d := ⟨p.1.2, p.2.2.1⟩

lemma pairFirstForm_action {d ℓ : ℤ} (g : SL(2, ℤ)) (p : FormPair ℤ d ℓ) :
    pairFirstForm (g • p) = g • pairFirstForm p := rfl

lemma pairSecondForm_action {d ℓ : ℤ} (g : SL(2, ℤ)) (p : FormPair ℤ d ℓ) :
    pairSecondForm (g • p) = g • pairSecondForm p := rfl

def pairOrbitFirst {d ℓ : ℤ} : IntegralPairOrbits d ℓ → IntegralFormOrbits d :=
  Quotient.map pairFirstForm (by
    intro p q hrel
    obtain ⟨g, hg⟩ := MulAction.mem_orbit_iff.mp (MulAction.orbitRel_apply.mp hrel)
    apply MulAction.orbitRel_apply.mpr
    apply MulAction.mem_orbit_iff.mpr
    exact ⟨g, (pairFirstForm_action g q).symm.trans (congrArg pairFirstForm hg)⟩)

def pairOrbitSecond {d ℓ : ℤ} : IntegralPairOrbits d ℓ → IntegralFormOrbits d :=
  Quotient.map pairSecondForm (by
    intro p q hrel
    obtain ⟨g, hg⟩ := MulAction.mem_orbit_iff.mp (MulAction.orbitRel_apply.mp hrel)
    apply MulAction.orbitRel_apply.mpr
    apply MulAction.mem_orbit_iff.mpr
    exact ⟨g, (pairSecondForm_action g q).symm.trans (congrArg pairSecondForm hg)⟩)

lemma pairOrbitFirst_out {d ℓ : ℤ} (q : IntegralPairOrbits d ℓ) :
    pairOrbitFirst q = integralFormOrbitMk (pairFirstForm q.out) :=
  (congrArg pairOrbitFirst (Quotient.out_eq q)).symm

lemma pairOrbitSecond_out {d ℓ : ℤ} (q : IntegralPairOrbits d ℓ) :
    pairOrbitSecond q = integralFormOrbitMk (pairSecondForm q.out) :=
  (congrArg pairOrbitSecond (Quotient.out_eq q)).symm

end Erdos1148.DukeArithmetic
