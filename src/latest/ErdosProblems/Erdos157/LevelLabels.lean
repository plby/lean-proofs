import ErdosProblems.Erdos157.PrefixParameters
import ErdosProblems.Erdos157.PrimeTripleCounts

/-! Prime-polynomial labels with an unambiguous construction level. -/

namespace Erdos157.Elementary

open Polynomial PolynomialCharacters

theorem levelDegree_strictMonoOn : StrictMonoOn levelDegree (Set.Ici 3) := by
  intro a ha b hb hab
  have hnext := levelDegree_lt_next_window a ha
  have hlower := levelDegree_lower b
  have hab' : (a : ℝ) + 1 ≤ b := by exact_mod_cast hab
  have hsq : ((a : ℝ) + 1) ^ 2 ≤ (b : ℝ) ^ 2 := by gcongr
  have hd : (levelDegree a : ℝ) < levelDegree b := by linarith
  exact_mod_cast hd

abbrev LevelLabel (K : Type*) [Field K] (k : ℕ) := PrimeDegree K (levelDegree k)

/-- The initial cutoff is only for the deterministic level-comparison inequalities. -/
abbrev Label (K : Type*) [Field K] := Σ k : {k : ℕ // 400 ≤ k}, LevelLabel K k.1

namespace Label

variable {K : Type*} [Field K]

def level (f : Label K) : ℕ := f.1.1

def polynomial (f : Label K) : K[X] := f.2.1.1

theorem level_ge (f : Label K) : 400 ≤ f.level := f.1.2

theorem monic (f : Label K) : f.polynomial.Monic := f.2.1.monic

theorem irreducible (f : Label K) : Irreducible f.polynomial := f.2.2

theorem natDegree (f : Label K) : f.polynomial.natDegree = levelDegree f.level := f.2.1.natDegree

theorem polynomial_injective : Function.Injective (polynomial (K := K)) := by
  rintro ⟨⟨k, hk⟩, f⟩ ⟨⟨l, hl⟩, g⟩ h
  have hdeg := congrArg Polynomial.natDegree h
  change f.1.1.natDegree = g.1.1.natDegree at hdeg
  rw [f.1.natDegree, g.1.natDegree] at hdeg
  have hkl : k = l := levelDegree_strictMonoOn.injOn (by change 3 ≤ k; omega)
    (by change 3 ≤ l; omega) hdeg
  subst l
  have hfg : f = g := Subtype.ext (Subtype.ext h)
  subst g
  rfl

instance countable [Fintype K] : Countable (Label K) := inferInstance

end Label
end Erdos157.Elementary
