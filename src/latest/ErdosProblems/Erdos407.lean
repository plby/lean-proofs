/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
This is a Lean formalization of a solution to Erdős Problem 407.
https://www.erdosproblems.com/forum/thread/407

Informal authors:
- Prajeet Bajpai
- Michael A. Bennett
- Jan-Hendrik Evertse
- Kálmán Győry
- Carl Ludwig Stewart
- Robert Tijdeman
- Hans Peter Schlickewei
- Wolfgang M. Schmidt

Formal authors:
- Codex
- GPT-5.6 Sol

URLs:
- https://github.com/plby/lean-proofs/blob/main/ErdosProblems/Erdos407.md
-/
/-
This file formalizes Erdős Problem 407 (Newman's conjecture).

For n : ℕ, w n is the number of ordered exponent quadruples (a,b,c,d) : ℕ⁴
such that n = 2^a + 3^b + 2^c * 3^d.  Thus this is the literal counting
convention in the problem statement, not the later convention which identifies
permutations of the three summands.

Informal sources:
- J.-H. Evertse, K. Győry, C. L. Stewart, R. Tijdeman (1988),
  "S-unit equations and their applications".
- J.-H. Evertse, H. P. Schlickewei, W. M. Schmidt (2002),
  "Linear equations in variables which lie in a multiplicative group".
- P. Bajpai, M. A. Bennett (2024),
  "Effective S-unit equations beyond three terms: Newman's conjecture".
-/
import ErdosProblems.Erdos407.Basic
import ErdosProblems.Erdos407.EGST
import ErdosProblems.Erdos407.PadicSubspace
import ErdosProblems.Erdos407.StrongInequalityBridge
import ErdosProblems.Erdos407.TerminalBridge

namespace Erdos407

open scoped BigOperators Matrix

/-- The numerical part of Bajpai--Bennett's 2024 theorem, stated using the
exact unordered count above.  This is a proposition, not an assumption. -/
def BajpaiBennettNineBound : Prop := ∀ n : ℕ, omega n ≤ 9

theorem raw_le_twenty_seven_of_BajpaiBennett
    (hBB : BajpaiBennettNineBound) (n : ℕ) : w n ≤ 27 := by
  calc
    w n ≤ 3 * omega n := w_le_three_mul_omega n
    _ ≤ 3 * 9 := Nat.mul_le_mul_left 3 (hBB n)
    _ = 27 := by norm_num

theorem erdos_407_of_BajpaiBennett (hBB : BajpaiBennettNineBound) :
    ∃ C : ℕ, ∀ n : ℕ, w n ≤ C :=
  ⟨27, raw_le_twenty_seven_of_BajpaiBennett hBB⟩

/-!
## The exact deep input used in the published proof

The definitions below state, without postulating, the Evertse--Schlickewei--
Schmidt solution set used for Problem 407.  Mathlib 4.33.0 does not yet contain
the Subspace Theorem or the ESS theorem asserting its uniform finiteness.
-/

section LinearEquation

variable {K : Type*} [Field K]

/-- Solutions in a multiplicative subgroup of a linear equation with fixed
coefficients. -/
def linearEquationSolutions (m : ℕ) (Γ : Subgroup (Fin m → Kˣ))
    (coeff : Fin m → K) : Set Γ :=
  {x | (∑ i, coeff i * (x.1 i : K)) = 1}

/-- No nonempty subsum of the linear equation vanishes. -/
def IsNondegenerate {m : ℕ} {Γ : Subgroup (Fin m → Kˣ)}
    (coeff : Fin m → K) (x : Γ) : Prop :=
  ∀ I : Finset (Fin m), I.Nonempty →
    (∑ i ∈ I, coeff i * (x.1 i : K)) ≠ 0

/-- The nondegenerate solutions counted by the ESS theorem. -/
def nondegenerateLinearEquationSolutions (m : ℕ)
    (Γ : Subgroup (Fin m → Kˣ)) (coeff : Fin m → K) : Set Γ :=
  {x | x ∈ linearEquationSolutions m Γ coeff ∧ IsNondegenerate coeff x}

/-- The exact uniform theorem of Evertse--Schlickewei--Schmidt needed below.
This is a proposition, not an assumed theorem. -/
def ESSUniformBound : Prop :=
  ∀ (m r : ℕ) (Γ : Subgroup (Fin m → ℚˣ)) [Group.FG Γ],
    CommGroup.freeRank Γ ≤ r → ∀ coeff : Fin m → ℚ,
      (∀ i, coeff i ≠ 0) →
      (nondegenerateLinearEquationSolutions m Γ coeff).Finite ∧
      (nondegenerateLinearEquationSolutions m Γ coeff).ncard ≤
        ⌈Real.exp (((6 * m) ^ (3 * m) * (r + 1) : ℕ) : ℝ)⌉₊

end LinearEquation

private def genPureTwo : Fin 3 → ℚˣ :=
  ![Units.mk0 (2 : ℚ) (by norm_num), 1, 1]

private def genPureThree : Fin 3 → ℚˣ :=
  ![1, Units.mk0 (3 : ℚ) (by norm_num), 1]

private def genMixedTwo : Fin 3 → ℚˣ :=
  ![1, 1, Units.mk0 (2 : ℚ) (by norm_num)]

private def genMixedThree : Fin 3 → ℚˣ :=
  ![1, 1, Units.mk0 (3 : ℚ) (by norm_num)]

/-- The four multiplicative generators used in the ESS proof of Problem 407. -/
def gamma407Generators : Finset (Fin 3 → ℚˣ) :=
  {genPureTwo, genPureThree, genMixedTwo, genMixedThree}

/-- The rank-four multiplicative subgroup containing every encoded
representation. -/
def Gamma407 : Subgroup (Fin 3 → ℚˣ) :=
  Subgroup.closure (gamma407Generators : Set (Fin 3 → ℚˣ))

theorem gamma407Generators_card : gamma407Generators.card = 4 := by
  decide

instance : Group.FG Gamma407 := by
  rw [Group.fg_iff_subgroup_fg]
  exact ⟨gamma407Generators, rfl⟩

theorem Gamma407_rank_le_four : Group.rank Gamma407 ≤ 4 := by
  change Group.rank
    (Subgroup.closure (gamma407Generators : Set (Fin 3 → ℚˣ))) ≤ 4
  exact (Subgroup.rank_closure_finset_le_card gamma407Generators).trans_eq
    gamma407Generators_card

private theorem freeRank_le_rank (G : Type*) [CommGroup G] [Group.FG G] :
    CommGroup.freeRank G ≤ Group.rank G := by
  rw [CommGroup.freeRank_def]
  exact Group.rank_le_of_surjective (QuotientGroup.mk' (CommGroup.torsion G))
    (QuotientGroup.mk'_surjective (CommGroup.torsion G))

theorem Gamma407_freeRank_le_four : CommGroup.freeRank Gamma407 ≤ 4 :=
  (freeRank_le_rank Gamma407).trans Gamma407_rank_le_four

/-- The multiplicative-group point attached to an exponent quadruple. -/
def Rep.encodeUnits (r : Rep) : Fin 3 → ℚˣ :=
  ![Units.mk0 ((2 : ℚ) ^ r.a) (pow_ne_zero _ (by norm_num)),
    Units.mk0 ((3 : ℚ) ^ r.b) (pow_ne_zero _ (by norm_num)),
    Units.mk0 ((2 : ℚ) ^ r.c * (3 : ℚ) ^ r.d)
      (mul_ne_zero (pow_ne_zero _ (by norm_num)) (pow_ne_zero _ (by norm_num)))]

theorem Rep.encodeUnits_mem (r : Rep) : r.encodeUnits ∈ Gamma407 := by
  have hA : genPureTwo ∈ Gamma407 :=
    Subgroup.subset_closure (by simp [gamma407Generators])
  have hB : genPureThree ∈ Gamma407 :=
    Subgroup.subset_closure (by simp [gamma407Generators])
  have hC : genMixedTwo ∈ Gamma407 :=
    Subgroup.subset_closure (by simp [gamma407Generators])
  have hD : genMixedThree ∈ Gamma407 :=
    Subgroup.subset_closure (by simp [gamma407Generators])
  have hprod :
      genPureTwo ^ r.a * genPureThree ^ r.b *
        genMixedTwo ^ r.c * genMixedThree ^ r.d ∈ Gamma407 :=
    Gamma407.mul_mem
      (Gamma407.mul_mem
        (Gamma407.mul_mem (Gamma407.pow_mem hA r.a) (Gamma407.pow_mem hB r.b))
        (Gamma407.pow_mem hC r.c))
      (Gamma407.pow_mem hD r.d)
  convert hprod using 1
  funext i
  fin_cases i <;>
    apply Units.ext <;>
    simp [Rep.encodeUnits, genPureTwo, genPureThree, genMixedTwo, genMixedThree]

/-- The encoded point, bundled with its membership in the rank-four group. -/
def Rep.encode (r : Rep) : Gamma407 := ⟨r.encodeUnits, r.encodeUnits_mem⟩

theorem Rep.encode_injective : Function.Injective Rep.encode := by
  intro r s hrs
  apply Rep.encodeNat_injective
  funext i
  have hi := congrArg (fun u : ℚˣ => (u : ℚ))
    (congrFun (congrArg Subtype.val hrs) i)
  fin_cases i <;>
    simp [Rep.encode, Rep.encodeUnits, Rep.encodeNat] at hi ⊢ <;>
    exact_mod_cast hi

private def coeff407 (n : ℕ) : Fin 3 → ℚ := fun _ => (n : ℚ)⁻¹

private theorem Rep.encode_mem_nondegenerateSolutions {n : ℕ} (hn : n ≠ 0)
    {r : Rep} (hr : r ∈ solutions n) :
    r.encode ∈ nondegenerateLinearEquationSolutions 3 Gamma407 (coeff407 n) := by
  constructor
  · change (∑ i, coeff407 n i * ((r.encode.1 i : ℚ))) = 1
    have hcast :
        ((2 ^ r.a + 3 ^ r.b + 2 ^ r.c * 3 ^ r.d : ℕ) : ℚ) = n := by
      exact_mod_cast hr
    simp [coeff407, Rep.encode, Rep.encodeUnits, Fin.sum_univ_succ]
    field_simp
    simpa [Nat.cast_add, Nat.cast_mul, Nat.cast_pow, add_assoc] using hcast
  · intro I hI
    apply ne_of_gt
    apply Finset.sum_pos
    · intro i hi
      have hnpos : (0 : ℚ) < (n : ℚ)⁻¹ := by
        exact inv_pos.mpr (by exact_mod_cast Nat.pos_of_ne_zero hn)
      have hcoord : (0 : ℚ) < (r.encode.1 i : ℚ) := by
        fin_cases i <;> simp [Rep.encode, Rep.encodeUnits]
      exact mul_pos hnpos hcoord
    · exact hI

/-- Once the published ESS theorem is available, all remaining steps of
Problem 407 are elementary.  This theorem records that exact reduction; its
hypothesis is deliberately explicit and is not an assumption of this file. -/
theorem erdos_407_of_ESS (hESS : ESSUniformBound) :
    ∃ C : ℕ, ∀ n : ℕ, w n ≤ C := by
  let C : ℕ := ⌈Real.exp (((6 * 3) ^ (3 * 3) * (4 + 1) : ℕ) : ℝ)⌉₊
  use C
  intro n
  by_cases hn : n = 0
  · subst n
    have hnone : solutions 0 = ∅ := by
      ext r
      simp only [solutions, Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
      intro hr
      have hpos : 0 < r.value := by
        simp only [Rep.value]
        positivity
      omega
    simp [w, hnone]
  · obtain ⟨hfinite, hcard⟩ :=
      hESS 3 4 Gamma407 Gamma407_freeRank_le_four (coeff407 n)
        (fun _ => inv_ne_zero (by exact_mod_cast hn))
    calc
      w n = (solutions n).ncard := rfl
      _ ≤ (nondegenerateLinearEquationSolutions 3 Gamma407 (coeff407 n)).ncard :=
        Set.ncard_le_ncard_of_injOn Rep.encode
          (fun _ hr => Rep.encode_mem_nondegenerateSolutions hn hr)
          Rep.encode_injective.injOn hfinite
      _ ≤ C := hcard

/-!
## Unconditional conclusion

The specialized rational three-place Subspace Theorem is proved in the
`PadicSubspace` development.  The strong-inequality bridge turns it into
bounded-arity `{2,3}`-unit equation finiteness, and the terminal bridge then
applies the elementary EGST partition argument to the literal ordered count.
-/

/-- **Erdős Problem 407 (Newman's conjecture).**  The number of ordered
quadruples `(a,b,c,d)` of nonnegative integers satisfying
`n = 2^a + 3^b + 2^c * 3^d` is bounded independently of `n`. -/
theorem erdos_407 : ∃ C : ℕ, ∀ n : ℕ, w n ≤ C :=
  TerminalBridge.erdos407_of_specializedPadicSubspaceUpToFive
    (StrongInequalityBridge.specializedPadicSubspaceFiniteCoverUpTo_five_of_strongTheorem
      (fun {n} hn2 hn5 L hL =>
        PadicSubspace.finiteCover_primitiveStrongSolutions hn2 hn5 L hL))

#print axioms erdos_407_of_ESS
#print axioms erdos_407_of_BajpaiBennett
#print axioms erdos_407

end Erdos407
