import ErdosProblems.Erdos4.DivisibilityExpansion
import ErdosProblems.Erdos4.CoprimeResidueCount

/-!
# A divisor label is one arithmetic residue class

Each occupied prime contributes one affine divisibility condition.
Pairwise coprimality combines these into one CRT class. With the fixed
small-prime condition, its interval count differs from its density main
term by at most the totient of the small modulus.
-/

open scoped BigOperators

namespace Erdos4.LabelResidueClass

open DivisorCoefficients LocalIndicatorExpansion DivisibilityExpansion

variable {P : Type*} [Fintype P] [DecidableEq P] {k : ℕ}
    (ell : P → ℕ) [∀ l, Fact (ell l).Prime]

def localModulus (b : P → Option (Fin k)) (l : P) : ℕ := if b l = none then 1 else ell l

def localShift (h : Fin k → ℕ) (b : P → Option (Fin k)) (l : P) : ℕ :=
  match b l with
  | none => 0
  | some i => h i

def Condition (h : Fin k → ℕ) (p : ℕ) (b : P → Option (Fin k)) (n : ℕ) : Prop :=
  ∀ l, localModulus ell b l ∣ n + localShift h b l * p

theorem localModulus_pos (b : P → Option (Fin k)) (l : P) : 0 < localModulus ell b l := by
  unfold localModulus
  split_ifs
  · exact Nat.zero_lt_one
  · exact (Fact.out : (ell l).Prime).pos

theorem localModulus_pairwise (hcop : Pairwise (fun l r => (ell l).Coprime (ell r)))
    (b : P → Option (Fin k)) : Pairwise (fun l r =>
      (localModulus ell b l).Coprime (localModulus ell b r)) := by
  intro l r hlr
  unfold localModulus
  split_ifs <;> first | simp | exact hcop hlr

theorem exists_residue (hcop : Pairwise (fun l r => (ell l).Coprime (ell r)))
    (h : Fin k → ℕ) (p : ℕ) (b : P → Option (Fin k)) :
    ∃ a : ℕ, ∀ n : ℕ, Condition ell h p b n ↔ n ≡ a [MOD totalDivisor ell b] := by
  classical
  let L := (Finset.univ : Finset P).toList
  let m := localModulus ell b
  let r : P → ℕ := fun l => BoundedGaps.Maynard.negativeShiftResidue (m l) (localShift h b l * p)
  have hpair : L.Pairwise (fun l r => (m l).Coprime (m r)) := by
    apply List.Nodup.pairwise_of_forall_ne Finset.univ.nodup_toList
    intro l _hl r _hr hlr
    exact localModulus_pairwise ell hcop b hlr
  let a : ℕ := Nat.chineseRemainderOfList r m L hpair
  have hprod : (L.map m).prod = totalDivisor ell b := by
    simp [L, m, localModulus, totalDivisor]
    rfl
  refine ⟨a, ?_⟩
  intro n
  have hc := BoundedGaps.Maynard.modEq_crt_iff r m L hpair n
  rw [hprod] at hc
  constructor
  · intro hn
    apply hc.mpr
    intro l _hl
    exact (BoundedGaps.Maynard.modEq_negativeShiftResidue_iff_dvd_add
      (m l) (localShift h b l * p) n (localModulus_pos ell b l)).mpr (hn l)
  · intro hn l
    exact (BoundedGaps.Maynard.modEq_negativeShiftResidue_iff_dvd_add
      (m l) (localShift h b l * p) n (localModulus_pos ell b l)).mp
      (hc.mp hn l (by simp [L]))

theorem residueState_some_iff (h : Fin k → ℕ)
    (hh : ∀ l, Function.Injective (fun i => (h i : ZMod (ell l))))
    (p : ℕ) (hp : p.Coprime (ProductCharacterEncoding.modulus ell)) (n : ℕ) (l : P) (i : Fin k) :
    AffineWeights.residueState ell h n p l = some i ↔ ell l ∣ n + h i * p := by
  have hp0 : (p : ZMod (ell l)) ≠ 0 := by
    rw [← AffineWeights.unitPoint_coe ell p hp l]
    exact Units.ne_zero _
  unfold AffineWeights.residueState
  rw [AffineWeights.state_eq_some_iff _ (hh l) _ _ hp0]
  simpa only [Nat.cast_add, Nat.cast_mul] using
    ZMod.natCast_eq_zero_iff (n + h i * p) (ell l)

theorem indicator_eq (h : Fin k → ℕ)
    (hh : ∀ l, Function.Injective (fun i => (h i : ZMod (ell l))))
    (p : ℕ) (hp : p.Coprime (ProductCharacterEncoding.modulus ell))
    (b : P → Option (Fin k)) (n : ℕ) (l : P) :
    indicator (AffineWeights.residueState ell h n p l) (b l) =
      if localModulus ell b l ∣ n + localShift h b l * p then 1 else 0 := by
  cases hb : b l with
  | none => simp [hb, indicator, localModulus, localShift]
  | some i =>
    simp only [indicator, localModulus, localShift, hb, reduceCtorEq, if_false]
    simp only [residueState_some_iff ell h hh p hp n l i]

open Classical in
theorem evaluation_eq (h : Fin k → ℕ)
    (hh : ∀ l, Function.Injective (fun i => (h i : ZMod (ell l))))
    (p : ℕ) (hp : p.Coprime (ProductCharacterEncoding.modulus ell))
    (b : P → Option (Fin k)) (n : ℕ) :
    evaluation (AffineWeights.residueState ell h n p) b =
      if Condition ell h p b n then 1 else 0 := by
  unfold evaluation
  simp_rw [indicator_eq ell h hh p hp b n]
  by_cases hn : Condition ell h p b n
  · rw [if_pos hn]
    exact Finset.prod_eq_one (fun l _hl => if_pos (hn l))
  · rw [if_neg hn]
    obtain ⟨l, hl⟩ := not_forall.mp hn
    exact Finset.prod_eq_zero (Finset.mem_univ l) (if_neg hl)

theorem evaluation_is_residue (hcop : Pairwise (fun l r => (ell l).Coprime (ell r)))
    (h : Fin k → ℕ) (hh : ∀ l, Function.Injective (fun i => (h i : ZMod (ell l))))
    (p : ℕ) (hp : p.Coprime (ProductCharacterEncoding.modulus ell)) (b : P → Option (Fin k)) :
    ∃ a : ℕ, ∀ n : ℕ, evaluation (AffineWeights.residueState ell h n p) b =
      if n ≡ a [MOD totalDivisor ell b] then 1 else 0 := by
  classical
  obtain ⟨a, ha⟩ := exists_residue ell hcop h p b
  refine ⟨a, ?_⟩
  intro n
  simp only [evaluation_eq ell h hh p hp b n, ha n]

theorem coprime_totalDivisor (W : ℕ) (hWcop : ∀ l, W.Coprime (ell l))
    (b : P → Option (Fin k)) : W.Coprime (totalDivisor ell b) := by
  apply Nat.coprime_prod_right_iff.mpr
  intro l _hl
  split_ifs
  · exact Nat.coprime_one_right W
  · exact hWcop l

theorem count_error_le (Y W : ℕ) (hW : 0 < W) (hWcop : ∀ l, W.Coprime (ell l))
    (hcop : Pairwise (fun l r => (ell l).Coprime (ell r)))
    (h : Fin k → ℕ) (hh : ∀ l, Function.Injective (fun i => (h i : ZMod (ell l))))
    (p : ℕ) (hp : p.Coprime (ProductCharacterEncoding.modulus ell)) (b : P → Option (Fin k)) :
    |(∑ n ∈ Finset.Icc 1 Y, if n.Coprime W then
        evaluation (AffineWeights.residueState ell h n p) b else 0) -
      BoundedGaps.Maynard.coprimeHarmonicDensity W * Y / totalDivisor ell b| ≤ Nat.totient W := by
  classical
  obtain ⟨a, ha⟩ := evaluation_is_residue ell hcop h hh p hp b
  have heq : (∑ n ∈ Finset.Icc 1 Y, if n.Coprime W then
      evaluation (AffineWeights.residueState ell h n p) b else 0) =
      CoprimeResidueCount.coprimeCount Y W (totalDivisor ell b) a := by
    unfold CoprimeResidueCount.coprimeCount
    apply Finset.sum_congr rfl
    intro n _hn
    rw [ha n]
    by_cases hc : n.Coprime W <;> by_cases hd : n ≡ a [MOD totalDivisor ell b] <;> simp [hc, hd]
  rw [heq]
  exact CoprimeResidueCount.density_error_le Y W (totalDivisor ell b) a hW
    (totalDivisor_pos ell (fun l => (Fact.out : (ell l).Prime).pos) b)
    (coprime_totalDivisor ell W hWcop b)

end Erdos4.LabelResidueClass
