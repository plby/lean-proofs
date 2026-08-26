import ErdosProblems.Erdos67.StationaryModel
import ErdosProblems.Erdos67.StationaryFiniteLaw

/-!
# Uniform residue blocks from joint stationarity

For pairwise coprime moduli, simultaneous addition of one is transitive on the
finite product of residue rings. Thus stationarity forces the joint residue law
to be uniform. This supplies the independence used in the entropy argument.
-/

open scoped BigOperators
open Finset MeasureTheory

namespace Erdos67.StationaryModel

open FiniteEntropy

theorem shift_nat_eq_iterate (n : ℕ) : shift (n : ℤ) = (shift 1)^[n] := by
  funext ω
  induction n with
  | zero => exact shift_zero ω
  | succ n ih =>
    rw [Function.iterate_succ_apply', ← ih, ← shift_add]
    congr 1
    push_cast
    ring

theorem shift_nat_preserving (Q : ProbabilityMeasure Configuration)
    (hQ : Measure.map (shift 1) (Q : Measure Configuration) = (Q : Measure Configuration))
    (n : ℕ) :
    Measure.map (shift (n : ℤ)) (Q : Measure Configuration) = (Q : Measure Configuration) := by
  have hpres :
      MeasurePreserving (shift 1) (Q : Measure Configuration) (Q : Measure Configuration) :=
    ⟨(continuous_shift 1).measurable, hQ⟩
  rw [shift_nat_eq_iterate]
  exact (hpres.iterate n).map_eq

variable {ι : Type*}

def residueTuple (q : ι → ℕ+) (ω : Configuration) : ∀ i, ZMod (q i).val :=
  fun i ↦ ω.2 (q i)

theorem continuous_residueTuple (q : ι → ℕ+) : Continuous (residueTuple q) :=
  continuous_pi fun i ↦ (continuous_apply (q i)).comp continuous_snd

theorem residueTuple_shift_nat (q : ι → ℕ+) (n : ℕ) (ω : Configuration) :
    residueTuple q (shift (n : ℤ) ω) = residueTuple q ω + (fun i ↦ (n : ZMod (q i).val)) := by
  funext i
  simp [residueTuple, shift]

/-- Every residue vector is represented by a single nonnegative integer. -/
theorem exists_nat_residueTuple [Finite ι] (q : ι → ℕ+)
    (hcoprime : Pairwise (Function.onFun Nat.Coprime (fun i ↦ (q i).val)))
    (a : ∀ i, ZMod (q i).val) :
    ∃ n : ℕ, (fun i ↦ (n : ZMod (q i).val)) = a := by
  let : Fintype ι := Fintype.ofFinite ι
  have hprod : 0 < ∏ i, (q i).val := Finset.prod_pos fun i _ ↦ (q i).pos
  let : NeZero (∏ i, (q i).val) := ⟨hprod.ne'⟩
  let e := ZMod.prodEquivPi (fun i ↦ (q i).val) hcoprime
  let n := (e.symm a).val
  refine ⟨n, ?_⟩
  calc
    (fun i ↦ (n : ZMod (q i).val)) = e (n : ZMod (∏ i, (q i).val)) := by
      rw [map_natCast]
      rfl
    _ = a := by
      dsimp [n]
      rw [ZMod.natCast_zmod_val, e.apply_symm_apply]

theorem residueTuple_law_uniform [Fintype ι] [DecidableEq ι] (Q : ProbabilityMeasure Configuration)
    (hQ : Measure.map (shift 1) (Q : Measure Configuration) = (Q : Measure Configuration))
    (q : ι → ℕ+)
    (hcoprime : Pairwise (Function.onFun Nat.Coprime (fun i ↦ (q i).val))) :
    measureLaw Q (residueTuple q) (continuous_residueTuple q).measurable = uniformVector := by
  let P := measureLaw Q (residueTuple q) (continuous_residueTuple q).measurable
  apply eq_uniformVector_of_constant P
  intro a b
  obtain ⟨n, hn⟩ := exists_nat_residueTuple q hcoprime (b - a)
  let e : Equiv.Perm (∀ i, ZMod (q i).val) :=
    Equiv.addRight (fun i ↦ (n : ZMod (q i).val))
  have heab : e a = b := by
    change a + (fun i ↦ (n : ZMod (q i).val)) = b
    rw [hn]
    abel
  have hfun : e ∘ residueTuple q = residueTuple q ∘ shift (n : ℤ) := by
    funext ω
    exact (residueTuple_shift_nat q n ω).symm
  have hmap := measureLaw_map Q (residueTuple q) (continuous_residueTuple q).measurable
    e (measurable_of_countable e)
  have hinv := measureLaw_comp_preserving Q (shift (n : ℤ)) (continuous_shift _).measurable
    (shift_nat_preserving Q hQ n) (residueTuple q) (continuous_residueTuple q).measurable
  have hP : stdSimplex.map e P = P := by
    rw [← hmap]
    simpa only [hfun] using hinv
  have hp := map_equiv_apply P e a
  rw [hP, heab] at hp
  exact hp.symm

end Erdos67.StationaryModel
