/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Residue points of the diagonal sextic and their determinant contribution.
Formal author: Codex.
-/

import ErdosProblems.Erdos477.Counting.PadicDeterminant

namespace Erdos477.Counting

/-- The affine diagonal sextic points modulo `p`. -/
def sexticResidues (p : ℕ) [NeZero p] (c : ℤ) : Finset (Fin 3 → ZMod p) :=
  Finset.univ.filter (fun z => z 0 ^ 6 + z 1 ^ 6 - z 2 ^ 6 = (c : ZMod p))

@[simp] lemma mem_sexticResidues (p : ℕ) [NeZero p] (c : ℤ) (z : Fin 3 → ZMod p) :
    z ∈ sexticResidues p c ↔ z 0 ^ 6 + z 1 ^ 6 - z 2 ^ 6 = (c : ZMod p) := by
  simp only [sexticResidues, Finset.mem_filter, Finset.mem_univ, true_and]

/-- A count defined for all natural moduli, for use in sums over primes. -/
noncomputable def residueCount (p : ℕ) (c : ℤ) : ℕ :=
  Nat.card {z : Fin 3 → ZMod p // z 0 ^ 6 + z 1 ^ 6 - z 2 ^ 6 = (c : ZMod p)}

lemma residueCount_eq (p : ℕ) [NeZero p] (c : ℤ) :
    residueCount p c = (sexticResidues p c).card := by
  simp only [residueCount, Nat.card_eq_fintype_card, Fintype.card_subtype, sexticResidues]

lemma residueCount_pos_of_point (p : ℕ) [NeZero p] (c : ℤ) (z : Fin 3 → ℤ)
    (hz : z 0 ^ 6 + z 1 ^ 6 - z 2 ^ 6 = c) : 0 < residueCount p c := by
  rw [residueCount_eq, Finset.card_pos]
  refine ⟨(fun k => (z k : ZMod p)), ?_⟩
  rw [mem_sexticResidues]
  simpa only [Int.cast_sub, Int.cast_add, Int.cast_pow] using
    congrArg (fun n : ℤ => (n : ZMod p)) hz

/-- No residue-class data are needed as hypotheses: reducing the integral
points modulo `p` and choosing occupied representatives supplies them. -/
theorem pow_dvd_sextic_eval_det_all {s : ℕ} (p : ℕ) [Fact p.Prime]
    (h6 : p.Coprime 6) (c : ℤ) (hc : ¬ (p : ℤ) ∣ c)
    (z : Fin s → Fin 3 → ℤ) (hz : ∀ j, z j 0 ^ 6 + z j 1 ^ 6 - z j 2 ^ 6 = c)
    (F : Fin s → MvPolynomial (Fin 3) ℤ) (m : ℕ) :
    (p : ℤ) ^ residueExponent (sexticResidues p c).card s m ∣
      Matrix.det (Matrix.of fun i j => MvPolynomial.eval (z j) (F i)) := by
  classical
  let red : Fin s → Fin 3 → ZMod p := fun j k => (z j k : ZMod p)
  let S : Finset (Fin 3 → ZMod p) := Finset.univ.image red
  have hpre (t : S) : ∃ j, red j = t.val := by
    obtain ⟨j, _, hj⟩ := Finset.mem_image.mp t.property
    exact ⟨j, hj⟩
  choose idx hidx using hpre
  let g : Fin s → S := fun j => ⟨red j, Finset.mem_image.mpr ⟨j, Finset.mem_univ j, rfl⟩⟩
  let center : S → Fin 3 → ℤ := fun t => z (idx t)
  have hres (j k) : (p : ℤ) ∣ z j k - center (g j) k := by
    apply (ZMod.intCast_eq_intCast_iff_dvd_sub (center (g j) k) (z j k) p).mp
    exact congrFun (hidx (g j)) k
  have h := pow_dvd_sextic_eval_det_residues p h6 c hc center
    (fun t => hz (idx t)) g z hres hz F m
  have hsub : S ⊆ sexticResidues p c := by
    intro t ht
    obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp ht
    rw [mem_sexticResidues]
    dsimp only [red]
    simpa only [Int.cast_sub, Int.cast_add, Int.cast_pow] using
      congrArg (fun n : ℤ => (n : ZMod p)) (hz j)
  have hcard : Fintype.card S ≤ (sexticResidues p c).card := by
    simpa only [Fintype.card_coe] using Finset.card_le_card hsub
  exact (pow_dvd_pow (p : ℤ) (residueExponent_antitone hcard s m)).trans h

#print axioms pow_dvd_sextic_eval_det_all
-- 'Erdos477.Counting.pow_dvd_sextic_eval_det_all' depends on axioms:
-- [propext, Classical.choice, Quot.sound]

end Erdos477.Counting
