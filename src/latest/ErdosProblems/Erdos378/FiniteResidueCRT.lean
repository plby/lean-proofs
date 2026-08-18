/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos387.LocalDensity

/-!
# Finite CRT products of variable residue sets

This file packages the exact finite counting statement needed by the
low-index sieve for Erdős 378.  The local modulus and the local residue set
may both depend on the index.  The resulting simultaneous residue set has
cardinality equal to the product of the local cardinalities, and counting it
in an initial interval has the usual one-period endpoint error.
-/

open scoped BigOperators

namespace Erdos378
namespace FiniteResidueCRT

noncomputable section

variable {ι : Type*} [DecidableEq ι]

/-- A choice of one allowed residue at every index of `I`. -/
def Assignment (I : Finset ι) (A : ι → Finset ℕ) :=
  (i : ↑I) → {a : ℕ // a ∈ A i}

instance (I : Finset ι) (A : ι → Finset ℕ) :
    Fintype (Assignment I A) := by
  unfold Assignment
  infer_instance

instance (I : Finset ι) (A : ι → Finset ℕ) :
    DecidableEq (Assignment I A) := Classical.decEq _

/-- The canonical simultaneous residue of an assignment. -/
def assignmentResidue (I : Finset ι) (q : ι → ℕ) (A : ι → Finset ℕ)
    (hq : ∀ i ∈ I, q i ≠ 0)
    (hcop : ∀ i ∈ I, ∀ j ∈ I, i ≠ j → Nat.Coprime (q i) (q j))
    (a : Assignment I A) : ℕ :=
  Nat.chineseRemainderOfFinset
    (fun i : ↑I ↦ (a i : ℕ)) (fun i : ↑I ↦ q i) Finset.univ
    (by intro i _; exact hq i i.property)
    (by
      intro i _ j _ hij
      exact hcop i i.property j j.property (fun h ↦ hij (Subtype.ext h)))

lemma assignmentResidue_mod
    (I : Finset ι) (q : ι → ℕ) (A : ι → Finset ℕ)
    (hq : ∀ i ∈ I, q i ≠ 0)
    (hcop : ∀ i ∈ I, ∀ j ∈ I, i ≠ j → Nat.Coprime (q i) (q j))
    (a : Assignment I A) (i : ↑I) :
    assignmentResidue I q A hq hcop a ≡ (a i : ℕ) [MOD q i] := by
  exact (Nat.chineseRemainderOfFinset
    (fun i : ↑I ↦ (a i : ℕ)) (fun i : ↑I ↦ q i) Finset.univ
    (by intro j _; exact hq j j.property)
    (by
      intro j _ l _ hjl
      exact hcop j j.property l l.property
        (fun h ↦ hjl (Subtype.ext h)))).prop i (Finset.mem_univ i)

lemma assignmentResidue_lt_prod
    (I : Finset ι) (q : ι → ℕ) (A : ι → Finset ℕ)
    (hq : ∀ i ∈ I, q i ≠ 0)
    (hcop : ∀ i ∈ I, ∀ j ∈ I, i ≠ j → Nat.Coprime (q i) (q j))
    (a : Assignment I A) :
    assignmentResidue I q A hq hcop a < ∏ i ∈ I, q i := by
  have h := Nat.chineseRemainderOfFinset_lt_prod
    (fun i : ↑I ↦ (a i : ℕ)) (fun i : ↑I ↦ q i) (t := Finset.univ)
    (by intro i _; exact hq i i.property)
    (by
      intro i _ j _ hij
      exact hcop i i.property j j.property
        (fun e ↦ hij (Subtype.ext e)))
  change assignmentResidue I q A hq hcop a <
    ∏ i : ↑I, q i at h
  rw [show (∏ i : ↑I, q i) = ∏ i ∈ I, q i by
    simpa using Finset.prod_attach I q] at h
  exact h

lemma assignmentResidue_injective
    (I : Finset ι) (q : ι → ℕ) (A : ι → Finset ℕ)
    (hq : ∀ i ∈ I, q i ≠ 0)
    (hcop : ∀ i ∈ I, ∀ j ∈ I, i ≠ j → Nat.Coprime (q i) (q j))
    (hA : ∀ i ∈ I, ∀ a ∈ A i, a < q i) :
    Function.Injective (assignmentResidue I q A hq hcop) := by
  intro a b hab
  funext i
  apply Subtype.ext
  have ha := assignmentResidue_mod I q A hq hcop a i
  have hb := assignmentResidue_mod I q A hq hcop b i
  have halt : (a i : ℕ) < q i := hA i i.property _ (a i).property
  have hblt : (b i : ℕ) < q i := hA i i.property _ (b i).property
  have hma := Nat.mod_eq_of_modEq ha halt
  have hmb := Nat.mod_eq_of_modEq hb hblt
  rw [hab] at hma
  omega

/-- The finite set of simultaneous CRT representatives. -/
def residueSet (I : Finset ι) (q : ι → ℕ) (A : ι → Finset ℕ)
    (hq : ∀ i ∈ I, q i ≠ 0)
    (hcop : ∀ i ∈ I, ∀ j ∈ I, i ≠ j → Nat.Coprime (q i) (q j)) :
    Finset ℕ :=
  Finset.univ.image (assignmentResidue I q A hq hcop)

lemma card_residueSet
    (I : Finset ι) (q : ι → ℕ) (A : ι → Finset ℕ)
    (hq : ∀ i ∈ I, q i ≠ 0)
    (hcop : ∀ i ∈ I, ∀ j ∈ I, i ≠ j → Nat.Coprime (q i) (q j))
    (hA : ∀ i ∈ I, ∀ a ∈ A i, a < q i) :
    (residueSet I q A hq hcop).card = ∏ i ∈ I, (A i).card := by
  classical
  unfold residueSet
  rw [Finset.card_image_of_injective _
    (assignmentResidue_injective I q A hq hcop hA), Finset.card_univ]
  unfold Assignment
  rw [Fintype.card_pi]
  simp only [Fintype.card_coe]
  simpa using Finset.prod_attach I (fun i ↦ (A i).card)

lemma residueSet_lt
    (I : Finset ι) (q : ι → ℕ) (A : ι → Finset ℕ)
    (hq : ∀ i ∈ I, q i ≠ 0)
    (hcop : ∀ i ∈ I, ∀ j ∈ I, i ≠ j → Nat.Coprime (q i) (q j)) :
    ∀ r ∈ residueSet I q A hq hcop, r < ∏ i ∈ I, q i := by
  intro r hr
  obtain ⟨a, _ha, rfl⟩ := Finset.mem_image.mp hr
  exact assignmentResidue_lt_prod I q A hq hcop a

lemma mod_mem_residueSet_iff
    (I : Finset ι) (q : ι → ℕ) (A : ι → Finset ℕ)
    (hq : ∀ i ∈ I, q i ≠ 0)
    (hcop : ∀ i ∈ I, ∀ j ∈ I, i ≠ j → Nat.Coprime (q i) (q j))
    (hA : ∀ i ∈ I, ∀ a ∈ A i, a < q i) (n : ℕ) :
    n % (∏ i ∈ I, q i) ∈ residueSet I q A hq hcop ↔
      ∀ i ∈ I, n % q i ∈ A i := by
  classical
  let Q := ∏ i ∈ I, q i
  have hQ : 0 < Q := by
    dsimp only [Q]
    exact Finset.prod_pos fun i hi ↦ Nat.pos_of_ne_zero (hq i hi)
  constructor
  · intro hn i hi
    obtain ⟨a, _ha, hna⟩ := Finset.mem_image.mp hn
    let i' : ↑I := ⟨i, hi⟩
    have hnQ : n ≡ assignmentResidue I q A hq hcop a [MOD Q] := by
      change n % Q = assignmentResidue I q A hq hcop a % Q
      rw [Nat.mod_eq_of_lt (assignmentResidue_lt_prod I q A hq hcop a)]
      exact hna.symm
    have hqi : q i ∣ Q := by
      dsimp only [Q]
      exact Finset.dvd_prod_of_mem q hi
    have hlocal := (hnQ.of_dvd hqi).trans
      (assignmentResidue_mod I q A hq hcop a i')
    have hlt := hA i hi (a i') (a i').property
    have heq := Nat.mod_eq_of_modEq hlocal hlt
    simpa [heq] using (a i').property
  · intro hn
    let a : Assignment I A := fun i ↦
      ⟨n % q i, hn i i.property⟩
    apply Finset.mem_image.mpr
    refine ⟨a, Finset.mem_univ _, ?_⟩
    symm
    apply Nat.mod_eq_of_modEq
    · let l := I.toList
      have hl : l.Pairwise (Function.onFun Nat.Coprime q) := by
        have hn := Finset.nodup_toList I
        apply hn.pairwise_of_forall_ne
        intro i hi j hj hij
        apply hcop i (by simpa [l] using hi) j (by simpa [l] using hj) hij
      have hm : n ≡ assignmentResidue I q A hq hcop a
          [MOD (l.map q).prod] := by
        apply (Nat.modEq_list_map_prod_iff hl).mpr
        intro i hi
        let i' : ↑I := ⟨i, by simpa [l] using hi⟩
        exact (Nat.mod_modEq n (q i)).symm.trans
          (assignmentResidue_mod I q A hq hcop a i').symm
      simpa [l] using hm
    · exact assignmentResidue_lt_prod I q A hq hcop a

/-- Exact endpoint-error estimate for a simultaneous family of local
conditions. -/
theorem abs_card_simultaneous_sub_density
    (I : Finset ι) (q : ι → ℕ) (A : ι → Finset ℕ)
    (hq : ∀ i ∈ I, q i ≠ 0)
    (hcop : ∀ i ∈ I, ∀ j ∈ I, i ≠ j → Nat.Coprime (q i) (q j))
    (hA : ∀ i ∈ I, ∀ a ∈ A i, a < q i) (N : ℕ) :
    let simultaneous := (Finset.range N).filter fun n ↦
      ∀ i ∈ I, n % q i ∈ A i
    |(simultaneous.card : ℝ) -
        (N : ℝ) * (∏ i ∈ I, ((A i).card : ℝ) / q i)| ≤
      ∏ i ∈ I, (A i).card := by
  classical
  dsimp only
  let Q := ∏ i ∈ I, q i
  let R := residueSet I q A hq hcop
  have hQ : 0 < Q := by
    dsimp only [Q]
    exact Finset.prod_pos fun i hi ↦ Nat.pos_of_ne_zero (hq i hi)
  have heq : (Finset.range N).filter (fun n ↦
      ∀ i ∈ I, n % q i ∈ A i) = Erdos387.modularPreimage N Q R := by
    ext n
    simp only [Erdos387.modularPreimage, Finset.mem_filter, Finset.mem_range,
      and_congr_right_iff]
    intro _hn
    exact (mod_mem_residueSet_iff I q A hq hcop hA n).symm
  have hcount := Erdos387.abs_card_modularPreimage_sub_density (X := N) hQ R
    (residueSet_lt I q A hq hcop)
  rw [← heq, card_residueSet I q A hq hcop hA] at hcount
  have hratio :
      (∏ i ∈ I, ((A i).card : ℝ) / q i) =
        ((∏ i ∈ I, (A i).card : ℕ) : ℝ) / Q := by
    rw [Finset.prod_div_distrib]
    dsimp only [Q]
    push_cast
    rfl
  rw [hratio]
  have hmain :
      (((∏ i ∈ I, (A i).card : ℕ) : ℝ) * (N : ℝ)) / Q =
        (N : ℝ) * (((∏ i ∈ I, (A i).card : ℕ) : ℝ) / Q) := by ring
  rw [← hmain]
  simpa only [Nat.cast_prod] using hcount

end

end FiniteResidueCRT
end Erdos378
