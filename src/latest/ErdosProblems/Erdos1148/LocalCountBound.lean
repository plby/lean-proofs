import ErdosProblems.Erdos1148.FlippedRootCounts
import ErdosProblems.Erdos1148.LocalLatticeCount

/-!
# A local lattice-count bound from quadratic congruences

Triangular representatives, the resultant depth bound, and the two root
bounds give a local count with the required half-valuation exponent.
This file handles a first vector whose leading coefficient has minimal
coefficient valuation, expressed as a prime-power multiple with unit lead.
-/

namespace Erdos1148.DukeArithmetic

def padicContainingLattices (p : ℕ) [Fact p.Prime]
    (t u : PadicInt p × PadicInt p × PadicInt p) : Set (Set (Padic p × Padic p × Padic p)) :=
  {L | (∃ g : specialDiscrGroup (Padic p),
      coefficientLattice (algebraMap (PadicInt p) (Padic p)) g = L) ∧
    mapCoeffs (algebraMap (PadicInt p) (Padic p)) t ∈ L ∧
    mapCoeffs (algebraMap (PadicInt p) (Padic p)) u ∈ L}

abbrev ValidPadicChart (p : ℕ) [Fact p.Prime]
    (t u : PadicInt p × PadicInt p × PadicInt p) (n : ℕ) (flipped : Bool) :=
  {z : ZMod (p ^ n) //
    mapCoeffs (algebraMap (PadicInt p) (Padic p)) t ∈ padicChartLattice p n z flipped ∧
    mapCoeffs (algebraMap (PadicInt p) (Padic p)) u ∈ padicChartLattice p n z flipped}

abbrev BoundedPadicCharts (p : ℕ) [Fact p.Prime]
    (t u : PadicInt p × PadicInt p × PadicInt p) :=
  Σ n : Fin ((pairResultant t u).valuation + 1), Σ flipped : Bool, ValidPadicChart p t u n flipped

def chartToContainingLattice (p : ℕ) [Fact p.Prime]
    (t u : PadicInt p × PadicInt p × PadicInt p) (x : BoundedPadicCharts p t u) :
    padicContainingLattices p t u :=
  ⟨padicChartLattice p x.1 x.2.2.1 x.2.1,
    ⟨⟨(padicChartIsometry p x.1 x.2.2.1 x.2.1)⁻¹, rfl⟩, x.2.2.2⟩⟩

theorem chartToContainingLattice_surjective (p : ℕ) [Fact p.Prime]
    (t u : PadicInt p × PadicInt p × PadicInt p) (hres : pairResultant t u ≠ 0) :
    Function.Surjective (chartToContainingLattice p t u) := by
  rintro ⟨L, ⟨g, rfl⟩, ht, hu⟩
  obtain ⟨n, z, flipped, hchart⟩ := exists_padicChartLattice p g
  have ht' := hchart ▸ ht
  have hu' := hchart ▸ hu
  have hn := padicChart_depth_le_of_contains_pair p t u hres n z flipped ht' hu'
  refine ⟨⟨⟨n, by omega⟩, flipped, z, ht', hu'⟩, ?_⟩
  apply Subtype.ext
  exact hchart.symm

theorem finite_padicContainingLattices (p : ℕ) [Fact p.Prime]
    (t u : PadicInt p × PadicInt p × PadicInt p) (hres : pairResultant t u ≠ 0) :
    Finite (padicContainingLattices p t u) :=
  Finite.of_surjective _ (chartToContainingLattice_surjective p t u hres)

lemma card_validPadicChart_false_le (p : ℕ) [Fact p.Prime] (n : ℕ)
    (t u : PadicInt p × PadicInt p × PadicInt p) :
    Nat.card (ValidPadicChart p t u n false) ≤ (quadraticRootResidues p n t).card := by
  let f : ValidPadicChart p t u n false → quadraticRootResidues p n t := fun z =>
    ⟨z.1, (mem_quadraticRootResidues_iff p n t z.1).mpr
      ((mem_padicChartLattice_false p n z.1 t).mp z.2.1)⟩
  have hf : Function.Injective f := by
    intro x y hxy
    have hval := congrArg (fun w : quadraticRootResidues p n t => w.1) hxy
    exact Subtype.ext hval
  simpa only [Nat.card_eq_finsetCard] using Nat.card_le_card_of_injective f hf

lemma card_validPadicChart_true_le (p : ℕ) [Fact p.Prime] (n : ℕ)
    (t u : PadicInt p × PadicInt p × PadicInt p) :
    Nat.card (ValidPadicChart p t u n true) ≤ (quadraticRootResidues p n (flipCoeffs t)).card := by
  let f : ValidPadicChart p t u n true → quadraticRootResidues p n (flipCoeffs t) := fun z =>
    ⟨z.1, (mem_quadraticRootResidues_iff p n (flipCoeffs t) z.1).mpr
      ((mem_padicChartLattice_true p n z.1 t).mp z.2.1)⟩
  have hf : Function.Injective f := by
    intro x y hxy
    have hval := congrArg (fun w : quadraticRootResidues p n (flipCoeffs t) => w.1) hxy
    exact Subtype.ext hval
  simpa only [Nat.card_eq_finsetCard] using Nat.card_le_card_of_injective f hf

theorem card_padicContainingLattices_le_of_scaled_unit (p : ℕ) [Fact p.Prime]
    (r : ℕ) (t u : PadicInt p × PadicInt p × PadicInt p) (ha : IsUnit t.1)
    (hD : discr t ≠ 0) (hres : pairResultant ((p : PadicInt p) ^ r • t) u ≠ 0) :
    Nat.card (padicContainingLattices p ((p : PadicInt p) ^ r • t) u) ≤
      16 * ((pairResultant ((p : PadicInt p) ^ r • t) u).valuation + 1) *
        p ^ ((discr ((p : PadicInt p) ^ r • t)).valuation / 2) := by
  classical
  let v := (p : PadicInt p) ^ r • t
  let C := 8 * p ^ ((discr v).valuation / 2)
  have hlocal (n : ℕ) (flipped : Bool) : Nat.card (ValidPadicChart p v u n flipped) ≤ C := by
    cases flipped with
    | false =>
      exact (card_validPadicChart_false_le p n v u).trans
        (quadraticRootResidues_card_le_of_scaled_unit p n r t ha hD)
    | true =>
      exact (card_validPadicChart_true_le p n v u).trans
        (quadraticRootResidues_flip_card_le_of_scaled_unit p n r t ha hD)
  have hcount : Nat.card (BoundedPadicCharts p v u) ≤
      ((pairResultant v u).valuation + 1) * (2 * C) := by
    rw [Nat.card_sigma]
    calc
      _ ≤ ∑ _ : Fin ((pairResultant v u).valuation + 1), 2 * C := by
        apply Finset.sum_le_sum
        intro n _
        rw [Nat.card_sigma]
        calc
          _ ≤ ∑ _ : Bool, C := Finset.sum_le_sum (fun b _ => hlocal n b)
          _ = 2 * C := by simp
      _ = _ := by simp
  have hsurj := Nat.card_le_card_of_surjective _ (chartToContainingLattice_surjective p v u hres)
  have h := hsurj.trans hcount
  calc
    _ ≤ ((pairResultant v u).valuation + 1) * (2 * C) := h
    _ = _ := by dsimp only [C, v]; ring

end Erdos1148.DukeArithmetic
