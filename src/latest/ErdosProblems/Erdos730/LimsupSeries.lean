/- leanprover/lean4:v4.33.0  mathlib db584cd6 (master, the commit the v4.33.0 tag is cut from) -/
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Topology.Algebra.Order.LiminfLimsup

/-!
# Finite-depth limsup assembly for Erdős 730

The small-prime proof first fixes finitely many digit depths and then sends
the depth cutoff to infinity.  This file isolates that purely topological
passage.  It contains no number-theoretic input.
-/

open Filter
open scoped Topology

namespace Erdos730.LimsupSeries

variable {ι κ : Type*} {f : Filter κ} [f.NeBot]

omit [f.NeBot] in
theorem isBoundedUnder_le_finset_sum
    (s : Finset ι) (u : ι → κ → ℝ)
    (hbdd : ∀ i ∈ s, IsBoundedUnder (· ≤ ·) f (u i)) :
    IsBoundedUnder (· ≤ ·) f (fun x ↦ ∑ i ∈ s, u i x) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simpa using (tendsto_const_nhds (x := (0 : ℝ))).isBoundedUnder_le
  | @insert i s hi ih =>
      have hiBdd := hbdd i (Finset.mem_insert_self i s)
      have hsBdd := ih fun j hj ↦ hbdd j (Finset.mem_insert_of_mem hj)
      simpa [Finset.sum_insert, hi] using! isBoundedUnder_le_add hiBdd hsBdd

theorem limsup_finset_sum_le_sum_limsup
    (s : Finset ι) (u : ι → κ → ℝ)
    (hnonneg : ∀ i ∈ s, ∀ x, 0 ≤ u i x)
    (hbdd : ∀ i ∈ s, IsBoundedUnder (· ≤ ·) f (u i)) :
    limsup (fun x ↦ ∑ i ∈ s, u i x) f ≤
      ∑ i ∈ s, limsup (u i) f := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
      have hiNonneg : ∀ x, 0 ≤ u i x :=
        hnonneg i (Finset.mem_insert_self i s)
      have hiLower : IsBoundedUnder (· ≥ ·) f (u i) := by
        exact isBoundedUnder_of ⟨0, hiNonneg⟩
      have hiBdd := hbdd i (Finset.mem_insert_self i s)
      let rest : κ → ℝ := fun x ↦ ∑ j ∈ s, u j x
      have hrestNonneg : ∀ x, 0 ≤ rest x := by
        intro x
        dsimp only [rest]
        exact Finset.sum_nonneg fun j hj ↦
          hnonneg j (Finset.mem_insert_of_mem hj) x
      have hrestCob : IsCoboundedUnder (· ≤ ·) f rest :=
        isCoboundedUnder_le_of_le f hrestNonneg
      have hrestBdd : IsBoundedUnder (· ≤ ·) f rest := by
        dsimp only [rest]
        exact isBoundedUnder_le_finset_sum s u fun j hj ↦
          hbdd j (Finset.mem_insert_of_mem hj)
      have hadd := limsup_add_le (f := f) (u := u i) (v := rest)
        (h₁ := hiLower) (h₂ := hiBdd)
        (h₃ := hrestCob) (h₄ := hrestBdd)
      have hrest := ih
        (fun j hj ↦ hnonneg j (Finset.mem_insert_of_mem hj))
        (fun j hj ↦ hbdd j (Finset.mem_insert_of_mem hj))
      have hrest' : limsup rest f ≤
          ∑ j ∈ s, limsup (u j) f := by
        simpa only [rest] using hrest
      rw [Finset.sum_insert hi]
      calc
        limsup (fun x ↦ ∑ j ∈ insert i s, u j x) f =
            limsup (u i + rest) f := by
          apply limsup_congr
          exact Eventually.of_forall fun x ↦ by
            simp [rest, hi]
        _ ≤ limsup (u i) f + limsup rest f := hadd
        _ ≤ limsup (u i) f + ∑ j ∈ s, limsup (u j) f := by
          exact add_le_add le_rfl hrest'

variable {term : ℕ → ℝ} {total : κ → ℝ} {band : ℕ → κ → ℝ}
  {tail : ℕ → κ → ℝ}

/-- A finite-depth decomposition with a uniformly vanishing tail turns the
fixed-depth limsup bounds into the corresponding infinite-series bound. -/
theorem limsup_le_tsum_of_finite_depth_and_tail
    (htermNonneg : ∀ r, 0 ≤ term r)
    (htermSum : Summable term)
    (htotalNonneg : ∀ x, 0 ≤ total x)
    (hbandNonneg : ∀ r x, 0 ≤ band r x)
    (hbandBdd : ∀ r, IsBoundedUnder (· ≤ ·) f (band r))
    (hbandLimsup : ∀ r, limsup (band r) f ≤ term r)
    (htailNonneg : ∀ R x, 0 ≤ tail R x)
    (htailBdd : ∀ R, IsBoundedUnder (· ≤ ·) f (tail R))
    (epsilon : ℕ → ℝ)
    (hepsilon : Tendsto epsilon atTop (𝓝 0))
    (htailLimsup : ∀ R, limsup (tail R) f ≤ epsilon R)
    (hdecomp : ∀ R, total ≤ᶠ[f]
      fun x ↦ (∑ r ∈ Finset.range R, band r x) + tail R x) :
    limsup total f ≤ ∑' r, term r := by
  have htotalCob : IsCoboundedUnder (· ≤ ·) f total :=
    isCoboundedUnder_le_of_le f htotalNonneg
  have hboundForall : ∀ R,
      limsup total f ≤ (∑ r ∈ Finset.range R, term r) + epsilon R := by
    intro R
    let partialSum : κ → ℝ := fun x ↦ ∑ r ∈ Finset.range R, band r x
    have hpartialBdd : IsBoundedUnder (· ≤ ·) f partialSum := by
      dsimp only [partialSum]
      exact isBoundedUnder_le_finset_sum (Finset.range R) band
        (fun r _ ↦ hbandBdd r)
    have hpartialLower : IsBoundedUnder (· ≥ ·) f partialSum := by
      exact isBoundedUnder_of ⟨0, fun x ↦ by
        dsimp only [partialSum]
        exact Finset.sum_nonneg fun r _ ↦ hbandNonneg r x⟩
    have htailCob : IsCoboundedUnder (· ≤ ·) f (tail R) :=
      isCoboundedUnder_le_of_le f (htailNonneg R)
    have hrhsBdd : IsBoundedUnder (· ≤ ·) f (partialSum + tail R) :=
      isBoundedUnder_le_add hpartialBdd (htailBdd R)
    have hmono : limsup total f ≤ limsup (partialSum + tail R) f := by
      apply limsup_le_limsup (hdecomp R) htotalCob hrhsBdd
    have hadd : limsup (partialSum + tail R) f ≤
        limsup partialSum f + limsup (tail R) f :=
      limsup_add_le (f := f) (u := partialSum) (v := tail R)
        (h₁ := hpartialLower) (h₂ := hpartialBdd)
        (h₃ := htailCob) (h₄ := htailBdd R)
    have hpartial : limsup partialSum f ≤
        ∑ r ∈ Finset.range R, limsup (band r) f := by
      dsimp only [partialSum]
      exact limsup_finset_sum_le_sum_limsup (Finset.range R) band
        (fun r _ ↦ hbandNonneg r) (fun r _ ↦ hbandBdd r)
    calc
      limsup total f ≤ limsup (partialSum + tail R) f := hmono
      _ ≤ limsup partialSum f + limsup (tail R) f := hadd
      _ ≤ (∑ r ∈ Finset.range R, limsup (band r) f) +
          limsup (tail R) f := add_le_add hpartial le_rfl
      _ ≤ (∑ r ∈ Finset.range R, term r) + epsilon R := by
        exact add_le_add
          (Finset.sum_le_sum fun r _ ↦ hbandLimsup r)
          (htailLimsup R)
  have hpartialLe (R : ℕ) :
      (∑ r ∈ Finset.range R, term r) ≤ ∑' r, term r := by
    exact htermSum.sum_le_tsum (Finset.range R) fun r _ ↦ htermNonneg r
  have heventual : ∀ᶠ R : ℕ in atTop,
      limsup total f ≤ (∑' r, term r) + epsilon R :=
    Eventually.of_forall fun R ↦
      (hboundForall R).trans
        (add_le_add (hpartialLe R) le_rfl)
  have hlimit : Tendsto (fun R : ℕ ↦ (∑' r, term r) + epsilon R)
      atTop (𝓝 (∑' r, term r)) := by
    have hconst : Tendsto (fun _ : ℕ ↦ ∑' r, term r) atTop
        (𝓝 (∑' r, term r)) := tendsto_const_nhds
    simpa only [zero_add, add_zero] using hconst.add hepsilon
  exact ge_of_tendsto hlimit heventual

#print axioms limsup_finset_sum_le_sum_limsup
#print axioms limsup_le_tsum_of_finite_depth_and_tail

end Erdos730.LimsupSeries
