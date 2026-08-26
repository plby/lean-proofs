import ErdosProblems.Erdos486.Periodic
import ErdosProblems.Erdos486.PeriodicCounting
import ErdosProblems.Erdos486.BiasedColoring
import ErdosProblems.Erdos486.BlockInterface
import ErdosProblems.Erdos486.BiasedGeometry

/- Ported to Lean/Mathlib 4.33.0; see README.md for source and modifications. -/
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Deterministic recovery for finitely many biased blocks

For a fixed colouring at every scale, a finite collection of blocks removes
a finite union of periodic cylinder sets.  This file places those cylinders
over one common product period, counts their pullbacks exactly, and obtains
the logarithmic-density recovery estimate used by `DyadicBlockInterface`.
-/

open Filter Set
open scoped BigOperators

namespace Erdos486

noncomputable section

/-- The geometry selected by a fixed family of biased colourings. -/
def biasedColoredGeometryAbove (firstScale : ℕ) (hfirst : 400 ≤ firstScale)
    (c : (j : ℕ) → BiasedColoring j) : DyadicBlockGeometry :=
  biasedGeometryAbove firstScale hfirst
    (fun j m ↦ selectedPrimes j (c j) m)

@[simp]
theorem biasedColoredGeometryAbove_endpoints
    (firstScale : ℕ) (hfirst : 400 ≤ firstScale)
    (c : (j : ℕ) → BiasedColoring j) (j : ℕ) :
    (biasedColoredGeometryAbove firstScale hfirst c).endpoints j =
      biasedEndpoints j := rfl

@[simp]
theorem biasedColoredGeometryAbove_modulus
    (firstScale : ℕ) (hfirst : 400 ≤ firstScale)
    (c : (j : ℕ) → BiasedColoring j) (j m : ℕ) :
    (biasedColoredGeometryAbove firstScale hfirst c).modulus j m =
      colouredModulus j (c j) m := rfl

/-- A common period for all biased blocks indexed by `J`. -/
def finiteBiasedPeriod (J : Finset ℕ) : ℕ :=
  ∏ j ∈ J, biasedPeriod j

theorem finiteBiasedPeriod_pos (J : Finset ℕ) :
    0 < finiteBiasedPeriod J := by
  simp [finiteBiasedPeriod, biasedPeriod_pos]

theorem biasedPeriod_dvd_finiteBiasedPeriod {J : Finset ℕ} {j : ℕ}
    (hj : j ∈ J) : biasedPeriod j ∣ finiteBiasedPeriod J := by
  rw [finiteBiasedPeriod]
  exact Finset.dvd_prod_of_mem (fun i ↦ biasedPeriod i) hj

theorem colouredModulus_dvd_finiteBiasedPeriod
    (c : (j : ℕ) → BiasedColoring j) {J : Finset ℕ} {j m : ℕ}
    (hj : j ∈ J) :
    colouredModulus j (c j) m ∣ finiteBiasedPeriod J :=
  (biasedModulus_dvd_period j (selectedPrimes j (c j) m)).trans
    (biasedPeriod_dvd_finiteBiasedPeriod hj)

/-- Coverage by the `j`th block, evaluated on a natural representative. -/
def IsBiasedCoveredNat (j : ℕ) (c : BiasedColoring j) (n : ℕ) : Prop :=
  IsBiasedCovered j c (n : ZMod (biasedPeriod j))

/-- Covered natural representatives below an arbitrary cutoff. -/
def biasedCoveredNatResidues (j : ℕ) (c : BiasedColoring j) (L : ℕ) :
    Finset ℕ := by
  classical
  exact (Finset.range L).filter (IsBiasedCoveredNat j c)

/-- The natural representatives of the covered residues in one scale period
have exactly the previously defined footprint cardinality. -/
theorem card_biasedCoveredNat_one_period (j : ℕ) (c : BiasedColoring j) :
    (biasedCoveredNatResidues j c (biasedPeriod j)).card =
      biasedFootprintCount j c := by
  letI : NeZero (biasedPeriod j) := ⟨(biasedPeriod_pos j).ne'⟩
  classical
  unfold biasedCoveredNatResidues
  unfold biasedFootprintCount
  refine Finset.card_bij
      (s := (Finset.range (biasedPeriod j)).filter
        (IsBiasedCoveredNat j c))
      (t := (Finset.univ : Finset (ZMod (biasedPeriod j))).filter
        (IsBiasedCovered j c))
      (fun n _hn ↦ (n : ZMod (biasedPeriod j))) ?_ ?_ ?_
  · intro n hn
    rw [Finset.mem_filter] at hn ⊢
    exact ⟨Finset.mem_univ _, hn.2⟩
  · intro a ha b hb hab
    rw [Finset.mem_filter] at ha hb
    change (a : ZMod (biasedPeriod j)) =
      (b : ZMod (biasedPeriod j)) at hab
    have hval := congrArg ZMod.val hab
    rw [ZMod.val_natCast_of_lt (Finset.mem_range.mp ha.1),
      ZMod.val_natCast_of_lt (Finset.mem_range.mp hb.1)] at hval
    exact hval
  · intro z hz
    rw [Finset.mem_filter] at hz
    refine ⟨z.val, ?_, ?_⟩
    · rw [Finset.mem_filter]
      exact ⟨Finset.mem_range.mpr z.val_lt, by
        simpa [IsBiasedCoveredNat, ZMod.natCast_zmod_val] using hz.2⟩
    · exact ZMod.natCast_zmod_val z

/-- Pulling one scale's footprint back to a common multiple preserves its
normalized cardinality exactly. -/
theorem card_biasedCoveredNat_of_dvd (j : ℕ) (c : BiasedColoring j)
    {L : ℕ} (hdiv : biasedPeriod j ∣ L) :
    biasedPeriod j *
        (biasedCoveredNatResidues j c L).card =
      L * biasedFootprintCount j c := by
  classical
  unfold biasedCoveredNatResidues
  let P : ℕ → Prop := IsBiasedCoveredNat j c
  have hperiodic : Function.Periodic P (biasedPeriod j) := by
    intro n
    have hcast :
        ((n + biasedPeriod j : ℕ) : ZMod (biasedPeriod j)) =
          (n : ZMod (biasedPeriod j)) := by
      have hzero :
          ((biasedPeriod j : ℕ) : ZMod (biasedPeriod j)) = 0 :=
        (ZMod.natCast_eq_zero_iff (biasedPeriod j) (biasedPeriod j)).2 dvd_rfl
      rw [Nat.cast_add, hzero, add_zero]
    exact congrArg (IsBiasedCovered j c) hcast
  have hmod :
      ((Finset.range L).filter fun n ↦ P (n % biasedPeriod j)).card =
        ((Finset.range L).filter P).card := by
    apply congrArg Finset.card
    ext n
    simp only [Finset.mem_filter, Finset.mem_range]
    have hp : P (n % biasedPeriod j) ↔ P n := by
      have hcast :
          ((n % biasedPeriod j : ℕ) : ZMod (biasedPeriod j)) =
            (n : ZMod (biasedPeriod j)) := by
        simp
      exact Iff.of_eq (congrArg (IsBiasedCovered j c) hcast)
    tauto
  rw [← hmod]
  rw [card_filter_range_mod_of_dvd P hdiv]
  rw [show ((Finset.range (biasedPeriod j)).filter P).card =
      biasedFootprintCount j c by
    simpa [P, biasedCoveredNatResidues] using
      card_biasedCoveredNat_one_period j c]

/-- The union of all covered residue representatives over the common period. -/
def finiteBiasedCoveredResidues
    (c : (j : ℕ) → BiasedColoring j) (J : Finset ℕ) : Finset ℕ := by
  classical
  exact J.biUnion fun j ↦
    biasedCoveredNatResidues j (c j) (finiteBiasedPeriod J)

/-- Residues in the common period that avoid every selected biased block. -/
def finiteBiasedSafeResidues
    (c : (j : ℕ) → BiasedColoring j) (J : Finset ℕ) : Finset ℕ :=
  Finset.range (finiteBiasedPeriod J) \ finiteBiasedCoveredResidues c J

theorem finiteBiasedCoveredResidues_subset_range
    (c : (j : ℕ) → BiasedColoring j) (J : Finset ℕ) :
    finiteBiasedCoveredResidues c J ⊆
      Finset.range (finiteBiasedPeriod J) := by
  classical
  intro n hn
  rw [finiteBiasedCoveredResidues, Finset.mem_biUnion] at hn
  obtain ⟨j, _hj, hn⟩ := hn
  exact Finset.filter_subset _ _ hn

theorem finiteBiasedCoveredResidues_card_le
    (c : (j : ℕ) → BiasedColoring j) (J : Finset ℕ) :
    (finiteBiasedCoveredResidues c J).card ≤
      ∑ j ∈ J,
        (biasedCoveredNatResidues j (c j) (finiteBiasedPeriod J)).card := by
  classical
  unfold finiteBiasedCoveredResidues
  exact Finset.card_biUnion_le

theorem finiteBiasedSafe_add_covered_card
    (c : (j : ℕ) → BiasedColoring j) (J : Finset ℕ) :
    (finiteBiasedSafeResidues c J).card +
        (finiteBiasedCoveredResidues c J).card = finiteBiasedPeriod J := by
  classical
  let U := finiteBiasedCoveredResidues c J
  let S := finiteBiasedSafeResidues c J
  have hsub : U ⊆ Finset.range (finiteBiasedPeriod J) :=
    finiteBiasedCoveredResidues_subset_range c J
  have hunion : S ∪ U = Finset.range (finiteBiasedPeriod J) := by
    simpa [S, U, finiteBiasedSafeResidues] using
      Finset.sdiff_union_of_subset hsub
  have hdisj : Disjoint S U := by
    rw [Finset.disjoint_left]
    intro n hnS hnU
    exact (Finset.mem_sdiff.mp hnS).2 hnU
  calc
    S.card + U.card = (S ∪ U).card :=
      (Finset.card_union_of_disjoint hdisj).symm
    _ = (Finset.range (finiteBiasedPeriod J)).card := by rw [hunion]
    _ = finiteBiasedPeriod J := Finset.card_range _

/-- Exact normalized pullback count for every scale in a finite family. -/
theorem biasedCoveredNat_ratio_eq_footprint
    (c : (j : ℕ) → BiasedColoring j) {J : Finset ℕ} {j : ℕ}
    (hj : j ∈ J) :
    ((biasedCoveredNatResidues j (c j) (finiteBiasedPeriod J)).card : ℝ) /
        (finiteBiasedPeriod J : ℝ) = biasedFootprint j (c j) := by
  have hL : 0 < finiteBiasedPeriod J := finiteBiasedPeriod_pos J
  have hd : 0 < biasedPeriod j := biasedPeriod_pos j
  have hcrossNat := card_biasedCoveredNat_of_dvd j (c j)
    (biasedPeriod_dvd_finiteBiasedPeriod hj)
  have hcrossReal :
      (biasedPeriod j : ℝ) *
          (biasedCoveredNatResidues j (c j) (finiteBiasedPeriod J)).card =
        (finiteBiasedPeriod J : ℝ) * biasedFootprintCount j (c j) := by
    exact_mod_cast hcrossNat
  rw [biasedFootprint]
  field_simp [ne_of_gt hL, ne_of_gt hd]
  nlinarith

/-- The safe residue density is at least one minus the sum of the individual
biased footprints. -/
theorem one_sub_sum_biasedFootprint_le_safeDensity
    (c : (j : ℕ) → BiasedColoring j) (J : Finset ℕ) :
    1 - (∑ j ∈ J, biasedFootprint j (c j)) ≤
      ((finiteBiasedSafeResidues c J).card : ℝ) /
        (finiteBiasedPeriod J : ℝ) := by
  let L := finiteBiasedPeriod J
  let S := finiteBiasedSafeResidues c J
  let U := finiteBiasedCoveredResidues c J
  let C : ℕ := ∑ j ∈ J,
    (biasedCoveredNatResidues j (c j) L).card
  have hLNat : 0 < L := finiteBiasedPeriod_pos J
  have hUle : U.card ≤ C := by
    simpa [U, C, L] using finiteBiasedCoveredResidues_card_le c J
  have hpartition : S.card + U.card = L := by
    simpa [S, U, L] using finiteBiasedSafe_add_covered_card c J
  have hcoverNat : L ≤ S.card + C := by omega
  have hcoverReal : (L : ℝ) ≤ (S.card : ℝ) + (C : ℝ) := by
    exact_mod_cast hcoverNat
  have hsumRatio :
      (C : ℝ) / (L : ℝ) = ∑ j ∈ J, biasedFootprint j (c j) := by
    calc
      (C : ℝ) / (L : ℝ) =
          (∑ j ∈ J,
            ((biasedCoveredNatResidues j (c j) L).card : ℝ)) / (L : ℝ) := by
            simp [C]
      _ = ∑ j ∈ J,
          ((biasedCoveredNatResidues j (c j) L).card : ℝ) / (L : ℝ) := by
            rw [Finset.sum_div]
      _ = ∑ j ∈ J, biasedFootprint j (c j) := by
            apply Finset.sum_congr rfl
            intro j hj
            simpa [L] using biasedCoveredNat_ratio_eq_footprint c hj
  rw [← hsumRatio]
  change 1 - (C : ℝ) / (L : ℝ) ≤ (S.card : ℝ) / (L : ℝ)
  rw [sub_le_iff_le_add]
  calc
    (1 : ℝ) ≤ ((S.card : ℝ) + (C : ℝ)) / (L : ℝ) := by
      apply (le_div_iff₀ (by exact_mod_cast hLNat)).2
      simpa using hcoverReal
    _ = (S.card : ℝ) / (L : ℝ) + (C : ℝ) / (L : ℝ) := by ring

/-- Unfolding the reduction map identifies coverage with the endpoint
congruence used by `blockResidues`. -/
theorem isBiasedCoveredNat_iff (j : ℕ) (c : BiasedColoring j) (n : ℕ) :
    IsBiasedCoveredNat j c n ↔
      ∃ m ∈ biasedEndpoints j,
        (n : ZMod (colouredModulus j c m)) =
          (m : ZMod (colouredModulus j c m)) := by
  simp [IsBiasedCoveredNat, IsBiasedCovered, reduceBiasedPeriod,
    colouredModulus]

theorem mem_finiteBiasedSafeResidues_iff
    (c : (j : ℕ) → BiasedColoring j) (J : Finset ℕ) (n : ℕ) :
    n ∈ finiteBiasedSafeResidues c J ↔
      n < finiteBiasedPeriod J ∧
        ∀ j ∈ J, ¬IsBiasedCoveredNat j (c j) n := by
  classical
  rw [finiteBiasedSafeResidues, Finset.mem_sdiff, Finset.mem_range]
  constructor
  · rintro ⟨hn, hnot⟩
    refine ⟨hn, ?_⟩
    intro j hj hcovered
    apply hnot
    rw [finiteBiasedCoveredResidues, Finset.mem_biUnion]
    refine ⟨j, hj, ?_⟩
    rw [biasedCoveredNatResidues, Finset.mem_filter]
    exact ⟨Finset.mem_range.mpr hn, hcovered⟩
  · rintro ⟨hn, hsafe⟩
    refine ⟨hn, ?_⟩
    intro hcovered
    rw [finiteBiasedCoveredResidues, Finset.mem_biUnion] at hcovered
    obtain ⟨j, hj, hn⟩ := hcovered
    rw [biasedCoveredNatResidues, Finset.mem_filter] at hn
    exact hsafe j hj hn.2

theorem isBiasedCoveredNat_mod_finiteBiasedPeriod_iff
    (c : (j : ℕ) → BiasedColoring j) {J : Finset ℕ} {j : ℕ}
    (hj : j ∈ J) (n : ℕ) :
    IsBiasedCoveredNat j (c j) (n % finiteBiasedPeriod J) ↔
      IsBiasedCoveredNat j (c j) n := by
  have hcast :
      ((n % finiteBiasedPeriod J : ℕ) : ZMod (biasedPeriod j)) =
        (n : ZMod (biasedPeriod j)) := by
    rw [ZMod.natCast_eq_natCast_iff]
    exact Nat.mod_mod_of_dvd n (biasedPeriod_dvd_finiteBiasedPeriod hj)
  exact Iff.of_eq (congrArg (IsBiasedCovered j (c j)) hcast)

theorem mod_mem_finiteBiasedSafeResidues_iff
    (c : (j : ℕ) → BiasedColoring j) (J : Finset ℕ) (n : ℕ) :
    n % finiteBiasedPeriod J ∈ finiteBiasedSafeResidues c J ↔
      ∀ j ∈ J, ¬IsBiasedCoveredNat j (c j) n := by
  rw [mem_finiteBiasedSafeResidues_iff]
  have hL : 0 < finiteBiasedPeriod J := finiteBiasedPeriod_pos J
  simp only [Nat.mod_lt n hL, true_and]
  constructor
  · intro h j hj hcovered
    exact h j hj ((isBiasedCoveredNat_mod_finiteBiasedPeriod_iff c hj n).2 hcovered)
  · intro h j hj hcovered
    exact h j hj ((isBiasedCoveredNat_mod_finiteBiasedPeriod_iff c hj n).1 hcovered)

/-- Once the cutoff is beyond the common period, every modulus in the finite
block system is active, and survivor membership is exactly avoidance of all
biased block footprints. -/
theorem mem_blockSurvivors_biasedColoredGeometryAbove_iff
    (firstScale : ℕ) (hfirst : 400 ≤ firstScale)
    (c : (j : ℕ) → BiasedColoring j) (J : Finset ℕ) (n : ℕ)
    (hn : finiteBiasedPeriod J < n) :
    n ∈ blockSurvivors (biasedColoredGeometryAbove firstScale hfirst c)
        (J : Set ℕ) ↔
      ∀ j ∈ J, ¬IsBiasedCoveredNat j (c j) n := by
  let G := biasedColoredGeometryAbove firstScale hfirst c
  have hnpos : 0 < n := (finiteBiasedPeriod_pos J).trans hn
  constructor
  · intro hs j hj hcovered
    rw [isBiasedCoveredNat_iff] at hcovered
    obtain ⟨m, hm, hcast⟩ := hcovered
    let q : blockModuli G (J : Set ℕ) :=
      ⟨colouredModulus j (c j) m, by
        refine ⟨j, ?_, m, ?_, ?_⟩
        · simpa using hj
        · simpa [G] using hm
        · simp [G]⟩
    have hqle : (q : ℕ) ≤ finiteBiasedPeriod J :=
      Nat.le_of_dvd (finiteBiasedPeriod_pos J)
        (colouredModulus_dvd_finiteBiasedPeriod c hj)
    have hq_lt_n : (q : ℕ) < n := hqle.trans_lt hn
    apply (hs.2 q hq_lt_n)
    exact ⟨j, by simpa using hj, m, by simpa [G] using hm,
      by simp [q], by simpa [q] using hcast⟩
  · intro hsafe
    refine ⟨hnpos, ?_⟩
    rintro ⟨q, hqmem⟩ _hqn hres
    obtain ⟨j, hj, m, hm, hqm, hcast⟩ := hres
    have hjJ : j ∈ J := by simpa using hj
    have hm' : m ∈ biasedEndpoints j := by simpa [G] using hm
    change colouredModulus j (c j) m = q at hqm
    subst q
    apply hsafe j hjJ
    rw [isBiasedCoveredNat_iff]
    exact ⟨m, hm', hcast⟩

/-- Explicit eventual periodicity of the finite biased survivor system.  The
threshold `L + 1` is what turns the original strict activation `q < n` on for
every modulus dividing the common period `L`. -/
theorem blockSurvivors_biasedColoredGeometryAbove_eventually_periodic
    (firstScale : ℕ) (hfirst : 400 ≤ firstScale)
    (c : (j : ℕ) → BiasedColoring j) (J : Finset ℕ) :
    ∀ n, finiteBiasedPeriod J + 1 ≤ n →
      (n ∈ blockSurvivors
          (biasedColoredGeometryAbove firstScale hfirst c) (J : Set ℕ) ↔
        n % finiteBiasedPeriod J ∈ finiteBiasedSafeResidues c J) := by
  intro n hn
  have hperiod_lt : finiteBiasedPeriod J < n := by omega
  rw [mem_blockSurvivors_biasedColoredGeometryAbove_iff
    firstScale hfirst c J n hperiod_lt]
  exact (mod_mem_finiteBiasedSafeResidues_iff c J n).symm

/-- The finite biased block system has logarithmic density equal to its safe
residue proportion in the common product period. -/
theorem hasLogDensity_blockSurvivors_biasedColoredGeometryAbove
    (firstScale : ℕ) (hfirst : 400 ≤ firstScale)
    (c : (j : ℕ) → BiasedColoring j) (J : Finset ℕ) :
    HasLogDensity
      (blockSurvivors (biasedColoredGeometryAbove firstScale hfirst c)
        (J : Set ℕ))
      (((finiteBiasedSafeResidues c J).card : ℝ) /
        (finiteBiasedPeriod J : ℝ)) := by
  apply hasLogDensity_of_eventually_periodic
      (blockSurvivors (biasedColoredGeometryAbove firstScale hfirst c)
        (J : Set ℕ))
      (finiteBiasedSafeResidues c J)
      (finiteBiasedPeriod J)
      (finiteBiasedPeriod J + 1)
      (finiteBiasedPeriod_pos J)
  · intro r hr
    exact (mem_finiteBiasedSafeResidues_iff c J r).mp hr |>.1
  · intro n hn
    exact hn.1
  · exact blockSurvivors_biasedColoredGeometryAbove_eventually_periodic
      firstScale hfirst c J

/-- The deterministic finite-past recovery statement in exactly the shape of
`DyadicBlockInterface.finite_recovery`. -/
theorem biasedColored_finite_recovery
    (firstScale : ℕ) (hfirst : 400 ≤ firstScale)
    (c : (j : ℕ) → BiasedColoring j) (J : Finset ℕ) :
    ∃ d : ℝ,
      Tendsto
          (logAverage
            (blockSurvivors
              (biasedColoredGeometryAbove firstScale hfirst c) (J : Set ℕ)))
          atTop (nhds d) ∧
        1 - (∑ j ∈ J, biasedFootprint j (c j)) ≤ d := by
  refine ⟨((finiteBiasedSafeResidues c J).card : ℝ) /
      (finiteBiasedPeriod J : ℝ), ?_,
    one_sub_sum_biasedFootprint_le_safeDensity c J⟩
  exact hasLogDensity_blockSurvivors_biasedColoredGeometryAbove
    firstScale hfirst c J

end

end Erdos486
