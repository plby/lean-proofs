import ErdosProblems.Erdos957.Basic

/-!
# The finite counting step in Dumitrescu's proof of Erdős 957

This file isolates the purely combinatorial content of the ``2520 exceptional
vertices'' estimate.  The seven positions in a cyclic window are represented
by seven permutations of an arbitrary finite index type.  This makes the
double-counting argument independent of the eventual polygon encoding.
-/

namespace Erdos957FlatCount

open scoped BigOperators

variable {ι : Type*} [Fintype ι]

/-- Indices at which the exterior turn is at least `threshold`. -/
noncomputable def largeTurnIndices (turn : ι → ℝ) (threshold : ℝ) : Finset ι :=
  Finset.univ.filter fun i ↦ threshold ≤ turn i

/-- Indices whose seven-position window contains a large exterior turn.

The maps `shift j` will later be instantiated by the seven cyclic shifts.
-/
noncomputable def nonflatIndices
    (turn : ι → ℝ) (threshold : ℝ) (shift : Fin 7 → Equiv.Perm ι) : Finset ι :=
  Finset.univ.filter fun i ↦ ∃ j : Fin 7, threshold ≤ turn (shift j i)

theorem card_nonflatIndices_le_seven_mul_card_largeTurnIndices
    (turn : ι → ℝ) (threshold : ℝ) (shift : Fin 7 → Equiv.Perm ι) :
    (nonflatIndices turn threshold shift).card ≤
      7 * (largeTurnIndices turn threshold).card := by
  classical
  let Bad := {i : ι // i ∈ nonflatIndices turn threshold shift}
  let Large := {i : ι // i ∈ largeTurnIndices turn threshold}
  let witness : Bad → Fin 7 := fun i ↦
    Classical.choose (Finset.mem_filter.mp i.property).2
  have hwitness (i : Bad) :
      threshold ≤ turn (shift (witness i) i.1) :=
    Classical.choose_spec (Finset.mem_filter.mp i.property).2
  let encode : Bad → Fin 7 × Large := fun i ↦
    (witness i,
      ⟨shift (witness i) i.1,
        Finset.mem_filter.mpr ⟨Finset.mem_univ _, hwitness i⟩⟩)
  have hencode : Function.Injective encode := by
    intro i k hik
    have hw : witness i = witness k := congrArg Prod.fst hik
    have hs : shift (witness i) i.1 = shift (witness k) k.1 :=
      congrArg (fun p : Fin 7 × Large ↦ p.2.1) hik
    have hs' : shift (witness i) i.1 = shift (witness i) k.1 := by
      simpa only [hw] using hs
    exact Subtype.ext ((shift (witness i)).injective hs')
  have hcard : Fintype.card Bad ≤ Fintype.card (Fin 7 × Large) :=
    Fintype.card_le_of_injective encode hencode
  simpa [Bad, Large, Fintype.card_prod] using hcard

/-- If nonnegative turns sum to `2π`, at most 360 of them can be at least
`π/180`.  No polygon geometry is used here; only the turn-sum identity is an
input. -/
theorem card_largeTurnIndices_le_360
    (turn : ι → ℝ)
    (hnonneg : ∀ i, 0 ≤ turn i)
    (hsum : ∑ i, turn i = 2 * Real.pi) :
    (largeTurnIndices turn (Real.pi / 180)).card ≤ 360 := by
  classical
  let L := largeTurnIndices turn (Real.pi / 180)
  have hpoint : ∀ i ∈ L, Real.pi / 180 ≤ turn i := by
    intro i hi
    exact (Finset.mem_filter.mp hi).2
  have hsubset : L ⊆ Finset.univ := fun _ _ ↦ Finset.mem_univ _
  have hlarge_sum :
      ∑ i ∈ L, Real.pi / 180 ≤ ∑ i ∈ L, turn i :=
    Finset.sum_le_sum fun i hi ↦ hpoint i hi
  have hrestrict : ∑ i ∈ L, turn i ≤ ∑ i, turn i := by
    exact Finset.sum_le_sum_of_subset_of_nonneg hsubset (fun i _ _ ↦ hnonneg i)
  have hreal : ((L.card : ℝ) * (Real.pi / 180)) ≤ 2 * Real.pi := by
    calc
      (L.card : ℝ) * (Real.pi / 180) = ∑ i ∈ L, Real.pi / 180 := by simp
      _ ≤ ∑ i ∈ L, turn i := hlarge_sum
      _ ≤ ∑ i, turn i := hrestrict
      _ = 2 * Real.pi := hsum
  have hpi : 0 < Real.pi := Real.pi_pos
  have hcard_real : (L.card : ℝ) ≤ 360 := by
    nlinarith
  exact_mod_cast hcard_real

/-- The `7 · 360 = 2520` conclusion used in the geometric proof. -/
theorem card_nonflatIndices_le_2520
    (turn : ι → ℝ) (shift : Fin 7 → Equiv.Perm ι)
    (hnonneg : ∀ i, 0 ≤ turn i)
    (hsum : ∑ i, turn i = 2 * Real.pi) :
    (nonflatIndices turn (Real.pi / 180) shift).card ≤ 2520 := by
  calc
    (nonflatIndices turn (Real.pi / 180) shift).card
        ≤ 7 * (largeTurnIndices turn (Real.pi / 180)).card :=
      card_nonflatIndices_le_seven_mul_card_largeTurnIndices turn _ shift
    _ ≤ 7 * 360 := Nat.mul_le_mul_left 7 (card_largeTurnIndices_le_360 turn hnonneg hsum)
    _ = 2520 := by norm_num

/-! ## Concrete cyclic windows -/

/-- Rotation by `j` places in the cyclic index type `Fin m`.  Defining this by
the power of `finRotate` also covers the harmless cases `m < 7`, where window
positions repeat. -/
def cyclicWindowShift (m : ℕ) (j : Fin 7) : Equiv.Perm (Fin m) :=
  (finRotate m) ^ j.1

/-- The nonflat indices for the literal forward seven-position cyclic window. -/
noncomputable def cyclicNonflatIndices (turn : Fin m → ℝ) : Finset (Fin m) :=
  nonflatIndices turn (Real.pi / 180) (cyclicWindowShift m)

theorem card_cyclicNonflatIndices_le_2520
    (turn : Fin m → ℝ)
    (hnonneg : ∀ i, 0 ≤ turn i)
    (hsum : ∑ i, turn i = 2 * Real.pi) :
    (cyclicNonflatIndices turn).card ≤ 2520 := by
  exact card_nonflatIndices_le_2520 turn (cyclicWindowShift m) hnonneg hsum

end Erdos957FlatCount

