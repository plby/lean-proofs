/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Copyright 2026 The Formal Conjectures Authors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/

import ErdosProblems.Erdos1165.Clock
import Mathlib.Analysis.PSeries

/-!
# Assembly of the HLOZ four-favorite upper bound

This file contains only the last, formal assembly of the upper bound.  The
analytic and Markov estimates from the paper are parameters of the theorems
below; none is asserted for planar random walk here.

The checked implication is the following.

* A first transition has cost at most `q m`.
* Each of the next two transitions has relative cost at most `q m`.
* Three gap scales range over a fixed finite mesh.
* Exceptional events have summable probabilities and `q m ^ 3` has a
  summable `p`-series envelope.
* The six domino tilings cover every configuration of four distinct favorite
  sites.

These inputs imply summability of `P(M_m^4)`.  First Borel--Cantelli then says
that only finitely many `M_m^4` occur, and the clock identity in `Clock.lean`
turns this into the eventual bound `favoriteCount <= 3`.
-/

open Filter MeasureTheory ProbabilityTheory Set
open scoped ENNReal

namespace Erdos1165
namespace UpperAssembly

/-- The finite index of the six HLOZ domino tilings.  Their geometric
construction and the proof that they cover four distinct lattice points are
upstream inputs to this assembly module. -/
abbrev UpperTiling := Fin 6

/-! ## Three gap scales in a finite mesh -/

/-- The three entries record the mesh bins of the three successive gaps
between four candidate favorite sites. -/
def meshTriples {Scale : Type*} (mesh : Finset Scale) :
    Finset ((Scale × Scale) × Scale) :=
  (mesh ×ˢ mesh) ×ˢ mesh

@[simp] theorem card_meshTriples {Scale : Type*} (mesh : Finset Scale) :
    (meshTriples mesh).card = mesh.card ^ 3 := by
  simp [meshTriples, pow_succ, mul_assoc]

/-- Union of all terminal branches obtained by assigning each of the three
gaps to a bin of the finite scale mesh. -/
def meshBranchUnion {Omega Scale : Type*} (mesh : Finset Scale)
    (branch : ((Scale × Scale) × Scale) → Set Omega) : Set Omega :=
  ⋃ a ∈ meshTriples mesh, branch a

@[simp] theorem mem_meshBranchUnion {Omega Scale : Type*} {mesh : Finset Scale}
    {branch : ((Scale × Scale) × Scale) → Set Omega} {omega : Omega} :
    omega ∈ meshBranchUnion mesh branch ↔
      ∃ a ∈ meshTriples mesh, omega ∈ branch a := by
  simp [meshBranchUnion]

/-! ## Multiplication of the three transition costs -/

/-- Three successive transition estimates multiply.  The second and third
hypotheses are deliberately stated as measure inequalities, so this lemma
does not silently assume independence or a Markov property.  In the HLOZ
proof those inequalities are supplied by successive strong-Markov and
screening estimates. -/
theorem measure_thirdStage_le_cube
    {Omega : Type*} [MeasurableSpace Omega] (mu : Measure Omega)
    {firstStage secondStage thirdStage : Set Omega} {q : ENNReal}
    (hfirst : mu firstStage ≤ q)
    (hsecond : mu secondStage ≤ q * mu firstStage)
    (hthird : mu thirdStage ≤ q * mu secondStage) :
    mu thirdStage ≤ q ^ 3 := by
  calc
    mu thirdStage ≤ q * mu secondStage := hthird
    _ ≤ q * (q * mu firstStage) := by gcongr
    _ ≤ q * (q * q) :=
      by gcongr
    _ = q ^ 3 := by simp [pow_succ, mul_assoc]

/-- Finite subadditivity over all three-bin assignments. -/
theorem measure_meshBranchUnion_le_card_mul
    {Omega Scale : Type*} [MeasurableSpace Omega] (mu : Measure Omega)
    (mesh : Finset Scale) (branch : ((Scale × Scale) × Scale) → Set Omega)
    (q : ENNReal)
    (hbranch : ∀ a ∈ meshTriples mesh, mu (branch a) ≤ q) :
    mu (meshBranchUnion mesh branch) ≤
      ((meshTriples mesh).card : ENNReal) * q := by
  rw [meshBranchUnion]
  calc
    mu (⋃ a ∈ meshTriples mesh, branch a) ≤
        ∑ a ∈ meshTriples mesh, mu (branch a) :=
      measure_biUnion_finset_le (meshTriples mesh) branch
    _ ≤ ∑ _a ∈ meshTriples mesh, q :=
      Finset.sum_le_sum fun a ha ↦ hbranch a ha
    _ = ((meshTriples mesh).card : ENNReal) * q := by simp

/-- One tiling and one level: the exceptional event plus the finite mesh of
three-transition branches has the expected union-bound cost. -/
theorem measure_screenedLevel_le
    {Omega Scale : Type*} [MeasurableSpace Omega] (mu : Measure Omega)
    (mesh : Finset Scale) (screened exceptional : Set Omega)
    (firstStage secondStage thirdStage : ((Scale × Scale) × Scale) → Set Omega)
    (q : ENNReal)
    (hcover : screened ⊆ exceptional ∪ meshBranchUnion mesh thirdStage)
    (hfirst : ∀ a ∈ meshTriples mesh, mu (firstStage a) ≤ q)
    (hsecond : ∀ a ∈ meshTriples mesh,
      mu (secondStage a) ≤ q * mu (firstStage a))
    (hthird : ∀ a ∈ meshTriples mesh,
      mu (thirdStage a) ≤ q * mu (secondStage a)) :
    mu screened ≤
      mu exceptional + ((meshTriples mesh).card : ENNReal) * q ^ 3 := by
  have hbranches : mu (meshBranchUnion mesh thirdStage) ≤
      ((meshTriples mesh).card : ENNReal) * q ^ 3 := by
    apply measure_meshBranchUnion_le_card_mul mu mesh thirdStage (q ^ 3)
    intro a ha
    exact measure_thirdStage_le_cube mu (hfirst a ha) (hsecond a ha) (hthird a ha)
  calc
    mu screened ≤ mu (exceptional ∪ meshBranchUnion mesh thirdStage) :=
      measure_mono hcover
    _ ≤ mu exceptional + mu (meshBranchUnion mesh thirdStage) :=
      measure_union_le _ _
    _ ≤ mu exceptional + ((meshTriples mesh).card : ENNReal) * q ^ 3 :=
      add_le_add (le_refl _) hbranches

/-! ## The summable power envelope -/

/-- The shifted real `p`-series, embedded into `ENNReal`.  The shift removes
the singular term at level zero. -/
noncomputable def pSeriesWeight (p : Real) (m : Nat) : ENNReal :=
  ENNReal.ofReal (1 / |(m : Real) + 1| ^ p)

theorem tsum_pSeriesWeight_ne_top {p : Real} (hp : 1 < p) :
    ∑' m, pSeriesWeight p m ≠ ∞ := by
  have hs : Summable (fun m : Nat ↦ 1 / |(m : Real) + 1| ^ p) :=
    (Real.summable_one_div_nat_add_rpow 1 p).2 hp
  exact hs.tsum_ofReal_ne_top

/-- The numerical inequality used by HLOZ: a one-transition exponent
`kappa > 1/3` makes the product of three transition costs summable. -/
theorem one_lt_three_mul_of_one_third_lt {kappa : Real}
    (hkappa : (1 : Real) / 3 < kappa) : 1 < 3 * kappa := by
  linarith

/-- Summability for a single tiling.  The earlier analytic work is visible in
exactly four hypotheses: the mesh cover, the three transition bounds, the
summable exceptional family, and the power envelope for the cubed cost. -/
theorem screenedLevel_series_ne_top
    {Omega Scale : Type*} [MeasurableSpace Omega] (mu : Measure Omega)
    (mesh : Finset Scale)
    (screened exceptional : Nat → Set Omega)
    (firstStage secondStage thirdStage :
      Nat → ((Scale × Scale) × Scale) → Set Omega)
    (q : Nat → ENNReal) (C : NNReal) (p : Real)
    (hp : 1 < p)
    (hcover : ∀ m, screened m ⊆
      exceptional m ∪ meshBranchUnion mesh (thirdStage m))
    (hfirst : ∀ m a, a ∈ meshTriples mesh → mu (firstStage m a) ≤ q m)
    (hsecond : ∀ m a, a ∈ meshTriples mesh →
      mu (secondStage m a) ≤ q m * mu (firstStage m a))
    (hthird : ∀ m a, a ∈ meshTriples mesh →
      mu (thirdStage m a) ≤ q m * mu (secondStage m a))
    (hexception : ∑' m, mu (exceptional m) ≠ ∞)
    (hpower : ∀ m, q m ^ 3 ≤ (C : ENNReal) * pSeriesWeight p m) :
    ∑' m, mu (screened m) ≠ ∞ := by
  let D : ENNReal := ((meshTriples mesh).card : ENNReal) * (C : ENNReal)
  have hpoint : ∀ m, mu (screened m) ≤
      mu (exceptional m) + D * pSeriesWeight p m := by
    intro m
    refine (measure_screenedLevel_le mu mesh (screened m) (exceptional m)
      (firstStage m) (secondStage m) (thirdStage m) (q m)
      (hcover m) (hfirst m) (hsecond m) (hthird m)).trans ?_
    apply add_le_add (le_refl _)
    calc
      ((meshTriples mesh).card : ENNReal) * q m ^ 3 ≤
          ((meshTriples mesh).card : ENNReal) *
            ((C : ENNReal) * pSeriesWeight p m) :=
        mul_le_mul_right (hpower m) _
      _ = D * pSeriesWeight p m := by
        simp only [D, mul_assoc]
  have hmajor : ∑' m,
      (mu (exceptional m) + D * pSeriesWeight p m) ≠ ∞ := by
    rw [ENNReal.tsum_add, ENNReal.tsum_mul_left]
    have hD : D ≠ ∞ := by
      exact ENNReal.mul_ne_top (by simp) ENNReal.coe_ne_top
    exact ENNReal.add_ne_top.mpr
      ⟨hexception, ENNReal.mul_ne_top hD (tsum_pSeriesWeight_ne_top hp)⟩
  exact ne_top_of_le_ne_top hmajor (ENNReal.tsum_le_tsum hpoint)

/-! ## Six tilings and `M_m^4` -/

/-- Summability passes through a cover by six event families.  This is the
finite union and interchange of sums; it makes no geometric assertion about
which events provide the cover. -/
theorem level_series_ne_top_of_six_cover
    {Omega : Type*} [MeasurableSpace Omega] (mu : Measure Omega)
    {bad : Nat → Set Omega} {screened : UpperTiling → Nat → Set Omega}
    (hcover : ∀ m, bad m ⊆ ⋃ t, screened t m)
    (hscreened : ∀ t, ∑' m, mu (screened t m) ≠ ∞) :
    ∑' m, mu (bad m) ≠ ∞ := by
  have hpoint : ∀ m, mu (bad m) ≤ ∑ t, mu (screened t m) := by
    intro m
    calc
      mu (bad m) ≤ mu (⋃ t, screened t m) := measure_mono (hcover m)
      _ ≤ ∑' t, mu (screened t m) := measure_iUnion_le _
      _ = ∑ t, mu (screened t m) := tsum_fintype _
  have hle : (∑' m, mu (bad m)) ≤ ∑' m, ∑ t, mu (screened t m) :=
    ENNReal.summable.tsum_le_tsum hpoint ENNReal.summable
  have hswap : (∑' m, ∑ t, mu (screened t m)) =
      ∑ t, ∑' m, mu (screened t m) := by
    simpa only [Finset.sum_attach, Finset.mem_univ, forall_const] using
      (Summable.tsum_finsetSum
        (s := Finset.univ)
        (f := fun t m ↦ mu (screened t m))
        (fun _ _ ↦ ENNReal.summable))
  rw [hswap] at hle
  apply ne_top_of_le_ne_top _ hle
  simp [hscreened]

/-- Complete finite-mesh/six-tiling summability assembly.  The transition and
covering hypotheses are generic: proving them for the canonical walk is the
remaining analytic content of the HLOZ upper bound, not a conclusion of this
file. -/
theorem levelFavorite_four_series_ne_top_of_three_transitions
    {Scale : Type*} (mu : Measure WalkPath) (mesh : Finset Scale)
    (screened exceptional : UpperTiling → Nat → Set WalkPath)
    (firstStage secondStage thirdStage :
      UpperTiling → Nat → ((Scale × Scale) × Scale) → Set WalkPath)
    (q : Nat → ENNReal) (C : NNReal) (p : Real)
    (hp : 1 < p)
    (hsix : ∀ m, levelFavoriteSet m 4 ⊆ ⋃ t, screened t m)
    (hmesh : ∀ t m, screened t m ⊆
      exceptional t m ∪ meshBranchUnion mesh (thirdStage t m))
    (hfirst : ∀ t m a, a ∈ meshTriples mesh →
      mu (firstStage t m a) ≤ q m)
    (hsecond : ∀ t m a, a ∈ meshTriples mesh →
      mu (secondStage t m a) ≤ q m * mu (firstStage t m a))
    (hthird : ∀ t m a, a ∈ meshTriples mesh →
      mu (thirdStage t m a) ≤ q m * mu (secondStage t m a))
    (hexception : ∀ t, ∑' m, mu (exceptional t m) ≠ ∞)
    (hpower : ∀ m, q m ^ 3 ≤ (C : ENNReal) * pSeriesWeight p m) :
    ∑' m, mu (levelFavoriteSet m 4) ≠ ∞ := by
  have hscreened : ∀ t, ∑' m,
      mu (screened t m) ≠ ∞ := by
    intro t
    exact screenedLevel_series_ne_top mu mesh
      (screened t) (exceptional t)
      (firstStage t) (secondStage t) (thirdStage t) q C p hp
      (hmesh t) (hfirst t) (hsecond t) (hthird t)
      (hexception t) hpower
  exact level_series_ne_top_of_six_cover mu hsix hscreened

/-! ## First Borel--Cantelli and the clock bridge -/

/-- First Borel--Cantelli plus the exact `M_m^4` clock identity. -/
theorem ae_eventually_favoriteCount_le_three_of_M4_summable
    (mu : Measure WalkPath)
    (hsum : ∑' m, mu (levelFavoriteSet m 4) ≠ ∞)
    (hdiv : ∀ᵐ s ∂mu, MaxLocalTimeDiverges s) :
    ∀ᵐ s ∂mu, ∀ᶠ n in atTop, favoriteCount s n ≤ 3 := by
  filter_upwards [ae_eventually_notMem hsum, hdiv] with s hfinite hsdiv
  by_contra hnot
  rw [not_eventually] at hnot
  have hfour : ∃ᶠ n in atTop, 4 ≤ favoriteCount s n :=
    hnot.mono fun n hn ↦ by omega
  have hlevels : ∃ᶠ m in atTop, levelFavorite s m 4 :=
    (frequently_favoriteCount_ge_iff_frequently_levelFavorite
      s 4 (by norm_num) hsdiv).mp hfour
  have hfinite' : ∀ᶠ m in atTop, ¬levelFavorite s m 4 := by
    simpa [levelFavoriteSet] using hfinite
  exact (hlevels.and_eventually hfinite').exists.elim fun _ hm ↦ hm.2 hm.1

/-- The full upper-bound assembly, from the named estimate hypotheses through
three transitions, a finite three-gap mesh, six tilings, first
Borel--Cantelli, and the ordinary-time clock bridge. -/
theorem ae_eventually_favoriteCount_le_three_of_three_transition_estimates
    {Scale : Type*} (mu : Measure WalkPath) (mesh : Finset Scale)
    (screened exceptional : UpperTiling → Nat → Set WalkPath)
    (firstStage secondStage thirdStage :
      UpperTiling → Nat → ((Scale × Scale) × Scale) → Set WalkPath)
    (q : Nat → ENNReal) (C : NNReal) (p : Real)
    (hp : 1 < p)
    (hsix : ∀ m, levelFavoriteSet m 4 ⊆ ⋃ t, screened t m)
    (hmesh : ∀ t m, screened t m ⊆
      exceptional t m ∪ meshBranchUnion mesh (thirdStage t m))
    (hfirst : ∀ t m a, a ∈ meshTriples mesh →
      mu (firstStage t m a) ≤ q m)
    (hsecond : ∀ t m a, a ∈ meshTriples mesh →
      mu (secondStage t m a) ≤ q m * mu (firstStage t m a))
    (hthird : ∀ t m a, a ∈ meshTriples mesh →
      mu (thirdStage t m a) ≤ q m * mu (secondStage t m a))
    (hexception : ∀ t, ∑' m, mu (exceptional t m) ≠ ∞)
    (hpower : ∀ m, q m ^ 3 ≤ (C : ENNReal) * pSeriesWeight p m)
    (hdiv : ∀ᵐ s ∂mu, MaxLocalTimeDiverges s) :
    ∀ᵐ s ∂mu, ∀ᶠ n in atTop, favoriteCount s n ≤ 3 := by
  apply ae_eventually_favoriteCount_le_three_of_M4_summable mu
  · exact levelFavorite_four_series_ne_top_of_three_transitions mu mesh
      screened exceptional firstStage secondStage thirdStage q C p hp hsix hmesh
      hfirst hsecond hthird hexception hpower
  · exact hdiv

end UpperAssembly
end Erdos1165
