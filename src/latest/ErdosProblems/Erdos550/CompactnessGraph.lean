import Mathlib
import ErdosProblems.Erdos550.Compactness
import ErdosProblems.Erdos550.BlockerInequalities

set_option relaxedAutoImplicit true
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Graph-native form of null-blocker compactness

`null_blocker_compactness` (file `Compactness.lean`) is stated in terms of
abstract probability spaces and measures.  In the application (Section 10 of the
paper) the probability spaces are the reservoirs `W i` equipped with the uniform
measure, and the events `A i x` are the red neighbourhoods of `x` inside `W i`,
so that the density `ρ_i(x)` equals `|commonRedNbhd Gr {x} (W i)| / |W i|`.

This file performs that measure-theoretic bridge once and for all, packaging
`null_blocker_compactness` as a purely graph-theoretic statement
`null_blocker_compactness_graph` whose hypotheses and conclusion only mention the
finset densities `|commonRedNbhd Gr S (W i)| / |W i|`.  The final assembly then
uses this corollary directly, never touching measures.
-/

open MeasureTheory Finset
open scoped ENNReal

namespace Erdos550

/-
**Density identity.**  For a nonempty reservoir `W` with the uniform
probability measure on the subtype `{w // w ∈ W}`, the measure of the event
"`w` is red-adjacent to every vertex of `T`" equals the finset density
`|commonRedNbhd Gr T W| / |W|`.
-/
theorem dens_uniform_commonRedNbhd {V : Type} [Fintype V] [DecidableEq V]
    (Gr : SimpleGraph V) [DecidableRel Gr.Adj] (W : Finset V) (hW : W.Nonempty)
    (T : Finset V) :
    haveI : Nonempty {w // w ∈ W} := ⟨⟨hW.choose, hW.choose_spec⟩⟩
    letI : MeasurableSpace {w // w ∈ W} := ⊤
    (((PMF.uniformOfFintype {w // w ∈ W}).toMeasure
        {w : {w // w ∈ W} | ∀ x ∈ T, Gr.Adj x w.val}).toReal)
      = ((commonRedNbhd Gr T W).card : ℝ) / (W.card : ℝ) := by
  convert! Set.indicator_apply ( fun w : { w // w ∈ W } => ∀ x ∈ T, Gr.Adj x ( w : V ) ) ( fun _ => 1 / ( Fintype.card { w // w ∈ W } : ENNReal ) ) using 1;
  simp +decide [ Set.indicator ];
  rw [ Finset.sum_ite ] ; norm_num;
  rw [ commonRedNbhd ];
  rw [ ← Finset.card_image_of_injective _ Subtype.coe_injective ] ; congr ; ext ; aesop

/-
**Null-blocker compactness, graph-native form.**

Fix `q ≥ 2`, `a ≥ 1`, and a rank bound `rStar ≥ 1`.  There is a threshold
`ε₀ > 0` such that for every finite graph `Gr` with reservoirs `W i` (all
nonempty), a remainder set `Xs`, hypergraphs `C i` of nonempty edges of size
`≤ rStar` contained in `Xs`, and slack `0 ≤ ε ≤ ε₀` satisfying

* (A1) `∑ᵢ |commonRedNbhd Gr {x} (W i)| / |W i| ≥ q - 1 - ε` for all `x ∈ Xs`,
* (A2) for every `a`-set `S ⊆ Xs`, some `i` has `|commonRedNbhd Gr S (W i)| / |W i| ≤ ε`,
* (A3) for every `i` and `E ∈ C i`, some `j ≠ i` has `|commonRedNbhd Gr E (W j)| / |W j| ≤ ε`,

there are a deletion set `Z ⊆ Xs` with `|Z| ≤ a - 1` and a colouring
`φ : V → Fin q` such that no edge `E ∈ C i` is monochromatic in colour `i` with
all vertices undeleted.
-/
set_option maxHeartbeats 1000000 in
theorem null_blocker_compactness_graph
    (q : ℕ) (hq : 2 ≤ q) (a : ℕ) (ha : 1 ≤ a) (rStar : ℕ) (hr : 1 ≤ rStar) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧
      ∀ {V : Type} [Fintype V] [DecidableEq V]
        (Gr : SimpleGraph V) [DecidableRel Gr.Adj]
        (W : Fin q → Finset V) (Xs : Finset V)
        (C : Fin q → Set (Finset V)) (ε : ℝ),
        0 ≤ ε → ε ≤ ε₀ →
        (∀ i, (W i).Nonempty) →
        (∀ i, ∀ E ∈ C i, E.Nonempty ∧ E.card ≤ rStar ∧ E ⊆ Xs) →
        (∀ x ∈ Xs, (q : ℝ) - 1 - ε ≤
          ∑ i, ((commonRedNbhd Gr {x} (W i)).card : ℝ) / (W i).card) →
        (∀ S : Finset V, S ⊆ Xs → S.card = a →
          ∃ i, ((commonRedNbhd Gr S (W i)).card : ℝ) / (W i).card ≤ ε) →
        (∀ i : Fin q, ∀ E ∈ C i, ∃ j, j ≠ i ∧
          ((commonRedNbhd Gr E (W j)).card : ℝ) / (W j).card ≤ ε) →
        ∃ (Z : Finset V) (φ : V → Fin q), Z ⊆ Xs ∧ Z.card ≤ a - 1 ∧
          ∀ i : Fin q, ∀ E ∈ C i, ¬ (∀ x ∈ E, x ∉ Z ∧ φ x = i) := by
  obtain ⟨ ε₀, hε₀, H ⟩ := null_blocker_compactness q hq a ha rStar hr;
  refine' ⟨ ε₀, hε₀, fun { V } _ _ Gr _ W Xs C ε hε₀ hε₁ hWne hCrank hA1 hA2 hA3 => _ ⟩;
  convert! H ( { x // x ∈ Xs } ) ( fun i => { w // w ∈ W i } ) ( fun i => ( PMF.uniformOfFintype { w // w ∈ W i } ).toMeasure ) ( fun i x => { w : { w // w ∈ W i } | Gr.Adj x.val w.val } ) _ ( fun i => { E' : Finset { x // x ∈ Xs } | ( E'.image Subtype.val ) ∈ C i } ) ε hε₀ hε₁ _ _ _ _ using 1;
  rotate_left;
  exact fun _ => ⊤;
  exact fun i => ⟨ ⟨ hWne i |> Classical.choose, hWne i |> Classical.choose_spec ⟩ ⟩;
  all_goals norm_num [ Set.subset_def ];
  · intro i E hE; specialize hCrank i ( E.image Subtype.val ) hE; simp +decide [ Finset.card_image_of_injective _ Subtype.coe_injective ] at hCrank ⊢;
    exact ⟨ hCrank.1, hCrank.2.1 ⟩;
  · intro x hx; specialize hA1 x hx; simp +decide [ dens ] at *;
    convert! hA1 using 3;
    refine' Finset.sum_congr rfl fun i _ => _;
    convert! dens_uniform_commonRedNbhd Gr ( W i ) ( hWne i ) { x } using 1;
    simp +decide [ Set.indicator, PMF.uniformOfFintype ];
  · intro S hS;
    obtain ⟨ i, hi ⟩ := hA2 ( S.image Subtype.val ) ( Finset.image_subset_iff.mpr fun x hx => x.2 ) ( by rw [ Finset.card_image_of_injective _ Subtype.coe_injective, hS ] );
    use i;
    convert! hi using 1;
    convert! dens_uniform_commonRedNbhd Gr ( W i ) ( hWne i ) ( S.image Subtype.val ) using 1;
    simp +decide [ Set.indicator, Finset.sum_ite ];
  · intro i E hE;
    obtain ⟨ j, hj₁, hj₂ ⟩ := hA3 i _ hE;
    refine' ⟨ j, hj₁, _ ⟩;
    convert! hj₂ using 1;
    convert! dens_uniform_commonRedNbhd Gr ( W j ) ( hWne j ) ( E.image Subtype.val ) using 1;
    simp +decide [ Set.indicator, Finset.sum_ite ];
  · constructor;
    · rintro ⟨ Z, hZ₁, hZ₂, x, hx ⟩;
      use Finset.filter (fun x => x.val ∈ Z) (Finset.univ : Finset { x // x ∈ Xs });
      refine' ⟨ _, _ ⟩;
      · convert! hZ₂ using 1;
        refine' Finset.card_bij ( fun y hy => y ) _ _ _ <;> simp +decide [  ];
        exact fun x hx => ⟨ hx, hZ₁ hx ⟩;
      · use fun ⟨ v, hv ⟩ => x v;
        grind +splitIndPred;
    · rintro ⟨ Z, hZ₁, x, hx ⟩;
      refine' ⟨ Z.image Subtype.val, _, _, _ ⟩;
      · exact Finset.image_subset_iff.mpr fun x hx => x.2;
      · rwa [ Finset.card_image_of_injective _ Subtype.coe_injective ];
      · use fun v => if hv : v ∈ Xs then x ⟨ v, hv ⟩ else ⟨ 0, by linarith ⟩;
        intro i E hE;
        obtain ⟨ y, hy₁, hy₂, hy₃ ⟩ := hx i ( Finset.subtype ( fun x => x ∈ Xs ) E ) ( by
          convert! hE using 1;
          ext; simp [Finset.mem_image];
          exact fun h => hCrank i E hE |>.2.2 h );
        grind

end Erdos550
