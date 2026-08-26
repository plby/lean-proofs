-- Modified for this repository: Lean 4.33.0 port and Erdos1177 namespace.
import Mathlib
import ErdosProblems.Erdos1177.ErdosHajnalGirthGeneral

set_option relaxedAutoImplicit true
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# The general-`k` chromatic lower bound (Erdős–Rado cofinal peeling)

This file proves the chromatic lower bound for the Erdős–Hajnal graph
`Erdos1177.EHG.graph k κ` at a **regular** cardinal `κ`: it is not `θ`-colourable
for any `θ < κ`.  Together with the initial-segment reduction
`EHG.colorableBy_of_le` (already proved) this yields the bound for every
uncountable `κ`, generalizing the `k = 3` base case `ER60.not_colorableBy`.

## Strategy

Given a proper `θ`-colouring `c` of the increasing `k`-tuples (`θ < κ` regular),
we build the **stabilization tower** `stab`: reading the coordinates from the
first, at each level we replace the colour of a partial tuple by the colour that
occurs *cofinally* as the next coordinate ranges over a tail (using
`ER60.cofinal_fiber`, valid because `θ < κ = cf κ`).  After `k` levels we obtain a
single colour `star`.

We then extract an increasing chain `α₀ < α₁ < ⋯ < α₂ₖ₋₁` whose two interleaved
`k`-subtuples `a = (α₀,α₁,α₃,…,α₂ₖ₋₃)` and `b = (α₂,α₄,…,α₂ₖ₋₂,α₂ₖ₋₁)` are both
built greedily inside the cofinal `star`-fibres, so `c a = c b = star`.  But
`a`~`b` is an edge, contradicting properness.
-/

open Cardinal Erdos1177.ER60

namespace Erdos1177
namespace EHG

open ER60 (Pt Cofinal cofinal_fiber cofinal_Ioi cofinal_univ)

universe u

variable {κ : Cardinal.{u}} {k : ℕ} {θ : Cardinal.{u}}

/-- The tail set above the last of the first `j` coordinates of `w` (all of
`Pt κ` when `j = 0`).  It is cofinal, so `cofinal_fiber` applies. -/
def tailSet (w : ℕ → Pt κ) (j : ℕ) : Set (Pt κ) :=
  if j = 0 then Set.univ else {z | w (j - 1) < z}

theorem tailSet_cofinal (hκ : ℵ₀ ≤ κ) (w : ℕ → Pt κ) (j : ℕ) :
    Cofinal (tailSet w j) := by
  unfold tailSet
  split
  · exact cofinal_univ hκ
  · exact cofinal_Ioi hκ _

/-- **The stabilization tower.**  `stab hreg hθ c fuel j w` is the colour obtained
from the total colouring `c` by cofinally stabilizing coordinates `j, j+1, …`
(there are `fuel` of them left to stabilize), the first `j` coordinates of `w`
being fixed.  With `fuel = 0` it just evaluates `c`. -/
noncomputable def stab (hreg : κ.IsRegular) (hθ : θ < κ) (c : (ℕ → Pt κ) → θ.out) :
    ℕ → ℕ → (ℕ → Pt κ) → θ.out
  | 0, _, w => c w
  | (fuel + 1), j, w =>
      Classical.choose (cofinal_fiber hreg hθ (tailSet_cofinal hreg.1 w j)
        (fun z => stab hreg hθ c fuel (j + 1) (Function.update w j z)))

/-- **Cofinal-fibre spec of the tower.**  For every level, the set of next
coordinates `z` in the tail that keep the stabilized colour equal to
`stab … (fuel+1) j w` is cofinal. -/
theorem stab_spec (hreg : κ.IsRegular) (hθ : θ < κ) (c : (ℕ → Pt κ) → θ.out)
    (fuel j : ℕ) (w : ℕ → Pt κ) :
    Cofinal {z | z ∈ tailSet w j ∧
      stab hreg hθ c fuel (j + 1) (Function.update w j z)
        = stab hreg hθ c (fuel + 1) j w} := by
  exact Classical.choose_spec (cofinal_fiber hreg hθ (tailSet_cofinal hreg.1 w j)
    (fun z => stab hreg hθ c fuel (j + 1) (Function.update w j z)))

/-
**Prefix congruence.**  If `c` reads only the first `k` coordinates, then
`stab … fuel j w` depends only on the first `j` coordinates of `w`, provided
`j + fuel ≥ k` (so the untouched high coordinates lie beyond `k`).
-/
theorem stab_congr (hreg : κ.IsRegular) (hθ : θ < κ) (c : (ℕ → Pt κ) → θ.out)
    (hc : ∀ w w' : ℕ → Pt κ, (∀ i < k, w i = w' i) → c w = c w') :
    ∀ (fuel j : ℕ), k ≤ j + fuel → ∀ (w w' : ℕ → Pt κ), (∀ i < j, w i = w' i) →
      stab hreg hθ c fuel j w = stab hreg hθ c fuel j w' := by
  intro fuel j hj w w' hw;
  induction' fuel with fuel ih generalizing j w w' <;> simp_all +decide [ stab ];
  · exact hc _ _ fun i hi => hw i ( by linarith );
  · congr! 1;
    ext x;
    congr! 1;
    ext y;
    simp +decide [ tailSet ];
    grind

/-- **One-step extension.**  From `stab_spec`, above any bound `B` there is a
next coordinate `z` (in the tail) that preserves the stabilized colour. -/
theorem exists_next_star (hreg : κ.IsRegular) (hθ : θ < κ) (c : (ℕ → Pt κ) → θ.out)
    (fuel j : ℕ) (w : ℕ → Pt κ) (B : Pt κ) :
    ∃ z, B < z ∧ z ∈ tailSet w j ∧
      stab hreg hθ c fuel (j + 1) (Function.update w j z)
        = stab hreg hθ c (fuel + 1) j w := by
  obtain ⟨z, hzS, hBz⟩ := stab_spec hreg hθ c fuel j w B
  exact ⟨z, hBz, hzS.1, hzS.2⟩

/-- Total colouring extending a colouring of increasing `k`-tuples by a junk
value off the strictly-monotone tuples. -/
noncomputable def toTotal (k : ℕ) (c0 : Vtx k κ → θ.out) (junk : θ.out) :
    (ℕ → Pt κ) → θ.out :=
  fun w => if h : StrictMono (fun i : Fin k => w i) then c0 ⟨_, h⟩ else junk

theorem toTotal_prefix (k : ℕ) (c0 : Vtx k κ → θ.out) (junk : θ.out)
    (w w' : ℕ → Pt κ) (h : ∀ i < k, w i = w' i) :
    toTotal k c0 junk w = toTotal k c0 junk w' := by
  unfold toTotal
  have he : (fun i : Fin k => w i) = (fun i : Fin k => w' i) := funext (fun i => h i i.2)
  simp only [he]

theorem toTotal_mono (k : ℕ) (c0 : Vtx k κ → θ.out) (junk : θ.out)
    (w : ℕ → Pt κ) (h : StrictMono (fun i : Fin k => w i)) :
    toTotal k c0 junk w = c0 ⟨fun i : Fin k => w i, h⟩ := dif_pos h

/-
**The interleaving-extraction induction.**  Building the two star-realizing
tuples `a` (of length `cb+2`) and `b` (of length `cb`) in the interleaved order
`a₀ < a₁ < b₀ < a₂ < b₁ < ⋯ < b_{cb-1} < a_{cb+1}`, with both colours pinned to
`star`.
-/
set_option maxHeartbeats 1200000 in
theorem extract_aux (hreg : κ.IsRegular) (hθ : θ < κ) (c : (ℕ → Pt κ) → θ.out)
    (star : θ.out) (hstar : ∀ w, stab hreg hθ c k 0 w = star) (hk : 2 ≤ k) :
    ∀ cb, cb ≤ k - 2 → ∃ (wa wb : ℕ → Pt κ),
      StrictMonoOn wa (Set.Iio (cb + 2)) ∧ StrictMonoOn wb (Set.Iio cb) ∧
      stab hreg hθ c (k - (cb + 2)) (cb + 2) wa = star ∧
      stab hreg hθ c (k - cb) cb wb = star ∧
      (∀ i < cb, wa (i + 1) < wb i) ∧
      (∀ i < cb, wb i < wa (i + 2)) ∧
      (∀ i < cb, wb i < wa (cb + 1)) := by
  intro cb hcb;
  induction' cb with cb ih generalizing k;
  · rcases k with ( _ | _ | k ) <;> simp_all +decide [ StrictMonoOn ];
    obtain ⟨ z₀, hz₀ ⟩ := exists_next_star hreg hθ c ( k + 1 ) 0 ( fun _ => Classical.choose ( show ∃ p : Pt κ, True from by
                                                                                                cases isEmpty_or_nonempty ( Pt κ ) <;> aesop ) ) ( Classical.choose ( show ∃ p : Pt κ, True from by
                                                                                                                                                              cases hreg ; aesop ) )
    generalize_proofs at *;
    obtain ⟨ z₁, hz₁ ⟩ := exists_next_star hreg hθ c k 1 ( Function.update ( fun _ => Classical.choose ‹∃ p : Pt κ, True› ) 0 z₀ ) z₀
    generalize_proofs at *;
    use Function.update (Function.update (fun _ => Classical.choose ‹∃ p : Pt κ, True›) 0 z₀) 1 z₁;
    simp_all +decide [ Function.update_apply ];
    exact ⟨ fun a ha b hb hab => by interval_cases a <;> interval_cases b ; tauto, by rintro rfl; exact absurd hθ ( by simp +decide ) ⟩;
  · obtain ⟨wa, wb, hwa_mono, hwb_mono, hwa_star, hwb_star, hwa_lt_hwb, hwb_lt_hwa, hwb_lt_hwa_last⟩ := ih hstar hk (by omega);
    -- Place `b_cb`: apply `exists_next_star` to get `zb` with `wa(cb+1) < zb`, `zb ∈ tailSet wb cb`, and `stab _ (k-cb-1) (cb+1) (Function.update wb cb zb) = star`.
    obtain ⟨zb, hzb_gt, hzb_tail, hzb_star⟩ : ∃ zb, wa (cb + 1) < zb ∧ zb ∈ tailSet wb cb ∧ stab hreg hθ c (k - cb - 1) (cb + 1) (Function.update wb cb zb) = star := by
      convert! exists_next_star hreg hθ c ( k - cb - 1 ) cb wb ( wa ( cb + 1 ) ) using 1;
      grind +revert;
    -- Place `a_{cb+2}`: apply `exists_next_star` to get `za` with `zb < za`, `za ∈ tailSet wa (cb+2)`, and `stab _ (k-(cb+2)-1) (cb+3) (Function.update wa (cb+2) za) = star`.
    obtain ⟨za, hza_gt, hza_tail, hza_star⟩ : ∃ za, zb < za ∧ za ∈ tailSet wa (cb + 2) ∧ stab hreg hθ c (k - (cb + 2) - 1) (cb + 3) (Function.update wa (cb + 2) za) = star := by
      convert! exists_next_star hreg hθ c ( k - ( cb + 2 ) - 1 ) ( cb + 2 ) wa zb using 1;
      grind +qlia;
    refine' ⟨ Function.update wa ( cb + 2 ) za, Function.update wb cb zb, _, _, _, _, _ ⟩;
    · intro x hx y hy hxy; simp_all +decide [ StrictMonoOn, Function.update_apply ] ;
      split_ifs <;> try linarith;
      · by_cases hx' : x < cb + 1;
        · exact lt_trans ( hwa_mono ( by linarith ) ( by linarith ) ( by linarith ) ) ( lt_trans hzb_gt hza_gt );
        · grind;
      · exact hwa_mono ( by omega ) ( by omega ) hxy;
    · intro i hi j hj hij; simp_all +decide [ StrictMonoOn ] ;
      grind +splitImp;
    · exact hza_star;
    · grind;
    · grind +locals

/-
**General chromatic lower bound at a regular cardinal.**  For `k ≥ 2` and
`κ` regular, `graph k κ` is not `θ`-colourable for any `θ < κ`.  Generalizes
`ER60.not_colorableBy_regular`.
-/
set_option maxHeartbeats 1600000 in
theorem not_colorableBy_regular_general (hreg : κ.IsRegular) (hk : 2 ≤ k)
    (hθ : θ < κ) :
    ¬ (SimpleGraph.toHG (graph k κ hk)).ColorableBy θ := by
  by_contra h_contra;
  -- Set `junk := c0 x0` for some vertex `x0 : Vtx k κ` (nonempty because `Pt κ` is infinite, so a strictly monotone `Fin k → Pt κ` exists; construct one or use `Classical`/`Nonempty`).
  obtain ⟨c0, hc0'⟩ := h_contra
  obtain ⟨x0, hx0⟩ : ∃ x0 : Vtx k κ, True := by
    have h_inf : Infinite (Pt κ) := by
      have := hreg.1;
      exact Cardinal.infinite_iff.2 ( by simpa using! this );
    obtain ⟨s, hs⟩ : ∃ s : Finset (Pt κ), s.card = k := by
      have := h_inf.natEmbedding;
      exact ⟨ Finset.image ( fun i : Fin k => this i ) Finset.univ, by rw [ Finset.card_image_of_injective _ fun i j hij => by simpa [ Fin.ext_iff ] using! this.injective hij ] ; simp +decide ⟩;
    exact ⟨ ⟨ fun i => s.orderEmbOfFin ( by aesop ) i, by aesop_cat ⟩, trivial ⟩
  set junk := c0 x0;
  -- Set `c := toTotal k c0 junk` and `hc := toTotal_prefix k c0 junk` (so `c` reads only the first `k` coords).
  set c := toTotal k c0 junk
  have hc : ∀ w w' : ℕ → Pt κ, (∀ i < k, w i = w' i) → c w = c w' := by
    grind +suggestions;
  obtain ⟨star, hstar⟩ : ∃ star : θ.out, ∀ w : ℕ → Pt κ, stab hreg hθ c k 0 w = star := by
    use stab hreg hθ c k 0 (fun _ => Classical.choice (by
    exact ⟨ x0.1 ⟨ 0, by linarith ⟩ ⟩ : Nonempty (Pt κ)));
    intro w; exact (by
    convert! stab_congr hreg hθ c hc k 0 ( by omega ) w ( fun _ => Classical.choice ( by solve_by_elim ) ) ( fun i hi => by
      contradiction ) using 1);
  obtain ⟨wa, wb, hwa, hwb, hwa_star, hwb_star, hwa_wb⟩ := extract_aux hreg hθ c star hstar hk (k - 2) (Nat.le_refl (k - 2));
  obtain ⟨zb, hzb⟩ := exists_next_star hreg hθ c 1 (k - 2) wb (wa (k - 1))
  obtain ⟨zc, hzc⟩ := exists_next_star hreg hθ c 0 (k - 1) (Function.update wb (k - 2) zb) zb;
  -- Let `a := (⟨fun i : Fin k => wa i, ha⟩ : Vtx k κ)` where `ha : StrictMono (fun i : Fin k => wa i)` from `StrictMonoOn wa (Set.Iio k)` (each `Fin` index is `< k`), and `b := (⟨fun i : Fin k => wb3 i, hb⟩ : Vtx k κ)` where `hb` from: `wb3` agrees with `wb` on `[0,k-2)`, `wb3 (k-2) = zb`, `wb3 (k-1) = zc`, using `StrictMonoOn wb (Set.Iio (k-2))`, `wb i < wa (k-1) < zb` (for `i<k-2`) and `zb < zc`.
  set a : Vtx k κ := ⟨fun i : Fin k => wa i, by
    intro i j hij; have := hwa ( show ( i : ℕ ) < k - 2 + 2 from by omega ) ( show ( j : ℕ ) < k - 2 + 2 from by omega ) hij; aesop;⟩
  set b : Vtx k κ := ⟨fun i : Fin k => (Function.update (Function.update wb (k - 2) zb) (k - 1) zc) i, by
    intro i j hij; simp +decide [ Function.update_apply ] ;
    split_ifs <;> try omega;
    · exact hzc.1;
    · grind +splitIndPred;
    · grind;
    · exact hwb ( show ( i : ℕ ) < k - 2 from by omega ) ( show ( j : ℕ ) < k - 2 from by omega ) ( by simpa [ Fin.ext_iff ] using! hij )⟩
  generalize_proofs at *;
  -- Colours: `c wa = star` and `c wb3 = star`, and by `toTotal_mono` these equal `c0 a` and `c0 b`; hence `c0 a = c0 b`.
  have hcol : c0 a = star ∧ c0 b = star := by
    have hcol : c wa = star ∧ c (Function.update (Function.update wb (k - 2) zb) (k - 1) zc) = star := by
      rcases k with ( _ | _ | k ) <;> simp_all +decide;
      · contradiction;
      · contradiction;
      · simp_all +decide [ Nat.succ_sub ];
        exact ⟨ hwa_star, hzc.2.2 ⟩;
    grind +locals;
  -- Edge: `(graph k κ hk).Adj a b` holds as `Or.inl (IsEdge a.1 b.1)`, where `IsEdge (fun i => wa i) (fun i => wb3 i)`.
  have hadj : (graph k κ hk).Adj a b := by
    refine' Or.inl ⟨ _, _ ⟩;
    · grind;
    · grind +splitImp;
  grind +suggestions

end EHG
end Erdos1177
