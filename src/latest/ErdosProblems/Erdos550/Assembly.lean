import Mathlib
import ErdosProblems.Erdos550.Basic
import ErdosProblems.Erdos550.FinalReduction
import ErdosProblems.Erdos550.BlockerInequalities
import ErdosProblems.Erdos550.CompactnessGraph

set_option relaxedAutoImplicit true
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Assembly core (Section 10 combinatorial heart)

This file isolates the purely-combinatorial heart of the main-theorem assembly:
given a clean reservoir configuration (reservoirs `W i`, remainder `X`) in a
red graph `Gr` with no red `F` and no blue `T`, together with the **red profile
bound** `A1` (which downstream comes from the profile lemma / absence of a blue
`T`), it produces — via the blocker hypergraph inequalities and null-blocker
compactness — the partition feeding `final_reduction`, and derives the capacity
contradiction.

All the chained existential thresholds (the cross-blue slack `ζ`, the reservoir
size threshold `s`, the compactness slack `ε`) are produced *internally* here, so
that the outer (analytic) part of the assembly only has to guarantee that the
reservoirs from the clean decomposition meet a single size threshold and a single
slack, and to supply `A1`.
-/

open SimpleGraph Finset

namespace Erdos550

/-
A obstruction `E` has at most `a + b` vertices: the `K_{a,b}`-copy living in
`W i ∪ E` uses at most `a+b` vertices outside `W i`, and by minimality `E` is
contained in that vertex set.
-/
lemma obstruction_card_le {V : Type*} [DecidableEq V] (Gr : SimpleGraph V)
    [DecidableRel Gr.Adj] (a b : ℕ) (Wi X E : Finset V)
    (h : IsObstruction Gr a b Wi X E) : E.card ≤ a + b := by
  obtain ⟨E', hE'ref, hE'⟩ : ∃ E' : Finset V, E' ⊆ E ∧ (Kbip a b ⊑ Gr.induce (↑(Wi ∪ E'))) ∧ E'.card ≤ a + b := by
    obtain ⟨f, hf⟩ := h.2.2.1;
    refine' ⟨ Finset.image ( fun x => ( f x : V ) ) ( Finset.univ.filter fun x => ( f x : V ) ∈ E ), _, _, _ ⟩;
    · grind;
    · refine' ⟨ _, _ ⟩;
      refine' { .. };
      use fun x => ⟨ f x, by
        grind +splitImp ⟩
      all_goals generalize_proofs at *;
      · exact fun { a b } hab => f.map_rel' hab;
      · exact fun x y hxy => hf <| Subtype.ext <| by simpa using! congr_arg Subtype.val hxy;
    · refine' le_trans ( Finset.card_image_le ) _;
      refine' le_trans ( Finset.card_le_univ _ ) _ ; simp +decide [  ];
  cases eq_or_ne E' E <;> simp_all +decide [ IsObstruction ];
  exact False.elim ( h.2.2.2 E' ( lt_of_le_of_ne hE'ref ‹_› ) |> fun h => h.elim hE'.1.some )

/-
From a `K_{a,b}`-copy inside `W i ∪ Y` (with `Y ⊆ X`) when `Gr[W i]` is
`K_{a,b}`-free, one extracts a obstruction `E ⊆ Y` (an inclusion-minimal subset of
`Y` whose union with `W i` still contains the copy).
-/
lemma exists_obstruction_of_copy {V : Type*} [Fintype V] [DecidableEq V]
    (Gr : SimpleGraph V) [DecidableRel Gr.Adj] (a b : ℕ) (Wi X Y : Finset V)
    (hY : Y ⊆ X) (hWiHfree : ¬ (Kbip a b ⊑ Gr.induce (↑Wi)))
    (hcopy : Kbip a b ⊑ Gr.induce (↑(Wi ∪ Y))) :
    ∃ E, E ⊆ Y ∧ IsObstruction Gr a b Wi X E := by
  obtain ⟨E, hE⟩ : ∃ E : Finset V, E ⊆ Y ∧ Kbip a b ⊑ Gr.induce (↑(Wi ∪ E)) ∧ ∀ E' ⊂ E, ¬ (Kbip a b ⊑ Gr.induce (↑(Wi ∪ E'))) := by
    -- By the well-ordering principle, there exists a minimal subset of `Y` whose union with `Wi` contains the copy.
    obtain ⟨E, hE⟩ : ∃ E : Finset V, E ∈ {E' : Finset V | E' ⊆ Y ∧ Kbip a b ⊑ Gr.induce (↑(Wi ∪ E'))} ∧ ∀ E' ∈ {E' : Finset V | E' ⊆ Y ∧ Kbip a b ⊑ Gr.induce (↑(Wi ∪ E'))}, E.card ≤ E'.card := by
      apply_rules [ Set.exists_min_image ];
      · exact Set.toFinite _;
      · exact ⟨ Y, Finset.Subset.refl _, hcopy ⟩;
    exact ⟨ E, hE.1.1, hE.1.2, fun E' hE' hE'' => not_lt_of_ge ( hE.2 E' ⟨ Finset.Subset.trans hE'.1 hE.1.1, hE'' ⟩ ) ( Finset.card_lt_card hE' ) ⟩;
  refine' ⟨ E, hE.1, _, _, hE.2.1, hE.2.2 ⟩ <;> simp_all +decide [  ];
  · refine' Finset.nonempty_of_ne_empty _;
    rintro rfl;
    convert! hWiHfree using 1;
    simp +decide [  ];
    convert! hE.2.1 using 1;
    congr! 2;
    · aesop;
    · simp +decide;
  · exact Finset.Subset.trans hE.1 hY

set_option maxHeartbeats 2000000 in
/-- **Assembly core.**  Fix `q ≥ 2`, `a = m' 0 ≥ 1` and class sizes
`m' : Fin (q+1) → ℕ` (monotone, positive).  There are a profile tolerance
`ε > 0`, a reservoir size threshold `sThr`, and a cross-blue slack `ζThr > 0`
such that: for every red graph `Gr` on a finite vertex set, every family of
reservoirs `W` and remainder `X` covering the vertex set, with reservoirs of size
`≥ sThr`, cross-blue slack `≤ ζThr`, each `Gr[W i]` `H`-free (`H = K_{m'0,m'1}`),
no red `F = K_{m'0,…,m'q}`, no blue `T`, the red-profile lower bound `A1`, a
Ramsey witness `r`, and `card V = q(r-1)+a`, we reach a contradiction. -/
theorem assembly_core (q a : ℕ) (hq : 2 ≤ q) (m' : Fin (q + 1) → ℕ)
    (hmono : Monotone m') (hpos : 1 ≤ m' 0) (haq : a = m' 0) :
    ∃ (ε : ℝ) (sThr : ℕ) (ζThr : ℝ), 0 < ε ∧ 0 < ζThr ∧
      ∀ {V : Type} [Fintype V] [DecidableEq V]
        (Gr : SimpleGraph V) [DecidableRel Gr.Adj]
        {Tt : Type} (T : SimpleGraph Tt)
        (W : Fin q → Finset V) (X : Finset V) (r : ℕ),
        (∀ i j, i ≠ j → Disjoint (W i) (W j)) →
        (∀ i, Disjoint X (W i)) →
        ((Finset.univ.biUnion W) ∪ X = Finset.univ) →
        (∀ i, sThr ≤ (W i).card) →
        (∀ i j, i ≠ j → ∀ w ∈ W i,
          (((W j).filter (fun v => ¬ Gr.Adj w v)).card : ℝ) ≤ ζThr * (W j).card) →
        (∀ i, ¬ (Kbip (m' 0) (m' 1) ⊑ Gr.induce (↑(W i)))) →
        ¬ (Kmult (q + 1) m' ⊑ Gr) →
        ¬ (T ⊑ Grᶜ) →
        (∀ x ∈ X, (q : ℝ) - 1 - ε ≤
          ∑ i, ((commonRedNbhd Gr {x} (W i)).card : ℝ) / (W i).card) →
        (∀ S : Finset V, r ≤ S.card →
          Kbip (m' 0) (m' 1) ⊑ Gr.induce (↑S) ∨ T ⊑ (Gr.induce (↑S))ᶜ) →
        Fintype.card V = q * (r - 1) + a →
        False := by
  -- Let `rStar := m' 0 + m' 1` (so `1 ≤ rStar`).
  set rStar := m' 0 + m' 1 with hrStar;
  obtain ⟨ ε₀, hε₀, Hcomp ⟩ := null_blocker_compactness_graph q hq a ( by linarith ) rStar ( by linarith );
  obtain ⟨ζa, hζa, sa, Ha⟩ := aset_separation q hq m' hmono hpos ε₀ hε₀
  obtain ⟨ζc, hζc, sc, Hc⟩ := obstruction_blocking q hq m' hmono hpos ε₀ hε₀
  use ε₀, max (max sa sc) 1, min ζa ζc, hε₀, lt_min hζa hζc;
  intro V _ _ Gr _ Tt T W X r hdisjW hdisjX hcover hWsize hslack hHfree hFfree hNoBlueT hA1 hRamsey hcard;
  obtain ⟨Z, φ, hZsub, hZcard, hindep⟩ := Hcomp Gr W X (fun i => {E | IsObstruction Gr (m' 0) (m' 1) (W i) X E}) ε₀ (by linarith) (by linarith) (fun i => Finset.card_pos.mp (by
  exact lt_of_lt_of_le ( by positivity ) ( hWsize i ))) (fun i E hE => by
    exact ⟨ hE.1, obstruction_card_le Gr ( m' 0 ) ( m' 1 ) ( W i ) X E hE, hE.2.1 ⟩) hA1 (fun S hSsub hScard => by
    specialize Ha Gr W X hdisjW hdisjX (fun i => le_trans (le_max_of_le_left (le_max_left sa sc)) (hWsize i)) (fun i j hij w hw => le_trans (hslack i j hij w hw) (mul_le_mul_of_nonneg_right (min_le_left ζa ζc) (Nat.cast_nonneg _))) hFfree S hSsub (by rw[← haq]; exact hScard);
    exact ⟨ Ha.choose, div_le_of_le_mul₀ ( Nat.cast_nonneg _ ) ( by positivity ) ( Ha.choose_spec ) ⟩) (fun i E hE => by
    obtain ⟨ j, hj₁, hj₂ ⟩ := Hc Gr W X hdisjW hdisjX ( fun i => by linarith [ hWsize i, le_max_left ( max sa sc ) 1, le_max_right ( max sa sc ) 1, le_max_left sa sc, le_max_right sa sc ] ) ( fun i j hij w hw => le_trans ( hslack i j hij w hw ) ( mul_le_mul_of_nonneg_right ( min_le_right _ _ ) ( Nat.cast_nonneg _ ) ) ) hFfree i E hE;
    exact ⟨ j, hj₁, by rwa [ div_le_iff₀ ( Nat.cast_pos.mpr <| Finset.card_pos.mpr <| Finset.card_pos.mp <| by linarith [ hWsize j, le_max_left ( max sa sc ) 1, le_max_right ( max sa sc ) 1, le_max_left sa sc, le_max_right sa sc ] ) ] ⟩);
  set Xi : Fin q → Finset V := fun i => X.filter (fun x => φ x = i ∧ x ∉ Z) with hXi
  set B : Fin q → Finset V := fun i => W i ∪ Xi i with hB
  have hclass : ∀ i, ¬ (Kbip (m' 0) (m' 1) ⊑ Gr.induce (↑(B i))) := by
    intro i hcopy
    obtain ⟨E, hEsub, hEcirc⟩ := exists_obstruction_of_copy Gr (m' 0) (m' 1) (W i) X (Xi i) (Finset.filter_subset _ _) (hHfree i) hcopy
    exact hindep i E hEcirc (by
    exact fun x hx => ⟨ Finset.mem_filter.mp ( hEsub hx ) |>.2.2, Finset.mem_filter.mp ( hEsub hx ) |>.2.1 ⟩);
  apply final_reduction Gr (Kbip (m' 0) (m' 1)) T q a r (by linarith) B Z hZcard (fun i j hij => by
    simp +decide [ Finset.disjoint_left ] at hdisjW hdisjX ⊢;
    grind) (fun i => by
    simp [B];
    exact ⟨ Finset.disjoint_left.mpr fun x hx hx' => Finset.disjoint_left.mp ( hdisjX i ) ( hZsub hx' ) hx, Finset.disjoint_left.mpr fun x hx hx' => Finset.mem_filter.mp hx |>.2.2 hx' ⟩) (by
  ext v; simp [hB, hXi];
  by_cases hv : v ∈ Z <;> simp +decide [ hv ];
  replace hcover := Finset.ext_iff.mp hcover v; simp +decide [  ] at hcover;
  exact hcover.elim ( fun ⟨ i, hi ⟩ => ⟨ i, Or.inl hi ⟩ ) fun hi => ⟨ φ v, Or.inr ⟨ hi, rfl ⟩ ⟩) hclass hNoBlueT hRamsey hcard

end Erdos550
