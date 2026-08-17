/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

import ErdosProblems.Erdos63.ExactPaths
import ErdosProblems.Erdos63.Density
import ErdosProblems.Erdos63.ExpanderExtraction
import ErdosProblems.Erdos63.LiuMontgomeryReduction
import ErdosProblems.Erdos63.Parameters
import ErdosProblems.Erdos63.PathCycles

/-!
# The finite Liu--Montgomery interval theorem

This file assembles the unconditional finite source used in the proof of
Erdős Problem 63.  The Komlós--Szemerédi extraction first produces a
bipartite Liu--Montgomery expander.  If it contains a large one-subdivision
of a complete graph, that subdivision supplies all even lengths in the
required interval.  Otherwise Liu--Montgomery Theorem 2.7 supplies an exact
path of length one less than every requested even length; a fixed edge closes
that path to a cycle.

The endpoint is allowed to depend on which side of the dichotomy occurs.  In
the subdivision branch it is twice the subdivision order.  In the exact-path
branch it is the natural floor of `n / (Real.log n) ^ 12`, where `n` is the
order of the extracted expander.
-/

open Filter Finset Set SimpleGraph
open scoped SimpleGraph

namespace Erdos63

noncomputable section

universe u

variable {V : Type u} {G : SimpleGraph V}

/-- An endpoint above `exp 6` has logarithmic eighth power at least six. -/
private theorem six_le_log_pow_eight_of_exp_six_le {ell : ℝ}
    (hell : Real.exp 6 ≤ ell) :
    (6 : ℝ) ≤ Real.log ell ^ 8 := by
  have hell_pos : 0 < ell := (Real.exp_pos 6).trans_le hell
  have hlog : (6 : ℝ) ≤ Real.log ell :=
    (Real.le_log_iff_exp_le hell_pos).2 hell
  calc
    (6 : ℝ) ≤ 6 ^ 8 := by norm_num
    _ ≤ Real.log ell ^ 8 := by gcongr

/-- The exact-path branch of Liu--Montgomery's final dichotomy.

The premise `hexact` is precisely the conclusion of Theorem 2.7, restricted
to the fixed endpoints of an edge.  All parity and floor bookkeeping needed
to close those paths into the advertised cycle interval is discharged here.
-/
private theorem even_cycle_interval_of_exact_paths_on_edge
    [Fintype V] (B : Bipartition G) {x y : V}
    (hxy : G.Adj x y) (hwindow :
      Real.log (Fintype.card V : ℝ) ^ 7 + 1 ≤
          Real.log (Parameters.lmFloorEndpoint (Fintype.card V) : ℝ) ^ 8 ∧
      (Parameters.lmFloorEndpoint (Fintype.card V) : ℝ) ≤
          Parameters.lmPathScale (Fintype.card V : ℝ))
    (hexact : ∀ q : ℕ, ParityCompatible B x y q →
      Real.log (Fintype.card V : ℝ) ^ 7 ≤ q →
      (q : ℝ) ≤ Parameters.lmPathScale (Fintype.card V : ℝ) →
      HasPathBetweenLength G x y q)
    (hlog6 : (6 : ℝ) ≤
      Real.log (Parameters.lmFloorEndpoint (Fintype.card V) : ℝ) ^ 8) :
    ∀ m : ℕ, Even m →
      Real.log (Parameters.lmFloorEndpoint (Fintype.card V) : ℝ) ^ 8 ≤ m →
      (m : ℝ) ≤ Parameters.lmFloorEndpoint (Fintype.card V) →
      HasCycleLength G m := by
  intro m hmEven hmLower hmUpper
  have hm6 : 6 ≤ m := by
    exact_mod_cast hlog6.trans hmLower
  have hmUpperNat : m ≤ Parameters.lmFloorEndpoint (Fintype.card V) := by
    exact_mod_cast hmUpper
  obtain ⟨hqLower, hqUpper⟩ :=
    Parameters.sub_one_mem_path_window hwindow hmLower hmUpperNat
  have hqOdd : Odd (m - 1) := by
    obtain ⟨a, ha⟩ := hmEven
    refine ⟨a - 1, ?_⟩
    omega
  have hqParity : ParityCompatible B x y (m - 1) := by
    rw [parityCompatible_iff]
    have hnotEven : ¬ Even (m - 1) :=
      (Nat.not_even_iff_odd.mpr hqOdd)
    have hnotSame : ¬ SameSide B.left B.right x y :=
      (B.oppositeSides_iff_not_sameSide x y).1 (B.oppositeSides_of_adj hxy)
    exact iff_of_false hnotEven hnotSame
  have hpath : HasPathBetweenLength G x y (m - 1) :=
    hexact (m - 1) hqParity hqLower hqUpper
  have hcycle : HasCycleLength G ((m - 1) + 1) :=
    hasCycleLength_succ_of_adj_hasPathBetweenLength hxy (by omega) hpath
  convert hcycle using 1 <;> omega

/-- Cycles found in an induced extracted graph lift through the spanning
subgraph chosen by the bipartite reduction and then into the original graph. -/
private theorem HasCycleLength.lift_extracted [Fintype V]
    {H : SimpleGraph V} (hHG : H ≤ G) (S : Finset V) {m : ℕ}
    (hcycle : HasCycleLength (H.induce (↑S : Set V)) m) :
    HasCycleLength G m :=
  (hcycle.of_induce (↑S : Set V)).mono hHG

/-- Assembly of the final dichotomy from the exact-path theorem.  This lemma
is kept private and is instantiated below by the proved Liu--Montgomery
Theorem 2.7; its purpose is to keep the extraction and numerical bookkeeping
independent of the internal adjuster construction used to prove that theorem.
-/
private theorem finite_even_cycle_intervals_of_exact_paths
    (d₀ : ℕ)
    (hexact : ∀ {W : Type u} [Fintype W] [Nonempty W]
      (J : SimpleGraph W) [DecidableEq W] [DecidableRel J.Adj]
      (B : Bipartition J) {d : ℕ},
      d₀ ≤ d →
      IsLMExpander J (1 / 1024) ((1 / 64) * (d : ℝ)) →
      (∀ v : W, (d : ℝ) ≤ J.degree v) →
      ¬ oneSubdivisionClique (d / 2) ⊑ J →
      ∀ {x y : W} {q : ℕ}, x ≠ y → ParityCompatible B x y q →
        Real.log (Fintype.card W : ℝ) ^ 7 ≤ q →
        (q : ℝ) ≤ Parameters.lmPathScale (Fintype.card W : ℝ) →
        HasPathBetweenLength J x y q) :
    ∀ (requested : ℝ), ∃ threshold : ℕ, 0 < threshold ∧
      ∀ {W : Type u} [Fintype W] [Nonempty W]
        (G : SimpleGraph W) [DecidableRel G.Adj],
        AvgDegreeAtLeast G threshold →
          ∃ ell : ℝ, requested ≤ ell ∧
            ∀ m : ℕ, Even m → Real.log ell ^ 8 ≤ m →
              (m : ℝ) ≤ ell → HasCycleLength G m := by
  intro requested
  let target : ℝ := max requested (Real.exp 6)
  have htarget_pos : 0 < target :=
    (Real.exp_pos 6).trans_le (le_max_right requested (Real.exp 6))
  obtain ⟨windowThreshold, hwindowThreshold⟩ :=
    (eventually_atTop.1 Parameters.eventually_lmFloorEndpoint_window)
  have hfloorTendsto :
      Tendsto (fun n : ℕ ↦
        (Parameters.lmFloorEndpoint n : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp Parameters.tendsto_lmFloorEndpoint_atTop
  obtain ⟨endpointThreshold, hendpointThreshold⟩ :=
    eventually_atTop.1
      (hfloorTendsto.eventually (eventually_ge_atTop target))
  let scale : ℕ := max ⌈target⌉₊
    (max d₀ (max windowThreshold endpointThreshold))
  let degreeScale : ℕ := 2 * scale
  let threshold : ℕ := 8 * degreeScale
  have hceil_pos : 0 < ⌈target⌉₊ := Nat.ceil_pos.mpr htarget_pos
  have hscale_pos : 0 < scale :=
    hceil_pos.trans_le (le_max_left ⌈target⌉₊
      (max d₀ (max windowThreshold endpointThreshold)))
  have hdegree_pos : 0 < degreeScale := by
    dsimp [degreeScale]
    omega
  have hthreshold_pos : 0 < threshold := by
    dsimp [threshold]
    omega
  refine ⟨threshold, hthreshold_pos, ?_⟩
  intro W _ _ G _ haverage
  classical
  have haverage' : AvgDegreeAtLeast G (8 * degreeScale) := by
    simpa [threshold] using haverage
  obtain ⟨H, S, hHG, hHbipartite, hSnonempty, hKexpander,
      _hKaverage, hKdegree⟩ :=
    exists_bipartite_liu_montgomery_expander G hdegree_pos
      (k := (1 / 64) * (degreeScale : ℝ)) (by positivity) haverage'
  let K : SimpleGraph (↑S : Set W) := H.induce (↑S : Set W)
  letI : Nonempty (↑S : Set W) :=
    ⟨⟨hSnonempty.choose, hSnonempty.choose_spec⟩⟩
  let partition : Bipartition K :=
    Bipartition.ofIsBipartite
      (SimpleGraph.IsBipartite.induce hHbipartite (↑S : Set W))
  let vertex : (↑S : Set W) :=
    ⟨hSnonempty.choose, hSnonempty.choose_spec⟩
  have hdegree_nat : degreeScale ≤ K.degree vertex := by
    exact_mod_cast hKdegree vertex
  have hdegree_card : degreeScale < Fintype.card (↑S : Set W) :=
    hdegree_nat.trans_lt (K.degree_lt_card_verts vertex)
  have hd₀ : d₀ ≤ degreeScale := by
    have : d₀ ≤ scale :=
      (le_max_left d₀ (max windowThreshold endpointThreshold)).trans
        (le_max_right ⌈target⌉₊
          (max d₀ (max windowThreshold endpointThreshold)))
    dsimp [degreeScale]
    omega
  have hwindowScale : windowThreshold ≤ degreeScale := by
    have : windowThreshold ≤ scale :=
      (le_max_left windowThreshold endpointThreshold).trans
        ((le_max_right d₀ (max windowThreshold endpointThreshold)).trans
          (le_max_right ⌈target⌉₊
            (max d₀ (max windowThreshold endpointThreshold))))
    dsimp [degreeScale]
    omega
  have hendpointScale : endpointThreshold ≤ degreeScale := by
    have : endpointThreshold ≤ scale :=
      (le_max_right windowThreshold endpointThreshold).trans
        ((le_max_right d₀ (max windowThreshold endpointThreshold)).trans
          (le_max_right ⌈target⌉₊
            (max d₀ (max windowThreshold endpointThreshold))))
    dsimp [degreeScale]
    omega
  have hwindow := hwindowThreshold (Fintype.card (↑S : Set W))
    (hwindowScale.trans hdegree_card.le)
  have hendpoint : target ≤
      (Parameters.lmFloorEndpoint (Fintype.card (↑S : Set W)) : ℝ) :=
    hendpointThreshold (Fintype.card (↑S : Set W))
      (hendpointScale.trans hdegree_card.le)
  have htarget_ceil : target ≤ (⌈target⌉₊ : ℝ) := Nat.le_ceil target
  have hceil_scale : ⌈target⌉₊ ≤ scale :=
    le_max_left ⌈target⌉₊
      (max d₀ (max windowThreshold endpointThreshold))
  by_cases hsubdivision : oneSubdivisionClique (degreeScale / 2) ⊑ K
  · let ellNat : ℕ := 2 * (degreeScale / 2)
    have hellNat : ellNat = 2 * scale := by
      simp [ellNat, degreeScale]
    have htarget_ell : target ≤ (ellNat : ℝ) := by
      calc
        target ≤ (⌈target⌉₊ : ℝ) := htarget_ceil
        _ ≤ (scale : ℝ) := by exact_mod_cast hceil_scale
        _ ≤ ((2 * scale : ℕ) : ℝ) := by
          exact_mod_cast (show scale ≤ 2 * scale by omega)
        _ = (ellNat : ℝ) := by rw [hellNat]
    have hexp6 : Real.exp 6 ≤ (ellNat : ℝ) :=
      (le_max_right requested (Real.exp 6)).trans htarget_ell
    have hlog6 := six_le_log_pow_eight_of_exp_six_le hexp6
    refine ⟨(ellNat : ℝ),
      (le_max_left requested (Real.exp 6)).trans htarget_ell, ?_⟩
    intro m hmEven hmLower hmUpper
    have hm6 : 6 ≤ m := by exact_mod_cast hlog6.trans hmLower
    have hmUpperNat : m ≤ ellNat := by exact_mod_cast hmUpper
    have hcopy : cycleGraph m ⊑ K :=
      every_even_cycle_isContained_of_oneSubdivisionClique hsubdivision
        hmEven hm6 (by simpa [ellNat] using hmUpperNat)
    have hcycleK : HasCycleLength K m :=
      (hasCycleLength_iff_cycleGraph_isContained (by omega)).2 hcopy
    exact hcycleK.lift_extracted hHG S
  · let ell : ℝ :=
      (Parameters.lmFloorEndpoint (Fintype.card (↑S : Set W)) : ℝ)
    have hell_target : target ≤ ell := by simpa [ell] using hendpoint
    have hell_exp : Real.exp 6 ≤ ell :=
      (le_max_right requested (Real.exp 6)).trans hell_target
    have hlog6 : (6 : ℝ) ≤ Real.log ell ^ 8 :=
      six_le_log_pow_eight_of_exp_six_le hell_exp
    have hvertex_degree_pos : 0 < K.degree vertex :=
      lt_of_lt_of_le hdegree_pos hdegree_nat
    obtain ⟨neighbor, hneighbor⟩ :=
      (K.degree_pos_iff_exists_adj vertex).1 hvertex_degree_pos
    have hpaths : ∀ q : ℕ,
        ParityCompatible partition vertex neighbor q →
        Real.log (Fintype.card (↑S : Set W) : ℝ) ^ 7 ≤ q →
        (q : ℝ) ≤
          Parameters.lmPathScale (Fintype.card (↑S : Set W) : ℝ) →
        HasPathBetweenLength K vertex neighbor q := by
      intro q hparity hlower hupper
      exact hexact K partition hd₀ hKexpander hKdegree hsubdivision
        hneighbor.ne hparity hlower hupper
    have hcyclesK := even_cycle_interval_of_exact_paths_on_edge
      partition hneighbor hwindow hpaths (by simpa [ell] using hlog6)
    refine ⟨ell,
      (le_max_left requested (Real.exp 6)).trans hell_target, ?_⟩
    intro m hmEven hmLower hmUpper
    exact (hcyclesK m hmEven (by simpa [ell] using hmLower)
      (by simpa [ell] using hmUpper)).lift_extracted hHG S

/-- The complete finite interval conclusion, with the sole remaining deep
input exposed as the literal robust simple-adjuster statement of Lemma 4.3.
This declaration verifies that the exact-path threshold and the final
subdivision/path dichotomy have precisely compatible interfaces. -/
theorem liuMontgomery_finite_even_cycle_intervals_of_robustAdjusters
    (hrobust : LMRobustSimpleAdjusterSupply.{u}) :
    ∀ (requested : ℝ), ∃ threshold : ℕ, 0 < threshold ∧
      ∀ {W : Type u} [Fintype W] [Nonempty W]
        (G : SimpleGraph W) [DecidableRel G.Adj],
        AvgDegreeAtLeast G threshold →
          ∃ ell : ℝ, requested ≤ ell ∧
            ∀ m : ℕ, Even m → Real.log ell ^ 8 ≤ m →
              (m : ℝ) ≤ ell → HasCycleLength G m := by
  obtain ⟨d₀, hexact⟩ :=
    eventually_exact_paths_of_robustSimpleAdjusterSupply hrobust
  exact finite_even_cycle_intervals_of_exact_paths d₀ (by
    intro W _ _ J _ _ B d hd hexp hdegree hfree x y q hxy hparity
      hlower hupper
    exact hexact J B hd hexp hdegree hfree hxy hparity hlower hupper)

/-- The unconditional finite even-cycle interval theorem obtained from
Liu--Montgomery Theorem 2.7.  This is the raw finite input consumed by the
power-tail argument. -/
theorem liuMontgomery_finite_even_cycle_intervals_raw :
    ∀ (requested : ℝ), ∃ threshold : ℕ, 0 < threshold ∧
      ∀ {W : Type u} [Fintype W] [Nonempty W]
        (G : SimpleGraph W) [DecidableRel G.Adj],
        AvgDegreeAtLeast G threshold →
          ∃ ell : ℝ, requested ≤ ell ∧
            ∀ m : ℕ, Even m → Real.log ell ^ 8 ≤ m →
              (m : ℝ) ≤ ell → HasCycleLength G m := by
  obtain ⟨d₀, hexact⟩ := liuMontgomery_theorem2_7
  exact finite_even_cycle_intervals_of_exact_paths d₀ (by
    intro W _ _ J _ _ B d hd hexp hdegree hfree x y q hxy hparity
      hlower hupper
    exact hexact J B hd hexp hdegree hfree hxy hparity hlower hupper)

end

end Erdos63
