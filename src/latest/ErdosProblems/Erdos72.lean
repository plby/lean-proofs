/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
This is a Lean formalization of a solution to Erdős Problem 72.
https://www.erdosproblems.com/forum/thread/72

Informal authors:
- Jacques Verstraëte
- Hong Liu
- Richard Montgomery

Formal authors:
- Codex
- GPT-5.6 Sol

URLs:
- https://github.com/plby/lean-proofs/blob/main/ErdosProblems/Erdos72.md
-/
/-
This is a Lean formalization of the solution to Erdős Problem 72.
https://www.erdosproblems.com/72

Informal authors:
- J. Verstraëte (the first existence proof)
- H. Liu and R. Montgomery (the powers-of-two strengthening)

Formal author:
- OpenAI Codex
-/

import Mathlib
import Util.Density
import ErdosProblems.Erdos63.LiuMontgomery

namespace Erdos72

open Filter Set Topology

/-- `G` contains a simple cycle with exactly `m` edges. -/
def HasCycleLength {V : Type*} (G : SimpleGraph V) (m : ℕ) : Prop :=
  ∃ (v : V) (w : G.Walk v v), w.IsCycle ∧ w.length = m

lemma HasCycleLength.map {V W : Type*} {G : SimpleGraph V} {H : SimpleGraph W}
    (f : G ↪g H) {m : ℕ} (h : HasCycleLength G m) : HasCycleLength H m := by
  rcases h with ⟨v, w, hw, rfl⟩
  exact ⟨f v, w.map f.toHom, hw.map f.injective, by simp⟩

/-- The real average degree of a finite simple graph. -/
noncomputable def averageDegree {V : Type*} [Fintype V] (G : SimpleGraph V) : ℝ := by
  classical
  exact (2 * G.edgeFinset.card : ℝ) / Fintype.card V

/-- The explicit unavoidable set used in the Liu--Montgomery resolution. -/
def powersOfTwo : Set ℕ := Set.range fun k : ℕ ↦ 2 ^ k

private lemma powersOfTwo_prefix_ncard_le (N : ℕ) :
    (powersOfTwo ∩ Set.Iio N).ncard ≤ Nat.log 2 N + 1 := by
  classical
  let F : Finset ℕ :=
    (Finset.range (Nat.log 2 N + 1)).image fun k : ℕ ↦ 2 ^ k
  have hsub : powersOfTwo ∩ Set.Iio N ⊆ (F : Set ℕ) := by
    rintro x ⟨⟨k, rfl⟩, hkN⟩
    have hk : k ≤ Nat.log 2 N :=
      Nat.le_log_of_pow_le (by norm_num) hkN.le
    simp only [F, Finset.mem_coe, Finset.mem_image, Finset.mem_range]
    exact ⟨k, Nat.lt_succ_iff.mpr hk, rfl⟩
  calc
    (powersOfTwo ∩ Set.Iio N).ncard ≤ ((F : Finset ℕ) : Set ℕ).ncard :=
      Set.ncard_le_ncard hsub
    _ = F.card := Set.ncard_coe_finset F
    _ ≤ Nat.log 2 N + 1 := by
      simpa [F] using
        (Finset.card_image_le :
          ((Finset.range (Nat.log 2 N + 1)).image fun k : ℕ ↦ 2 ^ k).card ≤
            (Finset.range (Nat.log 2 N + 1)).card)

private lemma tendsto_natLog_two_add_one_div :
    Tendsto (fun N : ℕ ↦ ((Nat.log 2 N + 1 : ℕ) : ℝ) / N)
      atTop (𝓝 0) := by
  let g : ℕ → ℝ := fun N ↦ (Real.log (N : ℝ) / Real.log 2 + 1) / N
  have hlogDiv :
      Tendsto (fun N : ℕ ↦ Real.log (N : ℝ) / N) atTop (𝓝 0) := by
    simpa only [Function.comp_def, id_eq] using
      Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero.comp
        tendsto_natCast_atTop_atTop
  have hg : Tendsto g atTop (𝓝 0) := by
    have h :=
      ((tendsto_const_nhds (x := (Real.log 2)⁻¹)).mul hlogDiv).add
        (tendsto_one_div_atTop_nhds_zero_nat (𝕜 := ℝ))
    convert h using 1
    · funext N
      dsimp [g]
      ring
    · norm_num
  apply squeeze_zero'
  · filter_upwards with N
    positivity
  · filter_upwards [eventually_gt_atTop 0] with N hN
    have hlog : (Nat.log 2 N : ℝ) ≤ Real.log (N : ℝ) / Real.log 2 := by
      simpa [Real.logb] using Real.natLog_le_logb N 2
    change
      ((Nat.log 2 N + 1 : ℕ) : ℝ) / N ≤
        (Real.log (N : ℝ) / Real.log 2 + 1) / N
    apply div_le_div_of_nonneg_right
    · norm_num only [Nat.cast_add, Nat.cast_one]
      linarith
    · positivity
  · exact hg

/-- The powers of two have natural density zero. -/
theorem powersOfTwo_hasDensity : powersOfTwo.HasDensity 0 := by
  rw [Set.HasDensity]
  suffices h : Tendsto
      (fun N : ℕ ↦ ((powersOfTwo ∩ Set.Iio N).ncard : ℝ) / N)
      atTop (𝓝 0) by
    simpa only [Set.partialDensity, Set.inter_univ, Set.univ_inter,
      Set.ncard_Iio_nat] using h
  apply squeeze_zero'
  · filter_upwards with N
    positivity
  · filter_upwards with N
    have hcard :
        ((powersOfTwo ∩ Set.Iio N).ncard : ℝ) ≤
          ((Nat.log 2 N + 1 : ℕ) : ℝ) := by
      exact_mod_cast powersOfTwo_prefix_ncard_le N
    exact div_le_div_of_nonneg_right hcard (by positivity)
  · exact tendsto_natLog_two_add_one_div

/-- The literal finite-graph assertion in Erdős Problem 72.  Graphs on `n`
vertices are represented on `Fin n`, which loses no information up to graph
isomorphism. -/
def ResolutionStatement : Prop :=
  ∃ A : Set ℕ, A.HasDensity 0 ∧
    ∃ c : ℝ, 0 < c ∧
      ∃ N₀ : ℕ, ∀ n, N₀ ≤ n → ∀ G : SimpleGraph (Fin n),
        c ≤ averageDegree G → ∃ m ∈ A, HasCycleLength G m

/-- The graph-theoretic content of Liu--Montgomery Corollary 1.3,
specialized to powers of two and to graphs on `Fin n`. -/
def PowerTwoUnavoidable : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∀ n (G : SimpleGraph (Fin n)),
    c ≤ averageDegree G → ∃ k : ℕ, HasCycleLength G (2 ^ k)

/-- Once the deep graph theorem is available, its assembly with the
density-zero calculation is elementary. -/
theorem resolution_of_powerTwoUnavoidable
    (h : PowerTwoUnavoidable) : ResolutionStatement := by
  rcases h with ⟨c, hc, hcycle⟩
  refine ⟨powersOfTwo, powersOfTwo_hasDensity, c, hc, 1, ?_⟩
  intro n hn G hdegree
  obtain ⟨k, hk⟩ := hcycle n G hdegree
  exact ⟨2 ^ k, ⟨k, rfl⟩, hk⟩

/-- Liu--Montgomery's finite power-tail theorem implies the literal
power-of-two unavoidability assertion used above.  This lemma also performs
the conversion from the division-free natural average-degree convention in
`Erdos63` to the real quotient occurring in the problem statement. -/
theorem powerTwoUnavoidable : PowerTwoUnavoidable := by
  obtain ⟨d, hd, htail⟩ := Erdos63.liuMontgomery_finitePowerTail (lower := 0)
  have hdReal : (0 : ℝ) < d := by exact_mod_cast hd
  refine ⟨d, hdReal, ?_⟩
  intro n G haverage
  by_cases hn : n = 0
  · subst n
    simp [averageDegree] at haverage
    linarith
  · have hnPos : 0 < n := Nat.pos_of_ne_zero hn
    let _ : Nonempty (Fin n) := Fin.pos_iff_nonempty.mp hnPos
    let _ : DecidableRel G.Adj := Classical.decRel G.Adj
    have hnReal : (0 : ℝ) < n := by exact_mod_cast hnPos
    have haverage' : (d : ℝ) ≤
        ((2 * G.edgeFinset.card : ℕ) : ℝ) / n := by
      simpa [averageDegree, Nat.cast_mul] using haverage
    have hmul : (d : ℝ) * n ≤ (2 * G.edgeFinset.card : ℕ) :=
      (le_div_iff₀ hnReal).mp haverage'
    have hnat : d * n ≤ 2 * G.edgeFinset.card := by
      exact_mod_cast hmul
    have havg : Erdos63.AvgDegreeAtLeast G d :=
      (Erdos63.avgDegreeAtLeast_iff_twice_card_edgeFinset G d).2 (by
        simpa using hnat)
    obtain ⟨k, _hkNonnegative, x, w, hwCycle, hwLength⟩ := htail G havg
    exact ⟨k, x, w, hwCycle, hwLength⟩

/-- Erdős Problem 72, resolved with the density-zero set of powers of two. -/
theorem erdos_72 :
    ∃ A : Set ℕ, A.HasDensity 0 ∧
      ∃ c : ℝ, 0 < c ∧
        ∃ N₀ : ℕ, ∀ n, N₀ ≤ n → ∀ G : SimpleGraph (Fin n),
          c ≤ averageDegree G → ∃ m ∈ A, HasCycleLength G m :=
  resolution_of_powerTwoUnavoidable powerTwoUnavoidable

end Erdos72

#print axioms Erdos72.erdos_72
