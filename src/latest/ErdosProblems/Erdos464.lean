/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/- This file has been modified for Lean/Mathlib 4.33.0. -/
/-
Erdős Problem 464.
Informal author: Bernard de Mathan.
Formal authors: Aristotle, JoshuaB.
Source: https://www.erdosproblems.com/forum/thread/464#post-7120
https://aristotle.harmonic.fun/dashboard/requests/f9894d2d-4bb1-42da-9301-e508aa881b17
Original Lean version: 4.28.0, confirmed by the user who supplied the source files.
The original Mathlib revision and a license notice were not supplied.
-/
import Mathlib
import ErdosProblems.Erdos464.NDist
import ErdosProblems.Erdos464.Uncountable
import ErdosProblems.Erdos464.Refinement
import ErdosProblems.Erdos464.Construction

set_option linter.mathlibStandardSet false

namespace Erdos464

/-!
# de Mathan's theorem (linear / lacunary case)

**Statement.** Let `a : ℕ → ℕ` be a lacunary sequence: strictly increasing with
`(1 + ε₀) · a k ≤ a (k+1)` for some `ε₀ > 0`.  Then there exists an irrational `θ` such that the
set of nearest-integer distances `{ ‖θ · a k‖ : k }` (here `‖x‖ = |x - round x|`, the distance to
the nearest integer) does **not** accumulate at `0`; consequently the sequence `(θ · a k)` is not
dense modulo `1`.

Since each `‖θ · a k‖` lies in `[0, 1/2]`, the literal phrasing "not dense in `[0,1]`" is automatic;
the meaningful (and stronger) statement we prove is that `0` is not a limit point of the set, i.e.
the values stay bounded away from `0`.
-/

/-
**de Mathan's theorem, linear case.** For a lacunary sequence `a`, there is an irrational `θ`
whose nearest-integer-distance values `‖θ · a k‖` stay bounded away from `0` (so the set
`{‖θ · a k‖}` is not dense in `[0,1]`; `0` is not an accumulation point).
-/
theorem erdos_464
    (a : ℕ → ℕ) (ha : StrictMono a) (ha0 : 0 < a 0)
    (ε₀ : ℝ) (hε₀ : 0 < ε₀) (hlac : ∀ k, (1 + ε₀) * (a k : ℝ) ≤ a (k + 1)) :
    ∃ θ : ℝ, Irrational θ ∧
      (0 : ℝ) ∉ closure
        (Set.range (fun k : ℕ => |θ * (a k : ℝ) - (round (θ * (a k : ℝ)) : ℝ)|)) := by
  -- Apply `exists_refinement` to get `Q` with the required properties.
  obtain ⟨Q, hQpos, hloQ, hhiQ, hrange⟩ := exists_refinement a ha0 (1 + ε₀) (by linarith) hlac;
  -- Apply `exists_setup` to get `S` with `S.Q = Q`.
  obtain ⟨S, hSQ⟩ := exists_setup Q (Real.sqrt (1 + ε₀)) (1 + ε₀) (by
  exact Real.lt_sqrt_of_sq_lt ( by linarith )) (by
  rw [ Real.sqrt_le_left ] <;> nlinarith) hQpos hloQ hhiQ;
  -- From `S.solution_uncountable` and `exists_irrational_of_not_countable`, obtain `θ` with `Irrational θ` and `hθ : ∀ m, 1 ≤ m → S.eps ≤ ndist (S.Q m * θ)`.
  obtain ⟨θ, hθ_irr, hθ⟩ : ∃ θ : ℝ, Irrational θ ∧ ∀ m, 1 ≤ m → S.eps ≤ ndist (S.Q m * θ) := by
    have := exists_irrational_of_not_countable ( Setup.solution_uncountable S );
    tauto;
  refine' ⟨ θ, hθ_irr, _ ⟩;
  -- Define `δ := min S.eps (ndist (θ * (a 0 : ℝ)))`.
  set δ := min S.eps (ndist (θ * (a 0 : ℝ))) with hδ_def;
  -- Claim: `∀ k, δ ≤ |θ * (a k:ℝ) - (round (θ * (a k:ℝ)):ℝ)|`, i.e. `δ ≤ ndist (θ * (a k:ℝ))`.
  have hδ_le : ∀ k, δ ≤ ndist (θ * (a k : ℝ)) := by
    intro k
    by_cases hk : k = 0;
    · aesop;
    · obtain ⟨ n, hn ⟩ := hrange k;
      by_cases hn1 : 1 ≤ n <;> simp_all +decide [ mul_comm ];
      · exact Or.inl ( by simpa only [ ← hn ] using hθ n hn1 );
      · have := hrange 0; obtain ⟨ m, hm ⟩ := this; have := hloQ 0; have := hhiQ 0; simp_all +decide ;
        exact absurd hm ( by linarith [ show ( a 0 : ℝ ) < a k from mod_cast ha ( Nat.pos_of_ne_zero hk ), show ( Q m : ℝ ) ≥ Q 0 from Nat.recOn m ( by norm_num ) fun n ihn => by nlinarith [ hloQ n, hhiQ n, hQpos n, Real.sqrt_nonneg ( 1 + ε₀ ), Real.mul_self_sqrt ( show 0 ≤ 1 + ε₀ by positivity ) ] ] );
  exact zero_notMem_closure_range ( show 0 < δ from lt_min ( S.eps_pos ) ( ndist_pos_of_irrational <| hθ_irr.mul_natCast <| by linarith ) ) hδ_le

#print axioms erdos_464
-- 'Erdos464.erdos_464' depends on axioms: [propext, Classical.choice, Quot.sound]

end Erdos464
