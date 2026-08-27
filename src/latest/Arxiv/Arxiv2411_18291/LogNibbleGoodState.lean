import Arxiv.Arxiv2411_18291.LogNibbleTrackedProcess
import Arxiv.Arxiv2411_18291.NibbleGoodState

/-! # Actual count, live-edge, and face bounds on the logarithmic good event -/

open Finset MeasureTheory ProbabilityTheory

noncomputable section

namespace Arxiv2411_18291.CliqueRemovalProcess

variable {V : Type*} [Fintype V] [DecidableEq V] {q r : ℕ}
variable {G : Hypergraph V (r + 1)} {H : Finset (Block V q)} {a D : ℝ}
variable {i : ℕ} {ω : ℕ → State V q}

theorem logNibbleGood_clique_deviation (hgood : ω ∈ logNibbleGood G H a D i) :
    let k := q.choose (r + 1)
    let p := removalDensity k G.card i
    |((remainingCliques (r + 1) H (trajectoryCliques ω i)).card : ℝ) -
      nibbleCliqueMain k G.card D p| ≤ logNibbleCliqueError k a G.card D p := by
  have hu := hgood (.inl true)
  have hl := hgood (.inl false)
  dsimp only
  change _ - (nibbleCliqueMain _ _ _ _ + logNibbleCliqueError _ _ _ _ _) < 0 at hu
  change -(_ - (nibbleCliqueMain _ _ _ _ - logNibbleCliqueError _ _ _ _ _)) < 0 at hl
  exact abs_le.mpr ⟨by linarith only [hl], by linarith only [hu]⟩

theorem logNibbleGood_remaining_nonempty {p₀ : ℝ}
    (P : LogNibbleParameters (q.choose (r + 1)) a G.card D p₀
      ((Fintype.card V : ℝ) ^ (q - (r + 1) - 1)))
    (hi : p₀ ≤ removalDensity (q.choose (r + 1)) G.card i)
    (hgood : ω ∈ logNibbleGood G H a D i) :
    (remainingCliques (r + 1) H (trajectoryCliques ω i)).Nonempty := by
  have hl := hgood (.inl false)
  have hc := P.clique_lower_pos hi
    (removalDensity_le_one (q.choose (r + 1)) P.graph_pos i)
  change -(((remainingCliques (r + 1) H (trajectoryCliques ω i)).card : ℝ) -
    logNibbleCliqueLower _ _ _ _ _) < 0 at hl
  have hpos : (0 : ℝ) < (remainingCliques (r + 1) H (trajectoryCliques ω i)).card := by
    linarith only [hl, hc]
  exact card_pos.mp (by exact_mod_cast hpos)

theorem logNibbleGood_live_degree_bounds {p₀ : ℝ}
    (P : LogNibbleParameters (q.choose (r + 1)) a G.card D p₀
      ((Fintype.card V : ℝ) ^ (q - (r + 1) - 1)))
    (hi : p₀ ≤ removalDensity (q.choose (r + 1)) G.card i)
    (hgood : ω ∈ logNibbleGood G H a D i)
    (hsupport : ∀ j, ω (j + 1) ∈ (step (r + 1) H j (Preorder.frestrictLe j ω)).support)
    (e : Block V (r + 1)) (heG : e ∈ G)
    (he : e ∉ cliqueSupport (r + 1) (trajectoryCliques ω i)) :
    let k := q.choose (r + 1)
    let p := removalDensity k G.card i
    let x := (((remainingCliques (r + 1) H (trajectoryCliques ω i)).filter
      fun Q => e.val ⊆ Q.val).card : ℝ)
    nibbleDegreeMain k D p - logNibbleDegreeError k a D p ≤ x ∧
      x ≤ nibbleDegreeMain k D p + logNibbleDegreeError k a D p := by
  have hR := logNibbleGood_remaining_nonempty P hi hgood
  have hu := hgood (.inr (.inl (e, true)))
  have hl := hgood (.inr (.inl (e, false)))
  change (if e ∈ G then frozenEdgeProcess H e (logNibbleDegreeUpperComparison _ _ _ _) i ω
    else -2 * (a ^ 2 * D)) < 0 at hu
  change (if e ∈ G then -frozenEdgeProcess H e (logNibbleDegreeLowerComparison _ _ _ _) i ω
    else -2 * (a ^ 2 * D)) < 0 at hl
  rw [if_pos heG] at hu hl
  rw [frozenEdgeProcess_eq_of_remaining_nonempty H ω hsupport e _ i hR he] at hu hl
  change _ - (nibbleDegreeMain _ _ _ + logNibbleDegreeError _ _ _ _) < 0 at hu
  change -(_ - (nibbleDegreeMain _ _ _ - logNibbleDegreeError _ _ _ _)) < 0 at hl
  dsimp only
  exact ⟨by linarith only [hl], by linarith only [hu]⟩

theorem logNibbleGood_remaining_degree_bounds {p₀ : ℝ}
    (P : LogNibbleParameters (q.choose (r + 1)) a G.card D p₀
      ((Fintype.card V : ℝ) ^ (q - (r + 1) - 1)))
    (hi : p₀ ≤ removalDensity (q.choose (r + 1)) G.card i)
    (hgood : ω ∈ logNibbleGood G H a D i)
    (hsupport : ∀ j, ω (j + 1) ∈ (step (r + 1) H j (Preorder.frestrictLe j ω)).support) :
    let k := q.choose (r + 1)
    let p := removalDensity k G.card i
    let R := remainingCliques (r + 1) H (trajectoryCliques ω i)
    ∀ e ∈ G \ cliqueSupport (r + 1) (trajectoryCliques ω i),
      nibbleDegreeMain k D p - logNibbleDegreeError k a D p ≤
          ((R.filter fun Q => e.val ⊆ Q.val).card : ℝ) ∧
        ((R.filter fun Q => e.val ⊆ Q.val).card : ℝ) ≤
          nibbleDegreeMain k D p + logNibbleDegreeError k a D p := by
  dsimp only
  intro e he
  exact logNibbleGood_live_degree_bounds P hi hgood hsupport e (mem_sdiff.mp he).1
    (mem_sdiff.mp he).2

theorem logNibbleGood_covered_degree_bounds {p₀ : ℝ}
    (P : LogNibbleParameters (q.choose (r + 1)) a G.card D p₀
      ((Fintype.card V : ℝ) ^ (q - (r + 1) - 1)))
    (hHG : ∀ Q ∈ H, cliqueEdges (r + 1) Q ⊆ G)
    (hi : p₀ ≤ removalDensity (q.choose (r + 1)) G.card i)
    (hgood : ω ∈ logNibbleGood G H a D i)
    (hsupport : ∀ j, ω (j + 1) ∈ (step (r + 1) H j (Preorder.frestrictLe j ω)).support) :
    let k := q.choose (r + 1)
    let p := removalDensity k G.card i
    let R := remainingCliques (r + 1) H (trajectoryCliques ω i)
    ∀ e : Block V (r + 1), (R.filter fun Q => e.val ⊆ Q.val).Nonempty →
      nibbleDegreeMain k D p - logNibbleDegreeError k a D p ≤
          ((R.filter fun Q => e.val ⊆ Q.val).card : ℝ) ∧
        ((R.filter fun Q => e.val ⊆ Q.val).card : ℝ) ≤
          nibbleDegreeMain k D p + logNibbleDegreeError k a D p := by
  dsimp only
  intro e he
  obtain ⟨Q', hQ'⟩ := he
  obtain ⟨hQR, heQ⟩ := mem_filter.mp hQ'
  have heG := hHG Q' (remainingCliques_subset H (trajectoryCliques ω i) hQR)
    ((mem_cliqueEdges e Q').mpr heQ)
  exact logNibbleGood_live_degree_bounds P hi hgood hsupport e heG
    (remaining_covered_edge_not_removed (trajectoryCliques ω i) e ⟨Q', hQ'⟩)

theorem logNibbleGood_face_bound (hgood : ω ∈ logNibbleGood G H a D i) (f : Block V r) :
    (((G \ cliqueSupport (r + 1) (trajectoryCliques ω i)).filter
      fun e => f.val ⊆ e.val).card : ℝ) ≤
      logNibbleFaceUpper a (Fintype.card V)
        (G.filter fun e => f.val ⊆ e.val).card
        (removalDensity (q.choose (r + 1)) G.card i) := by
  have h := hgood (.inr (.inr f))
  change _ - logNibbleFaceUpper _ _ _ _ < 0 at h
  linarith only [h]

end Arxiv2411_18291.CliqueRemovalProcess
