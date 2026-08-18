/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos984.HunterBlueRadial
import ErdosProblems.Erdos984.HunterProbability

/-!
# Red progressions and the independent radial-label argument

This file connects Hunter's geometric recurrence statement to the exact
finite counting lemma.  A constraint is an `X`-term progression in `[0,N)`.
If it approaches each center in a `Y`-element opportunity set, then matching
one prescribed radial label makes one term blue and destroys the red
progression.  Exact counting chooses one labeling that works for every
constraint.
-/

namespace Erdos984

noncomputable section

/-- An `X`-term positive-step arithmetic progression contained in `[0,N)`,
encoded inside `Fin N × Fin N` for a direct `N^2` cardinality bound. -/
def BoundedAP (N X : ℕ) :=
  {p : Fin N × Fin N //
    0 < (p.2 : ℕ) ∧ (p.1 : ℕ) + (X - 1) * (p.2 : ℕ) < N}

instance (N X : ℕ) : Fintype (BoundedAP N X) := by
  unfold BoundedAP
  infer_instance

instance (N X : ℕ) : DecidableEq (BoundedAP N X) := Classical.decEq _

def BoundedAP.start {N X : ℕ} (P : BoundedAP N X) : ℕ := P.1.1

def BoundedAP.step {N X : ℕ} (P : BoundedAP N X) : ℕ := P.1.2

lemma BoundedAP.step_pos {N X : ℕ} (P : BoundedAP N X) : 0 < P.step := P.2.1

lemma BoundedAP.end_lt {N X : ℕ} (P : BoundedAP N X) :
    P.start + (X - 1) * P.step < N := P.2.2

lemma card_boundedAP_le_sq (N X : ℕ) :
    Fintype.card (BoundedAP N X) ≤ N ^ 2 := by
  calc
    Fintype.card (BoundedAP N X) ≤ Fintype.card (Fin N × Fin N) :=
      Fintype.card_le_of_injective Subtype.val Subtype.val_injective
    _ = N ^ 2 := by simp [pow_two]

/-- Cancel the unconstrained label coordinates from the exact counting
inequality. -/
lemma radial_label_count_of_base {M K Y S : ℕ} (hYM : Y ≤ M)
    (hbase : S * K ^ Y < (K + 1) ^ Y) :
    S * (K ^ Y * (K + 1) ^ (M - Y)) < (K + 1) ^ M := by
  have hcommon : 0 < (K + 1) ^ (M - Y) := by positivity
  calc
    S * (K ^ Y * (K + 1) ^ (M - Y)) =
        (S * K ^ Y) * (K + 1) ^ (M - Y) := by ac_rfl
    _ < (K + 1) ^ Y * (K + 1) ^ (M - Y) :=
      Nat.mul_lt_mul_of_pos_right hbase hcommon
    _ = (K + 1) ^ M := by
      rw [← pow_add]
      congr 1
      omega

/-- The paper's coarser `N²` union bound implies the exact count needed by
`exists_labeling_hits_all`. -/
lemma boundedAP_radial_label_count
    {ι : Type*} [Fintype ι] {K N X Y : ℕ}
    (hYM : Y ≤ Fintype.card ι)
    (hbase : N ^ 2 * K ^ Y < (K + 1) ^ Y) :
    Fintype.card (BoundedAP N X) *
        (K ^ Y * (K + 1) ^ (Fintype.card ι - Y)) <
      (K + 1) ^ Fintype.card ι := by
  apply radial_label_count_of_base hYM
  exact lt_of_le_of_lt
    (Nat.mul_le_mul_right (K ^ Y) (card_boundedAP_le_sq N X)) hbase

/-- The exact recurrence datum needed from Hunter's Fourier argument.  Each
progression has a finite set of distinct center indices, and each selected
center is reached by a progression term with the prescribed radial bin. -/
def RadialOpportunities
    {D ι : Type*} [Fintype D] [Fintype ι] [DecidableEq ι]
    {K N X : ℕ} (center : ι → UnitAddTorus D) (Δ : ℝ)
    (θ : UnitAddTorus D) (S : BoundedAP N X → Finset ι)
    (target : BoundedAP N X → ι → Fin (K + 1)) : Prop :=
  ∀ P j, j ∈ S P → ∃ t < X, ∃ u : EuclideanSpace ℝ D,
    additiveOrbit θ (P.start + t * P.step) =
      center j + euclideanToTorus u ∧
    (target P j : ℕ) = radialBin Δ u

/-- If every progression gets one matching radial label, none is entirely
red. -/
lemma hunterRadialColor_avoids_true_of_hits
    {D ι : Type*} [Fintype D] [Fintype ι] [DecidableEq ι]
    {K N X : ℕ} (hX : 2 ≤ X)
    (center : ι → UnitAddTorus D) {Δ : ℝ} (hΔ : 0 < Δ)
    (label : ι → Fin (K + 1)) (θ : UnitAddTorus D)
    (S : BoundedAP N X → Finset ι)
    (target : BoundedAP N X → ι → Fin (K + 1))
    (hopportunities : RadialOpportunities center Δ θ S target)
    (hhit : ∀ P, ∃ j ∈ S P, label j = target P j) :
    AvoidsColorAP (hunterRadialColor center Δ label θ) true N X := by
  intro a d hd hend
  have haN : a < N := by
    exact lt_of_le_of_lt (Nat.le_add_right a _) hend
  have hXm1 : 1 ≤ X - 1 := by omega
  have hdprod : d ≤ (X - 1) * d := by
    simpa only [one_mul] using Nat.mul_le_mul_right d hXm1
  have hdN : d < N := by
    exact lt_of_le_of_lt (hdprod.trans (Nat.le_add_left _ a)) hend
  let P : BoundedAP N X :=
    ⟨⟨⟨a, haN⟩, ⟨d, hdN⟩⟩, hd, hend⟩
  obtain ⟨j, hjS, hjlabel⟩ := hhit P
  obtain ⟨t, htX, u, horbit, htarget⟩ := hopportunities P j hjS
  refine ⟨t, htX, ?_⟩
  have hlabelNat : (label j : ℕ) = radialBin Δ u := by
    rw [hjlabel]
    exact htarget
  have hblue : additiveOrbit θ (P.start + t * P.step) ∈
      hunterRadialBlueSet center Δ label :=
    mem_hunterRadialBlueSet_of_label_eq_radialBin hΔ horbit hlabelNat
  have hcfalse : hunterRadialColor center Δ label θ
      (a + t * d) = false := by
    apply hunterRadialColor_eq_false_iff.2
    simpa [P, BoundedAP.start, BoundedAP.step] using hblue
  simp [hcfalse]

/-- Exact finite counting produces a radial labeling which destroys all red
`X`-term progressions. -/
lemma exists_labeling_avoids_true
    {D ι : Type*} [Fintype D] [Fintype ι] [DecidableEq ι]
    {K N X Y : ℕ} (hX : 2 ≤ X)
    (center : ι → UnitAddTorus D) {Δ : ℝ} (hΔ : 0 < Δ)
    (θ : UnitAddTorus D) (S : BoundedAP N X → Finset ι)
    (target : BoundedAP N X → ι → Fin (K + 1))
    (hS : ∀ P, (S P).card = Y)
    (hopportunities : RadialOpportunities center Δ θ S target)
    (hcount : Fintype.card (BoundedAP N X) *
        (K ^ Y * (K + 1) ^ (Fintype.card ι - Y)) <
      (K + 1) ^ Fintype.card ι) :
    ∃ label : ι → Fin (K + 1),
      AvoidsColorAP (hunterRadialColor center Δ label θ) true N X := by
  obtain ⟨label, hhit⟩ := exists_labeling_hits_all S target Y hS (by
    simpa using hcount)
  exact ⟨label, hunterRadialColor_avoids_true_of_hits hX center hΔ label θ
    S target hopportunities hhit⟩

/-- End-to-end finite combinatorial wrapper: geometric blue hypotheses and
Fourier recurrence opportunities, together with the exact label count,
produce a `(3,X)`-good coloring of `[0,N)`. -/
lemma exists_goodOffDiagonal_of_radial_opportunities
    {D ι : Type*} [Fintype D] [Fintype ι] [DecidableEq ι]
    {K N X Y : ℕ} (hX : 2 ≤ X)
    (center : ι → UnitAddTorus D) (Δ ρ : ℝ) (hΔ : 0 < Δ)
    (θ : UnitAddTorus D)
    (S : BoundedAP N X → Finset ι)
    (target : BoundedAP N X → ι → Fin (K + 1))
    (hS : ∀ P, (S P).card = Y)
    (hopportunities : RadialOpportunities center Δ θ S target)
    (hcount : Fintype.card (BoundedAP N X) *
        (K ^ Y * (K + 1) ^ (Fintype.card ι - Y)) <
      (K + 1) ^ Fintype.card ι)
    (hK : radialLower Δ (K + 1) ≤ ρ)
    (hsep : TorusCenterThreeSeparated center ρ)
    (hnowrap : 4 * ρ < 1)
    (hstep : ∀ d : ℕ, 0 < d → d < N →
      radialSquaredWidth Δ K < squaredNorm (centeredTorusLift (d • θ))) :
    ∃ color : ℕ → Bool, GoodOffDiagonal color N X := by
  obtain ⟨label, hred⟩ := exists_labeling_avoids_true hX center hΔ θ
    S target hS hopportunities hcount
  refine ⟨hunterRadialColor center Δ label θ, ?_, hred⟩
  exact hunterRadialColor_avoids_false_three center Δ ρ label θ N
    hΔ.le hK hsep hnowrap hstep

end

end Erdos984
