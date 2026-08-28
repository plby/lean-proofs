import Wikipedia.SmoothSixDPoincare.FiberMotionRestriction
import Wikipedia.SmoothSixDPoincare.FiniteGraphMotion
import Wikipedia.SmoothSixDPoincare.RankThreeWhitneyModel

/-!
# The actual supported five-dimensional Whitney model motion

The already constructed finite motion preserves every normal coordinate.
Restrict it to the split five-dimensional normal submodel. The inverse also
preserves that submodel, the support projects to a compact subset of the
prescribed open source, and exact tracking and separation are retained.
-/

noncomputable section

open Set Function
open scoped ContDiff Manifold

namespace Wikipedia.SmoothSixDPoincare.RankThreeWhitneyModel

open WhitneyPairModel (bigon)

def lowerSplit : (Lower × ℝ) ≃L[ℝ] WhitneyPairModel.Plane :=
  ContinuousLinearEquiv.ofFinrankEq (by
    simp [Lower, WhitneyPairModel.Plane, Module.finrank_prod])

def lowerInclude : Lower →L[ℝ] WhitneyPairModel.Plane :=
  lowerSplit.toContinuousLinearMap.comp (ContinuousLinearMap.inl ℝ Lower ℝ)

def lowerProject : WhitneyPairModel.Plane →L[ℝ] Lower :=
  (ContinuousLinearMap.fst ℝ Lower ℝ).comp lowerSplit.symm.toContinuousLinearMap

theorem lowerProject_include (u : Lower) : lowerProject (lowerInclude u) = u := by
  change (lowerSplit.symm (lowerSplit (u, 0))).1 = u
  rw [lowerSplit.symm_apply_apply]

def normalInclude : (Lower × Upper) →L[ℝ] (WhitneyPairModel.Plane × WhitneyPairModel.Plane) :=
  lowerInclude.prodMap (ContinuousLinearMap.id ℝ Upper)

def normalProject : (WhitneyPairModel.Plane × WhitneyPairModel.Plane) →L[ℝ] (Lower × Upper) :=
  lowerProject.prodMap (ContinuousLinearMap.id ℝ Upper)

theorem normalProject_include : LeftInverse normalProject normalInclude :=
  fun z => Prod.ext (lowerProject_include z.1) rfl

def expand : Space →L[ℝ] WhitneyPairModel.Space := FiberRestriction.embed normalInclude

def collapse : WhitneyPairModel.Space →L[ℝ] Space := FiberRestriction.project normalProject

theorem collapse_expand (z : Space) : collapse (expand z) = z :=
  FiberRestriction.project_embed normalInclude normalProject normalProject_include z

theorem expand_zero (p : ℝ × ℝ) : expand (p, 0) = (p, 0) :=
  Prod.ext rfl normalInclude.map_zero

theorem collapse_zero (p : ℝ × ℝ) : collapse (p, 0) = (p, 0) :=
  Prod.ext rfl normalProject.map_zero

def verticalGraph (B : ℝ → ℝ) (t s : ℝ) : Space := ((s, t * B s), 0)

theorem collapse_verticalGraph (B : ℝ → ℝ) (t s : ℝ) :
    collapse (WhitneyPairModel.verticalGraph B t s) = verticalGraph B t s :=
  collapse_zero _

/-- All maps and diffeomorphisms here live in the genuine five-dimensional model. -/
structure GraphMotion (h : ℝ) (U : Set Space) where
  height : ℝ → ℝ
  nonneg_height : ∀ s, 0 ≤ height s
  above : ∀ s, |s| ≤ 1 → h * (1 - s ^ 2) < height s
  support : Set Space
  compact_support : IsCompact support
  support_subset : support ⊆ U
  family : ℝ × Space → Space
  smooth : ContDiff ℝ ∞ family
  initial : ∀ z, family (0, z) = z
  diffeomorph : ∀ t, ∃ d : Diffeomorph 𝓘(ℝ, Space) 𝓘(ℝ, Space) Space Space ∞,
    ∀ z, d z = family (t, z)
  fixed : ∀ t z, z ∉ support → family (t, z) = z
  horizontal : ∀ t z, (family (t, z)).1.1 = z.1.1
  normal : ∀ t z, (family (t, z)).2 = z.2
  tracking : ∀ s, family (1, firstSheet (s, 0)) = verticalGraph height 1 s

/-- Restriction transfers the proved finite motion,
with compact support and exact tracking. -/
theorem nonempty_graphMotion {h : ℝ} (hh : 0 < h) {U : Set Space} (hU : IsOpen U)
    (hKU : ∀ p ∈ bigon h, (p, (0 : Lower × Upper)) ∈ U) :
    Nonempty (GraphMotion h U) := by
  let V : Set WhitneyPairModel.Space := collapse ⁻¹' U
  have hV : IsOpen V := hU.preimage collapse.continuous
  have hKV : MapsTo WhitneyPairModel.bigonEmbedding (bigon h) V := by
    intro p hp
    change collapse (p, 0) ∈ U
    rw [collapse_zero]
    exact hKU p hp
  obtain ⟨g⟩ := WhitneyPairModel.nonempty_graphMotionData hh hV hKV
  obtain ⟨a⟩ := g.nonempty_graphMotion
  let A : ℝ × Space → Space := fun p => collapse (a.family (p.1, expand p.2))
  have hA : ContDiff ℝ ∞ A :=
    collapse.contDiff.comp (a.smooth.comp
      (contDiff_fst.prodMk (expand.contDiff.comp contDiff_snd)))
  refine ⟨{
    height := g.height
    nonneg_height := g.nonneg_height
    above := g.above
    support := collapse '' a.support
    compact_support := a.compact_support.image collapse.continuous
    support_subset := ?_
    family := A
    smooth := hA
    initial := ?_
    diffeomorph := ?_
    fixed := ?_
    horizontal := ?_
    normal := ?_
    tracking := ?_ }⟩
  · rintro _ ⟨z, hz, rfl⟩
    exact a.support_subset hz
  · intro z
    change collapse (a.family (0, expand z)) = z
    rw [a.initial, collapse_expand]
  · intro t
    obtain ⟨d, hd⟩ := a.diffeomorph t
    have hn : ∀ z, (d z).2 = z.2 := by
      intro z
      rw [hd]
      exact a.normal t z
    refine ⟨FiberRestriction.restrict normalInclude normalProject normalProject_include d hn, ?_⟩
    intro z
    change collapse (d (expand z)) = collapse (a.family (t, expand z))
    rw [hd]
  · intro t z hz
    have hz' : expand z ∉ a.support := fun hs => hz ⟨expand z, hs, collapse_expand z⟩
    change collapse (a.family (t, expand z)) = z
    rw [a.fixed t _ hz', collapse_expand]
  · intro t z
    change (a.family (t, expand z)).1.1 = z.1.1
    rw [a.horizontal]
    rfl
  · intro t z
    change normalProject (a.family (t, expand z)).2 = z.2
    rw [a.normal]
    exact normalProject_include z.2
  · intro s
    have he : expand (firstSheet (s, 0)) = WhitneyPairModel.firstSheet (s, 0) :=
      expand_zero (s, 0)
    change collapse (a.family (1, expand (firstSheet (s, 0)))) = verticalGraph g.height 1 s
    rw [he, a.tracking, collapse_verticalGraph]

/-- Preserved coordinates force every possible intersection onto the exactly tracked center line. -/
theorem GraphMotion.firstSheet_ne_secondSheet {h : ℝ} {U : Set Space}
    (a : GraphMotion h U) (hh : 0 < h) (p : LowerSheet) (q : UpperSheet) :
    a.family (1, firstSheet p) ≠ secondSheet h q := by
  intro heq
  have hst : p.1 = q.1 := by
    have he := congrArg (fun z : Space => z.1.1) heq
    rw [a.horizontal] at he
    exact he
  have hu : p.2 = 0 := by
    have he := congrArg (fun z : Space => z.2) heq
    rw [a.normal] at he
    exact congrArg Prod.fst he
  have hp : p = (q.1, 0) := Prod.ext hst hu
  rw [hp, a.tracking] at heq
  have ht : a.height q.1 = h * (1 - q.1 ^ 2) := by
    simpa only [verticalGraph, secondSheet, one_mul] using
      congrArg (fun z : Space => z.1.2) heq
  have hheight : 0 ≤ h * (1 - q.1 ^ 2) := ht ▸ a.nonneg_height q.1
  have hlevel : 0 ≤ 1 - q.1 ^ 2 := nonneg_of_mul_nonneg_right hheight hh
  have habs : |q.1| ≤ 1 := abs_le.mpr
    ⟨by nlinarith [sq_nonneg (q.1 + 1)], by nlinarith [sq_nonneg (q.1 - 1)]⟩
  exact (a.above q.1 habs).ne ht.symm

theorem GraphMotion.disjoint_ranges {h : ℝ} {U : Set Space}
    (a : GraphMotion h U) (hh : 0 < h) :
    Disjoint (range (fun p => a.family (1, firstSheet p))) (range (secondSheet h)) := by
  rw [Set.disjoint_left]
  rintro z ⟨p, rfl⟩ ⟨q, hq⟩
  exact a.firstSheet_ne_secondSheet hh p q hq.symm

end Wikipedia.SmoothSixDPoincare.RankThreeWhitneyModel
