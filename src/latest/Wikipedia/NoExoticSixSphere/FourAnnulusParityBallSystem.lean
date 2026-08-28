import Wikipedia.NoExoticSixSphere.FourAnnulusChartedParityBall
import Wikipedia.NoExoticSixSphere.AnnulusDoublePointSingularBoundary

/-!
# A finite disjoint system of original annulus parity-one balls

The index set is the original intrinsic singular set. Finite Hausdorff
separation and arbitrarily small local balls make their closed regions
pairwise disjoint. They can all be placed in the active middle annulus,
so both original protected end collars remain untouched.
-/

noncomputable section

open Set Function Metric Topology
open scoped Manifold ContDiff

namespace NoExoticSixSphere.GenericFourAnnulus

open GLOrthonormalization AnnulusDoublePoints SphereAnnulus

variable {M : Type*} [TopologicalSpace M] [ChartedSpace (Vector 7) M]

structure ParityBallSystem (g : Vector 4 → M) where
  finite_singular : (singularSet g).Finite
  ball : ∀ x : singularSet g, ParityBall g x.val
  pairwise_disjoint : Pairwise (fun x y ↦ Disjoint (ball x).closedRegion (ball y).closedRegion)

namespace ParityBallSystem

variable {g : Vector 4 → M} (P : ParityBallSystem g)

def openHoles : Set (Vector 4) := ⋃ x, (P.ball x).openRegion

def closedHoles : Set (Vector 4) := ⋃ x, (P.ball x).closedRegion

def linkingBoundary : Set (Vector 4) := ⋃ x, (P.ball x).boundaryRegion

theorem isOpen_openHoles : IsOpen P.openHoles :=
  isOpen_iUnion (fun x ↦ (P.ball x).isOpen_openRegion)

theorem isCompact_closedHoles : IsCompact P.closedHoles := by
  let := P.finite_singular.to_subtype
  exact isCompact_iUnion (fun x ↦ (P.ball x).isCompact_closedRegion)

theorem openHoles_subset_closedHoles : P.openHoles ⊆ P.closedHoles :=
  iUnion_mono (fun x ↦ (P.ball x).openRegion_subset_closedRegion)

theorem closedHoles_subset_interior : P.closedHoles ⊆ openDomain 3 :=
  iUnion_subset (fun x ↦ (P.ball x).closedRegion_subset_interior)

theorem singular_subset_openHoles : singularSet g ⊆ P.openHoles := by
  intro x hx
  exact mem_iUnion.mpr ⟨⟨x, hx⟩, (P.ball ⟨x, hx⟩).center_mem_openRegion⟩

theorem linkingBoundary_disjoint_singular : Disjoint P.linkingBoundary (singularSet g) := by
  apply disjoint_iUnion_left.mpr
  exact fun x ↦ (P.ball x).boundaryRegion_disjoint_singular.mono subset_rfl inter_subset_right

theorem closedHoles_sdiff_openHoles : P.closedHoles \ P.openHoles = P.linkingBoundary := by
  ext x
  constructor
  · rintro ⟨hx, hxnot⟩
    obtain ⟨q, hq⟩ := mem_iUnion.mp hx
    apply mem_iUnion.mpr
    refine ⟨q, ?_⟩
    rw [← (P.ball q).closedRegion_sdiff_openRegion]
    exact ⟨hq, fun ho ↦ hxnot (mem_iUnion.mpr ⟨q, ho⟩)⟩
  · intro hx
    obtain ⟨q, hq⟩ := mem_iUnion.mp hx
    rw [← (P.ball q).closedRegion_sdiff_openRegion] at hq
    refine ⟨mem_iUnion.mpr ⟨q, hq.1⟩, ?_⟩
    intro ho
    obtain ⟨w, hw⟩ := mem_iUnion.mp ho
    by_cases he : q = w
    · subst w
      exact hq.2 hw
    · exact disjoint_left.mp (P.pairwise_disjoint he) hq.1
        ((P.ball w).openRegion_subset_closedRegion hw)

theorem closure_openHoles : closure P.openHoles = P.closedHoles := by
  apply le_antisymm
  · exact closure_minimal P.openHoles_subset_closedHoles P.isCompact_closedHoles.isClosed
  · apply iUnion_subset
    intro x
    rw [← (P.ball x).closure_openRegion]
    exact closure_mono (subset_iUnion (fun y ↦ (P.ball y).openRegion) x)

theorem frontier_openHoles : frontier P.openHoles = P.linkingBoundary := by
  rw [frontier, P.closure_openHoles, P.isOpen_openHoles.interior_eq,
    P.closedHoles_sdiff_openHoles]

theorem exists_of_small_balls_in_open (g : Vector 4 → M) (hfin : (singularSet g).Finite)
    (W : Set (Vector 4)) (hW : IsOpen W) (hsW : singularSet g ⊆ W)
    (hlocal : ∀ x ∈ singularSet g, ∀ N : Set (Vector 4), IsOpen N → x ∈ N →
      ∃ B : ParityBall g x, B.closedRegion ⊆ N) :
    ∃ P : ParityBallSystem g, P.closedHoles ⊆ W := by
  obtain ⟨U, hU, hdisj⟩ := hfin.t2_separation
  choose B hB using fun x : singularSet g ↦ hlocal x.val x.property (U x.val ∩ W)
    ((hU x.val).2.inter hW) ⟨(hU x.val).1, hsW x.property⟩
  let P : ParityBallSystem g := {
    finite_singular := hfin
    ball := B
    pairwise_disjoint := by
      intro x y hne
      exact (hdisj x.property y.property (fun he ↦ hne (Subtype.ext he))).mono
        ((hB x).trans inter_subset_left) ((hB y).trans inter_subset_left) }
  refine ⟨P, ?_⟩
  exact iUnion_subset (fun x ↦ (hB x).trans inter_subset_right)

end ParityBallSystem

theorem exists_parityBallSystem (e : EuclideanEmbedding 7 M) (g : Vector 4 → M)
    (hg : ∀ x ∈ domain 3, ContMDiffAt (𝓡 4) (𝓡 7) ∞ g x)
    (r₀ r₁ : ℝ) (hr₀ : 1 < r₀) (hr₁ : r₁ < 2)
    (hi : ∀ x ∈ domain 3, ‖x‖ ≤ r₀ ∨ r₁ ≤ ‖x‖ →
      Injective (fderiv ℝ (e.toFun ∘ g) x))
    (C : Set (PartialDiffeomorph (𝓡 7) (𝓡 7) M (Vector 7) ∞))
    (hC : ∀ y : M, ∃ c ∈ C, y ∈ c.source)
    (hgen : ∀ c ∈ C, OperatorRank.RegularFourSevenOn
      (fun x ↦ fderiv ℝ (c ∘ g) x) {x | (r₀ < ‖x‖ ∧ ‖x‖ < r₁) ∧ g x ∈ c.source}) :
    ∃ P : ParityBallSystem g, P.closedHoles ⊆ {x | r₀ < ‖x‖ ∧ ‖x‖ < r₁} := by
  apply ParityBallSystem.exists_of_small_balls_in_open g
    (finite_singular_of_chart_jets e g hg r₀ r₁ hr₀ hr₁ hi C hC hgen)
    {x | r₀ < ‖x‖ ∧ ‖x‖ < r₁}
    ((isOpen_lt continuous_const continuous_norm).inter
      (isOpen_lt continuous_norm continuous_const))
  · intro x hx
    have hnot : ¬ (‖x‖ ≤ r₀ ∨ r₁ ≤ ‖x‖) := by
      intro hend
      exact hx.2 ((GenericFourDisk.injective_embedded_derivative_iff e g x
        ((hg x hx.1).mdifferentiableAt (by simp))).mp (hi x hx.1 hend))
    exact ⟨lt_of_not_ge (fun h ↦ hnot (Or.inl h)), lt_of_not_ge (fun h ↦ hnot (Or.inr h))⟩
  · intro x hx N hN hxN
    exact exists_parityBall_in_neighborhood e g hg r₀ r₁ hr₀ hr₁ hi C hC hgen
      x hx.1 hx.2 N hN hxN

end NoExoticSixSphere.GenericFourAnnulus
