import Wikipedia.NoExoticSixSphere.RelativeBoundaryLocalNonvanishing
import Wikipedia.NoExoticSixSphere.RegularSlabConnectingCap
import Wikipedia.NoExoticSixSphere.RegularSlabFundamentalLocalization
import Wikipedia.NoExoticSixSphere.RegularSlabBoundaryLocalHomology

/-!
# The connecting image is the original boundary fundamental class

The relative lift and local-zero argument prove that the connecting
image has a nonzero value at every boundary point. The original local
mod-two uniqueness and global fundamental-class uniqueness identify it
with the class of any supplied boundary atlas. The comparison also
allows the boundary subset to be given by its original manifold predicate.
-/

noncomputable section

open Set Module CategoryTheory
open scoped Manifold ContDiff
open Wikipedia.HopfProblem SingularMayerVietoris

namespace NoExoticSixSphere.CylinderFiberSlab.BoundaryPush

variable {M N : Type} [TopologicalSpace M] [TopologicalSpace N]
  (F : C(ℝ × M, N)) (z : N) (s t : ℝ)

theorem not_mem_ends_iff_interior (p : slab F z s t) :
    p ∉ ends F z s t ↔ p ∈ interiorDomain F z s t := by
  constructor
  · intro hp
    rcases eq_endpoints_or_mem_Ioo_of_mem_Icc p.property with hs | ht | hi
    · exact False.elim (hp (Or.inl hs))
    · exact False.elim (hp (Or.inr ht))
    · exact hi
  · intro hi hp
    exact hp.elim (ne_of_gt hi.1) (ne_of_lt hi.2)

theorem isClosed_ends : IsClosed (ends F z s t) := by
  have hc : Continuous (fun p : slab F z s t ↦ p.val.val.1) :=
    (continuous_subtype_val.comp continuous_subtype_val).fst
  exact (isClosed_eq hc continuous_const).union (isClosed_eq hc continuous_const)

end NoExoticSixSphere.CylinderFiberSlab.BoundaryPush

namespace NoExoticSixSphere.RegularCollaredCylinder

open CylinderFiberSlab
open ModTwoCapProduct (Coefficient)

variable {B H M C H' N : Type}
  [NormedAddCommGroup B] [NormedSpace ℝ B] [FiniteDimensional ℝ B]
  [TopologicalSpace H] {I : ModelWithCorners ℝ B H} [I.Boundaryless]
  [TopologicalSpace M] [T2Space M] [ChartedSpace H M] [IsManifold I ∞ M] [CompactSpace M]
  [NormedAddCommGroup C] [NormedSpace ℝ C] [FiniteDimensional ℝ C]
  [TopologicalSpace H'] {J : ModelWithCorners ℝ C H'} [J.Boundaryless]
  [TopologicalSpace N] [T2Space N] [ChartedSpace H' N] [IsManifold J ∞ N]
  {z : N} {s t : ℝ} (d : RegularCollaredCylinder (M := M) I J z s t)

theorem boundaryConnectingClass_local_ne_zero (n : ℕ)
    (hd : finrank ℝ (ℝ × B) = finrank ℝ C + (n + 3))
    (x : BoundaryPush.ends d.map z s t) :
    homologyLinearMap (RelativeCoefficients.projection Coefficient
        ({x}ᶜ : Set (BoundaryPush.ends d.map z s t))) (n + 2)
        (d.boundaryConnectingClass n hd) ≠ 0 := by
  apply RelativeCoefficients.connecting_localize_ne_zero Coefficient
    (BoundaryPush.ends d.map z s t) (n + 2) (d.relativeFundamentalClass n hd) x
  · exact d.boundaryLocalModHomology_subsingleton x 2 (by decide) (n + 3)
  · intro O hO hxO
    obtain ⟨y, hyO, hy⟩ := d.exists_interior_mem_open O hO x.val hxO
    exact ⟨y, hyO, (BoundaryPush.not_mem_ends_iff_interior d.map z s t y).mpr hy⟩
  · intro y hy
    exact d.relativeFundamentalClass_local_ne_zero n hd
      ⟨y, (BoundaryPush.not_mem_ends_iff_interior d.map z s t y).mp hy⟩

def relativeFundamentalClassOnBoundary (n : ℕ)
    (hd : finrank ℝ (ℝ × B) = finrank ℝ C + (n + 3))
    (U : Set (slab d.map z s t)) (hU : U = BoundaryPush.ends d.map z s t) :
    RelativeCoefficients.ModHomology 2 U (n + 3) := by
  subst U
  exact d.relativeFundamentalClass n hd

theorem cap_relativeFundamentalClassOnBoundary_bijective (n : ℕ)
    (hd : finrank ℝ (ℝ × B) = finrank ℝ C + (n + 3))
    (U : Set (slab d.map z s t)) (hU : U = BoundaryPush.ends d.map z s t)
    (p q : ℕ) (h : p + q = n + 3) :
    Function.Bijective (fun a : RelativeModTwoCochains.Cohomology U p ↦
      RelativeModTwoCap.capProductInDegree U h a
        (d.relativeFundamentalClassOnBoundary n hd U hU)) := by
  subst U
  exact d.cap_relativeFundamentalClass_bijective n hd p q h

theorem connecting_relativeFundamentalClassOnBoundary
    {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (r : ℕ) [Fact (finrank ℝ E = (r + 2) + 1)]
    (hd : finrank ℝ (ℝ × B) = finrank ℝ C + ((r + 1) + 3))
    (U : Set (slab d.map z s t)) (hU : U = BoundaryPush.ends d.map z s t)
    [ChartedSpace E U] [CompactSpace U] :
    RelativeCoefficients.connecting Coefficient U (r + 3)
        (d.relativeFundamentalClassOnBoundary (r + 1) hd U hU) =
      ManifoldFundamentalClass.fundamentalClass (E := E) r U := by
  subst U
  apply ManifoldFundamentalClass.fundamentalClass_unique (E := E) r
  intro x
  apply ModTwoLocalClass.eq_manifoldClass_of_ne_zero (E := E) r x
  exact d.boundaryConnectingClass_local_ne_zero (r + 1) hd x

end NoExoticSixSphere.RegularCollaredCylinder
