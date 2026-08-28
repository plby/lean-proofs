import Wikipedia.SmoothSixDPoincare.CoverOverlapHomology
import Wikipedia.SmoothSixDPoincare.CoverConnectingNaturality

/-!
# The actual connecting map is the sum over separated overlap components

Combine native Mayer–Vietoris naturality with the proved homology
decomposition of a disjoint open union. The summands are the original
restricted maps on the original overlap components. Their source classes
are defined by the actual source connecting map, not prescribed as signs
or local generators; identifying those classes remains a geometric step.
-/

noncomputable section

open Set Function ContinuousMap

namespace Wikipedia.SmoothSixDPoincare.CoverLocalContributions

open Wikipedia.HopfProblem.SingularMayerVietoris

variable {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
  {ι : Type} [Fintype ι]
  (U : Set X) (V : ι → Set X) (hU : IsOpen U) (hV : ∀ i, IsOpen (V i))
  (hd : Pairwise (Disjoint on V)) (hc : U ∪ (⋃ i, V i) = univ)

/-- Actual component coordinates of the native source connecting homomorphism. -/
def componentConnecting (k : ℕ) :
    SingularHomology X (k + 1) →ₗ[ℤ] (∀ i, SingularHomology (↥(U ∩ V i)) k) :=
  (CoverOverlapHomology.homologyEquiv U V hU hV hd k).toLinearMap.comp
    (connectingHomomorphism U (⋃ i, V i) hU (isOpen_iUnion hV) hc k)

variable (U' V' : Set Y) (f : C(X, Y)) (hfU : MapsTo f U U')
  (hfV : ∀ i, MapsTo f (V i) V')

omit [Fintype ι] in
include hfV in
theorem map_union : MapsTo f (⋃ i, V i) V' := by
  intro x hx
  obtain ⟨i, hi⟩ := mem_iUnion.mp hx
  exact hfV i hi

/-- The same original map restricted to one of the actual overlap components. -/
def localMap (i : ι) : C(↥(U ∩ V i), ↥(U' ∩ V')) :=
  CoverNaturality.mapOn f _ _ (fun _ hx => ⟨hfU hx.1, hfV i hx.2⟩)

variable (hU' : IsOpen U') (hV' : IsOpen V') (hc' : U' ∪ V' = univ)

/-- Native naturality and native disjoint-union homology give the literal finite sum. -/
theorem connecting_sum (k : ℕ) (a : SingularHomology X (k + 1)) :
    connectingHomomorphism U' V' hU' hV' hc' k (singularHomologyMap f (k + 1) a) =
      ∑ i, singularHomologyMap (localMap U V U' V' f hfU hfV i) k
        (componentConnecting U V hU hV hd hc k a i) := by
  rw [← CoverNaturality.connecting_naturality_apply U (⋃ i, V i) U' V' f
    hfU (map_union V V' f hfV) hU (isOpen_iUnion hV) hc hU' hV' hc' k a]
  rw [CoverOverlapHomology.homology_map_out U V hU hV hd]
  apply Finset.sum_congr rfl
  intro i _
  rfl

/-- When the target connecting map is injective, this sum determines the original homology map. -/
theorem homology_eq_of_local_sum (k : ℕ)
    (hinj : Injective (connectingHomomorphism U' V' hU' hV' hc' k))
    (a : SingularHomology X (k + 1)) (b : SingularHomology Y (k + 1))
    (hsum : (∑ i, singularHomologyMap (localMap U V U' V' f hfU hfV i) k
      (componentConnecting U V hU hV hd hc k a i)) =
        connectingHomomorphism U' V' hU' hV' hc' k b) :
    singularHomologyMap f (k + 1) a = b :=
  hinj ((connecting_sum U V hU hV hd hc U' V' f hfU hfV hU' hV' hc' k a).trans hsum)

end Wikipedia.SmoothSixDPoincare.CoverLocalContributions
