import Wikipedia.NoExoticSixSphere.Definitions
import Wikipedia.HopfProblem.DegreeCollapseSphereCube

/-!
# Actual based sphere homotopies and native cube homotopies

Use the existing genuine boundary-collapse quotient in each positive
dimension. A cube homotopy relative to every face descends jointly to a
sphere homotopy fixing the collapsed point, and conversely.
-/

noncomputable section

open Set
open scoped unitInterval

namespace NoExoticSixSphere.SphereCubeHomotopy

open Wikipedia.HopfProblem.DegreeCollapse.SphereCube

variable {n : ℕ} {X : Type*} [TopologicalSpace X]

def descend (hn : 0 < n) (f g : C(Sphere n, X))
    (H : (f.comp (quotient n)).HomotopyRel (g.comp (quotient n)) (Cube.boundary (Fin n))) :
    f.HomotopyRel g {point n} := by
  have hfib : ∀ a b, cylinder n a = cylinder n b → H a = H b := by
    rintro ⟨t, z⟩ ⟨s, w⟩ h
    have ht : t = s := congrArg Prod.fst h
    subst s
    have hzw : quotient n z = quotient n w := congrArg Prod.snd h
    rcases (quotient_eq_iff n z w).mp hzw with rfl | ⟨hz, hw⟩
    · rfl
    · rw [H.eq_fst t hz, H.eq_fst t hw]
      change f (quotient n z) = f (quotient n w)
      rw [quotient_boundary n z hz, quotient_boundary n w hw]
  let G := (cylinder_isQuotientMap hn).lift H.toHomotopy.toContinuousMap hfib
  have hG (t : unitInterval) (z : Fin n → unitInterval) :
      G (t, quotient n z) = H (t, z) :=
    ContinuousMap.congr_fun ((cylinder_isQuotientMap hn).lift_comp
      H.toHomotopy.toContinuousMap hfib) (t, z)
  refine {
    toContinuousMap := G
    map_zero_left := ?_
    map_one_left := ?_
    prop' := ?_ }
  · intro z
    obtain ⟨w, rfl⟩ := quotient_surjective hn z
    exact (hG 0 w).trans (H.apply_zero w)
  · intro z
    obtain ⟨w, rfl⟩ := quotient_surjective hn z
    exact (hG 1 w).trans (H.apply_one w)
  · intro t z hz
    have hz' : z = point n := hz
    subst z
    change G (t, point n) = f (point n)
    rw [← quotient_boundary n 0 (zero_boundary hn), hG]
    exact H.eq_fst t (zero_boundary hn)

theorem homotopicRel_iff (hn : 0 < n) (f g : C(Sphere n, X)) :
    f.HomotopicRel g {point n} ↔
      (f.comp (quotient n)).HomotopicRel (g.comp (quotient n)) (Cube.boundary (Fin n)) := by
  constructor
  · rintro ⟨H⟩
    refine ⟨{ toHomotopy := H.toHomotopy.compContinuousMap (quotient n), prop' := ?_ }⟩
    intro t z hz
    exact H.eq_fst t (show quotient n z ∈ {point n} from quotient_boundary n z hz)
  · rintro ⟨H⟩
    exact ⟨descend hn f g H⟩

theorem basedCube_nullhomotopic_iff (hn : 0 < n) (f : C(Sphere n, X)) :
    GenLoop.Homotopic (basedCube f) GenLoop.const ↔
      f.HomotopicRel (ContinuousMap.const _ (f (point n))) {point n} :=
  (homotopicRel_iff hn f (ContinuousMap.const _ (f (point n)))).symm

end NoExoticSixSphere.SphereCubeHomotopy
