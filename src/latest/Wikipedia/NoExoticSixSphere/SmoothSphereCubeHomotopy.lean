import Wikipedia.NoExoticSixSphere.SmoothCubeSphereQuotient
import Mathlib.Topology.Homotopy.HomotopyGroup

/-!
# Original sphere maps and native generalized loops

The constructed smooth-interior cube quotient identifies actual based
sphere maps with Mathlib's native generalized loops. Native homotopies
relative to every cube face descend jointly to sphere homotopies fixing
the stereographic pole. No new homotopy relation is assigned to the maps.
-/

noncomputable section

open Set Function Topology
open scoped unitInterval Topology

namespace NoExoticSixSphere.SmoothCube

variable {n : ℕ} {X : Type*} [TopologicalSpace X] {x : X}

abbrev BasedMap (n : ℕ) (X : Type*) [TopologicalSpace X] (x : X) :=
  {f : C(Sphere n, X) // f (spherePole n) = x}

def toGenLoop (f : BasedMap n X x) : GenLoop (Fin n) X x :=
  ⟨f.val.comp (quotient n), fun u hu ↦
    (congrArg f.val (quotient_boundary n u hu)).trans f.property⟩

theorem genLoop_constant_on_fibers (p : GenLoop (Fin n) X x) :
    ∀ u w, quotient n u = quotient n w → p u = p w := by
  intro u w h
  rcases (quotient_eq_iff n u w).mp h with rfl | ⟨hu, hw⟩
  · rfl
  · exact (p.property u hu).trans (p.property w hw).symm

def descend (hn : 0 < n) (p : GenLoop (Fin n) X x) : C(Sphere n, X) :=
  (quotient_isQuotientMap hn).lift p.val (genLoop_constant_on_fibers p)

theorem descend_quotient (hn : 0 < n) (p : GenLoop (Fin n) X x) (u : Fin n → I) :
    descend hn p (quotient n u) = p u :=
  ContinuousMap.congr_fun ((quotient_isQuotientMap hn).lift_comp p.val
    (genLoop_constant_on_fibers p)) u

theorem descend_pole (hn : 0 < n) (p : GenLoop (Fin n) X x) :
    descend hn p (spherePole n) = x := by
  rw [← quotient_boundary n 0 (zero_boundary hn), descend_quotient]
  exact p.property 0 (zero_boundary hn)

def basedEquiv (hn : 0 < n) : BasedMap n X x ≃ GenLoop (Fin n) X x where
  toFun := toGenLoop
  invFun p := ⟨descend hn p, descend_pole hn p⟩
  left_inv f := by
    apply Subtype.ext
    apply ContinuousMap.ext
    intro z
    obtain ⟨u, rfl⟩ := quotient_surjective hn z
    exact descend_quotient hn (toGenLoop f) u
  right_inv p := by
    apply Subtype.ext
    apply ContinuousMap.ext
    exact descend_quotient hn p

def cylinder (n : ℕ) : C(I × (Fin n → I), I × Sphere n) :=
  (ContinuousMap.id I).prodMap (quotient n)

theorem cylinder_surjective (hn : 0 < n) : Surjective (cylinder n) := by
  rintro ⟨t, z⟩
  obtain ⟨u, rfl⟩ := quotient_surjective hn z
  exact ⟨(t, u), rfl⟩

theorem cylinder_isQuotientMap (hn : 0 < n) : IsQuotientMap (cylinder n) :=
  .of_surjective_continuous (cylinder_surjective hn) (cylinder n).continuous

def descendHomotopy (hn : 0 < n) (f g : C(Sphere n, X))
    (H : (f.comp (quotient n)).HomotopyRel (g.comp (quotient n)) (Cube.boundary (Fin n))) :
    f.HomotopyRel g {spherePole n} := by
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
  have hG (t : I) (u : Fin n → I) : G (t, quotient n u) = H (t, u) :=
    ContinuousMap.congr_fun ((cylinder_isQuotientMap hn).lift_comp
      H.toHomotopy.toContinuousMap hfib) (t, u)
  refine {
    toContinuousMap := G
    map_zero_left := ?_
    map_one_left := ?_
    prop' := ?_ }
  · intro z
    obtain ⟨u, rfl⟩ := quotient_surjective hn z
    exact (hG 0 u).trans (H.apply_zero u)
  · intro z
    obtain ⟨u, rfl⟩ := quotient_surjective hn z
    exact (hG 1 u).trans (H.apply_one u)
  · intro t z hz
    have hz' : z = spherePole n := hz
    subst z
    change G (t, spherePole n) = f (spherePole n)
    rw [← quotient_boundary n 0 (zero_boundary hn), hG]
    exact H.eq_fst t (zero_boundary hn)

theorem homotopicRel_iff (hn : 0 < n) (f g : C(Sphere n, X)) :
    f.HomotopicRel g {spherePole n} ↔
      (f.comp (quotient n)).HomotopicRel (g.comp (quotient n)) (Cube.boundary (Fin n)) := by
  constructor
  · rintro ⟨H⟩
    refine ⟨{ toHomotopy := H.toHomotopy.compContinuousMap (quotient n), prop' := ?_ }⟩
    intro t u hu
    exact H.eq_fst t (show quotient n u ∈ {spherePole n} from quotient_boundary n u hu)
  · rintro ⟨H⟩
    exact ⟨descendHomotopy hn f g H⟩

def sphereClass (f : BasedMap n X x) : HomotopyGroup (Fin n) X x := ⟦toGenLoop f⟧

theorem sphereClass_eq_iff (hn : 0 < n) (f g : BasedMap n X x) :
    sphereClass f = sphereClass g ↔ f.val.HomotopicRel g.val {spherePole n} := by
  change (⟦toGenLoop f⟧ : HomotopyGroup (Fin n) X x) = ⟦toGenLoop g⟧ ↔ _
  rw [Quotient.eq]
  exact (homotopicRel_iff hn f.val g.val).symm

theorem sphereClass_surjective (hn : 0 < n) :
    Surjective (sphereClass (n := n) (X := X) (x := x)) := by
  intro a
  induction a using Quotient.inductionOn with
  | h p =>
    refine ⟨(basedEquiv hn).symm p, ?_⟩
    change (⟦basedEquiv hn ((basedEquiv hn).symm p)⟧ : HomotopyGroup (Fin n) X x) = ⟦p⟧
    rw [Equiv.apply_symm_apply]

end NoExoticSixSphere.SmoothCube
