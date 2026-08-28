import Wikipedia.HopfProblem.DegreeCollapsePathWedgeHomotopy
import Wikipedia.NoExoticSixSphere.SphereMooreCommutatorSmash

/-!
# Based product homotopies determine the original smash-sphere loop maps

First straighten on the actual fat wedge, then descend the whole
homotopy through the original pairing, jointly with homotopy time.
This proves injectivity at the level of based homotopy classes of
maps into native loop spaces, without an inference from homology.
-/

noncomputable section

open Topology
open scoped unitInterval

namespace Wikipedia.HopfProblem.DegreeCollapse.SmashLoopHomotopy

open NoExoticSixSphere SphereMooreCommutator JamesSphere

def pairingCylinder (n : ℕ) : C(I × Parameter n, I × Sphere (n + n)) :=
  (ContinuousMap.id I).prodMap (SecondStage.arrayPairing n)

theorem pairingCylinder_isQuotientMap (n : ℕ) : IsQuotientMap (pairingCylinder n) := by
  apply IsQuotientMap.of_surjective_continuous _ (pairingCylinder n).continuous
  rintro ⟨t, x⟩
  obtain ⟨v, hv⟩ := arrayPairing_surjective n x
  exact ⟨(t, v), Prod.ext rfl hv⟩

variable (n : ℕ) {Z : Type} [TopologicalSpace Z]
  {f g : C(Sphere (n + n), Z)}
  (H : (f.comp (SecondStage.arrayPairing n)).HomotopyRel
    (g.comp (SecondStage.arrayPairing n)) (Boundary n))

theorem respects (p q : I × Parameter n) (h : pairingCylinder n p = pairingCylinder n q) :
    H p = H q := by
  rcases p with ⟨t, v⟩
  rcases q with ⟨s, w⟩
  have ht : t = s := congrArg Prod.fst h
  subst s
  have hp : SecondStage.arrayPairing n v = SecondStage.arrayPairing n w :=
    congrArg Prod.snd h
  rcases pairing_fiber_condition n (v 0, v 1) (w 0, w 1) hp with hb | he
  · have hv := (arrayPairing_pole_iff n v).mp hb
    have hw := (arrayPairing_pole_iff n w).mp (hp.symm.trans hb)
    exact (H.eq_fst t hv).trans ((congrArg f hp).trans (H.eq_fst t hw).symm)
  · have hvw : v = w := by
      funext i
      fin_cases i
      · exact congrArg Prod.fst he
      · exact congrArg Prod.snd he
    exact congrArg (fun v ↦ H (t, v)) hvw

def descended : C(I × Sphere (n + n), Z) :=
  IsQuotientMap.lift (f := pairingCylinder n) (pairingCylinder_isQuotientMap n)
    H.toContinuousMap (respects n H)

theorem descended_pairing (t : I) (v : Parameter n) :
    descended n H (t, SecondStage.arrayPairing n v) = H (t, v) :=
  ContinuousMap.congr_fun (IsQuotientMap.lift_comp (pairingCylinder_isQuotientMap n)
    H.toContinuousMap (respects n H)) (t, v)

def descendedHomotopy : f.HomotopyRel g {spherePole (n + n)} where
  toContinuousMap := descended n H
  map_zero_left x := by
    obtain ⟨v, rfl⟩ := arrayPairing_surjective n x
    exact (descended_pairing n H 0 v).trans (H.apply_zero v)
  map_one_left x := by
    obtain ⟨v, rfl⟩ := arrayPairing_surjective n x
    exact (descended_pairing n H 1 v).trans (H.apply_one v)
  prop' t x hx := by
    have he : x = spherePole (n + n) := hx
    subst x
    have hp := (arrayPairing_pole_iff n (point n)).mpr (boundaryPoint n).property
    change descended n H (t, spherePole (n + n)) = f (spherePole (n + n))
    rw [← hp, descended_pairing]
    exact H.eq_fst t (boundaryPoint n).property

variable {Y : Type} [TopologicalSpace Y] {y : Y}
  {f g : C(Sphere (n + n), Path y y)}

theorem exists_based (hf : f (spherePole (n + n)) = Path.refl y)
    (hg : g (spherePole (n + n)) = Path.refl y)
    (H : (f.comp (SecondStage.arrayPairing n)).HomotopyRel
      (g.comp (SecondStage.arrayPairing n)) {point n}) :
    Nonempty (f.HomotopyRel g {spherePole (n + n)}) := by
  obtain ⟨K⟩ := PathWedgeHomotopy.exists_relative n
    (fun v hv ↦ (congrArg f ((arrayPairing_pole_iff n v).mpr hv)).trans hf)
    (fun v hv ↦ (congrArg g ((arrayPairing_pole_iff n v).mpr hv)).trans hg) H
  exact ⟨descendedHomotopy n K⟩

end Wikipedia.HopfProblem.DegreeCollapse.SmashLoopHomotopy
