import Wikipedia.NoExoticSixSphere.SphereMapReindex
import Wikipedia.NoExoticSixSphere.SphereCompactificationChart
import Wikipedia.NoExoticSixSphere.Topology.SimplyConnectedSphere
import Mathlib.Order.DirectedInverseSystem

/-!
# The actual sphere maps and transition maps for the sixth stable stem

Stage `k` consists of maps from the standard `(k + 8)`-sphere to the
standard `(k + 2)`-sphere, modulo actual continuous homotopy. Transition
maps are literal suspensions. The positive target dimensions ensure that
all constant maps have the same homotopy class. No computation of these
classes, or of their eventual direct limit, is assumed.
-/

noncomputable section

namespace NoExoticSixSphere.StableSixSphereMaps

abbrev StageMap (k : ℕ) := C(Sphere (k + 8), Sphere (k + 2))

def homotopySetoid (k : ℕ) : Setoid (StageMap k) where
  r := ContinuousMap.Homotopic
  iseqv := ContinuousMap.Homotopic.equivalence

abbrev Stage (k : ℕ) := Quotient (homotopySetoid k)

def classOf {k : ℕ} (f : StageMap k) : Stage k := Quotient.mk _ f

theorem classOf_eq_iff {k : ℕ} (f g : StageMap k) :
    classOf f = classOf g ↔ f.Homotopic g := Quotient.eq

def stageZero (k : ℕ) : Stage k :=
  classOf (ContinuousMap.const _ (spherePole (k + 2)))

theorem classOf_eq_stageZero_iff {k : ℕ} (f : StageMap k) :
    classOf f = stageZero k ↔ f.Nullhomotopic := by
  constructor
  · intro h
    exact ⟨spherePole (k + 2), (classOf_eq_iff _ _).mp h⟩
  · rintro ⟨b, h⟩
    apply (classOf_eq_iff _ _).mpr
    exact h.trans (ContinuousMap.homotopic_const_iff.mpr
      (PathConnectedSpace.joined b (spherePole (k + 2))))

def step {k : ℕ} : Stage k → Stage (k + 1) :=
  Quotient.map SphereMapSuspension.map (fun _ _ h ↦ SphereMapSuspension.map_homotopic h)

theorem step_classOf {k : ℕ} (f : StageMap k) :
    step (classOf f) = classOf (SphereMapSuspension.map f) := rfl

theorem step_stageZero (k : ℕ) : step (stageZero k) = stageZero (k + 1) := by
  apply (classOf_eq_stageZero_iff _).mpr
  exact SphereMapSuspension.map_nullhomotopic (ContinuousMap.nullhomotopic_of_constant _)

def liftMap {k l : ℕ} (h : k ≤ l) (f : StageMap k) : StageMap l :=
  Nat.leRecOn h (fun g ↦ SphereMapSuspension.map g) f

def transition (k l : ℕ) (h : k ≤ l) (x : Stage k) : Stage l :=
  Nat.leRecOn h step x

theorem liftMap_self (k : ℕ) (f : StageMap k) : liftMap le_rfl f = f :=
  Nat.leRecOn_self f

theorem liftMap_succ {k l : ℕ} (h : k ≤ l) (f : StageMap k) :
    liftMap (h.trans (Nat.le_succ l)) f = SphereMapSuspension.map (liftMap h f) :=
  Nat.leRecOn_succ h f

theorem transition_self (k : ℕ) (x : Stage k) : transition k k le_rfl x = x :=
  Nat.leRecOn_self x

theorem transition_succ {k l : ℕ} (h : k ≤ l) (x : Stage k) :
    transition k (l + 1) (h.trans (Nat.le_succ l)) x = step (transition k l h x) :=
  Nat.leRecOn_succ h x

instance : DirectedSystem Stage (fun {k l} h ↦ transition k l h) where
  map_self {k} x := transition_self k x
  map_map := by
    intro k j i h h' x
    exact (Nat.leRecOn_trans h h' x).symm

theorem transition_classOf {k l : ℕ} (h : k ≤ l) (f : StageMap k) :
    transition k l h (classOf f) = classOf (liftMap h f) := by
  induction l, h using Nat.le_induction with
  | base => rw [transition_self, liftMap_self]
  | succ l h ih => rw [transition_succ h, liftMap_succ h, ih, step_classOf]

theorem transition_stageZero {k l : ℕ} (h : k ≤ l) :
    transition k l h (stageZero k) = stageZero l := by
  induction l, h using Nat.le_induction with
  | base => exact transition_self k _
  | succ l h ih => rw [transition_succ h, ih, step_stageZero]

instance (k : ℕ) : Zero (Stage k) := ⟨stageZero k⟩

def transitionHom (k l : ℕ) (h : k ≤ l) : ZeroHom (Stage k) (Stage l) where
  toFun := transition k l h
  map_zero' := transition_stageZero h

instance : DirectedSystem Stage (fun {k l} h ↦ transitionHom k l h) where
  map_self {k} x := transition_self k x
  map_map := by
    intro k j i h h' x
    exact (Nat.leRecOn_trans h h' x).symm

theorem liftMap_add_heq (k r : ℕ) (f : StageMap k) :
    HEq (liftMap (Nat.le_add_right k r) f) (SphereMapSuspension.iterate f r) := by
  induction r with
  | zero => rw [liftMap_self]; rfl
  | succ r ih =>
    rw [liftMap_succ (Nat.le_add_right k r)]
    exact SphereMapSuspension.map_heq (Nat.add_right_comm k r 8) (Nat.add_right_comm k r 2) ih

theorem liftMap_add_nullhomotopic_iff (k r : ℕ) (f : StageMap k) :
    (liftMap (Nat.le_add_right k r) f).Nullhomotopic ↔
      (SphereMapSuspension.iterate f r).Nullhomotopic :=
  SphereMapSuspension.nullhomotopic_iff_of_heq
    (Nat.add_right_comm k r 8) (Nat.add_right_comm k r 2) (liftMap_add_heq k r f)

end NoExoticSixSphere.StableSixSphereMaps
