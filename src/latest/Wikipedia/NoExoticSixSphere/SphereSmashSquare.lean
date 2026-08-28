import Wikipedia.NoExoticSixSphere.SpherePairingCubeCoordinates
import Wikipedia.NoExoticSixSphere.NativeSphereComposition

/-!
# The actual smash square of a based sphere map

The product map descends through the ORIGINAL sphere pairing, with
its literal formula retained. Actual source and target coordinate
permutations exchanging the equal factors intertwine the descended map.
No homotopy class or order is assigned by definition.
-/

noncomputable section

open scoped Topology unitInterval

namespace NoExoticSixSphere.SphereSmash

open SmoothCube SphereComposition JamesSphere
open JamesSphere.PairingCoordinates

variable {m n : ℕ} (f : Based m n)

def pairMap : C(Sphere m × Sphere m, Sphere (n + n)) :=
  (pairing n).comp (f.val.prodMap f.val)

theorem pairMap_pole (p : Sphere m × Sphere m) (hp : pairing m p = spherePole (m + m)) :
    pairMap f p = spherePole (n + n) := by
  rcases (pairing_eq_pole_iff m p).mp hp with h | h
  · change pairing n (f.val p.1, f.val p.2) = _
    rw [h, f.property, pairing_left_pole]
  · change pairing n (f.val p.1, f.val p.2) = _
    rw [h, f.property, pairing_right_pole]

theorem pairMap_respects (p q : Sphere m × Sphere m) (h : pairing m p = pairing m q) :
    pairMap f p = pairMap f q := by
  rcases pairing_fiber_condition m p q h with hp | hp
  · exact (pairMap_pole f p hp).trans (pairMap_pole f q (h.symm.trans hp)).symm
  · exact congrArg (pairMap f) hp

def squareMap : C(Sphere (m + m), Sphere (n + n)) :=
  (isQuotientMap_pairing m).lift (pairMap f) (pairMap_respects f)

theorem squareMap_pairing (p : Sphere m × Sphere m) :
    squareMap f (pairing m p) = pairing n (f.val p.1, f.val p.2) :=
  ContinuousMap.congr_fun ((isQuotientMap_pairing m).lift_comp (pairMap f) (pairMap_respects f)) p

theorem squareMap_pole : squareMap f (spherePole (m + m)) = spherePole (n + n) := by
  rw [← pairing_left_pole m (spherePole m), squareMap_pairing]
  rw [f.property, pairing_left_pole]

def basedSquare : Based (m + m) (n + n) := ⟨squareMap f, squareMap_pole f⟩

theorem square_swap (hm : 0 < m) (hn : 0 < n)
    (e : Equiv.Perm (Fin (m + m))) (d : Equiv.Perm (Fin (n + n)))
    (he : ∀ u v : Fin m → I, Fin.append v u = fun j ↦ Fin.append u v (e j))
    (hd : ∀ u v : Fin n → I, Fin.append v u = fun j ↦ Fin.append u v (d j))
    (z : Sphere (m + m)) :
    permutation (n + n) (by omega) d (squareMap f z) =
      squareMap f (permutation (m + m) (by omega) e z) := by
  obtain ⟨⟨x, y⟩, rfl⟩ := pairing_surjective m z
  rw [← pairing_swap_of_coordinates m hm e he, squareMap_pairing, squareMap_pairing]
  exact (pairing_swap_of_coordinates n hn d hd (f.val x) (f.val y)).symm

end NoExoticSixSphere.SphereSmash
