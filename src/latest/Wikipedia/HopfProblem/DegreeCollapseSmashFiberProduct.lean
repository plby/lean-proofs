import Wikipedia.NoExoticSixSphere.SphereSmashSquare

/-!
# Actual non-basepoint fibers of a sphere smash square are products

The original sphere pairing has singleton fibers away from its pole.
Consequently the fiber of the actual smash square over the pair of a
non-basepoint value is homeomorphic to the product of the two original
fibers. This theorem retains the original pairing and descended map.
It does not assert smoothness or a framing comparison.
-/

noncomputable section

open scoped Topology

namespace Wikipedia.HopfProblem.DegreeCollapse.SmashFiberProduct

open NoExoticSixSphere SphereComposition JamesSphere

variable {m n : ℕ} (f : Based m n) (b : Sphere n)

abbrev Fiber := {x : Sphere m // f.val x = b}

def point : Sphere (n + n) := pairing n (b, b)

theorem point_ne_pole (hb : b ≠ spherePole n) : point b ≠ spherePole (n + n) := by
  intro h
  rcases (pairing_eq_pole_iff n (b, b)).mp h with h | h
  · exact hb h
  · exact hb h

theorem fiberMap_mem (p : Fiber f b × Fiber f b) :
    SphereSmash.squareMap f (pairing m (p.1.val, p.2.val)) = point b := by
  rw [SphereSmash.squareMap_pairing, p.1.property, p.2.property]
  rfl

def fiberMap : C(Fiber f b × Fiber f b,
    {x : Sphere (m + m) // SphereSmash.squareMap f x = point b}) :=
  ⟨fun p ↦ ⟨pairing m (p.1.val, p.2.val), fiberMap_mem f b p⟩,
    ((pairing m).continuous.comp
      ((continuous_subtype_val.comp continuous_fst).prodMk
        (continuous_subtype_val.comp continuous_snd))).subtype_mk _⟩

theorem fiberMap_bijective (hb : b ≠ spherePole n) : Function.Bijective (fiberMap f b) := by
  constructor
  · intro p q hpq
    have h := congrArg Subtype.val hpq
    change pairing m (p.1.val, p.2.val) = pairing m (q.1.val, q.2.val) at h
    rcases pairing_fiber_condition m _ _ h with h | h
    · rcases (pairing_eq_pole_iff m (p.1.val, p.2.val)).mp h with h | h
      · exact False.elim (hb (p.1.property.symm.trans
          ((congrArg f.val h).trans f.property)))
      · exact False.elim (hb (p.2.property.symm.trans
          ((congrArg f.val h).trans f.property)))
    · exact Prod.ext (Subtype.ext (congrArg Prod.fst h))
        (Subtype.ext (congrArg Prod.snd h))
  · intro y
    obtain ⟨p, hp⟩ := pairing_surjective m y.val
    have h : pairing n (f.val p.1, f.val p.2) = pairing n (b, b) :=
      (SphereSmash.squareMap_pairing f p).symm.trans
        ((congrArg (SphereSmash.squareMap f) hp).trans y.property)
    have he : (f.val p.1, f.val p.2) = (b, b) := by
      rcases pairing_fiber_condition n _ _ h with hzero | he
      · exact False.elim (point_ne_pole b hb (h.symm.trans hzero))
      · exact he
    refine ⟨(⟨p.1, congrArg Prod.fst he⟩, ⟨p.2, congrArg Prod.snd he⟩), ?_⟩
    exact Subtype.ext hp

def fiberHomeomorph (hb : b ≠ spherePole n) :
    Fiber f b × Fiber f b ≃ₜ
      {x : Sphere (m + m) // SphereSmash.squareMap f x = point b} := by
  let : CompactSpace (Fiber f b) :=
    isCompact_iff_compactSpace.mp ((isClosed_singleton.preimage f.val.continuous).isCompact)
  let e := Equiv.ofBijective (fiberMap f b) (fiberMap_bijective f b hb)
  exact e.toHomeomorphOfContinuousClosed (fiberMap f b).continuous
    (fiberMap f b).continuous.isClosedMap

theorem fiberHomeomorph_val (hb : b ≠ spherePole n) (p : Fiber f b × Fiber f b) :
    (fiberHomeomorph f b hb p).val = pairing m (p.1.val, p.2.val) := rfl

end Wikipedia.HopfProblem.DegreeCollapse.SmashFiberProduct

