import Wikipedia.HopfProblem.OrbitPairSynchronizedPairs
import Wikipedia.HopfProblem.OrbitPairFamilyDoublePoints

/-!
# The source points participating in synchronized collisions

The two projections of the finite ordered collision set give an actual
finite subset of time times the source surface. Embedded endpoint collars
place every such point strictly between the collar times.
-/

noncomputable section

open Set Function

namespace Wikipedia.HopfProblem.OrbitPair.FamilyDoublePoints

variable {M N : Type*}

def collisionSources (F : ℝ × M → N) : Set (ℝ × M) :=
  SynchronizedPairs.first '' doublePoints F ∪ SynchronizedPairs.second '' doublePoints F

def sliceCollisionSources (F : ℝ × M → N) (t : ℝ) : Set M :=
  (fun x => (t, x)) ⁻¹' collisionSources F

def collisionFiber (F : ℝ × M → N) (q : ℝ × M) : Set M :=
  {x | F (q.1, x) = F q}

theorem finite_collisionSources {F : ℝ × M → N} (hF : (doublePoints F).Finite) :
    (collisionSources F).Finite :=
  (hF.image SynchronizedPairs.first).union (hF.image SynchronizedPairs.second)

theorem first_mem_collisionSources {F : ℝ × M → N} {p : ℝ × (M × M)}
    (hp : p ∈ doublePoints F) : SynchronizedPairs.first p ∈ collisionSources F :=
  Or.inl (mem_image_of_mem _ hp)

theorem second_mem_collisionSources {F : ℝ × M → N} {p : ℝ × (M × M)}
    (hp : p ∈ doublePoints F) : SynchronizedPairs.second p ∈ collisionSources F :=
  Or.inr (mem_image_of_mem _ hp)

theorem finite_sliceCollisionSources {F : ℝ × M → N} (hF : (doublePoints F).Finite)
    (t : ℝ) : (sliceCollisionSources F t).Finite := by
  have hi : Injective (fun x : M => (t, x)) := by
    intro x y heq
    exact congrArg Prod.snd heq
  exact (finite_collisionSources hF).preimage hi.injOn

theorem collisionFiber_subset_sliceCollisionSources {F : ℝ × M → N} {q : ℝ × M}
    (hq : q ∈ collisionSources F) : collisionFiber F q ⊆ sliceCollisionSources F q.1 := by
  intro x hx
  by_cases heq : x = q.2
  · subst x
    exact hq
  · exact first_mem_collisionSources (p := (q.1, (x, q.2))) ⟨heq, hx⟩

theorem finite_collisionFiber {F : ℝ × M → N} (hF : (doublePoints F).Finite)
    {q : ℝ × M} (hq : q ∈ collisionSources F) : (collisionFiber F q).Finite :=
  (finite_sliceCollisionSources hF q.1).subset (collisionFiber_subset_sliceCollisionSources hq)

theorem collision_time_between_collars {F : ℝ × M → N} {L R : M → N}
    (hL : Injective L) (hR : Injective R) {a b : ℝ}
    (hlo : ∀ t x, t ≤ a → F (t, x) = L x)
    (hhi : ∀ t x, b ≤ t → F (t, x) = R x)
    {p : ℝ × (M × M)} (hp : p ∈ doublePoints F) : p.1 ∈ Ioo a b := by
  constructor
  · by_contra hn
    have ht : p.1 ≤ a := le_of_not_gt hn
    apply hp.1
    apply hL
    calc
      L p.2.1 = F (p.1, p.2.1) := (hlo _ _ ht).symm
      _ = F (p.1, p.2.2) := hp.2
      _ = L p.2.2 := hlo _ _ ht
  · by_contra hn
    have ht : b ≤ p.1 := le_of_not_gt hn
    apply hp.1
    apply hR
    calc
      R p.2.1 = F (p.1, p.2.1) := (hhi _ _ ht).symm
      _ = F (p.1, p.2.2) := hp.2
      _ = R p.2.2 := hhi _ _ ht

theorem collisionSources_time_between_collars {F : ℝ × M → N} {L R : M → N}
    (hL : Injective L) (hR : Injective R) {a b : ℝ}
    (hlo : ∀ t x, t ≤ a → F (t, x) = L x)
    (hhi : ∀ t x, b ≤ t → F (t, x) = R x) :
    ∀ p ∈ collisionSources F, p.1 ∈ Ioo a b := by
  intro p hp
  rcases hp with ⟨q, hq, rfl⟩ | ⟨q, hq, rfl⟩
  · exact collision_time_between_collars hL hR hlo hhi hq
  · exact collision_time_between_collars hL hR hlo hhi hq

theorem collisionSources_eq_of_doublePoints_eq {F G : ℝ × M → N}
    (hD : doublePoints F = doublePoints G) : collisionSources F = collisionSources G := by
  unfold collisionSources
  rw [hD]

end Wikipedia.HopfProblem.OrbitPair.FamilyDoublePoints
