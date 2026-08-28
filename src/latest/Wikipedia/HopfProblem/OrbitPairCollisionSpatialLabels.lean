import Wikipedia.HopfProblem.OrbitPairFiniteGuidingVelocities
import Wikipedia.HopfProblem.OrbitPairSupportedTargetClock

/-!
# Spatial labels identify collision events throughout time relocation

When collision sources have distinct spatial coordinates, an unordered
spatial pair determines its collision time. Exact global projected fibers
also identify each projected collision value with precisely one unordered
event. Consequently the target-clock relocation changes exactly the time
of the selected spatial label, even if other events share the new time.
-/

noncomputable section

open Set Function

namespace Wikipedia.HopfProblem.OrbitPair.FamilyDoublePoints

open NativeFamily SynchronizedPairs

variable {M N : Type*} {F : ℝ × M → N}

theorem unordered_spatial_labels_injective
    (hspace : InjOn Prod.snd (collisionSources F)) :
    InjOn Prod.snd (unorderedDoublePoints F) := by
  rintro _ ⟨p, hp, rfl⟩ _ ⟨q, hq, rfl⟩ hlabel
  apply Prod.ext
  · change p.1 = q.1
    change s(p.2.1, p.2.2) = s(q.2.1, q.2.2) at hlabel
    rcases Sym2.eq_iff.mp hlabel with ⟨hfirst, -⟩ | ⟨hsecond, -⟩
    · exact congrArg (fun z : ℝ × M => z.1)
        (hspace (first_mem_collisionSources hp) (first_mem_collisionSources hq) hfirst)
    · exact congrArg (fun z : ℝ × M => z.1)
        (hspace (first_mem_collisionSources hp) (second_mem_collisionSources hq) hsecond)
  · exact hlabel

theorem unorderedProjection_eq_of_projected_value_eq
    (hglobal : ∀ p ∈ doublePoints F, HasGlobalProjectedCollisionFiber F p)
    {p q : ℝ × (M × M)} (hp : p ∈ doublePoints F) (hq : q ∈ doublePoints F)
    (hvalue : F (first q) = F (first p)) :
    unorderedProjection q = unorderedProjection p := by
  rcases (hglobal p hp (first q)).mp hvalue with hfirst | hsecond
  · exact congrArg unorderedProjection
      (first_injOn_of_global_collision_fibers hglobal hq hp hfirst)
  · have hswap : (p.1, (p.2.2, p.2.1)) ∈ doublePoints F := ⟨hp.1.symm, hp.2.symm⟩
    have hqswap : q = (p.1, (p.2.2, p.2.1)) :=
      first_injOn_of_global_collision_fibers hglobal hq hswap hsecond
    rw [hqswap]
    exact Prod.ext rfl Sym2.eq_swap

theorem projected_value_eq_iff_spatial_label_eq
    (hglobal : ∀ p ∈ doublePoints F, HasGlobalProjectedCollisionFiber F p)
    (hspace : InjOn Prod.snd (collisionSources F))
    {p q : ℝ × (M × M)} (hp : p ∈ doublePoints F) (hq : q ∈ doublePoints F) :
    F (first q) = F (first p) ↔
      (unorderedProjection q).2 = (unorderedProjection p).2 := by
  constructor
  · intro hvalue
    exact congrArg Prod.snd (unorderedProjection_eq_of_projected_value_eq hglobal hp hq hvalue)
  · intro hlabel
    have heq := unordered_spatial_labels_injective hspace
      (mem_image_of_mem _ hq) (mem_image_of_mem _ hp) hlabel
    have htime : q.1 = p.1 := congrArg (fun z : ℝ × Sym2 M => z.1) heq
    change s(q.2.1, q.2.2) = s(p.2.1, p.2.2) at hlabel
    rcases Sym2.eq_iff.mp hlabel with ⟨hx, -⟩ | ⟨hx, -⟩
    · exact congrArg F (Prod.ext htime hx)
    · exact (congrArg F (Prod.ext htime hx)).trans hp.2.symm

end Wikipedia.HopfProblem.OrbitPair.FamilyDoublePoints

namespace Wikipedia.HopfProblem.OrbitPair.TargetClock

open NativeFamily FamilyDoublePoints SynchronizedPairs

variable {M N : Type*}

def replaceUnorderedTime (label : Sym2 M) (t₁ : ℝ) (q : ℝ × Sym2 M) : ℝ × Sym2 M := by
  classical
  exact (if q.2 = label then t₁ else q.1, q.2)

theorem unorderedProjection_relocateCollision
    {F : ℝ × M → N}
    (hglobal : ∀ p ∈ doublePoints F, HasGlobalProjectedCollisionFiber F p)
    (hspace : InjOn Prod.snd (collisionSources F))
    {p q : ℝ × (M × M)} (hp : p ∈ doublePoints F) (hq : q ∈ doublePoints F)
    (t₁ : ℝ) :
    unorderedProjection (relocateCollision F p (t₁ - p.1) q) =
      replaceUnorderedTime (unorderedProjection p).2 t₁ (unorderedProjection q) := by
  classical
  by_cases hlabel : (unorderedProjection q).2 = (unorderedProjection p).2
  · have hvalue := (projected_value_eq_iff_spatial_label_eq hglobal hspace hp hq).mpr hlabel
    have heq := unordered_spatial_labels_injective hspace
      (mem_image_of_mem _ hq) (mem_image_of_mem _ hp) hlabel
    have htime : q.1 = p.1 := congrArg (fun z : ℝ × Sym2 M => z.1) heq
    change s(q.2.1, q.2.2) = s(p.2.1, p.2.2) at hlabel
    simp [relocateCollision, unorderedProjection, replaceUnorderedTime, hvalue, htime, hlabel]
  · have hvalue : F (first q) ≠ F (first p) := fun heq =>
      hlabel ((projected_value_eq_iff_spatial_label_eq hglobal hspace hp hq).mp heq)
    change s(q.2.1, q.2.2) ≠ s(p.2.1, p.2.2) at hlabel
    simp [relocateCollision, unorderedProjection, replaceUnorderedTime, hvalue, hlabel]

theorem unorderedDoublePoints_eq_replaceTime_image
    {F F' : ℝ × M → N}
    (hglobal : ∀ p ∈ doublePoints F, HasGlobalProjectedCollisionFiber F p)
    (hspace : InjOn Prod.snd (collisionSources F))
    {p : ℝ × (M × M)} (hp : p ∈ doublePoints F) {t₁ : ℝ}
    (hD : doublePoints F' = relocateCollision F p (t₁ - p.1) '' doublePoints F) :
    unorderedDoublePoints F' =
      replaceUnorderedTime (unorderedProjection p).2 t₁ '' unorderedDoublePoints F := by
  unfold unorderedDoublePoints
  rw [hD, image_image, image_image]
  exact image_congr (fun q hq => unorderedProjection_relocateCollision hglobal hspace hp hq t₁)

end Wikipedia.HopfProblem.OrbitPair.TargetClock
