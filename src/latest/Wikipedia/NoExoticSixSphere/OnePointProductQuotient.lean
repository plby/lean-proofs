import Wikipedia.NoExoticSixSphere.OpenFiberCollapse

/-!
# The actual product compactification as a quotient of two compactifications

The map from `OnePoint E × OnePoint F` to `OnePoint (E × F)` retains every
finite pair and collapses exactly the two infinity axes. It is continuous
and surjective, hence a quotient map for locally compact Hausdorff spaces.
This is the geometric quotient needed for adding a coordinate to a framed
collapse; no stable homotopy group is substituted for the actual spaces.
-/

noncomputable section

open Set Function Topology
open scoped OnePoint

namespace NoExoticSixSphere.OnePointProduct

variable {E F : Type*}

def finiteTube (p : Unit × (E × F)) : OnePoint E × OnePoint F := (p.2.1, p.2.2)

theorem finiteTube_injective : Injective (finiteTube (E := E) (F := F)) := by
  rintro ⟨u, x, y⟩ ⟨v, x', y'⟩ h
  have hx : x = x' := OnePoint.coe_injective (congrArg Prod.fst h)
  have hy : y = y' := OnePoint.coe_injective (congrArg Prod.snd h)
  subst x'
  subst y'
  exact Prod.ext (Subsingleton.elim u v) rfl

def map (p : OnePoint E × OnePoint F) : OnePoint (E × F) :=
  OpenFiberCollapse.collapse finiteTube p

@[simp]
theorem map_coe (x : E) (y : F) : map (↑x, ↑y) = ((x, y) : OnePoint (E × F)) :=
  OpenFiberCollapse.collapse_apply finiteTube finiteTube_injective ((), x, y)

@[simp]
theorem map_infty_left (y : OnePoint F) : map (∞, y) = (∞ : OnePoint (E × F)) := by
  apply OpenFiberCollapse.collapse_of_not_mem
  rintro ⟨p, hp⟩
  exact OnePoint.coe_ne_infty p.2.1 (congrArg Prod.fst hp)

@[simp]
theorem map_infty_right (x : OnePoint E) : map (x, ∞) = (∞ : OnePoint (E × F)) := by
  apply OpenFiberCollapse.collapse_of_not_mem
  rintro ⟨p, hp⟩
  exact OnePoint.coe_ne_infty p.2.2 (congrArg Prod.snd hp)

theorem map_eq_coe_iff (p : OnePoint E × OnePoint F) (q : E × F) :
    map p = (q : OnePoint (E × F)) ↔ p.1 = ↑q.1 ∧ p.2 = ↑q.2 := by
  rw [map, OpenFiberCollapse.collapse_eq_coe_iff finiteTube finiteTube_injective]
  constructor
  · rintro ⟨u, hu⟩
    exact ⟨(congrArg Prod.fst hu).symm, (congrArg Prod.snd hu).symm⟩
  · rintro ⟨hx, hy⟩
    exact ⟨(), Prod.ext hx.symm hy.symm⟩

theorem map_eq_infty_iff (p : OnePoint E × OnePoint F) :
    map p = ∞ ↔ p.1 = ∞ ∨ p.2 = ∞ := by
  rcases p with ⟨x, y⟩
  induction x using OnePoint.rec with
  | infty => simp
  | coe x =>
    induction y using OnePoint.rec with
    | infty => simp
    | coe y => simp

theorem map_surjective : Surjective (map (E := E) (F := F)) := by
  intro z
  induction z using OnePoint.rec with
  | infty => exact ⟨(∞, ∞), map_infty_left ∞⟩
  | coe p => exact ⟨(↑p.1, ↑p.2), map_coe p.1 p.2⟩

section Topology

variable [TopologicalSpace E] [TopologicalSpace F]

theorem finiteTube_isOpenEmbedding : IsOpenEmbedding (finiteTube (E := E) (F := F)) :=
  (OnePoint.isOpenEmbedding_coe.prodMap OnePoint.isOpenEmbedding_coe).comp
    (Homeomorph.uniqueProd Unit (E × F)).isOpenEmbedding

variable [T2Space E] [T2Space F] [LocallyCompactSpace E] [LocallyCompactSpace F]

theorem continuous_map : Continuous (map (E := E) (F := F)) :=
  OpenFiberCollapse.continuous_collapse finiteTube finiteTube_isOpenEmbedding

def continuousMap : C(OnePoint E × OnePoint F, OnePoint (E × F)) :=
  ⟨map, continuous_map⟩

theorem isQuotientMap_map : IsQuotientMap (map (E := E) (F := F)) :=
  IsQuotientMap.of_surjective_continuous map_surjective continuous_map

end Topology

end NoExoticSixSphere.OnePointProduct
