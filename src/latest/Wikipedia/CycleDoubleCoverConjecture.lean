import Mathlib

universe u

open scoped BigOperators

namespace CycleDoubleCoverConjecture

abbrev F₂ := ZMod 2

structure FiniteGraph (V E : Type*) [Fintype V] [Fintype E] where
  endAt : E → Fin 2 → V
  loopless : ∀ e, endAt e 0 ≠ endAt e 1

namespace FiniteGraph

def edgeIncidence {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] (G : FiniteGraph V E)
    (v : V) (e : E) : F₂ :=
  (if G.endAt e 0 = v then 1 else 0) +
    (if G.endAt e 1 = v then 1 else 0)

def IsEvenEdgeSet {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] (G : FiniteGraph V E)
    (F : Finset E) : Prop :=
  ∀ v : V, ∑ e ∈ F, edgeIncidence G v e = 0

structure Cycle {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] (G : FiniteGraph V E) where
  edges : Finset E
  nonempty : edges.Nonempty
  even : IsEvenEdgeSet G edges
  minimal : ∀ D : Finset E, D.Nonempty → D ⊆ edges → IsEvenEdgeSet G D → D = edges


structure CycleDoubleCover {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (G : FiniteGraph V E) where
  cycles : List (Cycle G)
  coveredTwice : ∀ e : E, (cycles.filter fun C ↦ e ∈ C.edges).length = 2

end FiniteGraph

open FiniteGraph


abbrev Gamma := Fin 3 → F₂

structure CubicGraph (V E : Type*) [Fintype V] [Fintype E] where
  incidence : (V × Fin 3) ≃ (E × Fin 2)
  loopless : ∀ e : E,
    (incidence.symm (e, 0)).1 ≠ (incidence.symm (e, 1)).1

def CubicGraph.edgeAt {V E : Type*} [Fintype V] [Fintype E] (G : CubicGraph V E) (v : V) (i : Fin 3)
    : E := (G.incidence (v, i)).1

def CubicGraph.endAt {V E : Type*} [Fintype V] [Fintype E] (G : CubicGraph V E) (e : E) (j : Fin 2)
    : V := (G.incidence.symm (e, j)).1

@[simp]
lemma CubicGraph.endAt_edgeAt_incidence {V E : Type*} [Fintype V] [Fintype E] (G : CubicGraph V E)
    (v : V) (i : Fin 3) :
    G.endAt (G.edgeAt v i) (G.incidence (v, i)).2 = v := by
  simp [edgeAt, endAt]

lemma CubicGraph.edgeAt_injective {V E : Type*} [Fintype V] [Fintype E] (G : CubicGraph V E) (v : V)
    : Function.Injective (G.edgeAt v) := by
  intro i j h
  refine congrArg Prod.snd (G.incidence.injective (Prod.ext h ?_))
  have := G.endAt_edgeAt_incidence v i
  have := G.endAt_edgeAt_incidence v j
  have := G.loopless (G.edgeAt v i)
  generalize (G.incidence (v, i)).2 = a, (G.incidence (v, j)).2 = b at *
  fin_cases a <;> fin_cases b <;> simp_all [endAt]

lemma CubicGraph.sum_edgeEnds_eq_sum_vertexSlots {V E : Type*} [Fintype V] [Fintype E]
    (G : CubicGraph V E)
    {A : Type*} [AddCommMonoid A] (h : E → Fin 2 → A) :
    ∑ e : E, ∑ j : Fin 2, h e j =
      ∑ v : V, ∑ i : Fin 3,
        h (G.edgeAt v i) (G.incidence (v, i)).2 := by
  simpa [Fintype.sum_prod_type, edgeAt] using (G.incidence.sum_comp fun x => h x.1 x.2).symm

structure GammaFlow {V E : Type*} [Fintype V] [Fintype E] (G : CubicGraph V E) where
  val : E → Gamma
  nowhereZero : ∀ e, val e ≠ 0
  conservation : ∀ v, ∑ i : Fin 3, val (G.edgeAt v i) = 0

def pairIndicator (p h s : Gamma) : F₂ := if s = p ∨ s = p + h then 1 else 0

def localBase {V E : Type*} [Fintype V] [Fintype E] [DecidableEq E] (G : CubicGraph V E)
    (f : GammaFlow G) (v : V) (e : E) : Gamma :=
  if e = G.edgeAt v 1 then f.val (G.edgeAt v 0) else 0

def compatibilityRhs {V E : Type*} [Fintype V] [Fintype E] [DecidableEq E] (G : CubicGraph V E)
    (f : GammaFlow G) (e : E) : Gamma :=
  localBase G f (G.endAt e 0) e + localBase G f (G.endAt e 1) e

def compatibilityMap {V E : Type*} [Fintype V] [Fintype E] (G : CubicGraph V E) (f : GammaFlow G) :
    ((V → Gamma) × (E → F₂)) →ₗ[F₂] (E → Gamma) where
  toFun x e := x.1 (G.endAt e 0) + x.1 (G.endAt e 1) + x.2 e • f.val e
  map_add' x y := by
    ext e i
    dsimp
    ring
  map_smul' c x := by
    ext e i
    dsimp
    ring

def coordinateFunctional {E : Type*} [DecidableEq E] (φ : Module.Dual F₂ (E → Gamma)) (e : E) :
    Module.Dual F₂ Gamma :=
  φ.comp (LinearMap.single F₂ (fun _ : E ↦ Gamma) e)

lemma dual_apply_eq_sum_coordinates {E : Type*} [Fintype E] [DecidableEq E]
    (φ : Module.Dual F₂ (E → Gamma)) (y : E → Gamma) :
    φ y = ∑ e : E, coordinateFunctional φ e (y e) := by
  conv_lhs => rw [← LinearMap.sum_single_apply (fun _ : E ↦ Gamma) y]
  simp [coordinateFunctional]

def functionalCode (η : Module.Dual F₂ Gamma) : Gamma :=
  fun i ↦ η (Pi.single i 1)

def gammaPairing (a x : Gamma) : F₂ := ∑ i : Fin 3, x i * a i

lemma functional_apply_eq_pairing (η : Module.Dual F₂ Gamma) (x : Gamma) :
    η x = gammaPairing (functionalCode η) x := by
  conv_lhs => rw [show x = ∑ i, x i • Pi.single i 1 by ext j; simp [Pi.single_apply]]
  simp [gammaPairing, functionalCode]

def functionalNonzero (η : Module.Dual F₂ Gamma) : F₂ :=
  if functionalCode η = 0 then 0 else 1

lemma flow_triple_properties :
    ∀ (x y z : Gamma), x ≠ 0 → y ≠ 0 → z ≠ 0 → x + y + z = 0 →
      z = x + y ∧ x ≠ y := by
  decide

lemma compatibility_solvable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq E]
    (G : CubicGraph V E) (f : GammaFlow G) :
    compatibilityRhs G f ∈ LinearMap.range (compatibilityMap G f) := by
  classical
  refine (Subspace.forall_mem_dualAnnihilator_apply_eq_zero_iff
    (compatibilityMap G f).range (compatibilityRhs G f)).mp ?_
  intro φ hφ
  simp only [Submodule.mem_dualAnnihilator, LinearMap.mem_range, Prod.exists,
    forall_exists_index] at hφ
  have hmap (x : (V → Gamma) × (E → F₂)) : φ ((compatibilityMap G f) x) = 0 :=
    hφ _ x.1 x.2 rfl
  let η := coordinateFunctional φ
  have hedge (e : E) : η e (f.val e) = 0 := by
    have heq : (compatibilityMap G f) (0, Pi.single e 1) = Pi.single e (f.val e) := by
      ext e' i
      by_cases h : e = e' <;> simp [compatibilityMap, h]
    change φ (Pi.single e (f.val e)) = 0
    rw [← heq]
    exact hmap (0, Pi.single e 1)
  have hvertex_global (x : V → Gamma) :
      ∑ v : V, ∑ i : Fin 3, η (G.edgeAt v i) (x v) = 0 := by
    calc
      _ = ∑ e : E, ∑ j : Fin 2,
          η e (x (G.endAt e j)) := by
            symm
            simpa using G.sum_edgeEnds_eq_sum_vertexSlots
              (fun e j ↦ η e (x (G.endAt e j)))
      _ = φ ((compatibilityMap G f) (x, 0)) := by
            rw [dual_apply_eq_sum_coordinates]
            apply Finset.sum_congr rfl
            intro e _
            simp [η, compatibilityMap, Fin.sum_univ_succ]
      _ = 0 := hmap (x, 0)
  have hvertex (v : V) (x : Gamma) :
      ∑ i : Fin 3, η (G.edgeAt v i) x = 0 := by
    simpa [Pi.single_apply, apply_ite, eq_comm] using hvertex_global (Pi.single v x)
  have hcode (v : V) :
      ∑ i : Fin 3, functionalCode (η (G.edgeAt v i)) = 0 := by
    ext k
    simpa [functionalCode] using hvertex v (Pi.single k 1)
  have finite_check : (∀ a b p q r : Gamma,
      a ≠ 0 → b ≠ 0 → a ≠ b →
      p + q + r = 0 →
      gammaPairing p a = 0 → gammaPairing q b = 0 →
      gammaPairing r (a + b) = 0 →
      gammaPairing q a =
        (if p = 0 then 0 else 1) + (if q = 0 then 0 else 1) +
          (if r = 0 then 0 else 1)) ∧ (∀ x : F₂, 2 * x = 0) := by
    letI (P : Gamma → Prop) [DecidablePred P] : Decidable (∀ x, P x) :=
      Fintype.decidableForallFintype
    letI (P : F₂ → Prop) [DecidablePred P] : Decidable (∀ x, P x) :=
      Fintype.decidableForallFintype
    decide
  have hflow (v : V) :
      f.val (G.edgeAt v 2) = f.val (G.edgeAt v 0) + f.val (G.edgeAt v 1) ∧
        f.val (G.edgeAt v 0) ≠ f.val (G.edgeAt v 1) := by
    apply flow_triple_properties
    · exact f.nowhereZero _
    · exact f.nowhereZero _
    · exact f.nowhereZero _
    · simpa [Fin.sum_univ_succ, add_assoc] using f.conservation v
  have hlocal (v : V) :
      η (G.edgeAt v 1) (f.val (G.edgeAt v 0)) =
        ∑ i : Fin 3, functionalNonzero (η (G.edgeAt v i)) := by
    let p0 := functionalCode (η (G.edgeAt v 0))
    let p1 := functionalCode (η (G.edgeAt v 1))
    let p2 := functionalCode (η (G.edgeAt v 2))
    have hpsum : p0 + p1 + p2 = 0 := by
      simpa [p0, p1, p2, Fin.sum_univ_succ, add_assoc] using hcode v
    have hd0 : gammaPairing p0 (f.val (G.edgeAt v 0)) = 0 := by
      simpa [p0, functional_apply_eq_pairing] using hedge (G.edgeAt v 0)
    have hd1 : gammaPairing p1 (f.val (G.edgeAt v 1)) = 0 := by
      simpa [p1, functional_apply_eq_pairing] using hedge (G.edgeAt v 1)
    have hd2 : gammaPairing p2
        (f.val (G.edgeAt v 0) + f.val (G.edgeAt v 1)) = 0 := by
      rw [← (hflow v).1]
      simpa [p2, functional_apply_eq_pairing] using hedge (G.edgeAt v 2)
    have halg := finite_check.1
      (f.val (G.edgeAt v 0)) (f.val (G.edgeAt v 1)) p0 p1 p2
      (f.nowhereZero _) (f.nowhereZero _) (hflow v).2 hpsum hd0 hd1 hd2
    rw [functional_apply_eq_pairing]
    convert halg using 1
    all_goals simp [functionalNonzero, Fin.sum_univ_succ, p0, p1, p2, add_assoc]
    all_goals rfl
  rw [dual_apply_eq_sum_coordinates]
  calc
    ∑ e : E, η e (compatibilityRhs G f e) =
        ∑ e : E, ∑ j : Fin 2,
          η e (localBase G f (G.endAt e j) e) := by
      apply Finset.sum_congr rfl
      intro e _
      simp [compatibilityRhs, Fin.sum_univ_succ]
    _ = ∑ v : V, ∑ i : Fin 3,
        η (G.edgeAt v i) (localBase G f v (G.edgeAt v i)) := by
      simpa using G.sum_edgeEnds_eq_sum_vertexSlots
        (fun e j ↦ η e (localBase G f (G.endAt e j) e))
    _ = ∑ v : V,
        η (G.edgeAt v 1) (f.val (G.edgeAt v 0)) := by
      apply Finset.sum_congr rfl
      intro v _
      have h01 : G.edgeAt v 0 ≠ G.edgeAt v 1 := by
        intro h
        have := G.edgeAt_injective v h
        omega
      have h21 : G.edgeAt v 2 ≠ G.edgeAt v 1 := by
        intro h
        have := G.edgeAt_injective v h
        omega
      simp [Fin.sum_univ_succ, localBase, h01, h21]
    _ = ∑ v : V, ∑ i : Fin 3,
        functionalNonzero (η (G.edgeAt v i)) := by
      apply Finset.sum_congr rfl
      intro v _
      exact hlocal v
    _ = ∑ e : E, ∑ j : Fin 2, functionalNonzero (η e) := by
      symm
      simpa using G.sum_edgeEnds_eq_sum_vertexSlots
        (fun e (_ : Fin 2) ↦ functionalNonzero (η e))
    _ = 0 := by
      simp [finite_check.2]

structure CubicLabeling {V E : Type*} [Fintype V] [Fintype E] (G : CubicGraph V E) (f : GammaFlow G)
    where
  base : E → Gamma
  vertexParity : ∀ v s,
    ∑ i : Fin 3, pairIndicator (base (G.edgeAt v i)) (f.val (G.edgeAt v i)) s = 0

noncomputable def cubic_labeling {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V]
    [DecidableEq E] (G : CubicGraph V E) (f : GammaFlow G) : CubicLabeling G f := by
  have local_pair_parity :
      ∀ (x y t s : Gamma), x ≠ 0 → y ≠ 0 → x ≠ y →
        pairIndicator t x s +
        pairIndicator (t + x) y s +
        pairIndicator t (x + y) s = 0 := by
    decide
  have pairIndicator_eq_of_difference :
      ∀ (p q h : Gamma) (ε : F₂), h ≠ 0 → p + q = ε • h →
        pairIndicator p h = pairIndicator q h := by
    decide
  let x := Classical.choose (compatibility_solvable G f)
  have hx : compatibilityMap G f x = compatibilityRhs G f := by
    simpa [x] using Classical.choose_spec (compatibility_solvable G f)
  let t : V → Gamma := x.1
  let ε : E → F₂ := x.2
  let p : E → Gamma := fun e ↦ t (G.endAt e 0) + localBase G f (G.endAt e 0) e
  have hedge (e : E) :
      (t (G.endAt e 0) + localBase G f (G.endAt e 0) e) +
      (t (G.endAt e 1) + localBase G f (G.endAt e 1) e) = ε e • f.val e := by
    have hrearrange :
        ∀ (a b c d h : Gamma) (δ : F₂),
          a + b + δ • h = c + d → (a + c) + (b + d) = δ • h := by
      intro a b c d h δ hab
      ext i
      have hi := congrFun hab i
      dsimp at hi ⊢
      calc
        a i + c i + (b i + d i) = (a i + b i) + (c i + d i) := by ring
        _ = (a i + b i) + (a i + b i + δ * h i) := by rw [hi]
        _ = ((a i + b i) + (a i + b i)) + δ * h i := by ring
        _ = δ * h i := by rw [CharTwo.add_self_eq_zero, zero_add]
    apply hrearrange
    have := congrFun hx e
    simpa [compatibilityMap, compatibilityRhs, t, ε] using this
  have hp_endpoint (e : E) (j : Fin 2) :
      pairIndicator (p e) (f.val e) =
        pairIndicator (t (G.endAt e j) + localBase G f (G.endAt e j) e) (f.val e) := by
    fin_cases j
    · rfl
    · apply pairIndicator_eq_of_difference _ _ _ (ε e) (f.nowhereZero e)
      simpa [p, add_assoc, add_left_comm, add_comm] using hedge e
  refine ⟨p, ?_⟩
  intro v s
  have hslot (i : Fin 3) :
      pairIndicator (p (G.edgeAt v i)) (f.val (G.edgeAt v i)) =
        pairIndicator
          (t v + localBase G f v (G.edgeAt v i))
          (f.val (G.edgeAt v i)) := by
    let j := (G.incidence (v, i)).2
    have hend : G.endAt (G.edgeAt v i) j = v := by
      dsimp [j]
      exact G.endAt_edgeAt_incidence v i
    simpa only [hend] using hp_endpoint (G.edgeAt v i) j
  simp_rw [hslot]
  let x₀ := f.val (G.edgeAt v 0)
  let y₀ := f.val (G.edgeAt v 1)
  let z₀ := f.val (G.edgeAt v 2)
  have hsum : x₀ + y₀ + z₀ = 0 := by
    simpa [x₀, y₀, z₀, Fin.sum_univ_three] using f.conservation v
  obtain ⟨hz, hxy⟩ := flow_triple_properties x₀ y₀ z₀
    (f.nowhereZero _) (f.nowhereZero _) (f.nowhereZero _) hsum
  have hinj := G.edgeAt_injective v
  rw [Fin.sum_univ_three]
  simpa [localBase, x₀, y₀, z₀, hz,
    hinj.ne (by decide : (0 : Fin 3) ≠ 1),
    hinj.ne (by decide : (2 : Fin 3) ≠ 1)] using
      local_pair_parity x₀ y₀ (t v) s
        (f.nowhereZero _) (f.nowhereZero _) hxy

structure CubicGraph.IndexedEvenDoubleCover {V E : Type*} [Fintype V] [Fintype E]
    (G : CubicGraph V E) where
  member : Gamma → E → F₂
  vertexEven : ∀ s v, ∑ i : Fin 3, member s (G.edgeAt v i) = 0
  coveredTwice : ∀ e,
    (Finset.univ.filter fun s : Gamma ↦ member s e = 1).card = 2

noncomputable def cubic_even_double_cover {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V]
    [DecidableEq E] (G : CubicGraph V E) (f : GammaFlow G) :
    CubicGraph.IndexedEvenDoubleCover G := by
  let P := cubic_labeling G f
  refine
    { member := fun s e ↦ pairIndicator (P.base e) (f.val e) s
      vertexEven := ?_
      coveredTwice := ?_ }
  · intro s v
    exact P.vertexParity v s
  · intro e
    exact (by decide :
      ∀ (p h : Gamma), h ≠ 0 →
        (Finset.univ.filter fun s : Gamma ↦ pairIndicator p h s = 1).card = 2)
      (P.base e) (f.val e) (f.nowhereZero e)

abbrev HalfEdge (E : Type*) := E × Fin 2

def vertex {V E : Type*} [Fintype V] [Fintype E] (G : FiniteGraph V E) (h : HalfEdge E) : V :=
    G.endAt h.1 h.2

def halfEdgesAt {V E : Type*} [Fintype V] [Fintype E] (G : FiniteGraph V E) (v : V) :=
    {h : HalfEdge E // (vertex G) h = v}

instance {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] (G : FiniteGraph V E) (v : V) :
    Fintype ((halfEdgesAt G) v) :=
  Subtype.fintype (fun h : HalfEdge E ↦ (vertex G) h = v)

def degree {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] (G : FiniteGraph V E) (v : V) : ℕ
    := Fintype.card ((halfEdgesAt G) v)

def Crosses {V E : Type*} [Fintype V] [Fintype E] (G : FiniteGraph V E) (S : Finset V) (e : E) :
    Prop :=
  (G.endAt e 0 ∈ S) ≠ (G.endAt e 1 ∈ S)

noncomputable def cut {V E : Type*} [Fintype V] [Fintype E] (G : FiniteGraph V E) (S : Finset V) :
    Finset E := by
  classical
  exact Finset.univ.filter ((Crosses G) S)

def Bridgeless {V E : Type*} [Fintype V] [Fintype E] (G : FiniteGraph V E) : Prop :=
  ∀ S : Finset V, (cut G S).card ≠ 1

def IsFlow {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] (G : FiniteGraph V E) {A : Type*}
    [AddCommGroup A] (f : E → A) : Prop :=
  ∀ v : V,
    (∑ e : E, if G.endAt e 0 = v then f e else 0) -
      (∑ e : E, if G.endAt e 1 = v then f e else 0) = 0

def IsNowhereZero {E : Type*} {A : Type*} [Zero A] (f : E → A) : Prop := ∀ e, f e ≠ 0

structure NowhereZeroFlow {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V]
    (G : FiniteGraph V E) (A : Type*) [AddCommGroup A] [Zero A] where
  val : E → A
  conservation : (IsFlow G) val
  nowhereZero : IsNowhereZero val

structure IndexedEvenDoubleCover {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V]
    (G : FiniteGraph V E) where
  member : Gamma → E → F₂
  vertexEven : ∀ s v,
    ∑ e : E,
      ((if G.endAt e 0 = v then member s e else 0) +
       (if G.endAt e 1 = v then member s e else 0)) = 0
  coveredTwice : ∀ e,
    (Finset.univ.filter fun s : Gamma ↦ member s e = 1).card = 2

def CubicGraph.toFiniteGraph {V E : Type*} [Fintype V] [Fintype E] (K : CubicGraph V E) :
    FiniteGraph V E where
  endAt := K.endAt
  loopless := by
    intro e
    exact K.loopless e

@[simp]
lemma CubicGraph.neg_gamma : ∀ x : Gamma, -x = x := by decide

def CubicGraph.gammaFlowOfNowhereZero {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V]
    (K : CubicGraph V E)
    (f : (NowhereZeroFlow (K.toFiniteGraph)) Gamma) : GammaFlow K where
  val := f.val
  nowhereZero := f.nowhereZero
  conservation := by
    intro v
    have h := f.conservation v
    have hsigned :
        (∑ e : E, if K.endAt e 0 = v then f.val e else 0) +
          (∑ e : E, if K.endAt e 1 = v then f.val e else 0) = 0 := by
      simpa [toFiniteGraph, IsFlow, sub_eq_add_neg] using h
    have hinc :
        (∑ e : E, ∑ j : Fin 2, if K.endAt e j = v then f.val e else 0) =
          ∑ i : Fin 3, f.val (K.edgeAt v i) := by
      rw [K.sum_edgeEnds_eq_sum_vertexSlots]
      simp only [K.endAt_edgeAt_incidence]
      calc
        (∑ w : V, ∑ i : Fin 3, if w = v then f.val (K.edgeAt w i) else 0) =
            ∑ i : Fin 3, if v = v then f.val (K.edgeAt v i) else 0 := by
              apply Fintype.sum_eq_single v
              intro w hw
              simp [hw]
        _ = ∑ i : Fin 3, f.val (K.edgeAt v i) := by simp
    rw [← hinc]
    simp only [Fin.sum_univ_two]
    rw [Finset.sum_add_distrib]
    exact hsigned

def divergence {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] (G : FiniteGraph V E)
    {A : Type*} [AddCommGroup A] (f : E → A) (v : V) : A :=
  (∑ k : E, if G.endAt k 0 = v then f k else 0) -
    ∑ k : E, if G.endAt k 1 = v then f k else 0

lemma divergence_add {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] (G : FiniteGraph V E)
    {A : Type*} [AddCommGroup A] (f g : E → A) (v : V) :
    (divergence G) (f + g) v = (divergence G) f v + (divergence G) g v := by
  have hsum (j : Fin 2) :
      (∑ k : E, if G.endAt k j = v then (f + g) k else 0) =
        (∑ k : E, if G.endAt k j = v then f k else 0) +
          ∑ k : E, if G.endAt k j = v then g k else 0 := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro k _
    by_cases h : G.endAt k j = v <;> simp [h]
  simp only [divergence, hsum]
  abel

lemma divergence_neg {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] (G : FiniteGraph V E)
    {A : Type*} [AddCommGroup A] (f : E → A) (v : V) :
    (divergence G) (-f) v = -(divergence G) f v := by
  unfold divergence
  have h (j : Fin 2) : (∑ k : E, if G.endAt k j = v then (-f) k else 0) =
      -(∑ k : E, if G.endAt k j = v then f k else 0) := by
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro k _
    split_ifs <;> simp
  rw [h 0, h 1]
  abel

def HasIntegerPath {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] (G : FiniteGraph V E)
    (S : Finset E) (u v : V) : Prop :=
  ∃ c : E → ℤ, (∀ k ∈ S, c k = 0) ∧ ∀ w : V,
    (divergence G) c w = (if u = w then 1 else 0) - (if v = w then 1 else 0)

lemma divergence_single_one {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (G : FiniteGraph V E) (k : E) (w : V) :
    (divergence G) (Pi.single k (1 : ℤ)) w =
      (if G.endAt k 0 = w then 1 else 0) - (if G.endAt k 1 = w then 1 else 0) := by
  unfold divergence
  congr 1 <;> rw [Fintype.sum_eq_single k] <;> simp_all

lemma hasIntegerPath_single {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V]
    (G : FiniteGraph V E) (S : Finset E) (k : E) (hk : k ∉ S) :
    (HasIntegerPath G) S (G.endAt k 0) (G.endAt k 1) := by
  classical
  refine ⟨Pi.single k 1, ?_, (divergence_single_one G) k⟩
  intro e he
  simp [ne_of_mem_of_not_mem he hk]

lemma HasIntegerPath.symm {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V]
    (G : FiniteGraph V E) {S : Finset E} {u v : V}
    (h : (HasIntegerPath G) S u v) : (HasIntegerPath G) S v u := by
  rcases h with ⟨c,hc,h⟩
  exact ⟨-c, by simpa using hc, fun w ↦ by
    rw [(divergence_neg G), h]
    omega⟩

lemma HasIntegerPath.trans {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V]
    (G : FiniteGraph V E) {S : Finset E} {u v w : V}
    (h₁ : (HasIntegerPath G) S u v) (h₂ : (HasIntegerPath G) S v w) :
    (HasIntegerPath G) S u w := by
  rcases h₁ with ⟨f,hf,F⟩
  rcases h₂ with ⟨g,hg,H⟩
  refine ⟨f + g, ?_, ?_⟩
  · intro k hk
    simp [hf k hk, hg k hk]
  intro x
  rw [(divergence_add G),F x,H x]
  omega

def HasCycleCorrection {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (G : FiniteGraph V E) (S : Finset E) (e : E) : Prop :=
  ∃ c : E → ℤ, (IsFlow G) c ∧ c e = 1 ∧ ∀ k ∈ S.erase e, c k = 0

def IndexedEvenDoubleCover.support {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V]
    (G : FiniteGraph V E) (C : (IndexedEvenDoubleCover G)) (s : Gamma) : Finset E :=
  Finset.univ.filter fun e ↦ C.member s e = 1

noncomputable def IndexedEvenDoubleCover.toCycleDoubleCover {V E : Type*} [Fintype V] [Fintype E]
    [DecidableEq V] [DecidableEq E] (G : FiniteGraph V E)
    (C : (IndexedEvenDoubleCover G)) : CycleDoubleCover G := by
  classical
  have decompose : ∀ (F : Finset E), IsEvenEdgeSet G F →
      ∃ L : List (Cycle G),
        ∀ e : E, (L.filter fun Z ↦ e ∈ Z.edges).length =
          if e ∈ F then 1 else 0 := by
    intro F hF
    revert hF
    refine Finset.strongInductionOn F ?_
    intro F ih hF
    by_cases hne : F.Nonempty
    · by_cases hmin :
        (∀ D : Finset E, D.Nonempty → D ⊆ F → IsEvenEdgeSet G D → D = F)
      · let Z : Cycle G :=
          { edges := F
            nonempty := hne
            even := hF
            minimal := hmin }
        refine ⟨[Z], ?_⟩
        intro e
        by_cases he : e ∈ F <;> simp [Z, he]
      · push Not at hmin
        obtain ⟨D, hDne, hDF, hDeven, hDproper⟩ := hmin
        have hDssub : D ⊂ F := Finset.ssubset_iff_subset_ne.mpr ⟨hDF, hDproper⟩
        have hRssub : F \ D ⊂ F := by
          apply Finset.ssubset_iff_subset_ne.mpr
          refine ⟨Finset.sdiff_subset, ?_⟩
          intro heq
          obtain ⟨e, heD⟩ := hDne
          have : e ∈ F \ D := by simpa [heq] using hDF heD
          simp [heD] at this
        have hReven : IsEvenEdgeSet G (F \ D) := by
          intro v
          have hsplit := Finset.sum_sdiff hDF (f := fun e ↦ edgeIncidence G v e)
          rw [hDeven v, hF v] at hsplit
          simpa using hsplit
        obtain ⟨LD, hLD⟩ := ih D hDssub hDeven
        obtain ⟨LR, hLR⟩ := ih (F \ D) hRssub hReven
        refine ⟨LD ++ LR, ?_⟩
        intro e
        rw [List.filter_append, List.length_append, hLD e, hLR e]
        by_cases heD : e ∈ D
        · have heF : e ∈ F := hDF heD
          simp [heD, heF]
        · by_cases heF : e ∈ F <;> simp [heD, heF]
    · have hzero : F = ∅ := Finset.not_nonempty_iff_eq_empty.mp hne
      subst F
      exact ⟨[], by simp⟩
  have zero_or_one (x : F₂) : x = 0 ∨ x = 1 := by
    fin_cases x
    · exact Or.inl rfl
    · exact Or.inr rfl
  have hex : ∀ s : Gamma, ∃ L : List (Cycle G),
      ∀ e : E, (L.filter fun Z ↦ e ∈ Z.edges).length =
        if e ∈ IndexedEvenDoubleCover.support G C s then 1 else 0 := by
    intro s
    apply decompose (IndexedEvenDoubleCover.support G C s)
    intro v
    rw [← C.vertexEven s v]
    simp only [IndexedEvenDoubleCover.support, Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro e _
    rcases zero_or_one (C.member s e) with hz | ho
    · simp [hz]
    · simp [edgeIncidence, ho]
  choose pieces hpieces using hex
  refine
    { cycles := Finset.univ.toList.flatMap pieces
      coveredTwice := ?_ }
  intro e
  have hfilter (xs : List Gamma) :
      ((xs.flatMap pieces).filter fun Z ↦ e ∈ Z.edges).length =
        (xs.map fun s ↦ ((pieces s).filter fun Z ↦ e ∈ Z.edges).length).sum := by
    induction xs with
    | nil => simp
    | cons s xs ih => simp [ih]
  rw [hfilter]
  simp_rw [hpieces]
  simpa [IndexedEvenDoubleCover.support] using C.coveredTwice e

structure RotationSystem {V E : Type*} [Fintype V] [Fintype E] (G : FiniteGraph V E) where
  next : Equiv.Perm (HalfEdge E)
  sameVertex : ∀ h, (vertex G) (next h) = (vertex G) h
  next_ne : ∀ h, next h ≠ h
  fiberTransitive : ∀ h k, (vertex G) h = (vertex G) k →
    ∃ n : ℕ, (next : HalfEdge E → HalfEdge E)^[n] h = k

def halfEdgeSigmaEquiv {V E : Type*} [Fintype V] [Fintype E] (G : FiniteGraph V E) : HalfEdge E ≃
    (v : V) × (halfEdgesAt G) v where
  toFun h := ⟨(vertex G) h, h, rfl⟩
  invFun p := p.2.1
  left_inv _ := rfl
  right_inv p := by
    rcases p with ⟨v, ⟨h, hh⟩⟩
    dsimp
    subst v
    rfl

noncomputable def fiberCycle {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V]
    (G : FiniteGraph V E) (v : V) : Equiv.Perm ((halfEdgesAt G) v) :=
  (Fintype.equivFin ((halfEdgesAt G) v)).trans
    ((finRotate (Fintype.card ((halfEdgesAt G) v))).trans
      (Fintype.equivFin ((halfEdgesAt G) v)).symm)

noncomputable def rotationPerm {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V]
    (G : FiniteGraph V E) : Equiv.Perm (HalfEdge E) :=
  (halfEdgeSigmaEquiv G).trans
    ((Equiv.sigmaCongrRight (fiberCycle G)).trans (halfEdgeSigmaEquiv G).symm)

noncomputable def rotationSystemOfDegreeNeOne {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V]
    (G : FiniteGraph V E) (hne : ∀ v, (degree G) v ≠ 1) :
    (RotationSystem G) := by
  have sameVertex (h : HalfEdge E) :
      (vertex G) (rotationPerm G h) = (vertex G) h := by
    change (vertex G) (fiberCycle G ((vertex G) h) ⟨h, rfl⟩).1 = (vertex G) h
    exact (fiberCycle G ((vertex G) h) ⟨h, rfl⟩).property
  have next_ne (h : HalfEdge E) : rotationPerm G h ≠ h := by
    have hrotate {n : ℕ} (hn : n ≠ 1) (a : Fin n) : finRotate n a ≠ a := by
      haveI : NeZero n := a.neZero
      intro h
      rw [finRotate_apply] at h
      have hn2 : 2 ≤ n := by omega
      have hh : a + 1 = a + 0 := by simpa using h
      have hz : (1 : Fin n) = 0 := add_left_cancel hh
      have hv := congrArg Fin.val hz
      norm_num at hv
      omega
    intro heq
    have hs := congrArg (halfEdgeSigmaEquiv G) heq
    simp only [rotationPerm, Equiv.trans_apply, Equiv.apply_symm_apply] at hs
    change (⟨(vertex G) h, fiberCycle G ((vertex G) h) ⟨h, rfl⟩⟩ :
        (v : V) × (halfEdgesAt G) v) = ⟨(vertex G) h, ⟨h, rfl⟩⟩ at hs
    have hf : fiberCycle G ((vertex G) h) ⟨h, rfl⟩ = ⟨h, rfl⟩ := by
      injection hs
    have hi := congrArg (Fintype.equivFin ((halfEdgesAt G) ((vertex G) h))) hf
    simp only [fiberCycle, Equiv.trans_apply, Equiv.apply_symm_apply] at hi
    exact hrotate (hne ((vertex G) h)) _ hi
  have fiberTransitive (h k : HalfEdge E) (hvk : (vertex G) h = (vertex G) k) :
      ∃ n : ℕ, (rotationPerm G : HalfEdge E → HalfEdge E)^[n] h = k := by
    let v := (vertex G) h
    let eh : (halfEdgesAt G) v := ⟨h, rfl⟩
    let ek : (halfEdgesAt G) v := ⟨k, hvk.symm⟩
    let ef := Fintype.equivFin ((halfEdgesAt G) v)
    obtain ⟨n, hn⟩ : ∃ n : ℕ,
        (finRotate (Fintype.card ((halfEdgesAt G) v)) :
          Fin (Fintype.card ((halfEdgesAt G) v)) →
            Fin (Fintype.card ((halfEdgesAt G) v)))^[n] (ef eh) = ef ek := by
      haveI : NeZero (Fintype.card ((halfEdgesAt G) v)) := (ef eh).neZero
      refine ⟨(ef ek - ef eh).val, ?_⟩
      rw [← finCycle_eq_finRotate_iterate]
      simp only [finCycle_apply]
      rw [sub_eq_add_neg]
      abel
    have hsemFiber : Function.Semiconj ef (fiberCycle G v)
        (finRotate (Fintype.card ((halfEdgesAt G) v))) := by
      intro x
      simp only [ef, fiberCycle, Equiv.trans_apply, Equiv.apply_symm_apply]
    have hfiber : (fiberCycle G v : (halfEdgesAt G) v → (halfEdgesAt G) v)^[n] eh = ek := by
      apply ef.injective
      rw [hsemFiber.iterate_right]
      exact hn
    let sigmaCycle : Equiv.Perm ((v : V) × (halfEdgesAt G) v) :=
      Equiv.sigmaCongrRight (fiberCycle G)
    let embed : (halfEdgesAt G) v → ((v : V) × (halfEdgesAt G) v) := fun x ↦ ⟨v, x⟩
    have hsemEmbed : Function.Semiconj embed (fiberCycle G v) sigmaCycle := by
      intro x
      rfl
    have hsigma : (sigmaCycle : ((v : V) × (halfEdgesAt G) v) →
        ((v : V) × (halfEdgesAt G) v))^[n] ⟨v, eh⟩ = ⟨v, ek⟩ := by
      rw [← hsemEmbed.iterate_right]
      exact congrArg embed hfiber
    have hsemGlobal : Function.Semiconj (halfEdgeSigmaEquiv G) (rotationPerm G)
        sigmaCycle := by
      intro x
      simp only [rotationPerm, sigmaCycle, Equiv.trans_apply, Equiv.apply_symm_apply]
    refine ⟨n, (halfEdgeSigmaEquiv G).injective ?_⟩
    rw [hsemGlobal.iterate_right]
    have hh : halfEdgeSigmaEquiv G h = ⟨v, eh⟩ := rfl
    have hk : halfEdgeSigmaEquiv G k = ⟨v, ek⟩ := by
      apply Sigma.ext hvk.symm
      apply (Subtype.heq_iff_coe_eq (fun x => by simp [v, hvk, halfEdgeSigmaEquiv])).2
      rfl
    rw [hh, hk]
    exact hsigma
  exact
    { next := rotationPerm G
      sameVertex := sameVertex
      next_ne := next_ne
      fiberTransitive := fiberTransitive }

noncomputable def rotationSystemOfBridgeless {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V]
    (G : FiniteGraph V E) (hb : (Bridgeless G)) : (RotationSystem G) := by
  have hdegree (v : V) : (degree G) v ≠ 1 := by
    intro hd
    obtain ⟨h, hh⟩ := Fintype.card_eq_one_iff.mp hd
    let e : E := h.1.1
    have hend : G.endAt e h.1.2 = v := h.2
    have hcut : (cut G) {v} = {e} := by
      ext k
      simp only [cut, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
      constructor
      · intro hk
        simp only [Crosses, Finset.mem_singleton] at hk
        by_cases hk0 : G.endAt k 0 = v
        · have hkhe : (⟨(k, 0), hk0⟩ : (halfEdgesAt G) v) = h := hh _
          exact congrArg (fun q ↦ q.1.1) hkhe
        · have hk1 : G.endAt k 1 = v := by
            simpa [hk0] using hk
          have hkhe : (⟨(k, 1), hk1⟩ : (halfEdgesAt G) v) = h := hh _
          exact congrArg (fun q ↦ q.1.1) hkhe
      · intro hke
        subst k
        simp only [Crosses, Finset.mem_singleton]
        have hj : h.1.2 = 0 ∨ h.1.2 = 1 := by omega
        rcases hj with hj | hj
        · rw [hj] at hend
          have hne : G.endAt e 1 ≠ v := by
            intro hz
            exact G.loopless e (hend.trans hz.symm)
          simp [hend, hne]
        · rw [hj] at hend
          have hne : G.endAt e 0 ≠ v := by
            intro hz
            exact G.loopless e (hz.trans hend.symm)
          simp [hend, hne]
    have hc := hb {v}
    rw [hcut] at hc
    exact hc (Finset.card_singleton e)
  exact rotationSystemOfDegreeNeOne G hdegree

abbrev ExpandedVertex {V E : Type*} [Fintype V] [Fintype E] (_G : FiniteGraph V E) := HalfEdge E

abbrev ExpandedEdge {V E : Type*} [Fintype V] [Fintype E] (_G : FiniteGraph V E) := E ⊕ HalfEdge E

private def expansionToEnd {V E : Type*} [Fintype V] [Fintype E] (G : FiniteGraph V E)
    (R : (RotationSystem G)) :
    ((ExpandedVertex G) × Fin 3) → ((ExpandedEdge G) × Fin 2) := fun p ↦
  if p.2 = 0 then
    (Sum.inl p.1.1, p.1.2)
  else if p.2 = 1 then
    (Sum.inr p.1, 0)
  else
    (Sum.inr (R.next.symm p.1), 1)

private def expansionFromEnd {V E : Type*} [Fintype V] [Fintype E] (G : FiniteGraph V E)
    (R : (RotationSystem G)) :
    ((ExpandedEdge G) × Fin 2) → ((ExpandedVertex G) × Fin 3)
  | (Sum.inl e, j) => ((e, j), 0)
  | (Sum.inr h, j) => if j = 0 then (h, 1) else (R.next h, 2)

noncomputable def expansionIncidence {V E : Type*} [Fintype V] [Fintype E] (G : FiniteGraph V E)
    (R : (RotationSystem G)) :
    ((ExpandedVertex G) × Fin 3) ≃ ((ExpandedEdge G) × Fin 2) := by
  have left_inv : Function.LeftInverse (expansionFromEnd G R) (expansionToEnd G R) := by
    rintro ⟨h, i⟩
    fin_cases i <;> simp [expansionToEnd, expansionFromEnd]
  have right_inv : Function.RightInverse (expansionFromEnd G R) (expansionToEnd G R) := by
    rintro ⟨e, j⟩
    cases e with
    | inl e => simp [expansionToEnd, expansionFromEnd]
    | inr h => fin_cases j <;> simp [expansionToEnd, expansionFromEnd]
  exact
    { toFun := expansionToEnd G R
      invFun := expansionFromEnd G R
      left_inv := left_inv
      right_inv := right_inv }

noncomputable def cubicExpansion {V E : Type*} [Fintype V] [Fintype E] (G : FiniteGraph V E)
    (R : (RotationSystem G)) : CubicGraph (ExpandedVertex G) (ExpandedEdge G) where
  incidence := expansionIncidence G R
  loopless := by
    intro e
    cases e with
    | inl e =>
        simp [expansionIncidence, expansionFromEnd]
    | inr h =>
        simpa [expansionIncidence, expansionFromEnd] using (R.next_ne h).symm

def expansionGraph {V E : Type*} [Fintype V] [Fintype E] (G : FiniteGraph V E)
    (R : (RotationSystem G)) : FiniteGraph (ExpandedVertex G) (ExpandedEdge G) where
  endAt
    | Sum.inl e, j => (e, j)
    | Sum.inr h, j => if j = 0 then h else R.next h
  loopless := by
    intro e
    cases e with
    | inl e =>
        intro heq
        exact Fin.zero_ne_one (congrArg Prod.snd heq)
    | inr h => simpa using (R.next_ne h).symm

@[simp]
lemma cubicExpansion_edgeAt_zero {V E : Type*} [Fintype V] [Fintype E] (G : FiniteGraph V E)
    (R : (RotationSystem G)) (h : (ExpandedVertex G)) :
    (cubicExpansion G R).edgeAt h 0 = Sum.inl h.1 := rfl

@[simp]
lemma cubicExpansion_edgeAt_one {V E : Type*} [Fintype V] [Fintype E] (G : FiniteGraph V E)
    (R : (RotationSystem G)) (h : (ExpandedVertex G)) :
    (cubicExpansion G R).edgeAt h 1 = Sum.inr h := rfl

@[simp]
lemma cubicExpansion_edgeAt_two {V E : Type*} [Fintype V] [Fintype E] (G : FiniteGraph V E)
    (R : (RotationSystem G)) (h : (ExpandedVertex G)) :
    (cubicExpansion G R).edgeAt h 2 = Sum.inr (R.next.symm h) := rfl

noncomputable def projectEvenDoubleCover {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V]
    (G : FiniteGraph V E) (R : (RotationSystem G))
    (C : CubicGraph.IndexedEvenDoubleCover (cubicExpansion G R)) :
    (IndexedEvenDoubleCover G) := by
  have vertexEven (s : Gamma) (v : V) :
      ∑ e : E,
        ((if G.endAt e 0 = v then C.member s (Sum.inl e) else 0) +
         (if G.endAt e 1 = v then C.member s (Sum.inl e) else 0)) = 0 := by
    let spoke : (ExpandedVertex G) → F₂ := fun h ↦
      if (vertex G) h = v then C.member s (Sum.inl h.1) else 0
    let ring : (ExpandedVertex G) → F₂ := fun h ↦
      if (vertex G) h = v then C.member s (Sum.inr h) else 0
    let previousRing : (ExpandedVertex G) → F₂ := fun h ↦
      if (vertex G) h = v then C.member s (Sum.inr (R.next.symm h)) else 0
    have hlocal (h : (ExpandedVertex G)) :
        C.member s (Sum.inl h.1) + C.member s (Sum.inr h) +
          C.member s (Sum.inr (R.next.symm h)) = 0 := by
      simpa [Fin.sum_univ_three] using C.vertexEven s h
    have htotal :
        (∑ h : (ExpandedVertex G), (spoke h + ring h + previousRing h)) = 0 := by
      apply Finset.sum_eq_zero
      intro h _
      by_cases hv : (vertex G) h = v
      · simpa [spoke, ring, previousRing, hv] using hlocal h
      · simp [spoke, ring, previousRing, hv]
    have hring : (∑ h : (ExpandedVertex G), previousRing h) = ∑ h, ring h := by
      let f : (ExpandedVertex G) → F₂ := fun h ↦
        if (vertex G) h = v then C.member s (Sum.inr h) else 0
      have hpoint (h : (ExpandedVertex G)) : previousRing h = f (R.next.symm h) := by
        have hn : (vertex G) (R.next.symm h) = (vertex G) h := by
          have hx := R.sameVertex (R.next.symm h)
          simpa using hx.symm
        simp only [previousRing, f]
        rw [hn]
      simp_rw [hpoint]
      exact R.next.symm.sum_comp f
    have hspoke : (∑ h : (ExpandedVertex G), spoke h) = 0 := by
      rw [Finset.sum_add_distrib, Finset.sum_add_distrib, hring] at htotal
      ring_nf at htotal
      have htwo : (2 : F₂) = 0 := by decide
      rw [htwo, mul_zero, add_zero] at htotal
      exact htotal
    calc
      _ = ∑ e : E, ∑ j : Fin 2,
          if G.endAt e j = v then C.member s (Sum.inl e) else 0 := by
        apply Finset.sum_congr rfl
        intro e _
        rw [Fin.sum_univ_two]
      _ = ∑ h : (ExpandedVertex G), spoke h := by
        rw [← Fintype.sum_prod_type']
        rfl
      _ = 0 := hspoke
  exact
    { member := fun s e ↦ C.member s (Sum.inl e)
      vertexEven := vertexEven
      coveredTwice := fun e ↦ C.coveredTwice (Sum.inl e) }

def supportGraph {V E : Type*} [Fintype V] [Fintype E] (G : FiniteGraph V E) (S : Finset E) :
    SimpleGraph V :=
  SimpleGraph.fromRel fun u v ↦
    ∃ e ∈ S, G.endAt e 0 = u ∧ G.endAt e 1 = v

def ReachableIn {V E : Type*} [Fintype V] [Fintype E] (G : FiniteGraph V E) (S : Finset E) (u v : V)
    : Prop :=
  ((supportGraph G) S).Reachable u v

def Connects {V E : Type*} [Fintype V] [Fintype E] (G : FiniteGraph V E) (S : Finset E) : Prop :=
  ((supportGraph G) S).Connected

def IsSpanningTree {V E : Type*} [Fintype V] [Fintype E] (G : FiniteGraph V E) (S : Finset E) : Prop
    :=
  (Connects G) S ∧ S.card + 1 = Fintype.card V

def HasTreePacking {V E : Type*} [Fintype V] [Fintype E] (G : FiniteGraph V E) (k : ℕ) : Prop :=
  ∃ T : Fin k → Finset E,
    (∀ i, (IsSpanningTree G) (T i)) ∧
      ∀ i j, i ≠ j → Disjoint (T i) (T j)

noncomputable def crossingEdges {V E : Type*} [Fintype V] [Fintype E] (G : FiniteGraph V E)
    (P : Setoid V) : Finset E := by
  classical
  exact Finset.univ.filter fun e ↦ ¬ P.r (G.endAt e 0) (G.endAt e 1)

noncomputable def crossingClass {V E : Type*} [Fintype V] [Fintype E] (G : FiniteGraph V E)
    (S : Finset E) (P : Setoid V) : Finset E := by
  classical
  exact S.filter fun e ↦ ¬ P.r (G.endAt e 0) (G.endAt e 1)

@[simp]
lemma mem_crossingClass {V E : Type*} [Fintype V] [Fintype E] (G : FiniteGraph V E) {S : Finset E}
    {P : Setoid V} {e : E} :
    e ∈ (crossingClass G) S P ↔
      e ∈ S ∧ ¬ P.r (G.endAt e 0) (G.endAt e 1) := by simp[crossingClass]

noncomputable instance quotientFintype {V : Type*} [Fintype V]
    (P : Setoid V) : Fintype (Quotient P) :=
  Fintype.ofFinite _

noncomputable def quotientGraph {V E : Type*} [Fintype V] [Fintype E] (G : FiniteGraph V E)
    (S : Finset E) (P : Setoid V) :
    FiniteGraph (Quotient P) {e : E // e ∈ (crossingClass G) S P} where
  endAt e i := Quotient.mk _ (G.endAt e.1 i)
  loopless e := by
    intro h
    have hrel : P.r (G.endAt e.1 0) (G.endAt e.1 1) := Quotient.eq'.mp h
    exact ((mem_crossingClass (G := G)).mp e.2).2 hrel

def SatisfiesTreePackingCondition {V E : Type*} [Fintype V] [Fintype E] (G : FiniteGraph V E)
    (k : ℕ) : Prop :=
  ∀ P : Setoid V,
    k * (Nat.card (Quotient P) - 1) ≤ (crossingEdges (G := G) P).card

def componentSetoid {V E : Type*} [Fintype V] [Fintype E] (G : FiniteGraph V E) (S : Finset E) :
    Setoid V :=
  ((supportGraph G) S).reachableSetoid

noncomputable def insideEdges {V E : Type*} [Fintype V] [Fintype E] (G : FiniteGraph V E)
    (S : Finset E) (P : Setoid V) (u : V) : Finset E := by
  classical
  exact S.filter fun e ↦ P.r (G.endAt e 0) u ∧ P.r (G.endAt e 1) u

@[simp]
lemma mem_insideEdges {V E : Type*} [Fintype V] [Fintype E] (G : FiniteGraph V E) {S : Finset E}
    {P : Setoid V} {u : V} {e : E} :
    e ∈ (insideEdges G) S P u ↔
      e ∈ S ∧ P.r (G.endAt e 0) u ∧ P.r (G.endAt e 1) u := by simp[insideEdges]

lemma insideEdges_eq_of_rel {V E : Type*} [Fintype V] [Fintype E] (G : FiniteGraph V E)
    {S : Finset E} {P : Setoid V} {u v : V}
    (huv : P.r u v) : (insideEdges G) S P u = (insideEdges G) S P v := by
  have h (x) : P.r x u ↔ P.r x v :=
    ⟨(P.trans · huv), (P.trans · (P.symm huv))⟩
  ext e
  simp [insideEdges, h]

lemma insideEdges_erase {V E : Type*} [Fintype V] [Fintype E] [DecidableEq E] (G : FiniteGraph V E)
    (S : Finset E) (P : Setoid V) (u : V) (e : E) :
    (insideEdges G) (S.erase e) P u = ((insideEdges G) S P u).erase e := by
  ext x
  simp [insideEdges]
  tauto

noncomputable def refineSetoid {V E : Type*} [Fintype V] [Fintype E] (G : FiniteGraph V E)
    (P : Setoid V) (S : Finset E) : Setoid V where
  r u v := P.r u v ∧ (ReachableIn G) ((insideEdges G) S P u) u v
  iseqv := by
    constructor
    · intro u
      exact ⟨P.refl u, SimpleGraph.Reachable.refl u⟩
    · intro u v huv
      refine ⟨P.symm huv.1, ?_⟩
      rw [← (insideEdges_eq_of_rel G) huv.1]
      exact huv.2.symm
    · intro u v w huv hvw
      refine ⟨P.trans huv.1 hvw.1, ?_⟩
      have hEq : (insideEdges G) S P u = (insideEdges G) S P v :=
        insideEdges_eq_of_rel G huv.1
      exact huv.2.trans (hEq ▸ hvw.2)

noncomputable def colorClass {E : Type*} [Fintype E] {k : ℕ} (χ : E → Fin k) (i : Fin k) :
    Finset E := by
  classical
  exact Finset.univ.filter fun e ↦ χ e = i

@[simp]
lemma mem_colorClass {E : Type*} [Fintype E] {k : ℕ} {χ : E → Fin k} {i : Fin k} {e : E} :
    e ∈ colorClass χ i ↔ χ e = i := by simp[colorClass]

lemma colorClass_disjoint {E : Type*} [Fintype E] {k : ℕ} (χ : E → Fin k) {i j : Fin k}
    (hij : i ≠ j) :
    Disjoint (colorClass χ i) (colorClass χ j) := by
  simp_all [Finset.disjoint_left]

def PrefixTrees {V E : Type*} [Fintype V] [Fintype E] (G : FiniteGraph V E) {k : ℕ}
    (χ : E → Fin (k + 1)) : Prop :=
  ∀ i : Fin k, (IsSpanningTree G) (colorClass χ i.castSucc)

noncomputable def residualClass {E : Type*} [Fintype E] {k : ℕ} (χ : E → Fin (k + 1)) :
    Finset E :=
  colorClass χ (Fin.last k)

noncomputable def residualComponents {V E : Type*} [Fintype V] [Fintype E] (G : FiniteGraph V E)
    {k : ℕ} (χ : E → Fin (k + 1)) : ℕ :=
  Nat.card ((supportGraph G) (residualClass χ)).ConnectedComponent

def InternallyConnected {V E : Type*} [Fintype V] [Fintype E] (G : FiniteGraph V E) (S : Finset E)
    (P : Setoid V) : Prop :=
  ∀ u v : V, P.r u v → (ReachableIn G) ((insideEdges G) S P u) u v

def NeedsRefinement {V E : Type*} [Fintype V] [Fintype E] (G : FiniteGraph V E) {k : ℕ}
    (χ : E → Fin k) (P : Setoid V) : Prop :=
  ∃ i : Fin k, ¬ (InternallyConnected G) (colorClass χ i) P

noncomputable def firstDisconnectedColor {V E : Type*} [Fintype V] [Fintype E] (G : FiniteGraph V E)
    {k : ℕ} (χ : E → Fin k) (P : Setoid V) :
    Option (Fin k) := by
  classical
  exact if h : (NeedsRefinement G) χ P then
    some ((Finset.univ.filter fun i : Fin k ↦
      ¬ (InternallyConnected G) (colorClass χ i) P).min'
      (by
        rcases h with ⟨i, hi⟩
        exact ⟨i, by simp [hi]⟩))
  else none

lemma firstDisconnectedColor_eq_none_iff {V E : Type*} [Fintype V] [Fintype E] (G : FiniteGraph V E)
    {k : ℕ} (χ : E → Fin k) (P : Setoid V) :
    (firstDisconnectedColor G) χ P = none ↔ ¬ (NeedsRefinement G) χ P := by
  simp [firstDisconnectedColor]

lemma firstDisconnectedColor_spec {V E : Type*} [Fintype V] [Fintype E] (G : FiniteGraph V E)
    {k : ℕ} {χ : E → Fin k} {P : Setoid V}
    {i : Fin k} (h : (firstDisconnectedColor G) χ P = some i) :
    ¬ (InternallyConnected G) (colorClass χ i) P := by
  classical
  unfold firstDisconnectedColor at h
  split at h
  · rename_i hneed
    injection h with hmin
    subst i
    simpa using Finset.min'_mem (Finset.univ.filter fun i : Fin k ↦
      ¬ (InternallyConnected G) (colorClass χ i) P) _
  · cases h

lemma internallyConnected_iff_of_refineSetoid_eq {V E : Type*} [Fintype V] [Fintype E]
    (G : FiniteGraph V E)
    {S T : Finset E} {P : Setoid V}
    (hEq : (refineSetoid G) P S = (refineSetoid G) P T) :
    (InternallyConnected G) S P ↔ (InternallyConnected G) T P := by
  constructor<;>intro h u v huv
  all_goals have q := congrArg (fun Q : Setoid V ↦ Q.r u v) hEq
  · exact (q.mp ⟨huv,h u v huv⟩).2
  · exact (Eq.mp q.symm ⟨huv,h u v huv⟩).2

lemma firstDisconnectedColor_internal_of_lt {V E : Type*} [Fintype V] [Fintype E]
    (G : FiniteGraph V E) {k : ℕ}
    {χ : E → Fin k} {P : Setoid V} {c d : Fin k}
    (hc : (firstDisconnectedColor G) χ P = some c)
    (hdc : d < c) :
    (InternallyConnected G) (colorClass χ d) P := by
  classical
  unfold firstDisconnectedColor at hc
  split at hc
  · rename_i hneed
    injection hc with hmin
    by_contra hd
    have hdmem : d ∈ Finset.univ.filter fun i : Fin k ↦
        ¬ (InternallyConnected G) (colorClass χ i) P := by
      simp [hd]
    have hle : c ≤ d := by
      rw [← hmin]
      exact Finset.min'_le _ d hdmem
    exact (not_le_of_gt hdc) hle
  · cases hc

lemma firstDisconnectedColor_eq_some_of_spec {V E : Type*} [Fintype V] [Fintype E]
    (G : FiniteGraph V E) {k : ℕ}
    {χ : E → Fin k} {P : Setoid V} {c : Fin k}
    (hbad : ¬ (InternallyConnected G) (colorClass χ c) P)
    (hbefore : ∀ d : Fin k, d < c →
      (InternallyConnected G) (colorClass χ d) P) :
    (firstDisconnectedColor G) χ P = some c := by
  classical
  unfold firstDisconnectedColor
  let badSet := Finset.univ.filter fun i : Fin k ↦
    ¬ (InternallyConnected G) (colorClass χ i) P
  have hneed : (NeedsRefinement G) χ P := ⟨c, hbad⟩
  have hc_mem : c ∈ badSet := by
    simp [badSet, hbad]
  rw [dif_pos hneed]
  change some (badSet.min' _) = some c
  congr
  apply le_antisymm
  · exact Finset.min'_le badSet c hc_mem
  · apply Finset.le_min'
    intro d hd
    have hd' : ¬ (InternallyConnected G) (colorClass χ d) P := by
      simpa [badSet] using hd
    exact le_of_not_gt fun h ↦ hd' (hbefore d h)

noncomputable def refineOnce {V E : Type*} [Fintype V] [Fintype E] (G : FiniteGraph V E) {k : ℕ}
    (χ : E → Fin k) (P : Setoid V) : Setoid V :=
  match (firstDisconnectedColor G) χ P with
  | none => P
  | some i => (refineSetoid G) P (colorClass χ i)

noncomputable def kaiserPartition {V E : Type*} [Fintype V] [Fintype E] (G : FiniteGraph V E)
    {k : ℕ} (χ : E → Fin k) : ℕ → Setoid V
  | 0 => ⊤
  | n + 1 => (refineOnce G) χ (kaiserPartition G χ n)

lemma kaiserPartition_refines_of_le {V E : Type*} [Fintype V] [Fintype E] (G : FiniteGraph V E)
    {k : ℕ} (χ : E → Fin k)
    {m n : ℕ} (hmn : m ≤ n) {u v : V}
    (h : ((kaiserPartition G) χ n).r u v) :
    ((kaiserPartition G) χ m).r u v := by
  induction hmn with
  | refl=>exact h
  | step hmn ih=>
    apply ih
    rw[kaiserPartition]at h
    unfold refineOnce at h
    generalize (firstDisconnectedColor G) χ ((kaiserPartition G) χ _) = q at h
    cases q with
    | none=>exact h
    | some i=>exact h.1

def HasFiniteLevel {V E : Type*} [Fintype V] [Fintype E] (G : FiniteGraph V E) {k : ℕ}
    (χ : E → Fin k) (e : E) (m : ℕ) : Prop :=
  ((kaiserPartition G) χ m).r (G.endAt e 0) (G.endAt e 1) ∧
    ¬ ((kaiserPartition G) χ (m + 1)).r (G.endAt e 0) (G.endAt e 1)

lemma exists_finiteLevel_of_not_rel {V E : Type*} [Fintype V] [Fintype E] (G : FiniteGraph V E)
    {k : ℕ} {χ : E → Fin k} {e : E} {n : ℕ}
    (hnot : ¬ ((kaiserPartition G) χ n).r (G.endAt e 0) (G.endAt e 1)) :
    ∃ m : ℕ, (HasFiniteLevel G) χ e m := by
  induction n with
  | zero => exact (hnot trivial).elim
  | succ n ih =>
    by_cases h : ((kaiserPartition G) χ n).r (G.endAt e 0) (G.endAt e 1)
    · exact ⟨n, h, hnot⟩
    · exact ih h

def IsCyclicEdge {V E : Type*} [Fintype V] [Fintype E] [DecidableEq E] (G : FiniteGraph V E)
    (S : Finset E) (e : E) : Prop :=
  e ∈ S ∧ (ReachableIn G) (S.erase e) (G.endAt e 0) (G.endAt e 1)

def IsSuperfluousAt {V E : Type*} [Fintype V] [Fintype E] [DecidableEq E] (G : FiniteGraph V E)
    {k : ℕ} (χ : E → Fin (k + 1)) (e : E) (m : ℕ) : Prop :=
  (IsCyclicEdge G) (residualClass χ) e ∧ (HasFiniteLevel G) χ e m

def HasSuperfluousEdge {V E : Type*} [Fintype V] [Fintype E] [DecidableEq E] (G : FiniteGraph V E)
    {k : ℕ} (χ : E → Fin (k + 1)) : Prop :=
  ∃ e m, (IsSuperfluousAt G) χ e m

lemma insideEdges_top {V E : Type*} [Fintype V] [Fintype E] (G : FiniteGraph V E) (S : Finset E)
    (u : V) :
    (insideEdges G) S ⊤ u = S := by
  aesop

noncomputable def swapColor {E : Type*} [DecidableEq E] {k : ℕ} (χ : E → Fin k) (e e' : E) :
    E → Fin k :=
  Function.update (Function.update χ e (χ e')) e' (χ e)

lemma colorClass_swap_right {E : Type*} [Fintype E] [DecidableEq E] {k : ℕ} (χ : E → Fin k)
    {e e' : E}
    (hee' : e ≠ e') (hcol : χ e ≠ χ e') :
    colorClass (swapColor χ e e') (χ e') =
      (colorClass χ (χ e')).erase e' ∪ {e} := by
  ext x
  simp [swapColor, Function.update_apply]
  aesop

lemma colorClass_swap_other {E : Type*} [Fintype E] [DecidableEq E] {k : ℕ} (χ : E → Fin k)
    {e e' : E} {i : Fin k}
    (hee' : e ≠ e') (hi : i ≠ χ e) (hi' : i ≠ χ e') :
    colorClass (swapColor χ e e') i = colorClass χ i := by
  ext x
  simp [swapColor, Function.update]
  aesop

lemma supportGraph_adj_iff {V E : Type*} [Fintype V] [Fintype E] (G : FiniteGraph V E)
    (S : Finset E) (u v : V) :
    ((supportGraph G) S).Adj u v ↔
      u ≠ v ∧ ∃ e ∈ S,
        (G.endAt e 0 = u ∧ G.endAt e 1 = v) ∨
          (G.endAt e 0 = v ∧ G.endAt e 1 = u) := by
    simp [supportGraph]
    aesop

def symEdge {V E : Type*} [Fintype V] [Fintype E] (G : FiniteGraph V E) (e : E) : Sym2 V :=
    s(G.endAt e 0, G.endAt e 1)

lemma edgeFinset_supportGraph {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V]
    (G : FiniteGraph V E) (S : Finset E)
    [Fintype ((supportGraph G) S).edgeSet] :
    ((supportGraph G) S).edgeFinset = S.image (symEdge G) := by
  ext e
  refine Sym2.inductionOn e ?_
  intro u v
  have hloop :
      ∀ x ∈ S,
        ((G.endAt x 0 = u ∧ G.endAt x 1 = v) ∨
          (G.endAt x 0 = v ∧ G.endAt x 1 = u)) →
          u ≠ v := by
    intro x _ h huv
    rcases h with h | h
    · exact G.loopless x (h.1.trans (huv.trans h.2.symm))
    · exact G.loopless x (h.1.trans (huv.symm.trans h.2.symm))
  simpa [symEdge, supportGraph_adj_iff] using hloop

lemma reachableIn_mono {V E : Type*} [Fintype V] [Fintype E] (G : FiniteGraph V E) {S T : Finset E}
    (hST : S ⊆ T) {u v : V}
    (h : (ReachableIn G) S u v) : (ReachableIn G) T u v := by
  apply h.mono
  intro x y a
  rw [supportGraph_adj_iff] at a ⊢
  aesop

lemma reachable_of_adj_reachable {V : Type*} {H K : SimpleGraph V}
    (hstep : ∀ {u v : V}, H.Adj u v → K.Reachable u v) {u v : V}
    (h : H.Reachable u v) : K.Reachable u v := by
  rcases h with ⟨p⟩
  induction p with
  | nil => exact ⟨.nil⟩
  | cons h p ih => exact (hstep h).trans ih

lemma reachable_map_of_adj_reachable {V : Type*} {W : Type*} {H : SimpleGraph V}
    {K : SimpleGraph W} (f : V → W)
    (hstep : ∀ {u v : V}, H.Adj u v → K.Reachable (f u) (f v))
    {u v : V} (h : H.Reachable u v) : K.Reachable (f u) (f v) := by
  rcases h with ⟨p⟩
  induction p with
  | nil=>exact ⟨.nil⟩
  | cons a p ih=>exact (hstep a).trans ih

lemma quotientGraph_connected_of_connects {V E : Type*} [Fintype V] [Fintype E]
    (G : FiniteGraph V E) [Nonempty V] (S : Finset E) (P : Setoid V)
    (hS : (Connects G) S) :
    (Connects ((quotientGraph G) S P)) Finset.univ := by
  rw[Connects,SimpleGraph.connected_iff]at hS ⊢
  constructor
  · intro q r
    refine Quotient.inductionOn₂ q r fun u v↦?_
    have hstep{x y:V}(hxy:((supportGraph G) S).Adj x y):
        ((supportGraph ((quotientGraph G) S P)) Finset.univ).Reachable ⟦x⟧ ⟦y⟧:=by
      by_cases h:P.r x y
      · have e:Quotient.mk P x=Quotient.mk P y:=Quotient.eq'.2 h
        rw[e]
      · apply SimpleGraph.Adj.reachable
        rw[supportGraph_adj_iff]
        refine ⟨fun e↦h (Quotient.eq'.1 e),?_⟩
        rw[supportGraph_adj_iff]at hxy
        rcases hxy with ⟨_,e,he,hh⟩
        refine ⟨⟨e,((mem_crossingClass G)).2 ⟨he,?_⟩⟩,by simp,?_⟩
        · rcases hh with h0|h0
          · simpa[h0.1,h0.2]using h
          · simpa[h0.1,h0.2]using fun z↦h (P.symm z)
        · rcases hh with h0|h0
          · exact .inl ⟨congrArg _ h0.1,congrArg _ h0.2⟩
          · exact .inr ⟨congrArg _ h0.1,congrArg _ h0.2⟩
    rcases hS.1 u v with⟨p⟩
    induction p with
    | nil=>exact ⟨.nil⟩
    | cons h p ih=>exact (hstep h).trans ih
  · exact Nonempty.map (Quotient.mk P) hS.2

lemma insideEdges_subset_erase_of_crossing {V E : Type*} [Fintype V] [Fintype E] [DecidableEq E]
    (G : FiniteGraph V E) {S : Finset E} {P : Setoid V} {e : E}
    (he : e ∈ (crossingClass G) S P) (u : V) :
    (insideEdges G) S P u ⊆ S.erase e := by
  intro f hf
  simp only [mem_insideEdges,mem_crossingClass,Finset.mem_erase] at *
  exact ⟨fun h=>he.2 <| h ▸ P.trans hf.2.1 (P.symm hf.2.2),hf.1⟩

lemma reachableIn_erase_of_cyclic {V E : Type*} [Fintype V] [Fintype E] [DecidableEq E]
    (G : FiniteGraph V E) {S : Finset E} {e : E}
    (he : (IsCyclicEdge G) S e) {u v : V}
    (h : (ReachableIn G) S u v) : (ReachableIn G) (S.erase e) u v := by
  apply reachable_of_adj_reachable ?_ h
  intro x y hxy
  rw [(supportGraph_adj_iff G)] at hxy
  rcases hxy with ⟨hxy,k,hk,hkxy⟩
  by_cases hke : k = e
  · subst k
    rcases hkxy with hkxy | hkxy
    · simpa [ReachableIn, hkxy.1, hkxy.2] using he.2
    · simpa [ReachableIn, hkxy.1, hkxy.2] using he.2.symm
  · apply SimpleGraph.Adj.reachable
    rw [(supportGraph_adj_iff G)]
    exact ⟨hxy,k,Finset.mem_erase.mpr ⟨hke,hk⟩,hkxy⟩

lemma exists_isSpanningTree_subset_of_connects {V E : Type*} [Fintype V] [Fintype E]
    (G : FiniteGraph V E) [Nonempty V] (S : Finset E)
    (hS : (Connects G) S) :
    ∃ T : Finset E, T ⊆ S ∧ (IsSpanningTree G) T := by
  classical
  obtain ⟨K,hKH,hK⟩ := hS.exists_isTree_le
  let A := {x // x ∈ K.edgeFinset}
  have hsub (x : Sym2 V) : x ∈ K.edgeFinset →
      x ∈ ((supportGraph G) S).edgeFinset := by
    refine Sym2.inductionOn x ?_
    intro u v hx
    simpa using hKH (by simpa using hx)
  have hx (x : A) : ∃ e ∈ S, (symEdge G) e = x.1 := by
    rcases x with ⟨x,hx⟩
    have h := hsub x hx
    rw [(edgeFinset_supportGraph G) S] at h
    simpa using h
  let f : A → E := fun x ↦ (hx x).choose
  have hfS (x : A) : f x ∈ S := (hx x).choose_spec.1
  have hfs (x : A) : (symEdge G) (f x) = x.1 := (hx x).choose_spec.2
  have hfi : Function.Injective f := by
    intro x y h
    apply Subtype.ext
    rw [← hfs x, ← hfs y, h]
  let T := Finset.univ.image f
  have hi : T.image (symEdge G) = K.edgeFinset := by
    ext x
    simp only [T, Finset.mem_image, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨_,⟨a,rfl⟩,rfl⟩
      simp [hfs a]
    · intro hxK
      refine ⟨f ⟨x,hxK⟩,⟨⟨x,hxK⟩,rfl⟩,?_⟩
      exact hfs _
  have hGT : (supportGraph G) T = K := by
    have he : ((supportGraph G) T).edgeFinset = K.edgeFinset := by
      rw [(edgeFinset_supportGraph G) T, hi]
    ext u v
    have := congrArg (fun F : Finset (Sym2 V) ↦ s(u,v) ∈ F) he
    simpa using this
  refine ⟨T,?_,?_,?_⟩
  · change Finset.univ.image f ⊆ S
    exact Finset.image_subset_iff.mpr fun x _ ↦ hfS x
  · rw [Connects,hGT]
    exact hK.1
  · change (Finset.univ.image f).card + 1 = _
    rw [Finset.card_image_iff.mpr]
    · simpa [A] using hK.card_edgeFinset
    · intro x _ y _ h
      exact hfi h

lemma reachableIn_inside_of_walk_of_no_crossing {V E : Type*} [Fintype V] [Fintype E]
    (G : FiniteGraph V E)
    {T : Finset E} {P : Setoid V} {a u v : V}
    (p : ((supportGraph G) T).Walk u v) (hua : P.r u a)
    (hno : ∀ f ∈ T, (symEdge G) f ∈ p.edges →
      P.r (G.endAt f 0) (G.endAt f 1)) :
    (ReachableIn G) ((insideEdges G) T P a) u v := by
  induction p generalizing a with
  | nil => exact .refl _
  | @cons x y z h p ih =>
    have hh := h
    rw [(supportGraph_adj_iff G)] at hh
    rcases hh with ⟨hne, f, hf, hfend⟩
    have hedge : (symEdge G) f ∈ (SimpleGraph.Walk.cons h p).edges := by
      rcases hfend with hfend | hfend <;> simp [symEdge, hfend]
    have hrel := hno f hf hedge
    have hwa : P.r y a := by
      rcases hfend with hfend | hfend
      · have hx : P.r (G.endAt f 0) a := by simpa only [hfend.1] using hua
        simpa only [hfend.2] using P.trans (P.symm hrel) hx
      · have hx : P.r (G.endAt f 1) a := by simpa only [hfend.2] using hua
        simpa only [hfend.1] using P.trans hrel hx
    apply (SimpleGraph.Adj.reachable ?_).trans (ih hwa ?_)
    · rw [(supportGraph_adj_iff G)]
      refine ⟨hne, f, ?_, hfend⟩
      simp only [mem_insideEdges, hf, true_and]
      rcases hfend with hfend | hfend <;> simp_all
    · intro e he hep
      exact hno e he (by simp [hep])

lemma exists_crossing_tree_edge_of_not_internal_reachable {V E : Type*} [Fintype V] [Fintype E]
    (G : FiniteGraph V E)
    {T : Finset E} {P : Setoid V} {u v : V}
    (p : ((supportGraph G) T).Walk u v)
    (hnot : ¬ (ReachableIn G) ((insideEdges G) T P u) u v) :
    ∃ f ∈ T, (symEdge G) f ∈ p.edges ∧
      ¬ P.r (G.endAt f 0) (G.endAt f 1) := by
  classical
  by_contra h
  push Not at h
  exact hnot ((reachableIn_inside_of_walk_of_no_crossing G) p (P.refl u) h)

lemma reachableIn_inside_exchange_of_path_edge_of_new_support {V E : Type*} [Fintype V] [Fintype E]
    [DecidableEq E] (G : FiniteGraph V E)
    {T : Finset E} {P : Setoid V} {u : V} {e e' : E}
    (p : ((supportGraph G) T).Path (G.endAt e 0) (G.endAt e 1))
    (he'path : (symEdge G) e' ∈ p.1.edges)
    (he0 : P.r (G.endAt e 0) u) (he1 : P.r (G.endAt e 1) u)
    (hpath : ∀ f ∈ T, (symEdge G) f ∈ p.1.edges →
      P.r (G.endAt f 0) u ∧ P.r (G.endAt f 1) u) :
    (ReachableIn G)
      ((insideEdges G) (T.erase e' ∪ {e}) P u)
      (G.endAt e' 0) (G.endAt e' 1) := by
  let U := (insideEdges G) (T.erase e' ∪ {e}) P u
  let H := (supportGraph G) U
  have step {x y : V} (h : ((supportGraph G) T).Adj x y)
      (hm : s(x,y) ∈ p.1.edges) (hne : s(x,y) ≠ (symEdge G) e') :
      H.Reachable x y := by
    rw [(supportGraph_adj_iff G)] at h
    rcases h with ⟨hxy,f,hf,hend⟩
    have hfp : (symEdge G) f ∈ p.1.edges := by
      rcases hend with h | h
      · simpa [symEdge, h.1, h.2] using hm
      · simpa only [symEdge, h.1, h.2, Sym2.eq_swap] using hm
    have hfe : f ≠ e' := by
      intro rfl
      apply hne
      rcases hend with h | h <;> simp [symEdge, h.1, h.2]
    apply SimpleGraph.Adj.reachable
    rw [(supportGraph_adj_iff G)]
    exact ⟨hxy,f,by simp [U,mem_insideEdges,hfe,hf,hpath f hf hfp],hend⟩
  have map_walk : ∀ {x y : V} (q : ((supportGraph G) T).Walk x y),
      (∀ d ∈ q.edges, d ∈ p.1.edges) → (symEdge G) e' ∉ q.edges →
      H.Reachable x y := by
    intro x y q hsub hnot
    induction q with
    | nil => exact .refl _
    | @cons x z y h q ih =>
      have hh : s(x,z) ∈ p.1.edges := hsub _ (by simp)
      have hn : s(x,z) ≠ (symEdge G) e' := by
        intro heq
        exact hnot (by simp [heq])
      apply (step h hh hn).trans
      apply ih
      · intro d hd
        exact hsub d (by simp [hd])
      · intro hd
        exact hnot (by simp [hd])
  have orient {x y : V} (h : (symEdge G) e' = s(x,y))
      (hr : H.Reachable x y) : H.Reachable (G.endAt e' 0) (G.endAt e' 1) := by
    simp only [symEdge, Sym2.eq_iff] at h
    rcases h with h | h
    · simpa [h.1,h.2] using hr
    · simpa [h.1,h.2] using hr.symm
  have exchange : ∀ {x y : V} (q : ((supportGraph G) T).Walk x y),
      q.IsTrail → (∀ d ∈ q.edges, d ∈ p.1.edges) →
      (symEdge G) e' ∈ q.edges → H.Reachable x y →
      H.Reachable (G.endAt e' 0) (G.endAt e' 1) := by
    intro x y q ht hsub hm hr
    induction q with
    | nil => simp at hm
    | @cons x z y h q ih =>
      simp only [SimpleGraph.Walk.isTrail_cons] at ht
      rcases ht with ⟨ht,hn⟩
      simp only [SimpleGraph.Walk.edges_cons, List.mem_cons] at hm
      have hsubq : ∀ d ∈ q.edges, d ∈ p.1.edges := by
        intro d hd
        exact hsub d (by simp [hd])
      rcases hm with heq | hm
      · apply orient heq
        exact hr.trans (map_walk q hsubq (heq ▸ hn)).symm
      · apply ih ht hsubq hm
        have hne : s(x,z) ≠ (symEdge G) e' := fun heq ↦ hn (heq ▸ hm)
        exact (step h (hsub _ (by simp)) hne).symm.trans hr
  apply exchange p.1 p.2.isTrail (fun _ h ↦ h) he'path
  apply SimpleGraph.Adj.reachable
  rw [(supportGraph_adj_iff G)]
  exact ⟨G.loopless e,e,by simp [U,mem_insideEdges,he0,he1],.inl ⟨rfl,rfl⟩⟩

lemma reachableIn_inside_exchange_of_path_edge {V E : Type*} [Fintype V] [Fintype E]
    [DecidableEq E] (G : FiniteGraph V E) [Nonempty V]
    {T : Finset E} {P : Setoid V} {u : V} {e e' : E}
    (hT : (IsSpanningTree G) T)
    (p : ((supportGraph G) T).Path (G.endAt e 0) (G.endAt e 1))
    (he'path : (symEdge G) e' ∈ p.1.edges)
    (he0 : P.r (G.endAt e 0) u) (he1 : P.r (G.endAt e 1) u)
    (hpath : ∀ f ∈ T, (symEdge G) f ∈ p.1.edges →
      P.r (G.endAt f 0) u ∧ P.r (G.endAt f 1) u) :
    (ReachableIn G)
      ((insideEdges G) (T.erase e' ∪ {e}) P u)
      (G.endAt e' 0) (G.endAt e' 1) := by
  exact (fun _ : (IsSpanningTree G) T ↦
    (reachableIn_inside_exchange_of_path_edge_of_new_support G)
      p he'path he0 he1 hpath) hT

lemma cyclicEdge_of_mem_path_of_cyclic_edge {V E : Type*} [Fintype V] [Fintype E]
    [DecidableEq E] (G : FiniteGraph V E)
    {S : Finset E} {e f : E}
    (heCyc : (IsCyclicEdge G) S e)
    (p : ((supportGraph G) (S.erase e)).Path
      (G.endAt e 0) (G.endAt e 1))
    (hf : f ∈ S.erase e)
    (hfpath : (symEdge G) f ∈ p.1.edges) :
    (IsCyclicEdge G) S f := by
  refine ⟨Finset.mem_of_mem_erase hf, ?_⟩
  have h := reachableIn_inside_exchange_of_path_edge_of_new_support (G := G)
    (P := ⊤) (u := G.endAt e 0) p hfpath trivial trivial
    (fun _ _ _ ↦ ⟨trivial, trivial⟩)
  rw [(insideEdges_top G)] at h
  apply (reachableIn_mono G) ?_ h
  intro x hx
  simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_singleton] at hx ⊢
  rcases hx with ⟨hxf, hxe, hxS⟩ | rfl
  · exact ⟨hxf, hxS⟩
  · exact ⟨by rintro rfl; exact (Finset.mem_erase.mp hf).1 rfl, heCyc.1⟩

lemma reachableIn_inside_erase_of_min_superfluous {V E : Type*} [Fintype V] [Fintype E]
    [DecidableEq E] (G : FiniteGraph V E) [Nonempty V] {k : ℕ}
    {χ : E → Fin (k + 1)} {e : E} {m t : ℕ} {u v : V}
    (hsuper : (IsSuperfluousAt G) χ e m)
    (hmin : ∀ f n, (IsSuperfluousAt G) χ f n → m ≤ n)
    (htm : t < m)
    (h : (ReachableIn G)
      ((insideEdges G) (residualClass χ) ((kaiserPartition G) χ t) u) u v) :
    (ReachableIn G)
      ((insideEdges G) ((residualClass χ).erase e)
        ((kaiserPartition G) χ t) u) u v := by
  classical
  rw [(insideEdges_erase G)]
  let R := residualClass χ
  let P := (kaiserPartition G) χ t
  by_cases he : e ∈ (insideEdges G) R P u
  · apply (reachableIn_erase_of_cyclic G) ⟨he, ?_⟩ h
    rw [← (insideEdges_erase G)]
    obtain ⟨w⟩ := hsuper.1.2
    let p := w.toPath
    apply (reachableIn_inside_of_walk_of_no_crossing G) p.1
      (((mem_insideEdges G).mp) he).2.1
    intro f hf hfp
    by_contra hrel
    obtain ⟨n, hn⟩ := (exists_finiteLevel_of_not_rel G) hrel
    have hnt : n < t := by
      by_contra htn
      exact hrel ((kaiserPartition_refines_of_le G) χ (Nat.le_of_not_gt htn) hn.1)
    have hcyc : (IsCyclicEdge G) R f := by
      refine ⟨(Finset.mem_erase.mp hf).2, ?_⟩
      let z : V := Classical.choice inferInstance
      have hx := reachableIn_inside_exchange_of_path_edge_of_new_support (G := G)
        (P := (⊤ : Setoid V)) (u := z) (e := e) (e' := f)
        p hfp trivial trivial (fun _ _ _ ↦ ⟨trivial, trivial⟩)
      rw [(insideEdges_top G)] at hx
      apply (reachableIn_mono G) ?_ hx
      intro g hg
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_singleton] at hg ⊢
      rcases hg with ⟨hgf, _, hgR⟩ | rfl
      · exact ⟨hgf, hgR⟩
      · exact ⟨(Finset.mem_erase.mp hf).1.symm, hsuper.1.1⟩
    have := hmin f n ⟨hcyc, hn⟩
    omega
  · rw [Finset.erase_eq_self.mpr he]
    exact h

lemma refineSetoid_exchange_eq_of_path_internal {V E : Type*} [Fintype V] [Fintype E]
    [DecidableEq E] (G : FiniteGraph V E) [Nonempty V]
    {T : Finset E} {P : Setoid V} {e e' : E}
    (hT : (IsSpanningTree G) T) (he' : e' ∈ T)
    (p : ((supportGraph G) T).Path (G.endAt e 0) (G.endAt e 1))
    (he'path : (symEdge G) e' ∈ p.1.edges)
    (heRel : P.r (G.endAt e 0) (G.endAt e 1))
    (hpath : ∀ f ∈ T, (symEdge G) f ∈ p.1.edges →
      P.r (G.endAt f 0) (G.endAt e 0) ∧
        P.r (G.endAt f 1) (G.endAt e 0)) :
    (refineSetoid G) P (T.erase e' ∪ {e}) = (refineSetoid G) P T := by
  ext u v
  change (P.r u v ∧ (ReachableIn G) ((insideEdges G) (T.erase e' ∪ {e}) P u) u v) ↔
    (P.r u v ∧ (ReachableIn G) ((insideEdges G) T P u) u v)
  constructor
  · rintro ⟨huv, h⟩
    refine ⟨huv, reachable_of_adj_reachable ?_ h⟩
    intro x y hxy
    rw [(supportGraph_adj_iff G)] at hxy
    rcases hxy with ⟨hxy, f, hf, hend⟩
    have hfm := ((mem_insideEdges G).mp) hf
    simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_singleton] at hfm
    rcases hfm.1 with hfT | rfl
    · apply SimpleGraph.Adj.reachable
      rw [(supportGraph_adj_iff G)]
      exact ⟨hxy, f, ((mem_insideEdges G).mpr) ⟨hfT.2,
        hfm.2⟩, hend⟩
    · have hr := (reachableIn_inside_of_walk_of_no_crossing G) p.1
        hfm.2.1 (fun f hfT hfp ↦
          P.trans (hpath f hfT hfp).1 (P.symm (hpath f hfT hfp).2))
      rcases hend with hend | hend
      · simpa [ReachableIn, hend.1, hend.2] using hr
      · simpa [ReachableIn, hend.1, hend.2] using hr.symm
  · rintro ⟨huv, h⟩
    refine ⟨huv, reachable_of_adj_reachable ?_ h⟩
    intro x y hxy
    rw [(supportGraph_adj_iff G)] at hxy
    rcases hxy with ⟨hxy, f, hf, hend⟩
    have hfm := ((mem_insideEdges G).mp) hf
    by_cases hfe : f = e'
    · subst f
      have hp := hpath e' he' he'path
      have he0u := P.trans (P.symm hp.1) hfm.2.1
      have hr := (reachableIn_inside_exchange_of_path_edge G) hT p he'path he0u
        (P.trans (P.symm heRel) he0u) (fun f hfT hfp ↦
          ⟨P.trans (hpath f hfT hfp).1 he0u,
            P.trans (hpath f hfT hfp).2 he0u⟩)
      rcases hend with hend | hend
      · simpa [ReachableIn, hend.1, hend.2] using hr
      · simpa [ReachableIn, hend.1, hend.2] using hr.symm
    · apply SimpleGraph.Adj.reachable
      rw [(supportGraph_adj_iff G)]
      exact ⟨hxy, f, ((mem_insideEdges G).mpr) ⟨by simp [hfe, hfm.1], hfm.2⟩, hend⟩

lemma residualClass_swap_of_residual_of_tree {E : Type*} [Fintype E] [DecidableEq E] {k : ℕ}
    {χ : E → Fin (k + 1)} {i : Fin k} {e e' : E}
    (heRes : e ∈ residualClass χ)
    (he'T : e' ∈ colorClass χ i.castSucc) :
    residualClass (swapColor χ e e') =
      (residualClass χ).erase e ∪ {e'} := by
  ext x
  by_cases h : x = e <;> by_cases h' : x = e' <;>
    simp_all [residualClass, swapColor]

def HasSuperfluousLevel {V E : Type*} [Fintype V] [Fintype E] [DecidableEq E] (G : FiniteGraph V E)
    {k : ℕ} (χ : E → Fin (k + 1)) (m : ℕ) : Prop :=
  ∃ e : E, (IsSuperfluousAt G) χ e m

noncomputable def minSuperfluousLevel {V E : Type*} [Fintype V] [Fintype E] [DecidableEq E]
    (G : FiniteGraph V E) {k : ℕ} (χ : E → Fin (k + 1)) : ℕ := by
  classical
  exact if h : ∃ m, (HasSuperfluousLevel G) χ m then Nat.find h else 0

lemma minSuperfluousLevel_le {V E : Type*} [Fintype V] [Fintype E] [DecidableEq E]
    (G : FiniteGraph V E) {k : ℕ} {χ : E → Fin (k + 1)} {m : ℕ}
    (hm : (HasSuperfluousLevel G) χ m) :
    (minSuperfluousLevel G) χ ≤ m := by
  classical
  rw [minSuperfluousLevel, dif_pos ⟨m, hm⟩]
  exact Nat.find_min' _ hm

def HasKaiserImprovementStep {V E : Type*} [Fintype V] [Fintype E] [DecidableEq E]
    (G : FiniteGraph V E) (k : ℕ) : Prop :=
  ∀ χ : E → Fin (k + 1), (PrefixTrees G) χ →
    ¬ (Connects G) (residualClass χ) →
      ∃ χ' : E → Fin (k + 1), (PrefixTrees G) χ' ∧
        ((residualComponents G) χ' < (residualComponents G) χ ∨
          (residualComponents G) χ' = (residualComponents G) χ ∧
            (minSuperfluousLevel G) χ' < (minSuperfluousLevel G) χ)

noncomputable def coloringOfPacking {E : Type*} [DecidableEq E] {k : ℕ} (T : Fin k → Finset E) :
    E → Fin (k + 1) := fun e ↦
  if h : ∃ i : Fin k, e ∈ T i then (Classical.choose h).castSucc else Fin.last k

def IsThreeEdgeConnected {V E : Type*} [Fintype V] [Fintype E] (H : FiniteGraph V E) : Prop :=
  ∀ S : Finset V, S.Nonempty → S ≠ Finset.univ → 3 ≤ ((cut H) S).card

def doubleGraph {V E : Type*} [Fintype V] [Fintype E] (H : FiniteGraph V E) : FiniteGraph V
    (E × Fin 2) where
  endAt e i := H.endAt e.1 i
  loopless e := H.loopless e.1

noncomputable def classFinset {V : Type*} [Fintype V] (P : Setoid V) (q : Quotient P) : Finset V :=
    by
  classical
  exact Finset.univ.filter fun v => Quotient.mk P v = q

@[simp]
lemma mem_classFinset {V : Type*} [Fintype V] {P : Setoid V} {q : Quotient P} {v : V} :
    v ∈ classFinset P q ↔ Quotient.mk P v = q := by simp[classFinset]

@[simp]
lemma mem_cut_classFinset {V E : Type*} [Fintype V] [Fintype E] (H : FiniteGraph V E) {P : Setoid V}
    {q : Quotient P} {e : E} :
    e ∈ (cut H) (classFinset P q) ↔
      (Quotient.mk P (H.endAt e 0) = q) ≠
        (Quotient.mk P (H.endAt e 1) = q) := by simp[cut,Crosses]

def contractEdgeSetoid {V E : Type*} [Fintype V] [Fintype E] (H : FiniteGraph V E) (e : E) : Setoid
    V where
  r u v := u = v ∨
    (u = H.endAt e 0 ∧ v = H.endAt e 1) ∨
      (u = H.endAt e 1 ∧ v = H.endAt e 0)
  iseqv := by
    constructor
    · intro u
      exact Or.inl rfl
    · intro u v huv
      rcases huv with rfl | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact Or.inl rfl
      · exact Or.inr (Or.inr ⟨rfl, rfl⟩)
      · exact Or.inr (Or.inl ⟨rfl, rfl⟩)
    · intro u v w huv hvw
      rcases huv with rfl | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact hvw
      · rcases hvw with rfl | ⟨h, _⟩ | ⟨_, rfl⟩
        · exact Or.inr (Or.inl ⟨rfl, rfl⟩)
        · exact (H.loopless e h.symm).elim
        · exact Or.inl rfl
      · rcases hvw with rfl | ⟨_, rfl⟩ | ⟨h, _⟩
        · exact Or.inr (Or.inr ⟨rfl, rfl⟩)
        · exact Or.inl rfl
        · exact (H.loopless e h).elim

def SurvivesContraction {V E : Type*} [Fintype V] [Fintype E] (H : FiniteGraph V E) (e f : E) : Prop
    :=
  ¬ ((contractEdgeSetoid H) e).r (H.endAt f 0) (H.endAt f 1)

noncomputable instance contractEdgeQuotientDecidableEq
    {V E : Type*} [Fintype V] [Fintype E] (H : FiniteGraph V E) (e : E) :
    DecidableEq (Quotient ((contractEdgeSetoid H) e)) := Classical.decEq _

noncomputable instance survivesContractionDecidablePred
    {V E : Type*} [Fintype V] [Fintype E] (H : FiniteGraph V E) (e : E) :
    DecidablePred ((SurvivesContraction H) e) := Classical.decPred _

noncomputable instance survivesContractionFintype
    {V E : Type*} [Fintype V] [Fintype E] (H : FiniteGraph V E) (e : E) :
    Fintype {f : E // (SurvivesContraction H) e f} :=
  Fintype.ofFinite _

noncomputable def contractEdge {V E : Type*} [Fintype V] [Fintype E] (H : FiniteGraph V E) (e : E) :
    FiniteGraph (Quotient ((contractEdgeSetoid H) e))
      {f : E // (SurvivesContraction H) e f} := by
  classical
  letI : Fintype (Quotient ((contractEdgeSetoid H) e)) := Fintype.ofFinite _
  letI : Fintype {f : E // (SurvivesContraction H) e f} := Fintype.ofFinite _
  exact
    { endAt := fun f i => Quotient.mk _ (H.endAt f.1 i)
      loopless := by
        intro f h
        exact f.2 (Quotient.eq'.mp h) }

noncomputable def contractionPullback {V E : Type*} [Fintype V] [Fintype E] (H : FiniteGraph V E)
    (e : E)
    (A : Finset (Quotient ((contractEdgeSetoid H) e))) : Finset V := by
  classical
  exact Finset.univ.filter fun v => Quotient.mk ((contractEdgeSetoid H) e) v ∈ A

@[simp]
lemma mem_contractionPullback {V E : Type*} [Fintype V] [Fintype E] (H : FiniteGraph V E) {e : E}
    {A : Finset (Quotient ((contractEdgeSetoid H) e))} {v : V} :
    v ∈ (contractionPullback H) e A ↔
      Quotient.mk ((contractEdgeSetoid H) e) v ∈ A := by simp[contractionPullback]

lemma mem_contractEdge_cut_iff {V E : Type*} [Fintype V] [Fintype E] (H : FiniteGraph V E) {e : E}
    (A : Finset (Quotient ((contractEdgeSetoid H) e)))
    (f : {f : E // (SurvivesContraction H) e f}) :
    f ∈ (cut ((contractEdge H) e)) A ↔
      f.1 ∈ (cut H) ((contractionPullback H) e A) := by simp[cut,Crosses,contractEdge]

def gammaUnit : Gamma := Pi.single 0 1

lemma sum_cut_term_gamma_eq_sum_cut {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V]
    (H : FiniteGraph V E) (φ : E → Gamma) (S : Finset V) :
    (∑ e : E,
      ((if H.endAt e 0 ∈ S then φ e else 0) -
        (if H.endAt e 1 ∈ S then φ e else 0))) =
      ∑ e ∈ (cut H) S, φ e := by
  classical
  simp only [cut, Finset.sum_filter, Crosses]
  apply Finset.sum_congr rfl
  intro e _
  split_ifs <;> simp_all [CubicGraph.neg_gamma]

lemma sum_lift_off_contract_endpoints {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V]
    (H : FiniteGraph V E) {e : E}
    (ψ : (NowhereZeroFlow ((contractEdge H) e)) Gamma) (a : Gamma)
    {v : V} (hv0 : v ≠ H.endAt e 0) (hv1 : v ≠ H.endAt e 1)
    (j : Fin 2) :
    (∑ f : E, if H.endAt f j = v then
        (if hf : (SurvivesContraction H) e f then ψ.val ⟨f, hf⟩ else a) else 0) =
      ∑ f : {f : E // (SurvivesContraction H) e f},
        if ((contractEdge H) e).endAt f j = Quotient.mk _ v then ψ.val f else 0 := by
  classical
  have hsurv (f : E) (hf : H.endAt f j = v) :
      (SurvivesContraction H) e f := by
    intro h
    rcases h with h | h | h
    · exact H.loopless f h
    · fin_cases j
      · exact hv0 (hf.symm.trans h.1)
      · exact hv1 (hf.symm.trans h.2)
    · fin_cases j
      · exact hv1 (hf.symm.trans h.1)
      · exact hv0 (hf.symm.trans h.2)
  have hquot (f : {f : E // (SurvivesContraction H) e f}) :
      ((contractEdge H) e).endAt f j = Quotient.mk _ v ↔
        H.endAt f.1 j = v := by
    constructor
    · intro h
      have hr : ((contractEdgeSetoid H) e).r (H.endAt f.1 j) v := by
        apply Quotient.eq'.mp
        exact h
      rcases hr with hr | hr | hr
      · exact hr
      · exact (hv1 hr.2).elim
      · exact (hv0 hr.2).elim
    · rintro rfl
      rfl
  simp_rw [hquot]
  simp only [← Finset.sum_filter]
  refine Finset.sum_bij
    (fun f hf ↦ ⟨f, hsurv f (Finset.mem_filter.mp hf).2⟩) ?_ ?_ ?_ ?_
  · intro f hf
    simpa using (Finset.mem_filter.mp hf).2
  · intro f₁ hf₁ f₂ hf₂ h
    exact congrArg Subtype.val h
  · intro f hf
    refine ⟨f.1, ?_⟩
    refine ⟨?_, ?_⟩
    · simpa using (Finset.mem_filter.mp hf).2
    · exact Subtype.ext rfl
  · intro f hf
    have hs := hsurv f (Finset.mem_filter.mp hf).2
    simp [hs]

lemma endpoints_componentSetoid_rel {V E : Type*} [Fintype V] [Fintype E] (H : FiniteGraph V E)
    (e : E) :
    ((componentSetoid H) Finset.univ).r (H.endAt e 0) (H.endAt e 1) := by
  apply SimpleGraph.Adj.reachable
  rw[(supportGraph_adj_iff H)]
  exact ⟨H.loopless e,e,by simp,.inl ⟨rfl,rfl⟩⟩

abbrev ComponentVertex {V E : Type*} [Fintype V] [Fintype E] (H : FiniteGraph V E)
    (q : Quotient ((componentSetoid H) Finset.univ)) :=
  {v : V // Quotient.mk ((componentSetoid H) Finset.univ) v = q}

abbrev ComponentEdge {V E : Type*} [Fintype V] [Fintype E] (H : FiniteGraph V E)
    (q : Quotient ((componentSetoid H) Finset.univ)) :=
  {e : E // Quotient.mk ((componentSetoid H) Finset.univ) (H.endAt e 0) = q}

noncomputable instance componentVertexFintype
    {V E : Type*} [Fintype V] [Fintype E] (H : FiniteGraph V E)
    (q : Quotient ((componentSetoid H) Finset.univ)) : Fintype ((ComponentVertex H) q) :=
  Fintype.ofFinite _

noncomputable instance componentEdgeFintype
    {V E : Type*} [Fintype V] [Fintype E] (H : FiniteGraph V E)
    (q : Quotient ((componentSetoid H) Finset.univ)) : Fintype ((ComponentEdge H) q) :=
  Fintype.ofFinite _

noncomputable def componentGraph {V E : Type*} [Fintype V] [Fintype E] (H : FiniteGraph V E)
    (q : Quotient ((componentSetoid H) Finset.univ)) :
    FiniteGraph ((ComponentVertex H) q) ((ComponentEdge H) q) where
  endAt e i := if i = 0 then
      ⟨H.endAt e.1 0, e.2⟩
    else
      ⟨H.endAt e.1 1, by
        have hEq : Quotient.mk ((componentSetoid H) Finset.univ) (H.endAt e.1 1) =
            Quotient.mk ((componentSetoid H) Finset.univ) (H.endAt e.1 0) :=
          (Quotient.sound ((endpoints_componentSetoid_rel H) e.1)).symm
        exact hEq.trans e.2⟩
  loopless := by
    intro e h
    apply H.loopless e.1
    exact congrArg Subtype.val h

lemma mem_componentGraph_cut_iff {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V]
    (H : FiniteGraph V E)
    (q : Quotient ((componentSetoid H) Finset.univ))
    (A : Finset ((ComponentVertex H) q)) (e : (ComponentEdge H) q) :
    e ∈ (cut ((componentGraph H) q)) A ↔
      e.1 ∈ (cut H) (A.image Subtype.val) := by
  have h := (Quotient.sound ((endpoints_componentSetoid_rel H) e.1)).symm.trans e.2
  simp [cut,Crosses,componentGraph,e.2,h]

lemma hasCycleCorrection_compl_of_isSpanningTree :
    ∀ {W F : Type u} [Fintype W] [Fintype F] [DecidableEq W]
      [DecidableEq F] (H : FiniteGraph W F) [Nonempty W]
      (T : Finset F), (IsSpanningTree H) T → ∀ e : F, e ∉ T →
        (HasCycleCorrection H) (Finset.univ \ T) e := by
  intro W F _ _ _ _ H _ T hT e he
  let S := Finset.univ \ T
  have hs {u v} (a : ((supportGraph H) T).Adj u v) : (HasIntegerPath H) S u v := by
    rw [(supportGraph_adj_iff H)] at a
    rcases a with ⟨_, f, hf, h | h⟩
    · simpa [S, h.1, h.2] using (hasIntegerPath_single H) S f (by simp [S, hf])
    · exact HasIntegerPath.symm H (by
        simpa [S, h.1, h.2] using (hasIntegerPath_single H) S f (by simp [S, hf]))
  have hw {u v} (p : ((supportGraph H) T).Walk u v) : (HasIntegerPath H) S u v := by
    induction p with
    | nil => exact ⟨0, by simp, by simp [divergence]⟩
    | cons a p ih => exact HasIntegerPath.trans H (hs a) ih
  obtain ⟨p⟩ := hT.1.1 (H.endAt e 0) (H.endAt e 1)
  have hp := hw p
  rcases hp with ⟨c, hc, hd⟩
  refine ⟨Pi.single e 1 - c, ?_, ?_, ?_⟩
  · intro v
    change (divergence H) (Pi.single e 1 - c) v = 0
    rw [sub_eq_add_neg, (divergence_add H), (divergence_neg H),
      (divergence_single_one H), hd]
    omega
  · simp [hc e (by simp [S, he])]
  · intro k hk
    simp only [Finset.mem_erase] at hk
    simp [hk.1, hc k hk.2]

lemma hasTreePacking_succ_of_hasKaiserImprovementStep : ∀ {W F : Type u} [Fintype W] [Fintype F]
    [DecidableEq F] [Nonempty W]
    (H : FiniteGraph W F) (k : ℕ),
    (HasTreePacking H) k → (HasKaiserImprovementStep H) k →
      (HasTreePacking H) (k + 1) := by
  intro W F _ _ _ _ H k hpack hstep
  classical
  have finish : ∀ a b, ∀ χ : F → Fin (k + 1),
      (residualComponents H) χ = a → (minSuperfluousLevel H) χ = b →
      (PrefixTrees H) χ →
        ∃ χ' : F → Fin (k + 1), (PrefixTrees H) χ' ∧ (Connects H) (residualClass χ') := by
    intro a
    induction a using Nat.strong_induction_on with
    | h a ha =>
      intro b
      induction b using Nat.strong_induction_on with
      | h b hb =>
        intro χ hca hmb hp
        by_cases hc : (Connects H) (residualClass χ)
        · exact ⟨χ, hp, hc⟩
        · obtain ⟨χ', hp', hlt | ⟨heq, hlt⟩⟩ := hstep χ hp hc
          · exact ha _ (by simpa [hca] using hlt) _ χ' rfl rfl hp'
          · exact hb _ (by simpa [hmb] using hlt) χ' (heq.trans hca) rfl hp'
  obtain ⟨T, htree, hdj⟩ := hpack
  let χ := coloringOfPacking T
  have hclass (i : Fin k) : colorClass χ i.castSucc = T i := by
    ext e
    constructor
    · intro he
      have heq := (mem_colorClass.mp he)
      simp only [χ, coloringOfPacking] at heq
      split at heq
      next h =>
        have hi : Classical.choose h = i := Fin.castSucc_injective k heq
        simpa [← hi] using Classical.choose_spec h
      next h => exact (Fin.castSucc_ne_last i heq.symm).elim
    · intro he
      apply mem_colorClass.mpr
      simp only [χ, coloringOfPacking]
      split
      next h =>
        apply congrArg Fin.castSucc
        by_contra hne
        exact Finset.disjoint_left.mp (hdj _ _ hne) (Classical.choose_spec h) he
      next h => exact (h ⟨i, he⟩).elim
  have hp : (PrefixTrees H) χ := fun i => hclass i ▸ htree i
  obtain ⟨χ', hp', hc⟩ := finish _ _ χ rfl rfl hp
  obtain ⟨R, hRsub, hR⟩ := (exists_isSpanningTree_subset_of_connects H) _ hc
  let U : Fin (k + 1) → Finset F := Fin.lastCases R (fun i => colorClass χ' i.castSucc)
  have hU (i : Fin (k + 1)) : U i ⊆ colorClass χ' i := by
    refine Fin.lastCases (by simpa [U, residualClass] using hRsub) (fun a => ?_) i
    simp [U]
  refine ⟨U, ?_, ?_⟩
  · intro i
    refine Fin.lastCases (by simpa [U] using hR) (fun j => ?_) i
    simpa [U] using hp' j
  · intro i j hij
    exact Disjoint.mono (hU i) (hU j) (colorClass_disjoint χ' hij)

lemma connectedComponent_card_union_singleton_lt :
    ∀ {W F : Type u} [Fintype W] [Fintype F]
      [DecidableEq F]
      (H : FiniteGraph W F) (S : Finset F) (f : F),
      (¬ (ReachableIn H) S (H.endAt f 0) (H.endAt f 1)) →
        Nat.card ((supportGraph H) (S ∪ {f})).ConnectedComponent <
          Nat.card ((supportGraph H) S).ConnectedComponent := by
  classical
  intro W F _ _ _ H S f hf
  let G := (supportGraph H) S
  let K := (supportGraph H) (S ∪ {f})
  let q : G.ConnectedComponent → K.ConnectedComponent :=
    @Quotient.map W W G.reachableSetoid K.reachableSetoid id (by
      intro u v h
      change (ReachableIn H) S u v at h
      change (ReachableIn H) (S ∪ {f}) u v
      exact (reachableIn_mono H) Finset.subset_union_left h)
  have hq : Function.Surjective q := by
    intro x
    unfold SimpleGraph.ConnectedComponent at x
    refine Quot.inductionOn x ?_
    intro v
    exact ⟨@Quotient.mk W G.reachableSetoid v, rfl⟩
  have hn : ¬ Function.Injective q := by
    intro h
    have e : (@Quotient.mk W G.reachableSetoid (H.endAt f 0)) =
        @Quotient.mk W G.reachableSetoid (H.endAt f 1) := by
      apply h
      apply Quotient.sound
      apply SimpleGraph.Adj.reachable
      rw [(supportGraph_adj_iff H)]
      exact ⟨H.loopless f, f, by simp, .inl ⟨rfl, rfl⟩⟩
    exact hf (Quotient.eq'.mp e)
  letI := Fintype.ofFinite G.ConnectedComponent
  letI := Fintype.ofFinite K.ConnectedComponent
  simpa [G, K] using Fintype.card_lt_of_surjective_not_injective q hq hn

lemma exists_kaiserImprovement_of_hasSuperfluousEdge : ∀ {W F : Type u} [Fintype W] [Fintype F]
    [DecidableEq F] [Nonempty W]
    (H : FiniteGraph W F) (k : ℕ) (χ : F → Fin (k + 1)),
    (PrefixTrees H) χ → ¬ (Connects H) (residualClass χ) →
    (HasSuperfluousEdge H) χ →
    ∃ χ' : F → Fin (k + 1), (PrefixTrees H) χ' ∧
      ((residualComponents H) χ' < (residualComponents H) χ ∨
        (residualComponents H) χ' = (residualComponents H) χ ∧
          (minSuperfluousLevel H) χ' < (minSuperfluousLevel H) χ) := by
  intro W F _ _ _ _ H k χ htrees hres hsuperEdge
  classical
  have hlevel : ∃ m, (HasSuperfluousLevel H) χ m := by
    rcases hsuperEdge with ⟨e, m, he⟩
    exact ⟨m, e, he⟩
  let m := (minSuperfluousLevel H) χ
  have hmlevel : (HasSuperfluousLevel H) χ m := by
    simp only [m, minSuperfluousLevel, hlevel, dif_pos]
    exact Nat.find_spec hlevel
  obtain ⟨e, he⟩ := hmlevel
  have hminimal (f : F) (n : ℕ) (hf : (IsSuperfluousAt H) χ f n) : m ≤ n := by
    simpa only [m] using (minSuperfluousLevel_le H) ⟨f, hf⟩
  let P := (kaiserPartition H) χ m
  have heP : P.r (H.endAt e 0) (H.endAt e 1) := he.2.1
  have hePnext : ¬ ((kaiserPartition H) χ (m + 1)).r
      (H.endAt e 0) (H.endAt e 1) := he.2.2
  have hfirst_ne_none : (firstDisconnectedColor H) χ P ≠ none := by
    intro hnone
    apply hePnext
    rw [kaiserPartition, refineOnce, hnone]
    exact heP
  obtain ⟨c, hc⟩ := Option.ne_none_iff_exists'.mp hfirst_ne_none
  have heRefine : ¬ ((refineSetoid H) P (colorClass χ c)).r
      (H.endAt e 0) (H.endAt e 1) := by
    have h := hePnext
    change ¬ ((refineOnce H) χ P).r (H.endAt e 0) (H.endAt e 1) at h
    unfold refineOnce at h
    rw [hc] at h
    exact h
  have heNotInside : ¬ (ReachableIn H)
      ((insideEdges H) (colorClass χ c) P (H.endAt e 0))
      (H.endAt e 0) (H.endAt e 1) := by
    intro h
    exact heRefine ⟨heP, h⟩
  have hcLast : c ≠ Fin.last k := by
    intro hclast
    have hclass : colorClass χ c = residualClass χ := by
      simp [hclast, residualClass]
    obtain ⟨w⟩ := he.1.2
    let p := w.toPath
    have hnotR : ¬ (ReachableIn H)
        ((insideEdges H) ((residualClass χ).erase e) P (H.endAt e 0))
        (H.endAt e 0) (H.endAt e 1) := by
      intro h
      apply heNotInside
      rw [hclass]
      apply (reachableIn_mono H) ?_ h
      intro f hf
      simp only [mem_insideEdges] at hf ⊢
      exact ⟨(Finset.mem_erase.mp hf.1).2, hf.2⟩
    obtain ⟨f, hfR, hfpath, hfnot⟩ :=
      (exists_crossing_tree_edge_of_not_internal_reachable H) p.1 hnotR
    obtain ⟨n, hn⟩ := (exists_finiteLevel_of_not_rel H) hfnot
    have hnm : n < m := by
      by_contra hmn
      exact hfnot ((kaiserPartition_refines_of_le H) χ
        (Nat.le_of_not_gt hmn) hn.1)
    have hfcyc : (IsCyclicEdge H) (residualClass χ) f :=
      (cyclicEdge_of_mem_path_of_cyclic_edge H) he.1 p hfR hfpath
    exact (Nat.not_le_of_gt hnm) (hminimal f n ⟨hfcyc, hn⟩)
  have hcval : c.val < k := by
    have hcne : c.val ≠ k := by
      intro h
      apply hcLast
      apply Fin.ext
      simpa using h
    omega
  let i : Fin k := ⟨c.val, hcval⟩
  have hic : i.castSucc = c := Fin.ext rfl
  let T := colorClass χ c
  have hT : (IsSpanningTree H) T := by
    simpa [T, hic] using htrees i
  obtain ⟨w⟩ := hT.1.1 (H.endAt e 0) (H.endAt e 1)
  let p := w.toPath
  have hcross : ∃ f ∈ T, (symEdge H) f ∈ p.1.edges ∧
      ¬ P.r (H.endAt f 0) (H.endAt f 1) := by
    simpa [p] using (exists_crossing_tree_edge_of_not_internal_reachable H)
      (p := p.1) heNotInside
  obtain ⟨f₀, hf₀T, hf₀p, hf₀not⟩ := hcross
  obtain ⟨n₀, hn₀⟩ := (exists_finiteLevel_of_not_rel H) hf₀not
  have hn₀m : n₀ < m := by
    by_contra hmn
    exact hf₀not ((kaiserPartition_refines_of_le H) χ
      (Nat.le_of_not_gt hmn) hn₀.1)
  have hexLevel : ∃ n : ℕ, ∃ f : F,
      f ∈ T ∧ (symEdge H) f ∈ p.1.edges ∧ (HasFiniteLevel H) χ f n :=
    ⟨n₀, f₀, hf₀T, hf₀p, hn₀⟩
  let n := Nat.find hexLevel
  obtain ⟨e', he'T, he'path, he'level⟩ := Nat.find_spec hexLevel
  have hnm : n < m := lt_of_le_of_lt
    (Nat.find_min' hexLevel ⟨f₀, hf₀T, hf₀p, hn₀⟩) hn₀m
  have heRes : e ∈ residualClass χ := he.1.1
  have he'Tclass : χ e' = c := mem_colorClass.mp (show e' ∈ colorClass χ c from he'T)
  have heResClass : χ e = Fin.last k := by
    simpa [residualClass] using (mem_colorClass.mp heRes)
  have hee' : e ≠ e' := by
    intro h
    subst e'
    exact hcLast (heResClass.symm.trans he'Tclass).symm
  have hcolors : χ e ≠ χ e' := by
    rw [heResClass, he'Tclass]
    exact Ne.symm hcLast
  let χ' := swapColor χ e e'
  let T' := T.erase e' ∪ {e}
  have hT'class : colorClass χ' c = T' := by
    simpa [χ', T', T, he'Tclass] using
      (colorClass_swap_right χ (e := e) (e' := e') hee' hcolors)
  have heNotT : e ∉ T := by
    intro heT
    have := mem_colorClass.mp (show e ∈ colorClass χ c from heT)
    exact hcLast (heResClass.symm.trans this).symm
  have he'connect : (ReachableIn H) T' (H.endAt e' 0) (H.endAt e' 1) := by
    have h := reachableIn_inside_exchange_of_path_edge_of_new_support (G := H)
      (T := T) (P := (⊤ : Setoid W)) (u := H.endAt e 0)
      (e := e) (e' := e') p he'path trivial trivial
      (fun _ _ _ ↦ ⟨trivial, trivial⟩)
    rw [(insideEdges_top H)] at h
    exact h
  have hT'conn : (Connects H) T' := by
    rw [Connects, SimpleGraph.connected_iff]
    constructor
    · intro u v
      apply reachable_of_adj_reachable ?_ (hT.1.1 u v)
      intro x y hxy
      rw [(supportGraph_adj_iff H)] at hxy
      rcases hxy with ⟨hxy, f, hfT, hend⟩
      by_cases hfe : f = e'
      · subst f
        rcases hend with hend | hend
        · simpa [ReachableIn, hend.1, hend.2] using he'connect
        · simpa [ReachableIn, hend.1, hend.2] using he'connect.symm
      · apply SimpleGraph.Adj.reachable
        rw [(supportGraph_adj_iff H)]
        exact ⟨hxy, f, by simp [T', hfe, hfT], hend⟩
    · exact hT.1.2
  have hT' : (IsSpanningTree H) T' := by
    refine ⟨hT'conn, ?_⟩
    have heErase : e ∉ T.erase e' := fun hmem ↦ heNotT (Finset.mem_of_mem_erase hmem)
    rw [Finset.card_union_of_disjoint]
    · rw [Finset.card_erase_of_mem he'T]
      simp only [Finset.card_singleton]
      have hcardpos : 0 < T.card := Finset.card_pos.mpr ⟨e', he'T⟩
      calc
        T.card - 1 + 1 + 1 = T.card + 1 := by omega
        _ = Fintype.card W := hT.2
    · simp only [Finset.disjoint_left, Finset.mem_erase, Finset.mem_singleton]
      intro a ha hae
      exact heNotT (hae ▸ ha.2)
  have hprefix' : (PrefixTrees H) χ' := by
    intro d
    by_cases hdi : d = i
    · subst d
      simpa [hic, hT'class] using hT'
    · have hdRes : d.castSucc ≠ χ e := by
        rw [heResClass]
        exact Fin.castSucc_ne_last d
      have hdTree : d.castSucc ≠ χ e' := by
        rw [he'Tclass, ← hic]
        exact fun h ↦ hdi (Fin.castSucc_injective k h)
      rw [colorClass_swap_other χ (e := e) (e' := e') hee' hdRes hdTree]
      exact htrees d
  have he'Ti : e' ∈ colorClass χ i.castSucc := by
    simpa [T, hic] using he'T
  have hresidual' : residualClass χ' = (residualClass χ).erase e ∪ {e'} := by
    simpa [χ'] using residualClass_swap_of_residual_of_tree heRes he'Ti
  have hreach (u v : W) : (ReachableIn H) (residualClass χ) u v →
      (ReachableIn H) (residualClass χ') u v := by
    intro huv
    have h := (reachableIn_erase_of_cyclic H) he.1 huv
    apply (reachableIn_mono H) ?_ h
    intro f hf
    rw [hresidual']
    exact Finset.mem_union_left _ hf
  let oldC := ((supportGraph H) (residualClass χ)).ConnectedComponent
  let newC := ((supportGraph H) (residualClass χ')).ConnectedComponent
  let qmap : oldC → newC := fun q ↦
    Quotient.liftOn q
      (fun v : W ↦
        (Quotient.mk ((supportGraph H) (residualClass χ')).reachableSetoid v : newC))
      (fun (a b : W)
        (h : ((supportGraph H) (residualClass χ)).reachableSetoid.r a b) ↦
          Quotient.sound (hreach a b h))
  have hqsurj : Function.Surjective qmap := by
    intro q
    change Quotient ((supportGraph H) (residualClass χ')).reachableSetoid at q
    refine Quotient.inductionOn q (fun v ↦ ?_)
    exact ⟨(Quotient.mk ((supportGraph H) (residualClass χ)).reachableSetoid v : oldC), rfl⟩
  have hcomponents_le : (residualComponents H) χ' ≤ (residualComponents H) χ := by
    change Nat.card newC ≤ Nat.card oldC
    exact Nat.card_le_card_of_surjective qmap hqsurj
  by_cases hcomponents : (residualComponents H) χ' < (residualComponents H) χ
  · exact ⟨χ', hprefix', Or.inl hcomponents⟩
  have hcomponents_eq : (residualComponents H) χ' = (residualComponents H) χ :=
    Nat.le_antisymm hcomponents_le (Nat.le_of_not_gt hcomponents)
  letI : Fintype oldC := Fintype.ofFinite oldC
  letI : Fintype newC := Fintype.ofFinite newC
  have hcard_components : Fintype.card oldC = Fintype.card newC := by
    simpa [residualComponents, oldC, newC] using hcomponents_eq.symm
  have hqinj : Function.Injective qmap := by
    exact ((Fintype.bijective_iff_surjective_and_card qmap).2
      ⟨hqsurj, hcard_components⟩).1
  have he'new : (ReachableIn H) (residualClass χ')
      (H.endAt e' 0) (H.endAt e' 1) := by
    apply SimpleGraph.Adj.reachable
    rw [(supportGraph_adj_iff H)]
    refine ⟨H.loopless e', e', ?_, .inl ⟨rfl, rfl⟩⟩
    rw [hresidual']
    simp
  have he'old : (ReachableIn H) (residualClass χ)
      (H.endAt e' 0) (H.endAt e' 1) := by
    have hqeq :
        (Quotient.mk ((supportGraph H) (residualClass χ)).reachableSetoid
          (H.endAt e' 0) : oldC) =
        Quotient.mk ((supportGraph H) (residualClass χ)).reachableSetoid
          (H.endAt e' 1) := by
      apply hqinj
      change (Quotient.mk ((supportGraph H) (residualClass χ')).reachableSetoid
          (H.endAt e' 0) : newC) =
        Quotient.mk ((supportGraph H) (residualClass χ')).reachableSetoid
          (H.endAt e' 1)
      exact Quotient.sound he'new
    exact Quotient.eq'.mp hqeq
  have he'oldErase : (ReachableIn H) ((residualClass χ).erase e)
      (H.endAt e' 0) (H.endAt e' 1) :=
    (reachableIn_erase_of_cyclic H) he.1 he'old
  have he'NotRes : e' ∉ residualClass χ := by
    intro hmem
    have hh : χ e' = Fin.last k := by
      simpa [residualClass] using (mem_colorClass.mp hmem)
    exact hcLast (he'Tclass.symm.trans hh)
  have heraseResidual : (residualClass χ').erase e' =
      (residualClass χ).erase e := by
    rw [hresidual']
    ext f
    simp only [Finset.mem_erase, Finset.mem_union, Finset.mem_singleton]
    constructor
    · rintro ⟨hfe', hf | rfl⟩
      · exact hf
      · exact (hfe' rfl).elim
    · intro hf
      exact ⟨fun h ↦ he'NotRes (h ▸ hf.2), Or.inl hf⟩
  have he'Cyclic : (IsCyclicEdge H) (residualClass χ') e' := by
    refine ⟨?_, ?_⟩
    · rw [hresidual']
      simp
    · rw [heraseResidual]
      exact he'oldErase
  have hedge_n (f : F) (hfT : f ∈ T)
      (hfpath : (symEdge H) f ∈ p.1.edges) :
      ((kaiserPartition H) χ n).r (H.endAt f 0) (H.endAt f 1) := by
    by_cases hlev : ∃ q, (HasFiniteLevel H) χ f q
    · obtain ⟨q, hq⟩ := hlev
      exact (kaiserPartition_refines_of_le H) χ
        (Nat.find_min' hexLevel ⟨f, hfT, hfpath, hq⟩) hq.1
    · by_contra hnot
      exact hlev ((exists_finiteLevel_of_not_rel H) hnot)
  have walk_internal : ∀ {x y : W} (q : ((supportGraph H) T).Walk x y),
      ((kaiserPartition H) χ n).r x (H.endAt e 0) →
      (∀ f ∈ T, (symEdge H) f ∈ q.edges →
        ((kaiserPartition H) χ n).r (H.endAt f 0) (H.endAt f 1)) →
      ((kaiserPartition H) χ n).r y (H.endAt e 0) ∧
        ∀ f ∈ T, (symEdge H) f ∈ q.edges →
          ((kaiserPartition H) χ n).r (H.endAt f 0) (H.endAt e 0) ∧
          ((kaiserPartition H) χ n).r (H.endAt f 1) (H.endAt e 0) := by
    intro x y q
    induction q with
    | nil =>
        intro hx hedge
        refine ⟨hx, ?_⟩
        intro f hf hmem
        simp at hmem
    | @cons x z y h q ih =>
        intro hx hedge
        have hadj := h
        rw [(supportGraph_adj_iff H)] at hadj
        rcases hadj with ⟨_, g, hgT, hgends⟩
        have hgmem : (symEdge H) g ∈ (SimpleGraph.Walk.cons h q).edges := by
          rcases hgends with hgends | hgends <;> simp [symEdge, hgends]
        have hgrel := hedge g hgT hgmem
        have hxz : ((kaiserPartition H) χ n).r x z := by
          rcases hgends with hgends | hgends
          · simpa [hgends.1, hgends.2] using hgrel
          · simpa [hgends.1, hgends.2] using ((kaiserPartition H) χ n).symm hgrel
        have hz : ((kaiserPartition H) χ n).r z (H.endAt e 0) :=
          ((kaiserPartition H) χ n).trans
            (((kaiserPartition H) χ n).symm hxz) hx
        have hi := ih hz (fun f hf hmem ↦ hedge f hf (by simp [hmem]))
        refine ⟨hi.1, ?_⟩
        intro f hf hmem
        simp only [SimpleGraph.Walk.edges_cons, List.mem_cons] at hmem
        rcases hmem with hhead | htail
        · simp only [symEdge, Sym2.eq_iff] at hhead
          rcases hhead with hhead | hhead
          · simpa [hhead.1, hhead.2] using And.intro hx hz
          · simpa [hhead.1, hhead.2] using And.intro hz hx
        · exact hi.2 f hf htail
  have hpath_n : ∀ f ∈ T, (symEdge H) f ∈ p.1.edges →
      ((kaiserPartition H) χ n).r (H.endAt f 0) (H.endAt e 0) ∧
      ((kaiserPartition H) χ n).r (H.endAt f 1) (H.endAt e 0) := by
    exact (walk_internal p.1 (((kaiserPartition H) χ n).refl _)
      (fun f hf hfp ↦ hedge_n f hf hfp)).2
  obtain ⟨qwalk⟩ := he'oldErase
  let qpath := qwalk.toPath
  have qpath' : ((supportGraph H) ((residualClass χ').erase e')).Path
      (H.endAt e' 0) (H.endAt e' 1) := by
    rw [heraseResidual]
    exact qpath
  have hexEarly : ∃ f q, q < m ∧ (IsSuperfluousAt H) χ' f q := by
    by_contra hnone
    have hparts : ∀ t, t ≤ n + 1 →
        (kaiserPartition H) χ' t = (kaiserPartition H) χ t := by
      intro t
      induction t with
      | zero =>
          intro _
          rfl
      | succ t ih =>
          intro htn1
          have htn : t ≤ n := by omega
          have htEq := ih (by omega)
          let Pt := (kaiserPartition H) χ t
          have htm : t < m := lt_of_le_of_lt htn hnm
          have heRel : Pt.r (H.endAt e 0) (H.endAt e 1) := by
            exact (kaiserPartition_refines_of_le H) χ (Nat.le_of_lt htm) heP
          have hpath_t : ∀ f ∈ T, (symEdge H) f ∈ p.1.edges →
              Pt.r (H.endAt f 0) (H.endAt e 0) ∧
              Pt.r (H.endAt f 1) (H.endAt e 0) := by
            intro f hfT hfp
            exact ⟨(kaiserPartition_refines_of_le H) χ htn (hpath_n f hfT hfp).1,
              (kaiserPartition_refines_of_le H) χ htn (hpath_n f hfT hfp).2⟩
          have hrefTree : (refineSetoid H) Pt T' = (refineSetoid H) Pt T := by
            exact (refineSetoid_exchange_eq_of_path_internal H) hT he'T p he'path
              heRel hpath_t
          have hqrel : ∀ f ∈ (residualClass χ').erase e',
              (symEdge H) f ∈ qpath'.1.edges →
              Pt.r (H.endAt f 0) (H.endAt f 1) := by
            intro f hfR hfpath
            by_contra hfnot
            have hfnot' : ¬ ((kaiserPartition H) χ' t).r
                (H.endAt f 0) (H.endAt f 1) := by
              rw [htEq]
              simpa [Pt] using hfnot
            obtain ⟨r, hr⟩ := (exists_finiteLevel_of_not_rel H) hfnot'
            have hrt : r < t := by
              by_contra htr
              exact hfnot' ((kaiserPartition_refines_of_le H) χ'
                (Nat.le_of_not_gt htr) hr.1)
            have hfcyc : (IsCyclicEdge H) (residualClass χ') f :=
              (cyclicEdge_of_mem_path_of_cyclic_edge H) he'Cyclic qpath' hfR hfpath
            exact hnone ⟨f, r, lt_trans hrt htm, hfcyc, hr⟩
          have hqinside : (ReachableIn H)
              ((insideEdges H) ((residualClass χ').erase e') Pt (H.endAt e' 0))
              (H.endAt e' 0) (H.endAt e' 1) := by
            apply (reachableIn_inside_of_walk_of_no_crossing H) qpath'.1 (Pt.refl _)
            intro f hfR hfpath
            exact hqrel f hfR hfpath
          have hrefResidual :
              (refineSetoid H) Pt (residualClass χ') =
                (refineSetoid H) Pt (residualClass χ) := by
            ext u v
            change (Pt.r u v ∧ (ReachableIn H)
                ((insideEdges H) (residualClass χ') Pt u) u v) ↔
              (Pt.r u v ∧ (ReachableIn H)
                ((insideEdges H) (residualClass χ) Pt u) u v)
            constructor
            · rintro ⟨huv, h⟩
              refine ⟨huv, reachable_of_adj_reachable ?_ h⟩
              intro x y hxy
              rw [(supportGraph_adj_iff H)] at hxy
              rcases hxy with ⟨hxy, f, hf, hfend⟩
              have hfm := ((mem_insideEdges H).mp) hf
              by_cases hfe : f = e'
              · subst f
                have hbase :
                    (insideEdges H) ((residualClass χ').erase e') Pt (H.endAt e' 0) =
                      (insideEdges H) ((residualClass χ').erase e') Pt u :=
                  insideEdges_eq_of_rel H hfm.2.1
                have hq := hqinside
                rw [hbase, heraseResidual] at hq
                have hqold : (ReachableIn H)
                    ((insideEdges H) (residualClass χ) Pt u)
                    (H.endAt e' 0) (H.endAt e' 1) := by
                  apply (reachableIn_mono H) ?_ hq
                  intro g hg
                  simp only [mem_insideEdges] at hg ⊢
                  exact ⟨Finset.mem_of_mem_erase hg.1, hg.2⟩
                rcases hfend with hfend | hfend
                · simpa [ReachableIn, hfend.1, hfend.2] using hqold
                · simpa [ReachableIn, hfend.1, hfend.2] using hqold.symm
              · apply SimpleGraph.Adj.reachable
                rw [(supportGraph_adj_iff H)]
                refine ⟨hxy, f, ?_, hfend⟩
                apply ((mem_insideEdges H).mpr)
                refine ⟨?_, hfm.2⟩
                rw [hresidual'] at hfm
                rcases (Finset.mem_union.mp hfm.1) with hfR | hf'
                · exact Finset.mem_of_mem_erase hfR
                · exact (hfe (Finset.mem_singleton.mp hf')).elim
            · rintro ⟨huv, h⟩
              refine ⟨huv, ?_⟩
              have her := (reachableIn_inside_erase_of_min_superfluous H)
                he hminimal htm h
              apply (reachableIn_mono H) ?_ her
              intro f hf
              simp only [mem_insideEdges] at hf ⊢
              refine ⟨?_, hf.2⟩
              rw [hresidual']
              exact Finset.mem_union_left _ hf.1
          have hrefColor (d : Fin (k + 1)) :
              (refineSetoid H) Pt (colorClass χ' d) =
                (refineSetoid H) Pt (colorClass χ d) := by
            by_cases hdc : d = c
            · subst d
              simpa [hT'class, T] using hrefTree
            by_cases hdlast : d = Fin.last k
            · subst d
              simpa [residualClass] using hrefResidual
            have hdE : d ≠ χ e := by simpa [heResClass] using hdlast
            have hdE' : d ≠ χ e' := by simpa [he'Tclass] using hdc
            rw [colorClass_swap_other χ (e := e) (e' := e') hee' hdE hdE']
          have hint (d : Fin (k + 1)) :
              (InternallyConnected H) (colorClass χ' d) Pt ↔
                (InternallyConnected H) (colorClass χ d) Pt :=
            (internallyConnected_iff_of_refineSetoid_eq H) (hrefColor d)
          have hfirst : (firstDisconnectedColor H) χ' Pt =
              (firstDisconnectedColor H) χ Pt := by
            generalize ho : (firstDisconnectedColor H) χ Pt = o
            cases o with
            | none =>
                apply ((firstDisconnectedColor_eq_none_iff H) χ' Pt).2
                have hnold := ((firstDisconnectedColor_eq_none_iff H) χ Pt).1 ho
                intro hnnew
                rcases hnnew with ⟨d, hd⟩
                exact hnold ⟨d, fun hold ↦ hd ((hint d).2 hold)⟩
            | some d =>
                apply (firstDisconnectedColor_eq_some_of_spec H)
                · have hd := (firstDisconnectedColor_spec H) ho
                  exact fun hnew ↦ hd ((hint d).1 hnew)
                · intro a had
                  exact (hint a).2 ((firstDisconnectedColor_internal_of_lt H) ho had)
          have hrefOnce : (refineOnce H) χ' Pt = (refineOnce H) χ Pt := by
            unfold refineOnce
            rw [hfirst]
            generalize (firstDisconnectedColor H) χ Pt = o
            cases o with
            | none => rfl
            | some d => exact hrefColor d
          change (refineOnce H) χ' ((kaiserPartition H) χ' t) =
            (refineOnce H) χ ((kaiserPartition H) χ t)
          rw [htEq]
          exact hrefOnce
    have hnEq := hparts n (by omega)
    have hn1Eq := hparts (n + 1) (by omega)
    have he'level' : (HasFiniteLevel H) χ' e' n := by
      constructor
      · rw [hnEq]
        exact he'level.1
      · rw [hn1Eq]
        exact he'level.2
    exact hnone ⟨e', n, hnm, he'Cyclic, he'level'⟩
  obtain ⟨f, r, hrm, hfr⟩ := hexEarly
  have hmin' : (minSuperfluousLevel H) χ' ≤ r :=
    (minSuperfluousLevel_le H) ⟨f, hfr⟩
  refine ⟨χ', hprefix', Or.inr ⟨hcomponents_eq, ?_⟩⟩
  simpa only [m] using lt_of_le_of_lt hmin' hrm

lemma exists_kaiserPartition_firstDisconnectedColor_eq_none :
    ∀ {W F : Type u} [Fintype W] [Fintype F]
      [Nonempty W]
      (H : FiniteGraph W F) (r : ℕ) (χ : F → Fin r),
      ∃ n : ℕ,
        (firstDisconnectedColor H) χ ((kaiserPartition H) χ n) = none := by
  classical
  intro W F _ _ _ H r χ
  by_contra h
  push Not at h
  have hw(n): ∃ x:W×W, ((kaiserPartition H) χ n) x.1 x.2 ∧
      ¬ ((kaiserPartition H) χ (n+1)) x.1 x.2 := by
    cases ho : (firstDisconnectedColor H) χ ((kaiserPartition H) χ n) with
    | none => exact (h n ho).elim
    | some i =>
        have hi := (firstDisconnectedColor_spec H) ho
        rw [InternallyConnected] at hi
        push Not at hi
        obtain ⟨u,v,huv,hn⟩ := hi
        refine ⟨(u,v),huv,?_⟩
        rw [kaiserPartition, refineOnce, ho]
        exact fun q ↦ hn q.2
  choose f hf using hw
  have hinj : Function.Injective (fun i:Fin (Fintype.card (W×W)+1) ↦ f i) := by
    intro a b hab
    change f a.1=f b.1 at hab
    rcases lt_trichotomy a.1 b.1 with hablt | habeq | hbalt
    · exfalso
      apply (hf a.1).2
      rw [hab]
      exact (kaiserPartition_refines_of_le H) χ (Nat.succ_le_of_lt hablt) (hf b.1).1
    · exact Fin.ext habeq
    · exfalso
      apply (hf b.1).2
      rw [← hab]
      exact (kaiserPartition_refines_of_le H) χ (Nat.succ_le_of_lt hbalt) (hf a.1).1
  simpa using Fintype.card_le_of_injective _ hinj

lemma hasTreePacking_of_satisfiesTreePackingCondition :
    ∀ {W F : Type u} [Fintype W] [Fintype F]
      [Nonempty W]
      (H : FiniteGraph W F) (k : ℕ),
      (SatisfiesTreePackingCondition H) k → (HasTreePacking H) k := by
  intro W F _ _ _ H k hc
  classical
  induction k with
  | zero =>
      refine ⟨fun i ↦ Fin.elim0 i, ?_, ?_⟩ <;> intro i
      · exact Fin.elim0 i
      · exact Fin.elim0 i
  | succ k ih =>
    apply (hasTreePacking_succ_of_hasKaiserImprovementStep H) k
    · apply ih
      intro P
      exact (Nat.mul_le_mul_right _ (Nat.le_succ k)).trans (hc P)
    · intro χ htrees hres
      apply (exists_kaiserImprovement_of_hasSuperfluousEdge H) k χ htrees hres
      classical
      obtain ⟨n, hn⟩ := (exists_kaiserPartition_firstDisconnectedColor_eq_none H) (k + 1) χ
      let P := (kaiserPartition H) χ n
      letI : Nonempty (Quotient P) := Nonempty.map (Quotient.mk P) inferInstance
      have hint (d : Fin (k + 1)) : (InternallyConnected H) (colorClass χ d) P := by
        have hnone := ((firstDisconnectedColor_eq_none_iff H) χ P).mp hn
        by_contra hd
        exact hnone ⟨d, hd⟩
      have lift {S : Finset F} {Q : Setoid W} {e : F}
          (hInt : (InternallyConnected H) S Q) (he : e ∈ (crossingClass H) S Q)
          (U : Finset {f : F // f ∈ (crossingClass H) S Q})
          (heU : (⟨e, he⟩ : {f : F // f ∈ (crossingClass H) S Q}) ∉ U) {a b : W}
          (hab : (ReachableIn ((quotientGraph H) S Q)) U (Quotient.mk Q a) (Quotient.mk Q b)) :
          (ReachableIn H) (S.erase e) a b := by
        let rep : Quotient Q → W := fun q ↦ q.out
        have hrep (q : Quotient Q) : Quotient.mk Q (rep q) = q := Quotient.out_eq q
        have within {x y : W} (hxy : Q.r x y) : (ReachableIn H) (S.erase e) x y :=
          (reachableIn_mono H) ((insideEdges_subset_erase_of_crossing H) he x)
            (hInt x y hxy)
        have step {q r : Quotient Q} (hqr : ((supportGraph ((quotientGraph H) S Q)) U).Adj q r) :
            (ReachableIn H) (S.erase e) (rep q) (rep r) := by
          rw [(supportGraph_adj_iff ((quotientGraph H) S Q))] at hqr
          rcases hqr with ⟨_, f, hfU, hf⟩
          have hfe : f.1 ≠ e := by
            intro h
            apply heU
            have : f = ⟨e, he⟩ := Subtype.ext h
            simpa [this] using hfU
          have hedge : (ReachableIn H) (S.erase e) (H.endAt f.1 0) (H.endAt f.1 1) := by
            apply SimpleGraph.Adj.reachable
            rw [(supportGraph_adj_iff H)]
            exact ⟨H.loopless f.1, f.1,
              Finset.mem_erase.mpr ⟨hfe, (((mem_crossingClass H).mp) f.2).1⟩,
              .inl ⟨rfl, rfl⟩⟩
          rcases hf with hf | hf
          · have hq0 : Q.r (rep q) (H.endAt f.1 0) := by
              apply Quotient.eq'.mp
              exact (hrep q).trans hf.1.symm
            have h1r : Q.r (H.endAt f.1 1) (rep r) := by
              apply Quotient.eq'.mp
              exact hf.2.trans (hrep r).symm
            exact (within hq0).trans (hedge.trans (within h1r))
          · have hq1 : Q.r (rep q) (H.endAt f.1 1) := by
              apply Quotient.eq'.mp
              exact (hrep q).trans hf.2.symm
            have h0r : Q.r (H.endAt f.1 0) (rep r) := by
              apply Quotient.eq'.mp
              exact hf.1.trans (hrep r).symm
            exact (within hq1).trans (hedge.symm.trans (within h0r))
        have hmid := reachable_map_of_adj_reachable rep step hab
        have ha : Q.r a (rep (Quotient.mk Q a)) := by
          apply Quotient.eq'.mp
          exact (hrep _).symm
        have hb : Q.r (rep (Quotient.mk Q b)) b := by
          apply Quotient.eq'.mp
          exact hrep _
        exact (within ha).trans (hmid.trans (within hb))
      have acyc (T : Finset F) (hT : (IsSpanningTree H) T) {e : F}
          (he : e ∈ T) : ¬ (ReachableIn H) (T.erase e) (H.endAt e 0) (H.endAt e 1) := by
        intro hecyc
        have hc : (Connects H) (T.erase e) := by
          rw [Connects, SimpleGraph.connected_iff]
          exact ⟨fun u v ↦ (reachableIn_erase_of_cyclic H) ⟨he, hecyc⟩
            (hT.1.1 u v), hT.1.2⟩
        obtain ⟨U, hUsub, hU⟩ := (exists_isSpanningTree_subset_of_connects H) _ hc
        have hcard' : U.card + 1 = T.card + 1 := hU.2.trans hT.2.symm
        have hcard : U.card = T.card := Nat.add_right_cancel hcard'
        have hle := Finset.card_le_card hUsub
        have hp : 0 < T.card := Finset.card_pos.mpr ⟨e, he⟩
        rw [hcard, Finset.card_erase_of_mem he] at hle
        omega
      have tree_crossing_card (i : Fin k) :
          ((crossingClass H) (colorClass χ i.castSucc) P).card + 1 = Nat.card (Quotient P) := by
        let T := colorClass χ i.castSucc
        let QG := (quotientGraph H) T P
        have hT : (IsSpanningTree H) T := htrees i
        have hconn : (Connects QG) Finset.univ :=
          (quotientGraph_connected_of_connects H) T P hT.1
        obtain ⟨U, _, hU⟩ := (exists_isSpanningTree_subset_of_connects QG) _ hconn
        have hUeq : U = Finset.univ := by
          apply Finset.eq_univ_of_forall
          intro e
          by_contra heU
          have hp := hU.1.1 (QG.endAt e 0) (QG.endAt e 1)
          have hlift := lift (hint i.castSucc) e.2 U heU hp
          exact acyc T hT (((mem_crossingClass H).mp) e.2).1 hlift
        have hc := hU.2
        rw [hUeq] at hc
        simpa [QG, T] using hc
      let q := Nat.card (Quotient P)
      have hqpos : 0 < q := Nat.card_pos
      have htreeSum : (∑ i : Fin k,
          ((crossingClass H) (colorClass χ i.castSucc) P).card) = k * (q - 1) := by
        have hcard (i : Fin k) : ((crossingClass H)
            (colorClass χ i.castSucc) P).card = q - 1 := by
          have := tree_crossing_card i
          simp only [q] at *
          omega
        simp_rw [hcard]
        simp
      have hpartition : (∑ d : Fin (k + 1),
          ((crossingClass H) (colorClass χ d) P).card) = ((crossingEdges H) P).card := by
        have hfiber (d : Fin (k + 1)) : ((crossingClass H) (colorClass χ d) P).card =
            (∑ e ∈ (crossingEdges H) P, if χ e = d then 1 else 0) := by
          have heq : (crossingClass H) (colorClass χ d) P = ((crossingEdges H) P).filter
              fun e ↦ χ e = d := by
            ext e
            simp [crossingClass, crossingEdges, colorClass, and_comm]
          rw [heq, Finset.card_eq_sum_ones, Finset.sum_filter]
        simp_rw [hfiber]
        rw [Finset.sum_comm]
        simp
      let R := residualClass χ
      have hresCross : q - 1 ≤ ((crossingClass H) R P).card := by
        have hc' := hc P
        have htotal : ((crossingEdges H) P).card = (∑ i : Fin k,
            ((crossingClass H) (colorClass χ i.castSucc) P).card) +
            ((crossingClass H) R P).card := by
          rw [← hpartition, Fin.sum_univ_castSucc]
          rfl
        rw [htotal, htreeSum] at hc'
        change (k + 1) * (q - 1) ≤
          k * (q - 1) + ((crossingClass H) R P).card at hc'
        have hc' : k * (q - 1) + (q - 1) ≤
            k * (q - 1) + ((crossingClass H) R P).card := by
          simpa only [← Nat.succ_eq_add_one, Nat.succ_mul] using hc'
        omega
      have liftAll {S : Finset F} {Q : Setoid W}
          (hInt : (InternallyConnected H) S Q) {a b : W}
          (hab : (ReachableIn ((quotientGraph H) S Q)) Finset.univ (Quotient.mk Q a)
            (Quotient.mk Q b)) : (ReachableIn H) S a b := by
        let rep : Quotient Q → W := fun z ↦ z.out
        have hrep (z : Quotient Q) : Quotient.mk Q (rep z) = z := Quotient.out_eq z
        have within {x y : W} (hxy : Q.r x y) : (ReachableIn H) S x y := by
          apply reachableIn_mono (G := H) (T := S) _ (hInt x y hxy)
          intro f hf
          exact (((mem_insideEdges H).mp) hf).1
        have step {x y : Quotient Q}
            (hxy : ((supportGraph ((quotientGraph H) S Q)) Finset.univ).Adj x y) :
            (ReachableIn H) S (rep x) (rep y) := by
          rw [(supportGraph_adj_iff ((quotientGraph H) S Q))] at hxy
          rcases hxy with ⟨_, f, _, hf⟩
          have hedge : (ReachableIn H) S (H.endAt f.1 0) (H.endAt f.1 1) := by
            apply SimpleGraph.Adj.reachable
            rw [(supportGraph_adj_iff H)]
            exact ⟨H.loopless f.1, f.1, (((mem_crossingClass H).mp) f.2).1,
              .inl ⟨rfl, rfl⟩⟩
          rcases hf with hf | hf
          · exact (within (Quotient.eq'.mp ((hrep x).trans hf.1.symm))).trans
              (hedge.trans (within (Quotient.eq'.mp (hf.2.trans (hrep y).symm))))
          · exact (within (Quotient.eq'.mp ((hrep x).trans hf.2.symm))).trans
              (hedge.symm.trans (within (Quotient.eq'.mp (hf.1.trans (hrep y).symm))))
        have hmid := reachable_map_of_adj_reachable rep step hab
        exact (within (Quotient.eq'.mp (hrep _).symm)).trans
          (hmid.trans (within (Quotient.eq'.mp (hrep _))))
      by_contra hsuper
      let QG := (quotientGraph H) R P
      have hbridge (e : {f : F // f ∈ (crossingClass H) R P}) :
          ¬ (ReachableIn QG) (Finset.univ.erase e) (QG.endAt e 0) (QG.endAt e 1) := by
        have hnot : ¬ P.r (H.endAt e.1 0) (H.endAt e.1 1) :=
          (((mem_crossingClass H).mp) e.2).2
        obtain ⟨m, hm⟩ := exists_finiteLevel_of_not_rel (G := H) (n := n)
          (by simpa [P] using hnot)
        have hncyc : ¬ (IsCyclicEdge H) R e.1 := by
          intro hc
          exact hsuper ⟨e.1, m, hc, hm⟩
        intro hr
        apply hncyc
        refine ⟨(((mem_crossingClass H).mp) e.2).1, ?_⟩
        exact lift (hint (Fin.last k)) e.2
          (Finset.univ.erase e) (by simp) hr
      have hQdisc : ¬ (Connects QG) Finset.univ := by
        intro hc
        apply hres
        rw [Connects, SimpleGraph.connected_iff]
        refine ⟨?_, inferInstance⟩
        intro a b
        exact liftAll (hint (Fin.last k))
          (hc.1 (Quotient.mk P a) (Quotient.mk P b))
      have hbound : ∀ S : Finset {f : F // f ∈ (crossingClass H) R P},
          Nat.card ((supportGraph QG) S).ConnectedComponent + S.card ≤ q := by
        intro S
        induction S using Finset.induction_on with
        | empty =>
            simp only [Finset.card_empty, add_zero]
            exact Nat.card_le_card_of_surjective
              (fun x : Quotient P ↦
                (Quotient.mk ((supportGraph QG) ∅).reachableSetoid x))
              (Quotient.mk_surjective)
        | @insert e S he ih =>
            have hnr : ¬ (ReachableIn QG) S (QG.endAt e 0) (QG.endAt e 1) := by
              intro hr
              apply hbridge e
              apply (reachableIn_mono QG) ?_ hr
              intro f hf
              exact Finset.mem_erase.mpr ⟨fun h ↦ he (h ▸ hf), by simp⟩
            have hlt := (connectedComponent_card_union_singleton_lt QG) S e hnr
            have hcard : (insert e S).card = S.card + 1 := by simp [he]
            rw [hcard]
            rw [show insert e S = S ∪ {e} by
              ext
              simp]
            omega
      have hcomp : 2 ≤ Nat.card ((supportGraph QG) Finset.univ).ConnectedComponent := by
        have hex : ∃ a b : Quotient P,
            ¬ (ReachableIn QG) Finset.univ a b := by
          by_contra h
          push Not at h
          apply hQdisc
          rw [Connects, SimpleGraph.connected_iff]
          exact ⟨h, inferInstance⟩
        obtain ⟨a, b, hab⟩ := hex
        let f : Fin 2 → ((supportGraph QG) Finset.univ).ConnectedComponent :=
          ![@Quotient.mk (Quotient P) ((supportGraph QG) Finset.univ).reachableSetoid a,
            @Quotient.mk (Quotient P) ((supportGraph QG) Finset.univ).reachableSetoid b]
        have hf : Function.Injective f := by
          intro i j hij
          fin_cases i <;> fin_cases j <;>
            simp_all only [Nat.reduceAdd, Fin.zero_eta, Fin.isValue, Fin.mk_one, zero_ne_one,
              one_ne_zero]
          · apply (hab ?_).elim
            exact Quotient.eq'.mp hij
          · apply (hab ?_).elim
            exact Quotient.eq'.mp hij.symm
        convert Nat.card_le_card_of_injective f hf using 1
        norm_num
      have hb := hbound Finset.univ
      have hedgecard : (Finset.univ : Finset {f : F // f ∈ (crossingClass H) R P}).card =
          ((crossingClass H) R P).card := by simp
      rw [hedgecard] at hb
      omega

lemma nowhereZeroFlow_of_doubleGraph_treePacking_three :
    ∀ {W F : Type u} [Fintype W] [Fintype F] [DecidableEq W]
      (H : FiniteGraph W F) [Nonempty W],
      (HasTreePacking ((doubleGraph H))) 3 → Nonempty ((NowhereZeroFlow H) Gamma) := by
  classical
  intro W F _ _ _ H _ hpacking
  let D := (doubleGraph H)
  rcases hpacking with ⟨T, hT, hdisjoint⟩
  have missing_exists (e : F) :
      ∃ i : Fin 3, (e, 0) ∉ T i ∧ (e, 1) ∉ T i := by
    by_contra h
    push Not at h
    have h0 : (e, 0) ∈ T 0 ∨ (e, 1) ∈ T 0 := by
      by_cases he : (e, 0) ∈ T 0
      · exact Or.inl he
      · exact Or.inr (h 0 he)
    have h1 : (e, 0) ∈ T 1 ∨ (e, 1) ∈ T 1 := by
      by_cases he : (e, 0) ∈ T 1
      · exact Or.inl he
      · exact Or.inr (h 1 he)
    have h2 : (e, 0) ∈ T 2 ∨ (e, 1) ∈ T 2 := by
      by_cases he : (e, 0) ∈ T 2
      · exact Or.inl he
      · exact Or.inr (h 2 he)
    have noSame (i j : Fin 3) (hij : i ≠ j) (b : Fin 2)
        (hi : (e, b) ∈ T i) (hj : (e, b) ∈ T j) : False :=
      (Finset.disjoint_left.mp (hdisjoint i j hij)) hi hj
    rcases h0 with h00 | h01
    · rcases h1 with h10 | h11
      · exact noSame 0 1 (by decide) 0 h00 h10
      · rcases h2 with h20 | h21
        · exact noSame 0 2 (by decide) 0 h00 h20
        · exact noSame 1 2 (by decide) 1 h11 h21
    · rcases h1 with h10 | h11
      · rcases h2 with h20 | h21
        · exact noSame 1 2 (by decide) 0 h10 h20
        · exact noSame 0 2 (by decide) 1 h01 h21
      · exact noSame 0 1 (by decide) 1 h01 h11
  let missing (e : F) : Fin 3 := Classical.choose (missing_exists e)
  have hmissing (e : F) :
      (e, 0) ∉ T (missing e) ∧ (e, 1) ∉ T (missing e) :=
    Classical.choose_spec (missing_exists e)
  let M (i : Fin 3) := {e : F // missing e = i}
  letI (i : Fin 3) : Fintype (M i) := Fintype.ofFinite _
  have correction (i : Fin 3) (e : M i) :
      (HasCycleCorrection D) (Finset.univ \ T i) (e.1, 0) := by
    apply (hasCycleCorrection_compl_of_isSpanningTree D) (T i) (hT i)
    have hm := (hmissing e.1).1
    simpa [e.2] using hm
  choose c hc using correction
  let z (i : Fin 3) (p : F × Fin 2) : ℤ := ∑ e : M i, c i e p
  have hzFlow (i : Fin 3) : (IsFlow D) (z i) := by
    intro v
    have hside (j : Fin 2) :
        (∑ p : F × Fin 2,
          if D.endAt p j = v then z i p else 0) =
        ∑ e : M i, ∑ p : F × Fin 2,
          if D.endAt p j = v then c i e p else 0 := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro p _
      by_cases hp : D.endAt p j = v <;> simp [z, hp]
    rw [hside 0, hside 1, ← Finset.sum_sub_distrib]
    apply Finset.sum_eq_zero
    intro e _
    exact (hc i e).1 v
  let g (i : Fin 3) (p : F × Fin 2) : F₂ := (z i p : F₂)
  have hgFlow (i : Fin 3) : (IsFlow D) (g i) := by
    intro v
    have hv := hzFlow i v
    have hv' := congrArg (Int.castRingHom F₂) hv
    simpa [g] using hv'
  let φ : F → Gamma := fun e i ↦ g i (e, 0) + g i (e, 1)
  refine ⟨
    { val := φ
      conservation := ?_
      nowhereZero := ?_ }⟩
  · intro v
    ext i
    have hi := hgFlow i v
    simp only [D, doubleGraph,
      Fintype.sum_prod_type, Fin.sum_univ_two] at hi
    simp only [Pi.sub_apply, Finset.sum_apply, Pi.zero_apply]
    have hside (j : Fin 2) :
        (∑ e : F, (if H.endAt e j = v then φ e else 0) i) =
          ∑ e : F, (
            (if H.endAt e j = v then g i (e, 0) else 0) +
              (if H.endAt e j = v then g i (e, 1) else 0)) := by
      apply Finset.sum_congr rfl
      intro e _
      by_cases he : H.endAt e j = v <;> simp [φ, he]
    rw [hside 0, hside 1]
    exact hi
  · intro e
    let i := missing e
    let me : M i := ⟨e, rfl⟩
    have hm0 : (e, 0) ∉ T i := by
      simpa [i] using (hmissing e).1
    have hm1 : (e, 1) ∉ T i := by
      simpa [i] using (hmissing e).2
    have off (f : M i) (p : F × Fin 2)
        (hpT : p ∉ T i) (hpf : p ≠ (f.1, 0)) : c i f p = 0 := by
      exact (hc i f).2.2 p (Finset.mem_erase.mpr
        ⟨hpf, Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hpT⟩⟩)
    have hz0 : z i (e, 0) = 1 := by
      change (∑ f : M i, c i f (e, 0)) = 1
      calc
        _ = c i me (e, 0) := by
          apply Fintype.sum_eq_single me
          intro f hfm
          apply off f (e, 0) hm0
          intro hpair
          apply hfm
          exact Subtype.ext (congrArg Prod.fst hpair).symm
        _ = 1 := (hc i me).2.1
    have hz1 : z i (e, 1) = 0 := by
      change (∑ f : M i, c i f (e, 1)) = 0
      apply Finset.sum_eq_zero
      intro f _
      apply off f (e, 1) hm1
      intro hpair
      have := congrArg Prod.snd hpair
      norm_num at this
    intro heq
    have hi := congrFun heq i
    simp [φ, g, hz0, hz1] at hi

lemma nowhereZeroFlow_of_contractEdge_of_twoCut :
    ∀ {W F : Type u} [Fintype W] [Fintype F] [DecidableEq W]
      [DecidableEq F] (H : FiniteGraph W F) (S : Finset W) (a b : F),
      a ≠ b → (cut H) S = {a, b} →
      Nonempty ((NowhereZeroFlow ((contractEdge H) a)) Gamma) →
        Nonempty ((NowhereZeroFlow H) Gamma) := by
  classical
  intro W F _ _ _ _ H S a b hab hcut ⟨ψ⟩
  have haCross : (H.endAt a 0 ∈ S) ≠ (H.endAt a 1 ∈ S) := by
    have : a ∈ (cut H) S := by
      rw [hcut]
      simp
    simpa [cut, Crosses] using this
  have haNot : ¬ (SurvivesContraction H) a a := by
    intro h
    exact h (Or.inr (Or.inl ⟨rfl, rfl⟩))
  let x := if hb : (SurvivesContraction H) a b then ψ.val ⟨b, hb⟩ else gammaUnit
  have hx : x ≠ 0 := by
    dsimp [x]
    split
    · exact ψ.nowhereZero _
    · intro h
      have := congrFun h (0 : Fin 3)
      norm_num [gammaUnit] at this
  let φ : F → Gamma := fun e ↦
    if he : (SurvivesContraction H) a e then ψ.val ⟨e, he⟩ else x
  have hφa : φ a = x := by simp [φ, haNot]
  have hφb : φ b = x := by
    by_cases hb : (SurvivesContraction H) a b <;> simp [φ, x, hb]
  let δ (v : W) : Gamma := (divergence H) φ v
  have hother (v : W) (hv0 : v ≠ H.endAt a 0) (hv1 : v ≠ H.endAt a 1) : δ v = 0 := by
    dsimp [δ, divergence, φ]
    rw [(sum_lift_off_contract_endpoints H) ψ x hv0 hv1 0,
      (sum_lift_off_contract_endpoints H) ψ x hv0 hv1 1]
    exact ψ.conservation _
  have hend (A : Finset W) (hA : (cut H) A = {a, b}) (v : W) (hv : v ∈ A)
      (hsafe : ∀ u ∈ A, u ≠ v → u ≠ H.endAt a 0 ∧ u ≠ H.endAt a 1) : δ v = 0 := by
    calc
      δ v = ∑ u ∈ A, δ u := by
        symm
        apply Finset.sum_eq_single v
        · intro u hu huv
          exact hother u (hsafe u hu huv).1 (hsafe u hu huv).2
        · exact fun h ↦ (h hv).elim
      _ = ∑ e : F, ((if H.endAt e 0 ∈ A then φ e else 0) -
          (if H.endAt e 1 ∈ A then φ e else 0)) := by
        simp [δ, divergence, Finset.sum_sub_distrib, Finset.sum_comm]
      _ = ∑ e ∈ (cut H) A, φ e := (sum_cut_term_gamma_eq_sum_cut H) φ A
      _ = 0 := by
        rw [hA]
        simp [hab, hφa, hφb, show x + x = 0 by simpa using add_neg_cancel x]
  have hcompl : (cut H) (Finset.univ \ S) = {a, b} := by
    rw [show (cut H) (Finset.univ \ S) = (cut H) S by
      ext e
      simp [cut, Crosses]
      tauto]
    exact hcut
  have hends : δ (H.endAt a 0) = 0 ∧ δ (H.endAt a 1) = 0 := by
    by_cases h0 : H.endAt a 0 ∈ S
    · have h1 : H.endAt a 1 ∉ S := fun h1 ↦ haCross (by simp [h0, h1])
      constructor
      · exact hend S hcut _ h0 (fun u hu hu0 ↦ ⟨hu0, fun hu1 ↦ h1 (hu1 ▸ hu)⟩)
      · apply hend (Finset.univ \ S) hcompl _ (by simp [h1])
        intro u hu hu1
        have huS : u ∉ S := by simpa using hu
        exact ⟨fun hu0 ↦ huS (hu0 ▸ h0), hu1⟩
    · have h1 : H.endAt a 1 ∈ S := by
        by_contra h1
        exact haCross (by simp [h0, h1])
      constructor
      · apply hend (Finset.univ \ S) hcompl _ (by simp [h0])
        intro u hu hu0
        have huS : u ∉ S := by simpa using hu
        exact ⟨hu0, fun hu1 ↦ huS (hu1 ▸ h1)⟩
      · exact hend S hcut _ h1 (fun u hu hu1 ↦ ⟨fun hu0 ↦ h0 (hu0 ▸ hu), hu1⟩)
  refine ⟨⟨φ, ?_, ?_⟩⟩
  · intro v
    by_cases hv0 : v = H.endAt a 0
    · simpa [IsFlow, δ, divergence, hv0] using hends.1
    · by_cases hv1 : v = H.endAt a 1
      · simpa [IsFlow, δ, divergence, hv1] using hends.2
      · exact hother v hv0 hv1
  · intro e
    dsimp [φ]
    split
    · exact ψ.nowhereZero _
    · exact hx

lemma contractEdge_bridgeless :
    ∀ {W F : Type u} [Fintype W] [Fintype F] (H : FiniteGraph W F),
      (Bridgeless H) → ∀ a : F,
        (Bridgeless ((contractEdge H) a)) := by
  classical
  intro W F _ _ H hH a A hA
  let S := (contractionPullback H) a A
  have survives {e : F} (he : e ∈ (cut H) S) : (SurvivesContraction H) a e := by
    intro hr
    simp only [cut, Finset.mem_filter, Finset.mem_univ, true_and, Crosses] at he
    apply he
    simp only [S, mem_contractionPullback]
    exact congrArg (· ∈ A) (Quotient.eq'.mpr hr)
  have hc : ((cut ((contractEdge H) a)) A).card = ((cut H) S).card := by
    apply Finset.card_bij (fun e _ ↦ e.1)
    · exact fun e he ↦ ((mem_contractEdge_cut_iff H) A e).mp he
    · exact fun e _ f _ hef ↦ Subtype.ext hef
    · intro e he
      let f : {f : F // (SurvivesContraction H) a f} := ⟨e, survives he⟩
      exact ⟨f, ((mem_contractEdge_cut_iff H) A f).mpr he, rfl⟩
  apply hH S
  rwa [← hc]

lemma contractEdge_connects :
    ∀ {W F : Type u} [Fintype W] [Fintype F] (H : FiniteGraph W F) [Nonempty W],
      (Connects H) Finset.univ → ∀ a : F,
        (Connects ((contractEdge H) a)) Finset.univ := by
  classical
  intro W F _ _ H _ h a
  rw [Connects, SimpleGraph.connected_iff] at h ⊢
  refine ⟨?_, Nonempty.map (Quotient.mk _) h.2⟩
  intro q r
  refine Quotient.inductionOn₂ q r fun u v ↦
    reachable_map_of_adj_reachable (Quotient.mk _) ?_ (h.1 u v)
  intro x y hxy
  by_cases hrel : ((contractEdgeSetoid H) a).r x y
  · have e : Quotient.mk ((contractEdgeSetoid H) a) x =
        Quotient.mk ((contractEdgeSetoid H) a) y := Quotient.eq'.2 hrel
    rw [e]
  · apply SimpleGraph.Adj.reachable
    rw [supportGraph_adj_iff] at hxy ⊢
    rcases hxy with ⟨_, e, _, he⟩
    refine ⟨fun h ↦ hrel (Quotient.eq'.1 h), ⟨e, ?_⟩, by simp, ?_⟩
    · intro h
      rcases he with he | he
      · exact hrel (he.1 ▸ he.2 ▸ h)
      · exact hrel (he.1 ▸ he.2 ▸ ((contractEdgeSetoid H) a).symm h)
    · rcases he with he | he
      · exact .inl ⟨congrArg _ he.1, congrArg _ he.2⟩
      · exact .inr ⟨congrArg _ he.1, congrArg _ he.2⟩

lemma connected_bridgeless_flow_of_threeEdgeConnected_case
    (base : ∀ {W F : Type u} [Fintype W] [Fintype F] [DecidableEq W]
      [DecidableEq F] (H : FiniteGraph W F) [Nonempty W],
        (IsThreeEdgeConnected H) → Nonempty ((NowhereZeroFlow H) Gamma)) :
    ∀ {W F : Type u} [Fintype W] [Fintype F] [DecidableEq W]
      (H : FiniteGraph W F) [Nonempty W],
        (Connects H) Finset.univ → (Bridgeless H) →
          Nonempty ((NowhereZeroFlow H) Gamma) := by
  classical
  intro W F _ _ _ H _ hconn hbridge
  generalize hn : Fintype.card W = n
  induction n using Nat.strong_induction_on generalizing W F with
  | h n ih =>
      by_cases hthree : (IsThreeEdgeConnected H)
      · exact base H hthree
      · unfold IsThreeEdgeConnected at hthree
        push Not at hthree
        obtain ⟨S,hSne,hSproper,hlt⟩ := hthree
        obtain ⟨u,hu⟩ := hSne
        obtain ⟨v, hv⟩ : ∃ v, v ∉ S := by
          simpa [Finset.eq_univ_iff_forall] using hSproper
        have crossing {x y : W} (p : ((supportGraph H) Finset.univ).Walk x y)
            (hx : x ∈ S) (hy : y ∉ S) : ((cut H) S).Nonempty := by
          induction p with
          | nil => exact (hy hx).elim
          | @cons x z y hxz p hp =>
              by_cases hz : z ∈ S
              · exact hp hz hy
              · rw [(supportGraph_adj_iff H)] at hxz
                rcases hxz with ⟨_, e, _, he⟩
                refine ⟨e, ?_⟩
                rcases he with he | he <;> simp [cut, Crosses, he, hx, hz]
        obtain ⟨p⟩ := hconn.preconnected u v
        have hcard : ((cut H) S).card = 2 := by
          have := Finset.card_pos.mpr (crossing p hu hv)
          have := hbridge S
          omega
        obtain ⟨a,b,hab,hcut⟩ := Finset.card_eq_two.mp hcard
        apply (nowhereZeroFlow_of_contractEdge_of_twoCut H) S a b hab hcut
        letI := Nonempty.map (Quotient.mk ((contractEdgeSetoid H) a))
          (inferInstance : Nonempty W)
        apply ih (Fintype.card (Quotient ((contractEdgeSetoid H) a)))
        · simpa [hn] using Fintype.card_lt_of_surjective_not_injective
            (Quotient.mk _) Quotient.mk_surjective fun h ↦
              H.loopless a (h (Quotient.sound (Or.inr (Or.inl ⟨rfl, rfl⟩))))
        · exact (contractEdge_connects H) hconn a
        · exact (contractEdge_bridgeless H) hbridge a
        · rfl

lemma nowhereZeroFlow_of_componentGraph_flows :
    ∀ {W F : Type u} [Fintype W] [Fintype F]
      [DecidableEq W] (H : FiniteGraph W F),
      (∀ q : Quotient ((componentSetoid H) Finset.univ),
        Nonempty ((NowhereZeroFlow ((componentGraph H) q)) Gamma)) →
      Nonempty ((NowhereZeroFlow H) Gamma) := by
  classical
  intro W F _ _ _ H h
  let Q := (componentSetoid H) Finset.univ
  let ψ (q : Quotient Q) := Classical.choice (h q)
  let qedge (e : F) : Quotient Q := Quotient.mk Q (H.endAt e 0)
  let φ (e : F) : Gamma := (ψ (qedge e)).val ⟨e, rfl⟩
  refine ⟨⟨φ, ?_, fun e ↦ (ψ (qedge e)).nowhereZero ⟨e, rfl⟩⟩⟩
  intro v
  let qv : Quotient Q := Quotient.mk Q v
  let vv : (ComponentVertex H) qv := ⟨v, rfl⟩
  have hedge (e : F) (j : Fin 2) (he : H.endAt e j = v) : qedge e = qv := by
    fin_cases j
    · exact congrArg (Quotient.mk Q) he
    · exact (Quotient.sound ((endpoints_componentSetoid_rel H) e)).trans
        (congrArg (Quotient.mk Q) he)
  have htransport (e : F) {q : Quotient Q} (hq : qedge e = q) :
      φ e = (ψ q).val ⟨e, hq⟩ := by
    subst q
    rfl
  have hend (e : (ComponentEdge H) qv) (j : Fin 2) :
      ((componentGraph H) qv).endAt e j = vv ↔ H.endAt e.1 j = v := by
    fin_cases j <;> simp [componentGraph, vv]
  have hside (j : Fin 2) :
      (∑ e : F, if H.endAt e j = v then φ e else 0) =
        ∑ e : (ComponentEdge H) qv,
          if ((componentGraph H) qv).endAt e j = vv then (ψ qv).val e else 0 := by
    simp only [hend, ← Finset.sum_filter]
    refine Finset.sum_bij (fun e he ↦ ⟨e, hedge e j (Finset.mem_filter.mp he).2⟩) ?_ ?_ ?_ ?_
    · intro e he
      simpa using (Finset.mem_filter.mp he).2
    · intro e₁ he₁ e₂ he₂ he
      exact congrArg Subtype.val he
    · intro e he
      refine ⟨e.1, ?_, Subtype.ext rfl⟩
      simpa using (Finset.mem_filter.mp he).2
    · intro e he
      have hq := hedge e j (Finset.mem_filter.mp he).2
      change φ e = (ψ qv).val ⟨e, hq⟩
      exact htransport e hq
  rw [hside 0, hside 1]
  exact (ψ qv).conservation vv

lemma componentGraph_bridgeless :
    ∀ {W F : Type u} [Fintype W] [Fintype F]
      (H : FiniteGraph W F)
      (q : Quotient ((componentSetoid H) Finset.univ)),
      (Bridgeless H) → (Bridgeless ((componentGraph H) q)) := by
  classical
  intro W F _ _ H q hH A
  let B := A.image Subtype.val
  have hc : ((cut ((componentGraph H) q)) A).card = ((cut H) B).card := by
    apply Finset.card_bij (fun e _ ↦ e.1)
    · exact fun e he ↦ ((mem_componentGraph_cut_iff H) q A e).mp he
    · exact fun e _ f _ h ↦ Subtype.ext h
    · intro e he
      have hcross : (H.endAt e 0 ∈ B) ≠ (H.endAt e 1 ∈ B) := by
        simpa [cut, Crosses] using he
      have endpoint {j : Fin 2} (hj : H.endAt e j ∈ B) :
          Quotient.mk ((componentSetoid H) Finset.univ) (H.endAt e j) = q := by
        rcases Finset.mem_image.mp hj with ⟨v, hv, hve⟩
        rw [← hve]
        exact v.2
      have heq : Quotient.mk ((componentSetoid H) Finset.univ) (H.endAt e 0) = q := by
        by_cases h0 : H.endAt e 0 ∈ B
        · exact endpoint h0
        · have h1 : H.endAt e 1 ∈ B := by
            by_contra h1
            exact hcross (propext (by simp [h0, h1]))
          exact (Quotient.sound ((endpoints_componentSetoid_rel H) e)).trans (endpoint h1)
      let f : (ComponentEdge H) q := ⟨e, heq⟩
      exact ⟨f, ((mem_componentGraph_cut_iff H) q A f).mpr he, rfl⟩
  intro h
  apply hH B
  rwa [← hc]

lemma bridgeless_flow_of_threeEdgeConnected_case
    (base : ∀ {W F : Type u} [Fintype W] [Fintype F] [DecidableEq W]
      [DecidableEq F] (H : FiniteGraph W F) [Nonempty W],
        (IsThreeEdgeConnected H) → Nonempty ((NowhereZeroFlow H) Gamma)) :
    ∀ {W F : Type u} [Fintype W] [Fintype F] [DecidableEq W]
      (H : FiniteGraph W F), (Bridgeless H) →
        Nonempty ((NowhereZeroFlow H) Gamma) := by
  classical
  intro W F _ _ _ H hb
  generalize hn : Fintype.card W = n
  induction n using Nat.strong_induction_on generalizing W F with
  | h n ih =>
    by_cases hc : (Connects H) Finset.univ
    · letI : Nonempty W := hc.nonempty
      exact connected_bridgeless_flow_of_threeEdgeConnected_case base H hc hb
    · apply (nowhereZeroFlow_of_componentGraph_flows H)
      intro q
      apply ih (Fintype.card ((ComponentVertex H) q))
      · rw [← hn]
        obtain ⟨x, hx⟩ : ∃ x : W,
            Quotient.mk ((componentSetoid H) Finset.univ) x ≠ q := by
          by_contra h
          push Not at h
          apply hc
          rw [Connects, SimpleGraph.connected_iff]
          exact ⟨fun u v ↦ Quotient.eq'.mp ((h u).trans (h v).symm),
            Quotient.inductionOn q fun v ↦ ⟨v⟩⟩
        exact Fintype.card_subtype_lt hx
      · exact (componentGraph_bridgeless H) q hb
      · rfl

lemma expansionGraph_bridgeless :
    ∀ {W F : Type u} [Fintype W] [Fintype F]
      (H : FiniteGraph W F)
      (R : (RotationSystem H)),
      (Bridgeless H) → (Bridgeless ((expansionGraph H) R)) := by
  classical
  intro W F _ _ H R hb A hcard
  obtain ⟨x, hx⟩ := Finset.card_eq_one.mp hcard
  cases x with
  | inl e =>
      have hnext (h : HalfEdge F) : h ∈ A ↔ R.next h ∈ A := by
        have hn : Sum.inr h ∉ (cut ((expansionGraph H) R)) A := by
          rw [hx]
          simp
        simpa [cut, Crosses, expansionGraph] using hn
      have hiter (n : ℕ) (h : HalfEdge F) :
          h ∈ A ↔ (R.next : HalfEdge F → HalfEdge F)^[n] h ∈ A := by
        induction n generalizing h with
        | zero => simp
        | succ n ih =>
            rw [Function.iterate_succ_apply]
            exact (hnext h).trans (ih (R.next h))
      let S : Finset W := Finset.univ.filter fun v ↦
        ∃ h : HalfEdge F, (vertex H) h = v ∧ h ∈ A
      have hS (h : HalfEdge F) : (vertex H) h ∈ S ↔ h ∈ A := by
        constructor
        · intro hh
          obtain ⟨k, hk, hkA⟩ := (Finset.mem_filter.mp hh).2
          obtain ⟨n, hn⟩ := R.fiberTransitive k h hk
          have hi := (hiter n k).mp hkA
          simpa [hn] using hi
        · intro hh
          exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, h, rfl, hh⟩
      apply hb S
      have hcut : (cut H) S = {e} := by
        ext f
        have hp : f ∈ (cut H) S ↔ Sum.inl f ∈ (cut ((expansionGraph H) R)) A := by
          simp only [cut, Finset.mem_filter, Finset.mem_univ,
            true_and, Crosses]
          change ((H.endAt f 0 ∈ S) ≠ (H.endAt f 1 ∈ S)) ↔
            (((f, 0) ∈ A) ≠ ((f, 1) ∈ A))
          rw [show H.endAt f 0 ∈ S ↔ (f, 0) ∈ A by
                simpa only [vertex] using hS (f, 0),
              show H.endAt f 1 ∈ S ↔ (f, 1) ∈ A by
                simpa only [vertex] using hS (f, 1)]
        rw [hp, hx]
        simp
      rw [hcut]
      simp
  | inr h₀ =>
      have ht (h : HalfEdge F) :
          ((h ∈ A) ≠ (R.next h ∈ A)) ↔ h = h₀ := by
        have hm : Sum.inr h ∈ (cut ((expansionGraph H) R)) A ↔
            Sum.inr h ∈ ({Sum.inr h₀} : Finset (ExpandedEdge H)) := by
          rw [hx]
        simpa [cut, Crosses, expansionGraph] using hm
      let b : HalfEdge F → F₂ := fun h ↦ if h ∈ A then 1 else 0
      have hs : ∑ h, (b h + b (R.next h)) = 0 := by
        rw [Finset.sum_add_distrib,
          show (∑ h, b (R.next h)) = ∑ h, b h from
            R.next.sum_comp Finset.univ b (by simp)]
        exact CharTwo.add_self_eq_zero _
      have bitxor (p q : Prop) [Decidable p] [Decidable q] :
          (if p then 1 else 0 : F₂) + (if q then 1 else 0) =
            if p ≠ q then 1 else 0 := by
        by_cases hp : p <;> by_cases hq : q <;>
          simp [hp, hq, CharTwo.add_self_eq_zero]
      have hs' : ∑ h, (b h + b (R.next h)) = 1 := by
        simp_rw [b, bitxor, ht]
        simp
      rw [hs] at hs'
      norm_num at hs'

theorem cycleDoubleCover_of_bridgeless
    {V E : Type u} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (G : FiniteGraph V E) (hb : (Bridgeless G)) :
    Nonempty (CycleDoubleCover G) := by
  classical
  have b : ∀ {W F : Type u} [Fintype W] [Fintype F] [DecidableEq W]
      [DecidableEq F] (H : FiniteGraph W F) [Nonempty W],
      (IsThreeEdgeConnected H) → Nonempty ((NowhereZeroFlow H) Gamma) := by
    intro W F _ _ _ _ H _ ht
    apply (nowhereZeroFlow_of_doubleGraph_treePacking_three H)
    apply (hasTreePacking_of_satisfiesTreePackingCondition (doubleGraph H)) 3
    intro P
    have xor (a b q : Quotient P) (h : a ≠ b) :
        (if (a = q) ≠ (b = q) then 1 else 0) =
          (if q = a then 1 else 0) + if q = b then 1 else 0 := by
      by_cases ha : a = q <;> by_cases hb : b = q <;> simp_all [eq_comm]
    let K := classFinset P
    by_cases hs : Nat.card (Quotient P) ≤ 1
    · suffices Nat.card (Quotient P) - 1 = 0 by simp_all
      omega
    · have hp (q : Quotient P) : K q ≠ Finset.univ := by
        intro hq
        change classFinset P q = Finset.univ at hq
        apply hs
        rw [Nat.card_eq_fintype_card, Fintype.card_le_one_iff_subsingleton]
        constructor
        intro r s
        refine Quotient.inductionOn₂ r s fun v w ↦ ?_
        have h (x : W) : Quotient.mk P x = q :=
          mem_classFinset.mp (by
            rw [hq]
            simp)
        exact (h v).trans (h w).symm
      have hc (q : Quotient P) : 3 ≤ ((cut H) (K q)).card :=
      ht _ ⟨Quotient.out q,
          mem_classFinset.mpr (Quotient.out_eq q)⟩ (hp q)
      have hl : 3 * Nat.card (Quotient P) ≤
          ∑ q : Quotient P, ((cut H) (K q)).card := by
        rw [Nat.card_eq_fintype_card]
        calc
          3 * Fintype.card (Quotient P) =
              ∑ _ : Quotient P, 3 := by simp [mul_comm]
          _ ≤ _ := Finset.sum_le_sum fun q _ ↦ hc q
      have sm : (∑ q : Quotient P, ((cut H) (K q)).card) =
          2 * ((crossingEdges H) P).card := by
        have cd (q : Quotient P) : ((cut H) (K q)).card =
            ∑ e : F, if e ∈ (cut H) (K q) then 1 else 0 := by
          rw [Finset.card_eq_sum_ones]
          simp [cut]
        have ed (e : F) :
            (∑ q : Quotient P,
              if e ∈ (cut H) (K q) then 1 else 0) =
              if e ∈ (crossingEdges H) P then 2 else 0 := by
          by_cases hr : P.r (H.endAt e 0) (H.endAt e 1)
          · have heq : Quotient.mk P (H.endAt e 0) =
                Quotient.mk P (H.endAt e 1) := Quotient.sound hr
            simp [K, (mem_cut_classFinset H), heq, crossingEdges, hr]
          · have hne : Quotient.mk P (H.endAt e 0) ≠
                Quotient.mk P (H.endAt e 1) := fun h ↦ hr (Quotient.exact h)
            simp only [K, (mem_cut_classFinset H), xor _ _ _ hne,
              Finset.sum_add_distrib]
            simp [crossingEdges, hr]
        calc
          _ = ∑ e : F, ∑ q : Quotient P,
              if e ∈ (cut H) (K q) then 1 else 0 := by
            simp_rw [cd]
            rw [Finset.sum_comm]
          _ = ∑ e : F, if e ∈ (crossingEdges H) P then 2 else 0 := by
            apply Finset.sum_congr rfl
            intro e _
            exact ed e
          _ = 2 * ((crossingEdges H) P).card := by simp [mul_comm]
      have hd : ((crossingEdges (doubleGraph H)) P).card =
          2 * ((crossingEdges H) P).card := by
        let f : {p : F × Fin 2 // p ∈ (crossingEdges (doubleGraph H)) P} ≃
            {e : F // e ∈ (crossingEdges H) P} × Fin 2 :=
          { toFun := by
              rintro ⟨⟨e, i⟩, hp⟩
              exact ⟨⟨e, by simpa [crossingEdges, doubleGraph] using hp⟩, i⟩
            invFun := by
              rintro ⟨⟨e, he⟩, i⟩
              exact ⟨(e, i), by simpa [crossingEdges, doubleGraph] using he⟩
            left_inv := by
              rintro ⟨⟨e, i⟩, h⟩
              rfl
            right_inv := by
              rintro ⟨⟨e, h⟩, i⟩
              rfl }
        have hc := Fintype.card_congr f
        simpa [Fintype.card_coe, mul_comm] using hc
      rw [hd]
      exact (Nat.mul_le_mul_left 3 (Nat.sub_le _ _)).trans
        (hl.trans_eq sm)
  let R := (rotationSystemOfBridgeless G) hb
  obtain ⟨f⟩ := bridgeless_flow_of_threeEdgeConnected_case b
    ((expansionGraph G) R) ((expansionGraph_bridgeless G) R hb)
  have hend (e : (ExpandedEdge G)) (i : Fin 2) :
      ((cubicExpansion G) R).toFiniteGraph.endAt e i =
        ((expansionGraph G) R).endAt e i := by
    cases e <;> fin_cases i <;> rfl
  have f' : NowhereZeroFlow (((cubicExpansion G) R).toFiniteGraph) Gamma :=
    ⟨f.val, fun v ↦ by simpa only [hend] using f.conservation v, f.nowhereZero⟩
  let C := cubic_even_double_cover ((cubicExpansion G) R)
    (((cubicExpansion G) R).gammaFlowOfNowhereZero f')
  exact ⟨((projectEvenDoubleCover G) R C).toCycleDoubleCover⟩

#print axioms cycleDoubleCover_of_bridgeless
-- 'CycleDoubleCoverConjecture.cycleDoubleCover_of_bridgeless' depends on axioms:
-- [propext, Classical.choice, Quot.sound]

end CycleDoubleCoverConjecture
