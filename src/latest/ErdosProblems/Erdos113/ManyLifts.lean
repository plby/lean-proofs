import ErdosProblems.Erdos113.LiftCounting
import ErdosProblems.Erdos113.Supersaturation28

open scoped SimpleGraph

namespace Erdos113ManyLifts

noncomputable section

open Erdos113Cycles Erdos113Alternating56 Erdos113LiftCounting

variable {T V : Type*} [Fintype T] [DecidableEq T]
  [Fintype V] [DecidableEq V]

/-- The finite data needed to lift an auxiliary edge `a--b` through a
middle host vertex.  This is the abstract core of Janzer's many-four-cycle
construction. -/
structure LiftSystem (F : SimpleGraph T) (G : SimpleGraph V) where
  embed : T → V
  embed_injective : Function.Injective embed
  middle : T → T → Finset V
  lower : ℕ
  lower_pos : 0 < lower
  lower_card : ∀ {a b}, F.Adj a b → lower ≤ (middle a b).card
  upper_card : ∀ {a b}, F.Adj a b → (middle a b).card ≤ 2 * lower
  adj_left : ∀ {a b y}, y ∈ middle a b → G.Adj (embed a) y
  adj_right : ∀ {a b y}, y ∈ middle a b → G.Adj y (embed b)
  middle_disjoint : ∀ {a b y}, y ∈ middle a b → ∀ t, y ≠ embed t

def cycleMiddleSets {F : SimpleGraph T} {G : SimpleGraph V}
    (L : LiftSystem F G) (x : Fin 28 → T) : Fin 28 → Finset V :=
  fun i ↦ L.middle (x i) (x (i + 1))

def cycleEmbeddedVertices {F : SimpleGraph T} {G : SimpleGraph V}
    (L : LiftSystem F G) (x : Fin 28 → T) : Finset V :=
  Finset.univ.image fun i ↦ L.embed (x i)

def liftsOfCycle {F : SimpleGraph T} {G : SimpleGraph V}
    (L : LiftSystem F G) (x : Fin 28 → T) : Finset (Fin 28 → V) :=
  validChoices (cycleMiddleSets L x) (cycleEmbeddedVertices L x)

def liftPairs (F : SimpleGraph T) (G : SimpleGraph V) (L : LiftSystem F G) :
    Finset ((x : Fin 28 → T) × (Fin 28 → V)) :=
  (genuineCycles F 28).sigma fun x ↦ liftsOfCycle L x

def liftedTuple {F : SimpleGraph T} {G : SimpleGraph V}
    (L : LiftSystem F G) (p : (x : Fin 28 → T) × (Fin 28 → V)) : Fin 56 → V :=
  alternatingTuple (L.embed ∘ p.1) p.2

def liftedCycles (F : SimpleGraph T) (G : SimpleGraph V) (L : LiftSystem F G) :
    Finset (Fin 56 → V) :=
  (liftPairs F G L).image (liftedTuple L)

@[simp] lemma mem_cycleEmbeddedVertices {F : SimpleGraph T} {G : SimpleGraph V}
    (L : LiftSystem F G) (x : Fin 28 → T) (v : V) :
    v ∈ cycleEmbeddedVertices L x ↔ ∃ i, L.embed (x i) = v := by
  simp [cycleEmbeddedVertices]

lemma cycleEmbeddedVertices_card_le {F : SimpleGraph T} {G : SimpleGraph V}
    (L : LiftSystem F G) (x : Fin 28 → T) :
    (cycleEmbeddedVertices L x).card ≤ 28 := by
  calc
    (cycleEmbeddedVertices L x).card ≤ (Finset.univ : Finset (Fin 28)).card := by
      exact Finset.card_image_le
    _ = 28 := by simp

@[simp] lemma mem_liftPairs {F : SimpleGraph T} {G : SimpleGraph V}
    (L : LiftSystem F G) {p : (x : Fin 28 → T) × (Fin 28 → V)} :
    p ∈ liftPairs F G L ↔
      IsGenuineCycle F p.1 ∧ p.2 ∈ liftsOfCycle L p.1 := by
  simp [liftPairs]

lemma liftedTuple_injective {F : SimpleGraph T} {G : SimpleGraph V}
    (L : LiftSystem F G) : Function.Injective (liftedTuple L) := by
  rintro ⟨x, y⟩ ⟨x', y'⟩ hpq
  have hpair : (L.embed ∘ x, y) = (L.embed ∘ x', y') :=
    alternatingTuple_pair_injective hpq
  have hx : x = x' := by
    funext i
    exact L.embed_injective (congrFun (congrArg Prod.fst hpair) i)
  subst x'
  have hy : y = y' := congrArg Prod.snd hpair
  subst y'
  rfl

lemma card_liftedCycles {F : SimpleGraph T} {G : SimpleGraph V}
    (L : LiftSystem F G) :
    (liftedCycles F G L).card = (liftPairs F G L).card := by
  exact Finset.card_image_of_injective _ (liftedTuple_injective L)

lemma liftsOfCycle_half_lower {F : SimpleGraph T} {G : SimpleGraph V}
    (L : LiftSystem F G) (hlarge : 3136 * 2 ^ 27 ≤ L.lower)
    {x : Fin 28 → T} (hx : IsGenuineCycle F x) :
    L.lower ^ 28 ≤ 2 * (liftsOfCycle L x).card := by
  apply validChoices_half_lower
  · intro i
    exact L.lower_card (hx.2 i)
  · intro i
    exact L.upper_card (hx.2 i)
  · exact cycleEmbeddedVertices_card_le L x
  · exact hlarge

theorem liftedCycles_card_lower {F : SimpleGraph T} {G : SimpleGraph V}
    (L : LiftSystem F G) (hlarge : 3136 * 2 ^ 27 ≤ L.lower) :
    (genuineCycles F 28).card * L.lower ^ 28 ≤
      2 * (liftedCycles F G L).card := by
  rw [card_liftedCycles, liftPairs, Finset.card_sigma]
  have hsum : ∑ x ∈ genuineCycles F 28, L.lower ^ 28 ≤
      ∑ x ∈ genuineCycles F 28, 2 * (liftsOfCycle L x).card := by
    exact Finset.sum_le_sum fun x hx ↦
      liftsOfCycle_half_lower L hlarge (mem_genuineCycles.mp hx)
  simpa [Finset.mul_sum, Finset.sum_mul] using hsum

lemma liftedTuple_genuine {F : SimpleGraph T} {G : SimpleGraph V}
    (L : LiftSystem F G) {p : (x : Fin 28 → T) × (Fin 28 → V)}
    (hp : p ∈ liftPairs F G L) :
    IsGenuineCycle G (liftedTuple L p) := by
  have hx := (mem_liftPairs L).mp hp
  have hy := mem_validChoices.mp hx.2
  apply alternatingTuple_genuine
  · exact L.embed_injective.comp hx.1.1
  · exact hy.2.1
  · intro i j heq
    exact hy.2.2 j ((mem_cycleEmbeddedVertices L p.1 (p.2 j)).mpr ⟨i, heq⟩)
  · intro i
    exact L.adj_left (hy.1 i)
  · intro i
    exact L.adj_right (hy.1 i)

theorem liftedCycles_genuine {F : SimpleGraph T} {G : SimpleGraph V}
    (L : LiftSystem F G) {z : Fin 56 → V}
    (hz : z ∈ liftedCycles F G L) : IsGenuineCycle G z := by
  rw [liftedCycles, Finset.mem_image] at hz
  obtain ⟨p, hp, rfl⟩ := hz
  exact liftedTuple_genuine L hp

abbrev OffSingle56 (i : Fin 56) := {j : Fin 56 // j ≠ i}

def restrictOffSingle56 (i : Fin 56) (z : Fin 56 → V) :
    OffSingle56 i → V := fun j ↦ z j

def singleFiber56 (C : Finset (Fin 56 → V)) (i : Fin 56)
    (r : OffSingle56 i → V) : Finset (Fin 56 → V) :=
  C.filter fun z ↦ restrictOffSingle56 i z = r

lemma eval_injective_on_singleFiber56 (C : Finset (Fin 56 → V))
    (i : Fin 56) (r : OffSingle56 i → V) :
    Set.InjOn (fun z : Fin 56 → V ↦ z i) (singleFiber56 C i r) := by
  intro z hz w hw hzi
  have hzrest := (Finset.mem_filter.mp hz).2
  have hwrest := (Finset.mem_filter.mp hw).2
  funext j
  by_cases hji : j = i
  · simpa [hji] using hzi
  · have h := congrFun (hzrest.trans hwrest.symm) ⟨j, hji⟩
    exact h

lemma value_eq_of_mem_singleFiber56 {C : Finset (Fin 56 → V)}
    {i : Fin 56} {r : OffSingle56 i → V} {z w : Fin 56 → V}
    (hz : z ∈ singleFiber56 C i r) (hw : w ∈ singleFiber56 C i r)
    {j : Fin 56} (hji : j ≠ i) : z j = w j := by
  have hzrest := (Finset.mem_filter.mp hz).2
  have hwrest := (Finset.mem_filter.mp hw).2
  exact congrFun (hzrest.trans hwrest.symm) ⟨j, hji⟩

lemma fin56_sub_one_ne (i : Fin 56) : i - 1 ≠ i := by
  decide +revert

lemma fin56_add_one_ne (i : Fin 56) : i + 1 ≠ i := by
  decide +revert

lemma fin56_sub_one_add_one (i : Fin 56) : i - 1 + 1 = i := by
  decide +revert

lemma evenIndex_ne_oddIndex (i j : Fin 28) : evenIndex i ≠ oddIndex j := by
  intro h
  have := congrArg Fin.val h
  simp [evenIndex, oddIndex] at this
  omega

/-- A missing even coordinate is controlled by the host vertices in the
embedded auxiliary part that join its two fixed neighboring middle
vertices. -/
def bridgeAnchors {F : SimpleGraph T} {G : SimpleGraph V}
    [DecidableRel G.Adj] (L : LiftSystem F G) (u w : V) : Finset T :=
  Finset.univ.filter fun t ↦ G.Adj u (L.embed t) ∧ G.Adj (L.embed t) w

def IsMiddleVertex {F : SimpleGraph T} {G : SimpleGraph V}
    (L : LiftSystem F G) (y : V) : Prop :=
  ∃ a b, y ∈ L.middle a b

@[simp] lemma mem_bridgeAnchors {F : SimpleGraph T} {G : SimpleGraph V}
    [DecidableRel G.Adj] (L : LiftSystem F G) {u w : V} {t : T} :
    t ∈ bridgeAnchors L u w ↔
      G.Adj u (L.embed t) ∧ G.Adj (L.embed t) w := by
  simp [bridgeAnchors]

lemma oddIndex_halfIndex_sub_one_of_even (i : Fin 56)
    (hi : i.val % 2 = 0) :
    oddIndex (halfIndex i - 1) = i - 1 := by
  revert i
  decide +revert

theorem singleFiber56_liftedCycles_card_le
    {F : SimpleGraph T} {G : SimpleGraph V} [DecidableRel G.Adj]
    (L : LiftSystem F G)
    (cap : ℕ) (hmiddle : 2 * L.lower ≤ cap)
    (hbridge : ∀ u w, IsMiddleVertex L u →
      (bridgeAnchors L u w).card ≤ cap)
    (i : Fin 56) (r : OffSingle56 i → V) :
    (singleFiber56 (liftedCycles F G L) i r).card ≤ cap := by
  let C := liftedCycles F G L
  let K := singleFiber56 C i r
  by_cases hK : K.Nonempty
  · obtain ⟨z₀, hz₀K⟩ := hK
    have hz₀C : z₀ ∈ C := (Finset.mem_filter.mp hz₀K).1
    change z₀ ∈ liftedCycles F G L at hz₀C
    rw [liftedCycles, Finset.mem_image] at hz₀C
    obtain ⟨p₀, hp₀, hp₀eq⟩ := hz₀C
    by_cases hi : i.val % 2 = 0
    · let B := bridgeAnchors L (z₀ (i - 1)) (z₀ (i + 1))
      let E : Finset V := B.image L.embed
      have hzprevMiddle : IsMiddleVertex L (z₀ (i - 1)) := by
        have hp₀data := (mem_liftPairs L).mp hp₀
        have hp₀choices := (mem_validChoices.mp hp₀data.2).1
        let j := halfIndex i
        let k : Fin 28 := j - 1
        have hrepr : oddIndex k = i - 1 := by
          simpa [k, j] using oddIndex_halfIndex_sub_one_of_even i hi
        have hval : z₀ (i - 1) = p₀.2 k := by
          rw [← hp₀eq, ← hrepr]
          simp [liftedTuple]
        refine ⟨p₀.1 k, p₀.1 (k + 1), ?_⟩
        rw [hval]
        simpa [cycleMiddleSets] using hp₀choices k
      calc
        K.card ≤ E.card := by
          apply Finset.card_le_card_of_injOn (fun z : Fin 56 → V ↦ z i)
          · intro z hzK
            have hzC : z ∈ C := (Finset.mem_filter.mp hzK).1
            change z ∈ liftedCycles F G L at hzC
            rw [liftedCycles, Finset.mem_image] at hzC
            obtain ⟨p, hp, rfl⟩ := hzC
            have hpgen := liftedTuple_genuine L hp
            have hprev : liftedTuple L p (i - 1) = z₀ (i - 1) :=
              value_eq_of_mem_singleFiber56 hzK hz₀K (fin56_sub_one_ne i)
            have hnext : liftedTuple L p (i + 1) = z₀ (i + 1) :=
              value_eq_of_mem_singleFiber56 hzK hz₀K (fin56_add_one_ne i)
            change liftedTuple L p i ∈ E
            simp only [E, Finset.mem_image]
            refine ⟨p.1 (halfIndex i), ?_, ?_⟩
            · rw [mem_bridgeAnchors]
              constructor
              · rw [← hprev]
                have h := hpgen.2 (i - 1)
                rw [fin56_sub_one_add_one] at h
                simpa [liftedTuple, alternatingTuple, hi] using h
              · rw [← hnext]
                have h := hpgen.2 i
                simpa [liftedTuple, alternatingTuple, hi] using h
            · simp [liftedTuple, alternatingTuple, hi]
          · exact eval_injective_on_singleFiber56 C i r
        _ ≤ B.card := Finset.card_image_le
        _ ≤ cap := hbridge _ _ hzprevMiddle
    · let j := halfIndex i
      let B := L.middle (p₀.1 j) (p₀.1 (j + 1))
      calc
        K.card ≤ B.card := by
          apply Finset.card_le_card_of_injOn (fun z : Fin 56 → V ↦ z i)
          · intro z hzK
            have hzC : z ∈ C := (Finset.mem_filter.mp hzK).1
            change z ∈ liftedCycles F G L at hzC
            rw [liftedCycles, Finset.mem_image] at hzC
            obtain ⟨p, hp, hpeq⟩ := hzC
            have hpdata := (mem_liftPairs L).mp hp
            have hpchoices := (mem_validChoices.mp hpdata.2).1
            have hrepr : oddIndex j = i := oddIndex_halfIndex_of_odd i hi
            have hleft : p.1 j = p₀.1 j := by
              apply L.embed_injective
              have hne : evenIndex j ≠ i := by
                rw [← hrepr]
                exact evenIndex_ne_oddIndex j j
              have hcoord := value_eq_of_mem_singleFiber56 hzK hz₀K
                hne
              rw [← hpeq, ← hp₀eq] at hcoord
              simpa [liftedTuple] using hcoord
            have hright : p.1 (j + 1) = p₀.1 (j + 1) := by
              apply L.embed_injective
              have hne : evenIndex (j + 1) ≠ i := by
                rw [← hrepr]
                exact evenIndex_ne_oddIndex (j + 1) j
              have hcoord := value_eq_of_mem_singleFiber56 hzK hz₀K
                hne
              rw [← hpeq, ← hp₀eq] at hcoord
              simpa [liftedTuple] using hcoord
            change z i ∈ B
            rw [← hpeq, ← hrepr]
            simpa [B, cycleMiddleSets, liftedTuple, hleft, hright] using hpchoices j
          · exact eval_injective_on_singleFiber56 C i r
        _ ≤ cap := by
          have hp₀gen := (mem_liftPairs L).mp hp₀
          exact (L.upper_card (hp₀gen.1.2 j)).trans hmiddle
  · simp only [Finset.not_nonempty_iff_eq_empty] at hK
    change K.card ≤ cap
    rw [hK]
    simp

end

end Erdos113ManyLifts
