import Mathlib.Data.Finset.Card
import Mathlib.Data.Set.Card
import Mathlib.Order.WellQuasiOrder
import Mathlib.SetTheory.Cardinal.Pigeonhole

/-!
# Erdős Problem 603

There is no uniform cardinal bound on the number of colours needed in the
problem.  The detailed mathematical proof and Leanization plan are in
`tex/603.tex`.
-/

open Set Function Cardinal Ordinal

universe u

namespace Erdos603

variable {α : Type u} [LinearOrder α] [WellFoundedLT α]
variable {κ : Type u}

noncomputable def erPred (c : α → α → κ) : α → Set α :=
  WellFounded.fix wellFounded_lt fun x ih =>
    {y | ∃ _h : y < x, ∀ z ∈ ih y _h, c z y = c z x}

theorem mem_erPred_iff (c : α → α → κ) {x y : α} :
    y ∈ erPred c x ↔ ∃ _h : y < x, ∀ z ∈ erPred c y, c z y = c z x := by
  rw [erPred, WellFounded.fix_eq]
  rfl

theorem erPred_lt (c : α → α → κ) {x y : α} (h : y ∈ erPred c x) : y < x :=
  (mem_erPred_iff c).1 h |>.choose

theorem erPred_compat (c : α → α → κ) {x y : α} (hy : y ∈ erPred c x)
    {z : α} (hz : z ∈ erPred c y) : c z y = c z x :=
  (mem_erPred_iff c).1 hy |>.choose_spec z hz

theorem erPred_trans (c : α → α → κ) {x y z : α}
    (hzy : z ∈ erPred c y) (hyx : y ∈ erPred c x) : z ∈ erPred c x := by
  refine wellFounded_lt.induction x
    (C := fun x => ∀ {y z}, z ∈ erPred c y → y ∈ erPred c x → z ∈ erPred c x)
    ?_ hzy hyx
  intro x ih y z hzy hyx
  rw [mem_erPred_iff]
  refine ⟨(erPred_lt c hzy).trans (erPred_lt c hyx), ?_⟩
  intro w hwz
  have hwy : w ∈ erPred c y := ih y (erPred_lt c hyx) hwz hzy
  calc
    c w z = c w y := erPred_compat c hzy hwz
    _ = c w x := erPred_compat c hyx hwy

theorem erPred_chain (c : α → α → κ) {x a b : α}
    (ha : a ∈ erPred c x) (hb : b ∈ erPred c x) (hab : a < b) :
    a ∈ erPred c b := by
  refine wellFounded_lt.induction a
    (C := fun a => ∀ {x b}, a ∈ erPred c x → b ∈ erPred c x → a < b → a ∈ erPred c b)
    ?_ ha hb hab
  intro a ih x b ha hb hab
  rw [mem_erPred_iff]
  refine ⟨hab, ?_⟩
  intro z hza
  have hzx : z ∈ erPred c x := erPred_trans c hza ha
  have hzb : z ∈ erPred c b :=
    ih z (erPred_lt c hza) hzx hb ((erPred_lt c hza).trans hab)
  calc
    c z a = c z x := erPred_compat c ha hza
    _ = c z b := (erPred_compat c hb hzb).symm

theorem erPred_eq (c : α → α → κ) {x y : α} (hy : y ∈ erPred c x) :
    erPred c y = erPred c x ∩ Set.Iio y := by
  ext z
  constructor
  · intro hz
    exact ⟨erPred_trans c hz hy, erPred_lt c hz⟩
  · rintro ⟨hzx, hzy⟩
    exact erPred_chain c hzx hy hzy

noncomputable def erRank (c : α → α → κ) (x : α) : Ordinal :=
  Ordinal.type ((· < ·) : erPred c x → erPred c x → Prop)

def erPredRelIso (c : α → α → κ) {x y : α} (hy : y ∈ erPred c x) :
    ((· < ·) : erPred c y → erPred c y → Prop) ≃r
      ((· < ·) : Set.Iio (⟨y, hy⟩ : erPred c x) →
        Set.Iio (⟨y, hy⟩ : erPred c x) → Prop) where
  toFun z := ⟨⟨z, erPred_trans c z.property hy⟩, erPred_lt c z.property⟩
  invFun z := ⟨z.1.1, by rw [erPred_eq c hy]; exact ⟨z.1.2, z.2⟩⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_rel_iff' := by intro _ _; rfl

theorem erRank_eq_typein (c : α → α → κ) {x y : α} (hy : y ∈ erPred c x) :
    erRank c y = Ordinal.typein ((· < ·) : erPred c x → erPred c x → Prop) ⟨y, hy⟩ := by
  rw [erRank, (erPredRelIso c hy).ordinalType_congr, Ordinal.type_Iio_lt]

noncomputable def erAncestor (c : α → α → κ) (x : α) (i : Set.Iio (erRank c x)) : α :=
  (Ordinal.enum ((· < ·) : erPred c x → erPred c x → Prop) i).1

theorem erAncestor_mem (c : α → α → κ) (x : α) (i : Set.Iio (erRank c x)) :
    erAncestor c x i ∈ erPred c x :=
  (Ordinal.enum ((· < ·) : erPred c x → erPred c x → Prop) i).2

theorem erAncestor_rank (c : α → α → κ) (x : α) (i : Set.Iio (erRank c x)) :
    erRank c (erAncestor c x i) = i := by
  rw [erRank_eq_typein c (erAncestor_mem c x i)]
  exact Ordinal.typein_enum _ i.2

theorem erAncestor_lt (c : α → α → κ) (x : α)
    {i j : Set.Iio (erRank c x)} (hij : i < j) :
    erAncestor c x i < erAncestor c x j := by
  exact (Ordinal.enum_lt_enum (r := ((· < ·) : erPred c x → erPred c x → Prop))).2 hij

theorem erAncestor_mem_ancestor (c : α → α → κ) (x : α)
    {i j : Set.Iio (erRank c x)} (hij : i < j) :
    erAncestor c x i ∈ erPred c (erAncestor c x j) :=
  erPred_chain c (erAncestor_mem c x i) (erAncestor_mem c x j) (erAncestor_lt c x hij)

theorem erRank_lt (c : α → α → κ) {x y : α} (hy : y ∈ erPred c x) :
    erRank c y < erRank c x := by
  rw [erRank_eq_typein c hy]
  exact Ordinal.typein_lt_type _ _

theorem erRank_inj_of_mem (c : α → α → κ) {x a b : α}
    (ha : a ∈ erPred c x) (hb : b ∈ erPred c x) (hrank : erRank c a = erRank c b) : a = b := by
  rcases lt_trichotomy a b with hab | hab | hab
  · have hmem : a ∈ erPred c b := erPred_chain c ha hb hab
    exact ((erRank_lt c hmem).ne hrank).elim
  · exact hab
  · have hmem : b ∈ erPred c a := erPred_chain c hb ha hab
    exact ((erRank_lt c hmem).ne hrank.symm).elim

theorem erAncestor_self (c : α → α → κ) {x y : α} (hy : y ∈ erPred c x) :
    erAncestor c x ⟨erRank c y, erRank_lt c hy⟩ = y := by
  apply erRank_inj_of_mem c (erAncestor_mem c x _) hy
  exact erAncestor_rank c x _

def erLiftIndex (c : α → α → κ) {x y : α} (hy : y ∈ erPred c x)
    (i : Set.Iio (erRank c y)) : Set.Iio (erRank c x) :=
  ⟨i, i.2.trans (erRank_lt c hy)⟩

theorem erAncestor_of_pred (c : α → α → κ) {x y : α} (hy : y ∈ erPred c x)
    (i : Set.Iio (erRank c y)) :
    erAncestor c x (erLiftIndex c hy i) = erAncestor c y i := by
  have hmem : erAncestor c y i ∈ erPred c x :=
    erPred_trans c (erAncestor_mem c y i) hy
  have hself := erAncestor_self c hmem
  have hi :
      (⟨erRank c (erAncestor c y i), erRank_lt c hmem⟩ : Set.Iio (erRank c x)) =
        erLiftIndex c hy i := by
    apply Subtype.ext
    exact erAncestor_rank c y i
  rw [hi] at hself
  exact hself

noncomputable def erCode (c : α → α → κ) (x : α) : Set.Iio (erRank c x) → κ :=
  fun i => c (erAncestor c x i) x

theorem erCode_of_pred (c : α → α → κ) {x y : α} (hy : y ∈ erPred c x)
    (i : Set.Iio (erRank c y)) :
    erCode c y i = erCode c x (erLiftIndex c hy i) := by
  unfold erCode
  rw [erAncestor_of_pred c hy i]
  exact erPred_compat c hy (erAncestor_mem c y i)

def erLevel (c : α → α → κ) (σ : Ordinal) := {x : α // erRank c x = σ}

def erLevelIndex (c : α → α → κ) {σ : Ordinal} (x : erLevel c σ)
    (i : Set.Iio σ) : Set.Iio (erRank c x.1) :=
  ⟨i, by rw [x.2]; exact i.2⟩

noncomputable def erLevelCode (c : α → α → κ) (σ : Ordinal) :
    erLevel c σ → (Set.Iio σ → κ) :=
  fun x i => erCode c x.1 (erLevelIndex c x i)

theorem erLevel_ancestor_self (c : α → α → κ) {σ : Ordinal}
    (x : erLevel c σ) {z : α} (hz : z ∈ erPred c x.1) :
    erAncestor c x.1
      (erLevelIndex c x ⟨erRank c z, by rw [← x.2]; exact erRank_lt c hz⟩) = z := by
  apply erRank_inj_of_mem c (erAncestor_mem c x.1 _) hz
  exact erAncestor_rank c x.1 _

theorem erLevel_ancestor_of_rank (c : α → α → κ) {σ τ : Ordinal}
    (x : erLevel c σ) {z : α} (hz : z ∈ erPred c x.1) (hrank : erRank c z = τ)
    (hτ : τ < σ) :
    erAncestor c x.1 (erLevelIndex c x ⟨τ, hτ⟩) = z := by
  apply erRank_inj_of_mem c (erAncestor_mem c x.1 _) hz
  exact (erAncestor_rank c x.1 _).trans hrank.symm

theorem erLevelCode_injective (c : α → α → κ) (σ : Ordinal) :
    Function.Injective (erLevelCode c σ) := by
  refine WellFoundedLT.induction (motive := fun τ => Function.Injective (erLevelCode c τ)) σ ?_
  intro σ ih x y hcode
  apply Subtype.ext
  rcases lt_trichotomy x.1 y.1 with hxy | hxy | hyx
  · exfalso
    have hpred : x.1 ∈ erPred c y.1 := by
      rw [mem_erPred_iff]
      refine ⟨hxy, ?_⟩
      intro z hz
      let τ := erRank c z
      have hτσ : τ < σ := by
        rw [← x.2]
        exact erRank_lt c hz
      let w := erAncestor c y.1 ⟨τ, by rw [y.2]; exact hτσ⟩
      have hw : w ∈ erPred c y.1 := erAncestor_mem c y.1 _
      have hwrank : erRank c w = τ := erAncestor_rank c y.1 _
      have hzw : z = w := by
        have hlev : (⟨z, rfl⟩ : erLevel c τ) = ⟨w, hwrank⟩ := by
          apply ih τ hτσ
          apply funext
          intro i
          let iσ : Set.Iio σ := ⟨i, i.2.trans hτσ⟩
          let iw : Set.Iio (erRank c w) := ⟨i, by rw [hwrank]; exact i.2⟩
          calc
            erLevelCode c τ ⟨z, rfl⟩ i = erCode c z i := by rfl
            _ = erCode c x.1 (erLiftIndex c hz i) := erCode_of_pred c hz i
            _ = erLevelCode c σ x iσ := by
              apply congrArg (erCode c x.1)
              apply Subtype.ext
              rfl
            _ = erLevelCode c σ y iσ := congrFun hcode iσ
            _ = erCode c y.1 (erLiftIndex c hw iw) := by
              apply congrArg (erCode c y.1)
              apply Subtype.ext
              rfl
            _ = erCode c w iw := (erCode_of_pred c hw iw).symm
            _ = erLevelCode c τ ⟨w, hwrank⟩ i := by
              apply congrArg (erCode c w)
              apply Subtype.ext
              rfl
        exact congrArg Subtype.val hlev
      subst w
      let iσ : Set.Iio σ := ⟨τ, hτσ⟩
      calc
        c z x.1 = erLevelCode c σ x iσ := by
          unfold erLevelCode erCode
          rw [erLevel_ancestor_self c x hz]
        _ = erLevelCode c σ y iσ := congrFun hcode iσ
        _ = c z y.1 := by
          unfold erLevelCode erCode
          rw [erLevel_ancestor_of_rank c y hw hwrank hτσ]
          exact congrArg (fun q => c q y.1) hzw.symm
    have hrank := erRank_lt c hpred
    rw [x.2, y.2] at hrank
    exact hrank.false
  · exact hxy
  · exfalso
    have hfalse : False := by
      have hpred : y.1 ∈ erPred c x.1 := by
        rw [mem_erPred_iff]
        refine ⟨hyx, ?_⟩
        intro z hz
        let τ := erRank c z
        have hτσ : τ < σ := by rw [← y.2]; exact erRank_lt c hz
        let w := erAncestor c x.1 ⟨τ, by rw [x.2]; exact hτσ⟩
        have hw : w ∈ erPred c x.1 := erAncestor_mem c x.1 _
        have hwrank : erRank c w = τ := erAncestor_rank c x.1 _
        have hzw : z = w := by
          have hlev : (⟨z, rfl⟩ : erLevel c τ) = ⟨w, hwrank⟩ := by
            apply ih τ hτσ
            apply funext
            intro i
            let iσ : Set.Iio σ := ⟨i, i.2.trans hτσ⟩
            let iw : Set.Iio (erRank c w) := ⟨i, by rw [hwrank]; exact i.2⟩
            calc
              erLevelCode c τ ⟨z, rfl⟩ i = erCode c z i := by rfl
              _ = erCode c y.1 (erLiftIndex c hz i) := erCode_of_pred c hz i
              _ = erLevelCode c σ y iσ := by
                apply congrArg (erCode c y.1); apply Subtype.ext; rfl
              _ = erLevelCode c σ x iσ := congrFun hcode.symm iσ
              _ = erCode c x.1 (erLiftIndex c hw iw) := by
                apply congrArg (erCode c x.1); apply Subtype.ext; rfl
              _ = erCode c w iw := (erCode_of_pred c hw iw).symm
              _ = erLevelCode c τ ⟨w, hwrank⟩ i := by
                apply congrArg (erCode c w); apply Subtype.ext; rfl
          exact congrArg Subtype.val hlev
        subst w
        let iσ : Set.Iio σ := ⟨τ, hτσ⟩
        calc
          c z y.1 = erLevelCode c σ y iσ := by
            unfold erLevelCode erCode
            rw [erLevel_ancestor_self c y hz]
          _ = erLevelCode c σ x iσ := congrFun hcode.symm iσ
          _ = c z x.1 := by
            unfold erLevelCode erCode
            rw [erLevel_ancestor_of_rank c x hw hwrank hτσ]
            exact congrArg (fun q => c q x.1) hzw.symm
      have hrank := erRank_lt c hpred
      rw [y.2, x.2] at hrank
      exact hrank.false
    exact hfalse

def erPaddedSpace (κ : Type u) (T : Cardinal.{u}) :=
  Set.Iio T.ord × (Set.Iio T.ord → Option κ)

noncomputable def erPaddedCode (c : α → α → κ) (T : Cardinal.{u})
    (_h : ∀ x, erRank c x < T.ord) (x : α) : Set.Iio T.ord → Option κ :=
  fun i => if hi : i.1 < erRank c x then some (erCode c x ⟨i.1, hi⟩) else none

noncomputable def erPaddedProfile (c : α → α → κ) (T : Cardinal.{u})
    (h : ∀ x, erRank c x < T.ord) (x : α) : erPaddedSpace κ T :=
  (⟨erRank c x, h x⟩, erPaddedCode c T h x)

theorem erPaddedProfile_injective (c : α → α → κ) (T : Cardinal.{u})
    (h : ∀ x, erRank c x < T.ord) : Function.Injective (erPaddedProfile c T h) := by
  intro x y hxy
  have hrank : erRank c x = erRank c y :=
    congrArg (fun q : erPaddedSpace κ T => q.1.1) hxy
  have hcode : erPaddedCode c T h x = erPaddedCode c T h y := congrArg Prod.snd hxy
  let xl : erLevel c (erRank c x) := ⟨x, rfl⟩
  let yl : erLevel c (erRank c x) := ⟨y, hrank.symm⟩
  have hlevel : erLevelCode c (erRank c x) xl = erLevelCode c (erRank c x) yl := by
    apply funext
    intro i
    let j : Set.Iio T.ord := ⟨i.1, i.2.trans (h x)⟩
    have hj := congrFun hcode j
    unfold erPaddedCode at hj
    have hyi : i.1 < erRank c y := hrank ▸ i.2
    change (if hi : i.1 < erRank c x then some (erCode c x ⟨i.1, hi⟩) else none) =
      (if hi : i.1 < erRank c y then some (erCode c y ⟨i.1, hi⟩) else none) at hj
    rw [dif_pos (show i.1 < erRank c x from i.2), dif_pos hyi] at hj
    have hv := Option.some.inj hj
    change erCode c x (erLevelIndex c xl i) = erCode c y (erLevelIndex c yl i)
    simpa [erLevelIndex, xl, yl] using hv
  exact congrArg Subtype.val (erLevelCode_injective c _ hlevel)

theorem mk_erPaddedSpace (κ : Type u) (T : Cardinal.{u}) :
    #(erPaddedSpace κ T) = Cardinal.lift.{u + 1, u} (T * (#(Option κ) ^ T)) := by
  rw [erPaddedSpace, Cardinal.mk_prod, Cardinal.mk_arrow,
    Cardinal.mk_Iio_ordinal, Cardinal.card_ord]
  rw [Cardinal.lift_id'.{u, u + 1}, Cardinal.lift_id, ← Cardinal.lift_power]
  rw [Cardinal.lift_id]
  rw [← Cardinal.lift_mul]

noncomputable def erVertexCard (κ : Type u) (T : Cardinal.{u}) : Cardinal.{u} :=
  Order.succ (T * (#(Option κ) ^ T))

abbrev erVertex (κ : Type u) (T : Cardinal.{u}) := (erVertexCard κ T).ord.ToType

theorem exists_erRank_ge (κ : Type u) (T : Cardinal.{u})
    (c : erVertex κ T → erVertex κ T → κ) :
    ∃ x, T.ord ≤ erRank c x := by
  by_contra h
  push Not at h
  have hinj := erPaddedProfile_injective c T h
  have hmk : Cardinal.lift.{u + 1, u} #(erVertex κ T) ≤
      Cardinal.lift.{u, u + 1} #(erPaddedSpace κ T) := by
    apply Cardinal.lift_mk_le'.2
    exact ⟨⟨erPaddedProfile c T h, hinj⟩⟩
  rw [erVertex, Cardinal.mk_toType, Cardinal.card_ord, mk_erPaddedSpace,
    Cardinal.lift_id'.{u, u + 1}] at hmk
  have hle : erVertexCard κ T ≤ T * (#(Option κ) ^ T) := Cardinal.lift_le.mp hmk
  exact (not_lt_of_ge hle) (Order.lt_succ _)

theorem erAncestor_injective (c : α → α → κ) (x : α) :
    Function.Injective (erAncestor c x) := by
  intro i j hij
  apply Subtype.ext
  have h := congrArg (erRank c) hij
  simpa [erAncestor_rank c x i, erAncestor_rank c x j] using h

theorem ramification_homogeneous (κ : Type u) (T : Cardinal.{u})
    (hκ : #κ < T) (hT : (ℵ₀ : Cardinal.{u}) ≤ T)
    (c : erVertex κ T → erVertex κ T → κ) :
    ∃ (g : ℕ ↪ erVertex κ T) (k : κ), ∀ m n, m < n → c (g m) (g n) = k := by
  obtain ⟨x, hx⟩ := exists_erRank_ge κ T c
  let branchIndex : Set.Iio T.ord → Set.Iio (erRank c x) :=
    fun i => ⟨i.1, i.2.trans_le hx⟩
  let branchColor : Set.Iio T.ord → ULift.{u + 1, u} κ :=
    fun i => ULift.up (erCode c x (branchIndex i))
  have htLift : Cardinal.lift.{u + 1, u} (ℵ₀ : Cardinal.{u}) ≤
      Cardinal.lift.{u + 1, u} T := Cardinal.lift_le.2 hT
  letI : Infinite (Set.Iio T.ord) := Cardinal.infinite_iff.2 (by
    rw [Cardinal.mk_Iio_ordinal, Cardinal.card_ord]
    simpa using htLift)
  have hsmall : Cardinal.lift.{u + 1, u} #κ < #(Set.Iio T.ord) := by
    rw [Cardinal.mk_Iio_ordinal, Cardinal.card_ord]
    exact Cardinal.lift_lt.2 hκ
  obtain ⟨k, hk⟩ := Cardinal.exists_infinite_fiber branchColor (by simpa using hsmall)
  let raw : ℕ ↪ (branchColor ⁻¹' {k}) := Infinite.natEmbedding _
  obtain ⟨s, hs⟩ := wellQuasiOrdered_le.exists_monotone_subseq
    (fun n => (raw n).1 : ℕ → Set.Iio T.ord)
  let q : ℕ → Set.Iio T.ord := fun n => (raw (s n)).1
  have hq : StrictMono q := by
    intro m n hmn
    have hle := hs m n hmn.le
    exact hle.lt_of_ne (fun heq => hmn.ne (s.injective (raw.injective (Subtype.ext heq))))
  let qEmb : ℕ ↪o Set.Iio T.ord := OrderEmbedding.ofStrictMono q hq
  let g : ℕ ↪ erVertex κ T :=
    ⟨fun n => erAncestor c x (branchIndex (qEmb n)),
      (erAncestor_injective c x).comp (fun a b hij => by
        apply qEmb.injective
        apply Subtype.ext
        exact congrArg (fun z : Set.Iio (erRank c x) => z.1) hij)⟩
  refine ⟨g, k.down, ?_⟩
  intro m n hmn
  have hindex : branchIndex (qEmb m) < branchIndex (qEmb n) := hq hmn
  have hmnPred : erAncestor c x (branchIndex (qEmb m)) ∈
      erPred c (erAncestor c x (branchIndex (qEmb n))) :=
    erAncestor_mem_ancestor c x hindex
  have hnPred : erAncestor c x (branchIndex (qEmb n)) ∈ erPred c x :=
    erAncestor_mem c x _
  change c (erAncestor c x (branchIndex (qEmb m)))
    (erAncestor c x (branchIndex (qEmb n))) = k.down
  calc
    c (erAncestor c x (branchIndex (qEmb m)))
        (erAncestor c x (branchIndex (qEmb n))) =
        c (erAncestor c x (branchIndex (qEmb m))) x :=
      erPred_compat c hnPred hmnPred
    _ = (branchColor (qEmb m)).down := rfl
    _ = k.down := congrArg ULift.down (raw (s m)).2

theorem erdosRado_omega (κ : Type u) :
    let K : Cardinal.{u} := max #κ ℵ₀
    let T := Order.succ K
    ∀ c : erVertex κ T → erVertex κ T → κ,
      ∃ (g : ℕ ↪ erVertex κ T) (k : κ), ∀ m n, m < n → c (g m) (g n) = k := by
  dsimp
  apply ramification_homogeneous
  · exact (le_max_left _ _).trans_lt (Order.lt_succ _)
  · exact (le_max_right _ _).trans (Order.le_succ _)

theorem erVertex_infinite (κ : Type u) (T : Cardinal.{u})
    (hT : (ℵ₀ : Cardinal.{u}) ≤ T) : Infinite (erVertex κ T) := by
  rw [Cardinal.infinite_iff, Cardinal.mk_toType, Cardinal.card_ord]
  unfold erVertexCard
  have hbase : #(Option κ) ≠ 0 := Cardinal.mk_ne_zero_iff.2 inferInstance
  have hpow : 1 ≤ #(Option κ) ^ T :=
    Cardinal.one_le_iff_ne_zero.2 (Cardinal.power_ne_zero T hbase)
  have hmul : T ≤ T * (#(Option κ) ^ T) := by
    simpa [mul_comm] using mul_le_mul_left hpow T
  exact hT.trans (hmul.trans (Order.le_succ _))

def GraphEdge (V : Type u) := {e : Finset V // e.card = 2}

def completeGraph {V : Type u} (S : Set V) : Set (GraphEdge V) :=
  {e | (e.1 : Set V) ⊆ S}

theorem completeGraph_encard_ne_two {V : Type u} (S : Set V) :
    (completeGraph S).encard ≠ 2 := by
  classical
  intro hcard
  obtain ⟨e₁, e₂, hne, heq⟩ := Set.encard_eq_two.mp hcard
  have he₁ : e₁ ∈ completeGraph S := by rw [heq]; simp
  have he₂ : e₂ ∈ completeGraph S := by rw [heq]; simp
  have hnsub₁ : ¬ e₁.1 ⊆ e₂.1 := by
    intro hsub
    apply hne
    apply Subtype.ext
    exact Finset.eq_of_subset_of_card_le hsub (by rw [e₁.2, e₂.2])
  have hnsub₂ : ¬ e₂.1 ⊆ e₁.1 := by
    intro hsub
    apply hne.symm
    apply Subtype.ext
    exact Finset.eq_of_subset_of_card_le hsub (by rw [e₁.2, e₂.2])
  simp only [Finset.not_subset] at hnsub₁ hnsub₂
  obtain ⟨x, hx₁, hx₂⟩ := hnsub₁
  obtain ⟨y, hy₂, hy₁⟩ := hnsub₂
  have hxy : x ≠ y := by
    intro h
    subst y
    exact hx₂ hy₂
  let d : GraphEdge V := ⟨{x, y}, Finset.card_pair hxy⟩
  have hd : d ∈ completeGraph S := by
    intro z hz
    have hz' : z = x ∨ z = y := by simpa [d] using hz
    rcases hz' with rfl | rfl
    · exact he₁ hx₁
    · exact he₂ hy₂
  have hd₁ : d ≠ e₁ := by
    intro h
    have hy : y ∈ d.1 := by simp [d]
    rw [h] at hy
    exact hy₁ hy
  have hd₂ : d ≠ e₂ := by
    intro h
    have hx : x ∈ d.1 := by simp [d]
    rw [h] at hx
    exact hx₂ hx
  rw [heq] at hd
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hd
  exact hd.elim hd₁ hd₂

theorem completeGraph_range_countable {V : Type u} (f : ℕ ↪ V) :
    (completeGraph (Set.range f)).Countable := by
  classical
  let edgeMap : {p : ℕ × ℕ // p.1 ≠ p.2} → GraphEdge V :=
    fun p => ⟨{f p.1.1, f p.1.2}, Finset.card_pair (fun h => p.2 (f.injective h))⟩
  refine (Set.countable_range edgeMap).mono ?_
  intro e he
  obtain ⟨x, y, hxy, heq⟩ := Finset.card_eq_two.mp e.2
  have hxmem : x ∈ e.1 := by rw [heq]; simp
  have hymem : y ∈ e.1 := by rw [heq]; simp
  obtain ⟨m, hm⟩ := he hxmem
  obtain ⟨n, hn⟩ := he hymem
  let p : {p : ℕ × ℕ // p.1 ≠ p.2} :=
    ⟨(m, n), fun hmn => hxy (hm.symm.trans ((congrArg f hmn).trans hn))⟩
  refine ⟨p, ?_⟩
  apply Subtype.ext
  change {f m, f n} = e.1
  rw [hm, hn]
  exact heq.symm

noncomputable def natEdge {V : Type u} (f : ℕ ↪ V) (n : ℕ) : GraphEdge V := by
  classical
  refine ⟨{f (2 * n), f (2 * n + 1)}, Finset.card_pair ?_⟩
  intro h
  have := f.injective h
  omega

theorem mem_natEdge {V : Type u} (f : ℕ ↪ V) (n : ℕ) (z : V) :
    z ∈ (natEdge f n).1 ↔ z = f (2 * n) ∨ z = f (2 * n + 1) := by
  classical
  simp [natEdge]

theorem natEdge_injective {V : Type u} (f : ℕ ↪ V) : Function.Injective (natEdge f) := by
  intro m n hmn
  have hm : f (2 * m) ∈ (natEdge f n).1 := by
    have hm' : f (2 * m) ∈ (natEdge f m).1 := (mem_natEdge f m _).2 (Or.inl rfl)
    rwa [hmn] at hm'
  rw [mem_natEdge] at hm
  rcases hm with hm | hm
  · have := f.injective hm
    omega
  · have := f.injective hm
    omega

theorem completeGraph_range_infinite {V : Type u} (f : ℕ ↪ V) :
    (completeGraph (Set.range f)).Infinite := by
  apply Set.infinite_of_injective_forall_mem (natEdge_injective f)
  intro n z hz
  have hz' : z ∈ (natEdge f n).1 := hz
  rw [mem_natEdge] at hz'
  rcases hz' with rfl | rfl
  · exact ⟨2 * n, rfl⟩
  · exact ⟨2 * n + 1, rfl⟩

theorem completeGraph_inter {V : Type u} (S T : Set V) :
    completeGraph S ∩ completeGraph T = completeGraph (S ∩ T) := by
  ext e
  simp only [completeGraph, Set.mem_inter_iff, Set.mem_ofPred_eq]
  exact Set.subset_inter_iff.symm

noncomputable abbrev colorBound (Color : Type u) : Cardinal.{u} := max #Color ℵ₀

noncomputable abbrev colorBranchCard (Color : Type u) : Cardinal.{u} :=
  Order.succ (colorBound Color)

abbrev ColorVertex (Color : Type u) := erVertex Color (colorBranchCard Color)

abbrev ColorEdge (Color : Type u) := GraphEdge (ColorVertex Color)

abbrev ColorIndex (Color : Type u) := ℕ ↪ ColorVertex Color

def cliqueFamily (Color : Type u) (f : ColorIndex Color) : Set (ColorEdge Color) :=
  completeGraph (Set.range f)

theorem colorBranchCard_aleph0_le (Color : Type u) :
    (ℵ₀ : Cardinal.{u}) ≤ colorBranchCard Color :=
  (le_max_right _ _).trans (Order.le_succ _)

theorem graph_ramsey (Color : Type u) (color : ColorEdge Color → Color) :
    ∃ (g : ColorIndex Color) (k : Color),
      ∀ e ∈ cliqueFamily Color g, color e = k := by
  letI : Infinite (ColorVertex Color) :=
    erVertex_infinite Color (colorBranchCard Color) (colorBranchCard_aleph0_le Color)
  let f₀ : ℕ ↪ ColorVertex Color := Infinite.natEmbedding _
  let defaultColor : Color := color (natEdge f₀ 0)
  let c : ColorVertex Color → ColorVertex Color → Color := fun a b =>
    if h : a ≠ b then color ⟨{a, b}, Finset.card_pair h⟩ else defaultColor
  obtain ⟨g, k, hg⟩ := erdosRado_omega Color c
  refine ⟨g, k, ?_⟩
  intro e he
  obtain ⟨x, y, hxy, heq⟩ := Finset.card_eq_two.mp e.2
  have hxmem : x ∈ e.1 := by rw [heq]; simp
  have hymem : y ∈ e.1 := by rw [heq]; simp
  obtain ⟨m, hm⟩ := he hxmem
  obtain ⟨n, hn⟩ := he hymem
  have hmn : m ≠ n := by
    intro h
    apply hxy
    exact hm.symm.trans ((congrArg g h).trans hn)
  have hgmn : g m ≠ g n := fun h => hmn (g.injective h)
  rcases lt_or_gt_of_ne hmn with hlt | hgt
  · calc
      color e = color (⟨{g m, g n}, Finset.card_pair hgmn⟩ : ColorEdge Color) := by
        apply congrArg color
        apply Subtype.ext
        change e.1 = {g m, g n}
        rw [hm, hn]
        exact heq
      _ = c (g m) (g n) := by
        unfold c
        rw [dif_pos hgmn]
      _ = k := hg m n hlt
  · have hnm : n ≠ m := hmn.symm
    calc
      color e = color (⟨{g n, g m}, Finset.card_pair hgmn.symm⟩ : ColorEdge Color) := by
        apply congrArg color
        apply Subtype.ext
        change e.1 = {g n, g m}
        rw [hm, hn]
        simpa [Finset.pair_comm] using heq
      _ = c (g n) (g m) := by
        unfold c
        rw [dif_pos hgmn.symm]
      _ = k := hg n m hgt

def IsErdos603Family {I X : Type u} (A : I → Set X) : Prop :=
  (∀ i, (A i).Countable ∧ (A i).Infinite) ∧
    ∀ i j, i ≠ j → (A i ∩ A j).encard ≠ 2

def UnionHasMonochromaticMember {I X : Type u} (A : I → Set X) (Color : Type u) : Prop :=
  ∀ coloring : (⋃ i, A i) → Color,
    ∃ (i : I) (k : Color), ∀ x (hx : x ∈ A i),
      coloring ⟨x, Set.mem_iUnion.2 ⟨i, hx⟩⟩ = k

/-- Erdős Problem 603 has no uniform cardinal bound: for every cardinal of colors there is a
family of countably infinite sets, with no pair intersecting in exactly two points, for which
every coloring of the union has a monochromatic member. -/
theorem erdos_603 (C : Cardinal.{u}) :
    ∃ (I X : Type u) (A : I → Set X),
      IsErdos603Family A ∧ UnionHasMonochromaticMember A C.out := by
  classical
  let Color := C.out
  let I := ColorIndex Color
  let X := ColorEdge Color
  let A : I → Set X := cliqueFamily Color
  refine ⟨I, X, A, ?_, ?_⟩
  · constructor
    · intro f
      exact ⟨completeGraph_range_countable f, completeGraph_range_infinite f⟩
    · intro f g _hfg
      change (completeGraph (Set.range f) ∩ completeGraph (Set.range g)).encard ≠ 2
      rw [completeGraph_inter]
      exact completeGraph_encard_ne_two _
  · intro coloring
    letI : Infinite (ColorVertex Color) :=
      erVertex_infinite Color (colorBranchCard Color) (colorBranchCard_aleph0_le Color)
    let f₀ : I := Infinite.natEmbedding _
    obtain ⟨e₀, he₀⟩ := (completeGraph_range_infinite f₀).nonempty
    have he₀U : e₀ ∈ ⋃ i, A i := Set.mem_iUnion.2 ⟨f₀, he₀⟩
    let defaultColor : Color := coloring ⟨e₀, he₀U⟩
    let edgeColor : X → Color := fun e =>
      if h : e ∈ ⋃ i, A i then coloring ⟨e, h⟩ else defaultColor
    obtain ⟨g, k, hg⟩ := graph_ramsey Color edgeColor
    refine ⟨g, k, ?_⟩
    intro e he
    have heU : e ∈ ⋃ i, A i := Set.mem_iUnion.2 ⟨g, he⟩
    have hmono := hg e he
    unfold edgeColor at hmono
    rw [dif_pos heU] at hmono
    exact hmono

end Erdos603

#print axioms Erdos603.erdos_603
