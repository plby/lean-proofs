-- Modified for this repository: Lean 4.33.0 port and Erdos1177 namespace.
import ErdosProblems.Erdos1177.ReservoirSetup

set_option relaxedAutoImplicit true
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# The §6 reservoir recursion: lower bound

This file proves the chromatic lower bound `χ(L_κ) ≥ κ` of the §6 construction
(`lem:reservoir-capture` and `lem:calibration-lower`): no colouring of `L_κ`
with fewer than `κ = μ⁺` colours is proper.
-/

open Cardinal Ordinal

set_option maxHeartbeats 4000000

namespace Erdos1177

universe u

namespace CalibData

variable {μ : Cardinal.{u}} (D : CalibData μ)

/-! ### Helper lemmas for reservoir capture -/

/-- The union of the small colour classes has cardinality `< ρ`
(`|D| < ρ`, `eq:D-small`).  A vertex is "small" if its own colour class has size
`< ρ`. -/
theorem Dsmall_lt (hμ : ℵ₀ ≤ μ) {θ : Cardinal.{u}} (hθ : θ < Order.succ μ)
    (c : Vtx (rhoC μ) → θ.out) :
    #({v : Vtx (rhoC μ) | #({w | c w = c v}) < rhoC μ}) < rhoC μ := by
  have hρ : ℵ₀ ≤ rhoC μ := le_trans hμ (le_of_lt (Cardinal.cantor μ))
  have hpos : (0 : Cardinal) < rhoC μ := lt_of_lt_of_le Cardinal.aleph0_pos hρ
  refine lt_of_le_of_lt (Cardinal.mk_le_mk_of_subset
    (t := ⋃ a : θ.out, {v : Vtx (rhoC μ) | c v = a ∧ #({w | c w = a}) < rhoC μ}) ?_) ?_
  · intro x hx
    exact Set.mem_iUnion.2 ⟨c x, rfl, hx⟩
  · refine small_union (rhoC μ) μ hρ (cf_two_pow μ hμ) ?_
      (fun a => {v : Vtx (rhoC μ) | c v = a ∧ #({w | c w = a}) < rhoC μ}) ?_
    · rw [Cardinal.mk_out]; exact Order.lt_succ_iff.mp hθ
    · intro a
      show #({v : Vtx (rhoC μ) | c v = a ∧ #({w | c w = a}) < rhoC μ}) < rhoC μ
      by_cases ha : #({w | c w = a}) < rhoC μ
      · exact lt_of_le_of_lt (Cardinal.mk_le_mk_of_subset (fun x hx => hx.1)) ha
      · have he : {v : Vtx (rhoC μ) | c v = a ∧ #({w | c w = a}) < rhoC μ} = ∅ := by
          rw [Set.eq_empty_iff_forall_notMem]
          intro v hv; exact ha hv.2
        rw [he]; simpa using! hpos

/-
For a fixed large colour `a`, at most one value `ξ` can satisfy
`|C_a \ Q_ξ| < ρ` (`eq:exceptional`).
-/
theorem exceptional_subsingleton {θ : Cardinal.{u}} (c : Vtx (rhoC μ) → θ.out)
    (a : θ.out) (hlarge : rhoC μ ≤ #({v | c v = a})) :
    {ξ : Ordinal.{u} | #(↥(({v | c v = a} : Set (Vtx (rhoC μ))) \ {v | D.q (lrank v.1) = ξ})) < rhoC μ}.Subsingleton := by
  intro ξ hξ ζ hζ;
  contrapose! hlarge;
  refine' lt_of_le_of_lt _ ( Cardinal.add_lt_of_lt _ hξ hζ );
  · refine' le_trans _ ( Cardinal.mk_union_le _ _ );
    refine' Cardinal.mk_le_mk_of_subset _;
    grind;
  · exact le_trans D.hμ ( le_of_lt ( Cardinal.cantor μ ) )

/-
There is a value `ξ < κ` (a `q`-colour) that is not exceptional for any large
colour: for every large colour `a`, `|C_a \ Q_ξ| ≥ ρ`.
-/
theorem exists_xi {θ : Cardinal.{u}} (hθ : θ < Order.succ μ) (c : Vtx (rhoC μ) → θ.out) :
    ∃ ξ : Ordinal.{u}, ξ < (Order.succ μ).ord ∧
      ∀ a : θ.out, rhoC μ ≤ #({v | c v = a}) →
        rhoC μ ≤ #(↥(({v | c v = a} : Set (Vtx (rhoC μ))) \ {v | D.q (lrank v.1) = ξ})) := by
  by_contra! h;
  -- For each `lv : T`, set `ξ lv := Ordinal.typein (·<·) lv`, which satisfies `ξ lv < (Order.succ μ).ord` by `Ordinal.typein_lt_self`.
  set T := (Order.succ μ).ord.ToType
  have hT : #T = Order.succ μ := by
    rw [Cardinal.mk_toType, Cardinal.card_ord]
  choose! F hF₁ hF₂ using fun lv : T => h ( Ordinal.typein ( α := T ) ( · < · ) lv ) ( Ordinal.typein_lt_self lv );
  -- Claim `F : T → θ.out` is injective.
  have hF_inj : Function.Injective F := by
    intro lv lv' hF;
    have := D.exceptional_subsingleton c ( F lv ) ( hF₁ lv );
    exact Ordinal.typein_injective ( · < · ) ( this ( hF₂ lv ) ( by simpa [ hF ] using! hF₂ lv' ) );
  have hF_card : #T ≤ #θ.out := by
    exact Cardinal.mk_le_of_injective hF_inj;
  grind +suggestions

/-
Given a set `Y` of at most `ρ` vertices and a `q`-colour `ξ < κ`, there is a
level `lv` with `q(rk lv) = ξ` lying strictly above every vertex of `Y`
(`R = ρ⁺` is regular and `q`-fibres are cofinal).
-/
theorem exists_level_above (Y : Set (Vtx (rhoC μ))) (hY : #Y ≤ rhoC μ)
    (ξ : Ordinal.{u}) (hξ : ξ < (Order.succ μ).ord) :
    ∃ lv : Lev (rhoC μ), D.q (lrank lv) = ξ ∧ ∀ v ∈ Y, v.1 < lv := by
  -- Consider the function `f : ↥Y → Ordinal`, `f v := lrank v.val.1 = Ordinal.typein (·<·) v.val.1`.
  set f : Y → Ordinal := fun v => lrank v.val.1;
  -- By `Ordinal.iSup_lt_ord_lift`, `s := ⨆ v : ↥Y, f v < R`.
  have hs : ⨆ v : Y, f v < Rord (rhoC μ) := by
    apply Ordinal.iSup_lt_ord_lift;
    · have hcof : (Rord (rhoC μ)).cof = Order.succ (rhoC μ) := by
        exact Cardinal.IsRegular.cof_eq ( Cardinal.isRegular_succ ( by exact le_trans D.hμ ( le_of_lt ( Cardinal.cantor μ ) ) ) );
      exact hcof.symm ▸ lt_of_le_of_lt ( by simpa ) ( Order.lt_succ ( rhoC μ ) );
    · exact fun v => Ordinal.typein_lt_self _;
  obtain ⟨α, hα⟩ : ∃ α : Ordinal, ⨆ v : Y, f v < α ∧ α < Rord (rhoC μ) ∧ D.q α = ξ := by
    obtain ⟨α, hα⟩ : ∃ α : Ordinal, ⨆ v : Y, f v < α ∧ α < Rord (rhoC μ) ∧ D.q α = ξ := by
      have := D.hq2 ξ hξ (Order.succ (⨆ v : Y, f v)) (by
      refine' lt_of_le_of_ne _ _;
      · exact Order.succ_le_of_lt hs;
      · intro h;
        have := D.hμ;
        have := Cardinal.isRegular_succ ( show ℵ₀ ≤ rhoC μ from le_trans this ( le_of_lt ( Cardinal.cantor μ ) ) );
        have := this.2; simp_all +decide [ Rord ] ;
        rw [ ← h ] at this;
        rw [ Ordinal.cof_add_one ] at this ; norm_num at this;
        exact absurd this ( ne_of_gt ( Cardinal.power_pos _ ( by norm_num ) ) ))
      exact ⟨ this.choose, lt_of_lt_of_le ( Order.lt_succ _ ) this.choose_spec.1, this.choose_spec.2.1, this.choose_spec.2.2 ⟩;
    use α;
  obtain ⟨lv, hlv⟩ : ∃ lv : Lev (rhoC μ), lrank lv = α := by
    have h_enum : ∀ α : Ordinal, α < Rord (rhoC μ) → ∃ lv : Lev (rhoC μ), lrank lv = α := by
      intro α hα;
      have h_enum : ∀ α : Ordinal, α < Rord (rhoC μ) → ∃ lv : Lev (rhoC μ), lrank lv = α := by
        intro α hα
        have h_enum : α < Ordinal.type (· < · : Lev (rhoC μ) → Lev (rhoC μ) → Prop) := by
          convert! hα using 1;
          convert! Ordinal.type_toType ( Rord ( rhoC μ ) ) using 1
        exact ⟨ Ordinal.enum ( · < · ) ⟨ α, h_enum ⟩, by simp +decide [ lrank ] ⟩;
      exact h_enum α hα;
    exact h_enum α hα.2.1;
  refine' ⟨ lv, _, _ ⟩ <;> simp_all +decide only [Prod.forall];
  intro a b hab;
  exact Ordinal.typein_lt_typein ( · < · ) |>.1 ( hlv.symm ▸ lt_of_le_of_lt ( Ordinal.le_iSup ( fun v : Y => lrank v.val.1 ) ⟨ ( a, b ), hab ⟩ ) hα.1 )

/-
Among the `Λ = 2^ρ` installed copies at a level, fewer than `ρ` meet a fixed
set `Bad` of size `< ρ`, so some copy avoids `Bad` entirely.
-/
theorem exists_disjoint_copy (Bad : Set (Vtx (rhoC μ))) (hBad : #Bad < rhoC μ)
    (lv : Lev (rhoC μ))
    (X : {X : D.Ilab → Set (Vtx (rhoC μ)) // IsReservoir D.q lv X}) :
    ∃ η : Fib (rhoC μ), ∀ s : D.S, D.copy lv X η s ∉ Bad := by
  contrapose! hBad; have := D.copy_inj lv; simp_all +decide only [ge_iff_le] ;
  choose f hf using hBad;
  refine' le_trans _ ( Cardinal.mk_le_mk_of_subset <| show Set.range ( fun η : Fib ( rhoC μ ) => D.copy lv X η ( f η ) ) ⊆ Bad from Set.range_subset_iff.mpr hf );
  rw [ Cardinal.mk_range_eq ];
  · rw [ Cardinal.mk_out ];
    exact le_of_lt ( Cardinal.cantor _ );
  · intro η η' h; specialize this _ X.2 _ _ _ X.2 _ _ h; aesop;

/-- **Reservoir capture** (`lem:reservoir-capture`).  Given a colouring `c` of
`L_κ` with `θ < κ` colours, there is an admissible reservoir `X` at some level
`a` and an index `η < ρ` such that the installed copy `B = B_{X,η}` has the
following property: there is a label assignment `bigLabel : θ → I` for which,
for every vertex `s` of `S`, the reservoir set of the label `bigLabel (c(copy s))`
is nonempty and is entirely contained in the colour class of `c(copy s)`.

In the paper's terms, `B` is disjoint from the union `D` of the small colour
classes (so every colour occurring on `B` is "large"), and `bigLabel` is the
injection `a ↦ i_a` from large colours to labels, with `X_{i_a} ⊆ C_a`. -/
theorem reservoir_capture {θ : Cardinal.{u}} (hθ : θ < Order.succ μ)
    (c : Vtx (rhoC μ) → θ.out) :
    ∃ (a : Lev (rhoC μ))
      (X : {X : D.Ilab → Set (Vtx (rhoC μ)) // IsReservoir D.q a X})
      (η : Fib (rhoC μ)) (bigLabel : θ.out → D.Ilab),
      (∀ s : D.S, (X.val (bigLabel (c (D.copy a X η s)))).Nonempty) ∧
      (∀ s : D.S, X.val (bigLabel (c (D.copy a X η s))) ⊆ {v | c v = c (D.copy a X η s)}) := by
  have hμ : ℵ₀ ≤ μ := D.hμ
  have hρ : ℵ₀ ≤ rhoC μ := le_trans hμ (le_of_lt (Cardinal.cantor μ))
  have hpos : (0 : Cardinal) < rhoC μ := lt_of_lt_of_le Cardinal.aleph0_pos hρ
  have hθμ : θ ≤ μ := Order.lt_succ_iff.mp hθ
  obtain ⟨ξ, hξord, hξlarge⟩ := D.exists_xi hθ c
  have hemb : Nonempty (θ.out ↪ D.Ilab) := by
    rw [← Cardinal.le_def, Cardinal.mk_out, D.hIlab]
    exact le_trans hθμ (le_of_lt (Cardinal.cantor μ))
  obtain ⟨bigLabelE⟩ := hemb
  set bigLabel : θ.out → D.Ilab := ⇑bigLabelE with hblab
  have hbig : Function.Injective bigLabel := bigLabelE.injective
  set diff : θ.out → Set (Vtx (rhoC μ)) :=
    fun a => (({v | c v = a} : Set (Vtx (rhoC μ))) \ {v | D.q (lrank v.1) = ξ}) with hdiff
  have hZex : ∀ a : θ.out, ∃ Z : Set (Vtx (rhoC μ)),
      (rhoC μ ≤ #(diff a) → Z ⊆ diff a ∧ #Z = rhoC μ) ∧
      (#(diff a) < rhoC μ → Z = ∅) := by
    intro a
    by_cases ha : rhoC μ ≤ #(diff a)
    · obtain ⟨Z, hZsub, hZcard⟩ := Cardinal.le_mk_iff_exists_subset.mp ha
      exact ⟨Z, fun _ => ⟨hZsub, hZcard⟩, fun h => absurd h (not_lt.mpr ha)⟩
    · exact ⟨∅, fun h => absurd h ha, fun _ => rfl⟩
  choose Z hZ1 hZ2 using hZex
  have hZle : ∀ a, #(Z a) ≤ rhoC μ := by
    intro a
    by_cases ha : rhoC μ ≤ #(diff a)
    · exact le_of_eq (hZ1 a ha).2
    · rw [hZ2 a (not_le.mp ha)]; simp
  set X : D.Ilab → Set (Vtx (rhoC μ)) := fun i => ⋃ (a : θ.out) (_ : bigLabel a = i), Z a with hXdef
  have hXbig : ∀ a, X (bigLabel a) = Z a := by
    intro a; ext v
    simp only [hXdef, Set.mem_iUnion]
    constructor
    · rintro ⟨a', ha', hv⟩; rwa [hbig ha'] at hv
    · intro hv; exact ⟨a, rfl, hv⟩
  have hXsub : ∀ i, X i ⊆ ⋃ a, Z a := by
    intro i v hv
    simp only [hXdef, Set.mem_iUnion] at hv ⊢
    obtain ⟨a, _, hv⟩ := hv; exact ⟨a, hv⟩
  have hUcard : #(↥(⋃ a, Z a)) ≤ rhoC μ := by
    refine le_trans (Cardinal.mk_iUnion_le Z) ?_
    have h1 : #θ.out ≤ rhoC μ := by
      rw [Cardinal.mk_out]; exact le_trans hθμ (le_of_lt (Cardinal.cantor μ))
    calc #θ.out * ⨆ a, #(Z a) ≤ rhoC μ * rhoC μ :=
            mul_le_mul' h1 (ciSup_le' hZle)
      _ = rhoC μ := Cardinal.mul_eq_self hρ
  obtain ⟨lv, hlvq, hlvabove⟩ := D.exists_level_above (⋃ a, Z a) hUcard ξ hξord
  have hres : IsReservoir D.q lv X := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro i v hv
      exact hlvabove v (hXsub i hv)
    · intro i
      by_cases hi : ∃ a, bigLabel a = i
      · obtain ⟨a, rfl⟩ := hi
        rw [hXbig a]
        by_cases ha : rhoC μ ≤ #(diff a)
        · exact Or.inr (hZ1 a ha).2
        · exact Or.inl (hZ2 a (not_le.mp ha))
      · left
        ext v; simp only [hXdef, Set.mem_iUnion, Set.mem_empty_iff_false, iff_false]
        rintro ⟨a, ha, _⟩; exact hi ⟨a, ha⟩
    · intro i j hij hi hj
      obtain ⟨v, hv⟩ := hi
      simp only [hXdef, Set.mem_iUnion] at hv
      obtain ⟨a, hai, _⟩ := hv
      obtain ⟨w, hw⟩ := hj
      simp only [hXdef, Set.mem_iUnion] at hw
      obtain ⟨a', ha'j, _⟩ := hw
      subst hai; subst ha'j
      have haa' : a ≠ a' := fun h => hij (by rw [h])
      rw [hXbig a, hXbig a']
      rw [Set.disjoint_left]
      intro x hxa hxa'
      have hda : rhoC μ ≤ #(diff a) := by
        by_contra h; rw [hZ2 a (not_le.mp h)] at hxa; exact hxa
      have hda' : rhoC μ ≤ #(diff a') := by
        by_contra h; rw [hZ2 a' (not_le.mp h)] at hxa'; exact hxa'
      have e1 : c x = a := ((hZ1 a hda).1 hxa).1
      have e2 : c x = a' := ((hZ1 a' hda').1 hxa').1
      exact haa' (by rw [← e1, e2])
    · intro i v hv
      have hvU : v ∈ ⋃ a, Z a := hXsub i hv
      simp only [Set.mem_iUnion] at hvU
      obtain ⟨a, hva⟩ := hvU
      have hda : rhoC μ ≤ #(diff a) := by
        by_contra h; rw [hZ2 a (not_le.mp h)] at hva; exact hva
      have hvdiff : v ∈ diff a := (hZ1 a hda).1 hva
      rw [hlvq]
      exact fun hq => hvdiff.2 hq
  obtain ⟨η, hη⟩ := D.exists_disjoint_copy
    {v : Vtx (rhoC μ) | #({w | c w = c v}) < rhoC μ} (Dsmall_lt hμ hθ c) lv ⟨X, hres⟩
  refine ⟨lv, ⟨X, hres⟩, η, bigLabel, ?_, ?_⟩
  · intro s
    set p := c (D.copy lv ⟨X, hres⟩ η s) with hpdef
    have hnotsmall : ¬ (#({w | c w = p}) < rhoC μ) := hη s
    have hlarge : rhoC μ ≤ #({v | c v = p}) := not_lt.mp hnotsmall
    have hdifflarge : rhoC μ ≤ #(diff p) := hξlarge p hlarge
    show (X (bigLabel p)).Nonempty
    rw [hXbig p, ← Set.nonempty_coe_sort]
    exact Cardinal.mk_ne_zero_iff.mp (by rw [(hZ1 p hdifflarge).2]; exact ne_of_gt hpos)
  · intro s
    set p := c (D.copy lv ⟨X, hres⟩ η s) with hpdef
    have hnotsmall : ¬ (#({w | c w = p}) < rhoC μ) := hη s
    have hlarge : rhoC μ ≤ #({v | c v = p}) := not_lt.mp hnotsmall
    have hdifflarge : rhoC μ ≤ #(diff p) := hξlarge p hlarge
    show X (bigLabel p) ⊆ {v | c v = p}
    rw [hXbig p]
    exact fun v hv => ((hZ1 p hdifflarge).1 hv).1

/-
**Lower bound** (`lem:calibration-lower`): no colouring of `L_κ` with fewer
than `κ = μ⁺` colours is proper.
-/
theorem L_lower : ∀ θ, θ < Order.succ μ → ¬ (D.L).ColorableBy θ := by
  intro θ hθ hcolorable
  obtain ⟨c, hc⟩ := hcolorable;
  obtain ⟨ a, X, η, bigLabel, h1, h2 ⟩ := D.reservoir_capture hθ c;
  obtain ⟨ p, hp ⟩ := D.hP θ hθ ( fun s => c ( D.copy a X η s ) );
  obtain ⟨ x, y, hxy, hi, hx, hy ⟩ := hp ( bigLabel p );
  have h_contradiction : c (D.phi a X ⟨s(x, y), hxy⟩) = p := by
    have := D.phi_mem a X ⟨ s(x, y), hxy ⟩ ?_;
    · grind;
    · grind;
  have := hc _ ( D.mem_edgeSetL.mpr ⟨ a, X, η, ⟨ s(x, y), hxy ⟩, by
    grind, rfl ⟩ );
  simp_all +decide [CalibData.edgeBase]

end CalibData

end Erdos1177
