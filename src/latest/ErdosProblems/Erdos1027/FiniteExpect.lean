/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import Mathlib

/-!
# Elementary expectation lemmas for finite random colourings

All probabilities in this file are exact rational averages over `Finset.univ`.
This keeps the finite first-moment arguments used for Erdős Problem 1027
independent of measure theory.
-/

namespace Erdos1027.FiniteExpect

open scoped BigOperators
open Finset

/-- The rational-valued indicator of a proposition. -/
noncomputable def indicator (p : Prop) : ℚ :=
  @ite ℚ p (Classical.propDecidable p) 1 0

@[simp] lemma indicator_of_true {p : Prop} (hp : p) : indicator p = 1 := by
  simp [indicator, hp]

@[simp] lemma indicator_of_false {p : Prop} (hp : ¬p) : indicator p = 0 := by
  simp [indicator, hp]

lemma indicator_nonneg (p : Prop) : 0 ≤ indicator p := by
  by_cases hp : p <;> simp [indicator, hp]

lemma indicator_le_one (p : Prop) : indicator p ≤ 1 := by
  by_cases hp : p <;> simp [indicator, hp]

/-- Summing indicators on a finite type counts the corresponding subtype. -/
lemma sum_indicator_eq_card_subtype {Ω : Type*} [Fintype Ω]
    (P : Ω → Prop) [Fintype {ω : Ω // P ω}] :
    (∑ ω : Ω, indicator (P ω)) = (Fintype.card {ω : Ω // P ω} : ℚ) := by
  classical
  rw [show (∑ ω : Ω, indicator (P ω)) =
      ((Finset.univ.filter P).card : ℚ) by simp [indicator]]
  exact_mod_cast (Fintype.card_subtype P).symm

/-- Pointwise finite union bound for rational indicators. -/
lemma indicator_biExists_le_sum {ι : Type*} (I : Finset ι) (P : ι → Prop) :
    indicator (∃ i ∈ I, P i) ≤ ∑ i ∈ I, indicator (P i) := by
  classical
  by_cases h : ∃ i ∈ I, P i
  · obtain ⟨i, hi, hPi⟩ := h
    have hone : (1 : ℚ) ≤ ∑ j ∈ I, indicator (P j) := by
      calc
        (1 : ℚ) = indicator (P i) := (indicator_of_true hPi).symm
        _ ≤ ∑ j ∈ I, indicator (P j) := by
          exact Finset.single_le_sum (fun j _ ↦ indicator_nonneg (P j)) hi
    rw [indicator_of_true ⟨i, hi, hPi⟩]
    exact hone
  · rw [indicator_of_false h]
    exact Finset.sum_nonneg fun i _ ↦ indicator_nonneg (P i)

/-- The finite union bound, written as an expectation over a uniform finite
sample space. -/
lemma expect_indicator_biExists_le_sum {Ω ι : Type*} [Fintype Ω]
    (I : Finset ι) (P : ι → Ω → Prop) :
    (𝔼 ω : Ω, indicator (∃ i ∈ I, P i ω)) ≤
      ∑ i ∈ I, 𝔼 ω : Ω, indicator (P i ω) := by
  classical
  calc
    (𝔼 ω : Ω, indicator (∃ i ∈ I, P i ω)) ≤
        𝔼 ω : Ω, ∑ i ∈ I, indicator (P i ω) :=
      Finset.expect_le_expect fun ω _ ↦ indicator_biExists_le_sum I (fun i ↦ P i ω)
    _ = ∑ i ∈ I, 𝔼 ω : Ω, indicator (P i ω) :=
      Finset.expect_sum_comm _ _ _

/-- Markov's inequality for a nonnegative rational random variable on a
uniform finite sample space. -/
lemma expect_indicator_le_of_pos {Ω : Type*} [Fintype Ω]
    (Z : Ω → ℚ) (a : ℚ) (ha : 0 < a) (hZ : ∀ ω, 0 ≤ Z ω) :
    (𝔼 ω : Ω, indicator (a ≤ Z ω)) ≤ (𝔼 ω : Ω, Z ω) / a := by
  classical
  calc
    (𝔼 ω : Ω, indicator (a ≤ Z ω)) ≤ 𝔼 ω : Ω, Z ω / a := by
      apply Finset.expect_le_expect
      intro ω _
      by_cases h : a ≤ Z ω
      · rw [indicator_of_true h]
        exact (le_div_iff₀ ha).2 (by simpa using h)
      · rw [indicator_of_false h]
        exact div_nonneg (hZ ω) ha.le
    _ = (𝔼 ω : Ω, Z ω) / a := (Finset.expect_div _ _ _).symm

/-- Linearity of expectation for the number of events which occur. -/
lemma expect_sum_indicator {Ω ι : Type*} [Fintype Ω]
    (I : Finset ι) (P : ι → Ω → Prop) :
    (𝔼 ω : Ω, ∑ i ∈ I, indicator (P i ω)) =
      ∑ i ∈ I, 𝔼 ω : Ω, indicator (P i ω) := by
  classical
  exact Finset.expect_sum_comm _ _ _

/-! ## Products and restrictions of finite function spaces -/

/-- A function on a finite type is the same data as its restrictions to a
finset and to that finset's complement. -/
def restrictionEquiv {α β : Type*} [Fintype α] [DecidableEq α]
    (E : Finset α) :
    (α → β) ≃ ((x : ↥E) → β) × ((x : ↥((Finset.univ : Finset α) \ E)) → β) where
  toFun f := ⟨fun x ↦ f x, fun x ↦ f x⟩
  invFun f x := if hx : x ∈ E then f.1 ⟨x, hx⟩ else f.2 ⟨x, by simp [hx]⟩
  left_inv f := by
    funext x
    by_cases hx : x ∈ E <;> simp [hx]
  right_inv f := by
    apply Prod.ext
    · funext x
      simp [x.2]
    · funext x
      have hx : (x : α) ∉ E := by
        have hmem : (x : α) ∈ (Finset.univ : Finset α) \ E := x.2
        exact (Finset.mem_sdiff.mp hmem).2
      simp [hx]

/-- Dependent functions satisfying a finite list of pointwise restrictions. -/
def AllowedFunctions {α : Type*} {β : α → Type*}
    (allowed : ∀ x, Finset (β x)) :=
  {f : ∀ x, β x // ∀ x, f x ∈ allowed x}

/-- An allowed dependent function is equivalently a dependent function into
the corresponding subtype of allowed values. -/
def allowedFunctionsEquiv {α : Type*} {β : α → Type*}
    (allowed : ∀ x, Finset (β x)) :
    AllowedFunctions allowed ≃ ∀ x, ↥(allowed x) where
  toFun f x := ⟨f.1 x, f.2 x⟩
  invFun f := ⟨fun x ↦ (f x).1, fun x ↦ (f x).2⟩
  left_inv f := by rfl
  right_inv f := by rfl

noncomputable instance allowedFunctionsFintype
    {α : Type*} {β : α → Type*} [Fintype α]
    (allowed : ∀ x, Finset (β x)) :
    Fintype (AllowedFunctions allowed) := by
  classical
  exact Fintype.ofEquiv (∀ x, ↥(allowed x)) (allowedFunctionsEquiv allowed).symm

/-- The number of pointwise allowed functions is the product of the numbers
of choices at their coordinates. -/
lemma card_allowedFunctions {α : Type*} {β : α → Type*}
    [Fintype α] [∀ x, DecidableEq (β x)]
    (allowed : ∀ x, Finset (β x)) :
    Fintype.card (AllowedFunctions allowed) = ∏ x, (allowed x).card := by
  classical
  rw [Fintype.card_congr (allowedFunctionsEquiv allowed)]
  simp

/-! ## Exact sizes of discrete priority windows -/

/-- The upper `d / j` fraction of a priority interval of length `L`. -/
def IsHigh (L d j : ℕ) (p : Fin L) : Prop :=
  L ≤ p.1 + d * (L / j)

instance (L d j : ℕ) (p : Fin L) : Decidable (IsHigh L d j p) :=
  by
    unfold IsHigh
    infer_instance

/-- If `j ∣ L` and `d ≤ j`, the discrete upper priority window has exactly
`d * (L / j)` points. -/
lemma card_filter_isHigh {L d j : ℕ} (hdj : d ≤ j) (hjL : j ∣ L) :
    ((Finset.univ : Finset (Fin L)).filter (IsHigh L d j)).card = d * (L / j) := by
  have hm : d * (L / j) ≤ L := by
    calc
      d * (L / j) ≤ j * (L / j) := Nat.mul_le_mul_right (L / j) hdj
      _ = L := Nat.mul_div_cancel' hjL
  have hnot :
      ((Finset.univ : Finset (Fin L)).filter (fun p ↦ ¬IsHigh L d j p)).card =
        L - d * (L / j) := by
    rw [show (Finset.univ : Finset (Fin L)).filter (fun p ↦ ¬IsHigh L d j p) =
        Finset.univ.filter (fun p ↦ p.1 < L - d * (L / j)) by
      ext p
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      simp only [IsHigh]
      omega]
    simpa [Nat.min_eq_right (Nat.sub_le _ _)] using
      (Fin.card_filter_val_lt (n := L) (m := L - d * (L / j)))
  have hpartition :=
    Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Fin L)))
      (p := IsHigh L d j)
  simp only [Finset.card_univ, Fintype.card_fin] at hpartition
  rw [hnot] at hpartition
  omega

/-! ## Prescribed values of a uniform random function -/

/-- The event that `f` agrees with `g` at every point of `E`. -/
def AgreesOn {α β : Type*} [DecidableEq α]
    (E : Finset α) (g f : α → β) : Prop :=
  ∀ x ∈ E, f x = g x

/-- Functions which agree with `g` on `E`. -/
def RestrictedExtensions {α β : Type*} [Fintype α] [DecidableEq α]
    (E : Finset α) (g : α → β) :=
  {f : α → β // AgreesOn E g f}

/-- A prescribed restriction leaves exactly the complement coordinates
free. -/
def restrictedExtensionsEquiv {α β : Type*} [Fintype α] [DecidableEq α]
    (E : Finset α) (g : α → β) :
    RestrictedExtensions E g ≃ ((x : ↥((Finset.univ : Finset α) \ E)) → β) where
  toFun f x := f.1 x
  invFun f := ⟨fun x ↦ if hx : x ∈ E then g x else f ⟨x, by simp [hx]⟩, by
    intro x hx
    simp [AgreesOn, hx]⟩
  left_inv f := by
    apply Subtype.ext
    funext x
    by_cases hx : x ∈ E
    · simp [hx, f.2 x hx]
    · simp [hx]
  right_inv f := by
    funext x
    have hx : (x : α) ∉ E := by
      have hmem : (x : α) ∈ (Finset.univ : Finset α) \ E := x.2
      exact (Finset.mem_sdiff.mp hmem).2
    simp [hx]

noncomputable instance restrictedExtensionsFintype
    {α β : Type*} [Fintype α] [DecidableEq α] [Fintype β]
    (E : Finset α) (g : α → β) :
    Fintype (RestrictedExtensions E g) := by
  classical
  exact Fintype.ofEquiv ((x : ↥((Finset.univ : Finset α) \ E)) → β)
    (restrictedExtensionsEquiv E g).symm

lemma card_restrictedExtensions {α β : Type*}
    [Fintype α] [DecidableEq α] [Fintype β]
    (E : Finset α) (g : α → β) :
    Fintype.card (RestrictedExtensions E g) =
      Fintype.card β ^ (Fintype.card α - E.card) := by
  rw [Fintype.card_congr (restrictedExtensionsEquiv E g)]
  simp

/-- A uniform random function agrees with prescribed values on `E` with
probability `|β| ^ (-|E|)`. -/
lemma expect_indicator_agreesOn {α β : Type*}
    [Fintype α] [DecidableEq α] [Fintype β] [Nonempty β]
    (E : Finset α) (g : α → β) :
    (𝔼 f : α → β, indicator (AgreesOn E g f)) =
      1 / (Fintype.card β : ℚ) ^ E.card := by
  classical
  let : Fintype {f : α → β // AgreesOn E g f} :=
    restrictedExtensionsFintype E g
  rw [Fintype.expect_eq_sum_div_card]
  rw [sum_indicator_eq_card_subtype (fun f : α → β ↦ AgreesOn E g f)]
  change (Fintype.card (RestrictedExtensions E g) : ℚ) /
      (Fintype.card (α → β) : ℚ) = _
  rw [card_restrictedExtensions E g]
  simp only [Fintype.card_fun, Nat.cast_pow]
  have hβ : (Fintype.card β : ℚ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  apply (div_eq_div_iff (pow_ne_zero _ hβ) (pow_ne_zero _ hβ)).2
  rw [one_mul, ← pow_add, Nat.sub_add_cancel E.card_le_univ]

/-- Specialization to uniformly random `Fin k`-valued functions. -/
lemma expect_indicator_fin_agreesOn {α : Type*} [Fintype α] [DecidableEq α]
    {k : ℕ} (hk : 0 < k) (E : Finset α) (g : α → Fin k) :
    (𝔼 f : α → Fin k, indicator (AgreesOn E g f)) =
      1 / (k : ℚ) ^ E.card := by
  let : NeZero k := ⟨hk.ne'⟩
  simpa using expect_indicator_agreesOn E g

/-! ## Exact probabilities for fair Boolean colourings -/

/-- The event that a colouring is constant on `E`. -/
def IsMonochromatic {α : Type*} [DecidableEq α]
    (E : Finset α) (χ : α → Bool) : Prop :=
  ∃ b : Bool, ∀ x ∈ E, χ x = b

instance isMonochromaticDecidable {α : Type*} [DecidableEq α]
    (E : Finset α) (χ : α → Bool) : Decidable (IsMonochromatic E χ) := by
  unfold IsMonochromatic
  infer_instance

/-- Colourings which give one specified colour to all vertices in `E`. -/
def ConstantColorings {α : Type*} [Fintype α] [DecidableEq α]
    (E : Finset α) (b : Bool) :=
  {χ : α → Bool // ∀ x ∈ E, χ x = b}

/-- A colouring fixed on `E` is freely specified on the complement of `E`. -/
noncomputable def constantColoringsEquiv
    {α : Type*} [Fintype α] [DecidableEq α]
    (E : Finset α) (b : Bool) :
    ConstantColorings E b ≃ ((x : ↥((Finset.univ : Finset α) \ E)) → Bool) where
  toFun χ x := χ.1 x
  invFun f := ⟨fun x ↦ if hx : x ∈ E then b else f ⟨x, by simp [hx]⟩, by
    intro x hx
    simp [hx]⟩
  left_inv χ := by
    apply Subtype.ext
    funext x
    by_cases hx : x ∈ E
    · simp [hx, χ.2 x hx]
    · simp [hx]
  right_inv f := by
    funext x
    have hx : (x : α) ∉ E := by
      have hmem : (x : α) ∈ (Finset.univ : Finset α) \ E := x.2
      exact (Finset.mem_sdiff.mp hmem).2
    simp [hx]

noncomputable instance constantColoringsFintype
    {α : Type*} [Fintype α] [DecidableEq α]
    (E : Finset α) (b : Bool) :
    Fintype (ConstantColorings E b) :=
  Fintype.ofEquiv ((x : ↥((Finset.univ : Finset α) \ E)) → Bool)
    (constantColoringsEquiv E b).symm

lemma card_constantColorings
    {α : Type*} [Fintype α] [DecidableEq α]
    (E : Finset α) (b : Bool) :
    Fintype.card (ConstantColorings E b) =
      2 ^ (Fintype.card α - E.card) := by
  rw [Fintype.card_congr (constantColoringsEquiv E b)]
  simp

/-- A monochromatic colouring with its colour recorded. -/
def MonochromaticWitness {α : Type*} [Fintype α] [DecidableEq α]
    (E : Finset α) :=
  Σ b : Bool, ConstantColorings E b

noncomputable instance monochromaticWitnessFintype
    {α : Type*} [Fintype α] [DecidableEq α] (E : Finset α) :
    Fintype (MonochromaticWitness E) := by
  classical
  unfold MonochromaticWitness
  infer_instance

lemma card_monochromaticWitness
    {α : Type*} [Fintype α] [DecidableEq α]
    (E : Finset α) :
    Fintype.card (MonochromaticWitness E) =
      2 ^ (Fintype.card α - E.card + 1) := by
  simp only [MonochromaticWitness, Fintype.card_sigma, card_constantColorings]
  norm_num [pow_succ, Nat.mul_comm]

/-- On a nonempty edge, the monochromatic colour is unique. -/
noncomputable def monochromaticWitnessEquiv
    {α : Type*} [Fintype α] [DecidableEq α]
    (E : Finset α) (hE : E.Nonempty) :
    MonochromaticWitness E ≃ {χ : α → Bool // IsMonochromatic E χ} := by
  classical
  let x₀ : α := hE.choose
  have hx₀ : x₀ ∈ E := hE.choose_spec
  refine
    { toFun := fun w ↦ ⟨w.2.1, ⟨w.1, w.2.2⟩⟩
      invFun := fun χ ↦ ⟨χ.1 x₀, ⟨χ.1, ?_⟩⟩
      left_inv := ?_
      right_inv := ?_ }
  · intro x hx
    obtain ⟨b, hb⟩ := χ.2
    exact (hb x hx).trans (hb x₀ hx₀).symm
  · rintro ⟨b, χ⟩
    have hb : χ.1 x₀ = b := χ.2 x₀ hx₀
    refine Sigma.ext hb ?_
    refine (Subtype.heq_iff_coe_eq ?_).2 rfl
    intro f
    simp only [hb]
  · intro χ
    apply Subtype.ext
    rfl

lemma card_monochromaticColorings
    {α : Type*} [Fintype α] [DecidableEq α]
    (E : Finset α) (hE : E.Nonempty) :
    Fintype.card {χ : α → Bool // IsMonochromatic E χ} =
      2 ^ (Fintype.card α - E.card + 1) := by
  rw [← Fintype.card_congr (monochromaticWitnessEquiv E hE)]
  exact card_monochromaticWitness E

/-- A fixed nonempty set of vertices is monochromatic under a fair Boolean
colouring with probability exactly `2 / 2 ^ E.card`, equivalently
`2 ^ (1 - E.card)` with an integer exponent. -/
lemma expect_indicator_isMonochromatic
    {α : Type*} [Fintype α] [DecidableEq α]
    (E : Finset α) (hE : E.Nonempty) :
    (𝔼 χ : α → Bool, indicator (IsMonochromatic E χ)) =
      2 / (2 : ℚ) ^ E.card := by
  classical
  rw [Fintype.expect_eq_sum_div_card]
  rw [sum_indicator_eq_card_subtype
    (fun χ : α → Bool ↦ IsMonochromatic E χ)]
  rw [card_monochromaticColorings E hE]
  simp only [Fintype.card_fun, Fintype.card_bool, Nat.cast_pow, Nat.cast_ofNat]
  apply (div_eq_div_iff (by positivity) (by positivity)).2
  rw [← pow_add, ← pow_succ']
  congr 1
  have hle := E.card_le_univ
  omega

/-- The same probability in literal integer-exponent notation. -/
lemma expect_indicator_isMonochromatic_zpow
    {α : Type*} [Fintype α] [DecidableEq α]
    (E : Finset α) (hE : E.Nonempty) :
    (𝔼 χ : α → Bool, indicator (IsMonochromatic E χ)) =
      (2 : ℚ) ^ (1 - (E.card : ℤ)) := by
  rw [expect_indicator_isMonochromatic E hE]
  rw [zpow_sub₀ (by norm_num : (2 : ℚ) ≠ 0), zpow_one, zpow_natCast]

/-- The number of monochromatic edges in a Boolean colouring. -/
noncomputable def monochromaticEdgeCount {α : Type*} [DecidableEq α]
    (H : Finset (Finset α)) (χ : α → Bool) : ℚ :=
  ∑ E ∈ H, indicator (IsMonochromatic E χ)

/-- The expected number of monochromatic edges is the sum of their exact
dyadic probabilities. -/
lemma expect_monochromaticEdgeCount
    {α : Type*} [Fintype α] [DecidableEq α]
    (H : Finset (Finset α)) (hH : ∀ E ∈ H, E.Nonempty) :
    (𝔼 χ : α → Bool, monochromaticEdgeCount H χ) =
      ∑ E ∈ H, 2 / (2 : ℚ) ^ E.card := by
  classical
  change (𝔼 χ : α → Bool, ∑ E ∈ H, indicator (IsMonochromatic E χ)) = _
  rw [expect_sum_indicator]
  exact Finset.sum_congr rfl fun E hE ↦ expect_indicator_isMonochromatic E (hH E hE)

/-- An edge is almost monochromatic when deleting some one of its vertices
leaves a monochromatic set.  This is the event counted by `Q_j` in the
random-greedy argument. -/
def IsAlmostMonochromatic {α : Type*} [DecidableEq α]
    (E : Finset α) (χ : α → Bool) : Prop :=
  ∃ v ∈ E, IsMonochromatic (E.erase v) χ

instance isAlmostMonochromaticDecidable {α : Type*} [DecidableEq α]
    (E : Finset α) (χ : α → Bool) : Decidable (IsAlmostMonochromatic E χ) := by
  unfold IsAlmostMonochromatic
  infer_instance

/-- Union-bound estimate for one almost-monochromatic edge. -/
lemma expect_indicator_isAlmostMonochromatic_le
    {α : Type*} [Fintype α] [DecidableEq α]
    (E : Finset α) (hE : 2 ≤ E.card) :
    (𝔼 χ : α → Bool, indicator (IsAlmostMonochromatic E χ)) ≤
      (E.card : ℚ) * (2 / (2 : ℚ) ^ (E.card - 1)) := by
  classical
  calc
    (𝔼 χ : α → Bool, indicator (IsAlmostMonochromatic E χ)) ≤
        ∑ v ∈ E, 𝔼 χ : α → Bool,
          indicator (IsMonochromatic (E.erase v) χ) := by
      simpa only [IsAlmostMonochromatic] using
        (expect_indicator_biExists_le_sum (Ω := α → Bool) E
          (fun v χ ↦ IsMonochromatic (E.erase v) χ))
    _ = ∑ _v ∈ E, 2 / (2 : ℚ) ^ (E.card - 1) := by
      apply Finset.sum_congr rfl
      intro v hv
      have hcard : (E.erase v).card = E.card - 1 := Finset.card_erase_of_mem hv
      have herase : (E.erase v).Nonempty := Finset.card_pos.mp (by omega)
      rw [expect_indicator_isMonochromatic (E.erase v) herase, hcard]
    _ = (E.card : ℚ) * (2 / (2 : ℚ) ^ (E.card - 1)) := by
      simp

/-- The number of almost-monochromatic edges in a Boolean colouring. -/
noncomputable def almostMonochromaticEdgeCount {α : Type*} [DecidableEq α]
    (H : Finset (Finset α)) (χ : α → Bool) : ℚ :=
  ∑ E ∈ H, indicator (IsAlmostMonochromatic E χ)

/-- Expected almost-monochromatic edge count, in the non-uniform form used
before grouping the hypergraph by edge size. -/
lemma expect_almostMonochromaticEdgeCount_le
    {α : Type*} [Fintype α] [DecidableEq α]
    (H : Finset (Finset α)) (hH : ∀ E ∈ H, 2 ≤ E.card) :
    (𝔼 χ : α → Bool, almostMonochromaticEdgeCount H χ) ≤
      ∑ E ∈ H, (E.card : ℚ) * (2 / (2 : ℚ) ^ (E.card - 1)) := by
  classical
  change (𝔼 χ : α → Bool, ∑ E ∈ H, indicator (IsAlmostMonochromatic E χ)) ≤ _
  rw [expect_sum_indicator]
  exact Finset.sum_le_sum fun E hE ↦ expect_indicator_isAlmostMonochromatic_le E (hH E hE)

end Erdos1027.FiniteExpect
