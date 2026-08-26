import ErdosProblems.Erdos336.RectifiedEndpointNormalization
import ErdosProblems.Erdos336.VerticalStabilizer

/- Ported from Lean 4.31.0 to 4.33.0; imports, helper namespaces, and elaboration adapted. -/
set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

namespace Erdos336

set_option maxHeartbeats 1200000

open scoped Pointwise

variable {G : Type*} [AddCommGroup G] [DecidableEq G]

/-- Translating both summands translates their sum by twice the translate. -/
theorem add_vadd_self_eq_vadd_add (A : Finset G) (p : G) :
    (-p +ᵥ A) + (-p +ᵥ A) = -(p + p) +ᵥ (A + A) := by
  ext z
  constructor
  · intro hz
    obtain ⟨x, hx, y, hy, hxy⟩ := Finset.mem_add.mp hz
    obtain ⟨a, ha, hax⟩ := Finset.mem_vadd_finset.mp hx
    obtain ⟨b, hb, hby⟩ := Finset.mem_vadd_finset.mp hy
    apply Finset.mem_vadd_finset.mpr
    refine ⟨a + b, Finset.mem_add.mpr ⟨a, ha, b, hb, rfl⟩, ?_⟩
    simp only [vadd_eq_add] at hax hby ⊢
    rw [← hxy, ← hax, ← hby]
    abel
  · intro hz
    obtain ⟨w, hw, hwz⟩ := Finset.mem_vadd_finset.mp hz
    obtain ⟨a, ha, b, hb, hab⟩ := Finset.mem_add.mp hw
    apply Finset.mem_add.mpr
    refine ⟨-p + a, Finset.mem_vadd_finset.mpr ⟨a, ha, rfl⟩,
      -p + b, Finset.mem_vadd_finset.mpr ⟨b, hb, rfl⟩, ?_⟩
    simp only [vadd_eq_add] at hwz
    rw [← hwz, ← hab]
    abel

/-- Translating a set commutes with adding any finite set. -/
theorem vadd_add_eq_vadd_add (A V : Finset G) (p : G) :
    (-p +ᵥ A) + V = -p +ᵥ (A + V) := by
  ext z
  constructor
  · intro hz
    obtain ⟨x, hx, v, hv, hxv⟩ := Finset.mem_add.mp hz
    obtain ⟨a, ha, hax⟩ := Finset.mem_vadd_finset.mp hx
    apply Finset.mem_vadd_finset.mpr
    refine ⟨a + v, Finset.mem_add.mpr ⟨a, ha, v, hv, rfl⟩, ?_⟩
    simp only [vadd_eq_add] at hax ⊢
    rw [← hxv, ← hax]
    abel
  · intro hz
    obtain ⟨w, hw, hwz⟩ := Finset.mem_vadd_finset.mp hz
    obtain ⟨a, ha, v, hv, hav⟩ := Finset.mem_add.mp hw
    apply Finset.mem_add.mpr
    refine ⟨-p + a, Finset.mem_vadd_finset.mpr ⟨a, ha, rfl⟩, v, hv, ?_⟩
    simp only [vadd_eq_add] at hwz
    rw [← hwz, ← hav]
    abel

@[simp] theorem card_translate_add (A V : Finset G) (p : G) :
    ((-p +ᵥ A) + V).card = (A + V).card := by
  rw [vadd_add_eq_vadd_add, Finset.card_vadd_finset]

@[simp] theorem card_translate_double (A : Finset G) (p : G) :
    ((-p +ᵥ A) + (-p +ᵥ A)).card = (A + A).card := by
  rw [add_vadd_self_eq_vadd_add, Finset.card_vadd_finset]

@[simp] theorem card_translate_double_add (A V : Finset G) (p : G) :
    (((-p +ᵥ A) + (-p +ᵥ A)) + V).card = ((A + A) + V).card := by
  rw [add_vadd_self_eq_vadd_add, vadd_add_eq_vadd_add,
    Finset.card_vadd_finset]

/-- A homomorphic image has unchanged cardinality after translating its
source finset. -/
theorem card_image_vadd
    {Q : Type*} [AddCommGroup Q] [DecidableEq Q]
    (A : Finset G) (p : G) (f : G →+ Q) :
    ((-p +ᵥ A).image f).card = (A.image f).card := by
  have heq : (-p +ᵥ A).image f = -f p +ᵥ (A.image f) := by
    ext z
    constructor
    · intro hz
      obtain ⟨x, hx, hxz⟩ := Finset.mem_image.mp hz
      obtain ⟨a, ha, hax⟩ := Finset.mem_vadd_finset.mp hx
      apply Finset.mem_vadd_finset.mpr
      refine ⟨f a, Finset.mem_image.mpr ⟨a, ha, rfl⟩, ?_⟩
      simp only [vadd_eq_add] at hax ⊢
      rw [← hxz, ← hax, map_add, map_neg]
    · intro hz
      obtain ⟨w, hw, hwz⟩ := Finset.mem_vadd_finset.mp hz
      obtain ⟨a, ha, haw⟩ := Finset.mem_image.mp hw
      apply Finset.mem_image.mpr
      refine ⟨-p + a, Finset.mem_vadd_finset.mpr ⟨a, ha, rfl⟩, ?_⟩
      simp only [vadd_eq_add] at hwz
      rw [← hwz, ← haw, map_add, map_neg]
  rw [heq, Finset.card_vadd_finset]

variable {N m : ℕ} [NeZero N] [NeZero m]

/-- A double sumset saturated by a vertical subgroup equals the double of the
saturated original lift. -/
theorem add_self_add_vertical_eq_saturated_add_self
    (T : Finset (ℤ × ZMod N)) (K : AddSubgroup (ZMod N)) :
    (T + T) + verticalSubgroupFinset K =
      (T + verticalSubgroupFinset K) + (T + verticalSubgroupFinset K) := by
  ext z
  constructor
  · intro hz
    obtain ⟨s, hs, v, hv, hsv⟩ := Finset.mem_add.mp hz
    obtain ⟨x, hx, y, hy, hxy⟩ := Finset.mem_add.mp hs
    apply Finset.mem_add.mpr
    refine ⟨x + v, Finset.mem_add.mpr ⟨x, hx, v, hv, rfl⟩,
      y + 0, Finset.mem_add.mpr ⟨y, hy, 0, ?_, rfl⟩, ?_⟩
    · exact mem_verticalSubgroupFinset.mpr ⟨rfl, K.zero_mem⟩
    · rw [add_zero, ← hsv, ← hxy]
      abel
  · intro hz
    obtain ⟨xv, hxv, yw, hyw, hsum⟩ := Finset.mem_add.mp hz
    obtain ⟨x, hx, v, hv, hxveq⟩ := Finset.mem_add.mp hxv
    obtain ⟨y, hy, w, hw, hyweq⟩ := Finset.mem_add.mp hyw
    apply Finset.mem_add.mpr
    refine ⟨x + y, Finset.mem_add.mpr ⟨x, hx, y, hy, rfl⟩,
      v + w, ?_, ?_⟩
    · obtain ⟨hv0, hvK⟩ := mem_verticalSubgroupFinset.mp hv
      obtain ⟨hw0, hwK⟩ := mem_verticalSubgroupFinset.mp hw
      exact mem_verticalSubgroupFinset.mpr
        ⟨by simp [hv0, hw0], K.add_mem hvK hwK⟩
    · rw [← hsum, ← hxveq, ← hyweq]
      abel

/-- Strict-half rectification preserves the cardinality of a double sumset
also after saturation by a subgroup killed by the rectifying homomorphism. -/
theorem card_add_rectifiedLift_add_vertical
    (A : Finset (ZMod N)) (π : ZMod N →+ ZMod m) (α : ZMod m)
    (houter : ∀ x ∈ A,
      ∃ q : ℕ, 2 * q < m ∧ π x = α + (q : ZMod m))
    (K : AddSubgroup (ZMod N)) (hK : K ≤ π.ker) :
    ((rectifiedLift A π α + rectifiedLift A π α) +
      verticalSubgroupFinset K).card =
      ((A + A) + addSubgroupFinset K).card := by
  let V := verticalSubgroupFinset K
  let KF := addSubgroupFinset K
  have houterSat : ∀ x ∈ A + KF,
      ∃ q : ℕ, 2 * q < m ∧ π x = α + (q : ZMod m) := by
    intro x hx
    obtain ⟨a, ha, k, hk, hak⟩ := Finset.mem_add.mp hx
    obtain ⟨q, hq, hπa⟩ := houter a ha
    refine ⟨q, hq, ?_⟩
    rw [← hak, map_add, show π k = 0 from hK (by simpa [KF] using hk),
      add_zero, hπa]
  have hsaturated : rectifiedLift A π α + V =
      rectifiedLift (A + KF) π α := by
    simpa [V, KF] using rectifiedLift_add_vertical A π α houter K hK
  have hleft :
      ((rectifiedLift A π α + rectifiedLift A π α) + V).card =
        (rectifiedLift (A + KF) π α +
          rectifiedLift (A + KF) π α).card := by
    rw [add_self_add_vertical_eq_saturated_add_self]
    rw [hsaturated]
  have hcard := card_add_rectifiedLift (A + KF) π α houterSat
  have hKK : KF + KF = KF := by
    ext x
    constructor
    · intro hx
      obtain ⟨a, ha, b, hb, rfl⟩ := Finset.mem_add.mp hx
      apply (mem_addSubgroupFinset K (a + b)).mpr
      exact K.add_mem ((mem_addSubgroupFinset K a).mp ha)
        ((mem_addSubgroupFinset K b).mp hb)
    · intro hx
      exact Finset.mem_add.mpr ⟨x, hx, 0,
        (mem_addSubgroupFinset K 0).mpr K.zero_mem, by simp⟩
  have hsum : (A + KF) + (A + KF) = (A + A) + KF := by
    calc
      (A + KF) + (A + KF) = (A + A) + (KF + KF) := by
        ext x
        simp only [Finset.mem_add]
        constructor
        · rintro ⟨ak, ⟨a, ha, k, hk, rfl⟩, bl, ⟨b, hb, l, hl, rfl⟩, rfl⟩
          exact ⟨a + b, ⟨a, ha, b, hb, rfl⟩, k + l,
            ⟨k, hk, l, hl, rfl⟩, by abel⟩
        · rintro ⟨ab, ⟨a, ha, b, hb, rfl⟩, kl,
              ⟨k, hk, l, hl, rfl⟩, rfl⟩
          exact ⟨a + k, ⟨a, ha, k, hk, rfl⟩, b + l,
            ⟨b, hb, l, hl, rfl⟩, by abel⟩
      _ = (A + A) + KF := by rw [hKK]
  rw [hleft, hcard, hsum]

/-- Affine generation is invariant under translating a finite set. -/
theorem finsetAffineGenerates_vadd
    (A : Finset (ZMod N)) (p : ZMod N) (hA : FinsetAffineGenerates A) :
    FinsetAffineGenerates (-p +ᵥ A) := by
  intro K b hsub
  apply hA K (b + p)
  intro x hx
  have hy : -p + x ∈ -p +ᵥ A :=
    Finset.mem_vadd_finset.mpr ⟨x, hx, rfl⟩
  have hm := hsub (-p + x) hy
  convert hm using 1 <;> abel

/-- A rank certificate for a translate transfers back to the original set. -/
theorem finsetRankCertificate_of_translate
    (A : Finset (ZMod N)) (p : ZMod N)
    (hcert : FinsetRankCertificate (-p +ᵥ A)) :
    FinsetRankCertificate A := by
  obtain ⟨q, hq, ρ, hρ, β, L, V, hL, houter, hfiber, hcost⟩ := hcert
  refine ⟨q, hq, ρ, hρ, β + ρ p, L, V, hL, ?_, hfiber, ?_⟩
  · intro x hx
    have hy : -p + x ∈ -p +ᵥ A :=
      Finset.mem_vadd_finset.mpr ⟨x, hx, rfl⟩
    obtain ⟨k, hkL, hk⟩ := houter (-p + x) hy
    refine ⟨k, hkL, ?_⟩
    rw [map_add, map_neg] at hk
    calc
      ρ x = ρ p + (-ρ p + ρ x) := by abel
      _ = (β + ρ p) + (k : ZMod q) := by rw [hk]; abel
  · rw [Finset.card_vadd_finset] at hcost
    rw [card_translate_double A p] at hcost
    exact hcost

end Erdos336
