import ErdosProblems.Erdos118.Reused591.WeakPigeon
import ErdosProblems.Erdos118.Reused591.EMUnary
import ErdosProblems.Erdos118.Reused591.K4Core
import ErdosProblems.Erdos118.Reused591.CNFStrong

namespace Erdos118.Reused591

open Ordinal

namespace Erdos591.Schipperus.PieceIndiv

open K4Core

theorem k4_of_relFiniteIndivisible
    {A : Type*} [LinearOrder A]
    (h : EMUnary.RelFiniteIndivisible
      ((· < ·) : A → A → Prop)) :
    FinitelyIndivisible A := by
  intro n hn c
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hn)
  obtain ⟨i, e, he⟩ := h k c
  let f : A ↪o A := OrderEmbedding.ofStrictMono e
    (fun _ _ hab ↦ e.map_rel_iff.mpr hab)
  exact ⟨i, f, he⟩

theorem rawLevel_relFiniteIndivisible (r : ℕ) :
    EMUnary.RelFiniteIndivisible (@WeakPigeon.RawLevelLex r) := by
  intro k c
  exact WeakPigeon.rawLevel_finite_partition r k c

theorem typeLT_Iic {A : Type*} [LinearOrder A] [WellFoundedLT A] (a : A) :
    typeLT (Set.Iic a) = Order.succ (Ordinal.typein LT.lt a) := by
  have hd : Disjoint (Set.Iio a) ({a} : Set A) := by
    rw [Set.disjoint_left]
    rintro x hxa rfl
    exact (lt_irrefl x hxa)
  have hsep : ∀ x ∈ Set.Iio a, ∀ y ∈ ({a} : Set A), x < y := by
    rintro x hx y rfl
    exact hx
  have hu : Set.Iio a ∪ ({a} : Set A) = Set.Iic a := by
    ext x
    constructor
    · rintro (hx | rfl)
      · exact hx.le
      · exact le_rfl
    · exact lt_or_eq_of_le
  rw [← hu, CNFStrong.typeLT_union_of_separated _ _ hd hsep,
    Ordinal.type_Iio_lt]
  have hone : typeLT ({a} : Set A) = 1 := by simp
  rw [hone]
  exact Ordinal.add_one_eq_succ _

theorem not_large_Iic_of_isSuccLimit
    {A : Type*} [LinearOrder A] [WellFoundedLT A]
    (hlim : Order.IsSuccLimit (typeLT A)) (a : A) :
    ¬ Large A (Set.Iic a) := by
  intro hlarge
  have heq := K4Core.typeLT_eq_of_large hlarge
  have hlt : typeLT (Set.Iic a) < typeLT A := by
    rw [typeLT_Iic]
    exact hlim.succ_lt (Ordinal.typein_lt_type LT.lt a)
  exact hlt.ne heq

theorem localTarget_isSuccLimit (n : ℕ) :
    Order.IsSuccLimit
      ((ω : Ordinal.{0}) ^ ((ω : Ordinal.{0}) * (n + 1 : ℕ))) := by
  apply Ordinal.isSuccLimit_opow Ordinal.one_lt_omega0
  exact Ordinal.isSuccLimit_mul_left Ordinal.isSuccLimit_omega0 (by simp)

theorem singleton_not_large_of_isSuccLimit
    {A X : Type} [LinearOrder A] [WellFoundedLT A] [Preorder X]
    (hlim : Order.IsSuccLimit (typeLT A)) (x : X) :
    ¬ Large A ({x} : Set X) := by
  letI : Subsingleton ({x} : Set X) := ⟨fun a b ↦ by
    apply Subtype.ext
    exact a.2.trans b.2.symm⟩
  letI : IsWellOrder ({x} : Set X) ((· < ·)) :=
    Subsingleton.isWellOrder _
  intro hlarge
  have hle : typeLT A ≤ typeLT ({x} : Set X) := by
    rw [Ordinal.type_le_iff']
    exact ⟨hlarge.some.ltEmbedding⟩
  have hone : typeLT ({x} : Set X) = 1 := by simp
  rw [hone] at hle
  have honeLt : (1 : Ordinal) < typeLT A := one_lt_of_isSuccLimit hlim
  exact (not_le_of_gt honeLt) hle

theorem exponent_eq_omega_mul_add_of_le (e : Ordinal.{0}) (k : ℕ)
    (he : e ≤ ω * (k : Ordinal.{0})) :
    ∃ q r : ℕ, e = ω * (q : Ordinal.{0}) + (r : Ordinal.{0}) := by
  rcases he.eq_or_lt with heq | hlt
  · exact ⟨k, 0, by simpa using heq⟩
  · obtain ⟨q, hq, r, hr, her⟩ := Ordinal.lt_mul_iff.mp hlt
    have hqω : q < ω := hq.trans (Ordinal.natCast_lt_omega0 k)
    obtain ⟨q, rfl⟩ := Ordinal.lt_omega0.mp hqω
    obtain ⟨r, rfl⟩ := Ordinal.lt_omega0.mp hr
    exact ⟨q, r, her⟩

/-- Every omega-power whose exponent is bounded by the local block exponent
is finitely indivisible.  This combines Chang's `omega^omega` relation with
the elementary finite-level lexicographic pigeonhole theorem. -/
theorem omegaPower_finitelyIndivisible_of_le
    (h590 : OrdinalCardinalRamsey
      (ω ^ ω : Ordinal.{0}) (ω ^ ω : Ordinal.{0}) 3)
    {D : Type} [LinearOrder D] [WellFoundedLT D]
    (e : Ordinal.{0}) (k : ℕ)
    (hD : typeLT D = ω ^ e)
    (he : e ≤ ω * (k : Ordinal.{0})) :
    FinitelyIndivisible D := by
  obtain ⟨q, r, her⟩ := exponent_eq_omega_mul_add_of_le e k he
  let A := (ω ^ (ω * q) : Ordinal.{0}).ToType
  let R : A → A → Prop := (· < ·)
  let S : WeakPigeon.RawLevel r → WeakPigeon.RawLevel r → Prop :=
    @WeakPigeon.RawLevelLex r
  have hA : EMUnary.RelFiniteIndivisible R :=
    EMUnary.omega_mul_nat_relFiniteIndivisible h590 q
  have hR : EMUnary.RelFiniteIndivisible S :=
    rawLevel_relFiniteIndivisible r
  have hprod : EMUnary.RelFiniteIndivisible (Prod.Lex S R) :=
    hA.prodLex hR
  have htype : Ordinal.type (Prod.Lex S R) =
      Ordinal.type ((· < ·) : D → D → Prop) := by
    calc
      Ordinal.type (Prod.Lex S R) = Ordinal.type R * Ordinal.type S :=
        Ordinal.type_prod_lex R S
      _ = (ω ^ (ω * q) : Ordinal.{0}) * ω ^ r := by
        rw [show Ordinal.type R = (ω ^ (ω * q) : Ordinal.{0}) by
          exact Ordinal.type_toType _, WeakPigeon.rawLevel_type]
      _ = ω ^ ((ω : Ordinal.{0}) * q + r) := by
        rw [← Ordinal.opow_natCast, Ordinal.opow_add]
      _ = ω ^ e := by rw [her]
      _ = Ordinal.type ((· < ·) : D → D → Prop) := by
        simpa [hD] using (show typeLT D = _ from hD).symm
  let iso : (Prod.Lex S R) ≃r ((· < ·) : D → D → Prop) :=
    Classical.choice (Ordinal.type_eq.mp htype)
  exact k4_of_relFiniteIndivisible (hprod.congr iso)

end Erdos591.Schipperus.PieceIndiv



end Erdos118.Reused591
