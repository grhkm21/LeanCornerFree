import Mathlib.Tactic
import Mathlib.Data.List.ToFinsupp
import Mathlib.Order.SuccPred.IntervalSucc

import BenGreenCornerFree.Construction

namespace BenGreen.Bridge

open Int hiding range
open Finset BigOperators Filter Asymptotics
open BenGreen Construction

#eval (A (d := 2) (q := 5) 5)
#eval (univ : Finset (Vec' 2 5)).map VecToInt
#eval (A (d := 2) (q := 5) 5).map VecPairToInt
#eval AddCornerFree ((A (d := 2) (q := 5) 5).map VecPairToInt : Set (ℤ × ℤ))

#check List.map
#eval List.map (fun r ↦ (A (d := 2) (q := 5) r).card) (List.range 51)

-- The set of all pairs (x, y) with q/2 ⩽ x + y < 3q/2 has size 3/4*q^2 + O(q)
-- Might delete later (Yes this is a Cole reference)
def aux1_type (q m n : ℤ) : Finset ((Ico 0 q) × (Ico 0 q)) :=
    univ.filter (fun v ↦ v.fst.val + v.snd.val ∈ Ico m n)

theorem mem_aux1_type_iff {q m n : ℤ} {v : (Ico 0 q) × (Ico 0 q)} :
    v ∈ aux1_type q m n ↔ v.fst.val + v.snd.val ∈ Ico m n := by
  simp [aux1_type, mem_filter]

theorem Int.le_of_lt_succ {x a : Int} (h : x < a.succ) : x ≤ a := Int.le_of_add_le_add_right h

theorem Int.lt_succ_of_le {x a : Int} (h : x ≤ a) : x < a.succ := Int.add_le_add_right h 1

theorem Int.lt_succ_iff' {x a : Int} : x < a.succ ↔ x ≤ a := ⟨Int.le_of_lt_succ, Int.lt_succ_of_le⟩

lemma Int.mem_Ico_succ {a x : ℤ} : x ∈ Ico a a.succ ↔ a = x := by
  rw [mem_Ico]
  constructor <;> intro h
  · exact Int.eq_iff_le_and_ge.mpr ⟨h.left, Int.le_of_lt_succ h.right⟩
  · simpa [h] using lt_succ_self _

theorem mem_aux1_type_succ_iff (q m : ℤ) (v : (Ico 0 q) × (Ico 0 q)) :
    v ∈ aux1_type q m m.succ ↔ v.fst.val + v.snd.val = m := by
  rw [mem_aux1_type_iff, Int.mem_Ico_succ, eq_comm]

lemma aux_slice1 {q m} (hm₁ : 0 ≤ m) (hm₂ : m ≤ q - 1) : (aux1_type q m m.succ).card = m + 1 := by
  have : (aux1_type q m m.succ) ≃ Icc 0 m := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro ⟨x, hx⟩
      refine ⟨x.fst.val, ?_⟩
      rw [mem_aux1_type_succ_iff] at hx
      have : x.fst.val ≤ m := by linarith [(mem_Ico.mp x.snd.prop).left]
      exact mem_Icc.mpr ⟨(mem_Ico.mp x.fst.prop).left, this⟩
    · intro ⟨x, hx⟩
      refine ⟨⟨⟨x, ?_⟩, ⟨m - x, ?_⟩⟩, ?_⟩
      · sorry
      · sorry
      · sorry
    · sorry
    · sorry
  have := Fintype.card_congr this
  rw [Fintype.card_coe, Fintype.card_coe, card_Icc, sub_zero] at this
  rw [this, toNat_of_nonneg (by omega)]

lemma aux_slice2 {q m} (hm₁ : m ≤ 2 * q - 2) (hm₂ : q - 1 ≤ m):
    (aux1_type q m m.succ).card = 2 * q - m - 1 := by
  have : aux1_type q m m.succ ≃ aux1_type q (2 * q - m - 2) (2 * q - m - 2).succ := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro ⟨⟨x, y⟩, h⟩
      use ⟨⟨q - 1 - x.val, ?_⟩, ⟨q - 1 - y.val, ?_⟩⟩, ?_
      · have ⟨h₁, h₂⟩ := mem_Ico.mp x.prop; rw [mem_Ico]; constructor <;> linarith
      · have ⟨h₁, h₂⟩ := mem_Ico.mp y.prop; rw [mem_Ico]; constructor <;> linarith
      · simp_rw [mem_aux1_type_succ_iff] at h ⊢
        ring_nf
        rw [← neg_add', h, add_sub, sub_eq_add_neg]
    · sorry
    · sorry
    · sorry
  have := Fintype.card_congr this
  rw [Fintype.card_coe, Fintype.card_coe] at this
  rw [this, aux_slice1]
  · ring
  · linarith
  · linarith

lemma aux_triangle {q a b} (h : a < b) :
    aux1_type q a b ≃ Σ k : Ico a b, aux1_type q k.val k.val.succ where
  toFun := _
  invFun := _
  left_inv := _
  right_inv := _

lemma aux_triangle' (q a b) :
    (aux1_type q a b).card = ∑ k in Ico a b, (aux1_type q k k.succ).card := by
  repeat simp_rw [← Fintype.card_coe]
  rw [← sum_coe_sort, ← Fintype.card_sigma]
  apply Fintype.card_congr
  refine { toFun := ?_, invFun := ?_, left_inv := ?_, right_inv := ?_ }
  · intro ⟨⟨x, y⟩, h⟩
    use ⟨x.val + y.val, mem_aux1_type_iff.mp h⟩, ⟨x, y⟩
    rw [mem_aux1_type_succ_iff]
  · intro ⟨i, ⟨⟨x, y⟩, h⟩⟩
    use ⟨x, y⟩
    rw [mem_aux1_type_iff] at h ⊢
    apply mem_of_subset _ h
    rw [Ico_subset_Ico_iff]
    · obtain ⟨hi₁, hi₂⟩ := mem_Ico.mp i.prop
      use hi₁, by rwa [succ, ← lt_iff_add_one_le]
    · exact lt_succ _
  · intro; simp
  · intro ⟨i, ⟨⟨x, y⟩, h⟩⟩
    simp
    constructor
    · rw [mem_aux1_type_succ_iff] at h
      simp [h]
    · congr! 1
      funext a
      simp [mem_aux1_type_succ_iff] at h ⊢
      rw [h]

lemma Int.sum_Ico_id {m n : ℤ} (h : m < n) : ∑ x in Ico m n, x = (n - m) * (m + n - 1) / 2 := by
  apply (Int.ediv_eq_of_eq_mul_left two_ne_zero ?_).symm
  have (m n : ℤ) (h : m ≤ n) : Ico m (n + 1) = insert n (Ico m n) := by
    ext a
    rw [mem_insert, mem_Ico, mem_Ico, Int.lt_add_one_iff, le_iff_lt_or_eq (a := a), and_or_left]
    constructor <;> intro h <;> cases' h with h' h'
    · right; exact h'
    . left; exact h'.right
    · subst h'; right; exact ⟨h, rfl⟩
    · left; exact h'
  apply Int.le_induction ?_ ?_ n h
  · simp [this m m le_rfl, mul_two, add_sub_assoc]
  · intro k hk h'
    simp [this m k (le_trans (le_add_one le_rfl) hk), add_mul, ← h']
    ring_nf

-- TODO: Slim-check?
-- TODO (sec10)
#eval Id.run do
  let mut res := []
  for a in [:60] do
    for b in [:60] do
      let a':=(a:ℤ)-30
      let b':=(b:ℤ)-30
      if (a'/b'-1:ℚ)>(a'/b':ℤ) then
        res← res.cons [a,b]
  res ← res.reverse
  return res

lemma aux_floor_div {a b k : ℤ} (hb : a ≤ b) (hk : 0 < k) :
    ((a : ℚ) - k + 1) / k ≤ (b / k : ℤ) := by
  rw [div_le_iff (by norm_cast), ← add_sub_right_comm, sub_le_iff_le_add]
  norm_cast
  rw [add_one_le_iff]
  apply lt_of_le_of_lt hb
  rw [← add_one_mul, ← Int.ediv_lt_iff_lt_mul hk]
  exact lt_succ _

lemma aux_floor_div' {a b k : ℤ} (hb : a ≤ b) (hk : 0 < k) :
    ((a : ℚ) - k) / k ≤ (b / k : ℤ) := by
  apply le_trans ?_ (aux_floor_div hb hk)
  gcongr
  exact le_add_of_nonneg_right zero_le_one

theorem todo (a b : ℤ) : (a / b - 1 : ℚ) ≤ (a / b : ℤ) := by
  sorry

example {b : ℤ} (hb : 4 ≤ b) :
    ((b : ℚ) - 2) * (b - 4) / 8 - 1 ≤ ((b / 2) * (b / 2 - 1) / 2 : ℤ) := by
  calc  ((b : ℚ) - 2) * (b - 4) / 8 - 1
    _ = ((b / 2 - 1) * ((b / 2 - 1) - 1)) / 2 - 1 := by ring
    _ ≤ ((b / 2 : ℤ) * ((b / 2 : ℤ) - 1)) / 2 - 1 := by
      gcongr
      · linarith [show 4 ≤ (b:ℚ) by exact_mod_cast hb]
      · apply todo
      · apply todo
    _ ≤ ((b / 2) * (b / 2 - 1) : ℤ) / 2 - 1 := by simp
    _ ≤ ((b / 2) * (b / 2 - 1) / 2 : ℤ) := todo ..

lemma aux_triangle1 :
    (fun q ↦ ((aux1_type q 0 (q / 2)).card : ℝ) - (q : ℝ) ^ 2 / 8) =O[atTop] (fun q ↦ q) := by
  conv in ((aux1_type _ 0 _).card : ℝ) =>
    rw [aux_triangle' q 0 (q / 2), Nat.cast_sum,
      sum_congr rfl (β := ℝ) (g := fun x : ℤ ↦ x + 1) (fun x hx ↦ by
        rw [show ∀ a : ℕ, (a : ℝ) = (a : ℤ) by intro; norm_cast, aux_slice1 (mem_Ico.mp hx).left]
        · norm_cast
        · obtain ⟨_, h₂⟩ := mem_Ico.mp hx
          exact le_sub_one_of_lt $ lt_of_lt_of_le h₂ (by omega)
      ), sum_add_distrib, sum_const, nsmul_one, card_Ico, sub_zero]
  simp_rw [add_sub_right_comm]
  apply IsBigO.add
  . apply IsBigO.of_bound (1 / 2)
    simp only [Real.norm_eq_abs, eventually_atTop, ge_iff_le]
    use 2, fun b hb ↦ ?_
    conv in ∑ x in _, _ - _ =>
      rw [← cast_sum, Int.sum_Ico_id (by omega), zero_add, sub_zero]
    sorry
  . apply isBigO_of_le _ (fun x ↦ ?_)
    rw [RCLike.norm_natCast, norm_eq_abs, ← cast_abs]
    norm_cast
    cases' Int.le_total 0 x with h h
    · rw [abs_eq_self.mpr h, toNat_of_nonneg]
      all_goals omega
    · rw [abs_of_nonpos h, toNat_of_nonpos]
      all_goals omega

example {k : ℕ} : ∑ n in range k.succ, n = k * k.succ / 2 := by
  rw [Finset.sum_range_id, Nat.succ_sub_one, mul_comm]

lemma F {α : Type*} (s : Finset α) (f : α → ℤ) :
    (∑ x in s, f x : ℤ) = ∑ x in s, (f x : ℝ) := by
  exact cast_sum s f

lemma aux_triangle2 :
    (fun q ↦ ((aux1_type q (3 * q / 2) (2 * q)).card : ℝ)) =O[atTop] (fun q ↦ (q : ℝ) ^ 2 / 8) := by
  sorry

-- TODO: Link aux_bottom_left and a
lemma aux2 : (fun q ↦ ((aux1_type q (q / 2) (q * 3 / 2)).card : ℝ)) =O[atTop] (fun q ↦ ((q : ℝ) ^ 2 * 3 / 4)) := by
  sorry

#check Filter

-- The set of all pairs (x, y) with q/2 ⩽ x_i + y_i < 3q/2 for all i has size (3/4*q^2 + O(q))^d
/- theorem part2 : -/
