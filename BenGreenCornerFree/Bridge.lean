import Mathlib.Tactic
import Mathlib.Data.List.ToFinsupp
import Mathlib.Order.SuccPred.IntervalSucc

import BenGreenCornerFree.Construction
import BenGreenCornerFree.Mathlib.Analysis.Asymptotics.Asymptotics

namespace BenGreen.Bridge

open Int hiding range
open Finset BigOperators Filter Asymptotics
open BenGreen Construction

/- #eval (A (d := 2) (q := 5) 5) -/
/- #eval (univ : Finset (Vec' 2 5)).map VecToInt -/
/- #eval (A (d := 2) (q := 5) 5).map VecPairToInt -/
/- #eval AddCornerFree ((A (d := 2) (q := 5) 5).map VecPairToInt : Set (ℤ × ℤ)) -/
/-  -/
/- #check List.map -/
/- #eval List.map (fun r ↦ (A (d := 2) (q := 5) r).card) (List.range 51) -/

-- The set of all pairs (x, y) with q/2 ⩽ x + y < 3q/2 has size 3/4*q^2 + O(q)
-- Might delete later (Yes this is a Cole reference)
def aux1_type (q m n : ℤ) : Finset ((Ico 0 q) × (Ico 0 q)) :=
    univ.filter (fun v ↦ v.fst.val + v.snd.val ∈ Ico m n)

@[simp 90] theorem mem_aux1_type_iff {q m n : ℤ} {v : (Ico 0 q) × (Ico 0 q)} :
    v ∈ aux1_type q m n ↔ v.fst.val + v.snd.val ∈ Ico m n := by
  simp [aux1_type, mem_filter]

theorem mem_aux1_type_double {q : ℤ} {v} : v ∈ aux1_type q 0 (2 * q - 1) := by
  rcases v with ⟨⟨x, hx⟩, ⟨y, hy⟩⟩
  simp at hx hy ⊢
  omega

theorem Int.le_of_lt_succ {x a : Int} (h : x < a.succ) : x ≤ a := Int.le_of_add_le_add_right h

theorem Int.lt_succ_of_le {x a : Int} (h : x ≤ a) : x < a.succ := Int.add_le_add_right h 1

theorem Int.lt_succ_iff' {x a : Int} : x < a.succ ↔ x ≤ a := ⟨Int.le_of_lt_succ, Int.lt_succ_of_le⟩

lemma Int.mem_Ico_succ {a x : ℤ} : x ∈ Ico a a.succ ↔ a = x := by
  rw [mem_Ico]
  constructor <;> intro h
  · exact Int.eq_iff_le_and_ge.mpr ⟨h.left, Int.le_of_lt_succ h.right⟩
  · simpa [h] using lt_succ_self _

@[simp 100] theorem mem_aux1_type_succ_iff (q m : ℤ) (v : (Ico 0 q) × (Ico 0 q)) :
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
      · apply mem_of_subset _ hx
        rw [Icc_subset_Ico_iff hm₁]
        omega
      · have : m - x ∈ Icc 0 m := by simp [mem_Icc, hx, mem_Icc.mp hx]
        apply mem_of_subset _ this
        rw [Icc_subset_Ico_iff hm₁]
        omega
      · simp
    · intro ⟨⟨x, y⟩, h⟩
      simp at h ⊢
      simp_rw [← h]
      ring_nf
    · intro; simp
  have := Fintype.card_congr this
  rw [Fintype.card_coe, Fintype.card_coe, card_Icc, sub_zero] at this
  rw [this, toNat_of_nonneg (by omega)]

lemma aux_slice2 {q m} (hm₁ : m ≤ 2 * q - 2) (hm₂ : q - 1 ≤ m):
    (aux1_type q m m.succ).card = 2 * q - m - 1 := by
  have : aux1_type q m m.succ ≃ aux1_type q (2 * q - m - 2) (2 * q - m - 2).succ := by
    refine ⟨?_, ?_, ?_, ?_⟩ <;> intro ⟨⟨x, y⟩, h⟩
    any_goals
      /- first two goals -/
      use ⟨⟨q - 1 - x.val, ?_⟩, ⟨q - 1 - y.val, ?_⟩⟩, ?_
      · have ⟨h₁, h₂⟩ := mem_Ico.mp x.prop; rw [mem_Ico]; constructor <;> linarith
      · have ⟨h₁, h₂⟩ := mem_Ico.mp y.prop; rw [mem_Ico]; constructor <;> linarith
      · simp_rw [mem_aux1_type_succ_iff] at h ⊢
        ring_nf
        rw [← neg_add', h]
        ring
    all_goals
      /- remaining two goals -/
      ext <;> simp only <;> ring
  have := Fintype.card_congr this
  simp_rw [Fintype.card_coe] at this
  rw [this, aux_slice1]
  · ring
  · linarith
  · linarith

lemma aux_slice_bound {q m} (hq : 0 ≤ q) :
    (aux1_type q m m.succ).card ≤ q := by
  by_cases hm : m ≤ q - 1
  · by_cases hm' : 0 ≤ m
    · rw [aux_slice1] <;> omega
    · convert hq
      simp only [Nat.cast_eq_zero, card_eq_zero]
      ext ⟨⟨x, hx⟩, ⟨y, hy⟩⟩
      simp only [mem_aux1_type_succ_iff, not_mem_empty, iff_false]
      have := mem_Ico.mp hx
      have := mem_Ico.mp hy
      omega
  · by_cases hm' : m ≤ 2 * q - 2
    · rw [aux_slice2] <;> omega
    · convert hq
      simp only [Nat.cast_eq_zero, card_eq_zero]
      ext ⟨⟨x, hx⟩, ⟨y, hy⟩⟩
      simp only [mem_aux1_type_succ_iff, not_mem_empty, iff_false]
      have := mem_Ico.mp hx
      have := mem_Ico.mp hy
      omega

def aux_triangle {q a b} :
    aux1_type q a b ≃ Σ k : Ico a b, aux1_type q k.val k.val.succ := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro ⟨⟨x, y⟩, h⟩
    exact ⟨⟨x.val + y.val, mem_aux1_type_iff.mp h⟩, ⟨⟨x, y⟩, by simp⟩⟩
  · intro ⟨⟨k, hk⟩, ⟨⟨x, y⟩, h⟩⟩
    simp at h hk ⊢
    exact ⟨⟨x, y⟩, (by simp only at h ⊢; omega)⟩
  · intro ⟨⟨x, y⟩, h⟩; simp
  · intro ⟨⟨k, hk⟩, ⟨⟨x, y⟩, h⟩⟩; ext <;> simp; simpa using h

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

lemma lt_div_mul_add_pos (a b : ℕ) (hb : 0 < b) : a < a / b * b + b := by
  nth_rw 2 [← Nat.div_add_mod' a b, mul_comm _ b]
  rw [Nat.mul_add_div hb, add_mul, add_rotate]
  nth_rw 1 [← Nat.div_add_mod' a b, add_comm]
  apply add_lt_add_right $ Nat.lt_add_left _ $ Nat.mod_lt _ hb

lemma lem (a : ℕ) (b : ℤ) :
    (-a.succ : ℤ) / b = if b = 0 then 0 else if b > 0 then -(a / b).succ else (a / abs b).succ := by
  rw [Int.div_def, ediv, Nat.succ_eq_add_one, Nat.cast_add, Nat.cast_one, ← negSucc_eq]
  match b with
  | 0 => simp
  | ofNat (.succ n) => simp [show (n : ℤ) + 1 ≠ 0 by omega, negSucc_eq, Int.succ]
  | -[n+1] => split_ifs; any_goals tauto

def aux_type_mirror {a b q : ℤ} :
    aux1_type q a b ≃ aux1_type q (2 * q - 1 - b) (2 * q - 1 - a) where
  toFun := fun ⟨⟨⟨x, hx⟩, ⟨y, hy⟩⟩, h⟩ ↦ by
    use ⟨⟨q - 1 - x, ?_⟩, ⟨q - 1 - y, ?_⟩⟩, ?_
    all_goals simp [mem_Ico] at hx hy h ⊢; omega
  invFun := fun ⟨⟨⟨x, hx⟩, ⟨y, hy⟩⟩, h⟩ ↦ by
    use ⟨⟨q - 1 - x, ?_⟩, ⟨q - 1 - y, ?_⟩⟩, ?_
    all_goals simp [mem_Ico] at hx hy h ⊢; omega
  left_inv := fun ⟨⟨⟨_, _⟩, ⟨_, _⟩⟩, _⟩ ↦ by congr! <;> omega
  right_inv := fun ⟨⟨⟨_, _⟩, ⟨_, _⟩⟩, _⟩ ↦ by congr! <;> omega

theorem todo (a b : ℤ) : (a / b - 1 : ℚ) ≤ (a / b : ℤ) := by
  obtain ⟨b, rfl | rfl⟩ := Int.eq_nat_or_neg b
  · by_cases hb : b = 0
    · subst hb; simp
    · rw [sub_le_iff_le_add, div_le_iff]
      apply le_of_lt
      norm_cast
      apply lt_ediv_add_one_mul_self _ _
      all_goals norm_cast; omega
  · by_cases hb : b = 0
    · subst hb; simp
    · rw [sub_le_iff_le_add, div_le_iff_of_neg (by simp; omega), Int.ediv_neg, cast_neg, cast_neg,
        cast_natCast, add_mul, neg_mul_neg, one_mul, add_neg_le_iff_le_add]
      trans (a : ℚ)
      · norm_cast; exact Int.ediv_mul_le _ (by norm_cast)
      · simp

theorem todo' {a b : ℤ} (hb : 0 ≤ b) : (a / b : ℤ) ≤ (a / b : ℚ) := by
  rcases hb.eq_or_lt with (rfl | hb)
  · simp
  · rw [le_div_iff (by norm_cast), ← cast_mul, cast_le]
    exact Int.ediv_mul_le _ hb.ne.symm

/- theorem Int.mul_add_div {m : Int} (hm : m ≠ 0) (x y : Int) : (m * x + y) / m = x + y / m := by -/
/-   rw [add_comm, add_mul_ediv_left _ _ hm, add_comm] -/
/-  -/
/- lemma succ_div_le_div_succ (a b : ℕ) : a.succ / b ≤ (a / b).succ := by -/
/-   match b with -/
/-   | 0 => simp -/
/-   | 1 => simp [Nat.mod_one] -/
/-   | .succ (.succ b) => -/
/-     simp_rw [Nat.succ_eq_add_one, Nat.add_div (by omega : 0 < b + 1 + 1)] -/
/-     split_ifs <;> simp [show 1 / (b + 1 + 1) = 0 by rw [(Nat.div_eq_zero_iff ?_).mpr] <;> omega] -/

/- [a, b) - [c, d) = [a, c) + [d, b) -/
lemma asdf {a b c d : ℤ} (h : max a c < min b d) :
    Ico a b \ Ico c d = Ico a (max a c) ∪ Ico (min b d) b := by
  rw [← sdiff_inter_self_left, Ico_inter_Ico]
  have : Ico a b = Ico a (max a c) ∪ Ico (max a c) (min b d) ∪ Ico (min b d) b := by
    rw [Ico_union_Ico, Ico_union_Ico] <;> congr <;> omega
  rw [this, union_right_comm, union_sdiff_cancel_right]
  apply disjoint_union_left.mpr ⟨?_, ?_⟩
  all_goals
    rw [disjoint_iff_inter_eq_empty, Ico_inter_Ico, Ico_eq_empty_iff]
    omega

/- Error term from applying to IsInCons -/
lemma aux_error (q a b a' b' : ℤ) (hq : 0 ≤ q)
    (h : max a a' < min b b') (ha : |a - a'| ≤ 1) (hb : |b - b'| ≤ 1) :
    |(((aux1_type q a b).card - (aux1_type q a' b').card) : ℝ)| ≤ 4 * q := by
  rw [abs_le] at ha hb
  rw [aux_triangle', aux_triangle', Nat.cast_sum, Nat.cast_sum, ← sum_sdiff_sub_sum_sdiff]
  have h₁ : (Ico a b \ Ico a' b').card ≤ 2 := by
    rw [asdf h, card_union_of_disjoint, ← one_add_one_eq_two]
    apply add_le_add
    · simp; omega
    · simp; omega
    · rw [disjoint_iff_inter_eq_empty, Ico_inter_Ico, Ico_eq_empty_iff]; omega
  have h₂ : (Ico a' b' \ Ico a b).card ≤ 2 := by
    rw [max_comm, min_comm] at h
    rw [asdf h, card_union_of_disjoint, ← one_add_one_eq_two]
    apply add_le_add
    · simp; omega
    · simp; omega
    · rw [disjoint_iff_inter_eq_empty, Ico_inter_Ico, Ico_eq_empty_iff]; omega
  rw [show 4 * (q : ℝ) = 2 * q + 2 * q by ring]
  apply (abs_sub _ _).trans
  apply add_le_add
  all_goals
    apply (abs_sum_le_sum_abs _ _).trans
    apply (sum_le_sum (g := fun _ ↦ (q : ℝ)) _).trans
    · rw [sum_const, nsmul_eq_mul]; gcongr; norm_cast
    · intro x _; simp; norm_cast; exact aux_slice_bound hq

lemma aux_lower_bound {b : ℤ} (hb : 4 ≤ b) :
    ((b : ℚ) - 2) * (b - 4) / 8 - 1 ≤ ((b / 2) * (b / 2 - 1) / 2 : ℤ) := by
  calc ((b : ℚ) - 2) * (b - 4) / 8 - 1
    _ = ((b / 2 - 1) * ((b / 2 - 1) - 1)) / 2 - 1 := by ring
    _ ≤ ((b / 2 : ℤ) * ((b / 2 : ℤ) - 1)) / 2 - 1 := by
      gcongr
      · linarith [show 4 ≤ (b:ℚ) by exact_mod_cast hb]
      · apply todo
      · apply todo
    _ ≤ ((b / 2) * (b / 2 - 1) : ℤ) / 2 - 1 := by simp
    _ ≤ ((b / 2) * (b / 2 - 1) / 2 : ℤ) := todo ..

lemma aux_upper_bound {b : ℤ} (hb : 4 ≤ b) :
    ((b / 2) * (b / 2 - 1) / 2 : ℤ) ≤ ((b : ℚ) / 2) * (b / 2 - 1) / 2 := by
  calc
    _ ≤ ((b / 2) * (b / 2 - 1) : ℤ) / (2 : ℚ) := todo' zero_le_two
    _ ≤ (b / 2 : ℤ) * (b / 2 - 1 : ℤ) / 2 := by rw [cast_mul]
    _ ≤ _ := by
      gcongr
      · norm_cast; omega
      · exact todo' zero_le_two
      · simp; exact todo' zero_le_two

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
  . apply IsBigO.of_bound 1
    simp only [Real.norm_eq_abs, eventually_atTop, ge_iff_le]
    use 4, fun b hb ↦ ?_
    conv in ∑ __ in _, _ - _ =>
      rw [← cast_sum, Int.sum_Ico_id (by omega), zero_add, sub_zero]
    rw [norm_eq_abs, abs_eq_self.mpr (show 0 ≤ (b : ℝ) by norm_cast; omega), abs_le]
    constructor
    · trans ((b : ℝ) - 2) * (b - 4) / 8 - 1 - b ^ 2 / 8
      · ring_nf
        rw [neg_le_iff_add_nonneg, ← mul_add_one]
        norm_num
        omega
      · apply sub_le_sub_right
        have := Rat.cast_intCast (α := ℝ) _ ▸ ((Rat.cast_le (K := ℝ)).mpr (aux_lower_bound hb))
        convert this
        norm_cast
    · trans ((b : ℝ) / 2) * (b / 2 - 1) / 2 - (b : ℝ) ^ 2 / 8
      · apply sub_le_sub_right
        have := Rat.cast_intCast (α := ℝ) _ ▸ ((Rat.cast_le (K := ℝ)).mpr (aux_upper_bound hb))
        convert this
        norm_cast
      · ring_nf
        rw [neg_div, mul_neg, neg_le_iff_add_nonneg, ← mul_one_add]
        norm_num
        omega
  . apply isBigO_of_le _ (fun x ↦ ?_)
    rw [RCLike.norm_natCast, norm_eq_abs, ← cast_abs]
    norm_cast
    cases' Int.le_total 0 x with h h
    · rw [abs_eq_self.mpr h, toNat_of_nonneg]
      all_goals omega
    · rw [abs_of_nonpos h, toNat_of_nonpos]
      all_goals omega

lemma aux_triangle2_mirror {q : ℤ} :
    (aux1_type q (3 * q / 2) (2 * q - 1)).card = (aux1_type q 0 ((q - 1) / 2)).card :=
  card_eq_of_equiv (by convert aux_type_mirror using 5 <;> omega)

lemma aux_triangle2 :
    (fun q ↦ ((aux1_type q (3 * q / 2) (2 * q - 1)).card : ℝ) - (q : ℝ) ^ 2 / 8)
      =O[atTop] (fun q ↦ q) := by
  simp_rw [aux_triangle2_mirror]
  have h₃ : (fun q ↦ ((aux1_type q 0 ((q - 1) / 2)).card : ℝ) -
      (aux1_type q 0 (q / 2)).card) =O[atTop] (fun q ↦ q) := by
    refine isBigO_iff_isBigOWith.mpr ⟨4, ?_⟩
    rw [IsBigOWith]
    simp only [eventually_atTop, norm_eq_abs]
    refine ⟨3, fun q hq ↦ ?_⟩
    rw [abs_of_nonneg (by norm_cast; omega), Real.norm_eq_abs]
    apply aux_error
    all_goals
      try rw [abs_le]
      omega
  simpa using h₃.add aux_triangle1

lemma aux_triangle3 {q : ℤ} (hq : 0 ≤ q) : (aux1_type q 0 (2 * q - 1)).card = q ^ 2 := calc
  _ = ((univ : Finset (Ico 0 q × Ico 0 q)).card : ℤ) := by
    norm_cast
    apply Finset.card_eq_of_equiv
    simp only [mem_univ, mem_aux1_type_double]
    rfl
  _ = _ := by
    rw [card_univ, Fintype.card_prod, Fintype.card_coe, card_Ico, sub_zero, Nat.cast_mul,
      toNat_of_nonneg hq, sq]

def mem_aux1_type_union {q a b c : ℤ} (hab : a ≤ b) (hbc : b ≤ c) :
    ∀ x, (x ∈ aux1_type q a b ∪ aux1_type q b c) ↔ x ∈ aux1_type q a c := by
  intro ⟨x, y⟩
  simp
  constructor <;> intro h <;> cases' h <;> omega

lemma aux_triangles_union (q : ℤ) (hq : 1 ≤ q) :
    ((aux1_type q 0 (q / 2)).card + (aux1_type q (q / 2) (3 * q / 2)).card
      + (aux1_type q (3 * q / 2) (2 * q - 1)).card : ℤ) = q ^ 2 := by
  rw [← aux_triangle3 (zero_le_one.trans hq)]
  rw [← Nat.cast_add, ← Nat.cast_add, ← card_union_of_disjoint, ← card_union_of_disjoint]
  norm_cast
  · apply Finset.card_eq_of_equiv
    trans { x // x ∈ aux1_type q 0 (3 * q / 2) ∪ aux1_type q (3 * q / 2) (2 * q - 1) }
    · apply Equiv.subtypeEquivRight
      simp_rw [mem_union (t := aux1_type q (3 * q / 2) (2 * q - 1))]
      exact fun x ↦ or_congr_left $ mem_aux1_type_union (by omega) (by omega) x
    · exact Equiv.subtypeEquivRight $ mem_aux1_type_union (by omega) (by omega)
  · simp_rw [disjoint_union_left, disjoint_iff_ne]
    constructor
    all_goals
      intro ⟨x, y⟩ h ⟨x', y'⟩ h'
      simp at h h'
      by_contra!
      obtain ⟨hx, hy⟩ := Prod.mk.injEq _ _ _ _ ▸ this
      subst hx hy
      omega
  · rw [disjoint_iff_ne]
    intro ⟨x, y⟩ h ⟨x', y'⟩ h'
    simp at h h'
    by_contra!
    obtain ⟨hx, hy⟩ := Prod.mk.injEq _ _ _ _ ▸ this
    subst hx hy
    omega

lemma aux_triangles_union_real (q : ℤ) (hq : 1 ≤ q) :
    (aux1_type q 0 (q / 2)).card + (aux1_type q (q / 2) (3 * q / 2)).card
      + (aux1_type q (3 * q / 2) (2 * q - 1)).card = (q : ℝ) ^ 2 := by
  simp_rw [← cast_natCast (R := ℝ), ← cast_add]
  rw [aux_triangles_union q hq]
  exact cast_pow q 2

lemma aux_triangle12 :
    (fun q ↦ (aux1_type q 0 (q / 2)).card + (aux1_type q (3 * q / 2) (2 * q - 1)).card
      - (q : ℝ) ^ 2 / 4) =O[atTop] (fun q ↦ q) := by
  convert aux_triangle1.add aux_triangle2 using 2 with q
  ring

lemma aux_triangle3' :
    (fun q : ℤ ↦ (q : ℝ) ^ 2 * 3 / 4 - (aux1_type q (q / 2) (3 * q / 2)).card)
      =O[atTop] (fun q ↦ q) := by
  apply EventuallyEq.trans_isBigO _ aux_triangle12
  rw [EventuallyEq, eventually_atTop]
  use 1
  intro q hq
  rw [sub_eq_iff_eq_add, sub_add_eq_add_sub, add_right_comm, aux_triangles_union_real q hq]
  ring

lemma aux2 :
    (fun q ↦ ((aux1_type q (q / 2) (3 * q / 2)).card : ℝ) - (q : ℝ) ^ 2 * 3 / 4)
      =O[atTop] (fun q ↦ q) := by
  rw [← isBigO_neg_iff]
  apply EventuallyEq.trans_isBigO _ aux_triangle12
  rw [EventuallyEq, eventually_atTop]
  use 1
  intro q hq
  rw [Pi.neg_apply, neg_sub, sub_eq_iff_eq_add, sub_add_eq_add_sub, add_right_comm,
    aux_triangles_union_real q hq]
  ring

lemma card_cast_sub_eq_sdiff_card_sub_sdiff_card {α : Type*} [DecidableEq α] {s t : Finset α} :
    (s.card : ℝ) - (t.card : ℝ) = (s \ t).card - (t \ s).card := by
  rw [sub_eq_sub_iff_add_eq_add]
  norm_cast
  simp_rw [add_comm s.card _, card_sdiff_add_card, union_comm]

/- #check IsInCons -/

lemma aux_isInCons_rw1 {x q : ℤ} : q ≤ 2 * x ↔ (q + 1) / 2 ≤ x := by omega

lemma aux_isInCons_rw2 {x q : ℤ} : 2 * x + 1 ≤ 3 * q ↔ x < (3 * q + 1) / 2 := by omega

/- def aux_isInCons_embed {q r : ℕ} : -/
/-     @A d q r ↪ (Fin d → aux1_type q ((q + 1) / 2) ((3 * q + 1) / 2)) where -/
/-   toFun := fun ⟨⟨⟨x, hx⟩, ⟨y, hy⟩⟩, h⟩ i ↦ by -/
/-     rw [mem_A_iff, IsInCons] at h -/
/-     use ⟨⟨x i, ?_⟩, ⟨y i, ?_⟩⟩, ?_ -/
/-     · have := And.intro (hx.left i) (hx.right i); simpa [mem_Ico] -/
/-     · have := And.intro (hy.left i) (hy.right i); simpa [mem_Ico] -/
/-     · have := And.intro (h.right.left i) (h.right.right i); simp at this ⊢; omega -/
/-   inj' := fun ⟨⟨x, y⟩, h⟩ ⟨⟨x', y'⟩, h'⟩ h_eq ↦ by -/
/-     simp at h_eq ⊢ -/
/-     constructor -/
/-     all_goals -/
/-       ext i -/
/-       replace h_eq := congrFun h_eq i -/
/-       simp at h_eq -/
/-       tauto -/

lemma aux2' :
    (fun q ↦ ((aux1_type q ((q + 1) / 2) ((3 * q + 1) / 2)).card : ℝ) - (q : ℝ) ^ 2 * 3 / 4)
      =O[atTop] (fun q ↦ q) := by
  have h₃ : (fun q ↦ ((aux1_type q ((q + 1) / 2) ((3 * q + 1) / 2)).card : ℝ)
      - (aux1_type q (q / 2) (3 * q / 2)).card) =O[atTop] (fun q ↦ q) := by
    refine isBigO_iff_isBigOWith.mpr ⟨4, ?_⟩
    rw [IsBigOWith]
    simp only [eventually_atTop, norm_eq_abs]
    refine ⟨2, fun q hq ↦ ?_⟩
    rw [abs_of_nonneg (by norm_cast; omega), Real.norm_eq_abs]
    apply aux_error
    all_goals
      try rw [abs_le]
      omega
  simpa using h₃.add aux2

lemma A_empty {d q r : ℕ} (hr : d * (q - 1) ^ 2 < r) : @A d q r = ∅ := by
  rcases Nat.eq_zero_or_pos d with (rfl | h') <;> ext ⟨⟨x, hx⟩, ⟨y, hy⟩⟩
  · simp [norm'] at hr ⊢; omega
  · have : 1 ≤ (q : ℤ) := by
      have := And.intro (hx.left ⟨0, h'⟩) (hx.right ⟨0, h'⟩)
      simp at this
      omega
    simp_rw [mem_A_iff, not_mem_empty, IsInCons, iff_false, norm', Pi.sub_apply, not_and_or]
    left
    contrapose! hr
    zify
    rw [← hr]
    have h' (i) : (x i - y i) ^ 2 ≤ ((q : ℤ) - 1) ^ 2 := by
      have := And.intro (And.intro (hx.left i) (hx.right i)) (And.intro (hy.left i) (hy.right i))
      simp at this ⊢
      rw [sq_le_sq, abs_le, abs_of_nonneg (by omega)]
      omega
    apply (sum_le_sum (fun i _ ↦ h' i)).trans
    rw [sum_const, nsmul_eq_mul]
    gcongr
    · simp
    · omega
    · simp [Nat.cast_sub (by norm_cast at this : 1 ≤ q)]

def aux_isInCons_embed {d q : ℕ} (hd : 0 < d) :
    (Σ r : Fin (d * q ^ 2), @A d q r) ≃ (Fin d → aux1_type q ((q + 1) / 2) ((3 * q + 1) / 2)) where
  toFun := fun ⟨r, ⟨⟨⟨x, hx⟩, ⟨y, hy⟩⟩, hxy⟩⟩ i ↦ by
    use ⟨⟨x i, ?_⟩, ⟨y i, ?_⟩⟩, ?_
    · exact mem_Ico.mpr ⟨hx.left i, hx.right i⟩
    · exact mem_Ico.mpr ⟨hy.left i, hy.right i⟩
    · simp at hxy ⊢
      have := And.intro (hxy.right.left i) (hxy.right.right i)
      simp at this
      omega
  invFun := fun f ↦ by
    let r := norm' (fun i ↦ ((f i).val.fst.val - (f i).val.snd.val))
    have h₁ : 0 ≤ r := norm'_nonneg _
    have h₂ : r < d * q ^ 2 := by
      have h₁ (i) := (f i).val.fst.prop
      have h₂ (i) := (f i).val.snd.prop
      have h (i) : ((f i).val.fst.val - (f i).val.snd.val) ^ 2 ∈ Ico 0 ((q : ℤ) ^ 2) := by
        specialize h₁ i; specialize h₂ i
        rw [mem_Ico] at h₁ h₂ ⊢
        refine ⟨sq_nonneg _, ?_⟩
        rw [sq_lt_sq, abs_of_nonneg (h₁.left.trans h₁.right.le), abs_lt]
        omega
      dsimp [r, norm']
      apply lt_of_lt_of_le $ sum_lt_sum (fun i _ ↦ (mem_Ico.mp (h i)).right.le) ?_
      · simp
      · exact ⟨_, ⟨mem_univ _, (mem_Ico.mp (h ⟨0, hd⟩)).right⟩⟩
    use ⟨r.natAbs, by zify; rwa [abs_of_nonneg h₁]⟩,
      ⟨⟨fun i ↦ (f i).val.fst.val, ?_⟩, ⟨fun i ↦ (f i).val.snd.val, ?_⟩⟩, ?_
    · simp [Pi.le_def]
      have (i) := mem_Ico.mp (f i).val.fst.prop
      exact ⟨fun i ↦ (this i).left, fun i ↦ (this i).right⟩
    · simp [Pi.le_def]
      have (i) := mem_Ico.mp (f i).val.snd.prop
      exact ⟨fun i ↦ (this i).left, fun i ↦ (this i).right⟩
    · simp
      use ?_, ?_, ?_
      · rw [abs_of_nonneg h₁]; rfl
      · simp [Pi.le_def]
        intro i
        have := mem_Ico.mp $ mem_aux1_type_iff.mp (f i).prop
        omega
      · simp [Pi.le_def]
        intro i
        have := mem_Ico.mp $ mem_aux1_type_iff.mp (f i).prop
        omega
  left_inv := fun ⟨r, ⟨⟨⟨x, hx⟩, ⟨y, hy⟩⟩, hxy⟩⟩ ↦ by
    ext <;> try rfl
    zify
    simp at hxy
    rw [abs_of_nonneg $ norm'_nonneg _]
    exact hxy.left
  right_inv := fun f ↦ rfl

lemma A_empty' {d q r : ℕ} (hd : 0 < d) (hq : 0 < q) (hr : d * q ^ 2 ≤ r) : @A d q r = ∅ :=
  A_empty $ lt_of_lt_of_le (by gcongr; omega) hr

/- def aux_isInCons_embed (hd : 0 < d) : -/
/-     (Σ r : Fin (d * q ^ 2), @A d q r) ≃ (Fin d → aux1_type q ((q + 1) / 2) ((3 * q + 1) / 2)) where -/

-- The Σ-type (Σ r, A r) has size (3/4*q^2 + O(q))^d
theorem part2 {d : ℕ} (hd : 0 < d) : ∃ f : ℤ → ℝ, f =O[atTop] (fun q ↦ q) ∧
    (fun q ↦ (Fintype.card ((r : Fin (d * q ^ 2)) × @A d q r) : ℝ))
      =ᶠ[atTop] (fun q ↦ (q ^ 2 * 3 / 4 + f q) ^ d) := by
  refine ⟨_, ⟨aux2', ?_⟩⟩
  simp_rw [cast_natCast, add_sub_cancel, EventuallyEq, eventually_atTop]
  use 1
  intro q _
  norm_cast
  convert Fintype.ofEquiv_card $ (aux_isInCons_embed hd (q := q)).symm
  rw [Fintype.card_pi, prod_const, card_univ, Fintype.card_fin, Fintype.card_coe]
  rfl
