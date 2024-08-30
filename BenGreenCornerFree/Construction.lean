import Mathlib.Tactic
import Mathlib.Data.List.ToFinsupp

import BenGreenCornerFree.Defs

namespace BenGreen.Construction

open Int Finset BigOperators

/- Make sure this fails because of autoImplicit=false -/
/- example : a + 1 = 2 := by sorry -/

-- Before anything, let us check out the space ℤ_q^d
#check Module
#check Basis.ofVectorSpace

variable {d q r : ℕ}

/- We choose to write Fin d → ℤ instead of Fin d → Fin q
   because Fin q is modulo q and is inconvenient to expres our constraints.
   This is not much better since d - 1 is bad but yeah.
   Also f < g means ∃ x, f x < g x (Pi.lt_def) -/
abbrev Vec (d : ℕ) := Fin d → ℤ
abbrev Vec' (d q : ℕ) := {f : Vec d // 0 ≤ f ∧ f + 1 ≤ q}

lemma VecZeroSingleton {x y : Vec 0} : x = y := by ext a; exfalso; exact Nat.not_lt_zero _ a.prop

lemma Vec'ZeroSingleton {x y : Vec' 0 q} : x = y := by ext; rw [@VecZeroSingleton x y]

def VecEquivFun : Vec' d q ≃ (Fin d → Fin q) where
  toFun := fun ⟨f, ⟨hf₁, hf₂⟩⟩ x ↦ ⟨toNat (f x),
    (toNat_lt $ hf₁ x).mpr $ add_one_le_iff.mp (hf₂ x)⟩
  invFun := fun f ↦ ⟨fun x ↦ f x, ⟨Pi.le_def.mpr fun x ↦ by simp,
    Pi.le_def.mpr fun x ↦ by simp; exact toNat_le.mp (f x).prop⟩⟩
  left_inv := by intro ⟨f, ⟨hf₁, hf₂⟩⟩; ext x; simp [toNat_of_nonneg (hf₁ x)]
  right_inv := by intro f; ext x; simp

instance : Fintype (Vec' q d) := Fintype.ofEquiv _ VecEquivFun.symm

/- TODO: Change casing -/

/- Drop first d' elements -/
def VecTruncate (v : Vec' d q) (d' : Fin d) : Vec' (d - d') q where
  val := fun a ↦ v.val $ (a.addNat d').cast (by omega)
  property := by
    constructor <;> simp only [Pi.natCast_def, Pi.le_def, Pi.zero_apply]
    · exact fun _ ↦ v.prop.left _
    · exact fun _ ↦ v.prop.right _

lemma sum_modEq_sum_mod {α : Type*} [DecidableEq α] {f : α → ℤ} {s : Finset α} {q : ℤ} :
    ∑ i in s, f i ≡ ∑ i in s, (f i % q) [ZMOD q] := by
  induction' s using Finset.induction_on with x s hx ih
  · rfl
  · simp_rw [sum_insert hx]
    gcongr
    exact (Int.mod_modEq _ _).symm

lemma VecToInt_mod_q {v : Vec' d q} (hd : 0 < d) :
    (∑ i, v.val i * q ^ i.val) % q = v.val ⟨0, hd⟩ % q := by
  have : ∀ i, v.val i * q ^ i.val % q = if i = ⟨0, hd⟩ then v.val i % q else 0 := by
    intro ⟨i, hi⟩
    cases i with
    | zero => simp
    | succ n => simp [pow_succ, ← mul_assoc]
  rw [sum_modEq_sum_mod]
  simp [this]

theorem Int.emod_eq_self {a b : ℤ} (ha : 0 ≤ a) (ha' : a < b) : a % b = a := by
  have : a / b = 0 := Int.ediv_eq_zero_of_lt ha ha'
  rw [emod_def, this, mul_zero, sub_zero]

lemma aux (f : Fin d → ℤ) (g : ℤ) (k : Fin d) (N : ℤ)
    (hf : (∑ n, if n = k then g else f n) ≡ (∑ n, f n) [ZMOD N]) : g ≡ f k [ZMOD N] := by
  have {g : Fin d → ℤ} : (∑ n, g n) = g k + (∑ n, if n = k then 0 else g n) := by
    simp_rw [Fintype.sum_eq_add_sum_compl k, if_true, zero_add]
    congr 1
    apply sum_congr rfl fun x hx ↦ ?_
    simp at hx
    simp [hx]
  conv_lhs at hf => rw [this]
  conv_rhs at hf => rw [this]
  simp at hf
  have (n : Fin d) :
      (if n = k then 0 else if n = k then g else f n) = if n = k then 0 else f n := by
    split_ifs <;> simp
  simp_rw [this] at hf
  exact hf.add_right_cancel' _

variable (hq : 0 < q)

def VecToInt : Vec' d q ↪ ℤ where
  toFun := fun v ↦ ∑ i, v.val i * q ^ i.val
  inj' := fun v₁ v₂ hv ↦ by
    ext ⟨i, hi⟩
    revert hi
    induction' i using Nat.strong_induction_on with n ih
    intro hn
    replace ih := fun m h ↦ ih m h (h.trans hn)
    have hmod := congrArg (fun a : ℤ ↦ a % q ^ (n + 1)) hv
    simp only [Pi.natCast_def] at hmod
    conv_lhs at hmod => rw [Finset.sum_int_mod]
    conv_rhs at hmod => rw [Finset.sum_int_mod]
    have hd (i : Fin d) :
        (v₁.val i * (q : ℤ) ^ i.val) % ((q : ℤ) ^ (n + 1))
          = if i = ⟨n, hn⟩ then v₁.val ⟨n, hn⟩ * (q : ℤ) ^ n
              else (v₂.val i * (q : ℤ) ^ i.val) % ((q : ℤ) ^ (n + 1)) := by
      split_ifs with hi
      · subst hi
        have : v₁.val ⟨n, hn⟩ < q := by simpa using v₁.prop.right _
        rw [Int.emod_eq_of_lt]
        · apply mul_nonneg
          · exact v₁.prop.left _
          · positivity
        · apply lt_of_lt_of_le (b := (q : ℤ) * (q : ℤ) ^ n)
          · gcongr
          · nth_rw 1 [← pow_one q, Nat.cast_pow, ← pow_add]
            gcongr (q : ℤ) ^ ?_ <;> linarith
      · by_cases hi : i < ⟨n, hn⟩
        · rw [← ih i ‹_›]
        · have hi : i > ⟨n, hn⟩ := by omega
          have : (q : ℤ) ^ (n + 1) ∣ (q : ℤ) ^ i.val := pow_dvd_pow (q : ℤ) hi
          trans 0
          · rw [← Int.dvd_iff_emod_eq_zero]
            exact dvd_mul_of_dvd_right this _
          · rw [eq_comm, ← Int.dvd_iff_emod_eq_zero]
            exact dvd_mul_of_dvd_right this _
    simp_rw [hd] at hmod
    have := aux _ (v₁.val ⟨n, hn⟩ * (q : ℤ) ^ n) ⟨n, hn⟩ _ hmod
    rw [Int.emod_eq_of_lt] at this
    · change (_ % _) = (_ % _) at this
      rw [Int.emod_eq_of_lt, Int.emod_eq_of_lt] at this
      · simp [hq.ne.symm] at this
        exact this
      · apply mul_nonneg
        · exact v₂.prop.left _
        · positivity
      · have : v₂.val ⟨n, hn⟩ < q := by simpa using v₂.prop.right ⟨n, hn⟩
        apply lt_of_lt_of_le (b := (q : ℤ) * (q : ℤ) ^ n)
        · gcongr
        · rw [pow_add, pow_one, mul_comm]
      · apply mul_nonneg
        · exact v₁.prop.left _
        · positivity
      · have : v₁.val ⟨n, hn⟩ < q := by simpa using v₁.prop.right ⟨n, hn⟩
        apply lt_of_lt_of_le (b := (q : ℤ) * (q : ℤ) ^ n)
        · gcongr
        · rw [pow_add, pow_one, mul_comm]
    · apply mul_nonneg
      · exact v₂.prop.left _
      · positivity
    · have : v₂.val ⟨n, hn⟩ < q := by simpa using v₂.prop.right ⟨n, hn⟩
      apply lt_of_lt_of_le (b := (q : ℤ) * (q : ℤ) ^ n)
      · gcongr
      · rw [pow_add, pow_one, mul_comm]

/- Integer after dropping first d' elements -/
def VecToInt' (k : Fin d) : Vec' d q → ℤ := fun v ↦ VecToInt hq (VecTruncate v k)

lemma VecToIntZero (v : Vec' 0 q) : VecToInt hq v = 0 := rfl

lemma VecToInt'Zero (hd : 0 < d) : @VecToInt' d q hq ⟨0, hd⟩ = VecToInt hq := by
  ext a
  simp [VecToInt', VecToInt]
  exact sum_congr (by ext a; simp [Fin.le_iff_val_le_val]) (fun _ _ ↦ rfl)

def v₀ : Vec' 3 5 := VecEquivFun.invFun ![2, 4, 1]
#eval! VecToInt (by decide) v₀
#eval! VecToInt' (by decide) 0 v₀
#eval! VecToInt' (by decide) 1 v₀
#eval! VecToInt' (by decide) 2 v₀
#eval! v₀.val 1 + 5 * VecToInt' (by decide) ⟨2, by decide⟩ v₀

/-
[2,4,1] [4,1] [1]
-/
lemma aux1 (v : Vec' d q) (k : Fin d) (hk : 0 < k.val) (h h' h'') :
    ∑ x : Fin k, v.val (Fin.cast h (Fin.addNat x (d - k))) * q ^ x.val =
      v.val ⟨d - k, h''⟩ +
        q * ∑ x : Fin (k - 1), v.val (Fin.cast h' (Fin.addNat x ((d - k) + 1))) * q ^ x.val := by
  obtain ⟨d', rfl⟩ := Nat.exists_eq_add_of_le' (by omega : 0 < d)
  cases' Fin.eq_zero_or_eq_succ k with hk' hk'
  · subst hk'; rw [Fin.val_zero] at hk; omega
  · obtain ⟨k, rfl⟩ := hk'
    simp only [Fin.val_succ, Nat.reduceSucc, Pi.natCast_def, Nat.add_succ_sub_one, Nat.add_zero] at *
    rw [Fin.sum_univ_succ, Fin.val_zero, pow_zero, mul_one]
    congr! 1
    · congr!
      simp_rw [Fin.coe_cast, Fin.coe_addNat, Fin.succ, Fin.val_zero, zero_add] at h ⊢
    · simp_rw [mul_comm (q : ℤ), sum_mul, mul_assoc, ← pow_succ]
      congr! 3 with i _
      ext
      simp
      omega

lemma aux1' (v : Vec' d q) (k : Fin d) (hd : 0 < d) (hk : 0 < k.val) (h h' h'') :
    ∑ x : Fin (d - k), v.val (Fin.cast h (Fin.addNat x k)) * q ^ x.val =
      v.val ⟨k, h''⟩ +
        q * ∑ x : Fin (d - k - 1), v.val (Fin.cast h' (Fin.addNat x (k + 1))) * q ^ x.val := by
  have h1 := Nat.sub_sub_self h''.le
  have : 0 < d - k.val := by linarith
  have := by
    refine aux1 v ⟨d - k.val, Nat.sub_lt hd hk⟩ (by simp [this]) (by omega) ?_ ?_
    · simp; omega
    · simp [hd]
  convert this <;> simpa using h1.symm

/- The naming scheme is horrible -/
lemma VecToInt_eq_first_add_truncate (v : Vec' d q) (k) (h : k.val < d) (h' : 0 < k.val) (h'') :
    VecToInt' hq k v = v.val ⟨k, h⟩ + q * VecToInt' hq ⟨k.val + 1, h''⟩ v := by
  simp [VecToInt', VecToInt, VecTruncate]
  convert aux1' v k ?_ h' ?_ ?_ ?_ <;> omega

def VecPairToInt : Vec' d q × Vec' d q ↪ ℤ × ℤ where
  toFun := fun ⟨v₁, v₂⟩ ↦ ⟨VecToInt hq v₁, VecToInt hq v₂⟩
  inj' := fun ⟨a, b, c, d⟩ hv ↦ by simp; intro h₁ h₂; simp only [h₁, h₂]

lemma VecPairEquivInterval_eq_iff {u v : Vec' d q} {a b : ℤ} :
    VecPairToInt hq ⟨u, v⟩ = ⟨a, b⟩ ↔ VecToInt hq u = a ∧ VecToInt hq v = b := by
  rw [VecPairToInt, Function.Embedding.coeFn_mk, Prod.mk.injEq]

/- This is necessary since subst doesn't work for expressions or lets -/
lemma aux2 {m n d k q : ℕ} (f : Fin d → ℤ) (h h') :
    ∑ x : Fin m, f (Fin.cast h (Fin.addNat x k)) * q ^ x.val
    = ∑ x : Fin n, f (Fin.cast h' (Fin.addNat x k)) * q ^ x.val := by
  have : m = n := by omega
  subst this
  rfl

lemma VecEqMod (v : Vec' d q) (k : Fin d) :
    v.val k ≡ VecToInt' hq k v [ZMOD q] := by
  simp only [VecToInt', Int.modEq_iff_dvd, VecTruncate, VecToInt, Pi.natCast_def,
    Function.Embedding.coeFn_mk]
  have : 0 < d - k := have := k.prop; by omega
  obtain ⟨t, ht⟩ := Nat.exists_eq_add_of_le' this
  rw [aux2 v.val (by omega) (by omega) (n := t + 1), Fin.sum_univ_succ, add_comm, add_sub_assoc]
  simp
  apply dvd_add
  · apply dvd_sum
    intro k _
    simp_rw [pow_succ']
    rw [mul_comm (q : ℤ) _, ← mul_assoc]
    apply dvd_mul_left
  · convert dvd_zero _
    have {h} : Fin.cast h (Fin.addNat (0 : Fin (t + 1)) k.val) = k := by ext; simp
    rw [sub_eq_zero, this]

lemma VecEqMod' (v : Vec' d.succ q) : v.val 0 ≡ VecToInt hq v [ZMOD q] := VecEqMod hq v _

/- --------------------------------------------------------------------------- -/

lemma sum_sq_eq_zero {α β : Type*} [LinearOrderedSemiring β] [ExistsAddOfLE β]
    {f : α → β} {s : Finset α} : ∑ x in s, f x ^ 2 = 0 ↔ ∀ x ∈ s, f x = 0 := by
  constructor <;> intro h
  · contrapose! h
    obtain ⟨x, ⟨hx₁, hx₂⟩⟩ := h
    have := lt_of_le_of_ne (sq_nonneg _) (Ne.symm (sq_eq_zero_iff.not.mpr hx₂))
    exact (sum_pos' (fun _ _ ↦ sq_nonneg _) ⟨x, ⟨hx₁, this⟩⟩).ne.symm
  · rw [sum_congr rfl (g := fun _ ↦ 0) (by simpa using h), sum_const, nsmul_zero]

/- The Mathlib norm requires us to work with real numbers :( -/
/- TODO: Switch to using inner products ⟪⟫ -/
def norm' (v : Vec d) : ℤ := ∑ i, (v i) ^ 2

lemma norm'_zero : norm' (0 : Vec d) = 0 := by simp [norm']

lemma norm'_nonneg (v : Vec d) : 0 ≤ norm' v := sum_nonneg (fun _ _ ↦ sq_nonneg _)

lemma norm'_eq_zero_iff (v : Vec d) : norm' v = 0 ↔ v = 0 :=
  ⟨fun h ↦ by rw [norm'] at h; ext i; exact sum_sq_eq_zero.mp h _ (mem_univ _),
   fun h ↦ by subst h; exact norm'_zero⟩

@[simp] abbrev IsInCons (r : ℕ) (x y : Vec' d q) : Prop :=
    norm' (x.val - y.val) = r ∧ (q ≤ 2 * (x.val + y.val) ∧ 2 * (x.val + y.val) + 1 ≤ 3 * q)

/- As a consequence, this is easier to prove -/
theorem parallelogram_law_with_norm' (x y : Vec d) :
    norm' (x + y) + norm' (x - y) = 2 * (norm' x + norm' y) := by
  simp_rw [norm', two_mul, ← sum_add_distrib, Pi.add_apply, Pi.sub_apply]
  exact sum_congr rfl fun _ _ ↦ by ring_nf

instance : DecidablePred (@IsInCons d q r).uncurry := by
  intro ⟨x, y⟩
  simp [IsInCons]
  apply And.decidable (dp := ?_) (dq := And.decidable (dp := ?_) (dq := ?_))
  all_goals
    try simp only [Pi.le_def, Pi.lt_def]
    infer_instance

def A (r : ℕ) : Finset (Vec' d q × Vec' d q) := univ.filter (IsInCons r).uncurry

@[simp] lemma mem_A_iff {x y : Vec' d q} : ⟨x, y⟩ ∈ @A d q r ↔ IsInCons r x y := by
  simp only [mem_filter, mem_univ, true_and, Function.uncurry, A]

#eval (univ : Finset (Vec' 5 0))

#check Nat.ofDigits
#eval (A (d := 2) (q := 3) 5)
#eval (univ : Finset (Vec' 2 5)).map (VecToInt (by decide))
#eval (A (d := 2) (q := 3) 5).map (VecPairToInt (by decide))
#eval AddCornerFree ((A (d := 2) (q := 3) 5).map (VecPairToInt (by decide)) : Set (ℤ × ℤ))

/- --------------------------------------------------------------------------- -/

example {v : Vec' d.succ q} : v.val 0 ≡ VecToInt hq v [ZMOD q] := VecEqMod hq v 0

/- --------------------------------------------------------------------------- -/

lemma eq_zero_of_modEq_zero_of_abs_lt {a : ℤ} {q : ℕ}
    (h_bound : |a| < q) (h_modeq : a ≡ 0 [ZMOD q]) : a = 0 := by
  have : 0 < q := by zify; exact lt_of_le_of_lt (abs_nonneg a) h_bound
  obtain ⟨a, rfl⟩ := modEq_zero_iff_dvd.mp h_modeq
  rw [abs_mul, Nat.abs_cast] at h_bound
  rw [abs_lt_one_iff.mp $ (mul_lt_iff_lt_one_right (Nat.cast_pos.mpr this)).mp h_bound, mul_zero]

/- Concluding theorem -/
theorem part1 : AddCornerFree ((@A d q r).map (VecPairToInt hq) : Set (ℤ × ℤ)) := by
  intro im_x im_y im_d hd hdx hdy
  obtain ⟨⟨x, y⟩, ⟨hd₁, hd₂⟩⟩ := mem_map.mp $ mem_coe.mp hd
  obtain ⟨⟨xd, y'⟩, ⟨hdx₁, hdx₂⟩⟩ := mem_map.mp $ mem_coe.mp hdx
  obtain ⟨⟨x', yd⟩, ⟨hdy₁, hdy₂⟩⟩ := mem_map.mp $ mem_coe.mp hdy
  rw [VecPairEquivInterval_eq_iff] at hd₂ hdx₂ hdy₂
  have hx_equal : x = x' := (VecToInt hq).injective (hd₂.left.trans hdy₂.left.symm)
  have hy_equal : y = y' := (VecToInt hq).injective (hd₂.right.trans hdx₂.right.symm)
  subst hy_equal hx_equal
  clear hd hdx hdy

  obtain ⟨hx, hy⟩ := hd₂
  obtain hdx := hdx₂.left
  obtain hdy := hdy₂.right
  clear hdx₂ hdy₂

  cases' d with d
  /- d = 0 -/
  · simp [VecToIntZero] at hx hy hdx hdy
    omega

  /- (0.1): Then, ... -/
  have h₁ : norm' (x.val - y.val) = r := (mem_A_iff.mp hd₁).left
  have h₂ : norm' (xd.val - y.val) = r := (mem_A_iff.mp hdx₁).left
  have h₃ : norm' (x.val - yd.val) = r := (mem_A_iff.mp hdy₁).left

  /- (0.2): We claim that ... -/
  have : xd.val - x.val = yd.val - y.val := by
    rw [sub_eq_sub_iff_add_eq_add]
    ext i
    induction' i using Fin.induction with i hi
    · simp only [Pi.add_apply, Pi.natCast_def]
      have h_bound : |(xd.val 0 + y.val 0) - (yd.val 0 + x.val 0)| < q := by
        have h₁ := (mem_A_iff.mp hdx₁).right.left 0
        have h₂ := (mem_A_iff.mp hdx₁).right.right 0
        have h₃ := (mem_A_iff.mp hdy₁).right.left 0
        have h₄ := (mem_A_iff.mp hdy₁).right.right 0
        simp at h₁ h₂ h₃ h₄
        rw [abs_lt]
        constructor <;> linarith
      have h_modeq : (xd.val 0 + y.val 0) - (yd.val 0 + x.val 0) ≡ 0 [ZMOD q] := by
        rw [ModEq,
          ((VecEqMod' hq xd).add_right _).sub_right, ((VecEqMod' hq y).add_left _).sub_right,
          ((VecEqMod' hq yd).add_right _).sub_left, ((VecEqMod' hq x).add_left _).sub_left,
          hx, hy, hdx, hdy]
        ring_nf
      simpa [sub_eq_zero] using eq_zero_of_modEq_zero_of_abs_lt h_bound h_modeq
    · sorry

  have hp := parallelogram_law_with_norm' (x.val - y.val) (xd.val - x.val)
  rw [sub_add_sub_cancel', h₂, this, sub_sub_sub_cancel_right, h₃, h₁, mul_add, two_mul] at hp
  simp [norm'_eq_zero_iff, sub_eq_zero] at hp
  have hp' : yd = y := by ext; rw [hp]
  subst hp'
  omega

example {a b c : ℝ} : (a - b) + (c - a) = c - b := by rw?

#check parallelogram_law

def v : Vec' 3 5 := VecEquivFun.invFun ![2, 4, 1]
#eval v
#eval VecToInt' (by decide) 0 v
#eval VecToInt' (by decide) 1 v
#eval VecToInt' (by decide) 2 v
def i : Fin 3 := 2
#eval i
#eval Fin.succ i
#eval Fin.castSucc i

/- --------------------------------------------------------------------------- -/

#check parallelogram_law

