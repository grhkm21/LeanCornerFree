import Mathlib.Tactic
import Mathlib.Data.List.ToFinsupp

import BenGreenCornerFree.CornerFree

namespace BenGreen

open Int Finset BigOperators

/- Make sure this fails because of autoImplicit=false -/
example : a + 1 = 2 := by sorry

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
    constructor <;> simp only [Pi.coe_nat, Pi.le_def, Pi.zero_apply]
    · exact fun _ ↦ v.prop.left _
    · exact fun _ ↦ v.prop.right _

def VecToInt : Vec' d q ↪ ℤ where
  toFun := fun v ↦ ∑ i, v.val i * q ^ i.val
  inj' := fun v₁ v₂ hv ↦ by sorry

/- Integer after dropping first d' elements -/
def VecToInt' (k : Fin d) : Vec' d q ↪ ℤ where
  toFun := fun v ↦ VecToInt (VecTruncate v k)
  inj' := fun v₁ v₂ hv ↦ by sorry

lemma VecToInt'Zero (hd : 0 < d) : @VecToInt' d q ⟨0, hd⟩ = VecToInt := by
  ext a
  simp [VecToInt', VecToInt]
  exact sum_congr (by ext a; simp [Fin.le_iff_val_le_val]) (fun _ _ ↦ rfl)

def VecPairToInt : Vec' d q × Vec' d q ↪ ℤ × ℤ where
  toFun := fun ⟨v₁, v₂⟩ ↦ ⟨VecToInt v₁, VecToInt v₂⟩
  inj' := fun ⟨a, b, c, d⟩ hv ↦ by simp; intro h₁ h₂; simp only [h₁, h₂]

lemma VecPairEquivInterval_eq_iff {u v : Vec' d q} {a b : ℤ} :
    VecPairToInt ⟨u, v⟩ = ⟨a, b⟩ ↔ VecToInt u = a ∧ VecToInt v = b := by
  rw [VecPairToInt, Function.Embedding.coeFn_mk, Prod.mk.injEq]

lemma VecToIntZero (v : Vec' 0 q) : VecToInt v = 0 := rfl

lemma aux {m n d k q : ℕ} (f : Fin d → ℤ) (h h') :
    ∑ x : Fin m, f (Fin.cast h (Fin.addNat x k)) * q ^ x.val
    = ∑ x : Fin n, f (Fin.cast h' (Fin.addNat x k)) * q ^ x.val := by
  have : m = n := by omega
  subst this
  rfl

def v₀ : Vec' 3 5 := VecEquivFun.invFun ![2, 4, 1]
#eval v₀.val ⟨0, by omega⟩
#eval v₀.val ⟨1, by omega⟩
#eval v₀.val ⟨2, by omega⟩
#eval VecToInt' 0 v₀
#eval VecToInt' 1 v₀
#eval VecToInt' 2 v₀

lemma VecEqMod (v : Vec' d q) (k : Fin d) :
    v.val k ≡ VecToInt' k v [ZMOD q] := by
  simp only [VecToInt', Int.modEq_iff_dvd, VecTruncate, VecToInt, Pi.coe_nat,
    Function.Embedding.coeFn_mk]
  have : 0 < d - k := have := k.prop; by omega
  obtain ⟨t, ht⟩ := Nat.exists_eq_add_of_le' this
  rw [aux v.val (by omega) (by omega) (n := t + 1), Fin.sum_univ_succ, add_comm, add_sub_assoc]
  simp
  apply dvd_add
  · apply dvd_sum
    intro k _
    simp_rw [pow_succ']
    rw [← mul_assoc]
    apply dvd_mul_left
  · convert dvd_zero _
    have {h} : Fin.cast h (Fin.addNat (0 : Fin (t + 1)) k.val) = k := by ext; simp
    rw [sub_eq_zero, this]

lemma VecEqMod' (v : Vec' d.succ q) : v.val 0 ≡ VecToInt v [ZMOD q] := VecEqMod v _

/- --------------------------------------------------------------------------- -/

/- The Mathlib norm requires us to work with real numbers :( -/
def norm' (v : Vec d) : ℤ := ∑ i, (v i) ^ 2

def IsInCons (r : ℕ) (x y : Vec' d q) : Prop :=
    norm' (x.val - y.val) = r ∧ (q ≤ 2 * (x.val + y.val) ∧ 2 * (x.val + y.val) + 1 ≤ 3 * q)

instance : DecidablePred (@IsInCons d q r).uncurry := by
  intro ⟨x, y⟩
  simp [IsInCons]
  apply And.decidable (dp := ?_) (dq := And.decidable (dp := ?_) (dq := ?_))
  all_goals
    try simp only [Pi.le_def, Pi.lt_def]
    infer_instance

def A (r : ℕ) : Finset (Vec' d q × Vec' d q) := univ.filter (IsInCons r).uncurry

lemma mem_A_iff {x y : Vec' d q} : ⟨x, y⟩ ∈ @A d q r ↔ IsInCons r x y := by
  simp only [mem_filter, mem_univ, true_and, Function.uncurry, A]

#check Nat.ofDigits
#eval (A (d := 2) (q := 5) 5)
#eval (univ : Finset (Vec' 2 5)).map VecToInt
#eval (A (d := 2) (q := 5) 5).map VecPairToInt
#eval AddCornerFree ((A (d := 2) (q := 5) 5).map VecPairToInt : Set (ℤ × ℤ))

/- --------------------------------------------------------------------------- -/

example {v : Vec' d.succ q} : v.val 0 ≡ VecToInt v [ZMOD q] := ModEq.trans (VecEqMod v 0) rfl

/- --------------------------------------------------------------------------- -/

lemma eq_zero_of_modEq_zero_of_abs_lt {a : ℤ} {q : ℕ}
    (h_bound : |a| < q) (h_modeq : a ≡ 0 [ZMOD q]) : a = 0 := by
  have : 0 < q := by zify; exact lt_of_le_of_lt (abs_nonneg a) h_bound
  obtain ⟨a, rfl⟩ := modEq_zero_iff_dvd.mp h_modeq
  rw [abs_mul, Nat.abs_cast] at h_bound
  rw [abs_lt_one_iff.mp $ (mul_lt_iff_lt_one_right (Nat.cast_pos.mpr this)).mp h_bound, mul_zero]

/- Concluding theorem -/
theorem part1 : AddCornerFree ((@A d q r).map VecPairToInt : Set (ℤ × ℤ)) := by
  intro im_x im_y im_d hd hdx hdy
  obtain ⟨⟨x, y⟩, ⟨hd₁, hd₂⟩⟩ := mem_map.mp $ mem_coe.mp hd
  obtain ⟨⟨xd, y'⟩, ⟨hdx₁, hdx₂⟩⟩ := mem_map.mp $ mem_coe.mp hdx
  obtain ⟨⟨x', yd⟩, ⟨hdy₁, hdy₂⟩⟩ := mem_map.mp $ mem_coe.mp hdy
  rw [VecPairEquivInterval_eq_iff] at hd₂ hdx₂ hdy₂
  have hx_equal : x = x' := VecToInt.injective (hd₂.left.trans hdy₂.left.symm)
  have hy_equal : y = y' := VecToInt.injective (hd₂.right.trans hdx₂.right.symm)
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
  have : xd.val + y.val = x.val + yd.val := by
    ext i
    induction' i using Fin.induction with i hi
    · simp only [Pi.add_apply, Pi.coe_nat]
      have h_bound : |(xd.val 0 + y.val 0) - (x.val 0 + yd.val 0)| < q := by
        have h₁ := (mem_A_iff.mp hdx₁).right.left 0
        have h₂ := (mem_A_iff.mp hdx₁).right.right 0
        have h₃ := (mem_A_iff.mp hdy₁).right.left 0
        have h₄ := (mem_A_iff.mp hdy₁).right.right 0
        simp at h₁ h₂ h₃ h₄
        rw [abs_lt]
        constructor <;> linarith
      have h_modeq : (xd.val 0 + y.val 0) - (x.val 0 + yd.val 0) ≡ 0 [ZMOD q] := by
        rw [ModEq,
          ((VecEqMod' xd).add_right _).sub_right, ((VecEqMod' y).add_left _).sub_right,
          ((VecEqMod' x).add_right _).sub_left, ((VecEqMod' yd).add_left _).sub_left,
          hx, hy, hdx, hdy, add_comm im_y, ← add_assoc]
        ring_nf
      simpa [sub_eq_zero] using eq_zero_of_modEq_zero_of_abs_lt h_bound h_modeq
    · done

@[elab_as_elim] def induction {n : ℕ} {motive : Fin (n + 1) → Sort _} (zero : motive 0)
    (succ : ∀ i : Fin n, motive i.castSucc → motive i.succ) :
    ∀ i : Fin (n + 1), motive i
  | ⟨0, hi⟩ => by rwa [Fin.mk_zero]
  | ⟨i+1, hi⟩ => succ ⟨i, Nat.lt_of_succ_lt_succ hi⟩ (induction zero succ ⟨i, Nat.lt_of_succ_lt hi⟩)

def v : Vec' 3 5 := VecEquivFun.invFun ![2, 4, 1]
#eval v
#eval VecToInt' 0 v
#eval VecToInt' 1 v
#eval VecToInt' 2 v
def i : Fin 3 := 2
#eval i
#eval Fin.succ i
#eval Fin.castSucc i

/- --------------------------------------------------------------------------- -/

#check parallelogram_law

