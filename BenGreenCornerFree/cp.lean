import Mathlib.Tactic

def V (n : ℕ) := Fin n → ℤ
#synth AddCommMonoid (V 5)
#check Pi.addCommMonoid
#synth AddCommMonoid ℤ
