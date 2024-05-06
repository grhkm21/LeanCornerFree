import Mathlib.Algebra.RingQuot
import Mathlib.RingTheory.Ideal.IsPrimary
import Mathlib.RingTheory.Ideal.LocalRing

import Mathlib.Data.Sign
import Mathlib.Algebra.Order.Ring.Cone
import Mathlib.Tactic.Linarith.Frontend

open Polynomial Ideal Quotient LocalRing

scoped[PolynomialPolynomial] notation "Y" => Polynomial.X
scoped[PolynomialPolynomial] notation R "[X][Y]" => Polynomial (Polynomial R)

open PolynomialPolynomial

theorem RingEquiv.isDomain_iff {R S : Type*} [CommRing R] [CommRing S] (f : R ≃+* S) :
    IsDomain R ↔ IsDomain S :=
  ⟨fun _ ↦ f.symm.injective.isDomain f.symm.toRingHom,
    fun _ ↦ f.injective.isDomain f.toRingHom⟩

instance {K : Type*} [Field K] : IsPrime (span {Y} : Ideal (K[X][Y])) := by
  have := Polynomial.quotientSpanXSubCAlgEquiv (0 : K[X])
  rw [C_0, sub_zero] at this
  rw [← isDomain_iff_prime, ← this.toRingEquiv.symm.isDomain_iff]
  infer_instance
