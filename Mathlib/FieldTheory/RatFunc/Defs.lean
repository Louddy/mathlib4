/-
Copyright (c) 2021 Anne Baanen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anne Baanen
-/
module

public import Mathlib.Algebra.Polynomial.Basic
public import Mathlib.Algebra.Ring.NonZeroDivisors
public import Mathlib.RingTheory.Localization.FractionRing

/-!
# The field of rational functions

Files in this folder define the field `K⟮X⟯` of rational functions over a field `K`, show it
is the field of fractions of `K[X]` and provide the main results concerning it. This file contains
the basic definition.

For connections with Laurent Series, see `Mathlib/RingTheory/LaurentSeries.lean`.

## Main definitions
We provide a set of recursion and induction principles:
- `RatFunc.liftOn`: define a function by mapping a fraction of polynomials `p/q` to `f p q`,
  if `f` is well-defined in the sense that `p/q = p'/q' → f p q = f p' q'`.
- `RatFunc.liftOn'`: define a function by mapping a fraction of polynomials `p/q` to `f p q`,
  if `f` is well-defined in the sense that `f (a * p) (a * q) = f p' q'`.
- `RatFunc.induction_on`: if `P` holds on `p / q` for all polynomials `p q`, then `P` holds on all
  rational functions

## Implementation notes

To provide good API encapsulation and speed up unification problems,
`RatFunc` is defined as a structure, and all operations are `@[irreducible] def`s

We need a couple of maps to set up the `Field` and `IsFractionRing` structure,
namely `RatFunc.ofFractionRing`, `RatFunc.toFractionRing`, `RatFunc.mk` and
`RatFunc.toFractionRingRingEquiv`.
All these maps get `simp`ed to bundled morphisms like `algebraMap K[X] K⟮X⟯`
and `IsLocalization.algEquiv`.

There are separate lifts and maps of homomorphisms, to provide routes of lifting even when
the codomain is not a field or even an integral domain.

## References

* [Kleiman, *Misconceptions about $K_X$*][kleiman1979]
* https://freedommathdance.blogspot.com/2012/11/misconceptions-about-kx.html
* https://stacks.math.columbia.edu/tag/01X1

-/

public noncomputable section

open scoped nonZeroDivisors Polynomial

universe u v

variable (K : Type u)

/-- `RatFunc K` is `K(X)`, the field of rational functions over `K`.

The inclusion of polynomials into `RatFunc` is `algebraMap K[X] K⟮X⟯`,
the maps between `K⟮X⟯` and another field of fractions of `K[X]`,
especially `FractionRing K[X]`, are given by `IsLocalization.algEquiv`.
-/
def RatFunc [CommRing K] : Type u := FractionRing K[X]

@[inherit_doc] scoped[RatFunc] notation:9000 R "⟮X⟯" => RatFunc R

namespace RatFunc

section CommRing

variable {K}
variable [CommRing K]

section Rec

/-! ### Constructing `RatFunc`s and their induction principles -/


/-- Non-dependent recursion principle for `K⟮X⟯`:
To construct a term of `P : Sort*` out of `x : K⟮X⟯`,
it suffices to provide a constructor `f : Π (p q : K[X]), P`
and a proof that `f p q = f p' q'` for all `p q p' q'` such that `q' * p = q * p'` where
both `q` and `q'` are not zero divisors, stated as `q ∉ K[X]⁰`, `q' ∉ K[X]⁰`.

If considering `K` as an integral domain, this is the same as saying that
we construct a value of `P` for such elements of `K⟮X⟯` by setting
`liftOn (p / q) f _ = f p q`.

When `[IsDomain K]`, one can use `RatFunc.liftOn'`, which has the stronger requirement
of `∀ {p q a : K[X]} (hq : q ≠ 0) (ha : a ≠ 0), f (a * p) (a * q) = f p q)`.
-/
protected irreducible_def liftOn {P : Sort v} (x : K⟮X⟯) (f : K[X] → K[X] → P)
    (H : ∀ {p q p' q'} (_hq : q ∈ K[X]⁰) (_hq' : q' ∈ K[X]⁰), q' * p = q * p' → f p q = f p' q') :
    P :=
  Localization.liftOn (x) (fun p q => f p q) fun {_ _ q q'} h =>
    H q.2 q'.2 (let ⟨⟨_, _⟩, mul_eq⟩ := Localization.r_iff_exists.mp h
      mul_cancel_left_coe_nonZeroDivisors.mp mul_eq)

theorem liftOn_condition_of_liftOn'_condition {P : Sort v} {f : K[X] → K[X] → P}
    (H : ∀ {p q a} (_ : q ≠ 0) (_ha : a ≠ 0), f (a * p) (a * q) = f p q) ⦃p q p' q' : K[X]⦄
    (hq : q ≠ 0) (hq' : q' ≠ 0) (h : q' * p = q * p') : f p q = f p' q' :=
  calc
    f p q = f (q' * p) (q' * q) := (H hq hq').symm
    _ = f (q * p') (q * q') := by rw [h, mul_comm q']
    _ = f p' q' := H hq' hq

section IsDomain


/-- `RatFunc.mk (p q : K[X])` is `p / q` as a rational function.

If `q = 0`, then `mk` returns 0.

This is an auxiliary definition used to define an `Algebra` structure on `RatFunc`;
the `simp` normal form of `mk p q` is `algebraMap _ _ p / algebraMap _ _ q`.
-/
def mk (p : K[X]) (q : K[X]⁰) : K⟮X⟯ :=
  Localization.mk p q

theorem liftOn_mk {P : Sort v} (p : K[X]) (q : K[X]⁰) (f : K[X] → K[X] → P)
    (H : ∀ {p q p' q'} (_hq : q ∈ K[X]⁰) (_hq' : q' ∈ K[X]⁰), q' * p = q * p' → f p q = f p' q') :
    (RatFunc.mk p q).liftOn f @H = f p q := by
  simp only [RatFunc.liftOn, RatFunc.mk, Localization.liftOn_mk]

/-- Non-dependent recursion principle for `K⟮X⟯`: if `f p q : P` for all `p q`,
such that `f (a * p) (a * q) = f p q`, then we can find a value of `P`
for all elements of `K⟮X⟯` by setting `lift_on' (p / q) f _ = f p q`.

The value of `f p 0` for any `p` is never used and in principle this may be anything,
although many usages of `lift_on'` assume `f p 0 = f 0 1`.
-/
protected irreducible_def liftOn' [IsDomain K] {P : Sort v} (x : K⟮X⟯) (f : K[X] → K[X] → P)
  (H : ∀ {p q a} (_hq : q ≠ 0) (_ha : a ≠ 0), f (a * p) (a * q) = f p q) : P :=
  x.liftOn f fun {_p _q _p' _q'} hq hq' =>
    liftOn_condition_of_liftOn'_condition (@H) (nonZeroDivisors.ne_zero hq)
      (nonZeroDivisors.ne_zero hq')

theorem liftOn'_mk [IsDomain K] {P : Sort v} (p : K[X]) (q : K[X]⁰) (f : K[X] → K[X] → P)
    (H : ∀ {p q a} (_hq : q ≠ 0) (_ha : a ≠ 0), f (a * p) (a * q) = f p q) :
    (RatFunc.mk p q).liftOn' f @H = f p q := by
  rw [RatFunc.liftOn', RatFunc.liftOn_mk _ _ _]

/-- Induction principle for `K⟮X⟯`: if `f p q : P (RatFunc.mk p q)` for all `p q`,
then `P` holds on all elements of `K⟮X⟯`.

See also `induction_on`, which is a recursion principle defined in terms of `algebraMap`.
-/
@[elab_as_elim]
protected theorem induction_on' {P : K⟮X⟯ → Prop} (x : K⟮X⟯)
    (_pq : ∀ (p : K[X]) (q : K[X]⁰), P (RatFunc.mk p q)) : P x :=
  Localization.induction_on x (fun (p, q) ↦ _pq p q)

end IsDomain

end Rec

end CommRing

end RatFunc
