/-
Copyright (c) 2026 Brandon Yates. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib

/-!
# Challenge: zeros of the odd channel of Riemann's kernel

This file is the human-auditable statement. It imports only Mathlib.

**This file makes no claim about the Riemann hypothesis, in either direction.**

Riemann's kernel is
`Φ(u) = ∑_{n≥1} (4π²n⁴ e^{9u/2} − 6πn² e^{5u/2}) e^{−πn²e^{2u}}`,
the positive even function for which `ξ(½+w) = 2∫₀^∞ Φ(u) cosh(wu) du`
(Titchmarsh, *The Theory of the Riemann Zeta-Function*, §2.1).

The object studied here is the **odd channel** of that same kernel, obtained by
replacing `cosh` with `sinh`:
`F(w) = 2∫₀^∞ Φ(u) sinh(wu) du`.

Four statements are advertised: `F` is entire, it has infinitely many zeros,
every nonzero zero has both real and imaginary parts nonzero, and the zeros are
carried to zeros by `w ↦ -w` and by complex conjugation. The last advertised
statement is a consequence: the zeros of the sine channel `t ↦ F(it)` are not
all real.

Scope, stated plainly: the classical identification of `F` with the odd part of
the completed zeta function is **not** asserted anywhere in this file. Every
statement below quantifies over the integral `F` as defined here.
-/

namespace TemperedXi

open Real MeasureTheory Set

/-- The `n`-th summand of Riemann's kernel series,
`(4π²n⁴ e^{9u/2} − 6πn² e^{5u/2}) e^{−πn²e^{2u}}`. -/
noncomputable def phiTerm (n : ℕ) (u : ℝ) : ℝ :=
  (4 * π ^ 2 * (n : ℝ) ^ 4 * Real.exp (9 * u / 2) -
      6 * π * (n : ℝ) ^ 2 * Real.exp (5 * u / 2)) *
    Real.exp (-(π * (n : ℝ) ^ 2 * Real.exp (2 * u)))

/-- **Riemann's kernel** `Φ(u) = ∑_{n≥1} (4π²n⁴ e^{9u/2} − 6πn² e^{5u/2}) e^{−πn²e^{2u}}`.

The sum is over `n ≥ 1`; it is written as a sum over `n : ℕ` of `phiTerm (n+1)`.
This is the kernel of Riemann's integral representation of `ξ`: it is positive,
even, and superexponentially decaying. -/
noncomputable def Phi (u : ℝ) : ℝ := ∑' n : ℕ, phiTerm (n + 1) u

/-- **The odd channel** `F(w) = 2∫₀^∞ Φ(u) sinh(wu) du`.

The even channel of the same kernel is `ξ(½+w)`; this is its `sinh` analogue.
`F` is an odd entire function of `w`. -/
noncomputable def F (w : ℂ) : ℂ :=
  2 * ∫ u in Ioi (0:ℝ), (Phi u : ℂ) * Complex.sinh (w * u)

/-- `F` is entire. -/
theorem F_differentiable : Differentiable ℂ F := by
  sorry

/-- `F` has infinitely many zeros. -/
theorem zeros_infinite : {z : ℂ | F z = 0}.Infinite := by
  sorry

/-- Every nonzero zero of `F` has both real part and imaginary part nonzero.
Equivalently: apart from the origin, `F` has no zero on either coordinate axis. -/
theorem zeros_off_axes (w : ℂ) (hw : F w = 0) (hw0 : w ≠ 0) :
    w.re ≠ 0 ∧ w.im ≠ 0 := by
  sorry

/-- The zeros of `F` occur in quartets `w, -w, conj w, -conj w`. -/
theorem zeros_quartet (w : ℂ) (hw : F w = 0) :
    F (-w) = 0 ∧ F ((starRingEnd ℂ) w) = 0 ∧ F (-(starRingEnd ℂ) w) = 0 := by
  sorry

/-- **The critical-line conjecture for the tempered xi function is false.**

The source conjecture (X.-J. Yang, *On a tempered xi function associated with the
Riemann xi function*, Fractals 32 (2024) 2340116, Conjecture 1) asserts that
every zero of the tempered xi function lies on the critical line `Re s = 1/2`.
In the coordinates used here the tempered xi function at `s` is `F (s - 1/2)`,
so the conjecture says every zero `w` of `F` has `w.re = 0`.

It is false: `F` has infinitely many zeros and every nonzero one has `w.re ≠ 0`,
so apart from the zero at the origin **no** zero of `F` lies on the line. -/
theorem critical_line_conjecture_false :
    ¬ ∀ s : ℂ, F (s - 1/2) = 0 → s.re = 1/2 := by
  sorry

/-- **The sine channel does not have only real zeros.**

Writing `Λ(t) = F(it)` for the sine channel of Riemann's kernel, it is not the
case that every zero of `Λ` is real. This is the negation of a conjecture
recorded in the literature for this transform; it follows from `zeros_infinite`
together with `zeros_off_axes`, since a nonzero `t` with `Λ(t) = 0` real would
make `it` a nonzero zero of `F` with vanishing real part. -/
theorem sine_channel_zeros_not_all_real :
    ¬ ∀ t : ℂ, F (t * Complex.I) = 0 → t.im = 0 := by
  sorry

end TemperedXi
