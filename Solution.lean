/-
Copyright (c) 2026 Brandon Yates. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import XiLab.Zeros

/-!
# Solution

The proof development lives in the `XiLab` library. This file restates the
Challenge definitions verbatim and bridges to the library's theorems.

The two `example`s below are the bridge: `TemperedXi.Phi` and `TemperedXi.F`
are *definitionally* equal to `XiLab.Phi` and `XiLab.F`, so each theorem is
discharged by the corresponding library result applied directly.
-/
namespace TemperedXi
open Real MeasureTheory Set

noncomputable def phiTerm (n : ℕ) (u : ℝ) : ℝ :=
  (4 * π ^ 2 * (n : ℝ) ^ 4 * Real.exp (9 * u / 2) -
      6 * π * (n : ℝ) ^ 2 * Real.exp (5 * u / 2)) *
    Real.exp (-(π * (n : ℝ) ^ 2 * Real.exp (2 * u)))

noncomputable def Phi (u : ℝ) : ℝ := ∑' n : ℕ, phiTerm (n + 1) u

noncomputable def F (w : ℂ) : ℂ :=
  2 * ∫ u in Ioi (0:ℝ), (Phi u : ℂ) * Complex.sinh (w * u)

example : Phi = XiLab.Phi := rfl
example : F = XiLab.F := rfl

theorem F_differentiable : Differentiable ℂ F := XiLab.differentiable_F

theorem zeros_infinite : {z : ℂ | F z = 0}.Infinite := XiLab.F_zeros_infinite

theorem zeros_off_axes (w : ℂ) (hw : F w = 0) (hw0 : w ≠ 0) :
    w.re ≠ 0 ∧ w.im ≠ 0 := XiLab.re_ne_zero_and_im_ne_zero_of_zero hw hw0

theorem zeros_quartet (w : ℂ) (hw : F w = 0) :
    F (-w) = 0 ∧ F ((starRingEnd ℂ) w) = 0 ∧ F (-(starRingEnd ℂ) w) = 0 :=
  XiLab.zero_quartet hw

theorem critical_line_conjecture_false :
    ¬ ∀ s : ℂ, F (s - 1/2) = 0 → s.re = 1/2 := by
  intro h
  obtain ⟨w, hw, hw0⟩ := (XiLab.F_zeros_infinite.sdiff (Set.finite_singleton 0)).nonempty
  simp only [Set.mem_setOf_eq, Set.mem_singleton_iff] at hw hw0
  have hre : w.re ≠ 0 := (XiLab.re_ne_zero_and_im_ne_zero_of_zero hw hw0).1
  have hs : (1/2 + w : ℂ) - 1/2 = w := by ring
  have hkey := h (1/2 + w) (by rw [hs]; exact hw)
  rw [Complex.add_re] at hkey
  norm_num at hkey
  exact hre hkey

theorem sine_channel_zeros_not_all_real :
    ¬ ∀ t : ℂ, F (t * Complex.I) = 0 → t.im = 0 := by
  intro h
  obtain ⟨w, hw, hw0⟩ := (zeros_infinite.sdiff (Set.finite_singleton 0)).nonempty
  simp only [Set.mem_setOf_eq, Set.mem_singleton_iff] at hw hw0
  have hre : w.re ≠ 0 := (zeros_off_axes w hw hw0).1
  have hmul : (-w * Complex.I) * Complex.I = w := by ring_nf; simp [Complex.I_sq]
  have hkey := h (-w * Complex.I) (by rw [hmul]; exact hw)
  simp [Complex.mul_im, Complex.neg_im] at hkey
  exact hre hkey

end TemperedXi
