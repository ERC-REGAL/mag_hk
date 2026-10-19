import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! Direct evaluation of the monopole angular Coulomb integral. -/

namespace MagHK.Monopole

open Set MeasureTheory

noncomputable def coulombPrimitive (a b x : ℝ) : ℝ :=
  -(2 / (3 * b ^ 2)) * Real.sqrt (a - b * x) *
    (a - b * x + 3 * (b - a))

theorem hasDerivAt_coulombPrimitive (a b x : ℝ) (hb : b ≠ 0)
    (hq : 0 < a - b * x) :
    HasDerivAt (coulombPrimitive a b)
      ((1 - x) / Real.sqrt (a - b * x)) x := by
  have hd : HasDerivAt (fun y : ℝ => a - b * y) (-b) x := by
    convert! (hasDerivAt_const_mul (x := x) b).const_sub a using 1
  have hroot := hd.sqrt hq.ne'
  have hderiv := (hroot.mul (hd.add_const (3 * (b - a)))).const_mul
    (-(2 / (3 * b ^ 2)))
  have hsq := Real.sq_sqrt hq.le
  have hr : Real.sqrt (a - b * x) ≠ 0 := (Real.sqrt_pos.2 hq).ne'
  have heq : -(2 / (3 * b ^ 2)) *
      (-b / (2 * Real.sqrt (a - b * x)) * (a - b * x + 3 * (b - a)) +
        Real.sqrt (a - b * x) * -b) = (1 - x) / Real.sqrt (a - b * x) := by
    field_simp
    nlinarith [congrArg (fun z : ℝ => b * z) hsq]
  rw [heq] at hderiv
  convert! hderiv using 1
  ext y
  simp only [coulombPrimitive, Pi.mul_apply, mul_assoc]

theorem angular_radicand_pos (s t x : ℝ) (hs : 0 < s) (ht : 0 < t)
    (hne : s ≠ t) (hx : x ≤ 1) : 0 < s ^ 2 + t ^ 2 - 2 * s * t * x := by
  have hsq : 0 < (s - t) ^ 2 := sq_pos_of_ne_zero (sub_ne_zero.mpr hne)
  have hprod : 0 ≤ s * t * (1 - x) := mul_nonneg (mul_pos hs ht).le (sub_nonneg.2 hx)
  nlinarith

theorem angular_integrand_integrable_of_ne (s t : ℝ) (hs : 0 < s) (ht : 0 < t)
    (hne : s ≠ t) :
    IntervalIntegrable (fun x : ℝ =>
      (1 - x) / Real.sqrt (s ^ 2 + t ^ 2 - 2 * s * t * x)) volume (-1) 1 := by
  apply ContinuousOn.intervalIntegrable
  apply (continuous_const.sub continuous_id).continuousOn.div
    (Real.continuous_sqrt.comp (continuous_const.sub
      (continuous_const.mul continuous_id))).continuousOn
  intro x hx
  have hx' : x ≤ 1 := by
    simpa only [max_eq_right (by norm_num : (-1 : ℝ) ≤ 1)] using hx.2
  exact (Real.sqrt_pos.2 (angular_radicand_pos s t x hs ht hne hx')).ne'

theorem angular_integral_primitive_of_ne (s t : ℝ) (hs : 0 < s) (ht : 0 < t)
    (hne : s ≠ t) :
    (∫ x : ℝ in (-1)..1, (1 - x) / Real.sqrt (s ^ 2 + t ^ 2 - 2 * s * t * x)) =
      coulombPrimitive (s ^ 2 + t ^ 2) (2 * s * t) 1 -
        coulombPrimitive (s ^ 2 + t ^ 2) (2 * s * t) (-1) := by
  apply intervalIntegral.integral_eq_sub_of_hasDerivAt
  · intro x hx
    have hx' : x ≤ 1 := by
      simpa only [max_eq_right (by norm_num : (-1 : ℝ) ≤ 1)] using hx.2
    exact hasDerivAt_coulombPrimitive _ _ _ (by positivity)
      (angular_radicand_pos s t x hs ht hne hx')
  · exact angular_integrand_integrable_of_ne s t hs ht hne

theorem angular_integral_of_lt (s t : ℝ) (hs : 0 < s) (ht : 0 < t)
    (hst : t < s) :
    (1 / 2 : ℝ) * (∫ x : ℝ in (-1)..1,
      (1 - x) / Real.sqrt (s ^ 2 + t ^ 2 - 2 * s * t * x)) =
      1 / s - t / (3 * s ^ 2) := by
  rw [angular_integral_primitive_of_ne s t hs ht (ne_of_gt hst)]
  have hminus : s ^ 2 + t ^ 2 - 2 * s * t * 1 = (s - t) ^ 2 := by ring
  have hplus : s ^ 2 + t ^ 2 - 2 * s * t * (-1) = (s + t) ^ 2 := by ring
  unfold coulombPrimitive
  rw [hminus, hplus, Real.sqrt_sq (sub_nonneg.2 hst.le),
    Real.sqrt_sq (by linarith : 0 ≤ s + t)]
  field_simp
  ring

theorem angular_integral_of_ne (s t : ℝ) (hs : 0 < s) (ht : 0 < t)
    (hne : s ≠ t) :
    (1 / 2 : ℝ) * (∫ x : ℝ in (-1)..1,
      (1 - x) / Real.sqrt (s ^ 2 + t ^ 2 - 2 * s * t * x)) =
      1 / max s t - min s t / (3 * (max s t) ^ 2) := by
  rcases lt_or_gt_of_ne hne with hst | hts
  · rw [max_eq_right hst.le, min_eq_left hst.le]
    have h := angular_integral_of_lt t s ht hs hst
    convert h using 1
    congr 2
    ext x
    congr 2 <;> ring
  · rw [max_eq_left hts.le, min_eq_right hts.le]
    exact angular_integral_of_lt s t hs ht hts

theorem diagonal_angular_integrand (s x : ℝ) (hs : 0 < s) (hx : x ≤ 1) :
    (1 - x) / Real.sqrt (s ^ 2 + s ^ 2 - 2 * s * s * x) =
      Real.sqrt (s ^ 2 + s ^ 2 - 2 * s * s * x) / (2 * s ^ 2) := by
  by_cases hxeq : x = 1
  · subst x
    have he : s ^ 2 + s ^ 2 - 2 * s * s * 1 = 0 := by ring
    rw [he, Real.sqrt_zero]
    simp
  · have hxlt : x < 1 := lt_of_le_of_ne hx hxeq
    have hprod : 0 < s ^ 2 * (1 - x) := mul_pos (sq_pos_of_pos hs) (sub_pos.2 hxlt)
    have hq : 0 < s ^ 2 + s ^ 2 - 2 * s * s * x := by nlinarith
    have hsq := Real.sq_sqrt hq.le
    apply (div_eq_div_iff (Real.sqrt_pos.2 hq).ne' (by positivity)).2
    nlinarith

theorem diagonal_angular_integrand_integrable (s : ℝ) (hs : 0 < s) :
    IntervalIntegrable (fun x : ℝ =>
      (1 - x) / Real.sqrt (s ^ 2 + s ^ 2 - 2 * s * s * x)) volume (-1) 1 := by
  apply ContinuousOn.intervalIntegrable
  have hc : Continuous (fun x : ℝ =>
      Real.sqrt (s ^ 2 + s ^ 2 - 2 * s * s * x) / (2 * s ^ 2)) :=
    (Real.continuous_sqrt.comp (continuous_const.sub
      (continuous_const.mul continuous_id))).div_const _
  apply hc.continuousOn.congr
  intro x hx
  apply diagonal_angular_integrand s x hs
  simpa only [max_eq_right (by norm_num : (-1 : ℝ) ≤ 1)] using hx.2

theorem diagonal_angular_integral (s : ℝ) (hs : 0 < s) :
    (1 / 2 : ℝ) * (∫ x : ℝ in (-1)..1,
      (1 - x) / Real.sqrt (s ^ 2 + s ^ 2 - 2 * s * s * x)) =
      1 / s - s / (3 * s ^ 2) := by
  have hcont : ContinuousOn (coulombPrimitive (s ^ 2 + s ^ 2) (2 * s * s))
      (Icc (-1 : ℝ) 1) := by
    unfold coulombPrimitive
    fun_prop
  have hderiv : ∀ x ∈ Ioo (-1 : ℝ) 1,
      HasDerivAt (coulombPrimitive (s ^ 2 + s ^ 2) (2 * s * s))
        ((1 - x) / Real.sqrt (s ^ 2 + s ^ 2 - 2 * s * s * x)) x := by
    intro x hx
    apply hasDerivAt_coulombPrimitive _ _ _ (by positivity)
    have hprod : 0 < s ^ 2 * (1 - x) := mul_pos (sq_pos_of_pos hs) (sub_pos.2 hx.2)
    nlinarith
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le
    (by norm_num : (-1 : ℝ) ≤ 1) hcont hderiv (diagonal_angular_integrand_integrable s hs)]
  have hminus : s ^ 2 + s ^ 2 - 2 * s * s * 1 = 0 := by ring
  have hplus : s ^ 2 + s ^ 2 - 2 * s * s * (-1) = (2 * s) ^ 2 := by ring
  unfold coulombPrimitive
  rw [hminus, hplus, Real.sqrt_zero, Real.sqrt_sq (by positivity : 0 ≤ 2 * s)]
  field_simp
  ring

/-- Equation (angular-integral), including coincident positive radii. -/
theorem angular_integral (s t : ℝ) (hs : 0 < s) (ht : 0 < t) :
    (1 / 2 : ℝ) * (∫ x : ℝ in (-1)..1,
      (1 - x) / Real.sqrt (s ^ 2 + t ^ 2 - 2 * s * t * x)) =
      1 / max s t - min s t / (3 * (max s t) ^ 2) := by
  by_cases hne : s ≠ t
  · exact angular_integral_of_ne s t hs ht hne
  · have heq : s = t := not_ne_iff.mp hne
    subst t
    simpa only [max_self, min_self] using diagonal_angular_integral s hs

end MagHK.Monopole
