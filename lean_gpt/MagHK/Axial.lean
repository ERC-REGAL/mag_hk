import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Measure.Lebesgue.Integral
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.NormNum

/-! The actual bounded axial orbital and its differential equation. -/
noncomputable section
namespace MagHK.Axial
open Filter MeasureTheory
open scoped Topology ContDiff
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false

def sech (x : ℝ) : ℝ := 1 / Real.cosh x

theorem sech_pos (x : ℝ) : 0 < sech x := by
  unfold sech
  exact div_pos (by norm_num) (Real.cosh_pos x)

theorem hyperbolic_identity (x : ℝ) : sech x ^ 2 + Real.tanh x ^ 2 = 1 := by
  have hc : Real.cosh x ≠ 0 := ne_of_gt (Real.cosh_pos x)
  have hid := Real.cosh_sq_sub_sinh_sq x
  rw [Real.tanh_eq_sinh_div_cosh]
  unfold sech
  field_simp
  nlinarith

theorem sech_hasDerivAt (x : ℝ) : HasDerivAt sech (-Real.tanh x * sech x) x := by
  have hc : Real.cosh x ≠ 0 := ne_of_gt (Real.cosh_pos x)
  have h := (hasDerivAt_const x (1 : ℝ)).div (Real.hasDerivAt_cosh x) hc
  apply h.congr_deriv
  simp only [sech, Real.tanh_eq_sinh_div_cosh, zero_mul, one_mul, zero_sub]
  field_simp

theorem tanh_hasDerivAt (x : ℝ) : HasDerivAt Real.tanh (sech x ^ 2) x := by
  have hc : Real.cosh x ≠ 0 := ne_of_gt (Real.cosh_pos x)
  have hid := Real.cosh_sq_sub_sinh_sq x
  have h := (Real.hasDerivAt_sinh x).div (Real.hasDerivAt_cosh x) hc
  have heq : (fun x : ℝ => Real.sinh x / Real.cosh x) = Real.tanh :=
    funext (fun x => (Real.tanh_eq_sinh_div_cosh x).symm)
  rw [← heq]
  apply h.congr_deriv
  unfold sech
  field_simp
  nlinarith

def chi (c z : ℝ) : ℝ := Real.sqrt (c / 2) * sech (c * z)
def potential (c z : ℝ) : ℝ := c ^ 2 - 2 * c ^ 2 * sech (c * z) ^ 2
def superpotential (c z : ℝ) : ℝ := c * Real.tanh (c * z)

theorem chi_pos (c z : ℝ) (hc : 0 < c) : 0 < chi c z := by
  unfold chi
  exact mul_pos (Real.sqrt_pos.2 (by positivity)) (sech_pos _)

theorem chi_hasDerivAt (c z : ℝ) :
    HasDerivAt (chi c) (-superpotential c z * chi c z) z := by
  have hinner : HasDerivAt (fun u : ℝ => c * u) c z := by
    simpa using (hasDerivAt_id z).const_mul c
  have h := ((sech_hasDerivAt (c * z)).comp z hinner).const_mul (Real.sqrt (c / 2))
  apply h.congr_deriv
  unfold chi superpotential
  ring

theorem superpotential_hasDerivAt (c z : ℝ) :
    HasDerivAt (superpotential c) (c ^ 2 * sech (c * z) ^ 2) z := by
  have hinner : HasDerivAt (fun u : ℝ => c * u) c z := by
    simpa using (hasDerivAt_id z).const_mul c
  have h := ((tanh_hasDerivAt (c * z)).comp z hinner).const_mul c
  apply h.congr_deriv
  ring

theorem factorization (c z : ℝ) :
    superpotential c z ^ 2 - deriv (superpotential c) z = potential c z ∧
    superpotential c z ^ 2 + deriv (superpotential c) z = c ^ 2 := by
  rw [(superpotential_hasDerivAt c z).deriv]
  have h := congrArg (fun x : ℝ => c ^ 2 * x) (hyperbolic_identity (c * z))
  unfold superpotential potential
  constructor <;> nlinarith only [h]

theorem chiPrime_hasDerivAt (c z : ℝ) :
    HasDerivAt (fun u => -superpotential c u * chi c u) (potential c z * chi c z) z := by
  have h := (superpotential_hasDerivAt c z).neg.mul (chi_hasDerivAt c z)
  apply h.congr_deriv
  have hfac := (factorization c z).1
  rw [(superpotential_hasDerivAt c z).deriv] at hfac
  simp only [Pi.neg_apply]
  rw [← hfac]
  ring

theorem zero_eigen_equation (c z : ℝ) :
    -deriv (deriv (chi c)) z + potential c z * chi c z = 0 := by
  have heq : deriv (chi c) = fun u => -superpotential c u * chi c u :=
    funext (fun u => (chi_hasDerivAt c u).deriv)
  rw [heq, (chiPrime_hasDerivAt c z).deriv]
  ring

theorem chi_kernel (c z : ℝ) : deriv (chi c) z + superpotential c z * chi c z = 0 := by
  rw [(chi_hasDerivAt c z).deriv]
  ring

def primitive (c z : ℝ) : ℝ := Real.tanh (c * z) / 2

theorem primitive_hasDerivAt (c z : ℝ) (hc : 0 ≤ c) :
    HasDerivAt (primitive c) (chi c z ^ 2) z := by
  have hinner : HasDerivAt (fun u : ℝ => c * u) c z := by
    simpa using (hasDerivAt_id z).const_mul c
  have h := ((tanh_hasDerivAt (c * z)).comp z hinner).div_const 2
  apply h.congr_deriv
  unfold chi
  rw [mul_pow, Real.sq_sqrt (by positivity : 0 ≤ c / 2)]
  ring

theorem tanh_exponential_formula (x : ℝ) :
    Real.tanh x = (1 - Real.exp (-2 * x)) / (1 + Real.exp (-2 * x)) := by
  have hsum : 0 < Real.exp x + Real.exp (-x) := by positivity
  have hprod : Real.exp x * Real.exp (-x) = 1 := by rw [← Real.exp_add]; simp
  have hprod2 : Real.exp x * Real.exp (-x) ^ 2 = Real.exp (-x) := by
    calc
      Real.exp x * Real.exp (-x) ^ 2 = (Real.exp x * Real.exp (-x)) * Real.exp (-x) := by ring
      _ = Real.exp (-x) := by rw [hprod, one_mul]
  have heq : Real.exp (-2 * x) = Real.exp (-x) ^ 2 := by
    rw [show -2 * x = -x + -x by ring, Real.exp_add]
    ring
  rw [Real.tanh_eq, heq]
  field_simp
  nlinarith only [hprod2]

theorem tanh_tendsto_atTop : Tendsto Real.tanh atTop (𝓝 (1 : ℝ)) := by
  have harg : Tendsto (fun x : ℝ => -2 * x) atTop atBot :=
    tendsto_id.const_mul_atTop_of_neg (by norm_num)
  have he : Tendsto (fun x : ℝ => Real.exp (-2 * x)) atTop (𝓝 0) :=
    Real.tendsto_exp_atBot.comp harg
  have h : Tendsto (fun x : ℝ => (1 - Real.exp (-2 * x)) / (1 + Real.exp (-2 * x)))
      atTop (𝓝 ((1 - 0) / (1 + 0))) :=
    (tendsto_const_nhds.sub he).div (tendsto_const_nhds.add he) (by norm_num : (1 : ℝ) + 0 ≠ 0)
  simpa only [sub_zero, add_zero, div_one, ← tanh_exponential_formula] using h

theorem primitive_tendsto (c : ℝ) (hc : 0 < c) : Tendsto (primitive c) atTop (𝓝 (1 / 2)) := by
  have hinner : Tendsto (fun z : ℝ => c * z) atTop atTop := tendsto_id.const_mul_atTop hc
  exact (tanh_tendsto_atTop.comp hinner).div_const 2

theorem chi_halfline_normalization (c : ℝ) (hc : 0 < c) :
    (∫ z in Set.Ioi (0 : ℝ), chi c z ^ 2) = 1 / 2 := by
  have h := integral_Ioi_of_hasDerivAt_of_nonneg'
    (fun z (_ : z ∈ Set.Ici (0 : ℝ)) => primitive_hasDerivAt c z (le_of_lt hc))
    (fun z (_ : z ∈ Set.Ioi (0 : ℝ)) => sq_nonneg (chi c z)) (primitive_tendsto c hc)
  simpa [primitive] using h

theorem chi_even (c z : ℝ) : chi c (-z) = chi c z := by
  simp [chi, sech, mul_neg, Real.cosh_neg]

theorem chi_normalization (c : ℝ) (hc : 0 < c) : (∫ z : ℝ, chi c z ^ 2) = 1 := by
  have hAbs : (fun z : ℝ => chi c |z| ^ 2) = fun z => chi c z ^ 2 := by
    funext z
    by_cases hz : 0 ≤ z
    · rw [abs_of_nonneg hz]
    · rw [abs_of_neg (lt_of_not_ge hz), chi_even]
  have h := integral_comp_abs (f := fun z => chi c z ^ 2)
  rw [hAbs, chi_halfline_normalization c hc] at h
  norm_num at h
  exact h


/-- Normalization entails actual Lebesgue integrability, not only an improper limit. -/
theorem chi_squared_integrable (c : ℝ) (hc : 0 < c) : Integrable (fun z : ℝ => chi c z ^ 2) := by
  by_contra h
  have hz := integral_undef h
  rw [chi_normalization c hc] at hz
  norm_num at hz

theorem potential_bounded (c z : ℝ) : |potential c z| ≤ c ^ 2 := by
  have hid := congrArg (fun x : ℝ => c ^ 2 * x) (hyperbolic_identity (c * z))
  have h1 : 0 ≤ c ^ 2 * sech (c * z) ^ 2 := by positivity
  have h2 : 0 ≤ c ^ 2 * Real.tanh (c * z) ^ 2 := by positivity
  unfold potential
  apply abs_le.2
  constructor <;> nlinarith only [hid, h1, h2]


theorem sech_smooth : ContDiff ℝ ∞ sech :=
  contDiff_const.div Real.contDiff_cosh (fun x => ne_of_gt (Real.cosh_pos x))

theorem chi_smooth (c : ℝ) : ContDiff ℝ ∞ (chi c) := by
  exact contDiff_const.mul (sech_smooth.comp (contDiff_const.mul contDiff_id))

theorem potential_smooth (c : ℝ) : ContDiff ℝ ∞ (potential c) := by
  exact contDiff_const.sub
    (contDiff_const.mul ((sech_smooth.comp (contDiff_const.mul contDiff_id)).pow 2))

end MagHK.Axial
