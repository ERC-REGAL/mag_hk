import MagHK.Noninteracting
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Tactic.FunProp

/-!
Cartesian extensions of the two planar vector potentials. All smoothness
and boundedness statements below concern the displayed functions on the
whole plane, including the origin. No regularity hypothesis is supplied.
-/

noncomputable section
namespace MagHK.Cartesian

open MagHK.Noninteracting
open scoped ContDiff

def radiusSq (p : ℝ × ℝ) : ℝ := p.1 ^ 2 + p.2 ^ 2
def gaussianCoefficient (t : ℝ) (p : ℝ × ℝ) : ℝ := t / (1 + t * radiusSq p)
def radialExponential (p : ℝ × ℝ) : ℝ := Real.exp (Real.sqrt (1 + radiusSq p) - 1)
def boundedCoefficient (t : ℝ) (p : ℝ × ℝ) : ℝ :=
  t * radialExponential p ^ 2 / (1 + t * radiusSq p * radialExponential p ^ 2)

def gaussianVector (t : ℝ) (p : ℝ × ℝ) : ℝ × ℝ :=
  (-p.2 * gaussianCoefficient t p, p.1 * gaussianCoefficient t p)

def boundedVector (t : ℝ) (p : ℝ × ℝ) : ℝ × ℝ :=
  (-p.2 * boundedCoefficient t p, p.1 * boundedCoefficient t p)

def gaussianScalar (t : ℝ) (p : ℝ × ℝ) : ℝ :=
  radiusSq p - 2 / (1 + t * radiusSq p) - 2 * t / (1 + t * radiusSq p) ^ 2

theorem radiusSq_nonneg (p : ℝ × ℝ) : 0 ≤ radiusSq p := by
  unfold radiusSq
  positivity

theorem radiusSq_contDiff : ContDiff ℝ ∞ radiusSq :=
  (contDiff_fst.pow 2).add (contDiff_snd.pow 2)

theorem radialExponential_contDiff : ContDiff ℝ ∞ radialExponential := by
  have hs : ContDiff ℝ ∞ (fun p : ℝ × ℝ => Real.sqrt (1 + radiusSq p)) :=
    (contDiff_const.add radiusSq_contDiff).sqrt
      (fun p => ne_of_gt (by have := radiusSq_nonneg p; positivity))
  exact (hs.sub contDiff_const).exp

theorem gaussianCoefficient_contDiff (t : ℝ) (ht : 0 ≤ t) :
    ContDiff ℝ ∞ (gaussianCoefficient t) := by
  apply contDiff_const.div (contDiff_const.add (contDiff_const.mul radiusSq_contDiff))
  intro p
  have := radiusSq_nonneg p
  positivity

theorem boundedCoefficient_contDiff (t : ℝ) (ht : 0 ≤ t) :
    ContDiff ℝ ∞ (boundedCoefficient t) := by
  apply (contDiff_const.mul (radialExponential_contDiff.pow 2)).div
    (contDiff_const.add ((contDiff_const.mul radiusSq_contDiff).mul
      (radialExponential_contDiff.pow 2)))
  intro p
  have := radiusSq_nonneg p
  positivity

theorem gaussianVector_contDiff (t : ℝ) (ht : 0 ≤ t) :
    ContDiff ℝ ∞ (gaussianVector t) :=
  (contDiff_snd.neg.mul (gaussianCoefficient_contDiff t ht)).prodMk
    (contDiff_fst.mul (gaussianCoefficient_contDiff t ht))

theorem boundedVector_contDiff (t : ℝ) (ht : 0 ≤ t) :
    ContDiff ℝ ∞ (boundedVector t) :=
  (contDiff_snd.neg.mul (boundedCoefficient_contDiff t ht)).prodMk
    (contDiff_fst.mul (boundedCoefficient_contDiff t ht))

theorem gaussianScalar_contDiff (t : ℝ) (ht : 0 ≤ t) :
    ContDiff ℝ ∞ (gaussianScalar t) := by
  have hd : ContDiff ℝ ∞ (fun p : ℝ × ℝ => 1 + t * radiusSq p) :=
    contDiff_const.add (contDiff_const.mul radiusSq_contDiff)
  have hn : ∀ p : ℝ × ℝ, 1 + t * radiusSq p ≠ 0 := by
    intro p
    have := radiusSq_nonneg p
    positivity
  exact (radiusSq_contDiff.sub (contDiff_const.div hd hn)).sub
    (contDiff_const.div (hd.pow 2) (fun p => pow_ne_zero _ (hn p)))

theorem gaussianVector_origin (t : ℝ) : gaussianVector t (0, 0) = (0, 0) := by
  simp [gaussianVector]

theorem boundedVector_origin (t : ℝ) : boundedVector t (0, 0) = (0, 0) := by
  simp [boundedVector]

theorem boundedCoefficient_radial (t r : ℝ) (p : ℝ × ℝ)
    (hp : radiusSq p = r ^ 2) : boundedCoefficient t p * r = profileA t r := by
  rw [profileA_regular]
  unfold boundedCoefficient radialExponential
  rw [hp]
  ring

theorem gaussianCoefficient_radial (t r : ℝ) (p : ℝ × ℝ)
    (hp : radiusSq p = r ^ 2) : gaussianCoefficient t p * r = gaussianA t r := by
  unfold gaussianCoefficient gaussianA
  rw [hp]
  ring

theorem boundedVector_radial (t r : ℝ) (p : ℝ × ℝ)
    (hp : radiusSq p = r ^ 2) (hr : r ≠ 0) :
    boundedVector t p = (-p.2 * (profileA t r / r), p.1 * (profileA t r / r)) := by
  have hc : boundedCoefficient t p = profileA t r / r :=
    (eq_div_iff hr).2 (boundedCoefficient_radial t r p hp)
  simp only [boundedVector, hc]

/-- A global coordinate estimate that avoids differentiating polar coordinates. -/
theorem coordinate_coefficient_bound (x q c M : ℝ)
    (hx : x ^ 2 ≤ q) (hc : 0 ≤ c) (hM : 0 ≤ M)
    (hcq : c * q ≤ 1) (hsmall : q ≤ 1 → c ≤ M) : |x * c| ≤ M + 1 := by
  rw [abs_mul, abs_of_nonneg hc]
  by_cases hq : q ≤ 1
  · have hx1 : |x| ≤ 1 := by nlinarith [sq_abs x, abs_nonneg x]
    have hh := hsmall hq
    calc
      |x| * c ≤ 1 * c := mul_le_mul_of_nonneg_right hx1 hc
      _ ≤ M + 1 := by linarith
  · have hq1 : 1 ≤ q := le_of_not_ge hq
    have hq0 : 0 ≤ q := by linarith
    have hq2 : q ≤ q ^ 2 := by nlinarith [mul_nonneg hq0 (sub_nonneg.2 hq1)]
    have hxq : |x| ≤ q := by nlinarith [sq_abs x, abs_nonneg x]
    calc
      |x| * c ≤ q * c := mul_le_mul_of_nonneg_right hxq hc
      _ ≤ M + 1 := by nlinarith

theorem gaussianCoefficient_estimates (t : ℝ) (ht : 0 ≤ t) (p : ℝ × ℝ) :
    0 ≤ gaussianCoefficient t p ∧
    gaussianCoefficient t p * radiusSq p ≤ 1 ∧ gaussianCoefficient t p ≤ t := by
  have hq := radiusSq_nonneg p
  have hd : 0 < 1 + t * radiusSq p := by positivity
  unfold gaussianCoefficient
  refine ⟨by positivity, ?_, ?_⟩
  · rw [div_mul_eq_mul_div]
    apply (div_le_one hd).2
    linarith
  · apply (div_le_iff₀ hd).2
    nlinarith [mul_nonneg (sq_nonneg t) hq]

theorem boundedCoefficient_estimates (t : ℝ) (ht : 0 ≤ t) (p : ℝ × ℝ) :
    0 ≤ boundedCoefficient t p ∧
    boundedCoefficient t p * radiusSq p ≤ 1 ∧
    (radiusSq p ≤ 1 → boundedCoefficient t p ≤ t * Real.exp 2) := by
  have hq := radiusSq_nonneg p
  have hd : 0 < 1 + t * radiusSq p * radialExponential p ^ 2 := by positivity
  refine ⟨by unfold boundedCoefficient; positivity, ?_, ?_⟩
  · unfold boundedCoefficient
    rw [div_mul_eq_mul_div]
    apply (div_le_one hd).2
    nlinarith
  · intro hq1
    have hs : Real.sqrt (1 + radiusSq p) ≤ 2 :=
      (Real.sqrt_le_left (by norm_num)).2 (by linarith)
    have he : radialExponential p ^ 2 ≤ Real.exp 2 := by
      unfold radialExponential
      rw [pow_two, ← Real.exp_add]
      apply Real.exp_le_exp.2
      linarith
    have hc : boundedCoefficient t p ≤ t * radialExponential p ^ 2 := by
      unfold boundedCoefficient
      apply (div_le_iff₀ hd).2
      have hn : 0 ≤ (t * radialExponential p ^ 2) *
          (t * radiusSq p * radialExponential p ^ 2) := by positivity
      nlinarith
    exact hc.trans (mul_le_mul_of_nonneg_left he ht)

theorem gaussianVector_bound (t : ℝ) (ht : 0 ≤ t) (p : ℝ × ℝ) :
    ‖gaussianVector t p‖ ≤ t + 1 := by
  have he := gaussianCoefficient_estimates t ht p
  have hx : p.1 ^ 2 ≤ radiusSq p := by unfold radiusSq; nlinarith [sq_nonneg p.2]
  have hy : (-p.2) ^ 2 ≤ radiusSq p := by unfold radiusSq; nlinarith [sq_nonneg p.1]
  rw [gaussianVector, Prod.norm_def]
  apply max_le
  · exact coordinate_coefficient_bound (-p.2) (radiusSq p) _ t hy he.1 ht he.2.1
      (fun _ => he.2.2)
  · exact coordinate_coefficient_bound p.1 (radiusSq p) _ t hx he.1 ht he.2.1
      (fun _ => he.2.2)

theorem boundedVector_bound (t : ℝ) (ht : 0 ≤ t) (p : ℝ × ℝ) :
    ‖boundedVector t p‖ ≤ t * Real.exp 2 + 1 := by
  have he := boundedCoefficient_estimates t ht p
  have hx : p.1 ^ 2 ≤ radiusSq p := by unfold radiusSq; nlinarith [sq_nonneg p.2]
  have hy : (-p.2) ^ 2 ≤ radiusSq p := by unfold radiusSq; nlinarith [sq_nonneg p.1]
  rw [boundedVector, Prod.norm_def]
  apply max_le
  · exact coordinate_coefficient_bound (-p.2) (radiusSq p) _ _ hy he.1
      (by positivity) he.2.1 he.2.2
  · exact coordinate_coefficient_bound p.1 (radiusSq p) _ _ hx he.1
      (by positivity) he.2.1 he.2.2

theorem gaussianScalar_correction_bound (t : ℝ) (ht : 0 ≤ t) (p : ℝ × ℝ) :
    |gaussianScalar t p - radiusSq p| ≤ 2 + 2 * t := by
  have hq := radiusSq_nonneg p
  have hd : 0 < 1 + t * radiusSq p := by positivity
  have hd1 : 1 ≤ 1 + t * radiusSq p := by nlinarith [mul_nonneg ht hq]
  have hd2 : 1 ≤ (1 + t * radiusSq p) ^ 2 := one_le_pow₀ hd1
  have ha : 2 / (1 + t * radiusSq p) ≤ 2 := by
    apply (div_le_iff₀ hd).2
    linarith
  have hb : 2 * t / (1 + t * radiusSq p) ^ 2 ≤ 2 * t := by
    apply (div_le_iff₀ (sq_pos_of_pos hd)).2
    nlinarith [mul_nonneg ht (sub_nonneg.2 hd2)]
  have ha0 : 0 ≤ 2 / (1 + t * radiusSq p) := by positivity
  have hb0 : 0 ≤ 2 * t / (1 + t * radiusSq p) ^ 2 := by positivity
  unfold gaussianScalar
  rw [abs_of_nonpos (by linarith)]
  linarith

/-- Regular coefficient `1/sqrt(1+r²)` written directly in Cartesian variables. -/
def inverseRadius (p : ℝ × ℝ) : ℝ := 1 / Real.sqrt (1 + radiusSq p)
def regularDenominator (p : ℝ × ℝ) : ℝ := 1 + radiusSq p * inverseRadius p
def baseNumerator (p : ℝ × ℝ) : ℝ :=
  20 + inverseRadius p ^ 3 + 3 * inverseRadius p + radiusSq p * inverseRadius p ^ 2
def uCoefficient (t : ℝ) (p : ℝ × ℝ) : ℝ :=
  (baseNumerator p + 2 * boundedCoefficient t p) / (2 * regularDenominator p)

/-- Explicit regular formula for the radial derivative `U'_t`. -/
def uPrimeExtension (t : ℝ) (p : ℝ × ℝ) : ℝ :=
  ((20 + 4 * inverseRadius p ^ 3 - 3 * radiusSq p * inverseRadius p ^ 5 +
      radiusSq p * inverseRadius p ^ 2 + 2 * radiusSq p * inverseRadius p ^ 4) *
      regularDenominator p - radiusSq p * baseNumerator p *
        (inverseRadius p + inverseRadius p ^ 3)) / (2 * regularDenominator p ^ 2) +
  ((2 * regularDenominator p * boundedCoefficient t p *
      (1 - radiusSq p * boundedCoefficient t p) - boundedCoefficient t p) *
      regularDenominator p - radiusSq p * boundedCoefficient t p *
        (inverseRadius p + inverseRadius p ^ 3)) / regularDenominator p ^ 2

/-- The smooth planar scalar extension. The raw polar formula uses division by
    zero at the origin and has a different totalized value there. -/
def boundedScalar (t : ℝ) (p : ℝ × ℝ) : ℝ :=
  radiusSq p * uCoefficient t p ^ 2 - uPrimeExtension t p - uCoefficient t p -
    radiusSq p * boundedCoefficient t p ^ 2

theorem inverseRadius_pos (p : ℝ × ℝ) : 0 < inverseRadius p := by
  unfold inverseRadius
  have := radiusSq_nonneg p
  positivity

theorem regularDenominator_pos (p : ℝ × ℝ) : 0 < regularDenominator p := by
  unfold regularDenominator
  have := radiusSq_nonneg p
  have := inverseRadius_pos p
  positivity

theorem inverseRadius_contDiff : ContDiff ℝ ∞ inverseRadius := by
  apply contDiff_const.div ((contDiff_const.add radiusSq_contDiff).sqrt
    (fun p => ne_of_gt (by have := radiusSq_nonneg p; positivity)))
  intro p
  have := radiusSq_nonneg p
  positivity

theorem regularDenominator_contDiff : ContDiff ℝ ∞ regularDenominator :=
  contDiff_const.add (radiusSq_contDiff.mul inverseRadius_contDiff)

theorem baseNumerator_contDiff : ContDiff ℝ ∞ baseNumerator :=
  ((contDiff_const.add (inverseRadius_contDiff.pow 3)).add
    (contDiff_const.mul inverseRadius_contDiff)).add
      (radiusSq_contDiff.mul (inverseRadius_contDiff.pow 2))

theorem uCoefficient_contDiff (t : ℝ) (ht : 0 ≤ t) : ContDiff ℝ ∞ (uCoefficient t) := by
  apply (baseNumerator_contDiff.add (contDiff_const.mul (boundedCoefficient_contDiff t ht))).div
    (contDiff_const.mul regularDenominator_contDiff)
  intro p
  have := regularDenominator_pos p
  positivity

theorem uPrimeExtension_contDiff (t : ℝ) (ht : 0 ≤ t) :
    ContDiff ℝ ∞ (uPrimeExtension t) := by
  have hI := inverseRadius_contDiff
  have hQ := radiusSq_contDiff
  have hD := regularDenominator_contDiff
  have hN := baseNumerator_contDiff
  have hC := boundedCoefficient_contDiff t ht
  have hbase : ContDiff ℝ ∞ (fun p : ℝ × ℝ =>
      (20 + 4 * inverseRadius p ^ 3 - 3 * radiusSq p * inverseRadius p ^ 5 +
        radiusSq p * inverseRadius p ^ 2 + 2 * radiusSq p * inverseRadius p ^ 4) *
        regularDenominator p - radiusSq p * baseNumerator p *
          (inverseRadius p + inverseRadius p ^ 3)) := by fun_prop
  have hcorr : ContDiff ℝ ∞ (fun p : ℝ × ℝ =>
      (2 * regularDenominator p * boundedCoefficient t p *
        (1 - radiusSq p * boundedCoefficient t p) - boundedCoefficient t p) *
        regularDenominator p - radiusSq p * boundedCoefficient t p *
          (inverseRadius p + inverseRadius p ^ 3)) := by fun_prop
  exact (hbase.div (contDiff_const.mul (hD.pow 2))
    (fun p => ne_of_gt (by have := regularDenominator_pos p; positivity))).add
    (hcorr.div (hD.pow 2) (fun p => pow_ne_zero _ (regularDenominator_pos p).ne'))

theorem boundedScalar_contDiff (t : ℝ) (ht : 0 ≤ t) :
    ContDiff ℝ ∞ (boundedScalar t) :=
  (((radiusSq_contDiff.mul ((uCoefficient_contDiff t ht).pow 2)).sub
    (uPrimeExtension_contDiff t ht)).sub (uCoefficient_contDiff t ht)).sub
      (radiusSq_contDiff.mul ((boundedCoefficient_contDiff t ht).pow 2))

theorem radial_profile_identities (r : ℝ) (p : ℝ × ℝ) (hp : radiusSq p = r ^ 2) :
    profileH r = r * inverseRadius p ∧
    profileHPrime r = inverseRadius p ^ 3 ∧
    profileHSecond r = -3 * r * inverseRadius p ^ 5 := by
  unfold profileH profileHPrime profileHSecond inverseRadius
  rw [hp]
  refine ⟨by ring, ?_, ?_⟩
  · rw [div_pow, one_pow]
  · rw [div_pow, one_pow]
    ring

theorem profileU_cartesian (t r : ℝ) (p : ℝ × ℝ) (hp : radiusSq p = r ^ 2) :
    profileU t r = r * uCoefficient t p := by
  have hh := radial_profile_identities r p hp
  have ha : profileA t r = r * boundedCoefficient t p := by
    rw [← boundedCoefficient_radial t r p hp]
    ring
  have hD0 := regularDenominator_pos p
  unfold regularDenominator at hD0
  rw [hp] at hD0
  have hd : 1 + r * (r * inverseRadius p) ≠ 0 := by nlinarith
  unfold profileU boundedU uCoefficient baseNumerator regularDenominator
  rw [hh.1, hh.2.1, ha, hp]
  field_simp [hd, hD0.ne'] <;> ring

theorem profileUPrime_cartesian (t r : ℝ) (p : ℝ × ℝ)
    (hp : radiusSq p = r ^ 2) (hr : r ≠ 0) :
    boundedUPrime 20 r (profileH r) (profileHPrime r) (profileHSecond r) (profileA t r) =
      uPrimeExtension t p := by
  have hh := radial_profile_identities r p hp
  have ha : profileA t r = r * boundedCoefficient t p := by
    rw [← boundedCoefficient_radial t r p hp]
    ring
  have hD0 := regularDenominator_pos p
  unfold regularDenominator at hD0
  rw [hp] at hD0
  have hd : 1 + r * (r * inverseRadius p) ≠ 0 := by nlinarith
  rw [hh.1, hh.2.1, hh.2.2, ha]
  unfold boundedUPrime baseUPrime uPrimeExtension regularDenominator baseNumerator
  rw [hp]
  field_simp [hr, hd, hD0.ne']
  ring

theorem boundedScalar_agrees_off_axis (t r : ℝ) (p : ℝ × ℝ)
    (ht : 0 < t) (hr : 0 < r) (hp : radiusSq p = r ^ 2) :
    boundedScalar t p = profileV t r := by
  have ha : profileA t r = r * boundedCoefficient t p := by
    rw [← boundedCoefficient_radial t r p hp]
    ring
  unfold profileV boundedScalar
  rw [(profileU_hasDerivAt t r ht hr).deriv,
    profileUPrime_cartesian t r p hp hr.ne', profileU_cartesian t r p hp, ha, hp]
  field_simp <;> ring

theorem boundedScalar_origin (t : ℝ) : boundedScalar t (0, 0) = -2 * (12 + t) := by
  norm_num [boundedScalar, uCoefficient, uPrimeExtension, baseNumerator,
    regularDenominator, inverseRadius, boundedCoefficient, radialExponential, radiusSq]
  ring

end MagHK.Cartesian
