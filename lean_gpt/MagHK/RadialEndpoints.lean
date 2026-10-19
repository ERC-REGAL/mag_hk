import MagHK.Noninteracting
import MagHK.Ordering
import Mathlib.Analysis.Calculus.ContDiff.Deriv

/-!
Concrete origin and partner checks for the two radial constructions.
The origin derivatives prove the required U(r)=O(r), including the removable
singularity in the bounded vector potential. No self-adjoint realization
or closed quadratic form is assumed or constructed in this module.
-/

noncomputable section
namespace MagHK.RadialEndpoints

open MagHK.Noninteracting Filter Asymptotics
open scoped Topology

def gaussianU (t r : ℝ) : ℝ := r + gaussianA t r

theorem gaussianU_hasDerivAt (t r : ℝ) (ht : 0 ≤ t) :
    HasDerivAt (gaussianU t) (1 + gaussianAPrime t r) r :=
  (hasDerivAt_id r).add (gaussianA_hasDerivAt t r ht)

theorem gaussianU_at_zero (t : ℝ) : gaussianU t 0 = 0 := by
  simp [gaussianU, gaussianA]

theorem gaussianU_origin_derivative (t : ℝ) (ht : 0 ≤ t) :
    HasDerivAt (gaussianU t) (1 + t) 0 := by
  simpa [gaussianAPrime] using gaussianU_hasDerivAt t 0 ht

theorem gaussianU_isBigO_at_zero (t : ℝ) (ht : 0 ≤ t) :
    gaussianU t =O[𝓝 (0 : ℝ)] (fun r : ℝ => r) := by
  simpa only [gaussianU_at_zero, sub_zero] using
    (gaussianU_origin_derivative t ht).isBigO_sub

theorem gaussianU_logarithmic_derivative (t r : ℝ) (ht : 0 ≤ t) :
    -(deriv (gaussianF t) r) / gaussianF t r = gaussianU t r := by
  rw [(gaussianF_hasDerivAt t r ht).deriv]
  have hf : gaussianF t r ≠ 0 := ne_of_gt (gaussianF_pos t r ht)
  unfold gaussianU
  field_simp

theorem gaussian_partner_correction (t r : ℝ) (ht : 0 ≤ t) (hr : r ≠ 0) :
    deriv (gaussianU t) r + gaussianA t r / r =
      1 + 2 * t / (1 + t * r ^ 2) ^ 2 := by
  rw [(gaussianU_hasDerivAt t r ht).deriv]
  linarith [gaussian_field t r ht hr]

theorem gaussian_partner_correction_gt_one (t r : ℝ) (ht : 0 < t) (hr : 0 < r) :
    1 < deriv (gaussianU t) r + gaussianA t r / r := by
  rw [gaussian_partner_correction t r ht.le (ne_of_gt hr)]
  have h := gaussian_field_pos t r ht
  linarith

theorem gaussian_angular_bounds (t r : ℝ) (ht : 0 < t) (hr : 0 < r) :
    0 < r * gaussianA t r ∧ r * gaussianA t r < 1 := by
  have hden : 0 < 1 + t * r ^ 2 := by positivity
  have he : r * gaussianA t r = t * r ^ 2 / (1 + t * r ^ 2) := by
    unfold gaussianA
    ring
  rw [he]
  constructor
  · positivity
  · apply (div_lt_one hden).mpr
    linarith

/-- Cancellation of the apparent radial singularity gives the actual
derivative of a_t at the origin, including all real parameter values. -/
theorem profileA_origin_derivative (t : ℝ) : HasDerivAt (profileA t) t 0 := by
  have hE : HasDerivAt (fun r : ℝ => Real.exp (Real.sqrt (1 + r ^ 2) - 1)) 0 0 := by
    simpa using HasDerivAt.exp ((radiusSqrt_hasDerivAt 0).sub_const 1)
  have hn := ((hasDerivAt_id (0 : ℝ)).const_mul t).mul (hE.pow 2)
  have hd := ((((hasDerivAt_id (0 : ℝ)).pow 2).const_mul t).mul (hE.pow 2)).const_add 1
  have heq : profileA t = (fun r : ℝ =>
      t * r * Real.exp (Real.sqrt (1 + r ^ 2) - 1) ^ 2 /
      (1 + t * r ^ 2 * Real.exp (Real.sqrt (1 + r ^ 2) - 1) ^ 2)) :=
    funext (profileA_regular t)
  rw [heq]
  simpa using! hn.div hd (by norm_num)

theorem profileU_at_zero (t : ℝ) : profileU t 0 = 0 := by
  simp [profileU, boundedU, profileH, profileA, boundedA]

/-- The actual derivative is 12+t for the paper's lambda=20. This gives
the regular origin behavior required by the factorization-domain proof. -/
theorem profileU_origin_derivative (t : ℝ) : HasDerivAt (profileU t) (12 + t) 0 := by
  have hh := profileH_hasDerivAt 0
  have hp := profileHPrime_hasDerivAt 0
  have ha := profileA_origin_derivative t
  have hn := (((((hasDerivAt_id (0 : ℝ)).const_mul 20).add
    ((hasDerivAt_id (0 : ℝ)).mul hp)).add (hh.const_mul 3)).add
    ((hasDerivAt_id (0 : ℝ)).mul (hh.pow 2))).add (ha.const_mul 2)
  have hd := (((hasDerivAt_id (0 : ℝ)).mul hh).const_add 1).const_mul 2
  have h := hn.div hd (by norm_num [profileH])
  apply h.congr_deriv
  norm_num [profileH, profileHPrime, profileHSecond, profileA, boundedA]
  <;> ring

theorem profileU_isBigO_at_zero (t : ℝ) :
    profileU t =O[𝓝 (0 : ℝ)] (fun r : ℝ => r) := by
  simpa only [profileU_at_zero, sub_zero] using (profileU_origin_derivative t).isBigO_sub

theorem profileU_logarithmic_derivative (t r : ℝ) (ht : 0 ≤ t) :
    -(deriv (profileF t) r) / profileF t r = profileU t r := by
  rw [(profileF_hasDerivAt t r ht).deriv]
  have hf : profileF t r ≠ 0 := ne_of_gt (profileF_pos t r)
  field_simp

/-- The regular radial coefficient a(r)/r, defined also at zero. -/
def profileACoefficient (t r : ℝ) : ℝ :=
  t * Real.exp (Real.sqrt (1 + r ^ 2) - 1) ^ 2 /
    (1 + t * r ^ 2 * Real.exp (Real.sqrt (1 + r ^ 2) - 1) ^ 2)

theorem profileA_eq_mul_coefficient (t r : ℝ) :
    profileA t r = r * profileACoefficient t r := by
  rw [profileA_regular]
  unfold profileACoefficient
  ring

/-- The regular radial coefficient U(r)/r, defined also at zero. -/
def profileUCoefficient (t r : ℝ) : ℝ :=
  (20 + profileHPrime r + 3 / Real.sqrt (1 + r ^ 2) +
      profileH r ^ 2 + 2 * profileACoefficient t r) /
    (2 * (1 + r * profileH r))

theorem profileU_eq_mul_coefficient (t r : ℝ) :
    profileU t r = r * profileUCoefficient t r := by
  unfold profileU boundedU profileUCoefficient
  rw [profileA_eq_mul_coefficient]
  unfold profileH
  ring

theorem profileUCoefficient_at_zero (t : ℝ) : profileUCoefficient t 0 = 12 + t := by
  norm_num [profileUCoefficient, profileACoefficient, profileH, profileHPrime]
  <;> ring

private theorem radiusSqrt_contDiff :
    ContDiff ℝ ⊤ (fun r : ℝ => Real.sqrt (1 + r ^ 2)) :=
  (contDiff_const.add (contDiff_id.pow 2)).sqrt (fun r => ne_of_gt (by positivity))

private theorem profileH_contDiff : ContDiff ℝ ⊤ profileH :=
  contDiff_id.div radiusSqrt_contDiff (fun r => ne_of_gt (Real.sqrt_pos.mpr (by positivity)))

private theorem profileHPrime_contDiff : ContDiff ℝ ⊤ profileHPrime :=
  contDiff_const.div (radiusSqrt_contDiff.pow 3)
    (fun r => ne_of_gt (by positivity : 0 < Real.sqrt (1 + r ^ 2) ^ 3))

theorem profileACoefficient_contDiff (t : ℝ) (ht : 0 ≤ t) :
    ContDiff ℝ ⊤ (profileACoefficient t) := by
  have hE : ContDiff ℝ ⊤ (fun r : ℝ => Real.exp (Real.sqrt (1 + r ^ 2) - 1)) :=
    (radiusSqrt_contDiff.sub contDiff_const).exp
  have hn : ContDiff ℝ ⊤ (fun r : ℝ =>
      t * Real.exp (Real.sqrt (1 + r ^ 2) - 1) ^ 2) :=
    contDiff_const.mul (hE.pow 2)
  have hd : ContDiff ℝ ⊤ (fun r : ℝ =>
      1 + t * r ^ 2 * Real.exp (Real.sqrt (1 + r ^ 2) - 1) ^ 2) := contDiff_const.add
    ((contDiff_const.mul (contDiff_id.pow 2)).mul (hE.pow 2))
  exact hn.div hd (fun r => ne_of_gt (by positivity :
    0 < 1 + t * r ^ 2 * Real.exp (Real.sqrt (1 + r ^ 2) - 1) ^ 2))

theorem profileUCoefficient_contDiff (t : ℝ) (ht : 0 ≤ t) :
    ContDiff ℝ ⊤ (profileUCoefficient t) := by
  have hdiv : ContDiff ℝ ⊤ (fun r : ℝ => 3 / Real.sqrt (1 + r ^ 2)) :=
    contDiff_const.div radiusSqrt_contDiff
      (fun r => ne_of_gt (Real.sqrt_pos.mpr (by positivity)))
  have hn : ContDiff ℝ ⊤ (fun r : ℝ =>
      20 + profileHPrime r + 3 / Real.sqrt (1 + r ^ 2) +
        profileH r ^ 2 + 2 * profileACoefficient t r) :=
    (((contDiff_const.add profileHPrime_contDiff).add hdiv).add
      (profileH_contDiff.pow 2)).add (contDiff_const.mul (profileACoefficient_contDiff t ht))
  have hd : ContDiff ℝ ⊤ (fun r : ℝ => 2 * (1 + r * profileH r)) :=
    contDiff_const.mul (contDiff_const.add (contDiff_id.mul profileH_contDiff))
  exact hn.div hd (fun r => ne_of_gt (by
    have h := profileH_mul_nonneg r
    positivity))

theorem profileU_contDiff (t : ℝ) (ht : 0 ≤ t) : ContDiff ℝ ⊤ (profileU t) := by
  have heq : profileU t = fun r => r * profileUCoefficient t r :=
    funext (profileU_eq_mul_coefficient t)
  rw [heq]
  exact contDiff_id.mul (profileUCoefficient_contDiff t ht)

theorem profileA_contDiff (t : ℝ) (ht : 0 ≤ t) : ContDiff ℝ ⊤ (profileA t) := by
  have heq : profileA t = fun r => r * profileACoefficient t r :=
    funext (profileA_eq_mul_coefficient t)
  rw [heq]
  exact contDiff_id.mul (profileACoefficient_contDiff t ht)

/-- This is the smooth radial extension of the manuscript's scalar
potential. The raw profileV uses totalized division at zero. -/
def regularProfileV (t r : ℝ) : ℝ :=
  profileU t r ^ 2 - deriv (profileU t) r - profileUCoefficient t r - profileA t r ^ 2

theorem regularProfileV_eq (t r : ℝ) (hr : r ≠ 0) :
    regularProfileV t r = profileV t r := by
  have hratio : profileU t r / r = profileUCoefficient t r := by
    rw [profileU_eq_mul_coefficient]
    field_simp
  unfold regularProfileV profileV
  rw [hratio]

theorem regularProfileV_at_zero (t : ℝ) : regularProfileV t 0 = -(24 + 2 * t) := by
  unfold regularProfileV
  rw [profileU_at_zero, (profileU_origin_derivative t).deriv,
    profileUCoefficient_at_zero]
  simp [profileA, boundedA]
  <;> ring

theorem regularProfileV_contDiff (t : ℝ) (ht : 0 ≤ t) :
    ContDiff ℝ ⊤ (regularProfileV t) := by
  have hU := profileU_contDiff t ht
  have hDU : ContDiff ℝ ⊤ (deriv (profileU t)) :=
    ContDiff.deriv' (n := ⊤) (by simpa using hU)
  exact (((hU.pow 2).sub hDU).sub (profileUCoefficient_contDiff t ht)).sub
    ((profileA_contDiff t ht).pow 2)

theorem rawProfileV_at_zero (t : ℝ) : profileV t 0 = -(12 + t) := by
  unfold profileV
  rw [profileU_at_zero, (profileU_origin_derivative t).deriv]
  simp [profileA, boundedA]

theorem profileV_punctured_limit (t : ℝ) (ht : 0 ≤ t) :
    Tendsto (profileV t) (𝓝[≠] (0 : ℝ)) (𝓝 (-(24 + 2 * t))) := by
  have h : Tendsto (regularProfileV t) (𝓝[≠] (0 : ℝ)) (𝓝 (regularProfileV t 0)) :=
    (regularProfileV_contDiff t ht).continuous.continuousAt.tendsto.mono_left
      nhdsWithin_le_nhds
  rw [regularProfileV_at_zero] at h
  apply h.congr'
  filter_upwards [self_mem_nhdsWithin] with r hr
  exact regularProfileV_eq t r hr

end MagHK.RadialEndpoints
