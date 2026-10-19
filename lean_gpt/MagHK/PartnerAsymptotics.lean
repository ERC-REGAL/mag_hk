import MagHK.PotentialInfinity
import Mathlib.Analysis.Asymptotics.Lemmas

/-!
Concrete coefficients for the partner radial operator. The unitary change
from radial measure r dr to dr produces the leading coefficient 3/(4r²).
The estimates here concern the actual profile functions, without assuming
operator realizations or limit-point conclusions.
-/

noncomputable section
namespace MagHK.PartnerAsymptotics

open MagHK.Noninteracting MagHK.RadialEndpoints MagHK.PotentialInfinity
open Filter Set Asymptotics
open scoped Topology

theorem profileACoefficient_eq_div (t r : ℝ) (hr : r ≠ 0) :
    profileACoefficient t r = profileA t r / r := by
  rw [profileA_eq_mul_coefficient]
  field_simp

theorem profileUCoefficient_eq_div (t r : ℝ) (hr : r ≠ 0) :
    profileUCoefficient t r = profileU t r / r := by
  rw [profileU_eq_mul_coefficient]
  field_simp

theorem profileACoefficient_tendsto_atTop (t : ℝ) (ht : 0 < t) :
    Tendsto (profileACoefficient t) atTop (𝓝 0) := by
  have h : Tendsto (fun r : ℝ => profileA t r / r) atTop (𝓝 0) := by
    simpa only [div_eq_mul_inv, zero_mul] using!
      (profileA_tendsto_atTop t ht).mul tendsto_inv_atTop_zero
  apply h.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with r hr
  exact (profileACoefficient_eq_div t r (ne_of_gt hr)).symm

theorem profileUCoefficient_tendsto_atTop (t : ℝ) (ht : 0 < t) :
    Tendsto (profileUCoefficient t) atTop (𝓝 0) := by
  have h : Tendsto (fun r : ℝ => profileU t r / r) atTop (𝓝 0) := by
    simpa only [div_eq_mul_inv, mul_zero] using!
      (profileU_tendsto_atTop t ht).mul tendsto_inv_atTop_zero
  apply h.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with r hr
  exact (profileUCoefficient_eq_div t r (ne_of_gt hr)).symm

/-- Smooth extension of the correction U′+a/r. -/
def profileW (t r : ℝ) : ℝ :=
  deriv (profileU t) r + profileACoefficient t r

theorem profileW_eq (t r : ℝ) (hr : r ≠ 0) :
    profileW t r = deriv (profileU t) r + profileA t r / r := by
  rw [profileW, profileACoefficient_eq_div t r hr]

theorem profileW_pos (t r : ℝ) (ht : 0 < t) (hr : 0 < r) : 0 < profileW t r := by
  rw [profileW_eq t r (ne_of_gt hr)]
  exact positive_margin_positive t r ht hr

theorem profileW_contDiff (t : ℝ) (ht : 0 ≤ t) :
    ContDiff ℝ ⊤ (profileW t) := by
  have hd : ContDiff ℝ ⊤ (deriv (profileU t)) :=
    ContDiff.deriv' (n := ⊤) (by simpa using profileU_contDiff t ht)
  exact hd.add (profileACoefficient_contDiff t ht)

theorem profileW_at_zero (t : ℝ) : profileW t 0 = 12 + 2 * t := by
  rw [profileW, (profileU_origin_derivative t).deriv]
  norm_num [profileACoefficient]
  <;> ring

theorem profileW_tendsto_atTop (t : ℝ) (ht : 0 < t) :
    Tendsto (profileW t) atTop (𝓝 0) := by
  simpa only [profileW, add_zero] using!
    (profileU_deriv_tendsto_atTop t ht).add (profileACoefficient_tendsto_atTop t ht)

theorem profileW_bounded (t : ℝ) (ht : 0 < t) :
    ∃ C : ℝ, ∀ r : ℝ, 0 ≤ r → |profileW t r| ≤ C :=
  continuous_halfline_bounded_of_tendsto (profileW_contDiff t ht.le).continuous.continuousOn
    (profileW_tendsto_atTop t ht)

/-- The regular remainder of the transformed partner coefficient. -/
def profilePartnerRemainder (t r : ℝ) : ℝ :=
  profileU t r ^ 2 + deriv (profileU t) r - profileUCoefficient t r

/-- The partner coefficient after multiplication of the radial state by sqrt(r). -/
def profilePartnerCoefficient (t r : ℝ) : ℝ :=
  3 / (4 * r ^ 2) + profilePartnerRemainder t r

theorem profilePartnerCoefficient_eq (t r : ℝ) (hr : r ≠ 0) :
    profilePartnerCoefficient t r = 3 / (4 * r ^ 2) +
      profileU t r ^ 2 + deriv (profileU t) r - profileU t r / r := by
  rw [profilePartnerCoefficient, profilePartnerRemainder, profileUCoefficient_eq_div t r hr]
  ring

/-- Agreement with the transformed m=-1 potential plus the partner correction. -/
theorem profilePartnerCoefficient_from_radial (t r : ℝ) (hr : r ≠ 0) :
    profilePartnerCoefficient t r =
      (-1 / r + profileA t r) ^ 2 + profileV t r +
        2 * profileW t r - 1 / (4 * r ^ 2) := by
  rw [profilePartnerCoefficient_eq t r hr, profileW_eq t r hr]
  unfold profileV
  field_simp
  <;> ring

theorem profilePartnerRemainder_contDiff (t : ℝ) (ht : 0 ≤ t) :
    ContDiff ℝ ⊤ (profilePartnerRemainder t) := by
  have hd : ContDiff ℝ ⊤ (deriv (profileU t)) :=
    ContDiff.deriv' (n := ⊤) (by simpa using profileU_contDiff t ht)
  exact (((profileU_contDiff t ht).pow 2).add hd).sub
    (profileUCoefficient_contDiff t ht)

theorem profilePartnerRemainder_at_zero (t : ℝ) : profilePartnerRemainder t 0 = 0 := by
  simp [profilePartnerRemainder, profileU_at_zero,
    (profileU_origin_derivative t).deriv, profileUCoefficient_at_zero]

theorem profilePartnerRemainder_tendsto_zero (t : ℝ) (ht : 0 ≤ t) :
    Tendsto (profilePartnerRemainder t) (𝓝 (0 : ℝ)) (𝓝 0) := by
  simpa only [profilePartnerRemainder_at_zero] using
    ((profilePartnerRemainder_contDiff t ht).continuous.continuousAt
      (x := (0 : ℝ))).tendsto

theorem profilePartnerRemainder_tendsto_atTop (t : ℝ) (ht : 0 < t) :
    Tendsto (profilePartnerRemainder t) atTop (𝓝 (441 / 4)) := by
  have h := (((profileU_tendsto_atTop t ht).pow 2).add
    (profileU_deriv_tendsto_atTop t ht)).sub (profileUCoefficient_tendsto_atTop t ht)
  norm_num at h
  exact h

theorem profilePartnerRemainder_bounded (t : ℝ) (ht : 0 < t) :
    ∃ C : ℝ, ∀ r : ℝ, 0 ≤ r → |profilePartnerRemainder t r| ≤ C :=
  continuous_halfline_bounded_of_tendsto
    (profilePartnerRemainder_contDiff t ht.le).continuous.continuousOn
    (profilePartnerRemainder_tendsto_atTop t ht)

theorem profilePartner_at_origin (t : ℝ) (ht : 0 ≤ t) :
    (fun r : ℝ => profilePartnerCoefficient t r - 3 / (4 * r ^ 2))
      =O[𝓝 (0 : ℝ)] (fun _ : ℝ => (1 : ℝ)) := by
  simpa only [profilePartnerCoefficient, add_sub_cancel_left] using
    (profilePartnerRemainder_tendsto_zero t ht).isBigO_one ℝ

theorem profilePartner_near_origin (t : ℝ) (ht : 0 < t) :
    ∃ C : ℝ, ∀ r : ℝ, 0 < r → r ≤ 1 →
      |profilePartnerCoefficient t r - 3 / (4 * r ^ 2)| ≤ C := by
  obtain ⟨C, hC⟩ := profilePartnerRemainder_bounded t ht
  exact ⟨C, fun r hr _ => by
    simpa only [profilePartnerCoefficient, add_sub_cancel_left] using hC r hr.le⟩

theorem profilePartner_lower_bound (t : ℝ) (ht : 0 < t) :
    ∃ C : ℝ, ∀ r : ℝ, 0 ≤ r → -C ≤ profilePartnerCoefficient t r := by
  obtain ⟨C, hC⟩ := profilePartnerRemainder_bounded t ht
  refine ⟨C, fun r hr => ?_⟩
  have h := (abs_le.mp (hC r hr)).1
  have hlead : 0 ≤ 3 / (4 * r ^ 2) := by positivity
  dsimp [profilePartnerCoefficient]
  linarith

theorem profilePartner_lower_bound_at_infinity (t : ℝ) (ht : 0 < t) :
    ∃ R C : ℝ, ∀ r : ℝ, R ≤ r → -C ≤ profilePartnerCoefficient t r := by
  obtain ⟨C, hC⟩ := profilePartner_lower_bound t ht
  exact ⟨0, C, hC⟩

theorem profilePartner_tendsto_atTop (t : ℝ) (ht : 0 < t) :
    Tendsto (profilePartnerCoefficient t) atTop (𝓝 (441 / 4)) := by
  have hi : Tendsto (fun r : ℝ => 3 / (4 * r ^ 2)) atTop (𝓝 0) := by
    have h := (tendsto_inv_atTop_zero.pow 2).const_mul (3 / 4 : ℝ)
    norm_num at h
    convert h using 1 <;> ext r <;> simp [div_eq_mul_inv, mul_inv_rev, inv_pow] <;> ring
  simpa only [profilePartnerCoefficient, zero_add] using!
    hi.add (profilePartnerRemainder_tendsto_atTop t ht)

theorem profilePartner_above_lambda_eventually (t : ℝ) (ht : 0 < t) :
    ∀ᶠ r in atTop, 20 < profilePartnerCoefficient t r :=
  (profilePartner_tendsto_atTop t ht).eventually
    (eventually_gt_nhds (show (20 : ℝ) < 441 / 4 by norm_num))

/-! The same endpoint checks for the Gaussian construction. -/

def gaussianACoefficient (t r : ℝ) : ℝ := t / (1 + t * r ^ 2)
def gaussianUCoefficient (t r : ℝ) : ℝ := 1 + gaussianACoefficient t r

theorem gaussianA_eq_mul_coefficient (t r : ℝ) :
    gaussianA t r = r * gaussianACoefficient t r := by
  unfold gaussianA gaussianACoefficient
  ring

theorem gaussianU_eq_mul_coefficient (t r : ℝ) :
    gaussianU t r = r * gaussianUCoefficient t r := by
  rw [gaussianU, gaussianA_eq_mul_coefficient]
  unfold gaussianUCoefficient
  ring

theorem gaussianACoefficient_contDiff (t : ℝ) (ht : 0 ≤ t) :
    ContDiff ℝ ⊤ (gaussianACoefficient t) :=
  contDiff_const.div (contDiff_const.add (contDiff_const.mul (contDiff_id.pow 2)))
    (fun r => ne_of_gt (by positivity : 0 < 1 + t * r ^ 2))

theorem gaussianUCoefficient_contDiff (t : ℝ) (ht : 0 ≤ t) :
    ContDiff ℝ ⊤ (gaussianUCoefficient t) :=
  contDiff_const.add (gaussianACoefficient_contDiff t ht)

theorem gaussianA_contDiff (t : ℝ) (ht : 0 ≤ t) : ContDiff ℝ ⊤ (gaussianA t) := by
  rw [show gaussianA t = (fun r => r * gaussianACoefficient t r) from
    funext (gaussianA_eq_mul_coefficient t)]
  exact contDiff_id.mul (gaussianACoefficient_contDiff t ht)

theorem gaussianU_contDiff (t : ℝ) (ht : 0 ≤ t) : ContDiff ℝ ⊤ (gaussianU t) :=
  contDiff_id.add (gaussianA_contDiff t ht)

def gaussianW (t r : ℝ) : ℝ := 1 + 2 * t / (1 + t * r ^ 2) ^ 2

theorem gaussianW_eq (t r : ℝ) (ht : 0 ≤ t) (hr : r ≠ 0) :
    gaussianW t r = deriv (gaussianU t) r + gaussianA t r / r :=
  (gaussian_partner_correction t r ht hr).symm

theorem gaussianW_contDiff (t : ℝ) (ht : 0 ≤ t) : ContDiff ℝ ⊤ (gaussianW t) :=
  contDiff_const.add (contDiff_const.div
    ((contDiff_const.add (contDiff_const.mul (contDiff_id.pow 2))).pow 2)
    (fun r => ne_of_gt (by positivity : 0 < (1 + t * r ^ 2) ^ 2)))

theorem gaussianW_bounds (t r : ℝ) (ht : 0 ≤ t) :
    1 ≤ gaussianW t r ∧ |gaussianW t r| ≤ 1 + 2 * t := by
  have hn : 0 ≤ t * r ^ 2 := by positivity
  have hD : 1 ≤ (1 + t * r ^ 2) ^ 2 := one_le_pow₀ (by linarith)
  have hq : 0 ≤ 2 * t / (1 + t * r ^ 2) ^ 2 := by positivity
  have hq' : 2 * t / (1 + t * r ^ 2) ^ 2 ≤ 2 * t :=
    div_le_self (by positivity) hD
  unfold gaussianW
  rw [abs_of_nonneg (by positivity)]
  constructor <;> linarith

theorem gaussianW_bounded (t : ℝ) (ht : 0 ≤ t) :
    ∃ C : ℝ, ∀ r : ℝ, 0 ≤ r → |gaussianW t r| ≤ C :=
  ⟨1 + 2 * t, fun r _ => (gaussianW_bounds t r ht).2⟩

def gaussianPartnerRemainder (t r : ℝ) : ℝ :=
  gaussianU t r ^ 2 + deriv (gaussianU t) r - gaussianUCoefficient t r

def gaussianPartnerCoefficient (t r : ℝ) : ℝ :=
  3 / (4 * r ^ 2) + gaussianPartnerRemainder t r

theorem gaussianPartnerCoefficient_eq (t r : ℝ) (hr : r ≠ 0) :
    gaussianPartnerCoefficient t r = 3 / (4 * r ^ 2) +
      gaussianU t r ^ 2 + deriv (gaussianU t) r - gaussianU t r / r := by
  have hratio : gaussianU t r / r = gaussianUCoefficient t r := by
    rw [gaussianU_eq_mul_coefficient]
    field_simp
  rw [hratio]
  unfold gaussianPartnerCoefficient gaussianPartnerRemainder
  ring

theorem gaussianPartnerCoefficient_from_radial (t r : ℝ)
    (ht : 0 ≤ t) (hr : r ≠ 0) :
    gaussianPartnerCoefficient t r =
      (-1 / r + gaussianA t r) ^ 2 +
        (r ^ 2 - 2 / (1 + t * r ^ 2) - 2 * t / (1 + t * r ^ 2) ^ 2) +
        2 * gaussianW t r - 1 / (4 * r ^ 2) := by
  rw [gaussianPartnerCoefficient_eq t r hr, gaussianW_eq t r ht hr,
    gaussian_scalar_factorization t r ht hr, (gaussianU_hasDerivAt t r ht).deriv]
  unfold gaussianU
  field_simp
  <;> ring

theorem gaussianPartnerRemainder_contDiff (t : ℝ) (ht : 0 ≤ t) :
    ContDiff ℝ ⊤ (gaussianPartnerRemainder t) := by
  have hd : ContDiff ℝ ⊤ (deriv (gaussianU t)) :=
    ContDiff.deriv' (n := ⊤) (by simpa using gaussianU_contDiff t ht)
  exact (((gaussianU_contDiff t ht).pow 2).add hd).sub
    (gaussianUCoefficient_contDiff t ht)

theorem gaussianPartnerRemainder_at_zero (t : ℝ) (ht : 0 ≤ t) :
    gaussianPartnerRemainder t 0 = 0 := by
  simp [gaussianPartnerRemainder, gaussianU_at_zero,
    (gaussianU_origin_derivative t ht).deriv, gaussianUCoefficient, gaussianACoefficient]

theorem gaussianPartnerRemainder_tendsto_zero (t : ℝ) (ht : 0 ≤ t) :
    Tendsto (gaussianPartnerRemainder t) (𝓝 (0 : ℝ)) (𝓝 0) := by
  simpa only [gaussianPartnerRemainder_at_zero t ht] using
    ((gaussianPartnerRemainder_contDiff t ht).continuous.continuousAt
      (x := (0 : ℝ))).tendsto

theorem gaussianPartner_at_origin (t : ℝ) (ht : 0 ≤ t) :
    (fun r : ℝ => gaussianPartnerCoefficient t r - 3 / (4 * r ^ 2))
      =O[𝓝 (0 : ℝ)] (fun _ : ℝ => (1 : ℝ)) := by
  simpa only [gaussianPartnerCoefficient, add_sub_cancel_left] using
    (gaussianPartnerRemainder_tendsto_zero t ht).isBigO_one ℝ

theorem gaussianPartner_near_origin (t : ℝ) (ht : 0 ≤ t) :
    ∃ C : ℝ, ∀ r : ℝ, 0 < r → r ≤ 1 →
      |gaussianPartnerCoefficient t r - 3 / (4 * r ^ 2)| ≤ C := by
  have hc : ContinuousOn (fun r => |gaussianPartnerRemainder t r|) (Icc 0 1) :=
    (gaussianPartnerRemainder_contDiff t ht).continuous.abs.continuousOn
  obtain ⟨C, hC⟩ := isCompact_Icc.bddAbove_image hc
  refine ⟨C, fun r hr hr1 => ?_⟩
  simpa only [gaussianPartnerCoefficient, add_sub_cancel_left] using
    hC (mem_image_of_mem _ ⟨hr.le, hr1⟩)

theorem gaussianPartnerRemainder_formula (t r : ℝ) (ht : 0 ≤ t) :
    gaussianPartnerRemainder t r = gaussianU t r ^ 2 - 2 * gaussianA t r ^ 2 := by
  rw [gaussianPartnerRemainder, (gaussianU_hasDerivAt t r ht).deriv]
  have hD : 1 + t * r ^ 2 ≠ 0 := ne_of_gt (by positivity)
  unfold gaussianAPrime gaussianUCoefficient gaussianACoefficient gaussianA
  field_simp
  <;> ring

theorem gaussianA_square_le (t r : ℝ) (ht : 0 ≤ t) : gaussianA t r ^ 2 ≤ t := by
  have hD : 0 < 1 + t * r ^ 2 := by positivity
  have hDsq : t * r ^ 2 ≤ (1 + t * r ^ 2) ^ 2 := by
    nlinarith [sq_nonneg (t * r ^ 2)]
  have hmul := mul_le_mul_of_nonneg_left hDsq ht
  unfold gaussianA
  rw [div_pow]
  apply (div_le_iff₀ (sq_pos_of_pos hD)).mpr
  nlinarith

theorem gaussianU_square_ge (t r : ℝ) (ht : 0 ≤ t) : r ^ 2 ≤ gaussianU t r ^ 2 := by
  have hc : 0 ≤ gaussianACoefficient t r := by unfold gaussianACoefficient; positivity
  have hs : 1 ≤ (1 + gaussianACoefficient t r) ^ 2 := one_le_pow₀ (by linarith)
  have hmul := mul_le_mul_of_nonneg_left hs (sq_nonneg r)
  rw [gaussianU_eq_mul_coefficient, mul_pow]
  simpa only [gaussianUCoefficient, mul_one] using hmul

theorem gaussianPartner_quadratic_lower_bound (t r : ℝ) (ht : 0 ≤ t) :
    r ^ 2 - 2 * t ≤ gaussianPartnerCoefficient t r := by
  have hA := gaussianA_square_le t r ht
  have hU := gaussianU_square_ge t r ht
  have hlead : 0 ≤ 3 / (4 * r ^ 2) := by positivity
  rw [gaussianPartnerCoefficient, gaussianPartnerRemainder_formula t r ht]
  linarith

theorem gaussianPartner_lower_bound_at_infinity (t : ℝ) (ht : 0 ≤ t) :
    ∃ R C : ℝ, ∀ r : ℝ, R ≤ r → -C ≤ gaussianPartnerCoefficient t r := by
  refine ⟨0, 2 * t, fun r _ => ?_⟩
  linarith [gaussianPartner_quadratic_lower_bound t r ht, sq_nonneg r]

theorem gaussianScalar_quadratic_lower_bound (t r : ℝ) (ht : 0 ≤ t) :
    r ^ 2 - (2 + 2 * t) ≤
      r ^ 2 - 2 / (1 + t * r ^ 2) - 2 * t / (1 + t * r ^ 2) ^ 2 := by
  have hn : 0 ≤ t * r ^ 2 := by positivity
  have hD : 1 ≤ 1 + t * r ^ 2 := by linarith
  have hD2 : 1 ≤ (1 + t * r ^ 2) ^ 2 := one_le_pow₀ hD
  have h1 : 2 / (1 + t * r ^ 2) ≤ (2 : ℝ) := div_le_self (by norm_num) hD
  have h2 : 2 * t / (1 + t * r ^ 2) ^ 2 ≤ 2 * t := div_le_self (by positivity) hD2
  linarith

private theorem inverseSquare_contDiffOn :
    ContDiffOn ℝ ⊤ (fun r : ℝ => 3 / (4 * r ^ 2)) (Ioi 0) :=
  contDiffOn_const.div (contDiffOn_const.mul (contDiffOn_id.pow 2))
    (fun r hr => ne_of_gt (by have hr0 : 0 < r := hr; positivity))

theorem profilePartner_contDiffOn (t : ℝ) (ht : 0 ≤ t) :
    ContDiffOn ℝ ⊤ (profilePartnerCoefficient t) (Ioi 0) :=
  inverseSquare_contDiffOn.add (profilePartnerRemainder_contDiff t ht).contDiffOn

theorem gaussianPartner_contDiffOn (t : ℝ) (ht : 0 ≤ t) :
    ContDiffOn ℝ ⊤ (gaussianPartnerCoefficient t) (Ioi 0) :=
  inverseSquare_contDiffOn.add (gaussianPartnerRemainder_contDiff t ht).contDiffOn

end MagHK.PartnerAsymptotics
