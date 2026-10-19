import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.NormNum

/-!
Concrete algebraic and analytic verification of the two-orbital construction.
The last norm-balancing theorem explicitly assumes its continuity and endpoint
hypotheses, which are separate obligations for the integral-defined norms.
-/
noncomputable section

namespace MagHK.Noninteracting

open Filter
open scoped Topology
set_option linter.unnecessarySeqFocus false
set_option linter.unusedSimpArgs false

def cancellationA (q r : ℝ) : ℝ := q ^ 2 / (r * (1 + q ^ 2))

theorem total_current_zero (q r w : ℝ) (hr : r ≠ 0) :
    -w * q ^ 2 / r + (w * (1 + q ^ 2)) * cancellationA q r = 0 := by
  have hq : 1 + q ^ 2 ≠ 0 := ne_of_gt (by positivity)
  unfold cancellationA
  field_simp
  <;> ring

theorem orbital_current_cancellation (q r w : ℝ) (hr : r ≠ 0) :
    w * cancellationA q r + w * q ^ 2 * (cancellationA q r - 1 / r) = 0 := by
  have hq : 1 + q ^ 2 ≠ 0 := ne_of_gt (by positivity)
  unfold cancellationA
  field_simp
  <;> ring

theorem density_pos (q w : ℝ) (hw : 0 < w) : 0 < w * (1 + q ^ 2) := by
  positivity

def gaussianA (t r : ℝ) : ℝ := t * r / (1 + t * r ^ 2)
def gaussianAPrime (t r : ℝ) : ℝ := t * (1 - t * r ^ 2) / (1 + t * r ^ 2) ^ 2

theorem gaussianA_hasDerivAt (t r : ℝ) (ht : 0 ≤ t) :
    HasDerivAt (gaussianA t) (gaussianAPrime t r) r := by
  have hd : 1 + t * r ^ 2 ≠ 0 := ne_of_gt (by positivity)
  have h := ((hasDerivAt_id r).const_mul t).div
    (((hasDerivAt_id r).pow 2).const_mul t |>.const_add 1) hd
  apply h.congr_deriv
  simp only [id_eq, Pi.pow_apply, Pi.mul_apply, Pi.add_apply, Pi.div_apply, pow_one, mul_one, one_mul, zero_mul, mul_zero, zero_add, add_zero, Nat.cast_ofNat, Nat.reduceSub, gaussianA, gaussianAPrime, Pi.pow_apply]
  <;> field_simp <;> ring

theorem gaussian_field (t r : ℝ) (ht : 0 ≤ t) (hr : r ≠ 0) :
    gaussianAPrime t r + gaussianA t r / r = 2 * t / (1 + t * r ^ 2) ^ 2 := by
  have hd : 1 + t * r ^ 2 ≠ 0 := ne_of_gt (by positivity)
  unfold gaussianAPrime gaussianA
  field_simp
  <;> ring

theorem gaussian_field_pos (t r : ℝ) (ht : 0 < t) :
    0 < 2 * t / (1 + t * r ^ 2) ^ 2 := by positivity

theorem gaussianA_matches_cancellation (t r : ℝ) (ht : 0 ≤ t) (hr : r ≠ 0) :
    cancellationA (Real.sqrt t * r) r = gaussianA t r := by
  have hs : Real.sqrt t ^ 2 = t := Real.sq_sqrt ht
  have hd : 1 + t * r ^ 2 ≠ 0 := ne_of_gt (by positivity)
  unfold cancellationA gaussianA
  rw [mul_pow, hs]
  field_simp

theorem gaussian_density_cancellation (t r w : ℝ) (ht : 0 ≤ t) :
    (1 + t * r ^ 2) * (w / (1 + t * r ^ 2)) = w := by
  have hd : 1 + t * r ^ 2 ≠ 0 := ne_of_gt (by positivity)
  field_simp

def boundedA (x r : ℝ) : ℝ := x / (r * (1 + x))

theorem boundedA_bounds (x r : ℝ) (hx : 0 < x) (hr : 0 < r) :
    0 < r * boundedA x r ∧ r * boundedA x r < 1 := by
  have heq : r * boundedA x r = x / (1 + x) := by
    unfold boundedA
    field_simp
  rw [heq]
  constructor
  · positivity
  · exact (div_lt_one (by positivity)).2 (by linarith)

theorem second_orbital_reduction (r h hp U a : ℝ) (hr : r ≠ 0) :
    -(-1 / r ^ 2 + hp) - (1 / r + h) ^ 2 +
      2 * (1 / r + h) * U - (1 / r + h) / r + (1 - 2 * r * a) / r ^ 2 =
      2 * (1 + r * h) / r * U - hp - 3 * h / r - h ^ 2 - 2 * a / r := by
  field_simp
  <;> ring

def boundedU (lam r h hp a : ℝ) : ℝ :=
  (lam * r + r * hp + 3 * h + r * h ^ 2 + 2 * a) / (2 * (1 + r * h))

theorem second_orbital_eigenvalue (lam r h hp a : ℝ)
    (hr : r ≠ 0) (hd : 1 + r * h ≠ 0) :
    2 * (1 + r * h) / r * boundedU lam r h hp a - hp -
      3 * h / r - h ^ 2 - 2 * a / r = lam := by
  unfold boundedU
  field_simp
  <;> ring

def remainderK (r h hp hpp : ℝ) : ℝ :=
  4 * hp + r * hpp - 2 * h ^ 2 + 2 * r * h * hp +
    r ^ 2 * h * hpp + r ^ 2 * h ^ 2 * hp - r ^ 2 * hp ^ 2

def baseUPrime (lam r h hp hpp : ℝ) : ℝ :=
  ((lam + 4 * hp + r * hpp + h ^ 2 + 2 * r * h * hp) * (1 + r * h) -
    (lam * r + r * hp + 3 * h + r * h ^ 2) * (h + r * hp)) /
      (2 * (1 + r * h) ^ 2)

theorem baseUPrime_identity (lam r h hp hpp : ℝ) (hd : 1 + r * h ≠ 0) :
    2 * (1 + r * h) ^ 2 * baseUPrime lam r h hp hpp =
      lam * (1 - r ^ 2 * hp) + remainderK r h hp hpp := by
  unfold baseUPrime remainderK
  field_simp
  <;> ring

def boundedUPrime (lam r h hp hpp a : ℝ) : ℝ :=
  baseUPrime lam r h hp hpp +
    ((2 * ((1 + r * h) / r) * a * (1 - r * a) - a / r) * (1 + r * h) -
      a * (h + r * hp)) / (1 + r * h) ^ 2

theorem margin_identity (lam r h hp hpp a : ℝ)
    (hr : r ≠ 0) (hd : 1 + r * h ≠ 0) :
    boundedUPrime lam r h hp hpp a + a / r =
      baseUPrime lam r h hp hpp + r * a * (h ^ 2 - hp) / (1 + r * h) ^ 2 +
        2 * a * (1 - r * a) / r := by
  unfold boundedUPrime
  field_simp
  <;> ring

theorem reciprocal_cube_bound (x s : ℝ) (hx : 0 ≤ x) (hs : 0 < s)
    (hsq : s ^ 2 = 1 + x) :
    x / s ^ 3 ≤ 2 / (3 * Real.sqrt 3) := by
  have hk : 0 < Real.sqrt (3 : ℝ) := Real.sqrt_pos.2 (by norm_num)
  have hk2 : Real.sqrt (3 : ℝ) ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have hs6 : (s ^ 3) ^ 2 = (1 + x) ^ 3 := by
    calc
      (s ^ 3) ^ 2 = (s ^ 2) ^ 3 := by ring
      _ = (1 + x) ^ 3 := by rw [hsq]
  have hp : 0 ≤ (x - 2) ^ 2 * (4 * x + 1) := mul_nonneg (sq_nonneg _) (by linarith)
  have hleft : (3 * Real.sqrt 3 * x) ^ 2 = 27 * x ^ 2 := by
    calc
      (3 * Real.sqrt 3 * x) ^ 2 = 9 * (Real.sqrt 3 ^ 2) * x ^ 2 := by ring
      _ = 27 * x ^ 2 := by rw [hk2]; ring
  have hbound : 3 * Real.sqrt 3 * x ≤ 2 * s ^ 3 := by
    apply (sq_le_sq₀ (by positivity : 0 ≤ 3 * Real.sqrt 3 * x)
      (by positivity : 0 ≤ 2 * s ^ 3)).1
    nlinarith only [hs6, hp, hleft]
  apply (div_le_div_iff₀ (by positivity : 0 < s ^ 3) (by positivity)).2
  nlinarith

theorem margin_numerator_pos : 0 < 20 * (1 - 2 / (3 * Real.sqrt (3 : ℝ))) - 11 := by
  have hk : 0 < Real.sqrt (3 : ℝ) := Real.sqrt_pos.2 (by norm_num)
  have hk2 : Real.sqrt (3 : ℝ) ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have h27 : (40 : ℝ) < 27 * Real.sqrt 3 := by nlinarith
  have hdiv : (2 : ℝ) / (3 * Real.sqrt 3) < 9 / 20 := by
    apply (div_lt_iff₀ (by positivity)).2
    nlinarith
  linarith

theorem remainderK_lower (r h hp hpp : ℝ)
    (hr : 0 ≤ r) (hh : 0 ≤ h) (hp0 : 0 ≤ hp)
    (h1 : -3 ≤ r * hpp) (h2 : h ^ 2 ≤ 1)
    (h3 : -3 ≤ r ^ 2 * h * hpp) (h4 : r ^ 2 * hp ^ 2 ≤ 1) :
    -9 ≤ remainderK r h hp hpp := by
  have h5 : 0 ≤ 2 * r * h * hp := by positivity
  have h6 : 0 ≤ r ^ 2 * h ^ 2 * hp := by positivity
  unfold remainderK
  nlinarith

theorem positive_margin_of_estimates (r h hp hpp a : ℝ)
    (hr : 0 < r) (hh : 0 ≤ h) (ha : 0 ≤ a) (hra : r * a ≤ 1)
    (hp0 : 0 ≤ hp) (hp1 : hp ≤ 1)
    (hh1 : h ^ 2 ≤ 1) (hderiv : r ^ 2 * hp ≤ 2 / (3 * Real.sqrt 3))
    (h1 : -3 ≤ r * hpp) (h3 : -3 ≤ r ^ 2 * h * hpp)
    (h4 : r ^ 2 * hp ^ 2 ≤ 1) :
    (20 * (1 - 2 / (3 * Real.sqrt 3)) - 11) / (2 * (1 + r * h) ^ 2) ≤
      boundedUPrime 20 r h hp hpp a + a / r := by
  have hdpos : 0 < 1 + r * h := by positivity
  have hd : 1 + r * h ≠ 0 := ne_of_gt hdpos
  have hk := remainderK_lower r h hp hpp (le_of_lt hr) hh hp0 h1 hh1 h3 h4
  have hbase := baseUPrime_identity 20 r h hp hpp hd
  have hneg : -1 ≤ r * a * (h ^ 2 - hp) := by
    have hn : 0 ≤ r * a * h ^ 2 := by positivity
    have hn2 : r * a * hp ≤ 1 := by
      calc
        r * a * hp ≤ r * a * 1 := mul_le_mul_of_nonneg_left hp1 (by positivity)
        _ ≤ 1 := by simpa using hra
    nlinarith
  have hterm : 0 ≤ 2 * a * (1 - r * a) / r := by positivity
  rw [margin_identity 20 r h hp hpp a (ne_of_gt hr) hd]
  apply (div_le_iff₀ (by positivity : 0 < 2 * (1 + r * h) ^ 2)).2
  have heq : (baseUPrime 20 r h hp hpp + r * a * (h ^ 2 - hp) / (1 + r * h) ^ 2 +
      2 * a * (1 - r * a) / r) * (2 * (1 + r * h) ^ 2) =
      20 * (1 - r ^ 2 * hp) + remainderK r h hp hpp + 2 * (r * a * (h ^ 2 - hp)) +
        (2 * a * (1 - r * a) / r) * (2 * (1 + r * h) ^ 2) := by
    field_simp
    unfold baseUPrime remainderK
    field_simp
    <;> ring
  rw [heq]
  have hlast : 0 ≤ (2 * a * (1 - r * a) / r) * (2 * (1 + r * h) ^ 2) := by positivity
  nlinarith

theorem positive_margin_strict (r h : ℝ) (hr : 0 ≤ r) (hh : 0 ≤ h) :
    0 < (20 * (1 - 2 / (3 * Real.sqrt 3)) - 11) / (2 * (1 + r * h) ^ 2) := by
  exact div_pos margin_numerator_pos (by positivity)

theorem bounded_threshold : (20 : ℝ) < ((20 + 1) / 2) ^ 2 := by norm_num

/-- The IVT step. Analytic endpoint and continuity claims are explicit inputs. -/
theorem exists_equal_norms (F G : ℝ → ℝ) (a b : ℝ)
    (ha : 0 < a) (hab : a ≤ b)
    (hF : ContinuousOn F (Set.Icc a b)) (hG : ContinuousOn G (Set.Icc a b))
    (hleft : G a < F a) (hright : F b < G b)
    (hpos : ∀ t ∈ Set.Icc a b, 0 < F t) :
    ∃ t, 0 < t ∧ F t = G t ∧ 0 < F t := by
  have hz : (0 : ℝ) ∈ Set.Icc ((F - G) b) ((F - G) a) := by
    simp only [Pi.sub_apply, Set.mem_Icc]
    constructor <;> linarith
  obtain ⟨t, ht, heq⟩ := intermediate_value_Icc' hab (hF.sub hG) hz
  refine ⟨t, lt_of_lt_of_le ha ht.1, ?_, hpos t ht⟩
  simpa only [Pi.sub_apply, sub_eq_zero] using heq


/-- All auxiliary estimates are now proved for the actual square-root profile. -/
theorem profile_estimates (r s : ℝ) (hr : 0 < r) (hs : 0 < s)
    (hsq : s ^ 2 = 1 + r ^ 2) :
    0 ≤ r / s ∧ 0 ≤ 1 / s ^ 3 ∧ 1 / s ^ 3 ≤ 1 ∧
    (r / s) ^ 2 ≤ 1 ∧
    r ^ 2 * (1 / s ^ 3) ≤ 2 / (3 * Real.sqrt 3) ∧
    -3 ≤ r * (-3 * r / s ^ 5) ∧
    -3 ≤ r ^ 2 * (r / s) * (-3 * r / s ^ 5) ∧
    r ^ 2 * (1 / s ^ 3) ^ 2 ≤ 1 := by
  have hs1 : 1 ≤ s := by nlinarith [sq_nonneg r]
  have hs2 : 1 ≤ s ^ 2 := by nlinarith [sq_nonneg r]
  have hs3 : 1 ≤ s ^ 3 := one_le_pow₀ hs1
  have h25 : s ^ 2 ≤ s ^ 5 := pow_le_pow_right₀ hs1 (by omega)
  have h26 : s ^ 2 ≤ s ^ 6 := pow_le_pow_right₀ hs1 (by omega)
  have h46 : s ^ 4 ≤ s ^ 6 := pow_le_pow_right₀ hs1 (by omega)
  have hr4 : r ^ 4 ≤ s ^ 4 := by nlinarith [sq_nonneg (r ^ 2 - s ^ 2)]
  refine ⟨by positivity, by positivity, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact (div_le_one (by positivity)).2 hs3
  · rw [div_pow]
    apply (div_le_one (by positivity)).2
    linarith
  · simpa only [mul_one_div] using reciprocal_cube_bound (r ^ 2) s (sq_nonneg r) hs hsq
  · have heq : r * (-3 * r / s ^ 5) = -3 * r ^ 2 / s ^ 5 := by ring
    rw [heq]
    apply (le_div_iff₀ (by positivity)).2
    nlinarith
  · have heq : r ^ 2 * (r / s) * (-3 * r / s ^ 5) = -3 * r ^ 4 / s ^ 6 := by
      field_simp
    rw [heq]
    apply (le_div_iff₀ (by positivity)).2
    nlinarith
  · have heq : r ^ 2 * (1 / s ^ 3) ^ 2 = r ^ 2 / s ^ 6 := by ring
    rw [heq]
    apply (div_le_one (by positivity)).2
    nlinarith

/-- The auxiliary function γ in `eq:bounded-functions` of the submission. -/
def profileH (r : ℝ) : ℝ := r / Real.sqrt (1 + r ^ 2)
def profileHPrime (r : ℝ) : ℝ := 1 / Real.sqrt (1 + r ^ 2) ^ 3
def profileHSecond (r : ℝ) : ℝ := -3 * r / Real.sqrt (1 + r ^ 2) ^ 5

theorem radiusSqrt_hasDerivAt (r : ℝ) :
    HasDerivAt (fun u : ℝ => Real.sqrt (1 + u ^ 2)) (r / Real.sqrt (1 + r ^ 2)) r := by
  have hd : 0 < 1 + r ^ 2 := by positivity
  have hrad : HasDerivAt (fun u : ℝ => 1 + u ^ 2) (2 * r) r := by
    apply (((hasDerivAt_id r).pow 2).const_add 1).congr_deriv
    simp
  apply (HasDerivAt.sqrt hrad (ne_of_gt hd)).congr_deriv
  ring

theorem profileH_hasDerivAt (r : ℝ) :
    HasDerivAt profileH (profileHPrime r) r := by
  have hd : 0 < 1 + r ^ 2 := by positivity
  have hs : 0 < Real.sqrt (1 + r ^ 2) := Real.sqrt_pos.2 hd
  have hsq := Real.sq_sqrt (le_of_lt hd)
  have h := (hasDerivAt_id r).div (radiusSqrt_hasDerivAt r) (ne_of_gt hs)
  apply h.congr_deriv
  simp only [id_eq, Pi.pow_apply, Pi.mul_apply, Pi.add_apply, Pi.div_apply, pow_one, mul_one, one_mul, zero_mul, mul_zero, zero_add, add_zero, Nat.cast_ofNat, Nat.reduceSub, profileH, profileHPrime]
  field_simp
  nlinarith

theorem profileHPrime_hasDerivAt (r : ℝ) :
    HasDerivAt profileHPrime (profileHSecond r) r := by
  have hd : 0 < 1 + r ^ 2 := by positivity
  have hs : 0 < Real.sqrt (1 + r ^ 2) := Real.sqrt_pos.2 hd
  have hs' : Real.sqrt (1 + r ^ 2) ≠ 0 := ne_of_gt hs
  have h := (hasDerivAt_const r (1 : ℝ)).div
    ((radiusSqrt_hasDerivAt r).pow 3) (pow_ne_zero 3 hs')
  apply h.congr_deriv
  simp only [id_eq, Pi.pow_apply, Pi.mul_apply, Pi.add_apply, Pi.div_apply, pow_one, mul_one, one_mul, zero_mul, mul_zero, zero_add, add_zero, Nat.cast_ofNat, Nat.reduceSub, profileHPrime, profileHSecond]
  field_simp
  <;> ring

theorem positive_margin_profile (r a : ℝ) (hr : 0 < r)
    (ha : 0 ≤ a) (hra : r * a ≤ 1) :
    (20 * (1 - 2 / (3 * Real.sqrt 3)) - 11) / (2 * (1 + r * profileH r) ^ 2) ≤
      boundedUPrime 20 r (profileH r) (profileHPrime r) (profileHSecond r) a + a / r := by
  have hs : 0 < Real.sqrt (1 + r ^ 2) := Real.sqrt_pos.2 (by positivity)
  have he := profile_estimates r (Real.sqrt (1 + r ^ 2)) hr hs (Real.sq_sqrt (by positivity))
  rcases he with ⟨hh, hp0, hp1, hh1, hd, h1, h3, h4⟩
  exact positive_margin_of_estimates r _ _ _ a hr hh ha hra hp0 hp1 hh1 hd h1 h3 h4


/-- The scalar potential of the Gaussian construction agrees exactly with
its logarithmic-derivative factorization. -/
theorem gaussian_scalar_factorization (t r : ℝ) (ht : 0 ≤ t) (hr : r ≠ 0) :
    r ^ 2 - 2 / (1 + t * r ^ 2) - 2 * t / (1 + t * r ^ 2) ^ 2 =
      (r + gaussianA t r) ^ 2 - (1 + gaussianAPrime t r) -
        (r + gaussianA t r) / r - gaussianA t r ^ 2 := by
  have hd : 1 + t * r ^ 2 ≠ 0 := ne_of_gt (by positivity)
  unfold gaussianA gaussianAPrime
  field_simp
  <;> ring

theorem gaussian_second_orbital_energy (r a : ℝ) (hr : r ≠ 0) :
    -(-1 / r ^ 2) - (1 / r) ^ 2 + 2 * (1 / r) * (r + a) -
      (1 / r) / r + (1 - 2 * r * a) / r ^ 2 = 2 := by
  field_simp
  <;> ring

/-- Scalar algebra behind L_0 f = 0 whenever f' = -Uf and
f'' = (U^2-U')f. These derivative equalities are kept visible. -/
theorem zero_orbital_from_log_derivative (r a U Up f fp fpp : ℝ)
    (hfp : fp = -U * f) (hfpp : fpp = (U ^ 2 - Up) * f) :
    -fpp - fp / r + (a ^ 2 + (U ^ 2 - Up - U / r - a ^ 2)) * f = 0 := by
  rw [hfp, hfpp]
  ring

/-- The bounded axial factorization, using sech^2 + tanh^2 = 1. -/
theorem axial_factorization_algebra (c sechVal tanhVal : ℝ)
    (hid : sechVal ^ 2 + tanhVal ^ 2 = 1) :
    (c * tanhVal) ^ 2 - c ^ 2 * sechVal ^ 2 = c ^ 2 - 2 * c ^ 2 * sechVal ^ 2 ∧
    (c * tanhVal) ^ 2 + c ^ 2 * sechVal ^ 2 = c ^ 2 := by
  have h := congrArg (fun x : ℝ => c ^ 2 * x) hid
  constructor <;> nlinarith only [h]


/-- The actual radial growth factor in the bounded example. -/
def profileR (r : ℝ) : ℝ := r * Real.exp (Real.sqrt (1 + r ^ 2) - 1)

theorem profileR_pos (r : ℝ) (hr : 0 < r) : 0 < profileR r := by
  unfold profileR
  positivity

theorem profileR_hasDerivAt (r : ℝ) (hr : 0 < r) :
    HasDerivAt profileR (((1 + r * profileH r) / r) * profileR r) r := by
  have hsq : 0 < 1 + r ^ 2 := by positivity
  have hs : 0 < Real.sqrt (1 + r ^ 2) := Real.sqrt_pos.2 hsq
  have hexp : HasDerivAt (fun u : ℝ => Real.exp (Real.sqrt (1 + u ^ 2) - 1))
      (Real.exp (Real.sqrt (1 + r ^ 2) - 1) * (r / Real.sqrt (1 + r ^ 2))) r :=
    HasDerivAt.exp ((radiusSqrt_hasDerivAt r).sub_const 1)
  have h := (hasDerivAt_id r).mul hexp
  apply h.congr_deriv
  simp only [id_eq, Pi.pow_apply, Pi.mul_apply, Pi.add_apply, Pi.div_apply, pow_one, mul_one, one_mul, zero_mul, mul_zero, zero_add, add_zero, Nat.cast_ofNat, Nat.reduceSub, profileR, profileH]
  field_simp

def profileA (t r : ℝ) : ℝ := boundedA (t * profileR r ^ 2) r

theorem profileA_pos (t r : ℝ) (ht : 0 < t) (hr : 0 < r) : 0 < profileA t r := by
  have hR := profileR_pos r hr
  unfold profileA boundedA
  positivity

theorem profileA_bounds (t r : ℝ) (ht : 0 < t) (hr : 0 < r) :
    0 < r * profileA t r ∧ r * profileA t r < 1 := by
  exact boundedA_bounds (t * profileR r ^ 2) r (by have := profileR_pos r hr; positivity) hr

theorem profileA_hasDerivAt (t r : ℝ) (ht : 0 < t) (hr : 0 < r) :
    HasDerivAt (profileA t)
      (2 * ((1 + r * profileH r) / r) * profileA t r * (1 - r * profileA t r) -
        profileA t r / r) r := by
  have hR := profileR_pos r hr
  have hx := ((profileR_hasDerivAt r hr).pow 2).const_mul t
  have hd : r * (1 + t * profileR r ^ 2) ≠ 0 := ne_of_gt (by positivity)
  have h := hx.div ((hasDerivAt_id r).mul (hx.const_add 1)) hd
  apply h.congr_deriv
  simp only [id_eq, Pi.pow_apply, Pi.mul_apply, Pi.add_apply, Pi.div_apply, pow_one, mul_one, one_mul, zero_mul, mul_zero, zero_add, add_zero, Nat.cast_ofNat, Nat.reduceSub, profileA, boundedA, Pi.pow_apply]
  field_simp
  <;> ring

def profileU (t r : ℝ) : ℝ :=
  boundedU 20 r (profileH r) (profileHPrime r) (profileA t r)

theorem profileU_hasDerivAt (t r : ℝ) (ht : 0 < t) (hr : 0 < r) :
    HasDerivAt (profileU t)
      (boundedUPrime 20 r (profileH r) (profileHPrime r) (profileHSecond r) (profileA t r)) r := by
  have hh := profileH_hasDerivAt r
  have hp := profileHPrime_hasDerivAt r
  have ha := profileA_hasDerivAt t r ht hr
  have hH : 0 ≤ profileH r := by unfold profileH; positivity
  have hd : 2 * (1 + r * profileH r) ≠ 0 := ne_of_gt (by positivity)
  have hn := (((((hasDerivAt_id r).const_mul 20).add ((hasDerivAt_id r).mul hp)).add
    (hh.const_mul 3)).add ((hasDerivAt_id r).mul (hh.pow 2))).add (ha.const_mul 2)
  have hden := (((hasDerivAt_id r).mul hh).const_add 1).const_mul 2
  have h := hn.div hden hd
  apply h.congr_deriv
  simp only [id_eq, Pi.pow_apply, Pi.mul_apply, Pi.add_apply, Pi.div_apply, pow_one, mul_one, one_mul, zero_mul, mul_zero, zero_add, add_zero, Nat.cast_ofNat, Nat.reduceSub, profileU, boundedU, Pi.pow_apply]
  unfold boundedUPrime baseUPrime
  field_simp
  <;> ring

/-- The positivity lemma for the actual functions defined in the manuscript,
including the link from the displayed algebra to Lean's derivative. -/
theorem positive_margin (t r : ℝ) (ht : 0 < t) (hr : 0 < r) :
    (20 * (1 - 2 / (3 * Real.sqrt 3)) - 11) / (2 * (1 + r * profileH r) ^ 2) ≤
      deriv (profileU t) r + profileA t r / r := by
  rw [(profileU_hasDerivAt t r ht hr).deriv]
  exact positive_margin_profile r (profileA t r) hr (le_of_lt (profileA_pos t r ht hr))
    (le_of_lt (profileA_bounds t r ht hr).2)

theorem positive_margin_positive (t r : ℝ) (ht : 0 < t) (hr : 0 < r) :
    0 < deriv (profileU t) r + profileA t r / r := by
  have hh : 0 ≤ profileH r := by unfold profileH; positivity
  exact lt_of_lt_of_le (positive_margin_strict r (profileH r) (le_of_lt hr) hh)
    (positive_margin t r ht hr)

/-- The nonzero magnetic field of the bounded construction away from the axis. -/
theorem bounded_field_positive (t r : ℝ) (ht : 0 < t) (hr : 0 < r) :
    0 < deriv (profileA t) r + profileA t r / r := by
  rw [(profileA_hasDerivAt t r ht hr).deriv]
  have ha := profileA_pos t r ht hr
  have hra := (profileA_bounds t r ht hr).2
  have hh : 0 ≤ profileH r := by unfold profileH; positivity
  have hpos : 0 < 2 * ((1 + r * profileH r) / r) * profileA t r * (1 - r * profileA t r) := by positivity
  linarith


/-- The Gaussian radial orbital in the manuscript. -/
def gaussianF (t r : ℝ) : ℝ := Real.exp (-r ^ 2 / 2) / Real.sqrt (1 + t * r ^ 2)

theorem gaussianF_pos (t r : ℝ) (ht : 0 ≤ t) : 0 < gaussianF t r := by
  unfold gaussianF
  positivity

theorem gaussianF_hasDerivAt (t r : ℝ) (ht : 0 ≤ t) :
    HasDerivAt (gaussianF t) (-(r + gaussianA t r) * gaussianF t r) r := by
  have hd : 0 < 1 + t * r ^ 2 := by positivity
  have hs : 0 < Real.sqrt (1 + t * r ^ 2) := Real.sqrt_pos.2 hd
  have hrad : HasDerivAt (fun u : ℝ => 1 + t * u ^ 2) (2 * t * r) r := by
    apply ((((hasDerivAt_id r).pow 2).const_mul t).const_add 1).congr_deriv
    simp
    <;> ring
  have hS : HasDerivAt (fun u : ℝ => Real.sqrt (1 + t * u ^ 2))
      (t * r / Real.sqrt (1 + t * r ^ 2)) r := by
    apply (HasDerivAt.sqrt hrad (ne_of_gt hd)).congr_deriv
    ring
  have hE : HasDerivAt (fun u : ℝ => Real.exp (-u ^ 2 / 2))
      (-r * Real.exp (-r ^ 2 / 2)) r := by
    apply (HasDerivAt.exp ((((hasDerivAt_id r).pow 2).neg).div_const 2)).congr_deriv
    simp
    <;> ring
  have h := hE.div hS (ne_of_gt hs)
  apply h.congr_deriv
  simp only [id_eq, Pi.pow_apply, Pi.mul_apply, Pi.add_apply, Pi.div_apply, pow_one, mul_one, one_mul, zero_mul, mul_zero, zero_add, add_zero, Nat.cast_ofNat, Nat.reduceSub, gaussianF, gaussianA]
  field_simp [Real.sq_sqrt (le_of_lt hd)]
  ring_nf
  rw [Real.sq_sqrt (by positivity : 0 ≤ 1 + r ^ 2 * t)]
  ring

theorem gaussianFPrime_hasDerivAt (t r : ℝ) (ht : 0 ≤ t) :
    HasDerivAt (fun u => -(u + gaussianA t u) * gaussianF t u)
      (((r + gaussianA t r) ^ 2 - (1 + gaussianAPrime t r)) * gaussianF t r) r := by
  have h := (((hasDerivAt_id r).add (gaussianA_hasDerivAt t r ht)).neg).mul
    (gaussianF_hasDerivAt t r ht)
  apply h.congr_deriv
  simp
  <;> ring

/-- The displayed zero-energy radial eigen-equation holds for the actual
Gaussian function and its actual first and second derivatives. -/
theorem gaussian_zero_eigen_equation (t r : ℝ) (ht : 0 ≤ t) (hr : r ≠ 0) :
    -deriv (deriv (gaussianF t)) r - deriv (gaussianF t) r / r +
      (gaussianA t r ^ 2 +
        (r ^ 2 - 2 / (1 + t * r ^ 2) - 2 * t / (1 + t * r ^ 2) ^ 2)) * gaussianF t r = 0 := by
  have heq : deriv (gaussianF t) = fun u => -(u + gaussianA t u) * gaussianF t u := by
    funext u
    exact (gaussianF_hasDerivAt t u ht).deriv
  rw [heq, (gaussianFPrime_hasDerivAt t r ht).deriv,
    gaussian_scalar_factorization t r ht hr]
  ring


/-- Cancelling r gives a globally regular expression for a_t, including r=0. -/
theorem profileA_regular (t r : ℝ) :
    profileA t r = t * r * Real.exp (Real.sqrt (1 + r ^ 2) - 1) ^ 2 /
      (1 + t * r ^ 2 * Real.exp (Real.sqrt (1 + r ^ 2) - 1) ^ 2) := by
  by_cases hr : r = 0
  · simp [hr, profileA, boundedA, profileR]
  · unfold profileA boundedA profileR
    field_simp

theorem profileA_continuous (t : ℝ) (ht : 0 ≤ t) : Continuous (profileA t) := by
  have hs : Continuous (fun r : ℝ => Real.sqrt (1 + r ^ 2)) :=
    Real.continuous_sqrt.comp (continuous_const.add (continuous_id.pow 2))
  have hE : Continuous (fun r : ℝ => Real.exp (Real.sqrt (1 + r ^ 2) - 1)) :=
    Real.continuous_exp.comp (hs.sub continuous_const)
  have hn : Continuous (fun r : ℝ => t * r * Real.exp (Real.sqrt (1 + r ^ 2) - 1) ^ 2) :=
    (continuous_const.mul continuous_id).mul (hE.pow 2)
  have hd : Continuous (fun r : ℝ => 1 + t * r ^ 2 * Real.exp (Real.sqrt (1 + r ^ 2) - 1) ^ 2) :=
    continuous_const.add ((continuous_const.mul (continuous_id.pow 2)).mul (hE.pow 2))
  have hh := hn.div hd (fun r => ne_of_gt (by positivity :
    0 < 1 + t * r ^ 2 * Real.exp (Real.sqrt (1 + r ^ 2) - 1) ^ 2))
  have heq : profileA t = fun r => t * r * Real.exp (Real.sqrt (1 + r ^ 2) - 1) ^ 2 /
      (1 + t * r ^ 2 * Real.exp (Real.sqrt (1 + r ^ 2) - 1) ^ 2) := funext (profileA_regular t)
  rw [heq]
  exact hh

theorem profileU_continuous (t : ℝ) (ht : 0 ≤ t) : Continuous (profileU t) := by
  have hh : Continuous profileH := continuous_iff_continuousAt.2
    (fun r => (profileH_hasDerivAt r).continuousAt)
  have hp : Continuous profileHPrime := continuous_iff_continuousAt.2
    (fun r => (profileHPrime_hasDerivAt r).continuousAt)
  have ha := profileA_continuous t ht
  have hn : Continuous (fun r : ℝ => 20 * r + r * profileHPrime r + 3 * profileH r +
      r * profileH r ^ 2 + 2 * profileA t r) :=
    ((((continuous_const.mul continuous_id).add (continuous_id.mul hp)).add
      (continuous_const.mul hh)).add (continuous_id.mul (hh.pow 2))).add (continuous_const.mul ha)
  have hd : Continuous (fun r : ℝ => 2 * (1 + r * profileH r)) :=
    continuous_const.mul (continuous_const.add (continuous_id.mul hh))
  have hden : ∀ r : ℝ, 2 * (1 + r * profileH r) ≠ 0 := by
    intro r
    have hrh : 0 ≤ r * profileH r := by
      unfold profileH
      have h := div_nonneg (sq_nonneg r) (Real.sqrt_nonneg (1 + r ^ 2))
      simpa only [pow_two, mul_div_assoc] using h
    exact ne_of_gt (by positivity)
  exact hn.div hd hden

def profileF (t r : ℝ) : ℝ := Real.exp (-(∫ u in (0 : ℝ)..r, profileU t u))

theorem profileF_pos (t r : ℝ) : 0 < profileF t r := Real.exp_pos _

theorem profileF_hasDerivAt (t r : ℝ) (ht : 0 ≤ t) :
    HasDerivAt (profileF t) (-profileU t r * profileF t r) r := by
  have hc := profileU_continuous t ht
  have hi := intervalIntegral.integral_hasDerivAt_right (hc.intervalIntegrable 0 r)
    hc.aestronglyMeasurable.stronglyMeasurableAtFilter hc.continuousAt
  have h := HasDerivAt.exp hi.neg
  apply h.congr_deriv
  unfold profileF
  simp only [Pi.neg_apply]
  ring

theorem profileFPrime_hasDerivAt (t r : ℝ) (ht : 0 < t) (hr : 0 < r) :
    HasDerivAt (fun u => -profileU t u * profileF t u)
      ((profileU t r ^ 2 - deriv (profileU t) r) * profileF t r) r := by
  have h := (profileU_hasDerivAt t r ht hr).neg.mul (profileF_hasDerivAt t r (le_of_lt ht))
  apply h.congr_deriv
  rw [(profileU_hasDerivAt t r ht hr).deriv]
  simp only [Pi.neg_apply]
  ring

def profileV (t r : ℝ) : ℝ :=
  profileU t r ^ 2 - deriv (profileU t) r - profileU t r / r - profileA t r ^ 2

/-- The actual integral-defined bounded orbital solves its radial equation. -/
theorem bounded_zero_eigen_equation (t r : ℝ) (ht : 0 < t) (hr : 0 < r) :
    -deriv (deriv (profileF t)) r - deriv (profileF t) r / r +
      (profileA t r ^ 2 + profileV t r) * profileF t r = 0 := by
  have heq : deriv (profileF t) = fun u => -profileU t u * profileF t u := by
    funext u
    exact (profileF_hasDerivAt t u (le_of_lt ht)).deriv
  rw [heq, (profileFPrime_hasDerivAt t r ht hr).deriv]
  unfold profileV
  ring


theorem profileH_mul_nonneg (r : ℝ) : 0 ≤ r * profileH r := by
  unfold profileH
  have h := div_nonneg (sq_nonneg r) (Real.sqrt_nonneg (1 + r ^ 2))
  simpa only [pow_two, mul_div_assoc] using h

theorem profileU_difference (t r : ℝ) :
    profileU t r - profileU 0 r = profileA t r / (1 + r * profileH r) := by
  have hd : 1 + r * profileH r ≠ 0 := ne_of_gt (by have := profileH_mul_nonneg r; positivity)
  have hz : profileA 0 r = 0 := by simp [profileA, boundedA]
  unfold profileU boundedU
  rw [hz]
  field_simp
  <;> ring

/-- The exact f_t / f_0 comparison identity from the manuscript. -/
theorem profileF_comparison_identity (t r : ℝ) (ht : 0 ≤ t) :
    profileF t r = profileF 0 r *
      Real.exp (-(∫ u in (0 : ℝ)..r, profileA t u / (1 + u * profileH u))) := by
  have htC := profileU_continuous t ht
  have h0C := profileU_continuous 0 (by norm_num)
  have hi : (∫ u in (0 : ℝ)..r, profileA t u / (1 + u * profileH u)) =
      (∫ u in (0 : ℝ)..r, profileU t u) - (∫ u in (0 : ℝ)..r, profileU 0 u) := by
    simp_rw [← profileU_difference]
    exact intervalIntegral.integral_sub (htC.intervalIntegrable 0 r) (h0C.intervalIntegrable 0 r)
  unfold profileF
  rw [← Real.exp_add, hi]
  congr 1
  ring

theorem profileA_nonneg (t r : ℝ) (ht : 0 ≤ t) (hr : 0 ≤ r) : 0 ≤ profileA t r := by
  unfold profileA boundedA
  positivity

theorem profileF_le_base (t r : ℝ) (ht : 0 ≤ t) (hr : 0 ≤ r) :
    profileF t r ≤ profileF 0 r := by
  apply Real.exp_le_exp.2
  apply neg_le_neg
  apply intervalIntegral.integral_mono_on hr
    ((profileU_continuous 0 (by norm_num)).intervalIntegrable 0 r)
    ((profileU_continuous t ht).intervalIntegrable 0 r)
  intro u hu
  have h := profileU_difference t u
  have ha := profileA_nonneg t u ht hu.1
  have hd : 0 < 1 + u * profileH u := by have := profileH_mul_nonneg u; positivity
  have hp : 0 ≤ profileA t u / (1 + u * profileH u) := div_nonneg ha (le_of_lt hd)
  linarith


theorem profileR_hasDerivAt_regular (r : ℝ) :
    HasDerivAt profileR
      (Real.exp (Real.sqrt (1 + r ^ 2) - 1) * (1 + r * profileH r)) r := by
  have hexp : HasDerivAt (fun u : ℝ => Real.exp (Real.sqrt (1 + u ^ 2) - 1))
      (Real.exp (Real.sqrt (1 + r ^ 2) - 1) * (r / Real.sqrt (1 + r ^ 2))) r :=
    HasDerivAt.exp ((radiusSqrt_hasDerivAt r).sub_const 1)
  have h := (hasDerivAt_id r).mul hexp
  apply h.congr_deriv
  simp only [id_eq, one_mul, profileH]
  ring

def profileLog (t r : ℝ) : ℝ := Real.log (1 + t * profileR r ^ 2) / 2

theorem profileLog_hasDerivAt (t r : ℝ) (ht : 0 ≤ t) :
    HasDerivAt (profileLog t) ((1 + r * profileH r) * profileA t r) r := by
  have hd : 1 + t * profileR r ^ 2 ≠ 0 := ne_of_gt (by positivity)
  have hx : HasDerivAt (fun u : ℝ => 1 + t * profileR u ^ 2)
      (t * (2 * profileR r *
        (Real.exp (Real.sqrt (1 + r ^ 2) - 1) * (1 + r * profileH r)))) r := by
    apply ((((profileR_hasDerivAt_regular r).pow 2).const_mul t).const_add 1).congr_deriv
    simp
  have h := (HasDerivAt.log hx hd).div_const 2
  apply h.congr_deriv
  rw [profileA_regular]
  unfold profileR
  field_simp

theorem profileLog_derivative_continuous (t : ℝ) (ht : 0 ≤ t) :
    Continuous (fun r => (1 + r * profileH r) * profileA t r) := by
  have hH : Continuous profileH := continuous_iff_continuousAt.2
    (fun r => (profileH_hasDerivAt r).continuousAt)
  exact (continuous_const.add (continuous_id.mul hH)).mul (profileA_continuous t ht)

theorem profileCorrection_continuous (t : ℝ) (ht : 0 ≤ t) :
    Continuous (fun r => profileA t r / (1 + r * profileH r)) := by
  simp_rw [← profileU_difference]
  exact (profileU_continuous t ht).sub (profileU_continuous 0 (by norm_num))

/-- The logarithmic bound on I_t used for the lower norm comparison. -/
theorem profileCorrection_integral_le (t r : ℝ) (ht : 0 ≤ t) (hr : 0 ≤ r) :
    (∫ u in (0 : ℝ)..r, profileA t u / (1 + u * profileH u)) ≤ profileLog t r := by
  have hCorr := profileCorrection_continuous t ht
  have hLog := profileLog_derivative_continuous t ht
  have hle : (∫ u in (0 : ℝ)..r, profileA t u / (1 + u * profileH u)) ≤
      ∫ u in (0 : ℝ)..r, (1 + u * profileH u) * profileA t u := by
    apply intervalIntegral.integral_mono_on hr (hCorr.intervalIntegrable 0 r) (hLog.intervalIntegrable 0 r)
    intro u hu
    have ha := profileA_nonneg t u ht hu.1
    have hD : 1 ≤ 1 + u * profileH u := by have := profileH_mul_nonneg u; linarith
    have hD0 : 0 < 1 + u * profileH u := lt_of_lt_of_le (by norm_num) hD
    apply (div_le_iff₀ hD0).2
    calc
      profileA t u ≤ profileA t u * (1 + u * profileH u) := le_mul_of_one_le_right ha hD
      _ ≤ profileA t u * (1 + u * profileH u) * (1 + u * profileH u) :=
        le_mul_of_one_le_right (by positivity) hD
      _ = (1 + u * profileH u) * profileA t u * (1 + u * profileH u) := by ring
  have heq := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun u (_ : u ∈ Set.uIcc (0 : ℝ) r) => profileLog_hasDerivAt t u ht) (hLog.intervalIntegrable 0 r)
  have hz : profileLog t 0 = 0 := by simp [profileLog, profileR]
  rw [hz, sub_zero] at heq
  rwa [heq] at hle

/-- Both pointwise comparison inequalities for the actual integral-defined f_t. -/
theorem profileF_two_sided (t r : ℝ) (ht : 0 ≤ t) (hr : 0 ≤ r) :
    profileF 0 r / Real.sqrt (1 + t * profileR r ^ 2) ≤ profileF t r ∧
      profileF t r ≤ profileF 0 r := by
  refine ⟨?_, profileF_le_base t r ht hr⟩
  have hI := profileCorrection_integral_le t r ht hr
  have hE := Real.exp_le_exp.2 (neg_le_neg hI)
  have heq : Real.exp (-profileLog t r) = 1 / Real.sqrt (1 + t * profileR r ^ 2) := by
    unfold profileLog
    rw [Real.exp_neg, Real.exp_half, Real.exp_log (by positivity : 0 < 1 + t * profileR r ^ 2)]
    simp only [one_div]
  rw [profileF_comparison_identity t r ht]
  calc
    profileF 0 r / Real.sqrt (1 + t * profileR r ^ 2) = profileF 0 r * Real.exp (-profileLog t r) := by
      rw [heq]
      ring
    _ ≤ profileF 0 r * Real.exp (-(∫ u in (0 : ℝ)..r, profileA t u / (1 + u * profileH u))) :=
      mul_le_mul_of_nonneg_left hE (le_of_lt (profileF_pos 0 r))


theorem profileH_bounds (r : ℝ) (hr : 0 ≤ r) : 0 ≤ profileH r ∧ profileH r ≤ 1 := by
  have hs : 0 < Real.sqrt (1 + r ^ 2) := Real.sqrt_pos.2 (by positivity)
  have hsq := Real.sq_sqrt (by positivity : 0 ≤ 1 + r ^ 2)
  constructor
  · unfold profileH
    positivity
  · unfold profileH
    apply (div_le_one hs).2
    nlinarith

theorem profileU_nonneg (t r : ℝ) (ht : 0 ≤ t) (hr : 0 ≤ r) : 0 ≤ profileU t r := by
  have hh := (profileH_bounds r hr).1
  have hp : 0 ≤ profileHPrime r := by unfold profileHPrime; positivity
  have ha := profileA_nonneg t r ht hr
  unfold profileU boundedU
  positivity

theorem profileF_le_one (t r : ℝ) (ht : 0 ≤ t) (hr : 0 ≤ r) : profileF t r ≤ 1 := by
  have hi : 0 ≤ ∫ u in (0 : ℝ)..r, profileU t u :=
    intervalIntegral.integral_nonneg hr (fun u hu => profileU_nonneg t u ht hu.1)
  unfold profileF
  exact Real.exp_le_one_iff.2 (neg_nonpos.2 hi)

/-- A convenient explicit decay rate, avoiding an asymptotic expansion. -/
theorem profileU_base_ge_five (r : ℝ) (hr : 1 ≤ r) : 5 ≤ profileU 0 r := by
  have hr0 : 0 ≤ r := by linarith
  have hh := profileH_bounds r hr0
  have hH : 0 ≤ profileH r := hh.1
  have hp : 0 ≤ profileHPrime r := by unfold profileHPrime; positivity
  have hmul : r * profileH r ≤ r := by simpa using mul_le_mul_of_nonneg_left hh.2 hr0
  have hd : 0 < 2 * (1 + r * profileH r) := by positivity
  have h0 : profileA 0 r = 0 := by simp [profileA, boundedA]
  unfold profileU boundedU
  rw [h0]
  apply (le_div_iff₀ hd).2
  have hn1 : 0 ≤ r * profileHPrime r := by positivity
  have hn2 : 0 ≤ r * profileH r ^ 2 := by positivity
  nlinarith

theorem profileF_base_tail (r : ℝ) (hr : 1 ≤ r) :
    profileF 0 r ≤ Real.exp 5 * Real.exp (-5 * r) := by
  have hc := profileU_continuous 0 (by norm_num)
  have hI0 : 0 ≤ ∫ u in (0 : ℝ)..1, profileU 0 u :=
    intervalIntegral.integral_nonneg (by norm_num) (fun u hu => profileU_nonneg 0 u (by norm_num) hu.1)
  have hI1 : 5 * (r - 1) ≤ ∫ u in (1 : ℝ)..r, profileU 0 u := by
    have h := intervalIntegral.integral_mono_on (μ := MeasureTheory.volume) hr
      (continuous_const.intervalIntegrable 1 r) (hc.intervalIntegrable 1 r)
      (fun u (hu : u ∈ Set.Icc (1 : ℝ) r) => profileU_base_ge_five u hu.1)
    simpa only [intervalIntegral.integral_const, smul_eq_mul, mul_comm] using h
  have hsum := intervalIntegral.integral_add_adjacent_intervals (μ := MeasureTheory.volume) (hc.intervalIntegrable 0 1)
    (hc.intervalIntegrable 1 r)
  have hI : 5 * (r - 1) ≤ ∫ u in (0 : ℝ)..r, profileU 0 u := by linarith
  unfold profileF
  rw [← Real.exp_add]
  apply Real.exp_le_exp.2
  linarith

theorem profileR_upper (r : ℝ) (hr : 0 ≤ r) : profileR r ≤ r * Real.exp r := by
  have hs : Real.sqrt (1 + r ^ 2) ≤ 1 + r :=
    (Real.sqrt_le_left (by positivity)).2 (by nlinarith)
  unfold profileR
  apply mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 (by linarith)) hr


theorem profileH_le_self (r : ℝ) (hr : 0 ≤ r) : profileH r ≤ r := by
  have hs : 0 < Real.sqrt (1 + r ^ 2) := Real.sqrt_pos.2 (by positivity)
  have hs1 : 1 ≤ Real.sqrt (1 + r ^ 2) :=
    (Real.le_sqrt (by norm_num) (by positivity)).2 (by nlinarith)
  unfold profileH
  apply (div_le_iff₀ hs).2
  nlinarith

theorem gaussianA_le_profileA (t r : ℝ) (ht : 0 ≤ t) (hr : 0 ≤ r) :
    gaussianA t r ≤ profileA t r := by
  have hs1 : 1 ≤ Real.sqrt (1 + r ^ 2) :=
    (Real.le_sqrt (by norm_num) (by positivity)).2 (by nlinarith)
  have hE : 1 ≤ Real.exp (Real.sqrt (1 + r ^ 2) - 1) := Real.one_le_exp_iff.2 (by linarith)
  have hE2 : 1 ≤ Real.exp (Real.sqrt (1 + r ^ 2) - 1) ^ 2 := by nlinarith
  rw [profileA_regular]
  unfold gaussianA
  apply (div_le_div_iff₀ (by positivity) (by positivity)).2
  have hn : 0 ≤ t * r * (Real.exp (Real.sqrt (1 + r ^ 2) - 1) ^ 2 - 1) := by positivity
  nlinarith only [hn]

def gaussianLog (t r : ℝ) : ℝ := Real.log (1 + t * r ^ 2) / 2

theorem gaussianLog_hasDerivAt (t r : ℝ) (ht : 0 ≤ t) :
    HasDerivAt (gaussianLog t) (gaussianA t r) r := by
  have hd : 1 + t * r ^ 2 ≠ 0 := ne_of_gt (by positivity)
  have hx : HasDerivAt (fun u : ℝ => 1 + t * u ^ 2) (2 * t * r) r := by
    apply ((((hasDerivAt_id r).pow 2).const_mul t).const_add 1).congr_deriv
    simp
    <;> ring
  apply ((HasDerivAt.log hx hd).div_const 2).congr_deriv
  unfold gaussianA
  ring

/-- A quantitative lower bound forcing f_t(r) to zero at fixed r>0. -/
theorem profileCorrection_integral_ge (t r : ℝ) (ht : 0 ≤ t) (hr : 0 ≤ r) :
    Real.log (1 + t * r ^ 2) / (2 * (1 + r ^ 2)) ≤
      ∫ u in (0 : ℝ)..r, profileA t u / (1 + u * profileH u) := by
  have hga : Continuous (gaussianA t) := continuous_iff_continuousAt.2
    (fun u => (gaussianA_hasDerivAt t u ht).continuousAt)
  have hgc : Continuous (fun u => gaussianA t u / (1 + r ^ 2)) := hga.div_const _
  have hpc := profileCorrection_continuous t ht
  have hle : (∫ u in (0 : ℝ)..r, gaussianA t u / (1 + r ^ 2)) ≤
      ∫ u in (0 : ℝ)..r, profileA t u / (1 + u * profileH u) := by
    apply intervalIntegral.integral_mono_on hr (hgc.intervalIntegrable 0 r) (hpc.intervalIntegrable 0 r)
    intro u hu
    have hU := mul_le_mul_of_nonneg_left (profileH_le_self u hu.1) hu.1
    have hD : 1 + u * profileH u ≤ 1 + r ^ 2 := by nlinarith [hu.1, hu.2]
    have hD0 : 0 < 1 + u * profileH u := by have := profileH_mul_nonneg u; positivity
    calc
      gaussianA t u / (1 + r ^ 2) ≤ profileA t u / (1 + r ^ 2) :=
        div_le_div_of_nonneg_right (gaussianA_le_profileA t u ht hu.1) (by positivity)
      _ ≤ profileA t u / (1 + u * profileH u) :=
        div_le_div_of_nonneg_left (profileA_nonneg t u ht hu.1) hD0 hD
  have hInt := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun u (_ : u ∈ Set.uIcc (0 : ℝ) r) => gaussianLog_hasDerivAt t u ht) (hga.intervalIntegrable 0 r)
  have hz : gaussianLog t 0 = 0 := by simp [gaussianLog]
  rw [hz, sub_zero] at hInt
  rw [intervalIntegral.integral_div, hInt] at hle
  simpa only [gaussianLog, div_div] using hle

theorem profileF_parameter_upper (t r : ℝ) (ht : 0 ≤ t) (hr : 0 ≤ r) :
    profileF t r ≤ profileF 0 r *
      Real.exp (-(Real.log (1 + t * r ^ 2) / (2 * (1 + r ^ 2)))) := by
  rw [profileF_comparison_identity t r ht]
  apply mul_le_mul_of_nonneg_left _ (le_of_lt (profileF_pos 0 r))
  exact Real.exp_le_exp.2 (neg_le_neg (profileCorrection_integral_ge t r ht hr))

/-- The actual bounded orbital vanishes pointwise as t tends to infinity. -/
theorem profileF_tendsto_atTop (r : ℝ) (hr : 0 < r) :
    Tendsto (fun t => profileF t r) atTop (𝓝 0) := by
  have hlin : Tendsto (fun t : ℝ => t * r ^ 2) atTop atTop :=
    tendsto_id.atTop_mul_const (by positivity)
  have harg : Tendsto (fun t : ℝ => 1 + t * r ^ 2) atTop atTop :=
    tendsto_atTop_mono (fun t => by linarith) hlin
  have hlog : Tendsto (fun t : ℝ => Real.log (1 + t * r ^ 2)) atTop atTop :=
    Real.tendsto_log_atTop.comp harg
  have hscaled : Tendsto (fun t : ℝ => Real.log (1 + t * r ^ 2) / (2 * (1 + r ^ 2))) atTop atTop := by
    simpa only [div_eq_mul_inv] using hlog.atTop_mul_const (by positivity : 0 < (2 * (1 + r ^ 2))⁻¹)
  have hneg := tendsto_neg_atTop_atBot.comp hscaled
  have hE : Tendsto (fun t : ℝ => profileF 0 r *
      Real.exp (-(Real.log (1 + t * r ^ 2) / (2 * (1 + r ^ 2))))) atTop (𝓝 0) := by
    simpa only [mul_zero, Function.comp_def] using tendsto_const_nhds.mul (Real.tendsto_exp_atBot.comp hneg)
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hE
  · exact Eventually.of_forall (fun t => le_of_lt (profileF_pos t r))
  · filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht
    exact profileF_parameter_upper t r ht (le_of_lt hr)


/-- The actual bounded orbital tends pointwise to f_0 as t decreases to zero. -/
theorem profileF_tendsto_zero (r : ℝ) (hr : 0 ≤ r) :
    Tendsto (fun t => profileF t r) (𝓝[Set.Ici 0] 0) (𝓝 (profileF 0 r)) := by
  have hc : Continuous (fun t : ℝ => Real.sqrt (1 + t * profileR r ^ 2)) :=
    Real.continuous_sqrt.comp (continuous_const.add (continuous_id.mul continuous_const))
  have hca : ContinuousAt (fun t : ℝ => profileF 0 r / Real.sqrt (1 + t * profileR r ^ 2)) 0 :=
    continuousAt_const.div hc.continuousAt (by simp)
  have hlim : Tendsto (fun t : ℝ => profileF 0 r / Real.sqrt (1 + t * profileR r ^ 2))
      (𝓝[Set.Ici 0] 0) (𝓝 (profileF 0 r)) := by
    simpa using hca.tendsto.mono_left nhdsWithin_le_nhds
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hlim tendsto_const_nhds
  · filter_upwards [self_mem_nhdsWithin] with t ht
    exact (profileF_two_sided t r ht hr).1
  · filter_upwards [self_mem_nhdsWithin] with t ht
    exact (profileF_two_sided t r ht hr).2

/-- Squared radial-integrand dominators needed for the subsequent DCT argument. -/
theorem radial_integrand_bounds (t r : ℝ) (ht : 0 ≤ t) (hr : 0 ≤ r) :
    0 ≤ profileF t r ^ 2 * r ∧
    profileF t r ^ 2 * r ≤ profileF 0 r ^ 2 * r ∧
    t * profileR r ^ 2 * profileF t r ^ 2 * r ≤ t * profileR r ^ 2 * profileF 0 r ^ 2 * r := by
  have h0 := profileF_pos 0 r
  have ht0 := profileF_pos t r
  have hle := profileF_le_base t r ht hr
  have hs : profileF t r ^ 2 ≤ profileF 0 r ^ 2 := by nlinarith
  refine ⟨by positivity, mul_le_mul_of_nonneg_right hs hr, ?_⟩
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hs (by positivity)) hr

end MagHK.Noninteracting
